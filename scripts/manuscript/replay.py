#!/usr/bin/env python3
"""Portable read-only manuscript replay. Inputs may be ZIPs or extracted directories."""
import argparse
import datetime
import hashlib
import json
from pathlib import Path, PurePosixPath
import platform
import stat
import subprocess
import sys
import tempfile
import zipfile


def sha(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def file_record(path, relative_to=None):
    return {"path": str(path.relative_to(relative_to) if relative_to else path),
            "bytes": path.stat().st_size, "sha256": sha(path)}


def safe_extract(archive, destination):
    """Never execute archive files; reject escaping paths, links, and oversized ZIPs."""
    with zipfile.ZipFile(archive) as source:
        infos = source.infolist()
        if len(infos) > 10000 or sum(item.file_size for item in infos) > 512 * 1024 * 1024:
            raise ValueError("Input ZIP exceeds the replay's file-count/expanded-size limits")
        seen = set()
        for item in infos:
            name = PurePosixPath(item.filename)
            if (not item.filename or "\\" in item.filename or name.is_absolute()
                    or ".." in name.parts or any(":" in part for part in name.parts)):
                raise ValueError(f"Unsafe ZIP path: {item.filename!r}")
            if name.as_posix() in seen:
                raise ValueError(f"Duplicate ZIP path: {item.filename!r}")
            seen.add(name.as_posix())
            kind = stat.S_IFMT(item.external_attr >> 16)
            if kind not in (0, stat.S_IFREG, stat.S_IFDIR):
                raise ValueError(f"ZIP link or special file rejected: {item.filename!r}")
            if item.flag_bits & 1:
                raise ValueError(f"Encrypted ZIP member rejected: {item.filename!r}")
        for item in infos:
            target = destination.joinpath(*PurePosixPath(item.filename).parts)
            if item.is_dir():
                target.mkdir(parents=True, exist_ok=True)
            else:
                target.parent.mkdir(parents=True, exist_ok=True)
                with source.open(item) as src, target.open("wb") as dst:
                    for chunk in iter(lambda: src.read(1024 * 1024), b""):
                        dst.write(chunk)


def identify_layout(root, marker):
    marker = PurePosixPath(marker)
    candidates = []
    if (root / marker).is_file():
        candidates.append(root)
    # Accept the source/research directory itself as well as the enclosing root.
    if root.name == marker.parts[0] and (root.parent / marker).is_file():
        candidates.append(root.parent)
    if not candidates:
        for path in root.rglob(marker.name):
            if path.is_file() and tuple(path.parts[-len(marker.parts):]) == marker.parts:
                candidates.append(path.parents[len(marker.parts) - 1])
    unique = sorted(set(path.resolve() for path in candidates))
    if len(unique) != 1:
        raise ValueError(f"Expected exactly one {marker} layout in {root}; found {unique}")
    return unique[0]


def prepare_input(path, label, temporary, marker):
    path = path.resolve()
    if path.is_dir():
        root = identify_layout(path, marker)
        return root, {"kind": "directory", "supplied_path": str(path), "resolved_root": str(root)}
    if not path.is_file() or not zipfile.is_zipfile(path):
        raise ValueError(f"{label} must be an extracted directory or a ZIP: {path}")
    destination = temporary / label
    destination.mkdir()
    safe_extract(path, destination)
    root = identify_layout(destination, marker)
    return root, {"kind": "zip", "archive": file_record(path),
                  "root_inside_zip": str(root.relative_to(destination)), "extraction_paths_validated": True}


def is_within(child, parent):
    return child == parent or parent in child.parents


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--updated", type=Path, required=True,
                        help="Updated EC_ranks_5_7_manuscript ZIP or extracted root/source directory")
    parser.add_argument("--original", type=Path, required=True,
                        help="Original rank-5-elliptic-curves-main ZIP or extracted root/research directory")
    parser.add_argument("--lean-root", type=Path, required=True,
                        help="Checked repository root containing RankCertificates/*.lean")
    parser.add_argument("--output-dir", type=Path, required=True,
                        help="New external directory for receipts and logs; no input files are modified")
    args = parser.parse_args()
    scripts = Path(__file__).resolve().parent
    output = args.output_dir.resolve()
    lean = args.lean_root.resolve()
    if lean.name == "RankCertificates":
        lean = lean.parent
    if not (lean / "RankCertificates" / "PrimePatterns.lean").is_file():
        raise ValueError("--lean-root must contain RankCertificates/PrimePatterns.lean")
    for supplied in [lean, args.updated.resolve(), args.original.resolve()]:
        if supplied.is_dir() and is_within(output, supplied):
            raise ValueError("--output-dir must lie outside every input directory and the Lean repository")
    if output.exists() and any(output.iterdir()):
        raise ValueError("--output-dir must be absent or empty; existing receipts are not overwritten")
    output.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="ec567-replay-") as temporary_name:
        temporary = Path(temporary_name)
        updated, updated_record = prepare_input(args.updated, "updated", temporary, "source/sections/06-rank5.tex")
        original, original_record = prepare_input(args.original, "original", temporary, "research/paper/final_rank5.tex")
        commands = []
        for script, receipt in [("literal_compare.py", "literal-comparison.json"),
                                ("certificate_compare.py", "certificate-comparison.json")]:
            command = [sys.executable, str(scripts / script), "--updated-dir", str(updated),
                       "--original-dir", str(original), "--lean-root", str(lean),
                       "--output", str(output / receipt)]
            # Only these locally supplied replay scripts run. No extracted code runs.
            process = subprocess.run(command, capture_output=True, text=True, check=False)
            (output / (script + ".stdout.log")).write_text(process.stdout)
            (output / (script + ".stderr.log")).write_text(process.stderr)
            commands.append({"script": script, "argv": command, "returncode": process.returncode,
                             "stdout_log": script + ".stdout.log", "stderr_log": script + ".stderr.log"})
        literal = json.loads((output / "literal-comparison.json").read_text()) if (output / "literal-comparison.json").is_file() else {}
        certificate = json.loads((output / "certificate-comparison.json").read_text()) if (output / "certificate-comparison.json").is_file() else {}
        passed = (all(command["returncode"] == 0 for command in commands)
                  and literal.get("check_count") == 1176 and not literal.get("failed_checks", [True])
                  and certificate.get("summary", {}).get("exact_lean_table_checks") == 42
                  and certificate.get("summary", {}).get("passed") is True)
        lean_paths = {Path(row["path"]) for row in literal.get("sources", [])}
        lean_paths.update(Path(row["path"]) for row in certificate.get("lean_source_inventory", []))
        lean_inventory = [file_record(path, lean) for path in sorted(lean_paths) if is_within(path, lean)]
        manuscript_inventory = [file_record(path, updated) for path in sorted(updated.rglob("*"))
                                if path.is_file() and not path.is_symlink()]
        original_paths = [original / "research/paper/final_rank5.tex", original / "research/rank6/paper/rank6_infinitude.tex", original / "research/rank7/paper/rank7_infinitude.tex"]
        original_paths.extend(Path(row["original"]["path"]) for row in certificate.get("assets", []))
        report = {
            "schema_version": 1, "generated_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "passed": passed, "literal_checks": literal.get("check_count"),
            "certificate_table_checks": certificate.get("summary", {}).get("exact_lean_table_checks"),
            "dependencies": {"python": platform.python_version(), "sympy": literal.get("dependencies", {}).get("sympy")},
            "inputs": {"updated": updated_record, "original": original_record, "lean_root": str(lean)},
            "commands": commands, "replay_sources": [file_record(scripts / name) for name in ["replay.py", "literal_compare.py", "certificate_compare.py"]],
            "updated_source_inventory": manuscript_inventory,
            "original_compared_source_inventory": [file_record(path, original) for path in sorted(set(original_paths)) if path.is_file()],
            "lean_compared_source_inventory": lean_inventory,
            "receipts": [file_record(path, output) for path in sorted(output.glob("*.json"))],
            "safety_and_scope": {"uploaded_scripts_executed": False, "uploaded_scripts_imported": False,
                                 "lean_invoked": False, "input_files_modified": False,
                                 "scope": "Finite read-only data/transcription/AST comparison; not a new kernel build or a proof of the prime theorem."}}
        (output / "replay-receipt.json").write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
        print(json.dumps({"passed": passed, "literal_checks": report["literal_checks"],
                          "certificate_table_checks": report["certificate_table_checks"],
                          "receipt": str(output / "replay-receipt.json")}, indent=2))
        return 0 if passed else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, zipfile.BadZipFile) as error:
        print(f"Manuscript replay failed: {error}", file=sys.stderr)
        sys.exit(2)
