#!/usr/bin/env python3
"""Run the pinned Palomar Comparator and three kernels locally, without submission.

Requires an already built project, the exact PalomarSubmission checkout,
the official Lean rc3 toolchain, and bubblewrap 0.12.0. Nothing is installed.
The output directory contains local exports; do not commit or upload them.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

TOOLCHAIN = "leanprover/lean4:v4.35.0-rc3"
SUBMISSION_REV = "d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44"
MATHLIB_REV = "c55e6e786f49471c72fbddbec5415808896aec1e"
LEAN_REV = "470d5ce1400764999581fd26d5d72b00d990b0f4"
RELEASE_SOURCE_HASHES = {
    "src/lean/LeanExport.lean": "ec95c53d108c5b014e7a53d6b88a4dbe41dc75c2e55102b2f8211268fcb94cf5",
    "src/lean/lake/Lake/CLI/Check.lean": "55daf430e5adea38453b21798cbdf4cd099f66ec969494022a566a8ae098c00b",
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def digest(path: Path) -> str:
    checksum = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            checksum.update(chunk)
    return checksum.hexdigest()


def write_json(path: Path, data: object) -> None:
    path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")


def git_head(path: Path) -> str:
    return subprocess.check_output(
        ["git", "-C", str(path), "rev-parse", "HEAD"], text=True
    ).strip()


def snapshot(project: Path, libraries: list[Path], metadata: list[Path]) -> dict[str, str]:
    paths = list(project.rglob("*.lean"))
    paths = [p for p in paths if ".lake" not in p.relative_to(project).parts]
    paths += [project / name for name in (
        "comparator.json", "lean-toolchain", "lake-manifest.json", "lakefile.toml"
    )]
    for library in libraries:
        paths += [p for p in library.rglob("*") if p.is_file()]
    paths += metadata
    return {str(p): digest(p) for p in sorted(set(paths))}


def assert_snapshot(expected: dict[str, str]) -> None:
    for filename, checksum in expected.items():
        require(digest(Path(filename)) == checksum,
                "An input changed during verification: " + filename)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path,
                        default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--palomar-submission", type=Path, required=True,
                        help="Clean official checkout at the documented pinned revision")
    parser.add_argument("--toolchain-prefix", type=Path,
                        help="Official Lean installation; otherwise resolved using elan")
    parser.add_argument("--output-dir", type=Path,
                        help="Parent for a new isolated local verification directory")
    parser.add_argument("--check-host-only", action="store_true",
                        help="Check pins, tool availability and user namespaces, without exports")
    args = parser.parse_args()
    project = args.project.resolve(strict=True)
    official_repo = args.palomar_submission.resolve(strict=True)
    require(git_head(official_repo) == SUBMISSION_REV,
            "Wrong PalomarSubmission revision")
    require(not subprocess.check_output(
        ["git", "-C", str(official_repo), "status", "--porcelain"], text=True
    ).strip(), "PalomarSubmission checkout must be clean")
    sys.path.insert(0, str(official_repo))
    try:
        from scripts import verify_submission as official
    except ImportError as error:
        raise RuntimeError("Install the pinned PalomarSubmission requirements.txt in your Python environment") from error

    require((project / "lean-toolchain").read_text().strip() == TOOLCHAIN,
            "Wrong project toolchain")
    environment = dict(ELAN_TOOLCHAIN=TOOLCHAIN, LEAN_NUM_THREADS="1",
                       LANG="C.UTF-8", LEAN_ABORT_ON_PANIC="1",
                       HOME="/tmp/home", TMPDIR="/tmp")
    if args.toolchain_prefix:
        prefix = args.toolchain_prefix.resolve(strict=True)
    else:
        discovery_env = {**os.environ, "ELAN_TOOLCHAIN": TOOLCHAIN}
        lean = subprocess.check_output(["elan", "which", "lean"],
                                       text=True, env=discovery_env).strip()
        prefix = Path(lean).resolve(strict=True).parent.parent
    version = subprocess.check_output(
        [str(prefix / "bin/lean"), "-j1", "-DautoImplicit=false", "--version"],
        text=True, env=environment
    ).strip()
    require("4.35.0-rc3" in version and LEAN_REV[:12] in version,
            "Lean binary does not match the pinned release")
    for relative, expected in RELEASE_SOURCE_HASHES.items():
        require(digest(prefix / relative) == expected,
                "Modified Lean release source: " + relative)
    tools = official.toolchain_tools(prefix)
    bwrap_command_path = shutil.which("bwrap")
    require(bwrap_command_path is not None, "Install the documented bubblewrap prerequisite")
    bwrap = Path(bwrap_command_path).resolve(strict=True)
    bwrap_version = subprocess.check_output([str(bwrap), "--version"], text=True).strip()
    require(bwrap_version == "bubblewrap 0.12.0", "Expected bubblewrap 0.12.0")
    environment.update(PATH=str(prefix / "bin") + ":" + os.defpath,
                       COMPARATOR_BWRAP=str(bwrap))
    initial_tools = official.tool_digests(tools, bwrap)
    kernels = official.protected_kernels(tools)
    config = official.load_comparator_config(project / "comparator.json")
    manifest = json.loads((project / "lake-manifest.json").read_text())
    packages = {}
    package_pins = {}
    for entry in manifest["packages"]:
        package = (project / manifest.get("packagesDir", ".lake/packages") /
                   entry["name"]).resolve(strict=True)
        require(git_head(package) == entry["rev"], "Wrong dependency revision: " + entry["name"])
        require(subprocess.run(["git", "-C", str(package), "diff", "--quiet", "HEAD"]).returncode == 0,
                "Modified tracked dependency files: " + entry["name"])
        packages[entry["name"]] = package
        package_pins[entry["name"]] = entry["rev"]
    require(package_pins.get("mathlib") == MATHLIB_REV, "Wrong Mathlib pin")
    mathlib = packages["mathlib"]
    require((mathlib / "lean-toolchain").read_text().strip() == TOOLCHAIN,
            "Mathlib has a different toolchain")

    def dependency_artifacts(owner: Path) -> list[Path]:
        metadata = json.loads((owner / "lake-manifest.json").read_text())
        directories = []
        for entry in metadata["packages"]:
            name = entry["name"]
            require(name in packages and package_pins[name] == entry["rev"],
                    "Nested dependency pin disagrees with project lockfile: " + name)
            # Lake shares transitive package checkouts in the root workspace;
            # a dependency's own .lake/packages directory is usually absent.
            directories.append(packages[name] / ".lake/build/lib/lean")
        # Some Lake-only dependencies have no Lean artifact directory.
        return [directory.resolve(strict=True) for directory in directories
                if directory.is_dir()]

    parent = args.output_dir.resolve() if args.output_dir else None
    if parent:
        parent.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="ec567-protected-", dir=parent))
    print("Local verification directory:", work, flush=True)
    system = sorted({p.resolve() for p in map(Path, ("/usr", "/bin", "/lib", "/lib64"))
                     if p.exists()})
    commands = []

    def confined(command: list[str], *, cwd: Path, readable: list[Path],
                 writable: list[Path] | None = None, paths: list[Path] | None = None,
                 stdout: Path | None = None, log_name: str, nested: bool = False) -> None:
        env = dict(environment)
        env["LEAN_PATH"] = os.pathsep.join(str(p) for p in (paths or []))
        argv = official.bwrap_command(
            command, bwrap=bwrap, writable_directories=writable or [],
            readable_paths=sorted({cwd, *readable, *(paths or []),
                                   *official.system_readable_paths()}),
            executable_paths=[prefix, bwrap, *system], environment=env,
            nested_sandbox=nested,
        )
        # The official helper filters environment names. Keep the explicit
        # toolchain/thread settings even inside the compilation namespaces.
        boundary = argv.index("--")
        argv[boundary:boundary] = [
            "--dir", "/tmp/home",
            "--setenv", "ELAN_TOOLCHAIN", TOOLCHAIN,
            "--setenv", "LEAN_NUM_THREADS", "1",
        ]
        started = time.monotonic()
        log_path = work / log_name
        with log_path.open("w") as log:
            if stdout:
                with stdout.open("w") as output:
                    proc = subprocess.run(argv, cwd=cwd, env=environment,
                                          stdout=output, stderr=log)
            else:
                proc = subprocess.run(argv, cwd=cwd, env=environment,
                                      stdout=log, stderr=subprocess.STDOUT)
        commands.append(dict(command=command, sandbox_command=argv,
                             exit_code=proc.returncode, log=str(log_path),
                             elapsed_seconds=round(time.monotonic() - started, 2)))
        write_json(work / "commands.json", commands)
        require(proc.returncode == 0, f"Command exited {proc.returncode}; inspect {log_path}")

    require(shutil.which("true") is not None, "Missing system true command")
    confined([str(Path(shutil.which("true")).resolve())], cwd=work,
             readable=[], writable=[work], log_name="sandbox-preflight.log", nested=True)
    host = dict(toolchain=TOOLCHAIN, lean_version=version, bubblewrap=bwrap_version,
                tool_digests=initial_tools, dependency_pins=package_pins,
                release_source_hashes=RELEASE_SOURCE_HASHES,
                submission_revision=SUBMISSION_REV, kernels=kernels)
    write_json(work / "host-preflight.json", host)
    if args.check_host_only:
        print("HOST PREFLIGHT PASS", work, flush=True)
        return

    require((project / ".lake/build/lib/lean/EC567Solution.olean").is_file(),
            "Build the project before protected verification")
    trusted_paths = [*dependency_artifacts(mathlib),
                     mathlib / ".lake/build/lib/lean", prefix / "lib/lean"]
    candidate_paths = [project / ".lake/build/lib/lean",
                       *dependency_artifacts(project), prefix / "lib/lean"]
    dependency_metadata = [package / "lake-manifest.json" for package in packages.values()
                           if (package / "lake-manifest.json").is_file()]
    inputs = snapshot(project, sorted(set(trusted_paths + candidate_paths)),
                      dependency_metadata + [prefix / name for name in RELEASE_SOURCE_HASHES])
    write_json(work / "input-snapshots.json", inputs)
    protected = official.protected_comparator_config(
        project / "comparator.json", work / "protected-comparator.json", kernels=kernels
    )
    alias = json.loads(protected.read_text())["challenge_module"]
    source = work / "canonical/src" / Path(*alias.split(".")).with_suffix(".lean")
    source.parent.mkdir(parents=True)
    source.write_bytes((project / "EC567Challenge.lean").read_bytes())
    canonical_lib = work / "canonical/lib"
    canonical_object = canonical_lib / Path(*alias.split(".")).with_suffix(".olean")
    canonical_object.parent.mkdir(parents=True)
    print("Compiling canonical Challenge against pinned Mathlib only", flush=True)
    confined([str(tools["lean"]), "-j1", "-DautoImplicit=false",
              "--root=" + str(work / "canonical/src"), str(source),
              "-o", str(canonical_object)], cwd=work / "canonical/src",
             readable=[work / "canonical/src"], paths=trusted_paths,
             writable=[canonical_lib], log_name="canonical-challenge-compile.log")
    targets = official.comparator_export_targets(config, official.primitive_targets(prefix))
    exporter = prefix / "src/lean/LeanExport.lean"
    exports = work / "exports"
    exports.mkdir()
    for module, paths, name in (
        (alias, [canonical_lib, *trusted_paths], "challenge"),
        (config["solution_module"], candidate_paths, "solution"),
    ):
        print("Exporting", name, flush=True)
        confined([str(tools["lean"]), "-j1", "-DautoImplicit=false", "--run",
                  str(exporter), module, "--", *targets], cwd=work,
                 readable=[], paths=paths, stdout=exports / (name + ".export"),
                 log_name=name + "-export.log")
        official.verify_export(exports / (name + ".export"))
    assert_snapshot(inputs)
    require(official.tool_digests(tools, bwrap) == initial_tools, "Verifier binaries changed")

    judge = work / "judge"
    judge.mkdir()
    print("Judging exports with Comparator, con-ron, NanoDa and Lean", flush=True)
    confined([str(tools["lake"]), "comparator", "--config", str(protected),
              "--challenge-from-export", str(exports / "challenge.export"),
              "--solution-from-export", str(exports / "solution.export")], cwd=judge,
             readable=[protected, exports / "challenge.export", exports / "solution.export"],
             writable=[judge], log_name="comparator.log", nested=True)
    transcript = (work / "comparator.log").read_text()
    print(transcript, flush=True)
    for marker in (
        "con-ron kernel accepts the solution", "nanoda kernel accepts the solution",
        "Lean default kernel accepts the solution", "Your solution is okay!",
    ):
        require(re.search("^" + re.escape(marker) + "$", transcript, re.MULTILINE) is not None,
                "Required success marker missing: " + marker)
    assert_snapshot(inputs)
    require(official.tool_digests(tools, bwrap) == initial_tools, "Verifier binaries changed")
    write_json(work / "LOCAL_VERIFICATION_STATUS.json", dict(
        status="PASS local canonical Comparator + NanoDa + con-ron + Lean default",
        **host, source_compile_flags=["-j1", "-DautoImplicit=false"],
        input_snapshot=inputs, canonical_challenge_alias=alias,
        canonical_source_sha256=digest(source),
        exports={name: dict(bytes=(exports / (name + ".export")).stat().st_size,
                            sha256=digest(exports / (name + ".export")))
                 for name in ("challenge", "solution")},
        bubblewrap_enabled=True, sandbox_network_enabled=False,
        candidate_source_absent_from_judge=True, official_full_registry_workflow_run=False,
        official_cgroup_supervision_run=False, remote_write_or_submission_or_export_upload=False,
    ))
    print("LOCAL VERIFICATION PASS", work, flush=True)


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, OSError, subprocess.CalledProcessError) as error:
        print("Verification failed:", error, file=sys.stderr)
        sys.exit(1)
