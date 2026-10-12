#!/usr/bin/env python3
"""Validate portable replay receipts and exercise input guards using local fixtures."""
import argparse
import ast
import collections
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import zipfile

sys.dont_write_bytecode = True


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_module(path, name):
    # Import only the trusted packet's own source, never an input archive member.
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory-replay", type=Path, required=True)
    parser.add_argument("--zip-replay", type=Path, required=True)
    parser.add_argument("--frozen-literals", type=Path)
    parser.add_argument("--frozen-certificates", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    replay = load_module(root / "replay.py", "ec567_trusted_replay")
    certificate_checker = load_module(root / "certificate_compare.py", "ec567_trusted_certificate_checker")
    literal_receipts = [json.loads((path / "literal-comparison.json").read_text()) for path in [args.directory_replay, args.zip_replay]]
    certificate_receipts = [json.loads((path / "certificate-comparison.json").read_text()) for path in [args.directory_replay, args.zip_replay]]
    replay_receipts = [json.loads((path / "replay-receipt.json").read_text()) for path in [args.directory_replay, args.zip_replay]]
    tests = []

    def check(name, success):
        tests.append({"name": name, "passed": bool(success)})

    for index, receipt in enumerate(replay_receipts):
        check(f"replay{index}: exact counts and pass", receipt["passed"] and receipt["literal_checks"] == 1176 and receipt["certificate_table_checks"] == 42)
        check(f"replay{index}: current script hashes", all(digest(root / Path(row["path"]).name) == row["sha256"] for row in receipt["replay_sources"]))
    def literal_key(rows):
        result = []
        for row in rows:
            row = dict(row)
            if Path(row["reference"]).is_absolute():
                row["reference"] = Path(row["reference"]).name
            result.append(row)
        return result

    check("directory/ZIP literal results identical modulo input paths", literal_key(literal_receipts[0]["checks"]) == literal_key(literal_receipts[1]["checks"]))
    table_key = lambda rows: [{key: row[key] for key in ["rank", "json_field", "lean_declaration", "value", "equal"]} for row in rows]
    check("directory/ZIP 42 table results identical", table_key(certificate_receipts[0]["lean_table_checks"]) == table_key(certificate_receipts[1]["lean_table_checks"]))
    if args.frozen_literals:
        frozen = json.loads(args.frozen_literals.read_text())
        check("all 1176 ordered checks equal frozen audit modulo input paths", literal_key(frozen["checks"]) == literal_key(literal_receipts[0]["checks"]))
    if args.frozen_certificates:
        frozen = json.loads(args.frozen_certificates.read_text())
        check("all 42 ordered checks equal frozen audit", table_key(frozen["lean_table_checks"]) == table_key(certificate_receipts[0]["lean_table_checks"]))

    with tempfile.TemporaryDirectory(prefix="ec567-guard-") as temporary_name:
        temporary = Path(temporary_name)
        for index, name in enumerate(["../escape.txt", "/absolute.txt", "C:drive.txt", "back\\slash.txt"]):
            archive = temporary / f"path{index}.zip"
            with zipfile.ZipFile(archive, "w") as source:
                source.writestr(name, "fixture")
            try:
                replay.safe_extract(archive, temporary / f"target{index}")
                rejected = False
            except ValueError:
                rejected = True
            check(f"unsafe ZIP path rejected: {name}", rejected)
        archive = temporary / "symlink.zip"
        entry = zipfile.ZipInfo("linked")
        entry.create_system = 3
        entry.external_attr = (0o120777 << 16)
        with zipfile.ZipFile(archive, "w") as source:
            source.writestr(entry, "../escape")
        try:
            replay.safe_extract(archive, temporary / "symlink-target")
            rejected = False
        except ValueError:
            rejected = True
        check("ZIP symlink rejected", rejected)
        archive = temporary / "unexecuted-script.zip"
        payload = "raise RuntimeError('This input fixture must never execute')\n"
        with zipfile.ZipFile(archive, "w") as source:
            source.writestr("verify_input.py", payload)
        replay.safe_extract(archive, temporary / "unexecuted-target")
        check("archive Python retained strictly as text", (temporary / "unexecuted-target/verify_input.py").read_text() == payload)

    for expression in ["__import__('os')", "[1, 2]; print(1)"]:
        try:
            certificate_checker.integers(expression)
            rejected = False
        except ValueError:
            rejected = True
        check(f"nonliteral Lean expression rejected: {expression}", rejected)
    check("AST comparator ignores documentary docstring/comments", certificate_checker.executable_ast('"old"\nx = 1\n') == certificate_checker.executable_ast('"new"\n# edited\nx = 1\n'))
    check("AST comparator detects executable changes", certificate_checker.executable_ast('x = 1\n') != certificate_checker.executable_ast('x = 2\n'))

    import sympy as sp
    from sympy.parsing.sympy_parser import parse_expr, standard_transformations, implicit_multiplication_application, convert_xor
    import re
    tree = ast.parse((root / "literal_compare.py").read_text())
    function = next(node for node in tree.body if isinstance(node, ast.FunctionDef) and node.name == "arithmetic_parse")
    namespace = {"sp": sp, "re": re, "parse_expr": parse_expr, "standard_transformations": standard_transformations,
                 "convert_xor": convert_xor, "TRANS": standard_transformations + (convert_xor, implicit_multiplication_application)}
    # Compile one function from our trusted packet, not any supplied source string.
    exec(compile(ast.Module(body=[function], type_ignores=[]), str(root / "literal_compare.py"), "exec"), namespace)
    for expression in ['__import__("os")', "M.__class__", "[M]", "M[0]", "1;2", "lambda:1", "x=1"]:
        try:
            namespace["arithmetic_parse"](expression, {"M": sp.Symbol("M"), "N": sp.Symbol("N")})
            rejected = False
        except ValueError:
            rejected = True
        check(f"non-arithmetic expression rejected: {expression}", rejected)
    forbidden_prefix = chr(47) + "workspace"
    check("no workspace hardcoding in replay sources", all(forbidden_prefix not in (root / name).read_text() for name in ["replay.py", "literal_compare.py", "certificate_compare.py", "verify_packet.py"]))
    report = {
        "passed": all(test["passed"] for test in tests), "test_count": len(tests), "tests": tests,
        "literal_checks": 1176, "certificate_table_checks": 42,
        "literal_checks_per_rank": dict(collections.Counter(row["rank"] for row in literal_receipts[0]["checks"])),
        "source_hashes": [{"path": name, "sha256": digest(root / name), "bytes": (root / name).stat().st_size} for name in ["replay.py", "literal_compare.py", "certificate_compare.py", "verify_packet.py", "requirements.txt", "README.md"]],
        "input_scope": "Directory and actual ZIP replays against the supplied clean Lean source repository; no compiler run.",
        "archive_scripts_executed_or_imported": False,
        "validation_receipts": [{"path": str(path / "replay-receipt.json"), "sha256": digest(path / "replay-receipt.json")} for path in [args.directory_replay, args.zip_replay]]}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"passed": report["passed"], "test_count": report["test_count"], "output": str(args.output)}, indent=2))
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
