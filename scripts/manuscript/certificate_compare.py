#!/usr/bin/env python3
"""Compare six certificate assets and 42 Lean tables without running archive code."""
import argparse
import ast
import datetime
import difflib
import hashlib
import json
from pathlib import Path
import re
import sys


def sha(data):
    return hashlib.sha256(data).hexdigest()


def record(path):
    return {"path": str(path), "bytes": path.stat().st_size,
            "sha256": sha(path.read_bytes())}


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def differences(original, updated, pointer=""):
    if type(original) is not type(updated):
        return [{"path": pointer or "/", "original": original, "updated": updated}]
    if isinstance(original, dict):
        result = []
        for key in sorted(set(original) | set(updated)):
            child = pointer + "/" + key
            if key not in original:
                result.append({"path": child, "change": "added", "updated": updated[key]})
            elif key not in updated:
                result.append({"path": child, "change": "removed", "original": original[key]})
            else:
                result.extend(differences(original[key], updated[key], child))
        return result
    if isinstance(original, list):
        if len(original) != len(updated):
            return [{"path": pointer, "original": original, "updated": updated}]
        return [row for i, (a, b) in enumerate(zip(original, updated))
                for row in differences(a, b, pointer + "/" + str(i))]
    return [] if original == updated else [{"path": pointer, "original": original, "updated": updated}]


def executable_ast(text):
    """ast.parse is inspection only: the returned tree is never executed."""
    tree = ast.parse(text)
    if (tree.body and isinstance(tree.body[0], ast.Expr)
            and isinstance(tree.body[0].value, ast.Constant)
            and isinstance(tree.body[0].value.value, str)):
        tree.body = tree.body[1:]
    return ast.dump(tree, include_attributes=False)


def root_with_marker(root, suffix, marker):
    root = root.resolve()
    candidates = [root / suffix, root]
    found = [p for p in candidates if (p / marker).is_file()]
    if not found and root.is_dir():
        found = [p / suffix for p in sorted(root.iterdir())
                 if p.is_dir() and (p / suffix / marker).is_file()]
    if len(found) != 1:
        raise ValueError(f"Expected one recognized layout at {root}; found {found}")
    return found[0]


def section(text, rank):
    return text.split(f"namespace Rank{rank}\n", 1)[1].split(f"\nend Rank{rank}", 1)[0]


def def_value(text, name):
    match = re.search(r"^def " + re.escape(name) + r"\s*:[^\n]*?:=\s*(.+)$", text, re.M)
    if match is None:
        raise ValueError(f"Missing literal Lean definition {name}")
    return match.group(1).strip()


def integers(text):
    # The exact supported Lean table syntax contains integers and punctuation only.
    if re.fullmatch(r"[0-9\s,\[\]()⟨⟩!+\-]+", text) is None:
        raise ValueError(f"Nonliteral Lean table expression: {text!r}")
    return [int(value) for value in re.findall(r"-?\d+", text)]


def tuples(text, arity):
    values = integers(text)
    if len(values) % arity:
        raise ValueError(f"Table length is not divisible by {arity}")
    return [values[i:i + arity] for i in range(0, len(values), arity)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--updated-dir", type=Path, required=True)
    parser.add_argument("--original-dir", type=Path, required=True)
    parser.add_argument("--lean-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    updated = root_with_marker(args.updated_dir, "source", "sections/06-rank5.tex")
    original = root_with_marker(args.original_dir, "research", "paper/final_rank5.tex")
    lean = root_with_marker(args.lean_root, "RankCertificates", "Rank5.lean")
    asset_paths = [
        ("rank5/final155_certificate.json", "paper/final155_certificate.json"),
        ("rank5/verify_final155_certificate.py", "paper/verify_final155_certificate.py"),
        ("rank6/rank6_certificate.json", "rank6/paper/rank6_certificate.json"),
        ("rank6/verify_rank6_certificate.py", "rank6/paper/verify_rank6_certificate.py"),
        ("rank7/rank7_certificate.json", "rank7/paper/rank7_certificate.json"),
        ("rank7/verify_rank7_certificate.py", "rank7/paper/verify_rank7_certificate.py"),
    ]
    assets = []
    for new_name, old_name in asset_paths:
        new_path = updated / "certificates" / new_name
        old_path = original / old_name
        item = {"name": new_name, "updated": record(new_path), "original": record(old_path),
                "byte_identical_to_original": new_path.read_bytes() == old_path.read_bytes()}
        if new_path.suffix == ".json":
            old_data = json.loads(old_path.read_text())
            new_data = json.loads(new_path.read_text())
            excluded = {"coordinate", "review_status"} if new_path.name == "final155_certificate.json" else set()
            old_math = {key: value for key, value in old_data.items() if key not in excluded}
            new_math = {key: value for key, value in new_data.items() if key not in excluded}
            item.update(json_differences=differences(old_data, new_data),
                        ignored_documentary_fields=sorted(excluded),
                        all_mathematical_fields_identical=old_math == new_math,
                        mathematical_fields_canonical_json_sha256=sha(canonical(new_math).encode()))
        else:
            old_text, new_text = old_path.read_text(), new_path.read_text()
            old_ast, new_ast = executable_ast(old_text), executable_ast(new_text)
            item.update(executable_ast_identical_after_removing_module_docstring=old_ast == new_ast,
                        executable_ast_sha256=sha(new_ast.encode()),
                        unified_text_diff="".join(difflib.unified_diff(old_text.splitlines(True), new_text.splitlines(True), fromfile=str(old_path), tofile=str(new_path))),
                        execution_status="Parsed with ast.parse only; never imported or executed.")
        assets.append(item)

    texts = {name: (lean / name).read_text() for name in ["MatrixCertificates.lean", "PrimePatterns.lean"]}
    checks = []
    normalization_checks = []

    def check(rank, field, filename, declaration, expected, actual, method="literal numeric transcription"):
        content = texts[filename]
        body = section(content, rank)
        prefix = f"namespace Rank{rank}\n"
        pos = content.index(prefix) + len(prefix) + body.index("def " + declaration + " ")
        owner = "MatrixCertificates" if filename == "MatrixCertificates.lean" else "PrimePatterns"
        row = {"rank": rank, "json_field": field, "lean_file": str(lean / filename),
               "lean_declaration": f"RankCertificates.{owner}.Rank{rank}.{declaration}",
               "line": content[:pos].count("\n") + 1, "equal": expected == actual,
               "method": method, "value": actual}
        if expected != actual:
            row["expected"] = expected
        checks.append(row)

    for rank, name in [(5, "rank5/final155_certificate.json"), (6, "rank6/rank6_certificate.json"), (7, "rank7/rank7_certificate.json")]:
        data = json.loads((updated / "certificates" / name).read_text())
        matrix = section(texts["MatrixCertificates.lean"], rank)
        primes = section(texts["PrimePatterns.lean"], rank)
        if set(data["matrices"]) != {"E0", "E1", "Ep0", "Ep1"}:
            raise ValueError(f"Rank {rank} certificate must have exactly four matrix tables")
        for key in data["matrices"]:
            check(rank, "/matrices/" + key, "MatrixCertificates.lean", key, data["matrices"][key], integers(def_value(matrix, key)))
        for side in ["E", "Ep"]:
            key = "known_vectors" if rank == 5 else "known_codes"
            check(rank, "/" + key + "/" + side, "MatrixCertificates.lean", side + "generators", data[key][side], integers(def_value(matrix, side + "generators")))
        forms = [[row["a"], row["b"]] for row in data["forms"]] if rank == 5 else data["forms"]
        cofactors = data["ci"] if rank == 6 else data["cofactors"]
        check(rank, "/forms", "PrimePatterns.lean", "forms", forms, tuples(def_value(primes, "forms"), 2))
        check(rank, "/ci" if rank == 6 else "/cofactors", "PrimePatterns.lean", "cofactors", cofactors, integers(def_value(primes, "cofactors")))
        lattice = ({"W": int(data["modulus"]), "M0": int(data["M_residue"]), "N0": data["N_residue"]} if rank == 5 else
                   data["lattice"] if rank == 7 else {key: data[key] for key in ["W", "M0", "N0"]})
        for key in ["W", "M0", "N0"]:
            field = "/lattice/" + key if rank == 7 else {"W": "/modulus", "M0": "/M_residue", "N0": "/N_residue"}[key] if rank == 5 else "/" + key
            check(rank, field, "PrimePatterns.lean", key, lattice[key], int(def_value(primes, key)))
        width, m0, n0 = (lattice[key] for key in ["W", "M0", "N0"])
        outputs = []
        for (a, b), cofactor in zip(forms, cofactors):
            if not cofactor or any(value % cofactor for value in [a * width, b * width, a * m0 + b * n0]):
                raise ValueError(f"Rank {rank} output has a nonintegral normalization")
            outputs.append([a * width // cofactor, b * width // cofactor, (a * m0 + b * n0) // cofactor])
        if rank == 5:
            normalization_checks.append({"rank": rank, "check": "JSON prime_forms equal exact normalized forms", "passed": outputs == [[row["X"], row["Y"], row["constant"]] for row in data["prime_forms"]]})
        check(rank, "/prime_forms" if rank == 5 else "/forms + cofactors + lattice", "PrimePatterns.lean", "outputs", outputs, tuples(def_value(primes, "outputs"), 3), "exact integer normalization from JSON forms, cofactors and lattice")
        crt = ([[row["modulus"], row["M"] % row["modulus"], row["N"] % row["modulus"]] for row in data["congruences"]] if rank == 5 else
               [[int(modulus), *values] for modulus, values in data["moduli"].items()] if rank == 6 else
               [[row["modulus"], row["M"], row["N"]] for row in data["states"]])
        check(rank, "/congruences" if rank == 5 else "/moduli" if rank == 6 else "/states", "PrimePatterns.lean", "crt", crt, tuples(def_value(primes, "crt"), 3), "CRT residues normalized modulo their listed modulus")
        retained = data["crt_primes"] if rank < 7 else sorted({2 if modulus == 512 else 3 if modulus == 81 else modulus for modulus, _, _ in crt})
        check(rank, "/crt_primes" if rank < 7 else "/states (underlying prime moduli)", "PrimePatterns.lean", "retainedPrimes", retained, integers(def_value(primes, "retainedPrimes")))
        for side, rows in data.get("fixed_rows", {}).items():
            normalization_checks.append({"rank": rank, "check": f"fixed_rows.{side} equals both matrix prefixes", "passed": rows == data["matrices"][side + "0"][:len(rows)] == data["matrices"][side + "1"][:len(rows)]})

    mathematical = all(item.get("all_mathematical_fields_identical", True) for item in assets)
    executable = all(item.get("executable_ast_identical_after_removing_module_docstring", True) for item in assets)
    table_success = len(checks) == 42 and all(row["equal"] for row in checks)
    normalization_success = all(row["passed"] for row in normalization_checks)
    success = mathematical and executable and table_success and normalization_success
    report = {
        "schema_version": 2, "generated_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "scope": "Read-only original/updated certificate data, verifier ASTs, and 42 exact Lean table comparisons.",
        "safety_and_scope": {"attached_python_scripts_executed": False, "attached_python_scripts_imported": False,
                             "lean_compiler_invoked": False, "target_core_challenge_solution_modified": False},
        "summary": {"asset_count": len(assets), "byte_identical_to_original_count": sum(item["byte_identical_to_original"] for item in assets),
                    "mathematical_json_data_unchanged": mathematical, "verifier_executable_ast_unchanged": executable,
                    "exact_lean_table_checks": len(checks), "all_exact_lean_table_checks_passed": table_success,
                    "normalization_and_fixed_prefix_checks_passed": normalization_success, "passed": success},
        "assets": assets, "lean_table_checks": checks, "normalization_and_fixed_prefix_checks": normalization_checks,
        "lean_source_inventory": [record(lean / name) for name in texts],
        "limitations": ["Text/data equality is not a fresh Lean kernel build or an execution of the manuscript verifiers.",
                        "The attached verifier scripts are inspected with ast.parse; no supplied Python code is evaluated.",
                        "Only the explicitly listed documentary rank-5 JSON fields and module docstrings are ignored when testing unchanged mathematics/code."]}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({"report": str(args.output.resolve()), "sha256": sha(args.output.read_bytes()), "summary": report["summary"]}, indent=2))
    return 0 if success else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, IndexError, SyntaxError) as error:
        print(f"Certificate replay failed: {error}", file=sys.stderr)
        sys.exit(2)
