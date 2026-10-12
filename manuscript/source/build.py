#!/usr/bin/env python3
"""Run the three exact-arithmetic verifiers and compile the paper.

Usage (from the directory that contains this file):
    python3 build.py

Requires Python 3.10 or later (the verifiers use int.bit_count) and a TeX
installation with pdflatex and bibtex. The verifiers use only the Python
standard library. Their combined output is written to verification_output.txt.
"""
from pathlib import Path
import subprocess
import sys

if sys.version_info < (3, 10):
    sys.exit("build.py: Python 3.10 or later is required (found %s)." % sys.version.split()[0])

root = Path(__file__).resolve().parent
transcript = []
for name in (
    "certificates/rank5/verify_final155_certificate.py",
    "certificates/rank6/verify_rank6_certificate.py",
    "certificates/rank7/verify_rank7_certificate.py",
):
    result = subprocess.run([sys.executable, "-I", str(root / name)],
                            cwd=root, text=True, capture_output=True)
    transcript.extend([name, result.stdout, result.stderr])
    print(result.stdout, end="")
    if result.returncode != 0:
        print(result.stderr, end="")
        sys.exit("build.py: %s failed." % name)
(root / "verification_output.txt").write_text("\n".join(transcript))

def run(cmd):
    result = subprocess.run(cmd, cwd=root, text=True, capture_output=True)
    if result.returncode != 0:
        print(result.stdout[-4000:])
        sys.exit("build.py: %s failed." % " ".join(cmd))

run(["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "main.tex"])
run(["bibtex", "main"])
run(["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "main.tex"])
run(["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "main.tex"])
print("PASS: all three certificates; main.pdf compiled.")
