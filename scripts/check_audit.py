"""Verify that the axiom auditor rejects a private axiom used by an export.

The intentional negative fixture exists only in a separate Lean stdin process;
no fixture declaration is written to this repository or imported by its proofs.
"""
import subprocess
import re
from pathlib import Path

root = Path(__file__).resolve().parents[1]
source = (root / "AxiomAudit.lean").read_text()
source = re.sub(r"(?m)^import all RankCertificates(?:\.[A-Za-z0-9_']+)*\n", "", source)
source = re.sub(r"(?m)^import all Solution\n", "", source)
source = source.replace("module\n", "module\nimport all RankCertificates.Common\n", 1)
source = source.replace("open Lean Elab Command", """namespace RankCertificates
private axiom audit_fixture : False
public theorem audit_fixture_export : False := audit_fixture
end RankCertificates

open Lean Elab Command""")
result = subprocess.run(["lake", "env", "lean", "-j1", "-DautoImplicit=false", "--stdin"], input=source,
                        text=True, capture_output=True, cwd=root)
output = result.stdout + result.stderr
if (result.returncode == 0 or "Forbidden axiom" not in output
        or "audit_fixture" not in output):
    raise SystemExit("Negative axiom-audit test failed:\n" + output)
print("Negative audit test passed: an exported theorem using a private custom axiom was rejected.")
