#!/usr/bin/env bash
set -euo pipefail
if [[ $# -ne 1 ]]; then
  printf '%s\n' 'Usage: bash scripts/verify.sh /path/to/pinned/PalomarSubmission' >&2
  printf '%s\n' 'See PROTECTED_REPLAY.md for tool setup and exact revisions.' >&2
  exit 2
fi
palomar_submission_path="$(cd "$1" && pwd)"
cd "$(dirname "$0")/.."
export ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0-rc3
export LEAN_NUM_THREADS=1
lake build
lake env lean -j1 -DautoImplicit=false -DwarningAsError=true AxiomAudit.lean
python3 scripts/check_sources.py
python3 scripts/check_audit.py
python3 scripts/verify_protected.py --palomar-submission "$palomar_submission_path"
