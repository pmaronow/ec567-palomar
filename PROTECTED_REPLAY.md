# Private local protected replay

This replay checks the selected Challenge/Solution theorem locally. It never
changes repository visibility, writes to GitHub, submits to Palomar, registers
a formalization, or uploads an export. Keep the generated exports local.

The published theorem retains
`ConditionalPrimePatterns.FiniteComplexityPrimeAsymptotic` as an explicit
hypothesis. Kernel acceptance verifies the stated conditional theorem.

## Requirements

Use Linux with working unprivileged user namespaces, Python 3.11 or newer,
Git, the official `leanprover/lean4:v4.35.0-rc3` release, and bubblewrap
**0.12.0** already available on `PATH`. The script installs nothing. That Lean
release bundles `lake comparator`, `leanexport`, `leanchecker`, `nanoda_bin`
and `con-ron`; separate legacy Comparator/lean4export/Landrun installations
are unnecessary.

Use a Python environment containing the official tooling's pinned
`requirements.txt` dependencies (currently PyYAML 6.0.3). The optional virtual
environment commands below install those dependencies locally, without changing
system packages.

Build and audit this project first with `scripts/verify.sh`, following its
instructions for supplying the official verification-tool checkout. If
invoking the protected script separately, first complete the project's build,
source checks and owning-declaration axiom audit. The protected script requires
the resulting `EC567Solution.olean` and pinned dependency caches.

Prepare a clean checkout of the public official tooling at this exact revision:

```bash
palomar_tools=$(mktemp -d)
git clone https://github.com/PalomarRegistry/PalomarSubmission.git "$palomar_tools/PalomarSubmission"
git -C "$palomar_tools/PalomarSubmission" checkout --detach d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44
python3 -m venv "$palomar_tools/python"
"$palomar_tools/python/bin/python" -m pip install --require-hashes -r "$palomar_tools/PalomarSubmission/requirements.txt"
source "$palomar_tools/python/bin/activate"
```

These commands only read a public tooling repository. They do not publish this
private formalization. The script refuses a different revision or a modified
tool checkout.

## Run

From the formalization's root directory:

```bash
export ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0-rc3
export LEAN_NUM_THREADS=1
python3 scripts/verify_protected.py --palomar-submission "$palomar_tools/PalomarSubmission" --check-host-only
python3 scripts/verify_protected.py --palomar-submission "$palomar_tools/PalomarSubmission"
```

`--toolchain-prefix DIR` can specify an existing official Lean installation;
otherwise `elan which lean` resolves the pinned release. `--output-dir DIR`
chooses where the script creates a fresh verification directory. By default
it uses the system temporary directory. The script prints that directory and
preserves command records, logs, input snapshots, exports and the final status.

The full export is roughly 722 MB. Allow at least 16 GiB of RAM and several
GiB of temporary disk; the independent kernels can take tens of minutes.
The script runs the kernels sequentially and uses the official con-ron setting
of two workers. Source compilation and exporting use explicit `-j1` and
`-DautoImplicit=false`. The compiled `lake comparator` CLI has no `-j1` or
`-DautoImplicit=false` options; it judges these precomputed exports and invokes
the kernels without elaborating the project.

## What is checked

The script verifies the toolchain and dependency revisions, then copies the
Challenge bytes into an unpredictable canonical module. It compiles that
module against the pinned Mathlib environment only, without the candidate's
proof modules. Dependency tracked worktrees must be clean at their recorded
revisions. Their caches must come from a trusted build at those pins; an
unchanged artifact hash alone does not establish that provenance. It exports
both the canonical statement and the built Solution
using the release's integrated LeanExport entry point and the official target
list. Input and verifier hashes are checked before and after judgment,
including loaded dependency/toolchain library trees and the executed exporter
and primitive-target source files. The two source files are also checked against
fixed hashes from the pinned Lean release.

Compilation and exporting use the current official allowlist bubblewrap
builder. The outer judgment namespace contains only verifier-owned exports
and configuration, the pinned toolchain and required system files. It does
not mount the candidate's source or compiled proof tree. Network access is
disabled in every namespace. Comparator creates its own inner kernel
namespaces. The protected configuration requires both NanoDa and con-ron;
the project-supplied `comparator.json` cannot choose or disable those kernels.

Success requires exit zero and all four exact transcript lines:

```text
con-ron kernel accepts the solution
nanoda kernel accepts the solution
Lean default kernel accepts the solution
Your solution is okay!
```

Only after all checks succeed does the script write
`LOCAL_VERIFICATION_STATUS.json`. A plain `lake comparator comparator.json`
does not provide this complete protected replay.

This is a local technical verification, using the official bundled Comparator
and kernels. It does not run Palomar's registry workflow, cgroup supervisor,
admission review, or public visibility checks. It is not a registration or an
unconditional proof of the external analytic hypothesis.

## Pinned implementation sources

| Component | Revision |
| --- | --- |
| PalomarSubmission | `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44` |
| Lean / integrated Comparator and exporter | `470d5ce1400764999581fd26d5d72b00d990b0f4` (`v4.35.0-rc3`) |
| NanoDa source in that Lean release | `4c544ed4099c8227f07d5de77ad1e69fb0740a27` |
| con-ron source in that Lean release | `cb54c9a4e5f604a678b0230f96b8358b9fd73c82` |
| bubblewrap | `v0.12.0` |
| Mathlib | `282fbb865d53622ef7f9ef29f6763a0327ee6b5f` |

The final receipt records the actual local executable SHA-256 hashes. Exports
and binaries are not part of the private GitHub publication.
