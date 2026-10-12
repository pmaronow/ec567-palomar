# Portable manuscript comparison replay

This packet reproduces **1,176 family/literal checks and 42 certificate-to-Lean table checks** for the updated ranks 5–7 manuscript. It reads the updated manuscript, the original rank-5 repository archive, and a checked Lean source repository. It does not run or import uploaded verifier/build scripts, invoke Lean, or modify those inputs.

Requirements: Python 3.10 or later and `sympy==1.14.0`. The recorded replay used Python 3.12.14. `certificate_compare.py` and the ZIP wrapper use only the Python standard library. The original archive must contain `research/paper/final_rank5.tex`, `research/rank6/paper/rank6_infinitude.tex`, and `research/rank7/paper/rank7_infinitude.tex`; the earlier consolidated certificate-only archive is insufficient.

Install the sole third-party dependency in an environment of your choice:

```sh
python -m pip install -r /path/to/ec567-manuscript-replay/requirements.txt
```

Run from any working directory, using either ZIPs or extracted directories:

```sh
python /path/to/ec567-manuscript-replay/replay.py \
  --updated /path/to/EC_ranks_5_7_manuscript.zip \
  --original /path/to/rank-5-elliptic-curves-main.zip \
  --lean-root /path/to/ec567-temp \
  --output-dir /path/to/new-comparison-receipts
```

`--updated` also accepts the extracted root or its `source` directory. `--original` accepts the extracted repository root or its `research` directory. `--lean-root` accepts a repository containing `RankCertificates/*.lean` or that module directory itself. ZIPs may have a single enclosing directory. ZIP paths, links, duplicate members and expansion limits are checked before extraction into a temporary directory. The output directory must be absent or empty and must be outside all input directories.

The wrapper writes separate comparison JSON files, captured logs and `replay-receipt.json` with commands, input/source SHA256 hashes, dependency versions and result counts. It exits zero only if both check sets pass with exactly 1,176 and 42 checks, all six certificate assets retain their mathematical fields, and all three verifier scripts retain their executable ASTs after removing their module docstrings. Numerical expressions receive an arithmetic token/name allowlist before SymPy parsing. Uploaded Python is inspected with `ast.parse`, never evaluated.

The two checkers can also run separately, each with `--updated-dir`, `--original-dir`, `--lean-root`, and `--output`. They write only the specified JSON report. `literal_compare.py` preserves the original ordered checks; `certificate_compare.py` compares six assets, four matrices and two generator tables per rank, homogeneous forms, cofactors, three lattice constants, normalized outputs, CRT residues and retained primes. Exact normalization and fixed-row-prefix checks are reported in addition to the 42 table comparisons.

This replay establishes data/transcription consistency. It does not replace kernel compilation, certify the uploaded scripts, prove the external finite-complexity prime asymptotic, establish infinitude inside the paper's narrower cones, or prove the displayed five rank-5 points are linearly independent over the integers. The literal report retains those supplementary scope limits.

The historical source report used original hardcoded helpers `ec567-literal-audit/compare.py` and `ec567_certificate_compare.py`; those helpers are not dependencies of this portable packet. The portable scripts require no workspace-specific files or paths.

`verify_packet.py --directory-replay RECEIPT_DIR --zip-replay RECEIPT_DIR --output STATUS_JSON` validates both complete receipts, current replay-script hashes and semantic equality of all checks, and exercises unsafe-ZIP, non-arithmetic-expression and AST-change fixtures. Optional `--frozen-literals JSON` and `--frozen-certificates JSON` compare against the earlier audit. It imports only this packet's trusted checkers; its generated archive fixture contains Python text that is extracted without execution. The frozen `portable-replay-status.json` records these validations.
