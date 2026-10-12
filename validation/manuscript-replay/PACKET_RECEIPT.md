# Frozen portable comparison receipt

The final directory-input and actual ZIP-input replays both passed from an unrelated working directory (`/tmp`), using the clean `ec567-temp` repository. Each reproduced **1,176 literal checks** (rank 5: 461; rank 6: 358; rank 7: 357) and **42 certificate-to-Lean table checks** (14 per rank). The six assets retain all mathematical JSON fields and executable verifier ASTs after excluding the explicitly documented rank-5 metadata fields and module docstrings. Two assets are byte-identical to the originals; four contain documentary changes.

The complete final receipts and logs are in `verified-directory/` and `verified-zip/`. `portable-replay-status.json` records **26 passing regression and input-guard checks**, including semantic identity with both earlier frozen audits. Input-file references are normalized only for the cross-replay equality comparison; all numerical/check identities and the original check ordering are retained. Matrix traversal follows the original certificate JSON insertion order and requires exactly E0/E1/Ep0/Ep1.

This is a data/transcription/AST replay. No Lean compiler was run, no supplied verifier/build script was imported or executed, no checked repository file was changed, and no external action was taken. The scope limits concerning narrow cones, full local-field statements, displayed-point independence and the prime theorem remain explicit in the reports.

Dependencies: Python >=3.10, pinned SymPy 1.14.0; verified with Python 3.12.14. All portable scripts have zero workspace-specific hardcoded paths. `replay.py` accepts explicit updated/original ZIP-or-directory inputs and a source repository path. `literal_compare.py` and `certificate_compare.py` each accept four explicit path arguments. See README.md for commands.

Updated archive SHA256: `5d3f85d7f6a07c8e8382f2629a49449689746655b0c4d2edb319b0197523e75a`.

Original archive SHA256: `09591a0598f7ade20b0ed0cc3f1632073e297ed7122dedb8ba1a9746e8379592`.

## Frozen source hashes

| File | SHA256 |
| --- | --- |
| replay.py | d258e6369a86bba141ecf86a2c3fad50b72471f39eb0f34d2c8405a128828d5d |
| literal_compare.py | d8b2514a984ec15d296d9872927c439795366a20b6ee081a13a5050a497b852c |
| certificate_compare.py | 308669cb0a99a88bbfae60e720755d9fde52c40bb89b9488244981eeaf65b33a |
| verify_packet.py | ca87d7408a6971461f1db6f494846f27d0bff66fbc0a831f165943f4ffb24e1e |
| requirements.txt | 25f9f1fb1988b230147a1d3092d34e09c069eb7a6c6d6df46b3973b9f2d36efc |
| README.md | b3ef793b6d845b9a62ccc6b2fc469a7204f248fb382a812465ddc8236288bea0 |

The source/audit packet is frozen by `packet-manifest.json`. Failed intermediate guard-regression receipts and Python bytecode caches have been removed; only the final passing checkpoints are retained.

## Copy mapping

Copy the four `.py` files, `requirements.txt` and README.md into the target's `scripts/manuscript/`. Copy `portable-replay-status.json`, `PACKET_RECEIPT.md`, `packet-manifest.json`, and the two final receipt directories into `validation/manuscript-replay/`. These are independent artifacts; this agent has not changed the target repository.
