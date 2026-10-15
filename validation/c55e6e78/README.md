# Mathlib c55e6e78 verification

[`result.json`](result.json) summarizes the completed local checks for the
Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e` lockfile and the
EllipticCurves `71939de02eaa519ca47edcfb6cec38b1bb51eb4e` compatibility
snapshot. The logs, [`lockfile-check.json`](lockfile-check.json), and
[`source-snapshot.json`](source-snapshot.json) give the checked revisions and
source hashes.

The protected replay used the pinned official PalomarSubmission tooling. Its
[`comparator.log`](protected/comparator.log) records acceptance by con-ron,
NanoDa, and Lean. The complete local receipt has 133,433 input artifact hashes,
so it is stored as [`LOCAL_VERIFICATION_STATUS.json.gz`](protected/LOCAL_VERIFICATION_STATUS.json.gz);
[`summary.json`](protected/summary.json) records the uncompressed SHA-256 and
the export hashes. Proof exports and verifier binaries are not committed.
This is local technical verification, not registry submission or registration.
