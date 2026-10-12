# Independent LeanCert kernel numerical validation

Pinned pristine source: `alerad/leancert` revision
`b772f2c376b1103f444a71fe910b146c0bc9b002`, targeting Lean4.34.1.
The original checkout is unchanged. This isolated check uses cached
Lean4.35.0-rc3 and mathlib `282fbb865d53622ef7f9ef29f6763a0327ee6b5f`.

The compiled theorem in `src/GoldenKernelExample.lean` is exactly:

```
goldenKernelLogTwoUpper : Real.log 2 < 7 / 10
```

It has no mathematical hypotheses. The proof checks a genuine rational
interval certificate with `leancert_verify_cert` in strict kernel mode,
then applies LeanCert's proved `verify_strict_upper_bound` to obtain the
ordinary real-logarithm inequality. `golden-example.log` records successful
compilation, the exported type, and transitive axioms exactly
`[propext, Classical.choice, Quot.sound]`. An independent axiom allowlist
also passed: no `sorryAx`, `Lean.ofReduceBool`, native auxiliary axiom,
or other custom axiom is allowed.

`compatibility.patch` contains the sole source port: recognize reduced
`decide P` as `Bool.true/false` after Lean changed the `Decidable` constructors,
and quote historical native-axiom names without requiring those declarations
to exist in the new toolchain. `mkDecideProof`, eagerly kernel-validated
`mkAuxLemma`, and strict-mode routing remain unchanged. The source and patched
SHA256 hashes are recorded in `compatibility-manifest.json`.

`golden-closure-manifest.json` identifies the theorem's actual LeanCert
import closure, confirms every dependency compiled, and confirms only
`Verification.lean` differs from pristine source. `golden-artifact-sha256.txt`
freezes the test, patch, log, and manifests.

The larger frontend build was deliberately stopped after 85 logged modules
when the smaller numerical API was sufficient. The semantic `leancert`
frontend, whole library, native mode, and repository-wide theorem collection
are not validated by this test. No LeanCert source was added to the frozen
rank project. This result demonstrates trusted numerical assistance; it
supplies no arbitrary prime-pattern infinitude theorem and does not complete
the unconditional elliptic-curve infinitude goal.
