The sources and paths below describe isolated session audits. They are not imported proof dependencies or files required to reproduce the main rank project. The pinned public revision and compatibility patch identify the inspected source.

# LeanCert assessment for the rank 5–7 formalization

LeanCert can help prove numerical inequalities and replay finite certificates with kernel verification. The inspected snapshot does **not** provide the missing theorem that the twelve specified affine forms are simultaneously prime at arbitrarily large specializations. Its analytic-number-theory templates do not turn finite numerical checks into that theorem.

## Snapshot and scope

Inspected read-only repository: `https://github.com/alerad/leancert`, commit `b772f2c376b1103f444a71fe910b146c0bc9b002`. The upstream Lean and mathlib pins are both `v4.34.1`; our rank project uses Lean `v4.35.0-rc3`. This assessment examines actual implementation and theorem statements, the README, and the upstream soundness guards. It does not claim a full local build or a full transitive audit of LeanCert's 314-module root closure.

A separate, small local compatibility test builds the exact `Verification` and `Table` modules under our Lean version, with the recorded changes below. The broader numerical tactic closure is being independently built by another agent; its result is separate from this report.

## Relevant capabilities and their limits

| Source/API | What it proves | Input still needed |
|---|---|---|
| `Validity/Bounds/Core.lean`, `verify_upper_bound`, `verify_strict_lower_bound` | Bounds for supported expressions over a certified rational interval | A successful Boolean certificate, expression support, and checked domains |
| Checked integration and finite-sum APIs | Rigorous integral enclosures and finite sum bounds | A finite partition or finite index range and a successful certificate |
| `Engine/Table.lean`, `TableCert.verify` | Every listed row satisfies its semantic claim | A project-specific row checker and a proved row-soundness theorem |
| `ANT/PrimeEuler.lean:83`, `verify_primeEulerOneMinusInv_interval` | An enclosure for a finite Euler product through `N` | A successful finite computation |
| `ANT/Dirichlet.lean:129`, `verify_dirichletSum_interval`; `ANT/Mertens.lean:167` | Bounds on finite weighted sums and finite prime sums | Supplied coefficient/weight bounds and finite certificates |
| `Engine/Chebyshev/Theta.lean:691`, `verify_all_theta_rel_error` | A relative error bound throughout the checked range `start ≤ N ≤ limit` | The finite range certificate; it says nothing beyond `limit` |
| `Validity/Eventual.lean`, `verify_reciprocal_power_upper` | A genuine bound for every natural `n ≥ cutoff` | The specific supported form `q / n^k`, with nonnegative rational `q` and a positive exponent/cutoff |
| `ANT/Asymp/Env.lean`, `AsympEnv`; `Asymp/Checkers.lean`, `SlabTailCert` | Composition and consequences of global asymptotic envelopes | The all-large-`N` semantic envelope or symbolic tail proof is a field supplied by the project |
| `ANT/PNTCompilers.lean:32,58,100` | Transfers already-proved error bounds between abstract ψ, θ, π, and Li functions | Semantic decomposition identities and the analytic error bounds |

The last three rows are genuine unbounded mathematics. They are not automatic proofs of PNT, PNT in progressions, prime-pattern infinitude, or relative transference. In particular, `AsympEnv.cert` explicitly quantifies over every sufficiently large endpoint, and `SlabTailCert.tailBound` explicitly requires the tail proof. Inserting our desired conclusion in either field would leave the same obligation.

The repository also contains substantive analytic work on Gaussian Dirichlet series and the classical de Bruijn–Newman threshold (`Analysis/DBN/Threshold.lean`, `dbn_certificate`). It therefore should not be described as exclusively finite arithmetic. Those results concern zeros of particular entire functions and do not supply the required affine prime-pattern theorem. Inspection found no Green–Tao, Gowers inverse, nilsequence, prescribed-residue prime-AP, or general affine linear-forms endpoint.

For the current project, suitable uses would be explicit constants in a future analytic proof, finite prime-sum estimates, interval/integral sublemmas, or compact row-certificate replay. The existing finite descent and matrix certificates are already kernel-checked, and the new archive was independently reported byte-identical to the previously used seven assets. Neither importing LeanCert nor replaying those assets supplies the missing infinite existence input.

## Kernel trust routing

`Tactic/Verification.lean` is a real verification choke point, not merely a README promise:

- The option defaults to **native**. That branch calls `Lean.Meta.nativeEqTrue` and adds compiler/runtime trust.
- **Kernel** constructs `mkDecideProof`, reduces the decision, and retains the proof through `mkAuxLemma` with asynchronous validation disabled. Its failure branch is terminal; it never invokes native verification.
- **Auto** may bypass kernel verification through a cost gate or fall back after a failed kernel attempt. It is unsuitable for our standard-only dependency requirement unless the final theorem's dependencies are separately inspected.
- `#assert_trust kernel` checks transitive axioms and rejects compiler axioms, `sorryAx`, and unrecognized axioms. Upstream `Tests/TrustManifest.lean` pins representative golden theorems; `Tests/AxiomAudit.lean` includes exact axiom guards and namespace/environment sweeps. These files were inspected; their complete execution was not reproduced here.

If adopted, use `set_option leancert.trust "kernel"` or `(trust := kernel)`, and retain an independent final transitive axiom audit. The option controls certificate evaluation; it cannot erase native trust or placeholders inherited from other imported theorems.

## Explicit Li₂ boundary

`CertifiedBounds/Li2.lean` contains literal `sorry` proofs for `lower` and `upper`; `bounds` and `approx_1045` inherit them. `Examples/Li2Verified.lean` separately proves matching numerical statements, using `native_decide`, and its final metaprogram checks equality of their **types**. It neither replaces nor kernel-links the canonical placeholder proof bodies. Those canonical declarations cannot be used in a Palomar submission with no proof holes.

Comment-stripped import analysis gives these local-module closures:

| Import | Modules | Reaches canonical Li₂ placeholders |
|---|---:|---|
| `LeanCert` | 314 | No |
| `LeanCert.ANT` | 41 | No |
| `LeanCert.Tactic.LeanCert` | 134 | No |
| `LeanCert.CertifiedBounds` | 112 | Yes |

This is an import-boundary check, not a full trust certification of every declaration in those closures. The lexical scan of 494 project Lean files found exactly the two documented `sorry` tokens under `LeanCert`, no `admit` or `axiom` declaration token, and numerous legitimate native verification uses in demonstrations/tests. Details and source hashes are in `leancert-source-audit.json`.

## Local compatibility and verification evidence

Files are isolated in `leancert-kernel-audit435/`; the pinned shared repository and frozen rank sources are unchanged.

The exact upstream verification module first failed on historical native-axiom constant names, and then its kernel route rejected even `true = true`: Lean 4.35 represents `Decidable` using `Decidable.intro`, rather than the old `isTrue`/`isFalse` constructors. The recorded `compatibility.patch` makes two changes only:

1. Reduce the already-created `decide P` Boolean and recognize `Bool.true`/`Bool.false`, retaining the same `mkDecideProof` and eager kernel-validated `mkAuxLemma`.
2. Quote historical native-axiom names as unresolved names so the trust classifier can recognize them without requiring those obsolete constants to exist.

The copied modules build successfully. `KERNEL_ROUTE_AUDIT.lean` proves Boolean, natural arithmetic, and finite table certificates through strict kernel verification; all three proof terms have **no axioms**. Their semantic table consequence depends only on `propext` and `Quot.sound`. An independent negative check confirms a false certificate is rejected without assignment or new declarations. Every **420** declaration owned by the two copied modules, including private/generated declarations, passes a transitive allowlist containing only `propext`, `Classical.choice`, and `Quot.sound`.

Reproduction:

```sh
cd /workspace/work/analytic/leancert-kernel-audit435
export ELAN_HOME=/workspace/work/tooling/elan
export PATH=/workspace/work/tooling/elan/bin:$PATH
lake build LeanCert.Tactic.Verification LeanCert.Engine.Table
lake env lean KERNEL_ROUTE_AUDIT.lean
```

The final logs are `module-build-ported.log` and `route-audit-final.log`; `manifest.json` records provenance and hashes. These positive tests establish the small ported kernel/checker path, not numerical performance or complete library compatibility.
