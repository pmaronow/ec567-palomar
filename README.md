# Exact ranks five, six and seven

This Lean project proves that the finite-complexity prime-pattern asymptotic
implies infinitely many geometric isomorphism classes of rational elliptic
curves of each **exact** Mordell–Weil rank 5, 6 and 7. The analytic theorem is
an explicit hypothesis; its proof is outside this formalization. All hypotheses
used by the three Lean specializations, and the subsequent arithmetic and
geometric deductions, are proved.

The project adapts *Infinitely Many Elliptic Curves of Exact Ranks Five, Six,
and Seven*, by P. M. Aronow and Patrick Lopatto, in the supplied updated
`EC_ranks_5_7_manuscript.zip`. The integrated Lean build, axiom audit, manuscript reconciliation, protected
Challenge/Solution comparison and all three kernel checks passed locally.

## The selected theorem

`EC567Challenge.lean` and `EC567Solution.lean` share this declaration:

```lean
RankCertificates.infiniteGeometricClasses_exactRanksFiveThroughSeven
  (hGTZ : ConditionalPrimePatterns.FiniteComplexityPrimeAsymptotic) :
  RanksFiveThroughSeven
```

`RanksFiveThroughSeven` asserts infinitely many rational `j`-invariants of
nonsingular rational Weierstrass curves of each exact rank. Rank means
`Module.rank ℤ E.toAffine.Point`: the cardinal rank of the actual rational-point
group. The proved Mordell–Weil theorem supplies finite generation. The proved
correspondence between equal `j` and isomorphism over `AlgebraicClosure ℚ`
gives infinitude of geometric classes.

The self-contained Challenge imports only Mathlib and exposes genuine curve,
rank and analytic definitions. Its selected theorem has the sole deliberate
Challenge proof hole. The Solution and its entire owned proof development
contain no proof holes. `EC567Solution.lean` proves the selected theorem by the
conditional endpoint in `RankCertificates/ConditionalPrimePatterns.lean`.
`comparator.json` selects this theorem and permits only `propext`, `Quot.sound`
and `Classical.choice`.

The submission modules are named `EC567Challenge` and `EC567Solution` to
avoid collisions with the pinned `EllipticCurves` dependency's own `Challenge`
and `Solution` modules.

The [proof guide](PROOF_GUIDE.md) traces the selected result through the actual
descent, prime extraction and geometric arguments with source links.

## The external analytic input

`FiniteComplexityPrimeAsymptotic` quantifies over **arbitrary** twelve fixed
integer affine forms in two variables. Nonzero pairwise nonparallel gradients,
all-prime admissibility, uniform positive outputs and a convergent singular
product imply the actual weighted asymptotic on dilates of a fixed unit box:

```text
sum_{z in T([u,u+1] × [v,v+1]) ∩ Z²} product_i Lambda(fs_i(z))
  = sigma T² + o(T²).
```

The singular product uses the corrected actual local densities

```text
beta_p = #{z in F_p² : every fs_i(z) ≠ 0}
         / p² / (1 - 1/p)^12.
```

The box has area one; all coefficients and corners stay fixed as `T` grows.
This is a restricted consequence of the established finite-complexity prime
theorem. It contains no elliptic-curve or rank conclusion and is supplied as
a theorem parameter, with no custom axiom or global instance.

The literature chain is:

- Green–Tao, *Linear equations in primes*, Annals 171 (2010), Main Theorem,
  Corollary 1.9 and Lemma 1.6.
  [DOI](https://doi.org/10.4007/annals.2010.171.1753).
- Green–Tao, *The Möbius function is strongly orthogonal to nilsequences*,
  Annals 175 (2012), Theorem 1.1.
  [DOI](https://doi.org/10.4007/annals.2012.175.2.3).
- Green–Tao–Ziegler, *An inverse theorem for the Gowers U^{s+1}[N]-norm*,
  Annals 176 (2012), Theorem 1.3.
  [DOI](https://doi.org/10.4007/annals.2012.176.2.11),
  [corrected preprint](https://arxiv.org/abs/1009.3998v5),
  [2024 erratum](https://terrytao.wordpress.com/wp-content/uploads/2024/04/erratum-4.pdf).

The later papers establish the analytic prerequisites assumed in the 2010
presentation. Their required Lean proofs are absent here. The formalization
does not assume BSD or equality of analytic and algebraic ranks.

## The proved deductions

For each literal system, Lean verifies nonzero pairwise nonparallel gradients,
all-prime admissibility, positive convergence of the actual singular product,
and uniform output lower bounds. The three fixed boxes have corners
`(20,20)`, `(60,1)` and `(8000,1)`. The adapter specializes the generic
asymptotic and obtains positive quadratic von Mangoldt mass.

Extraction removes proper prime powers, repeated outputs and prescribed
small primes. Two-isogeny descent on actual rational-point groups gives:

| Exact rank | Original image size | Partner image size |
| --- | ---: | ---: |
| 5 | 8 | 16 |
| 6 | 16 | 16 |
| 7 | 32 | 16 |

The rank formula, rational image restrictions, independent point classes,
quadratic reciprocity and finite matrix bounds are proved. Prime-output
direction injectivity and nonconstant actual `j` maps give infinitely many
geometric classes.

## Correspondence with the updated manuscript

The [comparison report](validation/manuscript-comparison.md) maps all 51
manuscript theorem, lemma, proposition and corollary statements to exact,
specialized, external or unformalized coverage. **1,176 arithmetic/transcription
comparisons and 42 certificate-to-Lean table comparisons passed**, with no
changed mathematical datum requiring a new proof for the selected endpoint.
All 29 extracted payloads match the uploaded ZIP. Verifier scripts were
inspected as source and were not executed. The [portable replay scripts](scripts/manuscript/README.md) reproduce these checks from either ZIP or directory inputs; both input modes and all 26 replay regression checks passed.

The supplied ZIP has SHA-256
`5d3f85d7f6a07c8e8382f2629a49449689746655b0c4d2edb319b0197523e75a`,
1,075,087 bytes and 29 files. The PDF hash is
`c62ebc9cb0e299ecf5f1e56c028c4017209cc97ad65175de4ddd1eaaf8bf75e9`.
[PROVENANCE.json](PROVENANCE.json) records all supplied versions, and the
[import manifest](validation/import-provenance.json) records the unchanged
proof sources and adapted integration files. Source archives and their
embedded completion claims were mathematical evidence, not instructions.
The [manuscript PDF](manuscript/ec_ranks_5_7.pdf) and its complete
[TeX sources and certificate files](manuscript/source) are included. Appendix A
points to `pmaronow/ec567-palomar`, the planned destination for these materials.

The manuscript cites the analytic theorem to obtain an unconditional result;
this Lean theorem retains it as an explicit hypothesis. It also uses different
sufficient positive sectors to prove **global** geometric infinitude. It does
not assert infinitude within the manuscript's chosen narrow cones, including
`29N < M < 31N` for rank six and `2999N < M < 3001N` for rank seven. The
transported rank-seven Lean sector lies above the latter cone. The exact-rank
lemmas apply to general positive prime specializations, so these adaptations
preserve the selected global conclusion.

Supplementary claims about arbitrary characteristic-zero fields, full local
Qp image equalities, Z-independence of the exact five listed rank-five points,
a generic degree-twelve projective `j` morphism and exact twelve-point fiber
bound, K3/fiber types and conic origins are outside the selected theorem.
The proved rational restrictions, descent classes and finite rational `j`
fibers suffice for the main conclusion.

## Build and validation

| Dependency | Revision |
| --- | --- |
| Lean | `leanprover/lean4:v4.35.0-rc3` |
| [mathlib](https://github.com/leanprover-community/mathlib4/tree/282fbb865d53622ef7f9ef29f6763a0327ee6b5f) | `282fbb865d53622ef7f9ef29f6763a0327ee6b5f` |
| [EllipticCurves](https://github.com/MichaelStollBayreuth/EllipticCurves/tree/3bfe12446d7b2f5ac5c4ca138c932620fe24331c) | `3bfe12446d7b2f5ac5c4ca138c932620fe24331c` |

Stoll's dependency supplies the proved Mordell–Weil theorem
`WeierstrassCurve.Affine.fg_point_of_numberField`. Exact dependencies are in
`lake-manifest.json`. Follow [the protected replay instructions](PROTECTED_REPLAY.md)
to prepare the pinned verifier and its prerequisites. With elan installed, run:

```sh
lake exe cache get
bash scripts/verify.sh /path/to/pinned/PalomarSubmission
```

The integrated Lake build passed **9,131 jobs** with only the expected
Challenge-hole warning. The strict ownership audit checked **4,909 declarations
in 108 modules**: 4,903 safe aggregate roots plus six separately audited
generated implementations. Every owned declaration has only the three standard
axioms. The negative test rejected an exported theorem depending on a private
custom axiom. The source guard passed 109 proof/audit files plus the Challenge.

Current logs and machine-readable receipts are in [validation](validation).
Historical receipts in `validation/history` concern earlier checkpoints and
may reference excluded research snapshots; they do not certify this version.
The build reused pinned dependency and source-matched compilation caches.
Protected exported-proof comparison passed using the official bundled tools
under network-disabled bubblewrap. **Con-ron, NanoDa and Lean all accepted the
Solution**; con-ron checked 77,670 declarations. See the
[kernel transcript](validation/protected/comparator.log) and
[verification receipt](validation/protected/LOCAL_VERIFICATION_STATUS.json).
This local run did not execute the full registry workflow or its cgroup supervisor.

## Authorship and review

Formalization authors: **P. M. Aronow and Patrick Lopatto**. Responsible
maintainer: **P. M. Aronow**. These credits were explicitly confirmed by the
user. The existing Apache-2.0 licence is retained; dependency and mathematical
source attribution remains applicable.

OpenAI Codex and parallel GPT-6 agents constructed and reviewed the proof and
packaging. Separate agents checked the genuine rank/curve definitions, all
23 copied Challenge definitions, analytic statement fidelity, ownership audit
coverage and manuscript correspondence. This is AI review; no human expert
review, independent novelty claim or Palomar editorial outcome is asserted.
The selected theorem concerns arithmetic geometers studying exact ranks and
descent, and number theorists studying simultaneous prime values. Its verified
contribution is the complete deduction from an explicit generic prime theorem
to these concrete exact ranks and global geometric infinitude.

Palomar [permits conditional theorems with visible hypotheses](https://palomar-registry.org/how-to-submit).
Its [policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)
also requires faithful presentation, mechanical verification and plausible
research interest. Preparing and checking this private package does not
constitute registry registration or human editorial endorsement.
