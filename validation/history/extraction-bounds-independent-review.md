# ExtractionBounds semantic review

11 October 2026. Reviewed source:
`openai-inverse-audit/ExtractionBounds.lean`, SHA-256
`d6d473bb6e3e254e132e863066b0cc925bab6f24c67904adaea9acd93da1a0a9`.
The module was reviewed independently for statement meaning and proof
scope; its existing compilation and sampled axiom audits were supplied
separately by the parent agent.

**Verdict: no semantic defect found. Suitable for promotion as a genuine
finite extraction-bounds module.** It uses actual integer affine forms,
actual lattice points, actual mathlib von Mangoldt weights, and actual
natural-number primality. No prime-counting hypothesis or substitute
rank/prime predicate occurs.

The affine-level bound is correct: a nonzero first coefficient makes the
second-coordinate projection injective on a level, and vice versa.
The coordinate interval has exactly `2B+1` integer points. There is no
coprimality or primitive-form assumption, and the intercept and level may
be arbitrary integers. The same bound gives the finite-value exclusion
and the coincidence-line bound. The coincidence theorem requires
different linear parts; this follows from the manuscript's pairwise
nonproportionality assumption. Identical linear parts with different
intercepts would also have empty coincidence sets but are outside that
lemma's stated scope.

The proper-power cover is valid. If `p≥2`, `k≥2`, and `p^k≤X`, then
`p≤⌊√X⌋` and `k≤⌊log₂X⌋`. `powerCandidates` deliberately includes
extra values from bases zero/one and exponents zero/one, and sometimes
values larger than `X`; this only enlarges the finite cover. The later
theorem proves that every nonprime natural number with nonzero actual
von Mangoldt weight is a covered proper prime power. Thus the overcover
is an upper-bound device, not a weakened replacement for actual support.

The twelve-form weighted exclusion bound is also correct. Nonzero product
weight makes every factor nonzero. Since `Λ(0)=0`, a negative integer
output (whose `toNat` is zero) cannot enter the positive-weight support.
The `toNat` convention therefore gives the usual zero extension to
nonpositive integer inputs and introduces no false positive prime
patterns. A union bound contributes the factor twelve, and every factor
is bounded by `Real.log X`; the discarded mass is bounded by

```
12 (⌊√X⌋+1)(⌊log₂X⌋+1)(2B+1) (log X)^12.
```

The explicit assumptions are material and appropriate: every form has
nonzero linear part, all nonnegative outputs in the box are capped by
`X` through the stated `toNat` bound, and the weighted theorem requires
`X≥1`. For fixed affine coefficients, a cap `X=O(B)` can be derived
elementarily, but that derivation is not yet a theorem in this module.
The `B=0`, `X=0` counting cases and `X=1` weighted case cause no defect;
the exact formula retains the necessary `+1` terms.

The exact promotion boundary should remain clear. This module proves
finite counts and the nonprime-output mass bound. It does not yet prove
the `o(B²)` asymptotic when `X=O(B)`, weighted bounds for finite-value or
coincidence exclusions, restriction to the manuscript's convex sectors,
or positive surviving prime mass from a von Mangoldt asymptotic. Those
are downstream bridges. It supplies no finite-complexity prime-counting
theorem, Möbius/nilsequence orthogonality, Gowers uniformity, or prime
specialization infinitude. The description “size B sqrt(X) log(X)^13”
is an asymptotic shorthand; the actual proved finite bound above handles
small parameters correctly.

No main-project source was edited during this review.
