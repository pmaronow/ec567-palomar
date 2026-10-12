# Independent semantic review

Reviewed the frozen source of `LiteralAffineSystems.lean` and `LiteralPrimeBridge.lean`, together with the immediate definitions of affine forms, extraction weights, prime patterns, prime specializations and the final rank proposition. No compiler was run; root's existing compilation and declaration-wide axiom audit are separate checks.

Reviewed source SHA256:

| File | SHA256 |
|---|---|
| `LiteralAffineSystems.lean` | `648992eec93101ccfc0e7ffd68c06ae569c839a6f4a4cede9ae5c2058cac5b7d` |
| `LiteralPrimeBridge.lean` | `42227ccc6cade64e905e97682d700ed5edcc43d47018d68ccdf23e06a6cc37d4` |

## Findings

No semantic defect was found in either module's stated conversion, bounds or bridge.

`fromAffine` copies all three integer coefficients without changing variables or signs. Its evaluation identity is definitional. `system5`, `system6` and `system7` are therefore precisely the existing twelve manuscript-lattice outputs, in their original order, rather than newly chosen prime systems.

The output cap is valid for the entire integer square, including negative outputs: it bounds absolute value by `(|a|+|b|)B+|c|`, then uses `toNat≤natAbs`. The uniform constant `3000000000000000` is independent of B. An independent arithmetic check of the literal coefficient arrays gives maximum coefficient bounds 6,892,794,540,368; 855,838,956,038; and 2,360,233,301,132,138 for ranks 5, 6 and 7. Each is below the stated cap. All forms are nonconstant; the literal pairwise determinants are nonzero. The deduction of unequal linear coefficient pairs from nonparallelity is correct and is exactly what removal of equality lines needs.

The sectors are closed integer rectangles of side length T, hence contain `(T+1)^2` points. Their bounding-square dilations are respectively 21, 61 and 8001. For each affine output, choosing the minimizing rectangle corner according to the signs of its coefficients gives a lower bound of the form `L*T+c`; checking `L≥1` and `L+c≥1` confirms the claimed output lower bound for every T≥1. The smallest outputs at T=1 are respectively 7,523,010,721; 871,420,043; and 459,848,503,307. Thus the lower-bound statements do refer to nonempty regions in the intended positive cone.

`primePattern_positivePrimeOutputs` correctly bridges the two representations. The extraction predicate requires actual positive integer values, primality of `toNat`, injectivity of those integer values, and exclusion from the cast image of the small-prime list. Positivity proves `toNat=natAbs` and `(natAbs:ℤ)=value`, so primality, distinctness and all exclusions transfer without an absolute-value sign ambiguity. The specialized exclusion lists `[2,3,5]`, `[2,3,7]` and `[2,3,7,13]` match the definitions of `PrimeSpecialization5/6/7` exactly.

The dilation and cap arguments passed to `primePattern_infinite_of_scaled_quadratic_lower` have matching scales: the region lies in `box (K*T)`, and every output is bounded by `literalCap*(K*T+1)`. The imported extraction theorem proves infinitude of actual integer prime tuples, not just positive Mangoldt support or arbitrarily large weighted sums. Removing the region-membership conjunct by set inclusion is valid. The subsequent rank bridge uses the existing theorem whose hypothesis is infinitude of the identical specialization predicate.

## Exact limitation of the final endpoint

`HasQuadraticMangoldtMass ψ R` is the explicit assertion

```text
∃ c>0, eventually T,
  c*T² ≤ ∑ z∈R(T), ∏ i:Fin 12, Λ((ψ i)(z).toNat).
```

`ranksFiveThroughSeven_of_quadraticMangoldtMass` assumes this assertion separately for each of the three literal systems and sectors. Its conclusion is `RanksFiveThroughSeven`, namely infinitely many geometric isomorphism classes of rational elliptic curves of exact ranks 5, 6 and 7, as defined by the imported specification. This is an honest conditional reduction. Neither reviewed module establishes the three quadratic mass hypotheses or an unconditional rank-infinitude theorem.

The sector positivity and cardinality lemmas are useful semantic data; the final extraction proof does not need them as premises because nonzero Mangoldt support already forces positive outputs. Their absence from that call is not a gap. The cap is intentionally loose, which affects constants but not the asymptotic reduction.

Promotion alongside the extraction-completion modules is semantically supported, provided the documentation preserves the explicit analytic hypotheses and compilation/axiom audit covers the imported endpoint. This review did not independently reprove the deep geometric rank and j-invariant infinitude results imported by `InfinitudeReduction`.
