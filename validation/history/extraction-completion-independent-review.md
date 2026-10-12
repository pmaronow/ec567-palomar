# Independent review of the extraction completion

Reviewed by the root proof agent, separately from the agent that constructed
`FiniteExclusions`, `ExtractionAsymptotics`, `PrimeExtraction`, and
`PrimeAsymptoticBridge`. This is an AI agent review, not human peer review.
The exact frozen-source and promoted-source hashes are recorded in
`extraction-completion-promotion.json`.

The inspected definitions use the actual twelve-fold product
`∏ i, ArithmeticFunction.vonMangoldt ((ψ i).eval z).toNat`. Negative and zero
outputs receive their ordinary von Mangoldt value zero. Nonzero product
weight forces every output to be positive. No substitute prime weight or
rank predicate is introduced.

The finite discarded mass is bounded by the existing actual nonprime mass
bound plus the finite excluded-value and coincidence supports. The latter
supports lie in nonconstant affine level sets; the distinct linear-part
hypothesis makes each coincidence set a genuine affine line. Optional
additional excluded affine lines are also covered. All cardinality bounds
use the actual integer lattice square.

The analytic error bounds are proved, rather than assumed: for the linear
output cap `X = C(B+1)`, the proper-prime-power error and every fixed multiple
of the line error are `o(B²)`. The scaled variants use `B = K*T` with fixed
positive natural `C,K`. These asymptotics justify subtraction from a positive
quadratic lower bound for the actual weighted sum on the chosen regions.

Infinitude is stronger than finding one point at every scale. The proof
excludes an arbitrary finite set of candidate integer pairs by adding all
of their zeroth output values to the finite forbidden-value set. The proved
finite-value error remains subquadratic. The resulting good point lies
outside the arbitrary finite set, proving genuine set infinitude.

`PrimeAsymptoticBridge` accepts an explicit positive main coefficient and
an actual weighted error `o(T²)`; it derives the required lower bound and
then applies extraction. It supplies no prime-counting asymptotic itself.
The only conditional analytic input throughout this chain is the genuine
weighted lower bound or the displayed asymptotic that implies it.

The four original modules compiled before promotion and had an audit of
42 explicitly listed public declarations. The final main-project audit
covers their private and generated declarations as well. Promotion changes
only local import qualifications. All 92 preexisting proof modules are
byte-for-byte unchanged.
