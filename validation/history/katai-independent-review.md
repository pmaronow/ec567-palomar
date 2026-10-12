# Independent semantic review of the Kátai checkpoint

Reviewed the three frozen source modules below, including the latest large-prime-window endpoints. The mathematical statement and error structure pass independent semantic review. This review is read-only and does not replace the separate kernel build or exhaustive transitive axiom audit.

| Source | SHA-256 |
| --- | --- |
| `FiniteKatai.lean` | `1460dc67312e2b6cdbc11bd94e06ff8dd72c38232b9de1bbabc5efa43a2b8a80` |
| `PrimeDivisorMoments.lean` | `60a7fc1636959869f586d9d413792efe1cdb9e96fcdc033eaba65e2492c9f283` |
| `KataiAsymptotic.lean` | `1d8f158a825fa4b57070a3385892c056a69fc43edaa48d263d3567badaff5027` |

The interval is exactly the positive indices `1 ≤ n ≤ N`; zero is excluded. Dilation correlations are the literal products `a(p*m) * conjugate(a(q*m))`. The finite amplification uses the exact cutoff `floor(N/max(p,q))`, retaining each actual off-diagonal correlation norm. It does not substitute additive shifts for multiplication or move endpoints without accounting for them.

Multiplicativity is required only when the factors are coprime. For a prime `p`, its sole failure in `f(p*m)=f(p)f(m)` occurs when `p` divides `m`; after the original `m≤floor(N/p)` cutoff, there are exactly `floor(N/p²)` such indices. The error bound `2*floor(N/p²)` follows from one-boundedness of both products. Summing this error gives the explicitly retained square-divisor term.

Writing `S = sum_{p in P}1/p`, the actual divisor frequency has first moment `sum floor(N/p)` and second moment with diagonal `floor(N/p)` and distinct-prime term `floor(N/(p*q))`. These give the legitimate upper variance bound `N*S + 2*S*|P|`. The Gram expansion is an exact square before taking real parts and correlation norms; diagonal contributions are bounded by `N*S`. The final finite inequality therefore retains the frequency-variance error, the diagonal plus actual off-diagonal mass, and the square-divisor error. Empty prime windows cause no division or unsound positivity assertion in the finite theorem.

The asymptotic argument chooses a finite prime window first. For that fixed window, its finite collection of normalized dilation correlations tends to zero, including the truncation `floor(N/max(p,q))`; the normalization by `N` is justified by comparison with the normalized truncated length. The finite-window remainder tends to at most `(2*sqrt(S)+2*reciprocalSquareTotal)/S`. Divergence of prime reciprocals permits `S` to be arbitrarily large, and the reciprocal-square total is finite, so this remainder tends to zero. The argument has the required order of quantifiers and does not interchange an uncontrolled growing prime window with a pointwise correlation limit.

`AdmitsLargeOrthogonalPrimeWindows` is the explicit weaker analytic premise: for every real threshold it supplies a finite prime window with reciprocal mass above that threshold and decay for every distinct pair in the window. The latest endpoint uses this premise directly; all-prime decay implies it using actual prime-reciprocal divergence. A future exceptional-pair theorem must genuinely produce such windows, or use the finite weighted error inequality. Merely bounding the number of exceptional pairs does not prove window extraction with unbounded reciprocal mass.

The arbitrary fixed bound `C>0` is handled correctly by scaling `a` by `1/C`, scaling correlations by `c*conjugate(c)`, applying the one-bounded criterion, and scaling the conclusion back. The Möbius corollaries use the actual mathlib Möbius function cast from integers to complex numbers, its actual absolute bound, and its coprime multiplicativity.

**Scope limit:** the endpoints prove qualitative cancellation for a fixed sequence `a` under their stated prime-dilation hypothesis. They do not prove the hypothesis for arbitrary native niltests and do not provide an estimate uniform over a family of polynomial orbits chosen depending on `N`. In particular `a≡1` has dilation correlation average `1`; joint-dilation niltest representation supplies geometry, not decay. The mean/rational component and genuinely nontrivial vertical component require separate arithmetic and equidistribution arguments before these conditional endpoints can prove nilsequence Möbius orthogonality.

The original package build was reported clean by its owner. At the time of this review, the owner was correcting and rerunning the exhaustive axiom audit; its earlier log still contained counter/message typing errors. No completed exhaustive audit is certified by this independent semantic review. The root's promoted copies may change import and namespace qualifications; their new source hashes and audit must be recorded separately.
