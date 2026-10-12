# Additive van der Corput checkpoint

The isolated module `AdditiveVanDerCorput.lean` proves a genuine additive van der Corput criterion on the positive integer intervals `Ioc 0 N`. Its correlations are the actual sums

`additiveCorrelation a h N = ∑ n ∈ Ioc 0 N, a (n+h) * star (a n)`.

For every one-bounded complex sequence, its finite theorem proves

`H * ‖∑ n ∈ Ioc 0 N, a n‖ ≤ 2*H² + sqrt (N*(H*N + offDiagonalMass))`,

where the off-diagonal mass sums the norms of the actual pair correlations at shifts `h,k < H`. The translation boundary is at most `2h`; the `2H²` error is a coarse sum of those genuine boundary errors. The diagonal contribution is at most `H*N`.

The qualitative endpoint assumes cancellation of the displayed correlation for each fixed positive shift, normalized by `N`, and proves cancellation of the normalized original sum. The averaging window is fixed before passing to the limit in `N`, then its limit bound `sqrt H/H` tends to zero. A second endpoint handles every sequence bounded by a fixed positive constant through literal constant scaling.

This module does not assert any shift-correlation decay for a particular sequence. Polynomial phase cancellation is proved separately by the owning induction agent. The endpoint is qualitative for a fixed sequence; it provides no uniform rate for sequences depending on `N`.

The source builds warning-free with Lean v4.35.0-rc3 and the existing mathlib-only Kátai project. Its SHA256 is `a68a95eb2f3e252bce201b964ebd353cf08977e638d8b7c2dfc011fd303b869c`.

An independent semantic review by `/root/nilsequence_review` checked the literal intervals, ordered/reversed pair reductions, all finite errors, the order of limits, and fixed-bound scaling, and found no weakened substitute or omitted analytic premise. The exhaustive declaration axiom audit is recorded separately in `additive-verification-status.json` and `additive-axiom-audit.log`.
