# EllipticCurves compatibility snapshot

This standalone Lake package starts from Michael Stoll's EllipticCurves commit
[`1e4709496a2c0cb3da66b400efbb15939358d444`](https://github.com/MichaelStollBayreuth/EllipticCurves/tree/1e4709496a2c0cb3da66b400efbb15939358d444).
The upstream source is licensed under Apache-2.0; its `LICENSE` and source
copyright notices are retained.

The source changes needed with Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e` are:

- `EllipticCurves/Mathlib/Basic.lean`: use
  `w.asIdeal.ramificationIdx B` in `exists_valuationOfNeZero_map_eq`.
- `EllipticCurves/WeakMordellWeil.lean`: use
  `w.asIdeal.ramificationIdx R` in `valuation_algebraMap_eq`.
- `EllipticCurves/Mathlib/AdicCompletionExtension.lean`: rewrite the old
  `ramificationIdx'` expression to Mathlib's `ramificationIdx R` using
  `Ideal.ramificationIdx'_eq_ramificationIdx` in the proof of
  `valued_adicCompletionExtension`. The theorem statement is unchanged.
- `EllipticCurves/Mathlib/FormalGroup.lean`: parenthesize the `Algebra.intNorm`
  term in singleton notation to avoid Lean's extended-binder parser reading it
  as a set comprehension. The theorem statement is unchanged.
- `EllipticCurves/InfiniteOrderExample.lean`: prove the two finite-field point
  equations using `norm_num` and `decide` because `grind` encounters a ring
  instance mismatch. Add a local `IsScalarTower ℤ ℤ (ZMod p)` instance for the
  residue-field point equivalence. The curve and point data and all theorem
  statements are unchanged.

The package configuration also pins Mathlib to that commit, uses Lean
`v4.35.0-rc3`, and regenerates `lake-manifest.json` for those dependencies.
No upstream Git history is included in this standalone snapshot.
