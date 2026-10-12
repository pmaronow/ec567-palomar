module

public import EllipticCurves.MordellWeil
public import RankCertificates.Specification

/-!
# Finite generation of the actual rational point group

The Mordell–Weil theorem imported here is a proved theorem from Michael
Stoll's `EllipticCurves` library, pinned by the project manifest.  It applies
to the same `WeierstrassCurve.Affine.Point` group used in `rationalRank`.
Finite generation is therefore a conclusion for nonsingular rational
Weierstrass curves, rather than an additional hypothesis in these results.

No exact value of the rank is asserted.
-/

@[expose] public section

namespace RankCertificates

/-- Mordell–Weil finite generation of the genuine rational point group. -/
theorem rationalPoints_finitelyGenerated (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    IsAddFG E.toAffine.Point :=
  WeierstrassCurve.Affine.fg_point_of_numberField

/-- The actual rational point group is a finite `ℤ`-module in the sense of
finite generation.  This does not assert that its underlying set is finite. -/
instance rationalPoints_moduleFinite (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Module.Finite ℤ E.toAffine.Point :=
  Module.Finite.iff_addGroup_fg.mpr (rationalPoints_finitelyGenerated E)

/-- The cardinal rank agrees with finite rank for every nonsingular rational
Weierstrass curve, without a separate finite-generation hypothesis. -/
theorem rationalRank_eq_finrank (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    rationalRank E = (Module.finrank ℤ E.toAffine.Point : Cardinal) := by
  exact (Module.finrank_eq_rank ℤ E.toAffine.Point).symm

/-- The genuine rational Mordell–Weil rank is finite. -/
theorem rationalRank_lt_aleph0 (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    rationalRank E < Cardinal.aleph0 :=
  Module.rank_lt_aleph0 ℤ E.toAffine.Point

theorem rationalRank_exists_nat (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∃ r : ℕ, rationalRank E = (r : Cardinal) :=
  ⟨Module.finrank ℤ E.toAffine.Point, rationalRank_eq_finrank E⟩

theorem rationalRank_lt_aleph0_of_discriminant_ne_zero (E : WeierstrassCurve ℚ)
    (hΔ : E.Δ ≠ 0) : rationalRank E < Cardinal.aleph0 := by
  let : E.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  exact rationalRank_lt_aleph0 E

/-- Every genuine rational elliptic curve has some finite exact rank. -/
theorem RationalEllipticCurve.exists_exactRank (E : RationalEllipticCurve) :
    ∃ r : ℕ, HasExactRank E.model r :=
  rationalRank_exists_nat E.model

theorem hasExactRank_iff_finrank_eq_of_isElliptic (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (r : ℕ) :
    HasExactRank E r ↔ Module.finrank ℤ E.toAffine.Point = r :=
  hasExactRank_iff_finrank_eq E r

end RankCertificates
