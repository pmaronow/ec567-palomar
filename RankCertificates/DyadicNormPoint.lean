module

public import RankCertificates.PartnerNormReduction
public import RankCertificates.DyadicNorm

@[expose] public section

namespace RankCertificates.DyadicNormPoint

open LocalValuations PrimePowerResidues

/-- The genuine partner coordinate is a dyadic norm, and therefore its
normalized unit is one or three modulo eight. -/
theorem partner_coordinate_unit_eight (a : ℚ) (B : ℤ)
    (hB : (B:ZMod 8)=7) (hvB : padicValRat 2 (B:ℚ)=0)
    {x y : ℚ} (hx : x ≠ 0)
    (h : OnCurve (-2*a) (a^2-4*((2*B:ℤ):ℚ)) x y) :
    unitResiduePow 2 3 x=1 ∨ unitResiduePow 2 3 x=3 := by
  have hB0 : (B:ℚ) ≠ 0 := by
    exact_mod_cast (show B ≠ 0 from fun hz =>
      (by decide : (0:ZMod 8) ≠ 7) (by simpa only [hz,Int.cast_zero] using hB))
  have htwo : padicValRat 2 (2:ℚ)=1 := padicValRat.self (by norm_num)
  have hbeta : padicValRat 2 ((2*B:ℤ):ℚ)=1 := by
    simp only [Int.cast_mul,Int.cast_ofNat]
    rw [padicValRat.mul (by norm_num) hB0,htwo,hvB]
    omega
  obtain ⟨s,t,heq⟩ := PartnerNormReduction.partner_norm_representation hbeta hx h
  have hnorm : s^2-((2*B:ℤ):ℚ)*t^2 ≠ 0 := by
    rw [← heq]
    exact hx
  simpa only [← heq] using DyadicNorm.norm_unit_one_or_three B hB hvB hnorm

end RankCertificates.DyadicNormPoint
