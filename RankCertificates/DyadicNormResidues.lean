module

public import RankCertificates.PrimePowerPoints

@[expose] public section

namespace RankCertificates.DyadicNormResidues

open LocalValuations PrimePowerResidues

theorem norm_nonnegative (B : ℤ) {s t : ℚ}
    (hs : 0 ≤ padicValRat 2 s) (ht : 0 ≤ padicValRat 2 t) :
    0 ≤ padicValRat 2 (s^2-((2*B:ℤ):ℚ)*t^2) := by
  rw [show s^2-((2*B:ℤ):ℚ)*t^2=s^2+((-2*B:ℤ):ℚ)*t^2 by push_cast; ring]
  apply LocalSeven.valuation_nonnegative_add 2
  · rw [padicValRat.pow]; positivity
  · apply LocalSeven.valuation_nonnegative_mul 2
    · rw [padicValRat.of_int]; positivity
    · rw [padicValRat.pow]; positivity

/-- Direct residue of the genuine rational norm. The exact expression is
retained through the p-adic lift, without a dependent residue transport. -/
theorem norm_residue (k : ℕ) (B : ℤ) {s t : ℚ}
    (hs : 0 ≤ padicValRat 2 s) (ht : 0 ≤ padicValRat 2 t) :
    residuePow 2 k (s^2-((2*B:ℤ):ℚ)*t^2) (norm_nonnegative B hs ht)=
      (residuePow 2 k s hs)^2-((2*B:ℤ):ZMod (2^k))*(residuePow 2 k t ht)^2 := by
  have hp : integralRat 2 (s^2-((2*B:ℤ):ℚ)*t^2) (norm_nonnegative B hs ht)=
      (integralRat 2 s hs)^2-((2*B:ℤ):ℤ_[2])*(integralRat 2 t ht)^2 := by
    apply Subtype.coe_injective
    simp only [integralRat_coe,PadicInt.coe_sub,PadicInt.coe_pow,PadicInt.coe_mul,
      PadicInt.coe_intCast,Rat.cast_sub,Rat.cast_pow,Rat.cast_mul,Rat.cast_intCast]
  have hm := congrArg (PadicInt.toZModPow k) hp
  simpa only [residuePow,map_sub,map_pow,map_mul,map_intCast] using hm

theorem half_norm_nonnegative (B : ℤ) {s t : ℚ}
    (hs : 0 ≤ padicValRat 2 (s/2)) (ht : 0 ≤ padicValRat 2 t) :
    0 ≤ padicValRat 2 ((s^2-((2*B:ℤ):ℚ)*t^2)/2) := by
  rw [show (s^2-((2*B:ℤ):ℚ)*t^2)/2=2*(s/2)^2+((-B:ℤ):ℚ)*t^2 by push_cast; ring]
  apply LocalSeven.valuation_nonnegative_add 2
  · apply LocalSeven.valuation_nonnegative_mul 2
    · have htwo : padicValRat 2 (2:ℚ)=1 := padicValRat.self (by norm_num)
      omega
    · rw [padicValRat.pow]; positivity
  · apply LocalSeven.valuation_nonnegative_mul 2
    · rw [padicValRat.of_int]; positivity
    · rw [padicValRat.pow]; positivity

/-- Direct residue after the unique odd valuation of the integral norm
is removed. Both rational halves have already been proved integral. -/
theorem half_norm_residue (k : ℕ) (B : ℤ) {s t : ℚ}
    (hs : 0 ≤ padicValRat 2 (s/2)) (ht : 0 ≤ padicValRat 2 t) :
    residuePow 2 k ((s^2-((2*B:ℤ):ℚ)*t^2)/2) (half_norm_nonnegative B hs ht)=
      2*(residuePow 2 k (s/2) hs)^2-(B:ZMod (2^k))*(residuePow 2 k t ht)^2 := by
  have hp : integralRat 2 ((s^2-((2*B:ℤ):ℚ)*t^2)/2) (half_norm_nonnegative B hs ht)=
      (2:ℤ_[2])*(integralRat 2 (s/2) hs)^2-(B:ℤ_[2])*(integralRat 2 t ht)^2 := by
    apply Subtype.coe_injective
    simp only [integralRat_coe,PadicInt.coe_sub,PadicInt.coe_pow,PadicInt.coe_mul,
      PadicInt.coe_intCast,show ((2:ℤ_[2]):ℚ_[2])=2 by rfl]
    have hr : (s^2-((2*B:ℤ):ℚ)*t^2)/2=2*(s/2)^2-(B:ℚ)*t^2 := by push_cast; ring
    simpa only [Rat.cast_div,Rat.cast_sub,Rat.cast_pow,Rat.cast_mul,Rat.cast_intCast,
      Rat.cast_ofNat] using congrArg (fun z : ℚ => (z:ℚ_[2])) hr
  have hm := congrArg (PadicInt.toZModPow k) hp
  simpa only [residuePow,map_sub,map_pow,map_mul,map_intCast,map_ofNat] using hm

end RankCertificates.DyadicNormResidues
