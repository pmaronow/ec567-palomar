module

public import RankCertificates.PrimePowerResidues
public import RankCertificates.LocalSeven

/-! Reduction of genuine integral-model rational points modulo prime powers. -/

@[expose] public section

namespace RankCertificates.PrimePowerPoints

open LocalValuations PrimePowerResidues

theorem residuePow_pow_integral (p : ℕ) [Fact p.Prime] (k : ℕ) {x : ℚ}
    (hx : 0 ≤ padicValRat p x) (n : ℕ) :
    residuePow p k (x ^ n) (by rw [padicValRat.pow]; positivity) = (residuePow p k x hx) ^ n := by
  have he : integralRat p (x ^ n) (by rw [padicValRat.pow]; positivity) =
      (integralRat p x hx) ^ n := by
    apply PadicInt.coe_inj.mp
    simp only [integralRat_coe, PadicInt.coe_pow, Rat.cast_pow]
  simp only [residuePow, he, map_pow]

theorem onCurve_residuePow (p : ℕ) [Fact p.Prime] (k : ℕ) (a b : ℤ) {x y : ℚ}
    (hx : 0 ≤ padicValRat p x) (h : OnCurve (a : ℚ) (b : ℚ) x y) :
    ∃ hy : 0 ≤ padicValRat p y,
      (residuePow p k y hy) ^ 2 = (residuePow p k x hx) ^ 3 +
        (a : ZMod (p ^ k)) * (residuePow p k x hx) ^ 2 +
          (b : ZMod (p ^ k)) * residuePow p k x hx := by
  have hyden := onCurve_residue_denominator_unit p a b h
    (denominator_unit_of_nonnegative_valuation p x hx)
  have hy : 0 ≤ padicValRat p y := by
    have hyvd := padicValNat.eq_zero_of_not_dvd
      (fun hd => hyden ((ZMod.natCast_eq_zero_iff _ _).mpr hd))
    rw [padicValRat_def, hyvd]
    simp only [Nat.cast_zero, sub_zero]
    exact Int.natCast_nonneg _
  have ha : 0 ≤ padicValRat p (a : ℚ) := by rw [padicValRat.of_int]; positivity
  have hb : 0 ≤ padicValRat p (b : ℚ) := by rw [padicValRat.of_int]; positivity
  have hx2 : 0 ≤ padicValRat p (x ^ 2) := by rw [padicValRat.pow]; positivity
  have hx3 : 0 ≤ padicValRat p (x ^ 3) := by rw [padicValRat.pow]; positivity
  have hax := LocalSeven.valuation_nonnegative_mul p ha hx2
  have hbx := LocalSeven.valuation_nonnegative_mul p hb hx
  have hsum := LocalSeven.valuation_nonnegative_add p hx3 hax
  have hall := LocalSeven.valuation_nonnegative_add p hsum hbx
  refine ⟨hy, ?_⟩
  have heq : residuePow p k (y ^ 2) (by rw [padicValRat.pow]; positivity) =
      residuePow p k (x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x) hall := by
    congr 1
  rw [residuePow_pow_integral p k hy 2,
    residuePow_add p k hsum hbx hall, residuePow_add p k hx3 hax hsum,
    residuePow_mul p k ha hx2 hax, residuePow_mul p k hb hx hbx,
    residuePow_pow_integral p k hx 3, residuePow_pow_integral p k hx 2,
    residuePow_int p k a ha, residuePow_int p k b hb] at heq
  exact heq

end RankCertificates.PrimePowerPoints
