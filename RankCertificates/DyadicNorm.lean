module

public import RankCertificates.Rank6TwoDescent
public import RankCertificates.DyadicNormResidues

@[expose] public section

namespace RankCertificates.DyadicNorm

set_option maxHeartbeats 400000

open LocalValuations PrimePowerResidues PrimePowerPoints

theorem binomial_nonnegative (p : ℕ) [Fact p.Prime] (c d : ℤ) {s t : ℚ}
    (hs : 0 ≤ padicValRat p s) (ht : 0 ≤ padicValRat p t) :
    0 ≤ padicValRat p ((c : ℚ) * s ^ 2 + (d : ℚ) * t ^ 2) := by
  have hc : 0 ≤ padicValRat p (c : ℚ) := by rw [padicValRat.of_int]; positivity
  have hd : 0 ≤ padicValRat p (d : ℚ) := by rw [padicValRat.of_int]; positivity
  have hs2 : 0 ≤ padicValRat p (s ^ 2) := by rw [padicValRat.pow]; positivity
  have ht2 : 0 ≤ padicValRat p (t ^ 2) := by rw [padicValRat.pow]; positivity
  exact LocalSeven.valuation_nonnegative_add p
    (LocalSeven.valuation_nonnegative_mul p hc hs2)
    (LocalSeven.valuation_nonnegative_mul p hd ht2)

theorem binomial_residue (p : ℕ) [Fact p.Prime] (k : ℕ) (c d : ℤ) {s t : ℚ}
    (hs : 0 ≤ padicValRat p s) (ht : 0 ≤ padicValRat p t) :
    residuePow p k ((c : ℚ) * s ^ 2 + (d : ℚ) * t ^ 2) (binomial_nonnegative p c d hs ht) =
      (c : ZMod (p ^ k)) * (residuePow p k s hs) ^ 2 +
        (d : ZMod (p ^ k)) * (residuePow p k t ht) ^ 2 := by
  have hc : 0 ≤ padicValRat p (c : ℚ) := by rw [padicValRat.of_int]; positivity
  have hd : 0 ≤ padicValRat p (d : ℚ) := by rw [padicValRat.of_int]; positivity
  have hs2 : 0 ≤ padicValRat p (s ^ 2) := by rw [padicValRat.pow]; positivity
  have ht2 : 0 ≤ padicValRat p (t ^ 2) := by rw [padicValRat.pow]; positivity
  have hcs := LocalSeven.valuation_nonnegative_mul p hc hs2
  have hdt := LocalSeven.valuation_nonnegative_mul p hd ht2
  rw [residuePow_add p k hcs hdt, residuePow_mul p k hc hs2 hcs,
    residuePow_mul p k hd ht2 hdt, residuePow_int p k c hc, residuePow_int p k d hd,
    residuePow_pow_integral p k hs 2, residuePow_pow_integral p k ht 2]

theorem first_norm_residue (s : (ZMod 8)ˣ) (t : ZMod 8) :
    (s : ZMod 8) ^ 2 - 6 * t ^ 2 = 1 ∨ (s : ZMod 8) ^ 2 - 6 * t ^ 2 = 3 := by
  revert s t
  decide +kernel

theorem second_norm_residue (s : ZMod 8) (t : (ZMod 8)ˣ) :
    2 * s ^ 2 - 7 * (t : ZMod 8) ^ 2 = 1 ∨ 2 * s ^ 2 - 7 * (t : ZMod 8) ^ 2 = 3 := by
  revert s t
  decide +kernel

theorem norm_unit_one_or_three (B : ℤ)
    (hB : (B : ZMod 8) = 7) (hvB : padicValRat 2 (B : ℚ) = 0)
    {s t : ℚ} (hn : s ^ 2 - ((2 * B : ℤ) : ℚ) * t ^ 2 ≠ 0) :
    unitResiduePow 2 3 (s ^ 2 - ((2 * B : ℤ) : ℚ) * t ^ 2) = 1 ∨
      unitResiduePow 2 3 (s ^ 2 - ((2 * B : ℤ) : ℚ) * t ^ 2) = 3 := by
  have hB0 : (B : ℚ) ≠ 0 := by
    exact_mod_cast (show B ≠ 0 from fun hz => (by decide : (0 : ZMod 8) ≠ 7) (by simpa [hz] using hB))
  have hbeta0 : ((2 * B : ℤ) : ℚ) ≠ 0 := by exact_mod_cast mul_ne_zero (by norm_num : (2 : ℤ) ≠ 0) (Int.cast_ne_zero.mp hB0)
  have htwo : padicValRat 2 (2 : ℚ) = 1 := by
    simpa only [Nat.cast_ofNat] using padicValRat.self (p := 2) (by decide : 1 < 2)
  have hbeta : padicValRat 2 ((2 * B : ℤ) : ℚ) = 1 := by
    simp only [Int.cast_mul, Int.cast_ofNat]
    rw [padicValRat.mul (by norm_num) hB0, htwo, hvB]
    omega
  have hbetau : unitResiduePow 2 3 ((2 * B : ℤ) : ℚ) = 7 := by
    simp only [unitResiduePow, normalizedUnit, hbeta, zpow_one, Nat.cast_ofNat]
    have heq : ((2 * B : ℤ) : ℚ) / 2 = (B : ℚ) := by push_cast; ring
    simp only [heq, residuePow_int]
    exact hB
  have hnegative : unitResiduePow 2 3 (-((2 * B : ℤ) : ℚ)) = 1 := by
    have hminus : unitResiduePow 2 3 (-1 : ℚ) = 7 := by
      rw [Rank6TwoDescent.unitResiduePow_of_valuation_zero 3 (by simp)]
      have hr := residuePow_int 2 3 (-1) (by simp)
      norm_num only [Int.cast_neg, Int.cast_one] at hr
      rw [hr]
      decide
    rw [show -((2 * B : ℤ) : ℚ) = (-1 : ℚ) * ((2 * B : ℤ) : ℚ) by ring,
      unitResiduePow_mul 2 3 (by norm_num) hbeta0, hminus, hbetau]
    decide
  by_cases hs : s = 0
  · have ht : t ≠ 0 := by intro ht; simp [hs, ht] at hn
    left
    rw [show s ^ 2 - ((2 * B : ℤ) : ℚ) * t ^ 2 = -((2 * B : ℤ) : ℚ) * t ^ 2 by rw [hs]; ring,
      unitResiduePow_mul 2 3 (neg_ne_zero.mpr hbeta0) (pow_ne_zero 2 ht), hnegative,
      unitResiduePow_two_square ht, one_mul]
  by_cases ht : t = 0
  · left
    simpa only [ht, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, sub_zero] using unitResiduePow_two_square hs
  let m : ℤ := min (padicValRat 2 s) (padicValRat 2 t)
  let c : ℚ := (2 : ℚ) ^ m
  let S : ℚ := s / c
  let T : ℚ := t / c
  let g : ℚ := S ^ 2 - ((2 * B : ℤ) : ℚ) * T ^ 2
  have hc0 : c ≠ 0 := zpow_ne_zero _ (by norm_num)
  have hcv : padicValRat 2 c = m := by dsimp [c]; rw [padicValRat.zpow, htwo, mul_one]
  have hS0 : S ≠ 0 := div_ne_zero hs hc0
  have hT0 : T ≠ 0 := div_ne_zero ht hc0
  have hSv : padicValRat 2 S = padicValRat 2 s - m := by dsimp [S]; rw [padicValRat.div hs hc0, hcv]
  have hTv : padicValRat 2 T = padicValRat 2 t - m := by dsimp [T]; rw [padicValRat.div ht hc0, hcv]
  have hSnonneg : 0 ≤ padicValRat 2 S := by have hm := min_le_left (padicValRat 2 s) (padicValRat 2 t); omega
  have hTnonneg : 0 ≤ padicValRat 2 T := by have hm := min_le_right (padicValRat 2 s) (padicValRat 2 t); omega
  have hshape : s ^ 2 - ((2 * B : ℤ) : ℚ) * t ^ 2 = c ^ 2 * g := by
    dsimp [g, S, T]
    field_simp
  have hg0 : g ≠ 0 := by intro hz; rw [hshape, hz, mul_zero] at hn; exact hn rfl
  have hunit : unitResiduePow 2 3 (s ^ 2 - ((2 * B : ℤ) : ℚ) * t ^ 2) = unitResiduePow 2 3 g := by
    rw [hshape, unitResiduePow_mul 2 3 (pow_ne_zero 2 hc0) hg0, unitResiduePow_two_square hc0, one_mul]
  rw [hunit]
  by_cases hst : padicValRat 2 s ≤ padicValRat 2 t
  · have hSzero : padicValRat 2 S = 0 := by dsimp [m] at hSv; rw [min_eq_left hst] at hSv; omega
    have hnegv : padicValRat 2 (-((2 * B : ℤ) : ℚ) * T ^ 2) = 1 + 2 * padicValRat 2 T := by
      rw [padicValRat.mul (neg_ne_zero.mpr hbeta0) (pow_ne_zero 2 hT0), padicValRat.neg, hbeta, padicValRat.pow]
      norm_num
    have hgval := (LocalDescent.add_dominant (p := 2) (pow_ne_zero 2 hS0)
      (Or.inr (show padicValRat 2 (S ^ 2) < padicValRat 2 (-((2 * B : ℤ) : ℚ) * T ^ 2) by
        rw [padicValRat.pow, hSzero, hnegv]; omega))).2
    have hgeq : S ^ 2 + -((2 * B : ℤ) : ℚ) * T ^ 2 = g := by dsimp [g]; ring
    rw [hgeq, padicValRat.pow, hSzero] at hgval
    have hgv : padicValRat 2 g = 0 := by omega
    rw [Rank6TwoDescent.unitResiduePow_of_valuation_zero 3 hgv]
    have hr := DyadicNormResidues.norm_residue 3 B hSnonneg hTnonneg
    have hcoef : ((2 * B : ℤ) : ZMod 8) = 6 := by
      simp only [Int.cast_mul, Int.cast_ofNat, hB]
      decide
    have hrr : residuePow 2 3 g hgv.symm.le =
        (residuePow 2 3 S hSnonneg) ^ 2 - 6 * (residuePow 2 3 T hTnonneg) ^ 2 := by
      simpa only [g, hcoef] using hr
    rw [hrr]
    obtain ⟨u, hu⟩ := residuePow_isUnit 2 3 hS0 hSzero
    rw [← hu]
    exact first_norm_residue u _
  · have hts : padicValRat 2 t < padicValRat 2 s := lt_of_not_ge hst
    have hTzero : padicValRat 2 T = 0 := by dsimp [m] at hTv; rw [min_eq_right (le_of_lt hts)] at hTv; omega
    have hSpos : 1 ≤ padicValRat 2 S := by dsimp [m] at hSv; rw [min_eq_right (le_of_lt hts)] at hSv; omega
    have hnegv : padicValRat 2 (-((2 * B : ℤ) : ℚ) * T ^ 2) = 1 := by
      rw [padicValRat.mul (neg_ne_zero.mpr hbeta0) (pow_ne_zero 2 hT0), padicValRat.neg, hbeta, padicValRat.pow, hTzero]
      omega
    have hgval := (LocalDescent.add_dominant (p := 2) (mul_ne_zero (neg_ne_zero.mpr hbeta0) (pow_ne_zero 2 hT0))
      (Or.inr (show padicValRat 2 (-((2 * B : ℤ) : ℚ) * T ^ 2) < padicValRat 2 (S ^ 2) by
        rw [hnegv, padicValRat.pow]; omega))).2
    have hgeq : -((2 * B : ℤ) : ℚ) * T ^ 2 + S ^ 2 = g := by dsimp [g]; ring
    rw [hgeq, hnegv] at hgval
    let R : ℚ := S / 2
    have hRnonneg : 0 ≤ padicValRat 2 R := by dsimp [R]; rw [padicValRat.div hS0 (by norm_num), htwo]; omega
    have hgdiv : padicValRat 2 (g / 2) = 0 := by rw [padicValRat.div hg0 (by norm_num), hgval, htwo]; omega
    have hun : unitResiduePow 2 3 g = residuePow 2 3 (g / 2) (by omega) := by
      simp only [unitResiduePow, normalizedUnit, hgval, zpow_one, Nat.cast_ofNat]
    rw [hun]
    have hr := DyadicNormResidues.half_norm_residue 3 B hRnonneg hTnonneg
    have hrr : residuePow 2 3 (g / 2) hgdiv.symm.le =
        2 * (residuePow 2 3 R hRnonneg) ^ 2 - 7 * (residuePow 2 3 T hTnonneg) ^ 2 := by
      simpa only [g, R, hB] using hr
    rw [hrr]
    obtain ⟨u, hu⟩ := residuePow_isUnit 2 3 hT0 hTzero
    rw [← hu]
    exact second_norm_residue _ u

end RankCertificates.DyadicNorm
