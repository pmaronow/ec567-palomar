module

public import RankCertificates.LocalValuations

/-!
# Necessary fixed-prime restrictions at 7

These statements concern actual rational points and actual two-isogeny
images. At valuation one, the rational equation forces a root of the
normalized quadratic modulo 7. Away from valuation one, strict valuation
dominance supplies the necessary square character.
-/

@[expose] public section

namespace RankCertificates.LocalSeven

open LocalValuations

instance primeSeven : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem valuation_nonnegative_mul (p : ℕ) [Fact p.Prime] {x z : ℚ}
    (hx : 0 ≤ padicValRat p x) (hz : 0 ≤ padicValRat p z) :
    0 ≤ padicValRat p (x * z) := by
  by_cases hx0 : x = 0
  · simp [hx0]
  by_cases hz0 : z = 0
  · simp [hz0]
  rw [padicValRat.mul hx0 hz0]
  omega

theorem valuation_nonnegative_add (p : ℕ) [Fact p.Prime] {x z : ℚ}
    (hx : 0 ≤ padicValRat p x) (hz : 0 ≤ padicValRat p z) :
    0 ≤ padicValRat p (x + z) := by
  by_cases hsum : x + z = 0
  · simp [hsum]
  exact le_trans (le_min hx hz) (padicValRat.min_le_padicValRat_add hsum)

theorem residue_add_integral (p : ℕ) [Fact p.Prime] {x z : ℚ}
    (hx : 0 ≤ padicValRat p x) (hz : 0 ≤ padicValRat p z) :
    rationalResidue p (x + z) = rationalResidue p x + rationalResidue p z := by
  change ((x + z : ℚ) : ZMod p) = (x : ZMod p) + (z : ZMod p)
  exact Rat.cast_add_of_ne_zero
    (denominator_unit_of_nonnegative_valuation p x hx)
    (denominator_unit_of_nonnegative_valuation p z hz)

theorem residue_mul_integral (p : ℕ) [Fact p.Prime] {x z : ℚ}
    (hx : 0 ≤ padicValRat p x) (hz : 0 ≤ padicValRat p z) :
    rationalResidue p (x * z) = rationalResidue p x * rationalResidue p z :=
  rationalResidue_mul p
    (denominator_unit_of_nonnegative_valuation p x hx)
    (denominator_unit_of_nonnegative_valuation p z hz)

theorem residue_pow_integral (p : ℕ) [Fact p.Prime] {x : ℚ}
    (hx : 0 ≤ padicValRat p x) (n : ℕ) :
    rationalResidue p (x ^ n) = rationalResidue p x ^ n := by
  induction n with
  | zero => simp [rationalResidue]
  | succ n ih =>
    rw [pow_succ, residue_mul_integral p (by rw [padicValRat.pow]; positivity) hx, ih, pow_succ]

theorem valuation_zero_of_residue_ne_zero (p : ℕ) [Fact p.Prime] {x : ℚ}
    (hx : rationalResidue p x ≠ 0) : padicValRat p x = 0 := by
  have hn : (x.num : ZMod p) ≠ 0 := by
    intro hz
    apply hx
    simp [rationalResidue, hz]
  have hd : (x.den : ZMod p) ≠ 0 := by
    intro hz
    apply hx
    simp [rationalResidue, hz]
  have hvn := padicValInt.eq_zero_of_not_dvd (p := p) (z := x.num)
    (fun h => hn ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h))
  have hvd := padicValNat.eq_zero_of_not_dvd (p := p) (n := x.den)
    (fun h => hd ((ZMod.natCast_eq_zero_iff _ _).mpr h))
  simp only [padicValRat_def, hvn, hvd, Nat.cast_zero, sub_self]

theorem residue_cubic_integral (p : ℕ) [Fact p.Prime] (A B : ℤ) {u : ℚ}
    (hu : 0 ≤ padicValRat p u) :
    rationalResidue p (u ^ 3 + (A : ℚ) * u ^ 2 + (B : ℚ) * u) =
      rationalResidue p u ^ 3 + (A : ZMod p) * rationalResidue p u ^ 2 +
        (B : ZMod p) * rationalResidue p u := by
  have hA : 0 ≤ padicValRat p (A : ℚ) := by rw [padicValRat.of_int]; positivity
  have hB : 0 ≤ padicValRat p (B : ℚ) := by rw [padicValRat.of_int]; positivity
  have hu2 : 0 ≤ padicValRat p (u ^ 2) := by rw [padicValRat.pow]; positivity
  have hu3 : 0 ≤ padicValRat p (u ^ 3) := by rw [padicValRat.pow]; positivity
  have hAu := valuation_nonnegative_mul p hA hu2
  have hBu := valuation_nonnegative_mul p hB hu
  rw [residue_add_integral p (valuation_nonnegative_add p hu3 hAu) hBu,
    residue_add_integral p hu3 hAu, residue_mul_integral p hA hu2,
    residue_mul_integral p hB hu, residue_pow_integral p hu 3,
    residue_pow_integral p hu 2, rationalResidue_int, rationalResidue_int]

/-- At valuation one, the reduced normalized quadratic must vanish. -/
theorem valuation_one_quadratic_root (A B : ℤ) {x y : ℚ}
    (hx : x ≠ 0) (hv : padicValRat 7 x = 1)
    (h : OnCurve ((7 * A : ℤ) : ℚ) ((49 * B : ℤ) : ℚ) x y) :
    (unitResidue 7 x) ^ 2 + (A : ZMod 7) * unitResidue 7 x + (B : ZMod 7) = 0 := by
  let u : ℚ := x / 7
  let g : ℚ := u ^ 3 + (A : ℚ) * u ^ 2 + (B : ℚ) * u
  have hu0 : u ≠ 0 := div_ne_zero hx (by norm_num)
  have hseven : padicValRat 7 (7 : ℚ) = 1 := by
    simpa only [Nat.cast_ofNat] using padicValRat.self (p := 7) (by decide : 1 < 7)
  have huv : padicValRat 7 u = 0 := by
    dsimp [u]
    rw [padicValRat.div hx (by norm_num), hv, hseven]
    omega
  have hu_res : rationalResidue 7 u ≠ 0 := residue_ne_zero_of_valuation_zero 7 hu0 huv
  have hg_res : rationalResidue 7 g = 0 := by
    by_contra hgr
    have hgv := valuation_zero_of_residue_ne_zero 7 hgr
    have hg0 : g ≠ 0 := by intro hz; simp [hz, rationalResidue] at hgr
    have hy_eq : y ^ 2 = (7 : ℚ) ^ 3 * g := by
      dsimp [g, u]
      simp only [OnCurve, Int.cast_mul, Int.cast_ofNat] at h
      linear_combination h
    have hy0 : y ≠ 0 := by
      intro hz
      rw [hz, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hy_eq
      exact (mul_ne_zero (pow_ne_zero 3 (by norm_num : (7 : ℚ) ≠ 0)) hg0) hy_eq.symm
    have hvals := congrArg (padicValRat 7) hy_eq
    rw [padicValRat.pow, padicValRat.mul (pow_ne_zero 3 (by norm_num)) hg0,
      padicValRat.pow, hseven, hgv] at hvals
    omega
  have hpoly := residue_cubic_integral 7 A B (u := u) (by omega)
  change rationalResidue 7 g = _ at hpoly
  rw [hg_res] at hpoly
  have hf : rationalResidue 7 u *
      ((rationalResidue 7 u) ^ 2 + (A : ZMod 7) * rationalResidue 7 u + (B : ZMod 7)) = 0 := by
    linear_combination -hpoly
  have hquad := (mul_eq_zero.mp hf).resolve_left hu_res
  have heq : unitResidue 7 x = rationalResidue 7 u := by
    simp only [unitResidue, normalizedUnit, hv, zpow_one, Nat.cast_ofNat]
    rfl
  rwa [← heq] at hquad

theorem original_root_character {u : ZMod 7} (h : u ^ 2 + 2 * u + 4 = 0) :
    quadraticChar (ZMod 7) u = 1 := by
  revert u
  decide

theorem dual_root_character {u : ZMod 7} (h : u ^ 2 + 3 * u + 2 = 0) :
    quadraticChar (ZMod 7) u = -1 := by
  revert u
  decide

theorem seven_unit_square_character : quadraticChar (ZMod 7) (4 : ZMod 7) = 1 ∧
    quadraticChar (ZMod 7) (2 : ZMod 7) = 1 := by decide

theorem unitCharacter_square (p : ℕ) [Fact p.Prime] {x : ℚ} (hx : x ≠ 0) :
    unitCharacter p (x ^ 2) = 1 :=
  (unitCharacter_eq_one_iff p (pow_ne_zero 2 hx)).mpr (unitResidue_square p hx)

theorem same_squareclass_unitCharacter (p : ℕ) [Fact p.Prime] {x z : ℚ}
    (hx : x ≠ 0) (hz : z ≠ 0) (hc : rationalSquareClass x = rationalSquareClass z) :
    unitCharacter p x = unitCharacter p z := by
  have hprod : rationalSquareClass (x * z) = 1 := by
    rw [rationalSquareClass_mul hx hz, hc, rationalSquareClass_mul_self]
  obtain ⟨r, hr, hxr⟩ := (rationalSquareClass_eq_one_iff (mul_ne_zero hx hz)).mp hprod
  have hres : unitCharacter p x * unitCharacter p z = 1 := by
    rw [← unitCharacter_mul p hx hz, hxr, unitCharacter_square p hr]
  have hsq : unitCharacter p z * unitCharacter p z = 1 := by
    simpa only [unitCharacter, pow_two] using quadraticChar_sq_one (unitResidue_ne_zero p hz)
  have hnonzero : unitCharacter p z ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hsq
    omega
  exact mul_right_cancel₀ hnonzero (hres.trans hsq.symm)

theorem same_squareclass_valuation_mod_two (p : ℕ) [Fact p.Prime] {x z : ℚ}
    (hx : x ≠ 0) (hz : z ≠ 0) (hc : rationalSquareClass x = rationalSquareClass z) :
    padicValRat p x % 2 = padicValRat p z % 2 := by
  have hprod : rationalSquareClass (x * z) = 1 := by
    rw [rationalSquareClass_mul hx hz, hc, rationalSquareClass_mul_self]
  obtain ⟨r, _, hxr⟩ := (rationalSquareClass_eq_one_iff (mul_ne_zero hx hz)).mp hprod
  have hval := congrArg (padicValRat p) hxr
  rw [padicValRat.mul hx hz, padicValRat.pow] at hval
  omega

theorem coefficients_valuations (A B : ℤ)
    (hA : (A : ZMod 7) ≠ 0) (hB : (B : ZMod 7) ≠ 0) :
    padicValRat 7 ((7 * A : ℤ) : ℚ) = 1 ∧
      padicValRat 7 ((49 * B : ℤ) : ℚ) = 2 := by
  have hA0 : (A : ℚ) ≠ 0 := by
    exact_mod_cast (show A ≠ 0 from fun hz => hA (by simp [hz]))
  have hB0 : (B : ℚ) ≠ 0 := by
    exact_mod_cast (show B ≠ 0 from fun hz => hB (by simp [hz]))
  have hAv : padicValRat 7 (A : ℚ) = 0 :=
    valuation_zero_of_residue_ne_zero 7 (by rwa [rationalResidue_int])
  have hBv : padicValRat 7 (B : ℚ) = 0 :=
    valuation_zero_of_residue_ne_zero 7 (by rwa [rationalResidue_int])
  have h7 : padicValRat 7 (7 : ℚ) = 1 := by
    simpa only [Nat.cast_ofNat] using padicValRat.self (p := 7) (by decide : 1 < 7)
  have h49 : padicValRat 7 (49 : ℚ) = 2 := by
    rw [show (49 : ℚ) = 7 ^ 2 by norm_num, padicValRat.pow, h7]
    norm_num
  simp only [Int.cast_mul, Int.cast_ofNat]
  rw [padicValRat.mul (by norm_num) hA0, padicValRat.mul (by norm_num) hB0,
    hAv, hBv, h7, h49]
  norm_num

theorem linear_coefficient_character (B : ℤ) (hB : (B : ZMod 7) ≠ 0) :
    unitCharacter 7 ((49 * B : ℤ) : ℚ) = quadraticChar (ZMod 7) (B : ZMod 7) := by
  have hB0 : (B : ℚ) ≠ 0 := by
    exact_mod_cast (show B ≠ 0 from fun hz => hB (by simp [hz]))
  have hnot : ¬ (7 : ℤ) ∣ B :=
    fun hz => hB ((ZMod.intCast_zmod_eq_zero_iff_dvd B 7).mpr hz)
  simp only [Int.cast_mul, Int.cast_ofNat]
  rw [show (49 : ℚ) = 7 ^ 2 by norm_num,
    unitCharacter_mul 7 (pow_ne_zero 2 (by norm_num)) hB0,
    unitCharacter_square 7 (by norm_num), one_mul, unitCharacter, unitResidue_int_of_not_dvd 7 hnot]

/-- Off valuation one, strict dominance forces both even valuation and
square normalized character. -/
theorem coordinate_away_one (A B : ℤ) {x y : ℚ}
    (hA : (A : ZMod 7) ≠ 0) (hB : (B : ZMod 7) ≠ 0)
    (hBchar : quadraticChar (ZMod 7) (B : ZMod 7) = 1)
    (hx : x ≠ 0) (hv : padicValRat 7 x ≠ 1)
    (h : OnCurve ((7 * A : ℤ) : ℚ) ((49 * B : ℤ) : ℚ) x y) :
    Even (padicValRat 7 x) ∧ unitCharacter 7 x = 1 := by
  obtain ⟨ha, hb⟩ := coefficients_valuations A B hA hB
  have hb0 : ((49 * B : ℤ) : ℚ) ≠ 0 := by
    intro hz; rw [hz, padicValRat.zero] at hb; omega
  rcases lt_or_gt_of_ne hv with hlow | hhigh
  · have hs := LocalDescent.cubic_term_square_approximation (p := 7) hx
      (Or.inr (by omega)) (Or.inr (by omega)) h
    exact ⟨LocalDescent.square_approximation_even_valuation hx hs,
      squareApproximation_unitCharacter_eq_one 7 hx hs⟩
  · have hs := LocalDescent.linear_term_square_approximation (p := 7) hb0 hx
      (by omega) (Or.inr (by omega)) h
    have he := LocalDescent.square_approximation_even_valuation (mul_ne_zero hb0 hx) hs
    have hc := squareApproximation_unitCharacter_eq_one 7 (mul_ne_zero hb0 hx) hs
    have hbchar : unitCharacter 7 ((49 * B : ℤ) : ℚ) = 1 :=
      (linear_coefficient_character B hB).trans hBchar
    rw [unitCharacter_mul 7 hb0 hx, hbchar, one_mul] at hc
    refine ⟨?_, hc⟩
    obtain ⟨k, hk⟩ := he
    rw [padicValRat.mul hb0 hx, hb] at hk
    exact ⟨k - 1, by omega⟩

theorem original_coordinate_character (A B : ℤ) {x y : ℚ}
    (hA : (A : ZMod 7) = 2) (hB : (B : ZMod 7) = 4)
    (hx : x ≠ 0) (h : OnCurve ((7 * A : ℤ) : ℚ) ((49 * B : ℤ) : ℚ) x y) :
    unitCharacter 7 x = 1 := by
  by_cases hv : padicValRat 7 x = 1
  · have hroot := valuation_one_quadratic_root A B hx hv h
    rw [hA, hB] at hroot
    exact original_root_character hroot
  · exact (coordinate_away_one A B (by rw [hA]; decide) (by rw [hB]; decide)
      (by rw [hB]; exact seven_unit_square_character.1) hx hv h).2

theorem dual_coordinate_character (A B : ℤ) {x y : ℚ}
    (hA : (A : ZMod 7) = 3) (hB : (B : ZMod 7) = 2)
    (hx : x ≠ 0) (h : OnCurve ((7 * A : ℤ) : ℚ) ((49 * B : ℤ) : ℚ) x y) :
    unitCharacter 7 x = (-1 : ℤ) ^ (padicValRat 7 x % 2).toNat := by
  by_cases hv : padicValRat 7 x = 1
  · have hroot := valuation_one_quadratic_root A B hx hv h
    rw [hA, hB] at hroot
    have hc : unitCharacter 7 x = -1 := dual_root_character hroot
    simpa only [hv, Int.one_emod_two, Int.toNat_one, pow_one] using hc
  · obtain ⟨he, hc⟩ := coordinate_away_one A B (by rw [hA]; decide) (by rw [hB]; decide)
      (by rw [hB]; exact seven_unit_square_character.2) hx hv h
    have hmod : padicValRat 7 x % 2 = 0 := by obtain ⟨k, hk⟩ := he; omega
    simpa only [hmod, Int.toNat_zero, pow_zero] using hc

theorem unitCharacter_one : unitCharacter 7 (1 : ℚ) = 1 := by
  simp [unitCharacter, unitResidue, normalizedUnit, rationalResidue]

/-- The fixed-7 original row holds for every representative of every
actual two-isogeny image. -/
theorem original_image_character (A B : ℤ)
    (hA : (A : ZMod 7) = 2) (hB : (B : ZMod 7) = 4)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage ((7 * A : ℤ) : ℚ) ((49 * B : ℤ) : ℚ))
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) :
    unitCharacter 7 z = 1 := by
  have hb0 : ((49 * B : ℤ) : ℚ) ≠ 0 := by
    have hb := (coefficients_valuations A B (by rw [hA]; decide) (by rw [hB]; decide)).2
    intro hz; rw [hz, padicValRat.zero] at hb; omega
  obtain ⟨P, rfl⟩ := hq
  cases P with
  | zero =>
    rw [same_squareclass_unitCharacter 7 hz one_ne_zero (hc.trans rationalSquareClass_one.symm)]
    exact unitCharacter_one
  | some x y hP =>
    by_cases hx : x = 0
    · simp only [twoIsogenyClass, hx, ite_true] at hc
      rw [same_squareclass_unitCharacter 7 hz hb0 hc,
        linear_coefficient_character B (by rw [hB]; decide), hB]
      exact seven_unit_square_character.1
    · simp only [twoIsogenyClass, hx, ite_false] at hc
      rw [same_squareclass_unitCharacter 7 hz hx hc]
      exact original_coordinate_character A B hA hB hx ((onCurve_iff_equation _ _ _ _).mpr hP.1)

/-- The fixed-7 dual row is the character-parity equality on every
representative of every actual two-isogeny image. -/
theorem dual_image_character (A B : ℤ)
    (hA : (A : ZMod 7) = 3) (hB : (B : ZMod 7) = 2)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage ((7 * A : ℤ) : ℚ) ((49 * B : ℤ) : ℚ))
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) :
    unitCharacter 7 z = (-1 : ℤ) ^ (padicValRat 7 z % 2).toNat := by
  have hbval := (coefficients_valuations A B (by rw [hA]; decide) (by rw [hB]; decide)).2
  have hb0 : ((49 * B : ℤ) : ℚ) ≠ 0 := by
    intro hz; rw [hz, padicValRat.zero] at hbval; omega
  obtain ⟨P, rfl⟩ := hq
  cases P with
  | zero =>
    have hc1 := hc.trans rationalSquareClass_one.symm
    rw [same_squareclass_unitCharacter 7 hz one_ne_zero hc1,
      same_squareclass_valuation_mod_two 7 hz one_ne_zero hc1, padicValRat.one,
      Int.zero_emod, Int.toNat_zero, pow_zero]
    exact unitCharacter_one
  | some x y hP =>
    by_cases hx : x = 0
    · simp only [twoIsogenyClass, hx, ite_true] at hc
      rw [same_squareclass_unitCharacter 7 hz hb0 hc,
        same_squareclass_valuation_mod_two 7 hz hb0 hc, hbval]
      rw [show (2 : ℤ) % 2 = 0 by norm_num, Int.toNat_zero, pow_zero]
      rw [linear_coefficient_character B (by rw [hB]; decide), hB]
      exact seven_unit_square_character.2
    · simp only [twoIsogenyClass, hx, ite_false] at hc
      rw [same_squareclass_unitCharacter 7 hz hx hc,
        same_squareclass_valuation_mod_two 7 hz hx hc]
      exact dual_coordinate_character A B hA hB hx ((onCurve_iff_equation _ _ _ _).mpr hP.1)

end RankCertificates.LocalSeven
