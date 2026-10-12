module

public import RankCertificates.LocalCharacterRows

/-!
Necessary local restrictions when the integral equation reduces to
`Y² = X (X-t)²` and `t` is a nonzero square. The repeated-root case is
handled by its square residue, without assuming discriminant valuation one.
-/

@[expose] public section

namespace RankCertificates.SplitReductionDescent

open LocalValuations

variable (p : ℕ) [Fact p.Prime]

/-- Reduction to a split double root forces every nonzero unit coordinate
to have square residue, including the repeated root itself. -/
theorem unit_coordinate_square (A B : ℤ) (t : ZMod p)
    (ht : IsSquare t) (hA : (A : ZMod p) = -2 * t)
    (hB : (B : ZMod p) = t ^ 2) {x y : ℚ}
    (hvx : padicValRat p x = 0) (h : OnCurve (A : ℚ) (B : ℚ) x y) :
    IsSquare (unitResidue p x) := by
  have he := onCurve_residue p A B h
    (denominator_unit_of_nonnegative_valuation p x (by omega))
  rw [hA, hB] at he
  have hf : (rationalResidue p y) ^ 2 =
      rationalResidue p x * (rationalResidue p x - t) ^ 2 := by
    linear_combination he
  have hunit : unitResidue p x = rationalResidue p x := by
    simp only [unitResidue, normalizedUnit, hvx, zpow_zero, div_one]
  rw [hunit]
  by_cases hr : rationalResidue p x = t
  · exact hr ▸ ht
  · refine ⟨rationalResidue p y / (rationalResidue p x - t), ?_⟩
    have hd : rationalResidue p x - t ≠ 0 := sub_ne_zero.mpr hr
    field_simp [hd]
    linear_combination -hf

/-- Unit linear coefficient gives even coordinate valuation. The split
reduction further forces the normalized unit to be a square. -/
theorem coordinate_conditions (A B : ℤ) (t : ZMod p)
    (ht0 : t ≠ 0) (ht : IsSquare t) (hA : (A : ZMod p) = -2 * t)
    (hB : (B : ZMod p) = t ^ 2) {x y : ℚ} (hx : x ≠ 0)
    (h : OnCurve (A : ℚ) (B : ℚ) x y) :
    Even (padicValRat p x) ∧ IsSquare (unitResidue p x) := by
  have hBne : (B : ZMod p) ≠ 0 := hB ▸ pow_ne_zero 2 ht0
  have hBnot : ¬ (p : ℤ) ∣ B := fun hd =>
    hBne ((ZMod.intCast_zmod_eq_zero_iff_dvd B p).mpr hd)
  have hB0 : (B : ℚ) ≠ 0 := by
    exact_mod_cast (show B ≠ 0 from fun hz => hBnot (hz ▸ dvd_zero _))
  have hBval : padicValRat p (B : ℚ) = 0 := by
    rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hBnot]
    rfl
  have hAnonneg := LocalDescent.valuation_int_nonnegative (p := p) A
  have hBsquare : IsSquare (unitResidue p (B : ℚ)) := by
    rw [unitResidue_int_of_not_dvd p hBnot, hB]
    exact ⟨t, by ring⟩
  refine ⟨LocalDescent.integral_x_valuation_even (p := p) A B hBnot hx h, ?_⟩
  rcases lt_trichotomy (padicValRat p x) 0 with hvx | hvx | hvx
  · apply squareApproximation_unitResidue_isSquare p hx
    apply LocalDescent.cubic_term_square_approximation hx _ (Or.inr (by omega)) h
    by_cases hAzero : (A : ℚ) = 0
    · exact Or.inl hAzero
    · exact Or.inr (by omega)
  · exact unit_coordinate_square p A B t ht hA hB hvx h
  · have hquadratic : (A : ℚ) = 0 ∨
        padicValRat p (B : ℚ) < padicValRat p (A : ℚ) + padicValRat p x := by
      by_cases hAzero : (A : ℚ) = 0
      · exact Or.inl hAzero
      · exact Or.inr (by omega)
    have hs := squareApproximation_unitResidue_isSquare p (mul_ne_zero hB0 hx)
      (LocalDescent.linear_term_square_approximation (p := p) hB0 hx
        (by omega) hquadratic h)
    have he : unitResidue p x = unitResidue p ((B : ℚ) * x) /
        unitResidue p (B : ℚ) := by
      rw [unitResidue_mul p hB0 hx]
      field_simp [unitResidue_ne_zero p hB0]
    rw [he]
    exact hs.div hBsquare

/-- Being a square normalized residue depends only on the genuine rational
squareclass, not its chosen nonzero representative. -/
theorem same_squareclass_unitResidue_square {x z : ℚ} (hx : x ≠ 0) (hz : z ≠ 0)
    (hc : rationalSquareClass x = rationalSquareClass z)
    (hsx : IsSquare (unitResidue p x)) : IsSquare (unitResidue p z) := by
  have hclass : rationalSquareClass (x * z) = 1 := by
    rw [rationalSquareClass_mul hx hz, hc]
    exact rationalSquareClass_mul_self z
  obtain ⟨s, hs, heq⟩ := (rationalSquareClass_eq_one_iff (mul_ne_zero hx hz)).mp hclass
  have hprod : IsSquare (unitResidue p (x * z)) := by
    rw [heq]
    exact unitResidue_square p hs
  have hu : unitResidue p z = unitResidue p (x * z) / unitResidue p x := by
    rw [unitResidue_mul p hx hz]
    field_simp [unitResidue_ne_zero p hx]
  rw [hu]
  exact hprod.div hsx

/-- Every representative of every genuine image class has even valuation
and square normalized unit in the split-square-root reduction case. -/
theorem image_conditions (A B : ℤ) (t : ZMod p)
    (ht0 : t ≠ 0) (ht : IsSquare t) (hA : (A : ZMod p) = -2 * t)
    (hB : (B : ZMod p) = t ^ 2) {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (A : ℚ) (B : ℚ))
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) :
    Even (padicValRat p z) ∧ IsSquare (unitResidue p z) := by
  have hBne : (B : ZMod p) ≠ 0 := hB ▸ pow_ne_zero 2 ht0
  have hBnot : ¬ (p : ℤ) ∣ B := fun hd =>
    hBne ((ZMod.intCast_zmod_eq_zero_iff_dvd B p).mpr hd)
  have hB0 : (B : ℚ) ≠ 0 := by
    exact_mod_cast (show B ≠ 0 from fun hz => hBnot (hz ▸ dvd_zero _))
  have heven := LocalDescent.twoIsogenyImage_even_valuation (p := p) A B hBnot hq z hz hc
  refine ⟨heven, ?_⟩
  obtain ⟨P, rfl⟩ := hq
  cases P with
  | zero =>
    apply same_squareclass_unitResidue_square p one_ne_zero hz
      (rationalSquareClass_one.trans hc.symm)
    exact ⟨1, by simp [unitResidue, normalizedUnit, rationalResidue]⟩
  | some x y hP =>
    by_cases hx : x = 0
    · simp only [twoIsogenyClass, hx, ite_true] at hc
      apply same_squareclass_unitResidue_square p hB0 hz hc.symm
      rw [unitResidue_int_of_not_dvd p hBnot, hB]
      exact ⟨t, by ring⟩
    · simp only [twoIsogenyClass, hx, ite_false] at hc
      apply same_squareclass_unitResidue_square p hx hz hc.symm
      exact (coordinate_conditions p A B t ht0 ht hA hB hx
        ((onCurve_iff_equation _ _ _ _).mpr hP.1)).2

/-- The split-square-root restriction as normalized quadratic character. -/
theorem image_character_conditions (A B : ℤ) (t : ZMod p)
    (ht0 : t ≠ 0) (ht : IsSquare t) (hA : (A : ZMod p) = -2 * t)
    (hB : (B : ZMod p) = t ^ 2) {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (A : ℚ) (B : ℚ))
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) :
    Even (padicValRat p z) ∧ unitCharacter p z = 1 := by
  have hh := image_conditions p A B t ht0 ht hA hB hq hz hc
  exact ⟨hh.1, (unitCharacter_eq_one_iff p hz).mpr hh.2⟩

/-- Both genuine binary functionals vanish on the actual image. -/
theorem image_rows (A B : ℤ) (t : ZMod p)
    (ht0 : t ≠ 0) (ht : IsSquare t) (hA : (A : ZMod p) = -2 * t)
    (hB : (B : ZMod p) = t ^ 2) {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (A : ℚ) (B : ℚ)) :
    valuationParityLinear p (Additive.ofMul q) = 0 ∧
      unitCharacterLinear p (Additive.ofMul q) = 0 := by
  revert hq
  refine QuotientGroup.induction_on q fun u hq => ?_
  have hh := image_character_conditions p A B t ht0 ht hA hB hq
    u.ne_zero (rationalSquareClass_unit u)
  rw [← rationalSquareClass_unit u]
  constructor
  · change primeParity p (Fact.out : p.Prime)
      (Additive.ofMul (rationalSquareClass (u : ℚ))) = 0
    rw [primeParity_apply (Fact.out : p.Prime) u.ne_zero]
    exact hh.1.intCast_zmod_two
  · change unitCharacterParity p (Additive.ofMul (rationalSquareClass (u : ℚ))) = 0
    rw [unitCharacterParity_apply p u.ne_zero, hh.2, quadraticCharacterBit_one]

end RankCertificates.SplitReductionDescent
