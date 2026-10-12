module

public import RankCertificates.PrimeCoefficientSupport
public import RankCertificates.LocalValuations

@[expose] public section

/-!
# The actual fixed-prime restriction at 3 for the final rank-5 family

The exceptional coordinate valuation one is excluded by the actual cubic
equation.  The other branches give even valuation and square unit residue.
-/

namespace RankCertificates.Rank5ThreeDescent

open LocalValuations

theorem valuation_three : padicValRat 3 (3 : ℚ) = 1 := by
  simpa only [Nat.cast_ofNat] using padicValRat.self (p := 3) (by decide : 1 < 3)

theorem exceptional_valuation_impossible (a₁ b₁ : ℤ) {x y : ℚ}
    (hb : (b₁ : ZMod 3) = 1) (hx : x ≠ 0) (hvx : padicValRat 3 x = 1)
    (h : OnCurve (9 * (a₁ : ℚ)) (9 * (b₁ : ℚ)) x y) : False := by
  let u : ℚ := x / 3
  have hu : u ≠ 0 := div_ne_zero hx (by norm_num)
  have huv : padicValRat 3 u = 0 := by
    dsimp [u]
    rw [padicValRat.div hx (by norm_num), hvx, valuation_three]
    norm_num
  have hd := denominator_unit_of_nonnegative_valuation 3 u (by omega)
  have hn : (u.num : ZMod 3) ≠ 0 := by
    have hh := residue_ne_zero_of_valuation_zero 3 hu huv
    intro hz
    apply hh
    simp [rationalResidue, hz]
  have hns : (u.num : ZMod 3) ^ 2 = 1 := by
    simpa only [pow_two] using three_unit_square hn
  have hds : (u.den : ZMod 3) ^ 2 = 1 := by
    simpa only [pow_two] using three_unit_square hd
  let g : ℤ := u.num ^ 2 + 3 * a₁ * u.num * u.den + b₁ * (u.den : ℤ) ^ 2
  have hg : (g : ZMod 3) = 2 := by
    dsimp [g]
    simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_ofNat]
    rw [hns, hds, hb, show (3 : ZMod 3) = 0 by decide]
    norm_num
  have hgn : ¬ (3 : ℤ) ∣ g := by
    intro hdiv
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd g 3).mpr hdiv
    rw [hg] at hz
    exact (by decide : (2 : ZMod 3) ≠ 0) hz
  have hg0 : (g : ℚ) ≠ 0 := by
    exact_mod_cast (show g ≠ 0 from fun hz => hgn (hz ▸ dvd_zero _))
  have hgv : padicValRat 3 (g : ℚ) = 0 := by
    rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hgn]
    rfl
  have hdv : padicValRat 3 (u.den : ℚ) = 0 := by
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd
      (fun hh => hd ((ZMod.natCast_eq_zero_iff _ _).mpr hh))]
    rfl
  have hd0 : (u.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr u.den_ne_zero
  have hfactor : u ^ 2 + 3 * (a₁ : ℚ) * u + b₁ = (g : ℚ) / (u.den : ℚ) ^ 2 := by
    dsimp [g]
    simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_ofNat]
    conv_lhs => rw [← u.num_div_den]
    field_simp [hd0]
  have hf0 : u ^ 2 + 3 * (a₁ : ℚ) * u + b₁ ≠ 0 := by
    rw [hfactor]
    exact div_ne_zero hg0 (pow_ne_zero 2 hd0)
  have hfv : padicValRat 3 (u ^ 2 + 3 * (a₁ : ℚ) * u + b₁) = 0 := by
    rw [hfactor, padicValRat.div hg0 (pow_ne_zero 2 hd0), padicValRat.pow, hgv, hdv]
    norm_num
  have heq : y ^ 2 = 27 * u * (u ^ 2 + 3 * (a₁ : ℚ) * u + b₁) := by
    dsimp [u]
    unfold OnCurve at h
    linear_combination h
  have h27 : padicValRat 3 (27 : ℚ) = 3 := by
    rw [show (27 : ℚ) = (3 : ℚ) ^ 3 by norm_num, padicValRat.pow, valuation_three]
    norm_num
  have hh := congrArg (padicValRat 3) heq
  rw [padicValRat.pow, padicValRat.mul (mul_ne_zero (by norm_num) hu) hf0,
    padicValRat.mul (by norm_num) hu, h27, huv, hfv] at hh
  omega

theorem approximation_conditions {x : ℚ} (hx : x ≠ 0)
    (h : LocalDescent.SquareApproximation 3 x) :
    Even (padicValRat 3 x) ∧ unitResidue 3 x = 1 := by
  refine ⟨LocalDescent.square_approximation_even_valuation hx h, ?_⟩
  obtain ⟨r, hr⟩ := squareApproximation_unitResidue_isSquare 3 hx h
  have hr0 : r ≠ 0 := by
    intro hz
    apply unitResidue_ne_zero 3 hx
    rw [hr, hz]
    norm_num
  rw [hr]
  exact three_unit_square hr0

theorem normalized_model_coordinate_conditions (a₁ b₁ : ℤ) {x y : ℚ}
    (hb : (b₁ : ZMod 3) = 1) (hx : x ≠ 0)
    (h : OnCurve (9 * (a₁ : ℚ)) (9 * (b₁ : ℚ)) x y) :
    Even (padicValRat 3 x) ∧ unitResidue 3 x = 1 := by
  have hbnot : ¬ (3 : ℤ) ∣ b₁ := by
    intro hdiv
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd b₁ 3).mpr hdiv
    rw [hb] at hz
    exact one_ne_zero hz
  have hb0 : (b₁ : ℚ) ≠ 0 := by
    exact_mod_cast (show b₁ ≠ 0 from fun hz => hbnot (hz ▸ dvd_zero _))
  have hbval : padicValRat 3 (b₁ : ℚ) = 0 := by
    rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hbnot]
    rfl
  have h9 : padicValRat 3 (9 : ℚ) = 2 := by
    rw [show (9 : ℚ) = (3 : ℚ) ^ 2 by norm_num, padicValRat.pow, valuation_three]
    norm_num
  have hB0 : 9 * (b₁ : ℚ) ≠ 0 := mul_ne_zero (by norm_num) hb0
  have hB : padicValRat 3 (9 * (b₁ : ℚ)) = 2 := by
    rw [padicValRat.mul (by norm_num) hb0, h9, hbval]
    norm_num
  have hunitB : unitResidue 3 (9 * (b₁ : ℚ)) = 1 := by
    have hn : normalizedUnit 3 (9 * (b₁ : ℚ)) = b₁ := by
      simp only [normalizedUnit, hB]
      norm_num
    rw [unitResidue, hn, rationalResidue_int, hb]
  have haVal : a₁ = 0 ∨ 2 ≤ padicValRat 3 (9 * (a₁ : ℚ)) := by
    by_cases ha0 : a₁ = 0
    · exact Or.inl ha0
    · right
      have ha0q : (a₁ : ℚ) ≠ 0 := Int.cast_ne_zero.mpr ha0
      rw [padicValRat.mul (by norm_num) ha0q, h9]
      have hv := LocalDescent.valuation_int_nonnegative (p := 3) a₁
      omega
  rcases lt_trichotomy (padicValRat 3 x) 1 with hr | hr | hr
  · apply approximation_conditions hx
    apply LocalDescent.cubic_term_square_approximation hx _ (Or.inr (by omega)) h
    rcases haVal with ha0 | haVal
    · left; simp [ha0]
    · right; omega
  · exact False.elim (exceptional_valuation_impossible a₁ b₁ hb hx hr h)
  · have hquadratic : 9 * (a₁ : ℚ) = 0 ∨
        padicValRat 3 (9 * (b₁ : ℚ)) < padicValRat 3 (9 * (a₁ : ℚ)) + padicValRat 3 x := by
      rcases haVal with ha0 | haVal
      · left; simp [ha0]
      · right; omega
    have hap := LocalDescent.linear_term_square_approximation (p := 3) hB0 hx
      (by omega) hquadratic h
    obtain ⟨he, hu⟩ := approximation_conditions (mul_ne_zero hB0 hx) hap
    rw [padicValRat.mul hB0 hx, hB] at he
    obtain ⟨k, hk⟩ := he
    refine ⟨⟨k - 1, by omega⟩, ?_⟩
    rw [unitResidue_mul 3 hB0 hx, hunitB, one_mul] at hu
    exact hu

def outputInt (x y : ℤ) (i : Fin 12) : ℤ :=
  (PrimePatterns.Rank5.outputs i).eval x y

def a₁Int (x y : ℤ) : ℤ :=
  8000 * (outputInt x y 0 * outputInt x y 1 * outputInt x y 2 * outputInt x y 3)

def b₁Int (x y : ℤ) : ℤ :=
  -25600 * (outputInt x y 0 * outputInt x y 1 * outputInt x y 2 * outputInt x y 3) *
    (outputInt x y 4 * outputInt x y 5 * outputInt x y 6 * outputInt x y 7)

theorem output_mod_three (x y : ℤ) (i : Fin 12) :
    (outputInt x y i : ZMod 3) = (PrimePatterns.Rank5.mod3Units i : ZMod 3) := by
  have ha : ((PrimePatterns.Rank5.outputs i).a : ZMod 3) = 0 := by
    fin_cases i <;> decide
  have hb : ((PrimePatterns.Rank5.outputs i).b : ZMod 3) = 0 := by
    fin_cases i <;> decide
  have hc : ((PrimePatterns.Rank5.outputs i).c : ZMod 3) =
      (PrimePatterns.Rank5.mod3Units i : ZMod 3) := by
    fin_cases i <;> decide
  simp only [outputInt, PrimePatterns.AffineForm.eval, Int.cast_add, Int.cast_mul,
    ha, hb, hc, zero_mul, zero_add]

theorem b₁Int_mod_three (x y : ℤ) : (b₁Int x y : ZMod 3) = 1 := by
  simp only [b₁Int, Int.cast_mul, Int.cast_neg, Int.cast_ofNat, output_mod_three,
    PrimePatterns.Rank5.mod3Units]
  change -(25600 : ZMod 3) * (1 * 1 * 1 * 1) * (2 * 1 * 1 * 1) = 1
  decide

theorem coefficients_normalized (x y : ℤ) :
    Rank5.a (Integration.M5 x) (Integration.N5 y) = 81 * (a₁Int x y : ℚ) ∧
    Rank5.b (Integration.M5 x) (Integration.N5 y) = 729 * (b₁Int x y : ℚ) := by
  obtain ⟨hF, hH, _⟩ := lattice5_factorGroups x y
  constructor
  · simp only [Rank5.a, hF, a₁Int, outputInt, Integration.outputs5, Int.cast_mul, Int.cast_ofNat]
    ring
  · simp only [Rank5.b, hF, hH, b₁Int, outputInt, Integration.outputs5,
      Int.cast_mul, Int.cast_neg, Int.cast_ofNat]
    ring

/-- The actual rank-5 curve, on its entire CRT lattice, has trivial
normalized 3-adic coordinate character.  Prime outputs are not assumed. -/
theorem lattice_coordinate_conditions (m n : ℤ) {x y : ℚ} (hx : x ≠ 0)
    (h : OnCurve (Rank5.a (Integration.M5 m) (Integration.N5 n))
      (Rank5.b (Integration.M5 m) (Integration.N5 n)) x y) :
    Even (padicValRat 3 x) ∧ unitResidue 3 x = 1 := by
  have hscaled : OnCurve (9 * (a₁Int m n : ℚ)) (9 * (b₁Int m n : ℚ)) (x / 9) (y / 27) := by
    obtain ⟨ha, hb⟩ := coefficients_normalized m n
    unfold OnCurve at h ⊢
    rw [ha, hb] at h
    linear_combination (1 / 729 : ℚ) * h
  have hxs : x / 9 ≠ 0 := div_ne_zero hx (by norm_num)
  obtain ⟨hev, hunit⟩ := normalized_model_coordinate_conditions (a₁Int m n) (b₁Int m n)
    (b₁Int_mod_three m n) hxs hscaled
  have hclass : rationalSquareClass x = rationalSquareClass (x / 9) := by
    calc
      _ = rationalSquareClass ((x / 9) * (3 : ℚ) ^ 2) := by congr 1; ring
      _ = _ := rationalSquareClass_mul_square hxs (by norm_num)
  exact ⟨LocalDescent.same_squareclass_even_valuation hx hxs hclass hev,
    (same_squareclass_unitResidue_three hx hxs hclass).trans hunit⟩

/-- The original torsion coefficient obeys the same normalized restriction. -/
theorem lattice_torsion_conditions (m n : ℤ) :
    Even (padicValRat 3 (Rank5.b (Integration.M5 m) (Integration.N5 n))) ∧
      unitResidue 3 (Rank5.b (Integration.M5 m) (Integration.N5 n)) = 1 := by
  have hb := b₁Int_mod_three m n
  have hbnot : ¬ (3 : ℤ) ∣ b₁Int m n := by
    intro hdiv
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdiv
    rw [hb] at hz
    exact one_ne_zero hz
  have hb0 : (b₁Int m n : ℚ) ≠ 0 := by
    exact_mod_cast (show b₁Int m n ≠ 0 from fun hz => hbnot (hz ▸ dvd_zero _))
  have hbval : padicValRat 3 (b₁Int m n : ℚ) = 0 := by
    rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hbnot]
    rfl
  have h729 : padicValRat 3 (729 : ℚ) = 6 := by
    rw [show (729 : ℚ) = (3 : ℚ) ^ 6 by norm_num, padicValRat.pow, valuation_three]
    norm_num
  have hB : padicValRat 3 (Rank5.b (Integration.M5 m) (Integration.N5 n)) = 6 := by
    rw [(coefficients_normalized m n).2, padicValRat.mul (by norm_num) hb0, h729, hbval]
    norm_num
  refine ⟨by rw [hB]; exact ⟨3, by norm_num⟩, ?_⟩
  have hnorm : normalizedUnit 3 (Rank5.b (Integration.M5 m) (Integration.N5 n)) = b₁Int m n := by
    simp only [normalizedUnit]
    rw [hB, (coefficients_normalized m n).2]
    norm_num
  rw [unitResidue, hnorm, rationalResidue_int, hb]

/-- Every representative of every actual rank-5 image class obeys the
fixed-prime restriction at 3, throughout the entire CRT lattice. -/
theorem lattice_image_conditions (m n : ℤ) {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (Rank5.a (Integration.M5 m) (Integration.N5 n))
      (Rank5.b (Integration.M5 m) (Integration.N5 n)))
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) :
    Even (padicValRat 3 z) ∧ unitResidue 3 z = 1 := by
  obtain ⟨P, rfl⟩ := hq
  cases P with
  | zero =>
    have hc1 : rationalSquareClass z = rationalSquareClass 1 :=
      hc.trans rationalSquareClass_one.symm
    refine ⟨LocalDescent.same_squareclass_even_valuation hz one_ne_zero hc1 (by simp), ?_⟩
    rw [same_squareclass_unitResidue_three hz one_ne_zero hc1]
    simp [unitResidue, normalizedUnit, rationalResidue]
  | some x y hP =>
    by_cases hx : x = 0
    · simp only [twoIsogenyClass, hx, ite_true] at hc
      obtain ⟨hF, hH, _⟩ := Integration.products5_nonzero_on_lattice m n
      have hb0 := Rank5.b_ne_zero (Integration.M5 m) (Integration.N5 n) hF hH
      obtain ⟨he, hu⟩ := lattice_torsion_conditions m n
      exact ⟨LocalDescent.same_squareclass_even_valuation hz hb0 hc he,
        (same_squareclass_unitResidue_three hz hb0 hc).trans hu⟩
    · simp only [twoIsogenyClass, hx, ite_false] at hc
      obtain ⟨he, hu⟩ := lattice_coordinate_conditions m n hx
        ((onCurve_iff_equation _ _ _ _).mpr hP.1)
      exact ⟨LocalDescent.same_squareclass_even_valuation hz hx hc he,
        (same_squareclass_unitResidue_three hz hx hc).trans hu⟩

end RankCertificates.Rank5ThreeDescent
