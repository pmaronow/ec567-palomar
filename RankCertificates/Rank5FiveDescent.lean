module

public import RankCertificates.PrimeCoefficientSupport
public import RankCertificates.LocalValuations

@[expose] public section

/-!
# The actual fixed-prime restriction at 5 for the final rank-5 family
-/

namespace RankCertificates.Rank5FiveDescent

open LocalValuations

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem valuation_five : padicValRat 5 (5 : ℚ) = 1 := by
  simpa only [Nat.cast_ofNat] using padicValRat.self (p := 5) (by decide : 1 < 5)

theorem five_roots_square {u : ZMod 5} (h : u ^ 2 + 4 = 0) : IsSquare u := by
  have hr : u = 1 ∨ u = 4 := by
    revert u
    decide
  rcases hr with rfl | rfl
  · exact ⟨1, by decide⟩
  · exact ⟨2, by decide⟩

/-- The normalized quadratic character is invariant under genuine
rational squareclass equality, at every prime. -/
theorem same_squareclass_unitResidue_square (p : ℕ) [Fact p.Prime] {x z : ℚ}
    (hx : x ≠ 0) (hz : z ≠ 0) (hc : rationalSquareClass x = rationalSquareClass z)
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

theorem exceptional_coordinate_square (a₁ b₁ : ℤ) {x y : ℚ}
    (hb : (b₁ : ZMod 5) = 4) (hx : x ≠ 0) (hvx : padicValRat 5 x = 1)
    (h : OnCurve (125 * (a₁ : ℚ)) (25 * (b₁ : ℚ)) x y) :
    IsSquare (unitResidue 5 x) := by
  let u : ℚ := x / 5
  have hu : u ≠ 0 := div_ne_zero hx (by norm_num)
  have huv : padicValRat 5 u = 0 := by
    dsimp [u]
    rw [padicValRat.div hx (by norm_num), hvx, valuation_five]
    norm_num
  have hd := denominator_unit_of_nonnegative_valuation 5 u (by omega)
  have hd0 : (u.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr u.den_ne_zero
  let g : ℤ := u.num ^ 2 + 25 * a₁ * u.num * u.den + b₁ * (u.den : ℤ) ^ 2
  have hfactor : u ^ 2 + 25 * (a₁ : ℚ) * u + b₁ = (g : ℚ) / (u.den : ℚ) ^ 2 := by
    dsimp [g]
    simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_ofNat]
    conv_lhs => rw [← u.num_div_den]
    field_simp [hd0]
  have hg : (g : ZMod 5) = 0 := by
    by_contra hg
    have hgn : ¬ (5 : ℤ) ∣ g := by
      intro hdiv
      exact hg ((ZMod.intCast_zmod_eq_zero_iff_dvd g 5).mpr hdiv)
    have hg0 : (g : ℚ) ≠ 0 := by
      exact_mod_cast (show g ≠ 0 from fun hz => hgn (hz ▸ dvd_zero _))
    have hgv : padicValRat 5 (g : ℚ) = 0 := by
      rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hgn]
      rfl
    have hdv : padicValRat 5 (u.den : ℚ) = 0 := by
      rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd
        (fun hh => hd ((ZMod.natCast_eq_zero_iff _ _).mpr hh))]
      rfl
    have hf0 : u ^ 2 + 25 * (a₁ : ℚ) * u + b₁ ≠ 0 := by
      rw [hfactor]
      exact div_ne_zero hg0 (pow_ne_zero 2 hd0)
    have hfv : padicValRat 5 (u ^ 2 + 25 * (a₁ : ℚ) * u + b₁) = 0 := by
      rw [hfactor, padicValRat.div hg0 (pow_ne_zero 2 hd0), padicValRat.pow, hgv, hdv]
      norm_num
    have heq : y ^ 2 = 125 * u * (u ^ 2 + 25 * (a₁ : ℚ) * u + b₁) := by
      dsimp [u]
      unfold OnCurve at h
      linear_combination h
    have h125 : padicValRat 5 (125 : ℚ) = 3 := by
      rw [show (125 : ℚ) = (5 : ℚ) ^ 3 by norm_num, padicValRat.pow, valuation_five]
      norm_num
    have hh := congrArg (padicValRat 5) heq
    rw [padicValRat.pow, padicValRat.mul (mul_ne_zero (by norm_num) hu) hf0,
      padicValRat.mul (by norm_num) hu, h125, huv, hfv] at hh
    omega
  have hroot : (rationalResidue 5 u) ^ 2 + 4 = 0 := by
    dsimp [g] at hg
    simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_ofNat] at hg
    rw [hb, show (25 : ZMod 5) = 0 by decide] at hg
    simp only [zero_mul, add_zero] at hg
    simp only [rationalResidue]
    field_simp
    linear_combination hg
  have hnorm : normalizedUnit 5 x = u := by
    simp only [normalizedUnit, hvx, zpow_one]
    rfl
  rw [unitResidue, hnorm]
  exact five_roots_square hroot

theorem normalized_model_coordinate_square (a₁ b₁ : ℤ) {x y : ℚ}
    (hb : (b₁ : ZMod 5) = 4) (hx : x ≠ 0)
    (h : OnCurve (125 * (a₁ : ℚ)) (25 * (b₁ : ℚ)) x y) :
    IsSquare (unitResidue 5 x) := by
  have hbnot : ¬ (5 : ℤ) ∣ b₁ := by
    intro hdiv
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd b₁ 5).mpr hdiv
    rw [hb] at hz
    exact (by decide : (4 : ZMod 5) ≠ 0) hz
  have hb0 : (b₁ : ℚ) ≠ 0 := by
    exact_mod_cast (show b₁ ≠ 0 from fun hz => hbnot (hz ▸ dvd_zero _))
  have hbval : padicValRat 5 (b₁ : ℚ) = 0 := by
    rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hbnot]
    rfl
  have h25 : padicValRat 5 (25 : ℚ) = 2 := by
    rw [show (25 : ℚ) = (5 : ℚ) ^ 2 by norm_num, padicValRat.pow, valuation_five]
    norm_num
  have h125 : padicValRat 5 (125 : ℚ) = 3 := by
    rw [show (125 : ℚ) = (5 : ℚ) ^ 3 by norm_num, padicValRat.pow, valuation_five]
    norm_num
  have hB0 : 25 * (b₁ : ℚ) ≠ 0 := mul_ne_zero (by norm_num) hb0
  have hB : padicValRat 5 (25 * (b₁ : ℚ)) = 2 := by
    rw [padicValRat.mul (by norm_num) hb0, h25, hbval]
    norm_num
  have hunitB : unitResidue 5 (25 * (b₁ : ℚ)) = 4 := by
    have hn : normalizedUnit 5 (25 * (b₁ : ℚ)) = b₁ := by
      simp only [normalizedUnit, hB]
      norm_num
    rw [unitResidue, hn, rationalResidue_int, hb]
  have haVal : a₁ = 0 ∨ 3 ≤ padicValRat 5 (125 * (a₁ : ℚ)) := by
    by_cases ha0 : a₁ = 0
    · exact Or.inl ha0
    · right
      have ha0q : (a₁ : ℚ) ≠ 0 := Int.cast_ne_zero.mpr ha0
      rw [padicValRat.mul (by norm_num) ha0q, h125]
      have hv := LocalDescent.valuation_int_nonnegative (p := 5) a₁
      omega
  rcases lt_trichotomy (padicValRat 5 x) 1 with hr | hr | hr
  · apply squareApproximation_unitResidue_isSquare 5 hx
    apply LocalDescent.cubic_term_square_approximation hx _ (Or.inr (by omega)) h
    rcases haVal with ha0 | haVal
    · left; simp [ha0]
    · right; omega
  · exact exceptional_coordinate_square a₁ b₁ hb hx hr h
  · have hquadratic : 125 * (a₁ : ℚ) = 0 ∨
        padicValRat 5 (25 * (b₁ : ℚ)) < padicValRat 5 (125 * (a₁ : ℚ)) + padicValRat 5 x := by
      rcases haVal with ha0 | haVal
      · left; simp [ha0]
      · right; omega
    have hap := LocalDescent.linear_term_square_approximation (p := 5) hB0 hx
      (by omega) hquadratic h
    have hs := squareApproximation_unitResidue_isSquare 5 (mul_ne_zero hB0 hx) hap
    have hBsq : IsSquare (unitResidue 5 (25 * (b₁ : ℚ))) := by
      rw [hunitB]
      exact ⟨2, by decide⟩
    have heq : unitResidue 5 x = unitResidue 5 (25 * (b₁ : ℚ) * x) /
        unitResidue 5 (25 * (b₁ : ℚ)) := by
      rw [unitResidue_mul 5 hB0 hx]
      field_simp [unitResidue_ne_zero 5 hB0]
    rw [heq]
    exact hs.div hBsq

theorem normalized_model_torsion_square (b₁ : ℤ) (hb : (b₁ : ZMod 5) = 4) :
    IsSquare (unitResidue 5 (25 * (b₁ : ℚ))) := by
  have hbnot : ¬ (5 : ℤ) ∣ b₁ := by
    intro hdiv
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd b₁ 5).mpr hdiv
    rw [hb] at hz
    exact (by decide : (4 : ZMod 5) ≠ 0) hz
  have hb0 : (b₁ : ℚ) ≠ 0 := by
    exact_mod_cast (show b₁ ≠ 0 from fun hz => hbnot (hz ▸ dvd_zero _))
  have hbval : padicValRat 5 (b₁ : ℚ) = 0 := by
    rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hbnot]
    rfl
  have h25 : padicValRat 5 (25 : ℚ) = 2 := by
    rw [show (25 : ℚ) = (5 : ℚ) ^ 2 by norm_num, padicValRat.pow, valuation_five]
    norm_num
  have hB : padicValRat 5 (25 * (b₁ : ℚ)) = 2 := by
    rw [padicValRat.mul (by norm_num) hb0, h25, hbval]
    norm_num
  have hn : normalizedUnit 5 (25 * (b₁ : ℚ)) = b₁ := by
    simp only [normalizedUnit, hB]
    norm_num
  rw [unitResidue, hn, rationalResidue_int, hb]
  exact ⟨2, by decide⟩

theorem normalized_model_image_square (a₁ b₁ : ℤ) (hb : (b₁ : ZMod 5) = 4)
    {q : RationalSquareClasses} (hq : q ∈ twoIsogenyImage (125 * (a₁ : ℚ)) (25 * (b₁ : ℚ)))
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) :
    IsSquare (unitResidue 5 z) := by
  obtain ⟨P, rfl⟩ := hq
  cases P with
  | zero =>
    apply same_squareclass_unitResidue_square 5 one_ne_zero hz
      (rationalSquareClass_one.trans hc.symm)
    simp [unitResidue, normalizedUnit, rationalResidue]
  | some x y hP =>
    by_cases hx : x = 0
    · simp only [twoIsogenyClass, hx, ite_true] at hc
      have hb0 : (b₁ : ℚ) ≠ 0 := by
        intro hzero
        have hbint : b₁ = 0 := Int.cast_eq_zero.mp hzero
        rw [hbint, Int.cast_zero] at hb
        exact (by decide : (0 : ZMod 5) ≠ 4) hb
      exact same_squareclass_unitResidue_square 5 (mul_ne_zero (by norm_num) hb0)
        hz hc.symm (normalized_model_torsion_square b₁ hb)
    · simp only [twoIsogenyClass, hx, ite_false] at hc
      exact same_squareclass_unitResidue_square 5 hx hz hc.symm
        (normalized_model_coordinate_square a₁ b₁ hb hx ((onCurve_iff_equation _ _ _ _).mpr hP.1))

def FInt (m n : ℤ) : ℤ := m * (22 * m - n) * (9 * m - 2 * n) * (143 * m + 155 * n)
def HInt (m n : ℤ) : ℤ :=
  (-55 * m + 62 * n) * (3 * m - n) * (138 * m - 31 * n) * (55 * m + 64 * n)
def JInt (m n : ℤ) : ℤ :=
  (99 * m + 62 * n) * (5 * m - n) * (32 * m + 31 * n) * (55 * m - 12 * n)

theorem quartic_cast (m n : ℤ) :
    (FInt m n : ℚ) = Rank5.F (m : ℚ) (n : ℚ) ∧
    (HInt m n : ℚ) = Rank5.H (m : ℚ) (n : ℚ) ∧
    (JInt m n : ℚ) = Rank5.J (m : ℚ) (n : ℚ) := by
  simp [FInt, HInt, JInt, Rank5.F, Rank5.H, Rank5.J,
    Rank5.L0, Rank5.L1, Rank5.L2, Rank5.L3, Rank5.L4, Rank5.L5,
    Rank5.L6, Rank5.L7, Rank5.L8, Rank5.L9, Rank5.L10, Rank5.L11]

def latticeM (x : ℤ) : ℤ := PrimePatterns.Rank5.M0 + PrimePatterns.Rank5.W * x
def latticeN (y : ℤ) : ℤ := PrimePatterns.Rank5.N0 + PrimePatterns.Rank5.W * y
def a₁Int (x y : ℤ) : ℤ := 12 * FInt (latticeM x) (latticeN y)
def b₁Int (x y : ℤ) : ℤ := -108 * FInt (latticeM x) (latticeN y) * HInt (latticeM x) (latticeN y)
def dualA₁Int (x y : ℤ) : ℤ := -24 * FInt (latticeM x) (latticeN y)
def dualB₁Int (x y : ℤ) : ℤ := 2304 * FInt (latticeM x) (latticeN y) * JInt (latticeM x) (latticeN y)

theorem lattice_mod_five (x y : ℤ) :
    (latticeM x : ZMod 5) = 4 ∧ (latticeN y : ZMod 5) = 4 := by
  have hW : (PrimePatterns.Rank5.W : ZMod 5) = 0 := by decide
  have hM : (PrimePatterns.Rank5.M0 : ZMod 5) = 4 := by decide
  have hN : (PrimePatterns.Rank5.N0 : ZMod 5) = 4 := by decide
  simp only [latticeM, latticeN, Int.cast_add, Int.cast_mul, hW, hM, hN,
    zero_mul, add_zero, and_self]

theorem quartic_mod_five (x y : ℤ) :
    (FInt (latticeM x) (latticeN y) : ZMod 5) = 1 ∧
    (HInt (latticeM x) (latticeN y) : ZMod 5) = 2 ∧
    (JInt (latticeM x) (latticeN y) : ZMod 5) = 1 := by
  obtain ⟨hM, hN⟩ := lattice_mod_five x y
  simp only [FInt, HInt, JInt, Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_neg,
    Int.cast_ofNat, hM, hN]
  decide

theorem normalized_coefficients (x y : ℤ) :
    Rank5.a (Integration.M5 x) (Integration.N5 y) = 125 * (a₁Int x y : ℚ) ∧
    Rank5.b (Integration.M5 x) (Integration.N5 y) = 25 * (b₁Int x y : ℚ) ∧
    -2 * Rank5.a (Integration.M5 x) (Integration.N5 y) = 125 * (dualA₁Int x y : ℚ) ∧
    Rank5.c (Integration.M5 x) (Integration.N5 y) = 25 * (dualB₁Int x y : ℚ) := by
  have hg := quartic_cast (latticeM x) (latticeN y)
  change (FInt (latticeM x) (latticeN y) : ℚ) = Rank5.F (Integration.M5 x) (Integration.N5 y) ∧
    (HInt (latticeM x) (latticeN y) : ℚ) = Rank5.H (Integration.M5 x) (Integration.N5 y) ∧
    (JInt (latticeM x) (latticeN y) : ℚ) = Rank5.J (Integration.M5 x) (Integration.N5 y) at hg
  obtain ⟨hF, hH, hJ⟩ := hg
  simp only [a₁Int, b₁Int, dualA₁Int, dualB₁Int, Int.cast_mul, Int.cast_neg, Int.cast_ofNat,
    hF, hH, hJ, Rank5.a, Rank5.b, Rank5.c]
  ring_nf
  trivial

theorem normalized_linear_mod_five (x y : ℤ) :
    (b₁Int x y : ZMod 5) = 4 ∧ (dualB₁Int x y : ZMod 5) = 4 := by
  obtain ⟨hF, hH, hJ⟩ := quartic_mod_five x y
  simp only [b₁Int, dualB₁Int, Int.cast_mul, Int.cast_neg, Int.cast_ofNat, hF, hH, hJ]
  decide

/-- Every actual original-curve image has square normalized unit at 5,
on the full lattice, without any prime-output hypothesis. -/
theorem lattice_E_image_square (m n : ℤ) {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (Rank5.a (Integration.M5 m) (Integration.N5 n))
      (Rank5.b (Integration.M5 m) (Integration.N5 n)))
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) :
    IsSquare (unitResidue 5 z) := by
  obtain ⟨ha, hb, _, _⟩ := normalized_coefficients m n
  rw [ha, hb] at hq
  exact normalized_model_image_square (a₁Int m n) (b₁Int m n)
    (normalized_linear_mod_five m n).1 hq hz hc

/-- The same actual fixed-prime condition for the partner curve. -/
theorem lattice_Ep_image_square (m n : ℤ) {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (-2 * Rank5.a (Integration.M5 m) (Integration.N5 n))
      (Rank5.c (Integration.M5 m) (Integration.N5 n)))
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) :
    IsSquare (unitResidue 5 z) := by
  obtain ⟨_, _, ha, hb⟩ := normalized_coefficients m n
  rw [ha, hb] at hq
  exact normalized_model_image_square (dualA₁Int m n) (dualB₁Int m n)
    (normalized_linear_mod_five m n).2 hq hz hc

theorem lattice_E_image_character (m n : ℤ) {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (Rank5.a (Integration.M5 m) (Integration.N5 n))
      (Rank5.b (Integration.M5 m) (Integration.N5 n)))
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) : unitCharacter 5 z = 1 :=
  (unitCharacter_eq_one_iff 5 hz).mpr (lattice_E_image_square m n hq hz hc)

theorem lattice_Ep_image_character (m n : ℤ) {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (-2 * Rank5.a (Integration.M5 m) (Integration.N5 n))
      (Rank5.c (Integration.M5 m) (Integration.N5 n)))
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) : unitCharacter 5 z = 1 :=
  (unitCharacter_eq_one_iff 5 hz).mpr (lattice_Ep_image_square m n hq hz hc)

end RankCertificates.Rank5FiveDescent
