module

public import RankCertificates.Rank6Descent
public import RankCertificates.PrimeCoefficientSupport
public import RankCertificates.DyadicDominance
public import RankCertificates.PrimePowerCharacters
public import RankCertificates.PrimePowerPoints

/-!
# Necessary restrictions at 2 for the actual rank-six family

The literal CRT lattice admits integral models after square scaling by 16.
Both normalized linear coefficients are odd, so every image class has even
2-adic valuation. The partner model also has normalized unit 1 modulo 4.
-/

@[expose] public section

namespace RankCertificates.Rank6TwoDescent

open Integration
open LocalValuations PrimePowerResidues PrimePowerPoints

def outputInt (x y : ℤ) (i : Fin 12) : ℤ := (PrimePatterns.Rank6.outputs i).eval x y
def alphaInt (x y : ℤ) : ℤ :=
  35 * (outputInt x y 0 * outputInt x y 1 * outputInt x y 2 * outputInt x y 3)
def betaInt (x y : ℤ) : ℤ :=
  -49 * (outputInt x y 0 * outputInt x y 1 * outputInt x y 2 * outputInt x y 3) *
    (outputInt x y 4 * outputInt x y 5 * outputInt x y 6 * outputInt x y 7)
def gammaInt (x y : ℤ) : ℤ := alphaInt x y ^ 2 - 4 * betaInt x y

theorem scaled_coefficients (x y : ℤ) :
    Rank6.a (M6 x) (N6 y) = 16 * (alphaInt x y : ℚ) ∧
    Rank6.b (M6 x) (N6 y) = 256 * (betaInt x y : ℚ) ∧
    Rank6.c (M6 x) (N6 y) = 256 * (gammaInt x y : ℚ) := by
  obtain ⟨hF, hH, _⟩ := lattice6_factorGroups x y
  have ha : Rank6.a (M6 x) (N6 y) = 16 * (alphaInt x y : ℚ) := by
    simp only [Rank6.a, hF, alphaInt, outputInt, outputs6, Int.cast_mul, Int.cast_ofNat]
    ring
  have hb : Rank6.b (M6 x) (N6 y) = 256 * (betaInt x y : ℚ) := by
    simp only [Rank6.b, hF, hH, betaInt, outputInt, outputs6, Int.cast_mul, Int.cast_neg, Int.cast_ofNat]
    ring
  refine ⟨ha, hb, ?_⟩
  rw [← Rank6.isogeny_coefficient_identity, ha, hb]
  simp only [gammaInt, Int.cast_sub, Int.cast_pow, Int.cast_mul, Int.cast_ofNat]
  ring

theorem output_mod_eight (x y : ℤ) (i : Fin 12) :
    (outputInt x y i : ZMod 8) = (PrimePatterns.Rank6.mod8Units i : ZMod 8) := by
  rw [ZMod.intCast_eq_intCast_iff']
  dsimp [outputInt]
  rw [PrimePatterns.Rank6.residue8]
  fin_cases i <;> norm_num [PrimePatterns.Rank6.mod8Units]

theorem normalized_residues (x y : ℤ) :
    (alphaInt x y : ZMod 8) = 5 ∧ (betaInt x y : ZMod 8) = 3 ∧
      (gammaInt x y : ZMod 8) = 5 := by
  have h0 := output_mod_eight x y 0
  have h1 := output_mod_eight x y 1
  have h2 := output_mod_eight x y 2
  have h3 := output_mod_eight x y 3
  have h4 := output_mod_eight x y 4
  have h5 := output_mod_eight x y 5
  have h6 := output_mod_eight x y 6
  have h7 := output_mod_eight x y 7
  norm_num [PrimePatterns.Rank6.mod8Units] at h0 h1 h2 h3 h4 h5 h6 h7
  have ha : (alphaInt x y : ZMod 8) = 5 := by
    simp only [alphaInt, Int.cast_mul, Int.cast_ofNat, h0, h1, h2, h3]
    decide
  have hb : (betaInt x y : ZMod 8) = 3 := by
    simp only [betaInt, Int.cast_mul, Int.cast_neg, Int.cast_ofNat, h0, h1, h2, h3, h4, h5, h6, h7]
    decide
  refine ⟨ha, hb, ?_⟩
  simp only [gammaInt, Int.cast_sub, Int.cast_pow, Int.cast_mul, Int.cast_ofNat, ha, hb]
  decide

theorem scaled_point {a b x y : ℚ}
    (h : OnCurve (16 * a) (256 * b) x y) : OnCurve a b (x / 16) (y / 64) := by
  dsimp [OnCurve] at h ⊢
  linear_combination (1 / 4096 : ℚ) * h

theorem scaled_coordinate_class {x : ℚ} (hx : x ≠ 0) :
    rationalSquareClass (x / 16) = rationalSquareClass x := by
  have hx' : x / 16 ≠ 0 := div_ne_zero hx (by norm_num)
  have heq : x = (x / 16) * (4 : ℚ) ^ 2 := by ring
  have hc := rationalSquareClass_mul_square hx' (by norm_num : (4 : ℚ) ≠ 0)
  rw [← heq] at hc
  exact hc.symm

theorem coordinate_even {a b x y : ℚ}
    (ha : 0 ≤ padicValRat 2 a) (hb : padicValRat 2 b = 0)
    (hb0 : b ≠ 0) (hx : x ≠ 0) (h : OnCurve a b x y) :
    Even (padicValRat 2 x) := by
  rcases lt_trichotomy (padicValRat 2 x) 0 with hneg | hz | hpos
  · exact LocalDescent.x_valuation_even_of_negative ha (by omega) hx hneg h
  · rw [hz]; exact ⟨0, by omega⟩
  · exact LocalDescent.x_valuation_even_of_positive ha hb hb0 hx hpos h

theorem scaled_image_even (a b : ℤ) (hb : ¬ (2 : ℤ) ∣ b)
    {q : RationalSquareClasses} (hq : q ∈ twoIsogenyImage (16 * (a : ℚ)) (256 * (b : ℚ)))
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) :
    Even (padicValRat 2 z) := by
  have hb0 : (b : ℚ) ≠ 0 := by
    exact_mod_cast (show b ≠ 0 from fun hz => hb (hz ▸ dvd_zero _))
  obtain ⟨P, rfl⟩ := hq
  cases P with
  | zero =>
    exact LocalDescent.same_squareclass_even_valuation hz one_ne_zero
      (hc.trans rationalSquareClass_one.symm) (by simp)
  | some x y hP =>
    by_cases hx : x = 0
    · simp only [twoIsogenyClass, hx, ite_true] at hc
      have hclass : rationalSquareClass (256 * (b : ℚ)) = rationalSquareClass (b : ℚ) := by
        rw [show 256 * (b : ℚ) = (b : ℚ) * (16 : ℚ) ^ 2 by ring,
          rationalSquareClass_mul_square hb0 (by norm_num)]
      apply LocalDescent.same_squareclass_even_valuation hz hb0 (hc.trans hclass)
      rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hb]
      exact ⟨0, by omega⟩
    · simp only [twoIsogenyClass, hx, ite_false] at hc
      have hx' : x / 16 ≠ 0 := div_ne_zero hx (by norm_num)
      have hp := scaled_point ((onCurve_iff_equation _ _ _ _).mpr hP.1)
      apply LocalDescent.same_squareclass_even_valuation hz hx'
        (hc.trans (scaled_coordinate_class hx).symm)
      exact LocalDescent.integral_x_valuation_even a b hb hx' hp

theorem normalized_linear_odd (x y : ℤ) :
    ¬ (2 : ℤ) ∣ betaInt x y ∧ ¬ (2 : ℤ) ∣ gammaInt x y := by
  obtain ⟨_, hb, hc⟩ := normalized_residues x y
  have hbmod := (ZMod.intCast_eq_intCast_iff' (betaInt x y) 3 8).mp hb
  have hcmod := (ZMod.intCast_eq_intCast_iff' (gammaInt x y) 5 8).mp hc
  norm_num at hbmod hcmod
  constructor
  · intro hd
    have hz := Int.emod_eq_zero_of_dvd hd
    omega
  · intro hd
    have hz := Int.emod_eq_zero_of_dvd hd
    omega

theorem original_image_even (x y : ℤ)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (Rank6.a (M6 x) (N6 y)) (Rank6.b (M6 x) (N6 y)))
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) :
    Even (padicValRat 2 z) := by
  apply scaled_image_even (alphaInt x y) (betaInt x y) (normalized_linear_odd x y).1 _ hz hc
  simpa only [← (scaled_coefficients x y).1, ← (scaled_coefficients x y).2.1] using hq

theorem dual_image_even (x y : ℤ)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (-2 * Rank6.a (M6 x) (N6 y)) (Rank6.c (M6 x) (N6 y)))
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) :
    Even (padicValRat 2 z) := by
  apply scaled_image_even (-2 * alphaInt x y) (gammaInt x y) (normalized_linear_odd x y).2 _ hz hc
  have ha : 16 * ((-2 * alphaInt x y : ℤ) : ℚ) = -2 * Rank6.a (M6 x) (N6 y) := by
    rw [(scaled_coefficients x y).1]
    push_cast
    ring
  simpa only [ha, ← (scaled_coefficients x y).2.2] using hq

theorem original_image_valuation_row (x y : ℤ)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (Rank6.a (M6 x) (N6 y)) (Rank6.b (M6 x) (N6 y))) :
    valuationParityLinear 2 (Additive.ofMul q) = 0 := by
  apply primeParity_zero_of_evenValuationClass (Fact.out : Nat.Prime 2) q
  exact fun z hz hc => original_image_even x y hq hz hc

theorem dual_image_valuation_row (x y : ℤ)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (-2 * Rank6.a (M6 x) (N6 y)) (Rank6.c (M6 x) (N6 y))) :
    valuationParityLinear 2 (Additive.ofMul q) = 0 := by
  apply primeParity_zero_of_evenValuationClass (Fact.out : Nat.Prime 2) q
  exact fun z hz hc => dual_image_even x y hq hz hc

theorem unit_point_mod_sixteen (u : (ZMod 16)ˣ) (v : ZMod 16)
    (h : v ^ 2 = (u : ZMod 16) ^ 3 + 6 * (u : ZMod 16) ^ 2 + 13 * (u : ZMod 16)) :
    (ZMod.cast (u : ZMod 16) : ZMod 4) = 1 := by
  revert u v
  decide +kernel

theorem unitResiduePow_of_valuation_zero (k : ℕ) {q : ℚ} (hv : padicValRat 2 q = 0) :
    unitResiduePow 2 k q = residuePow 2 k q (by omega) := by
  simp only [unitResiduePow, normalizedUnit, hv, zpow_zero, div_one]

/-- The normalized partner equation with coefficients 6 and 13 modulo 16
has dyadic unit 1 modulo 4 at every nonzero rational coordinate. -/
theorem partner_coordinate_unit_four (a b : ℤ)
    (ha : (a : ZMod 16) = 6) (hb : (b : ZMod 16) = 13)
    {x y : ℚ} (hx : x ≠ 0) (h : OnCurve (a : ℚ) (b : ℚ) x y) :
    unitResiduePow 2 2 x = 1 := by
  have hbmod := (ZMod.intCast_eq_intCast_iff' b 13 16).mp hb
  norm_num at hbmod
  have hbnot : ¬ (2 : ℤ) ∣ b := by
    intro hd
    have hz := Int.emod_eq_zero_of_dvd hd
    omega
  have hb0 : (b : ℚ) ≠ 0 := by
    exact_mod_cast (show b ≠ 0 from fun hz => hbnot (hz ▸ dvd_zero _))
  have hbval : padicValRat 2 (b : ℚ) = 0 := by
    rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hbnot]
    rfl
  have ha8 : (a : ZMod 8) = 6 := by
    have he := congrArg (ZMod.castHom (by decide : 8 ∣ 16) (ZMod 8)) ha
    simpa only [map_intCast, map_ofNat] using he
  have ha_nonneg : 0 ≤ padicValRat 2 (a : ℚ) := by rw [padicValRat.of_int]; positivity
  have hav : padicValRat 2 (a : ℚ) = 1 := by
    apply valuation_two_eq_one_of_residue_six ha_nonneg
    rw [residuePow_int]
    exact ha8
  have hb4 : (b : ZMod 4) = 1 := by
    have he := congrArg (ZMod.castHom (by decide : 4 ∣ 16) (ZMod 4)) hb
    have he' : (b : ZMod 4) = 13 := by
      simpa only [map_intCast, map_ofNat] using he
    simpa only [show (13 : ZMod 4) = 1 by decide] using he'
  have hbunit : unitResiduePow 2 2 (b : ℚ) = 1 := by
    rw [unitResiduePow_of_valuation_zero 2 hbval, residuePow_int]
    exact hb4
  have heven := LocalDescent.integral_x_valuation_even (p := 2) a b hbnot hx h
  rcases lt_trichotomy (padicValRat 2 x) 0 with hneg | hv | hpos
  · have hr : padicValRat 2 x ≤ -2 := by obtain ⟨k, hk⟩ := heven; omega
    have hunit := DyadicDominance.cubic_unitResiduePow_one hx
      (Or.inr (by omega)) (Or.inr (by omega)) h
    rw [← unitResiduePow_cast 2 2 3 (by omega) x, hunit]
    decide
  · obtain ⟨hy, hres⟩ := onCurve_residuePow 2 4 a b (by omega) h
    rw [ha, hb] at hres
    obtain ⟨u, hu⟩ := residuePow_isUnit 2 4 hx hv
    have hu' : (u : ZMod 16) = residuePow 2 4 x (by omega) := hu
    rw [← hu'] at hres
    have hcast := unit_point_mod_sixteen u (residuePow 2 4 y hy) hres
    rw [hu'] at hcast
    rw [unitResiduePow_of_valuation_zero 2 hv,
      ← residuePow_cast 2 2 4 (by omega) (by omega)]
    exact hcast
  · have hr : 2 ≤ padicValRat 2 x := by obtain ⟨k, hk⟩ := heven; omega
    have hunit := DyadicDominance.linear_unitResiduePow_one hb0 hx
      (by omega) (Or.inr (by omega)) h
    have hunit4 : unitResiduePow 2 2 ((b : ℚ) * x) = 1 := by
      rw [← unitResiduePow_cast 2 2 3 (by omega) ((b : ℚ) * x), hunit]
      decide
    rw [unitResiduePow_mul 2 2 hb0 hx, hbunit, one_mul] at hunit4
    exact hunit4

theorem normalized_dual_mod_sixteen (x y : ℤ) :
    ((-2 * alphaInt x y : ℤ) : ZMod 16) = 6 ∧ (gammaInt x y : ZMod 16) = 13 := by
  obtain ⟨ha, hb, _⟩ := normalized_residues x y
  have ha8 := (ZMod.intCast_eq_intCast_iff' (alphaInt x y) 5 8).mp ha
  have hb8 := (ZMod.intCast_eq_intCast_iff' (betaInt x y) 3 8).mp hb
  norm_num at ha8 hb8
  have hAdiv := Int.emod_add_mul_ediv (alphaInt x y) 8
  have hBdiv := Int.emod_add_mul_ediv (betaInt x y) 8
  have hA : alphaInt x y = 5 + 8 * (alphaInt x y / 8) := by omega
  have hB : betaInt x y = 3 + 8 * (betaInt x y / 8) := by omega
  have hcoef : -2 * alphaInt x y = 6 + 16 * (-1 - alphaInt x y / 8) := by omega
  have hgamma : gammaInt x y = 13 + 16 *
      (5 * (alphaInt x y / 8) + 4 * (alphaInt x y / 8) ^ 2 - 2 * (betaInt x y / 8)) := by
    dsimp only [gammaInt]
    conv_lhs => rw [hA, hB]
    ring
  have hzero : (16 : ZMod 16) = 0 := by decide
  rw [hcoef, hgamma]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, hzero, zero_mul, add_zero, and_self]

theorem same_squareclass_unit_four {x z : ℚ} (hx : x ≠ 0) (hz : z ≠ 0)
    (hc : rationalSquareClass x = rationalSquareClass z) :
    unitResiduePow 2 2 x = unitResiduePow 2 2 z := by
  have h8 := unitResiduePow_two_same_squareclass hx hz hc
  have h4 := congrArg (fun t : ZMod (2 ^ 3) => (ZMod.cast t : ZMod (2 ^ 2))) h8
  simpa only [unitResiduePow_cast 2 2 3 (by omega)] using h4

/-- Square scaling preserves the complete necessary partner restriction,
including exceptional images, for every rational squareclass representative. -/
theorem scaled_partner_image_unit_four (a b : ℤ)
    (ha : (a : ZMod 16) = 6) (hb : (b : ZMod 16) = 13)
    {q : RationalSquareClasses} (hq : q ∈ twoIsogenyImage (16 * (a : ℚ)) (256 * (b : ℚ)))
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) :
    unitResiduePow 2 2 z = 1 := by
  have hbmod := (ZMod.intCast_eq_intCast_iff' b 13 16).mp hb
  norm_num at hbmod
  have hbnot : ¬ (2 : ℤ) ∣ b := by
    intro hd
    have hz := Int.emod_eq_zero_of_dvd hd
    omega
  have hb0 : (b : ℚ) ≠ 0 := by
    exact_mod_cast (show b ≠ 0 from fun hz => hbnot (hz ▸ dvd_zero _))
  obtain ⟨P, rfl⟩ := hq
  cases P with
  | zero =>
    rw [same_squareclass_unit_four hz one_ne_zero (hc.trans rationalSquareClass_one.symm)]
    exact unitResiduePow_one 2 2
  | some x y hP =>
    by_cases hx : x = 0
    · simp only [twoIsogenyClass, hx, ite_true] at hc
      have hclass : rationalSquareClass (256 * (b : ℚ)) = rationalSquareClass (b : ℚ) := by
        rw [show 256 * (b : ℚ) = (b : ℚ) * (16 : ℚ) ^ 2 by ring,
          rationalSquareClass_mul_square hb0 (by norm_num)]
      rw [same_squareclass_unit_four hz hb0 (hc.trans hclass)]
      have hbval : padicValRat 2 (b : ℚ) = 0 := by
        rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hbnot]
        rfl
      rw [unitResiduePow_of_valuation_zero 2 hbval, residuePow_int]
      have he := congrArg (ZMod.castHom (by decide : 4 ∣ 16) (ZMod 4)) hb
      have he' : (b : ZMod 4) = 13 := by simpa only [map_intCast, map_ofNat] using he
      simpa only [show (13 : ZMod 4) = 1 by decide] using he'
    · simp only [twoIsogenyClass, hx, ite_false] at hc
      have hx' : x / 16 ≠ 0 := div_ne_zero hx (by norm_num)
      rw [same_squareclass_unit_four hz hx' (hc.trans (scaled_coordinate_class hx).symm)]
      exact partner_coordinate_unit_four a b ha hb hx'
        (scaled_point ((onCurve_iff_equation _ _ _ _).mpr hP.1))

/-- The actual rank-six dual image has normalized unit 1 modulo 4 on
every point of the complete congruence lattice. -/
theorem dual_image_unit_four (x y : ℤ)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (-2 * Rank6.a (M6 x) (N6 y)) (Rank6.c (M6 x) (N6 y)))
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) :
    unitResiduePow 2 2 z = 1 := by
  obtain ⟨ha, hb⟩ := normalized_dual_mod_sixteen x y
  apply scaled_partner_image_unit_four (-2 * alphaInt x y) (gammaInt x y) ha hb _ hz hc
  have ha' : 16 * ((-2 * alphaInt x y : ℤ) : ℚ) = -2 * Rank6.a (M6 x) (N6 y) := by
    rw [(scaled_coefficients x y).1]
    push_cast
    ring
  simpa only [ha', ← (scaled_coefficients x y).2.2] using hq

/-- The actual dyadic character row vanishes on the rank-six dual image. -/
theorem dual_image_character_four_row (x y : ℤ)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (-2 * Rank6.a (M6 x) (N6 y)) (Rank6.c (M6 x) (N6 y))) :
    PrimePowerCharacters.dyadicCharacter4Linear (Additive.ofMul q) = 0 := by
  apply PrimePowerCharacters.powerCharacterLinear_actualImage 2 2 ZMod.χ₄ ZMod.isQuadratic_χ₄ hq
  intro z hz hc
  change ZMod.χ₄ (unitResiduePow 2 2 z) = 1
  rw [dual_image_unit_four x y hq hz hc, map_one]

end RankCertificates.Rank6TwoDescent
