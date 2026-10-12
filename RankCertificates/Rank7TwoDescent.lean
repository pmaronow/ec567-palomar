module

public import RankCertificates.Rank6TwoDescent
public import RankCertificates.DyadicNormPoint

/-!
# Genuine dyadic restrictions for the rank-seven family

The original image is generated locally by 1 and -2. The partner image
satisfies the primitive dyadic character associated to norms of s²+2t².
All restrictions are derived from rational point equations.
-/

@[expose] public section

namespace RankCertificates.Rank7TwoDescent

open Integration LocalValuations PrimePowerResidues PrimePowerCharacters PrimePowerPoints

theorem cubic_residuePow (p : ℕ) [Fact p.Prime] (k : ℕ) (c a b : ℤ) {x y : ℚ}
    (hx : 0 ≤ padicValRat p x)
    (h : y ^ 2 = (c : ℚ) * x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x) :
    ∃ hy : 0 ≤ padicValRat p y,
      (residuePow p k y hy) ^ 2 = (c : ZMod (p ^ k)) * (residuePow p k x hx) ^ 3 +
        (a : ZMod (p ^ k)) * (residuePow p k x hx) ^ 2 +
          (b : ZMod (p ^ k)) * residuePow p k x hx := by
  have hyden := cubic_residue_denominator_unit p c a b h
    (denominator_unit_of_nonnegative_valuation p x hx)
  have hy : 0 ≤ padicValRat p y := by
    have hyvd := padicValNat.eq_zero_of_not_dvd
      (fun hd => hyden ((ZMod.natCast_eq_zero_iff _ _).mpr hd))
    rw [padicValRat_def, hyvd]
    simp only [Nat.cast_zero, sub_zero]
    exact Int.natCast_nonneg _
  have hc : 0 ≤ padicValRat p (c : ℚ) := by rw [padicValRat.of_int]; positivity
  have ha : 0 ≤ padicValRat p (a : ℚ) := by rw [padicValRat.of_int]; positivity
  have hb : 0 ≤ padicValRat p (b : ℚ) := by rw [padicValRat.of_int]; positivity
  have hx2 : 0 ≤ padicValRat p (x ^ 2) := by rw [padicValRat.pow]; positivity
  have hx3 : 0 ≤ padicValRat p (x ^ 3) := by rw [padicValRat.pow]; positivity
  have hcx := LocalSeven.valuation_nonnegative_mul p hc hx3
  have hax := LocalSeven.valuation_nonnegative_mul p ha hx2
  have hbx := LocalSeven.valuation_nonnegative_mul p hb hx
  have hsum := LocalSeven.valuation_nonnegative_add p hcx hax
  have hall := LocalSeven.valuation_nonnegative_add p hsum hbx
  refine ⟨hy, ?_⟩
  have heq : residuePow p k (y ^ 2) (by rw [padicValRat.pow]; positivity) =
      residuePow p k ((c : ℚ) * x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x) hall := by
    congr 1
  rw [residuePow_pow_integral p k hy 2,
    residuePow_add p k hsum hbx hall, residuePow_add p k hcx hax hsum,
    residuePow_mul p k hc hx3 hcx, residuePow_mul p k ha hx2 hax, residuePow_mul p k hb hx hbx,
    residuePow_pow_integral p k hx 3, residuePow_pow_integral p k hx 2,
    residuePow_int p k c hc, residuePow_int p k a ha, residuePow_int p k b hb] at heq
  exact heq

theorem odd_int_valuation_zero (z : ℤ) (r : ZMod 8) (hr : IsUnit r)
    (hz : (z : ZMod 8) = r) : padicValRat 2 (z : ℚ) = 0 := by
  have hnot : ¬ (2 : ℤ) ∣ z := by
    intro hd
    have hz2 : (z : ZMod 2) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd
    have hmod := congrArg (ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2)) hz
    simp only [map_intCast, hz2] at hmod
    have hunit := hr.map (ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2))
    rw [← hmod] at hunit
    exact not_isUnit_zero hunit
  rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hnot]
  rfl

theorem double_valuations (A B : ℤ)
    (hA : (A : ZMod 8) = 5) (hB : (B : ZMod 8) = 7) :
    padicValRat 2 ((2 * A : ℤ) : ℚ) = 1 ∧ padicValRat 2 ((2 * B : ℤ) : ℚ) = 1 := by
  have hAv := odd_int_valuation_zero A 5 (by decide) hA
  have hBv := odd_int_valuation_zero B 7 (by decide) hB
  have hA0 : (A : ℚ) ≠ 0 := by
    exact_mod_cast (show A ≠ 0 from fun hz => (by decide : (0 : ZMod 8) ≠ 5) (by simpa [hz] using hA))
  have hB0 : (B : ℚ) ≠ 0 := by
    exact_mod_cast (show B ≠ 0 from fun hz => (by decide : (0 : ZMod 8) ≠ 7) (by simpa [hz] using hB))
  have h2 : padicValRat 2 (2 : ℚ) = 1 := by
    simpa only [Nat.cast_ofNat] using padicValRat.self (p := 2) (by decide : 1 < 2)
  simp only [Int.cast_mul, Int.cast_ofNat]
  rw [padicValRat.mul (by norm_num) hA0, padicValRat.mul (by norm_num) hB0, hAv, hBv, h2]
  norm_num

theorem double_linear_unit (B : ℤ) (hB : (B : ZMod 8) = 7) :
    unitResiduePow 2 3 ((2 * B : ℤ) : ℚ) = 7 := by
  have hBv := odd_int_valuation_zero B 7 (by decide) hB
  have hB0 : (B : ℚ) ≠ 0 := by
    exact_mod_cast (show B ≠ 0 from fun hz => (by decide : (0 : ZMod 8) ≠ 7) (by simpa [hz] using hB))
  have h2 : unitResiduePow 2 3 (2 : ℚ) = 1 := by
    have hv : padicValRat 2 (2 : ℚ) = 1 := by
      simpa only [Nat.cast_ofNat] using padicValRat.self (p := 2) (by decide : 1 < 2)
    simp only [unitResiduePow, normalizedUnit, hv, zpow_one, Nat.cast_ofNat, div_self (by norm_num : (2 : ℚ) ≠ 0)]
    exact residuePow_one 2 3 _
  simp only [Int.cast_mul, Int.cast_ofNat]
  rw [unitResiduePow_mul 2 3 (by norm_num) hB0, h2, one_mul,
    Rank6TwoDescent.unitResiduePow_of_valuation_zero 3 hBv, residuePow_int]
  exact hB

theorem original_unit_point_mod_eight (u : (ZMod 8)ˣ) (v : ZMod 8)
    (h : v ^ 2 = (u : ZMod 8) ^ 3 + 2 * (u : ZMod 8) ^ 2 + 6 * (u : ZMod 8)) :
    (u : ZMod 8) = 1 := by
  revert u v
  decide +kernel

theorem original_val_one_point_mod_eight (u : (ZMod 8)ˣ) (v : ZMod 8)
    (h : v ^ 2 = 2 * (u : ZMod 8) ^ 3 + 2 * (u : ZMod 8) ^ 2 + 7 * (u : ZMod 8)) :
    (u : ZMod 8) = 7 := by
  revert u v
  decide +kernel

theorem seven_product_one {u : ZMod 8} (h : 7 * u = 1) : u = 7 := by
  revert u
  decide

/-- Complete necessary dyadic restriction for the original normalized
model: its unit is 1 at even valuation and 7 at odd valuation. -/
theorem original_coordinate_unit_eight (A B : ℤ)
    (hA : (A : ZMod 8) = 5) (hB : (B : ZMod 8) = 7)
    {x y : ℚ} (hx : x ≠ 0)
    (h : OnCurve ((2 * A : ℤ) : ℚ) ((2 * B : ℤ) : ℚ) x y) :
    (Even (padicValRat 2 x) ∧ unitResiduePow 2 3 x = 1) ∨
      (Odd (padicValRat 2 x) ∧ unitResiduePow 2 3 x = 7) := by
  obtain ⟨ha, hb⟩ := double_valuations A B hA hB
  have hb0 : ((2 * B : ℤ) : ℚ) ≠ 0 := by
    intro hz; rw [hz, padicValRat.zero] at hb; omega
  rcases lt_trichotomy (padicValRat 2 x) 0 with hneg | hv0 | hpos
  · have he := LocalDescent.x_valuation_even_of_negative (p := 2)
      (by omega : 0 ≤ padicValRat 2 ((2 * A : ℤ) : ℚ))
      (by omega : 0 ≤ padicValRat 2 ((2 * B : ℤ) : ℚ)) hx hneg h
    have hr : padicValRat 2 x ≤ -2 := by obtain ⟨k, hk⟩ := he; omega
    exact Or.inl ⟨he, DyadicDominance.cubic_unitResiduePow_one hx
      (Or.inr (by omega)) (Or.inr (by omega)) h⟩
  · have ha8 : ((2 * A : ℤ) : ZMod 8) = 2 := by
      simp only [Int.cast_mul, Int.cast_ofNat, hA]
      decide
    have hb8 : ((2 * B : ℤ) : ZMod 8) = 6 := by
      simp only [Int.cast_mul, Int.cast_ofNat, hB]
      decide
    obtain ⟨hy, hres⟩ := onCurve_residuePow 2 3 (2 * A) (2 * B) (by omega) h
    rw [ha8, hb8] at hres
    obtain ⟨u, hu⟩ := residuePow_isUnit 2 3 hx hv0
    have hu' : (u : ZMod 8) = residuePow 2 3 x (by omega) := hu
    rw [← hu'] at hres
    have hunit := original_unit_point_mod_eight u (residuePow 2 3 y hy) hres
    rw [hu'] at hunit
    exact Or.inl ⟨by rw [hv0]; exact ⟨0, by omega⟩,
      (Rank6TwoDescent.unitResiduePow_of_valuation_zero 3 hv0).trans hunit⟩
  · by_cases hv1 : padicValRat 2 x = 1
    · let u : ℚ := x / 2
      let w : ℚ := y / 2
      have hu0 : u ≠ 0 := div_ne_zero hx (by norm_num)
      have h2 : padicValRat 2 (2 : ℚ) = 1 := by
        simpa only [Nat.cast_ofNat] using padicValRat.self (p := 2) (by decide : 1 < 2)
      have huv : padicValRat 2 u = 0 := by
        dsimp [u]
        rw [padicValRat.div hx (by norm_num), hv1, h2]
        omega
      have hw : w ^ 2 = (2 : ℚ) * u ^ 3 + ((2 * A : ℤ) : ℚ) * u ^ 2 + (B : ℚ) * u := by
        dsimp [w, u]
        simp only [OnCurve, Int.cast_mul, Int.cast_ofNat] at h ⊢
        linear_combination (1 / 4 : ℚ) * h
      obtain ⟨hwv, hres⟩ := cubic_residuePow 2 3 2 (2 * A) B (by omega) hw
      have ha8 : ((2 * A : ℤ) : ZMod 8) = 2 := by
        simp only [Int.cast_mul, Int.cast_ofNat, hA]
        decide
      rw [ha8, hB] at hres
      obtain ⟨v, hv⟩ := residuePow_isUnit 2 3 hu0 huv
      have hv' : (v : ZMod 8) = residuePow 2 3 u (by omega) := hv
      rw [← hv'] at hres
      have hunit := original_val_one_point_mod_eight v (residuePow 2 3 w hwv) hres
      rw [hv'] at hunit
      right
      refine ⟨by rw [hv1]; exact ⟨0, by omega⟩, ?_⟩
      have heq : unitResiduePow 2 3 x = residuePow 2 3 u (by omega) := by
        simp only [unitResiduePow, normalizedUnit, hv1, zpow_one, Nat.cast_ofNat]
        rfl
      exact heq.trans hunit
    · have hr : 2 ≤ padicValRat 2 x := by omega
      have he := LocalDescent.linear_term_valuation_even (p := 2) hb0 hx
        (by omega) (Or.inr (by omega)) h
      rw [hb] at he
      obtain ⟨k, hk⟩ := he
      have ho : Odd (padicValRat 2 x) := ⟨k - 1, by omega⟩
      have hr3 : 3 ≤ padicValRat 2 x := by omega
      have hunit := DyadicDominance.linear_unitResiduePow_one hb0 hx
        (by omega) (Or.inr (by omega)) h
      rw [unitResiduePow_mul 2 3 hb0 hx, double_linear_unit B hB] at hunit
      exact Or.inr ⟨ho, seven_product_one hunit⟩

def outputInt (x y : ℤ) (i : Fin 12) : ℤ := (PrimePatterns.Rank7.outputs i).eval x y
def dividedF (x y : ℤ) : ℤ :=
  81 * (outputInt x y 0 * outputInt x y 1 * outputInt x y 2 * outputInt x y 3)
def dividedH (x y : ℤ) : ℤ :=
  81 * (outputInt x y 4 * outputInt x y 5 * outputInt x y 6 * outputInt x y 7)
def AInt (x y : ℤ) : ℤ := 91205 * dividedF x y
def BInt (x y : ℤ) : ℤ := -91 ^ 2 * dividedF x y * dividedH x y
def alphaInt (x y : ℤ) : ℤ := 2 * AInt x y
def betaInt (x y : ℤ) : ℤ := 2 * BInt x y
def gammaInt (x y : ℤ) : ℤ := alphaInt x y ^ 2 - 4 * betaInt x y

theorem scaled_coefficients (x y : ℤ) :
    Rank7.a (M7 x) (N7 y) = 64 * (alphaInt x y : ℚ) ∧
    Rank7.b (M7 x) (N7 y) = 4096 * (betaInt x y : ℚ) ∧
    Rank7.c (M7 x) (N7 y) = 4096 * (gammaInt x y : ℚ) := by
  obtain ⟨hF, hH, _⟩ := lattice7_factorGroups x y
  have ha : Rank7.a (M7 x) (N7 y) = 64 * (alphaInt x y : ℚ) := by
    simp only [Rank7.a, hF, alphaInt, AInt, dividedF, outputInt, outputs7, Int.cast_mul, Int.cast_ofNat]
    ring
  have hb : Rank7.b (M7 x) (N7 y) = 4096 * (betaInt x y : ℚ) := by
    simp only [Rank7.b, hF, hH, betaInt, BInt, dividedF, dividedH, outputInt, outputs7,
      Int.cast_mul, Int.cast_neg, Int.cast_pow, Int.cast_ofNat]
    ring
  refine ⟨ha, hb, ?_⟩
  rw [← Rank7.discriminant_coefficient, ha, hb]
  simp only [gammaInt, Int.cast_sub, Int.cast_pow, Int.cast_mul, Int.cast_ofNat]
  ring

theorem output_mod_eight (x y : ℤ) (i : Fin 12) :
    (outputInt x y i : ZMod 8) = (PrimePatterns.Rank7.mod8Units i : ZMod 8) := by
  rw [ZMod.intCast_eq_intCast_iff']
  dsimp [outputInt]
  rw [PrimePatterns.Rank7.residue8]
  fin_cases i <;> norm_num [PrimePatterns.Rank7.mod8Units]

theorem normalized_residues (x y : ℤ) :
    (AInt x y : ZMod 8) = 5 ∧ (BInt x y : ZMod 8) = 7 := by
  have h0 := output_mod_eight x y 0
  have h1 := output_mod_eight x y 1
  have h2 := output_mod_eight x y 2
  have h3 := output_mod_eight x y 3
  have h4 := output_mod_eight x y 4
  have h5 := output_mod_eight x y 5
  have h6 := output_mod_eight x y 6
  have h7 := output_mod_eight x y 7
  norm_num [PrimePatterns.Rank7.mod8Units] at h0 h1 h2 h3 h4 h5 h6 h7
  simp only [AInt, BInt, dividedF, dividedH, Int.cast_mul, Int.cast_neg, Int.cast_pow,
    Int.cast_ofNat, h0, h1, h2, h3, h4, h5, h6, h7]
  decide

theorem scaled_point {a b x y : ℚ} (h : OnCurve (64 * a) (4096 * b) x y) :
    OnCurve a b (x / 64) (y / 512) := by
  dsimp [OnCurve] at h ⊢
  linear_combination (1 / 262144 : ℚ) * h

theorem scaled_coordinate_class {x : ℚ} (hx : x ≠ 0) :
    rationalSquareClass (x / 64) = rationalSquareClass x := by
  have hx' : x / 64 ≠ 0 := div_ne_zero hx (by norm_num)
  have heq : x = (x / 64) * (8 : ℚ) ^ 2 := by ring
  have hc := rationalSquareClass_mul_square hx' (by norm_num : (8 : ℚ) ≠ 0)
  rw [← heq] at hc
  exact hc.symm

theorem same_squareclass_local_conditions {x z : ℚ} (hx : x ≠ 0) (hz : z ≠ 0)
    (hc : rationalSquareClass x = rationalSquareClass z)
    (h : (Even (padicValRat 2 z) ∧ unitResiduePow 2 3 z = 1) ∨
      (Odd (padicValRat 2 z) ∧ unitResiduePow 2 3 z = 7)) :
    (Even (padicValRat 2 x) ∧ unitResiduePow 2 3 x = 1) ∨
      (Odd (padicValRat 2 x) ∧ unitResiduePow 2 3 x = 7) := by
  have hunit := unitResiduePow_two_same_squareclass hx hz hc
  rcases h with ⟨he, hu⟩ | ⟨ho, hu⟩
  · exact Or.inl ⟨LocalDescent.same_squareclass_even_valuation hx hz hc he, hunit.trans hu⟩
  · have hp := LocalSeven.same_squareclass_valuation_mod_two 2 hx hz hc
    have hxodd : Odd (padicValRat 2 x) := Int.odd_iff.mpr (hp.trans (Int.odd_iff.mp ho))
    exact Or.inr ⟨hxodd, hunit.trans hu⟩

/-- The complete local condition on every actual original-image class and
every representative, uniformly on the CRT lattice. -/
theorem original_image_unit_eight (x y : ℤ)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (Rank7.a (M7 x) (N7 y)) (Rank7.b (M7 x) (N7 y)))
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) :
    (Even (padicValRat 2 z) ∧ unitResiduePow 2 3 z = 1) ∨
      (Odd (padicValRat 2 z) ∧ unitResiduePow 2 3 z = 7) := by
  obtain ⟨hA, hB⟩ := normalized_residues x y
  have hbval := (double_valuations (AInt x y) (BInt x y) hA hB).2
  have hb0 : (betaInt x y : ℚ) ≠ 0 := by
    intro hzero
    change padicValRat 2 (betaInt x y : ℚ) = 1 at hbval
    rw [hzero, padicValRat.zero] at hbval
    omega
  obtain ⟨P, rfl⟩ := hq
  cases P with
  | zero =>
    apply same_squareclass_local_conditions hz one_ne_zero (hc.trans rationalSquareClass_one.symm)
    exact Or.inl ⟨by simp, unitResiduePow_one 2 3⟩
  | some X Y hP =>
    by_cases hX : X = 0
    · simp only [twoIsogenyClass, hX, ite_true] at hc
      have hclass : rationalSquareClass (Rank7.b (M7 x) (N7 y)) = rationalSquareClass (betaInt x y : ℚ) := by
        rw [(scaled_coefficients x y).2.1,
          show 4096 * (betaInt x y : ℚ) = (betaInt x y : ℚ) * (64 : ℚ) ^ 2 by ring,
          rationalSquareClass_mul_square hb0 (by norm_num)]
      apply same_squareclass_local_conditions hz hb0 (hc.trans hclass)
      right
      refine ⟨?_, double_linear_unit (BInt x y) hB⟩
      change padicValRat 2 (betaInt x y : ℚ) = 1 at hbval
      rw [hbval]
      exact ⟨0, by omega⟩
    · simp only [twoIsogenyClass, hX, ite_false] at hc
      have hX' : X / 64 ≠ 0 := div_ne_zero hX (by norm_num)
      apply same_squareclass_local_conditions hz hX' (hc.trans (scaled_coordinate_class hX).symm)
      apply original_coordinate_unit_eight (AInt x y) (BInt x y) hA hB hX'
      have hp : OnCurve (64 * (alphaInt x y : ℚ)) (4096 * (betaInt x y : ℚ)) X Y := by
        simpa only [← (scaled_coefficients x y).1, ← (scaled_coefficients x y).2.1]
          using ((onCurve_iff_equation _ _ _ _).mpr hP.1)
      simpa only [alphaInt, betaInt, Int.cast_mul, Int.cast_ofNat] using scaled_point hp

theorem original_image_character_eight_row (x y : ℤ)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (Rank7.a (M7 x) (N7 y)) (Rank7.b (M7 x) (N7 y))) :
    dyadicCharacter8Linear (Additive.ofMul q) = 0 := by
  apply powerCharacterLinear_actualImage 2 3 ZMod.χ₈ ZMod.isQuadratic_χ₈ hq
  intro z hz hc
  change ZMod.χ₈ (unitResiduePow 2 3 z) = 1
  rcases original_image_unit_eight x y hq hz hc with ⟨_, hu⟩ | ⟨_, hu⟩ <;>
    rw [hu] <;> decide

theorem original_image_character_four_valuation_row (x y : ℤ)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (Rank7.a (M7 x) (N7 y)) (Rank7.b (M7 x) (N7 y))) :
    (dyadicCharacter4Linear + valuationParityLinear 2) (Additive.ofMul q) = 0 := by
  revert hq
  refine QuotientGroup.induction_on q fun u hq => ?_
  have hl := original_image_unit_eight x y hq u.ne_zero (rationalSquareClass_unit u)
  rw [← rationalSquareClass_unit u]
  change powerCharacterParity 2 2 ZMod.χ₄ ZMod.isQuadratic_χ₄
    (Additive.ofMul (rationalSquareClass (u : ℚ))) +
      primeParity 2 (Fact.out : Nat.Prime 2) (Additive.ofMul (rationalSquareClass (u : ℚ))) = 0
  rw [powerCharacterParity_apply 2 2 ZMod.χ₄ ZMod.isQuadratic_χ₄ u.ne_zero,
    primeParity_apply (Fact.out : Nat.Prime 2) u.ne_zero]
  change quadraticCharacterBit (ZMod.χ₄ (unitResiduePow 2 2 (u : ℚ))) +
    ((padicValRat 2 (u : ℚ) : ℤ) : ZMod 2) = 0
  rw [← unitResiduePow_cast 2 2 3 (by omega) (u : ℚ)]
  rcases hl with ⟨he, hu⟩ | ⟨ho, hu⟩
  · rw [hu, he.intCast_zmod_two]
    decide
  · have hmod := Int.odd_iff.mp ho
    have hcast : ((padicValRat 2 (u : ℚ) : ℤ) : ZMod 2) = 1 := by
      change ((padicValRat 2 (u : ℚ) : ℤ) : ZMod 2) = ((1 : ℤ) : ZMod 2)
      apply (ZMod.intCast_eq_intCast_iff' _ _ 2).mpr
      simpa using hmod
    rw [hu, hcast]
    decide

theorem discriminant_nonzero_of_beta_valuation_one {a b : ℚ}
    (hb : padicValRat 2 b = 1) : a ^ 2 - 4 * b ≠ 0 := by
  have hb0 : b ≠ 0 := by intro hz; rw [hz, padicValRat.zero] at hb; omega
  have htwo : padicValRat 2 (2 : ℚ) = 1 := padicValRat.self (by norm_num)
  have hfour : padicValRat 2 (4 : ℚ) = 2 := by
    rw [show (4 : ℚ) = (2 : ℚ) ^ 2 by norm_num, padicValRat.pow, htwo]
    norm_num
  intro hz
  have heq := sub_eq_zero.mp hz
  have hv := congrArg (padicValRat 2) heq
  rw [padicValRat.pow, padicValRat.mul (by norm_num) hb0, hfour, hb] at hv
  omega

/-- Every representative of an actual partner image is a dyadic norm unit.
The exceptional two-torsion class is treated by the same norm calculation. -/
theorem dual_image_unit_eight (x y : ℤ)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (-2 * Rank7.a (M7 x) (N7 y)) (Rank7.c (M7 x) (N7 y)))
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) :
    unitResiduePow 2 3 z = 1 ∨ unitResiduePow 2 3 z = 3 := by
  obtain ⟨hA, hB⟩ := normalized_residues x y
  have hBv := odd_int_valuation_zero (BInt x y) 7 (by decide) hB
  have hbetav := (double_valuations (AInt x y) (BInt x y) hA hB).2
  have hgamma : (gammaInt x y : ℚ) =
      (alphaInt x y : ℚ) ^ 2 - ((2 * BInt x y : ℤ) : ℚ) * (2 : ℚ) ^ 2 := by
    simp only [gammaInt, betaInt, Int.cast_sub, Int.cast_pow, Int.cast_mul, Int.cast_ofNat]
    ring
  have hgamma0 : (gammaInt x y : ℚ) ≠ 0 := by
    have hh := discriminant_nonzero_of_beta_valuation_one hbetav (a := (alphaInt x y : ℚ))
    simpa only [gammaInt, betaInt, Int.cast_sub, Int.cast_pow, Int.cast_mul, Int.cast_ofNat] using hh
  obtain ⟨P, rfl⟩ := hq
  cases P with
  | zero =>
    rw [unitResiduePow_two_same_squareclass hz one_ne_zero (hc.trans rationalSquareClass_one.symm)]
    exact Or.inl (unitResiduePow_one 2 3)
  | some X Y hP =>
    by_cases hX : X = 0
    · simp only [twoIsogenyClass, hX, ite_true] at hc
      have hclass : rationalSquareClass (Rank7.c (M7 x) (N7 y)) = rationalSquareClass (gammaInt x y : ℚ) := by
        rw [(scaled_coefficients x y).2.2,
          show 4096 * (gammaInt x y : ℚ) = (gammaInt x y : ℚ) * (64 : ℚ) ^ 2 by ring,
          rationalSquareClass_mul_square hgamma0 (by norm_num)]
      rw [unitResiduePow_two_same_squareclass hz hgamma0 (hc.trans hclass)]
      have hn : (alphaInt x y : ℚ) ^ 2 - ((2 * BInt x y : ℤ) : ℚ) * (2 : ℚ) ^ 2 ≠ 0 := by
        rwa [← hgamma]
      simpa only [← hgamma] using DyadicNorm.norm_unit_one_or_three (BInt x y) hB hBv hn
    · simp only [twoIsogenyClass, hX, ite_false] at hc
      have hX' : X / 64 ≠ 0 := div_ne_zero hX (by norm_num)
      rw [unitResiduePow_two_same_squareclass hz hX' (hc.trans (scaled_coordinate_class hX).symm)]
      have hp : OnCurve (64 * (-2 * (alphaInt x y : ℚ))) (4096 * (gammaInt x y : ℚ)) X Y := by
        have hh := ((onCurve_iff_equation _ _ _ _).mpr hP.1)
        have he : -2 * Rank7.a (M7 x) (N7 y) = 64 * (-2 * (alphaInt x y : ℚ)) := by
          rw [(scaled_coefficients x y).1]
          ring
        simpa only [← he, ← (scaled_coefficients x y).2.2] using hh
      have hs := scaled_point hp
      have hs' : OnCurve (-2 * (alphaInt x y : ℚ))
          ((alphaInt x y : ℚ) ^ 2 - 4 * ((2 * BInt x y : ℤ) : ℚ)) (X / 64) (Y / 512) := by
        simpa only [gammaInt, betaInt, Int.cast_sub, Int.cast_pow, Int.cast_mul, Int.cast_ofNat] using hs
      exact DyadicNormPoint.partner_coordinate_unit_eight (alphaInt x y : ℚ) (BInt x y) hB hBv hX' hs'

/-- The partner image satisfies the primitive dyadic norm character row. -/
theorem dual_image_character_sum_row (x y : ℤ)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (-2 * Rank7.a (M7 x) (N7 y)) (Rank7.c (M7 x) (N7 y))) :
    (dyadicCharacter4Linear + dyadicCharacter8Linear) (Additive.ofMul q) = 0 := by
  revert hq
  refine QuotientGroup.induction_on q fun u hq => ?_
  have hl := dual_image_unit_eight x y hq u.ne_zero (rationalSquareClass_unit u)
  rw [← rationalSquareClass_unit u]
  change powerCharacterParity 2 2 ZMod.χ₄ ZMod.isQuadratic_χ₄
    (Additive.ofMul (rationalSquareClass (u : ℚ))) +
      powerCharacterParity 2 3 ZMod.χ₈ ZMod.isQuadratic_χ₈
        (Additive.ofMul (rationalSquareClass (u : ℚ))) = 0
  rw [powerCharacterParity_apply 2 2 ZMod.χ₄ ZMod.isQuadratic_χ₄ u.ne_zero,
    powerCharacterParity_apply 2 3 ZMod.χ₈ ZMod.isQuadratic_χ₈ u.ne_zero]
  change quadraticCharacterBit (ZMod.χ₄ (unitResiduePow 2 2 (u : ℚ))) +
    quadraticCharacterBit (ZMod.χ₈ (unitResiduePow 2 3 (u : ℚ))) = 0
  rw [← unitResiduePow_cast 2 2 3 (by omega) (u : ℚ)]
  rcases hl with hu | hu <;> rw [hu] <;> decide

end RankCertificates.Rank7TwoDescent
