module

public import RankCertificates.PrimeSpecializations
public import RankCertificates.LocalDescent
public import RankCertificates.LocalValuations

@[expose] public section

/-!
# Actual moving-prime conditions for the final rank-5 family

The hypotheses assert that the twelve literal lattice outputs are distinct
positive primes outside 2, 3 and 5.  The valuations below are derived from
the actual quartics and their coefficients, rather than supplied as local
descent hypotheses.
-/

namespace RankCertificates.Rank5PrimeValuations

open Integration

variable {x y : ℤ} (h : PrimeSpecialization5 x y)

theorem prime_nonzero (i : Fin 12) : (h.primes i : ℚ) ≠ 0 := by
  exact_mod_cast (h.prime i).ne_zero

theorem prime_valuation (i j : Fin 12) :
    padicValRat (h.primes i) (h.primes j : ℚ) = if i = j then 1 else 0 := by
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    exact padicValRat.self (h.prime i).one_lt
  · rw [ite_eq_right hij, padicValRat.of_nat]
    have hnd : ¬ h.primes i ∣ h.primes j := by
      have hpi : (h.primes i).Prime := h.prime i
      have hpj : (h.primes j).Prime := h.prime j
      rw [Nat.prime_dvd_prime_iff_eq hpi hpj]
      exact fun heq => hij (h.distinct heq)
    rw [padicValNat.eq_zero_of_not_dvd hnd]
    rfl

theorem small_prime_valuation (i : Fin 12) (q : ℕ) (hq : q.Prime)
    (hs : q ∈ [2, 3, 5]) : padicValRat (h.primes i) (q : ℚ) = 0 := by
  rw [padicValRat.of_nat]
  have hnd : ¬ h.primes i ∣ q := by
    have hpi : (h.primes i).Prime := h.prime i
    rw [Nat.prime_dvd_prime_iff_eq hpi hq]
    exact h.outside i q hs
  rw [padicValNat.eq_zero_of_not_dvd hnd]
  rfl

theorem forms_eq (i : Fin 12) :
    forms5 (M5 x) (N5 y) i = (PrimePatterns.Rank5.cofactors i : ℚ) * (h.primes i : ℚ) := by
  rw [normalization5]
  dsimp [outputs5]
  rw [h.cast_eq i]

theorem F_factorization : Rank5.F (M5 x) (N5 y) =
    432 * ((h.primes 0 : ℚ) * h.primes 1 * h.primes 2 * h.primes 3) := by
  have h0 := forms_eq h 0
  have h1 := forms_eq h 1
  have h2 := forms_eq h 2
  have h3 := forms_eq h 3
  norm_num [forms5, PrimePatterns.Rank5.cofactors] at h0 h1 h2 h3
  unfold Rank5.F
  rw [h0, h1, h2, h3]
  ring

theorem H_factorization : Rank5.H (M5 x) (N5 y) =
    16 * ((h.primes 4 : ℚ) * h.primes 5 * h.primes 6 * h.primes 7) := by
  have h4 := forms_eq h 4
  have h5 := forms_eq h 5
  have h6 := forms_eq h 6
  have h7 := forms_eq h 7
  norm_num [forms5, PrimePatterns.Rank5.cofactors] at h4 h5 h6 h7
  unfold Rank5.H
  rw [h4, h5, h6, h7]
  ring

theorem J_factorization : Rank5.J (M5 x) (N5 y) =
    24 * ((h.primes 8 : ℚ) * h.primes 9 * h.primes 10 * h.primes 11) := by
  have h8 := forms_eq h 8
  have h9 := forms_eq h 9
  have h10 := forms_eq h 10
  have h11 := forms_eq h 11
  norm_num [forms5, PrimePatterns.Rank5.cofactors] at h8 h9 h10 h11
  unfold Rank5.J
  rw [h8, h9, h10, h11]
  ring

theorem prime_product_valuation (i j k l m : Fin 12) :
    padicValRat (h.primes i) ((h.primes j : ℚ) * h.primes k * h.primes l * h.primes m) =
      (if i = j then 1 else 0) + (if i = k then 1 else 0) +
        (if i = l then 1 else 0) + (if i = m then 1 else 0) := by
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  rw [padicValRat.mul (mul_ne_zero (mul_ne_zero (prime_nonzero h j) (prime_nonzero h k))
    (prime_nonzero h l)) (prime_nonzero h m),
    padicValRat.mul (mul_ne_zero (prime_nonzero h j) (prime_nonzero h k)) (prime_nonzero h l),
    padicValRat.mul (prime_nonzero h j) (prime_nonzero h k)]
  rw [prime_valuation h, prime_valuation h, prime_valuation h, prime_valuation h]

theorem constant_valuations (i : Fin 12) :
    padicValRat (h.primes i) (432 : ℚ) = 0 ∧
    padicValRat (h.primes i) (16 : ℚ) = 0 ∧
    padicValRat (h.primes i) (24 : ℚ) = 0 ∧
    padicValRat (h.primes i) (1500 : ℚ) = 0 ∧
    padicValRat (h.primes i) (2700 : ℚ) = 0 ∧
    padicValRat (h.primes i) (57600 : ℚ) = 0 := by
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  have h2 : padicValRat (h.primes i) (2 : ℚ) = 0 := by
    simpa using small_prime_valuation h i 2 Nat.prime_two (by simp)
  have h3 : padicValRat (h.primes i) (3 : ℚ) = 0 := by
    simpa using small_prime_valuation h i 3 (by norm_num) (by simp)
  have h5 : padicValRat (h.primes i) (5 : ℚ) = 0 := by
    simpa using small_prime_valuation h i 5 (by norm_num) (by simp)
  have hv2 (n : ℕ) : padicValRat (h.primes i) ((2 : ℚ) ^ n) = 0 := by simp [padicValRat.pow, h2]
  have hv3 (n : ℕ) : padicValRat (h.primes i) ((3 : ℚ) ^ n) = 0 := by simp [padicValRat.pow, h3]
  have hv5 (n : ℕ) : padicValRat (h.primes i) ((5 : ℚ) ^ n) = 0 := by simp [padicValRat.pow, h5]
  have hv23 (n m : ℕ) : padicValRat (h.primes i) ((2 : ℚ) ^ n * 3 ^ m) = 0 := by
    rw [padicValRat.mul (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num)), hv2, hv3]
    norm_num
  have hv235 (n m l : ℕ) : padicValRat (h.primes i) ((2 : ℚ) ^ n * 3 ^ m * 5 ^ l) = 0 := by
    rw [padicValRat.mul (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num)))
      (pow_ne_zero _ (by norm_num)), hv23, hv5]
    norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert hv23 4 3 using 1; norm_num
  · convert hv2 4 using 1; norm_num
  · convert hv23 3 1 using 1; norm_num
  · convert hv235 2 1 3 using 1; norm_num
  · convert hv235 2 3 2 using 1; norm_num
  · convert hv235 8 2 2 using 1; norm_num

theorem F_valuation (i : Fin 12) :
    padicValRat (h.primes i) (Rank5.F (M5 x) (N5 y)) =
      (if i = 0 then 1 else 0) + (if i = 1 then 1 else 0) +
        (if i = 2 then 1 else 0) + (if i = 3 then 1 else 0) := by
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  rw [F_factorization h, padicValRat.mul (by norm_num)
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (prime_nonzero h 0) (prime_nonzero h 1))
      (prime_nonzero h 2)) (prime_nonzero h 3)), (constant_valuations h i).1,
    prime_product_valuation h]
  simp

theorem H_valuation (i : Fin 12) :
    padicValRat (h.primes i) (Rank5.H (M5 x) (N5 y)) =
      (if i = 4 then 1 else 0) + (if i = 5 then 1 else 0) +
        (if i = 6 then 1 else 0) + (if i = 7 then 1 else 0) := by
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  rw [H_factorization h, padicValRat.mul (by norm_num)
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (prime_nonzero h 4) (prime_nonzero h 5))
      (prime_nonzero h 6)) (prime_nonzero h 7)), (constant_valuations h i).2.1,
    prime_product_valuation h]
  simp

theorem J_valuation (i : Fin 12) :
    padicValRat (h.primes i) (Rank5.J (M5 x) (N5 y)) =
      (if i = 8 then 1 else 0) + (if i = 9 then 1 else 0) +
        (if i = 10 then 1 else 0) + (if i = 11 then 1 else 0) := by
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  rw [J_factorization h, padicValRat.mul (by norm_num)
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (prime_nonzero h 8) (prime_nonzero h 9))
      (prime_nonzero h 10)) (prime_nonzero h 11)), (constant_valuations h i).2.2.1,
    prime_product_valuation h]
  simp

theorem quartic_valuations (i : Fin 12) :
    padicValRat (h.primes i) (Rank5.F (M5 x) (N5 y)) = (if i.val < 4 then 1 else 0) ∧
    padicValRat (h.primes i) (Rank5.H (M5 x) (N5 y)) = (if 4 ≤ i.val ∧ i.val < 8 then 1 else 0) ∧
    padicValRat (h.primes i) (Rank5.J (M5 x) (N5 y)) = (if 8 ≤ i.val then 1 else 0) := by
  rw [F_valuation h, H_valuation h, J_valuation h]
  fin_cases i <;> norm_num

theorem coefficient_valuations (i : Fin 12) :
    padicValRat (h.primes i) (Rank5.a (M5 x) (N5 y)) =
      padicValRat (h.primes i) (Rank5.F (M5 x) (N5 y)) ∧
    padicValRat (h.primes i) (Rank5.b (M5 x) (N5 y)) =
      padicValRat (h.primes i) (Rank5.F (M5 x) (N5 y)) +
        padicValRat (h.primes i) (Rank5.H (M5 x) (N5 y)) ∧
    padicValRat (h.primes i) (Rank5.c (M5 x) (N5 y)) =
      padicValRat (h.primes i) (Rank5.F (M5 x) (N5 y)) +
        padicValRat (h.primes i) (Rank5.J (M5 x) (N5 y)) ∧
    padicValRat (h.primes i) (-2 * Rank5.a (M5 x) (N5 y)) =
      padicValRat (h.primes i) (Rank5.F (M5 x) (N5 y)) := by
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  obtain ⟨hF, hH, hJ⟩ := products5_nonzero_on_lattice x y
  obtain ⟨_, _, _, h1500, h2700, h57600⟩ := constant_valuations h i
  have h2 : padicValRat (h.primes i) (2 : ℚ) = 0 := by
    simpa using small_prime_valuation h i 2 Nat.prime_two (by simp)
  have ha0 : Rank5.a (M5 x) (N5 y) ≠ 0 := mul_ne_zero (by norm_num) hF
  have ha : padicValRat (h.primes i) (Rank5.a (M5 x) (N5 y)) =
      padicValRat (h.primes i) (Rank5.F (M5 x) (N5 y)) := by
    unfold Rank5.a
    rw [padicValRat.mul (by norm_num) hF, h1500, zero_add]
  refine ⟨ha, ?_, ?_, ?_⟩
  · unfold Rank5.b
    rw [padicValRat.mul (mul_ne_zero (by norm_num) hF) hH,
      padicValRat.mul (by norm_num) hF]
    have hneg : padicValRat (h.primes i) (-2700 : ℚ) = 0 := by
      rw [padicValRat.neg, h2700]
    rw [hneg, zero_add]
  · unfold Rank5.c
    rw [padicValRat.mul (mul_ne_zero (by norm_num) hF) hJ,
      padicValRat.mul (by norm_num) hF, h57600, zero_add]
  · rw [padicValRat.mul (by norm_num) ha0, padicValRat.neg, h2, zero_add, ha]

theorem typeIII_coefficient_valuations (i : Fin 12) (hi : i.val < 4) :
    padicValRat (h.primes i) (Rank5.a (M5 x) (N5 y)) = 1 ∧
    padicValRat (h.primes i) (Rank5.b (M5 x) (N5 y)) = 1 ∧
    padicValRat (h.primes i) (Rank5.c (M5 x) (N5 y)) = 1 ∧
    padicValRat (h.primes i) (-2 * Rank5.a (M5 x) (N5 y)) = 1 := by
  obtain ⟨hF, hH, hJ⟩ := quartic_valuations h i
  have hh : ¬ (4 ≤ i.val ∧ i.val < 8) := by omega
  have hj : ¬ 8 ≤ i.val := by omega
  simp only [ite_eq_left hi, ite_eq_right hh, ite_eq_right hj] at hF hH hJ
  simpa [hF, hH, hJ] using coefficient_valuations h i

theorem J_prime_coefficient_valuations (i : Fin 12) (hi : 8 ≤ i.val) :
    padicValRat (h.primes i) (Rank5.a (M5 x) (N5 y)) = 0 ∧
    padicValRat (h.primes i) (Rank5.b (M5 x) (N5 y)) = 0 ∧
    padicValRat (h.primes i) (Rank5.c (M5 x) (N5 y)) = 1 := by
  obtain ⟨hF, hH, hJ⟩ := quartic_valuations h i
  have hf : ¬ i.val < 4 := by omega
  have hh : ¬ (4 ≤ i.val ∧ i.val < 8) := by omega
  simp only [ite_eq_right hf, ite_eq_right hh, ite_eq_left hi] at hF hH hJ
  obtain ⟨ha, hb, hc, _⟩ := coefficient_valuations h i
  exact ⟨ha.trans hF, by omega, by omega⟩

theorem H_prime_coefficient_valuations (i : Fin 12) (hi : 4 ≤ i.val) (hi' : i.val < 8) :
    padicValRat (h.primes i) (-2 * Rank5.a (M5 x) (N5 y)) = 0 ∧
    padicValRat (h.primes i) (Rank5.c (M5 x) (N5 y)) = 0 ∧
    padicValRat (h.primes i) (Rank5.b (M5 x) (N5 y)) = 1 := by
  obtain ⟨hF, hH, hJ⟩ := quartic_valuations h i
  have hf : ¬ i.val < 4 := by omega
  have hj : ¬ 8 ≤ i.val := by omega
  simp only [ite_eq_right hf, ite_eq_left (show 4 ≤ i.val ∧ i.val < 8 from ⟨hi, hi'⟩), ite_eq_right hj] at hF hH hJ
  obtain ⟨_, hb, hc, ha'⟩ := coefficient_valuations h i
  exact ⟨ha'.trans hF, by omega, by omega⟩

/-- Actual original-curve image restriction at each of the four F primes. -/
theorem typeIII_E_image_restriction (i : Fin 12) (hi : i.val < 4)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (Rank5.a (M5 x) (N5 y)) (Rank5.b (M5 x) (N5 y))) :
    ∀ z : ℚ, z ≠ 0 → rationalSquareClass z = q →
      LocalDescent.SquareApproximation (h.primes i) z ∨
        LocalDescent.SquareApproximation (h.primes i) (Rank5.b (M5 x) (N5 y) * z) := by
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  obtain ⟨ha, hb, _, _⟩ := typeIII_coefficient_valuations h i hi
  exact LocalDescent.twoIsogenyImage_moving_prime_square_approximation (by omega) hb hq

/-- Actual partner-curve image restriction at each of the four F primes. -/
theorem typeIII_Ep_image_restriction (i : Fin 12) (hi : i.val < 4)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (-2 * Rank5.a (M5 x) (N5 y)) (Rank5.c (M5 x) (N5 y))) :
    ∀ z : ℚ, z ≠ 0 → rationalSquareClass z = q →
      LocalDescent.SquareApproximation (h.primes i) z ∨
        LocalDescent.SquareApproximation (h.primes i) (Rank5.c (M5 x) (N5 y) * z) := by
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  obtain ⟨_, _, hc, ha'⟩ := typeIII_coefficient_valuations h i hi
  exact LocalDescent.twoIsogenyImage_moving_prime_square_approximation (by omega) hc hq

/-- Actual original-curve image restriction at every J prime. -/
theorem J_prime_E_image_restriction (i : Fin 12) (hi : 8 ≤ i.val)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (Rank5.a (M5 x) (N5 y)) (Rank5.b (M5 x) (N5 y))) :
    LocalDescent.SquareApproximationClass (h.primes i) q := by
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  obtain ⟨hF, hH, _⟩ := products5_nonzero_on_lattice x y
  obtain ⟨ha, hb, hc⟩ := J_prime_coefficient_valuations h i hi
  have ha0 : Rank5.a (M5 x) (N5 y) ≠ 0 := mul_ne_zero (by norm_num) hF
  have hb0 := Rank5.b_ne_zero (M5 x) (N5 y) hF hH
  have hd : padicValRat (h.primes i)
      ((Rank5.a (M5 x) (N5 y)) ^ 2 - 4 * Rank5.b (M5 x) (N5 y)) = 1 := by
    rw [Rank5.isogeny_coefficient]
    exact hc
  exact LocalDescent.twoIsogenyImage_discriminant_prime_square_approximation (p := h.primes i)
    (h.outside i 2 (by simp)) ha0 ha hb0 hb hd hq

/-- Actual partner-curve image restriction at every H prime. -/
theorem H_prime_Ep_image_restriction (i : Fin 12) (hi : 4 ≤ i.val) (hi' : i.val < 8)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (-2 * Rank5.a (M5 x) (N5 y)) (Rank5.c (M5 x) (N5 y))) :
    LocalDescent.SquareApproximationClass (h.primes i) q := by
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  obtain ⟨hF, hH, hJ⟩ := products5_nonzero_on_lattice x y
  obtain ⟨ha', hc, hb⟩ := H_prime_coefficient_valuations h i hi hi'
  have ha0 : -2 * Rank5.a (M5 x) (N5 y) ≠ 0 :=
    mul_ne_zero (by norm_num) (mul_ne_zero (by norm_num) hF)
  have hb0 := Rank5.b_ne_zero (M5 x) (N5 y) hF hH
  have hc0 := Rank5.c_ne_zero (M5 x) (N5 y) hF hJ
  have hd : padicValRat (h.primes i)
      ((-2 * Rank5.a (M5 x) (N5 y)) ^ 2 - 4 * Rank5.c (M5 x) (N5 y)) = 1 := by
    rw [Rank5.dual_isogeny_coefficient, padicValRat.mul (by norm_num) hb0,
      (constant_valuations h i).2.1, zero_add, hb]
  exact LocalDescent.twoIsogenyImage_discriminant_prime_square_approximation (p := h.primes i)
    (h.outside i 2 (by simp)) ha0 ha' hc0 hc hd hq

/-- The moving J-prime character row follows from every actual image,
with the normalized character defined using ordinary finite-field squares. -/
theorem J_prime_E_image_character (i : Fin 12) [Fact (h.primes i).Prime] (hi : 8 ≤ i.val)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (Rank5.a (M5 x) (N5 y)) (Rank5.b (M5 x) (N5 y)))
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) :
    LocalValuations.unitCharacter (h.primes i) z = 1 := by
  exact LocalValuations.squareApproximation_unitCharacter_eq_one (h.primes i) hz
    (J_prime_E_image_restriction h i hi hq z hz hc)

/-- The corresponding moving H-prime character row for the partner curve. -/
theorem H_prime_Ep_image_character (i : Fin 12) [Fact (h.primes i).Prime] (hi : 4 ≤ i.val) (hi' : i.val < 8)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (-2 * Rank5.a (M5 x) (N5 y)) (Rank5.c (M5 x) (N5 y)))
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) :
    LocalValuations.unitCharacter (h.primes i) z = 1 := by
  exact LocalValuations.squareApproximation_unitCharacter_eq_one (h.primes i) hz
    (H_prime_Ep_image_restriction h i hi hi' hq z hz hc)

/-- The valuation parity chooses the exact original-curve type-III
character row at each F prime. -/
theorem typeIII_E_image_character (i : Fin 12) [Fact (h.primes i).Prime] (hi : i.val < 4)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (Rank5.a (M5 x) (N5 y)) (Rank5.b (M5 x) (N5 y)))
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) :
    LocalValuations.unitCharacter (h.primes i) z =
      LocalValuations.unitCharacter (h.primes i) (Rank5.b (M5 x) (N5 y)) ^
        (padicValRat (h.primes i) z % 2).toNat := by
  obtain ⟨ha, hb, _, _⟩ := typeIII_coefficient_valuations h i hi
  exact LocalValuations.twoIsogenyImage_moving_prime_unitCharacter_formula
    (h.primes i) (by omega) hb hq hz hc

/-- The exact partner-curve type-III character row at each F prime. -/
theorem typeIII_Ep_image_character (i : Fin 12) [Fact (h.primes i).Prime] (hi : i.val < 4)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (-2 * Rank5.a (M5 x) (N5 y)) (Rank5.c (M5 x) (N5 y)))
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) :
    LocalValuations.unitCharacter (h.primes i) z =
      LocalValuations.unitCharacter (h.primes i) (Rank5.c (M5 x) (N5 y)) ^
        (padicValRat (h.primes i) z % 2).toNat := by
  obtain ⟨_, _, hb, ha⟩ := typeIII_coefficient_valuations h i hi
  exact LocalValuations.twoIsogenyImage_moving_prime_unitCharacter_formula
    (h.primes i) (by omega) hb hq hz hc

/-- Positive prime outputs force the partner image's real-place row:
every nonzero representative of every actual image class is positive. -/
theorem dual_image_positive (h : PrimeSpecialization5 x y) {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (-2 * Rank5.a (M5 x) (N5 y)) (Rank5.c (M5 x) (N5 y)))
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) : 0 < z := by
  have hp (i : Fin 12) : 0 < (h.primes i : ℚ) := by
    exact_mod_cast (h.prime i).pos
  have hF : 0 < Rank5.F (M5 x) (N5 y) := by
    rw [F_factorization h]
    exact mul_pos (by norm_num) (mul_pos (mul_pos (mul_pos (hp 0) (hp 1)) (hp 2)) (hp 3))
  have hJ : 0 < Rank5.J (M5 x) (N5 y) := by
    rw [J_factorization h]
    exact mul_pos (by norm_num) (mul_pos (mul_pos (mul_pos (hp 8) (hp 9)) (hp 10)) (hp 11))
  apply LocalValuations.twoIsogenyImage_positive _ _ hq hz hc
  · simp only [Rank5.a]
    nlinarith
  · simp only [Rank5.c]
    positivity

end RankCertificates.Rank5PrimeValuations
