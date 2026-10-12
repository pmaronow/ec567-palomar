module

public import RankCertificates.PrimeSpecializations
public import RankCertificates.LocalDescent
public import RankCertificates.LocalValuations
public import RankCertificates.LocalCharacterRows

@[expose] public section

/-!
# Actual moving-prime conditions for the final rank-7 family

The hypotheses assert that the twelve literal lattice outputs are distinct
positive primes outside 2, 3, 7 and 13.  The valuations below are derived from
the actual quartics and their coefficients, rather than supplied as local
descent hypotheses.
-/

namespace RankCertificates.Rank7PrimeValuations

open Integration

variable {x y : ℤ} (h : PrimeSpecialization7 x y)

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
    (hs : q ∈ [2, 3, 7, 13]) : padicValRat (h.primes i) (q : ℚ) = 0 := by
  rw [padicValRat.of_nat]
  have hnd : ¬ h.primes i ∣ q := by
    have hpi : (h.primes i).Prime := h.prime i
    rw [Nat.prime_dvd_prime_iff_eq hpi hq]
    exact h.outside i q hs
  rw [padicValNat.eq_zero_of_not_dvd hnd]
  rfl

theorem forms_eq (i : Fin 12) :
    forms7 (M7 x) (N7 y) i = (PrimePatterns.Rank7.cofactors i : ℚ) * (h.primes i : ℚ) := by
  rw [normalization7]
  dsimp [outputs7]
  rw [h.cast_eq i]

theorem F_factorization : Rank7.F (M7 x) (N7 y) =
    10368 * ((h.primes 0 : ℚ) * h.primes 1 * h.primes 2 * h.primes 3) := by
  have h0 := forms_eq h 0
  have h1 := forms_eq h 1
  have h2 := forms_eq h 2
  have h3 := forms_eq h 3
  norm_num [forms7, PrimePatterns.Rank7.cofactors] at h0 h1 h2 h3
  unfold Rank7.F
  rw [h0, h1, h2, h3]
  ring

theorem H_factorization : Rank7.H (M7 x) (N7 y) =
    1296 * ((h.primes 4 : ℚ) * h.primes 5 * h.primes 6 * h.primes 7) := by
  have h4 := forms_eq h 4
  have h5 := forms_eq h 5
  have h6 := forms_eq h 6
  have h7 := forms_eq h 7
  norm_num [forms7, PrimePatterns.Rank7.cofactors] at h4 h5 h6 h7
  unfold Rank7.H
  rw [h4, h5, h6, h7]
  ring

theorem J_factorization : Rank7.J (M7 x) (N7 y) =
    279936 * ((h.primes 8 : ℚ) * h.primes 9 * h.primes 10 * h.primes 11) := by
  have h8 := forms_eq h 8
  have h9 := forms_eq h 9
  have h10 := forms_eq h 10
  have h11 := forms_eq h 11
  norm_num [forms7, PrimePatterns.Rank7.cofactors] at h8 h9 h10 h11
  unfold Rank7.J
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
    padicValRat (h.primes i) (10368 : ℚ) = 0 ∧
    padicValRat (h.primes i) (16 : ℚ) = 0 ∧
    padicValRat (h.primes i) (279936 : ℚ) = 0 ∧
    padicValRat (h.primes i) (1296 : ℚ) = 0 ∧
    padicValRat (h.primes i) (33124 : ℚ) = 0 ∧
    padicValRat (h.primes i) (9 : ℚ) = 0 := by
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  have h2 : padicValRat (h.primes i) (2 : ℚ) = 0 :=
    small_prime_valuation h i 2 Nat.prime_two (by simp)
  have h3 : padicValRat (h.primes i) (3 : ℚ) = 0 :=
    small_prime_valuation h i 3 (by norm_num) (by simp)
  have h7 : padicValRat (h.primes i) (7 : ℚ) = 0 :=
    small_prime_valuation h i 7 (by norm_num) (by simp)
  have h13 : padicValRat (h.primes i) (13 : ℚ) = 0 :=
    small_prime_valuation h i 13 (by norm_num) (by simp)
  have hv (n m k l : ℕ) :
      padicValRat (h.primes i) ((2:ℚ)^n*3^m*7^k*13^l)=0 := by
    rw [padicValRat.mul (by positivity) (by positivity),
      padicValRat.mul (by positivity) (by positivity),
      padicValRat.mul (by positivity) (by positivity)]
    simp [padicValRat.pow,h2,h3,h7,h13]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · convert hv 7 4 0 0 using 1; norm_num
  · convert hv 4 0 0 0 using 1; norm_num
  · convert hv 7 7 0 0 using 1; norm_num
  · convert hv 4 4 0 0 using 1; norm_num
  · convert hv 2 0 2 2 using 1; norm_num
  · convert hv 0 2 0 0 using 1; norm_num

/-- The extra factors of 91205 are not silently excluded from the prime
specialization hypothesis. Their valuation is merely nonnegative. -/
theorem constant_a_valuation_nonnegative (i : Fin 12) :
    0 ≤ padicValRat (h.primes i) (91205:ℚ) := by
  have hnat (p n : ℕ) : 0 ≤ padicValRat p (n:ℚ) := by
    rw [padicValRat.of_nat]
    positivity
  exact hnat (h.primes i) 91205

theorem F_valuation (i : Fin 12) :
    padicValRat (h.primes i) (Rank7.F (M7 x) (N7 y)) =
      (if i = 0 then 1 else 0) + (if i = 1 then 1 else 0) +
        (if i = 2 then 1 else 0) + (if i = 3 then 1 else 0) := by
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  rw [F_factorization h, padicValRat.mul (by norm_num)
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (prime_nonzero h 0) (prime_nonzero h 1))
      (prime_nonzero h 2)) (prime_nonzero h 3)), (constant_valuations h i).1,
    prime_product_valuation h]
  simp

theorem H_valuation (i : Fin 12) :
    padicValRat (h.primes i) (Rank7.H (M7 x) (N7 y)) =
      (if i = 4 then 1 else 0) + (if i = 5 then 1 else 0) +
        (if i = 6 then 1 else 0) + (if i = 7 then 1 else 0) := by
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  rw [H_factorization h, padicValRat.mul (by norm_num)
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (prime_nonzero h 4) (prime_nonzero h 5))
      (prime_nonzero h 6)) (prime_nonzero h 7)), (constant_valuations h i).2.2.2.1,
    prime_product_valuation h]
  simp

theorem J_valuation (i : Fin 12) :
    padicValRat (h.primes i) (Rank7.J (M7 x) (N7 y)) =
      (if i = 8 then 1 else 0) + (if i = 9 then 1 else 0) +
        (if i = 10 then 1 else 0) + (if i = 11 then 1 else 0) := by
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  rw [J_factorization h, padicValRat.mul (by norm_num)
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (prime_nonzero h 8) (prime_nonzero h 9))
      (prime_nonzero h 10)) (prime_nonzero h 11)), (constant_valuations h i).2.2.1,
    prime_product_valuation h]
  simp

theorem quartic_valuations (i : Fin 12) :
    padicValRat (h.primes i) (Rank7.F (M7 x) (N7 y)) = (if i.val < 4 then 1 else 0) ∧
    padicValRat (h.primes i) (Rank7.H (M7 x) (N7 y)) = (if 4 ≤ i.val ∧ i.val < 8 then 1 else 0) ∧
    padicValRat (h.primes i) (Rank7.J (M7 x) (N7 y)) = (if 8 ≤ i.val then 1 else 0) := by
  rw [F_valuation h, H_valuation h, J_valuation h]
  fin_cases i <;> norm_num

theorem coefficient_valuations (i : Fin 12) :
    padicValRat (h.primes i) (Rank7.a (M7 x) (N7 y)) =
      padicValRat (h.primes i) (91205:ℚ) +
        padicValRat (h.primes i) (Rank7.F (M7 x) (N7 y)) ∧
    padicValRat (h.primes i) (Rank7.b (M7 x) (N7 y)) =
      padicValRat (h.primes i) (Rank7.F (M7 x) (N7 y)) +
        padicValRat (h.primes i) (Rank7.H (M7 x) (N7 y)) ∧
    padicValRat (h.primes i) (Rank7.c (M7 x) (N7 y)) =
      padicValRat (h.primes i) (Rank7.F (M7 x) (N7 y)) +
        padicValRat (h.primes i) (Rank7.J (M7 x) (N7 y)) ∧
    padicValRat (h.primes i) (-2 * Rank7.a (M7 x) (N7 y)) =
      padicValRat (h.primes i) (Rank7.a (M7 x) (N7 y)) := by
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  obtain ⟨hF,hH,hJ⟩ := products7_nonzero_on_lattice x y
  obtain ⟨_,_,_,_,h33124,h9⟩ := constant_valuations h i
  have h2 : padicValRat (h.primes i) (2:ℚ)=0 :=
    small_prime_valuation h i 2 Nat.prime_two (by simp)
  have ha0 : Rank7.a (M7 x) (N7 y) ≠ 0 := mul_ne_zero (by norm_num) hF
  refine ⟨?_,?_,?_,?_⟩
  · unfold Rank7.a
    exact padicValRat.mul (by norm_num) hF
  · unfold Rank7.b
    rw [padicValRat.mul (mul_ne_zero (by norm_num) hF) hH,
      padicValRat.mul (by norm_num) hF]
    have hn : padicValRat (h.primes i) (-33124:ℚ)=0 := by rw [padicValRat.neg,h33124]
    rw [hn,zero_add]
  · unfold Rank7.c
    rw [padicValRat.mul (mul_ne_zero (by norm_num) hF) hJ,
      padicValRat.mul (by norm_num) hF,h9,zero_add]
  · rw [padicValRat.mul (by norm_num) ha0,padicValRat.neg,h2,zero_add]

theorem dual_discriminant_coefficient (M N : ℚ) :
    (-2*Rank7.a M N)^2-4*Rank7.c M N=16*Rank7.b M N := by
  linear_combination 4*Rank7.discriminant_coefficient M N

/-- A unit quadratic coefficient and a discriminant of valuation one force
an odd-prime unit linear coefficient. -/
theorem linear_coefficient_unit {p : ℕ} [Fact p.Prime] {a b d : ℚ}
    (h2 : padicValRat p (2:ℚ)=0) (hb0 : b ≠ 0)
    (hb : padicValRat p b=0) (hd : padicValRat p d=1)
    (hrel : a^2-4*b=d) : padicValRat p a=0 := by
  have h4 : padicValRat p (4:ℚ)=0 := by
    have hp := padicValRat.pow (p := p) (2:ℚ) (k := 2)
    norm_num only [show (2:ℚ)^2=4 by norm_num] at hp
    rw [h2] at hp
    simpa using hp
  have h4b : padicValRat p (4*b)=0 := by
    rw [padicValRat.mul (by norm_num) hb0,h4,hb,zero_add]
  have hs := (LocalDescent.add_dominant (mul_ne_zero (by norm_num : (4:ℚ) ≠ 0) hb0)
    (Or.inr (show padicValRat p (4*b)<padicValRat p d by rw [h4b,hd]; norm_num))).2
  have heq : 4*b+d=a^2 := by linear_combination -hrel
  rw [heq,padicValRat.pow,h4b] at hs
  omega

theorem typeIII_coefficient_valuations (i : Fin 12) (hi : i.val < 4) :
    1 ≤ padicValRat (h.primes i) (Rank7.a (M7 x) (N7 y)) ∧
    padicValRat (h.primes i) (Rank7.b (M7 x) (N7 y)) = 1 ∧
    padicValRat (h.primes i) (Rank7.c (M7 x) (N7 y)) = 1 ∧
    1 ≤ padicValRat (h.primes i) (-2*Rank7.a (M7 x) (N7 y)) := by
  obtain ⟨hF,hH,hJ⟩ := quartic_valuations h i
  have hh : ¬ (4 ≤ i.val ∧ i.val < 8) := by omega
  have hj : ¬ 8 ≤ i.val := by omega
  simp only [ite_eq_left hi,ite_eq_right hh,ite_eq_right hj] at hF hH hJ
  obtain ⟨ha,hb,hc,ha'⟩ := coefficient_valuations h i
  have hconst := constant_a_valuation_nonnegative h i
  omega

theorem J_prime_coefficient_valuations (i : Fin 12) (hi : 8 ≤ i.val) :
    padicValRat (h.primes i) (Rank7.a (M7 x) (N7 y)) = 0 ∧
    padicValRat (h.primes i) (Rank7.b (M7 x) (N7 y)) = 0 ∧
    padicValRat (h.primes i) (Rank7.c (M7 x) (N7 y)) = 1 := by
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  obtain ⟨hF,hH,hJ⟩ := quartic_valuations h i
  have hf : ¬ i.val < 4 := by omega
  have hh : ¬ (4 ≤ i.val ∧ i.val < 8) := by omega
  simp only [ite_eq_right hf,ite_eq_right hh,ite_eq_left hi] at hF hH hJ
  obtain ⟨_,hb,hc,_⟩ := coefficient_valuations h i
  have hbval : padicValRat (h.primes i) (Rank7.b (M7 x) (N7 y))=0 := by omega
  have hcval : padicValRat (h.primes i) (Rank7.c (M7 x) (N7 y))=1 := by omega
  obtain ⟨hFn,hHn,_⟩ := products7_nonzero_on_lattice x y
  exact ⟨linear_coefficient_unit (small_prime_valuation h i 2 Nat.prime_two (by simp))
    (Rank7.b_ne_zero hFn hHn) hbval hcval (Rank7.discriminant_coefficient _ _),hbval,hcval⟩

theorem H_prime_coefficient_valuations (i : Fin 12) (hi : 4 ≤ i.val) (hi' : i.val < 8) :
    padicValRat (h.primes i) (-2*Rank7.a (M7 x) (N7 y)) = 0 ∧
    padicValRat (h.primes i) (Rank7.c (M7 x) (N7 y)) = 0 ∧
    padicValRat (h.primes i) (Rank7.b (M7 x) (N7 y)) = 1 := by
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  obtain ⟨hF,hH,hJ⟩ := quartic_valuations h i
  have hf : ¬ i.val < 4 := by omega
  have hj : ¬ 8 ≤ i.val := by omega
  simp only [ite_eq_right hf,ite_eq_left (show 4 ≤ i.val ∧ i.val < 8 from ⟨hi,hi'⟩),ite_eq_right hj] at hF hH hJ
  obtain ⟨_,hb,hc,_⟩ := coefficient_valuations h i
  have hbval : padicValRat (h.primes i) (Rank7.b (M7 x) (N7 y))=1 := by omega
  have hcval : padicValRat (h.primes i) (Rank7.c (M7 x) (N7 y))=0 := by omega
  obtain ⟨hFn,hHn,hJn⟩ := products7_nonzero_on_lattice x y
  have hb0 := Rank7.b_ne_zero hFn hHn
  have hd : padicValRat (h.primes i) (16*Rank7.b (M7 x) (N7 y))=1 := by
    rw [padicValRat.mul (by norm_num) hb0,(constant_valuations h i).2.1,hbval,zero_add]
  exact ⟨linear_coefficient_unit (small_prime_valuation h i 2 Nat.prime_two (by simp))
    (Rank7.c_ne_zero hFn hJn) hcval hd (dual_discriminant_coefficient _ _),hcval,hbval⟩

/-- Actual original-curve image restriction at each of the four F primes. -/
theorem typeIII_E_image_restriction (i : Fin 12) (hi : i.val < 4)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (Rank7.a (M7 x) (N7 y)) (Rank7.b (M7 x) (N7 y))) :
    ∀ z : ℚ, z ≠ 0 → rationalSquareClass z = q →
      LocalDescent.SquareApproximation (h.primes i) z ∨
        LocalDescent.SquareApproximation (h.primes i) (Rank7.b (M7 x) (N7 y) * z) := by
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  obtain ⟨ha, hb, _, _⟩ := typeIII_coefficient_valuations h i hi
  exact LocalDescent.twoIsogenyImage_moving_prime_square_approximation (by omega) hb hq

/-- Actual partner-curve image restriction at each of the four F primes. -/
theorem typeIII_Ep_image_restriction (i : Fin 12) (hi : i.val < 4)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (-2 * Rank7.a (M7 x) (N7 y)) (Rank7.c (M7 x) (N7 y))) :
    ∀ z : ℚ, z ≠ 0 → rationalSquareClass z = q →
      LocalDescent.SquareApproximation (h.primes i) z ∨
        LocalDescent.SquareApproximation (h.primes i) (Rank7.c (M7 x) (N7 y) * z) := by
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  obtain ⟨_, _, hc, ha'⟩ := typeIII_coefficient_valuations h i hi
  exact LocalDescent.twoIsogenyImage_moving_prime_square_approximation (by omega) hc hq

/-- Actual original-curve image restriction at every J prime. -/
theorem J_prime_E_image_restriction (i : Fin 12) (hi : 8 ≤ i.val)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (Rank7.a (M7 x) (N7 y)) (Rank7.b (M7 x) (N7 y))) :
    LocalDescent.SquareApproximationClass (h.primes i) q := by
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  obtain ⟨hF, hH, _⟩ := products7_nonzero_on_lattice x y
  obtain ⟨ha, hb, hc⟩ := J_prime_coefficient_valuations h i hi
  have ha0 : Rank7.a (M7 x) (N7 y) ≠ 0 := mul_ne_zero (by norm_num) hF
  have hb0 := Rank7.b_ne_zero hF hH
  have hd : padicValRat (h.primes i)
      ((Rank7.a (M7 x) (N7 y)) ^ 2 - 4 * Rank7.b (M7 x) (N7 y)) = 1 := by
    rw [Rank7.discriminant_coefficient]
    exact hc
  exact LocalDescent.twoIsogenyImage_discriminant_prime_square_approximation (p := h.primes i)
    (h.outside i 2 (by simp)) ha0 ha hb0 hb hd hq

/-- Actual partner-curve image restriction at every H prime. -/
theorem H_prime_Ep_image_restriction (i : Fin 12) (hi : 4 ≤ i.val) (hi' : i.val < 8)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (-2 * Rank7.a (M7 x) (N7 y)) (Rank7.c (M7 x) (N7 y))) :
    LocalDescent.SquareApproximationClass (h.primes i) q := by
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  obtain ⟨hF, hH, hJ⟩ := products7_nonzero_on_lattice x y
  obtain ⟨ha', hc, hb⟩ := H_prime_coefficient_valuations h i hi hi'
  have ha0 : -2 * Rank7.a (M7 x) (N7 y) ≠ 0 :=
    mul_ne_zero (by norm_num) (mul_ne_zero (by norm_num) hF)
  have hb0 := Rank7.b_ne_zero hF hH
  have hc0 := Rank7.c_ne_zero hF hJ
  have hd : padicValRat (h.primes i)
      ((-2 * Rank7.a (M7 x) (N7 y)) ^ 2 - 4 * Rank7.c (M7 x) (N7 y)) = 1 := by
    rw [dual_discriminant_coefficient, padicValRat.mul (by norm_num) hb0,
      (constant_valuations h i).2.1, zero_add, hb]
  exact LocalDescent.twoIsogenyImage_discriminant_prime_square_approximation (p := h.primes i)
    (h.outside i 2 (by simp)) ha0 ha' hc0 hc hd hq

/-- The moving J-prime character row follows from every actual image,
with the normalized character defined using ordinary finite-field squares. -/
theorem J_prime_E_image_character (i : Fin 12) [Fact (h.primes i).Prime] (hi : 8 ≤ i.val)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (Rank7.a (M7 x) (N7 y)) (Rank7.b (M7 x) (N7 y)))
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) :
    LocalValuations.unitCharacter (h.primes i) z = 1 := by
  exact LocalValuations.squareApproximation_unitCharacter_eq_one (h.primes i) hz
    (J_prime_E_image_restriction h i hi hq z hz hc)

/-- The corresponding moving H-prime character row for the partner curve. -/
theorem H_prime_Ep_image_character (i : Fin 12) [Fact (h.primes i).Prime] (hi : 4 ≤ i.val) (hi' : i.val < 8)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (-2 * Rank7.a (M7 x) (N7 y)) (Rank7.c (M7 x) (N7 y)))
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) :
    LocalValuations.unitCharacter (h.primes i) z = 1 := by
  exact LocalValuations.squareApproximation_unitCharacter_eq_one (h.primes i) hz
    (H_prime_Ep_image_restriction h i hi hi' hq z hz hc)

/-- The valuation parity chooses the exact original-curve type-III
character row at each F prime. -/
theorem typeIII_E_image_character (i : Fin 12) [Fact (h.primes i).Prime] (hi : i.val < 4)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (Rank7.a (M7 x) (N7 y)) (Rank7.b (M7 x) (N7 y)))
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) :
    LocalValuations.unitCharacter (h.primes i) z =
      LocalValuations.unitCharacter (h.primes i) (Rank7.b (M7 x) (N7 y)) ^
        (padicValRat (h.primes i) z % 2).toNat := by
  obtain ⟨ha, hb, _, _⟩ := typeIII_coefficient_valuations h i hi
  exact LocalValuations.twoIsogenyImage_moving_prime_unitCharacter_formula
    (h.primes i) (by omega) hb hq hz hc

/-- The exact partner-curve type-III character row at each F prime. -/
theorem typeIII_Ep_image_character (i : Fin 12) [Fact (h.primes i).Prime] (hi : i.val < 4)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (-2 * Rank7.a (M7 x) (N7 y)) (Rank7.c (M7 x) (N7 y)))
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) :
    LocalValuations.unitCharacter (h.primes i) z =
      LocalValuations.unitCharacter (h.primes i) (Rank7.c (M7 x) (N7 y)) ^
        (padicValRat (h.primes i) z % 2).toNat := by
  obtain ⟨_, _, hb, ha⟩ := typeIII_coefficient_valuations h i hi
  exact LocalValuations.twoIsogenyImage_moving_prime_unitCharacter_formula
    (h.primes i) (by omega) hb hq hz hc

/-- Actual F-prime original image classes satisfy the genuine combined
character and valuation functional used in the binary descent rows. -/
theorem typeIII_E_image_row (i : Fin 12) [Fact (h.primes i).Prime] (hi : i.val < 4)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (Rank7.a (M7 x) (N7 y)) (Rank7.b (M7 x) (N7 y))) :
    typeIIICharacterLinear (h.primes i) (Rank7.b (M7 x) (N7 y)) (Additive.ofMul q)=0 := by
  obtain ⟨ha,hb,_,_⟩ := typeIII_coefficient_valuations h i hi
  exact typeIIICharacterLinear_actualImage (h.primes i) ha hb hq

/-- The corresponding combined F-prime functional for the partner image. -/
theorem typeIII_Ep_image_row (i : Fin 12) [Fact (h.primes i).Prime] (hi : i.val < 4)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (-2*Rank7.a (M7 x) (N7 y)) (Rank7.c (M7 x) (N7 y))) :
    typeIIICharacterLinear (h.primes i) (Rank7.c (M7 x) (N7 y)) (Additive.ofMul q)=0 := by
  obtain ⟨_,_,hb,ha⟩ := typeIII_coefficient_valuations h i hi
  exact typeIIICharacterLinear_actualImage (h.primes i) ha hb hq

/-- The actual J-prime character functional vanishes on the original image. -/
theorem J_prime_E_image_row (i : Fin 12) [Fact (h.primes i).Prime] (hi : 8 ≤ i.val)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (Rank7.a (M7 x) (N7 y)) (Rank7.b (M7 x) (N7 y))) :
    unitCharacterLinear (h.primes i) (Additive.ofMul q)=0 := by
  obtain ⟨hF,hH,_⟩ := products7_nonzero_on_lattice x y
  obtain ⟨ha,hb,hc⟩ := J_prime_coefficient_valuations h i hi
  have hd : padicValRat (h.primes i)
      (Rank7.a (M7 x) (N7 y)^2-4*Rank7.b (M7 x) (N7 y))=1 := by
    rw [Rank7.discriminant_coefficient]
    exact hc
  exact unitCharacterLinear_typeII (h.primes i) (h.outside i 2 (by simp))
    (mul_ne_zero (by norm_num) hF) ha (Rank7.b_ne_zero hF hH) hb hd hq

/-- The actual H-prime character functional vanishes on the partner image. -/
theorem H_prime_Ep_image_row (i : Fin 12) [Fact (h.primes i).Prime]
    (hi : 4 ≤ i.val) (hi' : i.val < 8)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (-2*Rank7.a (M7 x) (N7 y)) (Rank7.c (M7 x) (N7 y))) :
    unitCharacterLinear (h.primes i) (Additive.ofMul q)=0 := by
  obtain ⟨hF,hH,hJ⟩ := products7_nonzero_on_lattice x y
  obtain ⟨ha,hc,hb⟩ := H_prime_coefficient_valuations h i hi hi'
  have hd : padicValRat (h.primes i)
      ((-2*Rank7.a (M7 x) (N7 y))^2-4*Rank7.c (M7 x) (N7 y))=1 := by
    rw [dual_discriminant_coefficient,padicValRat.mul (by norm_num) (Rank7.b_ne_zero hF hH),
      (constant_valuations h i).2.1,zero_add]
    exact hb
  exact unitCharacterLinear_typeII (h.primes i) (h.outside i 2 (by simp))
    (mul_ne_zero (by norm_num) (mul_ne_zero (by norm_num) hF)) ha
    (Rank7.c_ne_zero hF hJ) hc hd hq

end RankCertificates.Rank7PrimeValuations
