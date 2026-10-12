module

public import RankCertificates.FiniteKatai
public import Mathlib.Data.Nat.Cast.Order.Field

@[expose] public section

open scoped BigOperators
open Finset

namespace RankCertificates.ArithmeticOrthogonality

noncomputable section

theorem divisor_frequency_nonneg (P : Finset ℕ) (n : ℕ) :
    0 ≤ divisorFrequency P n := by
  unfold divisorFrequency
  exact sum_nonneg fun p hp => by split_ifs <;> norm_num

theorem reciprocalMass_nonneg (P : Finset ℕ) : 0 ≤ reciprocalMass P := by
  exact sum_nonneg fun p hp => by positivity

theorem divisor_frequency_first_moment (P : Finset ℕ) (N : ℕ) :
    (∑ n ∈ initialInterval N, divisorFrequency P n) =
      ∑ p ∈ P, ((N / p : ℕ) : ℝ) := by
  classical
  unfold divisorFrequency
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  rw [← sum_filter]
  simp [initialInterval, Nat.Ioc_filter_dvd_card_eq_div]

theorem divisor_frequency_second_moment {P : Finset ℕ} (N : ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    (∑ n ∈ initialInterval N, (divisorFrequency P n) ^ 2) =
      ∑ p ∈ P, ∑ q ∈ P,
        if p = q then ((N / p : ℕ) : ℝ) else ((N / (p * q) : ℕ) : ℝ) := by
  classical
  simp only [divisorFrequency, pow_two, sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  rw [sum_comm]
  apply sum_congr rfl
  intro q hq
  by_cases hpq : p = q
  · subst q
    simp only [ite_true]
    have hpoint : ∀ n,
        (if p ∣ n then (1 : ℝ) else 0) * (if p ∣ n then (1 : ℝ) else 0) =
          if p ∣ n then (1 : ℝ) else 0 := by intro n; split_ifs <;> norm_num
    simp_rw [hpoint]
    rw [← sum_filter]
    simp [initialInterval, Nat.Ioc_filter_dvd_card_eq_div]
  · simp only [hpq, ite_false]
    have hcop : p.Coprime q := (Nat.coprime_primes (hP p hp) (hP q hq)).mpr hpq
    have hpoint : ∀ n,
        (if q ∣ n then (1 : ℝ) else 0) * (if p ∣ n then (1 : ℝ) else 0) =
          if p * q ∣ n then (1 : ℝ) else 0 := by
      intro n
      have hdiv : p * q ∣ n ↔ p ∣ n ∧ q ∣ n :=
        ⟨fun h => ⟨(dvd_mul_right p q).trans h, (dvd_mul_left q p).trans h⟩,
          fun h => hcop.mul_dvd_of_dvd_of_dvd h.1 h.2⟩
      by_cases hp : p ∣ n <;> by_cases hq : q ∣ n <;> simp [hp, hq, hdiv]
    simp_rw [hpoint]
    rw [← sum_filter]
    simp [initialInterval, Nat.Ioc_filter_dvd_card_eq_div]

theorem cast_div_lower {N p : ℕ} (hp : 0 < p) :
    (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := by
  have hmod : (N % p : ℝ) < (p : ℝ) := by exact_mod_cast Nat.mod_lt N hp
  have hsplit : (N : ℝ) = (N % p : ℝ) + (p : ℝ) * ((N / p : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div N p).symm
  rw [sub_le_iff_le_add, div_le_iff₀ (by exact_mod_cast hp)]
  nlinarith

theorem first_moment_lower {P : Finset ℕ} {N : ℕ}
    (hP : ∀ p ∈ P, 0 < p) :
    (N : ℝ) * reciprocalMass P - (P.card : ℝ) ≤
      ∑ n ∈ initialInterval N, divisorFrequency P n := by
  rw [divisor_frequency_first_moment]
  calc
    _ = ∑ p ∈ P, ((N : ℝ) / p - 1) := by
      simp only [reciprocalMass, mul_sum, sum_sub_distrib, sum_const,
        nsmul_eq_mul, mul_one, mul_one_div]
    _ ≤ _ := sum_le_sum fun p hp => cast_div_lower (hP p hp)

theorem diagonal_mass_le (P : Finset ℕ) (N : ℕ) :
    (∑ p ∈ P, ((N / p : ℕ) : ℝ)) ≤ (N : ℝ) * reciprocalMass P := by
  unfold reciprocalMass
  rw [mul_sum]
  exact sum_le_sum fun p hp => by simpa [div_eq_mul_inv] using (Nat.cast_div_le (m := N) (n := p) (α := ℝ))

theorem second_moment_upper {P : Finset ℕ} {N : ℕ}
    (hP : ∀ p ∈ P, p.Prime) :
    (∑ n ∈ initialInterval N, (divisorFrequency P n) ^ 2) ≤
      (N : ℝ) * reciprocalMass P + (N : ℝ) * (reciprocalMass P) ^ 2 := by
  classical
  rw [divisor_frequency_second_moment N hP]
  have hpair : ∀ p ∈ P, ∀ q ∈ P,
      (if p = q then ((N / p : ℕ) : ℝ) else ((N / (p * q) : ℕ) : ℝ)) ≤
        (if p = q then (N : ℝ) / p else 0) + (N : ℝ) / ((p : ℝ) * q) := by
    intro p hp q hq
    split_ifs with hpq
    · exact (Nat.cast_div_le (m := N) (n := p)).trans (le_add_of_nonneg_right (by positivity))
    · simpa only [Nat.cast_mul, zero_add] using (Nat.cast_div_le (m := N) (n := p*q) (α := ℝ))
  calc
    _ ≤ ∑ p ∈ P, ∑ q ∈ P,
        ((if p = q then (N : ℝ) / p else 0) + (N : ℝ) / ((p : ℝ) * q)) :=
      sum_le_sum fun p hp => sum_le_sum fun q hq => hpair p hp q hq
    _ = _ := by
      simp only [sum_add_distrib]
      have hdiag : (∑ p ∈ P, ∑ q ∈ P, if p = q then (N : ℝ) / p else 0) =
          (N : ℝ) * reciprocalMass P := by
        simp [reciprocalMass, mul_sum, div_eq_mul_inv]
      rw [hdiag]
      congr 1
      simp only [reciprocalMass, pow_two, sum_mul, mul_sum, div_eq_mul_inv]
      apply sum_congr rfl
      intro p hp
      apply sum_congr rfl
      intro q hq
      ring

/-- Pairwise prime divisors give the elementary finite Turán variance bound. -/
theorem divisorVariance_le {P : Finset ℕ} {N : ℕ}
    (hP : ∀ p ∈ P, p.Prime) :
    divisorVariance P N ≤ (N : ℝ) * reciprocalMass P +
      2 * reciprocalMass P * (P.card : ℝ) := by
  have hfirst := first_moment_lower (N := N) (fun p hp => (hP p hp).pos)
  have hsecond := second_moment_upper (N := N) hP
  have hL := reciprocalMass_nonneg P
  have hvar : divisorVariance P N =
      (∑ n ∈ initialInterval N, (divisorFrequency P n) ^ 2) -
      2 * reciprocalMass P * (∑ n ∈ initialInterval N, divisorFrequency P n) +
      (N : ℝ) * (reciprocalMass P) ^ 2 := by
    unfold divisorVariance
    simp_rw [sub_sq]
    rw [sum_add_distrib, sum_sub_distrib]
    simp only [sum_const, nsmul_eq_mul, initialInterval, Nat.card_Ioc, Nat.sub_zero]
    congr 2
    rw [mul_sum]
    apply sum_congr rfl
    intro n hn
    ring
  rw [hvar]
  nlinarith

theorem squareDivisorError_le (P : Finset ℕ) (N : ℕ) :
    squareDivisorError P N ≤ 2 * (N : ℝ) * ∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2 := by
  unfold squareDivisorError
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
  rw [mul_sum]
  exact sum_le_sum fun p hp => by
    simpa only [Nat.cast_mul, pow_two, div_eq_mul_inv, one_mul] using
      (Nat.cast_div_le (m := N) (n := p*p) (α := ℝ))

/-- A finite Kátai inequality with every divisor fluctuation bounded explicitly. -/
theorem finite_katai_explicit {a f : ℕ → ℂ} {P : Finset ℕ} {N : ℕ}
    (hP : ∀ p ∈ P, p.Prime) (ha : ∀ n, ‖a n‖ ≤ 1) (hf : ∀ n, ‖f n‖ ≤ 1)
    (hmul : ∀ m n, m.Coprime n → f (m * n) = f m * f n) :
    reciprocalMass P * ‖∑ n ∈ initialInterval N, f n * a n‖ ≤
      Real.sqrt ((N : ℝ) * ((N : ℝ) * reciprocalMass P +
        2 * reciprocalMass P * (P.card : ℝ))) +
      Real.sqrt ((N : ℝ) * ((N : ℝ) * reciprocalMass P + offDiagonalMass a P N)) +
      2 * (N : ℝ) * ∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2 := by
  apply (finite_katai_inequality hP ha hf hmul).trans
  apply add_le_add
  · exact add_le_add
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (divisorVariance_le hP) (by positivity)))
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
        (add_le_add (diagonal_mass_le P N) le_rfl) (by positivity)))
  · exact squareDivisorError_le P N

end

end RankCertificates.ArithmeticOrthogonality
