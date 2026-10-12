module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

@[expose] public section

open scoped BigOperators
open Finset

namespace RankCertificates.ArithmeticOrthogonality

noncomputable section

/-- The positive indices, excluding the exceptional index zero. -/
def initialInterval (N : ℕ) : Finset ℕ := Ioc 0 N

/-- A genuine multiplicative-dilation correlation, truncated at `H`. -/
def dilationCorrelation (a : ℕ → ℂ) (p q H : ℕ) : ℂ :=
  ∑ m ∈ initialInterval H, a (p * m) * star (a (q * m))

/-- The number of prime-window divisors of `n`. -/
def divisorFrequency (P : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ p ∈ P, if p ∣ n then (1 : ℝ) else 0

/-- The expected frequency of a finite prime window. -/
def reciprocalMass (P : Finset ℕ) : ℝ := ∑ p ∈ P, (1 : ℝ) / p

/-- The finite-window mean-square fluctuation, with no probabilistic hypothesis. -/
def divisorVariance (P : Finset ℕ) (N : ℕ) : ℝ :=
  ∑ n ∈ initialInterval N, (divisorFrequency P n - reciprocalMass P) ^ 2

theorem bounded_weight_cauchy_schwarz {s : Finset ℕ} {f u : ℕ → ℂ}
    (hf : ∀ n ∈ s, ‖f n‖ ≤ 1) :
    ‖∑ n ∈ s, f n * u n‖ ^ 2 ≤ (s.card : ℝ) * ∑ n ∈ s, ‖u n‖ ^ 2 := by
  have hnorm : ‖∑ n ∈ s, f n * u n‖ ≤ ∑ n ∈ s, ‖u n‖ := by
    calc
      _ ≤ ∑ n ∈ s, ‖f n * u n‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ s, ‖u n‖ := sum_le_sum fun n hn => by
        rw [norm_mul]
        simpa using mul_le_mul_of_nonneg_right (hf n hn) (norm_nonneg (u n))
  have hsq := sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun n => ‖u n‖)
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at hsq
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hsq

theorem bounded_weight_sqrt_bound {s : Finset ℕ} {f u : ℕ → ℂ}
    (hf : ∀ n ∈ s, ‖f n‖ ≤ 1) :
    ‖∑ n ∈ s, f n * u n‖ ≤ Real.sqrt ((s.card : ℝ) * ∑ n ∈ s, ‖u n‖ ^ 2) := by
  exact (Real.le_sqrt (norm_nonneg _) (by positivity)).2
    (bounded_weight_cauchy_schwarz hf)

theorem dilation_reindex {g : ℕ → ℂ} {p N : ℕ} (hp : 0 < p) :
    (∑ n ∈ (initialInterval N).filter (fun n => p ∣ n), g n) =
      ∑ m ∈ initialInterval (N / p), g (p * m) := by
  classical
  symm
  apply sum_bij (fun m _ => p * m)
  · intro m hm
    obtain ⟨hm0, hmN⟩ := mem_Ioc.mp hm
    refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨Nat.mul_pos hp hm0, ?_⟩, dvd_mul_right p m⟩
    simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hp).mp hmN
  · intro m hm m' hm' heq
    exact Nat.eq_of_mul_eq_mul_left hp heq
  · intro n hn
    obtain ⟨hnI, hdiv⟩ := mem_filter.mp hn
    obtain ⟨m, rfl⟩ := hdiv
    refine ⟨m, mem_Ioc.mpr ⟨?_, ?_⟩, rfl⟩
    · exact Nat.pos_of_mul_pos_left (mem_Ioc.mp hnI).1
    · exact (Nat.le_div_iff_mul_le hp).mpr (by simpa [Nat.mul_comm] using (mem_Ioc.mp hnI).2)
  · intro m hm
    rfl

/-- Weighted divisor amplification before using multiplicativity. -/
theorem divisor_amplification_identity {P : Finset ℕ} {a f : ℕ → ℂ} {N : ℕ}
    (hP : ∀ p ∈ P, 0 < p) :
    (∑ n ∈ initialInterval N, f n * a n * (divisorFrequency P n : ℂ)) =
      ∑ p ∈ P, ∑ m ∈ initialInterval (N / p), f (p * m) * a (p * m) := by
  classical
  unfold divisorFrequency
  simp only [Complex.ofReal_sum, apply_ite (fun r : ℝ => (r : ℂ)), Complex.ofReal_one,
    Complex.ofReal_zero, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  simp only [mul_ite, mul_one, mul_zero, ← sum_filter]
  exact dilation_reindex (hP p hp)

/-- The frequency error is controlled by its actual finite variance. -/
theorem divisor_frequency_error {P : Finset ℕ} {a f : ℕ → ℂ} {N : ℕ}
    (ha : ∀ n, ‖a n‖ ≤ 1) (hf : ∀ n, ‖f n‖ ≤ 1) :
    ‖(reciprocalMass P : ℂ) * (∑ n ∈ initialInterval N, f n * a n) -
      (∑ n ∈ initialInterval N, f n * a n * (divisorFrequency P n : ℂ))‖ ≤
      Real.sqrt ((N : ℝ) * divisorVariance P N) := by
  have hfactor :
      (reciprocalMass P : ℂ) * (∑ n ∈ initialInterval N, f n * a n) -
        (∑ n ∈ initialInterval N, f n * a n * (divisorFrequency P n : ℂ)) =
      ∑ n ∈ initialInterval N, (f n * a n) *
        ((reciprocalMass P - divisorFrequency P n : ℝ) : ℂ) := by
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro n hn
    push_cast
    ring
  rw [hfactor]
  have hbounded : ∀ n ∈ initialInterval N, ‖f n * a n‖ ≤ 1 := by
    intro n hn
    rw [norm_mul]
    exact (mul_le_mul (hf n) (ha n) (norm_nonneg _) (by positivity)).trans_eq (one_mul 1)
  convert bounded_weight_sqrt_bound hbounded using 1
  simp only [initialInterval, Nat.card_Ioc, Nat.sub_zero, divisorVariance,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  congr 2
  apply sum_congr rfl
  intro n hn
  ring

theorem truncated_sum_eq {p N : ℕ} (hp : 0 < p) (g : ℕ → ℂ) :
    (∑ m ∈ initialInterval N, if p * m ≤ N then g m else 0) =
      ∑ m ∈ initialInterval (N / p), g m := by
  classical
  rw [← sum_filter]
  congr 1
  ext m
  simp only [initialInterval, mem_filter, mem_Ioc]
  constructor
  · rintro ⟨⟨hm0, hmN⟩, hpm⟩
    exact ⟨hm0, (Nat.le_div_iff_mul_le hp).mpr (by simpa [Nat.mul_comm] using hpm)⟩
  · rintro ⟨hm0, hmN⟩
    have hpm : p * m ≤ N := by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hp).mp hmN
    refine ⟨⟨hm0, ?_⟩, hpm⟩
    exact (Nat.le_mul_of_pos_left m hp).trans hpm

/-- The sole multiplicativity exception is counted exactly by multiples of `p²`. -/
theorem multiplicativity_dilation_error {a f : ℕ → ℂ} {p N : ℕ}
    (hp : p.Prime) (ha : ∀ n, ‖a n‖ ≤ 1) (hf : ∀ n, ‖f n‖ ≤ 1)
    (hmul : ∀ m n, m.Coprime n → f (m * n) = f m * f n) :
    ‖(∑ m ∈ initialInterval (N / p), f (p * m) * a (p * m)) -
      (∑ m ∈ initialInterval (N / p), f m * (f p * a (p * m)))‖ ≤
      2 * ((N / (p * p) : ℕ) : ℝ) := by
  classical
  rw [← sum_sub_distrib]
  have hrestrict :
      (∑ m ∈ initialInterval (N / p), (f (p * m) * a (p * m) - f m * (f p * a (p * m)))) =
      ∑ m ∈ (initialInterval (N / p)).filter (fun m => p ∣ m),
        (f (p * m) * a (p * m) - f m * (f p * a (p * m))) := by
    rw [sum_filter]
    apply sum_congr rfl
    intro m hm
    split_ifs with hpm
    · rfl
    · rw [hmul p m (hp.coprime_iff_not_dvd.mpr hpm)]
      ring
  rw [hrestrict]
  calc
    _ ≤ ∑ m ∈ (initialInterval (N / p)).filter (fun m => p ∣ m),
        ‖f (p * m) * a (p * m) - f m * (f p * a (p * m))‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ (initialInterval (N / p)).filter (fun m => p ∣ m), (2 : ℝ) := by
      apply sum_le_sum
      intro m hm
      have h1 : ‖f (p * m) * a (p * m)‖ ≤ 1 := by
        rw [norm_mul]
        simpa using mul_le_mul (hf (p*m)) (ha (p*m)) (norm_nonneg _) (by positivity)
      have h2 : ‖f m * (f p * a (p * m))‖ ≤ 1 := by
        rw [norm_mul, norm_mul]
        have hpa : ‖f p‖ * ‖a (p * m)‖ ≤ 1 := by
          simpa using mul_le_mul (hf p) (ha (p*m)) (norm_nonneg _) (by positivity)
        simpa using mul_le_mul (hf m) hpa (by positivity) (by positivity)
      exact (norm_sub_le _ _).trans (by linarith)
    _ = 2 * ((N / (p * p) : ℕ) : ℝ) := by
      simp only [sum_const, nsmul_eq_mul, initialInterval, Nat.Ioc_filter_dvd_card_eq_div,
        Nat.div_div_eq_div_mul]
      ring

theorem complex_norm_square_re (z : ℂ) : ‖z‖ ^ 2 = (z * star z).re := by
  have h : z * star z = (‖z‖ : ℂ) ^ 2 := RCLike.mul_conj z
  rw [h, ← Complex.ofReal_pow]
  rfl

/-- A finite Gram estimate retains the sums of the actual correlations. -/
theorem finite_gram_bound (s P : Finset ℕ) (v : ℕ → ℕ → ℂ) :
    (∑ m ∈ s, ‖∑ p ∈ P, v p m‖ ^ 2) ≤
      ∑ p ∈ P, ∑ q ∈ P, ‖∑ m ∈ s, v p m * star (v q m)‖ := by
  have hgram :
      (∑ m ∈ s, ‖∑ p ∈ P, v p m‖ ^ 2) =
        ∑ p ∈ P, ∑ q ∈ P, (∑ m ∈ s, v p m * star (v q m)).re := by
    simp_rw [complex_norm_square_re, star_sum, sum_mul, mul_sum, Complex.re_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro p hp
    rw [sum_comm]
  rw [hgram]
  exact sum_le_sum fun p hp => sum_le_sum fun q hq => Complex.re_le_norm _

def dilationTerm (a f : ℕ → ℂ) (N p m : ℕ) : ℂ :=
  if p * m ≤ N then f p * a (p * m) else 0

def offDiagonalMass (a : ℕ → ℂ) (P : Finset ℕ) (N : ℕ) : ℝ :=
  ∑ p ∈ P, ∑ q ∈ P, if p = q then (0 : ℝ)
    else ‖dilationCorrelation a p q (N / max p q)‖

def squareDivisorError (P : Finset ℕ) (N : ℕ) : ℝ :=
  2 * ∑ p ∈ P, ((N / (p * p) : ℕ) : ℝ)

theorem dilationTerm_correlation {a f : ℕ → ℂ} {N p q : ℕ}
    (hp : 0 < p) (_hq : 0 < q) :
    (∑ m ∈ initialInterval N, dilationTerm a f N p m * star (dilationTerm a f N q m)) =
      (f p * star (f q)) * dilationCorrelation a p q (N / max p q) := by
  classical
  have hpoint : ∀ m, dilationTerm a f N p m * star (dilationTerm a f N q m) =
      if max p q * m ≤ N then
        (f p * star (f q)) * (a (p * m) * star (a (q * m))) else 0 := by
    intro m
    have hmax : max p q * m ≤ N ↔ p * m ≤ N ∧ q * m ≤ N := by
      rw [max_mul, max_le_iff]
    simp only [dilationTerm]
    by_cases hpm : p * m ≤ N <;> by_cases hqm : q * m ≤ N
    · simp [hpm, hqm, hmax, star_mul]
      ring
    · simp [hpm, hqm, hmax]
    · simp [hpm, hqm, hmax]
    · simp [hpm, hqm, hmax]
  simp_rw [hpoint]
  rw [truncated_sum_eq (lt_of_lt_of_le hp (le_max_left _ _))]
  simp only [dilationCorrelation, mul_sum]

theorem dilationTerm_gram_bound {a f : ℕ → ℂ} {P : Finset ℕ} {N : ℕ}
    (hP : ∀ p ∈ P, 0 < p) (ha : ∀ n, ‖a n‖ ≤ 1) (hf : ∀ n, ‖f n‖ ≤ 1) :
    (∑ m ∈ initialInterval N, ‖∑ p ∈ P, dilationTerm a f N p m‖ ^ 2) ≤
      (∑ p ∈ P, ((N / p : ℕ) : ℝ)) + offDiagonalMass a P N := by
  classical
  have hpair : ∀ p ∈ P, ∀ q ∈ P,
      ‖∑ m ∈ initialInterval N, dilationTerm a f N p m * star (dilationTerm a f N q m)‖ ≤
      if p = q then ((N / p : ℕ) : ℝ) else ‖dilationCorrelation a p q (N / max p q)‖ := by
    intro p hp q hq
    rw [dilationTerm_correlation (hP p hp) (hP q hq), norm_mul]
    have hcoeff : ‖f p * star (f q)‖ ≤ 1 := by
      rw [norm_mul, norm_star]
      simpa using mul_le_mul (hf p) (hf q) (norm_nonneg _) (by positivity)
    have hnorm := mul_le_mul_of_nonneg_right hcoeff
      (norm_nonneg (dilationCorrelation a p q (N / max p q)))
    rw [one_mul] at hnorm
    split_ifs with hpq
    · subst q
      apply hnorm.trans
      simp only [max_self, dilationCorrelation]
      calc
        _ ≤ ∑ m ∈ initialInterval (N / p), ‖a (p * m) * star (a (p * m))‖ := norm_sum_le _ _
        _ ≤ ∑ m ∈ initialInterval (N / p), (1 : ℝ) := by
          apply sum_le_sum
          intro m hm
          rw [norm_mul, norm_star]
          simpa using mul_le_mul (ha (p*m)) (ha (p*m)) (norm_nonneg _) (by positivity)
        _ = ((N / p : ℕ) : ℝ) := by simp [initialInterval]
    · exact hnorm
  calc
    _ ≤ ∑ p ∈ P, ∑ q ∈ P,
        ‖∑ m ∈ initialInterval N, dilationTerm a f N p m * star (dilationTerm a f N q m)‖ :=
      finite_gram_bound _ _ _
    _ ≤ ∑ p ∈ P, ∑ q ∈ P,
        if p = q then ((N / p : ℕ) : ℝ) else ‖dilationCorrelation a p q (N / max p q)‖ :=
      sum_le_sum fun p hp => sum_le_sum fun q hq => hpair p hp q hq
    _ = _ := by
      unfold offDiagonalMass
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro p hp
      have hd : ((N / p : ℕ) : ℝ) =
          ∑ q ∈ P, if p = q then ((N / p : ℕ) : ℝ) else 0 := by
        simp [hp]
      rw [hd, ← sum_add_distrib]
      apply sum_congr rfl
      intro q hq
      split_ifs <;> simp_all

/-- The finite Kátai amplification inequality.  Its off-diagonal terms are genuine
    multiplicative dilations and its multiplicativity error is explicit. -/
theorem finite_katai_inequality {a f : ℕ → ℂ} {P : Finset ℕ} {N : ℕ}
    (hP : ∀ p ∈ P, p.Prime) (ha : ∀ n, ‖a n‖ ≤ 1) (hf : ∀ n, ‖f n‖ ≤ 1)
    (hmul : ∀ m n, m.Coprime n → f (m * n) = f m * f n) :
    reciprocalMass P * ‖∑ n ∈ initialInterval N, f n * a n‖ ≤
      Real.sqrt ((N : ℝ) * divisorVariance P N) +
      Real.sqrt ((N : ℝ) * ((∑ p ∈ P, ((N / p : ℕ) : ℝ)) + offDiagonalMass a P N)) +
      squareDivisorError P N := by
  classical
  let W : ℂ := ∑ n ∈ initialInterval N, f n * a n * (divisorFrequency P n : ℂ)
  let T : ℂ := ∑ m ∈ initialInterval N, f m * (∑ p ∈ P, dilationTerm a f N p m)
  have herror : ‖W - T‖ ≤ squareDivisorError P N := by
    dsimp [W, T]
    rw [divisor_amplification_identity (fun p hp => (hP p hp).pos)]
    simp only [mul_sum]
    rw [sum_comm]
    have hT : ∀ p ∈ P,
        (∑ m ∈ initialInterval N, f m * dilationTerm a f N p m) =
          ∑ m ∈ initialInterval (N / p), f m * (f p * a (p * m)) := by
      intro p hp
      simp only [dilationTerm, mul_ite, mul_zero]
      exact truncated_sum_eq (hP p hp).pos _
    rw [sum_congr rfl hT, ← sum_sub_distrib]
    calc
      _ ≤ ∑ p ∈ P, ‖(∑ m ∈ initialInterval (N / p), f (p * m) * a (p * m)) -
          (∑ m ∈ initialInterval (N / p), f m * (f p * a (p * m)))‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ P, 2 * ((N / (p * p) : ℕ) : ℝ) :=
        sum_le_sum fun p hp => multiplicativity_dilation_error (hP p hp) ha hf hmul
      _ = squareDivisorError P N := by simp [squareDivisorError, mul_sum]
  have hT : ‖T‖ ≤ Real.sqrt ((N : ℝ) *
      ((∑ p ∈ P, ((N / p : ℕ) : ℝ)) + offDiagonalMass a P N)) := by
    calc
      _ ≤ Real.sqrt (((initialInterval N).card : ℝ) *
          ∑ m ∈ initialInterval N, ‖∑ p ∈ P, dilationTerm a f N p m‖ ^ 2) :=
        bounded_weight_sqrt_bound (fun m hm => hf m)
      _ ≤ _ := by
        simp only [initialInterval, Nat.card_Ioc, Nat.sub_zero]
        exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
          (dilationTerm_gram_bound (fun p hp => (hP p hp).pos) ha hf) (Nat.cast_nonneg _))
  have hcenter := divisor_frequency_error (P := P) (N := N) ha hf
  have hL : 0 ≤ reciprocalMass P := sum_nonneg fun p hp => by positivity
  calc
    _ = ‖(reciprocalMass P : ℂ) * (∑ n ∈ initialInterval N, f n * a n)‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hL]
    _ ≤ ‖(reciprocalMass P : ℂ) * (∑ n ∈ initialInterval N, f n * a n) - W‖ + ‖W‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ Real.sqrt ((N : ℝ) * divisorVariance P N) + (‖W - T‖ + ‖T‖) :=
      add_le_add hcenter (norm_le_norm_sub_add _ _)
    _ ≤ _ := by linarith

end

end RankCertificates.ArithmeticOrthogonality
