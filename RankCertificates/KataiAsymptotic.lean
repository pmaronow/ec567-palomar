module

public import RankCertificates.PrimeDivisorMoments
public import Mathlib.NumberTheory.SumPrimeReciprocals
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.PSeries

@[expose] public section

open scoped BigOperators Topology
open Finset Filter

namespace RankCertificates.ArithmeticOrthogonality

noncomputable section

def normalizedSum (f a : ℕ → ℂ) (N : ℕ) : ℂ :=
  (∑ n ∈ initialInterval N, f n * a n) / (N : ℂ)

/-- This hypothesis concerns integer multiplicative dilations, not additive shifts. -/
def VanishingPrimeDilationCorrelations (a : ℕ → ℂ) : Prop :=
  ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q →
    Tendsto (fun N => dilationCorrelation a p q N / (N : ℂ)) atTop (𝓝 0)

/-- Windows may omit exceptional primes or pairs, provided their reciprocal mass
    is arbitrarily large and every distinct pair in the chosen window cancels. -/
def AdmitsLargeOrthogonalPrimeWindows (a : ℕ → ℂ) : Prop :=
  ∀ R : ℝ, ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime) ∧ R < reciprocalMass P ∧
    ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      Tendsto (fun N => dilationCorrelation a p q N / (N : ℂ)) atTop (𝓝 0)

theorem sqrt_quadratic_factor (N u v : ℝ) (hN : 0 < N) :
    Real.sqrt (N * (N * u + v)) / N = Real.sqrt (u + v / N) := by
  have hfactor : N * (N * u + v) = N ^ 2 * (u + v / N) := by
    field_simp
  rw [hfactor, Real.sqrt_mul (sq_nonneg N), Real.sqrt_sq (le_of_lt hN)]
  exact mul_div_cancel_left₀ _ (ne_of_gt hN)

/-- The normalized finite estimate, suitable for passing to the limit with a fixed window. -/
theorem normalized_finite_katai {a f : ℕ → ℂ} {P : Finset ℕ} {N : ℕ}
    (hN : 0 < N) (hP : ∀ p ∈ P, p.Prime)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hf : ∀ n, ‖f n‖ ≤ 1)
    (hmul : ∀ m n, m.Coprime n → f (m * n) = f m * f n) :
    reciprocalMass P * ‖normalizedSum f a N‖ ≤
      Real.sqrt (reciprocalMass P + 2 * reciprocalMass P * (P.card : ℝ) / (N : ℝ)) +
      Real.sqrt (reciprocalMass P + offDiagonalMass a P N / (N : ℝ)) +
      2 * ∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h := div_le_div_of_nonneg_right (finite_katai_explicit (N := N) hP ha hf hmul) (le_of_lt hNr)
  rw [add_div, add_div, sqrt_quadratic_factor _ _ _ hNr,
    sqrt_quadratic_factor _ _ _ hNr] at h
  have hleft : reciprocalMass P * ‖normalizedSum f a N‖ =
      (reciprocalMass P * ‖∑ n ∈ initialInterval N, f n * a n‖) / (N : ℝ) := by
    simp only [normalizedSum, norm_div, Complex.norm_natCast]
    ring
  rw [hleft]
  convert h using 1
  field_simp

theorem dilation_cutoff_norm_tendsto {a : ℕ → ℂ} {p q k : ℕ}
    (hk : 0 < k)
    (h : Tendsto (fun N => dilationCorrelation a p q N / (N : ℂ)) atTop (𝓝 0)) :
    Tendsto (fun N => ‖dilationCorrelation a p q (N / k)‖ / (N : ℝ)) atTop (𝓝 0) := by
  have hnorm : Tendsto (fun H => ‖dilationCorrelation a p q H‖ / (H : ℝ)) atTop (𝓝 0) := by
    simpa only [norm_div, Complex.norm_natCast, norm_zero] using h.norm
  have hcut := hnorm.comp (Nat.tendsto_div_const_atTop (ne_of_gt hk))
  apply squeeze_zero' (Eventually.of_forall (fun N => by positivity)) _ hcut
  have hpos : ∀ᶠ N : ℕ in atTop, 0 < N / k :=
    (Nat.tendsto_div_const_atTop (ne_of_gt hk)).eventually (eventually_gt_atTop 0)
  filter_upwards [hpos] with N hNk
  have hN : 0 < N := lt_of_lt_of_le hNk (Nat.div_le_self _ _)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNkr : (0 : ℝ) < (N / k : ℕ) := by exact_mod_cast hNk
  apply (div_le_div_iff₀ hNr hNkr).mpr
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.div_le_self N k) (norm_nonneg _)

theorem offDiagonalMass_normalized_tendsto_of_window {a : ℕ → ℂ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime)
    (h : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      Tendsto (fun N => dilationCorrelation a p q N / (N : ℂ)) atTop (𝓝 0)) :
    Tendsto (fun N => offDiagonalMass a P N / (N : ℝ)) atTop (𝓝 0) := by
  classical
  have hpair : ∀ p ∈ P, ∀ q ∈ P,
      Tendsto (fun N => (if p = q then (0 : ℝ)
        else ‖dilationCorrelation a p q (N / max p q)‖) / (N : ℝ)) atTop (𝓝 0) := by
    intro p hp q hq
    by_cases hpq : p = q
    · simp only [hpq, ite_true, zero_div]
      exact tendsto_const_nhds
    · simp only [hpq, ite_false]
      exact dilation_cutoff_norm_tendsto
        (lt_of_lt_of_le (hP p hp).pos (le_max_left _ _)) (h p hp q hq hpq)
  simpa only [offDiagonalMass, div_eq_mul_inv, sum_mul, sum_const_zero] using
    tendsto_finsetSum P (fun p hp => tendsto_finsetSum P (fun q hq => hpair p hp q hq))

theorem offDiagonalMass_normalized_tendsto {a : ℕ → ℂ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (h : VanishingPrimeDilationCorrelations a) :
    Tendsto (fun N => offDiagonalMass a P N / (N : ℝ)) atTop (𝓝 0) :=
  offDiagonalMass_normalized_tendsto_of_window hP
    (fun p hp q hq hpq => h p q (hP p hp) (hP q hq) hpq)

theorem exists_prime_window_large (R : ℝ) :
    ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime) ∧ R < reciprocalMass P := by
  classical
  by_contra h
  push Not at h
  apply not_summable_one_div_on_primes
  apply summable_of_sum_le (c := R)
  · intro n
    by_cases hn : n.Prime <;> simp [hn]
  · intro s
    have hbound := h (s.filter Nat.Prime) (fun p hp => (mem_filter.mp hp).2)
    simpa only [reciprocalMass, sum_filter, Set.indicator_apply, Set.mem_ofPred_eq] using hbound

theorem VanishingPrimeDilationCorrelations.large_windows {a : ℕ → ℂ}
    (h : VanishingPrimeDilationCorrelations a) : AdmitsLargeOrthogonalPrimeWindows a := by
  intro R
  obtain ⟨P, hP, hR⟩ := exists_prime_window_large R
  exact ⟨P, hP, hR, fun p hp q hq hpq => h p q (hP p hp) (hP q hq) hpq⟩

def reciprocalSquareTotal : ℝ := ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2

theorem reciprocalSquareTotal_nonneg : 0 ≤ reciprocalSquareTotal := by
  exact tsum_nonneg fun n => by positivity

theorem reciprocalSquareSum_le (P : Finset ℕ) :
    (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) ≤ reciprocalSquareTotal := by
  exact Summable.sum_le_tsum P (fun n hn => by positivity)
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2:ℕ)))

theorem window_remainder_tendsto :
    Tendsto (fun L : ℝ => (2 * Real.sqrt L + 2 * reciprocalSquareTotal) / L)
      atTop (𝓝 0) := by
  have h1 : Tendsto (fun L : ℝ => (Real.sqrt L)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  have h2 : Tendsto (fun L : ℝ => L⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  convert (h1.const_mul 2).add (h2.const_mul (2 * reciprocalSquareTotal)) using 1
  · funext L
    rw [add_div, mul_div_assoc, Real.sqrt_div_self]
    rfl
  · simp

/-- The genuine qualitative Kátai criterion for every one-bounded multiplicative weight.
    The only analytic premise is actual cancellation of prime multiplicative dilations. -/
theorem katai_criterion_of_large_orthogonal_prime_windows {a f : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ 1) (hf : ∀ n, ‖f n‖ ≤ 1)
    (hmul : ∀ m n, m.Coprime n → f (m * n) = f m * f n)
    (hcor : AdmitsLargeOrthogonalPrimeWindows a) :
    Tendsto (normalizedSum f a) atTop (𝓝 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero]
  apply tendsto_order.mpr
  constructor
  · intro ε hε
    exact Eventually.of_forall fun N => lt_of_lt_of_le hε (norm_nonneg _)
  · intro ε hε
    have hev := window_remainder_tendsto.eventually (gt_mem_nhds hε)
    obtain ⟨R, hR⟩ := eventually_atTop.mp hev
    obtain ⟨P, hP, hPL, hPairs⟩ := hcor (max R 1)
    let L := reciprocalMass P
    have hL : 0 < L := lt_trans zero_lt_one (lt_of_le_of_lt (le_max_right _ _) hPL)
    have hlimit : (2 * Real.sqrt L + 2 * reciprocalSquareTotal) / L < ε :=
      hR L (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hPL))
    let U : ℕ → ℝ := fun N =>
      (Real.sqrt (L + 2 * L * (P.card : ℝ) / (N : ℝ)) +
        Real.sqrt (L + offDiagonalMass a P N / (N : ℝ)) +
        2 * reciprocalSquareTotal) / L
    have hU : Tendsto U atTop (𝓝 ((2 * Real.sqrt L + 2 * reciprocalSquareTotal) / L)) := by
      have hV := tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (2 * L * (P.card : ℝ))
      have hG := offDiagonalMass_normalized_tendsto_of_window hP hPairs
      have hA := ((tendsto_const_nhds (x := L)).add hV).sqrt
      have hB := ((tendsto_const_nhds (x := L)).add hG).sqrt
      convert ((hA.add hB).add_const (2 * reciprocalSquareTotal)).div_const L using 1
      congr 1
      simp only [add_zero]
      ring
    have hUε := hU.eventually (gt_mem_nhds hlimit)
    filter_upwards [hUε, eventually_gt_atTop (0:ℕ)] with N hUN hN
    have hfinite := normalized_finite_katai hN hP ha hf hmul
    have hupper : ‖normalizedSum f a N‖ ≤ U N := by
      apply (le_div_iff₀ hL).mpr
      change ‖normalizedSum f a N‖ * L ≤ _
      have hZ := reciprocalSquareSum_le P
      dsimp [L] at *
      nlinarith
    exact hupper.trans_lt hUN

theorem katai_criterion {a f : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ 1) (hf : ∀ n, ‖f n‖ ≤ 1)
    (hmul : ∀ m n, m.Coprime n → f (m * n) = f m * f n)
    (hcor : VanishingPrimeDilationCorrelations a) :
    Tendsto (normalizedSum f a) atTop (𝓝 0) :=
  katai_criterion_of_large_orthogonal_prime_windows ha hf hmul hcor.large_windows

theorem dilationCorrelation_mul_const (c : ℂ) (a : ℕ → ℂ) (p q N : ℕ) :
    dilationCorrelation (fun n => c * a n) p q N =
      (c * star c) * dilationCorrelation a p q N := by
  unfold dilationCorrelation
  rw [mul_sum]
  apply sum_congr rfl
  intro n hn
  rw [star_mul]
  ring

theorem normalizedSum_mul_const (c : ℂ) (f a : ℕ → ℂ) (N : ℕ) :
    normalizedSum f (fun n => c * a n) N = c * normalizedSum f a N := by
  unfold normalizedSum
  rw [← mul_div_assoc, mul_sum]
  congr 1
  apply sum_congr rfl
  intro n hn
  ring

theorem VanishingPrimeDilationCorrelations.mul_const {a : ℕ → ℂ}
    (h : VanishingPrimeDilationCorrelations a) (c : ℂ) :
    VanishingPrimeDilationCorrelations (fun n => c * a n) := by
  intro p q hp hq hpq
  have ht := (h p q hp hq hpq).const_mul (c * star c)
  simpa only [mul_zero, dilationCorrelation_mul_const, mul_div_assoc] using ht

theorem AdmitsLargeOrthogonalPrimeWindows.mul_const {a : ℕ → ℂ}
    (h : AdmitsLargeOrthogonalPrimeWindows a) (c : ℂ) :
    AdmitsLargeOrthogonalPrimeWindows (fun n => c * a n) := by
  intro R
  obtain ⟨P, hP, hR, hPairs⟩ := h R
  refine ⟨P, hP, hR, ?_⟩
  intro p hp q hq hpq
  have ht := (hPairs p hp q hq hpq).const_mul (c * star c)
  simpa only [mul_zero, dilationCorrelation_mul_const, mul_div_assoc] using ht

/-- The criterion also applies to sequences bounded by any fixed positive constant. -/
theorem katai_criterion_of_bounded_sequence_and_large_windows {a f : ℕ → ℂ} {C : ℝ}
    (hC : 0 < C) (ha : ∀ n, ‖a n‖ ≤ C) (hf : ∀ n, ‖f n‖ ≤ 1)
    (hmul : ∀ m n, m.Coprime n → f (m * n) = f m * f n)
    (hcor : AdmitsLargeOrthogonalPrimeWindows a) :
    Tendsto (normalizedSum f a) atTop (𝓝 0) := by
  let c : ℂ := (C : ℂ)⁻¹
  have hscaled : ∀ n, ‖c * a n‖ ≤ 1 := by
    intro n
    dsimp [c]
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC]
    rw [← div_eq_inv_mul]
    exact (div_le_one hC).mpr (ha n)
  have ht := (katai_criterion_of_large_orthogonal_prime_windows hscaled hf hmul
    (hcor.mul_const c)).const_mul (C : ℂ)
  have hCc : (C : ℂ) * c = 1 := by
    exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt hC))
  have hid : (fun N => (C : ℂ) * normalizedSum f (fun n => c * a n) N) =
      normalizedSum f a := by
    funext N
    rw [normalizedSum_mul_const, ← mul_assoc, hCc, one_mul]
  simpa only [hid, mul_zero] using ht

theorem katai_criterion_of_bounded_sequence {a f : ℕ → ℂ} {C : ℝ}
    (hC : 0 < C) (ha : ∀ n, ‖a n‖ ≤ C) (hf : ∀ n, ‖f n‖ ≤ 1)
    (hmul : ∀ m n, m.Coprime n → f (m * n) = f m * f n)
    (hcor : VanishingPrimeDilationCorrelations a) :
    Tendsto (normalizedSum f a) atTop (𝓝 0) :=
  katai_criterion_of_bounded_sequence_and_large_windows hC ha hf hmul hcor.large_windows

/-- The genuine Möbius sequence, viewed as a complex arithmetic weight. -/
def complexMoebius (n : ℕ) : ℂ := (ArithmeticFunction.moebius n : ℤ)

theorem complexMoebius_norm_le_one (n : ℕ) : ‖complexMoebius n‖ ≤ 1 := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;>
    simp [complexMoebius, h]

theorem complexMoebius_multiplicative (m n : ℕ) (h : m.Coprime n) :
    complexMoebius (m * n) = complexMoebius m * complexMoebius n := by
  unfold complexMoebius
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h]
  exact Int.cast_mul _ _

/-- Möbius orthogonality follows from the stated genuine dilation cancellation.
    No cancellation theorem for nilsequences is assumed to have been proved here. -/
theorem moebius_orthogonality_of_prime_dilation_cancellation {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ 1) (hcor : VanishingPrimeDilationCorrelations a) :
    Tendsto (normalizedSum complexMoebius a) atTop (𝓝 0) :=
  katai_criterion ha complexMoebius_norm_le_one complexMoebius_multiplicative hcor

theorem moebius_orthogonality_of_bounded_prime_dilation_cancellation
    {a : ℕ → ℂ} {C : ℝ} (hC : 0 < C) (ha : ∀ n, ‖a n‖ ≤ C)
    (hcor : VanishingPrimeDilationCorrelations a) :
    Tendsto (normalizedSum complexMoebius a) atTop (𝓝 0) :=
  katai_criterion_of_bounded_sequence hC ha complexMoebius_norm_le_one
    complexMoebius_multiplicative hcor

theorem moebius_orthogonality_of_bounded_large_orthogonal_prime_windows
    {a : ℕ → ℂ} {C : ℝ} (hC : 0 < C) (ha : ∀ n, ‖a n‖ ≤ C)
    (hcor : AdmitsLargeOrthogonalPrimeWindows a) :
    Tendsto (normalizedSum complexMoebius a) atTop (𝓝 0) :=
  katai_criterion_of_bounded_sequence_and_large_windows hC ha complexMoebius_norm_le_one
    complexMoebius_multiplicative hcor

end

end RankCertificates.ArithmeticOrthogonality
