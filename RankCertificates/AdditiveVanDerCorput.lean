module

public import RankCertificates.KataiAsymptotic

@[expose] public section

open scoped BigOperators Topology
open Finset Filter

namespace RankCertificates.ArithmeticOrthogonality

noncomputable section

/-- The correlation is an actual additive shift on the positive integer interval. -/
def additiveCorrelation (a : ℕ → ℂ) (h N : ℕ) : ℂ :=
  ∑ n ∈ initialInterval N, a (n + h) * star (a n)

def additiveMean (a : ℕ → ℂ) (N : ℕ) : ℂ :=
  (∑ n ∈ initialInterval N, a n) / (N : ℂ)

/-- Cancellation for every fixed positive additive shift. -/
def VanishingAdditiveCorrelations (a : ℕ → ℂ) : Prop :=
  ∀ h : ℕ, 0 < h →
    Tendsto (fun N => additiveCorrelation a h N / (N : ℂ)) atTop (𝓝 0)

def shiftPairCorrelation (a : ℕ → ℂ) (h k N : ℕ) : ℂ :=
  ∑ n ∈ initialInterval N, a (n + h) * star (a (n + k))

def additiveOffDiagonalMass (a : ℕ → ℂ) (H N : ℕ) : ℝ :=
  ∑ h ∈ range H, ∑ k ∈ range H,
    if h = k then 0 else ‖shiftPairCorrelation a h k N‖

theorem sum_initialInterval_eq_range (g : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ initialInterval N, g n) = ∑ n ∈ range N, g (n + 1) := by
  classical
  symm
  apply sum_bij (fun n _ => n + 1)
  · intro n hn
    simp only [initialInterval, mem_Ioc, mem_range] at *
    omega
  · intro n hn m hm hnm
    omega
  · intro n hn
    have hn' := mem_Ioc.mp hn
    refine ⟨n - 1, mem_range.mpr (by omega), ?_⟩
    omega
  · intro n hn
    rfl

/-- Shifting a one-bounded interval sum changes only its two boundary pieces. -/
theorem additive_shift_boundary {g : ℕ → ℂ} (hg : ∀ n, ‖g n‖ ≤ 1)
    (h N : ℕ) :
    ‖(∑ n ∈ initialInterval N, g (n + h)) -
      (∑ n ∈ initialInterval N, g n)‖ ≤ 2 * (h : ℝ) := by
  let f : ℕ → ℂ := fun n => g (n + 1)
  have hsum : (∑ n ∈ range N, f (n + h)) - (∑ n ∈ range N, f n) =
      (∑ n ∈ range h, f (N + n)) - (∑ n ∈ range h, f n) := by
    have hleft := sum_range_add f h N
    have hright := sum_range_add f N h
    rw [Nat.add_comm h N] at hleft
    simp only [Nat.add_comm h] at hleft
    linear_combination hright - hleft
  have hprefix : ‖∑ n ∈ range h, f n‖ ≤ (h : ℝ) := by
    calc
      _ ≤ ∑ n ∈ range h, ‖f n‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ range h, (1 : ℝ) := sum_le_sum fun n hn => hg _
      _ = _ := by simp
  have htail : ‖∑ n ∈ range h, f (N + n)‖ ≤ (h : ℝ) := by
    calc
      _ ≤ ∑ n ∈ range h, ‖f (N + n)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ range h, (1 : ℝ) := sum_le_sum fun n hn => hg _
      _ = _ := by simp
  rw [sum_initialInterval_eq_range, sum_initialInterval_eq_range]
  have heq : (∑ n ∈ range N, g (n + 1 + h)) = ∑ n ∈ range N, f (n + h) := by
    apply sum_congr rfl
    intro n hn
    simp only [f]
    congr 1
    omega
  rw [heq, hsum]
  exact (norm_sub_le _ _).trans (by linarith)

theorem shiftPairCorrelation_norm_swap (a : ℕ → ℂ) (h k N : ℕ) :
    ‖shiftPairCorrelation a h k N‖ = ‖shiftPairCorrelation a k h N‖ := by
  have heq : star (shiftPairCorrelation a h k N) = shiftPairCorrelation a k h N := by
    simp only [shiftPairCorrelation, star_sum, star_mul, star_star]
  rw [← heq, norm_star]

/-- A shifted pair differs from its corresponding positive-shift correlation
    by at most the two translated boundary pieces. -/
theorem shiftPairCorrelation_boundary {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ 1) {h k : ℕ} (hkh : k ≤ h) (N : ℕ) :
    ‖shiftPairCorrelation a h k N - additiveCorrelation a (h - k) N‖ ≤ 2 * (k : ℝ) := by
  let g : ℕ → ℂ := fun n => a (n + (h - k)) * star (a n)
  have hg : ∀ n, ‖g n‖ ≤ 1 := by
    intro n
    dsimp [g]
    rw [norm_mul, RCLike.norm_conj]
    simpa using mul_le_mul (ha _) (ha _) (norm_nonneg _) (by positivity)
  have hb := additive_shift_boundary hg k N
  convert hb using 1
  congr 2
  apply sum_congr rfl
  intro n hn
  dsimp [g]
  congr 2
  omega

theorem shiftPairCorrelation_norm_tendsto {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ 1) (hcor : VanishingAdditiveCorrelations a)
    {h k : ℕ} (hhk : h ≠ k) :
    Tendsto (fun N => ‖shiftPairCorrelation a h k N‖ / (N : ℝ)) atTop (𝓝 0) := by
  have ordered : ∀ {h k : ℕ}, k < h →
      Tendsto (fun N => ‖shiftPairCorrelation a h k N‖ / (N : ℝ)) atTop (𝓝 0) := by
    intro h k hkh
    have hbase : Tendsto (fun N => ‖additiveCorrelation a (h - k) N‖ / (N : ℝ))
        atTop (𝓝 0) := by
      simpa only [norm_div, Complex.norm_natCast, norm_zero] using
        (hcor (h - k) (by omega)).norm
    have hlimit := hbase.add (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (2 * (k : ℝ)))
    simp only [zero_add] at hlimit
    apply squeeze_zero' (Eventually.of_forall fun N => by positivity) _ hlimit
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (le_of_lt hNr)
    have hb := shiftPairCorrelation_boundary ha (le_of_lt hkh) N
    have hn' := norm_add_le (additiveCorrelation a (h - k) N)
      (shiftPairCorrelation a h k N - additiveCorrelation a (h - k) N)
    have heq' : additiveCorrelation a (h - k) N +
        (shiftPairCorrelation a h k N - additiveCorrelation a (h - k) N) =
        shiftPairCorrelation a h k N := by ring
    rw [heq'] at hn'
    linarith
  rcases lt_or_gt_of_ne hhk with hlt | hgt
  · have ht := ordered hlt
    simpa only [shiftPairCorrelation_norm_swap a h k] using ht
  · exact ordered hgt

theorem additiveOffDiagonalMass_tendsto {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ 1) (hcor : VanishingAdditiveCorrelations a) (H : ℕ) :
    Tendsto (fun N => additiveOffDiagonalMass a H N / (N : ℝ)) atTop (𝓝 0) := by
  classical
  have hpair : ∀ h ∈ range H, ∀ k ∈ range H,
      Tendsto (fun N => (if h = k then (0 : ℝ)
        else ‖shiftPairCorrelation a h k N‖) / (N : ℝ)) atTop (𝓝 0) := by
    intro h hh k hk
    by_cases heq : h = k
    · simp only [heq, ite_true, zero_div]
      exact tendsto_const_nhds
    · simp only [heq, ite_false]
      exact shiftPairCorrelation_norm_tendsto ha hcor heq
  simpa only [additiveOffDiagonalMass, div_eq_mul_inv, sum_mul, sum_const_zero] using
    tendsto_finsetSum (range H) (fun h hh =>
      tendsto_finsetSum (range H) (fun k hk => hpair h hh k hk))

/-- A finite van der Corput estimate with literal shift correlations and explicit
    boundary error. No cancellation assumption occurs in this inequality. -/
theorem finite_additive_van_der_corput {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ 1) (H N : ℕ) :
    (H : ℝ) * ‖∑ n ∈ initialInterval N, a n‖ ≤
      2 * (H : ℝ) ^ 2 + Real.sqrt ((N : ℝ) *
        ((H : ℝ) * N + additiveOffDiagonalMass a H N)) := by
  classical
  let B : ℂ := ∑ n ∈ initialInterval N, ∑ h ∈ range H, a (n + h)
  have hboundary : ‖(H : ℂ) * (∑ n ∈ initialInterval N, a n) - B‖ ≤
      2 * (H : ℝ) ^ 2 := by
    have heq : (H : ℂ) * (∑ n ∈ initialInterval N, a n) - B =
        ∑ h ∈ range H, ((∑ n ∈ initialInterval N, a n) -
          (∑ n ∈ initialInterval N, a (n + h))) := by
      dsimp [B]
      rw [sum_sub_distrib, sum_const, nsmul_eq_mul, sum_comm]
      simp
    rw [heq]
    calc
      _ ≤ ∑ h ∈ range H, ‖(∑ n ∈ initialInterval N, a n) -
          (∑ n ∈ initialInterval N, a (n + h))‖ := norm_sum_le _ _
      _ ≤ ∑ h ∈ range H, 2 * (H : ℝ) := by
        apply sum_le_sum
        intro h hh
        rw [norm_sub_rev]
        exact (additive_shift_boundary ha h N).trans (by
          have : (h : ℝ) ≤ H := by exact_mod_cast (le_of_lt (mem_range.mp hh))
          linarith)
      _ = _ := by simp; ring
  have hgram : (∑ n ∈ initialInterval N, ‖∑ h ∈ range H, a (n + h)‖ ^ 2) ≤
      (H : ℝ) * N + additiveOffDiagonalMass a H N := by
    have hg := finite_gram_bound (initialInterval N) (range H) (fun h n => a (n + h))
    apply hg.trans
    have hdiag : ∀ h, ‖shiftPairCorrelation a h h N‖ ≤ (N : ℝ) := by
      intro h
      calc
        _ ≤ ∑ n ∈ initialInterval N, ‖a (n + h) * star (a (n + h))‖ := norm_sum_le _ _
        _ ≤ ∑ n ∈ initialInterval N, (1 : ℝ) := by
          apply sum_le_sum
          intro n hn
          rw [norm_mul, norm_star]
          simpa using mul_le_mul (ha _) (ha _) (norm_nonneg _) (by positivity)
        _ = _ := by simp [initialInterval]
    have hb : (∑ h ∈ range H, ∑ k ∈ range H, ‖shiftPairCorrelation a h k N‖) ≤
        ∑ h ∈ range H, ∑ k ∈ range H,
          ((if h = k then (N : ℝ) else 0) +
            (if h = k then 0 else ‖shiftPairCorrelation a h k N‖)) := by
      apply sum_le_sum
      intro h hh
      apply sum_le_sum
      intro k hk
      by_cases heq : h = k
      · subst k
        simpa using hdiag h
      · simp [heq]
    have hds : (∑ h ∈ range H, ∑ k ∈ range H,
        if h = k then (N : ℝ) else 0) = (H : ℝ) * N := by
      calc
        _ = ∑ h ∈ range H, (N : ℝ) := by
          apply sum_congr rfl
          intro h hh
          simp [mem_range.mp hh]
        _ = _ := by simp
    apply hb.trans_eq
    simp only [sum_add_distrib]
    rw [hds]
    rfl
  have hB : ‖B‖ ≤ Real.sqrt ((N : ℝ) *
      ((H : ℝ) * N + additiveOffDiagonalMass a H N)) := by
    have hcs := bounded_weight_sqrt_bound (s := initialInterval N)
      (f := fun _ => (1 : ℂ)) (u := fun n => ∑ h ∈ range H, a (n + h))
      (by intro n hn; simp)
    simp only [one_mul, initialInterval, Nat.card_Ioc, Nat.sub_zero] at hcs
    apply hcs.trans
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hgram (by positivity))
  have htri := norm_sub_le ((H : ℂ) * (∑ n ∈ initialInterval N, a n) - B) (-B)
  simp only [sub_neg_eq_add, sub_add_cancel, norm_neg, norm_mul, Complex.norm_natCast] at htri
  linarith

/-- Normalized finite estimate, for a fixed averaging window. -/
theorem normalized_additive_van_der_corput {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ 1) {H N : ℕ} (hH : 0 < H) (hN : 0 < N) :
    ‖additiveMean a N‖ ≤ 2 * (H : ℝ) / (N : ℝ) +
      Real.sqrt ((H : ℝ) + additiveOffDiagonalMass a H N / (N : ℝ)) / (H : ℝ) := by
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hb := div_le_div_of_nonneg_right (finite_additive_van_der_corput ha H N) (le_of_lt hNr)
  rw [add_div, mul_comm (H : ℝ) (N : ℝ), sqrt_quadratic_factor _ _ _ hNr] at hb
  simp only [additiveMean, norm_div, Complex.norm_natCast]
  have heq : (H : ℝ) * (2 * (H : ℝ) / N +
      Real.sqrt ((H : ℝ) + additiveOffDiagonalMass a H N / N) / H) =
      2 * (H : ℝ) ^ 2 / N + Real.sqrt ((H : ℝ) + additiveOffDiagonalMass a H N / N) := by
    field_simp
  apply (mul_le_mul_iff_right₀ hHr).mp
  rw [heq]
  convert hb using 1
  ring

/-- The genuine qualitative additive van der Corput criterion. -/
theorem additive_van_der_corput {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ 1) (hcor : VanishingAdditiveCorrelations a) :
    Tendsto (additiveMean a) atTop (𝓝 0) := by
  have hwindow : Tendsto (fun H : ℕ => Real.sqrt (H : ℝ) / (H : ℝ)) atTop (𝓝 0) := by
    have ht := tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
    convert ht using 1
    funext H
    exact Real.sqrt_div_self
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero]
  apply tendsto_order.mpr
  constructor
  · intro ε hε
    exact Eventually.of_forall fun N => lt_of_lt_of_le hε (norm_nonneg _)
  · intro ε hε
    have hw := hwindow.eventually (gt_mem_nhds hε)
    obtain ⟨H, hlimit, hH⟩ := (hw.and (eventually_gt_atTop (0 : ℕ))).exists
    let U : ℕ → ℝ := fun N => 2 * (H : ℝ) / (N : ℝ) +
      Real.sqrt ((H : ℝ) + additiveOffDiagonalMass a H N / N) / H
    have hU : Tendsto U atTop (𝓝 (Real.sqrt (H : ℝ) / H)) := by
      have ht := additiveOffDiagonalMass_tendsto ha hcor H
      have hs := ((tendsto_const_nhds (x := (H : ℝ))).add ht).sqrt
      simpa only [add_zero, zero_add] using
        (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (2 * (H : ℝ))).add (hs.div_const H)
    filter_upwards [hU.eventually (gt_mem_nhds hlimit), eventually_gt_atTop (0 : ℕ)] with N hUN hN
    exact (normalized_additive_van_der_corput ha hH hN).trans_lt hUN


theorem additiveCorrelation_mul_const (c : ℂ) (a : ℕ → ℂ) (h N : ℕ) :
    additiveCorrelation (fun n => c * a n) h N =
      (c * star c) * additiveCorrelation a h N := by
  unfold additiveCorrelation
  rw [mul_sum]
  apply sum_congr rfl
  intro n hn
  rw [star_mul]
  ring

theorem additiveMean_mul_const (c : ℂ) (a : ℕ → ℂ) (N : ℕ) :
    additiveMean (fun n => c * a n) N = c * additiveMean a N := by
  unfold additiveMean
  rw [← mul_div_assoc, mul_sum]

theorem VanishingAdditiveCorrelations.mul_const {a : ℕ → ℂ}
    (h : VanishingAdditiveCorrelations a) (c : ℂ) :
    VanishingAdditiveCorrelations (fun n => c * a n) := by
  intro k hk
  have ht := (h k hk).const_mul (c * star c)
  simpa only [mul_zero, additiveCorrelation_mul_const, mul_div_assoc] using ht

/-- The same criterion for any sequence bounded by a fixed positive constant. -/
theorem additive_van_der_corput_of_bounded_sequence {a : ℕ → ℂ} {C : ℝ}
    (hC : 0 < C) (ha : ∀ n, ‖a n‖ ≤ C) (hcor : VanishingAdditiveCorrelations a) :
    Tendsto (additiveMean a) atTop (𝓝 0) := by
  let c : ℂ := (C : ℂ)⁻¹
  have hscaled : ∀ n, ‖c * a n‖ ≤ 1 := by
    intro n
    dsimp [c]
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC]
    rw [← div_eq_inv_mul]
    exact (div_le_one hC).mpr (ha n)
  have ht := (additive_van_der_corput hscaled (hcor.mul_const c)).const_mul (C : ℂ)
  have hCc : (C : ℂ) * c = 1 := by
    exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt hC))
  have hid : (fun N => (C : ℂ) * additiveMean (fun n => c * a n) N) = additiveMean a := by
    funext N
    rw [additiveMean_mul_const, ← mul_assoc, hCc, one_mul]
  simpa only [hid, mul_zero] using ht

end
end RankCertificates.ArithmeticOrthogonality
