module

public import RankCertificates.ExtractionBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section

namespace RankCertificates.AnalyticExtraction

open Filter Asymptotics

set_option maxHeartbeats 800000

/-- The exact finite prime-power mass bound, with its natural casts exposed. -/
noncomputable def primePowerError (B X : ℕ) : ℝ :=
  (12 * (((Nat.sqrt X + 1) * (Nat.log 2 X + 1)) * (2 * B + 1)) : ℕ) *
    (Real.log X) ^ 12

noncomputable def linearError (k B X : ℕ) : ℝ :=
  ((k * (2 * B + 1) : ℕ) : ℝ) * (Real.log X) ^ 12

theorem primePowerError_nonneg (B X : ℕ) : 0 ≤ primePowerError B X := by
  unfold primePowerError
  positivity

theorem linearError_nonneg (k B X : ℕ) : 0 ≤ linearError k B X := by
  unfold linearError
  positivity

theorem nat_sqrt_le_real_sqrt (X : ℕ) : (Nat.sqrt X : ℝ) ≤ Real.sqrt X := by
  apply (Real.le_sqrt (by positivity) (by positivity)).mpr
  exact_mod_cast Nat.sqrt_le' X

private noncomputable def logConstant : ℝ := (Real.log 2)⁻¹ + 1

private theorem logConstant_pos : 0 < logConstant := by
  have h : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold logConstant
  positivity

private theorem nat_log_factor_le {X : ℕ} (hlog : 1 ≤ Real.log X) :
    (Nat.log 2 X : ℝ) + 1 ≤ logConstant * Real.log X := by
  have h := Real.natLog_le_logb X 2
  simp only [Real.logb, Nat.cast_ofNat] at h
  unfold logConstant
  rw [div_eq_mul_inv] at h
  nlinarith

private theorem smoothPowerError_isLittleO :
    (fun x : ℝ => x * Real.sqrt x * (Real.log x) ^ 13) =o[atTop]
      (fun x : ℝ => x ^ 2) := by
  have hlog : (fun x : ℝ => (Real.log x) ^ 13) =o[atTop] Real.sqrt := by
    have h := isLittleO_log_rpow_rpow_atTop ((13 : ℕ) : ℝ)
      (by norm_num : 0 < (1 / 2 : ℝ))
    have h' : (fun x : ℝ => (Real.log x) ^ 13) =o[atTop]
        (fun x : ℝ => x ^ (1 / 2 : ℝ)) :=
      h.congr_left (fun x => Real.rpow_natCast (Real.log x) 13)
    exact h'.congr_right (fun x => (Real.sqrt_eq_rpow x).symm)
  have h := hlog.mul_isBigO (isBigO_refl (fun x : ℝ => x * Real.sqrt x) atTop)
  refine h.congr' (Eventually.of_forall (fun x => by ring)) ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  have hs := Real.sq_sqrt hx
  nlinarith

private theorem cap_tendsto (C : ℕ) (hC : 1 ≤ C) :
    Tendsto (fun B : ℕ => ((C * (B + 1) : ℕ) : ℝ)) atTop atTop := by
  have hc : 0 < (C : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hC)
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_mul_atTop hc

private theorem cap_square_isBigO (C : ℕ) :
    (fun B : ℕ => ((C * (B + 1) : ℕ) : ℝ) ^ 2) =O[atTop]
      (fun B : ℕ => (B : ℝ) ^ 2) := by
  apply IsBigO.of_bound (4 * (C : ℝ) ^ 2)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with B hB
  have hb : 1 ≤ (B : ℝ) := by exact_mod_cast hB
  simp only [Real.norm_eq_abs, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    abs_of_nonneg (sq_nonneg ((C : ℝ) * (B + 1))), abs_of_nonneg (sq_nonneg (B : ℝ))]
  have hs : ((B : ℝ) + 1) ^ 2 ≤ 4 * (B : ℝ) ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg (C : ℝ))
  nlinarith

private theorem primePowerError_le_smooth (B X : ℕ)
    (hX : 1 ≤ X) (hB : (2 * B + 1 : ℝ) ≤ 2 * X)
    (hlog : 1 ≤ Real.log X) :
    primePowerError B X ≤ (48 * logConstant) *
      ((X : ℝ) * Real.sqrt X * (Real.log X) ^ 13) := by
  have hx : 1 ≤ (X : ℝ) := by exact_mod_cast hX
  have hs : (Nat.sqrt X : ℝ) + 1 ≤ 2 * Real.sqrt X := by
    have h1 := (Real.one_le_sqrt).mpr hx
    have h2 := nat_sqrt_le_real_sqrt X
    linarith
  have hl := nat_log_factor_le hlog
  have hl0 : 0 ≤ Real.log X := by linarith
  have hk := logConstant_pos
  unfold primePowerError
  push_cast
  calc
    12 * (((Nat.sqrt X : ℝ) + 1) * ((Nat.log 2 X : ℝ) + 1) *
        (2 * (B : ℝ) + 1)) * Real.log X ^ 12 ≤
      12 * ((2 * Real.sqrt X) * (logConstant * Real.log X) *
        (2 * (X : ℝ))) * Real.log X ^ 12 := by
      gcongr
    _ = (48 * logConstant) * ((X : ℝ) * Real.sqrt X * Real.log X ^ 13) := by ring

/-- The proved finite prime-power error is o(B²) for a fixed linear output cap. -/
theorem primePowerError_isLittleO (C : ℕ) (hC : 1 ≤ C) :
    (fun B : ℕ => primePowerError B (C * (B + 1))) =o[atTop]
      (fun B : ℕ => (B : ℝ) ^ 2) := by
  have ht := cap_tendsto C hC
  have hs := smoothPowerError_isLittleO.comp_tendsto ht
  have hs' := hs.trans_isBigO (cap_square_isBigO C)
  have hb : (fun B : ℕ => primePowerError B (C * (B + 1))) =O[atTop]
      (fun B : ℕ => ((C * (B + 1) : ℕ) : ℝ) * Real.sqrt ((C * (B + 1) : ℕ) : ℝ) *
        Real.log ((C * (B + 1) : ℕ) : ℝ) ^ 13) := by
    apply IsBigO.of_bound (48 * logConstant)
    filter_upwards [(Real.tendsto_log_atTop.comp ht).eventually_ge_atTop 1] with B hlog
    change 1 ≤ Real.log ((C * (B + 1) : ℕ) : ℝ) at hlog
    have hx : 1 ≤ C * (B + 1) := Nat.succ_le_of_lt
      (Nat.mul_pos (by omega) (Nat.succ_pos B))
    have hb : (2 * B + 1 : ℝ) ≤ 2 * (C * (B + 1) : ℕ) := by
      have hc : 1 ≤ (C : ℝ) := by exact_mod_cast hC
      push_cast
      nlinarith [show 0 ≤ (B : ℝ) from Nat.cast_nonneg B]
    have hg0 : 0 ≤ ((C * (B + 1) : ℕ) : ℝ) * Real.sqrt ((C * (B + 1) : ℕ) : ℝ) *
        Real.log ((C * (B + 1) : ℕ) : ℝ) ^ 13 := by
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))
        (pow_nonneg (by linarith) _)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (primePowerError_nonneg _ _),
      abs_of_nonneg hg0] using primePowerError_le_smooth B _ hx hb hlog
  exact hb.trans_isLittleO hs'

private theorem smoothLinearError_isLittleO :
    (fun x : ℝ => x * (Real.log x) ^ 12) =o[atTop]
      (fun x : ℝ => x ^ 2) := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := 12)).mul_isBigO
    (isBigO_refl (id : ℝ → ℝ) atTop)
  simpa only [id_eq, pow_two, mul_comm] using h

/-- Weighted exclusions lying on finitely many affine lines are o(B²). -/
theorem linearError_isLittleO (k C : ℕ) (hC : 1 ≤ C) :
    (fun B : ℕ => linearError k B (C * (B + 1))) =o[atTop]
      (fun B : ℕ => (B : ℝ) ^ 2) := by
  have ht := cap_tendsto C hC
  have hs := (smoothLinearError_isLittleO.comp_tendsto ht).trans_isBigO
    (cap_square_isBigO C)
  have hb : (fun B : ℕ => linearError k B (C * (B + 1))) =O[atTop]
      (fun B : ℕ => ((C * (B + 1) : ℕ) : ℝ) *
        Real.log ((C * (B + 1) : ℕ) : ℝ) ^ 12) := by
    apply IsBigO.of_bound (2 * (k : ℝ))
    filter_upwards [] with B
    have hB : (2 * B + 1 : ℝ) ≤ 2 * ((C * (B + 1) : ℕ) : ℝ) := by
      have hc : 1 ≤ (C : ℝ) := by exact_mod_cast hC
      push_cast
      nlinarith [show 0 ≤ (B : ℝ) from Nat.cast_nonneg B]
    have hg0 : 0 ≤ ((C * (B + 1) : ℕ) : ℝ) *
        Real.log ((C * (B + 1) : ℕ) : ℝ) ^ 12 := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (linearError_nonneg _ _ _),
      abs_of_nonneg hg0]
    unfold linearError
    push_cast
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hB
    calc
      (k : ℝ) * (2 * (B : ℝ) + 1) * Real.log ((C : ℝ) * (B + 1)) ^ 12 ≤
        (k : ℝ) * (2 * ((C : ℝ) * (B + 1))) *
          Real.log ((C : ℝ) * (B + 1)) ^ 12 := by gcongr
      _ = 2 * (k : ℝ) * (((C : ℝ) * (B + 1)) *
          Real.log ((C : ℝ) * (B + 1)) ^ 12) := by ring
  exact hb.trans_isLittleO hs

theorem primePowerError_mono (B : ℕ) {X Y : ℕ} (hX : 1 ≤ X) (hXY : X ≤ Y) :
    primePowerError B X ≤ primePowerError B Y := by
  have hs := Nat.sqrt_le_sqrt hXY
  have hl := Nat.log_mono_right (b := 2) hXY
  have hr : Real.log X ≤ Real.log Y :=
    Real.log_le_log (by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hX))
      (by exact_mod_cast hXY)
  have hr0 : 0 ≤ Real.log X := Real.log_nonneg (by exact_mod_cast hX)
  unfold primePowerError
  gcongr

/-- The same negligible error bound applies to any eventually smaller output cap. -/
theorem primePowerError_isLittleO_of_eventually_le (C : ℕ) (hC : 1 ≤ C)
    (X : ℕ → ℕ) (hX : ∀ᶠ B in atTop, 1 ≤ X B)
    (hcap : ∀ᶠ B in atTop, X B ≤ C * (B + 1)) :
    (fun B : ℕ => primePowerError B (X B)) =o[atTop]
      (fun B : ℕ => (B : ℝ) ^ 2) := by
  have hdom : (fun B : ℕ => primePowerError B (X B)) =O[atTop]
      (fun B : ℕ => primePowerError B (C * (B + 1))) := by
    apply IsBigO.of_norm_eventuallyLE
    filter_upwards [hX, hcap] with B hx hc
    rw [Real.norm_eq_abs, abs_of_nonneg (primePowerError_nonneg _ _)]
    exact primePowerError_mono B hx hc
  exact hdom.trans_isLittleO (primePowerError_isLittleO C hC)

/-- Actual mass at nonprime outputs is o(B²), with no prime-counting assumption. -/
theorem nonprimePattern_mass_isLittleO (ψ : Fin 12 → IntegerAffine)
    (C : ℕ) (hC : 1 ≤ C)
    (hψ : ∀ i, (ψ i).a ≠ 0 ∨ (ψ i).b ≠ 0)
    (hbound : ∀ B z, z ∈ box B → ∀ i, ((ψ i).eval z).toNat ≤ C * (B + 1)) :
    (fun B : ℕ => ∑ z ∈ nonprimePatternSupport B ψ, patternWeight ψ z) =o[atTop]
      (fun B : ℕ => (B : ℝ) ^ 2) := by
  have hdom : (fun B : ℕ => ∑ z ∈ nonprimePatternSupport B ψ, patternWeight ψ z) =O[atTop]
      (fun B : ℕ => primePowerError B (C * (B + 1))) := by
    apply IsBigO.of_norm_le
    intro B
    have hsum : 0 ≤ ∑ z ∈ nonprimePatternSupport B ψ, patternWeight ψ z :=
      Finset.sum_nonneg (fun _ _ => patternWeight_nonnegative _ _)
    rw [Real.norm_eq_abs, abs_of_nonneg hsum]
    have hx : 1 ≤ C * (B + 1) := Nat.succ_le_of_lt
      (Nat.mul_pos (by omega) (Nat.succ_pos B))
    exact nonprimePattern_mass_le B _ ψ hx hψ (hbound B)
  exact hdom.trans_isLittleO (primePowerError_isLittleO C hC)

/-- A positive quadratic main term implies the explicit lower bound used
by extraction. The main-term asymptotic remains a supplied hypothesis. -/
theorem eventually_quadratic_lower_of_isLittleO (A : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (hA : (fun B : ℕ => A B - c * (B : ℝ) ^ 2) =o[atTop]
      (fun B : ℕ => (B : ℝ) ^ 2)) :
    ∀ᶠ B : ℕ in atTop, c / 2 * (B : ℝ) ^ 2 ≤ A B := by
  filter_upwards [hA.bound (by positivity : 0 < c / 2)] with B hB
  simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (B : ℝ))] at hB
  have hlo := (abs_le.mp hB).1
  linarith

end RankCertificates.AnalyticExtraction
