module

public import RankCertificates.LiteralPrimeBridge
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.Bertrand

@[expose] public section

namespace RankCertificates.AnalyticExtraction

open scoped BigOperators

/-- Reduction of the actual integer parameter pair. -/
def reducePair (p : ℕ) (z : ℤ × ℤ) : ZMod p × ZMod p := (z.1, z.2)

def IntegerAffine.residueEval (p : ℕ) (ψ : IntegerAffine) (v : ZMod p × ZMod p) : ZMod p :=
  ψ.a * v.1 + ψ.b * v.2 + ψ.c

@[simp] theorem residueEval_reducePair (p : ℕ) (ψ : IntegerAffine) (z : ℤ × ℤ) :
    ψ.residueEval p (reducePair p z) = (ψ.eval z : ZMod p) := by
  simp [IntegerAffine.residueEval, IntegerAffine.eval, reducePair]

/-- The canonical nonnegative representative window, before reduction. -/
def residueWindow (p : ℕ) : Set (ℤ × ℤ) :=
  {z | 0 ≤ z.1 ∧ z.1 < p ∧ 0 ≤ z.2 ∧ z.2 < p}

theorem intCast_val_of_nonnegative_lt (p : ℕ) (x : ℤ)
    (hx : 0 ≤ x) (hxp : x < p) : (x : ZMod p).val = x.toNat := by
  have heq : (x.toNat : ℤ) = x := Int.toNat_of_nonneg hx
  have hNat : x.toNat < p := by omega
  rw [← heq, Int.cast_natCast]
  exact ZMod.val_natCast_of_lt hNat

theorem reducePair_injective_on_window (p : ℕ) :
    Set.InjOn (reducePair p) (residueWindow p) := by
  intro z hz w hw heq
  have h1 := congrArg (fun v : ZMod p × ZMod p => v.1.val) heq
  have h2 := congrArg (fun v : ZMod p × ZMod p => v.2.val) heq
  change (z.1 : ZMod p).val = (w.1 : ZMod p).val at h1
  change (z.2 : ZMod p).val = (w.2 : ZMod p).val at h2
  rw [intCast_val_of_nonnegative_lt p z.1 hz.1 hz.2.1,
    intCast_val_of_nonnegative_lt p w.1 hw.1 hw.2.1] at h1
  rw [intCast_val_of_nonnegative_lt p z.2 hz.2.2.1 hz.2.2.2,
    intCast_val_of_nonnegative_lt p w.2 hw.2.2.1 hw.2.2.2] at h2
  apply Prod.ext
  · exact (Int.toNat_of_nonneg hz.1).symm.trans
      ((congrArg (fun n : ℕ => (n : ℤ)) h1).trans (Int.toNat_of_nonneg hw.1))
  · exact (Int.toNat_of_nonneg hz.2.2.1).symm.trans
      ((congrArg (fun n : ℕ => (n : ℤ)) h2).trans (Int.toNat_of_nonneg hw.2.2.1))

noncomputable def sectorImage (p : ℕ) (R : Finset (ℤ × ℤ)) : Finset (ZMod p × ZMod p) :=
  R.image (reducePair p)

/-- Actual von Mangoldt values of the reduced literal forms. -/
noncomputable def cyclicPatternWeight (ψ : Fin 12 → IntegerAffine) (p : ℕ)
    (v : ZMod p × ZMod p) : ℝ :=
  ∏ i, ArithmeticFunction.vonMangoldt ((ψ i).residueEval p v).val

/-- The full-field normalized mass with the actual sector image as its mask. -/
noncomputable def cyclicSectorMean (ψ : Fin 12 → IntegerAffine) (p : ℕ)
    (R : Finset (ℤ × ℤ)) : ℝ :=
  (∑ v ∈ sectorImage p R, cyclicPatternWeight ψ p v) / (p : ℝ) ^ 2

theorem sectorImage_card (p : ℕ) (R : Finset (ℤ × ℤ))
    (hR : ∀ z ∈ R, z ∈ residueWindow p) : (sectorImage p R).card = R.card := by
  classical
  apply Finset.card_image_iff.mpr
  intro z hz w hw heq
  exact reducePair_injective_on_window p (hR z hz) (hR w hw) heq

theorem cyclicPatternWeight_reducePair (ψ : Fin 12 → IntegerAffine) (p : ℕ)
    (z : ℤ × ℤ) (hpos : ∀ i, 0 ≤ (ψ i).eval z)
    (hcap : ∀ i, (ψ i).eval z < p) :
    cyclicPatternWeight ψ p (reducePair p z) = patternWeight ψ z := by
  unfold cyclicPatternWeight patternWeight
  apply Finset.prod_congr rfl
  intro i hi
  rw [residueEval_reducePair, intCast_val_of_nonnegative_lt p _ (hpos i) (hcap i)]

/-- Exact transport, with all injectivity and absence-of-wrap obligations explicit. -/
theorem sector_mass_eq_cyclic_mass (ψ : Fin 12 → IntegerAffine) (p : ℕ)
    (R : Finset (ℤ × ℤ)) (hR : ∀ z ∈ R, z ∈ residueWindow p)
    (hpos : ∀ z ∈ R, ∀ i, 0 ≤ (ψ i).eval z)
    (hcap : ∀ z ∈ R, ∀ i, (ψ i).eval z < p) :
    (∑ z ∈ R, patternWeight ψ z) =
      ∑ v ∈ sectorImage p R, cyclicPatternWeight ψ p v := by
  classical
  unfold sectorImage
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro z hz
    exact (cyclicPatternWeight_reducePair ψ p z (hpos z hz) (hcap z hz)).symm
  · intro z hz w hw heq
    exact reducePair_injective_on_window p (hR z hz) (hR w hw) heq

theorem sector_mass_eq_p_sq_mul_mean (ψ : Fin 12 → IntegerAffine) (p : ℕ)
    (hp : p ≠ 0) (R : Finset (ℤ × ℤ)) (hR : ∀ z ∈ R, z ∈ residueWindow p)
    (hpos : ∀ z ∈ R, ∀ i, 0 ≤ (ψ i).eval z)
    (hcap : ∀ z ∈ R, ∀ i, (ψ i).eval z < p) :
    (∑ z ∈ R, patternWeight ψ z) = (p : ℝ) ^ 2 * cyclicSectorMean ψ p R := by
  rw [sector_mass_eq_cyclic_mass ψ p R hR hpos hcap]
  unfold cyclicSectorMean
  rw [mul_div_cancel₀]
  exact pow_ne_zero 2 (by exact_mod_cast hp)

/-- A prime modulus just beyond the literal output cap, still linear in T. -/
def embeddingThreshold (K T : ℕ) : ℕ := literalCap * (K * T + 1)

theorem exists_embedding_prime (K T : ℕ) :
    ∃ p : ℕ, p.Prime ∧ embeddingThreshold K T < p ∧
      p ≤ 2 * embeddingThreshold K T := by
  apply Nat.exists_prime_lt_and_le_two_mul
  unfold embeddingThreshold
  exact Nat.mul_ne_zero (by norm_num [literalCap]) (by omega)

noncomputable def embeddingPrime (K T : ℕ) : ℕ :=
  Classical.choose (exists_embedding_prime K T)

theorem embeddingPrime_properties (K T : ℕ) :
    (embeddingPrime K T).Prime ∧ embeddingThreshold K T < embeddingPrime K T ∧
      embeddingPrime K T ≤ 2 * embeddingThreshold K T :=
  Classical.choose_spec (exists_embedding_prime K T)

theorem embeddingPrime_lt_linear (K T : ℕ) (hT : 1 ≤ T) :
    embeddingPrime K T ≤ (2 * literalCap * (K + 1)) * T := by
  have h := (embeddingPrime_properties K T).2.2
  unfold embeddingThreshold at h
  have hh : K * T + 1 ≤ (K + 1) * T := by nlinarith
  calc
    _ ≤ 2 * (literalCap * (K * T + 1)) := h
    _ ≤ 2 * (literalCap * ((K + 1) * T)) := by gcongr
    _ = _ := by ring

theorem embeddingPrime_gt_box (K T : ℕ) : K * T < embeddingPrime K T := by
  have h := (embeddingPrime_properties K T).2.1
  unfold embeddingThreshold at h
  have hcap : 1 ≤ literalCap := by norm_num [literalCap]
  have hbound : K * T < literalCap * (K * T + 1) := by
    calc
      _ < K * T + 1 := by omega
      _ ≤ _ := by simpa using Nat.mul_le_mul_right (K * T + 1) hcap
  exact hbound.trans h

theorem box_nonnegative_point_in_window {K T : ℕ} {z : ℤ × ℤ}
    (hz : z ∈ box (K * T)) (h0x : 0 ≤ z.1) (h0y : 0 ≤ z.2) :
    z ∈ residueWindow (embeddingPrime K T) := by
  have hq : ((K * T : ℕ) : ℤ) < embeddingPrime K T := by
    exact_mod_cast embeddingPrime_gt_box K T
  obtain ⟨hx, hy⟩ := Finset.mem_product.mp hz
  exact ⟨h0x, (Finset.mem_Icc.mp hx).2.trans_lt hq,
    h0y, (Finset.mem_Icc.mp hy).2.trans_lt hq⟩

theorem bounded_nonnegative_output_lt_prime {K T : ℕ} {x : ℤ}
    (hx : 0 ≤ x) (hcap : x.toNat ≤ literalCap * (K * T + 1)) :
    x < embeddingPrime K T := by
  have hq := (embeddingPrime_properties K T).2.1
  unfold embeddingThreshold at hq
  have hh : x.toNat < embeddingPrime K T := hcap.trans_lt hq
  rw [← Int.toNat_of_nonneg hx]
  exact_mod_cast hh

end RankCertificates.AnalyticExtraction
