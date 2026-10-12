module

public import RankCertificates.ExtractionBounds

@[expose] public section

namespace RankCertificates.AnalyticExtraction

open scoped BigOperators

/-- The actual weight on any finite subset of the bounded square. -/
theorem patternWeight_sum_le_card_mul_log (B X : ℕ)
    (ψ : Fin 12 → IntegerAffine) (S : Finset (ℤ × ℤ))
    (hS : S ⊆ box B) (hX : 1 ≤ X)
    (hbound : ∀ z ∈ box B, ∀ i, ((ψ i).eval z).toNat ≤ X) :
    ∑ z ∈ S, patternWeight ψ z ≤ (S.card : ℝ) * (Real.log X) ^ 12 := by
  calc
    _ ≤ ∑ _z ∈ S, (Real.log X) ^ 12 := by
      apply Finset.sum_le_sum
      intro z hz
      exact patternWeight_le_log_power ψ z hX (hbound z (hS hz))
    _ = _ := by simp

noncomputable def finiteValueSupport (B : ℕ) (ψ : Fin 12 → IntegerAffine)
    (Q : Finset ℤ) : Finset (ℤ × ℤ) :=
  Finset.univ.biUnion (fun i => (box B).filter (fun z => (ψ i).eval z ∈ Q))

theorem mem_finiteValueSupport (B : ℕ) (ψ : Fin 12 → IntegerAffine)
    (Q : Finset ℤ) (z : ℤ × ℤ) :
    z ∈ finiteValueSupport B ψ Q ↔ z ∈ box B ∧ ∃ i, (ψ i).eval z ∈ Q := by
  classical
  simp only [finiteValueSupport, Finset.mem_biUnion, Finset.mem_univ,
    true_and, Finset.mem_filter]
  aesop

theorem finiteValueSupport_card_le (B : ℕ) (ψ : Fin 12 → IntegerAffine)
    (Q : Finset ℤ) (hψ : ∀ i, (ψ i).a ≠ 0 ∨ (ψ i).b ≠ 0) :
    (finiteValueSupport B ψ Q).card ≤ 12 * Q.card * (2 * B + 1) := by
  classical
  have h := Finset.card_biUnion_le_card_mul Finset.univ
    (fun i : Fin 12 => (box B).filter (fun z => (ψ i).eval z ∈ Q))
    (Q.card * (2 * B + 1)) (fun i _ => values_card_le B (ψ i) Q (hψ i))
  simpa only [finiteValueSupport, Finset.card_univ, Fintype.card_fin,
    Nat.mul_assoc] using h

theorem finiteValue_mass_le (B X : ℕ) (ψ : Fin 12 → IntegerAffine)
    (Q : Finset ℤ) (hX : 1 ≤ X)
    (hψ : ∀ i, (ψ i).a ≠ 0 ∨ (ψ i).b ≠ 0)
    (hbound : ∀ z ∈ box B, ∀ i, ((ψ i).eval z).toNat ≤ X) :
    ∑ z ∈ finiteValueSupport B ψ Q, patternWeight ψ z ≤
      (12 * Q.card * (2 * B + 1) : ℕ) * (Real.log X) ^ 12 := by
  apply (patternWeight_sum_le_card_mul_log B X ψ _
    (fun z hz => ((mem_finiteValueSupport B ψ Q z).mp hz).1) hX hbound).trans
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast finiteValueSupport_card_le B ψ Q hψ) (by positivity)

noncomputable def diagonalSupport (B : ℕ) (ψ : Fin 12 → IntegerAffine) :
    Finset (ℤ × ℤ) :=
  Finset.univ.biUnion (fun i : Fin 12 =>
    (Finset.univ.filter (fun j : Fin 12 => i ≠ j)).biUnion
      (fun j => (box B).filter (fun z => (ψ i).eval z = (ψ j).eval z)))

theorem mem_diagonalSupport (B : ℕ) (ψ : Fin 12 → IntegerAffine) (z : ℤ × ℤ) :
    z ∈ diagonalSupport B ψ ↔
      z ∈ box B ∧ ∃ i j, i ≠ j ∧ (ψ i).eval z = (ψ j).eval z := by
  classical
  simp only [diagonalSupport, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_filter]
  aesop

theorem diagonalSupport_card_le (B : ℕ) (ψ : Fin 12 → IntegerAffine)
    (hparts : ∀ i j, i ≠ j → (ψ i).a ≠ (ψ j).a ∨ (ψ i).b ≠ (ψ j).b) :
    (diagonalSupport B ψ).card ≤ 144 * (2 * B + 1) := by
  classical
  have hi (i : Fin 12) :
      ((Finset.univ.filter (fun j : Fin 12 => i ≠ j)).biUnion
        (fun j => (box B).filter (fun z => (ψ i).eval z = (ψ j).eval z))).card ≤
        12 * (2 * B + 1) := by
    have h := Finset.card_biUnion_le_card_mul
      (Finset.univ.filter (fun j : Fin 12 => i ≠ j))
      (fun j => (box B).filter (fun z => (ψ i).eval z = (ψ j).eval z))
      (2 * B + 1) (fun j hj => diagonal_card_le B (ψ i) (ψ j)
        (hparts i j (Finset.mem_filter.mp hj).2))
    exact h.trans (Nat.mul_le_mul_right _ (by
      simpa using (Finset.card_filter_le Finset.univ (fun j : Fin 12 => i ≠ j))))
  have h := Finset.card_biUnion_le_card_mul Finset.univ _
    (12 * (2 * B + 1)) (fun i _ => hi i)
  simpa only [diagonalSupport, Finset.card_univ, Fintype.card_fin,
    ← Nat.mul_assoc] using h

theorem diagonal_mass_le (B X : ℕ) (ψ : Fin 12 → IntegerAffine) (hX : 1 ≤ X)
    (hparts : ∀ i j, i ≠ j → (ψ i).a ≠ (ψ j).a ∨ (ψ i).b ≠ (ψ j).b)
    (hbound : ∀ z ∈ box B, ∀ i, ((ψ i).eval z).toNat ≤ X) :
    ∑ z ∈ diagonalSupport B ψ, patternWeight ψ z ≤
      (144 * (2 * B + 1) : ℕ) * (Real.log X) ^ 12 := by
  apply (patternWeight_sum_le_card_mul_log B X ψ _
    (fun z hz => ((mem_diagonalSupport B ψ z).mp hz).1) hX hbound).trans
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast diagonalSupport_card_le B ψ hparts) (by positivity)

noncomputable def affineLineSupport {ι : Type*} [DecidableEq ι]
    (B : ℕ) (I : Finset ι) (θ : ι → IntegerAffine) : Finset (ℤ × ℤ) :=
  I.biUnion (fun i => level B (θ i) 0)

theorem mem_affineLineSupport {ι : Type*} [DecidableEq ι]
    (B : ℕ) (I : Finset ι) (θ : ι → IntegerAffine) (z : ℤ × ℤ) :
    z ∈ affineLineSupport B I θ ↔ z ∈ box B ∧ ∃ i ∈ I, (θ i).eval z = 0 := by
  classical
  simp only [affineLineSupport, Finset.mem_biUnion, level, Finset.mem_filter]
  aesop

theorem affineLineSupport_card_le {ι : Type*} [DecidableEq ι]
    (B : ℕ) (I : Finset ι) (θ : ι → IntegerAffine)
    (hθ : ∀ i ∈ I, (θ i).a ≠ 0 ∨ (θ i).b ≠ 0) :
    (affineLineSupport B I θ).card ≤ I.card * (2 * B + 1) :=
  Finset.card_biUnion_le_card_mul I _ _ (fun i hi => level_card_le B (θ i) 0 (hθ i hi))

theorem affineLine_mass_le {ι : Type*} [DecidableEq ι]
    (B X : ℕ) (ψ : Fin 12 → IntegerAffine) (I : Finset ι) (θ : ι → IntegerAffine)
    (hX : 1 ≤ X) (hθ : ∀ i ∈ I, (θ i).a ≠ 0 ∨ (θ i).b ≠ 0)
    (hbound : ∀ z ∈ box B, ∀ i, ((ψ i).eval z).toNat ≤ X) :
    ∑ z ∈ affineLineSupport B I θ, patternWeight ψ z ≤
      (I.card * (2 * B + 1) : ℕ) * (Real.log X) ^ 12 := by
  apply (patternWeight_sum_le_card_mul_log B X ψ _
    (fun z hz => ((mem_affineLineSupport B I θ z).mp hz).1) hX hbound).trans
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast affineLineSupport_card_le B I θ hθ) (by positivity)

end RankCertificates.AnalyticExtraction
