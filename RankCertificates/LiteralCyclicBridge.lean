module

public import RankCertificates.LiteralFiniteField

@[expose] public section

namespace RankCertificates.AnalyticExtraction

open Filter
open scoped BigOperators

theorem sector5_window {T : ℕ} {z : ℤ × ℤ} (hz : z ∈ positiveSector5 T) :
    z ∈ residueWindow (embeddingPrime 21 T) := by
  apply box_nonnegative_point_in_window (positiveSector5_subset_box T hz)
  · simp only [positiveSector5, Finset.mem_product, Finset.mem_Icc] at hz
    omega
  · simp only [positiveSector5, Finset.mem_product, Finset.mem_Icc] at hz
    omega

theorem sector6_window {T : ℕ} {z : ℤ × ℤ} (hz : z ∈ positiveSector6 T) :
    z ∈ residueWindow (embeddingPrime 61 T) := by
  apply box_nonnegative_point_in_window (positiveSector6_subset_box T hz)
  · simp only [positiveSector6, Finset.mem_product, Finset.mem_Icc] at hz
    omega
  · simp only [positiveSector6, Finset.mem_product, Finset.mem_Icc] at hz
    omega

theorem sector7_window {T : ℕ} {z : ℤ × ℤ} (hz : z ∈ positiveSector7 T) :
    z ∈ residueWindow (embeddingPrime 8001 T) := by
  apply box_nonnegative_point_in_window (positiveSector7_subset_box T hz)
  · simp only [positiveSector7, Finset.mem_product, Finset.mem_Icc] at hz
    omega
  · simp only [positiveSector7, Finset.mem_product, Finset.mem_Icc] at hz
    omega

theorem sector5_mass_eq_cyclic (T : ℕ) (hT : 1 ≤ T) :
    (∑ z ∈ positiveSector5 T, patternWeight system5 z) =
      (embeddingPrime 21 T : ℝ) ^ 2 *
        cyclicSectorMean system5 (embeddingPrime 21 T) (positiveSector5 T) := by
  apply sector_mass_eq_p_sq_mul_mean system5 _ (embeddingPrime_properties 21 T).1.ne_zero
    _ (fun z hz => sector5_window hz)
  · intro z hz i
    have h := positiveSector5_output_lower hT hz i
    exact (by positivity : (0 : ℤ) ≤ T).trans h
  · intro z hz i
    apply bounded_nonnegative_output_lt_prime
    · exact (by positivity : (0 : ℤ) ≤ T).trans (positiveSector5_output_lower hT hz i)
    · exact system5_output_bound (positiveSector5_subset_box T hz) i

theorem sector6_mass_eq_cyclic (T : ℕ) (hT : 1 ≤ T) :
    (∑ z ∈ positiveSector6 T, patternWeight system6 z) =
      (embeddingPrime 61 T : ℝ) ^ 2 *
        cyclicSectorMean system6 (embeddingPrime 61 T) (positiveSector6 T) := by
  apply sector_mass_eq_p_sq_mul_mean system6 _ (embeddingPrime_properties 61 T).1.ne_zero
    _ (fun z hz => sector6_window hz)
  · intro z hz i
    exact (by positivity : (0 : ℤ) ≤ T).trans (positiveSector6_output_lower hT hz i)
  · intro z hz i
    apply bounded_nonnegative_output_lt_prime
    · exact (by positivity : (0 : ℤ) ≤ T).trans (positiveSector6_output_lower hT hz i)
    · exact system6_output_bound (positiveSector6_subset_box T hz) i

theorem sector7_mass_eq_cyclic (T : ℕ) (hT : 1 ≤ T) :
    (∑ z ∈ positiveSector7 T, patternWeight system7 z) =
      (embeddingPrime 8001 T : ℝ) ^ 2 *
        cyclicSectorMean system7 (embeddingPrime 8001 T) (positiveSector7 T) := by
  apply sector_mass_eq_p_sq_mul_mean system7 _ (embeddingPrime_properties 8001 T).1.ne_zero
    _ (fun z hz => sector7_window hz)
  · intro z hz i
    exact (by positivity : (0 : ℤ) ≤ T).trans (positiveSector7_output_lower hT hz i)
  · intro z hz i
    apply bounded_nonnegative_output_lt_prime
    · exact (by positivity : (0 : ℤ) ≤ T).trans (positiveSector7_output_lower hT hz i)
    · exact system7_output_bound (positiveSector7_subset_box T hz) i

/-- A genuine lower bound for the masked actual twelve-fold Λ mean in the
selected prime fields. No declaration here proves this counting input. -/
def HasCyclicSectorMass (ψ : Fin 12 → IntegerAffine)
    (R : ℕ → Finset (ℤ × ℤ)) (K : ℕ) : Prop :=
  ∃ η : ℝ, 0 < η ∧ ∀ᶠ T : ℕ in atTop,
    η ≤ cyclicSectorMean ψ (embeddingPrime K T) (R T)

theorem HasCyclicSectorMass.quadraticMass {ψ : Fin 12 → IntegerAffine}
    {R : ℕ → Finset (ℤ × ℤ)} {K : ℕ} (hK : 1 ≤ K)
    (heq : ∀ T : ℕ, 1 ≤ T →
      (∑ z ∈ R T, patternWeight ψ z) = (embeddingPrime K T : ℝ) ^ 2 *
        cyclicSectorMean ψ (embeddingPrime K T) (R T))
    (h : HasCyclicSectorMass ψ R K) : HasQuadraticMangoldtMass ψ R := by
  obtain ⟨η, hη, hlo⟩ := h
  refine ⟨η, hη, ?_⟩
  filter_upwards [hlo, eventually_ge_atTop (1 : ℕ)] with T hmean hT
  rw [heq T hT]
  have hsize : T ≤ embeddingPrime K T :=
    (Nat.le_mul_of_pos_left T hK).trans (embeddingPrime_gt_box K T).le
  have hsize' : (T : ℝ) ≤ embeddingPrime K T := by exact_mod_cast hsize
  have hsquares : (T : ℝ) ^ 2 ≤ (embeddingPrime K T : ℝ) ^ 2 := by gcongr
  calc
    η * (T : ℝ) ^ 2 ≤ η * (embeddingPrime K T : ℝ) ^ 2 := by gcongr
    _ = (embeddingPrime K T : ℝ) ^ 2 * η := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmean (sq_nonneg _)

theorem rank5_infinitude_of_cyclicSectorMass
    (h : HasCyclicSectorMass system5 positiveSector5 21) : InfinitelyManyExactRank 5 :=
  rank5_infinitude_of_quadraticMangoldtMass
    (h.quadraticMass (by norm_num) sector5_mass_eq_cyclic)

theorem rank6_infinitude_of_cyclicSectorMass
    (h : HasCyclicSectorMass system6 positiveSector6 61) : InfinitelyManyExactRank 6 :=
  rank6_infinitude_of_quadraticMangoldtMass
    (h.quadraticMass (by norm_num) sector6_mass_eq_cyclic)

theorem rank7_infinitude_of_cyclicSectorMass
    (h : HasCyclicSectorMass system7 positiveSector7 8001) : InfinitelyManyExactRank 7 :=
  rank7_infinitude_of_quadraticMangoldtMass
    (h.quadraticMass (by norm_num) sector7_mass_eq_cyclic)

theorem ranksFiveThroughSeven_of_cyclicSectorMass
    (h5 : HasCyclicSectorMass system5 positiveSector5 21)
    (h6 : HasCyclicSectorMass system6 positiveSector6 61)
    (h7 : HasCyclicSectorMass system7 positiveSector7 8001) : RanksFiveThroughSeven :=
  ⟨rank5_infinitude_of_cyclicSectorMass h5,
    rank6_infinitude_of_cyclicSectorMass h6,
    rank7_infinitude_of_cyclicSectorMass h7⟩

end RankCertificates.AnalyticExtraction
