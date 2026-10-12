module

public import RankCertificates.PrimeExtraction

@[expose] public section

namespace RankCertificates.AnalyticExtraction

open Filter Asymptotics
open scoped BigOperators

/-- A positive main-term asymptotic for the actual twelve-fold von Mangoldt
sum yields infinitely many positive distinct prime tuples, with all prescribed
finite integer values and nonconstant affine lines excluded.
The prime-counting asymptotic is an explicit input to this theorem. -/
theorem primePatternAvoidingLines_infinite_of_scaled_quadratic_asymptotic
    {ι : Type*} [DecidableEq ι]
    (ψ : Fin 12 → IntegerAffine) (Q : Finset ℤ)
    (I : Finset ι) (θ : ι → IntegerAffine)
    (R : ℕ → Finset (ℤ × ℤ)) (C K : ℕ) (c : ℝ)
    (hR : ∀ T, R T ⊆ box (K * T)) (hC : 1 ≤ C) (hK : 1 ≤ K) (hc : 0 < c)
    (hψ : ∀ i, (ψ i).a ≠ 0 ∨ (ψ i).b ≠ 0)
    (hparts : ∀ i j, i ≠ j → (ψ i).a ≠ (ψ j).a ∨ (ψ i).b ≠ (ψ j).b)
    (hθ : ∀ i ∈ I, (θ i).a ≠ 0 ∨ (θ i).b ≠ 0)
    (hbound : ∀ T, ∀ z ∈ box (K * T), ∀ i,
      ((ψ i).eval z).toNat ≤ C * (K * T + 1))
    (hmain : (fun T : ℕ => (∑ z ∈ R T, patternWeight ψ z) - c * (T : ℝ) ^ 2)
      =o[atTop] (fun T : ℕ => (T : ℝ) ^ 2)) :
    {z : ℤ × ℤ | (∃ T, z ∈ R T) ∧ primePatternAvoidingLines ψ Q I θ z}.Infinite := by
  exact primePatternAvoidingLines_infinite_of_scaled_quadratic_lower ψ Q I θ R C K (c / 2)
    hR hC hK (by positivity) hψ hparts hθ hbound
    (eventually_quadratic_lower_of_isLittleO
      (fun T => ∑ z ∈ R T, patternWeight ψ z) c hc hmain)

theorem primePattern_infinite_of_scaled_quadratic_asymptotic
    (ψ : Fin 12 → IntegerAffine) (Q : Finset ℤ)
    (R : ℕ → Finset (ℤ × ℤ)) (C K : ℕ) (c : ℝ)
    (hR : ∀ T, R T ⊆ box (K * T)) (hC : 1 ≤ C) (hK : 1 ≤ K) (hc : 0 < c)
    (hψ : ∀ i, (ψ i).a ≠ 0 ∨ (ψ i).b ≠ 0)
    (hparts : ∀ i j, i ≠ j → (ψ i).a ≠ (ψ j).a ∨ (ψ i).b ≠ (ψ j).b)
    (hbound : ∀ T, ∀ z ∈ box (K * T), ∀ i,
      ((ψ i).eval z).toNat ≤ C * (K * T + 1))
    (hmain : (fun T : ℕ => (∑ z ∈ R T, patternWeight ψ z) - c * (T : ℝ) ^ 2)
      =o[atTop] (fun T : ℕ => (T : ℝ) ^ 2)) :
    {z : ℤ × ℤ | (∃ T, z ∈ R T) ∧ primePattern ψ Q z}.Infinite := by
  exact primePattern_infinite_of_scaled_quadratic_lower ψ Q R C K (c / 2)
    hR hC hK (by positivity) hψ hparts hbound
    (eventually_quadratic_lower_of_isLittleO
      (fun T => ∑ z ∈ R T, patternWeight ψ z) c hc hmain)

end RankCertificates.AnalyticExtraction
