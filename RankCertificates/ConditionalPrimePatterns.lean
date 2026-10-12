module

public import RankCertificates.LiteralPrimeBridge
public import RankCertificates.PrimeAsymptoticBridge
public import RankCertificates.SingularSeries

/-!
A conditional use of the published finite-complexity theorem for linear
forms in primes. The external analytic theorem is an explicit proposition
parameter. It contains no elliptic-curve, rank, or literal-family fields.
Every instance obligation and the subsequent rank-infinitude deduction
are proved from the existing arithmetic and geometric certificates.
-/

@[expose] public section

namespace RankCertificates.ConditionalPrimePatterns

open PrimePatterns AnalyticExtraction SingularSeries Filter Asymptotics
open scoped BigOperators

/-- The integer points in T times a fixed closed rectangle of area one. -/
def unitRectangle (u v : ℤ) (T : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (u * (T : ℤ)) ((u + 1) * T) ×ˢ
    Finset.Icc (v * (T : ℤ)) ((v + 1) * T)

/-- A restricted formulation of the standard finite-complexity prime
asymptotic on positive unit rectangles. Its singular-series factors are
the actual corrected residue densities, not unspecified constants.

This proposition is not asserted here. A proof of it is the sole external
analytic theorem input. Nonparallel binary gradients have finite complexity;
all coefficients and rectangle corners remain fixed as T tends to infinity.
Uniform linear positivity removes the archimedean sign restriction, and
the width-one rectangle contributes the area factor one. -/
def FiniteComplexityPrimeAsymptotic : Prop :=
  ∀ (fs : Fin 12 → AffineForm) (u v : ℤ),
    (∀ i, (fs i).a ≠ 0 ∨ (fs i).b ≠ 0) →
    (∀ i j, i ≠ j → (fs i).a * (fs j).b - (fs i).b * (fs j).a ≠ 0) →
    (∀ p : ℕ, p.Prime → Avoids fs p) →
    (∀ T : ℕ, 1 ≤ T → ∀ z ∈ unitRectangle u v T, ∀ i,
      (T : ℤ) ≤ (fs i).eval z.1 z.2) →
    ∀ σ : ℝ, HasProd (outputsLocalFactor fs) σ →
      (fun T : ℕ => (∑ z ∈ unitRectangle u v T,
        patternWeight (fromAffine ∘ fs) z) - σ * (T : ℝ) ^ 2)
        =o[atTop] (fun T : ℕ => (T : ℝ) ^ 2)

/-- A positive singular product converts the external asymptotic to the
actual weighted-mass input consumed by the checked extraction theorem. -/
theorem FiniteComplexityPrimeAsymptotic.quadraticMass
    (hGTZ : FiniteComplexityPrimeAsymptotic)
    (fs : Fin 12 → AffineForm) (u v : ℤ)
    (hcoeff : ∀ i, (fs i).a ≠ 0 ∨ (fs i).b ≠ 0)
    (hdet : ∀ i j, i ≠ j → (fs i).a * (fs j).b - (fs i).b * (fs j).a ≠ 0)
    (hlocal : ∀ p : ℕ, p.Prime → Avoids fs p)
    (hpositive : ∀ T : ℕ, 1 ≤ T → ∀ z ∈ unitRectangle u v T, ∀ i,
      (T : ℤ) ≤ (fs i).eval z.1 z.2)
    (σ : ℝ) (hσ : 0 < σ) (hprod : HasProd (outputsLocalFactor fs) σ) :
    HasQuadraticMangoldtMass (fromAffine ∘ fs) (unitRectangle u v) := by
  refine ⟨σ / 2, by positivity, ?_⟩
  exact eventually_quadratic_lower_of_isLittleO
    (fun T => ∑ z ∈ unitRectangle u v T, patternWeight (fromAffine ∘ fs) z)
    σ hσ (hGTZ fs u v hcoeff hdet hlocal hpositive σ hprod)

@[simp] theorem unitRectangle_rank5 (T : ℕ) :
    unitRectangle 20 20 T = positiveSector5 T := by
  norm_num [unitRectangle, positiveSector5]

@[simp] theorem unitRectangle_rank6 (T : ℕ) :
    unitRectangle 60 1 T = positiveSector6 T := by
  norm_num [unitRectangle, positiveSector6]

@[simp] theorem unitRectangle_rank7 (T : ℕ) :
    unitRectangle 8000 1 T = positiveSector7 T := by
  norm_num [unitRectangle, positiveSector7]

/-- The standard theorem input supplies rank five's literal weighted mass;
local admissibility, nonparallelism, positivity and product are certificates. -/
theorem rank5_quadraticMass_of_finiteComplexityPrimeAsymptotic
    (hGTZ : FiniteComplexityPrimeAsymptotic) :
    HasQuadraticMangoldtMass system5 positiveSector5 := by
  obtain ⟨σ, hσ, hprod⟩ := rank5_singularSeries_hasProd_pos
  have hpositive : ∀ T : ℕ, 1 ≤ T → ∀ z ∈ unitRectangle 20 20 T, ∀ i,
      (T : ℤ) ≤ (PrimePatterns.Rank5.outputs i).eval z.1 z.2 := by
    intro T hT z hz i
    exact positiveSector5_output_lower hT (by simpa only [unitRectangle_rank5] using hz) i
  have hmass := hGTZ.quadraticMass
    PrimePatterns.Rank5.outputs 20 20 system5_nonconstant
    PrimePatterns.Rank5.nonparallel_outputs PrimePatterns.Rank5.local_admissibility
    hpositive σ hσ hprod
  have hrect : unitRectangle 20 20 = positiveSector5 := funext unitRectangle_rank5
  rw [hrect] at hmass
  exact hmass

/-- The standard theorem input supplies rank six's literal weighted mass. -/
theorem rank6_quadraticMass_of_finiteComplexityPrimeAsymptotic
    (hGTZ : FiniteComplexityPrimeAsymptotic) :
    HasQuadraticMangoldtMass system6 positiveSector6 := by
  obtain ⟨σ, hσ, hprod⟩ := rank6_singularSeries_hasProd_pos
  have hpositive : ∀ T : ℕ, 1 ≤ T → ∀ z ∈ unitRectangle 60 1 T, ∀ i,
      (T : ℤ) ≤ (PrimePatterns.Rank6.outputs i).eval z.1 z.2 := by
    intro T hT z hz i
    exact positiveSector6_output_lower hT (by simpa only [unitRectangle_rank6] using hz) i
  have hmass := hGTZ.quadraticMass
    PrimePatterns.Rank6.outputs 60 1 system6_nonconstant
    PrimePatterns.Rank6.nonparallel_outputs PrimePatterns.Rank6.local_admissibility
    hpositive σ hσ hprod
  have hrect : unitRectangle 60 1 = positiveSector6 := funext unitRectangle_rank6
  rw [hrect] at hmass
  exact hmass

/-- The standard theorem input supplies rank seven's literal weighted mass. -/
theorem rank7_quadraticMass_of_finiteComplexityPrimeAsymptotic
    (hGTZ : FiniteComplexityPrimeAsymptotic) :
    HasQuadraticMangoldtMass system7 positiveSector7 := by
  obtain ⟨σ, hσ, hprod⟩ := rank7_singularSeries_hasProd_pos
  have hpositive : ∀ T : ℕ, 1 ≤ T → ∀ z ∈ unitRectangle 8000 1 T, ∀ i,
      (T : ℤ) ≤ (PrimePatterns.Rank7.outputs i).eval z.1 z.2 := by
    intro T hT z hz i
    exact positiveSector7_output_lower hT (by simpa only [unitRectangle_rank7] using hz) i
  have hmass := hGTZ.quadraticMass
    PrimePatterns.Rank7.outputs 8000 1 system7_nonconstant
    PrimePatterns.Rank7.nonparallel_outputs PrimePatterns.Rank7.local_admissibility
    hpositive σ hσ hprod
  have hrect : unitRectangle 8000 1 = positiveSector7 := funext unitRectangle_rank7
  rw [hrect] at hmass
  exact hmass

/-- Infinitely many geometric classes of exact ranks five, six and seven,
conditional only on the explicitly stated standard prime asymptotic.
This theorem proves an implication, not the external analytic theorem. -/
theorem ranksFiveThroughSeven_of_finiteComplexityPrimeAsymptotic
    (hGTZ : FiniteComplexityPrimeAsymptotic) : RanksFiveThroughSeven :=
  ranksFiveThroughSeven_of_quadraticMangoldtMass
    (rank5_quadraticMass_of_finiteComplexityPrimeAsymptotic hGTZ)
    (rank6_quadraticMass_of_finiteComplexityPrimeAsymptotic hGTZ)
    (rank7_quadraticMass_of_finiteComplexityPrimeAsymptotic hGTZ)

end RankCertificates.ConditionalPrimePatterns
