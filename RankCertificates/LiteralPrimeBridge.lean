module

public import RankCertificates.LiteralAffineSystems
public import RankCertificates.PrimeExtraction
public import RankCertificates.InfinitudeReduction

@[expose] public section

namespace RankCertificates.AnalyticExtraction

open Filter
open scoped BigOperators

def excludedPrimeValues (small : List ℕ) : Finset ℤ :=
  small.toFinset.image (fun p : ℕ => (p : ℤ))

/-- Extraction's actual integer prime tuples discharge exactly the hypotheses
of the geometric rank theorems. -/
theorem primePattern_positivePrimeOutputs (ψ : Fin 12 → IntegerAffine)
    (small : List ℕ) (z : ℤ × ℤ)
    (h : primePattern ψ (excludedPrimeValues small) z) :
    PositivePrimeOutputs (fun i => (ψ i).eval z) small := by
  have habs (i : Fin 12) : (((ψ i).eval z).natAbs : ℤ) = (ψ i).eval z :=
    Int.natAbs_of_nonneg (le_of_lt (h.1 i).1)
  have hnat (i : Fin 12) : ((ψ i).eval z).toNat = ((ψ i).eval z).natAbs := by
    have hto := Int.toNat_of_nonneg (le_of_lt (h.1 i).1)
    exact_mod_cast hto.trans (habs i).symm
  refine ⟨fun i => (h.1 i).1, ?_, ?_, ?_⟩
  · intro i
    simpa only [hnat i] using (h.1 i).2.1
  · intro i j hij
    apply h.2
    exact (habs i).symm.trans ((congrArg (fun p : ℕ => (p : ℤ)) hij).trans (habs j))
  · intro i p hp heq
    apply (h.1 i).2.2
    apply Finset.mem_image.mpr
    refine ⟨p, List.mem_toFinset.mpr hp, ?_⟩
    simpa only [heq] using habs i

theorem primePattern_specialization5 {z : ℤ × ℤ}
    (h : primePattern system5 (excludedPrimeValues [2, 3, 5]) z) :
    PrimeSpecialization5 z.1 z.2 := by
  exact primePattern_positivePrimeOutputs system5 [2, 3, 5] z h

theorem primePattern_specialization6 {z : ℤ × ℤ}
    (h : primePattern system6 (excludedPrimeValues [2, 3, 7]) z) :
    PrimeSpecialization6 z.1 z.2 := by
  exact primePattern_positivePrimeOutputs system6 [2, 3, 7] z h

theorem primePattern_specialization7 {z : ℤ × ℤ}
    (h : primePattern system7 (excludedPrimeValues [2, 3, 7, 13]) z) :
    PrimeSpecialization7 z.1 z.2 := by
  exact primePattern_positivePrimeOutputs system7 [2, 3, 7, 13] z h

theorem rank5_infinitude_of_extracted_prime_patterns
    (h : Set.Infinite {z : ℤ × ℤ |
      primePattern system5 (excludedPrimeValues [2, 3, 5]) z}) :
    InfinitelyManyExactRank 5 :=
  rank5_infinitude_of_prime_values (h.mono (fun _ hz => primePattern_specialization5 hz))

theorem rank6_infinitude_of_extracted_prime_patterns
    (h : Set.Infinite {z : ℤ × ℤ |
      primePattern system6 (excludedPrimeValues [2, 3, 7]) z}) :
    InfinitelyManyExactRank 6 :=
  rank6_infinitude_of_prime_values (h.mono (fun _ hz => primePattern_specialization6 hz))

theorem rank7_infinitude_of_extracted_prime_patterns
    (h : Set.Infinite {z : ℤ × ℤ |
      primePattern system7 (excludedPrimeValues [2, 3, 7, 13]) z}) :
    InfinitelyManyExactRank 7 :=
  rank7_infinitude_of_prime_values (h.mono (fun _ hz => primePattern_specialization7 hz))

/-- A positive quadratic lower bound for the actual twelve-fold von Mangoldt
sum. No theorem in this file asserts this analytic supplier unconditionally. -/
def HasQuadraticMangoldtMass (ψ : Fin 12 → IntegerAffine)
    (R : ℕ → Finset (ℤ × ℤ)) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ T : ℕ in atTop,
    c * (T : ℝ) ^ 2 ≤ ∑ z ∈ R T, patternWeight ψ z

theorem rank5_infinitude_of_quadraticMangoldtMass
    (h : HasQuadraticMangoldtMass system5 positiveSector5) :
    InfinitelyManyExactRank 5 := by
  obtain ⟨c, hc, hlo⟩ := h
  have hinf := primePattern_infinite_of_scaled_quadratic_lower system5
    (excludedPrimeValues [2, 3, 5]) positiveSector5 literalCap 21 c
    positiveSector5_subset_box (by norm_num [literalCap]) (by norm_num) hc
    system5_nonconstant system5_different_parts
    (fun _ _ hz i => system5_output_bound hz i) hlo
  exact rank5_infinitude_of_extracted_prime_patterns (hinf.mono (fun _ hz => hz.2))

theorem rank6_infinitude_of_quadraticMangoldtMass
    (h : HasQuadraticMangoldtMass system6 positiveSector6) :
    InfinitelyManyExactRank 6 := by
  obtain ⟨c, hc, hlo⟩ := h
  have hinf := primePattern_infinite_of_scaled_quadratic_lower system6
    (excludedPrimeValues [2, 3, 7]) positiveSector6 literalCap 61 c
    positiveSector6_subset_box (by norm_num [literalCap]) (by norm_num) hc
    system6_nonconstant system6_different_parts
    (fun _ _ hz i => system6_output_bound hz i) hlo
  exact rank6_infinitude_of_extracted_prime_patterns (hinf.mono (fun _ hz => hz.2))

theorem rank7_infinitude_of_quadraticMangoldtMass
    (h : HasQuadraticMangoldtMass system7 positiveSector7) :
    InfinitelyManyExactRank 7 := by
  obtain ⟨c, hc, hlo⟩ := h
  have hinf := primePattern_infinite_of_scaled_quadratic_lower system7
    (excludedPrimeValues [2, 3, 7, 13]) positiveSector7 literalCap 8001 c
    positiveSector7_subset_box (by norm_num [literalCap]) (by norm_num) hc
    system7_nonconstant system7_different_parts
    (fun _ _ hz i => system7_output_bound hz i) hlo
  exact rank7_infinitude_of_extracted_prime_patterns (hinf.mono (fun _ hz => hz.2))

theorem ranksFiveThroughSeven_of_quadraticMangoldtMass
    (h5 : HasQuadraticMangoldtMass system5 positiveSector5)
    (h6 : HasQuadraticMangoldtMass system6 positiveSector6)
    (h7 : HasQuadraticMangoldtMass system7 positiveSector7) : RanksFiveThroughSeven :=
  ⟨rank5_infinitude_of_quadraticMangoldtMass h5,
    rank6_infinitude_of_quadraticMangoldtMass h6,
    rank7_infinitude_of_quadraticMangoldtMass h7⟩

end RankCertificates.AnalyticExtraction
