module

public import RankCertificates.PrimeFamilyAssembly
public import RankCertificates.Rank5ExactRank
public import RankCertificates.Rank6ExactRank
public import RankCertificates.Rank7ExactRank

/-!
The arithmetic and geometric parts of the three exact-rank infinitude
arguments reduce to the infinitude of the three literal simultaneous-prime
specialization sets. Those analytic infinitude statements remain explicit
hypotheses here. No unconditional prime-pattern or main theorem is asserted.
-/

@[expose] public section

namespace RankCertificates

/-- Infinitely many literal prime specializations give infinitely many
geometric classes of exact rank five. All descent and rank inputs are proved. -/
theorem rank5_infinitude_of_prime_values
    (h : Set.Infinite {v : ℤ × ℤ | PrimeSpecialization5 v.1 v.2}) :
    InfinitelyManyExactRank 5 :=
  PrimeFamilyAssembly.rank5_infinitude_of_prime_specializations _ h
    (fun _ hv => hv) (fun _ hv => Rank5ExactRank.actualImageCardinalities hv)

/-- Infinitely many literal prime specializations give infinitely many
geometric classes of exact rank six. All descent and rank inputs are proved. -/
theorem rank6_infinitude_of_prime_values
    (h : Set.Infinite {v : ℤ × ℤ | PrimeSpecialization6 v.1 v.2}) :
    InfinitelyManyExactRank 6 :=
  PrimeFamilyAssembly.rank6_infinitude_of_prime_specializations _ h
    (fun _ hv => hv) (fun _ hv => Rank6ExactRank.actualImageCardinalities hv)

/-- Infinitely many literal prime specializations give infinitely many
geometric classes of exact rank seven. All descent and rank inputs are proved. -/
theorem rank7_infinitude_of_prime_values
    (h : Set.Infinite {v : ℤ × ℤ | PrimeSpecialization7 v.1 v.2}) :
    InfinitelyManyExactRank 7 :=
  PrimeFamilyAssembly.rank7_infinitude_of_prime_specializations _ h
    (fun _ hv => hv) (fun _ hv => Rank7ExactRank.actualImageCardinalities hv)

/-- The requested conjunction, conditional only on the three precisely
specified analytic prime-pattern infinitude statements. -/
theorem ranksFiveThroughSeven_of_prime_values
    (h5 : Set.Infinite {v : ℤ × ℤ | PrimeSpecialization5 v.1 v.2})
    (h6 : Set.Infinite {v : ℤ × ℤ | PrimeSpecialization6 v.1 v.2})
    (h7 : Set.Infinite {v : ℤ × ℤ | PrimeSpecialization7 v.1 v.2}) :
    RanksFiveThroughSeven :=
  ⟨rank5_infinitude_of_prime_values h5, rank6_infinitude_of_prime_values h6,
    rank7_infinitude_of_prime_values h7⟩

end RankCertificates
