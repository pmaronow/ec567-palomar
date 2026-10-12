module

public import RankCertificates.ConditionalPrimePatterns

/-!
The checked proof of the Challenge statement. The sole external analytic
input remains the explicit argument `hGTZ`; the local arithmetic, analytic
extraction, descent, exact rank and geometric-infinitude steps are supplied
by the substantive development imported above.
-/

@[expose] public section

namespace RankCertificates

/-- Infinitely many geometric classes at each exact rank 5, 6 and 7,
conditional on the stated standard finite-complexity prime asymptotic. -/
theorem infiniteGeometricClasses_exactRanksFiveThroughSeven
    (hGTZ : ConditionalPrimePatterns.FiniteComplexityPrimeAsymptotic) :
    RanksFiveThroughSeven :=
  ConditionalPrimePatterns.ranksFiveThroughSeven_of_finiteComplexityPrimeAsymptotic hGTZ

end RankCertificates
