module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Int.Interval
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Exact ranks five, six and seven, conditional on a standard prime theorem

The selected theorem states infinitude of geometric isomorphism classes of
elliptic curves over ℚ of each exact rational Mordell–Weil rank 5, 6 and 7.
The only external hypothesis is the explicitly written, general theorem on
finite-complexity linear patterns in primes below. Its statement has no
elliptic-curve, rank or special-family hypotheses.

This is a conditional formalization: the analytic theorem is not proved in
Lean here. The input is the positive-rectangle specialization of Green–Tao,
*Linear equations in primes* (2010), Main Theorem; its inverse-theorem and
Möbius–nilsequence prerequisites were proved in 2012 by Green–Tao–Ziegler and
Green–Tao, respectively. DOI: 10.4007/annals.2010.171.1753,
10.4007/annals.2012.176.2.11, and 10.4007/annals.2012.175.2.3.

All mathematical definitions needed to read the statement are given here.
This Challenge imports only Mathlib. Its sole deliberate proof hole is the
selected theorem; the separate Solution proves that same statement.
-/

@[expose] public section

namespace RankCertificates

/-- The genuine cardinal rank of the ℤ-module of rational points on a
Weierstrass model; infinite rank is not converted to a natural number. -/
noncomputable def rationalRank (E : WeierstrassCurve ℚ) : Cardinal :=
  Module.rank ℤ E.toAffine.Point

/-- Rational Mordell–Weil rank exactly the finite natural number `r`. -/
def HasExactRank (E : WeierstrassCurve ℚ) (r : ℕ) : Prop :=
  rationalRank E = (r : Cardinal)

/-- A rational Weierstrass model together with its nonsingularity certificate. -/
structure RationalEllipticCurve where
  model : WeierstrassCurve ℚ
  elliptic : model.IsElliptic

instance (E : RationalEllipticCurve) : E.model.IsElliptic := E.elliptic

/-- The usual rational j-invariant of a nonsingular rational model. -/
noncomputable def RationalEllipticCurve.j (E : RationalEllipticCurve) : ℚ := E.model.j

/-- Isomorphism after base change to the algebraic closure of ℚ, expressed
by a Weierstrass change of coordinates. Equal j-invariants classify it. -/
def GeometricallyIsomorphic (E E' : RationalEllipticCurve) : Prop :=
  ∃ C : WeierstrassCurve.VariableChange (AlgebraicClosure ℚ),
    C • E.model.baseChange (AlgebraicClosure ℚ) = E'.model.baseChange (AlgebraicClosure ℚ)

/-- Infinitely many distinct rational j-invariants of nonsingular rational
curves with exact rank `r`; thus infinitely many geometric isomorphism classes. -/
def InfinitelyManyExactRank (r : ℕ) : Prop :=
  Set.Infinite {j : ℚ | ∃ E : RationalEllipticCurve, E.j = j ∧ HasExactRank E.model r}

/-- The three principal infinitude claims, one for each exact rank. -/
def RanksFiveThroughSeven : Prop :=
  InfinitelyManyExactRank 5 ∧ InfinitelyManyExactRank 6 ∧ InfinitelyManyExactRank 7

namespace PrimePatterns

/-- An integer affine form `a*x + b*y + c` in two variables. -/
structure AffineForm where
  a : ℤ
  b : ℤ
  c : ℤ
  deriving DecidableEq

/-- Evaluation of an integer affine form at the integer pair `(x,y)`. -/
def AffineForm.eval (f : AffineForm) (x y : ℤ) : ℤ := f.a * x + f.b * y + f.c

/-- A simultaneous nonzero residue witness for all twelve forms modulo `p`. -/
def Avoids (fs : Fin 12 → AffineForm) (p : ℕ) : Prop :=
  ∃ x y : ℤ, ∀ i, (fs i).eval x y % (p : ℤ) ≠ 0

end PrimePatterns

namespace AnalyticExtraction

open scoped BigOperators

/-- The same integer affine form in the weighted-sum representation. -/
structure IntegerAffine where
  a : ℤ
  b : ℤ
  c : ℤ

/-- Evaluation of the weighted-sum form at an integer pair. -/
def IntegerAffine.eval (ψ : IntegerAffine) (z : ℤ × ℤ) : ℤ :=
  ψ.a * z.1 + ψ.b * z.2 + ψ.c

/-- The actual product of twelve von Mangoldt values. The positivity
hypothesis below makes `toNat` agree with each integer output. -/
noncomputable def patternWeight (ψ : Fin 12 → IntegerAffine) (z : ℤ × ℤ) : ℝ :=
  ∏ i, ArithmeticFunction.vonMangoldt ((ψ i).eval z).toNat

open PrimePatterns

/-- Preserve the three coefficients when changing affine-form representation. -/
def fromAffine (f : AffineForm) : IntegerAffine := ⟨f.a, f.b, f.c⟩

end AnalyticExtraction

namespace SingularSeries

open scoped BigOperators Classical

/-- The residue pairs on which no homogeneous form vanishes. -/
noncomputable def allowedResidues {K : Type*} [Field K] [Fintype K]
    {n : ℕ} (a b : Fin n → K) : Finset (K × K) :=
  Finset.univ.filter (fun z => ∀ i, a i * z.1 + b i * z.2 ≠ 0)

/-- The corrected local density for the homogeneous special case. -/
noncomputable def normalizedLocalFactor {K : Type*} [Field K] [Fintype K]
    {n : ℕ} (a b : Fin n → K) : ℝ :=
  ((allowedResidues a b).card : ℝ) / (Fintype.card K : ℝ) ^ 2 /
    (1 - 1 / (Fintype.card K : ℝ)) ^ n

/-- Prime-indexed corrected densities for homogeneous integer forms,
with factor 1 at every nonprime natural index. -/
noncomputable def integerLocalFactor {n : ℕ} (a b : Fin n → ℤ) (q : ℕ) : ℝ :=
  if h : q.Prime then
    letI : Fact q.Prime := ⟨h⟩
    normalizedLocalFactor (fun i => (a i : ZMod q)) (fun i => (b i : ZMod q))
  else 1

/-- The residue pairs on which no form vanishes, over a finite field. -/
noncomputable def affineAllowedResidues {K : Type*} [Field K] [Fintype K]
    {n : ℕ} (a b c : Fin n → K) : Finset (K × K) :=
  Finset.univ.filter (fun z => ∀ i, a i * z.1 + b i * z.2 + c i ≠ 0)

/-- Simultaneous nonvanishing density divided by the independent
nonvanishing density `(1 - 1/|K|)^n`. -/
noncomputable def affineNormalizedLocalFactor {K : Type*} [Field K] [Fintype K]
    {n : ℕ} (a b c : Fin n → K) : ℝ :=
  ((affineAllowedResidues a b c).card : ℝ) / (Fintype.card K : ℝ) ^ 2 /
    (1 - 1 / (Fintype.card K : ℝ)) ^ n

/-- The corrected residue density at a prime modulus, and 1 at every
nonprime index, so a product indexed by ℕ is the prime Euler product. -/
noncomputable def integerAffineLocalFactor {n : ℕ} (a b c : Fin n → ℤ) (q : ℕ) : ℝ :=
  if h : q.Prime then
    letI : Fact q.Prime := ⟨h⟩
    affineNormalizedLocalFactor (fun i => (a i : ZMod q))
      (fun i => (b i : ZMod q)) (fun i => (c i : ZMod q))
  else 1

/-- The actual local factors of the twelve affine forms. -/
noncomputable def outputsLocalFactor (fs : Fin 12 → PrimePatterns.AffineForm) : ℕ → ℝ :=
  integerAffineLocalFactor (fun i => (fs i).a) (fun i => (fs i).b) (fun i => (fs i).c)

end SingularSeries

namespace ConditionalPrimePatterns

open PrimePatterns AnalyticExtraction SingularSeries Filter Asymptotics
open scoped BigOperators

/-- The integer points in T times a fixed closed rectangle of area one. -/
def unitRectangle (u v : ℤ) (T : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (u * (T : ℤ)) ((u + 1) * T) ×ˢ
    Finset.Icc (v * (T : ℤ)) ((v + 1) * T)

/-- The external finite-complexity prime theorem, restricted to twelve
fixed nonconstant, pairwise nonparallel binary affine forms on a positive
unit rectangle. All coefficients and corners are fixed before T → ∞.

Local admissibility is simultaneous avoidance at every prime. The factor
σ is the product of the actual corrected residue densities. Positivity
at the integer rectangle corners extends to the real rectangle by affine
interpolation, so its archimedean factor is its area T². The conclusion
uses the actual twelvefold von Mangoldt sum and an error o(T²). -/
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

end ConditionalPrimePatterns

/-- Conditional on the explicitly stated general prime theorem, there
are infinitely many geometric isomorphism classes of elliptic curves over ℚ
with rational Mordell–Weil rank exactly 5, exactly 6, and exactly 7. -/
theorem infiniteGeometricClasses_exactRanksFiveThroughSeven
    (hGTZ : ConditionalPrimePatterns.FiniteComplexityPrimeAsymptotic) :
    RanksFiveThroughSeven := by
  sorry

end RankCertificates
