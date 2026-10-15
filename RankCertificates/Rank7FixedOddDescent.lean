module

public import RankCertificates.SplitReductionDescent
public import RankCertificates.PrimeCoefficientSupport

/-!
The partner rank-seven curve has split double-root reduction at 7 and 13.
The roots are nonzero squares on the entire literal CRT lattice, so both
valuation parity and normalized unit character vanish for its actual image.
-/

@[expose] public section

namespace RankCertificates.Rank7FixedOddDescent

open LocalValuations

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 13) := ⟨by decide⟩

theorem output_residues_seven (x y : ℤ) (i : Fin 12) :
    ((PrimePatterns.Rank7.outputs i).eval x y : ZMod 7) =
      ((PrimePatterns.Rank7.outputs i).c : ZMod 7) := by
  have hcoeff : ∀ i : Fin 12,
      ((PrimePatterns.Rank7.outputs i).a : ZMod 7) = 0 ∧
      ((PrimePatterns.Rank7.outputs i).b : ZMod 7) = 0 := by decide +kernel
  simp only [PrimePatterns.AffineForm.eval, Int.cast_add, Int.cast_mul,
    (hcoeff i).1, (hcoeff i).2, zero_mul, zero_add]

theorem output_residues_thirteen (x y : ℤ) (i : Fin 12) :
    ((PrimePatterns.Rank7.outputs i).eval x y : ZMod 13) =
      ((PrimePatterns.Rank7.outputs i).c : ZMod 13) := by
  have hcoeff : ∀ i : Fin 12,
      ((PrimePatterns.Rank7.outputs i).a : ZMod 13) = 0 ∧
      ((PrimePatterns.Rank7.outputs i).b : ZMod 13) = 0 := by decide +kernel
  simp only [PrimePatterns.AffineForm.eval, Int.cast_add, Int.cast_mul,
    (hcoeff i).1, (hcoeff i).2, zero_mul, zero_add]

theorem lattice_residues_seven (x y : ℤ) :
    (aInteger7 x y : ZMod 7) = 1 ∧
    (bInteger7 x y : ZMod 7) = 0 ∧
    (cInteger7 x y : ZMod 7) = 1 := by
  simp only [aInteger7, bInteger7, cInteger7, Int.cast_mul, Int.cast_neg,
    Int.cast_ofNat, output_residues_seven]
  decide +kernel

theorem lattice_residues_thirteen (x y : ℤ) :
    (aInteger7 x y : ZMod 13) = 12 ∧
    (bInteger7 x y : ZMod 13) = 0 ∧
    (cInteger7 x y : ZMod 13) = 1 := by
  simp only [aInteger7, bInteger7, cInteger7, Int.cast_mul, Int.cast_neg,
    Int.cast_ofNat, output_residues_thirteen]
  decide +kernel

/-- Every nonzero representative of every actual partner image class has
even 7-adic valuation and square normalized character. -/
theorem lattice_partner_seven_conditions (x y : ℤ)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage
      (-2 * Rank7.a (Integration.M7 x) (Integration.N7 y))
      (Rank7.c (Integration.M7 x) (Integration.N7 y)))
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) :
    Even (padicValRat 7 z) ∧ unitCharacter 7 z = 1 := by
  obtain ⟨ha, _, hb⟩ := lattice_residues_seven x y
  apply SplitReductionDescent.image_character_conditions 7
    (-2 * aInteger7 x y) (cInteger7 x y) 1
    (by decide) (by exact ⟨1, by decide⟩) _ _ _ hz hc
  · simp only [Int.cast_mul, Int.cast_neg, Int.cast_ofNat, ha]
    rfl
  · simpa only [one_pow] using hb
  · simpa only [Int.cast_mul, Int.cast_neg, Int.cast_ofNat,
      aInteger7_cast, cInteger7_cast] using hq

/-- The repeated residue root at 13 is 12, a nonzero square, so the same
necessary restrictions hold on the entire CRT lattice. -/
theorem lattice_partner_thirteen_conditions (x y : ℤ)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage
      (-2 * Rank7.a (Integration.M7 x) (Integration.N7 y))
      (Rank7.c (Integration.M7 x) (Integration.N7 y)))
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) :
    Even (padicValRat 13 z) ∧ unitCharacter 13 z = 1 := by
  obtain ⟨ha, _, hb⟩ := lattice_residues_thirteen x y
  apply SplitReductionDescent.image_character_conditions 13
    (-2 * aInteger7 x y) (cInteger7 x y) 12
    (by decide) (by exact ⟨5, by decide⟩) _ _ _ hz hc
  · simp only [Int.cast_mul, Int.cast_neg, Int.cast_ofNat, ha]
    rfl
  · simpa only [show (12 : ZMod 13) ^ 2 = 1 by decide] using hb
  · simpa only [Int.cast_mul, Int.cast_neg, Int.cast_ofNat,
      aInteger7_cast, cInteger7_cast] using hq

/-- Both actual partner-image binary functionals vanish at 7. -/
theorem lattice_partner_seven_rows (x y : ℤ)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage
      (-2 * Rank7.a (Integration.M7 x) (Integration.N7 y))
      (Rank7.c (Integration.M7 x) (Integration.N7 y))) :
    valuationParityLinear 7 (Additive.ofMul q) = 0 ∧
      unitCharacterLinear 7 (Additive.ofMul q) = 0 := by
  obtain ⟨ha, _, hb⟩ := lattice_residues_seven x y
  apply SplitReductionDescent.image_rows 7
    (-2 * aInteger7 x y) (cInteger7 x y) 1
    (by decide) (by exact ⟨1, by decide⟩)
  · simp only [Int.cast_mul, Int.cast_neg, Int.cast_ofNat, ha]
    rfl
  · simpa only [one_pow] using hb
  · simpa only [Int.cast_mul, Int.cast_neg, Int.cast_ofNat,
      aInteger7_cast, cInteger7_cast] using hq

/-- Both actual partner-image binary functionals vanish at 13. -/
theorem lattice_partner_thirteen_rows (x y : ℤ)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage
      (-2 * Rank7.a (Integration.M7 x) (Integration.N7 y))
      (Rank7.c (Integration.M7 x) (Integration.N7 y))) :
    valuationParityLinear 13 (Additive.ofMul q) = 0 ∧
      unitCharacterLinear 13 (Additive.ofMul q) = 0 := by
  obtain ⟨ha, _, hb⟩ := lattice_residues_thirteen x y
  apply SplitReductionDescent.image_rows 13
    (-2 * aInteger7 x y) (cInteger7 x y) 12
    (by decide) (by exact ⟨5, by decide⟩)
  · simp only [Int.cast_mul, Int.cast_neg, Int.cast_ofNat, ha]
    rfl
  · simpa only [show (12 : ZMod 13) ^ 2 = 1 by decide] using hb
  · simpa only [Int.cast_mul, Int.cast_neg, Int.cast_ofNat,
      aInteger7_cast, cInteger7_cast] using hq

end RankCertificates.Rank7FixedOddDescent
