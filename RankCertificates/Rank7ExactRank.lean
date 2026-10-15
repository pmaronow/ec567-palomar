module

public import RankCertificates.Rank7FixedRows
public import RankCertificates.Rank7TwoDescent
public import RankCertificates.AmbientDescent
public import RankCertificates.TwoIsogenyRank

@[expose] public section

/-! Exact actual image cardinalities, and hence exact rational rank, for
the final rank-seven family whenever its twelve literal lattice outputs
are positive distinct primes outside the four fixed prime columns. -/

namespace RankCertificates.Rank7ExactRank

-- The sign character's binary linear map uses the additive group underlying
-- the ring `ZMod 2`.
local instance : AddCommGroup (ZMod 2) := (ZMod.commRing 2).toAddCommGroup

open Integration Rank7CharacterEvaluation Rank7FixedRows PrimePowerCharacters

local instance : Fact (Nat.Prime 2) := ⟨by decide +kernel⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide +kernel⟩
local instance : Fact (Nat.Prime 7) := ⟨by decide +kernel⟩
local instance : Fact (Nat.Prime 13) := ⟨by decide +kernel⟩

variable {x y : ℤ} (h : PrimeSpecialization7 x y)

include h

theorem E_fixed_rows : ∀ row ∈ [4943, 8020, 195, 4],
    ∃ f : Additive RationalSquareClasses →ₗ[ZMod 2] ZMod 2,
      squareClassCharacterRow f (signedPrimeColumns (primeColumns7E h.primes)) =
        Binary.vector 13 row ∧
      ∀ q ∈ twoIsogenyImage (Rank7.a (M7 x) (N7 y)) (Rank7.b (M7 x) (N7 y)),
        f (Additive.ofMul q) = 0 := by
  intro row hr
  have hh : row = 4943 ∨ row = 8020 ∨ row = 195 ∨ row = 4 := by simpa using hr
  rcases hh with rfl | rfl | rfl | rfl
  · refine ⟨dyadicCharacter4Linear + valuationParityLinear 2,
      original_dyadic_combined_row h, ?_⟩
    intro q hq
    exact Rank7TwoDescent.original_image_character_four_valuation_row x y hq
  · refine ⟨dyadicCharacter8Linear, dyadic8_E_row h, ?_⟩
    intro q hq
    exact Rank7TwoDescent.original_image_character_eight_row x y hq
  · refine ⟨unitCharacterLinear 3, three_unit_row h, ?_⟩
    intro q hq
    exact (Rank7ThreeDescent.lattice_image_three_rows x y hq).2
  · refine ⟨valuationParityLinear 3, three_valuation_row h, ?_⟩
    intro q hq
    exact (Rank7ThreeDescent.lattice_image_three_rows x y hq).1

theorem E_all_rows0 (he : epsilon h = 1) :
    ∀ row ∈ MatrixCertificates.Rank7.E0,
      ∃ f : Additive RationalSquareClasses →ₗ[ZMod 2] ZMod 2,
        squareClassCharacterRow f (signedPrimeColumns (primeColumns7E h.primes)) =
          Binary.vector 13 row ∧
        ∀ q ∈ twoIsogenyImage (Rank7.a (M7 x) (N7 y)) (Rank7.b (M7 x) (N7 y)),
          f (Additive.ofMul q) = 0 := by
  intro row hr
  have hsplit : MatrixCertificates.Rank7.E0 =
      [4943, 8020, 195, 4] ++ MatrixCertificates.Rank7.E0.drop 4 := rfl
  rw [hsplit, List.mem_append] at hr
  exact hr.elim (fun hr => E_fixed_rows h row hr) (fun hr => E_moving_rows0 h he row hr)

theorem E_all_rows1 (he : epsilon h = -1) :
    ∀ row ∈ MatrixCertificates.Rank7.E1,
      ∃ f : Additive RationalSquareClasses →ₗ[ZMod 2] ZMod 2,
        squareClassCharacterRow f (signedPrimeColumns (primeColumns7E h.primes)) =
          Binary.vector 13 row ∧
        ∀ q ∈ twoIsogenyImage (Rank7.a (M7 x) (N7 y)) (Rank7.b (M7 x) (N7 y)),
          f (Additive.ofMul q) = 0 := by
  intro row hr
  have hsplit : MatrixCertificates.Rank7.E1 =
      [4943, 8020, 195, 4] ++ MatrixCertificates.Rank7.E1.drop 4 := rfl
  rw [hsplit, List.mem_append] at hr
  exact hr.elim (fun hr => E_fixed_rows h row hr) (fun hr => E_moving_rows1 h he row hr)

theorem actualImageE_card_upperBound :
    Nat.card (twoIsogenyImage (Rank7.a (M7 x) (N7 y)) (Rank7.b (M7 x) (N7 y))) ≤ 2 ^ 5 := by
  have hambient : ∀ q ∈ twoIsogenyImage (Rank7.a (M7 x) (N7 y)) (Rank7.b (M7 x) (N7 y)),
      Additive.ofMul q ∈
        (squareClassLinearMap (signedPrimeColumns (primeColumns7E h.primes))).range := by
    intro q hq
    exact h.actualImageE_mem_signedPrime_range hq
  rcases epsilon_dichotomy h with he | he
  · have hu := twoIsogenyImage_card_le_verifiedCharacterKernel _ _ _
      MatrixCertificates.Rank7.E0 hambient (E_all_rows0 h he)
    have hc : Nat.card ↥(Binary.kernelSubmodule 13 MatrixCertificates.Rank7.E0) = 2 ^ 5 := by
      rw [Nat.card_eq_fintype_card]
      exact Binary.kernelSubmodule_card MatrixCertificates.Rank7.E0_kernel_length
    exact hu.trans_eq hc
  · have hu := twoIsogenyImage_card_le_verifiedCharacterKernel _ _ _
      MatrixCertificates.Rank7.E1 hambient (E_all_rows1 h he)
    have hc : Nat.card ↥(Binary.kernelSubmodule 13 MatrixCertificates.Rank7.E1) = 2 ^ 5 := by
      rw [Nat.card_eq_fintype_card]
      exact Binary.kernelSubmodule_card MatrixCertificates.Rank7.E1_kernel_length
    exact hu.trans_eq hc

theorem actualImageE_card :
    Nat.card (twoIsogenyImage (Rank7.a (M7 x) (N7 y)) (Rank7.b (M7 x) (N7 y))) = 2 ^ 5 :=
  Nat.le_antisymm (actualImageE_card_upperBound h) h.actualImageE_card_lowerBound

theorem Ep_fixed_rows : ∀ row ∈ [7705, 4117, 8, 7626, 16, 1],
    ∃ f : Additive RationalSquareClasses →ₗ[ZMod 2] ZMod 2,
      squareClassCharacterRow f (signedPrimeColumns (primeColumns7Ep h.primes)) =
        Binary.vector 13 row ∧
      ∀ q ∈ twoIsogenyImage (-2 * Rank7.a (M7 x) (N7 y)) (Rank7.c (M7 x) (N7 y)),
        f (Additive.ofMul q) = 0 := by
  intro row hr
  have hh : row = 7705 ∨ row = 4117 ∨ row = 8 ∨ row = 7626 ∨ row = 16 ∨ row = 1 := by
    simpa using hr
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨dyadicCharacter4Linear + dyadicCharacter8Linear,
      partner_dyadic_combined_row h, ?_⟩
    intro q hq
    exact Rank7TwoDescent.dual_image_character_sum_row x y hq
  · refine ⟨unitCharacterLinear 7, seven_unit_row h, ?_⟩
    intro q hq
    exact (Rank7FixedOddDescent.lattice_partner_seven_rows x y hq).2
  · refine ⟨valuationParityLinear 7, seven_valuation_row h, ?_⟩
    intro q hq
    exact (Rank7FixedOddDescent.lattice_partner_seven_rows x y hq).1
  · refine ⟨unitCharacterLinear 13, thirteen_unit_row h, ?_⟩
    intro q hq
    exact (Rank7FixedOddDescent.lattice_partner_thirteen_rows x y hq).2
  · refine ⟨valuationParityLinear 13, thirteen_valuation_row h, ?_⟩
    intro q hq
    exact (Rank7FixedOddDescent.lattice_partner_thirteen_rows x y hq).1
  · refine ⟨squareClassSign.toZModLinearMap 2, sign_row h, ?_⟩
    intro q hq
    exact partner_sign_zero h hq

theorem Ep_all_rows0 (he : epsilon h = 1) :
    ∀ row ∈ MatrixCertificates.Rank7.Ep0,
      ∃ f : Additive RationalSquareClasses →ₗ[ZMod 2] ZMod 2,
        squareClassCharacterRow f (signedPrimeColumns (primeColumns7Ep h.primes)) =
          Binary.vector 13 row ∧
        ∀ q ∈ twoIsogenyImage (-2 * Rank7.a (M7 x) (N7 y)) (Rank7.c (M7 x) (N7 y)),
          f (Additive.ofMul q) = 0 := by
  intro row hr
  have hsplit : MatrixCertificates.Rank7.Ep0 =
      [7705, 4117, 8, 7626, 16, 1] ++ MatrixCertificates.Rank7.Ep0.drop 6 := rfl
  rw [hsplit, List.mem_append] at hr
  exact hr.elim (fun hr => Ep_fixed_rows h row hr) (fun hr => Ep_moving_rows0 h he row hr)

theorem Ep_all_rows1 (he : epsilon h = -1) :
    ∀ row ∈ MatrixCertificates.Rank7.Ep1,
      ∃ f : Additive RationalSquareClasses →ₗ[ZMod 2] ZMod 2,
        squareClassCharacterRow f (signedPrimeColumns (primeColumns7Ep h.primes)) =
          Binary.vector 13 row ∧
        ∀ q ∈ twoIsogenyImage (-2 * Rank7.a (M7 x) (N7 y)) (Rank7.c (M7 x) (N7 y)),
          f (Additive.ofMul q) = 0 := by
  intro row hr
  have hsplit : MatrixCertificates.Rank7.Ep1 =
      [7705, 4117, 8, 7626, 16, 1] ++ MatrixCertificates.Rank7.Ep1.drop 6 := rfl
  rw [hsplit, List.mem_append] at hr
  exact hr.elim (fun hr => Ep_fixed_rows h row hr) (fun hr => Ep_moving_rows1 h he row hr)

theorem actualImageEp_card_upperBound :
    Nat.card (twoIsogenyImage (-2 * Rank7.a (M7 x) (N7 y)) (Rank7.c (M7 x) (N7 y))) ≤ 2 ^ 4 := by
  have hambient : ∀ q ∈ twoIsogenyImage (-2 * Rank7.a (M7 x) (N7 y)) (Rank7.c (M7 x) (N7 y)),
      Additive.ofMul q ∈
        (squareClassLinearMap (signedPrimeColumns (primeColumns7Ep h.primes))).range := by
    intro q hq
    exact h.actualImageEp_mem_signedPrime_range hq
  rcases epsilon_dichotomy h with he | he
  · have hu := twoIsogenyImage_card_le_verifiedCharacterKernel _ _ _
      MatrixCertificates.Rank7.Ep0 hambient (Ep_all_rows0 h he)
    have hc : Nat.card ↥(Binary.kernelSubmodule 13 MatrixCertificates.Rank7.Ep0) = 2 ^ 4 := by
      rw [Nat.card_eq_fintype_card]
      exact Binary.kernelSubmodule_card MatrixCertificates.Rank7.Ep0_kernel_length
    exact hu.trans_eq hc
  · have hu := twoIsogenyImage_card_le_verifiedCharacterKernel _ _ _
      MatrixCertificates.Rank7.Ep1 hambient (Ep_all_rows1 h he)
    have hc : Nat.card ↥(Binary.kernelSubmodule 13 MatrixCertificates.Rank7.Ep1) = 2 ^ 4 := by
      rw [Nat.card_eq_fintype_card]
      exact Binary.kernelSubmodule_card MatrixCertificates.Rank7.Ep1_kernel_length
    exact hu.trans_eq hc

theorem actualImageEp_card :
    Nat.card (twoIsogenyImage (-2 * Rank7.a (M7 x) (N7 y)) (Rank7.c (M7 x) (N7 y))) = 2 ^ 4 :=
  Nat.le_antisymm (actualImageEp_card_upperBound h) h.actualImageEp_card_lowerBound

/-- Both actual rational-point Kummer images have the exact required sizes. -/
theorem actualImageCardinalities :
    ActualImageCardinalities (Rank7.a (M7 x) (N7 y)) (Rank7.b (M7 x) (N7 y)) 5 4 := by
  constructor
  · exact actualImageE_card h
  · rw [Rank7.discriminant_coefficient]
    exact actualImageEp_card h

/-- Every positive distinct prime specialization of the literal final
rank-seven lattice has genuine rational Mordell–Weil rank seven. -/
theorem hasExactRank : HasExactRank (Rank7.E (M7 x) (N7 y)) 7 := by
  let : (twoTorsionModel (Rank7.a (M7 x) (N7 y))
    (Rank7.b (M7 x) (N7 y))).IsElliptic := DescentWitnesses.elliptic7E_on_lattice x y
  exact hasExactRank_of_twoIsogeny_image_cardinalities _ _ 7 5 4
    (actualImageCardinalities h) (by decide +kernel)

end RankCertificates.Rank7ExactRank
