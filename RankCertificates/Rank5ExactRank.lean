module

public import RankCertificates.Rank5OddRows
public import RankCertificates.Rank5DyadicRows
public import RankCertificates.AmbientDescent
public import RankCertificates.TwoIsogenyRank

@[expose] public section

/-! Every positive, distinct prime specialization of the final rank-five
CRT lattice has exact rational Mordell–Weil rank five. The upper bounds
use actual point-image characters and the certified binary kernels. -/

namespace RankCertificates.Rank5ExactRank

open Integration Rank5CharacterEvaluation Rank5CharacterRows Rank5MovingRows
  Rank5FixedRows Rank5OddRows PrimePowerCharacters

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

variable {x y : ℤ} (h : PrimeSpecialization5 x y)

def fixedCodesE : Fin 5 → ℕ := ![1669, 3948, 267, 4, 3718]
def fixedCodesEp : Fin 3 → ℕ := ![108, 3206, 1]

noncomputable def fixedFunctionalE : Fin 5 →
    (Additive RationalSquareClasses →ₗ[ZMod 2] ZMod 2) :=
  ![dyadicCharacter4Linear, dyadicCharacter8Linear, unitCharacterLinear 3,
    valuationParityLinear 3, unitCharacterLinear 5]

noncomputable def fixedFunctionalEp : Fin 3 →
    (Additive RationalSquareClasses →ₗ[ZMod 2] ZMod 2) :=
  ![dyadicCharacter8Linear, unitCharacterLinear 5, realSignLinear]

def rowsE (e : ℤ) : List ℕ :=
  if e = 1 then MatrixCertificates.Rank5.E0 else MatrixCertificates.Rank5.E1

def rowsEp (e : ℤ) : List ℕ :=
  if e = 1 then MatrixCertificates.Rank5.Ep0 else MatrixCertificates.Rank5.Ep1

theorem rowsE_decompose (e : ℤ) : rowsE e = List.ofFn fixedCodesE ++
    List.ofFn (fun k => if e = 1 then codesE0 k else codesE1 k) := by
  by_cases he : e = 1 <;> simp only [rowsE, he, ite_true, ite_false]
  all_goals rfl

theorem rowsEp_decompose (e : ℤ) : rowsEp e = List.ofFn fixedCodesEp ++
    List.ofFn (fun k => if e = 1 then codesEp0 k else codesEp1 k) := by
  by_cases he : e = 1 <;> simp only [rowsEp, he, ite_true, ite_false]
  all_goals rfl

theorem fixedFunctionalE_literal (k : Fin 5) :
    squareClassCharacterRow (fixedFunctionalE k) (columnsE h.primes) =
      Binary.vector 12 (fixedCodesE k) := by
  fin_cases k
  · simpa [fixedFunctionalE, fixedCodesE] using dyadic4_E_literal h
  · simpa [fixedFunctionalE, fixedCodesE] using dyadic8_E_literal h
  · simpa [fixedFunctionalE, fixedCodesE] using three_E_literal h
  · simpa [fixedFunctionalE, fixedCodesE] using valuation3_E_literal h
  · simpa [fixedFunctionalE, fixedCodesE] using five_E_literal h

theorem fixedFunctionalEp_literal (k : Fin 3) :
    squareClassCharacterRow (fixedFunctionalEp k) (columnsEp h.primes) =
      Binary.vector 12 (fixedCodesEp k) := by
  fin_cases k
  · simpa [fixedFunctionalEp, fixedCodesEp] using dyadic8_Ep_literal h
  · simpa [fixedFunctionalEp, fixedCodesEp] using five_Ep_literal h
  · simpa [fixedFunctionalEp, fixedCodesEp] using real_Ep_literal h

theorem fixedFunctionalE_zero (k : Fin 5) {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (Rank5.a (M5 x) (N5 y)) (Rank5.b (M5 x) (N5 y))) :
    fixedFunctionalE k (Additive.ofMul q) = 0 := by
  fin_cases k
  · simpa [fixedFunctionalE] using Rank5TwoDescent.lattice_E_image_character_four_row x y hq
  · simpa [fixedFunctionalE] using Rank5TwoDescent.lattice_E_image_character_eight_row x y hq
  · simpa [fixedFunctionalE] using (three_actualImage hq).1
  · simpa [fixedFunctionalE] using (three_actualImage hq).2
  · simpa [fixedFunctionalE] using five_E_actualImage hq

include h in
theorem fixedFunctionalEp_zero (k : Fin 3) {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (-2 * Rank5.a (M5 x) (N5 y)) (Rank5.c (M5 x) (N5 y))) :
    fixedFunctionalEp k (Additive.ofMul q) = 0 := by
  fin_cases k
  · simpa [fixedFunctionalEp] using Rank5TwoDescent.lattice_Ep_image_character_eight_row x y hq
  · simpa [fixedFunctionalEp] using five_Ep_actualImage hq
  · simpa [fixedFunctionalEp] using real_Ep_actualImage h hq

theorem columnsE_signedPrime (p : Fin 12 → ℕ) :
    columnsE p = signedPrimeColumns (primeColumns5E p) := by
  funext i
  fin_cases i <;> norm_num [columnsE, signedPrimeColumns, primeColumns5E, Fin.cons]
  all_goals rfl

theorem columnsEp_signedPrime (p : Fin 12 → ℕ) :
    columnsEp p = signedPrimeColumns (primeColumns5Ep p) := by
  funext i
  fin_cases i <;> norm_num [columnsEp, signedPrimeColumns, primeColumns5Ep, Fin.cons]
  all_goals rfl

include h

theorem actualImageE_card_upperBound :
    Nat.card (twoIsogenyImage (Rank5.a (M5 x) (N5 y)) (Rank5.b (M5 x) (N5 y))) ≤ 2 ^ 3 := by
  have hambient : ∀ q ∈ twoIsogenyImage (Rank5.a (M5 x) (N5 y)) (Rank5.b (M5 x) (N5 y)),
      Additive.ofMul q ∈ (squareClassLinearMap (columnsE h.primes)).range := by
    intro q hq
    rw [columnsE_signedPrime]
    exact h.actualImageE_mem_signedPrime_range hq
  have hbound := twoIsogenyImage_card_le_verifiedCharacterKernel (Rank5.a (M5 x) (N5 y))
    (Rank5.b (M5 x) (N5 y)) (columnsE h.primes) (rowsE (epsilon h)) hambient (by
      intro row hrow
      rw [rowsE_decompose, List.mem_append] at hrow
      rcases hrow with hrow | hrow
      · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hrow
        exact ⟨fixedFunctionalE k, fixedFunctionalE_literal h k,
          fun _ hq => fixedFunctionalE_zero k hq⟩
      · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hrow
        exact ⟨functionalE h k, functionalE_literal h k,
          fun _ hq => functionalE_actualImage h k hq⟩)
  have hcard : Nat.card ↥(Binary.kernelSubmodule 12 (rowsE (epsilon h))) = 2 ^ 3 := by
    by_cases he : epsilon h = 1
    · simp only [rowsE, he, ite_true, Nat.card_eq_fintype_card]
      exact Binary.kernelSubmodule_card MatrixCertificates.Rank5.E0_kernel_length
    · simp only [rowsE, he, ite_false, Nat.card_eq_fintype_card]
      exact Binary.kernelSubmodule_card MatrixCertificates.Rank5.E1_kernel_length
  exact hbound.trans (le_of_eq hcard)

theorem actualImageEp_card_upperBound :
    Nat.card (twoIsogenyImage (-2 * Rank5.a (M5 x) (N5 y)) (Rank5.c (M5 x) (N5 y))) ≤ 2 ^ 4 := by
  have hambient : ∀ q ∈ twoIsogenyImage (-2 * Rank5.a (M5 x) (N5 y)) (Rank5.c (M5 x) (N5 y)),
      Additive.ofMul q ∈ (squareClassLinearMap (columnsEp h.primes)).range := by
    intro q hq
    rw [columnsEp_signedPrime]
    exact h.actualImageEp_mem_signedPrime_range hq
  have hbound := twoIsogenyImage_card_le_verifiedCharacterKernel (-2 * Rank5.a (M5 x) (N5 y))
    (Rank5.c (M5 x) (N5 y)) (columnsEp h.primes) (rowsEp (epsilon h)) hambient (by
      intro row hrow
      rw [rowsEp_decompose, List.mem_append] at hrow
      rcases hrow with hrow | hrow
      · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hrow
        exact ⟨fixedFunctionalEp k, fixedFunctionalEp_literal h k,
          fun _ hq => fixedFunctionalEp_zero h k hq⟩
      · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hrow
        exact ⟨functionalEp h k, functionalEp_literal h k,
          fun _ hq => functionalEp_actualImage h k hq⟩)
  have hcard : Nat.card ↥(Binary.kernelSubmodule 12 (rowsEp (epsilon h))) = 2 ^ 4 := by
    by_cases he : epsilon h = 1
    · simp only [rowsEp, he, ite_true, Nat.card_eq_fintype_card]
      exact Binary.kernelSubmodule_card MatrixCertificates.Rank5.Ep0_kernel_length
    · simp only [rowsEp, he, ite_false, Nat.card_eq_fintype_card]
      exact Binary.kernelSubmodule_card MatrixCertificates.Rank5.Ep1_kernel_length
  exact hbound.trans (le_of_eq hcard)

/-- The actual original Kummer image has eight rational squareclasses. -/
theorem actualImageE_card :
    Nat.card (twoIsogenyImage (Rank5.a (M5 x) (N5 y)) (Rank5.b (M5 x) (N5 y))) = 2 ^ 3 :=
  Nat.le_antisymm (actualImageE_card_upperBound h) h.actualImageE_card_lowerBound

/-- The actual partner Kummer image has sixteen rational squareclasses. -/
theorem actualImageEp_card :
    Nat.card (twoIsogenyImage (-2 * Rank5.a (M5 x) (N5 y)) (Rank5.c (M5 x) (N5 y))) = 2 ^ 4 :=
  Nat.le_antisymm (actualImageEp_card_upperBound h) h.actualImageEp_card_lowerBound

theorem actualImageCardinalities :
    ActualImageCardinalities (Rank5.a (M5 x) (N5 y)) (Rank5.b (M5 x) (N5 y)) 3 4 := by
  constructor
  · exact actualImageE_card h
  · rw [Rank5.isogeny_coefficient]
    exact actualImageEp_card h

/-- Exact rational rank five under the concrete prime-specialization hypothesis. -/
theorem hasExactRank : HasExactRank (Rank5.E (M5 x) (N5 y)) 5 := by
  let : (twoTorsionModel (Rank5.a (M5 x) (N5 y)) (Rank5.b (M5 x) (N5 y))).IsElliptic :=
    DescentWitnesses.elliptic5E_on_lattice x y
  exact hasExactRank_of_twoIsogeny_image_cardinalities _ _ 5 3 4
    (actualImageCardinalities h) (by decide)

end RankCertificates.Rank5ExactRank
