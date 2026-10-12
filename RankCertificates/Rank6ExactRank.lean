module

public import RankCertificates.Rank6FixedRows
public import RankCertificates.Rank6Descent
public import RankCertificates.Rank6TwoDescent
public import RankCertificates.AmbientDescent
public import RankCertificates.TwoIsogenyRank

@[expose] public section

/-! The exact rational Mordell–Weil rank of every positive prime
specialization of the final rank-six family. All upper bounds below arise
from genuine local characters of actual rational-point images. -/

namespace RankCertificates.Rank6ExactRank

open Integration Rank6CharacterEvaluation Rank6CharacterRows Rank6LiteralRows Rank6FixedRows

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {x y : ℤ} (h : PrimeSpecialization6 x y)

noncomputable def characterFamilyE : Fin 12 →
    (Additive RationalSquareClasses →ₗ[ZMod 2] ZMod 2) :=
  ![valuationParityLinear 2, unitCharacterLinear 3, valuationParityLinear 3,
    unitCharacterLinear 7,
    @typeIIICharacterLinear (h.primes 0) ⟨h.prime 0⟩ (Rank6.b (M6 x) (N6 y)),
    @typeIIICharacterLinear (h.primes 1) ⟨h.prime 1⟩ (Rank6.b (M6 x) (N6 y)),
    @typeIIICharacterLinear (h.primes 2) ⟨h.prime 2⟩ (Rank6.b (M6 x) (N6 y)),
    @typeIIICharacterLinear (h.primes 3) ⟨h.prime 3⟩ (Rank6.b (M6 x) (N6 y)),
    @unitCharacterLinear (h.primes 8) ⟨h.prime 8⟩,
    @unitCharacterLinear (h.primes 9) ⟨h.prime 9⟩,
    @unitCharacterLinear (h.primes 10) ⟨h.prime 10⟩,
    @unitCharacterLinear (h.primes 11) ⟨h.prime 11⟩]

noncomputable def characterFamilyEp : Fin 12 →
    (Additive RationalSquareClasses →ₗ[ZMod 2] ZMod 2) :=
  ![PrimePowerCharacters.dyadicCharacter4Linear, valuationParityLinear 2,
    characterValuationLinear 7 1, realSignLinear,
    @typeIIICharacterLinear (h.primes 0) ⟨h.prime 0⟩ (Rank6.c (M6 x) (N6 y)),
    @typeIIICharacterLinear (h.primes 1) ⟨h.prime 1⟩ (Rank6.c (M6 x) (N6 y)),
    @typeIIICharacterLinear (h.primes 2) ⟨h.prime 2⟩ (Rank6.c (M6 x) (N6 y)),
    @typeIIICharacterLinear (h.primes 3) ⟨h.prime 3⟩ (Rank6.c (M6 x) (N6 y)),
    @unitCharacterLinear (h.primes 4) ⟨h.prime 4⟩,
    @unitCharacterLinear (h.primes 5) ⟨h.prime 5⟩,
    @unitCharacterLinear (h.primes 6) ⟨h.prime 6⟩,
    @unitCharacterLinear (h.primes 7) ⟨h.prime 7⟩]

def rowsE (e : ℤ) : List ℕ :=
  if e = 1 then MatrixCertificates.Rank6.E0 else MatrixCertificates.Rank6.E1

def rowsEp (e : ℤ) : List ℕ :=
  if e = 1 then MatrixCertificates.Rank6.Ep0 else MatrixCertificates.Rank6.Ep1

theorem rowsE_ofFn (e : ℤ) : rowsE e = List.ofFn
    (fun i : Fin 12 => (rowsE e).getD i.val 0) := by
  by_cases he : e = 1 <;> simp only [rowsE, he, ite_true, ite_false]
  all_goals rfl

theorem rowsEp_ofFn (e : ℤ) : rowsEp e = List.ofFn
    (fun i : Fin 12 => (rowsEp e).getD i.val 0) := by
  by_cases he : e = 1 <;> simp only [rowsEp, he, ite_true, ite_false]
  all_goals rfl

theorem unitCharacterRow_as_characterRow {n : ℕ} (p : ℕ) [Fact p.Prime]
    (columns : Fin n → ℚ) :
    squareClassCharacterRow (unitCharacterLinear p) columns = unitCharacterRow p columns := rfl

theorem characterFamilyE_literal (i : Fin 12) :
    squareClassCharacterRow (characterFamilyE h i) (columnsE h.primes) =
      Binary.vector 12 ((rowsE (epsilon h)).getD i.val 0) := by
  by_cases he : epsilon h = 1
  all_goals fin_cases i
  · simpa [characterFamilyE, rowsE, he, MatrixCertificates.Rank6.E0, MatrixCertificates.Rank6.E1] using valuation2RowE_literal h
  · simpa [unitCharacterRow_as_characterRow,characterFamilyE, rowsE, he, MatrixCertificates.Rank6.E0, MatrixCertificates.Rank6.E1] using character3RowE_literal h
  · simpa [characterFamilyE, rowsE, he, MatrixCertificates.Rank6.E0, MatrixCertificates.Rank6.E1] using valuation3RowE_literal h
  · simpa [unitCharacterRow_as_characterRow,characterFamilyE, rowsE, he, MatrixCertificates.Rank6.E0, MatrixCertificates.Rank6.E1] using character7RowE_literal h
  · simpa [characterFamilyE, rowsE, he, rowCodeE, ERowNumber] using typeIIIRowE_literal h 0 (by decide)
  · simpa [characterFamilyE, rowsE, he, rowCodeE, ERowNumber] using typeIIIRowE_literal h 1 (by decide)
  · simpa [characterFamilyE, rowsE, he, rowCodeE, ERowNumber] using typeIIIRowE_literal h 2 (by decide)
  · simpa [characterFamilyE, rowsE, he, rowCodeE, ERowNumber] using typeIIIRowE_literal h 3 (by decide)
  · simpa [unitCharacterRow_as_characterRow,characterFamilyE, rowsE, he, rowCodeE, ERowNumber] using typeIIRowE_literal h 8 (by decide)
  · simpa [unitCharacterRow_as_characterRow,characterFamilyE, rowsE, he, rowCodeE, ERowNumber] using typeIIRowE_literal h 9 (by decide)
  · simpa [unitCharacterRow_as_characterRow,characterFamilyE, rowsE, he, rowCodeE, ERowNumber] using typeIIRowE_literal h 10 (by decide)
  · simpa [unitCharacterRow_as_characterRow,characterFamilyE, rowsE, he, rowCodeE, ERowNumber] using typeIIRowE_literal h 11 (by decide)
  · simpa [characterFamilyE, rowsE, he, MatrixCertificates.Rank6.E0, MatrixCertificates.Rank6.E1] using valuation2RowE_literal h
  · simpa [unitCharacterRow_as_characterRow,characterFamilyE, rowsE, he, MatrixCertificates.Rank6.E0, MatrixCertificates.Rank6.E1] using character3RowE_literal h
  · simpa [characterFamilyE, rowsE, he, MatrixCertificates.Rank6.E0, MatrixCertificates.Rank6.E1] using valuation3RowE_literal h
  · simpa [unitCharacterRow_as_characterRow,characterFamilyE, rowsE, he, MatrixCertificates.Rank6.E0, MatrixCertificates.Rank6.E1] using character7RowE_literal h
  · simpa [characterFamilyE, rowsE, he, rowCodeE, ERowNumber] using typeIIIRowE_literal h 0 (by decide)
  · simpa [characterFamilyE, rowsE, he, rowCodeE, ERowNumber] using typeIIIRowE_literal h 1 (by decide)
  · simpa [characterFamilyE, rowsE, he, rowCodeE, ERowNumber] using typeIIIRowE_literal h 2 (by decide)
  · simpa [characterFamilyE, rowsE, he, rowCodeE, ERowNumber] using typeIIIRowE_literal h 3 (by decide)
  · simpa [unitCharacterRow_as_characterRow,characterFamilyE, rowsE, he, rowCodeE, ERowNumber] using typeIIRowE_literal h 8 (by decide)
  · simpa [unitCharacterRow_as_characterRow,characterFamilyE, rowsE, he, rowCodeE, ERowNumber] using typeIIRowE_literal h 9 (by decide)
  · simpa [unitCharacterRow_as_characterRow,characterFamilyE, rowsE, he, rowCodeE, ERowNumber] using typeIIRowE_literal h 10 (by decide)
  · simpa [unitCharacterRow_as_characterRow,characterFamilyE, rowsE, he, rowCodeE, ERowNumber] using typeIIRowE_literal h 11 (by decide)

theorem characterFamilyEp_literal (i : Fin 12) :
    squareClassCharacterRow (characterFamilyEp h i) (columnsEp h.primes) =
      Binary.vector 12 ((rowsEp (epsilon h)).getD i.val 0) := by
  by_cases he : epsilon h = 1
  all_goals fin_cases i
  · simpa [characterFamilyEp, rowsEp, he, MatrixCertificates.Rank6.Ep0, MatrixCertificates.Rank6.Ep1] using dyadic_four_row_literal h
  · simpa [characterFamilyEp, rowsEp, he, MatrixCertificates.Rank6.Ep0, MatrixCertificates.Rank6.Ep1] using valuation2RowEp_literal h
  · simpa [characterFamilyEp, rowsEp, he, MatrixCertificates.Rank6.Ep0, MatrixCertificates.Rank6.Ep1] using dual_seven_row_literal h
  · simpa [characterFamilyEp, rowsEp, he, MatrixCertificates.Rank6.Ep0, MatrixCertificates.Rank6.Ep1] using real_row_literal h
  · simpa [characterFamilyEp, rowsEp, he, rowCodeEp] using typeIIIRowEp_literal h 0 (by decide)
  · simpa [characterFamilyEp, rowsEp, he, rowCodeEp] using typeIIIRowEp_literal h 1 (by decide)
  · simpa [characterFamilyEp, rowsEp, he, rowCodeEp] using typeIIIRowEp_literal h 2 (by decide)
  · simpa [characterFamilyEp, rowsEp, he, rowCodeEp] using typeIIIRowEp_literal h 3 (by decide)
  · simpa [unitCharacterRow_as_characterRow,characterFamilyEp, rowsEp, he, rowCodeEp] using typeIIRowEp_literal h 4 (by decide) (by decide)
  · simpa [unitCharacterRow_as_characterRow,characterFamilyEp, rowsEp, he, rowCodeEp] using typeIIRowEp_literal h 5 (by decide) (by decide)
  · simpa [unitCharacterRow_as_characterRow,characterFamilyEp, rowsEp, he, rowCodeEp] using typeIIRowEp_literal h 6 (by decide) (by decide)
  · simpa [unitCharacterRow_as_characterRow,characterFamilyEp, rowsEp, he, rowCodeEp] using typeIIRowEp_literal h 7 (by decide) (by decide)
  · simpa [characterFamilyEp, rowsEp, he, MatrixCertificates.Rank6.Ep0, MatrixCertificates.Rank6.Ep1] using dyadic_four_row_literal h
  · simpa [characterFamilyEp, rowsEp, he, MatrixCertificates.Rank6.Ep0, MatrixCertificates.Rank6.Ep1] using valuation2RowEp_literal h
  · simpa [characterFamilyEp, rowsEp, he, MatrixCertificates.Rank6.Ep0, MatrixCertificates.Rank6.Ep1] using dual_seven_row_literal h
  · simpa [characterFamilyEp, rowsEp, he, MatrixCertificates.Rank6.Ep0, MatrixCertificates.Rank6.Ep1] using real_row_literal h
  · simpa [characterFamilyEp, rowsEp, he, rowCodeEp] using typeIIIRowEp_literal h 0 (by decide)
  · simpa [characterFamilyEp, rowsEp, he, rowCodeEp] using typeIIIRowEp_literal h 1 (by decide)
  · simpa [characterFamilyEp, rowsEp, he, rowCodeEp] using typeIIIRowEp_literal h 2 (by decide)
  · simpa [characterFamilyEp, rowsEp, he, rowCodeEp] using typeIIIRowEp_literal h 3 (by decide)
  · simpa [unitCharacterRow_as_characterRow,characterFamilyEp, rowsEp, he, rowCodeEp] using typeIIRowEp_literal h 4 (by decide) (by decide)
  · simpa [unitCharacterRow_as_characterRow,characterFamilyEp, rowsEp, he, rowCodeEp] using typeIIRowEp_literal h 5 (by decide) (by decide)
  · simpa [unitCharacterRow_as_characterRow,characterFamilyEp, rowsEp, he, rowCodeEp] using typeIIRowEp_literal h 6 (by decide) (by decide)
  · simpa [unitCharacterRow_as_characterRow,characterFamilyEp, rowsEp, he, rowCodeEp] using typeIIRowEp_literal h 7 (by decide) (by decide)

theorem original_three_rows {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (Rank6.a (M6 x) (N6 y)) (Rank6.b (M6 x) (N6 y))) :
    valuationParityLinear 3 (Additive.ofMul q) = 0 ∧
      unitCharacterLinear 3 (Additive.ofMul q) = 0 := by
  obtain ⟨hm, hn⟩ := Rank6Descent.lattice_mod_three x y
  exact Rank6Descent.image_three_rows _ _ hm hn hq

theorem original_seven_row {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (Rank6.a (M6 x) (N6 y)) (Rank6.b (M6 x) (N6 y))) :
    unitCharacterLinear 7 (Additive.ofMul q) = 0 := by
  obtain ⟨hm, hn⟩ := Rank6Descent.lattice_mod_seven x y
  exact Rank6Descent.image_seven_row _ _ hm hn hq

theorem partner_seven_row {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (-2 * Rank6.a (M6 x) (N6 y)) (Rank6.c (M6 x) (N6 y))) :
    characterValuationLinear 7 1 (Additive.ofMul q) = 0 := by
  obtain ⟨hm, hn⟩ := Rank6Descent.lattice_mod_seven x y
  exact Rank6Descent.dual_image_seven_row _ _ hm hn hq

include h in
theorem partner_real_row {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (-2 * Rank6.a (M6 x) (N6 y)) (Rank6.c (M6 x) (N6 y))) :
    realSignLinear (Additive.ofMul q) = 0 := by
  have hp (i : Fin 12) : 0 < (h.primes i : ℚ) := by exact_mod_cast (h.prime i).pos
  have hp0 := hp 0
  have hp1 := hp 1
  have hp2 := hp 2
  have hp3 := hp 3
  have hp8 := hp 8
  have hp9 := hp 9
  have hp10 := hp 10
  have hp11 := hp 11
  have hF : 0 < Rank6.F (M6 x) (N6 y) := by
    rw [Rank6PrimeValuations.F_factorization h]
    positivity
  have hJ : 0 < Rank6.J (M6 x) (N6 y) := by
    rw [Rank6PrimeValuations.J_factorization h]
    positivity
  apply realSignLinear_actualImage (a := -2 * Rank6.a (M6 x) (N6 y))
    (b := Rank6.c (M6 x) (N6 y)) _ _ hq
  · simp only [Rank6.a]
    nlinarith
  · simp only [Rank6.c]
    positivity

theorem characterFamilyE_zero (i : Fin 12) {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (Rank6.a (M6 x) (N6 y)) (Rank6.b (M6 x) (N6 y))) :
    characterFamilyE h i (Additive.ofMul q) = 0 := by
  fin_cases i
  · simpa [characterFamilyE] using Rank6TwoDescent.original_image_valuation_row x y hq
  · simpa [characterFamilyE] using (original_three_rows hq).2
  · simpa [characterFamilyE] using (original_three_rows hq).1
  · simpa [characterFamilyE] using original_seven_row hq
  · let : Fact (h.primes 0).Prime := ⟨h.prime 0⟩
    simpa [characterFamilyE] using Rank6PrimeValuations.typeIII_E_image_row h 0 (by decide) hq
  · let : Fact (h.primes 1).Prime := ⟨h.prime 1⟩
    simpa [characterFamilyE] using Rank6PrimeValuations.typeIII_E_image_row h 1 (by decide) hq
  · let : Fact (h.primes 2).Prime := ⟨h.prime 2⟩
    simpa [characterFamilyE] using Rank6PrimeValuations.typeIII_E_image_row h 2 (by decide) hq
  · let : Fact (h.primes 3).Prime := ⟨h.prime 3⟩
    simpa [characterFamilyE] using Rank6PrimeValuations.typeIII_E_image_row h 3 (by decide) hq
  · let : Fact (h.primes 8).Prime := ⟨h.prime 8⟩
    simpa [characterFamilyE] using Rank6PrimeValuations.J_prime_E_image_row h 8 (by decide) hq
  · let : Fact (h.primes 9).Prime := ⟨h.prime 9⟩
    simpa [characterFamilyE] using Rank6PrimeValuations.J_prime_E_image_row h 9 (by decide) hq
  · let : Fact (h.primes 10).Prime := ⟨h.prime 10⟩
    simpa [characterFamilyE] using Rank6PrimeValuations.J_prime_E_image_row h 10 (by decide) hq
  · let : Fact (h.primes 11).Prime := ⟨h.prime 11⟩
    simpa [characterFamilyE] using Rank6PrimeValuations.J_prime_E_image_row h 11 (by decide) hq

theorem columnsE_signedPrimes (p : Fin 12 → ℕ) : columnsE p =
    signedPrimeColumns (primeColumns6E p) := by
  funext j
  fin_cases j <;> norm_num [columnsE, signedPrimeColumns, primeColumns6E, Fin.cons]
  all_goals rfl

theorem columnsEp_signedPrimes (p : Fin 12 → ℕ) : columnsEp p =
    signedPrimeColumns (primeColumns6Ep p) := by
  funext j
  fin_cases j <;> norm_num [columnsEp, signedPrimeColumns, primeColumns6Ep, Fin.cons]
  all_goals rfl

include h

theorem actualImageE_card_upperBound :
    Nat.card (twoIsogenyImage (Rank6.a (M6 x) (N6 y)) (Rank6.b (M6 x) (N6 y))) ≤ 2 ^ 4 := by
  have hambient : ∀ q ∈ twoIsogenyImage (Rank6.a (M6 x) (N6 y)) (Rank6.b (M6 x) (N6 y)),
      Additive.ofMul q ∈ (squareClassLinearMap (columnsE h.primes)).range := by
    intro q hq
    simpa only [columnsE_signedPrimes] using h.actualImageE_mem_signedPrime_range hq
  have hbound := twoIsogenyImage_card_le_verifiedCharacterKernel (Rank6.a (M6 x) (N6 y)) (Rank6.b (M6 x) (N6 y))
    (columnsE h.primes) (rowsE (epsilon h)) hambient (by
      intro row hrow
      rw [rowsE_ofFn] at hrow
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrow
      exact ⟨characterFamilyE h i, characterFamilyE_literal h i,
        fun _ hq => characterFamilyE_zero h i hq⟩)
  have hcard : Nat.card ↥(Binary.kernelSubmodule 12 (rowsE (epsilon h))) = 2 ^ 4 := by
    by_cases he : epsilon h = 1
    · simp only [rowsE, he, ite_true, Nat.card_eq_fintype_card]
      exact Binary.kernelSubmodule_card MatrixCertificates.Rank6.E0_kernel_length
    · simp only [rowsE, he, ite_false, Nat.card_eq_fintype_card]
      exact Binary.kernelSubmodule_card MatrixCertificates.Rank6.E1_kernel_length
  exact hbound.trans (le_of_eq hcard)

theorem actualImageE_card :
    Nat.card (twoIsogenyImage (Rank6.a (M6 x) (N6 y)) (Rank6.b (M6 x) (N6 y))) = 2 ^ 4 :=
  Nat.le_antisymm (actualImageE_card_upperBound h) h.actualImageE_card_lowerBound

theorem characterFamilyEp_zero (i : Fin 12) {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (-2 * Rank6.a (M6 x) (N6 y)) (Rank6.c (M6 x) (N6 y))) :
    characterFamilyEp h i (Additive.ofMul q) = 0 := by
  fin_cases i
  · simpa [characterFamilyEp] using Rank6TwoDescent.dual_image_character_four_row x y hq
  · simpa [characterFamilyEp] using Rank6TwoDescent.dual_image_valuation_row x y hq
  · simpa [characterFamilyEp] using partner_seven_row hq
  · simpa [characterFamilyEp] using partner_real_row h hq
  · let : Fact (h.primes 0).Prime := ⟨h.prime 0⟩
    simpa [characterFamilyEp] using Rank6PrimeValuations.typeIII_Ep_image_row h 0 (by decide) hq
  · let : Fact (h.primes 1).Prime := ⟨h.prime 1⟩
    simpa [characterFamilyEp] using Rank6PrimeValuations.typeIII_Ep_image_row h 1 (by decide) hq
  · let : Fact (h.primes 2).Prime := ⟨h.prime 2⟩
    simpa [characterFamilyEp] using Rank6PrimeValuations.typeIII_Ep_image_row h 2 (by decide) hq
  · let : Fact (h.primes 3).Prime := ⟨h.prime 3⟩
    simpa [characterFamilyEp] using Rank6PrimeValuations.typeIII_Ep_image_row h 3 (by decide) hq
  · let : Fact (h.primes 4).Prime := ⟨h.prime 4⟩
    simpa [characterFamilyEp] using Rank6PrimeValuations.H_prime_Ep_image_row h 4 (by decide) (by decide) hq
  · let : Fact (h.primes 5).Prime := ⟨h.prime 5⟩
    simpa [characterFamilyEp] using Rank6PrimeValuations.H_prime_Ep_image_row h 5 (by decide) (by decide) hq
  · let : Fact (h.primes 6).Prime := ⟨h.prime 6⟩
    simpa [characterFamilyEp] using Rank6PrimeValuations.H_prime_Ep_image_row h 6 (by decide) (by decide) hq
  · let : Fact (h.primes 7).Prime := ⟨h.prime 7⟩
    simpa [characterFamilyEp] using Rank6PrimeValuations.H_prime_Ep_image_row h 7 (by decide) (by decide) hq

theorem actualImageEp_card_upperBound :
    Nat.card (twoIsogenyImage (-2 * Rank6.a (M6 x) (N6 y)) (Rank6.c (M6 x) (N6 y))) ≤ 2 ^ 4 := by
  have hambient : ∀ q ∈ twoIsogenyImage (-2 * Rank6.a (M6 x) (N6 y)) (Rank6.c (M6 x) (N6 y)),
      Additive.ofMul q ∈ (squareClassLinearMap (columnsEp h.primes)).range := by
    intro q hq
    simpa only [columnsEp_signedPrimes] using h.actualImageEp_mem_signedPrime_range hq
  have hbound := twoIsogenyImage_card_le_verifiedCharacterKernel (-2 * Rank6.a (M6 x) (N6 y)) (Rank6.c (M6 x) (N6 y))
    (columnsEp h.primes) (rowsEp (epsilon h)) hambient (by
      intro row hrow
      rw [rowsEp_ofFn] at hrow
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrow
      exact ⟨characterFamilyEp h i, characterFamilyEp_literal h i,
        fun _ hq => characterFamilyEp_zero h i hq⟩)
  have hcard : Nat.card ↥(Binary.kernelSubmodule 12 (rowsEp (epsilon h))) = 2 ^ 4 := by
    by_cases he : epsilon h = 1
    · simp only [rowsEp, he, ite_true, Nat.card_eq_fintype_card]
      exact Binary.kernelSubmodule_card MatrixCertificates.Rank6.Ep0_kernel_length
    · simp only [rowsEp, he, ite_false, Nat.card_eq_fintype_card]
      exact Binary.kernelSubmodule_card MatrixCertificates.Rank6.Ep1_kernel_length
  exact hbound.trans (le_of_eq hcard)

theorem actualImageEp_card :
    Nat.card (twoIsogenyImage (-2 * Rank6.a (M6 x) (N6 y)) (Rank6.c (M6 x) (N6 y))) = 2 ^ 4 :=
  Nat.le_antisymm (actualImageEp_card_upperBound h) h.actualImageEp_card_lowerBound

/-- The actual isogeny images each have sixteen classes. -/
theorem actualImageCardinalities :
    ActualImageCardinalities (Rank6.a (M6 x) (N6 y)) (Rank6.b (M6 x) (N6 y)) 4 4 := by
  constructor
  · exact actualImageE_card h
  · rw [Rank6.isogeny_coefficient_identity]
    exact actualImageEp_card h

/-- Every specialization of the final literal lattice to twelve positive,
distinct primes outside the fixed columns has exact rational rank six. -/
theorem hasExactRank : HasExactRank (Rank6.E (M6 x) (N6 y)) 6 := by
  let : (twoTorsionModel (Rank6.a (M6 x) (N6 y))
    (Rank6.b (M6 x) (N6 y))).IsElliptic := DescentWitnesses.elliptic6E_on_lattice x y
  exact hasExactRank_of_twoIsogeny_image_cardinalities _ _ 6 4 4
    (actualImageCardinalities h) (by decide)

end RankCertificates.Rank6ExactRank
