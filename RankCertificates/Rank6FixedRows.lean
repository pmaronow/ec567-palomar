module

public import RankCertificates.Rank6LiteralRows
public import RankCertificates.PrimePowerCharacters
public import RankCertificates.LocalSeven

@[expose] public section

namespace RankCertificates.Rank6FixedRows

open Rank6CharacterEvaluation Rank6CharacterRows Rank6LiteralRows

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {x y : ℤ} (h : PrimeSpecialization6 x y)

theorem prime_residue_3 (i : Fin 12) :
    (h.primes i : ZMod 3) = ((PrimePatterns.Rank6.outputs i).c : ZMod 3) := by
  have he : ((h.primes i : ℤ) : ZMod 3) =
      ((PrimePatterns.Rank6.outputs i).eval x y : ZMod 3) :=
    congrArg (fun z : ℤ => (z : ZMod 3)) (Rank6ConstantCharacters.prime_int_eq h i)
  rw [Int.cast_natCast] at he
  rw [he]
  simp only [PrimePatterns.AffineForm.eval, Int.cast_add, Int.cast_mul]
  have ha : ((PrimePatterns.Rank6.outputs i).a : ZMod 3) = 0 := by
    fin_cases i <;> decide +kernel
  have hb : ((PrimePatterns.Rank6.outputs i).b : ZMod 3) = 0 := by
    fin_cases i <;> decide +kernel
  simp [ha, hb]

theorem prime_residue_7 (i : Fin 12) :
    (h.primes i : ZMod 7) = ((PrimePatterns.Rank6.outputs i).c : ZMod 7) := by
  have he : ((h.primes i : ℤ) : ZMod 7) =
      ((PrimePatterns.Rank6.outputs i).eval x y : ZMod 7) :=
    congrArg (fun z : ℤ => (z : ZMod 7)) (Rank6ConstantCharacters.prime_int_eq h i)
  rw [Int.cast_natCast] at he
  rw [he]
  simp only [PrimePatterns.AffineForm.eval, Int.cast_add, Int.cast_mul]
  have ha : ((PrimePatterns.Rank6.outputs i).a : ZMod 7) = 0 := by
    fin_cases i <;> decide +kernel
  have hb : ((PrimePatterns.Rank6.outputs i).b : ZMod 7) = 0 := by
    fin_cases i <;> decide +kernel
  simp [ha, hb]

theorem prime_residue_4 (i : Fin 12) :
    (h.primes i : ZMod 4) = ((PrimePatterns.Rank6.outputs i).c : ZMod 4) := by
  have he : ((h.primes i : ℤ) : ZMod 4) =
      ((PrimePatterns.Rank6.outputs i).eval x y : ZMod 4) :=
    congrArg (fun z : ℤ => (z : ZMod 4)) (Rank6ConstantCharacters.prime_int_eq h i)
  rw [Int.cast_natCast] at he
  rw [he]
  simp only [PrimePatterns.AffineForm.eval, Int.cast_add, Int.cast_mul]
  have ha : ((PrimePatterns.Rank6.outputs i).a : ZMod 4) = 0 := by
    fin_cases i <;> decide +kernel
  have hb : ((PrimePatterns.Rank6.outputs i).b : ZMod 4) = 0 := by
    fin_cases i <;> decide +kernel
  simp [ha, hb]

def primeBit3 : Fin 12 → ZMod 2 := ![0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1]

theorem prime_character_3 (i : Fin 12) :
    unitCharacterParity 3 (Additive.ofMul (rationalSquareClass (h.primes i : ℚ))) =
      primeBit3 i := by
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  rw [MovingPrimeCharacters.unitCharacterParity_prime_other 3 (h.primes i)
    (h.outside i 3 (by simp)).symm]
  have he : legendreSym 3 (h.primes i : ℤ) =
      legendreSym 3 (PrimePatterns.Rank6.outputs i).c :=
    MovingPrimeCharacters.legendre_eq_of_residue_eq 3 (by
      simpa only [Int.cast_natCast] using prime_residue_3 h i)
  rw [he]
  fin_cases i <;> norm_num [PrimePatterns.Rank6.outputs, primeBit3, quadraticCharacterBit]

def primeBit7 : Fin 12 → ZMod 2 := ![1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1]

theorem prime_character_7 (i : Fin 12) :
    unitCharacterParity 7 (Additive.ofMul (rationalSquareClass (h.primes i : ℚ))) =
      primeBit7 i := by
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  rw [MovingPrimeCharacters.unitCharacterParity_prime_other 7 (h.primes i)
    (h.outside i 7 (by simp)).symm]
  have he : legendreSym 7 (h.primes i : ℤ) =
      legendreSym 7 (PrimePatterns.Rank6.outputs i).c :=
    MovingPrimeCharacters.legendre_eq_of_residue_eq 7 (by
      simpa only [Int.cast_natCast] using prime_residue_7 h i)
  rw [he]
  fin_cases i <;> norm_num [PrimePatterns.Rank6.outputs, primeBit7, quadraticCharacterBit]

theorem prime_valuation_bit (p : ℕ) (hp : p.Prime) (i : Fin 12)
    (hne : p ≠ h.primes i) :
    primeParity p hp (Additive.ofMul (rationalSquareClass (h.primes i : ℚ))) = 0 := by
  have hv := primeParity_prime (q := h.primes i) hp (h.prime i)
  simpa only [ite_eq_right hne] using hv

theorem dyadic_int_character (z : ℤ) (hd : ¬ (2 : ℤ) ∣ z) :
    PrimePowerCharacters.dyadicCharacter4Linear
      (Additive.ofMul (rationalSquareClass (z : ℚ))) =
      quadraticCharacterBit (ZMod.χ₄ (z : ZMod 4)) := by
  have hn : (z : ℚ) ≠ 0 := by
    exact_mod_cast (show z ≠ 0 from fun hz => hd (hz ▸ dvd_zero _))
  change PrimePowerCharacters.powerCharacterParity 2 2 ZMod.χ₄ ZMod.isQuadratic_χ₄ _ = _
  rw [PrimePowerCharacters.powerCharacterParity_apply 2 2 _ _ hn]
  unfold PrimePowerCharacters.powerCharacter
  rw [PrimePowerResidues.unitResiduePow_int_of_not_dvd 2 2 z hd]

theorem dyadic_self_character :
    PrimePowerCharacters.dyadicCharacter4Linear
      (Additive.ofMul (rationalSquareClass (2 : ℚ))) = 0 := by
  change PrimePowerCharacters.powerCharacterParity 2 2 ZMod.χ₄ ZMod.isQuadratic_χ₄ _ = _
  rw [PrimePowerCharacters.powerCharacterParity_apply 2 2 _ _ (by norm_num)]
  unfold PrimePowerCharacters.powerCharacter
  have hs := PrimePowerResidues.unitResiduePow_prime_self 2 2
  norm_num only [Nat.cast_ofNat] at hs
  rw [hs, map_one, quadraticCharacterBit_one]

theorem dyadic_prime_character (i : Fin 12) :
    PrimePowerCharacters.dyadicCharacter4Linear
      (Additive.ofMul (rationalSquareClass (h.primes i : ℚ))) =
      quadraticCharacterBit (ZMod.χ₄ ((PrimePatterns.Rank6.outputs i).c : ZMod 4)) := by
  have hp : (h.primes i).Prime := h.prime i
  have hd : ¬ (2 : ℤ) ∣ (h.primes i : ℤ) := by
    have hnat : ¬ 2 ∣ h.primes i := by
      rw [Nat.prime_dvd_prime_iff_eq (by decide) hp]
      exact (h.outside i 2 (by simp)).symm
    exact_mod_cast hnat
  have hv := dyadic_int_character (h.primes i : ℤ) hd
  norm_cast at hv
  rw [prime_residue_4 h i] at hv
  exact hv

theorem valuation2RowE_literal :
    squareClassCharacterRow (valuationParityLinear 2) (columnsE h.primes) =
      Binary.vector 12 2 := by
  funext j
  fin_cases j
  · change primeParity 2 (Fact.out : Nat.Prime 2)
      (Additive.ofMul (rationalSquareClass (-1 : ℚ))) = 0
    exact primeParity_neg_one _
  · change primeParity 2 (Fact.out : Nat.Prime 2)
      (Additive.ofMul (rationalSquareClass (2 : ℚ))) = 1
    have hv := primeParity_prime (p := 2) (q := 2) (show Nat.Prime 2 by decide)
      (show Nat.Prime 2 by decide)
    norm_num at hv
    exact hv
  · change primeParity 2 (Fact.out : Nat.Prime 2)
      (Additive.ofMul (rationalSquareClass (3 : ℚ))) = 0
    have hv := primeParity_prime (p := 2) (q := 3) (show Nat.Prime 2 by decide)
      (show Nat.Prime 3 by decide)
    norm_num at hv
    exact hv
  · change primeParity 2 (Fact.out : Nat.Prime 2)
      (Additive.ofMul (rationalSquareClass (7 : ℚ))) = 0
    have hv := primeParity_prime (p := 2) (q := 7) (show Nat.Prime 2 by decide)
      (show Nat.Prime 7 by decide)
    norm_num at hv
    exact hv
  · change primeParity 2 (Fact.out : Nat.Prime 2)
      (Additive.ofMul (rationalSquareClass (h.primes 0 : ℚ))) = 0
    exact prime_valuation_bit h 2 (by decide) 0 (h.outside 0 2 (by simp)).symm
  · change primeParity 2 (Fact.out : Nat.Prime 2)
      (Additive.ofMul (rationalSquareClass (h.primes 1 : ℚ))) = 0
    exact prime_valuation_bit h 2 (by decide) 1 (h.outside 1 2 (by simp)).symm
  · change primeParity 2 (Fact.out : Nat.Prime 2)
      (Additive.ofMul (rationalSquareClass (h.primes 2 : ℚ))) = 0
    exact prime_valuation_bit h 2 (by decide) 2 (h.outside 2 2 (by simp)).symm
  · change primeParity 2 (Fact.out : Nat.Prime 2)
      (Additive.ofMul (rationalSquareClass (h.primes 3 : ℚ))) = 0
    exact prime_valuation_bit h 2 (by decide) 3 (h.outside 3 2 (by simp)).symm
  · change primeParity 2 (Fact.out : Nat.Prime 2)
      (Additive.ofMul (rationalSquareClass (h.primes 4 : ℚ))) = 0
    exact prime_valuation_bit h 2 (by decide) 4 (h.outside 4 2 (by simp)).symm
  · change primeParity 2 (Fact.out : Nat.Prime 2)
      (Additive.ofMul (rationalSquareClass (h.primes 5 : ℚ))) = 0
    exact prime_valuation_bit h 2 (by decide) 5 (h.outside 5 2 (by simp)).symm
  · change primeParity 2 (Fact.out : Nat.Prime 2)
      (Additive.ofMul (rationalSquareClass (h.primes 6 : ℚ))) = 0
    exact prime_valuation_bit h 2 (by decide) 6 (h.outside 6 2 (by simp)).symm
  · change primeParity 2 (Fact.out : Nat.Prime 2)
      (Additive.ofMul (rationalSquareClass (h.primes 7 : ℚ))) = 0
    exact prime_valuation_bit h 2 (by decide) 7 (h.outside 7 2 (by simp)).symm

theorem valuation3RowE_literal :
    squareClassCharacterRow (valuationParityLinear 3) (columnsE h.primes) =
      Binary.vector 12 4 := by
  funext j
  fin_cases j
  · change primeParity 3 (Fact.out : Nat.Prime 3)
      (Additive.ofMul (rationalSquareClass (-1 : ℚ))) = 0
    exact primeParity_neg_one _
  · change primeParity 3 (Fact.out : Nat.Prime 3)
      (Additive.ofMul (rationalSquareClass (2 : ℚ))) = 0
    have hv := primeParity_prime (p := 3) (q := 2) (show Nat.Prime 3 by decide)
      (show Nat.Prime 2 by decide)
    norm_num at hv
    exact hv
  · change primeParity 3 (Fact.out : Nat.Prime 3)
      (Additive.ofMul (rationalSquareClass (3 : ℚ))) = 1
    have hv := primeParity_prime (p := 3) (q := 3) (show Nat.Prime 3 by decide)
      (show Nat.Prime 3 by decide)
    norm_num at hv
    exact hv
  · change primeParity 3 (Fact.out : Nat.Prime 3)
      (Additive.ofMul (rationalSquareClass (7 : ℚ))) = 0
    have hv := primeParity_prime (p := 3) (q := 7) (show Nat.Prime 3 by decide)
      (show Nat.Prime 7 by decide)
    norm_num at hv
    exact hv
  · change primeParity 3 (Fact.out : Nat.Prime 3)
      (Additive.ofMul (rationalSquareClass (h.primes 0 : ℚ))) = 0
    exact prime_valuation_bit h 3 (by decide) 0 (h.outside 0 3 (by simp)).symm
  · change primeParity 3 (Fact.out : Nat.Prime 3)
      (Additive.ofMul (rationalSquareClass (h.primes 1 : ℚ))) = 0
    exact prime_valuation_bit h 3 (by decide) 1 (h.outside 1 3 (by simp)).symm
  · change primeParity 3 (Fact.out : Nat.Prime 3)
      (Additive.ofMul (rationalSquareClass (h.primes 2 : ℚ))) = 0
    exact prime_valuation_bit h 3 (by decide) 2 (h.outside 2 3 (by simp)).symm
  · change primeParity 3 (Fact.out : Nat.Prime 3)
      (Additive.ofMul (rationalSquareClass (h.primes 3 : ℚ))) = 0
    exact prime_valuation_bit h 3 (by decide) 3 (h.outside 3 3 (by simp)).symm
  · change primeParity 3 (Fact.out : Nat.Prime 3)
      (Additive.ofMul (rationalSquareClass (h.primes 4 : ℚ))) = 0
    exact prime_valuation_bit h 3 (by decide) 4 (h.outside 4 3 (by simp)).symm
  · change primeParity 3 (Fact.out : Nat.Prime 3)
      (Additive.ofMul (rationalSquareClass (h.primes 5 : ℚ))) = 0
    exact prime_valuation_bit h 3 (by decide) 5 (h.outside 5 3 (by simp)).symm
  · change primeParity 3 (Fact.out : Nat.Prime 3)
      (Additive.ofMul (rationalSquareClass (h.primes 6 : ℚ))) = 0
    exact prime_valuation_bit h 3 (by decide) 6 (h.outside 6 3 (by simp)).symm
  · change primeParity 3 (Fact.out : Nat.Prime 3)
      (Additive.ofMul (rationalSquareClass (h.primes 7 : ℚ))) = 0
    exact prime_valuation_bit h 3 (by decide) 7 (h.outside 7 3 (by simp)).symm

theorem valuation2RowEp_literal :
    squareClassCharacterRow (valuationParityLinear 2) (columnsEp h.primes) =
      Binary.vector 12 2 := by
  funext j
  fin_cases j
  · change primeParity 2 (Fact.out : Nat.Prime 2)
      (Additive.ofMul (rationalSquareClass (-1 : ℚ))) = 0
    exact primeParity_neg_one _
  · change primeParity 2 (Fact.out : Nat.Prime 2)
      (Additive.ofMul (rationalSquareClass (2 : ℚ))) = 1
    have hv := primeParity_prime (p := 2) (q := 2) (show Nat.Prime 2 by decide)
      (show Nat.Prime 2 by decide)
    norm_num at hv
    exact hv
  · change primeParity 2 (Fact.out : Nat.Prime 2)
      (Additive.ofMul (rationalSquareClass (3 : ℚ))) = 0
    have hv := primeParity_prime (p := 2) (q := 3) (show Nat.Prime 2 by decide)
      (show Nat.Prime 3 by decide)
    norm_num at hv
    exact hv
  · change primeParity 2 (Fact.out : Nat.Prime 2)
      (Additive.ofMul (rationalSquareClass (7 : ℚ))) = 0
    have hv := primeParity_prime (p := 2) (q := 7) (show Nat.Prime 2 by decide)
      (show Nat.Prime 7 by decide)
    norm_num at hv
    exact hv
  · change primeParity 2 (Fact.out : Nat.Prime 2)
      (Additive.ofMul (rationalSquareClass (h.primes 0 : ℚ))) = 0
    exact prime_valuation_bit h 2 (by decide) 0 (h.outside 0 2 (by simp)).symm
  · change primeParity 2 (Fact.out : Nat.Prime 2)
      (Additive.ofMul (rationalSquareClass (h.primes 1 : ℚ))) = 0
    exact prime_valuation_bit h 2 (by decide) 1 (h.outside 1 2 (by simp)).symm
  · change primeParity 2 (Fact.out : Nat.Prime 2)
      (Additive.ofMul (rationalSquareClass (h.primes 2 : ℚ))) = 0
    exact prime_valuation_bit h 2 (by decide) 2 (h.outside 2 2 (by simp)).symm
  · change primeParity 2 (Fact.out : Nat.Prime 2)
      (Additive.ofMul (rationalSquareClass (h.primes 3 : ℚ))) = 0
    exact prime_valuation_bit h 2 (by decide) 3 (h.outside 3 2 (by simp)).symm
  · change primeParity 2 (Fact.out : Nat.Prime 2)
      (Additive.ofMul (rationalSquareClass (h.primes 8 : ℚ))) = 0
    exact prime_valuation_bit h 2 (by decide) 8 (h.outside 8 2 (by simp)).symm
  · change primeParity 2 (Fact.out : Nat.Prime 2)
      (Additive.ofMul (rationalSquareClass (h.primes 9 : ℚ))) = 0
    exact prime_valuation_bit h 2 (by decide) 9 (h.outside 9 2 (by simp)).symm
  · change primeParity 2 (Fact.out : Nat.Prime 2)
      (Additive.ofMul (rationalSquareClass (h.primes 10 : ℚ))) = 0
    exact prime_valuation_bit h 2 (by decide) 10 (h.outside 10 2 (by simp)).symm
  · change primeParity 2 (Fact.out : Nat.Prime 2)
      (Additive.ofMul (rationalSquareClass (h.primes 11 : ℚ))) = 0
    exact prime_valuation_bit h 2 (by decide) 11 (h.outside 11 2 (by simp)).symm

theorem valuation3RowEp_literal :
    squareClassCharacterRow (valuationParityLinear 3) (columnsEp h.primes) =
      Binary.vector 12 4 := by
  funext j
  fin_cases j
  · change primeParity 3 (Fact.out : Nat.Prime 3)
      (Additive.ofMul (rationalSquareClass (-1 : ℚ))) = 0
    exact primeParity_neg_one _
  · change primeParity 3 (Fact.out : Nat.Prime 3)
      (Additive.ofMul (rationalSquareClass (2 : ℚ))) = 0
    have hv := primeParity_prime (p := 3) (q := 2) (show Nat.Prime 3 by decide)
      (show Nat.Prime 2 by decide)
    norm_num at hv
    exact hv
  · change primeParity 3 (Fact.out : Nat.Prime 3)
      (Additive.ofMul (rationalSquareClass (3 : ℚ))) = 1
    have hv := primeParity_prime (p := 3) (q := 3) (show Nat.Prime 3 by decide)
      (show Nat.Prime 3 by decide)
    norm_num at hv
    exact hv
  · change primeParity 3 (Fact.out : Nat.Prime 3)
      (Additive.ofMul (rationalSquareClass (7 : ℚ))) = 0
    have hv := primeParity_prime (p := 3) (q := 7) (show Nat.Prime 3 by decide)
      (show Nat.Prime 7 by decide)
    norm_num at hv
    exact hv
  · change primeParity 3 (Fact.out : Nat.Prime 3)
      (Additive.ofMul (rationalSquareClass (h.primes 0 : ℚ))) = 0
    exact prime_valuation_bit h 3 (by decide) 0 (h.outside 0 3 (by simp)).symm
  · change primeParity 3 (Fact.out : Nat.Prime 3)
      (Additive.ofMul (rationalSquareClass (h.primes 1 : ℚ))) = 0
    exact prime_valuation_bit h 3 (by decide) 1 (h.outside 1 3 (by simp)).symm
  · change primeParity 3 (Fact.out : Nat.Prime 3)
      (Additive.ofMul (rationalSquareClass (h.primes 2 : ℚ))) = 0
    exact prime_valuation_bit h 3 (by decide) 2 (h.outside 2 3 (by simp)).symm
  · change primeParity 3 (Fact.out : Nat.Prime 3)
      (Additive.ofMul (rationalSquareClass (h.primes 3 : ℚ))) = 0
    exact prime_valuation_bit h 3 (by decide) 3 (h.outside 3 3 (by simp)).symm
  · change primeParity 3 (Fact.out : Nat.Prime 3)
      (Additive.ofMul (rationalSquareClass (h.primes 8 : ℚ))) = 0
    exact prime_valuation_bit h 3 (by decide) 8 (h.outside 8 3 (by simp)).symm
  · change primeParity 3 (Fact.out : Nat.Prime 3)
      (Additive.ofMul (rationalSquareClass (h.primes 9 : ℚ))) = 0
    exact prime_valuation_bit h 3 (by decide) 9 (h.outside 9 3 (by simp)).symm
  · change primeParity 3 (Fact.out : Nat.Prime 3)
      (Additive.ofMul (rationalSquareClass (h.primes 10 : ℚ))) = 0
    exact prime_valuation_bit h 3 (by decide) 10 (h.outside 10 3 (by simp)).symm
  · change primeParity 3 (Fact.out : Nat.Prime 3)
      (Additive.ofMul (rationalSquareClass (h.primes 11 : ℚ))) = 0
    exact prime_valuation_bit h 3 (by decide) 11 (h.outside 11 3 (by simp)).symm

theorem valuation7RowEp_literal :
    squareClassCharacterRow (valuationParityLinear 7) (columnsEp h.primes) =
      Binary.vector 12 8 := by
  funext j
  fin_cases j
  · change primeParity 7 (Fact.out : Nat.Prime 7)
      (Additive.ofMul (rationalSquareClass (-1 : ℚ))) = 0
    exact primeParity_neg_one _
  · change primeParity 7 (Fact.out : Nat.Prime 7)
      (Additive.ofMul (rationalSquareClass (2 : ℚ))) = 0
    have hv := primeParity_prime (p := 7) (q := 2) (show Nat.Prime 7 by decide)
      (show Nat.Prime 2 by decide)
    norm_num at hv
    exact hv
  · change primeParity 7 (Fact.out : Nat.Prime 7)
      (Additive.ofMul (rationalSquareClass (3 : ℚ))) = 0
    have hv := primeParity_prime (p := 7) (q := 3) (show Nat.Prime 7 by decide)
      (show Nat.Prime 3 by decide)
    norm_num at hv
    exact hv
  · change primeParity 7 (Fact.out : Nat.Prime 7)
      (Additive.ofMul (rationalSquareClass (7 : ℚ))) = 1
    have hv := primeParity_prime (p := 7) (q := 7) (show Nat.Prime 7 by decide)
      (show Nat.Prime 7 by decide)
    norm_num at hv
    exact hv
  · change primeParity 7 (Fact.out : Nat.Prime 7)
      (Additive.ofMul (rationalSquareClass (h.primes 0 : ℚ))) = 0
    exact prime_valuation_bit h 7 (by decide) 0 (h.outside 0 7 (by simp)).symm
  · change primeParity 7 (Fact.out : Nat.Prime 7)
      (Additive.ofMul (rationalSquareClass (h.primes 1 : ℚ))) = 0
    exact prime_valuation_bit h 7 (by decide) 1 (h.outside 1 7 (by simp)).symm
  · change primeParity 7 (Fact.out : Nat.Prime 7)
      (Additive.ofMul (rationalSquareClass (h.primes 2 : ℚ))) = 0
    exact prime_valuation_bit h 7 (by decide) 2 (h.outside 2 7 (by simp)).symm
  · change primeParity 7 (Fact.out : Nat.Prime 7)
      (Additive.ofMul (rationalSquareClass (h.primes 3 : ℚ))) = 0
    exact prime_valuation_bit h 7 (by decide) 3 (h.outside 3 7 (by simp)).symm
  · change primeParity 7 (Fact.out : Nat.Prime 7)
      (Additive.ofMul (rationalSquareClass (h.primes 8 : ℚ))) = 0
    exact prime_valuation_bit h 7 (by decide) 8 (h.outside 8 7 (by simp)).symm
  · change primeParity 7 (Fact.out : Nat.Prime 7)
      (Additive.ofMul (rationalSquareClass (h.primes 9 : ℚ))) = 0
    exact prime_valuation_bit h 7 (by decide) 9 (h.outside 9 7 (by simp)).symm
  · change primeParity 7 (Fact.out : Nat.Prime 7)
      (Additive.ofMul (rationalSquareClass (h.primes 10 : ℚ))) = 0
    exact prime_valuation_bit h 7 (by decide) 10 (h.outside 10 7 (by simp)).symm
  · change primeParity 7 (Fact.out : Nat.Prime 7)
      (Additive.ofMul (rationalSquareClass (h.primes 11 : ℚ))) = 0
    exact prime_valuation_bit h 7 (by decide) 11 (h.outside 11 7 (by simp)).symm

theorem character3RowE_literal :
    unitCharacterRow 3 (columnsE h.primes) = Binary.vector 12 3875 := by
  funext j
  fin_cases j
  · change unitCharacterParity 3 (Additive.ofMul (rationalSquareClass (-1 : ℚ))) = 1
    have hv := unitCharacterParity_int_of_not_dvd 3
      (show ¬ (3 : ℤ) ∣ (-1) by norm_num)
    norm_num [quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 3 (Additive.ofMul (rationalSquareClass (2 : ℚ))) = 1
    have hv := unitCharacterParity_int_of_not_dvd 3
      (show ¬ (3 : ℤ) ∣ (2) by norm_num)
    norm_num [quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 3 (Additive.ofMul (rationalSquareClass (3 : ℚ))) = 0
    exact unitCharacterParity_prime_self 3
  · change unitCharacterParity 3 (Additive.ofMul (rationalSquareClass (7 : ℚ))) = 0
    have hv := unitCharacterParity_int_of_not_dvd 3
      (show ¬ (3 : ℤ) ∣ (7) by norm_num)
    norm_num [quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 3 (Additive.ofMul (rationalSquareClass (h.primes 0 : ℚ))) = 0
    have hv := prime_character_3 h 0
    norm_num [primeBit3] at hv
    exact hv
  · change unitCharacterParity 3 (Additive.ofMul (rationalSquareClass (h.primes 1 : ℚ))) = 1
    have hv := prime_character_3 h 1
    norm_num [primeBit3] at hv
    exact hv
  · change unitCharacterParity 3 (Additive.ofMul (rationalSquareClass (h.primes 2 : ℚ))) = 0
    have hv := prime_character_3 h 2
    norm_num [primeBit3] at hv
    exact hv
  · change unitCharacterParity 3 (Additive.ofMul (rationalSquareClass (h.primes 3 : ℚ))) = 0
    have hv := prime_character_3 h 3
    norm_num [primeBit3] at hv
    exact hv
  · change unitCharacterParity 3 (Additive.ofMul (rationalSquareClass (h.primes 4 : ℚ))) = 1
    have hv := prime_character_3 h 4
    norm_num [primeBit3] at hv
    exact hv
  · change unitCharacterParity 3 (Additive.ofMul (rationalSquareClass (h.primes 5 : ℚ))) = 1
    have hv := prime_character_3 h 5
    norm_num [primeBit3] at hv
    exact hv
  · change unitCharacterParity 3 (Additive.ofMul (rationalSquareClass (h.primes 6 : ℚ))) = 1
    have hv := prime_character_3 h 6
    norm_num [primeBit3] at hv
    exact hv
  · change unitCharacterParity 3 (Additive.ofMul (rationalSquareClass (h.primes 7 : ℚ))) = 1
    have hv := prime_character_3 h 7
    norm_num [primeBit3] at hv
    exact hv

theorem character7RowE_literal :
    unitCharacterRow 7 (columnsE h.primes) = Binary.vector 12 1557 := by
  funext j
  fin_cases j
  · change unitCharacterParity 7 (Additive.ofMul (rationalSquareClass (-1 : ℚ))) = 1
    have hv := unitCharacterParity_int_of_not_dvd 7
      (show ¬ (7 : ℤ) ∣ (-1) by norm_num)
    norm_num [quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 7 (Additive.ofMul (rationalSquareClass (2 : ℚ))) = 0
    have hv := unitCharacterParity_int_of_not_dvd 7
      (show ¬ (7 : ℤ) ∣ (2) by norm_num)
    norm_num [quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 7 (Additive.ofMul (rationalSquareClass (3 : ℚ))) = 1
    have hv := unitCharacterParity_int_of_not_dvd 7
      (show ¬ (7 : ℤ) ∣ (3) by norm_num)
    norm_num [quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 7 (Additive.ofMul (rationalSquareClass (7 : ℚ))) = 0
    exact unitCharacterParity_prime_self 7
  · change unitCharacterParity 7 (Additive.ofMul (rationalSquareClass (h.primes 0 : ℚ))) = 1
    have hv := prime_character_7 h 0
    norm_num [primeBit7] at hv
    exact hv
  · change unitCharacterParity 7 (Additive.ofMul (rationalSquareClass (h.primes 1 : ℚ))) = 0
    have hv := prime_character_7 h 1
    norm_num [primeBit7] at hv
    exact hv
  · change unitCharacterParity 7 (Additive.ofMul (rationalSquareClass (h.primes 2 : ℚ))) = 0
    have hv := prime_character_7 h 2
    norm_num [primeBit7] at hv
    exact hv
  · change unitCharacterParity 7 (Additive.ofMul (rationalSquareClass (h.primes 3 : ℚ))) = 0
    have hv := prime_character_7 h 3
    norm_num [primeBit7] at hv
    exact hv
  · change unitCharacterParity 7 (Additive.ofMul (rationalSquareClass (h.primes 4 : ℚ))) = 0
    have hv := prime_character_7 h 4
    norm_num [primeBit7] at hv
    exact hv
  · change unitCharacterParity 7 (Additive.ofMul (rationalSquareClass (h.primes 5 : ℚ))) = 1
    have hv := prime_character_7 h 5
    norm_num [primeBit7] at hv
    exact hv
  · change unitCharacterParity 7 (Additive.ofMul (rationalSquareClass (h.primes 6 : ℚ))) = 1
    have hv := prime_character_7 h 6
    norm_num [primeBit7] at hv
    exact hv
  · change unitCharacterParity 7 (Additive.ofMul (rationalSquareClass (h.primes 7 : ℚ))) = 0
    have hv := prime_character_7 h 7
    norm_num [primeBit7] at hv
    exact hv

theorem character7RowEp_literal :
    unitCharacterRow 7 (columnsEp h.primes) = Binary.vector 12 3605 := by
  funext j
  fin_cases j
  · change unitCharacterParity 7 (Additive.ofMul (rationalSquareClass (-1 : ℚ))) = 1
    have hv := unitCharacterParity_int_of_not_dvd 7
      (show ¬ (7 : ℤ) ∣ (-1) by norm_num)
    norm_num [quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 7 (Additive.ofMul (rationalSquareClass (2 : ℚ))) = 0
    have hv := unitCharacterParity_int_of_not_dvd 7
      (show ¬ (7 : ℤ) ∣ (2) by norm_num)
    norm_num [quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 7 (Additive.ofMul (rationalSquareClass (3 : ℚ))) = 1
    have hv := unitCharacterParity_int_of_not_dvd 7
      (show ¬ (7 : ℤ) ∣ (3) by norm_num)
    norm_num [quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 7 (Additive.ofMul (rationalSquareClass (7 : ℚ))) = 0
    exact unitCharacterParity_prime_self 7
  · change unitCharacterParity 7 (Additive.ofMul (rationalSquareClass (h.primes 0 : ℚ))) = 1
    have hv := prime_character_7 h 0
    norm_num [primeBit7] at hv
    exact hv
  · change unitCharacterParity 7 (Additive.ofMul (rationalSquareClass (h.primes 1 : ℚ))) = 0
    have hv := prime_character_7 h 1
    norm_num [primeBit7] at hv
    exact hv
  · change unitCharacterParity 7 (Additive.ofMul (rationalSquareClass (h.primes 2 : ℚ))) = 0
    have hv := prime_character_7 h 2
    norm_num [primeBit7] at hv
    exact hv
  · change unitCharacterParity 7 (Additive.ofMul (rationalSquareClass (h.primes 3 : ℚ))) = 0
    have hv := prime_character_7 h 3
    norm_num [primeBit7] at hv
    exact hv
  · change unitCharacterParity 7 (Additive.ofMul (rationalSquareClass (h.primes 8 : ℚ))) = 0
    have hv := prime_character_7 h 8
    norm_num [primeBit7] at hv
    exact hv
  · change unitCharacterParity 7 (Additive.ofMul (rationalSquareClass (h.primes 9 : ℚ))) = 1
    have hv := prime_character_7 h 9
    norm_num [primeBit7] at hv
    exact hv
  · change unitCharacterParity 7 (Additive.ofMul (rationalSquareClass (h.primes 10 : ℚ))) = 1
    have hv := prime_character_7 h 10
    norm_num [primeBit7] at hv
    exact hv
  · change unitCharacterParity 7 (Additive.ofMul (rationalSquareClass (h.primes 11 : ℚ))) = 1
    have hv := prime_character_7 h 11
    norm_num [primeBit7] at hv
    exact hv

theorem dual_seven_row_literal :
    squareClassCharacterRow (characterValuationLinear 7 1) (columnsEp h.primes) =
      Binary.vector 12 3613 := by
  have hu := congrFun (character7RowEp_literal h)
  have hp := congrFun (valuation7RowEp_literal h)
  funext j
  simp only [squareClassCharacterRow, characterValuationLinear, LinearMap.add_apply, one_smul]
  change unitCharacterRow 7 (columnsEp h.primes) j +
    squareClassCharacterRow (valuationParityLinear 7) (columnsEp h.primes) j = _
  rw [hu j, hp j]
  fin_cases j <;> norm_num [Binary.vector, Binary.scalar, Nat.testBit_eq_decide_div_mod_eq]

 theorem real_row_literal :
    squareClassCharacterRow realSignLinear (columnsEp h.primes) = Binary.vector 12 1 := by
  funext j
  fin_cases j
  · change squareClassSign (Additive.ofMul (rationalSquareClass (-1 : ℚ))) = 1
    exact squareClassSign_neg_one
  · change squareClassSign (Additive.ofMul (rationalSquareClass (2 : ℚ))) = 0
    exact squareClassSign_of_pos (by norm_num)
  · change squareClassSign (Additive.ofMul (rationalSquareClass (3 : ℚ))) = 0
    exact squareClassSign_of_pos (by norm_num)
  · change squareClassSign (Additive.ofMul (rationalSquareClass (7 : ℚ))) = 0
    exact squareClassSign_of_pos (by norm_num)
  · change squareClassSign (Additive.ofMul (rationalSquareClass (h.primes 0 : ℚ))) = 0
    exact squareClassSign_of_pos (by exact_mod_cast (h.prime 0).pos)
  · change squareClassSign (Additive.ofMul (rationalSquareClass (h.primes 1 : ℚ))) = 0
    exact squareClassSign_of_pos (by exact_mod_cast (h.prime 1).pos)
  · change squareClassSign (Additive.ofMul (rationalSquareClass (h.primes 2 : ℚ))) = 0
    exact squareClassSign_of_pos (by exact_mod_cast (h.prime 2).pos)
  · change squareClassSign (Additive.ofMul (rationalSquareClass (h.primes 3 : ℚ))) = 0
    exact squareClassSign_of_pos (by exact_mod_cast (h.prime 3).pos)
  · change squareClassSign (Additive.ofMul (rationalSquareClass (h.primes 8 : ℚ))) = 0
    exact squareClassSign_of_pos (by exact_mod_cast (h.prime 8).pos)
  · change squareClassSign (Additive.ofMul (rationalSquareClass (h.primes 9 : ℚ))) = 0
    exact squareClassSign_of_pos (by exact_mod_cast (h.prime 9).pos)
  · change squareClassSign (Additive.ofMul (rationalSquareClass (h.primes 10 : ℚ))) = 0
    exact squareClassSign_of_pos (by exact_mod_cast (h.prime 10).pos)
  · change squareClassSign (Additive.ofMul (rationalSquareClass (h.primes 11 : ℚ))) = 0
    exact squareClassSign_of_pos (by exact_mod_cast (h.prime 11).pos)

 theorem dyadic_four_row_literal :
    squareClassCharacterRow PrimePowerCharacters.dyadicCharacter4Linear (columnsEp h.primes) =
      Binary.vector 12 1981 := by
  funext j
  fin_cases j
  · change PrimePowerCharacters.dyadicCharacter4Linear
      (Additive.ofMul (rationalSquareClass (-1 : ℚ))) = 1
    have hv := dyadic_int_character (-1) (by norm_num)
    norm_num [ZMod.χ₄_int_eq_if_mod_four, quadraticCharacterBit] at hv
    exact hv
  · change PrimePowerCharacters.dyadicCharacter4Linear
      (Additive.ofMul (rationalSquareClass (2 : ℚ))) = 0
    exact dyadic_self_character
  · change PrimePowerCharacters.dyadicCharacter4Linear
      (Additive.ofMul (rationalSquareClass (3 : ℚ))) = 1
    have hv := dyadic_int_character (3) (by norm_num)
    norm_num [ZMod.χ₄_int_eq_if_mod_four, quadraticCharacterBit] at hv
    exact hv
  · change PrimePowerCharacters.dyadicCharacter4Linear
      (Additive.ofMul (rationalSquareClass (7 : ℚ))) = 1
    have hv := dyadic_int_character (7) (by norm_num)
    norm_num [ZMod.χ₄_int_eq_if_mod_four, quadraticCharacterBit] at hv
    exact hv
  · change PrimePowerCharacters.dyadicCharacter4Linear
      (Additive.ofMul (rationalSquareClass (h.primes 0 : ℚ))) = 1
    have hv := dyadic_prime_character h 0
    norm_num [PrimePatterns.Rank6.outputs, ZMod.χ₄_int_eq_if_mod_four, quadraticCharacterBit] at hv
    exact hv
  · change PrimePowerCharacters.dyadicCharacter4Linear
      (Additive.ofMul (rationalSquareClass (h.primes 1 : ℚ))) = 1
    have hv := dyadic_prime_character h 1
    norm_num [PrimePatterns.Rank6.outputs, ZMod.χ₄_int_eq_if_mod_four, quadraticCharacterBit] at hv
    exact hv
  · change PrimePowerCharacters.dyadicCharacter4Linear
      (Additive.ofMul (rationalSquareClass (h.primes 2 : ℚ))) = 0
    have hv := dyadic_prime_character h 2
    norm_num [PrimePatterns.Rank6.outputs, ZMod.χ₄_int_eq_if_mod_four, quadraticCharacterBit] at hv
    exact hv
  · change PrimePowerCharacters.dyadicCharacter4Linear
      (Additive.ofMul (rationalSquareClass (h.primes 3 : ℚ))) = 1
    have hv := dyadic_prime_character h 3
    norm_num [PrimePatterns.Rank6.outputs, ZMod.χ₄_int_eq_if_mod_four, quadraticCharacterBit] at hv
    exact hv
  · change PrimePowerCharacters.dyadicCharacter4Linear
      (Additive.ofMul (rationalSquareClass (h.primes 8 : ℚ))) = 1
    have hv := dyadic_prime_character h 8
    norm_num [PrimePatterns.Rank6.outputs, ZMod.χ₄_int_eq_if_mod_four, quadraticCharacterBit] at hv
    exact hv
  · change PrimePowerCharacters.dyadicCharacter4Linear
      (Additive.ofMul (rationalSquareClass (h.primes 9 : ℚ))) = 1
    have hv := dyadic_prime_character h 9
    norm_num [PrimePatterns.Rank6.outputs, ZMod.χ₄_int_eq_if_mod_four, quadraticCharacterBit] at hv
    exact hv
  · change PrimePowerCharacters.dyadicCharacter4Linear
      (Additive.ofMul (rationalSquareClass (h.primes 10 : ℚ))) = 1
    have hv := dyadic_prime_character h 10
    norm_num [PrimePatterns.Rank6.outputs, ZMod.χ₄_int_eq_if_mod_four, quadraticCharacterBit] at hv
    exact hv
  · change PrimePowerCharacters.dyadicCharacter4Linear
      (Additive.ofMul (rationalSquareClass (h.primes 11 : ℚ))) = 0
    have hv := dyadic_prime_character h 11
    norm_num [PrimePatterns.Rank6.outputs, ZMod.χ₄_int_eq_if_mod_four, quadraticCharacterBit] at hv
    exact hv

end RankCertificates.Rank6FixedRows
