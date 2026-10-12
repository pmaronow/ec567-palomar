module

public import RankCertificates.Rank5FixedCharacters

@[expose] public section

namespace RankCertificates.Rank5FixedRows

open Rank5CharacterRows Rank5FixedCharacters PrimePowerCharacters

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

variable {x y : ℤ} (h : PrimeSpecialization5 x y)

theorem dyadic4_E_literal : squareClassCharacterRow (dyadicCharacter4Linear) (columnsE h.primes) =
    Binary.vector 12 1669 := by
  funext j
  fin_cases j
  · change (dyadicCharacter4Linear) (Additive.ofMul (rationalSquareClass (-1 : ℚ))) = 1
    have hv := dyadic4_int (-1) (by norm_num)
    norm_num [ZMod.χ₄_int_eq_if_mod_four, quadraticCharacterBit] at hv
    exact hv
  · change (dyadicCharacter4Linear) (Additive.ofMul (rationalSquareClass (2 : ℚ))) = 0
    exact dyadic4_self
  · change (dyadicCharacter4Linear) (Additive.ofMul (rationalSquareClass (3 : ℚ))) = 1
    have hv := dyadic4_int (3) (by norm_num)
    norm_num [ZMod.χ₄_int_eq_if_mod_four, quadraticCharacterBit] at hv
    exact hv
  · change (dyadicCharacter4Linear) (Additive.ofMul (rationalSquareClass (5 : ℚ))) = 0
    have hv := dyadic4_int (5) (by norm_num)
    norm_num [ZMod.χ₄_int_eq_if_mod_four, quadraticCharacterBit] at hv
    exact hv
  · change (dyadicCharacter4Linear) (Additive.ofMul (rationalSquareClass (h.primes 0 : ℚ))) = 0
    have hv := dyadic4_moving h 0
    norm_num [PrimePatterns.Rank5.mod8Units,
      ZMod.χ₄_int_eq_if_mod_four, quadraticCharacterBit] at hv
    exact hv
  · change (dyadicCharacter4Linear) (Additive.ofMul (rationalSquareClass (h.primes 1 : ℚ))) = 0
    have hv := dyadic4_moving h 1
    norm_num [PrimePatterns.Rank5.mod8Units,
      ZMod.χ₄_int_eq_if_mod_four, quadraticCharacterBit] at hv
    exact hv
  · change (dyadicCharacter4Linear) (Additive.ofMul (rationalSquareClass (h.primes 2 : ℚ))) = 0
    have hv := dyadic4_moving h 2
    norm_num [PrimePatterns.Rank5.mod8Units,
      ZMod.χ₄_int_eq_if_mod_four, quadraticCharacterBit] at hv
    exact hv
  · change (dyadicCharacter4Linear) (Additive.ofMul (rationalSquareClass (h.primes 3 : ℚ))) = 1
    have hv := dyadic4_moving h 3
    norm_num [PrimePatterns.Rank5.mod8Units,
      ZMod.χ₄_int_eq_if_mod_four, quadraticCharacterBit] at hv
    exact hv
  · change (dyadicCharacter4Linear) (Additive.ofMul (rationalSquareClass (h.primes 4 : ℚ))) = 0
    have hv := dyadic4_moving h 4
    norm_num [PrimePatterns.Rank5.mod8Units,
      ZMod.χ₄_int_eq_if_mod_four, quadraticCharacterBit] at hv
    exact hv
  · change (dyadicCharacter4Linear) (Additive.ofMul (rationalSquareClass (h.primes 5 : ℚ))) = 1
    have hv := dyadic4_moving h 5
    norm_num [PrimePatterns.Rank5.mod8Units,
      ZMod.χ₄_int_eq_if_mod_four, quadraticCharacterBit] at hv
    exact hv
  · change (dyadicCharacter4Linear) (Additive.ofMul (rationalSquareClass (h.primes 6 : ℚ))) = 1
    have hv := dyadic4_moving h 6
    norm_num [PrimePatterns.Rank5.mod8Units,
      ZMod.χ₄_int_eq_if_mod_four, quadraticCharacterBit] at hv
    exact hv
  · change (dyadicCharacter4Linear) (Additive.ofMul (rationalSquareClass (h.primes 7 : ℚ))) = 0
    have hv := dyadic4_moving h 7
    norm_num [PrimePatterns.Rank5.mod8Units,
      ZMod.χ₄_int_eq_if_mod_four, quadraticCharacterBit] at hv
    exact hv
theorem dyadic8_E_literal : squareClassCharacterRow (dyadicCharacter8Linear) (columnsE h.primes) =
    Binary.vector 12 3948 := by
  funext j
  fin_cases j
  · change (dyadicCharacter8Linear) (Additive.ofMul (rationalSquareClass (-1 : ℚ))) = 0
    have hv := dyadic8_int (-1) (by norm_num)
    norm_num [ZMod.χ₈_int_eq_if_mod_eight, quadraticCharacterBit] at hv
    exact hv
  · change (dyadicCharacter8Linear) (Additive.ofMul (rationalSquareClass (2 : ℚ))) = 0
    exact dyadic8_self
  · change (dyadicCharacter8Linear) (Additive.ofMul (rationalSquareClass (3 : ℚ))) = 1
    have hv := dyadic8_int (3) (by norm_num)
    norm_num [ZMod.χ₈_int_eq_if_mod_eight, quadraticCharacterBit] at hv
    exact hv
  · change (dyadicCharacter8Linear) (Additive.ofMul (rationalSquareClass (5 : ℚ))) = 1
    have hv := dyadic8_int (5) (by norm_num)
    norm_num [ZMod.χ₈_int_eq_if_mod_eight, quadraticCharacterBit] at hv
    exact hv
  · change (dyadicCharacter8Linear) (Additive.ofMul (rationalSquareClass (h.primes 0 : ℚ))) = 0
    have hv := dyadic8_moving h 0
    norm_num [PrimePatterns.Rank5.mod8Units,
      ZMod.χ₈_int_eq_if_mod_eight, quadraticCharacterBit] at hv
    exact hv
  · change (dyadicCharacter8Linear) (Additive.ofMul (rationalSquareClass (h.primes 1 : ℚ))) = 1
    have hv := dyadic8_moving h 1
    norm_num [PrimePatterns.Rank5.mod8Units,
      ZMod.χ₈_int_eq_if_mod_eight, quadraticCharacterBit] at hv
    exact hv
  · change (dyadicCharacter8Linear) (Additive.ofMul (rationalSquareClass (h.primes 2 : ℚ))) = 1
    have hv := dyadic8_moving h 2
    norm_num [PrimePatterns.Rank5.mod8Units,
      ZMod.χ₈_int_eq_if_mod_eight, quadraticCharacterBit] at hv
    exact hv
  · change (dyadicCharacter8Linear) (Additive.ofMul (rationalSquareClass (h.primes 3 : ℚ))) = 0
    have hv := dyadic8_moving h 3
    norm_num [PrimePatterns.Rank5.mod8Units,
      ZMod.χ₈_int_eq_if_mod_eight, quadraticCharacterBit] at hv
    exact hv
  · change (dyadicCharacter8Linear) (Additive.ofMul (rationalSquareClass (h.primes 4 : ℚ))) = 1
    have hv := dyadic8_moving h 4
    norm_num [PrimePatterns.Rank5.mod8Units,
      ZMod.χ₈_int_eq_if_mod_eight, quadraticCharacterBit] at hv
    exact hv
  · change (dyadicCharacter8Linear) (Additive.ofMul (rationalSquareClass (h.primes 5 : ℚ))) = 1
    have hv := dyadic8_moving h 5
    norm_num [PrimePatterns.Rank5.mod8Units,
      ZMod.χ₈_int_eq_if_mod_eight, quadraticCharacterBit] at hv
    exact hv
  · change (dyadicCharacter8Linear) (Additive.ofMul (rationalSquareClass (h.primes 6 : ℚ))) = 1
    have hv := dyadic8_moving h 6
    norm_num [PrimePatterns.Rank5.mod8Units,
      ZMod.χ₈_int_eq_if_mod_eight, quadraticCharacterBit] at hv
    exact hv
  · change (dyadicCharacter8Linear) (Additive.ofMul (rationalSquareClass (h.primes 7 : ℚ))) = 1
    have hv := dyadic8_moving h 7
    norm_num [PrimePatterns.Rank5.mod8Units,
      ZMod.χ₈_int_eq_if_mod_eight, quadraticCharacterBit] at hv
    exact hv
theorem dyadic8_Ep_literal : squareClassCharacterRow (dyadicCharacter8Linear) (columnsEp h.primes) =
    Binary.vector 12 108 := by
  funext j
  fin_cases j
  · change (dyadicCharacter8Linear) (Additive.ofMul (rationalSquareClass (-1 : ℚ))) = 0
    have hv := dyadic8_int (-1) (by norm_num)
    norm_num [ZMod.χ₈_int_eq_if_mod_eight, quadraticCharacterBit] at hv
    exact hv
  · change (dyadicCharacter8Linear) (Additive.ofMul (rationalSquareClass (2 : ℚ))) = 0
    exact dyadic8_self
  · change (dyadicCharacter8Linear) (Additive.ofMul (rationalSquareClass (3 : ℚ))) = 1
    have hv := dyadic8_int (3) (by norm_num)
    norm_num [ZMod.χ₈_int_eq_if_mod_eight, quadraticCharacterBit] at hv
    exact hv
  · change (dyadicCharacter8Linear) (Additive.ofMul (rationalSquareClass (5 : ℚ))) = 1
    have hv := dyadic8_int (5) (by norm_num)
    norm_num [ZMod.χ₈_int_eq_if_mod_eight, quadraticCharacterBit] at hv
    exact hv
  · change (dyadicCharacter8Linear) (Additive.ofMul (rationalSquareClass (h.primes 0 : ℚ))) = 0
    have hv := dyadic8_moving h 0
    norm_num [PrimePatterns.Rank5.mod8Units,
      ZMod.χ₈_int_eq_if_mod_eight, quadraticCharacterBit] at hv
    exact hv
  · change (dyadicCharacter8Linear) (Additive.ofMul (rationalSquareClass (h.primes 1 : ℚ))) = 1
    have hv := dyadic8_moving h 1
    norm_num [PrimePatterns.Rank5.mod8Units,
      ZMod.χ₈_int_eq_if_mod_eight, quadraticCharacterBit] at hv
    exact hv
  · change (dyadicCharacter8Linear) (Additive.ofMul (rationalSquareClass (h.primes 2 : ℚ))) = 1
    have hv := dyadic8_moving h 2
    norm_num [PrimePatterns.Rank5.mod8Units,
      ZMod.χ₈_int_eq_if_mod_eight, quadraticCharacterBit] at hv
    exact hv
  · change (dyadicCharacter8Linear) (Additive.ofMul (rationalSquareClass (h.primes 3 : ℚ))) = 0
    have hv := dyadic8_moving h 3
    norm_num [PrimePatterns.Rank5.mod8Units,
      ZMod.χ₈_int_eq_if_mod_eight, quadraticCharacterBit] at hv
    exact hv
  · change (dyadicCharacter8Linear) (Additive.ofMul (rationalSquareClass (h.primes 8 : ℚ))) = 0
    have hv := dyadic8_moving h 8
    norm_num [PrimePatterns.Rank5.mod8Units,
      ZMod.χ₈_int_eq_if_mod_eight, quadraticCharacterBit] at hv
    exact hv
  · change (dyadicCharacter8Linear) (Additive.ofMul (rationalSquareClass (h.primes 9 : ℚ))) = 0
    have hv := dyadic8_moving h 9
    norm_num [PrimePatterns.Rank5.mod8Units,
      ZMod.χ₈_int_eq_if_mod_eight, quadraticCharacterBit] at hv
    exact hv
  · change (dyadicCharacter8Linear) (Additive.ofMul (rationalSquareClass (h.primes 10 : ℚ))) = 0
    have hv := dyadic8_moving h 10
    norm_num [PrimePatterns.Rank5.mod8Units,
      ZMod.χ₈_int_eq_if_mod_eight, quadraticCharacterBit] at hv
    exact hv
  · change (dyadicCharacter8Linear) (Additive.ofMul (rationalSquareClass (h.primes 11 : ℚ))) = 0
    have hv := dyadic8_moving h 11
    norm_num [PrimePatterns.Rank5.mod8Units,
      ZMod.χ₈_int_eq_if_mod_eight, quadraticCharacterBit] at hv
    exact hv
theorem three_E_literal : squareClassCharacterRow (unitCharacterLinear 3) (columnsE h.primes) =
    Binary.vector 12 267 := by
  funext j
  fin_cases j
  · change (unitCharacterLinear 3) (Additive.ofMul (rationalSquareClass (-1 : ℚ))) = 1
    change unitCharacterParity 3 _ = 1
    have hv := unitCharacterParity_int_of_not_dvd 3 (show ¬ (3 : ℤ) ∣ (-1) by norm_num)
    norm_num [quadraticCharacterBit] at hv
    exact hv
  · change (unitCharacterLinear 3) (Additive.ofMul (rationalSquareClass (2 : ℚ))) = 1
    change unitCharacterParity 3 _ = 1
    have hv := unitCharacterParity_int_of_not_dvd 3 (show ¬ (3 : ℤ) ∣ (2) by norm_num)
    norm_num [quadraticCharacterBit] at hv
    exact hv
  · change (unitCharacterLinear 3) (Additive.ofMul (rationalSquareClass (3 : ℚ))) = 0
    change unitCharacterParity 3 _ = 0
    exact unitCharacterParity_prime_self 3
  · change (unitCharacterLinear 3) (Additive.ofMul (rationalSquareClass (5 : ℚ))) = 1
    change unitCharacterParity 3 _ = 1
    have hv := unitCharacterParity_int_of_not_dvd 3 (show ¬ (3 : ℤ) ∣ (5) by norm_num)
    norm_num [quadraticCharacterBit] at hv
    exact hv
  · change (unitCharacterLinear 3) (Additive.ofMul (rationalSquareClass (h.primes 0 : ℚ))) = 0
    have hv := fixed_moving h 1 0
    norm_num [PrimePatterns.Rank5.retainedPrimes, PrimePatterns.Rank5.outputs,
      quadraticCharacterBit] at hv
    exact hv
  · change (unitCharacterLinear 3) (Additive.ofMul (rationalSquareClass (h.primes 1 : ℚ))) = 0
    have hv := fixed_moving h 1 1
    norm_num [PrimePatterns.Rank5.retainedPrimes, PrimePatterns.Rank5.outputs,
      quadraticCharacterBit] at hv
    exact hv
  · change (unitCharacterLinear 3) (Additive.ofMul (rationalSquareClass (h.primes 2 : ℚ))) = 0
    have hv := fixed_moving h 1 2
    norm_num [PrimePatterns.Rank5.retainedPrimes, PrimePatterns.Rank5.outputs,
      quadraticCharacterBit] at hv
    exact hv
  · change (unitCharacterLinear 3) (Additive.ofMul (rationalSquareClass (h.primes 3 : ℚ))) = 0
    have hv := fixed_moving h 1 3
    norm_num [PrimePatterns.Rank5.retainedPrimes, PrimePatterns.Rank5.outputs,
      quadraticCharacterBit] at hv
    exact hv
  · change (unitCharacterLinear 3) (Additive.ofMul (rationalSquareClass (h.primes 4 : ℚ))) = 1
    have hv := fixed_moving h 1 4
    norm_num [PrimePatterns.Rank5.retainedPrimes, PrimePatterns.Rank5.outputs,
      quadraticCharacterBit] at hv
    exact hv
  · change (unitCharacterLinear 3) (Additive.ofMul (rationalSquareClass (h.primes 5 : ℚ))) = 0
    have hv := fixed_moving h 1 5
    norm_num [PrimePatterns.Rank5.retainedPrimes, PrimePatterns.Rank5.outputs,
      quadraticCharacterBit] at hv
    exact hv
  · change (unitCharacterLinear 3) (Additive.ofMul (rationalSquareClass (h.primes 6 : ℚ))) = 0
    have hv := fixed_moving h 1 6
    norm_num [PrimePatterns.Rank5.retainedPrimes, PrimePatterns.Rank5.outputs,
      quadraticCharacterBit] at hv
    exact hv
  · change (unitCharacterLinear 3) (Additive.ofMul (rationalSquareClass (h.primes 7 : ℚ))) = 0
    have hv := fixed_moving h 1 7
    norm_num [PrimePatterns.Rank5.retainedPrimes, PrimePatterns.Rank5.outputs,
      quadraticCharacterBit] at hv
    exact hv
theorem five_E_literal : squareClassCharacterRow (unitCharacterLinear 5) (columnsE h.primes) =
    Binary.vector 12 3718 := by
  funext j
  fin_cases j
  · change (unitCharacterLinear 5) (Additive.ofMul (rationalSquareClass (-1 : ℚ))) = 0
    change unitCharacterParity 5 _ = 0
    have hv := unitCharacterParity_int_of_not_dvd 5 (show ¬ (5 : ℤ) ∣ (-1) by norm_num)
    norm_num [quadraticCharacterBit] at hv
    exact hv
  · change (unitCharacterLinear 5) (Additive.ofMul (rationalSquareClass (2 : ℚ))) = 1
    change unitCharacterParity 5 _ = 1
    have hv := unitCharacterParity_int_of_not_dvd 5 (show ¬ (5 : ℤ) ∣ (2) by norm_num)
    norm_num [quadraticCharacterBit] at hv
    exact hv
  · change (unitCharacterLinear 5) (Additive.ofMul (rationalSquareClass (3 : ℚ))) = 1
    change unitCharacterParity 5 _ = 1
    have hv := unitCharacterParity_int_of_not_dvd 5 (show ¬ (5 : ℤ) ∣ (3) by norm_num)
    norm_num [quadraticCharacterBit] at hv
    exact hv
  · change (unitCharacterLinear 5) (Additive.ofMul (rationalSquareClass (5 : ℚ))) = 0
    change unitCharacterParity 5 _ = 0
    exact unitCharacterParity_prime_self 5
  · change (unitCharacterLinear 5) (Additive.ofMul (rationalSquareClass (h.primes 0 : ℚ))) = 0
    have hv := fixed_moving h 2 0
    norm_num [PrimePatterns.Rank5.retainedPrimes, PrimePatterns.Rank5.outputs,
      quadraticCharacterBit] at hv
    exact hv
  · change (unitCharacterLinear 5) (Additive.ofMul (rationalSquareClass (h.primes 1 : ℚ))) = 0
    have hv := fixed_moving h 2 1
    norm_num [PrimePatterns.Rank5.retainedPrimes, PrimePatterns.Rank5.outputs,
      quadraticCharacterBit] at hv
    exact hv
  · change (unitCharacterLinear 5) (Additive.ofMul (rationalSquareClass (h.primes 2 : ℚ))) = 0
    have hv := fixed_moving h 2 2
    norm_num [PrimePatterns.Rank5.retainedPrimes, PrimePatterns.Rank5.outputs,
      quadraticCharacterBit] at hv
    exact hv
  · change (unitCharacterLinear 5) (Additive.ofMul (rationalSquareClass (h.primes 3 : ℚ))) = 1
    have hv := fixed_moving h 2 3
    norm_num [PrimePatterns.Rank5.retainedPrimes, PrimePatterns.Rank5.outputs,
      quadraticCharacterBit] at hv
    exact hv
  · change (unitCharacterLinear 5) (Additive.ofMul (rationalSquareClass (h.primes 4 : ℚ))) = 0
    have hv := fixed_moving h 2 4
    norm_num [PrimePatterns.Rank5.retainedPrimes, PrimePatterns.Rank5.outputs,
      quadraticCharacterBit] at hv
    exact hv
  · change (unitCharacterLinear 5) (Additive.ofMul (rationalSquareClass (h.primes 5 : ℚ))) = 1
    have hv := fixed_moving h 2 5
    norm_num [PrimePatterns.Rank5.retainedPrimes, PrimePatterns.Rank5.outputs,
      quadraticCharacterBit] at hv
    exact hv
  · change (unitCharacterLinear 5) (Additive.ofMul (rationalSquareClass (h.primes 6 : ℚ))) = 1
    have hv := fixed_moving h 2 6
    norm_num [PrimePatterns.Rank5.retainedPrimes, PrimePatterns.Rank5.outputs,
      quadraticCharacterBit] at hv
    exact hv
  · change (unitCharacterLinear 5) (Additive.ofMul (rationalSquareClass (h.primes 7 : ℚ))) = 1
    have hv := fixed_moving h 2 7
    norm_num [PrimePatterns.Rank5.retainedPrimes, PrimePatterns.Rank5.outputs,
      quadraticCharacterBit] at hv
    exact hv
theorem five_Ep_literal : squareClassCharacterRow (unitCharacterLinear 5) (columnsEp h.primes) =
    Binary.vector 12 3206 := by
  funext j
  fin_cases j
  · change (unitCharacterLinear 5) (Additive.ofMul (rationalSquareClass (-1 : ℚ))) = 0
    change unitCharacterParity 5 _ = 0
    have hv := unitCharacterParity_int_of_not_dvd 5 (show ¬ (5 : ℤ) ∣ (-1) by norm_num)
    norm_num [quadraticCharacterBit] at hv
    exact hv
  · change (unitCharacterLinear 5) (Additive.ofMul (rationalSquareClass (2 : ℚ))) = 1
    change unitCharacterParity 5 _ = 1
    have hv := unitCharacterParity_int_of_not_dvd 5 (show ¬ (5 : ℤ) ∣ (2) by norm_num)
    norm_num [quadraticCharacterBit] at hv
    exact hv
  · change (unitCharacterLinear 5) (Additive.ofMul (rationalSquareClass (3 : ℚ))) = 1
    change unitCharacterParity 5 _ = 1
    have hv := unitCharacterParity_int_of_not_dvd 5 (show ¬ (5 : ℤ) ∣ (3) by norm_num)
    norm_num [quadraticCharacterBit] at hv
    exact hv
  · change (unitCharacterLinear 5) (Additive.ofMul (rationalSquareClass (5 : ℚ))) = 0
    change unitCharacterParity 5 _ = 0
    exact unitCharacterParity_prime_self 5
  · change (unitCharacterLinear 5) (Additive.ofMul (rationalSquareClass (h.primes 0 : ℚ))) = 0
    have hv := fixed_moving h 2 0
    norm_num [PrimePatterns.Rank5.retainedPrimes, PrimePatterns.Rank5.outputs,
      quadraticCharacterBit] at hv
    exact hv
  · change (unitCharacterLinear 5) (Additive.ofMul (rationalSquareClass (h.primes 1 : ℚ))) = 0
    have hv := fixed_moving h 2 1
    norm_num [PrimePatterns.Rank5.retainedPrimes, PrimePatterns.Rank5.outputs,
      quadraticCharacterBit] at hv
    exact hv
  · change (unitCharacterLinear 5) (Additive.ofMul (rationalSquareClass (h.primes 2 : ℚ))) = 0
    have hv := fixed_moving h 2 2
    norm_num [PrimePatterns.Rank5.retainedPrimes, PrimePatterns.Rank5.outputs,
      quadraticCharacterBit] at hv
    exact hv
  · change (unitCharacterLinear 5) (Additive.ofMul (rationalSquareClass (h.primes 3 : ℚ))) = 1
    have hv := fixed_moving h 2 3
    norm_num [PrimePatterns.Rank5.retainedPrimes, PrimePatterns.Rank5.outputs,
      quadraticCharacterBit] at hv
    exact hv
  · change (unitCharacterLinear 5) (Additive.ofMul (rationalSquareClass (h.primes 8 : ℚ))) = 0
    have hv := fixed_moving h 2 8
    norm_num [PrimePatterns.Rank5.retainedPrimes, PrimePatterns.Rank5.outputs,
      quadraticCharacterBit] at hv
    exact hv
  · change (unitCharacterLinear 5) (Additive.ofMul (rationalSquareClass (h.primes 9 : ℚ))) = 0
    have hv := fixed_moving h 2 9
    norm_num [PrimePatterns.Rank5.retainedPrimes, PrimePatterns.Rank5.outputs,
      quadraticCharacterBit] at hv
    exact hv
  · change (unitCharacterLinear 5) (Additive.ofMul (rationalSquareClass (h.primes 10 : ℚ))) = 1
    have hv := fixed_moving h 2 10
    norm_num [PrimePatterns.Rank5.retainedPrimes, PrimePatterns.Rank5.outputs,
      quadraticCharacterBit] at hv
    exact hv
  · change (unitCharacterLinear 5) (Additive.ofMul (rationalSquareClass (h.primes 11 : ℚ))) = 1
    have hv := fixed_moving h 2 11
    norm_num [PrimePatterns.Rank5.retainedPrimes, PrimePatterns.Rank5.outputs,
      quadraticCharacterBit] at hv
    exact hv

theorem valuation3_E_literal : squareClassCharacterRow (valuationParityLinear 3)
    (columnsE h.primes) = Binary.vector 12 4 := by
  funext j
  fin_cases j
  · change primeParity 3 (by decide) (Additive.ofMul (rationalSquareClass (-1 : ℚ))) = 0
    exact primeParity_neg_one (by decide)
  · change primeParity 3 (by decide) (Additive.ofMul (rationalSquareClass (2 : ℚ))) = 0
    have hv := primeParity_prime (show Nat.Prime 3 by decide) (show Nat.Prime 2 by decide)
    norm_num at hv
    exact hv
  · change primeParity 3 (by decide) (Additive.ofMul (rationalSquareClass (3 : ℚ))) = 1
    have hv := primeParity_prime (show Nat.Prime 3 by decide) (show Nat.Prime 3 by decide)
    norm_num at hv
    exact hv
  · change primeParity 3 (by decide) (Additive.ofMul (rationalSquareClass (5 : ℚ))) = 0
    have hv := primeParity_prime (show Nat.Prime 3 by decide) (show Nat.Prime 5 by decide)
    norm_num at hv
    exact hv
  · change primeParity 3 (by decide) (Additive.ofMul (rationalSquareClass (h.primes 0 : ℚ))) = 0
    dsimp only [PositivePrimeOutputs.primes]
    rw [primeParity_prime (show Nat.Prime 3 by decide) (h.prime 0)]
    exact ite_eq_right (h.outside 0 3 (by simp)).symm
  · change primeParity 3 (by decide) (Additive.ofMul (rationalSquareClass (h.primes 1 : ℚ))) = 0
    dsimp only [PositivePrimeOutputs.primes]
    rw [primeParity_prime (show Nat.Prime 3 by decide) (h.prime 1)]
    exact ite_eq_right (h.outside 1 3 (by simp)).symm
  · change primeParity 3 (by decide) (Additive.ofMul (rationalSquareClass (h.primes 2 : ℚ))) = 0
    dsimp only [PositivePrimeOutputs.primes]
    rw [primeParity_prime (show Nat.Prime 3 by decide) (h.prime 2)]
    exact ite_eq_right (h.outside 2 3 (by simp)).symm
  · change primeParity 3 (by decide) (Additive.ofMul (rationalSquareClass (h.primes 3 : ℚ))) = 0
    dsimp only [PositivePrimeOutputs.primes]
    rw [primeParity_prime (show Nat.Prime 3 by decide) (h.prime 3)]
    exact ite_eq_right (h.outside 3 3 (by simp)).symm
  · change primeParity 3 (by decide) (Additive.ofMul (rationalSquareClass (h.primes 4 : ℚ))) = 0
    dsimp only [PositivePrimeOutputs.primes]
    rw [primeParity_prime (show Nat.Prime 3 by decide) (h.prime 4)]
    exact ite_eq_right (h.outside 4 3 (by simp)).symm
  · change primeParity 3 (by decide) (Additive.ofMul (rationalSquareClass (h.primes 5 : ℚ))) = 0
    dsimp only [PositivePrimeOutputs.primes]
    rw [primeParity_prime (show Nat.Prime 3 by decide) (h.prime 5)]
    exact ite_eq_right (h.outside 5 3 (by simp)).symm
  · change primeParity 3 (by decide) (Additive.ofMul (rationalSquareClass (h.primes 6 : ℚ))) = 0
    dsimp only [PositivePrimeOutputs.primes]
    rw [primeParity_prime (show Nat.Prime 3 by decide) (h.prime 6)]
    exact ite_eq_right (h.outside 6 3 (by simp)).symm
  · change primeParity 3 (by decide) (Additive.ofMul (rationalSquareClass (h.primes 7 : ℚ))) = 0
    dsimp only [PositivePrimeOutputs.primes]
    rw [primeParity_prime (show Nat.Prime 3 by decide) (h.prime 7)]
    exact ite_eq_right (h.outside 7 3 (by simp)).symm

theorem real_Ep_literal : squareClassCharacterRow realSignLinear
    (columnsEp h.primes) = Binary.vector 12 1 := by
  funext j
  fin_cases j
  · change squareClassSign (Additive.ofMul (rationalSquareClass (-1 : ℚ))) = 1
    exact squareClassSign_neg_one
  · change squareClassSign (Additive.ofMul (rationalSquareClass (2 : ℚ))) = 0
    have hv := squareClassSign_prime (show Nat.Prime 2 by decide)
    norm_num only [Nat.cast_ofNat] at hv
    exact hv
  · change squareClassSign (Additive.ofMul (rationalSquareClass (3 : ℚ))) = 0
    have hv := squareClassSign_prime (show Nat.Prime 3 by decide)
    norm_num only [Nat.cast_ofNat] at hv
    exact hv
  · change squareClassSign (Additive.ofMul (rationalSquareClass (5 : ℚ))) = 0
    have hv := squareClassSign_prime (show Nat.Prime 5 by decide)
    norm_num only [Nat.cast_ofNat] at hv
    exact hv
  · change squareClassSign (Additive.ofMul (rationalSquareClass (h.primes 0 : ℚ))) = 0
    exact squareClassSign_prime (h.prime 0)
  · change squareClassSign (Additive.ofMul (rationalSquareClass (h.primes 1 : ℚ))) = 0
    exact squareClassSign_prime (h.prime 1)
  · change squareClassSign (Additive.ofMul (rationalSquareClass (h.primes 2 : ℚ))) = 0
    exact squareClassSign_prime (h.prime 2)
  · change squareClassSign (Additive.ofMul (rationalSquareClass (h.primes 3 : ℚ))) = 0
    exact squareClassSign_prime (h.prime 3)
  · change squareClassSign (Additive.ofMul (rationalSquareClass (h.primes 8 : ℚ))) = 0
    exact squareClassSign_prime (h.prime 8)
  · change squareClassSign (Additive.ofMul (rationalSquareClass (h.primes 9 : ℚ))) = 0
    exact squareClassSign_prime (h.prime 9)
  · change squareClassSign (Additive.ofMul (rationalSquareClass (h.primes 10 : ℚ))) = 0
    exact squareClassSign_prime (h.prime 10)
  · change squareClassSign (Additive.ofMul (rationalSquareClass (h.primes 11 : ℚ))) = 0
    exact squareClassSign_prime (h.prime 11)

end RankCertificates.Rank5FixedRows
