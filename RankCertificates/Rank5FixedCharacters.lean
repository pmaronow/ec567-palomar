module

public import RankCertificates.Rank5MovingRows
public import RankCertificates.PrimePowerCharacters
public import RankCertificates.Rank5ThreeDescent
public import RankCertificates.Rank5FiveDescent

@[expose] public section

namespace RankCertificates.Rank5FixedCharacters

open Rank5CharacterRows Rank5CharacterEvaluation PrimePowerCharacters PrimePowerResidues

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

variable {x y : ℤ} (h : PrimeSpecialization5 x y)

theorem dyadic4_int (z : ℤ) (hz : ¬ (2 : ℤ) ∣ z) :
    dyadicCharacter4Linear (Additive.ofMul (rationalSquareClass (z : ℚ))) =
      quadraticCharacterBit (ZMod.χ₄ z) := by
  have hz0 : (z : ℚ) ≠ 0 := by exact_mod_cast (show z ≠ 0 from fun he => hz (he ▸ dvd_zero _))
  change powerCharacterParity 2 2 ZMod.χ₄ ZMod.isQuadratic_χ₄ _ = _
  rw [powerCharacterParity_apply 2 2 ZMod.χ₄ ZMod.isQuadratic_χ₄ hz0]
  simp only [powerCharacter, unitResiduePow_int_of_not_dvd 2 2 z hz]

theorem dyadic8_int (z : ℤ) (hz : ¬ (2 : ℤ) ∣ z) :
    dyadicCharacter8Linear (Additive.ofMul (rationalSquareClass (z : ℚ))) =
      quadraticCharacterBit (ZMod.χ₈ z) := by
  have hz0 : (z : ℚ) ≠ 0 := by exact_mod_cast (show z ≠ 0 from fun he => hz (he ▸ dvd_zero _))
  change powerCharacterParity 2 3 ZMod.χ₈ ZMod.isQuadratic_χ₈ _ = _
  rw [powerCharacterParity_apply 2 3 ZMod.χ₈ ZMod.isQuadratic_χ₈ hz0]
  simp only [powerCharacter, unitResiduePow_int_of_not_dvd 2 3 z hz]

theorem dyadic4_self : dyadicCharacter4Linear
    (Additive.ofMul (rationalSquareClass (2 : ℚ))) = 0 := by
  change powerCharacterParity 2 2 ZMod.χ₄ ZMod.isQuadratic_χ₄ _ = _
  rw [powerCharacterParity_apply 2 2 ZMod.χ₄ ZMod.isQuadratic_χ₄ (by norm_num)]
  simp only [powerCharacter]
  have hs := unitResiduePow_prime_self 2 2
  norm_num only [Nat.cast_ofNat] at hs
  rw [hs]
  decide +kernel

theorem dyadic8_self : dyadicCharacter8Linear
    (Additive.ofMul (rationalSquareClass (2 : ℚ))) = 0 := by
  change powerCharacterParity 2 3 ZMod.χ₈ ZMod.isQuadratic_χ₈ _ = _
  rw [powerCharacterParity_apply 2 3 ZMod.χ₈ ZMod.isQuadratic_χ₈ (by norm_num)]
  simp only [powerCharacter]
  have hs := unitResiduePow_prime_self 2 3
  norm_num only [Nat.cast_ofNat] at hs
  rw [hs]
  decide +kernel

theorem output_not_dvd (i : Fin 12) (j : Fin 8) :
    ¬ (PrimePatterns.Rank5.retainedPrimes j : ℤ) ∣
      (PrimePatterns.Rank5.outputs i).eval x y := by
  intro hd
  exact PrimePatterns.Rank5.retained_prime_residue i j x y (Int.emod_eq_zero_of_dvd hd)

theorem dyadic4_moving (i : Fin 12) : dyadicCharacter4Linear
    (Additive.ofMul (rationalSquareClass (h.primes i : ℚ))) =
      quadraticCharacterBit (ZMod.χ₄ (PrimePatterns.Rank5.mod8Units i)) := by
  rw [← h.cast_eq i, dyadic4_int _ (by simpa [PrimePatterns.Rank5.retainedPrimes] using output_not_dvd (x := x) (y := y) i 0)]
  have hres := PrimePatterns.Rank5.residue8 i x y
  have h4 : (PrimePatterns.Rank5.outputs i).eval x y % 4 = PrimePatterns.Rank5.mod8Units i % 4 := by omega
  rw [ZMod.χ₄_int_mod_four, h4, ← ZMod.χ₄_int_mod_four]

theorem dyadic8_moving (i : Fin 12) : dyadicCharacter8Linear
    (Additive.ofMul (rationalSquareClass (h.primes i : ℚ))) =
      quadraticCharacterBit (ZMod.χ₈ (PrimePatterns.Rank5.mod8Units i)) := by
  rw [← h.cast_eq i, dyadic8_int _ (by simpa [PrimePatterns.Rank5.retainedPrimes] using output_not_dvd (x := x) (y := y) i 0)]
  rw [ZMod.χ₈_int_mod_eight, PrimePatterns.Rank5.residue8]

/-- A fixed retained-prime character of each moving column is a literal
finite Legendre-symbol calculation at its CRT residue. -/
theorem fixed_moving (j : Fin 8) (i : Fin 12) :
    @unitCharacterLinear (PrimePatterns.Rank5.retainedPrimes j)
      ⟨PrimePatterns.Rank5.retained_primes_prime j⟩
      (Additive.ofMul (rationalSquareClass (h.primes i : ℚ))) =
      quadraticCharacterBit (@legendreSym (PrimePatterns.Rank5.retainedPrimes j)
        ⟨PrimePatterns.Rank5.retained_primes_prime j⟩
        ((PrimePatterns.Rank5.outputs i).c % (PrimePatterns.Rank5.retainedPrimes j : ℤ))) := by
  let : Fact (PrimePatterns.Rank5.retainedPrimes j).Prime := ⟨PrimePatterns.Rank5.retained_primes_prime j⟩
  rw [← h.cast_eq i]
  change unitCharacterParity (PrimePatterns.Rank5.retainedPrimes j) _ = _
  rw [unitCharacterParity_int_of_not_dvd _ (output_not_dvd (x := x) (y := y) i j), legendreSym.mod]
  rw [PrimePatterns.AffineForm.eval_mod _ _ _ _
    (PrimePatterns.Rank5.retained_prime_units i j).1
    (PrimePatterns.Rank5.retained_prime_units i j).2.1]

end RankCertificates.Rank5FixedCharacters
