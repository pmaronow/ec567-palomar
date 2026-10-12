module

public import RankCertificates.Rank7CharacterEvaluation
public import RankCertificates.Rank7ThreeDescent
public import RankCertificates.Rank7FixedOddDescent
public import RankCertificates.RealDescent
public import RankCertificates.PrimePowerCharacters

@[expose] public section

namespace RankCertificates.Rank7FixedRows

local instance : Fact (Nat.Prime 2) := ⟨by decide +kernel⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide +kernel⟩
local instance : Fact (Nat.Prime 7) := ⟨by decide +kernel⟩
local instance : Fact (Nat.Prime 13) := ⟨by decide +kernel⟩

open Integration Rank7CharacterEvaluation PrimePowerCharacters PrimePowerResidues

variable {x y : ℤ} (h : PrimeSpecialization7 x y)

theorem moving_residue (p : ℕ) (j : Fin 8)
    (hp : p = PrimePatterns.Rank7.retainedPrimes j) (i : Fin 12) :
    (h.primes i : ZMod p) = ((PrimePatterns.Rank7.outputs i).c : ZMod p) := by
  have ha := (PrimePatterns.Rank7.retained_prime_units i j).1
  have hb := (PrimePatterns.Rank7.retained_prime_units i j).2.1
  rw [← hp] at ha hb
  have hm := PrimePatterns.AffineForm.eval_mod (PrimePatterns.Rank7.outputs i) p x y ha hb
  have he := congrArg (fun z : ℤ => (z : ZMod p)) hm
  simp only [ZMod.intCast_mod] at he
  have hi := congrArg (fun z : ℤ => (z : ZMod p)) (prime_int_eq h i)
  simpa only [Int.cast_natCast] using hi.trans he

theorem fixed_moving_character (p : ℕ) [Fact p.Prime]
    (j : Fin 8) (hp : p = PrimePatterns.Rank7.retainedPrimes j)
    (hs : p ∈ [2, 3, 7, 13]) (i : Fin 12) :
    unitCharacterParity p (Additive.ofMul (rationalSquareClass (h.primes i : ℚ))) =
      quadraticCharacterBit (legendreSym p (PrimePatterns.Rank7.outputs i).c) := by
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  have he : legendreSym p (h.primes i : ℤ) =
      legendreSym p (PrimePatterns.Rank7.outputs i).c := by
    apply MovingPrimeCharacters.legendre_eq_of_residue_eq
    simpa only [Int.cast_natCast] using moving_residue h p j hp i
  rw [MovingPrimeCharacters.unitCharacterParity_prime_other p (h.primes i)
    (h.outside i p hs).symm, he]

theorem fixed_moving_parity (p : ℕ) [Fact p.Prime]
    (hs : p ∈ [2, 3, 7, 13]) (i : Fin 12) :
    primeParity p (Fact.out : p.Prime)
      (Additive.ofMul (rationalSquareClass (h.primes i : ℚ))) = 0 := by
  exact (primeParity_prime (p := p) (q := h.primes i)
    (Fact.out : p.Prime) (h.prime i)).trans (ite_eq_right (h.outside i p hs).symm)

theorem negative_character (p : ℕ) [Fact p.Prime] :
    unitCharacterParity p (Additive.ofMul (rationalSquareClass (-1))) =
      quadraticCharacterBit (legendreSym p (-1)) := by
  exact unitCharacterParity_int_of_not_dvd p
    ((ZMod.intCast_zmod_eq_zero_iff_dvd (-1) p).not.mp (by simp))

include h in
theorem partner_sign_zero {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (-2 * Rank7.a (M7 x) (N7 y)) (Rank7.c (M7 x) (N7 y))) :
    squareClassSign (Additive.ofMul q) = 0 := by
  have hpos (i : Fin 12) : (0 : ℚ) < h.primes i := by
    exact_mod_cast (h.prime i).pos
  have hF : 0 < Rank7.F (M7 x) (N7 y) := by
    rw [Rank7PrimeValuations.F_factorization h]
    exact mul_pos (by norm_num) (mul_pos (mul_pos (mul_pos (hpos 0) (hpos 1)) (hpos 2)) (hpos 3))
  have hJ : 0 < Rank7.J (M7 x) (N7 y) := by
    rw [Rank7PrimeValuations.J_factorization h]
    exact mul_pos (by norm_num) (mul_pos (mul_pos (mul_pos (hpos 8) (hpos 9)) (hpos 10)) (hpos 11))
  apply RealDescent.twoIsogenyImage_sign_zero (a := -2 * Rank7.a (M7 x) (N7 y))
    (b := Rank7.c (M7 x) (N7 y)) _ _ hq
  · unfold Rank7.a
    linarith
  · unfold Rank7.c
    positivity

set_option maxHeartbeats 2000000

theorem three_unit_row :
    squareClassCharacterRow (unitCharacterLinear 3)
      (signedPrimeColumns (primeColumns7E h.primes)) = Binary.vector 13 195 := by
  rw [signed_columnsE_eq]
  funext j
  fin_cases j
  · change unitCharacterParity 3 (Additive.ofMul (rationalSquareClass (-1 : ℚ))) = 1
    have hv := negative_character 3
    norm_num [PrimePatterns.Rank7.outputs, quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 3 (Additive.ofMul (rationalSquareClass (2 : ℚ))) = 1
    have hv := MovingPrimeCharacters.unitCharacterParity_prime_other 3 2 (by decide +kernel)
    norm_num [PrimePatterns.Rank7.outputs, quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 3 (Additive.ofMul (rationalSquareClass (3 : ℚ))) = 0
    simpa using MovingPrimeCharacters.unitCharacterParity_prime_self 3
  · change unitCharacterParity 3 (Additive.ofMul (rationalSquareClass (7 : ℚ))) = 0
    have hv := MovingPrimeCharacters.unitCharacterParity_prime_other 3 7 (by decide +kernel)
    norm_num [PrimePatterns.Rank7.outputs, quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 3 (Additive.ofMul (rationalSquareClass (13 : ℚ))) = 0
    have hv := MovingPrimeCharacters.unitCharacterParity_prime_other 3 13 (by decide +kernel)
    norm_num [PrimePatterns.Rank7.outputs, quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 3 (Additive.ofMul (rationalSquareClass (h.primes 0 : ℚ))) = 0
    have hv := fixed_moving_character h 3 1 (by rfl) (by simp) 0
    norm_num [PrimePatterns.Rank7.outputs, quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 3 (Additive.ofMul (rationalSquareClass (h.primes 1 : ℚ))) = 1
    have hv := fixed_moving_character h 3 1 (by rfl) (by simp) 1
    norm_num [PrimePatterns.Rank7.outputs, quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 3 (Additive.ofMul (rationalSquareClass (h.primes 2 : ℚ))) = 1
    have hv := fixed_moving_character h 3 1 (by rfl) (by simp) 2
    norm_num [PrimePatterns.Rank7.outputs, quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 3 (Additive.ofMul (rationalSquareClass (h.primes 3 : ℚ))) = 0
    have hv := fixed_moving_character h 3 1 (by rfl) (by simp) 3
    norm_num [PrimePatterns.Rank7.outputs, quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 3 (Additive.ofMul (rationalSquareClass (h.primes 4 : ℚ))) = 0
    have hv := fixed_moving_character h 3 1 (by rfl) (by simp) 4
    norm_num [PrimePatterns.Rank7.outputs, quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 3 (Additive.ofMul (rationalSquareClass (h.primes 5 : ℚ))) = 0
    have hv := fixed_moving_character h 3 1 (by rfl) (by simp) 5
    norm_num [PrimePatterns.Rank7.outputs, quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 3 (Additive.ofMul (rationalSquareClass (h.primes 6 : ℚ))) = 0
    have hv := fixed_moving_character h 3 1 (by rfl) (by simp) 6
    norm_num [PrimePatterns.Rank7.outputs, quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 3 (Additive.ofMul (rationalSquareClass (h.primes 7 : ℚ))) = 0
    have hv := fixed_moving_character h 3 1 (by rfl) (by simp) 7
    norm_num [PrimePatterns.Rank7.outputs, quadraticCharacterBit] at hv
    exact hv

theorem seven_unit_row :
    squareClassCharacterRow (unitCharacterLinear 7)
      (signedPrimeColumns (primeColumns7Ep h.primes)) = Binary.vector 13 4117 := by
  rw [signed_columnsEp_eq]
  funext j
  fin_cases j
  · change unitCharacterParity 7 (Additive.ofMul (rationalSquareClass (-1 : ℚ))) = 1
    have hv := negative_character 7
    norm_num [PrimePatterns.Rank7.outputs, quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 7 (Additive.ofMul (rationalSquareClass (2 : ℚ))) = 0
    have hv := MovingPrimeCharacters.unitCharacterParity_prime_other 7 2 (by decide +kernel)
    norm_num [PrimePatterns.Rank7.outputs, quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 7 (Additive.ofMul (rationalSquareClass (3 : ℚ))) = 1
    have hv := MovingPrimeCharacters.unitCharacterParity_prime_other 7 3 (by decide +kernel)
    norm_num [PrimePatterns.Rank7.outputs, quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 7 (Additive.ofMul (rationalSquareClass (7 : ℚ))) = 0
    simpa using MovingPrimeCharacters.unitCharacterParity_prime_self 7
  · change unitCharacterParity 7 (Additive.ofMul (rationalSquareClass (13 : ℚ))) = 1
    have hv := MovingPrimeCharacters.unitCharacterParity_prime_other 7 13 (by decide +kernel)
    norm_num [PrimePatterns.Rank7.outputs, quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 7 (Additive.ofMul (rationalSquareClass (h.primes 0 : ℚ))) = 0
    have hv := fixed_moving_character h 7 2 (by rfl) (by simp) 0
    norm_num [PrimePatterns.Rank7.outputs, quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 7 (Additive.ofMul (rationalSquareClass (h.primes 1 : ℚ))) = 0
    have hv := fixed_moving_character h 7 2 (by rfl) (by simp) 1
    norm_num [PrimePatterns.Rank7.outputs, quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 7 (Additive.ofMul (rationalSquareClass (h.primes 2 : ℚ))) = 0
    have hv := fixed_moving_character h 7 2 (by rfl) (by simp) 2
    norm_num [PrimePatterns.Rank7.outputs, quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 7 (Additive.ofMul (rationalSquareClass (h.primes 3 : ℚ))) = 0
    have hv := fixed_moving_character h 7 2 (by rfl) (by simp) 3
    norm_num [PrimePatterns.Rank7.outputs, quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 7 (Additive.ofMul (rationalSquareClass (h.primes 8 : ℚ))) = 0
    have hv := fixed_moving_character h 7 2 (by rfl) (by simp) 8
    norm_num [PrimePatterns.Rank7.outputs, quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 7 (Additive.ofMul (rationalSquareClass (h.primes 9 : ℚ))) = 0
    have hv := fixed_moving_character h 7 2 (by rfl) (by simp) 9
    norm_num [PrimePatterns.Rank7.outputs, quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 7 (Additive.ofMul (rationalSquareClass (h.primes 10 : ℚ))) = 0
    have hv := fixed_moving_character h 7 2 (by rfl) (by simp) 10
    norm_num [PrimePatterns.Rank7.outputs, quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 7 (Additive.ofMul (rationalSquareClass (h.primes 11 : ℚ))) = 1
    have hv := fixed_moving_character h 7 2 (by rfl) (by simp) 11
    norm_num [PrimePatterns.Rank7.outputs, quadraticCharacterBit] at hv
    exact hv

theorem thirteen_unit_row :
    squareClassCharacterRow (unitCharacterLinear 13)
      (signedPrimeColumns (primeColumns7Ep h.primes)) = Binary.vector 13 7626 := by
  rw [signed_columnsEp_eq]
  funext j
  fin_cases j
  · change unitCharacterParity 13 (Additive.ofMul (rationalSquareClass (-1 : ℚ))) = 0
    have hv := negative_character 13
    norm_num [PrimePatterns.Rank7.outputs, quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 13 (Additive.ofMul (rationalSquareClass (2 : ℚ))) = 1
    have hv := MovingPrimeCharacters.unitCharacterParity_prime_other 13 2 (by decide +kernel)
    norm_num [PrimePatterns.Rank7.outputs, quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 13 (Additive.ofMul (rationalSquareClass (3 : ℚ))) = 0
    have hv := MovingPrimeCharacters.unitCharacterParity_prime_other 13 3 (by decide +kernel)
    norm_num [PrimePatterns.Rank7.outputs, quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 13 (Additive.ofMul (rationalSquareClass (7 : ℚ))) = 1
    have hv := MovingPrimeCharacters.unitCharacterParity_prime_other 13 7 (by decide +kernel)
    norm_num [PrimePatterns.Rank7.outputs, quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 13 (Additive.ofMul (rationalSquareClass (13 : ℚ))) = 0
    simpa using MovingPrimeCharacters.unitCharacterParity_prime_self 13
  · change unitCharacterParity 13 (Additive.ofMul (rationalSquareClass (h.primes 0 : ℚ))) = 0
    have hv := fixed_moving_character h 13 4 (by rfl) (by simp) 0
    norm_num [PrimePatterns.Rank7.outputs, quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 13 (Additive.ofMul (rationalSquareClass (h.primes 1 : ℚ))) = 1
    have hv := fixed_moving_character h 13 4 (by rfl) (by simp) 1
    norm_num [PrimePatterns.Rank7.outputs, quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 13 (Additive.ofMul (rationalSquareClass (h.primes 2 : ℚ))) = 1
    have hv := fixed_moving_character h 13 4 (by rfl) (by simp) 2
    norm_num [PrimePatterns.Rank7.outputs, quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 13 (Additive.ofMul (rationalSquareClass (h.primes 3 : ℚ))) = 1
    have hv := fixed_moving_character h 13 4 (by rfl) (by simp) 3
    norm_num [PrimePatterns.Rank7.outputs, quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 13 (Additive.ofMul (rationalSquareClass (h.primes 8 : ℚ))) = 0
    have hv := fixed_moving_character h 13 4 (by rfl) (by simp) 8
    norm_num [PrimePatterns.Rank7.outputs, quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 13 (Additive.ofMul (rationalSquareClass (h.primes 9 : ℚ))) = 1
    have hv := fixed_moving_character h 13 4 (by rfl) (by simp) 9
    norm_num [PrimePatterns.Rank7.outputs, quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 13 (Additive.ofMul (rationalSquareClass (h.primes 10 : ℚ))) = 1
    have hv := fixed_moving_character h 13 4 (by rfl) (by simp) 10
    norm_num [PrimePatterns.Rank7.outputs, quadraticCharacterBit] at hv
    exact hv
  · change unitCharacterParity 13 (Additive.ofMul (rationalSquareClass (h.primes 11 : ℚ))) = 1
    have hv := fixed_moving_character h 13 4 (by rfl) (by simp) 11
    norm_num [PrimePatterns.Rank7.outputs, quadraticCharacterBit] at hv
    exact hv

theorem three_valuation_row :
    squareClassCharacterRow (valuationParityLinear 3)
      (signedPrimeColumns (primeColumns7E h.primes)) = Binary.vector 13 4 := by
  have hs2 := primeParity_prime (p := 3) (q := 2) (by decide +kernel) (by decide +kernel)
  have hs3 := primeParity_prime (p := 3) (q := 3) (by decide +kernel) (by decide +kernel)
  have hs7 := primeParity_prime (p := 3) (q := 7) (by decide +kernel) (by decide +kernel)
  have hs13 := primeParity_prime (p := 3) (q := 13) (by decide +kernel) (by decide +kernel)
  norm_num at hs2 hs3 hs7 hs13
  rw [signed_columnsE_eq]
  funext j
  fin_cases j <;> simp only [squareClassCharacterRow, valuationParityLinear,
    AddMonoidHom.coe_toZModLinearMap]
  all_goals norm_num [hs2, hs3, hs7, hs13, primeParity_neg_one,
    fixed_moving_parity h 3 (by simp), Binary.vector, Binary.scalar]
  all_goals decide +kernel

theorem seven_valuation_row :
    squareClassCharacterRow (valuationParityLinear 7)
      (signedPrimeColumns (primeColumns7Ep h.primes)) = Binary.vector 13 8 := by
  have hs2 := primeParity_prime (p := 7) (q := 2) (by decide +kernel) (by decide +kernel)
  have hs3 := primeParity_prime (p := 7) (q := 3) (by decide +kernel) (by decide +kernel)
  have hs7 := primeParity_prime (p := 7) (q := 7) (by decide +kernel) (by decide +kernel)
  have hs13 := primeParity_prime (p := 7) (q := 13) (by decide +kernel) (by decide +kernel)
  norm_num at hs2 hs3 hs7 hs13
  rw [signed_columnsEp_eq]
  funext j
  fin_cases j <;> simp only [squareClassCharacterRow, valuationParityLinear,
    AddMonoidHom.coe_toZModLinearMap]
  all_goals norm_num [hs2, hs3, hs7, hs13, primeParity_neg_one,
    fixed_moving_parity h 7 (by simp), Binary.vector, Binary.scalar]
  all_goals decide +kernel

theorem thirteen_valuation_row :
    squareClassCharacterRow (valuationParityLinear 13)
      (signedPrimeColumns (primeColumns7Ep h.primes)) = Binary.vector 13 16 := by
  have hs2 := primeParity_prime (p := 13) (q := 2) (by decide +kernel) (by decide +kernel)
  have hs3 := primeParity_prime (p := 13) (q := 3) (by decide +kernel) (by decide +kernel)
  have hs7 := primeParity_prime (p := 13) (q := 7) (by decide +kernel) (by decide +kernel)
  have hs13 := primeParity_prime (p := 13) (q := 13) (by decide +kernel) (by decide +kernel)
  norm_num at hs2 hs3 hs7 hs13
  rw [signed_columnsEp_eq]
  funext j
  fin_cases j <;> simp only [squareClassCharacterRow, valuationParityLinear,
    AddMonoidHom.coe_toZModLinearMap]
  all_goals norm_num [hs2, hs3, hs7, hs13, primeParity_neg_one,
    fixed_moving_parity h 13 (by simp), Binary.vector, Binary.scalar]
  all_goals decide +kernel

theorem sign_row :
    squareClassCharacterRow (squareClassSign.toZModLinearMap 2)
      (signedPrimeColumns (primeColumns7Ep h.primes)) = Binary.vector 13 1 := by
  rw [signed_columnsEp_eq]
  funext j
  fin_cases j
  · exact squareClassSign_neg_one
  · change squareClassSign (Additive.ofMul (rationalSquareClass (2 : ℚ))) = 0
    simpa using squareClassSign_prime (show Nat.Prime 2 by decide +kernel)
  · change squareClassSign (Additive.ofMul (rationalSquareClass (3 : ℚ))) = 0
    simpa using squareClassSign_prime (show Nat.Prime 3 by decide +kernel)
  · change squareClassSign (Additive.ofMul (rationalSquareClass (7 : ℚ))) = 0
    simpa using squareClassSign_prime (show Nat.Prime 7 by decide +kernel)
  · change squareClassSign (Additive.ofMul (rationalSquareClass (13 : ℚ))) = 0
    simpa using squareClassSign_prime (show Nat.Prime 13 by decide +kernel)
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
    ¬ (PrimePatterns.Rank7.retainedPrimes j : ℤ) ∣
      (PrimePatterns.Rank7.outputs i).eval x y := by
  intro hd
  exact PrimePatterns.Rank7.retained_prime_residue i j x y (Int.emod_eq_zero_of_dvd hd)

theorem dyadic4_moving (i : Fin 12) : dyadicCharacter4Linear
    (Additive.ofMul (rationalSquareClass (h.primes i : ℚ))) =
      quadraticCharacterBit (ZMod.χ₄ (PrimePatterns.Rank7.mod8Units i)) := by
  rw [← h.cast_eq i, dyadic4_int _ (by simpa [PrimePatterns.Rank7.retainedPrimes] using output_not_dvd (x := x) (y := y) i 0)]
  have hres := PrimePatterns.Rank7.residue8 i x y
  have h4 : (PrimePatterns.Rank7.outputs i).eval x y % 4 = PrimePatterns.Rank7.mod8Units i % 4 := by omega
  rw [ZMod.χ₄_int_mod_four, h4, ← ZMod.χ₄_int_mod_four]

theorem dyadic8_moving (i : Fin 12) : dyadicCharacter8Linear
    (Additive.ofMul (rationalSquareClass (h.primes i : ℚ))) =
      quadraticCharacterBit (ZMod.χ₈ (PrimePatterns.Rank7.mod8Units i)) := by
  rw [← h.cast_eq i, dyadic8_int _ (by simpa [PrimePatterns.Rank7.retainedPrimes] using output_not_dvd (x := x) (y := y) i 0)]
  rw [ZMod.χ₈_int_mod_eight, PrimePatterns.Rank7.residue8]

theorem dyadic4_E_row :
    squareClassCharacterRow dyadicCharacter4Linear
      (signedPrimeColumns (primeColumns7E h.primes)) = Binary.vector 13 4941 := by
  rw [signed_columnsE_eq]
  funext j
  fin_cases j
  · change dyadicCharacter4Linear (Additive.ofMul (rationalSquareClass (-1 : ℚ))) = 1
    have hv := dyadic4_int (-1) (by norm_num)
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₄_int_eq_if_mod_four,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter4Linear (Additive.ofMul (rationalSquareClass (2 : ℚ))) = 0
    exact dyadic4_self
  · change dyadicCharacter4Linear (Additive.ofMul (rationalSquareClass (3 : ℚ))) = 1
    have hv := dyadic4_int 3 (by norm_num)
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₄_int_eq_if_mod_four,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter4Linear (Additive.ofMul (rationalSquareClass (7 : ℚ))) = 1
    have hv := dyadic4_int 7 (by norm_num)
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₄_int_eq_if_mod_four,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter4Linear (Additive.ofMul (rationalSquareClass (13 : ℚ))) = 0
    have hv := dyadic4_int 13 (by norm_num)
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₄_int_eq_if_mod_four,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter4Linear (Additive.ofMul (rationalSquareClass (h.primes 0 : ℚ))) = 0
    have hv := dyadic4_moving h 0
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₄_int_eq_if_mod_four,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter4Linear (Additive.ofMul (rationalSquareClass (h.primes 1 : ℚ))) = 1
    have hv := dyadic4_moving h 1
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₄_int_eq_if_mod_four,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter4Linear (Additive.ofMul (rationalSquareClass (h.primes 2 : ℚ))) = 0
    have hv := dyadic4_moving h 2
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₄_int_eq_if_mod_four,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter4Linear (Additive.ofMul (rationalSquareClass (h.primes 3 : ℚ))) = 1
    have hv := dyadic4_moving h 3
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₄_int_eq_if_mod_four,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter4Linear (Additive.ofMul (rationalSquareClass (h.primes 4 : ℚ))) = 1
    have hv := dyadic4_moving h 4
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₄_int_eq_if_mod_four,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter4Linear (Additive.ofMul (rationalSquareClass (h.primes 5 : ℚ))) = 0
    have hv := dyadic4_moving h 5
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₄_int_eq_if_mod_four,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter4Linear (Additive.ofMul (rationalSquareClass (h.primes 6 : ℚ))) = 0
    have hv := dyadic4_moving h 6
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₄_int_eq_if_mod_four,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter4Linear (Additive.ofMul (rationalSquareClass (h.primes 7 : ℚ))) = 1
    have hv := dyadic4_moving h 7
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₄_int_eq_if_mod_four,
      quadraticCharacterBit] at hv
    exact hv

theorem dyadic8_E_row :
    squareClassCharacterRow dyadicCharacter8Linear
      (signedPrimeColumns (primeColumns7E h.primes)) = Binary.vector 13 8020 := by
  rw [signed_columnsE_eq]
  funext j
  fin_cases j
  · change dyadicCharacter8Linear (Additive.ofMul (rationalSquareClass (-1 : ℚ))) = 0
    have hv := dyadic8_int (-1) (by norm_num)
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₈_int_eq_if_mod_eight,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter8Linear (Additive.ofMul (rationalSquareClass (2 : ℚ))) = 0
    exact dyadic8_self
  · change dyadicCharacter8Linear (Additive.ofMul (rationalSquareClass (3 : ℚ))) = 1
    have hv := dyadic8_int 3 (by norm_num)
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₈_int_eq_if_mod_eight,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter8Linear (Additive.ofMul (rationalSquareClass (7 : ℚ))) = 0
    have hv := dyadic8_int 7 (by norm_num)
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₈_int_eq_if_mod_eight,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter8Linear (Additive.ofMul (rationalSquareClass (13 : ℚ))) = 1
    have hv := dyadic8_int 13 (by norm_num)
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₈_int_eq_if_mod_eight,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter8Linear (Additive.ofMul (rationalSquareClass (h.primes 0 : ℚ))) = 0
    have hv := dyadic8_moving h 0
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₈_int_eq_if_mod_eight,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter8Linear (Additive.ofMul (rationalSquareClass (h.primes 1 : ℚ))) = 1
    have hv := dyadic8_moving h 1
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₈_int_eq_if_mod_eight,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter8Linear (Additive.ofMul (rationalSquareClass (h.primes 2 : ℚ))) = 0
    have hv := dyadic8_moving h 2
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₈_int_eq_if_mod_eight,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter8Linear (Additive.ofMul (rationalSquareClass (h.primes 3 : ℚ))) = 1
    have hv := dyadic8_moving h 3
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₈_int_eq_if_mod_eight,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter8Linear (Additive.ofMul (rationalSquareClass (h.primes 4 : ℚ))) = 1
    have hv := dyadic8_moving h 4
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₈_int_eq_if_mod_eight,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter8Linear (Additive.ofMul (rationalSquareClass (h.primes 5 : ℚ))) = 1
    have hv := dyadic8_moving h 5
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₈_int_eq_if_mod_eight,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter8Linear (Additive.ofMul (rationalSquareClass (h.primes 6 : ℚ))) = 1
    have hv := dyadic8_moving h 6
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₈_int_eq_if_mod_eight,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter8Linear (Additive.ofMul (rationalSquareClass (h.primes 7 : ℚ))) = 1
    have hv := dyadic8_moving h 7
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₈_int_eq_if_mod_eight,
      quadraticCharacterBit] at hv
    exact hv

theorem dyadic4_Ep_row :
    squareClassCharacterRow dyadicCharacter4Linear
      (signedPrimeColumns (primeColumns7Ep h.primes)) = Binary.vector 13 4941 := by
  rw [signed_columnsEp_eq]
  funext j
  fin_cases j
  · change dyadicCharacter4Linear (Additive.ofMul (rationalSquareClass (-1 : ℚ))) = 1
    have hv := dyadic4_int (-1) (by norm_num)
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₄_int_eq_if_mod_four,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter4Linear (Additive.ofMul (rationalSquareClass (2 : ℚ))) = 0
    exact dyadic4_self
  · change dyadicCharacter4Linear (Additive.ofMul (rationalSquareClass (3 : ℚ))) = 1
    have hv := dyadic4_int 3 (by norm_num)
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₄_int_eq_if_mod_four,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter4Linear (Additive.ofMul (rationalSquareClass (7 : ℚ))) = 1
    have hv := dyadic4_int 7 (by norm_num)
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₄_int_eq_if_mod_four,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter4Linear (Additive.ofMul (rationalSquareClass (13 : ℚ))) = 0
    have hv := dyadic4_int 13 (by norm_num)
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₄_int_eq_if_mod_four,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter4Linear (Additive.ofMul (rationalSquareClass (h.primes 0 : ℚ))) = 0
    have hv := dyadic4_moving h 0
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₄_int_eq_if_mod_four,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter4Linear (Additive.ofMul (rationalSquareClass (h.primes 1 : ℚ))) = 1
    have hv := dyadic4_moving h 1
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₄_int_eq_if_mod_four,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter4Linear (Additive.ofMul (rationalSquareClass (h.primes 2 : ℚ))) = 0
    have hv := dyadic4_moving h 2
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₄_int_eq_if_mod_four,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter4Linear (Additive.ofMul (rationalSquareClass (h.primes 3 : ℚ))) = 1
    have hv := dyadic4_moving h 3
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₄_int_eq_if_mod_four,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter4Linear (Additive.ofMul (rationalSquareClass (h.primes 8 : ℚ))) = 1
    have hv := dyadic4_moving h 8
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₄_int_eq_if_mod_four,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter4Linear (Additive.ofMul (rationalSquareClass (h.primes 9 : ℚ))) = 0
    have hv := dyadic4_moving h 9
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₄_int_eq_if_mod_four,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter4Linear (Additive.ofMul (rationalSquareClass (h.primes 10 : ℚ))) = 0
    have hv := dyadic4_moving h 10
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₄_int_eq_if_mod_four,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter4Linear (Additive.ofMul (rationalSquareClass (h.primes 11 : ℚ))) = 1
    have hv := dyadic4_moving h 11
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₄_int_eq_if_mod_four,
      quadraticCharacterBit] at hv
    exact hv

theorem dyadic8_Ep_row :
    squareClassCharacterRow dyadicCharacter8Linear
      (signedPrimeColumns (primeColumns7Ep h.primes)) = Binary.vector 13 3412 := by
  rw [signed_columnsEp_eq]
  funext j
  fin_cases j
  · change dyadicCharacter8Linear (Additive.ofMul (rationalSquareClass (-1 : ℚ))) = 0
    have hv := dyadic8_int (-1) (by norm_num)
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₈_int_eq_if_mod_eight,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter8Linear (Additive.ofMul (rationalSquareClass (2 : ℚ))) = 0
    exact dyadic8_self
  · change dyadicCharacter8Linear (Additive.ofMul (rationalSquareClass (3 : ℚ))) = 1
    have hv := dyadic8_int 3 (by norm_num)
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₈_int_eq_if_mod_eight,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter8Linear (Additive.ofMul (rationalSquareClass (7 : ℚ))) = 0
    have hv := dyadic8_int 7 (by norm_num)
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₈_int_eq_if_mod_eight,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter8Linear (Additive.ofMul (rationalSquareClass (13 : ℚ))) = 1
    have hv := dyadic8_int 13 (by norm_num)
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₈_int_eq_if_mod_eight,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter8Linear (Additive.ofMul (rationalSquareClass (h.primes 0 : ℚ))) = 0
    have hv := dyadic8_moving h 0
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₈_int_eq_if_mod_eight,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter8Linear (Additive.ofMul (rationalSquareClass (h.primes 1 : ℚ))) = 1
    have hv := dyadic8_moving h 1
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₈_int_eq_if_mod_eight,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter8Linear (Additive.ofMul (rationalSquareClass (h.primes 2 : ℚ))) = 0
    have hv := dyadic8_moving h 2
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₈_int_eq_if_mod_eight,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter8Linear (Additive.ofMul (rationalSquareClass (h.primes 3 : ℚ))) = 1
    have hv := dyadic8_moving h 3
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₈_int_eq_if_mod_eight,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter8Linear (Additive.ofMul (rationalSquareClass (h.primes 8 : ℚ))) = 0
    have hv := dyadic8_moving h 8
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₈_int_eq_if_mod_eight,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter8Linear (Additive.ofMul (rationalSquareClass (h.primes 9 : ℚ))) = 1
    have hv := dyadic8_moving h 9
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₈_int_eq_if_mod_eight,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter8Linear (Additive.ofMul (rationalSquareClass (h.primes 10 : ℚ))) = 1
    have hv := dyadic8_moving h 10
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₈_int_eq_if_mod_eight,
      quadraticCharacterBit] at hv
    exact hv
  · change dyadicCharacter8Linear (Additive.ofMul (rationalSquareClass (h.primes 11 : ℚ))) = 0
    have hv := dyadic8_moving h 11
    norm_num [PrimePatterns.Rank7.mod8Units, ZMod.χ₈_int_eq_if_mod_eight,
      quadraticCharacterBit] at hv
    exact hv

theorem two_valuation_row :
    squareClassCharacterRow (valuationParityLinear 2)
      (signedPrimeColumns (primeColumns7E h.primes)) = Binary.vector 13 2 := by
  have hs2 := primeParity_prime (p := 2) (q := 2) (by decide +kernel) (by decide +kernel)
  have hs3 := primeParity_prime (p := 2) (q := 3) (by decide +kernel) (by decide +kernel)
  have hs7 := primeParity_prime (p := 2) (q := 7) (by decide +kernel) (by decide +kernel)
  have hs13 := primeParity_prime (p := 2) (q := 13) (by decide +kernel) (by decide +kernel)
  norm_num at hs2 hs3 hs7 hs13
  rw [signed_columnsE_eq]
  funext j
  fin_cases j <;> simp only [squareClassCharacterRow, valuationParityLinear, AddMonoidHom.coe_toZModLinearMap]
  all_goals norm_num [hs2, hs3, hs7, hs13, primeParity_neg_one,
    fixed_moving_parity h 2 (by simp), Binary.vector, Binary.scalar]
  all_goals decide +kernel

theorem original_dyadic_combined_row :
    squareClassCharacterRow (dyadicCharacter4Linear + valuationParityLinear 2)
      (signedPrimeColumns (primeColumns7E h.primes)) = Binary.vector 13 4943 := by
  change squareClassCharacterRow dyadicCharacter4Linear _ +
    squareClassCharacterRow (valuationParityLinear 2) _ = _
  rw [dyadic4_E_row h, two_valuation_row h]
  decide +kernel

theorem partner_dyadic_combined_row :
    squareClassCharacterRow (dyadicCharacter4Linear + dyadicCharacter8Linear)
      (signedPrimeColumns (primeColumns7Ep h.primes)) = Binary.vector 13 7705 := by
  change squareClassCharacterRow dyadicCharacter4Linear _ +
    squareClassCharacterRow dyadicCharacter8Linear _ = _
  rw [dyadic4_Ep_row h, dyadic8_Ep_row h]
  decide +kernel

end RankCertificates.Rank7FixedRows
