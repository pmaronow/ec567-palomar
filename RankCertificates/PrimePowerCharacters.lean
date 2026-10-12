module

public import RankCertificates.PrimePowerResidues
public import RankCertificates.LocalCharacterRows

/-! Quadratic characters of normalized prime-power units descend to the
actual rational squareclass group. In particular this supplies the two
dyadic binary rows from the primitive characters modulo 4 and 8. -/

@[expose] public section

namespace RankCertificates.PrimePowerCharacters

open PrimePowerResidues

variable (p k : ℕ) [Fact p.Prime]
    (χ : MulChar (ZMod (p ^ k)) ℤ) (hχ : χ.IsQuadratic)

noncomputable def powerCharacter (q : ℚ) : ℤ := χ (unitResiduePow p k q)

include hχ in
theorem powerCharacter_dichotomy {q : ℚ} (hq : q ≠ 0) :
    powerCharacter p k χ q = 1 ∨ powerCharacter p k χ q = -1 :=
  (hχ _).resolve_left ((MulChar.apply_ne_zero_iff).mpr (unitResiduePow_isUnit p k hq))

theorem powerCharacter_mul {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) :
    powerCharacter p k χ (q * r) = powerCharacter p k χ q * powerCharacter p k χ r := by
  simp only [powerCharacter, unitResiduePow_mul p k hq hr, map_mul]

@[simp] theorem powerCharacter_one : powerCharacter p k χ 1 = 1 := by
  simp [powerCharacter]

include hχ in
theorem powerCharacter_square {q : ℚ} (hq : q ≠ 0) :
    powerCharacter p k χ (q ^ 2) = 1 := by
  rw [pow_two, powerCharacter_mul p k χ hq hq]
  rcases powerCharacter_dichotomy p k χ hχ hq with he | he <;> rw [he] <;> norm_num

noncomputable def rationalUnitPowerCharacterParity : ℚˣ →* Multiplicative (ZMod 2) where
  toFun u := Multiplicative.ofAdd (quadraticCharacterBit (powerCharacter p k χ (u : ℚ)))
  map_one' := by
    change quadraticCharacterBit (powerCharacter p k χ 1) = 0
    rw [powerCharacter_one, quadraticCharacterBit_one]
  map_mul' u v := by
    change quadraticCharacterBit (powerCharacter p k χ ((u : ℚ) * (v : ℚ))) =
      quadraticCharacterBit (powerCharacter p k χ (u : ℚ)) +
        quadraticCharacterBit (powerCharacter p k χ (v : ℚ))
    rw [powerCharacter_mul p k χ u.ne_zero v.ne_zero]
    exact quadraticCharacterBit_mul (powerCharacter_dichotomy p k χ hχ u.ne_zero)
      (powerCharacter_dichotomy p k χ hχ v.ne_zero)

theorem squares_le_powerCharacterParity_ker :
    (powMonoidHom (α := ℚˣ) 2).range ≤
      (rationalUnitPowerCharacterParity p k χ hχ).ker := by
  rintro u ⟨v, rfl⟩
  change quadraticCharacterBit (powerCharacter p k χ ((v : ℚ) ^ 2)) = 0
  rw [powerCharacter_square p k χ hχ v.ne_zero, quadraticCharacterBit_one]

noncomputable def rationalSquareClassPowerCharacterParity :
    RationalSquareClasses →* Multiplicative (ZMod 2) :=
  QuotientGroup.lift _ (rationalUnitPowerCharacterParity p k χ hχ)
    (squares_le_powerCharacterParity_ker p k χ hχ)

noncomputable def powerCharacterParity : Additive RationalSquareClasses →+ ZMod 2 :=
  (rationalSquareClassPowerCharacterParity p k χ hχ).toAdditiveLeft

theorem powerCharacterParity_apply {q : ℚ} (hq : q ≠ 0) :
    powerCharacterParity p k χ hχ (Additive.ofMul (rationalSquareClass q)) =
      quadraticCharacterBit (powerCharacter p k χ q) := by
  rw [rationalSquareClass, dite_eq_right hq]
  rfl

noncomputable def powerCharacterLinear :
    Additive RationalSquareClasses →ₗ[ZMod 2] ZMod 2 :=
  (powerCharacterParity p k χ hχ).toZModLinearMap 2

/-- Any proved character-one restriction on actual representatives gives
annihilation by the corresponding genuine squareclass functional. -/
theorem powerCharacterLinear_actualImage {a b : ℚ} {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage a b)
    (hc : ∀ z : ℚ, z ≠ 0 → rationalSquareClass z = q → powerCharacter p k χ z = 1) :
    powerCharacterLinear p k χ hχ (Additive.ofMul q) = 0 := by
  revert hq hc
  refine QuotientGroup.induction_on q fun u hq hc => ?_
  rw [← rationalSquareClass_unit u]
  change powerCharacterParity p k χ hχ (Additive.ofMul (rationalSquareClass (u : ℚ))) = 0
  rw [powerCharacterParity_apply p k χ hχ u.ne_zero,
    hc u u.ne_zero (rationalSquareClass_unit u), quadraticCharacterBit_one]

/-- The normalized dyadic character modulo 4. -/
noncomputable abbrev dyadicCharacter4 := powerCharacter 2 2 ZMod.χ₄

/-- The normalized dyadic character modulo 8. -/
noncomputable abbrev dyadicCharacter8 := powerCharacter 2 3 ZMod.χ₈

noncomputable abbrev dyadicCharacter4Linear :=
  powerCharacterLinear 2 2 ZMod.χ₄ ZMod.isQuadratic_χ₄

noncomputable abbrev dyadicCharacter8Linear :=
  powerCharacterLinear 2 3 ZMod.χ₈ ZMod.isQuadratic_χ₈

end RankCertificates.PrimePowerCharacters
