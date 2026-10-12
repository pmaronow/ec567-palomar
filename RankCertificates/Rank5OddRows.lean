module

public import RankCertificates.Rank5FixedRows

@[expose] public section

namespace RankCertificates.Rank5OddRows

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

variable {x y : ℤ} (h : PrimeSpecialization5 x y)

theorem three_actualImage {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (Rank5.a (Integration.M5 x) (Integration.N5 y))
      (Rank5.b (Integration.M5 x) (Integration.N5 y))) :
    unitCharacterLinear 3 (Additive.ofMul q) = 0 ∧
      valuationParityLinear 3 (Additive.ofMul q) = 0 := by
  revert hq
  refine QuotientGroup.induction_on q fun u hq => ?_
  rw [← rationalSquareClass_unit u] at hq ⊢
  obtain ⟨hv, hr⟩ := Rank5ThreeDescent.lattice_image_conditions x y hq u.ne_zero rfl
  constructor
  · change unitCharacterParity 3 (Additive.ofMul (rationalSquareClass (u : ℚ))) = 0
    rw [unitCharacterParity_apply 3 u.ne_zero]
    simp only [LocalValuations.unitCharacter, hr, map_one, quadraticCharacterBit_one]
  · change primeParity 3 (by decide) (Additive.ofMul (rationalSquareClass (u : ℚ))) = 0
    rw [primeParity_apply (by decide) u.ne_zero]
    exact hv.intCast_zmod_two

theorem five_E_actualImage {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (Rank5.a (Integration.M5 x) (Integration.N5 y))
      (Rank5.b (Integration.M5 x) (Integration.N5 y))) :
    unitCharacterLinear 5 (Additive.ofMul q) = 0 := by
  revert hq
  refine QuotientGroup.induction_on q fun u hq => ?_
  rw [← rationalSquareClass_unit u] at hq ⊢
  change unitCharacterParity 5 (Additive.ofMul (rationalSquareClass (u : ℚ))) = 0
  rw [unitCharacterParity_apply 5 u.ne_zero,
    Rank5FiveDescent.lattice_E_image_character x y hq u.ne_zero rfl,
    quadraticCharacterBit_one]

theorem five_Ep_actualImage {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (-2 * Rank5.a (Integration.M5 x) (Integration.N5 y))
      (Rank5.c (Integration.M5 x) (Integration.N5 y))) :
    unitCharacterLinear 5 (Additive.ofMul q) = 0 := by
  revert hq
  refine QuotientGroup.induction_on q fun u hq => ?_
  rw [← rationalSquareClass_unit u] at hq ⊢
  change unitCharacterParity 5 (Additive.ofMul (rationalSquareClass (u : ℚ))) = 0
  rw [unitCharacterParity_apply 5 u.ne_zero,
    Rank5FiveDescent.lattice_Ep_image_character x y hq u.ne_zero rfl,
    quadraticCharacterBit_one]

include h in
theorem real_Ep_actualImage {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (-2 * Rank5.a (Integration.M5 x) (Integration.N5 y))
      (Rank5.c (Integration.M5 x) (Integration.N5 y))) :
    realSignLinear (Additive.ofMul q) = 0 := by
  revert hq
  refine QuotientGroup.induction_on q fun u hq => ?_
  rw [← rationalSquareClass_unit u] at hq ⊢
  change squareClassSign (Additive.ofMul (rationalSquareClass (u : ℚ))) = 0
  exact squareClassSign_of_pos (Rank5PrimeValuations.dual_image_positive h hq u.ne_zero rfl)

end RankCertificates.Rank5OddRows
