module

public import RankCertificates.LocalValuations
public import RankCertificates.SquareClassClassification

/-!
# Local quadratic characters as actual binary rows

The character of the normalized unit descends to rational squareclasses.
Its binary parity is a linear functional, so local conditions on actual point
images become equations on the corresponding prime-column vectors.
-/

@[expose] public section

namespace RankCertificates

/-- Binary parity of a sign character: `1` maps to zero and `-1` to one. -/
def quadraticCharacterBit (x : ℤ) : ZMod 2 := if x = 1 then 0 else 1

@[simp] theorem quadraticCharacterBit_one : quadraticCharacterBit 1 = 0 := by
  simp [quadraticCharacterBit]

@[simp] theorem quadraticCharacterBit_neg_one : quadraticCharacterBit (-1) = 1 := by
  norm_num [quadraticCharacterBit]

theorem quadraticCharacterBit_mul {x y : ℤ}
    (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) :
    quadraticCharacterBit (x * y) = quadraticCharacterBit x + quadraticCharacterBit y := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> decide +kernel

/-- The normalized unit character of a nonzero rational has values `±1`. -/
theorem unitCharacter_dichotomy (p : ℕ) [Fact p.Prime] {x : ℚ} (hx : x ≠ 0) :
    LocalValuations.unitCharacter p x = 1 ∨ LocalValuations.unitCharacter p x = -1 :=
  quadraticChar_dichotomy (LocalValuations.unitResidue_ne_zero p hx)

/-- Rational squares have trivial normalized unit character. -/
theorem unitCharacter_square (p : ℕ) [Fact p.Prime] {x : ℚ} (hx : x ≠ 0) :
    LocalValuations.unitCharacter p (x ^ 2) = 1 :=
  (LocalValuations.unitCharacter_eq_one_iff p (pow_ne_zero 2 hx)).mpr
    (LocalValuations.unitResidue_square p hx)

/-- Character parity is a homomorphism on nonzero rational units. -/
def rationalUnitCharacterParity (p : ℕ) [Fact p.Prime] :
    ℚˣ →* Multiplicative (ZMod 2) where
  toFun u := Multiplicative.ofAdd
    (quadraticCharacterBit (LocalValuations.unitCharacter p (u : ℚ)))
  map_one' := by
    have hc := unitCharacter_square p (x := (1 : ℚ)) one_ne_zero
    norm_num only [one_pow] at hc
    change quadraticCharacterBit (LocalValuations.unitCharacter p 1) = 0
    rw [hc, quadraticCharacterBit_one]
  map_mul' u v := by
    change quadraticCharacterBit (LocalValuations.unitCharacter p ((u : ℚ) * (v : ℚ))) =
      quadraticCharacterBit (LocalValuations.unitCharacter p (u : ℚ)) +
        quadraticCharacterBit (LocalValuations.unitCharacter p (v : ℚ))
    rw [LocalValuations.unitCharacter_mul p u.ne_zero v.ne_zero]
    exact quadraticCharacterBit_mul (unitCharacter_dichotomy p u.ne_zero)
      (unitCharacter_dichotomy p v.ne_zero)

theorem squares_le_rationalUnitCharacterParity_ker (p : ℕ) [Fact p.Prime] :
    (powMonoidHom (α := ℚˣ) 2).range ≤ (rationalUnitCharacterParity p).ker := by
  rintro u ⟨v, rfl⟩
  change quadraticCharacterBit (LocalValuations.unitCharacter p ((v : ℚ) ^ 2)) = 0
  rw [unitCharacter_square p v.ne_zero, quadraticCharacterBit_one]

/-- Character parity on the genuine quotient by rational squares. -/
def rationalSquareClassUnitCharacterParity (p : ℕ) [Fact p.Prime] :
    RationalSquareClasses →* Multiplicative (ZMod 2) :=
  QuotientGroup.lift _ (rationalUnitCharacterParity p)
    (squares_le_rationalUnitCharacterParity_ker p)

/-- The additive local quadratic character on rational squareclasses. -/
def unitCharacterParity (p : ℕ) [Fact p.Prime] :
    Additive RationalSquareClasses →+ ZMod 2 :=
  (rationalSquareClassUnitCharacterParity p).toAdditiveLeft

theorem unitCharacterParity_apply (p : ℕ) [Fact p.Prime] {x : ℚ} (hx : x ≠ 0) :
    unitCharacterParity p (Additive.ofMul (rationalSquareClass x)) =
      quadraticCharacterBit (LocalValuations.unitCharacter p x) := by
  rw [rationalSquareClass, dite_eq_right hx]
  rfl

/-- Local character parity as a binary linear functional. -/
noncomputable def unitCharacterLinear (p : ℕ) [Fact p.Prime] :
    Additive RationalSquareClasses →ₗ[ZMod 2] ZMod 2 :=
  (unitCharacterParity p).toZModLinearMap 2

/-- The actual quadratic-character values of the rational columns. -/
def unitCharacterRow {n : ℕ} (p : ℕ) [Fact p.Prime] (columns : Fin n → ℚ) :
    Fin n → ZMod 2 :=
  fun i => unitCharacterParity p (Additive.ofMul (rationalSquareClass (columns i)))

theorem unitCharacterRow_apply {n : ℕ} (p : ℕ) [Fact p.Prime]
    (columns : Fin n → ℚ) (i : Fin n) (hi : columns i ≠ 0) :
    unitCharacterRow p columns i =
      quadraticCharacterBit (LocalValuations.unitCharacter p (columns i)) :=
  unitCharacterParity_apply p hi

/-- On an integral prime unit, the row entry is the bit of the literal
Legendre symbol. -/
theorem unitCharacterParity_int_of_not_dvd (p : ℕ) [Fact p.Prime] {x : ℤ}
    (hx : ¬ (p : ℤ) ∣ x) :
    unitCharacterParity p (Additive.ofMul (rationalSquareClass (x : ℚ))) =
      quadraticCharacterBit (legendreSym p x) := by
  have hx0 : (x : ℚ) ≠ 0 := by
    exact_mod_cast (show x ≠ 0 from fun hz => hx (hz ▸ dvd_zero _))
  rw [unitCharacterParity_apply p hx0,
    LocalValuations.unitCharacter_int_of_not_dvd p hx]

/-- The prime itself has normalized unit one. -/
theorem unitCharacterParity_prime_self (p : ℕ) [Fact p.Prime] :
    unitCharacterParity p (Additive.ofMul (rationalSquareClass (p : ℚ))) = 0 := by
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [unitCharacterParity_apply p hp0]
  have hunit : LocalValuations.unitResidue p (p : ℚ) = 1 := by
    simp [LocalValuations.unitResidue, LocalValuations.normalizedUnit,
      padicValRat.self (Fact.out : p.Prime).one_lt, hp0,
      LocalValuations.rationalResidue]
  simp only [LocalValuations.unitCharacter, hunit, map_one, quadraticCharacterBit_one]

/-- Applying the genuine local character to a squareclass combination is
exactly the binary dot product with its character row. -/
theorem unitCharacterLinear_squareClassLinearMap {n : ℕ} (p : ℕ) [Fact p.Prime]
    (columns : Fin n → ℚ) (v : Fin n → ZMod 2) :
    unitCharacterLinear p (squareClassLinearMap columns v) =
      ∑ i, unitCharacterRow p columns i * v i := by
  simp only [squareClassLinearMap, Fintype.linearCombination_apply, map_sum, map_smul]
  simp only [unitCharacterLinear, AddMonoidHom.coe_toZModLinearMap,
    unitCharacterRow, smul_eq_mul, mul_comm]

/-- A verified literal row computes the local character of each bounded
mask using the archive's least-significant-bit convention. -/
theorem unitCharacterLinear_mask_dot {n : ℕ} (p : ℕ) [Fact p.Prime]
    (columns : Fin n → ℚ) (row code : ℕ)
    (hrow : unitCharacterRow p columns = Binary.vector n row) :
    unitCharacterLinear p (squareClassLinearMap columns (Binary.vector n code)) =
      Binary.scalar (Binary.dot n row code) := by
  rw [unitCharacterLinear_squareClassLinearMap, hrow, Binary.dot_eq_sum]

/-- Every actual type-II image class is annihilated by the genuine local
character functional. -/
theorem unitCharacterLinear_typeII (p : ℕ) [Fact p.Prime] {a b : ℚ}
    (hp : p ≠ 2) (ha0 : a ≠ 0) (ha : padicValRat p a = 0)
    (hb0 : b ≠ 0) (hb : padicValRat p b = 0)
    (hd : padicValRat p (a ^ 2 - 4 * b) = 1)
    {q : RationalSquareClasses} (hq : q ∈ twoIsogenyImage a b) :
    unitCharacterLinear p (Additive.ofMul q) = 0 := by
  revert hq
  refine QuotientGroup.induction_on q fun u hq => ?_
  rw [← rationalSquareClass_unit u]
  change unitCharacterParity p (Additive.ofMul (rationalSquareClass (u : ℚ))) = 0
  rw [unitCharacterParity_apply p u.ne_zero]
  rw [LocalValuations.twoIsogenyImage_discriminant_prime_unitCharacter_eq_one
    p hp ha0 ha hb0 hb hd hq u.ne_zero (rationalSquareClass_unit u),
    quadraticCharacterBit_one]

/-- At a type-III prime, the character bit equals the valuation bit times
the character bit of the linear coefficient. -/
theorem unitCharacterLinear_typeIII (p : ℕ) [Fact p.Prime] {a b : ℚ}
    (ha : 1 ≤ padicValRat p a) (hb : padicValRat p b = 1)
    {q : RationalSquareClasses} (hq : q ∈ twoIsogenyImage a b) :
    unitCharacterLinear p (Additive.ofMul q) =
      unitCharacterParity p (Additive.ofMul (rationalSquareClass b)) *
        primeParity p (Fact.out : p.Prime) (Additive.ofMul q) := by
  have hb0 : b ≠ 0 := by intro hz; rw [hz] at hb; simp at hb
  revert hq
  refine QuotientGroup.induction_on q fun u hq => ?_
  rw [← rationalSquareClass_unit u]
  change unitCharacterParity p (Additive.ofMul (rationalSquareClass (u : ℚ))) = _
  rw [unitCharacterParity_apply p u.ne_zero, unitCharacterParity_apply p hb0,
    primeParity_apply (Fact.out : p.Prime) u.ne_zero]
  have hparity := LocalValuations.twoIsogenyImage_moving_prime_unitCharacter_parity
    p ha hb hq u.ne_zero (rationalSquareClass_unit u)
  by_cases he : Even (padicValRat p (u : ℚ))
  · rw [hparity.1 he, quadraticCharacterBit_one, he.intCast_zmod_two, mul_zero]
  · have ho := Int.not_even_iff_odd.mp he
    rw [hparity.2 ho, ho.intCast_zmod_two, mul_one]

/-- The combined normalized-unit and valuation row at a type-III prime. -/
noncomputable def typeIIICharacterLinear (p : ℕ) [Fact p.Prime] (b : ℚ) :
    Additive RationalSquareClasses →ₗ[ZMod 2] ZMod 2 :=
  unitCharacterLinear p +
    unitCharacterParity p (Additive.ofMul (rationalSquareClass b)) •
      (primeParity p (Fact.out : p.Prime)).toZModLinearMap 2

/-- Actual type-III image classes satisfy the combined binary row. -/
theorem typeIIICharacterLinear_actualImage (p : ℕ) [Fact p.Prime] {a b : ℚ}
    (ha : 1 ≤ padicValRat p a) (hb : padicValRat p b = 1)
    {q : RationalSquareClasses} (hq : q ∈ twoIsogenyImage a b) :
    typeIIICharacterLinear p b (Additive.ofMul q) = 0 := by
  simp only [typeIIICharacterLinear, LinearMap.add_apply, LinearMap.smul_apply,
    AddMonoidHom.coe_toZModLinearMap, smul_eq_mul]
  rw [unitCharacterLinear_typeIII p ha hb hq]
  exact CharTwo.add_self_eq_zero _

/-- Any binary functional has its literal coordinate row. -/
def squareClassCharacterRow {n : ℕ}
    (f : Additive RationalSquareClasses →ₗ[ZMod 2] ZMod 2)
    (columns : Fin n → ℚ) : Fin n → ZMod 2 :=
  fun i => f (Additive.ofMul (rationalSquareClass (columns i)))

theorem characterLinear_squareClassLinearMap {n : ℕ}
    (f : Additive RationalSquareClasses →ₗ[ZMod 2] ZMod 2)
    (columns : Fin n → ℚ) (v : Fin n → ZMod 2) :
    f (squareClassLinearMap columns v) =
      ∑ i, squareClassCharacterRow f columns i * v i := by
  simp only [squareClassLinearMap, Fintype.linearCombination_apply, map_sum, map_smul]
  simp only [squareClassCharacterRow, smul_eq_mul, mul_comm]

/-- Type-II local solubility imposes a genuine binary dot-product equation. -/
theorem actualImage_typeII_row {n : ℕ} (p : ℕ) [Fact p.Prime] {a b : ℚ}
    (hp : p ≠ 2) (ha0 : a ≠ 0) (ha : padicValRat p a = 0)
    (hb0 : b ≠ 0) (hb : padicValRat p b = 0)
    (hd : padicValRat p (a ^ 2 - 4 * b) = 1)
    (columns : Fin n → ℚ) (v : Fin n → ZMod 2)
    (hq : (squareClassLinearMap columns v).toMul ∈ twoIsogenyImage a b) :
    ∑ i, unitCharacterRow p columns i * v i = 0 := by
  rw [← unitCharacterLinear_squareClassLinearMap]
  exact unitCharacterLinear_typeII p hp ha0 ha hb0 hb hd hq

/-- Type-III local solubility imposes the combined character/valuation row. -/
theorem actualImage_typeIII_row {n : ℕ} (p : ℕ) [Fact p.Prime] {a b : ℚ}
    (ha : 1 ≤ padicValRat p a) (hb : padicValRat p b = 1)
    (columns : Fin n → ℚ) (v : Fin n → ZMod 2)
    (hq : (squareClassLinearMap columns v).toMul ∈ twoIsogenyImage a b) :
    ∑ i, squareClassCharacterRow (typeIIICharacterLinear p b) columns i * v i = 0 := by
  rw [← characterLinear_squareClassLinearMap]
  exact typeIIICharacterLinear_actualImage p ha hb hq

/-- A verified literal type-II row vanishes on every actual image mask. -/
theorem actualImage_typeII_mask_dot {n : ℕ} (p : ℕ) [Fact p.Prime] {a b : ℚ}
    (hp : p ≠ 2) (ha0 : a ≠ 0) (ha : padicValRat p a = 0)
    (hb0 : b ≠ 0) (hb : padicValRat p b = 0)
    (hd : padicValRat p (a ^ 2 - 4 * b) = 1)
    (columns : Fin n → ℚ) (row code : ℕ)
    (hrow : unitCharacterRow p columns = Binary.vector n row)
    (hq : (squareClassLinearMap columns (Binary.vector n code)).toMul ∈
      twoIsogenyImage a b) : Binary.dot n row code = false := by
  apply (Binary.scalar_eq_zero _).mp
  rw [← unitCharacterLinear_mask_dot p columns row code hrow]
  exact unitCharacterLinear_typeII p hp ha0 ha hb0 hb hd hq

/-- A verified literal type-III row vanishes on every actual image mask. -/
theorem actualImage_typeIII_mask_dot {n : ℕ} (p : ℕ) [Fact p.Prime] {a b : ℚ}
    (ha : 1 ≤ padicValRat p a) (hb : padicValRat p b = 1)
    (columns : Fin n → ℚ) (row code : ℕ)
    (hrow : squareClassCharacterRow (typeIIICharacterLinear p b) columns =
      Binary.vector n row)
    (hq : (squareClassLinearMap columns (Binary.vector n code)).toMul ∈
      twoIsogenyImage a b) : Binary.dot n row code = false := by
  apply (Binary.scalar_eq_zero _).mp
  rw [Binary.dot_eq_sum, ← hrow, ← characterLinear_squareClassLinearMap]
  exact typeIIICharacterLinear_actualImage p ha hb hq

/-- Valuation parity as a linear functional on actual squareclasses. -/
noncomputable def valuationParityLinear (p : ℕ) [Fact p.Prime] :
    Additive RationalSquareClasses →ₗ[ZMod 2] ZMod 2 :=
  (primeParity p (Fact.out : p.Prime)).toZModLinearMap 2

/-- Combine a unit character with a scalar multiple of valuation parity.
This also covers fixed-prime character/valuation restrictions. -/
noncomputable def characterValuationLinear (p : ℕ) [Fact p.Prime] (c : ZMod 2) :
    Additive RationalSquareClasses →ₗ[ZMod 2] ZMod 2 :=
  unitCharacterLinear p + c • valuationParityLinear p

theorem typeIIICharacterLinear_eq (p : ℕ) [Fact p.Prime] (b : ℚ) :
    typeIIICharacterLinear p b = characterValuationLinear p
      (unitCharacterParity p (Additive.ofMul (rationalSquareClass b))) := rfl

/-- An exact parity-coupled character identity is the combined row equation. -/
theorem characterValuationLinear_eq_zero_of_relation (p : ℕ) [Fact p.Prime]
    (c : ZMod 2) (q : RationalSquareClasses)
    (h : unitCharacterLinear p (Additive.ofMul q) =
      c * primeParity p (Fact.out : p.Prime) (Additive.ofMul q)) :
    characterValuationLinear p c (Additive.ofMul q) = 0 := by
  simp only [characterValuationLinear, valuationParityLinear, LinearMap.add_apply,
    LinearMap.smul_apply, AddMonoidHom.coe_toZModLinearMap, smul_eq_mul]
  rw [h]
  exact CharTwo.add_self_eq_zero _

/-- A parity exponent of an integer character is exactly multiplication
of its character bit by the exponent's binary parity. -/
theorem quadraticCharacterBit_parity_power (c e : ℤ) :
    quadraticCharacterBit (c ^ (e % 2).toNat) =
      quadraticCharacterBit c * (e : ZMod 2) := by
  by_cases he : Even e
  · have hm : e % 2 = 0 := by obtain ⟨k, hk⟩ := he; omega
    rw [hm, Int.toNat_zero, pow_zero, quadraticCharacterBit_one,
      he.intCast_zmod_two, mul_zero]
  · have ho := Int.not_even_iff_odd.mp he
    rw [Int.odd_iff.mp ho, Int.toNat_one, pow_one, ho.intCast_zmod_two, mul_one]

/-- A local normalized-character formula for a representative proves the
combined character/valuation row for its genuine squareclass. -/
theorem characterValuationLinear_representative_eq_zero
    (p : ℕ) [Fact p.Prime] (c : ℤ) {x : ℚ} (hx : x ≠ 0)
    (h : LocalValuations.unitCharacter p x = c ^ (padicValRat p x % 2).toNat) :
    characterValuationLinear p (quadraticCharacterBit c)
      (Additive.ofMul (rationalSquareClass x)) = 0 := by
  apply characterValuationLinear_eq_zero_of_relation
  change unitCharacterParity p (Additive.ofMul (rationalSquareClass x)) = _
  rw [unitCharacterParity_apply p hx, primeParity_apply (Fact.out : p.Prime) hx,
    h, quadraticCharacterBit_parity_power]

/-- Integral curves have the actual valuation row zero outside the support
of their linear coefficient. -/
theorem valuationParityLinear_outside_support (p : ℕ) [Fact p.Prime]
    (a b : ℤ) (hb : ¬ (p : ℤ) ∣ b) {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (a : ℚ) (b : ℚ)) :
    valuationParityLinear p (Additive.ofMul q) = 0 :=
  primeParity_zero_of_evenValuationClass (Fact.out : p.Prime) q
    (LocalDescent.twoIsogenyImage_even_valuation a b hb hq)

/-- The fixed-prime restriction at three gives both genuine binary
functionals, for every actual image class. -/
theorem actualImage_three_characters_zero (a b : ℤ)
    (ha : (a : ZMod 3) = 1) (hb : (b : ZMod 3) = 1)
    {q : RationalSquareClasses} (hq : q ∈ twoIsogenyImage (a : ℚ) (b : ℚ)) :
    valuationParityLinear 3 (Additive.ofMul q) = 0 ∧
      unitCharacterLinear 3 (Additive.ofMul q) = 0 := by
  revert hq
  refine QuotientGroup.induction_on q fun u hq => ?_
  have hl := LocalValuations.twoIsogenyImage_three_localConditions a b ha hb hq
    u.ne_zero (rationalSquareClass_unit u)
  rw [← rationalSquareClass_unit u]
  constructor
  · change primeParity 3 (Fact.out : Nat.Prime 3)
      (Additive.ofMul (rationalSquareClass (u : ℚ))) = 0
    rw [primeParity_apply (Fact.out : Nat.Prime 3) u.ne_zero]
    exact hl.1.intCast_zmod_two
  · change unitCharacterParity 3 (Additive.ofMul (rationalSquareClass (u : ℚ))) = 0
    rw [unitCharacterParity_apply 3 u.ne_zero]
    simp only [LocalValuations.unitCharacter, hl.2, map_one, quadraticCharacterBit_one]

/-- The sign functional at the real place. -/
noncomputable def realSignLinear : Additive RationalSquareClasses →ₗ[ZMod 2] ZMod 2 :=
  squareClassSign.toZModLinearMap 2

/-- A nonpositive quadratic coefficient and positive linear coefficient
force the genuine real-place row to vanish. -/
theorem realSignLinear_actualImage {a b : ℚ} (ha : a ≤ 0) (hb : 0 < b)
    {q : RationalSquareClasses} (hq : q ∈ twoIsogenyImage a b) :
    realSignLinear (Additive.ofMul q) = 0 := by
  revert hq
  refine QuotientGroup.induction_on q fun u hq => ?_
  rw [← rationalSquareClass_unit u]
  exact squareClassSign_of_pos
    (LocalValuations.twoIsogenyImage_positive ha hb hq u.ne_zero (rationalSquareClass_unit u))

end RankCertificates
