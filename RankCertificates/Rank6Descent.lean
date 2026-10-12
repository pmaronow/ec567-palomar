module

public import RankCertificates.Rank6
public import RankCertificates.PrimePatterns
public import RankCertificates.LocalValuations
public import RankCertificates.LocalSeven
public import RankCertificates.LocalCharacterRows

/-!
# A genuine fixed-prime upper bound for the rank-six family

The original integral model has both coefficients equal to 1 modulo 3
throughout its congruence lattice. Every actual two-isogeny image therefore
has even 3-adic valuation and square normalized unit.
-/

@[expose] public section

namespace RankCertificates.Rank6Descent

def FInt (M N : ℤ) : ℤ := M * N * (169 * M + 750 * N) * (25 * M - 169 * N)
def HInt (M N : ℤ) : ℤ :=
  (M - 27 * N) * (7 * M + 20 * N) * (2 * M - 21 * N) * (9 * M + 10 * N)
def JInt (M N : ℤ) : ℤ :=
  (M + 15 * N) * (7 * M + 64 * N) * (M - 2 * N) * (32 * M - 105 * N)
def aInt (M N : ℤ) : ℤ := 70 * FInt M N
def bInt (M N : ℤ) : ℤ := -784 * FInt M N * HInt M N

theorem cast_aInt (M N : ℤ) : (aInt M N : ℚ) = Rank6.a (M : ℚ) (N : ℚ) := by
  simp [aInt, FInt, Rank6.a, Rank6.F, Rank6.L0, Rank6.L1, Rank6.L2, Rank6.L3]

theorem cast_bInt (M N : ℤ) : (bInt M N : ℚ) = Rank6.b (M : ℚ) (N : ℚ) := by
  simp [bInt, FInt, HInt, Rank6.b, Rank6.F, Rank6.H, Rank6.L0, Rank6.L1,
    Rank6.L2, Rank6.L3, Rank6.L4, Rank6.L5, Rank6.L6, Rank6.L7]

def A7 (M N : ℤ) : ℤ := 10 * FInt M N
def B7 (M N : ℤ) : ℤ := -16 * FInt M N * HInt M N
def A7dual (M N : ℤ) : ℤ := -20 * FInt M N
def B7dual (M N : ℤ) : ℤ := 36 * FInt M N * JInt M N

theorem seven_coefficients (M N : ℤ) :
    ((7 * A7 M N : ℤ) : ℚ) = Rank6.a (M : ℚ) (N : ℚ) ∧
    ((49 * B7 M N : ℤ) : ℚ) = Rank6.b (M : ℚ) (N : ℚ) ∧
    ((7 * A7dual M N : ℤ) : ℚ) = -2 * Rank6.a (M : ℚ) (N : ℚ) ∧
    ((49 * B7dual M N : ℤ) : ℚ) = Rank6.c (M : ℚ) (N : ℚ) := by
  have hF : (FInt M N : ℚ) = Rank6.F (M : ℚ) (N : ℚ) := by
    simp [FInt, Rank6.F, Rank6.L0, Rank6.L1, Rank6.L2, Rank6.L3]
  have hH : (HInt M N : ℚ) = Rank6.H (M : ℚ) (N : ℚ) := by
    simp [HInt, Rank6.H, Rank6.L4, Rank6.L5, Rank6.L6, Rank6.L7]
  have hJ : (JInt M N : ℚ) = Rank6.J (M : ℚ) (N : ℚ) := by
    simp [JInt, Rank6.J, Rank6.L8, Rank6.L9, Rank6.L10, Rank6.L11]
  simp only [A7, B7, A7dual, B7dual, Int.cast_mul, Int.cast_neg,
    Int.cast_ofNat, hF, hH, hJ, Rank6.a, Rank6.b, Rank6.c]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

theorem seven_normalized_residues (M N : ℤ)
    (hM : (M : ZMod 7) = 5) (hN : (N : ZMod 7) = 4) :
    (A7 M N : ZMod 7) = 2 ∧ (B7 M N : ZMod 7) = 4 ∧
    (A7dual M N : ZMod 7) = 3 ∧ (B7dual M N : ZMod 7) = 2 := by
  simp only [A7, B7, A7dual, B7dual, FInt, HInt, JInt, Int.cast_mul,
    Int.cast_add, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, hM, hN]
  decide

theorem coefficients_mod_three (M N : ℤ)
    (hM : (M : ZMod 3) = 1) (hN : (N : ZMod 3) = 2) :
    (aInt M N : ZMod 3) = 1 ∧ (bInt M N : ZMod 3) = 1 := by
  simp only [aInt, bInt, FInt, HInt, Int.cast_mul, Int.cast_add, Int.cast_sub,
    Int.cast_neg, Int.cast_ofNat, hM, hN]
  decide

/-- The necessary local upper bound applies to every representative of
every actual image class, uniformly in the parameter congruences. -/
theorem image_three_localConditions (M N : ℤ)
    (hM : (M : ZMod 3) = 1) (hN : (N : ZMod 3) = 2)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (Rank6.a (M : ℚ) (N : ℚ)) (Rank6.b (M : ℚ) (N : ℚ)))
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) :
    Even (padicValRat 3 z) ∧ LocalValuations.unitResidue 3 z = 1 := by
  obtain ⟨ha, hb⟩ := coefficients_mod_three M N hM hN
  apply LocalValuations.twoIsogenyImage_three_localConditions (aInt M N) (bInt M N)
    ha hb _ hz hc
  simpa only [cast_aInt, cast_bInt] using hq

theorem lattice_mod_three (x y : ℤ) :
    ((PrimePatterns.Rank6.M0 + PrimePatterns.Rank6.W * x : ℤ) : ZMod 3) = 1 ∧
    ((PrimePatterns.Rank6.N0 + PrimePatterns.Rank6.W * y : ℤ) : ZMod 3) = 2 := by
  have hW : (PrimePatterns.Rank6.W : ZMod 3) = 0 := by
    decide
  have hM : (PrimePatterns.Rank6.M0 : ZMod 3) = 1 := by
    decide
  have hN : (PrimePatterns.Rank6.N0 : ZMod 3) = 2 := by
    decide
  simp only [Int.cast_add, Int.cast_mul, hW, hM, hN, zero_mul, add_zero, and_self]

/-- The fixed-prime obstruction is proved on the exact rank-six lattice
used for the prime-producing affine forms. -/
theorem lattice_image_three_localConditions (x y : ℤ)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage
      (Rank6.a ((PrimePatterns.Rank6.M0 + PrimePatterns.Rank6.W * x : ℤ) : ℚ)
        ((PrimePatterns.Rank6.N0 + PrimePatterns.Rank6.W * y : ℤ) : ℚ))
      (Rank6.b ((PrimePatterns.Rank6.M0 + PrimePatterns.Rank6.W * x : ℤ) : ℚ)
        ((PrimePatterns.Rank6.N0 + PrimePatterns.Rank6.W * y : ℤ) : ℚ)))
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) :
    Even (padicValRat 3 z) ∧ LocalValuations.unitResidue 3 z = 1 := by
  obtain ⟨hM, hN⟩ := lattice_mod_three x y
  exact image_three_localConditions _ _ hM hN hq hz hc

/-- The dual image has positive representatives on the real cone used
for the prime specializations. -/
theorem dual_image_positive (M N : ℚ) (hN : 0 < N) (hM : 29 * N < M)
    {q : RationalSquareClasses} (hq : q ∈ twoIsogenyImage (-2 * Rank6.a M N) (Rank6.c M N))
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) : 0 < z := by
  obtain ⟨hF, _, hJ⟩ := Rank6.products_positive M N hN hM
  apply LocalValuations.twoIsogenyImage_positive _ _ hq hz hc
  · simp only [Rank6.a]
    nlinarith
  · simp only [Rank6.c]
    positivity

/-- The original fixed-7 row follows from the actual point equation. -/
theorem image_seven_character (M N : ℤ)
    (hM : (M : ZMod 7) = 5) (hN : (N : ZMod 7) = 4)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (Rank6.a (M : ℚ) (N : ℚ)) (Rank6.b (M : ℚ) (N : ℚ)))
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) :
    LocalValuations.unitCharacter 7 z = 1 := by
  obtain ⟨ha, hb, _⟩ := seven_normalized_residues M N hM hN
  apply LocalSeven.original_image_character (A7 M N) (B7 M N) ha hb _ hz hc
  simpa only [(seven_coefficients M N).1, (seven_coefficients M N).2.1] using hq

/-- The dual fixed-7 row is its genuine character-parity equality. -/
theorem dual_image_seven_character (M N : ℤ)
    (hM : (M : ZMod 7) = 5) (hN : (N : ZMod 7) = 4)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (-2 * Rank6.a (M : ℚ) (N : ℚ)) (Rank6.c (M : ℚ) (N : ℚ)))
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) :
    LocalValuations.unitCharacter 7 z = (-1 : ℤ) ^ (padicValRat 7 z % 2).toNat := by
  obtain ⟨_, _, ha, hb⟩ := seven_normalized_residues M N hM hN
  apply LocalSeven.dual_image_character (A7dual M N) (B7dual M N) ha hb _ hz hc
  simpa only [(seven_coefficients M N).2.2.1, (seven_coefficients M N).2.2.2] using hq

theorem lattice_mod_seven (x y : ℤ) :
    ((PrimePatterns.Rank6.M0 + PrimePatterns.Rank6.W * x : ℤ) : ZMod 7) = 5 ∧
    ((PrimePatterns.Rank6.N0 + PrimePatterns.Rank6.W * y : ℤ) : ZMod 7) = 4 := by
  have hW : (PrimePatterns.Rank6.W : ZMod 7) = 0 := by decide
  have hM : (PrimePatterns.Rank6.M0 : ZMod 7) = 5 := by decide
  have hN : (PrimePatterns.Rank6.N0 : ZMod 7) = 4 := by decide
  simp only [Int.cast_add, Int.cast_mul, hW, hM, hN, zero_mul, add_zero, and_self]

theorem lattice_image_seven_character (x y : ℤ)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage
      (Rank6.a ((PrimePatterns.Rank6.M0 + PrimePatterns.Rank6.W * x : ℤ) : ℚ)
        ((PrimePatterns.Rank6.N0 + PrimePatterns.Rank6.W * y : ℤ) : ℚ))
      (Rank6.b ((PrimePatterns.Rank6.M0 + PrimePatterns.Rank6.W * x : ℤ) : ℚ)
        ((PrimePatterns.Rank6.N0 + PrimePatterns.Rank6.W * y : ℤ) : ℚ)))
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) :
    LocalValuations.unitCharacter 7 z = 1 := by
  obtain ⟨hM, hN⟩ := lattice_mod_seven x y
  exact image_seven_character _ _ hM hN hq hz hc

theorem lattice_dual_image_seven_character (x y : ℤ)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage
      (-2 * Rank6.a ((PrimePatterns.Rank6.M0 + PrimePatterns.Rank6.W * x : ℤ) : ℚ)
        ((PrimePatterns.Rank6.N0 + PrimePatterns.Rank6.W * y : ℤ) : ℚ))
      (Rank6.c ((PrimePatterns.Rank6.M0 + PrimePatterns.Rank6.W * x : ℤ) : ℚ)
        ((PrimePatterns.Rank6.N0 + PrimePatterns.Rank6.W * y : ℤ) : ℚ)))
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) :
    LocalValuations.unitCharacter 7 z = (-1 : ℤ) ^ (padicValRat 7 z % 2).toNat := by
  obtain ⟨hM, hN⟩ := lattice_mod_seven x y
  exact dual_image_seven_character _ _ hM hN hq hz hc

theorem image_three_rows (M N : ℤ)
    (hM : (M : ZMod 3) = 1) (hN : (N : ZMod 3) = 2)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (Rank6.a (M : ℚ) (N : ℚ)) (Rank6.b (M : ℚ) (N : ℚ))) :
    valuationParityLinear 3 (Additive.ofMul q) = 0 ∧
      unitCharacterLinear 3 (Additive.ofMul q) = 0 := by
  obtain ⟨ha, hb⟩ := coefficients_mod_three M N hM hN
  apply actualImage_three_characters_zero (aInt M N) (bInt M N) ha hb
  simpa only [cast_aInt, cast_bInt] using hq

theorem image_seven_row (M N : ℤ)
    (hM : (M : ZMod 7) = 5) (hN : (N : ZMod 7) = 4)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (Rank6.a (M : ℚ) (N : ℚ)) (Rank6.b (M : ℚ) (N : ℚ))) :
    unitCharacterLinear 7 (Additive.ofMul q) = 0 := by
  revert hq
  refine QuotientGroup.induction_on q fun u hq => ?_
  have hchar := image_seven_character M N hM hN hq u.ne_zero (rationalSquareClass_unit u)
  rw [← rationalSquareClass_unit u]
  change unitCharacterParity 7 (Additive.ofMul (rationalSquareClass (u : ℚ))) = 0
  rw [unitCharacterParity_apply 7 u.ne_zero, hchar, quadraticCharacterBit_one]

theorem dual_image_seven_row (M N : ℤ)
    (hM : (M : ZMod 7) = 5) (hN : (N : ZMod 7) = 4)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (-2 * Rank6.a (M : ℚ) (N : ℚ)) (Rank6.c (M : ℚ) (N : ℚ))) :
    characterValuationLinear 7 1 (Additive.ofMul q) = 0 := by
  revert hq
  refine QuotientGroup.induction_on q fun u hq => ?_
  have hchar := dual_image_seven_character M N hM hN hq u.ne_zero (rationalSquareClass_unit u)
  have hzero := characterValuationLinear_representative_eq_zero 7 (-1) u.ne_zero hchar
  rw [rationalSquareClass_unit u, quadraticCharacterBit_neg_one] at hzero
  exact hzero

theorem dual_image_real_row (M N : ℚ) (hN : 0 < N) (hM : 29 * N < M)
    {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (-2 * Rank6.a M N) (Rank6.c M N)) :
    realSignLinear (Additive.ofMul q) = 0 := by
  obtain ⟨hF, _, hJ⟩ := Rank6.products_positive M N hN hM
  apply realSignLinear_actualImage _ _ hq
  · simp only [Rank6.a]
    nlinarith
  · simp only [Rank6.c]
    positivity

end RankCertificates.Rank6Descent
