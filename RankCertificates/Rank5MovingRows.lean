module

public import RankCertificates.Rank5LiteralRows

@[expose] public section

namespace RankCertificates.Rank5MovingRows

open Rank5CharacterEvaluation Rank5CharacterRows Rank5LiteralRows

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {x y : ℤ} (h : PrimeSpecialization5 x y)

def indexE : Fin 8 → Fin 12 := ![0, 1, 2, 3, 8, 9, 10, 11]
def indexEp : Fin 8 → Fin 12 := ![0, 1, 2, 3, 4, 5, 6, 7]
def codesE0 : Fin 8 → ℕ := ![1424, 642, 322, 4029, 3888, 37, 924, 2572]
def codesE1 : Fin 8 → ℕ := ![2656, 3442, 3762, 77, 192, 4053, 3180, 1532]
def codesEp0 : Fin 8 → ℕ := ![1424, 898, 66, 1597, 1494, 3887, 799, 2442]
def codesEp1 : Fin 8 → ℕ := ![2656, 3186, 4018, 2509, 2598, 223, 3311, 1658]

theorem rowsE0_certificate : ∀ k, movingRowE 1 (indexE k) = Binary.vector 12 (codesE0 k) := by
  decide +kernel

theorem rowsE1_certificate : ∀ k, movingRowE (-1) (indexE k) = Binary.vector 12 (codesE1 k) := by
  decide +kernel

theorem rowsEp0_certificate : ∀ k, movingRowEp 1 (indexEp k) = Binary.vector 12 (codesEp0 k) := by
  decide +kernel

theorem rowsEp1_certificate : ∀ k, movingRowEp (-1) (indexEp k) = Binary.vector 12 (codesEp1 k) := by
  decide +kernel

noncomputable def functionalE (k : Fin 8) :
    Additive RationalSquareClasses →ₗ[ZMod 2] ZMod 2 :=
  if (indexE k).val < 4 then
    @typeIIICharacterLinear (h.primes (indexE k)) ⟨h.prime (indexE k)⟩
      (Rank5.b (Integration.M5 x) (Integration.N5 y))
  else @unitCharacterLinear (h.primes (indexE k)) ⟨h.prime (indexE k)⟩

noncomputable def functionalEp (k : Fin 8) :
    Additive RationalSquareClasses →ₗ[ZMod 2] ZMod 2 :=
  if (indexEp k).val < 4 then
    @typeIIICharacterLinear (h.primes (indexEp k)) ⟨h.prime (indexEp k)⟩
      (Rank5.c (Integration.M5 x) (Integration.N5 y))
  else @unitCharacterLinear (h.primes (indexEp k)) ⟨h.prime (indexEp k)⟩

theorem functionalE_row (k : Fin 8) :
    squareClassCharacterRow (functionalE h k) (columnsE h.primes) =
      movingRowE (epsilon h) (indexE k) := by
  let : Fact (h.primes (indexE k)).Prime := ⟨h.prime (indexE k)⟩
  by_cases hi : (indexE k).val < 4
  · simp only [functionalE, ite_eq_left hi]
    exact typeIIIRowE_actual h _ hi
  · have hidx : ERowIndex (indexE k) := by fin_cases k <;> simp [indexE, ERowIndex]
    simp only [functionalE, movingRowE, ite_eq_right hi]
    change unitCharacterRow (h.primes (indexE k)) (columnsE h.primes) = _
    exact unitRowE_actual h _ hidx

theorem functionalEp_row (k : Fin 8) :
    squareClassCharacterRow (functionalEp h k) (columnsEp h.primes) =
      movingRowEp (epsilon h) (indexEp k) := by
  let : Fact (h.primes (indexEp k)).Prime := ⟨h.prime (indexEp k)⟩
  by_cases hi : (indexEp k).val < 4
  · simp only [functionalEp, ite_eq_left hi]
    exact typeIIIRowEp_actual h _ hi
  · have hidx : EpRowIndex (indexEp k) := by fin_cases k <;> simp [indexEp, EpRowIndex]
    simp only [functionalEp, movingRowEp, ite_eq_right hi]
    change unitCharacterRow (h.primes (indexEp k)) (columnsEp h.primes) = _
    exact unitRowEp_actual h _ hidx

theorem functionalE_literal (k : Fin 8) :
    squareClassCharacterRow (functionalE h k) (columnsE h.primes) =
      Binary.vector 12 (if epsilon h = 1 then codesE0 k else codesE1 k) := by
  rw [functionalE_row]
  rcases epsilon_dichotomy h with he | he
  · simp only [he, ite_true]
    exact rowsE0_certificate k
  · simp only [he, show (-1 : ℤ) ≠ 1 by decide, ite_false]
    exact rowsE1_certificate k

theorem functionalEp_literal (k : Fin 8) :
    squareClassCharacterRow (functionalEp h k) (columnsEp h.primes) =
      Binary.vector 12 (if epsilon h = 1 then codesEp0 k else codesEp1 k) := by
  rw [functionalEp_row]
  rcases epsilon_dichotomy h with he | he
  · simp only [he, ite_true]
    exact rowsEp0_certificate k
  · simp only [he, show (-1 : ℤ) ≠ 1 by decide, ite_false]
    exact rowsEp1_certificate k

theorem functionalE_actualImage (k : Fin 8) {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (Rank5.a (Integration.M5 x) (Integration.N5 y))
      (Rank5.b (Integration.M5 x) (Integration.N5 y))) :
    functionalE h k (Additive.ofMul q) = 0 := by
  let : Fact (h.primes (indexE k)).Prime := ⟨h.prime (indexE k)⟩
  by_cases hi : (indexE k).val < 4
  · simp only [functionalE, ite_eq_left hi]
    obtain ⟨ha, hb, _, _⟩ := Rank5PrimeValuations.typeIII_coefficient_valuations h _ hi
    exact typeIIICharacterLinear_actualImage _ (by omega) hb hq
  · have hJ : 8 ≤ (indexE k).val := by fin_cases k <;> simp [indexE] at hi ⊢
    simp only [functionalE, ite_eq_right hi]
    revert hq
    refine QuotientGroup.induction_on q fun u hq => ?_
    rw [← rationalSquareClass_unit u] at hq ⊢
    change unitCharacterParity (h.primes (indexE k))
      (Additive.ofMul (rationalSquareClass (u : ℚ))) = 0
    rw [unitCharacterParity_apply _ u.ne_zero,
      Rank5PrimeValuations.J_prime_E_image_character h _ hJ hq u.ne_zero rfl,
      quadraticCharacterBit_one]

theorem functionalEp_actualImage (k : Fin 8) {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (-2 * Rank5.a (Integration.M5 x) (Integration.N5 y))
      (Rank5.c (Integration.M5 x) (Integration.N5 y))) :
    functionalEp h k (Additive.ofMul q) = 0 := by
  let : Fact (h.primes (indexEp k)).Prime := ⟨h.prime (indexEp k)⟩
  by_cases hi : (indexEp k).val < 4
  · simp only [functionalEp, ite_eq_left hi]
    obtain ⟨_, _, hb, ha⟩ := Rank5PrimeValuations.typeIII_coefficient_valuations h _ hi
    exact typeIIICharacterLinear_actualImage _ (by omega) hb hq
  · have hH : 4 ≤ (indexEp k).val ∧ (indexEp k).val < 8 := by
      fin_cases k <;> simp [indexEp] at hi ⊢
    simp only [functionalEp, ite_eq_right hi]
    revert hq
    refine QuotientGroup.induction_on q fun u hq => ?_
    rw [← rationalSquareClass_unit u] at hq ⊢
    change unitCharacterParity (h.primes (indexEp k))
      (Additive.ofMul (rationalSquareClass (u : ℚ))) = 0
    rw [unitCharacterParity_apply _ u.ne_zero,
      Rank5PrimeValuations.H_prime_Ep_image_character h _ hH.1 hH.2 hq u.ne_zero rfl,
      quadraticCharacterBit_one]

end RankCertificates.Rank5MovingRows
