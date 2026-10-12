module

public import RankCertificates.FixedCharacterEvaluation
public import RankCertificates.PrimeSpecializations

@[expose] public section

/-! Exact finite constant-character computations for the final rank-5
CRT lattice. The square-part data are checked against the homogeneous
form determinants; no character assumptions are supplied. -/

namespace RankCertificates.Rank5ConstantCharacters

open PrimePatterns

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def RelevantPair (i j : Fin 12) : Prop :=
  i ≠ j ∧ i ≠ 0 ∧ j ≠ 0 ∧
    (i.val < 4 ∨ (i.val < 8 ∧ (j.val < 4 ∨ 8 ≤ j.val)) ∨ (8 ≤ i.val ∧ j.val < 8))

def pairConstant (i j : Fin 12) : ℤ :=
  (Rank5.forms i).b * Rank5.cofactors j *
    ((Rank5.forms i).b * (Rank5.forms j).a -
      (Rank5.forms j).b * (Rank5.forms i).a) * 54

def pairSquarePart : Fin 12 → Fin 12 → ℤ := ![![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  ![1, 1, -105, 21318, 3927, -114, -51, 4389, 8778, -102, 119, -209],
  ![1, 105, 1, 3, 42, -1, -1, 21, 7, 3, 21, 1],
  ![1, 3304290, 465, 1, -935, 8835, 510, -32395, 6270, 2635, 510, 32395],
  ![1, 121737, 1302, 187, 1, 1, 1, 1, 231, 2635, 357, 1705],
  ![1, 114, 1, 57, 1, 1, 1, 1, 190, 3, 30, 19],
  ![1, 1581, 31, 102, 1, 1, 1, 1, 10, 3162, 255, 31],
  ![1, 8778, 42, 418, 1, 1, 1, 1, 4389, 10, 42, 1045],
  ![1, 136059, 434, -627, -462, 2945, 5, -136059, 1, 1, 1, 1],
  ![1, 102, -3, 17, 85, -3, -102, 5, 1, 1, 1, 1],
  ![1, 3689, 651, -102, -357, 930, 255, -651, 1, 1, 1, 1],
  ![1, 418, -2, 418, 110, -38, -2, 1045, 1, 1, 1, 1]]
def pairSquareRoot : Fin 12 → Fin 12 → ℤ := ![![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  ![1, 1, 12, 3, 12, 3, 24, 6, 6, 3, 18, 18],
  ![1, 6, 1, 246, 96, 18, 18, 84, 216, 6, 42, 36],
  ![1, 3, 492, 1, 1116, 24, 651, 18, 186, 54, 93, 126],
  ![1, 6, 96, 558, 1, 1, 1, 1, 744, 18, 186, 180],
  ![1, 3, 36, 24, 1, 1, 1, 1, 18, 6, 15, 18],
  ![1, 24, 36, 651, 1, 1, 1, 1, 2790, 3, 186, 126],
  ![1, 24, 672, 72, 1, 1, 1, 1, 96, 360, 168, 288],
  ![1, 6, 216, 186, 744, 18, 2790, 12, 1, 1, 1, 1],
  ![1, 3, 12, 54, 36, 6, 3, 90, 1, 1, 1, 1],
  ![1, 18, 84, 93, 372, 15, 186, 42, 1, 1, 1, 1],
  ![1, 18, 72, 126, 360, 18, 126, 72, 1, 1, 1, 1]]
def pairResidue : Fin 12 → Fin 12 → ℕ := ![![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  ![1, 1, 109, 75637, 6073, 397, 157, 7921, 25477, 157, 361, 397],
  ![1, 1, 1, 1, 85, 1, 1, 1, 1, 1, 1, 1],
  ![3, 5948887, 607, 3, 2287, 11767, 247, 117787, 4927, 4327, 247, 117787],
  ![1, 279857, 1229, 105, 1, 1, 1, 1, 809, 1601, 1397, 1601],
  ![3, 283, 3, 55, 3, 3, 3, 3, 283, 7, 43, 55],
  ![3, 5683, 103, 379, 3, 3, 3, 3, 3, 5683, 583, 103],
  ![1, 31813, 61, 45, 1, 1, 1, 1, 14257, 13, 61, 2553],
  ![1, 63757, 393, 1057, 1, 2501, 1, 63757, 1, 1, 1, 1],
  ![3, 55, 7, 55, 191, 7, 55, 11, 3, 3, 3, 3],
  ![1, 13561, 1409, 233, 233, 2897, 437, 1409, 1, 1, 1, 1],
  ![1, 585, 1, 585, 57, 129, 1, 2257, 1, 1, 1, 1]]
def pairSign : Fin 12 → Fin 12 → ℤ := ![![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  ![1, 1, 1, -1, 1, -1, 1, 1, -1, -1, 1, 1],
  ![1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1, 1],
  ![1, 1, -1, 1, 1, 1, 1, 1, -1, 1, 1, -1],
  ![1, -1, 1, 1, 1, 1, 1, 1, 1, -1, 1, -1],
  ![1, -1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1],
  ![1, -1, -1, -1, 1, 1, 1, 1, 1, 1, -1, -1],
  ![1, 1, 1, -1, 1, 1, 1, 1, -1, 1, 1, -1],
  ![1, 1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1],
  ![1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  ![1, -1, -1, 1, 1, 1, -1, -1, 1, 1, 1, 1],
  ![1, 1, 1, 1, 1, -1, 1, -1, 1, 1, 1, 1]]

/-- Every required determinant character has an explicit square-part
and CRT residue certificate. -/
theorem pair_certificate (i j : Fin 12) (hij : RelevantPair i j) :
    pairConstant i j = pairSquarePart i j * (pairSquareRoot i j) ^ 2 ∧
    (Rank5.outputs i).a % (4 * (pairSquarePart i j).natAbs : ℕ) = 0 ∧
    (Rank5.outputs i).b % (4 * (pairSquarePart i j).natAbs : ℕ) = 0 ∧
    (Rank5.outputs i).c % (4 * (pairSquarePart i j).natAbs : ℕ) = pairResidue i j ∧
    jacobiSym (pairSquarePart i j) (pairResidue i j) = pairSign i j := by
  fin_cases i <;> fin_cases j <;>
    simp [RelevantPair] at hij
  all_goals norm_num [pairConstant, pairSquarePart, pairSquareRoot,
    pairResidue, pairSign, Rank5.forms, Rank5.cofactors, Rank5.outputs]

theorem prime_int_eq {x y : ℤ} (h : PrimeSpecialization5 x y) (i : Fin 12) :
    (h.primes i : ℤ) = (Rank5.outputs i).eval x y := by
  change (((Rank5.outputs i).eval x y).natAbs : ℤ) = _
  rw [Int.natCast_natAbs, abs_of_pos (h.positive i)]

/-- Actual determinant character at its moving prime. -/
theorem pair_character {x y : ℤ} (h : PrimeSpecialization5 x y)
    (i j : Fin 12) (hij : RelevantPair i j)
    (hu : ((pairConstant i j : ℤ) : ZMod (h.primes i)) ≠ 0) :
    @legendreSym (h.primes i) ⟨h.prime i⟩ (pairConstant i j) = pairSign i j := by
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  have cert := pair_certificate i j hij
  rw [FixedCharacterEvaluation.legendre_via_squarepart (h.primes i)
    (pairConstant i j) (pairSquarePart i j) (pairSquareRoot i j) (pairResidue i j)
    (h.outside i 2 (by simp)) cert.1 hu]
  · exact cert.2.2.2.2
  · apply FixedCharacterEvaluation.nat_residue_of_int_eq _ _ _ _ (prime_int_eq h i)
    rw [AffineForm.eval_mod _ _ _ _ cert.2.1 cert.2.2.1]
    exact cert.2.2.2.1

def baseSquarePart : Fin 12 → ℤ := ![1, -1, -1, 155, 31, -1, -31, 2, 62, -1, 31, -2]
def baseSquareRoot : Fin 12 → ℤ := ![1, 1, 4, 1, 4, 1, 1, 8, 2, 1, 1, 6]
def baseResidue : Fin 12 → ℕ := ![1, 1, 1, 161, 37, 1, 37, 1, 161, 1, 37, 1]
def baseSign : Fin 12 → ℤ := ![1, 1, 1, -1, -1, 1, -1, 1, -1, 1, -1, 1]

theorem base_certificate (j : Fin 12) (hj : j ≠ 0) :
    (Rank5.forms j).b * Rank5.cofactors j = baseSquarePart j * (baseSquareRoot j) ^ 2 ∧
    (Rank5.outputs 0).a % (4 * (baseSquarePart j).natAbs : ℕ) = 0 ∧
    (Rank5.outputs 0).b % (4 * (baseSquarePart j).natAbs : ℕ) = 0 ∧
    (Rank5.outputs 0).c % (4 * (baseSquarePart j).natAbs : ℕ) = baseResidue j ∧
    jacobiSym (baseSquarePart j) (baseResidue j) = baseSign j := by
  fin_cases j <;> simp at hj
  all_goals norm_num [Rank5.forms, Rank5.cofactors, Rank5.outputs,
    baseSquarePart, baseSquareRoot, baseResidue, baseSign]

theorem base_character {x y : ℤ} (h : PrimeSpecialization5 x y)
    (j : Fin 12) (hj : j ≠ 0)
    (hu : (((Rank5.forms j).b * Rank5.cofactors j : ℤ) : ZMod (h.primes 0)) ≠ 0) :
    @legendreSym (h.primes 0) ⟨h.prime 0⟩
      ((Rank5.forms j).b * Rank5.cofactors j) = baseSign j := by
  let : Fact (h.primes 0).Prime := ⟨h.prime 0⟩
  have cert := base_certificate j hj
  rw [FixedCharacterEvaluation.legendre_via_squarepart (h.primes 0)
    ((Rank5.forms j).b * Rank5.cofactors j) (baseSquarePart j) (baseSquareRoot j)
    (baseResidue j) (h.outside 0 2 (by simp)) cert.1 hu]
  · exact cert.2.2.2.2
  · apply FixedCharacterEvaluation.nat_residue_of_int_eq _ _ _ _ (prime_int_eq h 0)
    rw [AffineForm.eval_mod _ _ _ _ cert.2.1 cert.2.2.1]
    exact cert.2.2.2.1

end RankCertificates.Rank5ConstantCharacters
