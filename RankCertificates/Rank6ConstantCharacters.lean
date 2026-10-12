module

public import RankCertificates.FixedCharacterEvaluation
public import RankCertificates.PrimeSpecializations

@[expose] public section

/-! Exact finite constant-character computations for the final rank-6
CRT lattice. The square-part data are checked against the homogeneous
form determinants; no character assumptions are supplied. -/

namespace RankCertificates.Rank6ConstantCharacters

open PrimePatterns

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def RelevantPair (i j : Fin 12) : Prop :=
  i ≠ j ∧ i ≠ 0 ∧ j ≠ 0 ∧
    (i.val < 4 ∨ (i.val < 8 ∧ (j.val < 4 ∨ 8 ≤ j.val)) ∨ (8 ≤ i.val ∧ j.val < 8))

def pairConstant (i j : Fin 12) : ℤ :=
  (PrimePatterns.Rank6.forms i).b * PrimePatterns.Rank6.cofactors j *
    ((PrimePatterns.Rank6.forms i).b * (PrimePatterns.Rank6.forms j).a -
      (PrimePatterns.Rank6.forms j).b * (PrimePatterns.Rank6.forms i).a) * 1

def pairSquarePart : Fin 12 → Fin 12 → ℤ := ![![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  ![1, 1, 1, 2, 2, 7, 2, 1, 2, 21, 3, 2],
  ![1, -30, 1, 5865, 8855, 561, 1870, 1518, -119, -115, 170, 46],
  ![1, 1, 391, 1, -253, 187, -187, 1771, 17, 69, 357, 23],
  ![1, 3, 1771, 759, 1, 1, 1, 1, 7, 253, 1, 253],
  ![1, -35, -374, 1870, 1, 1, 1, 1, -34, -1155, 510, 11],
  ![1, 42, 1309, 7854, 1, 1, 1, 1, 238, 77, 119, 22],
  ![1, -10, -506, 8855, 1, 1, 1, 1, -1, -3795, 210, 506],
  ![1, -15, 119, 255, 35, 51, 85, 3, 1, 1, 1, 1],
  ![1, -7, 46, 46, 506, 77, 11, 506, 1, 1, 1, 1],
  ![1, 2, 34, -119, -1, 17, -34, 14, 1, 1, 1, 1],
  ![1, 210, 161, -4830, -17710, 231, -110, 5313, 1, 1, 1, 1]]

def pairSquareRoot : Fin 12 → Fin 12 → ℤ := ![![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  ![1, 1, 13, 10, 1, 1, 1, 3, 2, 3, 1, 4],
  ![1, 65, 1, 220, 30, 50, 45, 50, 300, 990, 120, 825],
  ![1, 65, 143, 1, 26, 39, 13, 13, 208, 429, 13, 143],
  ![1, 3, 9, 12, 1, 1, 1, 1, 36, 27, 45, 9],
  ![1, 2, 10, 12, 1, 1, 1, 1, 20, 12, 2, 50],
  ![1, 1, 9, 2, 1, 1, 1, 1, 6, 45, 3, 21],
  ![1, 3, 10, 4, 1, 1, 1, 1, 100, 6, 2, 5],
  ![1, 1, 15, 16, 6, 5, 3, 25, 1, 1, 1, 1],
  ![1, 8, 88, 176, 8, 16, 40, 8, 1, 1, 1, 1],
  ![1, 1, 8, 4, 10, 2, 1, 2, 1, 1, 1, 1],
  ![1, 4, 165, 22, 3, 25, 21, 5, 1, 1, 1, 1]]

def pairResidue : Fin 12 → Fin 12 → ℕ := ![![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  ![1, 1, 3, 3, 3, 11, 3, 3, 3, 11, 11, 3],
  ![1, 37, 1, 21457, 18237, 241, 5477, 4069, 37, 297, 37, 21],
  ![1, 3, 1459, 1, 355, 575, 575, 1367, 31, 79, 1255, 79],
  ![1, 5, 2941, 917, 1, 1, 1, 1, 1, 917, 1, 917],
  ![1, 101, 353, 4841, 1, 1, 1, 1, 81, 2201, 761, 1],
  ![1, 143, 5043, 31223, 1, 1, 1, 1, 759, 115, 283, 71],
  ![1, 17, 1073, 13217, 1, 1, 1, 1, 1, 13217, 617, 1073],
  ![1, 11, 23, 431, 51, 23, 91, 11, 1, 1, 1, 1],
  ![1, 3, 47, 47, 1703, 31, 31, 1703, 1, 1, 1, 1],
  ![1, 7, 135, 475, 3, 67, 135, 55, 1, 1, 1, 1],
  ![1, 461, 153, 4661, 69061, 377, 421, 12389, 1, 1, 1, 1]]

def pairSign : Fin 12 → Fin 12 → ℤ := ![![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  ![1, 1, 1, -1, -1, -1, -1, 1, -1, -1, 1, -1],
  ![1, 1, 1, -1, -1, 1, 1, -1, -1, 1, -1, 1],
  ![1, 1, -1, 1, 1, 1, -1, 1, -1, -1, -1, 1],
  ![1, -1, -1, 1, 1, 1, 1, 1, 1, -1, 1, -1],
  ![1, -1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 1],
  ![1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1],
  ![1, -1, 1, -1, 1, 1, 1, 1, 1, 1, 1, 1],
  ![1, -1, 1, -1, -1, -1, -1, 1, 1, 1, 1, 1],
  ![1, -1, -1, -1, 1, -1, -1, 1, 1, 1, 1, 1],
  ![1, 1, 1, -1, -1, 1, -1, 1, 1, 1, 1, 1],
  ![1, -1, 1, 1, -1, 1, -1, -1, 1, 1, 1, 1]]

/-- Every required determinant character has an explicit square-part
and CRT residue certificate. -/
theorem pair_certificate (i j : Fin 12) (hij : RelevantPair i j) :
    pairConstant i j = pairSquarePart i j * (pairSquareRoot i j) ^ 2 ∧
    (PrimePatterns.Rank6.outputs i).a % (4 * (pairSquarePart i j).natAbs : ℕ) = 0 ∧
    (PrimePatterns.Rank6.outputs i).b % (4 * (pairSquarePart i j).natAbs : ℕ) = 0 ∧
    (PrimePatterns.Rank6.outputs i).c % (4 * (pairSquarePart i j).natAbs : ℕ) = pairResidue i j ∧
    jacobiSym (pairSquarePart i j) (pairResidue i j) = pairSign i j := by
  fin_cases i <;> fin_cases j <;>
    simp [RelevantPair] at hij
  all_goals norm_num [pairConstant, pairSquarePart, pairSquareRoot,
    pairResidue, pairSign, PrimePatterns.Rank6.forms, PrimePatterns.Rank6.cofactors, PrimePatterns.Rank6.outputs]

theorem prime_int_eq {x y : ℤ} (h : PrimeSpecialization6 x y) (i : Fin 12) :
    (h.primes i : ℤ) = (PrimePatterns.Rank6.outputs i).eval x y := by
  change (((PrimePatterns.Rank6.outputs i).eval x y).natAbs : ℤ) = _
  rw [Int.natCast_natAbs, abs_of_pos (h.positive i)]

/-- Actual determinant character at its moving prime. -/
theorem pair_character {x y : ℤ} (h : PrimeSpecialization6 x y)
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

def baseSquarePart : Fin 12 → ℤ := ![1, 1, 30, -2, -6, 5, -21, 10, 30, 3, -6, -105]

def baseSquareRoot : Fin 12 → ℤ := ![1, 1, 5, 26, 3, 2, 1, 1, 2, 24, 1, 1]

def baseResidue : Fin 12 → ℕ := ![1, 3, 43, 3, 19, 3, 19, 3, 43, 7, 19, 103]

def baseSign : Fin 12 → ℤ := ![1, 1, -1, 1, -1, -1, 1, 1, -1, -1, -1, -1]

theorem base_certificate (j : Fin 12) (hj : j ≠ 0) :
    (PrimePatterns.Rank6.forms j).b * PrimePatterns.Rank6.cofactors j = baseSquarePart j * (baseSquareRoot j) ^ 2 ∧
    (PrimePatterns.Rank6.outputs 0).a % (4 * (baseSquarePart j).natAbs : ℕ) = 0 ∧
    (PrimePatterns.Rank6.outputs 0).b % (4 * (baseSquarePart j).natAbs : ℕ) = 0 ∧
    (PrimePatterns.Rank6.outputs 0).c % (4 * (baseSquarePart j).natAbs : ℕ) = baseResidue j ∧
    jacobiSym (baseSquarePart j) (baseResidue j) = baseSign j := by
  fin_cases j <;> simp at hj
  all_goals norm_num [PrimePatterns.Rank6.forms, PrimePatterns.Rank6.cofactors, PrimePatterns.Rank6.outputs,
    baseSquarePart, baseSquareRoot, baseResidue, baseSign]

theorem base_character {x y : ℤ} (h : PrimeSpecialization6 x y)
    (j : Fin 12) (hj : j ≠ 0)
    (hu : (((PrimePatterns.Rank6.forms j).b * PrimePatterns.Rank6.cofactors j : ℤ) : ZMod (h.primes 0)) ≠ 0) :
    @legendreSym (h.primes 0) ⟨h.prime 0⟩
      ((PrimePatterns.Rank6.forms j).b * PrimePatterns.Rank6.cofactors j) = baseSign j := by
  let : Fact (h.primes 0).Prime := ⟨h.prime 0⟩
  have cert := base_certificate j hj
  rw [FixedCharacterEvaluation.legendre_via_squarepart (h.primes 0)
    ((PrimePatterns.Rank6.forms j).b * PrimePatterns.Rank6.cofactors j) (baseSquarePart j) (baseSquareRoot j)
    (baseResidue j) (h.outside 0 2 (by simp)) cert.1 hu]
  · exact cert.2.2.2.2
  · apply FixedCharacterEvaluation.nat_residue_of_int_eq _ _ _ _ (prime_int_eq h 0)
    rw [AffineForm.eval_mod _ _ _ _ cert.2.1 cert.2.2.1]
    exact cert.2.2.2.1

end RankCertificates.Rank6ConstantCharacters
