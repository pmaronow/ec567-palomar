module

public import RankCertificates.Rank5ConstantCharacters
public import RankCertificates.Rank5PrimeValuations
public import RankCertificates.MatrixCertificates

@[expose] public section

/-! The genuine normalized-unit characters of the final rank-5
prime columns are evaluated using the concrete CRT lattice and one common
pivot character. This is finite algebraic descent, not prime-pattern existence. -/

namespace RankCertificates.Rank5CharacterEvaluation

open PrimePatterns MovingPrimeCharacters Rank5ConstantCharacters

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {x y : ℤ} (h : PrimeSpecialization5 x y)

def smallColumns : Fin 4 → ℤ := ![-1, 2, 3, 5]
def smallResidue : Fin 12 → Fin 4 → ℕ := ![![1, 1, 1, 1],
  ![1, 5, 1, 9],
  ![1, 5, 1, 1],
  ![3, 7, 7, 7],
  ![1, 5, 5, 1],
  ![3, 3, 7, 3],
  ![3, 3, 7, 3],
  ![1, 5, 1, 13],
  ![1, 1, 1, 1],
  ![3, 7, 7, 11],
  ![1, 1, 5, 17],
  ![1, 1, 5, 17]]
def smallSign : Fin 12 → Fin 4 → ℤ := ![![1, 1, 1, 1],
  ![1, -1, 1, 1],
  ![1, -1, 1, 1],
  ![-1, 1, -1, -1],
  ![1, -1, -1, 1],
  ![-1, -1, -1, -1],
  ![-1, -1, -1, -1],
  ![1, -1, 1, -1],
  ![1, 1, 1, 1],
  ![-1, 1, -1, 1],
  ![1, 1, -1, -1],
  ![1, 1, -1, -1]]

theorem small_certificate (i : Fin 12) (j : Fin 4) :
    (Rank5.outputs i).a % (4 * (smallColumns j).natAbs : ℕ) = 0 ∧
    (Rank5.outputs i).b % (4 * (smallColumns j).natAbs : ℕ) = 0 ∧
    (Rank5.outputs i).c % (4 * (smallColumns j).natAbs : ℕ) = smallResidue i j ∧
    jacobiSym (smallColumns j) (smallResidue i j) = smallSign i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [Rank5.outputs, smallColumns, smallResidue, smallSign]

theorem prime_unit (i : Fin 12) (q : ℕ) (hq : q.Prime) (hne : h.primes i ≠ q) :
    ((q : ℤ) : ZMod (h.primes i)) ≠ 0 := by
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  let : Fact q.Prime := ⟨hq⟩
  exact (legendreSym.eq_zero_iff (h.primes i) _).not.mp
    (legendre_prime_ne_zero (h.primes i) q hne)

theorem small_unit (i : Fin 12) (j : Fin 4) :
    ((smallColumns j : ℤ) : ZMod (h.primes i)) ≠ 0 := by
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  have h2 := prime_unit h i 2 (by norm_num) (h.outside i 2 (by simp))
  have h3 := prime_unit h i 3 (by norm_num) (h.outside i 3 (by simp))
  have h5 := prime_unit h i 5 (by norm_num) (h.outside i 5 (by simp))
  fin_cases j
  · norm_num [smallColumns]
  · simpa [smallColumns] using h2
  · simpa [smallColumns] using h3
  · simpa [smallColumns] using h5

theorem small_character (i : Fin 12) (j : Fin 4) :
    @legendreSym (h.primes i) ⟨h.prime i⟩ (smallColumns j) = smallSign i j := by
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  have cert := small_certificate i j
  rw [FixedCharacterEvaluation.legendre_via_squarepart (h.primes i)
    (smallColumns j) (smallColumns j) 1 (smallResidue i j)
    (h.outside i 2 (by simp)) (by ring) (small_unit h i j)]
  · exact cert.2.2.2
  · apply FixedCharacterEvaluation.nat_residue_of_int_eq _ _ _ _ (prime_int_eq h i)
    rw [AffineForm.eval_mod _ _ _ _ cert.1 cert.2.1]
    exact cert.2.2.1

theorem cofactor_unit (i j : Fin 12) :
    ((Rank5.cofactors j : ℤ) : ZMod (h.primes i)) ≠ 0 := by
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  have h2 := prime_unit h i 2 (by norm_num) (h.outside i 2 (by simp))
  have h3 := prime_unit h i 3 (by norm_num) (h.outside i 3 (by simp))
  norm_num only [Int.cast_natCast, Nat.cast_ofNat] at h2 h3
  rw [Rank5.cofactor_parts]
  push_cast
  exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)

def M (x : ℤ) : ℤ := Rank5.M0 + Rank5.W * x
def N (y : ℤ) : ℤ := Rank5.N0 + Rank5.W * y

theorem normalized_identity (i : Fin 12) :
    Rank5.cofactors i * (h.primes i : ℤ) =
      (Rank5.forms i).a * M x + (Rank5.forms i).b * N y := by
  rw [prime_int_eq h i]
  exact Rank5.normalization i x y

theorem base_identity : 54 * (h.primes 0 : ℤ) = M x := by
  simpa [Rank5.cofactors, Rank5.forms, LinearForm.eval] using normalized_identity h 0

theorem pivot_mod_four : h.primes 0 % 4 = 1 := by
  apply FixedCharacterEvaluation.nat_residue_of_int_eq _ _ _ _ (prime_int_eq h 0)
  rw [AffineForm.eval_mod]
  · norm_num [Rank5.outputs]
  · norm_num [Rank5.outputs]
  · norm_num [Rank5.outputs]

theorem prime_ne (i j : Fin 12) (hij : i ≠ j) : h.primes i ≠ h.primes j :=
  fun he => hij (h.distinct he)

theorem coefficient_unit (i : Fin 12) (hi : i ≠ 0) :
    (((Rank5.forms i).b : ℤ) : ZMod (h.primes i)) ≠ 0 := by
  let : Fact (h.primes 0).Prime := ⟨h.prime 0⟩
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  apply affine_b_unit (h.primes 0) (h.primes i) (M x) (N y) 54
    (Rank5.cofactors i) (Rank5.forms i).a (Rank5.forms i).b
    (base_identity h) (normalized_identity h i) (Rank5.original_forms_primitive i)
  · simpa [Rank5.cofactors] using cofactor_unit h i 0
  · exact prime_ne h i 0 hi

theorem base_coefficient_unit (j : Fin 12) (hj : j ≠ 0) :
    (((Rank5.forms j).b * Rank5.cofactors j : ℤ) : ZMod (h.primes 0)) ≠ 0 := by
  let : Fact (h.primes 0).Prime := ⟨h.prime 0⟩
  let : Fact (h.primes j).Prime := ⟨h.prime j⟩
  exact base_affine_coeff_unit (h.primes 0) (h.primes j) (M x) (N y) 54
    (Rank5.cofactors j) (Rank5.forms j).a (Rank5.forms j).b
    (base_identity h) (normalized_identity h j) (cofactor_unit h 0 j)
    (prime_ne h 0 j hj.symm)

def epsilon : ℤ := @legendreSym (h.primes 0) ⟨h.prime 0⟩ (N y)

theorem base_symbol (j : Fin 12) (hj : j ≠ 0) :
    @legendreSym (h.primes 0) ⟨h.prime 0⟩ (h.primes j : ℤ) = baseSign j * epsilon h := by
  let : Fact (h.primes 0).Prime := ⟨h.prime 0⟩
  rw [base_affine_symbol (h.primes 0) (h.primes j) (M x) (N y) 54
    (Rank5.cofactors j) (Rank5.forms j).a (Rank5.forms j).b
    (base_identity h) (normalized_identity h j) (cofactor_unit h 0 j),
    base_character h j hj (base_coefficient_unit h j hj)]
  rfl

theorem epsilon_dichotomy : epsilon h = 1 ∨ epsilon h = -1 := by
  let : Fact (h.primes 0).Prime := ⟨h.prime 0⟩
  let : Fact (h.primes 1).Prime := ⟨h.prime 1⟩
  have hs := base_symbol h 1 (by decide)
  have hn : epsilon h ≠ 0 := by
    have hu := legendre_prime_ne_zero (h.primes 0) (h.primes 1)
      (prime_ne h 0 1 (by decide))
    rw [hs] at hu
    exact (mul_ne_zero_iff.mp hu).2
  exact legendreSym.eq_one_or_neg_one (h.primes 0)
    ((legendreSym.eq_zero_iff (h.primes 0) (N y)).not.mp hn)

theorem pair_symbol (i j : Fin 12) (hij : RelevantPair i j) :
    @legendreSym (h.primes i) ⟨h.prime i⟩ (h.primes j : ℤ) =
      pairSign i j * baseSign i * epsilon h := by
  let : Fact (h.primes 0).Prime := ⟨h.prime 0⟩
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  let : Fact (h.primes j).Prime := ⟨h.prime j⟩
  have hu : (((Rank5.forms i).b * Rank5.cofactors j : ℤ) : ZMod (h.primes i)) ≠ 0 := by
    push_cast
    exact mul_ne_zero (coefficient_unit h i hij.2.1) (cofactor_unit h i j)
  have hc := affine_pair_constant_unit (h.primes 0) (h.primes i) (h.primes j)
    (M x) (N y) 54 (Rank5.cofactors i) (Rank5.cofactors j)
    (Rank5.forms i).a (Rank5.forms i).b (Rank5.forms j).a (Rank5.forms j).b
    (base_identity h) (normalized_identity h i) (normalized_identity h j) hu
    (prime_ne h i j hij.1)
  rw [affine_pair_symbol_one_mod_four (h.primes 0) (h.primes i) (h.primes j)
    (M x) (N y) 54 (Rank5.cofactors i) (Rank5.cofactors j)
    (Rank5.forms i).a (Rank5.forms i).b (Rank5.forms j).a (Rank5.forms j).b
    (base_identity h) (normalized_identity h i) (normalized_identity h j) hu
    (cofactor_unit h 0 i) (pivot_mod_four h) (h.outside i 2 (by simp))]
  rw [base_character h i hij.2.1 (base_coefficient_unit h i hij.2.1)]
  change legendreSym (h.primes i) (pairConstant i j) * baseSign i * epsilon h = _
  rw [pair_character h i j hij hc]

/-- Required prime-to-prime entries; pairs within H or within J are unused. -/
def RelevantEntry (i j : Fin 12) : Prop :=
  i = j ∨ (i ≠ j ∧ (i = 0 ∨ j = 0 ∨ RelevantPair i j))

def movingSign (e : ℤ) (i j : Fin 12) : ℤ :=
  if i = j then 1 else if i = 0 then baseSign j * e
  else if j = 0 then baseSign i * e else pairSign i j * baseSign i * e

theorem moving_symbol (i j : Fin 12) (hij : i ≠ j) (he : RelevantEntry i j) :
    @legendreSym (h.primes i) ⟨h.prime i⟩ (h.primes j : ℤ) =
      movingSign (epsilon h) i j := by
  let : Fact (h.primes 0).Prime := ⟨h.prime 0⟩
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  by_cases hi : i = 0
  · subst i
    simpa [movingSign, hij, hij.symm] using base_symbol h j hij.symm
  by_cases hj : j = 0
  · subst j
    rw [@legendreSym.quadratic_reciprocity_one_mod_four (h.primes 0) (h.primes i)
      ⟨h.prime 0⟩ ⟨h.prime i⟩ (pivot_mod_four h)
      (h.outside i 2 (by simp)), base_symbol h i hi]
    simp [movingSign, hi]
  have hp : RelevantPair i j := by
    rcases he with he | ⟨_, he | he | he⟩
    · exact False.elim (hij he)
    · exact False.elim (hi he)
    · exact False.elim (hj he)
    · exact he
  simpa [movingSign, hij, hi, hj] using pair_symbol h i j hp

def movingBit (e : ℤ) (i j : Fin 12) : ZMod 2 :=
  if i = j then 0 else quadraticCharacterBit (movingSign e i j)

theorem moving_entry (i j : Fin 12) (he : RelevantEntry i j) :
    @unitCharacterParity (h.primes i) ⟨h.prime i⟩
      (Additive.ofMul (rationalSquareClass (h.primes j : ℚ))) =
      movingBit (epsilon h) i j := by
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  let : Fact (h.primes j).Prime := ⟨h.prime j⟩
  by_cases hij : i = j
  · subst j
    simp only [movingBit, ite_true]
    exact RankCertificates.unitCharacterParity_prime_self (h.primes i)
  · rw [MovingPrimeCharacters.unitCharacterParity_prime_other _ _ (prime_ne h i j hij),
      moving_symbol h i j hij he]
    simp [movingBit, hij]

theorem small_entry (i : Fin 12) (j : Fin 4) :
    @unitCharacterParity (h.primes i) ⟨h.prime i⟩
      (Additive.ofMul (rationalSquareClass (smallColumns j : ℚ))) =
      quadraticCharacterBit (smallSign i j) := by
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  rw [unitCharacterParity_int_of_not_dvd (h.primes i)]
  · rw [small_character h i j]
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).not.mp (small_unit h i j)

end RankCertificates.Rank5CharacterEvaluation
