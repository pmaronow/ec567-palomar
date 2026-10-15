module

public import RankCertificates.Rank7PrimeValuations
public import RankCertificates.FixedCharacterEvaluation

@[expose] public section

/-! Exact moving-prime character evaluation for the final rank-seven lattice.
All characters belong to the actual rational squareclass group. -/

namespace RankCertificates.Rank7CharacterEvaluation

-- Keep the additive structure on `ZMod 2` coherent with its ring structure
-- when valuation parities are used as binary linear functionals.
local instance : AddCommGroup (ZMod 2) := (ZMod.commRing 2).toAddCommGroup

open Integration MovingPrimeCharacters FixedCharacterEvaluation

variable {x y : ℤ} (h : PrimeSpecialization7 x y)

theorem prime_int_eq (i : Fin 12) :
    (h.primes i : ℤ) = (PrimePatterns.Rank7.outputs i).eval x y := by
  change (((PrimePatterns.Rank7.outputs i).eval x y).natAbs : ℤ) = _
  rw [Int.natCast_natAbs, abs_of_pos (h.positive i)]

theorem affine_relation (i : Fin 12) :
    PrimePatterns.Rank7.cofactors i * (h.primes i : ℤ) =
      (PrimePatterns.Rank7.forms i).a * (PrimePatterns.Rank7.M0 + PrimePatterns.Rank7.W * x) +
      (PrimePatterns.Rank7.forms i).b * (PrimePatterns.Rank7.N0 + PrimePatterns.Rank7.W * y) := by
  rw [prime_int_eq h i]
  exact PrimePatterns.Rank7.normalization i x y

theorem small_cast_unit (i : Fin 12) (q : ℕ) (hq : q.Prime)
    (hs : q ∈ [2, 3, 7, 13]) : (q : ZMod (h.primes i)) ≠ 0 := by
  intro hz
  have hd : h.primes i ∣ q := (ZMod.natCast_eq_zero_iff q (h.primes i)).mp hz
  exact h.outside i q hs ((Nat.prime_dvd_prime_iff_eq (h.prime i) hq).mp hd)

theorem cofactor_unit (i j : Fin 12) :
    (PrimePatterns.Rank7.cofactors j : ZMod (h.primes i)) ≠ 0 := by
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  have h2 := small_cast_unit h i 2 (by decide +kernel) (by simp)
  have h3 := small_cast_unit h i 3 (by decide +kernel) (by simp)
  rw [PrimePatterns.Rank7.cofactor_parts]
  push_cast
  exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)

/-- The finite residue and square-part certificate evaluates a literal
integer character at an actual moving prime. -/
theorem fixed_symbol (i : Fin 12) [Fact (h.primes i).Prime]
    (c s d : ℤ) (r : ℕ) (v : ℤ)
    (hc : c = s * d ^ 2) (hu : (c : ZMod (h.primes i)) ≠ 0)
    (ha : (PrimePatterns.Rank7.outputs i).a % (4 * s.natAbs : ℕ) = 0)
    (hb : (PrimePatterns.Rank7.outputs i).b % (4 * s.natAbs : ℕ) = 0)
    (hr : (PrimePatterns.Rank7.outputs i).c % (4 * s.natAbs : ℕ) = r)
    (hv : jacobiSym s r = v) : legendreSym (h.primes i) c = v := by
  rw [legendre_via_squarepart (h.primes i) c s d r (h.outside i 2 (by simp)) hc hu]
  · exact hv
  · apply nat_residue_of_int_eq (h.primes i) (4 * s.natAbs) r
      ((PrimePatterns.Rank7.outputs i).eval x y) (prime_int_eq h i)
    rw [PrimePatterns.AffineForm.eval_mod _ _ _ _ ha hb]
    exact hr

theorem pivot_one_mod_four : h.primes 0 % 4 = 1 := by
  apply nat_residue_of_int_eq (h.primes 0) 4 1
    ((PrimePatterns.Rank7.outputs 0).eval x y) (prime_int_eq h 0)
  rw [PrimePatterns.AffineForm.eval_mod]
  all_goals norm_num [PrimePatterns.Rank7.outputs]

theorem base_constant_unit (i : Fin 12) (hi : i ≠ 0) :
    (((PrimePatterns.Rank7.forms i).b * PrimePatterns.Rank7.cofactors i : ℤ) :
      ZMod (h.primes 0)) ≠ 0 := by
  let : Fact (h.primes 0).Prime := ⟨h.prime 0⟩
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  apply base_affine_coeff_unit (h.primes 0) (h.primes i)
    (PrimePatterns.Rank7.M0 + PrimePatterns.Rank7.W * x)
    (PrimePatterns.Rank7.N0 + PrimePatterns.Rank7.W * y)
    (PrimePatterns.Rank7.cofactors 0) (PrimePatterns.Rank7.cofactors i)
    (PrimePatterns.Rank7.forms i).a (PrimePatterns.Rank7.forms i).b
  · simpa [PrimePatterns.Rank7.forms] using affine_relation h 0
  · exact affine_relation h i
  · exact cofactor_unit h 0 i
  · exact fun he => hi (h.distinct he).symm

theorem affine_b_unit_actual (i : Fin 12) (hi : i ≠ 0) :
    ((PrimePatterns.Rank7.forms i).b : ZMod (h.primes i)) ≠ 0 := by
  let : Fact (h.primes 0).Prime := ⟨h.prime 0⟩
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  apply affine_b_unit (h.primes 0) (h.primes i)
    (PrimePatterns.Rank7.M0 + PrimePatterns.Rank7.W * x)
    (PrimePatterns.Rank7.N0 + PrimePatterns.Rank7.W * y)
    (PrimePatterns.Rank7.cofactors 0) (PrimePatterns.Rank7.cofactors i)
    (PrimePatterns.Rank7.forms i).a (PrimePatterns.Rank7.forms i).b
  · simpa [PrimePatterns.Rank7.forms] using affine_relation h 0
  · exact affine_relation h i
  · exact PrimePatterns.Rank7.original_forms_primitive i
  · exact cofactor_unit h i 0
  · exact fun he => hi (h.distinct he)

def determinantConstant (i k : Fin 12) : ℤ :=
  (PrimePatterns.Rank7.forms i).b * PrimePatterns.Rank7.cofactors k *
    ((PrimePatterns.Rank7.forms i).b * (PrimePatterns.Rank7.forms k).a -
      (PrimePatterns.Rank7.forms k).b * (PrimePatterns.Rank7.forms i).a) *
    PrimePatterns.Rank7.cofactors 0

theorem determinant_constant_unit (i k : Fin 12) (hi : i ≠ 0) (hik : i ≠ k) :
    (determinantConstant i k : ZMod (h.primes i)) ≠ 0 := by
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  let : Fact (h.primes k).Prime := ⟨h.prime k⟩
  apply affine_pair_constant_unit (h.primes 0) (h.primes i) (h.primes k)
    (PrimePatterns.Rank7.M0 + PrimePatterns.Rank7.W * x)
    (PrimePatterns.Rank7.N0 + PrimePatterns.Rank7.W * y)
    (PrimePatterns.Rank7.cofactors 0) (PrimePatterns.Rank7.cofactors i)
    (PrimePatterns.Rank7.cofactors k) (PrimePatterns.Rank7.forms i).a
    (PrimePatterns.Rank7.forms i).b (PrimePatterns.Rank7.forms k).a
    (PrimePatterns.Rank7.forms k).b
  · simpa [PrimePatterns.Rank7.forms] using affine_relation h 0
  · exact affine_relation h i
  · exact affine_relation h k
  · simpa only [Int.cast_mul] using
      mul_ne_zero (affine_b_unit_actual h i hi) (cofactor_unit h i k)
  · exact fun he => hik (h.distinct he)

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def baseSign : Fin 12 → ℤ := ![0, 1, 1, -1, -1, 1, 1, -1, 1, -1, 1, -1]

def determinantSign : Fin 12 → Fin 12 → ℤ := ![
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, -1, 1, 1, 1, 1, 1, -1, 1, -1, -1],
  ![0, -1, 0, -1, 1, 1, 1, 1, 1, 1, -1, 1],
  ![0, 1, 1, 0, -1, 1, 1, -1, -1, -1, 1, 1],
  ![0, 1, -1, 1, 0, 0, 0, 0, -1, 1, -1, 1],
  ![0, 1, 1, -1, 0, 0, 0, 0, -1, -1, 1, -1],
  ![0, 1, 1, -1, 0, 0, 0, 0, -1, -1, 1, -1],
  ![0, 1, -1, 1, 0, 0, 0, 0, -1, 1, -1, 1],
  ![0, 1, 1, -1, -1, -1, -1, -1, 0, 0, 0, 0],
  ![0, -1, -1, -1, 1, 1, 1, 1, 0, 0, 0, 0],
  ![0, -1, -1, -1, 1, 1, 1, 1, 0, 0, 0, 0],
  ![0, -1, -1, -1, -1, 1, 1, -1, 0, 0, 0, 0]]

def UsedPair (i k : Fin 12) : Prop :=
  i ≠ k ∧ ¬(4 ≤ i.val ∧ i.val < 8 ∧ 4 ≤ k.val ∧ k.val < 8) ∧
    ¬(8 ≤ i.val ∧ 8 ≤ k.val)

theorem base_constant_symbol (i : Fin 12) (hi : i ≠ 0) [Fact (h.primes 0).Prime] :
    legendreSym (h.primes 0) ((PrimePatterns.Rank7.forms i).b *
      PrimePatterns.Rank7.cofactors i) = baseSign i := by
  fin_cases i
  · exact (hi rfl).elim
  · have hu : ((1 : ℤ) : ZMod (h.primes 0)) ≠ 0 := by simp
    change legendreSym (h.primes 0) 1 = 1
    exact fixed_symbol h 0 1 1 1 1 1
      (by norm_num) hu
      (by norm_num [PrimePatterns.Rank7.outputs])
      (by norm_num [PrimePatterns.Rank7.outputs])
      (by norm_num [PrimePatterns.Rank7.outputs])
      (by norm_num)
  · have hu : (((-11648) : ℤ) : ZMod (h.primes 0)) ≠ 0 := by
      simpa [PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
        base_constant_unit h 2 (by decide +kernel)
    change legendreSym (h.primes 0) (-11648) = 1
    exact fixed_symbol h 0 (-11648) (-182) 8 1 1
      (by norm_num) hu
      (by norm_num [PrimePatterns.Rank7.outputs])
      (by norm_num [PrimePatterns.Rank7.outputs])
      (by norm_num [PrimePatterns.Rank7.outputs])
      (by norm_num)
  · have hu : ((95013 : ℤ) : ZMod (h.primes 0)) ≠ 0 := by
      simpa [PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
        base_constant_unit h 3 (by decide +kernel)
    change legendreSym (h.primes 0) 95013 = (-1)
    exact fixed_symbol h 0 95013 1173 9 1669 (-1)
      (by norm_num) hu
      (by norm_num [PrimePatterns.Rank7.outputs])
      (by norm_num [PrimePatterns.Rank7.outputs])
      (by norm_num [PrimePatterns.Rank7.outputs])
      (by norm_num)
  · have hu : ((272 : ℤ) : ZMod (h.primes 0)) ≠ 0 := by
      simpa [PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
        base_constant_unit h 4 (by decide +kernel)
    change legendreSym (h.primes 0) 272 = (-1)
    exact fixed_symbol h 0 272 17 4 37 (-1)
      (by norm_num) hu
      (by norm_num [PrimePatterns.Rank7.outputs])
      (by norm_num [PrimePatterns.Rank7.outputs])
      (by norm_num [PrimePatterns.Rank7.outputs])
      (by norm_num)
  · have hu : (((-89424) : ℤ) : ZMod (h.primes 0)) ≠ 0 := by
      simpa [PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
        base_constant_unit h 5 (by decide +kernel)
    change legendreSym (h.primes 0) (-89424) = 1
    exact fixed_symbol h 0 (-89424) (-69) 36 13 1
      (by norm_num) hu
      (by norm_num [PrimePatterns.Rank7.outputs])
      (by norm_num [PrimePatterns.Rank7.outputs])
      (by norm_num [PrimePatterns.Rank7.outputs])
      (by norm_num)
  · have hu : (((-50301) : ℤ) : ZMod (h.primes 0)) ≠ 0 := by
      simpa [PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
        base_constant_unit h 6 (by decide +kernel)
    change legendreSym (h.primes 0) (-50301) = 1
    exact fixed_symbol h 0 (-50301) (-69) 27 13 1
      (by norm_num) hu
      (by norm_num [PrimePatterns.Rank7.outputs])
      (by norm_num [PrimePatterns.Rank7.outputs])
      (by norm_num [PrimePatterns.Rank7.outputs])
      (by norm_num)
  · have hu : ((425 : ℤ) : ZMod (h.primes 0)) ≠ 0 := by
      simpa [PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
        base_constant_unit h 7 (by decide +kernel)
    change legendreSym (h.primes 0) 425 = (-1)
    exact fixed_symbol h 0 425 17 5 37 (-1)
      (by norm_num) hu
      (by norm_num [PrimePatterns.Rank7.outputs])
      (by norm_num [PrimePatterns.Rank7.outputs])
      (by norm_num [PrimePatterns.Rank7.outputs])
      (by norm_num)
  · have hu : ((16128 : ℤ) : ZMod (h.primes 0)) ≠ 0 := by
      simpa [PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
        base_constant_unit h 8 (by decide +kernel)
    change legendreSym (h.primes 0) 16128 = 1
    exact fixed_symbol h 0 16128 7 48 1 1
      (by norm_num) hu
      (by norm_num [PrimePatterns.Rank7.outputs])
      (by norm_num [PrimePatterns.Rank7.outputs])
      (by norm_num [PrimePatterns.Rank7.outputs])
      (by norm_num)
  · have hu : ((85131648 : ℤ) : ZMod (h.primes 0)) ≠ 0 := by
      simpa [PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
        base_constant_unit h 9 (by decide +kernel)
    change legendreSym (h.primes 0) 85131648 = (-1)
    exact fixed_symbol h 0 85131648 16422 72 62665 (-1)
      (by norm_num) hu
      (by norm_num [PrimePatterns.Rank7.outputs])
      (by norm_num [PrimePatterns.Rank7.outputs])
      (by norm_num [PrimePatterns.Rank7.outputs])
      (by norm_num)
  · have hu : (((-2925) : ℤ) : ZMod (h.primes 0)) ≠ 0 := by
      simpa [PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
        base_constant_unit h 10 (by decide +kernel)
    change legendreSym (h.primes 0) (-2925) = 1
    exact fixed_symbol h 0 (-2925) (-13) 15 1 1
      (by norm_num) hu
      (by norm_num [PrimePatterns.Rank7.outputs])
      (by norm_num [PrimePatterns.Rank7.outputs])
      (by norm_num [PrimePatterns.Rank7.outputs])
      (by norm_num)
  · have hu : (((-411723) : ℤ) : ZMod (h.primes 0)) ≠ 0 := by
      simpa [PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
        base_constant_unit h 11 (by decide +kernel)
    change legendreSym (h.primes 0) (-411723) = (-1)
    exact fixed_symbol h 0 (-411723) (-5083) 9 105 (-1)
      (by norm_num) hu
      (by norm_num [PrimePatterns.Rank7.outputs])
      (by norm_num [PrimePatterns.Rank7.outputs])
      (by norm_num [PrimePatterns.Rank7.outputs])
      (by norm_num)

theorem determinant_symbol (i k : Fin 12) (hi : i ≠ 0) (hk : k ≠ 0)
    (hik : UsedPair i k) [Fact (h.primes i).Prime] :
    legendreSym (h.primes i) (determinantConstant i k) = determinantSign i k := by
  fin_cases i
  · exact (hi rfl).elim
  · let : Fact (h.primes 1).Prime := ⟨h.prime 1⟩
    fin_cases k
    · exact (hk rfl).elim
    · norm_num [UsedPair] at hik
    · have hu : ((1152 : ℤ) : ZMod (h.primes 1)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 1 2 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 1) 1152 = (-1)
      exact fixed_symbol h 1 1152 2 24 3 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((29484 : ℤ) : ZMod (h.primes 1)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 1 3 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 1) 29484 = 1
      exact fixed_symbol h 1 29484 91 18 11 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((1296 : ℤ) : ZMod (h.primes 1)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 1 4 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 1) 1296 = 1
      exact fixed_symbol h 1 1296 1 36 3 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((8100 : ℤ) : ZMod (h.primes 1)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 1 5 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 1) 8100 = 1
      exact fixed_symbol h 1 8100 1 90 3 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((324 : ℤ) : ZMod (h.primes 1)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 1 6 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 1) 324 = 1
      exact fixed_symbol h 1 324 1 18 3 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((144 : ℤ) : ZMod (h.primes 1)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 1 7 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 1) 144 = 1
      exact fixed_symbol h 1 144 1 12 3 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((1404 : ℤ) : ZMod (h.primes 1)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 1 8 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 1) 1404 = (-1)
      exact fixed_symbol h 1 1404 39 6 11 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((10108800 : ℤ) : ZMod (h.primes 1)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 1 9 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 1) 10108800 = 1
      exact fixed_symbol h 1 10108800 78 360 11 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((756 : ℤ) : ZMod (h.primes 1)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 1 10 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 1) 756 = (-1)
      exact fixed_symbol h 1 756 21 6 11 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((145152 : ℤ) : ZMod (h.primes 1)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 1 11 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 1) 145152 = (-1)
      exact fixed_symbol h 1 145152 7 144 11 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
  · let : Fact (h.primes 2).Prime := ⟨h.prime 2⟩
    fin_cases k
    · exact (hk rfl).elim
    · have hu : ((3276 : ℤ) : ZMod (h.primes 2)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 2 1 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 2) 3276 = (-1)
      exact fixed_symbol h 2 3276 91 6 333 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · norm_num [UsedPair] at hik
    · have hu : ((1287890604 : ℤ) : ZMod (h.primes 2)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 2 3 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 2) 1287890604 = (-1)
      exact fixed_symbol h 2 1287890604 91 3762 333 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((43819776 : ℤ) : ZMod (h.primes 2)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 2 4 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 2) 43819776 = 1
      exact fixed_symbol h 2 43819776 19019 48 38917 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : (((-24648624) : ℤ) : ZMod (h.primes 2)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 2 5 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 2) (-24648624) = 1
      exact fixed_symbol h 2 (-24648624) (-19019) 36 38917 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : (((-154053900) : ℤ) : ZMod (h.primes 2)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 2 6 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 2) (-154053900) = 1
      exact fixed_symbol h 2 (-154053900) (-19019) 90 38917 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((6162156 : ℤ) : ZMod (h.primes 2)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 2 7 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 2) 6162156 = 1
      exact fixed_symbol h 2 6162156 19019 18 38917 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((99341424 : ℤ) : ZMod (h.primes 2)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 2 8 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 2) 99341424 = 1
      exact fixed_symbol h 2 99341424 39 1596 125 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((613735170048 : ℤ) : ZMod (h.primes 2)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 2 9 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 2) 613735170048 = 1
      exact fixed_symbol h 2 613735170048 78 88704 281 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((15459444 : ℤ) : ZMod (h.primes 2)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 2 10 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 2) 15459444 = (-1)
      exact fixed_symbol h 2 15459444 21 858 53 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((3459210300 : ℤ) : ZMod (h.primes 2)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 2 11 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 2) 3459210300 = 1
      exact fixed_symbol h 2 3459210300 7 22230 25 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
  · let : Fact (h.primes 3).Prime := ⟨h.prime 3⟩
    fin_cases k
    · exact (hk rfl).elim
    · have hu : (((-34584732) : ℤ) : ZMod (h.primes 3)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 3 1 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 3) (-34584732) = 1
      exact fixed_symbol h 3 (-34584732) (-106743) 18 193447 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((531233645184 : ℤ) : ZMod (h.primes 3)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 3 2 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 3) 531233645184 = 1
      exact fixed_symbol h 3 531233645184 2346 15048 1075 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · norm_num [UsedPair] at hik
    · have hu : ((135032475600 : ℤ) : ZMod (h.primes 3)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 3 4 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 3) 135032475600 = (-1)
      exact fixed_symbol h 3 135032475600 14421 3060 36679 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((3995452091268 : ℤ) : ZMod (h.primes 3)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 3 5 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 3) 3995452091268 = 1
      exact fixed_symbol h 3 3995452091268 3553 33534 6583 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((1775756485008 : ℤ) : ZMod (h.primes 3)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 3 6 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 3) 1775756485008 = 1
      exact fixed_symbol h 3 1775756485008 3553 22356 6583 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((1350324756 : ℤ) : ZMod (h.primes 3)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 3 7 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 3) 1350324756 = (-1)
      exact fixed_symbol h 3 1350324756 14421 306 36679 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : (((-401306408100) : ℤ) : ZMod (h.primes 3)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 3 8 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 3) (-401306408100) = (-1)
      exact fixed_symbol h 3 (-401306408100) (-15249) 5130 10459 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : (((-1817626953707136) : ℤ) : ZMod (h.primes 3)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 3 9 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 3) (-1817626953707136) = (-1)
      exact fixed_symbol h 3 (-1817626953707136) (-26) 8361144 59 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((185416729344 : ℤ) : ZMod (h.primes 3)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 3 10 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 3) 185416729344 = 1
      exact fixed_symbol h 3 185416729344 8211 4752 29227 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((30416556156084 : ℤ) : ZMod (h.primes 3)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 3 11 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 3) 30416556156084 = 1
      exact fixed_symbol h 3 30416556156084 21 1203498 79 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
  · let : Fact (h.primes 4).Prime := ⟨h.prime 4⟩
    fin_cases k
    · exact (hk rfl).elim
    · have hu : (((-5508) : ℤ) : ZMod (h.primes 4)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 4 1 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 4) (-5508) = 1
      exact fixed_symbol h 4 (-5508) (-17) 18 31 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((65488896 : ℤ) : ZMod (h.primes 4)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 4 2 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 4) 65488896 = (-1)
      exact fixed_symbol h 4 65488896 7106 96 17099 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : (((-489248100) : ℤ) : ZMod (h.primes 4)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 4 3 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 4) (-489248100) = 1
      exact fixed_symbol h 4 (-489248100) (-209) 1530 379 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · norm_num [UsedPair] at hik
    · norm_num [UsedPair] at hik
    · norm_num [UsedPair] at hik
    · norm_num [UsedPair] at hik
    · have hu : (((-87210000) : ℤ) : ZMod (h.primes 4)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 4 8 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 4) (-87210000) = (-1)
      exact fixed_symbol h 4 (-87210000) (-969) 300 2887 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : (((-457219344384) : ℤ) : ZMod (h.primes 4)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 4 9 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 4) (-457219344384) = 1
      exact fixed_symbol h 4 (-457219344384) (-66) 83232 115 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((16984836 : ℤ) : ZMod (h.primes 4)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 4 10 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 4) 16984836 = (-1)
      exact fixed_symbol h 4 16984836 561 174 643 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((2435565996 : ℤ) : ZMod (h.primes 4)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 4 11 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 4) 2435565996 = 1
      exact fixed_symbol h 4 2435565996 19 11322 75 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
  · let : Fact (h.primes 5).Prime := ⟨h.prime 5⟩
    fin_cases k
    · exact (hk rfl).elim
    · have hu : ((2235600 : ℤ) : ZMod (h.primes 5)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 5 1 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 5) 2235600 = 1
      exact fixed_symbol h 5 2235600 69 180 49 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((2392270848 : ℤ) : ZMod (h.primes 5)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 5 2 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 5) 2392270848 = 1
      exact fixed_symbol h 5 2392270848 28842 288 30133 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((940106374416 : ℤ) : ZMod (h.primes 5)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 5 3 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 5) 940106374416 = (-1)
      exact fixed_symbol h 5 940106374416 209 67068 37 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · norm_num [UsedPair] at hik
    · norm_num [UsedPair] at hik
    · norm_num [UsedPair] at hik
    · norm_num [UsedPair] at hik
    · have hu : ((70707914496 : ℤ) : ZMod (h.primes 5)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 5 8 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 5) 70707914496 = (-1)
      exact fixed_symbol h 5 70707914496 1311 7344 3913 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((439815847680000 : ℤ) : ZMod (h.primes 5)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 5 9 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 5) 439815847680000 = (-1)
      exact fixed_symbol h 5 439815847680000 22 4471200 37 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((12119724144 : ℤ) : ZMod (h.primes 5)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 5 10 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 5) 12119724144 = 1
      exact fixed_symbol h 5 12119724144 759 3996 2809 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((2662052056848 : ℤ) : ZMod (h.primes 5)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 5 11 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 5) 2662052056848 = (-1)
      exact fixed_symbol h 5 2662052056848 57 216108 37 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
  · let : Fact (h.primes 6).Prime := ⟨h.prime 6⟩
    fin_cases k
    · exact (hk rfl).elim
    · have hu : ((201204 : ℤ) : ZMod (h.primes 6)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 6 1 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 6) 201204 = 1
      exact fixed_symbol h 6 201204 69 54 121 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((33641308800 : ℤ) : ZMod (h.primes 6)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 6 2 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 6) 33641308800 = 1
      exact fixed_symbol h 6 33641308800 28842 1080 81541 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((940106374416 : ℤ) : ZMod (h.primes 6)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 6 3 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 6) 940106374416 = (-1)
      exact fixed_symbol h 6 940106374416 209 67068 449 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · norm_num [UsedPair] at hik
    · norm_num [UsedPair] at hik
    · norm_num [UsedPair] at hik
    · norm_num [UsedPair] at hik
    · have hu : ((47101655196 : ℤ) : ZMod (h.primes 6)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 6 8 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 6) 47101655196 = (-1)
      exact fixed_symbol h 6 47101655196 1311 5994 2881 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((332896615108992 : ℤ) : ZMod (h.primes 6)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 6 9 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 6) 332896615108992 = (-1)
      exact fixed_symbol h 6 332896615108992 22 3889944 53 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((23026590576 : ℤ) : ZMod (h.primes 6)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 6 10 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 6) 23026590576 = 1
      exact fixed_symbol h 6 23026590576 759 5508 2605 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((4451261242500 : ℤ) : ZMod (h.primes 6)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 6 11 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 6) 4451261242500 = (-1)
      exact fixed_symbol h 6 4451261242500 57 279450 145 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
  · let : Fact (h.primes 7).Prime := ⟨h.prime 7⟩
    fin_cases k
    · exact (hk rfl).elim
    · have hu : (((-61200) : ℤ) : ZMod (h.primes 7)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 7 1 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 7) (-61200) = 1
      exact fixed_symbol h 7 (-61200) (-17) 60 7 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((920937600 : ℤ) : ZMod (h.primes 7)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 7 2 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 7) 920937600 = (-1)
      exact fixed_symbol h 7 920937600 7106 360 5923 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : (((-489248100) : ℤ) : ZMod (h.primes 7)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 7 3 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 7) (-489248100) = 1
      exact fixed_symbol h 7 (-489248100) (-209) 1530 71 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · norm_num [UsedPair] at hik
    · norm_num [UsedPair] at hik
    · norm_num [UsedPair] at hik
    · norm_num [UsedPair] at hik
    · have hu : (((-733436100) : ℤ) : ZMod (h.primes 7)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 7 8 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 7) (-733436100) = (-1)
      exact fixed_symbol h 7 (-733436100) (-969) 870 2047 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : (((-3384154857600) : ℤ) : ZMod (h.primes 7)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 7 9 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 7) (-3384154857600) = 1
      exact fixed_symbol h 7 (-3384154857600) (-66) 226440 115 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((315562500 : ℤ) : ZMod (h.primes 7)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 7 10 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 7) 315562500 = (-1)
      exact fixed_symbol h 7 315562500 561 750 1435 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((51415527600 : ℤ) : ZMod (h.primes 7)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 7 11 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 7) 51415527600 = 1
      exact fixed_symbol h 7 51415527600 19 52020 71 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
  · let : Fact (h.primes 8).Prime := ⟨h.prime 8⟩
    fin_cases k
    · exact (hk rfl).elim
    · have hu : (((-628992) : ℤ) : ZMod (h.primes 8)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 8 1 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 8) (-628992) = 1
      exact fixed_symbol h 8 (-628992) (-273) 48 599 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((15650095104 : ℤ) : ZMod (h.primes 8)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 8 2 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 8) 15650095104 = 1
      exact fixed_symbol h 8 15650095104 6 51072 23 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((153269625600 : ℤ) : ZMod (h.primes 8)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 8 3 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 8) 153269625600 = (-1)
      exact fixed_symbol h 8 153269625600 91 41040 235 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((9192960000 : ℤ) : ZMod (h.primes 8)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 8 4 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 8) 9192960000 = (-1)
      exact fixed_symbol h 8 9192960000 399 4800 1523 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((114772267008 : ℤ) : ZMod (h.primes 8)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 8 5 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 8) 114772267008 = (-1)
      exact fixed_symbol h 8 114772267008 133 29376 459 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((33979938048 : ℤ) : ZMod (h.primes 8)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 8 6 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 8) 33979938048 = (-1)
      exact fixed_symbol h 8 33979938048 133 15984 459 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((773127936 : ℤ) : ZMod (h.primes 8)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 8 7 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 8) 773127936 = (-1)
      exact fixed_symbol h 8 773127936 399 1392 1523 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · norm_num [UsedPair] at hik
    · norm_num [UsedPair] at hik
    · norm_num [UsedPair] at hik
    · norm_num [UsedPair] at hik
  · let : Fact (h.primes 9).Prime := ⟨h.prime 9⟩
    fin_cases k
    · exact (hk rfl).elim
    · have hu : (((-288206100) : ℤ) : ZMod (h.primes 9)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 9 1 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 9) (-288206100) = (-1)
      exact fixed_symbol h 9 (-288206100) (-35581) 90 114613 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((6153088499712 : ℤ) : ZMod (h.primes 9)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 9 2 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 9) 6153088499712 = (-1)
      exact fixed_symbol h 9 6153088499712 782 88704 2005 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((44178432902604 : ℤ) : ZMod (h.primes 9)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 9 3 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 9) 44178432902604 = (-1)
      exact fixed_symbol h 9 44178432902604 91 696762 317 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((3067179768576 : ℤ) : ZMod (h.primes 9)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 9 4 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 9) 3067179768576 = 1
      exact fixed_symbol h 9 3067179768576 1771 41616 4489 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((45432366210000 : ℤ) : ZMod (h.primes 9)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 9 5 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 9) 45432366210000 = 1
      exact fixed_symbol h 9 45432366210000 1309 186300 4181 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((15283447993044 : ℤ) : ZMod (h.primes 9)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 9 6 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 9) 15283447993044 = 1
      exact fixed_symbol h 9 15283447993044 1309 108054 4181 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((227020388364 : ℤ) : ZMod (h.primes 9)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 9 7 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 9) 227020388364 = 1
      exact fixed_symbol h 9 227020388364 1771 11322 4489 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · norm_num [UsedPair] at hik
    · norm_num [UsedPair] at hik
    · norm_num [UsedPair] at hik
    · norm_num [UsedPair] at hik
  · let : Fact (h.primes 10).Prime := ⟨h.prime 10⟩
    fin_cases k
    · exact (hk rfl).elim
    · have hu : ((245700 : ℤ) : ZMod (h.primes 10)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 10 1 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 10) 245700 = (-1)
      exact fixed_symbol h 10 245700 273 30 877 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : (((-1766793600) : ℤ) : ZMod (h.primes 10)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 10 2 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 10) (-1766793600) = (-1)
      exact fixed_symbol h 10 (-1766793600) (-6) 17160 13 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((51372921600 : ℤ) : ZMod (h.primes 10)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 10 3 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 10) 51372921600 = (-1)
      exact fixed_symbol h 10 51372921600 91 23760 149 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((1298840400 : ℤ) : ZMod (h.primes 10)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 10 4 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 10) 1298840400 = 1
      exact fixed_symbol h 10 1298840400 429 1740 409 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : (((-14271414300) : ℤ) : ZMod (h.primes 10)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 10 5 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 10) (-14271414300) = 1
      exact fixed_symbol h 10 (-14271414300) (-143) 9990 409 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : (((-12050953200) : ℤ) : ZMod (h.primes 10)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 10 6 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 10) (-12050953200) = 1
      exact fixed_symbol h 10 (-12050953200) (-143) 9180 409 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((241312500 : ℤ) : ZMod (h.primes 10)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 10 7 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 10) 241312500 = 1
      exact fixed_symbol h 10 241312500 429 750 409 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · norm_num [UsedPair] at hik
    · norm_num [UsedPair] at hik
    · norm_num [UsedPair] at hik
    · norm_num [UsedPair] at hik
  · let : Fact (h.primes 11).Prime := ⟨h.prime 11⟩
    fin_cases k
    · exact (hk rfl).elim
    · have hu : ((737807616 : ℤ) : ZMod (h.primes 11)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 11 1 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 11) 737807616 = (-1)
      exact fixed_symbol h 11 737807616 35581 144 132247 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : (((-6183091324800) : ℤ) : ZMod (h.primes 11)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 11 2 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 11) (-6183091324800) = (-1)
      exact fixed_symbol h 11 (-6183091324800) (-782) 88920 871 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((131805076676364 : ℤ) : ZMod (h.primes 11)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 11 3 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 11) 131805076676364 = (-1)
      exact fixed_symbol h 11 131805076676364 91 1203498 115 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((2912936931216 : ℤ) : ZMod (h.primes 11)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 11 4 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 11) 2912936931216 = (-1)
      exact fixed_symbol h 11 2912936931216 5681 22644 5471 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : (((-49026125380284) : ℤ) : ZMod (h.primes 11)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 11 5 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 11) (-49026125380284) = 1
      exact fixed_symbol h 11 (-49026125380284) (-4199) 108054 531 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : (((-36434397577500) : ℤ) : ZMod (h.primes 11)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 11 6 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 11) (-36434397577500) = 1
      exact fixed_symbol h 11 (-36434397577500) (-4199) 93150 531 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((614929710096 : ℤ) : ZMod (h.primes 11)) ≠ 0 := by
        simpa [determinantConstant, PrimePatterns.Rank7.forms, PrimePatterns.Rank7.cofactors] using
          determinant_constant_unit h 11 7 (by decide +kernel) (by decide +kernel)
      change legendreSym (h.primes 11) 614929710096 = (-1)
      exact fixed_symbol h 11 614929710096 5681 10404 5471 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · norm_num [UsedPair] at hik
    · norm_num [UsedPair] at hik
    · norm_num [UsedPair] at hik
    · norm_num [UsedPair] at hik

noncomputable def epsilon : ℤ :=
  letI : Fact (h.primes 0).Prime := ⟨h.prime 0⟩
  legendreSym (h.primes 0) (PrimePatterns.Rank7.N0 + PrimePatterns.Rank7.W * y)

def crossSign (i k : Fin 12) : ℤ :=
  if i = 0 then baseSign k else if k = 0 then baseSign i else
    determinantSign i k * baseSign i

theorem base_symbol (k : Fin 12) (hk : k ≠ 0) [Fact (h.primes 0).Prime] :
    legendreSym (h.primes 0) (h.primes k : ℤ) = baseSign k * epsilon h := by
  rw [base_affine_symbol (h.primes 0) (h.primes k)
    (PrimePatterns.Rank7.M0 + PrimePatterns.Rank7.W * x)
    (PrimePatterns.Rank7.N0 + PrimePatterns.Rank7.W * y)
    (PrimePatterns.Rank7.cofactors 0) (PrimePatterns.Rank7.cofactors k)
    (PrimePatterns.Rank7.forms k).a (PrimePatterns.Rank7.forms k).b
    (by simpa [PrimePatterns.Rank7.forms] using affine_relation h 0)
    (affine_relation h k) (cofactor_unit h 0 k), base_constant_symbol h k hk]
  rfl

/- Every moving-prime pair needed by the two actual descent matrices
has exactly the archived common-character dependence. -/
set_option backward.isDefEq.respectTransparency false in
theorem cross_symbol (i k : Fin 12) (hik : UsedPair i k)
    [Fact (h.primes i).Prime] :
    legendreSym (h.primes i) (h.primes k : ℤ) = crossSign i k * epsilon h := by
  let : Fact (h.primes 0).Prime := ⟨h.prime 0⟩
  by_cases hi : i = 0
  · subst i
    let : Fact (h.primes 0).Prime := ⟨h.prime 0⟩
    have hk : k ≠ 0 := fun hk => hik.1 hk.symm
    simpa only [crossSign, ite_eq_left, ↓reduceIte] using base_symbol h k hk
  by_cases hk : k = 0
  · subst k
    have hr := legendreSym.quadratic_reciprocity_one_mod_four
      (p := h.primes 0) (q := h.primes i) (pivot_one_mod_four h)
      (h.outside i 2 (by simp))
    rw [hr, base_symbol h i hi]
    simp only [crossSign, ite_eq_right hi, ↓reduceIte]
  · rw [affine_pair_symbol_one_mod_four (h.primes 0) (h.primes i) (h.primes k)
      (PrimePatterns.Rank7.M0 + PrimePatterns.Rank7.W * x)
      (PrimePatterns.Rank7.N0 + PrimePatterns.Rank7.W * y)
      (PrimePatterns.Rank7.cofactors 0) (PrimePatterns.Rank7.cofactors i)
      (PrimePatterns.Rank7.cofactors k) (PrimePatterns.Rank7.forms i).a
      (PrimePatterns.Rank7.forms i).b (PrimePatterns.Rank7.forms k).a
      (PrimePatterns.Rank7.forms k).b
      (by simpa [PrimePatterns.Rank7.forms] using affine_relation h 0)
      (affine_relation h i) (affine_relation h k)
      (by simpa only [Int.cast_mul] using
        mul_ne_zero (affine_b_unit_actual h i hi) (cofactor_unit h i k))
      (cofactor_unit h 0 i) (pivot_one_mod_four h) (h.outside i 2 (by simp))]
    change legendreSym (h.primes i) (determinantConstant i k) *
      legendreSym (h.primes 0)
        ((PrimePatterns.Rank7.forms i).b * PrimePatterns.Rank7.cofactors i) *
      epsilon h = _
    rw [determinant_symbol h i k hi hk hik, base_constant_symbol h i hi]
    simp only [crossSign, ite_eq_right hi, ite_eq_right hk]

set_option backward.isDefEq.respectTransparency false in
theorem epsilon_dichotomy : epsilon h = 1 ∨ epsilon h = -1 := by
  let : Fact (h.primes 0).Prime := ⟨h.prime 0⟩
  let : Fact (h.primes 1).Prime := ⟨h.prime 1⟩
  have hs := base_symbol h 1 (by decide +kernel)
  have he : legendreSym (h.primes 0) (h.primes 1 : ℤ) = epsilon h := by
    simpa [baseSign] using hs
  rw [← he]
  exact legendreSym.eq_one_or_neg_one (h.primes 0)
    (by simpa only [Int.cast_natCast] using
      (ZMod.prime_ne_zero (h.primes 0) (h.primes 1)
        (fun heq => (by decide : (0 : Fin 12) ≠ 1) (h.distinct heq))))

def constantColumns : Fin 5 → ℤ := ![-1, 2, 3, 7, 13]

def constantSign : Fin 12 → Fin 5 → ℤ := ![
  ![1, 1, 1, 1, 1],
  ![-1, -1, 1, -1, -1],
  ![1, 1, -1, 1, -1],
  ![-1, -1, -1, -1, -1],
  ![-1, -1, -1, -1, -1],
  ![1, -1, 1, -1, -1],
  ![1, -1, 1, -1, -1],
  ![-1, -1, -1, 1, 1],
  ![-1, 1, 1, -1, 1],
  ![1, -1, -1, 1, -1],
  ![1, -1, 1, 1, -1],
  ![-1, 1, 1, 1, -1]]

theorem constant_symbol (i : Fin 12) (j : Fin 5) [Fact (h.primes i).Prime] :
    legendreSym (h.primes i) (constantColumns j) = constantSign i j := by
  fin_cases i
  · let : Fact (h.primes 0).Prime := ⟨h.prime 0⟩
    fin_cases j
    · have hu : (((-1) : ℤ) : ZMod (h.primes 0)) ≠ 0 := by
        simp
      change legendreSym (h.primes 0) (-1) = 1
      exact fixed_symbol h 0 (-1) (-1) 1 1 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((2 : ℤ) : ZMod (h.primes 0)) ≠ 0 := by
        simpa using small_cast_unit h 0 2 (by decide +kernel) (by simp)
      change legendreSym (h.primes 0) 2 = 1
      exact fixed_symbol h 0 2 2 1 1 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((3 : ℤ) : ZMod (h.primes 0)) ≠ 0 := by
        simpa using small_cast_unit h 0 3 (by decide +kernel) (by simp)
      change legendreSym (h.primes 0) 3 = 1
      exact fixed_symbol h 0 3 3 1 1 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((7 : ℤ) : ZMod (h.primes 0)) ≠ 0 := by
        simpa using small_cast_unit h 0 7 (by decide +kernel) (by simp)
      change legendreSym (h.primes 0) 7 = 1
      exact fixed_symbol h 0 7 7 1 1 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((13 : ℤ) : ZMod (h.primes 0)) ≠ 0 := by
        simpa using small_cast_unit h 0 13 (by decide +kernel) (by simp)
      change legendreSym (h.primes 0) 13 = 1
      exact fixed_symbol h 0 13 13 1 1 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
  · let : Fact (h.primes 1).Prime := ⟨h.prime 1⟩
    fin_cases j
    · have hu : (((-1) : ℤ) : ZMod (h.primes 1)) ≠ 0 := by
        simp
      change legendreSym (h.primes 1) (-1) = (-1)
      exact fixed_symbol h 1 (-1) (-1) 1 3 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((2 : ℤ) : ZMod (h.primes 1)) ≠ 0 := by
        simpa using small_cast_unit h 1 2 (by decide +kernel) (by simp)
      change legendreSym (h.primes 1) 2 = (-1)
      exact fixed_symbol h 1 2 2 1 3 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((3 : ℤ) : ZMod (h.primes 1)) ≠ 0 := by
        simpa using small_cast_unit h 1 3 (by decide +kernel) (by simp)
      change legendreSym (h.primes 1) 3 = 1
      exact fixed_symbol h 1 3 3 1 11 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((7 : ℤ) : ZMod (h.primes 1)) ≠ 0 := by
        simpa using small_cast_unit h 1 7 (by decide +kernel) (by simp)
      change legendreSym (h.primes 1) 7 = (-1)
      exact fixed_symbol h 1 7 7 1 11 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((13 : ℤ) : ZMod (h.primes 1)) ≠ 0 := by
        simpa using small_cast_unit h 1 13 (by decide +kernel) (by simp)
      change legendreSym (h.primes 1) 13 = (-1)
      exact fixed_symbol h 1 13 13 1 11 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
  · let : Fact (h.primes 2).Prime := ⟨h.prime 2⟩
    fin_cases j
    · have hu : (((-1) : ℤ) : ZMod (h.primes 2)) ≠ 0 := by
        simp
      change legendreSym (h.primes 2) (-1) = 1
      exact fixed_symbol h 2 (-1) (-1) 1 1 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((2 : ℤ) : ZMod (h.primes 2)) ≠ 0 := by
        simpa using small_cast_unit h 2 2 (by decide +kernel) (by simp)
      change legendreSym (h.primes 2) 2 = 1
      exact fixed_symbol h 2 2 2 1 1 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((3 : ℤ) : ZMod (h.primes 2)) ≠ 0 := by
        simpa using small_cast_unit h 2 3 (by decide +kernel) (by simp)
      change legendreSym (h.primes 2) 3 = (-1)
      exact fixed_symbol h 2 3 3 1 5 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((7 : ℤ) : ZMod (h.primes 2)) ≠ 0 := by
        simpa using small_cast_unit h 2 7 (by decide +kernel) (by simp)
      change legendreSym (h.primes 2) 7 = 1
      exact fixed_symbol h 2 7 7 1 25 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((13 : ℤ) : ZMod (h.primes 2)) ≠ 0 := by
        simpa using small_cast_unit h 2 13 (by decide +kernel) (by simp)
      change legendreSym (h.primes 2) 13 = (-1)
      exact fixed_symbol h 2 13 13 1 21 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
  · let : Fact (h.primes 3).Prime := ⟨h.prime 3⟩
    fin_cases j
    · have hu : (((-1) : ℤ) : ZMod (h.primes 3)) ≠ 0 := by
        simp
      change legendreSym (h.primes 3) (-1) = (-1)
      exact fixed_symbol h 3 (-1) (-1) 1 3 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((2 : ℤ) : ZMod (h.primes 3)) ≠ 0 := by
        simpa using small_cast_unit h 3 2 (by decide +kernel) (by simp)
      change legendreSym (h.primes 3) 2 = (-1)
      exact fixed_symbol h 3 2 2 1 3 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((3 : ℤ) : ZMod (h.primes 3)) ≠ 0 := by
        simpa using small_cast_unit h 3 3 (by decide +kernel) (by simp)
      change legendreSym (h.primes 3) 3 = (-1)
      exact fixed_symbol h 3 3 3 1 7 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((7 : ℤ) : ZMod (h.primes 3)) ≠ 0 := by
        simpa using small_cast_unit h 3 7 (by decide +kernel) (by simp)
      change legendreSym (h.primes 3) 7 = (-1)
      exact fixed_symbol h 3 7 7 1 23 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((13 : ℤ) : ZMod (h.primes 3)) ≠ 0 := by
        simpa using small_cast_unit h 3 13 (by decide +kernel) (by simp)
      change legendreSym (h.primes 3) 13 = (-1)
      exact fixed_symbol h 3 13 13 1 7 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
  · let : Fact (h.primes 4).Prime := ⟨h.prime 4⟩
    fin_cases j
    · have hu : (((-1) : ℤ) : ZMod (h.primes 4)) ≠ 0 := by
        simp
      change legendreSym (h.primes 4) (-1) = (-1)
      exact fixed_symbol h 4 (-1) (-1) 1 3 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((2 : ℤ) : ZMod (h.primes 4)) ≠ 0 := by
        simpa using small_cast_unit h 4 2 (by decide +kernel) (by simp)
      change legendreSym (h.primes 4) 2 = (-1)
      exact fixed_symbol h 4 2 2 1 3 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((3 : ℤ) : ZMod (h.primes 4)) ≠ 0 := by
        simpa using small_cast_unit h 4 3 (by decide +kernel) (by simp)
      change legendreSym (h.primes 4) 3 = (-1)
      exact fixed_symbol h 4 3 3 1 7 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((7 : ℤ) : ZMod (h.primes 4)) ≠ 0 := by
        simpa using small_cast_unit h 4 7 (by decide +kernel) (by simp)
      change legendreSym (h.primes 4) 7 = (-1)
      exact fixed_symbol h 4 7 7 1 11 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((13 : ℤ) : ZMod (h.primes 4)) ≠ 0 := by
        simpa using small_cast_unit h 4 13 (by decide +kernel) (by simp)
      change legendreSym (h.primes 4) 13 = (-1)
      exact fixed_symbol h 4 13 13 1 15 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
  · let : Fact (h.primes 5).Prime := ⟨h.prime 5⟩
    fin_cases j
    · have hu : (((-1) : ℤ) : ZMod (h.primes 5)) ≠ 0 := by
        simp
      change legendreSym (h.primes 5) (-1) = 1
      exact fixed_symbol h 5 (-1) (-1) 1 1 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((2 : ℤ) : ZMod (h.primes 5)) ≠ 0 := by
        simpa using small_cast_unit h 5 2 (by decide +kernel) (by simp)
      change legendreSym (h.primes 5) 2 = (-1)
      exact fixed_symbol h 5 2 2 1 5 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((3 : ℤ) : ZMod (h.primes 5)) ≠ 0 := by
        simpa using small_cast_unit h 5 3 (by decide +kernel) (by simp)
      change legendreSym (h.primes 5) 3 = 1
      exact fixed_symbol h 5 3 3 1 1 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((7 : ℤ) : ZMod (h.primes 5)) ≠ 0 := by
        simpa using small_cast_unit h 5 7 (by decide +kernel) (by simp)
      change legendreSym (h.primes 5) 7 = (-1)
      exact fixed_symbol h 5 7 7 1 13 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((13 : ℤ) : ZMod (h.primes 5)) ≠ 0 := by
        simpa using small_cast_unit h 5 13 (by decide +kernel) (by simp)
      change legendreSym (h.primes 5) 13 = (-1)
      exact fixed_symbol h 5 13 13 1 5 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
  · let : Fact (h.primes 6).Prime := ⟨h.prime 6⟩
    fin_cases j
    · have hu : (((-1) : ℤ) : ZMod (h.primes 6)) ≠ 0 := by
        simp
      change legendreSym (h.primes 6) (-1) = 1
      exact fixed_symbol h 6 (-1) (-1) 1 1 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((2 : ℤ) : ZMod (h.primes 6)) ≠ 0 := by
        simpa using small_cast_unit h 6 2 (by decide +kernel) (by simp)
      change legendreSym (h.primes 6) 2 = (-1)
      exact fixed_symbol h 6 2 2 1 5 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((3 : ℤ) : ZMod (h.primes 6)) ≠ 0 := by
        simpa using small_cast_unit h 6 3 (by decide +kernel) (by simp)
      change legendreSym (h.primes 6) 3 = 1
      exact fixed_symbol h 6 3 3 1 1 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((7 : ℤ) : ZMod (h.primes 6)) ≠ 0 := by
        simpa using small_cast_unit h 6 7 (by decide +kernel) (by simp)
      change legendreSym (h.primes 6) 7 = (-1)
      exact fixed_symbol h 6 7 7 1 5 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((13 : ℤ) : ZMod (h.primes 6)) ≠ 0 := by
        simpa using small_cast_unit h 6 13 (by decide +kernel) (by simp)
      change legendreSym (h.primes 6) 13 = (-1)
      exact fixed_symbol h 6 13 13 1 37 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
  · let : Fact (h.primes 7).Prime := ⟨h.prime 7⟩
    fin_cases j
    · have hu : (((-1) : ℤ) : ZMod (h.primes 7)) ≠ 0 := by
        simp
      change legendreSym (h.primes 7) (-1) = (-1)
      exact fixed_symbol h 7 (-1) (-1) 1 3 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((2 : ℤ) : ZMod (h.primes 7)) ≠ 0 := by
        simpa using small_cast_unit h 7 2 (by decide +kernel) (by simp)
      change legendreSym (h.primes 7) 2 = (-1)
      exact fixed_symbol h 7 2 2 1 3 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((3 : ℤ) : ZMod (h.primes 7)) ≠ 0 := by
        simpa using small_cast_unit h 7 3 (by decide +kernel) (by simp)
      change legendreSym (h.primes 7) 3 = (-1)
      exact fixed_symbol h 7 3 3 1 7 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((7 : ℤ) : ZMod (h.primes 7)) ≠ 0 := by
        simpa using small_cast_unit h 7 7 (by decide +kernel) (by simp)
      change legendreSym (h.primes 7) 7 = 1
      exact fixed_symbol h 7 7 7 1 3 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((13 : ℤ) : ZMod (h.primes 7)) ≠ 0 := by
        simpa using small_cast_unit h 7 13 (by decide +kernel) (by simp)
      change legendreSym (h.primes 7) 13 = 1
      exact fixed_symbol h 7 13 13 1 35 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
  · let : Fact (h.primes 8).Prime := ⟨h.prime 8⟩
    fin_cases j
    · have hu : (((-1) : ℤ) : ZMod (h.primes 8)) ≠ 0 := by
        simp
      change legendreSym (h.primes 8) (-1) = (-1)
      exact fixed_symbol h 8 (-1) (-1) 1 3 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((2 : ℤ) : ZMod (h.primes 8)) ≠ 0 := by
        simpa using small_cast_unit h 8 2 (by decide +kernel) (by simp)
      change legendreSym (h.primes 8) 2 = 1
      exact fixed_symbol h 8 2 2 1 7 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((3 : ℤ) : ZMod (h.primes 8)) ≠ 0 := by
        simpa using small_cast_unit h 8 3 (by decide +kernel) (by simp)
      change legendreSym (h.primes 8) 3 = 1
      exact fixed_symbol h 8 3 3 1 11 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((7 : ℤ) : ZMod (h.primes 8)) ≠ 0 := by
        simpa using small_cast_unit h 8 7 (by decide +kernel) (by simp)
      change legendreSym (h.primes 8) 7 = (-1)
      exact fixed_symbol h 8 7 7 1 11 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((13 : ℤ) : ZMod (h.primes 8)) ≠ 0 := by
        simpa using small_cast_unit h 8 13 (by decide +kernel) (by simp)
      change legendreSym (h.primes 8) 13 = 1
      exact fixed_symbol h 8 13 13 1 27 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
  · let : Fact (h.primes 9).Prime := ⟨h.prime 9⟩
    fin_cases j
    · have hu : (((-1) : ℤ) : ZMod (h.primes 9)) ≠ 0 := by
        simp
      change legendreSym (h.primes 9) (-1) = 1
      exact fixed_symbol h 9 (-1) (-1) 1 1 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((2 : ℤ) : ZMod (h.primes 9)) ≠ 0 := by
        simpa using small_cast_unit h 9 2 (by decide +kernel) (by simp)
      change legendreSym (h.primes 9) 2 = (-1)
      exact fixed_symbol h 9 2 2 1 5 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((3 : ℤ) : ZMod (h.primes 9)) ≠ 0 := by
        simpa using small_cast_unit h 9 3 (by decide +kernel) (by simp)
      change legendreSym (h.primes 9) 3 = (-1)
      exact fixed_symbol h 9 3 3 1 5 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((7 : ℤ) : ZMod (h.primes 9)) ≠ 0 := by
        simpa using small_cast_unit h 9 7 (by decide +kernel) (by simp)
      change legendreSym (h.primes 9) 7 = 1
      exact fixed_symbol h 9 7 7 1 9 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((13 : ℤ) : ZMod (h.primes 9)) ≠ 0 := by
        simpa using small_cast_unit h 9 13 (by decide +kernel) (by simp)
      change legendreSym (h.primes 9) 13 = (-1)
      exact fixed_symbol h 9 13 13 1 5 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
  · let : Fact (h.primes 10).Prime := ⟨h.prime 10⟩
    fin_cases j
    · have hu : (((-1) : ℤ) : ZMod (h.primes 10)) ≠ 0 := by
        simp
      change legendreSym (h.primes 10) (-1) = 1
      exact fixed_symbol h 10 (-1) (-1) 1 1 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((2 : ℤ) : ZMod (h.primes 10)) ≠ 0 := by
        simpa using small_cast_unit h 10 2 (by decide +kernel) (by simp)
      change legendreSym (h.primes 10) 2 = (-1)
      exact fixed_symbol h 10 2 2 1 5 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((3 : ℤ) : ZMod (h.primes 10)) ≠ 0 := by
        simpa using small_cast_unit h 10 3 (by decide +kernel) (by simp)
      change legendreSym (h.primes 10) 3 = 1
      exact fixed_symbol h 10 3 3 1 1 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((7 : ℤ) : ZMod (h.primes 10)) ≠ 0 := by
        simpa using small_cast_unit h 10 7 (by decide +kernel) (by simp)
      change legendreSym (h.primes 10) 7 = 1
      exact fixed_symbol h 10 7 7 1 9 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((13 : ℤ) : ZMod (h.primes 10)) ≠ 0 := by
        simpa using small_cast_unit h 10 13 (by decide +kernel) (by simp)
      change legendreSym (h.primes 10) 13 = (-1)
      exact fixed_symbol h 10 13 13 1 45 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
  · let : Fact (h.primes 11).Prime := ⟨h.prime 11⟩
    fin_cases j
    · have hu : (((-1) : ℤ) : ZMod (h.primes 11)) ≠ 0 := by
        simp
      change legendreSym (h.primes 11) (-1) = (-1)
      exact fixed_symbol h 11 (-1) (-1) 1 3 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((2 : ℤ) : ZMod (h.primes 11)) ≠ 0 := by
        simpa using small_cast_unit h 11 2 (by decide +kernel) (by simp)
      change legendreSym (h.primes 11) 2 = 1
      exact fixed_symbol h 11 2 2 1 7 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((3 : ℤ) : ZMod (h.primes 11)) ≠ 0 := by
        simpa using small_cast_unit h 11 3 (by decide +kernel) (by simp)
      change legendreSym (h.primes 11) 3 = 1
      exact fixed_symbol h 11 3 3 1 11 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((7 : ℤ) : ZMod (h.primes 11)) ≠ 0 := by
        simpa using small_cast_unit h 11 7 (by decide +kernel) (by simp)
      change legendreSym (h.primes 11) 7 = 1
      exact fixed_symbol h 11 7 7 1 3 1
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)
    · have hu : ((13 : ℤ) : ZMod (h.primes 11)) ≠ 0 := by
        simpa using small_cast_unit h 11 13 (by decide +kernel) (by simp)
      change legendreSym (h.primes 11) 13 = (-1)
      exact fixed_symbol h 11 13 13 1 11 (-1)
        (by norm_num) hu
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num [PrimePatterns.Rank7.outputs])
        (by norm_num)

theorem constant_character (i : Fin 12) (j : Fin 5) [Fact (h.primes i).Prime] :
    unitCharacterParity (h.primes i)
      (Additive.ofMul (rationalSquareClass (constantColumns j : ℚ))) =
      quadraticCharacterBit (constantSign i j) := by
  have hu : (constantColumns j : ZMod (h.primes i)) ≠ 0 := by
    fin_cases j
    · simp [constantColumns]
    · simpa [constantColumns] using small_cast_unit h i 2 (by decide +kernel) (by simp)
    · simpa [constantColumns] using small_cast_unit h i 3 (by decide +kernel) (by simp)
    · simpa [constantColumns] using small_cast_unit h i 7 (by decide +kernel) (by simp)
    · simpa [constantColumns] using small_cast_unit h i 13 (by decide +kernel) (by simp)
  have hd : ¬ (h.primes i : ℤ) ∣ constantColumns j :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).not.mp hu
  rw [unitCharacterParity_int_of_not_dvd (h.primes i) hd, constant_symbol h i j]

def primeBit (i k : Fin 12) (e : ℤ) : ZMod 2 :=
  if i = k then 0 else quadraticCharacterBit (crossSign i k * e)

theorem prime_character (i k : Fin 12) [Fact (h.primes i).Prime]
    (hik : i = k ∨ UsedPair i k) :
    unitCharacterParity (h.primes i)
      (Additive.ofMul (rationalSquareClass (h.primes k : ℚ))) =
      primeBit i k (epsilon h) := by
  let : Fact (h.primes k).Prime := ⟨h.prime k⟩
  by_cases he : i = k
  · subst k
    rw [MovingPrimeCharacters.unitCharacterParity_prime_self]
    simp [primeBit]
  · have hu : UsedPair i k := hik.resolve_left he
    rw [unitCharacterParity_prime_other (h.primes i) (h.primes k)
      (fun heq => he (h.distinct heq)), cross_symbol h i k hu]
    simp only [primeBit, ite_eq_right he]

theorem character_mul (p : ℕ) [Fact p.Prime] {u v : ℚ}
    (hu : u ≠ 0) (hv : v ≠ 0) :
    unitCharacterParity p (Additive.ofMul (rationalSquareClass (u * v))) =
      unitCharacterParity p (Additive.ofMul (rationalSquareClass u)) +
        unitCharacterParity p (Additive.ofMul (rationalSquareClass v)) := by
  rw [rationalSquareClass_mul hu hv]
  exact (unitCharacterParity p).map_add _ _

theorem character_prod {ι : Type*} [DecidableEq ι] (p : ℕ) [Fact p.Prime]
    (s : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ s, f i ≠ 0) :
    unitCharacterParity p (Additive.ofMul (rationalSquareClass (∏ i ∈ s, f i))) =
      ∑ i ∈ s, unitCharacterParity p (Additive.ofMul (rationalSquareClass (f i))) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj,
      character_mul p (hf j (by simp))
        (Finset.prod_ne_zero_iff.mpr (fun i hi => hf i (by simp [hi])))]
    rw [ih (fun i hi => hf i (by simp [hi]))]

def EprimeIndex : Fin 8 → Fin 12 := ![0, 1, 2, 3, 4, 5, 6, 7]
def EpprimeIndex : Fin 8 → Fin 12 := ![0, 1, 2, 3, 8, 9, 10, 11]

theorem Eprime_pair (i : Fin 12) (hi : i.val < 4 ∨ 8 ≤ i.val) (k : Fin 8) :
    i = EprimeIndex k ∨ UsedPair i (EprimeIndex k) := by
  fin_cases k <;> norm_num [EprimeIndex, UsedPair] <;> omega

theorem Epprime_pair (i : Fin 12) (hi : i.val < 8) (k : Fin 8) :
    i = EpprimeIndex k ∨ UsedPair i (EpprimeIndex k) := by
  fin_cases k <;> norm_num [EpprimeIndex, UsedPair] <;> omega

theorem b_factorization : Rank7.b (M7 x) (N7 y) =
    (-2 * ∏ k : Fin 8, (h.primes (EprimeIndex k) : ℚ)) * 471744 ^ 2 := by
  rw [Rank7.b, Rank7PrimeValuations.F_factorization h,
    Rank7PrimeValuations.H_factorization h]
  norm_num [Fin.prod_univ_succ, EprimeIndex]
  ring

theorem c_factorization : Rank7.c (M7 x) (N7 y) =
    (3 * ∏ k : Fin 8, (h.primes (EpprimeIndex k) : ℚ)) * 93312 ^ 2 := by
  rw [Rank7.c, Rank7PrimeValuations.F_factorization h,
    Rank7PrimeValuations.J_factorization h]
  norm_num [Fin.prod_univ_succ, EpprimeIndex]
  ring

theorem coefficientE_character (i : Fin 12) [Fact (h.primes i).Prime]
    (hi : i.val < 4 ∨ 8 ≤ i.val) :
    unitCharacterParity (h.primes i)
      (Additive.ofMul (rationalSquareClass (Rank7.b (M7 x) (N7 y)))) =
      quadraticCharacterBit (constantSign i 0) + quadraticCharacterBit (constantSign i 1) +
        ∑ k : Fin 8, primeBit i (EprimeIndex k) (epsilon h) := by
  have hp : (∏ k : Fin 8, (h.primes (EprimeIndex k) : ℚ)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun k _ => Rank7PrimeValuations.prime_nonzero h _)
  rw [b_factorization h, rationalSquareClass_mul_square
    (mul_ne_zero (by norm_num) hp) (by norm_num)]
  rw [character_mul (h.primes i) (by norm_num) hp,
    character_prod _ _ _ (fun k _ => Rank7PrimeValuations.prime_nonzero h _)]
  have hconst : unitCharacterParity (h.primes i)
      (Additive.ofMul (rationalSquareClass (-2))) =
      quadraticCharacterBit (constantSign i 0) + quadraticCharacterBit (constantSign i 1) := by
    rw [show (-2 : ℚ) = -1 * 2 by norm_num]
    rw [character_mul _ (by norm_num) (by norm_num)]
    exact congrArg₂ (· + ·) (constant_character h i 0) (constant_character h i 1)
  rw [hconst]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact prime_character h i _ (Eprime_pair i hi k)

theorem coefficientEp_character (i : Fin 12) [Fact (h.primes i).Prime]
    (hi : i.val < 8) :
    unitCharacterParity (h.primes i)
      (Additive.ofMul (rationalSquareClass (Rank7.c (M7 x) (N7 y)))) =
      quadraticCharacterBit (constantSign i 2) +
        ∑ k : Fin 8, primeBit i (EpprimeIndex k) (epsilon h) := by
  have hp : (∏ k : Fin 8, (h.primes (EpprimeIndex k) : ℚ)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun k _ => Rank7PrimeValuations.prime_nonzero h _)
  rw [c_factorization h, rationalSquareClass_mul_square
    (mul_ne_zero (by norm_num) hp) (by norm_num)]
  rw [character_mul (h.primes i) (by norm_num) hp,
    character_prod _ _ _ (fun k _ => Rank7PrimeValuations.prime_nonzero h _)]
  rw [show unitCharacterParity (h.primes i)
      (Additive.ofMul (rationalSquareClass 3)) = quadraticCharacterBit (constantSign i 2)
    from constant_character h i 2]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact prime_character h i _ (Epprime_pair i hi k)

def movingERow (i : Fin 12) (e : ℤ) : Fin 13 → ZMod 2 :=
  ![quadraticCharacterBit (constantSign i 0), quadraticCharacterBit (constantSign i 1),
    quadraticCharacterBit (constantSign i 2), quadraticCharacterBit (constantSign i 3),
    quadraticCharacterBit (constantSign i 4),
    primeBit i 0 e, primeBit i 1 e, primeBit i 2 e, primeBit i 3 e,
    primeBit i 4 e, primeBit i 5 e, primeBit i 6 e, primeBit i 7 e]

def movingEpRow (i : Fin 12) (e : ℤ) : Fin 13 → ZMod 2 :=
  ![quadraticCharacterBit (constantSign i 0), quadraticCharacterBit (constantSign i 1),
    quadraticCharacterBit (constantSign i 2), quadraticCharacterBit (constantSign i 3),
    quadraticCharacterBit (constantSign i 4),
    primeBit i 0 e, primeBit i 1 e, primeBit i 2 e, primeBit i 3 e,
    primeBit i 8 e, primeBit i 9 e, primeBit i 10 e, primeBit i 11 e]

theorem signed_columnsE_eq (p : Fin 12 → ℕ) :
    signedPrimeColumns (primeColumns7E p) =
      ![-1, 2, 3, 7, 13, (p 0 : ℚ), p 1, p 2, p 3, p 4, p 5, p 6, p 7] := by
  funext j
  fin_cases j <;> rfl

theorem signed_columnsEp_eq (p : Fin 12 → ℕ) :
    signedPrimeColumns (primeColumns7Ep p) =
      ![-1, 2, 3, 7, 13, (p 0 : ℚ), p 1, p 2, p 3, p 8, p 9, p 10, p 11] := by
  funext j
  fin_cases j <;> rfl

theorem unitCharacterRowE (i : Fin 12) [Fact (h.primes i).Prime]
    (hi : i.val < 4 ∨ 8 ≤ i.val) :
    unitCharacterRow (h.primes i) (signedPrimeColumns (primeColumns7E h.primes)) =
      movingERow i (epsilon h) := by
  rw [signed_columnsE_eq]
  funext j
  fin_cases j
  · simpa [unitCharacterRow, signedPrimeColumns, primeColumns7E, movingERow, constantColumns]
      using constant_character h i 0
  · simpa [unitCharacterRow, signedPrimeColumns, primeColumns7E, movingERow, constantColumns]
      using constant_character h i 1
  · simpa [unitCharacterRow, signedPrimeColumns, primeColumns7E, movingERow, constantColumns]
      using constant_character h i 2
  · simpa [unitCharacterRow, signedPrimeColumns, primeColumns7E, movingERow, constantColumns]
      using constant_character h i 3
  · simpa [unitCharacterRow, signedPrimeColumns, primeColumns7E, movingERow, constantColumns]
      using constant_character h i 4
  · simpa [unitCharacterRow, signedPrimeColumns, primeColumns7E, movingERow, EprimeIndex]
      using prime_character h i (EprimeIndex 0) (Eprime_pair i hi 0)
  · simpa [unitCharacterRow, signedPrimeColumns, primeColumns7E, movingERow, EprimeIndex]
      using prime_character h i (EprimeIndex 1) (Eprime_pair i hi 1)
  · simpa [unitCharacterRow, signedPrimeColumns, primeColumns7E, movingERow, EprimeIndex]
      using prime_character h i (EprimeIndex 2) (Eprime_pair i hi 2)
  · simpa [unitCharacterRow, signedPrimeColumns, primeColumns7E, movingERow, EprimeIndex]
      using prime_character h i (EprimeIndex 3) (Eprime_pair i hi 3)
  · simpa [unitCharacterRow, signedPrimeColumns, primeColumns7E, movingERow, EprimeIndex]
      using prime_character h i (EprimeIndex 4) (Eprime_pair i hi 4)
  · simpa [unitCharacterRow, signedPrimeColumns, primeColumns7E, movingERow, EprimeIndex]
      using prime_character h i (EprimeIndex 5) (Eprime_pair i hi 5)
  · simpa [unitCharacterRow, signedPrimeColumns, primeColumns7E, movingERow, EprimeIndex]
      using prime_character h i (EprimeIndex 6) (Eprime_pair i hi 6)
  · simpa [unitCharacterRow, signedPrimeColumns, primeColumns7E, movingERow, EprimeIndex]
      using prime_character h i (EprimeIndex 7) (Eprime_pair i hi 7)

theorem unitCharacterRowEp (i : Fin 12) [Fact (h.primes i).Prime]
    (hi : i.val < 8) :
    unitCharacterRow (h.primes i) (signedPrimeColumns (primeColumns7Ep h.primes)) =
      movingEpRow i (epsilon h) := by
  rw [signed_columnsEp_eq]
  funext j
  fin_cases j
  · simpa [unitCharacterRow, signedPrimeColumns, primeColumns7Ep, movingEpRow, constantColumns]
      using constant_character h i 0
  · simpa [unitCharacterRow, signedPrimeColumns, primeColumns7Ep, movingEpRow, constantColumns]
      using constant_character h i 1
  · simpa [unitCharacterRow, signedPrimeColumns, primeColumns7Ep, movingEpRow, constantColumns]
      using constant_character h i 2
  · simpa [unitCharacterRow, signedPrimeColumns, primeColumns7Ep, movingEpRow, constantColumns]
      using constant_character h i 3
  · simpa [unitCharacterRow, signedPrimeColumns, primeColumns7Ep, movingEpRow, constantColumns]
      using constant_character h i 4
  · simpa [unitCharacterRow, signedPrimeColumns, primeColumns7Ep, movingEpRow, EpprimeIndex]
      using prime_character h i (EpprimeIndex 0) (Epprime_pair i hi 0)
  · simpa [unitCharacterRow, signedPrimeColumns, primeColumns7Ep, movingEpRow, EpprimeIndex]
      using prime_character h i (EpprimeIndex 1) (Epprime_pair i hi 1)
  · simpa [unitCharacterRow, signedPrimeColumns, primeColumns7Ep, movingEpRow, EpprimeIndex]
      using prime_character h i (EpprimeIndex 2) (Epprime_pair i hi 2)
  · simpa [unitCharacterRow, signedPrimeColumns, primeColumns7Ep, movingEpRow, EpprimeIndex]
      using prime_character h i (EpprimeIndex 3) (Epprime_pair i hi 3)
  · simpa [unitCharacterRow, signedPrimeColumns, primeColumns7Ep, movingEpRow, EpprimeIndex]
      using prime_character h i (EpprimeIndex 4) (Epprime_pair i hi 4)
  · simpa [unitCharacterRow, signedPrimeColumns, primeColumns7Ep, movingEpRow, EpprimeIndex]
      using prime_character h i (EpprimeIndex 5) (Epprime_pair i hi 5)
  · simpa [unitCharacterRow, signedPrimeColumns, primeColumns7Ep, movingEpRow, EpprimeIndex]
      using prime_character h i (EpprimeIndex 6) (Epprime_pair i hi 6)
  · simpa [unitCharacterRow, signedPrimeColumns, primeColumns7Ep, movingEpRow, EpprimeIndex]
      using prime_character h i (EpprimeIndex 7) (Epprime_pair i hi 7)

def Findex (i : Fin 4) : Fin 12 := ⟨i.val, by omega⟩
def Hindex (i : Fin 4) : Fin 12 := ⟨i.val + 4, by omega⟩
def Jindex (i : Fin 4) : Fin 12 := ⟨i.val + 8, by omega⟩

noncomputable def ETypeII (i : Fin 4) :
    Additive RationalSquareClasses →ₗ[ZMod 2] ZMod 2 :=
  letI : Fact (h.primes (Jindex i)).Prime := ⟨h.prime (Jindex i)⟩
  unitCharacterLinear (h.primes (Jindex i))

noncomputable def EpTypeII (i : Fin 4) :
    Additive RationalSquareClasses →ₗ[ZMod 2] ZMod 2 :=
  letI : Fact (h.primes (Hindex i)).Prime := ⟨h.prime (Hindex i)⟩
  unitCharacterLinear (h.primes (Hindex i))

theorem ETypeII_row0 (i : Fin 4) (he : epsilon h = 1) :
    squareClassCharacterRow (ETypeII h i) (signedPrimeColumns (primeColumns7E h.primes)) =
      Binary.vector 13 (MatrixCertificates.Rank7.E0.getD (i.val + 8) 0) := by
  let : Fact (h.primes (Jindex i)).Prime := ⟨h.prime (Jindex i)⟩
  change unitCharacterRow (h.primes (Jindex i)) _ = _
  rw [unitCharacterRowE h _ (Or.inr (by simp [Jindex])), he]
  fin_cases i <;> decide +kernel

theorem ETypeII_row1 (i : Fin 4) (he : epsilon h = -1) :
    squareClassCharacterRow (ETypeII h i) (signedPrimeColumns (primeColumns7E h.primes)) =
      Binary.vector 13 (MatrixCertificates.Rank7.E1.getD (i.val + 8) 0) := by
  let : Fact (h.primes (Jindex i)).Prime := ⟨h.prime (Jindex i)⟩
  change unitCharacterRow (h.primes (Jindex i)) _ = _
  rw [unitCharacterRowE h _ (Or.inr (by simp [Jindex])), he]
  fin_cases i <;> decide +kernel

theorem EpTypeII_row0 (i : Fin 4) (he : epsilon h = 1) :
    squareClassCharacterRow (EpTypeII h i) (signedPrimeColumns (primeColumns7Ep h.primes)) =
      Binary.vector 13 (MatrixCertificates.Rank7.Ep0.getD (i.val + 10) 0) := by
  let : Fact (h.primes (Hindex i)).Prime := ⟨h.prime (Hindex i)⟩
  change unitCharacterRow (h.primes (Hindex i)) _ = _
  rw [unitCharacterRowEp h _ (by simp [Hindex]; omega), he]
  fin_cases i <;> decide +kernel

theorem EpTypeII_row1 (i : Fin 4) (he : epsilon h = -1) :
    squareClassCharacterRow (EpTypeII h i) (signedPrimeColumns (primeColumns7Ep h.primes)) =
      Binary.vector 13 (MatrixCertificates.Rank7.Ep1.getD (i.val + 10) 0) := by
  let : Fact (h.primes (Hindex i)).Prime := ⟨h.prime (Hindex i)⟩
  change unitCharacterRow (h.primes (Hindex i)) _ = _
  rw [unitCharacterRowEp h _ (by simp [Hindex]; omega), he]
  fin_cases i <;> decide +kernel

theorem small_prime_parity (i : Fin 12) (q : ℕ) (hq : q.Prime)
    (hs : q ∈ [2, 3, 7, 13]) :
    primeParity (h.primes i) (h.prime i)
      (Additive.ofMul (rationalSquareClass (q : ℚ))) = 0 := by
  exact (primeParity_prime (h.prime i) hq).trans (ite_eq_right (h.outside i q hs))

set_option backward.isDefEq.respectTransparency false in
theorem moving_prime_parity (i k : Fin 12) :
    primeParity (h.primes i) (h.prime i)
      (Additive.ofMul (rationalSquareClass (h.primes k : ℚ))) =
      if i = k then 1 else 0 := by
  refine (primeParity_prime (p := h.primes i) (q := h.primes k)
    (h.prime i) (h.prime k)).trans ?_
  by_cases he : i = k
  · subst k
    simp
  · have hp : h.primes i ≠ h.primes k := fun hp => he (h.distinct hp)
    simp only [ite_eq_right hp, ite_eq_right he]

theorem valuationRowE (i : Fin 4) :
    squareClassCharacterRow
      ((primeParity (h.primes (Findex i)) (h.prime (Findex i))).toZModLinearMap 2)
      (signedPrimeColumns (primeColumns7E h.primes)) =
      Binary.vector 13 (2 ^ (5 + i.val)) := by
  have hs2 := small_prime_parity h (Findex i) 2 (by decide +kernel) (by simp)
  have hs3 := small_prime_parity h (Findex i) 3 (by decide +kernel) (by simp)
  have hs7 := small_prime_parity h (Findex i) 7 (by decide +kernel) (by simp)
  have hs13 := small_prime_parity h (Findex i) 13 (by decide +kernel) (by simp)
  norm_num at hs2 hs3 hs7 hs13
  rw [signed_columnsE_eq]
  funext j
  fin_cases j <;> simp only [squareClassCharacterRow, AddMonoidHom.coe_toZModLinearMap]
  all_goals norm_num [primeParity_neg_one, hs2, hs3, hs7, hs13,
    moving_prime_parity h, Binary.vector, Binary.scalar]
  all_goals fin_cases i <;> norm_num [Findex]
  all_goals decide +kernel

theorem valuationRowEp (i : Fin 4) :
    squareClassCharacterRow
      ((primeParity (h.primes (Findex i)) (h.prime (Findex i))).toZModLinearMap 2)
      (signedPrimeColumns (primeColumns7Ep h.primes)) =
      Binary.vector 13 (2 ^ (5 + i.val)) := by
  have hs2 := small_prime_parity h (Findex i) 2 (by decide +kernel) (by simp)
  have hs3 := small_prime_parity h (Findex i) 3 (by decide +kernel) (by simp)
  have hs7 := small_prime_parity h (Findex i) 7 (by decide +kernel) (by simp)
  have hs13 := small_prime_parity h (Findex i) 13 (by decide +kernel) (by simp)
  norm_num at hs2 hs3 hs7 hs13
  rw [signed_columnsEp_eq]
  funext j
  fin_cases j <;> simp only [squareClassCharacterRow, AddMonoidHom.coe_toZModLinearMap]
  all_goals norm_num [primeParity_neg_one, hs2, hs3, hs7, hs13,
    moving_prime_parity h, Binary.vector, Binary.scalar]
  all_goals fin_cases i <;> norm_num [Findex]
  all_goals decide +kernel

noncomputable def ETypeIII (i : Fin 4) :
    Additive RationalSquareClasses →ₗ[ZMod 2] ZMod 2 :=
  letI : Fact (h.primes (Findex i)).Prime := ⟨h.prime (Findex i)⟩
  typeIIICharacterLinear (h.primes (Findex i)) (Rank7.b (M7 x) (N7 y))

noncomputable def EpTypeIII (i : Fin 4) :
    Additive RationalSquareClasses →ₗ[ZMod 2] ZMod 2 :=
  letI : Fact (h.primes (Findex i)).Prime := ⟨h.prime (Findex i)⟩
  typeIIICharacterLinear (h.primes (Findex i)) (Rank7.c (M7 x) (N7 y))

theorem ETypeIII_character_row (i : Fin 4) :
    squareClassCharacterRow (ETypeIII h i) (signedPrimeColumns (primeColumns7E h.primes)) =
      movingERow (Findex i) (epsilon h) +
        (quadraticCharacterBit (constantSign (Findex i) 0) +
          quadraticCharacterBit (constantSign (Findex i) 1) +
          ∑ k : Fin 8, primeBit (Findex i) (EprimeIndex k) (epsilon h)) •
          Binary.vector 13 (2 ^ (5 + i.val)) := by
  let : Fact (h.primes (Findex i)).Prime := ⟨h.prime (Findex i)⟩
  have hu := unitCharacterRowE h (Findex i) (Or.inl i.isLt)
  have hc := coefficientE_character h (Findex i) (Or.inl i.isLt)
  have hv := valuationRowE h i
  funext j
  change unitCharacterRow (h.primes (Findex i)) _ j +
    unitCharacterParity (h.primes (Findex i))
      (Additive.ofMul (rationalSquareClass (Rank7.b (M7 x) (N7 y)))) *
    squareClassCharacterRow
      ((primeParity (h.primes (Findex i)) (h.prime (Findex i))).toZModLinearMap 2) _ j = _
  rw [hu, hc, hv]
  rfl

theorem EpTypeIII_character_row (i : Fin 4) :
    squareClassCharacterRow (EpTypeIII h i) (signedPrimeColumns (primeColumns7Ep h.primes)) =
      movingEpRow (Findex i) (epsilon h) +
        (quadraticCharacterBit (constantSign (Findex i) 2) +
          ∑ k : Fin 8, primeBit (Findex i) (EpprimeIndex k) (epsilon h)) •
          Binary.vector 13 (2 ^ (5 + i.val)) := by
  let : Fact (h.primes (Findex i)).Prime := ⟨h.prime (Findex i)⟩
  have hu := unitCharacterRowEp h (Findex i) (by simp [Findex]; omega)
  have hc := coefficientEp_character h (Findex i) (by simp [Findex]; omega)
  have hv := valuationRowEp h i
  funext j
  change unitCharacterRow (h.primes (Findex i)) _ j +
    unitCharacterParity (h.primes (Findex i))
      (Additive.ofMul (rationalSquareClass (Rank7.c (M7 x) (N7 y)))) *
    squareClassCharacterRow
      ((primeParity (h.primes (Findex i)) (h.prime (Findex i))).toZModLinearMap 2) _ j = _
  rw [hu, hc, hv]
  rfl

theorem ETypeIII_row0 (i : Fin 4) (he : epsilon h = 1) :
    squareClassCharacterRow (ETypeIII h i) (signedPrimeColumns (primeColumns7E h.primes)) =
      Binary.vector 13 (MatrixCertificates.Rank7.E0.getD (i.val + 4) 0) := by
  rw [ETypeIII_character_row h i, he]
  fin_cases i <;> decide +kernel

theorem ETypeIII_row1 (i : Fin 4) (he : epsilon h = -1) :
    squareClassCharacterRow (ETypeIII h i) (signedPrimeColumns (primeColumns7E h.primes)) =
      Binary.vector 13 (MatrixCertificates.Rank7.E1.getD (i.val + 4) 0) := by
  rw [ETypeIII_character_row h i, he]
  fin_cases i <;> decide +kernel

theorem EpTypeIII_row0 (i : Fin 4) (he : epsilon h = 1) :
    squareClassCharacterRow (EpTypeIII h i) (signedPrimeColumns (primeColumns7Ep h.primes)) =
      Binary.vector 13 (MatrixCertificates.Rank7.Ep0.getD (i.val + 6) 0) := by
  rw [EpTypeIII_character_row h i, he]
  fin_cases i <;> decide +kernel

theorem EpTypeIII_row1 (i : Fin 4) (he : epsilon h = -1) :
    squareClassCharacterRow (EpTypeIII h i) (signedPrimeColumns (primeColumns7Ep h.primes)) =
      Binary.vector 13 (MatrixCertificates.Rank7.Ep1.getD (i.val + 6) 0) := by
  rw [EpTypeIII_character_row h i, he]
  fin_cases i <;> decide +kernel

theorem ETypeII_actualImage (i : Fin 4) {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (Rank7.a (M7 x) (N7 y)) (Rank7.b (M7 x) (N7 y))) :
    ETypeII h i (Additive.ofMul q) = 0 := by
  let : Fact (h.primes (Jindex i)).Prime := ⟨h.prime (Jindex i)⟩
  exact Rank7PrimeValuations.J_prime_E_image_row h (Jindex i) (by simp [Jindex]) hq

theorem EpTypeII_actualImage (i : Fin 4) {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (-2 * Rank7.a (M7 x) (N7 y)) (Rank7.c (M7 x) (N7 y))) :
    EpTypeII h i (Additive.ofMul q) = 0 := by
  let : Fact (h.primes (Hindex i)).Prime := ⟨h.prime (Hindex i)⟩
  exact Rank7PrimeValuations.H_prime_Ep_image_row h (Hindex i)
    (by simp [Hindex]) (by simp [Hindex]; omega) hq

theorem ETypeIII_actualImage (i : Fin 4) {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (Rank7.a (M7 x) (N7 y)) (Rank7.b (M7 x) (N7 y))) :
    ETypeIII h i (Additive.ofMul q) = 0 := by
  let : Fact (h.primes (Findex i)).Prime := ⟨h.prime (Findex i)⟩
  exact Rank7PrimeValuations.typeIII_E_image_row h (Findex i)
    i.isLt hq

theorem EpTypeIII_actualImage (i : Fin 4) {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (-2 * Rank7.a (M7 x) (N7 y)) (Rank7.c (M7 x) (N7 y))) :
    EpTypeIII h i (Additive.ofMul q) = 0 := by
  let : Fact (h.primes (Findex i)).Prime := ⟨h.prime (Findex i)⟩
  exact Rank7PrimeValuations.typeIII_Ep_image_row h (Findex i)
    i.isLt hq

/-- Each literal moving-prime row is a proved functional on actual point images. -/
theorem E_moving_rows0 (he : epsilon h = 1) :
    ∀ row ∈ MatrixCertificates.Rank7.E0.drop 4,
      ∃ f : Additive RationalSquareClasses →ₗ[ZMod 2] ZMod 2,
        squareClassCharacterRow f (signedPrimeColumns (primeColumns7E h.primes)) =
          Binary.vector 13 row ∧
        ∀ q ∈ twoIsogenyImage (Rank7.a (M7 x) (N7 y)) (Rank7.b (M7 x) (N7 y)), f (Additive.ofMul q) = 0 := by
  intro row hr
  have hh : row = 4896 ∨ row = 219 ∨ row = 340 ∨ row = 3583 ∨ row = 7945 ∨ row = 7734 ∨ row = 466 ∨ row = 3121 := by
    simpa [MatrixCertificates.Rank7.E0] using hr
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨ETypeIII h 0, ?_, ?_⟩
    · simpa [MatrixCertificates.Rank7.E0] using ETypeIII_row0 h 0 he
    · intro q hq
      exact ETypeIII_actualImage h 0 hq
  · refine ⟨ETypeIII h 1, ?_, ?_⟩
    · simpa [MatrixCertificates.Rank7.E0] using ETypeIII_row0 h 1 he
    · intro q hq
      exact ETypeIII_actualImage h 1 hq
  · refine ⟨ETypeIII h 2, ?_, ?_⟩
    · simpa [MatrixCertificates.Rank7.E0] using ETypeIII_row0 h 2 he
    · intro q hq
      exact ETypeIII_actualImage h 2 hq
  · refine ⟨ETypeIII h 3, ?_, ?_⟩
    · simpa [MatrixCertificates.Rank7.E0] using ETypeIII_row0 h 3 he
    · intro q hq
      exact ETypeIII_actualImage h 3 hq
  · refine ⟨ETypeII h 0, ?_, ?_⟩
    · simpa [MatrixCertificates.Rank7.E0] using ETypeII_row0 h 0 he
    · intro q hq
      exact ETypeII_actualImage h 0 hq
  · refine ⟨ETypeII h 1, ?_, ?_⟩
    · simpa [MatrixCertificates.Rank7.E0] using ETypeII_row0 h 1 he
    · intro q hq
      exact ETypeII_actualImage h 1 hq
  · refine ⟨ETypeII h 2, ?_, ?_⟩
    · simpa [MatrixCertificates.Rank7.E0] using ETypeII_row0 h 2 he
    · intro q hq
      exact ETypeII_actualImage h 2 hq
  · refine ⟨ETypeII h 3, ?_, ?_⟩
    · simpa [MatrixCertificates.Rank7.E0] using ETypeII_row0 h 3 he
    · intro q hq
      exact ETypeII_actualImage h 3 hq
/-- Each literal moving-prime row is a proved functional on actual point images. -/
theorem E_moving_rows1 (he : epsilon h = -1) :
    ∀ row ∈ MatrixCertificates.Rank7.E1.drop 4,
      ∃ f : Additive RationalSquareClasses →ₗ[ZMod 2] ZMod 2,
        squareClassCharacterRow f (signedPrimeColumns (primeColumns7E h.primes)) =
          Binary.vector 13 row ∧
        ∀ q ∈ twoIsogenyImage (Rank7.a (M7 x) (N7 y)) (Rank7.b (M7 x) (N7 y)), f (Additive.ofMul q) = 0 := by
  intro row hr
  have hh : row = 3264 ∨ row = 7995 ∨ row = 7860 ∨ row = 4639 ∨ row = 233 ∨ row = 470 ∨ row = 7730 ∨ row = 5073 := by
    simpa [MatrixCertificates.Rank7.E1] using hr
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨ETypeIII h 0, ?_, ?_⟩
    · simpa [MatrixCertificates.Rank7.E1] using ETypeIII_row1 h 0 he
    · intro q hq
      exact ETypeIII_actualImage h 0 hq
  · refine ⟨ETypeIII h 1, ?_, ?_⟩
    · simpa [MatrixCertificates.Rank7.E1] using ETypeIII_row1 h 1 he
    · intro q hq
      exact ETypeIII_actualImage h 1 hq
  · refine ⟨ETypeIII h 2, ?_, ?_⟩
    · simpa [MatrixCertificates.Rank7.E1] using ETypeIII_row1 h 2 he
    · intro q hq
      exact ETypeIII_actualImage h 2 hq
  · refine ⟨ETypeIII h 3, ?_, ?_⟩
    · simpa [MatrixCertificates.Rank7.E1] using ETypeIII_row1 h 3 he
    · intro q hq
      exact ETypeIII_actualImage h 3 hq
  · refine ⟨ETypeII h 0, ?_, ?_⟩
    · simpa [MatrixCertificates.Rank7.E1] using ETypeII_row1 h 0 he
    · intro q hq
      exact ETypeII_actualImage h 0 hq
  · refine ⟨ETypeII h 1, ?_, ?_⟩
    · simpa [MatrixCertificates.Rank7.E1] using ETypeII_row1 h 1 he
    · intro q hq
      exact ETypeII_actualImage h 1 hq
  · refine ⟨ETypeII h 2, ?_, ?_⟩
    · simpa [MatrixCertificates.Rank7.E1] using ETypeII_row1 h 2 he
    · intro q hq
      exact ETypeII_actualImage h 2 hq
  · refine ⟨ETypeII h 3, ?_, ?_⟩
    · simpa [MatrixCertificates.Rank7.E1] using ETypeII_row1 h 3 he
    · intro q hq
      exact ETypeII_actualImage h 3 hq
/-- Each literal moving-prime row is a proved functional on actual point images. -/
theorem Ep_moving_rows0 (he : epsilon h = 1) :
    ∀ row ∈ MatrixCertificates.Rank7.Ep0.drop 6,
      ∃ f : Additive RationalSquareClasses →ₗ[ZMod 2] ZMod 2,
        squareClassCharacterRow f (signedPrimeColumns (primeColumns7Ep h.primes)) =
          Binary.vector 13 row ∧
        ∀ q ∈ twoIsogenyImage (-2 * Rank7.a (M7 x) (N7 y)) (Rank7.c (M7 x) (N7 y)), f (Additive.ofMul q) = 0 := by
  intro row hr
  have hh : row = 5408 ∨ row = 6811 ∨ row = 2388 ∨ row = 6399 ∨ row = 5503 ∨ row = 5914 ∨ row = 5914 ∨ row = 5479 := by
    simpa [MatrixCertificates.Rank7.Ep0] using hr
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨EpTypeIII h 0, ?_, ?_⟩
    · simpa [MatrixCertificates.Rank7.Ep0] using EpTypeIII_row0 h 0 he
    · intro q hq
      exact EpTypeIII_actualImage h 0 hq
  · refine ⟨EpTypeIII h 1, ?_, ?_⟩
    · simpa [MatrixCertificates.Rank7.Ep0] using EpTypeIII_row0 h 1 he
    · intro q hq
      exact EpTypeIII_actualImage h 1 hq
  · refine ⟨EpTypeIII h 2, ?_, ?_⟩
    · simpa [MatrixCertificates.Rank7.Ep0] using EpTypeIII_row0 h 2 he
    · intro q hq
      exact EpTypeIII_actualImage h 2 hq
  · refine ⟨EpTypeIII h 3, ?_, ?_⟩
    · simpa [MatrixCertificates.Rank7.Ep0] using EpTypeIII_row0 h 3 he
    · intro q hq
      exact EpTypeIII_actualImage h 3 hq
  · refine ⟨EpTypeII h 0, ?_, ?_⟩
    · simpa [MatrixCertificates.Rank7.Ep0] using EpTypeII_row0 h 0 he
    · intro q hq
      exact EpTypeII_actualImage h 0 hq
  · refine ⟨EpTypeII h 1, ?_, ?_⟩
    · simpa [MatrixCertificates.Rank7.Ep0] using EpTypeII_row0 h 1 he
    · intro q hq
      exact EpTypeII_actualImage h 1 hq
  · refine ⟨EpTypeII h 2, ?_, ?_⟩
    · simpa [MatrixCertificates.Rank7.Ep0] using EpTypeII_row0 h 2 he
    · intro q hq
      exact EpTypeII_actualImage h 2 hq
  · refine ⟨EpTypeII h 3, ?_, ?_⟩
    · simpa [MatrixCertificates.Rank7.Ep0] using EpTypeII_row0 h 3 he
    · intro q hq
      exact EpTypeII_actualImage h 3 hq
/-- Each literal moving-prime row is a proved functional on actual point images. -/
theorem Ep_moving_rows1 (he : epsilon h = -1) :
    ∀ row ∈ MatrixCertificates.Rank7.Ep1.drop 6,
      ∃ f : Additive RationalSquareClasses →ₗ[ZMod 2] ZMod 2,
        squareClassCharacterRow f (signedPrimeColumns (primeColumns7Ep h.primes)) =
          Binary.vector 13 row ∧
        ∀ q ∈ twoIsogenyImage (-2 * Rank7.a (M7 x) (N7 y)) (Rank7.c (M7 x) (N7 y)), f (Additive.ofMul q) = 0 := by
  intro row hr
  have hh : row = 2752 ∨ row = 1403 ∨ row = 5812 ∨ row = 1823 ∨ row = 2719 ∨ row = 2298 ∨ row = 2298 ∨ row = 2695 := by
    simpa [MatrixCertificates.Rank7.Ep1] using hr
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨EpTypeIII h 0, ?_, ?_⟩
    · simpa [MatrixCertificates.Rank7.Ep1] using EpTypeIII_row1 h 0 he
    · intro q hq
      exact EpTypeIII_actualImage h 0 hq
  · refine ⟨EpTypeIII h 1, ?_, ?_⟩
    · simpa [MatrixCertificates.Rank7.Ep1] using EpTypeIII_row1 h 1 he
    · intro q hq
      exact EpTypeIII_actualImage h 1 hq
  · refine ⟨EpTypeIII h 2, ?_, ?_⟩
    · simpa [MatrixCertificates.Rank7.Ep1] using EpTypeIII_row1 h 2 he
    · intro q hq
      exact EpTypeIII_actualImage h 2 hq
  · refine ⟨EpTypeIII h 3, ?_, ?_⟩
    · simpa [MatrixCertificates.Rank7.Ep1] using EpTypeIII_row1 h 3 he
    · intro q hq
      exact EpTypeIII_actualImage h 3 hq
  · refine ⟨EpTypeII h 0, ?_, ?_⟩
    · simpa [MatrixCertificates.Rank7.Ep1] using EpTypeII_row1 h 0 he
    · intro q hq
      exact EpTypeII_actualImage h 0 hq
  · refine ⟨EpTypeII h 1, ?_, ?_⟩
    · simpa [MatrixCertificates.Rank7.Ep1] using EpTypeII_row1 h 1 he
    · intro q hq
      exact EpTypeII_actualImage h 1 hq
  · refine ⟨EpTypeII h 2, ?_, ?_⟩
    · simpa [MatrixCertificates.Rank7.Ep1] using EpTypeII_row1 h 2 he
    · intro q hq
      exact EpTypeII_actualImage h 2 hq
  · refine ⟨EpTypeII h 3, ?_, ?_⟩
    · simpa [MatrixCertificates.Rank7.Ep1] using EpTypeII_row1 h 3 he
    · intro q hq
      exact EpTypeII_actualImage h 3 hq

end RankCertificates.Rank7CharacterEvaluation
