module

public import RankCertificates.Kummer
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# Prime valuations detect rational squareclasses

The genuine rational `p`-adic valuation, reduced modulo two, descends to
the group of rational squareclasses.  Distinct prime factors are detected
individually, without any assumptions about elliptic curve descent.
-/

@[expose] public section

namespace RankCertificates

/-- A rational square has even valuation at every natural prime. -/
theorem padicValRat_square_even {p : ℕ} (hp : p.Prime) (r : ℚ) :
    Even (padicValRat p (r ^ 2)) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [padicValRat.pow]
  exact ⟨padicValRat p r, by ring⟩

/-- The valuation of one prime at a distinct prime is zero. -/
theorem padicValRat_prime_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) : padicValRat p (q : ℚ) = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  simp only [padicValRat.of_nat, padicValNat_primes hpq, Nat.cast_zero]

/-- The valuation of a finite product of nonzero rationals is the sum
of their valuations. -/
theorem padicValRat_finset_prod {ι : Type*} {p : ℕ} (hp : p.Prime)
    (s : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValRat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat p (f i) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi,
        padicValRat.mul (hf i (Finset.mem_insert_self i s))]
      · rw [ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]
      · exact Finset.prod_ne_zero_iff.mpr (fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- Each exponent in a product of powers of distinct primes is exactly
the corresponding prime valuation. -/
theorem padicValRat_primeProduct {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → ℕ) (hP : ∀ i, (P i).Prime) (hPinj : Function.Injective P)
    (e : ι → ℕ) (j : ι) :
    padicValRat (P j) (∏ i, (P i : ℚ) ^ e i) = (e j : ℤ) := by
  have : Fact (P j).Prime := ⟨hP j⟩
  rw [padicValRat_finset_prod (hP j) Finset.univ _
    (fun i _ => pow_ne_zero _ (Nat.cast_ne_zero.mpr (hP i).ne_zero))]
  rw [Finset.sum_eq_single j]
  · rw [padicValRat.pow, padicValRat.self (hP j).one_lt, mul_one]
  · intro i _ hij
    rw [padicValRat.pow, padicValRat_prime_ne (hP j) (hP i)
      (fun h => hij (hPinj h.symm)), mul_zero]
  · simp

/-- The valuation parity homomorphism on nonzero rational numbers. -/
def rationalUnitValuationParity (p : ℕ) (hp : p.Prime) :
    ℚˣ →* Multiplicative (ZMod 2) where
  toFun u := Multiplicative.ofAdd (padicValRat p (u : ℚ) : ZMod 2)
  map_one' := by simp
  map_mul' u v := by
    have : Fact p.Prime := ⟨hp⟩
    change (padicValRat p ((u : ℚ) * (v : ℚ)) : ZMod 2) =
      (padicValRat p (u : ℚ) : ZMod 2) + (padicValRat p (v : ℚ) : ZMod 2)
    rw [padicValRat.mul u.ne_zero v.ne_zero, Int.cast_add]

theorem squares_le_rationalUnitValuationParity_ker (p : ℕ) (hp : p.Prime) :
    (powMonoidHom (α := ℚˣ) 2).range ≤ (rationalUnitValuationParity p hp).ker := by
  rintro u ⟨v, rfl⟩
  have : Fact p.Prime := ⟨hp⟩
  change (padicValRat p ((v : ℚ) ^ 2) : ZMod 2) = 0
  rw [padicValRat.pow]
  rw [Int.cast_mul]
  change (2 : ZMod 2) * (padicValRat p (v : ℚ) : ZMod 2) = 0
  rw [show (2 : ZMod 2) = 0 from ZMod.natCast_self 2, zero_mul]

/-- Reduction of the prime valuation modulo two, on actual rational
squareclasses. -/
def rationalSquareClassValuationParity (p : ℕ) (hp : p.Prime) :
    RationalSquareClasses →* Multiplicative (ZMod 2) :=
  QuotientGroup.lift _ (rationalUnitValuationParity p hp)
    (squares_le_rationalUnitValuationParity_ker p hp)

/-- Evaluating the squareclass parity homomorphism on a nonzero rational. -/
theorem rationalSquareClassValuationParity_apply {p : ℕ} (hp : p.Prime)
    {x : ℚ} (hx : x ≠ 0) :
    rationalSquareClassValuationParity p hp (rationalSquareClass x) =
      Multiplicative.ofAdd (padicValRat p x : ZMod 2) := by
  rw [rationalSquareClass, dite_eq_right hx]
  rfl

/-- Equality of nonzero rational squareclasses implies equality of
valuation parities. -/
theorem rationalSquareClass_eq_parity {p : ℕ} (hp : p.Prime)
    {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : rationalSquareClass x = rationalSquareClass y) :
    (padicValRat p x : ZMod 2) = (padicValRat p y : ZMod 2) := by
  have h' := congrArg (rationalSquareClassValuationParity p hp) h
  rw [rationalSquareClassValuationParity_apply hp hx,
    rationalSquareClassValuationParity_apply hp hy] at h'
  exact h'

/-- The additive version used to test independence over `ZMod 2`. -/
def primeParity (p : ℕ) (hp : p.Prime) : Additive RationalSquareClasses →+ ZMod 2 :=
  (rationalSquareClassValuationParity p hp).toAdditiveLeft

theorem primeParity_apply {p : ℕ} (hp : p.Prime) {x : ℚ} (hx : x ≠ 0) :
    primeParity p hp (Additive.ofMul (rationalSquareClass x)) =
      (padicValRat p x : ZMod 2) :=
  rationalSquareClassValuationParity_apply hp hx

/-- Prime parity separates distinct prime squareclasses. -/
theorem primeParity_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    primeParity p hp (Additive.ofMul (rationalSquareClass (q : ℚ))) =
      if p = q then 1 else 0 := by
  rw [primeParity_apply hp (Nat.cast_ne_zero.mpr hq.ne_zero)]
  split_ifs with h
  · subst q
    rw [padicValRat.self hp.one_lt]
    simp
  · rw [padicValRat_prime_ne hp hq h]
    simp

/-- The sign squareclass has zero prime valuation parity. -/
@[simp] theorem primeParity_neg_one {p : ℕ} (hp : p.Prime) :
    primeParity p hp (Additive.ofMul (rationalSquareClass (-1))) = 0 := by
  rw [primeParity_apply hp (by norm_num)]
  simp

/-- Prime parity reads a binary exponent in a finite prime product. -/
theorem primeParity_primeProduct {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → ℕ) (hP : ∀ i, (P i).Prime) (hPinj : Function.Injective P)
    (e : ι → ZMod 2) (j : ι) :
    primeParity (P j) (hP j)
      (Additive.ofMul (rationalSquareClass (∏ i, (P i : ℚ) ^ (e i).val))) = e j := by
  rw [primeParity_apply (hP j) (Finset.prod_ne_zero_iff.mpr
    (fun i _ => pow_ne_zero _ (Nat.cast_ne_zero.mpr (hP i).ne_zero))),
    padicValRat_primeProduct P hP hPinj (fun i => (e i).val) j]
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]

/-- Finite binary exponent vectors give distinct rational squareclasses
when their prime bases are distinct. -/
theorem rationalSquareClass_primeProduct_injective {ι : Type*}
    [Fintype ι] [DecidableEq ι] (P : ι → ℕ) (hP : ∀ i, (P i).Prime)
    (hPinj : Function.Injective P) :
    Function.Injective (fun e : ι → ZMod 2 =>
      rationalSquareClass (∏ i, (P i : ℚ) ^ (e i).val)) := by
  intro e f h
  funext j
  have h' := congrArg (fun c => primeParity (P j) (hP j) (Additive.ofMul c)) h
  simpa only [primeParity_primeProduct P hP hPinj] using h'

end RankCertificates
