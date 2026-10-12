module

public import RankCertificates.Common
public import RankCertificates.LocalDescent
public import Mathlib.Data.Rat.Cast.Lemmas
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# Necessary local restrictions on genuine rational coordinates

The residue map is used only when its rational denominator is a unit at
the indicated prime.  Its properties below are derived from the rational
point equation by clearing denominators; no local-solubility oracle is used.
-/

@[expose] public section

namespace RankCertificates.LocalValuations

def rationalResidue (p : ℕ) [Fact p.Prime] (q : ℚ) : ZMod p :=
  (q.num : ZMod p) / (q.den : ZMod p)

/-- Remove the exact power of the local prime from a rational number. -/
def normalizedUnit (p : ℕ) (q : ℚ) : ℚ := q / (p : ℚ) ^ padicValRat p q

def unitResidue (p : ℕ) [Fact p.Prime] (q : ℚ) : ZMod p :=
  rationalResidue p (normalizedUnit p q)

theorem normalizedUnit_ne_zero (p : ℕ) [Fact p.Prime] {q : ℚ} (hq : q ≠ 0) :
    normalizedUnit p q ≠ 0 := by
  exact div_ne_zero hq (zpow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))

theorem normalizedUnit_valuation_zero (p : ℕ) [Fact p.Prime] {q : ℚ} (hq : q ≠ 0) :
    padicValRat p (normalizedUnit p q) = 0 := by
  simp only [normalizedUnit]
  rw [padicValRat.div hq (zpow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)),
    padicValRat.zpow, padicValRat.self (Fact.out : p.Prime).one_lt, mul_one, sub_self]

theorem num_den_not_both_zero (p : ℕ) [Fact p.Prime] (q : ℚ) :
    (q.num : ZMod p) ≠ 0 ∨ (q.den : ZMod p) ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨u, v, huv⟩ := q.isCoprime_num_den
  have hm := congrArg (Int.castRingHom (ZMod p)) huv
  simp only [Int.coe_castRingHom, Int.cast_add, Int.cast_mul, Int.cast_one, Int.cast_natCast] at hm
  rw [h.1, h.2] at hm
  simp at hm

theorem denominator_unit_of_nonnegative_valuation (p : ℕ) [Fact p.Prime] (q : ℚ)
    (hval : 0 ≤ padicValRat p q) : (q.den : ZMod p) ≠ 0 := by
  intro hd
  have hn : (q.num : ZMod p) ≠ 0 := (num_den_not_both_zero p q).resolve_right (not_not.mpr hd)
  have hvn : padicValInt p q.num = 0 :=
    padicValInt.eq_zero_of_not_dvd (fun h => hn ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h))
  have hvd : padicValNat p q.den ≠ 0 := by
    intro hzero
    rcases padicValNat.eq_zero_iff.mp hzero with hp | hq | hnot
    · exact (Fact.out : p.Prime).ne_one hp
    · exact q.den_ne_zero hq
    · exact hnot ((ZMod.natCast_eq_zero_iff _ _).mp hd)
  simp only [padicValRat_def, hvn, Nat.cast_zero, zero_sub] at hval
  omega

theorem residue_ne_zero_of_valuation_zero (p : ℕ) [Fact p.Prime] {q : ℚ}
    (hq : q ≠ 0) (hval : padicValRat p q = 0) : rationalResidue p q ≠ 0 := by
  have hd := denominator_unit_of_nonnegative_valuation p q (by omega)
  have hvd : padicValNat p q.den = 0 := padicValNat.eq_zero_of_not_dvd
    (fun h => hd ((ZMod.natCast_eq_zero_iff _ _).mpr h))
  have hvn : padicValInt p q.num = 0 := by
    simp only [padicValRat_def, hvd, Nat.cast_zero, sub_zero] at hval
    exact_mod_cast hval
  have hn : (q.num : ZMod p) ≠ 0 := by
    intro hn
    rcases padicValInt.eq_zero_iff.mp hvn with hp | hnum | hnot
    · exact (Fact.out : p.Prime).ne_one hp
    · exact hq (Rat.num_eq_zero.mp hnum)
    · exact hnot ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hn)
  exact div_ne_zero hn hd

theorem residue_zero_of_positive_valuation (p : ℕ) [Fact p.Prime] {q : ℚ}
    (hval : 0 < padicValRat p q) : rationalResidue p q = 0 := by
  have hd := denominator_unit_of_nonnegative_valuation p q (by omega)
  have hvd : padicValNat p q.den = 0 := padicValNat.eq_zero_of_not_dvd
    (fun h => hd ((ZMod.natCast_eq_zero_iff _ _).mpr h))
  have hvn : padicValInt p q.num ≠ 0 := by
    intro hz
    simp only [padicValRat_def, hvd, hz, Nat.cast_zero, sub_zero] at hval
    omega
  have hn : (q.num : ZMod p) = 0 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    by_contra hnot
    exact hvn (padicValInt.eq_zero_of_not_dvd hnot)
  simp only [rationalResidue, hn, zero_div]

theorem rationalResidue_sub (p : ℕ) [Fact p.Prime] {x z : ℚ}
    (hx : (x.den : ZMod p) ≠ 0) (hz : (z.den : ZMod p) ≠ 0) :
    rationalResidue p (x - z) = rationalResidue p x - rationalResidue p z := by
  change ((x - z : ℚ) : ZMod p) = (x : ZMod p) - (z : ZMod p)
  exact Rat.cast_sub_of_ne_zero hx hz

/-- Agreement to precision strictly beyond the common valuation gives the
same normalized residue. -/
theorem unitResidue_eq_of_close (p : ℕ) [Fact p.Prime] {x z : ℚ}
    (hx : x ≠ 0) (hz : z ≠ 0) (hv : padicValRat p x = padicValRat p z)
    (hclose : x - z = 0 ∨ padicValRat p x < padicValRat p (x - z)) :
    unitResidue p x = unitResidue p z := by
  rcases hclose with heq | hclose
  · exact congrArg (unitResidue p) (sub_eq_zero.mp heq)
  by_cases hd : x - z = 0
  · exact congrArg (unitResidue p) (sub_eq_zero.mp hd)
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have heq : normalizedUnit p x - normalizedUnit p z =
      (x - z) / (p : ℚ) ^ padicValRat p x := by
    simp only [normalizedUnit, ← hv]
    ring
  have hdval : 0 < padicValRat p (normalizedUnit p x - normalizedUnit p z) := by
    rw [heq, padicValRat.div hd (zpow_ne_zero _ hp), padicValRat.zpow,
      padicValRat.self (Fact.out : p.Prime).one_lt, mul_one]
    omega
  have hr := residue_zero_of_positive_valuation p hdval
  rw [rationalResidue_sub p
    (denominator_unit_of_nonnegative_valuation p _ (by rw [normalizedUnit_valuation_zero p hx]))
    (denominator_unit_of_nonnegative_valuation p _ (by rw [normalizedUnit_valuation_zero p hz]))] at hr
  exact sub_eq_zero.mp hr

theorem normalizedUnit_mul (p : ℕ) [Fact p.Prime] {x z : ℚ} (hx : x ≠ 0) (hz : z ≠ 0) :
    normalizedUnit p (x * z) = normalizedUnit p x * normalizedUnit p z := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  simp only [normalizedUnit]
  rw [padicValRat.mul hx hz, zpow_add₀ hp]
  ring

theorem rationalResidue_mul (p : ℕ) [Fact p.Prime] {x z : ℚ}
    (hx : (x.den : ZMod p) ≠ 0) (hz : (z.den : ZMod p) ≠ 0) :
    rationalResidue p (x * z) = rationalResidue p x * rationalResidue p z := by
  change ((x * z : ℚ) : ZMod p) = (x : ZMod p) * (z : ZMod p)
  exact Rat.cast_mul_of_ne_zero hx hz

theorem unitResidue_mul (p : ℕ) [Fact p.Prime] {x z : ℚ} (hx : x ≠ 0) (hz : z ≠ 0) :
    unitResidue p (x * z) = unitResidue p x * unitResidue p z := by
  simp only [unitResidue]
  rw [normalizedUnit_mul p hx hz]
  exact rationalResidue_mul p
    (denominator_unit_of_nonnegative_valuation p _ (by rw [normalizedUnit_valuation_zero p hx]))
    (denominator_unit_of_nonnegative_valuation p _ (by rw [normalizedUnit_valuation_zero p hz]))

theorem unitResidue_ne_zero (p : ℕ) [Fact p.Prime] {q : ℚ} (hq : q ≠ 0) :
    unitResidue p q ≠ 0 :=
  residue_ne_zero_of_valuation_zero p (normalizedUnit_ne_zero p hq)
    (normalizedUnit_valuation_zero p hq)

/-- An actual rational square has square normalized residue at every prime. -/
theorem unitResidue_square (p : ℕ) [Fact p.Prime] {x : ℚ} (hx : x ≠ 0) :
    IsSquare (unitResidue p (x ^ 2)) := by
  refine ⟨unitResidue p x, ?_⟩
  rw [pow_two, unitResidue_mul p hx hx]

/-- The p-adic square approximations extracted from genuine points imply
an ordinary finite-field quadratic-residue restriction. -/
theorem squareApproximation_unitResidue_isSquare (p : ℕ) [Fact p.Prime] {x : ℚ}
    (hx : x ≠ 0) (h : LocalDescent.SquareApproximation p x) :
    IsSquare (unitResidue p x) := by
  obtain ⟨r, hr, hclose⟩ := h
  have hrs : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have hv : padicValRat p x = padicValRat p (r ^ 2) := by
    obtain ⟨_, hv⟩ := LocalDescent.add_dominant (p := p) hx
      (u := x) (v := -(x - r ^ 2))
      (hclose.elim (fun hz => Or.inl (by rw [hz, neg_zero]))
        (fun hc => Or.inr (by simpa only [padicValRat.neg] using hc)))
    have heq : x + -(x - r ^ 2) = r ^ 2 := by ring
    rw [heq] at hv
    exact hv.symm
  rw [unitResidue_eq_of_close p hx hrs hv hclose]
  exact unitResidue_square p hr

/-- The quadratic character of the normalized p-adic unit. -/
def unitCharacter (p : ℕ) [Fact p.Prime] (x : ℚ) : ℤ :=
  quadraticChar (ZMod p) (unitResidue p x)

theorem unitCharacter_eq_one_iff (p : ℕ) [Fact p.Prime] {x : ℚ} (hx : x ≠ 0) :
    unitCharacter p x = 1 ↔ IsSquare (unitResidue p x) :=
  quadraticChar_one_iff_isSquare (unitResidue_ne_zero p hx)

theorem unitCharacter_mul (p : ℕ) [Fact p.Prime] {x z : ℚ}
    (hx : x ≠ 0) (hz : z ≠ 0) :
    unitCharacter p (x * z) = unitCharacter p x * unitCharacter p z := by
  simp only [unitCharacter, unitResidue_mul p hx hz, map_mul]

theorem squareApproximation_unitCharacter_eq_one (p : ℕ) [Fact p.Prime] {x : ℚ}
    (hx : x ≠ 0) (h : LocalDescent.SquareApproximation p x) :
    unitCharacter p x = 1 :=
  (unitCharacter_eq_one_iff p hx).mpr (squareApproximation_unitResidue_isSquare p hx h)

theorem rationalResidue_int (p : ℕ) [Fact p.Prime] (x : ℤ) :
    rationalResidue p (x : ℚ) = (x : ZMod p) := by
  change (((x : ℚ) : ZMod p)) = (x : ZMod p)
  exact Rat.cast_intCast x

theorem unitResidue_int_of_not_dvd (p : ℕ) [Fact p.Prime] {x : ℤ}
    (hx : ¬ (p : ℤ) ∣ x) : unitResidue p (x : ℚ) = (x : ZMod p) := by
  have hv : padicValRat p (x : ℚ) = 0 := by
    rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hx]
    rfl
  simp only [unitResidue, normalizedUnit, hv, zpow_zero, div_one, rationalResidue_int]

/-- For an integral unit, the normalized unit character is exactly the
usual Legendre symbol used in the finite descent rows. -/
theorem unitCharacter_int_of_not_dvd (p : ℕ) [Fact p.Prime] {x : ℤ}
    (hx : ¬ (p : ℤ) ∣ x) : unitCharacter p (x : ℚ) = legendreSym p x := by
  simp only [unitCharacter, unitResidue_int_of_not_dvd p hx, legendreSym]

theorem squareApproximation_int_legendre_eq_one (p : ℕ) [Fact p.Prime] {x : ℤ}
    (hx : ¬ (p : ℤ) ∣ x) (h : LocalDescent.SquareApproximation p (x : ℚ)) :
    legendreSym p x = 1 := by
  have hx0 : (x : ℚ) ≠ 0 := by
    exact_mod_cast (show x ≠ 0 from fun hz => hx (hz ▸ dvd_zero _))
  rw [← unitCharacter_int_of_not_dvd p hx]
  exact squareApproximation_unitCharacter_eq_one p hx0 h

/-- The actual two-isogeny image has square normalized unit at type-II primes. -/
theorem twoIsogenyImage_discriminant_prime_unitResidue_square
    (p : ℕ) [Fact p.Prime] {a b : ℚ}
    (hp : p ≠ 2) (ha0 : a ≠ 0) (ha : padicValRat p a = 0)
    (hb0 : b ≠ 0) (hb : padicValRat p b = 0)
    (hd : padicValRat p (a ^ 2 - 4 * b) = 1)
    {q : RationalSquareClasses} (hq : q ∈ twoIsogenyImage a b)
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) :
    IsSquare (unitResidue p z) := by
  apply squareApproximation_unitResidue_isSquare p hz
  exact LocalDescent.twoIsogenyImage_discriminant_prime_square_approximation
    hp ha0 ha hb0 hb hd hq z hz hc

/-- The actual two-isogeny image has the normalized square character of
either 1 or b at a type-III prime. -/
theorem twoIsogenyImage_moving_prime_unitResidue_square
    (p : ℕ) [Fact p.Prime] {a b : ℚ}
    (ha : 1 ≤ padicValRat p a) (hb : padicValRat p b = 1)
    {q : RationalSquareClasses} (hq : q ∈ twoIsogenyImage a b)
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) :
    IsSquare (unitResidue p z) ∨ IsSquare (unitResidue p (b * z)) := by
  have hb0 : b ≠ 0 := by
    intro hz; rw [hz] at hb; simp at hb
  rcases LocalDescent.twoIsogenyImage_moving_prime_square_approximation ha hb hq z hz hc
    with hs | hs
  · exact Or.inl (squareApproximation_unitResidue_isSquare p hz hs)
  · exact Or.inr (squareApproximation_unitResidue_isSquare p (mul_ne_zero hb0 hz) hs)

theorem twoIsogenyImage_discriminant_prime_unitCharacter_eq_one
    (p : ℕ) [Fact p.Prime] {a b : ℚ}
    (hp : p ≠ 2) (ha0 : a ≠ 0) (ha : padicValRat p a = 0)
    (hb0 : b ≠ 0) (hb : padicValRat p b = 0)
    (hd : padicValRat p (a ^ 2 - 4 * b) = 1)
    {q : RationalSquareClasses} (hq : q ∈ twoIsogenyImage a b)
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) :
    unitCharacter p z = 1 := by
  apply (unitCharacter_eq_one_iff p hz).mpr
  exact twoIsogenyImage_discriminant_prime_unitResidue_square p hp ha0 ha hb0 hb hd hq hz hc

/-- A type-II character row applies to every integral unit representative
of the genuine image, with the usual Legendre symbol. -/
theorem twoIsogenyImage_discriminant_prime_legendre_eq_one
    (p : ℕ) [Fact p.Prime] {a b : ℚ}
    (hp : p ≠ 2) (ha0 : a ≠ 0) (ha : padicValRat p a = 0)
    (hb0 : b ≠ 0) (hb : padicValRat p b = 0)
    (hd : padicValRat p (a ^ 2 - 4 * b) = 1)
    {q : RationalSquareClasses} (hq : q ∈ twoIsogenyImage a b)
    {z : ℤ} (hz : ¬ (p : ℤ) ∣ z) (hc : rationalSquareClass (z : ℚ) = q) :
    legendreSym p z = 1 := by
  have hz0 : (z : ℚ) ≠ 0 := by
    exact_mod_cast (show z ≠ 0 from fun hzero => hz (hzero ▸ dvd_zero _))
  rw [← unitCharacter_int_of_not_dvd p hz]
  exact twoIsogenyImage_discriminant_prime_unitCharacter_eq_one
    p hp ha0 ha hb0 hb hd hq hz0 hc

/-- A type-III normalized character row applies to every representative of
the genuine image. -/
theorem twoIsogenyImage_moving_prime_unitCharacter
    (p : ℕ) [Fact p.Prime] {a b : ℚ}
    (ha : 1 ≤ padicValRat p a) (hb : padicValRat p b = 1)
    {q : RationalSquareClasses} (hq : q ∈ twoIsogenyImage a b)
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) :
    unitCharacter p z = 1 ∨ unitCharacter p b * unitCharacter p z = 1 := by
  have hb0 : b ≠ 0 := by
    intro hz; rw [hz] at hb; simp at hb
  rcases twoIsogenyImage_moving_prime_unitResidue_square p ha hb hq hz hc with hs | hs
  · exact Or.inl ((unitCharacter_eq_one_iff p hz).mpr hs)
  · right
    rw [← unitCharacter_mul p hb0 hz]
    exact (unitCharacter_eq_one_iff p (mul_ne_zero hb0 hz)).mpr hs

/-- At a type-III prime the parity of the representative chooses the
necessary normalized character. -/
theorem twoIsogenyImage_moving_prime_unitCharacter_parity
    (p : ℕ) [Fact p.Prime] {a b : ℚ}
    (ha : 1 ≤ padicValRat p a) (hb : padicValRat p b = 1)
    {q : RationalSquareClasses} (hq : q ∈ twoIsogenyImage a b)
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) :
    (Even (padicValRat p z) → unitCharacter p z = 1) ∧
    (Odd (padicValRat p z) → unitCharacter p z = unitCharacter p b) := by
  have hb0 : b ≠ 0 := by
    intro hz; rw [hz] at hb; simp at hb
  have happrox := LocalDescent.twoIsogenyImage_moving_prime_square_approximation ha hb hq z hz hc
  constructor
  · intro he
    rcases happrox with hs | hs
    · exact squareApproximation_unitCharacter_eq_one p hz hs
    · have he' := LocalDescent.square_approximation_even_valuation (mul_ne_zero hb0 hz) hs
      obtain ⟨k, hk⟩ := he
      obtain ⟨l, hl⟩ := he'
      rw [padicValRat.mul hb0 hz, hb] at hl
      omega
  · intro ho
    rcases happrox with hs | hs
    · have he := LocalDescent.square_approximation_even_valuation hz hs
      exact False.elim ((Int.not_even_iff_odd.mpr ho) he)
    · have hmul := squareApproximation_unitCharacter_eq_one p (mul_ne_zero hb0 hz) hs
      rw [unitCharacter_mul p hb0 hz] at hmul
      rcases quadraticChar_dichotomy (unitResidue_ne_zero p hb0) with hplus | hminus
      · change unitCharacter p b = 1 at hplus
        rw [hplus] at hmul ⊢
        simpa only [one_mul] using hmul
      · change unitCharacter p b = -1 at hminus
        rw [hminus] at hmul ⊢
        omega

/-- The same type-III restriction in the exact exponent form used by
binary character rows. -/
theorem twoIsogenyImage_moving_prime_unitCharacter_formula
    (p : ℕ) [Fact p.Prime] {a b : ℚ}
    (ha : 1 ≤ padicValRat p a) (hb : padicValRat p b = 1)
    {q : RationalSquareClasses} (hq : q ∈ twoIsogenyImage a b)
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) :
    unitCharacter p z = unitCharacter p b ^ (padicValRat p z % 2).toNat := by
  have hparity := twoIsogenyImage_moving_prime_unitCharacter_parity p ha hb hq hz hc
  by_cases he : Even (padicValRat p z)
  · have hmod : padicValRat p z % 2 = 0 := by
      obtain ⟨k, hk⟩ := he
      omega
    rw [hmod, Int.toNat_zero, pow_zero]
    exact hparity.1 he
  · have ho := Int.not_even_iff_odd.mp he
    have hmod := Int.odd_iff.mp ho
    rw [hmod, Int.toNat_one, pow_one]
    exact hparity.2 ho

theorem three_unit_square {u : ZMod 3} (hu : u ≠ 0) : u * u = 1 := by
  revert u
  decide

theorem three_unitResidue_square {x : ℚ} (hx : x ≠ 0) : unitResidue 3 (x ^ 2) = 1 := by
  rw [pow_two, unitResidue_mul 3 hx hx]
  exact three_unit_square (unitResidue_ne_zero 3 hx)

/-- The normalized residue condition is a genuine squareclass condition. -/
theorem same_squareclass_unitResidue_three {x z : ℚ} (hx : x ≠ 0) (hz : z ≠ 0)
    (hc : rationalSquareClass x = rationalSquareClass z) : unitResidue 3 x = unitResidue 3 z := by
  have hprod : rationalSquareClass (x * z) = 1 := by
    rw [rationalSquareClass_mul hx hz, hc, rationalSquareClass_mul_self]
  obtain ⟨r, hr, hxr⟩ := (rationalSquareClass_eq_one_iff (mul_ne_zero hx hz)).mp hprod
  have hres : unitResidue 3 x * unitResidue 3 z = 1 := by
    rw [← unitResidue_mul 3 hx hz, hxr, three_unitResidue_square hr]
  have hsq : unitResidue 3 z * unitResidue 3 z = 1 :=
    three_unit_square (unitResidue_ne_zero 3 hz)
  exact mul_right_cancel₀ (unitResidue_ne_zero 3 hz) (hres.trans hsq.symm)

theorem onCurve_cleared (a b : ℤ) {x y : ℚ}
    (h : OnCurve (a : ℚ) (b : ℚ) x y) :
    y.num ^ 2 * (x.den : ℤ) ^ 3 =
      (y.den : ℤ) ^ 2 * (x.num ^ 3 + a * x.num ^ 2 * x.den + b * x.num * (x.den : ℤ) ^ 2) := by
  have hq : (y.num : ℚ) ^ 2 * (x.den : ℚ) ^ 3 =
      (y.den : ℚ) ^ 2 * ((x.num : ℚ) ^ 3 + a * (x.num : ℚ) ^ 2 * x.den +
        b * x.num * (x.den : ℚ) ^ 2) := by
    simp only [OnCurve] at h
    rw [← x.num_div_den, ← y.num_div_den] at h
    field_simp at h
    linear_combination h
  exact_mod_cast hq

theorem onCurve_residue_denominator_unit (p : ℕ) [Fact p.Prime]
    (a b : ℤ) {x y : ℚ} (h : OnCurve (a : ℚ) (b : ℚ) x y)
    (hx : (x.den : ZMod p) ≠ 0) : (y.den : ZMod p) ≠ 0 := by
  intro hy
  have hm := congrArg (Int.castRingHom (ZMod p)) (onCurve_cleared a b h)
  simp only [Int.coe_castRingHom, Int.cast_mul, Int.cast_pow, Int.cast_add, Int.cast_natCast] at hm
  have hyn : (y.num : ZMod p) = 0 := by
    rw [hy, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul] at hm
    exact pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0) |>.mp
      ((mul_eq_zero.mp hm).resolve_right (pow_ne_zero 3 hx))
  exact (num_den_not_both_zero p y).elim (fun hn => hn hyn) (fun hd => hd hy)

theorem onCurve_residue (p : ℕ) [Fact p.Prime] (a b : ℤ) {x y : ℚ}
    (h : OnCurve (a : ℚ) (b : ℚ) x y) (hx : (x.den : ZMod p) ≠ 0) :
    (rationalResidue p y) ^ 2 = (rationalResidue p x) ^ 3 +
      (a : ZMod p) * (rationalResidue p x) ^ 2 + (b : ZMod p) * rationalResidue p x := by
  have hy := onCurve_residue_denominator_unit p a b h hx
  have hm := congrArg (Int.castRingHom (ZMod p)) (onCurve_cleared a b h)
  simp only [Int.coe_castRingHom, Int.cast_mul, Int.cast_pow, Int.cast_add, Int.cast_natCast] at hm
  simp only [rationalResidue]
  field_simp
  linear_combination hm

theorem cubic_cleared (c a b : ℤ) {x y : ℚ}
    (h : y ^ 2 = (c : ℚ) * x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x) :
    y.num ^ 2 * (x.den : ℤ) ^ 3 =
      (y.den : ℤ) ^ 2 * (c * x.num ^ 3 + a * x.num ^ 2 * x.den + b * x.num * (x.den : ℤ) ^ 2) := by
  have hq : (y.num : ℚ) ^ 2 * (x.den : ℚ) ^ 3 =
      (y.den : ℚ) ^ 2 * (c * (x.num : ℚ) ^ 3 + a * (x.num : ℚ) ^ 2 * x.den +
        b * x.num * (x.den : ℚ) ^ 2) := by
    rw [← x.num_div_den, ← y.num_div_den] at h
    field_simp at h
    linear_combination h
  exact_mod_cast hq

theorem cubic_residue_denominator_unit (p : ℕ) [Fact p.Prime]
    (c a b : ℤ) {x y : ℚ}
    (h : y ^ 2 = (c : ℚ) * x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x)
    (hx : (x.den : ZMod p) ≠ 0) : (y.den : ZMod p) ≠ 0 := by
  intro hy
  have hm := congrArg (Int.castRingHom (ZMod p)) (cubic_cleared c a b h)
  simp only [Int.coe_castRingHom, Int.cast_mul, Int.cast_pow, Int.cast_add, Int.cast_natCast] at hm
  have hyn : (y.num : ZMod p) = 0 := by
    rw [hy, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul] at hm
    exact pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0) |>.mp
      ((mul_eq_zero.mp hm).resolve_right (pow_ne_zero 3 hx))
  exact (num_den_not_both_zero p y).elim (fun hn => hn hyn) (fun hd => hd hy)

theorem cubic_residue (p : ℕ) [Fact p.Prime] (c a b : ℤ) {x y : ℚ}
    (h : y ^ 2 = (c : ℚ) * x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x)
    (hx : (x.den : ZMod p) ≠ 0) :
    (rationalResidue p y) ^ 2 = (c : ZMod p) * (rationalResidue p x) ^ 3 +
      (a : ZMod p) * (rationalResidue p x) ^ 2 + (b : ZMod p) * rationalResidue p x := by
  have hy := cubic_residue_denominator_unit p c a b h hx
  have hm := congrArg (Int.castRingHom (ZMod p)) (cubic_cleared c a b h)
  simp only [Int.coe_castRingHom, Int.cast_mul, Int.cast_pow, Int.cast_add, Int.cast_natCast] at hm
  simp only [rationalResidue]
  field_simp
  linear_combination hm

theorem scale_point_equation (a b s : ℤ) {x y : ℚ} (h : OnCurve (a : ℚ) (b : ℚ) x y) :
    OnCurve ((a * s ^ 2 : ℤ) : ℚ) ((b * s ^ 4 : ℤ) : ℚ)
      ((s : ℚ) ^ 2 * x) ((s : ℚ) ^ 3 * y) := by
  simp only [OnCurve, Int.cast_mul, Int.cast_pow] at h ⊢
  linear_combination (s : ℚ) ^ 6 * h

theorem divide_point_equation (a b s : ℤ) (hs : s ≠ 0) {x y : ℚ}
    (h : OnCurve (a : ℚ) (b : ℚ) x y) :
    (y / (s : ℚ)) ^ 2 = ((s ^ 4 : ℤ) : ℚ) * (x / (s : ℚ) ^ 2) ^ 3 +
      ((a * s ^ 2 : ℤ) : ℚ) * (x / (s : ℚ) ^ 2) ^ 2 + (b : ℚ) * (x / (s : ℚ) ^ 2) := by
  have hs' : (s : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hs
  simp only [OnCurve] at h
  simp only [Int.cast_mul, Int.cast_pow]
  field_simp
  linear_combination h

theorem three_residue_point {x y : ZMod 3}
    (h : y ^ 2 = x ^ 3 + x ^ 2 + x) (hx : x ≠ 0) : x = 1 := by
  revert x y
  decide

theorem three_cube_residue {x y : ZMod 3} (h : y ^ 2 = x ^ 3) (hx : x ≠ 0) : x = 1 := by
  revert x y
  decide

theorem three_square_residue {x y : ZMod 3} (h : y ^ 2 = x) (hx : x ≠ 0) : x = 1 := by
  revert x y
  decide

/-- Every rational point integral and nonzero at 3 has square unit residue
on an integral model whose two coefficients are both 1 modulo 3. -/
theorem three_unit_coordinate_residue (a b : ℤ) {x y : ℚ}
    (ha : (a : ZMod 3) = 1) (hb : (b : ZMod 3) = 1)
    (h : OnCurve (a : ℚ) (b : ℚ) x y)
    (hxden : (x.den : ZMod 3) ≠ 0) (hx : rationalResidue 3 x ≠ 0) :
    rationalResidue 3 x = 1 := by
  apply three_residue_point (y := rationalResidue 3 y) _ hx
  simpa only [ha, hb, one_mul] using onCurve_residue 3 a b h hxden

theorem three_scaled_negative_residue (a b : ℤ) {x y : ℚ} (n : ℕ) (hn : 0 < n)
    (hx : x ≠ 0) (hv : padicValRat 3 x = -2 * (n : ℤ))
    (h : OnCurve (a : ℚ) (b : ℚ) x y) :
    rationalResidue 3 (((3 : ℚ) ^ n) ^ 2 * x) = 1 := by
  have hs : (3 : ℚ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  have hsv : padicValRat 3 ((3 : ℚ) ^ n) = n := by
    have hthree : padicValRat 3 (3 : ℚ) = 1 := by
      simpa only [Nat.cast_ofNat] using padicValRat.self (p := 3) (by decide : 1 < 3)
    rw [padicValRat.pow, hthree, mul_one]
  have hxv : padicValRat 3 (((3 : ℚ) ^ n) ^ 2 * x) = 0 := by
    rw [padicValRat.mul (pow_ne_zero 2 hs) hx, padicValRat.pow, hsv, hv]
    omega
  have hxden := denominator_unit_of_nonnegative_valuation 3
    (((3 : ℚ) ^ n) ^ 2 * x) (by omega)
  have hxres := residue_ne_zero_of_valuation_zero 3 (mul_ne_zero (pow_ne_zero 2 hs) hx) hxv
  have hs3 : (((3 : ℤ) ^ n : ℤ) : ZMod 3) = 0 := by
    simp only [Int.cast_pow, Int.cast_ofNat]
    rw [show (3 : ZMod 3) = 0 by decide, zero_pow (by omega : n ≠ 0)]
  have ha' : ((a * ((3 : ℤ) ^ n) ^ 2 : ℤ) : ZMod 3) = 0 := by simp [hs3]
  have hb' : ((b * ((3 : ℤ) ^ n) ^ 4 : ℤ) : ZMod 3) = 0 := by simp [hs3]
  have hr := onCurve_residue 3 (a * ((3 : ℤ) ^ n) ^ 2) (b * ((3 : ℤ) ^ n) ^ 4)
    (scale_point_equation a b ((3 : ℤ) ^ n) h)
    (by simpa only [Int.cast_pow, Int.cast_ofNat] using hxden)
  have hc := three_cube_residue (y := rationalResidue 3 (((3 : ℚ) ^ n) ^ 3 * y))
    (by simpa only [ha', hb', zero_mul, add_zero, Int.cast_pow, Int.cast_ofNat] using hr) hxres
  simpa only [Int.cast_pow, Int.cast_ofNat] using hc

theorem three_scaled_positive_residue (a b : ℤ) {x y : ℚ} (n : ℕ) (hn : 0 < n)
    (hb : (b : ZMod 3) = 1) (hx : x ≠ 0) (hv : padicValRat 3 x = 2 * (n : ℤ))
    (h : OnCurve (a : ℚ) (b : ℚ) x y) :
    rationalResidue 3 (x / ((3 : ℚ) ^ n) ^ 2) = 1 := by
  have hs0 : (3 : ℤ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  have hs : (3 : ℚ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  have hsv : padicValRat 3 ((3 : ℚ) ^ n) = n := by
    have hthree : padicValRat 3 (3 : ℚ) = 1 := by
      simpa only [Nat.cast_ofNat] using padicValRat.self (p := 3) (by decide : 1 < 3)
    rw [padicValRat.pow, hthree, mul_one]
  have hxv : padicValRat 3 (x / ((3 : ℚ) ^ n) ^ 2) = 0 := by
    rw [padicValRat.div hx (pow_ne_zero 2 hs), padicValRat.pow, hsv, hv]
    omega
  have hxden := denominator_unit_of_nonnegative_valuation 3
    (x / ((3 : ℚ) ^ n) ^ 2) (by omega)
  have hxres := residue_ne_zero_of_valuation_zero 3 (div_ne_zero hx (pow_ne_zero 2 hs)) hxv
  have hs3 : (((3 : ℤ) ^ n : ℤ) : ZMod 3) = 0 := by
    simp only [Int.cast_pow, Int.cast_ofNat]
    rw [show (3 : ZMod 3) = 0 by decide, zero_pow (by omega : n ≠ 0)]
  have ha' : ((a * ((3 : ℤ) ^ n) ^ 2 : ℤ) : ZMod 3) = 0 := by simp [hs3]
  have hc' : ((((3 : ℤ) ^ n) ^ 4 : ℤ) : ZMod 3) = 0 := by simp [hs3]
  have hr := cubic_residue 3 (((3 : ℤ) ^ n) ^ 4) (a * ((3 : ℤ) ^ n) ^ 2) b
    (divide_point_equation a b ((3 : ℤ) ^ n) hs0 h)
    (by simpa only [Int.cast_pow, Int.cast_ofNat] using hxden)
  have hc := three_square_residue (y := rationalResidue 3 (y / ((3 : ℚ) ^ n)))
    (by simpa only [hc', ha', hb, zero_mul, zero_add, one_mul, Int.cast_pow, Int.cast_ofNat] using hr) hxres
  simpa only [Int.cast_pow, Int.cast_ofNat] using hc

/-- The complete necessary local restriction at 3 for nonzero coordinates:
the valuation is even and the normalized unit has square residue. -/
theorem three_coordinate_localConditions (a b : ℤ) {x y : ℚ}
    (ha : (a : ZMod 3) = 1) (hb : (b : ZMod 3) = 1)
    (hx : x ≠ 0) (h : OnCurve (a : ℚ) (b : ℚ) x y) :
    Even (padicValRat 3 x) ∧ unitResidue 3 x = 1 := by
  have hbnot : ¬ (3 : ℤ) ∣ b := by
    intro hdiv
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd b 3).mpr hdiv
    rw [hb] at hz
    exact one_ne_zero hz
  have he := LocalDescent.integral_x_valuation_even (p := 3) a b hbnot hx h
  refine ⟨he, ?_⟩
  simp only [unitResidue, normalizedUnit, Nat.cast_ofNat]
  rcases lt_trichotomy (padicValRat 3 x) 0 with hneg | hz | hpos
  · obtain ⟨k, hk⟩ := he
    have hkneg : k < 0 := by omega
    let n : ℕ := (-k).toNat
    have hncast : (n : ℤ) = -k := by
      dsimp [n]
      exact Int.toNat_of_nonneg (by omega)
    have hn : 0 < n := by omega
    have hv : padicValRat 3 x = -2 * (n : ℤ) := by omega
    have heq : x / (3 : ℚ) ^ padicValRat 3 x = ((3 : ℚ) ^ n) ^ 2 * x := by
      rw [hv, show (-2 * (n : ℤ)) = -((n * 2 : ℕ) : ℤ) by omega,
        zpow_neg, zpow_natCast, div_inv_eq_mul, pow_mul]
      ring
    rw [heq]
    exact three_scaled_negative_residue a b n hn hx hv h
  · simp only [hz, zpow_zero, div_one]
    exact three_unit_coordinate_residue a b ha hb h
      (denominator_unit_of_nonnegative_valuation 3 x (by omega))
      (residue_ne_zero_of_valuation_zero 3 hx hz)
  · obtain ⟨k, hk⟩ := he
    have hkpos : 0 < k := by omega
    let n : ℕ := k.toNat
    have hncast : (n : ℤ) = k := by
      dsimp [n]
      exact Int.toNat_of_nonneg (by omega)
    have hn : 0 < n := by omega
    have hv : padicValRat 3 x = 2 * (n : ℤ) := by omega
    have heq : x / (3 : ℚ) ^ padicValRat 3 x = x / ((3 : ℚ) ^ n) ^ 2 := by
      rw [hv, show (2 * (n : ℤ)) = (n : ℤ) * 2 by ring]
      simp only [zpow_mul, zpow_natCast]
      rfl
    rw [heq]
    exact three_scaled_positive_residue a b n hn hb hx hv h

/-- Every representative of every actual two-isogeny image satisfies the
fixed-prime restriction at 3. This includes the identity and the point `(0,0)`. -/
theorem twoIsogenyImage_three_localConditions (a b : ℤ)
    (ha : (a : ZMod 3) = 1) (hb : (b : ZMod 3) = 1)
    {q : RationalSquareClasses} (hq : q ∈ twoIsogenyImage (a : ℚ) (b : ℚ))
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) :
    Even (padicValRat 3 z) ∧ unitResidue 3 z = 1 := by
  have hbnot : ¬ (3 : ℤ) ∣ b := by
    intro hdiv
    have hzero := (ZMod.intCast_zmod_eq_zero_iff_dvd b 3).mpr hdiv
    rw [hb] at hzero
    exact one_ne_zero hzero
  refine ⟨LocalDescent.twoIsogenyImage_even_valuation a b hbnot hq z hz hc, ?_⟩
  obtain ⟨P, rfl⟩ := hq
  cases P with
  | zero =>
    have hc1 : rationalSquareClass z = rationalSquareClass 1 := by
      exact hc.trans rationalSquareClass_one.symm
    rw [same_squareclass_unitResidue_three hz one_ne_zero hc1]
    simp [unitResidue, normalizedUnit, rationalResidue]
  | some x y hP =>
    by_cases hx : x = 0
    · simp only [twoIsogenyClass, hx, ite_true] at hc
      have hb0 : (b : ℚ) ≠ 0 := by
        exact_mod_cast (show b ≠ 0 from fun hzero => hbnot (hzero ▸ dvd_zero _))
      rw [same_squareclass_unitResidue_three hz hb0 hc]
      have hbval : padicValRat 3 (b : ℚ) = 0 := by
        rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hbnot]
        rfl
      simp only [unitResidue, normalizedUnit, hbval, zpow_zero, div_one]
      change (((b : ℚ) : ZMod 3)) = 1
      rw [Rat.cast_intCast, hb]
    · simp only [twoIsogenyClass, hx, ite_false] at hc
      rw [same_squareclass_unitResidue_three hz hx hc]
      exact (three_coordinate_localConditions a b ha hb hx
        ((onCurve_iff_equation _ _ _ _).mpr hP.1)).2

/-- Positive representatives remain positive under equality of genuine
rational squareclasses. -/
theorem same_squareclass_positive {x z : ℚ} (hx : x ≠ 0) (hz : 0 < z)
    (hc : rationalSquareClass x = rationalSquareClass z) : 0 < x := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hprod : rationalSquareClass (x * z) = 1 := by
    rw [rationalSquareClass_mul hx hz0, hc, rationalSquareClass_mul_self]
  obtain ⟨r, hr, heq⟩ := (rationalSquareClass_eq_one_iff (mul_ne_zero hx hz0)).mp hprod
  have hpos : 0 < x * z := by rw [heq]; exact sq_pos_of_ne_zero hr
  exact (mul_pos_iff_of_pos_right hz).mp hpos

/-- With a nonpositive quadratic coefficient and a positive linear
coefficient, a genuine nonzero x coordinate must be positive. -/
theorem onCurve_coordinate_positive {a b x y : ℚ}
    (ha : a ≤ 0) (hb : 0 < b) (hx : x ≠ 0) (h : OnCurve a b x y) : 0 < x := by
  by_contra hpos
  have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hx
  have h3 : x ^ 3 < 0 := by
    rw [show (3 : ℕ) = 2 + 1 by rfl, pow_succ]
    exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hx) hxneg
  have h2 : a * x ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha (sq_nonneg x)
  have h1 : b * x < 0 := mul_neg_of_pos_of_neg hb hxneg
  have hy := sq_nonneg y
  dsimp [OnCurve] at h
  linarith

/-- The real-place positivity row holds for every representative of every
genuine image class, including both exceptional classes. -/
theorem twoIsogenyImage_positive {a b : ℚ} (ha : a ≤ 0) (hb : 0 < b)
    {q : RationalSquareClasses} (hq : q ∈ twoIsogenyImage a b)
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) : 0 < z := by
  obtain ⟨P, rfl⟩ := hq
  cases P with
  | zero =>
    apply same_squareclass_positive hz (by norm_num : (0 : ℚ) < 1)
    exact hc.trans rationalSquareClass_one.symm
  | some x y hP =>
    by_cases hx : x = 0
    · simp only [twoIsogenyClass, hx, ite_true] at hc
      exact same_squareclass_positive hz hb hc
    · simp only [twoIsogenyClass, hx, ite_false] at hc
      exact same_squareclass_positive hz
        (onCurve_coordinate_positive ha hb hx ((onCurve_iff_equation _ _ _ _).mpr hP.1)) hc

end RankCertificates.LocalValuations
