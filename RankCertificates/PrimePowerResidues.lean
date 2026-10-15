module

public import RankCertificates.LocalValuations
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar

/-!
Residues of integral rational numbers modulo prime powers, through the
proved ring homomorphisms on p-adic integers. These support necessary finite
congruence tests for rational points, including the dyadic place.
-/

@[expose] public section

namespace RankCertificates.PrimePowerResidues

open LocalValuations

variable (p : ℕ) [Fact p.Prime]

/-- An integral rational number as a p-adic integer. -/
noncomputable def integralRat (q : ℚ) (hq : 0 ≤ padicValRat p q) : ℤ_[p] :=
  ⟨(q : ℚ_[p]), (Padic.norm_le_one_iff_val_nonneg _).mpr
    (by rwa [Padic.valuation_ratCast])⟩

@[simp] theorem integralRat_coe (q : ℚ) (hq : 0 ≤ padicValRat p q) :
    ((integralRat p q hq : ℤ_[p]) : ℚ_[p]) = (q : ℚ_[p]) := rfl

@[simp] theorem integralRat_zero (hq : 0 ≤ padicValRat p 0) :
    integralRat p 0 hq = 0 := by
  apply Subtype.coe_injective
  simp

@[simp] theorem integralRat_one (hq : 0 ≤ padicValRat p 1) :
    integralRat p 1 hq = 1 := by
  apply Subtype.coe_injective
  simp

theorem integralRat_add {x y : ℚ} (hx : 0 ≤ padicValRat p x)
    (hy : 0 ≤ padicValRat p y) (hxy : 0 ≤ padicValRat p (x + y)) :
    integralRat p (x + y) hxy = integralRat p x hx + integralRat p y hy := by
  apply Subtype.coe_injective
  simp only [integralRat_coe, PadicInt.coe_add, Rat.cast_add]

theorem integralRat_sub {x y : ℚ} (hx : 0 ≤ padicValRat p x)
    (hy : 0 ≤ padicValRat p y) (hxy : 0 ≤ padicValRat p (x - y)) :
    integralRat p (x - y) hxy = integralRat p x hx - integralRat p y hy := by
  apply Subtype.coe_injective
  simp only [integralRat_coe, PadicInt.coe_sub, Rat.cast_sub]

theorem integralRat_mul {x y : ℚ} (hx : 0 ≤ padicValRat p x)
    (hy : 0 ≤ padicValRat p y) (hxy : 0 ≤ padicValRat p (x * y)) :
    integralRat p (x * y) hxy = integralRat p x hx * integralRat p y hy := by
  apply Subtype.coe_injective
  simp only [integralRat_coe, PadicInt.coe_mul, Rat.cast_mul]

theorem integralRat_isUnit {q : ℚ} (hq : q ≠ 0) (hv : padicValRat p q = 0) :
    IsUnit (integralRat p q (by omega)) := by
  apply PadicInt.isUnit_iff.mpr
  rw [PadicInt.norm_def, integralRat_coe, Padic.eq_padicNorm,
    padicNorm.eq_zpow_of_nonzero hq, hv]
  norm_num

/-- Reduction of an integral rational number modulo p^k. -/
noncomputable def residuePow (k : ℕ) (q : ℚ) (hq : 0 ≤ padicValRat p q) : ZMod (p ^ k) :=
  PadicInt.toZModPow k (integralRat p q hq)

@[simp] theorem residuePow_zero (k : ℕ) (hq : 0 ≤ padicValRat p 0) :
    residuePow p k 0 hq = 0 := by simp [residuePow]

@[simp] theorem residuePow_one (k : ℕ) (hq : 0 ≤ padicValRat p 1) :
    residuePow p k 1 hq = 1 := by simp [residuePow]

theorem residuePow_add (k : ℕ) {x y : ℚ} (hx : 0 ≤ padicValRat p x)
    (hy : 0 ≤ padicValRat p y) (hxy : 0 ≤ padicValRat p (x + y)) :
    residuePow p k (x + y) hxy = residuePow p k x hx + residuePow p k y hy := by
  unfold residuePow
  rw [integralRat_add p hx hy hxy, map_add]

theorem residuePow_sub (k : ℕ) {x y : ℚ} (hx : 0 ≤ padicValRat p x)
    (hy : 0 ≤ padicValRat p y) (hxy : 0 ≤ padicValRat p (x - y)) :
    residuePow p k (x - y) hxy = residuePow p k x hx - residuePow p k y hy := by
  unfold residuePow
  rw [integralRat_sub p hx hy hxy, map_sub]

theorem residuePow_mul (k : ℕ) {x y : ℚ} (hx : 0 ≤ padicValRat p x)
    (hy : 0 ≤ padicValRat p y) (hxy : 0 ≤ padicValRat p (x * y)) :
    residuePow p k (x * y) hxy = residuePow p k x hx * residuePow p k y hy := by
  unfold residuePow
  rw [integralRat_mul p hx hy hxy, map_mul]

theorem residuePow_isUnit (k : ℕ) {q : ℚ} (hq : q ≠ 0) (hv : padicValRat p q = 0) :
    IsUnit (residuePow p k q (by omega)) :=
  (integralRat_isUnit p hq hv).map (PadicInt.toZModPow k)

/-- Valuation at least k forces zero residue modulo p^k. -/
theorem residuePow_zero_of_valuation (k : ℕ) {q : ℚ}
    (hq : 0 ≤ padicValRat p q) (hk : (k : ℤ) ≤ padicValRat p q) :
    residuePow p k q hq = 0 := by
  by_cases hz : q = 0
  · subst q
    exact residuePow_zero p k hq
  have hne : integralRat p q hq ≠ 0 := by
    intro he
    have he' := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) he
    exact hz (by simpa using he')
  change integralRat p q hq ∈ RingHom.ker (PadicInt.toZModPow k)
  rw [PadicInt.ker_toZModPow, PadicInt.mem_span_pow_iff_le_valuation _ hne]
  rw [← Nat.cast_le (α := ℤ), ← PadicInt.valuation_coe, integralRat_coe,
    Padic.valuation_ratCast]
  exact hk

theorem normalizedUnit_valuation_nonnegative (q : ℚ) :
    0 ≤ padicValRat p (normalizedUnit p q) := by
  by_cases hq : q = 0
  · subst q
    simp [normalizedUnit]
  · rw [normalizedUnit_valuation_zero p hq]

/-- The exact normalized unit, reduced modulo p^k. -/
noncomputable def unitResiduePow (k : ℕ) (q : ℚ) : ZMod (p ^ k) :=
  residuePow p k (normalizedUnit p q) (normalizedUnit_valuation_nonnegative p q)

@[simp] theorem unitResiduePow_one (k : ℕ) : unitResiduePow p k 1 = 1 := by
  simp [unitResiduePow, normalizedUnit]

theorem unitResiduePow_mul (k : ℕ) {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0) :
    unitResiduePow p k (x * y) = unitResiduePow p k x * unitResiduePow p k y := by
  simp only [unitResiduePow, normalizedUnit_mul p hx hy]
  exact residuePow_mul p k _ _ _

theorem unitResiduePow_isUnit (k : ℕ) {q : ℚ} (hq : q ≠ 0) :
    IsUnit (unitResiduePow p k q) :=
  residuePow_isUnit p k (normalizedUnit_ne_zero p hq) (normalizedUnit_valuation_zero p hq)

/-- Normalized squares are squares in the finite prime-power ring. -/
theorem unitResiduePow_square (k : ℕ) {q : ℚ} (hq : q ≠ 0) :
    IsSquare (unitResiduePow p k (q ^ 2)) := by
  refine ⟨unitResiduePow p k q, ?_⟩
  rw [pow_two, unitResiduePow_mul p k hq hq]

/-- Every odd square is 1 modulo 8. -/
theorem odd_square_mod_eight (u : (ZMod 8)ˣ) : (u : ZMod 8) ^ 2 = 1 := by
  revert u
  decide +kernel

/-- A rational square has normalized dyadic unit 1 modulo 8. -/
theorem unitResiduePow_two_square {q : ℚ} (hq : q ≠ 0) :
    unitResiduePow 2 3 (q ^ 2) = 1 := by
  obtain ⟨u, hu⟩ := unitResiduePow_isUnit 2 3 hq
  rw [pow_two, unitResiduePow_mul 2 3 hq hq, ← hu, ← pow_two]
  exact odd_square_mod_eight u


/-- Precise zero criterion, retaining the valuation convention at zero. -/
theorem residuePow_eq_zero_iff (k : ℕ) {q : ℚ} (hq : 0 ≤ padicValRat p q) :
    residuePow p k q hq = 0 ↔ q = 0 ∨ (k : ℤ) ≤ padicValRat p q := by
  by_cases hz : q = 0
  · subst q
    simp
  have hne : integralRat p q hq ≠ 0 := by
    intro he
    have he' := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) he
    exact hz (by simpa using he')
  change integralRat p q hq ∈ RingHom.ker (PadicInt.toZModPow k) ↔ _
  rw [PadicInt.ker_toZModPow, PadicInt.mem_span_pow_iff_le_valuation _ hne]
  rw [← Nat.cast_le (α := ℤ), ← PadicInt.valuation_coe, integralRat_coe,
    Padic.valuation_ratCast]
  simp only [hz, false_or]

/-- Reduction from precision n to precision m is compatible. -/
theorem residuePow_cast (m n : ℕ) (hmn : m ≤ n) {q : ℚ}
    (hq : 0 ≤ padicValRat p q) :
    ZMod.cast (residuePow p n q hq) = residuePow p m q hq :=
  PadicInt.cast_toZModPow m n hmn _

theorem unitResiduePow_cast (m n : ℕ) (hmn : m ≤ n) (q : ℚ) :
    ZMod.cast (unitResiduePow p n q) = unitResiduePow p m q :=
  residuePow_cast p m n hmn _

/-- Agreement modulo p^k follows from the genuine rational difference. -/
theorem residuePow_eq_of_close (k : ℕ) {x y : ℚ}
    (hx : 0 ≤ padicValRat p x) (hy : 0 ≤ padicValRat p y)
    (hclose : x - y = 0 ∨ (k : ℤ) ≤ padicValRat p (x - y)) :
    residuePow p k x hx = residuePow p k y hy := by
  have hd : 0 ≤ padicValRat p (x - y) := by
    rcases hclose with hz | hv
    · simp [hz]
    · omega
  apply sub_eq_zero.mp
  rw [← residuePow_sub p k hx hy hd]
  exact (residuePow_eq_zero_iff p k hd).mpr hclose

/-- Agreement beyond the unit precision gives equal normalized residues. -/
theorem unitResiduePow_eq_of_close (k : ℕ) {x y : ℚ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hv : padicValRat p x = padicValRat p y)
    (hclose : x - y = 0 ∨ (k : ℤ) + padicValRat p x ≤ padicValRat p (x - y)) :
    unitResiduePow p k x = unitResiduePow p k y := by
  apply residuePow_eq_of_close p k
    (by rw [normalizedUnit_valuation_zero p hx])
    (by rw [normalizedUnit_valuation_zero p hy])
  have he : normalizedUnit p x - normalizedUnit p y =
      (x - y) / (p : ℚ) ^ padicValRat p x := by
    simp only [normalizedUnit, ← hv]
    ring
  rw [he]
  rcases hclose with hz | hc
  · exact Or.inl (by rw [hz, zero_div])
  · by_cases hz : x - y = 0
    · exact Or.inl (by rw [hz, zero_div])
    · right
      rw [padicValRat.div hz (zpow_ne_zero _
        (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)), padicValRat.zpow,
        padicValRat.self (Fact.out : p.Prime).one_lt, mul_one]
      omega

/-- A residue 6 modulo 8 has exact dyadic valuation one. -/
theorem valuation_two_eq_one_of_residue_six {q : ℚ}
    (hq : 0 ≤ padicValRat 2 q) (hr : residuePow 2 3 q hq = 6) :
    padicValRat 2 q = 1 := by
  have hq0 : q ≠ 0 := by
    intro hz
    subst q
    exact (by decide : (0 : ZMod (2 ^ 3)) ≠ 6) (by simpa using hr)
  have h1 : residuePow 2 1 q hq = 0 := by
    rw [← residuePow_cast 2 1 3 (by omega) hq, hr]
    decide
  have h2 : residuePow 2 2 q hq ≠ 0 := by
    rw [← residuePow_cast 2 2 3 (by omega) hq, hr]
    decide
  have hv1 := ((residuePow_eq_zero_iff 2 1 hq).mp h1).resolve_left hq0
  have hv2 : ¬ (2 : ℤ) ≤ padicValRat 2 q := by
    intro hv
    exact h2 ((residuePow_eq_zero_iff 2 2 hq).mpr (Or.inr hv))
  omega


/-- On integers this is the ordinary modular cast. -/
theorem residuePow_int (k : ℕ) (z : ℤ) (hz : 0 ≤ padicValRat p (z : ℚ)) :
    residuePow p k (z : ℚ) hz = (z : ZMod (p ^ k)) := by
  have he : integralRat p (z : ℚ) hz = (z : ℤ_[p]) := by
    apply Subtype.coe_injective
    simp
  simp only [residuePow, he, map_intCast]


/-- The normalized dyadic unit modulo 8 depends only on the genuine
rational squareclass. -/
theorem unitResiduePow_two_same_squareclass {x z : ℚ} (hx : x ≠ 0) (hz : z ≠ 0)
    (hc : rationalSquareClass x = rationalSquareClass z) :
    unitResiduePow 2 3 x = unitResiduePow 2 3 z := by
  have hclass : rationalSquareClass (x * z) = 1 := by
    rw [rationalSquareClass_mul hx hz, hc]
    exact rationalSquareClass_mul_self z
  obtain ⟨s, hs, heq⟩ := (rationalSquareClass_eq_one_iff (mul_ne_zero hx hz)).mp hclass
  have hfactor : x = z * (s / z) ^ 2 := by
    calc
      x = (x * z) / z := by field_simp [hz]
      _ = s ^ 2 / z := by rw [heq]
      _ = z * (s / z) ^ 2 := by field_simp [hz]
  rw [hfactor, unitResiduePow_mul 2 3 hz (pow_ne_zero 2 (div_ne_zero hs hz)),
    unitResiduePow_two_square (div_ne_zero hs hz), mul_one]


theorem unitResiduePow_of_valuation_zero (k : ℕ) {q : ℚ} (hv : padicValRat p q = 0) :
    unitResiduePow p k q = residuePow p k q (by omega) := by
  simp only [unitResiduePow, normalizedUnit, hv, zpow_zero, div_one]

theorem unitResiduePow_int_of_not_dvd (k : ℕ) (z : ℤ) (hz : ¬ (p : ℤ) ∣ z) :
    unitResiduePow p k (z : ℚ) = (z : ZMod (p ^ k)) := by
  have hv : padicValRat p (z : ℚ) = 0 := by
    rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hz]
    rfl
  rw [unitResiduePow_of_valuation_zero p k hv, residuePow_int]

/-- The local prime's normalized unit is exactly one at every precision. -/
theorem unitResiduePow_prime_self (k : ℕ) : unitResiduePow p k (p : ℚ) = 1 := by
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  simp only [unitResiduePow, normalizedUnit, padicValRat.self (Fact.out : p.Prime).one_lt,
    zpow_one, div_self hp0, residuePow_one]

end RankCertificates.PrimePowerResidues
