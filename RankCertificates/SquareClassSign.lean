module

public import RankCertificates.PrimeSquareParity

/-!
# Sign detects the negative rational squareclass

Rational squares are positive, so the sign of a nonzero rational number
descends to a homomorphism from rational squareclasses to `ZMod 2`.
-/

@[expose] public section

namespace RankCertificates

/-- Negative units have sign parity one and positive units have sign parity
zero. -/
def rationalUnitSign : ℚˣ →* Multiplicative (ZMod 2) where
  toFun u := Multiplicative.ofAdd (if (u : ℚ) < 0 then 1 else 0)
  map_one' := by simp
  map_mul' u v := by
    change (if (u : ℚ) * (v : ℚ) < 0 then (1 : ZMod 2) else 0) =
      (if (u : ℚ) < 0 then 1 else 0) + (if (v : ℚ) < 0 then 1 else 0)
    by_cases hu : (u : ℚ) < 0 <;> by_cases hv : (v : ℚ) < 0
    · have hpos := mul_pos_of_neg_of_neg hu hv
      simp only [hu, hv, not_lt_of_ge hpos.le, ite_false, ite_true]
      symm
      rw [one_add_one_eq_two]
      exact ZMod.natCast_self 2
    · have hvpos : 0 < (v : ℚ) :=
        lt_of_le_of_ne (le_of_not_gt hv) (Ne.symm v.ne_zero)
      simp only [hu, hv, mul_neg_of_neg_of_pos hu hvpos, ite_false, ite_true, add_zero]
    · have hupos : 0 < (u : ℚ) :=
        lt_of_le_of_ne (le_of_not_gt hu) (Ne.symm u.ne_zero)
      simp only [hu, hv, mul_neg_of_pos_of_neg hupos hv, ite_false, ite_true, zero_add]
    · have hupos : 0 < (u : ℚ) :=
        lt_of_le_of_ne (le_of_not_gt hu) (Ne.symm u.ne_zero)
      have hvpos : 0 < (v : ℚ) :=
        lt_of_le_of_ne (le_of_not_gt hv) (Ne.symm v.ne_zero)
      simp only [hu, hv, not_lt_of_ge (mul_pos hupos hvpos).le,
        ite_false, zero_add]

theorem squares_le_rationalUnitSign_ker :
    (powMonoidHom (α := ℚˣ) 2).range ≤ rationalUnitSign.ker := by
  rintro u ⟨v, rfl⟩
  change (if (v : ℚ) ^ 2 < 0 then (1 : ZMod 2) else 0) = 0
  rw [ite_eq_right (not_lt_of_ge (sq_nonneg (v : ℚ)))]

/-- Sign parity on the quotient by rational squares. -/
def rationalSquareClassSign : RationalSquareClasses →* Multiplicative (ZMod 2) :=
  QuotientGroup.lift _ rationalUnitSign squares_le_rationalUnitSign_ker

theorem rationalSquareClassSign_apply {x : ℚ} (hx : x ≠ 0) :
    rationalSquareClassSign (rationalSquareClass x) =
      Multiplicative.ofAdd (if x < 0 then (1 : ZMod 2) else 0) := by
  rw [rationalSquareClass, dite_eq_right hx]
  rfl

/-- Additive sign parity for linear independence arguments. -/
def squareClassSign : Additive RationalSquareClasses →+ ZMod 2 :=
  rationalSquareClassSign.toAdditiveLeft

theorem squareClassSign_apply {x : ℚ} (hx : x ≠ 0) :
    squareClassSign (Additive.ofMul (rationalSquareClass x)) =
      if x < 0 then (1 : ZMod 2) else 0 :=
  rationalSquareClassSign_apply hx

@[simp] theorem squareClassSign_neg_one :
    squareClassSign (Additive.ofMul (rationalSquareClass (-1))) = 1 := by
  rw [squareClassSign_apply (by norm_num)]
  norm_num

theorem squareClassSign_of_pos {x : ℚ} (hx : 0 < x) :
    squareClassSign (Additive.ofMul (rationalSquareClass x)) = 0 := by
  rw [squareClassSign_apply (ne_of_gt hx), ite_eq_right (not_lt_of_ge hx.le)]

@[simp] theorem squareClassSign_prime {p : ℕ} (hp : p.Prime) :
    squareClassSign (Additive.ofMul (rationalSquareClass (p : ℚ))) = 0 :=
  squareClassSign_of_pos (Nat.cast_pos.mpr hp.pos)

end RankCertificates
