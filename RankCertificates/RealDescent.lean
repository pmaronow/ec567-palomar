module

public import RankCertificates.SquareClassSign
public import RankCertificates.Common

/-! The real-place restriction on the actual two-isogeny image. -/

@[expose] public section

namespace RankCertificates.RealDescent

/-- A model with nonpositive quadratic coefficient and positive linear
coefficient has no rational point with negative x-coordinate. -/
theorem coordinate_nonnegative {a b x y : ℚ} (ha : a ≤ 0) (hb : 0 < b)
    (h : OnCurve a b x y) : 0 ≤ x := by
  by_contra hx
  have hx' : x < 0 := lt_of_not_ge hx
  have haq : 0 ≤ a * x := mul_nonneg_of_nonpos_of_nonpos ha hx'.le
  have hquad : 0 < x ^ 2 + a * x + b := by nlinarith [sq_nonneg x]
  have hneg : x * (x ^ 2 + a * x + b) < 0 := mul_neg_of_neg_of_pos hx' hquad
  unfold OnCurve at h
  nlinarith [sq_nonneg y]

/-- Every class in the actual descent image has trivial real sign. -/
theorem twoIsogenyImage_sign_zero {a b : ℚ} (ha : a ≤ 0) (hb : 0 < b)
    {q : RationalSquareClasses} (hq : q ∈ twoIsogenyImage a b) :
    squareClassSign (Additive.ofMul q) = 0 := by
  obtain ⟨P, rfl⟩ := hq
  cases P with
  | zero => exact map_zero squareClassSign
  | some x y h =>
    have he : OnCurve a b x y := (onCurve_iff_equation a b x y).mpr h.1
    by_cases hx : x = 0
    · simpa only [twoIsogenyClass, ite_eq_left hx] using squareClassSign_of_pos hb
    · have hxpos : 0 < x := lt_of_le_of_ne (coordinate_nonnegative ha hb he) (Ne.symm hx)
      simpa only [twoIsogenyClass, ite_eq_right hx] using squareClassSign_of_pos hxpos

end RankCertificates.RealDescent
