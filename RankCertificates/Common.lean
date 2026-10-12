module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.Tactic

/-! Explicit nonsingular rational Weierstrass equations and point certificates.
No Mordell–Weil rank is defined in this module. -/

@[expose] public section

namespace RankCertificates

/-- A rational affine point on the two-torsion normal form. -/
def OnCurve (a b x y : ℚ) : Prop := y ^ 2 = x ^ 3 + a * x ^ 2 + b * x

/-- The Weierstrass curve with coefficients `(0,a,0,b,0)`. -/
def model (a b : ℚ) : WeierstrassCurve ℚ := ⟨0, a, 0, b, 0⟩

theorem onCurve_of_ratio {a b x r : ℚ} (h : r ^ 2 = x + a + b / x)
    (hx : x ≠ 0) : OnCurve a b x (x * r) := by
  unfold OnCurve
  field_simp at h
  linear_combination x * h

theorem model_discriminant (a b : ℚ) :
    (model a b).Δ = 16 * b ^ 2 * (a ^ 2 - 4 * b) := by
  simp only [model, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem model_c4 (a b : ℚ) : (model a b).c₄ = 16 * (a ^ 2 - 3 * b) := by
  simp only [model, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

theorem model_isElliptic {a b : ℚ} (hb : b ≠ 0) (hc : a ^ 2 - 4 * b ≠ 0) :
    (model a b).IsElliptic := by
  constructor
  rw [isUnit_iff_ne_zero, model_discriminant]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hb)) hc

theorem onCurve_iff_equation (a b x y : ℚ) :
    OnCurve a b x y ↔ (model a b).toAffine.Equation x y := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [OnCurve, model]

theorem onCurve_nonsingular {a b x y : ℚ} (hΔ : (model a b).Δ ≠ 0)
    (h : OnCurve a b x y) : (model a b).toAffine.Nonsingular x y :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp
    ((onCurve_iff_equation a b x y).mp h)

theorem model_j (a b : ℚ) [(model a b).IsElliptic] :
    (model a b).j =
      256 * (a ^ 2 - 3 * b) ^ 3 / (b ^ 2 * (a ^ 2 - 4 * b)) := by
  rw [WeierstrassCurve.j_eq, model_discriminant, model_c4]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end RankCertificates
