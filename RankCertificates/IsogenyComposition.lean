module

public import RankCertificates.Isogeny
public import Mathlib.Tactic

@[expose] public section

/-! Coordinate identities for the dual composition and the actual tangent
formula for doubling. Exceptional points are handled by the point-map proofs. -/

namespace RankCertificates.IsogenyComposition

open Isogeny

/-- Nonzero `y` means the forward image has nonzero `x`. -/
theorem phiX_ne_zero_of_y_ne_zero {a b x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : OnCurve a b x y) : phiX a b x ≠ 0 := by
  rw [phiX_square hx h]
  exact pow_ne_zero 2 (div_ne_zero hy hx)

/-- The dual composition's first coordinate is the familiar rational doubling
expression. -/
theorem psi_phi_x_reduced {a b x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : OnCurve a b x y) :
    psiX (phiX a b x) (phiY b x y) = (x ^ 2 - b) ^ 2 / (4 * y ^ 2) := by
  rw [phiX_square hx h]
  unfold psiX phiY
  field_simp [hx, hy]

/-- The same coordinate agrees with the actual tangent formula. -/
theorem psi_phi_x_tangent {a b x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : OnCurve a b x y) :
    psiX (phiX a b x) (phiY b x y) =
      ((3 * x ^ 2 + 2 * a * x + b) / (2 * y)) ^ 2 - a - 2 * x := by
  rw [psi_phi_x_reduced hx hy h]
  unfold OnCurve at h
  field_simp [hy]
  linear_combination 16 * (a + 2 * x) * h

/-- The dual composition's second coordinate agrees with the actual tangent
formula, including the correct sign. -/
theorem psi_phi_y_tangent {a b x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : OnCurve a b x y) :
    psiY a b (phiX a b x) (phiY b x y) =
      ((3 * x ^ 2 + 2 * a * x + b) / (2 * y)) *
        (x - (((3 * x ^ 2 + 2 * a * x + b) / (2 * y)) ^ 2 - a - 2 * x)) - y := by
  rw [phiX_square hx h]
  unfold psiY phiY c
  unfold OnCurve at h
  field_simp [hx, hy]
  linear_combination 8 * ((9 * x ^ 2 - b) * (y ^ 2 + x ^ 3 + a * x ^ 2 + b * x) -
    4 * x ^ 2 * (3 * x ^ 2 + 2 * a * x + b) * (a + 3 * x)) * h

/-- The actual affine tangent slope on the two-torsion model. -/
theorem slope_self (a b x y : ℚ) (hy : y ≠ 0) :
    (twoTorsionModel a b).toAffine.slope x x y y =
      (3 * x ^ 2 + 2 * a * x + b) / (2 * y) := by
  have hyneg : y ≠ (twoTorsionModel a b).toAffine.negY x y := by
    change y ≠ -y - 0 * x - 0
    simp only [zero_mul, sub_zero]
    intro heq
    apply hy
    linarith
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hyneg]
  simp only [twoTorsionModel, WeierstrassCurve.Affine.negY, zero_mul, sub_zero]
  congr 1
  ring

/-- The first composition coordinate is exactly the first coordinate of the
actual point-group doubling formula. -/
theorem psi_phi_x_addX {a b x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : OnCurve a b x y) :
    psiX (phiX a b x) (phiY b x y) =
      (twoTorsionModel a b).toAffine.addX x x
        ((twoTorsionModel a b).toAffine.slope x x y y) := by
  rw [slope_self a b x y hy]
  simp only [WeierstrassCurve.Affine.addX, twoTorsionModel, zero_mul, add_zero]
  convert psi_phi_x_tangent hx hy h using 1
  ring

/-- The second composition coordinate is exactly the second coordinate of
actual point-group doubling. -/
theorem psi_phi_y_addY {a b x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : OnCurve a b x y) :
    psiY a b (phiX a b x) (phiY b x y) =
      (twoTorsionModel a b).toAffine.addY x x y
        ((twoTorsionModel a b).toAffine.slope x x y y) := by
  rw [slope_self a b x y hy]
  simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX,
    twoTorsionModel, zero_mul, sub_zero, add_zero]
  convert psi_phi_y_tangent hx hy h using 1
  ring

end RankCertificates.IsogenyComposition
