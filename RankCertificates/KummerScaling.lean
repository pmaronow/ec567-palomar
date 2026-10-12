module

public import RankCertificates.Normalization
public import RankCertificates.TwoIsogenyRank

/-! Admissible coordinate scaling preserves the genuine rational Kummer
squareclasses and hence the actual images, including infinity and torsion. -/

@[expose] public section

namespace RankCertificates.KummerScaling

open Normalization

 theorem rationalSquareClass_mul_square_all (x r : ℚ) (hr : r ≠ 0) :
    rationalSquareClass (x * r ^ 2) = rationalSquareClass x := by
  by_cases hx : x = 0
  · simp [hx]
  · exact rationalSquareClass_mul_square hx hr

 theorem onCurve_scale_down {u a b X Y : ℚ} (hu : u ≠ 0)
    (h : OnCurve (u ^ 2 * a) (u ^ 4 * b) X Y) :
    OnCurve a b (X / u ^ 2) (Y / u ^ 3) := by
  unfold OnCurve at *
  field_simp
  linear_combination h

set_option backward.isDefEq.respectTransparency false in
 theorem twoIsogenyClass_coordinateScale (u a b : ℚ) (hu : u ≠ 0)
    [(model a b).IsElliptic]
    (P : (twoTorsionModel (u ^ 2 * a) (u ^ 4 * b)).toAffine.Point) :
    twoIsogenyClass a b (modelCoordinateScaleEquiv u a b hu P) =
      twoIsogenyClass (u ^ 2 * a) (u ^ 4 * b) P := by
  cases P with
  | zero =>
    change twoIsogenyClass a b (modelCoordinateScaleEquiv u a b hu 0) = 1
    rw [modelCoordinateScaleEquiv_zero]
    rfl
  | some X Y h =>
    have heq : OnCurve (u ^ 2 * a) (u ^ 4 * b) X Y :=
      (onCurve_iff_equation _ _ _ _).mpr h.left
    have heq' := onCurve_scale_down hu heq
    have h' : (model a b).toAffine.Nonsingular (X / u ^ 2) (Y / u ^ 3) :=
      (WeierstrassCurve.Affine.equation_iff_nonsingular).mp
        ((onCurve_iff_equation _ _ _ _).mp heq')
    rw [modelCoordinateScaleEquiv_some u a b hu h h']
    change (if X / u ^ 2 = 0 then rationalSquareClass b else rationalSquareClass (X / u ^ 2)) =
      if X = 0 then rationalSquareClass (u ^ 4 * b) else rationalSquareClass X
    by_cases hx : X = 0
    · simp only [hx, zero_div, ite_true]
      symm
      have hpow : u ^ 4 * b = b * (u ^ 2) ^ 2 := by ring
      rw [hpow]
      exact rationalSquareClass_mul_square_all b (u ^ 2) (pow_ne_zero 2 hu)
    · rw [ite_eq_right hx, ite_eq_right (div_ne_zero hx (pow_ne_zero 2 hu))]
      simpa only [div_eq_mul_inv, inv_pow] using
        rationalSquareClass_mul_square_all X u⁻¹ (inv_ne_zero hu)

set_option backward.isDefEq.respectTransparency false in
/-- Pure square coordinate scaling leaves every actual image class unchanged. -/
 theorem twoIsogenyImage_coordinateScale (u a b : ℚ) (hu : u ≠ 0)
    [(model a b).IsElliptic] :
    twoIsogenyImage (u ^ 2 * a) (u ^ 4 * b) = twoIsogenyImage a b := by
  let e := modelCoordinateScaleEquiv u a b hu
  ext q
  constructor
  · rintro ⟨P, rfl⟩
    exact ⟨e P, twoIsogenyClass_coordinateScale u a b hu P⟩
  · rintro ⟨P, rfl⟩
    obtain ⟨Q, rfl⟩ := e.surjective P
    exact ⟨Q, (twoIsogenyClass_coordinateScale u a b hu Q).symm⟩


/-- Nonsingularity also transports from the scaled model to the base model. -/
theorem model_scale_down_isElliptic (u a b : ℚ)
    [(model (u ^ 2 * a) (u ^ 4 * b)).IsElliptic] : (model a b).IsElliptic := by
  have hΔ : (model (u ^ 2 * a) (u ^ 4 * b)).Δ ≠ 0 :=
    isUnit_iff_ne_zero.mp (model (u ^ 2 * a) (u ^ 4 * b)).isUnit_Δ
  have he : (model (u ^ 2 * a) (u ^ 4 * b)).Δ = u ^ 12 * (model a b).Δ := by
    rw [model_discriminant, model_discriminant]
    ring
  constructor
  apply isUnit_iff_ne_zero.mpr
  intro hz
  exact hΔ (by rw [he, hz, mul_zero])

end RankCertificates.KummerScaling
