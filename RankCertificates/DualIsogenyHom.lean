module

public import RankCertificates.IsogenyHom
public import RankCertificates.Normalization

/-! The dual point map is a genuine group homomorphism. It is the forward
isogeny of the partner followed by the admissible coordinate scaling by two. -/

@[expose] public section

namespace RankCertificates.Isogeny

open WeierstrassCurve

theorem dual_c (a b : ℚ) : c (-2*a) (c a b)=16*b := by unfold c; ring

theorem dualPartner_eq_scaled (a b : ℚ) :
    twoIsogenousModel (-2*a) (c a b)=model ((2:ℚ)^2*a) ((2:ℚ)^4*b) := by
  ext <;> simp [twoIsogenousModel,twoTorsionModel,model,c] <;> ring

theorem original_model_isElliptic {a b : ℚ} (hb : b ≠ 0) (hc : c a b ≠ 0) :
    (model a b).IsElliptic := model_isElliptic hb hc

noncomputable def psiScaleEquiv (a b : ℚ) (hb : b ≠ 0) (hc : c a b ≠ 0) :
    (twoIsogenousModel (-2*a) (c a b)).toAffine.Point ≃+ (twoTorsionModel a b).toAffine.Point := by
  letI : (model a b).IsElliptic := original_model_isElliptic hb hc
  exact (Affine.Point.equivOfEq (dualPartner_eq_scaled a b)).trans
    (Normalization.coefficientScaleEquiv (Units.mk0 2 (by norm_num)) a b)

set_option backward.isDefEq.respectTransparency false in
theorem psiScaleEquiv_some (a b : ℚ) (hb : b ≠ 0) (hc : c a b ≠ 0)
    {X Y : ℚ} (h : (twoIsogenousModel (-2*a) (c a b)).toAffine.Nonsingular X Y)
    (h' : (twoTorsionModel a b).toAffine.Nonsingular (X/4) (Y/8)) :
    psiScaleEquiv a b hb hc (.some X Y h)=.some (X/4) (Y/8) h' := by
  let : (model a b).IsElliptic := original_model_isElliptic hb hc
  unfold psiScaleEquiv
  dsimp only [AddEquiv.trans_apply]
  rw [Affine.Point.equivOfEq_some]
  have hxdiv : (((Units.mk0 2 (by norm_num) : ℚˣ):ℚ)⁻¹^2*X)=X/4 := by
    norm_num
    ring
  have hydiv : (((Units.mk0 2 (by norm_num) : ℚˣ):ℚ)⁻¹^3*Y)=Y/8 := by
    norm_num
    ring
  have h'' : (model a b).toAffine.Nonsingular
      (((Units.mk0 2 (by norm_num) : ℚˣ):ℚ)⁻¹^2*X)
      (((Units.mk0 2 (by norm_num) : ℚˣ):ℚ)⁻¹^3*Y) := by
    rw [hxdiv,hydiv]
    exact h'
  have he := Normalization.coefficientScaleEquiv_some
    (Units.mk0 2 (by norm_num)) a b ((dualPartner_eq_scaled a b) ▸ h) h''
  exact he.trans (affine_some_eq hxdiv hydiv)

theorem dual_phi_coordinates {a b X Y : ℚ} (hX : X ≠ 0)
    (h : OnCurve (-2*a) (c a b) X Y) :
    phiX (-2*a) (c a b) X/4=psiX X Y ∧
    phiY (c a b) X Y/8=psiY a b X Y := by
  constructor
  · unfold phiX psiX OnCurve at *
    field_simp [hX]
    linear_combination -h
  · unfold phiY psiY
    ring

noncomputable def psiScaledHom (a b : ℚ) (hb : b ≠ 0) (hc : c a b ≠ 0) :
    (twoIsogenousModel a b).toAffine.Point →+ (twoTorsionModel a b).toAffine.Point :=
  (psiScaleEquiv a b hb hc).toAddMonoidHom.comp
    (phiPointHom (-2*a) (c a b) hc (by rw [dual_c]; exact mul_ne_zero (by norm_num) hb))

theorem psiScaledHom_apply (a b : ℚ) (hb : b ≠ 0) (hc : c a b ≠ 0)
    (Q : (twoIsogenousModel a b).toAffine.Point) :
    psiScaledHom a b hb hc Q=psiPoint a b hb hc Q := by
  cases Q with
  | zero => exact map_zero _
  | some X Y h =>
    by_cases hX : X=0
    · have hc' : c (-2*a) (c a b) ≠ 0 := by rw [dual_c]; exact mul_ne_zero (by norm_num) hb
      change psiScaleEquiv a b hb hc
        (phiPoint (-2*a) (c a b) hc hc' (.some X Y h))=psiPoint a b hb hc (.some X Y h)
      simp [phiPoint,psiPoint,hX,← Affine.Point.zero_def]
    · have hc' : c (-2*a) (c a b) ≠ 0 := by rw [dual_c]; exact mul_ne_zero (by norm_num) hb
      have he : OnCurve (-2*a) (c a b) X Y :=
        (onCurve_iff_equation (-2*a) (c a b) X Y).mpr h.1
      have hcoord := dual_phi_coordinates hX he
      have hpsi : (twoTorsionModel a b).toAffine.Nonsingular (psiX X Y) (psiY a b X Y) :=
        onCurve_nonsingular (original_discriminant_ne_zero hb hc) (psi_onCurve hX he)
      have hs : (twoTorsionModel a b).toAffine.Nonsingular
          (phiX (-2*a) (c a b) X/4) (phiY (c a b) X Y/8) := by
        rw [hcoord.1,hcoord.2]
        exact hpsi
      change psiScaleEquiv a b hb hc
        (phiPoint (-2*a) (c a b) hc hc' (.some X Y h))=psiPoint a b hb hc (.some X Y h)
      simp only [phiPoint,dite_eq_right hX,psiPoint]
      exact (psiScaleEquiv_some a b hb hc _ hs).trans
        (affine_some_eq hcoord.1 hcoord.2)

/-- The dual map with exactly the previously defined coordinate function. -/
noncomputable def psiPointHom (a b : ℚ) (hb : b ≠ 0) (hc : c a b ≠ 0) :
    (twoIsogenousModel a b).toAffine.Point →+ (twoTorsionModel a b).toAffine.Point where
  toFun := psiPoint a b hb hc
  map_zero' := rfl
  map_add' P Q := by
    rw [← psiScaledHom_apply a b hb hc, ← psiScaledHom_apply a b hb hc,
      ← psiScaledHom_apply a b hb hc]
    exact map_add _ P Q

theorem originalClassHom_kernel (a b : ℚ) (hb : b ≠ 0) (hc : c a b ≠ 0) :
    (twoIsogenyClassAddHom a b hb).ker=(psiPointHom a b hb hc).range := by
  ext P
  change twoIsogenyClass a b P=1 ↔ ∃ Q,psiPoint a b hb hc Q=P
  exact twoIsogenyClass_eq_one_iff_range a b hb hc P

end RankCertificates.Isogeny
