module

public import RankCertificates.DualIsogenyHom

/-! The forward map composed with the dual map is doubling on the partner,
including infinity and every rational two-torsion point. -/

@[expose] public section

namespace RankCertificates.Isogeny

theorem phi_psi_x {a b X Y : ℚ} (hX : X ≠ 0) (hY : Y ≠ 0)
    (h : OnCurve (-2*a) (c a b) X Y) :
    phiX a b (psiX X Y)=((3*X^2-4*a*X+c a b)/(2*Y))^2+2*a-2*X := by
  unfold phiX psiX OnCurve c at *
  field_simp [hX,hY]
  linear_combination 4*(Y^2+9*X^3-6*a*X^2+(a^2-4*b)*X)*h

theorem phi_psi_y {a b X Y : ℚ} (hX : X ≠ 0) (hY : Y ≠ 0)
    (h : OnCurve (-2*a) (c a b) X Y) :
    phiY b (psiX X Y) (psiY a b X Y)=
      -((3*X^2-4*a*X+c a b)/(2*Y)*
        (((3*X^2-4*a*X+c a b)/(2*Y))^2+2*a-3*X)+Y) := by
  unfold phiY psiX psiY OnCurve c at *
  field_simp [hX,hY]
  linear_combination 8*(-27*X^5+54*a*X^4-36*a^2*X^3+16*b*X^3+9*X^2*Y^2+
    10*a^3*X^2-40*a*b*X^2-a^4*X+8*a^2*b*X-16*b^2*X-a^2*Y^2+4*b*Y^2)*h

theorem psiX_ne_zero {X Y : ℚ} (hX : X ≠ 0) (hY : Y ≠ 0) : psiX X Y ≠ 0 := by
  unfold psiX
  exact div_ne_zero (pow_ne_zero 2 hY) (mul_ne_zero (by norm_num) (pow_ne_zero 2 hX))

theorem phiPoint_psiPoint (a b : ℚ) (hb : b ≠ 0) (hc : c a b ≠ 0)
    (Q : (twoIsogenousModel a b).toAffine.Point) :
    phiPoint a b hb hc (psiPoint a b hb hc Q)=Q+Q := by
  cases Q with
  | zero => simp [WeierstrassCurve.Affine.Point.zero_def]
  | some X Y h =>
    have he : OnCurve (-2*a) (c a b) X Y :=
      (onCurve_iff_equation (-2*a) (c a b) X Y).mpr h.1
    by_cases hX : X=0
    · subst X
      have hY : Y=0 := by simpa [OnCurve] using he
      subst Y
      rw [WeierstrassCurve.Affine.Point.add_self_of_Y_eq (by
        simp [twoIsogenousModel,twoTorsionModel])]
      simp [phiPoint,psiPoint,WeierstrassCurve.Affine.Point.zero_def]
    · by_cases hY : Y=0
      · subst Y
        rw [WeierstrassCurve.Affine.Point.add_self_of_Y_eq (by
          simp [twoIsogenousModel,twoTorsionModel])]
        simp [phiPoint,psiPoint,hX,psiX,WeierstrassCurve.Affine.Point.zero_def]
      · have hyneg : Y ≠ (twoIsogenousModel a b).toAffine.negY X Y := by
          simp only [twoIsogenousModel,twoTorsionModel,WeierstrassCurve.Affine.negY,
            zero_mul,sub_zero]
          intro hy
          apply hY
          linarith
        have hslope : (twoIsogenousModel a b).toAffine.slope X X Y Y =
            (3*X^2-4*a*X+c a b)/(2*Y) := by
          rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hyneg]
          simp only [twoIsogenousModel,twoTorsionModel,WeierstrassCurve.Affine.negY,
            zero_mul,sub_zero]
          unfold c
          congr 1 <;> ring
        have hxcoord : phiX a b (psiX X Y)=
            (twoIsogenousModel a b).toAffine.addX X X
              ((twoIsogenousModel a b).toAffine.slope X X Y Y) := by
          rw [hslope]
          conv_rhs => simp only [WeierstrassCurve.Affine.addX,twoIsogenousModel,
            twoTorsionModel,zero_mul,add_zero]
          linear_combination phi_psi_x hX hY he
        have hycoord : phiY b (psiX X Y) (psiY a b X Y)=
            (twoIsogenousModel a b).toAffine.addY X X Y
              ((twoIsogenousModel a b).toAffine.slope X X Y Y) := by
          rw [hslope]
          conv_rhs => simp only [WeierstrassCurve.Affine.addY,WeierstrassCurve.Affine.negY,
            WeierstrassCurve.Affine.negAddY,WeierstrassCurve.Affine.addX,
            twoIsogenousModel,twoTorsionModel,zero_mul,add_zero,sub_zero]
          linear_combination phi_psi_y hX hY he
        rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hyneg]
        simp only [psiPoint,dite_eq_right hX,phiPoint,dite_eq_right (psiX_ne_zero hX hY)]
        exact affine_some_eq hxcoord hycoord

theorem phiPointHom_comp_psiPointHom (a b : ℚ) (hb : b ≠ 0) (hc : c a b ≠ 0) :
    (phiPointHom a b hb hc).comp (psiPointHom a b hb hc)=
      nsmulAddMonoidHom (α := (twoIsogenousModel a b).toAffine.Point) 2 := by
  ext Q
  change phiPoint a b hb hc (psiPoint a b hb hc Q)=2 • Q
  rw [two_nsmul]
  exact phiPoint_psiPoint a b hb hc Q

end RankCertificates.Isogeny
