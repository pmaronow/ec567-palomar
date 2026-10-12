module

public import RankCertificates.IsogenyHom

/-! The partner Kummer kernel is exactly the image of the forward isogeny.
The proof supplies rational lifts and includes infinity and the distinguished
two-torsion point. -/

@[expose] public section

namespace RankCertificates.Isogeny

def phiPreimageX (a s Y : ℚ) : ℚ := (s^2-a+Y/s)/2
def phiPreimageY (a s Y : ℚ) : ℚ := s*phiPreimageX a s Y

theorem phiPreimage_quadratic {a b s Y : ℚ} (hs : s ≠ 0)
    (h : OnCurve (-2*a) (c a b) (s^2) Y) :
    phiPreimageX a s Y ^ 2+(a-s^2)*phiPreimageX a s Y+b=0 := by
  unfold OnCurve c at h
  unfold phiPreimageX
  field_simp [hs]
  linear_combination h

theorem phiPreimage_linear {a s Y : ℚ} (hs : s ≠ 0) :
    2*s*phiPreimageX a s Y = s*(s^2-a)+Y := by
  unfold phiPreimageX
  field_simp [hs]

theorem phiPreimageX_ne_zero {a b s Y : ℚ} (hs : s ≠ 0) (hb : b ≠ 0)
    (h : OnCurve (-2*a) (c a b) (s^2) Y) : phiPreimageX a s Y ≠ 0 := by
  intro hz
  have hq := phiPreimage_quadratic hs h
  apply hb
  simpa only [hz, zero_pow (by decide : (2:ℕ) ≠ 0), mul_zero, zero_add] using hq

theorem phiPreimage_onCurve {a b s Y : ℚ} (hs : s ≠ 0)
    (h : OnCurve (-2*a) (c a b) (s^2) Y) :
    OnCurve a b (phiPreimageX a s Y) (phiPreimageY a s Y) := by
  have hq := phiPreimage_quadratic hs h
  unfold OnCurve phiPreimageY
  linear_combination -phiPreimageX a s Y*hq

theorem phi_phiPreimage_x {a b s Y : ℚ} (hs : s ≠ 0) (hb : b ≠ 0)
    (h : OnCurve (-2*a) (c a b) (s^2) Y) :
    phiX a b (phiPreimageX a s Y) = s^2 := by
  have hx := phiPreimageX_ne_zero hs hb h
  have hq := phiPreimage_quadratic hs h
  unfold phiX
  field_simp [hx]
  linear_combination hq

theorem phi_phiPreimage_y {a b s Y : ℚ} (hs : s ≠ 0) (hb : b ≠ 0)
    (h : OnCurve (-2*a) (c a b) (s^2) Y) :
    phiY b (phiPreimageX a s Y) (phiPreimageY a s Y) = Y := by
  have hx := phiPreimageX_ne_zero hs hb h
  have hq := phiPreimage_quadratic hs h
  have hl := phiPreimage_linear (a := a) (Y := Y) hs
  unfold phiY phiPreimageY
  field_simp [hx]
  linear_combination phiPreimageX a s Y*hl - s*hq

theorem phi_torsion_preimage {a b s : ℚ} (hb : b ≠ 0) (hs : c a b=s^2) :
    ∃ x : ℚ, x ≠ 0 ∧ OnCurve a b x 0 ∧ phiX a b x=0 ∧ phiY b x 0=0 := by
  let x := (-a+s)/2
  have hq : x^2+a*x+b=0 := by
    dsimp [x]
    unfold c at hs
    linear_combination -hs/4
  have hx : x ≠ 0 := by
    intro hz
    apply hb
    simpa only [hz, zero_pow (by decide : (2:ℕ) ≠ 0), mul_zero, zero_add] using hq
  refine ⟨x,hx,?_,?_,?_⟩
  · unfold OnCurve
    linear_combination -x*hq
  · unfold phiX
    field_simp [hx]
    linear_combination hq
  · simp [phiY]

theorem phiPoint_class (a b : ℚ) (hb : b ≠ 0) (hc : c a b ≠ 0)
    (P : (twoTorsionModel a b).toAffine.Point) :
    twoIsogenyClass (-2*a) (c a b) (phiPoint a b hb hc P)=1 := by
  cases P with
  | zero => rfl
  | some x y h =>
    by_cases hx : x=0
    · simp [phiPoint,hx,twoIsogenyClass]
    · have he := (onCurve_iff_equation a b x y).mpr h.1
      simp only [phiPoint,dite_eq_right hx,twoIsogenyClass]
      by_cases hX : phiX a b x=0
      · rw [ite_eq_left hX]
        have hy : y=0 := by
          have hs := phiX_square hx he
          rw [hX] at hs
          have hr : y/x=0 := sq_eq_zero_iff.mp hs.symm
          exact (div_eq_zero_iff).mp hr |>.resolve_right hx
        have hq : x^2+a*x+b=0 := by
          unfold OnCurve at he
          rw [hy] at he
          have hp : x*(x^2+a*x+b)=0 := by linear_combination -he
          exact (mul_eq_zero.mp hp).resolve_left hx
        have hs : c a b=(2*x+a)^2 := by
          unfold c
          linear_combination -4*hq
        rw [hs,rationalSquareClass_square]
      · rw [ite_eq_right hX,phiX_square hx he,rationalSquareClass_square]

theorem partnerClass_eq_one_iff_range (a b : ℚ) (hb : b ≠ 0) (hc : c a b ≠ 0)
    (Q : (twoIsogenousModel a b).toAffine.Point) :
    twoIsogenyClass (-2*a) (c a b) Q=1 ↔ Q ∈ Set.range (phiPoint a b hb hc) := by
  constructor
  · intro hδ
    cases Q with
    | zero => exact ⟨.zero,rfl⟩
    | some X Y h =>
      have he : OnCurve (-2*a) (c a b) X Y :=
        (onCurve_iff_equation (-2*a) (c a b) X Y).mpr h.1
      by_cases hX : X=0
      · subst X
        have hY : Y=0 := by simpa [OnCurve] using he
        subst Y
        have hs : rationalSquareClass (c a b)=1 := by
          simpa [twoIsogenyClass] using hδ
        obtain ⟨s,_,hs⟩ := (rationalSquareClass_eq_one_iff hc).mp hs
        obtain ⟨x,hx,hcurve,hxreturn,hyreturn⟩ := phi_torsion_preimage hb hs
        have hP : (twoTorsionModel a b).toAffine.Nonsingular x 0 :=
          onCurve_nonsingular (original_discriminant_ne_zero hb hc) hcurve
        refine ⟨.some x 0 hP,?_⟩
        simp only [phiPoint,dite_eq_right hx]
        exact affine_some_eq hxreturn hyreturn
      · have hs : rationalSquareClass X=1 := by
          simpa [twoIsogenyClass,hX] using hδ
        obtain ⟨s,hs,hXs⟩ := (rationalSquareClass_eq_one_iff hX).mp hs
        have he' : OnCurve (-2*a) (c a b) (s^2) Y := hXs ▸ he
        have hx := phiPreimageX_ne_zero hs hb he'
        have hcurve := phiPreimage_onCurve hs he'
        have hP : (twoTorsionModel a b).toAffine.Nonsingular (phiPreimageX a s Y) (phiPreimageY a s Y) :=
          onCurve_nonsingular (original_discriminant_ne_zero hb hc) hcurve
        refine ⟨.some _ _ hP,?_⟩
        simp only [phiPoint,dite_eq_right hx]
        exact affine_some_eq ((phi_phiPreimage_x hs hb he').trans hXs.symm)
          (phi_phiPreimage_y hs hb he')
  · rintro ⟨P,rfl⟩
    exact phiPoint_class a b hb hc P

theorem partnerClassHom_kernel (a b : ℚ) (hb : b ≠ 0) (hc : c a b ≠ 0) :
    (twoIsogenyClassAddHom (-2*a) (c a b) hc).ker = (phiPointHom a b hb hc).range := by
  ext Q
  change twoIsogenyClass (-2*a) (c a b) Q=1 ↔ ∃ P,phiPoint a b hb hc P=Q
  exact partnerClass_eq_one_iff_range a b hb hc Q

end RankCertificates.Isogeny
