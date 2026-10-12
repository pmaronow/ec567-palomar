module

public import RankCertificates.IsogenyHom
public import RankCertificates.IsogenyKernel
public import RankCertificates.IsogenyComposition
public import RankCertificates.DualIsogenyHom

@[expose] public section

/-! Exceptional points and the complete dual composition, together with the
forward coordinate map's exact two-point kernel. -/

namespace RankCertificates.IsogenyKernel

open Isogeny

theorem phiPoint_eq_zero_iff (a b : ℚ) (hb : b ≠ 0) (hc : c a b ≠ 0)
    (P : (twoTorsionModel a b).toAffine.Point) :
    phiPoint a b hb hc P = 0 ↔ P = 0 ∨ P = torsionPoint a b hb hc := by
  cases P with
  | zero => simp [WeierstrassCurve.Affine.Point.zero_def]
  | some x y h =>
    by_cases hx : x = 0
    · subst x
      rw [original_point_zero_x a b y hb hc h]
      simp [phiPoint, torsionPoint, WeierstrassCurve.Affine.Point.zero_def]
    · constructor
      · intro hzero
        simp [phiPoint, hx, WeierstrassCurve.Affine.Point.zero_def] at hzero
      · rintro (hzero | htor)
        · simp [WeierstrassCurve.Affine.Point.zero_def] at hzero
        · have hxy : x = 0 ∧ y = 0 := WeierstrassCurve.Affine.Point.some.inj htor
          exact (hx hxy.1).elim

theorem phiPoint_kernel_card (a b : ℚ) (hb : b ≠ 0) (hc : c a b ≠ 0) :
    Nat.card {P : (twoTorsionModel a b).toAffine.Point // phiPoint a b hb hc P = 0} = 2 :=
  card_fiber_zero_of_two_points (phiPoint a b hb hc) (torsionPoint a b hb hc)
    (torsionPoint_ne_zero a b hb hc) (phiPoint_eq_zero_iff a b hb hc)

/-- Exact order of the kernel of the genuine forward isogeny homomorphism. -/
theorem phiPointHom_kernel_card (a b : ℚ) (hb : b ≠ 0) (hc : c a b ≠ 0) :
    Nat.card ↥(phiPointHom a b hb hc).ker = 2 := by
  change Nat.card {P : (twoTorsionModel a b).toAffine.Point // phiPoint a b hb hc P = 0} = 2
  exact phiPoint_kernel_card a b hb hc

/-- Exact order of the kernel of the genuine dual isogeny homomorphism. -/
theorem psiPointHom_kernel_card (a b : ℚ) (hb : b ≠ 0) (hc : c a b ≠ 0) :
    Nat.card ↥(psiPointHom a b hb hc).ker = 2 := by
  change Nat.card {Q : (twoIsogenousModel a b).toAffine.Point // psiPoint a b hb hc Q = 0} = 2
  exact psiPoint_kernel_card a b hb hc

end RankCertificates.IsogenyKernel

namespace RankCertificates.IsogenyComposition

open Isogeny

/-- The actual dual coordinate map composed with the forward coordinate map
is doubling in the genuine rational-point group, including all torsion cases. -/
theorem psiPoint_phiPoint (a b : ℚ) (hb : b ≠ 0) (hc : c a b ≠ 0)
    (P : (twoTorsionModel a b).toAffine.Point) :
    psiPoint a b hb hc (phiPoint a b hb hc P) = P + P := by
  cases P with
  | zero => simp [WeierstrassCurve.Affine.Point.zero_def]
  | some x y hp =>
    have hcurve : OnCurve a b x y := (onCurve_iff_equation a b x y).mpr hp.1
    by_cases hx : x = 0
    · subst x
      have hy : y = 0 := by simpa [OnCurve] using hcurve
      subst y
      rw [WeierstrassCurve.Affine.Point.add_self_of_Y_eq (by
        simp [WeierstrassCurve.Affine.negY, twoTorsionModel])]
      simp [phiPoint, psiPoint, WeierstrassCurve.Affine.Point.zero_def]
    · by_cases hy : y = 0
      · subst y
        have hφx : phiX a b x = 0 := by rw [phiX_square hx hcurve]; simp
        rw [WeierstrassCurve.Affine.Point.add_self_of_Y_eq (by
          simp [WeierstrassCurve.Affine.negY, twoTorsionModel])]
        simp [phiPoint, hx, psiPoint, hφx, WeierstrassCurve.Affine.Point.zero_def]
      · have hyneg : y ≠ (twoTorsionModel a b).toAffine.negY x y := by
          change y ≠ -y - 0 * x - 0
          simp only [zero_mul, sub_zero]
          intro heq
          apply hy
          linarith
        have hφx : phiX a b x ≠ 0 := phiX_ne_zero_of_y_ne_zero hx hy hcurve
        rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hyneg]
        simp only [phiPoint, dite_eq_right hx, psiPoint, dite_eq_right hφx]
        exact affine_some_eq (psi_phi_x_addX hx hy hcurve) (psi_phi_y_addY hx hy hcurve)

/-- The composition identity as an equality of actual group homomorphisms. -/
theorem psiPointHom_comp_phiPointHom (a b : ℚ) (hb : b ≠ 0) (hc : c a b ≠ 0) :
    (psiPointHom a b hb hc).comp (phiPointHom a b hb hc) =
      nsmulAddMonoidHom (α := (twoTorsionModel a b).toAffine.Point) 2 := by
  ext P
  change psiPoint a b hb hc (phiPoint a b hb hc P) = 2 • P
  rw [two_nsmul]
  exact psiPoint_phiPoint a b hb hc P

end RankCertificates.IsogenyComposition
