module

public import RankCertificates.Isogeny
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic

@[expose] public section

/-! Exact size of the coordinate two-isogeny kernels. The distinguished
point `(0,0)` and infinity are the two points in each fiber over infinity. -/

namespace RankCertificates.IsogenyKernel

open Isogeny

/-- The distinguished rational point of order two on the original model. -/
def torsionPoint (a b : ℚ) (hb : b ≠ 0) (hc : c a b ≠ 0) :
    (twoTorsionModel a b).toAffine.Point :=
  .some 0 0 (onCurve_nonsingular (original_discriminant_ne_zero hb hc)
    (by simp [OnCurve]))

/-- The distinguished rational point of order two on the partner model. -/
def partnerTorsionPoint (a b : ℚ) (hb : b ≠ 0) (hc : c a b ≠ 0) :
    (twoIsogenousModel a b).toAffine.Point :=
  .some 0 0 (onCurve_nonsingular (partner_discriminant_ne_zero hb hc)
    (by simp [OnCurve]))

@[simp] theorem torsionPoint_ne_zero (a b : ℚ) (hb : b ≠ 0) (hc : c a b ≠ 0) :
    torsionPoint a b hb hc ≠ 0 := by
  simp [torsionPoint, WeierstrassCurve.Affine.Point.zero_def]

@[simp] theorem partnerTorsionPoint_ne_zero (a b : ℚ) (hb : b ≠ 0) (hc : c a b ≠ 0) :
    partnerTorsionPoint a b hb hc ≠ 0 := by
  simp [partnerTorsionPoint, WeierstrassCurve.Affine.Point.zero_def]

/-- The partner equation permits only `y=0` when its `x` coordinate is zero. -/
theorem partner_point_zero_x (a b y : ℚ) (hb : b ≠ 0) (hc : c a b ≠ 0)
    (h : (twoIsogenousModel a b).toAffine.Nonsingular 0 y) :
    (.some 0 y h : (twoIsogenousModel a b).toAffine.Point) = partnerTorsionPoint a b hb hc := by
  have hcurve : OnCurve (-2 * a) (c a b) 0 y :=
    (onCurve_iff_equation (-2 * a) (c a b) 0 y).mpr h.1
  have hy : y = 0 := by simpa [OnCurve] using hcurve
  subst y
  rfl

/-- The original equation permits only `y=0` when its `x` coordinate is zero. -/
theorem original_point_zero_x (a b y : ℚ) (hb : b ≠ 0) (hc : c a b ≠ 0)
    (h : (twoTorsionModel a b).toAffine.Nonsingular 0 y) :
    (.some 0 y h : (twoTorsionModel a b).toAffine.Point) = torsionPoint a b hb hc := by
  have hcurve : OnCurve a b 0 y := (onCurve_iff_equation a b 0 y).mpr h.1
  have hy : y = 0 := by simpa [OnCurve] using hcurve
  subst y
  rfl

/-- The complete dual-map kernel, including every exceptional coordinate. -/
theorem psiPoint_eq_zero_iff (a b : ℚ) (hb : b ≠ 0) (hc : c a b ≠ 0)
    (Q : (twoIsogenousModel a b).toAffine.Point) :
    psiPoint a b hb hc Q = 0 ↔ Q = 0 ∨ Q = partnerTorsionPoint a b hb hc := by
  cases Q with
  | zero => simp [WeierstrassCurve.Affine.Point.zero_def]
  | some X Y h =>
    by_cases hX : X = 0
    · subst X
      rw [partner_point_zero_x a b Y hb hc h]
      simp [psiPoint, partnerTorsionPoint, WeierstrassCurve.Affine.Point.zero_def]
    · constructor
      · intro hzero
        simp [psiPoint, hX, WeierstrassCurve.Affine.Point.zero_def] at hzero
      · rintro (hzero | htor)
        · simp [WeierstrassCurve.Affine.Point.zero_def] at hzero
        · have hxy : X = 0 ∧ Y = 0 := WeierstrassCurve.Affine.Point.some.inj htor
          exact (hX hxy.1).elim

/-- A fiber consisting of two distinct points has cardinality two. -/
theorem card_fiber_zero_of_two_points {X Y : Type*} [Zero X] [Zero Y]
    (f : X → Y) (T : X) (hT : T ≠ 0)
    (hf : ∀ x, f x = 0 ↔ x = 0 ∨ x = T) :
    Nat.card {x : X // f x = 0} = 2 := by
  have hset : {x : X | f x = 0} = {0, T} := by
    ext x
    exact hf x
  change Nat.card ↥({x : X | f x = 0}) = 2
  rw [Nat.card_coe_set_eq, hset]
  exact Set.ncard_pair hT.symm

/-- The actual dual coordinate map has precisely two points above infinity. -/
theorem psiPoint_kernel_card (a b : ℚ) (hb : b ≠ 0) (hc : c a b ≠ 0) :
    Nat.card {Q : (twoIsogenousModel a b).toAffine.Point // psiPoint a b hb hc Q = 0} = 2 :=
  card_fiber_zero_of_two_points (psiPoint a b hb hc) (partnerTorsionPoint a b hb hc)
    (partnerTorsionPoint_ne_zero a b hb hc) (psiPoint_eq_zero_iff a b hb hc)

end RankCertificates.IsogenyKernel
