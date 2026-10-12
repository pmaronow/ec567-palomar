module

public import RankCertificates.MordellWeil
public import RankCertificates.Geometric
public import EllipticCurves.VariableChange

/-!
Homogeneous parameter normalization preserves the actual rational point group,
and therefore its Mordell–Weil rank. The scaling used here is an admissible
change of Weierstrass coordinates, not a specialization assertion.
-/

@[expose] public section

namespace RankCertificates.Normalization

open WeierstrassCurve

/-- The genuine rank is invariant under an additive equivalence of point groups. -/
theorem hasExactRank_iff_of_addEquiv {E E' : WeierstrassCurve ℚ}
    (e : E.toAffine.Point ≃+ E'.toAffine.Point) (r : ℕ) :
    HasExactRank E r ↔ HasExactRank E' r := by
  unfold HasExactRank rationalRank
  rw [e.toIntLinearEquiv.rank_eq]

/-- A pure coordinate scaling. -/
def scaleChange (u : ℚˣ) : VariableChange ℚ := ⟨u, 0, 0, 0⟩

theorem scaleChange_model (u : ℚˣ) (a b : ℚ) :
    scaleChange u • model a b = model ((u : ℚ)⁻¹ ^ 2 * a) ((u : ℚ)⁻¹ ^ 4 * b) := by
  ext <;> simp [scaleChange, model, variableChange_def]

/-- Point-group equivalence for a homogeneous scaling of the coefficients. -/
noncomputable def coefficientScaleEquiv (u : ℚˣ) (a b : ℚ)
    [(model a b).IsElliptic] :
    (model ((u : ℚ) ^ 2 * a) ((u : ℚ) ^ 4 * b)).toAffine.Point ≃+
      (model a b).toAffine.Point := by
  have h : scaleChange u⁻¹ • model a b =
      model ((u : ℚ) ^ 2 * a) ((u : ℚ) ^ 4 * b) := by
    rw [scaleChange_model]
    simp
  exact (Affine.Point.equivOfEq h).symm.trans (Affine.Point.equivVariableChange _ _)

/-- Point-group equivalence for a homogeneous scaling of the coefficients. -/
noncomputable def modelCoordinateScaleEquiv (u a b : ℚ) (hu : u ≠ 0)
    [(model a b).IsElliptic] :
    (model (u ^ 2 * a) (u ^ 4 * b)).toAffine.Point ≃+ (model a b).toAffine.Point :=
  coefficientScaleEquiv (Units.mk0 u hu) a b

theorem point_equivOfEq_symm {W W' : WeierstrassCurve ℚ} (h : W = W') :
    (Affine.Point.equivOfEq h).symm = Affine.Point.equivOfEq h.symm := by
  subst h
  rfl

@[simp] theorem coefficientScaleEquiv_zero (u : ℚˣ) (a b : ℚ)
    [(model a b).IsElliptic] : coefficientScaleEquiv u a b 0 = 0 := map_zero _

theorem coefficientScaleEquiv_some (u : ℚˣ) (a b : ℚ)
    [(model a b).IsElliptic] {X Y : ℚ}
    (h : (model ((u : ℚ) ^ 2 * a) ((u : ℚ) ^ 4 * b)).toAffine.Nonsingular X Y)
    (h' : (model a b).toAffine.Nonsingular ((u : ℚ)⁻¹ ^ 2 * X) ((u : ℚ)⁻¹ ^ 3 * Y)) :
    coefficientScaleEquiv u a b (.some X Y h) =
      .some ((u : ℚ)⁻¹ ^ 2 * X) ((u : ℚ)⁻¹ ^ 3 * Y) h' := by
  simp only [coefficientScaleEquiv, AddEquiv.trans_apply, point_equivOfEq_symm,
    Affine.Point.equivOfEq_some, Affine.Point.equivVariableChange_some]
  apply Affine.Point.some_eq_some (model a b)
  · simp [scaleChange]
  · simp [scaleChange]

@[simp] theorem modelCoordinateScaleEquiv_zero (u a b : ℚ) (hu : u ≠ 0)
    [(model a b).IsElliptic] : modelCoordinateScaleEquiv u a b hu 0 = 0 := map_zero _

theorem modelCoordinateScaleEquiv_some (u a b : ℚ) (hu : u ≠ 0)
    [(model a b).IsElliptic] {X Y : ℚ}
    (h : (model (u ^ 2 * a) (u ^ 4 * b)).toAffine.Nonsingular X Y)
    (h' : (model a b).toAffine.Nonsingular (X / u ^ 2) (Y / u ^ 3)) :
    modelCoordinateScaleEquiv u a b hu (.some X Y h) = .some (X / u ^ 2) (Y / u ^ 3) h' := by
  have h'' : (model a b).toAffine.Nonsingular (u⁻¹ ^ 2 * X) (u⁻¹ ^ 3 * Y) := by
    simpa only [inv_pow, div_eq_mul_inv, mul_comm X, mul_comm Y] using h'
  change coefficientScaleEquiv (Units.mk0 u hu) a b (.some X Y h) = _
  calc
    _ = .some (u⁻¹ ^ 2 * X) (u⁻¹ ^ 3 * Y) h'' :=
      coefficientScaleEquiv_some (Units.mk0 u hu) a b h h''
    _ = .some (X / u ^ 2) (Y / u ^ 3) h' := by
      apply Affine.Point.some_eq_some (model a b)
      · rw [div_eq_mul_inv, inv_pow, mul_comm]
      · rw [div_eq_mul_inv, inv_pow, mul_comm]
  rfl

/-- Point-group equivalence for a homogeneous scaling of the coefficients. -/
noncomputable def modelScaleEquiv (s a b : ℚ) (hs : s ≠ 0)
    [(model a b).IsElliptic] :
    (model (s ^ 4 * a) (s ^ 8 * b)).toAffine.Point ≃+ (model a b).toAffine.Point := by
  let u : ℚˣ := Units.mk0 (s⁻¹ ^ 2) (pow_ne_zero 2 (inv_ne_zero hs))
  have h : scaleChange u • model a b = model (s ^ 4 * a) (s ^ 8 * b) := by
    rw [scaleChange_model]
    simp [u, inv_pow, ← pow_mul]
  exact (Affine.Point.equivOfEq h).symm.trans (Affine.Point.equivVariableChange _ _)

theorem hasExactRank_model_scale (s a b : ℚ) (hs : s ≠ 0)
    [(model a b).IsElliptic] (r : ℕ) :
    HasExactRank (model (s ^ 4 * a) (s ^ 8 * b)) r ↔ HasExactRank (model a b) r :=
  hasExactRank_iff_of_addEquiv (modelScaleEquiv s a b hs) r


theorem homogeneous5_F (s M N : ℚ) :
    RankCertificates.Rank5.F (s * M) (s * N) = s ^ 4 * RankCertificates.Rank5.F M N := by
  simp only [RankCertificates.Rank5.F, RankCertificates.Rank5.L0, RankCertificates.Rank5.L1, RankCertificates.Rank5.L2, RankCertificates.Rank5.L3]
  ring

theorem homogeneous5_H (s M N : ℚ) :
    RankCertificates.Rank5.H (s * M) (s * N) = s ^ 4 * RankCertificates.Rank5.H M N := by
  simp only [RankCertificates.Rank5.H, RankCertificates.Rank5.L4, RankCertificates.Rank5.L5, RankCertificates.Rank5.L6, RankCertificates.Rank5.L7]
  ring

theorem homogeneous5_J (s M N : ℚ) :
    RankCertificates.Rank5.J (s * M) (s * N) = s ^ 4 * RankCertificates.Rank5.J M N := by
  simp only [RankCertificates.Rank5.J, RankCertificates.Rank5.L8, RankCertificates.Rank5.L9, RankCertificates.Rank5.L10, RankCertificates.Rank5.L11]
  ring

theorem homogeneous5_a (s M N : ℚ) :
    RankCertificates.Rank5.a (s * M) (s * N) = s ^ 4 * RankCertificates.Rank5.a M N := by
  simp only [RankCertificates.Rank5.a, homogeneous5_F]
  ring

theorem homogeneous5_b (s M N : ℚ) :
    RankCertificates.Rank5.b (s * M) (s * N) = s ^ 8 * RankCertificates.Rank5.b M N := by
  simp only [RankCertificates.Rank5.b, homogeneous5_F, homogeneous5_H]
  ring

theorem homogeneous7_F (s M N : ℚ) :
    RankCertificates.Rank7.F (s * M) (s * N) = s ^ 4 * RankCertificates.Rank7.F M N := by
  simp only [RankCertificates.Rank7.F, RankCertificates.Rank7.L0, RankCertificates.Rank7.L1, RankCertificates.Rank7.L2, RankCertificates.Rank7.L3]
  ring

theorem homogeneous7_H (s M N : ℚ) :
    RankCertificates.Rank7.H (s * M) (s * N) = s ^ 4 * RankCertificates.Rank7.H M N := by
  simp only [RankCertificates.Rank7.H, RankCertificates.Rank7.L4, RankCertificates.Rank7.L5, RankCertificates.Rank7.L6, RankCertificates.Rank7.L7]
  ring

theorem homogeneous7_J (s M N : ℚ) :
    RankCertificates.Rank7.J (s * M) (s * N) = s ^ 4 * RankCertificates.Rank7.J M N := by
  simp only [RankCertificates.Rank7.J, RankCertificates.Rank7.L8, RankCertificates.Rank7.L9, RankCertificates.Rank7.L10, RankCertificates.Rank7.L11]
  ring

theorem homogeneous7_a (s M N : ℚ) :
    RankCertificates.Rank7.a (s * M) (s * N) = s ^ 4 * RankCertificates.Rank7.a M N := by
  simp only [RankCertificates.Rank7.a, homogeneous7_F]
  ring

theorem homogeneous7_b (s M N : ℚ) :
    RankCertificates.Rank7.b (s * M) (s * N) = s ^ 8 * RankCertificates.Rank7.b M N := by
  simp only [RankCertificates.Rank7.b, homogeneous7_F, homogeneous7_H]
  ring

theorem model_scale_isElliptic (s a b : ℚ) (hs : s ≠ 0)
    [(model a b).IsElliptic] : (model (s ^ 4 * a) (s ^ 8 * b)).IsElliptic := by
  let u : ℚˣ := Units.mk0 (s⁻¹ ^ 2) (pow_ne_zero 2 (inv_ne_zero hs))
  have h : scaleChange u • model a b = model (s ^ 4 * a) (s ^ 8 * b) := by
    rw [scaleChange_model]
    simp [u, inv_pow, ← pow_mul]
  rw [← h]
  infer_instance

theorem curve5_normalize (M N : ℚ) (hN : N ≠ 0) :
    RankCertificates.Rank5.E (M / N) 1 = model (N⁻¹ ^ 4 * RankCertificates.Rank5.a M N) (N⁻¹ ^ 8 * RankCertificates.Rank5.b M N) := by
  have h : RankCertificates.Rank5.E (N⁻¹ * M) (N⁻¹ * N) =
      model (N⁻¹ ^ 4 * RankCertificates.Rank5.a M N) (N⁻¹ ^ 8 * RankCertificates.Rank5.b M N) := by
    simp only [RankCertificates.Rank5.E, homogeneous5_a, homogeneous5_b]
  simpa only [inv_mul_cancel₀ hN, div_eq_mul_inv, mul_comm N⁻¹ M] using h

theorem normalized5_isElliptic (M N : ℚ) (hN : N ≠ 0)
    [(RankCertificates.Rank5.E M N).IsElliptic] : (RankCertificates.Rank5.E (M / N) 1).IsElliptic := by
  let : (model (Rank5.a M N) (Rank5.b M N)).IsElliptic :=
    ‹(Rank5.E M N).IsElliptic›
  rw [curve5_normalize M N hN]
  exact model_scale_isElliptic N⁻¹ _ _ (inv_ne_zero hN)

/-- Exact rank survives passage from a homogeneous pair to its rational direction. -/
theorem normalized5_exactRank_iff (M N : ℚ) (hN : N ≠ 0)
    [(RankCertificates.Rank5.E M N).IsElliptic] (r : ℕ) :
    HasExactRank (RankCertificates.Rank5.E (M / N) 1) r ↔ HasExactRank (RankCertificates.Rank5.E M N) r := by
  let : (model (Rank5.a M N) (Rank5.b M N)).IsElliptic :=
    ‹(Rank5.E M N).IsElliptic›
  rw [curve5_normalize M N hN]
  exact hasExactRank_model_scale N⁻¹ _ _ (inv_ne_zero hN) r

theorem curve6_normalize (M N : ℚ) (hN : N ≠ 0) :
    RankCertificates.Rank6.E (M / N) 1 = model (N⁻¹ ^ 4 * RankCertificates.Rank6.a M N) (N⁻¹ ^ 8 * RankCertificates.Rank6.b M N) := by
  have h : RankCertificates.Rank6.E (N⁻¹ * M) (N⁻¹ * N) =
      model (N⁻¹ ^ 4 * RankCertificates.Rank6.a M N) (N⁻¹ ^ 8 * RankCertificates.Rank6.b M N) := by
    simp only [RankCertificates.Rank6.E, RankCertificates.Rank6.homogeneous_a, RankCertificates.Rank6.homogeneous_b]
  simpa only [inv_mul_cancel₀ hN, div_eq_mul_inv, mul_comm N⁻¹ M] using h

theorem normalized6_isElliptic (M N : ℚ) (hN : N ≠ 0)
    [(RankCertificates.Rank6.E M N).IsElliptic] : (RankCertificates.Rank6.E (M / N) 1).IsElliptic := by
  let : (model (Rank6.a M N) (Rank6.b M N)).IsElliptic :=
    ‹(Rank6.E M N).IsElliptic›
  rw [curve6_normalize M N hN]
  exact model_scale_isElliptic N⁻¹ _ _ (inv_ne_zero hN)

/-- Exact rank survives passage from a homogeneous pair to its rational direction. -/
theorem normalized6_exactRank_iff (M N : ℚ) (hN : N ≠ 0)
    [(RankCertificates.Rank6.E M N).IsElliptic] (r : ℕ) :
    HasExactRank (RankCertificates.Rank6.E (M / N) 1) r ↔ HasExactRank (RankCertificates.Rank6.E M N) r := by
  let : (model (Rank6.a M N) (Rank6.b M N)).IsElliptic :=
    ‹(Rank6.E M N).IsElliptic›
  rw [curve6_normalize M N hN]
  exact hasExactRank_model_scale N⁻¹ _ _ (inv_ne_zero hN) r

theorem curve7_normalize (M N : ℚ) (hN : N ≠ 0) :
    RankCertificates.Rank7.E (M / N) 1 = model (N⁻¹ ^ 4 * RankCertificates.Rank7.a M N) (N⁻¹ ^ 8 * RankCertificates.Rank7.b M N) := by
  have h : RankCertificates.Rank7.E (N⁻¹ * M) (N⁻¹ * N) =
      model (N⁻¹ ^ 4 * RankCertificates.Rank7.a M N) (N⁻¹ ^ 8 * RankCertificates.Rank7.b M N) := by
    simp only [RankCertificates.Rank7.E, homogeneous7_a, homogeneous7_b]
  simpa only [inv_mul_cancel₀ hN, div_eq_mul_inv, mul_comm N⁻¹ M] using h

theorem normalized7_isElliptic (M N : ℚ) (hN : N ≠ 0)
    [(RankCertificates.Rank7.E M N).IsElliptic] : (RankCertificates.Rank7.E (M / N) 1).IsElliptic := by
  let : (model (Rank7.a M N) (Rank7.b M N)).IsElliptic :=
    ‹(Rank7.E M N).IsElliptic›
  rw [curve7_normalize M N hN]
  exact model_scale_isElliptic N⁻¹ _ _ (inv_ne_zero hN)

/-- Exact rank survives passage from a homogeneous pair to its rational direction. -/
theorem normalized7_exactRank_iff (M N : ℚ) (hN : N ≠ 0)
    [(RankCertificates.Rank7.E M N).IsElliptic] (r : ℕ) :
    HasExactRank (RankCertificates.Rank7.E (M / N) 1) r ↔ HasExactRank (RankCertificates.Rank7.E M N) r := by
  let : (model (Rank7.a M N) (Rank7.b M N)).IsElliptic :=
    ‹(Rank7.E M N).IsElliptic›
  rw [curve7_normalize M N hN]
  exact hasExactRank_model_scale N⁻¹ _ _ (inv_ne_zero hN) r

end RankCertificates.Normalization
