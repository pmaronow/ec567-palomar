module

public import RankCertificates.ConditionalAssembly
public import Mathlib.Tactic

@[expose] public section

namespace RankCertificates

@[simp] theorem rationalSquareClass_zero : rationalSquareClass 0 = 1 := by
  simp [rationalSquareClass]

@[simp] theorem rationalSquareClass_one : rationalSquareClass 1 = 1 := by
  simp [rationalSquareClass]

 theorem rationalSquareClass_mul {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0) :
    rationalSquareClass (x * y) = rationalSquareClass x * rationalSquareClass y := by
  simp only [rationalSquareClass, dite_eq_right hx, dite_eq_right hy, dite_eq_right (mul_ne_zero hx hy)]
  exact congrArg QuotientGroup.mk (Units.mk0_mul x y (mul_ne_zero hx hy))

 theorem rationalSquareClass_square (x : ℚ) : rationalSquareClass (x ^ 2) = 1 := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [rationalSquareClass, dite_eq_right (pow_ne_zero 2 hx)]
    apply (QuotientGroup.eq_one_iff _).mpr
    refine ⟨Units.mk0 x hx, ?_⟩
    apply Units.ext
    simp

@[simp] theorem rationalSquareClass_mul_self (x : ℚ) :
    rationalSquareClass x * rationalSquareClass x = 1 := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [← rationalSquareClass_mul hx hx, ← pow_two]
    exact rationalSquareClass_square x

 theorem rationalSquareClass_of_triple_square {x y z t : ℚ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (h : x * y * z = t ^ 2) :
    rationalSquareClass z = rationalSquareClass x * rationalSquareClass y := by
  have hc : rationalSquareClass x * rationalSquareClass y * rationalSquareClass z = 1 := by
    rw [← rationalSquareClass_mul hx hy, ← rationalSquareClass_mul (mul_ne_zero hx hy) hz,
      h, rationalSquareClass_square]
  have hh := congrArg (fun u : RationalSquareClasses => u * rationalSquareClass z) hc
  simpa only [mul_assoc, rationalSquareClass_mul_self, mul_one, one_mul] using hh.symm

 theorem rationalSquareClass_of_product {x y z : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : z = x * y) : rationalSquareClass y = rationalSquareClass z * rationalSquareClass x := by
  have hc : rationalSquareClass z = rationalSquareClass x * rationalSquareClass y := by
    rw [h, rationalSquareClass_mul hx hy]
  rw [hc, mul_right_comm, rationalSquareClass_mul_self, one_mul]

/-- The x-coordinate product for every nonvertical chord or tangent of the
actual two-torsion model is the square of its line intercept. -/
 theorem twoTorsion_chord_product (a b : ℚ) {x₁ x₂ y₁ y₂ : ℚ}
    (h₁ : (twoTorsionModel a b).toAffine.Equation x₁ y₁)
    (h₂ : (twoTorsionModel a b).toAffine.Equation x₂ y₂)
    (hxy : ¬ (x₁ = x₂ ∧ y₁ = (twoTorsionModel a b).toAffine.negY x₂ y₂)) :
    x₁ * x₂ * (twoTorsionModel a b).toAffine.addX x₁ x₂
      ((twoTorsionModel a b).toAffine.slope x₁ x₂ y₁ y₂) =
    (y₁ - (twoTorsionModel a b).toAffine.slope x₁ x₂ y₁ y₂ * x₁) ^ 2 := by
  have h := congrArg (fun f : Polynomial ℚ => f.coeff 0)
    ((twoTorsionModel a b).toAffine.addPolynomial_slope h₁ h₂ hxy)
  rw [WeierstrassCurve.Affine.addPolynomial_eq, Cubic.prod_X_sub_C_eq] at h
  simp only [Polynomial.coeff_neg, Cubic.coeff_eq_d] at h
  have ha₃ : (twoTorsionModel a b).toAffine.a₃ = 0 := rfl
  have ha₆ : (twoTorsionModel a b).toAffine.a₆ = 0 := rfl
  simp only [ha₃, ha₆, zero_mul, add_zero, sub_zero] at h
  linear_combination -h

/-- The coefficient of x in the same chord factorization; this controls the
exceptional case in which one of the three x-coordinates is zero. -/
 theorem twoTorsion_chord_pair_products (a b : ℚ) {x₁ x₂ y₁ y₂ : ℚ}
    (h₁ : (twoTorsionModel a b).toAffine.Equation x₁ y₁)
    (h₂ : (twoTorsionModel a b).toAffine.Equation x₂ y₂)
    (hxy : ¬ (x₁ = x₂ ∧ y₁ = (twoTorsionModel a b).toAffine.negY x₂ y₂)) :
    let ℓ := (twoTorsionModel a b).toAffine.slope x₁ x₂ y₁ y₂
    let z := (twoTorsionModel a b).toAffine.addX x₁ x₂ ℓ
    x₁ * x₂ + x₁ * z + x₂ * z = b - 2 * ℓ * (y₁ - ℓ * x₁) := by
  dsimp only
  have h := congrArg (fun f : Polynomial ℚ => f.coeff 1)
    ((twoTorsionModel a b).toAffine.addPolynomial_slope h₁ h₂ hxy)
  rw [WeierstrassCurve.Affine.addPolynomial_eq, Cubic.prod_X_sub_C_eq] at h
  simp only [Polynomial.coeff_neg, Cubic.coeff_eq_c] at h
  have ha₁ : (twoTorsionModel a b).toAffine.a₁ = 0 := rfl
  have ha₃ : (twoTorsionModel a b).toAffine.a₃ = 0 := rfl
  have ha₄ : (twoTorsionModel a b).toAffine.a₄ = b := rfl
  simp only [ha₁, ha₃, ha₄, zero_mul, zero_sub, sub_zero, neg_zero, zero_add] at h
  linear_combination h

/-- Multiplicativity of the coordinate rule for a chord, including each zero
coordinate case. The two displayed polynomial identities are sufficient. -/
 theorem twoTorsion_coordinate_class (b x₁ x₂ z ℓ t : ℚ) (hb : b ≠ 0)
    (hprod : x₁ * x₂ * z = t ^ 2)
    (hpair : x₁ * x₂ + x₁ * z + x₂ * z = b - 2 * ℓ * t) :
    (if z = 0 then rationalSquareClass b else rationalSquareClass z) =
      (if x₁ = 0 then rationalSquareClass b else rationalSquareClass x₁) *
      (if x₂ = 0 then rationalSquareClass b else rationalSquareClass x₂) := by
  by_cases hx₁ : x₁ = 0
  · have ht : t = 0 := sq_eq_zero_iff.mp (by simpa [hx₁] using hprod.symm)
    have hp : b = x₂ * z := by simpa [hx₁, ht] using hpair.symm
    have hx₂ : x₂ ≠ 0 := fun hz => hb (by simp [hp, hz])
    have hz : z ≠ 0 := fun hz => hb (by simp [hp, hz])
    simp only [ite_eq_left hx₁, ite_eq_right hx₂, ite_eq_right hz]
    exact rationalSquareClass_of_product hx₂ hz hp
  · by_cases hx₂ : x₂ = 0
    · have ht : t = 0 := sq_eq_zero_iff.mp (by simpa [hx₂] using hprod.symm)
      have hp : b = x₁ * z := by simpa [hx₂, ht] using hpair.symm
      have hz : z ≠ 0 := fun hz => hb (by simp [hp, hz])
      simp only [ite_eq_right hx₁, ite_eq_left hx₂, ite_eq_right hz]
      simpa only [mul_comm] using rationalSquareClass_of_product hx₁ hz hp
    · by_cases hz : z = 0
      · have ht : t = 0 := sq_eq_zero_iff.mp (by simpa [hz] using hprod.symm)
        have hp : b = x₁ * x₂ := by simpa [hz, ht] using hpair.symm
        simp only [ite_eq_left hz, ite_eq_right hx₁, ite_eq_right hx₂]
        rw [hp, rationalSquareClass_mul hx₁ hx₂]
      · simp only [ite_eq_right hz, ite_eq_right hx₁, ite_eq_right hx₂]
        exact rationalSquareClass_of_triple_square hx₁ hx₂ hz hprod

/-- The standard two-isogeny class function is multiplicative under the
actual rational-point addition law. Tangencies and all torsion cases are
included; no prime-pattern or local-image hypothesis is used. -/
 theorem twoIsogenyClass_add (a b : ℚ) (hb : b ≠ 0)
    (P Q : (twoTorsionModel a b).toAffine.Point) :
    twoIsogenyClass a b (P + Q) = twoIsogenyClass a b P * twoIsogenyClass a b Q := by
  cases P with
  | zero => simp [twoIsogenyClass, ← WeierstrassCurve.Affine.Point.zero_def]
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero => simp [twoIsogenyClass, ← WeierstrassCurve.Affine.Point.zero_def]
    | some x₂ y₂ h₂ =>
      by_cases hxy : x₁ = x₂ ∧ y₁ = (twoTorsionModel a b).toAffine.negY x₂ y₂
      · rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hxy.1 hxy.2]
        rcases hxy with ⟨rfl, _⟩
        by_cases hx : x₁ = 0 <;> simp [twoIsogenyClass, hx]
      · rw [WeierstrassCurve.Affine.Point.add_some hxy]
        change (if _ = 0 then rationalSquareClass b else rationalSquareClass _) = _
        exact twoTorsion_coordinate_class b x₁ x₂ _ _ _ hb
          (twoTorsion_chord_product a b h₁.1 h₂.1 hxy)
          (twoTorsion_chord_pair_products a b h₁.1 h₂.1 hxy)

/-- The genuine group homomorphism, with the rational-point group written
multiplicatively to match the squareclass target. -/
def twoIsogenyClassHom (a b : ℚ) (hb : b ≠ 0) :
    Multiplicative (twoTorsionModel a b).toAffine.Point →* RationalSquareClasses where
  toFun P := twoIsogenyClass a b P.toAdd
  map_one' := rfl
  map_mul' P Q := twoIsogenyClass_add a b hb P.toAdd Q.toAdd

 theorem twoTorsion_b_ne_zero (a b : ℚ) [(twoTorsionModel a b).IsElliptic] : b ≠ 0 := by
  have h := (twoTorsionModel a b).isUnit_Δ.ne_zero
  intro hb
  simp [twoTorsionModel, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈, hb] at h

/-- The homomorphism for an elliptic two-torsion model. -/
def ellipticTwoIsogenyClassHom (a b : ℚ) [(twoTorsionModel a b).IsElliptic] :
    Multiplicative (twoTorsionModel a b).toAffine.Point →* RationalSquareClasses :=
  twoIsogenyClassHom a b (twoTorsion_b_ne_zero a b)

/-- The same genuine homomorphism with both groups written additively. -/
def twoIsogenyClassAddHom (a b : ℚ) (hb : b ≠ 0) :
    (twoTorsionModel a b).toAffine.Point →+ Additive RationalSquareClasses where
  toFun P := Additive.ofMul (twoIsogenyClass a b P)
  map_zero' := rfl
  map_add' P Q := twoIsogenyClass_add a b hb P Q

/-- The previously defined actual rational-point image is the carrier of the
range subgroup of the proved homomorphism. -/
def twoIsogenyImageSubgroup (a b : ℚ) (hb : b ≠ 0) : Subgroup RationalSquareClasses :=
  (twoIsogenyClassHom a b hb).range

 theorem twoIsogenyImage_eq_subgroup (a b : ℚ) (hb : b ≠ 0) :
    twoIsogenyImage a b = (twoIsogenyImageSubgroup a b hb : Set RationalSquareClasses) := by
  ext q
  constructor
  · rintro ⟨P, hP⟩
    exact ⟨Multiplicative.ofAdd P, hP⟩
  · rintro ⟨P, hP⟩
    exact ⟨P.toAdd, hP⟩

 theorem rationalSquareClass_mul_square {x r : ℚ} (hx : x ≠ 0) (hr : r ≠ 0) :
    rationalSquareClass (x * r ^ 2) = rationalSquareClass x := by
  rw [rationalSquareClass_mul hx (pow_ne_zero 2 hr), rationalSquareClass_square, mul_one]

/-- Exact meaning of trivial squareclass for a nonzero rational number. -/
 theorem rationalSquareClass_eq_one_iff {x : ℚ} (hx : x ≠ 0) :
    rationalSquareClass x = 1 ↔ ∃ r : ℚ, r ≠ 0 ∧ x = r ^ 2 := by
  rw [rationalSquareClass, dite_eq_right hx, QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨(u : ℚ), u.ne_zero, ?_⟩
    have hv := congrArg (fun v : ℚˣ => (v : ℚ)) hu
    simpa using hv.symm
  · rintro ⟨r, hr, hxr⟩
    refine ⟨Units.mk0 r hr, ?_⟩
    apply Units.ext
    simpa using hxr.symm

end RankCertificates
