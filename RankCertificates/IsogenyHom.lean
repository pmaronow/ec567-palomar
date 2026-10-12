module

public import RankCertificates.Isogeny

/-!
# The forward rational two-isogeny and its chord identities

The algebraic chord identities in this file use the actual affine group law.
-/

@[expose] public section

namespace RankCertificates.Isogeny

theorem affine_some_eq {W : WeierstrassCurve.Affine ℚ} {x₁ x₂ y₁ y₂ : ℚ}
    {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
    (hx : x₁=x₂) (hy : y₁=y₂) :
    WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ = .some x₂ y₂ h₂ := by
  cases hx
  cases hy
  rfl

theorem phi_nonsingular {a b x y : ℚ} (hb : b ≠ 0) (hc : c a b ≠ 0)
    (hx : x ≠ 0) (h : (twoTorsionModel a b).toAffine.Nonsingular x y) :
    (twoIsogenousModel a b).toAffine.Nonsingular (phiX a b x) (phiY b x y) :=
  onCurve_nonsingular (partner_discriminant_ne_zero hb hc)
    (phi_onCurve hx ((onCurve_iff_equation a b x y).mpr h.1))

def phiPoint (a b : ℚ) (hb : b ≠ 0) (hc : c a b ≠ 0) :
    (twoTorsionModel a b).toAffine.Point → (twoIsogenousModel a b).toAffine.Point
  | .zero => .zero
  | .some x y h => if hx : x = 0 then .zero else
      .some (phiX a b x) (phiY b x y)
        (phi_nonsingular hb hc hx h)

@[simp] theorem phiPoint_zero (a b : ℚ) (hb : b ≠ 0) (hc : c a b ≠ 0) :
    phiPoint a b hb hc .zero = .zero := rfl

@[simp] theorem phiPoint_map_zero (a b : ℚ) (hb : b ≠ 0) (hc : c a b ≠ 0) :
    phiPoint a b hb hc 0 = 0 := rfl

theorem phi_chord_line {a b x m n : ℚ} (hx : x ≠ 0) (hn : n ≠ 0)
    (h : OnCurve a b x (m * x + n)) :
    phiY b x (m * x + n) =
      (m - b / n) * phiX a b x + (n - a * m + b * m ^ 2 / n) := by
  unfold phiY phiX OnCurve at *
  field_simp [hx, hn]
  linear_combination -b * h

theorem phi_chord_sum {a b x₁ x₂ x₃ m n : ℚ}
    (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0) (hx₃ : x₃ ≠ 0) (hn : n ≠ 0)
    (hsum : x₁ + x₂ + x₃ = m ^ 2 - a)
    (hpair : x₁*x₂ + x₁*x₃ + x₂*x₃ = b - 2*m*n)
    (hprod : x₁*x₂*x₃ = n ^ 2) :
    phiX a b x₁ + phiX a b x₂ + phiX a b x₃ = (m-b/n)^2 + 2*a := by
  unfold phiX
  field_simp [hx₁, hx₂, hx₃, hn]
  linear_combination n ^ 2 * x₁*x₂*x₃ * hsum +
    b*n ^ 2 * hpair - b*(b-2*m*n)*hprod

theorem phi_tangent_line {a b x y m n : ℚ} (hx : x ≠ 0) (hn : n ≠ 0)
    (h : OnCurve a b x y) (hline : y = m*x+n)
    (ht : 2*y*m = 3*x^2+2*a*x+b) :
    2 * phiY b x y * (m-b/n) =
      3 * phiX a b x ^ 2 - 4*a*phiX a b x + c a b := by
  unfold OnCurve at h
  have hi : 2*y*n+x*(x^2-b)=0 := by
    linear_combination 2*h - x*ht - 2*y*hline
  unfold phiY phiX c
  field_simp [hx, hn]
  apply (mul_left_cancel₀ hx)
  linear_combination n*x*(x^2-b)*ht - 2*b*y*hi + 4*b*n*h

theorem phi_coincident_tangent {a u v m n : ℚ}
    (hu : u ≠ 0) (hn : n ≠ 0)
    (h : OnCurve a (u*v) u (m*u+n))
    (hr : 2*m*u*v+n*(u+v)=0) :
    2*phiY (u*v) u (m*u+n)*(m-u*v/n) =
      3*phiX a (u*v) u^2-4*a*phiX a (u*v) u+c a (u*v) := by
  unfold OnCurve at h
  unfold phiY phiX c
  field_simp [hu, hn]
  apply (mul_left_cancel₀ hu)
  linear_combination 2*n*(u+v)*h - (2*m*n*u+2*n^2+u^3-u^2*v)*hr

theorem phiX_coincident {a b u v : ℚ} (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : u ≠ v) (h : phiX a b u = phiX a b v) : b = u*v := by
  unfold phiX at h
  field_simp [hu, hv] at h
  have hh : (u-v)*(b-u*v)=0 := by linear_combination -h
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr huv))

theorem phi_coincident_relation {a u v m n : ℚ}
    (huv : u ≠ v) (hn : n ≠ 0)
    (h₁ : OnCurve a (u*v) u (m*u+n))
    (h₂ : OnCurve a (u*v) v (m*v+n)) :
    2*m*u*v+n*(u+v)=0 := by
  unfold OnCurve at h₁ h₂
  apply (mul_left_cancel₀ (mul_ne_zero hn (sub_ne_zero.mpr huv)))
  linear_combination u^2*h₂-v^2*h₁

theorem twoTorsion_slope_line (a b : ℚ) {x₁ x₂ y₁ y₂ : ℚ}
    (h₁ : (twoTorsionModel a b).toAffine.Equation x₁ y₁)
    (h₂ : (twoTorsionModel a b).toAffine.Equation x₂ y₂)
    (hxy : ¬ (x₁=x₂ ∧ y₁=(twoTorsionModel a b).toAffine.negY x₂ y₂)) :
    let m := (twoTorsionModel a b).toAffine.slope x₁ x₂ y₁ y₂
    y₂ = m*x₂+(y₁-m*x₁) := by
  dsimp only
  by_cases hx : x₁=x₂
  · have hy := WeierstrassCurve.Affine.Y_eq_of_Y_ne h₁ h₂ hx
      (fun hy => hxy ⟨hx,hy⟩)
    rw [hx, hy]
    ring
  · rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
    field_simp [sub_ne_zero.mpr hx]
    ring

theorem twoTorsion_tangent (a b : ℚ) {x y₁ y₂ : ℚ}
    (h₁ : (twoTorsionModel a b).toAffine.Equation x y₁)
    (h₂ : (twoTorsionModel a b).toAffine.Equation x y₂)
    (hy : y₁ ≠ (twoTorsionModel a b).toAffine.negY x y₂) :
    2*y₁*(twoTorsionModel a b).toAffine.slope x x y₁ y₂ = 3*x^2+2*a*x+b := by
  have hsame := WeierstrassCurve.Affine.Y_eq_of_Y_ne h₁ h₂ rfl hy
  have hn : 2*y₁ ≠ 0 := by
    intro h
    apply hy
    simp only [twoTorsionModel, WeierstrassCurve.Affine.negY, zero_mul, sub_zero] at hy ⊢
    rw [← hsame]
    linear_combination h
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
  simp only [twoTorsionModel, WeierstrassCurve.Affine.negY, zero_mul, sub_zero]
  have hd : y₁-(-y₁) = 2*y₁ := by ring
  rw [hd, mul_div_cancel₀ _ hn]

theorem phi_slope (a b : ℚ) (hb : b ≠ 0) (hc : c a b ≠ 0)
    {x₁ x₂ y₁ y₂ : ℚ} (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0)
    (h₁ : (twoTorsionModel a b).toAffine.Equation x₁ y₁)
    (h₂ : (twoTorsionModel a b).toAffine.Equation x₂ y₂)
    (hxy : ¬ (x₁=x₂ ∧ y₁=(twoTorsionModel a b).toAffine.negY x₂ y₂))
    (hn : y₁-(twoTorsionModel a b).toAffine.slope x₁ x₂ y₁ y₂*x₁ ≠ 0) :
    let m := (twoTorsionModel a b).toAffine.slope x₁ x₂ y₁ y₂
    let n := y₁-m*x₁
    (twoIsogenousModel a b).toAffine.slope (phiX a b x₁) (phiX a b x₂)
      (phiY b x₁ y₁) (phiY b x₂ y₂) = m-b/n ∧
    ¬ (phiX a b x₁=phiX a b x₂ ∧
      phiY b x₁ y₁=(twoIsogenousModel a b).toAffine.negY (phiX a b x₂) (phiY b x₂ y₂)) := by
  let m := (twoTorsionModel a b).toAffine.slope x₁ x₂ y₁ y₂
  let n := y₁-m*x₁
  have hn' : n ≠ 0 := hn
  have hl₁ : y₁=m*x₁+n := by dsimp [n]; ring
  have hl₂ : y₂=m*x₂+n := twoTorsion_slope_line a b h₁ h₂ hxy
  have he₁ : OnCurve a b x₁ y₁ := (onCurve_iff_equation a b x₁ y₁).mpr h₁
  have he₂ : OnCurve a b x₂ y₂ := (onCurve_iff_equation a b x₂ y₂).mpr h₂
  have hL₁ := phi_chord_line hx₁ hn' (hl₁ ▸ he₁)
  have hL₂ := phi_chord_line hx₂ hn' (hl₂ ▸ he₂)
  rw [← hl₁] at hL₁
  rw [← hl₂] at hL₂
  by_cases hX : phiX a b x₁=phiX a b x₂
  · have hY : phiY b x₁ y₁=phiY b x₂ y₂ := by rw [hL₁,hL₂,hX]
    have ht : 2*phiY b x₁ y₁*(m-b/n) =
        3*phiX a b x₁^2-4*a*phiX a b x₁+c a b := by
      by_cases hx : x₁=x₂
      · subst x₂
        exact phi_tangent_line hx₁ hn' he₁ hl₁ (twoTorsion_tangent a b h₁ h₂ (fun hy => hxy ⟨rfl,hy⟩))
      · have hb' := phiX_coincident hx₁ hx₂ hx hX
        rw [hb'] at he₁ he₂ ⊢
        have hr := phi_coincident_relation hx hn' (hl₁ ▸ he₁) (hl₂ ▸ he₂)
        simpa [← hl₁] using phi_coincident_tangent hx₁ hn' (hl₁ ▸ he₁) hr
    have hns := onCurve_nonsingular (partner_discriminant_ne_zero hb hc) (phi_onCurve hx₁ he₁)
    have hnY : phiY b x₁ y₁ ≠ -phiY b x₁ y₁ := by
      intro heq
      rw [WeierstrassCurve.Affine.nonsingular_iff] at hns
      simp only [model, zero_mul, sub_zero] at hns
      rcases hns.2 with hder | hYne
      · apply hder
        unfold c at ht
        linear_combination ht - (m-b/n)*heq
      · exact hYne heq
    have hy : phiY b x₁ y₁ ≠
        (twoIsogenousModel a b).toAffine.negY (phiX a b x₂) (phiY b x₂ y₂) := by
      simp only [twoIsogenousModel, twoTorsionModel, WeierstrassCurve.Affine.negY, zero_mul, sub_zero]
      simpa [← hY] using hnY
    constructor
    · rw [WeierstrassCurve.Affine.slope_of_Y_ne hX hy]
      simp only [twoIsogenousModel, twoTorsionModel, WeierstrassCurve.Affine.negY, zero_mul, sub_zero]
      apply (div_eq_iff (sub_ne_zero.mpr hnY)).mpr
      change 3*phiX a b x₁^2+2*(-2*a)*phiX a b x₁+(a^2-4*b) =
        (m-b/n)*(phiY b x₁ y₁-(-phiY b x₁ y₁))
      unfold c at ht
      linear_combination -ht
    · exact fun h => hy h.2
  · constructor
    · rw [WeierstrassCurve.Affine.slope_of_X_ne hX]
      apply (div_eq_iff (sub_ne_zero.mpr hX)).mpr
      linear_combination hL₁-hL₂
    · exact fun h => hX h.1

theorem phi_torsion_translate {a b x y : ℚ} (hx : x ≠ 0) (hb : b ≠ 0) :
    phiX a b (b/x)=phiX a b x ∧
    phiY b (b/x) (-b*y/x^2)=phiY b x y := by
  constructor <;> simp only [phiX, phiY] <;> field_simp [hx, hb] <;> ring

theorem phi_add_coordinates (a b : ℚ) (hb : b ≠ 0) (hc : c a b ≠ 0)
    {x₁ x₂ y₁ y₂ : ℚ} (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0)
    (h₁ : (twoTorsionModel a b).toAffine.Equation x₁ y₁)
    (h₂ : (twoTorsionModel a b).toAffine.Equation x₂ y₂)
    (hxy : ¬ (x₁=x₂ ∧ y₁=(twoTorsionModel a b).toAffine.negY x₂ y₂))
    (hn : y₁-(twoTorsionModel a b).toAffine.slope x₁ x₂ y₁ y₂*x₁ ≠ 0) :
    let m := (twoTorsionModel a b).toAffine.slope x₁ x₂ y₁ y₂
    let z := (twoTorsionModel a b).toAffine.addX x₁ x₂ m
    let w := (twoTorsionModel a b).toAffine.addY x₁ x₂ y₁ m
    let m' := (twoIsogenousModel a b).toAffine.slope (phiX a b x₁) (phiX a b x₂)
      (phiY b x₁ y₁) (phiY b x₂ y₂)
    phiX a b z = (twoIsogenousModel a b).toAffine.addX (phiX a b x₁) (phiX a b x₂) m' ∧
    phiY b z w = (twoIsogenousModel a b).toAffine.addY (phiX a b x₁) (phiX a b x₂) (phiY b x₁ y₁) m' := by
  let m := (twoTorsionModel a b).toAffine.slope x₁ x₂ y₁ y₂
  let n := y₁-m*x₁
  let z := (twoTorsionModel a b).toAffine.addX x₁ x₂ m
  have hn' : n ≠ 0 := hn
  have hprod : x₁*x₂*z=n^2 := twoTorsion_chord_product a b h₁ h₂ hxy
  have hz : z ≠ 0 := by
    intro hz
    apply pow_ne_zero 2 hn'
    simpa [hz] using hprod.symm
  have hpair : x₁*x₂+x₁*z+x₂*z=b-2*m*n := twoTorsion_chord_pair_products a b h₁ h₂ hxy
  have hsum : x₁+x₂+z=m^2-a := by
    dsimp [z]
    simp only [twoTorsionModel, zero_mul, add_zero]
    ring
  have hS := phi_chord_sum hx₁ hx₂ hz hn' hsum hpair hprod
  have hm' := (phi_slope a b hb hc hx₁ hx₂ h₁ h₂ hxy hn).1
  have hl₁ : y₁=m*x₁+n := by dsimp [n]; ring
  have he₁ := (onCurve_iff_equation a b x₁ y₁).mpr h₁
  have hL₁ := phi_chord_line hx₁ hn' (hl₁ ▸ he₁)
  rw [← hl₁] at hL₁
  have he₃ : OnCurve a b z (m*z+n) := by
    have he := WeierstrassCurve.Affine.equation_negAdd h₁ h₂ hxy
    have hy₃ : (twoTorsionModel a b).toAffine.negAddY x₁ x₂ y₁ m=m*z+n := by
      simp only [WeierstrassCurve.Affine.negAddY]
      dsimp [z,n]
      ring
    rw [hy₃] at he
    exact (onCurve_iff_equation a b z (m*z+n)).mpr he
  have hL₃ := phi_chord_line hz hn' he₃
  have hw : (twoTorsionModel a b).toAffine.addY x₁ x₂ y₁ m = -(m*z+n) := by
    simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY, twoTorsionModel, zero_mul, sub_zero]
    dsimp [z,n]
    simp only [twoTorsionModel]
    ring
  dsimp only
  rw [hm']
  constructor
  · change phiX a b z = (twoIsogenousModel a b).toAffine.addX _ _ (m-b/n)
    conv_rhs => simp only [WeierstrassCurve.Affine.addX, twoIsogenousModel, twoTorsionModel, zero_mul, add_zero]
    linear_combination hS
  · change phiY b z ((twoTorsionModel a b).toAffine.addY x₁ x₂ y₁ m) =
      (twoIsogenousModel a b).toAffine.addY _ _ (phiY b x₁ y₁) (m-b/n)
    rw [hw]
    conv_rhs => simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX,
      twoIsogenousModel, twoTorsionModel, zero_mul, sub_zero, add_zero]
    have hneg : phiY b z (-(m*z+n)) = -phiY b z (m*z+n) := by unfold phiY; ring
    rw [hneg]
    linear_combination -hL₃ + hL₁ - (m-b/n)*hS

theorem twoTorsion_add_torsion_coordinates {a b x y : ℚ} (hx : x ≠ 0)
    (h : OnCurve a b x y) :
    let m := (twoTorsionModel a b).toAffine.slope x 0 y 0
    (twoTorsionModel a b).toAffine.addX x 0 m = b/x ∧
    (twoTorsionModel a b).toAffine.addY x 0 y m = -b*y/x^2 := by
  dsimp only
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
  simp only [sub_zero]
  have hz : (twoTorsionModel a b).toAffine.addX x 0 (y/x)=b/x := by
    simp only [WeierstrassCurve.Affine.addX, twoTorsionModel, zero_mul, add_zero, sub_zero]
    unfold OnCurve at h
    field_simp [hx]
    linear_combination h
  refine ⟨hz, ?_⟩
  simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.negAddY]
  rw [hz]
  simp only [twoTorsionModel, zero_mul, sub_zero]
  field_simp [hx]
  ring

theorem phiPoint_add_torsion_right (a b : ℚ) (hb : b ≠ 0) (hc : c a b ≠ 0)
    {x y : ℚ} (hx : x ≠ 0)
    (hP : (twoTorsionModel a b).toAffine.Nonsingular x y)
    (hT : (twoTorsionModel a b).toAffine.Nonsingular 0 0) :
    phiPoint a b hb hc (.some x y hP + .some 0 0 hT) =
      phiPoint a b hb hc (.some x y hP) := by
  have he := (onCurve_iff_equation a b x y).mpr hP.1
  have hcoord := twoTorsion_add_torsion_coordinates hx he
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx]
  simp only [phiPoint, hcoord.1, dite_eq_right (div_ne_zero hb hx), dite_eq_right hx]
  have ht := phi_torsion_translate (a := a) (y := y) hx hb
  exact affine_some_eq ht.1 (by rw [hcoord.2]; exact ht.2)

theorem phi_intercept_zero (a b : ℚ)
    {x₁ x₂ y₁ y₂ : ℚ} (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0)
    (h₁ : (twoTorsionModel a b).toAffine.Equation x₁ y₁)
    (h₂ : (twoTorsionModel a b).toAffine.Equation x₂ y₂)
    (hxy : ¬ (x₁=x₂ ∧ y₁=(twoTorsionModel a b).toAffine.negY x₂ y₂))
    (hn : y₁-(twoTorsionModel a b).toAffine.slope x₁ x₂ y₁ y₂*x₁ = 0) :
    (twoTorsionModel a b).toAffine.addX x₁ x₂
      ((twoTorsionModel a b).toAffine.slope x₁ x₂ y₁ y₂)=0 ∧
    phiX a b x₁=phiX a b x₂ ∧ phiY b x₁ y₁= -phiY b x₂ y₂ := by
  let m := (twoTorsionModel a b).toAffine.slope x₁ x₂ y₁ y₂
  let z := (twoTorsionModel a b).toAffine.addX x₁ x₂ m
  have hprod : x₁*x₂*z=0 := by
    have hp := twoTorsion_chord_product a b h₁ h₂ hxy
    change x₁*x₂*z=(y₁-m*x₁)^2 at hp
    rw [hn] at hp
    simpa only [zero_pow (by decide : (2:ℕ) ≠ 0)] using hp
  have hz : z=0 := (mul_eq_zero.mp hprod).resolve_left (mul_ne_zero hx₁ hx₂)
  have hb' : b=x₁*x₂ := by
    have hp := twoTorsion_chord_pair_products a b h₁ h₂ hxy
    change x₁*x₂+x₁*z+x₂*z=b-2*m*(y₁-m*x₁) at hp
    rw [hz, hn] at hp
    simpa only [mul_zero, zero_add, add_zero, sub_zero] using hp.symm
  have hl₁ : y₁=m*x₁ := sub_eq_zero.mp hn
  have hl₂ : y₂=m*x₂ := by
    have hl := twoTorsion_slope_line a b h₁ h₂ hxy
    change y₂=m*x₂+(y₁-m*x₁) at hl
    rw [hn] at hl
    simpa only [add_zero] using hl
  refine ⟨hz, ?_, ?_⟩
  · simp only [phiX, hb']
    field_simp [hx₁, hx₂]
    ring
  · rw [hl₁, hl₂, hb']
    unfold phiY
    field_simp [hx₁, hx₂]
    ring

theorem phiPoint_add (a b : ℚ) (hb : b ≠ 0) (hc : c a b ≠ 0)
    (P Q : (twoTorsionModel a b).toAffine.Point) :
    phiPoint a b hb hc (P+Q)=phiPoint a b hb hc P+phiPoint a b hb hc Q := by
  cases P with
  | zero => simp [← WeierstrassCurve.Affine.Point.zero_def]
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero => simp [← WeierstrassCurve.Affine.Point.zero_def]
    | some x₂ y₂ h₂ =>
      by_cases hx₁ : x₁=0
      · subst x₁
        have hy₁ : y₁=0 := by
          have he := (onCurve_iff_equation a b 0 y₁).mpr h₁.1
          simpa [OnCurve] using he
        subst y₁
        by_cases hx₂ : x₂=0
        · subst x₂
          have hy₂ : y₂=0 := by
            have he := (onCurve_iff_equation a b 0 y₂).mpr h₂.1
            simpa [OnCurve] using he
          subst y₂
          rw [WeierstrassCurve.Affine.Point.add_of_Y_eq rfl (by simp [twoTorsionModel])]
          simp [phiPoint, ← WeierstrassCurve.Affine.Point.zero_def]
        · rw [add_comm]
          have h := phiPoint_add_torsion_right a b hb hc hx₂ h₂ h₁
          simpa only [phiPoint, dite_true,
            ← WeierstrassCurve.Affine.Point.zero_def, zero_add] using h
      · by_cases hx₂ : x₂=0
        · subst x₂
          have hy₂ : y₂=0 := by
            have he := (onCurve_iff_equation a b 0 y₂).mpr h₂.1
            simpa [OnCurve] using he
          subst y₂
          have h := phiPoint_add_torsion_right a b hb hc hx₁ h₁ h₂
          simpa only [phiPoint, dite_true,
            ← WeierstrassCurve.Affine.Point.zero_def, add_zero] using h
        · by_cases hxy : x₁=x₂ ∧ y₁=(twoTorsionModel a b).toAffine.negY x₂ y₂
          · rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hxy.1 hxy.2]
            simp only [phiPoint, dite_eq_right hx₁, dite_eq_right hx₂]
            have hy : phiY b x₁ y₁=(twoIsogenousModel a b).toAffine.negY (phiX a b x₂) (phiY b x₂ y₂) := by
              have hy' : y₁ = -y₂ := by
                simpa [twoTorsionModel] using hxy.2
              simp only [twoIsogenousModel, twoTorsionModel,
                WeierstrassCurve.Affine.negY, zero_mul, sub_zero]
              rw [hxy.1, hy']
              unfold phiY
              ring
            rw [WeierstrassCurve.Affine.Point.add_of_Y_eq (congrArg (phiX a b) hxy.1) hy]
            rfl
          · by_cases hn : y₁-(twoTorsionModel a b).toAffine.slope x₁ x₂ y₁ y₂*x₁=0
            · have hz := phi_intercept_zero a b hx₁ hx₂ h₁.1 h₂.1 hxy hn
              rw [WeierstrassCurve.Affine.Point.add_some hxy]
              simp only [phiPoint, dite_eq_left hz.1, dite_eq_right hx₁, dite_eq_right hx₂]
              have hy : phiY b x₁ y₁=(twoIsogenousModel a b).toAffine.negY (phiX a b x₂) (phiY b x₂ y₂) := by
                simpa [twoIsogenousModel, twoTorsionModel] using hz.2.2
              rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hz.2.1 hy]
              rfl
            · have hprod := twoTorsion_chord_product a b h₁.1 h₂.1 hxy
              have hz : (twoTorsionModel a b).toAffine.addX x₁ x₂
                  ((twoTorsionModel a b).toAffine.slope x₁ x₂ y₁ y₂) ≠ 0 := by
                intro hz
                apply pow_ne_zero 2 hn
                rw [hz] at hprod
                simpa only [mul_zero] using hprod.symm
              have hslope := phi_slope a b hb hc hx₁ hx₂ h₁.1 h₂.1 hxy hn
              have hcoord := phi_add_coordinates a b hb hc hx₁ hx₂ h₁.1 h₂.1 hxy hn
              rw [WeierstrassCurve.Affine.Point.add_some hxy]
              simp only [phiPoint, dite_eq_right hz, dite_eq_right hx₁, dite_eq_right hx₂]
              rw [WeierstrassCurve.Affine.Point.add_some hslope.2]
              exact affine_some_eq hcoord.1 hcoord.2

def phiPointHom (a b : ℚ) (hb : b ≠ 0) (hc : c a b ≠ 0) :
    (twoTorsionModel a b).toAffine.Point →+ (twoIsogenousModel a b).toAffine.Point where
  toFun := phiPoint a b hb hc
  map_zero' := rfl
  map_add' := phiPoint_add a b hb hc

end RankCertificates.Isogeny
