module

public import RankCertificates.Common
public import RankCertificates.Kummer

/-!
# Rational coordinate identities for a two-isogeny pair

The coordinate identities give genuine rational points. The dual map extends
across infinity and the zero coordinate as a point-set function, and its
range is proved equal to the kernel of the Kummer homomorphism. This module
does not prove that the dual map is a group homomorphism, establish its
composition with the other map as doubling, or assert a rank formula.
-/

@[expose] public section

namespace RankCertificates.Isogeny

def c (a b : ℚ) : ℚ := a ^ 2 - 4 * b

def phiX (a b x : ℚ) : ℚ := x + a + b / x
def phiY (b x y : ℚ) : ℚ := y * (1 - b / x ^ 2)
def psiX (X Y : ℚ) : ℚ := Y ^ 2 / (4 * X ^ 2)
def psiY (a b X Y : ℚ) : ℚ := Y / 8 * (1 - c a b / X ^ 2)

/-- The displayed original-to-partner coordinates satisfy the partner equation. -/
theorem phi_onCurve {a b x y : ℚ} (hx : x ≠ 0) (h : OnCurve a b x y) :
    OnCurve (-2 * a) (c a b) (phiX a b x) (phiY b x y) := by
  unfold OnCurve at h ⊢
  unfold phiX phiY c
  field_simp [hx]
  linear_combination (x ^ 2 - b) ^ 2 * h

theorem phiX_square {a b x y : ℚ} (hx : x ≠ 0) (h : OnCurve a b x y) :
    phiX a b x = (y / x) ^ 2 := by
  unfold OnCurve at h
  unfold phiX
  field_simp [hx]
  linear_combination -h

/-- The displayed partner-to-original coordinates satisfy the original equation. -/
theorem psi_onCurve {a b X Y : ℚ} (hX : X ≠ 0)
    (h : OnCurve (-2 * a) (c a b) X Y) :
    OnCurve a b (psiX X Y) (psiY a b X Y) := by
  unfold OnCurve at h ⊢
  unfold psiX psiY c at *
  field_simp [hX]
  linear_combination -64 * Y ^ 2 * (Y ^ 2 + X ^ 3 + 2 * a * X ^ 2 +
    (a ^ 2 - 4 * b) * X) * h

def preimageX (a s y : ℚ) : ℚ := a + 2 * s ^ 2 + 2 * y / s
def preimageY (a s y : ℚ) : ℚ := 2 * s * preimageX a s y

/-- The elementary quadratic identity used to lift a square `x`-coordinate. -/
theorem preimage_quadratic {a b s y : ℚ} (hs : s ≠ 0)
    (h : OnCurve a b (s ^ 2) y) :
    preimageX a s y ^ 2 - (2 * a + 4 * s ^ 2) * preimageX a s y + c a b = 0 := by
  unfold OnCurve at h
  unfold preimageX c
  field_simp [hs]
  linear_combination 4 * h

theorem preimage_linear {a s y : ℚ} (hs : s ≠ 0) :
    s * preimageX a s y = s * (a + 2 * s ^ 2) + 2 * y := by
  unfold preimageX
  field_simp [hs]

/-- The explicit lift is a rational point of the partner equation. -/
theorem preimage_onCurve {a b s y : ℚ} (hs : s ≠ 0)
    (h : OnCurve a b (s ^ 2) y) :
    OnCurve (-2 * a) (c a b) (preimageX a s y) (preimageY a s y) := by
  have hq := preimage_quadratic hs h
  unfold OnCurve preimageY
  linear_combination -preimageX a s y * hq

/-- Nonsquare discriminant is not needed here: nonzero `c` already ensures
that the displayed lift has a nonzero coordinate. -/
theorem preimageX_ne_zero {a b s y : ℚ} (hs : s ≠ 0) (hc : c a b ≠ 0)
    (h : OnCurve a b (s ^ 2) y) : preimageX a s y ≠ 0 := by
  intro hx
  have hq := preimage_quadratic hs h
  apply hc
  simpa [hx] using hq

/-- The dual coordinate formula returns the original square coordinate. -/
theorem psi_preimage_x {a b s y : ℚ} (hs : s ≠ 0) (hc : c a b ≠ 0)
    (h : OnCurve a b (s ^ 2) y) :
    psiX (preimageX a s y) (preimageY a s y) = s ^ 2 := by
  have hx := preimageX_ne_zero hs hc h
  unfold psiX preimageY
  field_simp [hx]
  ring

/-- The sign in the explicit lift makes the dual formula return exactly `y`. -/
theorem psi_preimage_y {a b s y : ℚ} (hs : s ≠ 0) (hc : c a b ≠ 0)
    (h : OnCurve a b (s ^ 2) y) :
    psiY a b (preimageX a s y) (preimageY a s y) = y := by
  have hx := preimageX_ne_zero hs hc h
  have hq := preimage_quadratic hs h
  have hl := preimage_linear (a := a) (y := y) hs
  unfold psiY preimageY
  field_simp [hx]
  linear_combination -2 * s * hq + 4 * preimageX a s y * hl

/-- A point with nonzero square coordinate has the displayed rational lift. -/
theorem square_coordinate_has_preimage {a b s y : ℚ} (hs : s ≠ 0) (hc : c a b ≠ 0)
    (h : OnCurve a b (s ^ 2) y) :
    ∃ X Y : ℚ, X ≠ 0 ∧ OnCurve (-2 * a) (c a b) X Y ∧
      psiX X Y = s ^ 2 ∧ psiY a b X Y = y :=
  ⟨preimageX a s y, preimageY a s y, preimageX_ne_zero hs hc h,
    preimage_onCurve hs h, psi_preimage_x hs hc h, psi_preimage_y hs hc h⟩

/-- The first dual coordinate is literally a rational square. -/
theorem psiX_square (X Y : ℚ) : psiX X Y = (Y / (2 * X)) ^ 2 := by
  unfold psiX
  rw [div_pow, mul_pow]
  norm_num

/-- Away from the distinguished coordinate, the dual coordinate image is
exactly the rational points with square first coordinate. -/
theorem nonzero_coordinate_preimage_iff {a b x y : ℚ}
    (hc : c a b ≠ 0) (hx : x ≠ 0) (h : OnCurve a b x y) :
    (∃ X Y : ℚ, X ≠ 0 ∧ OnCurve (-2 * a) (c a b) X Y ∧
      psiX X Y = x ∧ psiY a b X Y = y) ↔ ∃ s : ℚ, x = s ^ 2 := by
  constructor
  · rintro ⟨X, Y, _, _, hxy, _⟩
    exact ⟨Y / (2 * X), hxy.symm.trans (psiX_square X Y)⟩
  · rintro ⟨s, rfl⟩
    have hs : s ≠ 0 := by
      intro hs
      apply hx
      simp [hs]
    exact square_coordinate_has_preimage hs hc h

/-- A nonzero-coordinate partner point above the distinguished original
torsion point exists exactly when `b` is a rational square. -/
theorem torsion_preimage_iff {a b : ℚ} (hc : c a b ≠ 0) :
    (∃ X : ℚ, X ≠ 0 ∧ OnCurve (-2 * a) (c a b) X 0) ↔
      ∃ s : ℚ, b = s ^ 2 := by
  constructor
  · rintro ⟨X, hx, h⟩
    have hp : X * (X ^ 2 - 2 * a * X + c a b) = 0 := by
      unfold OnCurve at h
      linear_combination -h
    have hq := (mul_eq_zero.mp hp).resolve_left hx
    refine ⟨(X - a) / 2, ?_⟩
    unfold c at hq
    field_simp
    linear_combination -hq
  · rintro ⟨s, hb⟩
    have hp : c a b = (a + 2 * s) * (a - 2 * s) := by
      unfold c
      rw [hb]
      ring
    refine ⟨a + 2 * s, ?_, ?_⟩
    · intro hx
      apply hc
      rw [hp, hx, zero_mul]
    · unfold OnCurve c
      rw [hb]
      ring

/-- The same torsion criterion including the dual formula's two coordinates. -/
theorem torsion_coordinate_preimage_iff {a b : ℚ} (hc : c a b ≠ 0) :
    (∃ X Y : ℚ, X ≠ 0 ∧ OnCurve (-2 * a) (c a b) X Y ∧
      psiX X Y = 0 ∧ psiY a b X Y = 0) ↔ ∃ s : ℚ, b = s ^ 2 := by
  constructor
  · rintro ⟨X, Y, hX, hcurve, hx, _⟩
    unfold psiX at hx
    field_simp [hX] at hx
    have hY : Y = 0 := by nlinarith [sq_nonneg Y]
    subst Y
    exact (torsion_preimage_iff hc).mp ⟨X, hX, hcurve⟩
  · intro hb
    obtain ⟨X, hX, hcurve⟩ := (torsion_preimage_iff hc).mpr hb
    refine ⟨X, 0, hX, hcurve, ?_, ?_⟩ <;> simp [psiX, psiY]

/-- The discriminant of the genuine original two-torsion model is nonzero. -/
theorem original_discriminant_ne_zero {a b : ℚ} (hb : b ≠ 0) (hc : c a b ≠ 0) :
    (twoTorsionModel a b).Δ ≠ 0 := by
  change (model a b).Δ ≠ 0
  rw [model_discriminant]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hb)) hc

theorem partner_discriminant (a b : ℚ) :
    (twoIsogenousModel a b).Δ = 256 * b * c a b ^ 2 := by
  change (model (-2 * a) (a ^ 2 - 4 * b)).Δ = _
  rw [model_discriminant]
  unfold c
  ring

theorem partner_discriminant_ne_zero {a b : ℚ} (hb : b ≠ 0) (hc : c a b ≠ 0) :
    (twoIsogenousModel a b).Δ ≠ 0 := by
  rw [partner_discriminant]
  exact mul_ne_zero (mul_ne_zero (by norm_num) hb) (pow_ne_zero 2 hc)

/-- The dual coordinate map on genuine rational points, with infinity and
the distinguished zero coordinate sent to infinity. No homomorphism
property is asserted for this map. -/
def psiPoint (a b : ℚ) (hb : b ≠ 0) (hc : c a b ≠ 0) :
    (twoIsogenousModel a b).toAffine.Point → (twoTorsionModel a b).toAffine.Point
  | .zero => .zero
  | .some X Y h => if hX : X = 0 then .zero else
      .some (psiX X Y) (psiY a b X Y)
        (onCurve_nonsingular (original_discriminant_ne_zero hb hc)
          (psi_onCurve hX ((onCurve_iff_equation (-2 * a) (c a b) X Y).mpr h.1)))

@[simp] theorem psiPoint_zero (a b : ℚ) (hb : b ≠ 0) (hc : c a b ≠ 0) :
    psiPoint a b hb hc .zero = .zero := rfl

/-- Every genuine dual-map value has trivial original Kummer class,
including the cases where either coordinate vanishes. -/
theorem psiPoint_class (a b : ℚ) (hb : b ≠ 0) (hc : c a b ≠ 0)
    (Q : (twoIsogenousModel a b).toAffine.Point) :
    twoIsogenyClass a b (psiPoint a b hb hc Q) = 1 := by
  cases Q with
  | zero => rfl
  | some X Y h =>
    by_cases hX : X = 0
    · simp [psiPoint, hX, twoIsogenyClass]
    · simp only [psiPoint, dite_eq_right hX, twoIsogenyClass]
      by_cases hz : psiX X Y = 0
      · rw [ite_eq_left hz]
        have hy : Y = 0 := by
          unfold psiX at hz
          field_simp [hX] at hz
          nlinarith [sq_nonneg Y]
        have hcurve : OnCurve (-2 * a) (c a b) X 0 := by
          have he := (onCurve_iff_equation (-2 * a) (c a b) X Y).mpr h.1
          simpa [hy] using he
        obtain ⟨s, hs⟩ := (torsion_preimage_iff hc).mp ⟨X, hX, hcurve⟩
        rw [hs, rationalSquareClass_square]
      · rw [ite_eq_right hz, psiX_square, rationalSquareClass_square]

/-- The genuine coordinate Kummer kernel equals the range of the genuine
dual point map. This identifies sets of rational points, without presuming
that `psiPoint` is a group homomorphism. -/
theorem twoIsogenyClass_eq_one_iff_range (a b : ℚ) (hb : b ≠ 0) (hc : c a b ≠ 0)
    (P : (twoTorsionModel a b).toAffine.Point) :
    twoIsogenyClass a b P = 1 ↔ P ∈ Set.range (psiPoint a b hb hc) := by
  constructor
  · intro hδ
    cases P with
    | zero => exact ⟨.zero, rfl⟩
    | some x y hp =>
      have hcurve : OnCurve a b x y := (onCurve_iff_equation a b x y).mpr hp.1
      by_cases hx : x = 0
      · subst x
        have hy : y = 0 := by
          unfold OnCurve at hcurve
          norm_num at hcurve
          exact hcurve
        subst y
        have hclass : rationalSquareClass b = 1 := by
          simpa [twoIsogenyClass] using hδ
        obtain ⟨s, _, hs⟩ := (rationalSquareClass_eq_one_iff hb).mp hclass
        obtain ⟨X, hX, hC⟩ := (torsion_preimage_iff hc).mpr ⟨s, hs⟩
        have hQ : (twoIsogenousModel a b).toAffine.Nonsingular X 0 :=
          onCurve_nonsingular (partner_discriminant_ne_zero hb hc) hC
        refine ⟨.some X 0 hQ, ?_⟩
        simp [psiPoint, hX, psiX, psiY]
      · have hclass : rationalSquareClass x = 1 := by
          simpa only [twoIsogenyClass, ite_eq_right hx] using hδ
        obtain ⟨s, hs, hxs⟩ := (rationalSquareClass_eq_one_iff hx).mp hclass
        rw [hxs] at hcurve
        obtain ⟨X, Y, hX, hC, hψX, hψY⟩ := square_coordinate_has_preimage hs hc hcurve
        have hQ : (twoIsogenousModel a b).toAffine.Nonsingular X Y :=
          onCurve_nonsingular (partner_discriminant_ne_zero hb hc) hC
        refine ⟨.some X Y hQ, ?_⟩
        simp only [psiPoint, dite_eq_right hX]
        have hxreturn : psiX X Y = x := hψX.trans hxs.symm
        cases hxreturn
        cases hψY
        rfl
  · rintro ⟨Q, rfl⟩
    exact psiPoint_class a b hb hc Q

/-- The kernel of the proved Kummer homomorphism has exactly this point-map
range as its carrier. The range itself is not declared as an isogeny
homomorphism range. -/
theorem twoIsogenyClassAddHom_kernel (a b : ℚ) (hb : b ≠ 0) (hc : c a b ≠ 0) :
    ((twoIsogenyClassAddHom a b hb).ker : Set (twoTorsionModel a b).toAffine.Point) =
      Set.range (psiPoint a b hb hc) := by
  ext P
  change twoIsogenyClass a b P = 1 ↔ _
  exact twoIsogenyClass_eq_one_iff_range a b hb hc P

end RankCertificates.Isogeny
