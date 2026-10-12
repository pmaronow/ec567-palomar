module

public import RankCertificates.Common

@[expose] public section

/-!
# Exact algebraic certificates for the rank-six family

This file verifies the explicit equations and rational points appearing in
`research/rank6/paper/rank6_infinitude.tex`.  Its conclusions concern genuine
Weierstrass curves and their discriminants.  It does not assert a
Mordell–Weil rank or the infinitude of prime specializations.
-/

namespace RankCertificates.Rank6

def L0 (M _N : ℚ) : ℚ := M
def L1 (_M N : ℚ) : ℚ := N
def L2 (M N : ℚ) : ℚ := 169 * M + 750 * N
def L3 (M N : ℚ) : ℚ := 25 * M - 169 * N
def L4 (M N : ℚ) : ℚ := M - 27 * N
def L5 (M N : ℚ) : ℚ := 7 * M + 20 * N
def L6 (M N : ℚ) : ℚ := 2 * M - 21 * N
def L7 (M N : ℚ) : ℚ := 9 * M + 10 * N
def L8 (M N : ℚ) : ℚ := M + 15 * N
def L9 (M N : ℚ) : ℚ := 7 * M + 64 * N
def L10 (M N : ℚ) : ℚ := M - 2 * N
def L11 (M N : ℚ) : ℚ := 32 * M - 105 * N

def F (M N : ℚ) : ℚ := L0 M N * L1 M N * L2 M N * L3 M N
def H (M N : ℚ) : ℚ := L4 M N * L5 M N * L6 M N * L7 M N
def J (M N : ℚ) : ℚ := L8 M N * L9 M N * L10 M N * L11 M N

theorem quartic_identity (M N : ℚ) : 25 * F M N + 16 * H M N = 9 * J M N := by
  simp only [F, H, J, L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L11]
  ring

theorem forms_positive (M N : ℚ) (hN : 0 < N) (hM : 29 * N < M) :
    0 < L0 M N ∧ 0 < L1 M N ∧ 0 < L2 M N ∧ 0 < L3 M N ∧
    0 < L4 M N ∧ 0 < L5 M N ∧ 0 < L6 M N ∧ 0 < L7 M N ∧
    0 < L8 M N ∧ 0 < L9 M N ∧ 0 < L10 M N ∧ 0 < L11 M N := by
  simp only [L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L11]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem products_positive (M N : ℚ) (hN : 0 < N) (hM : 29 * N < M) :
    0 < F M N ∧ 0 < H M N ∧ 0 < J M N := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    forms_positive M N hN hM
  exact ⟨mul_pos (mul_pos (mul_pos h0 h1) h2) h3,
    mul_pos (mul_pos (mul_pos h4 h5) h6) h7,
    mul_pos (mul_pos (mul_pos h8 h9) h10) h11⟩

def a (M N : ℚ) : ℚ := 70 * F M N
def b (M N : ℚ) : ℚ := -784 * F M N * H M N
def c (M N : ℚ) : ℚ := 1764 * F M N * J M N

def E (M N : ℚ) : WeierstrassCurve ℚ := model (a M N) (b M N)
def E' (M N : ℚ) : WeierstrassCurve ℚ := model (-2 * a M N) (c M N)

theorem isogeny_coefficient_identity (M N : ℚ) :
    (a M N) ^ 2 - 4 * b M N = c M N := by
  simp only [a, b, c]
  linear_combination 196 * F M N * quartic_identity M N

theorem discriminant_E (M N : ℚ) :
    (E M N).Δ = 16 * (b M N) ^ 2 * c M N := by
  simp only [E]
  rw [model_discriminant, isogeny_coefficient_identity]

theorem discriminant_E' (M N : ℚ) :
    (E' M N).Δ = 256 * (c M N) ^ 2 * b M N := by
  simp only [E']
  rw [model_discriminant]
  rw [← isogeny_coefficient_identity M N]
  ring

theorem c4_E (M N : ℚ) :
    (E M N).c₄ = 3136 * F M N * (25 * F M N + 12 * H M N) := by
  simp only [E]
  rw [model_c4]
  simp only [a, b]
  ring

theorem c4_E' (M N : ℚ) :
    (E' M N).c₄ = 3136 * F M N * (100 * F M N - 27 * J M N) := by
  simp only [E']
  rw [model_c4]
  simp only [a, c]
  ring

theorem discriminant_E_ne_zero (M N : ℚ)
    (hF : F M N ≠ 0) (hH : H M N ≠ 0) (hJ : J M N ≠ 0) :
    (E M N).Δ ≠ 0 := by
  rw [discriminant_E]
  simp only [b, c]
  exact mul_ne_zero (mul_ne_zero (by norm_num)
    (pow_ne_zero _ (mul_ne_zero (mul_ne_zero (by norm_num) hF) hH)))
    (mul_ne_zero (mul_ne_zero (by norm_num) hF) hJ)

theorem discriminant_E'_ne_zero (M N : ℚ)
    (hF : F M N ≠ 0) (hH : H M N ≠ 0) (hJ : J M N ≠ 0) :
    (E' M N).Δ ≠ 0 := by
  rw [discriminant_E']
  simp only [b, c]
  exact mul_ne_zero (mul_ne_zero (by norm_num)
    (pow_ne_zero _ (mul_ne_zero (mul_ne_zero (by norm_num) hF) hJ)))
    (mul_ne_zero (mul_ne_zero (by norm_num) hF) hH)

theorem elliptic_E (M N : ℚ)
    (hF : F M N ≠ 0) (hH : H M N ≠ 0) (hJ : J M N ≠ 0) :
    (E M N).IsElliptic := by
  exact ⟨isUnit_iff_ne_zero.mpr (discriminant_E_ne_zero M N hF hH hJ)⟩

theorem elliptic_E' (M N : ℚ)
    (hF : F M N ≠ 0) (hH : H M N ≠ 0) (hJ : J M N ≠ 0) :
    (E' M N).IsElliptic := by
  exact ⟨isUnit_iff_ne_zero.mpr (discriminant_E'_ne_zero M N hF hH hJ)⟩

theorem elliptic_pair_of_product_ne_zero (M N : ℚ)
    (h : F M N * H M N * J M N ≠ 0) :
    (E M N).IsElliptic ∧ (E' M N).IsElliptic := by
  obtain ⟨hFH, hJ⟩ := mul_ne_zero_iff.mp h
  obtain ⟨hF, hH⟩ := mul_ne_zero_iff.mp hFH
  exact ⟨elliptic_E M N hF hH hJ, elliptic_E' M N hF hH hJ⟩

theorem elliptic_pair_in_cone (M N : ℚ) (hN : 0 < N) (hM : 29 * N < M) :
    (E M N).IsElliptic ∧ (E' M N).IsElliptic := by
  obtain ⟨hF, hH, hJ⟩ := products_positive M N hN hM
  exact ⟨elliptic_E M N (ne_of_gt hF) (ne_of_gt hH) (ne_of_gt hJ),
    elliptic_E' M N (ne_of_gt hF) (ne_of_gt hH) (ne_of_gt hJ)⟩

def d (M N : ℚ) : ℚ := M ^ 2 + 30 * N ^ 2
def T (M N : ℚ) : ℚ := 25 * M ^ 2 - 338 * M * N - 750 * N ^ 2
def B1 (M N : ℚ) : ℚ := 52 * M ^ 2 + 375 * M * N - 975 * N ^ 2
def B2 (M N : ℚ) : ℚ := 39 * M ^ 2 - 500 * M * N + 4550 * N ^ 2

def z (M N : ℚ) : ℚ := -169 * M ^ 2 - 1500 * M * N + 5070 * N ^ 2

theorem conic_identity (M N : ℚ) :
    (z M N) ^ 2 = 47311 * (d M N) ^ 2 - 30 * (T M N) ^ 2 := by
  simp only [z, d, T]
  ring

theorem pullback_F (M N : ℚ) :
    (T M N) ^ 2 - 625 * (d M N) ^ 2 = -4 * F M N := by
  simp only [T, d, F, L0, L1, L2, L3]
  ring

theorem pullback_H (M N : ℚ) :
    (T M N) ^ 2 - 121 * (d M N) ^ 2 = 4 * H M N := by
  simp only [T, d, H, L4, L5, L6, L7]
  ring

theorem pullback_J (M N : ℚ) :
    (T M N) ^ 2 - 1521 * (d M N) ^ 2 = -4 * J M N := by
  simp only [T, d, J, L8, L9, L10, L11]
  ring

def P1x (M N : ℚ) : ℚ := 14 * H M N
def P1y (M N : ℚ) : ℚ := P1x M N * (42 * d M N)
def P2x (M N : ℚ) : ℚ := -2 * L1 M N * L2 M N * L4 M N * L5 M N
def P2y (M N : ℚ) : ℚ := P2x M N * (3 * (3 * T M N + 65 * d M N))
def P3x (M N : ℚ) : ℚ := -175 * L1 M N * L3 M N * L4 M N * L6 M N
def P3y (M N : ℚ) : ℚ := P3x M N * ((21 / 5 : ℚ) * B1 M N)

def Q1x (M N : ℚ) : ℚ := 14 * F M N
def Q1y (M N : ℚ) : ℚ := Q1x M N * (-168 * d M N)
def Q2x (M N : ℚ) : ℚ := 2 * L0 M N * L3 M N * L10 M N * L11 M N
def Q2y (M N : ℚ) : ℚ := Q2x M N * (8 * (2 * T M N - 55 * d M N))
def Q3x (M N : ℚ) : ℚ := (18 / 25 : ℚ) * L0 M N * L2 M N * L8 M N * L11 M N
def Q3y (M N : ℚ) : ℚ := Q3x M N * ((8 / 5 : ℚ) * B2 M N)

theorem P1_onCurve (M N : ℚ) : OnCurve (a M N) (b M N) (P1x M N) (P1y M N) := by
  simp only [OnCurve, a, b, F, H, P1x, P1y, d, L0, L1, L2, L3, L4, L5, L6, L7]
  ring

theorem P2_onCurve (M N : ℚ) : OnCurve (a M N) (b M N) (P2x M N) (P2y M N) := by
  simp only [OnCurve, a, b, F, H, P2x, P2y, d, T, L0, L1, L2, L3, L4, L5, L6, L7]
  ring

theorem P3_onCurve (M N : ℚ) : OnCurve (a M N) (b M N) (P3x M N) (P3y M N) := by
  simp only [OnCurve, a, b, F, H, P3x, P3y, B1, L0, L1, L2, L3, L4, L5, L6, L7]
  ring

theorem Q1_onCurve (M N : ℚ) : OnCurve (-2 * a M N) (c M N) (Q1x M N) (Q1y M N) := by
  simp only [OnCurve, a, c, F, J, Q1x, Q1y, d, L0, L1, L2, L3, L8, L9, L10, L11]
  ring

theorem Q2_onCurve (M N : ℚ) : OnCurve (-2 * a M N) (c M N) (Q2x M N) (Q2y M N) := by
  simp only [OnCurve, a, c, F, J, Q2x, Q2y, d, T, L0, L1, L2, L3, L8, L9, L10, L11]
  ring

theorem Q3_onCurve (M N : ℚ) : OnCurve (-2 * a M N) (c M N) (Q3x M N) (Q3y M N) := by
  simp only [OnCurve, a, c, F, J, Q3x, Q3y, B2, L0, L1, L2, L3, L8, L9, L10, L11]
  ring

def A (M N : ℚ) : ℚ := 2 * T M N - 55 * d M N
def V2 (M N : ℚ) : ℚ := L0 M N * L3 M N * L10 M N * L11 M N
def U2 (M N : ℚ) : ℚ := L1 M N * L2 M N * L8 M N * L9 M N
def V3 (M N : ℚ) : ℚ := L0 M N * L2 M N * L8 M N * L11 M N
def U3 (M N : ℚ) : ℚ := L1 M N * L3 M N * L9 M N * L10 M N

def R1x (M N : ℚ) : ℚ := 7056 * (d M N) ^ 2
def R1y (M N : ℚ) : ℚ := 294 * d M N * (9 * J M N - F M N)
def R2x (M N : ℚ) : ℚ := 16 * (A M N) ^ 2
def R2y (M N : ℚ) : ℚ := 2 * A M N * (V2 M N - 441 * U2 M N)
def R3x (M N : ℚ) : ℚ := (16 / 25 : ℚ) * (B2 M N) ^ 2
def R3y (M N : ℚ) : ℚ := (2 / 125 : ℚ) * B2 M N * (9 * V3 M N - 30625 * U3 M N)

theorem R1_onCurve (M N : ℚ) : OnCurve (a M N) (b M N) (R1x M N) (R1y M N) := by
  simp only [OnCurve, a, b, F, H, J, R1x, R1y, d, L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L11]
  ring

theorem R2_onCurve (M N : ℚ) : OnCurve (a M N) (b M N) (R2x M N) (R2y M N) := by
  simp only [OnCurve, a, b, F, H, R2x, R2y, A, d, T, V2, U2, L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L11]
  ring

theorem R3_onCurve (M N : ℚ) : OnCurve (a M N) (b M N) (R3x M N) (R3y M N) := by
  simp only [OnCurve, a, b, F, H, R3x, R3y, B2, V3, U3, L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L11]
  ring

/- The following polynomial identities express the rational dual-map formulas
after clearing denominators.  They hold even at parameters where Qᵢ.x = 0. -/

theorem dual_Q1_x_cleared (M N : ℚ) :
    (Q1y M N) ^ 2 = 4 * (Q1x M N) ^ 2 * R1x M N := by
  simp only [Q1x, Q1y, R1x]
  ring

theorem dual_Q2_x_cleared (M N : ℚ) :
    (Q2y M N) ^ 2 = 4 * (Q2x M N) ^ 2 * R2x M N := by
  simp only [Q2y, R2x, A]
  ring

theorem dual_Q3_x_cleared (M N : ℚ) :
    (Q3y M N) ^ 2 = 4 * (Q3x M N) ^ 2 * R3x M N := by
  simp only [Q3y, R3x]
  ring

theorem dual_Q1_y_cleared (M N : ℚ) :
    Q1y M N * ((Q1x M N) ^ 2 - c M N) =
      8 * (Q1x M N) ^ 2 * R1y M N := by
  simp only [Q1x, Q1y, R1y, c]
  ring

theorem dual_Q2_y_cleared (M N : ℚ) :
    Q2y M N * ((Q2x M N) ^ 2 - c M N) =
      8 * (Q2x M N) ^ 2 * R2y M N := by
  simp only [Q2x, Q2y, R2y, A, c, F, J, V2, U2, L0, L1, L2, L3, L8, L9, L10, L11]
  ring

theorem dual_Q3_y_cleared (M N : ℚ) :
    Q3y M N * ((Q3x M N) ^ 2 - c M N) =
      8 * (Q3x M N) ^ 2 * R3y M N := by
  simp only [Q3x, Q3y, R3y, c, F, J, V3, U3, L0, L1, L2, L3, L8, L9, L10, L11]
  ring

private theorem dual_x_of_cleared {x y u : ℚ} (hx : x ≠ 0)
    (h : y ^ 2 = 4 * x ^ 2 * u) : y ^ 2 / (4 * x ^ 2) = u := by
  apply (div_eq_iff (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx))).mpr
  linear_combination h

private theorem dual_y_of_cleared {x y v β : ℚ} (hx : x ≠ 0)
    (h : y * (x ^ 2 - β) = 8 * x ^ 2 * v) :
    y / 8 * (1 - β / x ^ 2) = v := by
  field_simp
  linear_combination h

theorem dual_Q1_coordinates (M N : ℚ) (hx : Q1x M N ≠ 0) :
    (Q1y M N) ^ 2 / (4 * (Q1x M N) ^ 2) = R1x M N ∧
    Q1y M N / 8 * (1 - c M N / (Q1x M N) ^ 2) = R1y M N :=
  ⟨dual_x_of_cleared hx (dual_Q1_x_cleared M N),
    dual_y_of_cleared hx (dual_Q1_y_cleared M N)⟩

theorem dual_Q2_coordinates (M N : ℚ) (hx : Q2x M N ≠ 0) :
    (Q2y M N) ^ 2 / (4 * (Q2x M N) ^ 2) = R2x M N ∧
    Q2y M N / 8 * (1 - c M N / (Q2x M N) ^ 2) = R2y M N :=
  ⟨dual_x_of_cleared hx (dual_Q2_x_cleared M N),
    dual_y_of_cleared hx (dual_Q2_y_cleared M N)⟩

theorem dual_Q3_coordinates (M N : ℚ) (hx : Q3x M N ≠ 0) :
    (Q3y M N) ^ 2 / (4 * (Q3x M N) ^ 2) = R3x M N ∧
    Q3y M N / 8 * (1 - c M N / (Q3x M N) ^ 2) = R3y M N :=
  ⟨dual_x_of_cleared hx (dual_Q3_x_cleared M N),
    dual_y_of_cleared hx (dual_Q3_y_cleared M N)⟩

theorem six_E_points_nonsingular (M N : ℚ)
    (hF : F M N ≠ 0) (hH : H M N ≠ 0) (hJ : J M N ≠ 0) :
    (E M N).toAffine.Nonsingular (P1x M N) (P1y M N) ∧
    (E M N).toAffine.Nonsingular (P2x M N) (P2y M N) ∧
    (E M N).toAffine.Nonsingular (P3x M N) (P3y M N) ∧
    (E M N).toAffine.Nonsingular (R1x M N) (R1y M N) ∧
    (E M N).toAffine.Nonsingular (R2x M N) (R2y M N) ∧
    (E M N).toAffine.Nonsingular (R3x M N) (R3y M N) := by
  have hΔ := discriminant_E_ne_zero M N hF hH hJ
  exact ⟨onCurve_nonsingular hΔ (P1_onCurve M N),
    onCurve_nonsingular hΔ (P2_onCurve M N),
    onCurve_nonsingular hΔ (P3_onCurve M N),
    onCurve_nonsingular hΔ (R1_onCurve M N),
    onCurve_nonsingular hΔ (R2_onCurve M N),
    onCurve_nonsingular hΔ (R3_onCurve M N)⟩

theorem three_E'_points_nonsingular (M N : ℚ)
    (hF : F M N ≠ 0) (hH : H M N ≠ 0) (hJ : J M N ≠ 0) :
    (E' M N).toAffine.Nonsingular (Q1x M N) (Q1y M N) ∧
    (E' M N).toAffine.Nonsingular (Q2x M N) (Q2y M N) ∧
    (E' M N).toAffine.Nonsingular (Q3x M N) (Q3y M N) := by
  have hΔ := discriminant_E'_ne_zero M N hF hH hJ
  exact ⟨onCurve_nonsingular hΔ (Q1_onCurve M N),
    onCurve_nonsingular hΔ (Q2_onCurve M N),
    onCurve_nonsingular hΔ (Q3_onCurve M N)⟩

theorem j_E (M N : ℚ) [(E M N).IsElliptic]
    (hF : F M N ≠ 0) (hH : H M N ≠ 0) (hJ : J M N ≠ 0) :
    (E M N).j = (16 / 9 : ℚ) * (25 * F M N + 12 * H M N) ^ 3 /
      ((H M N) ^ 2 * J M N) := by
  rw [WeierstrassCurve.j_eq, discriminant_E, c4_E]
  simp only [b, c]
  field_simp
  ring

theorem j_E' (M N : ℚ) [(E' M N).IsElliptic]
    (hF : F M N ≠ 0) (hH : H M N ≠ 0) (hJ : J M N ≠ 0) :
    (E' M N).j = (-4 / 81 : ℚ) * (100 * F M N - 27 * J M N) ^ 3 /
      (H M N * (J M N) ^ 2) := by
  rw [WeierstrassCurve.j_eq, discriminant_E', c4_E']
  simp only [b, c]
  field_simp
  ring

/-- The rational expression for the invariant, defined also at singular parameters. -/
def invariantFraction (M N : ℚ) : ℚ :=
  (16 / 9 : ℚ) * (25 * F M N + 12 * H M N) ^ 3 / ((H M N) ^ 2 * J M N)

theorem invariantFraction_distinct : invariantFraction 30 1 ≠ invariantFraction 31 1 := by
  norm_num [invariantFraction, F, H, J, L0, L1, L2, L3, L4, L5, L6, L7,
    L8, L9, L10, L11]

theorem invariantFraction_nonconstant :
    ¬ ∃ v : ℚ, ∀ t : ℚ, invariantFraction t 1 = v := by
  rintro ⟨v, hv⟩
  exact invariantFraction_distinct ((hv 30).trans (hv 31).symm)

theorem homogeneous_F (scale M N : ℚ) :
    F (scale * M) (scale * N) = scale ^ 4 * F M N := by
  simp only [F, L0, L1, L2, L3]
  ring

theorem homogeneous_H (scale M N : ℚ) :
    H (scale * M) (scale * N) = scale ^ 4 * H M N := by
  simp only [H, L4, L5, L6, L7]
  ring

theorem homogeneous_J (scale M N : ℚ) :
    J (scale * M) (scale * N) = scale ^ 4 * J M N := by
  simp only [J, L8, L9, L10, L11]
  ring

theorem homogeneous_a (scale M N : ℚ) :
    a (scale * M) (scale * N) = scale ^ 4 * a M N := by
  simp only [a, homogeneous_F]
  ring

theorem homogeneous_b (scale M N : ℚ) :
    b (scale * M) (scale * N) = scale ^ 8 * b M N := by
  simp only [b, homogeneous_F, homogeneous_H]
  ring

theorem homogeneous_c (scale M N : ℚ) :
    c (scale * M) (scale * N) = scale ^ 8 * c M N := by
  simp only [c, homogeneous_F, homogeneous_J]
  ring

theorem scale_onCurve (scale M N x y : ℚ) (h : OnCurve (a M N) (b M N) x y) :
    OnCurve (a (scale * M) (scale * N)) (b (scale * M) (scale * N))
      (scale ^ 4 * x) (scale ^ 6 * y) := by
  rw [homogeneous_a, homogeneous_b]
  simp only [OnCurve] at h ⊢
  linear_combination scale ^ 12 * h

def W : ℤ := 780373440
def M0 : ℤ := 416513683
def N0 : ℤ := 91046603

theorem crt_modulus : W = 64 * 81 * 7 * 5 * 11 * 17 * 23 := by
  norm_num [W]

theorem crt_residues :
    M0 % 64 = 19 ∧ N0 % 64 = 11 ∧ M0 % 81 = 19 ∧ N0 % 81 = 11 ∧
    M0 % 7 = 5 ∧ N0 % 7 = 4 ∧ M0 % 5 = 3 ∧ N0 % 5 = 3 ∧
    M0 % 11 = 3 ∧ N0 % 11 = 10 ∧ M0 % 17 = 15 ∧ N0 % 17 = 9 ∧
    M0 % 23 = 13 ∧ N0 % 23 = 22 := by
  norm_num [M0, N0]

end RankCertificates.Rank6
