module

public import RankCertificates.Common
public import Mathlib.Tactic

@[expose] public section

/-!
# The coefficient-155 rank-five family: unconditional algebraic certificates

These declarations certify the explicit rational equations and sections in
`research/paper/final_rank5.tex`.  They make no assertion about Mordell–Weil
rank or simultaneous primality of the twelve linear factors.
-/

namespace RankCertificates.Rank5

def L0 (M _N : ℚ) : ℚ := M
def L1 (M N : ℚ) : ℚ := 22 * M - N
def L2 (M N : ℚ) : ℚ := 9 * M - 2 * N
def L3 (M N : ℚ) : ℚ := 143 * M + 155 * N
def L4 (M N : ℚ) : ℚ := -55 * M + 62 * N
def L5 (M N : ℚ) : ℚ := 3 * M - N
def L6 (M N : ℚ) : ℚ := 138 * M - 31 * N
def L7 (M N : ℚ) : ℚ := 55 * M + 64 * N
def L8 (M N : ℚ) : ℚ := 99 * M + 62 * N
def L9 (M N : ℚ) : ℚ := 5 * M - N
def L10 (M N : ℚ) : ℚ := 32 * M + 31 * N
def L11 (M N : ℚ) : ℚ := 55 * M - 12 * N

def F (M N : ℚ) : ℚ := L0 M N * L1 M N * L2 M N * L3 M N
def H (M N : ℚ) : ℚ := L4 M N * L5 M N * L6 M N * L7 M N
def J (M N : ℚ) : ℚ := L8 M N * L9 M N * L10 M N * L11 M N

def D (M N : ℚ) : ℚ := 62 * N ^ 2 - 226 * M * N - 165 * M ^ 2
def T (M N : ℚ) : ℚ := 1550 * N ^ 2 - 5440 * M * N - 8745 * M ^ 2
def Q (M N : ℚ) : ℚ := 1240 * N ^ 2 - 3187 * M * N - 7755 * M ^ 2
def K (M N : ℚ) : ℚ := L2 M N * L3 M N * L6 M N * L7 M N
def R (M N : ℚ) : ℚ := L1 M N * L2 M N * L8 M N * L10 M N

def a (M N : ℚ) : ℚ := 1500 * F M N
def b (M N : ℚ) : ℚ := -2700 * F M N * H M N
def c (M N : ℚ) : ℚ := 57600 * F M N * J M N

def E (M N : ℚ) : WeierstrassCurve ℚ := model (a M N) (b M N)
def E' (M N : ℚ) : WeierstrassCurve ℚ := model (-2 * a M N) (c M N)

theorem quartic_identity (M N : ℚ) : 625 * F M N + 3 * H M N = 16 * J M N := by
  dsimp [F, H, J, L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L11]
  ring

theorem isogeny_coefficient (M N : ℚ) : (a M N) ^ 2 - 4 * b M N = c M N := by
  calc
    (a M N) ^ 2 - 4 * b M N = 3600 * F M N * (625 * F M N + 3 * H M N) := by
      dsimp [a, b]
      ring
    _ = c M N := by
      rw [quartic_identity]
      dsimp [c]
      ring

def Z (M N : ℚ) : ℚ := -105 * (62 * N ^ 2 - 2728 * M * N + 5137 * M ^ 2)

theorem conic_identity (M N : ℚ) :
    (Z M N) ^ 2 = 22999 * (T M N) ^ 2 - 1412660 * T M N * D M N + 20953150 * (D M N) ^ 2 := by
  dsimp [Z, T, D]
  ring

theorem pullback_minus25 (M N : ℚ) : T M N - 25 * D M N = -210 * L0 M N * L1 M N := by
  dsimp [T, D, L0, L1]
  ring

theorem pullback_plus25 (M N : ℚ) : T M N + 25 * D M N = -10 * L2 M N * L3 M N := by
  dsimp [T, D, L2, L3]
  ring

theorem pullback_minus39 (M N : ℚ) : T M N - 39 * D M N = 14 * L4 M N * L5 M N := by
  dsimp [T, D, L4, L5]
  ring

theorem pullback_plus39 (M N : ℚ) : T M N + 39 * D M N = -2 * L6 M N * L7 M N := by
  dsimp [T, D, L6, L7]
  ring

theorem pullback_minus11 (M N : ℚ) : T M N - 11 * D M N = -14 * L8 M N * L9 M N := by
  dsimp [T, D, L8, L9]
  ring

theorem pullback_plus11 (M N : ℚ) : T M N + 11 * D M N = -6 * L10 M N * L11 M N := by
  dsimp [T, D, L10, L11]
  ring

theorem pullback_F (M N : ℚ) : (T M N) ^ 2 - 625 * (D M N) ^ 2 = 2100 * F M N := by
  dsimp [T, D, F, L0, L1, L2, L3]
  ring

theorem pullback_H (M N : ℚ) : (T M N) ^ 2 - 1521 * (D M N) ^ 2 = -28 * H M N := by
  dsimp [T, D, H, L4, L5, L6, L7]
  ring

theorem pullback_J (M N : ℚ) : (T M N) ^ 2 - 121 * (D M N) ^ 2 = 84 * J M N := by
  dsimp [T, D, J, L8, L9, L10, L11]
  ring

def P1 (M N : ℚ) : ℚ × ℚ := (-150 * F M N, 3600 * D M N * F M N)
def P2 (M N : ℚ) : ℚ × ℚ :=
  ((10 / 49 : ℚ) * K M N, (80 / 343 : ℚ) * K M N * (2 * T M N - 55 * D M N))

def P'1 (M N : ℚ) : ℚ × ℚ := (24 * J M N, 288 * D M N * J M N)
def P'2 (M N : ℚ) : ℚ × ℚ :=
  (120 * M * L1 M N * L8 M N * L9 M N,
    (720 / 7 : ℚ) * M * L1 M N * L8 M N * L9 M N * (3 * T M N + 65 * D M N))
def P'3 (M N : ℚ) : ℚ × ℚ :=
  ((1600 / 49 : ℚ) * R M N, (3200 / 343 : ℚ) * R M N * Q M N)

theorem P1_onCurve (M N : ℚ) : OnCurve (a M N) (b M N) (P1 M N).1 (P1 M N).2 := by
  dsimp [OnCurve, P1, a, b, F, H, D, L0, L1, L2, L3, L4, L5, L6, L7]
  ring

theorem P2_onCurve (M N : ℚ) : OnCurve (a M N) (b M N) (P2 M N).1 (P2 M N).2 := by
  dsimp [OnCurve, P2, a, b, F, H, D, T, K, L0, L1, L2, L3, L4, L5, L6, L7]
  ring

theorem P'1_onCurve (M N : ℚ) : OnCurve (-2 * a M N) (c M N) (P'1 M N).1 (P'1 M N).2 := by
  dsimp [OnCurve, P'1, a, c, F, J, D, L0, L1, L2, L3, L8, L9, L10, L11]
  ring

theorem P'2_onCurve (M N : ℚ) : OnCurve (-2 * a M N) (c M N) (P'2 M N).1 (P'2 M N).2 := by
  dsimp [OnCurve, P'2, a, c, F, J, D, T, L0, L1, L2, L3, L8, L9, L10, L11]
  ring

theorem P'3_onCurve (M N : ℚ) : OnCurve (-2 * a M N) (c M N) (P'3 M N).1 (P'3 M N).2 := by
  dsimp [OnCurve, P'3, a, c, F, J, R, Q, L0, L1, L2, L3, L8, L9, L10, L11]
  ring

def P (M N : ℚ) : ℚ := L0 M N * L1 M N * L8 M N * L9 M N
def S1 (M N : ℚ) : ℚ := L2 M N * L3 M N * L10 M N * L11 M N
def V (M N : ℚ) : ℚ := L0 M N * L3 M N * L9 M N * L11 M N
def A0 (M N : ℚ) : ℚ := 3 * T M N + 65 * D M N

/-- Simplified coordinates of the dual-isogeny image of `P'1`. -/
def P3 (M N : ℚ) : ℚ × ℚ := (36 * (D M N) ^ 2, 36 * D M N * (J M N - 100 * F M N))
/-- Simplified coordinates of the dual-isogeny image of `P'2`. -/
def P4 (M N : ℚ) : ℚ × ℚ :=
  ((9 / 49 : ℚ) * (A0 M N) ^ 2, (90 / 7 : ℚ) * A0 M N * (P M N - 4 * S1 M N))
/-- Simplified coordinates of the dual-isogeny image of `P'3`. -/
def P5 (M N : ℚ) : ℚ × ℚ :=
  ((Q M N) ^ 2 / 49, Q M N * (400 * R M N - 21609 * V M N) / 343)

theorem P3_onCurve (M N : ℚ) : OnCurve (a M N) (b M N) (P3 M N).1 (P3 M N).2 := by
  dsimp [OnCurve, P3, a, b, F, H, J, D, L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L11]
  ring

theorem P4_onCurve (M N : ℚ) : OnCurve (a M N) (b M N) (P4 M N).1 (P4 M N).2 := by
  dsimp [OnCurve, P4, a, b, F, H, P, S1, A0, T, D, L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L11]
  ring

theorem P5_onCurve (M N : ℚ) : OnCurve (a M N) (b M N) (P5 M N).1 (P5 M N).2 := by
  dsimp [OnCurve, P5, a, b, F, H, Q, R, V, L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L11]
  ring

/-- Rational-coordinate formula for the dual isogeny, away from `x = 0`. -/
def dualCoordinates (M N x y : ℚ) : ℚ × ℚ :=
  (y ^ 2 / (4 * x ^ 2), y * (x ^ 2 - c M N) / (8 * x ^ 2))

theorem P3_dualCoordinates (M N : ℚ) (hx : (P'1 M N).1 ≠ 0) :
    dualCoordinates M N (P'1 M N).1 (P'1 M N).2 = P3 M N := by
  apply Prod.ext
  · change (P'1 M N).2 ^ 2 / (4 * (P'1 M N).1 ^ 2) = (P3 M N).1
    apply (div_eq_iff (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx))).2
    dsimp [P3, P'1]
    ring
  · change (P'1 M N).2 * ((P'1 M N).1 ^ 2 - c M N) /
      (8 * (P'1 M N).1 ^ 2) = (P3 M N).2
    apply (div_eq_iff (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx))).2
    dsimp [P3, P'1, c]
    dsimp [F, J, D, L0, L1, L2, L3, L8, L9, L10, L11]
    ring

theorem P4_dualCoordinates (M N : ℚ) (hx : (P'2 M N).1 ≠ 0) :
    dualCoordinates M N (P'2 M N).1 (P'2 M N).2 = P4 M N := by
  apply Prod.ext
  · change (P'2 M N).2 ^ 2 / (4 * (P'2 M N).1 ^ 2) = (P4 M N).1
    apply (div_eq_iff (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx))).2
    dsimp [P4, P'2, A0]
    ring
  · change (P'2 M N).2 * ((P'2 M N).1 ^ 2 - c M N) /
      (8 * (P'2 M N).1 ^ 2) = (P4 M N).2
    apply (div_eq_iff (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx))).2
    dsimp [P4, P'2, A0, c]
    dsimp [F, J, P, S1, T, D, L0, L1, L2, L3, L8, L9, L10, L11]
    ring

theorem P5_dualCoordinates (M N : ℚ) (hx : (P'3 M N).1 ≠ 0) :
    dualCoordinates M N (P'3 M N).1 (P'3 M N).2 = P5 M N := by
  apply Prod.ext
  · change (P'3 M N).2 ^ 2 / (4 * (P'3 M N).1 ^ 2) = (P5 M N).1
    apply (div_eq_iff (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx))).2
    dsimp [P5, P'3]
    ring
  · change (P'3 M N).2 * ((P'3 M N).1 ^ 2 - c M N) /
      (8 * (P'3 M N).1 ^ 2) = (P5 M N).2
    apply (div_eq_iff (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx))).2
    dsimp [P5, P'3, c]
    dsimp [F, J, Q, R, V, L0, L1, L2, L3, L8, L9, L10, L11]
    ring

/-- Standard discriminant of `y² = x³ + ax² + bx`. -/
def discriminant (M N : ℚ) : ℚ := 16 * (b M N) ^ 2 * c M N

/-- Standard fourth Weierstrass invariant of the original curve. -/
def c4 (M N : ℚ) : ℚ := 16 * ((a M N) ^ 2 - 3 * b M N)

theorem c4_formula (M N : ℚ) :
    c4 M N = 14400 * F M N * (2500 * F M N + 9 * H M N) := by
  dsimp [c4, a, b]
  ring

theorem discriminant_ne_zero (M N : ℚ)
    (hF : F M N ≠ 0) (hH : H M N ≠ 0) (hJ : J M N ≠ 0) :
    discriminant M N ≠ 0 := by
  dsimp [discriminant, b, c]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2
    (mul_ne_zero (mul_ne_zero (by norm_num) hF) hH)))
    (mul_ne_zero (mul_ne_zero (by norm_num) hF) hJ)

theorem E_discriminant (M N : ℚ) : (E M N).Δ = discriminant M N := by
  dsimp [E, discriminant]
  rw [model_discriminant, isogeny_coefficient]

theorem E_c4 (M N : ℚ) : (E M N).c₄ = c4 M N := by
  exact model_c4 (a M N) (b M N)

theorem b_ne_zero (M N : ℚ) (hF : F M N ≠ 0) (hH : H M N ≠ 0) : b M N ≠ 0 := by
  dsimp [b]
  exact mul_ne_zero (mul_ne_zero (by norm_num) hF) hH

theorem c_ne_zero (M N : ℚ) (hF : F M N ≠ 0) (hJ : J M N ≠ 0) : c M N ≠ 0 := by
  dsimp [c]
  exact mul_ne_zero (mul_ne_zero (by norm_num) hF) hJ

theorem E_isElliptic (M N : ℚ)
    (hF : F M N ≠ 0) (hH : H M N ≠ 0) (hJ : J M N ≠ 0) : (E M N).IsElliptic := by
  apply model_isElliptic (b_ne_zero M N hF hH)
  rw [isogeny_coefficient]
  exact c_ne_zero M N hF hJ

theorem dual_isogeny_coefficient (M N : ℚ) : (-2 * a M N) ^ 2 - 4 * c M N = 16 * b M N := by
  rw [← isogeny_coefficient]
  ring

theorem E'_isElliptic (M N : ℚ)
    (hF : F M N ≠ 0) (hH : H M N ≠ 0) (hJ : J M N ≠ 0) : (E' M N).IsElliptic := by
  apply model_isElliptic (c_ne_zero M N hF hJ)
  rw [dual_isogeny_coefficient]
  exact mul_ne_zero (by norm_num) (b_ne_zero M N hF hH)

theorem E_discriminant_ne_zero (M N : ℚ)
    (hF : F M N ≠ 0) (hH : H M N ≠ 0) (hJ : J M N ≠ 0) : (E M N).Δ ≠ 0 := by
  rw [E_discriminant]
  exact discriminant_ne_zero M N hF hH hJ

theorem E'_discriminant_ne_zero (M N : ℚ)
    (hF : F M N ≠ 0) (hH : H M N ≠ 0) (hJ : J M N ≠ 0) : (E' M N).Δ ≠ 0 := by
  let _ := E'_isElliptic M N hF hH hJ
  exact isUnit_iff_ne_zero.mp (E' M N).isUnit_Δ

theorem P1_nonsingular (M N : ℚ)
    (hF : F M N ≠ 0) (hH : H M N ≠ 0) (hJ : J M N ≠ 0) :
    (E M N).toAffine.Nonsingular (P1 M N).1 (P1 M N).2 :=
  onCurve_nonsingular (E_discriminant_ne_zero M N hF hH hJ) (P1_onCurve M N)

theorem P2_nonsingular (M N : ℚ)
    (hF : F M N ≠ 0) (hH : H M N ≠ 0) (hJ : J M N ≠ 0) :
    (E M N).toAffine.Nonsingular (P2 M N).1 (P2 M N).2 :=
  onCurve_nonsingular (E_discriminant_ne_zero M N hF hH hJ) (P2_onCurve M N)

theorem P3_nonsingular (M N : ℚ)
    (hF : F M N ≠ 0) (hH : H M N ≠ 0) (hJ : J M N ≠ 0) :
    (E M N).toAffine.Nonsingular (P3 M N).1 (P3 M N).2 :=
  onCurve_nonsingular (E_discriminant_ne_zero M N hF hH hJ) (P3_onCurve M N)

theorem P4_nonsingular (M N : ℚ)
    (hF : F M N ≠ 0) (hH : H M N ≠ 0) (hJ : J M N ≠ 0) :
    (E M N).toAffine.Nonsingular (P4 M N).1 (P4 M N).2 :=
  onCurve_nonsingular (E_discriminant_ne_zero M N hF hH hJ) (P4_onCurve M N)

theorem P5_nonsingular (M N : ℚ)
    (hF : F M N ≠ 0) (hH : H M N ≠ 0) (hJ : J M N ≠ 0) :
    (E M N).toAffine.Nonsingular (P5 M N).1 (P5 M N).2 :=
  onCurve_nonsingular (E_discriminant_ne_zero M N hF hH hJ) (P5_onCurve M N)

theorem P'1_nonsingular (M N : ℚ)
    (hF : F M N ≠ 0) (hH : H M N ≠ 0) (hJ : J M N ≠ 0) :
    (E' M N).toAffine.Nonsingular (P'1 M N).1 (P'1 M N).2 :=
  onCurve_nonsingular (E'_discriminant_ne_zero M N hF hH hJ) (P'1_onCurve M N)

theorem P'2_nonsingular (M N : ℚ)
    (hF : F M N ≠ 0) (hH : H M N ≠ 0) (hJ : J M N ≠ 0) :
    (E' M N).toAffine.Nonsingular (P'2 M N).1 (P'2 M N).2 :=
  onCurve_nonsingular (E'_discriminant_ne_zero M N hF hH hJ) (P'2_onCurve M N)

theorem P'3_nonsingular (M N : ℚ)
    (hF : F M N ≠ 0) (hH : H M N ≠ 0) (hJ : J M N ≠ 0) :
    (E' M N).toAffine.Nonsingular (P'3 M N).1 (P'3 M N).2 :=
  onCurve_nonsingular (E'_discriminant_ne_zero M N hF hH hJ) (P'3_onCurve M N)

theorem j_formula (M N : ℚ) [(E M N).IsElliptic]
    (hF : F M N ≠ 0) (hH : H M N ≠ 0) (hJ : J M N ≠ 0) :
    (E M N).j = (4 / 9 : ℚ) * (2500 * F M N + 9 * H M N) ^ 3 /
      ((H M N) ^ 2 * J M N) := by
  rw [WeierstrassCurve.j_eq, E_c4, E_discriminant, c4_formula]
  dsimp [discriminant, b, c]
  field_simp [hF, hH, hJ]
  ring

theorem positive_forms (M N : ℚ) (hM : 0 < M)
    (hlo : (19 / 20 : ℚ) * M < N) (hhi : N < (11 / 10 : ℚ) * M) :
    0 < L0 M N ∧ 0 < L1 M N ∧ 0 < L2 M N ∧ 0 < L3 M N ∧
    0 < L4 M N ∧ 0 < L5 M N ∧ 0 < L6 M N ∧ 0 < L7 M N ∧
    0 < L8 M N ∧ 0 < L9 M N ∧ 0 < L10 M N ∧ 0 < L11 M N := by
  dsimp [L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L11]
  repeat' apply And.intro
  all_goals linarith

theorem positive_products (M N : ℚ) (hM : 0 < M)
    (hlo : (19 / 20 : ℚ) * M < N) (hhi : N < (11 / 10 : ℚ) * M) :
    0 < F M N ∧ 0 < H M N ∧ 0 < J M N := by
  rcases positive_forms M N hM hlo hhi with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  dsimp [F, H, J]
  repeat' apply And.intro
  all_goals positivity

theorem E_isElliptic_in_cone (M N : ℚ) (hM : 0 < M)
    (hlo : (19 / 20 : ℚ) * M < N) (hhi : N < (11 / 10 : ℚ) * M) : (E M N).IsElliptic := by
  rcases positive_products M N hM hlo hhi with ⟨hF, hH, hJ⟩
  exact E_isElliptic M N (ne_of_gt hF) (ne_of_gt hH) (ne_of_gt hJ)

/-- The explicit rational expression for `j` on the affine parameter chart. -/
def jMap (u : ℚ) : ℚ :=
  (4 / 9 : ℚ) * (2500 * F u 1 + 9 * H u 1) ^ 3 / ((H u 1) ^ 2 * J u 1)

theorem jMap_distinct : jMap 1 ≠ jMap 2 := by
  norm_num [jMap, F, H, J, L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L11]

theorem jMap_not_constant : ¬ ∃ j₀ : ℚ, ∀ u : ℚ, jMap u = j₀ := by
  rintro ⟨j₀, h⟩
  exact jMap_distinct ((h 1).trans (h 2).symm)

end RankCertificates.Rank5
