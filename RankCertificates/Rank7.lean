module

public import RankCertificates.Common

/-!
# Exact algebraic certificates for the rank-seven family

The coefficients and sections below are those of the supplied rank-seven
manuscript. All identities are over `ℚ` and are checked by Lean's kernel.
This file proves curve equations and nonsingularity, not Mordell–Weil rank
or infinitude of simultaneous prime values.
-/

@[expose] public section

namespace RankCertificates.Rank7

set_option maxHeartbeats 2000000

def L0 (M _N : ℚ) : ℚ := M
def L1 (_M N : ℚ) : ℚ := N
def L2 (M N : ℚ) : ℚ := M - 182 * N
def L3 (M N : ℚ) : ℚ := 182 * M + 10557 * N
def L4 (M N : ℚ) : ℚ := 9 * M + 34 * N
def L5 (M N : ℚ) : ℚ := 25 * M - 4968 * N
def L6 (M N : ℚ) : ℚ := 2 * M - 5589 * N
def L7 (M N : ℚ) : ℚ := 8 * M + 425 * N
def L8 (M N : ℚ) : ℚ := 13 * M + 2688 * N
def L9 (M N : ℚ) : ℚ := 325 * M + 49266 * N
def L10 (M N : ℚ) : ℚ := 14 * M - 975 * N
def L11 (M N : ℚ) : ℚ := 896 * M - 45747 * N

def F (M N : ℚ) : ℚ := L0 M N * L1 M N * L2 M N * L3 M N
def H (M N : ℚ) : ℚ := L4 M N * L5 M N * L6 M N * L7 M N
def J (M N : ℚ) : ℚ := L8 M N * L9 M N * L10 M N * L11 M N

def a (M N : ℚ) : ℚ := 91205 * F M N
def b (M N : ℚ) : ℚ := -33124 * F M N * H M N
def c (M N : ℚ) : ℚ := 9 * F M N * J M N
def E (M N : ℚ) : WeierstrassCurve ℚ := model (a M N) (b M N)
def E' (M N : ℚ) : WeierstrassCurve ℚ := model (-2 * a M N) (c M N)

def d (M N : ℚ) : ℚ := M ^ 2 + 10557 * N ^ 2
def T (M N : ℚ) : ℚ := M ^ 2 - 364 * M * N - 10557 * N ^ 2
def Z (M N : ℚ) : ℚ := -182 * M ^ 2 - 21114 * M * N + 1921374 * N ^ 2
def A1 (M N : ℚ) : ℚ := 175 * M ^ 2 + 10738 * M * N + 2470338 * N ^ 2
def A2 (M N : ℚ) : ℚ := 364 * M ^ 2 + 36639 * M * N - 2825550 * N ^ 2
def A3 (M N : ℚ) : ℚ := 728 * M ^ 2 - 592647 * M * N + 28820610 * N ^ 2
def B1 (M N : ℚ) : ℚ := 49 * M ^ 2 - 43862 * M * N - 2026944 * N ^ 2
def B2 (M N : ℚ) : ℚ := 2912 * M ^ 2 + 2544237 * M * N - 432309150 * N ^ 2

theorem quartic_relation (M N : ℚ) :
    91205 ^ 2 * F M N + 4 * 33124 * H M N = 9 * J M N := by
  unfold F H J L0 L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11
  ring

theorem discriminant_coefficient (M N : ℚ) : a M N ^ 2 - 4 * b M N = c M N := by
  unfold a b c
  have h := quartic_relation M N
  linear_combination F M N * h

theorem conic_identity (M N : ℚ) :
    Z M N ^ 2 + 10557 * T M N ^ 2 = 43681 * d M N ^ 2 := by
  unfold Z T d
  ring

theorem pullback_U (M N : ℚ) : T M N ^ 2 - d M N ^ 2 = -4 * F M N := by
  unfold T d F L0 L1 L2 L3
  ring

theorem pullback_V (M N : ℚ) :
    241 ^ 2 * T M N ^ 2 - 209 ^ 2 * d M N ^ 2 = 4 * H M N := by
  unfold T d H L4 L5 L6 L7
  ring

theorem pullback_W (M N : ℚ) :
    8319 ^ 2 * T M N ^ 2 - 16769 ^ 2 * d M N ^ 2 = -4 * J M N := by
  unfold T d J L8 L9 L10 L11
  ring

def p1x (M N : ℚ) : ℚ := -58081 * F M N
def p1r (M N : ℚ) : ℚ := 10920 * d M N / 241
def p2x (M N : ℚ) : ℚ := (1225 / 9) * L0 M N * L2 M N * L6 M N * L7 M N
def p2r (M N : ℚ) : ℚ := (4 / 15) * A1 M N
def p3x (M N : ℚ) : ℚ := -2275 * L1 M N * L2 M N * L5 M N * L6 M N
def p3r (M N : ℚ) : ℚ := -(6 / 5) * A2 M N
def p4x (M N : ℚ) : ℚ := (182 / 361) * L2 M N * L3 M N * L6 M N * L7 M N
def p4r (M N : ℚ) : ℚ := A3 M N / 19
def q1x (M N : ℚ) : ℚ := 3481 * F M N
def q1r (M N : ℚ) : ℚ := 21840 * d M N / 59
def q2x (M N : ℚ) : ℚ := (49 / 64) * L0 M N * L2 M N * L8 M N * L9 M N
def q2r (M N : ℚ) : ℚ := (65 / 56) * B1 M N
def q3x (M N : ℚ) : ℚ := (16 / 225) * L0 M N * L3 M N * L8 M N * L10 M N
def q3r (M N : ℚ) : ℚ := B2 M N / 60

theorem p1_onCurve (M N : ℚ) :
    OnCurve (a M N) (b M N) (p1x M N) (p1x M N * p1r M N) := by
  unfold OnCurve a b p1x p1r d F H L0 L1 L2 L3 L4 L5 L6 L7
  ring

theorem p2_onCurve (M N : ℚ) :
    OnCurve (a M N) (b M N) (p2x M N) (p2x M N * p2r M N) := by
  unfold OnCurve a b p2x p2r A1 F H L0 L1 L2 L3 L4 L5 L6 L7
  ring

theorem p3_onCurve (M N : ℚ) :
    OnCurve (a M N) (b M N) (p3x M N) (p3x M N * p3r M N) := by
  unfold OnCurve a b p3x p3r A2 F H L0 L1 L2 L3 L4 L5 L6 L7
  ring

theorem p4_onCurve (M N : ℚ) :
    OnCurve (a M N) (b M N) (p4x M N) (p4x M N * p4r M N) := by
  unfold OnCurve a b p4x p4r A3 F H L0 L1 L2 L3 L4 L5 L6 L7
  ring

theorem q1_onCurve (M N : ℚ) :
    OnCurve (-2 * a M N) (c M N) (q1x M N) (q1x M N * q1r M N) := by
  unfold OnCurve a c q1x q1r d F J L0 L1 L2 L3 L8 L9 L10 L11
  ring

theorem q2_onCurve (M N : ℚ) :
    OnCurve (-2 * a M N) (c M N) (q2x M N) (q2x M N * q2r M N) := by
  unfold OnCurve a c q2x q2r B1 F J L0 L1 L2 L3 L8 L9 L10 L11
  ring

theorem q3_onCurve (M N : ℚ) :
    OnCurve (-2 * a M N) (c M N) (q3x M N) (q3x M N * q3r M N) := by
  unfold OnCurve a c q3x q3r B2 F J L0 L1 L2 L3 L8 L9 L10 L11
  ring

/-! The appendix's three points on `E`, written with only constant denominators. -/

def r1x (M N : ℚ) : ℚ := (10920 * d M N / 59) ^ 2
def r1y (M N : ℚ) : ℚ := (21840 * d M N / (8 * 59)) *
  (3481 * F M N - 9 * J M N / 3481)
def r2x (M N : ℚ) : ℚ := (65 * B1 M N / 112) ^ 2
def r2y (M N : ℚ) : ℚ := (65 * B1 M N / 448) *
  ((49 / 64) * L0 M N * L2 M N * L8 M N * L9 M N -
    (576 / 49) * L1 M N * L3 M N * L10 M N * L11 M N)
def r3x (M N : ℚ) : ℚ := (B2 M N / 120) ^ 2
def r3y (M N : ℚ) : ℚ := (B2 M N / 480) *
  ((16 / 225) * L0 M N * L3 M N * L8 M N * L10 M N -
    (2025 / 16) * L1 M N * L2 M N * L9 M N * L11 M N)

theorem r1_onCurve (M N : ℚ) : OnCurve (a M N) (b M N) (r1x M N) (r1y M N) := by
  unfold OnCurve a b r1x r1y d F H J L0 L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11
  ring

theorem r2_onCurve (M N : ℚ) : OnCurve (a M N) (b M N) (r2x M N) (r2y M N) := by
  unfold OnCurve a b r2x r2y B1 F H L0 L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11
  ring

theorem r3_onCurve (M N : ℚ) : OnCurve (a M N) (b M N) (r3x M N) (r3y M N) := by
  unfold OnCurve a b r3x r3y B2 F H L0 L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11
  ring

theorem raw_section_onCurve (M N : ℚ) :
    OnCurve (a M N) (b M N) (8281 * T M N ^ 2)
      ((8281 / 2) * d M N * T M N * Z M N) := by
  unfold OnCurve a b T d Z F H L0 L1 L2 L3 L4 L5 L6 L7
  ring

/-! Literal square factors relating the coordinates to the paper's representatives. -/

theorem b_square_factor (M N : ℚ) :
    b M N = (-F M N * H M N) * (182 : ℚ) ^ 2 := by unfold b; ring

theorem c_square_factor (M N : ℚ) :
    c M N = (F M N * J M N) * (3 : ℚ) ^ 2 := by unfold c; ring

theorem p1_square_factor (M N : ℚ) :
    p1x M N = (-F M N) * (241 : ℚ) ^ 2 := by unfold p1x; ring

theorem p2_square_factor (M N : ℚ) :
    p2x M N = (L0 M N * L2 M N * L6 M N * L7 M N) * (35 / 3 : ℚ) ^ 2 := by
  unfold p2x; ring

theorem p3_square_factor (M N : ℚ) :
    p3x M N = (-91 * L1 M N * L2 M N * L5 M N * L6 M N) * (5 : ℚ) ^ 2 := by
  unfold p3x; ring

theorem p4_square_factor (M N : ℚ) :
    p4x M N = (182 * L2 M N * L3 M N * L6 M N * L7 M N) * (1 / 19 : ℚ) ^ 2 := by
  unfold p4x; ring

theorem q1_square_factor (M N : ℚ) :
    q1x M N = F M N * (59 : ℚ) ^ 2 := by unfold q1x; ring

theorem q2_square_factor (M N : ℚ) :
    q2x M N = (L0 M N * L2 M N * L8 M N * L9 M N) * (7 / 8 : ℚ) ^ 2 := by
  unfold q2x; ring

theorem q3_square_factor (M N : ℚ) :
    q3x M N = (L0 M N * L3 M N * L8 M N * L10 M N) * (4 / 15 : ℚ) ^ 2 := by
  unfold q3x; ring

theorem E_discriminant (M N : ℚ) :
    (E M N).Δ = 16 * b M N ^ 2 * c M N := by
  unfold E model WeierstrassCurve.Δ WeierstrassCurve.b₂
    WeierstrassCurve.b₄ WeierstrassCurve.b₆ WeierstrassCurve.b₈
  dsimp
  rw [← discriminant_coefficient M N]
  ring

theorem E'_discriminant (M N : ℚ) :
    (E' M N).Δ = 256 * b M N * c M N ^ 2 := by
  unfold E' model WeierstrassCurve.Δ WeierstrassCurve.b₂
    WeierstrassCurve.b₄ WeierstrassCurve.b₆ WeierstrassCurve.b₈
  dsimp
  have h := discriminant_coefficient M N
  linear_combination 64 * c M N ^ 2 * h

theorem E_c4 (M N : ℚ) :
    (E M N).c₄ = 16 * F M N * (91205 ^ 2 * F M N + 3 * 182 ^ 2 * H M N) := by
  unfold E model WeierstrassCurve.c₄ WeierstrassCurve.b₂
    WeierstrassCurve.b₄ a b
  dsimp
  ring

theorem E'_c4 (M N : ℚ) :
    (E' M N).c₄ = 64 * a M N ^ 2 - 48 * c M N := by
  unfold E' model WeierstrassCurve.c₄ WeierstrassCurve.b₂ WeierstrassCurve.b₄
  dsimp
  ring

theorem b_ne_zero {M N : ℚ} (hF : F M N ≠ 0) (hH : H M N ≠ 0) : b M N ≠ 0 := by
  unfold b
  exact mul_ne_zero (mul_ne_zero (by norm_num) hF) hH

theorem c_ne_zero {M N : ℚ} (hF : F M N ≠ 0) (hJ : J M N ≠ 0) : c M N ≠ 0 := by
  unfold c
  exact mul_ne_zero (mul_ne_zero (by norm_num) hF) hJ

theorem E_discriminant_ne_zero {M N : ℚ}
    (hF : F M N ≠ 0) (hH : H M N ≠ 0) (hJ : J M N ≠ 0) : (E M N).Δ ≠ 0 := by
  rw [E_discriminant]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ (b_ne_zero hF hH)))
    (c_ne_zero hF hJ)

theorem E'_discriminant_ne_zero {M N : ℚ}
    (hF : F M N ≠ 0) (hH : H M N ≠ 0) (hJ : J M N ≠ 0) : (E' M N).Δ ≠ 0 := by
  rw [E'_discriminant]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (b_ne_zero hF hH))
    (pow_ne_zero _ (c_ne_zero hF hJ))

theorem E_isElliptic {M N : ℚ}
    (hF : F M N ≠ 0) (hH : H M N ≠ 0) (hJ : J M N ≠ 0) : (E M N).IsElliptic := by
  exact ⟨isUnit_iff_ne_zero.mpr (E_discriminant_ne_zero hF hH hJ)⟩

theorem E'_isElliptic {M N : ℚ}
    (hF : F M N ≠ 0) (hH : H M N ≠ 0) (hJ : J M N ≠ 0) : (E' M N).IsElliptic := by
  exact ⟨isUnit_iff_ne_zero.mpr (E'_discriminant_ne_zero hF hH hJ)⟩

theorem p1_equation (M N : ℚ) :
    (E M N).toAffine.Equation (p1x M N) (p1x M N * p1r M N) :=
  (onCurve_iff_equation _ _ _ _).mp (p1_onCurve M N)

theorem p2_equation (M N : ℚ) :
    (E M N).toAffine.Equation (p2x M N) (p2x M N * p2r M N) :=
  (onCurve_iff_equation _ _ _ _).mp (p2_onCurve M N)

theorem p3_equation (M N : ℚ) :
    (E M N).toAffine.Equation (p3x M N) (p3x M N * p3r M N) :=
  (onCurve_iff_equation _ _ _ _).mp (p3_onCurve M N)

theorem p4_equation (M N : ℚ) :
    (E M N).toAffine.Equation (p4x M N) (p4x M N * p4r M N) :=
  (onCurve_iff_equation _ _ _ _).mp (p4_onCurve M N)

theorem q1_equation (M N : ℚ) :
    (E' M N).toAffine.Equation (q1x M N) (q1x M N * q1r M N) :=
  (onCurve_iff_equation _ _ _ _).mp (q1_onCurve M N)

theorem q2_equation (M N : ℚ) :
    (E' M N).toAffine.Equation (q2x M N) (q2x M N * q2r M N) :=
  (onCurve_iff_equation _ _ _ _).mp (q2_onCurve M N)

theorem q3_equation (M N : ℚ) :
    (E' M N).toAffine.Equation (q3x M N) (q3x M N * q3r M N) :=
  (onCurve_iff_equation _ _ _ _).mp (q3_onCurve M N)

theorem p1_nonsingular {M N : ℚ}
    (hF : F M N ≠ 0) (hH : H M N ≠ 0) (hJ : J M N ≠ 0) :
    (E M N).toAffine.Nonsingular (p1x M N) (p1x M N * p1r M N) :=
  onCurve_nonsingular (E_discriminant_ne_zero hF hH hJ) (p1_onCurve M N)

theorem p2_nonsingular {M N : ℚ}
    (hF : F M N ≠ 0) (hH : H M N ≠ 0) (hJ : J M N ≠ 0) :
    (E M N).toAffine.Nonsingular (p2x M N) (p2x M N * p2r M N) :=
  onCurve_nonsingular (E_discriminant_ne_zero hF hH hJ) (p2_onCurve M N)

theorem p3_nonsingular {M N : ℚ}
    (hF : F M N ≠ 0) (hH : H M N ≠ 0) (hJ : J M N ≠ 0) :
    (E M N).toAffine.Nonsingular (p3x M N) (p3x M N * p3r M N) :=
  onCurve_nonsingular (E_discriminant_ne_zero hF hH hJ) (p3_onCurve M N)

theorem p4_nonsingular {M N : ℚ}
    (hF : F M N ≠ 0) (hH : H M N ≠ 0) (hJ : J M N ≠ 0) :
    (E M N).toAffine.Nonsingular (p4x M N) (p4x M N * p4r M N) :=
  onCurve_nonsingular (E_discriminant_ne_zero hF hH hJ) (p4_onCurve M N)

theorem q1_nonsingular {M N : ℚ}
    (hF : F M N ≠ 0) (hH : H M N ≠ 0) (hJ : J M N ≠ 0) :
    (E' M N).toAffine.Nonsingular (q1x M N) (q1x M N * q1r M N) :=
  onCurve_nonsingular (E'_discriminant_ne_zero hF hH hJ) (q1_onCurve M N)

theorem q2_nonsingular {M N : ℚ}
    (hF : F M N ≠ 0) (hH : H M N ≠ 0) (hJ : J M N ≠ 0) :
    (E' M N).toAffine.Nonsingular (q2x M N) (q2x M N * q2r M N) :=
  onCurve_nonsingular (E'_discriminant_ne_zero hF hH hJ) (q2_onCurve M N)

theorem q3_nonsingular {M N : ℚ}
    (hF : F M N ≠ 0) (hH : H M N ≠ 0) (hJ : J M N ≠ 0) :
    (E' M N).toAffine.Nonsingular (q3x M N) (q3x M N * q3r M N) :=
  onCurve_nonsingular (E'_discriminant_ne_zero hF hH hJ) (q3_onCurve M N)

theorem r1_nonsingular {M N : ℚ}
    (hF : F M N ≠ 0) (hH : H M N ≠ 0) (hJ : J M N ≠ 0) :
    (E M N).toAffine.Nonsingular (r1x M N) (r1y M N) :=
  onCurve_nonsingular (E_discriminant_ne_zero hF hH hJ) (r1_onCurve M N)

theorem r2_nonsingular {M N : ℚ}
    (hF : F M N ≠ 0) (hH : H M N ≠ 0) (hJ : J M N ≠ 0) :
    (E M N).toAffine.Nonsingular (r2x M N) (r2y M N) :=
  onCurve_nonsingular (E_discriminant_ne_zero hF hH hJ) (r2_onCurve M N)

theorem r3_nonsingular {M N : ℚ}
    (hF : F M N ≠ 0) (hH : H M N ≠ 0) (hJ : J M N ≠ 0) :
    (E M N).toAffine.Nonsingular (r3x M N) (r3y M N) :=
  onCurve_nonsingular (E_discriminant_ne_zero hF hH hJ) (r3_onCurve M N)

theorem E_j (M N : ℚ) [hE : (E M N).IsElliptic]
    (hF : F M N ≠ 0) (hH : H M N ≠ 0) (hJ : J M N ≠ 0) :
    (E M N).j = (256 / (9 * 182 ^ 4)) *
      (91205 ^ 2 * F M N + 3 * 182 ^ 2 * H M N) ^ 3 / (H M N ^ 2 * J M N) := by
  let : (model (a M N) (b M N)).IsElliptic := hE
  change (model (a M N) (b M N)).j = _
  rw [model_j, discriminant_coefficient]
  unfold a b c
  field_simp [hF, hH, hJ]
  ring

end RankCertificates.Rank7
