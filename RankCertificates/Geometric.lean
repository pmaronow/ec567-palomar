module

public import RankCertificates.Rank5
public import RankCertificates.Rank6
public import RankCertificates.Rank7
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Set.Finite.Lattice

@[expose] public section

namespace RankCertificates.Geometric

open Polynomial

noncomputable section

/-- Every fiber of a nonconstant rational function, away from poles, is finite. -/
theorem rational_fiber_finite (P Q : ℚ[X])
    (hnonconstant : ∀ c : ℚ, P ≠ C c * Q) (c : ℚ) :
    Set.Finite {t : ℚ | Q.eval t ≠ 0 ∧ P.eval t / Q.eval t = c} := by
  have hpoly : P - C c * Q ≠ 0 := sub_ne_zero.mpr (hnonconstant c)
  apply (Polynomial.finite_setOfPred_isRoot hpoly).subset
  intro t ht
  change (P - C c * Q).eval t = 0
  simp only [eval_sub, eval_mul, eval_C]
  exact sub_eq_zero.mpr ((div_eq_iff ht.1).mp ht.2)

/-- Nonconstant rational functions on an infinite parameter set have infinite image. -/
theorem rational_image_infinite (P Q : ℚ[X]) (s : Set ℚ) (hs : s.Infinite)
    (hregular : ∀ t ∈ s, Q.eval t ≠ 0)
    (hnonconstant : ∀ c : ℚ, P ≠ C c * Q) :
    (Set.image (fun t => P.eval t / Q.eval t) s).Infinite := by
  intro himage
  apply hs
  apply Set.Finite.of_finite_fibers (fun t => P.eval t / Q.eval t) himage
  intro c _
  apply (rational_fiber_finite P Q hnonconstant c).subset
  intro t ht
  exact ⟨hregular t ht.1, ht.2⟩

/-- Two unequal regular values are enough to certify nonconstancy. -/
theorem nonconstant_of_two_values (P Q : ℚ[X]) (u v : ℚ)
    (hu : Q.eval u ≠ 0) (hv : Q.eval v ≠ 0)
    (hne : P.eval u / Q.eval u ≠ P.eval v / Q.eval v) :
    ∀ c : ℚ, P ≠ C c * Q := by
  intro c heq
  apply hne
  have hu' : P.eval u = c * Q.eval u := by rw [heq, eval_mul, eval_C]
  have hv' : P.eval v = c * Q.eval v := by rw [heq, eval_mul, eval_C]
  rw [hu', hv', mul_div_cancel_right₀ _ hu, mul_div_cancel_right₀ _ hv]



def f5 : ℚ[X] := (X) * (22 * X - 1) * (9 * X - 2 * 1) * (143 * X + 155 * 1)

def h5 : ℚ[X] := (-55 * X + 62 * 1) * (3 * X - 1) * (138 * X - 31 * 1) * (55 * X + 64 * 1)

def a5 : ℚ[X] := 1500 * f5
def b5 : ℚ[X] := -2700 * f5 * h5

def numerator5 : ℚ[X] := 256 * (a5 ^ 2 - 3 * b5) ^ 3
def denominator5 : ℚ[X] := b5 ^ 2 * (a5 ^ 2 - 4 * b5)

theorem denominator5_ne_zero : denominator5 ≠ 0 := by
  intro heq
  have h := congrArg (Polynomial.eval (3 : ℚ)) heq
  norm_num [numerator5, denominator5, a5, b5, f5, h5] at h

theorem nonconstant5 : ∀ c : ℚ, numerator5 ≠ C c * denominator5 := by
  apply nonconstant_of_two_values _ _ 3 4
  all_goals norm_num [numerator5, denominator5, a5, b5, f5, h5]

theorem invariant5_eq (t : ℚ) :
    (Rank5.E t 1).Δ⁻¹ * (Rank5.E t 1).c₄ ^ 3 =
      (numerator5.eval t) / (denominator5.eval t) := by
  rw [Rank5.E, model_discriminant, model_c4]
  simp only [div_eq_mul_inv, mul_inv_rev]
  simp [numerator5, denominator5, a5, b5, f5, h5, Rank5.a, Rank5.b, Rank5.F, Rank5.H, Rank5.L0, Rank5.L1, Rank5.L2, Rank5.L3, Rank5.L4, Rank5.L5, Rank5.L6, Rank5.L7, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
  ring

theorem geometric_image5_infinite (s : Set ℚ) (hs : s.Infinite)
    (hregular : ∀ t ∈ s, denominator5.eval t ≠ 0) :
    (Set.image (fun t => (Rank5.E t 1).Δ⁻¹ * (Rank5.E t 1).c₄ ^ 3) s).Infinite := by
  simpa only [invariant5_eq] using
    rational_image_infinite numerator5 denominator5 s hs hregular nonconstant5

theorem full_regular_image5_infinite :
    (Set.image (fun t => (Rank5.E t 1).Δ⁻¹ * (Rank5.E t 1).c₄ ^ 3)
      {t : ℚ | denominator5.eval t ≠ 0}).Infinite := by
  apply geometric_image5_infinite
  · have hz := Polynomial.finite_setOfPred_isRoot denominator5_ne_zero
    simpa only [Polynomial.IsRoot, Set.compl_ofPred] using hz.infinite_compl
  · intro t ht
    exact ht

def f6 : ℚ[X] := (X) * (1) * (169 * X + 750 * 1) * (25 * X - 169 * 1)

def h6 : ℚ[X] := (X - 27 * 1) * (7 * X + 20 * 1) * (2 * X - 21 * 1) * (9 * X + 10 * 1)

def a6 : ℚ[X] := 70 * f6
def b6 : ℚ[X] := -784 * f6 * h6

def numerator6 : ℚ[X] := 256 * (a6 ^ 2 - 3 * b6) ^ 3
def denominator6 : ℚ[X] := b6 ^ 2 * (a6 ^ 2 - 4 * b6)

theorem denominator6_ne_zero : denominator6 ≠ 0 := by
  intro heq
  have h := congrArg (Polynomial.eval (3 : ℚ)) heq
  norm_num [numerator6, denominator6, a6, b6, f6, h6] at h

theorem nonconstant6 : ∀ c : ℚ, numerator6 ≠ C c * denominator6 := by
  apply nonconstant_of_two_values _ _ 3 4
  all_goals norm_num [numerator6, denominator6, a6, b6, f6, h6]

theorem invariant6_eq (t : ℚ) :
    (Rank6.E t 1).Δ⁻¹ * (Rank6.E t 1).c₄ ^ 3 =
      (numerator6.eval t) / (denominator6.eval t) := by
  rw [Rank6.E, model_discriminant, model_c4]
  simp only [div_eq_mul_inv, mul_inv_rev]
  simp [numerator6, denominator6, a6, b6, f6, h6, Rank6.a, Rank6.b, Rank6.F, Rank6.H, Rank6.L0, Rank6.L1, Rank6.L2, Rank6.L3, Rank6.L4, Rank6.L5, Rank6.L6, Rank6.L7, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
  ring

theorem geometric_image6_infinite (s : Set ℚ) (hs : s.Infinite)
    (hregular : ∀ t ∈ s, denominator6.eval t ≠ 0) :
    (Set.image (fun t => (Rank6.E t 1).Δ⁻¹ * (Rank6.E t 1).c₄ ^ 3) s).Infinite := by
  simpa only [invariant6_eq] using
    rational_image_infinite numerator6 denominator6 s hs hregular nonconstant6

theorem full_regular_image6_infinite :
    (Set.image (fun t => (Rank6.E t 1).Δ⁻¹ * (Rank6.E t 1).c₄ ^ 3)
      {t : ℚ | denominator6.eval t ≠ 0}).Infinite := by
  apply geometric_image6_infinite
  · have hz := Polynomial.finite_setOfPred_isRoot denominator6_ne_zero
    simpa only [Polynomial.IsRoot, Set.compl_ofPred] using hz.infinite_compl
  · intro t ht
    exact ht

def f7 : ℚ[X] := (X) * (1) * (X - 182 * 1) * (182 * X + 10557 * 1)

def h7 : ℚ[X] := (9 * X + 34 * 1) * (25 * X - 4968 * 1) * (2 * X - 5589 * 1) * (8 * X + 425 * 1)

def a7 : ℚ[X] := 91205 * f7
def b7 : ℚ[X] := -33124 * f7 * h7

def numerator7 : ℚ[X] := 256 * (a7 ^ 2 - 3 * b7) ^ 3
def denominator7 : ℚ[X] := b7 ^ 2 * (a7 ^ 2 - 4 * b7)

theorem denominator7_ne_zero : denominator7 ≠ 0 := by
  intro heq
  have h := congrArg (Polynomial.eval (3 : ℚ)) heq
  norm_num [numerator7, denominator7, a7, b7, f7, h7] at h

theorem nonconstant7 : ∀ c : ℚ, numerator7 ≠ C c * denominator7 := by
  apply nonconstant_of_two_values _ _ 3 4
  all_goals norm_num [numerator7, denominator7, a7, b7, f7, h7]

theorem invariant7_eq (t : ℚ) :
    (Rank7.E t 1).Δ⁻¹ * (Rank7.E t 1).c₄ ^ 3 =
      (numerator7.eval t) / (denominator7.eval t) := by
  rw [Rank7.E, model_discriminant, model_c4]
  simp only [div_eq_mul_inv, mul_inv_rev]
  simp [numerator7, denominator7, a7, b7, f7, h7, Rank7.a, Rank7.b, Rank7.F, Rank7.H, Rank7.L0, Rank7.L1, Rank7.L2, Rank7.L3, Rank7.L4, Rank7.L5, Rank7.L6, Rank7.L7, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
  ring

theorem geometric_image7_infinite (s : Set ℚ) (hs : s.Infinite)
    (hregular : ∀ t ∈ s, denominator7.eval t ≠ 0) :
    (Set.image (fun t => (Rank7.E t 1).Δ⁻¹ * (Rank7.E t 1).c₄ ^ 3) s).Infinite := by
  simpa only [invariant7_eq] using
    rational_image_infinite numerator7 denominator7 s hs hregular nonconstant7

theorem full_regular_image7_infinite :
    (Set.image (fun t => (Rank7.E t 1).Δ⁻¹ * (Rank7.E t 1).c₄ ^ 3)
      {t : ℚ | denominator7.eval t ≠ 0}).Infinite := by
  apply geometric_image7_infinite
  · have hz := Polynomial.finite_setOfPred_isRoot denominator7_ne_zero
    simpa only [Polynomial.IsRoot, Set.compl_ofPred] using hz.infinite_compl
  · intro t ht
    exact ht

theorem denominator5_eval (t : ℚ) : denominator5.eval t =
    (Rank5.b t 1) ^ 2 * ((Rank5.a t 1) ^ 2 - 4 * Rank5.b t 1) := by
  simp [denominator5, a5, b5, f5, h5, Rank5.a, Rank5.b, Rank5.F, Rank5.H, Rank5.L0, Rank5.L1, Rank5.L2, Rank5.L3, Rank5.L4, Rank5.L5, Rank5.L6, Rank5.L7]

theorem elliptic5_of_regular {t : ℚ} (h : denominator5.eval t ≠ 0) :
    (Rank5.E t 1).IsElliptic := by
  rw [denominator5_eval] at h
  apply model_isElliptic
  · intro hb
    simp [hb] at h
  · exact (mul_ne_zero_iff.mp h).2

theorem denominator6_eval (t : ℚ) : denominator6.eval t =
    (Rank6.b t 1) ^ 2 * ((Rank6.a t 1) ^ 2 - 4 * Rank6.b t 1) := by
  simp [denominator6, a6, b6, f6, h6, Rank6.a, Rank6.b, Rank6.F, Rank6.H, Rank6.L0, Rank6.L1, Rank6.L2, Rank6.L3, Rank6.L4, Rank6.L5, Rank6.L6, Rank6.L7]

theorem elliptic6_of_regular {t : ℚ} (h : denominator6.eval t ≠ 0) :
    (Rank6.E t 1).IsElliptic := by
  rw [denominator6_eval] at h
  apply model_isElliptic
  · intro hb
    simp [hb] at h
  · exact (mul_ne_zero_iff.mp h).2

theorem denominator7_eval (t : ℚ) : denominator7.eval t =
    (Rank7.b t 1) ^ 2 * ((Rank7.a t 1) ^ 2 - 4 * Rank7.b t 1) := by
  simp [denominator7, a7, b7, f7, h7, Rank7.a, Rank7.b, Rank7.F, Rank7.H, Rank7.L0, Rank7.L1, Rank7.L2, Rank7.L3, Rank7.L4, Rank7.L5, Rank7.L6, Rank7.L7]

theorem elliptic7_of_regular {t : ℚ} (h : denominator7.eval t ≠ 0) :
    (Rank7.E t 1).IsElliptic := by
  rw [denominator7_eval] at h
  apply model_isElliptic
  · intro hb
    simp [hb] at h
  · exact (mul_ne_zero_iff.mp h).2

end

end RankCertificates.Geometric
