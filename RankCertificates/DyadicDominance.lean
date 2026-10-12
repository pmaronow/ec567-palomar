module

public import RankCertificates.PrimePowerResidues

@[expose] public section

namespace RankCertificates.DyadicDominance

open LocalValuations PrimePowerResidues

theorem sum_lower_or_zero {p : ℕ} [Fact p.Prime] {k : ℤ} {u v : ℚ}
    (hu : u = 0 ∨ k ≤ padicValRat p u) (hv : v = 0 ∨ k ≤ padicValRat p v) :
    u + v = 0 ∨ k ≤ padicValRat p (u + v) := by
  rcases hu with rfl | hu
  · simpa using hv
  rcases hv with rfl | hv
  · simpa using Or.inr hu
  by_cases hz : u + v = 0
  · exact Or.inl hz
  · exact Or.inr (le_trans (le_min hu hv) (padicValRat.min_le_padicValRat_add hz))

/-- A rational square approximation to three unit bits certifies an odd
square residue modulo 8. -/
theorem unitResiduePow_one_of_precise_square {x r : ℚ}
    (hx : x ≠ 0) (hr : r ≠ 0)
    (hclose : x - r ^ 2 = 0 ∨ 3 + padicValRat 2 x ≤ padicValRat 2 (x - r ^ 2)) :
    unitResiduePow 2 3 x = 1 := by
  have hv : padicValRat 2 x = padicValRat 2 (r ^ 2) := by
    have hh : -(x - r ^ 2) = 0 ∨ padicValRat 2 x < padicValRat 2 (-(x - r ^ 2)) := by
      rcases hclose with hz | hv
      · exact Or.inl (by rw [hz, neg_zero])
      · exact Or.inr (by rw [padicValRat.neg]; omega)
    have hs := (LocalDescent.add_dominant (p := 2) hx hh).2
    rw [show x + -(x - r ^ 2) = r ^ 2 by ring] at hs
    exact hs.symm
  rw [unitResiduePow_eq_of_close 2 3 hx (pow_ne_zero 2 hr) hv hclose]
  exact unitResiduePow_two_square hr

/-- Cubic dominance at three unit bits gives the exact normalized dyadic
square unit for a genuine rational point. -/
theorem cubic_unitResiduePow_one {a b x y : ℚ} (hx : x ≠ 0)
    (ha : a = 0 ∨ 3 + padicValRat 2 x ≤ padicValRat 2 a)
    (hb : b = 0 ∨ 3 + 2 * padicValRat 2 x ≤ padicValRat 2 b)
    (h : OnCurve a b x y) : unitResiduePow 2 3 x = 1 := by
  have hax : a * x ^ 2 = 0 ∨ padicValRat 2 (x ^ 3) < padicValRat 2 (a * x ^ 2) := by
    rcases ha with rfl | ha
    · left; simp
    · by_cases ha0 : a = 0
      · left; simp [ha0]
      · right
        rw [padicValRat.pow, padicValRat.mul ha0 (pow_ne_zero 2 hx), padicValRat.pow]
        omega
  have hbx : b * x = 0 ∨ padicValRat 2 (x ^ 3) < padicValRat 2 (b * x) := by
    rcases hb with rfl | hb
    · left; simp
    · by_cases hb0 : b = 0
      · left; simp [hb0]
      · right
        rw [padicValRat.pow, padicValRat.mul hb0 hx]
        omega
  have hy : y ≠ 0 := by
    have hs := (LocalDescent.sum_dominant (p := 2) (pow_ne_zero 3 hx) hax hbx).1
    rw [← h] at hs
    exact fun hz => hs (by simp [hz])
  have hdiff : x - (y / x) ^ 2 = -a + -b / x := by
    dsimp [OnCurve] at h
    field_simp [hx]
    nlinarith [h]
  have ha' : -a = 0 ∨ 3 + padicValRat 2 x ≤ padicValRat 2 (-a) := by
    simpa only [neg_eq_zero, padicValRat.neg] using ha
  have hb' : -b / x = 0 ∨ 3 + padicValRat 2 x ≤ padicValRat 2 (-b / x) := by
    rcases hb with rfl | hb
    · left; simp
    · by_cases hb0 : b = 0
      · left; simp [hb0]
      · right
        rw [padicValRat.div (neg_ne_zero.mpr hb0) hx, padicValRat.neg]
        omega
  apply unitResiduePow_one_of_precise_square hx (div_ne_zero hy hx)
  rw [hdiff]
  exact sum_lower_or_zero ha' hb'

/-- Linear dominance at three unit bits gives the normalized square unit
of b*x for a genuine rational point. -/
theorem linear_unitResiduePow_one {a b x y : ℚ} (hb0 : b ≠ 0) (hx : x ≠ 0)
    (hb : 3 + padicValRat 2 b ≤ 2 * padicValRat 2 x)
    (ha : a = 0 ∨ 3 + padicValRat 2 b ≤ padicValRat 2 a + padicValRat 2 x)
    (h : OnCurve a b x y) : unitResiduePow 2 3 (b * x) = 1 := by
  have hc : x ^ 3 = 0 ∨ padicValRat 2 (b * x) < padicValRat 2 (x ^ 3) := by
    right
    rw [padicValRat.mul hb0 hx, padicValRat.pow]
    omega
  have ha' : a * x ^ 2 = 0 ∨ padicValRat 2 (b * x) < padicValRat 2 (a * x ^ 2) := by
    rcases ha with rfl | ha
    · left; simp
    · by_cases ha0 : a = 0
      · left; simp [ha0]
      · right
        rw [padicValRat.mul hb0 hx, padicValRat.mul ha0 (pow_ne_zero 2 hx), padicValRat.pow]
        omega
  have hy : y ≠ 0 := by
    have hs := (LocalDescent.sum_dominant (p := 2) (mul_ne_zero hb0 hx) hc ha').1
    have heq : b * x + x ^ 3 + a * x ^ 2 = y ^ 2 := by dsimp [OnCurve] at h; linear_combination -h
    rw [heq] at hs
    exact fun hz => hs (by simp [hz])
  have hdiff : b * x - y ^ 2 = -(x ^ 3) + -(a * x ^ 2) := by
    dsimp [OnCurve] at h
    linear_combination -h
  have hc' : -(x ^ 3) = 0 ∨ 3 + padicValRat 2 (b * x) ≤ padicValRat 2 (-(x ^ 3)) := by
    right
    rw [padicValRat.neg, padicValRat.pow, padicValRat.mul hb0 hx]
    omega
  have ha'' : -(a * x ^ 2) = 0 ∨
      3 + padicValRat 2 (b * x) ≤ padicValRat 2 (-(a * x ^ 2)) := by
    rcases ha with rfl | ha
    · left; simp
    · by_cases ha0 : a = 0
      · left; simp [ha0]
      · right
        rw [padicValRat.neg, padicValRat.mul ha0 (pow_ne_zero 2 hx), padicValRat.pow,
          padicValRat.mul hb0 hx]
        omega
  apply unitResiduePow_one_of_precise_square (mul_ne_zero hb0 hx) hy
  rw [hdiff]
  exact sum_lower_or_zero hc' ha''

end RankCertificates.DyadicDominance
