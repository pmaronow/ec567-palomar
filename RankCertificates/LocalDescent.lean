module

public import RankCertificates.Common
public import RankCertificates.Kummer
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

@[expose] public section

/-!
# Genuine valuation restrictions on two-isogeny point images

The statements here follow from the actual rational curve equation.  They
are not assumptions connecting a supplied matrix with a descent image.
For integral coefficients, every prime outside the support of `b` has even
valuation in every representative of every actual image squareclass.
-/

namespace RankCertificates.LocalDescent

variable {p : ℕ} [Fact p.Prime]

/-- A strictly smaller nonzero summand controls both nonvanishing and valuation. -/
theorem add_dominant {u v : ℚ} (hu : u ≠ 0)
    (hv : v = 0 ∨ padicValRat p u < padicValRat p v) :
    u + v ≠ 0 ∧ padicValRat p (u + v) = padicValRat p u := by
  rcases hv with rfl | hv
  · simpa using hu
  · by_cases hv0 : v = 0
    · subst v
      simpa using hu
    have huv : u + v ≠ 0 := by
      intro hzero
      have heq : v = -u := by linarith
      rw [heq, padicValRat.neg] at hv
      exact (lt_irrefl _ hv)
    exact ⟨huv, padicValRat.add_eq_of_lt huv hu hv0 hv⟩

/-- A unique smallest summand in a three-term sum controls its valuation. -/
theorem sum_dominant {u v w : ℚ} (hu : u ≠ 0)
    (hv : v = 0 ∨ padicValRat p u < padicValRat p v)
    (hw : w = 0 ∨ padicValRat p u < padicValRat p w) :
    u + v + w ≠ 0 ∧ padicValRat p (u + v + w) = padicValRat p u := by
  obtain ⟨huv, hval⟩ := add_dominant hu hv
  have hw' : w = 0 ∨ padicValRat p (u + v) < padicValRat p w := by
    rw [hval]
    exact hw
  obtain ⟨hs, hsval⟩ := add_dominant huv hw'
  exact ⟨hs, hsval.trans hval⟩

/-- A sum of two terms of higher valuation remains of higher valuation,
unless it vanishes.  The separate zero branch avoids the totalized
valuation's convention at zero. -/
theorem sum_higher_or_zero {k : ℤ} {u v : ℚ}
    (hu : u = 0 ∨ k < padicValRat p u) (hv : v = 0 ∨ k < padicValRat p v) :
    u + v = 0 ∨ k < padicValRat p (u + v) := by
  rcases hu with rfl | hu
  · simpa using hv
  rcases hv with rfl | hv
  · simpa using Or.inr hu
  by_cases hzero : u + v = 0
  · exact Or.inl hzero
  · exact Or.inr (lt_of_lt_of_le (lt_min hu hv) (padicValRat.min_le_padicValRat_add hzero))

/-- A rational square agrees with x to precision strictly beyond its
valuation.  At odd primes this directly certifies the square character
of the normalized unit, without choosing a residue-field implementation. -/
def SquareApproximation (p : ℕ) (x : ℚ) : Prop :=
  ∃ r : ℚ, r ≠ 0 ∧ (x - r ^ 2 = 0 ∨ padicValRat p x < padicValRat p (x - r ^ 2))

/-- A square approximation forces the valuation parity of a square. -/
theorem square_approximation_even_valuation {x : ℚ} (hx : x ≠ 0)
    (h : SquareApproximation p x) : Even (padicValRat p x) := by
  obtain ⟨r, _, hc⟩ := h
  have hn : -(x - r ^ 2) = 0 ∨ padicValRat p x < padicValRat p (-(x - r ^ 2)) := by
    simpa only [neg_eq_zero, padicValRat.neg] using hc
  have hv := (add_dominant hx hn).2
  rw [show x + -(x - r ^ 2) = r ^ 2 by ring, padicValRat.pow] at hv
  exact ⟨padicValRat p r, by omega⟩

/-- Cubic dominance supplies the explicit square approximation `(y/x)^2`. -/
theorem cubic_term_square_approximation {a b x y : ℚ} (hx : x ≠ 0)
    (ha : a = 0 ∨ padicValRat p x < padicValRat p a)
    (hb : b = 0 ∨ 2 * padicValRat p x < padicValRat p b)
    (h : OnCurve a b x y) : SquareApproximation p x := by
  have hax : a * x ^ 2 = 0 ∨ padicValRat p (x ^ 3) < padicValRat p (a * x ^ 2) := by
    rcases ha with rfl | ha
    · left; simp
    · by_cases ha0 : a = 0
      · left; simp [ha0]
      · right
        rw [padicValRat.pow, padicValRat.mul ha0 (pow_ne_zero 2 hx), padicValRat.pow]
        omega
  have hbx : b * x = 0 ∨ padicValRat p (x ^ 3) < padicValRat p (b * x) := by
    rcases hb with rfl | hb
    · left; simp
    · by_cases hb0 : b = 0
      · left; simp [hb0]
      · right; rw [padicValRat.pow, padicValRat.mul hb0 hx]; omega
  have hy : y ≠ 0 := by
    have hc := (sum_dominant (pow_ne_zero 3 hx) hax hbx).1
    rw [← h] at hc
    exact fun hz => hc (by simp [hz])
  have hdiff : x - (y / x) ^ 2 = -a + -b / x := by
    unfold OnCurve at h
    field_simp [hx]
    nlinarith [h]
  have han : -a = 0 ∨ padicValRat p x < padicValRat p (-a) := by
    simpa only [neg_eq_zero, padicValRat.neg] using ha
  have hbn : -b / x = 0 ∨ padicValRat p x < padicValRat p (-b / x) := by
    rcases hb with rfl | hb
    · left; simp
    · by_cases hb0 : b = 0
      · left; simp [hb0]
      · right; rw [padicValRat.div (neg_ne_zero.mpr hb0) hx, padicValRat.neg]; omega
  refine ⟨y / x, div_ne_zero hy hx, ?_⟩
  rw [hdiff]
  exact sum_higher_or_zero han hbn

/-- Linear dominance supplies the explicit approximation y² to the
product b*x, hence the corresponding normalized-unit character. -/
theorem linear_term_square_approximation {a b x y : ℚ} (hb0 : b ≠ 0) (hx : x ≠ 0)
    (hdegree : padicValRat p b < 2 * padicValRat p x)
    (hquadratic : a = 0 ∨ padicValRat p b < padicValRat p a + padicValRat p x)
    (h : OnCurve a b x y) : SquareApproximation p (b * x) := by
  have hcube : x ^ 3 = 0 ∨ padicValRat p (b * x) < padicValRat p (x ^ 3) := by
    right; rw [padicValRat.mul hb0 hx, padicValRat.pow]; omega
  have hquad : a * x ^ 2 = 0 ∨ padicValRat p (b * x) < padicValRat p (a * x ^ 2) := by
    rcases hquadratic with rfl | hquadratic
    · left; simp
    · by_cases ha0 : a = 0
      · left; simp [ha0]
      · right
        rw [padicValRat.mul hb0 hx, padicValRat.mul ha0 (pow_ne_zero 2 hx), padicValRat.pow]
        omega
  have heq : b * x + x ^ 3 + a * x ^ 2 = y ^ 2 := by
    unfold OnCurve at h
    linarith
  have hy : y ≠ 0 := by
    have hc := (sum_dominant (mul_ne_zero hb0 hx) hcube hquad).1
    rw [heq] at hc
    exact fun hz => hc (by simp [hz])
  have hnCube : -(x ^ 3) = 0 ∨ padicValRat p (b * x) < padicValRat p (-(x ^ 3)) := by
    simpa only [neg_eq_zero, padicValRat.neg] using hcube
  have hnQuad : -(a * x ^ 2) = 0 ∨ padicValRat p (b * x) < padicValRat p (-(a * x ^ 2)) := by
    simpa only [neg_eq_zero, padicValRat.neg] using hquad
  refine ⟨y, hy, ?_⟩
  rw [show b * x - y ^ 2 = -(x ^ 3) + -(a * x ^ 2) by linarith [heq]]
  exact sum_higher_or_zero hnCube hnQuad

/-- If the other factor in a square product agrees with a unit square,
the first factor has the explicit approximation `(y/k)^2`. -/
theorem square_approximation_of_near_square_factor {x y q k : ℚ}
    (hx : x ≠ 0) (hk : k ≠ 0) (hkv : padicValRat p k = 0)
    (hclose : q - k ^ 2 = 0 ∨ 0 < padicValRat p (q - k ^ 2))
    (h : y ^ 2 = x * q) : SquareApproximation p x := by
  have hq0 : q ≠ 0 := by
    have hc : q - k ^ 2 = 0 ∨ padicValRat p (k ^ 2) < padicValRat p (q - k ^ 2) := by
      simpa only [padicValRat.pow, hkv, mul_zero] using hclose
    have hh := (add_dominant (p := p) (pow_ne_zero 2 hk) hc).1
    simpa using hh
  have hy : y ≠ 0 := by
    have hh : y ^ 2 ≠ 0 := h ▸ mul_ne_zero hx hq0
    exact fun hz => hh (by simp [hz])
  have hdiff : x - (y / k) ^ 2 = -x * (q - k ^ 2) / k ^ 2 := by
    field_simp [hk]
    nlinarith [h]
  refine ⟨y / k, div_ne_zero hy hk, ?_⟩
  rw [hdiff]
  rcases hclose with hz | hv
  · left; rw [hz]; simp
  · right
    have hc0 : q - k ^ 2 ≠ 0 := by
      intro hz; rw [hz] at hv; simp at hv
    rw [padicValRat.div (mul_ne_zero (neg_ne_zero.mpr hx) hc0) (pow_ne_zero 2 hk),
      padicValRat.mul (neg_ne_zero.mpr hx) hc0, padicValRat.neg,
      padicValRat.pow, hkv]
    omega

/-- Negative x-valuations are even whenever both coefficients are p-integral. -/
theorem x_valuation_even_of_negative {a b x y : ℚ}
    (ha : 0 ≤ padicValRat p a) (hb : 0 ≤ padicValRat p b)
    (hx : x ≠ 0) (hr : padicValRat p x < 0) (h : OnCurve a b x y) :
    Even (padicValRat p x) := by
  have huv : a * x ^ 2 = 0 ∨ padicValRat p (x ^ 3) < padicValRat p (a * x ^ 2) := by
    by_cases ha0 : a = 0
    · left; simp [ha0]
    · right
      rw [padicValRat.pow, padicValRat.mul ha0 (pow_ne_zero 2 hx), padicValRat.pow]
      omega
  have huw : b * x = 0 ∨ padicValRat p (x ^ 3) < padicValRat p (b * x) := by
    by_cases hb0 : b = 0
    · left; simp [hb0]
    · right
      rw [padicValRat.pow, padicValRat.mul hb0 hx]
      omega
  have hv := (sum_dominant (pow_ne_zero 3 hx) huv huw).2
  rw [← h, padicValRat.pow, padicValRat.pow] at hv
  refine ⟨padicValRat p y - padicValRat p x, ?_⟩
  omega

/-- Positive x-valuations are even when the linear coefficient is a p-unit. -/
theorem x_valuation_even_of_positive {a b x y : ℚ}
    (ha : 0 ≤ padicValRat p a) (hb : padicValRat p b = 0) (hb0 : b ≠ 0)
    (hx : x ≠ 0) (hr : 0 < padicValRat p x) (h : OnCurve a b x y) :
    Even (padicValRat p x) := by
  have huv : x ^ 3 = 0 ∨ padicValRat p (b * x) < padicValRat p (x ^ 3) := by
    right
    rw [padicValRat.mul hb0 hx, hb, padicValRat.pow]
    omega
  have huw : a * x ^ 2 = 0 ∨ padicValRat p (b * x) < padicValRat p (a * x ^ 2) := by
    by_cases ha0 : a = 0
    · left; simp [ha0]
    · right
      rw [padicValRat.mul hb0 hx, hb, padicValRat.mul ha0 (pow_ne_zero 2 hx), padicValRat.pow]
      omega
  have hv := (sum_dominant (mul_ne_zero hb0 hx) huv huw).2
  have heq : b * x + x ^ 3 + a * x ^ 2 = y ^ 2 := by
    unfold OnCurve at h
    linarith
  rw [heq, padicValRat.pow, padicValRat.mul hb0 hx, hb] at hv
  exact ⟨padicValRat p y, by omega⟩

/-- Actual point coordinates have even valuation outside the support of b. -/
theorem x_valuation_even_of_unit_coefficient {a b x y : ℚ}
    (ha : 0 ≤ padicValRat p a) (hb : padicValRat p b = 0) (hb0 : b ≠ 0)
    (hx : x ≠ 0) (h : OnCurve a b x y) : Even (padicValRat p x) := by
  rcases lt_trichotomy (padicValRat p x) 0 with hr | hr | hr
  · exact x_valuation_even_of_negative ha (by omega) hx hr h
  · rw [hr]; exact ⟨0, by omega⟩
  · exact x_valuation_even_of_positive ha hb hb0 hx hr h

/-- Whenever the linear term has strictly smallest valuation, its valuation
is even.  This covers the nonexceptional branches of the fixed-prime and
moving-prime arguments. -/
theorem linear_term_valuation_even {a b x y : ℚ} (hb0 : b ≠ 0) (hx : x ≠ 0)
    (hdegree : padicValRat p b < 2 * padicValRat p x)
    (hquadratic : a = 0 ∨ padicValRat p b < padicValRat p a + padicValRat p x)
    (h : OnCurve a b x y) : Even (padicValRat p b + padicValRat p x) := by
  have hu : x ^ 3 = 0 ∨ padicValRat p (b * x) < padicValRat p (x ^ 3) := by
    right
    rw [padicValRat.mul hb0 hx, padicValRat.pow]
    omega
  have hv : a * x ^ 2 = 0 ∨ padicValRat p (b * x) < padicValRat p (a * x ^ 2) := by
    rcases hquadratic with rfl | hquadratic
    · left; simp
    · by_cases ha0 : a = 0
      · left; simp [ha0]
      · right
        rw [padicValRat.mul hb0 hx, padicValRat.mul ha0 (pow_ne_zero 2 hx), padicValRat.pow]
        omega
  have hval := (sum_dominant (mul_ne_zero hb0 hx) hu hv).2
  have heq : b * x + x ^ 3 + a * x ^ 2 = y ^ 2 := by
    unfold OnCurve at h
    linarith
  rw [heq, padicValRat.pow, padicValRat.mul hb0 hx] at hval
  exact ⟨padicValRat p y, by omega⟩

/-- At a moving prime with `v(a) ≥ 1` and `v(b) = 1`, every positive
x-valuation is odd.  This is a necessary condition on actual points. -/
theorem moving_prime_positive_valuation_odd {a b x y : ℚ}
    (ha : 1 ≤ padicValRat p a) (hb : padicValRat p b = 1)
    (hx : x ≠ 0) (hr : 0 < padicValRat p x) (h : OnCurve a b x y) :
    Odd (padicValRat p x) := by
  have hb0 : b ≠ 0 := by
    intro hzero
    subst b
    simp at hb
  have he := linear_term_valuation_even (p := p) hb0 hx (by omega) (Or.inr (by omega)) h
  obtain ⟨k, hk⟩ := he
  refine ⟨k - 1, ?_⟩
  omega

/-- The complementary branch at a type-III moving prime. -/
theorem moving_prime_negative_valuation_even {a b x y : ℚ}
    (ha : 1 ≤ padicValRat p a) (hb : padicValRat p b = 1)
    (hx : x ≠ 0) (hr : padicValRat p x < 0) (h : OnCurve a b x y) :
    Even (padicValRat p x) :=
  x_valuation_even_of_negative (by omega) (by omega) hx hr h

/-- The full normalized-unit restriction at a type-III moving prime:
either x or b*x agrees with a nonzero square to higher precision. -/
theorem moving_prime_square_approximation {a b x y : ℚ}
    (ha : 1 ≤ padicValRat p a) (hb : padicValRat p b = 1)
    (hx : x ≠ 0) (h : OnCurve a b x y) :
    SquareApproximation p x ∨ SquareApproximation p (b * x) := by
  have hb0 : b ≠ 0 := by
    intro hz; rw [hz] at hb; simp at hb
  by_cases hr : padicValRat p x ≤ 0
  · left
    exact cubic_term_square_approximation hx (Or.inr (by omega)) (Or.inr (by omega)) h
  · right
    exact linear_term_square_approximation (p := p) hb0 hx
      (by omega) (Or.inr (by omega)) h

/-- Two is a unit at every odd prime. -/
theorem valuation_two (hp : p ≠ 2) : padicValRat p (2 : ℚ) = 0 := by
  have hnot : ¬ p ∣ 2 := by
    rw [Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two]
    exact hp
  change padicValRat p ((2 : ℕ) : ℚ) = 0
  rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hnot]
  rfl

theorem valuation_four (hp : p ≠ 2) : padicValRat p (4 : ℚ) = 0 := by
  rw [show (4 : ℚ) = (2 : ℚ) ^ 2 by norm_num, padicValRat.pow, valuation_two hp]
  simp

/-- If the quadratic discriminant has valuation one, an actual unit x
coordinate cannot lie at its repeated residue root.  This is the genuine
exceptional-unit obstruction in the moving-prime descent argument. -/
theorem moving_prime_discriminant_no_exceptional_unit {a b x y : ℚ}
    (hp : p ≠ 2) (hd : padicValRat p (a ^ 2 - 4 * b) = 1)
    (hx : x ≠ 0) (hvx : padicValRat p x = 0) (h : OnCurve a b x y) :
    ¬ (x + a / 2 = 0 ∨ 0 < padicValRat p (x + a / 2)) := by
  intro hex
  have hd0 : a ^ 2 - 4 * b ≠ 0 := by
    intro hz
    rw [hz] at hd
    simp at hd
  have hc0 : -(a ^ 2 - 4 * b) / 4 ≠ 0 := by
    exact div_ne_zero (neg_ne_zero.mpr hd0) (by norm_num)
  have hcv : padicValRat p (-(a ^ 2 - 4 * b) / 4) = 1 := by
    rw [padicValRat.div (neg_ne_zero.mpr hd0) (by norm_num), padicValRat.neg,
      hd, valuation_four hp]
    norm_num
  have hterm : (x + a / 2) ^ 2 = 0 ∨
      padicValRat p (-(a ^ 2 - 4 * b) / 4) < padicValRat p ((x + a / 2) ^ 2) := by
    rcases hex with he | he
    · left; rw [he]; norm_num
    · right; rw [hcv, padicValRat.pow]; omega
  obtain ⟨hs0, hsv⟩ := add_dominant hc0 hterm
  have heq : x * (-(a ^ 2 - 4 * b) / 4 + (x + a / 2) ^ 2) = y ^ 2 := by
    calc
      _ = x ^ 3 + a * x ^ 2 + b * x := by ring
      _ = y ^ 2 := h.symm
  have hval := congrArg (padicValRat p) heq
  rw [padicValRat.mul hx hs0, hsv, hcv, hvx, padicValRat.pow] at hval
  omega

/-- For a unit coordinate at a discriminant prime, completing the square
produces a rational square with the same residue as x. -/
theorem discriminant_prime_unit_square_approximation {a b x y : ℚ}
    (hp : p ≠ 2) (ha : 0 ≤ padicValRat p a)
    (hd : padicValRat p (a ^ 2 - 4 * b) = 1)
    (hx : x ≠ 0) (hvx : padicValRat p x = 0) (h : OnCurve a b x y) :
    SquareApproximation p x := by
  have hnot := moving_prime_discriminant_no_exceptional_unit hp hd hx hvx h
  have ht0 : x + a / 2 ≠ 0 := fun ht => hnot (Or.inl ht)
  have hhalf : 0 ≤ padicValRat p (a / 2) := by
    by_cases ha0 : a = 0
    · simp [ha0]
    · rw [padicValRat.div ha0 (by norm_num), valuation_two hp]
      omega
  have htlow : 0 ≤ padicValRat p (x + a / 2) :=
    (le_min (by omega) hhalf).trans (padicValRat.min_le_padicValRat_add ht0)
  have htval : padicValRat p (x + a / 2) = 0 := by
    have htupper : ¬ 0 < padicValRat p (x + a / 2) := fun ht => hnot (Or.inr ht)
    omega
  have hd0 : a ^ 2 - 4 * b ≠ 0 := by
    intro hz; rw [hz] at hd; simp at hd
  have hc0 : -(a ^ 2 - 4 * b) / 4 ≠ 0 := div_ne_zero (neg_ne_zero.mpr hd0) (by norm_num)
  have hcv : padicValRat p (-(a ^ 2 - 4 * b) / 4) = 1 := by
    rw [padicValRat.div (neg_ne_zero.mpr hd0) (by norm_num), padicValRat.neg,
      hd, valuation_four hp]
    norm_num
  have hq0 : (x + a / 2) ^ 2 + -(a ^ 2 - 4 * b) / 4 ≠ 0 := by
    apply (add_dominant (p := p) (pow_ne_zero 2 ht0) (Or.inr ?_)).1
    rw [padicValRat.pow, htval, hcv]
    norm_num
  have hy : y ≠ 0 := by
    have heq : y ^ 2 = x * ((x + a / 2) ^ 2 + -(a ^ 2 - 4 * b) / 4) := by
      calc
        _ = x ^ 3 + a * x ^ 2 + b * x := h
        _ = _ := by ring
    have hh : y ^ 2 ≠ 0 := heq ▸ mul_ne_zero hx hq0
    exact fun hz => hh (by simp [hz])
  have hdiff : x - (y / (x + a / 2)) ^ 2 =
      x * (a ^ 2 - 4 * b) / (4 * (x + a / 2) ^ 2) := by
    have hraw := h
    unfold OnCurve at hraw
    have ht2 : x * 2 + a ≠ 0 := by
      intro hz
      apply ht0
      linarith
    field_simp [ht0, ht2]
    nlinarith [hraw]
  refine ⟨y / (x + a / 2), div_ne_zero hy ht0, Or.inr ?_⟩
  rw [hdiff, padicValRat.div (mul_ne_zero hx hd0)
    (mul_ne_zero (by norm_num) (pow_ne_zero 2 ht0)), padicValRat.mul hx hd0,
    padicValRat.mul (by norm_num : (4 : ℚ) ≠ 0) (pow_ne_zero 2 ht0),
    padicValRat.pow, valuation_four hp, htval, hd, hvx]
  norm_num

/-- The entire moving-prime restriction for a unit-coefficient curve
whose quadratic discriminant has valuation one.  Every nonzero actual
x-coordinate agrees with a square beyond its valuation. -/
theorem discriminant_prime_square_approximation {a b x y : ℚ}
    (hp : p ≠ 2) (ha0 : a ≠ 0) (ha : padicValRat p a = 0)
    (hb : padicValRat p b = 0) (hd : padicValRat p (a ^ 2 - 4 * b) = 1)
    (hx : x ≠ 0) (h : OnCurve a b x y) : SquareApproximation p x := by
  rcases lt_trichotomy (padicValRat p x) 0 with hr | hr | hr
  · exact cubic_term_square_approximation hx (Or.inr (by omega)) (Or.inr (by omega)) h
  · exact discriminant_prime_unit_square_approximation hp (by omega) hd hx hr h
  · have hk : a / 2 ≠ 0 := div_ne_zero ha0 (by norm_num)
    have hkv : padicValRat p (a / 2) = 0 := by
      rw [padicValRat.div ha0 (by norm_num), ha, valuation_two hp]
      norm_num
    have hd0 : a ^ 2 - 4 * b ≠ 0 := by
      intro hz; rw [hz] at hd; simp at hd
    have hc : -(a ^ 2 - 4 * b) / 4 = 0 ∨
        0 < padicValRat p (-(a ^ 2 - 4 * b) / 4) := by
      right
      rw [padicValRat.div (neg_ne_zero.mpr hd0) (by norm_num), padicValRat.neg,
        hd, valuation_four hp]
      norm_num
    have hcube : x ^ 2 = 0 ∨ 0 < padicValRat p (x ^ 2) := by
      right; rw [padicValRat.pow]; omega
    have hquad : a * x = 0 ∨ 0 < padicValRat p (a * x) := by
      right; rw [padicValRat.mul ha0 hx, ha]; omega
    have hclose : (x ^ 2 + a * x + b) - (a / 2) ^ 2 = 0 ∨
        0 < padicValRat p ((x ^ 2 + a * x + b) - (a / 2) ^ 2) := by
      rw [show (x ^ 2 + a * x + b) - (a / 2) ^ 2 =
        x ^ 2 + a * x + -(a ^ 2 - 4 * b) / 4 by ring]
      exact sum_higher_or_zero (sum_higher_or_zero hcube hquad) hc
    apply square_approximation_of_near_square_factor hx hk hkv hclose
    calc
      y ^ 2 = x ^ 3 + a * x ^ 2 + b * x := h
      _ = x * (x ^ 2 + a * x + b) := by ring

/-- The torsion coefficient has the same local square restriction at
a discriminant prime, with the explicit approximating square `(a/2)^2`. -/
theorem discriminant_prime_coefficient_square_approximation {a b : ℚ}
    (hp : p ≠ 2) (ha0 : a ≠ 0) (hb : padicValRat p b = 0)
    (hd : padicValRat p (a ^ 2 - 4 * b) = 1) : SquareApproximation p b := by
  have hd0 : a ^ 2 - 4 * b ≠ 0 := by
    intro hz; rw [hz] at hd; simp at hd
  refine ⟨a / 2, div_ne_zero ha0 (by norm_num), Or.inr ?_⟩
  rw [show b - (a / 2) ^ 2 = -(a ^ 2 - 4 * b) / 4 by ring,
    padicValRat.div (neg_ne_zero.mpr hd0) (by norm_num), padicValRat.neg,
    hd, valuation_four hp, hb]
  norm_num

/-- Multiplication by a nonzero square preserves the approximation condition. -/
theorem square_approximation_mul_square {x u : ℚ} (hx : x ≠ 0) (hu : u ≠ 0)
    (h : SquareApproximation p x) : SquareApproximation p (x * u ^ 2) := by
  obtain ⟨r, hr, hc⟩ := h
  refine ⟨r * u, mul_ne_zero hr hu, ?_⟩
  rw [show x * u ^ 2 - (r * u) ^ 2 = (x - r ^ 2) * u ^ 2 by ring]
  by_cases hz : x - r ^ 2 = 0
  · left; rw [hz]; simp
  · right
    have hv : padicValRat p x < padicValRat p (x - r ^ 2) := hc.resolve_left hz
    rw [padicValRat.mul hx (pow_ne_zero 2 hu),
      padicValRat.mul hz (pow_ne_zero 2 hu)]
    omega

/-- The normalized-unit square restriction is genuinely independent of
which nonzero rational representative of a squareclass is chosen. -/
theorem same_squareclass_square_approximation {x z : ℚ} (hx : x ≠ 0) (hz : z ≠ 0)
    (hc : rationalSquareClass x = rationalSquareClass z)
    (h : SquareApproximation p z) : SquareApproximation p x := by
  have hclass : rationalSquareClass (x * z) = 1 := by
    rw [rationalSquareClass_mul hx hz, hc]
    exact rationalSquareClass_mul_self z
  obtain ⟨s, hs, heq⟩ := (rationalSquareClass_eq_one_iff (mul_ne_zero hx hz)).mp hclass
  have hfactor : x = z * (s / z) ^ 2 := by
    calc
      x = (x * z) / z := by field_simp [hz]
      _ = s ^ 2 / z := by rw [heq]
      _ = z * (s / z) ^ 2 := by field_simp [hz]
  rw [hfactor]
  exact square_approximation_mul_square hz (div_ne_zero hs hz) h

/-- A local square-character restriction on genuine rational squareclasses. -/
def SquareApproximationClass (p : ℕ) (q : RationalSquareClasses) : Prop :=
  ∀ x : ℚ, x ≠ 0 → rationalSquareClass x = q → SquareApproximation p x

theorem squareApproximationClass_of_representative {x : ℚ} (hx : x ≠ 0)
    (h : SquareApproximation p x) : SquareApproximationClass p (rationalSquareClass x) := by
  intro z hz hc
  exact same_squareclass_square_approximation hz hx hc h

/-- The discriminant-prime square restriction holds for every actual
two-isogeny image and every nonzero rational representative of that image. -/
theorem twoIsogenyImage_discriminant_prime_square_approximation {a b : ℚ}
    (hp : p ≠ 2) (ha0 : a ≠ 0) (ha : padicValRat p a = 0)
    (hb0 : b ≠ 0) (hb : padicValRat p b = 0)
    (hd : padicValRat p (a ^ 2 - 4 * b) = 1)
    {q : RationalSquareClasses} (hq : q ∈ twoIsogenyImage a b) :
    SquareApproximationClass p q := by
  obtain ⟨P, rfl⟩ := hq
  cases P with
  | zero =>
    change SquareApproximationClass p 1
    rw [← rationalSquareClass_one]
    exact squareApproximationClass_of_representative one_ne_zero ⟨1, one_ne_zero, Or.inl (by norm_num)⟩
  | some x y hP =>
    by_cases hx : x = 0
    · simp only [twoIsogenyClass, hx, ite_true]
      exact squareApproximationClass_of_representative hb0
        (discriminant_prime_coefficient_square_approximation hp ha0 hb hd)
    · simp only [twoIsogenyClass, hx, ite_false]
      apply squareApproximationClass_of_representative hx
      exact discriminant_prime_square_approximation hp ha0 ha hb hd hx
        ((onCurve_iff_equation _ _ _ _).mpr hP.1)

/-- At a type-III prime every actual image class, with every nonzero
representative, has the square character of either 1 or b. -/
theorem twoIsogenyImage_moving_prime_square_approximation {a b : ℚ}
    (ha : 1 ≤ padicValRat p a) (hb : padicValRat p b = 1)
    {q : RationalSquareClasses} (hq : q ∈ twoIsogenyImage a b) :
    ∀ z : ℚ, z ≠ 0 → rationalSquareClass z = q →
      SquareApproximation p z ∨ SquareApproximation p (b * z) := by
  have hb0 : b ≠ 0 := by
    intro hz; rw [hz] at hb; simp at hb
  obtain ⟨P, rfl⟩ := hq
  cases P with
  | zero =>
    intro z hz hc
    left
    apply same_squareclass_square_approximation hz one_ne_zero
      (hc.trans rationalSquareClass_one.symm)
    exact ⟨1, one_ne_zero, Or.inl (by norm_num)⟩
  | some x y hP =>
    by_cases hx : x = 0
    · simp only [twoIsogenyClass, hx, ite_true]
      intro z hz hc
      right
      apply same_squareclass_square_approximation (mul_ne_zero hb0 hz) (pow_ne_zero 2 hb0)
      · rw [rationalSquareClass_mul hb0 hz, hc, pow_two, rationalSquareClass_mul hb0 hb0]
      · exact ⟨b, hb0, Or.inl (by ring)⟩
    · simp only [twoIsogenyClass, hx, ite_false]
      intro z hz hc
      rcases moving_prime_square_approximation ha hb hx
        ((onCurve_iff_equation _ _ _ _).mpr hP.1) with he | he
      · left; exact same_squareclass_square_approximation hz hx hc he
      · right
        apply same_squareclass_square_approximation (mul_ne_zero hb0 hz) (mul_ne_zero hb0 hx) _ he
        rw [rationalSquareClass_mul hb0 hz, rationalSquareClass_mul hb0 hx, hc]

omit [Fact p.Prime] in
theorem valuation_int_nonnegative (a : ℤ) : 0 ≤ padicValRat p (a : ℚ) := by
  rw [padicValRat.of_int]
  exact Int.natCast_nonneg _

/-- The standard global support lemma, expressed as parity at each prime. -/
theorem integral_x_valuation_even (a b : ℤ) {x y : ℚ}
    (hb : ¬ (p : ℤ) ∣ b) (hx : x ≠ 0) (h : OnCurve (a : ℚ) (b : ℚ) x y) :
    Even (padicValRat p x) := by
  have hb0 : (b : ℚ) ≠ 0 := by
    exact_mod_cast (show b ≠ 0 from fun hz => hb (hz ▸ dvd_zero _))
  apply x_valuation_even_of_unit_coefficient (valuation_int_nonnegative a) _ hb0 hx h
  rw [padicValRat.of_int]
  exact_mod_cast padicValInt.eq_zero_of_not_dvd hb

/-- Squareclass equality preserves valuation parity. -/
theorem same_squareclass_even_valuation {x z : ℚ} (hx : x ≠ 0) (hz : z ≠ 0)
    (hc : rationalSquareClass x = rationalSquareClass z)
    (he : Even (padicValRat p z)) : Even (padicValRat p x) := by
  have hclass : rationalSquareClass (x * z) = 1 := by
    rw [rationalSquareClass_mul hx hz, hc]
    exact rationalSquareClass_mul_self z
  obtain ⟨s, hs, heq⟩ := (rationalSquareClass_eq_one_iff (mul_ne_zero hx hz)).mp hclass
  have hv := congrArg (padicValRat p) heq
  rw [padicValRat.mul hx hz, padicValRat.pow] at hv
  obtain ⟨k, hk⟩ := he
  exact ⟨padicValRat p s - k, by omega⟩

/-- A property of a genuine squareclass, independent of its representative. -/
def EvenValuationClass (p : ℕ) (q : RationalSquareClasses) : Prop :=
  ∀ x : ℚ, x ≠ 0 → rationalSquareClass x = q → Even (padicValRat p x)

theorem evenValuationClass_of_representative {x : ℚ} (hx : x ≠ 0)
    (he : Even (padicValRat p x)) : EvenValuationClass p (rationalSquareClass x) := by
  intro z hz hc
  exact same_squareclass_even_valuation hz hx hc he

/-- Every actual rational two-isogeny image class has even valuation at any
prime that does not divide the integral coefficient b. -/
theorem twoIsogenyImage_even_valuation (a b : ℤ) (hb : ¬ (p : ℤ) ∣ b)
    {q : RationalSquareClasses} (hq : q ∈ twoIsogenyImage (a : ℚ) (b : ℚ)) :
    EvenValuationClass p q := by
  obtain ⟨P, rfl⟩ := hq
  cases P with
  | zero =>
    change EvenValuationClass p 1
    rw [← rationalSquareClass_one]
    exact evenValuationClass_of_representative one_ne_zero (by simp)
  | some x y hP =>
    by_cases hx : x = 0
    · simp only [twoIsogenyClass, hx, ite_true]
      have hb0 : (b : ℚ) ≠ 0 := by
        exact_mod_cast (show b ≠ 0 from fun hz => hb (hz ▸ dvd_zero _))
      apply evenValuationClass_of_representative hb0
      rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hb]
      exact ⟨0, by omega⟩
    · simp only [twoIsogenyClass, hx, ite_false]
      apply evenValuationClass_of_representative hx
      exact integral_x_valuation_even a b hb hx ((onCurve_iff_equation _ _ _ _).mpr hP.1)

end RankCertificates.LocalDescent
