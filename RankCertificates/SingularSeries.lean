module

public import RankCertificates.Admissibility
public import RankCertificates.PrimePatterns
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Quantitative local counts for homogeneous prime systems

Distinct homogeneous lines in a finite field meet only at the origin.
This module proves their exact forbidden and allowed residue counts. It
provides local-density infrastructure and makes no assertion of actual
simultaneous prime infinitude.
-/

@[expose] public section

namespace RankCertificates.SingularSeries

open scoped BigOperators Classical

/-- The zero line of a homogeneous binary linear form. -/
noncomputable def zeroLine {K : Type*} [Field K] [Fintype K] (a b : K) : Finset (K × K) :=
  Finset.univ.filter (fun z => a * z.1 + b * z.2 = 0)

@[simp] theorem mem_zeroLine {K : Type*} [Field K] [Fintype K] (a b : K) (z : K × K) :
    z ∈ zeroLine a b ↔ a * z.1 + b * z.2 = 0 := by
  classical
  simp [zeroLine]

/-- Every nonzero homogeneous form vanishes at exactly `q` field pairs. -/
theorem card_zeroLine {K : Type*} [Field K] [Fintype K] (a b : K)
    (h : a ≠ 0 ∨ b ≠ 0) : (zeroLine a b).card = Fintype.card K := by
  classical
  by_cases ha : a = 0
  · have hb : b ≠ 0 := h.resolve_left (by simp [ha])
    have he : zeroLine a b = Finset.univ.image (fun x : K => (x, 0)) := by
      ext z
      simp only [mem_zeroLine, ha, zero_mul, zero_add, mul_eq_zero,
        hb, false_or, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · intro hz
        exact ⟨z.1, Prod.ext rfl hz.symm⟩
      · rintro ⟨x, hx⟩
        exact (congrArg Prod.snd hx).symm
    rw [he, Finset.card_image_iff.mpr]
    · simp
    · intro x _ y _ hxy
      exact congrArg Prod.fst hxy
  · have he : zeroLine a b = Finset.univ.image (fun y : K => (-b * y / a, y)) := by
      ext z
      constructor
      · intro hz
        refine Finset.mem_image.mpr ⟨z.2, Finset.mem_univ _, ?_⟩
        have hz' := (mem_zeroLine a b z).mp hz
        refine Prod.ext ?_ rfl
        apply (div_eq_iff ha).mpr
        linear_combination -hz'
      · rintro hz
        obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hz
        apply (mem_zeroLine _ _ _).mpr
        field_simp [ha]
        ring
    rw [he, Finset.card_image_iff.mpr]
    · simp
    · intro x _ y _ hxy
      exact congrArg Prod.snd hxy

/-- Outside the origin, distinct nonproportional zero lines are disjoint. -/
theorem disjoint_punctured_zeroLines {K : Type*} [Field K] [Fintype K]
    (a b a' b' : K) (hdet : a * b' - b * a' ≠ 0) :
    Disjoint ((zeroLine a b).erase (0, 0)) ((zeroLine a' b').erase (0, 0)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  have hz0 := (Finset.mem_erase.mp hz).1
  have h₁ := (mem_zeroLine a b z).mp (Finset.mem_erase.mp hz).2
  have h₂ := (mem_zeroLine a' b' z).mp (Finset.mem_erase.mp hz').2
  have hx : (a * b' - b * a') * z.1 = 0 := by
    linear_combination b' * h₁ - b * h₂
  have hy : (a * b' - b * a') * z.2 = 0 := by
    linear_combination a * h₂ - a' * h₁
  apply hz0
  exact Prod.ext ((mul_eq_zero.mp hx).resolve_left hdet)
    ((mul_eq_zero.mp hy).resolve_left hdet)

/-- Forbidden residue pairs for a finite homogeneous system. -/
noncomputable def forbiddenResidues {K : Type*} [Field K] [Fintype K]
    {n : ℕ} (a b : Fin n → K) : Finset (K × K) :=
  Finset.univ.filter (fun z => ∃ i, a i * z.1 + b i * z.2 = 0)

/-- Allowed residue pairs for a finite homogeneous system. -/
noncomputable def allowedResidues {K : Type*} [Field K] [Fintype K]
    {n : ℕ} (a b : Fin n → K) : Finset (K × K) :=
  Finset.univ.filter (fun z => ∀ i, a i * z.1 + b i * z.2 ≠ 0)

/-- `n` distinct nonzero homogeneous lines forbid exactly `1+n(q-1)` pairs. -/
theorem card_forbiddenResidues {K : Type*} [Field K] [Fintype K]
    {n : ℕ} (a b : Fin n → K) (hn : 0 < n)
    (hcoeff : ∀ i, a i ≠ 0 ∨ b i ≠ 0)
    (hdet : ∀ i j, i ≠ j → a i * b j - b i * a j ≠ 0) :
    (forbiddenResidues a b).card = 1 + n * (Fintype.card K - 1) := by
  classical
  let punctured (i : Fin n) := (zeroLine (a i) (b i)).erase (0, 0)
  let union := Finset.univ.biUnion punctured
  have hcard (i : Fin n) : (punctured i).card = Fintype.card K - 1 := by
    rw [Finset.card_erase_of_mem (by simp), card_zeroLine _ _ (hcoeff i)]
  have hdisjoint : (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint punctured := by
    intro i _ j _ hij
    exact disjoint_punctured_zeroLines _ _ _ _ (hdet i j hij)
  have hunion : union.card = n * (Fintype.card K - 1) := by
    rw [Finset.card_biUnion hdisjoint]
    simp [hcard]
  have hzero : (0, 0) ∉ union := by
    simp [union, punctured]
  have he : forbiddenResidues a b = insert (0, 0) union := by
    ext z
    simp only [forbiddenResidues, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, union, Finset.mem_biUnion, punctured, Finset.mem_erase,
      mem_zeroLine]
    constructor
    · intro hz
      by_cases hz0 : z = (0, 0)
      · exact Or.inl hz0
      · obtain ⟨i, hi⟩ := hz
        exact Or.inr ⟨i, hz0, hi⟩
    · rintro (rfl | ⟨i, _, hi⟩)
      · exact ⟨⟨0, hn⟩, by simp⟩
      · exact ⟨i, hi⟩
  rw [he, Finset.card_insert_of_notMem hzero, hunion]
  omega

/-- Exact complement count: `(q-1)(q+1-n)` pairs avoid all `n` lines. -/
theorem card_allowedResidues {K : Type*} [Field K] [Fintype K]
    {n : ℕ} (a b : Fin n → K) (hn : 0 < n)
    (hcoeff : ∀ i, a i ≠ 0 ∨ b i ≠ 0)
    (hdet : ∀ i j, i ≠ j → a i * b j - b i * a j ≠ 0) :
    (allowedResidues a b).card =
      (Fintype.card K - 1) * (Fintype.card K + 1 - n) := by
  classical
  have hsum : (allowedResidues a b).card + (forbiddenResidues a b).card =
      Fintype.card K ^ 2 := by
    simpa [allowedResidues, forbiddenResidues, not_forall, not_ne_iff, pow_two]
      using Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (K × K)))
        (p := fun z : K × K => ∀ i, a i * z.1 + b i * z.2 ≠ 0)
  rw [card_forbiddenResidues a b hn hcoeff hdet] at hsum
  have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have hqsub := Nat.sub_add_cancel (by omega : 1 ≤ Fintype.card K)
  have hnle : n ≤ Fintype.card K + 1 := by nlinarith
  have hsub := Nat.sub_add_cancel hnle
  nlinarith

/-- The elementary remainder beyond the linear term in Bernoulli's bound. -/
theorem bernoulli_remainder_bounds (m : ℕ) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ (1 - x) ^ m - 1 + m * x ∧
      (1 - x) ^ m - 1 + m * x ≤ (m : ℝ) ^ 2 * x ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hr : (1 - x) ^ (m + 1) - 1 + (m + 1 : ℕ) * x =
        (1 - x) * ((1 - x) ^ m - 1 + m * x) + m * x ^ 2 := by
      push_cast
      rw [pow_succ]
      ring
    rw [hr]
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have ht : 0 ≤ 1 - x := by linarith
    have hmul := mul_le_mul_of_nonneg_right (by linarith : 1 - x ≤ 1) ih.1
    constructor
    · exact add_nonneg (mul_nonneg ht ih.1) (mul_nonneg hm (sq_nonneg x))
    · push_cast
      nlinarith [sq_nonneg x]

/-- Good-prime factor for `n` distinct nonzero homogeneous binary forms. -/
noncomputable def homogeneousLocalFactor (n q : ℕ) : ℝ :=
  (1 - ((n - 1 : ℕ) : ℝ) / q) / (1 - 1 / (q : ℝ)) ^ (n - 1)

/-- The local factor is positive once the field size is at least `n`. -/
theorem homogeneousLocalFactor_pos {n q : ℕ} (hn : 0 < n) (hq : 2 ≤ q)
    (hnq : n ≤ q) : 0 < homogeneousLocalFactor n q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have hmq : ((n - 1 : ℕ) : ℝ) < q := by exact_mod_cast (by omega : n - 1 < q)
  unfold homogeneousLocalFactor
  apply div_pos
  · have := (div_lt_one hq0).mpr hmq
    linarith
  · apply pow_pos
    have := (div_lt_one hq0).mpr hq1
    linarith

/-- A uniform explicit `O(q⁻²)` bound for the normalized good-prime factor. -/
theorem homogeneousLocalFactor_sub_one_bound {n q : ℕ} (hq : 2 ≤ q) :
    |homogeneousLocalFactor n q - 1| ≤
      (((n - 1 : ℕ) : ℝ) ^ 2 * 2 ^ (n - 1)) / (q : ℝ) ^ 2 := by
  let m := n - 1
  let x : ℝ := 1 / q
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hxhalf : x ≤ 1 / 2 := by
    dsimp [x]
    exact one_div_le_one_div_of_le (by norm_num) hq2
  have hxp : 0 < 1 - x := by linarith
  have hR := bernoulli_remainder_bounds m hx (by linarith)
  have hpow : 0 < (1 - x) ^ m := pow_pos hxp _
  have hscale : 1 ≤ (2 : ℝ) ^ m * (1 - x) ^ m := by
    rw [← mul_pow]
    exact one_le_pow₀ (by linarith)
  have hform : homogeneousLocalFactor n q - 1 =
      -((1 - x) ^ m - 1 + m * x) / (1 - x) ^ m := by
    have hmx : (m : ℝ) / (q : ℝ) = m * x := by dsimp [x]; ring
    change (1 - (m : ℝ) / q) / (1 - x) ^ m - 1 = _
    rw [hmx]
    field_simp [hpow.ne']
    ring
  rw [hform, abs_div, abs_neg, abs_of_nonneg hR.1, abs_of_pos hpow]
  apply (div_le_iff₀ hpow).mpr
  have hscale' := mul_le_mul_of_nonneg_left hscale
    (by positivity : 0 ≤ (m : ℝ) ^ 2 * x ^ 2)
  have hbound : (1 - x) ^ m - 1 + m * x ≤
      (m : ℝ) ^ 2 * 2 ^ m * x ^ 2 * (1 - x) ^ m := by
    nlinarith
  simpa [m, x, div_pow, div_eq_mul_inv, mul_assoc] using hbound

/-- The normalized local density, with the standard independent-primality correction. -/
noncomputable def normalizedLocalFactor {K : Type*} [Field K] [Fintype K]
    {n : ℕ} (a b : Fin n → K) : ℝ :=
  ((allowedResidues a b).card : ℝ) / (Fintype.card K : ℝ) ^ 2 /
    (1 - 1 / (Fintype.card K : ℝ)) ^ n

/-- The exact residue count gives the stated good-prime factor, rather than only a bound. -/
theorem normalizedLocalFactor_eq {K : Type*} [Field K] [Fintype K]
    {n : ℕ} (a b : Fin n → K) (hn : 0 < n)
    (hcoeff : ∀ i, a i ≠ 0 ∨ b i ≠ 0)
    (hdet : ∀ i j, i ≠ j → a i * b j - b i * a j ≠ 0)
    (hnq : n ≤ Fintype.card K) :
    normalizedLocalFactor a b = homogeneousLocalFactor n (Fintype.card K) := by
  have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have hq0 : (Fintype.card K : ℝ) ≠ 0 := by exact_mod_cast (by omega : Fintype.card K ≠ 0)
  have hq1 : (1 : ℝ) < Fintype.card K := by exact_mod_cast (by omega : 1 < Fintype.card K)
  have ht : 1 - 1 / (Fintype.card K : ℝ) ≠ 0 := by
    have := (div_lt_one (by linarith : (0 : ℝ) < Fintype.card K)).mpr hq1
    linarith
  unfold normalizedLocalFactor homogeneousLocalFactor
  rw [card_allowedResidues a b hn hcoeff hdet, Nat.cast_mul,
    Nat.cast_sub (by omega : 1 ≤ Fintype.card K),
    Nat.cast_sub (by omega : n ≤ Fintype.card K + 1), Nat.cast_add, Nat.cast_one]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  apply (div_eq_div_iff (pow_ne_zero _ ht) (pow_ne_zero _ ht)).mpr
  have hAB : ((Fintype.card K : ℝ) - 1) *
      ((Fintype.card K : ℝ) + 1 - ((m : ℝ) + 1)) / (Fintype.card K : ℝ) ^ 2 =
      (1 - (m : ℝ) / Fintype.card K) * (1 - 1 / (Fintype.card K : ℝ)) := by
    field_simp [hq0]
    ring
  rw [hAB, pow_succ]
  ring

/-- The Euler-product tail: only sufficiently large primes contribute a factor. -/
noncomputable def goodPrimeFactor (n q : ℕ) : ℝ :=
  if q.Prime ∧ n < q then homogeneousLocalFactor n q else 1

theorem goodPrimeFactor_pos {n : ℕ} (hn : 0 < n) (q : ℕ) :
    0 < goodPrimeFactor n q := by
  unfold goodPrimeFactor
  split_ifs with h
  · exact homogeneousLocalFactor_pos hn h.1.two_le (Nat.le_of_lt h.2)
  · norm_num

theorem goodPrimeFactor_sub_one_bound (n q : ℕ) :
    |goodPrimeFactor n q - 1| ≤
      (((n - 1 : ℕ) : ℝ) ^ 2 * 2 ^ (n - 1)) / (q : ℝ) ^ 2 := by
  unfold goodPrimeFactor
  split_ifs with h
  · exact homogeneousLocalFactor_sub_one_bound h.1.two_le
  · simp only [sub_self, abs_zero]
    positivity

/-- Absolute convergence of the deviations of good-prime local factors. -/
theorem summable_goodPrimeFactor_sub_one (n : ℕ) :
    Summable (fun q : ℕ => goodPrimeFactor n q - 1) := by
  have hs : Summable (fun q : ℕ => 1 / (q : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by decide)
  apply Summable.of_norm_bounded (hs.mul_left
    ((((n - 1 : ℕ) : ℝ) ^ 2 * 2 ^ (n - 1))))
  intro q
  simpa only [Real.norm_eq_abs, mul_one_div] using goodPrimeFactor_sub_one_bound n q

/-- The good-prime Euler product converges to a strictly positive real number. -/
theorem goodPrimeFactor_hasProd_pos {n : ℕ} (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ HasProd (goodPrimeFactor n) c := by
  have hlog : Summable (fun q : ℕ => Real.log (goodPrimeFactor n q)) := by
    simpa only [add_sub_cancel] using
      Real.summable_log_one_add_of_summable (summable_goodPrimeFactor_sub_one n)
  exact ⟨Real.exp (∑' q, Real.log (goodPrimeFactor n q)), Real.exp_pos _,
    Real.hasProd_of_hasSum_log (goodPrimeFactor_pos hn) hlog.hasSum⟩

theorem goodPrimeFactor_multipliable {n : ℕ} (hn : 0 < n) :
    Multipliable (goodPrimeFactor n) := by
  obtain ⟨c, _, hc⟩ := goodPrimeFactor_hasProd_pos hn
  exact ⟨c, hc⟩

theorem goodPrimeFactor_tprod_pos {n : ℕ} (hn : 0 < n) :
    0 < ∏' q, goodPrimeFactor n q := by
  obtain ⟨c, hc, hprod⟩ := goodPrimeFactor_hasProd_pos hn
  rw [hprod.tprod_eq]
  exact hc

/-- Positivity of the true local density is exactly supplied by local avoidance. -/
theorem normalizedLocalFactor_pos_of_admissible {K : Type*} [Field K] [Fintype K]
    {n : ℕ} (a b : Fin n → K)
    (h : ∃ x y : K, ∀ i, a i * x + b i * y ≠ 0) :
    0 < normalizedLocalFactor a b := by
  obtain ⟨x, y, hxy⟩ := h
  have hc : 0 < (allowedResidues a b).card := by
    apply Finset.card_pos.mpr
    exact ⟨(x, y), by simp [allowedResidues, hxy]⟩
  have hq1 : (1 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.one_lt_card (α := K)
  have ht : 0 < 1 - 1 / (Fintype.card K : ℝ) := by
    have := (div_lt_one (by linarith : (0 : ℝ) < Fintype.card K)).mpr hq1
    linarith
  unfold normalizedLocalFactor
  apply div_pos
  · apply div_pos
    · exact_mod_cast hc
    · positivity
  · exact pow_pos ht _

/-- Positive finite changes of the good-prime tail retain a positive convergent product. -/
theorem localFactors_hasProd_pos {n : ℕ} (β : ℕ → ℝ)
    (hpos : ∀ q, 0 < β q)
    (hgood : ∀ᶠ q in Filter.cofinite, β q = goodPrimeFactor n q) :
    ∃ c : ℝ, 0 < c ∧ HasProd β c := by
  have hdev : Summable (fun q => β q - 1) := by
    apply (summable_goodPrimeFactor_sub_one n).congr_cofinite
    filter_upwards [hgood] with q hq
    rw [hq]
  have hlog : Summable (fun q => Real.log (β q)) := by
    simpa only [add_sub_cancel] using Real.summable_log_one_add_of_summable hdev
  exact ⟨Real.exp (∑' q, Real.log (β q)), Real.exp_pos _,
    Real.hasProd_of_hasSum_log hpos hlog.hasSum⟩

/-- The actual prime-indexed normalized densities of an integer homogeneous system. -/
noncomputable def integerLocalFactor {n : ℕ} (a b : Fin n → ℤ) (q : ℕ) : ℝ :=
  if h : q.Prime then
    letI : Fact q.Prime := ⟨h⟩
    normalizedLocalFactor (fun i => (a i : ZMod q)) (fun i => (b i : ZMod q))
  else 1

/-- A nonzero integer remains nonzero modulo every sufficiently large modulus. -/
theorem eventually_intCast_ne_zero (z : ℤ) (hz : z ≠ 0) :
    ∀ᶠ q : ℕ in Filter.cofinite, (z : ZMod q) ≠ 0 := by
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [Filter.eventually_gt_atTop z.natAbs] with q hq
  intro hzero
  have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd z q).mp hzero
  have hle := Int.natAbs_le_of_dvd_ne_zero hdvd hz
  simp only [Int.natAbs_natCast] at hle
  omega

/-- Outside finitely many primes, the true density is the explicit good-prime factor. -/
theorem integerLocalFactor_eventually_eq {n : ℕ} (a b : Fin n → ℤ) (hn : 0 < n)
    (hcoeff : ∀ i, a i ≠ 0 ∨ b i ≠ 0)
    (hdet : ∀ i j, i ≠ j → a i * b j - b i * a j ≠ 0) :
    ∀ᶠ q in Filter.cofinite, integerLocalFactor a b q = goodPrimeFactor n q := by
  have hc : ∀ᶠ q : ℕ in Filter.cofinite,
      ∀ i, (a i : ZMod q) ≠ 0 ∨ (b i : ZMod q) ≠ 0 := by
    apply Filter.eventually_all.mpr
    intro i
    rcases hcoeff i with ha | hb
    · exact (eventually_intCast_ne_zero _ ha).mono (fun q hq => Or.inl hq)
    · exact (eventually_intCast_ne_zero _ hb).mono (fun q hq => Or.inr hq)
  have hd : ∀ᶠ q : ℕ in Filter.cofinite, ∀ i j, i ≠ j →
      ((a i * b j - b i * a j : ℤ) : ZMod q) ≠ 0 := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall (by simp [hij])
    · exact (eventually_intCast_ne_zero _ (hdet i j hij)).mono (fun q hq _ => hq)
  have hnq : ∀ᶠ q : ℕ in Filter.cofinite, n < q := by
    rw [Nat.cofinite_eq_atTop]
    exact Filter.eventually_gt_atTop n
  filter_upwards [hc, hd, hnq] with q hcq hdq hnqq
  by_cases hp : q.Prime
  · let : Fact q.Prime := ⟨hp⟩
    unfold integerLocalFactor goodPrimeFactor
    rw [dite_eq_left hp, ite_eq_left ⟨hp, hnqq⟩]
    have hdc : ∀ i j, i ≠ j →
        (a i : ZMod q) * (b j : ZMod q) - (b i : ZMod q) * (a j : ZMod q) ≠ 0 := by
      intro i j hij
      simpa only [Int.cast_sub, Int.cast_mul] using hdq i j hij
    have hnqc : n ≤ Fintype.card (ZMod q) := by
      simpa only [ZMod.card] using Nat.le_of_lt hnqq
    simpa only [ZMod.card] using normalizedLocalFactor_eq _ _ hn hcq hdc hnqc
  · simp [integerLocalFactor, goodPrimeFactor, hp]

/-- Local admissibility and nonproportionality suffice for positivity and convergence
of the actual singular series of a homogeneous integer system. This asserts a
local analytic property, not simultaneous primality. -/
theorem integerLocalFactor_hasProd_pos {n : ℕ} (a b : Fin n → ℤ) (hn : 0 < n)
    (hcoeff : ∀ i, a i ≠ 0 ∨ b i ≠ 0)
    (hdet : ∀ i j, i ≠ j → a i * b j - b i * a j ≠ 0)
    (hadmissible : ∀ q : ℕ, q.Prime →
      ∃ x y : ZMod q, ∀ i, (a i : ZMod q) * x + (b i : ZMod q) * y ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ HasProd (integerLocalFactor a b) c := by
  apply localFactors_hasProd_pos (n := n)
  · intro q
    by_cases hp : q.Prime
    · let : Fact q.Prime := ⟨hp⟩
      unfold integerLocalFactor
      rw [dite_eq_left hp]
      exact normalizedLocalFactor_pos_of_admissible _ _ (hadmissible q hp)
    · simp only [integerLocalFactor, dite_eq_right hp]
      norm_num
  · exact integerLocalFactor_eventually_eq a b hn hcoeff hdet

/-- Allowed residue pairs for an affine system. -/
noncomputable def affineAllowedResidues {K : Type*} [Field K] [Fintype K]
    {n : ℕ} (a b c : Fin n → K) : Finset (K × K) :=
  Finset.univ.filter (fun z => ∀ i, a i * z.1 + b i * z.2 + c i ≠ 0)

/-- A common translation of homogeneous forms leaves their local avoidance count unchanged. -/
theorem card_affineAllowedResidues_shift {K : Type*} [Field K] [Fintype K]
    {n : ℕ} (a b : Fin n → K) (s t : K) :
    (affineAllowedResidues a b (fun i => a i * s + b i * t)).card =
      (allowedResidues a b).card := by
  have he : affineAllowedResidues a b (fun i => a i * s + b i * t) =
      (allowedResidues a b).image (fun z => (z.1 - s, z.2 - t)) := by
    ext z
    simp only [affineAllowedResidues, allowedResidues, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hz
      refine ⟨(z.1 + s, z.2 + t), ?_, by simp⟩
      intro i
      convert hz i using 1
      ring
    · rintro ⟨w, hw, rfl⟩ i
      convert hw i using 1
      ring
  rw [he, Finset.card_image_iff.mpr]
  intro z _ w _ hzw
  apply Prod.ext
  · exact sub_left_inj.mp (congrArg Prod.fst hzw)
  · exact sub_left_inj.mp (congrArg Prod.snd hzw)

/-- The usual corrected residue density for an affine system. -/
noncomputable def affineNormalizedLocalFactor {K : Type*} [Field K] [Fintype K]
    {n : ℕ} (a b c : Fin n → K) : ℝ :=
  ((affineAllowedResidues a b c).card : ℝ) / (Fintype.card K : ℝ) ^ 2 /
    (1 - 1 / (Fintype.card K : ℝ)) ^ n

theorem affineNormalizedLocalFactor_shift {K : Type*} [Field K] [Fintype K]
    {n : ℕ} (a b : Fin n → K) (s t : K) :
    affineNormalizedLocalFactor a b (fun i => a i * s + b i * t) =
      normalizedLocalFactor a b := by
  simp only [affineNormalizedLocalFactor, normalizedLocalFactor,
    card_affineAllowedResidues_shift]

theorem affineNormalizedLocalFactor_pos {K : Type*} [Field K] [Fintype K]
    {n : ℕ} (a b c : Fin n → K)
    (h : ∃ x y : K, ∀ i, a i * x + b i * y + c i ≠ 0) :
    0 < affineNormalizedLocalFactor a b c := by
  obtain ⟨x, y, hxy⟩ := h
  have hc : 0 < (affineAllowedResidues a b c).card := by
    apply Finset.card_pos.mpr
    exact ⟨(x, y), by simp [affineAllowedResidues, hxy]⟩
  have hq1 : (1 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.one_lt_card (α := K)
  have ht : 0 < 1 - 1 / (Fintype.card K : ℝ) := by
    have := (div_lt_one (by linarith : (0 : ℝ) < Fintype.card K)).mpr hq1
    linarith
  unfold affineNormalizedLocalFactor
  apply div_pos
  · apply div_pos
    · exact_mod_cast hc
    · positivity
  · exact pow_pos ht _

/-- Actual prime-indexed factors for integer affine forms. -/
noncomputable def integerAffineLocalFactor {n : ℕ} (a b c : Fin n → ℤ) (q : ℕ) : ℝ :=
  if h : q.Prime then
    letI : Fact q.Prime := ⟨h⟩
    affineNormalizedLocalFactor (fun i => (a i : ZMod q))
      (fun i => (b i : ZMod q)) (fun i => (c i : ZMod q))
  else 1

/-- A rational common translation changes local factors only at finitely many primes. -/
theorem integerAffineLocalFactor_eventually_eq_homogeneous {n : ℕ}
    (a b c : Fin n → ℤ) (M S T : ℤ) (hM : M ≠ 0)
    (hshift : ∀ i, M * c i = a i * S + b i * T) :
    ∀ᶠ q in Filter.cofinite, integerAffineLocalFactor a b c q = integerLocalFactor a b q := by
  filter_upwards [eventually_intCast_ne_zero M hM] with q hMq
  by_cases hp : q.Prime
  · let : Fact q.Prime := ⟨hp⟩
    have hc : (fun i => (c i : ZMod q)) =
        (fun i => (a i : ZMod q) * ((S : ZMod q) / M) +
          (b i : ZMod q) * ((T : ZMod q) / M)) := by
      funext i
      have hi : (M : ZMod q) * (c i : ZMod q) =
          (a i : ZMod q) * (S : ZMod q) + (b i : ZMod q) * (T : ZMod q) := by
        simpa only [Int.cast_mul, Int.cast_add] using
          congrArg (fun z : ℤ => (z : ZMod q)) (hshift i)
      field_simp [hMq]
      linear_combination hi
    simp only [integerAffineLocalFactor, integerLocalFactor, dite_eq_left hp]
    rw [hc, affineNormalizedLocalFactor_shift]
  · simp only [integerAffineLocalFactor, integerLocalFactor, dite_eq_right hp]

/-- Positive convergent singular series for a locally admissible affine system
that is a rational common translation of pairwise nonproportional homogeneous forms. -/
theorem integerAffineLocalFactor_hasProd_pos {n : ℕ} (a b c : Fin n → ℤ)
    (hn : 0 < n) (hcoeff : ∀ i, a i ≠ 0 ∨ b i ≠ 0)
    (hdet : ∀ i j, i ≠ j → a i * b j - b i * a j ≠ 0)
    (M S T : ℤ) (hM : M ≠ 0) (hshift : ∀ i, M * c i = a i * S + b i * T)
    (hadmissible : ∀ q : ℕ, q.Prime → ∃ x y : ZMod q,
      ∀ i, (a i : ZMod q) * x + (b i : ZMod q) * y + (c i : ZMod q) ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ HasProd (integerAffineLocalFactor a b c) C := by
  apply localFactors_hasProd_pos (n := n)
  · intro q
    by_cases hp : q.Prime
    · let : Fact q.Prime := ⟨hp⟩
      simp only [integerAffineLocalFactor, dite_eq_left hp]
      exact affineNormalizedLocalFactor_pos _ _ _ (hadmissible q hp)
    · simp only [integerAffineLocalFactor, dite_eq_right hp]
      norm_num
  · exact Filter.EventuallyEq.trans
      (integerAffineLocalFactor_eventually_eq_homogeneous a b c M S T hM hshift)
      (integerLocalFactor_eventually_eq a b hn hcoeff hdet)

/-- Integer modular avoidance gives the same finite-field avoidance witness. -/
theorem modular_admissible_of_avoids (fs : Fin 12 → PrimePatterns.AffineForm)
    (q : ℕ) (h : PrimePatterns.Avoids fs q) :
    ∃ x y : ZMod q, ∀ i, ((fs i).a : ZMod q) * x + ((fs i).b : ZMod q) * y +
      ((fs i).c : ZMod q) ≠ 0 := by
  obtain ⟨x, y, hxy⟩ := h
  refine ⟨(x : ZMod q), (y : ZMod q), ?_⟩
  intro i hi
  have hz : ((fs i).eval x y : ZMod q) = 0 := by
    simpa only [PrimePatterns.AffineForm.eval, Int.cast_add, Int.cast_mul] using hi
  exact hxy i (Int.emod_eq_zero_of_dvd
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hz))

/-- Actual local factors of the twelve affine outputs. -/
noncomputable def outputsLocalFactor (fs : Fin 12 → PrimePatterns.AffineForm) : ℕ → ℝ :=
  integerAffineLocalFactor (fun i => (fs i).a) (fun i => (fs i).b) (fun i => (fs i).c)

theorem outputsLocalFactor_hasProd_pos (fs : Fin 12 → PrimePatterns.AffineForm)
    (M S T : ℤ) (hM : M ≠ 0)
    (hcoeff : ∀ i, (fs i).a ≠ 0 ∨ (fs i).b ≠ 0)
    (hdet : ∀ i j, i ≠ j → (fs i).a * (fs j).b - (fs i).b * (fs j).a ≠ 0)
    (hshift : ∀ i, M * (fs i).c = (fs i).a * S + (fs i).b * T)
    (hlocal : ∀ q, q.Prime → PrimePatterns.Avoids fs q) :
    ∃ C : ℝ, 0 < C ∧ HasProd (outputsLocalFactor fs) C := by
  apply integerAffineLocalFactor_hasProd_pos _ _ _ (by decide) hcoeff hdet M S T hM hshift
  intro q hq
  exact modular_admissible_of_avoids fs q (hlocal q hq)

/-- The rank-five affine prime system has a positive convergent actual singular series. -/
theorem rank5_singularSeries_hasProd_pos :
    ∃ C : ℝ, 0 < C ∧ HasProd (outputsLocalFactor PrimePatterns.Rank5.outputs) C := by
  apply outputsLocalFactor_hasProd_pos _ PrimePatterns.Rank5.W
    PrimePatterns.Rank5.M0 PrimePatterns.Rank5.N0
  · norm_num [PrimePatterns.Rank5.W]
  · intro i
    fin_cases i <;> norm_num [PrimePatterns.Rank5.outputs]
  · exact PrimePatterns.Rank5.nonparallel_outputs
  · intro i
    fin_cases i <;> norm_num [PrimePatterns.Rank5.outputs, PrimePatterns.Rank5.W,
      PrimePatterns.Rank5.M0, PrimePatterns.Rank5.N0]
  · exact PrimePatterns.Rank5.local_admissibility

/-- The rank-six affine prime system has a positive convergent actual singular series. -/
theorem rank6_singularSeries_hasProd_pos :
    ∃ C : ℝ, 0 < C ∧ HasProd (outputsLocalFactor PrimePatterns.Rank6.outputs) C := by
  apply outputsLocalFactor_hasProd_pos _ PrimePatterns.Rank6.W
    PrimePatterns.Rank6.M0 PrimePatterns.Rank6.N0
  · norm_num [PrimePatterns.Rank6.W]
  · intro i
    fin_cases i <;> norm_num [PrimePatterns.Rank6.outputs]
  · exact PrimePatterns.Rank6.nonparallel_outputs
  · intro i
    fin_cases i <;> norm_num [PrimePatterns.Rank6.outputs, PrimePatterns.Rank6.W,
      PrimePatterns.Rank6.M0, PrimePatterns.Rank6.N0]
  · exact PrimePatterns.Rank6.local_admissibility

/-- The rank-seven affine prime system has a positive convergent actual singular series. -/
theorem rank7_singularSeries_hasProd_pos :
    ∃ C : ℝ, 0 < C ∧ HasProd (outputsLocalFactor PrimePatterns.Rank7.outputs) C := by
  apply outputsLocalFactor_hasProd_pos _ PrimePatterns.Rank7.W
    PrimePatterns.Rank7.M0 PrimePatterns.Rank7.N0
  · norm_num [PrimePatterns.Rank7.W]
  · intro i
    fin_cases i <;> norm_num [PrimePatterns.Rank7.outputs]
  · exact PrimePatterns.Rank7.nonparallel_outputs
  · intro i
    fin_cases i <;> norm_num [PrimePatterns.Rank7.outputs, PrimePatterns.Rank7.W,
      PrimePatterns.Rank7.M0, PrimePatterns.Rank7.N0]
  · exact PrimePatterns.Rank7.local_admissibility

end RankCertificates.SingularSeries
