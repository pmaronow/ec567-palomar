module

public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.Tactic

@[expose] public section

namespace RankCertificates.AnalyticExtraction

open scoped BigOperators

structure IntegerAffine where
  a : ℤ
  b : ℤ
  c : ℤ

def IntegerAffine.eval (ψ : IntegerAffine) (z : ℤ × ℤ) : ℤ :=
  ψ.a * z.1 + ψ.b * z.2 + ψ.c

def box (B : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B

def level (B : ℕ) (ψ : IntegerAffine) (q : ℤ) : Finset (ℤ × ℤ) :=
  (box B).filter (fun z => ψ.eval z = q)

theorem card_le_coordinateBound (B : ℕ) (S : Finset (ℤ × ℤ))
    (π : ℤ × ℤ → ℤ) (hS : ∀ z ∈ S, π z ∈ Finset.Icc (-(B : ℤ)) B)
    (hinj : Set.InjOn π (S : Set (ℤ × ℤ))) : S.card ≤ 2 * B + 1 := by
  have hsub : S.image π ⊆ Finset.Icc (-(B : ℤ)) B := by
    intro n hn
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hn
    exact hS z hz
  calc
    S.card = (S.image π).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (Finset.Icc (-(B : ℤ)) B).card := Finset.card_le_card hsub
    _ = 2 * B + 1 := by rw [Int.card_Icc]; omega

/-- An affine level in a square has at most one point above each coordinate. -/
theorem level_card_le (B : ℕ) (ψ : IntegerAffine) (q : ℤ)
    (hψ : ψ.a ≠ 0 ∨ ψ.b ≠ 0) : (level B ψ q).card ≤ 2 * B + 1 := by
  rcases hψ with ha | hb
  · apply card_le_coordinateBound B (level B ψ q) Prod.snd
    · intro z hz
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hz).1).2
    · intro z hz z' hz' heq
      have he := (Finset.mem_filter.mp hz).2
      have he' := (Finset.mem_filter.mp hz').2
      apply Prod.ext _ heq
      apply mul_left_cancel₀ ha
      dsimp [IntegerAffine.eval] at he he'
      rw [heq] at he
      linarith
  · apply card_le_coordinateBound B (level B ψ q) Prod.fst
    · intro z hz
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hz).1).1
    · intro z hz z' hz' heq
      have he := (Finset.mem_filter.mp hz).2
      have he' := (Finset.mem_filter.mp hz').2
      apply Prod.ext heq
      apply mul_left_cancel₀ hb
      dsimp [IntegerAffine.eval] at he he'
      rw [heq] at he
      linarith

/-- Removing finitely many output values costs at most their number times
the number of lattice points on a line. -/
theorem values_card_le (B : ℕ) (ψ : IntegerAffine) (Q : Finset ℤ)
    (hψ : ψ.a ≠ 0 ∨ ψ.b ≠ 0) :
    ((box B).filter (fun z => ψ.eval z ∈ Q)).card ≤ Q.card * (2 * B + 1) := by
  let S := (box B).filter (fun z => ψ.eval z ∈ Q)
  by_contra h
  have hlt : Q.card * (2 * B + 1) < S.card := Nat.lt_of_not_ge h
  obtain ⟨q, hq, hf⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (f := ψ.eval) (s := S) (t := Q) (n := 2 * B + 1)
    (fun z hz => (Finset.mem_filter.mp hz).2) hlt
  have hsub : S.filter (fun z => ψ.eval z = q) ⊆ level B ψ q := by
    intro z hz
    obtain ⟨hzS, he⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hzS).1, he⟩
  have hle := (Finset.card_le_card hsub).trans (level_card_le B ψ q hψ)
  exact (not_lt_of_ge hle) hf

/-- A finite candidate set for every proper natural power up to X. Using
all bases, rather than just primes, gives a valid uniform upper bound. -/
def powerCandidates (X : ℕ) : Finset ℕ :=
  ((Finset.range (Nat.sqrt X + 1)) ×ˢ (Finset.range (Nat.log 2 X + 1))).image
    (fun z : ℕ × ℕ => z.1 ^ z.2)

theorem mem_powerCandidates {X p k : ℕ} (hp : 2 ≤ p) (hk : 2 ≤ k)
    (hpk : p ^ k ≤ X) : p ^ k ∈ powerCandidates X := by
  have hp2 : p ^ 2 ≤ X := (Nat.pow_le_pow_right (by omega) hk).trans hpk
  have hpsqrt : p ≤ Nat.sqrt X := Nat.le_sqrt'.mpr hp2
  have hklog : k ≤ Nat.log 2 X :=
    Nat.le_log_of_pow_le (by decide) ((Nat.pow_le_pow_left hp k).trans hpk)
  apply Finset.mem_image.mpr
  refine ⟨(p, k), ?_, rfl⟩
  exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩

theorem powerCandidates_card_le (X : ℕ) :
    (powerCandidates X).card ≤ (Nat.sqrt X + 1) * (Nat.log 2 X + 1) := by
  exact (Finset.card_image_le).trans (by simp)

/-- The exact finite counting bound used to remove proper prime powers
from a two-dimensional affine prime pattern. -/
theorem properPower_points_card_le (B X : ℕ) (ψ : IntegerAffine)
    (hψ : ψ.a ≠ 0 ∨ ψ.b ≠ 0) :
    ((box B).filter (fun z => ψ.eval z ∈ (powerCandidates X).image (Int.ofNat))).card ≤
      ((Nat.sqrt X + 1) * (Nat.log 2 X + 1)) * (2 * B + 1) := by
  exact (values_card_le B ψ _ hψ).trans
    (Nat.mul_le_mul_right _ ((Finset.card_image_le).trans (powerCandidates_card_le X)))

theorem vonMangoldt_nonprime_mem_powerCandidates {X n : ℕ}
    (hnX : n ≤ X) (hnot : ¬ n.Prime)
    (hweight : ArithmeticFunction.vonMangoldt n ≠ 0) : n ∈ powerCandidates X := by
  have hpow : IsPrimePow n := by
    by_contra hn
    exact hweight (by simp only [ArithmeticFunction.vonMangoldt_apply, ite_eq_right hn])
  obtain ⟨p, k, hp, hk, heq⟩ := isPrimePow_nat_iff n |>.mp hpow
  have hk2 : 2 ≤ k := by
    by_contra! hn
    have hk1 : k = 1 := by omega
    rw [hk1, pow_one] at heq
    exact hnot (heq ▸ hp)
  rw [← heq]
  exact mem_powerCandidates hp.two_le hk2 (heq ▸ hnX)

noncomputable def nonprimeSupport (B X : ℕ) (ψ : IntegerAffine) : Finset (ℤ × ℤ) :=
  (box B).filter (fun z => 0 ≤ ψ.eval z ∧ ψ.eval z ≤ X ∧
    ¬ (ψ.eval z).toNat.Prime ∧ ArithmeticFunction.vonMangoldt (ψ.eval z).toNat ≠ 0)

/-- Actual nonprime von Mangoldt support in a bounded affine box has the
prime-power extraction bound. No prime-counting premise occurs here. -/
theorem nonprimeSupport_card_le (B X : ℕ) (ψ : IntegerAffine)
    (hψ : ψ.a ≠ 0 ∨ ψ.b ≠ 0) :
    (nonprimeSupport B X ψ).card ≤
      ((Nat.sqrt X + 1) * (Nat.log 2 X + 1)) * (2 * B + 1) := by
  have hsub : nonprimeSupport B X ψ ⊆
      (box B).filter (fun z => ψ.eval z ∈ (powerCandidates X).image Int.ofNat) := by
    intro z hz
    obtain ⟨hzBox, hnonneg, hbound, hnot, hw⟩ := Finset.mem_filter.mp hz
    have hnX : (ψ.eval z).toNat ≤ X := by omega
    have hmem := vonMangoldt_nonprime_mem_powerCandidates hnX hnot hw
    refine Finset.mem_filter.mpr ⟨hzBox, ?_⟩
    exact Finset.mem_image.mpr ⟨(ψ.eval z).toNat, hmem, Int.toNat_of_nonneg hnonneg⟩
  exact (Finset.card_le_card hsub).trans (properPower_points_card_le B X ψ hψ)

def IntegerAffine.sub (ψ θ : IntegerAffine) : IntegerAffine :=
  ⟨ψ.a - θ.a, ψ.b - θ.b, ψ.c - θ.c⟩

@[simp] theorem IntegerAffine.sub_eval (ψ θ : IntegerAffine) (z : ℤ × ℤ) :
    (ψ.sub θ).eval z = ψ.eval z - θ.eval z := by
  dsimp [sub, eval]
  ring

/-- The coincidence set of two forms with different linear parts costs
only one line of lattice points. -/
theorem diagonal_card_le (B : ℕ) (ψ θ : IntegerAffine)
    (hparts : ψ.a ≠ θ.a ∨ ψ.b ≠ θ.b) :
    ((box B).filter (fun z => ψ.eval z = θ.eval z)).card ≤ 2 * B + 1 := by
  have heq : (box B).filter (fun z => ψ.eval z = θ.eval z) = level B (ψ.sub θ) 0 := by
    ext z
    simp only [Finset.mem_filter, level, IntegerAffine.sub_eval, sub_eq_zero]
  rw [heq]
  apply level_card_le
  rcases hparts with ha | hb
  · exact Or.inl (sub_ne_zero.mpr ha)
  · exact Or.inr (sub_ne_zero.mpr hb)

/-- Union bound for actual nonprime support across any finite affine system. -/
theorem nonprimeUnion_card_le {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (B X : ℕ) (ψ : ι → IntegerAffine)
    (hψ : ∀ i ∈ I, (ψ i).a ≠ 0 ∨ (ψ i).b ≠ 0) :
    (I.biUnion (fun i => nonprimeSupport B X (ψ i))).card ≤
      I.card * (((Nat.sqrt X + 1) * (Nat.log 2 X + 1)) * (2 * B + 1)) :=
  Finset.card_biUnion_le_card_mul I _ _ (fun i hi => nonprimeSupport_card_le B X (ψ i) (hψ i hi))

theorem vonMangoldt_le_log_bound {n X : ℕ} (hX : 1 ≤ X) (hn : n ≤ X) :
    ArithmeticFunction.vonMangoldt n ≤ Real.log X := by
  by_cases hn0 : n = 0
  · simpa only [hn0, ArithmeticFunction.map_zero] using
      Real.log_nonneg (by exact_mod_cast hX : (1 : ℝ) ≤ X)
  · exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hn0) (by exact_mod_cast hn))

noncomputable def patternWeight (ψ : Fin 12 → IntegerAffine) (z : ℤ × ℤ) : ℝ :=
  ∏ i, ArithmeticFunction.vonMangoldt ((ψ i).eval z).toNat

theorem patternWeight_nonnegative (ψ : Fin 12 → IntegerAffine) (z : ℤ × ℤ) :
    0 ≤ patternWeight ψ z :=
  Finset.prod_nonneg (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)

theorem patternWeight_le_log_power (ψ : Fin 12 → IntegerAffine) (z : ℤ × ℤ)
    {X : ℕ} (hX : 1 ≤ X) (hbound : ∀ i, ((ψ i).eval z).toNat ≤ X) :
    patternWeight ψ z ≤ (Real.log X) ^ 12 := by
  calc
    _ ≤ ∏ _i : Fin 12, Real.log X := Finset.prod_le_prod₀
      (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)
      (fun i _ => vonMangoldt_le_log_bound hX (hbound i))
    _ = _ := by simp

noncomputable def nonprimePatternSupport (B : ℕ) (ψ : Fin 12 → IntegerAffine) :
    Finset (ℤ × ℤ) :=
  (box B).filter (fun z => patternWeight ψ z ≠ 0 ∧ ∃ i, ¬ ((ψ i).eval z).toNat.Prime)

theorem nonprimePatternSupport_card_le (B X : ℕ) (ψ : Fin 12 → IntegerAffine)
    (hψ : ∀ i, (ψ i).a ≠ 0 ∨ (ψ i).b ≠ 0)
    (hbound : ∀ z ∈ box B, ∀ i, ((ψ i).eval z).toNat ≤ X) :
    (nonprimePatternSupport B ψ).card ≤
      12 * (((Nat.sqrt X + 1) * (Nat.log 2 X + 1)) * (2 * B + 1)) := by
  have hsub : nonprimePatternSupport B ψ ⊆
      Finset.univ.biUnion (fun i : Fin 12 => nonprimeSupport B X (ψ i)) := by
    intro z hz
    obtain ⟨hzBox, hw, i, hi⟩ := Finset.mem_filter.mp hz
    have hfac : ArithmeticFunction.vonMangoldt ((ψ i).eval z).toNat ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hw) i (Finset.mem_univ i)
    have hn0 : ((ψ i).eval z).toNat ≠ 0 := by
      intro hn
      apply hfac
      rw [hn, ArithmeticFunction.map_zero]
    have hnonneg : 0 ≤ (ψ i).eval z :=
      by omega
    have hupper : (ψ i).eval z ≤ X := by
      have hh : (((ψ i).eval z).toNat : ℤ) ≤ X := by exact_mod_cast hbound z hzBox i
      simpa only [Int.toNat_of_nonneg hnonneg] using hh
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
      Finset.mem_filter.mpr ⟨hzBox, hnonneg, hupper, hi, hfac⟩⟩
  exact (Finset.card_le_card hsub).trans (by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      nonprimeUnion_card_le Finset.univ B X ψ (fun i _ => hψ i))

/-- The actual twelve-fold von Mangoldt mass discarded at nonprime outputs
has an explicit finite bound of size B sqrt(X) log(X)^13. -/
theorem nonprimePattern_mass_le (B X : ℕ) (ψ : Fin 12 → IntegerAffine)
    (hX : 1 ≤ X) (hψ : ∀ i, (ψ i).a ≠ 0 ∨ (ψ i).b ≠ 0)
    (hbound : ∀ z ∈ box B, ∀ i, ((ψ i).eval z).toNat ≤ X) :
    ∑ z ∈ nonprimePatternSupport B ψ, patternWeight ψ z ≤
      (12 * (((Nat.sqrt X + 1) * (Nat.log 2 X + 1)) * (2 * B + 1)) : ℕ) *
        (Real.log X) ^ 12 := by
  calc
    _ ≤ ∑ _z ∈ nonprimePatternSupport B ψ, (Real.log X) ^ 12 := by
      apply Finset.sum_le_sum
      intro z hz
      exact patternWeight_le_log_power ψ z hX (hbound z (Finset.mem_filter.mp hz).1)
    _ = ((nonprimePatternSupport B ψ).card : ℝ) * (Real.log X) ^ 12 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast nonprimePatternSupport_card_le B X ψ hψ hbound)
      (by positivity)

end RankCertificates.AnalyticExtraction
