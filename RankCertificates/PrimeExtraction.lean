module

public import RankCertificates.FiniteExclusions
public import RankCertificates.ExtractionAsymptotics

@[expose] public section

namespace RankCertificates.AnalyticExtraction

open scoped BigOperators
open Filter Asymptotics

/-- All twelve actual integer outputs are positive, distinct primes outside Q. -/
def primePattern (ψ : Fin 12 → IntegerAffine) (Q : Finset ℤ) (z : ℤ × ℤ) : Prop :=
  (∀ i, 0 < (ψ i).eval z ∧ ((ψ i).eval z).toNat.Prime ∧ (ψ i).eval z ∉ Q) ∧
    Function.Injective (fun i => (ψ i).eval z)

def primePatternAvoidingLines {ι : Type*} [DecidableEq ι]
    (ψ : Fin 12 → IntegerAffine) (Q : Finset ℤ) (I : Finset ι)
    (θ : ι → IntegerAffine) (z : ℤ × ℤ) : Prop :=
  primePattern ψ Q z ∧ ∀ i ∈ I, (θ i).eval z ≠ 0

theorem patternWeight_ne_zero_outputs_positive (ψ : Fin 12 → IntegerAffine)
    (z : ℤ × ℤ) (hw : patternWeight ψ z ≠ 0) (i : Fin 12) :
    0 < (ψ i).eval z := by
  have hfac : ArithmeticFunction.vonMangoldt ((ψ i).eval z).toNat ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hw) i (Finset.mem_univ i)
  have hn : ((ψ i).eval z).toNat ≠ 0 := by
    intro hn
    exact hfac (by rw [hn, ArithmeticFunction.map_zero])
  omega

noncomputable def badPatternSupport {ι : Type*} [DecidableEq ι]
    (B : ℕ) (ψ : Fin 12 → IntegerAffine) (Q : Finset ℤ)
    (I : Finset ι) (θ : ι → IntegerAffine) : Finset (ℤ × ℤ) :=
  ((nonprimePatternSupport B ψ ∪ finiteValueSupport B ψ Q) ∪ diagonalSupport B ψ) ∪
    affineLineSupport B I θ

theorem badPatternSupport_subset_box {ι : Type*} [DecidableEq ι]
    (B : ℕ) (ψ : Fin 12 → IntegerAffine) (Q : Finset ℤ)
    (I : Finset ι) (θ : ι → IntegerAffine) :
    badPatternSupport B ψ Q I θ ⊆ box B := by
  intro z hz
  rcases Finset.mem_union.mp hz with hz | hz
  · rcases Finset.mem_union.mp hz with hz | hz
    · rcases Finset.mem_union.mp hz with hz | hz
      · exact (Finset.mem_filter.mp hz).1
      · exact ((mem_finiteValueSupport B ψ Q z).mp hz).1
    · exact ((mem_diagonalSupport B ψ z).mp hz).1
  · exact ((mem_affineLineSupport B I θ z).mp hz).1

theorem mem_badPatternSupport_of_not_good {ι : Type*} [DecidableEq ι]
    (B : ℕ) (ψ : Fin 12 → IntegerAffine) (Q : Finset ℤ)
    (I : Finset ι) (θ : ι → IntegerAffine) (z : ℤ × ℤ)
    (hz : z ∈ box B) (hw : patternWeight ψ z ≠ 0)
    (hbad : ¬ primePatternAvoidingLines ψ Q I θ z) :
    z ∈ badPatternSupport B ψ Q I θ := by
  classical
  by_cases hp : ∀ i, ((ψ i).eval z).toNat.Prime
  · by_cases hQ : ∀ i, (ψ i).eval z ∉ Q
    · by_cases hi : Function.Injective (fun i => (ψ i).eval z)
      · have hl : ¬ ∀ i ∈ I, (θ i).eval z ≠ 0 := by
          intro hl
          exact hbad ⟨⟨fun i => ⟨patternWeight_ne_zero_outputs_positive ψ z hw i,
            hp i, hQ i⟩, hi⟩, hl⟩
        push Not at hl
        exact Finset.mem_union_right _ ((mem_affineLineSupport B I θ z).mpr ⟨hz, hl⟩)
      · have hex : ∃ i j, i ≠ j ∧ (ψ i).eval z = (ψ j).eval z := by
          by_contra! h
          exact hi (fun i j hij => by_contra fun hne => h i j hne hij)
        exact Finset.mem_union_left _ (Finset.mem_union_right _
          ((mem_diagonalSupport B ψ z).mpr ⟨hz, hex⟩))
    · push Not at hQ
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
        ((mem_finiteValueSupport B ψ Q z).mpr ⟨hz, hQ⟩)))
  · push Not at hp
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨hz, hw, hp⟩)))

theorem badPatternSupport_card_le {ι : Type*} [DecidableEq ι]
    (B X : ℕ) (ψ : Fin 12 → IntegerAffine) (Q : Finset ℤ)
    (I : Finset ι) (θ : ι → IntegerAffine)
    (hψ : ∀ i, (ψ i).a ≠ 0 ∨ (ψ i).b ≠ 0)
    (hparts : ∀ i j, i ≠ j → (ψ i).a ≠ (ψ j).a ∨ (ψ i).b ≠ (ψ j).b)
    (hθ : ∀ i ∈ I, (θ i).a ≠ 0 ∨ (θ i).b ≠ 0)
    (hbound : ∀ z ∈ box B, ∀ i, ((ψ i).eval z).toNat ≤ X) :
    (badPatternSupport B ψ Q I θ).card ≤
      12 * (((Nat.sqrt X + 1) * (Nat.log 2 X + 1)) * (2 * B + 1)) +
      (12 * Q.card + 144 + I.card) * (2 * B + 1) := by
  have hn := nonprimePatternSupport_card_le B X ψ hψ hbound
  have hv := finiteValueSupport_card_le B ψ Q hψ
  have hd := diagonalSupport_card_le B ψ hparts
  have hl := affineLineSupport_card_le B I θ hθ
  have hu₁ := Finset.card_union_le (nonprimePatternSupport B ψ) (finiteValueSupport B ψ Q)
  have hu₂ := Finset.card_union_le
    (nonprimePatternSupport B ψ ∪ finiteValueSupport B ψ Q) (diagonalSupport B ψ)
  have hu₃ := Finset.card_union_le
    ((nonprimePatternSupport B ψ ∪ finiteValueSupport B ψ Q) ∪ diagonalSupport B ψ)
    (affineLineSupport B I θ)
  dsimp only [badPatternSupport]
  calc
    _ ≤ (nonprimePatternSupport B ψ).card + (finiteValueSupport B ψ Q).card +
        (diagonalSupport B ψ).card + (affineLineSupport B I θ).card := by omega
    _ ≤ _ := by nlinarith

/-- If a finite region contains no good prime tuple, all its actual Mangoldt mass
is bounded by the prime-power, finite-value, diagonal, and affine-line errors. -/
theorem region_mass_le_extraction_error_of_no_good {ι : Type*} [DecidableEq ι]
    (B X : ℕ) (ψ : Fin 12 → IntegerAffine) (Q : Finset ℤ)
    (I : Finset ι) (θ : ι → IntegerAffine) (R : Finset (ℤ × ℤ))
    (hR : R ⊆ box B) (hX : 1 ≤ X)
    (hψ : ∀ i, (ψ i).a ≠ 0 ∨ (ψ i).b ≠ 0)
    (hparts : ∀ i j, i ≠ j → (ψ i).a ≠ (ψ j).a ∨ (ψ i).b ≠ (ψ j).b)
    (hθ : ∀ i ∈ I, (θ i).a ≠ 0 ∨ (θ i).b ≠ 0)
    (hbound : ∀ z ∈ box B, ∀ i, ((ψ i).eval z).toNat ≤ X)
    (hbad : ∀ z ∈ R, ¬ primePatternAvoidingLines ψ Q I θ z) :
    ∑ z ∈ R, patternWeight ψ z ≤
      ((12 * (((Nat.sqrt X + 1) * (Nat.log 2 X + 1)) * (2 * B + 1)) +
        (12 * Q.card + 144 + I.card) * (2 * B + 1) : ℕ) : ℝ) * (Real.log X) ^ 12 := by
  classical
  have hsub : R.filter (fun z => patternWeight ψ z ≠ 0) ⊆
      badPatternSupport B ψ Q I θ := by
    intro z hz
    obtain ⟨hz, hw⟩ := Finset.mem_filter.mp hz
    exact mem_badPatternSupport_of_not_good B ψ Q I θ z (hR hz) hw (hbad z hz)
  calc
    _ = ∑ z ∈ R.filter (fun z => patternWeight ψ z ≠ 0), patternWeight ψ z :=
      (Finset.sum_filter_ne_zero R).symm
    _ ≤ ∑ z ∈ badPatternSupport B ψ Q I θ, patternWeight ψ z :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => patternWeight_nonnegative ψ z)
    _ ≤ ((badPatternSupport B ψ Q I θ).card : ℝ) * (Real.log X) ^ 12 :=
      patternWeight_sum_le_card_mul_log B X ψ _
        (badPatternSupport_subset_box B ψ Q I θ) hX hbound
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast badPatternSupport_card_le B X ψ Q I θ hψ hparts hθ hbound)
      (by positivity)

/-- A positive quadratic lower bound for the actual weighted count supplies
prime tuples after every prescribed finite value and line exclusion.
The quadratic counting estimate is an explicit hypothesis. -/
theorem eventually_primePatternAvoidingLines_of_quadratic_lower
    {ι : Type*} [DecidableEq ι]
    (ψ : Fin 12 → IntegerAffine) (Q : Finset ℤ)
    (I : Finset ι) (θ : ι → IntegerAffine)
    (R : ℕ → Finset (ℤ × ℤ)) (C : ℕ) (c : ℝ)
    (hR : ∀ B, R B ⊆ box B) (hC : 1 ≤ C) (hc : 0 < c)
    (hψ : ∀ i, (ψ i).a ≠ 0 ∨ (ψ i).b ≠ 0)
    (hparts : ∀ i j, i ≠ j → (ψ i).a ≠ (ψ j).a ∨ (ψ i).b ≠ (ψ j).b)
    (hθ : ∀ i ∈ I, (θ i).a ≠ 0 ∨ (θ i).b ≠ 0)
    (hbound : ∀ B, ∀ z ∈ box B, ∀ i, ((ψ i).eval z).toNat ≤ C * (B + 1))
    (hlower : ∀ᶠ B : ℕ in atTop,
      c * (B : ℝ) ^ 2 ≤ ∑ z ∈ R B, patternWeight ψ z) :
    ∀ᶠ B : ℕ in atTop, ∃ z ∈ R B, primePatternAvoidingLines ψ Q I θ z := by
  classical
  let k := 12 * Q.card + 144 + I.card
  have ho := (primePowerError_isLittleO C hC).add (linearError_isLittleO k C hC)
  have he := ho.bound (by positivity : 0 < c / 2)
  filter_upwards [hlower, he, eventually_ge_atTop (1 : ℕ)] with B hlo herr hB
  by_contra! hbad
  have hX : 1 ≤ C * (B + 1) :=
    Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))
  have hm := region_mass_le_extraction_error_of_no_good B (C * (B + 1))
    ψ Q I θ (R B) (hR B) hX hψ hparts hθ (hbound B) hbad
  have heq :
      ((12 * (((Nat.sqrt (C * (B + 1)) + 1) * (Nat.log 2 (C * (B + 1)) + 1)) *
        (2 * B + 1)) + (12 * Q.card + 144 + I.card) * (2 * B + 1) : ℕ) : ℝ) *
        (Real.log ((C * (B + 1) : ℕ) : ℝ)) ^ 12 =
      primePowerError B (C * (B + 1)) + linearError k B (C * (B + 1)) := by
    unfold primePowerError linearError k
    push_cast
    ring
  rw [heq] at hm
  have he0 : 0 ≤ primePowerError B (C * (B + 1)) + linearError k B (C * (B + 1)) :=
    add_nonneg (primePowerError_nonneg _ _) (linearError_nonneg _ _ _)
  have he' : primePowerError B (C * (B + 1)) + linearError k B (C * (B + 1)) ≤
      c / 2 * (B : ℝ) ^ 2 := by
    simpa only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg he0,
      abs_of_nonneg (sq_nonneg (B : ℝ))] using herr
  have hb : 0 < (B : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hB)
  have hp : 0 < c * (B : ℝ) ^ 2 := mul_pos hc (sq_pos_of_pos hb)
  linarith

theorem primePattern_mono_values (ψ : Fin 12 → IntegerAffine)
    (Q Q' : Finset ℤ) (hQ : Q ⊆ Q') (z : ℤ × ℤ)
    (hz : primePattern ψ Q' z) : primePattern ψ Q z := by
  exact ⟨fun i => ⟨(hz.1 i).1, (hz.1 i).2.1,
    fun hi => (hz.1 i).2.2 (hQ hi)⟩, hz.2⟩

/-- The finite-exclusion argument gives infinitely many actual integer pairs.
It works in arbitrary finite regions contained in the square, including sectors. -/
theorem primePatternAvoidingLines_infinite_of_quadratic_lower
    {ι : Type*} [DecidableEq ι]
    (ψ : Fin 12 → IntegerAffine) (Q : Finset ℤ)
    (I : Finset ι) (θ : ι → IntegerAffine)
    (R : ℕ → Finset (ℤ × ℤ)) (C : ℕ) (c : ℝ)
    (hR : ∀ B, R B ⊆ box B) (hC : 1 ≤ C) (hc : 0 < c)
    (hψ : ∀ i, (ψ i).a ≠ 0 ∨ (ψ i).b ≠ 0)
    (hparts : ∀ i j, i ≠ j → (ψ i).a ≠ (ψ j).a ∨ (ψ i).b ≠ (ψ j).b)
    (hθ : ∀ i ∈ I, (θ i).a ≠ 0 ∨ (θ i).b ≠ 0)
    (hbound : ∀ B, ∀ z ∈ box B, ∀ i, ((ψ i).eval z).toNat ≤ C * (B + 1))
    (hlower : ∀ᶠ B : ℕ in atTop,
      c * (B : ℝ) ^ 2 ≤ ∑ z ∈ R B, patternWeight ψ z) :
    {z : ℤ × ℤ | (∃ B, z ∈ R B) ∧ primePatternAvoidingLines ψ Q I θ z}.Infinite := by
  classical
  intro hfinite
  let F := hfinite.toFinset
  let Q' := Q ∪ F.image (fun z => (ψ 0).eval z)
  have he := eventually_primePatternAvoidingLines_of_quadratic_lower
    ψ Q' I θ R C c hR hC hc hψ hparts hθ hbound hlower
  obtain ⟨B, z, hzR, hzGood⟩ := he.exists
  have hzOld : primePatternAvoidingLines ψ Q I θ z :=
    ⟨primePattern_mono_values ψ Q Q' Finset.subset_union_left z hzGood.1, hzGood.2⟩
  have hzF : z ∈ F := hfinite.mem_toFinset.mpr ⟨⟨B, hzR⟩, hzOld⟩
  exact (hzGood.1.1 0).2.2 (Finset.mem_union_right Q
    (Finset.mem_image.mpr ⟨z, hzF, rfl⟩))

/-- The endpoint with no additional affine-line exclusions. -/
theorem primePattern_infinite_of_quadratic_lower
    (ψ : Fin 12 → IntegerAffine) (Q : Finset ℤ)
    (R : ℕ → Finset (ℤ × ℤ)) (C : ℕ) (c : ℝ)
    (hR : ∀ B, R B ⊆ box B) (hC : 1 ≤ C) (hc : 0 < c)
    (hψ : ∀ i, (ψ i).a ≠ 0 ∨ (ψ i).b ≠ 0)
    (hparts : ∀ i j, i ≠ j → (ψ i).a ≠ (ψ j).a ∨ (ψ i).b ≠ (ψ j).b)
    (hbound : ∀ B, ∀ z ∈ box B, ∀ i, ((ψ i).eval z).toNat ≤ C * (B + 1))
    (hlower : ∀ᶠ B : ℕ in atTop,
      c * (B : ℝ) ^ 2 ≤ ∑ z ∈ R B, patternWeight ψ z) :
    {z : ℤ × ℤ | (∃ B, z ∈ R B) ∧ primePattern ψ Q z}.Infinite := by
  simpa [primePatternAvoidingLines] using
      primePatternAvoidingLines_infinite_of_quadratic_lower ψ Q
        (∅ : Finset Unit) (fun _ => ⟨1, 0, 0⟩) R C c hR hC hc hψ hparts
        (by simp) hbound hlower

/-- Composing the proved errors with a fixed positive box dilation preserves o(T²). -/
theorem extractionError_scaled_isLittleO (k C K : ℕ) (hC : 1 ≤ C) (hK : 1 ≤ K) :
    (fun T : ℕ => primePowerError (K * T) (C * (K * T + 1)) +
      linearError k (K * T) (C * (K * T + 1))) =o[atTop]
        (fun T : ℕ => (T : ℝ) ^ 2) := by
  have ht : Tendsto (fun T : ℕ => K * T) atTop atTop :=
    tendsto_id.const_mul_atTop' (by omega)
  have hs : (fun T : ℕ => ((K * T : ℕ) : ℝ) ^ 2) =O[atTop]
      (fun T : ℕ => (T : ℝ) ^ 2) := by
    apply IsBigO.of_bound ((K : ℝ) ^ 2)
    filter_upwards [] with T
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
    simp only [Nat.cast_mul, mul_pow, le_refl]
  exact ((primePowerError_isLittleO C hC).add
    (linearError_isLittleO k C hC)).comp_tendsto ht |>.trans_isBigO hs

/-- The extraction theorem for a fixed dilation of the bounding square. -/
theorem eventually_primePatternAvoidingLines_of_scaled_quadratic_lower
    {ι : Type*} [DecidableEq ι]
    (ψ : Fin 12 → IntegerAffine) (Q : Finset ℤ)
    (I : Finset ι) (θ : ι → IntegerAffine)
    (R : ℕ → Finset (ℤ × ℤ)) (C K : ℕ) (c : ℝ)
    (hR : ∀ T, R T ⊆ box (K * T)) (hC : 1 ≤ C) (hK : 1 ≤ K) (hc : 0 < c)
    (hψ : ∀ i, (ψ i).a ≠ 0 ∨ (ψ i).b ≠ 0)
    (hparts : ∀ i j, i ≠ j → (ψ i).a ≠ (ψ j).a ∨ (ψ i).b ≠ (ψ j).b)
    (hθ : ∀ i ∈ I, (θ i).a ≠ 0 ∨ (θ i).b ≠ 0)
    (hbound : ∀ T, ∀ z ∈ box (K * T), ∀ i,
      ((ψ i).eval z).toNat ≤ C * (K * T + 1))
    (hlower : ∀ᶠ T : ℕ in atTop,
      c * (T : ℝ) ^ 2 ≤ ∑ z ∈ R T, patternWeight ψ z) :
    ∀ᶠ T : ℕ in atTop, ∃ z ∈ R T, primePatternAvoidingLines ψ Q I θ z := by
  classical
  let k := 12 * Q.card + 144 + I.card
  have he := (extractionError_scaled_isLittleO k C K hC hK).bound
    (by positivity : 0 < c / 2)
  filter_upwards [hlower, he, eventually_ge_atTop (1 : ℕ)] with T hlo herr hT
  by_contra! hbad
  have hX : 1 ≤ C * (K * T + 1) :=
    Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))
  have hm := region_mass_le_extraction_error_of_no_good (K * T) (C * (K * T + 1))
    ψ Q I θ (R T) (hR T) hX hψ hparts hθ (hbound T) hbad
  have heq :
      ((12 * (((Nat.sqrt (C * (K * T + 1)) + 1) *
        (Nat.log 2 (C * (K * T + 1)) + 1)) * (2 * (K * T) + 1)) +
        (12 * Q.card + 144 + I.card) * (2 * (K * T) + 1) : ℕ) : ℝ) *
        (Real.log ((C * (K * T + 1) : ℕ) : ℝ)) ^ 12 =
      primePowerError (K * T) (C * (K * T + 1)) +
        linearError k (K * T) (C * (K * T + 1)) := by
    unfold primePowerError linearError k
    push_cast
    ring
  rw [heq] at hm
  have he0 : 0 ≤ primePowerError (K * T) (C * (K * T + 1)) +
      linearError k (K * T) (C * (K * T + 1)) :=
    add_nonneg (primePowerError_nonneg _ _) (linearError_nonneg _ _ _)
  have he' : primePowerError (K * T) (C * (K * T + 1)) +
      linearError k (K * T) (C * (K * T + 1)) ≤ c / 2 * (T : ℝ) ^ 2 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg he0,
      abs_of_nonneg (sq_nonneg (T : ℝ))] using herr
  have ht : 0 < (T : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hT)
  have hp : 0 < c * (T : ℝ) ^ 2 := mul_pos hc (sq_pos_of_pos ht)
  linarith

theorem primePatternAvoidingLines_infinite_of_scaled_quadratic_lower
    {ι : Type*} [DecidableEq ι]
    (ψ : Fin 12 → IntegerAffine) (Q : Finset ℤ)
    (I : Finset ι) (θ : ι → IntegerAffine)
    (R : ℕ → Finset (ℤ × ℤ)) (C K : ℕ) (c : ℝ)
    (hR : ∀ T, R T ⊆ box (K * T)) (hC : 1 ≤ C) (hK : 1 ≤ K) (hc : 0 < c)
    (hψ : ∀ i, (ψ i).a ≠ 0 ∨ (ψ i).b ≠ 0)
    (hparts : ∀ i j, i ≠ j → (ψ i).a ≠ (ψ j).a ∨ (ψ i).b ≠ (ψ j).b)
    (hθ : ∀ i ∈ I, (θ i).a ≠ 0 ∨ (θ i).b ≠ 0)
    (hbound : ∀ T, ∀ z ∈ box (K * T), ∀ i,
      ((ψ i).eval z).toNat ≤ C * (K * T + 1))
    (hlower : ∀ᶠ T : ℕ in atTop,
      c * (T : ℝ) ^ 2 ≤ ∑ z ∈ R T, patternWeight ψ z) :
    {z : ℤ × ℤ | (∃ T, z ∈ R T) ∧ primePatternAvoidingLines ψ Q I θ z}.Infinite := by
  classical
  intro hfinite
  let F := hfinite.toFinset
  let Q' := Q ∪ F.image (fun z => (ψ 0).eval z)
  have he := eventually_primePatternAvoidingLines_of_scaled_quadratic_lower
    ψ Q' I θ R C K c hR hC hK hc hψ hparts hθ hbound hlower
  obtain ⟨T, z, hzR, hzGood⟩ := he.exists
  have hzOld : primePatternAvoidingLines ψ Q I θ z :=
    ⟨primePattern_mono_values ψ Q Q' Finset.subset_union_left z hzGood.1, hzGood.2⟩
  have hzF : z ∈ F := hfinite.mem_toFinset.mpr ⟨⟨T, hzR⟩, hzOld⟩
  exact (hzGood.1.1 0).2.2 (Finset.mem_union_right Q
    (Finset.mem_image.mpr ⟨z, hzF, rfl⟩))

theorem primePattern_infinite_of_scaled_quadratic_lower
    (ψ : Fin 12 → IntegerAffine) (Q : Finset ℤ)
    (R : ℕ → Finset (ℤ × ℤ)) (C K : ℕ) (c : ℝ)
    (hR : ∀ T, R T ⊆ box (K * T)) (hC : 1 ≤ C) (hK : 1 ≤ K) (hc : 0 < c)
    (hψ : ∀ i, (ψ i).a ≠ 0 ∨ (ψ i).b ≠ 0)
    (hparts : ∀ i j, i ≠ j → (ψ i).a ≠ (ψ j).a ∨ (ψ i).b ≠ (ψ j).b)
    (hbound : ∀ T, ∀ z ∈ box (K * T), ∀ i,
      ((ψ i).eval z).toNat ≤ C * (K * T + 1))
    (hlower : ∀ᶠ T : ℕ in atTop,
      c * (T : ℝ) ^ 2 ≤ ∑ z ∈ R T, patternWeight ψ z) :
    {z : ℤ × ℤ | (∃ T, z ∈ R T) ∧ primePattern ψ Q z}.Infinite := by
  simpa [primePatternAvoidingLines] using
    primePatternAvoidingLines_infinite_of_scaled_quadratic_lower ψ Q
      (∅ : Finset Unit) (fun _ => ⟨1, 0, 0⟩) R C K c hR hC hK hc hψ hparts
      (by simp) hbound hlower

end RankCertificates.AnalyticExtraction
