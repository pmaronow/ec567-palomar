module

public import RankCertificates.PrimePatterns
public import Mathlib.LinearAlgebra.Span.Basic

/-!
The Cauchy–Schwarz complexity of the three twelve-form prime systems is
exactly ten. The partition condition uses the rational spans of the linear
parts of the affine forms, as in the finite-complexity prime theorem.
This certifies a hypothesis of that theorem; it proves no prime infinitude.
-/

@[expose] public section

namespace RankCertificates.PrimeComplexity

open PrimePatterns

def gradient (f : AffineForm) : ℚ × ℚ := (f.a, f.b)

def determinant (v w : ℚ × ℚ) : ℚ := v.1 * w.2 - v.2 * w.1

/-- A partition into `s+1` classes of the other linear parts, each of whose
rational spans avoids the distinguished linear part. Empty classes are
allowed. This is the usual Cauchy–Schwarz partition condition. -/
def PartitionAt (v : Fin 12 → ℚ × ℚ) (i : Fin 12) (s : ℕ) : Prop :=
  ∃ color : {j : Fin 12 // j ≠ i} → Fin (s + 1),
    ∀ c, v i ∉ Submodule.span ℚ
      {w | ∃ j : {j : Fin 12 // j ≠ i}, color j = c ∧ v j.val = w}

/-- Complexity at most `s` means that the partition condition holds at
every distinguished form. -/
def ComplexityAtMost (v : Fin 12 → ℚ × ℚ) (s : ℕ) : Prop :=
  ∀ i, PartitionAt v i s

theorem mem_span_pair_of_determinant_ne_zero (v w z : ℚ × ℚ)
    (h : determinant v w ≠ 0) : z ∈ Submodule.span ℚ ({v, w} : Set (ℚ × ℚ)) := by
  apply Submodule.mem_span_pair.mpr
  refine ⟨(z.1 * w.2 - z.2 * w.1) / determinant v w,
    (v.1 * z.2 - v.2 * z.1) / determinant v w, ?_⟩
  apply Prod.ext
  all_goals
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]
    field_simp
    simp only [determinant] at h ⊢
    ring

theorem not_mem_span_singleton_of_determinant_ne_zero (v w : ℚ × ℚ)
    (h : determinant v w ≠ 0) : v ∉ Submodule.span ℚ ({w} : Set (ℚ × ℚ)) := by
  intro hv
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hv
  apply h
  rw [← ha]
  simp [determinant, mul_comm, mul_left_comm]

theorem partition_at_forces_injective {v : Fin 12 → ℚ × ℚ} {i : Fin 12} {s : ℕ}
    (hdet : ∀ j k, j ≠ k → determinant (v j) (v k) ≠ 0)
    (color : {j : Fin 12 // j ≠ i} → Fin (s + 1))
    (hc : ∀ c, v i ∉ Submodule.span ℚ
      {w | ∃ j : {j : Fin 12 // j ≠ i}, color j = c ∧ v j.val = w}) :
    Function.Injective color := by
  intro j k he
  by_contra hne
  have hjk : j.val ≠ k.val := fun hh => hne (Subtype.ext hh)
  apply hc (color j)
  apply Submodule.span_mono (s := ({v j.val, v k.val} : Set (ℚ × ℚ))) _
    (mem_span_pair_of_determinant_ne_zero _ _ _ (hdet _ _ hjk))
  intro w hw
  rcases Set.mem_insert_iff.mp hw with hw | hw
  · exact ⟨j, rfl, hw.symm⟩
  · exact ⟨k, he.symm, (Set.mem_singleton_iff.mp hw).symm⟩

theorem complexity_lower_bound {v : Fin 12 → ℚ × ℚ} {s : ℕ}
    (hdet : ∀ j k, j ≠ k → determinant (v j) (v k) ≠ 0)
    (h : ComplexityAtMost v s) : 10 ≤ s := by
  classical
  obtain ⟨color, hc⟩ := h 0
  have hi := Fintype.card_le_of_injective color (partition_at_forces_injective hdet color hc)
  have hcard : Fintype.card {j : Fin 12 // j ≠ (0 : Fin 12)} = 11 := by
    rw [Fintype.card_subtype_compl]
    simp
  rw [hcard, Fintype.card_fin] at hi
  omega

/-- The eleven indices other than `i`, in their original order. -/
def otherIndex (i : Fin 12) (j : {j : Fin 12 // j ≠ i}) : Fin 11 :=
  ⟨j.val.val - if i.val < j.val.val then 1 else 0, by
    have hj := j.val.isLt
    have hij : j.val.val ≠ i.val := fun h => j.property (Fin.ext h)
    split_ifs <;> omega⟩

theorem otherIndex_injective (i : Fin 12) : Function.Injective (otherIndex i) := by
  intro j k he
  have he' := congrArg Fin.val he
  simp only [otherIndex] at he'
  have hji : j.val.val ≠ i.val := fun h => j.property (Fin.ext h)
  have hki : k.val.val ≠ i.val := fun h => k.property (Fin.ext h)
  apply Subtype.ext
  apply Fin.ext
  split_ifs at he' <;> omega

theorem complexity_upper_bound {v : Fin 12 → ℚ × ℚ}
    (hdet : ∀ j k, j ≠ k → determinant (v j) (v k) ≠ 0) :
    ComplexityAtMost v 10 := by
  intro i
  refine ⟨otherIndex i, ?_⟩
  intro c hmem
  let S : Set (ℚ × ℚ) :=
    {w | ∃ j : {j : Fin 12 // j ≠ i}, otherIndex i j = c ∧ v j.val = w}
  by_cases hS : S.Nonempty
  · obtain ⟨w, j, hj, rfl⟩ := hS
    have hsub : S ⊆ {v j.val} := by
      rintro z ⟨k, hk, rfl⟩
      have he : k = j := otherIndex_injective i (hk.trans hj.symm)
      simp [he]
    exact not_mem_span_singleton_of_determinant_ne_zero _ _ (hdet _ _ j.property.symm)
      (Submodule.span_mono hsub hmem)
  · have hS0 : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    have hzero : v i = 0 := by
      change v i ∈ Submodule.span ℚ S at hmem
      rw [hS0, Submodule.span_empty] at hmem
      exact hmem
    let j : Fin 12 := if i = 0 then 1 else 0
    have hij : i ≠ j := by
      dsimp [j]
      split_ifs with hi
      · subst i; decide
      · exact hi
    have hd := hdet i j hij
    rw [hzero] at hd
    exact hd (by simp [determinant])

theorem exact_complexity_of_nonparallel (fs : Fin 12 → AffineForm)
    (h : ∀ i j, i ≠ j → (fs i).a * (fs j).b - (fs i).b * (fs j).a ≠ 0) :
    ComplexityAtMost (gradient ∘ fs) 10 ∧
      ∀ s, ComplexityAtMost (gradient ∘ fs) s → 10 ≤ s := by
  have hd (i j : Fin 12) (hij : i ≠ j) :
      determinant ((gradient ∘ fs) i) ((gradient ∘ fs) j) ≠ 0 := by
    change ((fs i).a : ℚ) * (fs j).b - ((fs i).b : ℚ) * (fs j).a ≠ 0
    exact_mod_cast h i j hij
  exact ⟨complexity_upper_bound hd, fun _ hs => complexity_lower_bound hd hs⟩

theorem rank5_exact_complexity : ComplexityAtMost (gradient ∘ Rank5.outputs) 10 ∧
    ∀ s, ComplexityAtMost (gradient ∘ Rank5.outputs) s → 10 ≤ s :=
  exact_complexity_of_nonparallel _ Rank5.nonparallel_outputs

theorem rank6_exact_complexity : ComplexityAtMost (gradient ∘ Rank6.outputs) 10 ∧
    ∀ s, ComplexityAtMost (gradient ∘ Rank6.outputs) s → 10 ≤ s :=
  exact_complexity_of_nonparallel _ Rank6.nonparallel_outputs

theorem rank7_exact_complexity : ComplexityAtMost (gradient ∘ Rank7.outputs) 10 ∧
    ∀ s, ComplexityAtMost (gradient ∘ Rank7.outputs) s → 10 ≤ s :=
  exact_complexity_of_nonparallel _ Rank7.nonparallel_outputs

end RankCertificates.PrimeComplexity
