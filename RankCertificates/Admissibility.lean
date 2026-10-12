module

public import Mathlib.Tactic
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

namespace RankCertificates.PrimePatterns

/-- Fewer affine lines than the field cardinality cannot cover its affine plane.
The hypothesis also allows a constant nonzero form. -/
theorem exists_pair_avoiding_affine {K : Type*} [Field K] [Fintype K]
    {n : ℕ} (a b c : Fin n → K)
    (h : ∀ i, a i ≠ 0 ∨ b i ≠ 0 ∨ c i ≠ 0)
    (hn : n < Fintype.card K) :
    ∃ x y : K, ∀ i, a i * x + b i * y + c i ≠ 0 := by
  classical
  let bad (i : Fin n) : Finset (K × K) :=
    Finset.univ.filter (fun z => a i * z.1 + b i * z.2 + c i = 0)
  have hbad (i : Fin n) : (bad i).card ≤ Fintype.card K := by
    by_cases ha : a i = 0
    · by_cases hb : b i = 0
      · have hc : c i ≠ 0 := by simpa [ha, hb] using h i
        have he : bad i = ∅ := by ext z; simp [bad, ha, hb, hc]
        simp [he]
      · have hinj : Set.InjOn Prod.fst (bad i : Set (K × K)) := by
          intro z hz w hw he
          have hz' : a i * z.1 + b i * z.2 + c i = 0 := (Finset.mem_filter.mp hz).2
          have hw' : a i * w.1 + b i * w.2 + c i = 0 := (Finset.mem_filter.mp hw).2
          simp only [ha, zero_mul, zero_add] at hz' hw'
          apply Prod.ext he
          apply mul_left_cancel₀ hb
          linear_combination hz' - hw'
        simpa using Finset.card_le_card_of_injOn Prod.fst
          (show Set.MapsTo (Prod.fst : K × K → K) (↑(bad i)) (↑(Finset.univ : Finset K)) from fun _ _ => Finset.mem_univ _)
          hinj
    · have hinj : Set.InjOn Prod.snd (bad i : Set (K × K)) := by
        intro z hz w hw he
        have hz' : a i * z.1 + b i * z.2 + c i = 0 := (Finset.mem_filter.mp hz).2
        have hw' : a i * w.1 + b i * w.2 + c i = 0 := (Finset.mem_filter.mp hw).2
        apply Prod.ext
        · apply mul_left_cancel₀ ha
          simp only [he] at hz'
          linear_combination hz' - hw'
        · exact he
      simpa using Finset.card_le_card_of_injOn Prod.snd
        (show Set.MapsTo (Prod.snd : K × K → K) (↑(bad i)) (↑(Finset.univ : Finset K)) from fun _ _ => Finset.mem_univ _)
        hinj
  let allBad : Finset (K × K) := Finset.univ.biUnion bad
  have hbound : allBad.card ≤ n * Fintype.card K := by
    calc
      allBad.card ≤ ∑ i : Fin n, (bad i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin n, Fintype.card K := Finset.sum_le_sum (fun i _ => hbad i)
      _ = n * Fintype.card K := by simp
  have hlt : allBad.card < (Finset.univ : Finset (K × K)).card := by
    have hpos : 0 < Fintype.card K := Fintype.card_pos
    simpa using lt_of_le_of_lt hbound (Nat.mul_lt_mul_of_pos_right hn hpos)
  obtain ⟨z, _, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨z.1, z.2, ?_⟩
  intro i hi
  apply hz
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩

/-- Integer affine forms of content one admit simultaneous unit values modulo
any prime larger than the number of forms. -/
theorem exists_pair_avoiding_integer {n : ℕ} (a b c : Fin n → ℤ)
    (h : ∀ i, ∃ u v w : ℤ, a i * u + b i * v + c i * w = 1)
    (p : ℕ) (hp : p.Prime) (hn : n < p) :
    ∃ x y : ℤ, ∀ i, (a i * x + b i * y + c i) % (p : ℤ) ≠ 0 := by
  let : Fact p.Prime := ⟨hp⟩
  have hcoeff (i : Fin n) : (a i : ZMod p) ≠ 0 ∨
      (b i : ZMod p) ≠ 0 ∨ (c i : ZMod p) ≠ 0 := by
    by_contra! hz
    obtain ⟨u, v, w, hbez⟩ := h i
    have hcast : (a i : ZMod p) * (u : ZMod p) +
        (b i : ZMod p) * (v : ZMod p) + (c i : ZMod p) * (w : ZMod p) = 1 := by
      simpa only [Int.cast_add, Int.cast_mul, Int.cast_one] using
        congrArg (fun z : ℤ => (z : ZMod p)) hbez
    simp [hz.1, hz.2.1, hz.2.2] at hcast
  obtain ⟨x, y, hxy⟩ := exists_pair_avoiding_affine
    (fun i => (a i : ZMod p)) (fun i => (b i : ZMod p)) (fun i => (c i : ZMod p))
    hcoeff (by simpa using hn)
  refine ⟨(x.val : ℤ), (y.val : ℤ), ?_⟩
  intro i hz
  have hz' : ((a i * (x.val : ℤ) + b i * (y.val : ℤ) + c i : ℤ) : ZMod p) = 0 := by
    rw [← ZMod.intCast_mod _ p, hz]
    simp
  apply hxy i
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val] using hz'

end RankCertificates.PrimePatterns
