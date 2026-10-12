module

public import RankCertificates.LiteralAffineSystems
public import Mathlib.Data.Nat.ChineseRemainder
public import Mathlib.Data.Nat.GCD.BigOperators

@[expose] public section

namespace RankCertificates.AnalyticExtraction.AdmissibleW

open scoped BigOperators Function
open Finset

noncomputable section

/-- The squarefree W modulus associated to an arbitrary finite prime set. -/
def modulus (S : Finset ℕ) : ℕ := ∏ p ∈ S, p

/-- Actual local admissibility of all twelve integer affine outputs. -/
def LocalAvoidance (ψ : Fin 12 → IntegerAffine) (p : ℕ) : Prop :=
  ∃ z : ℤ × ℤ, ∀ i, (ψ i).eval z % (p : ℤ) ≠ 0

/-- All twelve actual outputs avoid every prime in the chosen finite set. -/
def AdmissibleClass (ψ : Fin 12 → IntegerAffine) (S : Finset ℕ) (z : ℤ × ℤ) : Prop :=
  ∀ p ∈ S, ∀ i, ((ψ i).eval z : ZMod p) ≠ 0

def wShift (W : ℕ) (z t : ℤ × ℤ) : ℤ × ℤ :=
  (z.1 + (W : ℤ) * t.1, z.2 + (W : ℤ) * t.2)

/-- The literal affine system after choosing a W-admissible offset. -/
def wTrickedForm (W : ℕ) (z : ℤ × ℤ) (ψ : IntegerAffine) : IntegerAffine :=
  ⟨(W : ℤ) * ψ.a, (W : ℤ) * ψ.b, ψ.eval z⟩

theorem wTrickedForm_eval (W : ℕ) (z t : ℤ × ℤ) (ψ : IntegerAffine) :
    (wTrickedForm W z ψ).eval t = ψ.eval (wShift W z t) := by
  simp only [wTrickedForm, wShift, IntegerAffine.eval]
  ring

theorem modulus_pos {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) : 0 < modulus S := by
  exact prod_pos fun p hp => (hS p hp).pos

theorem prime_dvd_modulus {S : Finset ℕ} {p : ℕ} (hp : p ∈ S) : p ∣ modulus S :=
  dvd_prod_of_mem (fun p : ℕ => p) hp

theorem eval_cast_wShift (ψ : IntegerAffine) (z t : ℤ × ℤ) {p W : ℕ}
    (hpW : p ∣ W) : (ψ.eval (wShift W z t) : ZMod p) = (ψ.eval z : ZMod p) := by
  have hW : (W : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff W p).mpr hpW
  simp [wShift, IntegerAffine.eval, hW]

theorem AdmissibleClass.wShift {ψ : Fin 12 → IntegerAffine} {S : Finset ℕ}
    {z : ℤ × ℤ} (hz : AdmissibleClass ψ S z) (t : ℤ × ℤ) :
    AdmissibleClass ψ S (wShift (modulus S) z t) := by
  intro p hp i
  rw [eval_cast_wShift _ _ _ (prime_dvd_modulus hp)]
  exact hz p hp i

theorem AdmissibleClass.coprime {ψ : Fin 12 → IntegerAffine} {S : Finset ℕ}
    {z : ℤ × ℤ} (hz : AdmissibleClass ψ S z) (hS : ∀ p ∈ S, p.Prime) (i : Fin 12) :
    ((ψ i).eval z).natAbs.Coprime (modulus S) := by
  apply Nat.coprime_prod_right_iff.mpr
  intro p hp
  apply Nat.Coprime.symm
  apply (hS p hp).coprime_iff_not_dvd.mpr
  intro hd
  apply hz p hp i
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (Int.natCast_dvd.mpr hd)

/-- Genuine finite CRT combination of actual integer local witnesses. Both
    nonnegative representatives lie strictly below W, including the empty-set case. -/
theorem exists_bounded_admissible_residue (ψ : Fin 12 → IntegerAffine) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hlocal : ∀ p ∈ S, LocalAvoidance ψ p) :
    ∃ X Y : ℕ, X < modulus S ∧ Y < modulus S ∧
      AdmissibleClass ψ S ((X : ℤ), (Y : ℤ)) := by
  classical
  let z : ℕ → ℤ × ℤ := fun p =>
    if hp : p ∈ S then Classical.choose (hlocal p hp) else (0, 0)
  have hz : ∀ p ∈ S, ∀ i, (ψ i).eval (z p) % (p : ℤ) ≠ 0 := by
    intro p hp i
    simpa only [z, dite_eq_left hp] using Classical.choose_spec (hlocal p hp) i
  let x : ℕ → ℕ := fun p => ((z p).1 : ZMod p).val
  let y : ℕ → ℕ := fun p => ((z p).2 : ZMod p).val
  have hnonzero : ∀ p ∈ S, p ≠ 0 := fun p hp => (hS p hp).ne_zero
  have hpair : Set.Pairwise (S : Set ℕ) (Nat.Coprime on (fun p : ℕ => p)) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (hS p hp) (hS q hq)).mpr hpq
  let X := Nat.chineseRemainderOfFinset x (fun p : ℕ => p) S hnonzero hpair
  let Y := Nat.chineseRemainderOfFinset y (fun p : ℕ => p) S hnonzero hpair
  refine ⟨X.val, Y.val, Nat.chineseRemainderOfFinset_lt_prod x (fun p : ℕ => p) hnonzero hpair,
    Nat.chineseRemainderOfFinset_lt_prod y (fun p : ℕ => p) hnonzero hpair, ?_⟩
  intro p hp i
  let : NeZero p := ⟨(hS p hp).ne_zero⟩
  have hX : (X.val : ZMod p) = ((z p).1 : ZMod p) := by
    calc
      _ = (x p : ZMod p) := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (X.property p hp)
      _ = _ := ZMod.natCast_zmod_val _
  have hY : (Y.val : ZMod p) = ((z p).2 : ZMod p) := by
    calc
      _ = (y p : ZMod p) := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Y.property p hp)
      _ = _ := ZMod.natCast_zmod_val _
  have heval : ((ψ i).eval ((X.val : ℤ), (Y.val : ℤ)) : ZMod p) =
      ((ψ i).eval (z p) : ZMod p) := by
    simp only [IntegerAffine.eval, Int.cast_add, Int.cast_mul, Int.cast_natCast, hX, hY]
  rw [heval]
  intro heq
  apply hz p hp i
  exact Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp heq)

/-- Every integer W-shift of this canonical residue has actual outputs coprime to W. -/
theorem exists_bounded_coprime_shift_class (ψ : Fin 12 → IntegerAffine) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hlocal : ∀ p ∈ S, LocalAvoidance ψ p) :
    ∃ X Y : ℕ, X < modulus S ∧ Y < modulus S ∧
      ∀ t : ℤ × ℤ, ∀ i,
        ((ψ i).eval (wShift (modulus S) ((X : ℤ), (Y : ℤ)) t)).natAbs.Coprime (modulus S) := by
  obtain ⟨X, Y, hX, hY, hclass⟩ := exists_bounded_admissible_residue ψ S hS hlocal
  exact ⟨X, Y, hX, hY, fun t i => (hclass.wShift t).coprime hS i⟩

theorem system5_localAvoidance (p : ℕ) (hp : p.Prime) : LocalAvoidance system5 p := by
  obtain ⟨x, y, h⟩ := PrimePatterns.Rank5.local_admissibility p hp
  exact ⟨(x, y), h⟩

theorem system6_localAvoidance (p : ℕ) (hp : p.Prime) : LocalAvoidance system6 p := by
  obtain ⟨x, y, h⟩ := PrimePatterns.Rank6.local_admissibility p hp
  exact ⟨(x, y), h⟩

theorem system7_localAvoidance (p : ℕ) (hp : p.Prime) : LocalAvoidance system7 p := by
  obtain ⟨x, y, h⟩ := PrimePatterns.Rank7.local_admissibility p hp
  exact ⟨(x, y), h⟩

theorem system5_bounded_admissible_residue (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∃ X Y : ℕ, X < modulus S ∧ Y < modulus S ∧
      AdmissibleClass system5 S ((X : ℤ), (Y : ℤ)) :=
  exists_bounded_admissible_residue system5 S hS (fun p hp => system5_localAvoidance p (hS p hp))

theorem system6_bounded_admissible_residue (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∃ X Y : ℕ, X < modulus S ∧ Y < modulus S ∧
      AdmissibleClass system6 S ((X : ℤ), (Y : ℤ)) :=
  exists_bounded_admissible_residue system6 S hS (fun p hp => system6_localAvoidance p (hS p hp))

theorem system7_bounded_admissible_residue (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∃ X Y : ℕ, X < modulus S ∧ Y < modulus S ∧
      AdmissibleClass system7 S ((X : ℤ), (Y : ℤ)) :=
  exists_bounded_admissible_residue system7 S hS (fun p hp => system7_localAvoidance p (hS p hp))

/-- W-shifting the canonical rank-five residue into the proved positive sector. -/
theorem system5_positive_admissible_offset (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∃ X Y : ℕ, X < modulus S ∧ Y < modulus S ∧
      let z := wShift (modulus S) ((X : ℤ), (Y : ℤ)) (20, 20)
      z ∈ positiveSector5 (modulus S) ∧ AdmissibleClass system5 S z ∧
      ∀ i, 0 < (system5 i).eval z ∧ ((system5 i).eval z).natAbs.Coprime (modulus S) := by
  obtain ⟨X, Y, hX, hY, hclass⟩ := system5_bounded_admissible_residue S hS
  refine ⟨X, Y, hX, hY, ?_⟩
  have hpos := modulus_pos hS
  have hsector : wShift (modulus S) ((X : ℤ), (Y : ℤ)) (20, 20) ∈ positiveSector5 (modulus S) := by
    simp only [wShift, positiveSector5, mem_product, mem_Icc]
    have hX' : (X : ℤ) < (modulus S : ℤ) := by exact_mod_cast hX
    have hY' : (Y : ℤ) < (modulus S : ℤ) := by exact_mod_cast hY
    constructor <;> constructor <;> omega
  have hc := hclass.wShift (20, 20)
  refine ⟨hsector, hc, fun i => ⟨?_, hc.coprime hS i⟩⟩
  exact lt_of_lt_of_le (by exact_mod_cast hpos) (positiveSector5_output_lower hpos hsector i)

/-- W-shifting the canonical rank-six residue into the proved positive sector. -/
theorem system6_positive_admissible_offset (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∃ X Y : ℕ, X < modulus S ∧ Y < modulus S ∧
      let z := wShift (modulus S) ((X : ℤ), (Y : ℤ)) (60, 1)
      z ∈ positiveSector6 (modulus S) ∧ AdmissibleClass system6 S z ∧
      ∀ i, 0 < (system6 i).eval z ∧ ((system6 i).eval z).natAbs.Coprime (modulus S) := by
  obtain ⟨X, Y, hX, hY, hclass⟩ := system6_bounded_admissible_residue S hS
  refine ⟨X, Y, hX, hY, ?_⟩
  have hpos := modulus_pos hS
  have hsector : wShift (modulus S) ((X : ℤ), (Y : ℤ)) (60, 1) ∈ positiveSector6 (modulus S) := by
    simp only [wShift, positiveSector6, mem_product, mem_Icc]
    have hX' : (X : ℤ) < (modulus S : ℤ) := by exact_mod_cast hX
    have hY' : (Y : ℤ) < (modulus S : ℤ) := by exact_mod_cast hY
    constructor <;> constructor <;> omega
  have hc := hclass.wShift (60, 1)
  refine ⟨hsector, hc, fun i => ⟨?_, hc.coprime hS i⟩⟩
  exact lt_of_lt_of_le (by exact_mod_cast hpos) (positiveSector6_output_lower hpos hsector i)

/-- W-shifting the canonical rank-seven residue into the proved positive sector. -/
theorem system7_positive_admissible_offset (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∃ X Y : ℕ, X < modulus S ∧ Y < modulus S ∧
      let z := wShift (modulus S) ((X : ℤ), (Y : ℤ)) (8000, 1)
      z ∈ positiveSector7 (modulus S) ∧ AdmissibleClass system7 S z ∧
      ∀ i, 0 < (system7 i).eval z ∧ ((system7 i).eval z).natAbs.Coprime (modulus S) := by
  obtain ⟨X, Y, hX, hY, hclass⟩ := system7_bounded_admissible_residue S hS
  refine ⟨X, Y, hX, hY, ?_⟩
  have hpos := modulus_pos hS
  have hsector : wShift (modulus S) ((X : ℤ), (Y : ℤ)) (8000, 1) ∈ positiveSector7 (modulus S) := by
    simp only [wShift, positiveSector7, mem_product, mem_Icc]
    have hX' : (X : ℤ) < (modulus S : ℤ) := by exact_mod_cast hX
    have hY' : (Y : ℤ) < (modulus S : ℤ) := by exact_mod_cast hY
    constructor <;> constructor <;> omega
  have hc := hclass.wShift (8000, 1)
  refine ⟨hsector, hc, fun i => ⟨?_, hc.coprime hS i⟩⟩
  exact lt_of_lt_of_le (by exact_mod_cast hpos) (positiveSector7_output_lower hpos hsector i)

end
end RankCertificates.AnalyticExtraction.AdmissibleW
