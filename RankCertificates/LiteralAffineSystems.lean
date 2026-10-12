module

public import RankCertificates.ExtractionBounds
public import RankCertificates.PrimePatterns

@[expose] public section

namespace RankCertificates.AnalyticExtraction

open PrimePatterns

/-- The literal manuscript form, represented in the extraction API. -/
def fromAffine (f : AffineForm) : IntegerAffine := ⟨f.a, f.b, f.c⟩

@[simp] theorem fromAffine_eval (f : AffineForm) (z : ℤ × ℤ) :
    (fromAffine f).eval z = f.eval z.1 z.2 := rfl

def system5 : Fin 12 → IntegerAffine := fromAffine ∘ Rank5.outputs
def system6 : Fin 12 → IntegerAffine := fromAffine ∘ Rank6.outputs
def system7 : Fin 12 → IntegerAffine := fromAffine ∘ Rank7.outputs

def IntegerAffine.coefficientBound (ψ : IntegerAffine) : ℕ :=
  ψ.a.natAbs + ψ.b.natAbs + ψ.c.natAbs + 1

theorem natAbs_coordinate_le {B : ℕ} {x : ℤ}
    (hx : x ∈ Finset.Icc (-(B : ℤ)) B) : x.natAbs ≤ B := by
  have h := abs_le.mpr (Finset.mem_Icc.mp hx)
  rw [← Int.natCast_natAbs] at h
  exact_mod_cast h

/-- A fixed affine system has a linear output cap on every square. -/
theorem IntegerAffine.eval_toNat_le {B : ℕ} {z : ℤ × ℤ}
    (ψ : IntegerAffine) (hz : z ∈ box B) :
    (ψ.eval z).toNat ≤ ψ.coefficientBound * (B + 1) := by
  obtain ⟨hx, hy⟩ := Finset.mem_product.mp hz
  have hx' := natAbs_coordinate_le hx
  have hy' := natAbs_coordinate_le hy
  have h₁ := Int.natAbs_add_le (ψ.a * z.1 + ψ.b * z.2) ψ.c
  have h₂ := Int.natAbs_add_le (ψ.a * z.1) (ψ.b * z.2)
  simp only [Int.natAbs_mul] at h₂
  have hnorm : (ψ.eval z).natAbs ≤
      (ψ.a.natAbs + ψ.b.natAbs) * B + ψ.c.natAbs := by
    dsimp [IntegerAffine.eval]
    calc
      _ ≤ (ψ.a * z.1 + ψ.b * z.2).natAbs + ψ.c.natAbs := h₁
      _ ≤ ψ.a.natAbs * z.1.natAbs + ψ.b.natAbs * z.2.natAbs + ψ.c.natAbs := by omega
      _ ≤ ψ.a.natAbs * B + ψ.b.natAbs * B + ψ.c.natAbs := by gcongr
      _ = _ := by ring
  apply Int.toNat_le.mpr
  exact Int.le_natAbs.trans (by
    exact_mod_cast hnorm.trans (by
      dsimp [coefficientBound]
      rw [Nat.mul_add, Nat.mul_one]
      exact Nat.add_le_add (Nat.mul_le_mul_right B (by omega)) (by omega)))

theorem system5_nonconstant (i : Fin 12) :
    (system5 i).a ≠ 0 ∨ (system5 i).b ≠ 0 := by
  fin_cases i <;> norm_num [system5, fromAffine, Rank5.outputs]

theorem system6_nonconstant (i : Fin 12) :
    (system6 i).a ≠ 0 ∨ (system6 i).b ≠ 0 := by
  fin_cases i <;> norm_num [system6, fromAffine, Rank6.outputs]

theorem system7_nonconstant (i : Fin 12) :
    (system7 i).a ≠ 0 ∨ (system7 i).b ≠ 0 := by
  fin_cases i <;> norm_num [system7, fromAffine, Rank7.outputs]

theorem different_parts_of_nonparallel (fs : Fin 12 → AffineForm)
    (h : ∀ i j, i ≠ j → (fs i).a * (fs j).b - (fs i).b * (fs j).a ≠ 0)
    {i j : Fin 12} (hij : i ≠ j) :
    (fromAffine (fs i)).a ≠ (fromAffine (fs j)).a ∨
      (fromAffine (fs i)).b ≠ (fromAffine (fs j)).b := by
  by_contra! heq
  apply h i j hij
  simp only [fromAffine] at heq
  rw [heq.1, heq.2]
  ring

/-- A common cap for all three systems, independent of the box size. -/
def literalCap : ℕ := 3000000000000000

theorem system5_coefficientBound (i : Fin 12) :
    (system5 i).coefficientBound ≤ literalCap := by
  fin_cases i <;> norm_num [system5, fromAffine, IntegerAffine.coefficientBound,
    Rank5.outputs, literalCap]

theorem system6_coefficientBound (i : Fin 12) :
    (system6 i).coefficientBound ≤ literalCap := by
  fin_cases i <;> norm_num [system6, fromAffine, IntegerAffine.coefficientBound,
    Rank6.outputs, literalCap]

theorem system7_coefficientBound (i : Fin 12) :
    (system7 i).coefficientBound ≤ literalCap := by
  fin_cases i <;> norm_num [system7, fromAffine, IntegerAffine.coefficientBound,
    Rank7.outputs, literalCap]

theorem system5_output_bound {B : ℕ} {z : ℤ × ℤ} (hz : z ∈ box B) (i : Fin 12) :
    ((system5 i).eval z).toNat ≤ literalCap * (B + 1) :=
  ((system5 i).eval_toNat_le hz).trans
    (Nat.mul_le_mul_right _ (system5_coefficientBound i))

theorem system6_output_bound {B : ℕ} {z : ℤ × ℤ} (hz : z ∈ box B) (i : Fin 12) :
    ((system6 i).eval z).toNat ≤ literalCap * (B + 1) :=
  ((system6 i).eval_toNat_le hz).trans
    (Nat.mul_le_mul_right _ (system6_coefficientBound i))

theorem system7_output_bound {B : ℕ} {z : ℤ × ℤ} (hz : z ∈ box B) (i : Fin 12) :
    ((system7 i).eval z).toNat ≤ literalCap * (B + 1) :=
  ((system7 i).eval_toNat_le hz).trans
    (Nat.mul_le_mul_right _ (system7_coefficientBound i))

theorem system5_different_parts (i j : Fin 12) (hij : i ≠ j) :
    (system5 i).a ≠ (system5 j).a ∨ (system5 i).b ≠ (system5 j).b :=
  different_parts_of_nonparallel _ Rank5.nonparallel_outputs hij

theorem system6_different_parts (i j : Fin 12) (hij : i ≠ j) :
    (system6 i).a ≠ (system6 j).a ∨ (system6 i).b ≠ (system6 j).b :=
  different_parts_of_nonparallel _ Rank6.nonparallel_outputs hij

theorem system7_different_parts (i j : Fin 12) (hij : i ≠ j) :
    (system7 i).a ≠ (system7 j).a ∨ (system7 i).b ≠ (system7 j).b :=
  different_parts_of_nonparallel _ Rank7.nonparallel_outputs hij

/-- Rectangles in the positive cone. Each has exactly (T+1)^2 lattice points. -/
def positiveSector5 (T : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (20 * (T : ℤ)) (21 * T) ×ˢ Finset.Icc (20 * (T : ℤ)) (21 * T)

def positiveSector6 (T : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (60 * (T : ℤ)) (61 * T) ×ˢ Finset.Icc (T : ℤ) (2 * T)

def positiveSector7 (T : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (8000 * (T : ℤ)) (8001 * T) ×ˢ Finset.Icc (T : ℤ) (2 * T)

theorem positiveSector5_card (T : ℕ) : (positiveSector5 T).card = (T + 1) ^ 2 := by
  simp only [positiveSector5, Finset.card_product, Int.card_Icc]
  have h : (21 * (T : ℤ) + 1 - 20 * T).toNat = T + 1 := by omega
  rw [h]
  ring

theorem positiveSector6_card (T : ℕ) : (positiveSector6 T).card = (T + 1) ^ 2 := by
  simp only [positiveSector6, Finset.card_product, Int.card_Icc]
  have h₁ : (61 * (T : ℤ) + 1 - 60 * T).toNat = T + 1 := by omega
  have h₂ : (2 * (T : ℤ) + 1 - T).toNat = T + 1 := by omega
  rw [h₁, h₂]
  ring

theorem positiveSector7_card (T : ℕ) : (positiveSector7 T).card = (T + 1) ^ 2 := by
  simp only [positiveSector7, Finset.card_product, Int.card_Icc]
  have h₁ : (8001 * (T : ℤ) + 1 - 8000 * T).toNat = T + 1 := by omega
  have h₂ : (2 * (T : ℤ) + 1 - T).toNat = T + 1 := by omega
  rw [h₁, h₂]
  ring

theorem positiveSector5_subset_box (T : ℕ) : positiveSector5 T ⊆ box (21 * T) := by
  intro z hz
  simp only [positiveSector5, Finset.mem_product, Finset.mem_Icc] at hz
  simp only [box, Finset.mem_product, Finset.mem_Icc, Nat.cast_mul, Nat.cast_ofNat]
  omega

theorem positiveSector6_subset_box (T : ℕ) : positiveSector6 T ⊆ box (61 * T) := by
  intro z hz
  simp only [positiveSector6, Finset.mem_product, Finset.mem_Icc] at hz
  simp only [box, Finset.mem_product, Finset.mem_Icc, Nat.cast_mul, Nat.cast_ofNat]
  omega

theorem positiveSector7_subset_box (T : ℕ) : positiveSector7 T ⊆ box (8001 * T) := by
  intro z hz
  simp only [positiveSector7, Finset.mem_product, Finset.mem_Icc] at hz
  simp only [box, Finset.mem_product, Finset.mem_Icc, Nat.cast_mul, Nat.cast_ofNat]
  omega

/-- All outputs grow at least linearly throughout these rectangles. -/
theorem positiveSector5_output_lower {T : ℕ} (hT : 1 ≤ T) {z : ℤ × ℤ}
    (hz : z ∈ positiveSector5 T) (i : Fin 12) : (T : ℤ) ≤ (system5 i).eval z := by
  simp only [positiveSector5, Finset.mem_product, Finset.mem_Icc] at hz
  have hT' : (1 : ℤ) ≤ T := by exact_mod_cast hT
  fin_cases i <;> norm_num [system5, fromAffine, Rank5.outputs, IntegerAffine.eval] <;> omega

theorem positiveSector6_output_lower {T : ℕ} (hT : 1 ≤ T) {z : ℤ × ℤ}
    (hz : z ∈ positiveSector6 T) (i : Fin 12) : (T : ℤ) ≤ (system6 i).eval z := by
  simp only [positiveSector6, Finset.mem_product, Finset.mem_Icc] at hz
  have hT' : (1 : ℤ) ≤ T := by exact_mod_cast hT
  fin_cases i <;> norm_num [system6, fromAffine, Rank6.outputs, IntegerAffine.eval] <;> omega

theorem positiveSector7_output_lower {T : ℕ} (hT : 1 ≤ T) {z : ℤ × ℤ}
    (hz : z ∈ positiveSector7 T) (i : Fin 12) : (T : ℤ) ≤ (system7 i).eval z := by
  simp only [positiveSector7, Finset.mem_product, Finset.mem_Icc] at hz
  have hT' : (1 : ℤ) ≤ T := by exact_mod_cast hT
  fin_cases i <;> norm_num [system7, fromAffine, Rank7.outputs, IntegerAffine.eval] <;> omega

end RankCertificates.AnalyticExtraction
