module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Card
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.Tactic

@[expose] public section

/-! Exact binary matrices. Bit `i` of an integer is coordinate `i`, with the
least significant bit coordinate zero. All arithmetic in a row equation is in
`ZMod 2`. The executable Boolean test is proved equal to that equation. -/

namespace RankCertificates.Binary

/-- Embed a Boolean as a scalar in the binary field. -/
def scalar (b : Bool) : ZMod 2 := if b then 1 else 0

/-- Coordinate vector represented by the low `width` bits of a natural number. -/
def vector (width code : ℕ) : Fin width → ZMod 2 := fun i => scalar (code.testBit i)

/-- Binary dot product, calculated from most significant coordinate downward. -/
def dot : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | n + 1, r, v => (r.testBit n && v.testBit n) ^^ dot n r v

@[simp] theorem scalar_xor (a b : Bool) : scalar (a ^^ b) = scalar a + scalar b := by
  cases a <;> cases b <;> decide

@[simp] theorem scalar_and (a b : Bool) : scalar (a && b) = scalar a * scalar b := by
  cases a <;> cases b <;> simp [scalar]

/-- The executable dot product is the usual dot product in the binary field. -/
theorem dot_eq_sum (width row code : ℕ) :
    scalar (dot width row code) = ∑ i : Fin width, vector width row i * vector width code i := by
  induction width with
  | zero => simp [dot, scalar]
  | succ n ih =>
    simp only [dot, scalar_xor, scalar_and, Fin.sum_univ_castSucc, vector, Fin.val_castSucc,
      Fin.val_last] at *
    rw [ih, add_comm]

/-- A binary matrix is represented by its list of integer row masks. -/
def Kernel (width : ℕ) (rows : List ℕ) (code : ℕ) : Prop :=
  ∀ row ∈ rows, ∑ i : Fin width, vector width row i * vector width code i = 0

/-- Executable test for all binary row equations. -/
def kernelTest (width : ℕ) (rows : List ℕ) (code : ℕ) : Bool :=
  rows.all (fun row => !(dot width row code))

@[simp] theorem scalar_eq_zero (b : Bool) : scalar b = 0 ↔ b = false := by
  cases b <;> norm_num [scalar]

theorem kernelTest_eq_true (width : ℕ) (rows : List ℕ) (code : ℕ) :
    kernelTest width rows code = true ↔ Kernel width rows code := by
  simp only [kernelTest, List.all_eq_true, Bool.not_eq_true', Kernel]
  simp_rw [← dot_eq_sum, scalar_eq_zero]

instance kernelDecidable (width : ℕ) (rows : List ℕ) : DecidablePred (Kernel width rows) :=
  fun code => decidable_of_iff (kernelTest width rows code = true)
    (kernelTest_eq_true width rows code)

/-- Exhaustive, bounded list of the solutions to the binary row equations. -/
def kernelCodes (width : ℕ) (rows : List ℕ) : List ℕ :=
  (List.range (2 ^ width)).filter (kernelTest width rows)

/-- A consecutive block of masks, for checking large finite kernels in small
independent computations. -/
def kernelBlock (width : ℕ) (rows : List ℕ) (start count : ℕ) : List ℕ :=
  (List.range' start count).filter (kernelTest width rows)

theorem kernelCodes_eq_block (width : ℕ) (rows : List ℕ) :
    kernelCodes width rows = kernelBlock width rows 0 (2 ^ width) := by
  simp [kernelCodes, kernelBlock, List.range_eq_range']

theorem kernelBlock_add (width : ℕ) (rows : List ℕ) (start m n : ℕ) :
    kernelBlock width rows start (m + n) =
      kernelBlock width rows start m ++ kernelBlock width rows (start + m) n := by
  simp only [kernelBlock, ← List.range'_append_1, List.filter_append]

theorem mem_kernelCodes {width code : ℕ} {rows : List ℕ} :
    code ∈ kernelCodes width rows ↔ code < 2 ^ width ∧ Kernel width rows code := by
  simp [kernelCodes, kernelTest_eq_true]

/-- All binary sums of a given list of generators. Each generator is either
omitted or included, so this is exactly the `F₂` span in mask representation. -/
def spanCodes : List ℕ → List ℕ
  | [] => [0]
  | g :: gs => spanCodes gs ++ (spanCodes gs).map (fun c => Nat.xor g c)

/-- Mask addition agrees coordinatewise with vector addition over `F₂`. -/
theorem vector_xor (width a b : ℕ) :
    vector width (Nat.xor a b) = vector width a + vector width b := by
  funext i
  simp [vector, Nat.testBit_xor]

/-- An explicit recursive definition of the span of vectors over the binary
field. The two choices at a generator are the two scalars of `F₂`. -/
def VectorSpan (width : ℕ) : List ℕ → (Fin width → ZMod 2) → Prop
  | [], v => v = 0
  | g :: gs, v => VectorSpan width gs v ∨
      ∃ w, VectorSpan width gs w ∧ v = vector width g + w

/-- Every mask produced by binary summation represents a vector in the span. -/
theorem mem_spanCodes_vectorSpan {width code : ℕ} {generators : List ℕ}
    (h : code ∈ spanCodes generators) : VectorSpan width generators (vector width code) := by
  induction generators generalizing code with
  | nil =>
    simp only [spanCodes, List.mem_singleton] at h
    subst code
    change vector width 0 = 0
    funext i
    simp [vector, scalar]
  | cons g gs ih =>
    simp only [spanCodes, List.mem_append, List.mem_map] at h
    rcases h with h | ⟨c, hc, rfl⟩
    · exact Or.inl (ih h)
    · exact Or.inr ⟨vector width c, ih hc, vector_xor width g c⟩

/-- The generating vectors as a set. -/
def generatorSet (width : ℕ) (generators : List ℕ) : Set (Fin width → ZMod 2) :=
  {v | ∃ g ∈ generators, vector width g = v}

@[simp] theorem generatorSet_nil (width : ℕ) : generatorSet width [] = ∅ := by
  ext v
  simp [generatorSet]

@[simp] theorem generatorSet_cons (width g : ℕ) (gs : List ℕ) :
    generatorSet width (g :: gs) = insert (vector width g) (generatorSet width gs) := by
  ext v
  simp [generatorSet, eq_comm, or_and_right, exists_or]

/-- The ordered family of the supplied generating vectors. -/
def generatorFamily (width : ℕ) (generators : List ℕ) :
    Fin generators.length → (Fin width → ZMod 2) := fun i => vector width generators[i]

theorem generatorSet_eq_range (width : ℕ) (generators : List ℕ) :
    generatorSet width generators = Set.range (generatorFamily width generators) := by
  ext v
  constructor
  · rintro ⟨g, hg, heq⟩
    obtain ⟨i, hi, hgi⟩ := List.mem_iff_getElem.mp hg
    exact ⟨⟨i, hi⟩, by simpa [generatorFamily, hgi] using heq⟩
  · rintro ⟨i, rfl⟩
    exact ⟨generators[i], List.getElem_mem i.isLt, rfl⟩

/-- There are precisely the two scalars used by the recursive span. -/
theorem scalar_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have h : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide +kernel
  exact h a

/-- The recursive binary span is exactly mathlib's linear span. -/
theorem vectorSpan_iff_mem_span (width : ℕ) (generators : List ℕ)
    (v : Fin width → ZMod 2) :
    VectorSpan width generators v ↔ v ∈ Submodule.span (ZMod 2) (generatorSet width generators) := by
  induction generators generalizing v with
  | nil => simp [VectorSpan]
  | cons g gs ih =>
    rw [generatorSet_cons, Submodule.mem_span_insert]
    constructor
    · rintro (hv | ⟨w, hw, heq⟩)
      · exact ⟨0, v, (ih v).mp hv, by simp⟩
      · exact ⟨1, w, (ih w).mp hw, by simpa using heq⟩
    · rintro ⟨a, w, hw, heq⟩
      rcases scalar_cases a with rfl | rfl
      · left
        have hvw : v = w := by simpa using heq
        exact hvw ▸ (ih w).mpr hw
      · exact Or.inr ⟨w, (ih w).mpr hw, by simpa using heq⟩

/-- The row equations on an ordinary vector over the binary field. -/
def VectorKernel (width : ℕ) (rows : List ℕ) (v : Fin width → ZMod 2) : Prop :=
  ∀ row ∈ rows, ∑ i : Fin width, vector width row i * v i = 0

/-- The kernel as a submodule of the ordinary binary vector space. -/
def kernelSubmodule (width : ℕ) (rows : List ℕ) : Submodule (ZMod 2) (Fin width → ZMod 2) where
  carrier := {v | VectorKernel width rows v}
  zero_mem' := by
    change VectorKernel width rows 0
    simp [VectorKernel]
  add_mem' := by
    intro v w hv hw row hrow
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hv row hrow, hw row hrow,
      zero_add]
  smul_mem' := by
    intro a v hv row hrow
    change (∑ i : Fin width, vector width row i * (a * v i)) = 0
    calc
      _ = a * ∑ i : Fin width, vector width row i * v i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by rw [hv row hrow, mul_zero]

noncomputable instance kernelSubmoduleFintype (width : ℕ) (rows : List ℕ) :
    Fintype ↥(kernelSubmodule width rows) := Fintype.ofFinite _

/-- Mask coordinates determine a bounded mask uniquely. -/
theorem vector_injective_bounded {width a b : ℕ} (ha : a < 2 ^ width) (hb : b < 2 ^ width)
    (h : vector width a = vector width b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < width
  · have hs := congrFun h ⟨i, hi⟩
    change scalar (a.testBit i) = scalar (b.testBit i) at hs
    cases hea : a.testBit i <;> cases heb : b.testBit i <;> simp_all [scalar]
  · have hpow : 2 ^ width ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (ha.trans_le hpow), Nat.testBit_lt_two_pow (hb.trans_le hpow)]

/-- The usual binary-coordinate identification of all bounded masks and all
vectors over `F₂`. -/
def codeVector (width : ℕ) (code : Fin (2 ^ width)) : Fin width → ZMod 2 :=
  vector width code

theorem codeVector_bijective (width : ℕ) : Function.Bijective (codeVector width) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro a b h
    exact Fin.ext (vector_injective_bounded a.isLt b.isLt h)
  · simp [ZMod.card]

/-- The integer XOR span stays inside its declared number of coordinates. -/
theorem spanCodes_bounded {width : ℕ} {generators : List ℕ}
    (bounds : ∀ g ∈ generators, g < 2 ^ width) {code : ℕ} (h : code ∈ spanCodes generators) :
    code < 2 ^ width := by
  induction generators generalizing code with
  | nil =>
    have hc : code = 0 := by simpa [spanCodes] using h
    subst code
    exact Nat.two_pow_pos width
  | cons g gs ih =>
    simp only [spanCodes, List.mem_append, List.mem_map] at h
    rcases h with h | ⟨c, hc, rfl⟩
    · exact ih (fun x hx => bounds x (List.mem_cons_of_mem g hx)) h
    · exact Nat.xor_lt_two_pow (bounds g List.mem_cons_self)
        (ih (fun x hx => bounds x (List.mem_cons_of_mem g hx)) hc)

/-- Every vector in the span has a mask obtained by binary summation. -/
theorem vectorSpan_exists_mask {width : ℕ} {generators : List ℕ}
    {v : Fin width → ZMod 2} (h : VectorSpan width generators v) :
    ∃ code ∈ spanCodes generators, v = vector width code := by
  induction generators generalizing v with
  | nil =>
    refine ⟨0, by simp [spanCodes], ?_⟩
    have hv : v = 0 := h
    rw [hv]
    funext i
    simp [vector, scalar]
  | cons g gs ih =>
    rcases h with h | ⟨w, hw, heq⟩
    · obtain ⟨c, hc, hvc⟩ := ih h
      exact ⟨c, List.mem_append_left _ hc, hvc⟩
    · obtain ⟨c, hc, hwc⟩ := ih hw
      refine ⟨Nat.xor g c, List.mem_append_right _ (List.mem_map.mpr ⟨c, hc, rfl⟩), ?_⟩
      rw [heq, hwc, vector_xor]

/-- For bounded masks, executable span membership is semantic linear span
membership over the binary field. -/
theorem spanCodes_iff_mem_span {width code : ℕ} {generators : List ℕ}
    (bounds : ∀ g ∈ generators, g < 2 ^ width) (bound : code < 2 ^ width) :
    code ∈ spanCodes generators ↔
      vector width code ∈ Submodule.span (ZMod 2) (generatorSet width generators) := by
  constructor
  · intro h
    exact (vectorSpan_iff_mem_span width generators _).mp (mem_spanCodes_vectorSpan h)
  · intro h
    obtain ⟨c, hc, heq⟩ := vectorSpan_exists_mask
      ((vectorSpan_iff_mem_span width generators _).mpr h)
    have hcc : code = c := vector_injective_bounded bound (spanCodes_bounded bounds hc) heq
    simpa [hcc] using hc

/-- Structural insertion sort, used to compare small spans with the ascending
exhaustive enumeration without invoking an opaque sorting implementation. -/
def insertCode (code : ℕ) : List ℕ → List ℕ
  | [] => [code]
  | h :: t => if code ≤ h then code :: h :: t else h :: insertCode code t

def sortCodes : List ℕ → List ℕ
  | [] => []
  | h :: t => insertCode h (sortCodes t)

@[simp] theorem mem_insertCode {a code : ℕ} {l : List ℕ} :
    a ∈ insertCode code l ↔ a = code ∨ a ∈ l := by
  induction l with
  | nil => simp [insertCode]
  | cons h t ih =>
    simp only [insertCode]
    split <;> simp [ih, or_left_comm]

@[simp] theorem mem_sortCodes {a : ℕ} {l : List ℕ} : a ∈ sortCodes l ↔ a ∈ l := by
  induction l with
  | nil => simp [sortCodes]
  | cons h t ih => simp [sortCodes, ih]

@[simp] theorem length_insertCode (code : ℕ) (l : List ℕ) :
    (insertCode code l).length = l.length + 1 := by
  induction l with
  | nil => simp [insertCode]
  | cons h t ih => simp only [insertCode]; split <;> simp [ih, Nat.add_assoc]

@[simp] theorem length_sortCodes (l : List ℕ) : (sortCodes l).length = l.length := by
  induction l with
  | nil => rfl
  | cons h t ih => simp [sortCodes, ih]

@[simp] theorem length_spanCodes (generators : List ℕ) :
    (spanCodes generators).length = 2 ^ generators.length := by
  induction generators with
  | nil => rfl
  | cons g gs ih => simp [spanCodes, ih, pow_succ, Nat.mul_two]

/-- Exact finite certificates transfer directly to semantic matrix kernels. -/
theorem kernel_iff_spanCodes {width : ℕ} {rows generators : List ℕ}
    (certificate : kernelCodes width rows = sortCodes (spanCodes generators))
    {code : ℕ} (bound : code < 2 ^ width) :
    Kernel width rows code ↔ code ∈ spanCodes generators := by
  have h := @mem_kernelCodes width code rows
  rw [certificate] at h
  simpa [bound] using h.symm

/-- Exact finite certificates identify the matrix kernel with mathlib's
linear span over `F₂`, in the declared mask coordinates. -/
theorem kernel_iff_mem_span {width : ℕ} {rows generators : List ℕ}
    (certificate : kernelCodes width rows = sortCodes (spanCodes generators))
    (bounds : ∀ g ∈ generators, g < 2 ^ width) {code : ℕ} (bound : code < 2 ^ width) :
    Kernel width rows code ↔
      vector width code ∈ Submodule.span (ZMod 2) (generatorSet width generators) :=
  (kernel_iff_spanCodes certificate bound).trans (spanCodes_iff_mem_span bounds bound)

/-- The certificate identifies the complete kernel in the actual binary
vector space with the supplied generating span. Every vector is represented. -/
theorem vectorKernel_iff_mem_span {width : ℕ} {rows generators : List ℕ}
    (certificate : kernelCodes width rows = sortCodes (spanCodes generators))
    (bounds : ∀ g ∈ generators, g < 2 ^ width) (v : Fin width → ZMod 2) :
    VectorKernel width rows v ↔
      v ∈ Submodule.span (ZMod 2) (generatorSet width generators) := by
  obtain ⟨code, hcode⟩ := (codeVector_bijective width).surjective v
  rw [← hcode]
  exact kernel_iff_mem_span certificate bounds code.isLt

/-- Equality of the complete binary kernel submodule and the known span. -/
theorem kernelSubmodule_eq_span {width : ℕ} {rows generators : List ℕ}
    (certificate : kernelCodes width rows = sortCodes (spanCodes generators))
    (bounds : ∀ g ∈ generators, g < 2 ^ width) :
    kernelSubmodule width rows = Submodule.span (ZMod 2) (generatorSet width generators) := by
  ext v
  exact vectorKernel_iff_mem_span certificate bounds v

/-- The bounded binary kernel as a finite set of integer masks. -/
def kernelSet (width : ℕ) (rows : List ℕ) : Finset ℕ :=
  (kernelCodes width rows).toFinset

@[simp] theorem mem_kernelSet {width code : ℕ} {rows : List ℕ} :
    code ∈ kernelSet width rows ↔ code < 2 ^ width ∧ Kernel width rows code := by
  simp [kernelSet, mem_kernelCodes]

/-- The exhaustive list has no duplicates. -/
theorem kernelCodes_nodup (width : ℕ) (rows : List ℕ) :
    (kernelCodes width rows).Nodup := (List.nodup_range).filter _

/-- Finite-set cardinality certificate counts the actual bounded kernel. -/
theorem kernelSet_card {width : ℕ} {rows : List ℕ} {size : ℕ}
    (certificate : (kernelCodes width rows).length = size) :
    (kernelSet width rows).card = size := by
  rw [kernelSet, List.toFinset_card_of_nodup (kernelCodes_nodup width rows), certificate]

/-- Semantic kernel consists of the certified number of distinct masks. -/
theorem kernel_card {width : ℕ} {rows : List ℕ} {size : ℕ}
    (certificate : (kernelCodes width rows).length = size) :
    Fintype.card {code : Fin (2 ^ width) // Kernel width rows code} = size := by
  let e : {code : Fin (2 ^ width) // Kernel width rows code} ≃
      ↥(kernelSet width rows) :=
    { toFun := fun c => ⟨c.val.val, mem_kernelSet.mpr ⟨c.val.isLt, c.property⟩⟩
      invFun := fun c => ⟨⟨c.val, (mem_kernelSet.mp c.property).1⟩,
          (mem_kernelSet.mp c.property).2⟩
      left_inv := fun c => by rfl
      right_inv := fun c => by rfl }
  exact (Fintype.card_congr e).trans ((Fintype.card_coe _).trans (kernelSet_card certificate))

/-- Cardinality of the kernel in the actual binary vector space. -/
theorem kernelSubmodule_card {width : ℕ} {rows : List ℕ} {size : ℕ}
    (certificate : (kernelCodes width rows).length = size) :
    Fintype.card ↥(kernelSubmodule width rows) = size := by
  classical
  let e : {code : Fin (2 ^ width) // Kernel width rows code} ≃
      ↥(kernelSubmodule width rows) :=
    Equiv.subtypeEquiv (Equiv.ofBijective (codeVector width) (codeVector_bijective width))
      (fun _ => Iff.rfl)
  exact (Fintype.card_congr e).symm.trans (kernel_card certificate)

/-- An exact power-of-two count determines the kernel dimension. -/
theorem kernelSubmodule_finrank {width : ℕ} {rows : List ℕ} {dimension : ℕ}
    (certificate : (kernelCodes width rows).length = 2 ^ dimension) :
    Module.finrank (ZMod 2) ↥(kernelSubmodule width rows) = dimension := by
  have h := kernelSubmodule_card certificate
  rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card] at h
  exact (Nat.pow_right_inj (by decide : 1 < 2)).mp h

/-- An exact kernel/span certificate also proves that the supplied generators
are linearly independent in the actual binary vector space. -/
theorem generators_linearIndependent {width : ℕ} {rows generators : List ℕ}
    (certificate : kernelCodes width rows = sortCodes (spanCodes generators))
    (bounds : ∀ g ∈ generators, g < 2 ^ width) :
    LinearIndependent (ZMod 2) (generatorFamily width generators) := by
  apply linearIndependent_iff_card_eq_finrank_span.mpr
  simp only [Fintype.card_fin, Set.finrank]
  rw [← generatorSet_eq_range, ← kernelSubmodule_eq_span certificate bounds]
  symm
  apply kernelSubmodule_finrank
  rw [certificate, length_sortCodes, length_spanCodes]

end RankCertificates.Binary
