module

public import EllipticCurves.Mathlib.SelmerGroup
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic

@[expose] public section

/-! Finite-index algebra for a two-isogeny pair. These are abstract theorems
about genuine homomorphisms of finitely generated abelian groups. No rank
formula is assumed. The only arithmetic-free inputs are composition as
multiplication by two, the two kernel orders, and the Kummer kernel/range
identifications. -/

namespace RankCertificates.GroupIndex

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- The kernel of a composite maps onto the intersection of the first image
and second kernel, with kernel equal to the first kernel. -/
theorem card_kernel_comp (f : A →+ B) (g : B →+ A) :
    Nat.card ↥(g.comp f).ker =
      Nat.card ↥f.ker * Nat.card ↥(f.range ⊓ g.ker) := by
  let h : (g.comp f).ker →+ B := f.comp (g.comp f).ker.subtype
  have hrange : h.range = f.range ⊓ g.ker := by
    ext b
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨⟨a.val, rfl⟩, a.property⟩
    · rintro ⟨⟨a, rfl⟩, ha⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  let e : h.ker ≃ f.ker :=
    { toFun := fun a => ⟨a.val.val, a.property⟩
      invFun := fun a => ⟨⟨a.val, by
          change g (f a.val) = 0
          rw [a.property, map_zero]⟩, a.property⟩
      left_inv := fun a => rfl
      right_inv := fun a => rfl }
  calc
    Nat.card ↥(g.comp f).ker = Nat.card ↥h.ker * Nat.card ↥h.range :=
      (AddSubgroup.card_ker_mul_card_range h).symm
    _ = Nat.card ↥f.ker * Nat.card ↥(f.range ⊓ g.ker) := by
      rw [Nat.card_congr e, hrange]

/-- The finite-index product formula for an arbitrary composite. The common
intersection is retained, avoiding division or assumptions on its size. -/
theorem index_comp_mul_card_intersection (f : A →+ B) (g : B →+ A) :
    f.range.index * g.range.index * Nat.card ↥(f.range ⊓ g.ker) =
      (g.comp f).range.index * Nat.card ↥g.ker := by
  have hmap : (g.comp f).range.index =
      (f.range ⊔ g.ker).index * g.range.index := by
    rw [AddMonoidHom.range_comp, AddSubgroup.index_map]
  have htower := AddSubgroup.relIndex_mul_index
    (show f.range ≤ f.range ⊔ g.ker from le_sup_left)
  have hrel : f.range.relIndex (f.range ⊔ g.ker) = f.range.relIndex g.ker :=
    AddSubgroup.relIndex_sup_left g.ker f.range
  calc
    f.range.index * g.range.index * Nat.card ↥(f.range ⊓ g.ker) =
        (f.range.relIndex (f.range ⊔ g.ker) * (f.range ⊔ g.ker).index) *
          g.range.index * Nat.card ↥(f.range ⊓ g.ker) := by rw [htower]
    _ = ((f.range ⊔ g.ker).index * g.range.index) *
          (f.range.relIndex g.ker * Nat.card ↥(f.range ⊓ g.ker)) := by rw [hrel]; ring
    _ = (g.comp f).range.index * Nat.card ↥g.ker := by
      rw [← hmap, AddSubgroup.relIndex_mul_card]

/-- Composition as doubling determines the product of the two image indices.
The torsion contribution cancels exactly, so no hypothesis about the full
rational two-torsion subgroup is required. -/
theorem index_product_of_comp_two [IsAddFG A] (f : A →+ B) (g : B →+ A)
    [Finite ↥g.ker] (hcomp : g.comp f = nsmulAddMonoidHom (α := A) 2) :
    f.range.index * g.range.index =
      2 ^ Module.finrank ℤ A * Nat.card ↥f.ker * Nat.card ↥g.ker := by
  let i : ↥(f.range ⊓ g.ker) → ↥g.ker := fun x => ⟨x.val, x.property.2⟩
  have hi : Function.Injective i := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : ↥g.ker => z.val) h)
  let : Finite ↥(f.range ⊓ g.ker) := Finite.of_injective i hi
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥(f.range ⊓ g.ker)))
  have h := index_comp_mul_card_intersection f g
  rw [hcomp, AddSubgroup.index_range_nsmul_of_fg A (by decide : (2 : ℕ) ≠ 0)] at h
  have hker : Nat.card ↥(nsmulAddMonoidHom (α := A) 2).ker =
      Nat.card ↥f.ker * Nat.card ↥(f.range ⊓ g.ker) := by
    rw [← hcomp]
    exact card_kernel_comp f g
  rw [hker] at h
  convert h using 1
  ring

/-- Two kernels of order two give the usual two-isogeny index formula. -/
theorem two_isogeny_index_formula [IsAddFG A] (f : A →+ B) (g : B →+ A)
    (hcomp : g.comp f = nsmulAddMonoidHom (α := A) 2)
    (hf : Nat.card ↥f.ker = 2) (hg : Nat.card ↥g.ker = 2) :
    2 ^ Module.finrank ℤ A * 4 = f.range.index * g.range.index := by
  let : Finite ↥g.ker := Nat.finite_of_card_ne_zero (by rw [hg]; decide)
  have h := index_product_of_comp_two f g hcomp
  rw [hf, hg] at h
  nlinarith

/-- The rank formula derived from actual Kummer homomorphisms whose kernels
are the dual isogeny images. -/
theorem two_isogeny_kummer_rank_formula {C D : Type*} [AddGroup C] [AddGroup D]
    [IsAddFG A] (f : A →+ B) (g : B →+ A) (α : A →+ C) (β : B →+ D)
    (hcomp : g.comp f = nsmulAddMonoidHom (α := A) 2)
    (hf : Nat.card ↥f.ker = 2) (hg : Nat.card ↥g.ker = 2)
    (hα : α.ker = g.range) (hβ : β.ker = f.range) :
    2 ^ Module.finrank ℤ A * 4 = Nat.card ↥α.range * Nat.card ↥β.range := by
  rw [← AddSubgroup.index_ker α, ← AddSubgroup.index_ker β, hα, hβ]
  exact (two_isogeny_index_formula f g hcomp hf hg).trans (mul_comm _ _)

end RankCertificates.GroupIndex
