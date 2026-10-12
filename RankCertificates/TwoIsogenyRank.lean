module

public import RankCertificates.GroupIndex
public import RankCertificates.Isogeny
public import RankCertificates.IsogenyPointComposition
public import RankCertificates.IsogenyRange

@[expose] public section

/-! Relating the actual rational squareclass images to the abstract
finite-index theorem. The Kummer functions here are the proved group
homomorphisms on the genuine rational point groups. -/

namespace RankCertificates

/-- Nonsingularity of the normal form supplies precisely the two nonzero
coefficients required by the explicit rational isogeny maps. -/
theorem twoTorsionModel_coefficients_ne_zero (a b : ℚ)
    [(twoTorsionModel a b).IsElliptic] : b ≠ 0 ∧ Isogeny.c a b ≠ 0 := by
  have hΔ : (model a b).Δ ≠ 0 :=
    isUnit_iff_ne_zero.mp (twoTorsionModel a b).isUnit_Δ
  rw [model_discriminant] at hΔ
  constructor
  · intro hb
    apply hΔ
    simp [hb]
  · intro hc
    apply hΔ
    change a ^ 2 - 4 * b = 0 at hc
    rw [hc, mul_zero]

/-- Writing the squareclass group additively leaves the cardinality of the
actual rational-point image unchanged. -/
theorem twoIsogenyImage_card_eq_add_range (a b : ℚ) (hb : b ≠ 0) :
    Nat.card (twoIsogenyImage a b) = Nat.card ↥(twoIsogenyClassAddHom a b hb).range := by
  let e : (twoIsogenyImage a b) ≃ ↥(twoIsogenyClassAddHom a b hb).range :=
    { toFun := fun q => ⟨Additive.ofMul q.val, q.property⟩
      invFun := fun q => ⟨q.val.toMul, q.property⟩
      left_inv := fun q => rfl
      right_inv := fun q => rfl }
  exact Nat.card_congr e

/-- The two-isogeny rank identity follows from the actual isogeny
homomorphisms and their elementary kernel/composition properties.
Finite generation is supplied by the proved Mordell–Weil theorem. -/
theorem twoIsogenyRankIdentity_of_homs (a b : ℚ) (hb : b ≠ 0)
    (hc : Isogeny.c a b ≠ 0)
    (f : (twoTorsionModel a b).toAffine.Point →+ (twoIsogenousModel a b).toAffine.Point)
    (g : (twoIsogenousModel a b).toAffine.Point →+ (twoTorsionModel a b).toAffine.Point)
    (hcomp : g.comp f = nsmulAddMonoidHom (α := (twoTorsionModel a b).toAffine.Point) 2)
    (hf : Nat.card ↥f.ker = 2) (hg : Nat.card ↥g.ker = 2)
    (hα : (twoIsogenyClassAddHom a b hb).ker = g.range)
    (hβ : (twoIsogenyClassAddHom (-2 * a) (Isogeny.c a b) hc).ker = f.range) :
    TwoIsogenyRankIdentity a b := by
  let : (twoTorsionModel a b).IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr (Isogeny.original_discriminant_ne_zero hb hc)⟩
  let : IsAddFG (twoTorsionModel a b).toAffine.Point :=
    rationalPoints_finitelyGenerated (twoTorsionModel a b)
  constructor
  rw [twoIsogenyImage_card_eq_add_range a b hb,
    twoIsogenyImage_card_eq_add_range (-2 * a) (a ^ 2 - 4 * b) hc]
  exact GroupIndex.two_isogeny_kummer_rank_formula f g
    (twoIsogenyClassAddHom a b hb)
    (twoIsogenyClassAddHom (-2 * a) (Isogeny.c a b) hc) hcomp hf hg hα hβ

/-- The two-isogeny rank formula for the genuine rational point groups of
every nonsingular two-torsion normal form. All maps, kernels and compositions
are established by the explicit rational isogenies. -/
theorem twoIsogenyRankIdentity (a b : ℚ) (hb : b ≠ 0)
    (hc : Isogeny.c a b ≠ 0) : TwoIsogenyRankIdentity a b :=
  twoIsogenyRankIdentity_of_homs a b hb hc
    (Isogeny.phiPointHom a b hb hc) (Isogeny.psiPointHom a b hb hc)
    (IsogenyComposition.psiPointHom_comp_phiPointHom a b hb hc)
    (IsogenyKernel.phiPointHom_kernel_card a b hb hc)
    (IsogenyKernel.psiPointHom_kernel_card a b hb hc)
    (Isogeny.originalClassHom_kernel a b hb hc)
    (Isogeny.partnerClassHom_kernel a b hb hc)

/-- The rank formula with nonsingularity supplied by the elliptic-curve
instance, as in the Mordell–Weil theorem. -/
theorem twoIsogenyRankIdentity_of_isElliptic (a b : ℚ)
    [(twoTorsionModel a b).IsElliptic] : TwoIsogenyRankIdentity a b := by
  obtain ⟨hb, hc⟩ := twoTorsionModel_coefficients_ne_zero a b
  exact twoIsogenyRankIdentity a b hb hc

/-- Exact cardinalities of the two actual Kummer images imply the genuine
Mordell–Weil rank, with the isogeny rank identity supplied by its proof. -/
theorem hasExactRank_of_twoIsogeny_image_cardinalities (a b : ℚ) (r d d' : ℕ)
    [(twoTorsionModel a b).IsElliptic]
    (himages : ActualImageCardinalities a b d d') (hd : r + 2 = d + d') :
    HasExactRank (twoTorsionModel a b) r :=
  hasExactRank_of_twoIsogeny_images a b r d d'
    (twoIsogenyRankIdentity_of_isElliptic a b) himages hd

end RankCertificates
