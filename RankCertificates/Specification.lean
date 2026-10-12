module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.Data.Set.Finite.Lattice

/-!
# The actual exact-rank infinitude problem

The rank below is the cardinal rank of the genuine group of rational points,
viewed as a `ℤ`-module. In particular an infinite rank is not silently replaced
by the junk natural-number value of `Module.finrank`.

The infinitude target counts distinct rational `j`-invariants of nonsingular
Weierstrass models. The geometric-isomorphism lemma proves that this is exactly
infinitude up to isomorphism over `AlgebraicClosure ℚ`.

This module specifies the requested result and proves only general assembly
lemmas. It contains no proof of `InfinitelyManyExactRank 5`, `6`, or `7`.
-/

@[expose] public section

namespace RankCertificates

/-- The genuine rational Mordell–Weil rank, retaining its cardinal value. -/
noncomputable def rationalRank (E : WeierstrassCurve ℚ) : Cardinal :=
  Module.rank ℤ E.toAffine.Point

/-- An exact finite rational Mordell–Weil rank, expressed without `toNat`. -/
def HasExactRank (E : WeierstrassCurve ℚ) (r : ℕ) : Prop :=
  rationalRank E = (r : Cardinal)

/-- A rational Weierstrass model with certified nonzero discriminant. -/
structure RationalEllipticCurve where
  model : WeierstrassCurve ℚ
  elliptic : model.IsElliptic

instance (E : RationalEllipticCurve) : E.model.IsElliptic := E.elliptic

/-- The usual rational `j`-invariant of a nonsingular rational model. -/
noncomputable def RationalEllipticCurve.j (E : RationalEllipticCurve) : ℚ := E.model.j

/-- Isomorphism over the algebraic closure, in Weierstrass coordinates. -/
def GeometricallyIsomorphic (E E' : RationalEllipticCurve) : Prop :=
  ∃ C : WeierstrassCurve.VariableChange (AlgebraicClosure ℚ),
    C • E.model.baseChange (AlgebraicClosure ℚ) = E'.model.baseChange (AlgebraicClosure ℚ)

theorem geometricallyIsomorphic_iff_j_eq (E E' : RationalEllipticCurve) :
    GeometricallyIsomorphic E E' ↔ E.j = E'.j := by
  let : (E.model.baseChange (AlgebraicClosure ℚ)).IsElliptic := by
    dsimp only [WeierstrassCurve.baseChange]
    infer_instance
  let : (E'.model.baseChange (AlgebraicClosure ℚ)).IsElliptic := by
    dsimp only [WeierstrassCurve.baseChange]
    infer_instance
  constructor
  · rintro ⟨C, hC⟩
    have h := congrArg (fun W : WeierstrassCurve (AlgebraicClosure ℚ) =>
      W.c₄ ^ 3 / W.Δ) hC
    have hj : (E.model.baseChange (AlgebraicClosure ℚ)).j =
        (E'.model.baseChange (AlgebraicClosure ℚ)).j := by
      rw [← WeierstrassCurve.variableChange_j
        (E.model.baseChange (AlgebraicClosure ℚ)) C]
      simpa only [WeierstrassCurve.j_eq, div_eq_mul_inv, mul_comm] using h
    have hc : algebraMap ℚ (AlgebraicClosure ℚ) E.j =
        algebraMap ℚ (AlgebraicClosure ℚ) E'.j := by
      simpa only [RationalEllipticCurve.j, WeierstrassCurve.baseChange,
        WeierstrassCurve.map_j] using hj
    exact (algebraMap ℚ (AlgebraicClosure ℚ)).injective hc
  · intro h
    apply WeierstrassCurve.exists_variableChange_of_j_eq
    simpa only [RationalEllipticCurve.j, WeierstrassCurve.baseChange,
      WeierstrassCurve.map_j] using congrArg (algebraMap ℚ (AlgebraicClosure ℚ)) h

/-- Infinitely many geometric isomorphism classes of elliptic curves over `ℚ`
with rational Mordell–Weil rank exactly `r`. Equal `j`-invariants classify the
geometric isomorphism classes, as proved above. -/
def InfinitelyManyExactRank (r : ℕ) : Prop :=
  Set.Infinite {j : ℚ | ∃ E : RationalEllipticCurve, E.j = j ∧ HasExactRank E.model r}

/-- The main target when all three requested exact ranks are included. This is
a proposition, not a claimed theorem. -/
def RanksFiveThroughSeven : Prop :=
  InfinitelyManyExactRank 5 ∧ InfinitelyManyExactRank 6 ∧ InfinitelyManyExactRank 7

/-- For a finitely generated rational point group, cardinal rank agrees with
the usual finite rank. Finite generation is an explicit hypothesis. -/
theorem hasExactRank_iff_finrank_eq (E : WeierstrassCurve ℚ) (r : ℕ)
    [Module.Finite ℤ E.toAffine.Point] :
    HasExactRank E r ↔ Module.finrank ℤ E.toAffine.Point = r := by
  unfold HasExactRank rationalRank
  rw [← Module.finrank_eq_rank]
  exact Nat.cast_injective.eq_iff

/-- An infinite specialization set yields geometric infinitude if every fiber
of its `j`-map is finite and every specialization has the stated genuine rank.
The hypotheses isolate the analytic, geometric, and arithmetic obligations. -/
theorem infinitelyManyExactRank_of_finite_fibers {T : Type*} (s : Set T)
    (E : T → RationalEllipticCurve) (r : ℕ) (hs : s.Infinite)
    (hfinite : ∀ j : ℚ, {t : T | t ∈ s ∧ (E t).j = j}.Finite)
    (hrank : ∀ t ∈ s, HasExactRank (E t).model r) :
    InfinitelyManyExactRank r := by
  have himage : (RationalEllipticCurve.j ∘ E '' s).Infinite := by
    intro h
    apply hs
    exact h.of_finite_fibers _ (fun j _ => by
      simpa only [Set.inter_def, Set.preimage, Function.comp_apply,
        Set.mem_singleton_iff, Set.mem_ofPred_eq] using hfinite j)
  apply himage.mono
  rintro j ⟨t, ht, rfl⟩
  exact ⟨E t, rfl, hrank t ht⟩

end RankCertificates
