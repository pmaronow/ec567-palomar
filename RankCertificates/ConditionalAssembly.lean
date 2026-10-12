module

public import RankCertificates.MordellWeil
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Tactic

/-!
# Explicit conditional obligations for two-isogeny descent

This module defines the actual rational squareclass images, using the usual
`x`-coordinate maps on `y² = x³ + a x² + b x` and its two-isogenous partner.
It imports the proved Mordell–Weil theorem. Their homomorphisms and the isogeny rank formula are proved in the
Kummer and TwoIsogenyRank modules. This base module records explicit theorem
hypotheses so that the definitions do not depend on those later proofs.

The conditional theorem derives the genuine rank from the cardinalities of
these actual images and assembles geometric infinitude from an infinite
parameter set with finite `j`-fibers. The hypothesis about the images concerns
rational points and squareclasses, not the advertised rank conclusion.
-/

@[expose] public section

namespace RankCertificates

/-- The usual group `ℚˣ/(ℚˣ)²` of nonzero rational squareclasses. -/
abbrev RationalSquareClasses := ℚˣ ⧸ (powMonoidHom (α := ℚˣ) 2).range

/-- The squareclass of a nonzero rational number. The value at zero is `1`;
the descent map handles its zero-coordinate case separately. -/
def rationalSquareClass (x : ℚ) : RationalSquareClasses :=
  if hx : x = 0 then 1 else QuotientGroup.mk (Units.mk0 x hx)

/-- The standard Weierstrass equation with rational two-torsion `(0,0)`. -/
def twoTorsionModel (a b : ℚ) : WeierstrassCurve ℚ := ⟨0, a, 0, b, 0⟩

/-- The standard two-isogenous Weierstrass equation. -/
def twoIsogenousModel (a b : ℚ) : WeierstrassCurve ℚ :=
  twoTorsionModel (-2 * a) (a ^ 2 - 4 * b)

/-- The rational expression for `j`, defined even on singular parameters.
It is the genuine `j`-invariant whenever the model is nonsingular. -/
def twoTorsionInvariant (a b : ℚ) : ℚ :=
  (twoTorsionModel a b).Δ⁻¹ * (twoTorsionModel a b).c₄ ^ 3

theorem twoTorsionInvariant_eq_j (a b : ℚ) [(twoTorsionModel a b).IsElliptic] :
    twoTorsionInvariant a b = (twoTorsionModel a b).j := by
  rw [WeierstrassCurve.j_eq]
  rfl

/-- The classical two-isogeny squareclass function: infinity maps to `1`,
zero `x`-coordinate maps to `[b]`, and nonzero `x` maps to `[x]`.
Its homomorphism and kernel properties are proved in the later isogeny modules. -/
def twoIsogenyClass (a b : ℚ) : (twoTorsionModel a b).toAffine.Point →
    RationalSquareClasses
  | .zero => 1
  | .some x _ _ => if x = 0 then rationalSquareClass b else rationalSquareClass x

/-- The actual image on rational points, not a formal binary certificate. -/
def twoIsogenyImage (a b : ℚ) : Set RationalSquareClasses :=
  Set.range (twoIsogenyClass a b)

/-- The standard two-isogeny cardinality formula, proved for every
nonsingular normal form in `TwoIsogenyRank.lean`. -/
structure TwoIsogenyRankIdentity (a b : ℚ) : Prop where
  cardinalityFormula :
    2 ^ Module.finrank ℤ (twoTorsionModel a b).toAffine.Point * 4 =
      Nat.card (twoIsogenyImage a b) * Nat.card (twoIsogenyImage (-2 * a) (a ^ 2 - 4 * b))

/-- Missing arithmetic input: matching exact cardinalities of the actual
rational-point images on the two curves. Binary matrix enumeration alone
does not discharge these two fields. -/
structure ActualImageCardinalities (a b : ℚ) (d d' : ℕ) : Prop where
  original : Nat.card (twoIsogenyImage a b) = 2 ^ d
  partner : Nat.card (twoIsogenyImage (-2 * a) (a ^ 2 - 4 * b)) = 2 ^ d'

/-- The two-isogeny formula and actual image cardinalities imply the genuine
rank `d+d'-2`. A later wrapper supplies the proved rank formula. -/
theorem hasExactRank_of_twoIsogeny_images (a b : ℚ) (r d d' : ℕ)
    [(twoTorsionModel a b).IsElliptic]
    (hidentity : TwoIsogenyRankIdentity a b)
    (himages : ActualImageCardinalities a b d d') (hd : r + 2 = d + d') :
    HasExactRank (twoTorsionModel a b) r := by
  apply (hasExactRank_iff_finrank_eq (twoTorsionModel a b) r).mpr
  have h := hidentity.cardinalityFormula
  rw [himages.original, himages.partner, ← pow_add, ← hd, pow_add] at h
  norm_num at h
  exact h

/-- Conditional global assembly. Prime-pattern infinitude must supply `hs`;
the proved rank formula supplies `hidentity`, and local/global descent
must supply `himages`.
Geometric nonconstancy must supply `hfibers`. No hypothesis is silently
declared as an axiom or as an automatically available typeclass instance. -/
theorem infinitelyManyExactRank_of_twoIsogeny_images {T : Type*} (s : Set T)
    (a b : T → ℚ) (r d d' : ℕ) (hs : s.Infinite)
    (helliptic : ∀ t ∈ s, (twoTorsionModel (a t) (b t)).IsElliptic)
    (hfibers : ∀ j : ℚ, {t : T | t ∈ s ∧
      twoTorsionInvariant (a t) (b t) = j}.Finite)
    (hidentity : ∀ t ∈ s, TwoIsogenyRankIdentity (a t) (b t))
    (himages : ∀ t ∈ s, ActualImageCardinalities (a t) (b t) d d')
    (hd : r + 2 = d + d') : InfinitelyManyExactRank r := by
  have himage : ((fun t => twoTorsionInvariant (a t) (b t)) '' s).Infinite := by
    intro h
    apply hs
    exact h.of_finite_fibers _ (fun j _ => by
      simpa only [Set.inter_def, Set.preimage, Set.mem_singleton_iff,
        Set.mem_ofPred_eq] using hfibers j)
  apply himage.mono
  rintro j ⟨t, ht, rfl⟩
  let : (twoTorsionModel (a t) (b t)).IsElliptic := helliptic t ht
  let E : RationalEllipticCurve := ⟨twoTorsionModel (a t) (b t), helliptic t ht⟩
  refine ⟨E, ?_, hasExactRank_of_twoIsogeny_images (a t) (b t) r d d'
    (hidentity t ht) (himages t ht) hd⟩
  exact (twoTorsionInvariant_eq_j (a t) (b t)).symm

end RankCertificates
