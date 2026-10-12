module

public import RankCertificates.SquareClassIndependence

/-!
# Finiteness of genuine two-isogeny squareclass images

Mordell–Weil finite generation and exponent two imply that the actual Kummer
images are finite. This permits lower bounds from injective mask subgroups
to be expressed with natural cardinalities.
-/

@[expose] public section

namespace RankCertificates

/-- The actual additive Kummer image is finitely generated, because it is
an image of the genuine Mordell–Weil group. -/
theorem twoIsogenyImageSubgroup_addFG (a b : ℚ)
    [(twoTorsionModel a b).IsElliptic] :
    IsAddFG (twoIsogenyClassAddHom a b (twoTorsion_b_ne_zero a b)).range := by
  have : IsAddFG (twoTorsionModel a b).toAffine.Point :=
    rationalPoints_finitelyGenerated _
  exact IsAddFG.of_surjective
    (twoIsogenyClassAddHom a b (twoTorsion_b_ne_zero a b)).rangeRestrict
    (AddMonoidHom.rangeRestrict_surjective _)

/-- The actual Kummer image is finite over the binary field. -/
theorem twoIsogenyImageSubmodule_finite (a b : ℚ)
    [(twoTorsionModel a b).IsElliptic] :
    Module.Finite (ZMod 2) (AddSubgroup.toZModSubmodule 2
      (twoIsogenyClassAddHom a b (twoTorsion_b_ne_zero a b)).range) := by
  let S := AddSubgroup.toZModSubmodule 2
    (twoIsogenyClassAddHom a b (twoTorsion_b_ne_zero a b)).range
  have : IsAddFG S := twoIsogenyImageSubgroup_addFG a b
  have : Module.Finite ℤ S := Module.Finite.iff_addGroup_fg.mpr inferInstance
  exact Module.Finite.of_restrictScalars_finite ℤ (ZMod 2) S

/-- The genuine rational-point squareclass image is a finite set. -/
theorem twoIsogenyImage_finite (a b : ℚ)
    [(twoTorsionModel a b).IsElliptic] : (twoIsogenyImage a b).Finite := by
  let S := AddSubgroup.toZModSubmodule 2
    (twoIsogenyClassAddHom a b (twoTorsion_b_ne_zero a b)).range
  have : Module.Finite (ZMod 2) S := twoIsogenyImageSubmodule_finite a b
  have : Finite S := Module.finite_of_finite (ZMod 2)
  apply Set.finite_coe_iff.mp
  change Finite ↥((twoIsogenyClassAddHom a b (twoTorsion_b_ne_zero a b)).range :
    Set (Additive RationalSquareClasses))
  exact this

/-- A subgroup of known point classes gives an honest lower bound for the
finite actual Kummer image. -/
theorem twoIsogenyImage_card_lowerBound_of_closure (a b : ℚ)
    [(twoTorsionModel a b).IsElliptic] (s : Set RationalSquareClasses) (d : ℕ)
    (hcard : Nat.card (Subgroup.closure s) = 2 ^ d)
    (hmem : (Subgroup.closure s : Set RationalSquareClasses) ⊆ twoIsogenyImage a b) :
    2 ^ d ≤ Nat.card (twoIsogenyImage a b) := by
  rw [← hcard]
  have : Finite (twoIsogenyImage a b) := Set.finite_coe_iff.mpr
    (twoIsogenyImage_finite a b)
  exact Nat.card_le_card_of_injective (Set.inclusion hmem) (Set.inclusion_injective hmem)

/-- The witnessed rank-5 E masks give at least `2^3` classes
in the actual rational-point image, under distinct positive prime columns. -/
theorem actualImage5E_card_lowerBound (x y : ℤ)
    (hp : IsSignedPrimeColumnList (n := 11)
      (Integration.columns5E (Integration.outputs5 x y))) :
    2 ^ 3 ≤ Nat.card (twoIsogenyImage (Rank5.a (Integration.M5 x) (Integration.N5 y)) (Rank5.b (Integration.M5 x) (Integration.N5 y))) := by
  let : (twoTorsionModel (Rank5.a (Integration.M5 x) (Integration.N5 y)) (Rank5.b (Integration.M5 x) (Integration.N5 y))).IsElliptic :=
    DescentWitnesses.elliptic5E_on_lattice x y
  exact twoIsogenyImage_card_lowerBound_of_closure _ _ _ 3
    (knownclasses5E_closure_card (Integration.outputs5 x y) hp)
    (DescentWitnesses.knownclasses5E_closure_le_actual_image x y)

/-- The witnessed rank-5 Ep masks give at least `2^4` classes
in the actual rational-point image, under distinct positive prime columns. -/
theorem actualImage5Ep_card_lowerBound (x y : ℤ)
    (hp : IsSignedPrimeColumnList (n := 11)
      (Integration.columns5Ep (Integration.outputs5 x y))) :
    2 ^ 4 ≤ Nat.card (twoIsogenyImage ((-2 * Rank5.a (Integration.M5 x) (Integration.N5 y))) (Rank5.c (Integration.M5 x) (Integration.N5 y))) := by
  let : (twoTorsionModel ((-2 * Rank5.a (Integration.M5 x) (Integration.N5 y))) (Rank5.c (Integration.M5 x) (Integration.N5 y))).IsElliptic :=
    DescentWitnesses.elliptic5Ep_on_lattice x y
  exact twoIsogenyImage_card_lowerBound_of_closure _ _ _ 4
    (knownclasses5Ep_closure_card (Integration.outputs5 x y) hp)
    (DescentWitnesses.knownclasses5Ep_closure_le_actual_image x y)

/-- The witnessed rank-6 E masks give at least `2^4` classes
in the actual rational-point image, under distinct positive prime columns. -/
theorem actualImage6E_card_lowerBound (x y : ℤ)
    (hp : IsSignedPrimeColumnList (n := 11)
      (Integration.columns6E (Integration.outputs6 x y))) :
    2 ^ 4 ≤ Nat.card (twoIsogenyImage (Rank6.a (Integration.M6 x) (Integration.N6 y)) (Rank6.b (Integration.M6 x) (Integration.N6 y))) := by
  let : (twoTorsionModel (Rank6.a (Integration.M6 x) (Integration.N6 y)) (Rank6.b (Integration.M6 x) (Integration.N6 y))).IsElliptic :=
    DescentWitnesses.elliptic6E_on_lattice x y
  exact twoIsogenyImage_card_lowerBound_of_closure _ _ _ 4
    (knownclasses6E_closure_card (Integration.outputs6 x y) hp)
    (DescentWitnesses.knownclasses6E_closure_le_actual_image x y)

/-- The witnessed rank-6 Ep masks give at least `2^4` classes
in the actual rational-point image, under distinct positive prime columns. -/
theorem actualImage6Ep_card_lowerBound (x y : ℤ)
    (hp : IsSignedPrimeColumnList (n := 11)
      (Integration.columns6Ep (Integration.outputs6 x y))) :
    2 ^ 4 ≤ Nat.card (twoIsogenyImage ((-2 * Rank6.a (Integration.M6 x) (Integration.N6 y))) (Rank6.c (Integration.M6 x) (Integration.N6 y))) := by
  let : (twoTorsionModel ((-2 * Rank6.a (Integration.M6 x) (Integration.N6 y))) (Rank6.c (Integration.M6 x) (Integration.N6 y))).IsElliptic :=
    DescentWitnesses.elliptic6Ep_on_lattice x y
  exact twoIsogenyImage_card_lowerBound_of_closure _ _ _ 4
    (knownclasses6Ep_closure_card (Integration.outputs6 x y) hp)
    (DescentWitnesses.knownclasses6Ep_closure_le_actual_image x y)

/-- The witnessed rank-7 E masks give at least `2^5` classes
in the actual rational-point image, under distinct positive prime columns. -/
theorem actualImage7E_card_lowerBound (x y : ℤ)
    (hp : IsSignedPrimeColumnList (n := 12)
      (Integration.columns7E (Integration.outputs7 x y))) :
    2 ^ 5 ≤ Nat.card (twoIsogenyImage (Rank7.a (Integration.M7 x) (Integration.N7 y)) (Rank7.b (Integration.M7 x) (Integration.N7 y))) := by
  let : (twoTorsionModel (Rank7.a (Integration.M7 x) (Integration.N7 y)) (Rank7.b (Integration.M7 x) (Integration.N7 y))).IsElliptic :=
    DescentWitnesses.elliptic7E_on_lattice x y
  exact twoIsogenyImage_card_lowerBound_of_closure _ _ _ 5
    (knownclasses7E_closure_card (Integration.outputs7 x y) hp)
    (DescentWitnesses.knownclasses7E_closure_le_actual_image x y)

/-- The witnessed rank-7 Ep masks give at least `2^4` classes
in the actual rational-point image, under distinct positive prime columns. -/
theorem actualImage7Ep_card_lowerBound (x y : ℤ)
    (hp : IsSignedPrimeColumnList (n := 12)
      (Integration.columns7Ep (Integration.outputs7 x y))) :
    2 ^ 4 ≤ Nat.card (twoIsogenyImage ((-2 * Rank7.a (Integration.M7 x) (Integration.N7 y))) (Rank7.c (Integration.M7 x) (Integration.N7 y))) := by
  let : (twoTorsionModel ((-2 * Rank7.a (Integration.M7 x) (Integration.N7 y))) (Rank7.c (Integration.M7 x) (Integration.N7 y))).IsElliptic :=
    DescentWitnesses.elliptic7Ep_on_lattice x y
  exact twoIsogenyImage_card_lowerBound_of_closure _ _ _ 4
    (knownclasses7Ep_closure_card (Integration.outputs7 x y) hp)
    (DescentWitnesses.knownclasses7Ep_closure_le_actual_image x y)

end RankCertificates
