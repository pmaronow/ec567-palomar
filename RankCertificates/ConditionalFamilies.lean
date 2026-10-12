module

public import RankCertificates.TwoIsogenyRank
public import RankCertificates.Geometric

/-!
# Conditional exact-rank infinitude for the three explicit families

These implications concern genuine rational Mordell–Weil ranks and genuine
geometric isomorphism classes. The infinite specialization sets, the
exact cardinalities of the actual rational-point squareclass images
are hypotheses. The two-isogeny rank identity is proved separately. In particular these
declarations do not claim unconditional rank-five, rank-six, or rank-seven
infinitude. The separate binary certificate modules do not prove the actual
image-cardinality hypotheses.
-/

@[expose] public section

namespace RankCertificates

/-- Conditional rank-five infinitude. The image dimensions required by the
source manuscript are `3` and `4`; their rank contribution is `3+4-2=5`. -/
theorem conditional_rank5_infinitude (s : Set ℚ) (hs : s.Infinite)
    (hregular : ∀ t ∈ s, Geometric.denominator5.eval t ≠ 0)
    (himages : ∀ t ∈ s, ActualImageCardinalities (Rank5.a t 1) (Rank5.b t 1) 3 4) :
    InfinitelyManyExactRank 5 := by
  apply (Geometric.geometric_image5_infinite s hs hregular).mono
  rintro j ⟨t, ht, rfl⟩
  let : (Rank5.E t 1).IsElliptic := Geometric.elliptic5_of_regular (hregular t ht)
  let : (twoTorsionModel (Rank5.a t 1) (Rank5.b t 1)).IsElliptic := by
    simpa only [twoTorsionModel, Rank5.E, model] using
      Geometric.elliptic5_of_regular (hregular t ht)
  let E : RationalEllipticCurve := ⟨Rank5.E t 1, inferInstance⟩
  refine ⟨E, ?_, ?_⟩
  · exact WeierstrassCurve.j_eq (Rank5.E t 1)
  · exact hasExactRank_of_twoIsogeny_image_cardinalities (Rank5.a t 1) (Rank5.b t 1)
      5 3 4 (himages t ht) (by decide)

/-- Conditional rank-six infinitude. The actual image dimensions required by
the source manuscript are `4` and `4`. -/
theorem conditional_rank6_infinitude (s : Set ℚ) (hs : s.Infinite)
    (hregular : ∀ t ∈ s, Geometric.denominator6.eval t ≠ 0)
    (himages : ∀ t ∈ s, ActualImageCardinalities (Rank6.a t 1) (Rank6.b t 1) 4 4) :
    InfinitelyManyExactRank 6 := by
  apply (Geometric.geometric_image6_infinite s hs hregular).mono
  rintro j ⟨t, ht, rfl⟩
  let : (Rank6.E t 1).IsElliptic := Geometric.elliptic6_of_regular (hregular t ht)
  let : (twoTorsionModel (Rank6.a t 1) (Rank6.b t 1)).IsElliptic := by
    simpa only [twoTorsionModel, Rank6.E, model] using
      Geometric.elliptic6_of_regular (hregular t ht)
  let E : RationalEllipticCurve := ⟨Rank6.E t 1, inferInstance⟩
  refine ⟨E, ?_, ?_⟩
  · exact WeierstrassCurve.j_eq (Rank6.E t 1)
  · exact hasExactRank_of_twoIsogeny_image_cardinalities (Rank6.a t 1) (Rank6.b t 1)
      6 4 4 (himages t ht) (by decide)

/-- Conditional rank-seven infinitude. The actual image dimensions required by
the source manuscript are `5` and `4`. -/
theorem conditional_rank7_infinitude (s : Set ℚ) (hs : s.Infinite)
    (hregular : ∀ t ∈ s, Geometric.denominator7.eval t ≠ 0)
    (himages : ∀ t ∈ s, ActualImageCardinalities (Rank7.a t 1) (Rank7.b t 1) 5 4) :
    InfinitelyManyExactRank 7 := by
  apply (Geometric.geometric_image7_infinite s hs hregular).mono
  rintro j ⟨t, ht, rfl⟩
  let : (Rank7.E t 1).IsElliptic := Geometric.elliptic7_of_regular (hregular t ht)
  let : (twoTorsionModel (Rank7.a t 1) (Rank7.b t 1)).IsElliptic := by
    simpa only [twoTorsionModel, Rank7.E, model] using
      Geometric.elliptic7_of_regular (hregular t ht)
  let E : RationalEllipticCurve := ⟨Rank7.E t 1, inferInstance⟩
  refine ⟨E, ?_, ?_⟩
  · exact WeierstrassCurve.j_eq (Rank7.E t 1)
  · exact hasExactRank_of_twoIsogeny_image_cardinalities (Rank7.a t 1) (Rank7.b t 1)
      7 5 4 (himages t ht) (by decide)

end RankCertificates
