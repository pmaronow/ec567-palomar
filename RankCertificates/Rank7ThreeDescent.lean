module

public import RankCertificates.PrimeCoefficientSupport
public import RankCertificates.KummerScaling
public import RankCertificates.LocalCharacterRows

/-! The genuine fixed-three image restriction for the rank-seven family,
after its admissible square coordinate normalization. -/

@[expose] public section

namespace RankCertificates.Rank7ThreeDescent

open Integration

def aNorm (x y : ℤ) : ℤ := 11674240 *
  (PrimePatterns.Rank7.outputs 0).eval x y * (PrimePatterns.Rank7.outputs 1).eval x y *
  (PrimePatterns.Rank7.outputs 2).eval x y * (PrimePatterns.Rank7.outputs 3).eval x y

def bNorm (x y : ℤ) : ℤ := -67837952 *
  (PrimePatterns.Rank7.outputs 0).eval x y * (PrimePatterns.Rank7.outputs 1).eval x y *
  (PrimePatterns.Rank7.outputs 2).eval x y * (PrimePatterns.Rank7.outputs 3).eval x y *
  (PrimePatterns.Rank7.outputs 4).eval x y * (PrimePatterns.Rank7.outputs 5).eval x y *
  (PrimePatterns.Rank7.outputs 6).eval x y * (PrimePatterns.Rank7.outputs 7).eval x y

theorem coefficients_scale (x y : ℤ) :
    Rank7.a (M7 x) (N7 y) = 9 ^ 2 * (aNorm x y : ℚ) ∧
    Rank7.b (M7 x) (N7 y) = 9 ^ 4 * (bNorm x y : ℚ) := by
  rw [← aInteger7_cast, ← bInteger7_cast]
  simp only [aInteger7, bInteger7, aNorm, bNorm, Int.cast_mul, Int.cast_ofNat, Int.cast_neg]
  constructor <;> ring

theorem coefficients_mod_three (x y : ℤ) :
    (aNorm x y : ZMod 3) = 1 ∧ (bNorm x y : ZMod 3) = 1 := by
  have hr (i : Fin 12) : ((PrimePatterns.Rank7.outputs i).eval x y : ZMod 3) =
      (PrimePatterns.Rank7.mod3Units i : ZMod 3) := by
    rw [← ZMod.intCast_mod _ 3]
    exact congrArg (fun z : ℤ => (z : ZMod 3)) (PrimePatterns.Rank7.residue3 i x y)
  have hA : (11674240 : ZMod 3) = 1 := by decide
  have hB : (67837952 : ZMod 3) = 2 := by decide
  simp only [aNorm, bNorm, Int.cast_mul, Int.cast_neg, Int.cast_ofNat, hr, hA, hB]
  decide

theorem normalized_isElliptic (x y : ℤ) :
    (model (aNorm x y : ℚ) (bNorm x y : ℚ)).IsElliptic := by
  obtain ⟨ha, hb⟩ := coefficients_scale x y
  let : (model ((9 : ℚ) ^ 2 * (aNorm x y : ℚ)) ((9 : ℚ) ^ 4 * (bNorm x y : ℚ))).IsElliptic := by
    rw [← ha, ← hb]
    exact DescentWitnesses.elliptic7E_on_lattice x y
  exact KummerScaling.model_scale_down_isElliptic 9 _ _

/-- Every representative of every actual lattice image has trivial local
squareclass at three. -/
theorem lattice_image_three_conditions (x y : ℤ) {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (Rank7.a (M7 x) (N7 y)) (Rank7.b (M7 x) (N7 y)))
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z = q) :
    Even (padicValRat 3 z) ∧ LocalValuations.unitResidue 3 z = 1 := by
  obtain ⟨ha, hb⟩ := coefficients_scale x y
  let : (model (aNorm x y : ℚ) (bNorm x y : ℚ)).IsElliptic := normalized_isElliptic x y
  rw [ha, hb, KummerScaling.twoIsogenyImage_coordinateScale 9 _ _ (by norm_num)] at hq
  obtain ⟨hα, hβ⟩ := coefficients_mod_three x y
  exact LocalValuations.twoIsogenyImage_three_localConditions _ _ hα hβ hq hz hc

/-- The corresponding actual-image binary valuation and character rows. -/
theorem lattice_image_three_rows (x y : ℤ) {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (Rank7.a (M7 x) (N7 y)) (Rank7.b (M7 x) (N7 y))) :
    primeParity 3 (by norm_num) (Additive.ofMul q) = 0 ∧
      unitCharacterLinear 3 (Additive.ofMul q) = 0 := by
  obtain ⟨ha, hb⟩ := coefficients_scale x y
  let : (model (aNorm x y : ℚ) (bNorm x y : ℚ)).IsElliptic := normalized_isElliptic x y
  rw [ha, hb, KummerScaling.twoIsogenyImage_coordinateScale 9 _ _ (by norm_num)] at hq
  obtain ⟨hα, hβ⟩ := coefficients_mod_three x y
  exact actualImage_three_characters_zero _ _ hα hβ hq

end RankCertificates.Rank7ThreeDescent
