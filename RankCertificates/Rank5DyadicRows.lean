module

public import RankCertificates.Rank5OriginalTwoDescent
public import RankCertificates.Rank5PartnerTwoDescent
public import RankCertificates.KummerScaling
public import RankCertificates.PrimePowerCharacters

@[expose] public section

namespace RankCertificates.Rank5TwoDescent

open Integration LocalValuations PrimePowerResidues

set_option maxHeartbeats 0

/-- The dyadic normalized unit of every actual original image
representative in the coupled integral normal form. -/
theorem scaled_original_image_unit_eight (a b k : ℤ)
    (ha : (a:ZMod 8)=3) (hb : (b:ZMod 8)=1) (hk : (k:ZMod 8)=1)
    (hrel : a^2-b=8*k) {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (64*(a:ℚ)) (1024*(b:ℚ)))
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z=q) :
    unitResiduePow 2 3 z=1 := by
  obtain ⟨hb0,hbv⟩ := integer_unit_valuation_zero b (by rw [hb]; exact isUnit_one)
  obtain ⟨P,rfl⟩ := hq
  cases P with
  | zero =>
    rw [unitResiduePow_two_same_squareclass hz one_ne_zero
      (hc.trans rationalSquareClass_one.symm)]
    exact unitResiduePow_one 2 3
  | some X Y hP =>
    by_cases hx : X=0
    · simp only [twoIsogenyClass,hx,ite_true] at hc
      have hbclass : rationalSquareClass (1024*(b:ℚ))=rationalSquareClass (b:ℚ) := by
        rw [show 1024*(b:ℚ)=(b:ℚ)*(32:ℚ)^2 by ring,
          rationalSquareClass_mul_square hb0 (by norm_num)]
      rw [unitResiduePow_two_same_squareclass hz hb0 (hc.trans hbclass),
        unitResiduePow_of_valuation_zero 2 3 hbv,residuePow_int,hb]
    · simp only [twoIsogenyClass,hx,ite_false] at hc
      have hx' : X/16 ≠ 0 := div_ne_zero hx (by norm_num)
      have hclass : rationalSquareClass (X/16)=rationalSquareClass X := by
        rw [show X/16=X*(1/4:ℚ)^2 by ring]
        exact rationalSquareClass_mul_square hx (by norm_num)
      rw [unitResiduePow_two_same_squareclass hz hx' (hc.trans hclass.symm)]
      apply original_coordinate_unit_eight a b k ha hb hk hrel hx'
      have hcurve := (onCurve_iff_equation _ _ _ _).mpr hP.1
      have hA : (4:ℚ)^2*(4*(a:ℚ))=64*(a:ℚ) := by ring
      have hB : (4:ℚ)^4*(4*(b:ℚ))=1024*(b:ℚ) := by ring
      have hscaled := KummerScaling.onCurve_scale_down (u:=4) (a:=4*(a:ℚ)) (b:=4*(b:ℚ))
        (by norm_num) (by simpa only [hA,hB] using hcurve)
      simpa only [show (4:ℚ)^2=16 by norm_num,show (4:ℚ)^3=64 by norm_num] using hscaled

/-- The dyadic normalized unit of every actual partner image
representative in the integral normal form. -/
theorem scaled_partner_image_unit_eight (a k : ℤ)
    (ha : (a:ZMod 8)=3) (hk : (k:ZMod 8)=1) {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (-128*(a:ℚ)) (32768*(k:ℚ)))
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z=q) :
    unitResiduePow 2 3 z=1 ∨ unitResiduePow 2 3 z=7 := by
  obtain ⟨hk0,hkv⟩ := integer_unit_valuation_zero k (by rw [hk]; exact isUnit_one)
  obtain ⟨P,rfl⟩ := hq
  cases P with
  | zero =>
    left
    rw [unitResiduePow_two_same_squareclass hz one_ne_zero
      (hc.trans rationalSquareClass_one.symm)]
    exact unitResiduePow_one 2 3
  | some X Y hP =>
    by_cases hx : X=0
    · simp only [twoIsogenyClass,hx,ite_true] at hc
      have hb0 : 2*(k:ℚ) ≠ 0 := mul_ne_zero (by norm_num) hk0
      have hbclass : rationalSquareClass (32768*(k:ℚ))=rationalSquareClass (2*(k:ℚ)) := by
        rw [show 32768*(k:ℚ)=(2*(k:ℚ))*(128:ℚ)^2 by ring,
          rationalSquareClass_mul_square hb0 (by norm_num)]
      left
      have htwo : unitResiduePow 2 3 (2:ℚ)=1 := by
        simpa only [Nat.cast_ofNat] using unitResiduePow_prime_self 2 3
      rw [unitResiduePow_two_same_squareclass hz hb0 (hc.trans hbclass),
        unitResiduePow_mul 2 3 (by norm_num) hk0,htwo,
        unitResiduePow_of_valuation_zero 2 3 hkv,residuePow_int,hk,one_mul]
    · simp only [twoIsogenyClass,hx,ite_false] at hc
      have hx' : X/64 ≠ 0 := div_ne_zero hx (by norm_num)
      have hclass : rationalSquareClass (X/64)=rationalSquareClass X := by
        rw [show X/64=X*(1/8:ℚ)^2 by ring]
        exact rationalSquareClass_mul_square hx (by norm_num)
      rw [unitResiduePow_two_same_squareclass hz hx' (hc.trans hclass.symm)]
      apply partner_coordinate_unit_eight a k ha hk hx'
      have hcurve := (onCurve_iff_equation _ _ _ _).mpr hP.1
      have hA : (8:ℚ)^2*(-2*(a:ℚ))= -128*(a:ℚ) := by ring
      have hB : (8:ℚ)^4*(8*(k:ℚ))=32768*(k:ℚ) := by ring
      have hscaled := KummerScaling.onCurve_scale_down (u:=8) (a:= -2*(a:ℚ)) (b:=8*(k:ℚ))
        (by norm_num) (by simpa only [hA,hB] using hcurve)
      simpa only [show (8:ℚ)^2=64 by norm_num,show (8:ℚ)^3=512 by norm_num] using hscaled

/-- The fixed dyadic restriction holds throughout the complete rank-five
CRT lattice, independently of the moving-prime specialization. -/
theorem lattice_E_image_unit_eight (x y : ℤ) {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (Rank5.a (M5 x) (N5 y)) (Rank5.b (M5 x) (N5 y)))
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z=q) :
    unitResiduePow 2 3 z=1 := by
  obtain ⟨ha,hb,hk⟩ := normalized_residues x y
  apply scaled_original_image_unit_eight (alphaInt x y) (betaInt x y) (kappaInt x y)
    ha hb hk (coupled_coefficients x y) _ hz hc
  simpa only [← (normalized_coefficients x y).1,← (normalized_coefficients x y).2.1] using hq

theorem lattice_Ep_image_unit_eight (x y : ℤ) {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (-2*Rank5.a (M5 x) (N5 y)) (Rank5.c (M5 x) (N5 y)))
    {z : ℚ} (hz : z ≠ 0) (hc : rationalSquareClass z=q) :
    unitResiduePow 2 3 z=1 ∨ unitResiduePow 2 3 z=7 := by
  obtain ⟨ha,hb,hk⟩ := normalized_residues x y
  apply scaled_partner_image_unit_eight (alphaInt x y) (kappaInt x y) ha hk _ hz hc
  have hA : -128*(alphaInt x y:ℚ)= -2*Rank5.a (M5 x) (N5 y) := by
    rw [(normalized_coefficients x y).1]
    ring
  simpa only [hA,← (normalized_coefficients x y).2.2] using hq

/-- The first primitive dyadic character annihilates the entire actual
original image. -/
theorem lattice_E_image_character_four_row (x y : ℤ) {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (Rank5.a (M5 x) (N5 y)) (Rank5.b (M5 x) (N5 y))) :
    PrimePowerCharacters.dyadicCharacter4Linear (Additive.ofMul q)=0 := by
  apply PrimePowerCharacters.powerCharacterLinear_actualImage 2 2 ZMod.χ₄ ZMod.isQuadratic_χ₄ hq
  intro z hz hc
  have h8 := lattice_E_image_unit_eight x y hq hz hc
  have h4 : unitResiduePow 2 2 z=1 := by
    rw [← unitResiduePow_cast 2 2 3 (by omega),h8]
    decide
  change ZMod.χ₄ (unitResiduePow 2 2 z)=1
  rw [h4,map_one]

/-- The second primitive dyadic character annihilates the entire actual
original image. -/
theorem lattice_E_image_character_eight_row (x y : ℤ) {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (Rank5.a (M5 x) (N5 y)) (Rank5.b (M5 x) (N5 y))) :
    PrimePowerCharacters.dyadicCharacter8Linear (Additive.ofMul q)=0 := by
  apply PrimePowerCharacters.powerCharacterLinear_actualImage 2 3 ZMod.χ₈ ZMod.isQuadratic_χ₈ hq
  intro z hz hc
  change ZMod.χ₈ (unitResiduePow 2 3 z)=1
  rw [lattice_E_image_unit_eight x y hq hz hc,map_one]

/-- The second primitive dyadic character annihilates the entire actual
partner image. -/
theorem lattice_Ep_image_character_eight_row (x y : ℤ) {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (-2*Rank5.a (M5 x) (N5 y)) (Rank5.c (M5 x) (N5 y))) :
    PrimePowerCharacters.dyadicCharacter8Linear (Additive.ofMul q)=0 := by
  apply PrimePowerCharacters.powerCharacterLinear_actualImage 2 3 ZMod.χ₈ ZMod.isQuadratic_χ₈ hq
  intro z hz hc
  change ZMod.χ₈ (unitResiduePow 2 3 z)=1
  rcases lattice_Ep_image_unit_eight x y hq hz hc with hh | hh
  · rw [hh,map_one]
  · rw [hh]
    decide

end RankCertificates.Rank5TwoDescent
