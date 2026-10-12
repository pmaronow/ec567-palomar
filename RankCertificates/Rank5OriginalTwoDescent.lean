module

public import RankCertificates.Rank5TwoDescent

@[expose] public section

namespace RankCertificates.Rank5TwoDescent

open LocalValuations PrimePowerResidues

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Every genuine original coordinate in the coupled rank-five dyadic
normal form has normalized unit one modulo eight. -/
theorem original_coordinate_unit_eight (a b k : ℤ)
    (ha : (a:ZMod 8)=3) (hb : (b:ZMod 8)=1) (hk : (k:ZMod 8)=1)
    (hrel : a^2-b=8*k) {x y : ℚ} (hx : x ≠ 0)
    (h : OnCurve (4*(a:ℚ)) (4*(b:ℚ)) x y) : unitResiduePow 2 3 x=1 := by
  obtain ⟨ha0,hav⟩ := integer_unit_valuation_zero a (by rw [ha]; decide)
  obtain ⟨hb0,hbv⟩ := integer_unit_valuation_zero b (by rw [hb]; exact isUnit_one)
  have hv2 : padicValRat 2 (2:ℚ)=1 := padicValRat.self (by norm_num)
  have hv4 : padicValRat 2 (4:ℚ)=2 := by
    rw [show (4:ℚ)=(2:ℚ)^2 by norm_num,padicValRat.pow,hv2]
    norm_num
  have hav4 : padicValRat 2 (4*(a:ℚ))=2 := by rw [padicValRat.mul (by norm_num) ha0,hv4,hav]; norm_num
  have hbv4 : padicValRat 2 (4*(b:ℚ))=2 := by rw [padicValRat.mul (by norm_num) hb0,hv4,hbv]; norm_num
  have hunitb : unitResiduePow 2 3 (4*(b:ℚ))=1 := by
    rw [unitResiduePow_mul 2 3 (by norm_num) hb0,
      show unitResiduePow 2 3 (4:ℚ)=1 from
        (by simpa only [show (2:ℚ)^2=4 by norm_num] using unitResiduePow_two_square (q:=2) (by norm_num)),
      unitResiduePow_of_valuation_zero 2 3 hbv,residuePow_int,hb]
    exact one_mul 1
  rcases lt_trichotomy (padicValRat 2 x) 0 with hrneg | hrzero | hrpos
  · have he := LocalDescent.x_valuation_even_of_negative (p:=2) (by omega) (by omega) hx hrneg h
    have hr : padicValRat 2 x ≤ -2 := by obtain ⟨j,hj⟩ := he; omega
    exact DyadicDominance.cubic_unitResiduePow_one hx (Or.inr (by omega)) (Or.inr (by omega)) h
  · have hcast : OnCurve ((4*a:ℤ):ℚ) ((4*b:ℤ):ℚ) x y := by
      simpa only [Int.cast_mul,Int.cast_ofNat] using h
    obtain ⟨hy,hm⟩ := PrimePowerPoints.onCurve_residuePow 2 3 (4*a) (4*b) (by omega) hcast
    simp only [Int.cast_mul,Int.cast_ofNat,ha,hb,mul_one] at hm
    rw [unitResiduePow_of_valuation_zero 2 3 hrzero]
    exact original_zero_mod_eight (residuePow 2 3 x (by omega))
      (residuePow 2 3 y hy) (residuePow_isUnit 2 3 hx hrzero) hm
  · let u := normalizedUnit 2 x
    have hu : u ≠ 0 := normalizedUnit_ne_zero 2 hx
    have hvu : padicValRat 2 u=0 := normalizedUnit_valuation_zero 2 hx
    have huval : 0 ≤ padicValRat 2 u := by omega
    have huis : IsUnit (residuePow 2 3 u huval) := residuePow_isUnit 2 3 hu hvu
    change residuePow 2 3 u huval=1
    by_cases hr1 : padicValRat 2 x=1
    · have hform : x=2*u := by dsimp [u,normalizedUnit]; rw [hr1]; norm_num; ring
      let B : ℚ := u^2+2*(a:ℚ)*u+(b:ℚ)
      have hB : B=0 ∨ 2 ≤ padicValRat 2 B := original_quadratic_valuation hu hvu a b ha hb
      have heq : y^2=(2:ℚ)^3*u*B := by
        dsimp [OnCurve] at h
        rw [hform] at h
        dsimp [B]
        linear_combination h
      let t := y/8
      have ht : 0 ≤ padicValRat 2 t := by
        simpa only [show (2:ℚ)^3=8 by norm_num] using square_div_integral 3 3 2 hu hvu hB heq (by decide)
      have hdiv : (8:ℚ)*t^2=u^3+(2*a:ℤ)*u^2+(b:ℚ)*u := by
        dsimp [t,B] at *
        push_cast
        linear_combination (1/8:ℚ)*heq
      have hm := divided_square_residuePow 6 8 1 (2*a) b huval ht (by simpa only [Int.cast_ofNat,Int.cast_one,one_mul] using hdiv)
      have hbrel : b=a^2-8*k := by linarith
      rw [hbrel] at hm
      simp only [Int.cast_one,one_mul,Int.cast_mul,Int.cast_ofNat,Int.cast_sub,Int.cast_pow] at hm
      have hres := original_one_mod_sixtyfour (residuePow 2 6 u huval)
        (a:ZMod 64) (k:ZMod 64) (residuePow 2 6 t ht)
        (by rw [residuePow_cast 2 3 6 (by omega)]; exact huis)
        (by simpa only [ZMod.cast_intCast (by decide : 8 ∣ 64)] using ha)
        (by simpa only [ZMod.cast_intCast (by decide : 8 ∣ 64)] using hk) hm
      simpa only [residuePow_cast 2 3 6 (by omega)] using hres
    · have hr2 : 2 ≤ padicValRat 2 x := by omega
      have he := LocalDescent.linear_term_valuation_even (p:=2) (mul_ne_zero (by norm_num) hb0) hx
        (by omega) (Or.inr (by omega)) h
      by_cases hrEq2 : padicValRat 2 x=2
      · have hform : x=4*u := by dsimp [u,normalizedUnit]; rw [hrEq2]; norm_num; ring
        let B : ℚ := 4*u^2+4*(a:ℚ)*u+(b:ℚ)
        have hB : B=0 ∨ 0 ≤ padicValRat 2 B := by
          right
          simpa only [Int.cast_ofNat,Int.cast_mul] using quadratic_integral 4 (4*a) b huval
        have heq : y^2=(2:ℚ)^4*u*B := by
          dsimp [OnCurve] at h
          rw [hform] at h
          dsimp [B]
          linear_combination h
        let t := y/4
        have ht : 0 ≤ padicValRat 2 t := by
          simpa only [show (2:ℚ)^2=4 by norm_num] using square_div_integral 4 2 0 hu hvu hB heq (by decide)
        have hdiv : (1:ℚ)*t^2=(4:ℤ)*u^3+(4*a:ℤ)*u^2+(b:ℚ)*u := by
          dsimp [t,B] at *
          push_cast
          linear_combination (1/16:ℚ)*heq
        have hm := divided_square_residuePow 3 1 4 (4*a) b huval ht (by simpa only [Int.cast_ofNat,Int.cast_one,one_mul] using hdiv)
        simp only [Int.cast_one,one_mul,Int.cast_mul,Int.cast_ofNat,ha,hb] at hm
        exact original_two_mod_eight (residuePow 2 3 u huval) (residuePow 2 3 t ht) huis hm
      · have hr4 : 4 ≤ padicValRat 2 x := by obtain ⟨j,hj⟩ := he; omega
        have hm := DyadicDominance.linear_unitResiduePow_one (mul_ne_zero (by norm_num) hb0) hx
          (by omega) (Or.inr (by omega)) h
        rw [unitResiduePow_mul 2 3 (mul_ne_zero (by norm_num) hb0) hx,hunitb,one_mul] at hm
        exact hm

end RankCertificates.Rank5TwoDescent
