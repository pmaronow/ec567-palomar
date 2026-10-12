module

public import RankCertificates.Rank5TwoDescent

@[expose] public section

namespace RankCertificates.Rank5TwoDescent

open LocalValuations PrimePowerResidues

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Every genuine partner coordinate in the rank-five dyadic normal form
has normalized unit either one or minus one modulo eight. -/
theorem partner_coordinate_unit_eight (a k : ℤ)
    (ha : (a:ZMod 8)=3) (hk : (k:ZMod 8)=1)
    {x y : ℚ} (hx : x ≠ 0)
    (h : OnCurve (-2*(a:ℚ)) (8*(k:ℚ)) x y) :
    unitResiduePow 2 3 x=1 ∨ unitResiduePow 2 3 x=7 := by
  obtain ⟨ha0,hav⟩ := integer_unit_valuation_zero a (by rw [ha]; decide)
  obtain ⟨hk0,hkv⟩ := integer_unit_valuation_zero k (by rw [hk]; exact isUnit_one)
  have hv2 : padicValRat 2 (2:ℚ)=1 := padicValRat.self (by norm_num)
  have hv8 : padicValRat 2 (8:ℚ)=3 := by
    rw [show (8:ℚ)=(2:ℚ)^3 by norm_num,padicValRat.pow,hv2]
    norm_num
  have hav2 : padicValRat 2 (-2*(a:ℚ))=1 := by
    rw [padicValRat.mul (by norm_num) ha0,show (-2:ℚ)=-(2:ℚ) by norm_num,padicValRat.neg,hv2,hav]
    norm_num
  have hkv8 : padicValRat 2 (8*(k:ℚ))=3 := by
    rw [padicValRat.mul (by norm_num) hk0,hv8,hkv]; norm_num
  have hunitb : unitResiduePow 2 3 (8*(k:ℚ))=1 := by
    have htwo : unitResiduePow 2 3 (2:ℚ)=1 := by
      simpa only [Nat.cast_ofNat] using unitResiduePow_prime_self 2 3
    rw [unitResiduePow_mul 2 3 (by norm_num) hk0,
      show unitResiduePow 2 3 (8:ℚ)=1 from (by
        rw [show (8:ℚ)=2*(2:ℚ)^2 by norm_num,unitResiduePow_mul 2 3 (by norm_num) (by norm_num),
          htwo,unitResiduePow_two_square (by norm_num),mul_one]),
      unitResiduePow_of_valuation_zero 2 3 hkv,residuePow_int,hk]
    exact one_mul 1
  rcases lt_trichotomy (padicValRat 2 x) 0 with hrneg | hrzero | hrpos
  · have he := LocalDescent.x_valuation_even_of_negative (p:=2) (by omega) (by omega) hx hrneg h
    have hr : padicValRat 2 x ≤ -2 := by obtain ⟨j,hj⟩ := he; omega
    exact Or.inl (DyadicDominance.cubic_unitResiduePow_one hx (Or.inr (by omega)) (Or.inr (by omega)) h)
  · have hcast : OnCurve ((-2*a:ℤ):ℚ) ((8*k:ℤ):ℚ) x y := by
      simpa only [Int.cast_mul,Int.cast_neg,Int.cast_ofNat] using h
    obtain ⟨hy,hm⟩ := PrimePowerPoints.onCurve_residuePow 2 3 (-2*a) (8*k) (by omega) hcast
    simp only [Int.cast_mul,Int.cast_ofNat,Int.cast_neg,ha,hk,
      show (8:ZMod 8)=0 by decide,zero_mul,add_zero,neg_mul,← sub_eq_add_neg] at hm
    right
    rw [unitResiduePow_of_valuation_zero 2 3 hrzero]
    exact partner_zero_mod_eight (residuePow 2 3 x (by omega))
      (residuePow 2 3 y hy) (residuePow_isUnit 2 3 hx hrzero) hm
  · let u := normalizedUnit 2 x
    have hu : u ≠ 0 := normalizedUnit_ne_zero 2 hx
    have hvu : padicValRat 2 u=0 := normalizedUnit_valuation_zero 2 hx
    have huval : 0 ≤ padicValRat 2 u := by omega
    have huis : IsUnit (residuePow 2 3 u huval) := residuePow_isUnit 2 3 hu hvu
    change residuePow 2 3 u huval=1 ∨ residuePow 2 3 u huval=7
    have hsmall := partner_quadratic_valuations hu hvu a k ha hk
    by_cases hr1 : padicValRat 2 x=1
    · have hform : x=2*u := by dsimp [u,normalizedUnit]; rw [hr1]; norm_num; ring
      let B : ℚ := u^2-(a:ℚ)*u+2*(k:ℚ)
      have heq : y^2=(2:ℚ)^3*u*B := by
        dsimp [OnCurve] at h
        rw [hform] at h
        dsimp [B]
        linear_combination h
      let t := y/4
      have ht : 0 ≤ padicValRat 2 t := by
        simpa only [show (2:ℚ)^2=4 by norm_num] using square_div_integral 3 2 1 hu hvu hsmall.1 heq (by decide)
      have hdiv : (2:ℚ)*t^2=(1:ℤ)*u^3+(-a:ℤ)*u^2+(2*k:ℤ)*u := by
        dsimp [t,B] at *
        push_cast
        linear_combination (1/8:ℚ)*heq
      have hm := divided_square_residuePow 4 2 1 (-a) (2*k) huval ht
        (by simpa only [Int.cast_ofNat,one_mul] using hdiv)
      simp only [Int.cast_one,one_mul,Int.cast_mul,Int.cast_ofNat,Int.cast_neg,
        neg_mul,← sub_eq_add_neg] at hm
      have hh := partner_one_two_mod_sixteen (residuePow 2 4 u huval)
        (a:ZMod 16) (k:ZMod 16) (residuePow 2 4 t ht)
        (by rw [residuePow_cast 2 3 4 (by omega)]; exact odd_residue_eight _ huis)
        (by simpa only [ZMod.cast_intCast (by decide : 8 ∣ 16)] using ha)
        (by simpa only [ZMod.cast_intCast (by decide : 8 ∣ 16)] using hk) (Or.inl hm)
      simpa only [residuePow_cast 2 3 4 (by omega)] using hh
    · by_cases hr2 : padicValRat 2 x=2
      · have hform : x=4*u := by dsimp [u,normalizedUnit]; rw [hr2]; norm_num; ring
        let B : ℚ := 2*u^2-(a:ℚ)*u+(k:ℚ)
        have heq : y^2=(2:ℚ)^5*u*B := by
          dsimp [OnCurve] at h
          rw [hform] at h
          dsimp [B]
          linear_combination h
        let t := y/8
        have ht : 0 ≤ padicValRat 2 t := by
          simpa only [show (2:ℚ)^3=8 by norm_num] using square_div_integral 5 3 1 hu hvu hsmall.2 heq (by decide)
        have hdiv : (2:ℚ)*t^2=(2:ℤ)*u^3+(-a:ℤ)*u^2+(k:ℚ)*u := by
          dsimp [t,B] at *
          linear_combination (1/32:ℚ)*heq
        have hm := divided_square_residuePow 4 2 2 (-a) k huval ht
          (by simpa only [Int.cast_ofNat,one_mul] using hdiv)
        simp only [Int.cast_ofNat,Int.cast_neg,neg_mul,← sub_eq_add_neg] at hm
        have hh := partner_one_two_mod_sixteen (residuePow 2 4 u huval)
          (a:ZMod 16) (k:ZMod 16) (residuePow 2 4 t ht)
          (by rw [residuePow_cast 2 3 4 (by omega)]; exact odd_residue_eight _ huis)
          (by simpa only [ZMod.cast_intCast (by decide : 8 ∣ 16)] using ha)
          (by simpa only [ZMod.cast_intCast (by decide : 8 ∣ 16)] using hk) (Or.inr hm)
        simpa only [residuePow_cast 2 3 4 (by omega)] using hh
      · have hr3 : 3 ≤ padicValRat 2 x := by omega
        have he := LocalDescent.linear_term_valuation_even (p:=2) (mul_ne_zero (by norm_num) hk0) hx
          (by omega) (Or.inr (by omega)) h
        by_cases hrEq3 : padicValRat 2 x=3
        · have hform : x=8*u := by dsimp [u,normalizedUnit]; rw [hrEq3]; norm_num; ring
          let B : ℚ := 8*u^2-2*(a:ℚ)*u+(k:ℚ)
          have hB : B=0 ∨ 0 ≤ padicValRat 2 B := by
            right
            simpa only [Int.cast_ofNat,Int.cast_mul,Int.cast_neg,neg_mul,← sub_eq_add_neg] using
              quadratic_integral 8 (-2*a) k huval
          have heq : y^2=(2:ℚ)^6*u*B := by
            dsimp [OnCurve] at h
            rw [hform] at h
            dsimp [B]
            linear_combination h
          let t := y/8
          have ht : 0 ≤ padicValRat 2 t := by
            simpa only [show (2:ℚ)^3=8 by norm_num] using square_div_integral 6 3 0 hu hvu hB heq (by decide)
          have hdiv : (1:ℚ)*t^2=(8:ℤ)*u^3+(-2*a:ℤ)*u^2+(k:ℚ)*u := by
            dsimp [t,B] at *
            push_cast
            linear_combination (1/64:ℚ)*heq
          have hm := divided_square_residuePow 3 1 8 (-2*a) k huval ht
            (by simpa only [Int.cast_one,Int.cast_ofNat,one_mul] using hdiv)
          simp only [Int.cast_one,one_mul,Int.cast_mul,Int.cast_ofNat,Int.cast_neg,
            neg_mul,← sub_eq_add_neg,ha,hk] at hm
          exact Or.inr (partner_three_mod_eight _ _ huis hm)
        · have hr5 : 5 ≤ padicValRat 2 x := by obtain ⟨j,hj⟩ := he; omega
          have hm := DyadicDominance.linear_unitResiduePow_one (mul_ne_zero (by norm_num) hk0) hx
            (by omega) (Or.inr (by omega)) h
          rw [unitResiduePow_mul 2 3 (mul_ne_zero (by norm_num) hk0) hx,hunitb,one_mul] at hm
          exact Or.inl hm

end RankCertificates.Rank5TwoDescent
