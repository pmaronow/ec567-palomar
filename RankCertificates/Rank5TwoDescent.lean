module

public import RankCertificates.PrimeCoefficientSupport
public import RankCertificates.PrimePowerResidues
public import RankCertificates.DyadicDominance
public import RankCertificates.PrimePowerPoints

@[expose] public section

/-! Necessary dyadic restrictions for actual rational points in the rank-five
family. Square scalings yield coupled integral normal forms; the exceptional
unit obstructions are exact computations in finite residue rings. -/

namespace RankCertificates.Rank5TwoDescent

open Integration LocalValuations PrimePowerResidues

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def outputInt (x y : ℤ) (i : Fin 12) : ℤ := (PrimePatterns.Rank5.outputs i).eval x y
def alphaInt (x y : ℤ) : ℤ :=
  10125 * (outputInt x y 0 * outputInt x y 1 * outputInt x y 2 * outputInt x y 3)
def betaInt (x y : ℤ) : ℤ :=
  -18225 * (outputInt x y 0 * outputInt x y 1 * outputInt x y 2 * outputInt x y 3) *
    (outputInt x y 4 * outputInt x y 5 * outputInt x y 6 * outputInt x y 7)
def kappaInt (x y : ℤ) : ℤ :=
  18225 * (outputInt x y 0 * outputInt x y 1 * outputInt x y 2 * outputInt x y 3) *
    (outputInt x y 8 * outputInt x y 9 * outputInt x y 10 * outputInt x y 11)

theorem normalized_coefficients (x y : ℤ) :
    Rank5.a (M5 x) (N5 y) = 64 * (alphaInt x y : ℚ) ∧
    Rank5.b (M5 x) (N5 y) = 1024 * (betaInt x y : ℚ) ∧
    Rank5.c (M5 x) (N5 y) = 32768 * (kappaInt x y : ℚ) := by
  obtain ⟨hF,hH,hJ⟩ := lattice5_factorGroups x y
  refine ⟨?_,?_,?_⟩
  all_goals
    simp only [Rank5.a,Rank5.b,Rank5.c,hF,hH,hJ,alphaInt,betaInt,kappaInt,
      outputInt,outputs5,Int.cast_mul,Int.cast_neg,Int.cast_ofNat]
    ring

theorem coupled_coefficients (x y : ℤ) :
    alphaInt x y ^ 2 - betaInt x y = 8 * kappaInt x y := by
  obtain ⟨ha,hb,hc⟩ := normalized_coefficients x y
  have h := Rank5.isogeny_coefficient (M5 x) (N5 y)
  rw [ha,hb,hc] at h
  have hr : (alphaInt x y : ℚ)^2-(betaInt x y : ℚ)=8*(kappaInt x y : ℚ) := by
    linear_combination (1/4096:ℚ)*h
  exact_mod_cast hr

theorem output_mod_eight (x y : ℤ) (i : Fin 12) :
    (outputInt x y i : ZMod 8) = (PrimePatterns.Rank5.mod8Units i : ZMod 8) := by
  rw [ZMod.intCast_eq_intCast_iff']
  dsimp [outputInt]
  rw [PrimePatterns.Rank5.residue8]
  fin_cases i <;> norm_num [PrimePatterns.Rank5.mod8Units]

theorem normalized_residues (x y : ℤ) :
    (alphaInt x y : ZMod 8)=3 ∧ (betaInt x y : ZMod 8)=1 ∧
      (kappaInt x y : ZMod 8)=1 := by
  have h0 := output_mod_eight x y 0
  have h1 := output_mod_eight x y 1
  have h2 := output_mod_eight x y 2
  have h3 := output_mod_eight x y 3
  have h4 := output_mod_eight x y 4
  have h5 := output_mod_eight x y 5
  have h6 := output_mod_eight x y 6
  have h7 := output_mod_eight x y 7
  have h8 := output_mod_eight x y 8
  have h9 := output_mod_eight x y 9
  have h10 := output_mod_eight x y 10
  have h11 := output_mod_eight x y 11
  norm_num [PrimePatterns.Rank5.mod8Units] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  refine ⟨?_,?_,?_⟩
  all_goals
    simp only [alphaInt,betaInt,kappaInt,Int.cast_mul,Int.cast_ofNat,Int.cast_neg,
      h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11]
    decide

/-- Exact dyadic valuation two detected by a residue four modulo eight. -/
theorem valuation_two_eq_two_of_residue_four {q : ℚ}
    (hq : 0 ≤ padicValRat 2 q) (hr : residuePow 2 3 q hq = 4) :
    padicValRat 2 q = 2 := by
  have hq0 : q ≠ 0 := by
    intro hz
    subst q
    exact (by decide : (0 : ZMod (2 ^ 3)) ≠ 4) (by simpa using hr)
  have h2 : residuePow 2 2 q hq = 0 := by
    rw [← residuePow_cast 2 2 3 (by omega) hq,hr]
    decide
  have h3 : residuePow 2 3 q hq ≠ 0 := by rw [hr]; decide
  have hv2 := ((residuePow_eq_zero_iff 2 2 hq).mp h2).resolve_left hq0
  have hv3 : ¬ (3:ℤ) ≤ padicValRat 2 q := by
    intro hv
    exact h3 ((residuePow_eq_zero_iff 2 3 hq).mpr (Or.inr hv))
  omega

theorem odd_residue_eight (u : ZMod 8) (hu : IsUnit u) :
    u=1 ∨ u=3 ∨ u=5 ∨ u=7 := by
  revert u
  decide +kernel

theorem square_double_mod_sixteen (u : ZMod 16) (hu : IsUnit u) :
    2*u^2=2 := by
  revert u
  decide +kernel

theorem square_eight_mod_sixtyfour (u : ZMod 64) (hu : IsUnit u) :
    8*u^2=8 := by
  revert u
  decide +kernel

theorem zero_mod_eight_square_mod_sixtyfour (u : ZMod 64)
    (hu : (ZMod.cast u : ZMod 8)=0) : u^2=0 := by
  revert u
  decide +kernel

theorem five_mod_eight_eight_mul_mod_sixtyfour (u : ZMod 64)
    (hu : (ZMod.cast u : ZMod 8)=5) : 8*u=40 := by
  revert u
  decide +kernel

/-- The next dyadic digits cannot turn either exceptional partner cubic
at unit three into a rational square. -/
theorem partner_three_mod_sixteen (u a k : ZMod 16)
    (hu : (ZMod.cast u : ZMod 8)=3)
    (ha : (ZMod.cast a : ZMod 8)=3)
    (hk : (ZMod.cast k : ZMod 8)=1) :
    u*(u^2-a*u+2*k) ≠ 2 ∧ u*(2*u^2-a*u+k) ≠ 2 := by
  revert u a k
  decide +kernel

theorem square_double_options_mod_sixteen (t : ZMod 16) :
    2*t^2=0 ∨ 2*t^2=2 ∨ 2*t^2=8 := by
  revert t
  decide +kernel

theorem square_eight_options_mod_sixtyfour (t : ZMod 64) :
    8*t^2=0 ∨ 8*t^2=8 ∨ 8*t^2=32 := by
  revert t
  decide +kernel

theorem partner_three_rhs_mod_sixteen (u a k : ZMod 16)
    (hu : (ZMod.cast u : ZMod 8)=3)
    (ha : (ZMod.cast a : ZMod 8)=3)
    (hk : (ZMod.cast k : ZMod 8)=1) :
    (u*(u^2-a*u+2*k)=6 ∨ u*(u^2-a*u+2*k)=14) ∧
      (u*(2*u^2-a*u+k)=6 ∨ u*(2*u^2-a*u+k)=14) := by
  revert u a k
  decide +kernel

/-- The unit-five original obstruction is uniform in every higher digit. -/
theorem original_five_mod_sixtyfour (u a k t : ZMod 64)
    (hu : (ZMod.cast u : ZMod 8)=5)
    (ha : (ZMod.cast a : ZMod 8)=3)
    (hk : (ZMod.cast k : ZMod 8)=1) :
    8*t^2 ≠ u*((u+a)^2-8*k) := by
  have hsum : (ZMod.cast (u+a) : ZMod 8)=0 := by
    rw [ZMod.cast_add (by norm_num : 8 ∣ 64),hu,ha]
    decide
  have hs := zero_mod_eight_square_mod_sixtyfour (u+a) hsum
  have hprod : (ZMod.cast (u*k) : ZMod 8)=5 := by
    rw [ZMod.cast_mul (by norm_num : 8 ∣ 64),hu,hk,mul_one]
  have hp := five_mod_eight_eight_mul_mod_sixtyfour (u*k) hprod
  have hr : u*((u+a)^2-8*k)=24 := by
    rw [hs]
    calc
      u*(0-8*k)= -(8*(u*k)) := by ring
      _ = 24 := by rw [hp]; decide
  rw [hr]
  rcases square_eight_options_mod_sixtyfour t with ht | ht | ht <;> rw [ht] <;> decide

/-- Necessary rational exclusion of original unit five at valuation one.
The displayed divided square equation is reduced modulo 64. -/
theorem rational_original_five_obstruction {u a k t : ℚ}
    (hu : 0 ≤ padicValRat 2 u) (ha : 0 ≤ padicValRat 2 a)
    (hk : 0 ≤ padicValRat 2 k) (ht : 0 ≤ padicValRat 2 t)
    (hu8 : residuePow 2 3 u hu=5) (ha8 : residuePow 2 3 a ha=3)
    (hk8 : residuePow 2 3 k hk=1)
    (heq : 8*t^2=u*((u+a)^2-8*k)) : False := by
  have hpadic : (8:ℤ_[2])*(integralRat 2 t ht)^2 =
      integralRat 2 u hu * ((integralRat 2 u hu+integralRat 2 a ha)^2-
        8*integralRat 2 k hk) := by
    apply PadicInt.coe_inj.mp
    simp only [PadicInt.coe_mul,PadicInt.coe_pow,PadicInt.coe_add,PadicInt.coe_sub,
      integralRat_coe, show ((8:ℤ_[2]):ℚ_[2])=8 by rfl]
    simpa only [Rat.cast_mul,Rat.cast_pow,Rat.cast_sub,Rat.cast_add,Rat.cast_ofNat]
      using congrArg (fun z : ℚ => (z : ℚ_[2])) heq
  have hmod := congrArg (PadicInt.toZModPow 6) hpadic
  simp only [map_mul,map_pow,map_add,map_sub,map_ofNat] at hmod
  exact original_five_mod_sixtyfour
    (residuePow 2 6 u hu) (residuePow 2 6 a ha) (residuePow 2 6 k hk)
    (residuePow 2 6 t ht)
    ((residuePow_cast 2 3 6 (by omega) hu).trans hu8)
    ((residuePow_cast 2 3 6 (by omega) ha).trans ha8)
    ((residuePow_cast 2 3 6 (by omega) hk).trans hk8) hmod

/-- Necessary rational exclusion of partner unit three at either
exceptional valuation, with all higher coefficient digits retained. -/
theorem rational_partner_three_obstruction {u a k t : ℚ}
    (hu : 0 ≤ padicValRat 2 u) (ha : 0 ≤ padicValRat 2 a)
    (hk : 0 ≤ padicValRat 2 k) (ht : 0 ≤ padicValRat 2 t)
    (hu8 : residuePow 2 3 u hu=3) (ha8 : residuePow 2 3 a ha=3)
    (hk8 : residuePow 2 3 k hk=1)
    (heq : 2*t^2=u*(u^2-a*u+2*k) ∨ 2*t^2=u*(2*u^2-a*u+k)) : False := by
  let U := integralRat 2 u hu
  let A := integralRat 2 a ha
  let K := integralRat 2 k hk
  let T := integralRat 2 t ht
  have hpadic : (2:ℤ_[2])*T^2=U*(U^2-A*U+2*K) ∨
      (2:ℤ_[2])*T^2=U*(2*U^2-A*U+K) := by
    rcases heq with heq | heq
    · left
      apply PadicInt.coe_inj.mp
      simp only [U,A,K,T,PadicInt.coe_mul,PadicInt.coe_pow,PadicInt.coe_add,
        PadicInt.coe_sub,integralRat_coe, show ((2:ℤ_[2]):ℚ_[2])=2 by rfl]
      simpa only [Rat.cast_mul,Rat.cast_pow,Rat.cast_sub,Rat.cast_add,Rat.cast_ofNat]
        using congrArg (fun z : ℚ => (z : ℚ_[2])) heq
    · right
      apply PadicInt.coe_inj.mp
      simp only [U,A,K,T,PadicInt.coe_mul,PadicInt.coe_pow,PadicInt.coe_add,
        PadicInt.coe_sub,integralRat_coe, show ((2:ℤ_[2]):ℚ_[2])=2 by rfl]
      simpa only [Rat.cast_mul,Rat.cast_pow,Rat.cast_sub,Rat.cast_add,Rat.cast_ofNat]
        using congrArg (fun z : ℚ => (z : ℚ_[2])) heq
  obtain ⟨hleft,hright⟩ := partner_three_rhs_mod_sixteen
    (residuePow 2 4 u hu) (residuePow 2 4 a ha) (residuePow 2 4 k hk)
    ((residuePow_cast 2 3 4 (by omega) hu).trans hu8)
    ((residuePow_cast 2 3 4 (by omega) ha).trans ha8)
    ((residuePow_cast 2 3 4 (by omega) hk).trans hk8)
  have hsquare := square_double_options_mod_sixteen (residuePow 2 4 t ht)
  rcases hpadic with hpadic | hpadic
  · have hmod := congrArg (PadicInt.toZModPow 4) hpadic
    simp only [map_mul,map_pow,map_add,map_sub,map_ofNat] at hmod
    change 2*(residuePow 2 4 t ht)^2 = (residuePow 2 4 u hu)*
      ((residuePow 2 4 u hu)^2 - (residuePow 2 4 a ha)*(residuePow 2 4 u hu)+
        2*(residuePow 2 4 k hk)) at hmod
    rcases hsquare with hs | hs | hs <;> rcases hleft with hl | hl <;>
      rw [hs,hl] at hmod <;> revert hmod <;> decide
  · have hmod := congrArg (PadicInt.toZModPow 4) hpadic
    simp only [map_mul,map_pow,map_add,map_sub,map_ofNat] at hmod
    change 2*(residuePow 2 4 t ht)^2 = (residuePow 2 4 u hu)*
      (2*(residuePow 2 4 u hu)^2 - (residuePow 2 4 a ha)*(residuePow 2 4 u hu)+
        (residuePow 2 4 k hk)) at hmod
    rcases hsquare with hs | hs | hs <;> rcases hright with hl | hl <;>
      rw [hs,hl] at hmod <;> revert hmod <;> decide

/-- Every bounded rational divided square equation has its exact prime-power
residue equation, with integer coefficients. -/
theorem divided_square_residuePow (k : ℕ) (d c a b : ℤ) {u t : ℚ}
    (hu : 0 ≤ padicValRat 2 u) (ht : 0 ≤ padicValRat 2 t)
    (heq : (d:ℚ)*t^2=(c:ℚ)*u^3+(a:ℚ)*u^2+(b:ℚ)*u) :
    (d:ZMod (2^k))*(residuePow 2 k t ht)^2=
      (c:ZMod (2^k))*(residuePow 2 k u hu)^3+
      (a:ZMod (2^k))*(residuePow 2 k u hu)^2+
      (b:ZMod (2^k))*residuePow 2 k u hu := by
  have hp : (d:ℤ_[2])*(integralRat 2 t ht)^2=
      (c:ℤ_[2])*(integralRat 2 u hu)^3+
      (a:ℤ_[2])*(integralRat 2 u hu)^2+
      (b:ℤ_[2])*integralRat 2 u hu := by
    apply PadicInt.coe_inj.mp
    simpa only [PadicInt.coe_mul,PadicInt.coe_pow,PadicInt.coe_add,
      PadicInt.coe_intCast,integralRat_coe,Rat.cast_mul,Rat.cast_pow,
      Rat.cast_add,Rat.cast_intCast] using
      congrArg (fun z : ℚ => (z : ℚ_[2])) heq
  have hm := congrArg (PadicInt.toZModPow k) hp
  simpa only [residuePow,map_mul,map_pow,map_add,map_intCast] using hm

theorem original_zero_mod_eight (u t : ZMod 8) (hu : IsUnit u)
    (heq : t^2=u^3+4*3*u^2+4*u) : u=1 := by
  revert u t
  decide +kernel

theorem original_two_mod_eight (u t : ZMod 8) (hu : IsUnit u)
    (heq : t^2=4*u^3+4*3*u^2+u) : u=1 := by
  revert u t
  decide +kernel

theorem partner_zero_mod_eight (u t : ZMod 8) (hu : IsUnit u)
    (heq : t^2=u^3-2*3*u^2) : u=7 := by
  revert u t
  decide +kernel

theorem partner_three_mod_eight (u t : ZMod 8) (hu : IsUnit u)
    (heq : t^2=8*u^3-2*3*u^2+u) : u=7 := by
  revert u t
  decide +kernel

theorem original_one_root_mod_eight (u : ZMod 8) (hu : IsUnit u)
    (heq : u*(u+3)^2=0) : u=1 ∨ u=5 := by
  revert u
  decide +kernel

theorem original_one_mod_sixtyfour (u a k t : ZMod 64)
    (hu : IsUnit (ZMod.cast u : ZMod 8))
    (ha : (ZMod.cast a : ZMod 8)=3) (hk : (ZMod.cast k : ZMod 8)=1)
    (heq : 8*t^2=u^3+2*a*u^2+(a^2-8*k)*u) :
    (ZMod.cast u : ZMod 8)=1 := by
  have he : 8*t^2=u*((u+a)^2-8*k) := by linear_combination heq
  have h8 := congrArg (ZMod.castHom (by decide : 8 ∣ 64) (ZMod 8)) he
  simp only [map_mul,map_pow,map_add,map_sub,map_ofNat] at h8
  change 8*(ZMod.cast t : ZMod 8)^2=
    (ZMod.cast u : ZMod 8)*(((ZMod.cast u : ZMod 8)+(ZMod.cast a : ZMod 8))^2-
      8*(ZMod.cast k : ZMod 8)) at h8
  rw [ha,hk] at h8
  have hroot : (ZMod.cast u : ZMod 8)*((ZMod.cast u : ZMod 8)+3)^2=0 := by
    simpa only [show (8:ZMod 8)=0 by decide,zero_mul,sub_zero] using h8.symm
  rcases original_one_root_mod_eight (ZMod.cast u) hu hroot with hh | hh
  · exact hh
  · exact False.elim (original_five_mod_sixtyfour u a k t hh ha hk he)

theorem partner_one_two_mod_sixteen (u a k t : ZMod 16)
    (hu : (ZMod.cast u : ZMod 8)=1 ∨ (ZMod.cast u : ZMod 8)=3 ∨
      (ZMod.cast u : ZMod 8)=5 ∨ (ZMod.cast u : ZMod 8)=7)
    (ha : (ZMod.cast a : ZMod 8)=3) (hk : (ZMod.cast k : ZMod 8)=1)
    (heq : 2*t^2=u^3-a*u^2+2*k*u ∨ 2*t^2=2*u^3-a*u^2+k*u) :
    (ZMod.cast u : ZMod 8)=1 ∨ (ZMod.cast u : ZMod 8)=7 := by
  revert u a k t
  decide +kernel

/-- Removing a sufficiently small even power from a rational square
preserves integrality, as read from its factored point equation. -/
theorem square_div_integral {y u B : ℚ} (n d s : ℕ)
    (hu : u ≠ 0) (hvu : padicValRat 2 u=0)
    (hB : B=0 ∨ (s:ℤ) ≤ padicValRat 2 B)
    (heq : y^2=(2:ℚ)^n*u*B) (hnd : 2*d ≤ n+s+1) :
    0 ≤ padicValRat 2 (y/(2:ℚ)^d) := by
  by_cases hy : y=0
  · simp [hy]
  have hB0 : B ≠ 0 := by intro hz; rw [hz,mul_zero] at heq; exact (pow_ne_zero 2 hy) heq
  have hvB := hB.resolve_left hB0
  have hp : (2:ℚ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hv := congrArg (padicValRat 2) heq
  rw [padicValRat.pow,padicValRat.mul (mul_ne_zero hp hu) hB0,
    padicValRat.mul hp hu,padicValRat.pow,
    show padicValRat 2 (2:ℚ)=1 from padicValRat.self (by norm_num),hvu] at hv
  rw [padicValRat.div hy (pow_ne_zero _ (by norm_num)),padicValRat.pow,
    show padicValRat 2 (2:ℚ)=1 from padicValRat.self (by norm_num)]
  omega


theorem integer_unit_valuation_zero (z : ℤ) (hz : IsUnit (z:ZMod 8)) :
    (z:ℚ) ≠ 0 ∧ padicValRat 2 (z:ℚ)=0 := by
  have hz2 := hz.map (ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2))
  simp only [map_intCast] at hz2
  have hnot : ¬ (2:ℤ) ∣ z := by
    intro hd
    exact hz2.ne_zero ((ZMod.intCast_zmod_eq_zero_iff_dvd z 2).mpr hd)
  refine ⟨?_,?_⟩
  · exact_mod_cast (show z ≠ 0 from fun hh => hnot (hh ▸ dvd_zero _))
  · rw [padicValRat.of_int,padicValInt.eq_zero_of_not_dvd hnot]
    rfl

theorem quadratic_integral (c a b : ℤ) {u : ℚ}
    (hu : 0 ≤ padicValRat 2 u) :
    0 ≤ padicValRat 2 ((c:ℚ)*u^2+(a:ℚ)*u+(b:ℚ)) := by
  apply LocalSeven.valuation_nonnegative_add 2
  · apply LocalSeven.valuation_nonnegative_add 2
    · apply LocalSeven.valuation_nonnegative_mul 2
      · rw [padicValRat.of_int]; positivity
      · rw [padicValRat.pow]; positivity
    · apply LocalSeven.valuation_nonnegative_mul 2
      · rw [padicValRat.of_int]; positivity
      · exact hu
  · rw [padicValRat.of_int]; positivity

theorem quadratic_residuePow (k : ℕ) (c a b : ℤ) {u : ℚ}
    (hu : 0 ≤ padicValRat 2 u) :
    residuePow 2 k ((c:ℚ)*u^2+(a:ℚ)*u+(b:ℚ)) (quadratic_integral c a b hu)=
      (c:ZMod (2^k))*(residuePow 2 k u hu)^2+
        (a:ZMod (2^k))*residuePow 2 k u hu+(b:ZMod (2^k)) := by
  have hp : integralRat 2 ((c:ℚ)*u^2+(a:ℚ)*u+(b:ℚ)) (quadratic_integral c a b hu)=
      (c:ℤ_[2])*(integralRat 2 u hu)^2+(a:ℤ_[2])*integralRat 2 u hu+(b:ℤ_[2]) := by
    apply PadicInt.coe_inj.mp
    simp only [integralRat_coe,PadicInt.coe_add,PadicInt.coe_mul,
      PadicInt.coe_pow,PadicInt.coe_intCast,Rat.cast_add,Rat.cast_mul,
      Rat.cast_pow,Rat.cast_intCast]
  have hm := congrArg (PadicInt.toZModPow k) hp
  simpa only [residuePow,map_add,map_mul,map_pow,map_intCast] using hm

theorem original_quadratic_mod_four (u : ZMod 4) (hu : IsUnit u) :
    u^2+2*3*u+1=0 := by
  revert u
  decide +kernel

theorem partner_quadratics_mod_two (u : ZMod 2) (hu : IsUnit u) :
    u^2-3*u+2*1=0 ∧ 2*u^2-3*u+1=0 := by
  revert u
  decide +kernel

theorem original_quadratic_valuation {u : ℚ} (hu : u ≠ 0)
    (hvu : padicValRat 2 u=0) (a b : ℤ)
    (ha : (a:ZMod 8)=3) (hb : (b:ZMod 8)=1) :
    u^2+2*(a:ℚ)*u+(b:ℚ)=0 ∨ 2 ≤ padicValRat 2 (u^2+2*(a:ℚ)*u+(b:ℚ)) := by
  have ha4 : (a:ZMod 4)=3 := by
    have hh := congrArg (ZMod.castHom (by decide : 4 ∣ 8) (ZMod 4)) ha
    simpa only [map_intCast,map_ofNat] using hh
  have hb4 : (b:ZMod 4)=1 := by
    have hh := congrArg (ZMod.castHom (by decide : 4 ∣ 8) (ZMod 4)) hb
    simpa only [map_intCast,map_one] using hh
  have hz := original_quadratic_mod_four (residuePow 2 2 u (by omega))
    (residuePow_isUnit 2 2 hu hvu)
  have hm := quadratic_residuePow 2 1 (2*a) b (u:=u) (by omega)
  simp only [Int.cast_one,one_mul,Int.cast_mul,Int.cast_ofNat,ha4,hb4] at hm
  have he : residuePow 2 2 (u^2+2*(a:ℚ)*u+(b:ℚ))
      (by simpa only [Int.cast_one,one_mul,Int.cast_mul,Int.cast_ofNat] using
        quadratic_integral 1 (2*a) b (u:=u) (by omega))=0 := by
    simpa only [Int.cast_one,one_mul,Int.cast_mul,Int.cast_ofNat] using hm.trans hz
  exact (residuePow_eq_zero_iff 2 2 _).mp he

theorem partner_quadratic_valuations {u : ℚ} (hu : u ≠ 0)
    (hvu : padicValRat 2 u=0) (a k : ℤ)
    (ha : (a:ZMod 8)=3) (hk : (k:ZMod 8)=1) :
    (u^2-(a:ℚ)*u+2*(k:ℚ)=0 ∨ 1 ≤ padicValRat 2 (u^2-(a:ℚ)*u+2*(k:ℚ))) ∧
    (2*u^2-(a:ℚ)*u+(k:ℚ)=0 ∨ 1 ≤ padicValRat 2 (2*u^2-(a:ℚ)*u+(k:ℚ))) := by
  have ha2 : (a:ZMod 2)=3 := by
    have hh := congrArg (ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2)) ha
    simpa only [map_intCast,map_ofNat] using hh
  have hk2 : (k:ZMod 2)=1 := by
    have hh := congrArg (ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2)) hk
    simpa only [map_intCast,map_one] using hh
  have ⟨hz1,hz2⟩ := partner_quadratics_mod_two (residuePow 2 1 u (by omega))
    (residuePow_isUnit 2 1 hu hvu)
  have hm1 := quadratic_residuePow 1 1 (-a) (2*k) (u:=u) (by omega)
  have hm2 := quadratic_residuePow 1 2 (-a) k (u:=u) (by omega)
  simp only [Int.cast_one,one_mul,Int.cast_neg,Int.cast_mul,Int.cast_ofNat,
    ha2,hk2,neg_mul,← sub_eq_add_neg] at hm1 hm2
  rw [hz1] at hm1
  rw [hz2] at hm2
  constructor
  · simpa only [Int.cast_one,one_mul,Int.cast_neg,Int.cast_mul,Int.cast_ofNat,
      neg_mul,← sub_eq_add_neg,Nat.cast_one] using (residuePow_eq_zero_iff 2 1 _).mp hm1
  · simpa only [Int.cast_neg,Int.cast_mul,Int.cast_ofNat,
      neg_mul,← sub_eq_add_neg,Nat.cast_one] using (residuePow_eq_zero_iff 2 1 _).mp hm2

end RankCertificates.Rank5TwoDescent
