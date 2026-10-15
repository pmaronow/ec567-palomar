module

public import RankCertificates.SquareClassSign
public import RankCertificates.SquareClassIndependence
public import RankCertificates.LocalDescent

/-!
Sign and all prime valuation parities completely determine a rational
squareclass. This is the global completeness step in prime-support descent.
-/

@[expose] public section

namespace RankCertificates

-- Keep subtraction and scalar multiplication on `ZMod 2` aligned with its
-- canonical ring structure, as in `SquareClassIndependence`.
local instance : AddCommGroup (ZMod 2) := (ZMod.commRing 2).toAddCommGroup

theorem rationalSquareClass_unit (u : ℚˣ) :
    rationalSquareClass (u : ℚ) = QuotientGroup.mk u := by
  rw [rationalSquareClass, dite_eq_right u.ne_zero]
  congr 1
  exact Units.ext rfl

/-- A squareclass with trivial sign and all prime parities is trivial. -/
theorem squareClass_eq_zero_of_sign_primeParity
    (c : Additive RationalSquareClasses) (hs : squareClassSign c = 0)
    (hp : ∀ p (h : p.Prime), primeParity p h c = 0) : c = 0 := by
  change c.toMul = 1
  change squareClassSign (Additive.ofMul c.toMul) = 0 at hs
  change ∀ p (h : p.Prime), primeParity p h (Additive.ofMul c.toMul) = 0 at hp
  generalize hq : c.toMul = q at hs hp ⊢
  induction q using QuotientGroup.induction_on with
  | H u =>
    have hu : rationalSquareClass (u : ℚ) = QuotientGroup.mk u := rationalSquareClass_unit u
    have hs' : (if (u : ℚ) < 0 then (1 : ZMod 2) else 0) = 0 := by
      simpa only [← hu, squareClassSign_apply u.ne_zero] using hs
    have hnonneg : 0 ≤ (u : ℚ) := by
      by_contra h
      have hneg : (u : ℚ) < 0 := lt_of_not_ge h
      simp [hneg] at hs'
    have heven : ∀ p : ℕ, p.Prime → Even (padicValRat p (u : ℚ)) := by
      intro p h
      have hzero : (padicValRat p (u : ℚ) : ZMod 2) = 0 := by
        simpa only [← hu, primeParity_apply h u.ne_zero] using hp p h
      exact even_iff_two_dvd.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero)
    obtain ⟨r, hr⟩ := Rat.isSquare_iff_even_factorization.mpr ⟨hnonneg, heven⟩
    rw [← hu]
    apply (rationalSquareClass_eq_one_iff u.ne_zero).mpr
    refine ⟨r, ?_, by simpa only [pow_two] using hr⟩
    intro hzero
    apply u.ne_zero
    simpa only [hzero, mul_zero] using hr

/-- Agreement of sign and every prime parity implies equality of squareclasses. -/
theorem squareClass_eq_of_sign_primeParity (c d : Additive RationalSquareClasses)
    (hs : squareClassSign c = squareClassSign d)
    (hp : ∀ p (h : p.Prime), primeParity p h c = primeParity p h d) : c = d := by
  apply sub_eq_zero.mp
  apply squareClass_eq_zero_of_sign_primeParity
  · rw [map_sub, hs, sub_self]
  · intro p h
    rw [map_sub, hp p h, sub_self]

/-- A single faithful family of coordinates for all rational squareclasses. -/
theorem squareClass_sign_primeParity_injective :
    Function.Injective (fun c : Additive RationalSquareClasses =>
      (squareClassSign c, fun p : {p : ℕ // p.Prime} => primeParity p.val p.property c)) := by
  intro c d h
  apply squareClass_eq_of_sign_primeParity c d (congrArg Prod.fst h)
  intro p hp
  exact congrFun (congrArg Prod.snd h) ⟨p, hp⟩

/-- Prime coordinates outside a signed prime basis vanish on its span. -/
theorem primeParity_signedPrimeLinearMap_of_not_mem {n : ℕ}
    (P : Fin n → ℕ) (hP : ∀ i, (P i).Prime) {p : ℕ} (hp : p.Prime)
    (hnot : p ∉ Set.range P) (v : Fin (n + 1) → ZMod 2) :
    primeParity p hp (squareClassLinearMap (signedPrimeColumns P) v) = 0 := by
  classical
  change (primeParity p hp).toZModLinearMap 2
    (squareClassLinearMap (signedPrimeColumns P) v) = 0
  simp only [squareClassLinearMap, Fintype.linearCombination_apply, Fin.sum_univ_succ]
  simp only [map_add, map_sum, map_smul, AddMonoidHom.coe_toZModLinearMap,
    signedPrimeColumns_zero, signedPrimeColumns_succ, primeParity_neg_one,
    smul_zero, zero_add]
  apply Finset.sum_eq_zero
  intro i _
  rw [primeParity_prime hp (hP i)]
  simp [show p ≠ P i from fun h => hnot ⟨i, h.symm⟩]

/-- Every rational squareclass supported on the displayed finite prime set
has a binary signed-prime expansion. -/
theorem squareClass_mem_signedPrime_range {n : ℕ} (P : Fin n → ℕ)
    (hP : ∀ i, (P i).Prime) (hinj : Function.Injective P)
    (c : Additive RationalSquareClasses)
    (houtside : ∀ p (hp : p.Prime), p ∉ Set.range P → primeParity p hp c = 0) :
    c ∈ (squareClassLinearMap (signedPrimeColumns P)).range := by
  let v : Fin (n + 1) → ZMod 2 :=
    Fin.cons (squareClassSign c) (fun i => primeParity (P i) (hP i) c)
  refine ⟨v, ?_⟩
  symm
  apply squareClass_eq_of_sign_primeParity
  · rw [sign_signedPrimeLinearMap P hP]
    rfl
  · intro p hp
    by_cases hmem : p ∈ Set.range P
    · obtain ⟨j, rfl⟩ := hmem
      rw [primeParity_signedPrimeLinearMap P hP hinj]
      rfl
    · rw [houtside p hp hmem, primeParity_signedPrimeLinearMap_of_not_mem P hP hp hmem]

theorem primeParity_zero_of_evenValuationClass {p : ℕ} (hp : p.Prime)
    (q : RationalSquareClasses) (he : LocalDescent.EvenValuationClass p q) :
    primeParity p hp (Additive.ofMul q) = 0 := by
  induction q using QuotientGroup.induction_on with
  | H u =>
    rw [← rationalSquareClass_unit u, primeParity_apply hp u.ne_zero]
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    exact even_iff_two_dvd.mp (he (u : ℚ) u.ne_zero (rationalSquareClass_unit u))

/-- The actual rational-point image lies in the finite ambient binary space
when every prime divisor of the integral linear coefficient is displayed. -/
theorem integral_twoIsogenyImage_mem_signedPrime_range {n : ℕ}
    (a b : ℤ) (P : Fin n → ℕ) (hP : ∀ i, (P i).Prime)
    (hinj : Function.Injective P)
    (hsupport : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ b → p ∈ Set.range P)
    {q : RationalSquareClasses} (hq : q ∈ twoIsogenyImage (a : ℚ) (b : ℚ)) :
    Additive.ofMul q ∈ (squareClassLinearMap (signedPrimeColumns P)).range := by
  apply squareClass_mem_signedPrime_range P hP hinj
  intro p hp hnot
  let : Fact p.Prime := ⟨hp⟩
  exact primeParity_zero_of_evenValuationClass hp q
    (LocalDescent.twoIsogenyImage_even_valuation a b
      (fun hd => hnot (hsupport p hp hd)) hq)

/-- The full signed-prime ambient space has the expected finite size. -/
theorem signedPrime_range_card {n : ℕ} (P : Fin n → ℕ)
    (hP : ∀ i, (P i).Prime) (hinj : Function.Injective P) :
    Nat.card ↥(squareClassLinearMap (signedPrimeColumns P)).range = 2 ^ (n + 1) := by
  rw [Nat.card_congr (LinearEquiv.ofInjective _
    (signedPrime_squareClassLinearMap_injective P hP hinj)).symm.toEquiv]
  simp [Nat.card_eq_fintype_card]

/-- A uniform upper bound on the actual descent image, obtained from global
prime support alone. Further local conditions shrink this ambient space. -/
theorem integral_twoIsogenyImage_card_le {n : ℕ}
    (a b : ℤ) (P : Fin n → ℕ) (hP : ∀ i, (P i).Prime)
    (hinj : Function.Injective P)
    (hsupport : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ b → p ∈ Set.range P) :
    Nat.card (twoIsogenyImage (a : ℚ) (b : ℚ)) ≤ 2 ^ (n + 1) := by
  let f := squareClassLinearMap (signedPrimeColumns P)
  let : Finite ↥f.range := Finite.of_surjective f.rangeRestrict f.surjective_rangeRestrict
  let embed : twoIsogenyImage (a : ℚ) (b : ℚ) → f.range := fun q =>
    ⟨Additive.ofMul q.val,
      integral_twoIsogenyImage_mem_signedPrime_range a b P hP hinj hsupport q.property⟩
  have hembed : Function.Injective embed := by
    intro q r h
    exact Subtype.ext (congrArg (fun v : f.range => v.val.toMul) h)
  exact (Nat.card_le_card_of_injective embed hembed).trans_eq
    (signedPrime_range_card P hP hinj)

end RankCertificates
