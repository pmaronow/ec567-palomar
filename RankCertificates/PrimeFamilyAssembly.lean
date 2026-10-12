module

public import RankCertificates.PrimeSpecializations
public import RankCertificates.PrimeDirections
public import RankCertificates.Normalization
public import RankCertificates.Geometric
public import RankCertificates.TwoIsogenyRank

/-!
Passage from the literal integer prime specializations to geometric infinitude.
The analytic infinitude and sharp image cardinalities remain explicit inputs;
projective injectivity, rank transport and geometric nonconstancy are proved.
-/

@[expose] public section

namespace RankCertificates.PrimeFamilyAssembly

open Integration

/-- Two distinct prime coordinates determine the homogeneous direction. -/
theorem prime_coordinates_of_direction {M N M' N' k α β : ℚ}
    {p q p' q' : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp' : p'.Prime) (hq' : q'.Prime) (hpq : p ≠ q)
    (hk : k ≠ 0) (hβ : β ≠ 0) (hN : N ≠ 0) (hN' : N' ≠ 0)
    (hM : M = k * p) (hM' : M' = k * p')
    (hn : N = α * p + β * q) (hn' : N' = α * p' + β * q')
    (hr : M / N = M' / N') : p = p' ∧ q = q' := by
  have hcross := (div_eq_div_iff hN hN').mp hr
  rw [hM, hM', hn, hn'] at hcross
  have hz : k * β * ((p : ℚ) * q' - (p' : ℚ) * q) = 0 := by
    linear_combination hcross
  have he : (p : ℚ) * q' = (p' : ℚ) * q :=
    sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (mul_ne_zero hk hβ))
  apply PrimeDirections.prime_pair_eq_of_cross_mul_eq hp hq hp' hq' hpq
  exact_mod_cast he

def directions5 (v : ℤ × ℤ) : ℚ := M5 v.1 / N5 v.2

theorem denominator5_nonzero (y : ℤ) : N5 y ≠ 0 := by
  intro hz
  change (((-1 : ℤ) + 19984345920 * y : ℤ) : ℚ) = 0 at hz
  have he : (-1 : ℤ) + 19984345920 * y = 0 := by
    exact_mod_cast hz
  have hm := congrArg (fun z : ℤ => z % 2) he
  norm_num [Int.add_emod, Int.mul_emod] at hm

theorem prime_coordinates5 {x y : ℤ} (h : PrimeSpecialization5 x y) :
    M5 x = 54 * (h.primes 0 : ℚ) ∧
    N5 y = 1188 * (h.primes 0 : ℚ) + (-1) * (h.primes 1 : ℚ) := by
  have h0 := normalization5 x y 0
  have h1 := normalization5 x y 1
  rw [show outputs5 x y 0 = (h.primes 0 : ℚ) from h.cast_eq 0] at h0
  rw [show outputs5 x y 1 = (h.primes 1 : ℚ) from h.cast_eq 1] at h1
  norm_num [forms5, PrimePatterns.Rank5.cofactors, Rank5.L0, Rank5.L1] at h0 h1
  constructor <;> linarith

theorem directions5_injOn : Set.InjOn directions5
    {v : ℤ × ℤ | PrimeSpecialization5 v.1 v.2} := by
  rintro ⟨x, y⟩ h ⟨x', y'⟩ h' hr
  change PrimeSpecialization5 x y at h
  change PrimeSpecialization5 x' y' at h'
  obtain ⟨hM, hN⟩ := prime_coordinates5 h
  obtain ⟨hM', hN'⟩ := prime_coordinates5 h'
  have hpq : h.primes 0 ≠ h.primes 1 := fun he => by
    have := h.distinct he
    norm_num at this
  obtain ⟨hp, hq⟩ := prime_coordinates_of_direction
    (h.prime 0) (h.prime 1) (h'.prime 0) (h'.prime 1) hpq
    (by norm_num : (54 : ℚ) ≠ 0) (by norm_num : (-1 : ℚ) ≠ 0)
    (denominator5_nonzero y) (denominator5_nonzero y') hM hM' hN hN' hr
  change h.primes 0 = h'.primes 0 at hp
  change h.primes 1 = h'.primes 1 at hq
  have hMx : M5 x = M5 x' := by rw [hM, hM', hp]
  have hNy : N5 y = N5 y' := by rw [hN, hN', hp, hq]
  have hx : x = x' := by
    dsimp [M5] at hMx
    norm_num [PrimePatterns.Rank5.M0, PrimePatterns.Rank5.W] at hMx
    exact hMx
  have hy : y = y' := by
    dsimp [N5] at hNy
    norm_num [PrimePatterns.Rank5.N0, PrimePatterns.Rank5.W] at hNy
    exact hNy
  exact Prod.ext hx hy

def directions6 (v : ℤ × ℤ) : ℚ := M6 v.1 / N6 v.2

theorem denominator6_nonzero (y : ℤ) : N6 y ≠ 0 := by
  have h := forms6_nonzero_on_lattice 0 y 1
  simpa [forms6, Rank6.L1] using h

theorem prime_coordinates6 {x y : ℤ} (h : PrimeSpecialization6 x y) :
    M6 x = 1 * (h.primes 0 : ℚ) ∧
    N6 y = 0 * (h.primes 0 : ℚ) + (1) * (h.primes 1 : ℚ) := by
  have h0 := normalization6 x y 0
  have h1 := normalization6 x y 1
  rw [show outputs6 x y 0 = (h.primes 0 : ℚ) from h.cast_eq 0] at h0
  rw [show outputs6 x y 1 = (h.primes 1 : ℚ) from h.cast_eq 1] at h1
  norm_num [forms6, PrimePatterns.Rank6.cofactors, Rank6.L0, Rank6.L1] at h0 h1
  constructor <;> linarith

theorem directions6_injOn : Set.InjOn directions6
    {v : ℤ × ℤ | PrimeSpecialization6 v.1 v.2} := by
  rintro ⟨x, y⟩ h ⟨x', y'⟩ h' hr
  change PrimeSpecialization6 x y at h
  change PrimeSpecialization6 x' y' at h'
  obtain ⟨hM, hN⟩ := prime_coordinates6 h
  obtain ⟨hM', hN'⟩ := prime_coordinates6 h'
  have hpq : h.primes 0 ≠ h.primes 1 := fun he => by
    have := h.distinct he
    norm_num at this
  obtain ⟨hp, hq⟩ := prime_coordinates_of_direction
    (h.prime 0) (h.prime 1) (h'.prime 0) (h'.prime 1) hpq
    (by norm_num : (1 : ℚ) ≠ 0) (by norm_num : (1 : ℚ) ≠ 0)
    (denominator6_nonzero y) (denominator6_nonzero y') hM hM' hN hN' hr
  change h.primes 0 = h'.primes 0 at hp
  change h.primes 1 = h'.primes 1 at hq
  have hMx : M6 x = M6 x' := by rw [hM, hM', hp]
  have hNy : N6 y = N6 y' := by rw [hN, hN', hp, hq]
  have hx : x = x' := by
    dsimp [M6] at hMx
    norm_num [PrimePatterns.Rank6.M0, PrimePatterns.Rank6.W] at hMx
    exact hMx
  have hy : y = y' := by
    dsimp [N6] at hNy
    norm_num [PrimePatterns.Rank6.N0, PrimePatterns.Rank6.W] at hNy
    exact hNy
  exact Prod.ext hx hy

def directions7 (v : ℤ × ℤ) : ℚ := M7 v.1 / N7 v.2

theorem denominator7_nonzero (y : ℤ) : N7 y ≠ 0 := by
  have h := forms7_nonzero_on_lattice 0 y 1
  simpa [forms7, Rank7.L1] using h

theorem prime_coordinates7 {x y : ℤ} (h : PrimeSpecialization7 x y) :
    M7 x = 18 * (h.primes 0 : ℚ) ∧
    N7 y = 0 * (h.primes 0 : ℚ) + (1) * (h.primes 1 : ℚ) := by
  have h0 := normalization7 x y 0
  have h1 := normalization7 x y 1
  rw [show outputs7 x y 0 = (h.primes 0 : ℚ) from h.cast_eq 0] at h0
  rw [show outputs7 x y 1 = (h.primes 1 : ℚ) from h.cast_eq 1] at h1
  norm_num [forms7, PrimePatterns.Rank7.cofactors, Rank7.L0, Rank7.L1] at h0 h1
  constructor <;> linarith

theorem directions7_injOn : Set.InjOn directions7
    {v : ℤ × ℤ | PrimeSpecialization7 v.1 v.2} := by
  rintro ⟨x, y⟩ h ⟨x', y'⟩ h' hr
  change PrimeSpecialization7 x y at h
  change PrimeSpecialization7 x' y' at h'
  obtain ⟨hM, hN⟩ := prime_coordinates7 h
  obtain ⟨hM', hN'⟩ := prime_coordinates7 h'
  have hpq : h.primes 0 ≠ h.primes 1 := fun he => by
    have := h.distinct he
    norm_num at this
  obtain ⟨hp, hq⟩ := prime_coordinates_of_direction
    (h.prime 0) (h.prime 1) (h'.prime 0) (h'.prime 1) hpq
    (by norm_num : (18 : ℚ) ≠ 0) (by norm_num : (1 : ℚ) ≠ 0)
    (denominator7_nonzero y) (denominator7_nonzero y') hM hM' hN hN' hr
  change h.primes 0 = h'.primes 0 at hp
  change h.primes 1 = h'.primes 1 at hq
  have hMx : M7 x = M7 x' := by rw [hM, hM', hp]
  have hNy : N7 y = N7 y' := by rw [hN, hN', hp, hq]
  have hx : x = x' := by
    dsimp [M7] at hMx
    norm_num [PrimePatterns.Rank7.M0, PrimePatterns.Rank7.W] at hMx
    exact hMx
  have hy : y = y' := by
    dsimp [N7] at hNy
    norm_num [PrimePatterns.Rank7.N0, PrimePatterns.Rank7.W] at hNy
    exact hNy
  exact Prod.ext hx hy


/-- The normalized lattice parameter is regular on every integer pair. -/
theorem normalized5_regular (x y : ℤ) :
    Geometric.denominator5.eval (directions5 (x, y)) ≠ 0 := by
  let : (Rank5.E (M5 x) (N5 y)).IsElliptic :=
    DescentWitnesses.elliptic5E_on_lattice x y
  let : (Rank5.E (directions5 (x, y)) 1).IsElliptic :=
    Normalization.normalized5_isElliptic _ _ (denominator5_nonzero y)
  have hΔ : (Rank5.E (directions5 (x, y)) 1).Δ ≠ 0 :=
    isUnit_iff_ne_zero.mp (Rank5.E (directions5 (x, y)) 1).isUnit_Δ
  rw [Rank5.E, model_discriminant] at hΔ
  rw [Geometric.denominator5_eval]
  intro hz
  apply hΔ
  have hm : 16 * (Rank5.b (directions5 (x, y)) 1 ^ 2 *
      (Rank5.a (directions5 (x, y)) 1 ^ 2 - 4 * Rank5.b (directions5 (x, y)) 1)) = 0 := by
    rw [hz, mul_zero]
  simpa only [mul_assoc] using hm

/-- Exact actual-image cardinalities and infinitely many literal prime pairs
suffice for geometric infinitude; projective and rank transfer are proved. -/
theorem rank5_infinitude_of_prime_specializations (S : Set (ℤ × ℤ))
    (hS : S.Infinite)
    (hprime : ∀ v ∈ S, PrimeSpecialization5 v.1 v.2)
    (himages : ∀ v ∈ S, ActualImageCardinalities
      (Rank5.a (M5 v.1) (N5 v.2)) (Rank5.b (M5 v.1) (N5 v.2)) 3 4) :
    InfinitelyManyExactRank 5 := by
  have hdirections : (directions5 '' S).Infinite :=
    hS.image (directions5_injOn.mono (fun v hv => hprime v hv))
  have hregular : ∀ t ∈ directions5 '' S, Geometric.denominator5.eval t ≠ 0 := by
    rintro t ⟨⟨x, y⟩, _, rfl⟩
    exact normalized5_regular x y
  apply (Geometric.geometric_image5_infinite _ hdirections hregular).mono
  rintro j ⟨t, ⟨⟨x, y⟩, hv, rfl⟩, rfl⟩
  let : (Rank5.E (M5 x) (N5 y)).IsElliptic :=
    DescentWitnesses.elliptic5E_on_lattice x y
  let : (twoTorsionModel (Rank5.a (M5 x) (N5 y))
      (Rank5.b (M5 x) (N5 y))).IsElliptic :=
    DescentWitnesses.elliptic5E_on_lattice x y
  let : (Rank5.E (directions5 (x, y)) 1).IsElliptic :=
    Normalization.normalized5_isElliptic _ _ (denominator5_nonzero y)
  let E : RationalEllipticCurve := ⟨Rank5.E (directions5 (x, y)) 1, inferInstance⟩
  refine ⟨E, ?_, ?_⟩
  · exact WeierstrassCurve.j_eq _
  · apply (Normalization.normalized5_exactRank_iff _ _ (denominator5_nonzero y) 5).mpr
    exact hasExactRank_of_twoIsogeny_image_cardinalities _ _ 5 3 4
      (himages (x, y) hv) (by decide)


/-- The normalized lattice parameter is regular on every integer pair. -/
theorem normalized6_regular (x y : ℤ) :
    Geometric.denominator6.eval (directions6 (x, y)) ≠ 0 := by
  let : (Rank6.E (M6 x) (N6 y)).IsElliptic :=
    DescentWitnesses.elliptic6E_on_lattice x y
  let : (Rank6.E (directions6 (x, y)) 1).IsElliptic :=
    Normalization.normalized6_isElliptic _ _ (denominator6_nonzero y)
  have hΔ : (Rank6.E (directions6 (x, y)) 1).Δ ≠ 0 :=
    isUnit_iff_ne_zero.mp (Rank6.E (directions6 (x, y)) 1).isUnit_Δ
  rw [Rank6.E, model_discriminant] at hΔ
  rw [Geometric.denominator6_eval]
  intro hz
  apply hΔ
  have hm : 16 * (Rank6.b (directions6 (x, y)) 1 ^ 2 *
      (Rank6.a (directions6 (x, y)) 1 ^ 2 - 4 * Rank6.b (directions6 (x, y)) 1)) = 0 := by
    rw [hz, mul_zero]
  simpa only [mul_assoc] using hm

/-- Exact actual-image cardinalities and infinitely many literal prime pairs
suffice for geometric infinitude; projective and rank transfer are proved. -/
theorem rank6_infinitude_of_prime_specializations (S : Set (ℤ × ℤ))
    (hS : S.Infinite)
    (hprime : ∀ v ∈ S, PrimeSpecialization6 v.1 v.2)
    (himages : ∀ v ∈ S, ActualImageCardinalities
      (Rank6.a (M6 v.1) (N6 v.2)) (Rank6.b (M6 v.1) (N6 v.2)) 4 4) :
    InfinitelyManyExactRank 6 := by
  have hdirections : (directions6 '' S).Infinite :=
    hS.image (directions6_injOn.mono (fun v hv => hprime v hv))
  have hregular : ∀ t ∈ directions6 '' S, Geometric.denominator6.eval t ≠ 0 := by
    rintro t ⟨⟨x, y⟩, _, rfl⟩
    exact normalized6_regular x y
  apply (Geometric.geometric_image6_infinite _ hdirections hregular).mono
  rintro j ⟨t, ⟨⟨x, y⟩, hv, rfl⟩, rfl⟩
  let : (Rank6.E (M6 x) (N6 y)).IsElliptic :=
    DescentWitnesses.elliptic6E_on_lattice x y
  let : (twoTorsionModel (Rank6.a (M6 x) (N6 y))
      (Rank6.b (M6 x) (N6 y))).IsElliptic :=
    DescentWitnesses.elliptic6E_on_lattice x y
  let : (Rank6.E (directions6 (x, y)) 1).IsElliptic :=
    Normalization.normalized6_isElliptic _ _ (denominator6_nonzero y)
  let E : RationalEllipticCurve := ⟨Rank6.E (directions6 (x, y)) 1, inferInstance⟩
  refine ⟨E, ?_, ?_⟩
  · exact WeierstrassCurve.j_eq _
  · apply (Normalization.normalized6_exactRank_iff _ _ (denominator6_nonzero y) 6).mpr
    exact hasExactRank_of_twoIsogeny_image_cardinalities _ _ 6 4 4
      (himages (x, y) hv) (by decide)


/-- The normalized lattice parameter is regular on every integer pair. -/
theorem normalized7_regular (x y : ℤ) :
    Geometric.denominator7.eval (directions7 (x, y)) ≠ 0 := by
  let : (Rank7.E (M7 x) (N7 y)).IsElliptic :=
    DescentWitnesses.elliptic7E_on_lattice x y
  let : (Rank7.E (directions7 (x, y)) 1).IsElliptic :=
    Normalization.normalized7_isElliptic _ _ (denominator7_nonzero y)
  have hΔ : (Rank7.E (directions7 (x, y)) 1).Δ ≠ 0 :=
    isUnit_iff_ne_zero.mp (Rank7.E (directions7 (x, y)) 1).isUnit_Δ
  rw [Rank7.E, model_discriminant] at hΔ
  rw [Geometric.denominator7_eval]
  intro hz
  apply hΔ
  have hm : 16 * (Rank7.b (directions7 (x, y)) 1 ^ 2 *
      (Rank7.a (directions7 (x, y)) 1 ^ 2 - 4 * Rank7.b (directions7 (x, y)) 1)) = 0 := by
    rw [hz, mul_zero]
  simpa only [mul_assoc] using hm

/-- Exact actual-image cardinalities and infinitely many literal prime pairs
suffice for geometric infinitude; projective and rank transfer are proved. -/
theorem rank7_infinitude_of_prime_specializations (S : Set (ℤ × ℤ))
    (hS : S.Infinite)
    (hprime : ∀ v ∈ S, PrimeSpecialization7 v.1 v.2)
    (himages : ∀ v ∈ S, ActualImageCardinalities
      (Rank7.a (M7 v.1) (N7 v.2)) (Rank7.b (M7 v.1) (N7 v.2)) 5 4) :
    InfinitelyManyExactRank 7 := by
  have hdirections : (directions7 '' S).Infinite :=
    hS.image (directions7_injOn.mono (fun v hv => hprime v hv))
  have hregular : ∀ t ∈ directions7 '' S, Geometric.denominator7.eval t ≠ 0 := by
    rintro t ⟨⟨x, y⟩, _, rfl⟩
    exact normalized7_regular x y
  apply (Geometric.geometric_image7_infinite _ hdirections hregular).mono
  rintro j ⟨t, ⟨⟨x, y⟩, hv, rfl⟩, rfl⟩
  let : (Rank7.E (M7 x) (N7 y)).IsElliptic :=
    DescentWitnesses.elliptic7E_on_lattice x y
  let : (twoTorsionModel (Rank7.a (M7 x) (N7 y))
      (Rank7.b (M7 x) (N7 y))).IsElliptic :=
    DescentWitnesses.elliptic7E_on_lattice x y
  let : (Rank7.E (directions7 (x, y)) 1).IsElliptic :=
    Normalization.normalized7_isElliptic _ _ (denominator7_nonzero y)
  let E : RationalEllipticCurve := ⟨Rank7.E (directions7 (x, y)) 1, inferInstance⟩
  refine ⟨E, ?_, ?_⟩
  · exact WeierstrassCurve.j_eq _
  · apply (Normalization.normalized7_exactRank_iff _ _ (denominator7_nonzero y) 7).mpr
    exact hasExactRank_of_twoIsogeny_image_cardinalities _ _ 7 5 4
      (himages (x, y) hv) (by decide)


/-- Matching upper bounds suffice, since the known independent point classes
already give the lower bounds. -/
theorem rank5_infinitude_of_prime_specialization_upper_bounds (S : Set (ℤ × ℤ))
    (hS : S.Infinite)
    (hprime : ∀ v ∈ S, PrimeSpecialization5 v.1 v.2)
    (hE : ∀ v ∈ S, Nat.card (twoIsogenyImage
      (Rank5.a (M5 v.1) (N5 v.2)) (Rank5.b (M5 v.1) (N5 v.2))) ≤ 2 ^ 3)
    (hEp : ∀ v ∈ S, Nat.card (twoIsogenyImage
      (-2 * Rank5.a (M5 v.1) (N5 v.2)) (Rank5.c (M5 v.1) (N5 v.2))) ≤ 2 ^ 4) :
    InfinitelyManyExactRank 5 := by
  apply rank5_infinitude_of_prime_specializations S hS hprime
  intro v hv
  have h := hprime v hv
  constructor
  · exact Nat.le_antisymm (hE v hv) h.actualImageE_card_lowerBound
  · rw [Rank5.isogeny_coefficient]
    exact Nat.le_antisymm (hEp v hv) h.actualImageEp_card_lowerBound


/-- Matching upper bounds suffice, since the known independent point classes
already give the lower bounds. -/
theorem rank6_infinitude_of_prime_specialization_upper_bounds (S : Set (ℤ × ℤ))
    (hS : S.Infinite)
    (hprime : ∀ v ∈ S, PrimeSpecialization6 v.1 v.2)
    (hE : ∀ v ∈ S, Nat.card (twoIsogenyImage
      (Rank6.a (M6 v.1) (N6 v.2)) (Rank6.b (M6 v.1) (N6 v.2))) ≤ 2 ^ 4)
    (hEp : ∀ v ∈ S, Nat.card (twoIsogenyImage
      (-2 * Rank6.a (M6 v.1) (N6 v.2)) (Rank6.c (M6 v.1) (N6 v.2))) ≤ 2 ^ 4) :
    InfinitelyManyExactRank 6 := by
  apply rank6_infinitude_of_prime_specializations S hS hprime
  intro v hv
  have h := hprime v hv
  constructor
  · exact Nat.le_antisymm (hE v hv) h.actualImageE_card_lowerBound
  · rw [Rank6.isogeny_coefficient_identity]
    exact Nat.le_antisymm (hEp v hv) h.actualImageEp_card_lowerBound


/-- Matching upper bounds suffice, since the known independent point classes
already give the lower bounds. -/
theorem rank7_infinitude_of_prime_specialization_upper_bounds (S : Set (ℤ × ℤ))
    (hS : S.Infinite)
    (hprime : ∀ v ∈ S, PrimeSpecialization7 v.1 v.2)
    (hE : ∀ v ∈ S, Nat.card (twoIsogenyImage
      (Rank7.a (M7 v.1) (N7 v.2)) (Rank7.b (M7 v.1) (N7 v.2))) ≤ 2 ^ 5)
    (hEp : ∀ v ∈ S, Nat.card (twoIsogenyImage
      (-2 * Rank7.a (M7 v.1) (N7 v.2)) (Rank7.c (M7 v.1) (N7 v.2))) ≤ 2 ^ 4) :
    InfinitelyManyExactRank 7 := by
  apply rank7_infinitude_of_prime_specializations S hS hprime
  intro v hv
  have h := hprime v hv
  constructor
  · exact Nat.le_antisymm (hE v hv) h.actualImageE_card_lowerBound
  · rw [Rank7.discriminant_coefficient]
    exact Nat.le_antisymm (hEp v hv) h.actualImageEp_card_lowerBound

end RankCertificates.PrimeFamilyAssembly
