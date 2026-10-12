module

public import RankCertificates.TwoIsogenyRank
public import RankCertificates.PrimeSpecializations

/-!
The actual isogeny formula and witnessed, independent prime squareclasses
give genuine Mordell–Weil rank lower bounds on the concrete specializations.
Exactness additionally requires the local descent upper bounds.
-/

@[expose] public section

namespace RankCertificates

theorem rank_lowerBound_of_twoIsogeny_images (a b : ℚ) (r d d' : ℕ)
    [(twoTorsionModel a b).IsElliptic]
    (hE : 2 ^ d ≤ Nat.card (twoIsogenyImage a b))
    (hEp : 2 ^ d' ≤ Nat.card (twoIsogenyImage (-2 * a) (a ^ 2 - 4 * b)))
    (hd : r + 2 = d + d') :
    r ≤ Module.finrank ℤ (twoTorsionModel a b).toAffine.Point := by
  have hi := (twoIsogenyRankIdentity_of_isElliptic a b).cardinalityFormula
  have hb := Nat.mul_le_mul hE hEp
  rw [← pow_add, ← hd, ← hi] at hb
  have hp : 2 ^ (r + 2) ≤
      2 ^ (Module.finrank ℤ (twoTorsionModel a b).toAffine.Point + 2) := by
    simpa only [pow_add, show (2 : ℕ) ^ 2 = 4 from rfl] using hb
  have he := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hp
  omega

/-- A concrete distinct-prime specialization has actual Mordell–Weil rank at least 5. -/
theorem PrimeSpecialization5.rank_lowerBound {x y : ℤ}
    (h : PrimeSpecialization5 x y) :
    5 ≤ Module.finrank ℤ (Rank5.E (Integration.M5 x) (Integration.N5 y)).toAffine.Point := by
  let : (twoTorsionModel (Rank5.a (Integration.M5 x) (Integration.N5 y))
      (Rank5.b (Integration.M5 x) (Integration.N5 y))).IsElliptic :=
    DescentWitnesses.elliptic5E_on_lattice x y
  have hEp := h.actualImageEp_card_lowerBound
  rw [← Rank5.isogeny_coefficient (Integration.M5 x) (Integration.N5 y)] at hEp
  exact rank_lowerBound_of_twoIsogeny_images _ _ 5 3 4
    h.actualImageE_card_lowerBound hEp (by decide)

/-- A concrete distinct-prime specialization has actual Mordell–Weil rank at least 6. -/
theorem PrimeSpecialization6.rank_lowerBound {x y : ℤ}
    (h : PrimeSpecialization6 x y) :
    6 ≤ Module.finrank ℤ (Rank6.E (Integration.M6 x) (Integration.N6 y)).toAffine.Point := by
  let : (twoTorsionModel (Rank6.a (Integration.M6 x) (Integration.N6 y))
      (Rank6.b (Integration.M6 x) (Integration.N6 y))).IsElliptic :=
    DescentWitnesses.elliptic6E_on_lattice x y
  have hEp := h.actualImageEp_card_lowerBound
  rw [← Rank6.isogeny_coefficient_identity (Integration.M6 x) (Integration.N6 y)] at hEp
  exact rank_lowerBound_of_twoIsogeny_images _ _ 6 4 4
    h.actualImageE_card_lowerBound hEp (by decide)

/-- A concrete distinct-prime specialization has actual Mordell–Weil rank at least 7. -/
theorem PrimeSpecialization7.rank_lowerBound {x y : ℤ}
    (h : PrimeSpecialization7 x y) :
    7 ≤ Module.finrank ℤ (Rank7.E (Integration.M7 x) (Integration.N7 y)).toAffine.Point := by
  let : (twoTorsionModel (Rank7.a (Integration.M7 x) (Integration.N7 y))
      (Rank7.b (Integration.M7 x) (Integration.N7 y))).IsElliptic :=
    DescentWitnesses.elliptic7E_on_lattice x y
  have hEp := h.actualImageEp_card_lowerBound
  rw [← Rank7.discriminant_coefficient (Integration.M7 x) (Integration.N7 y)] at hEp
  exact rank_lowerBound_of_twoIsogeny_images _ _ 7 5 4
    h.actualImageE_card_lowerBound hEp (by decide)

end RankCertificates
