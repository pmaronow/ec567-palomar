module

public import RankCertificates.Rank5CharacterRows

@[expose] public section

namespace RankCertificates.Rank5LiteralRows

open Rank5CharacterEvaluation Rank5CharacterRows

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {x y : ℤ} (h : PrimeSpecialization5 x y)

theorem columnsE_nonzero (j : Fin 12) : columnsE h.primes j ≠ 0 := by
  have hn (i : Fin 12) : (h.primes i : ℚ) ≠ 0 := by exact_mod_cast (h.prime i).ne_zero
  fin_cases j <;> simp [columnsE, hn]

theorem columnsEp_nonzero (j : Fin 12) : columnsEp h.primes j ≠ 0 := by
  have hn (i : Fin 12) : (h.primes i : ℚ) ≠ 0 := by exact_mod_cast (h.prime i).ne_zero
  fin_cases j <;> simp [columnsEp, hn]

theorem columnsE_list : List.ofFn (columnsE h.primes) =
    Integration.columns5E (Integration.outputs5 x y) := by
  have hp : (fun i => (h.primes i : ℚ)) = Integration.outputs5 x y := by
    funext i
    exact (h.cast_eq i).symm
  rw [← hp]
  rfl

theorem columnsEp_list : List.ofFn (columnsEp h.primes) =
    Integration.columns5Ep (Integration.outputs5 x y) := by
  have hp : (fun i => (h.primes i : ℚ)) = Integration.outputs5 x y := by
    funext i
    exact (h.cast_eq i).symm
  rw [← hp]
  rfl

theorem b_squareclass : Additive.ofMul
    (rationalSquareClass (Rank5.b (Integration.M5 x) (Integration.N5 y))) =
    squareClassLinearMap (columnsE h.primes) (Binary.vector 12 4081) := by
  have ht := DescentWitnesses.witnesses5E_mask_classes x y 0
  have ht' : rationalSquareClass (Rank5.b (Integration.M5 x) (Integration.N5 y)) =
      rationalSquareClass (Integration.maskValue
        (Integration.columns5E (Integration.outputs5 x y)) 4081) := by
    simpa [DescentWitnesses.witnesses5E, Integration.codes5E] using ht
  rw [ht', ← columnsE_list h]
  exact squareClass_maskValue_ofFn _ (columnsE_nonzero h) _

theorem c_squareclass : Additive.ofMul
    (rationalSquareClass (Rank5.c (Integration.M5 x) (Integration.N5 y))) =
    squareClassLinearMap (columnsEp h.primes) (Binary.vector 12 4082) := by
  have ht := DescentWitnesses.witnesses5Ep_mask_classes x y 0
  have ht' : rationalSquareClass (Rank5.c (Integration.M5 x) (Integration.N5 y)) =
      rationalSquareClass (Integration.maskValue
        (Integration.columns5Ep (Integration.outputs5 x y)) 4082) := by
    simpa [DescentWitnesses.witnesses5Ep, Integration.codes5Ep] using ht
  rw [ht', ← columnsEp_list h]
  exact squareClass_maskValue_ofFn _ (columnsEp_nonzero h) _

def coefficientBitE (e : ℤ) (i : Fin 12) : ZMod 2 :=
  ∑ j, unitRowE e i j * Binary.vector 12 4081 j

def coefficientBitEp (e : ℤ) (i : Fin 12) : ZMod 2 :=
  ∑ j, unitRowEp e i j * Binary.vector 12 4082 j

theorem coefficientBitE_actual (i : Fin 12) (hi : i.val < 4) :
    @unitCharacterParity (h.primes i) ⟨h.prime i⟩ (Additive.ofMul
      (rationalSquareClass (Rank5.b (Integration.M5 x) (Integration.N5 y)))) =
    coefficientBitE (epsilon h) i := by
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  change unitCharacterLinear (h.primes i) _ = _
  rw [b_squareclass h, unitCharacterLinear_squareClassLinearMap,
    unitRowE_actual h i (Or.inl hi)]
  rfl

theorem coefficientBitEp_actual (i : Fin 12) (hi : i.val < 4) :
    @unitCharacterParity (h.primes i) ⟨h.prime i⟩ (Additive.ofMul
      (rationalSquareClass (Rank5.c (Integration.M5 x) (Integration.N5 y)))) =
    coefficientBitEp (epsilon h) i := by
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  change unitCharacterLinear (h.primes i) _ = _
  rw [c_squareclass h, unitCharacterLinear_squareClassLinearMap,
    unitRowEp_actual h i (by exact lt_trans hi (by decide))]
  rfl

def valuationRow (i : Fin 12) : Fin 12 → ZMod 2 :=
  fun j => if j.val = i.val + 4 then 1 else 0

theorem valuationRowE_actual (i : Fin 12) (hi : i.val < 4) :
    (fun j => primeParity (h.primes i) (h.prime i)
      (Additive.ofMul (rationalSquareClass (columnsE h.primes j)))) = valuationRow i := by
  dsimp [PrimeSpecialization5] at h
  funext j
  fin_cases j
  · change primeParity (h.primes i) (h.prime i)
      (Additive.ofMul (rationalSquareClass (-1))) = valuationRow i 0
    dsimp only [PositivePrimeOutputs.primes]
    rw [primeParity_neg_one]
    simp [valuationRow]
  · change primeParity (h.primes i) (h.prime i)
      (Additive.ofMul (rationalSquareClass (2 : ℚ))) = valuationRow i 1
    dsimp only [PositivePrimeOutputs.primes]
    have hv := primeParity_prime (h.prime i) (show Nat.Prime 2 by decide)
    norm_num only [Nat.cast_ofNat] at hv
    rw [ite_eq_right (h.outside i 2 (by simp))] at hv
    rw [hv]
    simp [valuationRow]
  · change primeParity (h.primes i) (h.prime i)
      (Additive.ofMul (rationalSquareClass (3 : ℚ))) = valuationRow i 2
    dsimp only [PositivePrimeOutputs.primes]
    have hv := primeParity_prime (h.prime i) (show Nat.Prime 3 by decide)
    norm_num only [Nat.cast_ofNat] at hv
    rw [ite_eq_right (h.outside i 3 (by simp))] at hv
    rw [hv]
    simp [valuationRow]
  · change primeParity (h.primes i) (h.prime i)
      (Additive.ofMul (rationalSquareClass (5 : ℚ))) = valuationRow i 3
    dsimp only [PositivePrimeOutputs.primes]
    have hv := primeParity_prime (h.prime i) (show Nat.Prime 5 by decide)
    norm_num only [Nat.cast_ofNat] at hv
    rw [ite_eq_right (h.outside i 5 (by simp))] at hv
    rw [hv]
    simp [valuationRow]
  · change primeParity (h.primes i) (h.prime i)
      (Additive.ofMul (rationalSquareClass (h.primes 0 : ℚ))) = valuationRow i 4
    dsimp only [PositivePrimeOutputs.primes]
    rw [primeParity_prime (h.prime i) (h.prime 0)]
    simp only [h.distinct.eq_iff]
    fin_cases i <;> simp at hi
    all_goals norm_num [valuationRow]
  · change primeParity (h.primes i) (h.prime i)
      (Additive.ofMul (rationalSquareClass (h.primes 1 : ℚ))) = valuationRow i 5
    dsimp only [PositivePrimeOutputs.primes]
    rw [primeParity_prime (h.prime i) (h.prime 1)]
    simp only [h.distinct.eq_iff]
    fin_cases i <;> simp at hi
    all_goals norm_num [valuationRow]
  · change primeParity (h.primes i) (h.prime i)
      (Additive.ofMul (rationalSquareClass (h.primes 2 : ℚ))) = valuationRow i 6
    dsimp only [PositivePrimeOutputs.primes]
    rw [primeParity_prime (h.prime i) (h.prime 2)]
    simp only [h.distinct.eq_iff]
    fin_cases i <;> simp at hi
    all_goals norm_num [valuationRow]
  · change primeParity (h.primes i) (h.prime i)
      (Additive.ofMul (rationalSquareClass (h.primes 3 : ℚ))) = valuationRow i 7
    dsimp only [PositivePrimeOutputs.primes]
    rw [primeParity_prime (h.prime i) (h.prime 3)]
    simp only [h.distinct.eq_iff]
    fin_cases i <;> simp at hi
    all_goals norm_num [valuationRow]
  · change primeParity (h.primes i) (h.prime i)
      (Additive.ofMul (rationalSquareClass (h.primes 4 : ℚ))) = valuationRow i 8
    dsimp only [PositivePrimeOutputs.primes]
    rw [primeParity_prime (h.prime i) (h.prime 4)]
    simp only [h.distinct.eq_iff]
    fin_cases i <;> simp at hi
    all_goals norm_num [valuationRow]
  · change primeParity (h.primes i) (h.prime i)
      (Additive.ofMul (rationalSquareClass (h.primes 5 : ℚ))) = valuationRow i 9
    dsimp only [PositivePrimeOutputs.primes]
    rw [primeParity_prime (h.prime i) (h.prime 5)]
    simp only [h.distinct.eq_iff]
    fin_cases i <;> simp at hi
    all_goals norm_num [valuationRow]
  · change primeParity (h.primes i) (h.prime i)
      (Additive.ofMul (rationalSquareClass (h.primes 6 : ℚ))) = valuationRow i 10
    dsimp only [PositivePrimeOutputs.primes]
    rw [primeParity_prime (h.prime i) (h.prime 6)]
    simp only [h.distinct.eq_iff]
    fin_cases i <;> simp at hi
    all_goals norm_num [valuationRow]
  · change primeParity (h.primes i) (h.prime i)
      (Additive.ofMul (rationalSquareClass (h.primes 7 : ℚ))) = valuationRow i 11
    dsimp only [PositivePrimeOutputs.primes]
    rw [primeParity_prime (h.prime i) (h.prime 7)]
    simp only [h.distinct.eq_iff]
    fin_cases i <;> simp at hi
    all_goals norm_num [valuationRow]
theorem valuationRowEp_actual (i : Fin 12) (hi : i.val < 4) :
    (fun j => primeParity (h.primes i) (h.prime i)
      (Additive.ofMul (rationalSquareClass (columnsEp h.primes j)))) = valuationRow i := by
  dsimp [PrimeSpecialization5] at h
  funext j
  fin_cases j
  · change primeParity (h.primes i) (h.prime i)
      (Additive.ofMul (rationalSquareClass (-1))) = valuationRow i 0
    dsimp only [PositivePrimeOutputs.primes]
    rw [primeParity_neg_one]
    simp [valuationRow]
  · change primeParity (h.primes i) (h.prime i)
      (Additive.ofMul (rationalSquareClass (2 : ℚ))) = valuationRow i 1
    dsimp only [PositivePrimeOutputs.primes]
    have hv := primeParity_prime (h.prime i) (show Nat.Prime 2 by decide)
    norm_num only [Nat.cast_ofNat] at hv
    rw [ite_eq_right (h.outside i 2 (by simp))] at hv
    rw [hv]
    simp [valuationRow]
  · change primeParity (h.primes i) (h.prime i)
      (Additive.ofMul (rationalSquareClass (3 : ℚ))) = valuationRow i 2
    dsimp only [PositivePrimeOutputs.primes]
    have hv := primeParity_prime (h.prime i) (show Nat.Prime 3 by decide)
    norm_num only [Nat.cast_ofNat] at hv
    rw [ite_eq_right (h.outside i 3 (by simp))] at hv
    rw [hv]
    simp [valuationRow]
  · change primeParity (h.primes i) (h.prime i)
      (Additive.ofMul (rationalSquareClass (5 : ℚ))) = valuationRow i 3
    dsimp only [PositivePrimeOutputs.primes]
    have hv := primeParity_prime (h.prime i) (show Nat.Prime 5 by decide)
    norm_num only [Nat.cast_ofNat] at hv
    rw [ite_eq_right (h.outside i 5 (by simp))] at hv
    rw [hv]
    simp [valuationRow]
  · change primeParity (h.primes i) (h.prime i)
      (Additive.ofMul (rationalSquareClass (h.primes 0 : ℚ))) = valuationRow i 4
    dsimp only [PositivePrimeOutputs.primes]
    rw [primeParity_prime (h.prime i) (h.prime 0)]
    simp only [h.distinct.eq_iff]
    fin_cases i <;> simp at hi
    all_goals norm_num [valuationRow]
  · change primeParity (h.primes i) (h.prime i)
      (Additive.ofMul (rationalSquareClass (h.primes 1 : ℚ))) = valuationRow i 5
    dsimp only [PositivePrimeOutputs.primes]
    rw [primeParity_prime (h.prime i) (h.prime 1)]
    simp only [h.distinct.eq_iff]
    fin_cases i <;> simp at hi
    all_goals norm_num [valuationRow]
  · change primeParity (h.primes i) (h.prime i)
      (Additive.ofMul (rationalSquareClass (h.primes 2 : ℚ))) = valuationRow i 6
    dsimp only [PositivePrimeOutputs.primes]
    rw [primeParity_prime (h.prime i) (h.prime 2)]
    simp only [h.distinct.eq_iff]
    fin_cases i <;> simp at hi
    all_goals norm_num [valuationRow]
  · change primeParity (h.primes i) (h.prime i)
      (Additive.ofMul (rationalSquareClass (h.primes 3 : ℚ))) = valuationRow i 7
    dsimp only [PositivePrimeOutputs.primes]
    rw [primeParity_prime (h.prime i) (h.prime 3)]
    simp only [h.distinct.eq_iff]
    fin_cases i <;> simp at hi
    all_goals norm_num [valuationRow]
  · change primeParity (h.primes i) (h.prime i)
      (Additive.ofMul (rationalSquareClass (h.primes 8 : ℚ))) = valuationRow i 8
    dsimp only [PositivePrimeOutputs.primes]
    rw [primeParity_prime (h.prime i) (h.prime 8)]
    simp only [h.distinct.eq_iff]
    fin_cases i <;> simp at hi
    all_goals norm_num [valuationRow]
  · change primeParity (h.primes i) (h.prime i)
      (Additive.ofMul (rationalSquareClass (h.primes 9 : ℚ))) = valuationRow i 9
    dsimp only [PositivePrimeOutputs.primes]
    rw [primeParity_prime (h.prime i) (h.prime 9)]
    simp only [h.distinct.eq_iff]
    fin_cases i <;> simp at hi
    all_goals norm_num [valuationRow]
  · change primeParity (h.primes i) (h.prime i)
      (Additive.ofMul (rationalSquareClass (h.primes 10 : ℚ))) = valuationRow i 10
    dsimp only [PositivePrimeOutputs.primes]
    rw [primeParity_prime (h.prime i) (h.prime 10)]
    simp only [h.distinct.eq_iff]
    fin_cases i <;> simp at hi
    all_goals norm_num [valuationRow]
  · change primeParity (h.primes i) (h.prime i)
      (Additive.ofMul (rationalSquareClass (h.primes 11 : ℚ))) = valuationRow i 11
    dsimp only [PositivePrimeOutputs.primes]
    rw [primeParity_prime (h.prime i) (h.prime 11)]
    simp only [h.distinct.eq_iff]
    fin_cases i <;> simp at hi
    all_goals norm_num [valuationRow]
def movingRowE (e : ℤ) (i : Fin 12) : Fin 12 → ZMod 2 :=
  if i.val < 4 then unitRowE e i + coefficientBitE e i • valuationRow i else unitRowE e i

def movingRowEp (e : ℤ) (i : Fin 12) : Fin 12 → ZMod 2 :=
  if i.val < 4 then unitRowEp e i + coefficientBitEp e i • valuationRow i else unitRowEp e i

theorem typeIIIRowE_actual (i : Fin 12) (hi : i.val < 4) :
    @squareClassCharacterRow 12 (@typeIIICharacterLinear (h.primes i) ⟨h.prime i⟩
      (Rank5.b (Integration.M5 x) (Integration.N5 y))) (columnsE h.primes) =
      movingRowE (epsilon h) i := by
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  have hu := congrFun (unitRowE_actual h i (Or.inl hi))
  have hv := congrFun (valuationRowE_actual h i hi)
  funext j
  simp only [squareClassCharacterRow, typeIIICharacterLinear, LinearMap.add_apply,
    LinearMap.smul_apply, AddMonoidHom.coe_toZModLinearMap, unitCharacterLinear,
    movingRowE, ite_eq_left hi, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [coefficientBitE_actual h i hi, hv j]
  change unitCharacterRow (h.primes i) (columnsE h.primes) j + _ = _
  rw [hu j]

theorem typeIIIRowEp_actual (i : Fin 12) (hi : i.val < 4) :
    @squareClassCharacterRow 12 (@typeIIICharacterLinear (h.primes i) ⟨h.prime i⟩
      (Rank5.c (Integration.M5 x) (Integration.N5 y))) (columnsEp h.primes) =
      movingRowEp (epsilon h) i := by
  let : Fact (h.primes i).Prime := ⟨h.prime i⟩
  have hu := congrFun (unitRowEp_actual h i (by exact lt_trans hi (by decide)))
  have hv := congrFun (valuationRowEp_actual h i hi)
  funext j
  simp only [squareClassCharacterRow, typeIIICharacterLinear, LinearMap.add_apply,
    LinearMap.smul_apply, AddMonoidHom.coe_toZModLinearMap, unitCharacterLinear,
    movingRowEp, ite_eq_left hi, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [coefficientBitEp_actual h i hi, hv j]
  change unitCharacterRow (h.primes i) (columnsEp h.primes) j + _ = _
  rw [hu j]

end RankCertificates.Rank5LiteralRows
