module

public import RankCertificates.SquareClassImageFinite

/-!
# Concrete positive prime specializations

The hypotheses here concern the twelve literal integer outputs of the CRT
lattice. They assert no existence or infinitude. Under these hypotheses,
the archived masks generate the certified numbers of actual point classes.
-/

@[expose] public section

namespace RankCertificates

/-- Twelve distinct positive prime values, avoiding the fixed small prime
columns used in the family. -/
structure PositivePrimeOutputs (outputs : Fin 12 → ℤ) (smallPrimes : List ℕ) : Prop where
  positive : ∀ i, 0 < outputs i
  prime : ∀ i, (outputs i).natAbs.Prime
  distinct : Function.Injective (fun i => (outputs i).natAbs)
  outside : ∀ i p, p ∈ smallPrimes → (outputs i).natAbs ≠ p

namespace PositivePrimeOutputs

/-- The natural prime represented by a positive integer output. -/
def primes {outputs : Fin 12 → ℤ} {smallPrimes : List ℕ}
    (_h : PositivePrimeOutputs outputs smallPrimes) : Fin 12 → ℕ :=
  fun i => (outputs i).natAbs

theorem cast_eq {outputs : Fin 12 → ℤ} {smallPrimes : List ℕ}
    (h : PositivePrimeOutputs outputs smallPrimes) (i : Fin 12) :
    (outputs i : ℚ) = (h.primes i : ℚ) := by
  have hi : ((outputs i).natAbs : ℤ) = outputs i := by
    rw [Int.natCast_natAbs, abs_of_pos (h.positive i)]
  change (outputs i : ℚ) = ((outputs i).natAbs : ℚ)
  simpa only [Int.cast_natCast] using
    (congrArg (fun z : ℤ => (z : ℚ)) hi).symm

theorem outputs_injective {outputs : Fin 12 → ℤ} {smallPrimes : List ℕ}
    (h : PositivePrimeOutputs outputs smallPrimes) : Function.Injective outputs := by
  intro i j hij
  exact h.distinct (congrArg Int.natAbs hij)

end PositivePrimeOutputs

/-- The final rank-5 lattice specializes to twelve positive distinct primes
outside its small-prime columns. -/
def PrimeSpecialization5 (x y : ℤ) : Prop :=
  PositivePrimeOutputs (fun i => (PrimePatterns.Rank5.outputs i).eval x y) [2, 3, 5]

/-- The rank-6 lattice specializes to twelve positive distinct primes. -/
def PrimeSpecialization6 (x y : ℤ) : Prop :=
  PositivePrimeOutputs (fun i => (PrimePatterns.Rank6.outputs i).eval x y) [2, 3, 7]

/-- The rank-7 lattice specializes to twelve positive distinct primes. -/
def PrimeSpecialization7 (x y : ℤ) : Prop :=
  PositivePrimeOutputs (fun i => (PrimePatterns.Rank7.outputs i).eval x y) [2, 3, 7, 13]

/-- Ordered original-curve prime columns, without the sign column. -/
def primeColumns5E (p : Fin 12 → ℕ) : Fin 11 → ℕ :=
  ![2, 3, 5, p 0, p 1, p 2, p 3, p 4, p 5, p 6, p 7]

def primeColumns5Ep (p : Fin 12 → ℕ) : Fin 11 → ℕ :=
  ![2, 3, 5, p 0, p 1, p 2, p 3, p 8, p 9, p 10, p 11]

def primeColumns6E (p : Fin 12 → ℕ) : Fin 11 → ℕ :=
  ![2, 3, 7, p 0, p 1, p 2, p 3, p 4, p 5, p 6, p 7]

def primeColumns6Ep (p : Fin 12 → ℕ) : Fin 11 → ℕ :=
  ![2, 3, 7, p 0, p 1, p 2, p 3, p 8, p 9, p 10, p 11]

def primeColumns7E (p : Fin 12 → ℕ) : Fin 12 → ℕ :=
  ![2, 3, 7, 13, p 0, p 1, p 2, p 3, p 4, p 5, p 6, p 7]

def primeColumns7Ep (p : Fin 12 → ℕ) : Fin 12 → ℕ :=
  ![2, 3, 7, 13, p 0, p 1, p 2, p 3, p 8, p 9, p 10, p 11]

theorem primeColumns5E_prime {outputs : Fin 12 → ℤ}
    (h : PositivePrimeOutputs outputs [2, 3, 5]) (i : Fin 11) :
    (primeColumns5E h.primes i).Prime := by
  fin_cases i <;> norm_num [primeColumns5E, PositivePrimeOutputs.primes, h.prime]

/-- The ordered prime columns are distinct when the twelve outputs are
pairwise distinct and avoid the fixed prime columns. -/
theorem primeColumns5E_injective {outputs : Fin 12 → ℤ}
    (h : PositivePrimeOutputs outputs [2, 3, 5]) :
    Function.Injective (primeColumns5E h.primes) := by
  have hpair (i j : Fin 12) : h.primes i = h.primes j ↔ i = j := h.distinct.eq_iff
  have hs2 (i : Fin 12) : h.primes i ≠ 2 := h.outside i 2 (by simp)
  have hs2' (i : Fin 12) : 2 ≠ h.primes i := (hs2 i).symm
  have hs3 (i : Fin 12) : h.primes i ≠ 3 := h.outside i 3 (by simp)
  have hs3' (i : Fin 12) : 3 ≠ h.primes i := (hs3 i).symm
  have hs5 (i : Fin 12) : h.primes i ≠ 5 := h.outside i 5 (by simp)
  have hs5' (i : Fin 12) : 5 ≠ h.primes i := (hs5 i).symm
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [primeColumns5E, hpair, hs2, hs2', hs3, hs3', hs5, hs5'] at hij ⊢

theorem primeColumns5E_columns_eq (p : Fin 12 → ℕ) :
    List.ofFn (signedPrimeColumns (primeColumns5E p)) =
      Integration.columns5E (fun i => (p i : ℚ)) := by
  rfl

/-- The concrete integer prime specialization discharges the squareclass
column condition used by the known-point cardinality theorem. -/
theorem PrimeSpecialization5.columnsE {x y : ℤ}
    (h : PrimeSpecialization5 x y) :
    IsSignedPrimeColumnList (n := 11)
      (Integration.columns5E (Integration.outputs5 x y)) := by
  refine ⟨primeColumns5E h.primes, primeColumns5E_prime h,
    primeColumns5E_injective h, ?_⟩
  rw [primeColumns5E_columns_eq]
  congr 1
  funext i
  exact h.cast_eq i

theorem primeColumns5Ep_prime {outputs : Fin 12 → ℤ}
    (h : PositivePrimeOutputs outputs [2, 3, 5]) (i : Fin 11) :
    (primeColumns5Ep h.primes i).Prime := by
  fin_cases i <;> norm_num [primeColumns5Ep, PositivePrimeOutputs.primes, h.prime]

/-- The ordered prime columns are distinct when the twelve outputs are
pairwise distinct and avoid the fixed prime columns. -/
theorem primeColumns5Ep_injective {outputs : Fin 12 → ℤ}
    (h : PositivePrimeOutputs outputs [2, 3, 5]) :
    Function.Injective (primeColumns5Ep h.primes) := by
  have hpair (i j : Fin 12) : h.primes i = h.primes j ↔ i = j := h.distinct.eq_iff
  have hs2 (i : Fin 12) : h.primes i ≠ 2 := h.outside i 2 (by simp)
  have hs2' (i : Fin 12) : 2 ≠ h.primes i := (hs2 i).symm
  have hs3 (i : Fin 12) : h.primes i ≠ 3 := h.outside i 3 (by simp)
  have hs3' (i : Fin 12) : 3 ≠ h.primes i := (hs3 i).symm
  have hs5 (i : Fin 12) : h.primes i ≠ 5 := h.outside i 5 (by simp)
  have hs5' (i : Fin 12) : 5 ≠ h.primes i := (hs5 i).symm
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [primeColumns5Ep, hpair, hs2, hs2', hs3, hs3', hs5, hs5'] at hij ⊢

theorem primeColumns5Ep_columns_eq (p : Fin 12 → ℕ) :
    List.ofFn (signedPrimeColumns (primeColumns5Ep p)) =
      Integration.columns5Ep (fun i => (p i : ℚ)) := by
  rfl

/-- The concrete integer prime specialization discharges the squareclass
column condition used by the known-point cardinality theorem. -/
theorem PrimeSpecialization5.columnsEp {x y : ℤ}
    (h : PrimeSpecialization5 x y) :
    IsSignedPrimeColumnList (n := 11)
      (Integration.columns5Ep (Integration.outputs5 x y)) := by
  refine ⟨primeColumns5Ep h.primes, primeColumns5Ep_prime h,
    primeColumns5Ep_injective h, ?_⟩
  rw [primeColumns5Ep_columns_eq]
  congr 1
  funext i
  exact h.cast_eq i

theorem primeColumns6E_prime {outputs : Fin 12 → ℤ}
    (h : PositivePrimeOutputs outputs [2, 3, 7]) (i : Fin 11) :
    (primeColumns6E h.primes i).Prime := by
  fin_cases i <;> norm_num [primeColumns6E, PositivePrimeOutputs.primes, h.prime]

/-- The ordered prime columns are distinct when the twelve outputs are
pairwise distinct and avoid the fixed prime columns. -/
theorem primeColumns6E_injective {outputs : Fin 12 → ℤ}
    (h : PositivePrimeOutputs outputs [2, 3, 7]) :
    Function.Injective (primeColumns6E h.primes) := by
  have hpair (i j : Fin 12) : h.primes i = h.primes j ↔ i = j := h.distinct.eq_iff
  have hs2 (i : Fin 12) : h.primes i ≠ 2 := h.outside i 2 (by simp)
  have hs2' (i : Fin 12) : 2 ≠ h.primes i := (hs2 i).symm
  have hs3 (i : Fin 12) : h.primes i ≠ 3 := h.outside i 3 (by simp)
  have hs3' (i : Fin 12) : 3 ≠ h.primes i := (hs3 i).symm
  have hs7 (i : Fin 12) : h.primes i ≠ 7 := h.outside i 7 (by simp)
  have hs7' (i : Fin 12) : 7 ≠ h.primes i := (hs7 i).symm
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [primeColumns6E, hpair, hs2, hs2', hs3, hs3', hs7, hs7'] at hij ⊢

theorem primeColumns6E_columns_eq (p : Fin 12 → ℕ) :
    List.ofFn (signedPrimeColumns (primeColumns6E p)) =
      Integration.columns6E (fun i => (p i : ℚ)) := by
  rfl

/-- The concrete integer prime specialization discharges the squareclass
column condition used by the known-point cardinality theorem. -/
theorem PrimeSpecialization6.columnsE {x y : ℤ}
    (h : PrimeSpecialization6 x y) :
    IsSignedPrimeColumnList (n := 11)
      (Integration.columns6E (Integration.outputs6 x y)) := by
  refine ⟨primeColumns6E h.primes, primeColumns6E_prime h,
    primeColumns6E_injective h, ?_⟩
  rw [primeColumns6E_columns_eq]
  congr 1
  funext i
  exact h.cast_eq i

theorem primeColumns6Ep_prime {outputs : Fin 12 → ℤ}
    (h : PositivePrimeOutputs outputs [2, 3, 7]) (i : Fin 11) :
    (primeColumns6Ep h.primes i).Prime := by
  fin_cases i <;> norm_num [primeColumns6Ep, PositivePrimeOutputs.primes, h.prime]

/-- The ordered prime columns are distinct when the twelve outputs are
pairwise distinct and avoid the fixed prime columns. -/
theorem primeColumns6Ep_injective {outputs : Fin 12 → ℤ}
    (h : PositivePrimeOutputs outputs [2, 3, 7]) :
    Function.Injective (primeColumns6Ep h.primes) := by
  have hpair (i j : Fin 12) : h.primes i = h.primes j ↔ i = j := h.distinct.eq_iff
  have hs2 (i : Fin 12) : h.primes i ≠ 2 := h.outside i 2 (by simp)
  have hs2' (i : Fin 12) : 2 ≠ h.primes i := (hs2 i).symm
  have hs3 (i : Fin 12) : h.primes i ≠ 3 := h.outside i 3 (by simp)
  have hs3' (i : Fin 12) : 3 ≠ h.primes i := (hs3 i).symm
  have hs7 (i : Fin 12) : h.primes i ≠ 7 := h.outside i 7 (by simp)
  have hs7' (i : Fin 12) : 7 ≠ h.primes i := (hs7 i).symm
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [primeColumns6Ep, hpair, hs2, hs2', hs3, hs3', hs7, hs7'] at hij ⊢

theorem primeColumns6Ep_columns_eq (p : Fin 12 → ℕ) :
    List.ofFn (signedPrimeColumns (primeColumns6Ep p)) =
      Integration.columns6Ep (fun i => (p i : ℚ)) := by
  rfl

/-- The concrete integer prime specialization discharges the squareclass
column condition used by the known-point cardinality theorem. -/
theorem PrimeSpecialization6.columnsEp {x y : ℤ}
    (h : PrimeSpecialization6 x y) :
    IsSignedPrimeColumnList (n := 11)
      (Integration.columns6Ep (Integration.outputs6 x y)) := by
  refine ⟨primeColumns6Ep h.primes, primeColumns6Ep_prime h,
    primeColumns6Ep_injective h, ?_⟩
  rw [primeColumns6Ep_columns_eq]
  congr 1
  funext i
  exact h.cast_eq i

theorem primeColumns7E_prime {outputs : Fin 12 → ℤ}
    (h : PositivePrimeOutputs outputs [2, 3, 7, 13]) (i : Fin 12) :
    (primeColumns7E h.primes i).Prime := by
  fin_cases i <;> norm_num [primeColumns7E, PositivePrimeOutputs.primes, h.prime]

/-- The ordered prime columns are distinct when the twelve outputs are
pairwise distinct and avoid the fixed prime columns. -/
theorem primeColumns7E_injective {outputs : Fin 12 → ℤ}
    (h : PositivePrimeOutputs outputs [2, 3, 7, 13]) :
    Function.Injective (primeColumns7E h.primes) := by
  have hpair (i j : Fin 12) : h.primes i = h.primes j ↔ i = j := h.distinct.eq_iff
  have hs2 (i : Fin 12) : h.primes i ≠ 2 := h.outside i 2 (by simp)
  have hs2' (i : Fin 12) : 2 ≠ h.primes i := (hs2 i).symm
  have hs3 (i : Fin 12) : h.primes i ≠ 3 := h.outside i 3 (by simp)
  have hs3' (i : Fin 12) : 3 ≠ h.primes i := (hs3 i).symm
  have hs7 (i : Fin 12) : h.primes i ≠ 7 := h.outside i 7 (by simp)
  have hs7' (i : Fin 12) : 7 ≠ h.primes i := (hs7 i).symm
  have hs13 (i : Fin 12) : h.primes i ≠ 13 := h.outside i 13 (by simp)
  have hs13' (i : Fin 12) : 13 ≠ h.primes i := (hs13 i).symm
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [primeColumns7E, hpair, hs2, hs2', hs3, hs3', hs7, hs7', hs13, hs13'] at hij ⊢

theorem primeColumns7E_columns_eq (p : Fin 12 → ℕ) :
    List.ofFn (signedPrimeColumns (primeColumns7E p)) =
      Integration.columns7E (fun i => (p i : ℚ)) := by
  rfl

/-- The concrete integer prime specialization discharges the squareclass
column condition used by the known-point cardinality theorem. -/
theorem PrimeSpecialization7.columnsE {x y : ℤ}
    (h : PrimeSpecialization7 x y) :
    IsSignedPrimeColumnList (n := 12)
      (Integration.columns7E (Integration.outputs7 x y)) := by
  refine ⟨primeColumns7E h.primes, primeColumns7E_prime h,
    primeColumns7E_injective h, ?_⟩
  rw [primeColumns7E_columns_eq]
  congr 1
  funext i
  exact h.cast_eq i

theorem primeColumns7Ep_prime {outputs : Fin 12 → ℤ}
    (h : PositivePrimeOutputs outputs [2, 3, 7, 13]) (i : Fin 12) :
    (primeColumns7Ep h.primes i).Prime := by
  fin_cases i <;> norm_num [primeColumns7Ep, PositivePrimeOutputs.primes, h.prime]

/-- The ordered prime columns are distinct when the twelve outputs are
pairwise distinct and avoid the fixed prime columns. -/
theorem primeColumns7Ep_injective {outputs : Fin 12 → ℤ}
    (h : PositivePrimeOutputs outputs [2, 3, 7, 13]) :
    Function.Injective (primeColumns7Ep h.primes) := by
  have hpair (i j : Fin 12) : h.primes i = h.primes j ↔ i = j := h.distinct.eq_iff
  have hs2 (i : Fin 12) : h.primes i ≠ 2 := h.outside i 2 (by simp)
  have hs2' (i : Fin 12) : 2 ≠ h.primes i := (hs2 i).symm
  have hs3 (i : Fin 12) : h.primes i ≠ 3 := h.outside i 3 (by simp)
  have hs3' (i : Fin 12) : 3 ≠ h.primes i := (hs3 i).symm
  have hs7 (i : Fin 12) : h.primes i ≠ 7 := h.outside i 7 (by simp)
  have hs7' (i : Fin 12) : 7 ≠ h.primes i := (hs7 i).symm
  have hs13 (i : Fin 12) : h.primes i ≠ 13 := h.outside i 13 (by simp)
  have hs13' (i : Fin 12) : 13 ≠ h.primes i := (hs13 i).symm
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [primeColumns7Ep, hpair, hs2, hs2', hs3, hs3', hs7, hs7', hs13, hs13'] at hij ⊢

theorem primeColumns7Ep_columns_eq (p : Fin 12 → ℕ) :
    List.ofFn (signedPrimeColumns (primeColumns7Ep p)) =
      Integration.columns7Ep (fun i => (p i : ℚ)) := by
  rfl

/-- The concrete integer prime specialization discharges the squareclass
column condition used by the known-point cardinality theorem. -/
theorem PrimeSpecialization7.columnsEp {x y : ℤ}
    (h : PrimeSpecialization7 x y) :
    IsSignedPrimeColumnList (n := 12)
      (Integration.columns7Ep (Integration.outputs7 x y)) := by
  refine ⟨primeColumns7Ep h.primes, primeColumns7Ep_prime h,
    primeColumns7Ep_injective h, ?_⟩
  rw [primeColumns7Ep_columns_eq]
  congr 1
  funext i
  exact h.cast_eq i

/-- A concrete positive prime specialization gives the certified lower
bound on the actual rank-5 E Kummer image. -/
theorem PrimeSpecialization5.actualImageE_card_lowerBound {x y : ℤ}
    (h : PrimeSpecialization5 x y) :
    2 ^ 3 ≤ Nat.card (twoIsogenyImage (Rank5.a (Integration.M5 x) (Integration.N5 y)) (Rank5.b (Integration.M5 x) (Integration.N5 y))) :=
  actualImage5E_card_lowerBound x y h.columnsE

/-- A concrete positive prime specialization gives the certified lower
bound on the actual rank-5 Ep Kummer image. -/
theorem PrimeSpecialization5.actualImageEp_card_lowerBound {x y : ℤ}
    (h : PrimeSpecialization5 x y) :
    2 ^ 4 ≤ Nat.card (twoIsogenyImage ((-2 * Rank5.a (Integration.M5 x) (Integration.N5 y))) (Rank5.c (Integration.M5 x) (Integration.N5 y))) :=
  actualImage5Ep_card_lowerBound x y h.columnsEp

/-- A concrete positive prime specialization gives the certified lower
bound on the actual rank-6 E Kummer image. -/
theorem PrimeSpecialization6.actualImageE_card_lowerBound {x y : ℤ}
    (h : PrimeSpecialization6 x y) :
    2 ^ 4 ≤ Nat.card (twoIsogenyImage (Rank6.a (Integration.M6 x) (Integration.N6 y)) (Rank6.b (Integration.M6 x) (Integration.N6 y))) :=
  actualImage6E_card_lowerBound x y h.columnsE

/-- A concrete positive prime specialization gives the certified lower
bound on the actual rank-6 Ep Kummer image. -/
theorem PrimeSpecialization6.actualImageEp_card_lowerBound {x y : ℤ}
    (h : PrimeSpecialization6 x y) :
    2 ^ 4 ≤ Nat.card (twoIsogenyImage ((-2 * Rank6.a (Integration.M6 x) (Integration.N6 y))) (Rank6.c (Integration.M6 x) (Integration.N6 y))) :=
  actualImage6Ep_card_lowerBound x y h.columnsEp

/-- A concrete positive prime specialization gives the certified lower
bound on the actual rank-7 E Kummer image. -/
theorem PrimeSpecialization7.actualImageE_card_lowerBound {x y : ℤ}
    (h : PrimeSpecialization7 x y) :
    2 ^ 5 ≤ Nat.card (twoIsogenyImage (Rank7.a (Integration.M7 x) (Integration.N7 y)) (Rank7.b (Integration.M7 x) (Integration.N7 y))) :=
  actualImage7E_card_lowerBound x y h.columnsE

/-- A concrete positive prime specialization gives the certified lower
bound on the actual rank-7 Ep Kummer image. -/
theorem PrimeSpecialization7.actualImageEp_card_lowerBound {x y : ℤ}
    (h : PrimeSpecialization7 x y) :
    2 ^ 4 ≤ Nat.card (twoIsogenyImage ((-2 * Rank7.a (Integration.M7 x) (Integration.N7 y))) (Rank7.c (Integration.M7 x) (Integration.N7 y))) :=
  actualImage7Ep_card_lowerBound x y h.columnsEp

end RankCertificates
