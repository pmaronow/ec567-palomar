module

public import RankCertificates.SquareClassSign
public import RankCertificates.DescentWitnesses
public import RankCertificates.MatrixCertificates
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Prime squareclasses and binary certificates

Prime valuation parity detects each coordinate in a finite family of distinct
positive primes. The resulting injective linear map transfers binary matrix
independence to genuine rational squareclasses.
-/

@[expose] public section

namespace RankCertificates

-- `Mathlib.GroupTheory.Nilpotent` also derives an additive commutative group
-- structure on `ZMod 2` via simplicity. Use the ring's canonical additive
-- structure so its self-module and function-module instances agree with the
-- linear maps below.
local instance : AddCommGroup (ZMod 2) := (ZMod.commRing 2).toAddCommGroup

/-- Every rational squareclass has exponent dividing two. -/
theorem rationalSquareClasses_pow_two (x : RationalSquareClasses) : x ^ 2 = 1 := by
  refine QuotientGroup.induction_on x fun u => ?_
  rw [← QuotientGroup.mk_pow]
  exact (QuotientGroup.eq_one_iff _).mpr ⟨u, rfl⟩

/-- Rational squareclasses form a vector space over the binary field. -/
noncomputable instance rationalSquareClassesModule :
    Module (ZMod 2) (Additive RationalSquareClasses) :=
  AddCommGroup.zmodModule (fun x => by
    change x.toMul ^ 2 = 1
    exact rationalSquareClasses_pow_two x.toMul)

/-- The linear combination of the squareclasses of a finite family of
rational columns. The zero convention for `rationalSquareClass` is inherited;
all arithmetic independence results below require nonzero columns. -/
noncomputable def squareClassLinearMap {n : ℕ} (columns : Fin n → ℚ) :
    (Fin n → ZMod 2) →ₗ[ZMod 2] Additive RationalSquareClasses :=
  Fintype.linearCombination (ZMod 2)
    (fun i => Additive.ofMul (rationalSquareClass (columns i)))

/-- Prime valuation parity recovers one coefficient of a linear combination
of the squareclasses of distinct primes. -/
theorem primeParity_squareClassLinearMap {n : ℕ} (P : Fin n → ℕ)
    (hP : ∀ i, (P i).Prime) (hinj : Function.Injective P)
    (v : Fin n → ZMod 2) (j : Fin n) :
    primeParity (P j) (hP j) (squareClassLinearMap (fun i => (P i : ℚ)) v) = v j := by
  classical
  change (primeParity (P j) (hP j)).toZModLinearMap 2
      (squareClassLinearMap (fun i => (P i : ℚ)) v) = v j
  simp only [squareClassLinearMap, Fintype.linearCombination_apply,
    map_sum, map_smul, AddMonoidHom.coe_toZModLinearMap]
  rw [Finset.sum_eq_single j]
  · rw [primeParity_prime (hP j) (hP j)]
    simp
  · intro i _ hij
    rw [primeParity_prime (hP j) (hP i)]
    simp [show P j ≠ P i from fun h => hij (hinj h).symm]
  · simp

/-- Distinct positive prime squareclasses give an injective binary linear map. -/
theorem prime_squareClassLinearMap_injective {n : ℕ} (P : Fin n → ℕ)
    (hP : ∀ i, (P i).Prime) (hinj : Function.Injective P) :
    Function.Injective (squareClassLinearMap (fun i => (P i : ℚ))) := by
  intro v w h
  funext j
  have := congrArg (primeParity (P j) (hP j)) h
  simpa only [primeParity_squareClassLinearMap P hP hinj] using this

/-- The squareclasses of distinct positive primes are linearly independent
in the actual rational squareclass vector space. -/
theorem prime_squareclasses_linearIndependent {n : ℕ} (P : Fin n → ℕ)
    (hP : ∀ i, (P i).Prime) (hinj : Function.Injective P) :
    LinearIndependent (ZMod 2)
      (fun i => Additive.ofMul (rationalSquareClass (P i : ℚ))) :=
  linearIndependent_iff_injective_fintypeLinearCombination.mpr
    (prime_squareClassLinearMap_injective P hP hinj)

/-- The column list used in descent starts with the negative sign and then
contains positive primes. -/
def signedPrimeColumns {n : ℕ} (P : Fin n → ℕ) : Fin (n + 1) → ℚ :=
  Fin.cons (-1) (fun i => (P i : ℚ))

@[simp] theorem signedPrimeColumns_zero {n : ℕ} (P : Fin n → ℕ) :
    signedPrimeColumns P 0 = -1 := rfl

@[simp] theorem signedPrimeColumns_succ {n : ℕ} (P : Fin n → ℕ) (i : Fin n) :
    signedPrimeColumns P i.succ = (P i : ℚ) := rfl

/-- All signed prime columns are nonzero. -/
theorem signedPrimeColumns_ne_zero {n : ℕ} (P : Fin n → ℕ)
    (hP : ∀ i, (P i).Prime) (i : Fin (n + 1)) : signedPrimeColumns P i ≠ 0 := by
  refine Fin.cases (by norm_num [signedPrimeColumns]) (fun j => ?_) i
  exact Nat.cast_ne_zero.mpr (hP j).ne_zero

/-- Sign recovers the coefficient of the negative column. -/
theorem sign_signedPrimeLinearMap {n : ℕ} (P : Fin n → ℕ)
    (hP : ∀ i, (P i).Prime) (v : Fin (n + 1) → ZMod 2) :
    squareClassSign (squareClassLinearMap (signedPrimeColumns P) v) = v 0 := by
  change squareClassSign.toZModLinearMap 2
    (squareClassLinearMap (signedPrimeColumns P) v) = v 0
  simp only [squareClassLinearMap, Fintype.linearCombination_apply, Fin.sum_univ_succ]
  simp only [map_add, map_sum, map_smul, AddMonoidHom.coe_toZModLinearMap,
    signedPrimeColumns_zero, signedPrimeColumns_succ, squareClassSign_neg_one,
    squareClassSign_prime (hP _), smul_eq_mul, mul_one, mul_zero, Finset.sum_const_zero, add_zero]

/-- Prime parity recovers each prime coefficient in the signed column map. -/
theorem primeParity_signedPrimeLinearMap {n : ℕ} (P : Fin n → ℕ)
    (hP : ∀ i, (P i).Prime) (hinj : Function.Injective P)
    (v : Fin (n + 1) → ZMod 2) (j : Fin n) :
    primeParity (P j) (hP j) (squareClassLinearMap (signedPrimeColumns P) v) =
      v j.succ := by
  classical
  change (primeParity (P j) (hP j)).toZModLinearMap 2
    (squareClassLinearMap (signedPrimeColumns P) v) = v j.succ
  simp only [squareClassLinearMap, Fintype.linearCombination_apply, Fin.sum_univ_succ]
  simp only [map_add, map_sum, map_smul, AddMonoidHom.coe_toZModLinearMap,
    signedPrimeColumns_zero, signedPrimeColumns_succ, primeParity_neg_one,
    smul_zero, zero_add]
  rw [Finset.sum_eq_single j]
  · rw [primeParity_prime (hP j) (hP j)]
    simp
  · intro i _ hij
    rw [primeParity_prime (hP j) (hP i)]
    simp [show P j ≠ P i from fun h => hij (hinj h).symm]
  · simp

/-- Including the sign column preserves injectivity of distinct-prime
squareclass coordinates. -/
theorem signedPrime_squareClassLinearMap_injective {n : ℕ} (P : Fin n → ℕ)
    (hP : ∀ i, (P i).Prime) (hinj : Function.Injective P) :
    Function.Injective (squareClassLinearMap (signedPrimeColumns P)) := by
  intro v w h
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · have := congrArg squareClassSign h
    simpa only [sign_signedPrimeLinearMap P hP] using this
  · have := congrArg (primeParity (P j) (hP j)) h
    simpa only [primeParity_signedPrimeLinearMap P hP hinj] using this

/-- The sign and distinct positive prime squareclasses are independent. -/
theorem signedPrime_squareclasses_linearIndependent {n : ℕ} (P : Fin n → ℕ)
    (hP : ∀ i, (P i).Prime) (hinj : Function.Injective P) :
    LinearIndependent (ZMod 2) (fun i => Additive.ofMul
      (rationalSquareClass (signedPrimeColumns P i))) :=
  linearIndependent_iff_injective_fintypeLinearCombination.mpr
    (signedPrime_squareClassLinearMap_injective P hP hinj)

/-- The literal bit-mask product represents the corresponding linear
combination of actual squareclasses, including arbitrary starting offsets. -/
theorem squareClass_maskValueFrom_ofFn {n : ℕ} (columns : Fin n → ℚ)
    (hnz : ∀ i, columns i ≠ 0) (code offset : ℕ) :
    Additive.ofMul (rationalSquareClass
      (Integration.maskValueFrom code offset (List.ofFn columns))) =
      ∑ i : Fin n, Binary.scalar (code.testBit (offset + i.val)) •
        Additive.ofMul (rationalSquareClass (columns i)) := by
  induction n generalizing offset with
  | zero => simp [Integration.maskValueFrom]
  | succ n ih =>
      rw [List.ofFn_succ, Integration.maskValueFrom]
      have htail : Integration.maskValueFrom code (offset + 1)
          (List.ofFn (fun i => columns i.succ)) ≠ 0 :=
        DescentWitnesses.maskValueFrom_ne_zero _ _ _ (by
          simpa using fun (i : Fin n) => hnz i.succ)
      have hhead : (if code.testBit offset then columns 0 else 1) ≠ 0 := by
        split_ifs
        · exact hnz 0
        · exact one_ne_zero
      rw [rationalSquareClass_mul hhead htail, ofMul_mul,
        ih (fun i => columns i.succ) (fun i => hnz i.succ) (offset + 1),
        Fin.sum_univ_succ]
      congr 1
      · cases hb : code.testBit offset
        · simp only [Fin.val_zero, Nat.add_zero, hb, Binary.scalar, Bool.false_eq_true, ite_false,
            rationalSquareClass_one, ofMul_one]
          exact (zero_smul (ZMod 2)
            (Additive.ofMul (rationalSquareClass (columns 0)))).symm
        · simp [hb, Binary.scalar]
      · apply Finset.sum_congr rfl
        intro i _
        simp only [Fin.val_succ]
        rw [show offset + 1 + i.val = offset + (i.val + 1) by omega]

/-- Literal mask multiplication agrees with the binary linear map. -/
theorem squareClass_maskValue_ofFn {n : ℕ} (columns : Fin n → ℚ)
    (hnz : ∀ i, columns i ≠ 0) (code : ℕ) :
    Additive.ofMul (rationalSquareClass
      (Integration.maskValue (List.ofFn columns) code)) =
      squareClassLinearMap columns (Binary.vector n code) := by
  simpa only [Integration.maskValue, squareClassLinearMap,
    Fintype.linearCombination_apply, Binary.vector, Nat.zero_add] using
    squareClass_maskValueFrom_ofFn columns hnz code 0

/-- Any independent binary family remains independent under an injective
squareclass column map. -/
theorem mask_classes_linearIndependent {n : ℕ} (columns : Fin n → ℚ)
    (hnz : ∀ i, columns i ≠ 0)
    (hinj : Function.Injective (squareClassLinearMap columns))
    (generators : List ℕ)
    (hgen : LinearIndependent (ZMod 2) (Binary.generatorFamily n generators)) :
    LinearIndependent (ZMod 2) (fun i : Fin generators.length =>
      Additive.ofMul (rationalSquareClass
        (Integration.maskValue (List.ofFn columns) generators[i]))) := by
  have := hgen.map' (squareClassLinearMap columns) (LinearMap.ker_eq_bot.mpr hinj)
  simpa only [Function.comp_def, Binary.generatorFamily,
    ← squareClass_maskValue_ofFn columns hnz] using this

/-- Cardinality of the squareclass span generated by an independent family
of masks. This is a statement about actual rational squareclasses. -/
theorem mask_classes_span_card {n : ℕ} (columns : Fin n → ℚ)
    (hnz : ∀ i, columns i ≠ 0)
    (hinj : Function.Injective (squareClassLinearMap columns))
    (generators : List ℕ)
    (hgen : LinearIndependent (ZMod 2) (Binary.generatorFamily n generators)) :
    Nat.card (Submodule.span (ZMod 2) (Set.range
      (fun i : Fin generators.length => Additive.ofMul (rationalSquareClass
        (Integration.maskValue (List.ofFn columns) generators[i]))))) =
      2 ^ generators.length := by
  classical
  let v := fun i : Fin generators.length => Additive.ofMul (rationalSquareClass
    (Integration.maskValue (List.ofFn columns) generators[i]))
  have hli : LinearIndependent (ZMod 2) v :=
    mask_classes_linearIndependent columns hnz hinj generators hgen
  have : Module.Finite (ZMod 2) (Submodule.span (ZMod 2) (Set.range v)) :=
    Module.Finite.span_of_finite (ZMod 2) (Set.finite_range v)
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_eq_fintype_card,
    ZMod.card, finrank_span_eq_card hli, Fintype.card_fin]

/-- Additive subgroup generation and binary linear span agree in a group
of exponent two. -/
theorem squareClasses_span_toAddSubgroup (s : Set (Additive RationalSquareClasses)) :
    (Submodule.span (ZMod 2) s).toAddSubgroup = AddSubgroup.closure s := by
  apply le_antisymm
  · change Submodule.span (ZMod 2) s ≤
      AddSubgroup.toZModSubmodule 2 (AddSubgroup.closure s)
    exact Submodule.span_le.mpr AddSubgroup.subset_closure
  · exact (AddSubgroup.closure_le _).mpr Submodule.subset_span

/-- Multiplicative subgroup generation of squareclasses is the same binary
span after changing notation from multiplication to addition. -/
theorem squareClasses_closure_toAddSubgroup {ι : Type*}
    (f : ι → RationalSquareClasses) :
    (Subgroup.closure (Set.range f)).toAddSubgroup =
      (Submodule.span (ZMod 2)
        (Set.range (fun i => Additive.ofMul (f i)))).toAddSubgroup := by
  rw [squareClasses_span_toAddSubgroup, Subgroup.toAddSubgroup_closure]
  rfl

/-- The subgroup generated by independent literal masks has the expected
power-of-two cardinality in the actual rational squareclass group. -/
theorem mask_classes_closure_card {n : ℕ} (columns : Fin n → ℚ)
    (hnz : ∀ i, columns i ≠ 0)
    (hinj : Function.Injective (squareClassLinearMap columns))
    (generators : List ℕ)
    (hgen : LinearIndependent (ZMod 2) (Binary.generatorFamily n generators)) :
    Nat.card (Subgroup.closure (Set.range (fun i : Fin generators.length =>
      rationalSquareClass (Integration.maskValue (List.ofFn columns) generators[i])))) =
      2 ^ generators.length := by
  change Nat.card ((Subgroup.closure (Set.range (fun i : Fin generators.length =>
    rationalSquareClass (Integration.maskValue (List.ofFn columns) generators[i])))).toAddSubgroup) = _
  rw [squareClasses_closure_toAddSubgroup]
  exact mask_classes_span_card columns hnz hinj generators hgen

/-- A list is an ordered sign column followed by distinct positive primes.
The order is part of the condition, so it agrees with the archived bit masks. -/
def IsSignedPrimeColumnList {n : ℕ} (columns : List ℚ) : Prop :=
  ∃ P : Fin n → ℕ, (∀ i, (P i).Prime) ∧ Function.Injective P ∧
    columns = List.ofFn (signedPrimeColumns P)

/-- Under the concrete prime-column condition, binary independent masks
produce a subgroup of actual rational squareclasses of the certified size. -/
theorem mask_classes_closure_card_of_signedPrimes {n : ℕ} (columns : List ℚ)
    (hcolumns : IsSignedPrimeColumnList (n := n) columns)
    (generators : List ℕ)
    (hgen : LinearIndependent (ZMod 2) (Binary.generatorFamily (n + 1) generators)) :
    Nat.card (Subgroup.closure (Set.range (fun i : Fin generators.length =>
      rationalSquareClass (Integration.maskValue columns generators[i])))) =
      2 ^ generators.length := by
  rcases hcolumns with ⟨P, hP, hinj, rfl⟩
  exact mask_classes_closure_card (signedPrimeColumns P)
    (signedPrimeColumns_ne_zero P hP)
    (signedPrime_squareClassLinearMap_injective P hP hinj) generators hgen

/-- Independent actual squareclasses generate a subgroup with the expected
cardinality. -/
theorem squareClasses_closure_card_of_linearIndependent {d : ℕ}
    (f : Fin d → RationalSquareClasses)
    (hli : LinearIndependent (ZMod 2) (fun i => Additive.ofMul (f i))) :
    Nat.card (Subgroup.closure (Set.range f)) = 2 ^ d := by
  classical
  change Nat.card ((Subgroup.closure (Set.range f)).toAddSubgroup) = _
  rw [squareClasses_closure_toAddSubgroup]
  have : Module.Finite (ZMod 2) (Submodule.span (ZMod 2)
      (Set.range (fun i => Additive.ofMul (f i)))) :=
    Module.Finite.span_of_finite (ZMod 2) (Set.finite_range _)
  change Nat.card (Submodule.span (ZMod 2)
    (Set.range (fun i => Additive.ofMul (f i)))) = _
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_eq_fintype_card,
    ZMod.card, finrank_span_eq_card hli, Fintype.card_fin]

/-- Cardinality transfer for a finite indexed family of literal masks. -/
theorem mask_family_closure_card_of_signedPrimes {n d : ℕ} (columns : List ℚ)
    (hcolumns : IsSignedPrimeColumnList (n := n) columns) (codes : Fin d → ℕ)
    (hcodes : LinearIndependent (ZMod 2) (fun i => Binary.vector (n + 1) (codes i))) :
    Nat.card (Subgroup.closure (Set.range (fun i => rationalSquareClass
      (Integration.maskValue columns (codes i))))) = 2 ^ d := by
  rcases hcolumns with ⟨P, hP, hinj, rfl⟩
  apply squareClasses_closure_card_of_linearIndependent
  have hli := hcodes.map' (squareClassLinearMap (signedPrimeColumns P))
    (LinearMap.ker_eq_bot.mpr (signedPrime_squareClassLinearMap_injective P hP hinj))
  simpa only [Function.comp_def, ← squareClass_maskValue_ofFn
    (signedPrimeColumns P) (signedPrimeColumns_ne_zero P hP)] using hli

/-- Exact size of the actual subgroup generated by the rank-5
E masks, when all its ordered prime columns are distinct positive primes. -/
theorem knownclasses5E_closure_card (p : Fin 12 → ℚ)
    (hp : IsSignedPrimeColumnList (n := 11) (Integration.columns5E p)) :
    Nat.card (Subgroup.closure (Set.range (fun i : Fin 3 => rationalSquareClass
      (Integration.maskValue (Integration.columns5E p) (Integration.codes5E i))))) =
      2 ^ 3 := by
  apply mask_family_closure_card_of_signedPrimes (Integration.columns5E p) hp
    Integration.codes5E
  have heq : (fun i : Fin 3 => Binary.vector 12 (Integration.codes5E i)) =
      Binary.generatorFamily 12 MatrixCertificates.Rank5.Egenerators := by
    funext i
    fin_cases i <;> rfl
  rw [heq]
  exact MatrixCertificates.Rank5.Egenerators_linearIndependent

/-- Exact size of the actual subgroup generated by the rank-5
Ep masks, when all its ordered prime columns are distinct positive primes. -/
theorem knownclasses5Ep_closure_card (p : Fin 12 → ℚ)
    (hp : IsSignedPrimeColumnList (n := 11) (Integration.columns5Ep p)) :
    Nat.card (Subgroup.closure (Set.range (fun i : Fin 4 => rationalSquareClass
      (Integration.maskValue (Integration.columns5Ep p) (Integration.codes5Ep i))))) =
      2 ^ 4 := by
  apply mask_family_closure_card_of_signedPrimes (Integration.columns5Ep p) hp
    Integration.codes5Ep
  have heq : (fun i : Fin 4 => Binary.vector 12 (Integration.codes5Ep i)) =
      Binary.generatorFamily 12 MatrixCertificates.Rank5.Epgenerators := by
    funext i
    fin_cases i <;> rfl
  rw [heq]
  exact MatrixCertificates.Rank5.Epgenerators_linearIndependent

/-- Exact size of the actual subgroup generated by the rank-6
E masks, when all its ordered prime columns are distinct positive primes. -/
theorem knownclasses6E_closure_card (p : Fin 12 → ℚ)
    (hp : IsSignedPrimeColumnList (n := 11) (Integration.columns6E p)) :
    Nat.card (Subgroup.closure (Set.range (fun i : Fin 4 => rationalSquareClass
      (Integration.maskValue (Integration.columns6E p) (Integration.codes6E i))))) =
      2 ^ 4 := by
  apply mask_family_closure_card_of_signedPrimes (Integration.columns6E p) hp
    Integration.codes6E
  have heq : (fun i : Fin 4 => Binary.vector 12 (Integration.codes6E i)) =
      Binary.generatorFamily 12 MatrixCertificates.Rank6.Egenerators := by
    funext i
    fin_cases i <;> rfl
  rw [heq]
  exact MatrixCertificates.Rank6.Egenerators_linearIndependent

/-- Exact size of the actual subgroup generated by the rank-6
Ep masks, when all its ordered prime columns are distinct positive primes. -/
theorem knownclasses6Ep_closure_card (p : Fin 12 → ℚ)
    (hp : IsSignedPrimeColumnList (n := 11) (Integration.columns6Ep p)) :
    Nat.card (Subgroup.closure (Set.range (fun i : Fin 4 => rationalSquareClass
      (Integration.maskValue (Integration.columns6Ep p) (Integration.codes6Ep i))))) =
      2 ^ 4 := by
  apply mask_family_closure_card_of_signedPrimes (Integration.columns6Ep p) hp
    Integration.codes6Ep
  have heq : (fun i : Fin 4 => Binary.vector 12 (Integration.codes6Ep i)) =
      Binary.generatorFamily 12 MatrixCertificates.Rank6.Epgenerators := by
    funext i
    fin_cases i <;> rfl
  rw [heq]
  exact MatrixCertificates.Rank6.Epgenerators_linearIndependent

/-- Exact size of the actual subgroup generated by the rank-7
E masks, when all its ordered prime columns are distinct positive primes. -/
theorem knownclasses7E_closure_card (p : Fin 12 → ℚ)
    (hp : IsSignedPrimeColumnList (n := 12) (Integration.columns7E p)) :
    Nat.card (Subgroup.closure (Set.range (fun i : Fin 5 => rationalSquareClass
      (Integration.maskValue (Integration.columns7E p) (Integration.codes7E i))))) =
      2 ^ 5 := by
  apply mask_family_closure_card_of_signedPrimes (Integration.columns7E p) hp
    Integration.codes7E
  have heq : (fun i : Fin 5 => Binary.vector 13 (Integration.codes7E i)) =
      Binary.generatorFamily 13 MatrixCertificates.Rank7.Egenerators := by
    funext i
    fin_cases i <;> rfl
  rw [heq]
  exact MatrixCertificates.Rank7.Egenerators_linearIndependent

/-- Exact size of the actual subgroup generated by the rank-7
Ep masks, when all its ordered prime columns are distinct positive primes. -/
theorem knownclasses7Ep_closure_card (p : Fin 12 → ℚ)
    (hp : IsSignedPrimeColumnList (n := 12) (Integration.columns7Ep p)) :
    Nat.card (Subgroup.closure (Set.range (fun i : Fin 4 => rationalSquareClass
      (Integration.maskValue (Integration.columns7Ep p) (Integration.codes7Ep i))))) =
      2 ^ 4 := by
  apply mask_family_closure_card_of_signedPrimes (Integration.columns7Ep p) hp
    Integration.codes7Ep
  have heq : (fun i : Fin 4 => Binary.vector 13 (Integration.codes7Ep i)) =
      Binary.generatorFamily 13 MatrixCertificates.Rank7.Epgenerators := by
    funext i
    fin_cases i <;> rfl
  rw [heq]
  exact MatrixCertificates.Rank7.Epgenerators_linearIndependent

end RankCertificates
