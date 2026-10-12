module

public import RankCertificates.PrimeCoefficientSupport
public import RankCertificates.SquareClassClassification
public import RankCertificates.LocalCharacterRows

@[expose] public section

/-! Global prime support places every genuine Kummer image of a concrete
prime specialization inside its finite signed-prime ambient space. -/

namespace RankCertificates

/-- Once actual classes satisfy verified local rows, their number is bounded
by the genuine kernel of that binary matrix. The ambient expansion supplies
the rational-point-to-vector bridge. -/
theorem twoIsogenyImage_card_le_binaryKernel {n : ℕ} (a b : ℚ)
    (columns : Fin n → ℚ) (rows : List ℕ)
    (hambient : ∀ q ∈ twoIsogenyImage a b,
      Additive.ofMul q ∈ (squareClassLinearMap columns).range)
    (hrows : ∀ v : Fin n → ZMod 2,
      (squareClassLinearMap columns v).toMul ∈ twoIsogenyImage a b →
      Binary.VectorKernel n rows v) :
    Nat.card (twoIsogenyImage a b) ≤ Nat.card ↥(Binary.kernelSubmodule n rows) := by
  classical
  let repr (q : twoIsogenyImage a b) : Fin n → ZMod 2 :=
    Classical.choose (hambient q.val q.property)
  have hrepr (q : twoIsogenyImage a b) :
      squareClassLinearMap columns (repr q) = Additive.ofMul q.val :=
    Classical.choose_spec (hambient q.val q.property)
  let embed : twoIsogenyImage a b → Binary.kernelSubmodule n rows := fun q =>
    ⟨repr q, hrows (repr q) (by rw [hrepr]; exact q.property)⟩
  apply Nat.card_le_card_of_injective embed
  intro q r h
  have hv : repr q = repr r := congrArg Subtype.val h
  apply Subtype.ext
  have hclass : Additive.ofMul q.val = Additive.ofMul r.val := by
    rw [← hrepr, ← hrepr, hv]
  exact congrArg Additive.toMul hclass

/-- A matrix whose literal rows are verified actual local characters bounds
the full rational-point image by its kernel cardinality. -/
theorem twoIsogenyImage_card_le_verifiedCharacterKernel {n : ℕ} (a b : ℚ)
    (columns : Fin n → ℚ) (rows : List ℕ)
    (hambient : ∀ q ∈ twoIsogenyImage a b,
      Additive.ofMul q ∈ (squareClassLinearMap columns).range)
    (hcharacters : ∀ row ∈ rows,
      ∃ f : Additive RationalSquareClasses →ₗ[ZMod 2] ZMod 2,
        squareClassCharacterRow f columns = Binary.vector n row ∧
        ∀ q ∈ twoIsogenyImage a b, f (Additive.ofMul q) = 0) :
    Nat.card (twoIsogenyImage a b) ≤ Nat.card ↥(Binary.kernelSubmodule n rows) := by
  apply twoIsogenyImage_card_le_binaryKernel a b columns rows hambient
  intro v hv row hrow
  obtain ⟨f, hf, hzero⟩ := hcharacters row hrow
  rw [← hf, ← characterLinear_squareClassLinearMap]
  exact hzero _ hv

/-- Every actual rank-5 E Kummer class has a signed-prime expansion. -/
theorem PrimeSpecialization5.actualImageE_mem_signedPrime_range {x y : ℤ}
    (h : PrimeSpecialization5 x y) {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (Rank5.a (Integration.M5 x) (Integration.N5 y)) (Rank5.b (Integration.M5 x) (Integration.N5 y))) :
    Additive.ofMul q ∈
      (squareClassLinearMap (signedPrimeColumns (primeColumns5E h.primes))).range := by
  apply integral_twoIsogenyImage_mem_signedPrime_range (aInteger5 x y) (bInteger5 x y)
    (primeColumns5E h.primes) (primeColumns5E_prime h) (primeColumns5E_injective h)
    (fun p hp hd => h.bInteger_prime_support hp hd)
  simpa only [aInteger5_cast, bInteger5_cast] using hq

/-- Global prime support bounds the actual rank-5 E Kummer image. -/
theorem PrimeSpecialization5.actualImageE_card_ambient_upperBound {x y : ℤ}
    (h : PrimeSpecialization5 x y) :
    Nat.card (twoIsogenyImage (Rank5.a (Integration.M5 x) (Integration.N5 y)) (Rank5.b (Integration.M5 x) (Integration.N5 y))) ≤ 2 ^ 12 := by
  have hu := integral_twoIsogenyImage_card_le (aInteger5 x y) (bInteger5 x y)
    (primeColumns5E h.primes) (primeColumns5E_prime h) (primeColumns5E_injective h)
    (fun p hp hd => h.bInteger_prime_support hp hd)
  simpa only [aInteger5_cast, bInteger5_cast] using hu

/-- Every actual rank-5 Ep Kummer class has a signed-prime expansion. -/
theorem PrimeSpecialization5.actualImageEp_mem_signedPrime_range {x y : ℤ}
    (h : PrimeSpecialization5 x y) {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage ((-2 * Rank5.a (Integration.M5 x) (Integration.N5 y))) (Rank5.c (Integration.M5 x) (Integration.N5 y))) :
    Additive.ofMul q ∈
      (squareClassLinearMap (signedPrimeColumns (primeColumns5Ep h.primes))).range := by
  apply integral_twoIsogenyImage_mem_signedPrime_range (-2 * aInteger5 x y) (cInteger5 x y)
    (primeColumns5Ep h.primes) (primeColumns5Ep_prime h) (primeColumns5Ep_injective h)
    (fun p hp hd => h.cInteger_prime_support hp hd)
  simpa only [Int.cast_mul, Int.cast_neg, Int.cast_ofNat, aInteger5_cast, cInteger5_cast] using hq

/-- Global prime support bounds the actual rank-5 Ep Kummer image. -/
theorem PrimeSpecialization5.actualImageEp_card_ambient_upperBound {x y : ℤ}
    (h : PrimeSpecialization5 x y) :
    Nat.card (twoIsogenyImage ((-2 * Rank5.a (Integration.M5 x) (Integration.N5 y))) (Rank5.c (Integration.M5 x) (Integration.N5 y))) ≤ 2 ^ 12 := by
  have hu := integral_twoIsogenyImage_card_le (-2 * aInteger5 x y) (cInteger5 x y)
    (primeColumns5Ep h.primes) (primeColumns5Ep_prime h) (primeColumns5Ep_injective h)
    (fun p hp hd => h.cInteger_prime_support hp hd)
  simpa only [Int.cast_mul, Int.cast_neg, Int.cast_ofNat, aInteger5_cast, cInteger5_cast] using hu

/-- Every actual rank-6 E Kummer class has a signed-prime expansion. -/
theorem PrimeSpecialization6.actualImageE_mem_signedPrime_range {x y : ℤ}
    (h : PrimeSpecialization6 x y) {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (Rank6.a (Integration.M6 x) (Integration.N6 y)) (Rank6.b (Integration.M6 x) (Integration.N6 y))) :
    Additive.ofMul q ∈
      (squareClassLinearMap (signedPrimeColumns (primeColumns6E h.primes))).range := by
  apply integral_twoIsogenyImage_mem_signedPrime_range (aInteger6 x y) (bInteger6 x y)
    (primeColumns6E h.primes) (primeColumns6E_prime h) (primeColumns6E_injective h)
    (fun p hp hd => h.bInteger_prime_support hp hd)
  simpa only [aInteger6_cast, bInteger6_cast] using hq

/-- Global prime support bounds the actual rank-6 E Kummer image. -/
theorem PrimeSpecialization6.actualImageE_card_ambient_upperBound {x y : ℤ}
    (h : PrimeSpecialization6 x y) :
    Nat.card (twoIsogenyImage (Rank6.a (Integration.M6 x) (Integration.N6 y)) (Rank6.b (Integration.M6 x) (Integration.N6 y))) ≤ 2 ^ 12 := by
  have hu := integral_twoIsogenyImage_card_le (aInteger6 x y) (bInteger6 x y)
    (primeColumns6E h.primes) (primeColumns6E_prime h) (primeColumns6E_injective h)
    (fun p hp hd => h.bInteger_prime_support hp hd)
  simpa only [aInteger6_cast, bInteger6_cast] using hu

/-- Every actual rank-6 Ep Kummer class has a signed-prime expansion. -/
theorem PrimeSpecialization6.actualImageEp_mem_signedPrime_range {x y : ℤ}
    (h : PrimeSpecialization6 x y) {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage ((-2 * Rank6.a (Integration.M6 x) (Integration.N6 y))) (Rank6.c (Integration.M6 x) (Integration.N6 y))) :
    Additive.ofMul q ∈
      (squareClassLinearMap (signedPrimeColumns (primeColumns6Ep h.primes))).range := by
  apply integral_twoIsogenyImage_mem_signedPrime_range (-2 * aInteger6 x y) (cInteger6 x y)
    (primeColumns6Ep h.primes) (primeColumns6Ep_prime h) (primeColumns6Ep_injective h)
    (fun p hp hd => h.cInteger_prime_support hp hd)
  simpa only [Int.cast_mul, Int.cast_neg, Int.cast_ofNat, aInteger6_cast, cInteger6_cast] using hq

/-- Global prime support bounds the actual rank-6 Ep Kummer image. -/
theorem PrimeSpecialization6.actualImageEp_card_ambient_upperBound {x y : ℤ}
    (h : PrimeSpecialization6 x y) :
    Nat.card (twoIsogenyImage ((-2 * Rank6.a (Integration.M6 x) (Integration.N6 y))) (Rank6.c (Integration.M6 x) (Integration.N6 y))) ≤ 2 ^ 12 := by
  have hu := integral_twoIsogenyImage_card_le (-2 * aInteger6 x y) (cInteger6 x y)
    (primeColumns6Ep h.primes) (primeColumns6Ep_prime h) (primeColumns6Ep_injective h)
    (fun p hp hd => h.cInteger_prime_support hp hd)
  simpa only [Int.cast_mul, Int.cast_neg, Int.cast_ofNat, aInteger6_cast, cInteger6_cast] using hu

/-- Every actual rank-7 E Kummer class has a signed-prime expansion. -/
theorem PrimeSpecialization7.actualImageE_mem_signedPrime_range {x y : ℤ}
    (h : PrimeSpecialization7 x y) {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage (Rank7.a (Integration.M7 x) (Integration.N7 y)) (Rank7.b (Integration.M7 x) (Integration.N7 y))) :
    Additive.ofMul q ∈
      (squareClassLinearMap (signedPrimeColumns (primeColumns7E h.primes))).range := by
  apply integral_twoIsogenyImage_mem_signedPrime_range (aInteger7 x y) (bInteger7 x y)
    (primeColumns7E h.primes) (primeColumns7E_prime h) (primeColumns7E_injective h)
    (fun p hp hd => h.bInteger_prime_support hp hd)
  simpa only [aInteger7_cast, bInteger7_cast] using hq

/-- Global prime support bounds the actual rank-7 E Kummer image. -/
theorem PrimeSpecialization7.actualImageE_card_ambient_upperBound {x y : ℤ}
    (h : PrimeSpecialization7 x y) :
    Nat.card (twoIsogenyImage (Rank7.a (Integration.M7 x) (Integration.N7 y)) (Rank7.b (Integration.M7 x) (Integration.N7 y))) ≤ 2 ^ 13 := by
  have hu := integral_twoIsogenyImage_card_le (aInteger7 x y) (bInteger7 x y)
    (primeColumns7E h.primes) (primeColumns7E_prime h) (primeColumns7E_injective h)
    (fun p hp hd => h.bInteger_prime_support hp hd)
  simpa only [aInteger7_cast, bInteger7_cast] using hu

/-- Every actual rank-7 Ep Kummer class has a signed-prime expansion. -/
theorem PrimeSpecialization7.actualImageEp_mem_signedPrime_range {x y : ℤ}
    (h : PrimeSpecialization7 x y) {q : RationalSquareClasses}
    (hq : q ∈ twoIsogenyImage ((-2 * Rank7.a (Integration.M7 x) (Integration.N7 y))) (Rank7.c (Integration.M7 x) (Integration.N7 y))) :
    Additive.ofMul q ∈
      (squareClassLinearMap (signedPrimeColumns (primeColumns7Ep h.primes))).range := by
  apply integral_twoIsogenyImage_mem_signedPrime_range (-2 * aInteger7 x y) (cInteger7 x y)
    (primeColumns7Ep h.primes) (primeColumns7Ep_prime h) (primeColumns7Ep_injective h)
    (fun p hp hd => h.cInteger_prime_support hp hd)
  simpa only [Int.cast_mul, Int.cast_neg, Int.cast_ofNat, aInteger7_cast, cInteger7_cast] using hq

/-- Global prime support bounds the actual rank-7 Ep Kummer image. -/
theorem PrimeSpecialization7.actualImageEp_card_ambient_upperBound {x y : ℤ}
    (h : PrimeSpecialization7 x y) :
    Nat.card (twoIsogenyImage ((-2 * Rank7.a (Integration.M7 x) (Integration.N7 y))) (Rank7.c (Integration.M7 x) (Integration.N7 y))) ≤ 2 ^ 13 := by
  have hu := integral_twoIsogenyImage_card_le (-2 * aInteger7 x y) (cInteger7 x y)
    (primeColumns7Ep h.primes) (primeColumns7Ep_prime h) (primeColumns7Ep_injective h)
    (fun p hp hd => h.cInteger_prime_support hp hd)
  simpa only [Int.cast_mul, Int.cast_neg, Int.cast_ofNat, aInteger7_cast, cInteger7_cast] using hu

end RankCertificates
