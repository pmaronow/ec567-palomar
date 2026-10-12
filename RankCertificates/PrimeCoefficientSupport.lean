module

public import RankCertificates.PrimeSpecializations

/-!
# Integral coefficients and prime support on the CRT lattices

Literal coefficient factorizations show that every prime divisor of `b`
or of the partner coefficient `c` is one of the corresponding ordered prime
columns. These are algebraic and divisibility statements, not prime existence
or local descent bounds.
-/

@[expose] public section

namespace RankCertificates

/-- A prime dividing a prime output is that output prime. -/
theorem PositivePrimeOutputs.prime_dvd_output_iff {outputs : Fin 12 → ℤ}
    {smallPrimes : List ℕ} (h : PositivePrimeOutputs outputs smallPrimes)
    {p : ℕ} (hp : p.Prime) (i : Fin 12) :
    (p : ℤ) ∣ outputs i ↔ p = h.primes i := by
  rw [← Int.natAbs_dvd_natAbs]
  simpa only [Int.natAbs_natCast, PositivePrimeOutputs.primes, eq_comm] using
    (h.prime i).dvd_iff_eq hp.ne_one

/-- A prime divisor of a power of a prime equals its base prime. -/
theorem prime_dvd_nat_prime_power {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {e : ℕ} (hd : (p : ℤ) ∣ (q : ℤ) ^ e) : p = q := by
  have hprime : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  have hnat : p ∣ q := Int.natCast_dvd_natCast.mp (hprime.dvd_of_dvd_pow hd)
  exact ((hq.dvd_iff_eq hp.ne_one).mp hnat).symm


theorem lattice5_factorGroups (x y : ℤ) :
    Rank5.F (Integration.M5 x) (Integration.N5 y) = 432 *
      (Integration.outputs5 x y 0 * Integration.outputs5 x y 1 *
        Integration.outputs5 x y 2 * Integration.outputs5 x y 3) ∧
    Rank5.H (Integration.M5 x) (Integration.N5 y) = 16 *
      (Integration.outputs5 x y 4 * Integration.outputs5 x y 5 *
        Integration.outputs5 x y 6 * Integration.outputs5 x y 7) ∧
    Rank5.J (Integration.M5 x) (Integration.N5 y) = 24 *
      (Integration.outputs5 x y 8 * Integration.outputs5 x y 9 *
        Integration.outputs5 x y 10 * Integration.outputs5 x y 11) := by
  have h0 : Rank5.L0 (Integration.M5 x) (Integration.N5 y) =
      54 * Integration.outputs5 x y 0 := by
    simpa [Integration.forms5, PrimePatterns.Rank5.cofactors] using
      Integration.normalization5 x y (0 : Fin 12)
  have h1 : Rank5.L1 (Integration.M5 x) (Integration.N5 y) =
      1 * Integration.outputs5 x y 1 := by
    simpa [Integration.forms5, PrimePatterns.Rank5.cofactors] using
      Integration.normalization5 x y (1 : Fin 12)
  have h2 : Rank5.L2 (Integration.M5 x) (Integration.N5 y) =
      8 * Integration.outputs5 x y 2 := by
    simpa [Integration.forms5, PrimePatterns.Rank5.cofactors] using
      Integration.normalization5 x y (2 : Fin 12)
  have h3 : Rank5.L3 (Integration.M5 x) (Integration.N5 y) =
      1 * Integration.outputs5 x y 3 := by
    simpa [Integration.forms5, PrimePatterns.Rank5.cofactors] using
      Integration.normalization5 x y (3 : Fin 12)
  have h4 : Rank5.L4 (Integration.M5 x) (Integration.N5 y) =
      8 * Integration.outputs5 x y 4 := by
    simpa [Integration.forms5, PrimePatterns.Rank5.cofactors] using
      Integration.normalization5 x y (4 : Fin 12)
  have h5 : Rank5.L5 (Integration.M5 x) (Integration.N5 y) =
      1 * Integration.outputs5 x y 5 := by
    simpa [Integration.forms5, PrimePatterns.Rank5.cofactors] using
      Integration.normalization5 x y (5 : Fin 12)
  have h6 : Rank5.L6 (Integration.M5 x) (Integration.N5 y) =
      1 * Integration.outputs5 x y 6 := by
    simpa [Integration.forms5, PrimePatterns.Rank5.cofactors] using
      Integration.normalization5 x y (6 : Fin 12)
  have h7 : Rank5.L7 (Integration.M5 x) (Integration.N5 y) =
      2 * Integration.outputs5 x y 7 := by
    simpa [Integration.forms5, PrimePatterns.Rank5.cofactors] using
      Integration.normalization5 x y (7 : Fin 12)
  have h8 : Rank5.L8 (Integration.M5 x) (Integration.N5 y) =
      4 * Integration.outputs5 x y 8 := by
    simpa [Integration.forms5, PrimePatterns.Rank5.cofactors] using
      Integration.normalization5 x y (8 : Fin 12)
  have h9 : Rank5.L9 (Integration.M5 x) (Integration.N5 y) =
      1 * Integration.outputs5 x y 9 := by
    simpa [Integration.forms5, PrimePatterns.Rank5.cofactors] using
      Integration.normalization5 x y (9 : Fin 12)
  have h10 : Rank5.L10 (Integration.M5 x) (Integration.N5 y) =
      1 * Integration.outputs5 x y 10 := by
    simpa [Integration.forms5, PrimePatterns.Rank5.cofactors] using
      Integration.normalization5 x y (10 : Fin 12)
  have h11 : Rank5.L11 (Integration.M5 x) (Integration.N5 y) =
      6 * Integration.outputs5 x y 11 := by
    simpa [Integration.forms5, PrimePatterns.Rank5.cofactors] using
      Integration.normalization5 x y (11 : Fin 12)
  refine ⟨?_, ?_, ?_⟩
  all_goals
    simp only [Rank5.F, Rank5.H, Rank5.J, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    ring

/-- The genuine coefficient is the cast of this explicit integer. -/
def aInteger5 (x y : ℤ) : ℤ := 648000 *
    (PrimePatterns.Rank5.outputs 0).eval x y *
    (PrimePatterns.Rank5.outputs 1).eval x y *
    (PrimePatterns.Rank5.outputs 2).eval x y *
    (PrimePatterns.Rank5.outputs 3).eval x y

theorem aInteger5_cast (x y : ℤ) :
    (aInteger5 x y : ℚ) = Rank5.a (Integration.M5 x) (Integration.N5 y) := by
  rcases lattice5_factorGroups x y with ⟨hF, hH, hJ⟩
  simp only [aInteger5, Int.cast_mul, Int.cast_ofNat,
    Rank5.a, hF, Integration.outputs5]
  ring

/-- The genuine coefficient is the cast of this explicit integer. -/
def bInteger5 (x y : ℤ) : ℤ := -18662400 *
    (PrimePatterns.Rank5.outputs 0).eval x y *
    (PrimePatterns.Rank5.outputs 1).eval x y *
    (PrimePatterns.Rank5.outputs 2).eval x y *
    (PrimePatterns.Rank5.outputs 3).eval x y *
    (PrimePatterns.Rank5.outputs 4).eval x y *
    (PrimePatterns.Rank5.outputs 5).eval x y *
    (PrimePatterns.Rank5.outputs 6).eval x y *
    (PrimePatterns.Rank5.outputs 7).eval x y

theorem bInteger5_cast (x y : ℤ) :
    (bInteger5 x y : ℚ) = Rank5.b (Integration.M5 x) (Integration.N5 y) := by
  rcases lattice5_factorGroups x y with ⟨hF, hH, hJ⟩
  simp only [bInteger5, Int.cast_mul, Int.cast_ofNat, Int.cast_neg,
    Rank5.b, hF, hH, Integration.outputs5]
  ring

/-- The genuine coefficient is the cast of this explicit integer. -/
def cInteger5 (x y : ℤ) : ℤ := 597196800 *
    (PrimePatterns.Rank5.outputs 0).eval x y *
    (PrimePatterns.Rank5.outputs 1).eval x y *
    (PrimePatterns.Rank5.outputs 2).eval x y *
    (PrimePatterns.Rank5.outputs 3).eval x y *
    (PrimePatterns.Rank5.outputs 8).eval x y *
    (PrimePatterns.Rank5.outputs 9).eval x y *
    (PrimePatterns.Rank5.outputs 10).eval x y *
    (PrimePatterns.Rank5.outputs 11).eval x y

theorem cInteger5_cast (x y : ℤ) :
    (cInteger5 x y : ℚ) = Rank5.c (Integration.M5 x) (Integration.N5 y) := by
  rcases lattice5_factorGroups x y with ⟨hF, hH, hJ⟩
  simp only [cInteger5, Int.cast_mul, Int.cast_ofNat,
    Rank5.c, hF, hJ, Integration.outputs5]
  ring

theorem lattice6_factorGroups (x y : ℤ) :
    Rank6.F (Integration.M6 x) (Integration.N6 y) = 8 *
      (Integration.outputs6 x y 0 * Integration.outputs6 x y 1 *
        Integration.outputs6 x y 2 * Integration.outputs6 x y 3) ∧
    Rank6.H (Integration.M6 x) (Integration.N6 y) = 2 *
      (Integration.outputs6 x y 4 * Integration.outputs6 x y 5 *
        Integration.outputs6 x y 6 * Integration.outputs6 x y 7) ∧
    Rank6.J (Integration.M6 x) (Integration.N6 y) = 648 *
      (Integration.outputs6 x y 8 * Integration.outputs6 x y 9 *
        Integration.outputs6 x y 10 * Integration.outputs6 x y 11) := by
  have h0 : Rank6.L0 (Integration.M6 x) (Integration.N6 y) =
      1 * Integration.outputs6 x y 0 := by
    simpa [Integration.forms6, PrimePatterns.Rank6.cofactors] using
      Integration.normalization6 x y (0 : Fin 12)
  have h1 : Rank6.L1 (Integration.M6 x) (Integration.N6 y) =
      1 * Integration.outputs6 x y 1 := by
    simpa [Integration.forms6, PrimePatterns.Rank6.cofactors] using
      Integration.normalization6 x y (1 : Fin 12)
  have h2 : Rank6.L2 (Integration.M6 x) (Integration.N6 y) =
      1 * Integration.outputs6 x y 2 := by
    simpa [Integration.forms6, PrimePatterns.Rank6.cofactors] using
      Integration.normalization6 x y (2 : Fin 12)
  have h3 : Rank6.L3 (Integration.M6 x) (Integration.N6 y) =
      8 * Integration.outputs6 x y 3 := by
    simpa [Integration.forms6, PrimePatterns.Rank6.cofactors] using
      Integration.normalization6 x y (3 : Fin 12)
  have h4 : Rank6.L4 (Integration.M6 x) (Integration.N6 y) =
      2 * Integration.outputs6 x y 4 := by
    simpa [Integration.forms6, PrimePatterns.Rank6.cofactors] using
      Integration.normalization6 x y (4 : Fin 12)
  have h5 : Rank6.L5 (Integration.M6 x) (Integration.N6 y) =
      1 * Integration.outputs6 x y 5 := by
    simpa [Integration.forms6, PrimePatterns.Rank6.cofactors] using
      Integration.normalization6 x y (5 : Fin 12)
  have h6 : Rank6.L6 (Integration.M6 x) (Integration.N6 y) =
      1 * Integration.outputs6 x y 6 := by
    simpa [Integration.forms6, PrimePatterns.Rank6.cofactors] using
      Integration.normalization6 x y (6 : Fin 12)
  have h7 : Rank6.L7 (Integration.M6 x) (Integration.N6 y) =
      1 * Integration.outputs6 x y 7 := by
    simpa [Integration.forms6, PrimePatterns.Rank6.cofactors] using
      Integration.normalization6 x y (7 : Fin 12)
  have h8 : Rank6.L8 (Integration.M6 x) (Integration.N6 y) =
      8 * Integration.outputs6 x y 8 := by
    simpa [Integration.forms6, PrimePatterns.Rank6.cofactors] using
      Integration.normalization6 x y (8 : Fin 12)
  have h9 : Rank6.L9 (Integration.M6 x) (Integration.N6 y) =
      27 * Integration.outputs6 x y 9 := by
    simpa [Integration.forms6, PrimePatterns.Rank6.cofactors] using
      Integration.normalization6 x y (9 : Fin 12)
  have h10 : Rank6.L10 (Integration.M6 x) (Integration.N6 y) =
      3 * Integration.outputs6 x y 10 := by
    simpa [Integration.forms6, PrimePatterns.Rank6.cofactors] using
      Integration.normalization6 x y (10 : Fin 12)
  have h11 : Rank6.L11 (Integration.M6 x) (Integration.N6 y) =
      1 * Integration.outputs6 x y 11 := by
    simpa [Integration.forms6, PrimePatterns.Rank6.cofactors] using
      Integration.normalization6 x y (11 : Fin 12)
  refine ⟨?_, ?_, ?_⟩
  all_goals
    simp only [Rank6.F, Rank6.H, Rank6.J, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    ring

/-- The genuine coefficient is the cast of this explicit integer. -/
def aInteger6 (x y : ℤ) : ℤ := 560 *
    (PrimePatterns.Rank6.outputs 0).eval x y *
    (PrimePatterns.Rank6.outputs 1).eval x y *
    (PrimePatterns.Rank6.outputs 2).eval x y *
    (PrimePatterns.Rank6.outputs 3).eval x y

theorem aInteger6_cast (x y : ℤ) :
    (aInteger6 x y : ℚ) = Rank6.a (Integration.M6 x) (Integration.N6 y) := by
  rcases lattice6_factorGroups x y with ⟨hF, hH, hJ⟩
  simp only [aInteger6, Int.cast_mul, Int.cast_ofNat,
    Rank6.a, hF, Integration.outputs6]
  ring

/-- The genuine coefficient is the cast of this explicit integer. -/
def bInteger6 (x y : ℤ) : ℤ := -12544 *
    (PrimePatterns.Rank6.outputs 0).eval x y *
    (PrimePatterns.Rank6.outputs 1).eval x y *
    (PrimePatterns.Rank6.outputs 2).eval x y *
    (PrimePatterns.Rank6.outputs 3).eval x y *
    (PrimePatterns.Rank6.outputs 4).eval x y *
    (PrimePatterns.Rank6.outputs 5).eval x y *
    (PrimePatterns.Rank6.outputs 6).eval x y *
    (PrimePatterns.Rank6.outputs 7).eval x y

theorem bInteger6_cast (x y : ℤ) :
    (bInteger6 x y : ℚ) = Rank6.b (Integration.M6 x) (Integration.N6 y) := by
  rcases lattice6_factorGroups x y with ⟨hF, hH, hJ⟩
  simp only [bInteger6, Int.cast_mul, Int.cast_ofNat, Int.cast_neg,
    Rank6.b, hF, hH, Integration.outputs6]
  ring

/-- The genuine coefficient is the cast of this explicit integer. -/
def cInteger6 (x y : ℤ) : ℤ := 9144576 *
    (PrimePatterns.Rank6.outputs 0).eval x y *
    (PrimePatterns.Rank6.outputs 1).eval x y *
    (PrimePatterns.Rank6.outputs 2).eval x y *
    (PrimePatterns.Rank6.outputs 3).eval x y *
    (PrimePatterns.Rank6.outputs 8).eval x y *
    (PrimePatterns.Rank6.outputs 9).eval x y *
    (PrimePatterns.Rank6.outputs 10).eval x y *
    (PrimePatterns.Rank6.outputs 11).eval x y

theorem cInteger6_cast (x y : ℤ) :
    (cInteger6 x y : ℚ) = Rank6.c (Integration.M6 x) (Integration.N6 y) := by
  rcases lattice6_factorGroups x y with ⟨hF, hH, hJ⟩
  simp only [cInteger6, Int.cast_mul, Int.cast_ofNat,
    Rank6.c, hF, hJ, Integration.outputs6]
  ring

theorem lattice7_factorGroups (x y : ℤ) :
    Rank7.F (Integration.M7 x) (Integration.N7 y) = 10368 *
      (Integration.outputs7 x y 0 * Integration.outputs7 x y 1 *
        Integration.outputs7 x y 2 * Integration.outputs7 x y 3) ∧
    Rank7.H (Integration.M7 x) (Integration.N7 y) = 1296 *
      (Integration.outputs7 x y 4 * Integration.outputs7 x y 5 *
        Integration.outputs7 x y 6 * Integration.outputs7 x y 7) ∧
    Rank7.J (Integration.M7 x) (Integration.N7 y) = 279936 *
      (Integration.outputs7 x y 8 * Integration.outputs7 x y 9 *
        Integration.outputs7 x y 10 * Integration.outputs7 x y 11) := by
  have h0 : Rank7.L0 (Integration.M7 x) (Integration.N7 y) =
      18 * Integration.outputs7 x y 0 := by
    simpa [Integration.forms7, PrimePatterns.Rank7.cofactors] using
      Integration.normalization7 x y (0 : Fin 12)
  have h1 : Rank7.L1 (Integration.M7 x) (Integration.N7 y) =
      1 * Integration.outputs7 x y 1 := by
    simpa [Integration.forms7, PrimePatterns.Rank7.cofactors] using
      Integration.normalization7 x y (1 : Fin 12)
  have h2 : Rank7.L2 (Integration.M7 x) (Integration.N7 y) =
      64 * Integration.outputs7 x y 2 := by
    simpa [Integration.forms7, PrimePatterns.Rank7.cofactors] using
      Integration.normalization7 x y (2 : Fin 12)
  have h3 : Rank7.L3 (Integration.M7 x) (Integration.N7 y) =
      9 * Integration.outputs7 x y 3 := by
    simpa [Integration.forms7, PrimePatterns.Rank7.cofactors] using
      Integration.normalization7 x y (3 : Fin 12)
  have h4 : Rank7.L4 (Integration.M7 x) (Integration.N7 y) =
      8 * Integration.outputs7 x y 4 := by
    simpa [Integration.forms7, PrimePatterns.Rank7.cofactors] using
      Integration.normalization7 x y (4 : Fin 12)
  have h5 : Rank7.L5 (Integration.M7 x) (Integration.N7 y) =
      18 * Integration.outputs7 x y 5 := by
    simpa [Integration.forms7, PrimePatterns.Rank7.cofactors] using
      Integration.normalization7 x y (5 : Fin 12)
  have h6 : Rank7.L6 (Integration.M7 x) (Integration.N7 y) =
      9 * Integration.outputs7 x y 6 := by
    simpa [Integration.forms7, PrimePatterns.Rank7.cofactors] using
      Integration.normalization7 x y (6 : Fin 12)
  have h7 : Rank7.L7 (Integration.M7 x) (Integration.N7 y) =
      1 * Integration.outputs7 x y 7 := by
    simpa [Integration.forms7, PrimePatterns.Rank7.cofactors] using
      Integration.normalization7 x y (7 : Fin 12)
  have h8 : Rank7.L8 (Integration.M7 x) (Integration.N7 y) =
      6 * Integration.outputs7 x y 8 := by
    simpa [Integration.forms7, PrimePatterns.Rank7.cofactors] using
      Integration.normalization7 x y (8 : Fin 12)
  have h9 : Rank7.L9 (Integration.M7 x) (Integration.N7 y) =
      1728 * Integration.outputs7 x y 9 := by
    simpa [Integration.forms7, PrimePatterns.Rank7.cofactors] using
      Integration.normalization7 x y (9 : Fin 12)
  have h10 : Rank7.L10 (Integration.M7 x) (Integration.N7 y) =
      3 * Integration.outputs7 x y 10 := by
    simpa [Integration.forms7, PrimePatterns.Rank7.cofactors] using
      Integration.normalization7 x y (10 : Fin 12)
  have h11 : Rank7.L11 (Integration.M7 x) (Integration.N7 y) =
      9 * Integration.outputs7 x y 11 := by
    simpa [Integration.forms7, PrimePatterns.Rank7.cofactors] using
      Integration.normalization7 x y (11 : Fin 12)
  refine ⟨?_, ?_, ?_⟩
  all_goals
    simp only [Rank7.F, Rank7.H, Rank7.J, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    ring

/-- The genuine coefficient is the cast of this explicit integer. -/
def aInteger7 (x y : ℤ) : ℤ := 945613440 *
    (PrimePatterns.Rank7.outputs 0).eval x y *
    (PrimePatterns.Rank7.outputs 1).eval x y *
    (PrimePatterns.Rank7.outputs 2).eval x y *
    (PrimePatterns.Rank7.outputs 3).eval x y

theorem aInteger7_cast (x y : ℤ) :
    (aInteger7 x y : ℚ) = Rank7.a (Integration.M7 x) (Integration.N7 y) := by
  rcases lattice7_factorGroups x y with ⟨hF, hH, hJ⟩
  simp only [aInteger7, Int.cast_mul, Int.cast_ofNat,
    Rank7.a, hF, Integration.outputs7]
  ring

/-- The genuine coefficient is the cast of this explicit integer. -/
def bInteger7 (x y : ℤ) : ℤ := -445084803072 *
    (PrimePatterns.Rank7.outputs 0).eval x y *
    (PrimePatterns.Rank7.outputs 1).eval x y *
    (PrimePatterns.Rank7.outputs 2).eval x y *
    (PrimePatterns.Rank7.outputs 3).eval x y *
    (PrimePatterns.Rank7.outputs 4).eval x y *
    (PrimePatterns.Rank7.outputs 5).eval x y *
    (PrimePatterns.Rank7.outputs 6).eval x y *
    (PrimePatterns.Rank7.outputs 7).eval x y

theorem bInteger7_cast (x y : ℤ) :
    (bInteger7 x y : ℚ) = Rank7.b (Integration.M7 x) (Integration.N7 y) := by
  rcases lattice7_factorGroups x y with ⟨hF, hH, hJ⟩
  simp only [bInteger7, Int.cast_mul, Int.cast_ofNat, Int.cast_neg,
    Rank7.b, hF, hH, Integration.outputs7]
  ring

/-- The genuine coefficient is the cast of this explicit integer. -/
def cInteger7 (x y : ℤ) : ℤ := 26121388032 *
    (PrimePatterns.Rank7.outputs 0).eval x y *
    (PrimePatterns.Rank7.outputs 1).eval x y *
    (PrimePatterns.Rank7.outputs 2).eval x y *
    (PrimePatterns.Rank7.outputs 3).eval x y *
    (PrimePatterns.Rank7.outputs 8).eval x y *
    (PrimePatterns.Rank7.outputs 9).eval x y *
    (PrimePatterns.Rank7.outputs 10).eval x y *
    (PrimePatterns.Rank7.outputs 11).eval x y

theorem cInteger7_cast (x y : ℤ) :
    (cInteger7 x y : ℚ) = Rank7.c (Integration.M7 x) (Integration.N7 y) := by
  rcases lattice7_factorGroups x y with ⟨hF, hH, hJ⟩
  simp only [cInteger7, Int.cast_mul, Int.cast_ofNat,
    Rank7.c, hF, hJ, Integration.outputs7]
  ring

theorem lattice5E_constant_prime_support {p : ℕ} (hp : p.Prime)
    (hd : (p : ℤ) ∣ (-18662400 : ℤ)) : p = 2 ∨ p = 3 ∨ p = 5 := by
  have hprime : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  have hfactor : (-18662400 : ℤ) = -((2 : ℤ) ^ 10 * (3 : ℤ) ^ 6 * (5 : ℤ) ^ 2) := by norm_num
  rw [hfactor, dvd_neg] at hd
  simp only [hprime.dvd_mul] at hd
  rcases hd with ((h0 | h1) | h2)
  · exact Or.inl (prime_dvd_nat_prime_power hp (by norm_num : Nat.Prime 2) h0)
  · exact Or.inr (Or.inl (prime_dvd_nat_prime_power hp (by norm_num : Nat.Prime 3) h1))
  · exact Or.inr (Or.inr (prime_dvd_nat_prime_power hp (by norm_num : Nat.Prime 5) h2))


theorem lattice5Ep_constant_prime_support {p : ℕ} (hp : p.Prime)
    (hd : (p : ℤ) ∣ (597196800 : ℤ)) : p = 2 ∨ p = 3 ∨ p = 5 := by
  have hprime : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  have hfactor : (597196800 : ℤ) = (2 : ℤ) ^ 15 * (3 : ℤ) ^ 6 * (5 : ℤ) ^ 2 := by norm_num
  rw [hfactor] at hd
  simp only [hprime.dvd_mul] at hd
  rcases hd with ((h0 | h1) | h2)
  · exact Or.inl (prime_dvd_nat_prime_power hp (by norm_num : Nat.Prime 2) h0)
  · exact Or.inr (Or.inl (prime_dvd_nat_prime_power hp (by norm_num : Nat.Prime 3) h1))
  · exact Or.inr (Or.inr (prime_dvd_nat_prime_power hp (by norm_num : Nat.Prime 5) h2))


theorem lattice6E_constant_prime_support {p : ℕ} (hp : p.Prime)
    (hd : (p : ℤ) ∣ (-12544 : ℤ)) : p = 2 ∨ p = 7 := by
  have hprime : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  have hfactor : (-12544 : ℤ) = -((2 : ℤ) ^ 8 * (7 : ℤ) ^ 2) := by norm_num
  rw [hfactor, dvd_neg] at hd
  simp only [hprime.dvd_mul] at hd
  rcases hd with (h0 | h1)
  · exact Or.inl (prime_dvd_nat_prime_power hp (by norm_num : Nat.Prime 2) h0)
  · exact Or.inr (prime_dvd_nat_prime_power hp (by norm_num : Nat.Prime 7) h1)


theorem lattice6Ep_constant_prime_support {p : ℕ} (hp : p.Prime)
    (hd : (p : ℤ) ∣ (9144576 : ℤ)) : p = 2 ∨ p = 3 ∨ p = 7 := by
  have hprime : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  have hfactor : (9144576 : ℤ) = (2 : ℤ) ^ 8 * (3 : ℤ) ^ 6 * (7 : ℤ) ^ 2 := by norm_num
  rw [hfactor] at hd
  simp only [hprime.dvd_mul] at hd
  rcases hd with ((h0 | h1) | h2)
  · exact Or.inl (prime_dvd_nat_prime_power hp (by norm_num : Nat.Prime 2) h0)
  · exact Or.inr (Or.inl (prime_dvd_nat_prime_power hp (by norm_num : Nat.Prime 3) h1))
  · exact Or.inr (Or.inr (prime_dvd_nat_prime_power hp (by norm_num : Nat.Prime 7) h2))


theorem lattice7E_constant_prime_support {p : ℕ} (hp : p.Prime)
    (hd : (p : ℤ) ∣ (-445084803072 : ℤ)) : p = 2 ∨ p = 3 ∨ p = 7 ∨ p = 13 := by
  have hprime : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  have hfactor : (-445084803072 : ℤ) = -((2 : ℤ) ^ 13 * (3 : ℤ) ^ 8 * (7 : ℤ) ^ 2 * (13 : ℤ) ^ 2) := by norm_num
  rw [hfactor, dvd_neg] at hd
  simp only [hprime.dvd_mul] at hd
  rcases hd with (((h0 | h1) | h2) | h3)
  · exact Or.inl (prime_dvd_nat_prime_power hp (by norm_num : Nat.Prime 2) h0)
  · exact Or.inr (Or.inl (prime_dvd_nat_prime_power hp (by norm_num : Nat.Prime 3) h1))
  · exact Or.inr (Or.inr (Or.inl (prime_dvd_nat_prime_power hp (by norm_num : Nat.Prime 7) h2)))
  · exact Or.inr (Or.inr (Or.inr (prime_dvd_nat_prime_power hp (by norm_num : Nat.Prime 13) h3)))


theorem lattice7Ep_constant_prime_support {p : ℕ} (hp : p.Prime)
    (hd : (p : ℤ) ∣ (26121388032 : ℤ)) : p = 2 ∨ p = 3 := by
  have hprime : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  have hfactor : (26121388032 : ℤ) = (2 : ℤ) ^ 14 * (3 : ℤ) ^ 13 := by norm_num
  rw [hfactor] at hd
  simp only [hprime.dvd_mul] at hd
  rcases hd with (h0 | h1)
  · exact Or.inl (prime_dvd_nat_prime_power hp (by norm_num : Nat.Prime 2) h0)
  · exact Or.inr (prime_dvd_nat_prime_power hp (by norm_num : Nat.Prime 3) h1)


/-- Every prime divisor of the integral rank-5 b coefficient
belongs to the corresponding ordered prime column family. -/
theorem PrimeSpecialization5.bInteger_prime_support {x y : ℤ}
    (h : PrimeSpecialization5 x y) {p : ℕ} (hp : p.Prime)
    (hd : (p : ℤ) ∣ bInteger5 x y) :
    p ∈ Set.range (primeColumns5E h.primes) := by
  have hprime : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  simp only [bInteger5, hprime.dvd_mul] at hd
  rcases hd with ((((((((hc | h0) | h1) | h2) | h3) | h4) | h5) | h6) | h7)
  · rcases lattice5E_constant_prime_support hp hc with hq2 | hq3 | hq5
    · refine ⟨(0 : Fin 11), ?_⟩
      change (2 : ℕ) = p
      exact hq2.symm
    · refine ⟨(1 : Fin 11), ?_⟩
      change (3 : ℕ) = p
      exact hq3.symm
    · refine ⟨(2 : Fin 11), ?_⟩
      change (5 : ℕ) = p
      exact hq5.symm
  · refine ⟨(3 : Fin 11), ?_⟩
    change h.primes (0 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (0 : Fin 12)).mp h0).symm
  · refine ⟨(4 : Fin 11), ?_⟩
    change h.primes (1 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (1 : Fin 12)).mp h1).symm
  · refine ⟨(5 : Fin 11), ?_⟩
    change h.primes (2 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (2 : Fin 12)).mp h2).symm
  · refine ⟨(6 : Fin 11), ?_⟩
    change h.primes (3 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (3 : Fin 12)).mp h3).symm
  · refine ⟨(7 : Fin 11), ?_⟩
    change h.primes (4 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (4 : Fin 12)).mp h4).symm
  · refine ⟨(8 : Fin 11), ?_⟩
    change h.primes (5 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (5 : Fin 12)).mp h5).symm
  · refine ⟨(9 : Fin 11), ?_⟩
    change h.primes (6 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (6 : Fin 12)).mp h6).symm
  · refine ⟨(10 : Fin 11), ?_⟩
    change h.primes (7 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (7 : Fin 12)).mp h7).symm


/-- Every prime divisor of the integral rank-5 c coefficient
belongs to the corresponding ordered prime column family. -/
theorem PrimeSpecialization5.cInteger_prime_support {x y : ℤ}
    (h : PrimeSpecialization5 x y) {p : ℕ} (hp : p.Prime)
    (hd : (p : ℤ) ∣ cInteger5 x y) :
    p ∈ Set.range (primeColumns5Ep h.primes) := by
  have hprime : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  simp only [cInteger5, hprime.dvd_mul] at hd
  rcases hd with ((((((((hc | h0) | h1) | h2) | h3) | h8) | h9) | h10) | h11)
  · rcases lattice5Ep_constant_prime_support hp hc with hq2 | hq3 | hq5
    · refine ⟨(0 : Fin 11), ?_⟩
      change (2 : ℕ) = p
      exact hq2.symm
    · refine ⟨(1 : Fin 11), ?_⟩
      change (3 : ℕ) = p
      exact hq3.symm
    · refine ⟨(2 : Fin 11), ?_⟩
      change (5 : ℕ) = p
      exact hq5.symm
  · refine ⟨(3 : Fin 11), ?_⟩
    change h.primes (0 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (0 : Fin 12)).mp h0).symm
  · refine ⟨(4 : Fin 11), ?_⟩
    change h.primes (1 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (1 : Fin 12)).mp h1).symm
  · refine ⟨(5 : Fin 11), ?_⟩
    change h.primes (2 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (2 : Fin 12)).mp h2).symm
  · refine ⟨(6 : Fin 11), ?_⟩
    change h.primes (3 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (3 : Fin 12)).mp h3).symm
  · refine ⟨(7 : Fin 11), ?_⟩
    change h.primes (8 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (8 : Fin 12)).mp h8).symm
  · refine ⟨(8 : Fin 11), ?_⟩
    change h.primes (9 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (9 : Fin 12)).mp h9).symm
  · refine ⟨(9 : Fin 11), ?_⟩
    change h.primes (10 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (10 : Fin 12)).mp h10).symm
  · refine ⟨(10 : Fin 11), ?_⟩
    change h.primes (11 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (11 : Fin 12)).mp h11).symm


/-- Every prime divisor of the integral rank-6 b coefficient
belongs to the corresponding ordered prime column family. -/
theorem PrimeSpecialization6.bInteger_prime_support {x y : ℤ}
    (h : PrimeSpecialization6 x y) {p : ℕ} (hp : p.Prime)
    (hd : (p : ℤ) ∣ bInteger6 x y) :
    p ∈ Set.range (primeColumns6E h.primes) := by
  have hprime : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  simp only [bInteger6, hprime.dvd_mul] at hd
  rcases hd with ((((((((hc | h0) | h1) | h2) | h3) | h4) | h5) | h6) | h7)
  · rcases lattice6E_constant_prime_support hp hc with hq2 | hq7
    · refine ⟨(0 : Fin 11), ?_⟩
      change (2 : ℕ) = p
      exact hq2.symm
    · refine ⟨(2 : Fin 11), ?_⟩
      change (7 : ℕ) = p
      exact hq7.symm
  · refine ⟨(3 : Fin 11), ?_⟩
    change h.primes (0 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (0 : Fin 12)).mp h0).symm
  · refine ⟨(4 : Fin 11), ?_⟩
    change h.primes (1 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (1 : Fin 12)).mp h1).symm
  · refine ⟨(5 : Fin 11), ?_⟩
    change h.primes (2 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (2 : Fin 12)).mp h2).symm
  · refine ⟨(6 : Fin 11), ?_⟩
    change h.primes (3 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (3 : Fin 12)).mp h3).symm
  · refine ⟨(7 : Fin 11), ?_⟩
    change h.primes (4 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (4 : Fin 12)).mp h4).symm
  · refine ⟨(8 : Fin 11), ?_⟩
    change h.primes (5 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (5 : Fin 12)).mp h5).symm
  · refine ⟨(9 : Fin 11), ?_⟩
    change h.primes (6 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (6 : Fin 12)).mp h6).symm
  · refine ⟨(10 : Fin 11), ?_⟩
    change h.primes (7 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (7 : Fin 12)).mp h7).symm


/-- Every prime divisor of the integral rank-6 c coefficient
belongs to the corresponding ordered prime column family. -/
theorem PrimeSpecialization6.cInteger_prime_support {x y : ℤ}
    (h : PrimeSpecialization6 x y) {p : ℕ} (hp : p.Prime)
    (hd : (p : ℤ) ∣ cInteger6 x y) :
    p ∈ Set.range (primeColumns6Ep h.primes) := by
  have hprime : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  simp only [cInteger6, hprime.dvd_mul] at hd
  rcases hd with ((((((((hc | h0) | h1) | h2) | h3) | h8) | h9) | h10) | h11)
  · rcases lattice6Ep_constant_prime_support hp hc with hq2 | hq3 | hq7
    · refine ⟨(0 : Fin 11), ?_⟩
      change (2 : ℕ) = p
      exact hq2.symm
    · refine ⟨(1 : Fin 11), ?_⟩
      change (3 : ℕ) = p
      exact hq3.symm
    · refine ⟨(2 : Fin 11), ?_⟩
      change (7 : ℕ) = p
      exact hq7.symm
  · refine ⟨(3 : Fin 11), ?_⟩
    change h.primes (0 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (0 : Fin 12)).mp h0).symm
  · refine ⟨(4 : Fin 11), ?_⟩
    change h.primes (1 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (1 : Fin 12)).mp h1).symm
  · refine ⟨(5 : Fin 11), ?_⟩
    change h.primes (2 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (2 : Fin 12)).mp h2).symm
  · refine ⟨(6 : Fin 11), ?_⟩
    change h.primes (3 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (3 : Fin 12)).mp h3).symm
  · refine ⟨(7 : Fin 11), ?_⟩
    change h.primes (8 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (8 : Fin 12)).mp h8).symm
  · refine ⟨(8 : Fin 11), ?_⟩
    change h.primes (9 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (9 : Fin 12)).mp h9).symm
  · refine ⟨(9 : Fin 11), ?_⟩
    change h.primes (10 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (10 : Fin 12)).mp h10).symm
  · refine ⟨(10 : Fin 11), ?_⟩
    change h.primes (11 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (11 : Fin 12)).mp h11).symm


/-- Every prime divisor of the integral rank-7 b coefficient
belongs to the corresponding ordered prime column family. -/
theorem PrimeSpecialization7.bInteger_prime_support {x y : ℤ}
    (h : PrimeSpecialization7 x y) {p : ℕ} (hp : p.Prime)
    (hd : (p : ℤ) ∣ bInteger7 x y) :
    p ∈ Set.range (primeColumns7E h.primes) := by
  have hprime : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  simp only [bInteger7, hprime.dvd_mul] at hd
  rcases hd with ((((((((hc | h0) | h1) | h2) | h3) | h4) | h5) | h6) | h7)
  · rcases lattice7E_constant_prime_support hp hc with hq2 | hq3 | hq7 | hq13
    · refine ⟨(0 : Fin 12), ?_⟩
      change (2 : ℕ) = p
      exact hq2.symm
    · refine ⟨(1 : Fin 12), ?_⟩
      change (3 : ℕ) = p
      exact hq3.symm
    · refine ⟨(2 : Fin 12), ?_⟩
      change (7 : ℕ) = p
      exact hq7.symm
    · refine ⟨(3 : Fin 12), ?_⟩
      change (13 : ℕ) = p
      exact hq13.symm
  · refine ⟨(4 : Fin 12), ?_⟩
    change h.primes (0 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (0 : Fin 12)).mp h0).symm
  · refine ⟨(5 : Fin 12), ?_⟩
    change h.primes (1 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (1 : Fin 12)).mp h1).symm
  · refine ⟨(6 : Fin 12), ?_⟩
    change h.primes (2 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (2 : Fin 12)).mp h2).symm
  · refine ⟨(7 : Fin 12), ?_⟩
    change h.primes (3 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (3 : Fin 12)).mp h3).symm
  · refine ⟨(8 : Fin 12), ?_⟩
    change h.primes (4 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (4 : Fin 12)).mp h4).symm
  · refine ⟨(9 : Fin 12), ?_⟩
    change h.primes (5 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (5 : Fin 12)).mp h5).symm
  · refine ⟨(10 : Fin 12), ?_⟩
    change h.primes (6 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (6 : Fin 12)).mp h6).symm
  · refine ⟨(11 : Fin 12), ?_⟩
    change h.primes (7 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (7 : Fin 12)).mp h7).symm


/-- Every prime divisor of the integral rank-7 c coefficient
belongs to the corresponding ordered prime column family. -/
theorem PrimeSpecialization7.cInteger_prime_support {x y : ℤ}
    (h : PrimeSpecialization7 x y) {p : ℕ} (hp : p.Prime)
    (hd : (p : ℤ) ∣ cInteger7 x y) :
    p ∈ Set.range (primeColumns7Ep h.primes) := by
  have hprime : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  simp only [cInteger7, hprime.dvd_mul] at hd
  rcases hd with ((((((((hc | h0) | h1) | h2) | h3) | h8) | h9) | h10) | h11)
  · rcases lattice7Ep_constant_prime_support hp hc with hq2 | hq3
    · refine ⟨(0 : Fin 12), ?_⟩
      change (2 : ℕ) = p
      exact hq2.symm
    · refine ⟨(1 : Fin 12), ?_⟩
      change (3 : ℕ) = p
      exact hq3.symm
  · refine ⟨(4 : Fin 12), ?_⟩
    change h.primes (0 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (0 : Fin 12)).mp h0).symm
  · refine ⟨(5 : Fin 12), ?_⟩
    change h.primes (1 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (1 : Fin 12)).mp h1).symm
  · refine ⟨(6 : Fin 12), ?_⟩
    change h.primes (2 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (2 : Fin 12)).mp h2).symm
  · refine ⟨(7 : Fin 12), ?_⟩
    change h.primes (3 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (3 : Fin 12)).mp h3).symm
  · refine ⟨(8 : Fin 12), ?_⟩
    change h.primes (8 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (8 : Fin 12)).mp h8).symm
  · refine ⟨(9 : Fin 12), ?_⟩
    change h.primes (9 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (9 : Fin 12)).mp h9).symm
  · refine ⟨(10 : Fin 12), ?_⟩
    change h.primes (10 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (10 : Fin 12)).mp h10).symm
  · refine ⟨(11 : Fin 12), ?_⟩
    change h.primes (11 : Fin 12) = p
    exact ((h.prime_dvd_output_iff hp (11 : Fin 12)).mp h11).symm


end RankCertificates
