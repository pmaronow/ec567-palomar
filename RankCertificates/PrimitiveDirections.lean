module

public import RankCertificates.PrimeDirections
public import RankCertificates.PrimePatterns
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.RingTheory.Int.Basic

/-! Primitive homogeneous integer pairs give distinct rational parameters. -/

@[expose] public section

namespace RankCertificates.PrimitiveDirections

def primitivePairs : Set (ℤ × ℤ) :=
  {v | 0 < v.2 ∧ Nat.Coprime v.1.natAbs v.2.natAbs}

def ratio (v : ℤ × ℤ) : ℚ := (v.1 : ℚ) / (v.2 : ℚ)

theorem ratio_injOn_primitivePairs : Set.InjOn ratio primitivePairs := by
  rintro ⟨m, n⟩ ⟨hn, hmn⟩ ⟨m', n'⟩ ⟨hn', hmn'⟩ h
  obtain ⟨hm, hn⟩ := Rat.div_int_inj hn hn' hmn hmn' h
  exact Prod.ext hm hn

theorem infinite_ratio_image {s : Set (ℤ × ℤ)} (hs : s.Infinite)
    (hprimitive : s ⊆ primitivePairs) : (ratio '' s).Infinite := by
  apply hs.image
  intro v hv w hw h
  exact ratio_injOn_primitivePairs (hprimitive hv) (hprimitive hw) h

theorem rank5_lattice_denominator_coprime54 (y : ℤ) :
    IsCoprime (54 : ℤ) (PrimePatterns.Rank5.N0 + PrimePatterns.Rank5.W * y) := by
  refine ⟨370080480 * y, -1, ?_⟩
  norm_num [PrimePatterns.Rank5.N0, PrimePatterns.Rank5.W]
  ring

/-- The first two distinct prime outputs force the rank-five pair to be primitive.
The denominator itself need not be prime. -/
theorem rank5_lattice_primitive (x y : ℤ) (p q : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (h0 : (PrimePatterns.Rank5.outputs 0).eval x y = (p : ℤ))
    (h1 : (PrimePatterns.Rank5.outputs 1).eval x y = (q : ℤ)) :
    Nat.Coprime (PrimePatterns.Rank5.M0 + PrimePatterns.Rank5.W * x).natAbs
      (PrimePatterns.Rank5.N0 + PrimePatterns.Rank5.W * y).natAbs := by
  let m := PrimePatterns.Rank5.M0 + PrimePatterns.Rank5.W * x
  let n := PrimePatterns.Rank5.N0 + PrimePatterns.Rank5.W * y
  have hm : m = 54 * (p : ℤ) := by
    have h := PrimePatterns.Rank5.normalization 0 x y
    rw [h0] at h
    simpa [m, PrimePatterns.Rank5.cofactors, PrimePatterns.Rank5.forms,
      PrimePatterns.LinearForm.eval] using h.symm
  have hn : n = 1188 * (p : ℤ) - q := by
    have h := PrimePatterns.Rank5.normalization 1 x y
    rw [h1] at h
    have h' : (q : ℤ) = 22 * m - n := by
      simpa [m, n, PrimePatterns.Rank5.cofactors, PrimePatterns.Rank5.forms,
        PrimePatterns.LinearForm.eval, sub_eq_add_neg, add_comm] using h
    rw [hm] at h'
    linarith
  have hpq' : IsCoprime (p : ℤ) (q : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa using (Nat.coprime_primes hp hq).mpr hpq
  have hpn : IsCoprime (p : ℤ) n := by
    obtain ⟨a, b, hab⟩ := hpq'
    refine ⟨a + 1188 * b, -b, ?_⟩
    rw [hn]
    linear_combination hab
  apply Int.isCoprime_iff_nat_coprime.mp
  change IsCoprime m n
  rw [hm]
  exact (rank5_lattice_denominator_coprime54 y).mul_left hpn

end RankCertificates.PrimitiveDirections
