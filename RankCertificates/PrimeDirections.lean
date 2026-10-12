module

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic

/-!
# Distinct prime pairs give distinct rational directions

The analytic prime-pattern input is not assumed here.  This file verifies
the elementary step that would take infinitely many pairs of distinct
natural primes to infinitely many rational projective directions.
-/

@[expose] public section

namespace RankCertificates.PrimeDirections

/-- Ordered pairs of distinct natural primes.  Primality implies positivity. -/
def primePairs : Set (ℕ × ℕ) := {v | v.1.Prime ∧ v.2.Prime ∧ v.1 ≠ v.2}

/-- The rational direction represented by an ordered pair. -/
def ratio (v : ℕ × ℕ) : ℚ := (v.1 : ℚ) / (v.2 : ℚ)

theorem prime_pair_eq_of_cross_mul_eq {p q p' q' : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hp' : p'.Prime) (hq' : q'.Prime)
    (hpq : p ≠ q) (h : p * q' = p' * q) : p = p' ∧ q = q' := by
  have hpp' : p ∣ p' := by
    have hdiv : p ∣ p' * q := by
      rw [← h]
      exact dvd_mul_right p q'
    rcases hp.dvd_mul.mp hdiv with hpp' | hpq'
    · exact hpp'
    · have heq : q = p := (hq.dvd_iff_eq hp.ne_one).mp hpq'
      exact (hpq heq.symm).elim
  have hqq' : q ∣ q' := by
    have hdiv : q ∣ p * q' := by
      rw [h]
      exact dvd_mul_left q p'
    rcases hq.dvd_mul.mp hdiv with hqp | hqq'
    · have heq : p = q := (hp.dvd_iff_eq hq.ne_one).mp hqp
      exact (hpq heq).elim
    · exact hqq'
  exact ⟨((hp'.dvd_iff_eq hp.ne_one).mp hpp').symm,
    ((hq'.dvd_iff_eq hq.ne_one).mp hqq').symm⟩

theorem prime_pair_eq_of_ratio_eq {p q p' q' : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hp' : p'.Prime) (hq' : q'.Prime)
    (hpq : p ≠ q) (h : (p : ℚ) / (q : ℚ) = (p' : ℚ) / (q' : ℚ)) :
    p = p' ∧ q = q' := by
  apply prime_pair_eq_of_cross_mul_eq hp hq hp' hq' hpq
  have hcross : (p : ℚ) * (q' : ℚ) = (p' : ℚ) * (q : ℚ) :=
    (div_eq_div_iff (Nat.cast_ne_zero.mpr hq.ne_zero)
      (Nat.cast_ne_zero.mpr hq'.ne_zero)).mp h
  exact_mod_cast hcross

theorem ratio_injOn_primePairs : Set.InjOn ratio primePairs := by
  rintro ⟨p, q⟩ ⟨hp, hq, hpq⟩ ⟨p', q'⟩ ⟨hp', hq', _⟩ h
  obtain ⟨hpp', hqq'⟩ := prime_pair_eq_of_ratio_eq hp hq hp' hq' hpq h
  exact Prod.ext hpp' hqq'

theorem infinite_ratio_image {S : Set (ℕ × ℕ)} (hS : S.Infinite)
    (hprimes : S ⊆ primePairs) : (ratio '' S).Infinite := by
  apply hS.image
  intro v hv w hw h
  exact ratio_injOn_primePairs (hprimes hv) (hprimes hw) h

end RankCertificates.PrimeDirections
