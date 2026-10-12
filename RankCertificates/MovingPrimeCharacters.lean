module

public import RankCertificates.LocalCharacterRows
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

@[expose] public section

/-! Affine determinant identities reduce all moving-prime Legendre symbols
needed by two-isogeny descent to fixed integer characters and one common
character. The reductions use genuine residue fields and quadratic reciprocity. -/

namespace RankCertificates.MovingPrimeCharacters

/-- Primitivity and a distinct distinguished prime force the affine
`N` coefficient to be a unit at its moving prime. No extra exclusion of
the prime divisors of that coefficient is needed. -/
theorem affine_b_not_dvd (p₀ pᵢ : ℕ) [Fact p₀.Prime] [Fact pᵢ.Prime]
    (M N C₀ Cᵢ aᵢ bᵢ : ℤ)
    (h₀ : C₀ * (p₀ : ℤ) = M)
    (hᵢ : Cᵢ * (pᵢ : ℤ) = aᵢ * M + bᵢ * N)
    (hprimitive : Int.gcd aᵢ bᵢ = 1)
    (hC₀ : ¬ (pᵢ : ℤ) ∣ C₀) (hne : pᵢ ≠ p₀) :
    ¬ (pᵢ : ℤ) ∣ bᵢ := by
  have hp : Prime (pᵢ : ℤ) := Int.prime_iff_natAbs_prime.mpr (by
    simpa using (Fact.out : pᵢ.Prime))
  have hM : ¬ (pᵢ : ℤ) ∣ M := by
    rw [← h₀, hp.dvd_mul]
    intro h
    rcases h with hc | hd
    · exact hC₀ hc
    · have heq : pᵢ = p₀ := (Nat.prime_dvd_prime_iff_eq
        (Fact.out : pᵢ.Prime) (Fact.out : p₀.Prime)).mp
          (Int.natCast_dvd_natCast.mp hd)
      exact hne heq
  intro hb
  have ha : ¬ (pᵢ : ℤ) ∣ aᵢ := by
    intro ha
    exact hp.not_isUnit ((Int.isCoprime_iff_gcd_eq_one.mpr hprimitive).isUnit_of_dvd' ha hb)
  have hd : (pᵢ : ℤ) ∣ aᵢ * M := by
    have hsum : (pᵢ : ℤ) ∣ aᵢ * M + bᵢ * N := by
      rw [← hᵢ]
      exact dvd_mul_left _ _
    have hterm : (pᵢ : ℤ) ∣ bᵢ * N := dvd_mul_of_dvd_left hb N
    simpa only [add_sub_cancel_right] using hsum.sub hterm
  exact hM ((hp.dvd_mul.mp hd).resolve_left ha)

/-- The residue-field version of the primitive affine coefficient lemma. -/
theorem affine_b_unit (p₀ pᵢ : ℕ) [Fact p₀.Prime] [Fact pᵢ.Prime]
    (M N C₀ Cᵢ aᵢ bᵢ : ℤ)
    (h₀ : C₀ * (p₀ : ℤ) = M)
    (hᵢ : Cᵢ * (pᵢ : ℤ) = aᵢ * M + bᵢ * N)
    (hprimitive : Int.gcd aᵢ bᵢ = 1)
    (hC₀ : (C₀ : ZMod pᵢ) ≠ 0) (hne : pᵢ ≠ p₀) :
    (bᵢ : ZMod pᵢ) ≠ 0 := by
  rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd] at hC₀ ⊢
  exact affine_b_not_dvd p₀ pᵢ M N C₀ Cᵢ aᵢ bᵢ h₀ hᵢ hprimitive hC₀ hne

/-- The normalized unit of a prime at itself is one. -/
theorem unitCharacter_prime_self (p : ℕ) [Fact p.Prime] :
    LocalValuations.unitCharacter p (p : ℚ) = 1 := by
  have hp : p.Prime := Fact.out
  have hp₀ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  simp only [LocalValuations.unitCharacter, LocalValuations.unitResidue,
    LocalValuations.normalizedUnit, padicValRat.self hp.one_lt, zpow_one,
    div_self hp₀]
  have hr : LocalValuations.rationalResidue p 1 = 1 := by
    simpa using LocalValuations.rationalResidue_int p 1
  rw [hr]
  simp

/-- A prime's self-coordinate contributes zero normalized-unit character bit. -/
theorem unitCharacterParity_prime_self (p : ℕ) [Fact p.Prime] :
    unitCharacterParity p (Additive.ofMul (rationalSquareClass (p : ℚ))) = 0 := by
  have hp₀ : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [unitCharacterParity_apply p hp₀, unitCharacter_prime_self,
    quadraticCharacterBit_one]

/-- At a different prime, a prime column's normalized character bit is
the ordinary Legendre-symbol bit. -/
theorem unitCharacterParity_prime_other (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≠ q) :
    unitCharacterParity p (Additive.ofMul (rationalSquareClass (q : ℚ))) =
      quadraticCharacterBit (legendreSym p (q : ℤ)) := by
  have hq₀ : (q : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hd : ¬ (p : ℤ) ∣ (q : ℤ) := by
    rw [Int.natCast_dvd_natCast, Nat.prime_dvd_prime_iff_eq
      (Fact.out : p.Prime) (Fact.out : q.Prime)]
    exact hpq
  rw [unitCharacterParity_apply p hq₀]
  rw [← LocalValuations.unitCharacter_int_of_not_dvd p hd]
  norm_cast

/-- Equal integral residues have equal Legendre symbols. -/
theorem legendre_eq_of_residue_eq (p : ℕ) [Fact p.Prime] {u v : ℤ}
    (h : (u : ZMod p) = (v : ZMod p)) : legendreSym p u = legendreSym p v := by
  exact congrArg (quadraticChar (ZMod p)) h

/-- Distinct prime arguments have nonzero Legendre symbol. -/
theorem legendre_prime_ne_zero (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hne : p ≠ q) : legendreSym p (q : ℤ) ≠ 0 := by
  apply (legendreSym.eq_zero_iff p (q : ℤ)).not.mpr
  simpa using ZMod.prime_ne_zero p q hne

/-- At the prime belonging to `M`, another affine form has the character
of its `N` coefficient times the common character of `N`. -/
theorem base_affine_symbol (p₀ p : ℕ) [Fact p₀.Prime]
    (M N C₀ C a b : ℤ)
    (h₀ : C₀ * (p₀ : ℤ) = M)
    (h : C * (p : ℤ) = a * M + b * N)
    (hC : (C : ZMod p₀) ≠ 0) :
    legendreSym p₀ (p : ℤ) =
      legendreSym p₀ (b * C) * legendreSym p₀ N := by
  have hrel : C ^ 2 * (p : ℤ) = b * C * N + C * a * C₀ * (p₀ : ℤ) := by
    linear_combination C * h - C * a * h₀
  have hres : ((C ^ 2 * (p : ℤ) : ℤ) : ZMod p₀) = ((b * C * N : ℤ) : ZMod p₀) := by
    rw [hrel]
    simp
  have hs := legendre_eq_of_residue_eq p₀ hres
  rw [legendreSym.mul, legendreSym.sq_one' p₀ hC, one_mul, legendreSym.mul] at hs
  exact hs

/-- The base affine coefficient product must be a residue-field unit:
otherwise the distinct prime's Legendre symbol would vanish. -/
theorem base_affine_coeff_unit (p₀ p : ℕ) [Fact p₀.Prime] [Fact p.Prime]
    (M N C₀ C a b : ℤ)
    (h₀ : C₀ * (p₀ : ℤ) = M)
    (h : C * (p : ℤ) = a * M + b * N)
    (hC : (C : ZMod p₀) ≠ 0) (hne : p₀ ≠ p) :
    ((b * C : ℤ) : ZMod p₀) ≠ 0 := by
  have hs := base_affine_symbol p₀ p M N C₀ C a b h₀ h hC
  have hp : legendreSym p₀ (b * C) * legendreSym p₀ N ≠ 0 := by
    rw [← hs]
    exact legendre_prime_ne_zero p₀ p hne
  exact (legendreSym.eq_zero_iff p₀ (b * C)).not.mp ((mul_ne_zero_iff.mp hp).1)

/-- An affine determinant relates two moving-prime characters to the
character of the distinguished `M` prime. -/
theorem affine_pair_symbol (p₀ pᵢ pₖ : ℕ) [Fact pᵢ.Prime]
    (M N C₀ Cᵢ Cₖ aᵢ bᵢ aₖ bₖ : ℤ)
    (h₀ : C₀ * (p₀ : ℤ) = M)
    (hᵢ : Cᵢ * (pᵢ : ℤ) = aᵢ * M + bᵢ * N)
    (hₖ : Cₖ * (pₖ : ℤ) = aₖ * M + bₖ * N)
    (hunit : ((bᵢ * Cₖ : ℤ) : ZMod pᵢ) ≠ 0) :
    legendreSym pᵢ (pₖ : ℤ) =
      legendreSym pᵢ (bᵢ * Cₖ * (bᵢ * aₖ - bₖ * aᵢ) * C₀) *
        legendreSym pᵢ (p₀ : ℤ) := by
  have hrel : (bᵢ * Cₖ) ^ 2 * (pₖ : ℤ) =
      (bᵢ * Cₖ * (bᵢ * aₖ - bₖ * aᵢ) * C₀) * (p₀ : ℤ) +
        bᵢ * Cₖ * bₖ * Cᵢ * (pᵢ : ℤ) := by
    linear_combination bᵢ ^ 2 * Cₖ * hₖ - bᵢ * Cₖ * bₖ * hᵢ -
      bᵢ * Cₖ * (bᵢ * aₖ - bₖ * aᵢ) * h₀
  have hres : (((bᵢ * Cₖ) ^ 2 * (pₖ : ℤ) : ℤ) : ZMod pᵢ) =
      (((bᵢ * Cₖ * (bᵢ * aₖ - bₖ * aᵢ) * C₀) * (p₀ : ℤ) : ℤ) : ZMod pᵢ) := by
    rw [hrel]
    simp
  have hs := legendre_eq_of_residue_eq pᵢ hres
  rw [legendreSym.mul, legendreSym.sq_one' pᵢ hunit, one_mul, legendreSym.mul] at hs
  exact hs

/-- Nonvanishing of the distinct moving prime proves that the entire
determinant constant is a unit, without extra prime-exclusion hypotheses. -/
theorem affine_pair_constant_unit (p₀ pᵢ pₖ : ℕ) [Fact pᵢ.Prime] [Fact pₖ.Prime]
    (M N C₀ Cᵢ Cₖ aᵢ bᵢ aₖ bₖ : ℤ)
    (h₀ : C₀ * (p₀ : ℤ) = M)
    (hᵢ : Cᵢ * (pᵢ : ℤ) = aᵢ * M + bᵢ * N)
    (hₖ : Cₖ * (pₖ : ℤ) = aₖ * M + bₖ * N)
    (hunit : ((bᵢ * Cₖ : ℤ) : ZMod pᵢ) ≠ 0) (hne : pᵢ ≠ pₖ) :
    ((bᵢ * Cₖ * (bᵢ * aₖ - bₖ * aᵢ) * C₀ : ℤ) : ZMod pᵢ) ≠ 0 := by
  have hs := affine_pair_symbol p₀ pᵢ pₖ M N C₀ Cᵢ Cₖ aᵢ bᵢ aₖ bₖ h₀ hᵢ hₖ hunit
  have hp : legendreSym pᵢ (bᵢ * Cₖ * (bᵢ * aₖ - bₖ * aᵢ) * C₀) *
      legendreSym pᵢ (p₀ : ℤ) ≠ 0 := by
    rw [← hs]
    exact legendre_prime_ne_zero pᵢ pₖ hne
  exact (legendreSym.eq_zero_iff pᵢ _).not.mp ((mul_ne_zero_iff.mp hp).1)

/-- Quadratic reciprocity expresses every affine-pair character through
fixed integer characters and the single common symbol `(N / p₀)`. -/
theorem affine_pair_symbol_reciprocity (p₀ pᵢ pₖ : ℕ)
    [Fact p₀.Prime] [Fact pᵢ.Prime]
    (M N C₀ Cᵢ Cₖ aᵢ bᵢ aₖ bₖ : ℤ)
    (h₀ : C₀ * (p₀ : ℤ) = M)
    (hᵢ : Cᵢ * (pᵢ : ℤ) = aᵢ * M + bᵢ * N)
    (hₖ : Cₖ * (pₖ : ℤ) = aₖ * M + bₖ * N)
    (hunit : ((bᵢ * Cₖ : ℤ) : ZMod pᵢ) ≠ 0)
    (hCᵢ : (Cᵢ : ZMod p₀) ≠ 0) (hp₀ : p₀ ≠ 2) (hpᵢ : pᵢ ≠ 2) :
    legendreSym pᵢ (pₖ : ℤ) =
      legendreSym pᵢ (bᵢ * Cₖ * (bᵢ * aₖ - bₖ * aᵢ) * C₀) *
        (-1) ^ (p₀ / 2 * (pᵢ / 2)) *
        legendreSym p₀ (bᵢ * Cᵢ) * legendreSym p₀ N := by
  rw [affine_pair_symbol p₀ pᵢ pₖ M N C₀ Cᵢ Cₖ aᵢ bᵢ aₖ bₖ h₀ hᵢ hₖ hunit,
    legendreSym.quadratic_reciprocity' hp₀ hpᵢ,
    base_affine_symbol p₀ pᵢ M N C₀ Cᵢ aᵢ bᵢ h₀ hᵢ hCᵢ]
  ring

/-- A distinguished prime congruent to one modulo four removes the
reciprocity sign, as in the rank-five and rank-seven prime lattices. -/
theorem affine_pair_symbol_one_mod_four (p₀ pᵢ pₖ : ℕ)
    [Fact p₀.Prime] [Fact pᵢ.Prime]
    (M N C₀ Cᵢ Cₖ aᵢ bᵢ aₖ bₖ : ℤ)
    (h₀ : C₀ * (p₀ : ℤ) = M)
    (hᵢ : Cᵢ * (pᵢ : ℤ) = aᵢ * M + bᵢ * N)
    (hₖ : Cₖ * (pₖ : ℤ) = aₖ * M + bₖ * N)
    (hunit : ((bᵢ * Cₖ : ℤ) : ZMod pᵢ) ≠ 0)
    (hCᵢ : (Cᵢ : ZMod p₀) ≠ 0) (hp₀ : p₀ % 4 = 1) (hpᵢ : pᵢ ≠ 2) :
    legendreSym pᵢ (pₖ : ℤ) =
      legendreSym pᵢ (bᵢ * Cₖ * (bᵢ * aₖ - bₖ * aᵢ) * C₀) *
        legendreSym p₀ (bᵢ * Cᵢ) * legendreSym p₀ N := by
  rw [affine_pair_symbol p₀ pᵢ pₖ M N C₀ Cᵢ Cₖ aᵢ bᵢ aₖ bₖ h₀ hᵢ hₖ hunit,
    legendreSym.quadratic_reciprocity_one_mod_four hp₀ hpᵢ,
    base_affine_symbol p₀ pᵢ M N C₀ Cᵢ aᵢ bᵢ h₀ hᵢ hCᵢ]
  ring

end RankCertificates.MovingPrimeCharacters
