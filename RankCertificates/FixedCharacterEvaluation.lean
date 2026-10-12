module

public import RankCertificates.MovingPrimeCharacters
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

@[expose] public section

/-! Fixed integral characters can be checked through a square-part
certificate and one finite CRT residue.  Jacobi periodicity includes the
quadratic reciprocity and supplementary-law signs. -/

namespace RankCertificates.FixedCharacterEvaluation

/-- Removing a rationally irrelevant integral square reduces a character
to a finite Jacobi-symbol computation. -/
theorem legendre_via_squarepart (p : ℕ) [Fact p.Prime]
    (c s d : ℤ) (r : ℕ) (hp : p ≠ 2)
    (hc : c = s * d ^ 2) (hu : (c : ZMod p) ≠ 0)
    (hr : p % (4 * s.natAbs) = r) :
    legendreSym p c = jacobiSym s r := by
  have hd : (d : ZMod p) ≠ 0 := by
    intro hz
    apply hu
    rw [hc]
    simp [hz]
  rw [hc, legendreSym.mul, legendreSym.sq_one' p hd, mul_one,
    jacobiSym.legendreSym.to_jacobiSym, jacobiSym.mod_right s
      (Nat.odd_iff.mpr ((Fact.out : p.Prime).eq_two_or_odd.resolve_left hp)), hr]

/-- Integer affine residues transfer to their positive natural prime. -/
theorem nat_residue_of_int_eq (p q r : ℕ) (z : ℤ)
    (hz : (p : ℤ) = z) (hr : z % (q : ℤ) = (r : ℤ)) :
    p % q = r := by
  rw [← hz] at hr
  exact_mod_cast hr

end RankCertificates.FixedCharacterEvaluation
