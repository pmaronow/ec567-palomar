module

public import RankCertificates.PrimePowerResidues

@[expose] public section

namespace RankCertificates.PartnerNormReduction

open LocalValuations PrimePowerResidues

/-- At an odd dyadic valuation of the original linear coefficient, a
nonzero partner coordinate cannot be a point with vanishing y. -/
theorem partner_y_ne_zero {a b x y : ℚ} (hb : padicValRat 2 b=1)
    (hx : x ≠ 0) (h : OnCurve (-2*a) (a^2-4*b) x y) : y ≠ 0 := by
  have hb0 : b ≠ 0 := by intro hz; rw [hz,padicValRat.zero] at hb; omega
  intro hy
  have heq : (x-a)^2=4*b := by
    have hh : x*((x-a)^2-4*b)=0 := by
      dsimp [OnCurve] at h
      rw [hy,zero_pow (by decide : (2:ℕ) ≠ 0)] at h
      linear_combination -h
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hx)
  have hxa : x-a ≠ 0 := by
    intro hh
    rw [hh,zero_pow (by decide : (2:ℕ) ≠ 0)] at heq
    exact (mul_ne_zero (by norm_num : (4:ℚ) ≠ 0) hb0) heq.symm
  have hv2 : padicValRat 2 (2:ℚ)=1 := padicValRat.self (by norm_num)
  have hv4 : padicValRat 2 (4:ℚ)=2 := by
    rw [show (4:ℚ)=(2:ℚ)^2 by norm_num,padicValRat.pow,hv2]
    norm_num
  have hv := congrArg (padicValRat 2) heq
  rw [padicValRat.pow,padicValRat.mul (by norm_num) hb0,hv4,hb] at hv
  omega

/-- The nonzero y partner equation gives an exact rational norm
representation, with no local approximation or solubility assumption. -/
theorem partner_norm_identity {a b x y : ℚ} (hy : y ≠ 0)
    (h : OnCurve (-2*a) (a^2-4*b) x y) :
    x=(x*(x-a)/y)^2-b*(2*x/y)^2 := by
  dsimp [OnCurve] at h
  field_simp
  linear_combination x*h

/-- An actual nonzero partner coordinate is a norm whenever the original
linear coefficient has odd dyadic valuation one. -/
theorem partner_norm_representation {a b x y : ℚ} (hb : padicValRat 2 b=1)
    (hx : x ≠ 0) (h : OnCurve (-2*a) (a^2-4*b) x y) :
    ∃ s t : ℚ, x=s^2-b*t^2 := by
  exact ⟨x*(x-a)/y,2*x/y,partner_norm_identity (partner_y_ne_zero hb hx h) h⟩

end RankCertificates.PartnerNormReduction
