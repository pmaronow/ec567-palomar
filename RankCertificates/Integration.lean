module

public import RankCertificates.Rank5
public import RankCertificates.Rank6
public import RankCertificates.Rank7
public import RankCertificates.PrimePatterns
public import RankCertificates.MatrixCertificates

@[expose] public section

/-!
# Bridges between algebraic curves, affine prime patterns, and binary masks

The coefficient tuples in `PrimePatterns` evaluate to precisely the linear
factors used in the three curve modules.  Each known binary mask evaluates,
in the displayed ordered rational columns, to the corresponding actual
point x-coordinate or torsion coefficient up to an explicit nonzero square.
These statements do not assert a descent homomorphism or Mordell–Weil rank.
-/

namespace RankCertificates.Integration

open scoped BigOperators

/-- Evaluate a least-significant-bit-first mask in an ordered multiplicative
column basis.  It uses the same `Nat.testBit` convention as `Binary.vector`. -/
def maskValueFrom (code offset : ℕ) : List ℚ → ℚ
  | [] => 1
  | column :: columns =>
      (if code.testBit offset then column else 1) * maskValueFrom code (offset + 1) columns

/-- A mask product, starting at bit zero. -/
def maskValue (columns : List ℚ) (code : ℕ) : ℚ := maskValueFrom code 0 columns

def forms5 (M N : ℚ) : Fin 12 → ℚ := ![Rank5.L0 M N, Rank5.L1 M N, Rank5.L2 M N, Rank5.L3 M N, Rank5.L4 M N, Rank5.L5 M N, Rank5.L6 M N, Rank5.L7 M N, Rank5.L8 M N, Rank5.L9 M N, Rank5.L10 M N, Rank5.L11 M N]

theorem forms5_cast (m n : ℤ) (i : Fin 12) :
    forms5 (m : ℚ) (n : ℚ) i = ((PrimePatterns.Rank5.forms i).eval m n : ℚ) := by
  fin_cases i <;> simp [forms5, Rank5.L0, Rank5.L1, Rank5.L2, Rank5.L3, Rank5.L4, Rank5.L5, Rank5.L6, Rank5.L7, Rank5.L8, Rank5.L9, Rank5.L10, Rank5.L11, PrimePatterns.Rank5.forms,
    PrimePatterns.LinearForm.eval] <;> ring

def M5 (x : ℤ) : ℚ := ((PrimePatterns.Rank5.M0 + PrimePatterns.Rank5.W * x : ℤ) : ℚ)
def N5 (y : ℤ) : ℚ := ((PrimePatterns.Rank5.N0 + PrimePatterns.Rank5.W * y : ℤ) : ℚ)
def outputs5 (x y : ℤ) (i : Fin 12) : ℚ := ((PrimePatterns.Rank5.outputs i).eval x y : ℚ)

theorem normalization5 (x y : ℤ) (i : Fin 12) :
    forms5 (M5 x) (N5 y) i = (PrimePatterns.Rank5.cofactors i : ℚ) * outputs5 x y i := by
  dsimp [M5, N5, outputs5]
  rw [forms5_cast]
  exact_mod_cast (PrimePatterns.Rank5.normalization i x y).symm

theorem forms5_nonzero_on_lattice (x y : ℤ) (i : Fin 12) :
    forms5 (M5 x) (N5 y) i ≠ 0 := by
  dsimp [M5, N5]
  rw [forms5_cast]
  exact_mod_cast PrimePatterns.Rank5.forms_nonzero_on_lattice i x y

def columns5E (p : Fin 12 → ℚ) : List ℚ := [-1, 2, 3, 5, p 0, p 1, p 2, p 3, p 4, p 5, p 6, p 7]
def codes5E : Fin 3 → ℕ := ![4081, 243, 3274]
def coordinates5E (M N : ℚ) : Fin 3 → ℚ := ![Rank5.b M N, (Rank5.P1 M N).1, (Rank5.P2 M N).1]
def squareFactors5E : Fin 3 → ℚ := ![4320, 180, (4 / 7 : ℚ)]

theorem codes5E_match : List.ofFn codes5E = MatrixCertificates.Rank5.Egenerators := by
  decide +kernel

theorem squareFactors5E_nonzero (i : Fin 3) : squareFactors5E i ≠ 0 := by
  fin_cases i <;> norm_num [squareFactors5E]

theorem point_masks5E (M N : ℚ) (p : Fin 12 → ℚ)
    (h : ∀ i : Fin 12, forms5 M N i = (PrimePatterns.Rank5.cofactors i : ℚ) * p i)
    (i : Fin 3) :
    coordinates5E M N i = maskValue (columns5E p) (codes5E i) * (squareFactors5E i) ^ 2 := by
  have h0 : Rank5.L0 M N = 54 * p 0 := by
    simpa [forms5, PrimePatterns.Rank5.cofactors] using h 0
  have h1 : Rank5.L1 M N = 1 * p 1 := by
    simpa [forms5, PrimePatterns.Rank5.cofactors] using h 1
  have h2 : Rank5.L2 M N = 8 * p 2 := by
    simpa [forms5, PrimePatterns.Rank5.cofactors] using h 2
  have h3 : Rank5.L3 M N = 1 * p 3 := by
    simpa [forms5, PrimePatterns.Rank5.cofactors] using h 3
  have h4 : Rank5.L4 M N = 8 * p 4 := by
    simpa [forms5, PrimePatterns.Rank5.cofactors] using h 4
  have h5 : Rank5.L5 M N = 1 * p 5 := by
    simpa [forms5, PrimePatterns.Rank5.cofactors] using h 5
  have h6 : Rank5.L6 M N = 1 * p 6 := by
    simpa [forms5, PrimePatterns.Rank5.cofactors] using h 6
  have h7 : Rank5.L7 M N = 2 * p 7 := by
    simpa [forms5, PrimePatterns.Rank5.cofactors] using h 7
  fin_cases i <;> norm_num [coordinates5E, codes5E, squareFactors5E,
    Nat.testBit_eq_decide_div_mod_eq, maskValue, maskValueFrom, columns5E, Rank5.b, Rank5.c, Rank5.P1, Rank5.P2, Rank5.P'1, Rank5.P'2, Rank5.P'3, Rank5.F, Rank5.H, Rank5.J, Rank5.K, Rank5.R]
    <;> simp only [h0, h1, h2, h3, h4, h5, h6, h7] <;> ring

theorem point_masks5E_on_lattice (x y : ℤ) (i : Fin 3) :
    coordinates5E (M5 x) (N5 y) i =
      maskValue (columns5E (outputs5 x y)) (codes5E i) * (squareFactors5E i) ^ 2 :=
  point_masks5E (M5 x) (N5 y) (outputs5 x y) (normalization5 x y) i

def columns5Ep (p : Fin 12 → ℚ) : List ℚ := [-1, 2, 3, 5, p 0, p 1, p 2, p 3, p 8, p 9, p 10, p 11]
def codes5Ep : Fin 4 → ℕ := ![4082, 3840, 824, 1378]
def coordinates5Ep (M N : ℚ) : Fin 4 → ℚ := ![Rank5.c M N, (Rank5.P'1 M N).1, (Rank5.P'2 M N).1, (Rank5.P'3 M N).1]
def squareFactors5Ep : Fin 4 → ℚ := ![17280, 24, 72, (160 / 7 : ℚ)]

theorem codes5Ep_match : List.ofFn codes5Ep = MatrixCertificates.Rank5.Epgenerators := by
  decide +kernel

theorem squareFactors5Ep_nonzero (i : Fin 4) : squareFactors5Ep i ≠ 0 := by
  fin_cases i <;> norm_num [squareFactors5Ep]

theorem point_masks5Ep (M N : ℚ) (p : Fin 12 → ℚ)
    (h : ∀ i : Fin 12, forms5 M N i = (PrimePatterns.Rank5.cofactors i : ℚ) * p i)
    (i : Fin 4) :
    coordinates5Ep M N i = maskValue (columns5Ep p) (codes5Ep i) * (squareFactors5Ep i) ^ 2 := by
  have h0 : Rank5.L0 M N = 54 * p 0 := by
    simpa [forms5, PrimePatterns.Rank5.cofactors] using h 0
  have h1 : Rank5.L1 M N = 1 * p 1 := by
    simpa [forms5, PrimePatterns.Rank5.cofactors] using h 1
  have h2 : Rank5.L2 M N = 8 * p 2 := by
    simpa [forms5, PrimePatterns.Rank5.cofactors] using h 2
  have h3 : Rank5.L3 M N = 1 * p 3 := by
    simpa [forms5, PrimePatterns.Rank5.cofactors] using h 3
  have h8 : Rank5.L8 M N = 4 * p 8 := by
    simpa [forms5, PrimePatterns.Rank5.cofactors] using h 8
  have h9 : Rank5.L9 M N = 1 * p 9 := by
    simpa [forms5, PrimePatterns.Rank5.cofactors] using h 9
  have h10 : Rank5.L10 M N = 1 * p 10 := by
    simpa [forms5, PrimePatterns.Rank5.cofactors] using h 10
  have h11 : Rank5.L11 M N = 6 * p 11 := by
    simpa [forms5, PrimePatterns.Rank5.cofactors] using h 11
  fin_cases i <;> norm_num [coordinates5Ep, codes5Ep, squareFactors5Ep,
    Nat.testBit_eq_decide_div_mod_eq, maskValue, maskValueFrom, columns5Ep, Rank5.b, Rank5.c, Rank5.P1, Rank5.P2, Rank5.P'1, Rank5.P'2, Rank5.P'3, Rank5.F, Rank5.H, Rank5.J, Rank5.K, Rank5.R]
    <;> simp only [h0, h1, h2, h3, h8, h9, h10, h11] <;> (try simp only [(show M = 54 * p 0 from h0)]) <;> ring

theorem point_masks5Ep_on_lattice (x y : ℤ) (i : Fin 4) :
    coordinates5Ep (M5 x) (N5 y) i =
      maskValue (columns5Ep (outputs5 x y)) (codes5Ep i) * (squareFactors5Ep i) ^ 2 :=
  point_masks5Ep (M5 x) (N5 y) (outputs5 x y) (normalization5 x y) i

theorem products5_nonzero_on_lattice (x y : ℤ) :
    Rank5.F (M5 x) (N5 y) ≠ 0 ∧ Rank5.H (M5 x) (N5 y) ≠ 0 ∧ Rank5.J (M5 x) (N5 y) ≠ 0 := by
  have h0 : Rank5.L0 (M5 x) (N5 y) ≠ 0 := by
    simpa [forms5] using forms5_nonzero_on_lattice x y 0
  have h1 : Rank5.L1 (M5 x) (N5 y) ≠ 0 := by
    simpa [forms5] using forms5_nonzero_on_lattice x y 1
  have h2 : Rank5.L2 (M5 x) (N5 y) ≠ 0 := by
    simpa [forms5] using forms5_nonzero_on_lattice x y 2
  have h3 : Rank5.L3 (M5 x) (N5 y) ≠ 0 := by
    simpa [forms5] using forms5_nonzero_on_lattice x y 3
  have h4 : Rank5.L4 (M5 x) (N5 y) ≠ 0 := by
    simpa [forms5] using forms5_nonzero_on_lattice x y 4
  have h5 : Rank5.L5 (M5 x) (N5 y) ≠ 0 := by
    simpa [forms5] using forms5_nonzero_on_lattice x y 5
  have h6 : Rank5.L6 (M5 x) (N5 y) ≠ 0 := by
    simpa [forms5] using forms5_nonzero_on_lattice x y 6
  have h7 : Rank5.L7 (M5 x) (N5 y) ≠ 0 := by
    simpa [forms5] using forms5_nonzero_on_lattice x y 7
  have h8 : Rank5.L8 (M5 x) (N5 y) ≠ 0 := by
    simpa [forms5] using forms5_nonzero_on_lattice x y 8
  have h9 : Rank5.L9 (M5 x) (N5 y) ≠ 0 := by
    simpa [forms5] using forms5_nonzero_on_lattice x y 9
  have h10 : Rank5.L10 (M5 x) (N5 y) ≠ 0 := by
    simpa [forms5] using forms5_nonzero_on_lattice x y 10
  have h11 : Rank5.L11 (M5 x) (N5 y) ≠ 0 := by
    simpa [forms5] using forms5_nonzero_on_lattice x y 11
  exact ⟨mul_ne_zero (mul_ne_zero (mul_ne_zero h0 h1) h2) h3,
    mul_ne_zero (mul_ne_zero (mul_ne_zero h4 h5) h6) h7,
    mul_ne_zero (mul_ne_zero (mul_ne_zero h8 h9) h10) h11⟩

theorem elliptic_pair5_on_lattice (x y : ℤ) :
    (Rank5.E (M5 x) (N5 y)).IsElliptic ∧ (Rank5.E' (M5 x) (N5 y)).IsElliptic := by
  obtain ⟨hF, hH, hJ⟩ := products5_nonzero_on_lattice x y
  exact ⟨Rank5.E_isElliptic (M5 x) (N5 y) hF hH hJ, Rank5.E'_isElliptic (M5 x) (N5 y) hF hH hJ⟩

def forms6 (M N : ℚ) : Fin 12 → ℚ := ![Rank6.L0 M N, Rank6.L1 M N, Rank6.L2 M N, Rank6.L3 M N, Rank6.L4 M N, Rank6.L5 M N, Rank6.L6 M N, Rank6.L7 M N, Rank6.L8 M N, Rank6.L9 M N, Rank6.L10 M N, Rank6.L11 M N]

theorem forms6_cast (m n : ℤ) (i : Fin 12) :
    forms6 (m : ℚ) (n : ℚ) i = ((PrimePatterns.Rank6.forms i).eval m n : ℚ) := by
  fin_cases i <;> simp [forms6, Rank6.L0, Rank6.L1, Rank6.L2, Rank6.L3, Rank6.L4, Rank6.L5, Rank6.L6, Rank6.L7, Rank6.L8, Rank6.L9, Rank6.L10, Rank6.L11, PrimePatterns.Rank6.forms,
    PrimePatterns.LinearForm.eval] <;> ring

def M6 (x : ℤ) : ℚ := ((PrimePatterns.Rank6.M0 + PrimePatterns.Rank6.W * x : ℤ) : ℚ)
def N6 (y : ℤ) : ℚ := ((PrimePatterns.Rank6.N0 + PrimePatterns.Rank6.W * y : ℤ) : ℚ)
def outputs6 (x y : ℤ) (i : Fin 12) : ℚ := ((PrimePatterns.Rank6.outputs i).eval x y : ℚ)

theorem normalization6 (x y : ℤ) (i : Fin 12) :
    forms6 (M6 x) (N6 y) i = (PrimePatterns.Rank6.cofactors i : ℚ) * outputs6 x y i := by
  dsimp [M6, N6, outputs6]
  rw [forms6_cast]
  exact_mod_cast (PrimePatterns.Rank6.normalization i x y).symm

theorem forms6_nonzero_on_lattice (x y : ℤ) (i : Fin 12) :
    forms6 (M6 x) (N6 y) i ≠ 0 := by
  dsimp [M6, N6]
  rw [forms6_cast]
  exact_mod_cast PrimePatterns.Rank6.forms_nonzero_on_lattice i x y

def columns6E (p : Fin 12 → ℚ) : List ℚ := [-1, 2, 3, 7, p 0, p 1, p 2, p 3, p 4, p 5, p 6, p 7]
def codes6E : Fin 4 → ℕ := ![4081, 3848, 865, 1449]
def coordinates6E (M N : ℚ) : Fin 4 → ℚ := ![Rank6.b M N, Rank6.P1x M N, Rank6.P2x M N, Rank6.P3x M N]
def squareFactors6E : Fin 4 → ℚ := ![112, 2, 2, 20]

theorem codes6E_match : List.ofFn codes6E = MatrixCertificates.Rank6.Egenerators := by
  decide +kernel

theorem squareFactors6E_nonzero (i : Fin 4) : squareFactors6E i ≠ 0 := by
  fin_cases i <;> norm_num [squareFactors6E]

theorem point_masks6E (M N : ℚ) (p : Fin 12 → ℚ)
    (h : ∀ i : Fin 12, forms6 M N i = (PrimePatterns.Rank6.cofactors i : ℚ) * p i)
    (i : Fin 4) :
    coordinates6E M N i = maskValue (columns6E p) (codes6E i) * (squareFactors6E i) ^ 2 := by
  have h0 : Rank6.L0 M N = 1 * p 0 := by
    simpa [forms6, PrimePatterns.Rank6.cofactors] using h 0
  have h1 : Rank6.L1 M N = 1 * p 1 := by
    simpa [forms6, PrimePatterns.Rank6.cofactors] using h 1
  have h2 : Rank6.L2 M N = 1 * p 2 := by
    simpa [forms6, PrimePatterns.Rank6.cofactors] using h 2
  have h3 : Rank6.L3 M N = 8 * p 3 := by
    simpa [forms6, PrimePatterns.Rank6.cofactors] using h 3
  have h4 : Rank6.L4 M N = 2 * p 4 := by
    simpa [forms6, PrimePatterns.Rank6.cofactors] using h 4
  have h5 : Rank6.L5 M N = 1 * p 5 := by
    simpa [forms6, PrimePatterns.Rank6.cofactors] using h 5
  have h6 : Rank6.L6 M N = 1 * p 6 := by
    simpa [forms6, PrimePatterns.Rank6.cofactors] using h 6
  have h7 : Rank6.L7 M N = 1 * p 7 := by
    simpa [forms6, PrimePatterns.Rank6.cofactors] using h 7
  fin_cases i <;> norm_num [coordinates6E, codes6E, squareFactors6E,
    Nat.testBit_eq_decide_div_mod_eq, maskValue, maskValueFrom, columns6E, Rank6.b, Rank6.c, Rank6.P1x, Rank6.P2x, Rank6.P3x, Rank6.Q1x, Rank6.Q2x, Rank6.Q3x, Rank6.F, Rank6.H, Rank6.J]
    <;> simp only [h0, h1, h2, h3, h4, h5, h6, h7] <;> ring

theorem point_masks6E_on_lattice (x y : ℤ) (i : Fin 4) :
    coordinates6E (M6 x) (N6 y) i =
      maskValue (columns6E (outputs6 x y)) (codes6E i) * (squareFactors6E i) ^ 2 :=
  point_masks6E (M6 x) (N6 y) (outputs6 x y) (normalization6 x y) i

def columns6Ep (p : Fin 12 → ℚ) : List ℚ := [-1, 2, 3, 7, p 0, p 1, p 2, p 3, p 8, p 9, p 10, p 11]
def codes6Ep : Fin 4 → ℕ := ![4080, 248, 3220, 2384]
def coordinates6Ep (M N : ℚ) : Fin 4 → ℚ := ![Rank6.c M N, Rank6.Q1x M N, Rank6.Q2x M N, Rank6.Q3x M N]
def squareFactors6Ep : Fin 4 → ℚ := ![3024, 4, 4, (12 / 5 : ℚ)]

theorem codes6Ep_match : List.ofFn codes6Ep = MatrixCertificates.Rank6.Epgenerators := by
  decide +kernel

theorem squareFactors6Ep_nonzero (i : Fin 4) : squareFactors6Ep i ≠ 0 := by
  fin_cases i <;> norm_num [squareFactors6Ep]

theorem point_masks6Ep (M N : ℚ) (p : Fin 12 → ℚ)
    (h : ∀ i : Fin 12, forms6 M N i = (PrimePatterns.Rank6.cofactors i : ℚ) * p i)
    (i : Fin 4) :
    coordinates6Ep M N i = maskValue (columns6Ep p) (codes6Ep i) * (squareFactors6Ep i) ^ 2 := by
  have h0 : Rank6.L0 M N = 1 * p 0 := by
    simpa [forms6, PrimePatterns.Rank6.cofactors] using h 0
  have h1 : Rank6.L1 M N = 1 * p 1 := by
    simpa [forms6, PrimePatterns.Rank6.cofactors] using h 1
  have h2 : Rank6.L2 M N = 1 * p 2 := by
    simpa [forms6, PrimePatterns.Rank6.cofactors] using h 2
  have h3 : Rank6.L3 M N = 8 * p 3 := by
    simpa [forms6, PrimePatterns.Rank6.cofactors] using h 3
  have h8 : Rank6.L8 M N = 8 * p 8 := by
    simpa [forms6, PrimePatterns.Rank6.cofactors] using h 8
  have h9 : Rank6.L9 M N = 27 * p 9 := by
    simpa [forms6, PrimePatterns.Rank6.cofactors] using h 9
  have h10 : Rank6.L10 M N = 3 * p 10 := by
    simpa [forms6, PrimePatterns.Rank6.cofactors] using h 10
  have h11 : Rank6.L11 M N = 1 * p 11 := by
    simpa [forms6, PrimePatterns.Rank6.cofactors] using h 11
  fin_cases i <;> norm_num [coordinates6Ep, codes6Ep, squareFactors6Ep,
    Nat.testBit_eq_decide_div_mod_eq, maskValue, maskValueFrom, columns6Ep, Rank6.b, Rank6.c, Rank6.P1x, Rank6.P2x, Rank6.P3x, Rank6.Q1x, Rank6.Q2x, Rank6.Q3x, Rank6.F, Rank6.H, Rank6.J]
    <;> simp only [h0, h1, h2, h3, h8, h9, h10, h11] <;> ring

theorem point_masks6Ep_on_lattice (x y : ℤ) (i : Fin 4) :
    coordinates6Ep (M6 x) (N6 y) i =
      maskValue (columns6Ep (outputs6 x y)) (codes6Ep i) * (squareFactors6Ep i) ^ 2 :=
  point_masks6Ep (M6 x) (N6 y) (outputs6 x y) (normalization6 x y) i

theorem products6_nonzero_on_lattice (x y : ℤ) :
    Rank6.F (M6 x) (N6 y) ≠ 0 ∧ Rank6.H (M6 x) (N6 y) ≠ 0 ∧ Rank6.J (M6 x) (N6 y) ≠ 0 := by
  have h0 : Rank6.L0 (M6 x) (N6 y) ≠ 0 := by
    simpa [forms6] using forms6_nonzero_on_lattice x y 0
  have h1 : Rank6.L1 (M6 x) (N6 y) ≠ 0 := by
    simpa [forms6] using forms6_nonzero_on_lattice x y 1
  have h2 : Rank6.L2 (M6 x) (N6 y) ≠ 0 := by
    simpa [forms6] using forms6_nonzero_on_lattice x y 2
  have h3 : Rank6.L3 (M6 x) (N6 y) ≠ 0 := by
    simpa [forms6] using forms6_nonzero_on_lattice x y 3
  have h4 : Rank6.L4 (M6 x) (N6 y) ≠ 0 := by
    simpa [forms6] using forms6_nonzero_on_lattice x y 4
  have h5 : Rank6.L5 (M6 x) (N6 y) ≠ 0 := by
    simpa [forms6] using forms6_nonzero_on_lattice x y 5
  have h6 : Rank6.L6 (M6 x) (N6 y) ≠ 0 := by
    simpa [forms6] using forms6_nonzero_on_lattice x y 6
  have h7 : Rank6.L7 (M6 x) (N6 y) ≠ 0 := by
    simpa [forms6] using forms6_nonzero_on_lattice x y 7
  have h8 : Rank6.L8 (M6 x) (N6 y) ≠ 0 := by
    simpa [forms6] using forms6_nonzero_on_lattice x y 8
  have h9 : Rank6.L9 (M6 x) (N6 y) ≠ 0 := by
    simpa [forms6] using forms6_nonzero_on_lattice x y 9
  have h10 : Rank6.L10 (M6 x) (N6 y) ≠ 0 := by
    simpa [forms6] using forms6_nonzero_on_lattice x y 10
  have h11 : Rank6.L11 (M6 x) (N6 y) ≠ 0 := by
    simpa [forms6] using forms6_nonzero_on_lattice x y 11
  exact ⟨mul_ne_zero (mul_ne_zero (mul_ne_zero h0 h1) h2) h3,
    mul_ne_zero (mul_ne_zero (mul_ne_zero h4 h5) h6) h7,
    mul_ne_zero (mul_ne_zero (mul_ne_zero h8 h9) h10) h11⟩

theorem elliptic_pair6_on_lattice (x y : ℤ) :
    (Rank6.E (M6 x) (N6 y)).IsElliptic ∧ (Rank6.E' (M6 x) (N6 y)).IsElliptic := by
  obtain ⟨hF, hH, hJ⟩ := products6_nonzero_on_lattice x y
  exact ⟨Rank6.elliptic_E (M6 x) (N6 y) hF hH hJ, Rank6.elliptic_E' (M6 x) (N6 y) hF hH hJ⟩

def forms7 (M N : ℚ) : Fin 12 → ℚ := ![Rank7.L0 M N, Rank7.L1 M N, Rank7.L2 M N, Rank7.L3 M N, Rank7.L4 M N, Rank7.L5 M N, Rank7.L6 M N, Rank7.L7 M N, Rank7.L8 M N, Rank7.L9 M N, Rank7.L10 M N, Rank7.L11 M N]

theorem forms7_cast (m n : ℤ) (i : Fin 12) :
    forms7 (m : ℚ) (n : ℚ) i = ((PrimePatterns.Rank7.forms i).eval m n : ℚ) := by
  fin_cases i <;> simp [forms7, Rank7.L0, Rank7.L1, Rank7.L2, Rank7.L3, Rank7.L4, Rank7.L5, Rank7.L6, Rank7.L7, Rank7.L8, Rank7.L9, Rank7.L10, Rank7.L11, PrimePatterns.Rank7.forms,
    PrimePatterns.LinearForm.eval] <;> ring

def M7 (x : ℤ) : ℚ := ((PrimePatterns.Rank7.M0 + PrimePatterns.Rank7.W * x : ℤ) : ℚ)
def N7 (y : ℤ) : ℚ := ((PrimePatterns.Rank7.N0 + PrimePatterns.Rank7.W * y : ℤ) : ℚ)
def outputs7 (x y : ℤ) (i : Fin 12) : ℚ := ((PrimePatterns.Rank7.outputs i).eval x y : ℚ)

theorem normalization7 (x y : ℤ) (i : Fin 12) :
    forms7 (M7 x) (N7 y) i = (PrimePatterns.Rank7.cofactors i : ℚ) * outputs7 x y i := by
  dsimp [M7, N7, outputs7]
  rw [forms7_cast]
  exact_mod_cast (PrimePatterns.Rank7.normalization i x y).symm

theorem forms7_nonzero_on_lattice (x y : ℤ) (i : Fin 12) :
    forms7 (M7 x) (N7 y) i ≠ 0 := by
  dsimp [M7, N7]
  rw [forms7_cast]
  exact_mod_cast PrimePatterns.Rank7.forms_nonzero_on_lattice i x y

def columns7E (p : Fin 12 → ℚ) : List ℚ := [-1, 2, 3, 7, 13, p 0, p 1, p 2, p 3, p 4, p 5, p 6, p 7]
def codes7E : Fin 5 → ℕ := ![8163, 483, 6306, 3291, 6554]
def coordinates7E (M N : ℚ) : Fin 5 → ℚ := ![Rank7.b M N, Rank7.p1x M N, Rank7.p2x M N, Rank7.p3x M N, Rank7.p4x M N]
def squareFactors7E : Fin 5 → ℚ := ![471744, 17352, 840, 360, (72 / 19 : ℚ)]

theorem codes7E_match : List.ofFn codes7E = MatrixCertificates.Rank7.Egenerators := by
  decide +kernel

theorem squareFactors7E_nonzero (i : Fin 5) : squareFactors7E i ≠ 0 := by
  fin_cases i <;> norm_num [squareFactors7E]

theorem point_masks7E (M N : ℚ) (p : Fin 12 → ℚ)
    (h : ∀ i : Fin 12, forms7 M N i = (PrimePatterns.Rank7.cofactors i : ℚ) * p i)
    (i : Fin 5) :
    coordinates7E M N i = maskValue (columns7E p) (codes7E i) * (squareFactors7E i) ^ 2 := by
  have h0 : Rank7.L0 M N = 18 * p 0 := by
    simpa [forms7, PrimePatterns.Rank7.cofactors] using h 0
  have h1 : Rank7.L1 M N = 1 * p 1 := by
    simpa [forms7, PrimePatterns.Rank7.cofactors] using h 1
  have h2 : Rank7.L2 M N = 64 * p 2 := by
    simpa [forms7, PrimePatterns.Rank7.cofactors] using h 2
  have h3 : Rank7.L3 M N = 9 * p 3 := by
    simpa [forms7, PrimePatterns.Rank7.cofactors] using h 3
  have h4 : Rank7.L4 M N = 8 * p 4 := by
    simpa [forms7, PrimePatterns.Rank7.cofactors] using h 4
  have h5 : Rank7.L5 M N = 18 * p 5 := by
    simpa [forms7, PrimePatterns.Rank7.cofactors] using h 5
  have h6 : Rank7.L6 M N = 9 * p 6 := by
    simpa [forms7, PrimePatterns.Rank7.cofactors] using h 6
  have h7 : Rank7.L7 M N = 1 * p 7 := by
    simpa [forms7, PrimePatterns.Rank7.cofactors] using h 7
  fin_cases i <;> norm_num [coordinates7E, codes7E, squareFactors7E,
    Nat.testBit_eq_decide_div_mod_eq, maskValue, maskValueFrom, columns7E, Rank7.b, Rank7.c, Rank7.p1x, Rank7.p2x, Rank7.p3x, Rank7.p4x, Rank7.q1x, Rank7.q2x, Rank7.q3x, Rank7.F, Rank7.H, Rank7.J]
    <;> simp only [h0, h1, h2, h3, h4, h5, h6, h7] <;> ring

theorem point_masks7E_on_lattice (x y : ℤ) (i : Fin 5) :
    coordinates7E (M7 x) (N7 y) i =
      maskValue (columns7E (outputs7 x y)) (codes7E i) * (squareFactors7E i) ^ 2 :=
  point_masks7E (M7 x) (N7 y) (outputs7 x y) (normalization7 x y) i

def columns7Ep (p : Fin 12 → ℚ) : List ℚ := [-1, 2, 3, 7, 13, p 0, p 1, p 2, p 3, p 8, p 9, p 10, p 11]
def codes7Ep : Fin 4 → ℕ := ![8164, 482, 1696, 2848]
def coordinates7Ep (M N : ℚ) : Fin 4 → ℚ := ![Rank7.c M N, Rank7.q1x M N, Rank7.q2x M N, Rank7.q3x M N]
def squareFactors7Ep : Fin 4 → ℚ := ![93312, 4248, 3024, (72 / 5 : ℚ)]

theorem codes7Ep_match : List.ofFn codes7Ep = MatrixCertificates.Rank7.Epgenerators := by
  decide +kernel

theorem squareFactors7Ep_nonzero (i : Fin 4) : squareFactors7Ep i ≠ 0 := by
  fin_cases i <;> norm_num [squareFactors7Ep]

theorem point_masks7Ep (M N : ℚ) (p : Fin 12 → ℚ)
    (h : ∀ i : Fin 12, forms7 M N i = (PrimePatterns.Rank7.cofactors i : ℚ) * p i)
    (i : Fin 4) :
    coordinates7Ep M N i = maskValue (columns7Ep p) (codes7Ep i) * (squareFactors7Ep i) ^ 2 := by
  have h0 : Rank7.L0 M N = 18 * p 0 := by
    simpa [forms7, PrimePatterns.Rank7.cofactors] using h 0
  have h1 : Rank7.L1 M N = 1 * p 1 := by
    simpa [forms7, PrimePatterns.Rank7.cofactors] using h 1
  have h2 : Rank7.L2 M N = 64 * p 2 := by
    simpa [forms7, PrimePatterns.Rank7.cofactors] using h 2
  have h3 : Rank7.L3 M N = 9 * p 3 := by
    simpa [forms7, PrimePatterns.Rank7.cofactors] using h 3
  have h8 : Rank7.L8 M N = 6 * p 8 := by
    simpa [forms7, PrimePatterns.Rank7.cofactors] using h 8
  have h9 : Rank7.L9 M N = 1728 * p 9 := by
    simpa [forms7, PrimePatterns.Rank7.cofactors] using h 9
  have h10 : Rank7.L10 M N = 3 * p 10 := by
    simpa [forms7, PrimePatterns.Rank7.cofactors] using h 10
  have h11 : Rank7.L11 M N = 9 * p 11 := by
    simpa [forms7, PrimePatterns.Rank7.cofactors] using h 11
  fin_cases i <;> norm_num [coordinates7Ep, codes7Ep, squareFactors7Ep,
    Nat.testBit_eq_decide_div_mod_eq, maskValue, maskValueFrom, columns7Ep, Rank7.b, Rank7.c, Rank7.p1x, Rank7.p2x, Rank7.p3x, Rank7.p4x, Rank7.q1x, Rank7.q2x, Rank7.q3x, Rank7.F, Rank7.H, Rank7.J]
    <;> simp only [h0, h1, h2, h3, h8, h9, h10, h11] <;> ring

theorem point_masks7Ep_on_lattice (x y : ℤ) (i : Fin 4) :
    coordinates7Ep (M7 x) (N7 y) i =
      maskValue (columns7Ep (outputs7 x y)) (codes7Ep i) * (squareFactors7Ep i) ^ 2 :=
  point_masks7Ep (M7 x) (N7 y) (outputs7 x y) (normalization7 x y) i

theorem products7_nonzero_on_lattice (x y : ℤ) :
    Rank7.F (M7 x) (N7 y) ≠ 0 ∧ Rank7.H (M7 x) (N7 y) ≠ 0 ∧ Rank7.J (M7 x) (N7 y) ≠ 0 := by
  have h0 : Rank7.L0 (M7 x) (N7 y) ≠ 0 := by
    simpa [forms7] using forms7_nonzero_on_lattice x y 0
  have h1 : Rank7.L1 (M7 x) (N7 y) ≠ 0 := by
    simpa [forms7] using forms7_nonzero_on_lattice x y 1
  have h2 : Rank7.L2 (M7 x) (N7 y) ≠ 0 := by
    simpa [forms7] using forms7_nonzero_on_lattice x y 2
  have h3 : Rank7.L3 (M7 x) (N7 y) ≠ 0 := by
    simpa [forms7] using forms7_nonzero_on_lattice x y 3
  have h4 : Rank7.L4 (M7 x) (N7 y) ≠ 0 := by
    simpa [forms7] using forms7_nonzero_on_lattice x y 4
  have h5 : Rank7.L5 (M7 x) (N7 y) ≠ 0 := by
    simpa [forms7] using forms7_nonzero_on_lattice x y 5
  have h6 : Rank7.L6 (M7 x) (N7 y) ≠ 0 := by
    simpa [forms7] using forms7_nonzero_on_lattice x y 6
  have h7 : Rank7.L7 (M7 x) (N7 y) ≠ 0 := by
    simpa [forms7] using forms7_nonzero_on_lattice x y 7
  have h8 : Rank7.L8 (M7 x) (N7 y) ≠ 0 := by
    simpa [forms7] using forms7_nonzero_on_lattice x y 8
  have h9 : Rank7.L9 (M7 x) (N7 y) ≠ 0 := by
    simpa [forms7] using forms7_nonzero_on_lattice x y 9
  have h10 : Rank7.L10 (M7 x) (N7 y) ≠ 0 := by
    simpa [forms7] using forms7_nonzero_on_lattice x y 10
  have h11 : Rank7.L11 (M7 x) (N7 y) ≠ 0 := by
    simpa [forms7] using forms7_nonzero_on_lattice x y 11
  exact ⟨mul_ne_zero (mul_ne_zero (mul_ne_zero h0 h1) h2) h3,
    mul_ne_zero (mul_ne_zero (mul_ne_zero h4 h5) h6) h7,
    mul_ne_zero (mul_ne_zero (mul_ne_zero h8 h9) h10) h11⟩

theorem elliptic_pair7_on_lattice (x y : ℤ) :
    (Rank7.E (M7 x) (N7 y)).IsElliptic ∧ (Rank7.E' (M7 x) (N7 y)).IsElliptic := by
  obtain ⟨hF, hH, hJ⟩ := products7_nonzero_on_lattice x y
  exact ⟨Rank7.E_isElliptic hF hH hJ, Rank7.E'_isElliptic hF hH hJ⟩

end RankCertificates.Integration
