module

public import Mathlib.Tactic
public import RankCertificates.Admissibility

@[expose] public section

/-!
Kernel-checked arithmetic for the three final prime-pattern progressions.
Source data: final155_certificate.json, rank6_certificate.json and
rank7_certificate.json in the uploaded research archive.
These are affine arithmetic and local admissibility statements; they do not
state an elliptic-curve rank theorem or a prime-pattern infinitude theorem.
-/

namespace RankCertificates.PrimePatterns

structure LinearForm where
  a : ℤ
  b : ℤ
  deriving DecidableEq

structure AffineForm where
  a : ℤ
  b : ℤ
  c : ℤ
  deriving DecidableEq

def LinearForm.eval (f : LinearForm) (m n : ℤ) : ℤ := f.a * m + f.b * n

def AffineForm.eval (f : AffineForm) (x y : ℤ) : ℤ := f.a * x + f.b * y + f.c

/-- A simultaneous nonzero residue witness at a positive integer modulus. -/
def Avoids (fs : Fin 12 → AffineForm) (p : ℕ) : Prop :=
  ∃ x y : ℤ, ∀ i, (fs i).eval x y % (p : ℤ) ≠ 0

theorem AffineForm.eval_mod (f : AffineForm) (q x y : ℤ)
    (ha : f.a % q = 0) (hb : f.b % q = 0) :
    f.eval x y % q = f.c % q := by
  simp [AffineForm.eval, Int.add_emod, Int.mul_emod, ha, hb]


/-- A unit factor makes the displayed exponent the exact removed power. -/
theorem exact_power_part (p : ℤ) (e : ℕ) (z : ℤ) (hp : p ≠ 0) (hu : z % p ≠ 0) :
    p ^ e ∣ p ^ e * z ∧ ¬ p ^ (e + 1) ∣ p ^ e * z := by
  constructor
  · exact ⟨z, rfl⟩
  · intro h
    rw [pow_succ] at h
    have hd : p ∣ z := (mul_dvd_mul_iff_left (pow_ne_zero e hp)).mp h
    exact hu (Int.emod_eq_zero_of_dvd hd)

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rank5

/-- Final rank-5 manuscript's ordered homogeneous forms. -/
def forms : Fin 12 → LinearForm := ![⟨1, 0⟩, ⟨22, -1⟩, ⟨9, -2⟩, ⟨143, 155⟩, ⟨-55, 62⟩, ⟨3, -1⟩, ⟨138, -31⟩, ⟨55, 64⟩, ⟨99, 62⟩, ⟨5, -1⟩, ⟨32, 31⟩, ⟨55, -12⟩]

def cofactors : Fin 12 → ℤ := ![54, 1, 8, 1, 8, 1, 1, 2, 4, 1, 1, 6]
def W : ℤ := 19984345920
def M0 : ℤ := 6555660534
def N0 : ℤ := -1

/-- Literal normalized affine outputs. -/
def outputs : Fin 12 → AffineForm := ![⟨370080480, 0, 121401121⟩, ⟨439655610240, -19984345920, 144224531749⟩, ⟨22482389160, -4996086480, 7375118101⟩, ⟨2857761466560, 3097573617600, 937459456207⟩, ⟨-137392378200, 154878680880, -45070166179⟩, ⟨59953037760, -19984345920, 19666981603⟩, ⟨2757839736960, -619514723520, 904681153723⟩, ⟨549569512800, 639499069440, 180280664653⟩, ⟨494612561520, 309757361760, 162252598201⟩, ⟨99921729600, -19984345920, 32778302671⟩, ⟨639499069440, 619514723520, 209781137057⟩, ⟨183189837600, -39968691840, 60093554897⟩]

/-- Integer coefficients witnessing affine content one. -/
def bezout : Fin 12 → ℤ × ℤ × ℤ := ![(58675400, 0, -178866719), (0, -44897355719, -6221162771), (-560437212, -2802186060, -189826979), (-1225874301249, 1131576278076, -2010203537), (58496729400, 51997092800, 360246581), (0, 6947902744, 7060020427), (3339897374000, 14877724666000, 6707100787), (-162573297992, 139348541136, 1287247237), (-204372400520, 326995840832, -1258608119), (0, -3360678186, -2048945489), (103405969918, -103405969918, -9850745887), (-46576721270, -214252917842, -516309007)]

/-- CRT conditions are represented by (modulus, M residue, N residue). -/
def crt : Fin 8 → ℤ × ℤ × ℤ := ![(64, 54, 63), (81, 54, 80), (5, 4, 4), (7, 3, 6), (11, 5, 10), (17, 4, 16), (19, 18, 18), (31, 14, 30)]

def retainedPrimes : Fin 8 → ℕ := ![2, 3, 5, 7, 11, 17, 19, 31]

def mod8Units : Fin 12 → ℤ := ![1, 5, 5, 7, 5, 3, 3, 5, 1, 7, 1, 1]
def mod3Units : Fin 12 → ℤ := ![1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2]

 theorem cofactors_positive (i : Fin 12) : 0 < cofactors i := by
  fin_cases i <;> norm_num [cofactors]

 theorem original_forms_primitive (i : Fin 12) :
    Int.gcd (forms i).a (forms i).b = 1 := by
  fin_cases i <;> norm_num [forms, Int.gcd]

 theorem bezout_certificate (i : Fin 12) :
    (outputs i).a * (bezout i).1 + (outputs i).b * (bezout i).2.1 +
      (outputs i).c * (bezout i).2.2 = 1 := by
  fin_cases i <;> norm_num [outputs, bezout]

 theorem normalization (i : Fin 12) (x y : ℤ) :
    cofactors i * (outputs i).eval x y =
      (forms i).eval (M0 + W * x) (N0 + W * y) := by
  fin_cases i <;> norm_num [cofactors, outputs, AffineForm.eval,
    forms, LinearForm.eval, M0, N0, W] <;> ring

 theorem cofactor_divides (i : Fin 12) (x y : ℤ) :
    cofactors i ∣ (forms i).eval (M0 + W * x) (N0 + W * y) :=
  ⟨(outputs i).eval x y, (normalization i x y).symm⟩

 theorem crt_certificate (j : Fin 8) :
    W % (crt j).1 = 0 ∧ M0 % (crt j).1 = (crt j).2.1 ∧
      N0 % (crt j).1 = (crt j).2.2 := by
  fin_cases j <;> norm_num [W, M0, N0, crt]

 theorem normalized_unit_residues (i : Fin 12) :
    (outputs i).a % 8 = 0 ∧ (outputs i).b % 8 = 0 ∧
    (outputs i).c % 8 = mod8Units i ∧ mod8Units i % 2 ≠ 0 ∧
    (outputs i).a % 3 = 0 ∧ (outputs i).b % 3 = 0 ∧
    (outputs i).c % 3 = mod3Units i ∧ mod3Units i ≠ 0 := by
  fin_cases i <;> norm_num [outputs, mod8Units, mod3Units]

 theorem residue8 (i : Fin 12) (x y : ℤ) :
    (outputs i).eval x y % 8 = mod8Units i := by
  rw [AffineForm.eval_mod _ _ _ _ (normalized_unit_residues i).1
      (normalized_unit_residues i).2.1]
  exact (normalized_unit_residues i).2.2.1

 theorem residue3 (i : Fin 12) (x y : ℤ) :
    (outputs i).eval x y % 3 = mod3Units i := by
  have h := normalized_unit_residues i
  rw [AffineForm.eval_mod _ _ _ _ h.2.2.2.2.1 h.2.2.2.2.2.1]
  exact h.2.2.2.2.2.2.1

 theorem retained_prime_units (i : Fin 12) (j : Fin 8) :
    (outputs i).a % (retainedPrimes j : ℤ) = 0 ∧
    (outputs i).b % (retainedPrimes j : ℤ) = 0 ∧
    (outputs i).c % (retainedPrimes j : ℤ) ≠ 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [outputs, retainedPrimes]

 theorem retained_prime_residue (i : Fin 12) (j : Fin 8) (x y : ℤ) :
    (outputs i).eval x y % (retainedPrimes j : ℤ) ≠ 0 := by
  rw [AffineForm.eval_mod _ _ _ _ (retained_prime_units i j).1
      (retained_prime_units i j).2.1]
  exact (retained_prime_units i j).2.2

 theorem nonparallel_original (i j : Fin 12) (h : i ≠ j) :
    (forms i).a * (forms j).b - (forms i).b * (forms j).a ≠ 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [forms] at *

 theorem nonparallel_outputs (i j : Fin 12) (h : i ≠ j) :
    (outputs i).a * (outputs j).b - (outputs i).b * (outputs j).a ≠ 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [outputs] at *

 theorem avoids_2 : Avoids outputs 2 := by
  refine ⟨0, 0, ?_⟩
  intro i
  fin_cases i <;> norm_num [outputs, AffineForm.eval]

 theorem avoids_3 : Avoids outputs 3 := by
  refine ⟨0, 0, ?_⟩
  intro i
  fin_cases i <;> norm_num [outputs, AffineForm.eval]

 theorem avoids_5 : Avoids outputs 5 := by
  refine ⟨0, 0, ?_⟩
  intro i
  fin_cases i <;> norm_num [outputs, AffineForm.eval]

 theorem avoids_7 : Avoids outputs 7 := by
  refine ⟨0, 0, ?_⟩
  intro i
  fin_cases i <;> norm_num [outputs, AffineForm.eval]

 theorem avoids_11 : Avoids outputs 11 := by
  refine ⟨0, 0, ?_⟩
  intro i
  fin_cases i <;> norm_num [outputs, AffineForm.eval]

/-- These exact outputs form a locally admissible affine system at every prime. -/
 theorem local_admissibility (p : ℕ) (hp : p.Prime) : Avoids outputs p := by
  by_cases hn : 12 < p
  · apply exists_pair_avoiding_integer (fun i => (outputs i).a)
      (fun i => (outputs i).b) (fun i => (outputs i).c) _ p hp hn
    intro i
    exact ⟨(bezout i).1, (bezout i).2.1, (bezout i).2.2, bezout_certificate i⟩
  · have hs : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 := by
      interval_cases p <;> norm_num at *
    rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact avoids_2
    · exact avoids_3
    · exact avoids_5
    · exact avoids_7
    · exact avoids_11

 theorem normalized_quotient (i : Fin 12) (x y : ℤ) :
    (forms i).eval (M0 + W * x) (N0 + W * y) / cofactors i =
      (outputs i).eval x y := by
  rw [← normalization i x y]
  exact Int.mul_ediv_cancel_left _ (ne_of_gt (cofactors_positive i))

/-- Exponents of the fixed powers removed at 2 and 3. -/
def exponent2 : Fin 12 → ℕ := ![1, 0, 3, 0, 3, 0, 0, 1, 2, 0, 0, 1]
def exponent3 : Fin 12 → ℕ := ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

 theorem cofactor_parts (i : Fin 12) :
    cofactors i = (2 : ℤ) ^ exponent2 i * 3 ^ exponent3 i := by
  fin_cases i <;> norm_num [cofactors, exponent2, exponent3]

/-- The quotient is a unit at 2 and 3 throughout the progression, so the
fixed cofactor removes precisely their powers. -/
 theorem normalized_quotient_units (i : Fin 12) (x y : ℤ) :
    ((forms i).eval (M0 + W * x) (N0 + W * y) / cofactors i) % 2 ≠ 0 ∧
    ((forms i).eval (M0 + W * x) (N0 + W * y) / cofactors i) % 3 ≠ 0 := by
  rw [normalized_quotient]
  constructor
  · simpa [retainedPrimes] using retained_prime_residue i 0 x y
  · simpa [retainedPrimes] using retained_prime_residue i 1 x y

 theorem retained_primes_prime (j : Fin 8) : (retainedPrimes j).Prime := by
  fin_cases j <;> norm_num [retainedPrimes]

 theorem cofactors_divide_modulus (i : Fin 12) : cofactors i ∣ W := by
  fin_cases i <;> norm_num [cofactors, W]

 theorem affine_content_one (i : Fin 12) :
    Int.gcd (Int.gcd (outputs i).a (outputs i).b : ℤ) (outputs i).c = 1 := by
  fin_cases i <;> norm_num [outputs, Int.gcd]

 theorem positive_forms (m n : ℤ) (_hn : 0 < n)
    (hlo : 19 * n < 20 * m) (hhi : 10 * m < 11 * n) (i : Fin 12) :
    0 < (forms i).eval m n := by
  fin_cases i <;> simp [forms, LinearForm.eval] <;> omega

 theorem outputs_nonzero (i : Fin 12) (x y : ℤ) : (outputs i).eval x y ≠ 0 := by
  have h := retained_prime_residue i 0 x y
  intro hz
  simp [hz] at h

 theorem forms_nonzero_on_lattice (i : Fin 12) (x y : ℤ) :
    (forms i).eval (M0 + W * x) (N0 + W * y) ≠ 0 := by
  rw [← normalization i x y]
  exact mul_ne_zero (ne_of_gt (cofactors_positive i)) (outputs_nonzero i x y)

/-- Uniform exact divisibility at 2 for every factor in the CRT progression. -/
 theorem exact_two_part (i : Fin 12) (x y : ℤ) :
    (2 : ℤ) ^ exponent2 i ∣ (forms i).eval (M0 + W * x) (N0 + W * y) ∧
    ¬ (2 : ℤ) ^ (exponent2 i + 1) ∣ (forms i).eval (M0 + W * x) (N0 + W * y) := by
  rw [← normalization i x y, cofactor_parts, mul_assoc]
  apply exact_power_part _ _ _ (by norm_num)
  have hu : (outputs i).eval x y % 2 ≠ 0 := by
    simpa [retainedPrimes] using retained_prime_residue i 0 x y
  have hthree : (3 : ℤ) ^ exponent3 i % 2 = 1 := by
    fin_cases i <;> norm_num [exponent3]
  simpa [Int.mul_emod, hthree] using hu

/-- Uniform exact divisibility at 3 for every factor in the CRT progression. -/
 theorem exact_three_part (i : Fin 12) (x y : ℤ) :
    (3 : ℤ) ^ exponent3 i ∣ (forms i).eval (M0 + W * x) (N0 + W * y) ∧
    ¬ (3 : ℤ) ^ (exponent3 i + 1) ∣ (forms i).eval (M0 + W * x) (N0 + W * y) := by
  rw [← normalization i x y, cofactor_parts, mul_comm ((2 : ℤ) ^ exponent2 i), mul_assoc]
  apply exact_power_part _ _ _ (by norm_num)
  rw [Int.mul_emod, residue3]
  fin_cases i <;> norm_num [exponent2, mod3Units]

end Rank5

namespace Rank6

/-- Final rank-6 manuscript's ordered homogeneous forms. -/
def forms : Fin 12 → LinearForm := ![⟨1, 0⟩, ⟨0, 1⟩, ⟨169, 750⟩, ⟨25, -169⟩, ⟨1, -27⟩, ⟨7, 20⟩, ⟨2, -21⟩, ⟨9, 10⟩, ⟨1, 15⟩, ⟨7, 64⟩, ⟨1, -2⟩, ⟨32, -105⟩]

def cofactors : Fin 12 → ℤ := ![1, 1, 1, 8, 2, 1, 1, 1, 8, 27, 3, 1]
def W : ℤ := 780373440
def M0 : ℤ := 416513683
def N0 : ℤ := 91046603

/-- Literal normalized affine outputs. -/
def outputs : Fin 12 → AffineForm := ![⟨780373440, 0, 416513683⟩, ⟨0, 780373440, 91046603⟩, ⟨131883111360, 585280080000, 138675764677⟩, ⟨2438667000, -16485388920, -621754229⟩, ⟨390186720, -10535041440, -1020872299⟩, ⟨5462614080, 15607468800, 4736527841⟩, ⟨1560746880, -16387842240, -1078951297⟩, ⟨7023360960, 7803734400, 4659089177⟩, ⟨97546680, 1463200200, 222776591⟩, ⟨202319040, 1849774080, 323799199⟩, ⟨260124480, -520248960, 78140159⟩, ⟨24971950080, -81939211200, 3768544541⟩]

/-- Integer coefficients witnessing affine content one. -/
def bezout : Fin 12 → ℤ × ℤ × ℤ := ![(-89898127, 0, 168431707), (0, 884467, -7580893), (-2594908938691, 584768211536, -205667507), (-7916514237, -1172816924, 46000651), (-102896805, 0, -39328099), (-3436272483, 1145424161, 188716001), (-4976447140, -497644714, 359931647), (1390496686, -1390496686, 232901033), (9257154, 0, -4053409), (-668285640, 74253960, -6628001), (1853126, 1853126, 6168959), (-4486347110, -1365409990, 40391861)]

/-- CRT conditions are represented by (modulus, M residue, N residue). -/
def crt : Fin 7 → ℤ × ℤ × ℤ := ![(64, 19, 11), (81, 19, 11), (7, 5, 4), (5, 3, 3), (11, 3, 10), (17, 15, 9), (23, 13, 22)]

def retainedPrimes : Fin 7 → ℕ := ![2, 3, 5, 7, 11, 17, 23]

def mod8Units : Fin 12 → ℤ := ![3, 3, 5, 3, 5, 1, 7, 1, 7, 7, 7, 5]
def mod3Units : Fin 12 → ℤ := ![1, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2]

 theorem cofactors_positive (i : Fin 12) : 0 < cofactors i := by
  fin_cases i <;> norm_num [cofactors]

 theorem original_forms_primitive (i : Fin 12) :
    Int.gcd (forms i).a (forms i).b = 1 := by
  fin_cases i <;> norm_num [forms, Int.gcd]

 theorem bezout_certificate (i : Fin 12) :
    (outputs i).a * (bezout i).1 + (outputs i).b * (bezout i).2.1 +
      (outputs i).c * (bezout i).2.2 = 1 := by
  fin_cases i <;> norm_num [outputs, bezout]

 theorem normalization (i : Fin 12) (x y : ℤ) :
    cofactors i * (outputs i).eval x y =
      (forms i).eval (M0 + W * x) (N0 + W * y) := by
  fin_cases i <;> norm_num [cofactors, outputs, AffineForm.eval,
    forms, LinearForm.eval, M0, N0, W] <;> ring

 theorem cofactor_divides (i : Fin 12) (x y : ℤ) :
    cofactors i ∣ (forms i).eval (M0 + W * x) (N0 + W * y) :=
  ⟨(outputs i).eval x y, (normalization i x y).symm⟩

 theorem crt_certificate (j : Fin 7) :
    W % (crt j).1 = 0 ∧ M0 % (crt j).1 = (crt j).2.1 ∧
      N0 % (crt j).1 = (crt j).2.2 := by
  fin_cases j <;> norm_num [W, M0, N0, crt]

 theorem normalized_unit_residues (i : Fin 12) :
    (outputs i).a % 8 = 0 ∧ (outputs i).b % 8 = 0 ∧
    (outputs i).c % 8 = mod8Units i ∧ mod8Units i % 2 ≠ 0 ∧
    (outputs i).a % 3 = 0 ∧ (outputs i).b % 3 = 0 ∧
    (outputs i).c % 3 = mod3Units i ∧ mod3Units i ≠ 0 := by
  fin_cases i <;> norm_num [outputs, mod8Units, mod3Units]

 theorem residue8 (i : Fin 12) (x y : ℤ) :
    (outputs i).eval x y % 8 = mod8Units i := by
  rw [AffineForm.eval_mod _ _ _ _ (normalized_unit_residues i).1
      (normalized_unit_residues i).2.1]
  exact (normalized_unit_residues i).2.2.1

 theorem residue3 (i : Fin 12) (x y : ℤ) :
    (outputs i).eval x y % 3 = mod3Units i := by
  have h := normalized_unit_residues i
  rw [AffineForm.eval_mod _ _ _ _ h.2.2.2.2.1 h.2.2.2.2.2.1]
  exact h.2.2.2.2.2.2.1

 theorem retained_prime_units (i : Fin 12) (j : Fin 7) :
    (outputs i).a % (retainedPrimes j : ℤ) = 0 ∧
    (outputs i).b % (retainedPrimes j : ℤ) = 0 ∧
    (outputs i).c % (retainedPrimes j : ℤ) ≠ 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [outputs, retainedPrimes]

 theorem retained_prime_residue (i : Fin 12) (j : Fin 7) (x y : ℤ) :
    (outputs i).eval x y % (retainedPrimes j : ℤ) ≠ 0 := by
  rw [AffineForm.eval_mod _ _ _ _ (retained_prime_units i j).1
      (retained_prime_units i j).2.1]
  exact (retained_prime_units i j).2.2

 theorem nonparallel_original (i j : Fin 12) (h : i ≠ j) :
    (forms i).a * (forms j).b - (forms i).b * (forms j).a ≠ 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [forms] at *

 theorem nonparallel_outputs (i j : Fin 12) (h : i ≠ j) :
    (outputs i).a * (outputs j).b - (outputs i).b * (outputs j).a ≠ 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [outputs] at *

 theorem avoids_2 : Avoids outputs 2 := by
  refine ⟨0, 0, ?_⟩
  intro i
  fin_cases i <;> norm_num [outputs, AffineForm.eval]

 theorem avoids_3 : Avoids outputs 3 := by
  refine ⟨0, 0, ?_⟩
  intro i
  fin_cases i <;> norm_num [outputs, AffineForm.eval]

 theorem avoids_5 : Avoids outputs 5 := by
  refine ⟨0, 0, ?_⟩
  intro i
  fin_cases i <;> norm_num [outputs, AffineForm.eval]

 theorem avoids_7 : Avoids outputs 7 := by
  refine ⟨0, 0, ?_⟩
  intro i
  fin_cases i <;> norm_num [outputs, AffineForm.eval]

 theorem avoids_11 : Avoids outputs 11 := by
  refine ⟨0, 0, ?_⟩
  intro i
  fin_cases i <;> norm_num [outputs, AffineForm.eval]

/-- These exact outputs form a locally admissible affine system at every prime. -/
 theorem local_admissibility (p : ℕ) (hp : p.Prime) : Avoids outputs p := by
  by_cases hn : 12 < p
  · apply exists_pair_avoiding_integer (fun i => (outputs i).a)
      (fun i => (outputs i).b) (fun i => (outputs i).c) _ p hp hn
    intro i
    exact ⟨(bezout i).1, (bezout i).2.1, (bezout i).2.2, bezout_certificate i⟩
  · have hs : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 := by
      interval_cases p <;> norm_num at *
    rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact avoids_2
    · exact avoids_3
    · exact avoids_5
    · exact avoids_7
    · exact avoids_11

 theorem normalized_quotient (i : Fin 12) (x y : ℤ) :
    (forms i).eval (M0 + W * x) (N0 + W * y) / cofactors i =
      (outputs i).eval x y := by
  rw [← normalization i x y]
  exact Int.mul_ediv_cancel_left _ (ne_of_gt (cofactors_positive i))

/-- Exponents of the fixed powers removed at 2 and 3. -/
def exponent2 : Fin 12 → ℕ := ![0, 0, 0, 3, 1, 0, 0, 0, 3, 0, 0, 0]
def exponent3 : Fin 12 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 1, 0]

 theorem cofactor_parts (i : Fin 12) :
    cofactors i = (2 : ℤ) ^ exponent2 i * 3 ^ exponent3 i := by
  fin_cases i <;> norm_num [cofactors, exponent2, exponent3]

/-- The quotient is a unit at 2 and 3 throughout the progression, so the
fixed cofactor removes precisely their powers. -/
 theorem normalized_quotient_units (i : Fin 12) (x y : ℤ) :
    ((forms i).eval (M0 + W * x) (N0 + W * y) / cofactors i) % 2 ≠ 0 ∧
    ((forms i).eval (M0 + W * x) (N0 + W * y) / cofactors i) % 3 ≠ 0 := by
  rw [normalized_quotient]
  constructor
  · simpa [retainedPrimes] using retained_prime_residue i 0 x y
  · simpa [retainedPrimes] using retained_prime_residue i 1 x y

 theorem retained_primes_prime (j : Fin 7) : (retainedPrimes j).Prime := by
  fin_cases j <;> norm_num [retainedPrimes]

 theorem cofactors_divide_modulus (i : Fin 12) : cofactors i ∣ W := by
  fin_cases i <;> norm_num [cofactors, W]

 theorem affine_content_one (i : Fin 12) :
    Int.gcd (Int.gcd (outputs i).a (outputs i).b : ℤ) (outputs i).c = 1 := by
  fin_cases i <;> norm_num [outputs, Int.gcd]

 theorem positive_forms (m n : ℤ) (hn : 0 < n) (hlo : 27 * n < m) (i : Fin 12) :
    0 < (forms i).eval m n := by
  fin_cases i <;> simp [forms, LinearForm.eval] <;> omega

 theorem outputs_nonzero (i : Fin 12) (x y : ℤ) : (outputs i).eval x y ≠ 0 := by
  have h := retained_prime_residue i 0 x y
  intro hz
  simp [hz] at h

 theorem forms_nonzero_on_lattice (i : Fin 12) (x y : ℤ) :
    (forms i).eval (M0 + W * x) (N0 + W * y) ≠ 0 := by
  rw [← normalization i x y]
  exact mul_ne_zero (ne_of_gt (cofactors_positive i)) (outputs_nonzero i x y)

/-- Uniform exact divisibility at 2 for every factor in the CRT progression. -/
 theorem exact_two_part (i : Fin 12) (x y : ℤ) :
    (2 : ℤ) ^ exponent2 i ∣ (forms i).eval (M0 + W * x) (N0 + W * y) ∧
    ¬ (2 : ℤ) ^ (exponent2 i + 1) ∣ (forms i).eval (M0 + W * x) (N0 + W * y) := by
  rw [← normalization i x y, cofactor_parts, mul_assoc]
  apply exact_power_part _ _ _ (by norm_num)
  have hu : (outputs i).eval x y % 2 ≠ 0 := by
    simpa [retainedPrimes] using retained_prime_residue i 0 x y
  have hthree : (3 : ℤ) ^ exponent3 i % 2 = 1 := by
    fin_cases i <;> norm_num [exponent3]
  simpa [Int.mul_emod, hthree] using hu

/-- Uniform exact divisibility at 3 for every factor in the CRT progression. -/
 theorem exact_three_part (i : Fin 12) (x y : ℤ) :
    (3 : ℤ) ^ exponent3 i ∣ (forms i).eval (M0 + W * x) (N0 + W * y) ∧
    ¬ (3 : ℤ) ^ (exponent3 i + 1) ∣ (forms i).eval (M0 + W * x) (N0 + W * y) := by
  rw [← normalization i x y, cofactor_parts, mul_comm ((2 : ℤ) ^ exponent2 i), mul_assoc]
  apply exact_power_part _ _ _ (by norm_num)
  rw [Int.mul_emod, residue3]
  fin_cases i <;> norm_num [exponent2, mod3Units]

end Rank6

namespace Rank7

/-- Final rank-7 manuscript's ordered homogeneous forms. -/
def forms : Fin 12 → LinearForm := ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, -182⟩, ⟨182, 10557⟩, ⟨9, 34⟩, ⟨25, -4968⟩, ⟨2, -5589⟩, ⟨8, 425⟩, ⟨13, 2688⟩, ⟨325, 49266⟩, ⟨14, -975⟩, ⟨896, -45747⟩]

def cofactors : Fin 12 → ℤ := ![18, 1, 64, 9, 8, 18, 9, 1, 6, 1728, 3, 9]
def W : ℤ := 308403583488
def M0 : ℤ := 79151095314
def N0 : ℤ := 151444919819

/-- Literal normalized affine outputs. -/
def outputs : Fin 12 → AffineForm := ![⟨17133532416, 0, 4397283073⟩, ⟨0, 308403583488, 151444919819⟩, ⟨4818805992, -877022690544, -429434754871⟩, ⟨6236605799424, 361757403431424, 179245501986259⟩, ⟨346954031424, 1310715229824, 732685891459⟩, ⟨428338310400, -85119389042688, -41688865793219⟩, ⟨68534129664, -191518625346048, -94029706075307⟩, ⟨2467228667904, 131071522982400, 64997299685587⟩, ⟨668207764224, 138164805402624, 68018818118759⟩, ⟨58004146200, 8792714666736, 4332644401493⟩, ⟨1439216722944, -100231164633600, -48850227163043⟩, ⟨30703290089472, -1567615414869504, -761914596173161⟩]

/-- Integer coefficients witnessing affine content one. -/
def bezout : Fin 12 → ℤ × ℤ × ℤ := ![(-1303327174, 0, 5078271745), (0, 52226493482, -106354427485), (77331986304, 0, 867763577), (1383395961701916, -23851654512102, 4559814235), (2552821805505, -680752481468, 8954489707), (12286842448700053, 61831701754781, -3630278891), (22029537058420188, 7884587350902, -2873364995), (550969574272651, -10395652344767, 49325994331), (-9630152718943897, 46578731409644, -8799677353), (35341752351781051, -233143901863494, -84244555), (1472058741502602, 21130029782334, 14822123509), (-130875406388438280, -2563324042321323, 937279271)]

/-- CRT conditions are represented by (modulus, M residue, N residue). -/
def crt : Fin 8 → ℤ × ℤ × ℤ := ![(512, 18, 11), (81, 18, 11), (7, 4, 4), (13, 5, 11), (11, 5, 6), (17, 3, 4), (19, 15, 12), (23, 4, 6)]

def retainedPrimes : Fin 8 → ℕ := ![2, 3, 7, 11, 13, 17, 19, 23]

def mod8Units : Fin 12 → ℤ := ![1, 3, 1, 3, 3, 5, 5, 3, 7, 5, 5, 7]
def mod3Units : Fin 12 → ℤ := ![1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2]

 theorem cofactors_positive (i : Fin 12) : 0 < cofactors i := by
  fin_cases i <;> norm_num [cofactors]

 theorem original_forms_primitive (i : Fin 12) :
    Int.gcd (forms i).a (forms i).b = 1 := by
  fin_cases i <;> norm_num [forms, Int.gcd]

 theorem bezout_certificate (i : Fin 12) :
    (outputs i).a * (bezout i).1 + (outputs i).b * (bezout i).2.1 +
      (outputs i).c * (bezout i).2.2 = 1 := by
  fin_cases i <;> norm_num [outputs, bezout]

 theorem normalization (i : Fin 12) (x y : ℤ) :
    cofactors i * (outputs i).eval x y =
      (forms i).eval (M0 + W * x) (N0 + W * y) := by
  fin_cases i <;> norm_num [cofactors, outputs, AffineForm.eval,
    forms, LinearForm.eval, M0, N0, W] <;> ring

 theorem cofactor_divides (i : Fin 12) (x y : ℤ) :
    cofactors i ∣ (forms i).eval (M0 + W * x) (N0 + W * y) :=
  ⟨(outputs i).eval x y, (normalization i x y).symm⟩

 theorem crt_certificate (j : Fin 8) :
    W % (crt j).1 = 0 ∧ M0 % (crt j).1 = (crt j).2.1 ∧
      N0 % (crt j).1 = (crt j).2.2 := by
  fin_cases j <;> norm_num [W, M0, N0, crt]

 theorem normalized_unit_residues (i : Fin 12) :
    (outputs i).a % 8 = 0 ∧ (outputs i).b % 8 = 0 ∧
    (outputs i).c % 8 = mod8Units i ∧ mod8Units i % 2 ≠ 0 ∧
    (outputs i).a % 3 = 0 ∧ (outputs i).b % 3 = 0 ∧
    (outputs i).c % 3 = mod3Units i ∧ mod3Units i ≠ 0 := by
  fin_cases i <;> norm_num [outputs, mod8Units, mod3Units]

 theorem residue8 (i : Fin 12) (x y : ℤ) :
    (outputs i).eval x y % 8 = mod8Units i := by
  rw [AffineForm.eval_mod _ _ _ _ (normalized_unit_residues i).1
      (normalized_unit_residues i).2.1]
  exact (normalized_unit_residues i).2.2.1

 theorem residue3 (i : Fin 12) (x y : ℤ) :
    (outputs i).eval x y % 3 = mod3Units i := by
  have h := normalized_unit_residues i
  rw [AffineForm.eval_mod _ _ _ _ h.2.2.2.2.1 h.2.2.2.2.2.1]
  exact h.2.2.2.2.2.2.1

 theorem retained_prime_units (i : Fin 12) (j : Fin 8) :
    (outputs i).a % (retainedPrimes j : ℤ) = 0 ∧
    (outputs i).b % (retainedPrimes j : ℤ) = 0 ∧
    (outputs i).c % (retainedPrimes j : ℤ) ≠ 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [outputs, retainedPrimes]

 theorem retained_prime_residue (i : Fin 12) (j : Fin 8) (x y : ℤ) :
    (outputs i).eval x y % (retainedPrimes j : ℤ) ≠ 0 := by
  rw [AffineForm.eval_mod _ _ _ _ (retained_prime_units i j).1
      (retained_prime_units i j).2.1]
  exact (retained_prime_units i j).2.2

 theorem nonparallel_original (i j : Fin 12) (h : i ≠ j) :
    (forms i).a * (forms j).b - (forms i).b * (forms j).a ≠ 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [forms] at *

 theorem nonparallel_outputs (i j : Fin 12) (h : i ≠ j) :
    (outputs i).a * (outputs j).b - (outputs i).b * (outputs j).a ≠ 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [outputs] at *

 theorem avoids_2 : Avoids outputs 2 := by
  refine ⟨0, 0, ?_⟩
  intro i
  fin_cases i <;> norm_num [outputs, AffineForm.eval]

 theorem avoids_3 : Avoids outputs 3 := by
  refine ⟨0, 0, ?_⟩
  intro i
  fin_cases i <;> norm_num [outputs, AffineForm.eval]

 theorem avoids_5 : Avoids outputs 5 := by
  refine ⟨0, 0, ?_⟩
  intro i
  fin_cases i <;> norm_num [outputs, AffineForm.eval]

 theorem avoids_7 : Avoids outputs 7 := by
  refine ⟨0, 0, ?_⟩
  intro i
  fin_cases i <;> norm_num [outputs, AffineForm.eval]

 theorem avoids_11 : Avoids outputs 11 := by
  refine ⟨0, 0, ?_⟩
  intro i
  fin_cases i <;> norm_num [outputs, AffineForm.eval]

/-- These exact outputs form a locally admissible affine system at every prime. -/
 theorem local_admissibility (p : ℕ) (hp : p.Prime) : Avoids outputs p := by
  by_cases hn : 12 < p
  · apply exists_pair_avoiding_integer (fun i => (outputs i).a)
      (fun i => (outputs i).b) (fun i => (outputs i).c) _ p hp hn
    intro i
    exact ⟨(bezout i).1, (bezout i).2.1, (bezout i).2.2, bezout_certificate i⟩
  · have hs : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 := by
      interval_cases p <;> norm_num at *
    rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact avoids_2
    · exact avoids_3
    · exact avoids_5
    · exact avoids_7
    · exact avoids_11

 theorem normalized_quotient (i : Fin 12) (x y : ℤ) :
    (forms i).eval (M0 + W * x) (N0 + W * y) / cofactors i =
      (outputs i).eval x y := by
  rw [← normalization i x y]
  exact Int.mul_ediv_cancel_left _ (ne_of_gt (cofactors_positive i))

/-- Exponents of the fixed powers removed at 2 and 3. -/
def exponent2 : Fin 12 → ℕ := ![1, 0, 6, 0, 3, 1, 0, 0, 1, 6, 0, 0]
def exponent3 : Fin 12 → ℕ := ![2, 0, 0, 2, 0, 2, 2, 0, 1, 3, 1, 2]

 theorem cofactor_parts (i : Fin 12) :
    cofactors i = (2 : ℤ) ^ exponent2 i * 3 ^ exponent3 i := by
  fin_cases i <;> norm_num [cofactors, exponent2, exponent3]

/-- The quotient is a unit at 2 and 3 throughout the progression, so the
fixed cofactor removes precisely their powers. -/
 theorem normalized_quotient_units (i : Fin 12) (x y : ℤ) :
    ((forms i).eval (M0 + W * x) (N0 + W * y) / cofactors i) % 2 ≠ 0 ∧
    ((forms i).eval (M0 + W * x) (N0 + W * y) / cofactors i) % 3 ≠ 0 := by
  rw [normalized_quotient]
  constructor
  · simpa [retainedPrimes] using retained_prime_residue i 0 x y
  · simpa [retainedPrimes] using retained_prime_residue i 1 x y

 theorem retained_primes_prime (j : Fin 8) : (retainedPrimes j).Prime := by
  fin_cases j <;> norm_num [retainedPrimes]

 theorem cofactors_divide_modulus (i : Fin 12) : cofactors i ∣ W := by
  fin_cases i <;> norm_num [cofactors, W]

 theorem affine_content_one (i : Fin 12) :
    Int.gcd (Int.gcd (outputs i).a (outputs i).b : ℤ) (outputs i).c = 1 := by
  fin_cases i <;> norm_num [outputs, Int.gcd]

 theorem positive_forms (m n : ℤ) (hn : 0 < n) (hlo : 5589 * n < 2 * m) (i : Fin 12) :
    0 < (forms i).eval m n := by
  fin_cases i <;> simp [forms, LinearForm.eval] <;> omega

 theorem outputs_nonzero (i : Fin 12) (x y : ℤ) : (outputs i).eval x y ≠ 0 := by
  have h := retained_prime_residue i 0 x y
  intro hz
  simp [hz] at h

 theorem forms_nonzero_on_lattice (i : Fin 12) (x y : ℤ) :
    (forms i).eval (M0 + W * x) (N0 + W * y) ≠ 0 := by
  rw [← normalization i x y]
  exact mul_ne_zero (ne_of_gt (cofactors_positive i)) (outputs_nonzero i x y)

/-- Uniform exact divisibility at 2 for every factor in the CRT progression. -/
 theorem exact_two_part (i : Fin 12) (x y : ℤ) :
    (2 : ℤ) ^ exponent2 i ∣ (forms i).eval (M0 + W * x) (N0 + W * y) ∧
    ¬ (2 : ℤ) ^ (exponent2 i + 1) ∣ (forms i).eval (M0 + W * x) (N0 + W * y) := by
  rw [← normalization i x y, cofactor_parts, mul_assoc]
  apply exact_power_part _ _ _ (by norm_num)
  have hu : (outputs i).eval x y % 2 ≠ 0 := by
    simpa [retainedPrimes] using retained_prime_residue i 0 x y
  have hthree : (3 : ℤ) ^ exponent3 i % 2 = 1 := by
    fin_cases i <;> norm_num [exponent3]
  simpa [Int.mul_emod, hthree] using hu

/-- Uniform exact divisibility at 3 for every factor in the CRT progression. -/
 theorem exact_three_part (i : Fin 12) (x y : ℤ) :
    (3 : ℤ) ^ exponent3 i ∣ (forms i).eval (M0 + W * x) (N0 + W * y) ∧
    ¬ (3 : ℤ) ^ (exponent3 i + 1) ∣ (forms i).eval (M0 + W * x) (N0 + W * y) := by
  rw [← normalization i x y, cofactor_parts, mul_comm ((2 : ℤ) ^ exponent2 i), mul_assoc]
  apply exact_power_part _ _ _ (by norm_num)
  rw [Int.mul_emod, residue3]
  fin_cases i <;> norm_num [exponent2, mod3Units]

end Rank7

end RankCertificates.PrimePatterns
