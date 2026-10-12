module

public import RankCertificates.Rank6CharacterEvaluation

@[expose] public section

namespace RankCertificates.Rank6CharacterRows

open Rank6CharacterEvaluation Rank6ConstantCharacters

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {x y : ℤ} (h : PrimeSpecialization6 x y)

def columnsE (p : Fin 12 → ℕ) : Fin 12 → ℚ :=
  ![-1, 2, 3, 7, p 0, p 1, p 2, p 3, p 4, p 5, p 6, p 7]

def columnsEp (p : Fin 12 → ℕ) : Fin 12 → ℚ :=
  ![-1, 2, 3, 7, p 0, p 1, p 2, p 3, p 8, p 9, p 10, p 11]

def unitRowE (e : ℤ) (i : Fin 12) : Fin 12 → ZMod 2 :=
  ![quadraticCharacterBit (smallSign i 0), quadraticCharacterBit (smallSign i 1),
    quadraticCharacterBit (smallSign i 2), quadraticCharacterBit (smallSign i 3),
    movingBit e i 0, movingBit e i 1, movingBit e i 2, movingBit e i 3,
    movingBit e i 4, movingBit e i 5, movingBit e i 6, movingBit e i 7]

def unitRowEp (e : ℤ) (i : Fin 12) : Fin 12 → ZMod 2 :=
  ![quadraticCharacterBit (smallSign i 0), quadraticCharacterBit (smallSign i 1),
    quadraticCharacterBit (smallSign i 2), quadraticCharacterBit (smallSign i 3),
    movingBit e i 0, movingBit e i 1, movingBit e i 2, movingBit e i 3,
    movingBit e i 8, movingBit e i 9, movingBit e i 10, movingBit e i 11]

def ERowIndex (i : Fin 12) : Prop := i.val < 4 ∨ 8 ≤ i.val

def EpRowIndex (i : Fin 12) : Prop := i.val < 8

theorem E_relevant (i j : Fin 12) (hi : ERowIndex i) (hj : j.val < 8) :
    RelevantEntry i j := by
  by_cases hij : i = j
  · exact Or.inl hij
  apply Or.inr
  refine ⟨hij, ?_⟩
  by_cases hi0 : i = 0
  · exact Or.inl hi0
  by_cases hj0 : j = 0
  · exact Or.inr (Or.inl hj0)
  apply Or.inr ∘ Or.inr
  refine ⟨hij, hi0, hj0, ?_⟩
  rcases hi with hi | hi
  · exact Or.inl hi
  · exact Or.inr (Or.inr ⟨hi, hj⟩)

theorem Ep_relevant (i j : Fin 12) (hi : EpRowIndex i) (hj : j.val < 4 ∨ 8 ≤ j.val) :
    RelevantEntry i j := by
  by_cases hij : i = j
  · exact Or.inl hij
  apply Or.inr
  refine ⟨hij, ?_⟩
  by_cases hi0 : i = 0
  · exact Or.inl hi0
  by_cases hj0 : j = 0
  · exact Or.inr (Or.inl hj0)
  apply Or.inr ∘ Or.inr
  refine ⟨hij, hi0, hj0, ?_⟩
  by_cases hF : i.val < 4
  · exact Or.inl hF
  · exact Or.inr (Or.inl ⟨hi, hj⟩)

theorem unitRowE_actual (i : Fin 12) (hi : ERowIndex i) :
    @unitCharacterRow 12 (h.primes i) ⟨h.prime i⟩ (columnsE h.primes) =
      unitRowE (epsilon h) i := by
  funext j
  fin_cases j
  · change @unitCharacterParity (h.primes i) ⟨h.prime i⟩
      (Additive.ofMul (rationalSquareClass (-1))) = quadraticCharacterBit (smallSign i 0)
    simpa [smallColumns] using small_entry h i 0
  · change @unitCharacterParity (h.primes i) ⟨h.prime i⟩
      (Additive.ofMul (rationalSquareClass 2)) = quadraticCharacterBit (smallSign i 1)
    simpa [smallColumns] using small_entry h i 1
  · change @unitCharacterParity (h.primes i) ⟨h.prime i⟩
      (Additive.ofMul (rationalSquareClass 3)) = quadraticCharacterBit (smallSign i 2)
    simpa [smallColumns] using small_entry h i 2
  · change @unitCharacterParity (h.primes i) ⟨h.prime i⟩
      (Additive.ofMul (rationalSquareClass 7)) = quadraticCharacterBit (smallSign i 3)
    simpa [smallColumns] using small_entry h i 3
  · change @unitCharacterParity (h.primes i) ⟨h.prime i⟩
      (Additive.ofMul (rationalSquareClass (h.primes 0 : ℚ))) = movingBit (epsilon h) i 0
    exact moving_entry h i 0 (E_relevant i 0 hi (by decide))
  · change @unitCharacterParity (h.primes i) ⟨h.prime i⟩
      (Additive.ofMul (rationalSquareClass (h.primes 1 : ℚ))) = movingBit (epsilon h) i 1
    exact moving_entry h i 1 (E_relevant i 1 hi (by decide))
  · change @unitCharacterParity (h.primes i) ⟨h.prime i⟩
      (Additive.ofMul (rationalSquareClass (h.primes 2 : ℚ))) = movingBit (epsilon h) i 2
    exact moving_entry h i 2 (E_relevant i 2 hi (by decide))
  · change @unitCharacterParity (h.primes i) ⟨h.prime i⟩
      (Additive.ofMul (rationalSquareClass (h.primes 3 : ℚ))) = movingBit (epsilon h) i 3
    exact moving_entry h i 3 (E_relevant i 3 hi (by decide))
  · change @unitCharacterParity (h.primes i) ⟨h.prime i⟩
      (Additive.ofMul (rationalSquareClass (h.primes 4 : ℚ))) = movingBit (epsilon h) i 4
    exact moving_entry h i 4 (E_relevant i 4 hi (by decide))
  · change @unitCharacterParity (h.primes i) ⟨h.prime i⟩
      (Additive.ofMul (rationalSquareClass (h.primes 5 : ℚ))) = movingBit (epsilon h) i 5
    exact moving_entry h i 5 (E_relevant i 5 hi (by decide))
  · change @unitCharacterParity (h.primes i) ⟨h.prime i⟩
      (Additive.ofMul (rationalSquareClass (h.primes 6 : ℚ))) = movingBit (epsilon h) i 6
    exact moving_entry h i 6 (E_relevant i 6 hi (by decide))
  · change @unitCharacterParity (h.primes i) ⟨h.prime i⟩
      (Additive.ofMul (rationalSquareClass (h.primes 7 : ℚ))) = movingBit (epsilon h) i 7
    exact moving_entry h i 7 (E_relevant i 7 hi (by decide))
theorem unitRowEp_actual (i : Fin 12) (hi : EpRowIndex i) :
    @unitCharacterRow 12 (h.primes i) ⟨h.prime i⟩ (columnsEp h.primes) =
      unitRowEp (epsilon h) i := by
  funext j
  fin_cases j
  · change @unitCharacterParity (h.primes i) ⟨h.prime i⟩
      (Additive.ofMul (rationalSquareClass (-1))) = quadraticCharacterBit (smallSign i 0)
    simpa [smallColumns] using small_entry h i 0
  · change @unitCharacterParity (h.primes i) ⟨h.prime i⟩
      (Additive.ofMul (rationalSquareClass 2)) = quadraticCharacterBit (smallSign i 1)
    simpa [smallColumns] using small_entry h i 1
  · change @unitCharacterParity (h.primes i) ⟨h.prime i⟩
      (Additive.ofMul (rationalSquareClass 3)) = quadraticCharacterBit (smallSign i 2)
    simpa [smallColumns] using small_entry h i 2
  · change @unitCharacterParity (h.primes i) ⟨h.prime i⟩
      (Additive.ofMul (rationalSquareClass 7)) = quadraticCharacterBit (smallSign i 3)
    simpa [smallColumns] using small_entry h i 3
  · change @unitCharacterParity (h.primes i) ⟨h.prime i⟩
      (Additive.ofMul (rationalSquareClass (h.primes 0 : ℚ))) = movingBit (epsilon h) i 0
    exact moving_entry h i 0 (Ep_relevant i 0 hi (by decide))
  · change @unitCharacterParity (h.primes i) ⟨h.prime i⟩
      (Additive.ofMul (rationalSquareClass (h.primes 1 : ℚ))) = movingBit (epsilon h) i 1
    exact moving_entry h i 1 (Ep_relevant i 1 hi (by decide))
  · change @unitCharacterParity (h.primes i) ⟨h.prime i⟩
      (Additive.ofMul (rationalSquareClass (h.primes 2 : ℚ))) = movingBit (epsilon h) i 2
    exact moving_entry h i 2 (Ep_relevant i 2 hi (by decide))
  · change @unitCharacterParity (h.primes i) ⟨h.prime i⟩
      (Additive.ofMul (rationalSquareClass (h.primes 3 : ℚ))) = movingBit (epsilon h) i 3
    exact moving_entry h i 3 (Ep_relevant i 3 hi (by decide))
  · change @unitCharacterParity (h.primes i) ⟨h.prime i⟩
      (Additive.ofMul (rationalSquareClass (h.primes 8 : ℚ))) = movingBit (epsilon h) i 8
    exact moving_entry h i 8 (Ep_relevant i 8 hi (by decide))
  · change @unitCharacterParity (h.primes i) ⟨h.prime i⟩
      (Additive.ofMul (rationalSquareClass (h.primes 9 : ℚ))) = movingBit (epsilon h) i 9
    exact moving_entry h i 9 (Ep_relevant i 9 hi (by decide))
  · change @unitCharacterParity (h.primes i) ⟨h.prime i⟩
      (Additive.ofMul (rationalSquareClass (h.primes 10 : ℚ))) = movingBit (epsilon h) i 10
    exact moving_entry h i 10 (Ep_relevant i 10 hi (by decide))
  · change @unitCharacterParity (h.primes i) ⟨h.prime i⟩
      (Additive.ofMul (rationalSquareClass (h.primes 11 : ℚ))) = movingBit (epsilon h) i 11
    exact moving_entry h i 11 (Ep_relevant i 11 hi (by decide))

end RankCertificates.Rank6CharacterRows
