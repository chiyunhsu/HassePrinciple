/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

public import HassePrinciple.HilbertSymbol.Basic

/-!
# Existence theorem
-/
@[expose] public section

namespace hilbertSym


/-- Given a finite set of rational numbers {a_i}_{i ∈ I} and functions from I to {±1} for each
place of ℚ, there exists a rational number x such that the Hilbert symbol of x and a_i at each place
is given by the respective function -/
theorem exists_rat_with_prescribed_hilbert_symbols_at_finitely_many_places
    {I : Type*} [Finite I] (a : I → ℚˣ) (efin : I × ℕ → ℤˣ) (einf : I → ℤˣ) :
    ∃ x : ℚˣ, ∀ i : I, ∀ n : ℕ, efin (i, n) = atP x (a i) (Nat.nth Nat.Prime n) ∧
      einf i = atInfty x (a i) ↔
      ∃ S : Finset ℕ, ∀ n , n ∉ S → efin (i, n) = 1 ∧
        ∀ i : I, einf i * ∏ (n ∈ S), efin (i, n) = 1 ∧
        ∀ n : ℕ, ∃ xn : ℚ_[Nat.nth Nat.Prime n], efin (i, n) = hilbertSym xn (a i) ∧
          ∃ xr : ℝ, einf i = hilbertSym xr (a i) := by
  sorry

end hilbertSym
