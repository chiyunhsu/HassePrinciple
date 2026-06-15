/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

public import HassePrinciple.HilbertSymbol.Basic
public import HassePrinciple.NumberTheory.ApproximationTheorem

/-!
# Existence theorem
-/
@[expose] public section

namespace hilbertSym

/-- Given a finite set of rational numbers `{a_i}_{i ∈ I}` and numbers `e_{i,v} ∈ {± 1}`,
there exists a rational number `x` such that the Hilbert symbols `(x,a_i)_v` at each place `v`
is equal to `e_{i,v}` if and only if
1) for all `i`, almost all `e_{i,v}` are 1
2) for all `i`, the product of all `e_{i,v}` is 1
3) for each place `v`, there is some `x_v ∈ Q_v` with `(x,a_i)_v = e_{i,v}`. -/
theorem exists_rat_with_prescribed_hilbert_symbols_at_finitely_many_places
    {I : Type*} [Finite I] (a : I → ℚˣ) (efin : I × Nat.Primes → ℤ) (einf : I → ℤ)
    (hefinpm1 : ∀ i : I, ∀ p : Nat.Primes, efin (i, p) = 1 ∨ efin (i, p) = -1)
    (heinfpm1 : ∀ i : I, einf i = 1 ∨ einf i = -1) :
      (∃ x : ℚˣ, ∀ i : I, (∀ p : Nat.Primes, efin (i, p) = atP x (a i) p) ∧
        einf i = atInfty x (a i)) ↔
        (∀ i : I, (∀ᶠ (p : Nat.Primes) in Filter.cofinite, efin (i, p) = 1)) ∧
          (∀ i : I, (einf i * ∏ᶠ (p : Nat.Primes), efin (i, p) = 1)) ∧
          ((∀ (p : Nat.Primes), ∃ xp : ℚ_[p], ∀ i : I, efin (i, p) = hilbertSym xp (a i)) ∧
            ∃ xr : ℝ, ∀ i : I, einf i = hilbertSym xr (a i)) := by
  sorry

end hilbertSym
