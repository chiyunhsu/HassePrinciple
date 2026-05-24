/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

public import HassePrinciple.Padics.Lemmas
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.NumberTheory.LSeries.PrimesInAP

/-! # The Hilbert symbol -/

@[expose] public section

-- `k` is a field and typically will be either `ℝ` or `ℚ_[p]`, but we need less for the definition.

/-- TODO -/
noncomputable def hilbertSym {k : Type*} [Field k] (a b : k) : ℤ := by
  classical exact if a = 0 ∨ b = 0 then 0
    else if ∃ z x y : k, (z, x, y) ≠ (0, 0, 0) ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0 then 1
    else -1

namespace hilbertSym

section Field

variable {k : Type*} [Field k] {a b : k} (a' b' : k)

/-- If `a` and `b` are nonzero, then `hilbertSym a b` is nonzero. -/
lemma ne_zero_of_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : hilbertSym a b ≠ 0 := by
  sorry

/-- TODO -/
@[simp]
lemma mul_square_eq :
    hilbertSym (a * a'^2) (b * b'^2) = hilbertSym a b := by
  sorry

/-- TODO -/
lemma comm : hilbertSym a b = hilbertSym b a := by
  sorry

/-
# Basic properties of the Hilbert symbol
-/

/- May make sense to split in two lemmas, one for `QuadraticAlgebra k b 0 = k` and the other for
  `QuadraticAlgebra k b 0 ≠ k`. -/

/-- TODO -/
theorem eq_one_iff (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertSym a b = 1 ↔ ∃ t : QuadraticAlgebra k b 0, a = QuadraticAlgebra.norm t := by
  sorry

/-- TODO -/
@[simp]
theorem right_square_eq_one (ha : a ≠ 0) (hb : b ≠ 0) : hilbertSym a (b ^ 2) = 1 := by
  sorry

/-- TODO -/
@[simp]
theorem right_neg_self_eq_one (ha : a ≠ 0) : hilbertSym a (-a) = 1 := by
  sorry

/-- TODO -/
@[simp]
theorem right_one_minus_self_eq_one (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    hilbertSym a (1 - a) = 1 := by
  sorry

/-- TODO -/
@[simp]
theorem right_mul_eq_of_eq_one (hab : hilbertSym a b = 1) :
    hilbertSym a (b * b') = hilbertSym a b' := by
  sorry

/-- TODO -/
@[simp]
theorem right_neg_mul : hilbertSym a (- (a * b)) = hilbertSym a b := by
  sorry

/-- TODO -/
@[simp]
theorem right_minus_self_mul (ha : a ≠ 1) :
    hilbertSym a ((1 - a) * b) = hilbertSym a b := by
  sorry

end Field

/-
## Local properties: computation of the Hilbert symbol in the real and p-adic cases
-/

/-- TODO -/
theorem real_eq {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertSym a b = if 0 < a ∨ 0 < b then 1 else -1 := by
  sorry

open Padic PadicInt

section odd

variable {p : ℕ} [hp : Fact (Nat.Prime p)] (hp2 : p ≠ 2) {x y : (ℚ_[p])} (hx : x ≠ 0) (hy : y ≠ 0)

/- TODO: either make the next three lemmas private or rename them before pushing to Mathlib. -/

/-- TODO -/
lemma padic_odd_case00 (hx0 : x.valuation = 0) (hx0 : y.valuation = 0) :
    hilbertSym x y = Int.negOnePow (x.valuation * y.valuation) /- * epsilon (p2 hp2)) -/ *
      legendreSym (unitPart (Units.mk0 x hx)) * legendreSym (unitPart (Units.mk0 y hy)) := by
  sorry

/-- TODO -/
lemma padic_odd_case10 (hx1 : valuation (x : ℚ_[p]) = 1) (hy0 : valuation (y : ℚ_[p]) = 0) :
    hilbertSym x y = Int.negOnePow (valuation (x : ℚ_[p]) * valuation (y : ℚ_[p]) *
      epsilon (p2 hp2)) * legendreSym (unitPart (Units.mk0 x hx)) *
      legendreSym (unitPart (Units.mk0 y hy)) := by
  sorry

/-- TODO -/
lemma padic_odd_case11 (hx0 : valuation (x : ℚ_[p]) = 1) (hy0 : valuation (y : ℚ_[p]) = 1) :
    hilbertSym x y = Int.negOnePow (valuation (x : ℚ_[p]) * valuation (y : ℚ_[p]) *
      epsilon (p2 hp2)) * legendreSym (unitPart (Units.mk0 x hx)) *
      legendreSym (unitPart (Units.mk0 y hy)) := by
  sorry

/-- TODO -/
theorem padic_odd_eq :
    hilbertSym x y = Int.negOnePow (valuation (x : ℚ_[p]) * valuation (y : ℚ_[p]) *
      epsilon (p2 hp2)) * legendreSym (unitPart (Units.mk0 x hx)) *
      legendreSym (unitPart (Units.mk0 y hy)) := by
  sorry

end odd

section two

variable {x y : (ℚ_[2])} (hx : x ≠ 0) (hy : y ≠ 0)

/- TODO: either make the next three lemmas private or rename them before pushing to Mathlib. -/

/-- TODO -/
lemma two_adic_case00 (hx0 : valuation (x : ℚ_[2]) = 0) (hy0 : valuation (y : ℚ_[2]) = 0) :
    hilbertSym x y = Int.negOnePow (epsilon (unitPart (Units.mk0 x hx)) *
      epsilon (unitPart (Units.mk0 y hy)) + valuation (x : ℚ_[2]) *
      omega (unitPart (Units.mk0 y hy)) + valuation (y : ℚ_[2]) *
      omega (unitPart (Units.mk0 x hx))) := by
  sorry

/-- TODO -/
lemma two_adic_case10 (hx0 : valuation (x : ℚ_[2]) = 1) (hy0 : valuation (y : ℚ_[2]) = 0) :
    hilbertSym x y = Int.negOnePow (epsilon (unitPart (Units.mk0 x hx)) *
      epsilon (unitPart (Units.mk0 y hy)) + valuation (x : ℚ_[2]) *
      omega (unitPart (Units.mk0 y hy)) + valuation (y : ℚ_[2]) *
      omega (unitPart (Units.mk0 x hx))) := by
  sorry

/-- TODO -/
lemma two_adic_case11 (hx0 : valuation (x : ℚ_[2]) = 1) (hy0 : valuation (y : ℚ_[2]) = 1) :
    hilbertSym x y = Int.negOnePow (epsilon (unitPart (Units.mk0 x hx)) *
      epsilon (unitPart (Units.mk0 y hy)) + valuation (x : ℚ_[2]) *
      omega (unitPart (Units.mk0 y hy)) + valuation (y : ℚ_[2]) *
      omega (unitPart (Units.mk0 x hx))) := by
  sorry

/-- TODO -/
theorem two_adic_eq :
    hilbertSym x y = Int.negOnePow (epsilon (unitPart (Units.mk0 x hx)) *
      epsilon (unitPart (Units.mk0 y hy)) + valuation (x : ℚ_[2]) *
      omega (unitPart (Units.mk0 y hy)) + valuation (y : ℚ_[2]) *
      omega (unitPart (Units.mk0 x hx))) := by
  sorry

end two

-- do we need the bilinear form property? (see Theorem 2 and Cor.)
/-
# Global properties of the Hilbert symbol
-/
open Nat

/-- For `a, b : ℚ`, and for a prime `p : ℕ`, `atP a b p` denotes the Hilbert symbol of `a` and `b`
computed in `ℚ_[p]`. -/
noncomputable abbrev atP (a b : ℚ) (p : ℕ) [hp : Fact (Nat.Prime p)] : ℤ :=
  hilbertSym (a : ℚ_[p]) (b : ℚ_[p])

/-- TODO -/
noncomputable abbrev atInfty (a b : ℚ) : ℤ := hilbertSym (a : ℝ) (b : ℝ)

/-- TODO -/
scoped instance fact_prime_nth_prime (n : ℕ) : Fact (Nat.Prime (Nat.nth Nat.Prime n)) :=
  fact_iff.mpr (Nat.prime_nth_prime n)

/-- For all but finitely many primes `p`, the Hilbert symbol of `a` and `b` at `p` is `1`. -/
theorem almost_all_one (a b : ℚˣ) :
    ∀ᶠ (n : ℕ) in Filter.cofinite, atP a b (Nat.nth Nat.Prime n) = 1 := by
  sorry

/-- TODO -/
theorem prod_eq_one (a b : ℚˣ) :
    atInfty a b * ∏ᶠ (n : ℕ), atP a b (Nat.nth Nat.Prime n) = 1 := by
  sorry

end hilbertSym
