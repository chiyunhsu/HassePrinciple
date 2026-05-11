/-
Copyright (c) 2026b Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.PrimeCounting
public import HassePrinciple.Padics.Legendre


@[expose] public section

noncomputable section

namespace HilbertSymbol

-- k is a field and typically will be either ℝ or ℚ_p, but we need less for the definition.
variable {k : Type*} [Field k] --[DecidableEq k] --[CharZero k]

/-TODO-/
noncomputable def _root_.HilbertSymbol (a b : kˣ) : ℤˣ := by
  classical exact if ∃ z x y : k, (z, x, y) ≠ (0, 0, 0) ∧
  z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0 then 1 else -1

/-TODO-/
lemma well_defined_up_to_squares (a b a' b' : kˣ) :
    HilbertSymbol a b = HilbertSymbol (a * a' ^ 2) (b * b' ^ 2)  := by
  sorry

/-
# Basic properties of the Hilbert symbol
-/

/-TODO-/
def kb (b : kˣ) := QuadraticAlgebra k b 0

--may make sense to split in two lemmas, one for kb=k and the other for kb≠k.
/-TODO-/
theorem eq_one_iff (a b : kˣ) : HilbertSymbol a b = 1 ↔ ∃ t : kb b, a =
  QuadraticAlgebra.norm t  := by
  sorry

/-TODO-/
theorem symm (a b : kˣ) : HilbertSymbol a b = HilbertSymbol b a := by
  sorry

/-TODO-/
@[simp]
theorem one_of_square (a c : kˣ) : HilbertSymbol a (c ^ 2) = 1 := by
  sorry

/-TODO-/
@[simp]
theorem one_of_neg_self (a : kˣ) : HilbertSymbol a (-a) = 1 := by
  sorry

/-TODO-/
theorem one_of_one_minus_self (a : kˣ) (h : (1 : k) - a ≠ 0) :
    HilbertSymbol a (Units.mk0 ((1 : k) - a) h) = 1 := by
  sorry

/-TODO-/
theorem of_mul (a a' b : kˣ) (hab : HilbertSymbol a b = 1) : HilbertSymbol (a * a') b =
  HilbertSymbol a' b := by
  sorry

/-TODO-/
@[simp]
theorem of_neg_mul (a b : kˣ) : HilbertSymbol a (- (a * b)) = HilbertSymbol a b := by
  sorry

/-TODO-/
theorem of_minus_self_mul (a b : kˣ) (h : (1 : k) - a ≠ 0) :
    HilbertSymbol a ((Units.mk0 ((1 : k) - a) h) * b) = HilbertSymbol a b := by
  sorry

/-
# Computation of the Hilbert symbol in the real and p-adic cases
-/

/-TODO-/
theorem real (a b : ℝˣ) : HilbertSymbol a b = if (0 : ℝ) < a ∨ (0 : ℝ) < b then 1 else -1 := by
  sorry

open Padic
/-
ε(u) is the class modulo 2 of (u-1)/2.
-/
def ε (u : (PadicInt 2)ˣ) : ZMod 2 :=
  if (u.val).appr 2 % 4 = 1 then 0 else 1

/- ω(u) is the class modulo 2 of (u^2-1)/8.-/
def ω (u : (PadicInt 2)ˣ) : ZMod 2 :=
  let u_mod_8 := (u.val).appr 3 % 8
  if u_mod_8 = 1 ∨ u_mod_8 = 7 then 0 else 1

--Should we move this to the padics?
/-TODO-/
lemma is_unit_odd_p {p : ℕ} [hp : Fact (Nat.Prime p)] (hp2 : p ≠ 2) : ‖(p : ℚ_[2])‖ = 1 := by
  sorry

/-TODO-/
def p_in_Q2 {p : ℕ} [hp : Fact (Nat.Prime p)] (hp2 : p ≠ 2) : ℤ_[2]ˣ :=
  PadicInt.mkUnits (is_unit_odd_p hp2)

--better name?
/-TODO-/
lemma nontrivialzero {p : ℕ} [hp : Fact (Nat.Prime p)] (v : (ℚ_[p])ˣ) (z x y : ℚ_[p])
  (hnontriv : (x, y, z) ≠ (0, 0, 0)) (hsol : z ^ 2 - p * x ^ 2 - v * y ^ 2 = 0) :
  ∃ z' y' : (ℚ_[p])ˣ, ∃ x' : ℤ_[p], (z' : ℚ_[p])^2 - p*(x' : ℚ_[p])^2 - v*(y' : ℚ_[p])^2 = 0 := by
  sorry

--shall I replace the statements with the expected results of the formulas?
/-TODO-/
lemma padic_odd_p_case00 {p : ℕ} [hp : Fact (Nat.Prime p)] (hp2 : p ≠ 2) (x y : (ℚ_[p])ˣ)
  (hα0 : valuation (x : ℚ_[p]) = 0) (hβ0 : valuation (y : ℚ_[p]) = 0) :
  HilbertSymbol x y =
    let v_x := valuation (x : ℚ_[p])
    let v_y := valuation (y : ℚ_[p])
    let u_x := padicUnitPart x
    let u_y := padicUnitPart y
    let p_in_Q2 := p_in_Q2 hp2
    let legpx := legp u_x
    let legpy := legp u_y
    (-1) ^ (v_x * v_y * ε (p_in_Q2 : ℤ_[2]ˣ)) * legpx * legpy := by
  sorry

/-TODO-/
lemma padic_odd_p_case10 {p : ℕ} [hp : Fact (Nat.Prime p)] (hp2 : p ≠ 2) (x y : (ℚ_[p])ˣ)
  (hα0 : valuation (x : ℚ_[p]) = 1) (hβ0 : valuation (y : ℚ_[p]) = 0) :
  HilbertSymbol x y =
    let v_x := valuation (x : ℚ_[p])
    let v_y := valuation (y : ℚ_[p])
    let u_x := padicUnitPart x
    let u_y := padicUnitPart y
    let p2 := p_in_Q2 hp2
    let legpx := legp u_x
    let legpy := legp u_y
    (-1) ^ (v_x * v_y * ε (p2 : ℤ_[2]ˣ)) * legpx * legpy := by
  sorry

/-TODO-/
lemma padic_odd_p_case11 {p : ℕ} [hp : Fact (Nat.Prime p)] (hp2 : p ≠ 2) (x y : (ℚ_[p])ˣ)
  (hα0 : valuation (x : ℚ_[p]) = 1) (hβ0 : valuation (y : ℚ_[p]) = 1) :
  HilbertSymbol x y =
    let v_x := valuation (x : ℚ_[p])
    let v_y := valuation (y : ℚ_[p])
    let u_x := padicUnitPart x
    let u_y := padicUnitPart y
    let p2 := p_in_Q2 hp2
    let legpx := legp u_x
    let legpy := legp u_y
    (-1) ^ (v_x * v_y * ε (p2 : ℤ_[2]ˣ)) * legpx * legpy := by
  sorry

/-TODO-/
theorem padic_odd_p {p : ℕ} [hp : Fact (Nat.Prime p)] (hp2 : p ≠ 2) (x y : (ℚ_[p])ˣ) :
  HilbertSymbol x y =
    let v_x := valuation (x : ℚ_[p])
    let v_y := valuation (y : ℚ_[p])
    let u_x := padicUnitPart x
    let u_y := padicUnitPart y
    let p2 := p_in_Q2 hp2
    let legpx := legp u_x
    let legpy := legp u_y
    (-1) ^ (v_x * v_y * ε (p2 : ℤ_[2]ˣ)) * legpx * legpy := by
  sorry

/-TODO-/
lemma padic_2_case00 (x y : (ℚ_[2])ˣ) (hα0 : valuation (x : ℚ_[2]) = 0)
(hβ0 : valuation (y : ℚ_[2]) = 0) :
  HilbertSymbol x y =
    let v_x := valuation (x : ℚ_[2])
    let v_y := valuation (y : ℚ_[2])
    let u_x := padicUnitPart x
    let u_y := padicUnitPart y
    (-1) ^ (ε u_x * ε u_y + v_x * ω u_y + v_y * ω u_x) := by
  sorry

/-TODO-/
lemma padic_2_case10 (x y : (ℚ_[2])ˣ) (hα0 : valuation (x : ℚ_[2]) = 1)
(hβ0 : valuation (y : ℚ_[2]) = 0) :
  HilbertSymbol x y =
    let v_x := valuation (x : ℚ_[2])
    let v_y := valuation (y : ℚ_[2])
    let u_x := padicUnitPart x
    let u_y := padicUnitPart y
    (-1) ^ (ε u_x * ε u_y + v_x * ω u_y + v_y * ω u_x) := by
  sorry

/-TODO-/
lemma padic_2_case11 (x y : (ℚ_[2])ˣ) (hα0 : valuation (x : ℚ_[2]) = 1)
(hβ0 : valuation (y : ℚ_[2]) = 1) :
  HilbertSymbol x y =
    let v_x := valuation (x : ℚ_[2])
    let v_y := valuation (y : ℚ_[2])
    let u_x := padicUnitPart x
    let u_y := padicUnitPart y
    (-1) ^ (ε u_x * ε u_y + v_x * ω u_y + v_y * ω u_x) := by
  sorry

/-TODO-/
theorem padic_2 (x y : (ℚ_[2])ˣ) :
  HilbertSymbol x y =
    let v_x := valuation (x : ℚ_[2])
    let v_y := valuation (y : ℚ_[2])
    let u_x := padicUnitPart x
    let u_y := padicUnitPart y
    (-1) ^ (ε u_x * ε u_y + v_x * ω u_y + v_y * ω u_x) := by
  sorry


-- do we need the bilinear form property? (see Theorem 2 and Cor.)
/-
# Global properties of the Hilbert symbol
-/
open Nat

-- For a, b in ℚˣ, and for all places of ℚ, we define the Hilbert symbol of a and b at that place.
def at_p (a b : ℚˣ) (p : ℕ) [hp : Fact (Nat.Prime p)] : ℤˣ :=
  let ap := Units.map (RingHom.toMonoidHom (algebraMap ℚ ℚ_[p])) a
  let bp := Units.map (RingHom.toMonoidHom (algebraMap ℚ ℚ_[p])) b
  HilbertSymbol ap bp

/-TODO-/
def at_infty (a b : ℚˣ) : ℤˣ :=
  let ar := Units.map (RingHom.toMonoidHom (algebraMap ℚ ℝ)) a
  let br := Units.map (RingHom.toMonoidHom (algebraMap ℚ ℝ)) b
  HilbertSymbol ar br

--do we need this in the blueprint?
/-TODO-/
instance fact_prime_nth_prime (n : ℕ) : Fact (Nat.Prime (Nat.nth Nat.Prime n)) := by
  rw [fact_iff]
  exact prime_nth_prime n

-- For all but finitely many primes p, the Hilbert symbol of a and b at p is 1.
/-TODO-/
theorem almost_all_one (a b : ℚˣ) :
  ∃ (S : Finset ℕ), ∀ n , n ∉ S →
    HilbertSymbol.at_p a b (Nat.nth Nat.Prime n) = 1 := by
  sorry

/-TODO-/
def hilbertSym_fun (a b : ℚˣ) : ℕ → ℤˣ := fun n => at_p a b (Nat.nth Nat.Prime n)

/-TODO-/
def hilbertSym_support (a b : ℚˣ) : Finset ℕ := (almost_all_one a b).choose

/-TODO-/
theorem product_formula (a b : ℚˣ) : HilbertSymbol.at_infty a b *
  ∏ (n ∈ hilbertSym_support a b), hilbertSym_fun a b n  = 1 := by
  sorry
/-
# Approximation theorem
-/

/-TODO-/
theorem chineseRemainder (n : ℕ) (h : n > 0) (a : Fin n → ℤ) (m : Fin n → ℕ) (hm : ∀ i, m i > 0)
(hcoprime : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j)) :
  ∃ x : ℤ, ∀ i, x % m i = a i % m i := by
  sorry

/- Since the proof concerns with the case where ℝ is part of the product, we assume it here
from the beginning. We can also do a different version if needed. -/
/-TODO-/
def Prod_over_S (S : Finset ℕ) := ℝ × (Π n : S, ℚ_[Nat.nth Nat.Prime n])

--If we state the approximation theorem in a concrete way as below, we don't need this definition.
/-TODO-/
def finite_embedding (S : Finset ℕ) : ℚ → Prod_over_S S :=
  fun x => ⟨algebraMap ℚ ℝ x, fun n => (algebraMap ℚ ℚ_[Nat.nth Nat.Prime n]) x⟩

-- I tried a concrete version without using topology. Can reformulate with sup if needed.
/-TODO-/
theorem approximation (S : Finset ℕ) : ∀ ε > 0, ∀ y : Prod_over_S S, ∃ x : ℚ,
  ‖y.1 - x‖ + Finset.sum (Finset.attach S) (fun n => ‖y.2 n - x‖) < ε := by
  sorry


/-
these two are "lemmas" to prove existence of rational numbers with given HS. Do we need that too?
-/

end HilbertSymbol
