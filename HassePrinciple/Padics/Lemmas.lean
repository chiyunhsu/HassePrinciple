/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/

module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.NumberTheory.Padics.Hensel
public import Mathlib.Algebra.Polynomial.Basic

/-! # Auxiliary result about padic numbers. -/

@[expose] public section

/-- An indexed family `f : σ → M` of elements is called primitive if at least one of the
  elements in the image is a unit. -/
def Function.IsPrimitive {M σ : Type*} [Monoid M] (f : σ → M) : Prop :=
   ∃ (s : σ), IsUnit (f s)

namespace Padic

variable {p : ℕ} [Fact (Nat.Prime p)] (x : ℚ_[p]ˣ)

/-- Given a nonzero padic number `x`, the norm of `x` times `p` raised to the negative of its
valuation equals one. -/
lemma norm_mul_pow_neg_valuation_eq_one : ‖(x : ℚ_[p]) * p ^ (- valuation x.val)‖ = 1 := by
  sorry

/-- Given a nonzero padic number `x`, the unit part of `x` is defined as the element in `ℤ_[p]ˣ`
which is equal to  `x` times `p` raised to the negative of its valuation. -/
noncomputable def unitPart : ℤ_[p]ˣ :=
  PadicInt.mkUnits (norm_mul_pow_neg_valuation_eq_one x)

/-- The map that sends a padic integer to its unit part in ℤ_[p]ˣ is the natural inclusion. -/
lemma map_unitPart :
    Units.map (algebraMap ℤ_[p] ℚ_[p]) (unitPart x) = x := by
  sorry

/-- For an odd prime `p` different from 2, the element `p` in ℤ_[2]ˣ is defined. -/
noncomputable abbrev p2 (hp : p ≠ 2) : ℤ_[2]ˣ :=
  PadicInt.mkUnits (Padic.norm_natCast_eq_one_iff.mpr
    ((Nat.coprime_primes Nat.prime_two Fact.out).mpr hp.symm))

--better name?
/-- If `p` is a prime, `x, y, z in ℚ_[p]` satisfy `z ^ 2 - p * x ^ 2 - v * y ^ 2`, with `v` nonzero,
and not all of `x, y, z` are zero, then there exists a nontrivial solution to the same equation with
`z', y'` units in `ℤ_[p]ˣ` and `x'` in `ℤ_[p]`. -/
lemma exists_nontrivial_zero {v : (ℚ_[p])ˣ} {x y z : ℚ_[p]}
    (hnontriv : (x, y, z) ≠ (0, 0, 0)) (hsol : z ^ 2 - p * x ^ 2 - v * y ^ 2 = 0) :
    ∃ z' y' : ℤ_[p]ˣ, ∃ x' : ℤ_[p],
      (z' : ℚ_[p])^2 - p * (x' : ℚ_[p])^2 - v * (y' : ℚ_[p])^2 = 0 := by
  sorry

lemma common_root_tfae {σ ι : Type*} {f : ι → MvPolynomial σ ℤ_[p]}
    (hf : ∀ i, (f i).IsHomogeneous (f i).totalDegree) :
    List.TFAE [∃ (z : σ → ℚ_[p]), (∃ s, z s ≠ 0)  ∧ (∀ i : ι, (f i).aeval z = 0),
      ∃ (z : σ → ℤ_[p]), z.IsPrimitive ∧ ∀ i : ι, (f i).aeval z = 0,
      ∀ {n : ℕ} (hn : 1 ≤ n),  ∃ (z : σ → ZMod (p ^ n)), z.IsPrimitive ∧
        ∀ i : ι, ((f i).map (PadicInt.toZModPow n)).aeval z = 0] := by
  sorry

end Padic



/-! # Applications and Multivariable Hensel's Lemma. -/

@[expose] public section


namespace Polynomial

/-- An element in ℤ_p (p odd) is a square if its reduction modulo p is a square. -/
lemma squares_in_Zp {p : ℕ} [Fact (Nat.Prime p)] (hodd : p ≠ 2) (m : ℤ_[p]) (n : ℕ)
    (hmod : m.zmodRepr ≡ n ^ 2 [MOD p]) : ∃ x : ℤ_[p], m = x ^ 2 := by
  --let F : ℤ_[p][X] := X ^ 2 - m
  sorry

/-- An element in ℤ_2 is a square if its reduction modulo 8 is a square. -/
lemma squares_in_Z2 (m : ℤ_[2]) (n : ℕ)
    (hmod : m.zmodRepr ≡ n ^ 2 [MOD 8]) : ∃ x : ℤ_[2], m = x^2 := by sorry

end Polynomial


namespace PadicInt

/-! ## Multivariable Hensel's Lemma -/


/-- Serre's generalization of Hensel's lemma to a multivariable polynomial over ℤ_[p]. If a
polynomial f in m variables has a solution a modulo p^n, and a is a zero modulo p^k of one of its
partial derivatives, with 0 < 2k < n, then there exists a solution in ℤ_[p], which is congruent to
a modulo p^{n-k}. -/
theorem multivariable_hensel {p : ℕ} [Fact (Nat.Prime p)] {m : ℕ}
    {f : MvPolynomial (Fin m) ℤ_[p]} {a : Fin m → ℤ_[p]}
    {n k : ℤ} (hk : 0 < 2 * k ∧ 2 * k < n) {j : Fin m}
    (hF : n ≤ valuation (MvPolynomial.aeval a f))
    (hJ : valuation (MvPolynomial.aeval a (MvPolynomial.pderiv j f)) = k) :
      ∃ (z : Fin m → ℤ_[p]), (MvPolynomial.aeval z f = 0) ∧
        ∀ i, n - k ≤ valuation (z i - a i) := by
  sorry

/-- Same theorem, in terms of norms. TODO: Keep one. -/
theorem multivariable_hensel' {p : ℕ} [Fact (Nat.Prime p)] {m : ℕ}
    {f : MvPolynomial (Fin m) ℤ_[p]} {a : Fin m → ℤ_[p]}
    {n k : ℤ} (hk : 0 < 2 * k ∧ 2 * k < n) {j : Fin m}
    (hF : ‖(MvPolynomial.aeval a) f‖ ≤ p ^ (-n))
    (hJ : ‖(MvPolynomial.aeval a) (MvPolynomial.pderiv j f)‖ = p ^ (-k)) :
      ∃ (z : Fin m → ℤ_[p]), (MvPolynomial.aeval z f = 0) ∧ ∀ i, ‖z i - a i‖ < p ^ (-n + k) := by
  sorry

end PadicInt
