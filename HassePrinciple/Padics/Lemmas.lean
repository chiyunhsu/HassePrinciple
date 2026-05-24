/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/

module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Auxiliary result about padic numbers. -/

@[expose] public section

/-- An indexed family `f : σ → M` of elements is called primitive if at least one of the
  elements in the image is a unit. -/
def Function.IsPrimitive {M σ : Type*} [Monoid M] (f : σ → M) : Prop :=
   ∃ (s : σ), IsUnit (f s)

namespace PadicInt

/-- epsilon(u) is the class modulo 2 of (u-1)/2. -/
noncomputable def epsilon (u : (PadicInt 2)ˣ) : ℤ :=
  if (u.val).appr 2 % 4 = 1 then 0 else 1

/-- omega(u) is the class modulo 2 of (u^2-1)/8. -/
noncomputable def omega (u : (PadicInt 2)ˣ) : ℤ :=
  if (u.val).appr 3 % 8 = 1 ∨ (u.val).appr 3 % 8 = 7 then 0 else 1

end PadicInt

namespace Padic

variable {p : ℕ} [Fact (Nat.Prime p)] (x : ℚ_[p]ˣ)

/-- TODO -/
lemma norm_mul_pow_neg_valuation_eq_one : ‖(x : ℚ_[p]) * p ^ (- valuation x.val)‖ = 1 := by
  sorry

/-- TODO -/
noncomputable def unitPart : ℤ_[p]ˣ :=
  PadicInt.mkUnits (norm_mul_pow_neg_valuation_eq_one x)

lemma map_unitPart (x : ℚ_[p]ˣ) :
    Units.map (algebraMap ℤ_[p] ℚ_[p]) (unitPart x) = x := by
  sorry

/-- TODO -/
lemma norm_natCast_eq_one_of_ne_two {n : ℕ} (hn : n ≠ 2) : ‖(n : ℚ_[2])‖ = 1 := by
  sorry

/-- TODO -/
noncomputable abbrev p2 {n : ℕ} (hn : n ≠ 2) : ℤ_[2]ˣ :=
  PadicInt.mkUnits (norm_natCast_eq_one_of_ne_two hn)

/-- TODO -/
noncomputable def legendreSym (u : ℤ_[p]ˣ) : ℤ := _root_.legendreSym p ((u.val).appr 1)

-- better name?
/-- TODO -/
lemma exists_nontrivial_zero {p : ℕ} [hp : Fact (Nat.Prime p)] {v : (ℚ_[p])ˣ} {x y z : ℚ_[p]}
    (hnontriv : (x, y, z) ≠ (0, 0, 0)) (hsol : z ^ 2 - p * x ^ 2 - v * y ^ 2 = 0) :
    ∃ z' y' : (ℚ_[p])ˣ, ∃ x' : ℤ_[p],
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
