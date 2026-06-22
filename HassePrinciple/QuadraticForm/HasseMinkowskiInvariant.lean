/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

public import HassePrinciple.QuadraticForm.Basic
public import HassePrinciple.QuadraticForm.Chain
public import HassePrinciple.HilbertSymbol.Basic
public import HassePrinciple.HilbertSymbol.ExistenceTheorem
public import HassePrinciple.NumberTheory.ApproximationTheorem
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.Data.Fin.Basic

/-! # The Hasse-Minkowski invariant -/

@[expose] public section

section Prelim

lemma LinearMap.separatingLeft_of_equivalent {R M M' N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup M'] [Module R M] [Module R M'] [AddCommGroup N] [Module R N]
    [Invertible (2 : R)] {Q : QuadraticMap R M N} {Q' : QuadraticMap R M' N} (h : Q.Equivalent Q')
    (hQ : LinearMap.SeparatingLeft Q.associated) :
    LinearMap.SeparatingLeft Q'.associated := by
  sorry

end Prelim

namespace QuadraticForm

variable {k : Type*} [Field k] --[CharZero k]

-- Let `V` be a `k`-vector space.
variable {V : Type*} [AddCommGroup V] [Module k V]

-- Let `Q` be a quadratic form on `V`.
variable (Q : QuadraticForm k V)

/-- Auxiliary definition for `HasseMinkoskiInvariant`. -/
noncomputable def HasseMinkoskiInvariantAux {n : ℕ} (w : Fin n → kˣ) : ℤ :=
  ∏ p : Fin n × Fin n with p.1 < p.2, hilbertSym (w p.1 : k) (w p.2)

lemma HasseMinkoskiInvariantAux_def {n : ℕ} (w : Fin n → kˣ) :
    HasseMinkoskiInvariantAux w =
      ∏ p : Fin n × Fin n with p.1 < p.2, hilbertSym (w p.1 : k) (w p.2) := rfl

lemma HasseMinkoskiInvariant_aux.eq_of_equivalent {n m : ℕ} {w : Fin n → kˣ} {w' : Fin m → kˣ}
    (h : (QuadraticMap.weightedSumSquares k w).Equivalent (QuadraticMap.weightedSumSquares k w')) :
    HasseMinkoskiInvariantAux w = HasseMinkoskiInvariantAux w' := by
  sorry

variable [Invertible (2 : k)] [FiniteDimensional k V]

/-- Let `Q` be a quadratic form on `V` such that `Q.associated` is `SeparatingLeft`, and
suppose that `Q` is equivalent to the diagonal quadratic form `a_1 X_1^2 + ⋯ + a_n X_n ^ 2`.
The Hasse-Minkowski invariant of `Q` is defined as the product `∏_{i < j} (a_i, a_j)`, where
`(·, ·)` denotes the Hilbert symbol.

This is denoted by `ε(Q)` in Serre's book. -/
noncomputable def HasseMinkoskiInvariant {Q : QuadraticForm k V}
    (hQ : LinearMap.SeparatingLeft Q.associated) : ℤ :=
  HasseMinkoskiInvariantAux (equivalent_weightedSumSquares_units_of_nondegenerate' Q hQ).choose

namespace HasseMinkoskiInvariant

open _root_.QuadraticMap

variable {Q Q' : QuadraticForm k V} (hQ : LinearMap.SeparatingLeft Q.associated)

lemma weightedSumSquares {n : ℕ} (w : Fin n → kˣ) :
    HasseMinkoskiInvariant
      (nondegenerate_associated_iff.mpr (nondegenerate_weightedSumSquares w)).1 =
      ∏ p : Fin n × Fin n with p.1 < p.2, hilbertSym (w p.1 : k) (w p.2) := by
  simp only [HasseMinkoskiInvariant, ← HasseMinkoskiInvariantAux_def w]
  exact HasseMinkoskiInvariant_aux.eq_of_equivalent
    ((equivalent_weightedSumSquares_units_of_nondegenerate' (QuadraticMap.weightedSumSquares k w))
      (nondegenerate_associated_iff.mpr (nondegenerate_weightedSumSquares w)).1).choose_spec.symm

lemma eq_of_equivalent_weightedSumSquares {n : ℕ} {w : Fin n → kˣ}
    (h : Q.Equivalent (QuadraticMap.weightedSumSquares k w)) :
    HasseMinkoskiInvariant hQ =
      HasseMinkoskiInvariant (LinearMap.separatingLeft_of_equivalent h hQ) := by
  sorry

lemma eq_of_equivalent (h : Q.Equivalent Q') :
    HasseMinkoskiInvariant hQ =
      HasseMinkoskiInvariant (LinearMap.separatingLeft_of_equivalent h hQ) := by
  sorry

lemma eq_one_or_neg_one :
    HasseMinkoskiInvariant hQ = 1 ∨ HasseMinkoskiInvariant hQ = 1 := sorry

end HasseMinkoskiInvariant

open Module
section Padic

variable {p : ℕ} [Fact (Nat.Prime p)]

instance invertibleTwo : Invertible (2 : ℚ_[p]) := sorry

variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [FiniteDimensional ℚ_[p] V]
  {Q : QuadraticForm ℚ_[p] V} (hQ : Q.Nondegenerate)

lemma represents_zero_iff_of_rank_three (b : Basis (Fin 3) ℚ_[p] V) :
    Q.represents 0 ↔
      hilbertSym (-1) (-Q.discr b) =
        HasseMinkoskiInvariant (Q.nondegenerate_associated_iff.mpr hQ).1 := by
  sorry

lemma represents_iff_of_rank_two (b : Basis (Fin 2) ℚ_[p] V) (a : ℚ_[p]) :
    Q.represents a ↔
      hilbertSym a (-Q.discr b) =
        HasseMinkoskiInvariant (Q.nondegenerate_associated_iff.mpr hQ).1 := by
  sorry

end Padic

end QuadraticForm
