module

public import HassePrinciple.LinearAlgebra.Basis.Chain
public import HassePrinciple.QuadraticForm.Basic
public import HassePrinciple.QuadraticForm.HilbertSymbol
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.Data.Fin.Basic

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

variable {k : Type*} [Field k] [Invertible (2 : k)] --[CharZero k]

-- Let `V` be a `k`-vector space.
variable {V : Type*} [AddCommGroup V] [Module k V]

-- Let `Q` be a quadratic form on `V`.
variable (Q : QuadraticForm k V)

/-- Auxiliary definition for `HasseMinkoskiInvariant`. -/
noncomputable def HasseMinkoskiInvariantAux {n : ℕ} (w : Fin n → kˣ) : ℤˣ :=
  ∏ p : Fin n × Fin n with p.1 < p.2, HilbertSymbol (w p.1) (w p.2)

lemma HasseMinkoskiInvariant_aux.eq_of_equivalent {n : ℕ} {w w' : Fin n → kˣ}
    (h : (QuadraticMap.weightedSumSquares k w).Equivalent (QuadraticMap.weightedSumSquares k w')) :
    HasseMinkoskiInvariantAux w = HasseMinkoskiInvariantAux w' := by
  sorry

variable [FiniteDimensional k V]

example {Q : QuadraticForm k V} (h : Q.Nondegenerate) :
    LinearMap.SeparatingLeft (QuadraticMap.associated Q) := by
  simp only [← QuadraticMap.nondegenerate_associated_iff] at h
  exact h.1

/-- Let `Q` be a quadratic form on `V` such wht `Q.associated` is `SeparatingLeft`, and
suppose that `Q` is equivalent to the diagonal quadratic form `a_1 X_1^2 + ⋯ + a_n X_n ^ 2`.
The Hasse-Minkowski invariant of `Q` is defined as the product `∏_{i < j} (a_i, a_j)`, where
`(·, ·)` denotes the Hilbert symbol.

This is denoted by `ε(Q)` in Serre's book. -/
noncomputable def HasseMinkoskiInvariant {Q : QuadraticForm k V}
    (hQ : LinearMap.SeparatingLeft Q.associated) : ℤˣ :=
  HasseMinkoskiInvariantAux (equivalent_weightedSumSquares_units_of_nondegenerate' Q hQ).choose

namespace HasseMinkoskiInvariant

variable {Q Q' : QuadraticForm k V} (hQ : LinearMap.SeparatingLeft Q.associated)

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

-- inferInstance fails (priority issue?)
noncomputable instance : Module ℚ_[p] ℚ_[p] := Semiring.toModule

instance : Invertible (2 : ℚ_[p]) := sorry

variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
  {Q : QuadraticForm ℚ_[p] V} (hQ : Q.Nondegenerate)

lemma represents_zero_iff_of_rank_three [FiniteDimensional ℚ_[p] V] (b : Basis (Fin 3) ℚ_[p] V) :
    Q.represents 0 ↔
      HilbertSymbol (-1 : ℚ_[p]ˣ)
        (Units.mk0 (-Q.discr b) (neg_ne_zero.mpr ((Q.nondegenerate_iff_discr_ne_zero b).mp hQ))) =
      HasseMinkoskiInvariant (Q.nondegenerate_associated_iff.mpr hQ).1 := by
  sorry

lemma represents_iff_of_rank_two [FiniteDimensional ℚ_[p] V] (b : Basis (Fin 2) ℚ_[p] V)
    (a : ℚ_[p]ˣ) :
    Q.represents a ↔
      HilbertSymbol a
        (Units.mk0 (-Q.discr b) (neg_ne_zero.mpr ((Q.nondegenerate_iff_discr_ne_zero b).mp hQ))) =
      HasseMinkoskiInvariant (Q.nondegenerate_associated_iff.mpr hQ).1 := by
  sorry

end Padic

end QuadraticForm
