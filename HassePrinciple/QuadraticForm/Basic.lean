/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct

@[expose] public section

namespace QuadraticForm

variable {K V : Type*} [Field K] [Invertible 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [NeZero (Module.finrank K V)]

theorem equivalent_weightedSumSquares' (Q : QuadraticForm K V) :
    ∃ (w : Fin (Module.finrank K V) → K), w (0 : Fin (Module.finrank K V)) = 1 ∧
      QuadraticMap.Equivalent Q (QuadraticMap.weightedSumSquares K w) := by
  sorry

theorem equivalent_weightedSumSquares_units_of_nondegenerate
    {Q : QuadraticForm K V} (hQ : Q.Nondegenerate) :
    ∃ (w : Fin (Module.finrank K V) → Kˣ), w (0 : Fin (Module.finrank K V)) = 1 ∧
      QuadraticMap.Equivalent Q (QuadraticMap.weightedSumSquares K w) := by
  sorry


end QuadraticForm
namespace QuadraticMap

section Represents

section CommSemiring

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- A quadratic form is isotropic if it vanishes on some nonzero vector. -/
abbrev Isotropic (Q : QuadraticMap R M N) := ¬ Q.Anisotropic

/-- `Q : QuadraticMap R M N` represents `n : N` if there exists a nonzero `x : V` such that
  `Q x = 0`. -/
def represents (Q : QuadraticMap R M N) (n : N) : Prop :=
  ∃ x : M, Q x = n ∧ x ≠ 0

lemma represents_zero_iff_isotropic {Q : QuadraticMap R M N} :
    Q.represents 0 ↔ Q.Isotropic := by
  sorry

lemma Equivalent.represents {Q Q' : QuadraticMap R M N} (h : Q.Equivalent Q') {n : N}
    (hQ : Q.represents n) :
    Q'.represents n := by
  sorry

lemma Equivalent.represents_iff {Q Q' : QuadraticMap R M N} (h : Q.Equivalent Q') (n : N) :
    Q.represents n ↔ Q'.represents n :=
  ⟨fun hQ ↦ h.represents hQ, fun hQ ↦ h.symm.represents hQ⟩

lemma Equivalent.isotropic {Q Q' : QuadraticMap R M N} (h : Q.Equivalent Q') (hQ : Q.Isotropic) :
    Q'.Isotropic := by
  sorry

lemma Equivalent.isotropic_iff {Q Q' : QuadraticMap R M N} (h : Q.Equivalent Q') :
    Q.Isotropic ↔ Q'.Isotropic :=
  ⟨fun hQ ↦ h.isotropic hQ, fun hQ ↦ h.symm.isotropic hQ⟩

end CommSemiring

section CommRing

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

lemma nondegenerate_of_anisotropic [Invertible (2 : R)] {Q : QuadraticMap R M N}
    (hQ : Q.Anisotropic) : Q.Nondegenerate :=
  sorry

open QuadraticMap

-- The rank zero case of Hasse-Minkowski will follow trivially from this lemma:
lemma anisotropic_of_rank_zero [IsDomain R] [StrongRankCondition R] [Module.Finite R M]
    [Module.IsTorsionFree R M] (hr : Module.finrank R M = 0) (Q : QuadraticMap R M N) :
    Q.Anisotropic := by
  rw [Module.finrank_zero_iff] at hr
  exact fun x _ ↦ Subsingleton.eq_zero x

-- The rank one case of Hasse-Minkowski will follow from:
lemma anisotropic_of_rank_one [IsDomain R] [StrongRankCondition R] [Module.IsTorsionFree R M]
    (hr : Module.finrank R M = 1) {Q : QuadraticMap R M N} (hQ : Q ≠ 0) :
    Q.Anisotropic := by
  sorry

end CommRing

end Represents

end QuadraticMap

namespace QuadraticForm

lemma degenerate_baseChange {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M]
    [Module R M] [Invertible (2 : R)] {Q : QuadraticForm R M}
    (hQ : ¬ Q.Nondegenerate) :
    ¬ (Q.baseChange A).Nondegenerate := by
  sorry

section Field

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

-- Condition (ii) seems annoying to state, can we avoid it?
lemma represents_iff_sub_isotropic {Q : QuadraticForm K V} (hQ : Q.Isotropic)
    (hQ' : Q.Nondegenerate) (r : Kˣ) :
    Q.represents r ↔
      (Q.prod (QuadraticMap.weightedSumSquares K ![-r])).Isotropic := sorry

lemma prod_isotropic_iff {Q : QuadraticForm K V} (hQ : Q.Nondegenerate) {Q' : QuadraticForm K W}
    (hQ' : Q'.Nondegenerate) :
    (Q.prod Q').Isotropic ↔ ∃ r : Kˣ, Q.represents r ∧ Q'.represents r := sorry

lemma prod_isotropic_iff' {Q : QuadraticForm K V} (hQ : Q.Nondegenerate) {Q' : QuadraticForm K W}
    (hQ' : Q'.Nondegenerate) :
    (Q.prod Q').Isotropic ↔ ∃ r : Kˣ,
      (Q.prod (QuadraticMap.weightedSumSquares K ![-r])).Isotropic ∧
      (Q'.prod (QuadraticMap.weightedSumSquares K ![-r])).Isotropic := sorry

end Field

section Hyperbolic

open Module

section CommRing

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

-- If needed for any particular result, replace `[CommRing R]` by `[Field R]`.

/-- A quadratic form is hyperbolic if it is equivalent to the form X^2 - Y^2. -/
def IsHyperbolic (Q : QuadraticForm R V) : Prop :=
  Q.Equivalent (QuadraticMap.weightedSumSquares R ![1, -1])

/-- The quadratic form `XY` on a two dimensional free `R`-module. -/
noncomputable abbrev XY (b : Basis (Fin 2) R V) : QuadraticForm R V where
  toFun v := b.repr v 0 * b.repr v 1
  toFun_smul r v := sorry
  exists_companion' := by
    let B : LinearMap.BilinMap R V R := {
      toFun v := {
        toFun w := b.repr v 0 * b.repr w 1 + b.repr w 0 * b.repr v 1
        map_add' v w := sorry
        map_smul' := sorry
      }
      map_add' w z := sorry
      map_smul' r w := sorry
    }
    exact ⟨B, by sorry⟩

lemma XY_isHyperbolic (b : Basis (Fin 2) R V) :
    IsHyperbolic (XY b) := sorry

lemma equivalent_hyperbolic_add {Q : QuadraticForm R V} (hQ : Q.Isotropic)
    (hQ' : Q.Nondegenerate) (r : R) :
    ∃ (A B : QuadraticForm R V), A.IsHyperbolic ∧ Q.Equivalent (A + B) := sorry

lemma represents_of_isotropic_of_nondegenerate {Q : QuadraticForm R V} (hQ : Q.Isotropic)
    (hQ' : Q.Nondegenerate) (r : R) :
    Q.represents r := sorry

end CommRing

end Hyperbolic

section Discr

-- TODO: PR to Mathlib before workshop

variable {R M n : Type*} [CommRing R] [Invertible (2 : R)] [AddCommGroup M] [Module R M]
  [Fintype n] [DecidableEq n] (b : Module.Basis n R M)
    {Q : QuadraticForm R M}

/-- A matrix representation of the quadratic form. -/
def toMatrix' (Q : QuadraticForm R (n → R)) : Matrix n n R :=
  LinearMap.toMatrix₂' R (Q.associated)

/-- A matrix representation of the quadratic form. -/
noncomputable def toMatrix (Q : QuadraticForm R M) : Matrix n n R :=
  LinearMap.toMatrix₂ b b (Q.associated)

lemma foo (Q : QuadraticForm R (n → R)) :
    Q.toMatrix (Pi.basisFun R n)  = Q.toMatrix' := by
  simp only [toMatrix, toMatrix']
  exact LinearEquiv.congr_arg rfl

/-- The discriminant of a quadratic form generalizes the discriminant of a quadratic polynomial. -/
noncomputable def discr (Q : QuadraticForm R M) : R :=
  (Q.toMatrix b).det

lemma nondegenerate_iff_discr_ne_zero [IsDomain R] :
    Q.Nondegenerate ↔ Q.discr b ≠ 0 := by
  simp [QuadraticForm.discr, QuadraticForm.toMatrix, ← QuadraticMap.nondegenerate_associated_iff,
    LinearMap.nondegenerate_iff_det_ne_zero (b := b)]

end Discr

end QuadraticForm
