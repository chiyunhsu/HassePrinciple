/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

public import HassePrinciple.QuadraticForm.Basic
public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers

public import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp

/-! # Quadratic forms over ℚ -/

@[expose] public section

open Module QuadraticMap

namespace QuadraticForm

-- Let `V` be a `ℚ`-vector space.
variable {V : Type*} [AddCommGroup V] [Module ℚ V]

-- Let `Q` be a quadratic form on `V`.
variable (Q : QuadraticForm ℚ V)

/-- A quadratic form over `ℚ` is everywhere locally isotropic if it has nontrivial
`p`-adic points for all `p`, and real points. -/
def EverywhereLocallyIsotropic :=
  (∀ (p : ℕ) [Fact (p.Prime)], (Q.baseChange ℚ_[p]).Isotropic) ∧ (Q.baseChange ℝ).Isotropic

variable {Q}

-- The easy implication of the Hasse-Minkowski theorem.
theorem _root_.QuadraticMap.Isotropic.everywhereLocallyIsotropic (h : Q.Isotropic) :
    Q.EverywhereLocallyIsotropic := by
  obtain ⟨x, ⟨hx, hxne0⟩⟩ := represents_zero_iff_isotropic.mpr h
  refine ⟨fun _ _ => ?_, ?_⟩ <;>
  exact represents_zero_iff_isotropic.mp ⟨1 ⊗ₜ x, ⟨by simp [hx], by simp [hxne0]⟩⟩

/- Will follow from `QuadraticMap.nondegenerate_of_anisotropic` and
  `QuadraticMap.degenerate_baseChange`. -/
theorem HasseMinkowski_of_degenerate (Q : QuadraticForm ℚ V) (hQ : ¬ Q.Nondegenerate) :
    Q.Isotropic ↔ Q.EverywhereLocallyIsotropic := by
  have dQ := Q.nondegenerate_of_anisotropic.mt hQ
  have dR := ((Q.baseChange ℝ).nondegenerate_of_anisotropic).mt (degenerate_baseChange (A := ℝ) hQ)
  simp only [Isotropic, dQ, not_false_eq_true, EverywhereLocallyIsotropic, dR, and_true, true_iff]
  intro p hp
  exact ((Q.baseChange ℚ_[p]).nondegenerate_of_anisotropic).mt (degenerate_baseChange hQ)

namespace EverywhereLocallyIsotropic

lemma isotropic_of_rank_zero [Module.Finite ℚ V] (hr : finrank ℚ V = 0)
    (hQ' : Q.EverywhereLocallyIsotropic) : Q.Isotropic := by
  have h' := hQ'.2
  contrapose! h'
  exact QuadraticMap.anisotropic_of_rank_zero (by simp [hr])

lemma isotropic_of_rank_one (hr : finrank ℚ V = 1) (hQ : Q.EverywhereLocallyIsotropic) :
    Q.Isotropic := by
  simpa [isotropic_iff_zero_of_rank_one hr, baseChange_ext_iff, Q.ext_iff] using
    (isotropic_iff_zero_of_rank_one (by simp [hr])).mp hQ.2

lemma LocalGlobal (a : ℚ) (hpos : a > 0) (h : ∀ (p : ℕ) [inst : Fact (Nat.Prime p)], IsSquare (a : ℚ_[p])) : IsSquare a := by
  rw [Rat.isSquare_iff]
  have num_pos : a.num > 0 := Rat.num_pos.mpr hpos
  let a_num := a.num.toNat
  #check Padic.valuation_pow
  #check Padic.valuation_ratCast
  #check Nat.eq_of_factorization_eq'
  #check associated_of_factorization_eq
  #check factorization_mul
  have : a_num = a.num := Int.toNat_of_nonneg (le_of_lt num_pos)
  have : ∀ (p : ℕ) [inst : Fact (Nat.Prime p)], Even (padicValRat p a) := by sorry
  constructor
  · sorry
  · sorry



lemma isotropic_of_rank_two [FiniteDimensional ℚ V] (hr : finrank ℚ V = 2) (hQ : Q.Nondegenerate)
    (hQ' : Q.EverywhereLocallyIsotropic) : Q.Isotropic := by
  -- obtain ⟨w, hw⟩ := QuadraticForm.equivalent_weightedSumSquares Q
  have : NeZero (Module.finrank ℚ V) := by sorry
  obtain ⟨w, hw⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate'
    (QuadraticMap.nondegenerate_associated_iff.mpr hQ).1
  change Equivalent Q (QuadraticMap.weightedSumSquares ℚ (fun i => (w i : ℚ))) at hw
  obtain ⟨hQ'P, hQ'R⟩ := hQ'
  rw [← represents_zero_iff_isotropic] at *
  rw [Equivalent.represents_iff hw]
  have heq := (Equivalent.baseChange ℝ hw).trans (QuadraticForm.baseChange_weightedSumSquares ℚ ℝ fun i => (w i : ℚ))
  rw [Equivalent.represents_iff heq] at hQ'R
  --
  obtain ⟨x, hx⟩ : ∃ (x : ℚ), x ^ 2 = -w 1 / w 0 := by sorry
  rw [hr] at w
  use fun i => if i = 0 then x else 1
  simp

  #check Padic.valuation
  #check Rat.padicValuation
  #check padicValRat --Good
  #check Nat.ordProj_mul
  #check Nat.factorization

  -- obtain ⟨x, hx⟩ := hQ'R
  -- simp only [eq_ratCast, weightedSumSquares_apply, smul_eq_mul] at hx
  sorry

end EverywhereLocallyIsotropic

end QuadraticForm
