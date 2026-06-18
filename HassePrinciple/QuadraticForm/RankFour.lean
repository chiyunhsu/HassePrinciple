/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

public import HassePrinciple.QuadraticForm.HasseMinkowskiInvariant
public import HassePrinciple.QuadraticForm.RankThree
public import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct

/-! # The Hasse-Minkowski theorem for rank 4 quadratic forms -/

@[expose] public section

namespace QuadraticForm.EverywhereLocallyIsotropic

open QuadraticMap

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {Q : QuadraticForm ℚ V}

/-- TODO. -/
noncomputable def finFinrankLinearEquivProd (h : Module.finrank ℚ V = 4) :
    (Fin (Module.finrank ℚ V) → ℚ) ≃ₗ[ℚ] (Fin 2 → ℚ) × (Fin 2 → ℚ) where
  toFun x  := ⟨![x ⟨0, by omega⟩, x ⟨1, by omega⟩], ![x ⟨2, by omega⟩, x ⟨3, by omega⟩]⟩
  map_add'  x y := by simp
  map_smul' r x := by simp
  invFun x a :=
    ![x.1 ⟨0, by omega⟩, x.1 ⟨1, by omega⟩, x.2 ⟨0, by omega⟩, x.2 ⟨1, by omega⟩] (finCongr h a)
  left_inv x := by -- This is ridiculous, there has to be a better way
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
      Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ext a
    cases a with
    | mk n hn =>
      have hn : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
      aesop
  right_inv x := by
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.mk_one,
      finCongr_apply, Fin.cast_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.reduceFinMk,
      Matrix.cons_val]
    exact Prod.ext_iff.mpr ⟨List.ofFn_inj.mp rfl, List.ofFn_inj.mp rfl⟩

lemma isotropic_of_rank_four (hr : Module.finrank ℚ V = 4) (hQ : Q.Nondegenerate)
    (hQ' : Q.EverywhereLocallyIsotropic) :
    Q.Isotropic := by
  have : FiniteDimensional ℚ V :=
    Module.finite_of_finrank_pos (Nat.lt_of_sub_eq_sub_one hr)
  -- Q is equivalent to a₁ X₁^2 + a₂ X₂ ^ 2 + a₃ X₃ ^3 + a₄ X₄^2, for some a_i : ℚˣ
  obtain ⟨w, hw⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate'
    (QuadraticMap.nondegenerate_associated_iff.mpr hQ).1
  -- Q1 := a₁ X₁^2 + a₂ X₂ ^ 2, Q2 := - a₃ X₃ ^3 - a₄ X₄^2
  let Q1 : QuadraticForm ℚ (Fin 2 → ℚ) :=
    QuadraticMap.weightedSumSquares ℚ ![w ⟨0, by omega⟩, w ⟨1, by omega⟩]
  let Q2 : QuadraticForm ℚ (Fin 2 → ℚ) :=
    QuadraticMap.weightedSumSquares ℚ ![-w ⟨2, by omega⟩, -w ⟨3, by omega⟩]
  -- Since Q is equivalent to (QuadraticMap.weightedSumSquares ℚ w) and to (Q1.prod (-Q2)),
  -- it suffices to prove that (Q1.prod (-Q2)) is isotropic
  apply hw.symm.isotropic
  -- TODO: extract lemma
  have heq : (QuadraticMap.weightedSumSquares ℚ w).Equivalent (Q1.prod (-Q2)) := ⟨
    finFinrankLinearEquivProd hr, by
    intro f
    simp only [finFinrankLinearEquivProd, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta,
      Fin.isValue, Fin.mk_one, finCongr_apply, AddHom.toFun_eq_coe, AddHom.coe_mk,
      QuadraticMap.prod_apply, QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, QuadraticMap.neg_apply,
      Units.neg_smul, neg_add_rev, neg_neg, Q1, Q2]
    calc _
    _ =  ∑ (x : Fin 4), w (finCongr hr.symm x) *
    (f (finCongr hr.symm x) * f (finCongr hr.symm x)) := by
        simp only [finCongr_apply, Fin.sum_univ_four, add_assoc, add_comm ((w ⟨3,_⟩) • _)]
        congr
    _ =  ∑ x, w x * (f x * f x) := Fintype.sum_equiv (finCongr (Eq.symm hr))
        (fun x ↦ w ((finCongr (Eq.symm hr)) x) *
        (f ((finCongr (Eq.symm hr)) x) * f ((finCongr (Eq.symm hr)) x)))
        (fun x ↦ w x * (f x * f x)) (congrFun rfl)⟩
  apply heq.symm.isotropic
  rw [prod_isotropic_iff (by sorry) (by sorry)]
  --
  have hp (p : ℕ) [Fact (Nat.Prime p)] : ∃ xₚ : ℚ_[p]ˣ, (Q1.baseChange ℚ_[p]).represents xₚ.1 ∧
      (Q2.baseChange ℚ_[p]).represents xₚ.1 := by
    rw [← prod_isotropic_iff (by sorry) (by sorry)]
    let Q' : QuadraticForm ℚ ((Fin 2 → ℚ) × (Fin 2 → ℚ)) := Q1.prod Q2
    have : (QuadraticMap.prod (QuadraticForm.baseChange ℚ_[p] Q1) (QuadraticForm.baseChange ℚ_[p] Q2)).Equivalent
      (Q'.baseChange ℚ_[p]) := sorry
    sorry
  obtain ⟨xr, hxr⟩ :
      ∃ x : ℝˣ, (Q1.baseChange ℝ).represents x.1 ∧ (Q2.baseChange ℝ).represents x.1 :=
    sorry
  have hp' (p : ℕ) [Fact (Nat.Prime p)] :
    hilbertSym (hp p).choose.1 (-(w ⟨0, by omega⟩)* (w ⟨1, by omega⟩)) =
      hilbertSym (w ⟨0, by omega⟩).1 (w ⟨1, by omega⟩) ∧
        hilbertSym (hp p).choose.1 (-(w ⟨2, by omega⟩)* (w ⟨3, by omega⟩)) =
        hilbertSym (w ⟨3, by omega⟩).1 (w ⟨3, by omega⟩) := sorry
  have hreal' : hilbertSym xr.1 (-(w ⟨0, by omega⟩)* (w ⟨1, by omega⟩)) =
      hilbertSym (w ⟨0, by omega⟩).1 (w ⟨1, by omega⟩) ∧
        hilbertSym xr.1 (-(w ⟨2, by omega⟩)* (w ⟨3, by omega⟩)) =
        hilbertSym (w ⟨3, by omega⟩).1 (w ⟨3, by omega⟩) :=
    sorry
  obtain ⟨x, hx⟩ : ∃ (x : ℚˣ), hilbertSym x.1 (-(w ⟨0, by omega⟩)* (w ⟨1, by omega⟩)) =
      hilbertSym (w ⟨0, by omega⟩).1 (w ⟨1, by omega⟩) ∧
        hilbertSym x.1 (-(w ⟨2, by omega⟩)* (w ⟨3, by omega⟩)) =
        hilbertSym (w ⟨3, by omega⟩).1 (w ⟨3, by omega⟩) := by
    have (p : Nat.Primes) : Fact (Nat.Prime p) := sorry
    have hprod :
      ∏ᶠ (p : Nat.Primes), hilbertSym (hp p).choose.1 (-(w ⟨0, by omega⟩)* (w ⟨1, by omega⟩)) *
        hilbertSym (w ⟨0, by omega⟩).1 (w ⟨1, by omega⟩) = 1 := sorry
    have hprod' :
      ∏ᶠ (p : Nat.Primes), hilbertSym (hp p).choose.1 (-(w ⟨2, by omega⟩)* (w ⟨3, by omega⟩)) *
        hilbertSym (w ⟨2, by omega⟩).1 (w ⟨3, by omega⟩) = 1 := sorry
    sorry
  let Q3 : QuadraticForm ℚ (Fin 3 → ℚ) :=
    QuadraticMap.weightedSumSquares ℚ ![w ⟨0, by omega⟩, w ⟨1, by omega⟩, -x]
  let Q4 : QuadraticForm ℚ (Fin 3 → ℚ) :=
    QuadraticMap.weightedSumSquares ℚ ![w ⟨2, by omega⟩, w ⟨3, by omega⟩, -x]
  have hrep_p (p : ℕ) [Fact (Nat.Prime p)] : (Q3.baseChange ℚ_[p]).Isotropic := sorry
  have hrep_p' (p : ℕ) [Fact (Nat.Prime p)] : (Q4.baseChange ℚ_[p]).Isotropic := sorry
  have hrep_r : (Q3.baseChange ℝ).Isotropic := by
    sorry
  have hrep_r' : (Q4.baseChange ℝ).Isotropic := sorry
  have hrep0 : Q3.Isotropic:= by
    apply isotropic_of_rank_three Q3 (Module.finrank_fin_fun ℚ) ?_ ⟨hrep_p, hrep_r⟩
    · sorry
  have hrep0' : Q4.Isotropic := sorry
  have hrep : Q1.represents x := sorry
  have hrep' : Q2.represents x := sorry
  have hw_rep : (QuadraticMap.weightedSumSquares ℚ w).Isotropic := by

    apply heq.symm.isotropic
    rw [prod_isotropic_iff']
    · sorry
    · --TODO: golf, remove the erw
      rw [QuadraticMap.nondegenerate_iff_radical_eq_bot]
      simp only [Q1]
      erw [radical_weightedSumSquares]
      simp [Pi.spanSubset]
    · sorry
  sorry


end QuadraticForm.EverywhereLocallyIsotropic
