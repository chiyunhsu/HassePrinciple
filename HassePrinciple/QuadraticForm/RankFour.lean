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
  obtain ⟨w, hw⟩ := Q.equivalent_weightedSumSquares
  let Q1 : QuadraticForm ℚ (Fin 2 → ℚ) :=
    QuadraticMap.weightedSumSquares ℚ ![w ⟨0, by omega⟩, w ⟨1, by omega⟩]
  let Q2 : QuadraticForm ℚ (Fin 2 → ℚ) :=
    QuadraticMap.weightedSumSquares ℚ ![-w ⟨2, by omega⟩, -w ⟨3, by omega⟩]
  have hp (p : ℕ) [Fact (Nat.Prime p)] : ∃ xₚ : ℚ_[p]ˣ, (Q1.baseChange ℚ_[p]).represents xₚ.1 ∧
    (Q2.baseChange ℚ_[p]).represents xₚ.1 := sorry
  obtain ⟨xr, hxr⟩ :
      ∃ x : ℝˣ, (Q1.baseChange ℝ).represents x.1 ∧ (Q2.baseChange ℝ).represents x.1 :=
    sorry
  have hp' (p : ℕ) [Fact (Nat.Prime p)] :
    hilbertSym (hp p).choose.1 (-(w ⟨0, by omega⟩)* (w ⟨1, by omega⟩)) =
      hilbertSym (w ⟨0, by omega⟩) (w ⟨1, by omega⟩) ∧
        hilbertSym (hp p).choose.1 (-(w ⟨2, by omega⟩)* (w ⟨3, by omega⟩)) =
        hilbertSym (w ⟨3, by omega⟩) (w ⟨3, by omega⟩) := sorry
  have hreal' : hilbertSym xr.1 (-(w ⟨0, by omega⟩)* (w ⟨1, by omega⟩)) =
      hilbertSym (w ⟨0, by omega⟩) (w ⟨1, by omega⟩) ∧
        hilbertSym xr.1 (-(w ⟨2, by omega⟩)* (w ⟨3, by omega⟩)) =
        hilbertSym (w ⟨3, by omega⟩) (w ⟨3, by omega⟩) :=
    sorry
  obtain ⟨x, hx⟩ : ∃ (x : ℚˣ), hilbertSym x.1 (-(w ⟨0, by omega⟩)* (w ⟨1, by omega⟩)) =
      hilbertSym (w ⟨0, by omega⟩) (w ⟨1, by omega⟩) ∧
        hilbertSym x.1 (-(w ⟨2, by omega⟩)* (w ⟨3, by omega⟩)) =
        hilbertSym (w ⟨3, by omega⟩) (w ⟨3, by omega⟩) := by
    have (p : Nat.Primes) : Fact (Nat.Prime p) := sorry
    have hprod :
      ∏ᶠ (p : Nat.Primes), hilbertSym (hp p).choose.1 (-(w ⟨0, by omega⟩)* (w ⟨1, by omega⟩)) *
        hilbertSym (w ⟨0, by omega⟩) (w ⟨1, by omega⟩) = 1 := sorry
    have hprod' :
      ∏ᶠ (p : Nat.Primes), hilbertSym (hp p).choose.1 (-(w ⟨2, by omega⟩)* (w ⟨3, by omega⟩)) *
        hilbertSym (w ⟨2, by omega⟩) (w ⟨3, by omega⟩) = 1 := sorry
    sorry
  let Q3 : QuadraticForm ℚ (Fin 3 → ℚ) :=
    QuadraticMap.weightedSumSquares ℚ ![w ⟨0, by omega⟩, w ⟨1, by omega⟩, -x]
  let Q4 : QuadraticForm ℚ (Fin 3 → ℚ) :=
    QuadraticMap.weightedSumSquares ℚ ![w ⟨2, by omega⟩, w ⟨3, by omega⟩, -x]
  have hrep_p (p : ℕ) [Fact (Nat.Prime p)] : (Q3.baseChange ℚ_[p]).represents 0 := sorry
  have hrep_p' (p : ℕ) [Fact (Nat.Prime p)] : (Q4.baseChange ℚ_[p]).represents 0 := sorry
  have hrep_r : (Q3.baseChange ℝ).represents 0 := sorry
  have hrep_r' : (Q4.baseChange ℝ).represents 0 := sorry
  have hrep0 : Q3.represents 0 := sorry
  have hrep0' : Q4.represents 0 := sorry
  have hrep : Q1.represents x := sorry
  have hrep' : Q2.represents x := sorry
  have hw_rep : (QuadraticMap.weightedSumSquares ℚ w).Isotropic := by
    have heq : (QuadraticMap.weightedSumSquares ℚ w).Equivalent (Q1.prod (-Q2)) := ⟨
      finFinrankLinearEquivProd hr, by
      intro f
      simp only [finFinrankLinearEquivProd, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta,
        Fin.isValue, Fin.mk_one, finCongr_apply, AddHom.toFun_eq_coe, AddHom.coe_mk,
        QuadraticMap.prod_apply, QuadraticMap.weightedSumSquares_apply, smul_eq_mul,
        Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        QuadraticMap.neg_apply, neg_mul, neg_add_rev, neg_neg, Q1, Q2]
      calc _
        _ =  ∑ (x : Fin 4), w (finCongr hr.symm x) *
        (f (finCongr hr.symm x) * f (finCongr hr.symm x)) := by
          simp only [finCongr_apply, Fin.sum_univ_four, add_assoc, add_comm (w ⟨3,_⟩ * _)]
          congr
        _ =  ∑ x, w x * (f x * f x) := Fintype.sum_equiv (finCongr (Eq.symm hr))
          (fun x ↦ w ((finCongr (Eq.symm hr)) x) *
            (f ((finCongr (Eq.symm hr)) x) * f ((finCongr (Eq.symm hr)) x)))
          (fun x ↦ w x * (f x * f x)) (congrFun rfl)⟩
    apply heq.symm.isotropic
    rw [prod_isotropic_iff']
    · sorry
    · sorry
    · sorry
  exact hw.symm.isotropic hw_rep

end QuadraticForm.EverywhereLocallyIsotropic
