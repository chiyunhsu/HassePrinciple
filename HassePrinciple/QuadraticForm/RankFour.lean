/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

public import HassePrinciple.QuadraticForm.HasseMinkowskiInvariant
public import HassePrinciple.QuadraticForm.RankThree
public import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Prod


/-! # The Hasse-Minkowski theorem for rank 4 quadratic forms -/

@[expose] public section

namespace LinearMap

variable {R A M N P Q : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [AddCommMonoid M]
  [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q] [Module R M] [Module R N] [Module R P]
  [Module R Q] [SMulCommClass R R P] (f : M →ₗ[R] N →ₗ[R] P) (g : Q →ₗ[R] N)

lemma baseChange_compl₂ :
    (f.compl₂ g).baseChange A = (f.compl₂ g).baseChange A := by
  ext; simp

def BilinMap.baseChange_compl₁₂ {R A M P Q : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    [AddCommMonoid M] [AddCommMonoid P] [AddCommMonoid Q] [Module R M] [Module R P] [Module R Q]
    [SMulCommClass R R P] (f : M →ₗ[R] M →ₗ[R] P) (g g' : Q →ₗ[R] M) :
    BilinMap.baseChange A (f.compl₁₂ g g') =
      (LinearMap.BilinMap.baseChange A f).compl₁₂ (g.baseChange A) (g'.baseChange A) := by
  ext; simp

def BilinForm.baseChange_compl₁₂ {R A M Q : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    [AddCommMonoid M] [AddCommMonoid Q] [Module R M] [Module R Q]
    (f : LinearMap.BilinForm R M) (g g' : Q →ₗ[R] M) :
    BilinForm.baseChange A (f.compl₁₂ g g') =
      (LinearMap.BilinForm.baseChange A f).compl₁₂ (g.baseChange A) (g'.baseChange A) := by
  ext; simp

@[simp]
def BilinForm.baseChange_add {R A M : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    [AddCommMonoid M] [Module R M] (f g : LinearMap.BilinForm R M) :
    BilinForm.baseChange A (f + g) = BilinForm.baseChange A f + BilinForm.baseChange A g := by
  ext; simp [add_smul]

end LinearMap

namespace QuadraticForm

abbrev prod {R M₁ M₂ : Type*} [CommSemiring R] [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁]
    [Module R M₂] (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) : QuadraticForm R (M₁ × M₂) :=
  QuadraticMap.prod Q₁ Q₂

abbrev weightedSumSquares {S : Type*} (R : Type*) [CommSemiring R] {ι : Type*}
    [Fintype ι] [Monoid S] [DistribMulAction S R] [SMulCommClass S R R] (w : ι → S) :
    QuadraticForm R (ι → R) :=
  QuadraticMap.weightedSumSquares R w

lemma weightedSumSquares_toMatrix {S : Type*} (R : Type*) [CommRing R] [Invertible (2 : R)]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid S] [DistribMulAction S R]
    [SMulCommClass S R R] (w : ι → S) :
    toMatrix (Pi.basisFun R ι) (weightedSumSquares R w) = Matrix.diagonal fun i ↦ w i • 1 := by
  ext i j
  simp only [toMatrix, LinearMap.toMatrix₂_apply, Pi.basisFun_apply, QuadraticMap.associated_apply,
    QuadraticMap.weightedSumSquares_apply, Pi.add_apply, Module.End.smul_def,
    QuadraticMap.half_moduleEnd_apply_eq_half_smul, smul_eq_mul, Matrix.diagonal_apply]
  split_ifs with hij
  · simp only [hij, Pi.single_apply, mul_ite, mul_one, mul_zero, smul_ite, smul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [Finset.sum_eq_single j (fun _ _ hkj ↦ by simp [hkj]) (by aesop)]
    · simp only [↓reduceIte]
      ring_nf
      have h4 : (4 : R) = 2 * 2 := by ring
      rw [← mul_smul_one, mul_right_comm _ _ 2]
      simp only [h4, ← mul_assoc, invOf_mul_self', one_mul]
      ring
  · simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, smul_ite, smul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [Finset.sum_eq_add i j hij (fun _ _ hkj ↦ by simp [hkj]) (by aesop) (by aesop)]
    simp [(Ne.symm hij), hij]

lemma weightedSumSquares_discr {S : Type*} (R : Type*) [CommRing R] [Invertible (2 : R)] {ι : Type*}
    [Fintype ι] [DecidableEq ι] [CommMonoid S] [DistribMulAction S R] [SMulCommClass S R R]
    (w : ι → S) : discr (Pi.basisFun R ι) (weightedSumSquares R w) = ∏ (i : ι), w i • 1 := by
  rw [← Matrix.det_diagonal, discr, weightedSumSquares_toMatrix]

lemma baseChange_toMatrix {R n M₁ : Type*} [Fintype n] [DecidableEq n] (A : Type*) [CommRing R]
    [AddCommGroup M₁] [Module R M₁] [CommRing A] [Algebra R A] [Invertible (2 : R)]
    [Invertible (2 : A)] (b : Module.Basis n R M₁) {Q : QuadraticForm R M₁} :
    (Q.baseChange A).toMatrix (b.baseChange A) = (Q.toMatrix b).map (algebraMap R A) := by
  ext i j
  have h2 : algebraMap R A 2 = 2 := by
    have : (2 : R) = 1 + 1 := by ring
    simp [this]; ring
  have : Invertible ((algebraMap R A) 2) := by rw [h2]; infer_instance
  have h2' : (algebraMap R A) ⅟2 = ⅟2 := by simp [map_invOf, h2]
  have h (j) : Q (b j) • ⅟(2 : A) = ⅟2 * (Q (b j) • 1) := by simp
  simp only [toMatrix, LinearMap.toMatrix₂_apply, Module.Basis.baseChange_apply,
    QuadraticMap.associated_apply, baseChange_tmul, mul_one, Module.End.smul_def, map_sub,
    QuadraticMap.half_moduleEnd_apply_eq_half_smul, smul_eq_mul, LinearMap.map_smul_of_tower,
    Matrix.map_apply, map_mul, h2']
  congr
  · have h0 (x y) :  QuadraticMap.polar (⇑(algebraMap R A)) x y = 0 := by simp [QuadraticMap.polar]
    simp only [QuadraticMap.map_add, baseChange_tmul, mul_one,
      Algebra.algebraMap_eq_smul_one (Q (b i)), Algebra.algebraMap_eq_smul_one (Q (b j))]
    simp only [add_assoc, add_right_inj]
    rw [← QuadraticMap.polarBilin_apply_apply]
    simp [polarBilin_baseChange,  Algebra.algebraMap_eq_smul_one, h0]
  · rw [h i, Algebra.algebraMap_eq_smul_one (Q (b i))]
  · rw [h j, Algebra.algebraMap_eq_smul_one (Q (b j))]

lemma baseChange_discr {R n M₁ : Type*} [Fintype n] [DecidableEq n] (A : Type*) [CommRing R]
    [AddCommGroup M₁] [Module R M₁] [CommRing A] [Algebra R A] [Invertible (2 : R)]
    [Invertible (2 : A)] (b : Module.Basis n R M₁) {Q : QuadraticForm R M₁} :
    (Q.baseChange A).discr (b.baseChange A) = algebraMap R A (Q.discr b) := by
  simp [discr, baseChange_toMatrix, Matrix.det_apply]

end QuadraticForm

namespace QuadraticMap

open QuadraticForm

-- TODO: move to Basic file.
lemma Equivalent.baseChange {R M₁ M₂ : Type*} (A : Type*) [CommRing R] [AddCommGroup M₁]
    [AddCommGroup M₂] [Module R M₁] [Module R M₂] [CommRing A] [Algebra R A] [Invertible (2 : R)]
    [Invertible (2 : A)] {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    (h : Q₁.Equivalent Q₂) : (Q₁.baseChange A).Equivalent (Q₂.baseChange A) := by
  obtain ⟨f⟩ := h
  use LinearEquiv.baseChange R A M₁ M₂ f
  intro a
  induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul a m => simp
    | add x y hx hy =>
      have : (Q₂.baseChange A).polarBilin
          (((f.toLinearEquiv.baseChange R A M₁ M₂)).toLinearMap x)
          ((((f.toLinearEquiv.baseChange R A M₁ M₂)).toLinearMap y)) =
          (Q₁.baseChange A).polarBilin x y := by
        simp only [polarBilin_baseChange, LinearEquiv.coe_baseChange, ← LinearMap.compl₁₂_apply,
          ← LinearMap.BilinForm.baseChange_compl₁₂]
        congr
        ext m n
        simp [polar, -map_add, ← map_add f]
      simpa [polar, ← hx, ← hy] using this

-- TODO: change in Mathlib
theorem polarBilin_injective' {R M N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [Invertible (2 : R)] :
    Function.Injective (polarBilin : QuadraticMap R M N → _) :=
  polarBilin_injective (isUnit_of_invertible 2)

theorem polarBilin_ext_iff {R M N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [Invertible (2 : R)]
    {Q₁ Q₂ : QuadraticMap R M N} :
    Q₁ = Q₂ ↔ Q₁.polarBilin = Q₂.polarBilin :=
  ⟨fun h ↦ by rw [h], fun h ↦ by apply QuadraticMap.polarBilin_injective' h⟩

end QuadraticMap

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

open _root_.QuadraticMap

theorem weightedSumSquares_equiv_prod (hr : Module.finrank ℚ V = 4)
   (w : Fin (Module.finrank ℚ V) → ℚˣ) :
    (weightedSumSquares ℚ w).Equivalent
      ((weightedSumSquares ℚ ![w ⟨0, by omega⟩, w ⟨1, by omega⟩]).prod
       (-weightedSumSquares ℚ ![-w ⟨2, by omega⟩, -w ⟨3, by omega⟩])) :=
  ⟨finFinrankLinearEquivProd hr, by
  intro f
  simp only [finFinrankLinearEquivProd, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta,
    Fin.isValue, Fin.mk_one, finCongr_apply, AddHom.toFun_eq_coe, AddHom.coe_mk,
    QuadraticMap.prod_apply, QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, QuadraticMap.neg_apply,
    Units.neg_smul, neg_add_rev, neg_neg]
  calc _
  _ =  ∑ (x : Fin 4), w (finCongr hr.symm x) *
  (f (finCongr hr.symm x) * f (finCongr hr.symm x)) := by
      simp only [finCongr_apply, Fin.sum_univ_four, add_assoc, add_comm ((w ⟨3,_⟩) • _)]
      congr
  _ =  ∑ x, w x * (f x * f x) := Fintype.sum_equiv (finCongr (Eq.symm hr))
      (fun x ↦ w ((finCongr (Eq.symm hr)) x) *
      (f ((finCongr (Eq.symm hr)) x) * f ((finCongr (Eq.symm hr)) x)))
      (fun x ↦ w x * (f x * f x)) (congrFun rfl)⟩

open TensorProduct

lemma _root_.TensorProduct.prodRight_fst {R A M₁ M₂ : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Invertible (2 : R)] [Invertible (2 : A)] [AddCommGroup M₁] [AddCommGroup M₂] [Module R M₁]
    [Module R M₂] (x : A ⊗[R] (M₁ × M₂)) :
    ((prodRight R A A M₁ M₂) x).1 = (LinearMap.baseChange A (LinearMap.fst R M₁ M₂)) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul => simp
  | add x y hx hy => simp [hx, hy]

lemma _root_.TensorProduct.prodRight_snd {R A M₁ M₂ : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Invertible (2 : R)] [Invertible (2 : A)] [AddCommGroup M₁] [AddCommGroup M₂] [Module R M₁]
    [Module R M₂] (x : A ⊗[R] (M₁ × M₂)) :
    ((prodRight R A A M₁ M₂) x).2 = (LinearMap.baseChange A (LinearMap.snd R M₁ M₂)) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul => simp
  | add x y hx hy => simp [hx, hy]

set_option backward.isDefEq.respectTransparency false in
open TensorProduct in
lemma prod_baseChange {R A M₁ M₂ : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Invertible (2 : R)] [Invertible (2 : A)] [AddCommGroup M₁] [AddCommGroup M₂] [Module R M₁]
    [Module R M₂] (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) :
    ((Q₁.prod Q₂).baseChange A).Equivalent ((Q₁.baseChange A).prod (Q₂.baseChange A)) := by
  constructor
  refine ⟨TensorProduct.prodRight R A A M₁ M₂, ?_⟩
  intro m
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul => simp [prodRight_tmul, add_smul]
  | add x y hx hy =>
    have : polar (Q₁.baseChange A) ((prodRight R A A M₁ M₂) x).1 ((prodRight R A A M₁ M₂) y).1 +
        polar (Q₂.baseChange A) ((prodRight R A A M₁ M₂) x).2 ((prodRight R A A M₁ M₂) y).2 =
        polar ((Q₁.prod Q₂).baseChange A) x y := by
      simp [← polarBilin_apply_apply, polarBilin_baseChange, LinearMap.BilinForm.baseChange_compl₁₂,
         prodRight_fst, prodRight_snd]
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
      QuadraticMap.prod_apply, map_add] at hx hy ⊢
    simp only [Prod.fst_add, Prod.snd_add, QuadraticMap.map_add (Q₁.baseChange A),
      QuadraticMap.map_add (Q₂.baseChange A), QuadraticMap.map_add ((Q₁.prod Q₂).baseChange A),
      ← hx, ← hy, ← this]
    ring

lemma prod_neg_baseChange {R A M₁ M₂ : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Invertible (2 : R)] [Invertible (2 : A)] [AddCommGroup M₁] [AddCommGroup M₂] [Module R M₁]
    [Module R M₂] (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) :
    ((Q₁.prod (-Q₂)).baseChange A).Equivalent ((Q₁.baseChange A).prod (- Q₂.baseChange A)) := by
  apply (prod_baseChange Q₁ (-Q₂) (A := A)).trans
  convert Equivalent.refl ((Q₁.baseChange A).prod (-Q₂.baseChange A))
  ext; simp

lemma isotropic_of_rank_four (hr : Module.finrank ℚ V = 4) (hQ : Q.Nondegenerate)
    (hQ' : Q.EverywhereLocallyIsotropic) :
    Q.Isotropic := by
  have : FiniteDimensional ℚ V :=
    Module.finite_of_finrank_pos (Nat.lt_of_sub_eq_sub_one hr)
  -- Q is equivalent to a₁ X₁^2 + a₂ X₂ ^ 2 + a₃ X₃ ^3 + a₄ X₄^2, for some a_i : ℚˣ
  obtain ⟨w, hw⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate'
    (QuadraticMap.nondegenerate_associated_iff.mpr hQ).1
  -- Q1 := a₁ X₁^2 + a₂ X₂ ^ 2, Q2 := - a₃ X₃ ^3 - a₄ X₄^2
  let Q1 : QuadraticForm ℚ (Fin 2 → ℚ) := weightedSumSquares ℚ ![w ⟨0, by omega⟩, w ⟨1, by omega⟩]
  let Q2 : QuadraticForm ℚ (Fin 2 → ℚ) := weightedSumSquares ℚ ![-w ⟨2, by omega⟩, -w ⟨3, by omega⟩]
  have heq : (weightedSumSquares ℚ w).Equivalent (Q1.prod (-Q2)) :=
    weightedSumSquares_equiv_prod hr w
  -- Since Q is equivalent to (QuadraticMap.weightedSumSquares ℚ w) and to (Q1.prod (-Q2)),
  -- it suffices to prove that (Q1.prod (-Q2)) is isotropic
  apply (hw.trans (weightedSumSquares_equiv_prod hr w)).symm.isotropic
  rw [prod_isotropic_iff (by sorry) (by sorry)]
  --
  have hp (p : ℕ) [Fact (Nat.Prime p)] : ∃ xₚ : ℚ_[p]ˣ, (Q1.baseChange ℚ_[p]).represents xₚ.1 ∧
      (Q2.baseChange ℚ_[p]).represents xₚ.1 := by
    rw [← prod_isotropic_iff (by sorry) (by sorry)]
    exact (prod_neg_baseChange _ _).isotropic (((hw.trans heq).baseChange _).isotropic (hQ'.1 p))
  obtain ⟨xr, hxr⟩ :
      ∃ x : ℝˣ, (Q1.baseChange ℝ).represents x.1 ∧ (Q2.baseChange ℝ).represents x.1 := by
    rw [← prod_isotropic_iff (by sorry) (by sorry)]
    exact (prod_neg_baseChange _ _).isotropic (((hw.trans heq).baseChange ℝ).isotropic hQ'.2)
  have hp' (p : ℕ) [Fact (Nat.Prime p)] :
      hilbertSym (hp p).choose.1 (-(w ⟨0, by omega⟩) * (w ⟨1, by omega⟩)) =
        hilbertSym ((w ⟨0, by omega⟩).1 : ℚ_[p]) (w ⟨1, by omega⟩) ∧
          hilbertSym (hp p).choose.1 (-(w ⟨2, by omega⟩) * (w ⟨3, by omega⟩)) =
          hilbertSym ((w ⟨3, by omega⟩).1 : ℚ_[p]) (w ⟨3, by omega⟩) := by
    have : (Q1.baseChange ℚ_[p]).represents (hp p).choose  := (hp p).choose_spec.1
    rw [QuadraticForm.represents_iff_of_rank_two _
      ((Pi.basisFun ℚ (Fin 2)).baseChange ℚ_[p])] at this
    · rw [HasseMinkoskiInvariant.eq_of_equivalent_weightedSumSquares
        (w := ![Units.map (algebraMap ℚ ℚ_[p]) (w ⟨0, by omega⟩),
        Units.map (algebraMap ℚ ℚ_[p]) (w ⟨1, by omega⟩)])] at this
      · rw [HasseMinkoskiInvariant.weightedSumSquares] at this
        refine ⟨?_, ?_⟩
        · convert this using 1
          · congr
            simp only [neg_mul, baseChange_discr, weightedSumSquares_discr, Fin.prod_univ_two,
              Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
              mul_smul_one, eq_ratCast, neg_inj, Q1]
            simp [Units.smul_def, mul_comm]
          · have h2 : Module.finrank ℚ_[p] (ℚ_[p] ⊗[ℚ] (Fin 2 → ℚ)) = 2 := sorry
            rw [Finset.prod_eq_single (⟨0, by omega⟩, ⟨1, by omega⟩) _ (fun h ↦ by simp at h)]
            · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
              Matrix.cons_val_zero, Units.coe_map, MonoidHom.coe_coe, eq_ratCast, Fin.mk_one,
              Matrix.cons_val_one, Matrix.cons_val_fin_one]
            · -- Contradiction since (0, 1) is the only possible index
              intro h hmem hne
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
              sorry
        sorry
      sorry
    · sorry
  have hreal' : hilbertSym xr.1 (-(w ⟨0, by omega⟩) * (w ⟨1, by omega⟩)) =
      hilbertSym ((w ⟨0, by omega⟩).1 : ℝ) (w ⟨1, by omega⟩) ∧
        hilbertSym xr.1 (-(w ⟨2, by omega⟩) * (w ⟨3, by omega⟩)) =
        hilbertSym ((w ⟨3, by omega⟩).1 : ℝ) (w ⟨3, by omega⟩) :=
    sorry
  have (p : Nat.Primes) : Fact (Nat.Prime p) := hilbertSym.fact_prime p
  obtain ⟨x, hx⟩ : ∃ (x : ℚˣ), (∀ (p : Nat.Primes),
      hilbertSym.atP x.1 (-(w ⟨0, by omega⟩) * (w ⟨1, by omega⟩)) p =
      hilbertSym.atP (w ⟨0, by omega⟩).1 (w ⟨1, by omega⟩) p) ∧
        hilbertSym.atInfty x.1 (-(w ⟨0, by omega⟩) * (w ⟨1, by omega⟩)) =
        hilbertSym.atInfty (w ⟨0, by omega⟩).1 (w ⟨1, by omega⟩) := by
    have hprod :
        (∏ᶠ (p : Nat.Primes), hilbertSym (hp p).choose.1 (-(w ⟨0, by omega⟩) * (w ⟨1, by omega⟩))) *
          hilbertSym xr.1 (-(w ⟨0, by omega⟩) * (w ⟨1, by omega⟩)) = 1 := by
      simp_rw [(hp' _).1, hreal'.1, hilbertSym.prod_eq_one]
    have hprod' :
      (∏ᶠ (p : Nat.Primes), hilbertSym (hp p).choose.1 (-(w ⟨2, by omega⟩) * (w ⟨3, by omega⟩))) *
        hilbertSym xr.1 (-(w ⟨2, by omega⟩) * (w ⟨3, by omega⟩)) = 1 := by
      simp_rw [(hp' _).2, hreal'.2, hilbertSym.prod_eq_one]
    have := hilbertSym.exists_rat_with_prescribed_hilbertSym
      (ep := fun p ↦ hilbertSym.atP (w ⟨0, by omega⟩).1 (w ⟨1, by omega⟩) p)
      (ereal := hilbertSym.atInfty (w ⟨0, by omega⟩).1 (w ⟨1, by omega⟩))
      (-(w ⟨0, by omega⟩) * (w ⟨1, by omega⟩)) (by sorry) (by sorry)
    simp only [Units.val_neg, Units.val_mul, Rat.cast_neg, Rat.cast_mul] at this
    rw [this]
    exact ⟨hilbertSym.almost_all_one _ _, hilbertSym.prod_eq_one _ _,
      fun p ↦ ⟨(hp p).choose, (hp' p).1⟩ , ⟨xr, hreal'.1⟩ ⟩
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
