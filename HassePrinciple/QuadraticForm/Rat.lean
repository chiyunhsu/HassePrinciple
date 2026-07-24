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

/-
Is this worth adding into Mathlib at Finsupp/Basic.lean?
There are already Finsupp.prod_pow and Finsupp.prod_mul which are similar.
-/
theorem prod_pow' {α M N : Type*} [Zero M] [CommMonoid N] (f : α →₀ M) (g : α → M → N) (n : ℕ) :
    (f.prod g) ^ n = (f.prod fun a b => (g a b) ^ n) := by simp [Finsupp.prod, Finset.prod_pow]

/-
The numerator and denominator of a rational number with even p-adic valuation
also have even p-adic valuation
-/
lemma EvenVal {a : ℚ} {p : ℕ} [Fact (Nat.Prime p)] (h : Even (padicValRat p a)) :
    Even (padicValInt p a.num) ∧ Even (padicValNat p a.den) := by
  have diff_even := padicValRat_def p a ▸ h
  have padicVal_eq_zero : padicValInt p a.num = 0 ∨ padicValNat p a.den = 0 := by
    by_contra h
    push Not at h
    apply not_not.mpr a.reduced
    have h1 : p ∣ a.num.natAbs := not_not.mp (mt padicValNat.eq_zero_of_not_dvd h.1)
    have h2 : p ∣ a.den := not_not.mp (mt padicValNat.eq_zero_of_not_dvd h.2)
    exact (Nat.not_coprime_of_dvd_of_dvd (Nat.Prime.one_lt (Fact.out)) h1 h2)
  rcases padicVal_eq_zero with (h0 | h0) <;>
  simpa [h0] using diff_even

-- A nonzero natural number with even p-adic valuation for all p is a square
lemma factorization_sqrt_Nat {n : ℕ} (h0 : n ≠ 0)
    (h : ∀ (p : ℕ) [Fact (Nat.Prime p)], Even (n.factorization p)) : IsSquare n := by
  refine ⟨n.factorization.prod fun a b ↦ a ^ (b / 2), ?_⟩
  rw [← pow_two, prod_pow']
  nth_rw 1 [← Nat.prod_factorization_pow_eq_self h0]
  refine Finsupp.prod_congr fun p hp ↦ ?_
  letI : Fact (Nat.Prime p) := ⟨by simp_all⟩
  rw [← pow_mul, Nat.div_two_mul_two_of_even (h p)]

-- A positive integer with even p-adic valuation for all p is a square
lemma factorization_sqrt_Int {n : ℤ} (h0 : n > 0)
    (h : ∀ (p : ℕ) [Fact (Nat.Prime p)], Even (n.natAbs.factorization p)) : IsSquare n := by
  obtain ⟨r, hr⟩ := factorization_sqrt_Nat (by simp only [ne_eq, Int.natAbs_eq_zero]; linarith) h
  exact ⟨r, (by rw [← Int.natAbs_of_nonneg (le_of_lt h0), hr]; norm_num)⟩

-- A positive rational number with even p-adic valuation for all p is a square
lemma factorization_sqrt_Rat {a : ℚ} (hR : a > 0)
    (hf : ∀ (p : ℕ) [Fact (Nat.Prime p)], Even (padicValRat p a)) : IsSquare a :=
  Rat.isSquare_iff.mpr
  ⟨factorization_sqrt_Int (Rat.num_pos.mpr hR)
    (fun p inst ↦
    by simpa [Nat.factorization_def _ (inst.out), padicValInt] using (EvenVal (hf p)).1),
  factorization_sqrt_Nat a.den_ne_zero
    (fun p inst ↦ by simpa [Nat.factorization_def _ (inst.out)] using (EvenVal (hf p)).2)⟩

/-
Auxiliary lemma deducing from a representation of 0 that the coefficient ratio is a square.
This is used twice, in ℝ and in ℚ_[p], so we make it a lemma in a general setting.
-/
lemma aux_of_represents_zero {K : Type*} [Field K] [CharZero K] {w : Fin 2 → ℚ} {x : Fin 2 → K}
    (hw0 : w 0 ≠ 0) (hx1 : x 1 ≠ 0) (h : ↑(w 0) * x 0 ^ 2 + ↑(w 1) * x 1 ^ 2 = 0) :
    ↑(- (w 0)⁻¹ * (w 1)) = ((x 1)⁻¹ * x 0) ^ 2 := by
  rw [Rat.cast_mul, Rat.cast_neg, Rat.cast_inv]
  field_simp [hw0, hx1]
  exact neg_eq_of_add_eq_zero_left h

/-
Auxiliary lemma that the representative of 0 of a nondegenerate quadratic form is nonzero
in both components.
This is used twice, in ℝ and in ℚ_[p], so we make it a lemma in a general setting.
-/
lemma comp_ne_zero_of_nondegenerate {K : Type*} [Field K] [CharZero K] {w : Fin 2 → ℚˣ}
    {x : Fin 2 → K} (h : w 0 * x 0 ^ 2 + w 1 * x 1 ^ 2 = 0 ∧ x ≠ 0) : x 0 ≠ 0 ∧ x 1 ≠ 0 := by
  obtain ⟨h, hx⟩ := h
  by_contra h'
  push +distrib Not at h'
  apply hx
  rcases h' with (hxi | hxi) <;>
  funext i <;>
  fin_cases i <;>
  simp [hxi] at h <;>
  assumption

lemma isotropic_of_rank_two [FiniteDimensional ℚ V] (hr : finrank ℚ V = 2) (hQ : Q.Nondegenerate)
    (hQ' : Q.EverywhereLocallyIsotropic) : Q.Isotropic := by
  obtain ⟨hQ'f, hQ'R⟩ := hQ'
  -- Change assumption and goal from isotropic to representing 0
  simp only [← represents_zero_iff_isotropic] at *
  -- Q is equivalent to Q (w)
  obtain ⟨w, hw⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate hr
    (QuadraticMap.nondegenerate_associated_iff.mpr hQ).1
  change Equivalent Q (QuadraticMap.weightedSumSquares ℚ (fun i ↦ (w i : ℚ))) at hw
  -- Q_v is equivalent to Q(w)_v
  have heqR : (Q.baseChange ℝ).Equivalent (QuadraticMap.weightedSumSquares ℝ (fun i ↦ (w i : ℚ))) :=
    (Equivalent.baseChange ℝ hw).trans
    (QuadraticForm.baseChange_weightedSumSquares ℚ ℝ fun i ↦ (w i : ℚ))
  have heqf : ∀ (p : ℕ) [Fact (Nat.Prime p)],
      (Q.baseChange ℚ_[p]).Equivalent (QuadraticMap.weightedSumSquares ℚ_[p] (fun i ↦ (w i : ℚ))) :=
    fun p _ ↦ (Equivalent.baseChange ℚ_[p] hw).trans
    (QuadraticForm.baseChange_weightedSumSquares ℚ ℚ_[p] fun i ↦ (w i : ℚ))
  -- Change assumption to Q (w) represents 0 everywhere
  rw [Equivalent.represents_iff hw]
  -- Change goal to Q (w) represents 0
  rw [Equivalent.represents_iff heqR] at hQ'R
  have hQ'fw : ∀ (p : ℕ) [Fact (Nat.Prime p)],
      (weightedSumSquares ℚ_[p] (fun i ↦ (w i : ℚ))).represents 0 :=
    fun p _ ↦ (Equivalent.represents_iff (heqf p) 0).mp (hQ'f p)
  -- Simplify weightedSumSquares expressions
  simp only [represents, weightedSumSquares_apply, Fin.sum_univ_two, ← pow_two,
    smul_eq_mul, Rat.smul_def] at hQ'R hQ'fw ⊢
  -- Represents 0 over ℝ implies that - (w 0)⁻¹ * w 1 is positive
  have hR' : 0 < - ((w 0 : ℚ)⁻¹) * w 1 := by
    obtain ⟨x, hx⟩ := hQ'R
    refine lt_of_le_of_ne ?_ (by simp)
    rw [← Rat.cast_nonneg (K := ℝ), ← Real.isSquare_iff]
    use (x 1)⁻¹ * x 0
    rw [← pow_two]
    exact aux_of_represents_zero (w := fun i ↦ (w i : ℚ)) (by simp)
      (comp_ne_zero_of_nondegenerate hx).2 hx.1
  -- Represents 0 over ℚ_[p] implies that the p-adic valuation of - (w 0)⁻¹ * w 1 is even
  have hf : ∀ (p : ℕ) [Fact (Nat.Prime p)], Even (padicValRat p (- (w 0 : ℚ)⁻¹ * w 1)) := by
    intro p inst
    obtain ⟨x, hx⟩ := hQ'fw p
    rw [← Padic.valuation_ratCast, aux_of_represents_zero (w := fun i ↦ (w i : ℚ)) (by simp)
      (comp_ne_zero_of_nondegenerate hx).2 hx.1]
    simp
  -- A positive rational number with even p-adic valuation for all p is a square
  obtain ⟨x, hx⟩ : ∃ (x : ℚ), - (w 0 : ℚ)⁻¹ * w 1 = x * x := factorization_sqrt_Rat hR' hf
  exact ⟨fun | 0 => x | 1 => 1, ⟨by simp [pow_two, ← hx], fun h ↦ by simpa using congrFun h 1⟩⟩

end EverywhereLocallyIsotropic

end QuadraticForm
