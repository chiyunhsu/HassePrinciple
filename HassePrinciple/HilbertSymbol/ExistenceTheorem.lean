/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

public import HassePrinciple.HilbertSymbol.Basic
public import HassePrinciple.NumberTheory.ApproximationTheorem
public import HassePrinciple.Padics.Lemmas
public import HassePrinciple.Padics.Squares
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
/-!
# Existence theorem
-/
@[expose] public section

namespace hilbertSym

open Filter Finset Nat Units

section Integer

variable {I : Type*} {a : I → ℤ} (ha : ∀ i, a i ≠ 0)
  {ep : I → Primes → ℤ} (hep : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
  {ereal : I → ℤ} (hereal : ∀ i : I, ereal i = 1 ∨ ereal i = -1)
  -- h1, h2, h3 are assumed in the hard direction of the existence theorem.
  (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1)
  (h2 : ∀ i : I, (∏ᶠ (p : Primes), ep i p) * ereal i = 1)
  (h3 : ((∀ (p : Primes), ∃ xp : ℚ_[p], ∀ i : I, hilbertSym xp (a i) = ep i p)) ∧
    ∃ xr : ℝ, ∀ i : I, hilbertSym xr (a i) = ereal i)

include ha in
/-- The necessary conditions in the Existence Theorem are indeed necessary. -/
private lemma necessary_cond (x : ℚˣ)
    (h : ∀ i : I, (∀ p : Primes, hilbertSym (x : ℚ_[p]) (a i) = ep i p) ∧
      hilbertSym (x : ℝ) (a i) = ereal i) :
    (∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1) ∧
    (∀ i : I, (∏ᶠ p : Primes, ep i p) * ereal i = 1) ∧
    (∀ p : Primes, ∃ xp : ℚ_[p], ∀ i : I, hilbertSym xp (a i) = ep i p) ∧
    ∃ xr : ℝ, ∀ i : I, hilbertSym xr (a i) = ereal i :=
  ⟨fun i ↦ by
    simp only [← h i, eventually_cofinite]; exact almost_all_one x (mk0 (a i) (by simp [ha])),
    fun i ↦ by simp only [← h i]; exact prod_eq_one x (mk0 (a i) (by simp [ha])),
    fun p ↦ ⟨x, by simp [h]⟩, x, by simp [h]⟩

include hep in
/-- From ep i p = 1 or -1, we deduce that ep i p = -1 iff not ep i p = 1. -/
private lemma ep_eq_neg_one_iff_not_one {i : I} {p : Primes} :
    ep i p = -1 ↔ ¬ep i p = 1 :=
  ⟨fun h ↦ by simp [h], fun h ↦ (hep i p).resolve_left h⟩

include ha hep h1 h2 in
/-- Using the product formula for the Hilbert symbol and for ep i, if we show that
hilbertSym x (a i) = ep i p for all but one p, we are done. -/
lemma all_but_one_places_suffice (q : Primes) (x : ℚˣ)
    (h4 : ∀ i : I, (∀ p : Primes, p ≠ q → hilbertSym (x : ℚ_[p]) (a i) = ep i p) ∧
      hilbertSym (x : ℝ) (a i) = ereal i) :
    ∀ i : I, (∀ p : Primes, hilbertSym (x : ℚ_[p]) (a i) = ep i p) ∧
      hilbertSym (x : ℝ) (a i) = ereal i := by
  let afun : I → ℚˣ := fun i ↦ mk0 (a i) (by simp [ha])
  refine fun i ↦ ⟨fun p ↦ ?_, by simp [h4]⟩
  --The nontrivial case is when p=q.
  by_cases hpq : p = q
  · have hprod' : ∏ᶠ (p' : Primes) (_ : p' ≠ q), hilbertSym (x : ℚ_[p']) (a i) =
        ∏ᶠ (p' : Primes) (_ : p' ≠  q), ep i p' := by
      congr! with p' h
      rw [(h4 i).1 p' h]
    have hprod : ∏ᶠ (p : Primes), hilbertSym (x : ℚ_[p]) (a i) = ∏ᶠ (p : Primes), ep i p := by
      rw [← mul_left_inj' (by grind : ereal i ≠ 0)]
      nth_rw 1 [← (h4 i).2, h2 i]
      exact prod_eq_one x (afun i)
    rw [← mul_finprod_cond_ne q (_),
      ← mul_finprod_cond_ne q (h1 i), hprod', mul_eq_mul_right_iff, ← hpq] at hprod
    · apply hprod.resolve_right
      rw [finprod_cond_ne _ _ (h1 i), ← ne_eq, prod_ne_zero_iff]
      grind
    · exact almost_all_one x (afun i)
  · exact (h4 i).1 p hpq

variable (a) in
/-- Define S to be the (finite!) set of primes that divide either the numerator or the denominator
of some (a i). N.B. In Serre, S contains also ∞. -/
private noncomputable def S [Fintype I] : Finset Primes :=
  (univ.biUnion (fun i ↦ (a i).natAbs.primeFactors) ∪ {2}).preimage Subtype.val
    Subtype.val_injective.injOn

include hep h1 in
private lemma Tfin [Finite I] :
    (⋃ i : I, {p : Primes | ep i p = -1}).Finite := by
  refine (Set.finite_iUnion fun i ↦ ?_)
  simp only [eventually_cofinite, ← ep_eq_neg_one_iff_not_one hep, Int.reduceNeg] at h1
  exact h1 i

/-- Define T to be the (finite!) set of primes such that at least one of the e_{i,v} is -1. -/
private noncomputable def T [Finite I] : Finset Primes := (Tfin hep h1).toFinset

private lemma ep_eq_one_of_not_mem_T [Finite I] {p : Primes} (hpT : p ∉ T hep h1) (i : I) :
    ep i p = 1 := by
  simp only [T, Int.reduceNeg, ep_eq_neg_one_iff_not_one hep, Set.Finite.mem_toFinset,
    Set.mem_iUnion, Set.mem_setOf_eq, not_exists, Decidable.not_not] at hpT
  exact hpT i

private lemma ep_eq_one_iff_not_mem_T [Finite I] (p : Primes) :
    p ∉ T hep h1 ↔ ∀ i : I, ep i p = 1 :=
  ⟨fun h i ↦ ep_eq_one_of_not_mem_T hep h1 h i, fun h ↦ by simp [T]; grind⟩

private lemma ep_eq_one_of_mem_S_disjoint [Fintype I] {p : Primes} (hpS : p ∈ S a)
    (disjoint_ST : Disjoint (S a) (T hep h1)) (i : I) : ep i p = 1 :=
  ep_eq_one_of_not_mem_T hep h1 (disjoint_left.mp disjoint_ST (by simp [hpS])) i

include ha in
private lemma is_unit_ai_of_p_notMem_S [Fintype I] {p : Primes} (hpS : p ∉ S a) (i : I) :
    padicValInt p (a i) = 0 := by
  simp only [S, union_singleton, mem_preimage, mem_insert, mem_biUnion, mem_univ, mem_primeFactors,
    p.2, ne_eq, Int.natAbs_eq_zero, true_and, not_or, not_exists, not_and, Decidable.not_not, ha,
    imp_false, ← Int.natCast_dvd] at hpS
  simp [ha, hpS]

--is there a simp or at least simple mathlib lemmma for this? I couldn't shorten further.
--Edit: I did shorten further, but now I don't know where to put this.
private lemma Rat.zpow_odd_eq_self (c : ℤ) (hodd : Odd c) :
    ∀ b : ℚ, (b = 1 ∨ b = -1) → b ^ c = b := by
  norm_num; rw [Odd.neg_one_zpow hodd]

private noncomputable abbrev A [Fintype I] : ℕ := ∏ t : T hep h1, (t : ℕ)

private lemma A_ne_zero [Fintype I] : A hep h1 ≠ 0 := by simp [prod_ne_zero_iff, A, NeZero.out]

private lemma A_pos [Fintype I] : 0 < A hep h1 := by simp [A, pos_of_neZero]

variable (a) in
private noncomputable abbrev M [Fintype I] := 4 * ∏ s : S a, (s : ℕ)

private lemma M_ne_zero [Fintype I] : M a ≠ 0 :=
  mul_ne_zero (by omega) (by simp [prod_ne_zero_iff, NeZero.out])

/-- The definition of q when S and T are disjoint using Dirichlet. -/
private lemma q_existence [Fintype I] [Nonempty I]
    (disjoint_ST : Disjoint (S a) (T hep h1)) :
    ∃ q : ℕ, Nat.Prime q ∧ q ≡ ∏ t : T hep h1, (t : ℕ) [MOD 4 * ∏ s : S a, (s : ℕ)] := by
  let A := hilbertSym.A hep h1
  let M := hilbertSym.M a
  have coprime_AM : A.Coprime M := by
    rw [coprime_fintype_prod_left_iff]
    refine fun t ↦ Coprime.mul_right ?_ ?_
    · have h2 : (⟨2, prime_two⟩ : Primes) = (2 : ℕ) := rfl
      rw [(by omega : 4 = 2 ^ 2), coprime_pow_right_iff (by omega), coprime_two_right]
      apply Prime.odd_of_ne_two t.1.2
      rw [← h2, ne_eq, Primes.coe_nat_inj, eq_comm]
      exact (disjoint_iff_ne.mp disjoint_ST) ⟨2,prime_two⟩ (by simp [hilbertSym.S]) t t.2
    · rw [coprime_fintype_prod_right_iff]
      intro s
      simp [coprime_primes t.1.2 s.1.2, Primes.coe_nat_inj,
        (disjoint_ST.forall_ne_finset s.2 t.2).symm]
  --We can apply Dirichlet's lemma.
  exact (infinite_setOf_prime_and_modEq M_ne_zero coprime_AM).nonempty

/-- Definition of q. -/
private noncomputable abbrev q [Fintype I] [Nonempty I] (disjoint_ST : Disjoint (S a) (T hep h1)) :
    ℕ := (q_existence hep h1 disjoint_ST).choose

private lemma q_prime [Fintype I] [Nonempty I] (disjoint_ST : Disjoint (S a) (T hep h1)) :
    Nat.Prime (q hep h1 disjoint_ST) := (q_existence hep h1 disjoint_ST).choose_spec.1

private lemma q_cong [Fintype I] [Nonempty I] (disjoint_ST : Disjoint (S a) (T hep h1)) :
    q hep h1 disjoint_ST ≡ ∏ t : T hep h1, (t : ℕ) [MOD 4 * ∏ s : S a, (s : ℕ)] :=
  (q_existence hep h1 disjoint_ST).choose_spec.2

private noncomputable def x [Fintype I] [Nonempty I] (disjoint_ST : Disjoint (S a) (T hep h1)) :=
  mk0 ((A hep h1) * (q hep h1 disjoint_ST) : ℚ) (by
    simp only [ne_eq, _root_.mul_eq_zero, cast_eq_zero, not_or]; refine
      ⟨A_ne_zero hep h1, Nat.Prime.ne_zero (q_prime hep h1 disjoint_ST)⟩)

private lemma x_pos [Fintype I] [Nonempty I] (disjoint_ST : Disjoint (S a) (T hep h1)) :
    0 < (x hep h1 disjoint_ST).val := by
  simp only [x, A, univ_eq_attach, cast_prod, mk0_mul, val_mul, val_mk0]
  refine mul_pos ?_ ?_
  · exact_mod_cast A_pos hep h1
  · exact_mod_cast Nat.Prime.pos (q_prime hep h1 disjoint_ST)

--this one is slower! (I removed some simps)
set_option trace.profiler true in
private lemma x_square [Fintype I] [Nonempty I] (disjoint_ST : Disjoint (S a) (T hep h1))
    (p : Primes) (hpS : p ∈ S a) : ∃ b : ℤ_[p], (A hep h1) * (q hep h1 disjoint_ST) = b ^ 2 := by
  let A := hilbertSym.A hep h1
  let q := hilbertSym.q hep h1 disjoint_ST
  have q_cong := hilbertSym.q_cong hep h1 disjoint_ST
  by_cases hp2 : p = ⟨2, prime_two⟩
  · rw [hp2]
    apply Polynomial.squares_in_Z2 _ A
    have : (q : ZMod 8) = A := by
      apply ModEq.of_dvd at q_cong
      · rw [← ZMod.natCast_eq_natCast_iff] at q_cong
        exact q_cong
      · simp only [(by omega : 8 = 4 * 2)]
        rw [mul_dvd_mul_iff_left (by omega), ← prod_subtype (S a) (by simp) (fun s ↦ (s : ℕ))]
        exact dvd_prod_of_mem Subtype.val (by simp [S, hilbertSym.S] : ⟨2, prime_two⟩ ∈ S a)
    simp [q, A, this, pow_two]
  · apply Polynomial.squares_in_Zp (by rw [← Primes.coe_nat_inj] at hp2; exact hp2) _ A
    have : (q : ZMod p) = A := by
      apply ModEq.of_dvd at q_cong
      · rw [← ZMod.natCast_eq_natCast_iff] at q_cong
        exact q_cong
      · refine Nat.dvd_mul_left_of_dvd ?_ 4
        rw [← prod_subtype (S a) (by simp) (fun s ↦ (s : ℕ))]
        exact dvd_prod_of_mem Subtype.val hpS
    simp only [cast_prod, univ_eq_attach, map_mul, map_prod, map_natCast, this, pow_two, A, q]

--this too! (I removed the simps)
set_option trace.profiler true in
private lemma x_square_of_p_mem_S [Fintype I] [Nonempty I] (disjoint_ST : Disjoint (S a) (T hep h1))
    (p : Primes) (hpS : p ∈ S a) : ∃ b : ℚ_[p], x hep h1 disjoint_ST = b ^ 2 := by
  have ⟨b, hb⟩ := x_square hep h1 disjoint_ST p hpS
  use b
  rw_mod_cast [x, ← hb]
  simp only [cast_mul, cast_prod, univ_eq_attach, mk0_mul, val_mul, val_mk0, Rat.cast_mul,
    Rat.cast_prod, Rat.cast_natCast, PadicInt.coe_mul, PadicInt.coe_natCast, mul_eq_mul_right_iff,
    cast_eq_zero]
  rw [← PadicInt.algebraMap_apply]
  simp only [map_prod, map_natCast, true_or]

private lemma val_x_eq_one_of_p_mem_T [Fintype I] [Nonempty I]
    (disjoint_ST : Disjoint (S a) (T hep h1)) (p : Primes) (pneq : p ≠ q hep h1 disjoint_ST)
    (hpT : p ∈ T hep h1) : padicValRat p (x hep h1 disjoint_ST).val = 1 := by
  let q := hilbertSym.q hep h1 disjoint_ST
  have q_prime := hilbertSym.q_prime hep h1 disjoint_ST
  have : Fact (Nat.Prime q) := ⟨q_prime⟩
  simp only [x, cast_prod, mk0_mul, val_mul, val_mk0]
  rw [padicValRat.mul (by exact_mod_cast A_ne_zero hep h1) (by simp [Nat.Prime.ne_zero q_prime]),
    padicValRat.of_nat]
  simp only [ne_eq, pneq, not_false_eq_true, padicValNat_primes, CharP.cast_eq_zero,
    add_zero]
  have hTp : T hep h1 = (T hep h1 \ {p}) ∪ {p} := by
    rw [union_singleton, insert_sdiff_self_of_mem hpT]
  rw_mod_cast [← prod_subtype (T hep h1) (by simp) (fun t ↦ (t : ℕ)), hTp, prod_union (by simp),
    prod_singleton, padicValNat.mul _ (Nat.Prime.ne_zero p.2), padicValNat_self]
  · rw [Nat.add_eq_right, padicValNat.eq_zero_iff]
    apply Or.inr (Or.inr (Prime.not_dvd_finsetProd (prime_iff.mp p.2) ?_))
    intro t
    simp [mem_singleton, ← ne_eq, ne_comm, prime_dvd_prime_iff_eq p.2 t.2,
      Primes.coe_nat_inj]
  · have := A_ne_zero hep h1
    simp only [implies_true, ← prod_subtype (T hep h1) _ (fun t ↦ (t : ℕ)),
      hilbertSym.A] at this
    rw [hTp, prod_union sdiff_disjoint] at this
    simp only [prod_singleton, ne_eq, mul_eq_zero, not_or] at this
    simp [this]

private lemma val_x_eq_zero_of_p_not_mem_T [Fintype I] [Nonempty I]
    (disjoint_ST : Disjoint (S a) (T hep h1)) (p : Primes) (pneq : p ≠ q hep h1 disjoint_ST)
    (hpT : p ∉ T hep h1) : padicValRat p (x hep h1 disjoint_ST).val = 0 := by
  let q := hilbertSym.q hep h1 disjoint_ST
  have q_prime := hilbertSym.q_prime hep h1 disjoint_ST
  have : Fact (Nat.Prime q) := ⟨q_prime⟩
  simp only [x, cast_prod, mk0_mul, val_mul, val_mk0]
  rw [padicValRat.mul (by exact_mod_cast A_ne_zero hep h1) (by simp [Nat.Prime.ne_zero q_prime]),
    padicValRat.of_nat]
  simp only [ne_eq, pneq, not_false_eq_true, padicValNat_primes, CharP.cast_eq_zero,
    add_zero]
  rw_mod_cast [← prod_subtype (T hep h1) (by simp) (fun t ↦ (t : ℕ))]
  simp only [padicValNat.eq_zero_iff]
  apply Or.inr (Or.inr (Prime.not_dvd_finsetProd (prime_iff.mp p.2) ?_))
  intro t ht
  simp only [prime_dvd_prime_iff_eq p.2 t.2, Primes.coe_nat_inj, ← ne_eq]
  intro hpt
  subst p
  contradiction

--this is slow too! (more simps removed)
set_option trace.profiler true in
include ha h2 h3 in
/-- We first prove the Existence Theorem when S and T are disjoint. -/
private lemma existence_disjoint [Fintype I] [Nonempty I]
    (disjoint_ST : Disjoint (S a) (T hep h1)) (infty_not_mem_T : ∀ i : I, ereal i = 1) :
    (∃ x : ℚˣ, ∀ i : I, (∀ p : Primes, hilbertSym (x : ℚ_[p]) (a i) = ep i p) ∧
      hilbertSym (x : ℝ) (a i) = ereal i) := by
  let q := hilbertSym.q hep h1 disjoint_ST
  have q_prime := hilbertSym.q_prime hep h1 disjoint_ST
  have : Fact (Nat.Prime q) := ⟨q_prime⟩
  let x := x hep h1 disjoint_ST
  use x
  --We apply lemma all_but_one_places_suffice to avoid dealing with q. Then we consider separately
  --the cases of p ∈ S, p ∈ T, p ∉ S ∪ T.
  apply all_but_one_places_suffice ha hep h1 h2 ⟨q, q_prime⟩ x
  refine fun i ↦ ⟨fun p pneq ↦ ?_,
    (by rw [real_eq (by simp) (by simp [ha]), infty_not_mem_T]; simp [x, x_pos hep h1 disjoint_ST])⟩
  have hpq : p.1 ≠ q := by simp only [ne_eq, ← Primes.coe_nat_inj] at pneq; exact pneq
  by_cases hpS : p ∈ S a
  · --case p ∈ S: LHR = 1 because x is a square, RHS = 1 because p ∉ T.
    have ⟨sqrt_x, hx⟩ := x_square_of_p_mem_S hep h1 disjoint_ST p hpS
    simp only [x, hx, comm, ep_eq_one_of_mem_S_disjoint hep h1 hpS disjoint_ST i]
    rw [right_square_eq_one (by simp [ha]) ?_]
    rw [← pow_ne_zero_iff two_ne_zero, ← hx]
    simp only [ne_eq, Rat.cast_eq_zero, ne_zero, not_false_eq_true]
  · --case p ∉ S: (x, a_i)ₚ = (legendreSym p a_i) ^ val_p(x).
    have hp2 : p.1 ≠ 2 := by
      rw [ne_eq, Primes.coe_nat_inj p ⟨2, prime_two⟩]
      exact fun h2 ↦ by simp [h2, S, hilbertSym.S] at hpS
    rw [← Int.cast_inj (α := ℚ), padic_odd_eq hp2 (by simp only [ne_eq, Rat.cast_eq_zero,
      ne_zero, not_false_eq_true]) (by simp only [ne_eq, Int.cast_eq_zero, ha, not_false_eq_true])]
    by_cases hpT : p ∈ T hep h1
      --case p ∈ T: val_p(x) = 1.
    · have val_x : padicValRat p x.val = 1 :=
        val_x_eq_one_of_p_mem_T hep h1 disjoint_ST p hpq hpT
      --we extract xp from h3 and use it.
      obtain ⟨xp, hxp⟩ := h3.1 p
      have val_xp : Odd xp.valuation := by
        simp only [hilbertSym.T, Int.reduceNeg, Set.Finite.mem_toFinset, Set.mem_iUnion,
          Set.mem_setOf_eq, T] at hpT
        obtain ⟨j, hej⟩ := hpT
        specialize hxp j
        rw [← Int.cast_inj (α := ℚ), hej,
          padic_odd_eq hp2 (fun xp0 ↦ by simp [hilbertSym, xp0] at hxp) (by simp [ha])] at hxp
        simp only [Padic.valuation_intCast, is_unit_ai_of_p_notMem_S ha hpS, CharP.cast_eq_zero,
          mul_zero, mul_ite, PadicInt.val_mkUnits, mul_one, ite_self, Int.negOnePow_zero,
          val_one, Int.cast_one, zpow_zero, one_mul, Int.reduceNeg, Int.cast_neg,
          zpow_eq_neg_one_iff₀] at hxp
        exact hxp.2
      simp only [Padic.valuation_ratCast, val_x, Padic.valuation_intCast,
        is_unit_ai_of_p_notMem_S ha hpS, CharP.cast_eq_zero, mul_zero, mul_ite,
        PadicInt.val_mkUnits, mul_one, ite_self, Int.negOnePow_zero, val_one, Int.cast_one,
        zpow_zero, zpow_one, one_mul, ← hxp, Int.cast_inj]
      rw [← Int.cast_inj (α := ℚ), padic_odd_eq hp2 (fun xp0 ↦ ?_) (by simp [ha])]
      · simp only [Padic.valuation_intCast, is_unit_ai_of_p_notMem_S ha hpS, CharP.cast_eq_zero,
          mul_zero, mul_ite, PadicInt.val_mkUnits, mul_one, ite_self, Int.negOnePow_zero,
          val_one, Int.cast_one, zpow_zero, one_mul]
        rw [Rat.zpow_odd_eq_self xp.valuation val_xp]
        exact_mod_cast PadicInt.legendreSym.eq_one_or_neg_one (by simp only [Units.isUnit] :
          IsUnit (Padic.unitPart (mk0 ((a i) : ℚ_[p]) _)).1)
      · simp only [hilbertSym, xp0] at hxp
      --Seriously?
        have : ∀ i : I, 0 = 1 ∨ 0 = -1 := by
          intro i
          specialize hep i p
          grind
        simp at this
    · --case p ∉ T: val_p(x) = 0, so LHR = 1 = RHS.
      have val_x : padicValRat p x.val = 0 :=
        val_x_eq_zero_of_p_not_mem_T hep h1 disjoint_ST p hpq hpT
      simp only [hilbertSym.T, Int.reduceNeg, ep_eq_neg_one_iff_not_one hep, Set.mem_iUnion,
        Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_exists, Decidable.not_not, T] at hpT
      simpa only [Padic.valuation_ratCast, val_x, Padic.valuation_intCast,
        is_unit_ai_of_p_notMem_S ha hpS, CharP.cast_eq_zero, mul_zero, mul_ite,
        PadicInt.val_mkUnits, mul_one, ite_self, Int.negOnePow_zero, val_one, Int.cast_one,
        zpow_zero] using (Int.cast_inj.mpr (hpT i).symm)

--this is bad
set_option trace.profiler true in
include ha hep hereal in
/-- Given a finite set of rational numbers `{a_i}_{i ∈ I}` and numbers `e_{i,v} ∈ {± 1}`,
there exists a rational number `x` such that the Hilbert symbols `(x,a_i)_v` at each place `v`
is equal to `e_{i,v}` if and only if
1) for all `i`, almost all `e_{i,v}` are 1
2) for all `i`, the product of all `e_{i,v}` is 1
3) for each place `v`, there is some `x_v ∈ Q_v` with `(x_v,a_i)_v = e_{i,v}`. -/
theorem exists_rat_with_finite_prescribed_hilbertSym_of_int [Finite I] [Nonempty I] :
    (∃ x : ℚˣ, ∀ i : I, (∀ p : Primes, hilbertSym (x : ℚ_[p]) (a i) = ep i p) ∧
      hilbertSym (x : ℝ) (a i) = ereal i) ↔
      (∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1) ∧
      (∀ i : I, (∏ᶠ (p : Primes), ep i p) * ereal i = 1) ∧
      ((∀ (p : Primes), ∃ xp : ℚ_[p], ∀ i : I, hilbertSym xp (a i) = ep i p)) ∧
      ∃ xr : ℝ, ∀ i : I, hilbertSym xr (a i) = ereal i := by
  have := Fintype.ofFinite I
  refine ⟨fun ⟨x,h⟩ ↦ (by apply necessary_cond <;> assumption), fun ⟨h1, h2, h3⟩ ↦ ?_⟩
  by_cases disjoint_ST : Disjoint (S a) (T hep h1) ∧
      ∀ i : I, ereal i = 1
  · exact existence_disjoint ha hep h1 h2 h3 disjoint_ST.1 disjoint_ST.2
  · let funxp := fun (p : Primes) ↦ (h3.1 p).choose
    have funxp_eq : ∀ p : Primes, ∀ (i : I), hilbertSym (funxp p) (a i) = ep i p := fun p ↦
      Exists.choose_spec (h3.1 p)
    have xp_ne_zero : ∀ p : Primes, funxp p ≠ 0 := by
      intro p hp
      specialize funxp_eq p
      simp only [hilbertSym, hp, Int.cast_eq_zero, true_or, ↓reduceIte] at funxp_eq
      --Seriously?
      --Can this be simplified? It's also used in several places in some variants.
      have : ∀ i : I, 0 = 1 ∨ 0 = -1 := by
        intro i
        specialize hep i p
        specialize funxp_eq i
        grind only
      simp at this
    let funxr := h3.2.choose
    have funxr_eq : ∀ (i : I), hilbertSym (funxr) (a i) = ereal i := Exists.choose_spec h3.2
    have xr_ne_zero : funxr ≠ 0 := by
      intro hr
      simp only [hilbertSym, hr, Int.cast_eq_zero, true_or, ↓reduceIte] at funxr_eq
      --Seriously?
      have : ∀ i : I, 0 = 1 ∨ 0 = -1 := by
        intro i
        specialize hereal i
        specialize funxr_eq i
        grind
      simp at this
    have square_approx : ∃ x' : ℚˣ, (∀ (p : Primes), p ∈ (S a) → IsSquare
        (x' / (funxp p) : ℚ_[p])) ∧ IsSquare (x' / h3.2.choose):= by
      have := Rat.approximation'' (S a)
      rw [dense_iff_inter_open] at this
      --let U : Set (Π p : S a, ℚ_[p]ˣ) := Π p, sorry
      --have hU : IsOpen U :=
      --???
      sorry
    obtain ⟨x', ⟨hx', hx'real⟩⟩ := square_approx
    have almost_all_one_x' (i : I) := almost_all_one x' (Units.mk0 (a i) (by simp [ha]))
    have prod_eq_one_x' (i : I) : (∏ᶠ (p : Primes), hilbertSym (x' : ℚ_[p]) (a i)) *
        hilbertSym (x' : ℝ) (a i) = 1 := prod_eq_one x' (Units.mk0 (a i) (by simp [ha]))
    have hilbertSym_agree_on_S :
        ∀ (i : I), ∀ (p : Primes), p ∈ (S a) → hilbertSym (x' : ℚ_[p]) (a i) = ep i p := by
      intro i p hpS
      have : hilbertSym (x': ℚ_[p]) (a i) = hilbertSym (funxp p) (a i) := by
        have ⟨c, hc⟩ : ∃ c, x' = funxp p * c ^ 2 := by
          specialize hx' p hpS
          obtain ⟨c', hc'⟩ := hx'
          use c'
          rw [pow_two, ← hc']
          field_simp [xp_ne_zero]
        rw [hc, mul_left_square_eq (by aesop)]
      simp [this, funxp]
      grind only
    have hilbertSym_agree_on_infty :
        ∀ (i : I), hilbertSym (x' : ℝ) (a i) = ereal i := by
      intro i
      have : hilbertSym (x' : ℝ) (a i) = hilbertSym (h3.2.choose) (a i) := by
        have ⟨c, hc⟩ : ∃ c, x' = h3.2.choose * c ^ 2 := by
          obtain ⟨c', hc'⟩ := hx'real
          use c'
          rw [pow_two, ← hc']
          field_simp [xr_ne_zero]
          grind only
        rw [hc, mul_left_square_eq (by aesop)]
      simp [this]
      grind
    let etap : I → Primes → ℤ := fun i p ↦ (ep i p) * hilbertSym (x' : ℚ_[p]) (a i)
    have hetap1 : ∀ i : I, ∀ p : Primes, etap i p = 1 ∨ etap i p = -1 := by
      intro i p
      have := eq_one_or_neg_one_of_ne_zero (by simp : (x'.1 : ℚ_[p]) ≠ 0)
          (by simp [ha] : ((a i) : ℚ_[p]) ≠ 0)
      grind
    let etareal : I → ℤ := fun i ↦ (ereal i) * hilbertSym (x' : ℝ) (a i)
    have heta1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, etap i p = 1 := by
      intro i
      let F := {p : Primes | ¬hilbertSym (x' : ℚ_[p]) (a i) = 1} ∪ {p | ¬ep i p = 1}
      have finiteF : F.Finite := by
        specialize h1 i
        simp only [eventually_cofinite, Units.val_mk0, Rat.cast_intCast] at h1 almost_all_one_x' i
        simp only [Set.finite_union, F]
        exact ⟨almost_all_one_x' i, h1⟩
      exact Set.Finite.subset finiteF (fun p ↦ by grind)
    have heta2 : ∀ i : I, (∏ᶠ (p : Primes), etap i p) * etareal i = 1 := by
      intro i
      simp only [etap, etareal]
      rw [finprod_mul_distrib]
      · calc _
        _ = ((∏ᶠ (p : Primes), ep i p) * ereal i) * ((∏ᶠ (p : Primes), hilbertSym (x' : ℚ_[p])
          (a i)) * hilbertSym (x' : ℝ) (a i)) := by ring
        _ = 1 * 1 := by rw [h2 i, prod_eq_one_x' i]
      · simp only [Function.HasFiniteMulSupport, Function.mulSupport]
        simp only [eventually_cofinite] at h1
        exact h1 i
      · simp only [Function.HasFiniteMulSupport, Function.mulSupport]
        simp only [eventually_cofinite] at almost_all_one_x' i
        exact almost_all_one_x' i
    have heta3 : ((∀ (p : Primes), ∃ xp : ℚ_[p], ∀ i : I, hilbertSym xp (a i) = etap i p)) ∧
        ∃ xr : ℝ, ∀ i : I, hilbertSym xr (a i) = etareal i := by
      refine ⟨fun p ↦ ⟨x' * funxp p, fun i ↦
        (by simp [funxp, padic_mul_left_eq, funxp_eq, etap]; ring)⟩, ⟨x' * h3.2.choose,
          (by simp [real_mul_left_eq, etareal]; grind)⟩⟩
    have etadisjoint_ST : Disjoint (S a) (T hetap1 heta1) := by
      suffices hprop : ∀ i : I, ∀ p ∈ S a, etap i p = 1 by
        rw [Finset.disjoint_left]
        intro p hpS
        rw [ep_eq_one_iff_not_mem_T]
        grind
      intro i p hpS
      simp [etap, hilbertSym_agree_on_S i p hpS]
      grind
    have etainfty_not_mem_T : ∀ i : I, etareal i = 1 := by
      simp [etareal, hilbertSym_agree_on_infty]
      grind
    have ⟨xeta, hxeta⟩ := existence_disjoint ha hetap1 heta1 heta2 heta3 etadisjoint_ST
      etainfty_not_mem_T
    use xeta * x'
    refine fun i ↦ ⟨fun p ↦ by simp [padic_mul_left_eq, hxeta i, etap]; grind only, by simp
      [real_mul_left_eq, hxeta i, etainfty_not_mem_T i, hilbertSym_agree_on_infty i]⟩
end Integer

theorem exists_rat_with_finite_prescribed_hilbertSym
    {I : Type*} [Finite I] [Nonempty I] (a : I → ℚˣ) {ep : I → Primes → ℤ} {ereal : I → ℤ}
    (hep : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (hereal : ∀ i : I, ereal i = 1 ∨ ereal i = -1) :
    (∃ x : ℚˣ, ∀ i : I, (∀ p : Primes, hilbertSym (x : ℚ_[p]) (a i) = ep i p) ∧
      hilbertSym (x : ℝ) (a i) = ereal i) ↔
      (∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1) ∧
      (∀ i : I, (∏ᶠ (p : Primes), ep i p) * ereal i = 1) ∧
      ((∀ (p : Primes), ∃ xp : ℚ_[p], ∀ i : I, hilbertSym xp (a i) = ep i p)) ∧
      ∃ xr : ℝ, ∀ i : I, hilbertSym xr (a i) = ereal i := by
  have : Fintype I := Fintype.ofFinite I
  let d := ∏ i, (a i).1.den
  have hd : d ≠ 0 := by simp [d, Finset.prod_ne_zero_iff]
  have heq (i : I) : ((a i).1 * d ^ 2).den = 1 := by
    classical
    simp only [cast_prod, d]
    rw [Finset.prod_eq_mul_prod_sdiff_singleton i _ (by simp)]
    simp only [mul_pow, pow_two ((a i).1.den : ℚ), ← mul_assoc, Rat.mul_den_eq_num]
    norm_cast
  simp_rw [Rat.den_eq_one_iff] at heq
  set b : I → ℤ := fun i ↦ ((a i).1 * d ^ 2).num with hb
  have hb0 (i : I) : ((a i).1 * d ^ 2).num ≠ 0 := by simp [hd]
  have hp (p : Primes) (i : I) (x : ℚ_[p]) : hilbertSym x (a i) = hilbertSym x (b i : ℚ) := by
    rw [hb, heq, Rat.cast_mul, Rat.cast_pow, hilbertSym.mul_right_square_eq (by simp [hd])]
  have hr (i : I) (x : ℝ) : hilbertSym x (a i) = hilbertSym x (b i : ℚ) := by
    rw [hb, heq, Rat.cast_mul, Rat.cast_pow, hilbertSym.mul_right_square_eq (by simp [hd])]
  simp_rw [hp, hr]
  exact exists_rat_with_finite_prescribed_hilbertSym_of_int hb0 hep hereal


theorem exists_rat_with_two_prescribed_hilbertSym (a b : ℚˣ) {ep ep' : Primes → ℤ} {er er' : ℤ}
    (hep : ∀ p : Primes, ep p = 1 ∨ ep p = -1) (hep' : ∀ p : Primes, ep' p = 1 ∨ ep' p = -1)
    (her : er  = 1 ∨ er = -1) (her' : er'  = 1 ∨ er' = -1) :
    (∃ x : ℚˣ, (∀ p : Primes, hilbertSym (x : ℚ_[p]) a = ep p ∧
      hilbertSym (x : ℚ_[p]) b = ep' p) ∧ hilbertSym (x : ℝ) a = er ∧ hilbertSym (x : ℝ) b = er') ↔
      ((∀ᶠ (p : Primes) in cofinite, ep p = 1) ∧
      (∀ᶠ (p : Primes) in cofinite, ep' p = 1)) ∧
     (((∏ᶠ (p : Primes), ep p) * er = 1) ∧ ((∏ᶠ (p : Primes), ep' p) * er' = 1)) ∧
      (∀ (p : Primes), ∃ xp : ℚ_[p], hilbertSym xp a = ep p ∧ hilbertSym xp b = ep' p) ∧
      ∃ xr : ℝ, hilbertSym xr a = er ∧ hilbertSym xr b = er':= by
  convert exists_rat_with_finite_prescribed_hilbertSym (I := Fin 2) (a := ![a, b])
    (ep := ![ep, ep']) (ereal := ![er, er']) (by simp [hep, hep']) (by simp [her, her']) <;>
  aesop

end hilbertSym
