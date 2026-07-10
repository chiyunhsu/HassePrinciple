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

open Filter Nat

variable {I : Type*} {ep : I → Primes → ℤ} {ereal : I → ℤ}

/-- The necessary conditions in the Existence Theorem are indeed necessary. -/
private lemma necessary_cond (x : ℚˣ) {a : I → ℤ} (ha : ∀ i, a i ≠ 0)
    (h : ∀ i : I, (∀ p : Primes, hilbertSym (x : ℚ_[p]) (a i) = ep i p) ∧
      hilbertSym (x : ℝ) (a i) = ereal i) :
    (∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1) ∧
    (∀ i : I, (∏ᶠ p : Primes, ep i p) * ereal i = 1) ∧
    (∀ p : Primes, ∃ xp : ℚ_[p], ∀ i : I, hilbertSym xp (a i) = ep i p) ∧
    ∃ xr : ℝ, ∀ i : I, hilbertSym xr (a i) = ereal i := by
  let afun : I → ℚˣ := fun i ↦ Units.mk0 (a i) (by simp [ha])
  refine ⟨fun i ↦ by simp only [← h i, eventually_cofinite]; exact almost_all_one x (afun i),
    fun i ↦ by simp only [← h i]; exact prod_eq_one x (afun i), fun p ↦ ⟨x, by simp [h]⟩, x,
      by simp [h]⟩

/-- From ep i p = 1 or -1, we deduce that ep i p = -1 iff not ep i p = 1. -/
private lemma ep_eq_neg_one_iff_not_one
    (hep : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1) {i : I} {p : Primes} :
    ep i p = -1 ↔ ¬ep i p = 1 :=
  ⟨fun h ↦ by simp [h], fun h ↦ (hep i p).resolve_left h⟩

/-- Using the product formula for the Hilbert symbol and for ep i, if we show that
hilbertSym x (a i) = ep i p for all but one p, we are done. -/
private lemma all_but_one_places_suffice (q : Primes) (x : ℚˣ) {a : I → ℤ} (ha : ∀ i, a i ≠ 0)
    (hep : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1)
    (h2 : ∀ i : I, (∏ᶠ (p : Primes), ep i p) * ereal i = 1)
    (h4 : ∀ i : I, (∀ p : Primes, p ≠ q → hilbertSym (x : ℚ_[p]) (a i) = ep i p) ∧
      hilbertSym (x : ℝ) (a i) = ereal i) :
    ∀ i : I, (∀ p : Primes, hilbertSym (x : ℚ_[p]) (a i) = ep i p) ∧
      hilbertSym (x : ℝ) (a i) = ereal i := by
  let afun : I → ℚˣ := fun i ↦ Units.mk0 (a i) (by simp [ha])
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
      rw [finprod_cond_ne _ _ (h1 i), ← ne_eq, Finset.prod_ne_zero_iff]
      grind
    · exact almost_all_one x (afun i)
  · exact (h4 i).1 p hpq

/-- Define S to be the (finite!) set of primes that divide either the numerator or the denominator
of some (a i). N.B. In Serre, S contains also ∞. -/
private noncomputable def S [Fintype I] {a : I → ℤ} (_ : ∀ i, a i ≠ 0) : Finset Primes :=
  (Finset.univ.biUnion (fun i ↦ (Int.natAbs (a i)).primeFactors) ∪
    {2}).preimage Subtype.val Subtype.val_injective.injOn

private lemma Tfin [Finite I] (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1)
    (hep : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1) :
    (⋃ i : I, {p : Primes | ep i p = -1}).Finite := by
  refine (Set.finite_iUnion fun i ↦ ?_)
  simp only [eventually_cofinite, ← ep_eq_neg_one_iff_not_one hep, Int.reduceNeg] at h1
  exact h1 i

/-- Define T to be the (finite!) set of primes such that at least one of the e_{i,v} is -1. -/
private noncomputable def T [Fintype I] (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1)
    (hep : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1) : Finset Primes :=
  Set.Finite.toFinset (Tfin h1 hep)

private lemma ep_eq_one_of_not_mem_T
    [Fintype I] (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1)
    (hep : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1) (p : Primes)
    (hpT : p ∉ T h1 hep) (i : I) : ep i p = 1 := by
  simp only [T, Int.reduceNeg, ep_eq_neg_one_iff_not_one hep, Set.Finite.mem_toFinset,
    Set.mem_iUnion, Set.mem_setOf_eq, not_exists, Decidable.not_not] at hpT
  exact hpT i

private lemma ep_eq_one_iff_not_mem_T
    [Fintype I] (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1)
    (hep : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1) (p : Primes) :
    p ∉ T h1 hep ↔ ∀ i : I, ep i p = 1 := by
  refine ⟨fun h i ↦ ep_eq_one_of_not_mem_T h1 hep p h i, fun h ↦ by simp [T]; grind⟩


private lemma ep_eq_one_of_mem_S_disjoint [Fintype I] {a : I → ℤ} (ha : ∀ i, a i ≠ 0)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1)
    (hep : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1) {p : Primes}
    (hpS : p ∈ S ha) (disjoint_ST : Disjoint (S ha) (T h1 hep)) (i : I) : ep i p = 1 := by
  apply ep_eq_one_of_not_mem_T h1 hep
  rw [Finset.disjoint_left] at disjoint_ST
  exact disjoint_ST (by simp [hpS])

private lemma is_unit_ai_of_p_not_mem_S [Fintype I] {a : I → ℤ} (ha : ∀ i, a i ≠ 0)
    {p : Primes} (hpS : p ∉ S ha) :
    ∀ i : I, padicValInt p (a i) = 0 := by
  intro i
  simp only [S, Finset.union_singleton, Finset.mem_preimage, Finset.mem_insert, Finset.mem_biUnion,
    Finset.mem_univ, mem_primeFactors, p.2, ne_eq, Int.natAbs_eq_zero, true_and, not_or, not_exists,
    not_and, Decidable.not_not] at hpS
  have := hpS.2 i
  simp only [ha, imp_false, ← Int.natCast_dvd] at this
  simp [ha, this]

--is there a simp or at least simple mathlib lemmma for this? I couldn't shorten further.
--Edit: I did shorten further, but now I don't know where to put this.
private lemma _root_.eq_self_of_unit_to_odd_power (c : ℤ) (hodd : Odd c) :
    ∀ b : ℚ, (b = 1 ∨ b = -1) → b = b ^ c := by
  norm_num; rw [Odd.neg_one_zpow hodd]

/-- We first prove the Existence Theorem when S and T are disjoint. -/
private lemma existence_disjoint [Fintype I] [Nonempty I] {a : I → ℤ} (ha : ∀ i, a i ≠ 0)
    (hep : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1)
    (h2 : ∀ i : I, (∏ᶠ (p : Primes), ep i p) * ereal i = 1)
    (h3 : ((∀ (p : Primes), ∃ xp : ℚ_[p], ∀ i : I, hilbertSym xp (a i) = ep i p)) ∧
      ∃ xr : ℝ, ∀ i : I, hilbertSym xr (a i) = ereal i)
    (disjoint_ST : Disjoint (S ha) (T h1 hep))
    (infty_not_mem_T : ∀ i : I, ereal i = 1) :
      (∃ x : ℚˣ, ∀ i : I, (∀ p : Primes, hilbertSym (x : ℚ_[p]) (a i) = ep i p) ∧
      hilbertSym (x : ℝ) (a i) = ereal i) := by
  --Abbreviations for S and T.
  let S := hilbertSym.S ha
  let T := hilbertSym.T h1 hep
  --Define A to be the product of the elements in T, and M to be 4 times the product of the
  --elements in S. Both are nonzero.
  let A := ∏ t : T, (t : ℕ)
  have A_ne_zero : A ≠ 0 := by
    simp only [Finset.univ_eq_attach, ne_eq, Finset.prod_ne_zero_iff, Finset.mem_attach,
      forall_const, Subtype.forall, A]
    exact fun _ _ ↦ NeZero.out
  let M := 4 * ∏ s : S, (s : ℕ)
  have M_ne_zero : M ≠ 0 := by
    apply mul_ne_zero (by lia)
    simp only [Finset.univ_eq_attach, ne_eq, Finset.prod_ne_zero_iff, Finset.mem_attach,
      forall_const, Subtype.forall]
    exact fun _ _ ↦ NeZero.out
  --If S and T are disjoint, then A and M are coprime.
  have coprime_AM : A.Coprime M := by
    rw [coprime_fintype_prod_left_iff]
    refine fun t ↦ Coprime.mul_right ?_ ?_
    · have := (Finset.disjoint_iff_ne.mp disjoint_ST) ⟨2,prime_two⟩ (by simp [hilbertSym.S]) t
      rw [(by omega : 4 = 2 ^ 2), coprime_pow_right_iff (by omega), coprime_two_right]
      refine Prime.odd_of_ne_two t.1.2 ?_
      revert this
      simp [← Primes.coe_nat_inj]
      aesop
    · rw [coprime_fintype_prod_right_iff]
      intro s
      rw [coprime_primes t.1.2 s.1.2, ne_comm, ne_eq, Primes.coe_nat_inj]
      apply Disjoint.forall_ne_finset disjoint_ST s.2 t.2
  --We can apply Dirichlet's lemma.
  obtain ⟨q, hq⟩ := Set.Infinite.nonempty (infinite_setOf_prime_and_modEq M_ne_zero coprime_AM)
  simp only [Set.mem_setOf_eq] at hq
  obtain ⟨q_prime, q_cong⟩ := hq
  have q_prime_fact : Fact (Nat.Prime q) := by
    rw [fact_iff]
    exact q_prime
  --We define x to be A * q, which is a nonzero (positive) rational number.
  have x_unit : IsUnit (A * q : ℚ) := by
    simp [A_ne_zero, Nat.Prime.ne_zero q_prime]
  let x := x_unit.unit'
  have xpos : 0 < x.val := by simp [x, pos_of_ne_zero, A_ne_zero, pos_of_neZero q]
  --We apply lemma all_but_one_places_suffice to avoid dealing with q.
  use x
  apply all_but_one_places_suffice ⟨q, q_prime⟩ x ha hep h1 h2
  --In order to prove that hilbertSym x (a i) and ep i p agree everywhere, we consider separately
  --the cases p ∈ S, p ∈ T, p ∉ S ∪ T, and the real place (which is trivial since x > 0).
  refine fun i ↦ ⟨fun p pneq ↦ ?_, (by rw [real_eq (by simp) (by simp [ha i])]; simp [xpos,
    infty_not_mem_T])⟩
  by_cases hpS : p ∈ S
  · --Strategy: x is a square mod p, so it's a square in ℚ_[p], hence (x,_)ₚ=1.
    --Since p ∉ T, ep i p = 1 as well.
    rw [ep_eq_one_of_mem_S_disjoint ha h1 hep hpS disjoint_ST i]
    have ⟨b, hb⟩ : ∃ b : ℤ_[p], A * q = b ^ 2 := by
      by_cases hp2 : p = ⟨2, prime_two⟩
      · rw [hp2]
        apply Polynomial.squares_in_Z2 _ A
        have : (q : ZMod 8) = A := by
          apply ModEq.of_dvd at q_cong
          · rw [← ZMod.natCast_eq_natCast_iff] at q_cong
            exact q_cong
          · simp only [(by omega : 8 = 4 * 2), M]
            rw [mul_dvd_mul_iff_left (by omega),
              ← Finset.prod_subtype S (by simp) (fun s ↦ (s : ℕ))]
            exact Finset.dvd_prod_of_mem Subtype.val (by simp [S, hilbertSym.S] :
              ⟨2, prime_two⟩ ∈ S)
        simp [this, pow_two]
      · apply Polynomial.squares_in_Zp (by rw [← Primes.coe_nat_inj] at hp2; exact hp2) _ A
        have : (q : ZMod p) = A := by
          apply ModEq.of_dvd at q_cong
          · rw [← ZMod.natCast_eq_natCast_iff] at q_cong
            exact q_cong
          · simp only [M]
            refine Nat.dvd_mul_left_of_dvd ?_ 4
            rw [← Finset.prod_subtype S (by simp) (fun s ↦ (s : ℕ))]
            exact Finset.dvd_prod_of_mem Subtype.val hpS
        simp [this, pow_two]
    have ⟨sqrt_x, h_sqrt_x⟩ : ∃ b : ℚ_[p], A * q = b ^ 2 := by
      refine ⟨b, by rw_mod_cast [← hb]; simp⟩
    simp only [IsUnit.val_unit', Rat.cast_mul, Rat.cast_natCast, h_sqrt_x, x]
    rw [hilbertSym.comm, right_square_eq_one (by aesop) _]
    rw [← mul_self_ne_zero, ← pow_two, ← h_sqrt_x]
    exact_mod_cast isUnit_iff_ne_zero.mp x_unit
  · --Using the explicit formula, if p ∉ S, (x,a_i)ₚ = (legendreSym p a_i) ^ val_p(x).
    have hp2 : p.1 ≠ 2 := by
      revert hpS
      simp [S, hilbertSym.S]
      tauto
    qify
    rw [padic_odd_eq hp2 (by simp) (by simp [ha])]
    by_cases hpT : p ∈ T
    -- If p ∈ T, the exponent is 1.
    · have val_x : padicValRat p x.val = 1 := by
        rw [IsUnit.val_unit', ← Rat.natCast_mul, ← padicValRat_of_nat, cast_eq_one,
          padicValNat.mul A_ne_zero (Nat.Prime.ne_zero q_prime)]
        simp only [padicValNat_primes (by revert pneq; simp [← Primes.coe_nat_inj] : p ≠ q),
          add_zero, A]
        rw [← Finset.prod_subtype T (by simp) (fun t ↦ (t : ℕ)),
          (by grind : T = (T \ {p}) ∪ {p}), Finset.prod_union (by simp),
          Finset.prod_singleton, padicValNat.mul _ (Nat.Prime.ne_zero p.2), padicValNat_self]
        · norm_num
          right; right
          apply Prime.not_dvd_finsetProd (prime_iff.mp p.2)
          intro t
          simp [Finset.mem_sdiff, Finset.mem_singleton, ← ne_eq, ne_comm,
            Nat.prime_dvd_prime_iff_eq p.2 t.2, Primes.coe_nat_inj]
        · simp only [implies_true, ← Finset.prod_subtype T _ (fun t ↦ (t : ℕ)), A] at A_ne_zero
          rw [(by grind : T = (T \ {p}) ∪ {p}), Finset.prod_union (by simp)] at A_ne_zero
          grind
      --We use h3 to obtain a padic xp with the prescribed hilbertSym.
      obtain ⟨xp, hxp⟩ := h3.1 p
      have val_xp : Odd xp.valuation := by
        simp only [hilbertSym.T, Int.reduceNeg, Set.Finite.mem_toFinset, Set.mem_iUnion,
          Set.mem_setOf_eq, T] at hpT
        obtain ⟨j, hej⟩ := hpT
        specialize hxp j
        qify at hxp
        rw [hej,
          padic_odd_eq hp2 (fun xp0 ↦ by simp [hilbertSym, xp0] at hxp) (by simp [ha])] at hxp
        simp only [Padic.valuation_intCast, is_unit_ai_of_p_not_mem_S ha hpS, CharP.cast_eq_zero,
          mul_zero, mul_ite, PadicInt.val_mkUnits, mul_one, ite_self, Int.negOnePow_zero,
          Units.val_one, Int.cast_one, zpow_zero, one_mul, Int.reduceNeg, Int.cast_neg,
          zpow_eq_neg_one_iff₀] at hxp
        exact hxp.2
      simp only [Padic.valuation_ratCast, val_x, Padic.valuation_intCast,
        is_unit_ai_of_p_not_mem_S ha hpS, CharP.cast_eq_zero, mul_zero, mul_ite,
        PadicInt.val_mkUnits, mul_one, ite_self, Int.negOnePow_zero, Units.val_one, Int.cast_one,
        zpow_zero, zpow_one, one_mul, ← hxp, Int.cast_inj]
      qify
      rw [padic_odd_eq hp2 (fun xp0 ↦ ?_) (by simp [ha])]
      swap
      · simp [hilbertSym, xp0] at hxp
      --Seriously?
        have : ∀ i : I, 0 = 1 ∨ 0 = -1 := by
          intro i
          specialize hep i p
          grind
        simp at this
      · simp only [Padic.valuation_intCast, is_unit_ai_of_p_not_mem_S ha hpS, CharP.cast_eq_zero,
        mul_zero, mul_ite, PadicInt.val_mkUnits, mul_one, ite_self, Int.negOnePow_zero,
        Units.val_one, Int.cast_one, zpow_zero, one_mul]
        apply eq_self_of_unit_to_odd_power xp.valuation val_xp
        exact_mod_cast PadicInt.legendreSym.eq_one_or_neg_one (by simp : IsUnit (Padic.unitPart
          (Units.mk0 ((a i) : ℚ_[p]) _)).1)
    · --If p ∉ T, the exponent is 0, so (x,a_i)ₚ = 1. Also, ep i p = 1.
      have val_x : padicValRat p x.val = 0 := by
        simp only [IsUnit.val_unit', x]
        rw [← Rat.natCast_mul, ← padicValRat_of_nat, cast_eq_zero, padicValNat.mul A_ne_zero
          (Nat.Prime.ne_zero q_prime)]
        have : p ≠ q := by
          contrapose pneq
          rw [← Primes.coe_nat_inj]
          simp only [pneq]
        simp only [padicValNat_primes this, add_zero, A]
        norm_num
        right; right
        apply Prime.not_dvd_finsetProd (prime_iff.mp p.2)
        intro t htinT hdvd
        simp_rw [Nat.prime_dvd_prime_iff_eq p.2 t.1.2, Primes.coe_nat_inj] at hdvd
        simp only [hdvd, SetLike.coe_mem, not_true_eq_false] at hpT
      simp only [hilbertSym.T, Int.reduceNeg, ep_eq_neg_one_iff_not_one hep, Set.mem_iUnion,
        Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_exists, Decidable.not_not, T] at hpT
      simp [is_unit_ai_of_p_not_mem_S ha hpS, val_x, hpT]

/-- Given a finite set of rational numbers `{a_i}_{i ∈ I}` and numbers `e_{i,v} ∈ {± 1}`,
there exists a rational number `x` such that the Hilbert symbols `(x,a_i)_v` at each place `v`
is equal to `e_{i,v}` if and only if
1) for all `i`, almost all `e_{i,v}` are 1
2) for all `i`, the product of all `e_{i,v}` is 1
3) for each place `v`, there is some `x_v ∈ Q_v` with `(x_v,a_i)_v = e_{i,v}`. -/
theorem exists_rat_with_finite_prescribed_hilbertSym_of_int
    {I : Type*} [Finite I] [Nonempty I] {a : I → ℤ} (ha : ∀ i, a i ≠ 0) {ep : I → Primes → ℤ}
    {ereal : I → ℤ} (hep : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (hereal : ∀ i : I, ereal i = 1 ∨ ereal i = -1) :
    (∃ x : ℚˣ, ∀ i : I, (∀ p : Primes, hilbertSym (x : ℚ_[p]) (a i) = ep i p) ∧
      hilbertSym (x : ℝ) (a i) = ereal i) ↔
      (∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1) ∧
      (∀ i : I, (∏ᶠ (p : Primes), ep i p) * ereal i = 1) ∧
      ((∀ (p : Primes), ∃ xp : ℚ_[p], ∀ i : I, hilbertSym xp (a i) = ep i p)) ∧
      ∃ xr : ℝ, ∀ i : I, hilbertSym xr (a i) = ereal i := by
  have := Fintype.ofFinite I
  refine ⟨fun ⟨x,h⟩ ↦ (by apply necessary_cond <;> assumption), fun ⟨h1, h2, h3⟩ ↦ ?_⟩
  by_cases disjoint_ST : Disjoint (S ha) (T h1 hep) ∧
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
      have : ∀ i : I, 0 = 1 ∨ 0 = -1 := by
        intro i
        specialize hep i p
        specialize funxp_eq i
        grind
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
    have square_approx : ∃ x' : ℚˣ, (∀ (p : Primes), p ∈ (S ha) → IsSquare
        (x' / (funxp p) : ℚ_[p])) ∧ IsSquare (x' / h3.2.choose):= by
      have := Rat.approximation'' (S ha)
      rw [dense_iff_inter_open] at this
      --let U : Set (Π p : S a, ℚ_[p]ˣ) := Π p, Padic.squares p
      --have hU : IsOpen U :=
      --???
      sorry
    obtain ⟨x', ⟨hx', hx'real⟩⟩ := square_approx
    have almost_all_one_x' (i : I) := almost_all_one x' (Units.mk0 (a i) (by simp [ha]))
    have prod_eq_one_x' (i : I) : (∏ᶠ (p : Primes), hilbertSym (x' : ℚ_[p]) (a i)) *
        hilbertSym (x' : ℝ) (a i) = 1 := prod_eq_one x' (Units.mk0 (a i) (by simp [ha]))
    have hilbertSym_agree_on_S :
        ∀ (i : I), ∀ (p : Primes), p ∈ (S ha) → hilbertSym (x' : ℚ_[p]) (a i) = ep i p := by
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
      grind
    have hilbertSym_agree_on_infty :
        ∀ (i : I), hilbertSym (x' : ℝ) (a i) = ereal i := by
      intro i
      have : hilbertSym (x' : ℝ) (a i) = hilbertSym (h3.2.choose) (a i) := by
        have ⟨c, hc⟩ : ∃ c, x' = h3.2.choose * c ^ 2 := by
          obtain ⟨c', hc'⟩ := hx'real
          use c'
          rw [pow_two, ← hc']
          field_simp [xr_ne_zero]
          grind
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
    have etadisjoint_ST : Disjoint (S ha) (T heta1 hetap1) := by
      suffices hprop : ∀ i : I, ∀ p ∈ S ha, etap i p = 1 by
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
    refine fun i ↦ ⟨fun p ↦ by simp [padic_mul_left_eq]; grind, by simp [real_mul_left_eq]; grind⟩

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
