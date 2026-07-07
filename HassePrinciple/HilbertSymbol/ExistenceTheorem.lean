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

variable {I : Type*} {a : I → ℚˣ} {ep : I → Primes → ℤ} {ereal : I → ℤ}

/-- The necessary conditions in the Existence Theorem are indeed necessary. -/
private lemma necessary_cond (x : ℚˣ)
    (h : ∀ i : I, (∀ p : Nat.Primes, hilbertSym (x : ℚ_[p]) (a i) = ep i p) ∧
      hilbertSym (x : ℝ) (a i) = ereal i) :
    (∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1) ∧
    (∀ i : I, (∏ᶠ p : Primes, ep i p) * ereal i = 1) ∧
    (∀ p : Primes, ∃ xp : ℚ_[p], ∀ i : I, hilbertSym xp (a i) = ep i p) ∧
    ∃ xr : ℝ, ∀ i : I, hilbertSym xr (a i) = ereal i :=
  ⟨fun i ↦ by simp [← h i,  almost_all_one x (a i)],
    fun i ↦ by simp [← h i, prod_eq_one x (a i)], fun p ↦ ⟨x, by simp [h]⟩, ⟨x, by simp [h]⟩⟩

/-- From ep i p = 1 or -1, we deduce that ep i p = -1 iff not ep i p = 1. -/
private lemma ep_eq_neg_one_iff_not_one
    (hep : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1) {i : I} {p : Primes} :
    ep i p = -1 ↔ ¬ep i p = 1 :=
  ⟨fun h ↦ by simp [h], fun h ↦ (hep i p).resolve_left h⟩

/-- Using the product formula for the Hilbert symbol and for ep i, if we show that
hilbertSym x (a i) = ep i p for all but one p, we are done. -/
private lemma all_but_one_places_suffice (q : Primes)
    (hep1 : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1)
    (h2 : ∀ i : I, (∏ᶠ (p : Primes), ep i p) * ereal i = 1)
    (h4 : ∃ x : ℚˣ, ∀ i : I, (∀ p : Primes, p ≠ q → hilbertSym (x : ℚ_[p]) (a i) = ep i p) ∧
      hilbertSym (x : ℝ) (a i) = ereal i) :
    ∃ x : ℚˣ, ∀ i : I, (∀ p : Primes, hilbertSym (x : ℚ_[p]) (a i) = ep i p) ∧
      hilbertSym (x : ℝ) (a i) = ereal i := by
  obtain ⟨x, hx⟩ := h4
  refine ⟨x, fun i ↦ ⟨fun p ↦ ?_, by simp [hx]⟩⟩
  --The nontrivial case is when p=q.
  by_cases hpq : p = q
  · have hprod' : ∏ᶠ (p' : Primes) (_ : p' ≠ q), hilbertSym (x : ℚ_[p']) (a i) =
        ∏ᶠ (p' : Primes) (_ : p' ≠  q), ep i p' := by
      congr! with p' h
      rw [(hx i).1 p' h]
    have hprod : ∏ᶠ (p : Primes), hilbertSym (x : ℚ_[p]) (a i) = ∏ᶠ (p : Primes), ep i p := by
      rw [← mul_left_inj' (by grind : ereal i ≠ 0)]
      nth_rw 1 [← (hx i).2, prod_eq_one x (a i), h2 i]
    rw [← mul_finprod_cond_ne q (almost_all_one x (a i)),
      ← mul_finprod_cond_ne q (h1 i), hprod', mul_eq_mul_right_iff, ← hpq] at hprod
    apply hprod.resolve_right
    rw [finprod_cond_ne _ _ (h1 i), ← ne_eq, Finset.prod_ne_zero_iff]
    grind
  · exact (hx i).1 p hpq

variable (a) in
/-- Define S to be the (finite!) set of primes that divide either the numerator or the denominator
of some (a i). N.B. In Serre, S contains also 2 and ∞. -/
private def SS [Fintype I] :=
  Finset.univ.biUnion (fun (i : I) ↦ (Int.natAbs (a i).val.num * (a i).val.den).primeFactors)

variable (ep) in
/-- Define T to be the (finite!) set of primes such that at least one of the e_{i,v} is -1. -/
private def T' :=
    ⋃ i : I, {p : Primes | ep i p = -1}

variable (ep) in
private def f := fun (t' : T' ep) ↦ (t' : ℕ)

private lemma Tfin [Finite I]
    (h₁ : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1)
    (hep1 : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1) :
    (Set.range (f ep)).Finite := by
  refine (Set.finite_range_iff fun t1 t2 ht ↦ ?_).mpr (Set.finite_iUnion fun i ↦ ?_)
  · simp only [f, PNat.coe_inj] at ht
    ext
    exact_mod_cast ht
  · simp only [eventually_cofinite, ← ep_eq_neg_one_iff_not_one hep1, Int.reduceNeg] at h₁
    exact h₁ i

private noncomputable def TT [Fintype I]
    (h₁ : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1)
    (hep1 : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1) : Finset ℕ :=
      Set.Finite.toFinset (Tfin h₁ hep1)

/-- We first prove the Existence Theorem when S and T are disjoint. -/
private lemma existence_disjoint
    [Fintype I] (hep1 : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (hereal : ∀ i : I, ereal i = 1 ∨ ereal i = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1)
    (h2 : ∀ i : I, (∏ᶠ (p : Primes), ep i p) * ereal i = 1)
    (h3 : ((∀ (p : Primes), ∃ xp : ℚ_[p], ∀ i : I, hilbertSym xp (a i) = ep i p)) ∧
      ∃ xr : ℝ, ∀ i : I, hilbertSym xr (a i) = ereal i)
    (disjoint_ST : Disjoint (SS a) (TT h1 hep1))
    (two_notin_T : 2 ∉ (TT h1 hep1))
    (infty_notin_T : ∀ i : I, ereal i = 1) :
      (∃ x : ℚˣ, ∀ i : I, (∀ p : Primes, hilbertSym (x : ℚ_[p]) (a i) = ep i p) ∧
      hilbertSym (x : ℝ) (a i) = ereal i) := by
--Properties and definitions regardsing S and T.
  let S := SS a
  let T := TT h1 hep1
  --S and T consist of prime numbers.
  have primes_S : ∀ s : S, Prime s := by
    simp [S, SS]
    aesop
  have primes_T : ∀ t : T, Prime t := by
    simp only [TT, T', Int.reduceNeg, Subtype.forall, Set.Finite.mem_toFinset, Set.mem_range, f,
      Subtype.exists, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop, forall_exists_index, and_imp,
      T]
    intro a x i h eq
    rw [← eq]
    exact x.2
  have t_in_T_iff : ∀ t : Primes , t.1 ∈ T ↔ ∃ j : I, ep j t = -1 := by
    simp only [TT, T', Int.reduceNeg, Set.Finite.mem_toFinset, Set.mem_range, f,
      Subtype.exists, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop, T]
    intro t
    refine ⟨fun ⟨a, ⟨i, hi⟩, h⟩ ↦ ⟨i, ?_⟩, by aesop⟩
    rw [← hi]
    congr
    exact_mod_cast h.symm
  --Define A to be the product of the elements in T, and M to be 8 times the product of the
  --elements in S. Both are nonzero.
  let A := ∏ t : T, (t : ℕ)
  have A_ne_zero : A ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    simp only [Finset.univ_eq_attach, Finset.mem_attach, ne_eq, forall_const]
    intro t
    specialize primes_T t
    aesop
  let M := 8 * ∏ s : S, (s : ℕ) --technically should exclude 2 here but probably not a problem
  have M_ne_zero : M ≠ 0 := by
    apply Nat.mul_ne_zero (by lia)
    rw [Finset.prod_ne_zero_iff]
    simp only [Finset.univ_eq_attach, Finset.mem_attach, ne_eq, forall_const]
    intro s
    specialize primes_S s
    aesop
  --If S and T are disjoint (and 2, ∞ ∉ T), then A and M are coprime.
  have coprime_AM : A.Coprime M := by
      rw [Nat.coprime_fintype_prod_left_iff]
      refine fun t ↦ Nat.Coprime.mul_right ?_ ?_
      · rw [(by omega : 8 = 2^3), Nat.coprime_pow_right_iff (by omega)]
        refine Odd.coprime_two_right (Prime.odd_of_ne_two (primes_T t) ?_)
        rw [← Finset.forall_mem_not_eq] at two_notin_T
        apply ne_comm.mp (two_notin_T t (Subtype.mem t))
      · rw [Nat.coprime_fintype_prod_right_iff]
        intro s
        rw [Nat.coprime_primes (primes_T t) (primes_S s)]
        refine Disjoint.ne_of_mem ?_ (Subtype.mem t) (Subtype.mem s)
        simp only [Finset.disjoint_coe]
        exact disjoint_ST.symm
  --We can apply Dirichlet's lemma.
  have dirichlet :=
      Set.Infinite.nonempty (Nat.infinite_setOf_prime_and_modEq M_ne_zero coprime_AM)
  obtain ⟨q, hq⟩ := dirichlet
  simp only [Set.mem_setOf_eq] at hq
  obtain ⟨q_prime, q_cong⟩ := hq
  have q_prime_fact : Fact (Nat.Prime q) := by
    rw [fact_iff]
    exact q_prime
  --We define x to be A * q, which is a nonzero rational number.
  let xQ := A * q
  have x_unit : IsUnit (xQ : ℚ) := by
    simp only [isUnit_iff_ne_zero, ne_eq, Nat.cast_eq_zero, xQ]
    rw [← ne_eq, Nat.mul_ne_zero_iff]
    simp [A_ne_zero, Nat.Prime.ne_zero q_prime]
  let x := x_unit.unit'
  --We apply lemma all_but_one_places_suffice to exclude dealing with q.
  apply all_but_one_places_suffice ⟨q, q_prime⟩ hep1 h1 h2
  use x
  --In order to prove that hilbertSym x (a i) and ep i p agree everywhere, we consider separately
  --the cases p = 2, p ∈ S, p ∈ p ∉ S ∪ T, and the real place.
  intro i
  refine ⟨fun ⟨p,pprime⟩ pneq ↦ ?_, ?_⟩
  · have pprime_fact : Fact (Nat.Prime p) := by
      rw [fact_iff]
      exact pprime
    by_cases hp2 : p = 2
    · --Strategy: x is a square mod 8, so it's a square in ℚ_[2], hence (x,_)₂=1.
      --Since 2 ∉ T, ep i 2 = 1 as well.
      have hilbertSym_2 : hilbertSym (x : ℚ_[2]) (a i) = 1 := by
        have ⟨sqrt_x, h_sqrt_x⟩ : ∃ b : ℚ_[2], xQ = b ^ 2 := by
          have ⟨b, hb⟩ : ∃ b : ℤ_[2], xQ = b ^ 2 := by
            apply Polynomial.squares_in_Z2 _ A
            have : (q : ZMod 8) = A := by
              apply Nat.ModEq.of_dvd (by omega : 8 ∣ M) at q_cong
              rw [← ZMod.natCast_eq_natCast_iff] at q_cong
              exact q_cong
            simp [xQ, this]
            ring
          use b
          rw_mod_cast [← hb]
          simp only [PadicInt.coe_natCast]
        simp only [IsUnit.val_unit', Rat.cast_natCast, x]
        rw [h_sqrt_x, hilbertSym.comm, right_square_eq_one (by aesop)]
        rw [← mul_self_ne_zero, ← pow_two, ← h_sqrt_x]
        exact_mod_cast isUnit_iff_ne_zero.mp x_unit
      have e2 : ep i ⟨p, pprime⟩ = 1 := by
        specialize t_in_T_iff ⟨2, prime_two⟩
        rw [← not_iff_not] at t_in_T_iff
        have : ¬ ∃ j, ep j ⟨2, prime_two⟩ = -1 := t_in_T_iff.mp two_notin_T
        simp only [Int.reduceNeg, not_exists] at this
        simp_rw [hp2]
        apply (or_iff_left (this i)).mp
        simp [hep1]
      rw [e2, ← hilbertSym_2]
      congr <;> exact heq_of_eqRec_eq (congrArg Fact (congrArg Nat.Prime hp2)) rfl
    · by_cases hpS : p ∈ S
      · --Strategy: x is a square mod p, so it's a square in ℚ_[p], hence (x,_)ₚ=1.
        --Since p ∉ T, ep i p = 1 as well.
        have p_dvd_M : p ∣ M := by
          simp only [M]
          refine Nat.dvd_mul_left_of_dvd ?_ 8
          rw [← Finset.prod_subtype S (by simp) (fun s ↦ s)]
          exact Finset.dvd_prod_of_mem (fun i ↦ i) hpS
        have hilbertSym_pS : hilbertSym (x : ℚ_[p]) (a i) = 1 := by
          have ⟨sqrt_x, h_sqrt_x⟩ : ∃ b : ℚ_[p], xQ = b ^ 2 := by
            have ⟨b, hb⟩ : ∃ b : ℤ_[p], xQ = b ^ 2 := by
              apply Polynomial.squares_in_Zp (by aesop) _ A
              have : (q : ZMod p) = A := by
                apply Nat.ModEq.of_dvd (p_dvd_M) at q_cong
                rw [← ZMod.natCast_eq_natCast_iff] at q_cong
                exact q_cong
              simp [xQ, this]
              ring
            use b
            rw_mod_cast [← hb]
            simp only [PadicInt.coe_natCast]
          simp only [IsUnit.val_unit', Rat.cast_natCast, x]
          rw [h_sqrt_x, hilbertSym.comm, right_square_eq_one (by aesop)]
          rw [← mul_self_ne_zero, ← pow_two, ← h_sqrt_x]
          exact_mod_cast isUnit_iff_ne_zero.mp x_unit
        have ep_1 : ep i ⟨p, pprime⟩ = 1 := by
          specialize t_in_T_iff ⟨p, pprime⟩
          rw [← not_iff_not] at t_in_T_iff
          have : ¬ ∃ j, ep j ⟨p, pprime⟩ = -1 := by
            rw [← t_in_T_iff]
            simp only
            exact Disjoint.notMem_of_mem_left_finset disjoint_ST hpS
          simp only [Int.reduceNeg, not_exists] at this
          apply (or_iff_left (this i)).mp
          simp [hep1]
        rw [hilbertSym_pS, ep_1]
      · --If p ∉ S, then all the a_i are p-adic units.
        have val_ai : ∀ i : I, padicValRat p (a i).val = 0 := by
          intro i
          rw [padicValRat.multiplicity_sub_multiplicity (Nat.Prime.ne_one pprime) (by simp)]
          simp only [SS, Finset.mem_biUnion, Finset.mem_univ, Nat.mem_primeFactors, pprime,
              ne_eq, mul_eq_zero, Int.natAbs_eq_zero, Rat.num_eq_zero, Units.ne_zero,
              Rat.den_ne_zero, or_self, not_false_eq_true, and_true, true_and, not_exists,
              S] at hpS
          specialize hpS i
          --can these be improved?
          have val_num_eq_zero : multiplicity (p : ℤ) ((a i).val).num = 0 := by
            rw [multiplicity_eq_zero]
            intro ⟨c, hc⟩
            rw [hc] at hpS
            apply hpS
            use c.natAbs * (a i).val.den
            simp [Int.natAbs_mul]
            ring
          have val_den_eq_zero : multiplicity p ((a i).val).den = 0 := by
            rw [multiplicity_eq_zero]
            intro ⟨c, hc⟩
            rw [hc] at hpS
            apply hpS
            use (a i).val.num.natAbs * c
            ring
          linarith
        --Using the explicit formula, we prove that (x,a_i)ₚ = (legendreSym p a_i) ^ val_p(x).
        by_cases hpT : p ∈ T
        -- If p ∈ T, the exponent is 1.
        · have val_x : padicValRat p x.val = 1 := by
            simp only [Nat.cast_mul, IsUnit.val_unit', x, xQ]
            rw [← Rat.natCast_mul, ← padicValRat_of_nat, Nat.cast_eq_one]
            rw [padicValNat.mul A_ne_zero (Nat.Prime.ne_zero q_prime)]
            have : p ≠ q := by
              contrapose pneq;
              rw [← Primes.coe_nat_inj]
              simp only [pneq]
            simp only [padicValNat_primes this, add_zero]
            have : A = (∏ t ∈ T \ { p }, t) * p := by
              rw [← Finset.prod_eq_prod_sdiff_singleton_mul hpT]
              simp only [Finset.univ_eq_attach, A]
              rw [Finset.prod_subtype T ?_ (fun t ↦ t)]
              · congr
              · simp
            rw [this]
            rw [padicValNat.mul (by rw [this] at A_ne_zero; exact left_ne_zero_of_mul A_ne_zero)
              (Nat.Prime.ne_zero pprime), padicValNat_self]
            norm_num
            right; right
            apply Prime.not_dvd_finsetProd (Nat.prime_iff.mp pprime)
            intro t htnep
            simp only [Finset.mem_sdiff, Finset.mem_singleton] at htnep
            simp only [ne_comm, ne_eq,
              ← prime_dvd_prime_iff_eq pprime (Subtype.forall.mp primes_T t htnep.1)] at htnep
            exact htnep.2
          obtain ⟨xp, hxp⟩ := h3.1 ⟨p, pprime⟩
          have val_xp : Odd xp.valuation := by
            have ⟨j, hej⟩ := (t_in_T_iff ⟨p,pprime⟩).mp hpT
            specialize hxp j
            rw [hej] at hxp
            qify at hxp
            rw [padic_odd_eq hp2 (fun xp0 ↦ by (simp only [hilbertSym, xp0, Rat.cast_eq_zero,
            Units.ne_zero, or_false, ↓reduceIte] at hxp; grind)) (by simp)] at hxp
            simp only [Padic.valuation_ratCast, val_ai, mul_zero, mul_ite, PadicInt.val_mkUnits,
              mul_one, ite_self, Int.negOnePow_zero, Units.val_one, Int.cast_one, zpow_zero,
              one_mul, zpow_eq_neg_one_iff₀] at hxp
            exact hxp.2
          rw [← hxp i]
          qify
          rw [padic_odd_eq hp2 (by simp) (by simp), padic_odd_eq hp2
            (fun xp0 ↦ by (simp only [hilbertSym, xp0, Rat.cast_eq_zero,
            Units.ne_zero, or_false, ↓reduceIte] at hxp; specialize hxp i; grind)) (by simp)]
          simp only [Padic.valuation_ratCast, val_x, val_ai, mul_zero, mul_ite,
            PadicInt.val_mkUnits, mul_one, ite_self, Int.negOnePow_zero, Units.val_one,
            Int.cast_one, zpow_zero, zpow_one, one_mul]
          --I couldn't come up with a nicer proof of this, but maybe there is
          have one_or_neg_one_to_odd_eq_self :
              ∀ b : ℚ, (b = 1 ∨ b = -1) → b = b ^ xp.valuation := by
            intro b hb
            cases hb
            · aesop
            · expose_names
              rw [h]
              symm
              apply Odd.neg_one_zpow
              exact val_xp
          have : IsUnit (Padic.unitPart (Units.mk0 ((a i).val : ℚ_[p]) (by simp))).1 := by
            simp
          have := PadicInt.legendreSym.eq_one_or_neg_one this
          apply one_or_neg_one_to_odd_eq_self
          exact_mod_cast this
        · --In this case, the exponent is 0, so (x,a_i)ₚ = 1. Since p ∉ T, ep i p = 1 as well.
          have val_x : padicValRat p x.val = 0 := by
            simp only [Nat.cast_mul, IsUnit.val_unit', x, xQ]
            rw [← Rat.natCast_mul, ← padicValRat_of_nat, Nat.cast_eq_zero]
            rw [padicValNat.mul A_ne_zero (Nat.Prime.ne_zero q_prime)]
            have : p ≠ q := by
              contrapose pneq;
              rw [← Primes.coe_nat_inj]
              simp only [pneq]
            simp only [padicValNat_primes this, add_zero, A]
            norm_num
            right; right
            apply Prime.not_dvd_finsetProd (prime_iff.mp pprime)
            intro t htinT hdvd
            rw [prime_dvd_prime_iff_eq pprime (primes_T t)] at hdvd
            rw [hdvd] at hpT
            simp at hpT
          qify
          rw [padic_odd_eq hp2 (by simp) (by simp)]
          have : ep i ⟨p, pprime⟩ = 1 := by
            specialize t_in_T_iff ⟨p, pprime⟩
            rw [← not_iff_not] at t_in_T_iff
            simp only [Int.reduceNeg, not_exists] at t_in_T_iff
            have := t_in_T_iff.mp hpT i
            have := hep1 i ⟨p, pprime⟩
            tauto
          simp [val_ai, val_x, this]
  · simp only [ne_eq, Rat.cast_eq_zero, Units.ne_zero, not_false_eq_true, real_eq, Rat.cast_pos,
    Int.reduceNeg, infty_notin_T i, ite_eq_left_iff, not_or, not_lt, reduceCtorEq, imp_false,
    not_and, not_le]
    have : 0 < x.val := by
      simp only [Finset.univ_eq_attach, Nat.cast_mul, Nat.cast_prod, IsUnit.val_unit', Nat.cast_pos,
        Prime.pos q_prime, mul_pos_iff_of_pos_right, x, xQ, A]
      apply Finset.prod_pos
      intro t ht
      exact_mod_cast Prime.pos (primes_T t)
    simp [this]

/-- Given a finite set of rational numbers `{a_i}_{i ∈ I}` and numbers `e_{i,v} ∈ {± 1}`,
there exists a rational number `x` such that the Hilbert symbols `(x,a_i)_v` at each place `v`
is equal to `e_{i,v}` if and only if
1) for all `i`, almost all `e_{i,v}` are 1
2) for all `i`, the product of all `e_{i,v}` is 1
3) for each place `v`, there is some `x_v ∈ Q_v` with `(x_v,a_i)_v = e_{i,v}`. -/
theorem exists_rat_with_finite_prescribed_hilbertSym
    {I : Type*} [Finite I] (a : I → ℚˣ) {ep : I → Primes → ℤ} {ereal : I → ℤ}
    (hep1 : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (hereal : ∀ i : I, ereal i = 1 ∨ ereal i = -1) :
    (∃ x : ℚˣ, ∀ i : I, (∀ p : Primes, hilbertSym (x : ℚ_[p]) (a i) = ep i p) ∧
      hilbertSym (x : ℝ) (a i) = ereal i) ↔
      (∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1) ∧
      (∀ i : I, (∏ᶠ (p : Primes), ep i p) * ereal i = 1) ∧
      ((∀ (p : Primes), ∃ xp : ℚ_[p], ∀ i : I, hilbertSym xp (a i) = ep i p)) ∧
      ∃ xr : ℝ, ∀ i : I, hilbertSym xr (a i) = ereal i := by
  have := Fintype.ofFinite I
  refine ⟨fun ⟨x,h⟩ ↦ (by apply necessary_cond <;> assumption), fun ⟨h1, h2, h3⟩ ↦ ?_⟩
  by_cases disjoint_ST : Disjoint (SS a) (TT h1 hep1) ∧ 2 ∉ (TT h1 hep1) ∧
      ∀ i : I, ereal i = 1
  · exact existence_disjoint hep1 hereal h1 h2 h3 disjoint_ST.1 disjoint_ST.2.1 disjoint_ST.2.2
  · let funxp := fun (p : Primes) ↦ (h3.1 p).choose
    have square_approx : ∃ x' : ℚˣ, ∀ (p : Primes), IsSquare (x' / (funxp p) : ℚ_[p]) := by sorry
    obtain ⟨x', hx'⟩ := square_approx
    have hilbertSym_agree_on_S :
        ∀ (i : I), ∀ (p : Primes), p.1 ∈ (SS a) → hilbertSym (x' : ℚ_[p]) (a i) = ep i p := by sorry
    let etap : I → Primes → ℤ := fun i p ↦ (ep i p) * hilbertSym (x' : ℚ_[p]) (a i)
    have hetap1 : ∀ i : I, ∀ p : Primes, etap i p = 1 ∨ etap i p = -1 := by sorry
    let etareal : I → ℤ := fun i ↦ (ereal i) * hilbertSym (x' : ℝ) (a i)
    have hetareal : ∀ i : I, etareal i = 1 ∨ etareal i = -1 := by sorry
    have heta1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, etap i p = 1 := by sorry
    have heta2 : ∀ i : I, (∏ᶠ (p : Primes), etap i p) * etareal i = 1 := by sorry
    have heta3 : ((∀ (p : Primes), ∃ xp : ℚ_[p], ∀ i : I, hilbertSym xp (a i) = etap i p)) ∧
      ∃ xr : ℝ, ∀ i : I, hilbertSym xr (a i) = etareal i := by sorry
    have etadisjoint_ST : Disjoint (SS a) (TT heta1 hetap1) := by sorry
    have etatwo_notin_T : 2 ∉ (TT heta1 hetap1) := by sorry
    have etainfty_notin_T : ∀ i : I, etareal i = 1 := by sorry
    have ⟨xeta,hxeta⟩ := existence_disjoint hetap1 hetareal heta1 heta2 heta3 etadisjoint_ST
        etatwo_notin_T etainfty_notin_T
    use xeta * x'
    refine fun i ↦ ⟨fun p ↦ ?_, ?_⟩
    · sorry
    · sorry

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
