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
    (h : ∀ i : I, (∀ p : Primes, hilbertSym (x : ℚ_[p]) (a i) = ep i p) ∧
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
of some (a i). N.B. In Serre, S contains also ∞. -/
private noncomputable def SS [Fintype I] : Finset Primes :=
  (Finset.univ.biUnion (fun i ↦ (Int.natAbs (a i).val.num * (a i).val.den).primeFactors) ∪
    {2}).preimage Subtype.val Subtype.val_injective.injOn

private lemma Tfin [Finite I] (h₁ : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1)
    (hep1 : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1) :
    (⋃ i : I, {p : Primes | ep i p = -1}).Finite := by
  refine (Set.finite_iUnion fun i ↦ ?_)
  simp only [eventually_cofinite, ← ep_eq_neg_one_iff_not_one hep1, Int.reduceNeg] at h₁
  exact h₁ i

/-- Define T to be the (finite!) set of primes such that at least one of the e_{i,v} is -1. -/
private noncomputable def TT [Fintype I] (h₁ : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1)
    (hep1 : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1) : Finset Primes :=
  Set.Finite.toFinset (Tfin h₁ hep1)

private lemma ep_eq_one_of_not_mem_T
    [Fintype I] (h₁ : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1)
    (hep1 : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1) (p : Primes)
    (hpT : p ∉ TT h₁ hep1) (i : I) : ep i p = 1 := by
  simp only [TT, Int.reduceNeg, ep_eq_neg_one_iff_not_one hep1, Set.Finite.mem_toFinset,
    Set.mem_iUnion, Set.mem_setOf_eq, not_exists, Decidable.not_not] at hpT
  exact hpT i

/-- We first prove the Existence Theorem when S and T are disjoint. -/
private lemma existence_disjoint
    [Fintype I] (hep1 : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (hereal : ∀ i : I, ereal i = 1 ∨ ereal i = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1)
    (h2 : ∀ i : I, (∏ᶠ (p : Primes), ep i p) * ereal i = 1)
    (h3 : ((∀ (p : Primes), ∃ xp : ℚ_[p], ∀ i : I, hilbertSym xp (a i) = ep i p)) ∧
      ∃ xr : ℝ, ∀ i : I, hilbertSym xr (a i) = ereal i)
    (disjoint_ST : Disjoint (SS a) (TT h1 hep1))
    (infty_not_mem_T : ∀ i : I, ereal i = 1) :
      (∃ x : ℚˣ, ∀ i : I, (∀ p : Primes, hilbertSym (x : ℚ_[p]) (a i) = ep i p) ∧
      hilbertSym (x : ℝ) (a i) = ereal i) := by
  --Abbreviations for S and T.
  let S := SS a
  let T := TT h1 hep1
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
    · rw [(by omega : 4 = 2 ^ 2), coprime_pow_right_iff (by omega)]
      simp only [coprime_two_right]
      refine Prime.odd_of_ne_two t.1.2 ?_
      rw [Finset.disjoint_iff_ne] at disjoint_ST
      specialize disjoint_ST ⟨2,prime_two⟩ (by simp [SS]) t
      simp only [SetLike.coe_mem, forall_const] at disjoint_ST
      contrapose disjoint_ST
      rw [← Primes.coe_nat_inj]
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
  --We define x to be A * q, which is a nonzero rational number.
  have x_unit : IsUnit (A * q : ℚ) := by
    simp [A_ne_zero, Nat.Prime.ne_zero q_prime]
  let x := x_unit.unit'
  --We apply lemma all_but_one_places_suffice to exclude dealing with q.
  apply all_but_one_places_suffice ⟨q, q_prime⟩ hep1 h1 h2
  use x
  --In order to prove that hilbertSym x (a i) and ep i p agree everywhere, we consider separately
  --the cases p = 2, p ∈ S, p ∈ p ∉ S ∪ T, and the real place.
  refine fun i ↦ ⟨fun p pneq ↦ ?_, ?_⟩
  · --have pprime_fact : Fact (Prime p) := fact_iff.mpr p.2
    by_cases hp2 : p = ⟨2, prime_two⟩
    · --Strategy: x is a square mod 8, so it's a square in ℚ_[2], hence (x,_)₂=1.
      --Since 2 ∉ T, ep i 2 = 1 as well.
      have hilbertSym_2 : hilbertSym (x : ℚ_[2]) (a i) = 1 := by
        have ⟨sqrt_x, h_sqrt_x⟩ : ∃ b : ℚ_[2], A * q = b ^ 2 := by
          have ⟨b, hb⟩ : ∃ b : ℤ_[2], A * q = b ^ 2 := by
            apply Polynomial.squares_in_Z2 _ A
            have : (q : ZMod 8) = A := by
              have eight_dvd_M : 8 ∣ M := by
                rw [(by omega : 8 = 4 * 2)]
                simp only [M]
                rw [mul_dvd_mul_iff_left (by omega)]
                simp only [Finset.prod_coe_sort_eq_attach, Finset.prod_attach]
                sorry
              apply ModEq.of_dvd eight_dvd_M at q_cong
              rw [← ZMod.natCast_eq_natCast_iff] at q_cong
              exact q_cong
            simp [this]
            ring
          use b
          rw_mod_cast [← hb]
          simp only [PadicInt.coe_natCast]
        simp only [IsUnit.val_unit', Rat.cast_mul, Rat.cast_natCast, x]
        rw [h_sqrt_x, hilbertSym.comm, right_square_eq_one (by aesop)]
        rw [← mul_self_ne_zero, ← pow_two, ← h_sqrt_x]
        exact_mod_cast isUnit_iff_ne_zero.mp x_unit
      have e2 : ep i p = 1 := by
        apply ep_eq_one_of_not_mem_T h1 hep1
        rw [Finset.disjoint_left] at disjoint_ST
        exact disjoint_ST (by simp [hp2, SS])
      rw [e2, ← hilbertSym_2]
      congr <;> simp [hp2]
    · by_cases hpS : p ∈ S
      · --Strategy: x is a square mod p, so it's a square in ℚ_[p], hence (x,_)ₚ=1.
        --Since p ∉ T, ep i p = 1 as well.
        have p_dvd_M : p.1 ∣ M := by
          simp only [M]
          refine Nat.dvd_mul_left_of_dvd ?_ 4
          sorry
        have hilbertSym_pS : hilbertSym (x : ℚ_[p]) (a i) = 1 := by
          have ⟨sqrt_x, h_sqrt_x⟩ : ∃ b : ℚ_[p], A * q = b ^ 2 := by
            have ⟨b, hb⟩ : ∃ b : ℤ_[p], A * q = b ^ 2 := by
              apply Polynomial.squares_in_Zp _ _ A
              · have : (q : ZMod p) = A := by
                  apply ModEq.of_dvd (p_dvd_M) at q_cong
                  rw [← ZMod.natCast_eq_natCast_iff] at q_cong
                  exact q_cong
                simp [this]
                ring
              · simp only [← Primes.coe_nat_inj] at hp2
                exact hp2
            use b
            rw_mod_cast [← hb]
            simp only [PadicInt.coe_natCast]
          simp only [IsUnit.val_unit', Rat.cast_mul, Rat.cast_natCast, x]
          rw [h_sqrt_x, hilbertSym.comm, right_square_eq_one (by aesop)]
          rw [← mul_self_ne_zero, ← pow_two, ← h_sqrt_x]
          exact_mod_cast isUnit_iff_ne_zero.mp x_unit
        have ep_1 : ep i p = 1 := by
          apply ep_eq_one_of_not_mem_T h1 hep1
          rw [Finset.disjoint_left] at disjoint_ST
          exact disjoint_ST hpS
        rw [hilbertSym_pS, ep_1]
      · --If p ∉ S, then all the a_i are p-adic units.
        have val_ai : ∀ i : I, padicValRat p (a i).val = 0 := by
          intro i
          rw [padicValRat.multiplicity_sub_multiplicity (Nat.Prime.ne_one p.2) (by simp)]
          simp only [SS, Finset.union_singleton, Finset.mem_preimage, Finset.mem_insert,
            Finset.mem_biUnion, Finset.mem_univ, mem_primeFactors, p.2, ne_eq, mul_eq_zero,
            Int.natAbs_eq_zero, Rat.num_eq_zero, Units.ne_zero, Rat.den_ne_zero, or_self,
            not_false_eq_true, and_true, true_and, not_or, not_exists, S] at hpS
          have := hpS.2 i
          --can these be improved?
          have val_num_eq_zero : multiplicity (p : ℤ) ((a i).val).num = 0 := by
            rw [multiplicity_eq_zero]
            intro ⟨c, hc⟩
            rw [hc] at this
            apply this
            use c.natAbs * (a i).val.den
            simp [Int.natAbs_mul]
            ring
          have val_den_eq_zero : multiplicity (p : ℕ) ((a i).val).den = 0 := by
            rw [multiplicity_eq_zero]
            intro ⟨c, hc⟩
            rw [hc] at this
            apply this
            use (a i).val.num.natAbs * c
            ring
          linarith
        --Using the explicit formula, we prove that (x,a_i)ₚ = (legendreSym p a_i) ^ val_p(x).
        by_cases hpT : p ∈ T
        -- If p ∈ T, the exponent is 1.
        · have val_x : padicValRat p x.val = 1 := by
            simp only [IsUnit.val_unit', x]
            rw [← Rat.natCast_mul, ← padicValRat_of_nat, cast_eq_one]
            rw [padicValNat.mul A_ne_zero (Nat.Prime.ne_zero q_prime)]
            have : p ≠ q := by
              contrapose pneq;
              rw [← Primes.coe_nat_inj]
              simp only [pneq]
            simp only [padicValNat_primes this, add_zero]
            sorry
            --this part broke
            -- have : A = (∏ t ∈ T \ { p }, t) * p := by
            --   rw [← Finset.prod_eq_prod_sdiff_singleton_mul hpT]
            --   simp only [Finset.univ_eq_attach, A]
            --   rw [Finset.prod_subtype T ?_ (fun t ↦ t)]
            --   · congr
            --   · simp
            -- rw [this]
            -- rw [padicValNat.mul (by rw [this] at A_ne_zero; exact left_ne_zero_of_mul A_ne_zero)
            --   (Nat.Prime.ne_zero pprime), padicValNat_self]
            -- norm_num
            -- right; right
            -- apply Prime.not_dvd_finsetProd (prime_iff.mp pprime)
            -- intro t htnep
            -- simp only [Finset.mem_sdiff, Finset.mem_singleton] at htnep
            -- simp only [ne_comm, ne_eq,
            --   ← prime_dvd_prime_iff_eq pprime (Subtype.forall.mp primes_T t htnep.1)] at htnep
            -- exact htnep.2
          obtain ⟨xp, hxp⟩ := h3.1 p
          have val_xp : Odd xp.valuation := by
            simp only [TT, Int.reduceNeg, Set.Finite.mem_toFinset, Set.mem_iUnion, Set.mem_setOf_eq,
              T] at hpT
            obtain ⟨j, hej⟩ := hpT
            specialize hxp j
            rw [hej] at hxp
            qify at hxp
            rw [padic_odd_eq _ (fun xp0 ↦ by (simp only [hilbertSym, xp0, Rat.cast_eq_zero,
            Units.ne_zero, or_false, ↓reduceIte] at hxp; grind)) (by simp)] at hxp
            · simp only [Padic.valuation_ratCast, val_ai, mul_zero, mul_ite, PadicInt.val_mkUnits,
                mul_one, ite_self, Int.negOnePow_zero, Units.val_one, Int.cast_one, zpow_zero,
                one_mul, zpow_eq_neg_one_iff₀] at hxp
              exact hxp.2
            · simp_rw [← Primes.coe_nat_inj] at hp2; exact hp2
          rw [← hxp i]
          qify
          rw [padic_odd_eq _ (by simp) (by simp), padic_odd_eq _
            (fun xp0 ↦ by (simp only [hilbertSym, xp0, Rat.cast_eq_zero,
            Units.ne_zero, or_false, ↓reduceIte] at hxp; specialize hxp i; grind)) (by simp)]
          pick_goal 2
          · simp_rw [← Primes.coe_nat_inj] at hp2; exact hp2
          pick_goal 2
          · simp_rw [← Primes.coe_nat_inj] at hp2; exact hp2
          · simp only [Padic.valuation_ratCast, val_x, val_ai, mul_zero, mul_ite,
              PadicInt.val_mkUnits, mul_one, ite_self, Int.negOnePow_zero, Units.val_one,
              Int.cast_one, zpow_zero, zpow_one, one_mul]
          --I couldn't come up with a nicer proof of this, but maybe there is
            have one_or_neg_one_to_odd_eq_self :
                ∀ b : ℚ, (b = 1 ∨ b = -1) → b = b ^ xp.valuation := by
              intro b hb
              cases hb
              · subst b
                rw [one_zpow]
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
            simp only [IsUnit.val_unit', x]
            rw [← Rat.natCast_mul, ← padicValRat_of_nat, cast_eq_zero]
            rw [padicValNat.mul A_ne_zero (Nat.Prime.ne_zero q_prime)]
            have : p ≠ q := by
              contrapose pneq;
              rw [← Primes.coe_nat_inj]
              simp only [pneq]
            simp only [padicValNat_primes this, add_zero, A]
            norm_num
            right; right
            apply Prime.not_dvd_finsetProd (prime_iff.mp p.2)
            intro t htinT hdvd
            simp_rw [Nat.prime_dvd_prime_iff_eq p.2 t.1.2, Primes.coe_nat_inj] at hdvd
            simp only [hdvd, SetLike.coe_mem, not_true_eq_false] at hpT
          qify
          rw [padic_odd_eq _ (by simp) (by simp)]
          swap
          · simp_rw [← Primes.coe_nat_inj] at hp2; exact hp2
          · have : ep i p = 1 := by
              simp only [TT, Int.reduceNeg, Set.Finite.mem_toFinset, Set.mem_iUnion,
                Set.mem_setOf_eq, not_exists, T] at hpT
              specialize hpT i
              simp [ep_eq_neg_one_iff_not_one hep1] at hpT
              tauto
            simp [val_ai, val_x, this]
  · simp only [ne_eq, Rat.cast_eq_zero, Units.ne_zero, not_false_eq_true, real_eq, Rat.cast_pos,
    Int.reduceNeg, infty_not_mem_T i, ite_eq_left_iff, not_or, not_lt, reduceCtorEq, imp_false,
    not_and, not_le]
    have : 0 < x.val := by
      simp only [Finset.univ_eq_attach, cast_prod, IsUnit.val_unit', cast_pos, Prime.pos q_prime,
        mul_pos_iff_of_pos_right, x, A]
      apply Finset.prod_pos
      intro t ht
      simp [Prime.pos t.1.2]
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
  by_cases disjoint_ST : Disjoint (SS a) (TT h1 hep1) ∧
      ∀ i : I, ereal i = 1
  · exact existence_disjoint hep1 hereal h1 h2 h3 disjoint_ST.1 disjoint_ST.2
  · let funxp := fun (p : Primes) ↦ (h3.1 p).choose --is there a more user friendly way?
    have square_approx : ∃ x' : ℚˣ, ∀ (p : Primes), p ∈ (SS a) → IsSquare
        (x' / (funxp p) : ℚ_[p]) := by sorry
    obtain ⟨x', hx'⟩ := square_approx
    have hilbertSym_agree_on_S :
        ∀ (i : I), ∀ (p : Primes), p ∈ (SS a) → hilbertSym (x' : ℚ_[p]) (a i) = ep i p := by
      intro i p hpS
      have : hilbertSym (x': ℚ_[p]) (a i) = hilbertSym (funxp p) (a i) := by sorry
      rw [this]
      simp [funxp]
      sorry
    let etap : I → Primes → ℤ := fun i p ↦ (ep i p) * hilbertSym (x' : ℚ_[p]) (a i)
    have hetap1 : ∀ i : I, ∀ p : Primes, etap i p = 1 ∨ etap i p = -1 := by sorry
    let etareal : I → ℤ := fun i ↦ (ereal i) * hilbertSym (x' : ℝ) (a i)
    have hetareal : ∀ i : I, etareal i = 1 ∨ etareal i = -1 := by sorry
    have heta1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, etap i p = 1 := by sorry
    have heta2 : ∀ i : I, (∏ᶠ (p : Primes), etap i p) * etareal i = 1 := by sorry
    have heta3 : ((∀ (p : Primes), ∃ xp : ℚ_[p], ∀ i : I, hilbertSym xp (a i) = etap i p)) ∧
      ∃ xr : ℝ, ∀ i : I, hilbertSym xr (a i) = etareal i := by sorry
    have etadisjoint_ST : Disjoint (SS a) (TT heta1 hetap1) := by sorry
    have etainfty_not_mem_T : ∀ i : I, etareal i = 1 := by sorry
    have ⟨xeta, hxeta⟩ := existence_disjoint hetap1 hetareal heta1 heta2 heta3 etadisjoint_ST
        etainfty_not_mem_T
    use xeta * x'
    refine fun i ↦ ⟨fun p ↦ by simp [padic_mul_left_eq]; grind, by simp [real_mul_left_eq]; grind⟩

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
