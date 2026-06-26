/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

public import HassePrinciple.HilbertSymbol.Basic
public import HassePrinciple.NumberTheory.ApproximationTheorem
public import HassePrinciple.Padics.Lemmas
import Mathlib


/-!
# Existence theorem
-/
@[expose] public section

namespace hilbertSym


/-- The necessary conditions in the Existence Theorem are necessary -/
lemma necessary_cond {I : Type*} [Finite I] (a : I → ℚˣ) {ep : I → Nat.Primes → ℤ} {ereal : I → ℤ}
    (_ : ∀ i : I, ∀ p : Nat.Primes, ep i p = 1 ∨ ep i p = -1)
    (_ : ∀ i : I, ereal i = 1 ∨ ereal i = -1) (x : ℚˣ)
    (h : ∀ i : I, (∀ p : Nat.Primes, hilbertSym (x : ℚ_[p]) (a i) = ep i p) ∧
      hilbertSym (x : ℝ) (a i) = ereal i) :
      (∀ i : I, ∀ᶠ (p : Nat.Primes) in Filter.cofinite, ep i p = 1) ∧
      (∀ i : I, (∏ᶠ (p : Nat.Primes), ep i p) * ereal i = 1) ∧
      ((∀ (p : Nat.Primes), ∃ xp : ℚ_[p], ∀ i : I, hilbertSym xp (a i) = ep i p)) ∧
      ∃ xr : ℝ, ∀ i : I, hilbertSym xr (a i) = ereal i := by
  refine ⟨fun i ↦ (by simp_rw [Filter.eventually_cofinite, ← h i]; exact almost_all_one x (a i)),
    fun i ↦ (by simp_rw [← h i]; exact prod_eq_one x (a i)),
    fun p ↦ (by use x; simp [h]), (by use x; simp [h])⟩


--define S to be the (finite!) set of primes that divide either the numerator or the denominator
--of some (a i). N.B. In Serre, S contains also 2 and ∞.
def SS {I : Type*} [Fintype I] (a : I → ℚˣ) :=
  Finset.univ.biUnion (fun (i : I) ↦ (Int.natAbs (a i).val.num * (a i).val.den).primeFactors)

--  define T to be the (finite!) set of primes such that at least one of the e_{i,v} is -1.
def T' {I : Type*} [Fintype I] (ep : I → Nat.Primes → ℤ) :=
    ⋃ i : I, {p : Nat.Primes | ep i p = -1}

def f {I : Type*} [Fintype I] (ep : I → Nat.Primes → ℤ) := fun (t' : T' ep) ↦ (t' : ℕ)


lemma Tfin {I : Type*} [Fintype I] {ep : I → Nat.Primes → ℤ}
    (h₁ : ∀ i : I, ∀ᶠ (p : Nat.Primes) in Filter.cofinite, ep i p = 1)
    (hep1 : ∀ i : I, ∀ p : Nat.Primes, ep i p = 1 ∨ ep i p = -1) :
    (Set.range (f ep)).Finite := by
  refine (Set.finite_range_iff ?_).mpr ?_
  · intro t1 t2 ht
    unfold f at ht
    ext
    exact_mod_cast ht
  · apply Set.finite_iUnion
    intro i
    specialize h₁ i
    simp only [Filter.eventually_cofinite] at h₁
    have (x : Nat.Primes) : ¬ep i x = 1 ↔ ep i x = -1 := by
      specialize hep1 i x
      lia
    simp_rw [this] at h₁
    exact h₁


noncomputable def TT {I : Type*} [Fintype I] {ep : I → Nat.Primes → ℤ}
    (h₁ : ∀ i : I, ∀ᶠ (p : Nat.Primes) in Filter.cofinite, ep i p = 1)
    (hep1 : ∀ i : I, ∀ p : Nat.Primes, ep i p = 1 ∨ ep i p = -1) : Finset ℕ :=
      Set.Finite.toFinset (Tfin h₁ hep1)

lemma existence_disjoint {I : Type*} [Finite I] [Fintype I] (a : I → ℚˣ) {ep : I → Nat.Primes → ℤ} {ereal : I → ℤ}
    (hep1 : ∀ i : I, ∀ p : Nat.Primes, ep i p = 1 ∨ ep i p = -1)
    (hereal : ∀ i : I, ereal i = 1 ∨ ereal i = -1)
    (h1 : ∀ i : I, ∀ᶠ (p : Nat.Primes) in Filter.cofinite, ep i p = 1)
    (h2 : ∀ i : I, (∏ᶠ (p : Nat.Primes), ep i p) * ereal i = 1)
    (h3 : (∀ (p : Nat.Primes), ∃ xp : ℚ_[p], ∀ i : I, hilbertSym xp (a i) = ep i p) ∧
      ∃ xr : ℝ, ∀ i : I, hilbertSym xr (a i) = ereal i)
      (disjoint_ST : Disjoint (SS a) (TT h1 hep1) ∧ 2 ∉ (TT h1 hep1) ∧ ∀ i : I, ereal i = 1) :
        (∃ x : ℚˣ, ∀ i : I, (∀ p : Nat.Primes, hilbertSym (x : ℚ_[p]) (a i) = ep i p) ∧
        hilbertSym (x : ℝ) (a i) = ereal i)
       := by
    let S := SS a
    let T := TT h1 hep1
    --S and T are made of prime numbers.
    have primes_S : ∀ s : S, Nat.Prime s := by sorry
    have primes_T : ∀ t : T, Nat.Prime t := by sorry
    --   intro t
    --   have tinT := Subtype.mem t
    --   simp only [T] at tinT
    --   have : ∀ x ∈ T, Nat.Prime x := by
    --     unfold T
    --     --simp only [Set.mem_range, Subtype.exists, forall_exists_index]
    --     intro x x_prime _ _
    --     have : x = x_prime := by aesop
    --     have : Nat.Prime x_prime := x_prime.2
    --     aesop
    --   aesop


    --Define A to be the product of the elements in T, and M to be 8 times the product of the
    --elements in S. Both are nonzero.
    let A := ∏ t : T, (t : ℕ)
    have A_ne_zero : A ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      simp only [Finset.univ_eq_attach, Finset.mem_attach, ne_eq, forall_const]
      intro t
      specialize primes_T t
      aesop
    let M := 8 * ∏ s : S, (s : ℕ) --technically should exclude 2 jere but probably not a problem
    have M_ne_zero : M ≠ 0 := by
      apply Nat.mul_ne_zero (by lia)
      rw [Finset.prod_ne_zero_iff]
      simp only [Finset.univ_eq_attach, Finset.mem_attach, ne_eq, forall_const]
      intro s
      specialize primes_S s
      aesop

    --Following Serre, we first assume that S and T are disjoint (and that 2, ∞ are not in T).

    have coprime_AM : A.Coprime M := by
        rw [Nat.coprime_fintype_prod_left_iff]
        refine fun t ↦ Nat.Coprime.mul_right ?_ ?_
        · have : Odd (t : ℕ) := by
            apply Nat.Prime.odd_of_ne_two (primes_T t)
            have two_notin_T := disjoint_ST.2.1
            rw [← Finset.forall_mem_not_eq] at two_notin_T
            apply ne_comm.mp (two_notin_T t (Subtype.mem t))
          rw [(by omega : 8 = 2^3), Nat.coprime_pow_right_iff (by omega)]
          exact Odd.coprime_two_right this
        · rw [Nat.coprime_fintype_prod_right_iff]
          intro s
          rw [Nat.coprime_primes (primes_T t) (primes_S s)]
          refine Disjoint.ne_of_mem ?_ (Subtype.mem t) (Subtype.mem s)
          simp only [Finset.disjoint_coe, (disjoint_ST.1).symm]
          sorry
    have dirichlet :=
        Set.Infinite.nonempty (Nat.infinite_setOf_prime_and_modEq M_ne_zero coprime_AM)
    obtain ⟨q, hq⟩ := dirichlet
    simp only [Set.mem_setOf_eq] at hq
    obtain ⟨q_prime, q_cong⟩ := hq

    let xQ := A * q
    have x_unit : IsUnit (xQ : ℚ) := by
      simp only [isUnit_iff_ne_zero, ne_eq, Nat.cast_eq_zero, xQ]
      rw [← ne_eq, Nat.mul_ne_zero_iff]
      simp [A_ne_zero, Nat.Prime.ne_zero q_prime]
    let x := x_unit.unit'


    have coe : ∀ b : ℚ, ∀ p : Nat.Primes,
      hilbertSym (x : ℚ_[p]) b = hilbertSym (x.1 : ℚ_[p]) b := fun b p ↦ by congr

    use x




    intro i
    refine ⟨fun ⟨p,pprime⟩ ↦ ?_, ?_⟩
    · by_cases hp : p = 2
      · --strategy: x is a square mod 8, so it's a square in ℚ_[2], hence (x,_)₂=1.
        --Since 2 ∉ T, ep i 2 = 1 as well.
        have hilbertSym_2 : hilbertSym (x : ℚ_[2]) (a i) = 1 := by
          rw [coe (a i) ⟨2, Nat.prime_two⟩]
          have ⟨xsqrt, hxsqrt⟩ : ∃ b : ℤ_[2], xQ = b ^ 2 := by
            apply Polynomial.squares_in_Z2 _ A
            have : q ≡ A [MOD M] := by sorry
            have : q ≡ A [MOD 8] := by sorry
            have := Nat.ModEq.mul_left A this
            simp [xQ]


            sorry

          --rw [hxsqrt, right_square_eq_one]
          sorry
        have e2 : ep i ⟨p,pprime⟩ = 1 := by
          have two_notin_T := disjoint_ST.2.1
          --maybe this is useful elsewhere, TODO move it.
          have t_in_T_iff : ∀ t : Nat.Primes , t.1 ∈ T ↔ ∃ j : I, ep j t = -1 := by
            intro t
            refine ⟨fun t_in_T ↦ ?_, fun eq_minus_one ↦ ?_⟩
            · simp only [Int.reduceNeg, Set.Finite.mem_toFinset, Set.mem_range, Subtype.exists,
              Set.mem_iUnion, Set.mem_setOf_eq, exists_prop, T, T', f] at t_in_T
              --obtain ⟨t1, ⟨i, hi⟩, hcoe⟩ := t_in_T
              use i
              sorry
              --rw [← (Nat.Primes.coe_nat_inj t1 t).mp hcoe]
              --exact hi
            · simp only [Int.reduceNeg, Set.Finite.mem_toFinset, Set.mem_range, Subtype.exists,
              Set.mem_iUnion, Set.mem_setOf_eq, exists_prop, T, T', f]
              sorry
              --use t
              --exact ⟨eq_minus_one, Nat.Primes.coe_pnat_nat t⟩
          specialize t_in_T_iff ⟨2, Nat.prime_two⟩
          rw [← not_iff_not] at t_in_T_iff
          have : ¬ ∃ j, ep j ⟨2, Nat.prime_two⟩ = -1 := by
            rw [← t_in_T_iff]
            exact two_notin_T
          simp only [Int.reduceNeg, not_exists] at this
          simp_rw [hp]
          apply (or_iff_left (this i)).mp
          simp [hep1]
        rw [e2]
        rw [← hilbertSym_2]
        congr
        · exact heq_of_eqRec_eq (congrArg Fact (congrArg Nat.Prime hp)) rfl
        · exact heq_of_eqRec_eq (congrArg Fact (congrArg Nat.Prime hp)) rfl
        · exact heq_of_eqRec_eq (congrArg Fact (congrArg Nat.Prime hp)) rfl


      · by_cases hp : p ∈ S
        · sorry
        · by_cases hp : p ∈ T
          · sorry
          · sorry
    · sorry

/-- Given a finite set of rational numbers `{a_i}_{i ∈ I}` and numbers `e_{i,v} ∈ {± 1}`,
there exists a rational number `x` such that the Hilbert symbols `(x,a_i)_v` at each place `v`
is equal to `e_{i,v}` if and only if
1) for all `i`, almost all `e_{i,v}` are 1
2) for all `i`, the product of all `e_{i,v}` is 1
3) for each place `v`, there is some `x_v ∈ Q_v` with `(x,a_i)_v = e_{i,v}`. -/
theorem exists_rat_with_finite_prescribed_hilbertSym
    {I : Type*} [Finite I] [Fintype I] (a : I → ℚˣ) {ep : I → Nat.Primes → ℤ} {ereal : I → ℤ}
    (hep1 : ∀ i : I, ∀ p : Nat.Primes, ep i p = 1 ∨ ep i p = -1)
    (hereal : ∀ i : I, ereal i = 1 ∨ ereal i = -1) :
    (∃ x : ℚˣ, ∀ i : I, (∀ p : Nat.Primes, hilbertSym (x : ℚ_[p]) (a i) = ep i p) ∧
      hilbertSym (x : ℝ) (a i) = ereal i) ↔
      (∀ i : I, ∀ᶠ (p : Nat.Primes) in Filter.cofinite, ep i p = 1) ∧
      (∀ i : I, (∏ᶠ (p : Nat.Primes), ep i p) * ereal i = 1) ∧
      ((∀ (p : Nat.Primes), ∃ xp : ℚ_[p], ∀ i : I, hilbertSym xp (a i) = ep i p)) ∧
      ∃ xr : ℝ, ∀ i : I, hilbertSym xr (a i) = ereal i := by
  refine ⟨fun ⟨x,h⟩ ↦ (by apply necessary_cond <;> assumption), fun ⟨h1,h2,h3⟩ ↦ ?_⟩
  let S := SS a
  let T := TT h1 hep1
  by_cases disjoint_ST : Disjoint S T ∧ 2 ∉ T ∧ ∀ i : I, ereal i = 1
  · exact existence_disjoint a hep1 hereal h1 h2 h3 disjoint_ST
  · sorry




theorem exists_rat_with_two_prescribed_hilbertSym (a b : ℚˣ) {ep ep' : Nat.Primes → ℤ} {er er' : ℤ}
    (hep : ∀ p : Nat.Primes, ep p = 1 ∨ ep p = -1) (hep' : ∀ p : Nat.Primes, ep' p = 1 ∨ ep' p = -1)
    (her : er  = 1 ∨ er = -1) (her' : er'  = 1 ∨ er' = -1) :
    (∃ x : ℚˣ, (∀ p : Nat.Primes, hilbertSym (x : ℚ_[p]) a = ep p ∧
      hilbertSym (x : ℚ_[p]) b = ep' p) ∧ hilbertSym (x : ℝ) a = er ∧ hilbertSym (x : ℝ) b = er') ↔
      ((∀ᶠ (p : Nat.Primes) in Filter.cofinite, ep p = 1) ∧
      (∀ᶠ (p : Nat.Primes) in Filter.cofinite, ep' p = 1)) ∧
     (((∏ᶠ (p : Nat.Primes), ep p) * er = 1) ∧ ((∏ᶠ (p : Nat.Primes), ep' p) * er' = 1)) ∧
      (∀ (p : Nat.Primes), ∃ xp : ℚ_[p], hilbertSym xp a = ep p ∧ hilbertSym xp b = ep' p) ∧
      ∃ xr : ℝ, hilbertSym xr a = er ∧ hilbertSym xr b = er':= by
  convert exists_rat_with_finite_prescribed_hilbertSym (I := Fin 2) (a := ![a, b])
    (ep := ![ep, ep']) (ereal := ![er, er']) (by simp [hep, hep']) (by simp [her, her']) <;>
  aesop

end hilbertSym
