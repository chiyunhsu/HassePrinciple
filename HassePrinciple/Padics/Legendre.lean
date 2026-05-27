/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/

module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.Padics.RingHoms

/-! # The Legendre Symbol for Padic Integers. -/

@[expose] public section


namespace PadicInt
variable (p : ℕ) [Fact (Nat.Prime p)] (u : ℤ_[p]ˣ)

/-- The zmodRepr of a p-adic unit is nonzero modulo p. -/
lemma zmodRepr_units_ne_zero_modp : ((u.val).zmodRepr : ZMod p) ≠ 0 := by
  have := zmodRepr_lt_p u.val
  have := PadicInt.zmodRepr_units_ne_zero u
  rw_mod_cast [ZMod.natCast_eq_zero_iff]
  refine Nat.not_dvd_of_pos_of_lt ?_ ?_
  all_goals repeat omega

/-- We define the Legendre symbol (at p) for a p-adic unit as the Legendre symbol (at p) of its
reduction mod p. -/
noncomputable def legendreSym : ℤˣ := by
  constructor
  pick_goal 3
  · exact _root_.legendreSym p ((u.val).zmodRepr)
  pick_goal 3
  · exact _root_.legendreSym p ((u.val).zmodRepr)
  all_goals {
    rw [← sq, _root_.legendreSym]
    simp only [Int.cast_natCast, quadraticChar_apply, sq_eq_one_iff, Int.reduceNeg]
    apply quadraticChar_dichotomy
    exact zmodRepr_units_ne_zero_modp p u
  }

/-- By definition, the Legendre symbol is equal to the Legendre symbol of its reduction mod p. -/
theorem legendreSym_eq : legendreSym p u = _root_.legendreSym p ((u.val).zmodRepr) := rfl

namespace legendreSym

/-- We have the congruence `legendreSym p u ≡ u ^ (p / 2) mod p`. -/
theorem eq_pow : (legendreSym p u : ZMod p) = (((u.val).zmodRepr) : ZMod p) ^ (p / 2) := by
  rw [legendreSym_eq p u, _root_.legendreSym.eq_pow, Int.cast_natCast]

/-- If u is a p-adic unit, then `legendreSym p u` is `1` or `-1`. -/
theorem eq_one_or_neg_one : legendreSym p u = 1 ∨ legendreSym p u = -1 :=
  Int.units_eq_one_or (legendreSym p u)

/-- If u is a p-adic unit, then `legendreSym p u = -1` iff `legendreSym p u ≠ 1`. -/
theorem eq_neg_one_iff_not_one :
    legendreSym p u = -1 ↔ ¬legendreSym p u = 1 :=
  ⟨fun h ↦ by rw [h]; simp only [neg_units_ne_self, not_false_eq_true],
    fun h₂ ↦ (or_iff_right h₂).mp (eq_one_or_neg_one p u)⟩

/-- The Legendre symbol at 1 is 1. -/
@[simp]
theorem at_one : legendreSym p 1 = 1 := by
  ext
  simp only [legendreSym, _root_.legendreSym, Units.val_one]
  rw [(by apply zmodRepr_natCast_ofNat (by apply Nat.Prime.one_lt; expose_names; exact Fact.out) :
    zmodRepr (1 : ℤ_[p]) = 1)]
  rw_mod_cast [MulChar.map_one]

/-- The Legendre symbol is multiplicative in `u` for `p` fixed. -/
theorem mul : ∀ u v : ℤ_[p]ˣ, legendreSym p (u * v) = legendreSym p u * legendreSym p v := by
  intro u v
  ext
  simp only [legendreSym, _root_.legendreSym, Units.val_mul, Int.cast_natCast]
  have : (u * v).val.zmodRepr = u.val.zmodRepr * v.val.zmodRepr % p:= by
    simp only [Units.val_mul, zmodRepr_mul]
  have : (quadraticChar (ZMod p)) (u.val * v.val).zmodRepr = (quadraticChar (ZMod p))
      (u.val.zmodRepr * v.val.zmodRepr) := by
    rw_mod_cast [this]
    simp only [ZMod.natCast_mod, Nat.cast_mul, quadraticChar_apply]
  rw [this]
  exact MulHomClass.map_mul (quadraticChar (ZMod p)) ↑(u.val).zmodRepr ↑(v.val).zmodRepr


-- The Legendre symbol is a homomorphism of groups.
-- @[simps]
noncomputable def legendreSym_hom : ℤ_[p]ˣ →* ℤˣ where
  toFun := legendreSym p
  map_one' := at_one p
  map_mul' := mul p

/-- The square of the symbol is 1. -/
theorem sq_one : legendreSym p u ^ 2 = 1 := by
  exact Int.units_pow_two (legendreSym p u)

/-- The Legendre symbol of `u^2` at `p` is 1. -/
theorem sq_one' : legendreSym p (u ^ 2) = 1 := by
  rw [sq, mul p u u, ← sq, sq_one]

/-- The Legendre symbol `legendreSym p u = 1` iff `u` is a square mod `p`. -/
theorem eq_one_iff (u : ℤ_[p]ˣ) : legendreSym p u = 1 ↔ IsSquare (u.val.zmodRepr : ZMod p) := by
  constructor
  · intro h
    have : (legendreSym p u : ℤ) = 1 := by rw [h]; simp only [Units.val_one]
    rw [← quadraticChar_one_iff_isSquare (zmodRepr_units_ne_zero_modp p u)]
    rw [legendreSym_eq p u, _root_.legendreSym] at this
    exact_mod_cast this
  · intro h
    rw [← quadraticChar_one_iff_isSquare (zmodRepr_units_ne_zero_modp p u)] at h
    ext
    simp only [legendreSym, _root_.legendreSym, Units.val_one]
    exact_mod_cast h

/-- `legendreSym p a = -1` iff `a` is a nonsquare mod `p`. -/
theorem eq_neg_one_iff (u : ℤ_[p]ˣ) :
    legendreSym p u = -1 ↔ ¬IsSquare (u.val.zmodRepr : ZMod p) := by
  rw [eq_neg_one_iff_not_one, eq_one_iff p u]

--I don't think we need this, since it's true for ℤ implies it's true for ℤ_[p]
-- section QuadraticForm

-- /-!
-- ### Applications to binary quadratic forms
-- -/


-- /-- The Legendre symbol `legendreSym p a = 1` if there is a solution in `ℤ/pℤ`
-- of the equation `x^2 - a*y^2 = 0` with `y ≠ 0`. -/
-- theorem eq_one_of_sq_sub_mul_sq_eq_zero {p : ℕ} [Fact p.Prime] {a : ℤ} (ha : (a : ZMod p) ≠ 0)
--     {x y : ZMod p} (hy : y ≠ 0) (hxy : x ^ 2 - a * y ^ 2 = 0) : legendreSym p a = 1 := by
--   apply_fun (· * y⁻¹ ^ 2) at hxy
--   simp only [zero_mul] at hxy
--   rw [(by ring : (x ^ 2 - ↑a * y ^ 2) * y⁻¹ ^ 2 = (x * y⁻¹) ^ 2 - a * (y * y⁻¹) ^ 2),
--     mul_inv_cancel₀ hy, one_pow, mul_one, sub_eq_zero, pow_two] at hxy
--   exact (eq_one_iff p ha).mpr ⟨x * y⁻¹, hxy.symm⟩

-- /-- The Legendre symbol `legendreSym p a = 1` if there is a solution in `ℤ/pℤ`
-- of the equation `x^2 - a*y^2 = 0` with `x ≠ 0`. -/
-- theorem eq_one_of_sq_sub_mul_sq_eq_zero' {p : ℕ} [Fact p.Prime] {a : ℤ} (ha : (a : ZMod p) ≠ 0)
--     {x y : ZMod p} (hx : x ≠ 0) (hxy : x ^ 2 - a * y ^ 2 = 0) : legendreSym p a = 1 := by
--   haveI hy : y ≠ 0 := by
--     rintro rfl
--     rw [zero_pow two_ne_zero, mul_zero, sub_zero, sq_eq_zero_iff] at hxy
--     exact hx hxy
--   exact eq_one_of_sq_sub_mul_sq_eq_zero ha hy hxy

-- /-- If `legendreSym p a = -1`, then the only solution of `x^2 - a*y^2 = 0` in `ℤ/pℤ`
-- is the trivial one. -/
-- theorem eq_zero_mod_of_eq_neg_one {p : ℕ} [Fact p.Prime] {a : ℤ} (h : legendreSym p a = -1)
--     {x y : ZMod p} (hxy : x ^ 2 - a * y ^ 2 = 0) : x = 0 ∧ y = 0 := by
--   have ha : (a : ZMod p) ≠ 0 := by
--     intro hf
--     rw [(eq_zero_iff p a).mpr hf] at h
--     simp at h
--   by_contra hf
--   rcases imp_iff_or_not.mp (not_and'.mp hf) with hx | hy
--   · rw [eq_one_of_sq_sub_mul_sq_eq_zero' ha hx hxy, CharZero.eq_neg_self_iff] at h
--     exact one_ne_zero h
--   · rw [eq_one_of_sq_sub_mul_sq_eq_zero ha hy hxy, CharZero.eq_neg_self_iff] at h
--     exact one_ne_zero h

-- /-- If `legendreSym p a = -1` and `p` divides `x^2 - a*y^2`, then `p` must divide `x` and `y`. -/
-- theorem prime_dvd_of_eq_neg_one {p : ℕ} [Fact p.Prime] {a : ℤ} (h : legendreSym p a = -1)
--     {x y : ℤ}
--     (hxy : (p : ℤ) ∣ x ^ 2 - a * y ^ 2) : ↑p ∣ x ∧ ↑p ∣ y := by
--   simp_rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hxy ⊢
--   push_cast at hxy
--   exact eq_zero_mod_of_eq_neg_one h hxy


-- end QuadraticForm

-- section Values

-- /-!
-- ### The value of the Legendre symbol at `-1`

-- See `jacobiSym.at_neg_one` for the corresponding statement for the Jacobi symbol.
-- -/


-- variable {p : ℕ} [Fact p.Prime]

-- open ZMod

-- /-- `legendreSym p (-1)` is given by `χ₄ p`. -/
-- theorem legendreSym.at_neg_one (hp : p ≠ 2) : legendreSym p (-1) = χ₄ p := by
--   simp only [legendreSym, card p, quadraticChar_neg_one ((ringChar_zmod_n p).substr hp),
--     Int.cast_neg, Int.cast_one]

-- /-- The value of the Legendre symbol at `-a` is `χ₄ p` times the value at `a`. -/
-- theorem legendreSym.at_neg (hp : p ≠ 2) (a : ℤ) : legendreSym p (-a) = χ₄ p *
--     legendreSym p a := by
--   rw [neg_eq_neg_one_mul, legendreSym.mul p (-1) a, legendreSym.at_neg_one hp]

-- namespace ZMod

-- /-- `-1` is a square in `ZMod p` iff `p` is not congruent to `3` mod `4`. -/
-- theorem exists_sq_eq_neg_one_iff : IsSquare (-1 : ZMod p) ↔ p % 4 ≠ 3 := by
--   rw [FiniteField.isSquare_neg_one_iff, card p]

-- theorem mod_four_ne_three_of_sq_eq_neg_one {y : ZMod p} (hy : y ^ 2 = -1) : p % 4 ≠ 3 :=
--   exists_sq_eq_neg_one_iff.1 ⟨y, hy ▸ pow_two y⟩

-- /-- If two nonzero squares are negatives of each other in `ZMod p`, then `p % 4 ≠ 3`. -/
-- theorem mod_four_ne_three_of_sq_eq_neg_sq' {x y : ZMod p} (hy : y ≠ 0) (hxy : x ^ 2 = -y ^ 2) :
--     p % 4 ≠ 3 :=
--   @mod_four_ne_three_of_sq_eq_neg_one p _ (x / y)
--     (by
--       apply_fun fun z => z / y ^ 2 at hxy
--       rwa [neg_div, ← div_pow, ← div_pow, div_self hy, one_pow] at hxy)

-- theorem mod_four_ne_three_of_sq_eq_neg_sq {x y : ZMod p} (hx : x ≠ 0) (hxy : x ^ 2 = -y ^ 2) :
--     p % 4 ≠ 3 :=
--   mod_four_ne_three_of_sq_eq_neg_sq' hx (neg_eq_iff_eq_neg.mpr hxy).symm

-- end ZMod

-- end Values

end legendreSym

end PadicInt
