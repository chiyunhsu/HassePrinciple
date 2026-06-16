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

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- The zmodRepr of a p-adic unit is nonzero modulo p. -/
lemma zmodRepr_coe_ne_zero_of_isUnit {a : ℤ_[p]} (ha : IsUnit a) :
    ((a.zmodRepr : ℤ) : ZMod p) ≠ 0 := by
  rw_mod_cast [ZMod.natCast_eq_zero_iff]
  exact Nat.not_dvd_of_pos_of_lt
    (Nat.ne_zero_iff_zero_lt.mp (PadicInt.zmodRepr_units_ne_zero ha.unit)) (zmodRepr_lt_p a)

/-- We define the Legendre symbol for a `p`-adic integer `a` as the Legendre symbol (at `p`) of its
reduction modulo `p`. -/
noncomputable def legendreSym (a : ℤ_[p]) : ℤ := _root_.legendreSym p a.zmodRepr

variable {a b : ℤ_[p]}
namespace legendreSym

lemma legendreSymMod (z : ℤ_[p]) : legendreSym (z) = legendreSym (z.zmodRepr : ℤ_[p]) := by
  unfold legendreSym
  unfold _root_.legendreSym
  simp

/-- The Padic Legendre symbol agrees with the classical Legendre symbol on ℕ. -/
lemma intCastNat (z : ℕ) : legendreSym (z : ℤ_[p]) = _root_.legendreSym p z := by
  unfold legendreSym
  unfold _root_.legendreSym
  have h₁ : (z : ZMod p)= (((z : ℤ_[p]).zmodRepr : ℤ): ZMod p) :=by
    rw [zmodRepr_natCast]
    simp
  simp [quadraticCharFun, h₁]

/-- The Padic Legendre symbol agrees with the classical Legendre symbol on ℤ. -/
lemma intCast (z : ℤ) : legendreSym (z : ℤ_[p]) = _root_.legendreSym p z := by
  let w := (z : ZMod p).val
  have h₁ : _root_.legendreSym p z = _root_.legendreSym p w := by
    rw [legendreSym.mod]
    congr
    exact Eq.symm (ZMod.val_intCast z)
  have h₂ : legendreSym (z : ℤ_[p]) = legendreSym (w : ℤ_[p]) := by
    rw [legendreSymMod]
    congr
    rw [← val_toZMod_eq_zmodRepr, map_intCast]
  rw [h₁, h₂, intCastNat]

/-- We have the congruence `legendreSym a ≡ a ^ (p / 2) mod p`. -/
theorem eq_pow : (legendreSym a : ZMod p) = ((a.zmodRepr) : ZMod p) ^ (p / 2) := by
  rw [legendreSym, _root_.legendreSym.eq_pow, Int.cast_natCast]

/-- If `a` is a p-adic unit, then `legendreSym a` is `1` or `-1`. -/
theorem eq_one_or_neg_one (ha : IsUnit a) : legendreSym a = 1 ∨ legendreSym a = -1 := by
  rw [legendreSym]
  exact _root_.legendreSym.eq_one_or_neg_one p (zmodRepr_coe_ne_zero_of_isUnit ha)

/-- If a is a p-adic unit, then `legendreSym a = -1` iff `legendreSym a ≠ 1`. -/
theorem eq_neg_one_iff_not_one (ha : IsUnit a) :
    legendreSym a = -1 ↔ ¬legendreSym a = 1 := by
  constructor
  · lia
  · have := eq_one_or_neg_one ha
    intro h
    tauto

/-- The Legendre symbol of `p` and `a` is zero iff `p ∣ a`. -/
theorem eq_zero_iff : legendreSym a = 0 ↔ ¬ IsUnit a := by
  constructor
  · contrapose
    intro h
    have := eq_one_or_neg_one h
    lia
  · intro h
    rw [not_isUnit_iff, norm_lt_one_iff_dvd] at h
    unfold legendreSym
    rw [_root_.legendreSym.eq_zero_iff, zmodRepr_eq_zero_of_dvd h]
    simp

/-- The Legendre symbol at zero is zero. -/
@[simp]
theorem at_zero : legendreSym (0 : ℤ_[p]) = 0 := by
  rw [← _root_.legendreSym.at_zero p]
  apply intCast

/-- The Legendre symbol at 1 is 1. -/
@[simp]
theorem at_one : legendreSym (1 : ℤ_[p]) = 1 := by
  rw [← _root_.legendreSym.at_one p]
  apply intCast

/-- The Legendre symbol is multiplicative in `a` for `p` fixed. -/
protected theorem mul : legendreSym (a * b) = legendreSym a * legendreSym b := by
  simp [legendreSym, _root_.legendreSym, zmodRepr_mul, map_mul]

/-- The Legendre symbol is a homomorphism of monoids with zero. -/
@[simps]
noncomputable def hom : ℤ_[p] →*₀ ℤ where
  toFun        := legendreSym
  map_zero'    := at_zero
  map_one'     := at_one
  map_mul' _ _ := legendreSym.mul

/-- The square of the symbol is 1 if `a` is a unit. -/
theorem sq_one (ha : IsUnit a) : legendreSym a ^ 2 = 1 := by
  cases eq_one_or_neg_one ha
  all_goals {
    expose_names
    rw [h]
    ring
    }

/-- The Legendre symbol of `a^2` at `p` is 1 if `a` is a unit. -/
theorem sq_one' (ha : IsUnit a) : legendreSym (a ^ 2) = 1 := by
  rw [pow_two, legendreSym.mul]
  cases eq_one_or_neg_one ha
  all_goals {
    expose_names
    rw [h]
    ring
    }

/-- If `a` is a unit, then `legendreSym a = 1` iff `a` is a square mod `p`. -/
theorem eq_one_iff (ha : IsUnit a) : legendreSym a = 1 ↔ IsSquare ((a.zmodRepr : ℤ) : ZMod p) := by
  rw [legendreSym, _root_.legendreSym.eq_one_iff]
  exact zmodRepr_coe_ne_zero_of_isUnit ha

/-- `legendreSym p a = -1` iff `a` is a nonsquare mod `p`. -/
theorem eq_neg_one_iff (ha : IsUnit a) :
    legendreSym a = -1 ↔ ¬ IsSquare ((a.zmodRepr : ℤ) : ZMod p) := by
  rw [eq_neg_one_iff_not_one ha, eq_one_iff ha]

end legendreSym

end PadicInt
