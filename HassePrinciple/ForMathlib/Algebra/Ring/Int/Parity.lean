/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Algebra.Ring.Int.Parity

/-! # Lemma about power of integers -/

@[expose] public section

namespace Int

lemma zpow_odd_one_or_neg_one_eq_self {α : Type*} [DivisionMonoid α] [HasDistribNeg α]
    {c : ℤ} (hodd : Odd c) {a : α} (ha : a = 1 ∨ a = -1) :
    a ^ c = a := by
  rcases ha with ha | ha <;>
  simp [ha, neg_one_zpow_eq_ite, if_neg (Int.not_even_iff_odd.mpr hodd)]

end Int
