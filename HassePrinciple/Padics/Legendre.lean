/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/

module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.Padics.RingHoms

@[expose] public section

--Not sure where to put this.

namespace Padic

/--TODO--/
noncomputable def padicUnitPart_qp {p : ℕ} [hp : Fact (Nat.Prime p)] (x : ℚ_[p]ˣ) : ℚ_[p] :=
  x * (↑(p : ℚ_[p]) ^ (-(valuation x.val : ℤ)))

/--TODO--/
lemma padic_unit_part_unit {p : ℕ} [hp : Fact (Nat.Prime p)] (x : (ℚ_[p])ˣ) :
  ‖padicUnitPart_qp x‖ = 1 := by
  sorry

/--TODO--/
noncomputable def padicUnitPart {p : ℕ} [hp : Fact (Nat.Prime p)] (x : (ℚ_[p])ˣ) : ℤ_[p]ˣ :=
  PadicInt.mkUnits (padic_unit_part_unit x)

/--TODO--/
noncomputable def legp {p : ℕ} [hp : Fact (Nat.Prime p)] (u : ℤ_[p]ˣ) : ℤˣ :=
  if legendreSym p ((u.val).appr p % p) = 1 then 1 else -1

end Padic
