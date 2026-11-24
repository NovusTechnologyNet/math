/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.Compendium.Defs
public import Pilean.Polylog.Defs

/-!
# Bailey's Compendium: the statements of degree `s` and the statements of degree 1

The formulas of degree `s ≥ 2` are stated with `Polylog.BaileyFormulaDeg x c s b B N a`:
`x = c · P(s, b^B, N, a)` (`Pilean/Polylog/Defs.lean`). For `s = 1` this is the statement
`BaileyFormula x c b B N a` of the degree-1 files:

* `baileyBlockDeg_one`: the block of degree 1 is `BaseB.baileyBlock`;
* `hasBaileyValueDeg_one_iff`, `baileyFormulaDeg_one_iff`: the two statement forms agree.

The formulas of degree 2 are in `Degree2Base64` ((30), (32)), `Degree2Base16` (the definition of
Catalan's constant, (29), (31), (33)) and `Degree2Base3` ((76), (77)); the plan for the others
is `literature/bailey-compendium/DEGREE2_PLAN.md`.
-/

@[expose] public section

namespace PiFormula

namespace Compendium

open Polylog

/-- For `s = 1` the block of degree `s` is the block of the degree-1 files. -/
theorem baileyBlockDeg_one (b B N : ℕ) (a : Fin N → ℚ) :
    baileyBlockDeg 1 b B N a = BaseB.baileyBlock b B N a := by
  funext j
  simp only [baileyBlockDeg, BaseB.baileyBlock, pow_one]

theorem hasBaileyValueDeg_one_iff {b B N : ℕ} {a : Fin N → ℚ} {x : ℝ} :
    HasBaileyValueDeg 1 b B N a x ↔ HasBaileyValue b B N a x := by
  rw [HasBaileyValueDeg, baileyBlockDeg_one, HasBaileyValue]

/-- **Degree 1.** `BaileyFormulaDeg x c 1 b B N a` is `BaileyFormula x c b B N a`. -/
theorem baileyFormulaDeg_one_iff {x c : ℝ} {b B N : ℕ} {a : Fin N → ℚ} :
    BaileyFormulaDeg x c 1 b B N a ↔ BaileyFormula x c b B N a := by
  simp only [BaileyFormulaDeg, BaileyFormula, hasBaileyValueDeg_one_iff]

end Compendium

end PiFormula
