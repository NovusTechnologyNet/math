/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.PiFormula
public import TauCeti.NumberTheory.PrimitivePrimeDivisors.Zsigmondy

/-!
# Bang's theorem

Bang (1886): for `N ≥ 2`, `N ≠ 6`, some prime `p` has `orderOf (2 : ZMod p) = N`. The proof
is the vendored Tau Ceti library (lean/vendor/README.md); this file only connects it to
the statement `PiFormula.BangTheorem` used in Theorem A.
-/

@[expose] public section

namespace PiFormula

theorem bang : BangTheorem := fun _ hN h6 => TauCeti.exists_prime_orderOf_two_eq hN h6

end PiFormula
