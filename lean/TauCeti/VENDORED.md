# Vendored code: Tau Ceti

`TauCeti/` holds 25 modules copied unchanged from the Tau Ceti library
(https://github.com/TauCetiProject/TauCeti), fetched on 24 November 2026 from the `main`
branch, which was then at commit `4db95028a48e52f7e46e0222e6879f6c2a03b7ff`. They are
the Bang-Zsigmondy theorem (`TauCeti/NumberTheory/PrimitivePrimeDivisors/`) and the
modules it imports: exactly the import closure of the two modules this project imports,
`TauCeti.NumberTheory.PrimitivePrimeDivisors.Zsigmondy` and
`TauCeti.NumberTheory.PrimitivePrimeDivisors.Cyclotomic`.

License: Apache License 2.0, copyright the Tau Ceti contributors; the license text is
in `TauCeti/LICENSE`. Tau Ceti describes itself as formal mathematics implemented and
maintained by AI contributors, with roadmaps directed and reviewed by people; its proofs
are checked by Lean like any other. Before each copy every file was scanned for code that
runs at build time (`#eval`, `run_cmd`, `IO`, `initialize`, `elab`, `macro`, `syntax`,
`extern`, `unsafe`, `implemented_by`), for `axiom`, `sorry`, `native_decide`, `opaque`
and `set_option`, and for hidden Unicode control characters: there are none. The files
import only Mathlib modules and each other.

The results used:

* `exists_prime_orderOf_two_eq`: for `n ≥ 2`, `n ≠ 6`, some prime `p` has
  `orderOf (2 : ZMod p) = n` (Bang 1886);
* `exists_prime_orderOf_eq`: for `a ≥ 3` and `n ≥ 3`, some prime `p` has
  `orderOf (a : ZMod p) = n`;
* the homogeneous cyclotomic polynomial `homogeneousCyclotomic` and its lemmas.

## Versions

Upstream at that commit builds on Lean v4.37.0-rc1. Here the 25 files compile without any
change on Lean 4.36.0 with Mathlib v4.36.0, and `#print axioms` of the results above gives
`propext`, `Classical.choice`, `Quot.sound` and nothing else (checked 24 November 2026).

## History

* 21 November 2026: first copy, from commit `b608709b45f23ccda55703d572b0adb1fdec30fd`.
* 24 November 2026: refreshed to commit `4db95028a48e52f7e46e0222e6879f6c2a03b7ff`. Ten
  files had changed upstream. `GroupTheory/OrderOfElement/Cauchy.lean` is new in the import
  closure. `NumberTheory/PrimitivePrimeDivisors/Multiplicity.lean` left this copy, because
  nothing here imports it; upstream still has it. Upstream renamed or removed five
  declarations of the files kept here; this project used none of them.

## Changes

None: every file is identical to upstream's at the commit above (the git blob hashes are
equal).
