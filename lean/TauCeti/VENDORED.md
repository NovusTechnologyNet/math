# Vendored code: Tau Ceti

`TauCeti/` holds 25 modules copied unchanged from the Tau Ceti library
(https://github.com/TauCetiProject/TauCeti), fetched on 21 November 2026 from the `main`
branch, which was then at commit `b608709b45f23ccda55703d572b0adb1fdec30fd`. They are
the Bang-Zsigmondy theorem (`TauCeti/NumberTheory/PrimitivePrimeDivisors/`) and the
modules it imports.

License: Apache License 2.0, copyright the Tau Ceti contributors; the license text is
in `TauCeti/LICENSE`. Tau Ceti describes itself as an AI-written library downstream of
Mathlib; its proofs are checked by Lean like any other, and before vendoring every file
was scanned for code that runs at build time (`#eval`, `run_cmd`, `IO`, `initialize`,
`elab`, `macro`, `extern`, `unsafe`) and for `axiom` and `sorry`: there are none.

The result used is `exists_prime_orderOf_two_eq`: for `n ≥ 2`, `n ≠ 6`, some prime `p`
has `orderOf (2 : ZMod p) = n` (Bang 1886). Any changes needed to build against this
project's Mathlib version are listed below.

## Changes

None yet.
