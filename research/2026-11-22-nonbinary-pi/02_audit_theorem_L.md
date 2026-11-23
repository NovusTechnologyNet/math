# Audit of Theorem L (`no_pi_bailey`) and Theorem G (every base b >= 5)

Date: 22 November 2026, 22:10 to 22:50 local time. Auditor: an independent AI agent that
did not write any of the audited files. No web access was used. Lean 4.36.0, Mathlib
v4.36.0. All scratch files were in `lean/ScratchAudit/`, which has been deleted; the
statements of the scratch lemmas are in the appendix.

Audited statements:

- `PiFormula.BaseB.no_pi_bailey` (`lean/Pilean/BaseB/NoPi.lean`, lines 109-121)
- `PiFormula.BaseB.Unconditional.eq_zero_of_hasSum_mul_pi` (`lean/Pilean/BaseB/TheoremG.lean`,
  lines 54-57)

## Verdict

Both theorems say what the documentation says, and I found no gap.

- The two Lean statements are faithful formal versions of the documented claims. The
  hypothesis of `no_pi_bailey` is satisfiable (in base 3 even with q = 0 and c != 0), the
  conclusion is not trivial (it fails in base 2, and it fails for B = 0), and `HasSum` is
  the ordinary sum of the series here.
- Both depend on `propext`, `Classical.choice`, `Quot.sound` and nothing else. This was
  confirmed three ways: `#print axioms`, an independent walk over the 65891 constants the
  theorem depends on, and a re-check of the whole dependency cone (66736 declarations,
  including the Mathlib part and the imported proof of Baker's theorem) by the external
  type checker nanoda, which reported no errors.
- No `sorry`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, `opaque`,
  `elab`, `macro`, `run_cmd`, `#eval` or kernel-weakening option anywhere in `Pilean/`,
  `Baker/` or `TauCeti/`.
- `KummerHom`, `SizeCond`, `GoodPrimesB`, `BakerTheorem` are not hypotheses of the final
  theorems; each is proved on the full range where it is used.
- 620 integer-relation searches in bases 3, 5, 6, 7, 9, 10, 12, 15, 18 found no formula for
  a rational multiple of pi; the same program finds the known formulas in bases 2, 4, 16
  and the known zero relations and pi sqrt(3) formulas in base 3.

There is no finding of severity A or B. There are four of severity C (documentation) and
several of severity D.

Note on a moving target: `notes/pi_formula_theorem.md`, `README.md` and `lean/README.md`
were edited by someone else at 22:31, 22:44 and 22:47, during the audit (Part VII gained a
"two-way form", references to `Sharpness.lean`, `NegativeBase.lean`, `TermsPerBit.lean`, a
paragraph on searches at every step and two remarks). Line numbers below are those of the
files at 22:50. Those three Lean files are not imported by `NoPi.lean` and were outside
the audit; I gave them a light check only (section 5).

## Findings

### Severity A (the theorem is wrong or vacuous)

None.

### Severity B (weaker than documented)

None.

### Severity C (documentation claims more than the Lean statement)

C1. One series, not a combination of series. `notes/pi_formula_theorem.md` line 1794:
"Theorem L answers Comment (10) for every integer base". Comment (10) of Borwein, Borwein
and Galway, as quoted in `research/2026-11-22-nonbinary-pi/01_literature.md` line 152, asks
whether pi is a linear combination of the L(1, b^m, n, j) "with b (and perhaps n) fixed",
that is, over several m and n at once. `no_pi_bailey` (and `bailey_pi_iff`,
`terms_per_bit`) speak of ONE series P(1, b^B, N, a). That a rational combination of
finitely many such series of the same base, with different (B, N), is again one series
P(1, b^B', N', a') is true and elementary (a series of step n is a series of step n m; take
a common step and period; it is Lemma 8 and Theorems 9, 10 of the 2004 paper according to
`01_literature.md` line 146), but it is not formalized. The same remark applies to every
sentence of the form "no degree-1 BBP-type formula ..." (`lean/README.md` line 97, header
of `NoPi.lean`) if "formula" is read as a combination. Suggested fix: either state the
closure lemma in Lean, or say "a series P(1, b^B, N, a)" in those sentences and mention
the reduction.

C2. `README.md` line 47 (row Theorem G), status "Lean, unconditional", and
`notes/pi_formula_theorem.md` lines 1575-1583 and 1586-1588:
- "A relation exists for b = 2, 3, 4 only": the "only" half is Theorem G. The existence of
  a relation in base 4 is not in Lean (the note says "a computation finds", line 1587). I
  reproduced it numerically: class F_4 has exactly one zero relation of period 6,
  rho(1..6) = (-1, 6, 2, 6, -1, 0), and a formula for pi sqrt(3), and no formula for pi.
- "a number has at most one formula" and "non-zero values are transcendental": in Lean
  these exist only with explicit hypotheses, `eq_of_hasSum_of_goodPrimesB` and
  `transcendental_of_hasSum_of_goodPrimesB` (`lean/Pilean/BaseB/Classification.lean` lines
  307 and 407, both take `(hB : BakerTheorem)` and `(hG : GoodPrimesB b)`), and
  `transcendental_of_isFBValue` (line 390, takes `hB`). There is no restatement without
  hypotheses in `TheoremG.lean`. Both hypotheses are theorems (`bakerTheorem`,
  `goodPrimesB hb`), and I checked that the one-line applications compile with the three
  standard axioms (appendix, `eq_of_hasSum_uncond`, `transcendental_uncond`). So the
  mathematics is covered; the named unconditional theorems do not include these two.

C3. Meaning of "exactly the powers of 2" (`notes/pi_formula_theorem.md` lines 1703-1709,
`README.md` line 48). At my first reading (22:20) the converse half was prose only; the
22:31 revision cites `bailey_pi_iff` and `bailey_int_pi_iff`, which do state it (light
check: they exist, are up to date, compile, standard axioms). What a reader should be told:
the equivalence holds because the exponent B is free (`exists B N c q, ...`). It is not
true that every power of 2, taken as Bailey's base itself, has a formula: numerically there
is no P(1, beta, N, a) = q pi for beta = 2, 4, 8, 32 with N <= 20 (and the sub-series
lemma explains why for 2, 4, 8); base 16 has one at N = 8. The Lean proof takes B = 4.
The 22:47 revision of the note says this itself (lines 1765-1770, "Two remarks"), so for
the note this finding is settled; the row of `README.md` (line 48) does not carry the
remark.

C4. "in any integer base" for the terms-per-bit bound (`notes/pi_formula_theorem.md` lines
1131 and 1814, `README.md` line 37): `terms_per_bit` (`lean/Pilean/BaseB/TermsPerBit.lean`
line 229) is stated for a natural number b >= 2. There is no version for `baileyBlockInt`
(negative bases). Outside the audited scope; noted because the sentence is in Part VII.

### Severity D (cosmetic, hygiene, tooling)

D1. `autoImplicit` is on. `lean/lakefile.toml` lines 6-10 set `relaxedAutoImplicit = false`
but not `autoImplicit = false`, and Lean's default is `true` (checked:
`theorem foo : n + 0 = n := rfl` compiles under the project options). So a mistyped
single-letter variable in a statement would silently become a new universally quantified
variable. It has no effect on the audited results: the elaborated statements have exactly
the binders written in the source (section 1), and the 30 files I recompiled, all 20 of
`BaseB` in the import closure of `NoPi.lean` among them, compile unchanged with
`-DautoImplicit=false`. Suggested fix: add `autoImplicit = false` to `[leanOptions]`.

D2. `lean/README.md` line 92: "`intRel_eq_zeroB` (no relation on the four roots, b >= 4)".
In Lean `intRel_eq_zeroB` needs `5 <= b` and `GoodPrimesB b` (`Classification.lean` line
96); the lemma for `4 <= b` is `unitB_zpow_eq_one` (`ClassificationAux.lean` line 384).
Likewise `notes/pi_formula_theorem.md` line 1648, "Step 3 works for every b >= 4", is prose:
the assembled step is stated in Lean for b >= 5 only.

D3. `notes/pi_formula_theorem.md` lines 1112-1114 and 1129: the Lemma of Part IV includes
"and the remaining terms sum to zero"; `subseries_of_kummerHom` (`Subseries.lean` line 282)
states only that the sub-series has the value q pi. The rest is one subtraction.

D4. `README.md` lines 51-56: "restate the theorems with no hypothesis
(`PiFormula.Unconditional.*`)". For Theorems G and L the statements without hypothesis are
in `PiFormula.BaseB.Unconditional` and `PiFormula.BaseB`.

D5. Titles "every integer base" (`README.md` line 48 before the revision, note line 1693):
`no_pi_bailey` has `b : Nat`, `2 <= b`. Negative bases are in `NegativeBase.lean` since the
revision (light check only).

D6. File times in the future. `lean/Pilean/Base3/Dimension.lean`, `GoodPrimes.lean`,
`Halves.lean`, `PiTheorem.lean` and their build outputs carry modification times of
23 November 00:28 to 01:25, two to three hours after the time of the audit. Lake compares
content hashes, so the build is not affected; a comparison by time is unusable.

D7. `lean/Baker/Basic.lean` lines 50-58: the docstring describes Baker's original proof and
says its lemmas "will be formalized in subsequent files"; the proof actually goes through
the Schneider-Lang criterion (`Baker/Reduction.lean`), and `Baker/Setup.lean` is not used
by the theorem at all. Vendored text, harmless.

D8. `lean/Pilean/BaseB/Reindex.lean` lines 145-154: `isFBValue_of_hasSum_subseries` has an
unused hypothesis `hb : 2 <= b`, with the linter switched off for that declaration. This is
the only `set_option` in `BaseB`; the other three in the project are `maxRecDepth` (twice)
and `maxHeartbeats 0`. None weakens checking.

D9. Tooling, not the project. (a) `leanchecker` with more than one module argument ends in
a segmentation fault on this machine (also with three small modules); with one module per
call it passes on all 82 modules. (b) `lean4lean` from the toolchain cannot read the
project's `.olean` files ("incompatible header") and was not used. (c) nanoda's pretty
printer shows the binders of Theorem G as `{b hb N : Nat}`; Lean's own printout has
`{b : Nat}, 5 <= b -> {N : Nat}`. (d) The parameter `B` of `no_pi_bailey` is redundant
(the statement for (b, B) is the statement for (b^B, 1)); harmless.

## 1. Statement faithfulness

Ran `#check` and `#print` with `set_option pp.explicit true` (`lake env lean`):

    no_pi_bailey : forall {b B N : Nat}, 2 <= b -> (forall (k : Nat), b != 2 ^ k) -> 0 < B ->
      0 < N -> forall (c : Fin N -> Rat) {q : Rat},
      HasSum (baileyBlock b B N c) (Rat.cast q * Real.pi) (SummationFilter.unconditional Nat)
      -> q = 0

    Unconditional.eq_zero_of_hasSum_mul_pi : forall {b : Nat}, 5 <= b -> forall {N : Nat},
      0 < N -> forall {rho : Nat -> Rat}, (forall k, rho (k + N) = rho k) ->
      forall {gamma : Real}, IsAlgebraic Rat gamma ->
      HasSum (seriesTermB b rho) (gamma * Real.pi) (SummationFilter.unconditional Nat) -> rho = 0

    baileyBlock b B N a j = sum over i : Fin N of
      Rat.cast (a i) / (Nat.cast b) ^ (B * j) / Nat.cast (N * j + Fin.val i + 1)
    seriesTermB b rho k  = Rat.cast (rho k) / (Nat.cast b) ^ (k / 2) / Nat.cast k
    seriesTermBN b n rho k = Rat.cast (rho k) / (Nat.cast b) ^ (k / n) / Nat.cast k

Reading:

- `baileyBlock b B N c j` is exactly block j of Bailey's P(1, b^B, N, c): `Fin.val i` runs
  over 0..N-1, so the denominators are N j + 1, ..., N j + N, and `c i` is Bailey's
  c_(i+1). The power is taken in the reals after the cast of b; `B * j` and `N * j + i + 1`
  are natural numbers with no subtraction. `k / 2` and `k / n` are floor divisions. The
  term at k = 0 of `seriesTermB` is 0 (division by zero), checked by `simp`. `2 ^ k` is in
  Nat. The topology on the reals is the standard one, the sum is over Nat with the
  unconditional filter, `Real.pi` and `HasSum` are Mathlib's (no local declaration shadows
  any Mathlib name; nanoda prints the same names fully qualified).
- (c) `HasSum` is the ordinary sum. Scratch lemmas (appendix): for b >= 2, B >= 1, N >= 1 the
  block series is summable (`summable_baileyBlock`), `HasSum f x <-> tsum f = x`, and
  `HasSum f x <->` the partial sums `sum_{j < n} f j` tend to x (`hasSum_iff_tendsto`). So
  the theorem says: the limit of the partial sums is never q pi with q a non-zero rational
  (`no_pi_partial_sums`).
- (a) Numerical evaluation of the definition, literally, at 60 digits (python, mpmath):

      BBP  b=16 B=1 N=8, c=(4,0,0,-2,-1,-1,0,0): 3.14159265358979323846...  diff from pi -6.2e-61
      same with b=2 B=4, and b=4 B=2:           diff -6.2e-61
      (-1/4)^k formula as b=16, N=8, c=(2,2,1,0,-1/2,-1/2,-1/4,0): diff 3.1e-61
      base 3 relation 130 (b=3,B=6,N=12): -2.9e-61;  relation 131: -9.2e-62
      Gregory P(1,9,4,(6,0,-2,0)) - pi*sqrt(3): -1.2e-60

- (b) Non-vacuity in Lean (appendix): `hypothesis_satisfiable` proves that every hypothesis
  of `no_pi_bailey` holds at b = 3, B = 6, N = 12, c = `Base3.rel130` (not zero), q = 0.
  `base_two_counterexample` proves that the conclusion fails at b = 2, B = 12, N = 24
  (Huvent's formula, q = 128), and `base_pow_two_counterexample` at b = 2^k for k | 12. So
  the hypothesis "not a power of 2" cannot be dropped. `0 < B` cannot be dropped either:
  P(1, 1, 4, (1,0,-1,0)) = pi/4 (numerically 0.0 at 30 digits).
- Mutation test. In a copy of `NoPi.lean`: replacing the use of `h2` at line 114 by `omega`
  fails there ("omega could not prove the goal"); removing `h2` from the statement fails at
  line 114 ("Unknown identifier h2"); removing `NotPerfectPower` from `rat_mul_pi_step`
  fails at line 69. The unmodified copy compiles. So "not a power of 2" is used exactly at
  `NoPi.lean` line 114, to show that the root a (b = a^j, a not a perfect power) is not 2;
  a is not 4 because 4 is a perfect power; hence a = 3 or a >= 5 (lines 113-116), which is
  what Theorem C3 (base 3) and Theorem G (base >= 5) need.

## 2. Axioms and gaps

    $ lake env lean ScratchAudit/Axioms.lean
    'PiFormula.BaseB.no_pi_bailey' depends on axioms: [propext, Classical.choice, Quot.sound]
    'PiFormula.BaseB.no_pi_bailey_ten' depends on axioms: [propext, Classical.choice, Quot.sound]
    'PiFormula.BaseB.Unconditional.eq_zero_of_hasSum_mul_pi' depends on axioms: [propext, Classical.choice, Quot.sound]
    'PiFormula.BaseB.Unconditional.mul_pi_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
    'PiFormula.bakerTheorem' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Transcendental.baker' depends on axioms: [propext, Classical.choice, Quot.sound]
    'PiFormula.BaseB.kummerHom' / 'sizeCond' / 'goodPrimesB': the same
    'PiFormula.Base3.Unconditional.not_isF3Value_rat_mul_pi': the same

Further checks:

- Sources match the build. `lake build Pilean.BaseB.NoPi --no-build` (a query, it builds
  nothing): "All targets up-to-date (18513 jobs)", exit code 0, no "sorry" in the replayed
  logs. In addition 30 source files were compiled again from source with
  `lake env lean -DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false -DautoImplicit=false`:
  all 20 `BaseB` files in the closure, `PiFormula/Baker`, `BakerBridge`, `Unconditional`,
  `Base3/Series`, `PiValue`, `PiTheorem`, `Unconditional`, `Base5/Defs`, `Classification`,
  `Unconditional`. All exit 0 with no error.
- Own dependency walk (a Lean meta program over the environment): 65891 constants reachable
  from `no_pi_bailey`; axioms among them: `Quot.sound`, `Classical.choice`, `propext`; no
  unsafe or partial constant; opaque constants only `Lean.opaqueId` and
  `String.Internal.append` (Lean core). The theorem uses 81 local modules: 18 of `Baker`,
  13 of `TauCeti`, and 50 of `Pilean` (11 `Base3`, 6 `Base5`, 20 `BaseB`, 13 `PiFormula`).
- External kernel. `leanexport Pilean.BaseB.NoPi -- no_pi_bailey
  Unconditional.eq_zero_of_hasSum_mul_pi no_pi_bailey_ten` wrote 9606481 lines (514 MB) with
  exactly 3 axiom records. `nanoda_bin` (version 0.4.17, permitted axioms: the three) printed
  the statements back and ended with "Checked 66736 declarations with no errors" in 57 s.
- `leanchecker` (kernel replay of a module's declarations): exit code 0 for each of the 81
  modules and for `Baker.Setup`, one module per call.
- Text search over every `.lean` file of `Pilean/`, `Baker/`, `TauCeti/`, `scripts/` for
  `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, `opaque`,
  `ofReduceBool`, `trustCompiler`, `skipKernelTC`, `autoImplicit`, `bv_decide`, `csimp`,
  `addDecl`, `run_cmd`, `#eval`, `initialize`, `elab`, `macro`, `syntax`, `open Lean`,
  `Lean.Elab`, `Lean.Meta`, `unseal`, `partial def`: the only hits are three comments
  (`PiFormula/Rank.lean` line 360 "opaque", `PiFormula/TheoremA.lean` line 9 and
  `PiFormula.lean` line 5 "no sorry"). `set_option`: four lines in all (D8). `decide +kernel`
  occurs in 19 files; it is checked by the kernel and adds no axiom. One
  `attribute [instance]` in `Baker/Setup.lean` line 80 (a `Fintype` instance; that file is
  not used by the theorem).
- Dependencies: `lake-manifest.json` pins Mathlib to `fc4f59e5...` (tag v4.36.0) and the
  other eight packages; every checkout under `.lake/packages/` is at the pinned commit with
  a clean working tree (`git status --porcelain`: nothing). The Baker proof is not a package:
  it is the local library `lean/Baker/` (19 files, 7385 lines, by Michail Karatarakis,
  Apache License 2.0, see `lean/Baker/README.md`).
- The statement of the imported theorem (`lean/Baker/Basic.lean` lines 83-86):

      theorem baker [Fintype i] {l : i -> Complex} (hl : forall i, IsAlgebraic Rat (exp (l i)))
          (hli : LinearIndependent Rat l) {b0 : Complex} {b : i -> Complex}
          (hb0 : IsAlgebraic Rat b0) (hb : forall i, IsAlgebraic Rat (b i))
          (hrel : b0 + sum i, b i * l i = 0) : b0 = 0 and forall i, b i = 0

  This is Theorem 2.1 of Baker's book, with the constant term: logarithms of algebraic
  numbers that are linearly independent over Q are, together with 1, linearly independent
  over the algebraic numbers. Not weaker, not stronger. The instances are the standard ones
  (checked with `pp.explicit`; `Rat.smul_def` applies). The project uses it as
  `BakerTheorem` (`lean/Pilean/PiFormula/Baker.lean` lines 42-47), where the independence
  is written with explicit sums `sum (q i : Complex) * lam i = 0 -> q = 0`; the bridge is
  `bakerTheorem_of_linearIndependent` (`BakerBridge.lean` line 23) and `bakerTheorem`
  (`Unconditional.lean` line 22). The file also derives the transcendence of pi and the
  Gelfond-Schneider theorem from it, both with the three axioms.

## 3. The interface statements

- Final statements: neither `no_pi_bailey` nor `Unconditional.eq_zero_of_hasSum_mul_pi` has
  a hypothesis of type `KummerHom`, `SizeCond`, `GoodPrimesB`, `HasGoodPrimeB` or
  `BakerTheorem` (printouts in section 1).
- Ranges. `kummerHom : 2 <= b -> NotPerfectPower b -> 0 < n -> KummerHom b n`
  (`Kummer.lean` line 144), used at `NoPi.lean` line 69 for exactly these b and n.
  `sizeCond : 6 <= b -> 3 <= m -> SizeCond b m` (`Size.lean` line 196), used at
  `GoodPrimes.lean` line 47 with m the order of r^2, which is >= 3 when r^4 != 1 (line 25).
  `goodPrimesB : 5 <= b -> GoodPrimesB b` (`GoodPrimes.lean` line 42): b = 5 from
  `goodPrimesB_five`, b >= 6 from the size condition. Base 3 goes through
  `Base3.Unconditional.not_isF3Value_rat_mul_pi`. `NotPerfectPower` comes from
  `exists_root_notPerfectPower` (`NoPi.lean` line 80).
- `SizeCond`, numerically (python, sympy and mpmath, 50 digits): no failure for
  6 <= b <= 130 and 3 <= m <= 240; the tightest case is (b, m, q) = (8, 6, 3) with
  Phi / (q (sqrt b + 1)^phi) = 1.296. At b = 5 the only failure for 3 <= m <= 240 is m = 6
  (ratio 1/1.496), as the note says. Edge cases: (6,3): 43 > 11.9, 3 does not divide 43;
  (6,4): 37; (6,6): 31; (6,5): 1555 = 5 * 311 and 5 * 141.6 = 708 < 1555; (7,3): 57 = 3 * 19
  and 3 * 13.29 = 39.9 < 57; (7,4): 50 and 2 * 13.29 = 26.6 < 50; (7,6): 43. The six
  exceptional triples of the proof and whether q divides Phi_m(b) are as stated in
  `Size.lean`.
- `KummerHom`, by computation (sympy `primitive_element`: d = [Q(zeta_M, c) : Q(zeta_M)],
  c = b^(1/n); the statement needs n1 | d, n1 = n/2 for even n and n for odd n): true in
  all 120 cases b in {2, 3, 5, 6, 7}, n in {1, 2, 3, 4}, M in {1, 3, 4, 6, 8, 12}, including
  the degenerate ones (b = 3, n = 4, M = 12: d = 2; b = 2, n = 4, M = 8: d = 2). For perfect
  powers it fails: (b, n, M) = (8, 3, 1): d = 1, n1 = 3; (4, 4, 8): d = 1, n1 = 2;
  (9, 4, 12): d = 1, n1 = 2.
- `KummerHom` in Lean (appendix): `kummerHom_two : KummerHom b 2` holds for every b (eta is
  1, the statement has no content for n <= 2), and `not_kummerHom_eight_three :
  not (KummerHom 8 3)`. So the statement has content and is false, hence unusable, for a
  perfect power; `kummerHom` rightly asks for `NotPerfectPower b`, and `no_pi_bailey` passes
  to the root a before using it.
- The sub-series lemma, numerically: in (b, n, P) = (2, 4, 16) the search finds one zero
  relation and one formula for pi, in (3, 4, 24) two zero relations; all are supported on
  the multiples of n1 = 2, as the lemma requires.

## 4. Search for a counterexample

Program: for a base b, a step n and a period P with n | P, the class sums
U_i = sum_j b^(-(B j + floor(i/n))) / (P j + i), i = 1..P, B = P/n. An integer relation
among U_1..U_P and pi is a rational relation among the series P(1, b^B, P, .) and pi. mpmath
`pslq`, repeated after removing one term of each zero relation found, so that a relation
with pi cannot hide behind zero relations. Precision 226 to 300 digits; coefficient bound
10^8 for P <= 12 and 10^6 for P <= 24; every relation found was re-evaluated at 900 digits.
`pslq` stopped each time with "Could not find an integer relation. Norm bound" above the
coefficient bound, not by running out of steps.

- Power test: (b, n, P) = (2, 2, 8), (4, 4, 8), (16, 8, 8) return the 1995 formula;
  (2, 2, 24) returns a formula and 5 zero relations (Bailey's table: 5); (3, 2, 12) with
  target pi sqrt(3) returns a formula and 2 zero relations; (9, 4, 4) returns the Gregory
  series.
- Search: bases 3, 5, 6, 10, 12, every (n, P) with n | P and P <= 24 (84 pairs each), and
  bases 7, 9, 15, 18 with P <= 16 (50 pairs each): 620 searches, 0 relations with pi.
- Zero relations found: only base 3 at (2, 12), (2, 24), (4, 24), two each, and base 9 at
  (4, 12), two (the same class). My own derivation from 1 - zeta_12/sqrt(3) =
  zeta_12^(-1)/sqrt(3) gives the relation (-243, 405, 0, 81, 27, 72, 9, 9, 0, 5, -1, 0) for
  P(1, 729, 12, .), which is `rel130 - rel131` of `Base3/Bailey.lean`.
- Theorem G, spot check: class F_b, periods 4, 6, 8, 12, b in {5, 6, 7, 8, 9, 10, 16, 25,
  27}: no relation at all. Base 4: one zero relation and a pi sqrt(3) formula, no pi (C2).
- Consistency with known formulas: base 16 and the (-1/4)^k formula are base 2^4; base 3
  has pi sqrt(3) only, and sqrt(3) is not rational; no contradiction.

## 5. Docs versus code

Compared: `notes/pi_formula_theorem.md` Part VI section "Every base b >= 5: Theorem G"
(lines 1566-1663) and Part VII (lines 1693-1816); `README.md` rows Theorem G and Theorem L
(lines 47-48). Sentences that claim more than the audited Lean statements are C1 to C4 and
D2 to D5 above. Everything else I compared agrees with the code, in particular:

- Theorem L as stated at lines 1699-1701 is `no_pi_bailey` word for word; base 10 is
  `no_pi_bailey_ten`; "the same for every step" (lines 1718-1720) is `rat_mul_pi_step`.
- Theorem G at lines 1568-1573 is `Unconditional.eq_zero_of_hasSum_mul_pi`; perfect squares
  are included (b is any natural number >= 5); gamma is a real algebraic number.
- Rational multiples only for Theorem L (line 1803): correct, q : Rat.
- The proof sketch (lines 1722-1749) names the lemmas that the Lean proof uses.
- The size condition paragraph (lines 1626-1631) agrees with `Size.lean` and with my
  numbers.
- The two remarks added at 22:47 (lines 1765-1770) agree with what I found independently:
  the Kummer statement fails for b = 8, n = 3 and b = 9, n = 4 (section 3), and the literal
  bases 2, 4, 8 have no formula with B = 1 (C3). The paragraph before them (lines
  1751-1763, 2434 searches by `python/basebn_explore.py`) was not re-run by me.

Light check of the three files cited by the 22:31 revision (not in the audit scope: they
are not imported by `NoPi.lean`): `Sharpness.lean`, `NegativeBase.lean`, `TermsPerBit.lean`
are up to date (`lake build ... --no-build`: "All targets up-to-date"), the first two
compile from source with `-DautoImplicit=false`, `leanchecker` passes on all three, and
`bbp_formula`, `exists_bailey_pi_of_two_pow`, `bailey_pi_iff`, `no_pi_bailey_int`,
`bailey_int_pi_iff`, `terms_per_bit`, `terms_per_bit_attained` depend on the three standard
axioms. Their statements match the revised sentences (two-way form: for an integer beta
with |beta| >= 2, a series with value q pi, q a non-zero rational, exists for some B, N >= 1
if and only if |beta| is a power of 2; `baileyBlockInt` is `baileyBlock` with the base cast
from Int). I did not read their proofs, export them, or test them numerically.

## What was NOT checked

- The proof of Baker's theorem was not read for understanding (7385 lines). Trust in it is
  trust in the kernel: Lean's kernel at build time, `leanchecker` per module, and nanoda on
  the whole cone. I did not compare `lean/Baker/` or `lean/TauCeti/` with their upstream
  repositories (no web), so the "changes made" lists in their READMEs are unverified.
- Nothing was rebuilt from scratch (`lake build` was off limits). Freshness rests on Lake's
  hash check and on recompiling 30 of the 132 files in the import closure.
- Mathlib was not re-checked as a whole; the part the theorem uses was (nanoda).
- The literature statements in Part VII (what the 2004 paper and the Compendium say) were
  not checked.
- The numerical search is finite: nine bases, periods up to 24 (16 for four of the bases),
  coefficients up to 10^6 or 10^8. It cannot find a relation with larger coefficients.
- `KummerHom` was tested only in small cases (n <= 4, M <= 12).
- `Sharpness.lean`, `NegativeBase.lean`, `TermsPerBit.lean`: light check only. `LogBase.lean`,
  `LogSelf.lean`, `LogNonValue*.lean`, `SubseriesLog.lean` and Theorem M: not looked at.
- Parts I to V of the note, the python programs of the project and the engine.
- Whether the committed git history has the same sources as the working tree.

## Appendix: the scratch lemmas (statements; all compiled, three standard axioms)

File `ScratchAudit/Sanity.lean`, imports `Pilean.BaseB.NoPi` and `Pilean.Base3.Bailey`.
ASCII transcription; `Nat`, `Rat`, `Real` are the usual number types.

    summable_baileyBlock (hb : 2 <= b) (hB : 0 < B) (hN : 0 < N) (c : Fin N -> Rat) :
        Summable (BaseB.baileyBlock b B N c)
      -- (hasSum_bailey_iff hb hB hN hN rfl c _).2 applied to
      -- (summable_seriesTermBN hb hN (Nat.mul_pos hB hN) (stepPat_periodic b N hB hN c)).hasSum

    hasSum_iff_tsum ... : HasSum (baileyBlock b B N c) x <-> tsum (baileyBlock b B N c) = x
    hasSum_iff_tendsto ... : HasSum (baileyBlock b B N c) x <->
        Tendsto (fun n => sum j in range n, baileyBlock b B N c j) atTop (nhds x)

    no_pi_partial_sums (hb : 2 <= b) (h2 : forall k, b != 2 ^ k) (hB : 0 < B) (hN : 0 < N)
        (c : Fin N -> Rat) {q : Rat} (hq : q != 0) :
        not (Tendsto (fun n => sum j in range n, baileyBlock b B N c j) atTop (nhds (q * pi)))

    hypothesis_satisfiable :
        2 <= 3 and (forall k : Nat, 3 != 2 ^ k) and 0 < 6 and 0 < 2 * 6 and Base3.rel130 != 0
        and HasSum (BaseB.baileyBlock 3 6 (2 * 6) Base3.rel130) ((0 : Rat) * pi)
      -- baileyBlock 3 B n a = Base3.baileyBlock3 B n a (funext; simp), then Base3.relation130

    base_two_counterexample :
        exists (c : Fin (2 * 12) -> Rat) (q : Rat), q != 0 and
          HasSum (BaseB.baileyBlock 2 12 (2 * 12) c) (q * pi)
      -- c = huvent1, q = 128, from PiFormula.huvent1_formula
    base_pow_two_counterexample (hk : k * B = 12) :
        exists c q, q != 0 and HasSum (BaseB.baileyBlock (2 ^ k) B (2 * 12) c) (q * pi)

    eq_of_hasSum_uncond (hb : 5 <= b) ... : rho = rho'
      := eq_of_hasSum_of_goodPrimesB bakerTheorem hb (goodPrimesB hb) hN hN' hrho hrho' h h'
    transcendental_uncond (hb : 5 <= b) ... (hrho0 : rho != 0) (h : HasSum (seriesTermB b rho) x) :
        Transcendental Rat x
      := transcendental_of_hasSum_of_goodPrimesB bakerTheorem hb (goodPrimesB hb) hN hrho hrho0 h

    halfIfEven 1 = 1, halfIfEven 2 = 1, halfIfEven 3 = 3, halfIfEven 4 = 2, halfIfEven 6 = 3  (decide)
    kummerHom_two (b : Nat) : KummerHom b 2          -- eta = 1, the inclusion map
    cB_eight_three : cB 8 3 = 2
    not_kummerHom_eight_three : not (KummerHom 8 3)  -- sigma 2 = 2, but should be zeta_3 * 2
