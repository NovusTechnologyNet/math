# Every step n in every base b: probes, the sub-series lemma for a general base, the statement

22 November 2026. Numerical probes and a check of a paper proof. No Lean in this pass: the Lean
files for the same statements (lean/Pilean/BaseB) were being written by others at the same time
and are not assessed here. Written in one sitting, reviewed by nobody. Program:
python/basebn_explore.py (new; its docstring gives the method and the guard).

## 1. The question

    F_(b,n) :  S(rho) = sum over k >= 1 of rho(k) b^(-floor(k/n)) / k,   rho rational and periodic.

Every degree-1 BBP-type formula sum_j b^(-B j) sum_{i=1..N} a_i/(N j + i) is such a series
(section 5). Two inputs come from elsewhere: Statement G (Part VI of the note: for b >= 5 and
n = 2, S(rho) = gamma pi with gamma algebraic forces rho = 0; machine-checked for b = 5, in
progress for b >= 6) and Theorem C3 (b = 3, n = 2: gamma pi is a value exactly for gamma in
Q sqrt(3); machine-checked). Claim tested: **a series of some F_(b,n) is a non-zero rational
multiple of pi only if b is a power of 2.**

## 2. What was run

- Probe A (no theory): integer relations among pi and the P class sums
  S_j = sum over k = j (mod P) of b^(-floor(k/n))/k. A relation is a rational pattern of period
  P with value in Q pi (0 included). For the bases 3 and 9 the target pi sqrt(3) was added.
- Probe B: integer relations among 2 pi i and the N numbers Log(1 - r/b^(1/n)), r^N = 1. By
  Baker's theorem and Galois descent its rank is the dimension of the rational patterns of
  period N whose value is an algebraic multiple of pi (0 included), for n | N.
- Guard: the lattice sees the values at Wc bits (A: 28 bits per number + 256; B: 30 per number
  + 300, two real coordinates); a reduced row counts as a relation only if it vanishes with 300
  (A) or 400 (B) more bits. Each run prints a certificate: every integer relation with sum of
  |coefficients| below the bound lies in the span of those found.
- `table OUT 20 144`: bases 3, 5, 6, 7, 10, 12, steps n = 1, 2, 3, 4, 6, periods: every multiple
  of n up to 60 (up to 100 for base 10) and 72, 84, 96, 120, 144 (also 80, 100 for base 5); bases
  9, 4, 8 at P = 12, 24, 48, 72. Both probes: 2200 runs, lattice dimension up to 146. `jobs`:
  base 10 at larger periods (3.2); steps 5, 8, 12 for the bases 5, 7, 10; base 2 as a control.
  In all 2434 runs, 28600 s of LLL. `selftest` (all ok), `kummer`, `reduce`: sections 4, 5.

## 3. Results

### 3.1 Table

"A", "B": ranks of the two probes; "new": the part of B not constant on the cosets of the n1'-th
roots of unity, i.e. not coming from step 2 or 1. Smallest certificate bounds over the standard
set: A 2^24, B 2^58 (sum of |coefficients|).

| b | n | periods | A | pi in A | B | new | what it is |
|---|---|---|---|---|---|---|---|
| 5, 6, 7, 10, 12 | 1, 2, 3, 4, 6 | the standard set: 1760 runs | 0 | no | 0 | 0 | nothing at all |
| 5, 7, 10 | 5, 8, 12 | multiples of n to 60; 72, 96, 120, 144 | 0 | no | 0 | 0 | nothing at all |
| 3 | 1, 3 | 65 and 25 periods, to 144 | 0 | no | 0 | 0 | nothing |
| 3 | 2 | 35 periods, to 144 | 3 if 12 divides P; 1 if 4 divides P; else 0 | no; pi sqrt(3) yes | as A | 0 | G, Z1, Z2 of Theorem C3 |
| 3 | 4 | 20 periods, to 144 | 3 if 24 divides P; 1 if 8 divides P; else 0 | no; pi sqrt(3) yes | 5 if 24 divides P; 1 if 8 divides P | 2 if 24 divides P | step 2 on even k; two new series on odd k (3.3) |
| 3 | 6 | 15 periods, to 144 | 3 if 36 divides P; 1 if 12 divides P; else 0 | no; pi sqrt(3) yes | 5 if 36 divides P; 3 if 12 divides P | 2 if 12 divides P | step 2 on 3 divides k; two new series (3.3) |
| 9 | 4 | 12, 24, 48, 72 | 3 | no; pi sqrt(3) yes | 3 | 0 | F_(9,4) = F_(3,2) |
| 9 | 1, 2, 3, 6 | 12, 24, 48, 72 | 0 | no | 0 | 0 | parts of F_(3,1) and F_(3,3) |
| 4 | 2 | 12, 24, 48, 72 | 1 | no | 2 | 0 | F_(4,2) = F_(2,1): one zero series; pi sqrt(3) |
| 4 | 4 | 12, 24, 48, 72 | 1, 6, 6, 6 | YES | 3, 8, 8, 8 | 0 | F_(4,4) = F_(2,2): the BBP formula |
| 4 | 6 | 12, 24, 48, 72 | 0, 0, 0, 1 | no | 2, 2, 2, 4 | 2 | F_(4,6) = F_(2,3): pi sqrt(3) 2^(1/3), 2^(2/3) |
| 8 | 3 | 12, 24, 48, 72 | 1 | no | 2 | 0 | F_(8,3) = F_(2,1) |
| 8 | 6 | 12, 24, 48, 72 | 1, 6, 6, 6 | YES | 3, 8, 8, 8 | 0 | F_(8,6) = F_(2,2) |
| 4, 8 | other n | 12, 24, 48, 72 | 0 | no | 0 | 0 | |
| 2 (control) | 3 / 4 / 6 | 36, 72 / 48, 96 / 72 | 1 / 6 / 8 | no / YES / YES | 4 / 12 / 16 | 2 / 4 / 8 | A as in outside_family_findings.md |

In every run with a relation, each relation splits into its parts on the classes k = u
(mod n1'), each part a relation by itself: the support is as the lemma of section 4 predicts (a
relation with pi or pi sqrt(3) lives on n1' | k; the other parts carry neither). For the perfect
powers the split modulo n1 itself fails where n1' < n1 (b = 9, n = 4; b = 4, n = 4; b = 8, n = 3
and 6): this is the correction of section 4.

### 3.2 Base 10

No relation of any kind in any run. Both probes, steps 1, 2, 3, 4, 6: every period that is a
multiple of n up to 100, then 120 and 144 (468 runs; bounds 2^24 and 2^59). Probe A also at
P = 160 and 200 (n = 1, 2, 4), 180 and 240 (n = 1, 2, 3, 4, 6): rank 0; bounds 2^24, 2^22, 2^23,
2^21 (lattice dimension 241, 7004 bits at P = 240). Probe B also at N = 160 and 200 (n = 2, 4),
180 (all five steps) and 240 (n = 2): rank 0, bounds 2^58, 2^56, 2^57, 2^54. Steps 5, 8, 12:
rank 0 in both probes (64 runs). In all 558 runs for base 10. So in this range base 10 has no
series for a rational multiple of pi, none for an algebraic multiple of pi, and none with sum 0.

### 3.3 Found on the way: base 3 has new series at steps 4 and 6

As base 2 has at steps 3, 4, 6. Checked by direct summation to 48 digits (`selftest`):

    2 pi 3^(1/6)  =  sum over j >= 0 of 9^(-j) ( 9/(12j+1) - 3/(12j+4) - 3/(12j+7) - 3/(12j+10) ),
    2 pi 3^(5/6)  =  S(rho), rho = (0,27,0,0,9,0,0,9,0,0,-9,0) of period 12 in F_(3,6),
    pi sqrt(2) 3^(1/4) = S(rho), rho of period 24 in F_(3,4), on odd k: 6,-6,2,12,2,-6,6,-2,-12,-2
                         at k = 1,5,7,9,11,13,17,19,21,23;   and one more for pi sqrt(6) 3^(1/4).

So in base 3, for n >= 4, gamma pi occurs for some gamma outside Q sqrt(3); these gamma lie
outside every cyclotomic field, as the lemma requires. Not looked up in print (no web here).

### 3.4 What the searches can and cannot show

- A run shows: at that period, no integer relation with sum of |coefficients| below the printed
  bound, other than those found. Nothing about larger coefficients, other periods, other steps
  or other bases. It is evidence, not proof. Probe A uses no theory; the reading of probe B
  uses Baker's theorem. mpmath (values) and python-flint (LLL) are trusted.
- For scale: the relations found in the bases 2, 3, 4, 8, 9 have sum of |coefficients| at most
  241 in probe A (coefficients at most 18) and at most 33 in probe B (exponents at most 7); the
  bounds are at least 2^21 (A) and 2^54 (B) in every run.

## 4. The sub-series lemma for a general base

K = the field of all roots of unity; c = b^(1/n) > 0; b = a^j with a not a perfect power;
n1 = n/2 (n even) or n (n odd); n1' = n1 / gcd(n1, j). So n1' = n1 when b is not a perfect power.

**Lemma.** Let rho be rational and periodic and S(rho) = gamma pi with gamma algebraic. Then
gamma lies in K(c) = sum over u mod n1' of K c^u (a direct sum), and for every u the sub-series
over k = u (mod n1') has the value gamma_u pi, gamma_u the component of gamma in K c^u. In
particular, if gamma is in K (for instance rational), the sub-series over the k divisible by
n1' has the value gamma pi and the other terms sum to 0.

*Proof, with b in place of 2.* Take a period P of rho with n | P and 4 | P.
(1) b^(-floor(k/n)) = c^(k mod n) c^(-k), so S(rho) = - sum over r^P = 1 of d_r Log(1 - r/c)
with d_r = (1/P) sum_k rho(k) c^(k mod n) r^(-k), in E = Q(zeta_P, c).
(2) Baker's theorem: the relations with algebraic coefficients among i pi and the Log(1 - r/c)
are spanned by those with rational coefficients. So (-i gamma; d) = sum_j x_j (eps_j; e_j) with
rational relation vectors; no relation involves i pi alone, so the e_j are independent and the
x_j, hence gamma, lie in E.
(3) Degree. Let m be the least positive integer with c^m in K. Then K(c)/K is cyclic of degree
m and the conjugates of c over K are the eta c with eta^m = 1 (Kummer theory; K contains the
roots of unity). Now c^m = a^(jm/n), and for s/t in lowest terms a^(s/t) generates Q(a^(1/t)), of
degree t over Q because a is not a perfect power (X^t - a is irreducible: a is no p-th power,
and a > 0 is not -4y^4); this real field is normal over Q only for t <= 2, and every subfield of
K is normal. So c^m is in K exactly when n divides 2jm, and m = n/gcd(n, 2j) = n1'.
(4) For eta^(n1') = 1 take an automorphism h of the algebraic numbers, the identity on K, with
h(c) = eta c. Then h(d_r) = d_(r/eta), because eta^(k mod n) = eta^k (n1' divides n); these are
the coefficients of the pattern eta^k rho(k). Applying h to (2): S(eta^k rho) = h(gamma) pi
(h fixes i). On K c^u, h multiplies by eta^u. Average eta^(-u) S(eta^k rho) over eta. QED.

**Checked, point by point.**
- Irreducibility of X^n1 - c^n1 over K for b not a perfect power: this is (3) with j = 1. By
  Capelli's criterion directly: c^n1 is b or sqrt(b); it is a p-th power in K only if b^(1/p) or
  b^(1/2p) is in K, which needs p = 2 and c^n1 = b; but then n1 = n is odd. Correct.
- The case 4 | n1 (the condition "not -4y^4"): over K it is empty, because -4 = (1+i)^4 is a
  fourth power in K, so "-4y^4" means "a fourth power", already excluded by "not a square". The
  note's sentence is right; the condition needs no separate argument.
- A second route to (3) without Capelli (sketched in the docstring of Pilean/BaseB/Kummer.lean,
  read here as a paper argument): with d the degree of c over Q(zeta_M), n | M, the constant term
  of the minimal polynomial gives c^d in Q(zeta_M); a positive real number of an abelian field
  with a rational n-th power has a rational square; so n divides 2dj. Same conclusion.
- h(d_r) = d_(r/eta) needs eta^n = 1 and n | P. Both hold.
- **No gap found for a base that is not a perfect power.**

**The correction: perfect powers.** For b = a^j the lemma holds with n1' = n1/gcd(n1, j). The
proof gives the statement with n1 only when gcd(n1, j) = 1, and otherwise the statement with n1
is false in general. Counterexamples (in `selftest`, by probe A and by direct summation):
b = 9, n = 4 (c = sqrt(3) is in K, n1' = 1): the zero series Z1 of base 3 is a series of F_(9,4),
and its part on even k, (0,1,0,0,0,4,0,3,0,4,0,0) as a pattern of base 3, has a positive sum.
b = 8, n = 3 (c = 2): the zero series log(3/4) = log(3/2) + log(1/2), pattern (1,-3,-2,-3,1,0)
of F_(2,1), has a non-zero part on the multiples of 3. b = 4, n = 4: the BBP formula; its terms
with even k are all negative. For a square b = a^2: n1' = n1 when n1 is odd and n1/2 when n1 is
even. None of this hurts the final statement: a formula in base a^j is a formula in base a
(with B replaced by jB), and the lemma is applied in base a.

**Which class in base a.** With g = gcd(j, n): F_(a^j, n) is the part of F_(a, n/g) supported on
the multiples of j/g, by rho'((j/g) k) = (j/g) a^(floor(j (k mod n)/n)) rho(k). Examples:
F_(9,4) = F_(3,2); F_(8,3) = F_(2,1); F_(16,8) = F_(2,2); F_(4,6) = F_(2,3); F_(27,2) = the part
of F_(3,2) on 3 | k. When j and n share the factor g the step drops from n to n/g.

**Numerical checks.** `kummer 12 240`: for 19 bases (2, 3, 5, 6, 7, 10, 12, 18, 72 and ten
perfect powers), every n <= 12 and every multiple M of n up to 240 (14117 triples), the degree of
b^(1/n) over Q(zeta_M) is n/gcd(n, 2j) when the conductor of Q(sqrt(a)) divides M and n/gcd(n, j)
otherwise: upper bound by construction, lower bound certified by a prime p = 1 (mod M) for which
b^((p-1)/n) has that order modulo p (a Frobenius argument, rigorous). The doubtful cases:
b = 12, n = 4: degree 2 = n1 (12^(1/4) is not in K although sqrt(12) is); F_(12,4) has no
relation, so there the lemma is tested only through the degree. b = 9, n = 4 and b = 8, n = 3:
degree 1, and the lemma with n1 fails as said. The lemma is confirmed on all 70 runs of probe A
that found a relation (bases 2, 3, 4, 8, 9), and on the components pi sqrt(3) 2^(1/3) (on
k = 1 mod 3) and pi sqrt(3) 2^(2/3) (on k = 2 mod 3) of F_(2,3).

## 5. The reduction "Bailey formula -> step n"

With g = gcd(B, N), n = N/g, m = B/g: sum_j b^(-B j) sum_i a_i/(N j + i) = S(rho) in F_(b,n),
rho(m (N j + i)) = m b^(floor(B i/N)) a_i, period m N, zero off the multiples of m; because
floor(m (N j + i)/n) = B j + floor(B i/N). Conversely a series of F_(b,n) of period P is the
Bailey formula with base b^(P/n) and N = P. `reduce`: the two sides agree to 50 digits on the
BBP formula (n = 2), the example of Part IV (n = 3) and eight random cases in the bases 3, 5, 6,
7, 10, 12 (largest difference 9e-58); the map of section 4 agrees on 16 pairs (b, n) (6e-62).

## 6. The final statement

**Statement.** For an integer b >= 2 the following are equivalent.
(a) There are integers B, N >= 1, rational a_1, ..., a_N and a rational q, not 0, with
    sum over j >= 0 of b^(-B j) sum_{i=1..N} a_i/(N j + i) = q pi.
(a') Some series of some class F_(b,n), n >= 1, has the value q pi with q rational, not 0.
(b) b is a power of 2.

*Proof from the inputs.* (a) and (a') are the same by section 5. (b) => (a): the BBP formula,
with its terms grouped j at a time, is a formula in base (2^j)^4 (checked for 4, 8, 32).
(a') => (b): write b = a^j, a not a perfect power, so a = 2, a = 3 or a >= 5. The series is a
series of some F_(a, n0). By the lemma in base a (n1 = n0/2 or n0) its sub-series over n1 | k
has the value q pi, and in the index k/n1 it is a series of F_(a,2) (of F_(a,1), inside F_(a,2),
for odd n0). For a >= 5 Statement G gives q = 0; for a = 3 Theorem C3 gives q in Q sqrt(3), so
q = 0.

**Which multiples of pi.** The same proof gives more than rational q. Let gamma be a real
algebraic number that lies in a cyclotomic field (rational, q sqrt(m), cos(2 pi/m), ...). If a
series of F_(b,n) has the value gamma pi, then gamma = 0 when b is not a power of 2 or 3, and
gamma is in Q sqrt(3) when b is a power of 3 (attained for every power of 3). For an arbitrary
algebraic gamma the proof gives only this: gamma is in K(c), its component in K is as just said,
and for a >= 5 the pattern vanishes on the multiples of n1'. **Not excluded by the proof:**
gamma = (cyclotomic number) * b^(u/n) with u not divisible by n1', and series with sum 0
supported off the multiples of n1'. Such series exist in base 2 (pi sqrt(3) 2^(1/3)) and in
base 3 (2 pi 3^(1/6), section 3.3). For b = 5, 6, 7, 10, 12 and the steps tested, probe B found
none; that is evidence only. For n <= 2 and b >= 5 Statement G excludes them.

**Status of the inputs.** Baker's theorem: formal proof, imported. Theorem C3: machine-checked.
Statement G: machine-checked for b = 5 (Theorem C5); for b >= 6 the note has a plan of proof,
marked as not reviewed, and a Lean proof was in progress. The lemma for a base that is not a
perfect power: paper proof, checked here, no gap; Lean in progress. The reductions: elementary,
checked numerically here. So today the statement is proved on paper modulo Statement G for a >= 6.

**"Base b" means base b^B for some B.** With the literal base beta of Bailey's P(1, beta, N, A)
the answer is narrower: by the lemma a formula for pi with beta = 2^m needs a pattern of F_(2,2)
of period 2m that carries pi, and probe A (`sums 2 2 P`, P = 2, 4, ..., 40) finds one exactly
when 4 | m: beta = 16, 256, ... have a formula, beta = 2, 4, 8, 32, 64 none (computed only).

## 7. Limits of the statement

- **Degree 1 only.** Terms a_i/(N j + i). Nothing is said about formulas of degree >= 2
  (polylogarithmic). In print pi^2 has a degree-2 formula in base 3 (compendium, formula 76).
- **Rational coefficients.** Needed: pi = 2 sqrt(3) sum (-1/3)^k/(2k+1) is a base-3 series of
  degree 1 with the coefficient sqrt(3) (it is S(G)/sqrt(3)).
- **Integer base.** Kristensen and Mathiasen have formulas for pi with rational coefficients in
  the irrational bases 1 + sqrt(3) and the golden ratio (file 05 of the base-5 research folder).
- **Periodic coefficients.** Zudilin's base-5 series (arXiv 2409.10097) has integer coefficients
  given by a recurrence, not periodic; it is outside the class.
- **Not a statement about computing digits.** It says that one mechanism, a degree-1 BBP-type
  formula in the base, is absent outside the powers of 2. Decimal digits of pi are computed
  individually by other series (Plouffe, Bellard, Gourdon; cost about n^2, as recorded in
  notes/outside_family_findings.md), and no lower bound for the n-th digit is proved.

## 8. In print, as far as the repository records it

From research/2026-11-22-base5/00_summary.md and 05_pi_other_bases_claims.md; no new lookup.
- Borwein, Borwein and Galway (Canad. J. Math. 56, 2004), Theorem 7: for a base b > 2 that is
  not a proper power, pi has no Machin-type formula (rational combinations of the series of
  arctan(b^(-m))). A narrower class: no series in sqrt(b), no general periodic pattern. Only
  the abstract was read.
- Bailey's compendium words this more broadly (no degree-1 BBP-type formula for pi except in
  bases that are powers of two) and attributes it to that paper; MathWorld adds that it does
  not rule out a different scheme; Zudilin (2024) calls other bases open.
- No source found states a degree-1 formula with rational coefficients for pi in an integer base
  that is not a power of 2, and none proves non-existence for the whole degree-1 class.
  MathSciNet and zbMATH were not searched. "Not found" is weak evidence.
- Values 0 or transcendental: Adhikari, Saradha, Shorey and Tijdeman (2001).
So section 6 is to be presented as an extension of the theorem of Borwein, Borwein and Galway:
from Machin-type formulas to all degree-1 formulas, and to perfect powers.

## 9. Not verified

- Statement G for b >= 6: here only the probes speak (rank 0 everywhere).
- The lemma: checked by one reader. The Lean files were not compiled or read as proofs.
- For b >= 5 and n >= 3: algebraic multiples outside cyclotomic fields, and zero series.
- Periods above 144 (above 240 for base 10 in probe A), other steps, other bases, and relations
  with coefficients above the bounds.
- The program: tested by its `selftest`, on known relations of the bases 2 and 3 only.
- The literal-base remark and the new base-3 series: computed; no proof, no literature check.
