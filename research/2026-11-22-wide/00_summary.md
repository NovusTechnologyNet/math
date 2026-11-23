# Wide research pass of 22 November 2026: synthesis of wave 1

The 31 reports of wave 1 in this folder (P01-P13 and F3 on pi, Q01-Q10 on primes, R01-R07 beyond) were read in full, with
`00_RULES.md`, `README.md` and the summaries of `../2026-11-22-nonbinary-pi`, `../2026-11-22-log-primes` and
`../2026-11-22-general-step`. No web access was used here. Marks are the reports' own: [READ], [SNIPPET], [INFERRED], and
[COMPUTED] / [MEASURED] where a helper ran something. Many [READ] are readings through a fetch tool that returns a digest of
the page, as the reports say. [INFERRED-S] marks a conclusion added by this synthesis. "Not found" is weak evidence
throughout. Results are named as in `README.md`; "Theorem N" is the paper result of the log-primes summary (in a base
b >= 5, b != 9, no log n with n >= 2 an integer is a value). Three wave-2 reports (W2_Q12, W2_Q14, W2_Q18) were already in
the folder; they are not part of this synthesis and are named only where they settle a doubt.

## 1. Search totals

As each report's search log states. "Usable" is the report's own figure, or attempted minus the failures it counts.
Conventions differ: P04, P09, P13, Q03, Q09, R03 count page reads as endpoint queries; Q04, R02, R04 count search
endpoints only (their page reads, about 34, 13 and 45, are extra).

| Report | WebSearch | Endpoint attempted | Usable | Note |
|---|---|---|---|---|
| P01 nonexistence, novelty | 4 | about 95 | about 75 | about 25 were archive requests for Compendium versions |
| P02 higher degree | 4 | 64 | about 44 | |
| P03 algebraic bases | 2 | 52 | about 36 | |
| P04 digit extraction | 6 | 106 | about 55 | search endpoints proper: about 47 |
| P05 normality | 4 | 62 | about 44 | |
| P06 Machin | 2 | 42 | 35 | |
| P07 series conjectures | 4 | 75 | about 50 | |
| P08 transcendence | 3 | 40 | 29 | |
| P09 pi in provers | 4 | about 65 | about 45 | |
| P10 continued fractions | 3 | 48 | about 36 | |
| P11 zero relations | 6 | 50 | about 46 | |
| P12 logs, arctans | 4 | 46 | 34 | |
| P13 computation | 5 | 70 | about 42 | |
| F3 rational bases | 4 | 78 | 66 | |
| **Pi (P and F3)** | **55** | **about 893** | **about 637** | P alone: 51 and about 815 |
| Q01 primitive divisors | 5 | about 71 | about 50 | |
| Q02 Aurifeuillian | 2 | 46 | 35 | |
| Q03 unique primes | 3 | 82 | 74 | |
| Q04 primes in provers | 5 | about 50 | about 43 | |
| Q05 Erdos problems | 1 | 54 | about 42 | batches of problem pages counted once |
| Q06 Chowla, Erdos | 1 | about 76 | about 65 | |
| Q07 prime records | 6 | 93 | about 76 | |
| Q08 explicit estimates | 6 | 49 | 43 | |
| Q09 special primes | 4 | 63 | about 58 | |
| Q10 primes and pi | 3 | 55 | about 40 | |
| **Primes (Q)** | **36** | **about 639** | **about 526** | |
| R01 Baker corollaries | 4 | about 85 | about 70 | |
| R02 other constants | 6 | 37 | about 23 | usable is my count of its log; it gives none |
| R03 AI and mathematics | 6 | 62 | about 50 | |
| R04 publication routes | 6 | 38 | about 21 | |
| R05 cyclotomic relations | 2 | 77 | about 56 | |
| R06 finite problems | 6 | 64 | about 45 | |
| R07 Lerch sums | 5 | about 55 | about 25 | |
| **Beyond (R)** | **35** | **about 418** | **about 290** | |
| **All 31 reports** | **126** | **about 1950** | **about 1453** | about 2076 searches attempted, about 1580 usable |

Rate limits. Every report met HTTP 429 from the arXiv API and Semantic Scholar (often from the first call) and from OpenAlex
after 3 to 20 calls (retry delay about 18 hours); GitHub code search always answered 401, zbMATH's web pages 403. No report
records a WebSearch cap error. Coverage was weakened most in P07 (says its forward citations are thin), Q10 (no citation
chasing at all), R07 (ASST and Saradha-Tijdeman unread), R04 (most publisher pages blocked), R02 (Chamberland's paper not
fetched), P08 (half the calls refused), P04 (Gourdon unread), P02 and P03 (a third of the queries lost), R06 (every arXiv
API and OpenAlex query failed). Q05 and Q06 used one WebSearch each. Several reports note that OpenAlex responses carried a
notice asking an agent to request an API key with an e-mail address; all ignored it.

## 2. Novelty and overlap

### 2.1 What is in print, result by result

- **Theorem L (pi iff |b| is a power of 2).** Cite: Borwein-Borwein-Galway 2004 (BBG), Theorem 7 (Machin-type only; Bang's
  theorem and Z[i], no Baker) and Comment 10, which poses the general case [READ P01, P03, P12, R02; checked in the
  nonbinary-pi summary]; Bailey's Compendium, which states it as shown [READ]; the BBP preprint (1995/97), section 6: PSLQ
  found no formula for bases 2..128 other than powers of 2, and J. P. Buhler "has reported a proof" that such an identity
  forces the base 2^K [READ by P04, preprint only]; Bailey-Crandall 2001 (base 10 asked) [READ P05]; Zudilin 2024 (calls it
  open) [READ P01, P04, P13, R02]; Lagarias 2001, Theorem 5.3, and ASST 2001 for the first use of Baker on such series (0
  or transcendental only) [READ Lagarias; ASST unread]. No report found a proof of the full statement or a counterexample.
  Threats: the Buhler report (2.2, item 1); a 2026 Zenodo "dissertation" by D. A. Kulik on a classification of binary
  digit-extraction formulas and a "reduction to S-unit search" [SNIPPET P01, unread].
- **Theorems M and N (logarithms).** Nearest: BBG Example 4 (no Machin-type formula for ln b in base b when M_b = 0, so
  none for ln 10; for any ln n "seems unlikely", not proved) and Example 5 (base 7) [READ P01, P12, R02]. Nobody states
  "iff b is a power of 2 or 3". The Compendium has base-10 and base-5 formulas for logarithms of non-integers (formula 84:
  log(9/10); 85-89) [READ P12, R02], so the statement must be about log n, n >= 2 an integer.
- **Theorem G (b >= 5), C5.** Not found anywhere (P01, P11, R05, R07). Nearest: Bailey's Table 1 (PSLQ counts; one
  non-binary row, base 3^6) [READ P11]; the dual theorem of Madritsch-Ziegler and Drungilas-Dubickas (m - zeta_k and
  n - zeta_k independent) [SNIPPET R05]; Bass 1966 and Ennola 1972 for alpha = 1 [READ / SNIPPET R05]; the Pade criteria of
  David, Hirata-Kohno and Kawashima, which by R07's evaluation need log b of order N log N (b >= 7.4 for N = 2, about 870
  for N = 4) [INFERRED from a garbled text layer]; ASST Theorem 4 as reported in Tijdeman's survey [READ survey]. The
  project's lemma on primes containing sqrt(b) - r is not a printed theorem; nearest are Postnikova-Schinzel 1968 [READ
  Q01] and Schinzel 1993 [SNIPPET].
- **Theorem C, Bailey's table, C3 in full.** Print has no dimension count and no structure theorem. The Compendium says the
  pattern of zero relations is not understood [READ P02, P11]; Barsky, Munoz and Perez-Marco ask whether all degree-1 null
  formulas come from their Theorem 1.1 [READ P02, P11]; BBG problem D(2) asks how many independent binary Machin-type zero
  relations exist [READ P06, P12]; Bailey-Crandall 2001 list a theory of "Ferguson anomalies" as open [READ P05];
  Kristensen-Mathiasen (K-M) recover 1 of 5, 1 of 3 and 1 of 2 known relations [READ P11]; Lafont (2011, unrefereed) proves
  eight relations one by one [READ via digest]. Bailey's counts agree with the project where compared.
- **Theorems E, F, E3, J (terms per bit).** No lower bound of any kind in print; Bellard's 1997 page asks whether a faster
  formula exists [READ P04]. Bellard and Euler 1779 (per Craig-Wood 2023) stand at 0.7 [READ / SNIPPET]. Huvent's page
  could not be read. Of Takahashi (Ramanujan J. 51, 2020) the helpers saw only the catalog abstract ("about 20% fewer
  terms") [SNIPPET P13]; that is the 64 against 80 of `notes/pi_formula_theorem.md` [INFERRED-S]. y-cruncher accepts one
  Chudnovsky run plus a BBP-type run at the matching hexadecimal offset [READ P13].
- **Theorems G (log 23), H, K, K3, K5.** Cite the BBP paper, section 5 (Pomerance: 23 is not a quotient of numbers
  2^a - 1; Harley: 29, 37 by Aurifeuillian factors) [READ P04]; BBG Theorem 4 (log 23, log 89: no non-Aurifeuillian
  Machin-type formula) and Remark (i) [READ P12]; Chamberland 2003 (sufficiency only; log 23 "still unknown") [READ P12,
  Q03, Q09]; the Compendium's list (9) and its sentence that it is unknown whether all primes, or finitely many, qualify
  [READ]. No iff criterion in print in any base. Ternary: only 2, 3, 5, 7, 11, 13 (Lafont 2009; OEIS A165132, keyword
  "more") [READ P12]. The link to "unique primes" is in print only in pieces (Q03).
- **Theorem I.** BBG Theorems 1-2 already exclude 3/8, 5/8, 5/11, 9/16, 11/18 in the Machin-type class and leave 2/7, 4/9,
  5/9 open when Aurifeuillian generators are allowed; the Compendium (2023) still calls arctan(2/7) unknown [READ P12]. So
  for 5/8 cite BBG; 2/7 and 4/9 are the new cases; 5/9 is not in `README.md`.
- **Values 0 or transcendental.** Known: ASST 2001, Lagarias 2001 Theorem 5.3, and per a zbMATH review Bundschuh 1979
  [READ / SNIPPET: P01, R01, R02, R07]. Cite them; no novelty.
- **Rational base 3/2.** F3: the construction is in print with a real parameter (Adegoke 2010; Adegoke-Layeni 2013; K-M
  Theorem 1), but only integer or Pisot bases were written down. The base-3/2 formula for pi was not found. The base-4/3
  formula for pi sqrt(3) is in print: Adegoke-Layeni, Appl. Math. E-Notes 10 (2010), eq. (4.4), ratio -(3/4)^3 [READ on
  ar5iv, checked numerically]. P03 had called both new. No digit extraction is known for a non-integer base.
- **Baker's theorem, formal.** R01 [READ, local README]: the imported proof (Karatarakis) is the qualitative theorem with
  constant term, on an unmerged branch, announced in no paper; Karatarakis-Wiedijk (arXiv 2603.24823) treat
  Gelfond-Schneider only and name Baker as future work. Not in Mathlib (P08, R01).
- **Theorems A, B, D**: no thread addressed them. Nearest: Stormer's criterion and two-term theorem, Yamada's finiteness
  for three terms, Gasull-Luca-Varona 2023 [READ P06].

### 2.2 To verify before use, most important first

1. **Buhler's reported proof.** Only P04 saw it, in the preprint. If the printed paper (Math. Comp. 66, 1997) keeps the
   sentence, the statement of Theorem L was claimed in 1997, with no published proof, for the shape
   sum n^(-k) (a_1/(mk+1) + ... + a_m/(mk+m)). Read the printed text, cite it, and ask whether a proof was ever written. It
   changes the wording of Theorem L, not the mathematics.
2. **Q06's parity result on Erdos's +-1 conjecture** (a claimed new proof, [COMPUTED]): a 2-adic obstruction is said to
   settle every odd non-square q = 1 mod 4 up to 1000, including q = 105, which three recent papers call open. It is
   conditional on Okada's criterion as transcribed from Chatterjee-Murty 2015 (Proposition 2.1), was run once in Python,
   and has no proof for all q. Needed: the criterion in Okada's or Saradha-Tijdeman's own text, an independent
   implementation, then a proof. (W2_Q11.)
3. **What the K-M formulas are.** Their abstract says integer coefficients in Pisot bases; P03 [COMPUTED] finds the
   displayed coefficient vectors in Q(sqrt 3) minus Q and in a field of degree 4; F3, P04, R02 and the general-step summary
   (section 7, "rational coefficients") repeat the abstract. If P03 is right, no rational-coefficient formula for pi in an
   irrational base is known and the sentence that bounds Theorem L must change. P03 also reads Compendium formula (132) as
   rational coefficients in the base (2/phi)^10, with its constant garbled.
4. **Rational bases.** (a) Base 4/3 is Adegoke-Layeni's (F3 read the source; P03 did not). (b) "Only r^2 in {1/4, 1/3, 1/2,
   2/3, 3/4}" is a computation for single triangles with angle denominators up to 60; "iff a power of 3/2 or 4/3" is P03's
   conjecture; combinations of several terms are not covered. (c) The Borwein-Chamberland manuscript and Chan 2008 were not
   read.
5. **Aurifeuillian halves.** Q02 [COMPUTED, h < 40]: each half has a primitive prime except b = 2, n = 4, 12, 20 and b = 3,
   n = 6. The base-3 lemma of C3 (E >= 3) avoids n = 6 [INFERRED-S]; check the side conditions in base 2. Q02 adds that the
   statement is not Schinzel 1962 as Stewart quotes it (ab a square or twice a square, so not bases 3, 5); Schinzel's paper
   was not read. (W2_Q15.)
6. **Bailey's count 7 at (2^60, 120)** against the project's 8 (P11 asks). Reading: 8 is the pi-space and the zero
   relations are 7 [INFERRED, P11 and S]; confirm against the Lean statement. Table 1 counts rewritings and omits "larger"
   relations, so P11's remark that it has no row with N = 3e (hence that steps >= 3 are new) is [INFERRED] too.
7. **"First formal Baker" and provenance.** carlok/diaz-modulus-lean lists Baker, with no named declaration [READ P08; R01
   could not see the proof]. Tau Ceti's status file has Baker unproved (Q06) while its roadmap says most of it exists on
   Karatarakis's branches (R01). The vendored proof is one person's unannounced work: write neither "first" nor "ours", and
   ask the author before any publicity.
8. **Absence from Mathlib** rests on documentation pages and issue searches; code search was refused for everyone. Agreed
   by several reports: no Zsigmondy (PR 28895 closed 18 Sep 2026: Q01, Q02, Q04, Q05, P03), no BBP or digit extraction
   (P04, P09, P13), no Baker, Gelfond-Schneider or Lindemann-Weierstrass merged, no transcendence of pi (P08, P09, R01).
   One report each, weak: no dilogarithm (P02), no normal numbers (P05), no Euler product at s = 1, no density 6/pi^2
   (Q10), no convergence theory for generalized continued fractions (P10), no Mertens (PRs open: Q04, Q08, Q10), no Stormer
   (R06). Conflict: Pocklington "not in Mathlib" (Q04, which looked) against "Mathlib has such tools" (Q10, [INFERRED]).
9. **Lean BBP elsewhere.** P04 found none; P09 and P13 found metasecdev/math-proofs (pushed 16 Nov 2026): BBP identity,
   digit certificates to n = 10000 and an all-n guard from a Mahler-type measure, by its own README; nobody built it. Leads
   on verified digit extraction must be judged against it. (W2_P15.)
10. **P04's route "Baker gives an irrationality measure of pi"** is [INFERRED] with its own caution: the formal Baker is
    qualitative (R01) and P09 calls the measure a different theorem. The 2026 claims mu(pi) = 2 and mu(log r) = 2 are
    unrefereed [P08 read only that they exist].
11. **A104885.** P12: nine entries are not in Bailey's list; `README.md` says all pass except 38737, so name them as
    passing. Q03 [INFERRED]: the "infinite set of primes" of Adegoke, Oliver Lafont and Layeni (2016, section 6.1) are
    rationals, not primes; P12 repeats their phrase. Read the section.
12. **Counts from Pomerance 2025.** 296 periods up to 2^17 against 179 in OEIS A161508 is Q03's line count [INFERRED];
    primality there is by Baillie-PSW, not proved. (W2_Q16.)
13. **The Riemann hypothesis announcement of 20 November 2026** (Q04 [READ: the note, the Lean community statement,
    Sutherland's page]; R03 [READ, secondary]): a Lean-only development, certified by the Lean and Mathlib communities as a
    proof of Mathlib's statement, not refereed, no readable proof. Unresolved between sources: whether two checkers accepted
    or declined the export, and a critique about a predicate defined as True (R03, secondary, no rebuttal found). Do not
    cite it as proved; its library has no license.
14. **Misreadings to correct when quoting.** P06 gives BBG's abstract as "b = 2"; it is "b != 2" (P01, P02, P12). P04 names
    Magaud and Zimmermann, P09 and P13 name Rideau and Thery, for the same arXiv 1709.01743. P01 found Compendium
    title-page dates 2004, 2009, 2011, 2013, 2023 only, while P02 cites a "2006" and P03, F3 a "2017" version: cite the
    title-page date. "Somewhat mysterious" is Bailey's phrase for R02 and Barsky et al.'s for P11.
15. **Smaller [INFERRED] claims, not facts yet.** Q01: BBG question (7) follows from Bilu-Hanrot-Voutier. Q09:
    Gaussian-Mersenne norm primes are 1 mod 4p. Q05: the reduction of Erdos 307. P02: the b <= 4 heuristic for degree 2.
    R07: the Pade threshold table. P10: "no proof found" for 18/pi^2 and three e entries. P13: Gibbons's conjecture still
    open (its own check: 12000 terms). Q02: an erratum for OEIS A250197 (W2_Q14 recomputed it and found every term right).
    R04: arXiv's limit of two submissions a month (secondary source; its own step 5 says one) and "a cross-list needs no
    endorsement".

## 3. Published questions

### 3.1 Answered by the project (always: degree 1, rational coefficients, integer base)

| Where it is asked | Question | Answer |
|---|---|---|
| BBG 2004, Comment 10 | is pi a rational combination of the L(1, b^m, n, j)? | only for b a power of 2: Theorem L in that notation (`no_pi_L_comb`) |
| BBG 2004, Example 4 | does any ln n have a formula in a base with M_b = 0? ("failed to prove") | ln b: Theorem M. Every integer n >= 2, b >= 5, b != 9: Theorem N (paper) |
| BBG Remark (i), D(8); BBP 1997 sec. 5; Chamberland 2003 | an Aurifeuillian formula for log 23? | none in F (Theorem G); Theorem K decides every y |
| BBG D(11) | why Machin-type generators capture everything | Baker's theorem (P12, [INFERRED]); worth one sentence |
| BBG Examples 2-3; Compendium sec. 3 | arctan(2/7), arctan(4/9) | Theorem I; 5/9 remains |
| BBG D(2) | how many independent binary Machin-type zero relations? | likely read off Theorem C; the two classes must be compared first (P06, P12) |
| Compendium (zero relations); Bailey-Crandall 2001 (Ferguson anomalies) | why zero relations occur for some (b, n) only | degree 1: all of them in bases 2 and 3 (steps 1, 2), none for b >= 5 |
| Compendium sec. 2; OEIS A104885 | do all primes have a binary formula? | no (23); each prime is decided by Theorem K |
| Bailey-Crandall 2001 sec. 5; BBP 1997 sec. 6 | a BBP-type scheme for pi in base 10? | none of this class (Theorem L) |
| Lagarias 2001, sec. 6, Question | have all G-function BBP numbers expansions in two independent bases? | pi has not, within degree 1 (P05, [INFERRED]); the Question allows higher-order poles, so it is not settled as posed |
| Bellard 1997 | is there a formula faster than his? | within degree 1 Huvent's 2/3 is optimal (Theorems E, F) |
| Barsky et al. 2021, sec. 1 | "no base 3 formula for pi is known" | none exists in this class (C3, L) |
| Zudilin 2024 | BBP-type computation of pi in other bases? | excluded only for this class; his series (Gaussian base, recurrence coefficients) lies outside |

### 3.2 Not answered

- BBP 1997, section 7, questions 1-5 (decimal digits of pi, e, sqrt 2, log 2 in base 10, log 23 in base 2, as statements
  about the class SC): the absence of a formula is not the absence of an algorithm. Decimal digits of pi are extracted by
  Plouffe's and Bellard's prime-by-prime method (P04, Q10); no proof of its correctness or space bound was found.
- Whether the primes with a binary formula are finitely many (Compendium, A104885). Q03 reduces it to the infinitude of
  unique-type primes [INFERRED], which is open.
- Hypothesis A and normality (P05): every degree-1 value is a BBP number in Lagarias's sense, nothing more.
- Degree >= 2: the s >= 2 rows of Bailey's Table 1, pi^2 in other bases, Broadhurst's questions. Even the irrationality of
  Li_2(1/2) is open, so unconditional nonexistence is out of reach (P02).
- Non-integer bases: K-M's three problems (digits, the golden-ratio abundance, higher degree), Cloitre's octagon question,
  BBG D(7) and D(9) (Gaussian bases), Zudilin's question on quadratic extensions.
- BBG D(3), D(4), D(5), D(6); the question of Barsky et al. on null formulas (P11 expects a corollary).
- "e has no BBP-type formula": equivalent to an open problem on periods; provable from Schanuel only (R02).
- The project's own open items: steps n >= 3 for b >= 5 beyond multiples of pi in cyclotomic fields, uniqueness for 7/24,
  Theorem N in Lean. Outside the project: Erdos's +-1 conjecture, Gibbons's spigot conjecture.

## 4. Errors and overstatements in print

| # | Where | Evidence | How firm |
|---|---|---|---|
| 1 | Bailey's Compendium, introduction: BBG "showed" there is no degree-1 formula for pi outside powers of two | absent in the versions of 1 Mar 2004 and 15 Sep 2009, present 13 Feb 2011, 29 Apr 2013, 8 Apr 2023 [READ P01]; BBG prove the Machin-type case and pose the rest [READ P01, P04, P12, R02]. Mendonca (arXiv 1209.2348) repeats it; MathWorld is correct | firm about the citation; the statement itself is true (Theorem L) |
| 2 | Chamberland 2003, table; OEIS A104885: the prime 38737 | fails the criterion (Lean iff plus program); printed in Chamberland's list [READ P12, Q03, Q09], absent from Bailey's list (9); no erratum found | firm; W2_Q14 adds 433 * 38737 = Phi_72(2) |
| 3 | OEIS A104885 as a whole | a 46-term prefix of Chamberland's list ending at 312709 (so 524287 is missing); last edited 2012 [READ P12] | firm, minor |
| 4 | K-M 2023, abstract: "integer coefficients" | P03's computation (2.2, item 3) | open |
| 5 | Adegoke, Oliver Lafont, Layeni 2016, sec. 6.1: an "infinite set of primes" with binary formulas | Q03 [INFERRED] | soft; read first |
| 6 | BBG p. 924: number-field Zsigmondy "with effective bounds on the exceptional cases" (Schinzel 1974, Bilu-Hanrot-Voutier) | Q01 [INFERRED]: the second is over Q, the first gives only a threshold n0(d) | soft |
| 7 | Schinzel 1962 as quoted by Stewart: two primitive divisors of 2^n - 1 except n = 4, 6, 12 | Q02 [COMPUTED]: 2^20 - 1 has one (41) | arithmetic firm; whose slip is unknown |
| 8 | Luca-Stanica, two-term arctangent relations in powers of the golden section | a missed case, corrected by Gasull-Luca-Varona 2023 [READ P06] | firm (published correction) |
| 9 | Explicit prime estimates: a missing condition in FKS2; Johnston-Yang (x >= 2 should be x >= 23); a Schoenfeld-type interval claim on the TME-EMT wiki (false at x = 2010880); Ramanujan-inequality papers; Ramare-Saouter's range; BKLNW Table 8 | Tao's log of the Lean project [READ digest, Q08]; printed corrigenda of Cully-Hugill and Lee 2024, Faber-Kadiri 2018 | found by others; firm as reported |
| 10 | Tables resting on one computation: pi(10^27..29) (one code base), pi_2(10^19) (one contributor, corrected July 2026), OEIS A161508 (179 terms, 296 known) | [READ Q07; INFERRED count Q03]; A006880 was wrong at 10^23 until 2007 | not errors; candidates for checks |
| 11 | Slips: "seventeen" for 18 primes (Caldwell-Dubner, Table 1); "Mertens 1984" for 1874 (Kaneko); "Wrench" formulas not in Wrench 1938 (Yamada); stale Prime Pages entry on Gaussian-Mersenne primes; Wikipedia on Riesel candidates (41 or 42), AP-27 (2019 or 2026), PiHex cost | Q03, Q10, P06, Q09, R06, Q07, P04 | firm, trivial |
| 12 | Zudilin, arXiv 2409.10097 v1: digits of pi in bases 5 and 10 | withdrawn in v2 ("An obvious flaw") [READ P04] | firm; cite v2 |
| 13 | Unrefereed 2026 claims the reports met: Catalan's constant irrational (gap reported by Wachs), mu(pi) = 2, mu(log r) = 2, proofs of Erdos-Straus; Verger-Gaugry 2017 on Lehmer | P08, R06 | unknown; never cite as theorems |

## 5. Leads

Each: statement; what it needs; size; why noticed; risk. Sources in brackets.

### 5a. Extensions of the project's own theorems

- **A1 Theorem N and K_b in Lean.** For b >= 5, b != 9: no q pi + q' log n (q' != 0, n >= 2 an integer) is a value; log y is
  a value iff a power of y is a product of orbit numbers. Needs the four pieces of the log-primes plan. Days to weeks.
  Noticed: closes BBG Example 4 in full. Risk: low; phrase it for integers.
- **A2 Rational bases.** Conjecture [P03]: a non-zero algebraic multiple of pi has a degree-1 formula with rational
  coefficients in a base (p/q)^B, p/q not an integer, iff p/q is a power of 3/2 or 4/3; then: which multiples. Needs
  Zsigmondy for p^n - q^n, the primes above q, Baker, the Kummer argument. Days for a search with p, q <= 200 [F3], weeks
  for a proof. Noticed: K-M call non-integer bases unexplored; same shape as Theorem L. Risk: 2.2, items 3 and 4.
- **A3 Every step n for b >= 5.** The numbers 1 - zeta/b^(1/n), zeta over all roots of unity, are multiplicatively
  independent (with -1) for b >= 5 not a perfect power; hence no zero relation and no algebraic multiple of pi at any step
  [R05 L1, R07 L2; general-step section 6]. Needs a primitive-prime lemma for b^(1/n) uniform in zeta, not in print [Q01].
  Days to weeks. Noticed: an Okada-type criterion for geometric weights is missing in print [R07]; dual of
  Drungilas-Dubickas. Risk: perfect powers; relations between the families of b and of b^(1/n).
- **A4 Steps 3, 4, 6 in bases 2 and 3.** Exact dimensions and bases of the spaces, with the series for 2 pi 3^(1/6) and
  pi sqrt(2) 3^(1/4) of the general-step summary [P11 L1]. Days to 2 weeks. Noticed: nothing like it in Bailey's table as
  far as P11 saw. Risk: Adegoke's general-base papers were not read in full.
- **A5 The unique-prime dictionary.** A prime p has a binary formula iff p = 2, or p is the only primitive prime of some
  2^n - 1, or alone in an Aurifeuillian half; Theorem P of the log-primes summary is the base-b form [Q03 L3]. Days.
  Noticed: joins Chamberland's list to Yates's notion and restates the finite-or-infinite question. Risk: low.
- **A6 Arctangents.** An effective criterion for arctan(y/x) in bases 2 and 3; decide 5/9; prove that Bailey's 15
  arctangents are independent (a PSLQ observation in print); a table for denominators below 100 [P12 L3]. Days for the
  table, weeks for the criterion. Noticed: answers the Compendium and BBG. Risk: low.
- **A7 pi sqrt(d) and L(1, chi).** For each fundamental discriminant D, |D| < 200: is pi sqrt(|D|), or sqrt(D) log(eps_D), a
  value in base 2, in base 3? In print: -4, -3, -8, 8, 5 in base 2 and -3 in base 3 [R02 4.1]. Days to 2 weeks. Risk: a
  short list; R02 did not read Adegoke's papers in full.
- **A8 Two bases.** The set of y with log y a value in a base 2^k and in a base 3^k; for each prime q the bases in which
  log q is a value [P05 L4, R02 4.3]. Days to weeks. Noticed: a precise answer to Lagarias's Question for simple poles.
- **A9 Quadratic and Gaussian bases.** (i) The dimension of rational-coefficient formulas for pi in the bases phi,
  1 + sqrt 2, 1 + sqrt 3, N <= 30, by exact computation [P03 L2]: 1 to 3 weeks; settles 2.2, item 3. (ii) A Machin-type
  exclusion in Z[phi] or Z[i] from Carmichael and Bilu-Hanrot-Voutier [P03 L3, Q01 L1]: weeks; no number-field Zsigmondy
  is formal anywhere. Risk: high for (ii).
- **A10 Degree 2, conditional.** For each (b, N) the kernel of the symbol map on degree-2 sums, tested against the counts
  2, 1, 2, 2, 1, 2, 4 of Bailey's Table 1 [P02 lead A]. Days for a first run. Noticed if it explains the counts or
  predicts a formula. Risk: conditional on period conjectures; unconditional statements are out of reach.

### 5b. Formalization targets that others have asked for

- **B1 Chowla's problem.** Baker-Birch-Wirsing for prime q (f rational, periodic, f(q) = 0, f not zero: sum f(n)/n != 0)
  and the unweighted ASST theorem (the sum is 0 or transcendental; L(1, chi) transcendental). Asked: Tau Ceti's roadmap
  lists the Baker corollaries (items 7.1-7.3) [R01]; no formal version found [Q06, R01]. Needs Baker (in hand) and
  Mathlib's L(1, chi) != 0, characters, cyclotomic Galois groups, Abel's limit theorem. 2 to 4 weeks. Risk: neither
  helper read the 1973 paper.
- **B2 Baker corollary layer.** pi + log alpha, e^(b0) prod alpha_i^(b_i), independence of the logs of the primes,
  Gelfond-Schneider and Hermite-Lindemann as corollaries [P08 L1, R01 lead 2]. Asked: the same roadmap; Karatarakis and
  Wiedijk's future work. Days. Risk: it may already exist on Karatarakis's branches.
- **B3 Dusart 2018, Proposition 5.4c.** A prime in (x, x(1 + 1/log^3 x)] for 89693 <= x <= 360653: a finite check left as
  `sorry` in the Lean explicit-estimates project, blocking its lcm theorem [Q08 lead 1]. Days. Asked: by that project
  (now teorth/IEANTN). Risk: someone may have done it since (W2_Q13).
- **B4 Zsigmondy for Mathlib.** On Mathlib's 1000+ list with no declaration; the one PR was withdrawn [Q01, Q04, Q05]. But
  Tau Ceti merged a proof on 15 Nov 2026 and the project vendors that one, so there is less to give than Q04 and Q05
  assume [INFERRED-S]. New here would be the Kummer and number-field side.
- **B5 Erdos 1948 for the Palomar registry.** sum 1/(t^n - 1) is irrational for every integer t >= 2; stated in Formal
  Conjectures (Erdos 1049, a variant) with a non-registry link [Q05 lead 1]. Days to 2 weeks. Risk: off the subject.
- **B6 BBP digit extraction, total correctness.** Asked: Lipton 2010 ("make BBP an algorithm"); Bertot, Rideau and Thery
  prove partial correctness and call a verified digit printer worthwhile [P04, P09, P13]. Needs an irrationality measure
  of pi, which the formal Baker does not give. Weeks. Risk: 2.2, items 9 and 10.
- **B7 Prime statements on lean-eval** [Q04]: Brun's theorem (weeks; Mathlib has a Selberg-sieve frame), sign changes of
  the prime race mod 4, Pocklington and Proth certificates (days). Linnik, bounded gaps, effective Baker, Roth: too big.
- **B8 Missing, though nobody asked** [weak "not found"]: normal numbers with Lagarias's equivalence (P05); Euler's product
  for pi/4 at s = 1 (Q10, 2 to 6 weeks) and the density 6/pi^2 (days); Brouncker's fraction and the Ramanujan Machine
  identities proved by Yamamoto (P10); a WZ lemma with one 1/pi^2 series (P07); Stormer's criterion and two-term theorem
  (P06); the BBP, Bellard and Huvent identities as a small Mathlib file (P09). Chudnovsky's formula is wanted by Mathlib
  and lean-eval, and out of reach.

### 5c. Computations and certified tables

- **C1 Lists of primes with logarithm formulas.** Bases 2, 3, 5, 10 to a stated bound, each entry with its certificate; a
  correction of A104885 and an extension of A165132 (six terms now; the project has 31 below 10^6) [P12 L1, Q09 lead 1].
  Days. Noticed by OEIS editors and the Compendium's maintainer. Risk: the lists are program output, not Lean per prime;
  OEIS has rules on AI-assisted submissions (W2_Q14).
- **C2 Unique-prime tables.** Extend A161508 and relatives from 179 to about 296 terms from Pomerance's appendix; first
  tables for bases 3, 5, 6, 7, 12 (none found in OEIS) [Q03 L1, L2]. Days. Risk: probable primes; count unverified.
- **C3 The parity scan for Erdos's conjecture,** redone independently with a certificate per q, squares treated apart
  [Q06 L1, L3, L4]. Days. Noticed only if item 2 of 2.2 survives; then much.
- **C4 Machin census.** All minimal rational relations among pi and arctan(1/x), x <= 10^9, verified in Z[i] [P06 lead A].
  Days. Noticed: three-term formulas are known finite with no list; longer ones are open. Risk: only "complete below X".
- **C5 Zero relations beyond Bailey's table.** Exact counts for N up to 240 and for steps >= 3, compared with every row of
  Table 1 and with the CARMA list [P11 L2, L4, L6]. Days. Risk: counting conventions.
- **C6 pi(x).** Recompute pi(10^27) with current primecount (3 days to 2 weeks on 24 cores by Q07's estimate, memory
  unknown), or a formal ladder pi(10^n) in Lean (kernel to about 10^8 to 10^10) [Q07]. Noticed modestly. Risk: same
  algorithm family, so not an independent check.
- **C7 Small certified tables.** Aurifeuillian halves without a primitive prime (Q02); consecutive smooth numbers and
  S-unit solutions in Lean for small S (R06, none formal anywhere); Lean-checked primality of Gaussian-Mersenne norms and
  record objects (Q07, Q09; W2_Q18).

### 5d. Top ten across the three lists

1. A1: Theorem N in Lean. Nearly done; answers a printed "failed to prove".
2. C1: certified prime lists and the two OEIS entries. Days; visible; depends on nobody.
3. A3 with A4: every step n. Completes the classification in the project's own class.
4. A2: rational bases, after 2.2 items 3 and 4. New ground with the same method.
5. B1: Baker-Birch-Wirsing and unweighted ASST, formal. First of its kind; uses the formal Baker.
6. C3: recheck Q06's parity result. Cheap; decisive either way.
7. A5 with C2: the unique-prime dictionary and its tables.
8. A6: the arctangent criterion and table, with 5/9.
9. B3: Dusart 5.4c for the Lean explicit-estimates project. Days; a way into an active community.
10. A7 with A8: pi sqrt(d), L(1, chi) and the two-bases statement.

Before all of them: the write-up of Theorems L, M, G, N (P01 lead 1, R03 lead 1, R04 steps 1-5).

## 6. Presentation and publication

What R03, R04, P09, R01, P08 and Q05 report, with their marks.

- **Framing.** Present Theorem L as a machine-checked proof of a statement that a standard reference asserts and whose
  cited source proves only a special case; cite BBG's Comment 10, the Buhler sentence and Zudilin. Lead with what was not
  found in print: G, M, N, C with Bailey's counts, E, K. Say "degree 1, rational coefficients, integer base; not a
  statement about computing digits" every time. [R03, P01]
- **Do** [R03 READ: the Leiden Declaration of 2 June 2026, Tao's FAQ, Boldt; R04 READ: the Lean "did you prove it" page]: a
  short explanation in the author's own words; a literature search stated as such; a file with only the statements, using
  Mathlib's definitions, read by a third party; `lake build` clean, `#print axioms` shown, a comparator or lean4checker
  run; a statement dictionary (claim, Lean name, definitions that differ from Mathlib); a specific disclosure (tool,
  version, what it did, who checked what); a tagged release with a Zenodo DOI and a Software Heritage identifier; an
  OSI-approved license (none is chosen yet; Reservoir also wants a root `lake-manifest.json` and two stars).
- **Credit.** Baker's theorem is Karatarakis's unannounced proof and Bang's theorem is Tau Ceti's: name both, and write to
  Karatarakis first (R01).
- **Avoid.** Announcements before checks, social media first, mass mailing, viXra, long unexplained output, "first" or
  "new" without the checks of 2.2, LLM-written comments on GitHub or Zulip, large AI-written pull requests. [R03, R04, P09]
- **Own words.** The Annals of Formalized Mathematics (AFM) takes only human-authored manuscripts and wants an AI
  disclosure for text and code; the Journal of Integer Sequences (JIS) forbids LLM-written text (rejection, possibly a
  lifetime ban) and wants LLM-suggested proof ideas credited; ITP forbids substantial AI-generated text [R04 READ]. So the
  paper must be written by the author; so must comments and replies to reviewers on Mathlib (P09, R03). How
  "human-authored" is judged for an author who works with an assistant was not found (R04).
- **arXiv.** Since 10 Dec 2025 a first submission to math needs a personal endorsement unless the author has an academic
  address and an accepted math paper [R04 READ]. arXiv's own advice: ask authors of recent related papers, one at a time,
  through the endorser link on abstract pages. Policy of May 2026: clear evidence of unchecked LLM output brings a
  one-year ban; LLM use itself is not forbidden [R03, R04]. AI-assisted, Lean-checked math.NT papers by little-known
  authors exist (Kimura, Fukui, Banwait, van Doorn-Monticone-Tang) [R04 READ abstracts]. Without an endorsement: Zenodo,
  which AFM accepts as the deposit.
- **Venues** [R04]: AFM (free, artifact mandatory, wants mathematical novelty beyond the formalization: the classification
  theorems qualify, a re-proof would not); JIS (free, median 197 days) and Integers (BBP papers by non-academics have
  appeared there); Experimental Mathematics (code culture; fees not obtained); ITP 2027 (abstract 8 Feb, paper 15 Feb
  2027; wants formalization method, not only mathematics); Lean Together (a recorded talk; call around early December,
  [INFERRED]). Policies of the Ramanujan Journal, Math. Comp., the Monthly and the Fibonacci Quarterly were not obtained.
- **Mathlib.** AI use must be stated in the PR description and labelled `LLM-generated`; the contributor must understand
  and defend every line without AI; low-quality LLM PRs may be closed without comment, repeated violations can bring a
  ban [READ P09, R03]. Practice: PR 43144 (pi transcendental, AI-written, for the 100-theorems file) closed as not wanted
  there [P08, R01]; a Stormer PR closed for AI-use policy [R06]; a PR closed for undisclosed AI use, resubmitted with
  disclosure [R03]; many disclosed `LLM-generated` PRs are open and under review [R03]. A maintainer's personal view:
  battle-test downstream first [R03]. R03 and R04 conclude: keep an own repository, offer Mathlib only small general
  lemmas. R01's worry that all AI-assisted upstreaming is barred goes beyond this evidence [INFERRED-S].
- **Formal Conjectures and Palomar** [Q05, P09]: the repository holds statements; proofs of research problems are linked
  only through a Palomar entry (comparator check, LLM screening, no peer review, AI allowed with a `formalization.yaml`).
  The project's results are theorems, so this suits only open questions the project can state.
- **Asking an expert** [R04, thin]: one named recipient, why that person, one narrow question (is this the statement you
  meant; is it known; would you endorse), the Lean statement and the axioms in a few lines. Natural recipients: the
  Compendium's maintainer, authors of the recent BBP papers, a Lean user for the statement check [R04 step 4].
- **Climate** [R03, Q04]: after the announcement of 20 November every Lean claim meets close scrutiny, and reviewers say
  they owe AI-assisted papers no checking; the author has to lower the cost of checking. Uncertain: how number-theory
  journals treat such papers (R03 and R04 could not read their policies).

## 7. Gaps of this pass

**Thin threads.** P07 (who proved which of Sun's conjectures after 2023), Q10 (the literature on the product for pi/4), R07
and R01 (the Baker-method papers known only through surveys and reviews), R04 (journal policies), R02 (which L(1, chi)
have formulas in print), P08 (independence measures of 1, pi, log 2), P10 (the current list of open Ramanujan Machine
conjectures). No thread examined Theorems A, B, D or the 7/24 measure against the literature. MathSciNet, Google Scholar
and the zbMATH reviews of BBG were used by nobody.

**Sources nobody could read.**
- On pi: the printed BBP paper (Math. Comp. 66, 1997; only the preprint was read); Takahashi 2020 and 2021 in full;
  Huvent's page; Gourdon 2003; Lafont's 2011 note (digest only); Broadhurst, "Vanishing polylogarithmic ladders" (2000,
  private); the Borwein-Chamberland manuscript on the golden base; Chan 2008; Calcut 2009; the CARMA list of zero
  relations; Compendium versions before March 2004; Kulik's Zenodo records; Craig-Wood 2023; Patel and Zhou on Sun's
  conjectures.
- On periodic sums: ASST 2001; Saradha-Tijdeman 2003; Okada 1982 and 1986; Baker-Birch-Wirsing 1973; Murty-Saradha 2007
  and 2010; the Pilehroods 2008; Hata 1990.
- On primes: Schinzel 1962 and 1974; Carmichael 1913 (scan); Stevenhagen 1987; Granville-Pleasants 2006 (abstract only);
  Yates 1980 and 1985; Caldwell 1997; the Cunningham tables book; Berrizbeitia-Iskra 2010; Stormer 1895 and 1896; Lehmer
  1938; Todd 1949; Ennola 1972; Conrad 2000; Washington, chapter 8; Drungilas-Dubickas 2019; Nagura 1952; Rosen 1999;
  the mersenneforum threads on pi(x) and prime gaps.
- Other: the policy pages of Springer, AMS, MAA, Integers and the Fibonacci Quarterly; MathOverflow; the 6 Oct 2026
  announcement on erdosproblems.com; the Lean sources of the 20 November development and the critique of it; the Baker
  file of diaz-modulus-lean; a build of metasecdev/math-proofs.

**Wave 2.** `00_QUEUE.md` lists 14 threads already started (W2_Q11 to Q20, W2_P14, P15, W2_R08, R09). They cover items 2,
5, 9 and 12 of section 2.2, lead B3, and the OEIS and certificate questions. Twelve further threads, not covered there:

1. (primes) Unique primes in bases 3, 5, 6, 7, 10, 12: Cunningham tables, factordb status, "generalized unique" primes on
   the Prime Pages, the papers of Yates and Caldwell; proved against probable.
2. (primes) Primitive prime divisors of p^n - q^n for a rational base p/q and of a^n - 1 in Kummer fields: exact
   exceptions, Aurifeuillian factorization for rational a (Allombert-Belabas); what lead A2 needs.
3. (primes) Primitive parts that are prime powers: Phi_n(b)/gcd = p^e, Wieferich primes, the Nagell-Ljunggren cases in
   OEIS A323748, Song's finiteness of bases for a fixed prime; is it effective by Baker?
4. (primes) Primes with a prescribed divisibility of ord_p(b): the density results behind BBG's Appendix C and problem
   D(4), elementary proofs, Chebotarev for Kummer extensions and its Lean status.
5. (primes) How many primes have a logarithm formula: Pomerance's heuristic, any provable upper bound (density zero?),
   what is known unconditionally about infinitely many unique primes in some base.
6. (primes) Primes with formulas in two bases: coincidences of primitive parts in bases 2 and 3, Goormaghtigh-type
   equations; the arithmetic side of Lagarias's Question.
7. (primes) Primitive divisors of Lucas and Lehmer numbers for the bases phi, 1 + sqrt 2 and for Z[i]: Carmichael's
   theorem, the Bilu-Hanrot-Voutier and Abouzaid tables, Flatters; what lead A9 needs.
8. (primes) Gaussian primes of x^2 + 1: Stormer numbers, Todd's and Lehmer's reductions, Wetherfield's lists, Yamada's
   bounds; the state of the three-term and four-term lists before attempting C4.
9. (primes) pi(x) at 10^27 to 10^29: how the two runs differed, parity algorithms (Lelechenko, Lifchitz), memory use of
   primecount, the frontier and audit trail of the maximal-gap search.
10. (pi) The unread sources: the printed BBP paper and Buhler, Takahashi's papers, Huvent, Lafont, Broadhurst 2000, ASST
    2001, Gourdon 2003; needs library access.
11. (pi) Steps n >= 3 and general bases in print: Adegoke's general-base papers read in full, for the base-2 step-3 and
    the base-3 step-4 and step-6 series, and for pi sqrt(d).
12. (pi) Non-integer bases: K-M's published text and formulas, Bailey's formulas (132) and (133), Chan, the
    Borwein-Chamberland manuscript, Cloitre; with a recomputation of every displayed coefficient vector.
