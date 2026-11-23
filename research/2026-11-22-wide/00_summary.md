# Wide research pass of 22-23 November 2026: synthesis of waves 1 and 2

Wave 1 (31 reports: P01-P13 and F3 on pi, Q01-Q10 on primes, R01-R07 beyond) and wave 2 (14 reports: W2_P14, W2_P15,
W2_Q11 to W2_Q20, W2_R08, W2_R09) were read in full, with `00_RULES.md`, `README.md` and the summaries of
`../2026-11-22-nonbinary-pi`, `../2026-11-22-log-primes`, `../2026-11-22-general-step`. No web access was used here.
**Everything that wave 2 added, confirmed or corrected is tagged [W2] with the report's name**; untagged text is the
wave-1 synthesis. Marks are the reports' own: [READ], [SNIPPET], [INFERRED], and [COMPUTED] / [MEASURED] where a helper
ran something. Many [READ] are readings through a fetch tool that returns a digest of the page. [INFERRED-S] marks a
conclusion added by this synthesis. "Not found" is weak evidence throughout. Results are named as in `README.md`;
"Theorem N" is the paper result of the log-primes summary (in a base b >= 5, b != 9, no log n with n >= 2 an integer is
a value).

## 1. Search totals

As each report's search log states. "Usable" is the report's own figure, or attempted minus the failures it counts;
"(s)" marks a figure counted by this synthesis from the log because the report gives none. Conventions differ: some
reports count page reads as endpoint queries (P04, P09, P13, Q03, Q09, R03, most of wave 2), others only search
endpoints (Q04, R02, R04; their page reads, about 34, 13 and 45, are extra).

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
| R01 Baker corollaries | 4 | about 85 | about 70 | |
| R02 other constants | 6 | 37 | about 23 (s) | |
| R03 AI and mathematics | 6 | 62 | about 50 | |
| R04 publication routes | 6 | 38 | about 21 | |
| R05 cyclotomic relations | 2 | 77 | about 56 | |
| R06 finite problems | 6 | 64 | about 45 | |
| R07 Lerch sums | 5 | about 55 | about 25 | |
| [W2] W2_P14 Gibbons's conjecture | 5 | 45 | about 36 | |
| [W2] W2_P15 formal work on BBP | 5 | about 90 | about 73 (s) | |
| [W2] W2_Q11 Erdos +-1 conjecture | 3 | 51 | about 40 | read Okada 1982 in the original |
| [W2] W2_Q12 Zsigmondy, formal | 5 | 60 | 49 | |
| [W2] W2_Q13 Lean PNT projects | 2 | 75 | 71 | |
| [W2] W2_Q14 OEIS entries | 1 | 50 | 46 | |
| [W2] W2_Q15 Schinzel's statements | 1 | about 64 | about 35 (s) | the 1962 and 1974 papers stayed unread |
| [W2] W2_Q16 cyclotomic primes | 3 | 49 | about 30 (s) | |
| [W2] W2_Q17 Chamberland 2003 | 1 | 41 | 30 | read the paper's TeX source in full |
| [W2] W2_Q18 primality in Lean | 3 | about 60 | about 40 | |
| [W2] W2_Q19 Mathlib facts | 0 | 51 | 41 | plus about 40 searches of the local Mathlib source |
| [W2] W2_Q20 covering problems | 2 | about 69 | about 47 | |
| [W2] W2_R08 venues at the source | 6 | about 100 | about 65 | |
| [W2] W2_R09 recent overlap | 6 | about 105 | about 95 (s) | |

| Subtotals | WebSearch | Endpoint attempted | Usable |
|---|---|---|---|
| Pi: wave 1 (P, F3) + wave 2 (W2_P) | 55 + 10 = 65 | 893 + 135 = about 1028 | 637 + 109 = about 746 |
| Primes: wave 1 (Q) + wave 2 (W2_Q) | 36 + 21 = 57 | 639 + 570 = about 1209 | 526 + 429 = about 955 |
| Beyond: wave 1 (R) + wave 2 (W2_R) | 35 + 12 = 47 | 418 + 205 = about 623 | 290 + 160 = about 450 |
| Wave 1 (31 reports) | 126 | about 1950 | about 1453 |
| [W2] Wave 2 (14 reports) | 43 | about 910 | about 698 |
| **Both waves (45 reports)** | **169** | **about 2860** | **about 2151** |

So about 3030 searches were attempted in all and about 2320 were usable. Rate limits: every report met HTTP 429 from
the arXiv API and Semantic Scholar (often from the first call) and from OpenAlex after 3 to 20 calls; GitHub code
search always answered 401, zbMATH's web pages 403. No report records a WebSearch cap error. Coverage was weakened most
in P07 (forward citations thin), Q10 (no citation chasing), R07 (ASST and Saradha-Tijdeman unread), R04 (publisher
pages blocked), R02, P08, P04, P02, P03, R06. [W2] In wave 2: W2_Q15 (Schinzel's 1962, 1963 and 1974 papers all
behind paywalls), W2_R08 (Springer, Taylor and Francis, AMS and MAA author pages still blocked), W2_Q16 (about 40% of
queries failed, by my count), W2_Q20 (erdosproblems.com refused every fetch). The strongest single source of the pass is W2_Q19,
which read the project's own Mathlib checkout (commit of 16 Nov 2026) instead of the web. Several reports note that
OpenAlex responses carried a notice asking an agent to request an API key with an e-mail address; all ignored it.

## 2. Novelty and overlap

### 2.1 What is in print, result by result

- **Theorem L (pi iff |b| is a power of 2).** Cite: Borwein-Borwein-Galway 2004 (BBG), Theorem 7 (Machin-type only;
  Bang's theorem and Z[i], no Baker) and Comment 10, which poses the general case [READ P01, P03, P12, R02; checked in
  the nonbinary-pi summary]; Bailey's Compendium, which states it as shown [READ]; the BBP preprint (1995/97), section
  6: PSLQ found no formula for bases 2..128 other than powers of 2, and J. P. Buhler "has reported a proof" that such
  an identity forces the base 2^K [READ by P04, preprint only]; Bailey-Crandall 2001 (base 10 asked) [READ P05];
  Zudilin 2024, both versions (calls it open) [READ P01, P04, P13, R02, W2_R09]; Lagarias 2001, Theorem 5.3, and ASST
  2001 for the first use of Baker on such series (0 or transcendental only). No report found a proof of the full
  statement or a counterexample. [W2_R09] No arXiv, Zenodo, zbMATH or Crossref item of 2023-2026 proves nonexistence
  for the full class, classifies zero relations or treats logarithms as Theorem K does. The Kulik text feared by P01
  was read (it survives in the DataCite record and a web-archive copy): a self-published study, frame by frame
  (b <= 320, N <= 9), of zero relations; it reduces them to an S-unit lattice with Baker's theorem, computes most
  dimensions by lattice reduction, and says itself that no global classification is claimed. Zenodo removed it and
  the author's account on 30 Oct 2026 ("out of scope"). No priority conflict; cite it, if at all, as a removed
  preprint. Euler's 1779 formulas (Craig-Wood 2023: bases 4 and 2^30) are binary and belong among the examples.
- **Theorems M and N (logarithms).** Nearest: BBG Example 4 (no Machin-type formula for ln b in base b when M_b = 0, so
  none for ln 10; for any ln n "seems unlikely", not proved) and Example 5 (base 7) [READ P01, P12, R02]. Nobody states
  "iff b is a power of 2 or 3" [W2_R09 agrees]. The Compendium has base-10 and base-5 formulas for logarithms of
  non-integers (formula 84: log(9/10); 85-89), so the statement must be about log n, n >= 2 an integer.
- **Theorem G (b >= 5), C5.** Not found anywhere (P01, P11, R05, R07, W2_R09). Nearest: Bailey's Table 1 (PSLQ counts;
  one non-binary row, base 3^6) [READ P11]; the dual theorem of Madritsch-Ziegler and Drungilas-Dubickas [SNIPPET
  R05]; Bass 1966 and Ennola 1972 for alpha = 1; the Pade criteria of David, Hirata-Kohno and Kawashima, which by
  R07's evaluation need log b of order N log N [INFERRED from a garbled text layer]; ASST Theorem 4 as reported in
  Tijdeman's survey. The project's lemma on primes containing sqrt(b) - r is not a printed theorem (nearest:
  Postnikova-Schinzel 1968 [READ Q01, W2_Q15], Schinzel 1993). [W2_Q12] It is in no formal library either: Tau Ceti's
  Zsigmondy (merged 15 Nov 2026) is for integers only.
- **Theorem C, Bailey's table, C3 in full.** Print has no dimension count and no structure theorem. The Compendium
  says the pattern of zero relations is not understood [READ P02, P11]; Barsky, Munoz and Perez-Marco (BMP) ask whether
  all degree-1 null formulas come from their Theorem 1.1 [READ P02, P11, W2_R09]; BBG problem D(2) asks how many
  independent binary Machin-type zero relations exist; Bailey-Crandall 2001 list a theory of "Ferguson anomalies" as
  open [READ P05]; Kristensen-Mathiasen (K-M) recover 1 of 5, 1 of 3 and 1 of 2 known relations [READ P11]; Lafont
  (2011, unrefereed) proves eight relations one by one. Bailey's counts agree with the project where compared.
- **Theorems E, F, E3, J (terms per bit).** No lower bound of any kind in print; Bellard's 1997 page asks whether a
  faster formula exists [READ P04]. [W2_R09] The measure itself is in print: BMP, Remark 1.2, define the efficiency
  m'/log b (non-zero coefficients per bit) and compare 1 (BBP) with 7/10 (Bellard); cite it as the source of the
  measure. Huvent's page could not be read. Of Takahashi (Ramanujan J. 51, 2020) the helpers saw only the abstract
  ("about 20% fewer terms") [SNIPPET P13]; that is the 64 against 80 of `notes/pi_formula_theorem.md` [INFERRED-S].
- **Theorems G (log 23), H, K, K3, K5.** Cite the BBP paper, section 5 (Pomerance: 23 is not a quotient of numbers
  2^a - 1; Harley: 29, 37) [READ P04]; BBG Theorem 4 and Remark (i) [READ P12]; Chamberland 2003 [READ P12, Q03, Q09,
  W2_Q17]; the Compendium's list (9). No iff criterion in print in any base. Ternary: only 2, 3, 5, 7, 11, 13 (OEIS
  A165132, keyword "more"). [W2_Q17] Chamberland's paper proves nothing about its table: 90 primes "by modest
  calculations with Maple", three worked examples (331, 14449, 599479), one theorem (on Aurifeuillian identities);
  Bailey's list (9) is exactly its 46 underlined primes. [W2_Q16] The link to unique primes is not in print:
  Pomerance's "Cyclotomic primes" (2025) is on base 2 only, proves that many primitive parts are composite, and
  mentions neither BBP nor logarithms; it leaves bases a > 2 "for another day".
- **Theorem I.** BBG Theorems 1-2 already exclude 3/8, 5/8, 5/11, 9/16, 11/18 in the Machin-type class and leave 2/7,
  4/9, 5/9 open when Aurifeuillian generators are allowed; the Compendium (2023) still calls arctan(2/7) unknown [READ
  P12, W2_Q14]. So for 5/8 cite BBG; 2/7 and 4/9 are the new cases; 5/9 is not in `README.md`.
- **Values 0 or transcendental.** Known: ASST 2001, Lagarias 2001 Theorem 5.3, Bundschuh 1979. Cite; no novelty.
- **Rational base 3/2.** F3: the construction is in print with a real parameter (Adegoke 2010; Adegoke-Layeni 2013;
  K-M Theorem 1), but only integer or Pisot bases were written down. The base-3/2 formula for pi was not found. The
  base-4/3 formula for pi sqrt(3) is in print: Adegoke-Layeni, Appl. Math. E-Notes 10 (2010), eq. (4.4) [READ on
  ar5iv, checked numerically]. P03 had called both new. No digit extraction is known for a non-integer base.
- **[W2_P15] Formal proofs of BBP formulas exist already.** The BBP identity for pi: HOL Light (Harrison 2010, per
  Bertot et al. [SNIPPET]), Coq (Bertot-Rideau-Thery 2017, with a partially correct digit algorithm), and twice in
  Lean in October-November 2026: metasecdev/math-proofs (also a guard depth for every position n, from an irrationality
  measure of 16^k pi with exponent 570 proved in that repository by Mahler's method) and bjbraams/lean-DLMF
  (`hasSum_bbp_pi`, series for log 2, log 3, 4 log 5 in base 16, (8/3) log 3 in base 64, Gauss's Machin formula; a
  general-radix file there has its three theorems as `sorry`). Neither is reviewed. Nothing formal was found on
  Bellard's or Huvent's formula, on classification, optimality or nonexistence. Not in Mathlib (W2_Q19).
- **Baker's theorem, formal.** R01 [READ, local README]: the imported proof (Karatarakis) is the qualitative theorem
  with constant term, on an unmerged branch, announced in no paper. Not in Mathlib (P08, R01, W2_Q19). [W2_Q12] Tau
  Ceti's roadmap plans to port it "with credit" and excludes effective bounds.
- **Theorems A, B, D**: no thread addressed them. Nearest: Stormer's criterion and two-term theorem, Yamada's
  finiteness for three terms, Gasull-Luca-Varona 2023 [READ P06].

### 2.2 To verify before use, most important first

1. **Buhler's reported proof (open; no wave-2 thread).** Only P04 saw it, in the preprint. If the printed paper (Math.
   Comp. 66, 1997) keeps the sentence, the statement of Theorem L was claimed in 1997, with no published proof, for
   the shape sum n^(-k) (a_1/(mk+1) + ... + a_m/(mk+m)). Read the printed text, cite it, ask whether a proof was ever
   written. It changes the wording of Theorem L, not the mathematics.
2. **Q06's parity result on Erdos's +-1 conjecture.** [W2_Q11] *Confirmed:* (a) Okada's criterion was read in the
   original (Acta Arith. 40 (1982), Theorem 10), and the form Q06 used (Chatterjee-Murty 2015) has the same solution
   space for q = 9, 15, 21, 45, 75, 105 [COMPUTED]; (b) a second, independent program reproduces the result for every
   composite non-prime-power q = 1 mod 4 below 480: the 2-adic test excludes a +-1 solution except for 225 and 441,
   both covered by Okada's own corollary; the test never fired falsely on 300 synthetic systems, and brute force over
   all sign vectors agrees for ten small q; (c) so the conjecture holds for these q, including 105 and 165 which the
   papers of 2015, 2019 and 2022 leave open, granted only Okada's published theorem. *Not confirmed:* (d) any proof
   for all non-square q (the pattern "survivors are exactly the squares" rests on about 30 cases); (e) the range
   480 < q <= 1000, which is Q06's run alone; (f) novelty: a parity obstruction is in print for q = 2 mod 4
   (Murty-Pathak 2022, as cited by Bharadwaj), and Murty-Saradha 2010, Murty-Pathak 2022 and Bharadwaj-Murty-Pathak
   2025 were not read; W2_Q11 puts "some form already in print" at about 40% [INFERRED]; (g) squares with three or
   more prime factors (smallest 105^2), where the test says nothing.
3. **What the K-M formulas are (open; no wave-2 thread).** Their abstract says integer coefficients in Pisot bases;
   P03 [COMPUTED] finds the displayed coefficient vectors in Q(sqrt 3) minus Q and in a field of degree 4; F3, P04, R02
   and the general-step summary (section 7, "rational coefficients") repeat the abstract. If P03 is right, no
   rational-coefficient formula for pi in an irrational base is known and the sentence bounding Theorem L must change.
4. **Rational bases (open).** (a) Base 4/3 is Adegoke-Layeni's. (b) "Only r^2 in {1/4, 1/3, 1/2, 2/3, 3/4}" is a
   computation for single triangles with angle denominators up to 60; "iff a power of 3/2 or 4/3" is P03's
   conjecture; combinations of several terms are not covered. (c) The Borwein-Chamberland manuscript is unread.
5. **Bailey's count 7 at (2^60, 120)** against the project's 8 (P11 asks). Reading: 8 is the pi-space and the zero
   relations are 7 [INFERRED, P11 and S]; confirm against the Lean statement. Table 1 counts rewritings and omits
   "larger" relations, so P11's remark that it has no row with N = 3e (steps >= 3 new) is [INFERRED] too.
6. **"First formal Baker" and provenance.** carlok/diaz-modulus-lean lists Baker, with no named declaration [READ P08;
   R01 could not see the proof]. The vendored proof is one person's unannounced work: write neither "first" nor
   "ours", and ask the author before any publicity. [W2_Q12] Tau Ceti may soon carry its own port, which could
   replace the vendored files.
7. **Aurifeuillian halves.** [W2_Q15] Partly settled. "Each half has a prime of order n" is equivalent to "neither
   half is 1 or the largest prime factor of n"; by exact computation to n = 140 the only failures are (b, n) = (2, 4),
   (2, 12), (2, 20), (3, 6), none for b = 5, as Q02 found. It is not Schinzel's 1962 theorem as quoted by Stewart
   (that is a bound P(a^n - b^n) >= 2n + 1, which holds at n = 20), nor a logical consequence of "at least two
   primitive primes" (the form in Aigner's review of Schinzel's 1963 paper). Still open: the texts of Schinzel 1962
   and 1963 (unread), a printed size bound for the halves beyond n = 140 (not found), and the side conditions of the
   project's base-2 Lean statements.
8. **Counts.** [W2_Q16] The two helpers read Pomerance's Table 1 differently: 289 is the number of m <= 2^17 with
   Phi_m(2) prime (Q03) or with prime primitive part (W2_Q16, which also counts 293 listed values); Q03 has 296 for
   the primitive part, against 179 in OEIS A161508. Recount before using any figure; primality there is by
   Baillie-PSW. [W2_Q17, W2_Q14] OEIS A088962 has about 60 terms where Chamberland's table has 108.
9. **The Riemann hypothesis announcement of 20 November 2026** (Q04, R03): a Lean-only development, certified by the
   Lean and Mathlib communities as a proof of Mathlib's statement, not refereed, no readable proof; sources disagree
   on whether two checkers accepted the export, and one critique (R03, secondary) is unanswered. Do not cite it as
   proved; its library has no license.
10. **Settled by wave 2** (drop as doubts, keep as wording):
    - [W2_Q19] *What Mathlib contains*, read in the source tree. In: Basel and zeta(2k); Euler products of zeta and
      Dirichlet L for Re s > 1 only; L(1, chi) != 0; Dirichlet's theorem; the prime number theorem and its version in
      progressions (`WeakPNT.lean`, merged 11 Nov 2026; no error term); Leibniz, Wallis, Euler's sine product; four
      Machin-type identities; 20 decimals of pi; irrationality of pi; generalized continued fractions (regular
      fraction of a real converges). Not in: any BBP-type formula; the proof of Chudnovsky (`proof_wanted`);
      transcendence of pi, Lindemann-Weierstrass, Baker; Zsigmondy; Mertens (three open PRs); natural density, hence
      6/pi^2; any Euler product at s = 1; Brouncker or any continued fraction of a named constant; polylogarithms
      (PR 44531 open); normal numbers. [W2_Q18] Nor Pocklington or Proth, which settles Q04 against Q10.
    - [W2_P15] *Lean BBP elsewhere*: P04's "none found" was wrong; see 2.1. Do not claim a first Lean proof of BBP, a
      first formalization of a BBP formula, or a first formal total correctness of digit extraction.
    - [W2_P15, W2_P14] *Irrationality measure*: P04's route through Baker is not needed; a Mahler-type measure is
      formal in metasecdev's repository, and Yap's argument needs any finite measure. The 2026 claims mu(pi) = 2 and
      mu(log r) = 2 remain unrefereed.
    - [W2_Q14] *OEIS A250197*: recomputed, all 56 terms right; Q02's suspected erratum is withdrawn.
    - [W2_R09] *Kulik*: read; no overlap in results (2.1).
11. **Wave-1 statements corrected by wave 2.**
    - [W2_Q13] Q08 said Dusart's Proposition 5.4c "blocks" the lcm theorem of the Lean prime-number-theorem project.
      It is one of three pieces: 5.4b is proved but rests on a prime-gap table whose verification is `sorry`, 5.4a on
      a `sorry` theorem; and the file has 32 `sorry`, not 33. Closing 5.4c alone makes nothing unconditional.
    - [W2_Q20] Q05's lead on Erdos 203 (a covering for 2^k 3^l m + 1): for every period box up to 120 x 120, and
      multiples of 60 up to 360 x 360, the total density of usable primes is at most 0.80 < 1 [COMPUTED]; no covering
      exists there and one is unlikely to be found. The problem is open (one mirror page says "solved": unresolved).
    - [W2_P14] P13's lead "prove Gibbons's Conjecture 1": the conjecture is equivalent to the absence of runs of 0s or
      9s of length about 0.13 n at decimal place n of pi [INFERRED], which no irrationality measure gives. Verified to
      20000 terms; a proof is out of reach; only a conditional theorem is.
    - [W2_Q17] Q09's remark that Gaussian-Mersenne norm primes are 1 mod 4p now has a short proof (every prime factor
      of 2^(2p) + 1 other than 5 is 1 mod 4p) [INFERRED]; print has only 1 mod p.
    - [W2_R08] R03 gave the Leiden Declaration 4,458 signatories, W2_R08 "over 2,000 within a week" [SNIPPET]; R03 and
      R04 date arXiv's one-year-ban rule to May 2026, W2_R08 read a July 2026 article calling it a clarification.
12. **A104885.** [W2_Q17] Of the 44 primes in Chamberland's table that are not Bailey's, 33 were verified to lie in
    the span of the paper's generators and 10 (from 25 to 54 digits) were beyond the search bound, untested; 38737 is
    the only failure found. All 41 printed products of two primes check. Q03 [INFERRED]: the "infinite set of primes"
    of Adegoke, Oliver Lafont and Layeni (2016, section 6.1) are rationals, not primes; unread still.
13. **Misreadings and small [INFERRED] claims.** P06 gives BBG's abstract as "b = 2"; it is "b != 2". P04 names Magaud
    and Zimmermann, P09, P13 and W2_P15 name Rideau and Thery, for arXiv 1709.01743. P01 found Compendium title-page
    dates 2004, 2009, 2011, 2013, 2023 only, while P02 cites a "2006" and P03, F3 a "2017" version. Not facts yet:
    BBG question (7) follows from Bilu-Hanrot-Voutier (Q01); the reduction of Erdos 307 (Q05); the Pade threshold
    table (R07); "no proof found" for 18/pi^2 (P10); arXiv's limit of two submissions a month (R04, secondary).

## 3. Published questions

### 3.1 Answered by the project (always: degree 1, rational coefficients, integer base)

| Where it is asked | Question | Answer |
|---|---|---|
| BBG 2004, Comment 10 | is pi a rational combination of the L(1, b^m, n, j)? | only for b a power of 2: Theorem L in that notation (`no_pi_L_comb`) |
| BBG 2004, Example 4 | does any ln n have a formula in a base with M_b = 0? ("failed to prove") | ln b: Theorem M. Every integer n >= 2, b >= 5, b != 9: Theorem N (paper) |
| BBG Remark (i), D(8); BBP 1997 sec. 5; Chamberland 2003 | an Aurifeuillian formula for log 23? | none in F (Theorem G); Theorem K decides every y. [W2_Q17] It is the only "unknown" stated in Chamberland's paper |
| BBG D(11) | why Machin-type generators capture everything | Baker's theorem (P12, [INFERRED]); worth one sentence |
| BBG Examples 2-3; Compendium sec. 3 | arctan(2/7), arctan(4/9) | Theorem I; 5/9 remains |
| BBG D(2) | how many independent binary Machin-type zero relations? | likely read off Theorem C; the two classes must be compared first (P06, P12). [W2_R09] Kulik's removed text quotes D(2) and D(10) as its problem and does not claim an answer |
| Compendium (zero relations); Bailey-Crandall 2001 (Ferguson anomalies) | why zero relations occur for some (b, n) only | degree 1: all of them in bases 2 and 3 (steps 1, 2), none for b >= 5 |
| Compendium sec. 2; OEIS A104885 | do all primes have a binary formula? | no (23); each prime is decided by Theorem K |
| Bailey-Crandall 2001 sec. 5; BBP 1997 sec. 6 | a BBP-type scheme for pi in base 10? | none of this class (Theorem L) |
| Lagarias 2001, sec. 6, Question | have all G-function BBP numbers expansions in two independent bases? | pi has not, within degree 1 (P05, [INFERRED]); the Question allows higher-order poles, so it is not settled as posed |
| Bellard 1997; [W2_R09] BMP 2021, Remark 1.2 ("hope" for more efficient formulas) | is there a formula faster than Bellard's 7/10? | within degree 1 Huvent's 2/3 is optimal (Theorems E, F) |
| Barsky et al. 2021, sec. 1 | "no base 3 formula for pi is known" | none exists in this class (C3, L) |
| Zudilin 2024 (v1 and v2) | BBP-type computation of pi in other bases? | excluded only for this class; his series (Gaussian base, recurrence coefficients) lies outside |

### 3.2 Not answered

- BBP 1997, section 7, questions 1-5 (decimal digits of pi, e, sqrt 2, log 2 in base 10, log 23 in base 2, as
  statements about the class SC): the absence of a formula is not the absence of an algorithm. Decimal digits of pi
  are extracted by Plouffe's and Bellard's prime-by-prime method (P04, Q10); no proof of its correctness was found.
- Whether the primes with a binary formula are finitely many (Compendium, A104885). [W2_Q16] Infinitely many would
  follow from infinitely many cyclotomic primes Phi_m(2), which is open even conditionally and contains the
  Mersenne question; finiteness is open too. So the classification can only be a criterion, never a list.
- Hypothesis A and normality (P05): every degree-1 value is a BBP number in Lagarias's sense, nothing more.
- Degree >= 2: the s >= 2 rows of Bailey's Table 1, pi^2 in other bases, Broadhurst's questions. Even the
  irrationality of Li_2(1/2) is open, so unconditional nonexistence is out of reach (P02).
- Non-integer bases: K-M's three problems, Cloitre's octagon question, BBG D(7) and D(9), Zudilin's question.
- BBG D(3), D(4), D(5), D(6); the question of BMP on null formulas (P11 and W2_R09 expect a corollary; not done).
- "e has no BBP-type formula": equivalent to an open problem on periods; provable from Schanuel only (R02).
- The project's own open items: steps n >= 3 for b >= 5 beyond multiples of pi in cyclotomic fields, uniqueness for
  7/24, Theorem N in Lean. Outside: Erdos's +-1 conjecture in general (2.2, item 2); Gibbons's conjecture (item 11).

## 4. Errors and overstatements in print

| # | Where | Evidence | How firm |
|---|---|---|---|
| 1 | Bailey's Compendium, introduction: BBG "showed" there is no degree-1 formula for pi outside powers of two | absent in the versions of 1 Mar 2004 and 15 Sep 2009, present 13 Feb 2011, 29 Apr 2013, 8 Apr 2023 [READ P01]; BBG prove the Machin-type case and pose the rest. Mendonca (arXiv 1209.2348) repeats it; MathWorld is correct | firm about the citation; the statement itself is true (Theorem L) |
| 2 | Chamberland 2003, table; OEIS A104885: the prime 38737 | fails the project's criterion (Lean iff plus program). [W2_Q17, W2_Q14] In the paper it occurs only in the bare list, with no formula; 433 * 38737 = Phi_72(2), and in about 2100 generators of the paper's types 38737 never occurs without 433, which is in no table: most likely the pair 433 * 38737 was filed as a single prime | firm that the entry is unsupported; the "misfiled pair" reading is [INFERRED] from a bounded computation |
| 3 | OEIS A104885 as a whole | a 46-term prefix of Chamberland's list ending at 312709; [W2_Q14] it cites only BBP 1997 and the Borwein-Bailey book, not Chamberland; three revisions, last 2012; no erratum | firm, minor |
| 4 | [W2_Q17] Chamberland 2003, text | the identity for Re log(1 - ((1 + sqrt(-3))/2) x) is wrong as printed (right: (1/2)[log(1 + x^3) - log(1 + x)]); "Phi_pn(x) = Phi_n(x^p) for p not dividing n" holds for p dividing n; a missing "=". The three worked examples, all 41 products and the 108 values of m were recomputed and are right | firm [COMPUTED]; harmless to its conclusions |
| 5 | K-M 2023, abstract: "integer coefficients" | P03's computation (2.2, item 3) | open |
| 6 | Adegoke, Oliver Lafont, Layeni 2016, sec. 6.1: an "infinite set of primes" with binary formulas | Q03 [INFERRED] | soft; read first |
| 7 | BBG p. 924: number-field Zsigmondy "with effective bounds on the exceptional cases" (Schinzel 1974, Bilu-Hanrot-Voutier) | Q01 [INFERRED]: the second is over Q; [W2_Q15] the first gives a threshold n0(d), exact text unread | soft |
| 8 | Schinzel 1962 as quoted by Stewart | WITHDRAWN as an error. [W2_Q15] The quoted theorem is the bound P(2^n - 1) >= 2n + 1 with exceptions n = 4, 6, 12, and it holds at n = 20 (41 = 2 * 20 + 1); only the loose phrase "two primitive divisors" fails there | not an error |
| 9 | Luca-Stanica, two-term arctangent relations in powers of the golden section | a missed case, corrected by Gasull-Luca-Varona 2023 [READ P06] | firm (published correction) |
| 10 | Explicit prime estimates: a missing condition in FKS2; Johnston-Yang (x >= 2 should be x >= 23); a Schoenfeld-type interval claim on the TME-EMT wiki (false at x = 2010880); Ramanujan-inequality papers; Ramare-Saouter's range; BKLNW Table 8 | Tao's log of the Lean project [READ digest, Q08]. [W2_Q13] Two more statements of that project are false as printed (issues 260 and 268 of teorth/IEANTN, on Buthe's numerics) | found by others; firm as reported |
| 11 | Tables resting on one computation: pi(10^27..29) (one code base), pi_2(10^19) (one contributor, corrected July 2026), OEIS A161508 (179 terms; 289 to 296 known, see 2.2 item 8), [W2_Q14] A002072 (terms 27 to 37 computed, in part predicted from an effective abc conjecture) | [READ Q07; SNIPPET W2_Q14] | not errors; candidates for checks |
| 12 | Slips: "seventeen" for 18 primes (Caldwell-Dubner); "Mertens 1984" for 1874 (Kaneko); "Wrench" formulas not in Wrench 1938 (Yamada); stale Prime Pages entry on Gaussian-Mersenne primes; Wikipedia on Riesel candidates, AP-27, PiHex cost; [W2_P14] Yap's preliminary text gives 7.6804 for Salikhov's 7.6063; [W2_Q20] a mirror labels Erdos 203 "solved" | as marked in the reports | firm, trivial |
| 13 | Zudilin, arXiv 2409.10097 v1: digits of pi in bases 5 and 10 | withdrawn in v2 ("An obvious flaw") [READ P04, W2_R09] | firm; cite v2 |
| 14 | Unrefereed 2026 claims the reports met: Catalan's constant irrational (gap reported by Wachs), mu(pi) = 2, mu(log r) = 2, proofs of Erdos-Straus; Verger-Gaugry 2017 on Lehmer; [W2_R09] Kulik's texts (removed by Zenodo) | P08, R06, W2_R09 | unknown; never cite as theorems |

## 5. Leads

Each: statement; what it needs; size; why noticed; risk. Sources in brackets.

### 5a. Extensions of the project's own theorems

- **A1 Theorem N and K_b in Lean.** For b >= 5, b != 9: no q pi + q' log n (q' != 0, n >= 2 an integer) is a value;
  log y is a value iff a power of y is a product of orbit numbers. Needs the four pieces of the log-primes plan. Days
  to weeks. Noticed: closes BBG Example 4 in full. Risk: low; phrase it for integers.
- **A2 Rational bases.** Conjecture [P03]: a non-zero algebraic multiple of pi has a degree-1 formula with rational
  coefficients in a base (p/q)^B, p/q not an integer, iff p/q is a power of 3/2 or 4/3. Needs Zsigmondy for
  p^n - q^n ([W2_Q12] Tau Ceti has it for coprime naturals), the primes above q, Baker, the Kummer argument. Days for
  a search with p, q <= 200 [F3], weeks for a proof. Noticed: K-M call non-integer bases unexplored; same shape as
  Theorem L. Risk: 2.2, items 3 and 4.
- **A3 Every step n for b >= 5.** The numbers 1 - zeta/b^(1/n), zeta over all roots of unity, are multiplicatively
  independent (with -1) for b >= 5 not a perfect power; hence no zero relation and no algebraic multiple of pi at any
  step [R05 L1, R07 L2; general-step section 6]. Needs a primitive-prime lemma for b^(1/n) uniform in zeta, not in
  print [Q01] and in no formal library [W2_Q12]. Days to weeks. Noticed: an Okada-type criterion for geometric
  weights is missing in print [R07]. Risk: perfect powers; relations between the families of b and of b^(1/n).
- **A4 Steps 3, 4, 6 in bases 2 and 3.** Exact dimensions and bases of the spaces, with the series for 2 pi 3^(1/6)
  and pi sqrt(2) 3^(1/4) of the general-step summary [P11 L1]. Days to 2 weeks. Risk: Adegoke's general-base papers
  were not read in full. [W2_R09] Kulik's computed relation at (16, 12) over Q(2^(1/3)) is a step-3 case to compare.
- **A5 The unique-prime dictionary.** [W2_Q16, lead 1, sharper than Q03's] p has a binary formula iff for some n a
  "piece" of Phi_n(2) (its primitive part, or one Aurifeuillian half when n = 4 mod 8) is a power of p, and the
  prime dividing both n and Phi_n(2), if any, is itself in the set; decided at n = ord_p(2) [INFERRED there; checked
  by hand against the 15 primes of Theorem H]. Theorem P is the base-b form. Days. Noticed: joins Chamberland's list to the
  unique-prime literature (Yates, Caldwell-Dubner, Pomerance) and explains 38737. Risk: low.
- **A6 Arctangents.** An effective criterion for arctan(y/x) in bases 2 and 3; decide 5/9; prove that Bailey's 15
  arctangents are independent (a PSLQ observation in print); a table for denominators below 100 [P12 L3]. Days for
  the table, weeks for the criterion. Risk: low.
- **A7 pi sqrt(d) and L(1, chi).** For each fundamental discriminant D, |D| < 200: is pi sqrt(|D|), or
  sqrt(D) log(eps_D), a value in base 2, in base 3? In print: -4, -3, -8, 8, 5 in base 2 and -3 in base 3 [R02];
  [W2_Q14] OEIS A260658 is a base-8 formula for 4 pi/sqrt(27). Days to 2 weeks. Risk: a short list.
- **A8 Two bases.** The set of y with log y a value in a base 2^k and in a base 3^k; for each prime q the bases in
  which log q is a value [P05 L4, R02 4.3]. Days to weeks. Noticed: Lagarias's Question for simple poles.
- **A9 Quadratic and Gaussian bases.** (i) The dimension of rational-coefficient formulas for pi in the bases phi,
  1 + sqrt 2, 1 + sqrt 3, N <= 30, by exact computation [P03 L2]: 1 to 3 weeks; settles 2.2, item 3. (ii) A
  Machin-type exclusion in Z[phi] or Z[i] [P03 L3, Q01 L1]: weeks; no number-field Zsigmondy is formal anywhere.
- **A10 Degree 2, conditional.** The kernel of the symbol map on degree-2 sums against the counts of Bailey's Table 1
  [P02 lead A]. Days for a first run. Risk: conditional on period conjectures; nothing unconditional is in reach.
- **[W2_Q15] A11 Aurifeuillian halves, as a theorem.** For b in {2, 3, 5} and n in the Aurifeuillian class each half
  of Phi_n(b) has a prime of order n, except (2, 4), (2, 12), (2, 20), (3, 6). Needs a size bound for the halves
  (not found in print) and a finite check. Days. Noticed: the printed source is unreadable and its exceptions unclear.

### 5b. Formalization targets that others have asked for

- **B1 Chowla's problem.** Baker-Birch-Wirsing for prime q and the unweighted ASST theorem (sum f(n)/n is 0 or
  transcendental; L(1, chi) transcendental). Asked: Tau Ceti's roadmap lists the Baker corollaries [R01, W2_Q12]; no
  formal version found [Q06, R01]. Needs Baker (in hand) and Mathlib's L(1, chi) != 0, characters, cyclotomic Galois
  groups, Abel's limit theorem [all confirmed present, W2_Q19]. 2 to 4 weeks. [W2_Q11] With Okada's theorem added it
  would turn the parity certificates of C3 into formal proofs. Risk: nobody read the 1973 paper; Okada's 1982 proof
  is a modification of it.
- **B2 Baker corollary layer.** pi + log alpha, e^(b0) prod alpha_i^(b_i), independence of the logs of the primes,
  Gelfond-Schneider and Hermite-Lindemann as corollaries [P08 L1, R01 lead 2]. Days. Risk: it may already exist on
  Karatarakis's branches; [W2_Q12] Tau Ceti wants such work as a human-written roadmap, code by the contributor's
  own agents, no stacked PRs, files under 1250 lines.
- **B3 Dusart 2018, Proposition 5.4c.** [W2_Q13] Still `sorry` (`proposition_5_4c` in the PNT+ file Dusart.lean),
  with no issue and no claimant; the source calls it "likely not formalizable". It is small: 22115 pairs of
  consecutive primes, or a chain of 2745 witness primes below 4 * 10^5, plus rational bounds for log; the tightest
  case is x = 89693 (allowed 60.47, needed 60) [COMPUTED]. Days to 2 weeks. Rules: ask on Zulip and `claim`;
  disclose the tool; data in a `*_tables.lean` file; no `native_decide` if a receipt in teorth/IEANTN is wanted.
  Honest scope: it removes one `sorry` and makes nothing unconditional (2.2, item 11). Noticed: a way into an
  active community. Risk: a kernel sieve by another contributor (PR 1804) may absorb it; audit the statement first.
- **B4 Zsigmondy for Mathlib.** [W2_Q12] Confirmed missing in Mathlib (the 1306-line PR was withdrawn by deleting
  the fork; no reason given). Tau Ceti has the integer theorem and does not push upstream; upstreaming is "probably
  not the best use of effort". What the project has and no library has: the number-field statement (a prime ideal
  containing sqrt(b) - r), as a self-contained module or as a Tau Ceti roadmap proposal.
- **B5 Erdos 1948 for the Palomar registry.** sum 1/(t^n - 1) is irrational for every integer t >= 2 [Q05 lead 1].
  Days to 2 weeks. Risk: off the subject.
- **B6 BBP digit extraction, total correctness.** [W2_P15] Largely done elsewhere: metasecdev's repository has a
  guard depth for every n in base 16 (very large, unreviewed). New would be Bellard's and Huvent's formulas. Low.
- **B7 Primality in Lean.** [W2_Q18] Proth's theorem is not in Mathlib; with it, Gaussian-Mersenne norm primes
  (N - 1 = 2^((p+1)/2) times a smaller number) can be proved in the kernel with one exponentiation each; Mersenne
  primes beyond exponent 4423 (the present limit) by a chunked Lucas-Lehmer test. Days to weeks. Coq is far ahead
  (ECPP certificates to 65,050 digits); Lean has no ECPP checker. Also [Q04]: Brun's theorem, the prime race mod 4.
- **B8 Missing, though nobody asked** [W2_Q19 confirms each as absent]: the density 6/pi^2 (needs a notion of natural
  density first); Euler's product for pi/4 at s = 1 (weeks; the prime number theorem in progressions is now in
  Mathlib); Brouncker's fraction; normal numbers (P05); a WZ lemma with one 1/pi^2 series (P07); Stormer's criterion
  (P06). Chudnovsky's formula is wanted by Mathlib and lean-eval, and out of reach.

### 5c. Computations and certified tables

- **C1 Lists of primes with logarithm formulas.** Bases 2, 3, 5, 10 to a stated bound, each entry with its
  certificate; a correction of A104885 (38737, with the pair 433 * 38737) and an extension of A165132 (six terms
  now; the project has 31 below 10^6) [P12 L1, Q09 lead 1, W2_Q14, W2_Q17]. Before any comment: run the criterion on
  all 90 primes of Chamberland's table (ten need a factorization of a 40 to 100 digit number) so that one comment
  covers every failure. Days. Noticed by OEIS editors and the Compendium's maintainer. Risk: [W2_Q14] OEIS's AI
  policy (29 Aug 2026): the submitter verifies every term, writes every comment in his own words, no bulk
  submissions; only proved terms in the data. The lists are program output, not Lean per prime.
- **C2 Unique-prime tables.** Extend A161508 and relatives from Pomerance's appendix (count to be fixed: 2.2, item
  8); first tables for bases 3, 5, 6, 7, 12 [Q03; W2_Q16 lead 5: Pomerance invites exactly this]; [W2_Q17] extend
  A088962 to the paper's 108 values. Days. Risk: probable primes.
- **C3 The parity theorem for Erdos's conjecture.** [W2_Q11] The computation stands (2.2, item 2). Next, in order:
  read Murty-Saradha 2010, Murty-Pathak 2022 and Bharadwaj-Murty-Pathak 2025 for priority; a modular implementation
  to q about 3000; then a proof that for odd non-square q = 1 mod 4 the 2-adically saturated lattice of Okada's
  system contains a vector of odd coordinate sum (first target: squarefree q with three primes). Days to weeks.
  Noticed: it would settle an open conjecture for infinitely many q and leave the squares. Risk: prior print (about
  40% by W2_Q11's guess); no proof idea beyond a heuristic; squares such as 105^2 need another method.
- **C4 Machin census.** All minimal rational relations among pi and arctan(1/x), x <= 10^9, verified in Z[i] [P06
  lead A]. Days. Noticed: three-term formulas are known finite with no list. Risk: only "complete below X".
- **C5 Zero relations beyond Bailey's table.** Exact counts for N up to 240 and steps >= 3, compared with every row
  of Table 1 and the CARMA list [P11]; [W2_R09 lead 1] and with Kulik's 2233 frames, since a referee who finds that
  text will ask. Days. Risk: counting conventions.
- **C6 pi(x).** Recompute pi(10^27) with current primecount (3 days to 2 weeks on 24 cores by Q07's estimate, memory
  unknown), or a formal ladder pi(10^n) in Lean [Q07]. Risk: same algorithm family, so not an independent check.
- **C7 Small certified tables.** Lean certificates for the covering sets of 78557, 271129, 509203 [W2_Q20: none
  found in Lean]; consecutive smooth numbers and S-unit solutions for small S (R06); record objects (Q07).
- **Dropped by wave 2:** a covering for Erdos 203 (W2_Q20) and a proof of Gibbons's conjecture (W2_P14); see 2.2,
  item 11. Of the latter a conditional theorem and a verified spigot with its safety test remain possible (weeks).

### 5d. Top ten across the three lists (revised after wave 2; previous rank in brackets)

1. A1: Theorem N in Lean. Nearly done; answers a printed "failed to prove". (1)
2. C1: certified prime lists and the two OEIS entries, now with the cause of 38737. (2)
3. C3: the parity theorem for Erdos's conjecture: priority check, then a proof. [W2_Q11] The computation was
   reproduced, so this rises; it has the highest possible return and the highest risk. (6)
4. A3 with A4: every step n. Completes the classification in the project's own class. (3)
5. A2: rational bases, after 2.2 items 3 and 4. (4)
6. B1: Baker-Birch-Wirsing, Okada and unweighted ASST, formal; it also carries C3. (5)
7. A5 with C2: the unique-prime dictionary in W2_Q16's form, and its tables. (7)
8. B3: Dusart 5.4c. [W2_Q13] Sized and unclaimed; days; worth less than Q08 said. (9)
9. A6: the arctangent criterion and table, with 5/9. (8)
10. A7 with A8: pi sqrt(d), L(1, chi) and the two-bases statement. (10)

Before all of them: the write-up of Theorems L, M, G, N (P01 lead 1, R03 lead 1, R04 steps 1-5).

## 6. Presentation and publication

What R03, R04, P09, R01, P08, Q05 report, and [W2] what W2_R08, W2_P15, W2_Q12, W2_Q13, W2_Q14 add.

- **Framing.** Present Theorem L as a machine-checked proof of a statement that a standard reference asserts and
  whose cited source proves only a special case; cite BBG's Comment 10, the Buhler sentence and Zudilin. Lead with
  what was not found in print: G, M, N, C with Bailey's counts, E, K. Say "degree 1, rational coefficients, integer
  base; not a statement about computing digits" every time. [R03, P01]
- **[W2_P15] Claims to avoid:** "first Lean proof of the BBP formula", "first formalization of a BBP-type formula",
  "first formal proof that digit extraction is correct for all n". Safe: the classification, the optimality bound,
  the nonexistence theorems and the logarithm criterion have no formal or printed counterpart found; for Bellard's
  and Huvent's identities write "to our knowledge". Cite Bertot-Rideau-Thery, the two Lean repositories and, per
  W2_R09, BMP for the efficiency measure and Craig-Wood for Euler's formulas.
- **Do** [R03: the Leiden Declaration, Tao's FAQ, Boldt; R04: the Lean "did you prove it" page]: a short explanation
  in the author's own words; a literature search stated as such; a file with only the statements, in Mathlib's
  definitions, read by a third party; `lake build` clean, `#print axioms` shown, a comparator run; a statement
  dictionary; a specific disclosure (tool, version, what it did, who checked what; [W2_R08] the Leiden text asks for
  a "tool and computational resource disclosure" section); a tagged release with a DOI; an OSI-approved license.
- **Credit.** Baker's theorem is Karatarakis's unannounced proof and Bang's theorem is Tau Ceti's: name both, and
  write to Karatarakis first (R01).
- **Avoid.** Announcements before checks, social media first, mass mailing, viXra, long unexplained output, "first"
  or "new" without the checks of 2.2, LLM-written comments on GitHub, Zulip or OEIS, large AI-written pull requests.
- **Own words.** [W2_R08, read at the source] The Annals of Formalized Mathematics (AFM): "only human-authored
  manuscripts", disclosure of AI use for manuscript and code with tools and tasks, and of subsidized tool access.
  Journal of Integer Sequences (JIS): LLM-written or LLM-translated text is prohibited, LLM-suggested proofs must be
  credited, undisclosed use means rejection. Integers: wording must be the author's own, with a statement of AI use
  at the end. ITP 2027: no substantial AI-generated text. So the paper is written by the author; so are replies to
  reviewers. How "human-authored" is judged for an author who works with an assistant is stated nowhere.
- **Preprint server.** arXiv: since 10 Dec 2025 a first submission to math needs a personal endorsement unless the
  author has an institutional address and an accepted paper in the field [R04, W2_R08]. [W2_P15] The author of the
  Lean BBP repository, in the same position, is stalled: one expert declined (he does not use arXiv), another had
  not answered after two weeks. [W2_R08] arXiv is not needed for AFM, an overlay on HAL, arXiv and Zenodo alike.
  HAL: independent researchers do deposit (8,515 records carry that label [SNIPPET]); no written rule found. Zenodo:
  content "produced largely by generative AI without a verifiable connection to human research" is out of scope;
  the record should describe the AI's role. [W2_R09] Zenodo does remove: the Kulik records and account went on 30
  Oct 2026 as "out of scope" (that the AI clause was the ground is [INFERRED] by W2_R08).
- **Venues** [R04; W2_R08]: AFM (free; artifact mandatory, open source, main results linked to code; wants new
  mathematical insight, so the classification theorems qualify and a re-proof would not; single-blind; review time
  not stated; about eight papers so far; no confirmed unaffiliated author). JIS (free; LaTeX by e-mail to the
  editor; median 197 days). Integers (free; scope more combinatorial). ITP 2027 (abstract 8 Feb, paper 15 Feb 2027,
  16 pages; wants formalization method, not size). Not suitable: Formalized Mathematics (Mizar only), Journal of
  Formalized Reasoning (no issue since 2020). Still unread, pages blocked twice: Experimental Mathematics, Math.
  Comp., the Monthly, the Ramanujan Journal, Research in Number Theory, Journal of Automated Reasoning.
- **Mathlib.** AI use must be stated in the PR description and labelled `LLM-generated`; the contributor must
  understand and defend every line without AI; low-quality LLM PRs may be closed without comment [READ P09, R03,
  W2_Q12, W2_Q13]. Practice: PR 43144 (pi transcendental, AI-written, for the 100-theorems file) closed as not
  wanted there; a Stormer PR closed for AI-use policy [R06]; many disclosed `LLM-generated` PRs are open [R03,
  W2_Q19]; reviewers object to files over 1000 to 1500 lines [W2_Q12]. So: an own repository, small lemmas upstream.
- **[W2] Other projects' rules.** Tau Ceti (W2_Q12): AI-written code welcome, roadmaps written and approved by
  humans, "reusable foundations, not frontier research". PNT+ and teorth/IEANTN (W2_Q13): claim an issue, disclose
  the tool, at most three open AI-assisted PRs, "the AI wrote it" is no answer to a reviewer; statements there are
  sometimes false as printed, so audit by script first. OEIS (W2_Q14): see C1. Formal Conjectures and Palomar (Q05,
  P09): statements only; proofs of research problems through a registry entry, AI allowed if disclosed.
- **Asking an expert** [R04, thin]: one named recipient, why that person, one narrow question (is this the statement
  you meant; is it known; would you endorse), the Lean statement and the axioms in a few lines.
- **Climate** [R03, Q04]: after the announcement of 20 November every Lean claim meets close scrutiny, and reviewers
  say they owe AI-assisted papers no checking; the author has to lower the cost of checking.

## 7. Gaps after two waves

**Thin threads.** P07 (who proved which of Sun's conjectures after 2023), Q10 (the literature on the product for
pi/4), R07 and R01 (the Baker-method papers known through surveys), R02 (which L(1, chi) have formulas in print), P08
(independence measures of 1, pi, log 2), P10 (open Ramanujan Machine conjectures). No thread examined Theorems A, B, D
or the 7/24 measure against the literature. MathSciNet and Google Scholar were used by nobody. [W2] Wave 2 closed the
threads on Mathlib's contents, formal BBP work, Chamberland's paper, the OEIS entries, the Kulik texts and Okada's
criterion; it did not reach Buhler's proof, the K-M coefficients, rational bases, or the publishers' policies.

**Sources nobody could read** ([W2] read since wave 1, so off this list: Okada 1982, Chamberland 2003 in full,
Postnikova-Schinzel 1968, Kulik's text, Pomerance 2025, the AFM, JIS, Integers and ITP pages).
- On pi: the printed BBP paper (Math. Comp. 66, 1997); Takahashi 2020 and 2021; Huvent's page; Gourdon 2003; Lafont's
  2011 note (digest only); Broadhurst's "Vanishing polylogarithmic ladders" (2000, private); the Borwein-Chamberland
  manuscript; Chan 2008; the CARMA list of zero relations; [W2] the HOL Light BBP file; a build of metasecdev's repo.
- On periodic sums: ASST 2001; Saradha-Tijdeman 2003; Okada 1986; Baker-Birch-Wirsing 1973; [W2] Murty-Saradha 2010,
  Murty-Pathak 2022, Bharadwaj-Murty-Pathak 2025, Tijdeman 2008: the four that decide the novelty of C3.
- On primes: [W2] Schinzel 1962, 1963, 1974 and his Selecta, Stewart 1977 (paywalled: a library task); Carmichael
  1913; Granville-Pleasants 2006; Yates; Caldwell 1997; the Cunningham tables book; Berrizbeitia-Iskra 2010; Dusart
  2018 itself; Stormer 1895, 1896; Ennola 1972; the mersenneforum threads on pi(x); the pages of erdosproblems.com.
- Other: the author pages of Springer, Taylor and Francis, AMS and MAA; the Lean sources of the 20 November
  development; the Baker file of diaz-modulus-lean.

**A third wave, if wanted** (ten threads; wave 2 covered the earlier list's items on Okada, Schinzel, OEIS,
Pomerance, certificates and the Lean prime-number-theorem tasks):
1. (primes) Priority for the parity result: the four papers above, and any 2-adic or mod-2 argument on Okada's system.
2. (primes) Unique primes in bases 3, 5, 6, 7, 10, 12: Cunningham tables, factordb status, proved against probable.
3. (primes) Primitive divisors of p^n - q^n for a rational base; a size bound for Aurifeuillian halves (for A2, A11).
4. (primes) Primitive parts that are prime powers: Wieferich primes, Nagell-Ljunggren, OEIS A323748, Song's lists.
5. (primes) Primes with a prescribed divisibility of ord_p(b): the densities behind BBG's Appendix C and D(4).
6. (primes) Primes with formulas in two bases: coincidences of primitive parts in bases 2 and 3 (Lagarias's Question).
7. (primes) Lucas and Lehmer primitive divisors for phi, 1 + sqrt 2 and Z[i]: Carmichael, Bilu-Hanrot-Voutier (for A9).
8. (primes) Gaussian primes of x^2 + 1 and the Machin lists (for C4); pi(x) at 10^27 to 10^29: parity, audit trail.
9. (pi) The unread sources through a library: the printed BBP paper and Buhler, Takahashi, Huvent, Lafont, Broadhurst
   2000, ASST 2001, Gourdon 2003; and Adegoke's general-base papers in full, for steps n >= 3 and for pi sqrt(d).
10. (pi) Non-integer bases: K-M's published text, Bailey's formulas (132) and (133), Chan, the Borwein-Chamberland
    manuscript, Cloitre; with a recomputation of every displayed coefficient vector.
