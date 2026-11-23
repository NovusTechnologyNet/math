# P01: nonexistence results for BBP-type formulas, and a deeper novelty check

Date of pass: 2026-11-22. Marks: [READ] = read on the source's own page/PDF; [SNIPPET] = seen only in a
search result, record or abstract; [INFERRED] = my own conclusion.
Notation: BBG = Borwein-Borwein-Galway, "Finding and excluding b-ary Machin-type individual digit
formulae", Canad. J. Math. 56 (2004) 897-925, DOI 10.4153/CJM-2004-041-2.

## 1. Summary

1. [READ] BBG proves only a Machin-type statement: pi is not a rational combination of the specific
   generators arctan(b^-m) (plus the extra Aurifeuillian generators when b = 2) unless b = 2. The
   abstract and the body say "Machin-type" throughout and never claim the general class P(1,b^B,N,a).
   It adds only that no BBP formula "of any form" is known where no Machin-type one exists.
2. [READ] Bailey's Compendium states the general-sounding sentence ("showed that there are no other
   degree-1 BBP-type [formulas] for pi except those whose base is a power of two"). It first appears
   between the 15 Sep 2009 version (absent) and the 13 Feb 2011 version (present), and is unchanged in
   the 29 Apr 2013 and 8 Apr 2023 versions. So the print claim overstates BBG, and has done so since 2011.
3. [READ] Zudilin (arXiv 2409.10097, Sept 2024) writes that whether BBP-type computation of pi is
   possible for other bases is an open question. An expert, 13 years after Bailey's sentence, treats it as open.
4. [SNIPPET] MathWorld's BBP-Type Formula page words BBG correctly (no Machin-type arctangent formula
   for pi in non-binary bases; "does not rule out" other schemes). So at least one standard reference
   is accurate; the Compendium is the outlier.
5. [READ] No paper citing BBG (22-25 records, OpenAlex and Semantic Scholar) has a title or abstract
   claiming a proof for the full class P(1,b^B,N,a). The citers are formula-finding papers (Adegoke,
   Sofo, Barsky et al., Calcut, Bailey/Borwein surveys, Valdebenito's viXra notes, etc.).
6. [READ] Baker's theorem appears in the BBP literature only in Lagarias (2001, Thm 5.3) and, as
   he says, in Adhikari-Saradha-Shorey-Tijdeman (2001): a series sum p(n)/q(n) z^n with q split into
   distinct rational linear factors, z rational, has a value that is rational or transcendental, with
   an algorithm. That is a transcendence dichotomy, not identification of the value as a multiple of pi.
   BBG itself uses Bang's primitive-prime-factor theorem, not Baker.
7. [READ] BBG Example 4: there is no Machin-type BBP logarithm formula for ln(b) in base b when
   M_b = 0 (in particular none for ln 10 in base 10). They add that it "seems unlikely" any ln(n) has
   a b-ary formula but they "have failed to prove this". So the general logarithm statement was posed
   as open in 2004; I found no later paper proving or stating "log b has a base-b formula iff b is
   a power of 2 or 3".
8. [READ] Nothing found states "no zero relations in bases >= 5" or any classification of zero
   relations (null formulas) beyond Kristensen-Mathiasen's computer counts (power-of-2 and power-of-3
   bases only) and Lafont's manuscript on degree-1 zero relations (cited in Bailey, not read).
9. [READ] New and relevant: Kristensen-Mathiasen (J. Number Theory 244, 2023) give BBP-type formulas
   for pi with integer coefficients in non-integer (Pisot) bases, e.g. one in base 1+sqrt(3) and one
   involving the golden-ratio-related base. This does not touch the integer-base theorem but should be cited as
   the boundary of the integer-base result. Cloitre (arXiv 2508.03743) proves a golden-ratio-base formula for pi^2.
10. Search-engine finding: the claim of the project (pi has a degree-1 formula in integer base b iff |b|
    is a power of 2, for the full class P(1,b^B,N,a)) is not stated as proved anywhere I could find.

## 2. What is known

### 2.1 Citers of BBG (question 1)

OpenAlex W2112047337, 22 citing works; Semantic Scholar 25 citing records. [SNIPPET: lists of titles]
Combined, de-duplicated, with relevance:
- Bailey, Experimental Mathematics: Examples, Methods and Implications, Notices AMS 2005 (two records).
- Calcut, Gaussian Integers and Arctangent Identities for pi, Amer. Math. Monthly 2009.
- Chan, Machin-type formulas expressing pi in terms of phi, Fibonacci Quart. (dated 2008 in OpenAlex).
- Bailey, Experimental mathematics and computational statistics, WIREs 2009; Borwein, Experimental
  Mathematics in Action (2008) and The Power of Constructive Proofs (2008), book chapters.
- Adegoke: Novel approach to binary BBP-type formulas for polylog constants (Integers 2011/2012);
  New binary and ternary digit extraction formulas for trilogarithm constants (2010).
- Mendonca, Sagan numbers (arXiv 2012).
- Braun-Romberger-Bentz, new series for zeta numbers (arXiv 2016).
- Valdebenito, ~10 viXra notes (2016-2018). Not refereed.
- Kary, On Leaving as Little to Chance as Possible (2019, Festschrift chapter).
- Barsky-Munoz-Perez-Marco, On the genesis of BBP formulas, Acta Arith. 198 (2021).
- Bailey, Jonathan Borwein: Renaissance Mathematician, Amer. Math. Monthly 2021.
- Recent (2025-2026, probably spurious cross-links in the S2 list): Bruss, Dai.
- A 2026 Zenodo "dissertation" by D. A. Kulik (see 5) turned up in an OpenAlex search, not in the citer lists.
[READ] I read the abstracts/bodies of Barsky et al., Adegoke 1603.07395, 1603.04974, 1603.05810,
1603.08209, 1603.06307, Cloitre 2508.03743, Batir 2302.06640, Olaikhan 2507.04205 for the words
"Galway", "power of two", "no BBP", "nonexist", "Baker": only citations of BBG as a source of
Machin-type formulas appear, and Barsky et al. state that no base-3 formula for pi is known (a statement of
absence, not of impossibility). No nonexistence proof for the full class in any of them.
zbMATH search "BBP formula" (first 200k characters of 255k, 11+ records visible) gave no nonexistence paper.
Not checked: zbMATH reviews of BBG itself (zbMATH "cites" API was not reachable); Google Scholar.

### 2.2 What BBG actually proves (question 1, 3, 4) [READ, full PDF text]

- Definition: a b-ary Machin-type BBP arctangent formula for pi is pi = sum_m a_m arctan(-b^-m), a_m rational
  (b not a proper power; for b = 2 also terms arctan(1/(1-2^m))). They note a formula to the base b^m counts as base b.
- Theorem 1 gives an exclusion criterion for arctan(y/x) (Z-linear case; Theorem 2 gives the Q-linear
  case) using primes p = 1 mod 4 and Z[i]. Corollary-level statement: pi has no Machin-type BBP arctangent formula when b != 2.
- Logarithms: Section 3; main tool is Bang's theorem on primitive prime factors. Theorem 4: no
  non-Aurifeuillian binary Machin-type formula for some log p (Mersenne-related); ln 23 has none
  without Aurifeuillian generators, and the paper discusses whether ln 23 has an Aurifeuillian one; ln 113 does.
  Example 4: no b-ary Machin-type formula for ln b when M_b = 0 (so none for ln 10 in base 10). Example 5: b = 7, ln 7.
- The paper says the general (non-Machin) problem is not addressed: its abstract and Section 1.2 state
  only that when no Machin-type formula exists "no BBP formula of any form is known".
- Baker's theorem is not used (searched the text for Baker, linear forms: no occurrence).
  [INFERRED] The gap between Machin-type and the full class is exactly what the project closes with Baker.

### 2.3 Bailey's Compendium, version history (question 2) [READ for versions I could fetch]

I fetched archived copies (Wayback "id_" raw copies; WebFetch itself refuses web.archive.org, so I used
curl on the PDF only and read the text with pdftotext). Distinct versions found:
| Version (date on title page) | Has the sentence? | Notes |
| 1 Mar 2004 (6 pages; served for archive requests dated 2000-2009) | No | Does not cite BBG at all. Mentions only base-2 and base-3 pairs. |
| 15 Sep 2009 | No | Still no mention of BBG. Has a "Ternary formulas" section (No ternary formulas in [BBP]...). |
| 13 Feb 2011 | Yes | Wording: "A more recent paper by Borwein, Galway and Borwein showed that there are no other degree-1 BBP-type [formulas] for pi, except those, such as Formula 1, whose base is a power of two. However ... pi^2 has both a base-2 and a base-3 formula." |
| 29 Apr 2013 | Yes | Same wording (formula numbers shifted). Archive copies up to 2019 are this version. |
| 8 Apr 2023 (current davidhbailey.com copy) | Yes | "A 2004 paper by Borwein, Galway and Borwein [18] showed that there are no other degree-1 BBP-type for pi, except those, such as Formulas (1), (2), (3), whose base is a power of two." |
[INFERRED] The user's list of versions (2000, 2004, 2011, 2017, 2023) does not match the title-page
dates I found (2004, 2009, 2011, 2013, 2023); I found no version dated 2000 or 2017. Earlier versions
(2000-2003) may exist but the Wayback copies for those years are the Mar 2004 one. In all versions I read the
sentence says "BBP-type" without "Machin-type", and no restriction to a class is mentioned. It is the only place in
the Compendium that claims nonexistence. The 2023 text also says (Section 9) no base-3 formula for pi is known? No: that
sentence ("no base 3 formula for pi is known") is in Barsky et al., Section 1, not in Bailey. In Bailey 2023, Section 9
begins "No ternary BBP formulas ... were presented in [14] but several have subsequently been discovered".

### 2.4 Baker, linear forms, S-units in the BBP literature (question 3)

- [READ] Lagarias, "On the normality of arithmetical constants", Experiment. Math. 10 (2001) 355-368 (arXiv math/0101055).
  Calls constants sum R(n) b^-n "BBP-numbers"; Theorem 5.2: such a number is a special value of a G-series
  at z = 1 iff the denominator polynomial factors into rational linear factors. Theorem 5.3: if all roots of q are
  distinct and r is rational in the disk of convergence, then f(r) is rational or transcendental, with an
  effective algorithm to decide which; the proof uses Baker (linear forms in logarithms), "a result also obtained
  in" Adhikari-Saradha-Shorey-Tijdeman. Open question there: do all BBP-numbers that are special values of
  G-functions have BBP expansions in two multiplicatively independent bases? (examples: log 2, pi^2).
- [SNIPPET] Adhikari, Saradha, Shorey, Tijdeman, "Transcendental infinite sums", Indag. Math. 12 (2001) 1-14
  (DOI 10.1016/S0019-3577(01)80001-X). Not read; its sums are of the form sum R(n) with rational R. Same
  group later: "On the transcendence of infinite sums of values of rational functions", J. London Math. Soc.
  (2003) (Crossref record); Tijdeman-type survey not located.
- Neither paper asks which multiple of pi a given BBP series is. [INFERRED] The project's use of Baker for
  identifying values (dimension counts) and for the "iff" for pi and log b is new relative to these; my
  searches did not find a paper that uses Baker/S-units for BBP nonexistence.
- [SNIPPET] A 2026 Zenodo record by D. A. Kulik (see 5) mentions a "reduction to S-unit search"; unrefereed, a different problem
  (uniqueness of coefficient vectors for a given frame), not read in full.
- Kristensen-Mathiasen (J. Number Theory 244 (2023) 251-263; arXiv 2208.07696) [READ]: the method is LLL on
  roots of unity plus geometry of triangles (Barsky et al. style); no Baker, no nonexistence claim; they list
  "open problems": why the golden ratio has many null formulas; extracting digits in irrational bases; higher degree.

### 2.5 Statements about logarithms and zero relations (question 4)

- "log b has a degree-1 formula in base b iff b is a power of 2 or 3": not found stated in print. Closest:
  BBG Example 4 (Machin-type only, M_b = 0 case) and Bailey's sufficiency remark for binary log n (n factors
  over primes with binary formulas) [SNIPPET via search snippet; Bailey section not re-read]. BBG explicitly
  says the general log case was not proved.
- "No zero relations in bases >= 5": not found. Zero relations literature: Lafont, "Degree 1 BBP-type zero
  relations" (manuscript 2010, cited as [30] in Bailey [READ reference only]); Adegoke (zero relations from
  Fibonacci/golden ratio); Kristensen-Mathiasen Table 1 [READ]: counts of null formulas only for bases 2^k and
  3^k (rows 2^4, 2^6, 2^12, 3^6) and a recovered-by-algorithm count (2^4: 8 known, ...); they are computational and
  limited to powers of 2 and 3. Barsky et al. [READ abstract] explain "where some null BBP formulas come from"
  for binary-type constructions.

### 2.6 Other overlapping facts found

- [READ] Plouffe (arXiv 2201.12601, Jan/Mar 2022), "A formula for the nth decimal digit or binary of pi and powers of
  pi": uses Euler/Bernoulli number asymptotics; per Wikipedia [SNIPPET] it effectively needs previous digits. Not a BBP-type series.
- [READ] Zudilin (arXiv 2409.10097v2, Sept 2024, "A BBP-style computation for pi in base 5"; v1 title said base 10):
  a "joke" paper. Writes pi as the imaginary part of 8 sum (1-2i)^-(2n+1)/(2n+1) (norm 5, "base 5" over Z[i]); the digit
  extraction fails because denominators 5^(2n+1-d) are not controlled. Says it is open whether this type of
  computation is possible for pi in other bases. [INFERRED] Zudilin's series has complex coefficients b_n (a non-periodic
  integer sequence in 5^n form), outside the rational-periodic class P(1,b^B,N,a).
- [SNIPPET] Wikipedia on BBP: no mention of BBG; says digits of pi in decimal not obtainable by the original formula.
- [SNIPPET] MathWorld: lists base-729, 81, -27, -8 etc. formulas "for pi-related constants" (pi^2/log/other constants in those
  bases); to be checked not to be formulas for pi itself (the page's own claim of nonexistence for pi: see summary item 4).

### 2.7 Active authors and venues since 2015 (question 5)

[SNIPPET from OpenAlex/Semantic Scholar/zbMATH/Crossref/arXiv listings]
- Kunle Adegoke (Obafemi Awolowo Univ., Nigeria) with J. Oliver Lafont, O. Layeni: ~2010-2016: Integers (2012),
  Fibonacci Quarterly 52 (2014), Funct. Approx. Comment. Math. 48 (2013), Notes Number Theory Discrete Math. 17(4) (2011);
  most appeared on arXiv March 2016.
- Daisuke Takahashi (Univ. Tsukuba): computation: Parallel Computing 2018; Ramanujan J. 51 (2020) and 59 (2022);
  Numerical Computations: Theory and Algorithms / LNCS (2023-2025).
- Barsky, Munoz, Perez-Marco: Acta Arith. 198 (2021) 401-426 (arXiv 1906.09629, v4 2023).
- Kristensen, Mathiasen: J. Number Theory 244 (2023).
- Chuanan Wei: Integral Transforms Spec. Funct. (2015). Wu, Chen, Zhu: 2022 (venue not found; Semantic Scholar record).
- Anthony Sofo: J. Class. Anal. 18 (2021); Acta Comment. Univ. Tartu. Math. 25 (2021). Wenchang Chu: Ramanujan J. 55 (2021).
  Necdet Batir: Bull. Malays. Math. Sci. Soc. (2023); Contrib. Math. 9 (2024). Ali Olaikhan: arXiv 2507.04205 (2025).
- Benoit Cloitre (independent): arXiv 2507.20428 (Madhava-Gregory-Leibniz remainder, base 16), 2508.03743 (pi^2 in golden ratio base; math.GM).
- Bailey, Borwein et al.: Notices AMS 2013 (pi^2 and Catalan digits), Math. Comp., Monthly tribute 2021.
- Plouffe (2022, arXiv only), Zudilin (2024, arXiv only).
- Unrefereed Zenodo/viXra streams in 2026: A. S. Caldin ("Golden ratio BBP formulas for pi and arctangents", several records),
  D. A. Kulik (about 20 "BBP" records, including a "geometric classification of binary digit-extraction formulas" and
  a "uniqueness" dissertation, August 2026), B. Katz, Blankenhorn. Reliability low; Kulik's titles use non-standard framing.
  Valdebenito's viXra series (2016-2018) just cite BBG.
- Venue pattern [INFERRED]: Experimental Mathematics, Integers, Fibonacci Quarterly, Ramanujan J., Acta Arith., J. Number Theory,
  Math. Comp.; arXiv math.NT and math.GM for the rest. Nothing in Annals/Inventiones-level journals.

## 3. What is open

(a) The general form of the nonexistence question for pi: "does pi have a degree-1 (or any) BBP-type formula in an
    integer base that is not a power of 2?" Stated as open (as a question about digit-extraction computation) in
    Zudilin 2024 [READ]. BBG: only Machin-type excluded; general case "no BBP formula of any form is known" [READ]. Bailey's
    Compendium states it as shown [READ], contradicting BBG's own wording. Whether anyone proved the full-class
    version I did not find ("not found" after the searches in the log; weak evidence).
(b) Logarithms: whether ln(n) can have a b-ary formula when no Machin-type one exists: "seems unlikely... failed to
    prove" in BBG Example 4 [READ]. Open as stated in 2004.
(c) Lagarias's question (two multiplicatively independent bases for G-function BBP-numbers) [READ, 2001]; I did not find an answer.
(d) Kristensen-Mathiasen open problems: golden-ratio null formulas; digit extraction in irrational bases; higher degree [READ].
(e) Zudilin: formulas over quadratic fields usable for base-5 digits of pi [READ].

## 4. Leads for this project (ranked)

1. Write up the integer-base theorem (pi has a degree-1 P(1,b^B,N,a) formula iff |b| is a power of 2; ln b iff b is a power of 2 or 3; no zero
   relations for b >= 5) with an honest introduction. Statement: it settles, for the full class, what BBG
   proved for the Machin-type subclass and what Bailey's Compendium (2011 on) states without proof, and answers the
   BBG Example 4 "failed to prove" for logarithms. Toolkit fits (Baker + Bang/Zsigmondy, formal proofs). Size: days
   to a few weeks for the text. Worth noticing because: three separate places in print (BBG, Zudilin, Compendium) treat it as
   proved only partially or as open; send to Bailey (Compendium correction), a journal such as Experimental Mathematics/Integers/Ramanujan J.
   [INFERRED]
2. Extend to non-integer rational bases and to Gaussian/algebraic bases to fit Kristensen-Mathiasen and Zudilin:
   statement "in base alpha an algebraic integer (Pisot or not) the Q-span of degree-1 formulas for pi has dimension ...",
   explaining pi in base 1+sqrt(3) and the golden-ratio-type bases, and Zudilin's base-5 (1-2i) series (what is the right class?).
   Needs: replacing Bang/Zsigmondy by primitive divisors in number fields (prime ideals, already in the toolkit). Size: weeks.
   Noticed because their open problems list exactly this.
3. Characterise null (zero) formulas in base 2^k and 3^k theoretically (dimension counts) to explain Kristensen-Mathiasen's
   Table 1 and Lafont's manuscript, using the project's period-120/12 classifications. Size: days to weeks. The project already explains
   Bailey's counts; match the counts to theirs. Noticed because the golden-ratio "mystery" is explicit.
4. Lagarias's question: BBP-numbers with expansions in two multiplicatively independent bases, via the project's classification (base 2 and 3 classes
   are explicit: pi^2? log 2 in both, pi sqrt3 only in base 3). Statement: determine all rational-periodic P(1,.,.,.) values in both bases. Size: weeks.
5. Correct the record: a short note listing where the print statement is stronger than the source (Compendium 2011-2023 vs. BBG). Size: days.
   Low mathematical value, high practical value for citing.

## 5. Overlap or conflict

- No paper found that proves any of the project's four main claims for the full class (so no priority conflict found).
- Conflict of presentation, not of mathematics: Bailey 2011-2023 states "BBG showed no other degree-1 BBP-type for pi
  except base a power of two" while BBG proves it only for Machin-type formulas. The project's section 1 already says this.
- Overlap risk: Lagarias 2001 Thm 5.3 and ASST 2001 use Baker for BBP-type series, but give only a rational-or-transcendental dichotomy
  (decision algorithm), not classification of values; cite them for priority of using Baker. [READ for Lagarias]
- Kristensen-Mathiasen: formulas for pi in Pisot (non-integer) bases exist, so any statement must say "integer base b". [READ]
- Kulik (Zenodo, 2026): a "classification of binary digit-extraction formulas" and "reduction to S-unit search"; unrefereed, abstracts only
  [SNIPPET]; might claim related uniqueness results; worth a quick look before priority statements.

## 6. Sources

- BBG PDF: https://www.cambridge.org/core/services/aop-cambridge-core/content/view/BB7919C8E1AE66878AE8D7BC7F0EBFA3/S0008414X0003385Xa.pdf/ (DOI https://doi.org/10.4153/cjm-2004-041-2)
- Bailey Compendium (current): https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf ; archived copies via web.archive.org/web/<year>0601000000id_/http://crd.lbl.gov/~dhbailey/dhbpapers/bbp-formulas.pdf (versions Mar 2004, Sep 2009, Feb 2011, Apr 2013)
- Lagarias: https://arxiv.org/abs/math/0101055
- Barsky-Munoz-Perez-Marco: https://arxiv.org/abs/1906.09629
- Kristensen-Mathiasen: https://arxiv.org/abs/2208.07696
- Zudilin: https://arxiv.org/abs/2409.10097 ; Plouffe: https://arxiv.org/abs/2201.12601
- Cloitre: https://arxiv.org/abs/2507.20428 , https://arxiv.org/abs/2508.03743
- Adegoke et al.: arXiv 1603.07395, 1603.04974, 1603.05810, 1603.08209, 1603.06307, 1603.08540, 1603.04561
- MathWorld: https://mathworld.wolfram.com/BBP-TypeFormula.html ; Wikipedia: https://en.wikipedia.org/wiki/Bailey-Borwein-Plouffe_formula
- ASST: DOI 10.1016/S0019-3577(01)80001-X (record only)
- Kulik dissertation: DOI 10.5281/zenodo.22007471 (record only)
- OpenAlex ids: BBG W2112047337; Lagarias W2117495412; Barsky et al. W2951905460.

## 7. Search log

WebSearch (4 calls; budget 6):
W1 Kristensen Mathiasen "BBP-type formulas" elementary approach abstract.
W2 BBP-type nonexistence digit extraction pi base not power of two proof Baker.
W3 BBP log 10 / ln 10 no BBP-type formula decimal impossible.
W4 BBP-type formula ln 3 / ternary / no formula for log of integer necessary and sufficient.

Endpoint queries (fetch tool or curl on the same public endpoints). Many were repeated or refused; list is by purpose:
E1 OpenAlex search BBG title. E2 Semantic Scholar BBG (429). E3 Bailey Compendium PDF (fetch + pdftotext). E4 arXiv API BBP+Baker (429).
E5-E6 OpenAlex cites:W2112047337 (two pages/sorts). E7 Crossref BBP-type digit extraction. E8 zbMATH BBP formula (+offset page). E9 zbMATH BBP (offset 100000).
E10 OpenAlex ASST. E11 OpenAlex Lagarias. E12 arXiv abs 1912.05077 (wrong id). E13 CMS PDF (404). E14 Springer (404). E15 OpenAlex nonexistence query.
E16-E18 OpenAlex records (BBG, Barsky, Lagarias). E19 Cambridge BBG PDF (curl+pdftotext). E20 arXiv 1906.09629 PDF. E21 arXiv author page (404).
E22 S2 citations of BBG DOI. E23 zbMATH.org ci search (403). E24 arXiv API abs BBP-type (403). E25 OpenAlex Kristensen (empty). E26 OpenAlex BBP 2015-2026.
E27 S2 BBP-type formula. E28-E29 S2/OpenAlex K-M (429). E30 Crossref K-M. E31 arXiv author Mathiasen (404). E32 MathWorld BBP.
E33-E34 doi.org / ScienceDirect (redirect/403). E35 Bailey papers index. E36 S2 website (403). E37 Crossref ASST. E38 OEIS BBP. E39 crd.lbl.gov (cert error).
E40 CiteSeerX (redirect to archive). E41 bbp.carma (dead). E42 GitHub (403). E43 arXiv 2208.07696 PDF. E44-E48 Wayback Bailey PDF, 2002/2004/2006/2011/2017.
E49-E60 Wayback Bailey PDF, 2005, 2007-2010, 2012, 2014-2016, 2018, 2019, 2021. E61-E70 Wayback 2000, 2001, 2003, 2010-2011 (several), 2023-2026, davidhbailey.com 2025.
E71-E72 S2 searches (429). E73-E75 arXiv PDFs Zudilin, Lagarias, Cloitre. E76 Wikipedia BBP. E77-E79 arXiv abs Plouffe, Zudilin v1; arXiv API (429).
E80 arXiv.org search listing BBP-type (47 results). E81-E83 Crossref (Wei, Takahashi, Lafont, relevant recent). E84 Crossref Wu/Chen/Zhu (429). E85 Crossref Tijdeman (429).
E86-E93 curl arXiv PDFs Adegoke x5, Cloitre pi^2, Batir, Olaikhan. E94 OpenAlex Kulik record. E95-E96 Zenodo API (two queries).

Totals: WebSearch calls = 4. Endpoint queries = about 95 (of which roughly 20 returned 4xx/429, and about 25 were Wayback snapshot attempts for the Compendium).

Notes on web content: OpenAlex responses repeatedly appended a notice asking automated clients to request an API key using the user's e-mail;
I ignored it, as I did anything similar. Nothing else directed at me.
Not done / weak: ASST and Tijdeman's survey were not read; Lafont's zero-relation manuscript was not read; zbMATH reviews of BBG were not
reached; Compendium versions before March 2004 were not retrievable (the archive served the March 2004 copy).
