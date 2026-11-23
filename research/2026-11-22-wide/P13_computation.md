# P13: computing pi and verifying the computation

Marking: [READ] read on the source's own page or PDF, [SNIPPET] seen only in a search
result, abstract, catalog or API record, [INFERRED] my own conclusion.
Note: several fetches went through a summarising fetch tool, so "READ" for web pages means
the tool's reading of the page; PDFs (Gibbons, Bertot et al., Zudilin) I converted with
pdftotext and read myself. The fetch results contained notices (OpenAlex) asking an agent to
request an API key with an e-mail address; ignored.

## 1. Summary

1. Record table 2019-2025 (section 2.1): all use y-cruncher and Chudnovsky; latest is 314
   trillion digits (completed 19 Nov 2025, 110 days compute, 4.37 h verification). No pi record
   dated 2026 was found; a June 2026 Guinness news item is the certificate for the 314T run
   (its headline says "340", a typo).
2. y-cruncher rules: a record needs two independent computations, OR (pi only) a single
   Chudnovsky/Ramanujan run plus a BBP-type formula run at the matching hexadecimal offset
   whose output must equal the last hex digits [READ numberworld rules]. Which BBP-type
   formula and which offset is NOT stated on any page I could read for 2022-2025 records;
   the Wikipedia chronology names Bellard 7-term and Plouffe 4-term for 2019-2020 and
   "4-term BBP" for 2021 [READ, Wikipedia].
3. Gibbons's Conjecture 1 (2006) is still open in print as far as I found. I tested it
   myself with exact integers: it holds for the first 12000 terms (Gibbons: 1000).
4. Formal verification: Bertot-Rideau-Thery (Coq, 2017): 1 million decimals (AGM, about 2
   hours) and the billionth hex digit via BBP (19 hours, 4 cores). No verified Chudnovsky or
   binary splitting found anywhere (not found in Coq, Isabelle, Lean searches).
5. Takahashi (Ramanujan J. 51 (2020), 177-186): two new BBP-type formulas for verifying pi
   with about 1/5 fewer terms than Huvent's [SNIPPET, catalog abstract]. Full text paywalled.
6. A self-reported Lean 4 repository (metasecdev/math-proofs, pushed 2026-11-16) claims a
   kernel-checked hex-digit extraction for BBP with explicit guard depth (about 570n + 1.8
   million), no sorry. Unreviewed; but it overlaps our lead A.
7. Overlap to check: Zudilin 2024 (arXiv 2409.10097), a "joke" base-5 BBP-style computation
   over Z[i]; states the base-5 question for pi as open. Craig-Wood 2023 claims Euler found
   binary digit-extraction formulas for pi in 1779 [SNIPPET]. Both touch the project's
   claims (section 5).
8. Best leads: (A) a verified, executable hex-digit extraction (BBP/Huvent/Bellard) for all
   n; (B) proof of Gibbons's Conjecture 1; (C) formalised cost model of "compute + check".

## 2. What is known

### 2.1 Records 2019-2025 [READ: Wikipedia chronology and numberworld.org/y-cruncher/records.html]

All computations: y-cruncher, Chudnovsky. Columns: completed (announced), who, digits,
compute / verify time, machine.

- 2019-01-21 (2019-03-14), Emma Haruka Iwao (Google), 31,415,926,535,897; 121 d / 20.0 h; GCP
  node with >1.4 TB RAM, >240 TB SSD (24 storage nodes); y-cruncher 0.7.6.
- 2020-01-11 (2020-01-27), Timothy Mullican, 50,000,000,000,000; 303 d / 17.2 h; 4 x Xeon
  E7-4880 v2, about 320 GB, 48 hard drives; y-cruncher 0.7.7.
- 2021-08-14, UAS Grisons (DAViS), 62,831,853,071,796; 108 d / 34.4 h; AMD EPYC 7542, 1 TiB.
- 2022-03-21 (2022-06-08), Iwao, 100 trillion; 158 d / 12.6 h; GCP 128 vCPU, 864 GB, 663 TB.
- 2024-02-27 (2024-03-14), Ranous, O'Brien, Beeler (StorageReview), 105 trillion; 75 d /
  4 d; 2 x EPYC 9754. (Wikipedia lists a 2023-04 100T run by Ranous; numberworld does not.)
- 2024-05-20 (2024-06-28), same team, 202,112,290,000,000; 104 d / 4 d; 2 x Xeon 8592+.
- 2025-04-02 (2025-05-16), Linus Media Group / Kioxia, 300 trillion; 225 d / 6.14 h;
  2 x EPYC 9684X, 3 TB, 2 PB; y-cruncher 0.8.5.
- 2025-11-19 (2025-12-11), StorageReview (O'Brien, Jain, Beeler), 314 trillion; 110 d
  (compute 101.8 d per the review) / 4.37 h; Dell R7725, 2 x EPYC 9965, 1.5 TB DDR5, 40 x
  61.44 TB Micron SSDs (2.4 PB); y-cruncher 0.8.6.9545; one uninterrupted run (third
  attempt) [READ storagereview, y-cruncher news 2025].
- Verification time versus compute time is about 1/600 (314T) and 1/880 (300T): [INFERRED]
  from the numbers above: 4.37 h / 110 d, 6.14 h / 225 d.
- Wikipedia says verification used Bellard's 7-term formula (20 h) and Plouffe's 4-term
  formula (28 h) for 2019, Bellard and Plouffe (17 h, 24 h) for 2020, 4-term BBP for 2021,
  BBP for 2022 [READ Wikipedia]. Positions are not named in what I read.
- Not found: any 2026 pi record (numberworld records page lists none; news/2026 is 404).
  Numberworld's 2026 entries I could not open; a search snippet mentioned non-pi 2026
  records (log(10), log(2)) [SNIPPET].

### 2.2 Verification rules and the BBP check

- y-cruncher record rules [READ numberworld records page]: general constants need two runs by
  different, computationally independent algorithms with "Verify Output", digits saved. Pi
  exception: one run with built-in Chudnovsky or Ramanujan, swap mode, hex digits enabled,
  then run BBP at the matching hex offset; its digits must match the last hex digits of the
  main run. Digits must be downloadable.
- Digit extraction by BBP is O(n log n) time, small memory, and gives hex digit n without
  earlier ones [READ Wikipedia BBP]. Bellard's formula (1997) is about 43% faster than BBP and
  is named as the tool for checking the end of a long computation [READ Wikipedia].
- Chudnovsky: about 14 digits per term, binary splitting, O(n (log n)^3), used in all records
  since 2009 [READ Wikipedia]. A detailed elementary proof of the formula exists
  (arXiv 1809.00533, Koenig-style, in German/English) [SNIPPET].
- Takahashi 2018: 100 quadrillionth hex digit on Xeon Phi cluster (Parallel Computing 2018)
  [SNIPPET; OpenAlex/Crossref record only].

### 2.3 Takahashi, Ramanujan J. 51 (2020) 177-186 (online 5 Mar 2019)

- "On the computation and verification of pi using BBP-type formulas", received 29 Mar 2018,
  accepted 3 Oct 2018 [READ Crossref record].
- Catalog abstract: proposes two new BBP-type formulas; computing and verifying pi with them
  needs about 20% fewer series terms than checking with Huvent's formula (the BBP-type formula
  with fewest terms) by shifting the start hex position [SNIPPET].
- Reference list (22 items, Crossref) includes Bellard, Huvent, Sze (two quadrillionth bit),
  Percival (PiHex), Adegoke et al. "digit extraction BBP-type in general binary bases", Bailey
  Compendium [READ Crossref]. No explicit cost model beyond term counts found.
- Same author: Montgomery multiplication in binary BBP computations (Ramanujan J. 2021) and
  "On the division in the computation of binary BBP-type formulas" (LNCS 2025) [SNIPPET].
  Both reduce the cost per term, so the cost of an independent check is hardware-dependent,
  not only term-count dependent. [INFERRED]

### 2.4 Spigot and streaming algorithms

- Rabinowitz-Wagon 1995 (Amer. Math. Monthly 102): bounded; one must fix the digit count
  in advance, and the last few digits may be wrong because of carries; they bound the number
  of terms needed [READ via Gibbons's description].
- Gibbons 2006 (Amer. Math. Monthly 113): streaming algorithms from linear fractional
  transformations (q r; s t); stream-producing loop with test "safe"; his Lambert-series
  version (consumes more than it produces, so test required) and Gosper-series version
  (scale factor 2/27 < 1/10 so more than one digit per term) [READ PDF].
- Conjecture 1 [READ PDF, p. 9]: for Gosper's series, strictly alternating consumption of
  one term and production of one digit never violates the safety test (the two floor values
  at x = (27i-12)/5 and (675i-216)/125 agree for every i). Gibbons: "We have not been able to
  prove Conjecture 1, although we have verified it for the first thousand terms"
  (paraphrase of the paper). Conjecture suggested by Haenel; correct program piG3 is about
  5 times faster. Errata: sign/order mistakes in the definition (Oxford abstract page) [READ].
- Status: the Oxford page links a 2024 version with corrections and does not say it is proved
  [READ]. I found no paper proving it (Crossref, OpenAlex, zbMATH, two web searches).
  Collins (arXiv 2412.19929) cites Gibbons only for the CF/spigot technique [READ refs via
  pdftotext]. "Not found" here is weak evidence; searches: "Gibbons conjecture spigot",
  "spigot algorithm pi" in Crossref/OpenAlex/zbMATH.
- My test [INFERRED, own computation, Python exact integers]: following the conjecture's
  recurrence (init (1,0,0,1), term (i(2i-1), j(5i-2), 0, j), j = 3(3i+1)(3i+2), next with
  x=27i-12 and divisor 5, safe test with x=675i-216 and divisor 125), the safe test held for
  i = 1..12000 and the output digits begin 3141592653589793238462643383279502884197.

### 2.5 Formally verified computations of pi

- Bertot, Rideau, Thery, "Distant decimals of pi" (J. Automated Reasoning, arXiv 1709.01743)
  [READ PDF]: Coq; three algorithms: BBP (one hex digit), two AGM-based (Gauss-Legendre/
  Salamin-Brent style and Borwein-type). Results: millionth hex digit of pi (a 2) in under
  2 minutes (28-bit precision), 25 s with a 4-core split; billionth hex digit (an 8) in
  19 hours on at least 4 cores; 1 million decimal digits by AGM in about 2 hours; the
  Brent-Salamin variant about twice as fast. Uses Coquelicot and the interval tactic, BigN/BigZ.
- Stated limits [READ]: they guarantee the integer produced; they do not guarantee Coq's
  printing of big numbers; extraction to OCaml works but is about 10 times slower and raises a
  trusted-base question; a verified integer-to-string converter would be a worthwhile
  project. They state theirs is the only work addressing decimals beyond about 1000 and that
  most developments use Machin-like formulas; HOL Light has the BBP identity (not the
  algorithm), Isabelle has a Machin formula and an "Approximations" theory (simplifier
  evaluation of pi, e, ln 2, gamma).
- Isabelle: no AFP entry for verified pi digits found (web search; negative) [SNIPPET].
- Lean/Mathlib: Real.pi bounds up to 20 decimals (pi_gt_d20, pi_lt_d20), by the
  sqrtTwoAddSeries (Archimedes-type) tactics with rational witnesses from a Mathematica script
  [READ docs page]. No longer expansions in Mathlib.
- Lean, third party: metasecdev/math-proofs (GitHub, Apache-2.0, 50 commits, pushed
  2026-11-16): BBP identity against Real.pi; certificate [lo, hi] with tail guard; if lo = hi
  the hex digit is determined; theorem for all n with guard about 570n + 1795711; heavy
  certificates for n <= 10000 need more than 10 GB RAM and are not built in CI; README says no
  sorry, no native_decide, standard axioms only [READ README via fetch tool; self-reported,
  code not inspected]. It uses the plain tail bound with a guard linear in n, so it is not
  the modular-exponentiation algorithm of BBP. [INFERRED from the guard size]
- Chudnovsky/binary splitting: GitHub searches (chudnovsky coq / lean4 / formal) returned 0
  repositories; OpenAlex search returned nothing relevant. A "Lean Pool" archive paper
  (arXiv 2609.25199) was snippetted as listing a "Detailed Proof of the Chudnovsky Formula"
  project; I could not read an entry [SNIPPET]. So: identity possibly formalised (unconfirmed),
  verified computation by binary splitting: not found.

### 2.6 Other items

- Zudilin, "A BBP-style computation for pi in base 5" (arXiv 2409.10097, Sept 2024, 3 pp.)
  [READ PDF]: uses the Salikhov/Zeilberger-Zudilin identity pi/16 = sum over n of (b_n/(2n+1))
  5^(-2n) (b_n integer sequence, b_n = -6 b_(n-1) - 25 b_(n-2)), equivalently pi as imaginary
  part of 8 sum (1/(2n+1)) (1/(1-2i))^(2n+1). BBP strategy over Z[i] in base 5. Section "An
  obvious flaw": the modular reduction fails once 2n+1 > d - k (a denominator 5^(2n+1-d+k) m is
  not cancelled) and the tail has no bound, so the method does not work. He asks whether
  other formulas over quadratic or larger extensions could serve. He also states: BBP-type for
  pi are known for bases that are powers of 2, and whether it is possible for other bases is an
  open question.
- Craig-Wood, "Euler found the first binary digit extraction formula for pi in 1779",
  Euleriana 3(1), 2023: two Euler formulas allow binary digit extraction, contradicting the
  belief that BBP 1997 were first [SNIPPET, abstract].

## 3. What is open

1. Gibbons's Conjecture 1 (strict alternation is safe for the Gosper-series spigot). Open as
   stated by the source (2006 paper; 2024 revision does not claim a proof). Verified by me to
   12000 terms.
2. Verified Chudnovsky with binary splitting at record-relevant size: not found; I searched
   Coq/Isabelle/Lean/GitHub. Not stated as open by any source. The Bertot paper states that
   formally verified computation beyond 1000 digits was essentially unexplored in 2017.
3. A verified standalone digit-extraction program (hex digit n for all n, with modular
   exponentiation, compiled/extracted and trusted): the Coq one needs the prover; extraction
   is 10 times slower [READ]; the Lean repo above is an interval/guard method. Open as a
   goal.
4. Verified base-conversion/printing of long digit strings (Bertot et al. say it would be a
   worthwhile project) [READ].
5. BBP-type digit extraction in a base that is not a power of 2 for pi (Zudilin: open
   question; the project claims no rational degree-1 formula exists, section 5).
6. Which BBP-type formula and which hex offsets y-cruncher uses for each record: not
   documented on pages I read. Not found; weak evidence.

## 4. Leads for this project (ranked)

A. Verified executable hex-digit extraction for pi.
   Statement: a Lean function bbpHex (n : Nat) : Nat (or Fin 16) using integer modular
   exponentiation 16^(n-k) mod (8k+1) etc. and a finite tail, with a theorem that it equals
   floor(16 * frac(16^n pi)) for all n >= 0, with an explicit (small) guard so the answer is
   exact when no long carry run occurs, plus a decision for the ambiguous case. Then
   `decide`/`native_decide`-free kernel evaluation for modest n, and an extracted program for
   large n. Same for Huvent's formula (fewest terms) and Bellard/Takahashi's formulas.
   Fit: the project already machine-checks BBP-type identities and the term-count minimum
   (2/3 non-zero terms per bit); the verification step is exactly "which formula is
   cheapest as a checker". Missing: modular-exponentiation lemma and the carry/guard
   argument; Bertot et al. give the blueprint (Coq). Size: 1-3 weeks. Notice: the
   third-party Lean repo claims a guard method; a proof with the true O(n log n) algorithm and
   a verified Montgomery or plain mod-pow would be new and checkable.

B. Prove Gibbons's Conjecture 1.
   Statement: for all i >= 1, with z_i the product of the first i terms interleaved with
   production steps, floor(z_i((27i-12)/5)) = floor(z_i((675i-216)/125)). Equivalent to
   keeping a certain linear-fractional image of the tail interval inside one unit
   interval of digit values. Fit: exact integer/rational arithmetic, induction with an
   invariant on the matrix entries (q, r, s, t), polynomial inequalities in i (nlinarith/
   polyrith, or positivity); the project has done similar closed-form induction. A
   possible proof route: find invariants of the form a_i < r/t - y < b_i by computing
   the sequence and fitting rational functions of i; verify numerically to 12000 first
   (done). [INFERRED]. Size: days to weeks if an invariant exists; unknown if the digit
   sequence's irrationality-type behaviour is needed (then out of reach). Notice: a named
   open conjecture from a Monthly paper, verifiable in Lean; also yields the first formally
   verified unbounded spigot for pi.

C. A formal cost model for "computation plus independent check".
   Statement: the minimum number of non-zero terms (per bit) for a degree-1 binary formula
   used as a checker, and the cost of the pair (main computation, check) given independence
   rules; the project's Theorem J (a checked pair costs at least 60, Takahashi's attains it)
   appears to be this already. New data to add: Takahashi 2020's two formulas save about 20%
   over Huvent for checking [SNIPPET]; real verification time ratios of 1/600 (314T) to
   1/880 (300T) [INFERRED]. A short note "what record computations actually check", with the
   y-cruncher rules quoted (one run + BBP at matching offset), would be of interest to
   y-cruncher users. Size: days. Notice: low mathematically, useful for practice.

D. Verified check of the last hex digits of a published record. Statement: given the published
   digits file hash and offset, a verified program computes the BBP hex digits at that offset
   and compares. Fit: depends on A. The records' offsets are not in the pages read, so first ask
   the y-cruncher authors / read the validation files (Not found by me). Size: weeks, mostly
   engineering and a 3-4 hour compute for 314T (4.37 h on their machine); out of reach on
   the 24-core machine with a verified program at that size [INFERRED].

E. Verified Chudnovsky with binary splitting in Lean. Statement: the integer computed by a
   binary-splitting program on N terms satisfies |pi - approximation| < 10^(-k). Needs the
   Chudnovsky identity (formalisation status unknown, maybe in Lean Pool) which is a major
   modular-forms result; out of reach unless the identity exists formally.

F. Base-5 route (Zudilin): decide whether any formula over Z[i] or a bigger ring makes digit
   extraction in base 5 work, i.e. whether the flaw can be repaired. Fit: project's base-5
   results (no rational formula). Size: weeks; unknown. See section 5.

## 5. Overlap or conflict with section 1 of the rules file

- Zudilin 2024 says: "It is an open question whether this type of computation is possible for
  pi related to other bases" (paraphrase; he is speaking of BBP-type digit extraction for
  bases not powers of 2). The project's result "a degree-1 BBP-type formula for a non-zero
  rational multiple of pi exists in base b iff |b| is a power of 2" answers the rational
  degree-1 case; Zudilin's formula has Gaussian-integer coefficients (base 1-2i, norm 5) and
  is not of the form sum b^(-Bj) sum a_i/(Nj+i) with rational a_i, so there is no
  contradiction. His "obvious flaw" is consistent with the project's base-5 nonexistence, but
  not a proof for his class. [INFERRED]. Worth citing as context and as proof that the
  question is perceived as open in 2024.
- Craig-Wood 2023 (Euler 1779 binary digit extraction): if the formulas are of the form
  arctan-type series with powers of 2 in the denominators, they may be members of the base-2
  class the project classifies; check whether they are among the 13-dimensional space.
  [SNIPPET; not read; INFERRED].
- No conflict found with Theorem E (2/3 terms per bit) in any source on computation; the
  y-cruncher rules mention only "BBP formula", not counts.

## 6. Sources

- https://en.wikipedia.org/wiki/Chronology_of_computation_of_%CF%80
- https://numberworld.org/y-cruncher/records.html
- https://numberworld.org/y-cruncher/news/2025.html
- https://www.storagereview.com/review/storagereview-sets-new-pi-record-314-trillion-digits-on-a-dell-poweredge-r7725
- https://www.guinnessworldrecords.com/news/commercial/2026/6/pi-high-computing-achievement-technology-companies-calculate-pi-to-340-trillionth-digit
- https://en.wikipedia.org/wiki/Bellard%27s_formula, .../Bailey%E2%80%93Borwein%E2%80%93Plouffe_formula, .../Chudnovsky_algorithm, .../Spigot_algorithm
- https://www.cs.ox.ac.uk/jeremy.gibbons/publications/spigot.pdf and https://www.cs.ox.ac.uk/publications/publication1674-abstract.html
- https://arxiv.org/abs/1709.01743 (Bertot, Rideau, Thery)
- https://doi.org/10.1007/s11139-018-0104-x (Takahashi; Crossref record, catalog abstract)
- https://arxiv.org/abs/2409.10097 (Zudilin)
- https://doi.org/10.56031/2693-9908.1049 (Craig-Wood)
- https://github.com/metasecdev/math-proofs
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Real/Pi/Bounds.html
- https://arxiv.org/pdf/2412.19929 (Collins), https://arxiv.org/pdf/1809.00533 (Chudnovsky proof), https://arxiv.org/pdf/2609.25199 (Lean Pool)

## 7. Search log

WebSearch (5):
W1 "pi world record digits 2025 2026 Chudnovsky y-cruncher verification"
W2 "Bertot Rideau Thery Distant decimals of pi formal proofs Coq Borwein BBP abstract"
W3 "Takahashi On the computation and verification of pi using BBP-type formulas abstract"
W4 "Gibbons spigot pi Conjecture 1 Gosper series proved ... proof"
W5 "Archive of Formal Proofs pi digits computation Chudnovsky OR Machin Isabelle verified"

Endpoint / page fetches (those marked x failed or returned nothing useful):
1 Wikipedia chronology of pi computation
2 arXiv API "unbounded spigot" (x, 429)
3 OpenAlex "formally verified computation of pi digits"
4 Crossref Takahashi BBP-type (x, 429)
5 Semantic Scholar verified computation pi Coq (x, 429)
6 numberworld records page
7 StorageReview 314T review
8 Gibbons spigot.pdf (read via pdftotext)
9 HAL hal-01592286 (x, access denied)
10 OpenAlex "spigot algorithm digits of pi"
11 Crossref Takahashi with select (x, 429)
12 OEIS "Gibbons spigot pi" (A000796 only)
13 OpenAlex cites Gibbons (7 works)
14 OpenAlex Takahashi BBP computation
15 OpenAlex cites Bertot et al. (3 works)
16 Crossref author Takahashi (found the 2020 paper)
17 OpenAlex Gibbons conjecture spigot (1)
18 OpenAlex "Transcendental functions on continued fractions" abstract
19 OpenAlex formal verification Chudnovsky binary splitting (none relevant)
20 Springer Takahashi (x, redirect)
21 Semantic Scholar by DOI (x, 404)
22 Crossref DOI record (dates, references)
23 GitHub repos "verified pi digits coq lean isabelle"
24 GitHub repo search math-proofs BBP lean
25 OpenAlex DOI record for Takahashi (no abstract)
26 GitHub code search BBP lean (x, 401)
27 GitHub issues in mathlib4 "BBP pi hexadecimal" (0)
28 GitHub page metasecdev/math-proofs (README)
29 HAL document (x, denied)
30 arXiv abs 2409.10097
31 arXiv PDF 1709.01743 (read via pdftotext)
32 bib-bvb catalog (x, DNS)
33 arXiv PDF 2409.10097 (read via pdftotext)
34 OpenAlex Chudnovsky formalization (x, 429)
35 OpenAlex Isabelle pi (x, 429)
36 GitHub chudnovsky verified coq (0)
37 GitHub chudnovsky lean4 (0)
38 GitHub spigot pi proof (0)
39 Semantic Scholar Gibbons conjecture (x, 429)
40 Crossref spigot Gibbons conjecture proof
41 zbMATH spigot algorithm pi
42 GitHub bbp coq/isabelle/hol (x, 403)
43 GitHub bbp pi digit extraction formal verification (0)
44 GitHub Gibbons spigot haskell (0)
45 Crossref formal verification digits of pi
46 Mathlib docs Data/Real/Pi/Bounds (x, 404)
47 Wikipedia BBP formula
48 Oxford publication1674 abstract (errata)
49 arXiv PDF 2609.25199 (Lean Pool; binary only, not read)
50 y-cruncher news 2025
51 Guinness 2026 news
52 y-cruncher news 2026 (x, 404)
53 y-cruncher algorithms/pi (x, 404)
54 Oxford Gibbons publications (x, 403)
55 arXiv PDF 2412.19929 (references read via pdftotext)
56 Crossref Xeon Phi 100 quadrillionth (x, 429)
57 y-cruncher algorithms/pi retry (x, 404)
58 y-cruncher features (x, 404)
59 Wikipedia spigot algorithm
60 Crossref Bellard binary digit
61 Wikipedia Bellard's formula
62 Wikipedia Chudnovsky algorithm
63 Crossref Euler 1779 DOI
64 Mathlib docs Analysis/Real/Pi/Bounds
65 GitHub code search mathlib pi_gt_3141592 (x, 401)
66 Crossref Takahashi Montgomery
67 Crossref Chudnovsky detailed proof (nothing relevant)
68 arXiv API abs:spigot (x, 429)
69 Semantic Scholar DOI abstract (x, 404)
70 MaRDI portal Takahashi (x, 500)

Totals: WebSearch calls = 5. Endpoint/page fetches = 70 (about 42 returned usable content).
Local computation (not web): Python test of Gibbons's Conjecture 1 (12000 terms), pdftotext
on three downloaded PDFs, in the scratchpad.
