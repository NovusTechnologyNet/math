# W2-R09: recent (2023-2026) papers that overlap the project, and the Kulik preprints

Date of pass: 2026-11-22. Marks: [READ] = read on the source's own page/PDF (or its full text as served by
the DataCite or Wayback copy); [SNIPPET] = seen only in a search result, abstract or API record;
[INFERRED] = my own conclusion. BBG = Borwein-Borwein-Galway, Canad. J. Math. 56 (2004) 897-925.

## 1. Summary

1. [READ] The Kulik material is a self-published Zenodo "programme" by Dean A. Kulik (about 20+ records, Jan-Oct
   2026). The record the previous pass meant is "The Reader and the Frame" (DOI 10.5281/zenodo.22007471, concept;
   version DOI 10.5281/zenodo.22007472), dated 19 Aug 2026. It is now a tombstone: Zenodo removed it on 30 Oct 2026,
   reason "out of scope", note "User was blocked". The whole account (every record I tested, 8 of 8) was removed
   the same day.
2. [READ] The full text survives in three places: the DataCite API record (the Zenodo description field holds the
   entire paper, 53,700 characters), and a Wayback Machine copy of the 24-page PDF and of the record page
   (both captured 8 Sep 2026). Zenodo itself serves only the tombstone.
3. [READ] What it claims: NOT a classification. It studies, frame by frame, the lattice K of integer relations among
   the "shell sums" S_r(b,N) of a frame (b,N) (period N, base b, roots of x^N - b). It reduces K to a multiplicative
   (S-unit) relation lattice R among the numbers 1 - 1/alpha (Baker used to show dim K over the algebraic closure
   equals dim R), derives the two classical kernels (16,8) and (64,6), gives a factorisation sieve that excludes
   1952 of 2233 frames (b in [2,320], N in [3,9]) as having no relation over Q, and finds a few non-trivial
   frames by lattice reduction ((16,12) relation over Q(2^(1/3)), (4096,24), (16,24)). It says in so many
   words that no global classification is claimed. Not a proof of any of the project's five targets.
4. [READ] A sister paper "Exactly Two Seeds" (21971618, 17 Aug 2026) proves that sec^m(2 pi/m) is an integer > 1
   only for m = 6 and 8 (giving base 16, period 8, for pi, and base 64, period 6, for pi/sqrt 3). This is a
   statement about one generator family, not "pi only in powers of 2" for all formulas. Also removed.
5. [READ] The decisive public record on "pi in bases that are not powers of 2" is unchanged by 2023-2026 work:
   Zudilin (arXiv 2409.10097) v1 and v2 both call it an open question; no paper since 2023 on arXiv (DataCite
   index of all arXiv titles containing BBP, 2023-2026, 18 records), Zenodo, zbMATH (12 records for
   "Bailey-Borwein-Plouffe") or Crossref proves nonexistence for the full class, classifies zero relations,
   or proves anything about logarithms in the sense of Theorem K.
6. [READ] Barsky-Munoz-Perez-Marco (1906.09629v4) say only "no base 3 formula for pi is known" and ask only whether all
   degree-1 null formulas come from combining their formulas for different s. They also define the efficiency
   m'/log b (non-zero coefficients per bit) and compare 1 (BBP) with 7/10 (Bellard); they do not discuss a lower
   bound. So the "2/3 per bit is optimal" result is not anticipated there.
7. [READ] Formal verification: the only Lean/Mathlib BBP item found is Taylor (Zenodo, 1 Nov 2026): pi = the BBP
   series in Lean 4/Mathlib, plus certified hexadecimal digit extraction with an explicit guard depth. Nothing on
   classification or nonexistence. Older: Bertot-Rideau-Thery, Coq/HOL Light, 2017.
8. [READ] New items a referee may raise: Craig-Wood (Euleriana, 2023; Euler's 1779 formulas are binary BBP-type:
   base 4 and base 2^30, so inside "powers of 2"), Cloitre (2025), Adegoke-Lafont (2023), Takahashi (2022, 2025),
   Pain (2022), Batir (2023, 2024), Kristensen-Mathiasen (2023). None conflicts with the five results.
9. [INFERRED] No priority conflict found. The only text that mentions Baker and S-units next to BBP is Kulik's,
   which is unrefereed, removed, and weaker in scope. Cite it, if at all, as a removed self-published preprint
   with the Wayback URL; do not rely on it.
10. [INFERRED] Kulik's frames are a possible cross-check: the project could state which of his 2233 sweep frames
   (and his "third seed") fall inside the base-2 / base-3 / b >= 5 classes and confirm/refute his computed kernel
   dimensions with exact methods.

## 2. What is known

### 2.1 The Kulik preprints (question 1)

Identification. [READ] Zenodo concept DOI 10.5281/zenodo.22007471, version DOI ...22007472, title "The Reader
and the Frame: The Annihilator Lattice of the Digit-Extraction Towers, its Instrument-Dependence, and the
Condition that Makes the Classical Formula Unique". Author "kulik, dean" (Dean A. Kulik), registered 19 Aug 2026
(DataCite), licence CC BY-NC 4.0. DataCite shows 0 citations, 0 views, 0 downloads. No OpenAlex record could be
retrieved (OpenAlex returned an API-budget error, so my earlier mention of an OpenAlex record in P01 is
not re-verified by me).

Status. [READ] zenodo.org/api/records/22007471 and /22007472 return HTTP 410 "Record deleted", tombstone:
removed by Zenodo user 1060945, removal date 2026-10-30 12:45 UTC, reason "out-of-scope", note "User was
blocked". Records 21971618/9 (Exactly Two Seeds), 22093512 (The Probe and the Kernel), 20789774 (Seam
Compiler), 21468248, 23361047, 18607797, 15471626 carry the same tombstone with removal times between 12:44 and 12:53
that day. So the account was blocked and everything removed. DataCite still lists the DOIs as "findable".

Surviving copies. [READ] (a) DataCite API: https://api.datacite.org/dois/10.5281/zenodo.22007471 (description
field = whole paper). (b) Wayback: http://web.archive.org/web/20260908104604id_/https://zenodo.org/records/22007472/files/The%20Reader%20and%20the%20Frame.pdf?preview=0
(24 pages, about 9,700 words, which I fetched and converted with pdftotext) and
http://web.archive.org/web/20260908104629id_/https://zenodo.org/records/22007472 (record page, 232 KB).
The Wayback availability API reported no snapshot for the concept DOI URL 22007471, for 21971618, or for 21971619.
A ResearchGate item by the same author, "The Diagonal of the Square: The BBP Formula and Spectral Sums of Every
Order on Native Binary Rings" (DOI 10.13140/RG.2.2.32770.44487, 12 Nov 2026, "Unpublished"), exists as a record;
ResearchGate returned HTTP 403 and DataCite has no abstract, so it is unread.
No mirror, discussion thread or citation of any Kulik BBP preprint was found (DataCite citations 0).

Abstract and claims of "The Reader and the Frame" (paraphrase) [READ]:
- Objects: a "frame" (b,N); shell sums S_r = sum_k b^-k/(Nk + r); K = integer vectors annihilating them
  ("zero relations", the same objects as Bailey's null formulas, in frame language); the "producer" is the
  coefficient vector giving pi or pi/sqrt 3.
- Claims as new (its own list): (1) K reduces to an S-unit relation lattice, and both classical kernels, (16,8) for
  pi and (64,6) for pi/sqrt 3, are derived with no integer-relation search; (2) odd-prime content of the frame is the
  factorisation of b-1, with a "rigorous exclusion sieve" (1952 of 2233 frames, b in [2,320], N in [3,9],
  zero false exclusions against 16 known-nonzero frames, 281 survivors); (3) a theta-grading theorem; (4)
  corrections to earlier claims ("winding", ancestry) and a third annihilator seed; (5) the "reader ladder":
  dim K over Q is a lower rung, the frame-intrinsic invariant is dim R, which by Baker is unchanged by widening the
  field; a frame the author earlier called empty, (16,12), has a relation over Q(2^(1/3)) (residual 5e-260);
  (6) uniqueness bridge: the "producer" is unique modulo K, and the DC-blocking linear functional Sigma
  is injective on K iff dim K = 1; uniqueness holds at 7 of 8 known towers and fails at (4096,24).
- Proofs vs computations: Theorem 4.2 (dim K over closure = dim R, Baker) and Proposition 6.1 (shared/unshared
  primes via valuations) are argued in the text; most dimension counts, the kernel dimensions at (16,24),
  (4096,24), (64,30) etc. are computed with PSLQ-type/LLL searches at 300 digits. The paper lists "unproven"
  items itself (Sigma generator, carrier iff d | C, etc.) and says plainly "no global classification is claimed".
- Bases: frames with b up to 320 and N up to 9; deep dives only for b = 16, 64, 256, 4096 with N = 6, 8, 12, 16, 18,
  24, 30, 72; negative b = -8, -27, -64 appear. Not stated for base 2 or 3 as such, not for "pi for all integer bases".
- Citations in the paper: BBG 2004 (explicitly credited with the closed form for L(1,b,n,j) and the valuation-vector
  method), BBP 1997, Baker, Capelli, Zsigmondy/Bang, "S-unit machinery as classical". It quotes BBG Research
  Problems 2 and 10 as the problem it addresses, and does not claim to answer them. It does not cite
  Kristensen-Mathiasen, Barsky et al., Lagarias or Bailey's Compendium (searched the text for them).
- Not claimed: optimality (no mention of terms-per-bit bounds), logarithms criterion, "pi only in powers of 2", any
  formal proof. The text says the author works with AI help ("Driven by"; a section on "AI-mediated scientific
  writing" appears in a sister record title, "A Compiler, not a Verdict", 25 Oct 2026) [SNIPPET].

Sister records [SNIPPET/READ from the descriptions]:
- "Exactly Two Seeds" (17 Aug 2026): imposes pole annihilation and a zero-sum condition on a coefficient space;
  the unique line is [4,-2,-1,-1] and everything follows from Re(z_char) = 1, forcing radix b = sec^m(2pi/m),
  an integer > 1 exactly for m = 6, 8 (proof via Q(2cos(2pi/m)) abelian, Q(2^(1/e)) not for e >= 3). "Towers"
  (b,n) = (b_seed^k, km). Predicts and verifies four new towers numerically.
- "Objects as Closures" (16 Aug 2026): same method, philosophical framing.
- "The Partner Predicate: Incidence, Forcing, and the Inverse Problem for BBP Relation Spaces" (21 Aug 2026,
  DOI 10.5281/zenodo.22036644): excludes 1893 of 2233 frames by factorisation alone; prime ideals in the orbit
  decomposition of x^N - b; kernel dimension counts. Same frames.
- "The Transform Layer" (21 Aug 2026, ...22041017): kernel structure under "winding"; new measurement (64,30),
  dim R = 1.
- Other Kulik titles (Nexus/SHA-256/"harmonic" framing, about 109 DataCite hits for the author name): not mathematics of
  this kind; a web search result describes them as self-published and framed outside standard mathematics.

Relation to the project [INFERRED]: his K is the same object as the zero relations of the project's base-2^k
classification, and his R is the S-unit lattice that the project's Baker step uses. His results are sweeps and
partial theorems for small N, b <= 320, while the project has complete classifications. Nothing in his text
mentions the denominators-in-a-fixed-power-of-b classification, bases >= 5 in general, or logarithms.

### 2.2 Barsky-Munoz-Perez-Marco, "On the genesis of BBP formulas" (arXiv 1906.09629v4, 13 Feb 2023; Acta Arith. 198 (2021)) [READ]

- Abstract: a general procedure (Laplace-Hadamard regularisation of polar parts of iterated primitives) that generates
  infinitely many BBP and BBP-like formulas for log 2, pi and similar numbers; explains why many formulas are
  rearrangements of each other and "where some null BBP formulas ... come from"; relation between log 2 and pi
  formulas by real/imaginary parts of a complex formula.
- Base 3: the introduction says there are both base-2 and base-3 formulas for some constants (cited from Bailey), but
  "no base 3 formula for pi is known". This is a statement of absence, not impossibility.
- Null formulas: they obtain some null formulas by comparing the formulas at different complex s (example with
  s = 1/2 and (1+i)/2); one stated question: is every degree-1 null BBP formula obtainable by combining formulas of
  their Theorem 1.1 for different s? This is the open question the project's dimension counts answer for
  the classes it covers [INFERRED].
- Efficiency: Remark 1.2 defines efficiency m'/log b (m' = number of non-zero coefficients per block) and compares (1) = 1
  with Bellard's formula 7/10. No lower bound is stated. They hope computer algebra will find more efficient ones.
- No Baker, no nonexistence claim, no list of open problems beyond the above.
- Cited by (Semantic Scholar, 5 records): Kristensen-Mathiasen 2022, Batir 2023, Munoz-Perez-Marco 2024 (Stirling-Ramanujan
  constants are exponential periods, 2402.02660), Raz-Shalyt-Leibtag 2025 (2502.17533, LLM formula unification, not BBP),
  Olaikhan 2026.

### 2.3 Zudilin, arXiv 2409.10097, both versions [READ]

- v1 (16 Sep 2024), title "A BBP-style computation for pi in base 10", abstract: "We articulate about how to compute
  (promptly) the digits of pi, in bases 5 and 10, from a given place without computing preceding ones".
- v2 (17 Sep 2024), title "... in base 5", abstract: "We joke about how to compute ... in base 5". Section 3 is
  "An obvious flaw": the equality used fails when 2n+1 > d-k. So the digit claim is withdrawn.
- Both versions state: several BBP-type formulae for pi are known for bases that are powers of 2, and it is an open
  question whether this type of computation is possible for pi related to other bases.
- Method: the imaginary part of sum (1-2i)^-(2n+1)/(2n+1) over Z[i], with norm 5. Coefficients are Gaussian (complex),
  outside P(1,b^B,N,a) [INFERRED]. For the project: Zudilin's "open" is exactly the full-class question that the
  integer-base theorem settles for rational a_i, so v1/v2 is a citable statement that the question was open in 2024.
- Cited by: no citing records found (Semantic Scholar returned an empty list).

### 2.4 Cloitre, arXiv 2508.03743 (Aug 2025, math.GM) [READ abstract]

Self-contained proof of a BBP-type formula for pi^2 in the golden-ratio base phi (discovered empirically by the author in
2004), via an identity linking phi to fifth roots of unity; extension to a "Machin-like" formula for zeta(3). The
formula is in a non-integer (Pisot) base; Cloitre notes that such expansions do not really give digit extraction
(web-search snippet). No overlap with integer bases. Relevant only as the non-integer boundary (with
Kristensen-Mathiasen). Cloitre 2507.20428 (Aug 2025): BBP-type formula for the remainder of the
Madhava-Gregory-Leibniz series, base 16, Pochhammer denominators; also a log 2 analogue. [READ abstract]

### 2.5 Kristensen-Mathiasen, J. Number Theory 244 (2023) 251-263 (arXiv 2208.07696) and follow-ups

- [READ] (from P01) LLL on roots of unity plus geometry of triangles; counts of null formulas only for bases 2^k and 3^k;
  open problems: why the golden ratio has many null formulas, digit extraction in irrational bases, higher degree.
- [SNIPPET] Citers (Semantic Scholar): Cloitre 2025 (2507.20428), Batir 2024 "A note on some classes of series for the
  logarithmic function", Adegoke-Lafont 2023 (2303.13374). A web search found no 2024-2025 follow-up by the authors
  themselves, and none on null formulas or Pisot bases.
- Adegoke-Lafont, 2303.13374 (24 Mar 2023) [READ abstract]: base-alpha (golden ratio) expansions of log F_n, log L_n,
  arctan(1/F_n), arctan(1/L_n) for all n. Formula-finding in a Pisot base; no classification.

### 2.6 Other 2022-2026 items found

- [SNIPPET] Takahashi, "On the use of Montgomery multiplication in the computation of binary BBP-type formulas" (2022,
  zbMATH 7576461) and "On the Division in the Computation of Binary BBP-Type Formulas for Mathematical Constants"
  (LNCS, 2025, DOI 10.1007/978-3-031-81244-6_32; Crossref has no abstract). Computational; binary only; no overlap with
  classification (not read in full).
- [READ abstract] Craig-Wood, "Euler found the first binary digit extraction formula for pi in 1779", Euleriana 3(1) (29 Mar 2023):
  Euler's two formulas for pi (base 4, with coefficients over 4k+1..4k+3, and a base 2^30 one with period 60) are
  BBP-type; Bailey's Compendium (8 Apr 2023 version) now cites it. Both are binary, so consistent with
  "pi only in powers of 2" and with the 2/3-per-bit bound (Euler (2): 4 terms per 2 bits [INFERRED from the
  Compendium text]). Craig-Wood also has arXiv 2508.08307 (Machin-like Lehmer measures), not BBP.
- [SNIPPET] Pain, "Relations between pi and the golden ratio phi in the form of BBP-type formulas" (2022, zbMATH 900534564)
  and Batir (Bull. Malays. Math. Sci. Soc. 2023, 2302.06640; 2024 note on log series): formula-finding.
- [SNIPPET] Olaikhan, arXiv 2507.04205 (Jul 2025): polylogarithmic integrals, Euler sums, BBP-type series.
- [SNIPPET] Wu-Chen-Zhu, Mathematics 10(3):290 (2022): new BBP-type formulae for pi from Taylor expansions of arctan.
- [READ] Taylor, Zenodo 10.5281/zenodo.23867087 (1 Nov 2026): Lean 4/Mathlib development, only standard axioms, no sorry:
  pi = the BBP series (bbpSeries_eq_pi); soundness of a guarded certificate for the n-th hex digit; explicit
  irrationality-measure bound at denominators 16^k; guard depth g >= 570n + 1795711. Not classification, only the base-16
  formula. This is the main "Lean BBP" item to cite when claiming a formal first.
- [SNIPPET] Zenodo/viXra noise from 2026: Caldin (golden-ratio BBP/arctangent identities, about 14 records, Oct 2026), Kim (Plouffe-Bellard
  digit-extraction folding, Oct-Nov 2026), "Quantum Pi Benchmark" (Aug 2026), a "Structural Classification of pi Formulas:
  Six Families" (10 Jul 2026, expository, BBP is one family; no BBP classification theorem).
- [READ] Searches that returned nothing relevant for 2023-2026: arXiv (DataCite index) for BBP + Baker/linear forms in logarithms,
  BBP + S-unit, "zero relations"/"null formulas" with BBP, Lean/Mathlib with BBP/Machin, Machin-type with BBP
  exclusion; zbMATH for "digit extraction pi" (4 hits) and "Machin-type" (1 hit); Crossref for BBP zero relations.
  Hence no author named Wei, Zhang, Lafont (beyond the 2023 golden-ratio paper), Takahashi, or Adegoke has a
  2023-2026 classification or nonexistence paper that I could find. Adegoke's 2023 outputs found: 2303.13374 (with Lafont).

### 2.7 Overlap with the five project claims (question 2)

| Project claim | Closest item | Overlap |
|---|---|---|
| Complete classification in bases 2 and 3 | Kulik "Reader and the Frame" (frame-wise kernel dimensions, b <= 320, N <= 9; "no global classification claimed") | Partial for zero relations only; computational; per-frame; removed. BMP open question (all null formulas from combinations?) is not answered by anyone in print. K-M Table 1 gives counts only. |
| No relations in bases >= 5 | Kulik's sieve: excludes 1952 of 2233 frames (factorisation) and says the surviving 281 are undecided; (16,12) and (4096,24) have relations | None proved for all b >= 5; his frames use roots of x^N - b with b arbitrary and are a different class from weights b^(-floor(k/2)) [INFERRED]. Check that the project's statement does not contradict his computed relations (they are in bases 16, 64, 256, 4096 = powers of 2). |
| pi only in powers of 2 | BBG 2004 (Machin-type), Bailey Compendium 2011-2023 (stated), Zudilin 2024 (open) | None proves the full class. Kulik's "exactly two seeds" is a different statement (admissible radices of one generator family). |
| 2/3 non-zero terms per bit optimal | BMP Remark 1.2 (efficiency defined, 7/10 for Bellard) | None states or proves a lower bound. |
| log b only for powers of 2 and 3 | BBG Example 4 ("failed to prove", Machin-type only) | None. |

## 3. What is open (question 2 and 3)

- (a) The full-class statement: Zudilin writes it as open (2024) [READ]; BBG says the non-Machin case is not covered [READ]; Bailey writes it as
  known [READ]. Not found proved by anyone else; weak evidence of absence (searches listed below).
- (b) BBG Research Problems [READ, full PDF]: (2) how many Q-linearly independent binary Machin-type zero relations
  exist, with upper bounds; (3) is the original BBP formula a Machin-type combination; (7) a Zsigmondy theorem over Q[i] for
  exclusion; (9) generalise to Gaussian-integer bases b and p,q in Z[i,k], to avoid treating arctan and log separately;
  (10) can their techniques decide when pi is a combination of L(1,b^m,n,j) with b and perhaps n fixed (needs
  Q[zeta_n, b^(1/n)]); (11) why do Machin-type generators give "all interesting" arctangents and logarithms.
  Problems 2, 7, 9, 10 are close to the project's toolkit [INFERRED].
- (c) BMP: do all degree-1 null formulas come from Theorem 1.1 at different s? [READ]
- (d) K-M: golden-ratio null formulas, irrational-base digit extraction, higher degree [READ].
- (e) Cloitre 2025: formulas of higher weight remain rare; a pure BBP-type zeta(3) formula in the golden base not found [SNIPPET].
- (f) Kulik's open problems (unreviewed; removed): the 3-versus-5 asymmetry, the remaining dimension at (4096,24)
  [READ]. Any such question should be treated as the author's own, not as literature.

## 4. Leads for this project, ranked

1. Cite and neutralise the Kulik overlap in the introduction. Statement: for the frames (b,N) with b in {16,64,256,4096},
   decide which of his sweep results are consequences of the project's classification, and state the project's result as
   a theorem rather than a sweep. Exact computation: for all b <= 320, N <= 9 list dim K over Q (from the project
   machinery) and compare with his 281 survivors and his 16 known frames. Size: days. Why it fits: the project has
   exact lattices; he used PSLQ. Worth noticing because: a referee who finds the DataCite text will ask. [INFERRED]
2. State BBG Research Problems 2 and 10 answers in the paper's introduction: Problem 2 (number of independent zero relations) is answered for
   the project's classes by the dimension counts. Size: days. Worth noticing because the problems are stated
   by the original authors in the journal. [INFERRED]
3. Answer the BMP question: show that all degree-1 null formulas in the project's classes arise by combining formulas of
   Barsky et al. Theorem 1.1 at different s, or that they do not. Size: weeks (needs their Theorem 1.1 explicitly). [INFERRED]
4. Lean positioning: the "Lean BBP" literature to date is Taylor's Nov 2026 development (base 16 identity and digit
   extraction). The project's formal classification and nonexistence theorems are a different and larger body. Cite Taylor as
   the only prior Lean BBP work found. Size: hours. [INFERRED]
5. Non-integer bases (K-M, Adegoke-Lafont, Cloitre): extend the integer-base iff-theorem to algebraic integer bases;
   see P01 lead 2. Size: weeks.

## 5. Overlap or conflict

- No conflict. The nearest text is Kulik: "No global classification is claimed anywhere in this paper." (the closing
  scope note [READ]). His claim "(1) the reduction of K to an S-unit relation lattice" overlaps the project's use of
  Baker plus primitive divisors, but only as a frame-wise reduction; his dimension counts are computed and several of
  his own earlier claims "died" (his section 13). If both are cited, say that the S-unit reduction of BBP relations
  is also in a removed 2026 Zenodo preprint, and that the classification here is complete and formal.
- Bailey 2011-2023 still states the full-class sentence without proof (P01). Zudilin 2024 states it open.
- BMP Remark 1.2 defines the efficiency measure used in the 2/3 theorem; cite it as the source of the measure.
- Euler's formulas (Craig-Wood 2023) are in the class "base a power of 2" and must be included in the examples list.

## 6. List for a referee: "did you know about this?" (question 3), dated

- 2001 Lagarias, Experiment. Math. 10 (arXiv math/0101055): BBP-numbers and a Baker-based dichotomy.
- 2001 Adhikari-Saradha-Shorey-Tijdeman, Indag. Math. 12: transcendental infinite sums.
- 2004 Borwein-Borwein-Galway, CJM 56: https://doi.org/10.4153/CJM-2004-041-2 (Machin-type exclusion; research problems 1-11).
- 2011-2023 Bailey, Compendium: https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf (full-class sentence; Euler note, 2023).
- 2021 Barsky-Munoz-Perez-Marco, Acta Arith. 198: https://arxiv.org/abs/1906.09629 (efficiency; null formulas question).
- 2022 Takahashi, Ramanujan J. / zbMATH 7576461 (Montgomery multiplication in binary BBP computation).
- 2022 Wu-Chen-Zhu, Mathematics 10(3):290; Pain (relations of pi and phi), zbMATH 900534564.
- 2023 Kristensen-Mathiasen, J. Number Theory 244: https://arxiv.org/abs/2208.07696.
- 2023 Craig-Wood, Euleriana 3(1): https://scholarlycommons.pacific.edu/euleriana/vol3/iss1/3/ (Euler 1779).
- 2023 Adegoke-Lafont, https://arxiv.org/abs/2303.13374 (golden-ratio base expansions).
- 2023-2024 Batir, https://arxiv.org/abs/2302.06640 and a 2024 note on logarithmic series.
- 2024 Zudilin, https://arxiv.org/abs/2409.10097 (v1 base 5 and 10 claim; v2 "joke", base 5, open question).
- 2025 Cloitre, https://arxiv.org/abs/2508.03743 (pi^2, golden-ratio base) and https://arxiv.org/abs/2507.20428 (base 16 remainder).
- 2025 Takahashi, LNCS, DOI 10.1007/978-3-031-81244-6_32 (division in binary BBP computation).
- 2025 Olaikhan, https://arxiv.org/abs/2507.04205.
- 2025 Raz-Shalyt-Leibtag, https://arxiv.org/abs/2502.17533 (LLM unification of pi formulas, from 455,050 arXiv papers; not BBP classification).
- Aug 2026 Kulik (Zenodo, removed 30 Oct 2026): DOIs 10.5281/zenodo.21970408 (Objects as Closures), .21971618 (Exactly Two Seeds),
  .22007471/.22007472 (The Reader and the Frame), .22036644 (Partner Predicate), .22041017 (Transform Layer); DataCite API
  copy: https://api.datacite.org/dois/10.5281/zenodo.22007471; Wayback PDF as in 2.1.
- 12 Nov 2026 Kulik, ResearchGate "The Diagonal of the Square" (DOI 10.13140/RG.2.2.32770.44487), unread.
- 1 Nov 2026 Taylor, Lean 4 hexadecimal digit extraction for pi (Zenodo 10.5281/zenodo.23867087).
- 2026 Caldin (Zenodo, Oct 2026), Kim (Zenodo, Oct-Nov 2026): formula-finding noise; no classification.

## 7. Sources (URLs)

- https://zenodo.org/api/records/22007472 (tombstone, 410), https://api.datacite.org/dois/10.5281/zenodo.22007471,
  https://api.datacite.org/dois?query=%22Exactly+Two+Seeds%22+OR+%22Reader+and+the+Frame%22+OR+%22Objects+as+Closures%22
- http://web.archive.org/web/20260908104604id_/https://zenodo.org/records/22007472/files/The%20Reader%20and%20the%20Frame.pdf?preview=0
- https://arxiv.org/abs/1906.09629 , https://arxiv.org/abs/2409.10097 , https://arxiv.org/abs/2508.03743 , https://arxiv.org/abs/2208.07696
- https://www.cambridge.org/core/services/aop-cambridge-core/content/view/BB7919C8E1AE66878AE8D7BC7F0EBFA3/S0008414X0003385Xa.pdf/finding-and-excluding-b-ary-machin-type-individual-digit-formulae.pdf
- https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf , https://zenodo.org/doi/10.5281/zenodo.23867087 (Taylor)

## 8. Search log

WebSearch (6 calls): W1 Kulik "Reader and the Frame" annihilator lattice (no hit except other Kulik records); W2 BBP-type pi
"power of two" nonexistence 2025/2026; W3 BBP Lean/Coq verification; W4 Scientific American "A New Formula for Pi?" (unrelated,
string theory and Technion pieces); W5 K-M follow-up/null formulas/Pisot; W6 "no BBP-type formula" base 10 Galway generalization.

Endpoint queries (about 105, via curl on public APIs; WebFetch returned only binary or 429 for some):
Zenodo API (record 22007471, 22007472, 21971618/9, 22093512, 20789774, 21468248, 23361047, 18607797, 15471626; four keyword
searches (poor ranking)); Zenodo DOI page; DataCite API (about 30 queries: BBP/digit extraction, arXiv prefix 10.48550 with
BBP / digit extraction / Baker / S-unit / zero relations / Lean / golden ratio / Machin, author queries Kulik, Adegoke, Lafont,
Takahashi, Kristensen, Perez-Marco, title lookups, individual DOI records); Wayback availability API (6 URLs) and CDX; Wayback PDF
and page fetches (2); Crossref (10 queries and 2 DOI lookups); Semantic Scholar (3 citations queries answered, 4 search queries
429); arXiv API (2, both 429), arxiv.org abs pages (4), PDFs (Zudilin v1, v2; BMP); Bailey Compendium PDF; BBG PDF;
Euleriana page; zbMATH Open API (5); OpenAlex (1, budget error); OEIS (1, empty); GitHub (1, empty); ResearchGate (403).
Totals: WebSearch calls = 6. Endpoint queries = about 105.

Notes: web content contained no instruction directed at me except OpenAlex's request to use an API key (ignored, no contact
detail supplied). Kulik's texts address "readers" in a stylised way but contained nothing directed at me. Not done / weak: the
RG paper, Takahashi's papers, Batir 2024, and Pain 2022 were not read; OpenAlex and S2 searches were rate-limited, so
"not found" for 2023-2026 items rests on DataCite/arXiv titles, Crossref, zbMATH and 6 web searches.
