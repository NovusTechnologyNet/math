# Novelty check: classification of binary Machin-type (arctangent) formulas for pi

State of knowledge as of 21 November 2026. Thread: one of seven. Scope: Theorems A and B and the
speed corollary of `pi_formula_theorem.md` (Parts I and II); Part III is touched only where a source
bears on it directly.

How to read the evidence labels:
- "read in full text" = I extracted and read the PDF text myself in this session.
- "via page summary" = the page was fetched and summarized by the fetch tool; wording is paraphrase.
- "not verified" = bibliographic lead only; content not seen.

Direct quotation is deliberately limited to one sentence (BBG's Research Problem 2); everything else
is paraphrase.

---

## 1. Overall verdict: (a) results that contain ours, (b) results that are close, (c) nothing found

### Takeaway
No source found states or proves Theorem A, Theorem B, or the uniqueness corollary for
pi/4 = 2 arctan(1/3) + arctan(1/7). Theorem A answers a research problem that Borwein, Borwein and
Galway posed explicitly in 2004 and that none of the roughly 25 papers citing them takes up; but its
two ingredients (BBG's "private primitive prime" argument and the fact that both Aurifeuillian
factors of 4^n + 1 have primitive prime factors) are both already in print, so the result is new as
a statement and short as a proof.

### Cited Findings

**(a) Results that already contain ours (in whole or in a named part)**

- Whole of Theorem A, Theorem B, Corollary: nothing found.
- The two-term sub-case of Theorem A is classical. Every generator is arctan(1/N) with N an integer,
  and Stormer's theorem says the only two-term relations m arctan(1/x) + n arctan(1/y) = k pi/4 are
  Machin's formula and the three formulas with arguments (2,3), (2,7), (3,7) — exactly R2, R3 and
  the Hutton/Euler formula. BBG themselves present it this way (their equations (11)-(13), read in
  full text) — [BBG 2004](https://www.cambridge.org/core/journals/canadian-journal-of-mathematics/article/finding-and-excluding-bary-machintype-individual-digit-formulae/BB7919C8E1AE66878AE8D7BC7F0EBFA3);
  Stormer solved it over the integers in 1895-1899, with a gap filled by Ljunggren in 1942
  (read in full text) — [Calcut 2009](https://www2.oberlin.edu/faculty/jcalcut/gausspi.pdf).
- Lemma 2 of the note (both Aurifeuillian factors L_n, M_n have a primitive prime factor, with small
  exceptions) is, in substance, Schinzel 1962 at (a, b) = (2, 1): Schinzel showed a^n - b^n has at
  least two primitive divisors under a squarefree-kernel condition, and proved it through an
  Aurifeuillian factorization of the cyclotomic value (read in full text) —
  [Stewart, "On divisors of Lucas and Lehmer numbers", arXiv:1008.1274](https://arxiv.org/abs/1008.1274);
  [Stewart's commentary for Schinzel's Selecta](https://uwaterloo.ca/pure-mathematics/sites/default/files/uploads/documents/schinzel-report1_0.pdf).
- The factorization used in the proof of Lemma 2, Phi_4n(2x^2) = [Phi_n(x(1+i)) Phi_n(x(1-i))] *
  [Phi_n(x(-1+i)) Phi_n(x(-1-i))], is printed as Example 3.2 of Chamberland 2003, who traces the
  m = 4 case to Schinzel's formula (12) (read in full text) —
  [Chamberland, J. Integer Seq. 6 (2003) 03.3.7](https://cs.uwaterloo.ca/journals/JIS/VOL6/Chamberland/chamberland60.pdf).
- The base-not-2 case (no formula at all) is BBG's Theorem 7, proved by exactly the argument the
  note uses: take the largest exponent M, pick a primitive prime of b^(4M) - 1 by Bang, observe that
  it divides b^M - i and no smaller generator, conclude the coefficient is zero (read in full text)
  — [BBG 2004 PDF](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/BB7919C8E1AE66878AE8D7BC7F0EBFA3/S0008414X0003385Xa.pdf/finding-and-excluding-b-ary-machin-type-individual-digit-formulae.pdf).

**(b) Results that are close**

- BBG 2004: defines the generators, proves non-existence for b != 2, finds R1-R3 and two zero
  relations by hand for b = 2, and asks how many zero relations there are (Section 2 below).
- Gasull, Luca, Varona 2023: complete classification of *two-term* formulas with arguments 2^a/b or
  b/2^a (Section 3 below). Different family (general numerators, two terms only), different tools.
- Chamberland 2003: the cyclotomic construction Re log Phi_m((+-1 + i)/2^n) for *logarithms*; the
  real-part twin of the note's Theorem B family; no classification (Section 6).
- Bailey's Compendium (April 2023 version): arctangent section defines the binary arctangent set
  through products of (1 +- (1+i)^u / 2^v)^w, reports PSLQ experiments, gives a 15-element list that
  "appears" independent, and a table of empirical zero-relation counts; no proofs of completeness
  (Section 6).
- Barsky, Munoz, Perez-Marco 2021: explains some null BBP formulas and asks whether all degree-1
  null formulas arise from their construction (Section 6).
- Yamada (arXiv 2018, v6 2025): finiteness with explicit bounds for nondegenerate three-term
  Machin-type formulas (Section 4).

**(c) Nothing found**

- A statement of the form "the only Machin-type relations with arguments 1/2^m and 1/(2^m - 1)
  are ..." in any paper, the Wikipedia articles on Machin-like formulas and on the BBP formula,
  MathWorld, Arndt's arctan page, or Lafont's OEIS wiki page (Sections 6 and 7).
- Any classification of relations among the cyclotomic "orbit sums" Im Log(1 - r/(1+i)) (Theorem B).
- Any proof that 2 arctan(1/3) + arctan(1/7) is optimal or unique in a class of binary formulas.

### Inferences
- Positioning: Theorem A is best presented as the answer to BBG's Research Problem (2) ("exactly
  two zero relations in the minimal generator set, namely BBG's (35) and (36)") and as carrying out
  the programme sketched in BBG's Problem (7), with Schinzel 1962 doing the work BBG expected from
  a Zsigmondy theorem for Q(i).
- Risk: a referee may regard Theorem A as a corollary of BBG's method plus Schinzel 1962. The note
  should cite Schinzel 1962 for Lemma 2 rather than present Lemma 2 as its own, and should cite
  Stormer for the two-term case.
- The same private-prime argument appears to settle BBG's "orphans" arctan(2/7), arctan(4/9),
  arctan(5/9) inside the Machin-type class (BBG's Theorem 2(b) excludes only non-Aurifeuillian
  formulas for them; Bailey's 2023 Compendium still lists arctan(2/7) as undecided). My own sketch,
  not checked by computer: 2 has order 52 modulo 53 (53 = 2^2 + 7^2), so 53 divides only
  M_13 = 53 * 157 among the norms of
  top index 52, 157 is private to arctan(1/2^13), and every generator of larger index has a private
  primitive prime, so no combination can isolate 53. If this holds up it is a second concrete
  corollary tied to a stated open item.

### Gaps
- Citation coverage is Semantic Scholar plus OpenAlex only. Google Scholar and MathSciNet were not
  queried; zbMATH returned HTTP 403. A citing paper indexed only there would have been missed.
- The search budget for this session was capped after 20 searches (shared limit across all agents),
  so no further keyword searches of MathOverflow, Math StackExchange or OEIS were possible beyond
  queries 13 and 14 in the log. Those two returned nothing relevant. This is a weaker negative than
  a site-specific search would give.

---

## 2. What exactly do Borwein-Borwein-Galway 2004 prove and leave open for base 2? Who cites them?

### Takeaway
BBG prove non-existence for every base other than 2 and give exclusion criteria; for base 2 they
find the formulas and two zero relations by hand and explicitly leave the count of zero relations
open. No citing paper found addresses that question.

### Cited Findings

All items in this block were read in the full text of the published PDF —
[BBG 2004 PDF](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/BB7919C8E1AE66878AE8D7BC7F0EBFA3/S0008414X0003385Xa.pdf/finding-and-excluding-b-ary-machin-type-individual-digit-formulae.pdf)
(J. M. Borwein, D. Borwein, W. F. Galway, Canad. J. Math. 56 (5) (2004) 897-925,
DOI 10.4153/CJM-2004-041-2; received 8 Jan 2003, revised 30 Jan 2004).

- Definition 1 (Section 2.4): for b > 2 not a proper power the generators are arctan(-b^(-m)); for
  b = 2 there are additional "Aurifeuillian" generators arctan(1/(1 - 2^m)) = Im ln(1 - (1+i) 2^(-m)).
  This is the "minimal set". A "full set" also allows arctan(1/(1 + 2^m)); both span the same space
  because Im ln(1 + (1+i)2^(-m)) = Im ln(1 - i 2^(1-2m)) - Im ln(1 - (1+i)2^(-m)).
  So the note's generators b_m, a_m and its Corollary 1 identity match BBG's setting exactly.
- Section 2.5: three binary formulas for pi/4 from the Gaussian products (2-i)(3-i) = 5-5i,
  (2-i)^2 (7+i) = 25-25i, (3-i)^2 (7-i) = 50-50i, i.e. the formulas with arguments (2,3), (2,7),
  (3,7), plus arctan(1) itself (their (17), credited to Ferguson). They are described as found by a
  hand search.
- Section 2.5, equations (35)-(36): "two linearly independent zero relations" among
  alpha_1, beta_1, beta_2, beta_3 (the generators for 1/2, 1, 1/3, 1/7). No claim that there are no
  others.
- Theorems 1 and 2: exclusion criteria. Theorem 2(a): if a prime p = 1 mod 4 with 4 not dividing
  ord_p(b) has theta_p(x + iy) != 0, then arctan(y/x) has no Q-linear formula (Aurifeuillian
  generators included when b = 2). Theorem 2(b) excludes only *non-Aurifeuillian* formulas.
  Consequence stated by BBG: for 2/7, 4/9, 5/9 only non-Aurifeuillian binary formulas are ruled out.
- Theorem 7 (Section 3.4): for b > 2 not a proper power there is no Q-linear b-ary Machin-type BBP
  arctangent formula for pi. Proof by Bang's theorem as described in Section 1(a) above.
- Appendix D, "Comments and Research Problems":
  - Problem (2), verbatim: "How many Q-linearly-independent binary Machin-type BBP arctangent zero
    relations exist?" followed by a request for upper bounds.
  - Problem (1): whether the two representations 3 + i = 2 + (1+i) = 4 - (1-i), which give two
    different BBP series for arctan(1/3), count as a trivial zero relation.
  - Problem (3): the original BBP formula does not appear to be a Q-combination of Machin-type
    generators; is there a simple derivation from one?
  - Problem (7): Zsigmondy's theorem has number-field generalizations (Schinzel 1974;
    Bilu-Hanrot-Voutier 2001) that should give an effective version for Q[i] and an exclusion
    criterion for arctangent formulas analogous to their Theorem 6.
  - Problem (8): exclusion criteria that handle Aurifeuillian generators (asked for logarithms).
  - Problem (10): whether pi is a combination of L(1, b^m, n, j) with b fixed; they expect this to
    need Q[zeta_n, b^(1/n)].
  - Problem (11): how to justify that Machin-type generators give all or most interesting cases.
- BBG's reference list contains Schinzel 1974 and Bilu-Hanrot-Voutier 2001 but not Schinzel 1962.

Citing papers:

- Semantic Scholar lists 25 citing items: Bailey and Borwein expository pieces (2005, 2009), Calcut
  2009, Adegoke 2010 and 2011, Mendonca 2012 ("Sagan numbers", arXiv:1209.2348), Braun-Romberger-Bentz
  2016 (arXiv:1609.03036), about a dozen viXra notes by E. Valdebenito (2016-2018), Kary 2019,
  Barsky-Munoz-Perez-Marco (Acta Arith. 2021), Bailey's 2021 Monthly memorial article, and two
  2025-2026 arXiv items —
  [Semantic Scholar citation record](https://api.semanticscholar.org/graph/v1/paper/DOI:10.4153/CJM-2004-041-2/citations?fields=title,year,authors,externalIds,venue&limit=200).
- OpenAlex lists 22, adding Chan, "Machin-type formulas expressing pi in terms of phi" (Fibonacci
  Quart. 2008) and two chapters of Borwein-Bailey, Mathematics by Experiment (2008) —
  [OpenAlex citation record](https://api.openalex.org/works?filter=cites:W2112047337).
- The two recent arXiv items are unrelated to arctangent formulas: a random-walk paper that builds
  coin-flipping estimators of pi — [arXiv:2512.21254](https://arxiv.org/abs/2512.21254) — and a
  spectral-geometry paper on triangles — [arXiv:2609.38953](https://arxiv.org/abs/2609.38953).
- Calcut 2009 is expository (Gaussian integers, Stormer's theorem, history); it cites BBG but proves
  nothing about binary generators (read in full text) —
  [Calcut 2009](https://www2.oberlin.edu/faculty/jcalcut/gausspi.pdf).
- Barsky-Munoz-Perez-Marco cite BBG once, in passing, and state that they find no new formulas and
  prove no classification (via page summary) —
  [arXiv:1906.09629](https://arxiv.org/abs/1906.09629).
- Adegoke-Lafont-Layeni cite BBG only for the rational-or-normal conjecture (via page summary) —
  [arXiv:1603.07395](https://arxiv.org/abs/1603.07395).
- Bailey's Compendium summarizes BBG as showing that pi has no degree-1 BBP-type formula outside
  bases that are powers of two, and credits BBG with a structure theory for arctangent formulas
  (read in full text) — [Bailey, Compendium, 8 April 2023](https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf).
- Kristensen and Mathiasen (J. Number Theory 2023) do not mention BBG at all (via page summary) —
  [arXiv:2208.07696](https://arxiv.org/abs/2208.07696).

### Inferences
- In BBG's notation the note's Theorem A says: the space of zero relations among the minimal
  generators is exactly two-dimensional, spanned by (35) and (36). That is a direct answer to
  Problem (2). I verified that (35) and (36) are R2 - R1 and R3 - R1 in the note's notation
  (alpha_1 = -arctan(1/2), beta_1 = -pi/4, beta_2 = -pi/4 + arctan(1/2), beta_3 = pi/4 - 2 arctan(1/2)).
- Corollary 1 of the note answers Problem (1): in the full set the extra relations are exactly the
  elementary identities, of which the arctan(1/3) coincidence is the m = 1 case.
- Bailey's summary of BBG ("no other degree-1 BBP-type formulas") is stronger than what BBG prove
  (they treat Machin-type formulas only). The note's Parts III and IV, which use Baker's theorem on
  the whole degree-1 class, are closer to that stronger statement than BBG is; this is worth saying
  carefully, because the literature already half-believes it.
- Parts III-IV of the note also line up with BBG's Problem (10) (the note's sub-series lemma works
  in exactly the field Q(zeta, 2^(1/n)) that BBG name).

### Gaps
- Not all 25 citing items were opened. Mendonca 2012, Braun et al. 2016, Kary 2019, Chan 2008 and
  the Valdebenito notes were judged irrelevant from title and venue only.
- BBG's Problem (2) could have been answered in a paper that does not cite BBG. Searches 3, 5, 13
  and 14 were aimed at that and found nothing.

---

## 3. What does Gasull-Luca-Varona 2023 prove? Follow-ups 2023-2026?

### Takeaway
GLV classify two-term formulas with dyadic-type arguments and nothing with three or more terms;
they do not mention BBG, BBP formulas or primitive divisors in that part. Six citing works to
November 2026, none a classification of the binary generator set.

### Cited Findings
- Bibliographic: A. Gasull, F. Luca, J. L. Varona, "Three essays on Machin's type formulas",
  Indag. Math. (N.S.) 34 (2023) 1373-1396, DOI 10.1016/j.indag.2023.07.002; arXiv v1 1 Feb 2023,
  v2 16 Jul 2023 — [arXiv:2302.00154](https://arxiv.org/abs/2302.00154).
- First essay, Theorem 1 (via page summary of the full text): classifies all
  x1 arctan(z1) + x2 arctan(z2) = pi/4 with rational x_k and rational 0 < z1 < z2 < 1 where each z_k
  is 2^a/b or b/2^a; the case with both exponents zero is left to Stormer. The answer is ten
  sporadic solutions plus two one-parameter families,
  (1, 1/(2^(a+1)+1), 1, 2^a/(2^a+1)) and (1, 1/(2^(a+1)-1), 1, (2^a-1)/2^a) —
  [ar5iv full text](https://ar5iv.labs.arxiv.org/html/2302.00154).
- The sporadic list includes (-1, 1/7, 2, 1/2) and (1, 1/7, 2, 1/3); the second family at a = 1 is
  arctan(1/3) + arctan(1/2). So R2, R3 and the Hutton/Euler formula all appear —
  [ar5iv full text](https://ar5iv.labs.arxiv.org/html/2302.00154).
- Tools in that essay (via page summary): factorization in Z[i], the restriction on rational values
  of tan of rational angles, the Diophantine equations x^2 + 1 = 2 y^n and x^2 + 2^a = y^n (their
  references are Cohn 1996 and Luca 2002), and a bounded computer search. The primitive divisor
  theorem is used only in the third essay (golden section) —
  [ar5iv full text](https://ar5iv.labs.arxiv.org/html/2302.00154).
- Second essay: a generating method showing two-term formulas exist with arbitrarily small Lehmer
  measure. Third essay: corrects Luca-Stanica (Int. J. Number Theory 2009) on two-term formulas in
  powers of the golden section — [arXiv:2302.00154](https://arxiv.org/abs/2302.00154).
- The bibliography (24 items) has Stormer 1895 and 1899, Lehmer 1938, Todd 1949, Wetherfield 1996,
  Chien-Lih 1997, Tweddle 1991, Calcut 1999 and 2009, Chamberland-Herman 2019, Chan 2008,
  Luca-Stanica 2009, Guillera 2007 (a Spanish-language history of pi algorithms). It has no
  Borwein-Borwein-Galway, Bailey, Schinzel or Bilu-Hanrot-Voutier —
  [ar5iv full text, references](https://ar5iv.labs.arxiv.org/html/2302.00154).
- Citing works per OpenAlex (6): four papers by Abrarov, Siddiqui, Jagpal, Quine (2023-2025, on
  iteration and rational approximation for two-term formulas); Tran, "A geometric generalization of
  the Euler-Machin formula ..." (Fibonacci Quart. 2025); Farhi, "On refinements of two-term
  Machin-like formulas" (arXiv, Jan 2026) —
  [OpenAlex citation record](https://api.openalex.org/works?filter=cites:W4385076198).
- Farhi 2026 is a construction (continued-fraction refinement of a two-term formula), not a
  classification, and its abstract mentions neither powers of two nor BBP —
  [arXiv:2601.10300](https://arxiv.org/abs/2601.10300).
- Craig-Wood 2025 (v2 Sep 2026) is a constrained PSLQ search for low-Lehmer-measure relations; no
  classification or binary content in the abstract —
  [arXiv:2508.08307](https://arxiv.org/abs/2508.08307).

### Inferences
- GLV neither proves nor conjectures Theorem A. It partly overlaps it: the two-term relations among
  the note's generators appear in GLV's list, but those are already Stormer's, because every
  generator is the arctangent of a reciprocal integer.
- GLV and BBG are two disjoint literatures on the same objects: GLV's community (Machin-type
  formulas, Lehmer measure) does not cite the BBP literature and vice versa. A paper that cites both
  and Schinzel 1962 would be bridging them.
- GLV's parametric families are, in BBG's terms, the elementary identity of the full generator set
  written with non-reciprocal arguments.

### Gaps
- The Semantic Scholar citation list for GLV returned HTTP 429; only OpenAlex was used.
- Tran 2025 and the four Abrarov et al. papers were not opened.

---

## 4. Classical classification results (Stormer, Lehmer, Todd, Wetherfield, Tweddle, Chien-Lih, Arndt)

### Takeaway
The classical literature gives the general machinery (unique factorization in Z[i]; arctangents of
"Stormer numbers" as a basis) and complete lists only for two terms; for restricted argument sets
such as powers of two or Mersenne-type numbers with any number of terms, no theorem was found.

### Cited Findings
- Stormer: exactly four two-term formulas with reciprocal-integer arguments; a necessary and
  sufficient criterion (1896) for given integers to admit a relation; 102 three-term formulas found;
  he asked whether there are infinitely many more (via page summary) —
  [Yamada, arXiv:1811.09273](https://arxiv.org/abs/1811.09273).
- Yamada, "Three-term Machin-type formulae" (arXiv v1 Nov 2018, v6 Mar 2025; no journal reference on
  the arXiv page): only finitely many nondegenerate three-term formulas, with explicit (very large)
  bounds, by linear forms in two and three logarithms —
  [arXiv:1811.09273](https://arxiv.org/abs/1811.09273).
- Todd 1949 (Amer. Math. Monthly 56, 517-528): arctan n is reducible exactly when the largest prime
  factor of 1 + n^2 is less than 2n; every arctan(n) is a unique integer combination of arctangents
  of Stormer numbers — [Wikipedia, Stormer number](https://en.wikipedia.org/wiki/St%C3%B8rmer_number);
  restated with a slightly different definition in Kroesche, Littlejohn, Reinhart, "Carl Stormer and
  his Numbers" (arXiv Nov 2025, v3 Apr 2026) — [arXiv:2511.03030](https://arxiv.org/abs/2511.03030).
- Lehmer 1938 introduced the measure; Wetherfield 1996 and Chien-Lih 1997 are about producing
  low-measure formulas, not classifying — [MathWorld, Machin-Like Formulas](https://mathworld.wolfram.com/Machin-LikeFormulas.html).
- Tweddle 1991 is historical: Machin already had all four two-term formulas in 1706, so the usual
  attributions of (2,3), (2,7), (3,7) to Euler 1737, Hermann 1706 and Hutton 1776 are disputed (read
  in full text) — [Calcut 2009](https://www2.oberlin.edu/faculty/jcalcut/gausspi.pdf).
- Wikipedia's Machin-like formula article states the four-solution result and the prime-factor
  recipe for building formulas; it mentions neither BBP, powers-of-two arguments, BBG nor GLV (via
  page summary) — [Wikipedia, Machin-like formula](https://en.wikipedia.org/wiki/Machin-like_formula).
- MathWorld gives the two-term count and tabulation counts for longer formulas; no completeness
  results beyond two terms; no binary or BBP discussion (via page summary) —
  [MathWorld, Machin-Like Formulas](https://mathworld.wolfram.com/Machin-LikeFormulas.html).
- Arndt's page lists relations up to 27 terms organized by the set of primes 4k+1 dividing the
  A^2 + 1, from an exhaustive search of arguments up to 10^14; no claim of completeness and nothing
  on arguments 2^n or 2^n +- 1 (via page summary) —
  [Arndt, arctan relations for pi](https://www.jjj.de/arctan/arctanpage.html).
- Closest classical analogue of "restricted argument set, any tool": Luca-Stanica 2009 and GLV's
  third essay classify two-term formulas in powers of the golden section, the latter using the
  primitive divisor theorem — [arXiv:2302.00154](https://arxiv.org/abs/2302.00154).

### Inferences
- In Todd's language Theorem A is a statement about which of the numbers 2^m and 2^m - 1 share
  Gaussian primes: beyond 1, 2, 3, 7 each has a prime that no other number of the family has. I
  found no place where this is said for this family.
- Naming: BBG credit (2,3) to Euler 1738, (2,7) to Hermann 1706, (3,7) to Hutton 1776; Calcut,
  following Tweddle, credits all three to Machin 1706. The note's "Hutton 1776 / Euler 1779" follows
  the BBG/Craig-Wood convention; a sentence acknowledging Tweddle would pre-empt a referee.

### Gaps
- Stormer's 1896 criterion and Todd's paper were not read in the original; statements are from
  secondary sources.
- Wetherfield's and Chien-Lih's Gazette notes were not opened.
- I could not confirm whether Yamada's paper has appeared in a journal.

---

## 5. Primitive divisor results that would make Theorem A a corollary

### Takeaway
Bang's theorem gives the non-Aurifeuillian half and Schinzel 1962 gives the Aurifeuillian half, so
the arithmetic input of Theorem A is entirely known; the general number-field theorems
(Schinzel 1974, Stewart, Voutier, Bilu-Hanrot-Voutier) do not by themselves give it for all n.

### Cited Findings
- Bang 1886 / Zsigmondy: 2^n - 1 has a primitive prime factor except for n = 1 and n = 6 —
  [Wikipedia, Zsigmondy's theorem](https://en.wikipedia.org/wiki/Zsigmondy%27s_theorem); BBG state
  and use it as their Theorem 3 —
  [BBG 2004](https://www.cambridge.org/core/journals/canadian-journal-of-mathematics/article/finding-and-excluding-bary-machintype-individual-digit-formulae/BB7919C8E1AE66878AE8D7BC7F0EBFA3).
- Schinzel, "On primitive prime factors of a^n - b^n", Proc. Cambridge Philos. Soc. 58 (1962)
  555-562 — [Cambridge record](https://www.cambridge.org/core/journals/mathematical-proceedings-of-the-cambridge-philosophical-society/article/on-primitive-prime-factors-of-anbn/FF4F8CB4D5BEDD2854151670559F36C6).
  Stewart's account: for coprime a, b with ab a square or twice a square, the largest prime factor
  of a^n - b^n is at least 2n + 1, excluding n = 4, 6, 12 for (a, b) = (2, 1); the proof shows that
  a^n - b^n has at least two primitive divisors, using an Aurifeuillian factorization (read in full
  text) — [Stewart, arXiv:1008.1274](https://arxiv.org/abs/1008.1274).
- Schinzel 1962 also gave new Aurifeuillian factorizations; Granville and Pleasants later showed he
  had found all of them; Stevenhagen and Brent showed how to compute them (read in full text) —
  [Stewart's commentary](https://uwaterloo.ca/pure-mathematics/sites/default/files/uploads/documents/schinzel-report1_0.pdf).
- Schinzel 1974 (J. reine angew. Math. 268/269, 27-33): for coprime algebraic integers A, B with
  A/B not a root of unity, A^n - B^n has a primitive prime ideal divisor for n > N(d), d the degree
  of A/B. Stewart 1977: N(d) = max{2(2^d - 1), e^452 d^67} (read in full text) —
  [Stewart's commentary](https://uwaterloo.ca/pure-mathematics/sites/default/files/uploads/documents/schinzel-report1_0.pdf).
- Schinzel 1993 (Math. Comp. 61, 441-444): the same for A^n - zeta_k B^n once n exceeds
  c (1 + log k)^(1 + epsilon) (read in full text) —
  [Stewart's commentary](https://uwaterloo.ca/pure-mathematics/sites/default/files/uploads/documents/schinzel-report1_0.pdf).
- Bilu-Hanrot-Voutier 2001: every Lucas or Lehmer number with n > 30 has a primitive divisor; before
  that Voutier had the constant 30030 (read in full text) —
  [Stewart, arXiv:1008.1274](https://arxiv.org/abs/1008.1274).
- Gaussian Mersenne numbers (1+i)^n - 1: norm 2^n - 2^(1 + n/2) cos(n pi/4) + 1; the primality
  literature (Berrizbeitia-Iskra 2010) is about when the norm is prime —
  [MathWorld, Gaussian Mersenne Prime](https://mathworld.wolfram.com/GaussianMersennePrime.html).
  Chamberland 2003 connects them to binary BBP formulas for logarithms —
  [Chamberland 2003](https://cs.uwaterloo.ca/journals/JIS/VOL6/Chamberland/chamberland60.pdf).

### Inferences
- Lemma 2 of the note is the statement that the Gaussian Mersenne number (1+i)^n - 1 and its twin
  (1+i)^n + 1 each have a primitive prime divisor in Z[i] for odd n >= 7. That is Schinzel 1962 for
  (a, b) = (2, 1), n = 4 mod 8, read through his proof. The note's own proof (size bound for
  n >= 309 plus computation to 801) is a re-derivation.
- The exceptions the note recalls (2^4 - 1, 2^12 - 1, 2^20 - 1) are consistent with Stewart's list
  n = 4, 6, 12 for the bound P >= 2n + 1: by direct arithmetic Phi_4(2) = 5, Phi_12(2) = 13 and
  Phi_20(2) = 5 * 41 each have a single primitive prime, and n = 20 is absent from Stewart's list
  only because 41 = 2 * 20 + 1 still meets the bound, while n = 6 fails the bound for Bang's reason.
  This is my arithmetic, not a quotation of Schinzel.
- Bilu-Hanrot-Voutier does not apply to (1+i, 1): neither the sum nor its square is a rational
  integer, so it is not a Lucas or Lehmer pair; and for the Lucas pair (2, 1) it only reproduces
  Bang (one primitive divisor of 2^(4n) - 1), not one in each Aurifeuillian factor. Schinzel 1974
  with Stewart's or Voutier's constant applies (degree 2) but leaves an astronomically large finite
  range. So BBG's Problem (7), which points to Schinzel 1974 and BHV, names tools that are not
  sufficient on their own; Schinzel 1962 is the one that closes the binary case.
- For Theorem B the atoms Phi_m(+-t) and Phi_m(+-i 2^(2^j)) are of the shape A^n - zeta B^n; Schinzel
  1993 is the general theorem behind "every atom of large index has a private prime", again only
  beyond an ineffective-in-practice bound, so the note's direct argument is needed for small indices.

### Gaps
- Schinzel 1962 itself is paywalled; I did not see the exact hypothesis (squarefree kernel k(ab),
  the factor eta, n/(eta k) odd) or his exact list of exceptions. The note's author should read it
  before submission; the statement to look for is "at least two primitive prime factors" and its
  exceptional triples (n, a, b).
- Voutier's general number-field bound (I recall n > max{2(2^d - 1), 4000 (d log 3d)^12}, Math.
  Proc. Cambridge Philos. Soc. 1998) was not re-verified in this session.
- A paper titled "On a number-theoretic result of Zsigmondy in domains of quadratic integers"
  (Steidl, Hanler, Tasche; Arch. Math. 53 (1989) 30-39) surfaced as a lead for a Zsigmondy theorem
  in rings like Z[i]; the publisher page required sign-in and the content is not verified —
  [Springer record](https://link.springer.com/article/10.1007/BF01194869). It should be checked: if
  it states a full Zsigmondy theorem for Z[i] with explicit exceptions, it is a second source for
  Lemma 2.
- No source found states "(1+i)^n - 1 has a primitive prime divisor for every n except ..." as a
  theorem about Gaussian Mersenne numbers (search 10).

---

## 6. Work by Chamberland, Bailey, Lafont, Adegoke, Guillera and others on binary BBP arctangent formulas, zero relations, exhaustive lists

### Takeaway
This literature constructs formulas and proves individual zero relations; its completeness
statements are all experimental (PSLQ) and several are flagged as not understood. Nothing
classifies the pi-formulas or the zero relations.

### Cited Findings
- Chamberland 2003 (read in full text): binary BBP formulas for log p from
  Re log Phi_m((+-1 + i)/2^n) and Re log Phi_m((+-1 + sqrt(3) i)/2^n); defines generalized
  Gaussian-Mersenne primes; notes redundancies explained by Aurifeuillian identities; proves a
  general cyclotomic factorization (Theorem 3.1). It treats logarithms only, cites BBG for related
  questions, and records that it was unknown whether log 23 has a binary BBP formula —
  [Chamberland 2003](https://cs.uwaterloo.ca/journals/JIS/VOL6/Chamberland/chamberland60.pdf).
- Chamberland and Herman, "Arctangent formulas and pi", Amer. Math. Monthly 126 (2019) 646-650,
  exists and is cited by GLV among term-splitting procedures —
  [ar5iv, GLV references](https://ar5iv.labs.arxiv.org/html/2302.00154).
- Bailey's Compendium, version of 8 April 2023 (read in full text) —
  [Bailey, Compendium](https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf):
  - Section 3: binary formulas found by PSLQ for arctan q coincide, in all cases studied, with the
    q arising from T = product of (1 +- (1+i)^u / 2^v)^w; a list of 15 rationals whose arctangents
    "appear to be" linearly independent; it is stated as unknown whether arctan(2/7) has a binary
    BBP formula.
  - Section 12: zero relations found by PSLQ; a table of counts of linearly independent zero
    relations by (degree, base, length), including for degree 1: one at (16, 8), five at
    (2^12, 24), three at (2^20, 40), seven at (2^60, 120); the text says it is not understood why
    zero relations occur for some parameters and not others.
  - The compendium says it is not meant to be comprehensive.
  - It identifies its formulas (2) and (3) as published by Euler in 1779, citing Craig-Wood, and
    notes that the alternating form of Ferguson's formula differs from the original BBP formula by
    a quarter of zero relation 111.
- Craig-Wood, "Euler found the first binary digit extraction formula for pi in 1779", Euleriana 3(1)
  (2023) 23-30, DOI 10.56031/2693-9908.1049 —
  [Euleriana record](https://scholarlycommons.pacific.edu/euleriana/vol3/iss1/3).
  Wikipedia's BBP article says the second Euler formula comes from expanding
  pi = 8 arctan(1/3) + 4 arctan(1/7) and yields 30 bits per 21 divisions, the same rate as Bellard's
  10 per 7 (via page summary) —
  [Wikipedia, BBP formula](https://en.wikipedia.org/wiki/Bailey%E2%80%93Borwein%E2%80%93Plouffe_formula).
- Lafont, "Degree 1 BBP-Type Zero Relations" (manuscript, 27 Jan 2011): proves eight previously
  unproved zero relations of the Compendium, five of length 24 in base 2^12 and three of length 40
  in base 2^20, by Fourier analysis of the coefficient vectors; it says all degree-1 binary formulas
  then listed are proved; it makes no completeness claim (via page summary) —
  [Lafont report](https://www.slideshare.net/slideshow/zero-relations/13076965).
  His OEIS wiki page lists a handful of zero relations with no completeness claim —
  [OEIS wiki, Lafont](https://oeis.org/wiki/User:Jaume_Oliver_Lafont/Zero_relations).
- Adegoke, Lafont, Layeni, "A class of digit extraction BBP-type formulas in general binary bases",
  Notes Number Theory Discrete Math. 17 (4) (2011) 18-32: explicit formulas in bases 2^(12p), binary
  BBP representations for arctangents of an infinite family of rationals (including 1/6 at p = 3),
  several zero relations; no completeness claim (via page summary) —
  [arXiv:1603.07395](https://arxiv.org/abs/1603.07395).
- Adegoke and Layeni, "BBP-type formulas, in general bases, for arctangents of real numbers", Notes
  Number Theory Discrete Math. 19 (3) (2013) 33-54: analytic derivations, not classification —
  [NNTDM record](https://nntdm.net/volume-19-2013/number-3/33-54/).
- Barsky, Munoz, Perez-Marco, "On the genesis of BBP formulas", Acta Arith. 198 (2021) 401-426: a
  generating procedure that recovers the main known formulas and explains some null formulas; the
  authors say they find no new formulas, prove no classification, and pose as natural the question
  whether all degree-1 null formulas come from combining theirs (via page summary) —
  [arXiv:1906.09629](https://arxiv.org/abs/1906.09629).
- Kristensen and Mathiasen, "BBP-type formulas — an elementary approach" (J. Number Theory 2023):
  an LLL-based search with exact verification; the authors say it does not recover all known
  formulas; no classification (via page summary) — [arXiv:2208.07696](https://arxiv.org/abs/2208.07696).
- Guillera: the only item found is a 2007 Spanish-language survey of formulas and algorithms for pi
  cited by GLV — [ar5iv, GLV references](https://ar5iv.labs.arxiv.org/html/2302.00154).

### Inferences
- Theorem B's family is the imaginary-part twin of Chamberland's construction and a Galois-invariant
  subfamily of the set behind Bailey's formulas (11)-(12). Bailey's experimental remarks ("coincide
  in all cases studied", "appear to be independent") are exactly the kind of statement Theorem B
  turns into a theorem for the pi-relations. Nothing found proves or conjectures Theorem B.
- Outside the assigned scope but relevant to positioning Part III: counting the basis elements of
  the note's Theorem C by period, I get 1, 5, 3 and 7 zero relations at periods 8, 24, 40 and 120.
  These equal Bailey's empirical table entries at (16, 8), (2^12, 24), (2^20, 40) and (2^60, 120),
  and Lafont's 5 + 3. If the note's Theorem C is right, it proves Bailey's degree-1 binary counts
  for those rows and answers both his "not understood" remark and the Barsky-Munoz-Perez-Marco
  question, for the class with weights 2^(-floor(k/2)). I did not check the other rows of the table
  (for example (2^30, 60), listed with one relation) against the note; the note's own code should be
  run against the whole degree-1 column before this is claimed.
- The device in the note's Theorem E (add a logarithm-type zero series to an arctangent formula) is
  the same device by which the Compendium relates the BBP formula to Ferguson's; this confirms the
  note's own remark that the device is old.
- The Wikipedia efficiency remark (Euler's formula equals Bellard's in terms per bit) uses a
  different cost measure from the note's per-prime state; the paper should say so explicitly, or a
  reader will think the comparison with Bellard is missing.

### Gaps
- Craig-Wood's Euleriana article could not be opened (HTTP 403 on the PDF); which arctangent
  identity underlies the second Euler formula is taken from Wikipedia, supported by my reading of
  the denominators in the Compendium's formula (3) (multiples of 3 from arctan(1/3) and of 5 from
  arctan(1/7)).
- Chamberland-Herman 2019 could not be opened (HTTP 403); its content is not verified.
- Broadhurst's manuscript "Vanishing polylogarithmic ladders" (2000), the one source Bailey credits
  with discussing why zero relations occur, is listed as available from its author only and was not
  seen.
- No dedicated search on Guillera was possible after the budget cap.

---

## 7. Is "the only Machin-type formulas with arguments 1/2^m and 1/(2^m - 1) are ..." stated anywhere informal?

### Takeaway
Not found. The two searches aimed at MathOverflow, Math StackExchange and CORDIC-angle discussions
returned nothing on linear independence of arctan(1/2^n), and the reference pages checked do not
contain the statement.

### Cited Findings
- Wikipedia's Machin-like formula article: no mention of binary or powers-of-two arguments —
  [Wikipedia, Machin-like formula](https://en.wikipedia.org/wiki/Machin-like_formula).
- Wikipedia's BBP article: no mention of BBG's theorem and no classification or optimality statement
  for binary formulas — [Wikipedia, BBP formula](https://en.wikipedia.org/wiki/Bailey%E2%80%93Borwein%E2%80%93Plouffe_formula).
- MathWorld's BBP-type formula entry reports BBG's non-binary exclusion only —
  [MathWorld, BBP-Type Formula](https://mathworld.wolfram.com/BBP-TypeFormula.html).
- MathWorld's Machin-like page and Arndt's page: nothing on the 2^n, 2^n +- 1 family —
  [MathWorld, Machin-Like Formulas](https://mathworld.wolfram.com/Machin-LikeFormulas.html);
  [Arndt](https://www.jjj.de/arctan/arctanpage.html).
- Lafont's OEIS wiki page: a short list of zero relations, no such statement —
  [OEIS wiki, Lafont](https://oeis.org/wiki/User:Jaume_Oliver_Lafont/Zero_relations).

### Inferences
- The linear independence of the CORDIC angles arctan(2^(-k)), k >= 2, over Q together with pi is a
  special case of Theorem A that hardware and numerical-analysis readers would recognize; I found no
  statement of it. It could be worth one sentence in the paper.

### Gaps
- MathOverflow and Math StackExchange were covered by two general web searches only (queries 13 and
  14), not by on-site search. OEIS entries and comments were not searched at all. Blogs were not
  searched. These are the weakest parts of the negative result and should be re-run when search
  budget is available. Suggested queries: "arctan(1/2^n) linearly independent over Q",
  "CORDIC angles rationally independent", "Machin formula powers of two only",
  "binary BBP arctangent zero relations count".

---

## Search log

Web searches actually executed: 20. A 21st was refused because the session-wide search budget
(shared by all agents) was exhausted; after that only specific known documents and citation records
were fetched, with no further keyword searching.

1. Borwein Borwein Galway "Finding and excluding b-ary Machin-type individual digit formulae"
2. Gasull Luca Varona "Three essays on Machin's type formulas"
3. binary Machin-type BBP arctangent formulas classification primitive prime divisors Gaussian integers
4. Schinzel 1962 "On primitive prime factors of a^n - b^n" Aurifeuillian factors
5. "Machin-type" BBP arctangent "zero relations" binary pi classification all formulas arctan(1/2^m)
6. Chamberland "Binary BBP-formulae for logarithms and generalized Gaussian-Mersenne primes"
7. papers citing "Finding and excluding b-ary Machin-type" Borwein Galway BBP arctangent 2020..2026
8. Stormer theorem arctan(1/x) Grave problem two-term Machin formulas only four solutions proof Gaussian integers
9. Schinzel "primitive prime factors" "a^n - b^n" two primitive prime factors exceptions n = 4, 12, 20 Aurifeuillian "2^n"
10. Gaussian Mersenne numbers (1+i)^n - 1 primitive prime divisors theorem every n
11. Zsigmondy theorem Gaussian integers primitive divisors alpha^n - beta^n imaginary quadratic field exceptions list
12. Wikipedia "Machin-like formula" Stormer Lehmer measure two-term formulas rational arctangent linear relations
13. mathoverflow linear independence arctan(1/2^n) over rationals powers of two arctangent relations pi
14. "arctan(1/2^" OR "arctan(2^-k)" linearly independent over Q CORDIC angles math.stackexchange
15. Todd 1949 "A problem on arc tangent relations" reducible arctan n largest prime factor 1+n^2 Stormer numbers basis
16. Adegoke Layeni "BBP-type formulas, in general bases, for arctangents of real numbers"
17. Schinzel theorem "at least two primitive prime factors" a^n - b^n "n = 20" "n = 12" squarefree kernel k(ab) odd integer exceptions
18. David Bailey "Compendium of BBP-type formulas" 2023 arctangent formulas "Machin-type" binary pi zero relations proven
19. Lafont "Degree 1 BBP-type zero relations" proof eight zero relations compendium
20. arXiv 2024 2025 2026 BBP-type formula pi classification "no BBP" base proof linear independence logarithms arctangent Baker

Refused (not executed): "Machin" formulas "powers of two" OR "powers of 2" arctan classification
theorem "Mersenne" arctan(1/(2^n-1)) identities complete list.

Total executed: 20.

Citation-record lookups (not keyword searches): Semantic Scholar citations of DOI
10.4153/CJM-2004-041-2 (25 items); OpenAlex citations of the same (22 items); OpenAlex citations of
DOI 10.1016/j.indag.2023.07.002 (6 items). Failed lookups: Semantic Scholar citations of
arXiv:2302.00154 (HTTP 429); zbMATH record for BBG (HTTP 403).

Full texts read directly in this session: BBG 2004; Bailey's Compendium (8 Apr 2023); Chamberland
2003; Calcut 2009; Stewart's arXiv:1008.1274; Stewart's commentary on Schinzel.
