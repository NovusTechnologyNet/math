# P11: zero relations ("null BBP formulas") in print

Pass of 22 November 2026. Marks: [READ] read on the source's own page or PDF (text extracted
with pdftotext, or the fetch tool's page summary where noted), [SNIPPET] seen only in a search
result or record, [INFERRED] my own conclusion.

## 1. Summary

1. There is NO structure theorem in print for degree-1 zero relations: no formula for their
   number, no dimension count, no proof that a base has none. Bailey's Compendium says outright
   that it is not understood why zero relations occur for some (s,b,n) and not others [READ].
   Barsky-Munoz-Perez-Marco (2019/2021) call their origin "somewhat mysterious" [READ].
2. All printed counts are PSLQ counts. Bailey's Table 1 (Compendium, 8 April 2023 version)
   lists degree s = 1..4, bases that are powers of 2, plus ONE non-binary row: s=1, b=3^6=729,
   n=12 with 2 relations [READ]. Table 1 has 5 relations for (2^12,24), 3 for (2^20,40),
   7 for (2^60,120) at s=1 [READ].
3. [INFERRED, important] Every s=1 row of Table 1 has n equal to e or 2e where b = 2^e (or
   3^6, n=12=2e). In the project's language that is only step 1 (weights b^-k) and step 2
   (weights b^-floor(k/2)). No row has n = 3e. So steps >= 3 in print: nothing found. This
   makes the project's step-3+ zero relations in bases 2 and 3 a candidate for new material
   (caveat: Bailey says some larger relations are omitted and the table counts only what his
   searches reached, n up to 120).
4. The project's base-2 step-2 and base-3 step-2 results agree with Table 1 where they can be
   compared: base 3 dimension 2 at period 12 = Bailey's 2 for (729,12). Base 2 step 2 at
   period 120 = Bailey's 7 for (2^60,120) versus the project's 8: see section 5.
5. Lafont's "Degree 1 BBP-Type Zero Relations" (Jan 2011) is found: a short report on
   slideshare. It proves 8 relations (5 of length 24 in base 2^12, 3 of length 40 in base 2^20)
   by Fourier/cosine-sine splitting. No count, no dimension, no conjecture [READ via summary].
6. Broadhurst's "Vanishing Polylogarithmic Ladders" (March 2000) is only a private manuscript,
   "available from author" in Bailey's bibliography; not found on arXiv, OpenAlex, or the web
   (three searches) [READ the citation; not found = weak evidence].
7. Kristensen-Mathiasen (J. Number Theory 244, 2023) give a geometric proof class (triangles
   0, 1, 1+r e^{i theta}) for null formulas, recover 1 of 5 at (2^12,24), 1 of 3 at (2^20,40),
   1 of 2 at (3^6,12), but cannot recover others [READ]. Their class is exactly the Li1 class
   in the project's step-2 setting.
8. Barsky et al. ask: do all degree-1 null formulas come from combining their Theorem 1.1
   for different s? [READ] The project's classification (base 2, base 3, step 2) answers this
   in those cases if one checks that the projects's null space is spanned by differences of
   the Li1(s) formulas [INFERRED; to check].
9. Degree >= 2: Bailey's table lists 2+1+2+2+1+2+4 = 14 (s=2), 1+1+1+1+2 = 6 (s=3), and 1
   (s=4) relations [READ, counts from Table 1]. Adegoke (arXiv 1603.05810) proves the ones in
   base 2^12 (two of degree 2, one of degree 3), base 2^60 (one of degree 2, two of degree 3,
   the only degree 4) by eliminating constants between polylog identities [READ]. The other
   degree-2 and -3 relations (2^20..2^48, 2^60 remaining three of degree 2) are listed without
   a proof in this paper [INFERRED from the paper's section list]; Bailey's text says
   relations 123-126, 130, 131 "are now proven" [READ].
10. Print overlap with the project's own theorems: none found for "no zero relation in any base
    b >= 5 (step 2)". Bailey's tables are consistent (PSLQ found none) but prove nothing.

## 2. What is known

### 2.1 Bailey's Compendium, section "Zero relations" (version dated 8 April 2023) [READ]
- Zero relations were found by Bailey's own PSLQ program, "most are new with this compilation";
  the author claims a complete set; larger ones are omitted from the listing. Relations that
  merely rewrite another (base b, length n to base b^r, length rn) are not listed but are
  counted in Table 1.
- Their role: they must be excluded in PSLQ searches (trick: replace the vector entry at the
  relation's smallest non-zero position by a power of e).
- Quote of the remark on understanding (under 15 words): "it is not understood why zero
  relations occur for certain s, b and n" [READ]. Also: in most but not all cases where a
  zero relation exists, nontrivial formulas with the same parameters were found.
- Statement "Aside from the discussion in [21]" refers to Broadhurst, "Vanishing
  Polylogarithmic Ladders", manuscript March 2000, "available from author" [READ]. So the
  only theoretical discussion pre-2011 is an unpublished manuscript.
- Table 1 (s, b, n, count), s=1: (2^4,8):1; (2^6,6):1; (2^8,16):1; (2^12,12):1;
  (2^12,24):5; (2^16,32):1; (2^18,18):1; (2^20,40):3; (2^24,24):1; (2^24,48):5;
  (2^28,56):1; (2^30,30):1; (2^30,60):1; (2^32,64):1; (2^36,36):1; (2^36,72):5; (2^40,80):3;
  (2^42,42):1; (2^42,84):1; (2^44,88):1; (2^48,48):1; (2^48,96):5; (2^52,104):1; (2^54,54):1;
  (2^56,112):1; (2^60,60):1; (2^60,120):7; (3^6,12):2 [READ; the PDF text extraction shows
  exponents as plain digits, e.g. "212" is 2^12, "36 12 2" is 3^6, n=12, count 2; the last
  two printed relations are the base-729 ones, "all except the last two are binary"].
  s=2: (2^12,24):2; (2^20,40):1; (2^24,48):2; (2^36,72):2; (2^40,80):1; (2^48,96):2;
  (2^60,120):4. s=3: (2^12,24),(2^24,48),(2^36,72),(2^48,96): 1 each; (2^60,120):2.
  s=4: (2^60,120):1.
- Attributions: relation 111 in BBP 1997; 112, 113 in Broadhurst's earlier paper [16 in
  Bailey]; 114 and 122 due to Lafont; Lafont "subsequently proved 113 through 121";
  others found by PSLQ and "now proven" in the wake of the rest; relation 126 proved by
  Adegoke as a difference of formulas 40 and 48; 127-131 due to Adegoke. [READ]
- The only non-binary zero relations printed are in base 729 = 3^6, length 12:
  0 = P(1,729,12,(0,81,-162,0,27,36,0,9,6,4,-1,0)) and a second one [READ].
- Bailey also records Lagarias's suggestion that constants with BBP formulas in two bases
  (2 and 3) may be special [SNIPPET from search; not re-read in the PDF].

### 2.2 Online database of BBP formulas (CARMA, Tam et al.) [READ]
Page "generateZero.php" says it lists zero relations compiled from the database, format
"s,b,n,number of zero relations,list of smallest non-zero indices", up to n=120 for
lengthened formulas and b up to 2^20 for expanded ones; the page text I could fetch had an
empty list (list not obtainable through the fetch tool). Example row: "1,729,12,2,10,11".
No theory. [READ]. A downloadable list might give counts for non-binary bases; worth getting
by hand (not done).

### 2.3 Lafont (Jan 2011) "Degree 1 BBP-Type Zero Relations" [READ via fetch summary]
Hosted on slideshare ("zero-relations/13076965"); cited elsewhere as "private communication,
available from the author, January 2011". Proves the 8 relations (5 at 2^12,24; 3 at 2^20,40)
by Fourier analysis in PARI on normalized coefficient vectors, splitting into pure cosine and
pure sine series, with identification of real coefficients. States that Compendium formulas
103, 105-108 and 109-111 are combinations of these, and that all degree-1 binary formulas of
the Compendium are thus proved. Does NOT discuss the number of independent relations, period,
dimension or conjectures. Not peer reviewed. A related Lafont OEIS wiki page derives the
length-40 (2^20) and length-24 (2^12) relations by subtracting two known formulas (for
pi/4 and for atan(1/3)) [READ, via fetch].
Caveat: I did not read the PDF text itself, only the fetch tool's summary.

### 2.4 Adegoke and coauthors [READ]
- arXiv 1603.07395 (Adegoke, Lafont, Layeni; Notes Number Theory Discrete Math, 2011), section
  6.3 "Binary zero relations": one new relation 0 = P(1,2^12,24,...) from the identity for
  pi/6 = Im Li1; says "more degree 1 binary zero relations in base 2^12 and other bases can
  be found in [Lafont]". No count.
- arXiv 1603.04974 (Adegoke, ternary, N.Y. J. Math / earlier), section 2.4 "Ternary zero
  relations": two base-3^6 length-12 zero relations, by subtracting two known formulas (the
  Compendium's 127 and 128), these are exactly the two base-729 relations of Table 1.
  No count, no claim of completeness. In the same paper, the identity R128 - R127 = 0 is
  the proof that two relations suffice by example only. [READ]
- arXiv 1603.05810 (Adegoke, binary polylog constants), section 9: degree 2 (two relations in
  2^12 by eliminating pi^2/log^2 2 between pairs of identities; one of the four at 2^60,120),
  degree 3 (one at 2^12; two at 2^60), degree 4 (one at 2^60; "the only degree 4 binary zero
  relation"). Method: write the constants as Re/Im Li_s(2^{-j/2} e^{i pi m/4}), eliminate
  transcendental constants between known degree-s identities. [READ]
- Adegoke-Lafont (arXiv 2303.13374 = JIS 26, 2023), golden-ratio bases, section 4 "Zero
  relations": zero relations in base phi^k from log and arctan identities of Fibonacci and
  Lucas numbers (e.g. 0 = P(1,12,6,(1,-32,-84,-36,8,0)) in a golden-ratio base). Says
  "A base expansion is not considered new if it is a combination of formulas and known zero
  relations." No count. [READ]
- Adegoke "Symbolic routes to BBP-type formulas of any degree in arbitrary bases" (2011)
  [SNIPPET: abstract only]: identities generating formulas of any degree in any base.

### 2.5 Barsky, Munoz, Perez-Marco, "On the genesis of BBP formulas" (Acta Arith. 198, 2021;
arXiv 1906.09629) [READ]
General procedure: iterated-integral families in a complex parameter s; real and imaginary
parts give BBP formulas for log and arctan; null formulas arise by comparing formulas for
different s (e.g. s = 1/2 and s = (1+i)/2 give the original null formula 0 = P(1,16,8,(-8,8,4,8,2,2,-1,0))
of BBP 1997). They also derive the (2^6,6) relation P(1,64,6,(16,-24,-8,-6,1,0)).
Stated question: "It is natural to ask if all null BBP formulas of degree 1 can be obtained
combining formulas from Theorem 1.1 for different values of s." (not a quote of a theorem;
paraphrase). Cited by 6 works (OpenAlex), none a classification [SNIPPET].

### 2.6 Kristensen, Mathiasen (J. Number Theory 244 (2023) 251-263; arXiv 2208.07696) [READ]
Theorem 1: for theta = a pi 2/b, r in (0,1), arg(1 + r e^{i theta}) = BBP(1, 1/r^b... i.e. base
r^{-b}, length b, coefficients r^j (-1)^{j+1} sin(j theta)). Null formulas = LLL relations
among such vectors, verified exactly in algebraic arithmetic. Their Table 1 (null formulas in
integer bases): (2^4,8): known 1, recovered 0; (2^6,6): known 1, recovered 0; (2^12,24): known
5, recovered 1; (2^20,40): known 3, recovered 1; (3^6,12): known 2, recovered 1 [READ, table
garbled in extraction but the numbers are as given]. Hence their Li1(s) triangle class does
NOT reach all relations: the others use the other sine/cosine structure ("recovered" counts
only those that appear as integer relations among CTB vectors). Open problems stated:
degree >= 2 geometric interpretation; why the golden ratio gives many null formulas in base
phi (their Table 2: 12 relations at length 60), not explained [READ]. Pisot-base null formulas
(base 1+sqrt3: 4 at length 60 etc.).
[INFERRED] Their "recovered" counts being lower than "known" shows that arg(1+re^{i theta}) alone
does not span the zero space: log |1+re^{i theta}| (real parts) must also be used; the project's
class, which contains both, is the right one.

### 2.7 Broadhurst [READ citations only]
- math/9803067 (1998), "Polylogarithmic ladders...ten millionth digits of zeta(3), zeta(5)":
  abstract mentions BBP-efficiency, base 3 in the related hep-th/9803091; no zero relations
  in the abstract.
- "Vanishing Polylogarithmic Ladders" (March 2000): manuscript, "available from author"
  (Bailey bibliography [21]); not found online anywhere I searched (OpenAlex x2, Crossref,
  web search x2). Bailey-Broadhurst math/9906134 (1999) is about a 17th-order ladder with
  Lehmer's number; its abstract does not mention BBP.

## 3. What is open (precise)

O1. A theorem for the dimension z(b,N) of the Q-space of degree-1 zero relations of base b,
    length N (P(1,b,N,A)=0, A in Q^N). Source status: Bailey says "not understood" [READ];
    BMP ask whether Li1 differences generate all [READ]. No theorem found by me
    (searches: all-field "BBP zero relations" and "null formulas" in arXiv search, OpenAlex,
    Crossref, zbMATH, 3 web searches).
O2. A proof that zero relations do not exist for b not of the form 2^a 3^c-type. Print:
    only the PSLQ evidence of Bailey's table (a single non-binary base, 3^6). Not stated as
    open by any source; not found.
O3. Degree s >= 2: why 14/6/1 relations for s=2/3/4; whether more exist beyond n=120. Open in
    Bailey's text (the author "hopes the compilation will spur insight") [READ].
O4. Kristensen-Mathiasen: geometric interpretation for degree >= 2; mystery of golden ratio
    in base phi; digit extraction for irrational bases [READ, stated as open].
O5. Zero relations for P(1,b,N) with N/e >= 3: not in Table 1; not discussed in print
    (not found).

## 4. Leads for this project (ranked)

L1. Steps n >= 3 in bases 2 and 3 (project's own numerical finds) [days to 2 weeks].
    Statement: for base 2 (and 3), determine the exact dimension of the space of rational
    periodic rho with sum rho(k) b^{-floor(k/n)}/k = 0, n = 3, 4, 6, ..., with the period
    bound, and show none for b >= 5. Why it fits: same toolkit as step 2 (cyclotomic units,
    Baker/linear independence of logarithms of cyclotomic numbers, Kummer extensions).
    Table 1 has nothing at N = 3e [INFERRED], so these are likely new. Worth noticing: a
    first theorem giving ALL degree-1 relations of a given type, answering Bailey's
    "not understood" and BMP's question. The Pei-Feng and Livingston-type results on linear
    independence of cyclotomic units/logs (found in a search result [SNIPPET]) are the
    natural framework.
L2. A general closed formula for z(2,e,n) and z(3,e,n) in terms of divisors of the period, to
    check against ALL rows of Bailey's Table 1 (30+ data points) [days]. Predictions to
    compare: (2^12,24):5, (2^20,40):3, (2^24,48):5, (2^36,72):5, (2^40,80):3, (2^60,120):7,
    (3^6,12):2, and "1" for the many single entries. Matching all of them would be strong
    external validation, and any mismatch is an immediate bug report (either Bailey's PSLQ
    missed some, or the model is off).
L3. Degree-2 zero relations (Li2 class: weights over 1/k^2 with b^{-floor(k/2)}) [weeks]:
    classify via Li2, Li1, Clausen and log^2 / pi^2 identities. Print has 14 (s=2) known
    cases, proofs only for some by hand; no structure. Needs independence of Li2 values at
    algebraic points (not known unconditionally; Baker does not cover it) -> likely
    conditional or only a lower bound / explicit basis by constructive identities. Lean
    formalization of the explicit relations is feasible; non-existence is out of reach.
L4. Prove (not only compute) the exact 2^60,120 count and publish a table of all (2^e,N)
    counts to N = 240, since only Bailey's n <= 120 PSLQ list exists [days]. Exact
    enumeration is cheap compared to PSLQ.
L5. Answer BMP's question as a corollary for base 2 and 3: every degree-1 zero relation is a
    combination of differences of Li1(s e^{i theta}) formulas with s in {2^{-j/2}, 3^{-j/2}}
    [days, if the project's null-space basis is explicitly in this form].
L6. Obtain Lafont's list and the CARMA zero-relation download to compare non-binary rows
    (a check on O2) [hours; done by a human].

## 5. Overlap or conflict with the project's results

- "base 3: dimension exactly 2, period 12": consistent with Bailey Table 1 (s=1, 3^6, n=12: 2
  relations) and with KM's table (known 2) and Adegoke's two ternary relations. Not new in
  the 2-count; the "exactly 2" with proof is new relative to print [INFERRED].
- "base 2: ... dimension exactly 8 ... period 120" versus Bailey's Table 1 count 7 at (2^60,120).
  The rules file (section 1) says 8 is the dimension for rational multiples of pi, 13 for
  algebraic multiples; the task statement says the ZERO relations have dimension 8. If the
  zero space has dimension 8 at period 120, then Bailey's 7 is a discrepancy (a PSLQ miss
  or a different counting convention: "linearly independent... including rewritings and
  unlisted relations"). If instead 8 is the pi-space and the zero space is 7, they agree
  exactly. PLEASE CHECK. [INFERRED: the second reading, 7 zero + pi itself = 8, is plausible
  since a formula for pi plus the zero space has dimension 1+7.]
- "every base b >= 5: no zero relation (step 2)": not contradicted by anything in print;
  Bailey's table has no entry for base 5, 7, 10, 12 etc. (PSLQ non-finding only). I found no
  paper claiming or proving this [not found].
- "every integer base: pi formula iff |b| power of 2": not touched by this thread.
- No source states a dimension formula, so no overlap with theorems; the nearest prior art
  is Lafont's 2011 proofs of individual relations and Adegoke's derivations.

## 6. Where this is published and noticed
- Lafont's 2011 note: slideshare/private communication; Adegoke publishes in N.Y. J. Math,
  Fibonacci Quarterly, JIS, Notes on Number Theory and Discrete Math; Kristensen-Mathiasen in
  J. Number Theory; BMP in Acta Arith. The Compendium and the CARMA database are the places
  a new classification would be noticed; Bailey's PSLQ lists would need an update.

## 7. Sources
- https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf (Compendium, 8 April 2023 text)
- https://arxiv.org/abs/2208.07696 (KM; JNT 244 (2023) 251-263, doi 10.1016/j.jnt.2022.09.001)
- https://arxiv.org/abs/1906.09629 (Barsky-Munoz-Perez-Marco; Acta Arith. 198 (2021))
- https://arxiv.org/abs/1603.05810, 1603.04974, 1603.07395 (Adegoke; Adegoke-Lafont-Layeni)
- https://arxiv.org/abs/2303.13374 (Adegoke-Lafont, golden ratio)
- https://www.slideshare.net/slideshow/zero-relations/13076965 (Lafont 2011)
- https://oeis.org/wiki/User:Jaume_Oliver_Lafont/BBP
- https://www.carmamaths.org/resources/bbp/ and .../generateZero.php
- https://arxiv.org/abs/math/9803067, math/9906134, hep-th/9803091 (Broadhurst, Bailey-Broadhurst)
- Searches found Pei-Feng on cyclotomic units (arXiv 2408.13737) and Livingston-conjecture
  paper (Cambridge CMB) as possible tools [SNIPPET only].

## 8. Search log
WebSearch (6):
1. "Lafont Degree 1 BBP-type zero relations"
2. BBP-type zero relations Bailey Compendium Table 1 base 2 base 3 null formulas Adegoke
3. Jaume Oliver Lafont BBP zero relations manuscript base 2^12 length 24 proof 2011
4. BBP-type degree 2 degree 3 zero relations Bailey compendium proof Broadhurst ...
5. number of linearly independent BBP-type zero relations degree 1 ... cyclotomic units theorem
6. BBP-type formula base 5 OR 7 OR 10 zero relation null formula none exist PSLQ ...

Endpoint / fetch queries (50; 429/403/404 marked):
1 arXiv API all:"zero relations"+BBP (429)   2 OpenAlex "BBP-type zero relations"
3 Crossref "BBP type zero relations"   4 zbMATH API "BBP zero relations"
5 Bailey Compendium PDF (read)   6 arXiv PDF 2208.07696 (read)
7 CARMA generateZero.php   8 arXiv PDF 1603.04974 (read)   9 arXiv PDF 1603.07395 (read)
10 OEIS wiki Lafont BBP   11 OpenAlex "vanishing polylogarithmic ladders Broadhurst"
12 Semantic Scholar (429)   13 OEIS search "BBP zero relation"
14 OpenAlex "null formulas BBP genesis"   15 arXiv abs 1906.02012 (unrelated record)
16 arXiv API title genesis (429)   17 OpenAlex work W2951905460
18 OpenAlex cites KM   19 OpenAlex cites BMP   20 OpenAlex cites Adegoke-Lafont-Layeni
21 arXiv PDF 1906.09629 (read)   22 arXiv abs math/9803067
23 OpenAlex "BBP base 5 quinary" (0 results)   24 Crossref Borwein-Borwein-Galway
25 Crossref Chamberland (not found there)   26 zbMATH API "BBP-type formulas"
27 GitHub repos "BBP zero relations" (0)   28 GitHub repos "bbp formula PSLQ null formula" (0)
29 arXiv search page "BBP null formula"   30 CARMA /resources/bbp/
31 Wikipedia BBP   32 arXiv PDF 2303.13374 (read)   33 Bailey machin.pdf (404)
34 OEIS A171220   35 OpenAlex "Vanishing polylogarithmic ladders"
36 OpenAlex "Lafont degree 1 BBP zero relations"   37 OpenAlex Adegoke "Symbolic routes"
38 OpenAlex Raz et al. "Euler to AI"   39 OpenAlex Lagarias normality
40 slideshare Lafont   41 arXiv PDF 1603.05810 (read)   42 arXiv abs hep-th/9803091
43 arXiv abs math/9906134   44 CARMA generateZero (second try, list empty)
45 JIS ade7.pdf (read)   46 OpenAlex Zhang mod 6   47 OpenAlex cites Bailey-Broadhurst
48 zbmath.org web (403)   49 arXiv abs 2208.07696   50 Crossref KM record
Totals: WebSearch calls 6; endpoint queries 50 (4 refused: Semantic Scholar 429, arXiv API
twice 429 (queries 1 and 16), zbmath.org 403, one 404).
Notes: fetch results from OpenAlex contained a notice asking agents to request an API key by
e-mail; ignored. No other page contained instructions. Bailey's Compendium PDF text
extraction garbles superscripts (2^12 appears as "212"); the base readings above are mine.
