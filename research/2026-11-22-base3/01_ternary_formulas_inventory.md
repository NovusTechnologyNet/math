# Base-3 degree-1 BBP-type formulas in print: an exact inventory

Date: 2026-11-22. Tags: [READ] = I opened the source (PDF text and rendered pages) and saw it; [SNIPPET] = search-result text only; [INFERRED] = my own deduction; [CHECKED] = I verified the formula numerically to at least 30 digits with mpmath (scripts py/chk.py, py/chk2.py, py/fam.py in the session scratchpad). P(s,b,n,A) = sum over k>=0 of b^(-k) sum over j=1..n of A_j/(nk+j)^s. "nz" = number of non-zero entries of A; B = log_3 |b|; "cost" = nz/B (terms per base-3 digit). Negative bases are allowed in the compendium (it uses b = -27 in formula 82), so I allow them and flag them.

## Key findings

1. **The explicit degree-1 base-3^k formulas in print are few.** Bailey's compendium section 9 has nine degree-1 formulas (67-75): log 2, sqrt(3)arctan(sqrt(3)/7), pi*sqrt(3), log 3 (twice), log 5, log 7, log 11, log 13 [READ, all CHECKED]. Adegoke's ternary paper adds alternative degree-1 forms for log 2, log 3 and pi*sqrt(3), including a base -3 formula for pi*sqrt(3) with ONE non-zero entry [READ, CHECKED]. Broadhurst's hep-th/9803091 states log 3 (his eq. 214, equal to compendium 71) and calls the weight-1 constant pi*sqrt(3) a member of his base-3 set, citing a physics reference for it [READ]. His math/9803067 is binary only; it mentions base 3 only in the abstract [READ].

2. **The compendium's general-base families (section 11, formulas 90-110; credited to Adegoke, with 103 first found by Lafont) contain far more base-3 material than the section 9 list.** Setting b = 3^m gives base-3^k degree-1 formulas for sqrt(3)*log(2+sqrt(3)) (at b = 3: base 3 itself, one term, B = 1), pi*sqrt(3), the arctangent family sqrt(3)arctan(sqrt(3)/(2b-+1)), logs of (b+-1)/b, of (b^2+-b+1)/b^2 and of (3b^2+-3b+1)/(3b^2) [READ from the rendered pages; CHECKED at b = 3 and several higher b]. The last family at b = 3 gives log(37/27) and log(19/27), so **log 19 and log 37 individually**, in base -3^9. These are the Aurifeuillian pair 3^(2m+1) +- 3^(m+1) + 1 at m = 1 [INFERRED identification]. No source I read lists log 19 or log 37 as ternary; they sit unannounced inside formula 109.

3. **Primes beyond 2, 3, 5, 7, 11, 13 reachable from the printed families at b = 3^m** (details in answer (a)): 19, 37, 31, 43, 41, 61, 73, 757, 1093, and also 271, 547 [INFERRED from printed formulas, many members CHECKED]. Every prime on your watch list (19, 31, 37, 41, 43, 61, 73, 757, 1093) is reached. The earlier Eisenstein-norm heuristic (report 02, finding 7) predicted 19, 31, 37, 41, 43, 61, 73; the printed families realize all of them and add 757 and 1093.

4. **pi*sqrt(3): cheapest in print is 1 term per base-3 digit, in three different formulas**: b = -3, n = 2, nz = 1, B = 1 (Adegoke 2.15); b = 9, n = 4, nz = 2, B = 2 (compendium 92 at b = 3); b = 3^6, n = 12, nz = 6, B = 6 (Adegoke 2.14). Compendium 69 (Broadhurst) costs 7/6; Adegoke 2.13 costs 10/6. Nothing below 1 is in print [READ, CHECKED].

5. **Cheapest logs per digit in print**: log 2 = (2/3)P(1,9,2,(1,0)), cost 1/2 (compendium 67). log 7 = (2/9)P(1,-27,6,(9,0,0,0,-1,0)) (formula 110 at b = 3, cost 2/3, base -27) beats compendium 73 (cost 5/6) [CHECKED; the compendium does not display it as a log 7 formula]. log 19 and log 37 via formula 109 cost 5/9 each.

6. **pi itself in base 3^k.** No source claims a rational-coefficient ternary formula for pi. The only negative statement is Bailey's sentence in the introduction (p. 2) attributing to Borwein-Borwein-Galway that no other degree-1 BBP-type formula for pi exists except in power-of-two bases. This overstates BBG, who treat only Machin-type (arctan(b^-m)) generators (report 02, finding 1) [READ]. MathWorld states the narrower, correct version [READ]. No source lists "pi in base 3" as an open question by name (answer (c)).

7. **Numbering trap.** Adegoke's 2011 paper cites older compendium numbers: its (2.10) is "formula (64)" and its (2.12) is "formula (67)" [READ]. In the April 2023 version they are 67 (log 2) and 70 (log 3). Compendium formulas 127 and 128 (zero relations) are proved by Adegoke's (2.17)-(2.20) [READ].

8. **A tool misreading to avoid.** A summary of MathWorld's BBP page claimed formulas for pi in bases 16, 729, 64, 4. The page text I fetched shows the base-729 equation (5) is the degree-2 pi^2 formula (compendium 76), not pi [READ]. MathWorld has no base-3 formula for pi.

## Table of formulas (degree 1, base +-3^B)

Source codes: C = Bailey compendium (April 2023 numbering); A = Adegoke arXiv:1603.04974 (equation numbers); Br = Broadhurst hep-th/9803091; O = OEIS (A165132, A154920, A164985); "C-g nnn at b=3" = my instantiation of compendium general formula nnn at b = 3.

| Source | Constant | Formula | s | b | n | A | nz | B | cost | Credit given | Checked |
|---|---|---|---|---|---|---|---|---|---|---|---|
| C 67; A 2.10 | log 2 | (2/3) P | 1 | 9 | 2 | (1,0) | 1 | 2 | 0.50 | appeared in ref [16] (compendium's reference); A derives it | CHECKED |
| C 68 (= C-g 94 at b=3) | sqrt3 arctan(sqrt3/7) | (1/6) P | 1 | 27 | 3 | (3,-1,0) | 2 | 3 | 0.67 | ref [16] | CHECKED |
| C 69 | pi sqrt3 | (1/9) P | 1 | 3^6 | 12 | (81,-54,0,-9,0,-12,-3,-2,0,-1,0,0) | 7 | 6 | 1.17 | Broadhurst | CHECKED |
| C 70; A 2.12; O A154920 | log 3 | (1/9) P | 1 | 9 | 2 | (9,1) | 2 | 2 | 1.00 | Povolotsky, simplified by Oliver Lafont | CHECKED |
| C 71; Br 214 | log 3 | (1/3^6) P | 1 | 3^6 | 6 | (729,81,81,9,9,1) | 6 | 6 | 1.00 | Broadhurst (eq. 214) | CHECKED |
| C 72; O A165132, A164985 | log 5 | (4/27) P | 1 | 3^4 | 4 | (9,3,1,0) | 3 | 4 | 0.75 | Oliver Lafont | CHECKED |
| C 73; O A165132 | log 7 | (1/3^5) P | 1 | 3^6 | 6 | (405,81,72,9,5,0) | 5 | 6 | 0.83 | Oliver Lafont | CHECKED |
| C 74; O A165132 | log 11 | (1/(2*3^9)) P | 1 | 3^10 | 10 | (85293,10935,9477,1215,648,135,117,15,13,0) | 9 | 10 | 0.90 | Oliver Lafont | CHECKED |
| C 75; O A165132 | log 13 | (1/3^5) P | 1 | 3^6 | 6 | (567,81,36,9,7,0) | 5 | 6 | 0.83 | Oliver Lafont | CHECKED |
| A 2.7 | log 2 | (1/(2*3^5)) P | 1 | 3^6 | 12 | (3^5,3^5,0,-3^4,-3^3,0,-3^2,-3^2,0,3,1,0) | 8 | 6 | 1.33 | Adegoke | CHECKED |
| A (after 2.7) | log 2 | (1/18) P | 1 | -27 | 6 | (9,9,0,-3,-1,0) | 4 | 3 | 1.33 | Adegoke (alternating) | CHECKED |
| A 2.16 | log 2 | (4/3^5) P | 1 | 3^6 | 12 | (0,81,0,0,0,9,0,0,0,1,0,0) | 3 | 6 | 0.50 | Adegoke (rewrite of 2.10) | CHECKED |
| A 2.11 | log 3 | (1/3^6) P | 1 | 3^6 | 12 | (3^6,3^5,0,-3^4,-3^4,-2*3^3,-3^3,-3^2,0,3,3,2) | 10 | 6 | 1.67 | Adegoke | CHECKED |
| A (after 2.11) | log 3 | (1/27) P | 1 | -27 | 6 | (27,9,0,-3,-3,-2) | 5 | 3 | 1.67 | Adegoke (alternating) | CHECKED |
| A 2.13 | pi sqrt3 | (1/3^4) P | 1 | 3^6 | 12 | (3^5,3^5,2*3^4,3^4,3^3,0,-3^2,-3^2,-2*3,-3,-1,0) | 10 | 6 | 1.67 | Adegoke | CHECKED |
| A 2.14 | pi sqrt3 | (2/3^4) P | 1 | 3^6 | 12 | (3^5,0,-3^4,0,3^3,0,-3^2,0,3,0,-1,0) | 6 | 6 | 1.00 | Adegoke | CHECKED |
| **A 2.15** | **pi sqrt3** | **6 P** | 1 | **-3** | 2 | **(1,0)** | **1** | **1** | **1.00** | Adegoke | CHECKED |
| C-g 92 at b=3 | pi sqrt3 | 2 P | 1 | 9 | 4 | (3,0,-1,0) | 2 | 2 | 1.00 | Adegoke | CHECKED |
| C-g 103 at b=3 | sqrt3 log(2+sqrt3) | 2 P | 1 | 3 | 2 | (1,0) | 1 | 1 | 1.00 | Adegoke [7]; 103 "first obtained" by Oliver Lafont [31] | CHECKED |
| C-g 93 at b=3 | 9 sqrt3 arctan(sqrt3/5) | (3/2) P | 1 | -27 | 3 | (3,1,0) | 2 | 3 | 0.67 | Adegoke | CHECKED |
| C-g 97 at b=3 | 27 sqrt3 sqrt2 arctan(sqrt6/2) | 2 P | 1 | 81 | 8 | (27,0,9,0,-3,0,-1,0) | 4 | 4 | 1.00 | Adegoke | CHECKED |
| C-g 98 at b=3 | 9*3^5 sqrt3 arctan(1/(5 sqrt3)) | (1/2) P | 1 | -3^9 | 6 | (729,243,54,9,1,0) | 5 | 9 | 0.56 | Adegoke | CHECKED |
| C-g 99 at b=3 | 9*3^5 sqrt3 arctan(1/(7 sqrt3)) | (1/2) P | 1 | -3^9 | 6 | (729,-243,54,-9,1,0) | 5 | 9 | 0.56 | Adegoke | CHECKED |
| C-g 100 at b=3 | 9 sqrt3 arctan(sqrt3/2) | P | 1 | -27 | 6 | (9,0,6,0,1,0) | 3 | 3 | 1.00 | Adegoke | CHECKED |
| C-g 101 at b=3 | log(4/3) | (1/9) P | 1 | 9 | 2 | (3,-1) | 2 | 2 | 1.00 | Adegoke | CHECKED |
| C-g 102 at b=3 | log(2/3) | -(1/9) P | 1 | 9 | 2 | (3,1) | 2 | 2 | 1.00 | Adegoke | CHECKED |
| C-g 104 at b=3 | log(13/9) | (1/27) P | 1 | 27 | 3 | (9,3,-2) | 3 | 3 | 1.00 | Adegoke | CHECKED |
| C-g 105 at b=3 | log(7/9) | -(1/27) P | 1 | -27 | 3 | (9,-3,-2) | 3 | 3 | 1.00 | Adegoke | CHECKED |
| C-g 90 at b=3 | 9 log(13/4) | 3 P | 1 | 27 | 3 | (3,1,0) | 2 | 3 | 0.67 | ref [16] | CHECKED |
| C-g 109(+) at b=3 | log(37/27) | (1/3^9) P | 1 | -3^9 | 6 | (6561,-729,0,27,-9,2) | 5 | 9 | 0.56 | Adegoke | CHECKED |
| C-g 109(-) at b=3 | log(19/27) | -(1/3^9) P | 1 | -3^9 | 6 | (6561,729,0,-27,-9,-2) | 5 | 9 | 0.56 | Adegoke | CHECKED |
| C-g 110 at b=3 | 9 log 7 | 2 P | 1 | -27 | 6 | (9,0,0,0,-1,0) | 2 | 3 | 0.67 | Adegoke | CHECKED |
| C-g 108 at b=3 | (3 sqrt3/sqrt2) log((4+sqrt6)/(4-sqrt6)) | 2 P | 1 | -9 | 4 | (3,0,-1,0) | 2 | 2 | 1.00 | Adegoke | not checked |

Notes on the table.
- Rows "C-g nnn at b=3" are my instantiations of the printed general formulas at b = 3 [INFERRED substitution; the numeric check [CHECKED] confirms each instantiated identity]. The compendium does not print them as base-3 formulas.
- C-g 92 as printed: sqrt(b) arctan(1/sqrt(b)) = (1/b) P(1,b^2,4,(b,0,-1,0)). At b = 3 this is pi*sqrt(3)/6 = (1/3) P(1,9,4,(3,0,-1,0)).
- Printed family members that are NOT in a power-of-3 base for any b = 3^m: 95, 96 (base 16 b^8), 106, 107 (base -+4 b^4) [READ].
- Any b = 3^m gives a formula in base 3^(m r) for the printed base b^r.
- Degree >= 2 ternary formulas (compendium 76-83, Adegoke sections 3-6, Broadhurst 17, 204, 212, 213, 215) are not degree 1 and are not listed.
- Adegoke-Layeni arXiv:1603.08540 eq. (4.4) gives a rapidly convergent pi*sqrt(3) series that its own authors say is not technically a BBP-type formula [READ].

## Answers

### (a) Primes with a base-3^k degree-1 formula for log p

Stated individually in print [READ, CHECKED]: **2, 3, 5, 7, 11, 13** only (compendium 67, 70-75; OEIS A165132, comment by Lafont, 2009). The OEIS entry gives no criterion or completeness claim.

Reachable from the compendium's own printed general families at b = 3^m, where the argument contains a single prime beyond 2, 3, 5, 7, 11, 13 (or is combined with log 7) [INFERRED from printed formulas; identities for the starred members CHECKED]:

| p | family, b | argument | base | note |
|---|---|---|---|---|
| 19 | 109(-), b = 3 | 19/27 | -3^9 | single prime, starred |
| 37 | 109(+), b = 3 | 37/27 | -3^9 | single prime, starred |
| 31 | 109(-), b = 9 | 217/243 = 7*31/3^5 | -3^13 | with log 7, starred |
| 43 | 109(-), b = 27 | 2107/2187 = 7^2*43/3^7 | -3^19 | with log 7, starred |
| 73 | 105, b = 9 | 73/81 | -3^6 | single prime (formula checked at b = 3; same family) |
| 41 | 101, b = 81 | 82/81 = 2*41/3^4 | 3^8 | starred |
| 61 | 101, b = 243 | 244/243 = 4*61/3^5 | 3^10 | starred |
| 757 | 104, b = 27 | 757/729 | 3^9 (n = 3, A = (729,27,-2), prefactor 1/27^3) | single prime, starred |
| 1093 | 102, b = 3^7 | 2186/2187 = 2*1093/3^7 | 3^14 | starred |
| 271 | 109(+), b = 9 | 271/243 | -3^13 | extra |
| 547 | 101, b = 3^7 | 2188/2187 = 4*547/3^7 | 3^14 | extra |

Checked members: 109(-) at b = 3, 9, 27; 109(+) at b = 3; 104 at b = 3 and 27; 105 at b = 3; 102 at b = 3 and 3^7; 101 at b = 3, 81 and 243; plus 90, 110 at b = 3. The rest follow by substituting b into the printed vectors.

Not reached by a single-prime member of families 101, 102, 104, 105, 109(+-), 90 for b = 3^m with m <= 12: 17, 23, 29, 47, 53, 59, 67, 71, 79, 83, 89, 97 [COMPUTED by py/fam.py; combinations of several members were not searched]. This agrees with the earlier Eisenstein-norm test (report 02, finding 7).

No source I read mentions 19, 31, 37, 41, 43, 61, 73, 757 or 1093 in a ternary context. The only completeness remark is in the compendium (p. 6, binary case: the list of primes with binary log formulas is certainly not complete); there is no base-3 analogue [READ].

### (b) pi*sqrt(3): every formula found

| Source | b | n | nz | B | cost (nz/B) | note |
|---|---|---|---|---|---|---|
| Adegoke 2.15 | -3 | 2 | 1 | 1 | **1.00** | pi sqrt3 = 6 P(1,-3,2,(1,0)); the arctan(1/sqrt3) series; negative base |
| Compendium 92 at b = 3 | 9 | 4 | 2 | 2 | **1.00** | positive base; pi sqrt3 = 2 P(1,9,4,(3,0,-1,0)) |
| Adegoke 2.14 | 3^6 | 12 | 6 | 6 | **1.00** | odd positions only; (2/81) P(1,729,12,(243,0,-81,0,27,0,-9,0,3,0,-1,0)) |
| Compendium 69 (Broadhurst) | 3^6 | 12 | 7 | 6 | 1.17 | |
| Adegoke 2.13 | 3^6 | 12 | 10 | 6 | 1.67 | |

Cheapest known: **1 non-zero entry per base-3 digit**, attained by three formulas. The positive-base ones are compendium 92 (b = 9) and Adegoke 2.14 (b = 3^6); Adegoke 2.15 reaches the same rate with the smallest data (b = -3, one entry). I found nothing in print below 1 for pi*sqrt(3). Broadhurst states that the weight-1 constant pi*sqrt(3) is in his base-3 set, citing a physics reference (his ref [37]) that I did not open [READ, text after eq. 214].

### (c) A formula for pi itself in a base that is a power of 3

- Not claimed anywhere I read.
- Stated not to exist: compendium p. 2 (introduction, paragraph after formula (3)) says the 2004 Borwein-Galway-Borwein paper showed there is no other degree-1 BBP-type formula for pi besides those in power-of-two bases [READ]. This overstates BBG, who prove it only inside the Machin-type class (report 02, finding 1). MathWorld "BBP-Type Formula" gives the narrower version (no non-binary Machin-type BBP arctangent formula for pi) and adds that it does not rule out a different scheme [READ].
- Open question: none stated in the sources opened this pass. The nearest are BBG's problem list and Zudilin arXiv:2409.10097 (base 5, not periodic) [from report 02].
- Context: the compendium notes that pi^2 has both a base-2 formula (29) and a base-3 formula (76) (p. 2) [READ]. Ternary formulas for pi in print involve pi*sqrt(3) only (Adegoke section 2.3 is titled for pi*sqrt3).

### (d) log(2+sqrt3) and sqrt3 log(2+sqrt3) as base-3 BBP values

- **sqrt(3) log(2+sqrt(3)) = 2 P(1,3,2,(1,0)) = 2 sum over k>=0 of 1/(3^k (2k+1))**: base 3 itself, one term per digit. It is compendium formula 103 at b = 3 (sqrt(b) log((sqrt(b)+1)/(sqrt(b)-1)) = 2 P(1,b,2,(1,0))); the compendium credits formulas 92-110 to Adegoke and says 103 was first obtained by Lafont [READ, CHECKED]. The compendium does not single out b = 3.
- log(2+sqrt3) alone: no statement found. It would need the irrational factor sqrt(3) in front, so it is outside the rational-coefficient class [INFERRED].
- A binary formula for sqrt3 log(2+sqrt3) (bases 2^(12p)) is treated in arXiv:1603.07395 [SNIPPET].
- Also at b = 3: formula 108 gives an algebraic-coefficient logarithm in base -9 (last row of the table, not checked).

## What could not be opened or verified

- Adegoke's NYJM 2010 trilogarithm paper and the 2011 "symbolic routes" paper: not opened (degree >= 3 or general; the ternary degree-1 content is in 1603.04974 and the general families in 1603.08209 and the compendium).
- Compendium references [16], [28], [31] (credit chain for 67, 68, 70, 103): read as citations only.
- Broadhurst's reference [37] for pi*sqrt(3). In hep-th/9803091 I did not find a displayed formula for pi*sqrt(3); the glyph is lost in text extraction and I read it from the rendered page as sqrt(3) pi.
- math/9803067: full text searched for ternary and BBP terms (none beyond the abstract).
- Plouffe's pages: not reached.
- The prime table in (a) rests on printed general formulas; I checked 20-odd members numerically, not every one.
- The cost column counts non-zero entries only and ignores prefactors and numerator sizes.
- Wikipedia was not refetched (covered in report 02).

## Search log

WebSearch: 4 of 30 used.
1. ternary BBP-type formula base 3 logarithm of prime (Lafont) log 13 log 11 digit extraction
2. BBP-type formula pi sqrt(3) base 3 ternary digit extraction arctan(1/sqrt(3))
3. "BBP" "log(2+sqrt(3))" base 3 formula digit extraction
4. BBP formula pi in base 3 impossible OR open "base 3" pi digit extraction ternary digits of pi

Fetched: arXiv PDFs 1603.04974, math/9803067, hep-th/9803091, 1603.08209, 1603.08540, 1603.07395 (pdftotext plus rendered key pages); the compendium PDF (full text, pages 26-28 rendered); OEIS JSON for A165132, A154920, A164985; arXiv API query au:Adegoke AND all:BBP (7 entries, only 1603.04974 is ternary); MathWorld BBP-Type Formula (twice). An OEIS full-text search for ternary BBP returned empty.

## Sources (opened)

- [Bailey, A Compendium of BBP-Type Formulas](https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf)
- [Adegoke, ternary BBP-type formulas for polylogarithm constants, arXiv:1603.04974](https://arxiv.org/pdf/1603.04974)
- [Adegoke, A non-PSLQ route to BBP-type formulas, arXiv:1603.08209](https://arxiv.org/pdf/1603.08209)
- [Adegoke and Layeni, higher derivatives of arctan, arXiv:1603.08540](https://arxiv.org/pdf/1603.08540)
- [Adegoke, Oliver Lafont, Layeni, general binary bases, arXiv:1603.07395](https://arxiv.org/pdf/1603.07395)
- [Broadhurst, Polylogarithmic ladders, arXiv:math/9803067](https://arxiv.org/pdf/math/9803067)
- [Broadhurst, Massive 3-loop Feynman diagrams, arXiv:hep-th/9803091](https://arxiv.org/pdf/hep-th/9803091)
- [OEIS A165132 (JSON)](https://oeis.org/search?q=id:A165132&fmt=json)
- [OEIS A154920 (JSON)](https://oeis.org/search?q=id:A154920&fmt=json)
- [OEIS A164985 (JSON)](https://oeis.org/search?q=id:A164985&fmt=json)
- [arXiv API, author Adegoke and BBP](http://export.arxiv.org/api/query?search_query=au:Adegoke+AND+all:BBP&max_results=50)
- [MathWorld, BBP-Type Formula](https://mathworld.wolfram.com/BBP-TypeFormula.html)
