# Base-5 BBP-type formulas of degree 1: literature inventory (2026-11-22)

Tags: [READ] = read in the source text itself (PDF text extracted locally, or page body fetched);
[SNIPPET] = only a search snippet or abstract; [INFERRED] = my own deduction.
Notation: P(s,b,n,A) = sum_{k>=0} b^-k sum_{j=1..n} A_j/(nk+j) (Bailey).

## 0. Method and limits
- Read in full or large part: Bailey's compendium (davidhbailey.com PDF; the edition with formulas up to about 120), Zudilin 2409.10097 (whole paper, 3 pages), Borwein-Borwein-Galway 2004 (PDF text), Kristensen-Mathiasen 2208.07696 (PDF text), Adegoke arXiv 1603.06307 (Section 5 text), Lafont's OEIS wiki "Zero relations" page, MathWorld BBP-Type Formula page.
- NOT read in full: Chamberland (only the HTML abstract page). Lafont's 2011 manuscript "Degree 1 BBP-Type Zero Relations" (only cited by Bailey). OEIS: no direct hit for a base-5 BBP entry; I did not open individual OEIS entries (A104885 etc. only appeared as search results).
- Bailey's PDF extraction garbles the formulas in Section 10; entries say where I reconstructed.

## 1. Inventory of base 5 / 25 / 125 / 5^5 degree-1 formulas in print

### 1a. Bailey compendium, Section 10 "Other specific bases" (85, 86 credited to Lafont; 87-89 said to appear in his ref [16])  [READ, partly garbled]
Source: https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf
- (85) a log of a rational, P(1, 25, 2, (1, 0)). [READ the P-form; constant garbled] Direct computation: sum 25^-k/(2k+1) = 5*artanh(1/5) = (5/2) log(3/2), so I take (85) to be (5/2) log(3/2) [INFERRED]. Base 25, n = 2.
- (86) sqrt(5) log(phi) = P(1, 5, 2, (1, 0)), phi the golden mean. [READ] Base 5, n = 2. Check: sum 5^-k/(2k+1) = sqrt5 artanh(1/sqrt5) = sqrt5 log phi [INFERRED].
- (87) a log of an expression in sqrt5 (visible: 781, 256, 57 - 55*sqrt5) = P(1, 5^5, 5, (0, 5, 1, 0, 0)). [READ P-form; left side garbled] Base 3125, n = 5.
- (88) a sum of two arctans with 5^(1/4) and sqrt5 in the arguments = a multiple of P(1, 5^5, 5, (125, -25, 5, -1, 0)). [READ P-form; arguments garbled] Base 3125, n = 5.
- Same section, not base 5 but same family: (84) log of a rational at base 10, n = 1; (89) a log at base 10^10, n = 10.
- None of (85)-(88) is a single log p, and none involves pi. [READ/INFERRED as stated]

### 1b. Bailey compendium, Section 11 "General bases"  [READ, garbled]
- Families in a free integer parameter b (log families with P(1,b,2,(1,0)), P(1,b^3,3,(b^2,b,-2)), arctan families with P(1,b^2,4,(b,0,-1,0)), P(1,b^2,2,(b,-1)), ...). The family containing 85/86 is the b-family with P(1,b,2,(1,0)).
- Setting b = 5 or b = 5^m gives base 5 (or 25, 125, ...) formulas. I did NOT verify specific instances, signs or constants; the extraction is too garbled. Instances are [INFERRED]; re-derive before use.
- Bailey Sect. 3 says non-binary-base arctangent formulas for certain rationals come from variants of his formulas 11 and 12. [READ]

### 1c. Adegoke, Sect. 5.2 "Base 5 BBP-type formulas", "The golden ratio, Fibonacci numbers and BBP-type formulas", arXiv 1603.06307  [READ]
Source: https://arxiv.org/pdf/1603.06307
- sqrt5 * arctan(1/sqrt5) = (1/5) P(1, 25, 4, (5, 0, -1, 0)) (5.18). Base 25, n = 4.
- sqrt5 * arctan(1/sqrt(5^3)) = (1/5^4) P(1, 5^6, 4, (5^3, 0, -1, 0)) (5.19). Base 15625.
- Consequences (5.20)-(5.22): sqrt5*(arctan(1/2)+arctan(1/4)) as a length-12 series at base 5^6; sqrt5*(arctan(1/2)+arctan(1/6)) = (1/5) P(1,25,4,(5,0,-1,0)); sqrt5*(arctan(1/4)-arctan(1/6)) = (1/5^4) P(1,5^6,4,(5^3,0,-1,0)). [READ; sqrt5 prefactors partly lost in extraction, reconstructed from (5.15)-(5.17)]
- Constants: sqrt5 times arctans of rationals. Not pi.
- His 5.1 and 5.3 are binary and base-phi material (see 1f).

### 1d. Adegoke 2016 (arXiv 1603.04561; Fibonacci Quarterly 52(4) 2014)  [SNIPPET]
Source: https://arxiv.org/pdf/1603.04561
- Abstract: before this, only a base-5 BBP-type formula was known for sqrt5*log(phi); this paper adds a binary one. The search summary ties the earlier one to Formula 83 of the April 2013 compendium (numbering differs from the edition I read, where it is 86). [SNIPPET]

### 1e. Chamberland, JIS 6 (2003) 03.3.7  [SNIPPET / abstract page only]
Source: https://cs.uwaterloo.ca/journals/JIS/VOL6/Chamberland/chamberland60.html
- Class defined for any base b, but results are binary (Gaussian-Mersenne and generalized Gaussian-Mersenne primes, Aurifeuillian factorizations). No base 5 content found. Full text not read.

### 1f. Golden-ratio base (SEPARATE: base phi, not base 5)
- Adegoke-Lafont arXiv 2303.13374; Adegoke 1603.06307 Sect. 5.3; Cloitre's phi-base pi^2 formula (MathWorld eq. 34). Adegoke notes these are expansions in a non-integer base and give no digit extraction [READ for 1603.06307; READ for MathWorld; SNIPPET for 2303.13374].

### 1g. MathWorld "BBP-Type Formula"  [READ]
Source: https://mathworld.wolfram.com/BBP-TypeFormula.html
- No base 5 content. Lists bases 16, 64, 729 (pi, ln 3), 10 (ln(9/10)), negative bases, phi.

### 1h. OEIS  [not found]
- Two searches (BBP with base 5; sqrt5 log phi) returned no OEIS entry for a base-5 BBP series. Weak evidence of absence only. Lafont's zero-relations wiki page was read (section 3).

## 2. Pi in base 5

### 2a. Zudilin, arXiv:2409.10097v2, "A BBP-style computation for pi in base 5" (3 pp.)  [READ, whole paper]
URL: https://arxiv.org/abs/2409.10097 ; pdf https://arxiv.org/pdf/2409.10097
- Abstract calls it a joke. Starting point: the Salikhov / Zeilberger-Zudilin identity (1) relating sum_n (1/(2n+1)) (1/(1-2i))^(2n+1) and its conjugate-type partner to pi. So pi = Im of 8 * sum_{n>=0} (1/(2n+1)) (1/(1-2i))^(2n+1). [READ; scalar constants garbled in extraction, structure clear]
- "Base 5" because |1-2i|^2 = 5: terms decay like 5^(-n). The series lives in Q[i]. He also gives a real form sum b_n/((2n+1) 5^(2n)) with b_n = -6 b_(n-1) - 25 b_(n-2), |b_n| < 2*5^n. [READ]
- Is it of the form sum rho(k) 5^-floor(k/2)/k with rational periodic rho? No. [INFERRED from READ text] The numerators (real and imaginary parts of powers of 1-2i) follow a linear recurrence with roots of modulus sqrt5 and non-root-of-unity argument, so they are neither periodic nor rational-constant; coefficients are Gaussian integers.
- Algorithm: compute 8*5^d/(2n+1) * (1-2i)^-(2n+1) mod Z[i] by fast exponentiation, assuming log(2d+4r-1)/log 5 <= d, with 2n+1 = 5^k m. [READ]
- What he says is wrong/open [READ]: Sect. 3 "An obvious flaw": the modular identity (3) is false when 2n+1 > d-k (the left side has denominator 5^(2n+1-d+k) m, the right only m); shortening the sum is no fix since the tail cannot be bounded then. So the method fails as stated. He asks for more suitable formulae for pi or other constants over quadratic or higher algebraic extensions. In Sect. 2 he says it is an open question whether this kind of computation is possible for pi in bases other than powers-of-2 bases. He proves no impossibility.
- Net: no working base-5 digit-extraction formula for pi, and no nonexistence statement. [READ]

### 2b. Kristensen-Mathiasen, arXiv:2208.07696  [READ text + abstract]
URL: https://arxiv.org/abs/2208.07696 ; pdf https://arxiv.org/pdf/2208.07696
- Sage search method; a new formula for pi*sqrt3; irrational (Pisot) bases with integer coefficients, e.g. pi in base 1+sqrt3. [READ]
- Integer bases computed: powers of 2 and of 3 only (Table 1: 2^4, 2^6, 2^12, 2^20, 3^6). No base 5. [READ]
- No nonexistence theorem for other bases. Open problems they list: why the golden ratio gives so many zero formulas; digit extraction from irrational-base formulas; degree above 1. [READ]

### 2c. Borwein-Borwein-Galway, Canad. J. Math. 56 (2004) 897-925, DOI 10.4153/CJM-2004-041-2  [READ, PDF text]
URL: https://www.cambridge.org/core/services/aop-cambridge-core/content/view/BB7919C8E1AE66878AE8D7BC7F0EBFA3/S0008414X0003385Xa.pdf/finding-and-excluding-b-ary-machin-type-individual-digit-formulae.pdf
- Their "Machin-type BBP" class is narrow: arctan formulas with generators arctan(b^-m) (for b = 2 also arctan(1/(1-2^m))), and log analogues with ln(1-b^-m); rational coefficients. [READ]
- Theorem 7 [READ]: for b > 2 not a proper power there is no Q-linear b-ary Machin-type BBP arctangent formula for pi. (The abstract lost a symbol in extraction; the theorem and Bang-theorem proof are clear.) So only base 2 (and its powers) works in that class.
- Theorem 1 and Example 1 [READ]: arctan(1/2) has no Z-linear b-ary Machin-type formula whenever 5 divides b; arctan(1/5) is excluded when 13 divides b. Relevant to base 5.
- Theorems 4 and 6 [READ]: Bang's theorem excludes Machin-type formulas for ln p when primitive prime factors cannot cancel; the worked examples are binary (ln 23, 89, 113).
- Caveat [READ]: abstract says that when no Machin-type formula exists, no BBP formula of any form is known for that constant. MathWorld's summary of the result says it does not rule out other digit-extraction schemes in other bases [READ].
- Their research-problems appendix is about binary zero relations; nothing on base 5. [READ]
- Our class (periodic rho with weight 5^-floor(k/2), i.e. sqrt5-type arguments as in 85, 86 and Adegoke 5.18) is strictly wider than Machin-type (arguments only b^-m), so Theorem 7 does not exclude pi in our class. [INFERRED]

## 3. Zero relations in base 5
- None found in print. Lafont's OEIS wiki page lists five zero relations (moduli 4, 6, 6, 8, 2); none is base 5 or a power of 5; no remark on base 5. [READ] https://oeis.org/wiki/User:Jaume_Oliver_Lafont/Zero_relations
- Bailey cites Lafont's manuscript "Degree 1 BBP-Type Zero Relations" (27 Jan 2011) and an OEIS-wiki derivation for binary zero relations (bases 2^12, 2^20). [READ citation only; manuscript not opened]
- Kristensen-Mathiasen Table 1 lists null formulas only for integer bases 2^4, 2^6, 2^12, 2^20, 3^6. [READ] A search snippet also mentioned a base-12 zero relation for sqrt3+1 [SNIPPET, unverified]. No base 5.
- No statement of nonexistence of base-5 zero relations was found. That absence overall is [INFERRED] from the sources I opened.

## 4. Primes p with log p expressible by a base-5 (or 25) formula
- No source found that states a single log p has a base-5/25 formula. [absence in opened sources]
- In print: log(3/2) (times 5/2) at base 25 (Lafont, Bailey 85), and sqrt5*log(phi) at base 5 (not a log of a rational). The first involves only primes 2 and 3 jointly. [READ/INFERRED]
- The b-general families (1b) at b = 5 plausibly give logs of rationals involving primes 2, 3, 5, 31 (5^3 - 1 = 4*31), unverified. [INFERRED]
- Facts for the Machin-type sublattice in base 5 (generators ln(1-5^-m)): 5-1 = 4; 5^2-1 = 24 = 8*3; 5^3-1 = 124 = 4*31; 5^4-1 = 624 = 16*3*13. From m=1,2: log(5/4) = 2log2 - log5 and log(25/24) combine to give log(3/2), matching (85). Whether log 2, log 3 or log 5 alone lies in this lattice was not worked out. [INFERRED, unchecked]
- Binary analogues are classified (Chamberland, BBG); I found no base-5 classification.

## Confidence summary
1. Explicit list = Bailey (85)-(88), the b-families, Adegoke (5.18)-(5.22): existence solid, constants of 85, 87, 88 reconstructed/garbled; list probably incomplete.
2. No base-5 pi formula of the periodic rational type in print; Zudilin's is over Z[i] and flawed by his own account; BBG exclude pi only for Machin-type, b > 2. Solid.
3. No base-5 zero relation found: medium (absence of evidence).
4. No single log p known in print for base 5: medium.
