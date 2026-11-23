# Claims in print: BBP-type formulas for pi in non-binary bases, and pi*sqrt(3) in base 3

Date of lookup: 2026-11-22. Tags: [READ] read in the source text itself; [SNIPPET] abstract or search snippet only; [INFERRED] my own deduction or hand arithmetic.
Method note: PDFs were saved and converted with pdftotext. Symbols such as pi, sqrt and Greek letters were dropped by the conversion in several places; I say so where it matters.

## 0. Bottom line

- No source found claims a degree-1, rational-coefficient, integer-base BBP formula for pi itself in any base that is not a power of 2. [READ for Bailey, Kristensen-Mathiasen; SNIPPET for Borwein-Borwein-Galway]
- The proved impossibility is only for the Machin-type arctangent class (Borwein, Borwein, Galway 2004). Bailey's compendium states it more broadly (see 2). Nobody proves nonexistence for all degree-1 formulas.
- Non-binary formulas "for pi" that do exist in print: Kristensen-Mathiasen's formulas in irrational Pisot bases (1+sqrt 3, golden ratio) with rational/integer coefficients. Zudilin's base-5 note is a different, non-BBP-class construction.
- The displayed base-729 identity for pi*sqrt(3) is in print in an equivalent form: it equals Bailey's Formula 69 plus a multiple of Bailey's Relation 131 (see 2.4). The exact vector is not printed.

## 1. Kristensen and Mathiasen, arXiv:2208.07696

URL: https://arxiv.org/abs/2208.07696 (PDF https://arxiv.org/pdf/2208.07696). Read the full PDF (v1, 16 Aug 2022, 12 pages) [READ].

- Actual title: "BBP-type formulas -- an elementary approach". Authors S. Kristensen, O. Mathiasen (Aarhus). The title in your brief is wrong. I did not check whether a journal version exists.
- Definition 1 uses BBP(d,b,n,A) = sum_k b^(-k) sum_j a_j/(kn+j)^d, with A real; they print only integer-coefficient results. [READ]
- Theorem 1: for theta = (a/b)*2*pi (a rational, b even) and r in (0,1), arg(1 + r e^(i theta)) = BBP(1, 1/r^b, b, A) with a_j = r^j (-1)^(j+1) sin(j theta). The formulas are for the argument of a triangle angle; pi comes out only when the angles are rational multiples of pi. The example is the Ferguson-Bailey-Arno pi/4 formula in base 16. [READ]
- The method finds null (zero) formulas by LLL and checks them in exact algebraic arithmetic. Integer bases covered are 2^4, 2^6, 2^12, 2^20, 3^6 (Table 1). In base 3^6 (r = 1/3, b = 12) they recover one known zero formula, Adegoke's. [READ] (Table 1 is partly garbled by extraction; I trust the text near it.)
- Base-729 zero relation printed: 0 = BBP(1, 729, 12, (243, -243, -324, -81, 27, 0, -9, 9, 12, 3, -1, 0)), credited to Adegoke [1] (NYJM 2010). [READ]
- A new formula "for [symbol lost]3" in base 2^12 with b = 24, the proof being a combination of two CTB24 vectors (r = 1/sqrt2, angles 5 and 11). The left side lost its symbols in extraction, so I cannot say whether it is pi*sqrt(3) or something else. [READ, but garbled]
- Pisot bases: formulas with rational/integer coefficients in irrational bases. The abstract says a formula for pi in base 1 + sqrt3 was found. The text has pi = 12 * BBP(1, 12, 12, CTB12(-1, 2)) in that base, and a golden-ratio-base formula pi = 10 * BBP(1, 15, 15, CTB(...)) (base symbol and argument lost in extraction). The value is pi itself (times an integer), the coefficients rational, the base irrational. [READ, partly garbled]
- They say the Pisot-base formulas are not beta-expansions, and that extracting digits from them is an open problem. They say formulas in non-integer bases were not found in the literature, except Adegoke's golden-ratio formulas, which have coefficients in Z[phi]. [READ]
- Nothing about base 5 or base 10. Nothing claiming a pi formula in base 3^m. [READ]

## 2. Bailey, "A compendium of BBP-type formulas"

URL: https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf (copy read: 1887-line text conversion, the version with 131 relations; a 2004 version also exists at https://corpora.tika.apache.org/base/docs/govdocs1/656/656518.pdf, not read).

### 2.1 Statement about pi

- Introduction: a 2004 paper of Borwein, Galway and Borwein showed there are no other degree-1 BBP-type formulas for pi except those whose base is a power of two (Formulas 1-3). It adds that for pi^2 there is both a base-2 and a base-3 formula (Formulas 29, 76). [READ, paraphrase] Note that this is a stronger wording than the BBG abstract (see 3.1).
- Nothing in the ternary section or elsewhere gives a pi formula in base 3 or 10. [READ]

### 2.2 Ternary section (9)

"No ternary BBP formulas were presented in [14], but several have been discovered." Listed (P(s,b,n,A) normalization) [READ]:
- 67: log 2 = (2/3) P(1,9,2,(1,0))
- 68: 3 arctan(sqrt3)... (symbols lost) = (1/6) P(1,27,3,(3,-1,0))? Left side garbled; I read it as arctan(1/sqrt 3)-type, so treat as unverified.
- 69: [left side lost: symbol sqrt/pi dropped, reads "3 ="] = (1/9) P(1,3^6,12,(81,-54,0,-9,0,-12,-3,-2,0,-1,0,0)). Credited to Broadhurst [19].
- 70: log 3 = (1/9) P(1,9,2,(9,1)); 71: log 3 base 3^6; 72-75: log 5, 7, 11, 13 (Oliver i Lafont).
- 76: pi^2 = (2/27) P(2,3^6,12,...); 77: log^2 3; 78: 3 pi... (pi*sqrt3*log 3-type, symbols lost); 79-83: Adegoke higher-degree.
- Other bases for pi*sqrt3: Mathworld's page lists a base-64 formula (SNIPPET); I did not find it in the compendium's text.

Is Formula 69's left side pi*sqrt3? The extraction lost the symbols. [INFERRED] By hand, (1/9)*P(...) = 9 - 6/2 - 1/4 - (4/3)/6 - (1/3)/7 - (2/9)/8 - (1/9)/10 + (tail of k>=1, small) gives about 5.4413, matching pi*sqrt3 = 5.4414. So I infer 69 is pi*sqrt3 (hand sum, not machine-checked). Please verify against the PDF image.

### 2.3 Zero relations in base 729 (Relations 130, 131)

The last two relations in the list, lines near the end, are:
- 0 = P(1,729,12,(0,81,-162,0,27,36,0,9,6,4,-1,0))   [Relation 130]
- 0 = P(1,729,12,(243,-324,-162,-81,0,-36,-9,0,6,-1,0,0))   [Relation 131]
Numbers 130/131 come from the attribution sentence ("130 and 131 were found experimentally by the author"). [READ] I did not machine-verify these two vectors.
These are the only base-3^m zero relations in the compendium that I found in the text. Relation 126 is credited as the difference of Formulas 40 and 48 (binary), not ternary. Adegoke's own ternary zero relations (see 4) are not printed as numbered compendium items in what I read.

### 2.4 Your identity versus the compendium (hand algebra, [INFERRED])

Your series in P(1,729,12,.) normalization: a_j = rho(j) * 3^(-floor(j/2)) with rho = (0,18,18,18,0,0,0,-18,-18,-18,0,0), giving
U = (0, 6, 6, 2, 0, 0, 0, -2/9, -2/9, -2/27, 0, 0), value claimed pi*sqrt3. This agrees term by term with your displayed series (3/(6j+1) = 6/(12j+2), etc.).
Caution: the vector "(0,81,54,27,0,0,0,-3,-2,-1,0,0)" in your brief is NOT proportional to U (U scaled by 27 is (0,162,162,54,0,0,0,-6,-6,-2,0,0)). Use U or the rho form.
Then U - (1/9)*(Formula 69 vector) = -(1/27) * (Relation 131 vector), exactly (I checked each of the 12 coordinates). So your identity is Formula 69 plus -(1/27) times Relation 131. Equivalent in print, provided 69's left side is pi*sqrt3 and 131 is correct.

## 3. Impossibility statements and open questions

### 3.1 Borwein, Borwein, Galway, "Finding and excluding b-ary Machin-type individual digit formulae", Canad. J. Math. 56 (2004) 897-925
URL: https://cambridge.org/core/journals/canadian-journal-of-mathematics/article/finding-and-excluding-bary-machintype-individual-digit-formulae/BB7919C8E1AE66878AE8D7BC7F0EBFA3 [SNIPPET: abstract only, not the full text]
- Class: "Machin-type BBP formulae", i.e. K = sum over arctangents of rational numbers (an arctangent-combination formula). Result: pi has none for b != 2 (b not a power of 2). Tools: factoring in Z[i] and Z. The class is formally restricted, so this is not a nonexistence proof for general degree-1 formulas. Note arctangent-combination formulas have a form (Gaussian rational) that matches the ones in your class only partly; whether every degree-1 rational formula for pi falls into the class is not something I verified. [INFERRED]
- MathWorld repeats this and adds that it "does not rule out a completely different scheme" in other bases. URL: https://mathworld.wolfram.com/BBP-TypeFormula.html [READ via fetch summary]. MathWorld also lists a golden-ratio-base pi^2 formula (Cloitre) and no base-3 pi*sqrt3 formula (the page's pi*sqrt3 formula is base 64) [READ via fetch summary, not original page text].

### 3.2 Zudilin, arXiv:2409.10097
URL: https://arxiv.org/abs/2409.10097 (v1 title "...in base 10", later "...in base 5"); HTML https://arxiv.org/html/2409.10097v2 [READ via fetch summary of the HTML, not the PDF].
- States BBP-type formulae for pi are known for power-of-2 bases and calls other bases an open question. Gives a "base 5" digit-extraction idea from 5-adic structure (norm of 1+-2i is 5), identity sum b_n/((2n+1)5^(2n)) = 5pi/16 with a second-order integer recurrence b_n. This is not a degree-1 rational-periodic BBP series with integer base. The page itself notes a flaw in one equation (3) and conditions on the digit window. [SNIPPET-level; the summary came from a fetch tool, not my own reading of the formulas.]

### 3.3 Others
- Wikipedia BBP article: BBP formulas need integer base; says many new formulas use bases that are powers of 2 or 3; says nothing about nonexistence for pi in base 3. URL: https://en.wikipedia.org/wiki/Bailey%E2%80%93Borwein%E2%80%93Plouffe_formula [READ via fetch summary].
- Plouffe 2022 decimal digits: not BBP-type (requires the earlier digits), per Wikipedia. [READ via summary]
- Bailey-Borwein "Mathematics by Experiment" section on base-10 degree-1 formulas: NOT found. Search returned only the citation in Bailey 2006. Unverified. Bailey-Crandall 2001: not looked up.
- Broadhurst arXiv:math/9803067: abstract says massive diagrams entail constants with base b = 3 (via hep-th/9803091). No pi*sqrt3 formula in the abstract. Full text not read. [SNIPPET] Bailey credits Formulas 69, 76-78 to Broadhurst [19].
- MathOverflow / Math StackExchange questions on pi in base 10 or 3: search returned none. A MetaFilter thread appeared (https://ask.metafilter.com/360896/Math-formula-that-only-works-in-some-base-systems), which repeats the BBG statement as "level 1 formulas only in powers of 2" [SNIPPET]. Nobody found who "conjectures" nonexistence beyond the compendium's wording.

## 4. Adegoke and ternary zero relations

- arXiv:1603.04974 (Adegoke, "A novel approach to ... " title partly unclear; NYJM 16 (2010) 361-367 is "New binary and ternary digit extraction (BBP-type) formulas for trilogarithm constants", per Kristensen-Mathiasen's reference list). URL read: https://arxiv.org/pdf/1603.04974 [READ, partly garbled: pi and sqrt symbols lost, numerals and denominators intact].
- Section 2.3 "Ternary formulas for [pi*sqrt3]" (the heading symbol is lost, the Greek characters read as "3"): (2.13) base 3^6, n = 12, coefficient numerators (3^5, 3^5, 2*3^4, 3^4, 3^3, 0, -3^2, -3^2, -2*3, -3, -1, 0) on 1/(12k+j), prefactor 1/3^4; (2.14) the odd-index version (3^5, 0, -3^4, 0, 3^3, 0, -3^2, 0, 3, 0, -1, 0) on 12k+1, 3, 5, 7, 9, 11; and the classical alternating series pi*sqrt3 = 6 sum (-1)^k/(3^k (2k+1)) (2.15). The left-hand sides are not visible in the text, so which multiple of pi*sqrt3 each carries is not read. [READ, garbled]
- Section 2.4 "Ternary Zero Relations": (2.17) 0 = sum 3^(-6k) [3^5/(12k+1) - 5*3^4/(12k+2) - 3^4/(12k+4) - 3^3/(12k+5) - 23*3^2/(12k+6) - 3^2/(12k+7) - 3^2/(12k+8) - 5/(12k+10) + 1/(12k+11)] (the "23*3^2" is hard to read, so uncertain); (2.19), the one Kristensen-Mathiasen quote: (243,-243,-324,-81,27,0,-9,9,12,3,-1,0). [READ, partly garbled]
- The final summary lists two zero relations in P(1,3^6,12,.) form: (3^5, -5*3^4, 0, -3^4, -3^3, -23*3^2, -3^2, -3^2, 0, -5, 1, 0) and (3^5, -3^5, -2^2*3^4, -3^4, 3^3, 0, -3^2, 3^2, 3*2^2, 3, -1, 0). [READ] These are Adegoke's, partly overlapping the compendium's span.
- Adegoke's golden-ratio paper (arXiv:1603.06307, Fibonacci Quart. 52 (2014)): binary formulas for arctangents of odd powers of phi, and phi-nary formulas for pi, log 2, log phi, sqrt2 arctan sqrt2, with coefficients in Z[phi]. Not about base 3. [SNIPPET: abstract]
- Lafont's notes (Degree 1 BBP-Type Zero Relations, OEIS wiki https://oeis.org/wiki/User:Jaume_Oliver_Lafont/BBP): cited by Bailey for relations 113-121 and 122, 114, binary. Not read.

## 5. Not verified

- Bailey Formula 69 and 78 left-hand sides (symbols dropped).
- Whether Adegoke's (2.13)/(2.14) equal Formula 69 or 78 (my guess: the arithmetic matches 78 or 69 in structure; not checked).
- The compendium's current web version may differ from the copy read (it carries 131 relations).
- Zudilin's and Borwein et al.'s full texts.
- Book "Mathematics by Experiment", Bailey-Crandall 2001, any MO/MSE thread.
