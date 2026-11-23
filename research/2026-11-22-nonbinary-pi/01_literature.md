# Literature check: degree-1 BBP-type formulas for pi in non-binary bases

Date: 2026-11-22. Marks: [READ] = read on the source's own page/PDF; [SNIPPET] = only seen in a search result, abstract or a fetch-tool
summary; [INFERRED] = my own conclusion. About 10 web searches and 8 page reads were used. No page contained text addressed to me.

Statement S (checked): in Bailey's form P(1, b^B, N, A), with b not a power of 2, no series equals a non-zero rational multiple of pi.

## Summary

- Borwein-Borwein-Galway (BBG 2004) prove a theorem about a RESTRICTED class ("Machin-type": Q-linear combinations of arctan(b^-m), m >= 1,
  b not a proper power, b > 2). They do NOT prove S as stated. [READ]
- Bailey's Compendium and a secondary source (Mendonca, "Sagan numbers") state the stronger-sounding claim "no degree-1 BBP-type formula for pi
  unless the base is a power of two", citing BBG. I found no proof of that wording; BBG's own abstract is weaker. [READ]
- So S, for arbitrary N in P(1, b^B, N, A), is, as far as I could find, not proved in print, though it is attributed in print to BBG.
  [INFERRED; "not found" is weak evidence]
- No counterexample: no source gives a degree-1 formula for pi (or a rational multiple) in a base that is not a power of 2. [READ for BBG and
  the Bailey compendium; absence elsewhere is weak evidence]

## Q1. What BBG prove

Source: the paper itself (Cambridge Core PDF of Canad. J. Math. 56(5), 2004, 897-925), text extracted with pdftotext. [READ]

- Their definition of a BBP formula: sum over k >= 0 of p(k)/q(k) * b^-k with p, q in Z[k] (any degree, any polynomial denominator). A formula to
  base b^m also counts as base b. Unless stated otherwise b is assumed NOT a proper power. [READ]
- Focus: degree one ("logarithmic", s = 1 in Bailey's P(s,b,n,A)) and moreover "Machin-type": a constant written as a Q-linear combination of real
  parts, or of imaginary parts, of logarithms chosen so as to give a BBP formula in base b. The numbers whose logarithms are used lie in the
  multiplicative group Q[i]^x (Gaussian rationals). [READ]
- Abstract (paraphrased): for b in N, b > 2, b not a proper power, a b-ary Machin-type BBP arctangent formula for pi is pi = sum_m a_m arctan(b^-m),
  a_m rational (for b = 2 also terms arctan(1/(1 - 2^m)) are allowed). They show pi has no Machin-type BBP arctangent formula when b != 2. [READ]
- Theorem 7 (Section 3.4): for b > 2 not a proper power there is no Q-linear b-ary Machin-type BBP arctangent formula for pi. Proof idea: a formula
  gives prod (b^m - i)^(n_m) in Q^x; with M the top index, Bang's theorem (Zsigmondy) gives a primitive prime p of b^(4M) - 1; p = 1 mod 4 splits in
  Z[i], divides b^M - i but no b^m - i with m < M; the Gaussian valuation at that prime then gives a contradiction. This uses Bang/Zsigmondy, NOT
  Baker's theorem. [READ]
- Other results: Theorem 2 (exclusion criteria for arctan of single rationals, e.g. no ternary formula for arctan(2/3) or arctan(1/4)); Theorem 6
  (exclusion for logarithms); Example 4: if M_b = 0 there is no b-ary Machin-type logarithm formula for ln(b), in particular none for ln(10).
  Logarithm generators are ln(1 - b^-m), ln|1 +- i b^-m| (plus Aurifeuillian ones when b = 2). [READ]
- The authors' scope remark (paraphrase): when no Machin-type formula exists for a constant, to the best of their knowledge no BBP formula of any
  form is known for it. This is a statement of knowledge, not a theorem. [READ]
- What they leave open (their closing list of questions, paraphrased): structure and counting of binary arctangent zero relations; how to derive the
  original BBP formula (63) for pi from a Machin-type formula (it does not look Machin-type); Chebotarev/Jacobi-symbol exclusion criteria; combining
  with PSLQ; a number-field version of Zsigmondy (effective, for Q[i]); Aurifeuillian generators for binary logarithm formulas; BBP over Z[i]. They do
  not formulate a base-10 problem for general degree. [READ]
- Why BBG's class is narrower than P(1, b^B, N, A) [INFERRED]: P(1,B,N,A) = sum_j a_j L(1,B,N,j), and L(1,B,N,j) involves logarithms of
  1 - zeta * B^(-1/N), zeta an N-th root of unity, i.e. numbers in cyclotomic fields adjoined B^(1/N), not only Q[i]. BBG's generators come from
  integer-b pieces over Q[i]. Their Appendix B (not carefully read) reduces polylogarithmic formulas to L(s,b,n,j) with only j varying; I did not
  verify whether that closes the gap to arbitrary N.
- Citation oddity: Bailey's reference [18] gives pages 1339-1342; the paper is pp. 897-925 (DOI 10.4153/CJM-2004-041-2). [READ]

## Q2. Is S, or something stronger, in print?

- Bailey, "A Compendium of BBP-Type Formulas for Mathematical Constants": says a 2004 paper by Borwein, Galway and Borwein showed there are no other
  degree-1 BBP-type formulas for pi except those whose base is a power of two. Also: pi^2 has a base-2 formula (29) and a base-3 formula (76);
  Lagarias links formulas in two or more bases to G-functions and a Furstenberg conjecture. [READ] This is the wording closest to S, but it is a
  summary of BBG; BBG's theorem as read above is narrower. [INFERRED: the summary overreaches]
- J. R. G. Mendonca, "Sagan numbers" (arXiv:1209.2348): BBG showed there is no base-n degree-1 BBP-type formula for pi when n is not a power of two; this
  does not rule out completely different approaches to digits in other bases; "an open problem". [READ] (secondary; same overstatement)
- MathWorld "BBP-Type Formula": BBG showed pi has no non-binary Machin-type BBP arctangent formula; does not rule out a different digit-extraction
  scheme in other bases; nothing on base 10. [SNIPPET: fetch-tool summary]
- Wikipedia "Bailey-Borwein-Plouffe formula": general base b >= 2 allowed; Plouffe 2022 decimal digit extraction (needs effectively more work than the
  binary case); Euler 1779; no mention of BBG or a non-existence result. [SNIPPET: fetch-tool summary]
- Baker's theorem: nothing found linking BBP-type formulas to Baker or linear forms in logarithms (searched "BBP" + "Baker" + "linear forms in
  logarithms" + nonexistence). [not found; weak evidence] The only exclusion technique found in print is Bang/Zsigmondy primitive prime divisors (BBG).
- Chamberland, Takahashi, Adegoke, Lafont, Kristensen-Mathiasen: no non-existence statement for pi found. Kristensen-Mathiasen (arXiv:2208.07696,
  "BBP-type formulas -- an elementary approach") is constructive (degree one, Pisot/non-integer bases, null formulas); its concluding remarks list open
  problems on extracting digits in irrational bases and on higher degree, not S. [READ for K-M remarks; others not found]
- Not read: Borwein-Bailey "Mathematics by Experiment", Bailey-Crandall, Galway's thesis. [not searched in depth]

## Q3. How is the open problem worded?

- Mendonca: finding similar identities for pi in other bases is "a whole research program"; BBG excludes degree-1 formulas for non-powers of two but not
  "completely different mathematical approaches" for fast digit computation in other bases. Class stated: degree-1 BBP-type. [READ]
- MathWorld: same point, with the class "Machin-type arctangent". [SNIPPET]
- Zudilin, "A BBP-style computation for pi in base 5" (arXiv:2409.10097, Sept 2024; v1 was titled "... in base 10"): the fetched summary of v1 says the
  extension to other bases is an open question; the abstract calls the paper a joke about computing digits in base 5 from a given place. [abstract page
  READ; the open-question wording SNIPPET] The scheme uses integers b_n with |b_n| < 2*5^n (non-periodic numerators; Salikhov/Zeilberger approximations,
  identity with 1/(1 +- 2i), norm 5) and sum b_n/((2n+1) 5^(2n)) = 5 pi/16. This is NOT of Bailey's degree-1 form. [SNIPPET; INFERRED for the last remark]
- Plouffe 2022 gives a decimal digit-extraction method for pi (Bernoulli-number based, not a BBP formula). [SNIPPET]
- Nobody I found states the question precisely as "any degree, any polynomial denominators, base 10". BBG define BBP formulas that generally but prove only
  the Machin-type degree-1 case. [INFERRED]

## Q4. Counterexample check

- No source gives a degree-1 formula for pi (or a non-zero rational multiple) in a base that is not a power of 2. [READ for BBG and Bailey; weak
  evidence elsewhere]
- Related formulas that do NOT count:
  - pi^2 in base 3 (degree 2): Bailey Compendium formula (76), pi^2 = (2/27) P(2, 3^6, 12, (243, -405, 0, -81, -27, -72, -9, -9, 0, -5, 1, 0)). [READ]
  - pi*sqrt(3) in base 3 (degree 1): Adegoke, arXiv:1603.04974, Section 2.3, formulas (2.13), (2.14) in base 3^6 with denominators 12k+j, and the
    alternating series pi*sqrt(3) = 6 * sum_k (-1)^k / (3^k (2k+1)) (extraction partly garbled; check against the paper). [READ]
  - pi in the golden-ratio base: Adegoke, arXiv:1603.06307 [SNIPPET]; Kristensen-Mathiasen, arXiv:2208.07696 (degree one in Pisot/non-integer real bases,
    e.g. formulas with parameter b = 12 and golden-ratio-type bases) [READ, fragmentary].
  - Zudilin 2024 base-5/base-10 computation: non-periodic numerators (see Q3). [SNIPPET]
- Negative bases:
  - Euler 1779, as reported by Bailey: pi = sum_k (-1)^k/4^k * (2/(4k+1) + 2/(4k+2) + 1/(4k+3)), i.e. base -4 (degree 1, N = 4); the second Euler formula has
    (-1)^k / 2^(30k) over denominators 60k+j (base -2^30). [READ] Both have |base| a power of 2, so they fit S.
  - Adegoke uses P(s, -27, 6, ...) (base -27 = -3^3) for ln 3, 3 ln 3, Cl_2(pi/3), etc. (arXiv:1603.04974). [READ] These are not pi; for pi*sqrt(3) the base is
    positive 3.
  - Reduction [INFERRED]: a series in base -B becomes a positive base-B^2 series (pair k = 2k', 2k'+1; same trick as BBG formula (2)) of the same degree-1
    type with N doubled. Thus negative bases with |b| not a power of 2 are covered by S via b^2, and no counterexample arises. Bellard's pi formula in base
    -1024 (from memory, not read here) is consistent with |b| a power of 2.

## Assessment for Statement S

1. S is the natural reading of Bailey's and Mendonca's sentence, but BBG's theorem as read is narrower (Machin-type, generators arctan(b^-m)). The step to
   arbitrary P(1, b^B, N, A) is, to my reading, not carried out in print. [INFERRED]
2. BBG's technique (Bang/Zsigmondy primitive prime divisors) is an ingredient of the proof you have; Baker's theorem is the extra tool needed for general N.
   Their open question about a number-field Zsigmondy points the same way. [INFERRED]
3. Suggested wording: "BBG (2004) exclude Machin-type formulas; Bailey and others summarize this as excluding all degree-1 formulas; we prove S for the full
   P(1,b^B,N,A) class." Claim novelty only after checking BBG Appendix B and Galway's thesis. [INFERRED]

## URLs used

- https://www.cambridge.org/core/journals/canadian-journal-of-mathematics/article/finding-and-excluding-bary-machintype-individual-digit-formulae/BB7919C8E1AE66878AE8D7BC7F0EBFA3
- https://www.cambridge.org/core/services/aop-cambridge-core/content/view/BB7919C8E1AE66878AE8D7BC7F0EBFA3/S0008414X0003385Xa.pdf/finding-and-excluding-b-ary-machin-type-individual-digit-formulae.pdf (read via pdftotext)
- https://www.davidhbailey.com//dhbpapers/bbp-formulas.pdf (Bailey Compendium)
- https://arxiv.org/pdf/1209.2348 (Mendonca, Sagan numbers)
- https://arxiv.org/pdf/1603.04974 (Adegoke, ternary BBP-type formulas)
- https://arxiv.org/pdf/2208.07696 (Kristensen-Mathiasen)
- https://arxiv.org/abs/2409.10097 and https://arxiv.org/html/2409.10097v1 (Zudilin)
- https://arxiv.org/html/2507.20428v1 (Madhava-Gregory-Leibniz remainder; base 16 only)
- https://arxiv.org/pdf/1603.06307 (Adegoke, golden ratio; snippet only)
- https://mathworld.wolfram.com/BBP-TypeFormula.html
- https://en.wikipedia.org/wiki/Bailey%E2%80%93Borwein%E2%80%93Plouffe_formula
- https://ask.metafilter.com/360896/Math-formula-that-only-works-in-some-base-systems (snippet only)

## Follow-up: is the general statement proved in BBG?

Verdict: NO. BBG proves only the Machin-type arctangent case; they explicitly list the general degree-1 case (arbitrary n, roots of unity) as an
open question (their Comment 10). Bailey's and Mendonca's wording is an overstatement of BBG. This CORRECTS my guess in Q1 above that Appendix B might
bridge the gap: it does not (it goes the other way). Source: the BBG PDF, text extracted with pdftotext, read directly. [READ unless marked]

1. Sections 1 and 2.
   - Definition 1 (Section 2.3): a constant has a b-ary Machin-type arctangent formula iff it is a Q-linear (or Z-linear) combination of the generators
     arctan(b^-m) (m >= 1, i.e. arg(1 - i b^-m)), plus, only for b = 2, the "Aurifeuillian" generators arctan(1/(1 - 2^m)). Logarithmic version (Definition 3): generators
     ln(1 - b^-m), ln|1 +- i b^-m| (plus Aurifeuillian ones for b = 2). [READ]
   - Section 1.2: they restrict to degree one AND to "formulae of a special form which we call Machin-type", with logarithms of elements of Q[i]^x. They call the class
     "formally limited" (abstract) and "restricted" (Section 1.2). [READ]
   - Remark after Definition 1: Machin-type formulas are "in one sense more restricted than the formulae considered by Bailey" but also more general in allowing
     P(1, b^m, n, ...) with m and n varying; Appendix B shows every Machin-type formula reduces to Bailey's form. So the inclusion proved is Machin-type inside
     Bailey's form, NOT the converse. [READ]
   - No sentence says that all degree-1 formulas are or reduce to Machin-type. The opposite is said: Comment D(3) states that the original 1995 BBP formula
     pi = sum 16^-k (4/(8k+1) - 2/(8k+4) - 1/(8k+5) - 1/(8k+6)) "does not appear to be" a Q-linear combination of Machin-type generators and asks for a derivation from a
     Machin-type formula; Comment D(11) asks how to justify that the limited Machin-type generators give all or most interesting arctans and logs. [READ]
     So Machin-type does not even contain all binary degree-1 formulas for pi.
   - Intro statement of knowledge only: "to the best of our knowledge", when no Machin-type formula exists no BBP formula of any form is known (abstract; Section 1.2). [READ]
2. Appendix B ("Conversion to Polylogarithmic Formulae").
   - Proves: V_{s,b,m,n} = span_Q of sum_k b^(-mk)/(nk+j)^s, 1 <= j <= n; Lemma 8 (V_{s,b,m,n} inside V_{s,b,m,dn}, V_{s,b,m} inside V_{s,b,dm,dn}); Theorems 9, 10 (an element of
     V_{s,b,m} or V_{s,b} lies in a single V_{s,b,m,n}); hence any constant with a Machin-type formula has a formula P(s, b^m, n, A) with rational A. It is a
     bookkeeping/lattice argument (common n and m); constructive example: arctan(1/6) as P(1, 2^36, 24, ...). [READ]
   - It does NOT treat logarithms 1 - zeta b^(-1/N) with zeta an N-th root of unity, does not decide anything about pi in V_{1,b}, and uses no transcendence result: a grep for
     Baker, Lindemann, Gelfond, "transcend" finds nothing in the paper. The tools are Bang/Zsigmondy primitive prime divisors, ord_p and Gaussian-prime valuations. [READ]
   - Comment D(10) is the explicit statement of the gap: with zeta_n a primitive n-th root of unity, L(1,b,n,j) = -(1/n) b^(j/n) sum_{r=0}^{n-1} zeta^(-rj) ln(1 - zeta^r b^(-1/n)) (their
     eq. 64); they ask whether their techniques can decide if pi is a linear combination of L(1, b^m, n, j) with b (and perhaps n) fixed, and say this "would probably require a good
     understanding" of Q[zeta_n, b^(1/n)]. So the general degree-1 class is posed as an open problem. [READ; the words in quotes are their phrase, shortened]
   - Comment D(9) also suggests extending to Gaussian-integer bases, again as future work. [READ]
3. Bailey's Compendium (version dated April 8, 2023, from davidhbailey.com/dhbpapers/bbp-formulas.pdf): the sentence is in Section 1 (Introduction), on page 2, right after
   formulas (1)-(3) for pi (the base-16 BBP formula, Euler's base -4 formula and Euler's second formula). Paraphrase: a 2004 paper by Borwein, Galway and Borwein showed there are no
   other degree-1 BBP-type formulas for pi except those, like (1)-(3), whose "base" is a power of two; but for pi^2 there is both a base-2 formula (29) and a base-3 formula (76).
   No qualification such as "Machin-type" is attached there. In the same document Section 3 (arctangent formulas) does mention BBG's "significant structure theory for BBP-type
   arctangent formulas". Bailey's reference [18] has wrong page numbers (1339-1342). [READ]
   The 2004 version of the Compendium (corpora.tika.apache.org copy) appeared in search results but I did not read it.
4. Searches (3 of the allowed 6): "Galway thesis ... Machin-type ... degree one ... Zsigmondy cyclotomic"; "Borwein Galway BBP pi no formula degree-1 logarithmic base not power of
   two proof"; plus earlier ones. I found no Galway thesis, erratum, later paper by these authors, or citing paper that states or proves the general degree-1 result. Citing sources
   (Bailey, Mendonca, MathWorld, MetaFilter) repeat or soften the claim; MathWorld says Machin-type only. [not found; weak evidence]

Consequence for Statement S [INFERRED]: S for the full class P(1, b^B, N, A) (arbitrary N, so cyclotomic fields Q[zeta_N, b^(1/N)]) is, as far as I can find, NOT proved in
print; BBG's Comment 10 asks exactly this question. A proof by Baker's theorem plus primitive prime divisors would settle a problem BBG pose, while the folklore statement in
Bailey's Compendium (page 2) would then be justified retroactively. Worth stating that the "known" claim in print is attributed to BBG without a proof there.
