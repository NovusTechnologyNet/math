# Where the binary degree-1 BBP classification could matter for other work

Date: 2026-11-22. 17 of 30 web searches used.

Reading conventions:
- **[P]** = read on a primary page or full PDF. Where a PDF was fetched I extracted the text locally with pdftotext and read it myself (Bailey compendium, Borwein-Borwein-Galway (BBG), Zudilin, Tijdeman survey, Chamberland).
- **[P*]** = opened with WebFetch, but the page was summarised by a small model, so details are only as reliable as that summary.
- **[S]** = seen only in a search-result snippet or search summary, not opened. Treat as unverified.

---

## 1. BBP-type formulas for pi in other bases

**What BBG 2004 prove [P].** "Finding and Excluding b-ary Machin-Type Individual Digit Formulae", Canad. J. Math. 56 (2004) 897-925. PDF: https://www.cambridge.org/core/services/aop-cambridge-core/content/view/BB7919C8E1AE66878AE8D7BC7F0EBFA3/S0008414X0003385Xa.pdf/finding-and-excluding-b-ary-machin-type-individual-digit-formulae.pdf
- Scope: b a natural number that is not a proper power. A "Machin-type BBP arctangent formula" is pi = sum_m a_m arctan(-b^-m) with a_m rational (for b = 2 also terms arctan(1/(1-2^m))). Main result: pi has no such formula when b is not 2. (The extracted abstract reads "b = 2"; that is a lost "not equal" sign.) The proof uses Bang/Zsigmondy primitive prime factors, the same tool as ours, with primes p = 1 mod 4 (their Theorem 2).
- The abstract adds that when no Machin-type formula exists for a constant, no BBP formula of any form is known for it. That is an observation, not a theorem.
- So what is proved concerns only the Machin-type generators (arctangents of rationals b^-m). It is not a statement about all degree-1 BBP formulas.

**Research Problem (10) in BBG [P].** With zeta_n a primitive n-th root of unity, L(1,b,n,j) is the general degree-1 generator, an explicit combination of log(1 - zeta^r b^(-1/n)) (their equation 64). Problem (10) asks whether their techniques can decide if pi is a linear combination of L(1, b^m, n, j) with b, and perhaps n, fixed, and says this "would probably require a good understanding of Q[zeta_n, b^(1/n)]". That is exactly the general degree-1 question in a fixed base. Our classification answers it for b = 2. For other b I found it still open.

Other BBG problems that touch our results [P]:
- (2): how many Q-linearly independent binary Machin-type arctangent zero relations exist, and good upper bounds? (This is the one our project answers.)
- (3): the original BBP formula for pi does not look like a Machin-type combination; is there a simple derivation of it from one? Our result (every formula lies in an 8-dimensional space of period-120 patterns) bears on this.
- (4): infinitely many primes p = 1 mod 4 with 4 dividing ord_b(p)?
- (7): effective Zsigmondy over Q[i] and number fields (the Z[i] input of our method).
- (8): Aurifeuillian generators in logarithm formulas.
- (9): allow Gaussian coefficients so logs and arctans are treated together.
- (11): why would Machin-type generators give all interesting arctans and logs?

**Bailey's compendium [P].** https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf (version dated April 8, 2023). It says BBG showed there are no other degree-1 BBP-type formulas for pi except those whose "base" is a power of two. That overstates BBG, which only treats Machin-type generators. Bailey adds that for pi^2 there are both a base-2 formula (Formula 29) and a base-3 formula (Formula 76); both have s = 2, so the base restriction does not carry over to higher degree.

**MathWorld [P*].** https://mathworld.wolfram.com/BBP-TypeFormula.html. Per the fetch summary: BBG showed pi has no Machin-type BBP arctangent formula that is not binary, and the page says this does not rule out a completely different scheme for other bases. No open problems listed.

**Wikipedia [P*].** https://en.wikipedia.org/wiki/Bailey%E2%80%93Borwein%E2%80%93Plouffe_formula. The summary says it mentions neither BBG nor non-existence. It does mention Bellard's faster variant and Plouffe's 2022 formula for the nth decimal digit of pi, noting that it effectively needs earlier digits.

**Is the general statement "no degree-1 BBP formula for pi in a non-power-of-2 base" proved anywhere?** I found no published proof beyond the Machin-type case. One targeted search returned only BBG and Bailey's restatement [S: https://www.davidhbailey.com//dhbpapers/bbp-formulas.pdf]. Absence from a search is not proof of absence, but Bailey's phrasing looks like a folklore upgrade of BBG's theorem. A rigorous proof for integer b not a power of 2 (even just b = 3, 5, 10) would be new. Our method plausibly gives it for the Gaussian-field part; the general case needs the span of log(1 - zeta^r b^(-1/n)) as in Problem (10) (my inference).

**Zudilin, arXiv 2409.10097 [P: full v2 PDF read].** https://arxiv.org/abs/2409.10097. The v1 title was "...in base 10" and later versions "...in base 5" [S: https://arxiv.org/html/2409.10097v1; I did not read v1]. The abstract says "We joke about how to compute (promptly) the digits of pi, in base 5". What it does:
- Starts from the Salikhov / Zeilberger-Zudilin identity writing pi as the imaginary part of 8 * sum (1/(2n+1)) (1-2i)^-(2n+1). Since |1-2i|^2 = 5 he reads this as a "base 5" BBP-type formula (strictly, powers of (1-2i)^2).
- Proposes the BBP strategy in Z[i]: compute 5^d times the series mod 1 by fast modular exponentiation.
- Section 3, "An obvious flaw": the congruence fails when 2n+1 > d - k, because the true denominator is 5^(2n+1-d+k) m, not m, and truncating the sum does not help since the tail cannot be bounded.
- States that it is open whether such a computation is possible for pi in other bases, and asks "Are there more suitable formulae for pi or other interesting constants, defined over quadratic or more general algebraic extensions". No theorem, no working algorithm.

Link to us: Zudilin's series is a Gaussian-coefficient (BBG Problem (9)) arctangent-type object with base norm 5. Our method (Baker + primitive prime divisors in Z[i]) is aimed at exactly the question "is there any rational-coefficient degree-1 formula here". A precise "no" or "yes" for base 5 with Gaussian coefficients would be a rigorous version of his section 3. That is my inference, not something I verified.

Other work on non-binary bases (abstract pages only [P*], except Plouffe [S]):
- Kristensen and Mathiasen, arXiv 2208.07696: a pi formula in the irrational Pisot base 1 + sqrt(3). https://arxiv.org/abs/2208.07696
- Cloitre, arXiv 2508.03743: BBP-type formula for pi^2 in golden-ratio base. https://arxiv.org/abs/2508.03743
- Plouffe, arXiv 2201.12601: nth decimal or binary digit of pi via Bernoulli/Euler number asymptotics; not BBP type. [S] https://arxiv.org/pdf/2201.12601
These show non-integer bases and non-BBP schemes exist, which is why the "integer base, degree 1" statement is the clean target.

**Verdict 1: could matter: yes.** A complete proof for integer bases that are not powers of 2 would turn Bailey's folklore statement into a theorem and answer BBG Problem (10); Zudilin's base 5 question is the natural test case.

---

## 2. Other tables and constants in Bailey's compendium

All from the compendium PDF [P] https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf unless marked.

**Table 1 (zero relation counts), Section 12.**
- The table has rows for s = 1, 2, 3 and 4 (degrees 1 to 4), not only degree 1. Example rows (s, b, n: count): (1, 2^12, 12: 1), (1, 2^12, 24: 5), (1, 2^20, 40: 3), (1, 2^60, 120: 7), (2, 2^60, 120: 4), (3, 2^60, 120: 2), (4, 2^60, 120: 1).
- Every row is binary. The text says all the zero relations listed except the last two are binary. The last two, listed after the table, are in base 729 = 3^6 with n = 12 and s = 1. So base-3 zero relations exist but no base-3 counts are tabulated.
- Bailey says it is not understood why zero relations occur for certain s, b and n but not others (my paraphrase; the sentence is in Section 12), citing only reference [21] as related discussion.
- He also notes that where a zero relation exists, nontrivial formulas with the same parameters usually exist too, suggesting "significant BBP-type results may remain to be discovered" (his words, 8 words).

So the s = 1 binary column is what our classification explains. Degrees 2, 3, 4 and base 3 are equally unexplained. Extending to s >= 2 needs a Baker-type independence result for polylogarithms of order >= 2, which does not exist (see section 4).

**Constants and open questions stated or implied:**
- log p for primes: the compendium lists primes with known binary formulas for log p (2, 3, 5, 7, 11, 13, 17, 19, 29, 31, 37, 41, 43, 61, 73, ..., 4432676798593) and says it is unknown whether all primes have this property or even whether the list is finite or infinite. 23 is absent. Chamberland [P: https://cs.uwaterloo.ca/journals/JIS/VOL6/Chamberland/chamberland60.pdf] says Pomerance showed 23 cannot be written in a certain form, and that it is still unknown whether log 23 has a binary BBP formula (2003). He proves a binary formula for log q for every Gaussian-Mersenne prime q.
- arctan(2/7): "not known" whether it has a binary BBP formula; arctan(5/36) does (Adegoke, Lafont, Layeni).
- Base 3: Section 9 lists ternary formulas (log 2, an arctan constant, pi*sqrt(3) in base 36, log 11, log 13 and others). OEIS A165132 lists only 2, 3, 5, 7, 11, 13 as primes with known ternary log formulas [S: https://oeis.org/A165132].
- pi^2: has binary (29) and ternary (76) degree-2 formulas, noted above.
- Catalan's constant: a binary formula credited to Adegoke; zeta(3): degree-3 binary and ternary formulas exist. I found no specific open question stated for either; the open question is the general "which combinations" one.
- pi*sqrt(3): Adegoke, Lafont and Layeni (arXiv 1603.07395) give new binary formulas without computer search, and formulas for logs of an infinite set of primes [P*: abstract only] https://arxiv.org/abs/1603.07395
- Normality: Bailey-Crandall Hypothesis A (open) would make BBP constants normal. Lagarias suggests special significance for constants with BBP formulas in two bases, e.g. 2 and 3 (this last statement is the compendium's summary [P]; the Lagarias paper was not opened [S: https://arxiv.org/abs/math/0101055]).
- Euler's 1779 formulas for pi, recognised as BBP-type by Craig-Wood in 2023, appear in the compendium intro (its formulas 2 and 3). They are binary degree 1 and so fall under our classification.

**Related paper [P*]:** Barsky, Munoz, Perez-Marco, "On the genesis of BBP formulas", Acta Arith. 198 (2021), arXiv 1906.09629, https://arxiv.org/abs/1906.09629. Abstract: a general method for generating BBP formulas, explains why many pi formulas are rearrangements of each other, and clarifies where some null BBP formulas come from. It does not claim a complete classification, so our 8-dimensional result is complementary and worth cross-checking.

**Verdict 2: could matter: yes.** The s = 1 binary column of Table 1 now has a theorem behind it, replacing "mysterious"; the explicit open questions (log 23, arctan(2/7), which primes admit binary log formulas, base-3 relations) look reachable by the same method; degrees 2-4 do not.

---

## 3. Digit-extraction practice

**y-cruncher [P*: summary of https://numberworld.org/y-cruncher/version_history.html, first 100000 of 114741 characters].**
- v0.8.4.9537 (Feb 21, 2024): the BBP digit extractor gained Huvent's formula, said to be "slightly faster than Bellard's".
- v0.8.5.9539 (Jul 1, 2024): the default BBP algorithm changed to Huvent's formula. The same release's compiler change made the BBP program slower.
- v0.7.8.9503 (Oct 2019): digit extractor revamped; offset limits tabulated for the original and Bellard formulas.
- No optimality claim. I found no head-to-head Huvent vs Bellard benchmark [S: search summary].
- Huvent's Catalan-constant formula was added in 2013 and called outdated in 2019. That is a different constant.
- Records page [P*] https://numberworld.org/y-cruncher/records.html : a pi record needs a BBP computation at the matching hex offset as an independent check of the main run. It does not mention Huvent.

**Far-out bit and digit records.**
- Yahoo, Sze 2010, "The Two Quadrillionth Bit of Pi is 0!" [P*] https://ar5iv.arxiv.org/html/1008.3171 : used Bellard's formula, two runs at positions n and n-4 and accepted only agreeing bits. Stated future work: ten-quadrillionth or quintillionth bit, and first n digits on Hadoop. Cluster size of 1000 to 4000 machines is in the abstract page and snippets [S].
- Karrels 2013, eight-quadrillionth bit on GPUs [S: https://techradar.com/news/computing-components/graphics-cards/nvidia-gpus-help-pi-researcher-calculate-eight-quadrillionth-place-1138118]. Formula not stated in the snippet.
- Takahashi 2016, 10^17-th hex digit [P*] https://www.hpcs.cs.tsukuba.ac.jp/~daisuke/pihex.html : Bellard's formula in both runs, no reason given. A Takahashi paper "On the computation and verification of pi using BBP-type formulas" exists [S: https://bvbvf1.bib-bvb.de/vufind/PrimoRecord/cdi_proquest_journals_2332363489]; not opened.
- Bellard's 2009 record was verified with a BBP-type formula [S: https://www.bellard.org/pi/pi2700e9/announce.html].

**Stated open problems.** Bellard states one [P*: https://www.bellard.org/pi/pi_bin/pi_bin.html]. His 1997 note gives a formula in base 2^10 with denominators 4n+1, 4n+3, 10n+1, 10n+3, 10n+5, 10n+7, 10n+9, which he says computes the nth binary digit about 43% faster than the BBP formula, and he says the existence of a still faster formula "remains an open question". Our result (fewest terms per bit is 2/3, attained only by the two Huvent formulas) answers that within binary degree-1 formulas. I found no comparable statements by Gourdon, Plouffe, Takahashi, Karrels or Yee.

Caveat: "terms per bit" is our metric. Real run time also depends on modular arithmetic cost, offset limits and vectorisation, so fewest terms is not automatically fastest. y-cruncher's own wording ("slightly faster") suggests a modest gain.

**Verdict 3: could matter: yes (modestly).** It closes Bellard's 1997 question for binary degree-1 formulas and justifies y-cruncher's switch to Huvent, but the practical gain is small and no one frames it as pressing.

---

## 4. Transcendence literature on periodic sums

**Baker, Birch, Wirsing, "On a problem of Chowla", J. Number Theory 5 (1973).** I did not open the original. From Murty's exposition "A Look at Chowla's Problem" [P*] https://ar5iv.labs.arxiv.org/html/2009.14359 : f from Z to algebraic numbers, nonzero, period q, f(r) = 0 whenever 1 < gcd(r,q) < q, and the q-th cyclotomic polynomial irreducible over Q(f(1),...,f(q)); then L(1,f) = sum f(n)/n is nonzero. The full vanishing characterisation (odd and even f) combines BBW with Chatterjee-Murty-Pathak and Okada-type criteria [P*, same page]. This is the case z = 1 (a root of unity) of sum f(n) z^n / n. Our setting is z = 2^-B, not a root of unity. I found no published treatment of the vanishing question there. A snippet from the Murty-Saradha work says no satisfactory extension of Baker's theorem handles the general polylogarithm case [S: https://mast.queensu.ca/%7Emurty/ram-siddhi-tapas.pdf; not opened].

**Adhikari, Saradha, Shorey, Tijdeman, "Transcendental infinite sums", Indag. Math. 12 (2001) 1-14.** I did not open it; bibliographic data only [S: https://repository.ias.ac.in/67731]. The content below is from Tijdeman's survey "On irrationality and transcendency of infinite sums of rational numbers", which I read in full text [P]: https://pub.math.leidenuniv.nl/~tijdemanr//tijsho3.pdf
- Theorem 1 (from ASST Theorem 4): for P, Q in Q[x] with Q having only simple rational zeros, and alpha algebraic, if S = sum alpha^n P(n)/Q(n) converges then S is rational or not algebraic; if alpha = 1 and all zeros lie in [-1, 0), S = 0 or transcendental. Proof route: Lehmer's identity turns the sum into a combination of (1 - zeta) log(1 - zeta), then Baker's theorem.
- Stated gaps: Theorem 1 excludes algebraic irrational values "but it leaves the question open whether S is rational", and "Is S rational?" is the subject of later subsections. A conjecture is stated: for f in Z(x), if S is algebraic then it is rational.
- Link: with alpha = 2^-B and denominators nj+i, S rational, S zero, or S rational multiple of pi is the question our classification decides. This is a concrete family of the "is S rational?" problem. The classification does not itself address transcendence; Baker already gives that.

**Murty-Weatherby, Murty-Saradha.** Murty and Weatherby, "On the transcendence of certain infinite series", Int. J. Number Theory 7 (2011) 323-339, studies sums over Z of A(n)/B(n) and ties them to Gelfond-Schneider-type conjectures [S: https://w7.cms.math.ca/Events/winter09/abs/pdf/nt-cw.pdf]. The Queen's PDF link redirected to a home page, so I could not read it. Weatherby's thesis uses Baker's theorem for sums such as 1/(n^3 +/- c^3) [S: https://queensu.scholaris.ca/items/8a73d833-e2cb-48d9-affa-98a7a9871bdf]. Murty-Saradha on Euler-Lehmer constants (at most one algebraic value) [S: https://mast.queensu.ca/~murty/murty-saradha.pdf] is again the z = 1 case. These concern rational-function sums, not geometric-weighted sums, so the link is by method, not by a stated problem.

**Verdict 4: could matter: maybe.** The best link is Tijdeman's "is S rational?" for algebraic alpha (our z = 2^-B), but nobody stated our classification as a target, and the root-of-unity (Chowla) theory is a neighbouring, not identical, setting.

---

## 5. Other questions the method plausibly reaches

Candidates with where each is stated. Likelihood is my judgement, not sourced.

1. **BBG Research Problem (10) for b other than powers of 2.** Is pi a linear combination of L(1, b^m, n, j)? Source: BBG PDF in section 1. Needs the structure of Q(zeta_n, b^(1/n)); BBG Problem (7) (Zsigmondy over number fields) is the ingredient they name as missing. Likelihood: moderate.
2. **Which primes have binary BBP formulas for log p; is log 23 one?** Source: compendium Section 2 and Chamberland 2003 (both [P]). A classification of Q-relations among log(1 - 2^-m) generators decides this by the same exclusion arguments (BBG acknowledgements credit Pomerance for the Bang's-theorem exclusion idea). BBG Problem (8) (Aurifeuillian generators) is the known obstacle. Likelihood: high, as the logarithm analogue of our arctangent result.
3. **Does arctan(2/7) have a binary BBP formula?** Source: compendium Section 3 [P]. Same Z[i] machinery; 7 + 2i has norm 53. Likelihood: high.
4. **Base-3 zero relations and base-3 degree-1 classification** (the two b = 729, n = 12 relations; no base-3 table). Source: compendium Section 12 [P]. Needs Eisenstein-type fields. Likelihood: moderate.
5. **Tijdeman's "is S rational?" for algebraic alpha** (survey [P], section 2.1 discussion). A general theorem for alpha = 1/b and linear denominators generalises our b = 2^B case. Likelihood: moderate.
6. **Chowla-type vanishing at z not a root of unity**: classify periodic f with sum f(n) z^n / n = 0 for z = 1/2^B. Our zero relations are exactly this for z = 2^-B. Compare Baker-Birch-Wirsing for z = 1. I found no published treatment [absence in my searches]. Likelihood: high for z = 2^-B, open beyond.
7. **Cross-check with Barsky-Munoz-Perez-Marco** on null BBP formulas ([P*] abstract). A concrete consistency test, not an open question.
8. **Degrees 2-4 in Table 1.** Not reachable: Baker's theorem does not cover polylogarithm linear forms of order >= 2.

**Verdict 5: could matter: yes.** Items 2, 3 and 6 look the most directly reachable.

---

## URLs used

Opened and read as text (pdftotext on the saved PDF):
- https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf
- https://www.cambridge.org/core/services/aop-cambridge-core/content/view/BB7919C8E1AE66878AE8D7BC7F0EBFA3/S0008414X0003385Xa.pdf/finding-and-excluding-b-ary-machin-type-individual-digit-formulae.pdf
- https://arxiv.org/pdf/2409.10097 and https://arxiv.org/abs/2409.10097
- https://pub.math.leidenuniv.nl/~tijdemanr//tijsho3.pdf
- https://cs.uwaterloo.ca/journals/JIS/VOL6/Chamberland/chamberland60.pdf

Opened via WebFetch (summarised):
- https://www.bellard.org/pi/pi_bin/pi_bin.html
- https://numberworld.org/y-cruncher/version_history.html
- https://numberworld.org/y-cruncher/records.html
- https://www.hpcs.cs.tsukuba.ac.jp/~daisuke/pihex.html
- https://ar5iv.arxiv.org/html/1008.3171 and https://arxiv.org/abs/1008.3171
- https://ar5iv.labs.arxiv.org/html/2009.14359
- https://mathworld.wolfram.com/BBP-TypeFormula.html
- https://en.wikipedia.org/wiki/Bailey%E2%80%93Borwein%E2%80%93Plouffe_formula
- https://arxiv.org/abs/1906.09629
- https://arxiv.org/abs/1603.07395
- https://arxiv.org/abs/2208.07696
- https://arxiv.org/abs/2508.03743

Seen only in search results, not opened:
- https://www.cambridge.org/core/journals/canadian-journal-of-mathematics/article/finding-and-excluding-bary-machintype-individual-digit-formulae/BB7919C8E1AE66878AE8D7BC7F0EBFA3
- https://arxiv.org/html/2409.10097v1
- https://arxiv.org/pdf/2201.12601
- https://www.bellard.org/pi/pi2700e9/announce.html
- https://techradar.com/news/computing-components/graphics-cards/nvidia-gpus-help-pi-researcher-calculate-eight-quadrillionth-place-1138118
- https://bvbvf1.bib-bvb.de/vufind/PrimoRecord/cdi_proquest_journals_2332363489
- https://repository.ias.ac.in/67731
- https://w7.cms.math.ca/Events/winter09/abs/pdf/nt-cw.pdf
- https://queensu.scholaris.ca/items/8a73d833-e2cb-48d9-affa-98a7a9871bdf
- https://mast.queensu.ca/~murty/murty-saradha.pdf
- https://mast.queensu.ca/%7Emurty/ram-siddhi-tapas.pdf
- https://oeis.org/A165132
- https://arxiv.org/abs/math/0101055

Attempted but not read:
- https://arxiv.org/pdf/1809.01841 (binary PDF, text not extracted)
- https://mast.queensu.ca/~murty/Murty-Weatherby-Series.pdf (redirected to a Queen's home page)
