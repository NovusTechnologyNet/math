# P12: BBP-type formulas for logarithms and arctangents of rationals

Date of pass: 2026-11-22. Marks: [READ] read on the source (PDF text extracted with pdftotext),
[SNIPPET] seen only in a search result, abstract or API record, [INFERRED] my own conclusion.
No quotation is used in this report.

## 1. Summary

1. Chamberland 2003 [READ] is a constructive paper: it lists about 100 primes (up to 5.3e21 and
   beyond, 1.46e48) with binary formulas, built from Re log of cyclotomic values Phi_m at
   (+-1 +-i)/2^n and similar points, tied to Aurifeuillian factorizations. It proves nothing
   about primes that are NOT on the list. The only conjecture in it: constants of BBP shape are
   rational or normal. It says it is unknown whether log 23 has a binary formula.
2. Bailey's Compendium (version of 8 April 2023) [READ] states that it is unknown whether all
   primes have a binary log formula, "or even whether the list is finite or infinite", and that
   arctan(2/7) is unknown. It also states (abstract-level section 1) that Borwein-Borwein-Galway
   showed there is no degree-1 BBP-type formula for pi except in power-of-2 bases. That is an
   overstatement of what BBG proved (see section 5).
3. BBG 2004 [READ] proves exclusion theorems only inside the "Machin-type" class (Q-linear
   combinations of Re/Im log(1 - b^-m), plus Aurifeuillian generators when b = 2). Thm 4: no
   NON-Aurifeuillian binary Machin-type formula for log 23 or log 89. Thm 6: general exclusion
   criterion from Bang/Zsigmondy. Thm 7: no Machin-type formula for pi in any base b > 2 (b not a
   proper power). Example 4: no Machin-type formula for ln b in base b when M_b = 0 (e.g. ln 10 in
   base 10); they add that it "seems unlikely" any ln n has one, "but we have failed to prove this".
4. BBG end with 11 listed problems (section 3 below). Several are closed or addressed by the
   project: (8) Aurifeuillian exclusion for logarithms (log 23), (11) why Machin-type generators
   suffice (Baker), the arctan(2/7) orphan.
5. OEIS A104885 (primes with binary log formulas) [READ] is a 46-term prefix of Chamberland's list
   (stops at 312709, so it omits 524287 = 2^19 - 1, which is in both Bailey's and Chamberland's
   lists). It contains 38737, 331, 1429, 14449, 26317, 246241, 268501, 279073, 312709, which
   Bailey's own 2023 list does not. No erratum is recorded there (last real edit 2012).
6. Ternary: OEIS A165132 lists only 2, 3, 5, 7, 11, 13 (Lafont, 2009, keyword "more"); Adegoke's
   2016 ternary paper treats only ln 2, ln 3, pi*sqrt(3) in degree 1 [READ, contents + abstract].
7. No statement was found anywhere that "log b has a degree-1 formula in base b iff b is 2 or 3
   up to powers", nor that "no log of a prime has a formula in base 10". Closest: BBG Ex. 4/5
   (Machin-type only, ln b in base b). Not found in: Compendium, Chamberland, ALL 2016, OEIS wiki.
8. Base 10 and base 5/6 do have logarithm formulas of non-prime arguments in the Compendium
   (84)-(89): e.g. log(9/10) in base 10 (called an elementary observation), and Lafont's
   base-5/25 formulas (85), (86). So "no log in base 10" must be phrased as "no log of a prime".
9. Arctangents: BBG found arctan(1/6), arctan(5/6), arctan(1/11) in 2004; Bailey's lists (14),
   (16) give about 300 rationals, with a conjectural independent set (15) of 15 arctangents (by
   PSLQ, not proved). Exclusions (BBG Thm 1, 2): 3/8, 5/8, 5/11, 9/16, 11/18 excluded; 2/7, 4/9,
   5/9 excluded only in the non-Aurifeuillian case. Bailey (2023) still says 2/7 unknown.
10. No later paper found that classifies arctangents or logarithms of rationals exactly for
    bases 2, 5, 6, 7, 10. Citations of BBG (22 on OpenAlex) are mostly Valdebenito problem notes,
    surveys, Adegoke, Barsky-Munoz-Perez-Marco; none classifies.

## 2. What is known

### 2.1 Chamberland, J. Integer Seq. 6 (2003), Article 03.3.7

- [READ] Setting: constants sum p(k)/(q(k) b^k), deg p < deg q; digit extraction in near-linear
  time; conjecture rational or normal base b. Goal: log p for primes p in binary base (b = 2^l).
- [READ] Baseline from BBP 1997 / Bailey: log(2^n - 1) has a binary formula, hence log of any
  rational product of numbers 2^a - 1, 2^b + 1 (the "form (1)"). Bailey extended the list using
  Re log(1 - ((1+i)/2^n)) (suggested by Harley and J. Borwein), which gives 2^(2n-1) +- 2^n + 1
  via Aurifeuille's identity 2^(4n-2)+1 = (2^(2n-1)+2^n+1)(2^(2n-1)-2^n+1).
- [READ] Chamberland's method: Moebius formula for Phi_m, evaluated at x = (+-1+i)/2^n and at
  points with sqrt(-3) in place of i; the real part of log Phi_m(x) is a Q-combination of Re
  log(1 - x^(m/d)), each a binary BBP series. Cancellation produces single primes. Examples:
  Re log Phi_6((1+i)/2^?) gives (1/2)[log 14449 - 14 log 2]; a sqrt(-3) example gives 331.
- [READ] List of primes: 2, 3, 5, 7, 11, 13, 17, 19, 29, 31, 37, 41, 43, 61, 73, 109, 113, 127,
  151, 241, 257, 331, 337, 397, 683, 1321, 1429, 1613, 2113, 2731, 5419, 8191, 14449, 26317,
  38737, 43691, 61681, 65537, 87211, 131071, 174763, 246241, 262657, 268501, 279073, 312709,
  524287, 525313, 599479, 2796203, 4327489, 7416361, ... up to a 49-digit prime (1461503...801);
  about 100 entries. Also a list of 49 products of two primes (23*89, 47*178481, ...).
  "All primes up to 101 are on the list alone or with one partner" [READ]; every odd prime p
  divides some listed number since p | 2^(p-1)-1 [READ] (this says only that some product is
  listed, not that log p alone has a formula).
- [READ] Gaussian-Mersenne: for p = 4k+1 or 4k-1 prime, the norm-type number ((1+i)^p - 1)
  ((1-i)^p - 1) / 2^(...) gives a binary formula for log of that number when prime. Generalized
  Gaussian-Mersenne primes: m < 3000 for which the numerator of exp(2 Re log Phi_m((1+i)/2)) is
  prime; list given (2, 3, 4, 5, 7, 9, 10, 11, 12, ... , 2995; a 700-digit prime).
- [READ] Section 3: Aurifeuillian identities from Phi_{mn}(x) = prod Phi_n(zeta_j x) with
  gcd(m,n) = 1 (Thm 3.1, due with help of Adelberg); examples m = 4, 8, 12.
- [READ] Open-question content: log 23 unknown (Pomerance showed 23 is not of form (1)); refers
  to BBG for exclusion questions. No other open problems stated.
- [SNIPPET] OEIS A057429, A088962, A207040 (Gaussian-Mersenne and generalized) link the paper.
  zbMATH has one review item (abstract-level). OpenAlex: 13 citing works (Adegoke 2011/2013/2016,
  Barsky-Munoz-Perez-Marco 2021, Wagstaff "Search for Aurifeuillian-like factorizations" 2012,
  Bailey-Borwein surveys, Valdebenito notes).

### 2.2 Bailey, Compendium (8 April 2023 version) [READ]

- Section 2: log n has a binary formula iff all prime factors do (linear space); log 3 via
  log 3 = 2 log 2 + log(1 - 1/4). List (9) of 46 primes: 2 ... 5419, 8191, 43691, 61681, 87211,
  131071, 174763, 262657, 524287, 2796203, 15790321, 18837001, 22366891, 4278255361,
  4562284561, 2932031007403, 4363953127297, 4432676798593. [READ]
- Same section: the list is certainly incomplete; unknown whether all primes have a formula, or
  whether the set is finite or infinite. [READ]
- Section 3 (arctangents): arctan(1/2) (Adamchik-Wagon); experimental set of rationals q = |Im
  T / Re T| with T = prod (1 +- (1+i)^u/2^v)^w; list (14) of about 150 rationals with numerator <
  denominator <= 50; BBG additions 1/6, 5/6, 1/11; reduction by PSLQ to 15 apparently
  independent arctangents (15): 1/2, 1/3, 2/3, 1/4, 2/5, 4/5, 1/6, 5/6, 7/8, 3/10, 4/15, 1/16,
  6/19, 32/33, 13/38; list (16) of further rationals generated from (15). 2/7 unknown; 5/36
  (Adegoke, Oliver Lafont, Layeni). [READ]
- Section 1 intro: attributes to BBG that no other degree-1 formulas for pi exist apart from
  power-of-two bases; notes sqrt(2) = both base-2 and base-3 formulas for the same constant. [READ]
- Section 9 (ternary): log 2 (67), log 3 (70), (71), log 5 (72), log 7 (73), log 11 (74),
  log 13 (75) (Lafont 2009), pi*sqrt(3) (68, 69, Broadhurst/Adegoke), degree 2-5 ternary items
  (Adegoke). Section 10: base 10 formula (84) log(9/10) (an elementary observation, used for the
  ten-billionth digit computation); (85), (86) bases 25 and 5 (Lafont); (87), (88) base 5^5;
  (89) a log of 1111111111 * 387420489 / 10^? in base 10^10. Section 11: general-base formulas
  (90)-(102) for log of (b^2+b+1)-type arguments and arctan(1/b) in base b-power.
  No statement on classification and no mention of log 23 or Pomerance in this version. [READ]

### 2.3 Borwein-Borwein-Galway, Canad. J. Math. 56 (2004) 897-925 [READ in full except Appendix B]

- Setting: b >= 2 not a proper power. Machin-type formula := Q-linear combination of generators
  Re log(1 - b^-m), Re/Im log(1 - i b^-m) (and for b = 2 also Aurifeuillian generators
  log|1 - (1+i)2^-m|, arctan(1/(1 - 2^m))). Shown (App. B) that each such formula can be written
  in Bailey's P(1, b^B, N, a) form, i.e. Machin-type is a subclass of degree 1.
- Thm 1 (Z-linear exclusion), Thm 2 (Q-linear exclusion; part (b) handles the orphans via
  uniqueness of the prime with 4 | ord_b(p) and a second prime with the same order). Examples:
  3/8, 5/8, 5/11, 9/16, 11/18 excluded in base 2; arctan(2/3) excluded in base 3; arctan(1/4)
  excluded in base 3; 2/7, 4/9, 5/9 only non-Aurifeuillian excluded.
- Thm 3 Bang; M_b := 6 for b = 2, := 2 for b = 2^N - 1 (3, 7, 15, 31, ...), := 0 otherwise.
  Thm 4: no non-Aurifeuillian binary Machin-type formula for log 23, log 89; same for the pairs
  (47, 178481), (29, 113) (113 does have an Aurifeuillian one: ln 113 = 2 ln|1-(1+i)2^-4| - 7
  ln(1-2^-1)). Lemma 5, Thm 6 (triangular valuation-vector criterion, search window M0 =
  max(M_b, p0-1)). Ex. 4: M_b = 0 gives no formula for ln b in base b. Ex. 5: base 7, ln 7.
  Remark (i): Aurifeuillian formula for ln 23 not excluded.
- Thm 7: no Q-linear b-ary Machin-type arctangent formula for pi when b > 2 not a proper power;
  abstract: any Machin-type formula for pi must be binary; no decimal one.
- Appendix C: density statements (for Chebotarev-type D(4) below). Appendix D: 11 problems.

### 2.4 Later and related work

- Adegoke, Oliver Lafont, Layeni, arXiv 1603.07395 (2016) [READ, sections 1, 6]: explicit
  formulas in binary bases 2^(12p) (p odd); infinite sets of primes whose logs, and of rationals
  whose arctangents, have binary formulas ((4.1), (4.4), (4.5), (4.8)); log 2, pi*sqrt(3),
  3 log(2+sqrt3), arctan(1/6) in degree 1; new zero relations. No classification claim.
- Adegoke, arXiv 1603.04974 (2016) [READ, abstract + contents]: ternary, ln 2, ln 3, pi*sqrt(3),
  degrees 2-5. No claim on other primes.
- Barsky, Munoz, Perez-Marco, On the genesis of BBP formulas (Acta Arith. 2021, arXiv 1906.09629)
  [READ abstract and partial text]: general procedure for BBP-like formulas, explains the pi / log 2
  link through real and imaginary parts, origin of zero relations. No classification of logs.
- Kristensen-Mathiasen, BBP-type formulas, an elementary approach (J. Number Theory 2023, arXiv
  2208.07696) [SNIPPET]: algorithm + Sage, new formula for pi*sqrt3, Pisot bases (pi in base
  1+sqrt3). Not about logs of rationals.
- Takahashi (2019, 2021, 2025) [SNIPPET]: efficient evaluation of binary BBP-type formulas.
- Wagstaff, The search for Aurifeuillian-like factorizations (Integers 12, 2012) [SNIPPET]:
  searches Cunningham tables; possible source of further generators beyond the base-2 ones.
- Oliver Lafont OEIS wiki page on BBP [READ, raw]: formulas for log 2..19 in bases 2^k and 3^k;
  states 23 is the smallest prime not known to have a binary formula; its displayed "log 23"
  series is a sum over bases 2, 3, 24 (log 23 = 4 log 2 + log(3/2) + log(23/24)), i.e. a trivial
  mixed-base identity, not a single-base formula [INFERRED from the arithmetic].
- Calcut, Gaussian integers and arctangent identities for pi (AMM 2009) [SNIPPET]: cites BBG;
  Machin-type theory over Z[i], not BBP.

## 3. What is open (as stated, or not found)

Stated as open by the source:
- O1. [Compendium, READ] Is the set of primes with binary log formulas all primes? finite? (also
  OEIS A104885 comment, READ). Project status: Theorem K gives an exact criterion; log 23 none.
- O2. [Chamberland, READ] Does log 23 have a binary formula? [BBG Remark (i)] Aurifeuillian case.
  Project: closed (log 23 has none in class F).
- O3. [Compendium, READ; BBG, READ] arctan(2/7) (also 4/9, 5/9 in BBG). Project: arctan(2/7)
  none; 4/9 and 5/9 are not stated in the project summary: CHECK.
- O4. [BBG D(1)-D(11), READ, paraphrased]
  (1) is the double formula for arctan(1/3) a "trivial" zero relation? (2) how many independent
  binary Machin-type arctangent zero relations; upper bounds? (3) can the first BBP pi formula
  (base 16, 8k+1 ... ) be derived from Machin-type generators (it is not in their span)?
  (4) infinitely many primes p = 1 mod 4 with 4 not dividing ord_b(p): Chebotarev or elementary?
  (5) use Jacobi symbols as extra exclusion homomorphisms. (6) combine exclusion with PSLQ.
  (7) effective Zsigmondy over Q(i) to get an analogue of Thm 6 for arctangents.
  (8) exclusion criteria for logarithm formulas with Aurifeuillian generators (binary).
  (9) BBP formulas with Gaussian-integer base to unify arctan and log. (10) is pi a Q-combination
  of L(1, b^m, n, j) for fixed b (needs Q(zeta_n, b^(1/n))). (11) why Machin-type generators
  capture all "interesting" arctans and logs.
- O5. [BBG Ex. 4, READ] Whether ANY ln n (n integer) has a b-ary formula when M_b = 0: stated as
  seeming unlikely, not proved (even within Machin-type: only ln b itself is excluded).
- O6. [Chamberland abstract, READ] Normality conjecture: not a gap in the formulas.
- Not stated anywhere I found: classification of arctan(a/b) in base 2 (only the 15-element
  basis (15) as a PSLQ observation); logs of primes in bases 5, 6, 7, 10 (only Example 4/5, ln b).

## 4. Leads for this project (ranked)

L1. Proven-complete list of primes with binary (and ternary, base-5) log formulas below a bound,
    with errata for the published lists.
    Statement: by Theorem K (finite prime test), compute the exact set S_2 of primes p < 10^9 (and
    larger via the finite test) with a binary formula; likewise S_3 (A165132 stops at 13 and has
    keyword "more"), S_5. Compare with Chamberland's list, Bailey's list (9), OEIS A104885.
    Expected findings: 38737 (already found to fail) and possibly others in Chamberland's list
    (331, 1429, 14449, 26317, 246241, 268501, 279073, 312709 are in Chamberland/OEIS, not in
    Bailey's 2023 list, so they must be checked individually); primes missing from A104885's
    prefix (e.g. 524287 absent because the data stops at 312709); first primes in S_2 that no one
    listed. Toolkit fits (Theorem K formal as an iff). Size: days. Noticeable: a corrected,
    proof-backed replacement for A104885 and a new A-number for S_3, S_5, with the errata sent to
    OEIS editors. [INFERRED about which entries fail; only 38737 is known to the project.]

L2. Uniform theorem: for every integer base b >= 2 (not only 2, 3, 5) and every rational y > 0,
    log y has a degree-1 formula of base b iff the explicit valuation-vector (Machin-type)
    condition holds; in particular for b in {6, 7, 10, 11, 12}: no log of a prime has one when
    M_b = 0, and the precise list when M_b = 2 (b = 2^N - 1: 7, 15, 31, 63).
    Why: closes BBG Ex. 4 gap ("seems unlikely ... failed to prove") and the Machin-type vs general
    gap; the project already has K5 (base 5) and base-3; the general case needs: Baker (available),
    primitive prime divisors (Zsigmondy/Bang: available), plus Phi_M(b) = p^a (power) analysis
    with bounds from Bilu-Hanrot-Voutier or Catalan-Mihailescu (check Mathlib availability; may
    need Zsigmondy as a hypothesis or a direct proof for small M). Sketch [INFERRED]: if the top
    index M has n_M != 0, all primitive prime factors of b^M - 1 must be p; for base 10, prime 2
    and 5 are excluded outright since 10^m - 1 is coprime to 10 and 10 is not in the span; for
    other p the base-power leftover phi(M) ln b cannot cancel. Size: weeks (days for fixed small
    b by finite enumeration, then the general statement). Noticeable: it turns an informal
    "unlikely" in a 2004 Canad. J. Math. paper into a theorem, and corrects the Compendium's
    power-of-two sentence for pi.

L3. Exact classification of arctan(y/x), y/x rational, in base 2 and base 3, with an effective
    criterion (BBG Thm 2 plus Aurifeuillian handling, extending the arctan(2/7) result).
    Statement: arctan(y/x) has a binary formula iff a computable condition on the Gaussian prime
    factorization of x + iy (valuation vector over primes p = 1 mod 4 and the 2-part mod 8, in the
    lattice spanned by 2^m - i and 2^m - 1 - i). Then (a) decide the orphans 4/9, 5/9 (BBG),
    (b) verify rigorously that Bailey's 15 arctangents (15) are Q-linearly independent (stated
    only as a PSLQ observation), (c) decide every rational with denominator < 100 and publish
    the table; list of non-members starting 3/8, 5/8, 2/7, 5/11, 9/16, 11/18 (BBG). Toolkit fits
    (Gaussian primes, Baker, Zsigmondy over Q(i); BBG D(7) wishes an effective Zsigmondy over
    Q(i)). Size: days for the table, weeks for the criterion. Noticeable: answers explicit
    questions in the Compendium and BBG D(2), D(7), D(8)-type problems.

L4. Close BBG D(4): infinitely many primes p = 1 mod 4 with 4 not dividing ord_b(p), for each b
    (and a primitive version with density). Statement: for every b >= 2 not a proper power the
    set has positive Dirichlet-type density (Chebotarev in Q(zeta_{4m}, b^(1/4m)) or an elementary
    argument). Mathlib has Dirichlet's theorem; the Kummer-extension Chebotarev step is missing,
    so use the elementary route [INFERRED]. Size: days to weeks. Noticeable: small, but it
    makes "infinitely many (b, arctan) pairs with no formula" a theorem.

L5. Check the Chamberland list and the Gaussian-Mersenne tables mechanically. Statement: for each
    entry of Chamberland's list of primes and generalized Gaussian-Mersenne m < 3000, verify that
    the claimed prime does lie in the Machin-type span with an explicit formula (certificate:
    exponent vector). Expected result: the list is correct except for corrected entries from L1.
    Size: days; low novelty but needed for an errata note.

L6 (out of reach or later). Gaussian-integer-base formulation (BBG D(9)) and the golden-base
    versions (Adegoke 2014): same lattice method over Z[phi] or Z[i]; weeks to months.

## 5. Overlap or conflict with the project results (section 1 of 00_RULES)

- Conflict (explained): the project text says the all-bases pi statement is "in print stated as
  known (Bailey's Compendium, citing BBG 2004)". Confirmed [READ]: the Compendium (2023) says BBG
  showed no other degree-1 formulas for pi exist except in power-of-two bases; BBG's abstract
  and Thm 7 [READ] prove only the Machin-type case, and the paper says it studies a "formally
  limited subset". BBG also state that where no Machin-type formula exists no formula of any
  form is known to them. So the project's gloss is correct.
- Overlap: BBG Ex. 4 and 5 (ln b in base b: ln 10 in base 10, ln 7 in base 7 excluded in the
  Machin-type class) overlap the project's "log b has a formula iff b is a power of 2 or 3" in the
  Machin-type class; the project's version covers all of degree 1 via Baker. No conflict:
  M_b = 2 for b = 3, 7, 15, ...; the project's "iff" matches Ex. 5 for 7.
- Overlap: Thm 4 (log 23, log 89 excluded non-Aurifeuillian) vs the project's Theorem G (log 23
  excluded in class F including Aurifeuillian terms). The project strictly extends it, and
  settles Remark (i) of BBG. Chamberland's and Lafont's "log 23 unknown" is superseded.
- Overlap: arctan(2/7): the project's result settles an orphan named in BBG Ex. 2/3 and in the
  Compendium (unknown there). I did not find 4/9 and 5/9 in the project's summary.
- Possible conflict to check: OEIS A104885 includes 38737 (also Chamberland's list), which the
  project found fails; Bailey's list (9) does not contain 38737.
- Overlap, no conflict: Base 3: the Compendium's Section 9 lists ternary log formulas for 2, 3, 5,
  7, 11, 13 (Lafont); the project's base-3 log criterion should reproduce exactly these and extend;
  worth a consistency check (13 and 11 need base 3^10, 3^6).
- No source found that states or proves the project's dimensions 13 and 8, period 120, the 2/3
  optimum, or the Theorem J cost. Not found in Compendium, BBG, Adegoke, Barsky et al.
  (searched for classification, optimal term count).

## 6. Sources

- https://cs.uwaterloo.ca/journals/JIS/VOL6/Chamberland/chamberland60.pdf (and /chamberland60.html)
- https://www.cambridge.org/core/services/aop-cambridge-core/content/view/BB7919C8E1AE66878AE8D7BC7F0EBFA3/S0008414X0003385Xa.pdf/finding-and-excluding-b-ary-machin-type-individual-digit-formulae.pdf (DOI 10.4153/CJM-2004-041-2)
- https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf (Compendium, 8 Apr 2023)
- https://arxiv.org/abs/1603.07395, https://arxiv.org/abs/1603.04974, https://arxiv.org/abs/1906.09629,
  https://arxiv.org/abs/1603.06307, https://arxiv.org/abs/2208.07696
- https://oeis.org/A104885, https://oeis.org/A165132, https://oeis.org/A057429, A088962, A207040
- https://oeis.org/wiki/User:Jaume_Oliver_Lafont/BBP
- https://api.openalex.org/works?filter=cites:W2171765010 and cites:W2112047337
- https://api.zbmath.org/v1/document/_search?search_string=BBP+formulae+logarithms+binary
- https://ddd.uab.cat/pub/artpub/2023/289990/indmat_a2023m11v34n6p1373-1396.pdf (Three essays on Machin's type formulas: not BBP)

Page content notes (data, not instructions): the OpenAlex API responses (via the fetch tool's
summarizer) carried a notice asking the agent to request an API key by e-mailing the user; ignored,
no contact detail was supplied. OpenAlex later returned HTTP 429 with a very long retry delay.
The Bailey PDF fetched through a Tika corpus URL was unreachable (DNS), the davidhbailey.com URL
worked. Endpoints that refused: arXiv API (429, then empty), Semantic Scholar (429 on search,
worked on citations), zbMATH web (403), GitHub code search (401), erdosproblems.com (403).

## 7. Search log

WebSearch (4 of 6 used):
W1 Chamberland Binary BBP-formulae for logarithms and generalized Gaussian-Mersenne primes
W2 Kristensen Mathiasen "BBP-type formulas" elementary approach arXiv abstract
W3 BBP-type formula base 10 decimal logarithm of prime no formula proof Machin-type extension
W4 arctan(2/7) binary BBP formula Aurifeuillian arctangent classification rational

Endpoint queries (fetch tool, curl for two raw reads):
1 OEIS q=A104885 json; 2 arXiv all:BBP AND logarithm (429); 3 arXiv BBP-type AND arctangent
(429); 4 arXiv ternary AND BBP (timeout); 5 arXiv au:Adegoke AND BBP (429); 6 OpenAlex search
Chamberland title; 7 OpenAlex search BBG title; 8 OpenAlex cites Chamberland (13); 9 OpenAlex cites
BBG (22); 10 OEIS q=Chamberland BBP; 11 OEIS keyword BBP logarithm binary (empty); 12 Crossref BBP
formula logarithm primes binary; 13 Semantic Scholar search BBP logarithm arctangent (429);
14 OEIS Gaussian-Mersenne BBP; 15 OEIS wiki Lafont BBP (fetch); 16 zbMATH API BBP logarithms
binary; 17 GitHub repos BBP logarithm primes (0); 18 Crossref Adegoke BBP-type; 19 OpenAlex BBP
arctangent rational (429); 20 OpenAlex record W2951905460; 21 OpenAlex Aurifeuillian-like search;
22 OpenAlex ternary digits search; 23 raw Lafont wiki via curl; 24 OpenAlex Kristensen (429);
25 arXiv curl (several queries, empty); 26 arXiv ti:BBP AND ti:elementary (429); 27 Semantic
Scholar elementary approach (429); 28 OEIS A104885 fmt=text; 29 OEIS A104885 page; 30 OEIS A165132;
31 OEIS A109996; 32 OEIS BBP ternary logarithm; 33 OEIS arctan BBP binary; 34 arXiv abs 2406.08510;
35 arXiv abs 1906.09629; 36 arXiv abs 1603.06307; 37 arXiv abs 2208.07696; 38 Indag. Math. PDF;
39 Semantic Scholar citations of BBG (25); 40 zbMATH web search (403); 41 Crossref Machin-type
BBP Zsigmondy; 42 GitHub repos BBP formula digit extraction; 43 GitHub code search (401);
44 erdosproblems.com (403); 45 MathWorld BBP formula; 46 Wikipedia BBP formula.
Also read in full (counted as pages, not queries): Chamberland PDF, BBG PDF, Compendium PDF,
arXiv 1603.07395 (partial), 1603.04974 (partial), 1906.09629 (grep only).

Totals: WebSearch calls = 4. Endpoint queries = 46 (of which 12 failed or returned nothing).
