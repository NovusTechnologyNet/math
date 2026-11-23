# Vanishing, transcendence and independence of sums f(n) x^n / n (periodic f)

Tags: [READ] = read in the source text/page image myself; [SNIPPET] = search-result snippet/abstract only; [INFERRED] = my deduction.

## 0. Bottom line

- The only place where a theorem covers sum alpha^n P(n)/Q(n) with algebraic alpha (so it includes |x|<1, x algebraic) is ASST 2001, Theorem 4 / Cor. 4.1 (as restated in Tijdeman's survey). It gives "S rational, or transcendental" and, for zeros in [-1,0), "S = 0 or transcendental". It does NOT classify when S = 0 for alpha != 1. [READ, via survey]
- A complete classification of the zero case exists only for x = 1 (L(1,f) = sum f(n)/n): Baker-Birch-Wirsing (1973) and Okada (1982), under the hypothesis that the cyclotomic polynomial Phi_q is irreducible over Q(f(1..q)). [READ, via Yuan-Li 2009 and Tijdeman]
- I found no source that classifies vanishing sums for x = 1/b or 1/sqrt(b), nor one stating "vanishes only for f = 0 when b >= 3". The zero relations in Bailey's compendium are said to be not understood. [READ]
- The statement "degree-1 BBP formula for pi exists only in power-of-2 bases" is attributed to Borwein-Borwein-Galway by Bailey's compendium, but BBG's own theorem is only for Machin-type formulas (sums of a_m arctan(-b^-m)). [READ both]

## 1. ASST 2001, "Transcendental infinite sums", Indag. Math. 12 (2001) 1-14

URL (bibliographic record only): https://repository.ias.ac.in/67731 . Full text NOT obtained [SNIPPET]. The statements below come from Tijdeman's survey, which quotes it.

Source read: R. Tijdeman, "On irrationality and transcendency of infinite sums of rational numbers", https://pub.math.leidenuniv.nl/~tijdemanr//tijsho3.pdf (read in full text and page image).

Theorem 1 of the survey = [AdSST] Theorem 4 and Corollary 4.1 [READ]: Let P in Qbar[x], alpha in Qbar, Q in Q[x] having only simple rational zeros. If S = sum_{n>=1} alpha^n P(n)/Q(n) converges, then S is rational or S is not algebraic (so transcendental). If moreover all zeros of Q lie in [-1,0), then S = 0 or S is transcendental.

Method [READ]: partial fractions, then (for alpha = 1) a Lehmer-type identity (their Lemma 5) turning the sum into sum_j c_j (1 - zeta^j) log(1 - zeta^j)-type terms; for alpha != 1 "a slightly more complicated formula" (proof of Theorem 4); then Baker's theorem: a Qbar-linear form in logarithms of algebraic numbers is 0 or transcendental. Tijdeman notes the theorem was also proved for P an exponential polynomial and with approximation measures when S is transcendental.

Relation to f(n) x^n / n [INFERRED]: f periodic mod q with algebraic values is a combination of zeta^{jn}, so S = -sum_j c_j log(1 - zeta^j x), a Qbar-linear form in logs. Baker then gives "0 or transcendental" directly for algebraic x, |x|<1. Whether ASST state exactly this form I could not confirm. The step "0 or transcendental" is the content; the vanishing case is left open by Baker.

Vanishing examples/conditions in ASST: not seen in the original. The survey gives these vanishing examples, all for alpha = 1 (x = 1): [READ]
- sum (16n^2+12n-1)/((4n+1)(4n+2)(4n+3)(4n+4)) = 0, a genuine vanishing sum with period 4, explained there by the linear form -log(1-i)+log(1-(-1))-log(1+i) = 0.
- sum (-1)^n (18n^2+15n+1)/((3n+1)(3n+2)(3n+3)) = 0.
- The survey remarks that in the [AdSST] setting S rational for degree >= 3 can happen non-obviously, and that sums with only "same residue class mod q" poles are rational by telescoping.
Hypothesis note: the "S = 0 or transcendental" clause needs zeros in [-1,0). For f(n)/n the denominator is n itself, so the reduction to this form is through Tijdeman's "reduction procedure" (see Yuan-Li below).

## 2. Follow-ups

### 2a. Baker-Birch-Wirsing 1973, "On a problem of Chowla" (x = 1)
Not read in the original. Described in Yuan-Li (arXiv 0909.2387, https://arxiv.org/pdf/0909.2387, [READ]): for f rational-valued, nonzero, period q, S = sum f(n)/n = 0 is impossible when (i) f(r) = 0 whenever 1 < gcd(r,q) < q, and (ii) Phi_q is irreducible over Q(f(1),...,f(q)). They also showed the result fails if (i) or (ii) is dropped (stated by Yuan-Li, [READ] second hand). Only x = 1.

### 2b. Okada 1982, Acta Arith. 40 (x = 1)
Described in Yuan-Li, Theorem A [READ, second hand]: if Phi_q is irreducible over Q(f(1..q)), then sum f(n)/n = 0 iff two explicit linear conditions on f hold (a condition for every a coprime to q involving f(a), f(r)A(r,a), f(q); and one for every prime p | q). Proof uses linear independence of logs of algebraic numbers and L(1,chi) != 0. This is a full classification of zero relations, but only for x = 1. Saradha-Tijdeman 2003 restate it as a "Decomposition Lemma" (S = 0 iff sums of f(am), m over integers composed of primes of q, vanish for each a coprime to q, plus a prime-wise condition); Lemma 2.2 there: S = 0 implies sum f(kn)/n = 0 for every k coprime to q. [READ, via Yuan-Li]
Murty-Pathak ("The Okada space and vanishing of L(1,f)") give a basis of the Q-space of rational periodic f with L(1,f)=0 [SNIPPET]: https://www.cmi.ac.in/~siddhi/Okada_space_RM_SP_Final.pdf

### 2c. Saradha-Tijdeman, J. London Math. Soc. 67 (2003) 580-592
Full text not obtained [SNIPPET]; described in Tijdeman survey and Yuan-Li [READ, second hand]. Sums sum (alpha n + beta)/((qn+s1)(qn+s2)(qn+s3)) (and alternating versions): transcendental unless a rational-reason (same residue class, or cancelling factor) applies. Only x = 1 or x = -1 (alternating). No |x|<1.

### 2d. Yuan-Li 2009 (arXiv 0909.2387)
[READ] Extends to deg Q = 4 for x = 1; finds exactly two exceptional vanishing families (period 4: (4n+1)..(4n+4) numerator 16n^2+12n-1; period 6: numerator 36n^2+36n-1 over (6n+1)(6n+2)(6n+4)(6n+5)).

### 2e. Murty-Saradha, "Transcendental values of the digamma function", J. Number Theory 125 (2007) 298-318
[SNIPPET only.] Concerns psi(a/q) + gamma, Baker periods; at most one of phi(n)+1 numbers is algebraic. Not about x^n/n with |x|<1. URL: https://mast.queensu.ca/~murty/murty-saradha.pdf (could not fetch; redirected).

### 2f. Murty-Weatherby, Int. J. Number Theory 7(2) (2011) 323-339, and Weatherby thesis
[SNIPPET only.] Sums over Z of A(n)/B(n) (two-sided), links to Gel'fond-Schneider type conjectures; Baker used for the unconditional parts. Not about x^n/n with |x|<1. Thesis: https://queensu.scholaris.ca/items/8a73d833-e2cb-48d9-affa-98a7a9871bdf . PDF at https://mast.queensu.ca/~murty/Murty-Weatherby-Series.pdf redirected, not read.

### 2g. Tijdeman survey, other content [READ]
Conjecture: a sum of a rational function value, if algebraic, is rational. Also E-function statement ([FN] Cor. 2.4): for non-trivial periodic algebraic c_n, sum c_n z^n / n! is transcendental at nonzero algebraic z (different series: n! not n).

## 3. Specific x (1/2, 1/sqrt2, 1/3, ...) and BBP literature

- No source found classifying vanishing sums for any specific x != 1 and no statement that for x = 1/b, b >= 3 only f = 0 vanishes. [Searched; not found.]
- Bailey, "A Compendium of BBP-Type Formulas", section 12 "Zero relations" [READ], https://www.davidhbailey.com//dhbpapers/bbp-formulas.pdf : lists degree-s BBP formulas evaluating to zero, found by PSLQ; counts in a table by (s, b, n) (examples with b = 2^12, 2^20 ...). It says these are "somewhat mysterious": it is not understood why zero relations occur for certain s, b, n and not others (paraphrase); most listed bases are powers of 2 ("all except the last two are binary"). Mentions a discussion in its ref. [21].
- Lafont, "Degree 1 BBP-Type Zero Relations" [SNIPPET via slideshare summary]: https://www.slideshare.net/slideshow/zero-relations/13076965 . Claims proofs of the 8 previously unproved degree-1 binary zero relations in the compendium (5 of length 24 in base 2^12, 3 of length 40 in base 2^20), by Fourier analysis of the coefficient vectors; no classification, no Baker, no other bases. Bailey's compendium (ref. [30]) cites it as a manuscript [READ].
- Bailey-Crandall (2001), Lagarias (2001), Chamberland, Huvent: not opened. No claim made.
- Kristensen-Mathiasen, arXiv 2208.07696 (https://arxiv.org/pdf/2208.07696): calls null formulas mysterious [SNIPPET only].
- Adegoke-Lafont (JIS 26, https://cs.uwaterloo.ca/journals/JIS/VOL26/Adegoke/ade7.pdf): cites Bailey-Crandall for base-alpha zero relations [SNIPPET only].

## 4. "Pi has a degree-1 BBP formula only in power-of-2 bases"

- Bailey's compendium [READ]: says BBG 2004 "showed that there are no other degree-1 BBP-type for pi, except those whose 'base' is a power of two", and notes that for pi^2 there is a base-2 formula (No. 29) and a base-3 formula (No. 76).
- BBG itself, Canad. J. Math. 56 (2004) 897-925, https://www.cambridge.org/core/services/aop-cambridge-core/content/view/BB7919C8E1AE66878AE8D7BC7F0EBFA3/S0008414X0003385Xa.pdf/finding-and-excluding-b-ary-machin-type-individual-digit-formulae.pdf [READ]. Abstract: for b > 2 not a proper power, a b-ary Machin-type BBP arctangent formula for pi is pi = sum a_m arctan(-b^-m), a_m rational (for b = 2 also terms arctan(1/(1-2^m))). Theorem 7: no such formula for pi when b > 2, b not a proper power. Proof by Bang-Zsigmondy primitive prime factors of b^{4M}-1, not by Baker. Closing remarks: the original BBP pi formula (8k+1 etc., base 16) is NOT a Q-combination of Machin-type generators, so the theorem does not cover it; they note that no BBP formula of any form is known for a constant lacking a Machin-type one. Exclusion criteria (their Theorems 1, 2, 4, 6) are also Bang/p-adic order based. Proper powers of b are handled by rewriting base b^m as base b.
- So the precise class proved is: Q-linear combinations of arctan(-b^-m) (m >= 1), b > 2 not a proper power. The wider claim (all degree-1 BBP with rational coefficients, i.e. all sum p(k)/q(k) b^-k with q(k) of degree 1 in k and periodic numerators) is NOT proved in BBG; the compendium's phrasing is a paraphrase going beyond the theorem. [INFERRED from reading both]
- Note [INFERRED]: general degree-1 formula = Q-combination of log(1 - zeta b^{-1/n}...)-type terms; excluding pi there requires showing no combination of arctan/log of Q(zeta_n, b^{1/n}) values equals pi. That is a linear-forms-in-logs problem where Baker gives transcendence of nonzero forms but not rational independence/zero-ness. That is exactly the gap.

## 5. Left open (as far as found)

1. Classification of f != 0 with sum f(n) x^n / n = 0 for any algebraic x != 1, |x| < 1: no theorem found. Baker gives only "0 or transcendental".
2. Linear independence over Q of such sums for varying f: only Baker's theorem (Q-bar linear forms in logs, which needs Q-bar-linear independence of logs, i.e. the nonzero-ness of a form) and the x = 1 Okada/Murty-Pathak structure; nothing found for x = 1/b.
3. Any proof that pi lacks degree-1 BBP formulas in non-power-of-2 bases outside Machin-type.
