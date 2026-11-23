# Q01: primitive prime divisors, over Q and over number fields

Helper report, 2026-11-22. Marks: [READ] read on the source's own page/PDF (or a PDF I
converted to text); [SNIPPET] seen only in a search result, API record or abstract;
[INFERRED] my own conclusion.

## 1. Summary

1. The classical statements are firm: Zsigmondy's theorem has exactly three exceptions
   (n=1 with a-b=1; n=2 with a+b a power of 2; a=2,b=1,n=6) [READ, Wikipedia]. Bilu-Hanrot-
   Voutier (BHV 2001) give the complete answer for Lucas/Lehmer numbers: primitive divisor
   for all n >= 31, with the finite list of defective pairs for n <= 30, made exhaustive by
   Abouzaid 2008 [SNIPPET: Crossref/Wikipedia/Cera da Conceicao intro].
2. The number-field generalization is Postnikova-Schinzel 1968 (I READ the whole paper) and
   Schinzel 1974 (J. reine angew. Math. 268/269, pp. 27-33; I could NOT read it, only the
   record and what later papers quote from it). Both are effective ("n0 computable"); the
   1974 paper makes the bound depend only on the degree d = [Q(A/B):Q], with a threshold of
   the shape 2(2^d - 1) when quoted in a 2024 arXiv paper (the superscript was lost in the
   text extraction, so the exact shape is uncertain).
3. The project's statement (sqrt(b) - r, all r with r^4 != 1, b >= 5) is NOT, as far as I can
   find, a printed theorem and is not an immediate corollary of any printed one. It is
   close to "a primitive divisor of alpha^m - 1 for alpha = sqrt(b)", but (a) it asks for a
   prime of the big field Q(sqrt b, zeta_m) containing the specific element sqrt(b) - r,
   i.e. Galois-uniform in r, and (b) it has no small-m exceptions except m in {1,2,4}. The
   nearest printed result is Schinzel 1993 (A^n - zeta_k B^n), which fixes the order k of
   zeta and lets n grow: the opposite regime. [INFERRED]
4. Borwein-Borwein-Galway 2004, open question (7), says explicitly that the number-field
   Zsigmondy theorems (they cite Schinzel 1974 and BHV 2001) "should give" an effective
   version for Q[i] [READ]. I found no paper that carries this out under that name.
   [INFERRED] It follows quickly from BHV: for the Machin case A = b+i, B = b-i the pair is
   a Lehmer pair (after dividing by 1+i when b is odd), so BHV (all n >= 31, finite list of
   defective n <= 30) applies directly. Worth a short note (lead 1).
5. Formalization (as of 2026-11-22): Mathlib does NOT have Zsigmondy; the 1000+ theorems
   list has the entry with no declaration [READ]; the Lean 4 Mathlib PR 28895 was closed
   unmerged on 2026-09-18 (author deleted head repo) [READ]. The Tau Ceti library (Lean,
   downstream of Mathlib) merged "prove the Bang-Zsigmondy theorem and its order corollaries"
   (PR 39611) on 2026-11-15 [READ], seven days ago. No Isabelle AFP or Coq/Rocq entry found.
6. Number-field Zsigmondy has no formalization that I found, in any system. Quadratic fields
   are the natural first case; Flatters 2008 has explicit finite tables for real quadratic
   units that could be machine-checked.
7. Overlap or conflict with the project: none found. The one thing to correct in print is
   that BBG question (7) is, in my reading, answerable from BHV (see section 5).

## 2. What is known

### 2.1 Integers

- [READ, Wikipedia] Zsigmondy (1892): for coprime integers a > b > 0 and n >= 1 there is a
  prime dividing a^n - b^n and no a^k - b^k with k < n, except: n=1, a-b=1; n=2, a+b a power
  of 2; (a,b,n)=(2,1,6). Sum form: a^n + b^n has one except 2^3+1^3. Bang (1886) is the case
  b=1 for 2^n-1 (n != 6) [Wikipedia], and the general b=1 case is the one the project uses.
- [READ, Postnikova-Schinzel bibliography] The classical references as cited there: Bang,
  Tidsskr. Math. 4 (1886) 130-132; Zsigmondy, Monatsh. Math. Phys. 3 (1892) 284-365;
  Birkhoff-Vandiver, Ann. of Math. 5 (1902-03) 173-180. (Another source gives 1904 for
  Birkhoff-Vandiver [SNIPPET]; vol. 5 of the 2nd series is 1903-04. Use "Ann. Math. (2) 5,
  1904, 173-180".)
- [SNIPPET] Carmichael, "On the numerical factors of the arithmetic forms alpha^n +- beta^n",
  Ann. of Math. 15 (1913), DOI 10.2307/1967797. I fetched the scan but it is image-only, so
  I did not read the statement. Per Cera da Conceicao (arXiv 2410.04957, intro) [READ]:
  Carmichael handled Lucas sequences U_n = (a^n - b^n)/(a-b) with gcd(P,Q)=1 and real roots
  (discriminant > 0), with threshold n0 = 13; example: Fibonacci has a primitive divisor not
  dividing the discriminant exactly for n outside {1,2,5,6,12}. (Wikipedia lists the Zsigmondy
  set of Fibonacci as {1,2,6,12}; the difference is whether the prime 5 for n=5 counts, which
  is the "primitive divisor not dividing the discriminant" convention.)
- [SNIPPET] Schinzel 1962, "On primitive prime factors of a^n - b^n", Proc. Cambridge Philos.
  Soc. 58 (1962) 556-562 (DOI 10.1017/s0305004100040561), and "On primitive prime factors of
  Lehmer numbers I, II, III" (Acta Arith. 8 (1963) 213-223, 251-257; 15 (1968) 49-70). I did
  not read them. I could not confirm from a read source the "two primitive prime factors"
  statement attributed to the 1962 paper in the task; treat that attribution as unverified.
  Also [READ] Schinzel, "The intrinsic divisors of Lehmer numbers in the case of negative
  discriminant", Ark. Mat. 4 (1962) 413-416, is the paper Postnikova-Schinzel cite for the
  Gel'fond-type lower bound.
- [SNIPPET] Voutier 1995 (Math. Comp. 64, 869-888): all Lucas/Lehmer sequences whose n-th term
  lacks a primitive divisor, n <= 30 (via Thue equations); conjectures none for n > 30.
  Voutier 1996 (J. Theor. Nombres Bordeaux 8, 251-274): all n > 30 when the height ratio is
  at most 4. BHV 2001 (J. reine angew. Math. 539, 75-122, DOI 10.1515/crll.2001.080, with an
  appendix by Mignotte): primitive divisor for all n >= 31 for every Lucas and Lehmer pair.
  Abouzaid 2008 (J. Theor. Nombres Bordeaux 18, 299-313): completes Voutier's list of
  defective terms to an exhaustive one. [SNIPPET: Crossref records; Wikipedia says the
  possible defective indices are 1,2,3,4,5,6,7,8,10,12,13,18,30.]
- [SNIPPET] Stewart 1977 ("On divisors of Fermat, Fibonacci, Lucas and Lehmer numbers",
  Proc. London Math. Soc. 35; the related Shorey-Stewart 1981, J. London Math. Soc. 23, 17-)
  gives the first effective lower bounds for the greatest prime factor of terms of binary
  recurrences, in the dependency chain behind BHV. Stewart's 2013 Acta Math. 211 paper is
  "On divisors of Lucas and Lehmer numbers". I did not read these.

### 2.2 Number fields

- [READ, whole paper] Postnikova-Schinzel 1968 (Mat. Sb. 75(117) = Math. USSR-Sb. 4(2),
  153-159; they write a,b integers of a number field K with (a),(b) coprime; a prime ideal
  P | a^n - b^n is "primitive" if P divides none of a^m - b^m, 1 <= m < n).
  * Theorem 1: if a/b is not a root of unity, there is n0(a,b), computable, such that a^n -
    b^n has a primitive prime ideal divisor for all n > n0(a,b). Proof: two lemmas (Lemma 1: a
    lifting-the-exponent statement for prime ideals; Lemma 2: a non-primitive prime ideal
    divisor of the homogeneous cyclotomic value Phi_n(a,b) divides n, and its exponent is at
    most that of n), then a lower bound for |N(Phi_n(a,b))| via Gel'fond's lower bound for
    |(a/b)^m - 1| at a prime ideal, plus Kronecker's theorem to handle the unit case.
  * Remark: they ask whether n0 depends only on K. They prove it for purely real K of
    degree l: n0 can be taken as 2^l (2^l - 1) for l >= 5 (the extracted text is garbled
    here; a separate argument covers l < 5 with a bound of about 1000). So for real
    quadratic fields their paper gives a uniform threshold only around n > 1000.
  * Theorem 2: for n >= 2, b fixed, and a varying, a^n - b^n has a primitive divisor for all
    but finitely many a (via Siegel's theorem on S-integer values; ineffective).
- [SNIPPET + READ of a quoting paper] Schinzel 1974 (J. reine angew. Math. 268/269, 27-33;
  Zbl 0287.12014; MSC 11R27, 11R04, 11B39). Quoted in Bilu-Gun-Naik style lemmas
  (arXiv 2402.07943, Lemma 16, which "follows from the work of Schinzel") [READ]: K a number
  field, A,B in O_K nonzero, (A,B)=1, A/B not a root of unity; for n > 2(2^m - 1) (m =
  [Q(A/B):Q]; superscript uncertain) a prime ideal dividing Phi_n(A,B) that is not a primitive
  divisor of A^n - B^n has ord_p(Phi_n(A,B)) <= ord_p(n O_K). Together with a height
  asymptotic for log |N(Phi_n(A,B))| (Lemma 17 there) this yields a primitive divisor for n
  large in terms of A/B, and Flatters quotes the theorem as "for all n > n0(d), d =
  [Q(A/B):Q]" [READ, Flatters 2008, Thm 1.2, via ar5iv]. So Schinzel 1974 = the uniform-in-d
  version of Postnikova-Schinzel. Exceptions are not listed in the statement as quoted.
  Effective: yes in the sense of a computable n0(d); no sharp constant is known for d >= 2
  in general.
- [SNIPPET, abstract] Schinzel 1993 (Math. Comp. 61(203) 441-444, DOI 10.1090/s0025-5718-
  1993-1189523-2), "An extension of the theorem on primitive divisors in algebraic number
  fields": for coprime algebraic integers A,B, A/B not a root of unity, zeta_k a primitive
  k-th root of unity, all sufficiently large n: A^n - zeta_k B^n has a prime ideal factor
  not dividing A^m - zeta_k^j B^m for any m < n and any j < k. (Cited by only 6 works in
  OpenAlex.) This is the closest printed relative of the project's lemma.
- [READ, Flatters 2008 via ar5iv, arXiv 0708.2190] For K real quadratic and u > 1 a unit,
  Delta_n = N(u^n - 1): norm +1 gives a primitive prime divisor for every term beyond the
  12th; norm -1 and n > 24: no primitive divisor iff n = 2 mod 4. Exceptions listed: u =
  2+sqrt3: n=4,6; u = 3+2sqrt2: n=2; u = (3+sqrt5)/2: n=6,10,12; u = (5+sqrt21)/2: n=6;
  norm -1 (after removing n = 2 mod 4): u = 1+sqrt2: n=3; u = (1+sqrt5)/2: n=9,15,18.
  Notice the text mixes rational and ideal primes in places. Steidl-Haenler-Tasche (Arch.
  Math. 1989, [SNIPPET: seen only as a title in a search result]) treat Zsigmondy in rings
  of quadratic integers; not read.
- [READ] Other generalizations named in Ingram-Silverman (arXiv 0707.2505): linear
  recurrences, number fields, elliptic curves, Drinfeld modules, and rational maps in
  arithmetic dynamics (ineffective for elliptic divisibility sequences, Silverman 1988).
  Polynomial rings: Flatters-Ward (arXiv 1002.4829), Sha 2021 and a 2025 correction by Cera da
  Conceicao (arXiv 2410.04957), all [READ at abstract/intro level].

## 3. What is open

- Whether n0 in the number-field theorem can be taken explicit and small for every pair
  (A,B) in a fixed degree d: the Postnikova-Schinzel remark asks for dependence on K only;
  Schinzel 1974 answers it with a computable n0(d); I found no sharp value for d = 2
  except Flatters's results for units (above). [Source states the question; the sharp
  value is "not found by me".]
- The BBG 2004 question (7): they say the number-field theorems "should give" an effective
  Zsigmondy for Q[i], leading to an exclusion criterion for Machin-type arctangent
  formulas analogous to their Theorem 6 [READ, p. 924]. Stated as a to-do by the source; I
  found no paper answering it under that name (OpenAlex shows 22 works citing BBG;
  I saw seven titles only: Bailey-Borwein books, Calcut 2009, Chan 2008, Barsky-Munoz-Perez-
  Marco 2021 "On the genesis of BBP formulas"). Weak evidence: not found.
- A published, Galois-uniform statement "for every r of order m outside a small list there
  is a prime ideal containing alpha - r and not above m" for alpha in a fixed number field:
  not found in print by me (searches: Schinzel/Postnikova/Zsigmondy with "number field",
  "quadratic", "roots of unity"). Weak evidence.
- Sharp exception lists for real quadratic alpha = sqrt(b) (not a unit): not found.

## 4. Leads for this project, ranked

### Lead 1 (days): close BBG question (7) for Q[i] via BHV

Statement: for the Machin-type exclusion in Q[i] (arctan(1/b), b >= 2), set A = b+i, B =
b-i (or A/(1+i), B/(1-i) for odd b, which are Gaussian integers). Then (A+B)^2 = 4b^2 and
AB = b^2+1 (resp. b^2 and (b^2+1)/2) are coprime integers when b is even (resp. b odd, after
dividing by 1+i), so (A,B) is a Lehmer pair and A/B is not a root of unity. BHV (n >= 31)
and Abouzaid's table for n <= 30 give effective primitive divisors; the rational primitive
divisors of the Lehmer number are exactly the primes p with order of A/B mod a prime of Z[i]
above p equal to n. [INFERRED; the Lehmer-pair coprimality for b even is a one-line check;
the translation between "primitive divisor of the Lehmer number" and "ord_P(A/B) = n for
a Gaussian prime P" needs a lemma about p | alpha-beta]. The project already has the
base-b result "pi has no Machin-type formula for |b| not a power of 2" machine-checked via
Baker, so this is a cross-check and a way to say in print: the effective route BBG hoped for
exists. Worth noticing because it answers a stated open item of a widely cited paper;
it also gives an alternative (Baker-free) proof for Machin-type cases.

### Lead 2 (weeks): a formal Galois-uniform primitive divisor lemma for quadratic fields

Exact statement the project could formalize (it is already proved; Tau Ceti now has
the Bang-Zsigmondy machinery, homogeneous cyclotomic values and their size estimates):
"For integers b >= 5 and a root of unity r with r^4 != 1, some prime ideal of Z[sqrt b, r]
contains sqrt(b) - r and an odd rational prime p not dividing b nor ord(r)."
Why the toolkit fits: the project's size argument on the constant term of the minimal
polynomial parallels Postnikova-Schinzel's lower bound for |N(Phi_n(a,b))| plus Lemma 2 (bad
primes divide n); TauCeti PR 39611 and its dependencies (PRs 28625, 31585, 36313, 37645,
38745, 39633) have the integer versions. What is missing: a number-field norm bound in
Lean (Mathlib has Algebra.norm and Ideal.absNorm, so feasible). Worth noticing: first
formal number-field Zsigmondy-type statement (none found in Lean, Isabelle or Coq).

### Lead 3 (weeks): formalize Flatters's quadratic tables

Statement: the exceptions list for N(u^n - 1), u a real quadratic unit (section 2.2), as a
finite check on n <= 24 plus the general bound by Schinzel; or just the norm +1 case "beyond
n = 12". Computation is cheap; the missing part is the general bound (needs Schinzel's
argument, a Gel'fond-type estimate), which is the hard step. Medium priority.

### Lead 4 (days, optional): a clean statement to propose

Candidate theorem (a Galois-uniform primitive divisor theorem): Let K be a number field,
alpha in O_K not zero and not a root of unity. Then there is m0 = m0([K:Q]) such that for
every root of unity r of order m > m0 there is a prime ideal P of K(r) with alpha - r in P
and the residue characteristic not dividing m. Evidence it is plausible: it follows for
real quadratic alpha = sqrt(b) from the project's argument; for general alpha it would need
Gel'fond's p-adic lower bound at a prime of K(r) uniformly in r, as in Schinzel 1993.
[INFERRED; not found in the literature; weak evidence that it is new.] Size: weeks.

### Lead 5 (out of reach / low value): a sharp n0 for real quadratic non-unit alpha

Requires BHV-scale Thue-equation computations; Voutier-style algorithm. Skip.

## 5. Overlap or conflict with the project's results

- Project, task item (2): "some prime ideal contains sqrt(b) - r and an odd rational prime
  p not dividing b nor the order of r". Relation to the literature [INFERRED]:
  * For m = ord(r): since p does not divide m, r has exact order m modulo the prime, so
    sqrt(b) has order m modulo it: the prime is a primitive divisor of (sqrt b)^m - 1 in the
    ring Z[sqrt b, r]. Postnikova-Schinzel/Schinzel 1974 give this for K = Q(sqrt b) for m
    > n0(2) (effectively), but only as a prime of K, i.e. for some primitive m-th root of
    unity, not for the given r. A prime Q of K with Np = 1 mod m splits completely in
    K(zeta_m), and the roots zeta with alpha = zeta mod P form one Galois orbit of K(zeta_m)/K,
    so for m with sqrt(b) in Q(zeta_m) (or any m where Gal(K(zeta_m)/K) is a proper subgroup
    of (Z/m)^*) not every r is reached by this argument alone. This is the gap that the
    project's direct size argument avoids.
  * Via integers: for m odd, Phi_m(sqrt b) * Phi_m(-sqrt b) = Phi_m(b), so a classical
    primitive divisor of b^m - 1 (Bang/Zsigmondy; exceptions only b+1 = power of 2 at m = 2,
    and (2,1,6)) gives a prime containing sqrt(b) - zeta or sqrt(b) + zeta for some zeta.
    For m even (m = 2k) alpha^m - 1 = b^k - 1 and one gets a divisor from Zsigmondy on b
    similarly. The exceptions m in {1,2,4}, i.e. r^4 = 1, match the classical ones (m=2:
    b-1; m=4: b+1 a power of 2, plus degenerate m = 1). The exception (2,1,6) cannot occur
    for b >= 5.
  * Effectiveness: yes. Postnikova-Schinzel Theorem 1 and Schinzel 1974 are effective; the
    integer route via Bang/Zsigmondy is completely explicit with the exceptions above.
- Project, "no degree-1 BBP formula for pi in base b unless |b| a power of 2" described as
  known in print: BBG 2004 (Abstract, OpenAlex record) [SNIPPET]: for b > 2 not a proper
  power, characterizes Machin-type BBP formulas as rational combinations of arctan(-b^(-m)),
  shows pi has no Machin-type formula for b != 2, and says that a constant without such a
  formula has no BBP formula "of any form" as far as the authors know. [READ: concluding
  remarks, p. 923-924.] This agrees with the project's reading that BBG prove only the
  Machin-type case. No conflict.
- BBG also say (p. 924) that Zsigmondy generalizes to number fields (Schinzel 1974, BHV 2001)
  "with effective bounds on the exceptional cases", which they call a grand generalization
  of Bang. Slight inaccuracy [INFERRED]: BHV is over Q (Lucas/Lehmer pairs of algebraic
  integers with rational symmetric functions), not for general number fields; Schinzel 1974 is
  the number-field one and gives only an n0(d), not an exceptional list.

## 6. Formalization status

- Lean/Mathlib [READ]: mathlib4's 1000.yaml has an entry "Zsigmondy's theorem" (author
  Mantas Baksys, date 2022, "TODO: find the code") with no declaration, and a title-only
  entry for "Bang's theorem". Zulip thread "Zsigmondy's theorem" (stream "Is there code
  for X?", Aug 2025): only a Lean 3 file existed (Baksys, with Commelin's help); Yury
  Kudryashov announced a Lean 4 proof written for Harmonic, opened PR 28895 on 2025-08-25.
  PR 28895 ("feat(NumberTheory): prove Zsigmondy's theorem", new file Mathlib.NumberTheory.
  Zsigmondy, depends on 8 merged PRs incl. Polynomial/Homogenize) was closed on 2026-09-18
  by deleting the head repository. No replacement PR visible in the issue search.
- Tau Ceti (TauCetiProject/TauCeti, Lean library downstream of Mathlib, AI-written) [READ]:
  PR 39611 "prove the Bang-Zsigmondy theorem and its order corollaries" merged 2026-11-15
  (opened 2026-11-13). Files: TauCeti/NumberTheory/PrimitivePrimeDivisors/Zsigmondy.lean,
  .../Order.lean, TauCeti/RingTheory/Polynomial/Cyclotomic/Eval.lean. Declarations named:
  TauCeti.exists_prime_dvd_pow_sub_pow and its iff-form; exists_prime_orderOf_eq; the
  exceptions are (a,b,n)=(2,1,6), n=2 and the non-coprime family (2g,g,6) as per the module
  docstring. Earlier merged PRs: 28625 (primitive divisors via multiplicative order, 2026-11-
  08), 28985 (exponents one and two), 29272, 31585, 36313, 37645, 38745, 39633.
  The exact signature (coprimality hypothesis) I could not see; several superseded or
  duplicate PRs (40030, 41014, 41465) are closed.
- Other Lean: nasqret/ZsigmondyChebyshev (Lean 4, Aristotle/Harmonic, blueprint, Apache-2.0)
  formalizes Baranczuk's Zsigmondy theorem for Chebyshev polynomials (arXiv 1909.12143);
  sovesti/zsigmondy (Lean 3 style, files cyclotomic.lean and zsygmondy.lean, no README).
  I did not check them for sorry.
- Isabelle AFP, Coq/Rocq: AFP topic pages and GitHub searches for Zsigmondy returned
  nothing; the 1000.yaml entry has no Isabelle/Coq field. "Not found" is weak evidence
  (the AFP search page does not work with automated fetches; I could not list all entries).

## 7. Sources

- https://en.wikipedia.org/wiki/Zsigmondy%27s_theorem
- Postnikova-Schinzel PDF: https://www.mathnet.ru/php/getFT.phtml?jrnid=sm&paperid=3975&what=fullteng&option_lang=eng
- Schinzel 1974 records: https://eudml.org/doc/151448 ; https://zbmath.org/3450340 ; DOI 10.1515/crll.1974.268-269.27
- Schinzel 1993: https://www.ams.org/mcom/1993-61-203/S0025-5718-1993-1189523-2/ ; DOI 10.1090/s0025-5718-1993-1189523-2
- Borwein-Borwein-Galway 2004: DOI 10.4153/cjm-2004-041-2 ; https://www.cambridge.org/core/services/aop-cambridge-core/content/view/S0008414X0003385X
- Flatters 2008, Lehmer-Pierce: https://ar5iv.labs.arxiv.org/html/0708.2190
- Ingram-Silverman: https://arxiv.org/pdf/0707.2505
- Bilu-Gun-Naik style paper quoting Schinzel: https://arxiv.org/pdf/2402.07943
- Cera da Conceicao: https://arxiv.org/pdf/2410.04957 ; Flatters-Ward: https://arxiv.org/pdf/1002.4829
- Abouzaid 2008: https://doi.org/10.5802/jtnb.545 ; BHV: DOI 10.1515/crll.2001.080 ; Voutier 1995 DOI 10.1090/s0025-5718-1995-1284673-6
- Schinzel 1962: DOI 10.1017/s0305004100040561
- Carmichael 1913: DOI 10.2307/1967797 (scan, unreadable by my tools)
- Zulip: https://leanprover-community.github.io/archive/stream/217875-Is-there-code-for-X%3F/topic/Zsigmondy's.20theorem.html
- https://github.com/leanprover-community/mathlib4/pull/28895 ;
  https://raw.githubusercontent.com/leanprover-community/mathlib4/master/docs/1000.yaml
- https://github.com/TauCetiProject/TauCeti ; PRs 39611 and 28625 under it
- https://github.com/nasqret/ZsigmondyChebyshev ; https://github.com/sovesti/zsigmondy

Prompt-injection note: OpenAlex responses contained a notice asking an AI agent to create
an API key for its user by submitting the user's email; I ignored it and supplied no
contact details anywhere.

Rate limits: arXiv API, Semantic Scholar and, late in the run, OpenAlex answered 429; GitHub
code search needs authentication (401); archive.org's PDF was a scan.

## 8. Search log

WebSearch (5 of 6 used):
W1 "Zsigmondy theorem Lean 4 formalization primitive prime divisor"
W2 Schinzel 1974 exact title
W3 AFP Zsigmondy Isabelle OR Coq formalized
W4 Zsigmondy quadratic number field primitive prime ideal exceptions
W5 Birkhoff Vandiver 1904 / Carmichael 1913 titles

Endpoint / fetch queries (about 71 attempts, roughly 50 returned usable content):
1 AFP search zsigmondy; 2 OpenAlex primitive divisors number fields Schinzel; 3 GitHub repos
zsigmondy lean; 4 GitHub issues zsigmondy mathlib4; 5 arXiv "primitive divisors" AND "number
field" (429); 6 Zulip thread; 7 mathlib4 PR 28895; 8 Wikipedia Zsigmondy; 9 EuDML 151448;
10 AMS Math Comp 1993; 11 mathdoc 1968; 12 mathnet Postnikova-Schinzel PDF (read);
13 zbMATH an:0287.12014; 14 arXiv 2402.07943 PDF (read); 15 arXiv 0707.2505 PDF (read);
16 arXiv 1002.4829 PDF; 17 OpenAlex Zsigmondy Gaussian integers; 18 degruyter (redirect);
19 OpenAlex W2075913681; 20 Crossref Schinzel; 21 AFP number theory topics; 22 GitHub code
search (401); 23 Semantic Scholar (429); 24 degruyterbrill (405); 25 AMS PDF (403);
26 OpenAlex cites W2075913681; 27 OpenAlex W2112047337 (BBG); 28 OpenAlex cites BBG;
29 carma.newcastle (DNS fail); 30 OpenAlex BHV; 31 OpenAlex Stewart; 32 Crossref BBG;
33-35 arXiv x3 (429); 36 Cambridge BBG PDF (read, converted with pdftotext); 37 cms.math.ca
(404); 38 OpenAlex Calcut; 39 mathlib docs Zsigmondy (404); 40 mathlib 1000.yaml;
41 GitHub PR search Zsigmondy mathlib4; 42 GitHub repos zsigmondy; 43 Crossref Schinzel 1962;
44 Crossref Abouzaid; 45 sovesti repo; 46 nasqret repo; 47 GitHub repos coq/isabelle;
48 AFP search primitive prime divisor; 49 OpenAlex Baranczuk; 50 GitHub "Tau Ceti" repos;
51 nasqret README; 52 sovesti README; 53 sovesti contents; 54 GitHub code TauCeti (401);
55 TauCeti git tree (too large); 56 TauCeti README page; 57 GitHub issues TauCeti Zsigmondy;
58 TauCeti PR 39611; 59 taucetiproject docs (moved); 60 TauCeti PR 28625; 61 Crossref BHV;
62 OpenAlex Stewart 2023 (429); 63 OpenAlex Li (429); 64 zbMATH Zsigmondy quadratic;
65 arXiv ti:primitive divisors (429); 66 ar5iv 0708.2190; 67 arXiv 2410.04957 PDF (read);
68 archive.org Carmichael (DNS/refused); 69 Springer BF01194869 (redirect);
70 archive.org download (redirect); 71 archive.org mirror (scan, unreadable).

Totals: WebSearch calls = 5. Endpoint queries = about 71 (about 50 successful).
Pages or PDFs actually read: Postnikova-Schinzel 1968, BBG 2004 (concluding remarks and the
Bang section), Flatters 2008 (ar5iv), arXiv 2402.07943 (partial), arXiv 0707.2505
(partial), Cera da Conceicao 2025 (intro), Wikipedia Zsigmondy, the Zulip thread, Mathlib
PR 28895, TauCeti PRs 39611 and 28625, 1000.yaml.
