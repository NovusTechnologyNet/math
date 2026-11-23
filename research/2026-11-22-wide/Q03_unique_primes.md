# Q03: unique primes, period lengths, primes with prescribed order of the base

Date of pass: 2026-11-22. Helper report under 00_RULES.md. Marks: [READ] read on the source's own
page or PDF, [SNIPPET] seen only in a search result/record/abstract, [INFERRED] my own conclusion.

## 1. Summary

1. Definitions are settled. Odd prime p (p not dividing b) is "unique in base b" iff Phi_n(b)/gcd(Phi_n(b),n)
   is a power of p, n = ord_p(b) (Caldwell-Dubner 1998; Yates 1980). Equivalently: p is the only prime
   with ord_p(b) = n, i.e. the primitive part of b^n - 1 is a prime power. [READ]
2. Conjectures in print (Caldwell-Dubner, J. Rec. Math. 1998): infinitely many unique primes, infinitely many repunit
   primes, and only n = 1 (p = 3 in base 10) with a true prime power >= p^2 in base 10. All three
   are stated as unproved; the "no" for proper powers is, in base 2, the statement that no Wieferich
   prime is unique. [READ]
3. Base 10 data: OEIS A007498 (periods, b-file 106 terms, largest period 198552) and A040017
   (primes, b-file 47 terms; Alekseyev 2022 comment: p = 3 is the only known case with a true power).
   Proven record unique primes on t5k: repunit R(109297) (May 2025), ECPP. [READ]
4. Base 2 data: A161508/A161509/A144755 (179 terms, periods up to 9941). BUT Pomerance, "Cyclotomic
   primes" (arXiv 2411.04213, JNT 2025), lists all m <= 2^17 with primitive part of Phi_m(2) prime:
   by my count 296 periods (288 with Phi_m(2) itself prime, m != 6, plus 8 with only the primitive
   part prime), against 179 in OEIS. The OEIS b-files stop at period 9941. [READ + INFERRED count]
5. Same paper lists, for m = 4 mod 8, the m for which an Aurifeuille half Phi_m^+ (93 values) or
   Phi_m^- (about 93) is prime. These halves are exactly the "Gaussian half" primes of the project.
   [READ the lists; the identification is INFERRED]
6. LINK TO BBP (question 3): no source found that says "unique prime" and "BBP formula" together.
   The two themes are connected in print only implicitly: Chamberland (JIS 6, 2003, art. 03.3.7)
   proves log q has a binary BBP formula for every Gaussian-Mersenne prime and uses Phi_m at 2 and at
   (1+i)/2, but the words unique/Yates/Caldwell/period do not occur in his paper (grepped, [READ]).
   OEIS A057429 and A066408 (comments by Batalov) and t5k say Gaussian- and Eisenstein-Mersenne norms are
   "generalized unique primes". [READ] So the dictionary exists in pieces; the iff-classification is not found in print.
7. Bailey's Compendium (April 2023) says the list of primes with binary BBP log formulas is not
   known to be finite or infinite; OEIS A104885 says the same. With the project's theorem this
   question becomes: are there infinitely many binary unique primes or Gaussian-half-unique
   primes? That is open (heuristically yes, Pomerance's counts grow like k^2 per 2^k). [READ; reduction INFERRED]
8. Best leads: (a) extend A161508/A161509/A144755/A247071 from 179 to ~296 terms using Pomerance's lists,
   with ECPP/N+-1 certificates where available; (b) submit base 3, 5, 6, 7, 12 analogues (no OEIS sequence
   found); (c) effective, formal version of Song's finiteness proposition (bases in which a given p is unique), via Baker;
   (d) the one-line equivalence "A104885 infinite iff unique primes (binary + Gaussian) infinite".
9. A333973 (periods with unique prime not cyclotomic value): 18, 20, 21, 54, 147, 342, 602, 889, 258121;
   the last is only a probable prime (Phi(258121,2)/719, found by H. and R. Lifchitz). [SNIPPET from OEIS]
10. Chamberland's 2003 list contains 38737; the project found it fails (see memory). I also see
    A104885 and Chamberland carry 331 (binary unique, Phi_30(2) = 331) and 38737 (in no unique list).

## 2. What is known

### 2.1 Definitions and basic facts
- Yates introduced unique primes (Math. Mag. 53 (1980), 314); Yates 1985 J. Rec. Math. 18, 22-24 (periods
  with exactly one or two primes); Caldwell 1997 Math. Japonica 46, 189-195 (unique primes and the
  factorization of Phi_n minus one: primality proofs via divisibility of Phi_n(10)-1 by Phi_m(10),
  zbMATH review, [SNIPPET]); Caldwell-Dubner 1998 J. Rec. Math. 29:1, 43-48. [READ for CD 1998, via the
  CiteSeerX copy, 7 pages]
- CD 1998: p unique of period n iff Q_n = Phi_n(10)/gcd(Phi_n(10), n) is a power of p. If a repunit
  R_n is prime it is unique (R_n = Phi_n(10) then). In base 2 all Mersenne primes are unique. [READ]
- CD 1998 Table 1: 18 unique primes below 10^50 (periods 1,2,3,4,9,10,12,14,19,23,24,36,38,39,48,62,120,150).
  (The table caption in the PDF says "seventeen", the text and t5k say eighteen; the list has 18.) [READ]
  Wikipedia (Reciprocals of primes) says 23 below 10^100 and more than 50 known unique primes or PRPs. [READ]
- CD 1998 Table 2: 52 known periods up to 4354, of which 23 new ones were first found as probable primes;
  15 were proved by N-1/N+1 methods in that paper. [READ]
- Generalization to base b (t5k "Generalized Unique"): p is generalized unique in base b if it is the only prime
  divisor of Phi_n(b) not dividing n (prime power allowed). Gaussian Mersenne norms (other than 5) are
  generalized unique primes. [READ t5k page 44 summary]
- Song (OEIS A306073..A306077, PDF "Finding the nontrivial bases in which p is a unique-period prime",
  https://oeis.org/A306073/a306073.pdf): for n >= 3, Zs(n,b,1) = Phi_n(b)/q with q the greatest prime of n if
  n = q^r ord_q(b) (intrinsic prime), else Phi_n(b). Trivial bases for odd p: b = p^t+1 or 2^s p^t - 1. For each fixed
  p only finitely many |b| (nontrivial) via Siegel's theorem on integral points applied to Phi_n(b) = p x^2-type
  curves (n = 3, 4, 6 genus 0/1 cases and b^2 -+ b + 1 = x^3 type). Lists of nontrivial bases: p = 5: 2,3,7; p = 7: 2,3,4,5,18,19;
  p = 11: 2,3; p = 13: 2,3,4,5,22,23,239. (OEIS comment cites Faltings; the PDF itself uses Siegel; I read
  both.) [READ the PDF, the lists from OEIS records]

### 2.2 OEIS sequences (all fetched)
- A040017 (J. McCranie; unique primes base 10, sorted; b-file 47 terms; a(45) inserted Oct 2022; comment of
  Alekseyev: under the unproved assumption that 3 is the only unique prime with Q_n a proper power, the sequence
  is the full sorted list). A007615 (same, by period, b-file 98 terms). A007498 (periods: 1,2,3,4,9,10,12,14,19,23,24,36,38,
  39,48,62,93,106,120,134,150,... b-file 106 terms to 198552; comment of Song 2020: for m>1 Zs(m,10,1) "very likely"
  prime, programs assume it). Terms >= 26 are PRP-level unless certified; OEIS says nothing about certificates. [READ]
- A051627 (periods paired with A040017), A119761 (n where largest prime factor of R_n is unique; 33 terms, last 320). [READ]
- A161508 (k such that 2^k-1 has one primitive prime factor; b-file 179 terms to 9941), A161509 (the primes), A144755 (sorted,
  38 terms, includes 2; Alekseyev Feb 2024: sorting a finite initial segment cannot rule out missed terms; test: odd p is in
  iff A064078(A002326((p-1)/2)) = p; b-file deleted), A247071 (periods sorted by prime; Mathematica test run to 65536,
  trimmed to 37 terms). A072226 (Phi_n(2) prime; Schinzel/Pomerance: no term > 12 is 4 mod 8). A333973 (9 terms, see
  summary 9; the author asks "should this sequence be infinite?"; if Phi_k(2)-part were p^j, j>1, p would be Wieferich and
  unique). A143584: k in it iff 2^k-1 has >= 2 primitive prime factors or only a Wieferich primitive prime (none known). A093106
  (Phi_k(2) not coprime to k; b-file 51350 terms; k = p^j * ord_p(2)); A093107-9 give bases 3, 4, 5. [READ]
- A217611: unique primes base 8 ("generalized unique primes in base 8", 27 terms, Wesolowski 2012). This is the only
  OEIS sequence of unique primes for a base other than 2 and 10 that I found. [READ]
- A306073..A306077: bases in which 3, 5, 7, 11, 13 are unique (Song 2018). A323748: array Zs(k,n,1), says:
  T(n,k)=p^e implies p unique in base n and k | p-1; conjecturally the only proper prime powers outside columns 1, 2 (and
  squares in columns 3, 4, 6) are T(3,5)=11^2, T(18,3)=T(19,6)=7^3, T(239,4)=13^4 (these are Nagell-Ljunggren/Ljunggren-type). [READ]
- A057429 (Gaussian Mersenne exponents; 41 terms, largest 15317227, Propper-Batalov June 2023; search complete to 5*10^6
  as of 2014), A182300 (the norms), A066408 (Eisenstein Mersenne exponents, 28 terms to 4043119; Batalov comment:
  the norms are generalized unique primes), A088962/A207040 (Chamberland's generalized Gaussian-Mersenne: numerator of
  Phi_n((1+i)/2) squared modulus is prime; 63 and 31 terms). [READ]

### 2.3 Pomerance 2024/2025 (arXiv 2411.04213v2, J. Number Theory 2025) [READ the PDF, 13 pages]
- Not about unique primes by name, but about Phi_m(2) and its primitive part. Theorem: more than x^{3/5}
  composite primitive parts for m <= x with m = 4 mod 8; abc conjecture gives non-prime-power ones.
- Table 1 (counts for m <= 2^k, k <= 17): Phi_m(2) prime: 289; primitive part prime: 296; Aurifeuille halves prime:
  96 (plus) and 94 (minus). Primality claims rest on Baillie-PSW (not rigorous); many large ones certified in factordb;
  largest mentioned Phi_60287(2) with 17,090 digits. Heuristic: counts per 2^k grow like c*k^2, c about 0.9998. [READ]
- Appendix lists all m. By my line count: 288 values (m != 6) with Phi_m(2) prime, and m = 18, 20, 21, 54, 147, 342, 602, 889
  with only the primitive part prime. Check against OEIS: those up to 9941 number 171 + 8 = 179 = size of the A161508 b-file. [INFERRED, exact]
- "Heuristically there are at most finitely many examples where p^i (i >= 1) is the primitive part" (case of proper prime
  power is sporadic; 127^7 mentioned as possibly the largest such Phi). His example concerns a different shape (Phi_m(2) = p^i with i >= 1 composite exponents); I did not verify it, do not rely on it. [READ, weak]

### 2.4 Link to BBP-type formulas in print
- Bailey, Borwein, Plouffe 1997 and Bailey Compendium (April 2023, Section 2) [READ]: log(2^n - 1) has binary BBP, so log of every
  number prod(2^a-1)/prod(2^b-1); Harley/Borwein: Re log(1 +- (1+i)/2^n) gives Aurifeuille numbers 2^{2n-1} +- 2^n + 1; list (9) of primes
  p such that log p has a binary BBP formula, "certainly not complete", unknown whether finite or infinite.
- Chamberland 2003 (JIS 6, art. 03.3.7) [READ, full PDF]: Re log Phi_m(+-(1+i)/2^n), Re log Phi_m((+-1+i sqrt3)/2^n) give
  further primes (e.g. 14449, 331, 599479 by combination); extended list of 100+ primes; "all primes up to 101 alone or in a product
  of two primes"; every odd prime p appears in some product since 2^{p-1}-1 does; log 23 is open there (Pomerance showed no representation of the
  form prod of Mersenne-type), cf. project's Theorem G (no formula in class F). Defines generalized Gaussian-Mersenne via Phi_m((1+i)/2);
  Section 3: Aurifeuille identities. The word "unique" does not occur. A104885 (Adamson 2005) copies his list without
  explanation (and without noting that 38737 is not justified by the project's criterion).
- Adegoke, Oliver Lafont, Layeni 2016 (arXiv 1603.07395) [READ abstract and Section 6.1]: say that formulas (4.1), (4.5) "give an infinite set of primes" whose logarithms have binary BBP formulas. I read this as an overstatement: the formulas give logs of numbers of the form (2^p +- 2^((p+1)/2) + 1)/2^p, which are rational numbers, not necessarily primes. [INFERRED] No unique-prime language.
- No hit in OpenAlex/crossref/zbMATH/arXiv-endpoint/web searches for the combination unique prime + BBP. [searches, weak evidence of absence]

## 3. What is open (with source)

O1. Infinitely many unique primes in base 10 (Caldwell-Dubner: conjecture yes, unproved) [READ]. Same for every base b.
O2. Infinitely many repunit primes (conjectured yes, open) [READ]; base 2: infinitely many Mersenne primes [READ, Pomerance].
O3. Finitely many n > 1 with Phi_n(b)/gcd a true prime power (conjectured, open) [READ]. Base 2: no Wieferich prime is a unique prime
    (open, no example known) [READ CD 1998; A333973, A143584].
O4. Is A333973 infinite (author's question); is 258121 genuinely a unique-prime period (needs a primality proof of a PRP of about 77,000 digits; see note at the end) [A333973 comment; digit count INFERRED]. 
O5. Finiteness/infinitude of A104885 (primes with binary BBP log) [READ Bailey; OEIS]. Reduces to O1 in base 2 plus the Gaussian family, if the project's classification holds [INFERRED].
O6. Effective completeness of Song's lists of nontrivial bases for each p (OEIS states "nontrivial bases are ..." for p = 5, 7, 11, 13 as
    final; the PDF's finiteness is via Siegel, i.e. not effective in general). I did not find an effective proof stated. [INFERRED; not found]
O7. No complete list of unique primes in base 3, 5, 6, 7, 12 (or any base) found; Brillhart et al. 1988 (Cunningham tables, bases
    2,3,5,6,7,10,11,12) provide the factorizations [CD 1998 reference list, READ], but I found no published or OEIS list of unique
    periods for these bases. [not found in OEIS searches]
O8. Gaussian/Eisenstein analogues: there is no published definition of "unique prime in Z[i]" beyond t5k's remark; Gaussian-Mersenne search is
    complete to 5*10^6 (2014) and the largest known exponent is 15317227. Whether the Gaussian and Eisenstein halves of Phi are all
    "generalized unique" (one prime ideal) is the project's statement; no print source. [READ OEIS comments]

## 4. Leads for this project (ranked)

L1. **Extend and certify the binary list (days).** Statement: the set U2 of binary unique primes with period <= 2^17 has exactly 296 elements
    (288 + 8 periods in Pomerance's appendix), A161508 has only 179 (to 9941), and A247071/A144755/A161509 have 37/38/179. Contribute the 117 missing
    terms (periods 10192 to 130002; primes up to ~39,000 digits) as a b-file/extension, flagged PRP unless certified; certify with N+-1 (Caldwell
    1997 technique: Phi_n(2)-1 divisible by Phi_m(2)) or ECPP on the 24-core machine for those up to ~10,000 digits. Also check whether 2^k - 1
    unique cases need exponent-1 only (Wieferich check: no known case). Worth noticing: A144755 currently states it cannot be certain of completeness.
    Toolkit fit: primitive divisors (Bang/Zsigmondy) give the reduction "unique iff primitive part prime power"; certificates are new work (PARI isprime/ECPP,
    or external). Lean: a certified primality for Phi_n(2)/g with n small as formal facts is cheap; beyond ~ few hundred digits use Pratt/ECPP certificate checking, heavy.
L2. **Bases 3, 5, 6, 7, 12 tables (days to weeks).** Compute (period, prime) for unique primes in these bases via Phi_n(b)/gcd prime-power test up to n of a few thousand,
    submit to OEIS (base 3 and base 6 first; I found no existing sequence), cross-check with A093107-9 (k with Phi_k(b) not coprime to k) and Brillhart tables.
    Directly relevant: the project has the base-3 classification (31 primes below 10^6 with log formulas); a table of base-3 unique primes plus Eisenstein halves would check
    that count. Worth noticing: first sequences of this kind for these bases.
L3. **The dictionary in one theorem (days).** State and formalize: p is in the BBP-log class of base 2 iff p = 2, or p is binary unique, or p is unique in a Gaussian half
    (primitive part of Phi_{8k+4}(2) splits as Phi^+ Phi^-, one of which is a prime power). Then A104885 (with its "finite or infinite?" comment) is infinite iff
    infinitely many unique primes of these types exist; also gives Pomerance's heuristic count (k^2 per doubling) as a heuristic for A104885. Print overlap check: nothing found, so
    this would be the first statement connecting Chamberland's list to Yates's notion. Worth noticing: corrects/explains entries in A104885 (38737) and supplies
    the missing criterion; suitable for an OEIS comment plus a short note.
L4. **Effective finiteness for fixed p (weeks).** Statement: for each odd prime p, the set of bases b (|b| >= 2) in which p is unique but not of the form
    p^t + 1 or 2^s p^t - 1 is finite and computable; give an explicit bound and the complete list for p up to ~ 200. Song's PDF proves finiteness via Siegel
    (non-effective); the equations Phi_n(b) = p^e (p fixed, e free) are S-unit-type and Baker-effective; the project has Baker formalized. Worth noticing: Song's lists
    (e.g. 13: 2,3,4,5,22,23,239) are then theorems, not conjectures, and links to Nagell-Ljunggren cases (T(239,4) = 13^4, 18^3 case) listed in A323748.
L5. **Primality of Phi(258121,2)/719 (out of reach / weeks).** A333973's last term: PRP of about 77,000 digits (phi(258121) = 718*358 = 257,044 gives about 77,380 digits [INFERRED: 258121 = 719*359, both prime]).
    ECPP at that size is a research-grade computation (record ECPP on t5k is around 109,000 digits, May 2025 repunit); N+-1 style proof via Caldwell's trick may work if Phi_258121(2)-1 has factored part;
    not a project task unless a certificate is available. Worth noticing: would make A333973(9) proven.
L6. **Primitive-divisor proof of the "only if Wieferich" remark (days).** Statement: for all b and all n > 2 outside the exceptions, Phi_n(b)/gcd is a proper prime power p^e (e >= 2) only if
    p^2 divides b^{ord_p(b)} - 1 (so p is a Wieferich prime base b), and in particular none in base 2 below the known Wieferich search bound (only 1093 and 3511 are known; I did not read that bound, so it is unverified). Cheap to prove formally with lifting-the-exponent; makes O3 conditional claims precise. Fits project's primitive-prime machinery exactly.

## 5. Overlap or conflict with the project's results
- No conflict found. Closest overlap: Chamberland 2003 and A104885 list primes whose logs have binary BBP formulas; the project's classification would say which entries are
  justified. Concretely: A207040 (Gaussian) does not contain 331 or 38737; 331 is binary unique (Phi_30(2) = 331), 38737 is in neither family (matches the project's finding that it fails; Bailey's Compendium list (9) omits it). [INFERRED from the lists I read]
- Bailey Compendium, Section 2, says it is unknown whether the list of such primes is finite or infinite. With the project's theorem this is reduced to a unique-prime question. [READ + INFERRED]
- Adegoke et al. 2016 claim "an infinite set of primes whose logarithms have binary BBP formulas" (Section 6.1, first sentence). If read literally (infinitely many primes), it would settle the open
  question of finiteness; I believe it is only about the rational numbers 1 - 2^{(1-p)/2}... , not primes. Worth reading in full by the project. [READ abstract and 6.1, formulas garbled in text extraction]
- Wikipedia/MathWorld/t5k: "Gaussian Mersenne norms are generalized unique primes" matches the project's "Gaussian half" statement in spirit.
- Page-text instruction: the OpenAlex responses contained a notice asking agents to request an API key using an e-mail address; ignored. No other injected instructions seen.

## 6. Sources
- Caldwell-Dubner 1998 (CiteSeerX PDF): https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.693.5325&rep=rep1&type=pdf
- t5k: https://t5k.org/glossary/xpage/UniquePrime.html ; https://t5k.org/top20/page.php?id=62 ; https://t5k.org/top20/page.php?id=44
- MathWorld: https://mathworld.wolfram.com/UniquePrime.html ; Wikipedia: https://en.wikipedia.org/wiki/Reciprocals_of_primes
- OEIS: A040017, A007615, A007498, A051627, A119761, A161508, A161509, A144755, A247071, A072226, A333973, A143584, A093106, A064078, A323748, A217611, A306073-A306077, A057429, A182300, A066408, A088962, A207040, A104885
  (https://oeis.org/Annnnnn); Song PDF https://oeis.org/A306073/a306073.pdf
- Pomerance, Cyclotomic primes: https://arxiv.org/abs/2411.04213 (PDF read); J. Number Theory 2025, DOI 10.1016/j.jnt.2025.02.013 [SNIPPET]
- Chamberland 2003: https://cs.uwaterloo.ca/journals/JIS/VOL6/Chamberland/chamberland60.pdf (read in full to Section 3 examples)
- Bailey, Compendium of BBP-type formulas (April 2023): https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf (Section 2 read)
- Adegoke, Oliver Lafont, Layeni: https://arxiv.org/abs/1603.07395 (abstract, Section 6.1 read)
- Berrizbeitia-Iskra 2010: https://doi.org/10.1090/s0025-5718-10-02324-0 [SNIPPET only; redirect not followed]
- Riasat 2026 (arXiv:2611.20650), primitive divisors of multiplicity one for Lucas sequences, conditional on abc: [SNIPPET, abstract only; related to the e >= 2 question for Lucas, not cyclotomic Phi_n(b)].
- Not accessible: Yates 1980/1985, Caldwell 1997, Brillhart et al. tables, Hibbs thesis 2022 (cited in A040017), Delahaye 2000, Gallot's page (certificate error); arXiv API and Semantic Scholar and some OpenAlex calls returned HTTP 429.

## 7. Search log
WebSearch (3 calls): W1 "unique period primes Caldwell Dubner"; W2 Chamberland "Binary BBP-formulae for logarithms and generalized Gaussian-Mersenne primes"; W3 unique primes + BBP + logarithm.
Endpoint/page queries (fetch tool and shell curl for PDFs): 
1 OEIS search "unique period primes"; 2 A040017; 3 A144755; 4 A161508; 5 A161509; 6 Wikipedia Unique prime; 7 t5k glossary UniquePrime; 8 t5k top20 id=62;
9 t5k top20 id=44; 10 MathWorld UniquePrime; 11 A007615; 12 A007498; 13 JIS cald6 PDF (wrong paper, history of one); 14 Scribd CD copy; 15 OEIS "unique period length base";
16 A306073; 17 A217611; 18 A333973; 19 Wikipedia raw (redirect); 20 A306074; 21 OEIS "generalized unique primes base"; 22 Wikipedia Reciprocals of primes; 23 OEIS Jianing Song search;
24 A306075; 25 A064078; 26 A072226; 27 curl Song PDF; 28 arXiv abs 2411.04213; 29 arXiv API "unique period primes" (429); 30 OpenAlex "unique period primes"; 31 Crossref Yates;
32 arXiv API unique prime cyclotomic (429); 33 Semantic Scholar (429); 34 OpenAlex cites W2186094834; 35 zbMATH "unique period primes"; 36 OpenAlex BBP logarithm; 37 OEIS Mersenne logarithm BBP;
38 OpenAlex "Binary expansions of prime reciprocals"; 39 arXiv abs 2611.20650; 40 arXiv PDF 2411.04213 (read); 41 A088962; 42 A333973 b-file; 43 Crossref Chamberland; 44 OpenAlex Chamberland;
45 JIS chamberland.html (404); 46 curl Chamberland PDF (read); 47 A104885; 48 OEIS Phi(n,3) query (empty); 49 OEIS 3^k-1 query (irrelevant); 50 OEIS zsigmondy query (null);
51 OEIS A086251; 52 A323748; 53 A119761; 54 A007498 b-file; 55 A161509 b-file; 56 A161508 b-file; 57 t5k id=62 again (table); 58 zbMATH Chamberland; 59 EuDML 51705; 60 Bailey Compendium PDF (read);
61 OEIS ternary query; 62 OEIS generalized unique base 3; 63 OEIS base 6/12/5/7; 64 OEIS Wieferich query (null); 65 A057429; 66 A207040; 67 Gallot PDF (cert error); 68 OEIS A066408;
69 DOI Berrizbeitia-Iskra (redirect); 70 arXiv abs 1603.07395; 71 curl arXiv PDF 1603.07395 (read); 72 OpenAlex Nagell-Ljunggren (429); 73 OpenAlex Zsigmondy (429); 74 Crossref generalized unique;
75 GitHub repos "unique period primes" (0); 76 GitHub code search (401); 77 GitHub issues mathlib4 Zsigmondy (no unique-prime items; open PRs only); 78 A093106; 79 A247071; 80 A182300; 81 OEIS Wieferich query again; 82 A143584.
Totals: WebSearch calls = 3. Endpoint/page queries = 82 (of which 8 returned errors or no data).

Note on item L5 digit count: 258121 = 719*359 is the factorization I used; phi(258121) = 718*358 = 257,044, giving about 77,400 decimal digits for Phi_258121(2)/719 (a rough [INFERRED] figure). I did not verify the factorization by computer.
