# Q09: special primes that are values of cyclotomic-type expressions

Date of pass: 22 November 2026. Marking: [READ] page or PDF read on the source; [SNIPPET] only in a
search result or API record (this includes statements obtained through the fetch tool's page
summaries of Wikipedia, OEIS and Mathlib pages, which is a small model's digest, not the raw
text; I flag the ones that looked unreliable); [INFERRED] my own conclusion.

## 1. Summary

1. The Mersenne record is still 2^136279841-1 (41,024,320 digits, 12 Oct 2024, 52 known Mersenne
   primes) as of Nov 2026. The Prime Pages top 20 has seven non-Mersenne entries, the newest a
   generalized Fermat prime 7172162^1048576+1 (Aug 2026) and the biggest non-Mersenne a GFN
   2524190^2097152+1 (13.4 M digits, Oct 2025). [SNIPPET]
2. Gaussian-Mersenne exponents (OEIS A057429): 41 terms, largest 15317227 (found 2023 by
   Propper and Batalov), search complete below 5,000,000. Eisenstein-Mersenne (A066408): 28 terms,
   largest exponent 4043119 (2023), next term > 4,400,000. [SNIPPET]
3. Chamberland (J. Integer Seq. 2003) is the source of "norm of a Gaussian-Mersenne prime q has a
   binary BBP formula for log q" and of the "generalized Gaussian-Mersenne primes" (numerators of
   exp(2 Re log Phi_m((1+i)/2)), checked for m < 3000). I read the paper. [READ] His list of
   primes with binary log formulas (which became OEIS A104885) contains 38737, which our project
   found to fail; the 38737 entry is thus traced to his Maple list (in the PDF). [READ]
4. The only theorem there is the sufficiency direction (a formula exists for each listed prime).
   Which primes have a formula is not claimed complete; OEIS A104885 says finiteness is unknown.
   Our Theorem K gives the iff, so the list can be audited completely. [INFERRED]
5. Mathlib has Lucas-Lehmer in both directions (necessity merged Aug 2025), Fermat numbers with
   Pepin, lifting the exponent, and the Lucas primality theorem; the Euclid-Euler theorem is an
   open PR (Oct 2026). It has no general "prime divisors of 2^p-1 are 1 mod 2p" theorem that I
   could find, no Wieferich file, no Gaussian-Mersenne file. [SNIPPET]
6. Primality certificates in Lean exist as community code: PrimeCert (Pocklington and a cube-root
   variant, Lean kernel only, no native_decide), a 78-digit Pratt/ECC chain certificate, and an
   unpolished Pratt generator in Mathlib's LucasPrimality file. ECPP certificates are not checked
   in Lean by anything I found. [SNIPPET]
7. Best leads: (a) audit all of A104885 and Chamberland's generalized list with Theorem K and
   machine-check each verdict; (b) formalize the elementary divisor facts of Gaussian-Mersenne
   norms, including a sharper congruence than the OEIS one (q = 1 mod 4p); (c) Lean-certified
   primality of small Gaussian/Eisenstein-Mersenne norms by Pocklington/BLS using cyclotomic
   factors of q-1.

## 2. What is known

### 2.1 Frontiers in 2026

- Largest known prime 2^136279841-1, 41,024,320 digits, found 12 Oct 2024 (GIMPS, GPU, cloud).
  Called "Mersenne 52?" on the Prime Pages list; the question mark is the unverified/not yet
  double-checked flag. [SNIPPET]
- Verification: all exponents below 100 million double-checked/tested at least once as of Dec
  2020 (Wikipedia digest). [SNIPPET]
- Top 20 (Prime Pages, as of Nov 2026): 10 Mersenne primes, 3 generalized Fermat (ranks 6, 15,
  20), 2 generalized unique primes (ranks 9, 10: 5166932^2097152 - 5166932^1048576 + 1 and
  4658592^2097152 - 4658592^1048576 + 1), a Proth prime 10223*2^31172165+1, a Riesel prime
  69*2^24612729-1, a generalized Cullen 4052186*69^4052186+1 (Apr 2025). Exponents were
  reconstructed from flattened text by the fetch tool; check before quoting. [SNIPPET]
- Generalized Fermat primes: PrimeGrid finds them continuously (GFN 131072 and 262144 families,
  new ones Jan to Oct 2026 in the Top 5000 list at about 1.1 M digits). Largest 2524190^2097152+1
  (13,426,224 digits, Oct 2025). Seven of the ten largest GFN primes are of the form F_20(a). [SNIPPET]
- Gaussian-Mersenne: exponents 2, 3, 5, 7, 11, 19, 29, 47, 73, 79, 113, 151, 157, 163, 167, 239,
  241, 283, 353, 367, 379, 457, 997, 1367, 3041, 10141, 14699, 27529, 49207, 77291, 85237,
  106693, 160423, 203789, 364289, 991961, 1203793, 1667321, 3704053, 4792057, 15317227 (A057429,
  41 terms). Terms 39, 40: Batalov 2014; term 41: Propper and Batalov, June 2023; search complete
  for exponents < 5,000,000 (comment of Sept 2014). The norm 2^15317227+2^7658614+1 has
  4,610,945 digits (MathWorld, Aug 2026). The Prime Pages glossary page still lists only 34
  exponents with largest 203789; it is stale. [SNIPPET]
- Eisenstein-Mersenne exponents (A066408): 2, 5, 7, 11, 17, 19, 79, 163, 193, 239, 317, 353, 659,
  709, 1049, 1103, 1759, 2029, 5153, 7541, 9049, 10453, 23743, 255361, 534827, 2237561, 2888387,
  4043119; the last two added June 2023 (Propper and Batalov); "next term > 4400000". The prime
  norms are in A066413 (only 8 terms stored). [SNIPPET]
- Wagstaff primes (2^p+1)/3 (A000978): 3, 5, 7, ..., 138937 are proven or PRP depending on the
  size; terms from a(32) on (exponent 95369 onward) were only probable primes as of 2018; the
  largest listed PRP exponent is 4031399 (1,213,572 digits, Vrba-Reix PRP, Tony Reix); a(30) was
  proved with fastECPP by Morain; further PRP exponents 13347311, 13372531 (Propper 2013, "maybe
  not the next ones") and 15135397. [SNIPPET]
- Repunits in base 10: R_n prime for n = 2, 19, 23, 317, 1031, 49081, 86453, 109297 (proved by
  ECPP, May 2025), then PRPs R270343 (2007), R5794777 and R8177207 (2021, largest PRP). [SNIPPET]
- A066180: for each prime exponent prime(n), the smallest base b with (b^p-1)/(b-1) prime;
  entries n = 5 and 8..70 were certified with Primo (comment). Bases such as 606, 602, 304, 183
  occur. Last edit 2026-05-30. Whether a(n)=0 can occur is asked in the entry (open as stated). [SNIPPET]
- Generalized Gaussian-Mersenne primes (A207040, A088962): 31 terms from 5, 13, 29, 37, 41,
  61, ... up to 1759217765581, defined as the numerator of exp(2 Re log Phi_n((1+i)/2)). [SNIPPET]
- Aurifeuillian primitive parts: A250197 lists k such that the left Aurifeuillian part of 2^k+1
  is prime (10, 14, 18, 22, 26, 30, 42, ... 1926). [SNIPPET]
- Cunningham project: main tables as of 15 Nov 2026 are up to date (through #6901 on page 150),
  plain-text .txt files; "wanted" lists maintained. [SNIPPET]

### 2.2 Chamberland's paper (the link between these primes and BBP formulas) [READ]

I read the PDF (JIS vol. 6, article 03.3.7, 2003; extracted with pdftotext).
- Setup: constants C = sum p(k)/(q(k) b^k) have digit extraction in linear time; he recalls the
  conjecture that such constants are rational or normal. Log of an integer m has a binary BBP
  formula for every m of the form (2^a1-1)...(2^ah-1)/((2^b1-1)...(2^bj-1)), and by the
  Harley-Borwein idea via Re log(1 - ((+-1+i)/2^n)) more integers.
- Mechanism: Re log Phi_m((+-1+i)/2^n) and the analogue with (+-1+sqrt(-3))/2^n are linear
  combinations of expressions of that type by Moebius inversion; the numerators of
  exp(2 Re log Phi_m((1+i)/2)) are the "generalized Gaussian-Mersenne" numbers. For m = prime p
  = 4k+1 he shows the expression equals (1/2) log of the Gaussian-Mersenne norm minus a
  multiple of log 2, so log q has a binary BBP formula for every Gaussian-Mersenne norm q.
- Example identities quoted: Re log Phi_6((1+i)/16) = (1/2)[log 14449 - 14 log 2] (so 14449 is
  admitted); Re log Phi_5((1+sqrt(-3))/4) = (1/2)[log 331 - 8 log 2].
- Table of primes with log formulas, 2 up to about 8.7e53, found "by modest Maple calculations";
  the list includes 38737 and also 524287, 599479 (from a product identity with 7 and 23*89 and
  44 log 2), 2796203, and about 60 larger entries. Products of two primes also occur (23*89 etc.).
- Statement: log 23 is not of the form (1) (Pomerance), and it is "still unknown" to him whether
  log 23 has a binary BBP formula. Our project settles this: log 23 has none.
- Generalized Gaussian-Mersenne list for m < 3000 (his own list, 2, 3, 4, 5, 7, 9, 10, ... 2995);
  m = 2995 gives a prime with over 700 digits.
- Section 3: Aurifeuillian factorizations: a theorem expressing Phi_{mn}(x) as a product over
  primitive m-th roots of unity of Phi_n(x zeta_j), applied to Phi_{4n}(x) = Phi_n(ix)Phi_n(-ix)
  for odd n, explaining why products of the "+-" norms 2^(2n-1) +- 2^n + 1 duplicate entries
  (2^(4n-2)+1 = (2^(2n-1)+2^n+1)(2^(2n-1)-2^n+1)).
- Nothing in the paper proves that the set of listed primes is complete. [READ, as to the
  paper's text]

OEIS A104885 ("Primes whose logarithms are known to possess binary BBP formulas") reproduces the
first 46 terms of this list and says that finiteness is unknown; mentions PSLQ discovery; has no
correction note and does not mention Chamberland. [SNIPPET]

### 2.3 Primality tests and papers

- Berrizbeitia and Iskra, "Gaussian Mersenne and Eisenstein Mersenne primes", Math. Comp. 79
  (2010) 1779-1791: a Lucas-Lehmer-type deterministic test for the Gaussian-Mersenne norm from the
  biquadratic reciprocity law, and one for the Eisenstein-Mersenne norm from cubic reciprocity;
  searches for both families were run in 2004-2005. Full text not read (publisher gave 403). [SNIPPET]
- Palimar and Dukkipati, arXiv:1401.6656: if a Gaussian-Mersenne prime G_p is written x^2+7y^2
  then x = +-1 and y = 0 mod 8, via splitting in a cyclic quartic unramified extension of
  Q(sqrt(-14)); generalizes to d = 7 mod 24; second proof follows Lenstra-Stevenhagen's treatment
  of Mersenne primes. [READ abstract on arXiv]
- Denomme and Savin (J. Number Theory 2008): elliptic-curve primality tests for Fermat and
  related primes; Abatzoglou, Silverberg, Sutherland, Wong (2013): deterministic ECPP for a
  special sequence. [SNIPPET]
- Franke, Kleinjung, Morain, Wirth 2004: fastECPP; Morain 2007: asymptotically fast ECPP. [SNIPPET]

### 2.4 Elementary theorems about divisors

- For odd prime p, every prime divisor q of 2^p-1 satisfies q = 1 mod 2p and q = +-1 mod 8; if p
  = 3 mod 4 and 2p+1 is prime then 2p+1 divides 2^p-1; a Mersenne prime is never Wieferich;
  composite divisors of 2^p-1 are strong pseudoprimes to base 2. (Wikipedia digest.) [SNIPPET]
- Repunits: R_a | R_n if a | n; gcd(R_m, R_n) = R_gcd(m,n); composite length implies composite;
  Goormaghtigh conjecture (31 and 8191 are the only numbers that are repunits with at least 3
  digits in two bases) and Feit-Thompson conjecture (R_q(p) never divides R_p(q) for distinct primes
  p, q) are stated as open there. [SNIPPET]
- Fermat: odd prime divisors of a^(2^n)+1 are 1 mod 2^(n+1); for n > 1, divisors of F_n are
  1 mod 2^(n+2). [SNIPPET]
- OEIS A182300 comment (Ordowski 2019): each Gaussian-Mersenne norm q = 2^p +- 2^((p+1)/2) + 1
  satisfies q = 1 mod p. [SNIPPET] I can sharpen it by hand, see lead 2.

### 2.5 Conjectures and heuristics

- Lenstra-Pomerance-Wagstaff: infinitely many Mersenne primes; the number below x is about
  e^gamma log_2 log_2 x, giving about 5.92 exponents per decimal-digit length. The Wikipedia digest
  also gives a generalization to (a^p-b)/(a-b) and a sentence about "at least 12 versus 3.7
  expected" in a range of 220 to 285 million that I cannot reconcile with the 52 known primes;
  treat it as unreliable. [SNIPPET]
- New Mersenne conjecture (Bateman, Selfridge, Wagstaff 1989, Amer. Math. Monthly): for an odd
  prime p, any two of (i) p = 2^k +- 1 or 4^k +- 3, (ii) 2^p-1 prime, (iii) (2^p+1)/3 prime imply
  the third. Nine exponents satisfy all three (3, 5, 7, 13, 17, 19, 31, 61, 127); 89 and 107 only
  (ii). Reported verified for primes up to 10^7 in condition (i)... and a counterexample would
  need MM61 or MM127 style double Mersenne primes; both are composite. Selfridge regarded the
  conjecture as fit to data. [SNIPPET]
- Gaussian-Mersenne density: only the remark (Prime Pages, attributed to Oakes) that they occur with
  about the density of Mersenne primes; no precise heuristic found. [SNIPPET]
- Repunit prime conjecture: generalized repunits R_p(b) for b not a perfect power and not -4k^4
  follow a prime-number-theorem style density; infinitude is conjectural only. [SNIPPET]
- A252503: conjecture that for every n that is not 2^k (k > 5) there is a prime p with Phi_n(p)
  prime; zeros for n = 2^k mean "none found" (A252503; Bunyakovsky-type). [SNIPPET]
- Provable pieces: none of the infinitude statements is provable with known tools. [INFERRED]

### 2.6 Formalization and certificates

- Mathlib: `mersenne`, `lucas_lehmer_sufficiency` and `lucas_lehmer_necessity` (converse merged
  2025, PR 26272), `Nat.Prime.of_mersenne` (prime exponent), `legendreSym_mersenne_two/three`,
  `mersenne_mod_eight`; the Archive file certifies exponents up to 4423; a `norm_num` extension
  evaluates the test. The Euclid-Euler theorem is PR 44848 (open Oct 2026). [SNIPPET]
- Mathlib.NumberTheory.Fermat: pairwise coprimality, Pepin's test, prime factors of F_n of the form
  k 2^(n+2)+1, `Nat.pow_of_pow_add_prime`, `Nat.prime_of_pow_sub_one_prime`. [SNIPPET]
- Multiplicity.lean: lifting the exponent for odd p and p = 2, geometric-sum divisibility; no
  Zsigmondy there. LucasPrimality.lean: `lucas_primality`, `reverse_lucas_primality`, iff; a TODO
  to integrate Pratt certificates into norm_num primality. [SNIPPET]
- Open Mathlib PR 46022 (Nov 2026): Stickelberger's theorem on Gauss sums (cyclotomic fields);
  PR 38606: preparation for vanishing sums of roots of unity. [SNIPPET]
- PrimeCert (b-mehta): Pocklington plus cube-root variant, macro `prime_cert%`, certificates need a
  full or partial factorization of N-1 (Python script via sympy/factor/ECM), only Lean kernel; no
  size data in the README (example: 60 digits). [SNIPPET]
- wjbrob/secp256k1-primality-lean: Pratt certificates with kernel-evaluated `powMod`, primes up to
  78 digits in about a minute of build, no native_decide, axioms only propext, Classical.choice,
  Quot.sound. [SNIPPET]
- lfrmrc-pixel/mills-forest: ECPP certificates stored as files, verified with PARI/GP
  primecertisvalid or Primo, not in Lean; Lean checks only the deduction. [SNIPPET]
- A Zulip thread (2025-26) refers to an unpolished Pratt certificate generator by Himmel in
  LucasPrimality.lean; an arXiv paper (2608.08643) is quoted to use `lucas_primality` with
  `reduce_mod_char`, reporting that plain norm_num trial division at about 2^31 steps costs an hour
  of build. (The arXiv abstract itself does not mention this; the digest came from a search result.) [SNIPPET]
- Formal Conjectures (DeepMind) tree: first 100k characters showed no Mersenne/Wagstaff/Fermat/
  repunit/Wieferich file; list truncated, not conclusive. [SNIPPET]
- Certificate formats: Primo (ECPP, text, verified by Primo and PARI), PARI/GP `primecert`
  (fastECPP/CM), Pratt (needs factorization of p-1, Mathlib theorem exists), Pocklington/BLS
  (partial factorization of N-1, PrimeCert). Lean checking exists for the last two and for Pratt;
  none found for ECPP. [INFERRED from the above]

## 3. What is open

- Infinitely many Mersenne / Gaussian-Mersenne / Eisenstein-Mersenne / Wagstaff / repunit /
  generalized-Fermat primes: open, stated so in all sources. Fermat primes beyond F_4: open; the
  heuristic gives probability under 1e-9 (Boklan-Conway), via Wikipedia digest. [SNIPPET]
- Whether the set of primes with a binary BBP log formula is finite or infinite (OEIS A104885
  comment, stated open). With our Theorem K this question becomes one about the primes y with a
  certain finite test; I did not find any paper after 2003 that decides it. [INFERRED]
- Whether A066180 can contain 0 (a(n) = 0): asked in the entry. [SNIPPET]
- Goormaghtigh and Feit-Thompson conjectures (repunits): open as stated there. [SNIPPET]
- Whether the A252503 conjecture is true for n > 32 powers of 2 (e.g. Phi_{2^k}(p) prime): open. [SNIPPET]
- Exhaustive Gaussian-Mersenne search is complete only up to 5,000,000; Eisenstein up to about
  4.4 million; these are search limits, not theorems. [SNIPPET]
- Not found by me: any formal statement of a conjectured density of Gaussian-Mersenne primes; any
  formalization of Gaussian-Mersenne primes; Lean checking of ECPP certificates. Searched: OEIS,
  Prime Pages, Mathlib docs and PR list, GitHub repository search (two queries), Formal
  Conjectures tree (partial).

## 4. Leads for this project, ranked

**Lead 1: audit of the Chamberland list with Theorem K.**
Statement: for every prime y in OEIS A104885 / Chamberland's table (up to 8.7e53, about 90 primes
plus the products), decide with the finite prime test whether log y has a binary BBP formula, and
record failures (38737 already fails) with a machine-checked verdict, for each by the formal iff
of Theorem K. Also the m < 3000 generalized Gaussian-Mersenne list and A207040/A088962.
Why it fits: Theorem K is formal for every positive rational y; the test is finite. Missing:
the primes themselves are known only as decimal numbers; need a small script plus Lean `decide`
or `norm_num` data per prime. Size: days. Noticeable because the OEIS entry names the set "known
to possess" formulas and may contain more errors; a correction submitted with a certificate is a
tangible, checkable contribution and also cites Chamberland's 2003 table as the origin.
Caution: my report cannot say which other entries fail; 38737 is the only one known to the
project. Two cases to look at: each entry 2^a+-1-type products, and entries obtained through the
6th and 5th cyclotomic evaluations (14449, 331, 599479).

**Lead 2: elementary divisor theory of Gaussian-Mersenne norms, formalized.**
Statement (proved by hand below, not yet in Lean): for an odd prime p put q = 2^p +- 2^((p+1)/2) + 1
(the sign chosen so that this is N((1+-i)^p-1)). Then q divides 2^(2p)+1 (the Aurifeuillian
identity 2^(2p)+1 = (2^p+2^((p+1)/2)+1)(2^p-2^((p+1)/2)+1)). If q is prime, the order of 2 mod q
divides 4p and does not divide 2p, so it is 4 or 4p; order 4 gives q | 15, i.e. q = 5, so for q > 5
the order is 4p and q = 1 mod 4p. This strengthens the OEIS comment q = 1 mod p (A182300) and gives
a Euler-type criterion for prime divisors of these norms; also every prime divisor of such a q
is 1 mod 4p or small. [INFERRED] Together with Mathlib's Mersenne facts (mod 8, Legendre symbols)
a short Lean file: Aurifeuillian identity, order argument via `orderOf` in `ZMod q`, and the
Gaussian Mersenne norm. Size: days. Noticeable: no Gaussian-Mersenne file in Mathlib that I found.

**Lead 3: formal certified primality of small Gaussian-/Eisenstein-Mersenne norms, Wagstaff
and the first repunit primes.**
Statement: Lean-check `Nat.Prime` of all 12 listed Gaussian-Mersenne norms (up to 54 digits,
A182300) and the 8 Eisenstein-Mersenne norms (up to 78 digits, A066413) plus Wagstaff primes up to
modest exponent. Method: for q = 2^p +- 2^((p+1)/2)+1, q-1 = 2^((p+1)/2) (2^((p-1)/2) +- 1) and the second
factor splits by cyclotomic polynomials (explicit algebraic factors), so a Pocklington/BLS
certificate with partial factorization is cheap; PrimeCert (or the 78-digit powMod trick of the
secp256k1 repository) can check it in the kernel. Missing: PrimeCert's size limits are not
documented; ECPP is not available, so general repunits R_n in base 10 beyond about 100 digits
need a Pocklington partial factorization of R_n-1 (hard) or are out. Size: 1 to 2 weeks. Noticeable:
supplies a verified fragment of OEIS tables and Lean test cases for PrimeCert.

**Lead 4: statement-level formalization of the conjectures (no proofs).**
Statements: Lenstra-Pomerance-Wagstaff as an asymptotic count; New Mersenne conjecture (three
conditions); Chamberland's "generalized Gaussian-Mersenne"; and the bridge theorem "if q is a
Gaussian-Mersenne norm then log q has a binary BBP formula of the stated form" (proved there in
a few lines, our Part-I machinery handles the formula side). The bridge could be proved fully in
Lean now; the conjecture statements are definitional. The Formal Conjectures repository seems to
lack them (partial tree seen). Size: 1 week. Noticeable: the bridge theorem is a clean, checkable
theorem that ties the project's logarithm criterion to Mersenne-type primes.

**Lead 5: the converse of Chamberland's bridge.**
Statement: for which primes y does log y have a binary BBP formula, expressed in terms of
cyclotomic evaluations Phi_m((1+i)/2^n)? Our criterion K already decides each y; the question is
whether every y satisfying K appears as a prime factor of a numerator in his family, i.e. whether
his family is complete. This is a structural theorem about the prime ideals of Z[zeta] above 2
and Baker's theorem (the project's tools). Size: weeks, unclear; not stated as open by Chamberland
(only that his list was computed). Worth noticing if true.

**Lead 6: extending tables.** A057429 is complete to 5e6 and A066408 to 4.4e6 by large searches;
nothing here is cheaply extendable on one 24-core machine (each test at p about 1.5e7 needs days of GPU/CPU
time and Prime95/LLR). A090-type small items like A066180 beyond n=300 or A250197 beyond 1926
are feasible but low value. Size: days, low value. [INFERRED]

## 5. Overlap or conflict with section 1 of the rules

- Chamberland's paper asserts, and OEIS A104885 inherits, that 38737 and other entries of the
  list have binary BBP formulas; the project's finding that 38737 fails conflicts with the table
  in the PDF (list line: "...26317, 38737, 43691..." [READ]). I did not see a published correction.
  His text says the Maple search was a "modest calculation" and that he proves
  only the families, so the entry may come from a software or cancellation error; I did not find
  out which. [INFERRED]
- His statement that it is unknown whether log 23 has a binary BBP formula is answered by the
  project (no). OEIS A104885 comment on finiteness is open as written. [READ / SNIPPET]
- No conflict with the base-3, base b >= 5 or "only powers of 2" results; this thread is only
  adjacent through Chamberland's constants sum p(k)/(q(k) b^k) with b = 2^l.
- Prime Pages glossary page on Gaussian Mersenne primes is stale (34 exponents, largest 203789)
  against OEIS (41 terms, 15317227). Not a conflict with the project.

## 6. Sources

- https://t5k.org/top20/page.php?id=3 and https://en.wikipedia.org/wiki/Largest_known_prime_number
- https://oeis.org/A057429, A182300, A066408, A066413, A088962, A207040, A104885, A165132,
  A000978, A066180, A250197, A252503 (via oeis.org/search?q=...&fmt=json)
- http://eudml.org/doc/51705 (record) and the paper PDF at
  https://cs.uwaterloo.ca/journals/JIS/VOL6/Chamberland/chamberland60.pdf (read with pdftotext)
- https://t5k.org/glossary/xpage/GaussianMersenne.html ; https://mathworld.wolfram.com/GaussianMersennePrime.html
- https://arxiv.org/abs/1401.6656 ; Berrizbeitia and Iskra, https://www.ams.org/journals/mcom/2010-79-271/S0025-5718-10-02324-0
- https://en.wikipedia.org/wiki/Mersenne_prime, /Repunit, /New_Mersenne_conjecture, /Wagstaff_prime,
  /Generalized_Fermat_number
- Mathlib docs: NumberTheory/LucasLehmer, LucasPrimality, Fermat, Multiplicity, PrimeCounting
- https://github.com/b-mehta/PrimeCert ; https://github.com/wjbrob/secp256k1-primality-lean ;
  https://github.com/lfrmrc-pixel/mills-forest
- https://homes.cerias.purdue.edu/~ssw/cun/index.html ; http://factordb.com/api (query 2^127-1)
- Zulip archive: Practical ways to prove Nat.Prime N

Page-content note: no page addressed instructions to me.

## 7. Search log

WebSearch (4 calls)
1. largest known Mersenne prime 2026 GIMPS
2. PrimeGrid generalized Fermat prime 2026 discovery Eisenstein-Mersenne Gaussian-Mersenne
3. Gaussian Mersenne and Eisenstein Mersenne primes Berrizbeitia Iskra
4. Lean 4 Mathlib verified primality certificate Pratt Pocklington norm_num

Endpoint / page queries (fetch tool)
1 OEIS q=Gaussian Mersenne; 2 t5k top20 id=3 (redirect); 3 arXiv API all:"Gaussian Mersenne" (429);
4 arXiv API BBP and Mersenne (429); 5 Crossref Chamberland query; 6 t5k top20 (read); 7 Wikipedia
Largest known prime; 8 OEIS A182300; 9 OEIS repunit primes base; 10 Semantic Scholar (429);
11 OpenAlex (429); 12 OEIS A057429; 13 Wikipedia Mersenne prime; 14 Wikipedia Repunit; 15 Crossref
LPW; 16 zbMATH Gaussian Mersenne; 17 GitHub repos lucas-lehmer lean4 (0 results); 18 EuDML 51705;
19 Mathlib LucasLehmer docs; 20 GitHub issues Mersenne mathlib4; 21 GitHub repos primality
certificate lean; 22 arXiv abs 1401.6656; 23 AMS Berrizbeitia-Iskra (403); 24 EMIS Chamberland
(redirect); 25 mills-forest repo; 26 secp256k1-primality-lean repo; 27 Mathlib LucasPrimality;
28 GitHub repos Pocklington (0 results); 29 JIS Chamberland html; 30 OEIS A104885; 31 OEIS
Eisenstein-Mersenne; 32 OEIS Wagstaff primes; 33 OEIS Phi_n(2) cyclotomic; 34 JIS PDF (read through
pdftotext); 35 OEIS A088962; 36 OEIS A207040; 37 OEIS A066408/A066413; 38 OEIS repunit base 3;
39 OEIS new Mersenne; 40 OEIS Wieferich Fermat; 41 Crossref ECPP records; 42 t5k Gaussian Mersenne
glossary; 43 Wikipedia New Mersenne conjecture; 44 Wikipedia Wagstaff prime; 45 Wikipedia
generalized Fermat; 46 Mathlib Fermat; 47 GitHub code search formal-conjectures (401); 48 formal-
conjectures git tree; 49 GitHub issues Wieferich/Zsigmondy/cyclotomic mathlib4; 50 erdosproblems.com
(digest returned nothing specific, no result recorded); 51 MathWorld Gaussian Mersenne prime
(through fetch tool; first 403 on another MathWorld-related request was not made, only this
request); 52 OEIS A066180; 53 PrimeCert repo; 54 arXiv abs 2608.08643; 55 Zulip Practical ways;
56 OEIS Phi cyclotomic prime; 57 OEIS A252503; 58 Cunningham project page; 59 factordb API;
60 Mathlib Multiplicity; 61 OEIS Wieferich/Aurifeuillian (empty); 62 OEIS A250197; 63 Mathlib
PrimeCounting.

Totals: WebSearch calls 4; endpoint/page queries 63 (of which 5 refused: arXiv x2, Semantic
Scholar, OpenAlex with HTTP 429; AMS 403; GitHub code search 401; MathWorld ok).
Items read in full or substantially: Chamberland PDF, OEIS A057429/A066408/A104885/A207040/A066180,
Wikipedia Mersenne/New Mersenne/Repunit pages, Mathlib LucasLehmer/Fermat/LucasPrimality/Multiplicity
pages, secp256k1 repo, PrimeCert README, Prime Pages top 20.
