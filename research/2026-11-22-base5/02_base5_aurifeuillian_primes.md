# Base 5: Aurifeuillian factors, primitive primes, unique primes (literature lookup, 2026-11-22)

Tags: [READ] = read in the source text (fetched page, or the PDF converted to text); [SNIPPET] = search-result snippet only; [INFERRED] = my own deduction or arithmetic.
Caveat: web pages were read through a fetch tool that returns a model-made summary, not raw HTML, so "READ" for web pages means "the fetch summary of the page". Only the Wagstaff slides PDF was read as raw text (pdftotext).
Not opened: Granville-Pleasants, the Brillhart et al. book, Brent's paper, Schinzel 1962, Stewart 1977 (no full text found).

## 1. Aurifeuillian factorization for base 5

Your formula is correct.
- Wagstaff slides (SIAM, 27 Mar 2015), p.16: 5^(5(2k-1)) - 1 = (5^(2k-1) - 1) * L * M, with L, M = 5^(2(2k-1)) + 3*5^(2k-1) + 1 -/+ 5^k (5^(2k-1)+1). [READ] https://www.cs.purdue.edu/homes/ssw/aurif/but.pdf
  With h = 2k-1 this is exactly your L, M, since k = (h+1)/2. [INFERRED]
- Check h = 1: 41 -/+ 30 gives 11 and 71. [INFERRED arithmetic]. The slides' Table 5- lists n=5 as L=11, M=71. [READ]
- Wikipedia, same formula in other notation: 5^(10k+5) - 1 = F*(C-D)*(C+D), F = 5^(2k+1) - 1, C = 5^(4k+2) + 3*5^(2k+1) + 1, D = 5^(3k+2) + 5^(k+1). [READ, fetch summary] https://en.wikipedia.org/wiki/Aurifeuillean_factorization (D = 5^(k+1)(5^(2k+1)+1), matching the slides. [INFERRED])
- Cunningham notation: L = minus sign, M = plus sign (slides p.15, stated for base 3, same convention for 5). [READ]
- Slides p.18: for odd prime b, the Aurifeuillian factorization is for b^(b(2k-1)) - 1 when b = 1 mod 4 and for b^(b(2k-1)) + 1 when b = 3 mod 4. [READ]
- General rule (Wikipedia): write b = s^2 * t with t squarefree. If t = 1 mod 4 and n = t mod 2t (n an odd multiple of t), then b^n - 1 has it; if t = 2 or 3 mod 4 and n = 2t mod 4t, then b^n + 1 has it. [READ, fetch summary]. Your belief (b = 1 mod 4 needs n an odd multiple of b) is right for squarefree b; for non-squarefree b the squarefree part t is what counts.
- Table 5- of the slides (p.17): n=5: L 11, M 71; n=15: L (5M) 181, M (5L) 1741; n=25: L 9384251, M 101.251.401. [READ] I did not work out what the "(5M)" and "(5L)" tags mean; check the Cunningham book introduction.
- History: Aurifeuille/Lucas (1870s); Schinzel 1962 found more cases; Granville-Pleasants (Math. Comp. 75 (2006) 497-508, doi 10.1090/S0025-5718-05-01766-7) showed Schinzel found all such identities under their definition. [READ in the slides, p.19-20 (slides say 2007); the citation details are SNIPPET]

## 2. Do both Aurifeuillian factors have a prime of order exactly n?

What the sources say:
- Slides p.18: Aurifeuillian factorizations cut across the cyclotomic ones and can show that certain b^n +/- 1 have at least two primitive prime factors. The example given is base 3 (3^27+1 has 19441 and 19927). [READ]
- Schinzel 1962: for a, b coprime with ab a square or twice a square, the largest prime factor of a^n - b^n exceeds 2n+1, with exceptions n = 4, 6, 12 for a=2, b=1; at least two primitive divisors, using an Aurifeuillian factorization of Phi_n. [SNIPPET, from a search summary citing Stewart 2013 and Voutier; primary paper not opened]. That hypothesis (ab a square or twice a square) does NOT cover a=5, b=1 (ab = 5), so as quoted it is not a base-5 statement. [INFERRED]
- Stewart 1977 (Transcendence Theory, Academic Press, pp. 79-92): effective version for Lucas and Lehmer numbers with finitely many exceptions. [SNIPPET] Not a statement about L and M separately.
- I found NO source stating, for base 5, that each of L and M has a prime p with ord_p(5) = n.

My own argument (not from any source, gaps flagged) [INFERRED]:
- A prime p dividing Phi_n(5) with ord_p(5) != n must be the largest prime factor P of n and divides Phi_n(5) exactly once (P odd). p = 5 never divides Phi_n(5), since Phi_n(5) = 1 mod 5.
- So if L_n and M_n are coprime and both larger than P, each has a primitive prime factor. For the full product Phi_5(5^h) = L*M (which contains all Phi_{5d}(5), d | h), L and M are coprime: M - L = 2*5^k*(5^h+1), and a common odd prime p != 5 would divide 5^h+1, but then Phi_5(5^h) = 1 mod p; p = 2 is excluded as the value is odd. I checked this only for the full product. For the individual Phi_n(5) with finer splitting, coprimality and sizes are NOT checked. So: plausible, proved by me only for the full product, not for each Phi_n(5).
- Data point: A143665 gives 11 for n=5 and 181 for n=15 as the least prime of order n [READ], consistent with these being primitive primes of the L parts.

## 3. Zsigmondy for base 5

- Statement: for coprime a > b > 0 and n >= 1, a^n - b^n has a primitive prime divisor except for n=1 with a-b=1, n=2 with a+b a power of 2, and n=6 with a=2, b=1. [READ, fetch summary] https://en.wikipedia.org/wiki/Zsigmondy%27s_theorem
- For a=5, b=1: n=1 gives 4 (a-b is not 1) and n=2 gives a+b = 6 (not a power of 2), so no exceptions: 5^n - 1 has a primitive prime factor for every n >= 1. [INFERRED from the statement]

## 4. Unique primes in base 5, and OEIS

- No OEIS sequence found listing primes p such that no other prime has the same order of 5. Two searches, nothing. [SNIPPET, negative result, not exhaustive]
- Closest: A306074, "Bases in which 5 is a unique-period prime": nontrivial bases 2, 3, 7, plus the families 5^t+1 and 2^s*5^t-1; the comments say the family pattern holds for any odd prime p. [READ, fetch summary] https://oeis.org/A306074. Siblings: A000051 (p=2), A306073, A306075, A306076, A306077. A040017 is base 10 unique-period primes. A144755 is listed there as a base-2 related sequence. [READ]
- A143665, least prime with ord_5 = n: 2, 3, 31, 13, 11, 7, 19531, 313, 19, 521, 12207031, 601, 305175781, 29, 181, 17, 409, 5167, 191, 41, ... ; a table to n = 520 by Alekseyev. [READ] https://oeis.org/A143665. Cross-refs: A064081 (Zsigmondy numbers a=5, b=1), A074479 (largest prime factor of 5^n-1). A211241 = order of 5 mod the n-th prime; A019335 = full reptend primes in base 5. [SNIPPET]
- Primes (5^k-1)/4: A086122 (31, 19531, 12207031, 305175781, ...), exponents A004061 (3, 7, 11, 13, 47, 127, ...; 19 known terms at snippet time). A088554 also. [SNIPPET] https://oeis.org/A086122 https://oeis.org/A004061
- Phi_k(5) prime: A138935, indices k = 3, 7, 10, 11, 12, 13, 24, 28, 47, 48, 49, 56, 57, 88, 90, 92, 108, 110, 116, 120, 127, 134, 141, 149, 161, 181, 198, 202, 206, 236, 248, 288, 357, 384, 420, 458, 500, 530, 536, 619, 620, 694, 798, 897, 929, 981, 992, 1064, 1134, 1230, 1670, 1807, 2094, 2369. A comment asks whether an odd multiple of 5 can occur. [READ, fetch summary] https://oeis.org/A138935. Values: A019323. Primes dividing Phi_5(k): A256153 [SNIPPET].
  No odd multiple of 5 appears in the list, as expected since Phi_n(5) = L*M is composite there (both factors > 1). [INFERRED]
- No OEIS sequence found for "an Aurifeuillian factor L or M of base 5 is prime". [SNIPPET, negative]. The slides' table shows L=11, M=71 (n=5) and L=181, M=1741 (n=15), all prime. [READ]

## 5. Cunningham project data

- Main page: https://homes.cerias.purdue.edu/~ssw/cun/index.html . Files named there: pmain1126.txt (main tables, as of 15 Nov 2026, all factors through #6901 on page 150), appa1126.txt, appc1126.txt, appc.txt, champ.txt. Page last modified 20 Nov 2026. [READ, fetch summary]. The page did not name a per-base exponent range or a separate 5^n-1 file; the exact file URLs are not verified (presumably relative to that directory). [INFERRED]
- Intro page: https://homes.cerias.purdue.edu/~ssw/cun/intro . Bases 2, 3, 5, 6, 7, 10, 11, 12; third edition (2002) of "Factorizations of b^n +/- 1", AMS Contemporary Mathematics 22, with electronic tables on the AMS site (conm/022). [READ, fetch summary]
- Exponent limit for base 5: a snippet cites 600 as of 2024-05-23, as a cap on the table range (source page not identified). [SNIPPET, weak]. Completeness boundary for base 5 is NOT established.
- The 5- table ends with Aurifeuillian formulae (stated in the Cunningham introduction, per a snippet). [SNIPPET]
- Brent rpb200 (https://maths-people.anu.edu.au/~brent/pd/rpb200.pdf) covers bases 13-99, not base 5. [SNIPPET]

## Open items
1. Fetch Granville-Pleasants and the Cunningham book introduction for the exact printed statement and the 5L/5M labelling.
2. Find or prove: each of L_n, M_n has a primitive prime for every odd multiple n of 5.
3. Get the n-range of completeness for base 5 from pmain1126.txt.
