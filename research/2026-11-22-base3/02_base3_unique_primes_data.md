# Base 3: unique primes, prime values, factor tables, Wieferich primes (data pass)

Date: 22 November 2026. Tags: [READ] page opened this session; [SNIPPET] search-result text only; [INFERRED]; [COMPUTED] our own script. WebSearch calls used: 3 of 30 (see search log).

## Key findings

1. **No OEIS sequence lists the base-3 unique primes.** There is no base-3 analogue of A144755 / A161508 / A161509 that I could find. The entries A161508, A161509, A072226 and A144755 do not mention base 3 in their cross-references [READ]. Search by terms (primes 2,5,7,11,13,41,61,73,547,757,1093,1181; indices 1,3,4,5,...,24) returned nothing [READ]. The nearest entries are A306073 (bases in which 3 is a unique-period prime; a different question) and A040017/A007615 (base 10) [READ]. So our list would be new as an OEIS item.
2. **[COMPUTED] Base-3 unique primes below 20000 (3 excluded):** 2, 5, 7, 11, 13, 41, 61, 73, 547, 757, 1093, 1181, 4561, 6481 (14 primes; orders n = 1, 4, 6, 5, 3, 8, 10, 12, 14, 9, 7, 20, 15, 24). Here "unique" means: after removing p and the primes dividing n, nothing is left of Phi_n(3). Primes 5, 41, 1181 are unique only up to the factor 2 or 5 dividing n; 11 because Phi_5(3) = 11^2 (Wieferich).
3. **[COMPUTED] Primes below 20000 alone in one Aurifeuillian half but not unique:** 19 and 37 (n = 18), 31 and 271 (n = 30), 43 and 2269 (n = 42), 19441 and 19927 (n = 54). Also 7 (n = 6, half M = 7, L = 1) is both unique and alone in a half. Phi_54(3) = 19441 * 19927 [COMPUTED]. Split exact: for every n = 6 mod 12 that occurs as an order of a prime below 20000 with phi(n) <= 240, gcd(Phi_n(3), L) * gcd(Phi_n(3), M) = Phi_n(3) exactly; no exceptions, no factor 3 [COMPUTED].
4. **The data agree with OEIS where they overlap.** Every prime value of Phi_k(3) below 20000 (A211874: 2, 7, 13, 61, 73, 547, 757, 1093, 4561, 6481) is in our unique list [COMPUTED vs READ]. The Eisenstein-Mersenne primes 7, 271, 2269 (A066413) are all alone in a half [COMPUTED vs READ]. The primes in A125743/A125744 and A239842 correspond to the halves: A239842 equals the union of A125743 and A125744 as sets of indices [INFERRED from the term lists: 5, 11, 31, 37, 47, 53, 97, ... each appears in one of the two]. A prime half gives a prime that is alone in its half.
5. **Wieferich in base 3:** only 11 and 1006003 are known (Mirimanoff primes, A014127); none others up to 9.7 * 10^14 (Dorais and Klyve) [READ]. Below 20000 only 11 [COMPUTED].
6. **Factor tables for base 3 are available.** The Cunningham main table file at Purdue (pmain1126.txt, dated 15 November 2026) has Table 3- (3^n - 1, odd n < 900) and Table 3+ (3^n + 1, n <= 900) with L/M split for n = 6k - 3 <= 1797 (i.e. m <= 599) [READ]. FactorDB can be queried by URL and has an API [READ]. Brent's pages point to factors.gz for a < 10000, n < 10000 (base 3 only through the Cunningham data, n up to about 1200) [READ, indirect].

## Q1. Unique primes in base 3

| Item | Result |
|---|---|
| Base-3 analogue of A144755 (sorted unique primes) | not found |
| Base-3 analogue of A161508 (k with one primitive prime factor of 3^k - 1) | not found |
| Base-3 analogue of A161509 | not found |
| Closest existing | A306073 "Bases in which 3 is a unique-period prime" (2, 4, 5, 8, 10, 11, 17, 23, 26, 28, 35, 47, 53, 71, 80, ...) [READ]; A306074 to A306077 same for 5, 7, 11, 13 [READ] |
| General definition | Wikipedia "Unique prime": a prime is unique when no other prime has the same period length for 1/q; Yates 1980; equivalent to some Phi_n(b) being a power of p [SNIPPET]. |

Base-2 originals, for comparison [READ]: A144755, author Vladimir Shevelev, Sep 2008 (created Jan 2009, revised 2024), 38 terms, the sorted version of A161509 (note by Alekseyev that sorting a finite part cannot prove no terms were skipped). A161508 and A161509: T. D. Noe, 17 June 2009; data fields 66 and 36 terms, b-files with 179 terms. A072226: Reiner Martin, 4 July 2002; 65 terms in data, b-file 289 terms. None cross-references a base-3 version.

Useful base-3 relatives that do exist:

| A-number | Name (as read) | Author, year | Terms | Notes |
|---|---|---|---|---|
| A129733 | List of primitive prime divisors of (3^k-1)/2 (A003462) for k >= 2, in order of occurrence | N. J. A. Sloane, 2007 | 44 in data; b-file 2636 terms (Alekseyev; covers k <= 730) | first 20: 2, 13, 5, 11, 7, 1093, 41, 757, 61, 23, 3851, 73, 797161, 547, 4561, 17, 193, 1871, 34511, 19. Not grouped by k, so does not isolate uniqueness. Base-2 counterparts named: A108974. b-file: https://oeis.org/A129733/b129733.txt (named in the entry; not opened) |
| A019321 | Cyclotomic polynomials at x = 3 | | | 3, 2, 4, 13, 10, 121, 7, 1093, 82, 757, 61, 88573, 73, 797161, 547 (from n = 0 offset as printed) |
| A306073 | Bases in which 3 is a unique-period prime | | | different question |

[COMPUTED] Table of the 14 unique primes below 20000, with Phi_n(3):

| p | n = ord_p(3) | Phi_n(3) |
|---|---|---|
| 2 | 1 | 2 |
| 5 | 4 | 10 = 2 * 5 |
| 7 | 6 | 7 |
| 11 | 5 | 121 = 11^2 |
| 13 | 3 | 13 |
| 41 | 8 | 82 = 2 * 41 |
| 61 | 10 | 61 |
| 73 | 12 | 73 |
| 547 | 14 | 547 |
| 757 | 9 | 757 |
| 1093 | 7 | 1093 |
| 1181 | 20 | 5905 = 5 * 1181 |
| 4561 | 15 | 4561 |
| 6481 | 24 | 6481 |

Remark [INFERRED]: this list is the primes 7, 13, 61, 73, 547, 757, 1093, 4561, 6481 (prime values of Phi_n(3)) plus 2, 5, 11, 41, 1181 (prime power or prime times the intrinsic prime). The next candidates in A138933 (indices with Phi_k(3) prime: 21, 24, 26, 33, ...) give larger unique primes, e.g. 368089, 398581, 530713, 797161 from A211874 [READ].

## Q2. Prime values

| Topic | A-number | Exact name | Author, year | Terms and extent |
|---|---|---|---|---|
| n with Phi_n(3) prime (base-3 analogue of A072226) | A138933 | "Indices k such that A019321(k)=Phi[k](3) is prime, where Phi is a cyclotomic polynomial." | M. F. Hasler, 3 Apr 2008 | 58 terms in data, last ones 747, 760, 782, 828, 875, 892, 974, 984; b-file n = 1..167 (Robert Price): https://oeis.org/A138933/b138933.txt. Probable primes (PARI uses a pseudoprime test). First 40: 1, 3, 6, 7, 9, 10, 12, 13, 14, 15, 21, 24, 26, 33, 36, 40, 46, 60, 63, 70, 71, 72, 86, 103, 108, 130, 132, 143, 145, 154, 161, 236, 255, 261, 276, 279, 287, 304, 364, 430 [READ] |
| Prime values | A292007 | "Primes of the form Phi(k, 3), where Phi is the cyclotomic polynomial." | Robert Price, 7 Sep 2017 | 23 terms; b-file 1..39. A211874 (Alexander Gruber, 12 Feb 2013) sorted, 24 terms: 2, 7, 13, 61, 73, 547, 757, 1093, 4561, 6481, 368089, 398581, 530713, 797161, 42521761, 47763361, 2413941289, 23535794707, 282429005041, 374857981681, 144542918285300809, 150094634909578633, 13490012358249728401, 82064241848634269407 [READ] |
| (3^n - 1)/2 prime | A028491 | "Numbers k such that (3^k - 1)/2 is prime." | N. J. A. Sloane, Jean-Yves Perrier | 23 terms: 3, 7, 13, 71, 103, 541, 1091, 1367, 1627, 4177, 9011, 9551, 36913, 43063, 49681, 57917, 483611, 877843, 2215303, 2704981, 3598867, 7973131, 8530117; later terms are probable primes; no b-file [READ] |
| (3^n + 1)/4 prime | A007658 | "Numbers k such that (3^k + 1)/4 is prime." | N. J. A. Sloane, Robert G. Wilson v | 29 terms: 3, 5, 7, 13, 23, 43, 281, 359, 487, 577, 1579, 1663, 1741, 3191, 9209, 11257, 12743, 13093, 17027, 26633, 104243, 134227, 152287, 700897, 1205459, 1896463, 2533963, 2674381, 7034611 (last added Dec 2024); no b-file [READ] |
| Eisenstein-Mersenne exponents | A066408 | "Numbers n such that the Eisenstein integer (1 - w)^n - 1 has prime norm, where w = -1/2 + sqrt(-3)/2." | Mike Oakes | 28 terms: 2, 5, 7, 11, 17, 19, 79, 163, 193, 239, 317, 353, 659, 709, 1049, 1103, 1759, 2029, 5153, 7541, 9049, 10453, 23743, 255361, 534827, 2237561, 2888387, 4043119; "next term > 4400000" [READ] |
| Eisenstein-Mersenne primes | A066413 | "Eisenstein-Mersenne primes: primes of the form ((3 +/- sqrt(-3))/2)^p - 1." | Mike Oakes | 8 terms: 7, 271, 2269, 176419, 129159847, 1162320517, then two of 38 and 78 digits (exponents 2 to 163) [READ] |
| 3^p - 3^((p+1)/2) + 1 over 7 prime | A125743 | "Primes p such that (3^p - 3^((p + 1)/2) + 1)/7 is prime." | Alexander Adamchuk, 4 Dec 2006 | 13 terms: 5, 31, 53, 163, 509, 1061, 13627, 20047, 28411, 50993, 71453, 272141, 1353449 [READ] |
| 3^p + 3^((p+1)/2) + 1 over 7 prime | A125744 | "Primes p such that (3^p + 3^((p + 1)/2) + 1)/7 is prime." | Alexander Adamchuk, 4 Dec 2006 | 14 terms: 11, 37, 47, 97, 167, 877, 2027, 2293, 3011, 6803, 8423, 50221, 152809, 505823 [READ] |
| Eisenstein norm of ((1-w)^k + 1)/(2 - w) prime | A239842 | "Numbers k such that the Eisenstein integer ((1-ω)^k+1)/(2-ω) has prime norm, where ω = - 1/2 + sqrt(-3)/2." | Serge Batalov, 27 Mar 2014 | 27 terms: 5, 11, 31, 37, 47, 53, 97, 163, 167, 509, 877, 1061, 2027, 2293, 3011, 6803, 8423, 13627, 20047, 28411, 50221, 50993, 71453, 152809, 272141, 505823, 1353449; proved prime only up to a(19) = 20047; a(28) > 1,500,000 [READ] |
| Gaussian-Mersenne (base-2 neighbour) | A057429 | "Numbers n such that (1+i)^n - 1 times its conjugate is prime." | R. G. Wilson V, 2000 | 41 terms, complete below 5,000,000 (Batalov 2014) [READ] |
| Primes with ternary BBP formula known | A165132 | "Primes whose logarithms are known to possess ternary BBP formulas." | Jaume Oliver Lafont, 4 Sep 2009 | 6 terms: 2, 3, 5, 7, 11, 13 [READ] |

Notes [INFERRED]: in A125743/A125744 the division by 7 removes Phi_6(3) = 7 from 3^(3p)+1 (p odd prime index in the cube-split), so the quotient is the full half of Phi_{6p}(3); this matches A239842 being the union. In A239842's data the terms 5, 31, 53, ... (from A125743) and 11, 37, 47, ... (from A125744) interleave, as expected.

## Q3. Factor tables

| Source | URL | Coverage | Opened? |
|---|---|---|---|
| Cunningham project main tables (Wagstaff, Purdue) | https://homes.cerias.purdue.edu/~ssw/cun/pmain1126.txt | Text file, about 1.0 million characters, as of 15 Nov 2026. Table 3-: 3^n - 1, odd n < 900. Table 3+: 3^n + 1, n <= 900, with L,M sub-table for n = 6k - 3 <= 1797 (formula 3^(3h)+1 = (3^h+1) L M, L = 3^h - 3^k + 1, M = 3^h + 3^k + 1, h = 2k-1). Sample rows: n = 9 gives L 19, M 37; n = 15 gives L 31 (with 3), M 271. Last composite shown in Table 3+: n = 899 with a 267-digit composite. Notation: P(d) probable prime, C(d) composite, parentheses list algebraic factors | yes (read in slices; table 2LM for base 2 also present, n = 4k-2 < 3000) |
| Purdue index page | https://homes.cerias.purdue.edu/~ssw/cun/index.html | Links: pmain1126.txt, appa1126.txt, appc1126.txt, Third Edition index, old pages, paper on Aurifeuillian-like factorizations (Integers 12A, 2012) | yes |
| Cunningham Book, 3rd edition page | https://homes.cerias.purdue.edu/~ssw/cun/third/index.html | Bases 2, 3, 5, 6, 7, 10, 11, 12; files dated 18 Sep 2001 (older) | yes |
| Brent's factor page | https://maths-people.anu.edu.au/~brent/factors.html | Brent-Montgomery-te Riele tables cover 13 < a < 99; base 3 only via Cunningham data, n up to about 1200; combined file factors.gz (a < 10000, n < 10000), format not described on the page | yes (page); the files themselves not opened |
| FactorDB | http://factordb.com/index.php?query=3%5E100-1 ; API at factordb.com/api.php and JSON-RPC | Any number; 3^100 - 1 shows fully factored with algebraic factors listed (primitive parts C(100,3)/5 etc.) | yes (one query) |
| OEIS attachment, base 2 only | A250197 (Eric Chen, 18 Jan 2015): "Factorization of Phi_n(2) for n up to 1280" by Chen and Palameta | no base-3 counterpart found | yes (entry) |
| Brent-Montgomery-te Riele original (Brent's file rpb134, "pub134.html") | named on Brent's page | not for base 3 | not opened |

## Q4. Wieferich in base 3

A014127 "Mirimanoff primes: primes p such that p^2 divides 3^(p-1) - 1" [READ]. Author N. J. A. Sloane, later edited by Max Alekseyev. Terms: 11, 1006003 (the second attributed to K. E. Kloss, 1965). Search limit: no further terms up to 9.7 * 10^14 (Dorais and Klyve). Also: such primes divide the numerator of the harmonic number H(floor(p/3)). Consequence [INFERRED]: Phi_5(3) = 121 = 11^2 (order 5, unique prime with exponent 2); for 1006003 the order n of 3 mod p is large, so the primitive part of Phi_n(3) can contain p^2 there [INFERRED; order not computed].

## Q5. Computation [COMPUTED]

Script (kept in the scratchpad, not in the project): for each prime p < 20000, p != 3, compute n = ord_p(3); skip when phi(n) > 240 (1946 primes; Phi_n(3) > 3^(phi-2) > 10^56, which cannot be p^a times a prime dividing n, since the only base-3 Wieferich prime below 20000 is 11). For phi(n) <= 120: strip p and all primes dividing n from Phi_n(3) (via sympy.cyclotomic_poly); p is unique if 1 remains. For n = 6 mod 12 with phi(n) <= 240: m = n/6, L = 3^m - 3^((m+1)/2) + 1, M = 3^m + 3^((m+1)/2) + 1; g1 = gcd(Phi_n(3), L), g2 = gcd(Phi_n(3), M); check g1 * g2 = Phi_n(3); take the half containing p and strip p and primes of n.

Output:

```
Wieferich base 3 below 20000: [11]
unique (phi<=120): 14
[(2, 1), (5, 4), (7, 6), (11, 5), (13, 3), (41, 8), (61, 10), (73, 12), (547, 14), (757, 9), (1093, 7), (1181, 20), (4561, 15), (6481, 24)]
skipped phi>240 count 1946 first [(503, 251), (509, 508), (557, 556)]
half-only (phi<=240): 9
[(7, 6), (19, 18), (31, 30), (37, 18), (43, 42), (271, 30), (2269, 42), (19441, 54), (19927, 54)]
half-only not unique: [(19, 18), (31, 30), (37, 18), (43, 42), (271, 30), (2269, 42), (19441, 54), (19927, 54)]
exceptions to g1*g2==Phi: []
```

Comparison with OEIS: A211874 values below 20000 (2, 7, 13, 61, 73, 547, 757, 1093, 4561, 6481) are exactly the unique primes with Phi_n(3) itself prime; our four extra unique primes 5, 11, 41, 1181 have Phi_n(3) = 2*5, 11^2, 2*41, 5*1181. Orders match the indices of A138933 (3, 6, 7, 9, 10, 12, 14, 15, 24 and 1 are all in it). Eisenstein-Mersenne 7, 271, 2269 (A066413) and the exponents 5, 11, 31, 37 of A239842 correspond to halves of Phi_{6p}: 31 and 271 are the two halves of Phi_30(3) with p = 5 index, 19 and 37 (n = 18, m = 3) are the two halves of Phi_18(3) = 703. Phi_16(3) = 3281 = 17 * 193 [INFERRED from the brief; 17 and 193 are not in our unique list, as the brief predicts, and 17 and 193 appear in A129733 as separate primitive primes].

## What could not be opened or verified

- No b-file was opened (A129733, A138933, A292007); only entries.
- The Cunningham file was read in slices of 100,000 characters by a summarizing tool; the L/M table rows beyond samples were not read line by line. The exact count of composite entries in Table 3- (n < 900) was not determined.
- Brent's factors.gz and rpb files, and the Cunningham Aurifeuillian paper (mine.pdf), were not opened.
- FactorDB was only queried once; coverage of every 3^n +- 1 was not tested.
- Order of 1006003 modulo 3 and the primitive part of its exponent were not computed.
- Absence of a base-3 unique-prime OEIS sequence rests on term searches and 3 web searches; this is weak evidence.

## Search log

WebSearch (3 of 30): (1) OEIS "3^k-1" exactly one primitive prime factor unique primes base 3; (2) OEIS numbers k such that cyclotomic polynomial Phi_k(3) is prime; (3) OEIS primes p ternary expansion 1/p unique period length no other prime has that period. WebFetch: OEIS JSON searches for unique-period base 3, id queries (A014127, A144755, A161508/9, A072226, A028491, A007658, A066408, A066413, A125743, A125744, A239842, A057429, A165132, A138933, A292007, A211874, A019321, A129733, A250197, A200923 and others), term searches (four, all empty for the unique-prime lists), the Purdue pages, Brent's page, FactorDB.

## Sources

- [OEIS search: unique period base 3](https://oeis.org/search?q=unique+period+base+3&fmt=json)
- [A014127](https://oeis.org/search?q=id:A014127&fmt=json)
- [A144755](https://oeis.org/search?q=id:A144755&fmt=json)
- [A161508, A161509, A072226](https://oeis.org/search?q=id:A161508|id:A161509|id:A072226&fmt=json)
- [A129733 (term search and entry)](https://oeis.org/search?q=id:A129733&fmt=json)
- [A028491, A007658, A066408, A066413](https://oeis.org/search?q=id:A028491|id:A007658|id:A066408|id:A066413&fmt=json)
- [A125743, A125744, A239842, A057429, A165132](https://oeis.org/search?q=id:A125743|id:A125744|id:A239842|id:A057429|id:A165132&fmt=json)
- [A138933, A292007, A211874](https://oeis.org/search?q=id:A138933|id:A292007|id:A211874&fmt=json)
- [A138933 page](https://oeis.org/A138933)
- [A250197](https://oeis.org/search?q=id:A250197&fmt=json)
- [Cunningham main tables](https://homes.cerias.purdue.edu/~ssw/cun/pmain1126.txt)
- [Cunningham index](https://homes.cerias.purdue.edu/~ssw/cun/index.html)
- [Cunningham Book, 3rd edition](https://homes.cerias.purdue.edu/~ssw/cun/third/index.html)
- [Brent's factor page](https://maths-people.anu.edu.au/~brent/factors.html)
- [FactorDB query for 3^100-1](http://factordb.com/index.php?query=3%5E100-1)
