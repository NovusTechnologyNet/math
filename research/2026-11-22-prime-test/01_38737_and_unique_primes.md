# 38737 in OEIS A104885, and unique primes: provenance, comparison, data

Date: 2026-11-22. Tags: [READ] = I opened the source and saw it; [SNIPPET] = search-result text only; [INFERRED] = my reasoning or my own computation (marked as such).

## Key findings

1. **38737 comes from Chamberland (2003), not from Bailey.** [READ] Chamberland's paper (J. Integer Seq. 6, Art. 03.3.7, received 15 July 2003, revised 24 October 2003) states that "modest calculations with Maple" produced an augmentation of Bailey's list of primes with binary BBP logarithm formulas; 38737 is in that augmented list. The paper gives no formula and no factorization for 38737. Bailey's own list in the March-2004-era compendium text (list (9), the version I opened is dated April 8, 2023 but its list is the short one) does not contain 38737, and the 2023 compendium itself says the list is incomplete. The Borwein-Bailey book (2nd edition, 2008, p. 130, cites Chamberland's manuscript as [103]) copies the 38737 entry; OEIS A104885 (Gary W. Adamson, 29 March 2005) copies the same list up to 312709.
2. **OEIS never changed the entry.** [READ] A104885 has three revisions (2005-04-09 creation, 2007-11-10 references and keyword, 2012-03-30 a server edit with no visible content change). The data line, with 38737 in it, is in revision 1 and in the current version. There is no comment, no formula and no discussion text on the entry. 433 never appears.
3. **No source lists 433. No source gives a justification for 38737.** [READ for Chamberland PDF (two copies), the 2008 book, Bailey 2023 compendium, Adegoke et al. arXiv:1603.07395; text search for "433" and "38737"]. No erratum, correction or forum remark about 38737 turned up in one targeted search [SNIPPET: none found].
4. **A likely origin of the mistake (my inference, not stated by any source).** [INFERRED, computed by me] Chamberland's method (formula (6)) takes Re log Phi_m((1+i)/2^n), whose real part is log|Phi_m(1+i)|. For m = 144 I computed |Phi_144(1+i)|^2 = (433 * 38737)^2, that is, |Phi_144(1+i)| = Phi_72(2) = 433 * 38737. The only m below 200 where 38737 or 433 divides a norm |Phi_m(1+i)|^2 is m = 144. So this formula gives log 433 + log 38737 and nothing about either prime alone. Chamberland's list of two-prime products (23x89, 47x178481, ...) does not contain 433 x 38737, and his single-prime list contains 38737 but not 433. So the entry looks like a slip in reading the Maple factorization (one factor kept as a "single prime", the partner dropped). This fits our Lean result (log 433 + log 38737 is a value, neither alone is).
5. **Our 51 primes below 10^7 split exactly as: 1 (the prime 2) + 31 binary unique primes + 19 primes that are unique only in an Aurifeuillian half.** [INFERRED, computed by me; the 31 agree with OEIS A144755] There is no binary unique prime below 10^7 missing from our list, and every prime on our list is either 2, a binary unique prime, or half-unique. This is a precise match, not just a resemblance.
6. **Unique primes and BBP logarithms: not connected in anything I found.** The only link on the unique-prime side is that Caldwell's "generalized unique primes" page treats Gaussian-Mersenne norms as generalized unique primes [READ]. No paper or page connecting unique primes (or "unique in a half") with BBP formulas turned up in two targeted searches [SNIPPET, negative]. I found no named notion for "unique in its Aurifeuillian half".
7. **Data to extend the list far past 10^7 exists** (Section 3): factorizations of Phi_n(2) for n up to 1280 split into Aurifeuillian halves (file attached to A250197), the unique-prime lists A161508/A161509 (179 terms), prime-value lists A072226 (289 terms, n up to 130002), A250197/A250198, A057429, A124112/A125742. Chamberland's own list goes up to 54 digits; I checked all 38 of his primes above 10^7 against our test, 34 of them completely (the rest need an order above 600) and all pass the shape test (Section 2).

## Details

### Question 1: provenance of 38737

**OEIS entry.** [READ] `https://oeis.org/A104885/internal`, the JSON endpoint and the history page. Name: primes whose logarithms are known to possess binary BBP formulas. Author Gary W. Adamson, 29 Mar 2005; created 2005-04-09 (Sloane); keyword nonn; 46 terms 2 to 312709; references BBP 1997 and Borwein-Bailey 2004 p. 130. Revision 1 (2005) already has the full 46-term data line with 38737. Revision 2 (Sloane, 2007) only touches REFERENCES and KEYWORD. Revision 3 (2012) shows only a "Discussion" server edit. The per-revision pages (`/history/view?...`) refuse WebFetch with HTTP 403 but opened with curl; revision 1 shows the full DATA.

**Chamberland 2003.** [READ] Two copies (cs.uwaterloo.ca PDF, and the author's Grinnell copy, a pre-publication version) both contain the sentence about Maple, then the list (about 90 primes up to 28 digits; 38737 sits between 26317 and 43691) and then a list of products of two primes (23x89, 47x178481, 53x157, ..., 181549x12112549). Two worked examples tie specific primes to a formula: Re log Phi_6((1+i)/2^n) gives 14449, Re log Phi_5((-1+3i)/2^n) gives 331, and a third gives 599479 via 23x89. For 38737 no example, formula or factorization is given. 433 is not mentioned anywhere in the paper. Chamberland also writes that the underlined numbers in his list were Bailey's, so he labels his additions himself; the plain text I extracted does not preserve which numbers are underlined, so I could not confirm that 38737 is not underlined. [Limit, see Section 4.]

**Bailey's compendium.** [READ] The copy I opened (davidhbailey.com, dated April 8, 2023) has the short list (9): 2, 3, 5, 7, ..., 2796203, 15790321, 18837001, 22366891, 4278255361, 4562284561, 2932031007403, 4363953127297, 4432676798593. No 38737, no 433, no 331. It says explicitly that the list is not complete and that the formulas are "generally straightforward to derive". The tika-corpus copy tagged "1 Mar 2004" could not be downloaded (curl returned no file); an earlier report read the 2023 version only, and I did not see any earlier version of the compendium.

**Mathematics by Experiment.** [READ] The 2nd edition (A K Peters, 2008), p. 130, formula (3.48): 55 primes from 2 to 22366891. Compared with our 51 primes below 10^7: the book's list contains all 51, plus 38737, plus 15790321, 18837001 and 22366891 (all three pass our test, they are binary unique primes in A144755). Reference [103] is Chamberland's manuscript of 2003. I did not see the 2004 first edition (the OEIS entry cites p. 130 of it; same page number in the second edition). Text around the list: "this list is certainly not complete".

**MathWorld and Wikipedia.** [READ] The MathWorld pages "BBP Formula" and "BBP-Type Formula" do not list primes with logarithm formulas and mention neither 38737 nor 433. The Wikipedia page "Unique prime" does not discuss binary unique primes in its text (only decimal), does not mention BBP or logarithms.

**Errata and forum remarks.** [SNIPPET, negative] One search for an erratum on Chamberland's paper, and one for "38737 BBP", returned only the paper, the OEIS entry, Bailey's compendium and Adegoke et al. I found no erratum, no MathOverflow thread, no remark. Absence in a search is weak evidence.

**Adegoke, Lafont and Layeni (arXiv:1603.07395).** [READ, text search] No occurrence of 38737, 433 or 331.

### Question 2: unique primes

**The notion.** [READ] Caldwell's page "Generalized unique primes" (t5k.org/top20/page.php?id=44): a prime p is generalized unique in base b if for some n it is the only prime divisor of Phi_n(b) that does not divide n (it may occur as a power). It says Gaussian Mersenne norms other than 5 are generalized unique, as they are Phi_4(2^((n+1)/2) +- 1)/2. For base 2 this is exactly "Phi_n(2)/gcd(Phi_n(2), n) is a power of p". OEIS comments say the same for A161509/A161508 [READ]: A161508 = k such that 2^k - 1 has exactly one primitive prime factor (179 terms, b-file), A161509 = that prime (179 terms, in order of k), A144755 = the same primes sorted (38 listed). Note a subtlety: our test also allows a partner q that divides n **and itself passes**; unique primes ignore q altogether. For the four cases below, q = 3, 5, 7 and 3, which all pass, so there is no discrepancy up to 10^7.

**My computation** [INFERRED; Python, sympy, run in this session]. For every n with phi(n) <= 29 I factored Phi_n(2) and took the primes of order exactly n; a prime below 10^7 that is the only primitive prime of its n is "binary unique" (a prime power p^x with x >= 2 would need a Wieferich prime and cannot occur here; the bound phi(n) <= 29 suffices since a prime below 2^23.3 forces phi(n) of about 26 at most). Result: 31 primes (without 2), identical to the terms of A144755 below 10^7. I ran the program's list of 51 primes (from the note) against them. For the 19 others I computed the half containing p (norm |Phi_d(1+i)|^2 or |Phi_2d(1+i)|^2 with n = 4d) and factored it.

### Comparison table for question 2

| Class | Count | Primes below 10^7 |
|---|---|---|
| 2 (log 2 has a formula by itself; not a "unique prime" in the A161509 sense) | 1 | 2 |
| Binary unique primes, Phi_n(2) has only p as primitive prime, no other factor | 27 | 3, 5, 7, 11, 13, 17, 31, 43, 73, 127, 151, 241, 257, 331, 683, 2731, 5419, 8191, 43691, 61681, 65537, 131071, 174763, 262657, 524287, 599479, 2796203 |
| Binary unique, Phi_n(2) = p * q with q dividing n (q = 3 for 19 and 87211, 5 for 41, 7 for 337) | 4 | 19, 41, 337, 87211 |
| Unique only in an Aurifeuillian half (Phi_n(2) has two primitive primes, one in each half) | 18 | 29, 37, 61, 109, 113, 397, 1321, 1429, 1613, 2113, 14449, 26317, 246241, 279073, 312709, 525313, 4327489, 7416361 |
| Half-unique with a partner: the half is 5 * 268501, and 5 divides n = 100 | 1 | 268501 |
| Binary unique primes not on our list | 0 | none |
| Our primes that are neither 2, nor binary unique, nor half-unique | 0 | none |

Total 1 + 27 + 4 + 18 + 1 = 51. Check: 27 + 4 = 31 binary unique primes; 18 + 1 = 19 half-only.

Cross-check with Chamberland's generalized Gaussian-Mersenne primes [READ, OEIS A207040 data]: A207040 (primes that are norms |(1+i)^n - c|^2 and prime) contains every one of the 18 half-unique primes with a pure half, and also 5, 13, 41; it omits 268501, because 268501's half is composite (5 * 268501), and omits 19, 31, ... which are not Gaussian norms. This explains why 268501 is on A104885 yet not on A207040. Terms of A207040 below 10^7 (21 terms: 5, 13, 29, 37, 41, 61, 109, 113, 397, 1321, 1429, 1613, 2113, 14449, 26317, 246241, 279073, 312709, 525313, 4327489, 7416361) are all on our list.

Beyond 10^7, binary unique primes are on Chamberland's list too: 15790321, 18837001, 22366891 and 4278255361, 4562284561 etc. all appear in A144755 or A153443.

**Chamberland's primes above 10^7 against our test** [INFERRED, my computation]. 38 primes in his list exceed 10^7 (15790321 to a 54-digit prime). For the 34 whose order of 2 is at most 600 I computed the primitive part (full Phi_n(2), or the half for n = 4 mod 8): in 33 cases p is the whole part (R = 1), in one case (19177458387940268116349766612211, order 342) the cofactor is 19, which divides 342, and 19 passes. So all 34 pass the test. Four primes (orders above 600: 304832756195865229284807891468769, 3652124453410972878264128353955921, 1461503031127477825099979369543473122548042956801, and the 54-digit one) were not checked.

**Named notions for the half case.** [SNIPPET, READ for OEIS] Not found. Related OEIS names: A250197/A250198 "left/right Aurifeuillian primitive part of 2^k+1 is prime" (the halves = our |Phi_d(1+i)|^2, |Phi_2d(1+i)|^2, with k = 2d, d odd, listed as n = 2 mod 4); A153443 "Aurifeuillian primes of the form 2^k+1" (a different, broader notion: irreducible real factor of x^k+1 at 2 being prime); A124112/A125742 (Gaussian-prime and Aurifeuillian cofactor/5 forms). The ratio-style notion "unique in its half" has no name I could find; the notion "generalized unique prime" (Caldwell) covers it only if one allows Phi_4(2^m +- 1)/2 as a polynomial value. Oakes (2000) called such norms "a new series of Mersenne-like Gaussian primes" [SNIPPET from OEIS A057429 link, mail archive not opened].

**Connection with BBP, prior work.** Two targeted searches [SNIPPET]: none found. The closest are Chamberland's own remarks that the primes he adds come from Re log Phi_m((1+i)/2^n), which in modern language are the Gaussian-norm primes, and Caldwell's remark that Gaussian Mersenne norms are generalized unique. Nobody states the equivalence "unique primes plus half-unique plus one partner with log p a BBP value" that our criterion gives. This is absence of evidence only; I make no novelty claim.

### Question 3: data to extend the list

All numbers below verified by opening the OEIS record (JSON endpoint) or the b-file [READ].

| Sequence | What it lists | Known extent |
|---|---|---|
| **A161508** | k with exactly one primitive prime factor of 2^k - 1 (the "unique period" indices) | b-file 179 terms, k up to 9941 |
| **A161509** | the corresponding unique primes (in order of k) | b-file 179 terms; largest k = 9941 (a prime of about 3000 digits) |
| **A144755** | the same primes sorted; incomplete beyond the first listed gap (comment says any prime not yet in A161509 must be tested separately) | 38 terms, last 4278255361 |
| **A064078** | Zsigmondy numbers Zs(n,2,1) (primitive part of 2^n - 1) | b-file n = 1..1000 |
| **A086251** | number of primitive prime factors of 2^n - 1 (equals 1 iff n in A161508) | b-file n up to 1212 |
| **A085021** | number of prime factors of Phi_n(2) | b-file n up to 1212 |
| **A072226** | n such that Phi_n(2) is prime | b-file 289 terms, largest n = 130002 (terms 278-289 from Pomerance 2024; Pomerance's "Cyclotomic primes", arXiv:2411.04213, is linked there) |
| **A333973** | n where Phi_n(2) > A064078(n) and A064078(n) is prime or a prime power (unique prime with a composite part removed) | 9 terms: 18, 20, 21, 54, 147, 342, 602, 889, 258121; note A161508 minus A072226 contains them |
| **A112927** | least prime with order of 2 equal to n | b-file n up to 1236 |
| **A250197** | k = 2 mod 4 such that the **left** Aurifeuillian primitive part of 2^k + 1 is prime (Phi_{2nL(n)}(2) prime) | 54 terms listed, up to 1926 |
| **A250198** | the same, **right** Aurifeuillian part | 43 terms listed, up to 1994 |
| **File "a250197_2.txt"** (attached to A250197; Eric Chen, Gord Palameta) | factorization of Phi_n(2) for n up to 1280, with the two Aurifeuillian halves of n = 4 mod 8 shown separately as "nL" and "nM" | 1439 lines |
| **A057429** | n such that (1+i)^n - 1 has prime norm (Gaussian-Mersenne exponents; the norms are A182300, 12 terms shown, last 2854495385411919762116496381035264358442074113) | 41 terms, largest n = 15317227; links to Berrizbeitia-Iskra and the MersenneForum project |
| **A182300** | the Gaussian-Mersenne primes themselves (p = 2^n +- 2^((n+1)/2) + 1) | 12 terms listed |
| **A088962** / **A207040** | Chamberland's generalized Gaussian-Mersenne n and primes (norms |(1+i)^n - c|^2 prime, general c) | 63 and 31 terms; A207040 up to 1759217765581 |
| **A124112** | k with ((1+i)^k + 1)/(2+i) a Gaussian prime (Gaussian cofactor, the 5 x partner case) | 45 terms, up to 5243339 and a known 12503723; proved prime only to 12583 |
| **A125742** | primes p with (2^p - 2^((p+1)/2) + 1)/5 prime (the Aurifeuillian cofactor of 4^p + 1) | 27 terms, up to 5243339; every term is in A124112; many only probable primes |
| **A153443** | Aurifeuillian primes of the form 2^k + 1 (irreducible real factor of x^k + 1 at 2) | 27 terms, up to 4363953127297 |
| **A066408** | the Eisenstein analogue (not needed here) | 28 terms |

**Other tables named by these entries** [READ as links, pages not opened]: the Cunningham project (Wagstaff, homes.cerias.purdue.edu/~ssw/cun/index.html), H. Mishima's "Factorization of Cyclotomic Numbers" (asahi-net.or.jp/~KC2H-MSM/cn/), Gallot's cyclotomic primes paper, primenumbers.net PRP records (Phi(258121,2)/719), Caldwell's list of generalized unique primes (t5k.org top 20, base 2 entries include the 4.6 million digit 2^15317227 + 2^7658614 + 1).

**How the data extends our list** [INFERRED]. Because the test needs only (i) the order n = ord_p(2), (ii) whether Phi_n(2) (or its half) is a prime power times at most one prime dividing n, a prime p above 10^7 is on the list iff it is a prime of type "Phi_n(2) prime or a prime times a divisor of n", or the same for a half. So for n up to 1280 one can read the answer from the file attached to A250197; for larger n from A161508/A161509 (n up to 9941) and A072226 (n up to 130002, for the prime case), with the half cases from A057429/A124112-type searches and Cunningham tables; the list stays open-ended, as Phi_n(2) values keep growing.

## What could not be opened or verified

- OEIS per-revision pages: WebFetch got 403 (the OEIS refuses the tool); curl worked, but the history diff markup shows only the final text for DATA in revision 1. I could not see any edit history of the data line other than "present in revision 1 and now".
- The first edition (2004) of Mathematics by Experiment; I read the second edition (2008).
- A pre-2023 version of Bailey's compendium (the "1 Mar 2004" tika-corpus copy did not download). Hence I do not know whether Bailey's older versions had 38737 or 331.
- Whether numbers in Chamberland's list are underlined (marking Bailey's contributions): the PDF text extraction loses formatting.
- Whether any forum or mailing-list thread discusses 38737 (search engines only; MathOverflow and mersenneforum not searched directly).
- Which Maple output led Chamberland to 38737: my explanation (|Phi_144(1+i)| = 433 * 38737) is an inference.
- The Chamberland primes of order above 600 (four primes) against our test; and whether A144755/A161509 beyond what is listed hold any unique prime above 10^7 that Chamberland's list lacks (not needed for the question below 10^7, which is settled: none).
- The sources Oakes (2000, mail-archive.com), Berrizbeitia-Iskra and Pomerance (arXiv:2411.04213) were not opened.

## Search log

1. "Mathematics by Experiment" BBP logarithms primes 2, 3, 5, ..., 331 (WebSearch; no listing found in snippet; found ed2-book.pdf and compendium links)
2. BBP-type formula logarithm of prime 38737 binary formula (WebSearch; OEIS entry, Chamberland, Bailey, Adegoke)
3. unique period primes binary BBP logarithm Aurifeuillian Gaussian-Mersenne norm "unique" cyclotomic Phi_n(2) log p digit extraction (WebSearch; Caldwell, MathWorld, Wikipedia; no link to BBP)
4. Chamberland "Binary BBP-formulae for logarithms" list of primes error OR correction OR erratum (WebSearch; no erratum found)

Total: 4 WebSearch calls (limit 35). OEIS JSON/b-file/history calls (not limited): A104885 (JSON, /internal, history, three revision pages), A161509, A144755, A161508, A051627, A057429, A182300, A088962, A207040, A072226, A125742, A153443, A019320, A050922, A001265, A097062, A161510, A250197, A250198, A333973, A085021, A086251, A064078, A124112, A112927; b-files A072226, A161508, A161509, A085021; file a250197_2.txt; keyword searches "Aurifeuillian", "unique primitive prime factor", "Gaussian-Mersenne", "A064078".

## Sources

Opened (read):
- [OEIS A104885 (internal format)](https://oeis.org/A104885/internal)
- [OEIS A104885 (JSON)](https://oeis.org/search?q=id:A104885&fmt=json)
- [OEIS A104885 revision history](https://oeis.org/history?seq=A104885)
- [Chamberland 2003 (J. Integer Seq. 6, 03.3.7), PDF](https://cs.uwaterloo.ca/journals/JIS/VOL6/Chamberland/chamberland60.pdf)
- [Chamberland's pre-publication copy (Grinnell)](https://chamberland.math.grinnell.edu/papers/bbp.pdf)
- [Borwein and Bailey, Mathematics by Experiment, 2nd edition (2008), PDF copy](https://carmamaths.org/jon/Preprints/Talks/M2600/Readings/ed2-book.pdf)
- [Bailey, A Compendium of BBP-Type Formulas (April 8, 2023)](https://www.davidhbailey.com//dhbpapers/bbp-formulas.pdf)
- [Adegoke, Lafont, Layeni, arXiv:1603.07395](https://arxiv.org/pdf/1603.07395)
- [MathWorld: BBP Formula](https://mathworld.wolfram.com/BBPFormula.html)
- [MathWorld: BBP-Type Formula](https://mathworld.wolfram.com/BBP-TypeFormula.html)
- [Wikipedia: Unique prime](https://en.wikipedia.org/wiki/Unique_prime)
- [Caldwell, Generalized unique primes (PrimePages Top 20)](https://t5k.org/top20/page.php?id=44)
- [OEIS A161508](https://oeis.org/A161508), [A161509](https://oeis.org/A161509), [A144755](https://oeis.org/A144755), [A064078](https://oeis.org/A064078), [A086251](https://oeis.org/A086251), [A085021](https://oeis.org/A085021), [A072226](https://oeis.org/A072226), [A333973](https://oeis.org/A333973), [A112927](https://oeis.org/A112927)
- [OEIS A057429](https://oeis.org/A057429), [A182300](https://oeis.org/A182300), [A088962](https://oeis.org/A088962), [A207040](https://oeis.org/A207040), [A124112](https://oeis.org/A124112), [A125742](https://oeis.org/A125742), [A153443](https://oeis.org/A153443), [A250197](https://oeis.org/A250197), [A250198](https://oeis.org/A250198)
- [A250197 attachment: factorization of Phi_n(2), n up to 1280](https://oeis.org/A250197/a250197_2.txt)
- b-files: [A072226](https://oeis.org/A072226/b072226.txt), [A161508](https://oeis.org/A161508/b161508.txt), [A161509](https://oeis.org/A161509/b161509.txt), [A085021](https://oeis.org/A085021/b085021.txt)

Seen only as search results or links (not opened): [Berrizbeitia-Iskra](https://doi.org/10.1090/S0025-5718-10-02324-0), [Cunningham project](http://homes.cerias.purdue.edu/~ssw/cun/index.html), [Pomerance, Cyclotomic primes](https://arxiv.org/abs/2411.04213), [Mishima, factorization of cyclotomic numbers](http://www.asahi-net.or.jp/~KC2H-MSM/cn/).
