# W2-Q14: OEIS sequences touching the project's results

Date of access: 22 Nov 2026. Marks: [READ] = read by me on the source's own page or PDF text
(I extracted the text of the two PDFs myself with pdftotext); [SNIPPET] = OEIS JSON/API
record or page as relayed by the fetch tool (the fetch tool runs a small summarising model
over each page, so long number lists and wording can be slightly off; verify any term before
quoting it publicly); [INFERRED] = my own conclusion; [COMPUTED] = I ran it myself (Python,
sympy), not from the web.

## 1. Summary

1. A104885 (author Gary W. Adamson, 29 Mar 2005; created 9 Apr 2005; last edit 30 Mar 2012;
   3 revisions) lists exactly 46 terms, 2 ... 312709, including 38737. [SNIPPET] These are
   the first 46 terms of the augmented list printed in Chamberland, J. Integer Sequences 6
   (2003), Art. 03.3.7, which has about 90 single primes up to 8.7e53. [READ] The OEIS
   entry does not cite Chamberland at all (its references are BBP 1997 and the Borwein-Bailey
   book p. 130). [SNIPPET] No erratum, no "uncertain" remark, no b-file, no link, no later
   comment is recorded. [SNIPPET + history page]
2. 38737 is NOT in Bailey's own list (his Compendium, list (9), 46 primes ending 4432676798593).
   [READ] It first appears in Chamberland's list. [READ] So the source of that term is
   Chamberland 2003 ("modest calculations with Maple"), not Bailey. The same Chamberland list
   also contains 331, 1429, 14449, 26317, 65537, 246241, 268501, 279073, 312709, ... which
   Bailey's list lacks; Chamberland marks Bailey's ones by underlining (underlining is lost
   in the text layer). [READ]
3. [COMPUTED] 38737 | Phi_72(2) = 433 * 38737 (2^24 - 2^12 + 1 = 16773121), 2 has order 72 mod
   both 433 and 38737, and 433 is not in Chamberland's list, nor is a product 433*38737 in
   his list of products of two primes. Among m < 400, the only m with 38737 | N(Phi_m(1+i))
   is m = 144, where N = (433*38737)^2. So in the Chamberland mechanism 38737 can only enter
   together with 433 [INFERRED]; this is consistent with the project's finding that the
   entry 38737 fails. I found no published erratum (searches in OEIS, history page).
4. Chamberland (2003) states that it is "still unknown" whether log 23 has a binary BBP formula
   (citing Pomerance for the absence of the form (1)); the project's Theorem G (log 23 has none
   in class F) settles that within the degree-1 class. [READ, Chamberland p. ~6]
5. A250197: I recomputed all 56 listed terms [COMPUTED] (gcd of the left Aurifeuillian factor
   2^(n/2) - 2^((n+2)/4) + 1 with Phi_2n(2), prime test BPSW, n = 2 mod 4, n < 1960): the
   list matches exactly, no missing and no extra term. So a(10) = 66 is correct (and the
   value 10 is also correct as a(1)). No error found. One definitional quirk: a(1) = 10
   arises because gcd(25, 205) = 5, a prime that also divides 2^2+1, i.e. not "primitive".
6. The OEIS policy on AI (approved 29 Aug 2026): AI-assisted submissions are allowed only with a
   human author who verifies everything; forbidden: AI as (co-)author, AI-generated full text of
   comments, pasting AI text into editor replies, bulk/serial automated submissions without
   prior permission. [SNIPPET of the wiki page via fetch tool; one WebSearch hit confirms the
   page title "Use of AI for OEIS Submissions is Forbidden"]
7. Similar sequences already in OEIS: ternary: A165132 (primes 2,3,5,7,11,13 only, Jaume Oliver
   Lafont, keyword "more"), A154920, A164985. No OEIS sequence for degree-1 BBP in base 3 with
   a proved complete classification, none for zero relations, none for "dimension 13/8" objects.

## 2. What is known: each sequence

### A104885 (primes whose logarithms are known to possess binary BBP formulas)
- Name as above. Offset 1,1. Keyword nonn. [SNIPPET]
- Data (46 terms): 2, 3, 5, 7, 11, 13, 17, 19, 29, 31, 37, 41, 43, 61, 73, 109, 113, 127,
  151, 241, 257, 331, 337, 397, 683, 1321, 1429, 1613, 2113, 2731, 5419, 8191, 14449, 26317,
  38737, 43691, 61681, 65537, 87211, 131071, 174763, 246241, 262657, 268501, 279073, 312709.
  [SNIPPET; same list as Chamberland's, checked against the PDF text: READ]
- Comments: unknown whether finite; BBP-type = base b = 2^p; most formulas found
  experimentally with PSLQ. [SNIPPET] (The "PSLQ" remark does not match Chamberland, whose
  formulas come from cyclotomic/Mobius identities with Maple, and Bailey's, which are
  derived. [INFERRED])
- References: Bailey-Borwein-Plouffe, Math. Comp. 66 (1997) 903-913; Borwein-Bailey,
  Mathematics by Experiment (2004) p. 130. Formula field: "algorithm originated with BBP".
  No links, no program, no cross-reference except none to A165132 in this direction
  (A165132 cites A104885). [SNIPPET]
- History page (3 revisions): #1 N. J. A. Sloane, 9 Apr 2005 (original); #2 N. J. A. Sloane,
  10 Nov 2007 (added references, keyword edit new -> nonn); #3 Russ Cox, 30 Mar 2012 (server
  edit). Text only; the fetch tool could not show what exactly changed. [SNIPPET]
- Truncation: Chamberland's list continues 524287, 525313, 599479, 2796203, 4327489,
  7416361, 15790321, 18837001, 22366891, 29247661, ... up to
  867988564747274927163124868127898657976489313137639569; OEIS stops at 312709 (a
  size-of-data-field cut, not a stated search bound). [READ + INFERRED]
- Source of each term: terms in Bailey's Compendium list (9) are Bailey's (e.g. 2, 3, 5, 7,
  11, 13, 17, 19, 29, 31, 37, 41, 43, 61, 73, 109, 113, 127, 151, 241, 257, 337, 397, 683,
  1321, 1613, 2113, 2731, 5419, 8191, 43691, 61681, 87211, 131071, 174763, 262657 and later
  terms). [READ] The others (331, 1429, 14449, 26317, 38737, 65537, 246241, 268501, 279073,
  312709) come from Chamberland: 14449 from Re log Phi_6((1+i)/2^3)-type identity
  (formula (6)), 331 from Re log Phi_5((-1+sqrt(-3))/2^4) type identity (formula (7)),
  599479 from a combination with 2^11-1 = 23*89. [READ] For 38737 no derivation is printed
  in the paper. [READ: I grepped the extracted text; only the list line contains 38737.]
- Erratum: none recorded anywhere I looked (OEIS entry, history, A165132, A088962, A207040,
  Chamberland html). Not found is weak evidence. A search of OEIS for "38737 binary BBP"
  returned only A104885 itself. [SNIPPET]

### Chamberland (2003), J. Integer Seq. 6, Art. 03.3.7 [READ, PDF text]
- Defines binary BBP formulas for log m via Re log Phi_n((1+i)/2^k) etc.; every odd prime p
  is on the list "either alone or in some product" since 2^(p-1)-1 is on it and p divides it;
  the list of products of two primes is given (23*89, 47*178481, ..., 137*953, 641*6700417,
  ...). He remarks that all primes up to 101 are on the list alone or with one partner, and
  that "it is still unknown whether log 23 has a binary BBP-formula". The list was produced
  by "modest calculations with Maple". No completeness claim; no mention of verification of
  each entry beyond that. [READ]
- Note that this implies the OEIS name "known to possess" is a statement about 2003
  knowledge, and the entry contains no way to see that the list is a union of two sources.
  [INFERRED]

### A165132 (primes whose logarithms are known to possess ternary BBP formulas) [SNIPPET]
- Data: 2, 3, 5, 7, 11, 13. Offset 1,1. Keywords nonn, more. Author Jaume Oliver Lafont, 4 Sep
  2009 (created 1 Jun 2010 in the system, comment 7 Oct 2009; 13 revisions; last 22 Jul 2025).
- Comments give P(1, 3^k, N, a) formulas for log 2, 3, 5, 7, 11, 13 (e.g. log 2 =
  (2/3)P(1,9,2,(1,0)); log 3 = (1/9)P(1,9,2,(9,1)); log 5 uses base 3^4, N=4; log 7 and
  log 13 use base 3^6, N=6; log 11 base 3^10, N=10), with reduced forms in the PARI code.
  Reference: Bailey Compendium p. 24. Cross-ref A104885. No claim of completeness, no "17".
- Related: A154920 (denominators of ternary BBP for log 3, formula log 3 = sum (9/(2k+1)+
  1/(2k+2))/9^(k+1), Compendium p. 14), A164985 (denominators, log 5). [SNIPPET]
- OEIS search "ternary BBP" returns only these three. [SNIPPET]

### A057429 (Gaussian-Mersenne indices) [SNIPPET]
- Numbers n with (1+i)^n - 1 of prime norm; 41 terms, 2, 3, 5, 7, 11, 19, 29, 47, 73, 79,
  113, 151, 157, 163, 167, 239, 241, 283, 353, 367, 379, 457, 997, 1367, 3041, 10141, 14699,
  27529, 49207, 77291, 85237, 106693, 160423, 203789, 364289, 991961, 1203793, 1667321,
  3704053, 4792057, 15317227. Author Robert G. Wilson v, 7 Sep 2000; created 2003-05-16;
  extensions through a(41) (Ryan Propper and Serge Batalov, 20 Jun 2023); last edited 6 Oct
  2026 (rev 91); keywords nonn, nice, hard, more. Links include Chamberland 2003 and
  Berrizbeitia-Iskra (Math. Comp. 79 (2010)); exhaustive search below 5,000,000 reported by
  Batalov 2014. Related: A182300 (the primes, e.g. 5, 13, 41, 113, 2113, ...), A088962.
- A088962 (Chamberland, 28 Oct 2003; 63 terms 2 ... 283; formula: numerator of
  exp(2 Re log Phi_n((1+i)/2)) prime) and A207040 (Wesolowski 2012; the 31 primes, 5, 13, 29,
  37, 41, 61, 109, ... 1759217765581) are the "generalised Gaussian-Mersenne" sequences; they
  link to Chamberland but make no remark on BBP. 38737 is not in A207040. [SNIPPET]

### A066408 (Eisenstein-Mersenne indices) [SNIPPET]
- Numbers n with (1-w)^n - 1 of prime norm: 2, 5, 7, 11, 17, 19, 79, 163, 193, 239, 317, 353,
  659, 709, 1049, 1103, 1759, 2029, 5153, 7541, 9049, 10453, 23743, 255361, 534827, 2237561,
  2888387, 4043119 (28 terms). Author Mike Oakes, 24 Dec 2001; a(26) Batalov 2014; a(27), a(28)
  Propper and Batalov Jun 2023; next term > 4,400,000 (June 2023). Norm = 3^p - (3/p) 3^((p+1)/2)
  + 1. Links: Berrizbeitia-Iskra. No BBP remark.

### A144755 (sorted unique primes, binary) [SNIPPET]
- Name: primes which divide none of the overpseudoprimes to base 2 (A141232) [name as relayed;
  the comments identify them with sorted A161509]. 38 terms 2, 3, 5, 7, 11, 13, 17, 19, 31, 41,
  43, 73, 127, 151, 241, 257, 331, 337, 683, 2731, 5419, 8191, 43691, 61681, 65537, 87211, 131071,
  174763, 262657, 524287, 599479, 2796203, 15790321, 18837001, 22366891, 715827883, 2147483647,
  4278255361. Author Vladimir Shevelev 2008; extended T. D. Noe 2010; b-file deleted by Max
  Alekseyev 10 Feb 2024; rev 17. Comment (Alekseyev 2024): sorting a finite initial segment of
  A161509 cannot guarantee that no term was missed; test p via A064078(A002326((p-1)/2)) = p.
  Uncertainty remark: yes (completeness of the finite list).

### A161508 / A161509 (binary unique periods and primes) [SNIPPET]
- A161508: k with 2^k-1 having exactly one primitive prime factor (T. D. Noe, 17 Jun 2009);
  data 2, 3, 4, 5, 7, 8, 9, 10, 12, 13, ..., 208 (66 terms shown); b-file of 179 terms
  (Noe); code PARI by Greathouse: isprimepower(polcyclo(n,2)/gcd(polcyclo(n,2),n)).
  Comments: shares most terms with A072226, which also has 6; A072226 lacks 18, 20, 21, 54, 147,
  342, 602, 889 below 10000; all known terms not in A072226 are in A333973
  (18, 20, 21, 54, 147, 342, 602, 889, 258121; Jeppe Stig Nielsen 2020, keywords hard, more;
  open question "should this be infinite?"; prime power p^j, j>1, would need a Wieferich
  prime that is also a unique prime).
- A161509: the primes (36 terms shown: 3, 7, 5, 31, 127, 17, 73, 11, 13, 8191, 43, 151, 257,
  131071, 19, 524287, 41, 337, 683, 241, 2731, 262657, 331, 2147483647, 65537, 599479, 43691,
  174763, 61681, 5419, 2796203, 4432676798593, 87211, 15790321, 2305843009213693951,
  715827883); b-file n=1..179 (Alekseyev; first 100 from Noe); rev 9, last 10 Feb 2024.
  No uncertainty remark in A161509 itself; the caution lives in A144755. A161508 has no
  remark about completeness of the search beyond n = 179 (b-file) [SNIPPET].

### A040017 (decimal unique-period primes) [SNIPPET]
- 3, 11, 37, 101, 9091, 9901, 333667, 909091, 99990001, 999999000001, ... (16 shown; b-file
  of 47 terms, Wilson). Author Jud McCranie (1999). Comment (Max Alekseyev, 14 Oct 2022):
  3 is the only known unique-period prime with A019328(r)/gcd = power of p with exponent >1;
  assuming none other exists, this lists all unique-period primes; "missing a(45)" fixed in
  b-file 13 Oct 2022 at the suggestion of Eric Chen. Last modified 28 Jun 2026, rev 56.
  Remark on uncertainty: conditional on that assumption (cf. A323748).
- A217611 (octal unique-period primes; A. Wesolowski, 8 Oct 2012): 3, 7, 19, 73, 87211,
  262657, 18837001, 77158673929, 5302306226370307681801, ... 13 terms shown, b-file 27 terms,
  rev 15, last edit 20 Sep 2026. "Generalised unique primes in base 8"; computed with
  Cyclotomic[n,8] / gcd(n) being a prime power for n <= 138. [SNIPPET]
- Note the base-2 and base-8 lists share 73, 87211, 262657, 18837001 etc. [INFERRED]

### A250197 (Aurifeuillian) [SNIPPET + COMPUTED]
- Numbers k with the left Aurifeuillian primitive part of 2^k+1 prime; data 10, 14, 18, 22, 26,
  30, 42, 54, 58, 66, 70, 86, 94, 98, 106, 110, 126, 130, 138, 146, 158, 174, 186, 210, 222,
  226, 258, 302, 334, 434, 462, 478, 482, 522, 566, 602, 638, 706, 734, 750, 770, 782, 914,
  1062, 1086, 1114, 1126, 1226, 1266, 1358, 1382, 1434, 1742, 1926 (56 terms). Author Eric
  Chen, 18 Jan 2015 (entered 2 Mar 2015); last edit 30 Jun 2025 (rev 79). Link: Chen and
  Palameta, factorisation of Phi_n(2) n <= 1280 (b-file). Programs: Mathematica; PARI by
  Michel Marcus 27 Jan 2015. Cross-refs A250198, A153443, A019320, A072226, A161508.
- [COMPUTED] My recomputation with the gcd definition for all n = 2 mod 4, n < 1960, gives
  exactly this list (56 terms). So there is no error in the terms; "term 10" is either the
  value 10 (valid) or a(10) = 66 (valid). Possible source of suspicion: for n = 10 the part is
  5, which also divides 2^2+1 (so is not a primitive prime divisor in the Zsigmondy sense). The
  OEIS definition is by gcd(L, Phi_2n(2)), under which 10 is correct. [INFERRED]
- Beyond n = 1280 the primality of the large gcd values is by probable-prime tests in my run
  (a(46)-a(56) are PRP-level for me, and likely so in OEIS). [INFERRED]

### A002072 (Stormer) [SNIPPET]
- a(n) = smallest m such that for all k > m, k or k+1 has a prime factor > prime(n). 27 terms
  shown, a(1..27) = 1, 8, 80, 4374, 9800, 123200, 336140, 11859210, 11859210, 177182720, ...,
  19316158377073923834000; b-file n = 1..37 (Ken Clements). Offset 1,2. Author N. J. A. Sloane;
  corrections Kulsha Aug 2011 (from Jim White's computations); a(18)-a(26) Fred Schneider
  2006; rev 97, last 15 Jul 2026. Comments: Lucas A. Brown: an EFFECTIVE abc conjecture would
  imply a(27)..a(32) are equal, predicts a(33); Clements (July 2026): computations confirm
  these predictions for a(27)-a(33), plateaus at n = 22-26, 27-33, 34-36; a(37) lies far outside
  the primorial interval. Conditional terms: the values beyond what is proved by Lehmer's
  method / certificate runs are tied to computer certificates (Clements, orders 16-37 logs on
  GitHub). The record itself speaks of "calculations confirm", i.e. computed, not proved, for
  the largest orders; I did not see an explicit "proved" statement per term. [SNIPPET, partly
  INFERRED]. Conjectured formula a(n) < 10^n/n (Hasler 2015).

### A007508 (twin prime pairs below 10^n) [SNIPPET]
- 2, 8, 35, 205, 1224, 8169, 58980, 440312, 3424506, 27412679, 224376048, 1870585220,
  15834664872, 135780321665, 1177209242304, 10304195697298, 90948839353159, 808675888577436,
  7237518093734545 (19 terms). a(16) corrected by Dana Jacobsen 28 Mar 2014; a(19) added by
  Benjamin Chaffin 2 Jun 2026, "corrected" 8 Jul 2026. Rev 149; created 1994. The a(19)
  correction one month after its addition is a recorded instance of a computed term being
  wrong at first. Compared against Hardy-Littlewood by Hugo Pfoertner (2026).

### A005042 / A060421 (primes in the digits of pi) [SNIPPET]
- A060421: k such that the first k digits of pi are prime: 1, 2, 6, 38, 16208, 47577, 78073,
  613373 (offset 1,2; Michel ten Voorde 2001; a(8) Adrian Bondrescu 29 May 2016; rev 51, last
  30 May 2026). Comment 2 (RJ Baillie, 18 May 2026): the 16208-digit probable prime has since
  been PROVED prime. The three larger terms are not stated to be proved (probable primes).
- A005042: 3, 31, 314159, 31415926535897932384626433832795028841 (rev 50, 10 Oct 2026);
  next term is the 16208-digit prime (Prothro, 2001, PRP). Formula a(n) = floor(10^(A060421(n)
  -1) * pi) (Hasler 2013). Kleber (2004): naive heuristic suggests infinite. [SNIPPET]

### Other sequences touching BBP / Machin / Lehmer measure (searches) [SNIPPET]
- OEIS search "BBP" gives only 10 records: A154920, A145960-A145963 (Jasinski, decimal
  expansions of BBP pieces), A260658 (David Brink, numerators of a BBP-like formula for
  4 pi/sqrt(27): sum (-1/8)^n (2/(3n+1) + 1/(3n+2)); comment Jonas Kaiser 2024: unsigned version
  via the reduced Collatz function on 6n+3), A104885, A154925 (Povolotsky), A164985, A165132.
  This is a base-8 formula with pi*sqrt(3) type value: relevant to the project's base-3/8
  classifications [INFERRED].
- "Machin-like": A338878, A338879 (Sanjar Abrarov, numerators/denominators of expansions of the
  single-term Machin-like formula for pi), digit expansions of arctan(1/3), 1/5, 1/7, 1/239
  (Jacobs), A195790, A127266 (1/pi in base 2). No sequence counting Machin-like formulas, no
  sequence of Lehmer measure values (search "Lehmer measure" gives Lehmer's constant A073011
  (Salem number), A070178, A059928, which are unrelated Mahler-measure sequences).
- "Aurifeuillian": A220978/9, A220990, A220983/4 (Clary), A061442/3 (Broadhurst), A352711,
  A352732, A352400 (Patrick A. Thomas), plus A250197. None connected to BBP.
- No OEIS sequence found for: zero relations of Bailey's Compendium; dimension counts; the
  classification of base 2 or base 3; degree-1 formulas in base 10 (search terms tried:
  BBP, Bailey Borwein Plouffe, ternary BBP, Machin, arctangent Machin, Lehmer Machin, Gaussian
  Mersenne BBP, Chamberland). Not found is weak evidence.

## 3. What is open (with sources)
- Whether A104885's list is finite: stated as unknown in the OEIS comment and by Bailey
  ("certainly not complete"). [SNIPPET, READ] The project's criterion for log p (Theorem K) and
  Theorem G (log 23 excluded) replace "known" by "is" for every p; that is a theorem the entry
  lacks. Finite or infinite: Chamberland's mechanism gives infinitely many primes only if
  infinitely many Gaussian-type primes exist (open). [INFERRED]
- Whether A161508 / A333973 are infinite (Nielsen's question) [SNIPPET]; completeness of
  A144755 (Alekseyev) [SNIPPET]; the base-10 unique-period list (assumption on 3) [SNIPPET].
- A057429: next term beyond 15317227 unknown; searched below 5e6 exhaustively (2014), search
  beyond partly done by Propper and Batalov [SNIPPET].

## 4. Leads for this project, ranked

1. **Propose a correction comment on A104885 (days).** Statement: 38737 is not a prime whose
   log has a binary degree-1 BBP formula (the project's Theorem K plus formal criterion); give
   the source of the entry (Chamberland 2003 list, not Bailey's), note that 331, 1429, 14449,
   26317, ... come from Chamberland, and note that log 23 has none (so 23 is correctly
   excluded). Fit: formal proof already exists; what is missing is the exact statement of
   which listed terms pass the criterion (run the criterion on all 46 terms and on
   Chamberland's whole list to ~8.7e53: a day of computation). Worth noticing: first erratum
   for a 20-year-old entry quoted by Bailey's Compendium lineage and the Borwein-Bailey book.
   Caveat: check the whole list first so that one comment covers every failure. [INFERRED]
2. **Propose a new, precisely defined sequence (days to a week):** "primes p such that log p
   has a degree-1 binary BBP-type formula" with a proved criterion, so the definition is
   mathematical rather than "known to". Terms: those p that the project's criterion accepts
   (possibly a finite initial segment up to 10^k; for the part below 100 the project has
   classified all). Also "primes p with a degree-1 ternary BBP for log p": the existing
   A165132 stops at 13 and has keyword "more"; the project has the base-3 criterion and a
   computed prime list. Extending A165132 with proved terms (and showing non-membership of
   e.g. 17, 19, 23 if the criterion says so) is a natural comment/extension. Size: days.
   Check A165132 first for whether the criterion makes 17 etc. members. [INFERRED]
3. **A new sequence about periods/relations (weeks):** e.g. "number of linearly independent
   zero relations (or dimension of the class) as a function of the period" in base 2 and 3
   (13 and 8 for period 120; 3 for period 12 in base 3). Fits the toolkit (exact enumeration).
   Value to OEIS: none similar exists (my searches). Risk: OEIS wants "general interest";
   more apt as a comment on A104885/A165132 or a table linked by a Links entry.
4. **Cross-check of Chamberland's list against the criterion (days):** compute for all ~90 primes
   and ~35 products in his lists; report which fail. If more than one fails, the OEIS entry
   plus Bailey Compendium list (9) can be checked in the same pass (list (9) has 46 primes; I
   saw no error in it, not verified). 
5. **Add terms/links to A333973 or A161508/9 (out of scope).** These sequences are computational
   (cyclotomic factorisation); no tie to the toolkit beyond primitive prime divisors.

## 5. Overlap or conflict with Section 1 results
- A104885 as printed contains 38737, which conflicts with the project's finding (Section 1
  of the rules says the criterion for log y; the memory notes that entry 38737 fails). My own
  computation supports the doubt: 38737 occurs only through (433 * 38737)^2 in N(Phi_144(1+i))
  for m < 400 and 433 is not on Chamberland's list. [COMPUTED/INFERRED]
- Chamberland (2003) says it is unknown whether log 23 has a binary BBP formula; the project's
  Theorem G shows none in class F. Not a contradiction, a gap closed in the degree-1 class.
  [READ]
- Bailey Compendium (arXiv/DHB PDF, sec. 2): states "it is not known whether arctan(2/7)
  possesses a binary BBP formula"; project's Theorem I says it has none. Same status.
  [READ]
- No OEIS sequence or comment contradicts the base-3 or base >= 5 results. A260658 (base 8,
  4 pi/sqrt(27)) is consistent with the base-3-type value pi*sqrt(3) in a power-of-2 base
  (P(1,8,...)); not a conflict. [INFERRED]

## 6. OEIS rules: corrections, submitters, process, AI policy

- Who may submit: anyone, after registering (account on the OEIS site). New sequences should
  be well defined, of general interest, ideally infinite. [SNIPPET of Welcome page]
- Process: allocate an A-number; save (status editing); click "ready for review" (proposed); an
  OEIS Editor checks definition and style; an Editor-in-Chief approves. Review takes from
  minutes to months. Comments on existing entries: via the edit button, which goes through the
  same (smaller) process, signed and dated. Public pink-box discussion. Disputes: ombudsman
  Hilarie Orman; to reach an author you log in to the wiki and email through their user page.
  [SNIPPET of "Overview of the contribution process" and Welcome pages]
- Style rules relevant here: at least 4 terms (ideally ~260 characters); only proven terms in
  Data, conjectured ones in Comments or Extensions, probable primes flagged; sign and date
  every added comment; use b-files for long lists; "famous open problems belong in a journal
  first". [SNIPPET of Style Sheet]
- AI policy: wiki page "Use of AI for OEIS Submissions is Forbidden", latest approved revision
  29 Aug 2026. Content as relayed by the fetch tool: every sequence needs a human author who is
  responsible for correctness and could give an expert-level talk on it (cites a 2026 remark by
  Terence Tao); submitter must independently verify name, terms, formulas (provably correct),
  programs, comments; forbidden: AI as author/co-author, AI-generated full text of comments,
  pasting AI text into editor replies, programs the submitter does not understand, bulk or
  serial AI submissions without prior permission; AI-assisted work is otherwise allowed;
  editors may reject, repeat offenders can be blocked. [SNIPPET]
  Practical consequence [INFERRED]: any comment or sequence about the project must be written
  by the owner in his own words and its terms recomputed and understood by him; the Lean proof
  can be cited as a link but a comment must not read as AI-generated; do not list any AI as
  author; do not do batch submissions. Whether a "formally verified by Lean" statement is
  welcome is not addressed by the page.

## 7. Sources
- https://oeis.org/A104885 ; https://oeis.org/history?seq=A104885 ; JSON API records for
  A104885, A165132, A057429, A066408, A144755, A040017, A161508, A161509, A250197, A002072,
  A007508, A005042, A060421, A217611, A088962, A207040, A260658, A154920, A333973, A182300,
  A007615, A072226 (https://oeis.org/search?q=id:ANUMBER&fmt=json)
- Chamberland, https://cs.uwaterloo.ca/journals/JIS/VOL6/Chamberland/chamberland60.pdf (and .html)
- Bailey Compendium, https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf (section 2, list (9))
- https://oeis.org/wiki/Welcome ; /wiki/Style_Sheet ; /wiki/Overview_of_the_contribution_process ;
  https://oeis.org/wiki/Use_of_AI_for_OEIS_Submissions_is_Forbidden

## 8. Search log
WebSearch (1): 1. "OEIS policy AI-generated LLM contributions sequences submissions".
Endpoint queries (fetch tool):
1 oeis A104885 json; 2 A250197; 3 A165132; 4 A057429; 5 A066408; 6 A144755; 7 A040017; 8 A161508;
9 A161509; 10 A002072; 11 A007508; 12 A005042; 13 A060421; 14 A217611; 15 A104885/internal;
16 history?seq=A104885; 17 Chamberland html; 18 search "BBP"; 19 "Machin-like"; 20 "Lehmer measure";
21 "Aurifeuillian"; 22 wiki Style_Sheet; 23 Chamberland pdf (text extracted locally); 24 wiki
Welcome; 25 wiki OEIS_policy_on_AI (404); 26 "38737 binary BBP"; 27 "Chamberland"; 28
"Gaussian-Mersenne BBP"; 29 "ternary BBP"; 30 "arctangent relations Machin"; 31 "Lehmer Machin
arctan Pi formulas"; 32 A088962; 33 A207040; 34 A260658; 35 A154920; 36 wiki
Contributing_a_new_sequence_or_comment (404); 37 search Zsigmondy/primitive prime (empty);
38 A333973; 39 wiki Use_of_AI_for_OEIS_Submissions_is_Forbidden; 40 wiki
Overview_of_the_contribution_process; 41 search "Bailey Borwein Plouffe"; 42 search "unique
period base 3"; 43 search "ternary expansion of 1/p unique period"; 44 search "Pi BBP formula
digits base 16"; 45 search "Gaussian Mersenne norm Aurifeuillian" (empty); 46 search "Stormer
smooth consecutive integers"; 47 Bailey Compendium pdf (text extracted locally); 48 A182300;
49 A007615; 50 A072226.
Totals: WebSearch calls = 1; endpoint queries = 50 (two returned 404, two empty).
Local computations (not web): recomputation of A250197 (n < 1960) and factorisation of
Phi_72(2), N(Phi_m(1+i)) for m < 400.
Note: no page contained instructions addressed to me.
