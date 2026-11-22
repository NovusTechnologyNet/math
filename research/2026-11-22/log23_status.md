# log 23 binary BBP status (checked 2026-11-22)

**Verdict: still open (as far as published/online sources I could find).** Only a restricted ansatz is excluded (Pomerance); no source proves or disproves a general binary BBP formula, and none found classifies all m. Absence of evidence only: 6 searches were run, no MathOverflow/MSE thread was found.

## Read on primary pages (full text, extracted locally)

1. Chamberland 2003, JIS 6, Art. 03.3.7 (PDF https://cs.uwaterloo.ca/journals/JIS/VOL6/Chamberland/chamberland60.pdf), p. ~7.
   - Quote: "it is still unknown whether log 23 has a binary BBP-formula."
   - Pomerance (cited as [2], i.e. BBP 1997) "showed that 23 could not be written in the form (1)".
   - Form (1) = ratios of products of Mersenne numbers: (2^a1 - 1)...(2^ah - 1) / ((2^b1 - 1)...(2^bj - 1)). So log 23 is not a Z-combination of log(2^k - 1) and log 2. (Only this ansatz, not all binary BBP formulas.)
   - Notes 2^11 - 1 = 23 x 89; every odd prime p appears alone or in a product in the list, since p | 2^(p-1) - 1. Chamberland's list of primes has no 23.
2. Bailey compendium, April 2023 version (https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf), section 2 "Logarithm formulas".
   - Quote: "it is unknown whether or not all primes have this property"; also unknown whether the list is finite or infinite.
   - List of primes: 2, 3, 5, 7, 11, 13, 17, 19, 29, 31, 37, 41, 43, 61, 73, 109, 113, 127, 151, 241, 257, 337, 397, 683, ... (23 absent). I found no mention of 23 or Pomerance in this PDF (grep for "23" showed only unrelated hits).
3. Borwein, Borwein, Galway, "Finding and excluding b-ary Machin-type individual digit formulae", Canad. J. Math 56 (2004) 897-925, DOI 10.4153/CJM-2004-041-2 (PDF via Cambridge URL below).
   - Theorem 4: no *non-Aurifeuillian* binary Machin-type BBP log formula for ln 23 (nor ln 89). Proof via Bang's theorem / primitive prime factors: 23 and 89 are both primitive factors of 2^11 - 1, cannot cancel 89. Same for pairs (47,53), (29,113).
   - Remark (i): "unable to exclude" a binary Machin-type formula for ln 23 using some Aurifeuillian generators; they think it unlikely, and such a formula would need "truly massive generators". For odd prime p, ord_p(1-(1+i)2^-m)=0 forces 2(p) = 0 mod 4 type restriction (garbled in extraction; see paper).
   - Note: this is about Machin-type (generator) formulas, not all BBP formulas. Baker's theorem not mentioned (grep).
4. OEIS A104885, "Primes whose logarithms are known to possess binary BBP formulas" (https://oeis.org/A104885). Comment: unknown whether the list of such primes is finite or infinite; formulas mostly found by PSLQ. Data: 2, 3, 5, 7, 11, 13, 17, 19, 29, 31, 37, 41, 43, 61, 73, 109, 113, 127, 151, 241, 257, 331, 337, 397, ... (23 absent). (Fetched via WebFetch summary of the page, not raw text.)
5. Barsky, Munoz, Perez-Marco, "On the genesis of BBP formulas", arXiv:1906.09629v4 (Feb 2023), sec. 4. Says 2 and 2^N +- 1 generate a subgroup of Q^* with binary BBP logs; "The first prime that it is not in this subgroup is k = 23" (2^11-1 = 23 x 89, they always appear together). It does not claim a proof of non-existence in general.
6. Adegoke, Oliver Lafont, Layeni, arXiv:1603.07395 and Adegoke arXiv:1603.05810; Kristensen-Mathiasen arXiv:2208.07696: downloaded, grep for log 23 / Baker found nothing relevant (they give more primes, not 23).

## Only seen in search snippets / search-tool summaries (not verified on a page)
- Search summaries described Pomerance's "form (1)" vaguely or wrongly; I used the PDF text above instead.
- A 2025 arXiv listing (https://arxiv.org/html/2507.20428v1, BBP-type formula for the remainder of the Madhava-Gregory-Leibniz series) and Integers l66 (https://emis.univie.ac.at/journals/INTEGERS/papers/l66/l66.pdf) appeared in results; not opened.
- Plouffe-hosted copy of Chamberland: http://www.plouffe.fr/simon/Citations/Binary%20BBP-Formulae%20for%20Logarithms.pdf (not opened). Chamberland's page: https://chamberland.math.grinnell.edu/papers/bbp.pdf (not opened).

## Not found
- No paper/MO/MSE/blog proving log 23 has no binary BBP formula, nor giving one.
- No general theorem classifying m with log m having a binary BBP formula, and nothing using Baker's theorem for this. (Chamberland points to Borwein-Borwein-Galway for related questions.) The HTML version of Chamberland (chamberland4.html) returned 404.

## URLs used
- https://cs.uwaterloo.ca/journals/JIS/VOL6/Chamberland/chamberland60.pdf
- https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf
- https://www.cambridge.org/core/services/aop-cambridge-core/content/view/BB7919C8E1AE66878AE8D7BC7F0EBFA3/S0008414X0003385Xa.pdf/finding-and-excluding-b-ary-machin-type-individual-digit-formulae.pdf
- https://oeis.org/A104885
- https://arxiv.org/pdf/1906.09629
- https://arxiv.org/pdf/1603.07395
- https://arxiv.org/pdf/1603.05810
- https://arxiv.org/pdf/2208.07696
