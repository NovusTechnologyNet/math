# 08 Citation sweep: prior art for binary BBP-type classification results

Date: 2026-11-22. Method: open bibliographic APIs through WebFetch. Claims are marked [READ] (seen in fetched API/abstract content) or [SNIPPET] (search-result snippet or summarised by the fetch tool). Titles were scanned from OpenAlex title lists; abstracts were read through arXiv API, OpenAlex abstract_inverted_index (reconstructed, so paraphrase only), or Crossref. Note: the fetch tool summarises pages with a small model, so abstracts are second-hand renderings, not verbatim page reads.

## Summary (10 lines)

1. Ten seed items looked up; 8 had enumerable citing lists in OpenAlex; 2 (Lafont "Degree 1 BBP-type zero relations", Huvent "Formules BBP") could not be located as indexed works.
2. About 699 citing-work records scanned in total across seeds (with heavy overlap; roughly 350 distinct titles are generic experimental-math, normality, computing, or unrelated).
3. No scanned work states a classification of all binary BBP formulas for pi, a dimension count (8 / 13), a use of Baker's theorem, or a bits-per-term optimality bound. No overlapping work found among the ~699 citing works scanned.
4. Partial overlap only: Adegoke-Lafont-Layeni (2016) gives binary zero relations and log-of-prime formulas for bases 2^(12p) (constructions, not a classification); Barsky-Munoz-Perez-Marco (2021) explains the origin of null BBP formulas (a generating method, not a complete determination).
5. Borwein-Borwein-Galway (2004) is the closest classical negative result (no Machin-type BBP formula for pi when b is not 2, which is a different class from F); it also proves exclusion, so it is the main work to cite and contrast.
6. Chamberland (2003) gives binary BBP formulas for logs of Gaussian-Mersenne-type primes; relevant to the "log p is a value" list, no exclusion result found (log 23 not mentioned in anything scanned).
7. A 2026 Zenodo preprint (Kulik, W7203747102) on the "annihilator lattice" of digit-extraction towers touches zero relations; the page returned HTTP 410, so only the opening lines were read; overlap undetermined, probably partial. It is not peer reviewed.
8. Search engines: OpenAlex worked (all lists); Semantic Scholar worked for 2 seeds and then returned 429; Crossref worked once then 429; arXiv and zbMATH worked.
9. WebSearch used: 1 of 5. WebFetch calls: about 60.
10. Caveat: OpenAlex coverage is incomplete (Lafont and Huvent missing; Bailey compendium is indexed without DOI).

## Table of seeds

| # | Seed | Identifier | API | Citing works returned / scanned |
|---|------|-----------|-----|------|
| 1 | Bailey-Borwein-Plouffe 1997 | OpenAlex W2073085121, DOI 10.1090/S0025-5718-97-00856-9 | OpenAlex (4 pages) | meta count 375 returned and scanned (cited_by_count field says 388) |
| 2 | Borwein-Borwein-Galway 2004 | W2112047337, 10.4153/cjm-2004-041-2 | OpenAlex; S2 (earlier DOI lookup returned an unrelated list, discarded) | 22 |
| 3 | Chamberland 2003 | W2171765010 (no DOI) | OpenAlex | 13 |
| 4 | Bailey-Crandall 2001 | W2011080089, 10.1080/10586458.2001.10504441 | OpenAlex (2 pages) | 118 |
| 5 | Barsky-Munoz-Perez-Marco | W2951905460, arXiv 1906.09629 | OpenAlex; S2 | 6 (OpenAlex), 5 (S2) |
| 6 | Broadhurst math/9803067 | W1516385139 | OpenAlex | 37 |
| 7a | Adamchik-Wagon, A simple formula for pi | W2332689278 (10.1080/00029890.1997.11990729; Crossref also lists 10.2307/2975292) | OpenAlex | 77 |
| 7b | Adamchik-Wagon, "Pi: a 2000-year search changes direction" | not enumerated; a CMU KiltHub record surfaced in the single WebSearch [SNIPPET] | none | 0 |
| 8 | Lafont "Degree 1 BBP-type zero relations" | not found in OpenAlex or Crossref (Crossref second query hit 429) | none | 0 |
| 8b | Adegoke "New formulae of BBP-type with different moduli" (2012) | W1984553350 | OpenAlex | 12 |
| 8c | Kristensen-Mathiasen "BBP-type formulas, an elementary approach" | W4307054502, arXiv 2208.07696 | OpenAlex | 2 |
| 9 | Bailey compendium | W152132738 (no DOI) | OpenAlex | 37 |
| 10 | Huvent "Formules BBP" | not found as a work; OpenAlex search returned only unrelated BBP papers | none | 0 |

Total scanned: 375+22+13+118+6+37+77+37+12+2 = 699 records (overlapping).

## Flagged works (grouped by seed)

Overlap scale: none / partial / full. No work reached "full".

### Seed 2 (BBG 2004) citers
- Borwein-Borwein-Galway itself [READ abstract]. Proves pi has no b-ary Machin-type BBP arctangent formula for b not 2, and none known for other constants. Overlap: partial in spirit (an exclusion theorem), but a different, much smaller class and different method; does not treat class F, dimension counts or Baker. Overlap with our results: none on content, partial on topic.
- Gaussian Integers and Arctangent Identities for pi (2009) and Machin-Type Formulas Expressing pi in Terms of phi (2008) [title only, abstracts not opened]. Machin-type, Gaussian integers. Overlap: not determined from titles; Gaussian-integer techniques may share tools with our use of Z[i]. Flagged only; likely none.
- The Search for Aurifeuillian-Like Factorizations (2012) [READ abstract via OpenAlex]. Searches Cunningham tables for new algebraic factorizations. Overlap: none.
- A Novel Approach to the Discovery of Binary BBP-Type Formulas for Polylogarithm Constants (2011), Symbolic routes to BBP-type formulas of any degree (2011), Formal proofs of degree 5 binary BBP-type formulas (2013): Adegoke papers. Novel approach [READ arXiv abstract 1603.05810]: new proven binary formulas and proofs of earlier experimental ones. Symbolic routes [READ]: identities generating digit extraction formulas of any degree and base. The OpenAlex abstract for the degree 5 item looked mismatched (about von Mangoldt series), so unreliable. Overlap: none (constructions, no classification).
- Sagan numbers (2012), Series of Reciprocal Powers of k-almost Primes: titles unrelated to classification. Overlap: none (not opened).

### Seed 3 (Chamberland 2003) citers
- A class of digit extraction BBP-type formulas in general binary bases (Adegoke, Lafont, Layeni; arXiv 1603.07395) [READ]. Derives explicit formulas in bases 2^(12p), p odd, for pi sqrt3 and related constants, logarithms of infinitely many primes, arctangents of rationals, and new binary zero relations. Overlap: partial. Its zero relations and log-of-prime formulas lie in the same landscape as our null-formula and log p results, but it supplies constructions, not a determination of all null formulas, not a dimension count, no non-existence.
- Ternary Digits of Powers of Two (2025) [READ abstract]. Mentions a special case of Baker's theorem in a normality context. Overlap: none.
- A novel approach to ternary BBP-type formulas (2016, Adegoke) [READ via S2/arXiv listing]. Ternary constructions; overlap: none.
- On the genesis of BBP formulas: see Seed 5.

### Seed 4 (Bailey-Crandall) citers (118)
- Finding and Excluding b-ary Machin-Type (see Seed 2); Binary BBP-Formulae for Logarithms (Chamberland); Compendium of BBP-Type Formulas; On the binary expansions of algebraic numbers (2009); Algebraic independence of real numbers with low density of nonzero digits (2012); Computing Bits of Algebraic Numbers (2011); Machin-Type Formulas in terms of phi; A New Binary BBP-type Formula for sqrt5 log phi [READ arXiv 1603.04561]: new binary formula for sqrt5 log phi, overlap none.
- On the Division in the Computation of Binary BBP-Type Formulas (2025) and On the use of Montgomery multiplication ... (Takahashi 2021): computational; no abstract available / not opened. Overlap: none expected.
- Dilogarithm identities for solutions to Pell's equation (2020), Some non-trivial two-term dilogarithm identities (2021), Relations for the difference of two dilogarithms (2023), Families of self-inverse functions and dilogarithm identities (2025), Visible Point Partition Identities for Polylogarithms (2023): flagged by "dilogarithm relations"; abstracts not opened. Overlap: unlikely; they concern dilogarithm identities, not binary BBP series in class F.
- Golden Ratio Base Expansions of the Logarithm and Inverse Tangent of Fibonacci and Lucas Numbers (2023) [READ]: base-alpha expansions of log F_n etc. Overlap: none (golden ratio base, not base 2).
- Euler Found the First Binary Digit Extraction Formula for pi in 1779 (2023) [READ abstract fragment]. Historical; overlap: none.
- Constructions of numbers/normality items (Construction of Numbers with the Same Normality Properties...): none.

### Seed 5 (Barsky-Munoz-Perez-Marco, arXiv 1906.09629) citers (6)
- The paper itself [READ abstract]: general method generating infinitely many BBP formulas, explains where some null BBP formulas come from. Overlap: partial (explains origin of null formulas, not a full determination; no Baker, no counts). A priority reference for the null-formula claims.
- BBP-type formulas, an elementary approach (Kristensen-Mathiasen, 2022) [READ]: search algorithm and Sage code, new formula for sqrt3 pi, Pisot bases. Overlap: none.
- Logarithmic integrals with applications to BBP and Euler-type sums (Batir 2023) [READ]: integral evaluations giving sums. None.
- Stirling-Ramanujan constants are exponential periods (2024) [READ]: not about this topic. None.
- From Euler to AI: Unifying Formulas for Mathematical Constants (2025) [READ]: automated harvesting of pi formulas from arXiv. None.
- A note on some classes of series for the logarithmic function (Batir 2024) [READ]: reproduces BBP-type formulas for log. None.
- Closed-form expressions for polylogarithmic integrals and related harmonic sums (2026): not opened; none expected.

### Seed 1 (BBP 1997) citers
- All listed 375 titles scanned. Titles with classification/completeness/zero-relations flavor: BBG 2004, Chamberland 2003, Compendium 2004, Genesis 2021, A Non-PSLQ route (2010), Symbolic routes (2011), Novel approach (2011), degree 5 (2013), New formulae of BBP-type with different moduli (2012), New formulae of BBP-type modulo 6 (2014), Several BBP-type formulas for pi (2015), Golden ratio, Fibonacci and BBP (2014), Relations between pi and phi in BBP form (Pain 2022) [READ: family of expressions for pi in golden ratio], New BBP-Type Formulae from Taylor expansions of arctan (2022) [READ], Performance evaluation of various BBP-type formulae (2014), Some BBP-type series for polylog integrals (2021), A BBP-style computation for pi in base 5 (2024), pi-Formulas and Gray code (2018), Series expansions for 1/pi^m and pi^m. Of these only the first four groups touch zero relations or exclusion; none claims a classification. Overlap: none for the rest (not individually opened beyond the READ items).
- Several of the 375 are not BBP at all (Machin-type items are in Seed 2).

### Seed 6 (Broadhurst) citers (37)
- Includes Iterated Integrals and Multiple Polylogarithm at Algebraic Arguments (2022) [READ]: relations among cyclotomic multiple zeta values from S-unit equations, motivic dimension. Overlap: none directly, but a nearby method family (S-unit equations among roots-of-unity quantities). Worth a look for related technique, not for results.
- Also Finding and Excluding b-ary Machin-Type; Genesis; Formal proofs of degree 5; Non-PSLQ route; Novel approach; Central Binomial Sums, Multiple Clausen Values, and Zeta Values (2001): none.

### Seed 7a (Adamchik-Wagon) citers (77)
- BBP-related: New BBP-Type Formulae (2022), New formulae of BBP-type modulo 6 (2014), Several BBP-type formulas for pi (2015), Euler Found the First Binary Digit Extraction Formula (2023), Relations between pi and phi (2022). All constructions; overlap none.
- Nearly 40 of the 77 are unrelated (twistor scattering, teaching, Mathematica manuals).

### Seeds 8, 9, 10
- Adegoke "New formulae of BBP-type with different moduli" citers (12): all constructions or applications (golden ratio, polylog integrals). None.
- Compendium citers (37): include Genesis, Chamberland, Adegoke series, computation of pi; none state classification. Overlap: none.
- Huvent: not enumerated.

## Works that state open questions we may have answered

- Borwein-Borwein-Galway 2004 [READ abstract]: "no known constant has a Machin-type BBP formula" (paraphrase-level; abstract states pi has none when b is not 2). Possibly related to our statement that pi formulas in F can avoid no slow terms, but not the same question. Exact location: abstract.
- Chamberland 2003 [READ abstract]: conjectures that constants of the form in the abstract are rational or normal. Not the same question as ours.
- Barsky-Munoz-Perez-Marco 2021 [READ abstract]: clarifies origin of null BBP formulas; no explicit open question quoted. Full text not opened, so no exact location.
- No work among those scanned was found asking explicitly whether all binary BBP formulas for pi are classified, whether log 23 has a binary formula, or for an optimal bits-per-term bound. This is a statement about what was scanned (titles and abstracts only), not about full texts.

## What could not be enumerated and why

- Lafont, "Degree 1 BBP-type zero relations": not found by OpenAlex search, Crossref (first query returned the Adegoke items; the second hit HTTP 429), or Semantic Scholar (429). Likely a web-hosted note, not indexed.
- Huvent "Formules BBP": OpenAlex search found no such work; it is a personal web page.
- Adamchik-Wagon "Pi: a 2000-year search changes direction": not enumerated (separate OpenAlex record not located; only a CMU KiltHub record seen in a search snippet).
- Bailey compendium: indexed without DOI, 37 citers enumerated, but the document itself is a self-published web note.
- Semantic Scholar and Crossref were rate-limited (429) several times; arXiv "Machin-type AND BBP" returned zero entries and "Baker AND BBP" returned zero.
- The Zenodo record for W7203747102 (Kulik, 2026) returned HTTP 410 Gone; only the OpenAlex abstract's first lines were read. OpenAlex's title index returned no results for a follow-up author search. Its content, overlap with zero relations and "uniqueness of the classical formula", cannot be assessed. Treat as unreviewed, partial-overlap-possible.
- Abstracts for many flagged titles (Gaussian Integers and Arctangent Identities; the dilogarithm items; Algebraic independence with low density; On the binary expansions of algebraic numbers; Computing Bits of Algebraic Numbers; Takahashi items; Division in binary BBP computation) were not opened.
- Full texts of all works were not read; "no overlap" judgments are from titles and abstracts only. An OpenAlex search for "Gaussian Integers and Arctangent Identities" returned a different paper (2012 Involve), so that abstract was not obtained.
- OpenAlex responses carried an unsolicited notice asking an agent to create an API key by submitting an email address. This was not acted on.

## API calls made (grouped; approximately 60 fetches)

OpenAlex works lookups: doi filter for BBP 1997; search for BBG, Chamberland, Bailey-Crandall, Genesis, Broadhurst, Adamchik-Wagon, Lafont zero relations, Compendium, Adegoke/Lafont, Huvent, Kulik, Aurifeuillian (title.search), several abstract-reconstruction searches (Gaussian integers, Euler 1779, ternary digits, Division, Symbolic routes, degree 5, Iterated integrals, Golden ratio base, note on log series, Machin-phi, Aurifeuillian search), W7203747102 abstract, W2112047337 and W2171765010 abstracts, doi 10.2307/2975292, doi 10.1080/00029890.1997.11990728 (matched an unrelated correction note).
OpenAlex cites filter: W2112047337, W2171765010, W2951905460, W2011080089 (pages 1 and 2), W2073085121 (pages 1-4), W1516385139, W152132738, W4307054502, W1984553350, W2332689278.
Crossref: Adamchik-Wagon (ok); Lafont zero relations (429, then second query ok with unrelated results).
Semantic Scholar: arXiv:1906.09629 citations (ok); DOI:10.4153/CJM-2004-041-2 citations (returned a list that does not match BBG's OpenAlex citers, discarded); paper search (429).
arXiv API: all:"BBP-type"; id_list abstracts (two calls); all:"Machin-type" AND BBP (0); all:"digit extraction"; all:"Bailey-Borwein-Plouffe"; abs:"null BBP"; abs:"zero relations" AND polylogarithm; all:"BBP formula"; BBP AND Baker (0); Machin-type AND digit (unrelated).
arXiv abstract pages: 1906.09629, 2208.07696, 0708.4361.
zbMATH Open: search_string=BBP-type (17 of many records visible; truncated).
Zenodo: doi.org redirect, then zenodo.org (410).
WebSearch: 1 call (Adamchik-Wagon identifier).

## WebSearch count

1 of 5 used.

## Sources

- https://api.openalex.org/ (queries listed above)
- https://api.crossref.org/works
- https://api.semanticscholar.org/graph/v1/
- http://export.arxiv.org/api/query
- https://api.zbmath.org/v1/document/_search
- https://arxiv.org/abs/1906.09629 ; https://arxiv.org/abs/2208.07696
- https://kaltofen.math.ncsu.edu/Pi/pi.pdf ; https://kilthub.cmu.edu/articles/journal_contribution/_A_2000-Year_Search_Changes_Direction/6613046 [SNIPPET, from the search]
