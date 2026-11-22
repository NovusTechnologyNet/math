# Novelty check: binary BBP-type formulas for pi (results A, C, D, E)

Date: 2026-11-22. About 24 web searches used (cap 30). Evidence is labelled **[PRIMARY]** (I read the page text or an extracted PDF; where a tool returned only a model summary, that is noted) or **[SNIPPET]** (only seen in a search-result summary). Absence of prior art means "not found in these searches", not a proof of novelty.

## Verdicts

| Result | Verdict | Confidence |
|---|---|---|
| A (all Q-relations among pi, arctan 1/2^m, arctan 1/(2^m-1)) | No prior art found. It answers an explicitly posed open problem (BBG 2004, Appendix D (2)). | Medium-high |
| C (period 120, dim 8 / dim 13, explains Bailey Table 1) | No prior art found. Bailey (2023) says the phenomenon is "not understood"; the literature proves individual relations or explains origins of some. | Medium-high |
| D (nonzero term at gcd(k,120) <= 3; six-coefficient value formula) | No prior art found. | Medium |
| E (optimality 2/3 term per bit; Huvent attains; answers Bellard) | No prior art found for an optimality proof. Bellard's page still says open. Huvent's formula is y-cruncher's default. | Medium-high |

## Detail

### Result A
- **[PRIMARY, pdftotext of the Cambridge PDF]** BBG 2004, Appendix D, item (2): asks how many Q-linearly-independent binary Machin-type BBP arctangent zero relations exist, and whether there are good upper bounds. This is the target problem. The paper itself exhibits two independent zero relations ((35), (36)) among its generators and does not classify. It uses Bang/Zsigmondy in Z[i] only for exclusion results; item (7) of Appendix D suggests an effective Zsigmondy for Q[i]. No Baker-theorem classification there.
- Note for wording: BBG's two zero relations are among their generators (with the pi/4 piece already absorbed in the Aurifeuillian generators), so check that your "three relations" statement is phrased compatibly.
- **[SNIPPET]** Stormer-type work: Yamada, "Three-term Machin-type formulae" (arXiv 1811.09273) uses linear forms in logarithms for finiteness of three-term arctan(1/m) formulas with general integers m, not the 2^m family. Gasull-Luca-Varona (arctan(2^k/m) variants) also snippet only. None classifies relations among arctan(1/2^m), arctan(1/(2^m-1)).
- Not checked: Google Scholar "cited by" for BBG 2004 (not reachable with these tools). Recommend checking manually.

### Result C
- **[PRIMARY, pdftotext of Bailey 2023, section 12]** Bailey: "it is not understood why zero relations occur" for certain parameters. Relations were found by PSLQ. Cites only Broadhurst's manuscript [21] "Vanishing Polylogarithmic Ladders" (March 2000, "available from author") as discussion, and Lafont's 2011 manuscript [30].
- **[PRIMARY, via WebFetch summary of the slideshare page]** Lafont, "Degree 1 BBP-Type Zero Relations" (27 Jan 2011): proves the 8 previously unproved binary degree-1 zero relations (5 of length 24 in base 2^12, 3 of length 40 in base 2^20) by Fourier analysis plus numerical identification, and says all degree-1 binary formulas in the Compendium are now proved. No Baker, period, or dimension. So individual relations are known; no structural or count theorem seen.
- **[PRIMARY, abstract via WebFetch]** Barsky, Munoz, Perez-Marco, "On the genesis of BBP formulas" (arXiv 1906.09629): explains where some null formulas come from; no classification or count; no Baker.
- **[PRIMARY, via WebFetch summary of ar5iv]** Kristensen and Mathiasen, "BBP-type formulas - an elementary approach" (arXiv 2208.07696): search algorithm, tables of null formulas in bases 2^4, 2^6, 2^12, 2^20; no Baker, no period 120.
- **[SNIPPET]** Adegoke (arXiv 1603.05810) and Adegoke-Lafont-Layeni (arXiv 1603.07395, section 6.3 "Binary Zero Relations"): proofs of individual relations. I could not read 1603.07395 (tool returned only an outline).
- Broadhurst's manuscript: **not found online**. Only his published ladder papers (arXiv math/9803067, math/9906134) surfaced, seen as snippets. Its contents are unknown to me. It is the main possible overlap; ask Broadhurst or Bailey for it.

### Result D
- No source found that states a lower bound on gcd(k,120) for a non-zero term, or a six-coefficient value formula. Nothing read in Bailey, Lafont, Adegoke, Kristensen-Mathiasen or Barsky et al. addresses it.

### Result E
- **[PRIMARY, via WebFetch of Bellard's page]** https://www.bellard.org/pi/pi_bin/pi_bin.html: whether a faster formula exists "remains an open question" (the tool's quote of the page). No later answer found.
- **[PRIMARY, version history text]** y-cruncher v0.8.4.9537 (21 Feb 2024) added Huvent's BBP formula, "slightly faster than Bellard's"; v0.8.5.9539 (1 Jul 2024) made it the default. Only the first 100000 of 114741 characters were read; no denominators are given there.
- **[PRIMARY, pdftotext]** Bailey 2023 credits G. Huvent with a degree-2 formula (39) and proofs of formulas 45-54, but I did not find Huvent's pi formula (denominators y^24 - 2^12) in it. I could not find Huvent's 2001 pi formula online in several searches, so the "2001" date and the formula's shape are unverified here.
- No proof of optimality of any BBP-type pi formula found, and no claim of it being open other than Bellard's remark. Nothing found for a "7/24" second cost measure.

### Lean / Isabelle / Coq
- **[SNIPPET]** Coq: Bertot, Rideau, Thery, "Distant decimals of pi" (arXiv 1709.01743) formally verifies BBP-style hex digit extraction. Not a classification.
- No Lean/Mathlib or Isabelle BBP formalization found. A self-published Lean "pi transcendence" blog claim appeared; unverified and irrelevant.

## Could not do
- Read Broadhurst's 2000 manuscript (not online as far as found).
- Read Adegoke-Lafont-Layeni body text, Bailey's 2004 PDF, Huvent's original source, or Scholar citations of BBG 2004.
- Search 2025-2026 arXiv exhaustively; one targeted query found nothing relevant.

## URLs used
- https://www.davidhbailey.com//dhbpapers/bbp-formulas.pdf
- https://www.cambridge.org/core/services/aop-cambridge-core/content/view/BB7919C8E1AE66878AE8D7BC7F0EBFA3/S0008414X0003385Xa.pdf/finding-and-excluding-b-ary-machin-type-individual-digit-formulae.pdf
- https://www.slideshare.net/slideshow/zero-relations/13076965
- https://arxiv.org/abs/1906.09629
- https://ar5iv.labs.arxiv.org/html/2208.07696
- https://arxiv.org/pdf/2208.07696
- https://www.bellard.org/pi/pi_bin/pi_bin.html
- https://numberworld.org/y-cruncher/version_history.html
- https://arxiv.org/pdf/1603.07395 (unreadable)
- https://arxiv.org/pdf/1603.05810 (snippet)
- https://arxiv.org/pdf/1811.09273 (snippet)
- https://arxiv.org/pdf/1709.01743 (snippet)
- https://cs.uwaterloo.ca/journals/JIS/VOL6/Chamberland/chamberland60.pdf (snippet)
- https://www.arxiv.org/pdf/math/9906134 and https://web3.arxiv.org/pdf/math/9803067 (snippets)
- https://corpora.tika.apache.org/base/docs/govdocs1/656/656518.pdf (snippet)
