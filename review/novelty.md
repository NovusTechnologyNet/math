# Novelty ledger: what is known, what was searched, who was asked

One row per result. The routine and the labels are in `PRACTICES.md`, section 3. This file was
first written on 25 November 2026 from the research reports in `research/`; those reports are
summaries made by AI helpers of sources they read, and they can be wrong. "Not found in print"
means that the searches named found nothing: it is weak evidence, and MathSciNet and zbMATH
were not searched for any row. No specialist has been asked about any row yet; writing to one
is the repository owner's decision.

Labels: **known**; **stated as known, proof not found in print**; **not found in print
(searched DATE)**; **prior work found (DATE)**; **not searched**.

| Result (Lean name) | Label | What the searches found | Asked |
|---|---|---|---|
| Theorems A, C, D, E: the class F of binary formulas for pi (`PiFormula.theoremA`, `Unconditional.theoremC`, `theoremD_sharp`, `theoremE`) | not found in print (searched 22 Nov 2026) | No earlier statement in about 24 searches (`research/2026-11-22/novelty_check.md`) and in 57 targeted searches, about 700 citing papers and ten papers read closely (`research/2026-11-22-deep/03_novelty_pi_classification.md`). Not seen: Broadhurst's unpublished manuscript of 2000. Known pieces, credited in the note: the zero-relation counts 1, 5, 3, 7 are in Bailey's Compendium (found by PSLQ, called "not understood" there), so Theorem C is a proof of that table and not a new count; both formulas that attain 2/3 are Huvent's (2001), so Theorem E adds the lower bound and the uniqueness; Lemma 2 is Schinzel 1962, Theorem 2 (a = 2, b = 1) and Drauschke-Tasche 1987, Theorem 4.2, which credits Redei and Sachs; Bang 1886. | no |
| Theorem B: the cyclotomic family (`PiFormula.theoremB`) | not searched | Covered only by the searches for Theorem A. | no |
| Theorems G, H, K: logarithms in class F (`Unconditional.no_log23`, `log_primes_below_100`, `isFValue_log_rat_iff_pow`) | not found in print (searched 22 Nov 2026) | Chamberland 2003 raises log 23; Bailey's Compendium says it is unknown whether every prime has a binary formula for its logarithm (`research/2026-11-22/log23_status.md`, `research/2026-11-22-deep/04_novelty_logarithms.md`). Our answer is inside class F only. | no |
| Theorem I: arctan(2/7) (`Unconditional.not_isFValue_arctan_two_sevenths`) | not searched | Bailey's Compendium prints the question as open. No separate search is recorded. Inside class F only. | no |
| Theorem J: cost of a checked pair (`Unconditional.pairCost_ge`, `checkedPair`) | not searched | The two formulas are Takahashi's (Ramanujan J. 2020). The lower bound 60 came from our computation and is now a Lean theorem; no separate search is recorded. | no |
| Base 3: Theorems K3, C3, E3 (`Base3.Unconditional.*`) | not found in print (searched 22 Nov 2026) for the completeness and the optimum; the relations themselves are **known** | In print: Compendium relations 130 and 131, Adegoke's zero relation (2010), Broadhurst's formula 69; Lemma H is Schinzel 1962, Theorem 2 (a = 3, b = 1); the transcendence of the values is Adhikari-Saradha-Shorey-Tijdeman 2001. Borwein-Borwein-Galway 2004 leave base 3 open (their research problem 10). The second optimal pattern `rhoSecond` was not found in the inventory of printed base-3 formulas. Reports: `research/2026-11-22-base3/`. | no |
| Base 5: Theorems C5, K5 (`Base5.Unconditional.*`) | not found in print (searched 22 Nov 2026) | Borwein-Borwein-Galway 2004, Theorem 7 excludes pi for the narrower Machin-type class only; nothing found on zero relations in base 5 or on pi for a class this wide (`research/2026-11-22-base5/00_summary.md`). | no |
| Values are 0 or transcendental, bases 2, 3, 5 (`Transcendence.lean`) | known | Adhikari, Saradha, Shorey, Tijdeman 2001. | - |
| Theorem G for every base b >= 5 (`BaseB.Unconditional.eq_zero_of_hasSum_mul_pi`) | not found in print (searched 22 Nov 2026) | An extension of Borwein-Borwein-Galway, Theorem 7 from the Machin-type class to the whole step-2 class (`research/2026-11-22-nonbinary-pi/00_summary.md`). | no |
| Theorem L: no degree-1 formula for pi unless the base is a power of 2 (`BaseB.no_pi_bailey`) | stated as known, proof not found in print | Bailey's Compendium (2023 version, p. 2) gives the statement as shown by Borwein-Borwein-Galway 2004; that paper proves the Machin-type case and asks the general question in its Comment (10). Bailey-Borwein-Plouffe 1997 says J. P. Buhler "has reported a proof" of a statement of this kind; no proof or reference was found. So: reported in 1997, never published as far as we found; ours is written down and machine-checked. Never "first proof". Reports: `research/2026-11-22-nonbinary-pi/`. | no (Bailey, the authors of the 2004 paper, Buhler) |
| Theorems M, N: logarithms in a general base (`BaseB.bailey_log_self_iff`, `no_log_nat_bailey`) | not searched | Nearest in print: Borwein-Borwein-Galway 2004, Example 4 (Machin-type, ln 10). | no |
| Theorem F: other binary families, terms per bit (`BaseB.terms_per_bit`) | not searched | - | no |
| Theorem R: rational bases (`RatBase.hasRelation_iff`) | not found in print (searched 22 Nov 2026) for the classification | The five bases are exactly the pairs in the exception list of Schinzel 1962, Theorem 2 (read 23 Nov 2026, `research/2026-11-23-schinzel/02_paper_read.md`). The relation in base 4/3 is in print in an equivalent form (Adegoke-Layeni 2010); the formula for pi/4 in base 3/2 was not found in print. Report: `research/2026-11-22-rational-bases/00_summary.md`. | no |
| Bailey's Compendium, verified (`Compendium.formula_*`) | known | A check of a published paper; nothing is claimed as new. The small errors found in the paper are listed in `literature/bailey-compendium/`. | no (Bailey) |
| Erdos's conjecture, q odd and not a perfect square (`Erdos.erdos_pm_one_nat`) | not found in print (searched 23 Nov 2026) | Not stated in any paper found (`research/2026-11-23-erdos-pm1/E1_priority_check.md`, `E2_wide_priority_search.md`); Chatterjee-Murty 2015, Pathak 2019, Murty-Pathak 2022 and Bharadwaj 2022 call q = 1 mod 4 open. Not seen: a submitted paper by Bharadwaj, Murty and Pathak on the conjecture, which may contain this case or more. **Priority is not established.** | no (Pathak, Murty, Bharadwaj) |
| Erdos's conjecture, the other cases in `erdos_pm_one_of_cases` | known | q prime: Baker-Birch-Wirsing; q = 3 mod 4: Murty-Saradha 2010; the size condition q <= 2 phi(q): Okada, Chatterjee-Murty; q even. As listed in the priority searches (`E1_priority_check.md`, `E2_wide_priority_search.md`); the attributions in the Lean docstrings of these files were written from memory. | - |
| Okada's criterion, both directions (`Erdos.okadaCriterionGeneral`) | known | Okada 1982; ours is a formalization. | - |
| Odd squares: an odd-valued f with sum 0 exists exactly when q is a square (`Erdos.exists_oddValued_sumIsZero_iff`) | not searched | - | no |

## Findings about printed lists

| Finding | Evidence | Told the author |
|---|---|---|
| The entry 38737 of OEIS A104885 (primes p with a binary formula for log p) does not belong, inside class F: log 433 + log 38737 is a value, neither logarithm alone is. The entry comes from the list in Chamberland 2003. | `Unconditional.not_isFValue_log_38737`, `not_isFValue_log_433`, `isFValue_log_433_add_log_38737` | no |
