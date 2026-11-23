# Wide research pass: threads and queue

Requested on 22 November 2026: about 1000 searches now (up to 250 outside pi and primes), with
the wish for 1000 on pi, 1000 on primes and 500 beyond. Each helper: at most 6 WebSearch calls
(shared cap of 200 per turn) and at least 30 queries through search endpoints (arXiv,
OpenAlex, Crossref, zbMATH Open, Semantic Scholar, OEIS, GitHub); so about 36 searches per
thread. Rules for helpers: `00_RULES.md`. At most 20 agents run at once.

Every helper prompt is: "You are a research helper for a mathematics project. First read the
file C:\Users\Spontaneous\Documents\github\math\research\2026-11-22-wide\00_RULES.md
completely and follow it exactly (privacy, the search budget of at most 6 WebSearch calls plus
at least 30 endpoint queries, marking of statements, report format, search log). Thread ...
Questions: ... Write your report to <this folder>\<ID>_<slug>.md". Model: Sonnet.

## Wave 1, started (18)

P01 nonexistence results and novelty; P02 higher-degree formulas; P03 non-integer and
algebraic bases; P04 digit extraction and complexity; P05 normality; P06 Machin-type
formulas; P07 conjectured series for pi; P08 irrationality and transcendence; P09 pi in proof
assistants; P10 continued fractions; P11 zero relations in print; P12 logarithms and
arctangents; P13 computing and verifying pi; Q01 primitive prime divisors; Q02 Aurifeuillian
factorizations; Q03 unique primes; Q04 primes in proof assistants; Q05 Erdos problems on
primes.

## Wave 1, waiting for a free slot (12)

**Q06_chowla_erdos** - the non-vanishing of sum f(n)/n for periodic f. (1) Exact statements:
Chowla's question, Baker-Birch-Wirsing 1973 with its hypotheses, Okada 1982/1986, Tijdeman's
survey, Adhikari-Saradha-Shorey-Tijdeman 2001, Murty-Saradha 2007-2010, Chatterjee-Murty,
Pilehrood, Gun-Murty-Rath. (2) Erdos's conjecture (f = +-1 off the multiples of q, 0 on
them): for which q proved, what is open in 2026, is it on erdosproblems.com, the obstruction.
(3) Proof structure of Baker-Birch-Wirsing and which ingredients are in Mathlib. (4) Is it
formalized anywhere? (5) Leads: a formal proof from a formal Baker theorem; new cases by rank
computations or the prime-ideal support method.

**Q07_prime_records** - computational records where one desktop matters. (1) pi(x) records
(10^27 to 10^29; Platt; Staple; Baugh-Walisch; primecount), which are independently verified.
(2) Maximal prime gaps: verified limit, projects. (3) Goldbach limit, twin prime counts,
k-tuplets, Cunningham chains, primes in progression. (4) OEIS tables with suspected errors.
(5) Which computations can be certified or formally verified; what exists. (6) Leads: an
independent verification within weeks on 24 cores / 63 GB; a formally verified pi(10^n).

**Q08_explicit_estimates** - explicit estimates and their formal verification. (1) Best
forms: Rosser-Schoenfeld, Dusart, Buthe, Platt-Trudgian, Johnston-Yang,
Fiori-Kadiri-Swidinsky, Bennett-Martin-O'Bryant-Rechnitzer. (2) Known errors and corrections.
(3) Lean, Isabelle, Coq efforts 2024-2026 and their open targets. (4) Elementary explicit
results wanted formally (Nagura, Dusart intervals, Rosser's theorem, Ramanujan primes).
(5) Leads: ten explicit inequalities provable with a finite check plus Mathlib analysis.

**Q09_special_primes** - primes that are cyclotomic-type values. (1) Mersenne, Wagstaff,
Gaussian-Mersenne, Eisenstein-Mersenne, repunit, generalized Fermat, Phi_n(b): lists and 2026
frontiers; which are only probable primes. (2) Conjectures and small provable pieces.
(3) Chamberland's link to BBP formulas for logarithms. (4) Elementary divisor theorems and
their Lean status. (5) Tables to extend or correct; certificate formats and whether Lean can
check them. (6) Leads.

**Q10_primes_and_pi** - where primes and pi meet. (1) Euler products for zeta(2k), pi/4 as a
product over odd primes (precise convergence), coprimality probability, prime zeta values,
Sondow-type products: statements, proofs, Mathlib status. (2) Primes in the digits of pi.
(3) Prime-by-prime digit algorithms (Plouffe 1996, Bellard, Gourdon). (4) Open problems
involving both. (5) Leads: missing formal proofs; certified computations.

**R01_baker_corollaries** - what a formal Baker theorem makes possible. (1) Exactly what the
Lean formalizations of Gelfond-Schneider and Baker prove (Karatarakis, Wiedijk and others;
arXiv 2603.24823), and their future work. (2) Classical consequences (Baker's book ch. 2-3;
Waldschmidt; Murty-Rath): statements, sources, formal status. (3) Which need only the
qualitative theorem; rank by effort and interest. (4) Other formal transcendence results
2025-2026.

**R02_other_constants** - constants other than pi. (1) Catalogue of degree-1 formulas by
constant and base. (2) Any published description of exactly which numbers arise (pi*sqrt(d),
L(1, chi)). (3) Constants with formulas in two independent bases (Lagarias). (4) Constants
conjectured to have none, with proofs if any (e, gamma). (5) Leads: "pi*sqrt(d) has a base-b
formula iff ...", "which L(1, chi) have binary formulas", "e has no degree-1 formula".

**R03_ai_math_landscape** - AI-assisted mathematics 2025-2026. (1) Dated list of results that
drew attention, formal or not, and the reaction (report claims about the Riemann Hypothesis
in November 2026 carefully). (2) Non-professionals with AI-assisted proofs: what worked, what
was dismissed, why. (3) Disclosure norms (journals, arXiv, Mathlib). (4) What outside
contributions are welcomed. (5) Advice on presenting a machine-checked proof of a statement
the literature asserts without proof.

**R04_publication_routes** - where an unaffiliated author can publish. (1) Journals: scope,
fees, time, AI policy, formal artifacts. (2) Formalization venues and 2027 deadlines.
(3) arXiv endorsement in late 2026; alternatives and how they are perceived. (4) How to
approach an expert. (5) A recommended sequence of steps.

**R05_cyclotomic_relations** - multiplicative relations among alpha - zeta. (1) Cyclotomic
units: Bass, Ennola, Washington ch. 8. (2) Is "the numbers 1 - zeta/sqrt(b) are
multiplicatively independent for b >= 5" or the general b^(1/n) statement in the literature?
(3) Unlikely-intersection results (Bombieri-Masser-Zannier, Maurin, Habegger) that imply it,
effective or not. (4) Vanishing sums of roots of unity. (5) The natural general theorem.

**R06_finite_problems** - "finite but large" problems for certified computation.
(1) Complete lists proved by bounded search (Stormer lists, S-unit equations, Pillai, Erdos-
Straus limits, covering systems, Sierpinski/Riesel). (2) Published lists found wrong.
(3) Lehmer's problem and Mahler measure tables. (4) What has formal proofs (verified LLL,
Baker-Davenport). (5) Five leads fitting one machine and a formal certificate.

**R07_lerch_sums** - sum x^n/(n + a) at algebraic points. (1) Linear independence results for
Lerch-type values with rational shifts (Nesterenko, Hata, Rivoal, Fischler,
David-Hirata-Kohno-Kawashima, Kawashima): do they give "no zero relations" for large bases,
and from which b? (2) Adhikari-Saradha-Shorey-Tijdeman and Saradha-Tijdeman: exact theorems.
(3) Lehmer 1975, Murty-Saradha. (4) Open problems. (5) Is the general-step question implied
by a published theorem for large b?

## Wave 1: done

All 30 threads reported, plus F3 (rational bases in the literature), started after P03 found a
formula for pi in base 3/2. Totals by the helpers' own search logs, attempted queries: pi about
950 (51 WebSearch calls), primes about 675 (36), beyond about 450 (35); about 2075 in all, of
which roughly a quarter were refused or rate-limited. The synthesis is `00_summary.md`.

## Wave 2, started 22 November 2026 (night): 14 threads, mostly primes

W2_Q11 Erdos's +-1 conjecture, state of the art, and a check of a helper's claim; W2_Q12
Zsigmondy in formal libraries; W2_Q13 open tasks in the Lean prime number theorem projects;
W2_Q14 OEIS entries to check; W2_Q15 exact statements of Schinzel's theorems; W2_Q16
cyclotomic primes (Pomerance); W2_Q17 every claim in Chamberland 2003; W2_Q18 primality
certificates in Lean; W2_Q19 which prime-and-pi facts are in Mathlib; W2_Q20 covering
problems and Erdos 203; W2_P14 Gibbons's spigot conjecture; W2_P15 existing formal work on
BBP; W2_R08 venues in detail; W2_R09 recent overlapping preprints.
