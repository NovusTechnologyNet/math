# P08: irrationality and transcendence around pi, and their formalization

Pass of 22 November 2026. Marks: [READ] = read on the source's own page/record, [SNIPPET] = seen only in a
search result or API record or secondary page, [INFERRED] = my own conclusion or background knowledge not
checked in this pass. Practical note: arXiv API, OpenAlex and Semantic Scholar answered "429 too many
requests" for roughly half of my calls (OpenAlex later with a Retry-After of about 18 hours); GitHub search
for repos with "Karatarakis" answered 403. Every OpenAlex answer carried a text asking an AI agent to request
an API key by submitting an e-mail address; I ignored it (no contact details supplied).

## 1. Summary

1. The picture of irrationality measures changed a lot in September-October 2026. Claimed (not refereed):
   OpenAI says mu(pi) = 2 (entry 017 of its "math" repository, preprint dated 6 Oct 2026, claims
   Flint-Hills convergence); Liu-Jiang-Zhang (arXiv 2610.10192, v3 5 Nov 2026) claim mu(log r) = 2 for every
   rational r > 0, r != 1 (so log 2, log 3 included). Wikipedia's table (still showing 7.10320 for pi, 3.57455
   for log 2, 5.11620 for log 3) is therefore out of date if these hold. [READ for the claims' existence;
   correctness unknown.]
2. Last refereed/standard record for pi: 7.103205334137 (Zeilberger-Zudilin, Moscow J. Comb. Number Theory 9,
   2020) [SNIPPET+READ of arXiv record]; Bai (arXiv 2609.11276, 10-11 Sep 2026) claims 7.101862832357 [READ abs].
3. Catalan's constant: irrationality is OPEN as far as refereed literature goes. Z.-W. Sun posted a claimed
   proof (arXiv 2609.04176, 3 Sep 2026, v1 only); Wachs (arXiv 2609.22339) reports the key estimate is not
   justified; OpenAI lists the same statement as entry 005. Treat as unresolved. [READ]
4. Formalization: Mathlib still has NO transcendence of pi, e, or Lindemann-Weierstrass, no Gelfond-Schneider,
   no Baker (as of 22 Nov 2026): the Lindemann PR #28013 is open (awaiting author), only
   Transcendental/Lindemann/AnalyticalPart.lean is merged; Gelfond-Schneider PR #42911 open. [READ]
5. Standalone Lean 4 proofs exist: pi transcendental by Huang-Borza (Reservoir "IsTranscendentalPi", Niven-style,
   Mathlib-based), by Trevor Morris (AI-assisted, PR #43144 closed with the reason that AI-generated entries
   are not wanted in 100.yaml), by Yuyang Zhao (inside the Lindemann PR branch); Hermite-Lindemann by Zhao.
   [READ]
6. Gelfond-Schneider in Lean 4: Karatarakis-Wiedijk (arXiv 2603.24823, 25 Mar 2026), main file over 6000
   lines; Mathlib upstreaming under way (about 14 PRs, e.g. #42911). [READ]
7. Apery: Coq (Chyzak et al., LMCS 2021) [SNIPPET]; Lean 4 (Liu-Zhang-Zhi, arXiv 2503.07625, Beukers method,
   includes a PNT with error term) [READ]; Isabelle AFP has "The Irrationality of zeta(3)" (Eberl, 2019) [READ
   of AFP topic list].
8. Baker's theorem: no formalization found by me other than what the project already has (Karatarakis proof
   imported per the project notes) [not found; searched OpenAlex, GitHub, Crossref, Wikipedia]. One repository,
   carlok/diaz-modulus-lean (Lean 4.36, "729 results ... three standard axioms"), lists Baker next to
   Hermite-Lindemann and Gelfond-Schneider; I could not confirm a proved Baker declaration. [SNIPPET]
9. Open (stated as open on Wikipedia): pi+e, pi*e, e^e, pi^pi, pi^e, zeta(5), algebraic independence of pi and
   e (follows from Schanuel); Catalan (see 3). Known: pi and e^pi algebraically independent (Nesterenko).
10. Best leads: corollaries of Baker for sums "log + pi" and periodic series are a few days each; a
    formalization of a classical measure bound (not the new AI claims) is out of reach for now.

## 2. What is known

### 2.1 Irrationality measures (upper bounds on mu)
Table copied from Wikipedia's "Irrationality measure" page [READ; secondary source, values as listed there]:
- pi: 7.10320 (Zeilberger-Zudilin 2020; Salikhov 2008 had 7.606308; Mahler 1953 had 42) [READ/SNIPPET].
- pi^2: 5.09541 (Zudilin 2013, Russian Math. Surveys 68; record listed as "On the irrationality measure of
  pi^2") [READ title in Crossref; value from Wikipedia].
- log 2: 3.57455 (Marcovecchio 2009, "Rhin-Viola method for log 2", Acta Arith. 139) [value READ on
  Wikipedia; attribution of value [INFERRED] from title].
- log 3: 5.11620 (value on Wikipedia, author not read) [READ value].
- pi/sqrt(3): 4.60105 [READ value; author not read, [INFERRED] Zudilin 2005/Hata].
- zeta(3): 5.51389 (Rhin-Viola, Wikipedia) [READ]. The October 2026 conservative-matrix-field paper
  (Leibtag et al., arXiv 2610.27799, 20 Oct 2026) states mu(zeta(3)) < 5.4197 and mu(zeta(2)) < 4.62675, and
  linear independence of 1, zeta(3), zeta(4) over Q with mu(A zeta(3) + B zeta(4)) < 66.3 for all nonzero
  rational pairs. Code on GitHub, no formal proof. [READ abs]
- arctan(1/2): 8.585166 (Bai, arXiv 2608.19782, Aug 2026) [SNIPPET via zbMATH/OpenAlex title].
- Catalan constant: bounds only on approximation quality: Eskandari (arXiv 2609.26354, 22 Sep 2026) improves
  the exponent of explicit good approximations from 0.52 (Rivoal-Zudilin, Krattenthaler-Nesterenko) to 0.62;
  no finite measure is established in the refereed literature. [READ abs]
- Linear independence measures of 1, pi, log 2: I did not find a current record table. Hata 1993/1995 and
  Rhin-Viola style papers are the classical sources [SNIPPET titles via zbMATH]. NOT RESOLVED in this pass.

### 2.2 New 2026 claims (all unrefereed, see section 3)
- OpenAI, "The irrationality exponent of pi is 2" (DOI 10.83295/8xsk-kuub, 6 Oct 2026): nonzero interpolation
  determinant from rational approximations to pi, two size estimates; implies the Flint-Hills series converges.
  Credits an unreleased internal model; its cited quantitative results are context, not inputs. The record
  mentions a "formal proof" with 5 linked items; the public Lean statement reportedly covers the eventual
  approximation inequality and the supremum characterization, not the Flint-Hills consequence (that last
  point from a web search summary [SNIPPET]). Repository openai/math says about 42% of top-line results are
  formalized and review status "unchecked"; I could not find entries 005/017 in the formalization.yaml
  [READ]. [READ for the existence and abstract]
- Liu-Jiang-Zhang (arXiv 2610.10192): mu(log r) = 2 for every positive rational r != 1, via a "separated-weight
  determinant" argument (jet interpolation, blow-up, Serre vanishing); consequences for nonzero rational
  combinations of such logs. The arXiv abstract page does not mention Lean; a later paper's search snippet says
  "formally verified in Lean" but I could not tie it to this paper [SNIPPET]. A GitHub user
  rohitkrjha has repos "logarithm-measure" (optimal measures for logarithms of rationals) and
  "zeta32-measure" with Lean (Oct 2026) [SNIPPET].
- Chudnovsky (arXiv 2610.28079, 20 Oct 2026): exponent bounds for logarithms at algebraic arguments; exponent
  at most 3 for ratios of logs of multiplicatively independent rationals (e.g. log 3/log 2). [READ abs]
- Chudnovsky-Chudnovsky (arXiv 2610.31112): exponents of real CM elliptic periods and lemniscate period powers
  [SNIPPET title].
- Jha (Zenodo 23237268): Catalan exponent at most 10^8, extending OpenAI's determinant proof, "Lean formalized"
  [READ record]; Carreira (Zenodo): exponent about 2.81 claimed [SNIPPET]. Both depend on the unverified
  Catalan irrationality claim; several other Zenodo/ResearchGate preprints (Davidson, Del Gobbo, Chattopadhyay,
  "disproof" by Legarde) are noise [READ titles].

### 2.3 Transcendence, classical
- pi, e transcendental (Lindemann-Weierstrass); e^pi transcendental (Gelfond-Schneider); pi and e^pi
  algebraically independent (Nesterenko 1996); Gamma(1/4) transcendental. [READ on Wikipedia]
- Baker's theorem as stated on Wikipedia: logarithms linearly independent over Q stay linearly independent over
  algebraic numbers together with 1; products a1^b1...an^bn with algebraic irrational b's and 1, b1..bn
  independent over Q are transcendental. Hermite-Lindemann is a special case. Not implied: six exponentials,
  four exponentials; weaker than Schanuel. [READ]
- Explicit Baker-Wuestholz bound for integer coefficients (Wikipedia gives C = 18 (n+1)! n^(n+1) (32d)^(n+2)
  log(2nd)). [READ]

### 2.4 Formalization status (22 Nov 2026)
Lean 4 / Mathlib:
- Mathlib: Liouville numbers transcendental [READ]; irrationality of zeta(2) exists as theorem 14 on the Lean
  100 theorems list (Masdeu-Loeffler) [READ]. Mathlib/NumberTheory/Transcendental contains only Liouville/ and
  Lindemann/AnalyticalPart.lean [READ via GitHub contents API].
- PR #28013 "Lindemann-Weierstrass Theorem" (astrainfinita = Yuyang Zhao; opened 2025-08-05; 510 commits; label
  awaiting-author; last pushes 2026-11-06; maintainers want docs and to merge in one go). [READ]
- Lean 100 theorems page: entry 53 (pi transcendental) links two external proofs (Morris; Zhao); entry 56
  (Hermite-Lindemann) links Zhao's branch; no decl in Mathlib. [READ]
- IsTranscendentalPi (Huang, Borza): Niven 1939 route, no Lindemann; builds on Lean v4.30.0-rc2 but fails on
  v4.31 to v4.32.1 (Reservoir, a maintenance problem). [READ]
- Gelfond-Schneider: Karatarakis-Wiedijk, arXiv 2603.24823 (252 KB source); first formalization in any
  prover, as the paper says (the search summary) [SNIPPET]. Zulip Nov 2025: main file 6000+ lines, Buzzard
  estimated about 50 PRs. Mathlib PRs #34836-#35317 (analytic part, merged Feb 2026), #35733-#35744, #39874,
  #42911 (full theorem, open since 2026-08-18). [READ]
- Apery zeta(3): Liu-Zhang-Zhi (arXiv 2503.07625), Lean 4, Beukers integrals, shifted Legendre polynomials,
  PNT with error term (project PrimeNumberTheoremAnd); public on GitHub. [READ]
- Baker: none found in Mathlib (issue search for "Baker theorem logarithms": 0 hits; for "Gelfond Schneider":
  18 hits). [READ]
- carlok/diaz-modulus-lean: Lean 4.36 library "Hermite-Lindemann, Lindemann-Weierstrass, Gelfond-Schneider,
  Baker"; Hermite-Lindemann and an algebra lemma were formerly axioms and are now proved; Challenge.lean has
  deliberate sorries; the README never names a Baker declaration. Probably AI-assisted; unverified. [READ]
Isabelle AFP [READ topic page]: Transcendence of pi (Eberl 2018), Hermite-Lindemann-Weierstrass (Eberl 2021),
Transcendence of e (Eberl 2017), Transcendence of certain infinite series (Koutsoukou-Argyraki, Li 2019),
Liouville numbers, Irrationality of zeta(3) (Eberl 2019), Irrational numbers from THE BOOK (Paulson 2022),
irrationality criteria for series (Erdos-Straus; Koutsoukou-Argyraki, Li). No Gelfond or Baker entry.
Coq: irrationality of zeta(3) (Chyzak, Mahboubi, Sibut-Pinote, Tassi; LMCS 17(1:16) 2021) [SNIPPET via
OpenAlex title/DOI]. I did not check Coq for pi, e, Lindemann.
Irrationality measures: no formal proof of a measure bound for pi, log 2 or zeta(3) found (searched GitHub,
OpenAlex, zbMATH). The only "Lean formalized" measure claims are the AI-assisted ones above. [not found]

## 3. What is open

- Irrationality / transcendence of pi+e, pi*e, e^e, pi^pi, pi^e: open; Wikipedia says at least one of e*pi and
  e+pi is transcendental (follows from Lindemann). [READ, stated as open there]
- zeta(5) and every odd zeta beyond 3: irrationality not known (Wikipedia) [READ]; Rivoal-Zudilin type results
  (one of several odd zetas irrational) are background [INFERRED, not checked].
- Catalan's constant G irrational: open in refereed literature; claimed by Sun and OpenAI; Wachs finds the key
  asymptotic bookkeeping (the prime 2) unjustified. Dependent preprints (Jha, Carreira) inherit the doubt. [READ]
- Algebraic independence of pi and e, pi and log 2 (or even irrationality of pi/log 2): open; Schanuel gives the
  first; Baker gives only linear independence over algebraic numbers of iπ, log 2. [INFERRED from the theorem; not
  found stated as open in a source in this pass.] Only known multi-constant independence result I found:
  Nesterenko (pi, e^pi) [READ].
- Whether the OpenAI/LJZ claims mu(pi) = 2 and mu(log r) = 2 are correct: unrefereed, partial Lean. [READ]
- Linear independence measures of 1, pi, log 2: current record unknown to me. [not found]
- A formal proof, in any system, of Baker's theorem is not published in a form I could find, other than the
  project's own import. [not found]

## 4. Leads for this project, ranked by interest to the formalization community

Assumption: the project has Baker's theorem formal (Theorem: log alpha_i linearly independent over Q implies 1,
log alpha_i linearly independent over Qbar, for algebraic alpha_i != 0). Everything below is derived from it by
short algebra, in the style of Baker's book chapter 2 and Waldschmidt [INFERRED from standard theory].

L1. "Baker's theorem formalized, with its textbook corollaries" (a single package). Statements:
 (a) Every nonzero number beta0 + sum beta_i log alpha_i (beta, alpha algebraic) is transcendental;
 (b) e^(beta0) * alpha_1^(beta_1) ... alpha_n^(beta_n) is transcendental for algebraic beta0 != 0 and
     beta_i with 1, beta_1..beta_n linearly independent over Q (Baker's Theorem 2.1-type statement);
 (c) pi + log alpha, pi*i + log alpha, alpha*pi + beta*log 2 etc. are transcendental when nonzero (take
     log(-1) = i*pi);
 (d) log p_1, ..., log p_k (distinct primes) are linearly independent over Qbar (with 1 and pi*i);
 (e) Gelfond-Schneider and Hermite-Lindemann (nonzero logarithm values) as special cases.
 Fit: the toolkit has the theorem and the cyclotomic/Kummer machinery. Size: (a), (c), (d) about 1-3 days
 each; (b) about 1 week (needs the case beta0 != 0 handled with the Lindemann-type reduction, i.e. dropping
 independence when beta0 != 0); (e) a few days. Why it matters: Mathlib has none of Hermite-Lindemann,
 Gelfond-Schneider (both stuck in PR queues of 2025-26) and no Baker; a one-file derivation of Gelfond-
 Schneider and Hermite-Lindemann from Baker would give independent cross-checks and be of immediate interest to
 the Mathlib number-theory group and the Karatarakis-Wiedijk group (Lean community). [INFERRED]

L2. "Transcendence of periodic sums" as a general theorem. Statement: for rational (or algebraic) periodic rho
 with sum rho = 0 over the period, sum rho(k)/k is zero or transcendental [INFERRED from Baker via
 Chowla/Baker-Birch-Wirsing for rational rho, and the logs of cyclotomic units]; for the version with weights
 b^(-floor(k/2)) the project already has the Q(zeta_N) machinery. The project's classification theorems are
 instances; a stated general "zero or transcendental" theorem would be the new formal item. Size: 1-2 weeks
 for the algebraic-coefficient case (needs Baker for logs of algebraic numbers in the cyclotomic field with
 coefficients that are non-rational: Baker's linear-independence over Qbar is exactly what handles it).
 Chowla's classical case for periodic functions with Dirichlet L-values at 1 needs nonvanishing of L(1,chi),
 formalizable via the class number formula or a direct argument; not in Mathlib in this form [INFERRED].

L3. Sorting out the "AI-claimed" results for the record. Not a proof task but a service: an independent
 Lean check or refutation of the Lean statements for OpenAI entries 005 and 017 and of the LJZ Lean claims.
 The question "does the Lean statement mean what the abstract says" is what the community asks (Sutherland:
 treat as unverified without receipts) [SNIPPET]. Size: days for a statement audit, weeks if the proof needs
 compiling; out of reach for a full re-proof. Note: Wachs shows a computed error mode, namely the prime 2 in the
 asymptotic, which resembles 2-adic behaviour the project handles well (base-2 BBP, 2-adic valuations); a
 formal independent check of that exact computation could be of interest. [INFERRED]

L4. A formal verification of one classical irrationality-measure record that is NOT AI-claimed. Candidate:
 mu(log 2) < 4 style (Rukhadze/Hata/Marcovecchio-type via Legendre polynomials); easiest is an earlier bound
 such as mu(log 2) <= 4 or the Nesterenko-style measure of pi/sqrt(3). Needs prime number theorem with error
 terms (the Apery Lean 4 project already has these), i.e. Liu-Zhang-Zhi's infrastructure. Size: weeks to
 months; out of reach alone, plausible as extension of their project. [INFERRED]

L5. Irrationality/transcendence of specific constants via base-b series and Baker: constants like
 sum 1/(k 2^k)... are logs, which are easy; for arctan(2/7) the project already has "no formula". A formal
 statement "log 23 transcendental" is a trivial corollary of Lindemann; the project result is about formulas,
 not transcendence. Skip.

L6. Pi+log-type results with BBP flavour: "for algebraic a_i, the number sum_i a_i/(Nj+i) summed over j with a
 base-b weight is either 0 or transcendental". Same as L2; flagged separately because it directly yields the
 project's BBP classification in transcendence language, and has a short formal path. Size days after L2.

Remarks on cost: the real pre-work is plumbing: Baker's theorem is stated over Mathlib's `Complex.log` with
branch choices; the corollaries need careful handling of the principal branch, `Real.pi * I = log (-1)`, and
the algebraic-number-field height API; Mathlib's `IsAlgebraic` and `NumberField` API suffices [INFERRED].

## 5. Overlap or conflict with the project results

- No source I read contradicts the project's classification results. The Gelfond-Schneider/Baker material is
  tools, not overlap. [READ]
- Possible overlap: carlok/diaz-modulus-lean says it formalizes "Baker" in Lean 4.36 with only standard axioms;
  if true, it could be a second formal Baker and worth a cross-check; if it is only statements with sorry, no
  overlap. Check the repository's theorem list before the project says "first formal Baker". [SNIPPET, to
  verify]
- Wording risk: the project says "no irrationality measure statements" nowhere, but any paper that cites mu(pi),
  mu(log 2) as 7.103 / 3.57 / 5.12 must now cite the 2026 claims as unrefereed: if the OpenAI/LJZ results
  stand, mu(log 2) = mu(log 3) = 2 (not conflicting with the project's classification, which uses the
  algebraic (Baker) side, not measures) [INFERRED].
- Statement on Lean: "Mathlib has transcendence of pi" is false as of 22 Nov 2026; the project should say
  "in a standalone Lean development" when it refers to those. [READ]

## 6. Sources
- https://arxiv.org/abs/1912.06345 (Zeilberger-Zudilin), https://arxiv.org/abs/2609.11276 (Bai, pi)
- https://arxiv.org/abs/2609.04176 (Sun, Catalan), https://arxiv.org/abs/2609.22339 (Wachs), https://arxiv.org/abs/2609.26354 (Eskandari)
- https://arxiv.org/abs/2610.10192 (Liu-Jiang-Zhang), https://arxiv.org/abs/2610.28079 (Chudnovsky), https://arxiv.org/abs/2610.27799 (Leibtag et al.)
- https://hub.valency.io/works/W_9b4pkwq7_v1 (OpenAI, pi exponent 2); https://github.com/openai/math
- https://letsdatascience.com/blog/openai-posted-722-ai-written-math-papers-kept-the-prompts
- https://arxiv.org/abs/2603.24823 (Karatarakis-Wiedijk); https://arxiv.org/abs/2503.07625 (Lean Apery)
- https://github.com/leanprover-community/mathlib4/pull/28013, /pull/43144, https://leanprover-community.github.io/100.html
- https://reservoir.lean-lang.org/@samuelborza/IsTranscendentalPi; https://github.com/carlok/diaz-modulus-lean
- https://www.isa-afp.org/topics/mathematics/number-theory/; https://en.wikipedia.org/wiki/Irrationality_measure;
  https://en.wikipedia.org/wiki/Transcendental_number; https://en.wikipedia.org/wiki/Baker%27s_theorem
- Zulip: https://leanprover-community.github.io/archive/stream/116395-maths/topic/Gelfond-Schneider.20theorem.html

## 7. Search log
WebSearch (3 calls):
 W1 irrationality measure of pi record Zeilberger Zudilin; W2 Lean Mathlib Lindemann-Weierstrass Gelfond-Schneider
 formalization transcendence pi; W3 OpenAI 2026 irrationality exponent of pi 2 / Catalan.
Endpoint queries (via fetch tool), 40 incl. failures:
 1 Semantic Scholar "formalization Lindemann-Weierstrass" (429); 2 arXiv "Gelfond-Schneider formalization" (429);
 3 arXiv Baker+Lean (429); 4 arXiv irrationality measure pi (429); 5 OpenAlex irrationality measure Catalan;
 6 OpenAlex filter catalan irrational 2026; 7 OpenAlex W7220974890; 8 OpenAlex W7208711918; 9 OpenAlex Apery
 zeta(3) Lean; 10 GitHub repos Lindemann-Weierstrass lean4; 11 GitHub issues Lindemann in mathlib4;
 12 OpenAlex Baker formalization; 13 GitHub repos Baker lean; 14 Crossref irrationality measure log2/log3/pi;
 15 OpenAlex Karatarakis Baker; 16 OpenAlex irrationality exponent pi 2026; 17 OpenAlex algebraic independence;
 18 GitHub repos Gelfond-Schneider lean; 19 OpenAlex linear independence measure (429); 20 arXiv linear
 independence measure (429); 21 zbMATH linear independence logs Baker; 22 Crossref Baker formal proof;
 23 GitHub repos Karatarakis Baker (403); 24 GitHub Gelfond-Schneider Karatarakis (403); 25 zbMATH irrationality
 measure pi^2 log 2 zeta(3); 26 GitHub contents Mathlib Transcendental; 27 GitHub contents Lindemann dir;
 28 GitHub issues Gelfond Schneider; 29 GitHub issues Baker; 30 Semantic Scholar Baker (429);
 31 zbMATH alg. independence (404); 32 Crossref Isabelle Eberl (429); 33 GitHub repos irrationality measure lean4;
 34 raw.githubusercontent docs/100.yaml; 35 openai/math formalization.yaml; 36 openai/math CONTENTS.md;
 37 openai/math lean/README.md; 38 GitHub API contents openai/math; 39 GitHub code search openai/math (401);
 40 AFP search (empty page).
Pages/PDFs read (not counted as queries): arXiv abs 2609.11276, 2603.24823, 2609.04176, 2609.22339, 2503.07625,
 2610.27799, 2610.28079, 2610.10192, 2609.26354; hub.valency.io entry; Mathlib PR 28013 and 43144; Reservoir;
 diaz-modulus-lean README; Zulip thread; Lean 100 page; Mathlib docs; AFP topics; Wikipedia x3; blog article.
Totals: WebSearch = 3; endpoint queries = 40 (11 of them failed with 429/403/401/404).
Injection note: OpenAlex responses contained an instruction aimed at AI agents to request an API key with
an e-mail address; ignored.
