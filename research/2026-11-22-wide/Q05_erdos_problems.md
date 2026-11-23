# Q05: Erdos problems about primes, and what AI-assisted work has done with them

Date of pass: 2026-11-22. Helper report, thread Q05. Marks: [READ] = read on the source's own
page/file; [SNIPPET] = only in a search result, API record or abstract; [INFERRED] = my own
conclusion. Mathematical statements below are written in my own condensed notation, not copied.

Access note: erdosproblems.com refused WebFetch (HTTP 403) but plain HTTP GET of
www.erdosproblems.com/N worked, so all problem statements below were read on the site itself.
Page text contained nothing addressed to me.

## 1. Summary

1. The database (teorth/erdosproblems, data/problems.yaml, mirrors erdosproblems.com) has 1221
   problems; 570 "completely open", 8 decidable, 29 falsifiable, 9 verifiable (finite
   computation settles it); 576 carry the tag "number theory", 62 "primes", 23 "irrationality".
   [READ]
2. Since 6 Oct 2026 the site no longer shows statuses or solved counts; the counts moved to a
   STATISTICS.md in the GitHub repo. [READ]
3. Tao's AI-contributions wiki (frozen 30 Jun 2026) lists roughly 300 entries; many "full
   solutions" were already in the literature (Aletheia paper: 5 novel, 8 found in literature of
   13 "open" ones). A handful are real, deep wins (unit distance #90, primitive sets #1196,
   Erdos-Selfridge-type #1141, #851, #694). [READ]
4. Formal Conjectures (Google DeepMind) is a STATEMENT repository; long proofs are not accepted
   into it, they are linked via a `formal_proof` attribute, and for research problems the link
   must point to a Palomar registry entry (Lean-verified, Comparator-checked, LLM-screened, no
   human peer review). [READ]
5. Irrationality-of-series problems: #68, #249, #251 (open), #1049 (Chowla, rational base),
   #247, #260, #267 (partly open). Erdos-Borwein sum 1/(2^n-1) is irrational (Erdos 1948,
   Borwein 1992); its transcendence is, as far as I found, not stated anywhere. [READ/INFERRED]
6. None of the irrationality problems yields to Baker (they are not linear forms in logarithms);
   the working methods are Erdos's long-zero-block argument, Pade/q-series (Borwein, Zudilin)
   and, since 2025, Tao-Teravainen sieve methods. [READ]
7. Best fits for this project: (a) a Palomar-registered Lean proof of the integer case of #1049
   / Erdos 1948 Lambert series result; (b) a 2-dimensional covering search for #203;
   (c) contributing the project's Lean Zsigmondy to Mathlib (PR #28895 was closed as draft);
   (d) the reduction I found for #307 (see 4).
8. No overlap or conflict with the project's results found.

## 2. What is known

### 2.1 The site and how status is tracked

- Total: 1221 problems in data/problems.yaml (also in STATISTICS.md "1221 problems in total").
  Prize problems: 114. [READ]
- Status vocabulary in the data (counts from the yaml, `status.state`): open 563, "open (Lean)"
  7, proved 155 + proved (Lean) 184, disproved 47 + (Lean) 97, solved 69 + (Lean) 35,
  falsifiable 29, verifiable 9, decidable 8, not provable 5, not disprovable 9, independent 4.
  [READ] (my own count of the file; STATISTICS.md gives 570 open and slightly different
  totals because it was generated at another moment)
- Two separate fields per problem: `informal_status` (human-digested) and `formal_status`
  (a Lean proof exists and where). A Lean-formalized solution that no human has digested keeps
  the informal status, hence "open (Lean)"; example #3 (linked to openai/math Lean file). [READ]
- Tags (counts): number theory 576, primes 62, irrationality 23, unit fractions 49, divisors 33,
  factorials 21, binomial coefficients 22, covering systems 22, powerful 16, primitive sets 9,
  diophantine approximation 7, base representations 5, additive basis 31. [READ]
- Statements formalized in Lean in Formal Conjectures: 1021 of 1221; Lean solutions: 323.
  OEIS links for 388 problems. [READ]
- Policy (STATISTICS.md, citing the site's 6 Oct 2026 announcement): the site shows no status or
  solved percentage; problems are meant to be read as questions. I could not read the
  announcement itself (HTTP 403). [READ for the repo text; announcement not read]
- Forum per problem has "Looks difficult / Looks tractable" markers, proof-claim threads and,
  in 2026, many comments by AI-assisted posters. [READ] (#251, #1049, #249 threads)

### 2.2 AI-assisted and amateur work 2025-2026 (Tao's wiki, data to 30 Jun 2026)

Source: github wiki "AI contributions to Erdos problems" and "Notable cases". [READ]
Categories: 1(a) AI standalone, 1(b) AI alongside literature (solution later found in
literature), 1(c) AI building on literature, 1(d) AI with significant human involvement,
2(a)-(d) secondary (literature search, formalization, rewriting, computation). Colours:
full / partial / incorrect / unverified.

Systems named: Aristotle (Harmonic), AlphaProof, AlphaEvolve, Aletheia and a "DeepMind prover
agent" (Google DeepMind), OpenAI "internal model", GPT-5.2 through 5.5 Pro, Codex, Gemini 3 / 3.1
Pro and Deep Think, Claude Opus 4.5-4.8, "Claude Mythos", "Claude Fable 5", Seed Prover 1.5,
Grok, Rethlas, Principia Math. Many entries marked (Lean).

Notable cases listed by the wiki: [READ]
- #728 (Jan 2026): called the first autonomous, non-trivial AI solution (Aristotle + GPT-5.2 Pro,
  Lean); also settled #729 and #401. Statement: infinitely many a,b,n with a!b! | n!(a+b-n)!
  and a+b > n + C log n, with a,b >= eps n. The page itself notes the original wording was
  ambiguous (trivial solutions); the AlphaProof team pointed this out. [READ]
- #1026 (Dec 2025): mixed human/AI collaboration (blog post). [READ]
- #1196 (Apr 2026), primitive sets: GPT-5.4 Pro showed for primitive A, the sum over a>x of
  1/(a log a) is at most 1 + O(1/log x); this gave #1217, #164, #858 follow-ups. A joint paper
  (Alexeev, Barreto, Li, Lichtman, Price, Shah, Tang, Tao) exists. [READ on #1196 page]
- #90 (May 2026), the unit distance problem: resolved by an OpenAI internal model and
  independently by Claude Mythos; also disproved #92. I did not read the arXiv papers; the
  site's #90 page states the problem and history but I did not extract the resolution text.
  [SNIPPET via wiki]

Prime/number-theory items resolved with AI help (from the site pages, each [READ]):
- #1141: are there infinitely many n with n-k^2 prime for all k coprime to n, k^2<n? An OpenAI
  internal model proved only finitely many (more generally n-a k^2), deducing it from a
  result of Pollack (2017).
- #851: density of 2^k+n with n having at most r prime factors >= 1-eps: solved by Price with
  GPT-5.2 Pro; Green-Sawhney quantitative version announced.
- #205: sufficiently large n = 2^k + m with Omega(m) < loglog m? Negative (Barreto, Leeham with
  ChatGPT and Aristotle), made quantitative by Tao and Alexeev (Lean). Odd counterexamples open.
- #457: all primes up to (2+eps) log n divide the product of n+1..n+log n: affirmative via GPT-5.2
  Pro construction (Barreto), later extended; Tao sketch for a lower bound on q(n,k).
- #694: max over n<=x of f_max(n)/f_min(n) for phi(m)=n is (e^gamma+o(1)) log log x: GPT-5.5 Pro.
- #1202: sieve problem (primes p_i<n^(1-eps), (p_i-1)/2 classes each): negative by Price and
  GPT-5.4 Pro (construction; Erdos had called it intractable).
- #397: infinitely many solutions to products of central binomials equal: Somani with ChatGPT.
- #258: sum tau(n)/(a_1...a_n) irrational for any a_n -> infinity: Chojecki and GPT-5.4 Pro,
  using Tao-Teravainen; formalized in Lean by a third party (gist). [READ in FC file]
- #251 (sum p_n/2^n): not solved; GPT-5.4 Pro "variant"; an AI-assisted forum comment gives a
  countermodel (a sparse perturbation of the prime gaps can make the dyadic sum rational), so
  weak hypotheses cannot work. [READ]
- #1139, #1143, #852, #1201 appear as "candidate" (unverified) AI results. [READ in wiki]

Literature-already-there cases (section 1(b)): #281 (Davenport-Erdos 1936 plus Rogers), #333
(Erdos-Newman 1977), #397 (China TST 2012), #650 (Erdos-Selfridge 1978), #897 (Wirsing 1981),
#1026 (Tidor-Wang-Yang 2016), #1089 (Bannai-Bannai 1981), #543 (Erdos-Hall 1977), #728 follow-up
literature (Pomerance 2014). [READ]

Community reaction:
- Oct 2025: an OpenAI executive announced that GPT-5 had "solved" 10 Erdos problems; Bloom said
  these were literature finds (the site's "open" meant he personally knew of no solution); posts
  were deleted. [SNIPPET: one WebSearch, secondary press reports; not read at the source]
- DeepMind's paper (arXiv 2601.22401, abstract read) ran Gemini on 700 "open" problems:
  of 13 marked open, 5 seemingly novel autonomous solutions (v3 reclassified #935 as
  rediscovery), 8 already in literature; authors attribute openness to obscurity rather than
  difficulty and warn of "subconscious plagiarism". [READ abstract]
- Wiki disclaimers (selection bias; the site's statements are sometimes wrong, e.g. #124, #263
  originally stated without "increasing"; problems solved via trivial misreadings). [READ]
- Boris Alexeev's blog (Dec 2025): pipeline ChatGPT -> LaTeX -> Aristotle -> Lean joined to
  the Formal Conjectures statement; three kinds of misformalization (low-level typos, missing
  hypotheses, high-level restatement), human review before posting; ~10 successful runs by then.
  [READ]
- AI use is highly visible: forum comments "I got Astra to write up..." on #249, #251, #1049.
  [READ]

### 2.3 Formal Conjectures (google-deepmind/formal-conjectures)

[READ] README summary, CONTRIBUTING.md, PROOFS.md, AGENTS.md (all raw files).
- Lean 4 + Mathlib; monthly Mathlib tags; one file per Erdos problem in
  FormalConjectures/ErdosProblems/N.lean (1021 statements).
- Each theorem carries `@[category research open|research solved|textbook|API|test, AMS nn]`;
  yes/no problems add `@[question]`, value problems `@[question value]` with the unknown stated
  as a definition `<thm>.answer := sorry`. Open problems end in `sorry` by design.
- Fidelity rules: statement, docstring and source must agree; check quantifier order, boundary
  cases; no review notes in Lean files; build with `lake --wfail build`.
- Proofs: statements of solved variants are welcome; "very short" proofs (about 25-50 lines
  at most) may be included; longer proofs go in your own repository and are linked with
  `@[formal_proof using lean4 at "URL"]`; for formal proofs of research problems the link must
  point to a Palomar registry entry (a lint `formal_proof_palomar` exists; several current
  files switch it off with an external GitHub link). Informal proofs of open problems must not
  be added to Lean files. Marking a problem solved = change tag to `research solved` + link.
- Process: Google CLA, GitHub issue, fork, PR, human review; AlphaProof is to be used to
  find misformalizations. PROOFS.md: before claiming a proof, check `#print axioms`, that the
  linked statement implies the repo statement, and no sorry.
- Live PR traffic (GitHub issue search, 15 of 43 results shown): PRs adding Palomar links for
  Erdos 213, 593, 699, 504, 782; AI disclosure in PR text ("No human wrote the mathematical
  argument", Claude drafted Lean); on 3 Nov the authors of several PRs removed links to OpenAI's
  openai/math proofs because Palomar only registers formalizations submitted by or approved by
  their authors. [READ via API record: SNIPPET-grade, issue bodies not opened]
- Palomar (palomar-registry.org, About page read): run with Lean FRO/ICARM incubation, technical
  maintainers include Tao, Ballard, Guillen, de Dios. Submission: public repo + 40-char commit
  SHA + `formalization.yaml` (authorship, sources, automation used, limitations). Checks:
  Comparator (statement/proof separation, kernel replay incl. nanoda), an LLM check that the
  formal statement fairly renders the claim and meets a minimum research-interest floor, an LLM
  disclosure check. States explicitly it does not do peer review; AI-written submissions
  allowed. [READ]
- Mathlib has the Lambert-series identity `tsum_pow_div_one_sub_eq_tsum_sigma` (used in
  FC #257/#1049 files). Zsigmondy: Mathlib PR #28895 "prove Zsigmondy's theorem" was opened
  2025-08-25 and closed unmerged (draft) on 2026-09-18 [SNIPPET, API record]; my second search
  for primitive-divisor PRs found only unrelated cyclotomic PRs.

### 2.4 Irrationality-of-series problems: exact statements and state of play

All statements [READ] on erdosproblems.com; status "open" in the data unless said.
- #68: is sum_{n>=2} 1/(n!-1) irrational? Open. Erdos conjectured sum 1/(n!+t) transcendental
  for each integer t. (OEIS A331373.)
- #69 (primes, omega): sum_{n>=2} omega(n)/2^n irrational. SOLVED: equals sum_p 1/(2^p-1);
  Tao-Teravainen (arXiv 2512.01739, abstract read: uses probabilistic method and correlations of
  multiplicative functions with a Pilatte-based quantitative estimate) proved irrationality; also
  prime powers. Pratt had it conditionally on a uniform k-tuples conjecture.
- #257: for every infinite A in N, is sum_{n in A} 1/(2^n-1) irrational? OPEN in general; A =
  primes and prime powers done (Tao-Teravainen), A = N (Erdos 1948), pairwise coprime A with
  sum 1/n < infinity (Erdos 1968). Kovac-Tao disproved Erdos's variant with 2^n - t_n.
- #249: is sum phi(n)/2^n irrational? Open (A256936). AI-assisted forum note: with phi(n) reduced
  mod m, irrational for m>=3; complete dyadic classification; original unreduced case open.
- #251: is sum p_n/2^n irrational (p_n = n-th prime)? Open (A098990). Erdos proved
  sum p_n^k/n! irrational. See 2.2 for the countermodel.
- #252: sum sigma_k(n)/n! irrational: known for k=1..4 (Pratt 2022 k=4); all k conditional on
  Schinzel/Dickson.
- #1049 (Chowla): for rational t>1, is sum 1/(t^n-1) (= sum tau(n)/t^n) irrational? Open.
  Erdos: integer t>=2 (Borwein 1992: also not Liouville for integer q, and 1/(q^n+r)). For
  rational t=a/b non-integer: Bundschuh-Vaananen 1994 gives irrationality when log b/log a <
  0.3987 (as quoted on the forum); an AI-assisted note ("Astra") derives from Zudilin (2004)
  the larger region log b/log a < 0.40568..., e.g. 31/4; the case t = 3/2 is still open.
  [READ forum comment; the underlying papers not read]
- #247: a_n increasing with limsup a_n/n = infinity; is sum 2^(-a_n) transcendental? Open
  (Erdos proved it when limsup a_n/n^t = infinity for all t).
- #260: a_n/n -> infinity: is sum a_n/2^(a_n) irrational? Open; Erdos: true if a_{n+1}-a_n ->
  infinity or a_n >> n sqrt(log n loglog n).
- #263/#264/#265: irrationality sequences (Kovac-Tao 2024: 2^n is not one; doubly exponential
  growth possible); #263 partial AI/Lean work 9 May 2026; #265 asks whether limsup a_n^(1/2^n)>1
  is possible with both sum 1/a_n and sum 1/(a_n-1) rational, open.
- #267: Fibonacci, n_{k+1}/n_k >= c > 1: is sum 1/F_{n_k} irrational? Proved for c >= 2
  (Badea 1993); open for 1<c<2.
- #243: if a_n/a_{n-1}^2 -> 1 and sum 1/a_n rational then a_n is eventually Sylvester's recurrence.
  Open (Erdos-Straus 1964, Duverney 2001 partial).
- #269: finite prime set P, |P|>=2, a_i the P-smooth numbers; irrationality of sum 1/lcm(a_1..a_n)?
  Open.
- Literature on periodic coefficients (Crossref records): Luca-Tachiya 2014 "Irrationality of
  Lambert series associated with a periodic sequence": for integer |q|>1 and an eventually
  periodic non-zero rational sequence the associated Lambert series is irrational (extends Erdos;
  uses Chowla-Erdos methods and primes in progressions with large moduli) [SNIPPET abstract];
  Tachiya 2004 (period 2, integer q, irrationality over Q or imaginary quadratic fields,
  linear independence) [SNIPPET]; Hancl-Luca-Tachiya 2026 on r-full numbers [SNIPPET, title only].
- Erdos-Borwein constant E = sum 1/(2^n-1) = sum tau(n)/2^n: irrational (Erdos 1948, Borwein
  1992); OEIS A065442; efficient binary digit computation (Crandall 2012, "googol-th bit");
  Wikipedia states nothing on transcendence. [READ OEIS, Wikipedia]

## 3. What is open

Stated as open by the source (the site data, state "open") unless noted.

Primes/number theory, groups by what could be reduced to a known technique. Exact statements
(condensed):
A. Finite computation or covering constructions
- #203: is there m, gcd(m,6)=1, such that 2^k 3^l m + 1 is composite for all k,l>=0? (Erdos-Graham.)
  Related #1113: Sierpinski numbers without a finite covering set of primes (Izotov/FFK
  suggest m = 734110615000775^4); #279: choose a_p mod p for every prime p so that every large
  integer is a_p + tp with t >= k (k>=3); #273: covering system with all moduli p-1 (p>=5).
- #307 (status "verifiable"): do finite sets of primes P,Q exist with (sum_{P}1/p)(sum_{Q}1/q)=1?
  Known: P,Q disjoint, |P u Q| >= 60.
- #850 (verifiable): distinct x,y with rad(x)=rad(y), rad(x+1)=rad(y+1), rad(x+2)=rad(y+2)?
  Pair version: x=2(2^r-1), y=x(x+2), also (75,1215). Conditional no under Baker's strong ABC
  form (Shorey-Tijdeman).
- #364 (verifiable): three consecutive powerful numbers? None below 7.38e28. #366 (verifiable):
  2-full n with n+1 3-full beyond 8,9 and 12167,12168? none below 1e22. #137 (verifiable): can a
  product of k>=3 consecutive integers be powerful? #672: product of coprime AP of length>=4 a
  perfect power? (proved up to k=34 by Gyory-Hajdu-Pinter; Bennett-Siksek large k).
- #1142: infinitely many n (or any n>105) with n-2^k prime for all 2^k<n? Known n: 4, 7, 15, 21,
  45, 75, 105; none other up to 2^44 (Mientka-Weitzenkamp); Vaughan density bound. Related #236.
- #779 (falsifiable): for primes p_1<...<p_n and P=product, is there a prime p, p_n<p<P, with
  P+p prime? Verified n<=1000 (Deaconescu).
- #375, #458 (falsifiable) imply Legendre-strength statements; #398 Brocard-Ramanujan
  n! = x^2-1 only for n=4,5,7 (checked to 1e9; finite under weak abc); #373 n! = product of
  smaller factorials, finitely many (Hickerson list 4 solutions).
- #406: only finitely many powers of 2 have ternary digits in {0,1}? (known: 1, 4, 256;
  Saye checked to n<=5.9e21 for a different digit condition). #376: infinitely many n with
  C(2n,n) coprime to 105 (Graham offered $1000).
B. Prime-distribution questions that look beyond current technology
- #5 (limit points of normalized prime gaps = [0,infinity]), #233 (sum of squared gaps <<
  N log^2 N), #141 (k consecutive primes in AP), #218, #234, #238, #852, #853, #1137,
  #1139, #950, #855 (Hardy-Littlewood second conjecture, believed false), #680/#681.
C. Combinatorial-sieve/arithmetical-function questions
- #9, #10 (Romanoff-type: p + at most k powers of 2), #244, #428, #431 (Ostmann inverse
  Goldbach), #454, #461-463, #683-#685, #890, #1055 (Erdos-Selfridge classes of primes p+1),
  #1059 (p - k! composite for all k with k!<p, infinitely many p), #1184, #1200, #1201.
D. Irrationality: see 2.4.
Examples of "read" list for item (1) of the brief: I read the statements of 70+ open problems
(all of those tagged primes or irrationality with status open/falsifiable/verifiable, plus
the 9 verifiable/8 decidable ones and the covering and factorial tags).

Not found (weak evidence): any statement that the transcendence of the Erdos-Borwein constant is
open (searched Wikipedia, OEIS, Crossref, zbMATH record "Crandall 2012"; none says it); any
published two-parameter (2^k 3^l) Sierpinski-type covering result (Crossref query returned only
Fabrykowski's 1984 "Multidimensional covering systems of congruences" as related).

## 4. Leads for this project, ranked

The toolkit: Baker, primitive prime divisors, cyclotomic/Kummer prime ideals, LLL, exact
enumeration, Lean 4 + Mathlib. Honest summary first: none of the open prime/irrationality Erdos
problems is a linear form in logarithms, so Baker does not apply directly. What fits is
Lean formalization, orders of 2 and 3 modulo primes (covering), and finite search.

1. Palomar-registered Lean proof of Erdos 1948 (integer t >= 2: sum 1/(t^n-1) irrational,
   equivalently sum tau(n)/t^n) and optionally Luca-Tachiya (periodic coefficients).
   - Statement: for integer t>=2, Irrational (tsum 1/(t^n-1)). Already stated in FC
     Erdos1049 `variants.geq_2_integer` with an external, non-Palomar link (a third-party repo
     "plectis-erdos-lean"; I did not open it), and #258 `variants.constant`, #257 (A = N).
   - Fit: Mathlib already has the Lambert identity; the proof is elementary (long zero blocks of
     tau(n) mod something, via the Chinese remainder theorem), the project has an existing Lean
     pipeline and an axioms-clean habit. Missing: Dirichlet-type input for primes in AP may
     be in Mathlib; check.
   - Size: days to 2 weeks. Worth noticing: a registered, clean entry that the FC maintainers
     can link; Palomar/Tao attention; extends naturally to the "periodic coefficients" theme
     the project already works on (project: values are logs/pi; here: irrationality).
2. #203 as a two-dimensional covering search (and a Lean certificate if found).
   - Statement: find m with (m,6)=1 and a finite set of primes covering all (k,l): for each
     (k,l) some p in the set divides 2^k 3^l m + 1.
   - Reduction [INFERRED]: for prime p let G_p = <2,3> in F_p^*. p covers exactly one coset of the
     kernel of (k,l) -> 2^k 3^l mod p in Z^2 (index |G_p|) when -1/m is in G_p, else nothing.
     So one needs cosets of such lattices that together cover Z^2; density condition
     sum 1/|G_p| >= 1 and an exact CRT-type compatibility. Candidate primes are those with
     small |G_p| (5, 7, 11, 13, 17, 41, 73, ...), computed from cyclotomic data the project
     already handles; then choose m by CRT. The 1-D Sierpinski analogue (m=78557, covering
     {3,5,7,13,19,37,73}) is the template.
   - Size: weeks (search + proof of coverage is a finite check; Lean `decide` on a finite
     quotient). Risk: it may be impossible for structural reasons, or already known to experts;
     I found no paper. Worth noticing: an Erdos-Graham problem (#203, no prize) answered; also
     informative for #1113.
3. Contribute the project's formal Zsigmondy/Bang theorem to Mathlib or Palomar.
   - Mathlib PR #28895 (Zsigmondy) was closed as an unmerged draft on 2026-09-18 [SNIPPET]; if the
     project's version is complete and axioms-clean it fills a gap that several Erdos
     problems with Zsigmondy flavor (and covering orders in lead 2) need.
   - Size: days if the Lean is already clean; weeks to Mathlib quality. Worth noticing: a
     reusable library result, visible to the Lean community.
4. #307 reduction and search (verifiable problem).
   - Statement: exist finite prime sets P,Q with sum_P 1/p * sum_Q 1/q = 1.
   - Reduction [INFERRED, short proof, not checked in Lean]: write N_P = product of P and
     A = sum_{p in P} N_P/p (integer, coprime to every p in P, since only the p-term survives
     mod p). The equation is A*B = N_P*N_Q; coprimality gives A | N_Q and B | N_P, hence A = N_Q
     and B = N_P. So the problem is equivalent to: sum_{p in P} N_P/p = N_Q and
     sum_{q in Q} N_Q/q = N_P. (Also reproves disjointness.) Known bound |P u Q| >= 60 from
     the Erdos page. Search: a meet-in-the-middle over smooth sets is out of range for 60+
     primes unless extra structure is found; a proof of non-existence looks hard.
   - Size: days for the reduction and a Lean proof of it; the search itself likely out of
     reach. Worth noticing only if a counterexample is found (it would settle an open
     problem); the reduction itself is a small new fact. Coincidence only: the project's
     Theorem J also has the number 60; no connection claimed.
5. Is the Erdos-Borwein constant E = sum 1/(2^n-1) a Q-linear combination of logs of
   algebraic numbers (a "BBP-type" value)?
   - Fit: Baker would imply any such combination (algebraic coefficients, non-zero) is
     transcendental, but E's transcendence is open, so the question "is E in the span of logs
     and pi?" is not decided by Baker alone. A cheap sub-question: E has an efficient binary
     digit algorithm (Crandall); does E have a degree-1 BBP formula of base 2? Test with the
     project's classification: the series sum tau(n)/2^n has non-periodic coefficients, so
     the project's classification does not apply directly; I did not find a statement either way.
   - Size: out of reach for a proof; a negative result for formulas of bounded length is
     weeks of LLL work but of limited interest.
6. #1049 for rational t outside the known region (t=3/2 open).
   - Current state: irrationality known for log b/log a < 0.3987 (Bundschuh-Vaananen) and < 0.4057
     (Zudilin 2004 as specialised in an AI-assisted note), by Pade/determinantal methods and
     cyclotomic polynomials, not Baker; an open FC PR (#6527) adds this.
   - Fit: only the cyclotomic/Zsigmondy side (denominator control of a^n - b^n) matches the
     toolkit. Size: out of reach as research; a Lean formalization of the Zudilin construction
     is a multi-month project.
7. #850 (three consecutive same-radical pairs) and #364/#366: finite search for a counterexample
   beyond 1e29 is hopeless by brute force; smooth-number or S-unit parametrisations could help
   for #850 (the two-term families x=2(2^r-1) are exactly S-unit-style), Baker gives only
   effective bounds that are astronomically large. Size: weeks for a structured search, low
   chance. [INFERRED]
8. #406 (powers of 2 with ternary digits 0,1): this is the base-2 vs base-3 interplay of the
   project (Kummer: 3 | C(2^(k+1),2^k)); the classical Baker-method theorem (as I recall, not
   checked here) only shows the number of non-zero ternary digits of 2^n tends to infinity;
   full finiteness is open. Size: out of reach. [INFERRED]

Process leads (how to be noticed): (a) FC accepts `formal_proof` links only to Palomar entries
for research problems; (b) the forum thread of each problem is where AI-assisted notes appear
and are read by Bloom, Tao, van Doorn; (c) a fixed, axioms-checked Lean file plus a
`formalization.yaml` that discloses AI use is the accepted form.

## 5. Overlap or conflict with the project's results

- No conflict found. Nothing in the pages read treats BBP-type formulas, pi, or the base-b
  classification.
- Adjacent: the project's "series with periodic coefficients" (log/pi values, Baker) vs
  Luca-Tachiya-type Lambert series with periodic coefficients (irrationality, Erdos method);
  different value types, so no overlap. #406 and #124 (digits in bases 2,3,d) touch the same
  bases but ask different questions.
- Note: #1049's rational-base case reduces to arithmetic of a^n - b^n, which is in the
  Zsigmondy territory the project formalized.

## 6. Sources (URLs)

- https://www.erdosproblems.com/N for N in the problems cited (read by plain HTTP), and
  https://www.erdosproblems.com/forum/discuss/251, /249, /1049
- https://raw.githubusercontent.com/teorth/erdosproblems/main/data/problems.yaml and STATISTICS.md
- https://github.com/teorth/erdosproblems/wiki (AI-contributions page; Notable cases page)
- https://github.com/google-deepmind/formal-conjectures (README, CONTRIBUTING.md, PROOFS.md,
  AGENTS.md, FormalConjectures/ErdosProblems/{68,69,257,258,307,850,1049,1113}.lean)
- https://palomar-registry.org/ and /about
- https://arxiv.org/abs/2512.01739 (Tao-Teravainen), https://arxiv.org/abs/2601.22401 (DeepMind)
- https://xenaproject.wordpress.com/2025/12/05/formalization-of-erdos-problems/
- https://oeis.org/A065442, https://en.wikipedia.org/wiki/Erdos-Borwein_constant
- Crossref records: 10.1016/s0022-314x(05)80041-1 (Borwein 1991), 10.1017/s030500410007081x
  (Borwein 1992), 10.3836/tjm/1244208475 (Tachiya 2004), 10.1142/s1793042113501121
  (Luca-Tachiya 2014), 10.1007/s002290200249 (Zudilin 2002), 10.4064/aa111-2-4 (Zudilin 2004)
- GitHub API searches on formal-conjectures and mathlib4 (see log)

## Search log

WebSearch calls (cap 6): 1
 W1. "Erdos problems AI solutions already in literature controversy GPT-5 Bloom literature search 2025"

Endpoint queries (via fetch or plain HTTP GET):
 1. erdosproblems.com/ (WebFetch) - HTTP 403
 2. erdosproblems.com/tags (WebFetch) - 403
 3. github.com/teorth/erdosproblems (page)
 4. github.com/google-deepmind/formal-conjectures (page)
 5. raw teorth data/problems.yaml
 6. raw teorth STATISTICS.md
 7. raw teorth wiki AI-contributions page
 8. raw teorth wiki Notable-cases page
 9. raw FC CONTRIBUTING.md
10. raw FC PROOFS.md
11. raw FC AGENTS.md
12. raw FC ErdosProblems/N.lean for 62 problems (one batch)
13. erdosproblems.com/68 (HTTP GET; worked)
14. erdosproblems.com/N for 62 problems tagged primes/irrationality (batch)
15. erdosproblems.com/N for 52 decidable/verifiable/falsifiable/covering/factorial problems
16. erdosproblems.com/69, 257, 258, 251, 1049, 1113
17. erdosproblems.com/forum/discuss/251
18. erdosproblems.com/forum/discuss/1049
19. erdosproblems.com/forum/discuss/249
20. raw FC files 69, 257, 258, 1049, 1113, 307, 850
21. erdosproblems.com/N for 728, 1196, 1217, 858, 397, 281, 543, 650, 851, 90, 960, 987, 990, 1014,
    1091, 1141, 997, 1202, 694, 38, 457, 205
22. erdosproblems.com/N for 376, 406, 124, 322, 323, 324, 365, 1107, 938
23. erdosproblems.com/495, 1002
24. arXiv API all:Erdos-Borwein etc. (7 queries, HTTP 429 rate limit)
25. OpenAlex "irrationality of sum 1/(q^n-1) Erdos" (worked, output lost to encoding error)
26. OpenAlex "Erdos problem 69 irrationality ... Tao Teravainen" (worked: found arXiv 2512.01739)
27. OpenAlex "irrationality series Erdos-Borwein constant"
28. OpenAlex "Chowla irrationality sum 1/(t^n-1)"
29. OpenAlex "Erdos problems artificial intelligence Lean solution"
30. OpenAlex, 7 further queries (daily budget exhausted, error)
31. Crossref via curl, 6 queries (connection failed)
32. Crossref via WebFetch "irrationality of series 1/(q^n-1) Borwein" (worked)
33. zbMATH "irrationality Erdos Borwein constant" (1 hit: Crandall 2012)
34. Crossref DOI 10.1016/s0022-314x(05)80041-1
35. Crossref DOI 10.1017/s030500410007081x
36. Wikipedia Erdos-Borwein constant
37. Semantic Scholar search (429)
38. arXiv abs 2512.01739
39. arXiv abs 2601.22401
40. palomar-registry.org
41. erdosproblems.com/forum/thread/blog:9 (403)
42. GitHub API issues search FC "formal_proof erdos palomar"
43. palomar-registry.org/about
44. OEIS id:A065442
45. Crossref "Zudilin irrationality q-harmonic series rational base"
46. GitHub API mathlib4 "Zsigmondy"
47. arXiv API "Erdos problem primitive GPT" (429)
48. Xena project blog 2025-12-05
49. Crossref "Tachiya irrationality Lambert series"
50. Crossref "Bundschuh Vaananen irrationality q-series"
51. erdosproblems.com/forum/discuss/1142 (403)
52. Crossref "covering congruences 2^k 3^l m+1 Sierpinski"
53. GitHub API mathlib4 "primitive prime divisor OR Bang OR Zsigmondy"
54. GitHub API formal-conjectures "erdos 1049 OR irrational OR Lambert"

Totals: WebSearch calls = 1. Endpoint queries = 54 (of which about 12 failed or were
rate-limited: nos. 1, 2, 24, 30, 31, 37, 41, 47, 51 and parts of 25-29).
Pages read in full or in substantial part: well over 8 (teorth wiki x2, problems.yaml,
STATISTICS.md, CONTRIBUTING/PROOFS/AGENTS, ~110 erdosproblems pages, 3 forum threads, Palomar
about, arXiv abstracts, Xena blog, OEIS).
