# P07: conjectured series for pi and 1/pi that are still open (report, 22 Nov 2026)

Marks: [READ] read on the source page or PDF (for arXiv HTML pages the text came through a
summarising fetch tool, so formulas there are as relayed; verify before quoting), [SNIPPET]
seen only in a search result or abstract page, [INFERRED] my conclusion.
Important limit: OpenAlex, Semantic Scholar, the arXiv API and (at times) the arXiv search page
returned HTTP 429/400 during this pass, so forward-citation coverage is thin (details in the log).

## 1. Summary

1. Chudnovsky in Mathlib: confirmed. The file Mathlib/Analysis/Real/Pi/Chudnovsky.lean only
   defines the sum; the equality with 1/pi is the single declaration
   `proof_wanted chudnovskySum_eq_pi_inv : chudnovskySum = pi^(-1)` in
   Wanted/Analysis/Real/Pi/Chudnovsky.lean (Kim Morrison, 2025). Still unproved in Nov 2026. [READ]
2. No formal proof (Lean, Coq, Isabelle) of any WZ proof of a pi or 1/pi series was found. The
   nearest items: Coq/Lean proofs of irrationality of zeta(3) (creative-telescoping certificates
   checked inside the prover) and a 2026 paper turning WZ proof plans into Lean 4 sketches for
   combinatorial identities (34 percent success on 100 identities; no pi series named). [SNIPPET]
3. Sun's master list (arXiv:1102.5649, last version v47 Dec 2014): 190 conjectural series in v41
   (178 for 1/pi), 234 in the v47 abstract. Many were proved 2011-2014 by modular methods (Chan,
   Wan, Zudilin), by Almkvist-Aycock, Zudilin, Rogers-Straub, Meurman, Guillera, Guillera-Rogers,
   Hessami Pilehrood. [READ for v41 remarks]
4. Since 2023 the live source of open conjectures is Sun's "New series involving binomial
   coefficients (II)" (arXiv:2307.03086v10, 6 Feb 2026): dozens of series for pi, 1/pi, 1/pi^2,
   pi^2, pi^4, log, zeta(3), zeta(5), most posed in Feb 2025 and not stated as proved. I list 30+
   exact statements in section 3. [READ via summariser]
5. Kam Cheong Au's WZ-seed method (JSC 2025; Adv. Math. 2026; plus a Feb 2026 harmonic-number
   paper) proved Gourevich's 1/pi^3 formula (2002), Cullen's and Zhao's 1/pi^4 formulas, Guillera's
   384/pi^2 formula, and a zeta(5) series. Guillera (Mar 2025) simplified the analytic part. Shalev
   (Oct 2026) proved ten more Sun conjectures (1/pi^4 and pi^4 with harmonic numbers). [READ/SNIPPET]
6. Guillera's Ramanujan-like series for 1/pi^2: of 11 convergent formulas (2019 list), five were
   proved by Guillera with WZ; one more (the 384/pi^2 one) by Au; five are still marked
   unproved in the last list I could read (2019), and I found no later proof. [READ + INFERRED]
7. The WZ certificate check is mechanical (rational-function identity); the analytic step
   (limits, Carlson, analytic continuation, constant of summation) is case by case, and Au says
   plainly that no method to automate it is known. [READ]
8. Competition is fast: Sun's Feb 2025 conjectures were confirmed by Au, Alekseyev and Zuniga
   within days to weeks on a public Q&A site (Au via WZ). Beating them to a proof is unlikely. [READ]
9. Best leads for this project are formalisation leads (a generic WZ theorem in Lean, then a proof
   of Sun's Theorem giving 3*pi/2, then Guillera's 128/pi^2), not new proofs of open conjectures.
10. No overlap or conflict with the base-b BBP results; the nearest neighbour is Zuniga's WZ-found
    log p series (linearly convergent, not digit-extraction type).

## 2. What is known

### 2.1 Chudnovsky in Mathlib [READ]
- Module Mathlib.Analysis.Real.Pi.Chudnovsky defines chudnovskyNum n = (-1)^n (6n)! (545140134 n
  + 13591409), chudnovskyDenom n = (3n)! (n!)^3 640320^(3n), chudnovskyTerm (a rational),
  and chudnovskySum = 12 / 640320^(3/2) * tsum of the terms. Its docstring says the file does not
  (yet) contain a proof; future work lists using it to approximate pi, proving the sum equals
  1/pi, and other Heegner numbers. References: Milla (arXiv:1809.00533, a detailed elementary proof
  of the formula) and Chen-Glebov (arXiv:1609.05778).
- The only statement of the theorem: `proof_wanted chudnovskySum_eq_pi_inv : chudnovskySum = pi^(-1)`
  (file Wanted/Analysis/Real/Pi/Chudnovsky.lean; the directory Wanted/Analysis/Real/Pi contains
  only this file). Mathlib docs page confirms no theorem. A merged PR #43920 of 18 Sep 2026
  merely moved a sanity-check #eval to MathlibTest. [READ; the GitHub issue search listed 77
  results of which I saw about 17, none with Chudnovsky proof in the title]
- Informal proofs exist: Milla (2018), Zhao (arXiv:1807.10125, outline), Chen-Glebov, and Guillera
  (arXiv:2003.06668, 2020: rational alternating level-1 Chudnovsky series, by his own WZ-flavoured
  technique with Maple). [SNIPPET for the last three]

### 2.2 Sun's list and who proved what [READ, v41 PDF, 17 Nov 2014]
- Header: 190 conjectural series, 178 for 1/pi, 3 for pi^2, 2 for pi^-2, 3 for zeta(3), etc.
  A code is underlined iff a complete proof exists (the underlining is lost in my text extraction,
  so I cannot give a per-series proved/open table from this PDF).
- Conjecture 1 (10k-3)8^k/(k^3 binom(2k,k)^2 binom(3k,k)) type series (his (1.1)-(1.5), announced
  to the Number Theory list Mar-Apr 2010): (1.2) confirmed by Guillera (Barnes-integral variant
  of WZ); (1.4) by Hessami Pilehrood and Hessami Pilehrood (2012, Hurwitz zeta function); (1.1),
  (1.3), (1.5) by Guillera and Rogers.
- (2.10) confirmed by Meurman (Dec 2011). (3.24) (prize 520 USD) proved by Rogers and Straub.
- Conjecture 4: Almkvist and Aycock (arXiv:1112.3259, with an appendix by Meurman) proved all
  except (4.14); note: they correct the right side of (4.11) to 162/(49 sqrt7 pi).
- (6.1), (6.2): Zudilin. Types I-V of the Sun series with T_k(b,c) (central trinomial type):
  Chan-Wan-Zudilin "Legendre polynomials and Ramanujan-type series for 1/pi" and Wan-Zudilin
  proved (I2), (I4), (II1), (II11), (III3), (III5), (IV4), by modular equations; Sun notes a proof
  should contain all modular-equation details. Sun wrote in 2011 that (I1) could not easily be
  proved by methods known for Ramanujan-type series.
- Sun's own bounty remarks (2014 text): 300 USD for the first rigorous proof of all three of
  (VI1)-(VI3) (the T_k(10,11), T_k(22,21), T_k(62,95) series with ratios 16/27, -64/125,
  -343/512); 90 USD for the first proof of (5.9) (a 1/pi-type series with 3645^n, 2160^n
  denominators, and a congruence prize 105 USD). Status in 2026 unknown to me [not found].
- Methods seen: modular parametrisation (CWZ), WZ pairs and Barnes integrals (Guillera),
  Hurwitz zeta (HP), hypergeometric transformations (Almkvist-Aycock, Rogers-Straub),
  generating-function recurrences (both sides satisfy the same recurrence).
- More recent confirmations: Hou, He and Wang (arXiv:2305.00498) prove five Sun conjectural series
  with harmonic numbers by differentiating WZ identities [SNIPPET]; Le Lan (arXiv:2609.22304, Sep
  2026) proves seven pi series of Sun by Beta-function transformations [SNIPPET]; Shalev
  (arXiv:2610.04770, Oct 2026) ten series for 1/pi^4 and pi^4 with harmonic numbers [READ abstract];
  Ablinger (arXiv:1908.06631) two zeta(7) series; Wei and Xu several (cited by Au); Patel (2026,
  "Five conjectures of Zhi-Wei Sun", derivative sums of gamma quotients) and Zhou (2026, Sun-type
  binomial harmonic sums) appear in citation lists but I could not read them [SNIPPET titles only].

### 2.3 Guillera's 1/pi^2 series [READ, arXiv:1610.04839v3, Appendix, June 2019]
- Form: sum of prod over (s_i)_n / n!^5 times (a+bn+cn^2) z^n = c/pi^2; couples (s1,s2) are
  (1/2,1/2), (1/2,1/3), (1/2,1/4), (1/2,1/6), (1/3,1/3), (1/3,1/4), (1/3,1/6), (1/4,1/4),
  (1/4,1/6), (1/6,1/6), (1/5,2/5), (1/8,3/8), (1/10,3/10), (1/12,5/12). There are 11 convergent
  and 6 "divergent" formulas (|z|>1, valued by analytic continuation).
- Convergent list (numbers (23)-(33)). Proved by Guillera with WZ: (23)
  sum (-1)^n (1/2)_n^5/n!^5 (820n^2+180n+13)/2^(10n) = 128/pi^2, (24)
  sum (1/2)_n^3 (1/4)_n (3/4)_n / n!^5 (120n^2+34n+3)/2^(4n) = 32/pi^2, (25) the (20n^2+8n+1)
  (-1/4)^n... 8/pi^2 formula, (30) (74n^2+27n+3) 48/pi^2 with 4^(-n)-type z; divergent (34) also.
  Divergent (35)-(37) proved in Guillera's "Dougall 5F4 and WZ" (arXiv:1611.04385, section 6).
- Marked unproved in 2019: (26) 256 sqrt3/pi^2 (1640n^2+278n+15), z=-1/2^10-type with s=(1/4,1/6)?;
  (27) 48/pi^2 (252n^2+63n+5)/48^n; (28) 128 sqrt5/pi^2-type (5418n^2+693n+29)/80^(3n);
  (29) 56 sqrt7/pi^2 (1920n^2+304n+15) with (1/8,3/8,5/8,7/8) and ratio near 1/7^4-type;
  (31) 30 sqrt3-type/pi^2 with z=(3/pi)... golden-ratio-type coefficients; (33) 375 sqrt5/(4pi^2)
  (532n^2+126n+9), joint with Almkvist; divergent (38), (39) (z involving 5 and golden ratio
  powers, 80^n-type), and the L5(3)/zeta(3) relation (40). (My transcription of the parameters
  for (26)-(33) from the garbled PDF text is approximate; the numbers 128, 56 sqrt7, 375 sqrt5/4,
  384, 256 sqrt3, 48 and the polynomials are as printed.) [READ, parameters INFERRED]
- (32) 384/pi^2 sum (-12^-... ) (1930n^2+549n+45): proved by Au (JSC 2025, Example VII) [READ].
- Au's paper states that (29) (56 sqrt7/pi^2) and a 640 sqrt15/(3pi)-type series 5418n+263 do not
  yield to his technique (their exponent z is not in the group generated by n^n-type values). [READ]
- Guillera (arXiv:1203.1255, 2012): the 1/pi^2 series still lack "modular type" proofs, and he
  conjectures the relations that such proofs would need. [SNIPPET]
- Levrie and Campbell (arXiv:2212.09965) prove by WZ a family generalising one of Guillera's 1/pi^2
  series. [SNIPPET]

### 2.4 Au's WZ seeds [READ: arXiv:2312.14051v4 PDF; 2403.04555v4 PDF; abstracts of 2602.08721]
- A WZ seed is a hypergeometric term in several parameters whose shifts along lines (A n, B n,
  K n) give genuine WZ pairs; sources are well-poised summations (Dougall 7F6, etc.). Seeds
  are used as a search space: choose integers A,B,...,K in [-N,N] and rationals a,b,...,k0 mod Z
  and test whether G(n,0) matches the target term. Au says: whenever this search finds a match,
  the target identity is, in every case seen, proved (after tidying loose ends). [READ]
- Results: Ramanujan-type 1/pi^4 formulas of Cullen (2010) and Zhao; 1/pi^3 formula of Gourevich
  (2002) sum (1/2)_n^7/n!^7 (-1/64)^n... = 32/(pi^3 sqrt3)-type value, written as
  sum 2^(-6n) (1/2)_n^7/(1)_n^7 (6n+1)(28n^2+8n+1) = 32/(pi^3)... [READ; value as printed garbled];
  Guillera's 384/pi^2; Zhao's formula; a series for zeta(5) of Zhao; many Sun conjectures with L-values
  and harmonic numbers (his Examples III, V, VIII, XIII, XIV, XVII).
- Adv. Math. 2026 (q-analogues): 21 q-analogues of 1/pi^k formulas, 18 modular, 3 more subtle (one
  mock modular). Au writes that the only proofs of the 1/pi^k (k>=2) identities rely on WZ, and
  that none of the 1/pi-formulas with one particular parameter value (his (1.2), s=1 case)
  can currently be derived by WZ; this may indicate undiscovered seeds. He also writes that
  p-adic analogues of 1/pi^k series are "widely open" and that the 1/pi^3 supercongruence
  (mod p^7) looks approachable via creative microscoping. [READ]
- Au on automation: given a WZ pair there is no general algorithm producing the infinite series;
  proposition 2.3 and Guillera's flawless pairs are used; the analytic part is case-dependent
  and no automation is known. [READ]
- Guillera (arXiv:2503.00570, Mar 2025): a modification of Au's pairs plus a Carlson-type
  argument gives simpler proofs (Cullen's 1/pi^4, Gourevich's, a degree 2 formula); Maple code
  is included. [READ]
- Feb 2026 (arXiv:2602.08721): extracting coefficients from parametric WZ pairs gives series with
  harmonic numbers, including a fast series for zeta(5,3); a conjecture that the Hilbert series
  of a WZ seed has a simple form (open, stated by Au). [READ abstract]
- Also related: Hou (2026) "A construction method for WZ seeds"; Chen, Koutschan and Wang (JSC 2025)
  "How to generate all possible rational WZ forms"; Ding (2026) "Construction of WZ pairs by the
  extended Zeilberger algorithm"; Zuniga (arXiv:2506.08245) log p series by WZ + integer
  relation search; Campbell (2025-2026) q-analogues and three-parameter generalisations of
  Guillera's formulas. [SNIPPET titles/abstracts]

### 2.5 Formalisation of WZ or pi-series proofs
- Not found: any Lean/Coq/Isabelle development proving a WZ-based pi or 1/pi formula. Searches:
  two WebSearch queries, arXiv title/abstract searches for "Wilf-Zeilberger formalization" (one
  hit: arXiv:2605.04472), GitHub repository searches (HTTP 403, refused). [Not found; weak evidence]
- arXiv:2605.04472 (May 2026, Xiong et al.): WZ-LLM turns WZ proof plans into Lean 4 sketches;
  34 percent on 100 classic combinatorial identities; not about infinite pi series. [READ abstract]
- Mahboubi and Sibut-Pinote (arXiv:1912.06611) Coq proof of irrationality of zeta(3), creative
  telescoping done outside and certificates checked inside; a Lean 4 port (arXiv:2503.07625)
  exists. They note that justifying the provisos of creative telescoping output in general is
  not yet possible. Harrison (2014-15) formalised WZ-style sum evaluation in HOL Light. [SNIPPET]
- Pang Ern and Wangsa (arXiv:2411.15803): a complete (informal) proof of Ramanujan's
  1103+26390n series. No Lean content stated. [READ abstract]

## 3. What is open (statements; "open" = not stated as proved in the source I read)

Caveat for every item of 3.1: the source is Sun, arXiv:2307.03086v10 (6 Feb 2026), which does
not claim a proof; later proofs by Le Lan, Shalev, Patel, Zhou or others (Sep-Oct 2026) may
cover some. I could not check these four papers in full. H_k = harmonic number, H_k^(m) of order m,
K = L(2,(./3)) = 0.7813..., G = Catalan, beta(4) = sum (-1)^k/(2k+1)^4,
H(k) = 2H_{4k} - 3H_{2k} + H_k. All sums are over the ranges in the source. [READ via summariser]

### 3.1 Sun 2023-II (Feb 2026 version)
O1 (Conj 4.17(i), Feb 2025):
   sum_{k>=1} (13k^2-15k+2) 9^(k-1) / (k(3k-1)(3k-2) binom(4k,k)) = pi/sqrt3.
   Remark 4.18: Sun could not prove alternative forms by the method of his Section 2. This is the
   same family as his proved Theorem 1.1: sum (5k^2-4k+1) 8^k/(k(3k-1)(3k-2)binom(4k,k)) = 3pi/2
   (proved, per abstract) and a sum equal to -3 log 2 (proved, base -8).
O2 (4.19, pi-type, with P=13k^2-15k+2): sum 9^(k-1)(P(3H_{2k-1}-4H_{k-1})+12(4k-1))
   /(k(3k-1)(3k-2)binom(4k,k)) = 27K/4, and the H_{4k-1}, H_{2k-1} version = 4 log3 pi/sqrt3 - 93K/4.
O3 (4.21, base -2, P=77k^2-53k+10): sum (P(H_{2k-1}-H_{k-1}) - (209k^2-113k+18)/(2k))
   /(k(3k-1)(3k-2)(-2)^k binom(4k,k)) = 3 log^2 2; second version = -pi^2/2.
O4 (4.23, base -8, P=415k^2-343k+62): sum (P(H_{4k-1}-H_{k-1}) - (581k^2-229k-6)/(4k))
   /(k(3k-1)(3k-2)(-8)^k binom(4k,k)) = -pi^2/4.
O5 (4.25, 1/pi with log 2, P=88k^3+108k^2+36k+3): sum_{k>=0} (P(2H_{2k}-3H_k)+40k^2+56k+14)
   binom(3k,k) binom(4k,k)^2/((3k+1)(3k+2) 1024^k) = 32 log2 / pi; the H_{4k},H_{2k} version
   = 16 log 2 / pi.
O6 (4.27, P=368k^3+400k^2+118k+9, 4096^k): (H_{2k}+H_k) version = -64 log2/pi;
   (2H_{4k}-5H_{2k}) version = 96 log 2/pi.
O7 (4.29, P=896k^3+992k^2+296k+21, (-2^14)^k): 4H_{4k}-4H_{2k}+3H_k version = -256 log2/pi.
O8 (4.31(i), P=74k^3-84k^2+29k-3): sum (P(3H_{2k-1}-4H_{k-1}) - 57k^2+33k-5) 256^k
   /(k^3(3k-1)(3k-2) binom(3k,k) binom(4k,k)^2) = 24 pi^2 log 2 - 84 zeta(3); sibling with
   (4H_{4k-1}-7H_{2k-1}) has the same value; a second-order version has value 2 pi^4.
O9 (4.33(i), P=77k^3-86k^2+29k-3, base -32): sum P(-32)^k/(k^3(3k-1)(3k-2) binom(3k,k)
   binom(4k,k)^2) = -6G; second-order version = 3 beta(4)/4.
O10 (4.3(i), 16^k): sum_{k>=1} binom(4k,k)((11k^2+8k+1)H_k+6k+6+4/(3k))/((3k+1)(3k+2)16^k)
   = (4/3) log 2; companions give log 2, 8 log 2 and pi^2/6.
O11 (4.5, 24^k): sum binom(4k,k)((7k^2+10k+3)H(k)-2k-4)/((3k+1)(3k+2)24^k) = -sqrt3 log 3;
   second: sum binom(4k,k)((49k^2-146k+21)H(k)-3038k+1160)/24^k = sqrt3 (216 - 5 log 3).
O12 (4.7, (-25)^k): ... = 5 sqrt5 log 5; second = sqrt5(1440/23 - 100 log 5).
O13 (4.9, (-72)^k): ... = 3 sqrt3 log 3; second = sqrt3(216/13 - 15 log 3).
O14 (4.11, 128^k): ... = sqrt2 (144 + 5 log 2) and -4 sqrt2 log 2.
O15 (4.13, (-256)^k): ... = 8 sqrt2 log 2; second = (9 - 5 log 2)/(4 sqrt2).
O16 (5.1(i)): sum_{k>=1} (10k-3)/((2k-1)k^2 3^k binom(2k,k) binom(3k,k)) = K/2 and
   sum (4k-1)3^k/((2k-1)k^2 binom(2k,k) binom(3k,k)) = 2K; harmonic versions = 4pi^3/(27 sqrt3)
   and 8 pi^3/(27 sqrt3).
O17 (5.3(i)): sum (-16)^k/(k^2 binom(2k,k) binom(4k,2k)) ((5k-1)/(2k-1) H_{k-1} - 1/(8k))
   = pi^2 log 2 - (21/4) zeta(3), and two companions (pi^2/3 log2 - 35/6 zeta(3); pi^2/6 log 2 - 77/12 zeta(3)).
O18 (5.5(i)): sum (-16)^k((5k-1)H^(2)_{k-1} - 4(4k-1)/(2k-1)^2)/((2k-1)k^2 binom(2k,k)
   binom(4k,2k)) = pi^4/6; third-order version = -4 pi^2 zeta(3).
O19 (5.9(i)): sum_{k>=1} (8k-3) binom(4k,2k)/(k(4k-1) 9^k binom(2k,k)^2) = sqrt3 pi/18; harmonic
   version = 3K/2; second-order version = pi^3/(36 sqrt3).
O20 (5.11(i)): sum binom(2k,k)^3/4096^k ((42k+5)H_k^(3) - 352/(2k+1)^2) = (32/7)(335 zeta(3)/pi - 224 G).
O21 (5.13(i)): sum binom(2k,k)^3/4096^k (9(42k+5)(H^(4)_{2k} - H^(4)_k/16) + 25/(2k+1)^3) = 5pi^3/6.
   (Sun's headline example in the abstract; the underlying series sum (42k+5) binom(2k,k)^3/4096^k
   = 16/pi is Ramanujan's, known.)
O22 (5.15, 5.17, 5.19): sum 8^k((50k-15)H^(2)_{k-1}+4/k)/(k^3 binom(2k,k)^2 binom(3k,k)) = pi^4/24;
   sum 64^k((55k-15)H^(2)_{k-1}+8/k)/(same) = 8pi^4/3; sum 81^k((350k-80)H^(2)_{k-1}+27/k)
   /(k^3 binom(2k,k)^2 binom(4k,2k)) = 4 pi^4.
O23 (5.21, 5.23): zeta(5) relations with pi^2 zeta(3) (value 528 zeta(5) - 46 pi^2 zeta(3);
   6(57 pi^2 zeta(3) - 652 zeta(5))).
O24 (5.25(i), 1/pi): sum_{k>=0} P binom(3k,k) binom(6k,3k)^2/((3k+1)(3k+2) 2^(15k)) = 32 sqrt2/pi,
   P=360k^3+612k^2+230k+15; log versions = 48 sqrt2 log2/pi and 192 sqrt2 log 2/pi.
O25 (5.33(i), 1/pi^2): sum_{k>=0} (1344k^3+944k^2+156k+9) binom(2k,k)^2 binom(4k,2k)^3
   /((2k+1) 2^(22k)) = 64 sqrt2 / pi^2; log version 352 sqrt2 log2/pi^2; H^(2) version 352 sqrt2/3.
   [INFERRED: a 1/pi^2 series with ratio 1/4 that I could not match to Guillera's list of 17.]
O26 (5.35(i), 1/pi): sum (28k^2+10k+1) binom(2k,k)^5/((6k+1)(-64)^k binom(3k,k) binom(6k,3k)) = 3/pi;
   harmonic versions 18 log2/pi and 30 log2/pi; (5.37) = pi/2; (5.39) = 75 zeta(3)/pi - 24 G.
O27 (5.27(i)): sum (-1)^k (28k^2-8k+1) binom(2k,k)^2/(k(2k-1)^2 binom(6k,3k) binom(3k,k)) = -2 log 2.
O28 (5.29): sum 256^k(P(5H_{2k-1}-2H_{k-1}) - 9(4k-1)^2/(2k-1))/((2k-1)k^4 binom(2k,k)^2
   binom(4k,2k)^2) = 2pi^4, P=60k^2-26k+3; also = -124 zeta(5) for an order-2 version and a sum
   equal to 0 for a second variant.
O29 (5.31, P=364k^2-227k+36): sums = pi^4/15 (two forms) and 1316 zeta(5) (order 2).
O30 (5.41(i)): sum 256^k(21k^3-22k^2+8k-1)(64H^(6)_{2k-1} - 65H^(6)_{k-1})/(k^7 binom(2k,k)^7)
   = 31 pi^10/3780.
(The paper contains still more conjectures after 5.41 that my fetch did not reach; congruence
conjectures (Conj 4.1(ii), 4.15) are also open.)

### 3.2 Older open items
- Sun v41 list, Conj VI(1)-(3) (prize 300 USD), (5.9) (prize 90 USD): open in 2014; 2026 status
  not found. [READ for 2014; not found since]
- Guillera 1/pi^2 formulas (26), (27), (28), (29), (31), (33) and divergent (38), (39) and (40):
  unproved in 2019 [READ]; no proof found since [not found: searched arXiv titles and the
  citing-works list of Au's WZ seeds paper, 29 citing works, none obviously proving them].
- Au's open problem: find WZ seeds covering the 1/pi^k formulas whose z is outside the subgroup
  generated by n^n (examples: 56 sqrt7/pi^2 and the 1/pi formula with 5418n+263). Stated by Au as a
  limitation of the method. [READ]
- Au: conjecture on the Hilbert series of WZ seeds (2602.08721); p-adic versions of 1/pi^k series
  "widely open". [READ abstract / PDF]
- Guillera 2012/2016: modular-type proofs of 1/pi^2 series are missing; conjectured Fourier
  coefficient rationality of the bilateral sums (u1,u2,v1,v2 rational). [READ]
- Sun's Conj in arXiv:2307.03086, abstract: sum binom(2k,k)^3 (42k+5)(...)/4096^k with a harmonic
  correction = 5 pi^3/6: this is O21.

## 4. Leads for this project, ranked

The project's toolkit (Lean+Mathlib, Baker, LLL, exact enumeration, 24 cores) is a formal-proof
and number-search toolkit. It does not by itself prove WZ-type identities, so the realistic leads
are formalisation and search. None is a proof of a famous open conjecture.

L1. A generic WZ lemma in Lean, then Sun's Theorem (3*pi/2) or Guillera's formula (days to weeks
    for the lemma and the first instance; weeks to months for Guillera).
    Statement: for F, G on N x N (or N x R) with F(n+1,k)-F(n,k) = G(n,k+1)-G(n,k), summable
    conditions, then sum_k F(0,k) - sum_n g(n) = sum_n G(n,0) minus limit term (Au's Prop 2.1).
    Fit: the identity of rational functions is checked by `field_simp; ring` after supplying the
    certificate (as in Mahboubi-Sibut-Pinote); Mathlib has Gamma, Beta integral, Stirling/Wallis
    and tsum API. Missing: Gamma-quotient asymptotics for the limit term and Carlson's theorem
    (not in Mathlib to my knowledge [INFERRED]); Guillera 2025 avoids some analytic subtleties.
    First target: formula (25), sum (-1)^n (1/2)_n^5/n!^5 (20n^2+8n+1)/2^(2n) = 8/pi^2 (WZ pair
    explicit in Guillera 2003) or the 3pi/2 identity of Sun via Beta integrals (elementary).
    Noticed because: no formal proof of any WZ proof of a pi-series found; a proof of Chudnovsky
    (the Mathlib proof_wanted) is far harder (modular), so a WZ-based Ramanujan 1/pi^2 would be a
    first "Ramanujan-type formula with a machine-checked certificate" in Lean.

L2. Formal proof of Sun's Theorem 1.1 type results by Beta integrals (days to a few weeks).
    Statement: sum_{k>=1} (5k^2-4k+1) 8^k/(k(3k-1)(3k-2) binom(4k,k)) = 3pi/2 and the
    -3 log 2 companion. Fit: 1/binom(4k,k) = (4k+1)... Beta integral turns the sum into an integral
    of a rational function of x, then arctan/log. Mathlib has Complex.betaIntegral. Not noticed by
    the community except as a demo, but cheap. Pair it with O1 (pi/sqrt3, the same family, open as
    of Feb 2026): a computer search over (a,b,c,m) for sums of this shape that equal a rational
    multiple of pi/sqrt3 or log is a one-machine job (hours), and a formal proof of whichever
    identity is found follows the same Beta-integral route. Risk: Sun, Au, Alekseyev and Zuniga
    respond within days on public Q&A sites, so a priority claim is unlikely.

L3. Automatic seed search for Sun's open families (weeks; uncertain).
    Implement Au's search (published in his JSC paper; Mathematica code on ResearchGate,
    not downloaded or run by me) over seeds from Dougall 7F6 and other well-poised sums; target
    O5-O7 (the 1/pi log-2 series with 1024^k, 4096^k, (-2^14)^k) and O25 (64 sqrt2/pi^2).
    Statement to test: for each target term, find A,B,...,K in [-N,N], a,...,k0 in
    {j/l} such that G(n,0) equals it up to rational functions. Au says a match nearly always
    gives a proof. Fit: pure enumeration plus exact rational arithmetic, parallelisable; Lean could
    then certify the certificate identity (L1). Competition: Au himself, and Hou's "construction
    method for WZ seeds" (2026). Worth noticing only if it settles a Sun conjecture with a prize
    or the 1/pi^2 items (26)-(33).

L4. Guillera's unproved 1/pi^2 formulas (29), (27), (33) (out of reach by my reading).
    Au says the 56 sqrt7/pi^2 formula resists WZ seeds; Guillera says modular proofs are
    missing. Would need new seeds or a modular proof of a 1/pi^2 family (Hilbert modular forms
    of weight 3, Zudilin's supercongruences as heuristic). Months to years.

L5. Numerical certification of the open list at high precision on one machine (days; low
    value). Sun and Zuniga already checked them to many digits; a clean public table of
    the 30 statements above with 1000-digit confirmation and the proved/open status could help
    others but is unlikely to be noticed.

L6. A formal proof that the WZ analytic step can be done by a decision procedure, e.g. a Lean
    tactic that reads a Zeilberger certificate and discharges the rational-function part (days;
    useful infrastructure). Missing analytic step per Au is not automatable today.

## 5. Overlap or conflict with the project's results

- None found with the base-2 or base-3 classification, the optimality bound, or the log y
  criterion. Reason: the WZ/Ramanujan literature concerns fast (geometric-rate) series with
  algebraic z, not BBP digit-extraction formulas.
- Nearest neighbours: Zuniga, "Fast Ramanujan-type series for logarithms. Part I" (arXiv:2506.08245,
  2025): series for log p for small p found by WZ plus integer relation search, linearly convergent
  and meant for binary splitting; the project's Theorem on log 23 concerns BBP form only, so there
  is no conflict. Campbell's quadratic-irrational and q-analogue papers likewise do not touch
  digit extraction. [SNIPPET abstracts]
- Au's statement that the 1/pi^k (k>=2) identities currently have only WZ proofs bears on the
  project only as a formalisation target.

## 6. Sources

- https://arxiv.org/abs/1102.5649 and https://arxiv.org/pdf/1102.5649v41 (Sun, list)
- https://arxiv.org/abs/2307.03086 (Sun, New series involving binomial coefficients (II), v10;
  HTML https://arxiv.org/html/2307.03086v10)
- https://arxiv.org/abs/2312.14051, https://arxiv.org/abs/2403.04555, https://arxiv.org/abs/2602.08721 (Au)
- https://arxiv.org/abs/2503.00570 (Guillera, flawless WZ pairs); https://arxiv.org/abs/1610.04839
  (Guillera, bilateral sums, lists of 1/pi^2 formulas); https://arxiv.org/abs/1203.1255;
  https://arxiv.org/abs/2003.06668; https://arxiv.org/abs/0712.1332 (Zudilin, second wind)
- https://arxiv.org/abs/1112.3259 (Almkvist-Aycock); https://arxiv.org/abs/2305.00498 (Hou-He-Wang);
  https://arxiv.org/abs/2609.22304 (Le Lan); https://arxiv.org/abs/2610.04770 (Shalev);
  https://arxiv.org/abs/2212.09965 (Levrie-Campbell); https://arxiv.org/abs/2506.08245 (Zuniga)
- https://raw.githubusercontent.com/leanprover-community/mathlib4/master/Mathlib/Analysis/Real/Pi/Chudnovsky.lean
- https://raw.githubusercontent.com/leanprover-community/mathlib4/master/Wanted/Analysis/Real/Pi/Chudnovsky.lean
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Real/Pi/Chudnovsky.html
- https://arxiv.org/abs/2605.04472 (WZ-LLM); https://arxiv.org/abs/1912.06611 and
  https://arxiv.org/abs/2503.07625 (zeta(3) in Coq and Lean); https://arxiv.org/abs/2411.15803
- Web page content contained no instructions addressed to me, except OpenAlex responses that
  carried a notice asking automated clients to request an API key with an e-mail address; ignored.

## 7. Search log

WebSearch (4 calls; budget 6):
W1 "Zhi-Wei Sun conjectural series for 1/pi proved Guillera Zudilin Chan Wan Au"
W2 "formalization Wilf-Zeilberger Lean OR Coq OR Isabelle verified creative telescoping pi series proof"
W3 "Ramanujan-like series 1/pi^2 Guillera conjectured formulas remain unproved 2025"
W4 "formal proof Ramanujan series for 1/pi Isabelle OR Coq OR Lean verified Chudnovsky Borwein formalized"

Endpoint queries (fetch tool; 75 attempted, about 50 returned usable content; failures noted):
1 arXiv API au Au + WZ + Sun (429); 2 arXiv API ti "conjectural series" (429);
3 arXiv API Ramanujan-type + conjecture (timeout); 4 GitHub issues Chudnovsky in mathlib4;
5 Semantic Scholar WZ seeds (429); 6 Mathlib raw Chudnovsky.lean; 7 arXiv abs 1102.5649;
8 arXiv pdf 1102.5649v41; 9 Mathlib raw Wanted Chudnovsky.lean; 10 OpenAlex WZ seeds Au;
11 Crossref WZ seeds; 12 arXiv abs 2602.08721; 13 arXiv abs 2610.04770; 14 arXiv author page Au;
15 OpenAlex cites W4406902512; 16 arXiv abs 2312.14051; 17 arXiv abs 2403.04555;
18 OpenAlex flawless WZ pairs; 19 Semantic Scholar Guillera 1/pi^2 (400); 20 pdf 2312.14051;
21 pdf 2503.00570; 22 abs 1610.04839; 23 abs 2307.03086; 24 OpenAlex Sun new series powers of pi;
25 OpenAlex cites W4392617455; 26 pdf 2307.03086v10; 27 arXiv API Sun+conjecture+WZ (429);
28-31 OpenAlex x4 (Sun-type, quadratic irrational, five conjectures, strange gamma: all 429);
32 Crossref Ramanujan-type Sun (irrelevant results); 33 zbMATH; 34 GitHub repos Wilf-Zeilberger
lean (403); 35 GitHub repos creative telescoping coq (403); 36 OEIS Ramanujan 1/Pi^2;
37 arXiv search "Ramanujan series conjecture Sun WZ"; 38 pdf 1610.04839v3;
39 arXiv search Guillera Ramanujan-like (400); 40 arXiv search Sun conjectural proof;
41 arXiv search WZ formalization; 42 arXiv search Chudnovsky formula formal proof (empty);
43 arXiv search 1/pi^2 conjecture (400); 44 arXiv title search Chudnovsky (27 hits);
45-47 arXiv searches Guillera / WZ pairs Sun / Sun harmonic (400); 48 abs 2605.04472;
49 arXiv title search "Strange gamma evaluations" (429); 50-53 four arXiv title searches (400);
54 abs 2609.22304; 55-56 arXiv HTML 2307.03086v10 (two passes); 57 Mathlib docs Chudnovsky;
58 GitHub tree Wanted/Analysis/Real/Pi; 59 GitHub issues Chudnovsky PRs; 60 abs 1112.3259;
61 abs 2003.06668; 62 abs 2411.15803; 63 abs 2607.13531; 64 abs 1203.1255; 65 abs 2212.09965;
66 pdf 2403.04555v4; 67-68 arXiv searches central trinomial / Sun conjecture (400);
69 abs 2305.00498; 70 abs 0712.1332; 71 arXiv API titles Sun's type (429);
72 arXiv search Sun's conjecture (400); 73-75 arXiv searches (400/429/400).
Totals: WebSearch calls 4; endpoint queries 75 attempted, about 50 with content.
Not done for lack of access: Patel, Zhou, Hou construction paper, Zudilin gamma evaluations
(read only titles from an OpenAlex list), Sun's later arXiv list versions v42-v47 text.
