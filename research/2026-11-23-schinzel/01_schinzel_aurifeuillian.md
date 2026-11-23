# Schinzel 1962 and primitive prime factors of the Aurifeuillian factors of 3^(3E)+1

Date: 2026-11-23. Summary: I could NOT open the text of Schinzel's paper (paywalled; the Cambridge page shows only the first sentence).
Everything about Theorems 1/2 below is therefore secondhand. The exact theorem, its exception list, and the "one in each factor" claim are NOT verified.

## 1. Schinzel's Theorem 1/2 and exceptions
- Paper: A. Schinzel, On primitive prime factors of a^n - b^n, Proc. Cambridge Philos. Soc. 58 (1962), 555-562 (some sources say 556-562).
  https://www.cambridge.org/core/journals/mathematical-proceedings-of-the-cambridge-philosophical-society/article/on-primitive-prime-factors-of-anbn/FF4F8CB4D5BEDD2854151670559F36C6
  DOI 10.1017/S0305004100040561
- [READ, Cambridge page] Only the opening: a, b coprime, |a| > |b| > 0, then the cyclotomic polynomial definition. No theorem statement visible.
- [READ, Stewart arXiv 1008.1274, intro, https://arxiv.org/pdf/1008.1274] Stewart describes Schinzel's result as: if a, b coprime and ab is a square or twice a square,
  then P(a^n - b^n) >= 2n+1 (P = greatest prime factor), excluding n = 4, 6, 12 when a=2, b=1. Proved by showing a^n - b^n has at least two primitive divisors, using an
  Aurifeuillian factorization of Phi_n. NOTE: this is a different hypothesis ("ab = square or twice a square") from your "n/(eta*kappa) odd" with kappa = squarefree kernel.
  For a=3, b=1, ab = 3 is neither, so a=3,b=1 is not in the case Stewart describes. This does not contradict your belief: Stewart's summary is probably a simplified
  corollary (his wording may also be about the exponent form). [INFERRED] I cannot reconcile the two without the paper.
- [READ, Waterloo "Comments for the Selecta of A. Schinzel", https://uwaterloo.ca/pure-mathematics/sites/default/files/uploads/documents/schinzel-report1_0.pdf]
  Schinzel gave new Aurifeuillian factorizations and used them to give conditions under which a^n - b^n has at least two primitive divisors. No statement or exception list.
- Your kappa/eta formulation: NOT confirmed anywhere I could read. [UNVERIFIED]
- n = 6, a=3, b=1: not determined from sources. [INFERRED, own arithmetic] 3^6 - 1 = 728 = 8*7*13; Phi_6(3) = 7 = 3^2 - 3 + 1 (one primitive prime, 7), so E=1 gives
  L_1 = 3^1 - 3^1 + 1 = 1 and M_1 = 7: L_1 trivial, so at n=6 "two primitive factors" fails (only 7). So an exception at E=1 is forced; consistent with your E >= 3.
  (Bang/Zsigmondy exception is only a=2,b=1,n=6; for a=3 n=6 has primitive prime 7.)

## 2. Does Schinzel say the two primes lie one in each Aurifeuillian factor?
- Unable to confirm. Every secondary source I read says only "at least two primitive divisors, obtained via an Aurifeuillian factorization". [SNIPPET/READ of secondaries]
- Wagstaff (INTEGERS 10 (2010), https://homes.cerias.purdue.edu/~ssw/cun/mine.pdf) [READ]: Aurifeuillian factorizations "cut across" the cyclotomic ones and may be used to show certain b^n +- 1 have at least two primitive prime factors; example 3^27+1 has primitive primes 19441 and 19927. [READ]
  Check by hand: for E=9, L_9 = 3^9 - 3^5 + 1 = 19683 - 243 + 1 = 19441; M_9 = 19683+243+1 = 19927. [INFERRED, own arithmetic] So each factor is itself the (prime) primitive factor here: a one-in-each instance, but a single example.
  Also Wagstaff says 3^(6k-3)+1 always has at least two primitive prime factors for k>1 (i.e. Phi_{6E}(3) composite for E odd >= 3). [SNIPPET, from search summary; I did not locate that exact sentence in the text I extracted.]
  The "at least two" conclusion is plausibly obtained precisely because each Aurifeuillian factor contributes one, but that is [INFERRED].

## 3. Other sources
- Pomerance, Cyclotomic primes, https://math.dartmouth.edu/~carlp/cyclotomicprimes17.1.pdf [READ]: for base 2, Phi_{8k+4}(2) = Phi+ * Phi- where Phi+/- = gcd(Phi_{8k+4}(2), 2^(2k+1) +- 2^(k+1) + 1)
  (after removing an intrinsic prime), and "this factorization is nontrivial for k >= 3, a result due to Schinzel [Proc. Camb. 58, 556-562]". Nontrivial means both parts > 1, i.e. each
  Aurifeuillian factor contains a primitive prime factor. This is the base-2 analogue of Statement H and is attributed to this very Schinzel paper. He also mentions a Schinzel problem on p. 561.
  Note the subtlety for Statement H: L_E*M_E = Phi_6(3^E) = product over d | E of Phi_{6d}(3), so L_E, M_E contain primitive primes of smaller d | E as well; H needs a prime of exact order 6E in EACH, which is the gcd-with-Phi_{6E}(3) version. Pomerance's statement is of that gcd form, for base 2. The base-3 version is not stated there. [INFERRED]
- Granville & Pleasants, Aurifeuillian factorization, Math. Comp. 75 (2006) 497-508, DOI 10.1090/S0025-5718-05-01766-7. AMS PDF returned HTTP 403; not read.
  Secondary: they show Schinzel found all Aurifeuillian identities (Wagstaff; Waterloo comments) [READ]; Allombert-Belabas Prop 1.1 [READ, https://www.numdam.org/item/10.5802/jtnb.641.pdf]: for squarefree a, a^{...} Phi_d(a) is a norm-square condition: a | d and (a = 1 mod 4, d odd) or (a = 3 mod 4, v2(d) = 1) or (a even, v2(d) = 2). For a=3, d=6E, E odd: 3 = 3 mod 4, v2 = 1, 3 | 6E: Aurifeuillian factorization exists. [INFERRED check, consistent with the hypothesis shape of your kappa/eta condition]
- Brent, On computing factors of cyclotomic polynomials, https://arxiv.org/pdf/1004.5466.pdf [READ]: identities (6)-(8); credits Schinzel for L_n(x) = C_n(x^2) - s x^n D_n(x^2). No primitive-factor statement found.
- Stewart 1977 (Fermat/Fibonacci/Lucas/Lehmer divisors) and Rotkiewicz 1962 (Lucas numbers with two intrinsic divisors, Bull. Acad. Polon. Sci. 10, 229-232): not opened. Rotkiewicz is said to extend Schinzel's argument to Lucas numbers [READ in Waterloo comments]. Brillhart et al. book: not opened.
- Schinzel's follow-ups on Lehmer numbers (Acta Arith. 8 (1963) 213-223, 251-257; Ark. Mat. 4 (1962) 413-416): not opened; candidates for the "at least two/ k primitive" statements.

## 4. Formalization
- Not searched adequately (the search budget went to 1-3). I did not find any claim of a Lean/Coq/Isabelle formalization of Schinzel's theorem. [UNVERIFIED; absence of evidence only]

## Bottom line
- Known? Very likely true and in the literature in spirit: Schinzel 1962 gives Aurifeuillian-based "at least two primitive factors", and Pomerance credits Schinzel with the nontriviality (both parts > 1) in base 2. For base 3, E odd >= 3, the numerical example E=9 fits. [INFERRED]
- Exact published statement, exception list, and "one in each factor" for base 3: not verified. Next step: obtain the paper (library / Sci-Hub-free route such as interlibrary loan), or read Granville-Pleasants via an accessible mirror, or ask Pomerance's source for the exact lemma.
