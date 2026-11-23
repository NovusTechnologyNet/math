# Schinzel 1962 (Proc. Camb. Phil. Soc. 58, 555-562): what could actually be read

Bottom line: the paper's own text could NOT be obtained. The "n/(eta*kappa) odd" form could not be confirmed in any readable source. What was read is consistent with the "square or twice a square" statement, but that is Stewart's one-line paraphrase of a corollary, not the main Aurifeuillian theorem.

## Route 1: the paper itself (failed)
- Cambridge page https://www.cambridge.org/core/journals/mathematical-proceedings-of-the-cambridge-philosophical-society/article/on-primitive-prime-factors-of-anbn/FF4F8CB4D5BEDD2854151670559F36C6 [READ, but only the preview]. It shows the first sentence only: a, b coprime with |a|>|b|>0, Phi_n the n-th cyclotomic polynomial. Full text is paywalled ("purchase temporarily unavailable"). It lists pp. 556-562 and the author's address as Trinity College, Cambridge.
- Selecta, EuDML, Polish libraries, Semantic Scholar, CORE, archive.org: no open copy turned up in the searches [SNIPPET: absence only]. I did not find a hit that I could fetch.
- The Waterloo "Comments for the Selecta of A. Schinzel" (Stewart) https://uwaterloo.ca/pure-mathematics/sites/default/files/uploads/documents/schinzel-report1_0.pdf [READ via local pdftotext]. It is only a commentary. It says Schinzel gave new Aurifeuillian factorizations and used them to give conditions under which a^n - b^n has at least two primitive divisors. It also says Granville-Pleasants show Schinzel found all such factorizations. It gives NO hypotheses.

## Route 2: quoting sources
1. Stewart, "On divisors of Lucas and Lehmer numbers", Acta Math. 211 (2013); arXiv https://arxiv.org/pdf/1008.1274 [READ, PDF text extracted locally].
   - Paraphrase of the statement: if a and b are coprime and ab is a square or twice a square, then the greatest prime factor of a^n - b^n is at least 2n+1.
   - Exclusion: n = 4, 6, 12 when a = 2, b = 1. This is the only exceptional list given, and it is the full list.
   - Method: Schinzel showed a^n - b^n has at least 2 primitive divisors, via an Aurifeuillian factorization of Phi_n.
   - It also recalls Schinzel's question: pairs with ab different from +-2c^2 and +-c^h (h >= 2).
   - No kappa, no eta, no condition on n/(eta*kappa).
2. Allombert-Belabas, "Practical Aurifeuillian factorization", J. Theor. Nombres Bordeaux 20 (2008), https://jtnb.centre-mersenne.org/item/10.5802/jtnb.641.pdf [READ, extracted locally]. This is not Schinzel's theorem. It is the Granville-Pleasants criterion (Prop. 1.1).
   - Let a* be the squarefree representative of a in Q*/(Q*)^2. Then Phi_d(a) has an Aurifeuillian factorization iff a* divides d and one of the following holds:
     - a* = 1 mod 4 and d odd;
     - a* = 3 mod 4 and v2(d) = 1;
     - a even and v2(d) = 2.
   - The paper says Phi_d(X) = U(X)^2 - c X V(X)^2 follows Schinzel's identity (reference [9]). It does not state the primitive-divisor theorem.
3. Brent, "On computing factors of cyclotomic polynomials" https://arxiv.org/pdf/1004.5466 [READ, extracted locally]. It gives the Aurifeuille-Le Lasseur-Lucas identities. Its worked example is Phi_5(x) = (x^2+3x+1)^2 - 5x(x+1)^2, which is the base-5 identity of case (ii). It cites Schinzel and Beeger for the more general identities. No primitive-divisor statement.
4. Wagstaff, "The search for Aurifeuillian-like factorizations", Integers 10 (2010), https://homes.cerias.purdue.edu/~ssw/cun/mine.pdf, and slides https://www.cs.purdue.edu/homes/ssw/aurif/mark.pdf [READ, extracted locally].
   - It says Aurifeuillian factorizations "may be used to show that certain b^n +- 1 have at least two primitive prime factors."
   - Example: 3^27+1 has the two primitive prime factors 19441 and 19927, the L and M parts of Phi_27(3). Here L = 3^9 - 3^5 + 1 and M = 3^9 + 3^5 + 1.
   - It states that 3^(6k-3)+1 = 3^(3(2k-1))+1 always has at least two primitive prime factors for k > 1.
   - It says Schinzel proved the existence of Aurifeuillian factorizations of a^n - b^n in many cases, and that Granville-Pleasants showed he found all of them. It says nothing about kappa or eta.
5. Wikipedia "Aurifeuillean factorization" https://en.wikipedia.org/wiki/Aurifeuillean_factorization [READ via fetch tool, which returns a summary, so not verbatim]. For b = s^2 t with t squarefree, there is an Aurifeuillian factorization iff t = 1 mod 4 and n = t mod 2t, or t = 2, 3 mod 4 and n = 2t mod 4t. Schinzel is not mentioned.
6. Wikipedia "Zsigmondy's theorem" https://en.wikipedia.org/wiki/Zsigmondy%27s_theorem [READ via fetch tool, summary]. It does not mention Schinzel or two primitive divisors.
7. Not obtained (blocked or no access):
   - Granville-Pleasants, Math. Comp. 75 (2006): AMS returned an anti-bot page and 403; ResearchGate 403; the andrew/PDF URL guess was 404.
   - Ribenboim, Stewart 1977, Bilu-Hanrot-Voutier, Rotkiewicz 1962 were not found open.
   - MathOverflow / Math StackExchange: searches found no answer stating the theorem.

## (a) Hypotheses and exceptions as read
The only statement actually read is Stewart's. Hypotheses: gcd(a,b) = 1 and ab is a square or twice a square. Conclusion: at least two primitive prime divisors, hence P >= 2n+1. Exceptions: (a,b,n) = (2,1,4), (2,1,6), (2,1,12) only. The kappa/eta form was NOT found in any source I could read.

## (b) Cases (i) and (ii)
- ab = 3 and ab = 5 are neither a square nor twice a square. So Stewart's stated hypothesis does NOT cover (i) or (ii) as written [READ].
- Case (i): Wagstaff states "at least two primitive prime factors" for 3^(3(2k-1))+1 with k > 1 [READ]. That is n = 3E with E odd, E > 1, which is the 3^(3E)+1 of case (i). It is a claim about primitive prime factors of 3^n+1 as a whole. It does not say each Aurifeuillian factor has one. The identity is 3^(3E)+1 = (3^E+1)(3^E - 3^((E+1)/2) + 1)(3^E + 3^((E+1)/2) + 1). The two trinomials are Aurifeuillian factors, but the sources do not say each holds a primitive prime. [INFERRED: Schinzel's actual theorem is presumably stated for Phi_n and so should cover this.]
- Case (ii): the identity Phi_5(x) = (x^2+3x+1)^2 - 5x(x+1)^2 is read [READ, Brent]. No source I read states a primitive-divisor conclusion for base 5, n = 5h. Granville-Pleasants' criterion for a* = 5 = 1 mod 4 requires d odd with 5 | d, which fits n = 5h with h odd [READ, Allombert-Belabas]. Whether Schinzel's theorem is stated for it is [INFERRED] only.
- Neither case: no source says every Aurifeuillian factor has a primitive prime factor. Only "at least two in total" appears.

## (c) Reconciling the two descriptions
- "ab square or twice a square" is Stewart's one-sentence paraphrase [READ]. It is a special case or corollary, and it is tied to the bound P >= 2n+1.
- The kappa/eta form could not be verified. It is plausible as the general Aurifeuillian hypothesis, since it resembles the Granville-Pleasants criterion [INFERRED], and it would cover b = 1 with a = 3 or 5 if the form is right. I could not confirm it.
- The two are not shown to be reconciled. They are probably different levels: Stewart quotes the special case for the 2n+1 bound, and the general theorem has a hypothesis in terms of the squarefree kernel of ab.
- To settle this you need the paper's pp. 556-562 (ILL or Selecta Vol. 1), or Granville-Pleasants.
