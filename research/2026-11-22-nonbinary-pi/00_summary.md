# Is "no degree-1 BBP-type formula for pi outside powers of 2" in print? (22 November 2026)

**The statement (Theorem L).** Let b >= 2 be an integer that is not a power of 2. No series
sum_j b^(-Bj) sum_{i=1..N} a_i/(Nj+i) with rational a_i (Bailey's P(1, b^B, N, a)) is a
non-zero rational multiple of pi. It is proved in `lean/Pilean/BaseB/NoPi.lean`
(`no_pi_bailey`), so nothing below is needed for the mathematics. The question here is what
may be claimed about it.

One research helper, about 15 searches and 10 page reads, then a second pass on the 2004
paper. Its report is `01_literature.md`. The two key passages were then checked by us in the
extracted text of the two sources (marked *checked*).

## What was found

1. **Borwein, Borwein and Galway 2004** (Finding and excluding b-ary Machin-type individual
   digit formulae, Canad. J. Math. 56, 897-925) prove the statement for Machin-type formulas
   only: for b > 2 not a proper power, pi is not a rational combination of arctan(b^(-m))
   (Theorem 7). Tools: Bang's theorem (primitive prime divisors) and Gaussian primes. No
   transcendence theorem is used.
2. **The general case is posed there as a question** (*checked*). Comment (10) at the end of
   the paper writes L(1, b, n, j) through ln(1 - zeta^r b^(-1/n)) and asks whether their
   techniques can determine if pi is a linear combination of the L(1, b^m, n, j); it adds that
   this would probably need a good understanding of Q[zeta_n, b^(1/n)]. Comment (3) says the
   1995 formula does not appear to be a combination of Machin-type generators. Their Appendix
   B goes the other way (Machin-type formulas are of Bailey's form).
3. **Bailey's Compendium states the general result as known** (*checked*; version of
   8 April 2023, Introduction, page 2): the 2004 paper is said to have shown that there are
   no other degree-1 BBP-type formulas for pi except those whose base is a power of two. No
   restriction to Machin type is attached. Mendonca (arXiv:1209.2348) repeats it. MathWorld
   gives the Machin-type version.
4. **No proof of the general statement was found**, nor any use of Baker's theorem for
   BBP-type formulas, nor a later paper or erratum by the three authors.
5. **No counterexample was found.** Known formulas in other bases are for pi sqrt(3) (base 3),
   pi^2 (base 3, degree 2), or use non-integer bases; Euler's formula with (-1/4)^k is base 16.

## What this changes

- Theorem L should not be called a new statement: it is in the standard reference as a known
  fact. What we can say: the reference given for it proves a special case and asks the
  general question; we found no proof of the general statement in print; ours is a proof,
  and it is machine-checked. Theorem L answers Comment (10) of the 2004 paper.
- Theorem G (every b >= 5: no zero relation, no algebraic multiple of pi, formulas unique)
  was not found in any source read.
- Before a paper: search MathSciNet and zbMATH; read the 2004 Compendium version; ask the
  authors (D. Bailey maintains the Compendium) whether a proof of the general statement
  exists. Whether and how to write to them is the user's decision.
- "Not found" is weak evidence throughout.

Sources: see the URLs at the end of `01_literature.md`.
