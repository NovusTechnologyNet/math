# Is the lemma on Aurifeuillian factors in base 3 in print? (23 November 2026)

**The lemma.** For every odd E >= 3, each of 3^E - 3^((E+1)/2) + 1 and
3^E + 3^((E+1)/2) + 1 has a prime factor p with ord_p(3) = 6E. It is proved in
`lean/Pilean/Base3/Halves.lean` (`primitiveHalves3`), so nothing below is needed for the
mathematics. The question here is only how to cite it.

One research helper, about 20 searches and page reads. Its report is
`01_schinzel_aurifeuillian.md`. Statements are the helper's unless marked.

## What was found

1. **Schinzel's paper could not be read** (A. Schinzel, On primitive prime factors of
   a^n - b^n, Proc. Cambridge Philos. Soc. 58 (1962), 555-562; paywalled). Its exact
   theorem and its list of exceptions are not verified. Secondary sources describe it as:
   under a condition on a, b and n, a^n - b^n has at least two primitive prime factors,
   proved with an Aurifeuillian factorization. Two secondary summaries give the condition
   in different forms, and we could not reconcile them without the paper.
2. **"One prime in each Aurifeuillian factor"** is what our lemma says. No source read
   states it in that form for base 3. For base 2, Pomerance's notes on cyclotomic primes
   attribute to Schinzel's paper that the two parts of Phi_(8k+4)(2) are both non-trivial
   for k >= 3, which is the base-2 analogue (our Lemma 2).
3. **An example in print**: Wagstaff mentions that 3^27 + 1 has the primitive prime factors
   19441 and 19927. *Checked by us:* these are exactly the two Aurifeuillian factors for
   E = 9, and `python/base3_halves_check.py` prints them.
4. **Formalization**: none found, but the search for one was thin.

## What this changes

- In the note the lemma is stated with its proof, with the sentence that it is of the kind
  proved by Schinzel and that we do not claim it is new.
- Before a paper is submitted, Schinzel 1962 should be read (it was already on the list of
  papers to read for Lemma 2), to say precisely which case of his theorem this is.

Sources: see the URLs in `01_schinzel_aurifeuillian.md`.
