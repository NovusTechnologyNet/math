# Certificate generators for Part III

These scripts produced the generated parts of `Pilean/PiFormula/Relations.lean` and
`Pilean/PiFormula/VSeries.lean`. Run them with the system Python, with sympy and mpmath
installed.

| Script | Produces |
|---|---|
| `m1check.py` | checks the `ℤ[i]` model of the new formula against pi_formula_120.json (M1) |
| `relgen.py` | the 13 relations and their quotients modulo `Φ_20` / `Φ_24` (the body of `Relations.lean`) |
| `twgen.py` | the 24 certificates of the twisted power sum modulo `Φ_24` |
| `named.py` | the 8 named patterns (checked against decompose_formula.py), the 64 values at `k = 1..8`, and the inverse matrix used for independence |
| `rankgen.py` | section 6 of `Rank.lean` (M5): the 13 exponent vectors, each relation in exponent form, the values of a combination at the 13 pivot exponents, `relations_span` and `rel_independent`. It prints to standard output and needs no extra package |
| `argtable.py` | section 4 of `ExactArgs.lean` (M7): the three coefficient functions `alpha`, `beta`, `gam` and the 24 cases of `garg_table` |
| `logforms.py` | all of `LogForms.lean` (M7): the 78 exact logarithmic forms and the six `conjlog_b`. It prints to standard output; the rational multiples it writes are recomputed by Lean |
| `baileygen.py` | sections 2 and 3 of `TheoremD.lean` (M8): the values of a combination of the eight named patterns at 29 positions, and the certificates `coords_p8`, `coords_p12`, `coords_p24`, `coords_p40`, `coords_p60`, `coords_even`, `coords_D`, `coords_Dall`. It prints to standard output; `TheoremD.lean` is `thmD_head.lean.in`, this output and `thmD_tail.lean.in`, concatenated |
| `fivegen.py` | M7 part 3. `python fivegen.py series`: section 3 of `FiveSeries.lean` (the five tables, the power sums and one certificate per residue, modulo `Φ_24` or `Φ_20`); the file is `five_head.lean.in`, this output and `five_tail.lean.in`. `python fivegen.py indep`: section 2 of `TheoremC3.lean` (values of the thirteen patterns, the inverse matrix, `coords13_D`); the file is `c3_head.lean.in`, this output and `c3_tail.lean.in` |
| `egen.py` | Theorem E. `python egen.py classes`: the tables of `Classes.lean` (with `classes_head.lean.in`, `classes_tail.lean.in`). `python egen.py prime`: section 2 of `PrimeMeasure.lean`, the values on the four chains and 17 linear facts (with `prime_head.lean.in`, `prime_tail.lean.in`). `python egen.py terms`: the certificate of `FewestTerms.lean`, a branch-and-bound tree with an integer identity for every derived fact (with `terms_head.lean.in`, `terms_tail.lean.in`) |
| `assemble.py` | glues `vseries_head.lean.in`, `vseries_tail.lean.in` and the generated parts into `VSeries.lean` |
| `pairgen.py` | Theorem J. Writes `CheckedPairDefs.lean` (`pair_head.lean.in`: the checker and its soundness), `CheckedPairCert1.lean` to `CheckedPairCert6.lean` (the certificate: a search tree on the zero relation and then on the formula, with an integer identity for every derived fact, cut into closed pieces of at most 250 nodes, each followed by the theorem that it passes the checker), and `CheckedPair.lean` (the branches above the pieces, the proof that the whole tree passes, Takahashi's coefficient tables, and `pair_tail.lean.in`). The kernel checks one piece at a time, so no file needs more than about 4 GB of memory; one `decide +kernel` on the whole tree needed more than 22 GB. `PIECE` and `PARTS` in the script set the size of a piece and the number of files. About three minutes |
| `unconditional_gen.py` | `Unconditional.lean` and `UnconditionalPair.lean`: each main theorem of Part III with `(hB : BakerTheorem)` removed, proved by applying the original to `bakerTheorem`. The theorems of `CheckedPair.lean` go to `UnconditionalPair.lean`, so that `All.lean` and `Unconditional.lean`, which most of the library imports, do not depend on the certificate of Theorem J |

`relgen.py`, `twgen.py` and `named.py` write intermediate files to `scripts/generated/`
(not in git), which `assemble.py` reads. Lean checks the certificates; the scripts only find them.

## Fragments and the module system

The files `*_head.lean.in` and `*_tail.lean.in` are pieces of Lean files, not Lean files: a
generated file is a head, the output of its script and a tail, concatenated. They have the
extension `.lean.in` so that every file ending in `.lean` in the repository is a complete
module.

Every Lean file of the library uses Lean's module system: it starts with `module`, its imports
are `public import`, and its body is in `@[expose] public section`. The head fragments have
these lines, and so do the scripts that write whole files (`pairgen.py`,
`unconditional_gen.py`, `logforms.py`, and `python/compendium_lean.py`,
`python/ratbase_size_tables.py`, `python/fewest_terms_unique_cert.py` at the top of the
repository). The same places carry the copyright header that every file of the project opens
with.

Two generated files were edited by hand afterwards and will not come out of their scripts
unchanged: in `Relations.lean` and `VSeries.lean` the lines longer than 100 characters were
rewrapped (24 November 2026), and `VSeries.lean` already differed from the output of
`assemble.py` before that.
