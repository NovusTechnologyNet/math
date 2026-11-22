# Generates lean/Pilean/PiFormula/Unconditional.lean: the main theorems of Part III with the
# hypothesis `BakerTheorem` discharged by the formal proof of Baker's theorem in lean/Baker.
#
#   python lean/scripts/unconditional_gen.py
#
# It writes lean/Pilean/PiFormula/Unconditional.lean itself, and only after every statement
# has been found, so a failure cannot leave an empty file behind.
#
# Each statement is copied from its source file with `(hB : BakerTheorem)` removed, so the
# file can be read on its own; each proof is the original theorem applied to `bakerTheorem`.
import io
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(HERE, "..", "Pilean", "PiFormula")

# (file, theorem, one-line description)
ITEMS = [
    ("TheoremC2", "finrank_ratSpace",
     "**Theorem C, rational case.** The patterns of period `N` (`120 ∣ N`) whose series is a\n"
     "rational multiple of `π` form a space of dimension exactly 8."),
    ("TheoremC3", "finrank_algSpace",
     "**Theorem C, algebraic case.** The patterns whose series is an algebraic multiple of `π`\n"
     "form a space of dimension exactly 13."),
    ("TheoremC3", "theoremC", "**Theorem C.** Both dimensions together."),
    ("TheoremD", "value_formula",
     "**The value formula.** The value of a series of the 8-dimensional space, from six of its\n"
     "coefficients."),
    ("SharpD", "theoremD_sharp",
     "**Theorem D, sharp form.** A pattern with no term at any `k` with `gcd(k, 120) < 4` whose\n"
     "series is a rational multiple of `π` is a multiple of one fixed zero relation."),
    ("TheoremDAlg", "theoremD_alg_sharp",
     "**Theorem D for algebraic multiples of `π`**, sharp form."),
    ("BaileySums", "bailey_count_F2",
     "**Bailey's table, family `n = 2B`.** The number of independent zero relations of\n"
     "`P(1, 2^B, 2B, ·)`, for every `B`."),
    ("BaileySums", "bailey_count_F1",
     "**Bailey's table, family `n = B`.** The number of independent zero relations of\n"
     "`P(1, 2^B, B, ·)`, for every `B`."),
    ("BaileySums", "bailey_table", "**Bailey's table**, the 27 rows of degree 1 in base `2^B`."),
    ("TheoremE", "theoremE",
     "**Theorem E.** A formula for a non-zero rational multiple of `π` has at least 40 non-zero\n"
     "coefficients per 120 (2/3 of a term per bit) and prime cost at least 7/24."),
    ("Log23", "no_log23",
     "**Theorem G.** No series of the class F is a non-zero algebraic multiple of `log 23`."),
    ("Log23", "bailey_no_log23_F2", "**Theorem G** for `P(1, 2^B, 2B, A)`, every `B ≥ 1`."),
    ("Log23", "bailey_no_log23_F1", "**Theorem G** for `P(1, 2^B, B, A)`, every `B ≥ 1`."),
    ("LogPrimes", "not_isFValue_log_of_mem",
     "**Ten primes with no formula.** For `ℓ = 23, 47, 53, 59, 67, 71, 79, 83, 89, 97`, `log ℓ`\n"
     "is not a value of the class F."),
    ("LogYes", "log_primes_below_100",
     "**Theorem H.** For a prime `p < 100`, `log p` is a value of the class F if and only if\n"
     "`p` is one of `2, 3, 5, 7, 11, 13, 17, 19, 29, 31, 37, 41, 43, 61, 73`."),
    ("Arctan", "no_arctan_two_sevenths",
     "**Theorem I.** No series of the class F is a non-zero algebraic multiple of\n"
     "`arctan (2/7)`."),
    ("Arctan", "not_isFValue_arctan_two_sevenths",
     "**Theorem I.** `arctan (2/7)` is not a value of the class F."),
    ("Arctan", "not_isFValue_arctan_five_eighths",
     "`arctan (5/8)` is not a value of the class F."),
    ("Arctan", "not_isFValue_arctan_four_ninths",
     "`arctan (4/9)` is not a value of the class F."),
    ("Arctan", "bailey_no_arctan_two_sevenths_F2",
     "**Theorem I** for `P(1, 2^B, 2B, A)`, every `B ≥ 1`."),
    ("Arctan", "bailey_no_arctan_two_sevenths_F1",
     "**Theorem I** for `P(1, 2^B, B, A)`, every `B ≥ 1`."),
]

OPEN = {"(": ")", "{": "}", "[": "]", "⟨": "⟩"}
CLOSE = set(OPEN.values())


def signature(fname, name):
    """The text between `theorem name` and its `:=`, split into binders and statement."""
    s = io.open(os.path.join(SRC, fname + ".lean"), encoding="utf-8").read()
    key = "theorem %s (hB : BakerTheorem)" % name
    assert s.count(key) == 1, (fname, name, s.count(key))
    a = s.index(key) + len("theorem %s" % name)
    b = s.index(":=", a)
    sig = s[a:b].rstrip()
    assert sig.startswith(" (hB : BakerTheorem)")
    sig = sig[len(" (hB : BakerTheorem)"):]
    # the first colon outside all brackets separates the binders from the statement
    depth = 0
    for i, ch in enumerate(sig):
        if ch in OPEN:
            depth += 1
        elif ch in CLOSE:
            depth -= 1
        elif ch == ":" and depth == 0:
            return sig[:i], sig[i + 1:]
    raise ValueError(name)


def explicit_names(binders):
    """Names of the explicit `( ... : ...)` binders, in order."""
    names, depth, start = [], 0, None
    for i, ch in enumerate(binders):
        if ch in OPEN:
            if depth == 0:
                start = (i, ch)
            depth += 1
        elif ch in CLOSE:
            depth -= 1
            if depth == 0 and start[1] == "(":
                group = binders[start[0] + 1:i]
                names += group.split(":")[0].split()
    return names


out = io.StringIO()
w = out.write
w("""import Pilean.PiFormula.All
import Baker.Basic

/-!
# The main theorems, without a hypothesis

Part III proves its theorems from `BakerTheorem : Prop`, Baker's theorem on linear forms in
logarithms stated as a hypothesis. `Baker/` holds a formal proof of Baker's theorem
(`Transcendental.baker`, by Michail Karatarakis, Apache License 2.0; see `Baker/README.md`).
`bakerTheorem` below feeds it through `bakerTheorem_of_linearIndependent`, and the rest of
the file restates the main theorems with the hypothesis removed.

This file is generated by `scripts/unconditional_gen.py`: each statement is the original
with `(hB : BakerTheorem)` deleted, and each proof is the original applied to `bakerTheorem`.
-/

open Complex

namespace PiFormula

/-- **Baker's theorem**, in the form used throughout Part III. -/
theorem bakerTheorem : BakerTheorem :=
  bakerTheorem_of_linearIndependent fun hl hli _ _ hβ₀ hβ hrel =>
    Transcendental.baker hl hli hβ₀ hβ hrel

namespace Unconditional
""")
for fname, name, doc in ITEMS:
    binders, stmt = signature(fname, name)
    binders = binders.rstrip()
    args = "".join(" " + n for n in explicit_names(binders))
    w("\n/-- %s -/\n" % doc)
    w("theorem %s%s :%s :=\n" % (name, binders, stmt))
    w("  _root_.PiFormula.%s bakerTheorem%s\n" % (name, args))
w("\nend Unconditional\n\nend PiFormula\n")
text = out.getvalue()
assert sum(1 for line in text.splitlines() if line.startswith("theorem ")) == len(ITEMS) + 1
with io.open(os.path.join(SRC, "Unconditional.lean"), "w", encoding="utf-8", newline="\n") as fh:
    fh.write(text)
print("wrote Unconditional.lean: %d theorems" % (len(ITEMS) + 1))
