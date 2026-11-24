# Generates lean/Pilean/PiFormula/FewestTermsUniqueCert.lean: the certificate for
#
#   a pattern of the 8-dimensional space V with non-zero value has at least 41 non-zero
#   entries per period of 120, unless its coordinates lie on one of two lines
#
# (Theorem E, standard measure: the optimum 2/3 is attained only by Huvent's two formulas).
#
#   python fewest_terms_unique_cert.py            writes the Lean file (a few minutes)
#   python fewest_terms_unique_cert.py --check    also runs the exhaustive search (section 3)
#
# The 119 conditions "rho(k) = 0" on V fall into 35 classes of proportional linear forms in
# the coordinates q (the tables of lean/Pilean/PiFormula/Classes.lean, read from that file).
# The certificate is a case tree on "class i vanishes / does not vanish":
#   * a `derive` node records that a class cannot vanish, with an integer identity: if it
#     vanished, with the classes assumed to vanish, then the value q0 + q2 or a class known
#     to be non-zero would vanish;
#   * a `done` leaf: the classes known to be non-zero cover at least 41 positions;
#   * a `huv` leaf: seven independent classes vanish, and they cut out one of Huvent's lines.
# Lean checks the tree with a verified checker (FewestTermsUnique.lean). Everything here is
# exact rational arithmetic; the tree is checked again in Python before it is written.
import io
import math
import os
import re
import sys
from fractions import Fraction as Fr

sys.setrecursionlimit(100000)
HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.join(HERE, "..", "lean", "Pilean", "PiFormula")


# ------------------------------------------------------------------ 1. the 35 classes
def _table(name, text):
    return re.search(r"def %s : [^\n]*:=\s*(\[.*?\])\s*\n\n" % name, text, re.S).group(1)


_text = open(os.path.join(LEAN, "Classes.lean"), encoding="utf-8").read()
CLS = eval(_table("clsIdxTab", _text))       # class of the condition rho(k) = 0, k < 120
VECS = eval(_table("vecTab", _text))         # integer vector of each class
NC = 35
assert len(CLS) == 120 and len(VECS) == NC and CLS[0] == 35
assert all(len(v) == 8 for v in VECS) and sorted(set(CLS[1:])) == list(range(NC))
SIZES = [CLS.count(i) for i in range(NC)]    # number of positions of each class
VAL = [1, 0, 1, 0, 0, 0, 0, 0]               # the value q0 + q2, in units of pi/4
FV = [[Fr(x) for x in v] for v in VECS]
FVAL = [Fr(x) for x in VAL]
HUV = [[2, -2, 0, -2, 0, 0, 1, 0],           # coordinates of rhoHuvent1, divided by 256
       [-2, 2, 0, -2, 0, 0, 1, 0]]           # coordinates of rhoHuvent2, divided by -512
NEED = 41
ORDER = sorted(range(NC), key=lambda i: (-SIZES[i], i))


# ------------------------------------------------------------------ 2. exact linear algebra
def reduce_vec(basis, v):
    v = list(v)
    for piv, r in basis:
        if v[piv] != 0:
            f = v[piv]
            v = [a - f * b for a, b in zip(v, r)]
    return v


def add_vec(basis, v):
    w = reduce_vec(basis, v)
    piv = next((i for i, x in enumerate(w) if x != 0), None)
    if piv is None:
        return basis
    w = [x / w[piv] for x in w]
    nb = []
    for p, r in basis:
        if r[piv] != 0:
            f = r[piv]
            r = tuple(a - f * b for a, b in zip(r, w))
        nb.append((p, r))
    nb.append((piv, tuple(w)))
    return tuple(nb)


def in_span(basis, v):
    return all(x == 0 for x in reduce_vec(basis, v))


_cache = {}


def closure(Z):
    """(the classes in the span of Z, a reduced basis of the span, value not in the span?)"""
    key = frozenset(Z)
    if key not in _cache:
        basis = ()
        for i in sorted(key):
            basis = add_vec(basis, FV[i])
        cl = frozenset(i for i in range(NC) if in_span(basis, FV[i]))
        _cache[key] = _cache[cl] = (cl, basis, not in_span(basis, FVAL))
    return _cache[key]


def weight(S):
    return sum(SIZES[i] for i in S)


def combination(target, idx):
    """Rationals c with target = sum c_i * VECS[idx_i]; the vectors are independent."""
    n = len(idx)
    A = [[FV[idx[j]][t] for j in range(n)] + [Fr(target[t])] for t in range(8)]
    r = 0
    for col in range(n):
        p = next((i for i in range(r, 8) if A[i][col] != 0), None)
        assert p is not None
        A[r], A[p] = A[p], A[r]
        inv = 1 / A[r][col]
        A[r] = [x * inv for x in A[r]]
        for i in range(8):
            if i != r and A[i][col] != 0:
                f = A[i][col]
                A[i] = [a - f * b for a, b in zip(A[i], A[r])]
        r += 1
    assert all(A[i][n] == 0 for i in range(r, 8))
    c = [A[i][n] for i in range(n)]
    assert all(Fr(target[t]) == sum(c[j] * FV[idx[j]][t] for j in range(n)) for t in range(8))
    return c


def lcm_den(xs):
    d = 1
    for x in xs:
        d = d * x.denominator // math.gcd(d, x.denominator)
    return d


# ------------------------------------------------------------------ 3. the exhaustive search
def exhaustive(target=79):
    """All sets of classes that are the zero set of a pattern with non-zero value and have at
    least `target` zero positions among k = 1, ..., 119. Plain search (class by class, in or
    out), independent of the tree below."""
    found = []

    def search(cl, excl, start):
        rest = [i for i in range(start, NC) if i not in cl and i not in excl]
        if weight(cl) + weight(rest) < target:
            return
        if not rest:
            found.append(cl)
            return
        i = rest[0]
        cl2, _, feas = closure(set(cl) | {i})
        if feas and not (cl2 & excl):
            search(cl2, excl, i + 1)
        search(cl, excl | {i}, i + 1)

    search(closure(set())[0], frozenset(), 0)
    return found


def zero_set(q):
    return frozenset(i for i in range(NC) if sum(VECS[i][t] * q[t] for t in range(8)) == 0)


HZ = [zero_set(h) for h in HUV]              # the zero sets of Huvent's two patterns
assert all(weight(z) == 79 and len(closure(z)[1]) == 7 and closure(z)[2] for z in HZ)


# ------------------------------------------------------------------ 4. the tree
def new_facts(cl, known):
    """The classes that cannot vanish when those of cl vanish and those of `known` do not,
    as steps (j, target): if j vanished, the target would (35 stands for the value)."""
    known, steps = set(known), []
    changed = True
    while changed:
        changed = False
        for j in ORDER:
            if j in cl or j in known:
                continue
            cl2, _, feas2 = closure(set(cl) | {j})
            if not feas2:
                tgt = 35
            else:
                hit = sorted(cl2 & known)
                if not hit:
                    continue
                tgt = hit[0]
            steps.append((j, tgt))
            known.add(j)
            changed = True
    return known, steps


def choose(cl, known, free):
    """The class to branch on: the one whose two branches both learn the most."""
    base = weight(known)

    def score(i):
        a = weight(new_facts(cl, known | {i})[0]) - base
        b = weight(new_facts(closure(set(cl) | {i})[0], known)[0]) - base
        return (min(a, b), a + b, -i)

    return max(free, key=score)


HUV_PATHS = [[], []]                       # the zero classes on the way to each `huv` leaf


def build(Zpath, known_in):
    """The tree below the node where the classes of Zpath (independent) vanish and those of
    known_in do not. Every fact is recorded at the first node where it holds."""
    cl, basis, feas = closure(Zpath)
    assert feas and not (cl & known_in) and len(basis) == len(Zpath)
    known, steps = new_facts(cl, known_in)
    if weight(known) >= NEED:
        node = ["done"]
    elif len(basis) == 7:
        assert cl in HZ                      # the only vertices with 79 zeros
        node = ["huv", HZ.index(cl)]
        HUV_PATHS[HZ.index(cl)].append(list(Zpath))
        steps = []
    else:
        free = [i for i in range(NC) if i not in cl and i not in known]
        i = choose(cl, known, free)
        node = ["branch", i, build(Zpath + [i], known), build(Zpath, known | {i})]
    for j, tgt in reversed(steps):
        idx = list(Zpath) + [j]
        c = combination(VAL if tgt == 35 else VECS[tgt], idx)
        d = lcm_den(c)
        cs = [(z, int(x * d)) for z, x in zip(idx, c) if x != 0]
        node = ["derive", j, tgt, d, cs, node]
    return node



# ------------------------------------------------------------------ 5. the checker, in Python
def vecz(i, t):
    return VECS[i][t] if i < NC else 0


def tgtvec(tgt, t):
    return VAL[t] if tgt == 35 else vecz(tgt, t)


def check(Z, D, node, huvs):
    """The function `checkU` of the Lean file."""
    while node[0] == "derive":
        _, j, tgt, d, cs, rest = node
        if not (d != 0 and (tgt == 35 or tgt in D) and all(z == j or z in Z for z, _ in cs)
                and all(d * tgtvec(tgt, t) == sum(c * vecz(z, t) for z, c in cs)
                        for t in range(8))):
            return False
        D = [j] + D
        node = rest
    if node[0] == "done":
        return NEED <= sum(1 for i in CLS if i in D)
    if node[0] == "huv":
        return all(z in Z for z in huvs[node[1]])
    _, i, t0, t1 = node
    return check([i] + Z, D, t0, huvs) and check(Z, [i] + D, t1, huvs)


def prune(Z, D, node, huvs):
    """Remove the facts that no leaf below needs, deepest first."""
    if node[0] == "branch":
        node[2] = prune([node[1]] + Z, D, node[2], huvs)
        node[3] = prune(Z, [node[1]] + D, node[3], huvs)
    elif node[0] == "derive":
        node[5] = prune(Z, [node[1]] + D, node[5], huvs)
        if check(Z, D, node[5], huvs):
            return node[5]
    return node


def count(node, st):
    while node[0] == "derive":
        st["derive"] += 1
        node = node[5]
    st[node[0]] += 1
    if node[0] == "branch":
        count(node[2], st)
        count(node[3], st)
    return st


# ------------------------------------------------------------------ 6. output
def wrap(text, indent, width=100):
    """Break a line after ", " so that no line is longer than `width`."""
    out, cur = [], ""
    for tok in re.split(r"(?<=, )", text):
        if len((cur + tok).rstrip()) > width and cur.strip():
            out.append(cur.rstrip())
            cur = indent + tok
        else:
            cur += tok
    out.append(cur.rstrip())
    return out


def size(node):
    n = 0
    while node[0] == "derive":
        n += 1
        node = node[5]
    if node[0] == "branch":
        return n + 1 + size(node[2]) + size(node[3])
    return n + 1


def emit_tree(tree):
    """The Lean terms: (name, lines), large subtrees as definitions of their own."""
    defs, counter = [], [0]

    def emit(node, lines, top):
        if node[0] == "done":
            lines.append("UCert.done")
        elif node[0] == "huv":
            lines.append("(UCert.huv %s)" % ("true" if node[1] else "false"))
        elif node[0] == "derive":
            _, j, tgt, d, cs, rest = node
            body = "[" + ", ".join("(%d, %d)" % zc for zc in cs) + "]"
            lines.append("(UCert.derive %d %d %d %s" % (j, tgt, d, body))
            emit(rest, lines, False)
            lines[-1] += ")"
        else:
            _, i, t0, t1 = node
            if not top and size(node) > 25:
                counter[0] += 1
                name = "ucert%d" % counter[0]
                sub = []
                emit(node, sub, True)
                defs.append((name, sub))
                lines.append(name)
                return
            lines.append("(UCert.branch %d" % i)
            emit(t0, lines, False)
            emit(t1, lines, False)
            lines[-1] += ")"

    top = []
    emit(tree, top, True)
    defs.append(("theUCert", top))
    return defs


HEADER = r"""module

public import Pilean.PiFormula.FewestTerms

/-!
# The certificate for the uniqueness of Huvent's two formulas

`FewestTerms.lean` proves that a pattern of the 8-dimensional space `V` with non-zero value
has at least 40 non-zero entries per period. This file holds the data for the next step: such
a pattern has at least 41 non-zero entries, unless seven classes vanish that cut out one of
two lines of `V`. The checker is proved sound in `FewestTermsUnique.lean`, where the two lines
are identified with Huvent's two formulas.

A certificate (`UCert`) is a tree, as in `FewestTerms.lean`:

* a `branch` node splits on "class `i` vanishes or not";
* a `derive` node proves that a class cannot vanish, from an integer linear identity (if it
  vanished, with the classes already assumed to vanish, then the value or a class known to be
  non-zero would vanish); here it may stand at any node, so that a fact is proved once for
  all the leaves below it;
* a `done` leaf counts the positions whose class is known to be non-zero, and needs at least
  41;
* a `huv` leaf closes a node at which the seven classes of `huvS1` (or of `huvS2`) vanish.

The certificate (section 2) is generated by python/fewest_terms_unique_cert.py and checked by
`decide +kernel`. With `--check` the same script also runs an exhaustive exact search that does
not use the tree: among the patterns with non-zero value exactly two zero sets have 79 zeros or
more, those of Huvent's two patterns.
-/

@[expose] public section

namespace PiFormula

/-! ## 1. Certificates and the checker -/

/-- A certificate tree for "at least 41 non-zero entries, or on one of Huvent's two lines". -/
inductive UCert where
  | done : UCert
  | huv (second : Bool) : UCert
  | derive (j tgt : ℕ) (d : ℤ) (cs : List (ℕ × ℤ)) (rest : UCert) : UCert
  | branch (i : ℕ) (zero nz : UCert) : UCert

"""

CHECKER = r"""/-- The checker. `Z` lists the classes assumed to vanish, `D` those known not to vanish. -/
def checkU : List ℕ → List ℕ → UCert → Bool
  | _, D, .done => decide (41 ≤ clsIdxTab.countP fun i => D.contains i)
  | Z, _, .huv second => (bif second then huvS2 else huvS1).all fun z => Z.contains z
  | Z, D, .derive j tgt d cs rest =>
      (d != 0) && (tgt == 35 || D.contains tgt) && (cs.all fun p => p.1 == j || Z.contains p.1)
        && certEq tgt d cs && checkU Z (j :: D) rest
  | Z, D, .branch i t0 t1 => checkU (i :: Z) D t0 && checkU Z (i :: D) t1

"""

FOOTER = r"""/-- The certificate passes the checker (kernel computation). -/
theorem theUCert_ok : checkU [] [] theUCert = true := by decide +kernel

end PiFormula
"""


def main():
    if "--check" in sys.argv:
        found = exhaustive(79)
        assert sorted(map(sorted, found)) == sorted(map(sorted, HZ)), found
        print("exhaustive search: exactly two zero sets with at least 79 zeros and non-zero "
              "value, those of Huvent's two patterns")
    tree = build([], set())
    assert all(len(p) == 1 for p in HUV_PATHS), HUV_PATHS     # each line is reached once
    huvs = [p[0] for p in HUV_PATHS]
    for w in (0, 1):                         # the seven classes cut out the line
        assert len(huvs[w]) == 7 and len(closure(huvs[w])[1]) == 7
        assert all(sum(VECS[z][t] * HUV[w][t] for t in range(8)) == 0 for z in huvs[w])
    assert check([], [], tree, huvs)
    before = count(tree, {"branch": 0, "done": 0, "derive": 0, "huv": 0})
    tree = prune([], [], tree, huvs)
    assert check([], [], tree, huvs)
    st = count(tree, {"branch": 0, "done": 0, "derive": 0, "huv": 0})
    defs = emit_tree(tree)
    out = io.StringIO()
    out.write(HEADER)
    out.write("/-- Seven classes that vanish together only on Huvent's first line. -/\n")
    out.write("def huvS1 : List ℕ := %s\n\n" % huvs[0])
    out.write("/-- Seven classes that vanish together only on Huvent's second line. -/\n")
    out.write("def huvS2 : List ℕ := %s\n\n" % huvs[1])
    out.write(CHECKER)
    out.write("/-! ## 2. The certificate (generated by python/fewest_terms_unique_cert.py) -/\n\n")
    out.write("/-! %d branch nodes, %d derived facts, %d `done` leaves and %d `huv` leaves, in %d "
              "pieces. -/\n\n" % (st["branch"], st["derive"], st["done"], st["huv"], len(defs)))
    for name, lines in defs:
        if name == "theUCert":
            out.write("/-- The certificate: at least 41 entries per period are non-zero, or the "
                      "pattern is on\none of Huvent's two lines. -/\n")
        out.write("def %s : UCert :=\n" % name)
        for ln in lines:
            out.write("\n".join(wrap("  " + ln, "    ")) + "\n")
        out.write("\n")
    out.write(FOOTER)
    text = out.getvalue()
    bad = [ln for ln in text.split("\n") if len(ln) > 100]
    assert not bad, bad[:3]
    target = os.path.join(LEAN, "FewestTermsUniqueCert.lean")
    with open(target, "w", encoding="utf-8", newline="\n") as f:
        f.write(text)
    print("facts before pruning: %d" % before["derive"])
    print("written %s: %s, %d pieces, %d lines"
          % (os.path.normpath(target), st, len(defs), text.count("\n")))


if __name__ == "__main__":
    main()
