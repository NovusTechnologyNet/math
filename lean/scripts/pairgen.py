# Generates the certificate of lean/Pilean/PiFormula/CheckedPair.lean: a search tree proving
# that the cost of a checked computation of pi with two formulas of the class F is at least 60
# per period of 120 (one term per bit).
#
#   python lean/scripts/pairgen.py
#
# It writes these files in lean/Pilean/PiFormula itself:
#   CheckedPairDefs.lean    pair_head.lean.in: the checker and its soundness;
#   CheckedPairCert<k>.lean the certificate, cut into closed pieces of at most PIECE nodes,
#                           each with the theorem that it passes the checker (`decide +kernel`);
#   CheckedPair.lean        the branches above the pieces, the proof that the whole tree
#                           passes, and pair_tail.lean.in (the bound, Takahashi's pair).
# Every file is a module of Lean's module system: `module`, public imports, and the body
# in `@[expose] public section` (the two fragments have these lines already).
# The certificate is found here and checked in Lean by a verified checker.
#
# Why pieces.  The kernel gives back the memory of a computation only when the declaration is
# finished: one `decide +kernel` on the whole tree (26,204 nodes) needs more than 22 GB.  A
# piece of 250 nodes needs about half a GB for a moment, and the PARTS files are compiled by
# separate Lean processes.
#
# The tree.  With z = rho1 - rho2 (a zero relation) and rho = rho1, the cost is
#     (positions where z has a term) + 2 (positions where rho has a term and z has none).
# First the tree branches on the 35 classes of positions for z: "class i vanishes or not".
# A branch is closed when the classes known not to vanish have weight >= 60.  Twelve branches
# end in a single zero relation with fewer than 60 terms; there the tree continues with rho,
# inside the zero set of z, until weight(z) + 2 weight(rho inside) >= 60.
# Every fact used on the way ("this class must vanish", "this class cannot vanish") comes with
# an integer linear identity, which is what Lean checks.
import io
import math
import os
import sys
import time
from fractions import Fraction as Fr

sys.setrecursionlimit(100000)
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
_argv = sys.argv
sys.argv = [_argv[0], "none"]          # egen runs nothing for this mode
import egen as E                        # noqa: E402
sys.argv = _argv

FV, SIZES, NC, QV = E.FV, E.SIZES, E.NC, E.QV
TARGET = 60
ORDER = sorted(range(NC), key=lambda i: (-SIZES[i], i))
VAL = 35                                # the index of the value form q0 + q2
_cw = {}


def vec(i):
    return QV if i == VAL else FV[i]


def clW(Z):
    """Closure of zero conditions on z, where the value form also vanishes; and the rank."""
    key = frozenset(Z)
    if key not in _cw:
        basis = E.add_vec((), QV)
        for i in sorted(key):
            basis = E.add_vec(basis, FV[i])
        cl = frozenset(i for i in range(NC) if E.in_span(basis, FV[i]))
        _cw[key] = _cw[cl] = (cl, len(basis))
    return _cw[key]


def wt(S):
    return sum(SIZES[i] for i in S)


def int_comb(target, idx):
    """Integers (d, c) with d * target = sum c_j * vec(idx_j), d > 0.  The vectors are linearly
    independent and the target lies in their span."""
    n = len(idx)
    A = [[vec(idx[j])[t] for j in range(n)] + [target[t]] for t in range(8)]
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
    d = 1
    for x in c:
        d = d * x.denominator // math.gcd(d, x.denominator)
    ci = [int(x * d) for x in c]
    assert all(d * target[t] == sum(ci[j] * vec(idx[j])[t] for j in range(n)) for t in range(8))
    return d, [(i, x) for i, x in zip(idx, ci) if x != 0]


# ------------------------------------------------------------------ the part on rho
def build_q(clw, base, Zq, Dq, stats):
    """A tree for: every pattern of non-zero value with classes Zq zero and Dq non-zero has
    base + 2 * (weight of its non-zero classes inside clw) >= TARGET."""
    cl, basis, feas = E.closure(Zq)
    assert feas and not (cl & set(Dq))
    known, order = set(Dq), []
    changed = True
    while changed:
        changed = False
        for j in ORDER:
            if j in cl or j in known:
                continue
            cl2, b2, feas2 = E.closure(set(cl) | {j})
            if not feas2:
                tgt = VAL
            else:
                hit = sorted(cl2 & known)
                if not hit:
                    continue
                tgt = hit[0]
            order.append((j, tgt))
            known.add(j)
            changed = True
    stats["qnodes"] += 1
    if base + 2 * wt(known & clw) >= TARGET:
        total = base + 2 * wt(set(Dq) & clw)
        steps, have = [], set(Dq)
        # a derived class may be needed as the target of a later one, so keep the order
        for j, tgt in order:
            if total >= TARGET:
                break
            d, cs = int_comb(vec(tgt), list(Zq) + [j])
            steps.append(("nzQ", j, tgt, d, cs))
            have.add(j)
            if j in clw:
                total += 2 * SIZES[j]
        assert total >= TARGET
        node = ("done",)
        for s in reversed(steps):
            node = s + (node,)
        stats["derives"] += len(steps)
        return node
    free = [i for i in ORDER if i in clw and i not in cl and i not in known]
    assert free, ("the bound fails", sorted(clw), base)
    i = free[0]
    return ("brQ", i, build_q(clw, base, list(Zq) + [i], Dq, stats),
            build_q(clw, base, Zq, list(Dq) + [i], stats))


# ------------------------------------------------------------------ the part on z
def build_w(Zw, Dw, stats):
    cl, rank = clW(Zw)
    stats["wnodes"] += 1
    if rank == 8:
        # every class vanishes: derive them all, then `dead`
        node = ("dead",)
        steps = []
        for j in range(NC):
            if j not in Zw:
                d, cs = int_comb(FV[j], [VAL] + list(Zw))
                steps.append(("zeroW", j, d, cs))
        for s in reversed(steps):
            node = s + (node,)
        stats["derives"] += len(steps)
        stats["dead"] += 1
        return node
    known, order = set(Dw), []
    if known:
        changed = True
        while changed:
            changed = False
            for j in ORDER:
                if j in cl or j in known:
                    continue
                hit = sorted(clW(set(cl) | {j})[0] & known)
                if hit:
                    order.append((j, hit[0]))
                    known.add(j)
                    changed = True
    have = wt(known)

    def derive_nz(limit):
        """Steps deriving forced classes until the weight of Dw reaches `limit`."""
        total, steps = wt(Dw), []
        for j, tgt in order:
            if total >= limit:
                break
            d, cs = int_comb(FV[tgt], [VAL] + list(Zw) + [j])
            steps.append(("nzW", j, tgt, d, cs))
            total += SIZES[j]
        return steps, total

    if have >= TARGET:
        steps, total = derive_nz(TARGET)
        assert total >= TARGET
        node = ("done",)
        for s in reversed(steps):
            node = s + (node,)
        stats["derives"] += len(steps)
        return node
    free = [i for i in ORDER if i not in cl and i not in known]
    if not free:
        # z is one zero relation with fewer than TARGET terms: continue with rho
        steps, total = derive_nz(10 ** 9)
        assert total == have
        zsteps = []
        for j in sorted(cl):
            if j not in Zw:
                d, cs = int_comb(FV[j], [VAL] + list(Zw))
                zsteps.append(("zeroW", j, d, cs))
        stats["exceptional"].append((have, sorted(cl)))
        node = build_q(cl, have, [], [], stats)
        for s in reversed(steps + zsteps):
            node = s + (node,)
        stats["derives"] += len(steps) + len(zsteps)
        return node
    # the class whose vanishing forces the most zeros
    i = max(free, key=lambda j: (wt(clW(set(cl) | {j})[0]), SIZES[j], -j))
    return ("brW", i, build_w(list(Zw) + [i], Dw, stats), build_w(Zw, list(Dw) + [i], stats))


PIECE = 250                             # a piece has at most this many nodes
PARTS = 6                               # the pieces are spread over this many files
OUT = os.path.join(HERE, "..", "Pilean", "PiFormula")


def size(node):
    if node[0] in ("done", "dead"):
        return 1
    if node[0] in ("brW", "brQ"):
        return 1 + size(node[2]) + size(node[3])
    return 1 + size(node[-1])


def emit_tree(node, lines):
    """The Lean term of a subtree, one node per line."""
    def body(cs):
        return "[" + ", ".join("(%d, %d)" % zc for zc in cs) + "]"

    kind = node[0]
    if kind == "done":
        lines.append("PCert.done")
    elif kind == "dead":
        lines.append("PCert.dead")
    elif kind == "zeroW":
        _, j, d, cs, rest = node
        lines.append("(PCert.zeroW %d %d %s" % (j, d, body(cs)))
        emit_tree(rest, lines)
        lines[-1] += ")"
    elif kind in ("nzW", "nzQ"):
        _, j, tgt, d, cs, rest = node
        lines.append("(PCert.%s %d %d %d %s" % (kind, j, tgt, d, body(cs)))
        emit_tree(rest, lines)
        lines[-1] += ")"
    else:
        _, i, t0, t1 = node
        lines.append("(PCert.%s %d" % (kind, i))
        emit_tree(t0, lines)
        emit_tree(t1, lines)
        lines[-1] += ")"


def cut(tree):
    """Cuts the tree into closed pieces of at most PIECE nodes: the largest subtrees of that
    size.  Returns the pieces (name, subtree, context), in the order of the tree, and the part
    of the tree above them twice: as a Lean term with the names of the pieces as leaves, and
    as the proof that this term passes the checker, with the theorems of the pieces as leaves.
    A context is (Zw, Dw, Zq, Dq), the four lists of `checkPair` at that place, as the checker
    builds them (newest entry first)."""
    pieces, term, proof = [], [], []

    def go(node, ctx, ind):
        if size(node) <= PIECE:
            name = "pcert%d" % (len(pieces) + 1)
            pieces.append((name, node, ctx))
            term.append(ind + name)
            proof.append(ind + name + "_ok")
            return
        kind = node[0]
        # above the pieces the proof has a lemma for the two kinds of branches only
        assert kind in ("brW", "brQ"), "a %s node above the pieces: raise PIECE" % kind
        _, i, t0, t1 = node
        Zw, Dw, Zq, Dq = ctx
        if kind == "brW":
            c0, c1 = ((i,) + Zw, Dw, Zq, Dq), (Zw, (i,) + Dw, Zq, Dq)
        else:
            c0, c1 = (Zw, Dw, (i,) + Zq, Dq), (Zw, Dw, Zq, (i,) + Dq)
        term.append("%s(PCert.%s %d" % (ind, kind, i))
        proof.append("%s(checkPair_%s_ok" % (ind, kind))
        go(t0, c0, ind + " ")
        go(t1, c1, ind + " ")
        term[-1] += ")"
        proof[-1] += ")"

    go(tree, ((), (), (), ()), "  ")
    return pieces, term, proof


def split_parts(pieces):
    """The pieces in PARTS groups of about the same number of nodes, in order."""
    total = sum(size(node) for _, node, _ in pieces)
    parts, done = [[] for _ in range(PARTS)], 0
    for p in pieces:
        parts[done * PARTS // total].append(p)
        done += size(p[1])
    assert all(parts)
    return parts


def part_text(k, part):
    """The file CheckedPairCert<k>.lean."""
    out = io.StringIO()
    w = out.write
    w("module\n\npublic import Pilean.PiFormula.CheckedPairDefs\n\n")
    w("/-!\n# The certificate of Theorem J, part %d of %d (generated by scripts/pairgen.py)\n\n"
      % (k, PARTS))
    w("The pieces `%s` to `%s` of the search tree of `CheckedPair.lean`: %d closed subtrees, of\n"
      "%d nodes together. After each piece comes the theorem that it passes the checker, a\n"
      "kernel computation of its own. The four lists in its statement are the classes that the\n"
      "checker has collected on the way from the root of the tree down to the piece.\n-/\n\n"
      % (part[0][0], part[-1][0], len(part), sum(size(node) for _, node, _ in part)))
    w("@[expose] public section\n\nnamespace PiFormula\n\n")
    for name, node, ctx in part:
        lines = []
        emit_tree(node, lines)
        w("def %s : PCert :=\n" % name)
        for ln in lines:
            w(E.wrap("  " + ln, "", "    ", E.ITEMS).rstrip() + "\n")
        w("\ntheorem %s_ok :\n" % name)
        lists = " ".join("[" + ", ".join(str(x) for x in c) + "]" for c in ctx)
        w(E.wrap("    checkPair %s %s = true := by" % (lists, name), "", "      ",
                 E.ITEMS).rstrip() + "\n")
        w("  decide +kernel\n\n")
    w("end PiFormula\n")
    return out.getvalue()


def top_text(tree, stats, pieces, term, proof):
    """The file CheckedPair.lean."""
    cert = io.StringIO()
    w = cert.write
    w("/-! ## 4. The certificate (generated by scripts/pairgen.py) -/\n\n")
    w("/-! %d nodes on the zero relation and %d on the formula, %d derived facts.\n"
      "%d branches end in a single zero relation with fewer than 60 terms.\n\n"
      % (stats["wnodes"], stats["qnodes"], stats["derives"], len(stats["exceptional"])))
    w("The tree has %d nodes. It is cut into %d closed pieces of at most %d nodes, `pcert1` to\n"
      "`pcert%d`, in the files `CheckedPairCert1.lean` to `CheckedPairCert%d.lean`, where the\n"
      "kernel checks each piece. Below are the %d branches above the pieces. -/\n\n"
      % (size(tree), len(pieces), PIECE, len(pieces), PARTS, len(pieces) - 1))
    w("/-- The certificate that the cost of a checked pair is at least 60. -/\n")
    w("def pairCert : PCert :=\n%s\n\n" % "\n".join(term))
    w("/-- The certificate passes the checker: every piece passes (kernel computations, in the\n"
      "files `CheckedPairCert*.lean`), and a branch passes if both sides do. -/\n")
    w("theorem pairCert_ok : checkPair [] [] [] [] pairCert = true :=\n%s\n" % "\n".join(proof))
    tail = io.open(os.path.join(HERE, "pair_tail.lean.in"), encoding="utf-8").read()
    assert tail.count("-- PAIR_CERT\n") == 1 and tail.count("-- TAKAHASHI_TABLES\n") == 1
    tail = tail.replace("-- PAIR_CERT\n", cert.getvalue())
    tail = tail.replace("-- TAKAHASHI_TABLES\n", takahashi_tables())
    imports = "".join("public import Pilean.PiFormula.CheckedPairCert%d\n" % k
                      for k in range(1, PARTS + 1))
    return "module\n\n" + imports + "\n" + tail


def lean_files(tree, stats):
    """All the files, as a list of (name, text)."""
    pieces, term, proof = cut(tree)
    assert len(term) == 2 * len(pieces) - 1
    head = io.open(os.path.join(HERE, "pair_head.lean.in"), encoding="utf-8").read()
    files = [("CheckedPairDefs.lean", head.rstrip("\n") + "\n\nend PiFormula\n")]
    for k, part in enumerate(split_parts(pieces), 1):
        files.append(("CheckedPairCert%d.lean" % k, part_text(k, part)))
    files.append(("CheckedPair.lean", top_text(tree, stats, pieces, term, proof)))
    # every node of the tree is written exactly once, in a piece or above the pieces
    assert sum(t.count("PCert.") for _, t in files[1:]) == size(tree)
    assert "theorem checkPair_sound" in files[0][1] and "theorem pairCost_ge" in files[-1][1]
    return files


# ------------------------------------------------------------------ Takahashi's formulas
# (m, j, sign, e): the term sign * 2^e * S(m, j), S(m, j) = sum_k (-1)^k / (2^(30k) (mk + j)).
TAK23 = [(12, 1, -1, -1), (12, 3, -1, -6), (12, 5, 1, -11), (12, 7, 1, -16), (12, 9, -1, -21),
         (12, 11, -1, -26), (30, 1, 1, 2), (30, 3, -1, 0), (30, 5, -1, -4), (30, 7, -1, -4),
         (30, 9, 1, -6), (30, 11, -1, -8), (30, 13, 1, -10), (30, 15, 1, -14),
         (30, 17, 1, -14), (30, 19, -1, -16), (30, 21, 1, -18), (30, 23, -1, -20),
         (30, 25, -1, -24), (30, 27, -1, -24), (30, 29, 1, -26)]
TAK26 = [(10, 5, 1, -14), (20, 1, 1, 0), (20, 3, 1, -3), (20, 5, -1, -6), (20, 7, -1, -9),
         (20, 9, 1, -12), (20, 11, 1, -15), (20, 13, -1, -18), (20, 15, -1, -21),
         (20, 17, 1, -24), (20, 19, 1, -27), (30, 1, 1, 1), (30, 3, 1, -2), (30, 5, 1, -3),
         (30, 7, -1, -5), (30, 9, -1, -8), (30, 11, -1, -9), (30, 13, 1, -11),
         (30, 15, -1, -13), (30, 17, 1, -15), (30, 19, -1, -17), (30, 21, -1, -20),
         (30, 23, -1, -21), (30, 25, 1, -23), (30, 27, 1, -26), (30, 29, 1, -27)]


def takahashi_numerators(terms):
    """a_1..a_120 of P(1, 2^60, 120, A), times 2^57: the two steps k = 2J, 2J + 1 of his
    series are one step of ours."""
    a = [Fr(0)] * 121
    for m, j, sign, e in terms:
        s = 60 // m
        c = sign * Fr(2) ** e * s
        a[s * j] += c
        a[s * j + 60] -= c / 2 ** 30
    nums = [x * 2 ** 57 for x in a[1:]]
    assert all(x.denominator == 1 for x in nums)
    return [int(x) for x in nums]


def takahashi_tables():
    out = io.StringIO()
    for name, terms, which in (("tak1Num", TAK23, "first"), ("tak2Num", TAK26, "second")):
        nums = takahashi_numerators(terms)
        out.write("/-- The coefficients of Takahashi's %s formula, times `2^57`. -/\n" % which)
        out.write("def %s : List ℤ :=\n" % name)
        out.write(E.wrap("  [" + ", ".join(str(x) for x in nums) + "]", "", "   ",
                         E.ITEMS).rstrip() + "\n\n")
    return out.getvalue().rstrip("\n") + "\n"


if __name__ == "__main__":
    t0 = time.time()
    stats = {"wnodes": 0, "qnodes": 0, "derives": 0, "dead": 0, "exceptional": []}
    tree = build_w([], [], stats)
    files = lean_files(tree, stats)
    for name, text in files:
        with io.open(os.path.join(OUT, name), "w", encoding="utf-8", newline="\n") as fh:
            fh.write(text)
    names = [name for name, _ in files]
    stale = [f for f in sorted(os.listdir(OUT))
             if f.startswith("CheckedPairCert") and f.endswith(".lean") and f not in names]
    print("z-nodes %d, rho-nodes %d, derived facts %d, dead ends %d; %d files, %d lines; %.0f s"
          % (stats["wnodes"], stats["qnodes"], stats["derives"], stats["dead"], len(files),
             sum(text.count("\n") for _, text in files), time.time() - t0))
    for f in stale:
        print("NOT written by this run, delete it: %s" % f)
    print("zero relations with fewer than %d terms (terms, zero classes):" % TARGET)
    for have, cl in sorted(stats["exceptional"]):
        print("   %d terms; %d classes vanish" % (have, len(cl)))
