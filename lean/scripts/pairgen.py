# Generates the certificate of lean/Pilean/PiFormula/CheckedPair.lean: a search tree proving
# that the cost of a checked computation of pi with two formulas of the class F is at least 60
# per period of 120 (one term per bit).
#
#   python lean/scripts/pairgen.py
#
# It writes lean/Pilean/PiFormula/CheckedPair.lean itself: pair_head.lean, the certificate, and
# pair_tail.lean.  The certificate is found here and checked in Lean by a verified checker.
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


def size(node):
    if node[0] in ("done", "dead"):
        return 1
    if node[0] in ("brW", "brQ"):
        return 1 + size(node[2]) + size(node[3])
    return 1 + size(node[-1])


def emit_all(tree, w, stats):
    defs, counter = [], [0]

    def body(cs):
        return "[" + ", ".join("(%d, %d)" % zc for zc in cs) + "]"

    def emit(node, lines, top):
        kind = node[0]
        if kind == "done":
            lines.append("PCert.done")
        elif kind == "dead":
            lines.append("PCert.dead")
        elif kind == "zeroW":
            _, j, d, cs, rest = node
            lines.append("(PCert.zeroW %d %d %s" % (j, d, body(cs)))
            emit(rest, lines, False)
            lines[-1] += ")"
        elif kind in ("nzW", "nzQ"):
            _, j, tgt, d, cs, rest = node
            lines.append("(PCert.%s %d %d %d %s" % (kind, j, tgt, d, body(cs)))
            emit(rest, lines, False)
            lines[-1] += ")"
        else:
            _, i, t0, t1 = node
            if not top and size(node) > 40:
                counter[0] += 1
                name = "pcert%d" % counter[0]
                sub = []
                emit(node, sub, True)
                defs.append((name, sub))
                lines.append(name)
                return
            lines.append("(PCert.%s %d" % (kind, i))
            emit(t0, lines, False)
            emit(t1, lines, False)
            lines[-1] += ")"

    top = []
    emit(tree, top, True)
    defs.append(("pairCert", top))
    w("/-! ## 4. The certificate (generated by scripts/pairgen.py) -/\n\n")
    w("/-! %d nodes on the zero relation and %d on the formula, %d derived facts, in %d pieces.\n"
      "%d branches end in a single zero relation with fewer than 60 terms. -/\n\n"
      % (stats["wnodes"], stats["qnodes"], stats["derives"], len(defs), len(stats["exceptional"])))
    for name, lines in defs:
        if name == "pairCert":
            w("/-- The certificate that the cost of a checked pair is at least 60. -/\n")
        w("def %s : PCert :=\n" % name)
        for ln in lines:
            w(E.wrap("  " + ln, "", "    ", E.ITEMS).rstrip() + "\n")
        w("\n")


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
    out = io.StringIO()
    out.write(io.open(os.path.join(HERE, "pair_head.lean"), encoding="utf-8").read())
    emit_all(tree, out.write, stats)
    tail = io.open(os.path.join(HERE, "pair_tail.lean"), encoding="utf-8").read()
    assert tail.count("-- TAKAHASHI_TABLES\n") == 1
    out.write(tail.replace("-- TAKAHASHI_TABLES\n", takahashi_tables()))
    text = out.getvalue()
    assert "PCert.done" in text and "theorem pairCost_ge" in text
    dst = os.path.join(HERE, "..", "Pilean", "PiFormula", "CheckedPair.lean")
    with io.open(dst, "w", encoding="utf-8", newline="\n") as fh:
        fh.write(text)
    print("z-nodes %d, rho-nodes %d, derived facts %d, dead ends %d; %d lines; %.0f s"
          % (stats["wnodes"], stats["qnodes"], stats["derives"], stats["dead"],
             text.count("\n"), time.time() - t0))
    print("zero relations with fewer than %d terms (terms, zero classes):" % TARGET)
    for have, cl in sorted(stats["exceptional"]):
        print("   %d terms; %d classes vanish" % (have, len(cl)))
