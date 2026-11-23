"""Check the ledger of Bailey's "Compendium of BBP-Type Formulas" (version of 8 April 2023).

    python compendium_check.py [--write] [--dps N] [--lll] [--only ID[,ID...]]

Reads  literature/bailey-compendium/ledger.json  (one entry per numbered formula, table row,
list entry and prose assertion of the paper; the transcription is the ledger's, this program
does not read the paper) and checks every entry:

  1. NUMERICS.  Both sides of every formula are evaluated with mpmath at --dps digits
     (default 100); agreement to at least 60 digits is required.  Zero relations are formulas
     with left side 0.  Formulas with a parameter b are evaluated at several values of b.
  2. EXACT STATUS OF THE DEGREE-1 ITEMS against the project's theorems:
       * the class: P(1, b0^B, n, A) is a series  sum rho(k) b0^(-floor(k/2))/k  (n = 2B,
         "step 2") or  sum rho(k) b0^(-k)/k  (n = B, "step 1");
       * base 2, value a rational multiple of pi (or 0): exact coordinates in the eight named
         patterns of lean/Pilean/PiFormula/VSeries.lean (namedA1 ... namedTW), so that
         `hasSum_namedComb` gives the value, and in the basis of pi_space_basis_120.json;
         value sqrt(2) pi, sqrt(3) pi, sqrt(5) pi: coordinates in the thirteen patterns of
         Theorem C (`comb13`);
       * base 3, period 12: coordinates in G, Z1, Z2 of lean/Pilean/Base3/Dimension.lean;
       * the Lean theorem, when the same statement is already one.
  3. LISTS.  Each prime of list (9) against the criterion of Theorem K
     (log_prime_criterion.py), and the primes below the largest entry that pass the criterion
     but are not listed.  Each rational of lists (14), (15), (16): an exact certificate in
     Z[i] that arctan q is a rational combination of pi and the arguments of the atoms
     Phi_m(1+i), Phi_m(-1-i), Phi_m(i 2^(2^(e+1))) (m odd); independence of (15); the span.
  4. TABLE 1.  Degree 1: the count from Theorem C (derive_bailey_table.py) and the Lean
     theorem.  Higher degree: the rank of the printed relations, rewritten to the row's base
     and length, as a lower bound; with --lll (needs python-flint) the count is also found
     numerically by lattice reduction, for every row.
  5. PROSE.  The assertions with a mechanical content (linear combinations of formulas and
     relations, equivalences, counts, positions) are checked exactly; the others get a
     status written by hand in this file (settled by a theorem of the project, overstated,
     open, attribution not checked, ...).

With --write the results are stored in the ledger (field "checks" and "status" of each entry,
and "summaries" for the two lists) and literature/bailey-compendium/LEDGER.md is regenerated.
Without it nothing is written.  A run without --lll keeps the lattice counts that an earlier
run with --lll stored.  Needs mpmath and sympy (python-flint for --lll); it imports
log_prime_criterion.py and derive_bailey_table.py from this folder.  Output is ASCII.

What a status means.  "numerically confirmed (d digits)": both sides agree to d digits, which
is evidence, not proof.  "Lean: name": the same statement is a theorem of lean/Pilean.
"from the classification: ...": the exact coordinates of the formula's pattern in the
project's basis, from which the Lean proof is one line.  A certificate for arctan q is an exact
identity in Z[i]; it proves that arctan q is a value of the class F.  The absence of a
certificate proves the contrary only together with Baker's theorem (Theorem I of the project,
formalized for 2/7, 5/8 and 4/9).
"""
import ast
import io
import json
import os
import sys
import time
from fractions import Fraction
from functools import lru_cache
from math import gcd

import mpmath
from mpmath import mp, mpf, mpc

HERE = os.path.dirname(os.path.abspath(__file__))
LEDGER_DIR = os.path.join(os.path.dirname(HERE), "literature", "bailey-compendium")
LEDGER = os.path.join(LEDGER_DIR, "ledger.json")
LEDGER_MD = os.path.join(LEDGER_DIR, "LEDGER.md")
NEED_DIGITS = 60

# =====================================================================================
# 1. Expressions
# =====================================================================================
# The ledger writes numbers and constants as ASCII expressions with ^ for powers.  They are
# evaluated on the syntax tree, never with eval(): integers and quotients of integers stay
# exact (int, Fraction); everything else is an mpmath number.


def _is_exact(x):
    return isinstance(x, (int, Fraction)) and not isinstance(x, bool)


def _clausen(n, t):
    n = int(n)
    return mp.clcos(n, t) if n % 2 else mp.clsin(n, t)


def _fn(name):
    return {
        "log": lambda x: mp.log(mpf(x)), "sqrt": lambda x: mp.sqrt(mpf(x)),
        "atan": lambda x: mp.atan(mpf(x)), "acos": lambda x: mp.acos(mpf(x)),
        "zeta": lambda x: mp.zeta(x), "cl": _clausen,
        "clog": lambda x: mp.log(mpc(x)), "re": lambda x: mp.re(x),
    }[name]


def _const(name):
    if name == "pi":
        return +mp.pi
    if name == "phi":
        return (1 + mp.sqrt(5)) / 2
    if name == "catalan":
        return +mp.catalan
    if name == "I":
        return mpc(0, 1)
    raise KeyError(name)


def _num(x):
    return mpf(x.numerator) / mpf(x.denominator) if isinstance(x, Fraction) else x


def _ev(node, env):
    if isinstance(node, ast.Expression):
        return _ev(node.body, env)
    if isinstance(node, ast.Constant):
        assert isinstance(node.value, int), node.value
        return node.value
    if isinstance(node, ast.Name):
        return env[node.id] if node.id in env else _const(node.id)
    if isinstance(node, ast.UnaryOp):
        v = _ev(node.operand, env)
        return -v if isinstance(node.op, ast.USub) else v
    if isinstance(node, ast.Call):
        return _fn(node.func.id)(*[_num(_ev(a, env)) for a in node.args])
    if isinstance(node, ast.IfExp):
        return _ev(node.body, env) if _ev(node.test, env) else _ev(node.orelse, env)
    if isinstance(node, ast.Compare):
        a, b = _ev(node.left, env), _ev(node.comparators[0], env)
        return {ast.Lt: a < b, ast.Gt: a > b, ast.Eq: a == b}[type(node.ops[0])]
    if isinstance(node, ast.BinOp):
        a, b = _ev(node.left, env), _ev(node.right, env)
        op = type(node.op)
        if op is ast.Pow:
            if _is_exact(a) and isinstance(b, int):
                return Fraction(a) ** b if (b < 0 or isinstance(a, Fraction)) else a ** b
            return mp.power(_num(a), _num(b))
        if _is_exact(a) and _is_exact(b):
            if op is ast.Add:
                return a + b
            if op is ast.Sub:
                return a - b
            if op is ast.Mult:
                return a * b
            r = Fraction(a) / Fraction(b)
            return r.numerator if r.denominator == 1 else r
        a, b = _num(a), _num(b)
        if op is ast.Add:
            return a + b
        if op is ast.Sub:
            return a - b
        if op is ast.Mult:
            return a * b
        return a / b
    raise ValueError(ast.dump(node))


@lru_cache(maxsize=None)
def _parse(expr):
    return ast.parse(expr.replace("^", "**"), mode="eval")


def ev(expr, env=None):
    """Value of a ledger expression: int or Fraction when it is rational, else mpmath."""
    return _ev(_parse(expr), env or {})


def evn(expr, env=None):
    return _num(ev(expr, env))


# =====================================================================================
# 2. Series
# =====================================================================================

def P_value(s, b, n, A):
    """Bailey's P(s, b, n, A) = sum_{k>=0} b^(-k) sum_{j=1..n} a_j/(kn+j)^s, numerically."""
    b = _num(b)
    A = [_num(a) for a in A]
    K = int((mp.dps + 25) * mp.log(10) / mp.log(abs(b))) + 3
    tot = mpf(0)
    bk = mpf(1)
    for k in range(K):
        inner = mpf(0)
        for j, a in enumerate(A, 1):
            if a:
                inner += a / mpf(k * n + j) ** s
        tot += inner * bk
        bk /= b
    return tot


def P_scale(s, n, A):
    return sum(abs(_num(a)) / mpf(j) ** s for j, a in enumerate(A, 1))


def series_value(term, k0, env=None, limit=200000):
    """sum_{k>=k0} term(k) for a geometrically convergent series."""
    env = dict(env or {})
    tot = mpf(0)
    small = 0
    eps = mpf(10) ** (-(mp.dps + 20))
    for k in range(k0, limit):
        env["k"] = k
        t = evn(term, env)
        tot += t
        small = small + 1 if abs(t) < eps * max(1, abs(tot)) else 0
        if small >= 8:
            return tot
    raise ArithmeticError("series did not converge: " + term)


def digits(lhs, rhs, scale=None):
    d = abs(lhs - rhs)
    sc = scale if scale else max(abs(lhs), abs(rhs))
    if d == 0:
        return mp.dps
    return int(mp.floor(-mp.log10(d / sc)))


def rhs_vector(term, env):
    """(s, b, n, A) of one P term, with the rule of formula 91 expanded."""
    b = ev(term["b"], env)
    n = term["n"] if isinstance(term["n"], int) else int(ev(term["n"], env))
    if isinstance(term["A"], dict):
        A = []
        for j in range(1, n + 1):
            e2 = dict(env)
            e2["j"] = j
            A.append(ev(term["A"]["rule"], e2))
    else:
        A = [ev(a, env) for a in term["A"]]
    assert len(A) == n, "vector length %d, n = %d" % (len(A), n)
    return term["s"], b, n, A


def check_formula_numeric(e):
    """Numerical check of one formula entry.  Returns the dict stored under checks.numeric."""
    c = e["content"]
    typ = c["type"]
    if typ == "exact":
        return None
    envs = [{}]
    if "param" in c:
        envs = [{c["param"]["name"]: ev(v)} for v in c["param"]["test_values"]]
    if "params" in c:
        envs = [{}]
        for name, vals in c["params"].items():
            envs = [dict(en, **{name: ev(v)}) for en in envs for v in vals]
    worst = None
    lhs_show = None
    for env in envs:
        if typ == "P":
            lhs = evn(c["lhs"], env)
            rhs = mpf(0)
            scale = mpf(0)
            for t in c["rhs"]:
                s, b, n, A = rhs_vector(t, env)
                co = evn(t["coef"], env)
                rhs += co * P_value(s, b, n, A)
                scale += abs(co) * P_scale(s, n, A)
            d = digits(lhs, rhs, scale if lhs == 0 else None)
        elif typ == "series":
            lhs = evn(c["lhs"], env)
            if c.get("slow"):
                rhs = mp.nsum(lambda k: evn(c["term"], {"k": int(k)}), [c["k0"], mp.inf])
            else:
                rhs = series_value(c["term"], c["k0"], env)
            rhs = evn(c.get("constant_term", "0"), env) + evn(c["prefactor"], env) * rhs
            d = digits(lhs, rhs)
        elif typ == "recurrence_series":
            lhs = evn(c["lhs"], env)
            D0, D1 = 1, 1
            tot = mpf(0)
            for k in range(0, int((mp.dps + 25) / 0.65) + 5):   # |D_k| <= c 5^(k/2), ratio sqrt(5)/10
                tot += mpf(D0) / mpf(10) ** k / (k + 1)
                D0, D1 = D1, D1 - 5 * D0
            rhs = evn(c["prefactor"]) * tot
            d = digits(lhs, rhs)
        elif typ == "identity":
            lhs = evn(c["lhs"], env)
            rhs = evn(c["rhs"], env)
            d = digits(lhs, rhs)
        elif typ == "chain":
            lhs = evn(c["lhs"], env)
            d = mp.dps
            for st in c["steps"]:
                if isinstance(st, str):
                    v = evn(st, env)
                else:
                    v = sum(evn(co) * series_value(tm, k0) for co, tm, k0 in st["series"])
                d = min(d, digits(lhs, v))
            rhs = v
        else:
            raise ValueError(typ)
        if worst is None or d < worst:
            worst = d
            lhs_show = lhs
    return {"status": "agree" if worst >= NEED_DIGITS else "DISAGREE", "digits": int(min(worst, mp.dps - 10)),
            "working_digits": mp.dps, "evaluations": len(envs),
            "value": mp.nstr(lhs_show, 25) if lhs_show is not None else None}


# =====================================================================================
# 3. Exact vectors, rewriting, patterns
# =====================================================================================

def exact_vector(e, env=None, bare=False):
    """(s, b, n, [coef * a_j]) with exact rationals, for a formula with one P term and
    rational base, prefactor and coefficients; None otherwise.  With bare=True the prefactor
    is left out (it may then be irrational)."""
    c = e["content"]
    if c.get("type") != "P" or len(c["rhs"]) != 1 or ("param" in c and env is None):
        return None
    t = c["rhs"][0]
    try:
        s, b, n, A = rhs_vector(t, env or {})
        co = 1 if bare else ev(t["coef"], env or {})
    except Exception:
        return None
    if not (_is_exact(b) and _is_exact(co) and all(_is_exact(a) for a in A)):
        return None
    if isinstance(b, Fraction):
        return None
    return s, b, n, [Fraction(co) * a for a in A]


def rewrite(vec, r):
    """P(s, b, n, A) = P(s, b^r, rn, A') with a'_(mn+j) = a_j b^(-m), m = 0..r-1."""
    s, b, n, A = vec
    out = []
    for m in range(r):
        out += [a / Fraction(b) ** m for a in A]
    return s, b ** r, r * n, out


def to_frame(vec, b_target, n_target):
    s, b, n, A = vec
    if n_target % n:
        return None
    r = n_target // n
    v = rewrite(vec, r)
    return v if v[1] == b_target else None


def root_power(b):
    """|b| = b0^B with b0 >= 2 not a perfect power."""
    a = abs(b)
    for B in range(a.bit_length(), 0, -1):
        r = int(round(a ** (1.0 / B)))
        for c in (r - 1, r, r + 1):
            if c >= 2 and c ** B == a:
                return c, B
    raise ValueError(b)


def class_of(vec):
    """The class of P(1, b, n, A): root base b0, exponent B, step, and the pattern rho of
    period `period` with  P = sum_{k>=1} rho(k) b0^(-floor(k/2))/k  (rho as a list, index k-1)."""
    s, b, n, A = vec
    if b < 0:
        s, b, n, A = rewrite(vec, 2)
    b0, B = root_power(b)
    info = {"root_base": b0, "B": B, "n": n}
    if n == 2 * B:
        info["step"] = 2
        info["period"] = n
        rho = [A[j - 1] * b0 ** (j // 2) for j in range(1, n + 1)]
    elif n == B:
        info["step"] = 1
        info["period"] = 2 * n
        rho = [0] * (2 * n)
        for j in range(1, n + 1):
            rho[2 * j - 1] = 2 * A[j - 1] * b0 ** j
    else:
        info["step"] = "other"
        # other root bases: b = c^B' with n = B' or 2B'
        alt = []
        for d in range(1, B + 1):
            if B % d == 0 and n in (B // d, 2 * B // d):
                alt.append("%d^%d with step %d" % (b0 ** d, B // d, 2 if n == 2 * B // d else 1))
        info["alternatives"] = alt
        return info, None
    return info, rho


def pattern_value(rho, b0):
    """sum_{k>=1} rho(k) b0^(-floor(k/2))/k numerically (rho periodic, list index k-1)."""
    N = len(rho)
    K = int((mp.dps + 25) * mp.log(10) / mp.log(b0)) * 2 + 4
    tot = mpf(0)
    for k in range(1, K):
        r = rho[(k - 1) % N]
        if r:
            tot += mpf(r.numerator) / r.denominator / mpf(b0) ** (k // 2) / k
    return tot


def solve(rows, target):
    """Exact solution x of sum_i x_i rows[i] = target (lists of Fractions), or None."""
    m = len(rows)
    ncol = len(target)
    M = [[Fraction(rows[i][c]) for i in range(m)] + [Fraction(target[c])] for c in range(ncol)]
    piv = []
    r = 0
    for col in range(m):
        p = next((i for i in range(r, ncol) if M[i][col] != 0), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        inv = 1 / M[r][col]
        M[r] = [x * inv for x in M[r]]
        for i in range(ncol):
            if i != r and M[i][col] != 0:
                f = M[i][col]
                M[i] = [x - f * y for x, y in zip(M[i], M[r])]
        piv.append(col)
        r += 1
    if any(M[i][m] != 0 for i in range(r, ncol)):
        return None
    x = [Fraction(0)] * m
    for i, col in enumerate(piv):
        x[col] = M[i][m]
    return x


def rank(rows):
    rows = [[Fraction(x) for x in r] for r in rows if any(r)]
    r = 0
    ncols = len(rows[0]) if rows else 0
    for c in range(ncols):
        p = next((i for i in range(r, len(rows)) if rows[i][c] != 0), None)
        if p is None:
            continue
        rows[r], rows[p] = rows[p], rows[r]
        for i in range(len(rows)):
            if i != r and rows[i][c] != 0:
                f = rows[i][c] / rows[r][c]
                rows[i] = [a - f * b for a, b in zip(rows[i], rows[r])]
        r += 1
    return r


def nullspace(rows):
    """A basis of the coefficient vectors c with sum_i c_i rows[i] = 0."""
    m = len(rows)
    out = []
    indep = []          # indices of an independent subfamily
    for i in range(m):
        x = solve([rows[j] for j in indep], rows[i]) if indep else (None if any(rows[i]) else [])
        if x is None:
            indep.append(i)
        else:
            c = [Fraction(0)] * m
            c[i] = Fraction(-1)
            for j, xj in zip(indep, x):
                c[j] = xj
            out.append(c)
    return out


def fs(x):
    x = Fraction(x)
    return str(x.numerator) if x.denominator == 1 else "%d/%d" % (x.numerator, x.denominator)


# =====================================================================================
# 4. The project's bases (base 2: period 120; base 3: period 12)
# =====================================================================================
# The eight named patterns and the five further patterns of Theorem C are rebuilt here from
# their definitions in the Lean files (rhoA P = -Im(P U)/2, rhoL P = -Re(P U)/2, with the
# power-sum tables P and U(k) = (-i)^(k div 2) (2 or 1 - i)); lean/scripts/baileygen.py and
# fivegen.py build them the same way.  They are checked below against values quoted in
# TheoremC3.lean (`comb13_at_1`) and numerically against the stated sums.

def _ipow(n):
    return [(1, 0), (0, 1), (-1, 0), (0, -1)][n % 4]


def _gm(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def _U(k):
    u = _ipow(-(k // 2))
    return _gm(u, (2, 0) if k % 2 == 0 else (1, -1))


def _c(n):
    def ram(k):                     # Ramanujan sum c_n(k) for n = 2, 6, 10
        tot = 0
        for d in range(1, n + 1):
            if n % d == 0 and k % d == 0:
                mu = {1: 1, 2: -1, 3: -1, 5: -1, 6: 1, 10: 1}[n // d]
                tot += d * mu
        return (tot, 0)
    return ram


def _p8a(k):
    return _gm((2, 0), _ipow(k // 2)) if k % 2 == 0 else (0, 0)


def _p8b(k):
    return _gm((2, 0), _ipow(-(k // 2))) if k % 2 == 0 else (0, 0)


def _p24(k):
    a = _gm((6, 0), _ipow(k // 6)) if k % 6 == 0 else (0, 0)
    b = _p8b(k)
    return (a[0] - b[0], a[1] - b[1])


def _twisted(n, groups):
    """Table over k mod n of sum over groups of coef(z) * sum of sign * z^(a k), z = e^(2 pi i/n);
    the values are Gaussian integers (checked)."""
    with mp.workdps(40):
        z = mp.expjpi(mpf(2) / n)
        tab = []
        for r in range(n):
            v = mpc(0)
            for coef, terms in groups:
                cv = sum(sg * z ** ex for sg, ex in coef)
                v += cv * sum(sg * z ** ((a * r) % n) for sg, a in terms)
            a, b = int(mp.nint(v.real)), int(mp.nint(v.imag))
            assert abs(v - mpc(a, b)) < mpf(10) ** (-25), (n, r, v)
            tab.append((a, b))
    return lambda k: tab[k % n]


_S3 = [(1, 2), (-1, 10)]                         # sqrt(3) = z24^2 - z24^10
_PTW = _twisted(24, [(_S3, [(1, 1), (-1, 5), (1, 13), (-1, 17), (1, 4), (-1, 20)])])
_PS3 = _twisted(24, [(_S3, [(1, 4), (-1, 20)])])
_PS2 = _twisted(24, [([(1, 3), (1, 21)], [(1, 9), (-1, 21), (-1, 1), (1, 5), (1, 13), (-1, 17)])])
_PS5 = _twisted(20, [([(1, 4), (-1, 8), (-1, 12), (1, 16)],
                      [(1, 3), (1, 7), (-1, 11), (-1, 19), (-1, 2), (-1, 18), (1, 6), (1, 14)])])
_TH1, _TH3 = [(1, 1), (1, 19)], [(1, 3), (1, 17)]
_PT1 = _twisted(20, [(_TH1, [(1, 3), (-1, 2), (-1, 7), (1, 18)]), (_TH3, [(-1, 19), (1, 6), (1, 11), (-1, 14)])])
_PT2 = _twisted(20, [(_TH3, [(1, 3), (-1, 2), (-1, 7), (1, 18)]), (_TH1, [(1, 19), (-1, 6), (-1, 11), (1, 14)])])
_one = lambda k: (1, 0)


def _rhoA(P, k):
    return Fraction(-_gm(P(k), _U(k))[1], 2)


def _rhoL(P, k):
    return Fraction(-_gm(P(k), _U(k))[0], 2)


NAMED = [
    ("namedA1", lambda k: _rhoA(_one, k), "pi/4"),
    ("namedA6", lambda k: _rhoA(_c(6), k), "0"),
    ("namedA10", lambda k: _rhoA(_c(10), k) - _rhoA(_c(2), k), "pi/4"),
    ("namedL6", lambda k: _rhoL(_c(6), k) - 2 * _rhoL(_one, k), "0"),
    ("namedL8", lambda k: _rhoL(_p8a, k) - 2 * _rhoL(_one, k), "0"),
    ("namedL10", lambda k: _rhoL(_c(10), k) - _rhoL(_c(2), k) - 3 * _rhoL(_one, k), "0"),
    ("namedL24", lambda k: _rhoL(_p24, k) - _rhoL(_p8b, k) - 2 * _rhoL(_one, k), "0"),
    ("namedTW", lambda k: _rhoA(_PTW, k), "0"),
]
EXTRA = [
    ("extraS3", lambda k: _rhoA(_PS3, k), "-sqrt(3)/3*pi"),
    ("extraS2", lambda k: _rhoA(_PS2, k), "-sqrt(2)*pi"),
    ("extraS5", lambda k: _rhoA(_PS5, k), "-sqrt(5)*pi"),
    ("extraT1", lambda k: _rhoA(_PT1, k), "(th1 - 3*th3)/5*pi"),
    ("extraT2", lambda k: _rhoA(_PT2, k), "(3*th1 + th3)/5*pi"),
]


def _vec120(f):
    return [f(k) for k in range(1, 121)]


def project_bases():
    """The thirteen patterns as lists (index k-1, k = 1..120) and their values; self-test."""
    out = []
    env = {"th1": 2 * mp.cos(mp.pi / 10), "th3": 2 * mp.cos(3 * mp.pi / 10)}
    at1 = {"namedA1": "1/2", "namedA6": "1/2", "namedA10": "1", "namedL6": "1/2", "namedL8": "1",
           "namedL10": "1/2", "namedL24": "1", "namedTW": "-3/2", "extraS3": "-3/2", "extraS2": "-4",
           "extraS5": "-5", "extraT1": "0", "extraT2": "5"}                 # comb13_at_1
    for name, f, val in NAMED + EXTRA:
        v = _vec120(f)
        assert v[0] == Fraction(at1[name]), (name, v[0])
        with mp.workdps(40):
            assert abs(pattern_value(v, 2) - evn(val, env)) < mpf(10) ** (-35), name
        out.append((name, v, val))
    return out, env


def rho120(rho):
    N = len(rho)
    if 120 % N:
        return None
    return [rho[(k - 1) % N] for k in range(1, 121)]


# base 3 (lean/Pilean/Base3/PiSqrt3.lean, Dimension.lean): G, Z1, Z2 of period 12
def base3_patterns():
    G = [Fraction(6 * (-1) ** (k // 2)) if k % 2 == 1 else Fraction(0) for k in range(1, 13)]
    z1 = {2: 1, 3: -2, 5: 1, 6: 4, 8: 3, 9: 2, 10: 4, 11: -1}
    z2 = {1: 1, 2: -3, 3: -4, 4: -3, 5: 1, 7: -1, 8: 3, 9: 4, 10: 3, 11: -1}
    Z1 = [Fraction(z1.get(k % 12, 0)) for k in range(1, 13)]
    Z2 = [Fraction(z2.get(k % 12, 0)) for k in range(1, 13)]
    with mp.workdps(40):
        assert abs(pattern_value(G, 3) - mp.pi * mp.sqrt(3)) < mpf(10) ** (-35)
        assert abs(pattern_value(Z1, 3)) < mpf(10) ** (-35) and abs(pattern_value(Z2, 3)) < mpf(10) ** (-35)
    return G, Z1, Z2


# Closed forms that reduce a value to pi and arctangents of rationals (checked numerically).
VALUE_NOTES = {
    "10": ("pi/2 - atan(1/2)", "arctan(1/2) is a generator of Theorem A"),
    "25": ("pi/4 + atan(1/2)/2", "tan(2 arctan phi) = -2"),
    "26": ("pi/2 - atan(1/2)/2", "tan(2 arctan phi^3) = -1/2"),
    "27": ("pi/2 - atan(2/11)/2", "tan(2 arctan phi^5) = -2/11 (Lucas number 11); 2/11 is in list (14)"),
    "28": ("pi/2 - atan(2/29)/2", "tan(2 arctan phi^7) = -2/29 (Lucas number 29); 2/29 is in list (14)"),
}

# Entries whose statement is already a theorem of the Lean library (same series, same value).
LEAN_SAME = {
    "1": "PiFormula.BaseB.bbp_formula", "6": "PiFormula.BaseB.bbp_formula",
    "4": "PiFormula.BaseB.hasSum_log_two (P(1, 2, 1, (1/2)) = log 2)",
    "7": "PiFormula.BaseB.hasSum_log_two (P(1, 2, 1, (1/2)) = log 2)",
    "70": "PiFormula.BaseB.hasSum_log_three (P(1, 9, 2, (1, 1/9)) = log 3)",
    "p25.c": "PiFormula.BaseB.hasSum_log_three (the same series)",
    "69": "PiFormula.Base3.broadhurst_formula",
    "130": "PiFormula.Base3.relation130", "131": "PiFormula.Base3.relation131",
    "p05.g": "PiFormula.aurifeuille",
}
# Existence of a formula for the same constant in the same class is a Lean theorem (the explicit
# series of the paper is not).
LEAN_EXISTS = {
    "8": "PiFormula.isFValue_log_3 (existence only)",
    "67": "PiFormula.Base3.isF3Value_log_2 (existence only)",
    "71": "PiFormula.Base3.isF3Value_log_three (existence; formula 70 is the Lean series)",
    "72": "PiFormula.Base3.isF3Value_log_5 (existence only)",
    "73": "PiFormula.Base3.isF3Value_log_7 (existence only)",
    "74": "PiFormula.Base3.isF3Value_log_11 (existence only)",
    "75": "PiFormula.Base3.isF3Value_log_13 (existence only)",
    "85": "PiFormula.Base5.isF5Value_log_three_halves (existence only)",
}


def degree1_status(e, bases, b3):
    """Exact status of a degree-1 formula with integer base against the project's theorems."""
    vec = exact_vector(e)
    c = e["content"]
    out = {}
    prefactor = "1"
    if vec is None and "param" not in c and exact_vector(e, bare=True) is not None:
        vec = exact_vector(e, bare=True)                # irrational prefactor (formula 88)
        prefactor = c["rhs"][0]["coef"]
        out["prefactor_note"] = "the prefactor %s is irrational; the class is that of P(...) itself" % prefactor
    if vec is None:
        if "param" in c:
            inst = {}
            for bv in ("2", "3"):
                try:
                    v = exact_vector(e, {c["param"]["name"]: ev(bv)})
                    if v is None:
                        inst[bv] = "base or coefficients not rational"
                        continue
                    info, _ = class_of(v)
                    inst[bv] = "base %d^%d, n = %d: step %s" % (info["root_base"], info["B"], info["n"], info["step"]) + (
                        " (" + "; ".join(info.get("alternatives", [])) + ")" if info.get("alternatives") else "")
                except Exception as ex:
                    inst[bv] = "not defined (%s)" % type(ex).__name__
            out["class"] = "family in the parameter b; instances: b = 2: %s; b = 3: %s" % (inst["2"], inst["3"])
            out["from_classification"] = ("no: an identity in b; each instance in base 2 or 3 with a value in Q pi "
                                          "or 0 has coordinates, the family needs a direct proof")
        else:
            out["class"] = "not a series with rational base and coefficients"
            out["from_classification"] = "no"
        return out
    info, rho = class_of(vec)
    b0 = info["root_base"]
    proj = {2: "F (base 2)", 3: "F3 (base 3)", 5: "F5 (base 5)"}.get(b0, "F_b, b = %d" % b0 if b0 >= 5 else "base %d" % b0)
    out["root_base"], out["B"], out["step"] = b0, info["B"], info["step"]
    if rho is None:
        out["class"] = "base %d^%d, n = %d: neither n = B nor n = 2B%s" % (
            b0, info["B"], info["n"], "; as " + ", ".join(info["alternatives"]) if info["alternatives"] else "")
        out["from_classification"] = "no"
        return out
    out["class"] = "%s, step %d (weights %d^(-%s)), period %d" % (
        proj, info["step"], b0, "floor(k/2)" if info["step"] == 2 else "k", info["period"])
    lhs = c["lhs"]
    lhs_val = evn(lhs)
    with mp.workdps(50):
        assert abs(pattern_value(rho, b0) * evn(prefactor) - evn(lhs)) < mpf(10) ** (-40), e["id"]
    if e["id"] in VALUE_NOTES:
        expr, text = VALUE_NOTES[e["id"]]
        assert abs(evn(expr) - lhs_val) < mpf(10) ** (-NEED_DIGITS), e["id"]
        out["closed_form"] = "%s = %s (checked numerically); %s" % (lhs, expr, text)
    if lhs.startswith("atan(") and "phi" not in lhs and "sqrt" not in lhs:
        q = Fraction(ev(lhs[5:-1]))
        ok, desc = arctan_certificate(q.denominator, q.numerator)
        out["arctan_certificate"] = desc if ok else "NONE: " + desc
    if b0 == 2:
        r = rho120(rho)
        named = bases[0]
        kind = None
        if lhs in ("pi", "0"):
            kind = "rational"
        elif lhs in ("pi*sqrt(2)", "pi*sqrt(3)", "pi*sqrt(5)"):
            kind = "algebraic"
        if kind and r is not None:
            use = named[:8] if kind == "rational" else named
            q = solve([v for _, v, _ in use], r)
            if q is None:
                out["from_classification"] = "NOT in the span of the project's basis (unexpected)"
            else:
                val = sum(evn(fs(qi)) * evn(vs, bases[1]) for qi, (_, _, vs) in zip(q, use))
                assert abs(val - lhs_val) < mpf(10) ** (-NEED_DIGITS), e["id"]
                out["coordinates_named"] = {nm: fs(qi) for qi, (nm, _, _) in zip(q, use) if qi != 0}
                if kind == "rational":
                    assert (q[0] + q[2]) / 4 == (1 if lhs == "pi" else 0)
                    pats, qs = bases[2]
                    qj = solve(pats, r)
                    assert qj is not None and sum(a * b for a, b in zip(qj, qs)) == (1 if lhs == "pi" else 0)
                    out["coordinates_json_basis"] = [fs(x) for x in qj]
                    out["from_classification"] = ("yes: pattern = namedComb q, value (q0 + q2) pi/4 "
                                                  "(hasSum_bailey_F%d + hasSum_namedComb)" % info["step"])
                else:
                    out["from_classification"] = ("yes: pattern = comb13 q p (Theorem C, thirteen patterns); value "
                                                  "from hasSum_namedA1 ... hasSum_extraT2")
        elif lhs.startswith("log(") and lhs.endswith(")") and lhs.count("(") == 1:
            out["from_classification"] = ("existence follows from Theorem K (criterion for logarithms); the explicit "
                                          "series needs the generator lemma isFValue_gen / hasSum_gen")
        elif lhs.startswith("atan(") and "phi" not in lhs and "sqrt" not in lhs:
            out["from_classification"] = ("no (value is not in Q-bar pi); in class F; provable from the arguments of "
                                          "(1+i)^n - c: hasSum_gamma, exp_gamma (as isFValue_arctan_inv_129)")
        elif "closed_form" in out:
            out["from_classification"] = ("no (value is not in Q-bar pi); in class F; the value is a rational "
                                          "combination of pi and the argument of a Gaussian integer: hasSum_gamma, exp_gamma")
        else:
            out["from_classification"] = ("no (value is not an algebraic multiple of pi); in class F; needs "
                                          "series_eq_logs (Fourier inversion) and an exact evaluation of the logarithms")
    elif b0 == 3:
        if lhs in ("pi*sqrt(3)", "0") and 12 % len(rho) == 0:
            r = [rho[(k - 1) % len(rho)] for k in range(1, 13)]
            q = solve(list(b3), r)
            assert q is not None, e["id"]
            assert q[0] == (1 if lhs != "0" else 0)
            out["coordinates_base3"] = {"G": fs(q[0]), "Z1": fs(q[1]), "Z2": fs(q[2])}
            out["from_classification"] = "yes: pattern = comb3 a b c, value a pi sqrt(3) (hasSum_bailey3_F2 + hasSum_comb3)"
        elif lhs.startswith("log("):
            out["from_classification"] = ("existence follows from Theorem K3 (criterion for logarithms, base 3); the "
                                          "explicit series needs hasSum_gen3")
        else:
            out["from_classification"] = "no (value is not an algebraic multiple of pi); in class F3"
    else:
        if lhs.startswith("log("):
            out["from_classification"] = ("existence is consistent with the criteria K5 / M; the explicit series is a "
                                          "direct computation (Mercator series)")
        else:
            out["from_classification"] = "no; in the class of base %d, value transcendental by the project's theorems" % b0
    return out


INGREDIENTS = {
    2: "dilogarithm ladder: Li_2 at 1/2 and (1+-i)/2 (Euler reflection, Landen, distribution relations); "
       "imaginary parts give G and Cl_2",
    3: "trilogarithm ladder: Li_3 at 1/2 and (1+-i)/2 (Landen's Li_3 identity, inversion, distribution relations), zeta(3)",
    4: "polylogarithm ladder of order 4 at 1/2, (1+-i)/2 and 2^(-1/2) e^(i pi/4 m) (Broadhurst's ladders; Kummer-type "
       "relations), Cl_4 from imaginary parts",
    5: "polylogarithm ladder of order 5 (Broadhurst; Adegoke's proofs): Li_5 at 1/2, (1+-i)/2 with inversion and "
       "distribution relations, zeta(5)",
}


def ingredients(e):
    s = e["degree"]
    c = e["content"]
    base3 = str(e["base"]).startswith(("3", "9", "-27"))
    if base3:
        return ("polylogarithms of order %d at 1/3, -1/3 and e^(i pi/6 m)/sqrt(3) (sixth roots of unity): inversion "
                "and distribution relations" % s)
    t = INGREDIENTS[s]
    if "sqrt(3)" in c["lhs"]:
        t += "; arguments 2^(-1/2) times twelfth roots of unity for the sqrt(3) terms"
    if c.get("zero_relation"):
        t = "vanishing combination of the same functional equations: " + t
    return t


# =====================================================================================
# 5. List (9): primes
# =====================================================================================

def check_primes(entries, log):
    import sympy
    sys.path.insert(0, HERE)
    import log_prime_criterion as lpc
    listed = [int(e["content"]["p"]) for e in entries]
    X = max(listed)
    res = {}
    lean_below_100 = {2, 3, 5, 7, 11, 13, 17, 19, 29, 31, 37, 41, 43, 61, 73}
    lean_dvd = {2, 3, 5, 7, 11, 13, 31, 41, 61, 151, 331, 1321}
    for p in listed:
        assert sympy.isprime(p), p
        ok = lpc.has_formula(p)
        inst = None
        m = (p + 1).bit_length() - 1
        if p + 1 == 1 << m:
            inst = "isFValue_log_two_pow_sub_one (m = %d)" % m
        else:
            for k in range(0, 40):
                n = 2 * k + 1
                if p == 2 ** n - 2 ** (k + 1) + 1:
                    inst = "isFValue_log_L (n = %d)" % n
                if p == 2 ** n + 2 ** (k + 1) + 1:
                    inst = "isFValue_log_M (n = %d)" % n
        if p in lean_below_100:
            lean = "PiFormula.Unconditional.log_primes_below_100 / isFValue_log_of_mem"
        elif inst:
            lean = "PiFormula." + inst + " (this prime is the number itself)"
        elif p in lean_dvd:
            lean = "PiFormula.isFValue_log_of_dvd (prime factor of 2 (2^60 - 1))"
        else:
            lean = "PiFormula.Unconditional.isFValue_log_prime_classification (the test, evaluated by program)"
        res[p] = {"criterion": "passes" if ok else "FAILS", "explain": lpc.explain(p), "lean": lean}
    # completeness: every prime p <= X that passes the criterion.  Enumerate the primitive
    # parts g by index n; p passes iff g = p^x R with R = 1 or R a prime factor of n that passes.
    found = set()
    wieferich = [1093, 3511]       # the only primes p < 4.5e12 with p^2 | 2^(p-1) - 1 (published searches)
    xbits = X.bit_length()
    x_sym = sympy.Symbol("x")
    nmax = 60000
    for n in range(1, nmax + 1):
        phi = int(sympy.totient(n))
        half = n % 8 == 4
        lower = phi // 2 - 12 if half else phi - 2          # g > 2^lower (as in log_prime_criterion.py)
        if lower > xbits + n.bit_length():
            continue
        if half:
            d = n // 4
            parts = [lpc.norm_phi_at_t(d), lpc.norm_phi_at_t(2 * d)]
        else:
            parts = [int(sympy.cyclotomic_poly(n, 2))]
        for g in parts:
            r = g
            for q in sympy.primefactors(n):
                while r % q == 0:
                    r //= q
            if r > 1 and r <= X and sympy.isprime(r):
                if lpc.has_formula(r):
                    found.add(r)
    # the bound used: phi(n) >= sqrt(n/2), so every n with lower <= xbits + bits(n) is below nmax
    assert (int((nmax / 2) ** 0.5) // 2 - 12) > xbits + nmax.bit_length()
    for p in [2] + wieferich:
        if lpc.has_formula(p):
            found.add(p)
    missing = sorted(found - set(listed))
    extra = sorted(set(listed) - found)
    below_1e7 = sorted(p for p in found if p < 10 ** 7)
    summary = {"largest_listed": X, "listed": len(listed), "passing_up_to_largest": len(found),
               "passing_not_listed": missing, "listed_not_found_by_enumeration": extra,
               "passing_not_listed_explained": {str(p): lpc.explain(p) for p in missing},
               "passing_below_1e7": len(below_1e7),
               "assumption": "x = 1 (no p^2 in the primitive part) except for the Wieferich primes 1093 and 3511, "
                             "the only ones below 4.5e12 by published searches; both were tested directly"}
    log("list (9): %d primes, all pass the criterion: %s; primes <= %d passing: %d; not listed: %d"
        % (len(listed), all(v["criterion"] == "passes" for v in res.values()), X, len(found), len(missing)))
    return res, summary


# =====================================================================================
# 6. Lists (14), (15), (16): arctangents
# =====================================================================================

def _gnorm(a):
    return a[0] * a[0] + a[1] * a[1]


def _gpow(a, n):
    r = (1, 0)
    for _ in range(n):
        r = _gm(r, a)
    return r


@lru_cache(maxsize=None)
def _cyclo_coeffs(m):
    import sympy
    x = sympy.Symbol("x")
    return tuple(int(c) for c in sympy.Poly(sympy.cyclotomic_poly(m, x), x).all_coeffs())


def cyclo_at(m, u):
    acc = (0, 0)
    for c in _cyclo_coeffs(m):
        acc = _gm(acc, u)
        acc = (acc[0] + c, acc[1])
    return acc


@lru_cache(maxsize=None)
def sqrt_minus_one(p):
    for a in range(2, p):
        x = pow(a, (p - 1) // 4, p)
        if x * x % p == p - 1:
            return min(x, p - x)
    raise ValueError(p)


def sval(w, p):
    """v_P(w) - v_Pbar(w) for the prime P of Z[i] above p (p = 1 mod 4) that contains i - iota,
    iota the smaller square root of -1 modulo p."""
    a, b = w
    while a % p == 0 and b % p == 0:
        a //= p
        b //= p
    N = a * a + b * b
    v = 0
    while N % p == 0:
        N //= p
        v += 1
    if v == 0:
        return 0
    return v if (a + b * sqrt_minus_one(p)) % p == 0 else -v


@lru_cache(maxsize=None)
def atom_of_prime(p):
    """The atom whose norm is the primitive part containing p: (name, Gaussian integer, index n),
    or (None, None, n) when 4 does not divide n = ord_p(2)."""
    import sympy
    n = int(sympy.n_order(2, p))
    if n % 4:
        return None, None, n
    if n % 8 == 4:
        m = n // 4
        A = cyclo_at(m, (1, 1))
        name = "Phi_%d(1+i)" % m
        if _gnorm(A) % p:
            A = cyclo_at(m, (-1, -1))
            name = "Phi_%d(-1-i)" % m
    else:
        e = 0
        while (n >> (e + 3)) % 2 == 0:
            e += 1
        m = n >> (e + 3)
        A = cyclo_at(m, (0, 2 ** (2 ** (e + 1))))
        name = "Phi_%d(%di)" % (m, 2 ** (2 ** (e + 1)))
    assert _gnorm(A) % p == 0, (p, name)
    return name, A, n


def odd_primes_of(N):
    import sympy
    while N % 2 == 0:
        N //= 2
    return sorted(sympy.factorint(N))


def class_vector(x, y):
    g = gcd(x, y)
    x, y = x // g, y // g
    return {p: sval((x, y), p) for p in odd_primes_of(x * x + y * y)}


def arctan_certificate(x, y):
    """Exact certificate that arctan(y/x) = sum e_A arg(A) + (rational) pi over the atoms A.
    Returns (True, description) or (False, reason)."""
    import sympy
    g = gcd(x, y)
    x, y = x // g, y // g
    z = (x, y)
    zprimes = odd_primes_of(x * x + y * y)
    if not zprimes:
        return True, "a multiple of pi/4"
    allp = list(zprimes)
    atoms = {}
    reasons = []
    i = 0
    while i < len(allp):
        p = allp[i]
        i += 1
        name, A, n = atom_of_prime(p)
        if name is None:
            reasons.append("%d: ord_%d(2) = %d is not divisible by 4" % (p, p, n))
            continue
        if name in atoms:
            continue
        R = _gnorm(A)
        for q in set(zprimes) | set(sympy.primefactors(n)):
            while R % q == 0:
                R //= q
        if R != 1:
            reasons.append("%d: its atom %s (norm %s) has a prime factor outside the norm of %d+%di"
                           % (p, name, _short(_gnorm(A)), x, y))
            continue
        atoms[name] = A
        for q in sympy.primefactors(n):
            if q % 4 == 1 and _gnorm(A) % q == 0 and q not in allp:
                allp.append(q)
    names = sorted(atoms)
    rows = [[sval(atoms[nm], p) for p in allp] for nm in names]
    target = [sval(z, p) for p in allp]
    sol = solve(rows, target) if names else None
    if sol is None:
        return False, "; ".join(reasons) if reasons else "the linear system has no solution"
    # exact verification: W = z^k prod A^(-k e_A) has W^4 real
    k = 1
    for s in sol:
        k = k * s.denominator // gcd(k, s.denominator)
    num, den = _gpow(z, k), (1, 0)
    for nm, s in zip(names, sol):
        ex = int(s * k)
        if ex > 0:
            den = _gm(den, _gpow(atoms[nm], ex))
        elif ex < 0:
            num = _gm(num, _gpow(atoms[nm], -ex))
    W = _gm(num, (den[0], -den[1]))
    assert _gpow(W, 4)[1] == 0, (x, y)
    desc = " ".join("%s%s arg %s" % ("+" if s > 0 else "-", "" if abs(s) == 1 else " " + fs(abs(s)), nm)
                    for nm, s in zip(names, sol) if s != 0)
    return True, desc + " (mod Q pi)"


def _short(n):
    s = str(n)
    return s if len(s) <= 14 else s[:6] + "...(%d digits)" % len(s)


def check_arctans(entries, log):
    lists = {"14": [], "15": [], "16": []}
    for e in entries:
        lists[e["content"]["list"]].append(e["content"]["q"])
    res = {}

    def cert(q):
        y, x = [int(t) for t in q.split("/")]
        return arctan_certificate(x, y)

    for L in lists:
        for q in lists[L]:
            ok, desc = cert(q)
            res[(L, q)] = {"certificate": ok, "detail": desc}
    summary = {}
    # duplicates and non-reduced entries
    red = lambda q: fs(Fraction(q))
    notes = []
    for L in lists:
        for q in lists[L]:
            if red(q) != q:
                where = [M for M in lists if red(q) in lists[M]]
                notes.append("%s in list (%s) is not in lowest terms (= %s%s)" % (
                    q, L, red(q), ", which is also in list (%s)" % ", ".join(where) if where else ""))
                res[(L, q)]["note"] = notes[-1]
    both = sorted(set(lists["14"]) & set(lists["16"]), key=lambda q: Fraction(q))
    for q in both:
        notes.append("%s is in both lists (14) and (16)" % q)
        res[("16", q)]["note"] = "also in list (14)"
    summary["notes"] = notes
    # independence of (15), spans
    primes = sorted({p for L in lists for q in lists[L]
                     for p in class_vector(int(q.split("/")[1]), int(q.split("/")[0]))})
    vec = lambda q: [class_vector(int(q.split("/")[1]), int(q.split("/")[0])).get(p, 0) for p in primes]
    r15 = rank([vec(q) for q in lists["15"]])
    summary["rank_15"] = r15
    deps = []
    for cvec in nullspace([vec(q) for q in lists["15"]]):
        tot = sum(mpf(c.numerator) / c.denominator * mp.atan(mpf(Fraction(q).numerator) / Fraction(q).denominator)
                  for c, q in zip(cvec, lists["15"]))
        den = 1
        for c in cvec:
            den = den * c.denominator // gcd(den, c.denominator)
        j = mp.nint(4 * den * tot / mp.pi)                  # the sum is a multiple of pi/(4 den) exactly
        assert abs(4 * den * tot / mp.pi - j) < mpf(10) ** (-60)
        if next(c for c in cvec if c != 0) < 0:
            cvec, j = [-c for c in cvec], -j
        deps.append({"relation": " ".join("%s%s arctan(%s)" % ("+" if c > 0 else "-", "" if abs(c) == 1 else " " + fs(abs(c)), q)
                                          for c, q in zip(cvec, lists["15"]) if c != 0),
                     "pi_multiple": fs(Fraction(int(j), 4 * den))})
    summary["dependencies_15_mod_pi"] = deps
    b15 = [vec(q) for q in lists["15"]]
    not_spanned = []
    for L in ("14", "16"):
        for q in lists[L]:
            inspan = solve(b15, vec(q)) is not None
            res[(L, q)]["in_span_of_15"] = inspan
            if not inspan:
                not_spanned.append("%s (list %s)" % (q, L))
    for q in lists["15"]:
        res[("15", q)]["in_span_of_15"] = True
    summary["not_in_span_of_15"] = not_spanned
    summary["rank_14_16"] = rank([vec(q) for L in ("14", "16") for q in lists[L]])
    # every reduced y/x with y < x <= 50: which have a certificate
    listed = {red(q) for L in lists for q in lists[L]}
    values, nonvalues = [], []
    for x in range(2, 51):
        for y in range(1, x):
            if gcd(x, y) == 1:
                (values if arctan_certificate(x, y)[0] else nonvalues).append("%d/%d" % (y, x))
    summary["values_den_le_50"] = len(values)
    summary["nonvalues_den_le_50"] = len(nonvalues)
    summary["values_not_listed"] = [q for q in values if q not in listed]
    summary["listed_without_certificate"] = sorted({red(q) for q in listed if red(q) not in values and
                                                    Fraction(red(q)).denominator <= 50})
    allvec = []
    allprimes = sorted({p for q in values for p in class_vector(int(q.split("/")[1]), int(q.split("/")[0]))})
    for q in values:
        cv = class_vector(int(q.split("/")[1]), int(q.split("/")[0]))
        allvec.append([cv.get(p, 0) for p in allprimes])
    summary["rank_all_values_den_le_50"] = rank(allvec)
    log("arctangent lists: (14) %d, (15) %d, (16) %d entries; without certificate: %d; rank of (15): %d; "
        "values with denominator <= 50: %d, of which not listed: %d"
        % (len(lists["14"]), len(lists["15"]), len(lists["16"]),
           sum(1 for v in res.values() if not v["certificate"]), r15, len(values), len(summary["values_not_listed"])))
    return res, summary


def gaussian_identity(spec):
    """'5/6=+1/1-1/5+1/9-1/255': the product of the Gaussian integers on the right, divided by
    the one on the left, is a positive rational (so the arctangents agree modulo 2 pi)."""
    lhs, rhs = spec.split("=")
    y, x = [int(t) for t in lhs.split("/")]
    num = (1, 0)
    i = 0
    while i < len(rhs):
        sg = rhs[i]
        j = i + 1
        while j < len(rhs) and rhs[j] not in "+-":
            j += 1
        yy, xx = [int(t) for t in rhs[i + 1:j].split("/")]
        num = _gm(num, (xx, yy if sg == "+" else -yy))
        i = j
    W = _gm(num, (x, -y))
    return W[1] == 0 and W[0] > 0


# =====================================================================================
# 7. Table 1
# =====================================================================================

def lll_count(s, b0, B, n):
    """Number of independent rational relations sum_j a_j P_j = 0 among
    P_j = sum_k b^(-k)/(kn+j)^s (b = b0^B), found numerically by lattice reduction.
    The unknowns are scaled (a_j = b0^(B - ceil(j B/n)) u_j) so that the known relations have
    small integer u.  Evidence, not proof: relations with |u| above the bound are not seen."""
    from flint import fmpz_mat
    W = 64 * n + 600                                     # working bits
    guard = 64
    sums = []
    for prec in (W, 2 * W):
        row = []
        K = prec // (B * (b0.bit_length() - 1)) + 3
        for j in range(1, n + 1):
            w = b0 ** (B - -(-j * B // n))
            acc = 0
            for k in range(K):
                acc += ((w << (prec + guard)) // (k * n + j) ** s) // b0 ** (B * k)
            row.append(acc >> guard)
        sums.append(row)
    M = fmpz_mat([[1 if c == r else 0 for c in range(n)] + [sums[0][r]] for r in range(n)])
    R = M.lll()
    rels = []
    for r in range(n):
        u = [int(R[r, c]) for c in range(n)]
        if max(abs(x) for x in u).bit_length() > W // (2 * n) + 40:
            continue
        resid = sum(a * v for a, v in zip(u, sums[1]))
        # checked against sums computed independently with 2W bits: a relation leaves a
        # residual of the size of u, anything else a residual above 2^W
        if abs(resid).bit_length() < W:
            rels.append(u)
    return rank(rels) if rels else 0


def check_table(rows, formulas, log, use_lll):
    sys.path.insert(0, HERE)
    import derive_bailey_table as dbt
    pats, qs = dbt.load_basis("")
    res = {}
    zero = [f for f in formulas if f["content"].get("zero_relation")]
    for e in rows:
        c = e["content"]
        s, n, count = c["s"], c["n"], c["count"]
        b = ev(c["b"])
        b0, B = root_power(b)
        r = {}
        if s == 1 and b0 == 2:
            if n == 2 * B:
                full, z = dbt.dims(pats, qs, n, False)
                r["lean"] = "PiFormula.Unconditional.bailey_count_F2 (B = %d), bailey_table" % B
            else:
                assert n == B
                full, z = dbt.dims(pats, qs, 2 * n, True)
                r["lean"] = "PiFormula.Unconditional.bailey_count_F1 (B = %d), bailey_table" % B
            r["theorem_count"] = z
            r["pi_formula_with_same_parameters"] = full > z
            r["agrees"] = z == count
        elif s == 1 and b0 == 3:
            z = 2 if (n == 2 * B and B % 6 == 0) else 0
            r["theorem_count"] = z
            r["lean"] = ("PiFormula.Base3.bailey3_count_F2 (2 if 6 | B, else 0), bailey3_729_zero_iff, with "
                         "PiFormula.bakerTheorem for the hypothesis")
            r["agrees"] = z == count
        # printed relations rewritten to this row
        vs = []
        ids = []
        for f in zero:
            v = exact_vector(f)
            if v[0] != s:
                continue
            w = to_frame(v, b, n)
            if w is not None:
                vs.append(w[3])
                ids.append(f["id"])
        r["printed_relations"] = ids
        r["rank_of_printed_relations"] = rank(vs) if vs else 0
        if "agrees" not in r:
            r["agrees"] = None
            r["consistent_with_printed"] = r["rank_of_printed_relations"] <= count
        if use_lll:
            t0 = time.time()
            r["lll_count"] = lll_count(s, b0, B, n)
            r["lll_agrees"] = r["lll_count"] == count
            log("  Table 1 row s=%d b=%s n=%d: printed %d, LLL %d (%.0f s)" % (s, c["b"], n, count, r["lll_count"],
                                                                         time.time() - t0))
        res[e["id"]] = r
    return res


# =====================================================================================
# 8. Assertions
# =====================================================================================

def lincomb_check(rel, byid, proportional=False):
    """target = sum c_i (formula i) as an identity between coefficient vectors (each formula
    taken with its prefactor, so that its series equals its left side), in the common frame."""
    ids = [rel["target"]] + [t[1] for t in rel["terms"]]
    vecs = {i: exact_vector(byid[i]) for i in ids}
    nmax = max(v[2] for v in vecs.values())
    frame_b = None
    for v in vecs.values():
        if v[2] == nmax:
            frame_b = v[1]
    fr = {}
    for i, v in vecs.items():
        w = to_frame(v, frame_b, nmax)
        if w is None:
            return {"ok": False, "detail": "formula %s cannot be rewritten to base %s, length %d" % (i, frame_b, nmax)}
        fr[i] = w[3]
    comb = [Fraction(0)] * nmax
    for co, i in rel["terms"]:
        cf = Fraction(ev(co))
        comb = [a + cf * b for a, b in zip(comb, fr[i])]
    tgt = fr[rel["target"]]
    if comb == tgt:
        return {"ok": True, "detail": "exact identity of coefficient vectors in P(s, %s, %d, .)" % (_bstr(frame_b), nmax)}
    if proportional:
        lam = None
        ok = True
        for a, b in zip(comb, tgt):
            if b == 0 and a == 0:
                continue
            if b == 0 or a == 0:
                ok = False
                break
            lam = a / b if lam is None else lam
            if a / b != lam:
                ok = False
                break
        if ok and lam is not None:
            return {"ok": True, "detail": "the combination equals %s times the vector of %s" % (fs(lam), rel["target"])}
    # corrected coefficients of the zero relations, the other terms kept as printed
    zr = [i for _, i in rel["terms"] if byid[i]["content"].get("zero_relation")]
    fixed = [Fraction(0)] * nmax
    for co, i in rel["terms"]:
        if i not in zr:
            fixed = [a + Fraction(ev(co)) * b for a, b in zip(fixed, fr[i])]
    x = solve([fr[i] for i in zr], [a - b for a, b in zip(tgt, fixed)]) if zr else None
    if x is not None:
        return {"ok": False, "corrected": {i: fs(xi) for i, xi in zip(zr, x)},
                "detail": "the vectors differ; the identity holds exactly with the coefficients %s (printed: %s)"
                % (", ".join("%s for relation %s" % (fs(xi), i) for i, xi in zip(zr, x)),
                   ", ".join("%s for %s" % (co, i) for co, i in rel["terms"] if i in zr))}
    # is the difference at least a zero relation numerically?
    diff = [a - b for a, b in zip(comb, tgt)]
    s = vecs[rel["target"]][0]
    val = P_value(s, frame_b, nmax, diff)
    sc = P_scale(s, nmax, diff)
    return {"ok": False, "detail": "vectors differ; P of the difference / scale = %s" % mp.nstr(val / sc, 5),
            "difference_is_zero_relation": bool(abs(val) < sc * mpf(10) ** (-NEED_DIGITS))}


def _bstr(b):
    b0, B = root_power(b)
    return ("-" if b < 0 else "") + ("%d^%d" % (b0, B) if B > 1 else str(b0))


def equivalent(a, b, byid):
    va, vb = exact_vector(byid[a]), exact_vector(byid[b])
    n = max(va[2], vb[2])
    fa = va if va[2] == n else rewrite(va, n // va[2])
    fb = vb if vb[2] == n else rewrite(vb, n // vb[2])
    if fa[1] < 0 or fb[1] < 0:
        fa, fb = rewrite(fa, 2), rewrite(fb, 2)
    return fa[1] == fb[1] and fa[3] == fb[3]


# =====================================================================================
# 9. Statuses of the prose assertions
# =====================================================================================
# Statuses that are not the result of a computation are written here by hand, with the
# theorem of the project that settles the question.

FIXED = {
    "none:algorithmic": ("not checked", "a property of the digit algorithm, not an identity"),
    "none:attribution": ("attribution, not checked", "the cited source is not in the repository"),
    "none:conjecture": ("open", "a conjecture; nothing in the project bears on it"),
    "none:conditional": ("not checked", "a conditional statement resting on Hypothesis A"),
    "none:method": ("no claim to check", "description of a method"),
    "none:definition": ("definition", ""),
    "none:general": ("not checked", "general remark"),
    "none:trivial": ("confirmed", "linearity of the series"),
    "overstated_bbg": (
        "OVERSTATED attribution; the statement itself is now a theorem",
        "The cited paper (local copy read: Canad. J. Math. 56 (2004) 897-925, Theorem 7, p. 918) excludes only "
        "Machin-type arctangent formulas, pi = sum a_m arctan(b^(-m)), for b > 2 not a proper power, and poses "
        "the general degree-1 question as its open problem (10). The general statement (no degree-1 BBP-type "
        "formula P(1, b^B, N, A) for a non-zero rational multiple of pi unless b is a power of 2) is Theorem L "
        "of the project: PiFormula.BaseB.no_pi_bailey, bailey_pi_iff, no_pi_bailey_comb, no_pi_bailey_int "
        "(Lean, no hypothesis)."),
    "two_bases": (
        "remark, not checked",
        "Relevant theorems of the project: pi has a degree-1 formula only in bases 2^m (Theorem L); log 2 and "
        "log 3 have degree-1 formulas in base 2 and in base 3 (formulas 7, 8, 67, 70; Theorems K, K3); log b has "
        "one in base b iff b is a power of 2 or 3 (Theorem M)."),
    "same_base_sum": (
        "confirmed (elementary)",
        "Lean: PiFormula.BaseB.exists_bailey_add, exists_bailey_of_sum (series of bases b^B1, b^B2 combine into one)."),
    "xref_section_11": (
        "editorial slip", "the zero relations are in Section 12; Section 11 is 'General bases'"),
    "log_closed_under_products": (
        "confirmed", "the values of class F form a rational vector space; Lean: PiFormula.IsFValue.add, IsFValue.const_mul"),
    "log_two_pow_pm_one": (
        "confirmed",
        "Lean: PiFormula.isFValue_log_two_pow_sub_one (log(2^m - 1) is a value for every m >= 1; "
        "2^n + 1 = (2^(2n) - 1)/(2^n - 1)); which primes arise is decided by Theorem K"),
    "harley_series": (
        "confirmed",
        "Lean: PiFormula.isFValue_gen, isFValue_log_L, isFValue_log_M: log(2^N -+ 2^((N+1)/2) + 1) is a value of F "
        "for every odd N (here N = 2n - 1)"),
    "borwein_single_expression": (
        "confirmed, and it is all there is",
        "Theorem K (PiFormula.Unconditional.isFValue_log_rat_iff_pow): log y has a formula in class F iff a power "
        "of y is a product of powers of 2 and of the norms |(1+i)^n - c|^2, c in {1, -1, i, -i}"),
    "unknown_all_primes": (
        "SETTLED by the project: no",
        "log 23 has no formula in class F (Theorem G: PiFormula.Unconditional.no_log23, bailey_no_log23_F2, "
        "bailey_no_log23_F1); below 100 exactly the 15 listed primes have one (Theorem H: log_primes_below_100); "
        "a finite test decides every prime (isFValue_log_prime_classification). Scope: series P(1, 2^B, n, A) "
        "with n = B or n = 2B; other lengths n are not formalized."),
    "unknown_finite_infinite": (
        "OPEN (not settled by the project)",
        "Theorem K reduces it to arithmetic: p qualifies iff the primitive part of 2^n - 1, n = ord_p(2) (or its "
        "Aurifeuillian half when n = 4 mod 8), is p^x or p^x q with q a qualifying prime factor of n. Whether "
        "this happens for infinitely many n is unknown (it would follow from infinitely many Mersenne primes)."),
    "list9_formulas": (
        "not checked one by one", "existence for each listed prime follows from the criterion (see the list entries)"),
    "nonbinary_logs": (
        "formula 84 confirmed numerically; the digit computation is not checked",
        "Project: criteria K3 and K5 for bases 3 and 5; Theorem M (PiFormula.BaseB.bailey_log_self_iff, "
        "no_log_bailey_ten): log b has a degree-1 formula of base b iff b is a power of 2 or 3, so log 2, log 5, "
        "log 10 have none in base 10"),
    "arctan_T_positive": (
        "confirmed (the positive half)",
        "1 +- (1+i)^u/2^v is a unit times ((1+i)^n - c)/(1+i)^n or its inverse; Lean: PiFormula.hasSum_gamma, "
        "exp_gamma, isFValue_gamma_gen (as used for isFValue_arctan_inv_129)"),
    "unknown_arctan_2_7": (
        "SETTLED by the project: no",
        "Theorem I: PiFormula.Unconditional.not_isFValue_arctan_two_sevenths, no_arctan_two_sevenths, "
        "bailey_no_arctan_two_sevenths_F2, bailey_no_arctan_two_sevenths_F1 (also arctan(5/8) and arctan(4/9)); "
        "arctan(2/7) + arctan(6/11) is a value (isFValue_arctan_two_sevenths_add)."),
    "attribution_sec5": (
        "attributions not checked, one consistency check",
        "the abstract of the local copy of [12] (arXiv:1603.07395v1) announces binary formulas for pi sqrt(3) log 2 "
        "and sqrt(3) Cl_2(pi/3), consistent with the attribution of 36 and 37"),
    "attribution_sec12": (
        "attributions not checked",
        "relations 130 and 131 are Lean theorems here (PiFormula.Base3.relation130, relation131); 111-122 follow "
        "from Theorem C with the coordinates given at each entry"),
    "unknown_e": ("OPEN (not addressed by the project)", ""),
    "unknown_why_zero_relations": (
        "SETTLED by the project for degree 1; open for degree >= 2",
        "Degree 1, base 2: the zero relations of P(1, 2^B, 2B, .) have dimension 1, 1, 5, 3, 1, 7 when "
        "gcd(2B, 120) = 8, 12, 24, 40, 60, 120 and 0 otherwise; those of P(1, 2^B, B, .) dimension 1 if 6 | B, "
        "else 0 (Theorem C; PiFormula.Unconditional.bailey_count_F2, bailey_count_F1), with explicit bases. "
        "Base 3: 2 if 6 | B (n = 2B), else 0 (PiFormula.Base3.bailey3_count_F2, bailey3_count_F1). Every base "
        "b >= 5: none (Theorem G, PiFormula.BaseB.Unconditional.eq_zero_of_hasSum_zero). The reason is the "
        "finite list of multiplicative relations among 1 - r/(1+i), r a root of unity. Nothing is proved here "
        "for s >= 2."),
    "citation_bbg": (
        "citation slip",
        "checked against the local copy of the paper: Canad. J. Math. 56 (5), 2004, pp. 897-925, authors "
        "J. M. Borwein, D. Borwein, W. F. Galway; the page range 1339-1342 and the order of the authors do not match"),
}


def run_assertions(E, byid, log, primes_summary, arct, table_res):
    arct_res, arct_sum = arct
    res = {}

    def put(e, status, detail="", **kw):
        d = {"status": status, "detail": detail}
        d.update(kw)
        res[e["id"]] = d

    numeric_ok = lambda i: byid[i]["checks"].get("numeric", {}).get("status") == "agree"
    for e in E:
        c = e["content"]
        chk = c.get("check")
        if e["kind"] not in ("assertion", "formula") or not chk:
            continue
        if chk in FIXED:
            put(e, *FIXED[chk])
        elif chk.startswith("refs:"):
            ids = chk[5:].split(",")
            put(e, "confirmed" if all(numeric_ok(i) for i in ids) else "NOT CONFIRMED",
                "formulas %s agree numerically" % ", ".join(ids))
        elif chk == "bbp_single_fraction":
            ok = all(Fraction(4, 8 * k + 1) - Fraction(2, 8 * k + 4) - Fraction(1, 8 * k + 5) - Fraction(1, 8 * k + 6)
                     == Fraction(47 + 151 * k + 120 * k * k,
                                 15 + 194 * k + 712 * k ** 2 + 1024 * k ** 3 + 512 * k ** 4) for k in range(0, 40))
            put(e, "confirmed (exact)" if ok else "DISAGREES",
                "equal to the summand of formula (1) as rational functions (40 integer points; degree at most 8)")
        elif chk == "bbp_iteration_term":
            ok = all(Fraction(120 * n * n - 89 * n + 16, 512 * n ** 4 - 1024 * n ** 3 + 712 * n * n - 206 * n + 21)
                     == Fraction(4, 8 * n - 7) - Fraction(2, 8 * n - 4) - Fraction(1, 8 * n - 3) - Fraction(1, 8 * n - 2)
                     for n in range(1, 41))
            put(e, "the rational function is confirmed (exact); the implication is conditional, not checked"
                if ok else "DISAGREES", "r_n equals the summand of formula (1) at k = n - 1")
        elif chk == "rewriting_rule":
            ok = True
            for i, r in (("17", 2), ("21", 3), ("67", 2), ("111", 3)):
                v = exact_vector(byid[i])
                w = rewrite(v, r)
                ok &= abs(P_value(*v) - P_value(*w)) < mpf(10) ** (-NEED_DIGITS)
            put(e, "confirmed" if ok else "DISAGREES",
                "a'_(mn+j) = a_j b^(-m); checked numerically on formulas 17, 21, 67, 111 and used for every "
                "comparison of vectors in this ledger")
        elif chk == "paper_self_check":
            bad = [f["id"] for f in E if f["kind"] == "formula" and f["content"].get("type") == "P"
                   and f["checks"].get("numeric", {}).get("status") != "agree"]
            put(e, "consistent with our check" if not bad else "NOT consistent: " + ", ".join(bad),
                "every P-notation formula agrees here to at least %d digits; two are not well formed as printed "
                "(91: b - 1 entries for length b; 100: unbalanced parenthesis)" % NEED_DIGITS)
        elif chk == "aurifeuille":
            ok = all(2 ** (4 * n - 2) + 1 == (2 ** (2 * n - 1) + 2 ** n + 1) * (2 ** (2 * n - 1) - 2 ** n + 1)
                     for n in range(1, 60))
            put(e, "confirmed (exact)" if ok else "DISAGREES",
                "(a + 1)^2 - b^2 with a = 2^(2n-1), b = 2^n, b^2 = 2a; checked for n < 60; Lean: PiFormula.aurifeuille")
        elif chk == "catalan_definition":
            ok = mp.nstr(mp.catalan, 12).startswith(c["printed_value"])
            put(e, "confirmed" if ok else "DISAGREES", "the printed decimals agree with Catalan's constant")
        elif chk == "list9_incomplete":
            m = primes_summary["passing_not_listed"]
            put(e, "confirmed" if m else "NOT CONFIRMED",
                "%d primes up to the largest entry pass the criterion of Theorem K; %d of them are not in list (9): %s. "
                "Assumption: %s" % (primes_summary["passing_up_to_largest"], len(m), ", ".join(map(str, m)),
                                    primes_summary["assumption"]), missing=m)
        elif chk == "arctan_T_set":
            nolist = arct_sum["listed_without_certificate"]
            put(e, "confirmed for the listed rationals; the lists are not the whole set",
                "every rational of lists (14), (15), (16) has an exact certificate (a product of atoms, hence of "
                "factors of the form (11)); listed rationals without certificate: %s. Of the %d reduced y/x with "
                "y < x <= 50 that have a certificate, %d are in none of the lists: %s"
                % (", ".join(nolist) or "none", arct_sum["values_den_le_50"], len(arct_sum["values_not_listed"]),
                   ", ".join(arct_sum["values_not_listed"])))
        elif chk == "form12_is_form11":
            ok = all(_gm(_gpow((1, 1), 2), (1, 0)) == (0, 2) for _ in range(1))
            put(e, "confirmed (exact)" if ok else "DISAGREES",
                "i/2^t = (1+i)^2/2^(t+1): the first factor of (12) is a factor of (11) with u = 2")
        elif chk == "T_example":
            def fac(sign, num, k):          # 1 + sign * num / 2^k as a pair of Fractions
                return (1 + sign * Fraction(num[0], 2 ** k), sign * Fraction(num[1], 2 ** k))
            fm = lambda a, b: (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])
            T = (Fraction(1), Fraction(0))
            for f in (fac(1, (0, 1), 1), fac(-1, (1, 1), 1), fac(-1, (0, 1), 1), fac(1, (1, 1), 3)):
                T = fm(T, f)
            ok = T == (Fraction(25, 32), Fraction(-5, 8)) and abs(T[1] / T[0]) == Fraction(4, 5)
            put(e, "confirmed (exact)" if ok else "DISAGREES",
                "(1 + i/2)(1 - (1+i)/2)(1 - i/2)(1 + (1+i)/8) = %s + (%s) i" % (fs(T[0]), fs(T[1])))
        elif chk == "list14_count":
            n14 = sum(1 for f in E if f["kind"] == "list entry" and f["content"]["list"] == "14")
            bad = [q for (L, q), v in arct_res.items() if L == "14" and not v["certificate"]]
            put(e, "confirmed" if not bad else "NOT CONFIRMED for " + ", ".join(bad),
                "%d rationals; each has an exact certificate that arctan q is a rational combination of pi and "
                "arguments of atoms, so a series of class F (positive half, as in Arctan.lean)" % n14)
        elif chk.startswith("gaussian:"):
            ok = gaussian_identity(chk[9:])
            put(e, "confirmed (exact)" if ok else "DISAGREES", "product of Gaussian integers is a positive rational multiple")
        elif chk == "arctan_three":
            oks = [arctan_certificate(6, 1), arctan_certificate(6, 5), arctan_certificate(11, 1)]
            put(e, "confirmed" if all(o[0] for o in oks) else "NOT CONFIRMED",
                "exact certificates: 1/6: %s; 5/6: %s; 1/11: %s" % tuple(o[1] for o in oks))
        elif chk == "list15_independent":
            deps = arct_sum["dependencies_15_mod_pi"]
            indep = all(d["pi_multiple"] != "0" for d in deps) and len(deps) <= 1
            put(e, "confirmed (exact): independent over Q; but pi lies in their span" if indep and deps
                else ("confirmed (exact)" if indep else "DISAGREES"),
                "by unique factorization in Z[i] the rational relations among the 15 arctangents and pi are "
                "spanned by: %s. So the 15 numbers are linearly independent over Q (the paper says 'appear to "
                "be'), they span a space of dimension 15 that contains pi, and modulo Q pi their rank is %d."
                % ("; ".join("%s = %s pi" % (d["relation"], d["pi_multiple"]) for d in deps) or "none",
                   arct_sum["rank_15"]))
        elif chk == "list15_spans":
            ns = arct_sum["not_in_span_of_15"]
            put(e, "confirmed (exact)" if not ns else "NOT CONFIRMED for " + ", ".join(ns),
                "each rational of (14) and (16) has its prime-exponent vector in the span of those of (15) "
                "(a relation modulo Q pi); rank of (14) and (16) together: %d. Slips: %s"
                % (arct_sum["rank_14_16"], "; ".join(arct_sum["notes"]) or "none"))
        elif chk == "lists_gaps":
            put(e, "confirmed, and made precise",
                "of the %d reduced y/x with y < x <= 50, %d have a certificate (arctan is a value of F) and %d do "
                "not; the %d values missing from lists (14), (16) and {1/6, 5/6}: %s. All values with denominator "
                "<= 50 span a space of dimension %d modulo Q pi; the set (15) spans 14 of them, so it is "
                "not a basis of all values (arctan(23/30) and arctan(5/36) bring the primes 1429 and 1321). "
                "A certificate proves that arctan q is a value of F. That a rational without certificate is "
                "not a value follows from Baker's theorem by the argument of Theorem I; this is formalized for "
                "2/7, 5/8 and 4/9 only (none of the three, nor 6/11, is listed)."
                % (arct_sum["values_den_le_50"] + arct_sum["nonvalues_den_le_50"], arct_sum["values_den_le_50"],
                   arct_sum["nonvalues_den_le_50"],
                   len([q for q in arct_sum["values_not_listed"] if q not in ("1/6", "5/6")]),
                   ", ".join(q for q in arct_sum["values_not_listed"] if q not in ("1/6", "5/6")),
                   arct_sum["rank_all_values_den_le_50"]))
        elif chk == "arctan_5_36":
            ok, desc = arctan_certificate(36, 5)
            put(e, "the statement is confirmed (exact certificate); the attribution is not confirmed" if ok
                else "NOT CONFIRMED",
                "36 + 5i has norm 1321 and arctan(5/36) = %s. In the local copy of [12] (arXiv:1603.07395v1) "
                "Section 6.1.4 gives a formula for arctan(1/6); '5/36' does not occur in its extracted text. "
                "5/36 has denominator <= 50 and is in neither list." % desc)
        elif chk.startswith("equiv:"):
            pairs = [p.split("=") for p in chk[6:].split(",")]
            ok = all(equivalent(a, b, byid) for a, b in pairs)
            put(e, ("confirmed (exact)" if ok else "DISAGREES") + "; attribution not checked",
                "identical coefficient vectors after rewriting to a common base and length: "
                + ", ".join("%s and %s" % (a, b) for a, b in pairs))
        elif chk in ("lincomb", "lincomb_proportional"):
            r = lincomb_check(c["relation"], byid, proportional=(chk == "lincomb_proportional"))
            if r["ok"]:
                put(e, "confirmed (exact)", r["detail"])
            else:
                put(e, "DISAGREES as printed", r["detail"], **{k: v for k, v in r.items() if k not in ("ok", "detail")})
        elif chk == "lafont_is_70":
            v = exact_vector(byid["70"])
            ok = v[1] == 9 and v[2] == 2 and v[3] == [Fraction(1), Fraction(1, 9)]
            put(e, "confirmed (exact)" if ok else "DISAGREES",
                "Lafont's series is (1/9) P(1, 9, 2, (9, 1)) term by term; Lean: PiFormula.BaseB.hasSum_log_three")
        elif chk == "table1_overview":
            rows = [f for f in E if f["kind"] == "table row"]
            ag = [f["id"] for f in rows if table_res[f["id"]].get("agrees")]
            dis = [f["id"] for f in rows if table_res[f["id"]].get("agrees") is False]
            hi = [f["id"] for f in rows if table_res[f["id"]].get("agrees") is None]
            put(e, "degree-1 rows confirmed by theorem; higher-degree rows consistent",
                "%d rows of degree 1 equal the count of Theorems C / C3 (Lean); disagreeing: %s; %d rows of degree "
                ">= 2 have no theorem: the printed relations, rewritten, never exceed the count" %
                (len(ag), ", ".join(dis) or "none", len(hi)))
        elif chk == "five_relations_113_118":
            vs = [exact_vector(byid[str(i)])[3] for i in range(113, 119)]
            r = rank(vs)
            put(e, "count 5 confirmed (theorem); but six relations are printed under these numbers",
                "113-118 are six vectors of rank %d; the dimension 5 is PiFormula.Unconditional.bailey_count_F2 "
                "at B = 12 (zeroCount 24 = 5); 114 (credited to Oliver Lafont) is a combination of the others" % r,
                rank=r)
        elif chk == "positions_113_118":
            pos = []
            for i in range(113, 119):
                A = exact_vector(byid[str(i)])[3]
                pos.append(max(j for j, a in enumerate(A, 1) if a != 0))
            put(e, "editorial slip" if pos != [23, 22, 21, 20, 19] else "confirmed",
                "last non-zero positions of 113, ..., 118: %s; the sentence fits the five relations 113, 115, 116, "
                "117, 118 (114 also ends at position 23)" % pos, positions=pos)
        elif chk == "zero_relation_vs_formula":
            no = ["b=%s, n=%d" % (f["content"]["b"], f["content"]["n"]) for f in E if f["kind"] == "table row"
                  and table_res[f["id"]].get("pi_formula_with_same_parameters") is False]
            put(e, "made precise for degree 1, base 2",
                "by Theorem C a formula for a non-zero rational multiple of pi exists with the same parameters in "
                "every row of Table 1 of degree 1 and base 2 except: %s. There no rational multiple of pi is a "
                "value; other constants still are (formula 21 for pi sqrt(3) has b = 64, n = 6)."
                % ("; ".join(no) or "none"))
        elif chk == "last_two_nonbinary":
            zs = [f for f in E if f["kind"] == "formula" and f["content"].get("zero_relation")]
            roots = [root_power(ev(f["base"]))[0] for f in zs]
            ok = roots[-2:] == [3, 3] and all(r == 2 for r in roots[:-2])
            put(e, "confirmed" if ok else "DISAGREES", "111-129 have base 2^m; 130 and 131 have base 3^6")
        elif chk == "golden_base":
            phi = (1 + mp.sqrt(5)) / 2
            ok = abs(2 / phi - (2 * phi - 2)) < mpf(10) ** (-90)
            put(e, "identity confirmed; editorial slip in the cross-reference" if ok else "DISAGREES",
                "2/phi = 2 phi - 2 because phi^2 = phi + 1; the golden mean is introduced in Sections 4 and 10, not 9")
        else:
            raise KeyError(chk)
    return res


# =====================================================================================
# 10. Main
# =====================================================================================

MANUAL_CLASS = {
    "4": "the series of formula 7: F (base 2), step 1",
    "p02.g": "the series of formula 1 with its four fractions combined: F (base 2), step 2, period 8",
    "p04.b": "telescoping example with rational value; not a constant of interest",
    "p05.c": "the derivation of formula 8: F (base 2), step 1 (weights 2^(-k)) after rewriting 4^(-k)",
    "p05.e": "identity behind the series of log |(1+i)^n -+ ...|; closed form, no series",
    "p25.b": "base 9, length 2 after shifting the index: F3 (base 3), step 1; equals formula 70 plus a telescoping part",
    "p25.c": "the series of formula 70: F3 (base 3), step 1",
    "133": "not a BBP-type series (coefficients D_k from a recurrence)",
    "132": "irrational base (2/phi)^10: outside every class of the project",
}


def short_formula(e):
    c = e["content"]
    t = c.get("type")
    if t == "P":
        r = c["rhs"][0]
        A = r["A"]
        if isinstance(A, dict):
            vec = A["printed"] + " [length b; see note]"
        elif len(A) <= 12:
            vec = "(" + ", ".join(A) + ")"
        else:
            vec = "A: %d entries, in ledger.json" % len(A)
        co = "" if r["coef"] == "1" else ("(%s) " % r["coef"] if any(ch in r["coef"] for ch in "/*^") else r["coef"] + " ")
        return "%s = %sP(%d, %s, %s, %s)" % (c["lhs"], co, r["s"], r["b"], r["n"], vec)
    if t == "series":
        pre = "" if c["prefactor"] == "1" else "(%s) " % c["prefactor"]
        ct = c["constant_term"] + " + " if "constant_term" in c else ""
        return "%s = %s%ssum_{k>=%d} %s" % (c["lhs"], ct, pre, c["k0"], c["term"])
    if t == "recurrence_series":
        return "%s = (%s) sum_{k>=0} %s, D_0 = D_1 = 1, %s" % (c["lhs"], c["prefactor"], c["term"], c["recurrence"]["rule"])
    if t == "identity":
        return "%s = %s" % (c["lhs"], c["rhs"])
    if t == "chain":
        return "%s = %s = (three series, in ledger.json)" % (c["lhs"], c["steps"][0])
    if t == "exact":
        return c["statement"]
    return ""


def md_escape(s):
    return str(s).replace("|", "\\|").replace("\n", " ")


def write_md(led, stats):
    E = led["entries"]
    L = []
    L.append("# Ledger: D. H. Bailey, A Compendium of BBP-Type Formulas for Mathematical Constants (8 April 2023)")
    L.append("")
    L.append("Generated by `python/compendium_check.py --write` from `ledger.json` (the source of truth; the long "
             "coefficient vectors are only there). One row per numbered formula, table row, list entry and prose "
             "assertion of the paper. Formulas are in the paper's notation "
             "P(s, b, n, A) = sum_{k>=0} b^(-k) sum_{j=1..n} a_j/(kn+j)^s, written in ASCII (^ is a power; "
             "cl(n, t) the Clausen function; phi the golden mean). Statements are in our words.")
    L.append("")
    L.append("Column R (reading): T = read from the text layer of the PDF (superscripts from glyph positions), "
             "I = read on the page image, U = uncertain reading. Column s is the degree, b the base.")
    L.append("")
    L.append("Counts: %s." % "; ".join("%s: %d" % kv for kv in stats))
    L.append("")
    secs = []
    for e in E:
        if e["section"] not in secs:
            secs.append(e["section"])
    rd = {"read from text": "T", "read from page image": "I", "uncertain reading": "U"}
    for sec in secs:
        L.append("## " + sec)
        L.append("")
        ents = [e for e in E if e["section"] == sec]
        main = [e for e in ents if e["kind"] in ("formula", "assertion")]
        if main:
            L.append("| ID | p. | kind | content | s | b | R | status |")
            L.append("|---|---|---|---|---|---|---|---|")
            for e in main:
                content = short_formula(e) if e["kind"] == "formula" else e["content"]["statement"]
                if e.get("reading_note") and e["kind"] == "formula" and len(e["reading_note"]) < 90:
                    content += " [" + e["reading_note"] + "]"
                kind = "zero relation" if e["content"].get("zero_relation") else e["kind"]
                L.append("| %s | %d | %s | %s | %s | %s | %s | %s |" % (
                    e["id"], e["page"], kind, md_escape(content), e["degree"] if e["degree"] else "",
                    md_escape(e["base"] or ""), rd[e["reading"]], md_escape(e.get("status", ""))))
            L.append("")
        for lst, title, cols in (("9", "List (9): primes p with a binary formula for log p", None),
                                 ("14", "List (14): rationals q with a binary formula for arctan q", None),
                                 ("15", "List (15): the reduced set", None),
                                 ("16", "List (16): further rationals", None)):
            le = [e for e in ents if e["kind"] == "list entry" and e["content"]["list"] == lst]
            if not le:
                continue
            L.append("### " + title + " (%d entries, page %d, R = T)" % (len(le), le[0]["page"]))
            L.append("")
            if lst == "9":
                L.append("| ID | p | criterion of Theorem K | primitive part | Lean |")
                L.append("|---|---|---|---|---|")
                for e in le:
                    k = e["checks"]["criterion"]
                    L.append("| %s | %s | %s | %s | %s |" % (e["id"], e["content"]["p"], k["criterion"],
                                                             md_escape(k["explain"]), md_escape(k["lean"])))
            else:
                L.append("| ID | q | status | certificate: arctan q = ... (mod Q pi) |")
                L.append("|---|---|---|---|")
                for e in le:
                    k = e["checks"]["certificate"]
                    L.append("| %s | %s | %s | %s |" % (e["id"], e["content"]["q"], md_escape(e.get("status", "")),
                                                       md_escape(k["detail"])))
            L.append("")
        tr = [e for e in ents if e["kind"] == "table row"]
        if tr:
            L.append("### Table 1: number of independent zero relations (page %d, R = I)" % tr[0]["page"])
            L.append("")
            L.append("| ID | s | b | n | printed | theorem | printed relations (rank) | lattice count | status |")
            L.append("|---|---|---|---|---|---|---|---|---|")
            for e in tr:
                c, k = e["content"], e["checks"]["table"]
                L.append("| %s | %d | %s | %d | %d | %s | %s | %s | %s |" % (
                    e["id"], c["s"], c["b"], c["n"], c["count"],
                    k.get("theorem_count", "none"),
                    (", ".join(k["printed_relations"]) + " (%d)" % k["rank_of_printed_relations"]) if k["printed_relations"] else "none",
                    k.get("lll_count", "not run"), md_escape(e.get("status", ""))))
            L.append("")
    io.open(LEDGER_MD, "w", encoding="utf-8", newline="\n").write("\n".join(L) + "\n")


def main():
    args = sys.argv[1:]
    write = "--write" in args
    use_lll = "--lll" in args
    mp.dps = 100
    for i, a in enumerate(args):
        if a == "--dps":
            mp.dps = int(args[i + 1])
    led = json.load(io.open(LEDGER, encoding="utf-8"))
    E = led["entries"]
    byid = {e["id"]: e for e in E}

    def log(s):
        print(s)

    t0 = time.time()
    old_lll = {e["id"]: e["checks"].get("table", {}).get("lll_count") for e in E if e["kind"] == "table row"}
    for e in E:
        e["checks"] = {}
        e.pop("status", None)
    formulas = [e for e in E if e["kind"] == "formula"]
    # ---- 1. numerics
    bad = []
    for e in formulas:
        try:
            r = check_formula_numeric(e)
        except Exception as ex:
            r = {"status": "ERROR", "detail": "%s: %s" % (type(ex).__name__, ex)}
        if r is not None:
            e["checks"]["numeric"] = r
            if r["status"] != "agree":
                bad.append(e["id"])
                log("  formula %s: %s %s" % (e["id"], r["status"], r.get("digits", r.get("detail"))))
    nform = sum(1 for e in formulas if "numeric" in e["checks"])
    log("numerics: %d formulas evaluated with %d digits; agreeing to at least %d digits: %d; not agreeing: %s"
        % (nform, mp.dps, NEED_DIGITS, nform - len(bad), ", ".join(bad) or "none"))
    # ---- 2. degree 1
    sys.path.insert(0, HERE)
    import derive_bailey_table as dbt
    named, env = project_bases()
    pats, qs = dbt.load_basis("")
    pats = [[p[k % 120] for k in range(1, 121)] for p in pats]
    bases = (named, env, (pats, qs))
    b3 = base3_patterns()
    for e in formulas:
        if e["degree"] == 1:
            if e["content"]["type"] == "P" and e["id"] != "132":
                d = degree1_status(e, bases, b3)
            else:
                d = {"class": MANUAL_CLASS[e["id"]], "from_classification": "no"}
            d["lean"] = LEAN_SAME.get(e["id"]) or LEAN_EXISTS.get(e["id"]) or "none"
            d["lean_same_statement"] = e["id"] in LEAN_SAME
            e["checks"]["degree1"] = d
        elif e["degree"]:
            e["checks"]["proof"] = {"lean": "not attempted", "ingredients": ingredients(e)}
    # the same coefficient vector (up to a factor) used at another degree
    shape = {}
    for e in formulas:
        v = exact_vector(e, bare=True)
        if v is None or not any(v[3]):
            continue
        lead = next(a for a in v[3] if a != 0)
        shape.setdefault((v[1], v[2], tuple(a / lead for a in v[3])), []).append(e)
    for same in shape.values():
        if len({f["degree"] for f in same}) > 1:
            for f in same:
                others = ["%s (degree %d)" % (g["id"], g["degree"]) for g in same if g["degree"] != f["degree"]]
                f["checks"].setdefault("proof" if f["degree"] > 1 else "degree1", {})["same_vector_as"] = others
                if f["degree"] > 1:
                    f["checks"]["proof"]["ingredients"] += "; same coefficient vector as " + ", ".join(others)
    # ranks of the groups of printed zero relations
    groups = {}
    for e in formulas:
        if e["content"].get("zero_relation"):
            v = exact_vector(e)
            groups.setdefault((v[0], v[1], v[2]), []).append((e["id"], v[3]))
    for (s, b, n), items in groups.items():
        r = rank([v for _, v in items])
        for i, _ in items:
            byid[i]["checks"]["group"] = {"same_parameters": [j for j, _ in items], "rank": r}
    log("degree 1: %d formulas; class, coordinates and Lean names recorded" % sum(1 for e in formulas if e["degree"] == 1))
    # ---- 3. lists
    pr = [e for e in E if e["kind"] == "list entry" and e["content"]["list"] == "9"]
    pres, psum = check_primes(pr, log)
    for e in pr:
        e["checks"]["criterion"] = pres[int(e["content"]["p"])]
    ar = [e for e in E if e["kind"] == "list entry" and e["content"]["list"] in ("14", "15", "16")]
    ares, asum = check_arctans(ar, log)
    for e in ar:
        e["checks"]["certificate"] = ares[(e["content"]["list"], e["content"]["q"])]
    # ---- 4. Table 1
    rows = [e for e in E if e["kind"] == "table row"]
    tres = check_table(rows, formulas, log, use_lll)
    for e in rows:
        e["checks"]["table"] = tres[e["id"]]
        if not use_lll and old_lll.get(e["id"]) is not None:       # keep an earlier --lll result
            tres[e["id"]]["lll_count"] = old_lll[e["id"]]
            tres[e["id"]]["lll_agrees"] = old_lll[e["id"]] == e["content"]["count"]
    log("Table 1: %d rows; degree-1 rows agreeing with the theorems: %d of %d; higher-degree rows consistent with "
        "the printed relations: %d of %d" % (
            len(rows), sum(1 for r in tres.values() if r["agrees"]), sum(1 for r in tres.values() if r["agrees"] is not None),
            sum(1 for r in tres.values() if r.get("consistent_with_printed")),
            sum(1 for r in tres.values() if r["agrees"] is None)))
    # ---- 5. assertions
    asr = run_assertions(E, byid, log, psum, (ares, asum), tres)
    for i, r in asr.items():
        byid[i]["checks"]["assertion"] = r
    led["summaries"] = {"primes": psum, "arctangents": asum}
    # ---- statuses
    for e in E:
        k = e["checks"]
        if e["kind"] == "formula":
            parts = []
            if "numeric" in k:
                parts.append("numerically confirmed (%d digits)" % k["numeric"]["digits"] if k["numeric"]["status"] == "agree"
                             else "NUMERICAL " + k["numeric"]["status"])
            if "assertion" in k:
                parts.append(k["assertion"]["status"])
            if "degree1" in k:
                d = k["degree1"]
                if d.get("lean_same_statement"):
                    parts.append("Lean: " + d["lean"])
                elif "coordinates_named" in d:
                    parts.append("from the classification: " + ", ".join(
                        "%s %s" % (v, n) for n, v in d["coordinates_named"].items()))
                elif "coordinates_base3" in d:
                    parts.append("from the classification: " + ", ".join(
                        "%s %s" % (v, n) for n, v in d["coordinates_base3"].items() if v != "0"))
                else:
                    parts.append("class: " + d["class"])
                    if "closed_form" in d:
                        parts.append(d["closed_form"])
                    elif "arctan_certificate" in d:
                        parts.append("arctan = " + d["arctan_certificate"])
                    if d["lean"] != "none":
                        parts.append("Lean: " + d["lean"])
            if "proof" in k:
                parts.append("Lean: not attempted; needs " + k["proof"]["ingredients"])
            if "group" in k and len(k["group"]["same_parameters"]) > k["group"]["rank"]:
                parts.append("printed relations %s have rank %d" % ("-".join([k["group"]["same_parameters"][0],
                                                                              k["group"]["same_parameters"][-1]]),
                                                                    k["group"]["rank"]))
            if e.get("print_defect"):
                parts.append("PRINT DEFECT: " + e["print_defect"])
            e["status"] = "; ".join(parts)
        elif e["kind"] == "assertion":
            a = k.get("assertion", {"status": "", "detail": ""})
            e["status"] = a["status"] + (": " + a["detail"] if a["detail"] else "")
        elif e["kind"] == "list entry":
            if "criterion" in k:
                e["status"] = "criterion of Theorem K: " + k["criterion"]["criterion"]
            else:
                cc = k["certificate"]
                e["status"] = ("value of F (exact certificate)" if cc["certificate"] else "NO certificate: " + cc["detail"]) + (
                    "; " + cc["note"] if "note" in cc else "")
        elif e["kind"] == "table row":
            t = k["table"]
            if t["agrees"] is True:
                e["status"] = "equals the theorem's count; Lean: " + t["lean"]
            elif t["agrees"] is False:
                e["status"] = "DISAGREES with the theorem's count %d" % t["theorem_count"]
            else:
                e["status"] = ("no theorem; the %d printed relation(s) that rewrite to this row have rank %d <= %d"
                               % (len(t["printed_relations"]), t["rank_of_printed_relations"], e["content"]["count"])
                               if t["consistent_with_printed"] else "INCONSISTENT with the printed relations")
            if t.get("lll_count") is not None:
                e["status"] += "; lattice reduction finds %d" % t["lll_count"]
    # ---- counts
    stats = []
    kinds = {}
    for e in E:
        kd = "zero relation" if e["content"].get("zero_relation") else e["kind"]
        kinds[kd] = kinds.get(kd, 0) + 1
    stats = sorted(kinds.items())
    log("entries: " + "; ".join("%s: %d" % kv for kv in stats))
    bydeg = {}
    for e in formulas:
        if e["degree"]:
            key = (e["degree"], classify_base(e))
            bydeg[key] = bydeg.get(key, 0) + 1
    log("formulas by degree and base: " + "; ".join("s=%d %s: %d" % (k[0], k[1], v) for k, v in sorted(bydeg.items())))
    d1 = [e for e in formulas if e["degree"] == 1]
    log("degree 1: Lean has the same statement: %d (%s); with coordinates in the project's bases: %d (%s)" % (
        sum(1 for e in d1 if e["checks"]["degree1"].get("lean_same_statement")),
        ", ".join(e["id"] for e in d1 if e["checks"]["degree1"].get("lean_same_statement")),
        sum(1 for e in d1 if "coordinates_named" in e["checks"]["degree1"] or "coordinates_base3" in e["checks"]["degree1"]),
        ", ".join(e["id"] for e in d1 if "coordinates_named" in e["checks"]["degree1"] or "coordinates_base3" in e["checks"]["degree1"])))
    for e in E:
        st = e.get("status", "")
        if any(w in st for w in ("DISAGREE", "OVERSTATED", "slip", "SETTLED", "NOT CONFIRMED", "INCONSISTENT",
                                 "NO certificate", "FAILS", "PRINT DEFECT", "have rank", "not confirmed")):
            log("  [%s p.%d] %s" % (e["id"], e["page"], st[:400]))
    log("time: %.0f s" % (time.time() - t0))
    if write:
        io.open(LEDGER, "w", encoding="utf-8", newline="\n").write(json.dumps(led, indent=1) + "\n")
        write_md(led, stats)
        log("written: %s, %s" % (os.path.relpath(LEDGER, os.path.dirname(HERE)), os.path.relpath(LEDGER_MD, os.path.dirname(HERE))))


def classify_base(e):
    b = str(e["base"])
    if e["base"] is None:
        return "no base"
    if "phi" in b:
        return "base (2/phi)^10"
    if "b" in b:
        return "general base b"
    r = root_power(ev(b))[0]
    return "base %d" % r


if __name__ == "__main__":
    main()
