"""Referee check of Step 3 and Theorems C, D (and the data behind E, F), by a method that
does not reuse full_class_theorem.py / cheaper_formula.py.

Run with PYTHONPATH set to the numpy + python-flint folders:  python review_space.py [out.pkl]

1. The 13 relations printed by full_class_theorem.py are re-verified EXACTLY with
   python-flint polynomial arithmetic modulo Phi_120 (product of (t - zeta^j)^e equals
   zeta^m t^(sum e)), and their angles content*i*pi are re-computed with arb balls.
2. Rigorous rank certificate: the place matrix (2-adic row, the four distinct valuation rows
   computed by review_valuations.py, and log|sigma_a(w_j)| for the 16 embeddings a = 1 mod 4)
   is evaluated in ball arithmetic; the Gram determinant of the 11 "independent" columns is
   a ball that excludes 0, so the relation space has dimension exactly 13.
3. The space W of rational period-120 patterns whose series is an algebraic multiple of pi
   is built EXACTLY (no floating point, no rational reconstruction):
       d_j(rho) = 0 for zeta^j outside the 24 roots,   sum_j f_j d_j(rho) = 0 for f in M^perp,
   as rational linear conditions on rho (each d_j is an element of Q(zeta_120), 32 coordinates).
   value(rho)/pi = (1/2) sum_j c_j d_j(rho), where c is any rational vector with
   c . e_a = content_a for the 13 relations.
4. V = rational-value subspace; Theorem D thresholds; the F_1 (even-support) claim;
   membership of pi_formula_120.json; the 35 conditions "entry = 0".
"""
import json
import pickle
import sys
from fractions import Fraction
from math import gcd

from flint import fmpz_poly, fmpq_mat, fmpz_mat, fmpq, arb, acb, arb_mat, ctx
from mpmath import mp, mpf, pi as MPI

N = 120
PHI = fmpz_poly.cyclotomic(N)
DEG = PHI.degree()
X = fmpz_poly([0, 1])
R0 = [0, 60, 30, 90, 20, 100, 15, 45, 75, 105, 12, 36, 84, 108, 10, 50, 18, 42, 66, 114, 5, 25, 65, 85]
RELS = [({0: -1, 30: 1}, Fraction(-1, 2)),
        ({0: -2, 20: 1, 100: 1}, Fraction(-1, 2)),
        ({0: -2, 15: 1, 75: 1}, Fraction(-1, 2)),
        ({0: -3, 12: 1, 36: 1, 60: -1, 84: 1, 108: 1}, Fraction(-1, 2)),
        ({10: 1, 20: -1}, Fraction(1, 3)),
        ({0: -2, 20: 1, 50: 1}, Fraction(-5, 6)),
        ({12: -4, 18: 4, 60: 1, 90: -1}, Fraction(-11, 10)),
        ({0: -12, 12: 4, 36: 4, 42: 4, 60: -3, 84: 4, 90: -1}, Fraction(-39, 10)),
        ({60: 1, 66: 4, 84: -4, 90: -1}, Fraction(-7, 10)),
        ({36: -4, 60: 1, 90: -1, 114: 4}, Fraction(17, 10)),
        ({5: -2, 25: 2, 45: 1, 105: -1}, Fraction(-4, 3)),
        ({0: -2, 5: 2, 45: -1, 65: 2, 105: -1}, Fraction(-1, 6)),
        ({0: -1, 5: 1, 45: -1, 85: 1}, Fraction(1, 4))]
VAL_ROWS = [{45: 2, 5: 1, 85: 1}, {105: 2, 25: 1, 65: 1},          # from review_valuations.py
            {60: 4, 12: 1, 36: 1, 84: 1, 108: 1}, {90: 4, 18: 1, 42: 1, 66: 1, 114: 1}]


def zpow(m):
    return (X ** (m % N)) % PHI


T = (1 + zpow(30)) % PHI


def vec(p):
    c = [int(x) for x in p.coeffs()]
    return c + [0] * (DEG - len(c))


# ---------------------------------------------------------------- 1. exact relations
def check_relations():
    ctx.prec = 600
    for e, content in RELS:
        num, den = fmpz_poly(1), fmpz_poly(1)
        for j, c in e.items():
            f = (T - zpow(j)) % PHI
            if c > 0:
                num = (num * f ** c) % PHI
            else:
                den = (den * f ** (-c)) % PHI
        tot = sum(e.values())
        assert tot == 0, "relation with non-zero exponent sum"
        m = [k for k in range(N) if (num - (zpow(k) * den) % PHI) % PHI == 0]
        assert len(m) == 1, ("not a root of unity", e)
        # angle in ball arithmetic: sum e_j Log(1 - zeta^j / t)
        tt = acb(1, 1)
        s = acb(0)
        for j, c in e.items():
            z = acb(arb(2 * j) / N).exp_pi_i()
            s += c * (1 - z / tt).log()
        want = arb(content.numerator) / content.denominator * arb.pi()
        assert abs(s.real) < arb(10) ** -150 and (s.imag - want).contains(0)
        assert (content * 60 - m[0]) % 120 == 0
    print("1. all 13 relations hold exactly (flint, mod Phi_120); angles confirmed in ball arithmetic")


# ---------------------------------------------------------------- 2. rigorous rank
def place_matrix(cols):
    ctx.prec = 600
    tt = acb(1, 1)
    rows = [[arb(1) for _ in cols]]
    for vr in VAL_ROWS:
        rows.append([arb(vr.get(j, 0)) for j in cols])
    for a in range(1, N):
        if gcd(a, N) == 1 and a % 4 == 1:
            rows.append([abs(1 - acb(arb(2 * (j * a % N)) / N).exp_pi_i() / tt).log() for j in cols])
    return arb_mat(rows)


def rank_certificate():
    dep = set()
    for e, _ in RELS:                      # the root with the largest position in R0 order
        dep.add(max(e, key=lambda j: R0.index(j)))
    indep = [j for j in R0 if j not in dep]
    A = place_matrix(indep)
    G = A.transpose() * A
    dt = G.det()
    print("2. place matrix on the %d independent columns %s:" % (len(indep), indep))
    print("   Gram determinant (ball) = %s ; excludes 0: %s" % (dt.str(10), not dt.contains(0)))
    # relations lie in the kernel of the full place matrix
    Afull = place_matrix(R0)
    worst = arb(0)
    for e, _ in RELS:
        v = arb_mat([[arb(e.get(j, 0))] for j in R0])
        r = Afull * v
        for i in range(r.nrows()):
            assert r[i, 0].contains(0)
    print("   every relation is in the kernel of the full place matrix (ball arithmetic)")
    E = fmpq_mat([[e.get(j, 0) for j in R0] for e, _ in RELS])
    print("   rank of the 13 relation vectors: %d  ->  relation space has dimension exactly 13"
          % E.rank())
    return indep


# ---------------------------------------------------------------- 3. W exactly
def kvec_of_powers(terms):
    """terms: list of (coefficient, exponent of zeta) -> coordinate vector (integers)."""
    acc = fmpz_poly(0)
    for c, m in terms:
        acc += c * zpow(m)
    return vec(acc % PHI)


def d_columns():
    """A[j][k] = coordinate vector (times 120) of the coefficient of rho(k) in d_j."""
    A = {}
    for j in range(N):
        cols = []
        for k in range(1, N + 1):
            e = 30 + 30 * ((k // 2) % 4) - j * k
            terms = [(-2, e)]
            if k % 2:
                terms.append((-2, e + 30))
            cols.append(kvec_of_powers(terms))
        A[j] = cols                       # list over k = 1..120 of 32-vectors
    return A


def nullspace_q(rows, ncols):
    M = fmpz_mat(rows) if rows else fmpz_mat(0, ncols)
    ns, nullity = M.nullspace()
    basis = []
    for c in range(nullity):
        v = [Fraction(int(ns[r, c])) for r in range(ncols)]
        basis.append(v)
    return basis


def rref_rows(rows, ncols):
    if not rows:
        return []
    M = fmpq_mat([[fmpq(x.numerator, x.denominator) for x in r] for r in rows])
    R, rank = M.rref()
    out = []
    for i in range(rank):
        out.append([Fraction(int(R[i, c].p), int(R[i, c].q)) for c in range(ncols)])
    return out


def build_W():
    A = d_columns()
    Emat = [[e.get(j, 0) for j in R0] for e, _ in RELS]
    Mperp = nullspace_q(Emat, 24)                                  # f with f . e_a = 0
    assert len(Mperp) == 11
    rows = []
    for j in range(N):
        if j in R0:
            continue
        for m in range(DEG):
            rows.append([A[j][k][m] for k in range(N)])
    for f in Mperp:
        for m in range(DEG):
            rows.append([sum(int(f[i] * 1) * A[j][k][m] for i, j in enumerate(R0)) for k in range(N)])
    # f has integer entries already (nullspace over Z)
    W = nullspace_q(rows, N)                                       # vectors indexed k = 1..120
    print("3. W (exact rational nullspace): dimension %d" % len(W))
    # value functional: c . e_a = content_a
    E = fmpq_mat([[fmpq(e.get(j, 0)) for j in R0] for e, _ in RELS])
    b = fmpq_mat([[fmpq(c.numerator, c.denominator)] for _, c in RELS])
    # least-squares-free: solve E c = b using an exact right inverse via E E^T
    EEt = E * E.transpose()
    y = EEt.solve(b)
    cvec = E.transpose() * y
    c = [Fraction(int(cvec[i, 0].p), int(cvec[i, 0].q)) for i in range(24)]
    for (e, content) in RELS:
        assert sum(c[i] * e.get(j, 0) for i, j in enumerate(R0)) == content
    def value(rho_k):                          # rho_k: list over k = 1..120
        acc = [Fraction(0)] * DEG
        for i, j in enumerate(R0):
            if c[i] == 0:
                continue
            for k in range(N):
                if rho_k[k]:
                    col = A[j][k]
                    for m in range(DEG):
                        if col[m]:
                            acc[m] += c[i] * rho_k[k] * col[m]
        return [x / (2 * N) for x in acc]      # A carries the factor 120; value/pi = (1/2) c.d
    def in_W_exact(rho_k):
        for j in range(N):
            dj = [sum(A[j][k][m] * rho_k[k] for k in range(N)) for m in range(DEG)]
            if j not in R0 and any(dj):
                return False
        for f in Mperp:
            s = [sum(f[i] * sum(A[j][k][m] * rho_k[k] for k in range(N)) for i, j in enumerate(R0))
                 for m in range(DEG)]
            if any(s):
                return False
        return True
    return W, value, in_W_exact


def series_value(rho_k, dps=60):
    mp.dps = dps
    tot = mpf(0)
    k = 1
    while k // 2 <= mp.prec + 40:
        r = rho_k[(k - 1) % N]
        if r:
            tot += mpf(r.numerator) / r.denominator / (mpf(k) * mpf(2) ** (k // 2))
        k += 1
    return tot


def main():
    check_relations()
    rank_certificate()
    W, value, in_W = build_W()
    vals = [value(w) for w in W]
    # numeric cross-check of the value functional
    worst = 0
    for w, v in zip(W, vals):
        num = series_value(w) / MPI
        from mpmath import exp as mexp
        q = sum(mpf(x.numerator) / x.denominator * mexp(2j * MPI * m / N) for m, x in enumerate(v))
        worst = max(worst, abs(q - num))
    print("   value/pi of the 13 basis patterns vs direct summation: max error %s" % mp.nstr(worst, 3))
    # image of value/pi: Q-span dimension
    img = rref_rows([list(v) for v in vals], DEG)
    print("   dim_Q of the values/pi of W: %d  -> dim V predicted = 13 - %d + 1 = %d"
          % (len(img), len(img), 14 - len(img)))
    # V: combinations with coordinates 1..31 of value zero
    rows = [[vals[b][m] for b in range(len(W))] for m in range(1, DEG)]
    rows = [[x * 1 for x in r] for r in rows]
    den = 1
    for r in rows:
        for x in r:
            den = den * x.denominator // gcd(den, x.denominator)
    comb = nullspace_q([[int(x * den) for x in r] for r in rows], len(W))
    V = [[sum(cb[b] * W[b][k] for b in range(len(W))) for k in range(N)] for cb in comb]
    qV = [sum(cb[b] * vals[b][0] for b in range(len(W))) for cb in comb]
    print("4. V (rational value): dimension %d; values/pi of basis: %s" % (len(V), [str(q) for q in qV]))

    # Theorem D and the step-C table, exactly over Q
    print("   thresholds (rational solutions in W vanishing on all k with gcd(k,120) < g):")
    for g in (2, 3, 4, 5, 6, 8):
        slow = [k for k in range(1, N + 1) if gcd(k, N) < g]
        rows = [[W[b][k - 1] for b in range(len(W))] for k in slow]
        den = 1
        for r in rows:
            for x in r:
                den = den * x.denominator // gcd(den, x.denominator)
        sol = nullspace_q([[int(x * den) for x in r] for r in rows], len(W))
        carry = []
        for s in sol:
            v = [sum(s[b] * vals[b][m] for b in range(len(W))) for m in range(DEG)]
            carry.append(any(v))
        print("      g = %d: %d solutions; any with non-zero value: %s" % (g, len(sol), any(carry)))

    # F_1 claim: V restricted to even support
    rows = [[V[b][k - 1] for b in range(len(V))] for k in range(1, N + 1, 2)]
    den = 1
    for r in rows:
        for x in r:
            den = den * x.denominator // gcd(den, x.denominator)
    sol = nullspace_q([[int(x * den) for x in r] for r in rows], len(V))
    qs = [sum(s[b] * qV[b] for b in range(len(V))) for s in sol]
    print("   patterns of V supported on even k: dimension %d, values/pi %s" % (len(sol), [str(q) for q in qs]))
    # and W restricted to even support (algebraic multiples)
    rows = [[W[b][k - 1] for b in range(len(W))] for k in range(1, N + 1, 2)]
    den = 1
    for r in rows:
        for x in r:
            den = den * x.denominator // gcd(den, x.denominator)
    sol = nullspace_q([[int(x * den) for x in r] for r in rows], len(W))
    nz = []
    for s in sol:
        v = [sum(s[b] * vals[b][m] for b in range(len(W))) for m in range(DEG)]
        nz.append(any(v))
    print("   patterns of W supported on even k: dimension %d, any with non-zero value: %s" % (len(sol), any(nz)))

    # the claimed optimal formula
    data = json.load(open("pi_formula_120.json"))
    rho = [Fraction(a, data["denominator"]) for a in data["numerators"]]   # index k mod 120
    rho_k = [rho[k % N] for k in range(1, N + 1)]
    print("   pi_formula_120.json: in W exactly: %s; exact value/pi = %s; non-zero entries %d"
          % (in_W(rho_k), [str(x) for x in value(rho_k)][:1] + (["(non-rational part zero)"] if not any(value(rho_k)[1:]) else ["NON-RATIONAL"]),
             sum(1 for x in rho if x)))
    mp.dps = 1010
    s = series_value(rho_k, 1010)
    print("   |series - pi/4| at 1000 digits: %s" % mp.nstr(abs(s - MPI / 4), 3))
    # cost
    units = [c for c in range(1, N) if gcd(c, N) == 1]
    lv = {}
    for cl in units:
        s_ = 1
        while rho[s_ * cl % N] == 0:
            s_ += 1
        lv[cl] = s_
    cost = sum(Fraction(1, x) for x in lv.values()) / len(units)
    print("   levels s by p mod 4: p=1: %s, p=3: %s;  mean(1/s) = %s"
          % (sorted({lv[c] for c in units if c % 4 == 1}), sorted({lv[c] for c in units if c % 4 == 3}), cost))

    # conditions 'entry = 0' on V
    classes = {}
    for k in range(1, N + 1):
        col = tuple(V[b][k - 1] for b in range(len(V)))
        if any(col):
            lead = next(x for x in col if x != 0)
            classes.setdefault(tuple(x / lead for x in col), []).append(k % N)
    zero_entries = [k % N for k in range(1, N + 1) if not any(V[b][k - 1] for b in range(len(V)))]
    print("   entries identically zero on V: %s; distinct conditions: %d" % (zero_entries, len(classes)))
    if len(sys.argv) > 1:
        with open(sys.argv[1], "wb") as fh:
            pickle.dump({"V": V, "qV": qV, "W": W, "vals": vals}, fh)


if __name__ == "__main__":
    main()
