"""Derive Bailey's table of binary degree-1 zero relations from Theorem C.

Run:  python derive_bailey_table.py [patterns.pkl]

Bailey's compendium (version of 8 April 2023), Table 1, lists for each base b = 2^B and
length N the number of linearly independent zero relations

    0 = sum over i = 1..N of a_i * S_i,      S_i = sum over j >= 0 of 2^(-Bj) / (Nj + i),

found by PSLQ. Every row of the table has N = 2B or N = B.

Theorem C (pi_formula_theorem.md, Part III) gives the 8-dimensional space V of all
rational periodic patterns rho with  sum_k rho(k) 2^(-floor(k/2)) / k  in Q*pi, all of
period dividing 120. The zero relations form the 7-dimensional subspace V0 (pi content 0).

Translation (k = Nj + i):
  * N = 2B: 2^(-Bj) = 2^(-floor(k/2)) * 2^(floor(i/2)), so the relations are the patterns
    in V0 of period dividing N; by Theorem C, of period dividing gcd(N, 120).
  * N = B:  2^(-Bj) = 2^(-k) * 2^i, and 2^(-k)/k = 2 * 2^(-floor(2k/2))/(2k): the
    relations are the patterns in V0 supported on even k with period dividing 2N
    (again intersected with period 120).
So each count is the dimension of a subspace of V0 cut out by linear conditions, and
is computed here exactly, in rational arithmetic, from the basis of V.

The first time it runs, the script also writes that basis to pi_space_basis_120.json
(exact rationals) so that it no longer depends on a temporary file.
"""
import json
import os
import pickle
import sys
from fractions import Fraction
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))
BASIS = os.path.join(HERE, "pi_space_basis_120.json")
N = 120

# Bailey 2023, Table 1, degree 1, binary rows: (B, n) -> count, with b = 2^B.
BAILEY = {
    (4, 8): 1, (6, 6): 1, (8, 16): 1, (12, 12): 1, (12, 24): 5, (16, 32): 1, (18, 18): 1,
    (20, 40): 3, (24, 24): 1, (24, 48): 5, (28, 56): 1, (30, 30): 1, (30, 60): 1,
    (32, 64): 1, (36, 36): 1, (36, 72): 5, (40, 80): 3, (42, 42): 1, (42, 84): 1,
    (44, 88): 1, (48, 48): 1, (48, 96): 5, (52, 104): 1, (54, 54): 1, (56, 112): 1,
    (60, 60): 1, (60, 120): 7,
}


def load_basis(pkl):
    if os.path.exists(BASIS):
        data = json.load(open(BASIS))
        pats = [[Fraction(x) for x in p] for p in data["patterns"]]
        qs = [Fraction(x) for x in data["pi_content"]]
        return pats, qs
    pats, qs = pickle.load(open(pkl, "rb"))
    data = {
        "statement": "Basis of V: rational patterns rho (index k mod 120) with "
                     "sum_k rho(k) 2^(-floor(k/2))/k = q*pi; pi_content[i] = q of pattern i",
        "patterns": [[str(x) for x in p] for p in pats],
        "pi_content": [str(q) for q in qs],
    }
    json.dump(data, open(BASIS, "w"), indent=0)
    return pats, qs


def rank(rows):
    rows = [list(r) for r in rows if any(r)]
    r, ncols = 0, len(rows[0]) if rows else 0
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


def dims(pats, qs, period, even_only):
    """(dimension with pi allowed, dimension of zero relations) of the subspace of V of
    patterns with period dividing `period` (and supported on even k if even_only)."""
    d = len(pats)
    cond = []
    p = gcd(period, N)
    for k in range(N):
        cond.append([pats[i][k] - pats[i][(k + p) % N] for i in range(d)])
        if even_only and k % 2 == 1:
            cond.append([pats[i][k] for i in range(d)])
    full = d - rank(cond)
    zero = d - rank(cond + [qs])
    return full, zero


def main():
    pkl = sys.argv[1] if len(sys.argv) > 1 else ""
    pats, qs = load_basis(pkl)
    assert len(pats) == 8 and len(pats[0]) == N
    print("basis of V: %d patterns of period 120, pi content %s" % (len(pats), [str(q) for q in qs]))
    print()
    print("Bailey's Table 1 (degree 1, b = 2^B, length n) against Theorem C:")
    print("     B    n | family  period used | zero relations: Bailey  Theorem C | pi formula?")
    agree = 0
    for (B, n), count in sorted(BAILEY.items(), key=lambda t: (t[0][1] // t[0][0], t[0][1])):
        if n == 2 * B:
            full, zero = dims(pats, qs, n, False)
            fam, per = "F_2", gcd(n, N)
        elif n == B:
            full, zero = dims(pats, qs, 2 * n, True)
            fam, per = "F_1", gcd(2 * n, N)
        else:
            raise ValueError((B, n))
        ok = zero == count
        agree += ok
        print("  %4d %4d |  %s    %4d        |        %3d       %3d   %s | %s"
              % (B, n, fam, per, count, zero, "ok" if ok else "DIFFERENT", "yes" if full > zero else "no"))
    print("  rows agreeing: %d of %d" % (agree, len(BAILEY)))
    print()
    print("Rows Theorem C predicts that are NOT in Bailey's table (n <= 240):")
    seen = set()
    for n in range(1, 241):
        for B, fam in ((n // 2, "F_2") if n % 2 == 0 else (None, None), (n, "F_1")):
            if B is None or (B, n) in BAILEY or B < 1:
                continue
            if fam == "F_2":
                full, zero = dims(pats, qs, n, False)
                per = gcd(n, N)
            else:
                if n > 120:
                    continue
                full, zero = dims(pats, qs, 2 * n, True)
                per = gcd(2 * n, N)
            key = (fam, per, n % 1)
            if zero > 0 or full > zero:
                print("  b = 2^%-3d n = %-3d (%s, period %3d): %d zero relation(s)%s"
                      % (B, n, fam, per, zero, ", and a formula for pi" if full > zero else ""))
    print()
    print("Dimension of V0 at each period dividing 120 (family F_2, all supports):")
    for p in sorted(d for d in range(1, 121) if 120 % d == 0):
        full, zero = dims(pats, qs, p, False)
        if full:
            print("  period %3d: %d zero relation(s)%s" % (p, zero, " + pi" if full > zero else ""))


if __name__ == "__main__":
    main()
