"""Computer checks for the wider theorem (all cyclotomic-type binary series).

Run with the system Python (needs sympy and mpmath):  python wider_theorem.py

Setting. Let t = 1 + i. For a root of unity r put  g(r) = Im Log(1 - r/t).
Roots of unity fall into classes ("orbits") that share a minimal polynomial over
Q(i); for an orbit O put  gamma(O) = sum of g(r) over r in O. The class studied is
the rational combinations of the gamma(O): the Galois-invariant patterns. (General
periodic patterns need algebraic coefficients on individual roots; those "twisted"
series are NOT covered here.)

Claims checked here:
  1. gamma(O*) = -gamma(O), where O* = { i * conj(r) : r in O }.
  2. gamma(O1) = pi/4, gamma(O6) = 0, gamma(O2) = atan(1/2) - pi/4,
     gamma(O10) = atan(1/2), where On is the orbit of the primitive n-th roots.
  3. Apart from 1 and 2, the gamma(O) are independent: with one orbit chosen from
     each pair {O, O*}, the only relations are gamma(O1) = pi/4, gamma(O6) = 0
     and gamma(O10) - gamma(O2) = pi/4.
  4. Speed. A series alpha*gamma(O1) + beta*gamma(O6) + delta*(gamma(O10)-gamma(O2))
     has k-th coefficient -E(k) * Im(t^-k) / k with
         E(k) = alpha + beta*c6(k) + delta*(c10(k) - (-1)^k)
     (c6, c10 Ramanujan sums). Speed above 3/2 would need E = 0 on every k with
     gcd(k, 60) in {1, 2, 3}; that forces alpha = beta = delta = 0.
"""
import sys
from fractions import Fraction
from math import gcd

from mpmath import mp, mpc, mpf, pi, log, atan, exp
from sympy import factorint, totient

from machin_theorem import nullspace, sqrt_minus_one

mp.dps = 120
T = mpc(1, 1)


def orbits_of_order(d):
    """Orbits of primitive d-th roots of unity under the Galois group over Q(i).
    A root exp(2*pi*i*e/d) is stored as the fraction e/d."""
    units = [a for a in range(1, d + 1) if gcd(a, d) == 1]
    stab = [a for a in units if d % 4 != 0 or a % 4 == 1]
    seen, out = set(), []
    for b in units:
        if b in seen:
            continue
        orb = frozenset(Fraction(a * b % d, d) for a in stab)
        seen.update(int(f * d) % d for f in orb)
        out.append(orb)
    return out


def star(orb):
    """r -> i * conj(r): the fraction f goes to 1/4 - f (mod 1)."""
    return frozenset((Fraction(1, 4) - f) % 1 for f in orb)


def gamma(orb):
    total = mpf(0)
    for f in orb:
        r = exp(2j * pi * mpf(f.numerator) / f.denominator)
        total += log(1 - r / T).imag
    return total


def atom(orb):
    """prod (t - r) over the orbit: an exact Gaussian integer."""
    z = mpc(1)
    for f in orb:
        z *= T - exp(2j * pi * mpf(f.numerator) / f.denominator)
    a, b = int(mp.nint(z.real)), int(mp.nint(z.imag))
    assert abs(z - mpc(a, b)) < mpf(10) ** -40, "atom is not a Gaussian integer"
    return a, b


def vector(w, cache):
    a, b = w
    g = gcd(a, b)
    a, b = a // g, b // g
    vec = {}
    for p, e in factorint(a * a + b * b).items():
        if p == 2:
            continue
        if p not in cache:
            cache[p] = sqrt_minus_one(p)
        vec[p] = e if (a + b * cache[p]) % p == 0 else -e
    return vec


def main(max_size):
    # ---- orbits of every order d whose orbit size is at most max_size
    orbs = {}
    d = 1
    while d <= 16 * max_size:
        size = totient(d) // (2 if d % 4 == 0 else 1)
        if size <= max_size:
            for o in orbits_of_order(d):
                orbs[o] = d
        d += 1
    # close under the pairing
    names = {o: "O%d%s" % (d, "" if d % 4 else "'") for o, d in orbs.items()}
    missing = [o for o in orbs if star(o) not in orbs]
    assert not missing, "orbit set is not closed under the pairing"

    val = {o: gamma(o) for o in orbs}
    worst = max(abs(val[o] + val[star(o)]) for o in orbs)
    selfpaired = [o for o in orbs if star(o) == o]
    print("orbits: %d (orders up to %d); self-paired: %d" % (len(orbs), max(orbs.values()), len(selfpaired)))
    print("claim 1: max |gamma(O) + gamma(O*)| = %s" % mp.nstr(worst, 3))

    def first(n):
        return next(o for o, dd in orbs.items() if dd == n)
    o1, o2, o6, o10 = first(1), first(2), first(6), first(10)
    u = atan(mpf(1) / 2)
    print("claim 2: gamma(O1) - pi/4 = %s; gamma(O6) = %s; gamma(O2) - (atan(1/2) - pi/4) = %s; "
          "gamma(O10) - atan(1/2) = %s"
          % tuple(mp.nstr(x, 3) for x in (val[o1] - pi / 4, val[o6], val[o2] - (u - pi / 4), val[o10] - u)))

    # ---- one representative per pair, never a self-paired orbit
    reps, used = [], set()
    for o in sorted(orbs, key=lambda o: (orbs[o], sorted(o))):
        if o in used or star(o) == o:
            continue
        used.add(o)
        used.add(star(o))
        reps.append(o)
    cache = {}
    vecs = [vector(atom(o), cache) for o in reps]
    primes = sorted({p for v in vecs for p in v})
    rows = [[v.get(p, 0) for v in vecs] for p in primes]
    basis = nullspace(rows, len(reps)) if primes else []
    print("claim 3: %d representative orbits, %d primes, %d independent relations (expected 3)"
          % (len(reps), len(primes), len(basis)))
    for rel in basis:
        total = sum(c * val[o] for c, o in zip(rel, reps))
        m = total / (pi / 4)
        terms = " ".join("%+d*gamma(O%d)" % (c, orbs[o]) for c, o in zip(rel, reps) if c)
        print("      %s = %s * pi/4" % (terms, mp.nstr(m, 6)))
    special = {orbs[o] for rel in basis for c, o in zip(rel, reps) if c}
    print("      orders of the orbits that occur in any relation: %s" % sorted(special))

    # ---- claim 4: the speed bound, by exact linear algebra
    def ram(n, k):                         # Ramanujan sum c_n(k)
        return int(round(sum(mp.cos(2 * pi * a * k / n) for a in range(1, n + 1) if gcd(a, n) == 1)))
    table = {}
    for k in range(1, 61):
        if k % 4:
            table.setdefault(gcd(k, 60), set()).add((1, ram(6, k), ram(10, k) - (-1) ** k))
    print("claim 4: E(k) = alpha*a + beta*b + delta*c with (a, b, c) by gcd(k, 60):")
    for g in sorted(table):
        assert len(table[g]) == 1
        print("      gcd %2d: %s" % (g, next(iter(table[g]))))
    slow = [list(next(iter(table[g]))) for g in (1, 2, 3)]
    kernel = nullspace(slow, 3)
    print("      solutions of E = 0 on gcd 1, 2, 3: %d (0 means speed 3/2 cannot be beaten)" % len(kernel))
    two = nullspace([list(next(iter(table[g]))) for g in (1, 2)], 3)
    print("      solutions of E = 0 on gcd 1, 2 only (speed exactly 3/2): %s  as (alpha, beta, delta)" % two)
    a, b, dl = two[0]
    euler = a * val[o1] + b * val[o6] + dl * (val[o10] - val[o2])
    check = 2 * atan(mpf(1) / 3) + atan(mpf(1) / 7)
    print("      that series sums to %s * pi/4; Euler's 2atan(1/3)+atan(1/7) = %s * pi/4"
          % (mp.nstr(euler / (pi / 4), 6), mp.nstr(check / (pi / 4), 6)))


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 36)
