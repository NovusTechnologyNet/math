"""Check the statement PrimitiveHalves3 for small E, independently of the Lean proof.

    python base3_halves_check.py [BOUND]        (default BOUND = 3001; needs sympy)

PrimitiveHalves3 is the lemma on primes used by the Lean proof of "pi is not the value of any
base-3 series of the class F3". It is proved in lean/Pilean/Base3/Halves.lean
(`primitiveHalves3`); this script is a separate numerical check, written before that proof:

    for every odd E >= 3, each of the two Aurifeuillian factors
        L_E = 3^E - 3^((E+1)/2) + 1,    M_E = 3^E + 3^((E+1)/2) + 1
    of 3^(3E) + 1 has a prime factor p with ord_p(3) = 6E.

How it is checked.  Phi_{6E}(3) divides L_E * M_E, and L_E, M_E are coprime, so
Phi_{6E}(3) = H1 * H2 with H1 = gcd(Phi, L_E), H2 = gcd(Phi, M_E).  A prime factor of
Phi_{6E}(3) either has order exactly 6E, or is the largest prime factor q of 6E, and then it
divides Phi_{6E}(3) only once (a classical fact; in Lean it is in the Tau Ceti library).  So a
half that is larger than q has a prime factor of order 6E.  The program checks H1 > q and
H2 > q for every odd E from 3 to BOUND, and for E <= 45 it also factors the halves and
exhibits the primes.

By itself this is evidence, not a proof; the proof for all E is the Lean file named above.
"""
import sys
from math import gcd, log

from sympy import factorint, n_order, primefactors, totient

from base3_criterion import cyc_value


def halves(E):
    k = (E + 1) // 2
    L = 3 ** E - 3 ** k + 1
    M = 3 ** E + 3 ** k + 1
    assert L * M * (3 ** E + 1) == 3 ** (3 * E) + 1 and gcd(L, M) == 1
    phi = cyc_value(6 * E)
    h1, h2 = gcd(phi, L), gcd(phi, M)
    assert h1 * h2 == phi, E
    return L, M, h1, h2


if __name__ == "__main__":
    bound = int(sys.argv[1]) if len(sys.argv) > 1 else 3001
    worst = None
    for E in range(3, bound + 1, 2):
        L, M, h1, h2 = halves(E)
        q = max(primefactors(6 * E))
        assert h1 > q and h2 > q, ("FAILS", E, h1, h2, q)
        # how far each half is from 3^(phi(6E)/2), in powers of 3
        half_deg = int(totient(6 * E)) // 2
        for h in (h1, h2):
            slack = log(h) / log(3) - half_deg
            if worst is None or slack < worst[0]:
                worst = (slack, E)
    print("checked: for every odd E from 3 to %d, both halves of Phi_{6E}(3) exceed the "
          "largest prime factor of 6E" % bound)
    print("smallest value of log_3(half) - phi(6E)/2: %.3f (at E = %d)" % worst)
    print()
    print("explicit primes of order 6E, for E <= 45:")
    for E in range(3, 46, 2):
        L, M, h1, h2 = halves(E)
        out = []
        for name, X in (("L", L), ("M", M)):
            ps = [p for p in factorint(X) if n_order(3, p) == 6 * E]
            assert ps, (E, name)
            out.append("%s_%d: %s" % (name, E, ", ".join(str(p) for p in ps[:3])))
        print("   E = %2d   %s" % (E, ";   ".join(out)))
