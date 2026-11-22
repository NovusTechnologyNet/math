import json, sys
d = json.load(open(sys.argv[1]))
num = d['numerators']
# Gaussian integers as complex with integer parts
def gi_pow(n): return [1, 1j, -1, -1j][n % 4]
def ngi_pow(n): return [1, -1j, -1, 1j][n % 4]
def c2(k): return (2 if k % 2 == 0 else 0) - 1
def c6(k): return (6 if k % 6 == 0 else 0) - (3 if k % 3 == 0 else 0) - (2 if k % 2 == 0 else 0) + 1
def c10(k): return (10 if k % 10 == 0 else 0) - (5 if k % 5 == 0 else 0) - (2 if k % 2 == 0 else 0) + 1
def p8a(k): return 2 * gi_pow(k // 2) if k % 2 == 0 else 0
def p8b(k): return 2 * ngi_pow(k // 2) if k % 2 == 0 else 0
def p24(k): return (6 * gi_pow(k // 6) if k % 6 == 0 else 0) - p8b(k)
def U(k): return ngi_pow(k // 2) * (2 if k % 2 == 0 else (1 - 1j))
def N(k):
    u = U(k)
    im = lambda z: (z * u).imag
    re = lambda z: (z * u).real
    # T = -2 tau6 + (tau10 - tau2) + 2(tL6 - 2 tL1) - 2(tL8a - 2 tL1) + (tL24 - tL8b - 2 tL1)
    # tau S = -Im(p w)/k, tL S = -Re(p w)/k, w = U/(2*2^(k//2))
    val = (-2 * -im(c6(k)) + (-im(c10(k)) + im(c2(k)))
           + 2 * (-re(c6(k)) + 2 * re(1)) - 2 * (-re(p8a(k)) + 2 * re(1))
           + (-re(p24(k)) + re(p8b(k)) + 2 * re(1)))
    return val
bad = [k for k in range(240) if abs(N(k) - num[k % 120]) > 1e-9]
print("mismatches:", bad[:10], "count", len(bad))
print([N(k) for k in range(12)], num[:12])
