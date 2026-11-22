import os, pickle, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction
from flint import fmpq_mat, fmpq
import decompose_formula as dfm
V = pickle.load(open(sys.argv[1], "rb"))["V"]
N = 120
Vk = [[v[k - 1] if k else v[N - 1] for k in range(N)] for v in V]
def rank(rows):
    return fmpq_mat([[fmpq(x.numerator, x.denominator) for x in r] for r in rows]).rank()
allnamed = []
for name, pat, val in dfm.NAMED:
    pat = [Fraction(x) for x in pat]
    allnamed.append(pat)
    print("%-48s in my V: %s" % (name, rank(Vk + [pat]) == 8))
print("rank of the 8 named series:", rank(allnamed))
