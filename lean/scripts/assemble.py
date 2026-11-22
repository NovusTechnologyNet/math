import re
import os
HERE = os.path.dirname(os.path.abspath(__file__))
S = os.path.join(HERE, "generated") + os.sep      # written by twgen.py and named.py
head = open(os.path.join(HERE, "vseries_head.lean"), encoding="utf-8").read()
tail = open(os.path.join(HERE, "vseries_tail.lean"), encoding="utf-8").read()
cases = open(S + "tw_cases.lean", encoding="utf-8").read().splitlines()
indep = open(S + "indep.lean", encoding="utf-8").read().splitlines()
table = [(0,0),(0,3),(6,3),(0,0),(0,3),(0,-3),(0,0),(0,3),(0,9),(0,0),(-6,-3),(0,-3),(0,0),(0,3),(-6,3),(0,0),(0,-9),(0,-3),(0,0),(0,3),(0,-3),(0,0),(6,-3),(0,-3)]
old = """  intro r hr
  interval_cases r <;>
    simp only [Nat.reduceMul, Nat.reduceMod, dTW, twTable, List.getD_cons_zero,
      List.getD_cons_succ, GaussianInt.toComplex_def', I_z24] <;> push_cast
"""
assert old in head
new = "  intro r hr\n  interval_cases r\n"
for r in range(24):
    a, b = table[r]
    cert = cases[r].replace("  · linear_combination ", "")
    new += "  · simp only [Nat.reduceMul, Nat.reduceMod]\n"
    new += "    rw [show twTable.getD %d 0 = (⟨%d, %d⟩ : GaussianInt) from rfl, GaussianInt.toComplex_def',\n      I_z24, dTW]\n" % (r, a, b)
    new += "    push_cast\n"
    new += "    linear_combination %s\n" % cert
head = head.replace(old, new)
vals = [l for l in indep if l.startswith("theorem")]
lcs = [l for l in indep if l.startswith("  · linear_combination")]
names = ["namedA1", "namedA6", "namedA10", "namedL6", "namedL8", "namedL10", "namedL24", "namedTW"]
sec = "\n".join(vals) + "\n\n"
sec += """/-- **The eight patterns are linearly independent over ℚ** (their values at `k = 1, ..., 8` form
an invertible matrix). -/
theorem named_linearIndependent :
    LinearIndependent ℚ ![namedA1, namedA6, namedA10, namedL6, namedL8, namedL10, namedL24,
      namedTW] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
"""
valnames = [v.split()[1] for v in vals]
for k in range(1, 9):
    vs = ", ".join(n for n in valnames if n.endswith("_at_%d" % k))
    sec += "  have e%d := congrFun hg %d\n" % (k, k)
    sec += "  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_eight,\n    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Pi.zero_apply, %s] at e%d\n" % (vs, k)
for i in range(8):
    sec += "  have g%d : g %d = 0 := by\n  %s\n" % (i, i, lcs[i].replace("  · ", "  "))
sec += "  intro i\n  fin_cases i\n"
for i in range(8):
    sec += "  · exact g%d\n" % i
sec += """
/-- The new formula is in the span: `ρ_new = -2 A6 + A10 + 2 L6 - 2 L8 + L24`. -/
theorem rhoNew_eq_named (k : ℕ) :
    rhoNew k = -2 * namedA6 k + namedA10 k + 2 * namedL6 k - 2 * namedL8 k + namedL24 k := by
  have h := NZ_eq k
  have e : rhoNew k = (NZ k : ℚ) / 2 := by linarith
  rw [e]
  simp only [NZ, namedA6, namedA10, namedL6, namedL8, namedL24, rhoA, rhoL, P1Z, one_mul]
  push_cast
  ring

/-- **Theorem C, lower half.** Eight rational patterns of period 120 (`named_periodic`),
linearly independent over ℚ, whose series are rational multiples of π:
`π/4, 0, π/4, 0, 0, 0, 0, 0`. -/
theorem V_lower_bound :
    LinearIndependent ℚ ![namedA1, namedA6, namedA10, namedL6, namedL8, namedL10, namedL24,
      namedTW] ∧
    HasSum (seriesTerm namedA1) (Real.pi / 4) ∧ HasSum (seriesTerm namedA6) 0 ∧
    HasSum (seriesTerm namedA10) (Real.pi / 4) ∧ HasSum (seriesTerm namedL6) 0 ∧
    HasSum (seriesTerm namedL8) 0 ∧ HasSum (seriesTerm namedL10) 0 ∧
    HasSum (seriesTerm namedL24) 0 ∧ HasSum (seriesTerm namedTW) 0 :=
  ⟨named_linearIndependent, hasSum_namedA1, hasSum_namedA6, hasSum_namedA10, hasSum_namedL6,
    hasSum_namedL8, hasSum_namedL10, hasSum_namedL24, hasSum_namedTW⟩

end PiFormula
"""
open(os.path.join(HERE, "..", "Pilean", "PiFormula", "VSeries.lean"), "w", encoding="utf-8").write(head + tail + sec)
print("assembled")
