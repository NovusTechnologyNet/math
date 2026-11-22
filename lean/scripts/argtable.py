# Generates section 4 of lean/Pilean/PiFormula/ExactArgs.lean: the table
#   garg j = alpha j * pi + beta j * garg 60 + gam j * garg 5      (j in R0Exps)
# with the three coefficient functions and the 24 cases of its proof.
#
#   python lean/scripts/argtable.py > fragment.lean
import sys, io
from fractions import Fraction as Fr

R0 = [0, 60, 30, 90, 20, 100, 15, 45, 75, 105, 12, 36, 84, 108, 10, 50, 18, 42, 66, 114,
      5, 25, 65, 85]
# j : (alpha, beta, gamma, facts used by linarith)
T = {
    0: (Fr(1, 4), 0, 0, "garg_zero"),
    60: (0, 1, 0, ""),
    30: (Fr(-1, 4), 0, 0, "garg_zero, garg_partner (j := 0) (k := 30) (Or.inl (by norm_num))"),
    90: (0, -1, 0, "garg_partner (j := 60) (k := 90) (Or.inr (by norm_num))"),
    20: (Fr(-1, 6), 0, 0, "garg_20"),
    100: (Fr(1, 6), 0, 0, "garg_100"),
    15: (0, 0, 0, "garg_partner (j := 15) (k := 15) (Or.inl (by norm_num))"),
    45: (Fr(-2, 3), 0, 2, "garg_45"),
    75: (0, 0, 0, "garg_partner (j := 75) (k := 75) (Or.inr (by norm_num))"),
    105: (Fr(2, 3), 0, -2, "garg_45, garg_partner (j := 45) (k := 105) (Or.inr (by norm_num))"),
    12: (Fr(11, 80), Fr(1, 4), 0, "garg_12"),
    36: (Fr(-17, 80), Fr(1, 4), 0, "garg_36"),
    84: (Fr(7, 80), Fr(1, 4), 0, "garg_84"),
    108: (Fr(19, 80), Fr(1, 4), 0, "garg_108"),
    10: (Fr(1, 6), 0, 0, "garg_20, garg_partner (j := 20) (k := 10) (Or.inl (by norm_num))"),
    50: (Fr(-1, 6), 0, 0,
         "garg_100, garg_partner (j := 100) (k := 50) (Or.inr (by norm_num))"),
    18: (Fr(-11, 80), Fr(-1, 4), 0,
         "garg_12, garg_partner (j := 12) (k := 18) (Or.inl (by norm_num))"),
    42: (Fr(-19, 80), Fr(-1, 4), 0,
         "garg_108, garg_partner (j := 108) (k := 42) (Or.inr (by norm_num))"),
    66: (Fr(-7, 80), Fr(-1, 4), 0,
         "garg_84, garg_partner (j := 84) (k := 66) (Or.inr (by norm_num))"),
    114: (Fr(17, 80), Fr(-1, 4), 0,
          "garg_36, garg_partner (j := 36) (k := 114) (Or.inr (by norm_num))"),
    5: (0, 0, 1, ""),
    25: (0, 0, -1, "garg_partner (j := 5) (k := 25) (Or.inl (by norm_num))"),
    65: (Fr(1, 6), 0, -1, "garg_65"),
    85: (Fr(-1, 6), 0, 1, "garg_65, garg_partner (j := 65) (k := 85) (Or.inr (by norm_num))"),
}
assert sorted(T) == sorted(R0)


def q(x):
    x = Fr(x)
    if x.denominator == 1:
        return str(x.numerator)
    return "%d / %d" % (x.numerator, x.denominator)


def qp(x):
    s = q(x)
    return "(%s)" % s if s.startswith("-") else s


out = io.StringIO()
w = out.write
w("/-! ## 4. The table of arguments -/\n\n")
for name, idx, doc in (("alpha", 0, "`π`"), ("beta", 1, "`garg 60`"), ("gam", 2, "`garg 5`")):
    w("/-- The coefficient of %s in `garg j`. -/\n" % doc)
    w("def %s (j : ℕ) : ℚ :=\n" % name)
    items = [(j, T[j][idx]) for j in R0 if T[j][idx] != 0]
    line = "  "
    for j, v in items:
        piece = "if j = %d then %s else " % (j, q(v))
        if len(line) + len(piece) > 96:
            w(line.rstrip() + "\n")
            line = "  "
        line += piece
    w(line + "0\n\n")

w("/-- **The table of arguments**: each `arg w_j` in terms of `π`, `arg w_60` and `arg w_5`. -/\n")
w("theorem garg_table : ∀ j ∈ R0Exps,\n")
w("    garg j = alpha j * Real.pi + beta j * garg 60 + gam j * garg 5 := by\n")
w("  intro j hj\n")
w("  simp only [R0Exps, Finset.mem_insert, Finset.mem_singleton] at hj\n")
w("  rcases hj with " + " | ".join(["rfl"] * 12) + "\n    | " + " | ".join(["rfl"] * 12) + "\n")
for j in R0:
    a, b, c, facts = T[j]
    w("  · rw [show alpha %d = %s from by norm_num [alpha],\n" % (j, q(a)))
    w("      show beta %d = %s from by norm_num [beta],\n" % (j, q(b)))
    w("      show gam %d = %s from by norm_num [gam]]\n" % (j, q(c)))
    w("    push_cast\n")
    if facts:
        fl = "    linarith [%s]" % facts
        if len(fl) > 100:
            parts = facts.split(", ", 1)
            fl = "    linarith [%s,\n      %s]" % (parts[0], parts[1])
        w(fl + "\n")
    else:
        w("    linarith\n")
w("\n")
sys.stdout.buffer.write(out.getvalue().encode("utf-8"))
