# Generates section 6 of lean/Pilean/PiFormula/Rank.lean: the 13 relations as exponent vectors,
# the evaluation of an integer combination at the 13 pivot exponents, the span theorem and
# the independence of the 13 vectors.
#
#   python lean/scripts/rankgen.py > fragment.lean
#
# The fragment is appended to Rank.lean (before `end PiFormula`). The data (exponents and the
# root of unity zeta^m of each relation) is that of Relations.lean.
import sys, io

R0 = [0, 60, 30, 90, 20, 100, 15, 45, 75, 105, 12, 36, 84, 108, 10, 50, 18, 42, 66, 114,
      5, 25, 65, 85]
B11 = [30, 15, 20, 45, 105, 5, 60, 90, 12, 36, 84]
rels = [
    {0: -1, 30: 1},
    {0: -2, 20: 1, 100: 1},
    {0: -2, 15: 1, 75: 1},
    {0: -3, 12: 1, 36: 1, 60: -1, 84: 1, 108: 1},
    {10: 1, 20: -1},
    {0: -2, 20: 1, 50: 1},
    {12: -4, 18: 4, 60: 1, 90: -1},
    {0: -12, 12: 4, 36: 4, 42: 4, 60: -3, 84: 4, 90: -1},
    {60: 1, 66: 4, 84: -4, 90: -1},
    {36: -4, 60: 1, 90: -1, 114: 4},
    {5: -2, 25: 2, 45: 1, 105: -1},
    {0: -2, 5: 2, 45: -1, 65: 2, 105: -1},
    {0: -1, 5: 1, 45: -1, 85: 1},
]
ms = [90, 90, 90, 90, 20, 70, 54, 6, 78, 102, 40, 110, 15]
# pivot exponent of each relation (relation 1 has pivot 0)
piv = [0, 100, 75, 108, 10, 50, 18, 42, 66, 114, 25, 65, 85]
assert sorted(piv + B11) == sorted(R0)
for r in rels:
    assert sum(r.values()) == 0

out = io.StringIO()
w = out.write


def lit(e):
    return "(%d)" % e if e < 0 else "%d" % e


w("/-! ## 6. The 13 relations, as exponent vectors -/\n\n")
w("theorem prodW_add (J : Finset ℕ) (f g : ℕ → ℤ) :\n")
w("    ∏ j ∈ J, wJ j ^ (f + g) j = (∏ j ∈ J, wJ j ^ f j) * ∏ j ∈ J, wJ j ^ g j := by\n")
w("  rw [← Finset.prod_mul_distrib]\n")
w("  exact Finset.prod_congr rfl fun j _ => zpow_add₀ (wJ_ne_zero j) _ _\n\n")
w("theorem prod_single {J : Finset ℕ} {a : ℕ} (ha : a ∈ J) (c : ℤ) :\n")
w("    ∏ j ∈ J, wJ j ^ (Pi.single a c : ℕ → ℤ) j = wJ a ^ c := by\n")
w("  rw [Finset.prod_eq_single a]\n")
w("  · rw [Pi.single_eq_same]\n")
w("  · intro b _ hb; rw [Pi.single_eq_of_ne hb, zpow_zero]\n")
w("  · intro h; exact absurd ha h\n\n")
w("theorem aJ_ne (j : ℕ) : tC - ζ120 ^ j ≠ 0 :=\n")
w("  tC_sub_root_ne_zero (isOfFinOrder_ζ120_pow j)\n\n")
w("theorem aJ_zero_ne : tC - 1 ≠ 0 := by\n")
w("  have h := aJ_ne 0\n  rwa [pow_zero] at h\n\n")

for k, r in enumerate(rels, 1):
    terms = " + ".join("Pi.single %d %s" % (j, lit(e)) for j, e in sorted(r.items()))
    doc = " ".join("%+d[%d]" % (e, j) for j, e in sorted(r.items()))
    w("/-- Exponents of relation %d: `%s`. -/\n" % (k, doc))
    line = "def rel%d : ℕ → ℤ := %s" % (k, terms)
    if len(line) > 100:
        parts = terms.split(" + ")
        line = "def rel%d : ℕ → ℤ :=\n  " % k + " + ".join(parts[:4])
        if len(parts) > 4:
            line += "\n    + " + " + ".join(parts[4:])
    w(line + "\n\n")
    w("theorem rel%d_prod : ∏ j ∈ R0Exps, wJ j ^ rel%d j = ζ120 ^ %d := by\n"
      % (k, k, ms[k - 1]))
    w("  simp (disch := decide) only [rel%d, prodW_add, prod_single]\n" % k)
    w("  simp only [wJ_eq, zpow_neg, zpow_ofNat]\n")
    w("  have ht := tC_ne_zero\n")
    for j in sorted(r):
        if j == 0:
            w("  have h0 := aJ_zero_ne\n")
        else:
            w("  have h%d := aJ_ne %d\n" % (j, j))
    w("  field_simp\n")
    w("  linear_combination relation_%d\n\n" % k)
    w("theorem rel%d_isRel : IsRelJ R0Exps rel%d :=\n" % (k, k))
    w("  ⟨_, isOfFinOrder_ζ120_pow %d, rel%d_prod⟩\n\n" % (ms[k - 1], k))

w("/-- The integer combination `∑ c_k · rel_k` of the 13 relations. -/\n")
w("def comb (c : Fin 13 → ℤ) (j : ℕ) : ℤ :=\n")
w("  c 0 * rel1 j + c 1 * rel2 j + c 2 * rel3 j + c 3 * rel4 j + c 4 * rel5 j + c 5 * rel6 j\n")
w("    + c 6 * rel7 j + c 7 * rel8 j + c 8 * rel9 j + c 9 * rel10 j + c 10 * rel11 j\n")
w("    + c 11 * rel12 j + c 12 * rel13 j\n\n")
w("/-- Every integer combination of the 13 relations is a relation. -/\n")
w("theorem comb_isRel (c : Fin 13 → ℤ) : IsRelJ R0Exps (comb c) :=\n")
expr = "(rel1_isRel.zsmul (c 0))"
for k in range(2, 14):
    expr = "(%s.add\n    (rel%d_isRel.zsmul (c %d)))" % (expr, k, k - 1)
w("  " + expr[1:-1] + "\n\n")

for p in piv:
    coeffs = [(k, r.get(p, 0)) for k, r in enumerate(rels) if r.get(p, 0) != 0]
    ts = ["%s * c %d" % (lit(e), k) for k, e in coeffs]
    rhs = " + ".join(ts[:5])
    if len(ts) > 5:
        rhs += "\n      + " + " + ".join(ts[5:])
    w("theorem comb_at_%d (c : Fin 13 → ℤ) :\n    comb c %d = %s := by\n" % (p, p, rhs))
    w("  simp +decide only [comb, rel1, rel2, rel3, rel4, rel5, rel6, rel7, rel8, rel9, rel10,\n")
    w("    rel11, rel12, rel13, Pi.add_apply, Pi.single_apply, ↓reduceIte]\n")
    w("  ring\n\n")

# span coefficients: g = 4 f - comb c vanishes at the pivots
d = [rels[k][piv[k]] for k in range(13)]          # diagonal: 1 or 4 or 2 (and -1 for k = 0)
cexpr = [None] * 13
for k in range(1, 13):
    m = 4 // d[k]
    cexpr[k] = ("%d * f %d" % (m, piv[k])) if m != 1 else ("f %d" % piv[k])
# pivot 0: 4 f 0 = sum_k c_k rel_k(0)  =>  c_0 = -(4 f 0 - sum_{k>=1} c_k rel_k(0))
terms0 = ["4 * f 0"]
for k in range(1, 13):
    e = rels[k].get(0, 0)
    if e != 0:
        m = 4 // d[k]
        terms0.append("%d * f %d" % (-e * m, piv[k]))
cexpr[0] = "-(" + " + ".join(terms0[:5]) + chr(10) + "      + " + " + ".join(terms0[5:]) + ")"
w("/-- The coefficients that express `4 f` by the 13 relations. -/\n")
w("def spanCoeff (f : ℕ → ℤ) : Fin 13 → ℤ :=\n  ![%s,\n    %s,\n    %s]\n\n" % (
    cexpr[0], ", ".join(cexpr[1:7]), ", ".join(cexpr[7:])))
for k in range(13):
    w("theorem spanCoeff_%d (f : ℕ → ℤ) :" % k + chr(10) + "    spanCoeff f %d = %s := rfl" % (k, cexpr[k]) + chr(10) + chr(10))

w("/-- `4 f - comb (spanCoeff f)` vanishes at the 13 pivot exponents. -/\n")
w("theorem span_pivots (f : ℕ → ℤ) : ∀ j ∈ R0Exps, j ∉ B11 →\n")
w("    4 * f j + -1 * comb (spanCoeff f) j = 0 := by\n")
w("  intro j hj hnj\n")
w("  simp only [R0Exps, Finset.mem_insert, Finset.mem_singleton] at hj\n")
w("  rcases hj with " + " | ".join(["rfl"] * 12) + "\n    | " + " | ".join(["rfl"] * 12) + "\n")
for j in R0:
    if j in B11:
        w("  · exact absurd (by decide) hnj\n")
    else:
        ks = ["spanCoeff_%d" % k for k, r in enumerate(rels) if r.get(j, 0) != 0]
        used = ", ".join(ks[:5]) + ((","+chr(10)+"      " + ", ".join(ks[5:])) if len(ks) > 5 else "")
        w("  · rw [comb_at_%d]" % j + chr(10) + "    simp only [%s]" % used + chr(10) + "    ring" + chr(10))
w("\n")

w("/-- **Every relation among the 24 numbers is a rational combination of the 13.**\n")
w("If `f` is a relation on `R0Exps`, then `4 f` is an integer combination of `rel1, ..., rel13`. -/\n")
w("theorem relations_span {f : ℕ → ℤ} (h : IsRelJ R0Exps f) :\n")
w("    ∃ c : Fin 13 → ℤ, ∀ j ∈ R0Exps, 4 * f j = comb c j := by\n")
w("  refine ⟨spanCoeff f, ?_⟩\n")
w("  have hg : IsRelJ R0Exps (fun j => 4 * f j + -1 * comb (spanCoeff f) j) :=\n")
w("    (h.zsmul 4).add ((comb_isRel (spanCoeff f)).zsmul (-1))\n")
w("  have hpiv := span_pivots f\n")
w("  have hB := basis_independent (hg.restrict (by decide) hpiv)\n")
w("  intro j hj\n")
w("  by_cases hjB : j ∈ B11\n")
w("  · have h0 := hB j hjB\n    omega\n")
w("  · have h0 := hpiv j hj hjB\n    omega\n\n")

w("/-- **The 13 relations are linearly independent.** -/\n")
w("theorem rel_independent {c : Fin 13 → ℤ} (h : ∀ j ∈ R0Exps, comb c j = 0) :" + chr(10) + "    ∀ k, c k = 0 := by" + chr(10))
for p in piv:
    w("  have h%d := h %d (by decide)\n  rw [comb_at_%d] at h%d\n" % (p, p, p, p))
w("  intro k\n  fin_cases k\n")
order = piv  # relation k (0-based) has pivot piv[k]
for k in range(13):
    w("  · show c %d = 0\n    omega\n" % k)
w("\n")
sys.stdout.buffer.write(out.getvalue().encode("utf-8"))
