"""Lean statements and proofs for the degree-1 formulas of Bailey's Compendium.

    python compendium_lean.py [--write] [--status] [--axioms]

(--status writes LEAN_STATUS.md only and leaves the generated Lean files alone.)

Reads  literature/bailey-compendium/ledger.json  (the source of truth: for each formula its
constant, prefactor, base, length and integer vector, and for the formulas that follow from
the classification their exact coordinates in the project's basis) and, with --write, writes

    lean/Pilean/Compendium/Base2Pi.lean     formulas 1, 2, 3, 6, 17, 18, 19
    lean/Pilean/Compendium/Base2Sqrt.lean   formulas 20, 21, 22
    lean/Pilean/Compendium/Base2Zero.lean   zero relations 111 to 122
    lean/Pilean/Compendium/Base3.lean       formulas 69, 130, 131
    lean/Pilean/Compendium/Logs.lean        formulas 7, 8, 67, 70 to 75, 84, 85, 89
    literature/bailey-compendium/LEAN_STATUS.md

Each of these Lean files is generated in full: statements and proofs.  The other files of
lean/Pilean/Compendium (Defs.lean, Series.lean, Arctan.lean, Base5.lean) are written by hand;
for each theorem `formula_*` in them this program builds the statement from the ledger (or,
for the formulas that are not in the notation P, takes it from HAND_TEXT below) and checks
that the file contains it, character for character up to white space.

The formulas with a parameter b (section "General bases", the telescoping example of page 4),
the two curiosities (132, 133) and formula 88 are in the hand-written files GeneralLog.lean,
GeneralArctan.lean, GeneralSqrt.lean and Curiosities.lean (with GeneralDefs.lean and
GeneralCore.lean): see GENERAL below.  For these the program checks the ledger entry
numerically and checks that each named theorem is in its file; the statements themselves were
compared with the ledger numerically when they were written.

Before anything is written, every formula that gets a Lean statement is checked numerically
from the ledger, vector and value, at 70 digits; agreement to 50 digits is required.  A
formula that fails is not stated.  The logarithm formulas are also checked exactly, as an
identity between integer combinations of logarithms of primes.

With --axioms the file  lean/ScratchCL/Axioms.lean  is written: it imports every module and
prints the axioms of every theorem `formula_*`.  Compile it with `lake env lean`, then delete
the folder.

Needs mpmath and sympy; imports compendium_check.py from this folder.  Output is ASCII; the
Lean files are UTF-8 with LF line endings.
"""
import ast
import io
import json
import os
import re
import sys
from fractions import Fraction

import sympy
from mpmath import mp

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import compendium_check as cc  # noqa: E402

ROOT = os.path.dirname(HERE)
LEAN = os.path.join(ROOT, "lean")
LEAN_DIR = os.path.join(LEAN, "Pilean", "Compendium")
STATUS_MD = os.path.join(cc.LEDGER_DIR, "LEAN_STATUS.md")
SCRATCH = os.path.join(LEAN, "ScratchCL")
NEED = 50
WIDTH = 100

NAMED = ["namedA1", "namedA6", "namedA10", "namedL6", "namedL8", "namedL10", "namedL24",
         "namedTW"]
EXTRA = ["extraS2", "extraS3", "extraS5"]

# ---- which formula goes where ------------------------------------------------------------
# Generated files: file -> (title, list of ids).
GENERATED = [
    ("Base2Pi", "the formulas for pi in base 2", ["1", "2", "3", "6", "17", "18", "19"]),
    ("Base2Sqrt", "the formulas for sqrt(2) pi, sqrt(3) pi, sqrt(5) pi in base 2",
     ["20", "21", "22"]),
    ("Base2Zero", "the zero relations 111 to 122 in base 2",
     ["111", "112", "113", "114", "115", "116", "117", "118", "119", "120", "121", "122"]),
    ("Base3", "formulas 69, 130 and 131 in base 3", ["69", "130", "131"]),
    ("Logs", "explicit logarithm formulas",
     ["7", "8", "67", "70", "71", "72", "73", "74", "75", "84", "85", "89"]),
]

# Hand-written theorems: id -> (file, how).  A formula of type P must appear in the file with
# the statement built from the ledger; the series (type "series") are stated by hand, and
# their statement is given here as the text that the file must contain.
HAND = {
    "4": ("Series", "from `hasSum_log_two`"),
    "p02.g": ("Series", "from `bbp_formula`, the four fractions combined"),
    "p25.b": ("Series", "from `hasSum_log_three` and a telescoping series"),
    "p25.c": ("Series", "from `hasSum_log_three`"),
    "p05.c": ("Series", "the four steps, from formulas 4 and 8 and the series of "
              "log(1 - 1/4)"),
    "p05.e": ("Series", "the norm of 1 +- (1+i)/2^n, for every n >= 1"),
    "10": ("Arctan", "formula 17 minus 8 times the series of arctan(1/2)"),
    "13": ("Arctan", "formula 17 and the series of arctan(1/2), regrouped to length 40, the "
           "series of arctan(1/32), and relations 119, 120, 121"),
    "28": ("Arctan", "formula 17 and the series of arctan(1/2), regrouped to length 24, and "
           "the series of arctan(1/8)"),
    "23": ("Arctan", "the series of log((1+x)/(1-x)) at x = 1/sqrt(2), regrouped"),
    "24": ("Arctan", "the series of arctan at x = 1/sqrt(2), regrouped"),
    "25": ("Arctan", "formula 17 plus 8 times the series of arctan(1/2)"),
    "26": ("Arctan", "formula 17 minus 4 times the series of arctan(1/2)"),
    "27": ("Arctan", "formula 17 plus 24 times the series of arctan(1/2)"),
    "68": ("Arctan", "the imaginary part of the series of -log(1 - w/3), w a cube root of "
           "unity"),
    "86": ("Arctan", "the series of log((1+x)/(1-x)) at x = 1/sqrt(5)"),
    "87": ("Base5", "the series of cos(k t) x^k / k at x = 1/5, t = 2 pi/5 and 4 pi/5, with "
           "log(1 - 1/5) and log(1 - 5^(-5))"),
}

HAND_TEXT = {
    "4": "theorem formula_4 :\n    HasSum (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ) * 2 ^ (k + 1))) "
         "(Real.log 2)",
    "p02.g": "theorem formula_p02_g :\n    HasSum (fun k : ℕ => (47 + 151 * (k : ℝ) + 120 * "
             "(k : ℝ) ^ 2) /\n      (16 ^ k * (15 + 194 * (k : ℝ) + 712 * (k : ℝ) ^ 2 + 1024 * "
             "(k : ℝ) ^ 3 + 512 * (k : ℝ) ^ 4)))\n      Real.pi",
    "p25.b": "theorem formula_p25_b : ∃ S : ℝ,\n    HasSum (fun k : ℕ => (27 / (2 * (k : ℝ) + 1) "
             "+ 4 / (2 * (k : ℝ) + 2) + 1 / (2 * (k : ℝ) + 3)) /\n      9 ^ (k + 1)) S ∧ "
             "Real.log 3 = 1 / 4 + 1 / 4 * S",
    "p25.c": "theorem formula_p25_c :\n    HasSum (fun k : ℕ => (9 / (2 * (k : ℝ) + 1) + 1 / "
             "(2 * (k : ℝ) + 2)) / 9 ^ (k + 1)) (Real.log 3)",
    "p05.c": "theorem formula_p05_c : Real.log 3 = 2 * Real.log 2 + Real.log (1 - 1 / 4) ∧ "
             "(∃ S T : ℝ, HasSum (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ) * 2 ^ (k + 1))) S ∧ "
             "HasSum (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ) * 4 ^ (k + 1))) T ∧ "
             "Real.log 3 = 2 * S - T) ∧ (∃ S T : ℝ, HasSum (fun k : ℕ => "
             "(2 / (2 * (k : ℝ) + 1) + 1 / (2 * (k : ℝ) + 2)) / 4 ^ k) S ∧ "
             "HasSum (fun k : ℕ => 2 / (2 * (k : ℝ) + 2) / 4 ^ k) T ∧ "
             "Real.log 3 = 1 / 2 * S - 1 / 4 * T) ∧ "
             "HasSum (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) / 4 ^ k) (Real.log 3)",
    "p05.e": "theorem formula_p05_e (n : ℕ) (hn : 1 ≤ n) : "
             "(Complex.log (1 + (1 + Complex.I) / 2 ^ n)).re = (1 / 2 - n) * Real.log 2 + "
             "1 / 2 * Real.log (2 ^ (2 * n - 1) + 2 ^ n + 1) ∧ "
             "(Complex.log (1 - (1 + Complex.I) / 2 ^ n)).re = (1 / 2 - n) * Real.log 2 + "
             "1 / 2 * Real.log (2 ^ (2 * n - 1) - 2 ^ n + 1)",
}

# Extra theorems of the hand-written files that are not entries of the ledger: formulas (1)
# and (2) as the explicit series that are printed (the ledger records them in the notation P).
EXTRA_THEOREMS = [("formula_1_series", "Series"), ("formula_2_series", "Series")]

# Formulas with a parameter b, the curiosities 132 and 133, and formula 88 (irrational
# prefactor and left side; it is in Curiosities.lean): id -> (file, theorems, range, how).
# `theorems` lists the Lean theorems: `formula_N_real` (real parameter b, in the form
# BaileyFormulaReal of GeneralDefs.lean) and `formula_N` (natural b >= 2, in the form
# BaileyFormula / BaileyFormulaInt).  `range` is the set of real b of the real version.
_W3 = "w a cube root of unity"
_EIS = "c = (3 + i sqrt 3)/2"
GENERAL = {
    "p04.b": ("GeneralLog", ["formula_p04_b_real", "formula_p04_b"], "b < -1 or b > 1",
              "the series of -log(1 - 1/b) and the same series without its first two terms"),
    "90": ("GeneralLog", ["formula_90_real", "formula_90"], "b < -1 or b > 1",
           "the series of -log(1 - 1/b) and the real part of the series of -log(1 - w/b), "
           + _W3),
    "91": ("GeneralLog", ["formula_91"], None,
           "natural b >= 2 only (the length is b): a series of step 1, a combination of "
           "log(1 - 1/b) and log(1 - b^(-b)); the printed vector has b - 1 entries, the "
           "entry a_b = 0 is supplied"),
    "92": ("GeneralSqrt", ["formula_92_real", "formula_92"], "b > 1",
           "the series of arctan at x = 1/sqrt(b), summed in pairs"),
    "93": ("GeneralArctan", ["formula_93_real", "formula_93"], "b < -1 or b > 1",
           "the imaginary part of the series of -log(1 + w/b), " + _W3),
    "94": ("GeneralArctan", ["formula_94_real", "formula_94"], "b < -1 or b > 1",
           "the imaginary part of the series of -log(1 - w/b), " + _W3),
    "95": ("GeneralArctan", ["formula_95_real", "formula_95"], "2 b^2 > 1",
           "the imaginary part of the series of -log(1 - (1+i)/(2b))"),
    "96": ("GeneralArctan", ["formula_96_real", "formula_96"], "2 b^2 > 1",
           "the imaginary part of the series of -log(1 + (1+i)/(2b))"),
    "97": ("GeneralSqrt", ["formula_97_real", "formula_97"], "b > 1",
           "the imaginary parts of the series of -log(1 - v(1+i)) at v and at -v, "
           "v = 1/sqrt(2b)"),
    "98": ("GeneralArctan", ["formula_98_real", "formula_98"], "3 b^2 > 1",
           "the imaginary part of the series of -log(1 - c/(3b)), " + _EIS),
    "99": ("GeneralArctan", ["formula_99_real", "formula_99"], "3 b^2 > 1",
           "the imaginary part of the series of -log(1 + c/(3b)), " + _EIS),
    "100": ("GeneralSqrt", ["formula_100_real", "formula_100"], "b > 1",
            "the imaginary parts of the series of -log(1 - v c) at v and at -v, "
            "v = 1/sqrt(3b), " + _EIS),
    "101": ("GeneralLog", ["formula_101_real", "formula_101"], "b < -1 or b > 1",
            "the series of -log(1 + 1/b)"),
    "102": ("GeneralLog", ["formula_102_real", "formula_102"], "b < -1 or b > 1",
            "the series of -log(1 - 1/b)"),
    "103": ("GeneralSqrt", ["formula_103_real", "formula_103"], "b > 1",
            "the series of log((1+x)/(1-x)) at x = 1/sqrt(b)"),
    "104": ("GeneralLog", ["formula_104_real", "formula_104"], "b < -1 or b > 1",
            "the real part of the series of -log(1 - w/b), " + _W3),
    "105": ("GeneralLog", ["formula_105_real", "formula_105"], "b < -1 or b > 1",
            "the real part of the series of -log(1 + w/b), " + _W3),
    "106": ("GeneralLog", ["formula_106_real", "formula_106"], "2 b^2 > 1",
            "the real part of the series of -log(1 - (1+i)/(2b))"),
    "107": ("GeneralLog", ["formula_107_real", "formula_107"], "2 b^2 > 1",
            "the real part of the series of -log(1 + (1+i)/(2b))"),
    "108": ("GeneralSqrt", ["formula_108_real", "formula_108"], "b > 1",
            "the real parts of the series of -log(1 - v(1+i)) at v and at -v, "
            "v = 1/sqrt(2b)"),
    "109+": ("GeneralLog", ["formula_109_plus_real", "formula_109_plus"], "3 b^2 > 1",
             "the real part of the series of -log(1 + c/(3b)), " + _EIS),
    "109-": ("GeneralLog", ["formula_109_minus_real", "formula_109_minus"], "3 b^2 > 1",
             "the real part of the series of -log(1 - c/(3b)), " + _EIS),
    "110": ("GeneralSqrt", ["formula_110_real", "formula_110"], "b > 1",
            "the real parts of the series of -log(1 - v c) at v and at -v, v = 1/sqrt(3b), "
            + _EIS),
    "88": ("Curiosities", ["formula_88"], None,
           "the series of sin(2 pi k/5) x^k / k and of sin(4 pi k/5) x^k / k at x = 1/5, with "
           "the values t1 and t2; the two arctangents of the print are t2 - t1 and t1 + t2, "
           "and 5^(1/4) = 2 sin(pi/5) sqrt(phi)"),
    "132": ("Curiosities", ["formula_132"], None,
            "stated with `BaileyFormulaReal` (irrational base and coefficients): the series "
            "of sin(k pi/5) x^k / k at x = phi/2 = cos(pi/5)"),
    "133": ("Curiosities", ["formula_133"], None,
            "for every sequence with D_0 = D_1 = 1 and D_(k+1) = D_k - 5 D_(k-1) for k >= 1 "
            "(the print says k >= 2, which leaves D_2 free): the imaginary part of the series "
            "of -log(1 - a/10), a = (1 + i sqrt 19)/2"),
}

# Not done: id -> reason.  Every degree-1 formula is in GENERATED, HAND, GENERAL or here.
NOT_DONE = {}


# ---- ledger expressions as Lean terms --------------------------------------------------

def _lx(node):
    """(text, precedence) of a ledger expression as a Lean term over the reals."""
    if isinstance(node, ast.Constant):
        return str(node.value), 1024
    if isinstance(node, ast.Name):
        return {"pi": "Real.pi", "phi": "Real.goldenRatio"}[node.id], 1024
    if isinstance(node, ast.UnaryOp):
        assert isinstance(node.op, ast.USub)
        return "-" + _par(_lx(node.operand), 75), 75
    if isinstance(node, ast.Call):
        f = {"log": "Real.log", "sqrt": "Real.sqrt", "atan": "Real.arctan"}[node.func.id]
        return f + " " + _par(_lx(node.args[0]), 1024), 1023
    if isinstance(node, ast.BinOp):
        op = type(node.op)
        if op is ast.Pow:
            # The exponent is a natural number (a power of a real) or a real expression
            # (`Real.rpow`).  A quotient of integers such as 13/4 would be read by Lean as
            # a quotient of natural numbers: such a statement is refused.
            r = node.right
            is_nat = isinstance(r, ast.Constant) and isinstance(r.value, int) and r.value >= 0
            is_real = isinstance(r, ast.Call) or (isinstance(r, ast.Name) and r.id in
                                                  ("pi", "phi"))
            if not (is_nat or is_real):
                raise ValueError("exponent not supported: " + ast.unparse(node))
            return _par(_lx(node.left), 76) + " ^ " + _par(_lx(node.right), 75), 75
        p, sym = {ast.Add: (65, "+"), ast.Sub: (65, "-"), ast.Mult: (70, "*"),
                  ast.Div: (70, "/")}[op]
        return _par(_lx(node.left), p) + " " + sym + " " + _par(_lx(node.right), p + 1), p
    raise ValueError(ast.dump(node))


def _par(sp, need):
    s, p = sp
    return s if p >= need else "(" + s + ")"


def lean_term(expr):
    """A ledger expression as a Lean term (not parenthesized)."""
    return _lx(ast.parse(expr.replace("^", "**"), mode="eval").body)[0]


def lean_arg(expr):
    """A ledger expression as a Lean function argument (parenthesized if it is not atomic)."""
    return _par(_lx(ast.parse(expr.replace("^", "**"), mode="eval").body), 1024)


def frac(q):
    """A rational number as a Lean term."""
    q = Fraction(q)
    return str(q.numerator) if q.denominator == 1 else "%d / %d" % (q.numerator, q.denominator)


def parse_base(bstr):
    """A printed base: (negative?, number, exponent).  '2^12' -> (False, 2, 12); '-4' ->
    (True, 4, 1); '-2^30' -> (True, 2, 30), which means -(2^30)."""
    s = bstr.strip()
    neg = s.startswith("-")
    if neg:
        s = s[1:]
    if "^" in s:
        b, e = s.split("^")
        return neg, int(b), int(e)
    return neg, int(s), 1


def root_exponent(b, root):
    """j with root^j = b."""
    j, x = 0, 1
    while x < b:
        x *= root
        j += 1
    assert x == b, (b, root)
    return j


def wrap(items, indent, sep=", ", open_="![", close="]"):
    """A bracketed list wrapped at WIDTH columns; continuation lines are indented by two more
    spaces."""
    lines = []
    cur = " " * indent + open_
    for i, it in enumerate(items):
        piece = it + (sep if i < len(items) - 1 else close)
        if len(cur) + len(piece.rstrip()) > WIDTH and cur.strip() != open_.strip():
            lines.append(cur.rstrip())
            cur = " " * (indent + 2) + piece
        else:
            cur += piece
    if not items:
        cur += close
    lines.append(cur.rstrip())
    return "\n".join(lines)


def thm_name(fid):
    return "formula_" + fid.replace(".", "_")


# ---- statements ------------------------------------------------------------------------

class Formula:
    """A degree-1 formula of type P with one term, read from the ledger."""

    def __init__(self, e):
        self.e = e
        self.id = e["id"]
        c = e["content"]
        assert c["type"] == "P" and len(c["rhs"]) == 1, self.id
        t = c["rhs"][0]
        assert t["s"] == 1
        self.lhs = c["lhs"]
        self.coef = t["coef"]
        self.base = t["b"]
        self.n = t["n"]
        self.A = list(t["A"])
        self.neg, self.pb, self.pe = parse_base(self.base)
        self.d1 = e["checks"].get("degree1", {})
        self.coef_q = Fraction(cc.ev(self.coef))
        self.A_q = [Fraction(cc.ev(a)) for a in self.A]
        assert all(a.denominator == 1 for a in self.A_q), self.id

    def vector(self, indent=4):
        return wrap([lean_term(a) for a in self.A], indent)

    def statement(self):
        """The Lean statement: `theorem formula_N : BaileyFormula x c b B N ![...]`."""
        if self.neg:
            beta = "(-%d)" % self.pb if self.pe == 1 else "(-%d ^ %d)" % (self.pb, self.pe)
            head = "theorem %s : BaileyFormulaInt %s %s %s 1 %d" % (
                thm_name(self.id), lean_arg(self.lhs), lean_arg(self.coef), beta, self.n)
        else:
            head = "theorem %s : BaileyFormula %s %s %d %d %d" % (
                thm_name(self.id), lean_arg(self.lhs), lean_arg(self.coef), self.pb, self.pe,
                self.n)
        one = head + " ![" + ", ".join(lean_term(a) for a in self.A) + "]"
        if len(one) + len(" := by") <= WIDTH:
            return one
        return head + "\n" + self.vector()

    def doc(self):
        """A one-line description for the docstring."""
        vec = "(" + ", ".join(self.A) + ")" if self.n <= 12 else "A) with the %d entries below" \
            % self.n
        co = "" if self.coef == "1" else self.coef + " "
        txt = "%s = %sP(1, %s, %d, %s" % (self.lhs, co, self.base, self.n, vec)
        if self.n <= 12:
            txt += ")"
        return txt


def docstring(text):
    """A docstring wrapped at WIDTH columns."""
    words = ("/-- " + text + " -/").split(" ")
    lines, cur = [], ""
    for w in words:
        if cur and len(cur) + 1 + len(w) > WIDTH:
            lines.append(cur)
            cur = w
        else:
            cur = (cur + " " + w) if cur else w
    lines.append(cur)
    return "\n".join(lines)


def normalize(s):
    return " ".join(s.split())


# ---- proofs ----------------------------------------------------------------------------

def coords(f):
    """Coordinates of the pattern of the printed vector A: the ledger gives those of
    coef * A."""
    cn = f.d1.get("coordinates_named")
    assert cn, f.id
    assert set(cn) <= set(NAMED) | set(EXTRA), cn
    q = [Fraction(cc.ev(cn.get(nm, "0"))) / f.coef_q for nm in NAMED]
    s = [Fraction(cc.ev(cn.get(nm, "0"))) / f.coef_q for nm in EXTRA]
    return q, s


def proof_class_F(f):
    """Base 2, the classification: the pattern of A is an explicit combination of the named
    patterns (`decide +kernel` on one period of 120)."""
    assert f.d1["root_base"] == 2
    B = f.d1["B"]
    step = f.d1["step"]
    q, s = coords(f)
    sq = any(s)
    j = root_exponent(f.pb, 2)
    out = []
    qv = "![" + ", ".join(frac(x) for x in q) + "]"
    sv = "![" + ", ".join(frac(x) for x in s) + "]"
    if sq:
        val = "combSValue %s %s" % (qv, sv)
        fin = ["(by", "    simp only [combSValue, Matrix.cons_val_zero, Matrix.cons_val_one, "
               "Matrix.cons_val]", "    push_cast", "    ring)"]
    else:
        c = q[0] + q[2]
        val = "((%s : ℚ) : ℝ) * (Real.pi / 4)" % frac(c)
        fin = ["(by", "    push_cast", "    ring)"]
    ctor = "HasBaileyValueInt.formula" if f.neg else "HasBaileyValue.formula"
    head = "  refine %s (S := %s) ?_" % (ctor, val)
    if len(head) + 1 + len(fin[0]) > WIDTH:
        out.append("  refine %s" % ctor)
        out.append("    (S := %s) ?_ %s" % (val, fin[0]))
    else:
        out.append(head + " " + fin[0])
    out.extend(fin[1:])
    if f.neg:
        # P(1, -b, N, A) from its paired form P(1, b^2, 2N, A') with b = 2^(j e)
        assert f.pe == 1 or f.pb == 2
        e_tot = j * f.pe
        assert 2 * e_tot == B and step == 2 and 2 * f.n == 2 * B, f.id
        out.append("  refine hasBaileyValueInt_of_pair (b := 2 ^ %d) (N := %d) (by norm_num) "
                   "(by norm_num) one_pos ?_" % (e_tot, f.n))
        out.append("  refine HasBaileyValue.of_pow (a := 2) (j := %d) (B := 2 * 1) ?_" % e_tot)
    else:
        assert j * f.pe == B, f.id
        if j != 1:
            out.append("  refine HasBaileyValue.of_pow (a := 2) (j := %d) (B := %d) ?_"
                       % (j, f.pe))
    m = 120 // (2 * B)
    assert 2 * B * m == 120, f.id
    if step == 2:
        lem = "hasBaileyValue_F2_S" if sq else "hasBaileyValue_F2"
    else:
        assert step == 1 and not f.neg and f.n == B
        lem = "hasBaileyValue_F1_S" if sq else "hasBaileyValue_F1"
    args = [qv] + ([sv] if sq else [])
    line = "  exact %s (B := %d) (by norm_num) (m := %d) rfl _" % (lem, B, m)
    tail = "(by decide +kernel)" + ("" if sq else " (by norm_num)")
    for a in args + [tail]:
        if len(line) + 1 + len(a) > WIDTH:
            out.append(line)
            line = "    " + a
        else:
            line += " " + a
    out.append(line)
    return out


def proof_known(f):
    """The entries whose statement is already a Lean theorem."""
    i = f.id
    if i in ("1", "6"):
        return ["  exact HasBaileyValue.formula bbp_formula (one_mul _).symm"]
    if i == "7":
        return ["  have h : HasBaileyValue 2 1 1 ![1 / 2] (Real.log 2) := hasSum_log_two",
                "  refine ((h.smul 2).of_eq (by decide +kernel) rfl).formula ?_",
                "  push_cast",
                "  ring"]
    if i == "70":
        return ["  have h : HasBaileyValue 3 2 2 ![1, 1 / 9] (Real.log 3) := hasSum_log_three",
                "  refine HasBaileyValue.formula (S := ((9 : ℚ) : ℝ) * Real.log 3) ?_ (by",
                "    push_cast",
                "    ring)",
                "  refine HasBaileyValue.of_pow (a := 3) (j := 2) (B := 1) ?_",
                "  exact (h.smul 9).of_eq (by decide +kernel) rfl"]
    if i == "69":
        return ["  have h : HasBaileyValue 3 6 (2 * 6) Base3.broadhurst "
                "(9 * (Real.pi * Real.sqrt 3)) := by",
                "    rw [HasBaileyValue, baileyBlock_three]",
                "    exact Base3.broadhurst_formula",
                "  refine HasBaileyValue.formula h ?_",
                "  ring"]
    if i in ("130", "131"):
        return ["  have h : HasBaileyValue 3 6 (2 * 6) Base3.rel%s 0 := by" % i,
                "    rw [HasBaileyValue, baileyBlock_three]",
                "    exact Base3.relation%s" % i,
                "  exact HasBaileyValue.formula (HasBaileyValue.of_pow (a := 3) (j := 6) "
                "(B := 1) h)",
                "    (mul_zero _).symm"]
    raise KeyError(i)


def prime_vec(m):
    """log m as a dict prime -> exponent."""
    return {int(p): int(k) for p, k in sympy.factorint(m).items()}


def is_atom(m):
    """m is a prime: `Real.log m` is kept as it is."""
    v = prime_vec(m)
    return len(v) == 1 and list(v.values()) == [1]


def lin_logs(v):
    """A combination of logarithms of primes as Lean text, in the shape that
    `Real.log_mul` and `Real.log_pow` produce."""
    parts = []
    for p in sorted(v):
        parts.append("Real.log %d" % p if v[p] == 1 else "%d * Real.log %d" % (v[p], p))
    return " + ".join(parts)


def prod_text(v):
    return " * ".join("%d" % p if v[p] == 1 else "%d ^ %d" % (p, v[p]) for p in sorted(v))


def have_eq(name, lhs, rhs, indent=2):
    """Lines `have name : lhs = rhs := by`, broken after `=` and at ` + ` when too long."""
    pad = " " * indent
    one = "%shave %s : %s = %s := by" % (pad, name, lhs, rhs)
    if len(one) <= WIDTH:
        return [one]
    out = ["%shave %s : %s =" % (pad, name, lhs)]
    cur = pad + "    "
    parts = rhs.split(" + ")
    for k, p in enumerate(parts):
        piece = p + (" +" if k < len(parts) - 1 else " := by")
        if len(cur) + len(piece) > WIDTH and cur.strip():
            out.append(cur.rstrip())
            cur = pad + "      " + piece + " "
        else:
            cur += piece + " "
    out.append(cur.rstrip())
    return out


def log_lemma(m):
    """Lines proving `l<m> : Real.log m = sum of e_p log p`, for a composite m."""
    v = prime_vec(m)
    assert m > 1 and not is_atom(m), m
    rws = ["show (%d : ℝ) = %s by norm_num" % (m, prod_text(v))]
    rws += ["Real.log_mul (by norm_num) (by norm_num)"] * (len(v) - 1)
    npow = sum(1 for p in v if v[p] > 1)
    rws += ["Real.log_pow"] * npow
    out = have_eq("l%d" % m, "Real.log %d" % m, lin_logs(v))
    out.append(wrap(rws, 4, open_="rw [", close="]"))
    if npow:
        out.append("    push_cast")
        out.append("    ring")
    return out


def proof_log(f):
    """A series of step 1 whose pattern g(k) = a_k b^k depends on gcd(k, N) only: a
    combination of the logarithms log(1 - b^(-d)), d | N."""
    r = f.d1["root_base"]
    N = f.n
    j = root_exponent(f.pb, r)
    assert not f.neg and f.d1["step"] == 1 and j * f.pe == N, f.id
    g = [f.A_q[i - 1] * r ** i for i in range(1, N + 1)]
    divs = [d for d in range(1, N + 1) if N % d == 0]
    c = {}
    for d in divs:
        c[d] = g[d - 1] - sum(c[d2] for d2 in divs if d2 < d and d % d2 == 0)
    for i in range(1, N + 1):
        assert g[i - 1] == sum(c[d] for d in divs if i % d == 0), (f.id, i)
    L = [(d, c[d]) for d in divs if c[d] != 0]
    # exact check: coef * sum c_d (log r - log(r^d - 1)/d) = lhs, in logarithms of primes
    tot = {}

    def add(v, k):
        for p, x in v.items():
            tot[p] = tot.get(p, 0) + Fraction(x) * k

    for d, cd in L:
        add(prime_vec(r), f.coef_q * cd)
        add(prime_vec(r ** d - 1), -f.coef_q * cd / d)
    node = ast.parse(f.lhs.replace("^", "**"), mode="eval").body
    assert isinstance(node, ast.Call) and node.func.id == "log", f.lhs
    Q = Fraction(cc.ev(ast.unparse(node.args[0]).replace("**", "^")))
    add(prime_vec(Q.numerator), -1)
    add(prime_vec(Q.denominator), 1)
    assert all(x == 0 for x in tot.values()), (f.id, tot)
    # Lean
    Ltxt = "[" + ", ".join("(%d, %s)" % (d, frac(cd)) for d, cd in L) + "]"
    out = []
    out.append("  have h := hasBaileyValue_step_one (b := %d) (N := %d) (by norm_num) (by norm_num)"
               % (r, N))
    out.append("    %s (by decide)" % Ltxt)
    composites = []

    def need(m):
        if m > 1 and not is_atom(m) and m not in composites:
            composites.append(m)

    used = []
    for d, _ in L:
        m = r ** d - 1
        out.append("  have t%d : logTerm %d %d = Real.log %d - Real.log %d / %d := by" %
                   (d, r, d, r, m, d))
        out.append("    exact_mod_cast logTerm_eq (b := %d) (d := %d) (m := %d) (by norm_num) "
                   "(by norm_num)" % (r, d, m))
        out.append("      (by norm_num)")
        for x in (r, m):
            if not is_atom(x) and x not in used:
                used.append(x)
    for x in used:
        need(x)
    lt = None
    if not (Q.denominator == 1 and is_atom(Q.numerator)):
        # the constant itself as a combination of logarithms of primes
        for x in (Q.numerator, Q.denominator):
            need(x)
        rws = []
        if Q.denominator != 1:
            rws.append("Real.log_div (by norm_num) (by norm_num)")
        num_c = Q.numerator in composites
        den_c = Q.denominator in composites
        if num_c:
            rws.append("l%d" % Q.numerator)
        if den_c and Q.denominator != Q.numerator:
            rws.append("l%d" % Q.denominator)
        ntxt = lin_logs(prime_vec(Q.numerator))
        if Q.denominator != 1:
            dv = prime_vec(Q.denominator)
            dtxt = lin_logs(dv)
            if len(dv) > 1:
                dtxt = "(" + dtxt + ")"
            rhs = ntxt + " - " + dtxt
        else:
            rhs = ntxt
        lt = have_eq("lt", lean_term(f.lhs), rhs) + [wrap(rws, 4, open_="rw [", close="]")]
    for m in composites:
        out.extend(log_lemma(m))
    if lt:
        out.extend(lt)
    if j != 1:
        out.append("  refine (HasBaileyValue.of_pow (a := %d) (j := %d) (B := %d)" % (r, j, f.pe))
        out.append("    (h.of_eq (by decide +kernel) rfl)).formula ?_")
    else:
        out.append("  refine (h.of_eq (by decide +kernel) rfl).formula ?_")
    rws = (["lt"] if lt else []) + ["listVal_cons"] * len(L) + ["listVal_nil"]
    rws += ["t%d" % d for d, _ in L]
    rws += ["Real.log_one" if m == 1 else "l%d" % m for m in used]
    out.append(wrap(rws, 2, open_="rw [", close="]"))
    out.append("  push_cast")
    out.append("  ring")
    return out


def proof_of(f):
    i = f.id
    known = {"1": "BaseB.bbp_formula", "6": "BaseB.bbp_formula", "7": "BaseB.hasSum_log_two",
             "70": "BaseB.hasSum_log_three", "69": "Base3.broadhurst_formula",
             "130": "Base3.relation130", "131": "Base3.relation131"}
    if i in known:
        return proof_known(f), "restated from the existing theorem `%s`" % known[i]
    if f.d1.get("coordinates_named"):
        q, s = coords(f)
        names = [nm for nm, x in zip(NAMED + EXTRA, q + s) if x]
        how = "the pattern is a combination of %s (one period of 120 by `decide +kernel`)" \
            % ", ".join(names)
        if f.neg:
            how += ", after pairing the blocks of the negative base"
        return proof_class_F(f), how
    return proof_log(f), "series of step 1: a combination of log(1 - b^(-d)), d dividing n"


# ---- numerical check -------------------------------------------------------------------

def numeric_digits(e):
    r = cc.check_formula_numeric(e)
    return r["digits"] if r["status"] == "agree" else -1


# ---- files -----------------------------------------------------------------------------

HEADERS = {
    "Base2Pi": """\
# Bailey's Compendium: the formulas for `π` in base 2

Formulas (1) and (6) (Bailey, Borwein and Plouffe), (2) and (18), (3) and (19), and (17), each
stated as printed: constant, prefactor, base, length, integer vector.

* (1) and (6) are `BaseB.bbp_formula`. (1) is printed as an explicit series; it is stated here
  in the notation `P`, as formula (6) and as the ledger records it.
* (17) has base 16 and length 8. Its pattern in the class F (weights `2^(-⌊k/2⌋)`) is
  `16·namedA1`, checked on one period of 120 by `decide +kernel`; the value is
  `hasSum_of_coords`.
* (2), (3), (18), (19) have a negative base (`-4` and `-2^30`): they are stated with
  `BaileyFormulaInt` (`BaseB.baileyBlockInt`), not in a paired positive form. The proof pairs
  the blocks (`hasBaileyValueInt_of_pair`): `P(1, -b, N, A) = P(1, b^2, 2N, A')` with
  `A' = intPairCoeff (-b) 1 A`, and the pattern of `A'` is `4·namedA1`, respectively
  `2^26 (-8·namedA6 + 4·namedA10)`. (2) and (3) are printed as explicit series with `(-1)^k`;
  they are stated in the notation `P`, as (18) and (19) and as the ledger records them.
""",
    "Base2Sqrt": """\
# Bailey's Compendium: `π√2`, `π√3`, `π√5` in base 2

Formulas (20), (21), (22), stated as printed. The pattern of each vector in the class F is a
multiple of one of the patterns `extraS2`, `extraS3`, `extraS5` of
`PiFormula/FiveSeries.lean` (for (21) plus a multiple of the zero relation `namedTW`), checked
on one period of 120 by `decide +kernel` (`hasBaileyValue_F2_S`, `hasBaileyValue_F1_S`).
""",
    "Base2Zero": """\
# Bailey's Compendium: the zero relations (111) to (122)

Each relation `0 = P(1, b, n, A)` is stated as printed. The pattern of `A` in the class F is an
explicit combination of the named zero relations `namedA6`, `namedL6`, `namedL8`, `namedL10`,
`namedL24`, `namedTW` and of `namedA10 - namedA1`, checked on one period of 120 by
`decide +kernel`; the value `(q₀ + q₂) π/4 = 0` is `hasSum_of_coords`.
""",
    "Base3": """\
# Bailey's Compendium: formulas (69), (130), (131) in base 3

Broadhurst's formula for `π√3` and the two zero relations of base 729, stated as printed and
derived from `Base3.broadhurst_formula`, `Base3.relation130`, `Base3.relation131`.
""",
    "Logs": """\
# Bailey's Compendium: explicit logarithm formulas

Formulas (7), (8) (base 2), (67), (70) to (75) (base 3), (85) (base 25), (84), (89) (base 10),
stated as printed.

* (7) and (70) are `BaseB.hasSum_log_two` and `BaseB.hasSum_log_three` with the printed
  prefactor.
* The others are series of step 1, `∑_{k ≥ 1} g(k) b^(-k) / k`, where `g(k) = a_k b^k` depends
  on `gcd(k, n)` only. Then `g(k) = ∑_{d ∣ k} c_d` and the value is
  `∑ c_d · (-(1/d) log (1 - b^(-d)))` (`hasBaileyValue_step_one`). The proof of each formula
  is: the vector is the one of the list `(d, c_d)` (`decide +kernel`), each
  `log (1 - b^(-d))` is `log (b^d - 1) - d log b` (`logTerm_eq`), the integers are factored
  into primes, and the identity between logarithms of primes is `ring`.
""",
}


def lean_file(name, title, ids, F):
    out = ["/-",
           "Copyright (c) 2026 Novus Technology. All rights reserved.",
           "Released under Apache 2.0 license as described in the file LICENSE.",
           "Authors: Novus Technology",
           "-/",
           "module", "", "public import Pilean.Compendium.Defs", "",
           "/-!", HEADERS[name].rstrip("\n"), "",
           "This file is generated by `python/compendium_lean.py` from",
           "`literature/bailey-compendium/ledger.json`; do not edit it by hand.", "-/", "",
           "@[expose] public section", "",
           "namespace PiFormula", "",
           "namespace Compendium", "", "open BaseB", ""]
    hows = {}
    for i in ids:
        f = F[i]
        body, how = proof_of(f)
        hows[i] = how
        e = f.e
        out.append(docstring("**Formula (%s)** of the Compendium (page %d): `%s`." %
                             (i, e["page"], f.doc())))
        out.append(f.statement() + " := by")
        out.extend(body)
        out.append("")
    out += ["end Compendium", "", "end PiFormula", ""]
    text = "\n".join(out)
    for n, l in enumerate(text.split("\n"), 1):
        assert len(l) <= WIDTH, "%s.lean line %d has %d characters" % (name, n, len(l))
    return text, hows


def status_md(rows, counts):
    out = ["# Bailey's Compendium, degree 1: status of the Lean proofs", "",
           "Generated by `python/compendium_lean.py --write` from `ledger.json`. One row per "
           "formula of degree 1 (80 rows).", "",
           "The Lean theorems are in `lean/Pilean/Compendium/` (namespace "
           "`PiFormula.Compendium`). A formula `x = c P(1, b, n, A)`",
           "is stated as `BaileyFormula x c b B n A` (base `b^B`: a base printed as a number "
           "has `B = 1`), or",
           "`BaileyFormulaInt x c β B n A` for a negative base `β`; both are defined in "
           "`Defs.lean`. The four",
           "formulas printed as explicit series only (4, p02.g, p25.b, p25.c) are stated as "
           "`HasSum` of the printed term;",
           "p05.c is the conjunction of its four steps, p05.e a closed form for every "
           "`n >= 1`.",
           "Formulas 1, 2, 3 are printed as explicit series and stated in the notation P, "
           "as the ledger records them",
           "(they are the same statements as 6, 18, 19); `Series.lean` also has "
           "`formula_1_series` and `formula_2_series`,",
           "formulas 1 and 2 as the series that are printed. Formulas 2, 3, 18, 19 have a "
           "negative base and are stated",
           "with `BaileyFormulaInt` (not in a paired positive form).", "",
           "The formulas with a parameter `b` (90 to 110) have two theorems each: "
           "`formula_N_real`, for a real `b` in the",
           "range given in the last column, stated as `BaileyFormulaReal x c β n A` (real "
           "base `β`, real coefficients;",
           "`GeneralDefs.lean`), and `formula_N`, for a natural number `b >= 2`, stated as "
           "`BaileyFormula` or `BaileyFormulaInt`",
           "like the other formulas (a base `-b^3` is the integer `-(b : ℤ) ^ 3` with "
           "`B = 1`). The paper gives no range for `b`.",
           "Formula 91 has the length `b` and is stated for natural `b >= 2` only. The "
           "example p04.b is stated as `HasSum` of",
           "the printed term, in the same two versions. Formula 132 has an irrational base "
           "and is stated with",
           "`BaileyFormulaReal`. Formula 133 is stated for every sequence `D` with "
           "`D_0 = D_1 = 1` and the recurrence for",
           "`k >= 1`: the series of the printed term has a sum `S`, and the constant is "
           "`S/10`.", "",
           "Every stated formula was checked numerically from the ledger to at least %d digits "
           "before it was written;" % NEED,
           "the logarithm formulas of `Logs.lean` also exactly, as identities between "
           "logarithms of primes.", "",
           "Proved: %d of 80. Not done: %d." % (counts[0], counts[1]), "",
           "| id | page | constant | printed as | Lean theorem | file | proof, or why not |",
           "|---|---|---|---|---|---|---|"]
    for r in rows:
        out.append("| " + " | ".join(r) + " |")
    out.append("")
    return "\n".join(out)


def main():
    args = sys.argv[1:]
    mp.dps = 70
    led = json.load(io.open(cc.LEDGER, encoding="utf-8"))
    E = [e for e in led["entries"] if e["kind"] == "formula" and e.get("degree") == 1]
    byid = {e["id"]: e for e in E}
    assert len(E) == 80
    gen_ids = [i for _, _, ids in GENERATED for i in ids]
    covered = gen_ids + list(HAND) + list(GENERAL) + list(NOT_DONE)
    assert sorted(covered) == sorted(byid), sorted(set(byid) ^ set(covered))
    # 1. numerical check of everything that is stated
    bad = []
    for i in gen_ids + list(HAND) + list(GENERAL):
        d = numeric_digits(byid[i])
        if d < NEED:
            bad.append(i)
            print("formula %s: numerical check FAILED (%d digits)" % (i, d))
    print("numerical check at %d digits: %d formulas, %d failed" %
          (mp.dps, len(gen_ids) + len(HAND) + len(GENERAL), len(bad)))
    F = {i: Formula(byid[i]) for i in byid
         if byid[i]["content"]["type"] == "P" and i not in NOT_DONE and i not in GENERAL}
    # 2. generated files
    files, hows = {}, {}
    for name, title, ids in GENERATED:
        ids = [i for i in ids if i not in bad]
        text, hw = lean_file(name, title, ids, F)
        files[name] = text
        hows.update(hw)
    # 3. hand-written files contain the statements of the ledger
    missing = []
    for i, (fname, how) in HAND.items():
        if i in bad:
            continue
        path = os.path.join(LEAN_DIR, fname + ".lean")
        src = normalize(io.open(path, encoding="utf-8").read()) if os.path.exists(path) else ""
        want = F[i].statement() if i in F else HAND_TEXT[i]
        if normalize(want) + " :=" not in src:
            missing.append(i)
            print("formula %s: statement not found in %s.lean:\n%s" %
                  (i, fname, want.encode("ascii", "backslashreplace").decode()))
    print("hand-written statements: %d expected, %d missing" % (len(HAND), len(missing)))
    # 3b. the files of the formulas with a parameter contain the named theorems
    gen_missing = 0
    for i, (fname, names, rng, how) in GENERAL.items():
        path = os.path.join(LEAN_DIR, fname + ".lean")
        src = normalize(io.open(path, encoding="utf-8").read()) if os.path.exists(path) else ""
        for nm in names:
            if not re.search(r"theorem %s[ :({]" % re.escape(nm), src):
                gen_missing += 1
                if i not in missing:
                    missing.append(i)
                print("formula %s: theorem %s not found in %s.lean" % (i, nm, fname))
    print("theorems of the formulas with a parameter: %d expected, %d missing" %
          (sum(len(v[1]) for v in GENERAL.values()), gen_missing))
    # 4. status table
    rows = []
    done = 0
    file_of = {i: name for name, _, ids in GENERATED for i in ids}
    for e in E:
        i = e["id"]
        c = e["content"]
        if c["type"] == "P":
            t = c["rhs"][0]
            printed = "%sP(1, %s, %s, ...)" % ("" if t["coef"] == "1" else t["coef"] + " ",
                                               t["b"], t["n"])
        else:
            printed = {"series": "explicit series", "chain": "chain of equalities",
                       "identity": "closed form", "recurrence_series": "series with a "
                       "recurrence"}[c["type"]]
        const = e["constant"].replace("|", "\\|")
        if i in NOT_DONE or i in bad or i in missing:
            why = NOT_DONE.get(i, "numerical check failed" if i in bad else
                               "statement missing from the hand-written file")
            rows.append([i, str(e["page"]), const, printed, "", "", why])
        elif i in GENERAL:
            done += 1
            fname, names, rng, how = GENERAL[i]
            how = "by hand: " + how
            if rng is not None:
                how = "real b with %s, and natural b >= 2; %s" % (rng, how)
            rows.append([i, str(e["page"]), const, printed,
                         ", ".join("`%s`" % nm for nm in names), "`%s.lean`" % fname, how])
        else:
            done += 1
            if i in HAND:
                fname, how = HAND[i]
                how = "by hand: " + how
            else:
                fname, how = file_of[i], hows[i]
            rows.append([i, str(e["page"]), const, printed, "`%s`" % thm_name(i),
                         "`%s.lean`" % fname, how])
    md = status_md(rows, (done, 80 - done))
    print("degree-1 formulas: 80; with a Lean theorem: %d; not done: %d" % (done, 80 - done))
    if "--status" in args and "--write" not in args:
        with io.open(STATUS_MD, "w", encoding="utf-8", newline="\n") as fh:
            fh.write(md)
        print("wrote literature/bailey-compendium/LEAN_STATUS.md")
    if "--write" in args:
        os.makedirs(LEAN_DIR, exist_ok=True)
        for name, text in files.items():
            with io.open(os.path.join(LEAN_DIR, name + ".lean"), "w", encoding="utf-8",
                         newline="\n") as fh:
                fh.write(text)
            print("wrote lean/Pilean/Compendium/%s.lean (%d lines)" %
                  (name, text.count("\n")))
        with io.open(STATUS_MD, "w", encoding="utf-8", newline="\n") as fh:
            fh.write(md)
        print("wrote literature/bailey-compendium/LEAN_STATUS.md")
    if "--axioms" in args:
        mods = [name for name, _, _ in GENERATED] + sorted(
            set(v[0] for v in HAND.values()) | set(v[0] for v in GENERAL.values()))
        names = [thm_name(i) for i in gen_ids + list(HAND) if i not in bad and i not in missing]
        names += [n for n, _ in EXTRA_THEOREMS]
        names += [nm for i, v in GENERAL.items() if i not in bad and i not in missing
                  for nm in v[1]]
        lines = ["import Pilean.Compendium.%s" % m for m in mods]
        lines += ["", "open PiFormula.Compendium", ""]
        lines += ["#print axioms %s" % n for n in names]
        os.makedirs(SCRATCH, exist_ok=True)
        with io.open(os.path.join(SCRATCH, "Axioms.lean"), "w", encoding="utf-8",
                     newline="\n") as fh:
            fh.write("\n".join(lines) + "\n")
        print("wrote lean/ScratchCL/Axioms.lean (%d theorems)" % len(names))
    return 1 if (bad or missing) else 0


if __name__ == "__main__":
    sys.exit(main())
