#!/usr/bin/env python3
"""Check the form of every Lean file in the repository (no Lean needed, a few seconds).

    python scripts/check_format.py

What Lean's kernel checks is the proofs. This script checks the things around them that a
reader relies on and that the kernel does not see (see PRACTICES.md, section 1):

  every tracked .lean file
    - is a module (`module` is the first line of code) and has at most 10,000 lines;
    - has no proof gap or escape hatch: `sorry`, `native_decide`, `axiom`, `unsafe`,
      `implemented_by`, `extern`, `opaque`;
    - has nothing that runs code while the file compiles or changes how later text is read:
      `#eval` and other `#` commands, `run_cmd`, `initialize`, `macro`, `syntax`, `elab`,
      `notation`.
  every file of this project (not the vendored lean/TauCeti and lean/Baker/)
    - opens with the copyright header;
    - imports with `public import` only;
    - has no line longer than 100 characters.

Comments, docstrings and string literals are ignored when looking for words. The exceptions
are listed in ALLOWED below, each with its reason. Exit code 1 if anything is found.
"""
import re
import subprocess
import sys

HEADER = (
    "/-\n"
    "Copyright (c) 2026 Novus Technology. All rights reserved.\n"
    "Released under Apache 2.0 license as described in the file LICENSE.\n"
    "Authors: Novus Technology\n"
    "-/\n"
)

GAPS = ["sorry", "native_decide", "axiom", "unsafe", "implemented_by", "extern", "opaque"]
RUNS = ["run_cmd", "run_elab", "run_meta", "initialize", "builtin_initialize", "macro",
        "macro_rules", "syntax", "declare_syntax_cat", "elab", "elab_rules", "notation",
        "notation3", "infix", "infixl", "infixr", "prefix", "postfix"]

# (file, word): reason
ALLOWED = {
    ("lean/Pilean/Challenge/Erdos.lean", "sorry"):
        "the challenge file states the theorem for `lake comparator`; its proof is elsewhere",
}


def strip(text):
    """Blank out comments (nested), docstrings and string literals, keeping line breaks."""
    out, i, n, depth = [], 0, len(text), 0
    while i < n:
        two = text[i:i + 2]
        if depth:
            if two == "/-":
                depth += 1
                i += 2
            elif two == "-/":
                depth -= 1
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif two == "/-":
            depth = 1
            i += 2
        elif two == "--":
            while i < n and text[i] != "\n":
                i += 1
        elif text[i] == '"':
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            i += 1
            out.append('""')
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def main():
    files = subprocess.run(["git", "ls-files", "*.lean"], capture_output=True, text=True,
                           check=True).stdout.split()
    problems, notes = [], []
    word = lambda w: re.compile(r"(?<![A-Za-z0-9_.'!?])" + re.escape(w) + r"(?![A-Za-z0-9_'!?])")
    pats = [(w, word(w), "proof gap or escape hatch") for w in GAPS] + \
           [(w, word(w), "runs or re-reads at compile time") for w in RUNS]
    hash_cmd = re.compile(r"^\s*#[a-z_]+", re.M)
    for f in sorted(files):
        raw = open(f, encoding="utf-8").read().replace("\r\n", "\n")
        code = strip(raw)
        lines = raw.split("\n")
        ours = not (f.startswith("lean/TauCeti/") or f.startswith("lean/Baker/"))
        first = next((l.strip() for l in code.split("\n") if l.strip()), "")
        if first != "module":
            problems.append((f, 1, "the first line of code is not `module`"))
        if len(lines) > 10000:
            problems.append((f, len(lines), "more than 10,000 lines"))
        for w, pat, why in pats:
            for m in pat.finditer(code):
                ln = code.count("\n", 0, m.start()) + 1
                if (f, w) in ALLOWED:
                    notes.append((f, ln, "`%s` allowed: %s" % (w, ALLOWED[(f, w)])))
                else:
                    problems.append((f, ln, "`%s`: %s" % (w, why)))
        for m in hash_cmd.finditer(code):
            ln = code.count("\n", 0, m.start()) + 1
            problems.append((f, ln, "`%s`: a # command" % m.group(0).strip()))
        if ours:
            if not raw.startswith(HEADER + "module\n"):
                problems.append((f, 1, "does not open with the copyright header and `module`"))
            for i, l in enumerate(code.split("\n"), 1):
                if re.match(r"\s*(private\s+|meta\s+)*import\s", l):
                    problems.append((f, i, "plain `import`; use `public import`"))
            for i, l in enumerate(lines, 1):
                if len(l) > 100:
                    problems.append((f, i, "line of %d characters" % len(l)))
    for f, ln, msg in notes:
        print("note    %s:%d: %s" % (f, ln, msg))
    for f, ln, msg in problems:
        print("PROBLEM %s:%d: %s" % (f, ln, msg))
    print("%d Lean files checked, %d problems, %d allowed exceptions"
          % (len(files), len(problems), len(notes)))
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
