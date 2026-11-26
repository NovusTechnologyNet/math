#!/usr/bin/env python3
"""Print what a theorem of the library says, with no prose of ours around it.

    python scripts/statement_view.py OUT.txt [-i Module ...] Full.Theorem.Name [...]

For each named theorem the output has its statement as Lean prints it, and after the
statements every definition of this project (Pilean, TauCeti, Baker) that the statements use,
directly or through other definitions, again as Lean prints them. Comments, docstrings and
proofs are not shown: the text is made from the compiled library, not from the source files.
Definitions of Mathlib and of Lean itself are not expanded. Every numeral and every coercion
is printed with its type, so that `5 ^ (1 / 4 : ℝ)` (a real power) cannot be taken for
`5 ^ (1 / 4 : ℕ)` (the power 0): a reader of an earlier version, without these types, could not
tell the two apart.

This is the text given to the independent reader of a statement (see PRACTICES.md). Run it from
the top folder of the repository after `lake build`. `-i` adds a module to import when a
theorem is not reachable from `Pilean` (for example `-i Pilean.Erdos.Final`).

The Lean program below is written to a scratch folder, run once with `lake env lean`, and
removed. It only reads the environment and writes OUT.txt.
"""
import os
import shutil
import subprocess
import sys

LEAN = r'''
open Lean Meta Elab Command

namespace StatementView

def ours (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => [`Pilean, `TauCeti, `Baker].contains (env.header.moduleNames[idx.toNat]!).getRoot
  | none => false

def compiledRecursion (e : Expr) : Bool :=
  e.getUsedConstants.any fun c =>
    match c with
    | .str _ s => s == "brecOn" || s == "rec" || s == "below" || s == "fix"
    | _ => false

partial def closure (env : Environment) : List Name → NameSet → Array Name → Array Name
  | [], _, out => out
  | n :: rest, seen, out =>
    if seen.contains n then closure env rest seen out
    else
      let seen := seen.insert n
      let next (es : List Expr) : List Name :=
        (es.foldl (fun acc e => acc ++ e.getUsedConstants.toList) []).filter (ours env)
      match env.find? n with
      | some (.defnInfo d) => closure env (next [d.type, d.value] ++ rest) seen (out.push n)
      | some (.opaqueInfo d) => closure env (next [d.type] ++ rest) seen (out.push n)
      | some (.axiomInfo d) => closure env (next [d.type] ++ rest) seen (out.push n)
      | some (.inductInfo d) => closure env (next [d.type] ++ d.ctors ++ rest) seen (out.push n)
      | some (.ctorInfo d) => closure env (next [d.type] ++ rest) seen out
      | _ => closure env rest seen out

def block (head : String) (body : Format) : String :=
  (Format.text head ++ Format.nest 2 (Format.line ++ body)).pretty 100

def clip (s : String) : String :=
  if s.length > 6000 then (s.take 6000).toString ++ "\n  ... (cut: this definition prints longer than 6000 characters)"
  else s

def render (n : Name) : MetaM String := do
  let env ← getEnv
  let some ci := env.find? n | return s!"-- {n}: not found"
  let ty ← ppExpr ci.type
  match ci with
  | .thmInfo _ => return block s!"theorem {n} :" ty
  | .axiomInfo _ => return block s!"axiom {n} :" ty
  | .opaqueInfo _ => return block s!"opaque {n} :" ty
  | .inductInfo d =>
    let mut s := block s!"inductive {n} :" ty
    for c in d.ctors do
      if let some cc := env.find? c then
        s := s ++ "\n" ++ block s!"  | {c} :" (← ppExpr cc.type)
    return s
  | .defnInfo d =>
    let head := block s!"def {n} :" ty
    if compiledRecursion d.value then
      match ← getEqnsFor? n with
      | some eqs =>
        let mut s := head ++ "\n  -- defined by recursion; its defining equations:"
        for e in eqs do
          if let some ec := env.find? e then
            s := s ++ "\n" ++ block "  equation:" (← ppExpr ec.type)
        return s
      | none => return clip (head ++ "\n" ++ block "  :=" (← ppExpr d.value))
    else
      return clip (head ++ "\n" ++ block "  :=" (← ppExpr d.value))
  | _ => return block s!"constant {n} :" ty

elab "#statement_view " out:str ids:ident* : command => do
  let env ← getEnv
  let targets := ids.map (·.getId)
  for t in targets do
    unless env.contains t do throwError "unknown constant {t}"
  let mut seeds : List Name := []
  for t in targets do
    if let some ci := env.find? t then
      seeds := seeds ++ ci.type.getUsedConstants.toList.filter (ours env)
  let all := closure env seeds {} #[]
  let defs := all.filter fun n =>
    !(isMatcherCore env n) && !n.isInternal && !(env.isProjectionFn n)
  let text ← liftTermElabM do
    let mut s := "STATEMENTS\n==========\n"
    for t in targets do
      s := s ++ "\n" ++ (← render t) ++ "\n"
    s := s ++ s!"\nPROJECT DEFINITIONS USED BY THE STATEMENTS ({defs.size}), in order of first use\n"
    s := s ++ "====================================================================\n"
    for n in defs do
      let mod := match env.getModuleIdxFor? n with
        | some idx => toString env.header.moduleNames[idx.toNat]!
        | none => "?"
      s := s ++ s!"\n-- from module {mod}\n" ++ (← render n) ++ "\n"
    s := s ++ "\nEverything else named above is defined in Mathlib or in Lean itself.\n"
    return s
  IO.FS.writeFile out.getString text

end StatementView

set_option pp.deepTerms true
set_option pp.maxSteps 200000
set_option pp.proofs false
set_option pp.unicode.fun true
set_option pp.funBinderTypes true
set_option pp.coercions.types true
set_option pp.numericTypes true
'''


def main(argv):
    if len(argv) < 3:
        print(__doc__)
        return 2
    out = os.path.abspath(argv[1])
    imports, names, i = ["Pilean"], [], 2
    while i < len(argv):
        if argv[i] == "-i":
            imports.append(argv[i + 1])
            i += 2
        else:
            names.append(argv[i])
            i += 1
    scratch = "ScratchView"
    os.makedirs(scratch, exist_ok=True)
    src = os.path.join(scratch, "View.lean")
    with open(src, "w", encoding="utf-8", newline="\n") as fh:
        fh.write("import Lean\n" + "".join("import %s\n" % m for m in imports))
        fh.write(LEAN)
        fh.write('#statement_view "%s" %s\n' % (out.replace("\\", "/"), " ".join(names)))
    env = dict(os.environ)
    env.setdefault("LEAN_NUM_THREADS", "4")
    try:
        r = subprocess.run(["lake", "env", "lean", src], env=env)
    finally:
        shutil.rmtree(scratch, ignore_errors=True)
    if r.returncode == 0:
        print("wrote", out)
    return r.returncode


if __name__ == "__main__":
    sys.exit(main(sys.argv))
