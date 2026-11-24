/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.Erdos.Defs

/-!
# The algebraic core of Theorem A: the statement

Theorem A (`Defs.lean`) is proved in two steps (paper proof: `02_proof_part_II.md` in
`research/2026-11-23-erdos-pm1/`).

1. *Arithmetic* (Lemmas 1 and 2 there): from `f` one builds elements `g_n` of a group ring that
   satisfy one equation, (M), and are congruent to known elements modulo 2.
2. *Algebra* (Lemmas D and KL there): the equation (M) and the congruences force a congruence
   for the sums of the coefficients of the `g_n`.

This file states step 2 with the arithmetic removed (`AbstractTheoremA`), so that the two steps
can be proved separately. The setting:

* a finite set `ι` (in the application: the primes dividing `q`);
* for `p : ι` an exponent `s p ≥ 1`, the cyclic group `C_p = ℤ/2^(s p)` (written additively),
  an integer `π p > 1` with `v_2(π p - 1) = s p` (in the application: the prime `p` itself),
  and an integer `k p` (in the application: `v_p(q)`);
* `S = ∏_p C_p` (`Grp s`) and the group ring `ℚ[S]` (`GRing s`); for a set `n` of indices,
  `S_n` is the subgroup of the elements with zero component outside `n` (`InSub`), and
  `N_n ∈ ℚ[S]` is the sum of its elements (`normElt`); `ε` is the sum of the coefficients
  (`aug`);
* for `p : ι` an element `u p` of `S` with zero component at `p`, and
  `a_p = π p - [u p] ∈ ℚ[S]` (`aElt`), `a_n = ∏_{p ∈ n} a_p` (`aProd`);
* for every non-empty `n` an element `g n ∈ ℚ[S]` of the form `(∏_{p ∈ n} k p) N_n + 2 e` with
  `e` supported on `S_n` and with coefficients in `ℤ_(2)`.

**Statement.** If `∑_{n ≠ ∅} a_n N_{nᶜ} g_n = 0`, then for every `p₀`

  `∑_{∅ ≠ n ⊆ ι ∖ {p₀}} (∏_{p ∈ n} (π p - 1)/2^(s p)) ε(g n) ≡ (π p₀ - 1) k p₀`
  modulo `2^(s p₀ + 1) ℤ_(2)`.

Nothing is proved in this file.
-/

@[expose] public section

open scoped BigOperators

namespace PiFormula

namespace Erdos

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `S = ∏_p C_p` with `C_p = ℤ/2^(s p)`, written additively. -/
abbrev Grp (s : ι → ℕ) : Type := ∀ p : ι, ZMod (2 ^ s p)

/-- The group ring `ℚ[S]`. -/
abbrev GRing (s : ι → ℕ) : Type := AddMonoidAlgebra ℚ (Grp s)

/-- `x ∈ S_n`: the components of `x` outside `n` are zero. -/
def InSub {s : ι → ℕ} (n : Finset ι) (x : Grp s) : Prop := ∀ p, p ∉ n → x p = 0

instance {s : ι → ℕ} (n : Finset ι) (x : Grp s) : Decidable (InSub n x) :=
  inferInstanceAs (Decidable (∀ p, p ∉ n → x p = 0))

/-- `N_n`: the sum of the elements of `S_n`. -/
noncomputable def normElt (s : ι → ℕ) (n : Finset ι) : GRing s :=
  ∑ x : Grp s, if InSub n x then AddMonoidAlgebra.single x 1 else 0

/-- `ε`: the sum of the coefficients. -/
noncomputable def aug {s : ι → ℕ} (y : GRing s) : ℚ := ∑ x : Grp s, y.coeff x

/-- The coefficients lie in `ℤ_(2)`. -/
def Integral2 {s : ι → ℕ} (y : GRing s) : Prop := ∀ x : Grp s, IsZ2 (y.coeff x)

/-- The support lies in `S_n`. -/
def SuppIn {s : ι → ℕ} (n : Finset ι) (y : GRing s) : Prop :=
  ∀ x : Grp s, y.coeff x ≠ 0 → InSub n x

/-- `a_p = π p - [u p]`. -/
noncomputable def aElt {s : ι → ℕ} (π : ι → ℤ) (u : ι → Grp s) (p : ι) : GRing s :=
  AddMonoidAlgebra.single 0 (π p : ℚ) - AddMonoidAlgebra.single (u p) 1

/-- `a_n = ∏_{p ∈ n} a_p`. -/
noncomputable def aProd {s : ι → ℕ} (π : ι → ℤ) (u : ι → Grp s) (n : Finset ι) : GRing s :=
  ∏ p ∈ n, aElt π u p

/-- **The algebraic core of Theorem A.** -/
def AbstractTheoremA : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (s : ι → ℕ) (π : ι → ℤ) (k : ι → ℕ)
    (u : ι → Grp s) (g : Finset ι → GRing s),
    (∀ p, 1 ≤ s p) → (∀ p, 1 < π p) →
    (∀ p, (2 : ℤ) ^ s p ∣ π p - 1 ∧ ¬ (2 : ℤ) ^ (s p + 1) ∣ π p - 1) →
    (∀ p, u p p = 0) →
    (∀ n : Finset ι, n.Nonempty → ∃ e : GRing s, Integral2 e ∧ SuppIn n e ∧
      g n = ((∏ p ∈ n, k p : ℕ) : ℚ) • normElt s n + (2 : ℚ) • e) →
    (∑ n ∈ (Finset.univ : Finset ι).powerset.filter Finset.Nonempty,
      aProd π u n * normElt s nᶜ * g n = 0) →
    ∀ p₀ : ι, ∃ z : ℚ, IsZ2 z ∧
      (∑ n ∈ ((Finset.univ : Finset ι).erase p₀).powerset.filter Finset.Nonempty,
        (∏ p ∈ n, ((π p : ℚ) - 1) / 2 ^ s p) * aug (g n)) =
        ((π p₀ : ℚ) - 1) * k p₀ + 2 ^ (s p₀ + 1) * z

end Erdos

end PiFormula
