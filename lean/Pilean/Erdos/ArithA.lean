module

public import Pilean.Erdos.ArithDefs
public import Pilean.Erdos.ArithWeight

/-!
# Theorem A from the abstract theorem

Goal of the files `Arith*.lean`: `theoremA_of_abstract : AbstractTheoremA → TheoremA`.
REACHED (23 Nov 2026): it is in `Main.lean`. This file proves `theoremA_of_lemma1_ell`, Theorem A
from the abstract theorem and the two statements `Arith.Lemma1Prop` and `Arith.EllProp`
(`Prop`s defined in `ArithDefs.lean`); these are proved in `ArithLemma1.lean` (`Arith.lemma1`)
and `ArithEll.lean` (`Arith.ellProp`), following the plans kept below. Lemma 2
(`Arith.mainEq : Arith.MainEqProp`) is in `ArithWeight.lean`. No `sorry` anywhere.

## Status, file by file (all seven files compile)

* `ArithLocal.lean` (complete): the ring `ℤ/p^k`. `locV` (exponent of `p`, `k` at `0`), `locR`
  (residue of `x/p^j` mod `p`), `locT` (`t ↦ p^(k-1) t`). Proved: `loc_rep`, `loc_std`,
  `locV_lt`, `locV_eq_iff`, `locR_ne_zero`, `loc_natCast_mul`, `loc_p_mul`,
  `exists_p_mul_of_locV`, `loc_locT`, `locT_injective`, `exists_locT`, `sum_fiber_p_mul`,
  `card_fiber_p_mul`, `card_locV_eq`, `card_locV_locR` (the number of `x` with exponent `j` and
  residue with property `P` is `p^(k-1-j)` times the number of such non-zero residues).
* `ArithChar.lean` (complete): `IsLogChar p t χ`, `exists_isLogChar`, `IsLogChar.card_fiber`
  (`2^t * #{a ≠ 0 : χ a = c} = p - 1`).
* `ArithDefs.lean` (complete): `Idx`, `sExp`, `kExp`, `piVal`, `crt` (`ZMod.equivPi`), `uVec`,
  `zLoc`, `zPi`, `suppPi`, `clPi`, `oRat`, `gElt`; the statements `Lemma1Prop`, `MainEqProp`,
  `EllProp`; the numerical hypotheses of the abstract theorem (`sExp_pos`, `one_lt_piVal`,
  `piVal_dvd`, `uVec_self`), `kExp_eq`, `kExp_ne_zero`, `exists_chars`.
* `ArithSeries.lean` (complete): all the analysis. `sum_eq_zero_of_harmonic`: if
  `∑_{r : p r = r'} w(r) = p w(r')` for all primes `p ∣ q` and all `r'` divisible by `p`, then
  (a) gives `∑_r f(r) w(r) = 0`. (`serH`, `serH_insert`, `theta_insert`.)
* `ArithRing.lean` (complete): `coeff_normElt`, `single_mul_normElt`, `normElt_singleton`,
  `normElt_eq_prod`, `smul_eq_single_mul`, `single_zero_mul_cancel`, `aug_add`, `aug_single`,
  `aug_smul`, `aug_sum`, and `ℤ_(2)`: `isZ2_*`, `isZ2_inv_natCast`, `Even2` (`x ∈ 2 ℤ_(2)`),
  `even2_add/sub/sum/mul_left`, `even2_intCast_sub`, `even2_sub_one` (odd rational `≡ 1`).
* `ArithWeight.lean` (complete): Lemma 2. Route: not the paper's rearrangement, but the finite
  one. Weight `W(r) = ∏_p w_p(r_p)` in `ℚ[S]` (`wGlob`, `wLoc`); `sum_wGlob_fiber`
  (`∑_{r : p r = r'} W(r) = p W(r')`, from `sum_wLoc_fiber` and `wLoc_natCast_mul`);
  `wGlob_eq` (`W(r) = o(P - n) a_n N_{P - n} [cl(r)]`); `sum_wGlob`; `mainEq`.

## The plans for the last two statements (both carried out)

1. `Lemma1Prop`. Put `e = (1/2) • (g_n - ν N_n)`, `ν = ∏_{p ∈ n} k_p`. The coefficient of `σ` in
   `g_n` is `o(n)^(-1) ∑ f(r)` over `T = {r : n(r) = n, cl(r) = σ}`; `T` is empty unless
   `σ ∈ S_n` (`clPi y p = 0` when `y p = 0`). Needed: `#T ≡ ν` mod 2 for `σ ∈ S_n`. Count through
   `crt`: split the `y` by the tuple `j_p = locV (y p)` (`Finset.card_eq_sum_card_fiberwise`;
   `j_p < k_p` for `p ∈ n`, `j_p = k_p` otherwise: `ν` tuples); for a fixed tuple the set is a
   `Fintype.piFinset` of the sets `{x : locV x = j_p ∧ (p ∈ n → χ_p (locR x) = σ_p - ∑_{p'}
   j_{p'} • u_{p'} p)}` (`clPi y p = χ_p (locR (y p)) + ∑_{p'} locV (y p') • uVec p' p` for
   `y p ≠ 0`, since `uVec p p = 0`), of odd size `p^(k-1-j) (p-1)/2^s` by `card_locV_locR` and
   `IsLogChar.card_fiber` (odd because `¬ 2^(s+1) ∣ p - 1`), or `1` by `card_locV_eq`. Then
   `even2_sub_one`, `even2_sum`, and `o(n)` is an odd natural number (`isZ2_inv_natCast`).
2. `EllProp`. `aug (gElt n) = o(n)^(-1) ∑_{r : n(r) = n} f r` (`aug_smul`, `aug_sum`,
   `aug_single`); so the left side is the sum of `f r` over the `r ≠ 0` with `crt q r p₀ = 0`
   (`Finset.sum_fiberwise_of_maps_to`); these are the `(r : ZMod q)`, `r ∈ Icc 1 (q - 1)`,
   `p₀^k ∣ r` (`ZMod.prodEquivPi_apply`/`map_natCast`, `ZMod.natCast_eq_zero_iff`, `kExp_eq`).
3. Then `theoremA_of_abstract := theoremA_of_lemma1_ell lemma1 ell`, and the axiom check.
-/

@[expose] public section

namespace PiFormula

namespace Erdos

open Arith

/-- Theorem A from the abstract theorem and the three statements of `ArithDefs.lean`. -/
theorem theoremA_of_props (h1 : Lemma1Prop) (h2 : MainEqProp) (h3 : EllProp) :
    AbstractTheoremA → TheoremA := by
  intro hA q hq f hf0 hodd ha p hp hpq
  have : NeZero q := ⟨hq.pos.ne'⟩
  obtain ⟨χ, hχ⟩ := exists_chars q
  have hpm : p ∈ q.primeFactors := Nat.mem_primeFactors.2 ⟨hp, hpq, NeZero.ne q⟩
  obtain ⟨z, hz, e⟩ := hA (Idx q) (sExp q) (piVal q) (kExp q) (uVec q χ) (gElt q χ f)
    (sExp_pos hq) one_lt_piVal piVal_dvd (uVec_self q χ) (h1 q hq χ hχ f hodd)
    (h2 q hq χ hχ f hf0 ha) ⟨p, hpm⟩
  refine ⟨z, hz, ?_⟩
  rw [h3 q hq χ f ⟨p, hpm⟩, kExp_eq] at e
  rw [e]
  simp [piVal, sExp]

/-- Theorem A from the abstract theorem, Lemma 1 and step 3 (Lemma 2 is proved: `mainEq`). -/
theorem theoremA_of_lemma1_ell (h1 : Lemma1Prop) (h3 : EllProp) :
    AbstractTheoremA → TheoremA :=
  theoremA_of_props h1 mainEq h3

end Erdos

end PiFormula
