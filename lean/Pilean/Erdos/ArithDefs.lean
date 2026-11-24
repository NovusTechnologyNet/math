module

public import Pilean.Erdos.AbstractDefs
public import Pilean.Erdos.ArithLocal
public import Pilean.Erdos.ArithChar
public import Mathlib.Data.ZMod.QuotientRing

/-!
# Theorem A from the abstract theorem, part 3: the instance of the abstract setting

For odd `q` (paper: `02_proof_part_II.md`, section 1; the paper writes the groups
multiplicatively):

* `Idx q`: the primes dividing `q`; `sExp q p = v_2(p - 1)`, `kExp q p = v_p(q)`,
  `piVal q p = p`;
* `crt q`: the Chinese remainder isomorphism `ℤ/q ≃ ∏_p ℤ/p^(k_p)`; everything about
  `r ∈ ℤ/q` is defined through its components `crt q r p`;
* `χ p`: a surjective homomorphism `(ℤ/p)^× → ℤ/2^(s_p)` (`IsLogChar`);
* `uVec q χ p`: the element `u_p` of `S`, with component `-χ_{p'}(p)` at `p' ≠ p` and `0` at `p`;
* `suppPi y`: the set `n(r)` of the `p` with `v_p(r) < k_p`, that is, with non-zero component;
* `clPi q χ y`: the class `cl(r)` of `r / gcd(r, q)` in `S_{n(r)}`. Its component at `p ∈ n(r)`
  is `χ_p(r_p / p^(v_p(r))) - ∑_{p' ≠ p} min(v_{p'}(r), k_{p'}) χ_p(p')`;
* `oRat q n = o(n) = ∏_{p ∈ n} (p - 1)/2^(s_p)`;
* `gElt q χ f n = g_n = o(n)^(-1) ∑_{r : n(r) = n} f(r) [cl(r)]`.
-/

@[expose] public section

open scoped BigOperators

open AddMonoidAlgebra (single)

namespace PiFormula

namespace Erdos

namespace Arith

/-- The index set: the primes dividing `q`. -/
abbrev Idx (q : ℕ) : Type := {p : ℕ // p ∈ q.primeFactors}

instance idxFact (q : ℕ) (p : Idx q) : Fact (p.1.Prime) :=
  ⟨Nat.prime_of_mem_primeFactors p.2⟩

/-- `s_p = v_2(p - 1)`. -/
def sExp (q : ℕ) (p : Idx q) : ℕ := padicValNat 2 (p.1 - 1)

/-- `k_p = v_p(q)`. -/
abbrev kExp (q : ℕ) (p : Idx q) : ℕ := q.factorization p.1

/-- `π_p = p`. -/
def piVal (q : ℕ) (p : Idx q) : ℤ := (p.1 : ℤ)

/-- The ring `ℤ/p^(k_p)`. -/
abbrev LocRing (q : ℕ) (p : Idx q) : Type := ZMod (p.1 ^ q.factorization p.1)

/-- The Chinese remainder isomorphism `ℤ/q ≃ ∏_p ℤ/p^(k_p)`. -/
noncomputable def crt (q : ℕ) [NeZero q] : ZMod q ≃+* ∀ p : Idx q, LocRing q p :=
  ZMod.equivPi q (NeZero.ne q)

section Data

variable (q : ℕ) (χ : ∀ p : Idx q, ZMod p.1 → ZMod (2 ^ sExp q p))

/-- `u_p`: component `-χ_{p'}(p)` at `p' ≠ p`, and `0` at `p`. -/
def uVec (p : Idx q) : Grp (sExp q) := fun p' => if p' = p then 0 else -χ p' (p.1 : ZMod p'.1)

/-- The contribution of the component at `p` to the class: `v_p • u_p`, plus `χ_p` of the
residue at the place `p` if the component is not zero. -/
noncomputable def zLoc (p : Idx q) (x : LocRing q p) : Grp (sExp q) :=
  locV p.1 (kExp q p) x • uVec q χ p +
    if x = 0 then 0 else Pi.single p (χ p (locR p.1 (kExp q p) x))

/-- The sum of the contributions of all components. -/
noncomputable def zPi (y : ∀ p : Idx q, LocRing q p) : Grp (sExp q) := ∑ p, zLoc q χ p (y p)

/-- `n(r)`: the set of the `p` with non-zero component. -/
def suppPi (y : ∀ p : Idx q, LocRing q p) : Finset (Idx q) :=
  Finset.univ.filter (fun p => y p ≠ 0)

/-- `cl(r)`: `zPi` cut down to `S_{n(r)}`. -/
noncomputable def clPi (y : ∀ p : Idx q, LocRing q p) : Grp (sExp q) :=
  fun p => if y p = 0 then 0 else zPi q χ y p

/-- `o(n) = ∏_{p ∈ n} (p - 1)/2^(s_p)`. -/
def oRat (n : Finset (Idx q)) : ℚ := ∏ p ∈ n, ((piVal q p : ℚ) - 1) / 2 ^ sExp q p

variable [NeZero q]

/-- `g_n = o(n)^(-1) ∑_{r : n(r) = n} f(r) [cl(r)]`. -/
noncomputable def gElt (f : ZMod q → ℚ) (n : Finset (Idx q)) : GRing (sExp q) :=
  (oRat q n)⁻¹ • ∑ r ∈ Finset.univ.filter (fun r : ZMod q => suppPi q (crt q r) = n),
    single (clPi q χ (crt q r)) (f r)

end Data

/-! ### The statements of the three steps -/

/-- Lemma 1: `g_n = (∏_{p ∈ n} k_p) N_n + 2 e` with `e ∈ ℤ_(2)[S_n]`. -/
def Lemma1Prop : Prop :=
  ∀ (q : ℕ) [NeZero q], Odd q → ∀ χ : ∀ p : Idx q, ZMod p.1 → ZMod (2 ^ sExp q p),
    (∀ p, IsLogChar p.1 (sExp q p) (χ p)) → ∀ f : ZMod q → ℚ,
    (∀ r : ZMod q, r ≠ 0 → IsOddRat (f r)) → ∀ n : Finset (Idx q), n.Nonempty →
    ∃ e : GRing (sExp q), Integral2 e ∧ SuppIn n e ∧
      gElt q χ f n = ((∏ p ∈ n, kExp q p : ℕ) : ℚ) • normElt (sExp q) n + (2 : ℚ) • e

/-- Lemma 2: condition (a) gives the equation (M). -/
def MainEqProp : Prop :=
  ∀ (q : ℕ) [NeZero q], Odd q → ∀ χ : ∀ p : Idx q, ZMod p.1 → ZMod (2 ^ sExp q p),
    (∀ p, IsLogChar p.1 (sExp q p) (χ p)) → ∀ f : ZMod q → ℚ, f 0 = 0 → CondA q f →
    ∑ n ∈ (Finset.univ : Finset (Idx q)).powerset.filter Finset.Nonempty,
      aProd (piVal q) (uVec q χ) n * normElt (sExp q) nᶜ * gElt q χ f n = 0

/-- Step 3 of section 6: the sum in the conclusion of the abstract theorem is `ℓ_p`. -/
def EllProp : Prop :=
  ∀ (q : ℕ) [NeZero q], Odd q → ∀ χ : ∀ p : Idx q, ZMod p.1 → ZMod (2 ^ sExp q p),
    ∀ (f : ZMod q → ℚ) (p₀ : Idx q),
    ∑ n ∈ ((Finset.univ : Finset (Idx q)).erase p₀).powerset.filter Finset.Nonempty,
      (∏ p ∈ n, ((piVal q p : ℚ) - 1) / 2 ^ sExp q p) * aug (gElt q χ f n) = ell q f p₀.1

/-! ### The numerical hypotheses of the abstract theorem -/

theorem sExp_pos {q : ℕ} (hq : Odd q) (p : Idx q) : 1 ≤ sExp q p := by
  have hp : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
  have hpq : p.1 ∣ q := Nat.dvd_of_mem_primeFactors p.2
  have hodd : Odd p.1 := Odd.of_dvd_nat hq hpq
  have h2 : 2 ∣ p.1 - 1 := by
    obtain ⟨m, hm⟩ := hodd
    exact ⟨m, by omega⟩
  have hne : p.1 - 1 ≠ 0 := by
    have := hp.two_le
    omega
  rw [sExp, Nat.padicValNat_def]
  exact (Nat.pow_dvd_iff_le_multiplicity (by norm_num) hne).1 (by simpa using h2)

theorem one_lt_piVal {q : ℕ} (p : Idx q) : 1 < piVal q p := by
  have hp : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
  have := hp.one_lt
  unfold piVal
  exact_mod_cast this

theorem piVal_sub_one {q : ℕ} (p : Idx q) : piVal q p - 1 = ((p.1 - 1 : ℕ) : ℤ) := by
  have hp : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
  have := hp.one_lt
  unfold piVal
  omega

theorem two_pow_sExp_dvd {q : ℕ} (p : Idx q) : 2 ^ sExp q p ∣ p.1 - 1 := by
  rw [sExp, Nat.padicValNat_def]
  exact pow_multiplicity_dvd 2 (p.1 - 1)

theorem not_two_pow_sExp_succ_dvd {q : ℕ} (p : Idx q) : ¬ 2 ^ (sExp q p + 1) ∣ p.1 - 1 := by
  have hp : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
  have hne : p.1 - 1 ≠ 0 := by
    have := hp.two_le
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [sExp, Nat.padicValNat_def]
  exact pow_succ_multiplicity_not_dvd hne

theorem piVal_dvd {q : ℕ} (p : Idx q) :
    (2 : ℤ) ^ sExp q p ∣ piVal q p - 1 ∧ ¬ (2 : ℤ) ^ (sExp q p + 1) ∣ piVal q p - 1 := by
  rw [piVal_sub_one]
  constructor
  · exact_mod_cast Int.natCast_dvd_natCast.2 (two_pow_sExp_dvd p)
  · intro h
    apply not_two_pow_sExp_succ_dvd p
    exact_mod_cast h

theorem uVec_self (q : ℕ) (χ : ∀ p : Idx q, ZMod p.1 → ZMod (2 ^ sExp q p)) (p : Idx q) :
    uVec q χ p p = 0 := by
  simp [uVec]

theorem kExp_eq (q : ℕ) (p : Idx q) : kExp q p = padicValNat p.1 q := by
  rw [kExp, Nat.factorization_def q (Nat.prime_of_mem_primeFactors p.2), Nat.padicValNat_def]

theorem kExp_ne_zero {q : ℕ} (p : Idx q) : kExp q p ≠ 0 :=
  (Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors p.2)
    (Nat.mem_primeFactors.1 p.2).2.2 (Nat.dvd_of_mem_primeFactors p.2)).ne'

theorem exists_chars (q : ℕ) :
    ∃ χ : ∀ p : Idx q, ZMod p.1 → ZMod (2 ^ sExp q p), ∀ p, IsLogChar p.1 (sExp q p) (χ p) := by
  have h : ∀ p : Idx q, ∃ χ : ZMod p.1 → ZMod (2 ^ sExp q p), IsLogChar p.1 (sExp q p) χ :=
    fun p => exists_isLogChar p.1 (sExp q p) (two_pow_sExp_dvd p)
  exact ⟨fun p => (h p).choose, fun p => (h p).choose_spec⟩

end Arith

end Erdos

end PiFormula
