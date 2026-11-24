module

public import Pilean.PiFormula.Relations

/-!
# The space V: eight series with rational multiples of π (Part III, Theorem C)

Theorem C says that the rational patterns `ρ` (period 120) with
`∑ ρ(k) 2^(-⌊k/2⌋) / k ∈ ℚ π` form an 8-dimensional space `V`, spanned by eight named series
(decompose_formula.py):

* `ARG(O_1) = π/4`, `ARG(O_6) = 0`, `ARG(O_10) - ARG(O_2) = π/4`;
* `LOG(O_6) - 2 LOG(O_1) = 0`, `LOG(O_8a) - 2 LOG(O_1) = 0`, `LOG(O_10) - LOG(O_2) - 3 LOG(O_1) = 0`,
  `LOG(O_24) - LOG(O_8b) - 2 LOG(O_1) = 0`;
* the `√3`-twisted series `TW = √3 ∑_k -Im(t^(-k) (ζ^k - ζ^5k + ζ^13k - ζ^17k + ζ^4k - ζ^20k))/k`
  (`ζ = ζ_24`), with value 0.

This file proves the lower half of Theorem C: these eight patterns are rational, have period
120, have the stated values (`hasSum_namedA1` ... `hasSum_namedTW`), and are linearly
independent over ℚ (`named_linearIndependent`). The new formula is in their span
(`rhoNew_eq_named`). That `V` is no larger needs Baker's theorem (lean/PART3_PLAN.md).

The patterns are defined through `ℤ[i]` models of the power sums, as in `NewFormula.lean`:
`ρ = -Im(P(k) U_k)/2` or `-Re(P(k) U_k)/2`. For the twisted series the power sum, which
involves `√3 = ζ_24^2 - ζ_24^10` and single roots of order 24 and 6, is a Gaussian integer of
period 24, checked case by case modulo `Φ_24` (`psTW_eq`). Its value is 0 by the pairing
`g(i conj r) = -g(r)` and three explicit arguments, `π/6`, `-π/6`, `π/6`.
-/

@[expose] public section

open Polynomial Complex ComplexConjugate

namespace PiFormula

/-! ## 1. Patterns from `ℤ[i]` models -/

/-- The `k`-th term `ρ(k) 2^(-⌊k/2⌋) / k` of the series of a pattern. -/
noncomputable def seriesTerm (ρ : ℕ → ℚ) (k : ℕ) : ℝ := (ρ k : ℝ) / 2 ^ (k / 2) / k

/-- The arctangent-type pattern of a power-sum model `P`. -/
def rhoA (P : ℕ → GaussianInt) (k : ℕ) : ℚ := -((P k * UZ k).im : ℚ) / 2

/-- The logarithm-type pattern of a power-sum model `P`. -/
def rhoL (P : ℕ → GaussianInt) (k : ℕ) : ℚ := -((P k * UZ k).re : ℚ) / 2

theorem tau_eq_rhoA {S : Multiset ℂ} {P : ℕ → GaussianInt} (hP : ∀ k, psum S k = (P k : ℂ))
    (k : ℕ) : tau S k = seriesTerm (rhoA P) k := by
  rw [tau, hP, mul_tC_inv_pow_im, seriesTerm, rhoA]
  push_cast
  ring

theorem tauL_eq_rhoL {S : Multiset ℂ} {P : ℕ → GaussianInt} (hP : ∀ k, psum S k = (P k : ℂ))
    (k : ℕ) : tauL S k = seriesTerm (rhoL P) k := by
  rw [tauL, hP, mul_tC_inv_pow_re, seriesTerm, rhoL]
  push_cast
  ring

/-- The constant model `1` (the orbit `O_1 = {1}`). -/
def P1Z : ℕ → GaussianInt := fun _ => 1

/-! ## 2. The seven orbit series -/

def namedA1 : ℕ → ℚ := rhoA P1Z
def namedA6 : ℕ → ℚ := rhoA P6Z
def namedA10 : ℕ → ℚ := fun k => rhoA P10Z k - rhoA P2Z k
def namedL6 : ℕ → ℚ := fun k => rhoL P6Z k - 2 * rhoL P1Z k
def namedL8 : ℕ → ℚ := fun k => rhoL P8aZ k - 2 * rhoL P1Z k
def namedL10 : ℕ → ℚ := fun k => rhoL P10Z k - rhoL P2Z k - 3 * rhoL P1Z k
def namedL24 : ℕ → ℚ := fun k => rhoL P24Z k - rhoL P8bZ k - 2 * rhoL P1Z k

theorem hO1 : ∀ r ∈ O1, ‖r‖ = 1 := fun _ hr => norm_of_mem_orbit hr
theorem hO2 : ∀ r ∈ O2, ‖r‖ = 1 := fun _ hr => norm_of_mem_orbit hr
theorem hO6 : ∀ r ∈ O6, ‖r‖ = 1 := fun _ hr => norm_of_mem_orbit hr
theorem hO10 : ∀ r ∈ O10, ‖r‖ = 1 := fun _ hr => norm_of_mem_orbit hr

theorem psum_P1Z (k : ℕ) : psum O1 k = ((P1Z k : GaussianInt) : ℂ) := psum_O1Z k

theorem hasSum_namedA1 : HasSum (seriesTerm namedA1) (Real.pi / 4) := by
  have h := hasSum_gamma hO1
  rw [gamma_orbit_P0] at h
  convert h using 1
  funext k
  exact (tau_eq_rhoA psum_P1Z k).symm

theorem hasSum_namedA6 : HasSum (seriesTerm namedA6) 0 := by
  have h := hasSum_gamma hO6
  rw [gamma_orbit_Q1] at h
  convert h using 1
  funext k
  exact (tau_eq_rhoA psum_O6Z k).symm

theorem hasSum_namedA10 : HasSum (seriesTerm namedA10) (Real.pi / 4) := by
  have h := (hasSum_gamma hO10).sub (hasSum_gamma hO2)
  rw [gamma_orbit_Q2, gamma_orbit_Q0, show Real.arctan (1 / 2) - (Real.arctan (1 / 2) -
    Real.pi / 4) = Real.pi / 4 by ring] at h
  convert h using 1
  funext k
  simp only [tau_eq_rhoA psum_O10Z, tau_eq_rhoA psum_O2Z, seriesTerm, namedA10]
  push_cast
  ring

theorem hasSum_namedL6 : HasSum (seriesTerm namedL6) 0 := by
  have h := (hasSum_LOG hO6).sub ((hasSum_LOG hO1).mul_left 2)
  rw [LOG_relations.1] at h
  convert h using 1
  funext k
  simp only [tauL_eq_rhoL psum_O6Z, tauL_eq_rhoL psum_P1Z, seriesTerm, namedL6]
  push_cast
  ring

theorem hasSum_namedL8 : HasSum (seriesTerm namedL8) 0 := by
  have h := (hasSum_LOG (S := O8a) fun _ hr => norm_selfOrb hr).sub ((hasSum_LOG hO1).mul_left 2)
  rw [LOG_relations.2.1] at h
  convert h using 1
  funext k
  simp only [tauL_eq_rhoL psum_O8aZ, tauL_eq_rhoL psum_P1Z, seriesTerm, namedL8]
  push_cast
  ring

theorem norm_zO_orbit (a : Atom) : ‖zO (orbit a)‖ = ‖((atom a : GaussianInt) : ℂ)‖ := by
  have := congrArg norm (zO_orbit a)
  rwa [norm_mul, norm_pow, norm_eq_one_of_pow_four (kappa_pow_four a), one_pow, one_mul] at this

/-- `LOG(O_10) - LOG(O_2) - 3 LOG(O_1) = 0`: `|z(O_10)| = |z(O_2)| = |2 + i|`. -/
theorem LOG_relation_10 : LOG O10 - LOG O2 - 3 * LOG O1 = 0 := by
  have h1 := LOG_eq hO1
  have h2 := LOG_eq hO2
  have h10 := LOG_eq hO10
  have e : ‖zO O10‖ = ‖zO O2‖ := by rw [O10, O2, norm_zO_orbit, norm_zO_orbit, atom_Q2, atom_Q0]
  have c10 : Multiset.card O10 = 4 := by
    rw [O10, card_orbit, show mOf (.Q 2) = 5 from rfl, totient_five]; rfl
  have c2 : Multiset.card O2 = 1 := by rw [O2, card_orbit]; simp [mOf, Npow]
  rw [norm_zO_O1, card_O1, Real.log_one] at h1
  rw [c2] at h2
  rw [c10, e] at h10
  rw [h1, h2, h10]
  push_cast
  ring

theorem hasSum_namedL10 : HasSum (seriesTerm namedL10) 0 := by
  have h := ((hasSum_LOG hO10).sub (hasSum_LOG hO2)).sub ((hasSum_LOG hO1).mul_left 3)
  rw [LOG_relation_10] at h
  convert h using 1
  funext k
  simp only [tauL_eq_rhoL psum_O10Z, tauL_eq_rhoL psum_O2Z, tauL_eq_rhoL psum_P1Z,
    seriesTerm, namedL10]
  push_cast
  ring

theorem hasSum_namedL24 : HasSum (seriesTerm namedL24) 0 := by
  have h := ((hasSum_LOG (S := O24) fun _ hr => norm_selfOrb hr).sub
    (hasSum_LOG (S := O8b) fun _ hr => norm_selfOrb hr)).sub ((hasSum_LOG hO1).mul_left 2)
  rw [LOG_relations.2.2] at h
  convert h using 1
  funext k
  simp only [tauL_eq_rhoL psum_O24Z, tauL_eq_rhoL psum_O8bZ, tauL_eq_rhoL psum_P1Z,
    seriesTerm, namedL24]
  push_cast
  ring

/-! ## 3. The twisted series -/

theorem z24_pow_12 : z24 ^ 12 = -1 := by
  have h24 := z24_prim.pow_eq_one
  have hne : z24 ^ 12 ≠ 1 := z24_prim.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have : (z24 ^ 12 - 1) * (z24 ^ 12 + 1) = 0 := by linear_combination h24
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (sub_eq_zero.1 h) hne
  · linear_combination h

theorem z24_pow_mod (n : ℕ) : z24 ^ n = z24 ^ (n % 24) := by
  conv_lhs => rw [← Nat.div_add_mod n 24, pow_add, pow_mul, z24_prim.pow_eq_one, one_pow, one_mul]

/-- `√3`, written as `ζ_24^2 - ζ_24^10`. -/
noncomputable def dTW : ℂ := z24 ^ 2 - z24 ^ 10

/-- The power sum of the twisted series. -/
noncomputable def psTW (k : ℕ) : ℂ :=
  dTW * (z24 ^ k - (z24 ^ 5) ^ k + (z24 ^ 13) ^ k - (z24 ^ 17) ^ k + (z24 ^ 4) ^ k -
    (z24 ^ 20) ^ k)

/-- Its values, of period 24. -/
def twTable : List GaussianInt :=
  [⟨0, 0⟩, ⟨0, 3⟩, ⟨6, 3⟩, ⟨0, 0⟩, ⟨0, 3⟩, ⟨0, -3⟩, ⟨0, 0⟩, ⟨0, 3⟩, ⟨0, 9⟩, ⟨0, 0⟩, ⟨-6, -3⟩,
   ⟨0, -3⟩, ⟨0, 0⟩, ⟨0, 3⟩, ⟨-6, 3⟩, ⟨0, 0⟩, ⟨0, -9⟩, ⟨0, -3⟩, ⟨0, 0⟩, ⟨0, 3⟩, ⟨0, -3⟩, ⟨0, 0⟩,
   ⟨6, -3⟩, ⟨0, -3⟩]

def PTWZ (k : ℕ) : GaussianInt := twTable.getD (k % 24) 0

/-- `psTW k` with the exponents reduced mod 24. -/
theorem psTW_reduce (k : ℕ) : psTW k = dTW * (z24 ^ (k % 24) - z24 ^ (5 * (k % 24) % 24) +
    z24 ^ (13 * (k % 24) % 24) - z24 ^ (17 * (k % 24) % 24) + z24 ^ (4 * (k % 24) % 24) -
    z24 ^ (20 * (k % 24) % 24)) := by
  simp only [psTW, ← pow_mul]
  rw [z24_pow_mod k, z24_pow_mod (5 * k), z24_pow_mod (13 * k), z24_pow_mod (17 * k),
    z24_pow_mod (4 * k), z24_pow_mod (20 * k), Nat.mul_mod 5, Nat.mul_mod 13, Nat.mul_mod 17,
    Nat.mul_mod 4, Nat.mul_mod 20]

theorem psTW_small : ∀ r < 24, dTW * (z24 ^ r - z24 ^ (5 * r % 24) + z24 ^ (13 * r % 24) -
    z24 ^ (17 * r % 24) + z24 ^ (4 * r % 24) - z24 ^ (20 * r % 24)) =
    ((twTable.getD r 0 : GaussianInt) : ℂ) := by
  intro r hr
  interval_cases r
  · simp only [Nat.reduceMul, Nat.reduceMod]
    rw [show twTable.getD 0 0 = (⟨0, 0⟩ : GaussianInt) from rfl, GaussianInt.toComplex_def',
      I_z24, dTW]
    push_cast
    linear_combination (0) * cyc24
  · simp only [Nat.reduceMul, Nat.reduceMod]
    rw [show twTable.getD 1 0 = (⟨0, 3⟩ : GaussianInt) from rfl, GaussianInt.toComplex_def',
      I_z24, dTW]
    push_cast
    linear_combination (z24 ^ 22 + z24 ^ 19 + z24 ^ 18 - z24 ^ 14 - 2 * z24 ^ 11 - 2 * z24 ^ 10 - 2 * z24 ^ 6 + z24 ^ 3) * cyc24
  · simp only [Nat.reduceMul, Nat.reduceMod]
    rw [show twTable.getD 2 0 = (⟨6, 3⟩ : GaussianInt) from rfl, GaussianInt.toComplex_def',
      I_z24, dTW]
    push_cast
    linear_combination (z24 ^ 18 + z24 ^ 14 + 2 * z24 ^ 12 - 2 * z24 ^ 10 + 2 * z24 ^ 8 - 3 * z24 ^ 6 - 4 * z24 ^ 4 - 6) * cyc24
  · simp only [Nat.reduceMul, Nat.reduceMod]
    rw [show twTable.getD 3 0 = (⟨0, 0⟩ : GaussianInt) from rfl, GaussianInt.toComplex_def',
      I_z24, dTW]
    push_cast
    linear_combination (0) * cyc24
  · simp only [Nat.reduceMul, Nat.reduceMod]
    rw [show twTable.getD 4 0 = (⟨0, 3⟩ : GaussianInt) from rfl, GaussianInt.toComplex_def',
      I_z24, dTW]
    push_cast
    linear_combination (2 * z24 ^ 22 + z24 ^ 18 - 3 * z24 ^ 14 - 2 * z24 ^ 10 - z24 ^ 6) * cyc24
  · simp only [Nat.reduceMul, Nat.reduceMod]
    rw [show twTable.getD 5 0 = (⟨0, -3⟩ : GaussianInt) from rfl, GaussianInt.toComplex_def',
      I_z24, dTW]
    push_cast
    linear_combination (-z24 ^ 22 - z24 ^ 19 - z24 ^ 18 + z24 ^ 14 + 2 * z24 ^ 11 + 2 * z24 ^ 10 + 2 * z24 ^ 6 - z24 ^ 3) * cyc24
  · simp only [Nat.reduceMul, Nat.reduceMod]
    rw [show twTable.getD 6 0 = (⟨0, 0⟩ : GaussianInt) from rfl, GaussianInt.toComplex_def',
      I_z24, dTW]
    push_cast
    linear_combination (0) * cyc24
  · simp only [Nat.reduceMul, Nat.reduceMod]
    rw [show twTable.getD 7 0 = (⟨0, 3⟩ : GaussianInt) from rfl, GaussianInt.toComplex_def',
      I_z24, dTW]
    push_cast
    linear_combination (z24 ^ 25 + z24 ^ 22 + z24 ^ 18 - 2 * z24 ^ 17 - z24 ^ 14 - 2 * z24 ^ 10 + z24 ^ 9 - 2 * z24 ^ 6) * cyc24
  · simp only [Nat.reduceMul, Nat.reduceMod]
    rw [show twTable.getD 8 0 = (⟨0, 9⟩ : GaussianInt) from rfl, GaussianInt.toComplex_def',
      I_z24, dTW]
    push_cast
    linear_combination (3 * z24 ^ 18 + 3 * z24 ^ 14 - 6 * z24 ^ 10 - 9 * z24 ^ 6) * cyc24
  · simp only [Nat.reduceMul, Nat.reduceMod]
    rw [show twTable.getD 9 0 = (⟨0, 0⟩ : GaussianInt) from rfl, GaussianInt.toComplex_def',
      I_z24, dTW]
    push_cast
    linear_combination (0) * cyc24
  · simp only [Nat.reduceMul, Nat.reduceMod]
    rw [show twTable.getD 10 0 = (⟨-6, -3⟩ : GaussianInt) from rfl, GaussianInt.toComplex_def',
      I_z24, dTW]
    push_cast
    linear_combination (-z24 ^ 18 - z24 ^ 14 - 2 * z24 ^ 12 + 2 * z24 ^ 10 - 2 * z24 ^ 8 + 3 * z24 ^ 6 + 4 * z24 ^ 4 + 6) * cyc24
  · simp only [Nat.reduceMul, Nat.reduceMod]
    rw [show twTable.getD 11 0 = (⟨0, -3⟩ : GaussianInt) from rfl, GaussianInt.toComplex_def',
      I_z24, dTW]
    push_cast
    linear_combination (-z24 ^ 25 - z24 ^ 22 - z24 ^ 18 + 2 * z24 ^ 17 + z24 ^ 14 + 2 * z24 ^ 10 - z24 ^ 9 + 2 * z24 ^ 6) * cyc24
  · simp only [Nat.reduceMul, Nat.reduceMod]
    rw [show twTable.getD 12 0 = (⟨0, 0⟩ : GaussianInt) from rfl, GaussianInt.toComplex_def',
      I_z24, dTW]
    push_cast
    linear_combination (0) * cyc24
  · simp only [Nat.reduceMul, Nat.reduceMod]
    rw [show twTable.getD 13 0 = (⟨0, 3⟩ : GaussianInt) from rfl, GaussianInt.toComplex_def',
      I_z24, dTW]
    push_cast
    linear_combination (z24 ^ 22 + z24 ^ 19 + z24 ^ 18 - z24 ^ 14 - 2 * z24 ^ 11 - 2 * z24 ^ 10 - 2 * z24 ^ 6 + z24 ^ 3) * cyc24
  · simp only [Nat.reduceMul, Nat.reduceMod]
    rw [show twTable.getD 14 0 = (⟨-6, 3⟩ : GaussianInt) from rfl, GaussianInt.toComplex_def',
      I_z24, dTW]
    push_cast
    linear_combination (2 * z24 ^ 24 + 2 * z24 ^ 20 + z24 ^ 18 - 4 * z24 ^ 16 + z24 ^ 14 - 6 * z24 ^ 12 - 2 * z24 ^ 10 - 3 * z24 ^ 6 + 6 * z24 ^ 4 + 6) * cyc24
  · simp only [Nat.reduceMul, Nat.reduceMod]
    rw [show twTable.getD 15 0 = (⟨0, 0⟩ : GaussianInt) from rfl, GaussianInt.toComplex_def',
      I_z24, dTW]
    push_cast
    linear_combination (0) * cyc24
  · simp only [Nat.reduceMul, Nat.reduceMod]
    rw [show twTable.getD 16 0 = (⟨0, -9⟩ : GaussianInt) from rfl, GaussianInt.toComplex_def',
      I_z24, dTW]
    push_cast
    linear_combination (-3 * z24 ^ 18 - 3 * z24 ^ 14 + 6 * z24 ^ 10 + 9 * z24 ^ 6) * cyc24
  · simp only [Nat.reduceMul, Nat.reduceMod]
    rw [show twTable.getD 17 0 = (⟨0, -3⟩ : GaussianInt) from rfl, GaussianInt.toComplex_def',
      I_z24, dTW]
    push_cast
    linear_combination (-z24 ^ 22 - z24 ^ 19 - z24 ^ 18 + z24 ^ 14 + 2 * z24 ^ 11 + 2 * z24 ^ 10 + 2 * z24 ^ 6 - z24 ^ 3) * cyc24
  · simp only [Nat.reduceMul, Nat.reduceMod]
    rw [show twTable.getD 18 0 = (⟨0, 0⟩ : GaussianInt) from rfl, GaussianInt.toComplex_def',
      I_z24, dTW]
    push_cast
    linear_combination (0) * cyc24
  · simp only [Nat.reduceMul, Nat.reduceMod]
    rw [show twTable.getD 19 0 = (⟨0, 3⟩ : GaussianInt) from rfl, GaussianInt.toComplex_def',
      I_z24, dTW]
    push_cast
    linear_combination (z24 ^ 25 + z24 ^ 22 + z24 ^ 18 - 2 * z24 ^ 17 - z24 ^ 14 - 2 * z24 ^ 10 + z24 ^ 9 - 2 * z24 ^ 6) * cyc24
  · simp only [Nat.reduceMul, Nat.reduceMod]
    rw [show twTable.getD 20 0 = (⟨0, -3⟩ : GaussianInt) from rfl, GaussianInt.toComplex_def',
      I_z24, dTW]
    push_cast
    linear_combination (-2 * z24 ^ 22 - z24 ^ 18 + 3 * z24 ^ 14 + 2 * z24 ^ 10 + z24 ^ 6) * cyc24
  · simp only [Nat.reduceMul, Nat.reduceMod]
    rw [show twTable.getD 21 0 = (⟨0, 0⟩ : GaussianInt) from rfl, GaussianInt.toComplex_def',
      I_z24, dTW]
    push_cast
    linear_combination (0) * cyc24
  · simp only [Nat.reduceMul, Nat.reduceMod]
    rw [show twTable.getD 22 0 = (⟨6, -3⟩ : GaussianInt) from rfl, GaussianInt.toComplex_def',
      I_z24, dTW]
    push_cast
    linear_combination (-2 * z24 ^ 24 - 2 * z24 ^ 20 - z24 ^ 18 + 4 * z24 ^ 16 - z24 ^ 14 + 6 * z24 ^ 12 + 2 * z24 ^ 10 + 3 * z24 ^ 6 - 6 * z24 ^ 4 - 6) * cyc24
  · simp only [Nat.reduceMul, Nat.reduceMod]
    rw [show twTable.getD 23 0 = (⟨0, -3⟩ : GaussianInt) from rfl, GaussianInt.toComplex_def',
      I_z24, dTW]
    push_cast
    linear_combination (-z24 ^ 25 - z24 ^ 22 - z24 ^ 18 + 2 * z24 ^ 17 + z24 ^ 14 + 2 * z24 ^ 10 - z24 ^ 9 + 2 * z24 ^ 6) * cyc24

theorem psTW_eq (k : ℕ) : psTW k = ((PTWZ k : GaussianInt) : ℂ) := by
  rw [psTW_reduce, PTWZ]
  exact psTW_small (k % 24) (Nat.mod_lt _ (by norm_num))

/-- The twisted pattern. -/
def namedTW : ℕ → ℚ := rhoA PTWZ

/-! ### Explicit values -/

theorem sqrt3_sq : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
  push_cast
  rfl

theorem z24_sq_trig : z24 ^ 2 =
    Complex.cos ((Real.pi / 6 : ℝ) : ℂ) + Complex.sin ((Real.pi / 6 : ℝ) : ℂ) * I := by
  rw [z24, ← pow_mul, ζ120, ← Complex.exp_nat_mul,
    show ((5 * 2 : ℕ) : ℂ) * (2 * Real.pi * I / 120) = ((Real.pi / 6 : ℝ) : ℂ) * I by
      push_cast; ring, Complex.exp_mul_I]

theorem z24_sq : z24 ^ 2 = ((Real.sqrt 3 : ℝ) : ℂ) / 2 + I / 2 := by
  rw [z24_sq_trig, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_six,
    Real.sin_pi_div_six]
  push_cast
  ring

theorem z24_ne_zero : z24 ≠ 0 := z24_prim.ne_zero (by norm_num)

theorem z24_pow_10 : z24 ^ 10 = -((Real.sqrt 3 : ℝ) : ℂ) / 2 + I / 2 := by
  have h : z24 ^ 10 * z24 ^ 2 = -1 := by rw [← pow_add]; exact z24_pow_12
  have hc : (-((Real.sqrt 3 : ℝ) : ℂ) / 2 + I / 2) * z24 ^ 2 = -1 := by
    rw [z24_sq]; linear_combination (-1 / 4 : ℂ) * sqrt3_sq + (1 / 4 : ℂ) * Complex.I_sq
  exact mul_right_cancel₀ (pow_ne_zero 2 z24_ne_zero) (h.trans hc.symm)

/-- `ζ_24^2 - ζ_24^10 = √3`. -/
theorem dTW_eq : dTW = ((Real.sqrt 3 : ℝ) : ℂ) := by
  rw [dTW, z24_sq, z24_pow_10]
  ring

theorem z24_pow_4 : z24 ^ 4 = 1 / 2 + ((Real.sqrt 3 : ℝ) : ℂ) / 2 * I := by
  rw [show z24 ^ 4 = (z24 ^ 2) ^ 2 by ring, z24_sq]
  linear_combination (1 / 4 : ℂ) * sqrt3_sq + (1 / 4 : ℂ) * Complex.I_sq

theorem z24_pow_20 : z24 ^ 20 = 1 / 2 - ((Real.sqrt 3 : ℝ) : ℂ) / 2 * I := by
  rw [show z24 ^ 20 = (z24 ^ 10) ^ 2 by ring, z24_pow_10]
  linear_combination (1 / 4 : ℂ) * sqrt3_sq + (1 / 4 : ℂ) * Complex.I_sq

theorem z24_pow_13 : z24 ^ 13 = -z24 := by rw [pow_succ, z24_pow_12]; ring

theorem norm_z24_pow (n : ℕ) : ‖z24 ^ n‖ = 1 := by
  rw [norm_pow, z24_prim.norm'_eq_one (by norm_num), one_pow]

theorem conj_z24 : conj z24 = z24 ^ 23 := by
  have h1 : z24 * conj z24 = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, z24_prim.norm'_eq_one (by norm_num)]
    norm_num
  have h2 : z24 * z24 ^ 23 = 1 := by rw [← pow_succ']; exact z24_prim.pow_eq_one
  exact mul_left_cancel₀ z24_ne_zero (h1.trans h2.symm)

theorem gfun_z24_5 : gfun (z24 ^ 5) = -gfun z24 := by
  have e : I * conj z24 = z24 ^ 5 := by
    rw [conj_z24, I_z24, ← pow_add, z24_pow_mod]
  rw [← e]
  exact gfun_partner (by simpa using norm_z24_pow 1)

theorem gfun_z24_17 : gfun (z24 ^ 17) = -gfun (z24 ^ 13) := by
  have e : I * conj (z24 ^ 13) = z24 ^ 17 := by
    rw [map_pow, conj_z24, I_z24, ← pow_mul, ← pow_add, z24_pow_mod]
  rw [← e]
  exact gfun_partner (norm_z24_pow 13)

theorem inv_two_I : (2 * I)⁻¹ = -I / 2 := by
  refine inv_eq_of_mul_eq_one_right ?_
  linear_combination (-1 : ℂ) * Complex.I_sq

theorem arg_real_mul_trig {c θ : ℝ} (hc : 0 < c) (hθ : θ ∈ Set.Ioc (-Real.pi) Real.pi) :
    arg ((c : ℂ) * (Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * I)) = θ := by
  rw [Complex.arg_real_mul _ hc, Complex.arg_cos_add_sin_mul_I hθ]

theorem pi_div_six_mem : Real.pi / 6 ∈ Set.Ioc (-Real.pi) Real.pi := by
  have := Real.pi_pos
  constructor <;> linarith

theorem neg_pi_div_six_mem : -(Real.pi / 6) ∈ Set.Ioc (-Real.pi) Real.pi := by
  have := Real.pi_pos
  constructor <;> linarith

theorem sqrt3_gt_one : 1 < Real.sqrt 3 := by
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

theorem trig_pi_div_six :
    Complex.cos ((Real.pi / 6 : ℝ) : ℂ) + Complex.sin ((Real.pi / 6 : ℝ) : ℂ) * I =
      ((Real.sqrt 3 : ℝ) : ℂ) / 2 + I / 2 := by
  rw [← z24_sq_trig, z24_sq]

theorem trig_neg_pi_div_six :
    Complex.cos ((-(Real.pi / 6) : ℝ) : ℂ) + Complex.sin ((-(Real.pi / 6) : ℝ) : ℂ) * I =
      ((Real.sqrt 3 : ℝ) : ℂ) / 2 - I / 2 := by
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
    Real.cos_pi_div_six, Real.sin_pi_div_six]
  push_cast
  ring

/-- `g(ζ) + g(ζ^13) = π/6`: `w(ζ) w(-ζ) = 1 - ζ²/t² = (√3/2) ζ²`. -/
theorem gfun_z24_add_13 : gfun z24 + gfun (z24 ^ 13) = Real.pi / 6 := by
  have h1 := abs_gfun_le (by simpa using norm_z24_pow 1 : ‖z24‖ = 1)
  have h13 := abs_gfun_le (norm_z24_pow 13)
  simp only [gfun_eq_arg] at h1 h13 ⊢
  have hw1 : 1 - z24 / tC ≠ 0 := by
    rw [show 1 - z24 / tC = (tC - z24) / tC by rw [sub_div, div_self tC_ne_zero]]
    exact div_ne_zero (tC_sub_ne_zero (by simpa using norm_z24_pow 1)) tC_ne_zero
  have hw13 : 1 - z24 ^ 13 / tC ≠ 0 := by
    rw [show 1 - z24 ^ 13 / tC = (tC - z24 ^ 13) / tC by rw [sub_div, div_self tC_ne_zero]]
    exact div_ne_zero (tC_sub_ne_zero (norm_z24_pow 13)) tC_ne_zero
  have hmem : arg (1 - z24 / tC) + arg (1 - z24 ^ 13 / tC) ∈ Set.Ioc (-Real.pi) Real.pi := by
    have := Real.pi_pos
    rw [abs_le] at h1 h13
    constructor <;> linarith [h1.1, h1.2, h13.1, h13.2]
  rw [← Complex.arg_mul hw1 hw13 hmem]
  have e : (1 - z24 / tC) * (1 - z24 ^ 13 / tC) =
      ((Real.sqrt 3 / 2 : ℝ) : ℂ) * (Complex.cos ((Real.pi / 6 : ℝ) : ℂ) +
        Complex.sin ((Real.pi / 6 : ℝ) : ℂ) * I) := by
    rw [trig_pi_div_six, z24_pow_13]
    have : (1 - z24 / tC) * (1 - -z24 / tC) = 1 - z24 ^ 2 * (tC ^ 2)⁻¹ := by
      field_simp [tC_ne_zero]
      ring
    rw [this, tC_sq, inv_two_I, z24_sq]
    push_cast
    linear_combination (1 / 4 : ℂ) * Complex.I_sq - (1 / 4 : ℂ) * sqrt3_sq
  rw [e, arg_real_mul_trig (by positivity) pi_div_six_mem]

/-- `g(ζ^4) = -π/6`: `w(ζ_6) = ((√3 - 1)/2) e^(-iπ/6)`. -/
theorem gfun_z24_4 : gfun (z24 ^ 4) = -(Real.pi / 6) := by
  rw [gfun_eq_arg]
  have e : 1 - z24 ^ 4 / tC = (((Real.sqrt 3 - 1) / 2 : ℝ) : ℂ) *
      (Complex.cos ((-(Real.pi / 6) : ℝ) : ℂ) + Complex.sin ((-(Real.pi / 6) : ℝ) : ℂ) * I) := by
    rw [trig_neg_pi_div_six, div_eq_mul_inv, tC_inv, z24_pow_4]
    push_cast
    linear_combination (-1 / 4 : ℂ) * sqrt3_sq + (((Real.sqrt 3 : ℝ) : ℂ) / 4) * Complex.I_sq
  rw [e, arg_real_mul_trig (by linarith [sqrt3_gt_one]) neg_pi_div_six_mem]

/-- `g(ζ^20) = π/6`: `w(ζ_6^5) = ((1 + √3)/2) e^(iπ/6)`. -/
theorem gfun_z24_20 : gfun (z24 ^ 20) = Real.pi / 6 := by
  rw [gfun_eq_arg]
  have e : 1 - z24 ^ 20 / tC = (((1 + Real.sqrt 3) / 2 : ℝ) : ℂ) *
      (Complex.cos ((Real.pi / 6 : ℝ) : ℂ) + Complex.sin ((Real.pi / 6 : ℝ) : ℂ) * I) := by
    rw [trig_pi_div_six, div_eq_mul_inv, tC_inv, z24_pow_20]
    push_cast
    linear_combination (-1 / 4 : ℂ) * sqrt3_sq - (((Real.sqrt 3 : ℝ) : ℂ) / 4) * Complex.I_sq
  rw [e, arg_real_mul_trig (by positivity) pi_div_six_mem]

/-- The bracket of the twisted series vanishes. -/
theorem tw_bracket : gfun z24 - gfun (z24 ^ 5) + gfun (z24 ^ 13) - gfun (z24 ^ 17) +
    gfun (z24 ^ 4) - gfun (z24 ^ 20) = 0 := by
  rw [gfun_z24_5, gfun_z24_17, gfun_z24_4, gfun_z24_20]
  linarith [gfun_z24_add_13]

/-- **The twisted series**: its pattern is rational, and its value is 0. -/
theorem hasSum_namedTW : HasSum (seriesTerm namedTW) 0 := by
  have hz1 : ‖z24‖ = 1 := by simpa using norm_z24_pow 1
  have h := ((((((hasSum_gfun hz1).sub (hasSum_gfun (norm_z24_pow 5))).add
    (hasSum_gfun (norm_z24_pow 13))).sub (hasSum_gfun (norm_z24_pow 17))).add
    (hasSum_gfun (norm_z24_pow 4))).sub (hasSum_gfun (norm_z24_pow 20))).mul_left
    (Real.sqrt 3)
  rw [tw_bracket, mul_zero] at h
  convert h using 1
  funext k
  have e : seriesTerm namedTW k = -((psTW k * tC⁻¹ ^ k).im / k) := by
    rw [psTW_eq, mul_tC_inv_pow_im, seriesTerm, namedTW, rhoA]
    push_cast
    ring
  rw [e, psTW, dTW_eq, mul_assoc, Complex.im_ofReal_mul]
  simp only [sub_mul, add_mul, Complex.sub_im, Complex.add_im]
  ring

/-! ## 4. Period 120 -/

theorem UZ_add_120 (k : ℕ) : UZ (k + 120) = UZ k := by
  have h2 : 2 ∣ k + 120 ↔ 2 ∣ k := by omega
  have e2 : (k + 120) / 2 = k / 2 + 4 * 15 := by omega
  simp only [UZ, h2, e2, pow_add_four_mul negI_pow_four]

theorem rhoA_add_120 {P : ℕ → GaussianInt} (hP : ∀ k, P (k + 120) = P k) (k : ℕ) :
    rhoA P (k + 120) = rhoA P k := by simp only [rhoA, hP, UZ_add_120]

theorem rhoL_add_120 {P : ℕ → GaussianInt} (hP : ∀ k, P (k + 120) = P k) (k : ℕ) :
    rhoL P (k + 120) = rhoL P k := by simp only [rhoL, hP, UZ_add_120]

theorem models_add_120 (k : ℕ) :
    P1Z (k + 120) = P1Z k ∧ P2Z (k + 120) = P2Z k ∧ P6Z (k + 120) = P6Z k ∧
      P10Z (k + 120) = P10Z k ∧ P8aZ (k + 120) = P8aZ k ∧ P8bZ (k + 120) = P8bZ k ∧
      P24Z (k + 120) = P24Z k ∧ PTWZ (k + 120) = PTWZ k := by
  have h2 : 2 ∣ k + 120 ↔ 2 ∣ k := by omega
  have h3 : 3 ∣ k + 120 ↔ 3 ∣ k := by omega
  have h5 : 5 ∣ k + 120 ↔ 5 ∣ k := by omega
  have h6 : 6 ∣ k + 120 ↔ 6 ∣ k := by omega
  have h10 : 10 ∣ k + 120 ↔ 10 ∣ k := by omega
  have e2 : (k + 120) / 2 = k / 2 + 4 * 15 := by omega
  have e6 : (k + 120) / 6 = k / 6 + 4 * 5 := by omega
  have e24 : (k + 120) % 24 = k % 24 := by omega
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [P2Z, P6Z, P10Z, P8aZ, P8bZ, P24Z, PTWZ, h2, h3, h5, h6, h10, e2, e6, e24,
      pow_add_four_mul gI_pow_four, pow_add_four_mul negI_pow_four]

/-- The eight patterns have period 120. -/
theorem named_periodic (k : ℕ) :
    namedA1 (k + 120) = namedA1 k ∧ namedA6 (k + 120) = namedA6 k ∧
      namedA10 (k + 120) = namedA10 k ∧ namedL6 (k + 120) = namedL6 k ∧
      namedL8 (k + 120) = namedL8 k ∧ namedL10 (k + 120) = namedL10 k ∧
      namedL24 (k + 120) = namedL24 k ∧ namedTW (k + 120) = namedTW k := by
  have hm := fun k => models_add_120 k
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [namedA1, namedA6, namedA10, namedL6, namedL8, namedL10, namedL24, namedTW,
      rhoA_add_120 (fun k => (hm k).1), rhoA_add_120 (fun k => (hm k).2.1),
      rhoA_add_120 (fun k => (hm k).2.2.1), rhoA_add_120 (fun k => (hm k).2.2.2.1),
      rhoA_add_120 (fun k => (hm k).2.2.2.2.2.2.2),
      rhoL_add_120 (fun k => (hm k).1), rhoL_add_120 (fun k => (hm k).2.1),
      rhoL_add_120 (fun k => (hm k).2.2.1), rhoL_add_120 (fun k => (hm k).2.2.2.1),
      rhoL_add_120 (fun k => (hm k).2.2.2.2.1), rhoL_add_120 (fun k => (hm k).2.2.2.2.2.1),
      rhoL_add_120 (fun k => (hm k).2.2.2.2.2.2.1)]

/-! ## 5. Linear independence -/

theorem namedA1_at_1 : namedA1 1 = (1 / 2 : ℚ) := by decide +kernel
theorem namedA6_at_1 : namedA6 1 = (1 / 2 : ℚ) := by decide +kernel
theorem namedA10_at_1 : namedA10 1 = (1 : ℚ) := by decide +kernel
theorem namedL6_at_1 : namedL6 1 = (1 / 2 : ℚ) := by decide +kernel
theorem namedL8_at_1 : namedL8 1 = (1 : ℚ) := by decide +kernel
theorem namedL10_at_1 : namedL10 1 = (1 / 2 : ℚ) := by decide +kernel
theorem namedL24_at_1 : namedL24 1 = (1 : ℚ) := by decide +kernel
theorem namedTW_at_1 : namedTW 1 = (-3 / 2 : ℚ) := by decide +kernel
theorem namedA1_at_2 : namedA1 2 = (1 : ℚ) := by decide +kernel
theorem namedA6_at_2 : namedA6 2 = (-1 : ℚ) := by decide +kernel
theorem namedA10_at_2 : namedA10 2 = (-2 : ℚ) := by decide +kernel
theorem namedL6_at_2 : namedL6 2 = (0 : ℚ) := by decide +kernel
theorem namedL8_at_2 : namedL8 2 = (-2 : ℚ) := by decide +kernel
theorem namedL10_at_2 : namedL10 2 = (0 : ℚ) := by decide +kernel
theorem namedL24_at_2 : namedL24 2 = (-4 : ℚ) := by decide +kernel
theorem namedTW_at_2 : namedTW 2 = (6 : ℚ) := by decide +kernel
theorem namedA1_at_3 : namedA1 3 = (1 / 2 : ℚ) := by decide +kernel
theorem namedA6_at_3 : namedA6 3 = (-1 : ℚ) := by decide +kernel
theorem namedA10_at_3 : namedA10 3 = (1 : ℚ) := by decide +kernel
theorem namedL6_at_3 : namedL6 3 = (-2 : ℚ) := by decide +kernel
theorem namedL8_at_3 : namedL8 3 = (-1 : ℚ) := by decide +kernel
theorem namedL10_at_3 : namedL10 3 = (-1 / 2 : ℚ) := by decide +kernel
theorem namedL24_at_3 : namedL24 3 = (-1 : ℚ) := by decide +kernel
theorem namedTW_at_3 : namedTW 3 = (0 : ℚ) := by decide +kernel
theorem namedA1_at_4 : namedA1 4 = (0 : ℚ) := by decide +kernel
theorem namedA6_at_4 : namedA6 4 = (0 : ℚ) := by decide +kernel
theorem namedA10_at_4 : namedA10 4 = (0 : ℚ) := by decide +kernel
theorem namedL6_at_4 : namedL6 4 = (-3 : ℚ) := by decide +kernel
theorem namedL8_at_4 : namedL8 4 = (-4 : ℚ) := by decide +kernel
theorem namedL10_at_4 : namedL10 4 = (-5 : ℚ) := by decide +kernel
theorem namedL24_at_4 : namedL24 4 = (2 : ℚ) := by decide +kernel
theorem namedTW_at_4 : namedTW 4 = (3 : ℚ) := by decide +kernel
theorem namedA1_at_5 : namedA1 5 = (-1 / 2 : ℚ) := by decide +kernel
theorem namedA6_at_5 : namedA6 5 = (-1 / 2 : ℚ) := by decide +kernel
theorem namedA10_at_5 : namedA10 5 = (3 / 2 : ℚ) := by decide +kernel
theorem namedL6_at_5 : namedL6 5 = (-1 / 2 : ℚ) := by decide +kernel
theorem namedL8_at_5 : namedL8 5 = (-1 : ℚ) := by decide +kernel
theorem namedL10_at_5 : namedL10 5 = (-3 : ℚ) := by decide +kernel
theorem namedL24_at_5 : namedL24 5 = (-1 : ℚ) := by decide +kernel
theorem namedTW_at_5 : namedTW 5 = (-3 / 2 : ℚ) := by decide +kernel
theorem namedA1_at_6 : namedA1 6 = (-1 : ℚ) := by decide +kernel
theorem namedA6_at_6 : namedA6 6 = (-2 : ℚ) := by decide +kernel
theorem namedA10_at_6 : namedA10 6 = (2 : ℚ) := by decide +kernel
theorem namedL6_at_6 : namedL6 6 = (0 : ℚ) := by decide +kernel
theorem namedL8_at_6 : namedL8 6 = (-2 : ℚ) := by decide +kernel
theorem namedL10_at_6 : namedL10 6 = (0 : ℚ) := by decide +kernel
theorem namedL24_at_6 : namedL24 6 = (2 : ℚ) := by decide +kernel
theorem namedTW_at_6 : namedTW 6 = (0 : ℚ) := by decide +kernel
theorem namedA1_at_7 : namedA1 7 = (-1 / 2 : ℚ) := by decide +kernel
theorem namedA6_at_7 : namedA6 7 = (-1 / 2 : ℚ) := by decide +kernel
theorem namedA10_at_7 : namedA10 7 = (-1 : ℚ) := by decide +kernel
theorem namedL6_at_7 : namedL6 7 = (1 / 2 : ℚ) := by decide +kernel
theorem namedL8_at_7 : namedL8 7 = (1 : ℚ) := by decide +kernel
theorem namedL10_at_7 : namedL10 7 = (1 / 2 : ℚ) := by decide +kernel
theorem namedL24_at_7 : namedL24 7 = (1 : ℚ) := by decide +kernel
theorem namedTW_at_7 : namedTW 7 = (-3 / 2 : ℚ) := by decide +kernel
theorem namedA1_at_8 : namedA1 8 = (0 : ℚ) := by decide +kernel
theorem namedA6_at_8 : namedA6 8 = (0 : ℚ) := by decide +kernel
theorem namedA10_at_8 : namedA10 8 = (0 : ℚ) := by decide +kernel
theorem namedL6_at_8 : namedL6 8 = (3 : ℚ) := by decide +kernel
theorem namedL8_at_8 : namedL8 8 = (0 : ℚ) := by decide +kernel
theorem namedL10_at_8 : namedL10 8 = (5 : ℚ) := by decide +kernel
theorem namedL24_at_8 : namedL24 8 = (6 : ℚ) := by decide +kernel
theorem namedTW_at_8 : namedTW 8 = (-9 : ℚ) := by decide +kernel

/-- **The eight patterns are linearly independent over ℚ** (their values at `k = 1, ..., 8` form
an invertible matrix). -/
theorem named_linearIndependent :
    LinearIndependent ℚ ![namedA1, namedA6, namedA10, namedL6, namedL8, namedL10, namedL24,
      namedTW] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have e1 := congrFun hg 1
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_eight,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Pi.zero_apply, namedA1_at_1, namedA6_at_1, namedA10_at_1, namedL6_at_1, namedL8_at_1, namedL10_at_1, namedL24_at_1, namedTW_at_1] at e1
  have e2 := congrFun hg 2
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_eight,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Pi.zero_apply, namedA1_at_2, namedA6_at_2, namedA10_at_2, namedL6_at_2, namedL8_at_2, namedL10_at_2, namedL24_at_2, namedTW_at_2] at e2
  have e3 := congrFun hg 3
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_eight,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Pi.zero_apply, namedA1_at_3, namedA6_at_3, namedA10_at_3, namedL6_at_3, namedL8_at_3, namedL10_at_3, namedL24_at_3, namedTW_at_3] at e3
  have e4 := congrFun hg 4
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_eight,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Pi.zero_apply, namedA1_at_4, namedA6_at_4, namedA10_at_4, namedL6_at_4, namedL8_at_4, namedL10_at_4, namedL24_at_4, namedTW_at_4] at e4
  have e5 := congrFun hg 5
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_eight,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Pi.zero_apply, namedA1_at_5, namedA6_at_5, namedA10_at_5, namedL6_at_5, namedL8_at_5, namedL10_at_5, namedL24_at_5, namedTW_at_5] at e5
  have e6 := congrFun hg 6
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_eight,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Pi.zero_apply, namedA1_at_6, namedA6_at_6, namedA10_at_6, namedL6_at_6, namedL8_at_6, namedL10_at_6, namedL24_at_6, namedTW_at_6] at e6
  have e7 := congrFun hg 7
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_eight,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Pi.zero_apply, namedA1_at_7, namedA6_at_7, namedA10_at_7, namedL6_at_7, namedL8_at_7, namedL10_at_7, namedL24_at_7, namedTW_at_7] at e7
  have e8 := congrFun hg 8
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_eight,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Pi.zero_apply, namedA1_at_8, namedA6_at_8, namedA10_at_8, namedL6_at_8, namedL8_at_8, namedL10_at_8, namedL24_at_8, namedTW_at_8] at e8
  have g0 : g 0 = 0 := by
    linear_combination (1445 / 1312 : ℚ) * e1 + (1061 / 2624 : ℚ) * e2 + (143 / 656 : ℚ) * e3 + (405 / 2624 : ℚ) * e4 + (21 / 328 : ℚ) * e5 + (-89 / 656 : ℚ) * e6 + (55 / 164 : ℚ) * e7 + (93 / 1312 : ℚ) * e8
  have g1 : g 1 = 0 := by
    linear_combination (-621 / 1312 : ℚ) * e1 + (-653 / 2624 : ℚ) * e2 + (-135 / 656 : ℚ) * e3 + (3 / 2624 : ℚ) * e4 + (-29 / 328 : ℚ) * e5 + (-127 / 656 : ℚ) * e6 + (-115 / 164 : ℚ) * e7 + (59 / 1312 : ℚ) * e8
  have g2 : g 2 = 0 := by
    linear_combination (61 / 328 : ℚ) * e1 + (-51 / 656 : ℚ) * e2 + (-1 / 164 : ℚ) * e3 + (-51 / 656 : ℚ) * e4 + (1 / 82 : ℚ) * e5 + (27 / 164 : ℚ) * e6 + (-13 / 41 : ℚ) * e7 + (-19 / 328 : ℚ) * e8
  have g3 : g 3 = 0 := by
    linear_combination (475 / 1312 : ℚ) * e1 + (603 / 2624 : ℚ) * e2 + (-239 / 656 : ℚ) * e3 + (-53 / 2624 : ℚ) * e4 + (75 / 328 : ℚ) * e5 + (57 / 656 : ℚ) * e6 + (9 / 164 : ℚ) * e7 + (51 / 1312 : ℚ) * e8
  have g4 : g 4 = 0 := by
    linear_combination (63 / 164 : ℚ) * e1 + (-11 / 328 : ℚ) * e2 + (3 / 82 : ℚ) * e3 + (-11 / 328 : ℚ) * e4 + (-3 / 41 : ℚ) * e5 + (1 / 82 : ℚ) * e6 + (33 / 82 : ℚ) * e7 + (-25 / 164 : ℚ) * e8
  have g5 : g 5 = 0 := by
    linear_combination (-57 / 164 : ℚ) * e1 + (-33 / 328 : ℚ) * e2 + (9 / 82 : ℚ) * e3 + (-33 / 328 : ℚ) * e4 + (-9 / 41 : ℚ) * e5 + (3 / 82 : ℚ) * e6 + (-12 / 41 : ℚ) * e7 + (7 / 164 : ℚ) * e8
  have g6 : g 6 = 0 := by
    linear_combination (723 / 2624 : ℚ) * e1 + (-13 / 5248 : ℚ) * e2 + (-71 / 1312 : ℚ) * e3 + (643 / 5248 : ℚ) * e4 + (-93 / 656 : ℚ) * e5 + (113 / 1312 : ℚ) * e6 + (61 / 328 : ℚ) * e7 + (-37 / 2624 : ℚ) * e8
  have g7 : g 7 = 0 := by
    linear_combination (73 / 656 : ℚ) * e1 + (25 / 1312 : ℚ) * e2 + (-95 / 984 : ℚ) * e3 + (25 / 1312 : ℚ) * e4 + (-23 / 164 : ℚ) * e5 + (35 / 328 : ℚ) * e6 + (-5 / 246 : ℚ) * e7 + (-55 / 656 : ℚ) * e8
  intro i
  fin_cases i
  · exact g0
  · exact g1
  · exact g2
  · exact g3
  · exact g4
  · exact g5
  · exact g6
  · exact g7

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
