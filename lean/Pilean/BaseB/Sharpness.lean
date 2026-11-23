import Pilean.BaseB.NoPi

/-!
# Sharpness: every power of 2 has a degree-1 BBP-type formula for `π`

`NoPi` proves that a series `∑_{j ≥ 0} b^(-B j) ∑_{i=1}^{N} c_i / (N j + i)` with rational
`c_i` (Bailey's `P(1, b^B, N, c)`) is not a non-zero rational multiple of `π` when `b` is not a
power of 2. This file proves the converse, so the condition is exact.

* `bbp_formula`: the formula of Bailey, Borwein and Plouffe,
  `π = ∑_j 16^(-j) (4/(8j+1) - 2/(8j+4) - 1/(8j+5) - 1/(8j+6))`, as
  `P(1, 16, 8, (4, 0, 0, -2, -1, -1, 0, 0)) = π`;
* `exists_bailey_pi_of_two_pow`: for every `e ≥ 1` there is a formula for `π` in base `2^e`;
* `bailey_pi_iff`: for `b ≥ 2`, some `P(1, b^B, N, c)` is a non-zero rational multiple of `π`
  if and only if `b` is a power of 2.

The formula is not proved from scratch. Its pattern in the class F (weights `2^(-⌊k/2⌋)`),
`ρ = (4, 0, 0, -8, -4, -8, 0, 0)` of period 8, is `4·namedA1 + 2·namedL8` in the named series
of `PiFormula/VSeries.lean` (`rhoBBP_eq`, a check of 120 residues): `namedA1` has the value
`π/4` and `namedL8` has the value 0. For the base `2^e` the same pattern is read with the
period `8e`: it is `P(1, (2^e)^4, 8e, c)` with `c_i = ρ(i) / 2^⌊i/2⌋`.

Baker's theorem is used only in `bailey_pi_iff`, through `no_pi_bailey`.
-/

namespace PiFormula

namespace BaseB

/-! ## 1. The formula of Bailey, Borwein and Plouffe -/

private theorem pos4 : 0 < 4 := by norm_num

/-- The coefficients `a_1, …, a_8` of the formula of Bailey, Borwein and Plouffe. -/
def bbpCoeff : Fin (2 * 4) → ℚ := ![4, 0, 0, -2, -1, -1, 0, 0]

/-- The pattern of the formula of Bailey, Borwein and Plouffe in the class F:
`(4, 0, 0, -8, -4, -8, 0, 0)`, of period 8. -/
def rhoBBP : ℕ → ℚ := patF2 (Nat.mul_pos two_pos pos4) bbpCoeff

theorem rhoBBP_periodic (k : ℕ) : rhoBBP (k + 2 * 4) = rhoBBP k :=
  patF2_periodic _ bbpCoeff k

private theorem rhoBBP_periodic_120 (k : ℕ) : rhoBBP (k + 120) = rhoBBP k :=
  periodic_mul (f := rhoBBP) (a := 2 * 4) rhoBBP_periodic 15 k

/-- The pattern in the eight named series: `4·namedA1 + 2·namedL8`. -/
theorem rhoBBP_eq (k : ℕ) : rhoBBP k = namedComb ![4, 0, 0, 0, 2, 0, 0, 0] k := by
  have htab : ∀ r < 120, rhoBBP r = namedComb ![4, 0, 0, 0, 2, 0, 0, 0] r := by
    decide +kernel
  have h1 := mod_120 rhoBBP_periodic_120 k
  have h2 := mod_120 (namedComb_periodic ![4, 0, 0, 0, 2, 0, 0, 0]) k
  rw [← h1, ← h2]
  exact htab (k % 120) (Nat.mod_lt _ (by norm_num))

/-- The series of the pattern has the value `π`. -/
theorem hasSum_rhoBBP : HasSum (seriesTerm rhoBBP) Real.pi := by
  have h := hasSum_of_coords (f := rhoBBP) ![4, 0, 0, 0, 2, 0, 0, 0] rhoBBP_eq (c := 4)
    (by norm_num)
  have e : ((4 : ℚ) : ℝ) * (Real.pi / 4) = Real.pi := by
    rw [Rat.cast_ofNat]
    ring
  rw [e] at h
  exact h

/-- For `b = 2`, `baileyBlock` is the block of `PiFormula/BaileySums.lean`. -/
theorem baileyBlock_two (B n : ℕ) (a : Fin n → ℚ) :
    baileyBlock 2 B n a = PiFormula.baileyBlock B n a := by
  funext j
  simp only [baileyBlock, PiFormula.baileyBlock, Nat.cast_ofNat]

/-- The formula of Bailey, Borwein and Plouffe, written in base 2: `P(1, 2^4, 8, A) = π`. -/
theorem bbp_formula_two : HasSum (baileyBlock 2 4 8 ![4, 0, 0, -2, -1, -1, 0, 0]) Real.pi := by
  have h := (hasSum_bailey_F2 pos4 bbpCoeff Real.pi).2 hasSum_rhoBBP
  rw [← baileyBlock_two] at h
  exact h

/-- **The formula of Bailey, Borwein and Plouffe** (1995):

  `π = ∑_{j ≥ 0} 16^(-j) (4/(8j+1) - 2/(8j+4) - 1/(8j+5) - 1/(8j+6))`,

that is, `P(1, 16, 8, (4, 0, 0, -2, -1, -1, 0, 0)) = π`. -/
theorem bbp_formula : HasSum (baileyBlock 16 1 8 ![4, 0, 0, -2, -1, -1, 0, 0]) Real.pi := by
  have e : baileyBlock 16 1 8 ![4, 0, 0, -2, -1, -1, 0, 0] =
      baileyBlock 2 4 8 ![4, 0, 0, -2, -1, -1, 0, 0] :=
    baileyBlock_pow 2 4 1 8 ![4, 0, 0, -2, -1, -1, 0, 0]
  rw [e]
  exact bbp_formula_two

/-! ## 2. Every power of 2 -/

/-- The series of a rational pattern `ρ` of period `2B` in the class F is Bailey's sum
`P(1, 2^B, 2B, A)` with `a_i = ρ(i) / 2^⌊i/2⌋`. -/
theorem hasSum_bailey_two_of_pattern {B : ℕ} (hB : 0 < B) {ρ : ℕ → ℚ}
    (hρ : ∀ k, ρ (k + 2 * B) = ρ k) {x : ℝ} (h : HasSum (seriesTerm ρ) x) :
    HasSum (baileyBlock 2 B (2 * B) fun i => ρ ((i : ℕ) + 1) / 2 ^ (((i : ℕ) + 1) / 2)) x := by
  have hn : 0 < 2 * B := Nat.mul_pos two_pos hB
  have e : patF2 hn (fun i : Fin (2 * B) => ρ ((i : ℕ) + 1) / 2 ^ (((i : ℕ) + 1) / 2)) = ρ := by
    funext k
    have h2 : (2 : ℚ) ^ (((bIdx hn k : ℕ) + 1) / 2) ≠ 0 := pow_ne_zero _ (by norm_num)
    rw [patF2_apply, div_mul_cancel₀ _ h2]
    exact period_bIdx hn hρ k
  rw [baileyBlock_two, hasSum_bailey_F2 hB, e]
  exact h

/-- **Every power of 2 has a degree-1 BBP-type formula for `π`.** For `e ≥ 1` there are
`B, N ≥ 1` and rational `c_1, …, c_N` with

  `∑_{j ≥ 0} (2^e)^(-B j) ∑_{i=1}^{N} c_i / (N j + i) = π`.

Here `B = 4`, `N = 8e` and `c_i = ρ(i) / 2^⌊i/2⌋` for the pattern `ρ` of the formula of
Bailey, Borwein and Plouffe. -/
theorem exists_bailey_pi_of_two_pow {e : ℕ} (he : 0 < e) :
    ∃ (B N : ℕ) (c : Fin N → ℚ), 0 < B ∧ 0 < N ∧ HasSum (baileyBlock (2 ^ e) B N c) Real.pi := by
  have hB : 0 < e * 4 := Nat.mul_pos he pos4
  have hρ : ∀ k, rhoBBP (k + 2 * (e * 4)) = rhoBBP k := fun k => by
    have h := periodic_mul (f := rhoBBP) (a := 2 * 4) rhoBBP_periodic e k
    rwa [show 2 * 4 * e = 2 * (e * 4) by ring] at h
  refine ⟨4, 2 * (e * 4), fun i => rhoBBP ((i : ℕ) + 1) / 2 ^ (((i : ℕ) + 1) / 2), pos4,
    Nat.mul_pos two_pos hB, ?_⟩
  rw [baileyBlock_pow]
  exact hasSum_bailey_two_of_pattern hB hρ hasSum_rhoBBP

/-! ## 3. The exact characterization -/

/-- **The bases with a degree-1 BBP-type formula for `π` are the powers of 2.** For an integer
`b ≥ 2`, some series `∑_{j ≥ 0} b^(-B j) ∑_{i=1}^{N} c_i / (N j + i)` with `B, N ≥ 1` and
rational `c_i` is a non-zero rational multiple of `π` if and only if `b` is a power of 2. -/
theorem bailey_pi_iff {b : ℕ} (hb : 2 ≤ b) :
    (∃ (B N : ℕ) (c : Fin N → ℚ) (q : ℚ), 0 < B ∧ 0 < N ∧ q ≠ 0 ∧
      HasSum (baileyBlock b B N c) ((q : ℝ) * Real.pi)) ↔ ∃ e : ℕ, b = 2 ^ e := by
  constructor
  · rintro ⟨B, N, c, q, hB, hN, hq, h⟩
    by_contra hne
    exact hq (no_pi_bailey hb (fun k hk => hne ⟨k, hk⟩) hB hN c h)
  · rintro ⟨e, rfl⟩
    have he : 0 < e := by
      rcases Nat.eq_zero_or_pos e with rfl | he
      · norm_num at hb
      · exact he
    obtain ⟨B, N, c, hB, hN, h⟩ := exists_bailey_pi_of_two_pow he
    exact ⟨B, N, c, 1, hB, hN, one_ne_zero, by rwa [Rat.cast_one, one_mul]⟩

end BaseB

end PiFormula
