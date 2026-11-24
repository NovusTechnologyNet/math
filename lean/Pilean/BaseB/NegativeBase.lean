module

public import Pilean.BaseB.Sharpness

/-!
# Negative bases: a degree-1 BBP-type formula for `π` exists only if `|β|` is a power of 2

For an integer base `β` (possibly negative), Bailey's `P(1, β^B, N, a)` is

  `∑_{j ≥ 0} β^(-B j) ∑_{i=1}^{N} a_i / (N j + i)`,   `a_i` rational.

**Theorem** (`no_pi_bailey_int`). Let `|β| ≥ 2` be not a power of 2. If such a series has the
value `q π` with `q` rational, then `q = 0`.

The proof pairs the blocks `2j` and `2j + 1`. Since `β^(2 B j) = |β|^(2 B j)`, the sum of
the two blocks is the block `j` of `P(1, |β|^(2B), 2N, a')` with `a'_i = a_i` for `i ≤ N` and
`a'_(N+i) = a_i / β^B` (`baileyBlockInt_pair`). A convergent series may be summed in pairs,
so the paired series has the same value, and `no_pi_bailey` applies to `|β|`.

The condition is exact (`bailey_int_pi_iff`): if `|β| = 2^e` with `e ≥ 1`, a formula for `π`
in base `β` with an even exponent `B` is a formula in base `|β|`, and
`exists_bailey_pi_of_two_pow` gives one.
-/

@[expose] public section

namespace PiFormula

namespace BaseB

/-- Block `j` of `P(1, β^B, N, a)` for an integer base `β` (possibly negative). -/
noncomputable def baileyBlockInt (β : ℤ) (B N : ℕ) (a : Fin N → ℚ) (j : ℕ) : ℝ :=
  ∑ i : Fin N, (a i : ℝ) / (β : ℝ) ^ (B * j) / ((N * j + i + 1 : ℕ) : ℝ)

/-- For a base `β = b ≥ 0` this is `baileyBlock`. -/
theorem baileyBlockInt_natCast (b B N : ℕ) (a : Fin N → ℚ) :
    baileyBlockInt (b : ℤ) B N a = baileyBlock b B N a := by
  funext j
  simp only [baileyBlockInt, baileyBlock, Int.cast_natCast]

private theorem natAbs_sq_real (β : ℤ) : ((β.natAbs : ℕ) : ℝ) ^ 2 = (β : ℝ) ^ 2 := by
  rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]

/-! ## 1. No formula unless `|β|` is a power of 2 -/

/-- The coefficients of the paired series: `a'_i = a_i` and `a'_(N+i) = a_i / β^B`. -/
def intPairCoeff (β : ℤ) (B : ℕ) {N : ℕ} (a : Fin N → ℚ) : Fin (N + N) → ℚ :=
  Fin.append a fun i => a i / (β : ℚ) ^ B

/-- **Two consecutive blocks in base `β` are one block in base `|β|`**, with the exponent
`2B`, the length `2N` and the coefficients `intPairCoeff β B a`. -/
theorem baileyBlockInt_pair (β : ℤ) (B N : ℕ) (a : Fin N → ℚ) (j : ℕ) :
    baileyBlockInt β B N a (2 * j) + baileyBlockInt β B N a (2 * j + 1) =
      baileyBlock β.natAbs (2 * B) (N + N) (intPairCoeff β B a) j := by
  have hp : ((β.natAbs : ℕ) : ℝ) ^ (2 * B * j) = (β : ℝ) ^ (B * (2 * j)) := by
    rw [mul_assoc, pow_mul, natAbs_sq_real, ← pow_mul, mul_left_comm]
  simp only [baileyBlockInt, baileyBlock]
  rw [Fin.sum_univ_add]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => ?_)
    (Finset.sum_congr rfl fun i _ => ?_)
  · rw [intPairCoeff, Fin.append_left, hp, Fin.val_castAdd,
      show N * (2 * j) + (i : ℕ) + 1 = (N + N) * j + (i : ℕ) + 1 by ring]
  · rw [intPairCoeff, Fin.append_right, hp, Fin.val_natAdd,
      show N * (2 * j + 1) + (i : ℕ) + 1 = (N + N) * j + (N + (i : ℕ)) + 1 by ring,
      mul_add, mul_one, pow_add]
    push_cast
    ring

/-- A convergent series, summed in pairs of consecutive terms. -/
private theorem hasSum_pair {f : ℕ → ℝ} {x : ℝ} (h : HasSum f x) :
    HasSum (fun j : ℕ => f (2 * j) + f (2 * j + 1)) x := by
  have he : Summable fun j : ℕ => f (2 * j) :=
    h.summable.comp_injective (mul_right_injective₀ two_ne_zero)
  have ho : Summable fun j : ℕ => f (2 * j + 1) :=
    h.summable.comp_injective fun m n hmn => by
      have h' : 2 * m + 1 = 2 * n + 1 := hmn
      omega
  have e := (he.hasSum.even_add_odd ho.hasSum).unique h
  have h2 := he.hasSum.add ho.hasSum
  rw [e] at h2
  exact h2

/-- **The series in base `β`, summed in pairs of blocks, is a series in base `|β|`**:
`P(1, β^B, N, a) = P(1, |β|^(2B), 2N, a')` with `a' = intPairCoeff β B a`. -/
theorem hasSum_baileyBlockInt_pair {β : ℤ} {B N : ℕ} {a : Fin N → ℚ} {x : ℝ}
    (h : HasSum (baileyBlockInt β B N a) x) :
    HasSum (baileyBlock β.natAbs (2 * B) (N + N) (intPairCoeff β B a)) x := by
  have e : baileyBlock β.natAbs (2 * B) (N + N) (intPairCoeff β B a) = fun j : ℕ =>
      baileyBlockInt β B N a (2 * j) + baileyBlockInt β B N a (2 * j + 1) :=
    funext fun j => (baileyBlockInt_pair β B N a j).symm
  rw [e]
  exact hasSum_pair h

/-- **No degree-1 BBP-type formula for `π` in a base `β` with `|β|` not a power of 2**, for
negative bases too. Let `β` be an integer with `|β| ≥ 2` not a power of 2, `B, N ≥ 1`, and
`c_1, …, c_N` rational. If

  `∑_{j ≥ 0} β^(-B j) ∑_{i=1}^{N} c_i / (N j + i) = q π`

with `q` rational, then `q = 0`. -/
theorem no_pi_bailey_int {β : ℤ} {B N : ℕ} (hβ : 2 ≤ β.natAbs) (h2 : ∀ k : ℕ, β.natAbs ≠ 2 ^ k)
    (hB : 0 < B) (hN : 0 < N) (c : Fin N → ℚ) {q : ℚ}
    (h : HasSum (baileyBlockInt β B N c) ((q : ℝ) * Real.pi)) : q = 0 :=
  no_pi_bailey hβ h2 (Nat.mul_pos two_pos hB) (Nat.add_pos_left hN N) _
    (hasSum_baileyBlockInt_pair h)

/-! ## 2. The exact characterization -/

/-- For an even exponent the sign of the base plays no role. -/
theorem baileyBlockInt_even (β : ℤ) (B N : ℕ) (a : Fin N → ℚ) :
    baileyBlockInt β (2 * B) N a = baileyBlock β.natAbs (2 * B) N a := by
  funext j
  have hp : ((β.natAbs : ℕ) : ℝ) ^ (2 * B * j) = (β : ℝ) ^ (2 * B * j) := by
    rw [mul_assoc, pow_mul, natAbs_sq_real, ← pow_mul]
  simp only [baileyBlockInt, baileyBlock, hp]

/-- **Every integer base `β` with `|β| = 2^e`, `e ≥ 1`, has a degree-1 BBP-type formula for
`π`** (with an even exponent `B`, so that it is a formula in base `|β|`). -/
theorem exists_bailey_int_pi {β : ℤ} {e : ℕ} (he : 0 < e) (hβ : β.natAbs = 2 ^ e) :
    ∃ (B N : ℕ) (c : Fin N → ℚ), 0 < B ∧ 0 < N ∧ HasSum (baileyBlockInt β B N c) Real.pi := by
  obtain ⟨B, N, c, hB, hN, h⟩ :=
    exists_bailey_pi_of_two_pow (e := 2 * e) (Nat.mul_pos two_pos he)
  refine ⟨2 * B, N, c, Nat.mul_pos two_pos hB, hN, ?_⟩
  rw [baileyBlockInt_even, hβ, ← baileyBlock_pow, ← pow_mul, mul_comm e 2]
  exact h

/-- **The integer bases with a degree-1 BBP-type formula for `π` are `±2^e`.** For an integer
`β` with `|β| ≥ 2`, some series `∑_{j ≥ 0} β^(-B j) ∑_{i=1}^{N} c_i / (N j + i)` with
`B, N ≥ 1` and rational `c_i` is a non-zero rational multiple of `π` if and only if `|β|` is a
power of 2. -/
theorem bailey_int_pi_iff {β : ℤ} (hβ : 2 ≤ β.natAbs) :
    (∃ (B N : ℕ) (c : Fin N → ℚ) (q : ℚ), 0 < B ∧ 0 < N ∧ q ≠ 0 ∧
      HasSum (baileyBlockInt β B N c) ((q : ℝ) * Real.pi)) ↔ ∃ e : ℕ, β.natAbs = 2 ^ e := by
  constructor
  · rintro ⟨B, N, c, q, hB, hN, hq, h⟩
    by_contra hne
    exact hq (no_pi_bailey_int hβ (fun k hk => hne ⟨k, hk⟩) hB hN c h)
  · rintro ⟨e, he⟩
    have he0 : 0 < e := by
      rcases Nat.eq_zero_or_pos e with rfl | h0
      · rw [he] at hβ
        norm_num at hβ
      · exact h0
    obtain ⟨B, N, c, hB, hN, h⟩ := exists_bailey_int_pi he0 he
    exact ⟨B, N, c, 1, hB, hN, one_ne_zero, by rwa [Rat.cast_one, one_mul]⟩

end BaseB

end PiFormula
