module

public import Pilean.Erdos.CriterionGeneral
public import Pilean.Erdos.Main

/-!
# Odd squares: an odd-valued function with sum `0`, so the 2-adic method is sharp

**Theorem** (`exists_oddValued_sumIsZero`). For every odd perfect square `q` there is a function
`f` on `ℤ/q` with `f(0) = 0`, every other value a rational number with odd numerator and odd
denominator, and `∑_{n ≥ 1} f(n)/n = 0` (`SumIsZero`).

With Theorem C (`isSquare_of_condA_condB`, `Main.lean`) and Okada's criterion
(`okadaCriterionGeneral`) this gives, for odd `q` (`exists_oddValued_sumIsZero_iff`): such a
function exists if and only if `q` is a perfect square. So an argument that uses only "the
values of `f` are odd" proves Erdős's conjecture for exactly the odd `q` that are not squares.

**The function.** Let `q = s²` with `s` odd, and let `E` be the function with period `s` given
by `E(n) = (-1)^(n mod s)` if `s ∤ n` and `E(n) = 0` if `s ∣ n` (`Squares.altNat`). Put
(`Squares.sqNat`, `Squares.sqFun`)

  `f(n) = -E(n)/s + [s ∣ n] E(n/s)`,

that is, `f(n) = -(-1)^(n mod s)/s` if `s ∤ n`, `f(n) = (-1)^((n/s) mod s)` if `s ∣ n` and
`s² ∤ n`, and `f(n) = 0` if `s² ∣ n`. It has period `s²` and its values off `0` are `±1/s` and
`±1`.

**Proof.** `∑_{x mod s} E(x) = 0` because `s - 1` is even, so the partial sums
`P(N) = ∑_{n < N} E(n)/n` have a limit `L` (`fourierLimit_gen`; this is elementary, no
transcendence is used). The multiples of `s` below `N` are the `s m` with `m < ⌈N/s⌉`, hence
`∑_{n < N} f(n)/n = -(1/s) P(N) + (1/s) P(⌈N/s⌉) → -(1/s) L + (1/s) L = 0`
(`Squares.partialSum_sqFun`, `Squares.sumIsZero_sqFun`).

Okada's criterion is not used for the existence; it is used for the other direction of the
equivalence, and it shows that this `f` satisfies conditions (a) and (b)
(`Squares.condA_condB_sqFun`).

**Remarks.**
* The function is not the one of the paper notes (`research/2026-11-23-erdos-pm1/`,
  `00_summary.md`, section 6.3, which uses `Ω`, `rad` and a Legendre symbol); it is simpler,
  and for `q = 9` the two agree up to sign (there the solution is unique up to a factor).
  Conditions (a) and (b) were also checked for it by exact computation for
  `q = 9, 25, 49, 81, 121, 225, 441, 625, 729, 1225, 2025, 3969` and (three primes, a sample of
  the units for (a)) `q = 11025, 27225, 99225`.
* The hypothesis `1 < q` of the two theorems is not needed (for `q = 1` the function `0`
  works); it is kept because the statements were fixed with it.
  `exists_oddValued_sumIsZero_of_isSquare` is the statement without it.

Status: complete, for every odd square; no hypothesis, the three standard axioms.
-/

@[expose] public section

open scoped BigOperators

open Filter Finset

namespace PiFormula

namespace Erdos

namespace Squares

/-! ## 1. The alternating function with period `s` -/

/-- `E(n) = (-1)^(n mod s)` if `s ∤ n`, and `E(n) = 0` if `s ∣ n`. -/
def altNat (s n : ℕ) : ℚ := if s ∣ n then 0 else (-1) ^ (n % s)

theorem altNat_mod (s n : ℕ) : altNat s (n % s) = altNat s n := by
  unfold altNat
  simp only [Nat.mod_mod, Nat.dvd_mod_iff (dvd_refl s)]

theorem altNat_of_dvd {s n : ℕ} (h : s ∣ n) : altNat s n = 0 := ite_eq_left h

theorem altNat_of_not_dvd {s n : ℕ} (h : ¬ s ∣ n) : altNat s n = 1 ∨ altNat s n = -1 := by
  unfold altNat
  rw [ite_eq_right h]
  exact neg_one_pow_eq_or ℚ (n % s)

/-- The function `E` on `ℤ/s`. -/
def altSign (s : ℕ) (x : ZMod s) : ℚ := altNat s x.val

theorem altSign_natCast (s n : ℕ) : altSign s (n : ZMod s) = altNat s n := by
  unfold altSign
  rw [ZMod.val_natCast, altNat_mod]

/-- `∑_{0 < n ≤ 2m} (-1)^n = 0`. -/
theorem sum_range_alt (m : ℕ) :
    ∑ n ∈ range (2 * m + 1), (if n = 0 then (0 : ℚ) else (-1) ^ n) = 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : 2 * m + 1 ≠ 0 := by omega
    have h2 : 2 * m + 1 + 1 ≠ 0 := by omega
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, ite_eq_right h1, ite_eq_right h2]
    ring

/-- A sum over `0 ≤ n < q` of a function of the class of `n` is the sum over `ℤ/q`. -/
theorem sum_range_natCast (q : ℕ) [NeZero q] (g : ZMod q → ℚ) :
    ∑ n ∈ range q, g (n : ZMod q) = ∑ x : ZMod q, g x := by
  refine Finset.sum_nbij' (fun n : ℕ => (n : ZMod q)) ZMod.val ?_ ?_ ?_ ?_ ?_
  · intro n _
    exact mem_univ _
  · intro x _
    exact mem_range.2 (ZMod.val_lt x)
  · intro n hn
    exact ZMod.val_cast_of_lt (mem_range.1 hn)
  · intro x _
    exact ZMod.natCast_zmod_val x
  · intro n _
    rfl

/-- For odd `s` the sum of `E` over a period is `0`. -/
theorem sum_altSign {s : ℕ} [NeZero s] (hs : Odd s) : ∑ x : ZMod s, altSign s x = 0 := by
  rw [← sum_range_natCast]
  obtain ⟨m, rfl⟩ := hs
  rw [← sum_range_alt m]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn' : n < 2 * m + 1 := mem_range.1 hn
  rw [altSign_natCast]
  unfold altNat
  rw [Nat.mod_eq_of_lt hn']
  by_cases h0 : n = 0
  · have hd : 2 * m + 1 ∣ n := h0 ▸ dvd_zero _
    rw [ite_eq_left h0, ite_eq_left hd]
  · have hd : ¬ 2 * m + 1 ∣ n := fun h => h0 (Nat.eq_zero_of_dvd_of_lt h hn')
    rw [ite_eq_right h0, ite_eq_right hd]

/-! ## 2. Two facts of analysis -/

/-- If the sum of `f` over a period is `0`, the partial sums of `∑ f(n)/n` have a limit. -/
theorem exists_tendsto_partialSum {q : ℕ} [NeZero q] (f : ZMod q → ℚ)
    (hsum : ∑ r : ZMod q, f r = 0) : ∃ L : ℝ, Tendsto (partialSum q f) atTop (nhds L) := by
  refine ⟨(-Okada.logForm q (Okada.fourierCoeff q f)).re, ?_⟩
  have h := (Complex.continuous_re.tendsto _).comp (fourierLimit_gen q f hsum)
  refine h.congr fun N => ?_
  exact Complex.ofReal_re _

/-- A sum over `n < N` of a function supported on the multiples of `s` is a sum over the
`m < ⌈N/s⌉`. -/
theorem sum_range_dvd (G : ℕ → ℝ) {s : ℕ} (hs : 0 < s) (hG : ∀ n, ¬ s ∣ n → G n = 0) (N : ℕ) :
    ∑ n ∈ range N, G n = ∑ m ∈ range ((N + s - 1) / s), G (s * m) := by
  have hmem : ∀ m : ℕ, m ∈ range ((N + s - 1) / s) ↔ s * m < N := by
    intro m
    rw [mem_range, Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hs, Nat.add_mul, one_mul,
      mul_comm m s]
    omega
  have hinj : ∀ a ∈ range ((N + s - 1) / s), ∀ b ∈ range ((N + s - 1) / s),
      s * a = s * b → a = b := fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hs h
  rw [← Finset.sum_image (s := range ((N + s - 1) / s)) (g := fun m => s * m) (f := G) hinj]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro x hx
    obtain ⟨m, hm, rfl⟩ := mem_image.1 hx
    exact mem_range.2 ((hmem m).1 hm)
  · intro x hx hx'
    by_contra h
    have hsx : s ∣ x := by
      by_contra h'
      exact h (hG x h')
    obtain ⟨m, rfl⟩ := hsx
    exact hx' (mem_image.2 ⟨m, (hmem m).2 (mem_range.1 hx), rfl⟩)

theorem tendsto_ceilDiv {s : ℕ} (hs : 0 < s) :
    Tendsto (fun N : ℕ => (N + s - 1) / s) atTop atTop := by
  refine tendsto_atTop_atTop.2 fun b => ⟨b * s, fun N hN => ?_⟩
  rw [Nat.le_div_iff_mul_le hs]
  omega

/-! ## 3. The function for `q = s²` -/

/-- `f(n) = -E(n)/s + [s ∣ n] E(n/s)`, as a function of the natural number `n`. -/
def sqNat (s n : ℕ) : ℚ := -altNat s n / s + if s ∣ n then altNat s (n / s) else 0

theorem sqNat_mod (s n : ℕ) : sqNat s (n % (s * s)) = sqNat s n := by
  have h1 : altNat s (n % (s * s)) = altNat s n := by
    rw [← altNat_mod, Nat.mod_mod_of_dvd _ (dvd_mul_right s s), altNat_mod]
  have h2 : s ∣ n % (s * s) ↔ s ∣ n := Nat.dvd_mod_iff (dvd_mul_right s s)
  have h3 : altNat s (n % (s * s) / s) = altNat s (n / s) := by
    rw [Nat.mod_mul_right_div_self, altNat_mod]
  unfold sqNat
  rw [h1, h3]
  simp only [h2]

/-- `f(n) = (-1)^((n/s) mod s)` up to the cases, if `s ∣ n`. -/
theorem sqNat_of_dvd {s n : ℕ} (h : s ∣ n) : sqNat s n = altNat s (n / s) := by
  unfold sqNat
  rw [altNat_of_dvd h, ite_eq_left h, neg_zero, zero_div, zero_add]

/-- `f(n) = -E(n)/s` if `s ∤ n`. -/
theorem sqNat_of_not_dvd {s n : ℕ} (h : ¬ s ∣ n) : sqNat s n = -altNat s n / s := by
  unfold sqNat
  rw [ite_eq_right h, add_zero]

/-- **The function**: `f(r) = -E(r)/s + [s ∣ r] E(r/s)` on `ℤ/s²`. -/
def sqFun (s : ℕ) (r : ZMod (s * s)) : ℚ := sqNat s r.val

theorem sqFun_natCast (s n : ℕ) : sqFun s (n : ZMod (s * s)) = sqNat s n := by
  unfold sqFun
  rw [ZMod.val_natCast, sqNat_mod]

theorem sqFun_zero (s : ℕ) : sqFun s 0 = 0 := by
  unfold sqFun
  rw [ZMod.val_zero, sqNat_of_dvd (dvd_zero s), Nat.zero_div, altNat_of_dvd (dvd_zero s)]

/-! ## 4. The values are odd -/

theorem isOddRat_neg {x : ℚ} (hx : IsOddRat x) : IsOddRat (-x) := by
  refine ⟨?_, ?_⟩
  · rw [Rat.neg_num]
    exact hx.1.neg
  · rw [Rat.neg_den]
    exact hx.2

theorem isOddRat_inv_natCast {s : ℕ} (hs : Odd s) : IsOddRat ((s : ℚ)⁻¹) := by
  refine ⟨?_, ?_⟩
  · rw [Rat.inv_natCast_num_of_pos hs.pos]
    exact odd_one
  · rw [Rat.inv_natCast_den_of_pos hs.pos]
    exact hs

/-- For odd `s`, every value of `f` off `0` has odd numerator and odd denominator: it is
`±1` on the multiples of `s` and `±1/s` elsewhere. -/
theorem isOddRat_sqFun {s : ℕ} (hs : Odd s) (r : ZMod (s * s)) (hr : r ≠ 0) :
    IsOddRat (sqFun s r) := by
  have hpos : 0 < s := hs.pos
  have : NeZero (s * s) := ⟨(Nat.mul_pos hpos hpos).ne'⟩
  have hlt : r.val < s * s := ZMod.val_lt r
  have hne : r.val ≠ 0 := fun h => hr ((ZMod.val_eq_zero r).1 h)
  unfold sqFun
  by_cases hd : s ∣ r.val
  · have h1 : r.val / s < s := Nat.div_lt_of_lt_mul hlt
    have h2 : 0 < r.val / s :=
      Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hd) hpos
    have hnd : ¬ s ∣ r.val / s := fun h => absurd (Nat.le_of_dvd h2 h) (not_le.2 h1)
    rw [sqNat_of_dvd hd]
    rcases altNat_of_not_dvd hnd with h | h <;> rw [h]
    · exact isOddRat_one
    · exact isOddRat_neg_one
  · rw [sqNat_of_not_dvd hd]
    rcases altNat_of_not_dvd hd with h | h <;> rw [h]
    · rw [neg_div, one_div]
      exact isOddRat_neg (isOddRat_inv_natCast hs)
    · rw [neg_neg, one_div]
      exact isOddRat_inv_natCast hs

/-! ## 5. The sum is `0` -/

/-- `∑_{n < N} f(n)/n = -(1/s) P(N) + (1/s) P(⌈N/s⌉)`, where `P` are the partial sums of
`∑ E(n)/n`. -/
theorem partialSum_sqFun {s : ℕ} (hs : 0 < s) (N : ℕ) :
    partialSum (s * s) (sqFun s) N =
      -(1 / (s : ℝ)) * partialSum s (altSign s) N +
        1 / (s : ℝ) * partialSum s (altSign s) ((N + s - 1) / s) := by
  unfold partialSum
  have h1 : ∀ n : ℕ, ((sqFun s (n : ZMod (s * s)) : ℚ) : ℝ) / (n : ℝ) =
      -(1 / (s : ℝ)) * ((altSign s (n : ZMod s) : ℝ) / (n : ℝ)) +
        (if s ∣ n then (altNat s (n / s) : ℝ) / (n : ℝ) else 0) := by
    intro n
    rw [sqFun_natCast, altSign_natCast]
    unfold sqNat
    split_ifs with h
    · push_cast
      ring
    · push_cast
      ring
  have h2 : ∀ n : ℕ, ¬ s ∣ n →
      (if s ∣ n then (altNat s (n / s) : ℝ) / (n : ℝ) else 0) = 0 :=
    fun n hn => ite_eq_right hn
  simp only [h1]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_range_dvd (fun n => if s ∣ n then (altNat s (n / s) : ℝ) / (n : ℝ) else 0) hs h2 N]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [ite_eq_left (dvd_mul_right s m), Nat.mul_div_cancel_left m hs, altSign_natCast]
  push_cast
  ring

/-- **The series of `f` has sum `0`**, for odd `s`. -/
theorem sumIsZero_sqFun {s : ℕ} (hs : Odd s) : SumIsZero (s * s) (sqFun s) := by
  have hpos : 0 < s := hs.pos
  have : NeZero s := ⟨hpos.ne'⟩
  obtain ⟨L, hL⟩ := exists_tendsto_partialSum (altSign s) (sum_altSign hs)
  have h := (hL.const_mul (-(1 / (s : ℝ)))).add
    ((hL.comp (tendsto_ceilDiv hpos)).const_mul (1 / (s : ℝ)))
  have e : -(1 / (s : ℝ)) * L + 1 / (s : ℝ) * L = 0 := by ring
  rw [e] at h
  refine h.congr fun N => ?_
  rw [partialSum_sqFun hpos N]
  rfl

/-- The function satisfies conditions (a) and (b) of Okada's criterion. -/
theorem condA_condB_sqFun {s : ℕ} (hs : Odd s) :
    CondA (s * s) (sqFun s) ∧ CondB (s * s) (sqFun s) :=
  (okadaCriterionGeneral (Nat.mul_pos hs.pos hs.pos) (sqFun s)).1 (sumIsZero_sqFun hs)

end Squares

/-! ## 6. The theorems -/

/-- For every odd perfect square `q` there is a function on `ℤ/q` with `f(0) = 0`, every other
value a rational number with odd numerator and odd denominator, and `∑ f(n)/n = 0`. -/
theorem exists_oddValued_sumIsZero_of_isSquare {q : ℕ} (hq : Odd q) (hsq : IsSquare q) :
    ∃ f : ZMod q → ℚ, f 0 = 0 ∧ (∀ r : ZMod q, r ≠ 0 → IsOddRat (f r)) ∧ SumIsZero q f := by
  obtain ⟨s, rfl⟩ := hsq
  have hs : Odd s := (Nat.odd_mul.1 hq).1
  exact ⟨Squares.sqFun s, Squares.sqFun_zero s, Squares.isOddRat_sqFun hs,
    Squares.sumIsZero_sqFun hs⟩

set_option linter.unusedVariables false in
/-- **The converse of Theorem C: the 2-adic method is sharp.** For every odd perfect square
`q > 1` there is a function `f` on `ℤ/q` with `f(0) = 0`, every other value a rational number
with odd numerator and odd denominator, and `∑_{n ≥ 1} f(n)/n = 0`. (The hypothesis `1 < q` is
not used.) -/
theorem exists_oddValued_sumIsZero {q : ℕ} (hq : Odd q) (hsq : IsSquare q) (hq1 : 1 < q) :
    ∃ f : ZMod q → ℚ, f 0 = 0 ∧ (∀ r : ZMod q, r ≠ 0 → IsOddRat (f r)) ∧ SumIsZero q f :=
  exists_oddValued_sumIsZero_of_isSquare hq hsq

/-- **Odd `q`: an odd-valued function with sum `0` exists exactly for the perfect squares.**
"Only if" is Okada's criterion with Theorem C; "if" is `exists_oddValued_sumIsZero`. -/
theorem exists_oddValued_sumIsZero_iff {q : ℕ} (hq : Odd q) (hq1 : 1 < q) :
    (∃ f : ZMod q → ℚ, f 0 = 0 ∧ (∀ r : ZMod q, r ≠ 0 → IsOddRat (f r)) ∧ SumIsZero q f)
      ↔ IsSquare q := by
  constructor
  · rintro ⟨f, h0, hodd, hS⟩
    have h := (okadaCriterionGeneral (le_of_lt hq1) f).1 hS
    exact isSquare_of_condA_condB hq f h0 hodd h.1 h.2
  · intro hsq
    exact exists_oddValued_sumIsZero hq hsq hq1

end Erdos

end PiFormula
