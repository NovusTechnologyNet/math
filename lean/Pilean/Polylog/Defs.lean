module

public import Mathlib

/-!
# The polylogarithm as a power series, and Bailey's series of degree `s`

The polylogarithm of order `s` is `Li_s(z) = ∑_{k ≥ 1} z^k / k^s`. Mathlib has no polylogarithm;
this file defines it as a series, for a natural number `s`:

* `polylog s z`, for complex `z`, and `polylogReal s x`, for real `x`;
  the terms are written with the index `k + 1`: `z^(k+1) / (k+1)^s`;
* `summable_polylog_term`: the series converges absolutely on the closed unit disc for `s ≥ 2`
  (`summable_polylog_term_of_lt`: on the open unit disc for every `s`);
* `hasSum_polylog`, `hasSum_polylogReal`, and the forms indexed by all `m : ℕ`,
  `hasSum_polylog_nat`, `hasSum_polylogReal_nat`: `∑_m z^m / m^s`, where the term at `m = 0`
  is `1 / 0^s = 0`; `hasSum_re_polylog_nat`, `hasSum_im_polylog_nat`: the series of the real
  and imaginary parts;
* `polylog_ofReal`: the two definitions agree on the real line; `polylog_conj`;
* `polylogReal_two_one`: `Li_2(1) = π²/6`;
* `hasSum_dvd`: the sub-series over the multiples of `d`,
  `∑_{d ∣ m} y^(m/d) / m^s = (∑_m y^m / m^s) / d^s`;
* `polylog_dup`, `polylogReal_dup`: the duplication formula
  `2^s (Li_s(z) + Li_s(-z)) = 2 Li_s(z²)`.

Bailey's notation is `P(s, β, N, A) = ∑_{j ≥ 0} β^(-j) ∑_{i=1}^{N} a_i / (N j + i)^s`. The
degree-`s` versions of the definitions of the project for `s = 1`:

* `baileyBlockDegReal s β N a j`: block `j`, for a real base and real coefficients;
* `baileyBlockDeg s b B N a j`: block `j` for the base `b^B` (`b` natural) and a rational
  vector; `HasBaileyValueDeg s b B N a x`: the series converges to `x`;
* `BaileyFormulaDeg x c s b B N a`: the statement `x = c · P(s, b^B, N, a)`.

The regrouping lemmas express `P(s, β, N, A)` through series `∑_m u(m) / m^s`:

* `hasSum_block_sums`: a convergent series, summed in blocks of `N` consecutive terms;
* `hasSum_baileyBlockDegReal_of_quasiperiodic`: if `u(m + N) = u(m) / β` then
  `∑_{m ≥ 1} u(m) / m^s = P(s, β, N, (u(1), …, u(N)))`;
* `hasSum_baileyBlockDegReal_of_periodic`: for a pattern `c` of period `N` and `x^N β = 1`,
  `∑_{m ≥ 1} c(m) x^m / m^s = P(s, β, N, (c(1) x, …, c(N) x^N))`;
* `hasBaileyValueDeg_of_quasiperiodic`: the same for the base `b^B` and a rational vector.
-/

@[expose] public section

namespace PiFormula

namespace Polylog

/-! ## 1. The series -/

/-- The polylogarithm of order `s` as a power series: `Li_s(z) = ∑_{k ≥ 1} z^k / k^s`. The term
of index `k : ℕ` is `z^(k+1) / (k+1)^s`. The series converges for `‖z‖ < 1`, and for `‖z‖ ≤ 1`
when `s ≥ 2`; outside, the value is the junk value `0` of `tsum`. -/
noncomputable def polylog (s : ℕ) (z : ℂ) : ℂ := ∑' k : ℕ, z ^ (k + 1) / ((k : ℂ) + 1) ^ s

/-- The real polylogarithm of order `s`: `Li_s(x) = ∑_{k ≥ 1} x^k / k^s` for real `x`. -/
noncomputable def polylogReal (s : ℕ) (x : ℝ) : ℝ := ∑' k : ℕ, x ^ (k + 1) / ((k : ℝ) + 1) ^ s

/-- The norm of a term of the series. -/
theorem norm_polylog_term (s : ℕ) (z : ℂ) (k : ℕ) :
    ‖z ^ (k + 1) / ((k : ℂ) + 1) ^ s‖ = ‖z‖ ^ (k + 1) / ((k : ℝ) + 1) ^ s := by
  have e : ‖(k : ℂ) + 1‖ = (k : ℝ) + 1 := by
    rw [← Nat.cast_succ, Complex.norm_natCast, Nat.cast_succ]
  rw [norm_div, norm_pow, norm_pow, e]

/-- `∑ 1/(k+1)^s` converges for `s ≥ 2`. -/
theorem summable_one_div_succ_pow {s : ℕ} (hs : 2 ≤ s) :
    Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ s := by
  have h := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by omega : 1 < s))
  simpa using h

/-- On the closed unit disc a term is bounded by `1/(k+1)^s`. -/
theorem norm_polylog_term_le (s : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) (k : ℕ) :
    ‖z ^ (k + 1) / ((k : ℂ) + 1) ^ s‖ ≤ 1 / ((k : ℝ) + 1) ^ s := by
  rw [norm_polylog_term]
  have hp : (0 : ℝ) < ((k : ℝ) + 1) ^ s := by positivity
  exact div_le_div_of_nonneg_right (pow_le_one₀ (norm_nonneg z) hz) hp.le

/-- **Convergence on the closed unit disc**, for `s ≥ 2`. -/
theorem summable_polylog_term {s : ℕ} (hs : 2 ≤ s) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Summable fun k : ℕ => z ^ (k + 1) / ((k : ℂ) + 1) ^ s :=
  Summable.of_norm_bounded (summable_one_div_succ_pow hs) (norm_polylog_term_le s hz)

/-- **Convergence on the open unit disc**, for every `s`. -/
theorem summable_polylog_term_of_lt (s : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun k : ℕ => z ^ (k + 1) / ((k : ℂ) + 1) ^ s := by
  have hg : Summable fun k : ℕ => ‖z‖ ^ (k + 1) :=
    (summable_nat_add_iff 1).2 (summable_geometric_of_lt_one (norm_nonneg z) hz)
  refine Summable.of_norm_bounded hg fun k => ?_
  rw [norm_polylog_term]
  have h1 : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ s :=
    one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) k])
  exact div_le_self (pow_nonneg (norm_nonneg z) _) h1

/-- `Li_s(z)` is the sum of its series on the closed unit disc, for `s ≥ 2`. -/
theorem hasSum_polylog {s : ℕ} (hs : 2 ≤ s) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    HasSum (fun k : ℕ => z ^ (k + 1) / ((k : ℂ) + 1) ^ s) (polylog s z) :=
  (summable_polylog_term hs hz).hasSum

/-- `Li_s(z)` is the sum of its series on the open unit disc, for every `s`. -/
theorem hasSum_polylog_of_lt (s : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => z ^ (k + 1) / ((k : ℂ) + 1) ^ s) (polylog s z) :=
  (summable_polylog_term_of_lt s hz).hasSum

/-- A series `∑_{m ≥ 0} f(m)` with `f(0) = 0` is the series `∑_{k ≥ 0} f(k + 1)`. -/
theorem hasSum_succ_iff {𝕜 : Type*} [NormedField 𝕜] {f : ℕ → 𝕜} (h0 : f 0 = 0) {L : 𝕜} :
    HasSum (fun k : ℕ => f (k + 1)) L ↔ HasSum f L := by
  rw [← hasSum_nat_add_iff' 1 (f := f)]
  simp [h0]

/-- `Li_s(z) = ∑_{m ≥ 1} z^m / m^s`, indexed by all `m : ℕ` (the term at `m = 0` is `0`);
closed unit disc, `s ≥ 2`. -/
theorem hasSum_polylog_nat {s : ℕ} (hs : 2 ≤ s) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    HasSum (fun m : ℕ => z ^ m / (m : ℂ) ^ s) (polylog s z) := by
  refine (hasSum_succ_iff (f := fun m : ℕ => z ^ m / (m : ℂ) ^ s) ?_).1 ?_
  · simp [show s ≠ 0 by omega]
  · simpa using hasSum_polylog hs hz

/-- `Li_s(z) = ∑_{m ≥ 1} z^m / m^s`, indexed by all `m : ℕ`; open unit disc, `s ≥ 1`. -/
theorem hasSum_polylog_nat_of_lt {s : ℕ} (hs : s ≠ 0) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun m : ℕ => z ^ m / (m : ℂ) ^ s) (polylog s z) := by
  refine (hasSum_succ_iff (f := fun m : ℕ => z ^ m / (m : ℂ) ^ s) ?_).1 ?_
  · simp [hs]
  · simpa using hasSum_polylog_of_lt s hz

/-- The real part of `w / m^s` for a natural number `m`. -/
theorem div_natCast_pow_re (w : ℂ) (m s : ℕ) : (w / (m : ℂ) ^ s).re = w.re / (m : ℝ) ^ s := by
  rw [← Nat.cast_pow, Complex.div_natCast_re, Nat.cast_pow]

/-- The imaginary part of `w / m^s` for a natural number `m`. -/
theorem div_natCast_pow_im (w : ℂ) (m s : ℕ) : (w / (m : ℂ) ^ s).im = w.im / (m : ℝ) ^ s := by
  rw [← Nat.cast_pow, Complex.div_natCast_im, Nat.cast_pow]

/-- `Re Li_s(z) = ∑_{m ≥ 1} Re(z^m) / m^s` on the closed unit disc, `s ≥ 2`. -/
theorem hasSum_re_polylog_nat {s : ℕ} (hs : 2 ≤ s) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    HasSum (fun m : ℕ => (z ^ m).re / (m : ℝ) ^ s) (polylog s z).re :=
  (Complex.hasSum_re (hasSum_polylog_nat hs hz)).congr_fun fun m =>
    (div_natCast_pow_re (z ^ m) m s).symm

/-- `Im Li_s(z) = ∑_{m ≥ 1} Im(z^m) / m^s` on the closed unit disc, `s ≥ 2`. -/
theorem hasSum_im_polylog_nat {s : ℕ} (hs : 2 ≤ s) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    HasSum (fun m : ℕ => (z ^ m).im / (m : ℝ) ^ s) (polylog s z).im :=
  (Complex.hasSum_im (hasSum_polylog_nat hs hz)).congr_fun fun m =>
    (div_natCast_pow_im (z ^ m) m s).symm

/-! ## 2. The real polylogarithm -/

/-- The two definitions agree on the real line. -/
theorem polylog_ofReal (s : ℕ) (x : ℝ) : polylog s (x : ℂ) = (polylogReal s x : ℂ) := by
  rw [polylog, polylogReal, Complex.ofReal_tsum]
  refine tsum_congr fun k => ?_
  simp

/-- The real polylogarithm is the real part of the complex one. -/
theorem polylogReal_eq_re (s : ℕ) (x : ℝ) : polylogReal s x = (polylog s (x : ℂ)).re := by
  rw [polylog_ofReal, Complex.ofReal_re]

/-- Convergence of the real series on `[-1, 1]`, for `s ≥ 2`. -/
theorem summable_polylogReal_term {s : ℕ} (hs : 2 ≤ s) {x : ℝ} (hx : |x| ≤ 1) :
    Summable fun k : ℕ => x ^ (k + 1) / ((k : ℝ) + 1) ^ s := by
  have h := summable_polylog_term hs (z := (x : ℂ))
    (by rwa [Complex.norm_real, Real.norm_eq_abs])
  rw [← Complex.summable_ofReal]
  refine h.congr fun k => ?_
  simp

/-- Convergence of the real series on `(-1, 1)`, for every `s`. -/
theorem summable_polylogReal_term_of_lt (s : ℕ) {x : ℝ} (hx : |x| < 1) :
    Summable fun k : ℕ => x ^ (k + 1) / ((k : ℝ) + 1) ^ s := by
  have h := summable_polylog_term_of_lt s (z := (x : ℂ))
    (by rwa [Complex.norm_real, Real.norm_eq_abs])
  rw [← Complex.summable_ofReal]
  refine h.congr fun k => ?_
  simp

/-- The real `Li_s(x)` is the sum of its series on `[-1, 1]`, for `s ≥ 2`. -/
theorem hasSum_polylogReal {s : ℕ} (hs : 2 ≤ s) {x : ℝ} (hx : |x| ≤ 1) :
    HasSum (fun k : ℕ => x ^ (k + 1) / ((k : ℝ) + 1) ^ s) (polylogReal s x) :=
  (summable_polylogReal_term hs hx).hasSum

/-- The real `Li_s(x)` is the sum of its series on `(-1, 1)`, for every `s`. -/
theorem hasSum_polylogReal_of_lt (s : ℕ) {x : ℝ} (hx : |x| < 1) :
    HasSum (fun k : ℕ => x ^ (k + 1) / ((k : ℝ) + 1) ^ s) (polylogReal s x) :=
  (summable_polylogReal_term_of_lt s hx).hasSum

/-- The real `Li_s(x) = ∑_{m ≥ 1} x^m / m^s`, indexed by all `m : ℕ` (the term at `m = 0` is
`0`); `|x| ≤ 1`, `s ≥ 2`. -/
theorem hasSum_polylogReal_nat {s : ℕ} (hs : 2 ≤ s) {x : ℝ} (hx : |x| ≤ 1) :
    HasSum (fun m : ℕ => x ^ m / (m : ℝ) ^ s) (polylogReal s x) := by
  refine (hasSum_succ_iff (f := fun m : ℕ => x ^ m / (m : ℝ) ^ s) ?_).1 ?_
  · simp [show s ≠ 0 by omega]
  · simpa using hasSum_polylogReal hs hx

/-- `Li_s(0) = 0`. -/
theorem polylog_zero (s : ℕ) : polylog s 0 = 0 := by
  simp [polylog]

/-- `Li_s(0) = 0`. -/
theorem polylogReal_zero (s : ℕ) : polylogReal s 0 = 0 := by
  simp [polylogReal]

/-- `Li_s(conj z) = conj (Li_s(z))`. -/
theorem polylog_conj (s : ℕ) (z : ℂ) :
    polylog s ((starRingEnd ℂ) z) = (starRingEnd ℂ) (polylog s z) := by
  rw [polylog, polylog, Complex.conj_tsum]
  refine tsum_congr fun k => ?_
  simp

/-- `Li_2(1) = π²/6` (Euler; Mathlib's `hasSum_zeta_two`). -/
theorem polylogReal_two_one : polylogReal 2 1 = Real.pi ^ 2 / 6 := by
  have h := hasSum_polylogReal_nat (s := 2) le_rfl (x := 1) (by norm_num)
  have h2 : HasSum (fun m : ℕ => (1 : ℝ) ^ m / (m : ℝ) ^ 2) (Real.pi ^ 2 / 6) := by
    simpa using hasSum_zeta_two
  exact h.unique h2

/-! ## 3. Sub-series over the multiples of `d`, and duplication -/

/-- **The sub-series over the multiples of `d`.** If `∑_m y^m / m^s = L` then
`∑_{d ∣ m} y^(m/d) / m^s = L / d^s`. -/
theorem hasSum_dvd {𝕜 : Type*} [NormedField 𝕜] {s d : ℕ} (hd : 0 < d) {y L : 𝕜}
    (h : HasSum (fun m : ℕ => y ^ m / (m : 𝕜) ^ s) L) :
    HasSum (fun m : ℕ => if d ∣ m then y ^ (m / d) / (m : 𝕜) ^ s else 0)
      (L / (d : 𝕜) ^ s) := by
  have hinj : Function.Injective fun m : ℕ => d * m := fun _ _ e =>
    Nat.eq_of_mul_eq_mul_left hd e
  have hoff : ∀ m ∉ Set.range (fun m : ℕ => d * m),
      (if d ∣ m then y ^ (m / d) / (m : 𝕜) ^ s else 0) = 0 := fun m hm =>
    ite_eq_right fun ⟨c, hc⟩ => hm ⟨c, hc.symm⟩
  rw [← hinj.hasSum_iff hoff]
  have e : ((fun m : ℕ => if d ∣ m then y ^ (m / d) / (m : 𝕜) ^ s else 0) ∘
      fun m : ℕ => d * m) = fun m : ℕ => y ^ m / (m : 𝕜) ^ s / (d : 𝕜) ^ s := by
    funext m
    simp only [Function.comp_apply]
    rw [ite_eq_left (dvd_mul_right d m), Nat.mul_div_cancel_left m hd, Nat.cast_mul, mul_pow,
      div_div, mul_comm]
  rw [e]
  exact h.div_const _

/-- `z^m + (-z)^m` is `2 z^m` for even `m` and `0` for odd `m`. -/
theorem pow_add_neg_pow {𝕜 : Type*} [Field 𝕜] (z : 𝕜) (m : ℕ) :
    z ^ m + (-z) ^ m = if 2 ∣ m then 2 * (z ^ 2) ^ (m / 2) else 0 := by
  rcases Nat.even_or_odd m with he | ho
  · have h2 : 2 ∣ m := he.two_dvd
    obtain ⟨c, rfl⟩ := h2
    rw [ite_eq_left (dvd_mul_right 2 c), Nat.mul_div_cancel_left c two_pos, he.neg_pow, pow_mul]
    ring
  · have h2 : ¬ 2 ∣ m := fun h => (Nat.not_even_iff_odd.2 ho) (even_iff_two_dvd.2 h)
    rw [ite_eq_right h2, ho.neg_pow]
    ring

/-- **Duplication.** `2^s (Li_s(z) + Li_s(-z)) = 2 Li_s(z²)` on the closed unit disc,
`s ≥ 2`. -/
theorem polylog_dup {s : ℕ} (hs : 2 ≤ s) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    2 ^ s * (polylog s z + polylog s (-z)) = 2 * polylog s (z ^ 2) := by
  have hz2 : ‖z ^ 2‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg z) hz
  have h1 := (hasSum_polylog_nat hs hz).add (hasSum_polylog_nat hs (z := -z) (by rwa [norm_neg]))
  have h2 := (hasSum_dvd (d := 2) two_pos (hasSum_polylog_nat hs hz2)).mul_left 2
  have e : (fun m : ℕ => z ^ m / (m : ℂ) ^ s + (-z) ^ m / (m : ℂ) ^ s) = fun m : ℕ =>
      2 * (if 2 ∣ m then (z ^ 2) ^ (m / 2) / (m : ℂ) ^ s else 0) := by
    funext m
    rw [← add_div, pow_add_neg_pow]
    split_ifs <;> ring
  rw [e] at h1
  have h3 := h1.unique h2
  have h20 : (2 : ℂ) ^ s ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [h3]
  push_cast
  field_simp

/-- **Duplication** for the real polylogarithm: `2^s (Li_s(x) + Li_s(-x)) = 2 Li_s(x²)` for
`|x| ≤ 1`, `s ≥ 2`. -/
theorem polylogReal_dup {s : ℕ} (hs : 2 ≤ s) {x : ℝ} (hx : |x| ≤ 1) :
    2 ^ s * (polylogReal s x + polylogReal s (-x)) = 2 * polylogReal s (x ^ 2) := by
  have h := polylog_dup hs (z := (x : ℂ)) (by rwa [Complex.norm_real, Real.norm_eq_abs])
  rw [← Complex.ofReal_neg, ← Complex.ofReal_pow, polylog_ofReal, polylog_ofReal,
    polylog_ofReal] at h
  exact_mod_cast h

/-- **Duplication for the dilogarithm**: `Li_2(x²) = 2 (Li_2(x) + Li_2(-x))` for `|x| ≤ 1`. -/
theorem polylogReal_two_sq {x : ℝ} (hx : |x| ≤ 1) :
    polylogReal 2 (x ^ 2) = 2 * (polylogReal 2 x + polylogReal 2 (-x)) := by
  have h := polylogReal_dup (s := 2) le_rfl hx
  linarith

/-! ## 4. Bailey's series of degree `s` -/

/-- Block `j` of Bailey's series `P(s, β, N, a)` for a real base `β` and real coefficients:
`β^(-j) ∑_{i=1}^{N} a_i / (N j + i)^s`; `a i` (`i : Fin N`) is `a_(i+1)`. -/
noncomputable def baileyBlockDegReal (s : ℕ) (β : ℝ) (N : ℕ) (a : Fin N → ℝ) (j : ℕ) : ℝ :=
  ∑ i : Fin N, a i / β ^ j / ((N * j + i + 1 : ℕ) : ℝ) ^ s

/-- Block `j` of Bailey's series `P(s, b^B, N, a)` for a natural `b` and a rational vector:
`b^(-B j) ∑_{i=1}^{N} a_i / (N j + i)^s`. For `s = 1` this is the block of the degree-1
files of the project (`BaseB.baileyBlock`). -/
noncomputable def baileyBlockDeg (s b B N : ℕ) (a : Fin N → ℚ) (j : ℕ) : ℝ :=
  ∑ i : Fin N, (a i : ℝ) / (b : ℝ) ^ (B * j) / ((N * j + i + 1 : ℕ) : ℝ) ^ s

/-- Bailey's series `P(s, b^B, N, a)` converges to `x`. -/
def HasBaileyValueDeg (s b B N : ℕ) (a : Fin N → ℚ) (x : ℝ) : Prop :=
  HasSum (baileyBlockDeg s b B N a) x

/-- A formula of degree `s`: `x = c · P(s, b^B, N, a)`. The series converges, and `c` times
its sum is `x`. A base printed as a number (`16`, `64`) is written with `B = 1`; a base
printed as a power (`2^12`, `3^6`) with that exponent. -/
def BaileyFormulaDeg (x c : ℝ) (s b B N : ℕ) (a : Fin N → ℚ) : Prop :=
  ∃ S : ℝ, HasBaileyValueDeg s b B N a S ∧ x = c * S

theorem HasBaileyValueDeg.formula {s b B N : ℕ} {a : Fin N → ℚ} {S : ℝ}
    (h : HasBaileyValueDeg s b B N a S) {x c : ℝ} (e : x = c * S) :
    BaileyFormulaDeg x c s b B N a :=
  ⟨S, h, e⟩

/-- A formula as one convergent series: `∑_j c · (block j) = x`. -/
theorem BaileyFormulaDeg.hasSum {x c : ℝ} {s b B N : ℕ} {a : Fin N → ℚ}
    (h : BaileyFormulaDeg x c s b B N a) :
    HasSum (fun j => c * baileyBlockDeg s b B N a j) x := by
  obtain ⟨S, hS, rfl⟩ := h
  exact HasSum.mul_left c hS

/-- The block for the base `b^B` and a rational vector is the block with a real base. -/
theorem baileyBlockDeg_eq_real (s b B N : ℕ) (a : Fin N → ℚ) :
    baileyBlockDeg s b B N a = baileyBlockDegReal s ((b : ℝ) ^ B) N fun i => (a i : ℝ) := by
  funext j
  simp only [baileyBlockDeg, baileyBlockDegReal, ← pow_mul]

/-- The base `a^j` with the exponent `B` is the base `a` with the exponent `j B`. -/
theorem baileyBlockDeg_pow (s a j B N : ℕ) (c : Fin N → ℚ) :
    baileyBlockDeg s (a ^ j) B N c = baileyBlockDeg s a (j * B) N c := by
  funext k
  simp only [baileyBlockDeg, Nat.cast_pow, ← pow_mul, mul_assoc]

/-- The base `a^j` with the exponent `B` is the base `a` with the exponent `j B`. -/
theorem HasBaileyValueDeg.of_pow {s a j B N : ℕ} {c : Fin N → ℚ} {x : ℝ}
    (h : HasBaileyValueDeg s a (j * B) N c x) : HasBaileyValueDeg s (a ^ j) B N c x := by
  rw [HasBaileyValueDeg, baileyBlockDeg_pow]
  exact h

/-! ## 5. Regrouping -/

/-- A convergent series `∑_{m ≥ 1} h(m)` (with `h(0) = 0`), summed in blocks of `N`
consecutive terms: block `j` consists of the terms `N j + 1, …, N j + N`. -/
theorem hasSum_block_sums {N : ℕ} (hN : 0 < N) {h : ℕ → ℝ} (h0 : h 0 = 0) {S : ℝ}
    (hS : HasSum h S) : HasSum (fun j : ℕ => ∑ i : Fin N, h (N * j + i + 1)) S := by
  have : NeZero N := ⟨hN.ne'⟩
  have h1 : HasSum (fun m : ℕ => h (m + 1)) S := (hasSum_succ_iff h0).2 hS
  have h2 : HasSum ((fun m : ℕ => h (m + 1)) ∘ (Nat.divModEquiv N).symm) S :=
    (Equiv.hasSum_iff (Nat.divModEquiv N).symm).2 h1
  refine h2.prod_fiberwise fun j => ?_
  have e : (∑ i : Fin N, h (N * j + i + 1)) =
      ∑ i : Fin N, ((fun m : ℕ => h (m + 1)) ∘ (Nat.divModEquiv N).symm) (j, i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    change h (N * j + i + 1) = h (j * N + i + 1)
    rw [mul_comm]
  rw [e]
  exact hasSum_fintype _

/-- A sequence with `u(m + N) = u(m) / β` satisfies `u(m + N j) = u(m) / β^j`. -/
theorem quasiperiodic_add_mul {N : ℕ} {u : ℕ → ℝ} {β : ℝ} (hu : ∀ m, u (m + N) = u m / β)
    (m j : ℕ) : u (m + N * j) = u m / β ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [Nat.mul_succ, ← add_assoc, hu, ih, pow_succ, div_div]

/-- **Regrouping.** If `u(m + N) = u(m) / β` for every `m` and `∑_{m ≥ 1} u(m) / m^s = S`
(`s ≥ 1`), then `P(s, β, N, (u(1), …, u(N))) = S`: block `j` is the sum of the terms
`N j + 1, …, N j + N`. -/
theorem hasSum_baileyBlockDegReal_of_quasiperiodic {s N : ℕ} (hs : s ≠ 0) (hN : 0 < N)
    {u : ℕ → ℝ} {β : ℝ} (hu : ∀ m, u (m + N) = u m / β) {S : ℝ}
    (h : HasSum (fun m : ℕ => u m / (m : ℝ) ^ s) S) :
    HasSum (baileyBlockDegReal s β N fun i => u ((i : ℕ) + 1)) S := by
  have h' := hasSum_block_sums hN (h := fun m : ℕ => u m / (m : ℝ) ^ s) (by simp [hs]) h
  refine h'.congr_fun fun j => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  have e1 : N * j + (i : ℕ) + 1 = (i : ℕ) + 1 + N * j := by ring
  have e2 : u (N * j + (i : ℕ) + 1) = u ((i : ℕ) + 1) / β ^ j := by
    rw [e1, quasiperiodic_add_mul hu]
  rw [e2]

/-- **Regrouping, periodic pattern.** For a pattern `c` of period `N` and a real `x` with
`x^N β = 1`, the series `∑_{m ≥ 1} c(m) x^m / m^s` is `P(s, β, N, a)` with `a_i = c(i) x^i`
(`1 ≤ i ≤ N`). In Bailey's notation `x = β^(-1/N)` and `c(i) = a_i β^(i/N)`. -/
theorem hasSum_baileyBlockDegReal_of_periodic {s N : ℕ} (hs : s ≠ 0) (hN : 0 < N)
    {c : ℕ → ℝ} (hc : ∀ m, c (m + N) = c m) {x β : ℝ} (hx : x ^ N * β = 1) {S : ℝ}
    (h : HasSum (fun m : ℕ => c m * x ^ m / (m : ℝ) ^ s) S) :
    HasSum (baileyBlockDegReal s β N fun i => c ((i : ℕ) + 1) * x ^ ((i : ℕ) + 1)) S := by
  have hβ0 : β ≠ 0 := fun h0 => by simp [h0] at hx
  have hu : ∀ m : ℕ, c (m + N) * x ^ (m + N) = c m * x ^ m / β := by
    intro m
    rw [hc, pow_add, eq_div_iff hβ0]
    linear_combination (c m * x ^ m) * hx
  exact hasSum_baileyBlockDegReal_of_quasiperiodic (u := fun m => c m * x ^ m) hs hN hu h

/-- **Regrouping, base `b^B` and a rational vector.** If `u(m + N) = u(m) / b^B` for every
`m`, `u(i) = a_i` for `1 ≤ i ≤ N`, and `∑_{m ≥ 1} u(m) / m^s = S`, then
`P(s, b^B, N, a) = S`. -/
theorem hasBaileyValueDeg_of_quasiperiodic {s b B N : ℕ} (hs : s ≠ 0) (hN : 0 < N)
    {a : Fin N → ℚ} {u : ℕ → ℝ} (hu : ∀ m, u (m + N) = u m / (b : ℝ) ^ B)
    (ha : ∀ i : Fin N, u ((i : ℕ) + 1) = (a i : ℝ)) {S : ℝ}
    (h : HasSum (fun m : ℕ => u m / (m : ℝ) ^ s) S) : HasBaileyValueDeg s b B N a S := by
  have h' := hasSum_baileyBlockDegReal_of_quasiperiodic hs hN hu h
  have e : (fun i : Fin N => u ((i : ℕ) + 1)) = fun i => (a i : ℝ) := funext ha
  rw [e] at h'
  rw [HasBaileyValueDeg, baileyBlockDeg_eq_real]
  exact h'

end Polylog

end PiFormula
