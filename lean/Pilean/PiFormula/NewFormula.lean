module

public import Pilean.PiFormula.TheoremBSpeed

/-!
# The new formula (Part III of pi_formula_theorem.md): its series

The formula of pi_formula_120.json,

    π/4 = ∑_{k ≥ 1} ρ(k) 2^(-⌊k/2⌋) / k,   ρ(k) = numerators[k mod 120] / 2,

is the one the native engine sums (`piwindow --formula new`). `PiFormula.new_formula` only
checks its *value*; this file proves the *series* (`new_formula_series`).

The proof uses the decomposition of decompose_formula.py, into the orbits of Part II:

    -2 ARG(O_6) + (ARG(O_10) - ARG(O_2)) + 2 (LOG(O_6) - 2 LOG(O_1))
      - 2 (LOG(O_8a) - 2 LOG(O_1)) + (LOG(O_24) - LOG(O_8b) - 2 LOG(O_1)),

with `ARG(O) = γ(O)`, `LOG(O) = ∑_{r ∈ O} log |1 - r/t|`, `O_1, O_2, O_6, O_10` the orbits
`orbit (P 0), orbit (Q 0), orbit (Q 1), orbit (Q 2)`, and `O_8a = selfOrb 0 false`
(`r² = i`), `O_8b = selfOrb 0 true` (`r² = -i`), `O_24 = selfOrb 1 true`.

* The value: `γ(O_6) = 0`, `γ(O_10) - γ(O_2) = π/4` (Part II), and the three `LOG`
  combinations vanish, from `LOG(O) = log |z_O| - |O| log |t|` with `|z_O| = 1, 1, 1, 3, 3`
  for `O_1, O_6, O_8a, O_8b, O_24` (`LOG_eq`, `norm_zO_*`).
* The terms: each series term is `-Im` or `-Re` of `p_k(O) t^(-k) / k`, and
  `t^(-k) = U_k / (2 · 2^⌊k/2⌋)` with `U_k ∈ ℤ[i]` of period 8. So `2 · 2^⌊k/2⌋ k` times the
  `k`-th term is an integer `N(k)`, computed in `ℤ[i]` (`NZ`), of period 120, and the 120
  values `N(k) = numerators[k]` are checked by `decide` (`NZ_eq_rhoNum`).
-/

@[expose] public section

open Polynomial Complex ComplexConjugate

namespace PiFormula

/-! ## 1. The `LOG` series -/

/-- `log |1 - r/t|`. -/
noncomputable def lfun (r : ℂ) : ℝ := (Complex.log (1 - r / tC)).re

/-- `LOG(O) = ∑_{r ∈ O} log |1 - r/t|`. -/
noncomputable def LOG (S : Multiset ℂ) : ℝ := (S.map lfun).sum

/-- The `k`-th term of the series of `LOG(O)`. -/
noncomputable def tauL (S : Multiset ℂ) (k : ℕ) : ℝ := -((psum S k * tC⁻¹ ^ k).re / k)

theorem hasSum_lfun {r : ℂ} (hr : ‖r‖ = 1) :
    HasSum (fun k : ℕ => -((r ^ k * tC⁻¹ ^ k).re / k)) (lfun r) := by
  have h := Complex.reCLM.hasSum (hasSum_taylorSeries_neg_log (norm_div_tC_lt hr))
  simp only [Complex.reCLM_apply, Complex.neg_re] at h
  have h2 := h.neg
  rw [neg_neg] at h2
  have e : lfun r = (Complex.log (1 - r / tC)).re := rfl
  rw [e]
  convert h2 using 2 with k
  rw [div_pow, div_eq_mul_inv (r ^ k), ← inv_pow, Complex.div_natCast_re]

theorem hasSum_LOG {S : Multiset ℂ} (hS : ∀ r ∈ S, ‖r‖ = 1) : HasSum (tauL S) (LOG S) := by
  induction S using Multiset.induction_on with
  | empty =>
    have : tauL 0 = fun _ => 0 := by funext k; simp [tauL, psum]
    rw [this]
    simp [LOG]
  | cons r S ih =>
    have hr := hS r (Multiset.mem_cons_self r S)
    have hS' : ∀ x ∈ S, ‖x‖ = 1 := fun x hx => hS x (Multiset.mem_cons_of_mem hx)
    have := (hasSum_lfun hr).add (ih hS')
    convert this using 1
    · funext k
      simp only [tauL, psum, Multiset.map_cons, Multiset.sum_cons, add_mul, Complex.add_re]
      ring
    · simp [LOG]

theorem lfun_eq {r : ℂ} (hr : ‖r‖ = 1) : lfun r = Real.log ‖tC - r‖ - Real.log ‖tC‖ := by
  rw [lfun, Complex.log_re, show 1 - r / tC = (tC - r) / tC by rw [sub_div, div_self tC_ne_zero],
    norm_div, Real.log_div (norm_ne_zero_iff.2 (tC_sub_ne_zero hr)) (norm_ne_zero_iff.2 tC_ne_zero)]

/-- `LOG(O) = log |z_O| - |O| log |t|`. -/
theorem LOG_eq {S : Multiset ℂ} (hS : ∀ r ∈ S, ‖r‖ = 1) :
    LOG S = Real.log ‖zO S‖ - Multiset.card S * Real.log ‖tC‖ := by
  induction S using Multiset.induction_on with
  | empty => simp [LOG, zO]
  | cons r S ih =>
    have hr := hS r (Multiset.mem_cons_self r S)
    have hS' : ∀ x ∈ S, ‖x‖ = 1 := fun x hx => hS x (Multiset.mem_cons_of_mem hx)
    have e1 : LOG (r ::ₘ S) = lfun r + LOG S := by simp [LOG]
    have e2 : zO (r ::ₘ S) = (tC - r) * zO S := by simp [zO]
    rw [e1, e2, norm_mul, Real.log_mul (norm_ne_zero_iff.2 (tC_sub_ne_zero hr))
      (norm_ne_zero_iff.2 (zO_ne_zero hS')), lfun_eq hr, ih hS', Multiset.card_cons]
    push_cast
    ring

/-! ## 2. The orbits of the formula -/

/-- `O_1`, `O_2`, `O_6`, `O_10`, `O_8a`, `O_8b`, `O_24`. -/
noncomputable abbrev O1 : Multiset ℂ := orbit (.P 0)
noncomputable abbrev O2 : Multiset ℂ := orbit (.Q 0)
noncomputable abbrev O6 : Multiset ℂ := orbit (.Q 1)
noncomputable abbrev O10 : Multiset ℂ := orbit (.Q 2)
noncomputable abbrev O8a : Multiset ℂ := selfOrb 0 false
noncomputable abbrev O8b : Multiset ℂ := selfOrb 0 true
noncomputable abbrev O24 : Multiset ℂ := selfOrb 1 true

theorem norm_selfOrb {k : ℕ} {b : Bool} {r : ℂ} (hr : r ∈ selfOrb k b) : ‖r‖ = 1 :=
  norm_of_mem_roots_cycPoly (by omega) (norm_eq_one_of_pow_four (kappaS_pow_four b))
    (by norm_num) hr

theorem tC_sq : tC ^ 2 = 2 * I := by
  unfold tC
  linear_combination Complex.I_sq

/-- `|z_O| = |Φ_m(κ t^N)|`. -/
theorem norm_zO_cycPoly {m N : ℕ} {κ : ℂ} (hκ : ‖κ‖ = 1) (hN : N ≠ 0) :
    ‖zO (cycPoly m N κ).roots‖ = ‖(cyclotomic m ℂ).eval (κ * tC ^ N)‖ := by
  have hκ0 : κ ≠ 0 := by intro h; rw [h, norm_zero] at hκ; exact zero_ne_one hκ
  have := congrArg norm (zO_cycPoly (m := m) hκ0 hN)
  rwa [norm_mul, norm_pow, hκ, one_pow, one_mul] at this

theorem norm_I_eq_one : ‖(I : ℂ)‖ = 1 := Complex.norm_I

theorem norm_negI : ‖(-I : ℂ)‖ = 1 := by rw [norm_neg, Complex.norm_I]

theorem norm_zO_O1 : ‖zO O1‖ = 1 := by
  rw [O1, orbit, norm_zO_cycPoly (by simp [kappa]) (by simp [Npow])]
  simp only [mOf, kappa, Npow, show 2 * 0 + 1 = 1 from rfl, cyclotomic_one, eval_sub, eval_X,
    eval_one, one_mul, pow_one]
  rw [show tC - 1 = I by unfold tC; ring, Complex.norm_I]

theorem norm_zO_O6 : ‖zO O6‖ = 1 := by
  rw [O6, orbit, norm_zO_cycPoly (by simp [kappa]) (by simp [Npow])]
  simp only [mOf, kappa, Npow, show 2 * 1 + 1 = 3 from rfl, cyclotomic_three, eval_add, eval_pow,
    eval_X, eval_one, pow_one]
  rw [show (-1 * tC) ^ 2 + -1 * tC + 1 = I by
    rw [show (-1 * tC) ^ 2 = tC ^ 2 by ring, tC_sq]; unfold tC; ring, Complex.norm_I]

theorem norm_zO_O8a : ‖zO O8a‖ = 1 := by
  rw [O8a, selfOrb, norm_zO_cycPoly (by simp [kappaS]) (by norm_num)]
  simp only [kappaS, Bool.false_eq_true, ↓reduceIte, show 2 * 0 + 1 = 1 from rfl, cyclotomic_one,
    eval_sub, eval_X, eval_one, tC_sq]
  rw [show -I * (2 * I) - 1 = 1 by linear_combination (-2 : ℂ) * Complex.I_sq, norm_one]

theorem norm_zO_O8b : ‖zO O8b‖ = 3 := by
  rw [O8b, selfOrb, norm_zO_cycPoly (by simp [kappaS]) (by norm_num)]
  simp only [kappaS, ↓reduceIte, show 2 * 0 + 1 = 1 from rfl, cyclotomic_one, eval_sub, eval_X,
    eval_one, tC_sq]
  rw [show I * (2 * I) - 1 = -3 by linear_combination (2 : ℂ) * Complex.I_sq, norm_neg]
  simp

theorem norm_zO_O24 : ‖zO O24‖ = 3 := by
  rw [O24, selfOrb, norm_zO_cycPoly (by simp [kappaS]) (by norm_num)]
  simp only [kappaS, ↓reduceIte, show 2 * 1 + 1 = 3 from rfl, cyclotomic_three, eval_add,
    eval_pow, eval_X, eval_one, tC_sq]
  rw [show (I * (2 * I)) ^ 2 + I * (2 * I) + 1 = 3 by
    linear_combination (4 * I ^ 2 - 4 + 2 : ℂ) * Complex.I_sq]
  simp

theorem card_O1 : Multiset.card O1 = 1 := by rw [O1, card_orbit]; simp [mOf, Npow]

theorem card_O6 : Multiset.card O6 = 2 := by
  rw [O6, card_orbit, show mOf (.Q 1) = 3 from rfl, totient_three]; rfl

theorem card_selfOrb (k : ℕ) (b : Bool) :
    Multiset.card (selfOrb k b) = (2 * k + 1).totient * 2 :=
  card_roots_cycPoly (by cases b <;> simp [kappaS])

/-- The three `LOG` relations of the formula: `LOG(O_6) - 2 LOG(O_1) = 0`,
`LOG(O_8a) - 2 LOG(O_1) = 0`, `LOG(O_24) - LOG(O_8b) - 2 LOG(O_1) = 0`. -/
theorem LOG_relations :
    LOG O6 - 2 * LOG O1 = 0 ∧ LOG O8a - 2 * LOG O1 = 0 ∧
      LOG O24 - LOG O8b - 2 * LOG O1 = 0 := by
  have h1 := LOG_eq (S := O1) fun r hr => norm_of_mem_orbit hr
  have h6 := LOG_eq (S := O6) fun r hr => norm_of_mem_orbit hr
  have h8a := LOG_eq (S := O8a) fun r hr => norm_selfOrb hr
  have h8b := LOG_eq (S := O8b) fun r hr => norm_selfOrb hr
  have h24 := LOG_eq (S := O24) fun r hr => norm_selfOrb hr
  rw [norm_zO_O1, card_O1] at h1
  rw [norm_zO_O6, card_O6] at h6
  rw [norm_zO_O8a, card_selfOrb] at h8a
  rw [norm_zO_O8b, card_selfOrb] at h8b
  rw [norm_zO_O24, card_selfOrb, show 2 * 1 + 1 = 3 from rfl, totient_three] at h24
  simp only [show 2 * 0 + 1 = 1 from rfl, Nat.totient_one, Real.log_one] at h1 h6 h8a h8b h24
  push_cast at h1 h6 h8a h8b h24
  refine ⟨by rw [h6, h1]; ring, by rw [h8a, h1]; ring, by rw [h24, h8b, h1]; ring⟩

/-! ## 3. Power sums of the self-paired orbits -/

/-- `∑_{r^n = c} r^k = n c^(k/n)` if `n ∣ k`, else `0`. -/
theorem sum_nthRoots_pow {n : ℕ} (hn : 0 < n) {c : ℂ} (hc : c ≠ 0) (k : ℕ) :
    ((nthRoots n c).map (· ^ k)).sum = if n ∣ k then (n : ℂ) * c ^ (k / n) else 0 := by
  have hζ := Complex.isPrimitiveRoot_exp n hn.ne'
  set ζ := Complex.exp (2 * Real.pi * I / n) with hζdef
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hn.ne'
  have hnd : (nthRoots n c).Nodup :=
    nodup_roots (separable_X_pow_sub_C c (by exact_mod_cast hn.ne') hc)
  have hcard : Multiset.card (nthRoots n c) = n := by
    rw [nthRoots, IsAlgClosed.card_roots_eq_natDegree, natDegree_X_pow_sub_C]
  split_ifs with hdvd
  · obtain ⟨j, rfl⟩ := hdvd
    have : ∀ r ∈ nthRoots n c, r ^ (n * j) = c ^ j := fun r hr => by
      rw [pow_mul, (mem_nthRoots hn).1 hr]
    rw [Multiset.map_congr rfl this, Multiset.map_const', Multiset.sum_replicate, hcard,
      nsmul_eq_mul, Nat.mul_div_cancel_left _ hn]
  · have hζk : ζ ^ k ≠ 1 := fun h => hdvd ((hζ.pow_eq_one_iff_dvd k).1 h)
    have hrot : (nthRoots n c).map (ζ * ·) = nthRoots n c := by
      rw [Multiset.Nodup.ext (hnd.map (mul_right_injective₀ hζ0)) hnd]
      intro x
      rw [Multiset.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [mem_nthRoots hn] at hy ⊢
        rw [mul_pow, hζ.pow_eq_one, hy, one_mul]
      · intro hx
        refine ⟨ζ⁻¹ * x, ?_, by field_simp⟩
        rw [mem_nthRoots hn] at hx ⊢
        rw [mul_pow, inv_pow, hζ.pow_eq_one, hx, inv_one, one_mul]
    set S := ((nthRoots n c).map (· ^ k)).sum with hS
    have : ζ ^ k * S = S := by
      conv_rhs => rw [hS, ← hrot]
      rw [hS, Multiset.map_map, ← Multiset.sum_map_mul_left]
      congr 1
      exact Multiset.map_congr rfl fun r _ => by simp [mul_pow]
    have h2 : (ζ ^ k - 1) * S = 0 := by linear_combination this
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hζk)

theorem CI_sq : (C I * C I : ℂ[X]) = -1 := by
  rw [← C_mul, Complex.I_mul_I, C_neg, C_1]

theorem O8a_eq : O8a = nthRoots 2 I := by
  simp only [O8a, selfOrb, cycPoly, kappaS, Bool.false_eq_true, ↓reduceIte,
    show 2 * 0 + 1 = 1 from rfl, cyclotomic_one, sub_comp, X_comp, one_comp]
  rw [show (C (-I) * X ^ 2 - 1 : ℂ[X]) = C (-I) * (X ^ 2 - C I) by
      rw [C_neg]; linear_combination (-1 : ℂ[X]) * CI_sq,
    roots_C_mul _ (neg_ne_zero.2 Complex.I_ne_zero)]
  rfl

theorem O8b_eq : O8b = nthRoots 2 (-I) := by
  simp only [O8b, selfOrb, cycPoly, kappaS, ↓reduceIte, show 2 * 0 + 1 = 1 from rfl,
    cyclotomic_one, sub_comp, X_comp, one_comp]
  rw [show (C I * X ^ 2 - 1 : ℂ[X]) = C I * (X ^ 2 - C (-I)) by
      rw [C_neg]; linear_combination (-1 : ℂ[X]) * CI_sq,
    roots_C_mul _ Complex.I_ne_zero]
  rfl

/-- `X^6 - i = (X² + i)(X⁴ - i X² - 1)`, so the roots of `X^6 = i` are `O_8b` and `O_24`. -/
theorem nthRoots_six_I : nthRoots 6 I = O8b + O24 := by
  rw [O8b_eq]
  simp only [O24, selfOrb, cycPoly, kappaS, ↓reduceIte, show 2 * 1 + 1 = 3 from rfl,
    cyclotomic_three, add_comp, pow_comp, X_comp, one_comp]
  have hprod : (X ^ 6 - C I : ℂ[X]) =
      (X ^ 2 - C (-I)) * -((C I * X ^ 2) ^ 2 + C I * X ^ 2 + 1) := by
    rw [C_neg]
    linear_combination (X ^ 6 + C I * X ^ 4 + X ^ 2) * CI_sq
  have hne : (X ^ 6 - C I : ℂ[X]) ≠ 0 := X_pow_sub_C_ne_zero (by norm_num) I
  rw [nthRoots, hprod, roots_mul (hprod ▸ hne), roots_neg]
  rfl

theorem psum_O8a (k : ℕ) : psum O8a k = if 2 ∣ k then 2 * I ^ (k / 2) else 0 := by
  rw [psum, O8a_eq, sum_nthRoots_pow (by norm_num) Complex.I_ne_zero]
  norm_num

theorem psum_O8b (k : ℕ) : psum O8b k = if 2 ∣ k then 2 * (-I) ^ (k / 2) else 0 := by
  rw [psum, O8b_eq, sum_nthRoots_pow (by norm_num) (neg_ne_zero.2 Complex.I_ne_zero)]
  norm_num

theorem psum_O24 (k : ℕ) :
    psum O24 k = (if 6 ∣ k then 6 * I ^ (k / 6) else 0) - psum O8b k := by
  have h := congrArg (fun S => (S.map (· ^ k)).sum) nthRoots_six_I
  simp only [Multiset.map_add, Multiset.sum_add] at h
  rw [sum_nthRoots_pow (by norm_num) Complex.I_ne_zero] at h
  rw [psum, psum]
  push_cast at h ⊢
  linear_combination -h

/-! ## 4. The integer model -/

/-- The power sums `p_k(O)` of the seven orbits, in `ℤ[i]`. -/
def P2Z (k : ℕ) : GaussianInt := (if 2 ∣ k then 2 else 0) - 1

def P6Z (k : ℕ) : GaussianInt :=
  (if 6 ∣ k then 6 else 0) - (if 3 ∣ k then 3 else 0) - (if 2 ∣ k then 2 else 0) + 1

def P10Z (k : ℕ) : GaussianInt :=
  (if 10 ∣ k then 10 else 0) - (if 5 ∣ k then 5 else 0) - (if 2 ∣ k then 2 else 0) + 1

def P8aZ (k : ℕ) : GaussianInt := if 2 ∣ k then 2 * gI ^ (k / 2) else 0

def P8bZ (k : ℕ) : GaussianInt := if 2 ∣ k then 2 * (-gI) ^ (k / 2) else 0

def P24Z (k : ℕ) : GaussianInt := (if 6 ∣ k then 6 * gI ^ (k / 6) else 0) - P8bZ k

/-- `U_k = 2 · 2^⌊k/2⌋ t^(-k) ∈ ℤ[i]`. -/
def UZ (k : ℕ) : GaussianInt := (-gI) ^ (k / 2) * (if 2 ∣ k then 2 else ⟨1, -1⟩)

/-- `N(k) = 2 · 2^⌊k/2⌋ k` times the `k`-th term of the decomposition. -/
def NZ (k : ℕ) : ℤ :=
  2 * (P6Z k * UZ k).im - (P10Z k * UZ k).im + (P2Z k * UZ k).im - 2 * (P6Z k * UZ k).re +
    2 * (P8aZ k * UZ k).re - (P24Z k * UZ k).re + (P8bZ k * UZ k).re + 2 * (UZ k).re

/-- The numerators of pi_formula_120.json (`ρ(k) = numerators[k mod 120] / 2`). -/
def rhoNum : List ℤ :=
  [0, 0, 0, 0, 8, 5, 24, 0, 24, 12, 10, 0, 8, 0, 0, 5, 24, 0, 0, 0, 8, -12, 0, 0, 0, -5, 0,
   0, 8, 0, 14, 0, 24, 12, 0, -5, 8, 0, 0, 0, 24, 0, 0, 0, 8, -7, 0, 0, 0, 0, 10, 0, 8, 0,
   24, 5, 24, 12, 0, 0, 8, 0, 0, 0, 24, -5, 0, 0, 8, -12, -10, 0, 0, 0, 0, -5, 8, 0, 24, 0,
   24, 12, 0, 0, 8, 5, 0, 0, 24, 0, 10, 0, 8, -12, 0, 5, 0, 0, 0, 0, 8, 0, 24, 0, 24, 7, 0,
   0, 8, 0, -10, 0, 24, 0, 0, -5, 8, -12, 0, 0]

/-- `ρ(k)`, the coefficient of the new formula. -/
def rhoNew (k : ℕ) : ℚ := (rhoNum.getD (k % 120) 0 : ℚ) / 2

/-- **The 120 checks.** -/
theorem NZ_eq_rhoNum : ∀ k < 120, NZ k = rhoNum.getD k 0 := by decide

theorem gI_pow_four : gI ^ 4 = 1 := by decide

theorem negI_pow_four : (-gI) ^ 4 = 1 := by decide

theorem pow_add_four_mul {x : GaussianInt} (hx : x ^ 4 = 1) (a b : ℕ) :
    x ^ (a + 4 * b) = x ^ a := by
  rw [pow_add, pow_mul, hx, one_pow, mul_one]

theorem NZ_periodic (k : ℕ) : NZ (k + 120) = NZ k := by
  have h2 : 2 ∣ k + 120 ↔ 2 ∣ k := by omega
  have h3 : 3 ∣ k + 120 ↔ 3 ∣ k := by omega
  have h5 : 5 ∣ k + 120 ↔ 5 ∣ k := by omega
  have h6 : 6 ∣ k + 120 ↔ 6 ∣ k := by omega
  have h10 : 10 ∣ k + 120 ↔ 10 ∣ k := by omega
  have e2 : (k + 120) / 2 = k / 2 + 4 * 15 := by omega
  have e6 : (k + 120) / 6 = k / 6 + 4 * 5 := by omega
  simp only [NZ, P2Z, P6Z, P10Z, P8aZ, P8bZ, P24Z, UZ, h2, h3, h5, h6, h10, e2, e6,
    pow_add_four_mul gI_pow_four, pow_add_four_mul negI_pow_four]

theorem NZ_mod (k : ℕ) : NZ k = NZ (k % 120) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k < 120
    · rw [Nat.mod_eq_of_lt hk]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 120 := ⟨k - 120, by omega⟩
      rw [NZ_periodic, ih j (by omega), show (j + 120) % 120 = j % 120 by omega]

theorem NZ_eq (k : ℕ) : (NZ k : ℚ) = 2 * rhoNew k := by
  rw [NZ_mod, NZ_eq_rhoNum _ (Nat.mod_lt k (by norm_num)), rhoNew]
  ring

/-! ## 5. From the model to the series terms -/

theorem gI_cast : ((gI : GaussianInt) : ℂ) = I := by simp [gI, GaussianInt.toComplex_def']

theorem tC_inv_sq : tC⁻¹ ^ 2 = -I / 2 := by
  rw [tC_inv]; linear_combination (1 / 4 : ℂ) * Complex.I_sq

/-- `t^(-k) = U_k / (2 · 2^⌊k/2⌋)`. -/
theorem tC_inv_pow_eq (k : ℕ) :
    tC⁻¹ ^ k = ((UZ k : GaussianInt) : ℂ) / ((2 * 2 ^ (k / 2) : ℝ) : ℂ) := by
  have h2 : (2 : ℂ) ^ (k / 2) ≠ 0 := pow_ne_zero _ two_ne_zero
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · have hj : 2 * j / 2 = j := by omega
    have hev : 2 ∣ 2 * j := dvd_mul_right 2 j
    simp only [UZ, hj, hev, ↓reduceIte]
    rw [pow_mul, tC_inv_sq, map_mul, map_pow, map_neg, gI_cast, map_ofNat]
    push_cast
    field_simp
    have key : ((-1 / 2 : ℂ)) ^ j * 2 ^ j = (-1) ^ j := by rw [← mul_pow]; norm_num
    linear_combination I ^ j * key
  · have hj : (2 * j + 1) / 2 = j := by omega
    have hodd : ¬ 2 ∣ 2 * j + 1 := by omega
    simp only [UZ, hj, hodd, ↓reduceIte]
    rw [pow_succ, pow_mul, tC_inv_sq, tC_inv, map_mul, map_pow, map_neg, gI_cast,
      GaussianInt.toComplex_def']
    push_cast
    field_simp
    have key : ((-1 / 2 : ℂ)) ^ j * 2 ^ j = (-1) ^ j := by rw [← mul_pow]; norm_num
    linear_combination (I ^ j - I * I ^ j) * key

theorem mul_tC_inv_pow_im (z : GaussianInt) (k : ℕ) :
    ((z : ℂ) * tC⁻¹ ^ k).im = ((z * UZ k).im : ℝ) / (2 * 2 ^ (k / 2)) := by
  rw [tC_inv_pow_eq, ← mul_div_assoc, ← GaussianInt.toComplex_mul, Complex.div_ofReal_im,
    GaussianInt.intCast_im]

theorem mul_tC_inv_pow_re (z : GaussianInt) (k : ℕ) :
    ((z : ℂ) * tC⁻¹ ^ k).re = ((z * UZ k).re : ℝ) / (2 * 2 ^ (k / 2)) := by
  rw [tC_inv_pow_eq, ← mul_div_assoc, ← GaussianInt.toComplex_mul, Complex.div_ofReal_re,
    GaussianInt.intCast_re]

theorem psum_O1Z (k : ℕ) : psum O1 k = ((1 : GaussianInt) : ℂ) := by
  rw [psum_O1, GaussianInt.toComplex_one]

theorem psum_O2Z (k : ℕ) : psum O2 k = ((P2Z k : GaussianInt) : ℂ) := by
  rw [psum_O2, c2, P2Z]
  split_ifs <;> norm_num [map_ofNat]

theorem psum_O6Z (k : ℕ) : psum O6 k = ((P6Z k : GaussianInt) : ℂ) := by
  rw [psum_O6, c6, P6Z]
  split_ifs <;> norm_num [map_ofNat]

theorem psum_O10Z (k : ℕ) : psum O10 k = ((P10Z k : GaussianInt) : ℂ) := by
  rw [psum_O10, c10, P10Z]
  split_ifs <;> norm_num [map_ofNat]

theorem psum_O8aZ (k : ℕ) : psum O8a k = ((P8aZ k : GaussianInt) : ℂ) := by
  rw [psum_O8a, P8aZ]
  split_ifs <;> simp [gI_cast, map_ofNat]

theorem psum_O8bZ (k : ℕ) : psum O8b k = ((P8bZ k : GaussianInt) : ℂ) := by
  rw [psum_O8b, P8bZ]
  split_ifs <;> simp [gI_cast, map_ofNat]

theorem psum_O24Z (k : ℕ) : psum O24 k = ((P24Z k : GaussianInt) : ℂ) := by
  rw [psum_O24, psum_O8bZ, P24Z, GaussianInt.toComplex_sub]
  congr 1
  split_ifs <;> simp [gI_cast, map_ofNat]

/-- The `k`-th term of the decomposition. -/
noncomputable def termNew (k : ℕ) : ℝ :=
  -2 * tau O6 k + (tau O10 k - tau O2 k) + 2 * (tauL O6 k - 2 * tauL O1 k) -
    2 * (tauL O8a k - 2 * tauL O1 k) + (tauL O24 k - tauL O8b k - 2 * tauL O1 k)

theorem termNew_eq (k : ℕ) : termNew k = (NZ k : ℝ) / (2 * 2 ^ (k / 2)) / k := by
  simp only [termNew, tau, tauL, psum_O1Z, psum_O2Z, psum_O6Z, psum_O10Z, psum_O8aZ, psum_O8bZ,
    psum_O24Z, mul_tC_inv_pow_im, mul_tC_inv_pow_re, NZ, one_mul]
  push_cast
  ring

/-! ## 6. The series of the new formula -/

theorem hasSum_termNew :
    HasSum termNew (-2 * gamma O6 + (gamma O10 - gamma O2) + 2 * (LOG O6 - 2 * LOG O1) -
      2 * (LOG O8a - 2 * LOG O1) + (LOG O24 - LOG O8b - 2 * LOG O1)) := by
  have g6 := hasSum_gamma (S := O6) fun r hr => norm_of_mem_orbit hr
  have g10 := hasSum_gamma (S := O10) fun r hr => norm_of_mem_orbit hr
  have g2 := hasSum_gamma (S := O2) fun r hr => norm_of_mem_orbit hr
  have l1 := hasSum_LOG (S := O1) fun r hr => norm_of_mem_orbit hr
  have l6 := hasSum_LOG (S := O6) fun r hr => norm_of_mem_orbit hr
  have l8a := hasSum_LOG (S := O8a) fun r hr => norm_selfOrb hr
  have l8b := hasSum_LOG (S := O8b) fun r hr => norm_selfOrb hr
  have l24 := hasSum_LOG (S := O24) fun r hr => norm_selfOrb hr
  exact ((((g6.mul_left (-2)).add (g10.sub g2)).add ((l6.sub (l1.mul_left 2)).mul_left 2)).sub
    ((l8a.sub (l1.mul_left 2)).mul_left 2)).add ((l24.sub l8b).sub (l1.mul_left 2))

/-- **The new formula, as a series.**
`π/4 = ∑_{k ≥ 0} ρ(k) / (2^⌊k/2⌋ k)` (the `k = 0` term is 0), with `ρ` of period 120 from
pi_formula_120.json. -/
theorem new_formula_series :
    HasSum (fun k : ℕ => (rhoNew k : ℝ) / 2 ^ (k / 2) / k) (Real.pi / 4) := by
  have hval : -2 * gamma O6 + (gamma O10 - gamma O2) + 2 * (LOG O6 - 2 * LOG O1) -
      2 * (LOG O8a - 2 * LOG O1) + (LOG O24 - LOG O8b - 2 * LOG O1) = Real.pi / 4 := by
    obtain ⟨h1, h2, h3⟩ := LOG_relations
    rw [h1, h2, h3, O6, O10, O2, gamma_orbit_Q1, gamma_orbit_Q2, gamma_orbit_Q0]
    ring
  rw [← hval]
  convert hasSum_termNew using 1
  funext k
  rw [termNew_eq]
  have h := NZ_eq k
  have hR : (NZ k : ℝ) = 2 * (rhoNew k : ℝ) := by exact_mod_cast h
  rw [hR]
  ring

end PiFormula
