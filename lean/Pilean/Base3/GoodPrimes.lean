module

public import Pilean.Base3.HasPrime
public import TauCeti.NumberTheory.PrimitivePrimeDivisors.Zsigmondy

/-!
# Base 3: every root of unity outside the six exceptional ones has a good prime

`goodPrimes3_of_halves`: `GoodPrimes3` holds, given one statement about the Aurifeuillian
factors of `3^(3E) + 1`:

`PrimitiveHalves3`: for every odd `E ≥ 3`, each of `3^E - 3^((E+1)/2) + 1` and
`3^E + 3^((E+1)/2) + 1` has a prime factor `p` with `ord_p(3) = 6E`.

This statement is proved in `Halves.lean` (`primitiveHalves3`), so `GoodPrimes3` holds with no
hypothesis (`goodPrimes3`, in the same file). It is kept as a hypothesis here only to
separate the two arguments.

The proof. Let `r` have order `M`, `g = gcd(M, 6)`, `E = M/g`, `c = r^E`, a root of unity of
order `g`. By `goodPrime_of_coset` it suffices to find a prime `p` with `ord_p(3) = n`, where
`n h = 2M` for some `h ∣ 8`, such that `p` divides the integer `|t^E - c|^2`:

| `g` | `c` | `E` | `|t^E - c|^2` | `n` | `h` |
|---|---|---|---|---|---|
| 1 | `1` | odd | `3^E + 1` | `2E` | 1 |
| 2 | `-1` | odd | `3^E + 1` | `2E` | 2 |
| 2 | `-1` | `2m`, `m` odd | `(3^m - 1)^2` | `m` | 8 |
| 2 | `-1` | `2m`, `m` even | `(3^m + 1)^2` | `2m` | 4 |
| 3 | `ω^u` | odd | an Aurifeuillian factor | `6E` | 1 |
| 6 | `-ω^u` | odd | an Aurifeuillian factor | `6E` | 2 |
| 6 | `-ω^u` | `2m`, `m` odd | `9^m + 3^m + 1` | `3m` | 8 |
| 6 | `-ω^u` | `2m`, `m` even | `9^m - 3^m + 1` | `6m` | 4 |

In the rows without Aurifeuillian factors the prime comes from Zsigmondy's theorem for base 3
(`TauCeti.exists_prime_orderOf_eq`) and elementary divisibility; `n < 3` happens only for
`r = ±1, ±i`. In the two Aurifeuillian rows with `E = 1` the number is 1 (for `r = ω`,
`-ω²`) or 7.
-/

@[expose] public section

open Complex Polynomial

namespace PiFormula

namespace Base3

/-- For every odd `E = 2k + 1 ≥ 3`, each of the two Aurifeuillian factors
`3^E ∓ 3^((E+1)/2) + 1` of `3^(3E) + 1` has a prime factor `p` with `ord_p(3) = 6E`.
Proved in `Halves.lean` (`primitiveHalves3`). -/
def PrimitiveHalves3 : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    (∃ p : ℕ, p.Prime ∧ orderOf (3 : ZMod p) = 6 * (2 * k + 1) ∧
      (p : ℤ) ∣ 3 ^ (2 * k + 1) - 3 ^ (k + 1) + 1) ∧
    (∃ p : ℕ, p.Prime ∧ orderOf (3 : ZMod p) = 6 * (2 * k + 1) ∧
      (p : ℤ) ∣ 3 ^ (2 * k + 1) + 3 ^ (k + 1) + 1)

/-! ## 1. Primes with a given order of 3 -/

theorem prime_facts_of_orderOf {p n : ℕ} (hp : p.Prime) (hn : 3 ≤ n)
    (h : orderOf (3 : ZMod p) = n) : 5 ≤ p ∧ n < p := by
  have := Fact.mk hp
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h0
    have h1 : (3 : ZMod p) ^ n = 1 := by rw [← h]; exact pow_orderOf_eq_one _
    rw [h0, zero_pow (by omega)] at h1
    exact zero_ne_one h1
  have hd := ZMod.orderOf_dvd_card_sub_one h3
  rw [h] at hd
  have h2 := hp.two_le
  have hle := Nat.le_of_dvd (by omega) hd
  have hlt : n < p := by omega
  refine ⟨?_, hlt⟩
  have h4 : p ≠ 4 := by
    rintro rfl
    exact absurd hp (by norm_num)
  omega

theorem not_dvd_of_orderOf {p n M h : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hlt : n < p)
    (hn0 : 0 < n) (h8 : h ∣ 8) (hn : n * h = 2 * M) : ¬ p ∣ M := by
  intro hpM
  have h1 : p ∣ n * h := by
    rw [hn]
    exact Dvd.dvd.mul_left hpM 2
  rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
  · exact absurd (Nat.le_of_dvd hn0 h2) (by omega)
  · have h3 : p ∣ 8 := h2.trans h8
    have h4 := Nat.le_of_dvd (by norm_num) h3
    interval_cases p <;> first | omega | exact absurd hp (by norm_num)

/-- The common end of every case. -/
theorem goodPrime_of_order {r : ℂ} (hr : IsOfFinOrder r) {E : ℕ} (hE : 0 < E)
    (hgE : Nat.gcd (orderOf r) 6 * E = orderOf r) {p n h : ℕ} (hp : p.Prime) (hn3 : 3 ≤ n)
    (hord : orderOf (3 : ZMod p) = n) (h8 : h ∣ 8) (hnh : n * h = 2 * orderOf r)
    (hQ : HasPrime p (t3 ^ E - r ^ E)) : HasGoodPrime3 r := by
  obtain ⟨hp5, hlt⟩ := prime_facts_of_orderOf hp hn3 hord
  exact goodPrime_of_coset hr hE hgE hp hp5
    (not_dvd_of_orderOf hp hp5 hlt (by omega) h8 hnh) h8 (by rw [hord]; exact hnh) hQ

theorem exists_prime_order_three {n : ℕ} (hn : 3 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ orderOf (3 : ZMod p) = n := by
  obtain ⟨p, hp, h⟩ := TauCeti.exists_prime_orderOf_eq (a := 3) le_rfl hn
  exact ⟨p, hp, by simpa using h⟩

/-- `3^E = -1` modulo a prime at which 3 has order `2E`. -/
theorem pow_eq_neg_one_of_orderOf {p : ℕ} [Fact p.Prime] {E : ℕ} (hE : 0 < E)
    (h : orderOf (3 : ZMod p) = 2 * E) : (3 : ZMod p) ^ E = -1 := by
  have h1 : ((3 : ZMod p) ^ E) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, ← h]
    exact pow_orderOf_eq_one _
  have h2 : (3 : ZMod p) ^ E ≠ 1 := by
    intro h0
    have hd := orderOf_dvd_of_pow_eq_one h0
    rw [h] at hd
    have := Nat.le_of_dvd hE hd
    omega
  have h3 : ((3 : ZMod p) ^ E - 1) * ((3 : ZMod p) ^ E + 1) = 0 := by linear_combination h1
  rcases mul_eq_zero.1 h3 with h4 | h4
  · exact absurd (sub_eq_zero.1 h4) h2
  · exact eq_neg_of_add_eq_zero_left h4

theorem dvd_of_cast_eq_zero {p : ℕ} {D : ℤ} (h : ((D : ℤ) : ZMod p) = 0) : (p : ℤ) ∣ D :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd D p).1 h

/-! ## 2. The numbers `|t^E + ω^u|^2` -/

theorem norm_sq_even_add (m u : ℕ) :
    ‖t3 ^ (2 * m) + w3 ^ u‖ ^ 2 =
      if u % 3 = 0 then ((-3 : ℝ) ^ m + 1) ^ 2 else ((-3 : ℝ) ^ m) ^ 2 - (-3 : ℝ) ^ m + 1 := by
  have h3 := sqrt3_mul_self
  rw [norm_sq_eq, t3_pow_even, w3_pow_mod u]
  have h : u % 3 < 3 := Nat.mod_lt _ (by norm_num)
  obtain ⟨x, hx⟩ : ∃ x, u % 3 = x := ⟨_, rfl⟩
  rw [hx] at h ⊢
  interval_cases x
  · simp only [pow_zero, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im, ↓reduceIte]
    ring
  · simp only [pow_one, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      w3, one_ne_zero, ↓reduceIte]
    linear_combination (1 / 4 : ℝ) * h3
  · rw [w3_sq]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      OfNat.ofNat_ne_zero, ↓reduceIte]
    linear_combination (1 / 4 : ℝ) * h3

theorem norm_sq_odd_add (m u : ℕ) :
    ‖t3 ^ (2 * m + 1) + w3 ^ u‖ ^ 2 =
      if u % 3 = 0 then 3 * ((-3 : ℝ) ^ m) ^ 2 + 1
      else if u % 3 = 1 then 3 * ((-3 : ℝ) ^ m) ^ 2 + 3 * (-3 : ℝ) ^ m + 1
      else 3 * ((-3 : ℝ) ^ m) ^ 2 - 3 * (-3 : ℝ) ^ m + 1 := by
  have h3 := sqrt3_mul_self
  rw [norm_sq_eq, t3_pow_odd, w3_pow_mod u]
  have h : u % 3 < 3 := Nat.mod_lt _ (by norm_num)
  obtain ⟨x, hx⟩ : ∃ x, u % 3 = x := ⟨_, rfl⟩
  rw [hx] at h ⊢
  interval_cases x
  · simp only [pow_zero, Complex.add_re, Complex.add_im, Complex.mul_I_re, Complex.mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im, ↓reduceIte]
    linear_combination ((-3 : ℝ) ^ m) ^ 2 * h3
  · simp only [pow_one, Complex.add_re, Complex.add_im, Complex.mul_I_re, Complex.mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im, w3, one_ne_zero, ↓reduceIte]
    linear_combination ((-3 : ℝ) ^ m + 1 / 2) ^ 2 * h3
  · rw [w3_sq]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_I_re, Complex.mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im, OfNat.ofNat_ne_zero, ↓reduceIte,
      show (2 : ℕ) ≠ 1 by norm_num]
    linear_combination ((-3 : ℝ) ^ m - 1 / 2) ^ 2 * h3

theorem neg_three_pow_sq (m : ℕ) : ((-3 : ℝ) ^ m) ^ 2 = ((3 : ℝ) ^ m) ^ 2 := by
  rcases neg_three_pow_cases m with h | h
  · rw [h]
  · rw [h, neg_sq]

theorem neg_three_pow_odd {m : ℕ} (hm : Odd m) : (-3 : ℝ) ^ m = -(3 : ℝ) ^ m := hm.neg_pow 3

theorem neg_three_pow_even {m : ℕ} (hm : Even m) : (-3 : ℝ) ^ m = (3 : ℝ) ^ m := hm.neg_pow 3

/-! ## 3. Prime ideals containing `t^E ∓ ω^u` -/

theorem hasPrime_sub {p : ℕ} (hp : p.Prime) (E u : ℕ) {D : ℤ} (hD : (p : ℤ) ∣ D)
    (hnorm : ((D : ℤ) : ℝ) = ‖t3 ^ E - w3 ^ u‖ ^ 2) : HasPrime p (t3 ^ E - w3 ^ u) := by
  let F : ℤ[X] := (X - X ^ 2) ^ E - X ^ u
  have hF : aeval w3 F = t3 ^ E - w3 ^ u := by simp [F, ← t3_eq]
  rw [← hF] at hnorm ⊢
  exact hasPrime_of_dvd_norm (by norm_num) isPrimitiveRoot_w3 hp F hD hnorm

theorem hasPrime_add {p : ℕ} (hp : p.Prime) (E u : ℕ) {D : ℤ} (hD : (p : ℤ) ∣ D)
    (hnorm : ((D : ℤ) : ℝ) = ‖t3 ^ E + w3 ^ u‖ ^ 2) : HasPrime p (t3 ^ E + w3 ^ u) := by
  let F : ℤ[X] := (X - X ^ 2) ^ E + X ^ u
  have hF : aeval w3 F = t3 ^ E + w3 ^ u := by simp [F, ← t3_eq]
  rw [← hF] at hnorm ⊢
  exact hasPrime_of_dvd_norm (by norm_num) isPrimitiveRoot_w3 hp F hD hnorm

theorem orderOf_three_zmod_seven : orderOf (3 : ZMod 7) = 6 :=
  (orderOf_eq_iff (by norm_num)).2 ⟨by decide, by decide⟩

/-! ## 4. The theorem -/

/-- **Good primes in base 3** (from `PrimitiveHalves3`). Every root of unity other than
`1, -1, i, -i, ω, -ω²` has a good prime. -/
theorem goodPrimes3_of_halves (hH : PrimitiveHalves3) : GoodPrimes3 := by
  intro r hr hr0
  obtain ⟨M, hMdef⟩ : ∃ M, orderOf r = M := ⟨_, rfl⟩
  have hM0 : 0 < M := hMdef ▸ hr.orderOf_pos
  obtain ⟨g, hgdef⟩ : ∃ g, Nat.gcd M 6 = g := ⟨_, rfl⟩
  have hg6 : g ∣ 6 := hgdef ▸ Nat.gcd_dvd_right M 6
  obtain ⟨E, hE⟩ : g ∣ M := hgdef ▸ Nat.gcd_dvd_left M 6
  have hE0 : 0 < E := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hg0 : 0 < g := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hgE : Nat.gcd (orderOf r) 6 * E = orderOf r := by rw [hMdef, hgdef, ← hE]
  have hordc : orderOf (r ^ E) = g := by
    rw [orderOf_pow' r hE0.ne', hMdef, hE, Nat.gcd_mul_left_left, Nat.mul_div_cancel _ hE0]
  -- if `E` is even then `g` is even
  have hEg : E % 2 = 0 → g % 2 = 0 := by
    intro he
    have h2 : 2 ∣ Nat.gcd M 6 :=
      Nat.dvd_gcd (hE ▸ Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero he) g) (by norm_num)
    rw [hgdef] at h2
    omega
  have hgle : g ≤ 6 := Nat.le_of_dvd (by norm_num) hg6
  have hg4 : g = 1 ∨ g = 2 ∨ g = 3 ∨ g = 6 := by
    interval_cases g <;> omega
  have h2M : 2 * orderOf r = 2 * (g * E) := by rw [hMdef, hE]
  rcases hg4 with rfl | rfl | rfl | rfl
  · -- `g = 1`: `c = 1`, `E` odd
    have hc : r ^ E = 1 := orderOf_eq_one_iff.1 hordc
    obtain ⟨m, hm⟩ : ∃ m, E = 2 * m + 1 := ⟨E / 2, by
      have : E % 2 ≠ 0 := fun h => by have := hEg h; omega
      omega⟩
    subst hm
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · exfalso
      apply hr0
      left
      simpa using hc
    obtain ⟨p, hp, hord⟩ := exists_prime_order_three (n := 2 * (2 * m + 1)) (by omega)
    have := Fact.mk hp
    refine goodPrime_of_order hr hE0 hgE hp (by omega) hord (h := 1) (by norm_num)
      (by rw [h2M]; ring) ?_
    rw [hc]
    have hD : (p : ℤ) ∣ 3 ^ (2 * m + 1) + 1 := by
      apply dvd_of_cast_eq_zero
      push_cast
      rw [pow_eq_neg_one_of_orderOf (by omega) hord]
      ring
    have h := hasPrime_sub hp (2 * m + 1) 0 hD (by
      rw [norm_sq_odd]
      simp only [Nat.zero_mod, ↓reduceIte]
      push_cast
      rw [neg_three_pow_sq]
      ring)
    simpa using h
  · -- `g = 2`: `c = -1`
    have hc : r ^ E = -1 := by
      have h2 : (r ^ E) ^ 2 = 1 := by rw [← hordc]; exact pow_orderOf_eq_one _
      have h1 : r ^ E ≠ 1 := by
        intro h1
        rw [orderOf_eq_one_iff.2 h1] at hordc
        omega
      have h3 : (r ^ E - 1) * (r ^ E + 1) = 0 := by linear_combination h2
      rcases mul_eq_zero.1 h3 with h4 | h4
      · exact absurd (sub_eq_zero.1 h4) h1
      · exact eq_neg_of_add_eq_zero_left h4
    rcases Nat.even_or_odd' E with ⟨m, rfl | rfl⟩
    · -- `E = 2m`
      have hm0 : 0 < m := by omega
      rcases Nat.even_or_odd m with hme | hmo
      · -- `m` even: `(3^m + 1)^2`, order `2m`
        have hm2 : 2 ≤ m := by
          obtain ⟨k, hk⟩ := hme
          omega
        obtain ⟨p, hp, hord⟩ := exists_prime_order_three (n := 2 * m) (by omega)
        have := Fact.mk hp
        refine goodPrime_of_order hr hE0 hgE hp (by omega) hord (h := 4) (by norm_num)
          (by rw [h2M]; ring) ?_
        rw [hc, sub_neg_eq_add]
        have hD : (p : ℤ) ∣ (3 ^ m + 1) ^ 2 := by
          apply dvd_of_cast_eq_zero
          push_cast
          rw [pow_eq_neg_one_of_orderOf hm0 hord]
          ring
        have h := hasPrime_add hp (2 * m) 0 hD (by
          rw [norm_sq_even_add]
          simp only [Nat.zero_mod, ↓reduceIte]
          push_cast
          rw [neg_three_pow_even hme])
        simpa using h
      · -- `m` odd: `(3^m - 1)^2`, order `m`
        rcases Nat.lt_or_ge m 3 with hlt | hge
        · -- `m = 1`: `r^2 = -1`, so `r = ±i`
          have hm1 : m = 1 := by
            obtain ⟨k, hk⟩ := hmo
            omega
          subst hm1
          exfalso
          apply hr0
          have h3 : (r - I) * (r + I) = 0 := by
            have h4 : r ^ 2 = -1 := by simpa using hc
            linear_combination h4 - Complex.I_sq
          rcases mul_eq_zero.1 h3 with h4 | h4
          · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.1 h4)))
          · exact Or.inr (Or.inr (Or.inr (Or.inl (eq_neg_of_add_eq_zero_left h4))))
        obtain ⟨p, hp, hord⟩ := exists_prime_order_three (n := m) hge
        have := Fact.mk hp
        refine goodPrime_of_order hr hE0 hgE hp hge hord (h := 8) (by norm_num)
          (by rw [h2M]; ring) ?_
        rw [hc, sub_neg_eq_add]
        have hD : (p : ℤ) ∣ (3 ^ m - 1) ^ 2 := by
          apply dvd_of_cast_eq_zero
          push_cast
          have h1 : (3 : ZMod p) ^ m = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
          rw [h1]
          ring
        have h := hasPrime_add hp (2 * m) 0 hD (by
          rw [norm_sq_even_add]
          simp only [Nat.zero_mod, ↓reduceIte]
          push_cast
          rw [neg_three_pow_odd hmo]
          ring)
        simpa using h
    · -- `E = 2m + 1`
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · exfalso
        apply hr0
        right; left
        simpa using hc
      obtain ⟨p, hp, hord⟩ := exists_prime_order_three (n := 2 * (2 * m + 1)) (by omega)
      have := Fact.mk hp
      refine goodPrime_of_order hr hE0 hgE hp (by omega) hord (h := 2) (by norm_num)
        (by rw [h2M]; ring) ?_
      rw [hc, sub_neg_eq_add]
      have hD : (p : ℤ) ∣ 3 ^ (2 * m + 1) + 1 := by
        apply dvd_of_cast_eq_zero
        push_cast
        rw [pow_eq_neg_one_of_orderOf (by omega) hord]
        ring
      have h := hasPrime_add hp (2 * m + 1) 0 hD (by
        rw [norm_sq_odd_add]
        simp only [Nat.zero_mod, ↓reduceIte]
        push_cast
        rw [neg_three_pow_sq]
        ring)
      simpa using h
  · -- `g = 3`: `c = ω^u`, `u ≢ 0`, `E` odd
    have hc3 : (r ^ E) ^ 3 = 1 := by rw [← hordc]; exact pow_orderOf_eq_one _
    obtain ⟨u, hu⟩ := eq_w3_pow_of_cube hc3
    have hu3 : u % 3 ≠ 0 := by
      intro h0
      have h1 : r ^ E = 1 := by rw [hu, w3_pow_mod, h0, pow_zero]
      rw [orderOf_eq_one_iff.2 h1] at hordc
      omega
    obtain ⟨m, hm⟩ : ∃ m, E = 2 * m + 1 := ⟨E / 2, by
      have : E % 2 ≠ 0 := fun h => by have := hEg h; omega
      omega⟩
    subst hm
    have hcases : u % 3 = 1 ∨ u % 3 = 2 := by omega
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · -- `E = 1`: `r = ω^u`
      have hru : r = w3 ^ u := by simpa using hu
      rcases hcases with h1 | h2
      · exfalso
        apply hr0
        rw [hru, w3_pow_mod, h1, pow_one]
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · refine goodPrime_of_order hr hE0 hgE (p := 7) (by norm_num) (by norm_num)
          orderOf_three_zmod_seven (h := 1) (by norm_num) (by rw [h2M]) ?_
        rw [hu]
        exact hasPrime_sub (by norm_num) 1 u (D := 7) (dvd_refl _) (by
          have h := norm_sq_odd 0 u
          simp only [Nat.mul_zero, Nat.zero_add] at h
          rw [h]
          simp only [h2, ↓reduceIte, show (2 : ℕ) ≠ 1 by norm_num]
          norm_num)
    · obtain ⟨⟨p₁, hp₁, hord₁, hd₁⟩, ⟨p₂, hp₂, hord₂, hd₂⟩⟩ := hH m hm0
      have hnorm := norm_sq_odd m u
      rcases hcases with h1 | h2
      · -- `3 s² - 3 s + 1`
        simp only [h1, ↓reduceIte] at hnorm
        rcases neg_three_pow_cases m with hs | hs
        · refine goodPrime_of_order hr hE0 hgE hp₁ (by omega) hord₁ (h := 1) (by norm_num)
            (by rw [h2M]; ring) ?_
          rw [hu]
          exact hasPrime_sub hp₁ (2 * m + 1) u hd₁ (by
            rw [hnorm, hs]
            push_cast
            ring)
        · refine goodPrime_of_order hr hE0 hgE hp₂ (by omega) hord₂ (h := 1) (by norm_num)
            (by rw [h2M]; ring) ?_
          rw [hu]
          exact hasPrime_sub hp₂ (2 * m + 1) u hd₂ (by
            rw [hnorm, hs]
            push_cast
            ring)
      · -- `3 s² + 3 s + 1`
        simp only [h2, ↓reduceIte, show (2 : ℕ) ≠ 1 by norm_num] at hnorm
        rcases neg_three_pow_cases m with hs | hs
        · refine goodPrime_of_order hr hE0 hgE hp₂ (by omega) hord₂ (h := 1) (by norm_num)
            (by rw [h2M]; ring) ?_
          rw [hu]
          exact hasPrime_sub hp₂ (2 * m + 1) u hd₂ (by
            rw [hnorm, hs]
            push_cast
            ring)
        · refine goodPrime_of_order hr hE0 hgE hp₁ (by omega) hord₁ (h := 1) (by norm_num)
            (by rw [h2M]; ring) ?_
          rw [hu]
          exact hasPrime_sub hp₁ (2 * m + 1) u hd₁ (by
            rw [hnorm, hs]
            push_cast
            ring)
  · -- `g = 6`: `c = -ω^u`, `u ≢ 0`
    have hc6 : (r ^ E) ^ 6 = 1 := by rw [← hordc]; exact pow_orderOf_eq_one _
    have hc3 : (r ^ E) ^ 3 ≠ 1 := by
      intro h3
      have hd := orderOf_dvd_of_pow_eq_one h3
      rw [hordc] at hd
      omega
    have hc2 : (r ^ E) ^ 2 ≠ 1 := by
      intro h2
      have hd := orderOf_dvd_of_pow_eq_one h2
      rw [hordc] at hd
      omega
    have hneg : (-(r ^ E)) ^ 3 = 1 := by
      have h3 : ((r ^ E) ^ 3 - 1) * ((r ^ E) ^ 3 + 1) = 0 := by linear_combination hc6
      rcases mul_eq_zero.1 h3 with h4 | h4
      · exact absurd (sub_eq_zero.1 h4) hc3
      · linear_combination -h4
    obtain ⟨u, hu⟩ := eq_w3_pow_of_cube hneg
    have hcu : r ^ E = -w3 ^ u := by rw [← hu, neg_neg]
    have hu3 : u % 3 ≠ 0 := by
      intro h0
      apply hc2
      rw [hcu, w3_pow_mod, h0, pow_zero]
      norm_num
    have hcases : u % 3 = 1 ∨ u % 3 = 2 := by omega
    rcases Nat.even_or_odd' E with ⟨m, rfl | rfl⟩
    · -- `E = 2m`
      have hm0 : 0 < m := by omega
      have hnorm := norm_sq_even_add m u
      simp only [hu3, ↓reduceIte] at hnorm
      rcases Nat.even_or_odd m with hme | hmo
      · -- `9^m - 3^m + 1`, order `6m`
        obtain ⟨p, hp, hord⟩ := exists_prime_order_three (n := 6 * m) (by omega)
        have := Fact.mk hp
        refine goodPrime_of_order hr hE0 hgE hp (by omega) hord (h := 4) (by norm_num)
          (by rw [h2M]; ring) ?_
        rw [hcu, sub_neg_eq_add]
        have hD : (p : ℤ) ∣ (3 ^ m) ^ 2 - 3 ^ m + 1 := by
          apply dvd_of_cast_eq_zero
          push_cast
          have h3m : (3 : ZMod p) ^ (3 * m) = -1 :=
            pow_eq_neg_one_of_orderOf (by omega) (by rw [hord]; ring)
          have hne : (3 : ZMod p) ^ m + 1 ≠ 0 := by
            intro h0
            have h1 : (3 : ZMod p) ^ (2 * m) = 1 := by
              rw [mul_comm, pow_mul]
              linear_combination ((3 : ZMod p) ^ m - 1) * h0
            have hd := orderOf_dvd_of_pow_eq_one h1
            rw [hord] at hd
            have := Nat.le_of_dvd (by omega) hd
            omega
          have h5 : ((3 : ZMod p) ^ m + 1) * (((3 : ZMod p) ^ m) ^ 2 - (3 : ZMod p) ^ m + 1) =
              0 := by
            rw [mul_comm 3 m, pow_mul] at h3m
            linear_combination h3m
          exact (mul_eq_zero.1 h5).resolve_left hne
        exact hasPrime_add hp (2 * m) u hD (by
          rw [hnorm, neg_three_pow_even hme]
          push_cast
          ring)
      · -- `9^m + 3^m + 1`, order `3m`
        obtain ⟨p, hp, hord⟩ := exists_prime_order_three (n := 3 * m) (by omega)
        have := Fact.mk hp
        refine goodPrime_of_order hr hE0 hgE hp (by omega) hord (h := 8) (by norm_num)
          (by rw [h2M]; ring) ?_
        rw [hcu, sub_neg_eq_add]
        have hD : (p : ℤ) ∣ (3 ^ m) ^ 2 + 3 ^ m + 1 := by
          apply dvd_of_cast_eq_zero
          push_cast
          have h3m : (3 : ZMod p) ^ (3 * m) = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
          have hne : (3 : ZMod p) ^ m - 1 ≠ 0 := by
            intro h0
            have hd := orderOf_dvd_of_pow_eq_one (sub_eq_zero.1 h0)
            rw [hord] at hd
            have := Nat.le_of_dvd hm0 hd
            omega
          have h5 : ((3 : ZMod p) ^ m - 1) * (((3 : ZMod p) ^ m) ^ 2 + (3 : ZMod p) ^ m + 1) =
              0 := by
            rw [mul_comm 3 m, pow_mul] at h3m
            linear_combination h3m
          exact (mul_eq_zero.1 h5).resolve_left hne
        exact hasPrime_add hp (2 * m) u hD (by
          rw [hnorm, neg_three_pow_odd hmo]
          push_cast
          ring)
    · -- `E = 2m + 1`
      have hnorm := norm_sq_odd_add m u
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · -- `E = 1`: `r = -ω^u`
        have hru : r = -w3 ^ u := by simpa using hcu
        rcases hcases with h1 | h2
        · refine goodPrime_of_order hr hE0 hgE (p := 7) (by norm_num) (by norm_num)
            orderOf_three_zmod_seven (h := 2) (by norm_num) (by rw [h2M]) ?_
          rw [hcu, sub_neg_eq_add]
          exact hasPrime_add (by norm_num) 1 u (D := 7) (dvd_refl _) (by
            simp only [Nat.mul_zero, Nat.zero_add] at hnorm
            rw [hnorm]
            simp only [h1, ↓reduceIte]
            norm_num)
        · exfalso
          apply hr0
          rw [hru, w3_pow_mod, h2]
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      · obtain ⟨⟨p₁, hp₁, hord₁, hd₁⟩, ⟨p₂, hp₂, hord₂, hd₂⟩⟩ := hH m hm0
        rcases hcases with h1 | h2
        · -- `3 s² + 3 s + 1`
          simp only [h1, ↓reduceIte] at hnorm
          rcases neg_three_pow_cases m with hs | hs
          · refine goodPrime_of_order hr hE0 hgE hp₂ (by omega) hord₂ (h := 2) (by norm_num)
              (by rw [h2M]; ring) ?_
            rw [hcu, sub_neg_eq_add]
            exact hasPrime_add hp₂ (2 * m + 1) u hd₂ (by
              rw [hnorm, hs]
              push_cast
              ring)
          · refine goodPrime_of_order hr hE0 hgE hp₁ (by omega) hord₁ (h := 2) (by norm_num)
              (by rw [h2M]; ring) ?_
            rw [hcu, sub_neg_eq_add]
            exact hasPrime_add hp₁ (2 * m + 1) u hd₁ (by
              rw [hnorm, hs]
              push_cast
              ring)
        · -- `3 s² - 3 s + 1`
          simp only [h2, ↓reduceIte, show (2 : ℕ) ≠ 1 by norm_num] at hnorm
          rcases neg_three_pow_cases m with hs | hs
          · refine goodPrime_of_order hr hE0 hgE hp₁ (by omega) hord₁ (h := 2) (by norm_num)
              (by rw [h2M]; ring) ?_
            rw [hcu, sub_neg_eq_add]
            exact hasPrime_add hp₁ (2 * m + 1) u hd₁ (by
              rw [hnorm, hs]
              push_cast
              ring)
          · refine goodPrime_of_order hr hE0 hgE hp₂ (by omega) hord₂ (h := 2) (by norm_num)
              (by rw [h2M]; ring) ?_
            rw [hcu, sub_neg_eq_add]
            exact hasPrime_add hp₂ (2 * m + 1) u hd₂ (by
              rw [hnorm, hs]
              push_cast
              ring)

end Base3

end PiFormula
