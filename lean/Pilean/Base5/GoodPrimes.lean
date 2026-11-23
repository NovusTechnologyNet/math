import Pilean.Base5.Defs

/-!
# Base 5: every root of unity other than `1` and `-1` has a good prime

`goodPrimes5_of_halves`: `GoodPrimes5` holds, given the statement `PrimitiveHalves5` about the
two Aurifeuillian factors `L_h`, `M_h` of `Φ_5(5^h)` (each has a prime factor `p` with
`ord_p(5) = 5h`, for every odd `h`).

The proof. Let `t = √5`, let `r ≠ ±1` be a root of unity of order `n`, and let `m ≥ 2` be the
order of `r²` (so `n = m` or `n = 2m`).

1. `hasPrime_five_sub`: if `ord_p(5) = m`, some prime ideal `P` contains `p` and `5 - r²`.
   Indeed `p` divides `5^m - 1 = ∏_j (5 - (r²)^j)`, so a prime ideal above `p` contains some
   `5 - (r²)^j`; the order of 5 forces `(r²)^j` to have order `m`, so `j` is prime to `m`,
   and `5 - (r²)^j` is conjugate to `5 - r²` (`hasPrime_conj`).
2. `5 - r² = (t - r)(t + r)`, so `P` contains `t - r` or `t + r`
   (`exists_prime_t5_sub_or_add`). Such a `p` is odd, is not 5, and does not divide `n`.
3. It remains to pass from `t + r` to `t - r`:

| case | the prime `p` | from `t + r` to `t - r` |
|---|---|---|
| `5 ∤ m` | Zsigmondy (`p = 3` for `m = 2`) | conjugation by `a ≡ 1 (mod n)`, `a ≡ 2 (mod 5)` |
| `10 ∣ m` | Zsigmondy | conjugation by `a = 1 + m`: `r^a = -r`, `a ≡ 1 (mod 5)` |
| `m = 5h`, `h` odd | a factor of `L_h` or of `M_h` | `t + r ∈ P` is impossible |

   The conjugations (`hasPrime_t5_conj`): `t = ±(η - η² - η³ + η⁴)` for a primitive fifth root
   of unity `η` (`gaussSum5_sq`), so `t - r` is an integer polynomial in a root of unity `ζ`,
   and `ζ ↦ ζ^a` sends `t` to `t` if `a ≡ 1 (mod 5)` and to `-t` if `a ≡ 2 (mod 5)`.

   The last row (`hasPrime_of_halves`). Put `Q(x) = x⁴ - t x³ + 3x² - t x + 1` (`aur5`). Then
   `L_h = Q(t^h)`, `M_h = Q(-t^h)`, and `Q(c) Q(-c) = c⁸ + c⁶ + c⁴ + c² + 1 = 0` for
   `c = r^h`. If `Q(c) = 0`, take `p ∣ L_h`: if `t + r ∈ P` then `t^h + c ∈ P`, which divides
   `Q(-t^h) - Q(c) = M_h`, so `P` contains `M_h - L_h = 2·5^((h+1)/2) (5^h + 1)`, against
   `ord_p(5) = 5h`. If `Q(-c) = 0`, take `p ∣ M_h` in the same way.
-/

open Complex Polynomial

namespace PiFormula

namespace Base5

/-! ## 1. Primes with a given order of 5 -/

/-- A prime at which 5 has order `m ≥ 2` is odd, is not 5, and is larger than `m`. -/
theorem prime_facts_of_orderOf_five {p m : ℕ} (hp : p.Prime) (hm : 2 ≤ m)
    (h : orderOf (5 : ZMod p) = m) : p ≠ 2 ∧ p ≠ 5 ∧ m < p := by
  have := Fact.mk hp
  have h5 : (5 : ZMod p) ≠ 0 := by
    intro h0
    have h1 : (5 : ZMod p) ^ m = 1 := by rw [← h]; exact pow_orderOf_eq_one _
    rw [h0, zero_pow (by omega)] at h1
    exact zero_ne_one h1
  have hd := ZMod.orderOf_dvd_card_sub_one h5
  rw [h] at hd
  have h2 := hp.two_le
  have hle := Nat.le_of_dvd (by omega) hd
  refine ⟨by omega, ?_, by omega⟩
  intro hp5
  have h6 : ((5 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff 5 p).2 (by rw [hp5])
  exact h5 (by exact_mod_cast h6)

/-- Such a prime does not divide a divisor of `2m`. -/
theorem not_dvd_of_orderOf_five {p m n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hlt : m < p)
    (hm : 0 < m) (hn : n ∣ 2 * m) : ¬ p ∣ n := by
  intro hpn
  rcases (Nat.Prime.dvd_mul hp).1 (hpn.trans hn) with h | h
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  · exact absurd (Nat.le_of_dvd hm h) (by omega)

/-- For every `m ≥ 2` there is a prime at which 5 has order `m` (Zsigmondy's theorem; the
prime is 3 for `m = 2`). -/
theorem exists_prime_orderOf_five {m : ℕ} (hm : 2 ≤ m) :
    ∃ p : ℕ, p.Prime ∧ orderOf (5 : ZMod p) = m := by
  rcases Nat.lt_or_ge m 3 with h | h
  · obtain rfl : m = 2 := by omega
    exact ⟨3, by norm_num, (orderOf_eq_iff (by norm_num)).2 ⟨by decide, by decide⟩⟩
  · obtain ⟨p, hp, h⟩ := TauCeti.exists_prime_orderOf_eq (a := 5) (by norm_num) h
    exact ⟨p, hp, by simpa using h⟩

/-! ## 2. A prime ideal containing `5 - r²` -/

private theorem isIntegral_five : IsIntegral ℤ (5 : ℂ) := by
  rw [← t5_sq]
  exact isIntegral_t5.pow 2

private theorem isIntegral_three : IsIntegral ℤ (3 : ℂ) := by
  simpa using isIntegral_natCast' 3

/-- If 5 has order `ord ρ` modulo the prime `p`, some prime ideal contains `p` and `5 - ρ`. -/
theorem hasPrime_five_sub {ρ : ℂ} (hρ : IsOfFinOrder ρ) {p : ℕ} (hp : p.Prime)
    (hord : orderOf (5 : ZMod p) = orderOf ρ) : Base3.HasPrime p (5 - ρ) := by
  classical
  have := Fact.mk hp
  obtain ⟨m, hm⟩ : ∃ m, orderOf ρ = m := ⟨_, rfl⟩
  rw [hm] at hord
  have hm0 : 0 < m := hm ▸ hρ.orderOf_pos
  have hprim : IsPrimitiveRoot ρ m := hm ▸ IsPrimitiveRoot.orderOf ρ
  have hρi := isIntegral_of_finOrder hρ
  obtain ⟨Q, hQ, hpQ⟩ := exists_prime_above hp
  -- if `5^d - 1 ∈ Q` then `m ∣ d`
  have hdvd : ∀ d : ℕ, InP Q ((5 : ℂ) ^ d - 1) → m ∣ d := by
    intro d hd
    have h2 : InP Q (((5 ^ d - 1 : ℕ) : ℂ)) := by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num))]
      push_cast
      exact hd
    have h3 : p ∣ 5 ^ d - 1 := by
      by_contra hnd
      exact not_inP_coprime ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd).symm h2 hpQ
    rw [← hord]
    apply orderOf_dvd_of_pow_eq_one
    have h5 : ((5 ^ d - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h3
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num))] at h5
    push_cast at h5
    exact sub_eq_zero.1 h5
  -- `5^m - 1 ∈ Q`
  have h1 : InP Q ((5 : ℂ) ^ m - 1) := by
    have h5 : (5 : ZMod p) ^ m = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
    have h3 : p ∣ 5 ^ m - 1 := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num))]
      push_cast
      rw [h5, sub_self]
    obtain ⟨k, hk⟩ := h3
    have h4 : (5 : ℂ) ^ m - 1 = (p : ℂ) * (k : ℂ) := by
      have h6 : (((5 ^ m - 1 : ℕ)) : ℂ) = ((p * k : ℕ) : ℂ) := by rw [hk]
      rw [Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num))] at h6
      push_cast at h6
      exact h6
    rw [h4]
    exact hpQ.mul_right (isIntegral_natCast' k)
  -- `5^m - 1 = ∏ (5 - ρ^j)`
  have hprod : (5 : ℂ) ^ m - 1 = ∏ j ∈ Finset.range m, (5 - ρ ^ j * 1) := by
    have h := Base3.prod_sub_nthRoots hm0 1 (5 : ℂ)
    rw [hprim.nthRoots_eq (one_pow m), Multiset.map_map] at h
    exact h.symm
  rw [hprod] at h1
  obtain ⟨j, -, hjQ⟩ := inP_prod (Finset.range m) _
    (fun j _ => isIntegral_five.sub ((hρi.pow j).mul isIntegral_one)) h1
  rw [mul_one] at hjQ
  -- `ρ^j` has order `m`
  have hj : m ∣ orderOf (ρ ^ j) := by
    apply hdvd
    have e := (Commute.all (5 : ℂ) (ρ ^ j)).mul_geom_sum₂ (orderOf (ρ ^ j))
    rw [pow_orderOf_eq_one] at e
    rw [← e]
    exact hjQ.mul_right (IsIntegral.sum _ fun i _ =>
      (isIntegral_five.pow _).mul ((hρi.pow j).pow _))
  have hj2 : orderOf (ρ ^ j) ∣ m := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow]
  have hjm : orderOf (ρ ^ j) = m := Nat.dvd_antisymm hj2 hj
  have hcop : j.Coprime m := by
    have h : IsPrimitiveRoot (ρ ^ j) m := hjm ▸ IsPrimitiveRoot.orderOf (ρ ^ j)
    exact (hprim.pow_iff_coprime hm0 j).1 h
  -- conjugate `5 - ρ^j` to `5 - ρ`
  let F : ℤ[X] := 5 - X
  have hF : ∀ z : ℂ, aeval z F = 5 - z := fun z => by
    simp only [F, map_sub, aeval_X, map_ofNat]
  rw [← hF ρ]
  refine Base3.hasPrime_conj hm0 hprim F hcop ?_
  rw [hF]
  exact ⟨Q, hQ, hpQ, hjQ⟩

/-- If 5 has order `ord r²` modulo the prime `p`, some prime ideal contains `p` and one of
`t - r`, `t + r`. -/
theorem exists_prime_t5_sub_or_add {r : ℂ} (hr : IsOfFinOrder r) {p : ℕ} (hp : p.Prime)
    (hord : orderOf (5 : ZMod p) = orderOf (r ^ 2)) :
    ∃ Q : Ideal Aint, Q.IsPrime ∧ InP Q (p : ℂ) ∧ (InP Q (t5 - r) ∨ InP Q (t5 + r)) := by
  obtain ⟨Q, hQ, hpQ, hx⟩ := hasPrime_five_sub (hr.pow (n := 2)) hp hord
  have e : (5 : ℂ) - r ^ 2 = (t5 - r) * (t5 + r) := by
    rw [← t5_sq]
    ring
  rw [e] at hx
  have hri := isIntegral_of_finOrder hr
  exact ⟨Q, hQ, hpQ, inP_mul (isIntegral_t5.sub hri) (isIntegral_t5.add hri) hx⟩

/-! ## 3. Conjugation: `t` as a polynomial in a fifth root of unity -/

/-- The Gauss sum: `(η - η² - η³ + η⁴)² = 5` for a fifth root of unity `η ≠ 1`. -/
theorem gaussSum5_sq {η : ℂ} (h5 : η ^ 5 = 1) (h1 : η ≠ 1) :
    (η - η ^ 2 - η ^ 3 + η ^ 4) ^ 2 = 5 := by
  have hs : η ^ 4 + η ^ 3 + η ^ 2 + η + 1 = 0 := by
    have h : (η - 1) * (η ^ 4 + η ^ 3 + η ^ 2 + η + 1) = 0 := by linear_combination h5
    exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 h1)
  linear_combination (η ^ 4 - 3 * η ^ 3 + η ^ 2 + 5 * η - 5) * hs

/-- **Conjugation in base 5.** Let `a` be prime to the order of the root of unity `r`. If
`a ≡ 1 (mod 5)`, a prime for `t - r^a` gives a prime for `t - r`; if `a ≡ 2 (mod 5)`, a prime
for `t + r^a` gives a prime for `t - r`. -/
theorem hasPrime_t5_conj {r : ℂ} (hr : IsOfFinOrder r) {p a : ℕ}
    (ha : a.Coprime (orderOf r)) :
    (a % 5 = 1 → Base3.HasPrime p (t5 - r ^ a) → Base3.HasPrime p (t5 - r)) ∧
      (a % 5 = 2 → Base3.HasPrime p (t5 + r ^ a) → Base3.HasPrime p (t5 - r)) := by
  obtain ⟨n, hn⟩ : ∃ n, orderOf r = n := ⟨_, rfl⟩
  rw [hn] at ha
  have hn0 : 0 < n := hn ▸ hr.orderOf_pos
  have hrn : r ^ n = 1 := hn ▸ pow_orderOf_eq_one r
  have hN0 : 0 < 5 * n := by omega
  have : NeZero (5 * n) := ⟨hN0.ne'⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ (5 * n) := ⟨_, zetaN_prim hN0⟩
  -- `η = ζ^n` is a primitive fifth root of unity, and `t = ±(η - η² - η³ + η⁴)`
  have hη : IsPrimitiveRoot (ζ ^ n) 5 := hζ.pow hN0 (mul_comm 5 n)
  have h5 : (ζ ^ n) ^ 5 = 1 := hη.pow_eq_one
  have h1 : ζ ^ n ≠ 1 := hη.ne_one (by norm_num)
  obtain ⟨δ, hδ⟩ : ∃ δ : ℤ,
      (δ : ℂ) * (ζ ^ n - (ζ ^ n) ^ 2 - (ζ ^ n) ^ 3 + (ζ ^ n) ^ 4) = t5 := by
    have h := gaussSum5_sq h5 h1
    have h2 : (ζ ^ n - (ζ ^ n) ^ 2 - (ζ ^ n) ^ 3 + (ζ ^ n) ^ 4 - t5) *
        (ζ ^ n - (ζ ^ n) ^ 2 - (ζ ^ n) ^ 3 + (ζ ^ n) ^ 4 + t5) = 0 := by
      linear_combination h - t5_sq
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact ⟨1, by rw [Int.cast_one, one_mul]; exact sub_eq_zero.1 h3⟩
    · exact ⟨-1, by push_cast; linear_combination -h3⟩
  obtain ⟨k, -, hk⟩ := hζ.eq_pow_of_pow_eq_one
    (show r ^ (5 * n) = 1 by rw [mul_comm, pow_mul, hrn, one_pow])
  -- `t - r = F(ζ)`
  let F : ℤ[X] := C δ * (X ^ n - (X ^ n) ^ 2 - (X ^ n) ^ 3 + (X ^ n) ^ 4) - X ^ k
  have hF : ∀ z : ℂ, aeval z F =
      (δ : ℂ) * (z ^ n - (z ^ n) ^ 2 - (z ^ n) ^ 3 + (z ^ n) ^ 4) - z ^ k := fun z => by
    simp [F]
  have hF1 : aeval ζ F = t5 - r := by rw [hF, hδ, hk]
  have hcop : a % 5 ≠ 0 → a.Coprime (5 * n) := fun h0 =>
    Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2
      (fun hd => h0 (Nat.mod_eq_zero_of_dvd hd))).symm ha
  have hka : (ζ ^ a) ^ k = r ^ a := by rw [← pow_mul, mul_comm, pow_mul, hk]
  have hna : (ζ ^ a) ^ n = (ζ ^ n) ^ a := by rw [← pow_mul, mul_comm, pow_mul]
  constructor
  · intro ha5 h
    rw [← hF1]
    refine Base3.hasPrime_conj hN0 hζ F (hcop (by omega)) ?_
    have e : (ζ ^ n) ^ a = ζ ^ n := by
      obtain ⟨q, hq⟩ : ∃ q, a = 5 * q + 1 := ⟨a / 5, by omega⟩
      rw [hq, pow_succ, pow_mul, h5, one_pow, one_mul]
    rw [hF, hna, e, hδ, hka]
    exact h
  · intro ha5 h
    rw [← hF1]
    refine Base3.hasPrime_conj hN0 hζ F (hcop (by omega)) ?_
    have e : (ζ ^ n) ^ a = (ζ ^ n) ^ 2 := by
      obtain ⟨q, hq⟩ : ∃ q, a = 5 * q + 2 := ⟨a / 5, by omega⟩
      rw [hq, pow_add, pow_mul, h5, one_pow, one_mul]
    have e2 : aeval (ζ ^ a) F = -(t5 + r ^ a) := by
      rw [hF, hna, e, hka, ← hδ]
      linear_combination (δ : ℂ) * ((ζ ^ n) ^ 3 - ζ ^ n) * h5
    rw [e2]
    obtain ⟨Q, hQ, hpQ, hx⟩ := h
    exact ⟨Q, hQ, hpQ, hx.neg⟩

/-! ## 4. The Aurifeuillian factors -/

/-- `Q(x) = x⁴ - t x³ + 3x² - t x + 1`, the polynomial with roots `e^(±iπ/5)`, `e^(±2iπ/5)`.
`L_h = Q(t^h)` and `M_h = Q(-t^h)` for odd `h`. -/
noncomputable def aur5 (x : ℂ) : ℂ := x ^ 4 - t5 * x ^ 3 + 3 * x ^ 2 - t5 * x + 1

/-- `Q(c) Q(-c) = c⁸ + c⁶ + c⁴ + c² + 1`. -/
theorem aur5_mul_aur5_neg (c : ℂ) :
    aur5 c * aur5 (-c) = c ^ 8 + c ^ 6 + c ^ 4 + c ^ 2 + 1 := by
  simp only [aur5]
  linear_combination (-(c ^ 2 * (c ^ 2 + 1) ^ 2)) * t5_sq

private theorem t5_pow_odd (k : ℕ) : t5 ^ (2 * k + 1) = 5 ^ k * t5 := by
  rw [pow_succ, pow_mul, t5_sq]

/-- `L_h = Q(t^h)` for odd `h`. -/
theorem L5_cast_eq_aur5 {h : ℕ} (hh : Odd h) : ((L5 h : ℤ) : ℂ) = aur5 (t5 ^ h) := by
  obtain ⟨k, rfl⟩ := hh
  have e : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  rw [L5, aur5, e, t5_pow_odd]
  push_cast
  linear_combination (-((5 : ℂ) ^ k) ^ 4 * (t5 ^ 2 + 5) + ((5 : ℂ) ^ k) ^ 3 * (t5 ^ 2 + 5) -
    3 * ((5 : ℂ) ^ k) ^ 2 + (5 : ℂ) ^ k) * t5_sq

/-- `M_h = Q(-t^h)` for odd `h`. -/
theorem M5_cast_eq_aur5 {h : ℕ} (hh : Odd h) : ((M5 h : ℤ) : ℂ) = aur5 (-(t5 ^ h)) := by
  obtain ⟨k, rfl⟩ := hh
  have e : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  rw [M5, aur5, e, t5_pow_odd]
  push_cast
  linear_combination (-((5 : ℂ) ^ k) ^ 4 * (t5 ^ 2 + 5) - ((5 : ℂ) ^ k) ^ 3 * (t5 ^ 2 + 5) -
    3 * ((5 : ℂ) ^ k) ^ 2 - (5 : ℂ) ^ k) * t5_sq

/-- If `Q(c) = 0` and `x - c ∈ P`, then `Q(x) ∈ P`: `x - c` divides `Q(x) - Q(c)`. -/
theorem inP_aur5 {P : Ideal Aint} {x c : ℂ} (hx : IsIntegral ℤ x) (hc : IsIntegral ℤ c)
    (hc0 : aur5 c = 0) (h : InP P (x - c)) : InP P (aur5 x) := by
  have e : aur5 x = (x - c) * (x ^ 3 + x ^ 2 * c + x * c ^ 2 + c ^ 3 -
      t5 * (x ^ 2 + x * c + c ^ 2) + 3 * (x + c) - t5) := by
    have h0 : aur5 x = aur5 x - aur5 c := by rw [hc0, sub_zero]
    rw [h0]
    simp only [aur5]
    ring
  rw [e]
  have ht := isIntegral_t5
  exact h.mul_right ((((((((hx.pow 3).add ((hx.pow 2).mul hc)).add (hx.mul (hc.pow 2))).add
    (hc.pow 3)).sub (ht.mul (((hx.pow 2).add (hx.mul hc)).add (hc.pow 2)))).add
    (isIntegral_three.mul (hx.add hc)))).sub ht)

/-- A prime ideal above a prime `p` with `ord_p(5) = 5h`, `h` odd, does not contain both
`L_h` and `M_h`: their difference is `2·5^((h+1)/2) (5^h + 1)`. -/
theorem not_inP_L5_M5 {P : Ideal Aint} [P.IsPrime] {p h : ℕ} (hp : p.Prime) (hh : Odd h)
    (hord : orderOf (5 : ZMod p) = 5 * h) (hpP : InP P (p : ℂ))
    (hL : InP P ((L5 h : ℤ) : ℂ)) (hM : InP P ((M5 h : ℤ) : ℂ)) : False := by
  have := Fact.mk hp
  have hh0 : 0 < h := hh.pos
  obtain ⟨hp2, hp5, -⟩ := prime_facts_of_orderOf_five hp (by omega) hord
  have hD : InP P ((2 * 5 ^ ((h + 1) / 2) * (5 ^ h + 1) : ℕ) : ℂ) := by
    have e : ((2 * 5 ^ ((h + 1) / 2) * (5 ^ h + 1) : ℕ) : ℂ) =
        ((M5 h : ℤ) : ℂ) - ((L5 h : ℤ) : ℂ) := by
      simp only [L5, M5]
      push_cast
      ring
    rw [e]
    exact hM.sub hL
  have hdvd : p ∣ 2 * 5 ^ ((h + 1) / 2) * (5 ^ h + 1) := by
    by_contra hnd
    exact not_inP_coprime ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd).symm hD hpP
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h1 | h1
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h1)
    · exact hp5 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 (hp.dvd_of_dvd_pow h1))
  · have hz : ((5 ^ h + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h1
    push_cast at hz
    have h3 : (5 : ZMod p) ^ h = -1 := eq_neg_of_add_eq_zero_left hz
    have h4 : (5 : ZMod p) ^ (2 * h) = 1 := by
      rw [mul_comm, pow_mul, h3]
      norm_num
    have hd := orderOf_dvd_of_pow_eq_one h4
    rw [hord] at hd
    have := Nat.le_of_dvd (by omega) hd
    omega

/-- **The Aurifeuillian case.** If `r²` has order `5h` with `h` odd, one of the two primes of
`PrimitiveHalves5` lies under a prime ideal containing `t - r`. -/
theorem hasPrime_of_halves (hH : PrimitiveHalves5) {r : ℂ} (hr : IsOfFinOrder r) {h : ℕ}
    (hh : Odd h) (hm : orderOf (r ^ 2) = 5 * h) :
    ∃ p : ℕ, p.Prime ∧ orderOf (5 : ZMod p) = 5 * h ∧ Base3.HasPrime p (t5 - r) := by
  obtain ⟨⟨p₁, hp₁, hord₁, hd₁⟩, ⟨p₂, hp₂, hord₂, hd₂⟩⟩ := hH h hh
  have hri := isIntegral_of_finOrder hr
  have hci : IsIntegral ℤ (r ^ h) := hri.pow h
  have hti : IsIntegral ℤ (t5 ^ h) := isIntegral_t5.pow h
  -- `c = r^h` satisfies `c^10 = 1`, `c² ≠ 1`, so `Q(c) Q(-c) = 0`
  have hc10 : (r ^ h) ^ 10 = 1 := by
    have h1 := pow_orderOf_eq_one (r ^ 2)
    rw [hm] at h1
    rw [← h1]
    ring
  have hc2 : (r ^ h) ^ 2 ≠ 1 := by
    intro h1
    have h2 : (r ^ 2) ^ h = 1 := by
      rw [← h1]
      ring
    have hd := orderOf_dvd_of_pow_eq_one h2
    rw [hm] at hd
    have hh0 := hh.pos
    have := Nat.le_of_dvd hh0 hd
    omega
  have hcyc : aur5 (r ^ h) * aur5 (-(r ^ h)) = 0 := by
    rw [aur5_mul_aur5_neg]
    have h3 : ((r ^ h) ^ 2 - 1) *
        ((r ^ h) ^ 8 + (r ^ h) ^ 6 + (r ^ h) ^ 4 + (r ^ h) ^ 2 + 1) = 0 := by
      linear_combination hc10
    exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hc2)
  -- `t + r` divides `t^h + r^h`
  have key : ∀ Q : Ideal Aint, InP Q (t5 + r) → InP Q (t5 ^ h + r ^ h) := by
    intro Q hx
    have e := (Commute.all t5 (-r)).mul_geom_sum₂ h
    rw [hh.neg_pow] at e
    simp only [sub_neg_eq_add] at e
    rw [← e]
    exact hx.mul_right (IsIntegral.sum _ fun i _ =>
      (isIntegral_t5.pow _).mul (hri.neg.pow _))
  rcases mul_eq_zero.1 hcyc with h0 | h0
  · -- `Q(c) = 0`: the prime of `L_h`
    refine ⟨p₁, hp₁, hord₁, ?_⟩
    obtain ⟨Q, hQ, hpQ, hx | hx⟩ := exists_prime_t5_sub_or_add hr hp₁ (hord₁.trans hm.symm)
    · exact ⟨Q, hQ, hpQ, hx⟩
    · exfalso
      have hL : InP Q ((L5 h : ℤ) : ℂ) := by
        obtain ⟨k, hk⟩ := hd₁
        rw [hk]
        push_cast
        exact hpQ.mul_right (isIntegral_intCast k)
      have hM : InP Q ((M5 h : ℤ) : ℂ) := by
        rw [M5_cast_eq_aur5 hh]
        have h1 := (key Q hx).neg
        have e : -(t5 ^ h + r ^ h) = -(t5 ^ h) - r ^ h := by ring
        rw [e] at h1
        exact inP_aur5 hti.neg hci h0 h1
      exact not_inP_L5_M5 hp₁ hh hord₁ hpQ hL hM
  · -- `Q(-c) = 0`: the prime of `M_h`
    refine ⟨p₂, hp₂, hord₂, ?_⟩
    obtain ⟨Q, hQ, hpQ, hx | hx⟩ := exists_prime_t5_sub_or_add hr hp₂ (hord₂.trans hm.symm)
    · exact ⟨Q, hQ, hpQ, hx⟩
    · exfalso
      have hM : InP Q ((M5 h : ℤ) : ℂ) := by
        obtain ⟨k, hk⟩ := hd₂
        rw [hk]
        push_cast
        exact hpQ.mul_right (isIntegral_intCast k)
      have hL : InP Q ((L5 h : ℤ) : ℂ) := by
        rw [L5_cast_eq_aur5 hh]
        have h1 := key Q hx
        have e : t5 ^ h + r ^ h = t5 ^ h - -(r ^ h) := by ring
        rw [e] at h1
        exact inP_aur5 hti hci.neg h0 h1
      exact not_inP_L5_M5 hp₂ hh hord₂ hpQ hL hM

/-! ## 5. The theorem -/

/-- **Good primes in base 5** (from `PrimitiveHalves5`). Every root of unity other than `1`
and `-1` has a good prime. -/
theorem goodPrimes5_of_halves (hH : PrimitiveHalves5) : GoodPrimes5 := by
  intro r hr hr1 hr2
  obtain ⟨n, hn⟩ : ∃ n, orderOf r = n := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, orderOf (r ^ 2) = m := ⟨_, rfl⟩
  have hm0 : 0 < m := hm ▸ (hr.pow (n := 2)).orderOf_pos
  have hrm : (r ^ 2) ^ m = 1 := hm ▸ pow_orderOf_eq_one (r ^ 2)
  -- `m ≥ 2` because `r ≠ ±1`
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have h1 : m = 1 := by omega
    have h2 : r ^ 2 = 1 := orderOf_eq_one_iff.1 (hm.trans h1)
    have h3 : (r - 1) * (r + 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact hr1 (sub_eq_zero.1 h4)
    · exact hr2 (eq_neg_of_add_eq_zero_left h4)
  have hnm : n ∣ 2 * m := by
    rw [← hn]
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul]
    exact hrm
  -- the common end of every case
  have finish : ∀ p : ℕ, p.Prime → orderOf (5 : ZMod p) = m → Base3.HasPrime p (t5 - r) →
      HasGoodPrime5 r := by
    intro p hp hord ⟨Q, hQ, hpQ, hx⟩
    obtain ⟨hp2, hp5, hlt⟩ := prime_facts_of_orderOf_five hp hm2 hord
    exact ⟨Q, hQ, p, hp, hp2, hp5,
      by rw [hn]; exact not_dvd_of_orderOf_five hp hp2 hlt hm0 hnm, hpQ, hx⟩
  by_cases h5 : 5 ∣ m
  · rcases Nat.even_or_odd m with hme | hmo
    · -- `10 ∣ m`: `-r = r^(1 + m)` and `1 + m ≡ 1 (mod 5)`
      obtain ⟨p, hp, hord⟩ := exists_prime_orderOf_five hm2
      refine finish p hp hord ?_
      obtain ⟨Q, hQ, hpQ, hx | hx⟩ := exists_prime_t5_sub_or_add hr hp (hord.trans hm.symm)
      · exact ⟨Q, hQ, hpQ, hx⟩
      · have hrm1 : r ^ m = -1 := by
          have h1 : (r ^ m - 1) * (r ^ m + 1) = 0 := by linear_combination hrm
          rcases mul_eq_zero.1 h1 with h2 | h2
          · exfalso
            obtain ⟨m', hm'⟩ := hme
            have h3 : (r ^ 2) ^ m' = 1 := by
              rw [← sub_eq_zero.1 h2, hm']
              ring
            have hd := orderOf_dvd_of_pow_eq_one h3
            rw [hm] at hd
            have := Nat.le_of_dvd (by omega) hd
            omega
          · exact eq_neg_of_add_eq_zero_left h2
        have hcop : (m + 1).Coprime (orderOf r) := by
          rw [hn]
          refine Nat.Coprime.coprime_dvd_right hnm (Nat.Coprime.mul_right ?_ ?_)
          · exact Nat.coprime_two_right.2 hme.add_one
          · simp
        refine (hasPrime_t5_conj hr hcop).1 (by omega) ⟨Q, hQ, hpQ, ?_⟩
        have e : t5 - r ^ (m + 1) = t5 + r := by
          rw [pow_succ, hrm1]
          ring
        rw [e]
        exact hx
    · -- `m = 5h`, `h` odd: the Aurifeuillian case
      obtain ⟨h, rfl⟩ := h5
      obtain ⟨p, hp, hord, hx⟩ := hasPrime_of_halves hH hr (Nat.odd_mul.1 hmo).2 hm
      exact finish p hp hord hx
  · -- `5 ∤ m`: an exponent `a ≡ 1 (mod n)`, `a ≡ 2 (mod 5)`
    obtain ⟨p, hp, hord⟩ := exists_prime_orderOf_five hm2
    refine finish p hp hord ?_
    obtain ⟨Q, hQ, hpQ, hx | hx⟩ := exists_prime_t5_sub_or_add hr hp (hord.trans hm.symm)
    · exact ⟨Q, hQ, hpQ, hx⟩
    · have h5n : ¬ 5 ∣ n := fun hd => by
        rcases (Nat.Prime.dvd_mul Nat.prime_five).1 (hd.trans hnm) with h | h
        · exact absurd h (by decide)
        · exact h5 h
      have hc : Nat.Coprime n 5 :=
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 h5n).symm
      let x := Nat.chineseRemainder hc 1 2
      have hx1 : x.1 ≡ 1 [MOD n] := x.2.1
      have hx2 : x.1 % 5 = 2 := x.2.2
      have hcop : Nat.Coprime x.1 (orderOf r) := by
        rw [hn, Nat.Coprime, hx1.gcd_eq]
        simp
      have hra : r ^ x.1 = r := by
        have h1 : r ^ x.1 = r ^ 1 := by
          rw [← pow_mod_orderOf r x.1, ← pow_mod_orderOf r 1, hn,
            show x.1 % n = 1 % n from hx1]
        rwa [pow_one] at h1
      refine (hasPrime_t5_conj hr hcop).2 hx2 ⟨Q, hQ, hpQ, ?_⟩
      rw [hra]
      exact hx

end Base5

end PiFormula
