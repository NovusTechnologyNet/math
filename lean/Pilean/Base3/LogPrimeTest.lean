import Pilean.Base3.LogPrimeTestAux

/-!
# Base 3: the finite test for a prime

For a prime `p ≠ 3`, whether `log p` is the value of a series of the class F3 is decided by
one integer, the *primitive part that contains `p`* (`primPart3 p`). Let `n` be the order of 3
modulo `p`.

* If `n` is not 6 modulo 12, the primitive part is `Φ_n(3)`.
* If `n = 6E` with `E` odd, `Φ_n(3)` is the product of the two numbers
  `gcd(Φ_n(3), L_E)` and `gcd(Φ_n(3), M_E)`, where `L_E = 3^E - 3^((E+1)/2) + 1` and
  `M_E = 3^E + 3^((E+1)/2) + 1` are the Aurifeuillian factors of `3^(3E) + 1`
  (`halfL E`, `halfM E`; `halves_facts`), and the primitive part is the one that `p` divides.

**The test** (`isF3Value_log_prime_iff`, from Baker's theorem), for every prime `p ≠ 3`:
`log p` is a value of the class F3 if and only if every prime `q ≠ p` that divides the
primitive part divides `n` and has `log q` a value of F3.

There is at most one such `q` (`primPart3_intrinsic_unique`): a prime factor of `Φ_n(3)` that
divides `n` is the largest prime factor of `n`, and it divides `Φ_n(3)` exactly once; the
other prime factors of the primitive part have order `n` (`primPart3_prime_factor`). So the
test is finite, and it reads (`isF3Value_log_prime_iff_explicit`): the primitive part is
`p^x`, or `p^x q` with `q` a prime dividing `n` and `log q` a value of F3. Since `log 3` is a
value, this decides every prime (`isF3Value_log_prime_classification`). Unlike in base 2, no
prime is excepted. With the formal proof of Baker's theorem the hypothesis disappears
(`LogPrimeTestUnconditional.lean`).

The two halves of the proof.

* *The primitive part is a value* (`primPart3_facts`, no Baker): `log Φ_n(3)` is a value by
  induction on `n` from `∏_{d ∣ n} Φ_d(3) = 3^n - 1`. For `n = 6E`, with `E = 3^a m`, `3 ∤ m`,
  the two halves are the norms `N(Φ_m(ω t^(3^a)))` and `N(Φ_m(ω² t^(3^a)))` in the Eisenstein
  integers (`Halves.lean`), and `log N(Φ_m(z))` is a value by induction from
  `∏_{d ∣ m} N(Φ_d(z)) = N(z^m - 1)`: the numbers `N(z^d - 1)` are base numbers `L`, `M`.
* *A second primitive prime excludes `p`* (`not_isF3Value_log_of_partner`, from Baker's
  theorem): if a prime `q ≠ p` that does not divide `n` divides the primitive part, then
  `log p` is not a value. Such a `q` has order `n` too, and the statement is
  `not_isF3Value_log_of_same_part` of `LogPrimeTestAux.lean`.

Examples: `log 31`, `log 41`, `log 43`, `log 61`, `log 73` are values (no Baker); `log 17` and
`log 23` are not (from Baker's theorem).
-/

open Polynomial

namespace PiFormula

namespace Base3

/-! ## 1. The logarithm of `Φ_n(3)` is a value -/

/-- `log Φ_n(3)` is a value of the class F3, for every `n ≥ 1`. -/
theorem isF3Value_log_cyclotomic_three : ∀ n : ℕ, 0 < n →
    IsF3Value (Real.log (((cyclotomic n ℤ).eval 3 : ℤ) : ℝ)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have hpos : ∀ d : ℕ, (0 : ℝ) < (((cyclotomic d ℤ).eval 3 : ℤ) : ℝ) := fun d => by
      exact_mod_cast cyclotomic_pos' d (R := ℤ) (x := 3) (by norm_num)
    have hprod : ∏ d ∈ n.divisors, (((cyclotomic d ℤ).eval 3 : ℤ) : ℝ) =
        (((3 : ℤ) ^ n - 1 : ℤ) : ℝ) := by
      have h := congrArg (Polynomial.eval (3 : ℤ)) (prod_cyclotomic_eq_X_pow_sub_one hn ℤ)
      rw [eval_prod] at h
      have h2 := congrArg (fun z : ℤ => (z : ℝ)) h
      simp only [Int.cast_prod] at h2
      rw [h2]
      simp
    rw [← Nat.insert_self_properDivisors hn.ne',
      Finset.prod_insert (by simp : n ∉ n.properDivisors)] at hprod
    have hlog : Real.log (((cyclotomic n ℤ).eval 3 : ℤ) : ℝ) =
        Real.log (((3 : ℤ) ^ n - 1 : ℤ) : ℝ) -
          ∑ d ∈ n.properDivisors, Real.log (((cyclotomic d ℤ).eval 3 : ℤ) : ℝ) := by
      rw [← hprod, Real.log_mul (hpos n).ne' (Finset.prod_pos fun d _ => hpos d).ne',
        Real.log_prod (fun d _ => (hpos d).ne')]
      ring
    rw [hlog]
    refine (isF3Value_log_int (Or.inr (Or.inl ⟨n, hn, rfl⟩))).sub ?_
    exact Submodule.sum_mem f3Values fun d hd =>
      ih d (Nat.mem_properDivisors.1 hd).2 (Nat.pos_of_mem_properDivisors hd)

/-! ## 2. The two halves of `Φ_{6E}(3)` -/

/-- `log N(Φ_n(z))` is a value, for `z` in the Eisenstein integers with `N(z) > 1`, as soon
as the `log N(z^d - 1)` are. -/
theorem isF3Value_log_norm_cyclotomic {z : Eis} (hz : 1 < z.norm) {P : ℕ → Prop}
    (hP : ∀ n d : ℕ, P n → d ∣ n → P d)
    (hU : ∀ n : ℕ, 0 < n → P n → IsF3Value (Real.log (((z ^ n - 1).norm : ℤ) : ℝ))) :
    ∀ n : ℕ, 0 < n → P n →
      IsF3Value (Real.log ((((cyclotomic n Eis).eval z).norm : ℤ) : ℝ)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hPn
    have hpos : ∀ d : ℕ, 0 < d →
        (0 : ℝ) < ((((cyclotomic d Eis).eval z).norm : ℤ) : ℝ) := fun d hd => by
      have h0 := norm_eval_cyclotomic_ne_zero3 hz hd
      have h1 := eis_norm_nonneg ((cyclotomic d Eis).eval z)
      exact_mod_cast lt_of_le_of_ne h1 (Ne.symm h0)
    have hprod : ∏ d ∈ n.divisors, ((((cyclotomic d Eis).eval z).norm : ℤ) : ℝ) =
        (((z ^ n - 1).norm : ℤ) : ℝ) := by
      exact_mod_cast prod_norm_eval_cyclotomic3 z hn
    rw [← Nat.insert_self_properDivisors hn.ne',
      Finset.prod_insert (by simp : n ∉ n.properDivisors)] at hprod
    have hpd : ∀ d ∈ n.properDivisors, 0 < d := fun d hd => Nat.pos_of_mem_properDivisors hd
    have hlog : Real.log ((((cyclotomic n Eis).eval z).norm : ℤ) : ℝ) =
        Real.log (((z ^ n - 1).norm : ℤ) : ℝ) -
          ∑ d ∈ n.properDivisors, Real.log ((((cyclotomic d Eis).eval z).norm : ℤ) : ℝ) := by
      rw [← hprod, Real.log_mul (hpos n hn).ne'
          (Finset.prod_pos fun d hd => hpos d (hpd d hd)).ne',
        Real.log_prod (fun d hd => (hpos d (hpd d hd)).ne')]
      ring
    rw [hlog]
    refine (hU n hn hPn).sub ?_
    exact Submodule.sum_mem f3Values fun d hd =>
      ih d (Nat.mem_properDivisors.1 hd).2 (hpd d hd)
        (hP n d hPn (Nat.mem_properDivisors.1 hd).1)

/-- `N(ω t^E - 1)` and `N(ω² t^E - 1)` are `L_k` and `M_k` in some order, `E = 2k + 1`. -/
theorem norm_w_tE_cases (k : ℕ) :
    ((wE * tE ^ (2 * k + 1) - 1).norm = L3 k ∧ (wE ^ 2 * tE ^ (2 * k + 1) - 1).norm = M3 k) ∨
      ((wE * tE ^ (2 * k + 1) - 1).norm = M3 k ∧
        (wE ^ 2 * tE ^ (2 * k + 1) - 1).norm = L3 k) := by
  obtain ⟨h1, h2⟩ := norm_w_tE k
  have h9 : (9 : ℤ) ^ k = (3 ^ k) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rcases Nat.even_or_odd k with he | ho
  · have hs : (-3 : ℤ) ^ k = 3 ^ k := he.neg_pow 3
    right
    rw [h1, h2, hs, h9]
    unfold L3 M3
    constructor <;> ring
  · have hs : (-3 : ℤ) ^ k = -3 ^ k := ho.neg_pow 3
    left
    rw [h1, h2, hs, h9]
    unfold L3 M3
    constructor <;> ring

/-- `N(ω^j t^e - 1)` is a base number, for `3 ∤ j` and `e` odd. -/
theorem norm_pow_mem {j e : ℕ} (hj : ¬ 3 ∣ j) (he : Odd e) :
    (wE ^ j * tE ^ e - 1).norm ∈ baseNumbers3 := by
  obtain ⟨k, rfl⟩ := he
  rw [wE_pow_mod j]
  rcases (by omega : j % 3 = 1 ∨ j % 3 = 2) with h | h <;> rw [h]
  · rw [pow_one]
    rcases norm_w_tE_cases k with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
    · exact L3_mem k
    · exact M3_mem k
  · rcases norm_w_tE_cases k with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2]
    · exact M3_mem k
    · exact L3_mem k

/-- `L_k` and `M_k` are coprime. -/
theorem isCoprime_L3_M3 (k : ℕ) : IsCoprime (L3 k) (M3 k) := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra h
  have h' : ¬ Nat.Coprime (L3 k).natAbs (M3 k).natAbs := h
  obtain ⟨r, hr, hrL, hrM⟩ := Nat.Prime.not_coprime_iff_dvd.1 h'
  have hL : (r : ℤ) ∣ L3 k := Int.natCast_dvd.2 hrL
  have hM : (r : ℤ) ∣ M3 k := Int.natCast_dvd.2 hrM
  rcases eq_two_or_three_of_dvd hr hL hM with rfl | rfl
  · -- `L_k` is odd
    have h3 : Odd ((3 : ℤ) ^ (2 * k + 1)) := Odd.pow ⟨1, by norm_num⟩
    have h4 : Odd ((3 : ℤ) ^ (k + 1)) := Odd.pow ⟨1, by norm_num⟩
    have h5 : Odd (L3 k) := (h3.sub_odd h4).add_one
    exact (Int.not_even_iff_odd.2 h5) (even_iff_two_dvd.2 (by exact_mod_cast hL))
  · -- `L_k` is 1 modulo 3
    have h3 : (3 : ℤ) ∣ 3 ^ (2 * k + 1) - 3 ^ (k + 1) :=
      dvd_sub (dvd_pow_self 3 (by omega)) (dvd_pow_self 3 (by omega))
    have hL' : (3 : ℤ) ∣ L3 k := by exact_mod_cast hL
    have h4 : (3 : ℤ) ∣ 1 := (dvd_add_right h3).1 hL'
    exact absurd h4 (by decide)

/-- If `a ∣ L`, `b ∣ M` and `L`, `M` are coprime, then `gcd(a b, L) = a`. -/
theorem gcd_mul_eq_left {a b L M : ℤ} (ha : 0 ≤ a) (haL : a ∣ L) (hbM : b ∣ M)
    (hLM : IsCoprime L M) : (Int.gcd (a * b) L : ℤ) = a := by
  have hLb : IsCoprime L b := hLM.of_isCoprime_of_dvd_right hbM
  have hg : IsCoprime (Int.gcd (a * b) L : ℤ) b :=
    hLb.of_isCoprime_of_dvd_left (Int.gcd_dvd_right _ _)
  have h1 : (Int.gcd (a * b) L : ℤ) ∣ a := hg.dvd_of_dvd_mul_right (Int.gcd_dvd_left _ _)
  have h2 : a ∣ (Int.gcd (a * b) L : ℤ) := Int.dvd_coe_gcd (dvd_mul_right a b) haL
  exact Int.dvd_antisymm (Int.natCast_nonneg _) ha h1 h2

/-- The half of `Φ_{6E}(3)` in the Aurifeuillian factor `L_E = 3^E - 3^((E+1)/2) + 1`. -/
noncomputable def halfL (E : ℕ) : ℤ := Int.gcd (Phi6 E) (3 ^ E - 3 ^ ((E + 1) / 2) + 1)

/-- The half of `Φ_{6E}(3)` in the Aurifeuillian factor `M_E = 3^E + 3^((E+1)/2) + 1`. -/
noncomputable def halfM (E : ℕ) : ℤ := Int.gcd (Phi6 E) (3 ^ E + 3 ^ ((E + 1) / 2) + 1)

theorem halfL_eq (k : ℕ) : halfL (2 * k + 1) = Int.gcd (Phi6 (2 * k + 1)) (L3 k) := by
  have e : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  rw [halfL, e]
  rfl

theorem halfM_eq (k : ℕ) : halfM (2 * k + 1) = Int.gcd (Phi6 (2 * k + 1)) (M3 k) := by
  have e : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  rw [halfM, e]
  rfl

theorem halfL_dvd (k : ℕ) : halfL (2 * k + 1) ∣ L3 k := by
  rw [halfL_eq]
  exact Int.gcd_dvd_right _ _

theorem halfM_dvd (k : ℕ) : halfM (2 * k + 1) ∣ M3 k := by
  rw [halfM_eq]
  exact Int.gcd_dvd_right _ _

/-- The two halves are coprime. -/
theorem isCoprime_halfL_halfM (k : ℕ) : IsCoprime (halfL (2 * k + 1)) (halfM (2 * k + 1)) :=
  ((isCoprime_L3_M3 k).of_isCoprime_of_dvd_left (halfL_dvd k)).of_isCoprime_of_dvd_right
    (halfM_dvd k)

/-- **The two halves.** For odd `E` the numbers `gcd(Φ_{6E}(3), L_E)` and `gcd(Φ_{6E}(3), M_E)`
are positive, their product is `Φ_{6E}(3)`, and their logarithms are values of the class
F3. -/
theorem halves_facts {E : ℕ} (hE : Odd E) :
    halfL E * halfM E = Phi6 E ∧ 0 < halfL E ∧ 0 < halfM E ∧
      IsF3Value (Real.log ((halfL E : ℤ) : ℝ)) ∧ IsF3Value (Real.log ((halfM E : ℤ) : ℝ)) := by
  obtain ⟨a, m, h3, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hE.pos.ne' 3 (by norm_num)
  have hm : Odd m := (Nat.odd_mul.1 hE).2
  have hm0 : 0 < m := hm.pos
  obtain ⟨k, hk⟩ := hE
  have hbig : (1 : ℤ) < 3 ^ 3 ^ a := one_lt_pow₀ (by norm_num) (by positivity)
  have hnorm : ∀ i : ℕ, (wE ^ i * tE ^ 3 ^ a).norm = 3 ^ 3 ^ a := fun i => by
    rw [map_mul, map_pow, map_pow, norm_wE, norm_tE, one_pow, one_mul]
  -- the two norms
  obtain ⟨h1, hh1⟩ : ∃ h1 : ℤ, h1 = ((cyclotomic m Eis).eval (wE ^ 1 * tE ^ 3 ^ a)).norm :=
    ⟨_, rfl⟩
  obtain ⟨h2, hh2⟩ : ∃ h2 : ℤ, h2 = ((cyclotomic m Eis).eval (wE ^ 2 * tE ^ 3 ^ a)).norm :=
    ⟨_, rfl⟩
  have hprod : h1 * h2 = Phi6 (3 ^ a * m) := by
    rw [hh1, hh2, pow_one]
    exact half_mul_half wE_rel norm_wE a hm h3
  have hpos : ∀ i : ℕ, 0 < ((cyclotomic m Eis).eval (wE ^ i * tE ^ 3 ^ a)).norm := fun i =>
    lt_of_le_of_ne (eis_norm_nonneg _)
      (Ne.symm (norm_eval_cyclotomic_ne_zero3 (by rw [hnorm]; exact hbig) hm0))
  have hp1 : 0 < h1 := hh1 ▸ hpos 1
  have hp2 : 0 < h2 := hh2 ▸ hpos 2
  -- their logarithms are values
  have hV : ∀ i : ℕ, ¬ 3 ∣ i → IsF3Value
      (Real.log ((((cyclotomic m Eis).eval (wE ^ i * tE ^ 3 ^ a)).norm : ℤ) : ℝ)) := by
    intro i hi
    refine isF3Value_log_norm_cyclotomic (by rw [hnorm]; exact hbig) (P := fun d => d ∣ m)
      (fun n d hn hd => hd.trans hn) (fun d _ hdm => ?_) m hm0 dvd_rfl
    have e : (wE ^ i * tE ^ 3 ^ a) ^ d = wE ^ (i * d) * tE ^ (3 ^ a * d) := by
      rw [mul_pow, ← pow_mul, ← pow_mul]
    rw [e]
    refine isF3Value_log_int (norm_pow_mem (fun h => ?_)
      ((Odd.pow (by decide)).mul (hm.of_dvd_nat hdm)))
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · exact hi h
    · exact h3 (h.trans hdm)
  have hV1 : IsF3Value (Real.log ((h1 : ℤ) : ℝ)) := hh1 ▸ hV 1 (by norm_num)
  have hV2 : IsF3Value (Real.log ((h2 : ℤ) : ℝ)) := hh2 ▸ hV 2 (by norm_num)
  -- each divides one of `L_k`, `M_k`
  have hd : ∀ i : ℕ, ((cyclotomic m Eis).eval (wE ^ i * tE ^ 3 ^ a)).norm ∣
      (wE ^ (i * m % 3) * tE ^ (2 * k + 1) - 1).norm := by
    intro i
    have e : (wE ^ i * tE ^ 3 ^ a) ^ m = wE ^ (i * m % 3) * tE ^ (2 * k + 1) := by
      rw [mul_pow, ← pow_mul, ← pow_mul, hk, wE_pow_mod (i * m)]
    rw [← e]
    exact norm_eval_cyclotomic_dvd3 _ hm0
  have hdiv : (h1 ∣ L3 k ∧ h2 ∣ M3 k) ∨ (h1 ∣ M3 k ∧ h2 ∣ L3 k) := by
    have hd1 := hd 1
    have hd2 := hd 2
    rw [← hh1] at hd1
    rw [← hh2] at hd2
    rcases (by omega : m % 3 = 1 ∨ m % 3 = 2) with hm3 | hm3
    · rw [show 1 * m % 3 = 1 by omega, pow_one] at hd1
      rw [show 2 * m % 3 = 2 by omega] at hd2
      rcases norm_w_tE_cases k with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact Or.inl ⟨e1 ▸ hd1, e2 ▸ hd2⟩
      · exact Or.inr ⟨e1 ▸ hd1, e2 ▸ hd2⟩
    · rw [show 1 * m % 3 = 2 by omega] at hd1
      rw [show 2 * m % 3 = 1 by omega, pow_one] at hd2
      rcases norm_w_tE_cases k with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact Or.inr ⟨e2 ▸ hd1, e1 ▸ hd2⟩
      · exact Or.inl ⟨e2 ▸ hd1, e1 ▸ hd2⟩
  rw [hk] at hprod ⊢
  have hcop := isCoprime_L3_M3 k
  rcases hdiv with ⟨hL, hM⟩ | ⟨hM, hL⟩
  · have eL : halfL (2 * k + 1) = h1 := by
      rw [halfL_eq, ← hprod]
      exact gcd_mul_eq_left hp1.le hL hM hcop
    have eM : halfM (2 * k + 1) = h2 := by
      rw [halfM_eq, ← hprod, mul_comm]
      exact gcd_mul_eq_left hp2.le hM hL hcop.symm
    rw [eL, eM]
    exact ⟨hprod, hp1, hp2, hV1, hV2⟩
  · have eL : halfL (2 * k + 1) = h2 := by
      rw [halfL_eq, ← hprod, mul_comm]
      exact gcd_mul_eq_left hp2.le hL hM hcop
    have eM : halfM (2 * k + 1) = h1 := by
      rw [halfM_eq, ← hprod]
      exact gcd_mul_eq_left hp1.le hM hL hcop.symm
    rw [eL, eM]
    exact ⟨by rw [mul_comm]; exact hprod, hp2, hp1, hV2, hV1⟩

/-! ## 3. Prime divisors of `Φ_n(3)` -/

theorem homogeneous_eq_cyclotomic3 (n : ℕ) :
    TauCeti.homogeneousCyclotomic n ((3 : ℕ) : ℤ) ((1 : ℕ) : ℤ) = (cyclotomic n ℤ).eval 3 := by
  rw [Nat.cast_ofNat, Nat.cast_one, TauCeti.homogeneousCyclotomic_one_right]

theorem not_dvd_one_int3 {p : ℕ} (hp : p.Prime) : ¬ (p : ℤ) ∣ ((1 : ℕ) : ℤ) := by
  norm_cast
  exact hp.not_dvd_one

/-- If 3 has order `n` modulo the prime `p`, then `p ∣ Φ_n(3)`. -/
theorem dvd_cyclotomic_of_orderOf3 {p n : ℕ} (hp : p.Prime) (hn : 0 < n)
    (h : orderOf (3 : ZMod p) = n) : (p : ℤ) ∣ (cyclotomic n ℤ).eval 3 := by
  have := Fact.mk hp
  have hprim : IsPrimitiveRoot (3 : ZMod p) n := by rw [← h]; exact IsPrimitiveRoot.orderOf 3
  have hroot := hprim.isRoot_cyclotomic hn
  rw [IsRoot.def, ← map_cyclotomic_int n (ZMod p)] at hroot
  have e := eval_intCast_map (Int.castRingHom (ZMod p)) (cyclotomic n ℤ) 3
  rw [Int.cast_ofNat, hroot] at e
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 e.symm

/-- A prime divisor of `Φ_n(3)` that does not divide `n` has order `n`. -/
theorem orderOf_three_of_not_dvd {n q : ℕ} (hn : 0 < n) (hq : q.Prime)
    (hdvd : (q : ℤ) ∣ (cyclotomic n ℤ).eval 3) (hqn : ¬ q ∣ n) :
    orderOf (3 : ZMod q) = n := by
  have hdvd' := (homogeneous_eq_cyclotomic3 n).symm ▸ hdvd
  have h := (hq.dvd_homogeneousCyclotomic_iff_orderOf_eq (not_dvd_one_int3 hq) hn.ne').1 hdvd'
  rw [(Nat.ordCompl_eq_self_iff_zero_or_not_dvd n hq).2 (Or.inr hqn)] at h
  simpa using h

/-- Every prime factor of `n` is at most any prime divisor of `Φ_n(3)`. So at most one prime
divisor of `Φ_n(3)` divides `n`: the largest prime factor of `n`. -/
theorem le_of_dvd_cyclotomic3 {n p q : ℕ} (hp : p.Prime)
    (hdvd : (p : ℤ) ∣ (cyclotomic n ℤ).eval 3) (hq : q.Prime) (hqn : q ∣ n) : q ≤ p :=
  hp.le_of_dvd_homogeneousCyclotomic_of_prime_of_dvd (not_dvd_one_int3 hp)
    ((homogeneous_eq_cyclotomic3 n).symm ▸ hdvd) hq hqn

/-- The order of 3 modulo a prime is never 2: `3^2 - 1 = 2^3`, and 3 has order 1 modulo 2. -/
theorem orderOf_three_ne_two {p : ℕ} (hp : p.Prime) : orderOf (3 : ZMod p) ≠ 2 := by
  intro h
  have h1 : (p : ℤ) ∣ 3 ^ 2 - 1 := (dvd_pow_sub_one_iff p 2).2 (by rw [h])
  have h2 : (p : ℤ) ∣ ((2 ^ 3 : ℕ) : ℤ) := by
    norm_num at h1 ⊢
    exact h1
  have h3 : p ∣ 2 ^ 3 := by exact_mod_cast h2
  obtain rfl := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h3)
  rw [orderOf_three_zmod_two] at h
  omega

/-- A prime factor of `n` divides `Φ_n(3)` at most once (`n ≠ 2`). -/
theorem not_sq_dvd_cyclotomic3 {n q : ℕ} (hq : q.Prime) (hqn : q ∣ n) (hn2 : n ≠ 2) :
    ¬ (q : ℤ) ^ 2 ∣ (cyclotomic n ℤ).eval 3 := by
  intro hsq
  have hdvd : (q : ℤ) ∣ (cyclotomic n ℤ).eval 3 := (dvd_pow_self _ two_ne_zero).trans hsq
  have hmul := hq.multiplicity_homogeneousCyclotomic_eq_one (a := 3) (b := 1)
    (by norm_num) hq.not_dvd_one hqn hn2 ((homogeneous_eq_cyclotomic3 _).symm ▸ hdvd)
  rw [homogeneous_eq_cyclotomic3] at hmul
  have hfin : FiniteMultiplicity (q : ℤ) ((cyclotomic n ℤ).eval 3) :=
    FiniteMultiplicity.of_prime_left (Nat.prime_iff_prime_int.1 hq)
      (cyclotomic_pos' _ (by norm_num)).ne'
  exact hfin.not_pow_dvd_of_multiplicity_lt (by rw [hmul]; norm_num) hsq

/-! ## 4. The primitive part that contains `p` -/

open Classical in
/-- The primitive part that contains the prime `p`: with `n` the order of 3 modulo `p`, it is
`Φ_n(3)` if `n` is not 6 modulo 12, and for `n = 6E`, `E` odd, the one of
`gcd(Φ_n(3), L_E)`, `gcd(Φ_n(3), M_E)` that `p` divides. -/
noncomputable def primPart3 (p : ℕ) : ℤ :=
  if orderOf (3 : ZMod p) % 12 = 6 then
    (if (p : ℤ) ∣ halfL (orderOf (3 : ZMod p) / 6) then halfL (orderOf (3 : ZMod p) / 6)
    else halfM (orderOf (3 : ZMod p) / 6))
  else (cyclotomic (orderOf (3 : ZMod p)) ℤ).eval 3

theorem primPart3_eq_cyclotomic {p n : ℕ} (hord : orderOf (3 : ZMod p) = n)
    (h : n % 12 ≠ 6) : primPart3 p = (cyclotomic n ℤ).eval 3 := by
  subst hord
  simp only [primPart3, h, ↓reduceIte]

theorem primPart3_eq_halfL {p n E : ℕ} (hord : orderOf (3 : ZMod p) = n) (h : n % 12 = 6)
    (hE : n / 6 = E) (hdvd : (p : ℤ) ∣ halfL E) : primPart3 p = halfL E := by
  subst hord hE
  simp only [primPart3, h, hdvd, ↓reduceIte]

theorem primPart3_eq_halfM {p n E : ℕ} (hord : orderOf (3 : ZMod p) = n) (h : n % 12 = 6)
    (hE : n / 6 = E) (hdvd : ¬ (p : ℤ) ∣ halfL E) : primPart3 p = halfM E := by
  subst hord hE
  simp only [primPart3, h, hdvd, ↓reduceIte]

/-- The facts about the primitive part, for a prime `p ≠ 3`: it divides `Φ_n(3)`, it is
positive and `p` divides it; and its logarithm is a value of the class F3. -/
theorem primPart3_facts {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) :
    primPart3 p ∣ (cyclotomic (orderOf (3 : ZMod p)) ℤ).eval 3 ∧ 0 < primPart3 p ∧
      (p : ℤ) ∣ primPart3 p ∧ IsF3Value (Real.log ((primPart3 p : ℤ) : ℝ)) := by
  obtain ⟨n, hord⟩ : ∃ n, orderOf (3 : ZMod p) = n := ⟨_, rfl⟩
  have hn : 0 < n := hord ▸ orderOf_three_pos hp hp3
  have hΦpos : 0 < (cyclotomic n ℤ).eval 3 := cyclotomic_pos' n (by norm_num)
  have hpΦ : (p : ℤ) ∣ (cyclotomic n ℤ).eval 3 := dvd_cyclotomic_of_orderOf3 hp hn hord
  rw [hord]
  by_cases h12 : n % 12 = 6
  · obtain ⟨E, hE⟩ : ∃ E, n / 6 = E := ⟨_, rfl⟩
    have hnE : 6 * E = n := by omega
    have hodd : Odd E := Nat.odd_iff.2 (by omega)
    obtain ⟨hmul, hL, hM, hVL, hVM⟩ := halves_facts hodd
    have hmul' : halfL E * halfM E = (cyclotomic n ℤ).eval 3 := by rw [hmul, Phi6, hnE]
    by_cases hdvd : (p : ℤ) ∣ halfL E
    · rw [primPart3_eq_halfL hord h12 hE hdvd]
      exact ⟨⟨_, hmul'.symm⟩, hL, hdvd, hVL⟩
    · rw [primPart3_eq_halfM hord h12 hE hdvd]
      refine ⟨⟨halfL E, by rw [← hmul', mul_comm]⟩, hM, ?_, hVM⟩
      rw [← hmul'] at hpΦ
      exact ((Nat.prime_iff_prime_int.1 hp).dvd_or_dvd hpΦ).resolve_left hdvd
  · rw [primPart3_eq_cyclotomic hord h12]
    exact ⟨dvd_rfl, hΦpos, hpΦ, isF3Value_log_cyclotomic_three n hn⟩

/-- The logarithm of the primitive part that contains `p` is a value of the class F3. -/
theorem isF3Value_log_primPart3 {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) :
    IsF3Value (Real.log ((primPart3 p : ℤ) : ℝ)) :=
  (primPart3_facts hp hp3).2.2.2

/-- **The prime factors of the primitive part.** Let `n` be the order of 3 modulo `p`. A prime
factor `q` of the primitive part that contains `p` either has order `n` too, or it divides
`n`; in the second case it is the largest prime factor of `n` and divides the primitive part
exactly once. -/
theorem primPart3_prime_factor {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) {q : ℕ} (hq : q.Prime)
    (hqg : (q : ℤ) ∣ primPart3 p) :
    orderOf (3 : ZMod q) = orderOf (3 : ZMod p) ∨
      (q ∣ orderOf (3 : ZMod p) ∧ (∀ r : ℕ, r.Prime → r ∣ orderOf (3 : ZMod p) → r ≤ q) ∧
        ¬ (q : ℤ) ^ 2 ∣ primPart3 p) := by
  have hgΦ := (primPart3_facts hp hp3).1
  by_cases hqn : q ∣ orderOf (3 : ZMod p)
  · exact Or.inr ⟨hqn, fun r hr hrn => le_of_dvd_cyclotomic3 hq (hqg.trans hgΦ) hr hrn,
      fun hsq => not_sq_dvd_cyclotomic3 hq hqn (orderOf_three_ne_two hp) (hsq.trans hgΦ)⟩
  · exact Or.inl (orderOf_three_of_not_dvd (orderOf_three_pos hp hp3) hq (hqg.trans hgΦ) hqn)

/-! ## 5. A second primitive prime excludes `p` -/

/-- **A partner excludes `p`** (from Baker's theorem). Let `p ≠ 3` be a prime and `n` the
order of 3 modulo `p`. If a prime `q ≠ p` that does not divide `n` divides the primitive part
that contains `p`, then `log p` is not a value of the class F3. -/
theorem not_isF3Value_log_of_partner (hB : BakerTheorem) {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) (hqg : (q : ℤ) ∣ primPart3 p)
    (hqn : ¬ q ∣ orderOf (3 : ZMod p)) : ¬ IsF3Value (Real.log p) := by
  obtain ⟨hgΦ, -, hpg, -⟩ := primPart3_facts hp hp3
  have hn : 0 < orderOf (3 : ZMod p) := orderOf_three_pos hp hp3
  have hordq : orderOf (3 : ZMod q) = orderOf (3 : ZMod p) :=
    orderOf_three_of_not_dvd hn hq (hqg.trans hgΦ) hqn
  refine not_isF3Value_log_of_same_part hB hp hq hqp hp3 hordq fun j hj => ?_
  have h12 : orderOf (3 : ZMod p) % 12 = 6 := by omega
  have hE : orderOf (3 : ZMod p) / 6 = 2 * j + 1 := by omega
  by_cases hdvd : (p : ℤ) ∣ halfL (2 * j + 1)
  · rw [primPart3_eq_halfL rfl h12 hE hdvd] at hqg
    exact Or.inl ⟨hdvd.trans (halfL_dvd j), hqg.trans (halfL_dvd j)⟩
  · rw [primPart3_eq_halfM rfl h12 hE hdvd] at hqg hpg
    exact Or.inr ⟨hpg.trans (halfM_dvd j), hqg.trans (halfM_dvd j)⟩

/-! ## 6. The test -/

/-- If the logarithms of the prime factors of `H` are values of the class F3, so is
`log H`. -/
theorem isF3Value_log_of_primeFactors : ∀ H : ℕ, 0 < H →
    (∀ q : ℕ, q.Prime → q ∣ H → IsF3Value (Real.log q)) → IsF3Value (Real.log H) := by
  intro H
  induction H using Nat.strong_induction_on with
  | _ H ih =>
    intro hH h
    rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hH) with h1 | h1
    · rw [← h1]
      simpa using isF3Value_zero
    · have hp := Nat.minFac_prime (by omega : H ≠ 1)
      obtain ⟨m, hm⟩ := Nat.minFac_dvd H
      have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; omega)
      have hlt : m < H := by
        calc m = 1 * m := (one_mul m).symm
          _ < H.minFac * m := Nat.mul_lt_mul_of_pos_right hp.one_lt hm0
          _ = H := hm.symm
      have e : (H : ℝ) = (H.minFac : ℝ) * (m : ℝ) := by exact_mod_cast hm
      have hlog : Real.log (H : ℝ) = Real.log (H.minFac : ℝ) + Real.log (m : ℝ) := by
        rw [e, Real.log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hm0.ne')]
      rw [hlog]
      exact (h _ hp (Nat.minFac_dvd H)).add
        (ih m hlt hm0 fun q hq hqm => h q hq (hqm.trans ⟨H.minFac, by rw [mul_comm]; exact hm⟩))

/-- **The finite test for a prime in base 3** (from Baker's theorem). Let `p ≠ 3` be a prime
and `n` the order of 3 modulo `p`. Then `log p` is a value of the class F3 if and only if
every prime `q ≠ p` dividing the primitive part that contains `p` divides `n` and has `log q`
a value of the class F3. -/
theorem isF3Value_log_prime_iff (hB : BakerTheorem) {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) :
    IsF3Value (Real.log p) ↔ ∀ q : ℕ, q.Prime → (q : ℤ) ∣ primPart3 p → q ≠ p →
      q ∣ orderOf (3 : ZMod p) ∧ IsF3Value (Real.log q) := by
  obtain ⟨hgΦ, hgpos, hpg, hVg⟩ := primPart3_facts hp hp3
  obtain ⟨G, hG⟩ := Int.eq_ofNat_of_zero_le hgpos.le
  rw [hG] at hgΦ hgpos hpg hVg
  have hG0 : 0 < G := by exact_mod_cast hgpos
  have hpG : p ∣ G := by exact_mod_cast hpg
  have hVG : IsF3Value (Real.log (G : ℝ)) := by exact_mod_cast hVg
  obtain ⟨a, H, hH, hGH⟩ := Nat.exists_eq_pow_mul_and_not_dvd hG0.ne' p hp.ne_one
  have hH0 : 0 < H := Nat.pos_of_ne_zero (by rintro rfl; exact hH (dvd_zero _))
  have ha : 0 < a := by
    rcases Nat.eq_zero_or_pos a with rfl | h
    · rw [pow_zero, one_mul] at hGH
      exact absurd (hGH ▸ hpG) hH
    · exact h
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hlog : Real.log (G : ℝ) = a * Real.log (p : ℝ) + Real.log (H : ℝ) := by
    rw [hGH]
    push_cast
    rw [Real.log_mul (pow_ne_zero _ hpR) (by exact_mod_cast hH0.ne'), Real.log_pow]
  have hdvdG : ∀ r : ℕ, (r : ℤ) ∣ primPart3 p ↔ r ∣ G := fun r => by
    rw [hG]
    exact Int.natCast_dvd_natCast
  constructor
  · intro hval q hq hqg hqp
    have hqG : q ∣ G := (hdvdG q).1 hqg
    -- every prime factor of `G` other than `p` divides `n`
    have hdvdn : ∀ r : ℕ, r.Prime → r ∣ G → r ≠ p → r ∣ orderOf (3 : ZMod p) := by
      intro r hr hrG hrp
      by_contra hrn
      exact not_isF3Value_log_of_partner hB hp hp3 hr hrp ((hdvdG r).2 hrG) hrn hval
    refine ⟨hdvdn q hq hqG hqp, ?_⟩
    have hΦ : ∀ r : ℕ, r ∣ G → (r : ℤ) ∣ (cyclotomic (orderOf (3 : ZMod p)) ℤ).eval 3 :=
      fun r hrG => (Int.natCast_dvd_natCast.2 hrG).trans hgΦ
    -- so every prime factor of `H` is `q`
    have hHq : ∀ {r : ℕ}, r.Prime → r ∣ H → r = q := by
      intro r hr hrH
      have hrp : r ≠ p := by
        rintro rfl
        exact hH hrH
      have hrG : r ∣ G := hGH ▸ Dvd.dvd.mul_left hrH _
      exact le_antisymm
        (le_of_dvd_cyclotomic3 hq (hΦ q hqG) hr (hdvdn r hr hrG hrp))
        (le_of_dvd_cyclotomic3 hr (hΦ r hrG) hq (hdvdn q hq hqG hqp))
    have hHpow := Nat.eq_prime_pow_of_unique_prime_dvd hH0.ne' hHq
    obtain ⟨b, hb⟩ : ∃ b, H.primeFactorsList.length = b := ⟨_, rfl⟩
    rw [hb] at hHpow
    have hqH : q ∣ H := by
      rw [hGH] at hqG
      rcases (Nat.Prime.dvd_mul hq).1 hqG with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h)) hqp
      · exact h
    have hb0 : 0 < b := by
      rcases Nat.eq_zero_or_pos b with rfl | h
      · rw [hHpow, pow_zero] at hqH
        exact absurd (Nat.dvd_one.1 hqH) hq.ne_one
      · exact h
    have hlogH : Real.log (H : ℝ) = b * Real.log (q : ℝ) := by
      rw [hHpow]
      push_cast
      rw [Real.log_pow]
    have h1 : IsF3Value ((b : ℝ) * Real.log (q : ℝ)) := by
      have h2 := hVG.sub (hval.const_mul (a : ℚ))
      rw [hlog, hlogH] at h2
      convert h2 using 1
      push_cast
      ring
    have h3 := h1.const_mul ((b : ℚ)⁻¹)
    have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb0.ne'
    convert h3 using 1
    push_cast
    field_simp
  · intro h
    have hHV : IsF3Value (Real.log (H : ℝ)) :=
      isF3Value_log_of_primeFactors H hH0 fun r hr hrH =>
        (h r hr ((hdvdG r).2 (hGH ▸ Dvd.dvd.mul_left hrH _))
          (by rintro rfl; exact hH hrH)).2
    have h1 : IsF3Value ((a : ℝ) * Real.log (p : ℝ)) := by
      have h2 := hVG.sub hHV
      rw [hlog] at h2
      convert h2 using 1
      ring
    have h3 := h1.const_mul ((a : ℚ)⁻¹)
    have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
    convert h3 using 1
    push_cast
    field_simp

/-- At most one prime other than `p` can pass the condition of the test: two primes that
divide the primitive part and the order `n` are equal. -/
theorem primPart3_intrinsic_unique {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) {r q : ℕ}
    (hr : r.Prime) (hq : q.Prime) (hrg : (r : ℤ) ∣ primPart3 p) (hqg : (q : ℤ) ∣ primPart3 p)
    (hrn : r ∣ orderOf (3 : ZMod p)) (hqn : q ∣ orderOf (3 : ZMod p)) : r = q :=
  le_antisymm
    (le_of_dvd_cyclotomic3 hq (hqg.trans (primPart3_facts hp hp3).1) hr hrn)
    (le_of_dvd_cyclotomic3 hr (hrg.trans (primPart3_facts hp hp3).1) hq hqn)

/-- **The test in the form of the note** (from Baker's theorem). For a prime `p ≠ 3`, with `n`
the order of 3 modulo `p`: `log p` is a value of the class F3 if and only if the primitive
part that contains `p` is a power of `p`, or a power of `p` times one prime `q` that divides
`n` and has `log q` a value of the class F3. -/
theorem isF3Value_log_prime_iff_explicit (hB : BakerTheorem) {p : ℕ} (hp : p.Prime)
    (hp3 : p ≠ 3) :
    IsF3Value (Real.log p) ↔ (∃ x : ℕ, primPart3 p = (p : ℤ) ^ x) ∨
      ∃ x q : ℕ, q.Prime ∧ q ∣ orderOf (3 : ZMod p) ∧ primPart3 p = (p : ℤ) ^ x * q ∧
        IsF3Value (Real.log q) := by
  rw [isF3Value_log_prime_iff hB hp hp3]
  obtain ⟨hgΦ, hgpos, -, -⟩ := primPart3_facts hp hp3
  constructor
  · intro C
    obtain ⟨G, hG⟩ := Int.eq_ofNat_of_zero_le hgpos.le
    have hG0 : 0 < G := by
      rw [hG] at hgpos
      exact_mod_cast hgpos
    obtain ⟨a, H, hH, hGH⟩ := Nat.exists_eq_pow_mul_and_not_dvd hG0.ne' p hp.ne_one
    have hH0 : 0 < H := Nat.pos_of_ne_zero (by rintro rfl; exact hH (dvd_zero _))
    have hHg : ∀ r : ℕ, r ∣ H → (r : ℤ) ∣ primPart3 p := by
      intro r hrH
      rw [hG, hGH]
      exact Int.natCast_dvd_natCast.2 (Dvd.dvd.mul_left hrH _)
    have hC : ∀ r : ℕ, r.Prime → r ∣ H →
        r ∣ orderOf (3 : ZMod p) ∧ IsF3Value (Real.log r) := fun r hr hrH =>
      C r hr (hHg r hrH) (by rintro rfl; exact hH hrH)
    have hΦ : ∀ r : ℕ, r ∣ H → (r : ℤ) ∣ (cyclotomic (orderOf (3 : ZMod p)) ℤ).eval 3 :=
      fun r hrH => (hHg r hrH).trans hgΦ
    rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hH0) with h1 | h1
    · left
      refine ⟨a, ?_⟩
      rw [hG, hGH, ← h1]
      push_cast
      ring
    · right
      obtain ⟨q, hqdef⟩ : ∃ q, H.minFac = q := ⟨_, rfl⟩
      have hq : q.Prime := hqdef ▸ Nat.minFac_prime (by omega : H ≠ 1)
      have hqH : q ∣ H := hqdef ▸ Nat.minFac_dvd H
      obtain ⟨hqn, hqV⟩ := hC q hq hqH
      have hHq : ∀ {r : ℕ}, r.Prime → r ∣ H → r = q := fun {r} hr hrH =>
        le_antisymm (le_of_dvd_cyclotomic3 hq (hΦ q hqH) hr (hC r hr hrH).1)
          (le_of_dvd_cyclotomic3 hr (hΦ r hrH) hq hqn)
      have hHpow := Nat.eq_prime_pow_of_unique_prime_dvd hH0.ne' hHq
      obtain ⟨b, hb⟩ : ∃ b, H.primeFactorsList.length = b := ⟨_, rfl⟩
      rw [hb] at hHpow
      -- `q` divides `Φ_n(3)` exactly once
      have hb1 : b = 1 := by
        rcases (show b = 0 ∨ b = 1 ∨ 2 ≤ b by omega) with rfl | h | h
        · rw [pow_zero] at hHpow
          omega
        · exact h
        · exfalso
          have h2 : q ^ 2 ∣ H := by
            rw [hHpow]
            exact pow_dvd_pow q h
          have h3 := hΦ (q ^ 2) h2
          exact not_sq_dvd_cyclotomic3 hq hqn (orderOf_three_ne_two hp) (by simpa using h3)
      refine ⟨a, q, hq, hqn, ?_, hqV⟩
      rw [hG, hGH, hHpow, hb1]
      push_cast
      ring
  · rintro (⟨x, hx⟩ | ⟨x, q0, hq0, hq0n, hx, hV⟩) q hq hqg hqp
    · exfalso
      rw [hx] at hqg
      have h1 : q ∣ p ^ x := by exact_mod_cast hqg
      exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h1))
    · rw [hx] at hqg
      have h1 : q ∣ p ^ x * q0 := by exact_mod_cast hqg
      rcases (Nat.Prime.dvd_mul hq).1 h1 with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h)) hqp
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hq hq0).1 h
        exact ⟨hq0n, hV⟩

/-- **The classification of the primes in base 3** (from Baker's theorem). For a prime `p`,
`log p` is a value of the class F3 if and only if `p = 3` or `p` passes the test: every prime
`q ≠ p` dividing the primitive part that contains `p` divides the order of 3 modulo `p` and
has `log q` a value of the class F3. -/
theorem isF3Value_log_prime_classification (hB : BakerTheorem) {p : ℕ} (hp : p.Prime) :
    IsF3Value (Real.log p) ↔ p = 3 ∨
      ∀ q : ℕ, q.Prime → (q : ℤ) ∣ primPart3 p → q ≠ p →
        q ∣ orderOf (3 : ZMod p) ∧ IsF3Value (Real.log q) := by
  by_cases hp3 : p = 3
  · subst hp3
    exact ⟨fun _ => Or.inl rfl, fun _ => by simpa using isF3Value_log_three⟩
  · rw [isF3Value_log_prime_iff hB hp hp3]
    exact ⟨Or.inr, fun h => h.resolve_left hp3⟩

/-! ## 7. Examples -/

/-- `31 = (3^5 - 3^3 + 1) / 7`. -/
theorem isF3Value_log_31 : IsF3Value (Real.log 31) := by
  have h0 := isF3Value_log_int (g := 217) (Or.inr (Or.inr (Or.inl ⟨2, by norm_num⟩)))
  have h := h0.sub isF3Value_log_7
  have e : Real.log ((217 : ℤ) : ℝ) - Real.log 7 = Real.log 31 := by
    rw [show ((217 : ℤ) : ℝ) = 31 * 7 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  rwa [e] at h

/-- `41 = (3^8 - 1) / (2^5 · 5)`. -/
theorem isF3Value_log_41 : IsF3Value (Real.log 41) := by
  have h0 := isF3Value_log_int (g := 6560) (Or.inr (Or.inl ⟨8, by norm_num, by norm_num⟩))
  have h := (h0.sub (isF3Value_log_2.const_mul 5)).sub isF3Value_log_5
  have e : Real.log ((6560 : ℤ) : ℝ) - ((5 : ℚ) : ℝ) * Real.log 2 - Real.log 5 =
      Real.log 41 := by
    rw [show ((6560 : ℤ) : ℝ) = 41 * 2 ^ 5 * 5 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    push_cast
    ring
  rwa [e] at h

/-- `43 = (3^7 - 3^4 + 1) / 7^2`. -/
theorem isF3Value_log_43 : IsF3Value (Real.log 43) := by
  have h0 := isF3Value_log_int (g := 2107) (Or.inr (Or.inr (Or.inl ⟨3, by norm_num⟩)))
  have h := h0.sub (isF3Value_log_7.const_mul 2)
  have e : Real.log ((2107 : ℤ) : ℝ) - ((2 : ℚ) : ℝ) * Real.log 7 = Real.log 43 := by
    rw [show ((2107 : ℤ) : ℝ) = 43 * 7 ^ 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast
    ring
  rwa [e] at h

/-- `61 = (3^10 - 1) / (2^3 · 11^2)`. -/
theorem isF3Value_log_61 : IsF3Value (Real.log 61) := by
  have h0 := isF3Value_log_int (g := 59048) (Or.inr (Or.inl ⟨10, by norm_num, by norm_num⟩))
  have h := (h0.sub (isF3Value_log_2.const_mul 3)).sub (isF3Value_log_11.const_mul 2)
  have e : Real.log ((59048 : ℤ) : ℝ) - ((3 : ℚ) : ℝ) * Real.log 2 -
      ((2 : ℚ) : ℝ) * Real.log 11 = Real.log 61 := by
    rw [show ((59048 : ℤ) : ℝ) = 61 * 2 ^ 3 * 11 ^ 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  rwa [e] at h

/-- `73 = (3^12 - 1) / (2^4 · 5 · 7 · 13)`. -/
theorem isF3Value_log_73 : IsF3Value (Real.log 73) := by
  have h0 := isF3Value_log_int (g := 531440)
    (Or.inr (Or.inl ⟨12, by norm_num, by norm_num⟩))
  have h := (((h0.sub (isF3Value_log_2.const_mul 4)).sub isF3Value_log_5).sub
    isF3Value_log_7).sub isF3Value_log_13
  have e : Real.log ((531440 : ℤ) : ℝ) - ((4 : ℚ) : ℝ) * Real.log 2 - Real.log 5 -
      Real.log 7 - Real.log 13 = Real.log 73 := by
    rw [show ((531440 : ℤ) : ℝ) = 73 * 2 ^ 4 * 5 * 7 * 13 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    push_cast
    ring
  rwa [e] at h

theorem orderOf_three_zmod_17 : orderOf (3 : ZMod 17) = 16 := by
  have h := orderOf_eq_prime_pow (x := (3 : ZMod 17)) (p := 2) (n := 3) (by decide) (by decide)
  simpa using h

theorem orderOf_three_zmod_193 : orderOf (3 : ZMod 193) = 16 := by
  have h := orderOf_eq_prime_pow (x := (3 : ZMod 193)) (p := 2) (n := 3) (by decide)
    (by decide)
  simpa using h

theorem orderOf_three_zmod_23 : orderOf (3 : ZMod 23) = 11 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide) (by decide)

theorem orderOf_three_zmod_3851 : orderOf (3 : ZMod 3851) = 11 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide) (by decide)

/-- **`log 17` is not a value of the class F3** (from Baker's theorem): 3 has order 16 modulo
17 and modulo 193, and `Φ_16(3) = 3^8 + 1 = 2 · 17 · 193`. -/
theorem not_isF3Value_log_17 (hB : BakerTheorem) : ¬ IsF3Value (Real.log 17) := by
  have h := not_isF3Value_log_of_same_part hB (p := 17) (q := 193) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by rw [orderOf_three_zmod_193, orderOf_three_zmod_17])
    (fun j hj => by rw [orderOf_three_zmod_17] at hj; omega)
  simpa using h

/-- **`log 23` is not a value of the class F3** (from Baker's theorem): 3 has order 11 modulo
23 and modulo 3851, and `Φ_11(3) = (3^11 - 1) / 2 = 23 · 3851`. -/
theorem not_isF3Value_log_23 (hB : BakerTheorem) : ¬ IsF3Value (Real.log 23) := by
  have h := not_isF3Value_log_of_same_part hB (p := 23) (q := 3851) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by rw [orderOf_three_zmod_3851, orderOf_three_zmod_23])
    (fun j hj => by rw [orderOf_three_zmod_23] at hj; omega)
  simpa using h

end Base3

end PiFormula
