/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.RatBase.SizeSmallAux

/-!
# The size condition for small rational bases: a checkable certificate

`certOK p q a b F rows` is a computable Boolean. When it is `true`, the size condition
`SizeCondR p q m` holds at every `m ≥ 3` with `(p, q, m)` outside `leftoverTriples`
(`sizeCondR_of_certOK`). The data: `a/b ≥ √(p q)`; a number `F` such that the analytic bound of
`SizeSmallAux.lean` gives the size condition for `φ(m) > F`; and `rows`, the list of the factored
forms of `m = 3, 4, …, M`, where `M` is such that `φ(m) ≤ F` forces `m ≤ M`.

A factored form is a list `[(ℓ₁, e₁), …, (ℓₖ, eₖ)]` of distinct primes with exponents `eᵢ ≥ 1`
(`wfF`); it stands for `m = ∏ ℓᵢ^eᵢ` (`prodF`). From it are computed `φ(m)` (`totF`) and
`Φ_m(a, b)` for `a > b` (`phiN`), by `Φ_1(a, b) = a - b` and, for a prime `ℓ ∤ n`,

  `Φ_{ℓ^e n}(a, b) = Φ_n(a^(ℓ^e), b^(ℓ^e)) / Φ_n(a^(ℓ^(e-1)), b^(ℓ^(e-1)))`.

A row `m` passes (`rowOK`) if `(p, q, m)` is in `leftoverTriples`, or the factored form is
correct and either `φ(m) > F` or the size condition is checked on the integers: with
`s = b (p + q) + 2 a`, `h = φ(m)/2` and `N = Φ_m(p, q)`, `s^h < N b^h`, and for each prime `ℓ` of
the factored form, `ℓ ∤ N` or `ℓ s^h < N b^h`.
-/

@[expose] public section

namespace PiFormula

namespace RatBase

/-! ## 1. Factored forms -/

/-- The number with the factored form `fm`: the product of the `ℓ^e` over `(ℓ, e)` in `fm`. -/
def prodF : List (ℕ × ℕ) → ℕ
  | [] => 1
  | x :: r => x.1 ^ x.2 * prodF r

/-- The totient of the number with the factored form `fm`. -/
def totF : List (ℕ × ℕ) → ℕ
  | [] => 1
  | x :: r => x.1 ^ (x.2 - 1) * (x.1 - 1) * totF r

/-- A factored form is well formed: primes (below 400), positive exponents, each prime not
dividing the product of the later prime powers. -/
def wfF : List (ℕ × ℕ) → Bool
  | [] => true
  | x :: r =>
    decide (x.1 ∈ smallPrimes) && decide (0 < x.2) && decide (prodF r % x.1 ≠ 0) && wfF r

/-- `Φ_m(a, b)` for `a > b`, computed from the factored form of `m`. -/
def phiN : List (ℕ × ℕ) → ℕ → ℕ → ℕ
  | [], a, b => a - b
  | x :: r, a, b =>
    phiN r (a ^ x.1 ^ x.2) (b ^ x.1 ^ x.2) / phiN r (a ^ x.1 ^ (x.2 - 1)) (b ^ x.1 ^ (x.2 - 1))

theorem of_wfF_cons {x : ℕ × ℕ} {r : List (ℕ × ℕ)} (h : wfF (x :: r) = true) :
    x.1.Prime ∧ 0 < x.2 ∧ ¬ x.1 ∣ prodF r ∧ wfF r = true := by
  simp only [wfF, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨prime_of_mem_smallPrimes h1, h2, fun hd => h3 (Nat.mod_eq_zero_of_dvd hd), h4⟩

/-- `phiN` computes the homogeneous cyclotomic value. -/
theorem cast_phiN {fm : List (ℕ × ℕ)} (hwf : wfF fm = true) {a b : ℕ} (hba : b < a) :
    ((phiN fm a b : ℕ) : ℤ) = TauCeti.homogeneousCyclotomic (prodF fm) (a : ℤ) (b : ℤ) := by
  induction fm generalizing a b with
  | nil => rw [phiN, prodF, TauCeti.homogeneousCyclotomic_one, Nat.cast_sub hba.le]
  | cons x r ih =>
    obtain ⟨hp, he, hnd, hr⟩ := of_wfF_cons hwf
    obtain ⟨e, he'⟩ : ∃ e, x.2 = e + 1 := ⟨x.2 - 1, by omega⟩
    have hlt : ∀ k : ℕ, b ^ x.1 ^ k < a ^ x.1 ^ k := fun k =>
      Nat.pow_lt_pow_left hba (pow_ne_zero _ hp.ne_zero)
    have h1 := ih hr (hlt (e + 1))
    have h2 := ih hr (hlt e)
    have hrec := TauCeti.homogeneousCyclotomic_prime_pow_mul_mul_homogeneousCyclotomic (R := ℤ)
      hp hnd e (a : ℤ) (b : ℤ)
    push_cast at h1 h2
    rw [← h1, ← h2] at hrec
    have hpos : (0 : ℤ) < ((phiN r (a ^ x.1 ^ e) (b ^ x.1 ^ e) : ℕ) : ℤ) := by
      rw [h2]
      refine TauCeti.homogeneousCyclotomic_pos (by positivity) ?_ _
      exact_mod_cast hlt e
    rw [phiN, prodF, he', Nat.add_sub_cancel, Int.natCast_div]
    exact Int.ediv_eq_of_eq_mul_left hpos.ne' hrec.symm

/-- `totF` computes the totient. -/
theorem totient_prodF {fm : List (ℕ × ℕ)} (hwf : wfF fm = true) :
    (prodF fm).totient = totF fm := by
  induction fm with
  | nil => simp [prodF, totF]
  | cons x r ih =>
    obtain ⟨hp, he, hnd, hr⟩ := of_wfF_cons hwf
    have hc : Nat.Coprime (x.1 ^ x.2) (prodF r) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd)
    rw [prodF, totF, Nat.totient_mul hc, Nat.totient_prime_pow hp he, ih hr]

/-- A prime divisor of the number with the factored form `fm` is one of the primes of `fm`. -/
theorem exists_mem_of_prime_dvd_prodF {fm : List (ℕ × ℕ)} (hwf : wfF fm = true) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (h : ℓ ∣ prodF fm) : ∃ x ∈ fm, x.1 = ℓ := by
  induction fm with
  | nil =>
    rw [prodF] at h
    exact absurd (Nat.dvd_one.1 h) hℓ.ne_one
  | cons x r ih =>
    obtain ⟨hp, he, hnd, hr⟩ := of_wfF_cons hwf
    rw [prodF] at h
    rcases (Nat.Prime.dvd_mul hℓ).1 h with h1 | h1
    · exact ⟨x, List.mem_cons_self,
        ((Nat.prime_dvd_prime_iff_eq hℓ hp).1 (hℓ.dvd_of_dvd_pow h1)).symm⟩
    · obtain ⟨y, hy, hy'⟩ := ih hr h1
      exact ⟨y, List.mem_cons_of_mem _ hy, hy'⟩

/-! ## 2. One row -/

/-- The check on the integers: `s^h < N b^h`, and for every prime `ℓ` of `fm`, `ℓ ∤ N` or
`ℓ s^h < N b^h`. -/
def directOK (s b N h : ℕ) (fm : List (ℕ × ℕ)) : Bool :=
  decide (s ^ h < N * b ^ h) &&
    fm.all fun x => decide (N % x.1 ≠ 0) || decide (x.1 * s ^ h < N * b ^ h)

/-- The check of the row `m` with the factored form `fm`. -/
def rowOK (p q a b F m : ℕ) (fm : List (ℕ × ℕ)) : Bool :=
  decide ((p, q, m) ∈ leftoverTriples) ||
    (wfF fm && decide (prodF fm = m) &&
      (decide (F < totF fm) ||
        (decide (totF fm % 2 = 0) &&
          directOK (b * (p + q) + 2 * a) b (phiN fm p q) (totF fm / 2) fm)))

/-- From the inequality on the integers to the inequality on the reals. -/
theorem mul_sqrt_add_sqrt_pow_lt_of_direct {p q a b h N L : ℕ} (hb : 0 < b)
    (hab : p * q * b ^ 2 ≤ a ^ 2) (hd : L * (b * (p + q) + 2 * a) ^ h < N * b ^ h) :
    (L : ℝ) * (Real.sqrt (p : ℝ) + Real.sqrt (q : ℝ)) ^ (2 * h) < (N : ℝ) := by
  have hS := sqrt_add_sqrt_sq_le (p := p) (q := q) hb hab
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hd' : (L : ℝ) * ((b * (p + q) + 2 * a : ℕ) : ℝ) ^ h < (N : ℝ) * (b : ℝ) ^ h := by
    exact_mod_cast hd
  generalize ((b * (p + q) + 2 * a : ℕ) : ℝ) = s at hd' hS
  calc (L : ℝ) * (Real.sqrt (p : ℝ) + Real.sqrt (q : ℝ)) ^ (2 * h)
      = L * ((Real.sqrt (p : ℝ) + Real.sqrt (q : ℝ)) ^ 2) ^ h := by rw [pow_mul]
    _ ≤ L * (s / b) ^ h :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sq_nonneg _) hS h) (Nat.cast_nonneg L)
    _ < N := by
        rw [div_pow, ← mul_div_assoc, div_lt_iff₀ (pow_pos hb' h)]
        exact hd'

/-- A row that passes gives the size condition, outside `leftoverTriples`. -/
theorem sizeCondR_of_rowOK {p q a b F m : ℕ} {fm : List (ℕ × ℕ)} (hq : 0 < q) (hqp : q < p)
    (hb : 0 < b) (hab : p * q * b ^ 2 ≤ a ^ 2)
    (hbase : (F + 2) ^ 2 * (b * (p + q) + 2 * a) ^ (F + 1) <
      ((p ^ 2 + q ^ 2 - p * q) * b) ^ (F + 1))
    (hstep : (F + 3) ^ 2 * (b * (p + q) + 2 * a) ≤ (F + 2) ^ 2 * ((p ^ 2 + q ^ 2 - p * q) * b))
    (hm : 3 ≤ m) (h : rowOK p q a b F m fm = true) (hmem : (p, q, m) ∉ leftoverTriples) :
    SizeCondR p q m := by
  simp only [rowOK, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | ⟨⟨hwf, hprod⟩, h⟩
  · exact absurd h hmem
  have htot := totient_prodF hwf
  rw [hprod] at htot
  rcases h with h | ⟨hev, hd⟩
  · exact sizeCondR_of_lt_totient hq hqp hb hab hbase hstep hm (by rw [htot]; exact h)
  · have hN := cast_phiN hwf hqp
    rw [hprod] at hN
    have hcv : ((cycValR p q m : ℤ) : ℝ) = ((phiN fm p q : ℕ) : ℝ) := by
      rw [cycValR, ← hN, Int.cast_natCast]
    have hcv' : cycValR p q m = ((phiN fm p q : ℕ) : ℤ) := hN.symm
    have ht : m.totient = 2 * (totF fm / 2) := by omega
    simp only [directOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      Bool.or_eq_true] at hd
    obtain ⟨hd1, hd2⟩ := hd
    refine ⟨?_, ?_⟩
    · have h1 := mul_sqrt_add_sqrt_pow_lt_of_direct (p := p) (q := q) (L := 1) hb hab
        (by rw [one_mul]; exact hd1)
      rw [Nat.cast_one, one_mul] at h1
      rw [hcv, ht]
      exact h1
    · intro ℓ hℓ hℓm hℓΦ
      rw [hcv'] at hℓΦ
      obtain ⟨x, hx, rfl⟩ := exists_mem_of_prime_dvd_prodF hwf hℓ (hprod ▸ hℓm)
      rcases hd2 x hx with h1 | h1
      · exact absurd (Nat.mod_eq_zero_of_dvd (Int.natCast_dvd_natCast.1 hℓΦ)) h1
      · rw [hcv, ht]
        exact mul_sqrt_add_sqrt_pow_lt_of_direct hb hab h1

/-! ## 3. All rows, and the certificate -/

/-- The check of the rows `m₀, m₀ + 1, …`, one factored form for each. -/
def rowsOK (p q a b F : ℕ) : ℕ → List (List (ℕ × ℕ)) → Bool
  | _, [] => true
  | m, fm :: rs => rowOK p q a b F m fm && rowsOK p q a b F (m + 1) rs

theorem exists_rowOK_of_rowsOK {p q a b F : ℕ} :
    ∀ {rows : List (List (ℕ × ℕ))} {m₀ : ℕ}, rowsOK p q a b F m₀ rows = true →
      ∀ m, m₀ ≤ m → m < m₀ + rows.length → ∃ fm, rowOK p q a b F m fm = true
  | [], m₀, _, m, h1, h2 => by
    simp only [List.length_nil] at h2
    omega
  | fm :: rs, m₀, h, m, h1, h2 => by
    rw [rowsOK, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | h3
    · exact ⟨fm, h.1⟩
    · refine exists_rowOK_of_rowsOK h.2 m h3 ?_
      simp only [List.length_cons] at h2
      omega

/-- The certificate for the pair `(p, q)`: `a/b ≥ √(p q)`, the two numerical conditions on `F`,
`φ(m) ≤ F` only for `m < 3 + rows.length`, and the rows `3, 4, …`. -/
def certOK (p q a b F : ℕ) (rows : List (List (ℕ × ℕ))) : Bool :=
  decide (0 < q) && decide (q < p) && decide (0 < b) && decide (p * q * b ^ 2 ≤ a ^ 2) &&
    decide ((F + 2) ^ 2 * (b * (p + q) + 2 * a) ^ (F + 1) <
      ((p ^ 2 + q ^ 2 - p * q) * b) ^ (F + 1)) &&
    decide ((F + 3) ^ 2 * (b * (p + q) + 2 * a) ≤ (F + 2) ^ 2 * ((p ^ 2 + q ^ 2 - p * q) * b)) &&
    decide (F + 2 ≤ 400) &&
    decide (F * (primesLt (F + 2)).prod <
      (3 + rows.length) * ((primesLt (F + 2)).map (· - 1)).prod) &&
    rowsOK p q a b F 3 rows

/-- **A certificate gives the size condition** at every `m ≥ 3` outside `leftoverTriples`. -/
theorem sizeCondR_of_certOK {p q a b F : ℕ} {rows : List (List (ℕ × ℕ))}
    (h : certOK p q a b F rows = true) {m : ℕ} (hm : 3 ≤ m)
    (hmem : (p, q, m) ∉ leftoverTriples) : SizeCondR p q m := by
  simp only [certOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hq, hqp⟩, hb⟩, hab⟩, hbase⟩, hstep⟩, hF⟩, hM⟩, hrows⟩ := h
  by_cases hlt : m < 3 + rows.length
  · obtain ⟨fm, hfm⟩ := exists_rowOK_of_rowsOK hrows m hm hlt
    exact sizeCondR_of_rowOK hq hqp hb hab hbase hstep hm hfm hmem
  · refine sizeCondR_of_lt_totient hq hqp hb hab hbase hstep hm ?_
    by_contra hcon
    have h1 := mul_prod_pred_le_of_totient_le hF (by omega) (not_lt.1 hcon)
    exact hlt (lt_of_mul_lt_mul_right (lt_of_le_of_lt h1 hM) (Nat.zero_le _))

/-- The data of a certificate for the pair `(p, q)`. -/
structure PairCert where
  /-- The numerator of the base. -/
  p : ℕ
  /-- The denominator of the base. -/
  q : ℕ
  /-- `a/b ≥ √(p q)`. -/
  a : ℕ
  /-- `a/b ≥ √(p q)`. -/
  b : ℕ
  /-- The analytic bound is used for `φ(m) > F`. -/
  F : ℕ
  /-- The factored forms of `m = 3, 4, …`. -/
  rows : List (List (ℕ × ℕ))

/-- The check of a certificate. -/
def PairCert.ok (c : PairCert) : Bool :=
  certOK c.p c.q c.a c.b c.F c.rows

end RatBase

end PiFormula
