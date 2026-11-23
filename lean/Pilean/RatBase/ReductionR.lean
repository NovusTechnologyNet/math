import Pilean.RatBase.ReductionRCyclo
import Pilean.RatBase.ReductionRRoots

/-!
# Rational bases: a good prime from the size condition

`hasGoodPrimeR_of_sizeCondR`: let `p > q ≥ 1` be coprime, let `r` be a root of unity with
`r⁴ ≠ 1`, and let `m ≥ 3` be the order of `r²`. If `SizeCondR p q m` holds, then `r` has a good
prime in the base `p/q`: a prime ideal of the algebraic integers that contains `√(pq) - q r`
and an odd rational prime dividing neither `p q` nor the order of `r`.

It is the proof of `BaseB.hasGoodPrimeB_of_sizeCond` with `u = √(pq)` for `√b` and
`x = u - q r` for `√b - r` (research note `research/2026-11-22-rational-bases/00_summary.md`,
section 3.3). No field norm and no Galois theory. Let `n = ord r`, `μ` the minimal polynomial
of `x` over `ℤ` and `c₀ = μ(0)`.

1. Every prime `ℓ ∣ c₀` lies under a prime ideal containing `x`
   (`BaseB.hasPrime_of_dvd_minpoly_eval_zero`).
2. There are integers `C`, `C'` with `C ∣ c₀²`, `q^(2 φ(n)) C C' = (Ψ(u) Ψ(-u))²` and
   `|C'| ≤ (√p + √q)^(2 φ(n))` (`exists_cofactorR`, file `ReductionRRoots`). Here
   `C = c₀² / q^(deg μ)`: the powers of `q` are removed from the constant term and from the
   cofactor separately, because the square of each root is `q` times an algebraic integer.
3. `Ψ(u) Ψ(-u) = q^φ(n) Φ_m(p, q)^k` and `φ(n) = k φ(m)` with `k ≥ 1` (`cycloScaled_value`,
   file `ReductionRCyclo`). So `C C' = Φ_m(p, q)^(2k)`.
4. A prime `ℓ ∣ C` divides `Φ_m(p, q)` and `c₀`. It does not divide `p q`. If `ℓ ∤ m`, then
   `p/q` has order `m` modulo `ℓ`: `ℓ ≡ 1 (mod m)`, `ℓ` is odd and `ℓ ∤ n`
   (`prime_facts_of_dvd_cycValR`). This is a good prime.
5. Otherwise every prime factor of `C` divides `m` and `Φ_m(p, q)`. Such a prime is the largest
   prime factor of `m`, and it divides `Φ_m(p, q)` exactly once (`nonprimitive_factsR`). So
   `|C| = 1` or `|C| = ℓ^j` with `j ≤ 2k`, and
   `Φ_m(p, q)^(2k) = |C| |C'| ≤ (ℓ (√p + √q)^φ(m))^(2k)`, against the size condition
   (`size_contradictionR`).
-/

open Complex Polynomial

namespace PiFormula

namespace RatBase

/-- `Φ_m(p, q) > 0` for `p > q ≥ 0`. -/
private theorem cycValR_pos {p q : ℕ} (hqp : q < p) (m : ℕ) : 0 < cycValR p q m :=
  TauCeti.homogeneousCyclotomic_pos (Int.natCast_nonneg q) (by exact_mod_cast hqp) m

/-- A prime factor `ℓ` of `Φ_m(p, q)`, `m ≥ 3`, `p` and `q` coprime, that does not divide `m`
is odd, does not divide `p q`, and is larger than `m`. -/
theorem prime_facts_of_dvd_cycValR {p q m ℓ : ℕ} (hcop : Nat.Coprime p q) (hm : 3 ≤ m)
    (hℓ : ℓ.Prime) (hdvd : (ℓ : ℤ) ∣ cycValR p q m) (hℓm : ¬ ℓ ∣ m) :
    ℓ ≠ 2 ∧ ¬ ℓ ∣ p * q ∧ m < ℓ := by
  have := Fact.mk hℓ
  have hdvd' : (ℓ : ℤ) ∣ TauCeti.homogeneousCyclotomic m (p : ℤ) (q : ℤ) := hdvd
  have hpq : ¬ ℓ ∣ p * q := hcop.not_dvd_mul_of_dvd_homogeneousCyclotomic hℓ hdvd'
  have hq1 : ¬ (ℓ : ℤ) ∣ (q : ℤ) := fun h =>
    hpq (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.1 h) p)
  have hord := (hℓ.dvd_homogeneousCyclotomic_iff_orderOf_eq hq1 (by omega : m ≠ 0)).1 hdvd'
  rw [(Nat.ordCompl_eq_self_iff_zero_or_not_dvd m hℓ).2 (Or.inr hℓm)] at hord
  have ha0 : (((p : ℤ) : ZMod ℓ) * ((q : ℤ) : ZMod ℓ)⁻¹) ≠ 0 := by
    intro h0
    have h1 := pow_orderOf_eq_one (((p : ℤ) : ZMod ℓ) * ((q : ℤ) : ZMod ℓ)⁻¹)
    rw [hord, h0, zero_pow (by omega)] at h1
    exact zero_ne_one h1
  have hd := ZMod.orderOf_dvd_card_sub_one ha0
  rw [hord] at hd
  have h2 := hℓ.two_le
  have hle := Nat.le_of_dvd (by omega) hd
  exact ⟨by omega, hpq, by omega⟩

/-- A prime factor `ℓ` of `Φ_m(p, q)`, `p > q` coprime, `m ≥ 3`, that divides `m` is at least
every prime factor of `m`, and `ℓ²` does not divide `Φ_m(p, q)`. -/
theorem nonprimitive_factsR {p q m ℓ : ℕ} (hqp : q < p) (hcop : Nat.Coprime p q) (hm : 3 ≤ m)
    (hℓ : ℓ.Prime) (hdvd : (ℓ : ℤ) ∣ cycValR p q m) (hℓm : ℓ ∣ m) :
    (∀ d : ℕ, d.Prime → d ∣ m → d ≤ ℓ) ∧ ¬ (ℓ : ℤ) ^ 2 ∣ cycValR p q m := by
  have hdvd' : (ℓ : ℤ) ∣ TauCeti.homogeneousCyclotomic m (p : ℤ) (q : ℤ) := hdvd
  have hpq : ¬ ℓ ∣ p * q := hcop.not_dvd_mul_of_dvd_homogeneousCyclotomic hℓ hdvd'
  have hq0 : ¬ ℓ ∣ q := fun h => hpq (dvd_mul_of_dvd_right h p)
  have hq1 : ¬ (ℓ : ℤ) ∣ (q : ℤ) := fun h => hq0 (Int.natCast_dvd_natCast.1 h)
  refine ⟨fun d hd hdm =>
    hℓ.le_of_dvd_homogeneousCyclotomic_of_prime_of_dvd hq1 hdvd' hd hdm, ?_⟩
  have hmul : multiplicity (ℓ : ℤ) (cycValR p q m) = 1 :=
    hℓ.multiplicity_homogeneousCyclotomic_eq_one hqp hq0 hℓm (by omega) hdvd'
  have hfin : FiniteMultiplicity (ℓ : ℤ) (cycValR p q m) :=
    FiniteMultiplicity.of_prime_left (Nat.prime_iff_prime_int.1 hℓ) (cycValR_pos hqp m).ne'
  exact hfin.not_pow_dvd_of_multiplicity_lt (by rw [hmul]; norm_num)

/-- **The size argument.** If `c h = Φ_m(p, q)^K` with `|h| ≤ (√p + √q)^(K φ(m))`, and every
prime factor of `c` divides `m`, the size condition fails. -/
theorem size_contradictionR {p q m K : ℕ} (hqp : q < p) (hcop : Nat.Coprime p q) (hm : 3 ≤ m)
    (hK : 0 < K) (hS : SizeCondR p q m) {c h : ℤ} (hch : c * h = cycValR p q m ^ K)
    (hbound : |(h : ℝ)| ≤ (Real.sqrt (p : ℝ) + Real.sqrt (q : ℝ)) ^ (K * m.totient))
    (hall : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ c → ℓ ∣ m) : False := by
  have hfacts := fun (ℓ : ℕ) (hℓ : ℓ.Prime) => nonprimitive_factsR (ℓ := ℓ) hqp hcop hm hℓ
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℤ, cycValR p q m = Φ := ⟨_, rfl⟩
  have hΦpos : 0 < Φ := hΦ ▸ cycValR_pos hqp m
  obtain ⟨hS1, hS2⟩ := hS
  rw [hΦ] at hch hS1 hS2 hfacts
  obtain ⟨s, hs⟩ : ∃ s : ℝ, (Real.sqrt (p : ℝ) + Real.sqrt (q : ℝ)) ^ m.totient = s := ⟨_, rfl⟩
  have hs0 : 0 < s := by
    rw [← hs]
    have h1 : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < p))
    have h2 := Real.sqrt_nonneg (q : ℝ)
    positivity
  rw [pow_mul', hs] at hbound
  rw [hs] at hS1 hS2
  have hΦR : (0 : ℝ) < (Φ : ℝ) := by exact_mod_cast hΦpos
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hch
    exact (pow_pos hΦpos K).ne hch
  obtain ⟨N, hN⟩ : ∃ N : ℕ, c.natAbs = N := ⟨_, rfl⟩
  have hN0 : N ≠ 0 := hN ▸ Int.natAbs_ne_zero.2 hc0
  have hreal : (N : ℝ) * |(h : ℝ)| = (Φ : ℝ) ^ K := by
    have h1 : ((|c| * |h| : ℤ) : ℝ) = ((Φ ^ K : ℤ) : ℝ) := by
      rw [← abs_mul, hch, abs_of_pos (pow_pos hΦpos K)]
    rw [← hN]
    push_cast at h1 ⊢
    rw [← h1, Nat.cast_natAbs, Int.cast_abs]
  have hprime : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ N → ℓ ∣ m ∧ (ℓ : ℤ) ∣ Φ := by
    intro ℓ hℓ hℓN
    have hℓc : (ℓ : ℤ) ∣ c := Int.natCast_dvd.2 (hN ▸ hℓN)
    exact ⟨hall ℓ hℓ hℓc,
      (Nat.prime_iff_prime_int.1 hℓ).dvd_of_dvd_pow (hch ▸ Dvd.dvd.mul_right hℓc h)⟩
  by_cases hN1 : N = 1
  · -- `|c| = 1`
    rw [hN1, Nat.cast_one, one_mul] at hreal
    have h1 : s ^ K < (Φ : ℝ) ^ K := pow_lt_pow_left₀ hS1 hs0.le hK.ne'
    linarith
  · obtain ⟨ℓ, hℓ, hℓN⟩ := Nat.exists_prime_and_dvd hN1
    obtain ⟨hℓm, hℓΦ⟩ := hprime ℓ hℓ hℓN
    obtain ⟨hmax, hsq⟩ := hfacts ℓ hℓ hℓΦ hℓm
    have huniq : ∀ {d : ℕ}, d.Prime → d ∣ N → d = ℓ := by
      intro d hd hdN
      obtain ⟨hdm, hdΦ⟩ := hprime d hd hdN
      obtain ⟨hmax', -⟩ := hfacts d hd hdΦ hdm
      exact le_antisymm (hmax d hd hdm) (hmax' ℓ hℓ hℓm)
    obtain ⟨j, hj⟩ : ∃ j, N = ℓ ^ j := ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hN0 huniq⟩
    have hjK : j ≤ K := by
      by_contra hlt
      push Not at hlt
      apply BaseB.not_pow_succ_dvd_pow hℓ hsq K
      have h1 : (ℓ : ℤ) ^ (K + 1) ∣ (ℓ : ℤ) ^ j := pow_dvd_pow _ hlt
      have h2 : ((N : ℕ) : ℤ) ∣ Φ ^ K := by
        rw [← hch, ← hN]
        exact (Int.natAbs_dvd.2 dvd_rfl).mul_right h
      rw [hj] at h2
      push_cast at h2
      exact h1.trans h2
    have hsz := hS2 ℓ hℓ hℓm hℓΦ
    have hℓ1 : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ.one_le
    have hNle : (N : ℝ) ≤ (ℓ : ℝ) ^ K := by
      rw [hj]
      push_cast
      exact pow_le_pow_right₀ hℓ1 hjK
    have h1 : (Φ : ℝ) ^ K ≤ (ℓ : ℝ) ^ K * s ^ K := by
      rw [← hreal]
      exact mul_le_mul hNle hbound (abs_nonneg _) (by positivity)
    have h2 : ((ℓ : ℝ) * s) ^ K < (Φ : ℝ) ^ K :=
      pow_lt_pow_left₀ hsz (by positivity) hK.ne'
    rw [mul_pow] at h2
    linarith

/-- **A good prime from the size condition.** Let `p > q ≥ 1` be coprime and let `r` be a root
of unity with `r⁴ ≠ 1`. If the size condition holds at `(p, q, m)`, `m` the order of `r²`, then
`r` has a good prime in the base `p/q`. -/
theorem hasGoodPrimeR_of_sizeCondR {p q : ℕ} (hq : 0 < q) (hqp : q < p) (hcop : Nat.Coprime p q)
    {r : ℂ} (hr : IsOfFinOrder r) (h4 : r ^ 4 ≠ 1) (hS : SizeCondR p q (orderOf (r ^ 2))) :
    HasGoodPrimeR p q r := by
  obtain ⟨hm3, hnm, k, hk, htot, hV⟩ := cycloScaled_value p hq hr h4
  obtain ⟨C, C', hCdvd, hprod, hbound⟩ := exists_cofactorR hq hqp hr
  have hq0 : (q : ℤ) ≠ 0 := Int.natCast_ne_zero.2 hq.ne'
  -- `C C' = Φ_m(p, q)^(2k)`
  have hCC' : C * C' = cycValR p q (orderOf (r ^ 2)) ^ (2 * k) := by
    have h1 : (q : ℤ) ^ (2 * (orderOf r).totient) * (C * C') =
        (q : ℤ) ^ (2 * (orderOf r).totient) * cycValR p q (orderOf (r ^ 2)) ^ (2 * k) := by
      have h2 : ((q : ℂ) ^ (orderOf r).totient *
          ((cycValR p q (orderOf (r ^ 2)) : ℤ) : ℂ) ^ k) ^ 2 =
          (((q : ℤ) ^ (2 * (orderOf r).totient) *
            cycValR p q (orderOf (r ^ 2)) ^ (2 * k) : ℤ) : ℂ) := by
        push_cast
        ring
      rw [hV, h2] at hprod
      exact_mod_cast hprod
    exact mul_left_cancel₀ (pow_ne_zero _ hq0) h1
  have hbound' : |(C' : ℝ)| ≤ (Real.sqrt (p : ℝ) + Real.sqrt (q : ℝ)) ^
      (2 * k * (orderOf (r ^ 2)).totient) := by
    rw [htot, ← pow_mul] at hbound
    rwa [mul_assoc]
  have hx := isIntegral_tB_sub_natCast_mul p q hr
  by_cases hex : ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : ℤ) ∣ C ∧ ¬ ℓ ∣ orderOf (r ^ 2)
  · -- a prime of `C` that does not divide `m`
    obtain ⟨ℓ, hℓ, hℓC, hℓm⟩ := hex
    have hℓi := Nat.prime_iff_prime_int.1 hℓ
    have hℓΦ : (ℓ : ℤ) ∣ cycValR p q (orderOf (r ^ 2)) :=
      hℓi.dvd_of_dvd_pow (hCC' ▸ Dvd.dvd.mul_right hℓC C')
    have hℓc : (ℓ : ℤ) ∣ (minpoly ℤ (BaseB.tB (p * q) - (q : ℂ) * r)).eval 0 :=
      hℓi.dvd_of_dvd_pow (hℓC.trans hCdvd)
    obtain ⟨hℓ2, hℓpq, hlt⟩ := prime_facts_of_dvd_cycValR hcop hm3 hℓ hℓΦ hℓm
    obtain ⟨Q, hQ, hℓQ, hxQ⟩ := BaseB.hasPrime_of_dvd_minpoly_eval_zero hx hℓ hℓc
    refine ⟨Q, hQ, ℓ, hℓ, hℓ2, hℓpq, ?_, hℓQ, hxQ⟩
    intro hℓn
    rcases (Nat.Prime.dvd_mul hℓ).1 (hℓn.trans hnm) with h | h
    · exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 h)
    · exact absurd (Nat.le_of_dvd (by omega) h) (by omega)
  · -- every prime of `C` divides `m`: impossible by size
    exfalso
    push Not at hex
    exact size_contradictionR hqp hcop hm3 (by omega : 0 < 2 * k) hS hCC' hbound' hex

end RatBase

end PiFormula
