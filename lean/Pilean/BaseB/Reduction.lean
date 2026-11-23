import Pilean.BaseB.ReductionCyclo
import Pilean.BaseB.ReductionRoots

/-!
# A general base `b`: a good prime from the size condition

`hasGoodPrimeB_of_sizeCond`: let `b ≥ 2`, let `r` be a root of unity with `r⁴ ≠ 1`, and let
`m ≥ 3` be the order of `r²`. If `SizeCond b m` holds, then `r` has a good prime in base `b`:
a prime ideal of the algebraic integers that contains `√b - r` and an odd rational prime
dividing neither `b` nor the order of `r`.

The proof uses no field norm and no Galois theory. Let `t = √b`, `n = ord r`, `x = t - r`,
`μ` the minimal polynomial of `x` over `ℤ` and `c₀ = μ(0)`.

1. Every prime `p ∣ c₀` lies under a prime ideal containing `x`
   (`hasPrime_of_dvd_minpoly_eval_zero`, file `Symmetrize`).
2. `c₀ h = Φ_n(t) Φ_n(-t)` for an integer `h` with `|h| ≤ (√b + 1)^φ(n)` (`exists_cofactor`,
   file `ReductionRoots`).
3. `Φ_n(t) Φ_n(-t) = Φ_m(b)^k` and `φ(n) = k φ(m)` with `k ≥ 1` (`cyclo_data`, file
   `ReductionCyclo`).
4. A prime `p ∣ c₀` with `p ∤ m` divides `Φ_m(b)`, so `b` has order `m` modulo `p`: then
   `p ≡ 1 (mod m)`, `p` is odd, `p ∤ b` and `p ∤ n` (`prime_facts_of_dvd_cyclotomic`). This is
   a good prime.
5. Otherwise every prime factor of `c₀` divides `m` and `Φ_m(b)`. Such a prime is the largest
   prime factor of `m`, and it divides `Φ_m(b)` exactly once (`nonprimitive_facts`). So
   `|c₀| = 1` or `|c₀| = q^j` with `j ≤ k`, and
   `Φ_m(b)^k = |c₀| |h| ≤ (q (√b + 1)^φ(m))^k`, against the size condition
   (`size_contradiction`).
-/

open Complex Polynomial

namespace PiFormula

namespace BaseB

/-- `Φ_m(b)` as a homogeneous cyclotomic value. -/
theorem homogeneous_eq_eval (m b : ℕ) :
    TauCeti.homogeneousCyclotomic m ((b : ℕ) : ℤ) ((1 : ℕ) : ℤ) =
      (cyclotomic m ℤ).eval (b : ℤ) := by
  rw [Nat.cast_one, TauCeti.homogeneousCyclotomic_one_right]

/-- A prime factor `p` of `Φ_m(b)`, `m ≥ 3`, that does not divide `m` is odd, does not divide
`b`, and is larger than `m`. -/
theorem prime_facts_of_dvd_cyclotomic {b m p : ℕ} (hm : 3 ≤ m) (hp : p.Prime)
    (hdvd : (p : ℤ) ∣ (cyclotomic m ℤ).eval (b : ℤ)) (hpm : ¬ p ∣ m) :
    p ≠ 2 ∧ ¬ p ∣ b ∧ m < p := by
  have := Fact.mk hp
  have hb1 : ¬ (p : ℤ) ∣ ((1 : ℕ) : ℤ) := by
    norm_cast
    exact hp.not_dvd_one
  have hord := (hp.dvd_homogeneousCyclotomic_iff_orderOf_eq hb1 (by omega : m ≠ 0)).1
    ((homogeneous_eq_eval m b).symm ▸ hdvd)
  rw [(Nat.ordCompl_eq_self_iff_zero_or_not_dvd m hp).2 (Or.inr hpm)] at hord
  have hord' : orderOf ((b : ℕ) : ZMod p) = m := by simpa using hord
  have hb0 : ((b : ℕ) : ZMod p) ≠ 0 := by
    intro h0
    have h1 : ((b : ℕ) : ZMod p) ^ m = 1 := by rw [← hord']; exact pow_orderOf_eq_one _
    rw [h0, zero_pow (by omega)] at h1
    exact zero_ne_one h1
  have hd := ZMod.orderOf_dvd_card_sub_one hb0
  rw [hord'] at hd
  have h2 := hp.two_le
  have hle := Nat.le_of_dvd (by omega) hd
  exact ⟨by omega, fun hpb => hb0 ((ZMod.natCast_eq_zero_iff b p).2 hpb), by omega⟩

/-- A prime factor `p` of `Φ_m(b)`, `b ≥ 2`, `m ≥ 3`, that divides `m` is at least every prime
factor of `m`, and `p²` does not divide `Φ_m(b)`. -/
theorem nonprimitive_facts {b m p : ℕ} (hb : 2 ≤ b) (hm : 3 ≤ m) (hp : p.Prime)
    (hdvd : (p : ℤ) ∣ (cyclotomic m ℤ).eval (b : ℤ)) (hpm : p ∣ m) :
    (∀ q : ℕ, q.Prime → q ∣ m → q ≤ p) ∧ ¬ (p : ℤ) ^ 2 ∣ (cyclotomic m ℤ).eval (b : ℤ) := by
  have hdvd' : (p : ℤ) ∣ TauCeti.homogeneousCyclotomic m ((b : ℕ) : ℤ) ((1 : ℕ) : ℤ) :=
    (homogeneous_eq_eval m b).symm ▸ hdvd
  have hb1 : ¬ (p : ℤ) ∣ ((1 : ℕ) : ℤ) := by
    norm_cast
    exact hp.not_dvd_one
  refine ⟨fun q hq hqm =>
    hp.le_of_dvd_homogeneousCyclotomic_of_prime_of_dvd hb1 hdvd' hq hqm, ?_⟩
  have hmul := hp.multiplicity_homogeneousCyclotomic_eq_one (a := b) (b := 1) (by omega)
    hp.not_dvd_one hpm (by omega) hdvd'
  rw [homogeneous_eq_eval] at hmul
  have hfin : FiniteMultiplicity (p : ℤ) ((cyclotomic m ℤ).eval (b : ℤ)) :=
    FiniteMultiplicity.of_prime_left (Nat.prime_iff_prime_int.1 hp)
      (cyclotomic_pos (by omega) (b : ℤ)).ne'
  exact hfin.not_pow_dvd_of_multiplicity_lt (by rw [hmul]; norm_num)

/-- If `q²` does not divide `Φ`, then `q^(k+1)` does not divide `Φ^k`. -/
theorem not_pow_succ_dvd_pow {q : ℕ} (hq : q.Prime) {Φ : ℤ} (h2 : ¬ (q : ℤ) ^ 2 ∣ Φ) (k : ℕ) :
    ¬ (q : ℤ) ^ (k + 1) ∣ Φ ^ k := by
  have hqi := Nat.prime_iff_prime_int.1 hq
  intro h
  have hqΦ : (q : ℤ) ∣ Φ := hqi.dvd_of_dvd_pow ((dvd_pow_self _ (Nat.succ_ne_zero k)).trans h)
  obtain ⟨u, rfl⟩ := hqΦ
  rw [mul_pow, pow_succ, mul_dvd_mul_iff_left (pow_ne_zero k hqi.ne_zero)] at h
  have hu : (q : ℤ) ∣ u := hqi.dvd_of_dvd_pow h
  exact h2 (by rw [sq]; exact mul_dvd_mul_left _ hu)

/-- **The size argument.** If `c h = Φ_m(b)^k` with `|h| ≤ (√b + 1)^(k φ(m))`, and every prime
factor of `c` divides `m`, the size condition fails. -/
theorem size_contradiction {b m k : ℕ} (hb : 2 ≤ b) (hm : 3 ≤ m) (hk : 0 < k)
    (hS : SizeCond b m) {c h : ℤ} (hch : c * h = (cyclotomic m ℤ).eval (b : ℤ) ^ k)
    (hbound : |(h : ℝ)| ≤ (Real.sqrt (b : ℝ) + 1) ^ (k * m.totient))
    (hall : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ c → p ∣ m) : False := by
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℤ, (cyclotomic m ℤ).eval (b : ℤ) = Φ := ⟨_, rfl⟩
  have hΦpos : 0 < Φ := hΦ ▸ cyclotomic_pos (by omega) (b : ℤ)
  obtain ⟨hS1, hS2⟩ := hS
  rw [hΦ] at hch hS1 hS2
  obtain ⟨s, hs⟩ : ∃ s : ℝ, (Real.sqrt (b : ℝ) + 1) ^ m.totient = s := ⟨_, rfl⟩
  have hs0 : 0 < s := by
    rw [← hs]
    have := Real.sqrt_nonneg (b : ℝ)
    positivity
  rw [pow_mul', hs] at hbound
  rw [hs] at hS1 hS2
  have hΦR : (0 : ℝ) < (Φ : ℝ) := by exact_mod_cast hΦpos
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hch
    exact (pow_pos hΦpos k).ne hch
  obtain ⟨N, hN⟩ : ∃ N : ℕ, c.natAbs = N := ⟨_, rfl⟩
  have hN0 : N ≠ 0 := hN ▸ Int.natAbs_ne_zero.2 hc0
  have hreal : (N : ℝ) * |(h : ℝ)| = (Φ : ℝ) ^ k := by
    have h1 : ((|c| * |h| : ℤ) : ℝ) = ((Φ ^ k : ℤ) : ℝ) := by
      rw [← abs_mul, hch, abs_of_pos (pow_pos hΦpos k)]
    rw [← hN]
    push_cast at h1 ⊢
    rw [← h1, Nat.cast_natAbs, Int.cast_abs]
  have hprime : ∀ p : ℕ, p.Prime → p ∣ N → p ∣ m ∧ (p : ℤ) ∣ Φ := by
    intro p hp hpN
    have hpc : (p : ℤ) ∣ c := Int.natCast_dvd.2 (hN ▸ hpN)
    exact ⟨hall p hp hpc,
      (Nat.prime_iff_prime_int.1 hp).dvd_of_dvd_pow (hch ▸ Dvd.dvd.mul_right hpc h)⟩
  by_cases hN1 : N = 1
  · -- `|c| = 1`
    rw [hN1, Nat.cast_one, one_mul] at hreal
    have h1 : s ^ k < (Φ : ℝ) ^ k := pow_lt_pow_left₀ hS1 hs0.le hk.ne'
    linarith
  · obtain ⟨q, hq, hqN⟩ := Nat.exists_prime_and_dvd hN1
    obtain ⟨hqm, hqΦ⟩ := hprime q hq hqN
    obtain ⟨hmax, hsq⟩ := nonprimitive_facts hb hm hq (hΦ ▸ hqΦ) hqm
    rw [hΦ] at hsq
    have huniq : ∀ {d : ℕ}, d.Prime → d ∣ N → d = q := by
      intro d hd hdN
      obtain ⟨hdm, hdΦ⟩ := hprime d hd hdN
      obtain ⟨hmax', -⟩ := nonprimitive_facts hb hm hd (hΦ ▸ hdΦ) hdm
      exact le_antisymm (hmax d hd hdm) (hmax' q hq hqm)
    obtain ⟨j, hj⟩ : ∃ j, N = q ^ j := ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hN0 huniq⟩
    have hjk : j ≤ k := by
      by_contra hlt
      push Not at hlt
      apply not_pow_succ_dvd_pow hq hsq k
      have h1 : (q : ℤ) ^ (k + 1) ∣ (q : ℤ) ^ j := pow_dvd_pow _ hlt
      have h2 : ((N : ℕ) : ℤ) ∣ Φ ^ k := by
        rw [← hch, ← hN]
        exact (Int.natAbs_dvd.2 dvd_rfl).mul_right h
      rw [hj] at h2
      push_cast at h2
      exact h1.trans h2
    have hsz := hS2 q hq hqm hqΦ
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.one_le
    have hNle : (N : ℝ) ≤ (q : ℝ) ^ k := by
      rw [hj]
      push_cast
      exact pow_le_pow_right₀ hq1 hjk
    have h1 : (Φ : ℝ) ^ k ≤ (q : ℝ) ^ k * s ^ k := by
      rw [← hreal]
      exact mul_le_mul hNle hbound (abs_nonneg _) (by positivity)
    have h2 : ((q : ℝ) * s) ^ k < (Φ : ℝ) ^ k :=
      pow_lt_pow_left₀ hsz (by positivity) hk.ne'
    rw [mul_pow] at h2
    linarith

/-- **A good prime from the size condition.** Let `b ≥ 2` and let `r` be a root of unity with
`r⁴ ≠ 1`. If the size condition holds at `(b, m)`, `m` the order of `r²`, then `r` has a good
prime in base `b`. -/
theorem hasGoodPrimeB_of_sizeCond {b : ℕ} (hb : 2 ≤ b) {r : ℂ} (hr : IsOfFinOrder r)
    (h4 : r ^ 4 ≠ 1) (hS : SizeCond b (orderOf (r ^ 2))) : HasGoodPrimeB b r := by
  obtain ⟨hm3, hnm, k, hk, htot, hD⟩ := cyclo_data b hr h4
  obtain ⟨h, hch, hbound⟩ := exists_cofactor hb hr
  rw [hD] at hch
  rw [htot] at hbound
  have hch' : (minpoly ℤ (tB b - r)).eval 0 * h =
      (cyclotomic (orderOf (r ^ 2)) ℤ).eval (b : ℤ) ^ k := by exact_mod_cast hch
  have hx := isIntegral_tB_sub b hr
  by_cases hex : ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ (minpoly ℤ (tB b - r)).eval 0 ∧
      ¬ p ∣ orderOf (r ^ 2)
  · -- a prime of the constant term that does not divide `m`
    obtain ⟨p, hp, hpc, hpm⟩ := hex
    have hpΦ : (p : ℤ) ∣ (cyclotomic (orderOf (r ^ 2)) ℤ).eval (b : ℤ) :=
      (Nat.prime_iff_prime_int.1 hp).dvd_of_dvd_pow (hch' ▸ Dvd.dvd.mul_right hpc h)
    obtain ⟨hp2, hpb, hlt⟩ := prime_facts_of_dvd_cyclotomic hm3 hp hpΦ hpm
    obtain ⟨Q, hQ, hpQ, hxQ⟩ := hasPrime_of_dvd_minpoly_eval_zero hx hp hpc
    refine ⟨Q, hQ, p, hp, hp2, hpb, ?_, hpQ, hxQ⟩
    intro hpn
    rcases (Nat.Prime.dvd_mul hp).1 (hpn.trans hnm) with h | h
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
    · exact absurd (Nat.le_of_dvd (by omega) h) (by omega)
  · -- every prime of the constant term divides `m`: impossible by size
    exfalso
    push Not at hex
    exact size_contradiction hb hm3 hk hS hch' hbound hex

end BaseB

end PiFormula
