import Pilean.PiFormula.Log23

/-!
# Primes whose logarithm has no binary BBP-type formula

`Log23.lean` shows that `log 23` is not a value of the class F. The argument works for any
prime `ℓ` with a "partner": every atom that contains `ℓ` as a primitive prime also contains
another good prime. This file makes that general (`goodPrimes_ne`, `no_rel_of_goodPrimes`,
`not_isFValue_log`) and applies it to the ten primes below 100 that are not on Bailey's list:

| `ℓ` | `ord_ℓ(2)` | the atom that contains `ℓ` | partner |
|---|---|---|---|
| 23, 89 | 11 | `Φ_11(2) = 2047 = 23 · 89` | each other |
| 47 | 23 | `Φ_23(2) = 47 · 178481` | 178481 |
| 53 | 52 | `Φ_13(1+i)`, of norm `53 · 157` | 157 |
| 59 | 58 | `Φ_29(-2) = 59 · 3033169` | 3033169 |
| 67 | 66 | `Φ_33(-2) = 67 · 20857` | 20857 |
| 71 | 35 | `Φ_35(2) = 71 · 122921` | 122921 |
| 79 | 39 | `Φ_39(2) = 79 · 121369` | 121369 |
| 83 | 82 | `Φ_41(-2) = 83 · 8831418697` | a prime factor of the cofactor |
| 97 | 48 | `Φ_3(16i)`, of norm `97 · 673` | 673 |

`IsFValue x` says that `x` is the value of a series `∑ ρ(k) 2^(-⌊k/2⌋)/k` with `ρ` rational
and periodic. `not_isFValue_log_of_mem` (from Baker's theorem): for these ten primes `ℓ`,
`log ℓ` is not such a value. The classification below 100 is in `LogYes.lean`.
-/

open Complex Polynomial

namespace PiFormula

/-! ## 1. The general statements -/

/-- `x` is the value of a series of the class F: `x = ∑ ρ(k) 2^(-⌊k/2⌋)/k` for some rational
periodic pattern `ρ`. -/
def IsFValue (x : ℝ) : Prop :=
  ∃ (N : ℕ) (ρ : ℕ → ℚ), 0 < N ∧ (∀ k, ρ (k + N) = ρ k) ∧ HasSum (seriesTerm ρ) x

/-- A prime of Lemma 3 for a non-exceptional atom, other than `ℓ`. -/
theorem atom_prime_ne {ℓ : ℕ} {n0 : ℕ} (hord : orderOf (2 : ZMod ℓ) = n0)
    (hA : ∀ a : Atom, a ∉ exceptional → 4 * nOf a = n0 → ∃ p, p ≠ ℓ ∧ p.Prime ∧ p % 4 = 1 ∧
      p ≠ 2 ∧ ¬ p ∣ mOf a ∧ (p : ℤ) ∣ (atom a).norm)
    (a : Atom) (hex : a ∉ exceptional) :
    ∃ p, p ≠ ℓ ∧ p.Prime ∧ p % 4 = 1 ∧ p ≠ 2 ∧ ¬ p ∣ mOf a ∧ (p : ℤ) ∣ (atom a).norm := by
  by_cases h : 4 * nOf a = n0
  · exact hA a hex h
  · obtain ⟨p, hp, hord', hdvd⟩ := exists_primitive_atom a hex
    have : Fact p.Prime := ⟨hp⟩
    have hge := prime_ge_of_orderOf (nOf_pos a) hord'
    have hle := mOf_le_nOf a
    refine ⟨p, ?_, hp, mod_four_eq_one_of_orderOf (nOf_pos a) hord',
      ne_two_of_orderOf (nOf_pos a) hord',
      Nat.not_dvd_of_pos_of_lt (mOf_odd a).pos (by omega), hdvd⟩
    rintro rfl
    exact h (hord'.symm.trans hord)

/-- **Good primes of characteristic other than `ℓ`.** Let `ℓ` be a prime with `ord_ℓ(2) = n0`.
If every atom of index `n0` has a prime other than `ℓ`, then every root of unity outside `R0`
has a good prime of residue characteristic other than `ℓ`. -/
theorem goodPrimes_ne {ℓ : ℕ} {n0 : ℕ} (hord : orderOf (2 : ZMod ℓ) = n0)
    (hA : ∀ a : Atom, a ∉ exceptional → 4 * nOf a = n0 → ∃ p, p ≠ ℓ ∧ p.Prime ∧ p % 4 = 1 ∧
      p ≠ 2 ∧ ¬ p ∣ mOf a ∧ (p : ℤ) ∣ (atom a).norm)
    (hF : ∀ k, 1 ≤ k → 2 * k + 1 = n0 → ∃ q, q ≠ ℓ ∧ q.Prime ∧ q ≠ 2 ∧ ¬ q ∣ 2 * k + 1 ∧
      (q : ℤ) ∣ (cyclotomic (2 * k + 1) ℤ).eval 2)
    (hT : ∀ k, 2 ≤ k → 2 * (2 * k + 1) = n0 → ∃ q, q ≠ ℓ ∧ q.Prime ∧ q ≠ 2 ∧
      ¬ q ∣ 2 * k + 1 ∧ (q : ℤ) ∣ (cyclotomic (2 * k + 1) ℤ).eval (-2))
    (r : ℂ) (hr : IsOfFinOrder r) (hR0 : r ∉ R0) : ∃ p, p ≠ ℓ ∧ HasGoodPrimeAt r p := by
  obtain ⟨n, hn, hrn⟩ := isOfFinOrder_iff_pow_eq_one.1 hr
  rcases exists_explicit_orbit hn hrn with ⟨a, ha⟩ | ⟨a, ha⟩ | ⟨k, b, hkb⟩
  · by_cases hex : a ∈ exceptional
    · exact absurd (orbit_exceptional_R0 hex ha) hR0
    · obtain ⟨p, hpℓ, hp, h4, hp2, hpm, hdvd⟩ := atom_prime_ne hord hA a hex
      exact ⟨p, hpℓ, goodAt_orbit_of_prime a hp h4 hp2 hpm hdvd ha⟩
  · by_cases hex : a ∈ exceptional
    · exact absurd (partner_exceptional_R0 hex ha) hR0
    · obtain ⟨p, hpℓ, hp, h4, hp2, hpm, hdvd⟩ := atom_prime_ne hord hA a hex
      exact ⟨p, hpℓ, goodAt_partner_of_prime a hp h4 hp2 hpm hdvd ha⟩
  · cases b
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · exact absurd (selfOrb_zero_false_R0 hkb) hR0
      · by_cases hk0 : 2 * k + 1 = n0
        · obtain ⟨q, hqℓ, hq, hq2, hqm, hdvd⟩ := hF k hk hk0
          exact ⟨q, hqℓ, goodAt_selfOrb_of_dvd k false hq hq2 hqm (by simpa using hdvd) hkb⟩
        · obtain ⟨q, hq, hord'⟩ := bang (2 * k + 1) (by omega) (by omega)
          have : Fact q.Prime := ⟨hq⟩
          have hlt := lt_of_orderOf_two (by omega) hord'
          have hdvd := dvd_cyclotomic_of_orderOf (by omega) hord'
          refine ⟨q, ?_, goodAt_selfOrb_of_dvd k false hq (by omega)
            (Nat.not_dvd_of_pos_of_lt (by omega) hlt) (by simpa using hdvd) hkb⟩
          rintro rfl
          exact hk0 (hord'.symm.trans hord)
    · rcases (show k = 0 ∨ k = 1 ∨ 2 ≤ k by omega) with rfl | rfl | hk
      · exact absurd (selfOrb_zero_true_R0 hkb) hR0
      · exact absurd (selfOrb_one_true_R0 hkb) hR0
      · by_cases hk0 : 2 * (2 * k + 1) = n0
        · obtain ⟨q, hqℓ, hq, hq2, hqm, hdvd⟩ := hT k hk hk0
          exact ⟨q, hqℓ, goodAt_selfOrb_of_dvd k true hq hq2 hqm (by simpa using hdvd) hkb⟩
        · obtain ⟨q, hq, hord'⟩ := bang (2 * (2 * k + 1)) (by omega) (by omega)
          have : Fact q.Prime := ⟨hq⟩
          have hlt := lt_of_orderOf_two (by omega) hord'
          have hdvd := dvd_cyclotomic_of_orderOf (by omega) hord'
          rw [cyclotomic_two_mul_of_odd ⟨k, rfl⟩ (by omega) ℤ, eval_comp, eval_neg, eval_X]
            at hdvd
          refine ⟨q, ?_, goodAt_selfOrb_of_dvd k true hq (by omega)
            (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) (by simpa using hdvd) hkb⟩
          rintro rfl
          exact hk0 (hord'.symm.trans hord)

/-- **No multiplicative relation with `ℓ`**, for an odd prime `ℓ` prime to `2^60 - 1` such that
every root outside `R0` has a good prime of characteristic other than `ℓ`. -/
theorem no_rel_of_goodPrimes {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hcop : Nat.Coprime (2 ^ 60 - 1) ℓ)
    (hG : ∀ r : ℂ, IsOfFinOrder r → r ∉ R0 → ∃ p, p ≠ ℓ ∧ HasGoodPrimeAt r p)
    {S : Finset ℂ} (hS : ∀ r ∈ S, IsOfFinOrder r) {e : ℂ → ℤ} {m : ℤ}
    (h : IsRelUpTo ℓ S e m) : m = 0 := by
  classical
  have hsupp := support_upTo hℓ hG hS h
  set S' := S.filter (fun r => e r ≠ 0) with hS'def
  have hS' : ∀ r ∈ S', IsOfFinOrder r := fun r hr => hS r (Finset.mem_filter.1 hr).1
  have h' : IsRelUpTo ℓ S' e m := by
    obtain ⟨ξ, hξ, hrel⟩ := h
    refine ⟨ξ, hξ, ?_⟩
    rw [hS'def, Finset.prod_filter_of_ne (p := fun r => e r ≠ 0)
      (fun r _ hr hc => hr (by simp [hc]))]
    exact hrel
  have hR0 : ∀ r ∈ S', r ∈ R0 := by
    intro r hr
    by_contra hnot
    exact (Finset.mem_filter.1 hr).2 (hsupp r (Finset.mem_filter.1 hr).1 hnot)
  obtain ⟨P, hP, hin⟩ := exists_prime_above hℓ
  have ht : ¬ InP P tC := by
    intro ht
    have h2 := ht.mul_right (isIntegral_one.sub (isIntegral_of_finOrder isOfFinOrder_I))
    rw [tC_mul_conj] at h2
    exact not_inP_coprime (a := 2) (b := ℓ)
      ((Nat.coprime_primes Nat.prime_two hℓ).2 (Ne.symm hℓ2)) (by exact_mod_cast h2) hin
  exact exponent_eq_zero_upTo hℓ.ne_zero hS' h' hin ht
    fun r hr => not_inP_R0 hcop hin (hR0 r hr)

/-- **No series of the class F for `log ℓ`** (from Baker's theorem), given that no
multiplicative relation among the `1 - r/t` involves `ℓ`. -/
theorem no_log_of_rel (hB : BakerTheorem) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (hmul : ∀ S : Finset ℂ, (∀ r ∈ S, IsOfFinOrder r) → ∀ (e : ℂ → ℤ) (m : ℤ),
      IsRelUpTo ℓ S e m → m = 0)
    {N : ℕ} (hN : 0 < N) {ρ : ℕ → ℚ} (hρ : ∀ k, ρ (k + N) = ρ k) {q : ℝ}
    (hq : IsAlgebraic ℚ q) (h : HasSum (seriesTerm ρ) (q * Real.log ℓ)) : q = 0 := by
  have hρ8 : ∀ k, ρ (k + 8 * N) = ρ k := fun k => by
    have h8 := periodic_mul hρ 8 k
    rwa [mul_comm] at h8
  have hN8 : 0 < 8 * N := by positivity
  have h1 := series_eq_logs hN8 (Dvd.intro N rfl) hρ8
  have e : (fun k : ℕ => (ρ k : ℂ) / 2 ^ (k / 2) / k) =
      fun k : ℕ => ((seriesTerm ρ k : ℝ) : ℂ) := by
    funext k
    simp [seriesTerm]
  rw [e] at h1
  have h2 := h1.unique (Complex.hasSum_ofReal.2 h)
  have hqC : IsAlgebraic ℚ (q : ℂ) :=
    (isAlgebraic_algebraMap_iff (algebraMap ℝ ℂ).injective).2 hq
  have h3 : ∑ r ∈ rootsN (8 * N), fourierD (8 * N) ρ r * Complex.log (1 - r / tC) =
      (q : ℂ) * (Real.log (ℓ : ℝ) : ℂ) := by
    rw [h2]
    push_cast
    ring
  have h4 := baker_no_log hB hℓ hmul (fun r hr => isOfFinOrder_of_mem_rootsN hN8 hr)
    (fun r hr => isAlgebraic_fourierD (8 * N) ρ (isOfFinOrder_of_mem_rootsN hN8 hr)) hqC h3
  exact_mod_cast h4

/-- **`log ℓ` is not a value of the class F** (from Baker's theorem), for a prime `ℓ` prime to
`2^60 - 1` such that every root outside `R0` has a good prime of characteristic other than
`ℓ`. -/
theorem not_isFValue_log (hB : BakerTheorem) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hcop : Nat.Coprime (2 ^ 60 - 1) ℓ)
    (hG : ∀ r : ℂ, IsOfFinOrder r → r ∉ R0 → ∃ p, p ≠ ℓ ∧ HasGoodPrimeAt r p) :
    ¬ IsFValue (Real.log ℓ) := by
  rintro ⟨N, ρ, hN, hρ, h⟩
  have h1 : HasSum (seriesTerm ρ) ((1 : ℝ) * Real.log ℓ) := by rwa [one_mul]
  have h0 := no_log_of_rel hB hℓ.pos
    (fun S hS e m hrel => no_rel_of_goodPrimes hℓ hℓ2 hcop hG hS hrel) hN hρ isAlgebraic_one h1
  exact one_ne_zero h0

/-! ## 2. Tools for the partners -/

/-- A prime factor of a cofactor `N0` of `v`: other than `ℓ`, odd, and not dividing the prime
`m`. -/
theorem exists_prime_factor_of_cofactor {ℓ N0 m : ℕ} {v : ℤ} (hN0 : N0 ≠ 1)
    (hv : (N0 : ℤ) ∣ v) (hℓ : ¬ ℓ ∣ N0) (h2 : ¬ 2 ∣ N0) (hm : m.Prime) (hmN : ¬ m ∣ N0) :
    ∃ q, q ≠ ℓ ∧ q.Prime ∧ q ≠ 2 ∧ ¬ q ∣ m ∧ (q : ℤ) ∣ v := by
  have hq := Nat.minFac_prime hN0
  have hd := Nat.minFac_dvd N0
  refine ⟨N0.minFac, ?_, hq, ?_, ?_, (Int.natCast_dvd_natCast.2 hd).trans hv⟩
  · intro h
    exact hℓ (h ▸ hd)
  · intro h
    exact h2 (h ▸ hd)
  · intro h
    have e := (Nat.prime_dvd_prime_iff_eq hq hm).1 h
    exact hmN (e ▸ hd)

theorem eval_cyclotomic_prime (m : ℕ) [Fact m.Prime] (x : ℤ) :
    (cyclotomic m ℤ).eval x = ∑ i ∈ Finset.range m, x ^ i := by
  rw [cyclotomic_prime, eval_finsetSum]
  simp only [eval_pow, eval_X]

/-- A prime `q` with `ord_q(2) = n` as a partner in `Φ_n(2)`. -/
theorem partner_of_order {q n : ℕ} [Fact q.Prime] (hn : 3 ≤ n)
    (hord : orderOf (2 : ZMod q) = n) :
    q ≠ 2 ∧ ¬ q ∣ n ∧ (q : ℤ) ∣ (cyclotomic n ℤ).eval 2 := by
  have hlt := lt_of_orderOf_two (by omega) hord
  exact ⟨by omega, Nat.not_dvd_of_pos_of_lt (by omega) hlt,
    dvd_cyclotomic_of_orderOf (by omega) hord⟩

/-! ## 3. Orders of 2 -/

theorem ord_two_47 : orderOf (2 : ZMod 47) = 23 := by
  have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)

theorem ord_two_53 : orderOf (2 : ZMod 53) = 52 :=
  (orderOf_eq_iff (by norm_num)).2 ⟨by decide +kernel, by decide +kernel⟩

theorem ord_two_59 : orderOf (2 : ZMod 59) = 58 :=
  (orderOf_eq_iff (by norm_num)).2 ⟨by decide +kernel, by decide +kernel⟩

theorem ord_two_67 : orderOf (2 : ZMod 67) = 66 :=
  (orderOf_eq_iff (by norm_num)).2 ⟨by decide +kernel, by decide +kernel⟩

theorem ord_two_71 : orderOf (2 : ZMod 71) = 35 :=
  (orderOf_eq_iff (by norm_num)).2 ⟨by decide +kernel, by decide +kernel⟩

theorem ord_two_79 : orderOf (2 : ZMod 79) = 39 :=
  (orderOf_eq_iff (by norm_num)).2 ⟨by decide +kernel, by decide +kernel⟩

theorem ord_two_83 : orderOf (2 : ZMod 83) = 82 :=
  (orderOf_eq_iff (by norm_num)).2 ⟨by decide +kernel, by decide +kernel⟩

theorem ord_two_97 : orderOf (2 : ZMod 97) = 48 :=
  (orderOf_eq_iff (by norm_num)).2 ⟨by decide +kernel, by decide +kernel⟩

theorem ord_two_122921 : orderOf (2 : ZMod 122921) = 35 :=
  (orderOf_eq_iff (by norm_num)).2 ⟨by decide +kernel, by decide +kernel⟩

theorem ord_two_121369 : orderOf (2 : ZMod 121369) = 39 :=
  (orderOf_eq_iff (by norm_num)).2 ⟨by decide +kernel, by decide +kernel⟩

theorem ord_two_20857 : orderOf (2 : ZMod 20857) = 66 :=
  (orderOf_eq_iff (by norm_num)).2 ⟨by decide +kernel, by decide +kernel⟩

/-! ## 4. The atoms of index 13 and 12 -/

theorem atom_P6 : atom (.P 6) = ⟨-64, 65⟩ := by
  have := Fact.mk (show Nat.Prime 13 by norm_num)
  simp only [atom, mOf, base]
  rw [show 2 * 6 + 1 = 13 by rfl, cyclotomic_prime, eval_finsetSum]
  simp only [eval_pow, eval_X]
  decide +kernel

theorem atom_Q6 : atom (.Q 6) = ⟨-38, -13⟩ := by
  have := Fact.mk (show Nat.Prime 13 by norm_num)
  simp only [atom, mOf, base]
  rw [show 2 * 6 + 1 = 13 by rfl, cyclotomic_prime, eval_finsetSum]
  simp only [eval_pow, eval_X]
  decide +kernel

theorem atom_R11 : atom (.R 1 1) = ⟨-255, 16⟩ := by
  simp only [atom, mOf, base]
  rw [show 2 * 1 + 1 = 3 by rfl, cyclotomic_three]
  simp only [eval_add, eval_pow, eval_X, eval_one]
  decide +kernel

/-! ## 5. The ten primes -/

theorem good_23 (r : ℂ) (hr : IsOfFinOrder r) (hR0 : r ∉ R0) :
    ∃ p, p ≠ 23 ∧ HasGoodPrimeAt r p := goodPrimes_ne_23 r hr hR0

theorem good_89 (r : ℂ) (hr : IsOfFinOrder r) (hR0 : r ∉ R0) :
    ∃ p, p ≠ 89 ∧ HasGoodPrimeAt r p := by
  refine goodPrimes_ne orderOf_two_89 (fun a _ h => by omega) (fun k _ h => ?_)
    (fun k _ h => by omega) r hr hR0
  obtain rfl : k = 5 := by omega
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  refine exists_prime_factor_of_cofactor (N0 := 23) (by norm_num) ?_ (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  change ((23 : ℕ) : ℤ) ∣ (cyclotomic 11 ℤ).eval 2
  rw [eval_cyclotomic_prime]
  decide +kernel

theorem good_47 (r : ℂ) (hr : IsOfFinOrder r) (hR0 : r ∉ R0) :
    ∃ p, p ≠ 47 ∧ HasGoodPrimeAt r p := by
  refine goodPrimes_ne ord_two_47 (fun a _ h => by omega) (fun k _ h => ?_)
    (fun k _ h => by omega) r hr hR0
  obtain rfl : k = 11 := by omega
  have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  refine exists_prime_factor_of_cofactor (N0 := 178481) (by norm_num) ?_ (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  change ((178481 : ℕ) : ℤ) ∣ (cyclotomic 23 ℤ).eval 2
  rw [eval_cyclotomic_prime]
  decide +kernel

theorem good_59 (r : ℂ) (hr : IsOfFinOrder r) (hR0 : r ∉ R0) :
    ∃ p, p ≠ 59 ∧ HasGoodPrimeAt r p := by
  refine goodPrimes_ne ord_two_59 (fun a _ h => by omega) (fun k _ h => by omega)
    (fun k _ h => ?_) r hr hR0
  obtain rfl : k = 14 := by omega
  have : Fact (Nat.Prime 29) := ⟨by norm_num⟩
  refine exists_prime_factor_of_cofactor (N0 := 3033169) (by norm_num) ?_ (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  change ((3033169 : ℕ) : ℤ) ∣ (cyclotomic 29 ℤ).eval (-2)
  rw [eval_cyclotomic_prime]
  decide +kernel

theorem good_83 (r : ℂ) (hr : IsOfFinOrder r) (hR0 : r ∉ R0) :
    ∃ p, p ≠ 83 ∧ HasGoodPrimeAt r p := by
  refine goodPrimes_ne ord_two_83 (fun a _ h => by omega) (fun k _ h => by omega)
    (fun k _ h => ?_) r hr hR0
  obtain rfl : k = 20 := by omega
  have : Fact (Nat.Prime 41) := ⟨by norm_num⟩
  refine exists_prime_factor_of_cofactor (N0 := 8831418697) (by norm_num) ?_ (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  change ((8831418697 : ℕ) : ℤ) ∣ (cyclotomic 41 ℤ).eval (-2)
  rw [eval_cyclotomic_prime]
  decide +kernel

theorem good_71 (r : ℂ) (hr : IsOfFinOrder r) (hR0 : r ∉ R0) :
    ∃ p, p ≠ 71 ∧ HasGoodPrimeAt r p := by
  refine goodPrimes_ne ord_two_71 (fun a _ h => by omega) (fun k _ h => ?_)
    (fun k _ h => by omega) r hr hR0
  obtain rfl : k = 17 := by omega
  have : Fact (Nat.Prime 122921) := ⟨by norm_num⟩
  obtain ⟨h2, hm, hd⟩ := partner_of_order (q := 122921) (n := 35) (by norm_num) ord_two_122921
  exact ⟨122921, by norm_num, Fact.out, h2, hm, hd⟩

theorem good_79 (r : ℂ) (hr : IsOfFinOrder r) (hR0 : r ∉ R0) :
    ∃ p, p ≠ 79 ∧ HasGoodPrimeAt r p := by
  refine goodPrimes_ne ord_two_79 (fun a _ h => by omega) (fun k _ h => ?_)
    (fun k _ h => by omega) r hr hR0
  obtain rfl : k = 19 := by omega
  have : Fact (Nat.Prime 121369) := ⟨by norm_num⟩
  obtain ⟨h2, hm, hd⟩ := partner_of_order (q := 121369) (n := 39) (by norm_num) ord_two_121369
  exact ⟨121369, by norm_num, Fact.out, h2, hm, hd⟩

theorem good_67 (r : ℂ) (hr : IsOfFinOrder r) (hR0 : r ∉ R0) :
    ∃ p, p ≠ 67 ∧ HasGoodPrimeAt r p := by
  refine goodPrimes_ne ord_two_67 (fun a _ h => by omega) (fun k _ h => by omega)
    (fun k _ h => ?_) r hr hR0
  obtain rfl : k = 16 := by omega
  have : Fact (Nat.Prime 20857) := ⟨by norm_num⟩
  obtain ⟨h2, hm, hd⟩ := partner_of_order (q := 20857) (n := 66) (by norm_num) ord_two_20857
  rw [show 66 = 2 * (2 * 16 + 1) by norm_num,
    cyclotomic_two_mul_of_odd ⟨16, rfl⟩ (by norm_num) ℤ, eval_comp, eval_neg, eval_X] at hd
  refine ⟨20857, by norm_num, Fact.out, h2, ?_, hd⟩
  intro h
  exact hm (h.trans ⟨2, by norm_num⟩)

theorem good_53 (r : ℂ) (hr : IsOfFinOrder r) (hR0 : r ∉ R0) :
    ∃ p, p ≠ 53 ∧ HasGoodPrimeAt r p := by
  refine goodPrimes_ne ord_two_53 (fun a _ h => ?_) (fun k _ h => by omega)
    (fun k _ h => by omega) r hr hR0
  rcases a with k | k | ⟨k, e⟩
  · obtain rfl : k = 6 := by
      simp only [nOf] at h
      omega
    refine ⟨157, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num [mOf], ?_⟩
    rw [atom_P6]
    decide
  · obtain rfl : k = 6 := by
      simp only [nOf] at h
      omega
    refine ⟨1613, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num [mOf], ?_⟩
    rw [atom_Q6]
    decide
  · exfalso
    simp only [nOf] at h
    have h2 : 2 ∣ 2 ^ (e + 1) * (2 * k + 1) :=
      Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
    omega

theorem good_97 (r : ℂ) (hr : IsOfFinOrder r) (hR0 : r ∉ R0) :
    ∃ p, p ≠ 97 ∧ HasGoodPrimeAt r p := by
  refine goodPrimes_ne ord_two_97 (fun a _ h => ?_) (fun k _ h => by omega)
    (fun k _ h => by omega) r hr hR0
  rcases a with k | k | ⟨k, e⟩
  · exfalso
    simp only [nOf] at h
    omega
  · exfalso
    simp only [nOf] at h
    omega
  · simp only [nOf] at h
    rcases e with _ | _ | e
    · exfalso
      norm_num at h
      omega
    · obtain rfl : k = 1 := by
        norm_num at h
        omega
      refine ⟨673, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num [mOf], ?_⟩
      rw [atom_R11]
      decide
    · exfalso
      have h8 : 8 ∣ 2 ^ (e + 1 + 1 + 1) * (2 * k + 1) := by
        refine Dvd.dvd.mul_right ?_ _
        rw [show e + 1 + 1 + 1 = 3 + e by ring, pow_add]
        exact Dvd.intro _ rfl
      omega

/-- The ten primes below 100 whose logarithm has no formula in the class F. -/
def noLogPrimes : Finset ℕ := {23, 47, 53, 59, 67, 71, 79, 83, 89, 97}

/-- **Ten primes with no formula (from Baker's theorem).** For
`ℓ = 23, 47, 53, 59, 67, 71, 79, 83, 89, 97`, `log ℓ` is not the value of any series
`∑ ρ(k) 2^(-⌊k/2⌋)/k` with `ρ` rational and periodic. -/
theorem not_isFValue_log_of_mem (hB : BakerTheorem) {ℓ : ℕ} (hℓ : ℓ ∈ noLogPrimes) :
    ¬ IsFValue (Real.log ℓ) := by
  simp only [noLogPrimes, Finset.mem_insert, Finset.mem_singleton] at hℓ
  rcases hℓ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_isFValue_log hB (by norm_num) (by norm_num) (by norm_num) good_23
  · exact not_isFValue_log hB (by norm_num) (by norm_num) (by norm_num) good_47
  · exact not_isFValue_log hB (by norm_num) (by norm_num) (by norm_num) good_53
  · exact not_isFValue_log hB (by norm_num) (by norm_num) (by norm_num) good_59
  · exact not_isFValue_log hB (by norm_num) (by norm_num) (by norm_num) good_67
  · exact not_isFValue_log hB (by norm_num) (by norm_num) (by norm_num) good_71
  · exact not_isFValue_log hB (by norm_num) (by norm_num) (by norm_num) good_79
  · exact not_isFValue_log hB (by norm_num) (by norm_num) (by norm_num) good_83
  · exact not_isFValue_log hB (by norm_num) (by norm_num) (by norm_num) good_89
  · exact not_isFValue_log hB (by norm_num) (by norm_num) (by norm_num) good_97

end PiFormula
