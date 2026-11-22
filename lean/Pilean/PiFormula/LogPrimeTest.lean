import Pilean.PiFormula.LogExplicit

/-!
# The finite test for a prime (Theorem K, the test)

For a prime `ℓ`, whether `log ℓ` is the value of a series of the class F is decided by one
integer, the *primitive part that contains `ℓ`* (`primPart ℓ`). Let `n` be the order of 2
modulo `ℓ`.

* If `n` is not 4 modulo 8, the primitive part is `Φ_n(2)`.
* If `n = 4d` with `d` odd, `Φ_n(2)` is the product of the two numbers `N(Φ_d(1+i))` and
  `N(Φ_d(-1-i))` (`Aplus d`, `Aminus d`; `Aplus_mul_Aminus`), and the primitive part is the
  one that `ℓ` divides.

**The test** (`isFValue_log_prime_iff`, from Baker's theorem), for an odd prime `ℓ` that does
not divide `2^60 - 1`: `log ℓ` is a value of the class F if and only if every prime `q ≠ ℓ`
that divides the primitive part divides `n` and has `log q` a value of F.

There is at most one such `q`: a prime factor of `Φ_n(2)` that divides `n` is the largest
prime factor of `n`. So the test is finite: `q < ℓ`, and `q` is tested in the same way.

The primes that divide `2^60 - 1` are `3, 5, 7, 11, 13, 31, 41, 61, 151, 331, 1321`; for
them and for 2 the logarithm is a value (`isFValue_log_of_dvd`). Together
(`isFValue_log_prime_classification`) this decides every prime.

The two halves of the proof.

* *The primitive part is a value* (`isFValue_log_primPart`, no Baker): `log Φ_n(2)`,
  `log N(Φ_n(1+i))` and `log N(Φ_d(-1-i))` (`d` odd) are values of F, by induction on `n`
  from `∏_{d ∣ n} Φ_d(x) = x^n - 1`. So if the other primes of the primitive part have
  logarithms that are values, so has `ℓ`.
* *A second primitive prime excludes `ℓ`* (`not_isFValue_log_of_partner`, from Baker's
  theorem): if a prime `q ≠ ℓ` that does not divide `n` divides the primitive part, then
  `log ℓ` is not a value. This is `goodPrimes_ne` and `not_isFValue_log` of `LogPrimes.lean`,
  with the three hypotheses on atoms supplied in general: `q` has order `n` too
  (`orderOf_two_of_not_dvd`), and for `n = 4d` the two halves have no common prime of order
  `n` (`not_dvd_norm_P_and_Q`).
-/

open Complex Polynomial

namespace PiFormula

/-! ## 1. The logarithms of the primitive parts are values -/

/-- `log Φ_n(2)` is a value of the class F, for every `n ≥ 1`. -/
theorem isFValue_log_cyclotomic_two : ∀ n : ℕ, 0 < n →
    IsFValue (Real.log (((cyclotomic n ℤ).eval 2 : ℤ) : ℝ)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have hpos : ∀ d : ℕ, (0 : ℝ) < (((cyclotomic d ℤ).eval 2 : ℤ) : ℝ) := fun d => by
      exact_mod_cast cyclotomic_pos' d (R := ℤ) (x := 2) (by norm_num)
    have hprod : ∏ d ∈ n.divisors, (((cyclotomic d ℤ).eval 2 : ℤ) : ℝ) = (2 : ℝ) ^ n - 1 := by
      have h := congrArg (Polynomial.eval (2 : ℤ)) (prod_cyclotomic_eq_X_pow_sub_one hn ℤ)
      rw [eval_prod] at h
      have h2 := congrArg (fun z : ℤ => (z : ℝ)) h
      simp only [Int.cast_prod] at h2
      rw [h2]
      simp
    rw [← Nat.insert_self_properDivisors hn.ne',
      Finset.prod_insert (by simp : n ∉ n.properDivisors)] at hprod
    have hlog : Real.log (((cyclotomic n ℤ).eval 2 : ℤ) : ℝ) = Real.log ((2 : ℝ) ^ n - 1) -
        ∑ d ∈ n.properDivisors, Real.log (((cyclotomic d ℤ).eval 2 : ℤ) : ℝ) := by
      rw [← hprod, Real.log_mul (hpos n).ne' (Finset.prod_pos fun d _ => hpos d).ne',
        Real.log_prod (fun d _ => (hpos d).ne')]
      ring
    rw [hlog]
    refine (isFValue_log_two_pow_sub_one hn).sub ?_
    exact Submodule.sum_mem fValues fun d hd =>
      ih d (Nat.mem_properDivisors.1 hd).2 (Nat.pos_of_mem_properDivisors hd)

/-- `log N(Φ_n(z))` is a value, for `N(z) = 2`, as soon as the `log N(z^d - 1)` are. -/
theorem isFValue_log_norm_cyclotomic {z : GaussianInt} (hz : z.norm = 2) {P : ℕ → Prop}
    (hP : ∀ n d : ℕ, P n → d ∣ n → P d)
    (hU : ∀ n : ℕ, 0 < n → P n → IsFValue (Real.log (((z ^ n - 1).norm : ℤ) : ℝ))) :
    ∀ n : ℕ, 0 < n → P n →
      IsFValue (Real.log ((((cyclotomic n GaussianInt).eval z).norm : ℤ) : ℝ)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hPn
    have hpos : ∀ d : ℕ, 0 < d →
        (0 : ℝ) < ((((cyclotomic d GaussianInt).eval z).norm : ℤ) : ℝ) := fun d hd => by
      have h0 : ((cyclotomic d GaussianInt).eval z).norm ≠ 0 := fun h0 =>
        norm_pow_sub_one_ne_zero hz hd (zero_dvd_iff.1 (h0 ▸ norm_eval_cyclotomic_dvd z hd))
      have h1 := GaussianInt.norm_nonneg ((cyclotomic d GaussianInt).eval z)
      exact_mod_cast lt_of_le_of_ne h1 (Ne.symm h0)
    have hprod : ∏ d ∈ n.divisors, ((((cyclotomic d GaussianInt).eval z).norm : ℤ) : ℝ) =
        (((z ^ n - 1).norm : ℤ) : ℝ) := by
      exact_mod_cast prod_norm_eval_cyclotomic z hn
    rw [← Nat.insert_self_properDivisors hn.ne',
      Finset.prod_insert (by simp : n ∉ n.properDivisors)] at hprod
    have hpd : ∀ d ∈ n.properDivisors, 0 < d := fun d hd => Nat.pos_of_mem_properDivisors hd
    have hlog : Real.log ((((cyclotomic n GaussianInt).eval z).norm : ℤ) : ℝ) =
        Real.log (((z ^ n - 1).norm : ℤ) : ℝ) -
          ∑ d ∈ n.properDivisors,
            Real.log ((((cyclotomic d GaussianInt).eval z).norm : ℤ) : ℝ) := by
      rw [← hprod, Real.log_mul (hpos n hn).ne'
          (Finset.prod_pos fun d hd => hpos d (hpd d hd)).ne',
        Real.log_prod (fun d hd => (hpos d (hpd d hd)).ne')]
      ring
    rw [hlog]
    refine (hU n hn hPn).sub ?_
    exact Submodule.sum_mem fValues fun d hd =>
      ih d (Nat.mem_properDivisors.1 hd).2 (hpd d hd)
        (hP n d hPn (Nat.mem_properDivisors.1 hd).1)

/-- `log N(Φ_n(1+i))` is a value of the class F, for every `n ≥ 1`. -/
theorem isFValue_log_Aplus {n : ℕ} (hn : 0 < n) : IsFValue (Real.log ((Aplus n : ℤ) : ℝ)) :=
  isFValue_log_norm_cyclotomic norm_tG (P := fun _ => True) (fun _ _ _ _ => trivial)
    (fun _ hm _ => isFValue_log_norm hm (one_pow 4)) n hn trivial

/-- `log N(Φ_n(-1-i))` is a value of the class F, for every odd `n`. -/
theorem isFValue_log_Aminus {n : ℕ} (hn : Odd n) : IsFValue (Real.log ((Aminus n : ℤ) : ℝ)) := by
  refine isFValue_log_norm_cyclotomic norm_neg_tG (P := fun m => Odd m)
    (fun _ d hm hd => hm.of_dvd_nat hd) (fun _ hm hodd => ?_) n hn.pos hn
  obtain ⟨k, rfl⟩ := hodd
  have h := isFValue_log_norm (n := 2 * k + 1) hm neg_one_pow_four'
  rw [← Uminus_odd] at h
  exact h

/-! ## 2. Prime divisors of `Φ_n(2)` -/

theorem homogeneous_eq_cyclotomic (n : ℕ) :
    TauCeti.homogeneousCyclotomic n ((2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) = (cyclotomic n ℤ).eval 2 := by
  rw [Nat.cast_ofNat, Nat.cast_one, TauCeti.homogeneousCyclotomic_one_right]

theorem not_dvd_one_int {p : ℕ} (hp : p.Prime) : ¬ (p : ℤ) ∣ ((1 : ℕ) : ℤ) := by
  norm_cast
  exact hp.not_dvd_one

/-- A prime divisor of `Φ_n(2)` is odd. -/
theorem ne_two_of_dvd_cyclotomic {n p : ℕ} (hp : p.Prime)
    (hdvd : (p : ℤ) ∣ (cyclotomic n ℤ).eval 2) : p ≠ 2 := by
  have hdvd' := (homogeneous_eq_cyclotomic n).symm ▸ hdvd
  have h2 : ¬ p ∣ 2 * 1 :=
    Nat.Coprime.not_dvd_mul_of_dvd_homogeneousCyclotomic (by norm_num) hp hdvd'
  rintro rfl
  exact h2 (by norm_num)

/-- A prime divisor of `Φ_n(2)` that does not divide `n` has order `n`. -/
theorem orderOf_two_of_not_dvd {n p : ℕ} (hn : 0 < n) (hp : p.Prime)
    (hdvd : (p : ℤ) ∣ (cyclotomic n ℤ).eval 2) (hpn : ¬ p ∣ n) :
    orderOf (2 : ZMod p) = n := by
  have hdvd' := (homogeneous_eq_cyclotomic n).symm ▸ hdvd
  have h := (hp.dvd_homogeneousCyclotomic_iff_orderOf_eq (not_dvd_one_int hp) hn.ne').1 hdvd'
  rw [(Nat.ordCompl_eq_self_iff_zero_or_not_dvd n hp).2 (Or.inr hpn)] at h
  simpa using h

/-- Every prime factor of `n` is at most any prime divisor of `Φ_n(2)`. So at most one prime
divisor of `Φ_n(2)` divides `n`: the largest prime factor of `n`. -/
theorem le_of_dvd_cyclotomic {n p q : ℕ} (hp : p.Prime)
    (hdvd : (p : ℤ) ∣ (cyclotomic n ℤ).eval 2) (hq : q.Prime) (hqn : q ∣ n) : q ≤ p :=
  hp.le_of_dvd_homogeneousCyclotomic_of_prime_of_dvd (not_dvd_one_int hp)
    ((homogeneous_eq_cyclotomic n).symm ▸ hdvd) hq hqn

theorem orderOf_two_pos {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) : 0 < orderOf (2 : ZMod ℓ) := by
  have := Fact.mk hℓ
  have h2 : (2 : ZMod ℓ) ≠ 0 := by
    intro h
    have h3 : ((2 : ℕ) : ZMod ℓ) = 0 := by exact_mod_cast h
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1
      ((ZMod.natCast_eq_zero_iff 2 ℓ).1 h3))
  have hℓ1 := hℓ.two_le
  exact orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2
    ⟨ℓ - 1, by omega, ZMod.pow_card_sub_one_eq_one h2⟩)

/-- The order of 2 modulo a prime that does not divide `2^60 - 1` does not divide 60. -/
theorem orderOf_two_not_dvd_sixty {ℓ : ℕ} (hℓ : ℓ.Prime) (hcop : Nat.Coprime (2 ^ 60 - 1) ℓ) :
    ¬ orderOf (2 : ZMod ℓ) ∣ 60 := by
  intro h
  have h1 : (2 : ZMod ℓ) ^ 60 = 1 := orderOf_dvd_iff_pow_eq_one.1 h
  have h2 : ((2 ^ 60 - 1 : ℕ) : ZMod ℓ) = 0 := by
    rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, h1,
      sub_self]
  have h3 : ℓ ∣ 2 ^ 60 - 1 := (ZMod.natCast_eq_zero_iff _ _).1 h2
  have h4 : ℓ ∣ Nat.gcd (2 ^ 60 - 1) ℓ := Nat.dvd_gcd h3 dvd_rfl
  rw [hcop] at h4
  exact hℓ.one_lt.ne' (Nat.dvd_one.1 h4)

/-! ## 3. The atoms of a given index -/

/-- A prime of order `4 n` divides the norm of the atom `R k e` of index `4 n`. -/
theorem dvd_norm_atom_R {p : ℕ} (hp : p.Prime) (k e : ℕ)
    (hord : orderOf (2 : ZMod p) = 4 * nOf (.R k e)) : (p : ℤ) ∣ (atom (.R k e)).norm := by
  have := Fact.mk hp
  have hn0 : 0 < 2 ^ (e + 1) * (2 * k + 1) := by positivity
  have hord' : orderOf (2 : ZMod p) = 4 * (2 ^ (e + 1) * (2 * k + 1)) := hord
  have h4 : p ∣ 4 ^ (2 ^ (e + 1) * (2 * k + 1)) + 1 := dvd_four_pow_add_one_of_orderOf hn0 hord'
  have hprod := prod_norm_eval_cyclotomic (xR e) (n := 2 * k + 1) (by omega)
  rw [norm_xR_pow_sub_one] at hprod
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hdv : (p : ℤ) ∣ ∏ d ∈ (2 * k + 1).divisors,
      ((cyclotomic d GaussianInt).eval (xR e)).norm := by
    rw [hprod]
    exact_mod_cast h4
  obtain ⟨d, hd, hpd⟩ := (hpZ.dvd_finsetProd_iff _).1 hdv
  have hdm : d ∣ 2 * k + 1 := Nat.dvd_of_mem_divisors hd
  obtain ⟨l, rfl⟩ : Odd d := (odd_two_mul_add_one k).of_dvd_nat hdm
  have h5 : (p : ℤ) ∣ 4 ^ (2 ^ (e + 1) * (2 * l + 1)) + 1 := by
    have := hpd.trans (norm_eval_cyclotomic_dvd (xR e) (n := 2 * l + 1) (by omega))
    rwa [norm_xR_pow_sub_one] at this
  have h6 : p ∣ 4 ^ (2 ^ (e + 1) * (2 * l + 1)) + 1 := by exact_mod_cast h5
  have h7 := (dvd_and_odd_of_orderOf hn0 hord' h6).1
  have hmd : 2 * k + 1 ∣ 2 * l + 1 := Nat.dvd_of_mul_dvd_mul_left (by positivity) h7
  have heq : 2 * l + 1 = 2 * k + 1 := Nat.dvd_antisymm hdm hmd
  rw [heq] at hpd
  exact hpd

/-- A prime `ℓ ≡ 1 (mod 4)` does not divide both `N(Φ_m(1+i))` and `N(Φ_m(-1-i))`. -/
theorem not_dvd_norm_P_and_Q {ℓ : ℕ} (hℓ : ℓ.Prime) (h4 : ℓ % 4 = 1) (k : ℕ)
    (h1 : (ℓ : ℤ) ∣ (atom (.P k)).norm) (h2 : (ℓ : ℤ) ∣ (atom (.Q k)).norm) : False := by
  have hℓ2 : ℓ ≠ 2 := by omega
  obtain ⟨ρ, -, hpi, hρP⟩ := exists_prime_dvd_of_dvd_norm hℓ h4 h1
  obtain ⟨ρ', hρ', hpi', hρQ⟩ := exists_prime_dvd_of_dvd_norm hℓ h4 h2
  obtain ⟨hn1, hn2⟩ := not_dvd_pair hpi' hℓ hℓ2 (a := .Q k) (b := .P k) rfl
    (by intro h; cases h) hρQ
  have hdiv : ρ' ∣ ρ * star ρ := by
    rw [hpi, ← hpi']
    exact dvd_mul_right _ _
  rcases hρ'.dvd_or_dvd hdiv with h | h
  · exact hn1 (h.trans hρP)
  · apply hn2
    obtain ⟨w, hw⟩ := hρP
    exact h.trans ⟨star w, by rw [hw, star_mul']⟩

/-- The prime of Lemma 3 for an atom whose norm `ℓ` does not divide. -/
theorem atom_prime_of_not_dvd {ℓ : ℕ} {a : Atom} (hex : a ∉ exceptional)
    (h : ¬ (ℓ : ℤ) ∣ (atom a).norm) :
    ∃ p, p ≠ ℓ ∧ p.Prime ∧ p % 4 = 1 ∧ p ≠ 2 ∧ ¬ p ∣ mOf a ∧ (p : ℤ) ∣ (atom a).norm := by
  obtain ⟨p, hp, hord', hdvd⟩ := exists_primitive_atom a hex
  have : Fact p.Prime := ⟨hp⟩
  have hge := prime_ge_of_orderOf (nOf_pos a) hord'
  have hle := mOf_le_nOf a
  refine ⟨p, ?_, hp, mod_four_eq_one_of_orderOf (nOf_pos a) hord',
    ne_two_of_orderOf (nOf_pos a) hord',
    Nat.not_dvd_of_pos_of_lt (mOf_odd a).pos (by omega), hdvd⟩
  rintro rfl
  exact h hdvd

/-- A prime `q ≠ ℓ` of order equal to the index of an atom, dividing its norm. -/
theorem atom_prime_of_order {ℓ q : ℕ} (hq : q.Prime) (hqℓ : q ≠ ℓ) {a : Atom}
    (hord : orderOf (2 : ZMod q) = 4 * nOf a) (hdvd : (q : ℤ) ∣ (atom a).norm) :
    ∃ p, p ≠ ℓ ∧ p.Prime ∧ p % 4 = 1 ∧ p ≠ 2 ∧ ¬ p ∣ mOf a ∧ (p : ℤ) ∣ (atom a).norm := by
  have : Fact q.Prime := ⟨hq⟩
  have hge := prime_ge_of_orderOf (nOf_pos a) hord
  have hle := mOf_le_nOf a
  exact ⟨q, hqℓ, hq, mod_four_eq_one_of_orderOf (nOf_pos a) hord,
    ne_two_of_orderOf (nOf_pos a) hord,
    Nat.not_dvd_of_pos_of_lt (mOf_odd a).pos (by omega), hdvd⟩

/-! ## 4. The primitive part that contains `ℓ` -/

open Classical in
/-- The primitive part that contains the prime `ℓ`: with `n` the order of 2 modulo `ℓ`, it is
`Φ_n(2)` if `n` is not 4 modulo 8, and for `n = 4d`, `d` odd, the one of `N(Φ_d(1+i))`,
`N(Φ_d(-1-i))` that `ℓ` divides. -/
noncomputable def primPart (ℓ : ℕ) : ℤ :=
  if orderOf (2 : ZMod ℓ) % 8 = 4 then
    (if (ℓ : ℤ) ∣ Aplus (orderOf (2 : ZMod ℓ) / 4) then Aplus (orderOf (2 : ZMod ℓ) / 4)
    else Aminus (orderOf (2 : ZMod ℓ) / 4))
  else (cyclotomic (orderOf (2 : ZMod ℓ)) ℤ).eval 2

theorem primPart_eq_cyclotomic {ℓ n : ℕ} (hord : orderOf (2 : ZMod ℓ) = n) (h : n % 8 ≠ 4) :
    primPart ℓ = (cyclotomic n ℤ).eval 2 := by
  subst hord
  simp only [primPart, h, ↓reduceIte]

theorem primPart_eq_Aplus {ℓ n d : ℕ} (hord : orderOf (2 : ZMod ℓ) = n) (h : n % 8 = 4)
    (hd : n / 4 = d) (hdvd : (ℓ : ℤ) ∣ Aplus d) : primPart ℓ = Aplus d := by
  subst hord hd
  simp only [primPart, h, hdvd, ↓reduceIte]

theorem primPart_eq_Aminus {ℓ n d : ℕ} (hord : orderOf (2 : ZMod ℓ) = n) (h : n % 8 = 4)
    (hd : n / 4 = d) (hdvd : ¬ (ℓ : ℤ) ∣ Aplus d) : primPart ℓ = Aminus d := by
  subst hord hd
  simp only [primPart, h, hdvd, ↓reduceIte]

/-- The three facts about the primitive part: it divides `Φ_n(2)`, it is positive and `ℓ`
divides it; and its logarithm is a value of the class F. -/
theorem primPart_facts {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) :
    primPart ℓ ∣ (cyclotomic (orderOf (2 : ZMod ℓ)) ℤ).eval 2 ∧ 0 < primPart ℓ ∧
      (ℓ : ℤ) ∣ primPart ℓ ∧ IsFValue (Real.log ((primPart ℓ : ℤ) : ℝ)) := by
  have := Fact.mk hℓ
  obtain ⟨n, hord⟩ : ∃ n, orderOf (2 : ZMod ℓ) = n := ⟨_, rfl⟩
  have hn : 0 < n := hord ▸ orderOf_two_pos hℓ hℓ2
  have hΦpos : 0 < (cyclotomic n ℤ).eval 2 := cyclotomic_pos' n (by norm_num)
  have hℓΦ : (ℓ : ℤ) ∣ (cyclotomic n ℤ).eval 2 := dvd_cyclotomic_of_orderOf hn hord
  rw [hord]
  by_cases h8 : n % 8 = 4
  · obtain ⟨d, hd⟩ : ∃ d, n / 4 = d := ⟨_, rfl⟩
    have hnd : 4 * d = n := by omega
    have hodd : Odd d := Nat.odd_iff.2 (by omega)
    have hmul : Aplus d * Aminus d = (cyclotomic n ℤ).eval 2 := by
      rw [Aplus_mul_Aminus hodd, Phi4, hnd]
    have hA : 0 < Aplus d := by
      refine lt_of_le_of_ne (Aplus_nonneg d) fun h0 => ?_
      rw [← h0, zero_mul] at hmul
      omega
    have hA' : 0 < Aminus d := by
      refine lt_of_le_of_ne (Aminus_nonneg d) fun h0 => ?_
      rw [← h0, mul_zero] at hmul
      omega
    by_cases hdvd : (ℓ : ℤ) ∣ Aplus d
    · rw [primPart_eq_Aplus hord h8 hd hdvd]
      exact ⟨⟨_, hmul.symm⟩, hA, hdvd, isFValue_log_Aplus hodd.pos⟩
    · rw [primPart_eq_Aminus hord h8 hd hdvd]
      refine ⟨⟨Aplus d, by rw [← hmul, mul_comm]⟩, hA', ?_, isFValue_log_Aminus hodd⟩
      rw [← hmul] at hℓΦ
      exact ((Nat.prime_iff_prime_int.1 hℓ).dvd_or_dvd hℓΦ).resolve_left hdvd
  · rw [primPart_eq_cyclotomic hord h8]
    exact ⟨dvd_rfl, hΦpos, hℓΦ, isFValue_log_cyclotomic_two n hn⟩

/-! ## 5. A second primitive prime excludes `ℓ` -/

/-- **A partner excludes `ℓ`** (from Baker's theorem). Let `ℓ` be an odd prime that does not
divide `2^60 - 1`, and `n` the order of 2 modulo `ℓ`. If a prime `q ≠ ℓ` that does not divide
`n` divides the primitive part that contains `ℓ`, then `log ℓ` is not a value of the class
F. -/
theorem not_isFValue_log_of_partner (hB : BakerTheorem) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hcop : Nat.Coprime (2 ^ 60 - 1) ℓ) {q : ℕ} (hq : q.Prime) (hqℓ : q ≠ ℓ)
    (hqg : (q : ℤ) ∣ primPart ℓ) (hqn : ¬ q ∣ orderOf (2 : ZMod ℓ)) :
    ¬ IsFValue (Real.log ℓ) := by
  have := Fact.mk hℓ
  have hqΦ0 := hqg.trans (primPart_facts hℓ hℓ2).1
  obtain ⟨n, hord⟩ : ∃ n, orderOf (2 : ZMod ℓ) = n := ⟨_, rfl⟩
  rw [hord] at hqn hqΦ0
  have hn : 0 < n := hord ▸ orderOf_two_pos hℓ hℓ2
  have hordq : orderOf (2 : ZMod q) = n := orderOf_two_of_not_dvd hn hq hqΦ0 hqn
  have hq2 : q ≠ 2 := ne_two_of_dvd_cyclotomic hq hqΦ0
  refine not_isFValue_log hB hℓ hℓ2 hcop (goodPrimes_ne hord ?_ ?_ ?_)
  · -- the atoms of index `n`
    intro a hex han
    rcases a with k | k | ⟨k, e⟩
    · have han' : 4 * (2 * k + 1) = n := han
      have h8 : n % 8 = 4 := by omega
      have hd : n / 4 = 2 * k + 1 := by omega
      by_cases hdvd : (ℓ : ℤ) ∣ Aplus (2 * k + 1)
      · rw [primPart_eq_Aplus hord h8 hd hdvd] at hqg
        exact atom_prime_of_order hq hqℓ (hordq.trans han.symm) hqg
      · exact atom_prime_of_not_dvd hex hdvd
    · have han' : 4 * (2 * k + 1) = n := han
      have h8 : n % 8 = 4 := by omega
      have hd : n / 4 = 2 * k + 1 := by omega
      by_cases hdvd : (ℓ : ℤ) ∣ Aplus (2 * k + 1)
      · have h4 : ℓ % 4 = 1 :=
          mod_four_eq_one_of_orderOf (n := 2 * k + 1) (by omega) (hord.trans han'.symm)
        exact atom_prime_of_not_dvd hex fun h => not_dvd_norm_P_and_Q hℓ h4 k hdvd h
      · rw [primPart_eq_Aminus hord h8 hd hdvd] at hqg
        exact atom_prime_of_order hq hqℓ (hordq.trans han.symm) hqg
    · have hordq' : orderOf (2 : ZMod q) = 4 * nOf (.R k e) := hordq.trans han.symm
      exact atom_prime_of_order hq hqℓ hordq' (dvd_norm_atom_R hq k e hordq')
  · -- `n` odd
    intro k _ hkn
    have h8 : n % 8 ≠ 4 := by omega
    rw [primPart_eq_cyclotomic hord h8] at hqg
    exact ⟨q, hqℓ, hq, hq2, hkn ▸ hqn, hkn ▸ hqg⟩
  · -- `n` twice an odd number
    intro k hk hkn
    have h8 : n % 8 ≠ 4 := by omega
    rw [primPart_eq_cyclotomic hord h8, ← hkn,
      cyclotomic_two_mul_of_odd ⟨k, rfl⟩ (by omega) ℤ, eval_comp, eval_neg, eval_X] at hqg
    refine ⟨q, hqℓ, hq, hq2, fun h => hqn (h.trans ⟨2, by rw [← hkn]; ring⟩), ?_⟩
    simpa using hqg

/-! ## 6. The test -/

/-- If the logarithms of the prime factors of `H` are values of the class F, so is
`log H`. -/
theorem isFValue_log_of_primeFactors : ∀ H : ℕ, 0 < H →
    (∀ q : ℕ, q.Prime → q ∣ H → IsFValue (Real.log q)) → IsFValue (Real.log H) := by
  intro H
  induction H using Nat.strong_induction_on with
  | _ H ih =>
    intro hH h
    rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hH) with h1 | h1
    · rw [← h1]
      simpa using isFValue_zero
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

/-- **The finite test for a prime** (from Baker's theorem). Let `ℓ` be an odd prime that does
not divide `2^60 - 1` and `n` the order of 2 modulo `ℓ`. Then `log ℓ` is a value of the class
F if and only if every prime `q ≠ ℓ` dividing the primitive part that contains `ℓ` divides
`n` and has `log q` a value of the class F. -/
theorem isFValue_log_prime_iff (hB : BakerTheorem) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hcop : Nat.Coprime (2 ^ 60 - 1) ℓ) :
    IsFValue (Real.log ℓ) ↔ ∀ q : ℕ, q.Prime → (q : ℤ) ∣ primPart ℓ → q ≠ ℓ →
      q ∣ orderOf (2 : ZMod ℓ) ∧ IsFValue (Real.log q) := by
  obtain ⟨hgΦ, hgpos, hℓg, hVg⟩ := primPart_facts hℓ hℓ2
  obtain ⟨G, hG⟩ := Int.eq_ofNat_of_zero_le hgpos.le
  rw [hG] at hgΦ hgpos hℓg hVg
  have hG0 : 0 < G := by exact_mod_cast hgpos
  have hℓG : ℓ ∣ G := by exact_mod_cast hℓg
  have hVG : IsFValue (Real.log (G : ℝ)) := by exact_mod_cast hVg
  obtain ⟨a, H, hH, hGH⟩ := Nat.exists_eq_pow_mul_and_not_dvd hG0.ne' ℓ hℓ.ne_one
  have hH0 : 0 < H := Nat.pos_of_ne_zero (by rintro rfl; exact hH (dvd_zero _))
  have ha : 0 < a := by
    rcases Nat.eq_zero_or_pos a with rfl | h
    · rw [pow_zero, one_mul] at hGH
      exact absurd (hGH ▸ hℓG) hH
    · exact h
  have hℓR : (ℓ : ℝ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hlog : Real.log (G : ℝ) = a * Real.log (ℓ : ℝ) + Real.log (H : ℝ) := by
    rw [hGH]
    push_cast
    rw [Real.log_mul (pow_ne_zero _ hℓR) (by exact_mod_cast hH0.ne'), Real.log_pow]
  have hdvdG : ∀ p : ℕ, (p : ℤ) ∣ primPart ℓ ↔ p ∣ G := fun p => by
    rw [hG]
    exact Int.natCast_dvd_natCast
  constructor
  · intro hval q hq hqg hqℓ
    have hqG : q ∣ G := (hdvdG q).1 hqg
    -- every prime factor of `G` other than `ℓ` divides `n`
    have hdvdn : ∀ p : ℕ, p.Prime → p ∣ G → p ≠ ℓ → p ∣ orderOf (2 : ZMod ℓ) := by
      intro p hp hpG hpℓ
      by_contra hpn
      exact not_isFValue_log_of_partner hB hℓ hℓ2 hcop hp hpℓ ((hdvdG p).2 hpG) hpn hval
    refine ⟨hdvdn q hq hqG hqℓ, ?_⟩
    have hΦ : ∀ p : ℕ, p ∣ G → (p : ℤ) ∣ (cyclotomic (orderOf (2 : ZMod ℓ)) ℤ).eval 2 :=
      fun p hpG => (Int.natCast_dvd_natCast.2 hpG).trans hgΦ
    -- so every prime factor of `H` is `q`
    have hHq : ∀ {p : ℕ}, p.Prime → p ∣ H → p = q := by
      intro p hp hpH
      have hpℓ : p ≠ ℓ := by
        rintro rfl
        exact hH hpH
      have hpG : p ∣ G := hGH ▸ Dvd.dvd.mul_left hpH _
      exact le_antisymm
        (le_of_dvd_cyclotomic hq (hΦ q hqG) hp (hdvdn p hp hpG hpℓ))
        (le_of_dvd_cyclotomic hp (hΦ p hpG) hq (hdvdn q hq hqG hqℓ))
    have hHpow := Nat.eq_prime_pow_of_unique_prime_dvd hH0.ne' hHq
    obtain ⟨b, hb⟩ : ∃ b, H.primeFactorsList.length = b := ⟨_, rfl⟩
    rw [hb] at hHpow
    have hqH : q ∣ H := by
      rw [hGH] at hqG
      rcases (Nat.Prime.dvd_mul hq).1 hqG with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hq hℓ).1 (hq.dvd_of_dvd_pow h)) hqℓ
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
    have h1 : IsFValue ((b : ℝ) * Real.log (q : ℝ)) := by
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
    have hHV : IsFValue (Real.log (H : ℝ)) :=
      isFValue_log_of_primeFactors H hH0 fun p hp hpH =>
        (h p hp ((hdvdG p).2 (hGH ▸ Dvd.dvd.mul_left hpH _))
          (by rintro rfl; exact hH hpH)).2
    have h1 : IsFValue ((a : ℝ) * Real.log (ℓ : ℝ)) := by
      have h2 := hVG.sub hHV
      rw [hlog] at h2
      convert h2 using 1
      ring
    have h3 := h1.const_mul ((a : ℚ)⁻¹)
    have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
    convert h3 using 1
    push_cast
    field_simp

/-- At most one prime other than `ℓ` can pass the condition of the test: two primes that
divide the primitive part and the order `n` are equal. -/
theorem primPart_intrinsic_unique {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpg : (p : ℤ) ∣ primPart ℓ) (hqg : (q : ℤ) ∣ primPart ℓ)
    (hpn : p ∣ orderOf (2 : ZMod ℓ)) (hqn : q ∣ orderOf (2 : ZMod ℓ)) : p = q :=
  le_antisymm
    (le_of_dvd_cyclotomic hq (hqg.trans (primPart_facts hℓ hℓ2).1) hp hpn)
    (le_of_dvd_cyclotomic hp (hpg.trans (primPart_facts hℓ hℓ2).1) hq hqn)

/-- **The test in the form of the note** (from Baker's theorem). For an odd prime `ℓ` that
does not divide `2^60 - 1`, with `n` the order of 2 modulo `ℓ`: `log ℓ` is a value of the
class F if and only if the primitive part that contains `ℓ` is a power of `ℓ`, or a power of
`ℓ` times one prime `q` that divides `n` and has `log q` a value of the class F. -/
theorem isFValue_log_prime_iff_explicit (hB : BakerTheorem) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hcop : Nat.Coprime (2 ^ 60 - 1) ℓ) :
    IsFValue (Real.log ℓ) ↔ (∃ x : ℕ, primPart ℓ = (ℓ : ℤ) ^ x) ∨
      ∃ x q : ℕ, q.Prime ∧ q ∣ orderOf (2 : ZMod ℓ) ∧ primPart ℓ = (ℓ : ℤ) ^ x * q ∧
        IsFValue (Real.log q) := by
  rw [isFValue_log_prime_iff hB hℓ hℓ2 hcop]
  obtain ⟨hgΦ, hgpos, -, -⟩ := primPart_facts hℓ hℓ2
  constructor
  · intro C
    obtain ⟨G, hG⟩ := Int.eq_ofNat_of_zero_le hgpos.le
    have hG0 : 0 < G := by
      rw [hG] at hgpos
      exact_mod_cast hgpos
    obtain ⟨a, H, hH, hGH⟩ := Nat.exists_eq_pow_mul_and_not_dvd hG0.ne' ℓ hℓ.ne_one
    have hH0 : 0 < H := Nat.pos_of_ne_zero (by rintro rfl; exact hH (dvd_zero _))
    have hHg : ∀ p : ℕ, p ∣ H → (p : ℤ) ∣ primPart ℓ := by
      intro p hpH
      rw [hG, hGH]
      exact Int.natCast_dvd_natCast.2 (Dvd.dvd.mul_left hpH _)
    have hC : ∀ p : ℕ, p.Prime → p ∣ H →
        p ∣ orderOf (2 : ZMod ℓ) ∧ IsFValue (Real.log p) := fun p hp hpH =>
      C p hp (hHg p hpH) (by rintro rfl; exact hH hpH)
    have hΦ : ∀ p : ℕ, p ∣ H → (p : ℤ) ∣ (cyclotomic (orderOf (2 : ZMod ℓ)) ℤ).eval 2 :=
      fun p hpH => (hHg p hpH).trans hgΦ
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
      have hHq : ∀ {p : ℕ}, p.Prime → p ∣ H → p = q := fun {p} hp hpH =>
        le_antisymm (le_of_dvd_cyclotomic hq (hΦ q hqH) hp (hC p hp hpH).1)
          (le_of_dvd_cyclotomic hp (hΦ p hpH) hq hqn)
      have hHpow := Nat.eq_prime_pow_of_unique_prime_dvd hH0.ne' hHq
      obtain ⟨b, hb⟩ : ∃ b, H.primeFactorsList.length = b := ⟨_, rfl⟩
      rw [hb] at hHpow
      -- `q` divides `Φ_n(2)` exactly once
      have hn2 : orderOf (2 : ZMod ℓ) ≠ 2 := fun h =>
        orderOf_two_not_dvd_sixty hℓ hcop (h ▸ by norm_num)
      have hmul := hq.multiplicity_homogeneousCyclotomic_eq_one (a := 2) (b := 1)
        (by norm_num) hq.not_dvd_one hqn hn2 ((homogeneous_eq_cyclotomic _).symm ▸ hΦ q hqH)
      rw [homogeneous_eq_cyclotomic] at hmul
      have hb1 : b = 1 := by
        rcases (show b = 0 ∨ b = 1 ∨ 2 ≤ b by omega) with rfl | h | h
        · rw [pow_zero] at hHpow
          omega
        · exact h
        · exfalso
          have hsq : (q : ℤ) ^ 2 ∣ (cyclotomic (orderOf (2 : ZMod ℓ)) ℤ).eval 2 := by
            have h2 : q ^ 2 ∣ H := by
              rw [hHpow]
              exact pow_dvd_pow q h
            have h3 := hΦ (q ^ 2) h2
            simpa using h3
          have hfin : FiniteMultiplicity (q : ℤ)
              ((cyclotomic (orderOf (2 : ZMod ℓ)) ℤ).eval 2) :=
            FiniteMultiplicity.of_prime_left (Nat.prime_iff_prime_int.1 hq)
              (cyclotomic_pos' _ (by norm_num)).ne'
          exact hfin.not_pow_dvd_of_multiplicity_lt (by rw [hmul]; norm_num) hsq
      refine ⟨a, q, hq, hqn, ?_, hqV⟩
      rw [hG, hGH, hHpow, hb1]
      push_cast
      ring
  · rintro (⟨x, hx⟩ | ⟨x, q0, hq0, hq0n, hx, hV⟩) q hq hqg hqℓ
    · exfalso
      rw [hx] at hqg
      have h1 : q ∣ ℓ ^ x := by exact_mod_cast hqg
      exact hqℓ ((Nat.prime_dvd_prime_iff_eq hq hℓ).1 (hq.dvd_of_dvd_pow h1))
    · rw [hx] at hqg
      have h1 : q ∣ ℓ ^ x * q0 := by exact_mod_cast hqg
      rcases (Nat.Prime.dvd_mul hq).1 h1 with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hq hℓ).1 (hq.dvd_of_dvd_pow h)) hqℓ
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hq hq0).1 h
        exact ⟨hq0n, hV⟩

/-! ## 7. The primes that divide `2^60 - 1`, and the classification -/

/-- `151 = Φ_15(2) = (2^15 - 1) / (31 · 7)`. -/
theorem isFValue_log_151 : IsFValue (Real.log 151) := by
  have h := ((isFValue_log_two_pow_sub_one (m := 15) (by norm_num)).sub isFValue_log_31).sub
    isFValue_log_7
  have e : Real.log ((2 : ℝ) ^ 15 - 1) - Real.log 31 - Real.log 7 = Real.log 151 := by
    have h1 : (2 : ℝ) ^ 15 - 1 = 151 * 31 * 7 := by norm_num
    rw [h1, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]
    ring
  rwa [e] at h

/-- `331 = Φ_30(2)`, and `2^30 - 1 = 3^2 · 7 · 11 · 31 · 151 · 331`. -/
theorem isFValue_log_331 : IsFValue (Real.log 331) := by
  have h := (((((isFValue_log_two_pow_sub_one (m := 30) (by norm_num)).sub
    (isFValue_log_3.const_mul 2)).sub isFValue_log_7).sub isFValue_log_11).sub
    isFValue_log_31).sub isFValue_log_151
  have e : Real.log ((2 : ℝ) ^ 30 - 1) - ((2 : ℚ) : ℝ) * Real.log 3 - Real.log 7 - Real.log 11 -
      Real.log 31 - Real.log 151 = Real.log 331 := by
    have h1 : (2 : ℝ) ^ 30 - 1 = 3 ^ 2 * 7 * 11 * 31 * 151 * 331 := by norm_num
    rw [h1, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast
    ring
  rwa [e] at h

/-- `1321`: `2^15 + 2^8 + 1 = 5^2 · 1321`. -/
theorem isFValue_log_1321 : IsFValue (Real.log 1321) := by
  have hM : M (2 * 7 + 1) = 33025 := by norm_num [M]
  have h0 := isFValue_log_M 7
  rw [hM] at h0
  have h := h0.sub (isFValue_log_5.const_mul 2)
  have e : Real.log ((33025 : ℤ) : ℝ) - ((2 : ℚ) : ℝ) * Real.log 5 = Real.log 1321 := by
    have h1 : ((33025 : ℤ) : ℝ) = 5 ^ 2 * 1321 := by norm_num
    rw [h1, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast
    ring
  rwa [e] at h

/-- **The twelve small primes.** If the prime `ℓ` divides `2 (2^60 - 1)`, that is, if `ℓ` is
one of `2, 3, 5, 7, 11, 13, 31, 41, 61, 151, 331, 1321`, then `log ℓ` is a value of the class
F. -/
theorem isFValue_log_of_dvd {ℓ : ℕ} (hℓ : ℓ.Prime) (h : ℓ ∣ 2 * (2 ^ 60 - 1)) :
    IsFValue (Real.log ℓ) := by
  have hfac : 2 * (2 ^ 60 - 1) =
      2 * (3 ^ 2 * 5 ^ 2 * 7 * 11 * 13 * 31 * 41 * 61 * 151 * 331 * 1321) := by norm_num
  rw [hfac] at h
  have e : ∀ {p : ℕ}, p.Prime → ℓ ∣ p → ℓ = p := fun hp hd =>
    (Nat.prime_dvd_prime_iff_eq hℓ hp).1 hd
  rcases (Nat.Prime.dvd_mul hℓ).1 h with h | h
  · obtain rfl := e Nat.prime_two h
    simpa using isFValue_log_2
  rcases (Nat.Prime.dvd_mul hℓ).1 h with h | h
  swap
  · obtain rfl := e (by norm_num : Nat.Prime 1321) h
    simpa using isFValue_log_1321
  rcases (Nat.Prime.dvd_mul hℓ).1 h with h | h
  swap
  · obtain rfl := e (by norm_num : Nat.Prime 331) h
    simpa using isFValue_log_331
  rcases (Nat.Prime.dvd_mul hℓ).1 h with h | h
  swap
  · obtain rfl := e (by norm_num : Nat.Prime 151) h
    simpa using isFValue_log_151
  rcases (Nat.Prime.dvd_mul hℓ).1 h with h | h
  swap
  · obtain rfl := e (by norm_num : Nat.Prime 61) h
    simpa using isFValue_log_61
  rcases (Nat.Prime.dvd_mul hℓ).1 h with h | h
  swap
  · obtain rfl := e (by norm_num : Nat.Prime 41) h
    simpa using isFValue_log_41
  rcases (Nat.Prime.dvd_mul hℓ).1 h with h | h
  swap
  · obtain rfl := e (by norm_num : Nat.Prime 31) h
    simpa using isFValue_log_31
  rcases (Nat.Prime.dvd_mul hℓ).1 h with h | h
  swap
  · obtain rfl := e (by norm_num : Nat.Prime 13) h
    simpa using isFValue_log_13
  rcases (Nat.Prime.dvd_mul hℓ).1 h with h | h
  swap
  · obtain rfl := e (by norm_num : Nat.Prime 11) h
    simpa using isFValue_log_11
  rcases (Nat.Prime.dvd_mul hℓ).1 h with h | h
  swap
  · obtain rfl := e (by norm_num : Nat.Prime 7) h
    simpa using isFValue_log_7
  rcases (Nat.Prime.dvd_mul hℓ).1 h with h | h
  · obtain rfl := e Nat.prime_three (hℓ.dvd_of_dvd_pow h)
    simpa using isFValue_log_3
  · obtain rfl := e Nat.prime_five (hℓ.dvd_of_dvd_pow h)
    simpa using isFValue_log_5

/-- **The classification of the primes** (from Baker's theorem). For a prime `ℓ`, `log ℓ` is
a value of the class F if and only if `ℓ` divides `2 (2^60 - 1)` or `ℓ` passes the test:
every prime `q ≠ ℓ` dividing the primitive part that contains `ℓ` divides the order of 2
modulo `ℓ` and has `log q` a value of the class F. -/
theorem isFValue_log_prime_classification (hB : BakerTheorem) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    IsFValue (Real.log ℓ) ↔ ℓ ∣ 2 * (2 ^ 60 - 1) ∨
      ∀ q : ℕ, q.Prime → (q : ℤ) ∣ primPart ℓ → q ≠ ℓ →
        q ∣ orderOf (2 : ZMod ℓ) ∧ IsFValue (Real.log q) := by
  by_cases hd : ℓ ∣ 2 * (2 ^ 60 - 1)
  · exact ⟨fun _ => Or.inl hd, fun _ => isFValue_log_of_dvd hℓ hd⟩
  · have hℓ2 : ℓ ≠ 2 := by
      rintro rfl
      exact hd (dvd_mul_right _ _)
    have hcop : Nat.Coprime (2 ^ 60 - 1) ℓ :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hℓ).2 fun h => hd (Dvd.dvd.mul_left h 2))
    rw [isFValue_log_prime_iff hB hℓ hℓ2 hcop]
    exact ⟨Or.inr, fun h => h.resolve_left hd⟩

end PiFormula
