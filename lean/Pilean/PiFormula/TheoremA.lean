/-
Copyright (c) 2026 Novus Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Novus Technology
-/
module

public import Pilean.PiFormula
public import Pilean.PiFormula.Gaussian
public import Pilean.PiFormula.Orders
public import Pilean.PiFormula.Bang

/-!
# Theorem A: assembly

Status (21 November 2026): complete, no `sorry`.

* `exists_private_prime` and `coeff_eq_zero_of_not_special`: the "largest index"
  argument, from Bang's theorem, Lemma 2 and the order facts of `Orders.lean`;
* `four_generators`: the last step, from R1-R3 and the irrationality of `arctan (1/2) / π`
  (`int_mul_arctan_half_eq_zero`, the private prime `5`);
* `goal`: clearing denominators and putting the pieces together, which proves the
  statement `Goal` of `PiFormula.lean`: Bang's theorem and Lemma 2 imply Theorem A;
* `theoremA_of_lemma2`: Bang's theorem is proved (`Bang.lean`), so Theorem A follows
  from Lemma 2 alone.

Lemma 2 itself (the Aurifeuillian primitive-divisor lemma) is the one remaining input.
-/

@[expose] public section

open Real

namespace PiFormula

/-- Generators: `inl m` stands for `b_m = arctan (1/2^m)`, `inr m` for
`a_m = arctan (1/(2^m - 1))`. -/
abbrev Gen := ℕ ⊕ ℕ

/-- The integer `n` with `arctan (1/n)` the generator. -/
def gen : Gen → ℕ
  | .inl m => 2 ^ m
  | .inr m => 2 ^ m - 1

/-- The four generators that do occur in relations: `a_1, b_1, a_2, a_3` (`n = 1, 2, 3, 7`). -/
def special : Finset Gen := {.inr 1, .inl 1, .inr 2, .inr 3}

/-- The order in which generators are eliminated: twice the top index (`4m` for `b_m`,
`4(2m-1)` for `a_m`), plus 1 for `b_m`, so that `b_n` comes before `a_((n+1)/2)`. -/
def key : Gen → ℕ
  | .inl m => 8 * m + 1
  | .inr m => 8 * (2 * m - 1)

theorem gen_pos {x : Gen} (hx : x ≠ .inl 0 ∧ x ≠ .inr 0) : 0 < gen x := by
  rcases x with m | m
  · exact Nat.two_pow_pos m
  · have : m ≠ 0 := fun h => hx.2 (by rw [h])
    have : 2 ≤ 2 ^ m := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp only [gen]
    omega

/-! ### Helper facts -/

theorem gen_inl_sq (m : ℕ) : gen (.inl m) ^ 2 + 1 = 4 ^ m + 1 := by
  simp only [gen]
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

/-- For the special generators, `gen x ^ 2 + 1` is `2, 5, 10` or `50`, a divisor of 50. -/
theorem gen_sq_dvd_fifty {x : Gen} (hx : x ∈ special) : gen x ^ 2 + 1 ∣ 50 := by
  simp only [special, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> decide

/-- A prime `p ≥ 7` divides no `gen x ^ 2 + 1` with `x` special. -/
theorem not_dvd_special {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) {x : Gen} (hx : x ∈ special) :
    ¬ p ∣ gen x ^ 2 + 1 := by
  intro h
  have h50 : p ∣ 2 * 5 ^ 2 := h.trans (gen_sq_dvd_fifty hx)
  rcases (Nat.Prime.dvd_mul hp).1 h50 with h2 | h5
  · have := Nat.le_of_dvd (by norm_num) h2; omega
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h5); omega

/-- If 2 has order `4n` modulo `p`, then `p ≥ 4n + 1`. -/
theorem prime_ge_of_orderOf {p n : ℕ} [hp : Fact p.Prime] (hn : 0 < n)
    (h : orderOf (2 : ZMod p) = 4 * n) : 4 * n + 1 ≤ p := by
  have hd := ZMod.orderOf_dvd_card_sub_one (two_ne_zero_of_orderOf hn h)
  rw [h] at hd
  have := hp.out.two_le
  have := Nat.le_of_dvd (by omega) hd
  omega

theorem dvd_Mn_of_dvd_M {p n : ℕ} (h : (p : ℤ) ∣ M n) : p ∣ Mn n := by
  have e : ((Mn n : ℕ) : ℤ) = M n := by simp [Mn, M]
  rw [← e] at h
  exact_mod_cast h

theorem dvd_Ln_of_dvd_L {p n : ℕ} (hn : 1 ≤ n) (h : (p : ℤ) ∣ L n) : p ∣ Ln n := by
  have e : ((Ln n : ℕ) : ℤ) = L n := by
    unfold Ln L
    rw [Nat.cast_add, Nat.cast_sub (two_pow_half_le n hn)]
    push_cast
    ring
  rw [← e] at h
  exact_mod_cast h

/-- A prime of order `4n` dividing `N(2^m + i) = 4^m + 1`: then `n ∣ m` and `n ≤ m`. -/
theorem inl_dvd {p n m : ℕ} [Fact p.Prime] (hn : 0 < n) (hord : orderOf (2 : ZMod p) = 4 * n)
    (hm : 0 < m) (h : p ∣ gen (.inl m) ^ 2 + 1) : n ∣ m ∧ n ≤ m := by
  rw [gen_inl_sq] at h
  exact ⟨(dvd_and_odd_of_orderOf hn hord h).1, le_of_orderOf hn hm hord h⟩

/-- A prime of order `4n` dividing `N(2^m - 1 + i) = 2 L(2m-1)`: then `p ∣ L(2m-1)`,
`n ∣ 2m - 1` and `n ≤ 2m - 1`. -/
theorem inr_dvd {p n m : ℕ} [hp : Fact p.Prime] (hn : 0 < n)
    (hord : orderOf (2 : ZMod p) = 4 * n) (hm : 1 ≤ m) (h : p ∣ gen (.inr m) ^ 2 + 1) :
    p ∣ Ln (2 * m - 1) ∧ n ∣ 2 * m - 1 ∧ n ≤ 2 * m - 1 := by
  have hp2 := ne_two_of_orderOf hn hord
  have hLd : p ∣ Ln (2 * m - 1) := by
    simp only [gen] at h
    rw [sq_add_one_eq_two_mul_Ln m hm] at h
    rcases (Nat.Prime.dvd_mul hp.out).1 h with h2 | h2
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 h2) hp2
    · exact h2
  have h4 : p ∣ 4 ^ (2 * m - 1) + 1 := hLd.trans ⟨_, (Ln_mul_Mn m hm).symm⟩
  exact ⟨hLd, (dvd_and_odd_of_orderOf hn hord h4).1, le_of_orderOf hn (by omega) hord h4⟩

/-! ### The private prime -/

/-- **The private prime of the generator of largest key.** -/
theorem exists_private_prime (hB : BangTheorem) (hL : Lemma2) (s : Finset Gen)
    (hs : ∀ x ∈ s, x ≠ .inl 0 ∧ x ≠ .inr 0) (g : Gen) (hg : g ∈ s) (hgs : g ∉ special)
    (hmax : ∀ x ∈ s, x ∉ special → key x ≤ key g) :
    ∃ p, p.Prime ∧ p % 4 = 1 ∧ p ∣ gen g ^ 2 + 1 ∧ ∀ x ∈ s, x ≠ g → ¬ p ∣ gen x ^ 2 + 1 := by
  have pos_inl : ∀ {m}, Sum.inl m ∈ s → 0 < m := fun {m} hx => by
    have := (hs _ hx).1
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exact absurd (by rw [h0]) this
    · exact h0
  have pos_inr : ∀ {m}, Sum.inr m ∈ s → 1 ≤ m := fun {m} hx => by
    have := (hs _ hx).2
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exact absurd (by rw [h0]) this
    · exact h0
  rcases g with n | m₀
  · -- g = b_n
    have hn : 0 < n := pos_inl hg
    have hn1 : n ≠ 1 := fun h => hgs (by simp [special, h])
    rcases Nat.even_or_odd n with hev | hodd
    · -- n even: Bang
      obtain ⟨p, hp, hord⟩ := hB (4 * n) (by omega) (by omega)
      have := Fact.mk hp
      have hp9 := prime_ge_of_orderOf hn hord
      refine ⟨p, hp, mod_four_eq_one_of_orderOf hn hord, ?_, ?_⟩
      · rw [gen_inl_sq]; exact dvd_four_pow_add_one_of_orderOf hn hord
      intro x hx hxg hdvd
      by_cases hxs : x ∈ special
      · exact not_dvd_special hp (by omega) hxs hdvd
      have hkey := hmax x hx hxs
      rcases x with m | m
      · obtain ⟨-, hle⟩ := inl_dvd hn hord (pos_inl hx) hdvd
        simp only [key] at hkey
        exact hxg (by rw [show m = n by omega])
      · obtain ⟨-, hdv, -⟩ := inr_dvd hn hord (pos_inr hx) hdvd
        have h2 : 2 ∣ 2 * m - 1 := hev.two_dvd.trans hdv
        have := pos_inr hx
        omega
    · -- n odd: Lemma 2 for M_n
      obtain ⟨p, ⟨hp, hord⟩, hM⟩ := hL.1 n hodd
      have := Fact.mk hp
      have hp9 := prime_ge_of_orderOf hn hord
      refine ⟨p, hp, mod_four_eq_one_of_orderOf hn hord, ?_, ?_⟩
      · rw [gen_inl_sq]; exact dvd_four_pow_add_one_of_orderOf hn hord
      intro x hx hxg hdvd
      by_cases hxs : x ∈ special
      · exact not_dvd_special hp (by omega) hxs hdvd
      have hkey := hmax x hx hxs
      rcases x with m | m
      · obtain ⟨-, hle⟩ := inl_dvd hn hord (pos_inl hx) hdvd
        simp only [key] at hkey
        exact hxg (by rw [show m = n by omega])
      · obtain ⟨hLd, -, hle⟩ := inr_dvd hn hord (pos_inr hx) hdvd
        simp only [key] at hkey
        have hodd' := hodd
        obtain ⟨k, hk⟩ := hodd'
        have heq : 2 * m - 1 = n := by omega
        have hm2 : 2 ≤ m := by omega
        have hMn : p ∣ Mn (2 * m - 1) := by rw [heq]; exact dvd_Mn_of_dvd_M hM
        exact not_dvd_Ln_and_Mn m hm2 hp hLd hMn
  · -- g = a_m₀, with n = 2 m₀ - 1 ≥ 7: Lemma 2 for L_n
    have hm₀ : 1 ≤ m₀ := pos_inr hg
    have h1 : m₀ ≠ 1 := fun h => hgs (by simp [special, h])
    have h2 : m₀ ≠ 2 := fun h => hgs (by simp [special, h])
    have h3 : m₀ ≠ 3 := fun h => hgs (by simp [special, h])
    obtain ⟨p, ⟨hp, hord⟩, hLz⟩ := hL.2 (2 * m₀ - 1) ⟨m₀ - 1, by omega⟩ (by omega)
    have := Fact.mk hp
    have hn : 0 < 2 * m₀ - 1 := by omega
    have hp9 := prime_ge_of_orderOf hn hord
    have hLn : p ∣ Ln (2 * m₀ - 1) := dvd_Ln_of_dvd_L (by omega) hLz
    refine ⟨p, hp, mod_four_eq_one_of_orderOf hn hord, ?_, ?_⟩
    · simp only [gen]
      rw [sq_add_one_eq_two_mul_Ln m₀ hm₀]
      exact dvd_mul_of_dvd_right hLn 2
    intro x hx hxg hdvd
    by_cases hxs : x ∈ special
    · exact not_dvd_special hp (by omega) hxs hdvd
    have hkey := hmax x hx hxs
    rcases x with k | m
    · obtain ⟨-, hle⟩ := inl_dvd hn hord (pos_inl hx) hdvd
      simp only [key] at hkey
      omega
    · obtain ⟨-, -, hle⟩ := inr_dvd hn hord (pos_inr hx) hdvd
      simp only [key] at hkey
      have := pos_inr hx
      exact hxg (by rw [show m = m₀ by omega])

/-- **Core of Theorem A** (from Bang's theorem and Lemma 2): in an integer relation among
generators of index `≥ 1`, only the four special generators can have a non-zero
coefficient. A non-special generator of largest `key` would have a private prime. -/
theorem coeff_eq_zero_of_not_special (hB : BangTheorem) (hL : Lemma2) (s : Finset Gen)
    (hs : ∀ x ∈ s, x ≠ .inl 0 ∧ x ≠ .inr 0) (c : Gen → ℤ) (q : ℚ)
    (h : ∑ x ∈ s, (c x : ℝ) * arctan (1 / gen x) = q * π) :
    ∀ x ∈ s, x ∉ special → c x = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  set s' := s.filter (fun x => c x ≠ 0) with hs'def
  set T := s'.filter (fun x => x ∉ special) with hTdef
  have hT : T.Nonempty := by
    obtain ⟨x, hx, hxs, hcx⟩ := hcon
    exact ⟨x, by simp [hTdef, hs'def, hx, hxs, hcx]⟩
  obtain ⟨g, hgT, hgmax⟩ := Finset.exists_max_image T key hT
  have hgs' : g ∈ s' := (Finset.mem_filter.1 hgT).1
  have hgspec : g ∉ special := (Finset.mem_filter.1 hgT).2
  have hcg : c g ≠ 0 := (Finset.mem_filter.1 hgs').2
  have hmax : ∀ x ∈ s', x ∉ special → key x ≤ key g :=
    fun x hx hxs => hgmax x (Finset.mem_filter.2 ⟨hx, hxs⟩)
  have hs'0 : ∀ x ∈ s', x ≠ .inl 0 ∧ x ≠ .inr 0 := fun x hx => hs x (Finset.mem_filter.1 hx).1
  have h' : ∑ x ∈ s', (c x : ℝ) * arctan (1 / gen x) = q * π := by
    rw [hs'def, Finset.sum_filter_of_ne (p := fun x => c x ≠ 0)
      (fun x _ hx hc => hx (by simp [hc]))]
    exact h
  obtain ⟨p, hp, hp4, hpg, hpriv⟩ := exists_private_prime hB hL s' hs'0 g hgs' hgspec hmax
  exact hcg (coeff_eq_zero_of_private_prime (fun x hx => gen_pos (hs'0 x hx)) h' hp hp4 hgs'
    hpg hpriv)

/-- `arctan (1/2) / π` is irrational: the private prime `5` divides `2² + 1`. -/
theorem int_mul_arctan_half_eq_zero (K : ℤ) (q : ℚ) (h : (K : ℝ) * arctan (1 / 2) = q * π) :
    K = 0 := by
  have h' : ∑ x ∈ ({()} : Finset Unit), ((fun _ => K) x : ℝ) * arctan (1 / ((fun _ => 2) x : ℕ))
      = q * π := by simpa using h
  exact coeff_eq_zero_of_private_prime (s := {()}) (f := fun _ => 2) (c := fun _ => K)
    (by simp) h' (p := 5) (by norm_num) (by norm_num) (Finset.mem_singleton_self ())
    (by norm_num) (by simp)

/-- **The last step.** A relation among `arctan 1, arctan (1/2), arctan (1/3), arctan (1/7)`
is a combination of R1, R2, R3. -/
theorem four_generators (c₁ c₂ c₃ c₇ : ℤ) (q : ℚ)
    (h : (c₁ : ℝ) * arctan 1 + c₂ * arctan (1 / 2) + c₃ * arctan (1 / 3) + c₇ * arctan (1 / 7)
      = q * π) :
    c₂ - c₃ + 2 * c₇ = 0 ∧ q = (c₁ + c₃ - c₇) / 4 := by
  have key : ((c₂ - c₃ + 2 * c₇ : ℤ) : ℝ) * arctan (1 / 2) =
      ((q - (c₁ + c₃ - c₇) / 4 : ℚ) : ℝ) * π := by
    push_cast
    linear_combination h - (c₁ : ℝ) * R1 - (c₃ : ℝ) * R2 + (c₇ : ℝ) * R3
  have hK := int_mul_arctan_half_eq_zero _ _ key
  refine ⟨hK, ?_⟩
  rw [hK] at key
  have hq : ((q - (c₁ + c₃ - c₇) / 4 : ℚ) : ℝ) = 0 := by
    have := Real.pi_pos
    push_cast at key ⊢
    nlinarith [key]
  have : q - (c₁ + c₃ - c₇) / 4 = 0 := by exact_mod_cast hq
  linarith

/-- **Theorem A from Bang's theorem and Lemma 2** (the statement `Goal` of `PiFormula.lean`):
clear the denominators of the coefficients, move from `value b a` to a sum over `Gen`,
apply `coeff_eq_zero_of_not_special`, then `four_generators`. -/
theorem goal : Goal := by
  intro hB hL b a q hb0 ha0 hval
  classical
  set coeff : Gen → ℚ := Sum.elim (fun m => b m) (fun m => a m) with hcoeff
  set s : Finset Gen := b.support.disjSum a.support with hsdef
  -- the relation as a sum over generators
  have hval' : ∑ x ∈ s, (coeff x : ℝ) * arctan (1 / gen x) = q * π := by
    rw [← hval]
    unfold value
    rw [hsdef, Finset.sum_disjSum]
    congr 1
    · rw [Finsupp.sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp [hcoeff, gen]
    · rw [Finsupp.sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      simp [hcoeff, gen, Nat.cast_sub h1]
  have hzero : ∀ x, x ∉ s → coeff x = 0 := by
    intro x hx
    rcases x with m | m <;> simpa [hsdef, hcoeff, Finsupp.mem_support_iff] using hx
  have hs0 : ∀ x ∈ s, x ≠ .inl 0 ∧ x ≠ .inr 0 := by
    intro x hx
    constructor <;> rintro rfl <;> simp [hsdef, Finsupp.mem_support_iff, hb0, ha0] at hx
  -- clear denominators
  obtain ⟨D, hD, hden⟩ : ∃ D : ℕ, 0 < D ∧ ∀ x, (coeff x).den ∣ D := by
    refine ⟨∏ x ∈ s, (coeff x).den, Finset.prod_pos fun x _ => (coeff x).den_pos, fun x => ?_⟩
    by_cases hx : x ∈ s
    · exact Finset.dvd_prod_of_mem _ hx
    · rw [hzero x hx]; simp
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  obtain ⟨c, hc⟩ : ∃ c : Gen → ℤ, ∀ x, (c x : ℚ) = D * coeff x := by
    refine ⟨fun x => ((D / (coeff x).den : ℕ) : ℤ) * (coeff x).num, fun x => ?_⟩
    simp only [Int.cast_mul, Int.cast_natCast]
    rw [Nat.cast_div (hden x) (by exact_mod_cast (coeff x).den_ne_zero)]
    conv_rhs => rw [← Rat.num_div_den (coeff x)]
    field_simp
  have hcR : ∀ x, (c x : ℝ) = (D : ℝ) * coeff x := fun x => by exact_mod_cast hc x
  have hrel : ∑ x ∈ s, (c x : ℝ) * arctan (1 / gen x) = ((D * q : ℚ) : ℝ) * π := by
    calc ∑ x ∈ s, (c x : ℝ) * arctan (1 / gen x)
        = ∑ x ∈ s, (D : ℝ) * ((coeff x : ℝ) * arctan (1 / gen x)) :=
          Finset.sum_congr rfl fun x _ => by rw [hcR x]; ring
      _ = (D : ℝ) * (q * π) := by rw [← Finset.mul_sum, hval']
      _ = ((D * q : ℚ) : ℝ) * π := by push_cast; ring
  -- the core: only special generators survive
  have hcore := coeff_eq_zero_of_not_special hB hL s hs0 c (D * q) hrel
  have hcz : ∀ x, x ∉ special → coeff x = 0 := by
    intro x hxs
    by_cases hx : x ∈ s
    · have h2 := hc x
      rw [hcore x hx hxs] at h2
      push_cast at h2
      exact (mul_eq_zero.1 h2.symm).resolve_left hDq
    · exact hzero x hx
  have hc0 : ∀ x, coeff x = 0 → c x = 0 := fun x h0 => by
    have := hc x
    rw [h0, mul_zero] at this
    exact_mod_cast this
  refine ⟨fun m hm => ?_, fun m hm => ?_, ?_⟩
  · have := hcz (.inl m) (by simp [special]; omega)
    simpa [hcoeff] using this
  · have := hcz (.inr m) (by simp [special]; omega)
    simpa [hcoeff] using this
  -- the four special generators
  have hspec : ∑ x ∈ s, (c x : ℝ) * arctan (1 / gen x) =
      ∑ x ∈ special, (c x : ℝ) * arctan (1 / gen x) := by
    calc ∑ x ∈ s, (c x : ℝ) * arctan (1 / gen x)
        = ∑ x ∈ s ∩ special, (c x : ℝ) * arctan (1 / gen x) :=
          (Finset.sum_subset Finset.inter_subset_left fun x hxs hxn => by
            have : x ∉ special := fun h => hxn (Finset.mem_inter.2 ⟨hxs, h⟩)
            simp [hc0 x (hcz x this)]).symm
      _ = ∑ x ∈ special, (c x : ℝ) * arctan (1 / gen x) :=
          Finset.sum_subset Finset.inter_subset_right fun x hxsp hxn => by
            have : x ∉ s := fun h => hxn (Finset.mem_inter.2 ⟨h, hxsp⟩)
            simp [hc0 x (hzero x this)]
  have h4 : (c (.inr 1) : ℝ) * arctan 1 + c (.inl 1) * arctan (1 / 2) +
      c (.inr 2) * arctan (1 / 3) + c (.inr 3) * arctan (1 / 7) = ((D * q : ℚ) : ℝ) * π := by
    rw [← hrel, hspec]
    simp [special, gen]
    ring
  obtain ⟨hK, hq⟩ := four_generators _ _ _ _ _ h4
  have e : ∀ x, (c x : ℚ) = D * coeff x := hc
  have hK' : ((c (.inl 1) - c (.inr 2) + 2 * c (.inr 3) : ℤ) : ℚ) = 0 := by exact_mod_cast hK
  push_cast at hK'
  rw [e, e, e] at hK' hq
  simp only [hcoeff, Sum.elim_inl, Sum.elim_inr] at hK' hq
  refine ⟨?_, ?_⟩
  · have : (D : ℚ) * (b 1 - a 2 + 2 * a 3) = 0 := by linear_combination hK'
    exact (mul_eq_zero.1 this).resolve_left hDq
  · have : (D : ℚ) * (q - (a 1 + a 2 - a 3) / 4) = 0 := by linear_combination hq
    linarith [(mul_eq_zero.1 this).resolve_left hDq]

/-- Theorem A, given Lemma 2 (Bang's theorem is proved, via Tau Ceti). -/
theorem theoremA_of_lemma2 (hL : Lemma2) : TheoremA := goal bang hL

end PiFormula
