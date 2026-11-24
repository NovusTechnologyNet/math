module

public import Pilean.Erdos.OkadaLayerAux

/-!
# The coefficient of `log p`: `ℓ_p = c_p` (`OkadaLayerSum`)

Status: proved, no hypothesis left (`okadaLayerSum`). The hypotheses `Odd q` and `f 0 = 0` of
the statement are not used.

Let `p ∣ q` be a prime, `k = v_p(q)`, and let `u_d` be the indicator function of the multiples
of `d` in `ℤ/q` (`lay_ind`). The weight is

`w = u_p + u_{p^2} + ⋯ + u_{p^k} + u_{p^k}/(p - 1)`   (`lay_w`).

* `w(r) = λ(r, p)` for `1 ≤ r ≤ q` (`lay_w_natCast`), so `c_p = ∑_r f(r) w(r)` (`lay_okadaC`).
* For a prime `l ≠ p` of `q` and `l ∣ r'`: `∑_{r : l r = r'} w(r) = l w(r')`, because
  `p^i ∣ r ↔ p^i ∣ l r` and the equation has `l` solutions (`lay_w_fiber_ne`).
* For `p ∣ r'`: `∑_{r : p r = r'} u_{p^i}(r)` is `p u_{p^(i+1)}(r')` for `i < k`
  (`lay_ind_fiber_mul`) and `u_{p^k}(r')` for `i = k` (`lay_ind_fiber_top`: one solution in
  `p^k ℤ/q`, or none). Summing, `∑_{r : p r = r'} w(r) = p (w(r') - 1)` (`lay_w_fiber_self`).
* `w(r) = 0` when `p ∤ r` (`lay_w_eq_zero`).

`lay_main` (`OkadaLayerAux.lean`) then gives `ℓ_p = ∑_r f(r) w(r)`.
-/

@[expose] public section

open scoped BigOperators

namespace PiFormula

namespace Erdos

namespace Okada

variable {q : ℕ}

/-! ### The indicator functions -/

open Classical in
/-- The indicator function of the multiples of `d` in `ℤ/q`. -/
noncomputable def lay_ind (q d : ℕ) (x : ZMod q) : ℝ := if (d : ZMod q) ∣ x then 1 else 0

theorem lay_ind_of_dvd {d : ℕ} {x : ZMod q} (h : (d : ZMod q) ∣ x) : lay_ind q d x = 1 := by
  unfold lay_ind
  simp only [h, ↓reduceIte]

theorem lay_ind_of_not_dvd {d : ℕ} {x : ZMod q} (h : ¬ (d : ZMod q) ∣ x) :
    lay_ind q d x = 0 := by
  unfold lay_ind
  simp only [h, ↓reduceIte]

theorem lay_ind_congr {d d' : ℕ} {x x' : ZMod q}
    (h : (d : ZMod q) ∣ x ↔ (d' : ZMod q) ∣ x') : lay_ind q d x = lay_ind q d' x' := by
  by_cases hx : (d : ZMod q) ∣ x
  · rw [lay_ind_of_dvd hx, lay_ind_of_dvd (h.1 hx)]
  · rw [lay_ind_of_not_dvd hx, lay_ind_of_not_dvd (mt h.2 hx)]

/-- If `d` is prime to `l ∣ q`, the indicator of the multiples of `d` is harmonic at `l`. -/
theorem lay_ind_fiber_coprime [NeZero q] {l d : ℕ} (hl : l ∣ q) (hd : d.Coprime l)
    {r' : ZMod q} (hr' : (l : ZMod q) ∣ r') :
    ∑ r ∈ Finset.univ.filter (fun r : ZMod q => (l : ZMod q) * r = r'), lay_ind q d r =
      (l : ℝ) * lay_ind q d r' := by
  have h : ∀ r ∈ Finset.univ.filter (fun r : ZMod q => (l : ZMod q) * r = r'),
      lay_ind q d r = lay_ind q d r' := by
    intro r hr
    have hr1 : (l : ZMod q) * r = r' := (Finset.mem_filter.1 hr).2
    refine lay_ind_congr ?_
    rw [← hr1]
    exact ⟨fun h => Dvd.dvd.mul_left h _, lay_dvd_of_coprime_mul hd⟩
  rw [Finset.sum_congr rfl h, Finset.sum_const, lay_card_fiber hl hr', nsmul_eq_mul]

/-- If `a d ∣ q` and `a ∣ r'`, then `∑_{r : a r = r'} u_d(r) = a u_{a d}(r')`. -/
theorem lay_ind_fiber_mul [NeZero q] {a d : ℕ} (ha : 0 < a) (had : a * d ∣ q)
    {r' : ZMod q} (hr' : (a : ZMod q) ∣ r') :
    ∑ r ∈ Finset.univ.filter (fun r : ZMod q => (a : ZMod q) * r = r'), lay_ind q d r =
      (a : ℝ) * lay_ind q (a * d) r' := by
  have h : ∀ r ∈ Finset.univ.filter (fun r : ZMod q => (a : ZMod q) * r = r'),
      lay_ind q d r = lay_ind q (a * d) r' := by
    intro r hr
    have hr1 : (a : ZMod q) * r = r' := (Finset.mem_filter.1 hr).2
    refine lay_ind_congr ?_
    rw [← hr1]
    constructor
    · intro h
      rw [Nat.cast_mul]
      exact mul_dvd_mul_left _ h
    · intro h
      have h' : ((a * d : ℕ) : ZMod q) ∣ ((a * r.val : ℕ) : ZMod q) := by
        rw [Nat.cast_mul a r.val, ZMod.natCast_zmod_val]
        exact h
      have h2 : a * d ∣ a * r.val := (lay_natCast_dvd_iff had _).1 h'
      rw [← ZMod.natCast_zmod_val r]
      exact Nat.cast_dvd_cast (Nat.dvd_of_mul_dvd_mul_left ha h2)
  rw [Finset.sum_congr rfl h, Finset.sum_const,
    lay_card_fiber (Dvd.dvd.trans (dvd_mul_right a d) had) hr', nsmul_eq_mul]

/-- If `q = p^k n` with `p` prime to `n`, then `∑_{r : p r = r'} u_{p^k}(r) = u_{p^k}(r')`:
the equation `p r = r'` has exactly one solution divisible by `p^k` when `p^k ∣ r'`, and none
otherwise. -/
theorem lay_ind_fiber_top [NeZero q] {p k n : ℕ} (hq : q = p ^ k * n) (hpn : p.Coprime n)
    (r' : ZMod q) :
    ∑ r ∈ Finset.univ.filter (fun r : ZMod q => (p : ZMod q) * r = r'),
      lay_ind q (p ^ k) r = lay_ind q (p ^ k) r' := by
  have hc : IsCoprime (p : ℤ) (n : ℤ) := Nat.isCoprime_iff_coprime.2 hpn
  obtain ⟨u, v, huv⟩ := hc
  have h1 : (u : ZMod q) * (p : ZMod q) + (v : ZMod q) * (n : ZMod q) = 1 := by
    have h0 := congrArg (Int.cast : ℤ → ZMod q) huv
    push_cast at h0
    exact h0
  have hz : ((p ^ k : ℕ) : ZMod q) * (n : ZMod q) = 0 := by
    rw [← Nat.cast_mul, ← hq]
    exact ZMod.natCast_self q
  by_cases hr' : ((p ^ k : ℕ) : ZMod q) ∣ r'
  · obtain ⟨s, rfl⟩ := hr'
    have hmem : ((p ^ k : ℕ) : ZMod q) * ((u : ZMod q) * s) ∈ Finset.univ.filter
        (fun r : ZMod q => (p : ZMod q) * r = ((p ^ k : ℕ) : ZMod q) * s) := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      linear_combination (((p ^ k : ℕ) : ZMod q) * s) * h1 - (v : ZMod q) * s * hz
    rw [Finset.sum_eq_single_of_mem _ hmem]
    · rw [lay_ind_of_dvd (dvd_mul_right _ _), lay_ind_of_dvd (dvd_mul_right _ _)]
    · intro r hr hne
      have h2 : (p : ZMod q) * r = ((p ^ k : ℕ) : ZMod q) * s := (Finset.mem_filter.1 hr).2
      apply lay_ind_of_not_dvd
      rintro ⟨t, rfl⟩
      apply hne
      linear_combination (-(((p ^ k : ℕ) : ZMod q) * t)) * h1 + (u : ZMod q) * h2 +
        (v : ZMod q) * t * hz
  · rw [lay_ind_of_not_dvd hr']
    refine Finset.sum_eq_zero fun r hr => ?_
    have h2 : (p : ZMod q) * r = r' := (Finset.mem_filter.1 hr).2
    apply lay_ind_of_not_dvd
    intro hdiv
    apply hr'
    rw [← h2]
    exact Dvd.dvd.mul_left hdiv _

/-! ### The weight -/

/-- The weight with a parameter `k`: `u_p + ⋯ + u_{p^k} + u_{p^k}/(p - 1)`. -/
noncomputable def lay_wk (q p k : ℕ) (x : ZMod q) : ℝ :=
  ∑ j ∈ Finset.range k, lay_ind q (p ^ (j + 1)) x + 1 / ((p : ℝ) - 1) * lay_ind q (p ^ k) x

/-- The weight: `lay_wk` with `k = v_p(q)`. On the class of `1 ≤ r ≤ q` it is `λ(r, p)`. -/
noncomputable def lay_w (q p : ℕ) (x : ZMod q) : ℝ := lay_wk q p (padicValNat p q) x

theorem lay_wk_fiber_coprime [NeZero q] {l p : ℕ} (k : ℕ) (hl : l ∣ q) (hpl : p.Coprime l)
    {r' : ZMod q} (hr' : (l : ZMod q) ∣ r') :
    ∑ r ∈ Finset.univ.filter (fun r : ZMod q => (l : ZMod q) * r = r'), lay_wk q p k r =
      (l : ℝ) * lay_wk q p k r' := by
  have hcop : ∀ i : ℕ, (p ^ i).Coprime l := fun i => Nat.Coprime.pow_left i hpl
  unfold lay_wk
  rw [Finset.sum_add_distrib, Finset.sum_comm, ← Finset.mul_sum,
    lay_ind_fiber_coprime hl (hcop k) hr',
    Finset.sum_congr rfl (fun j _ => lay_ind_fiber_coprime hl (hcop (j + 1)) hr'),
    ← Finset.mul_sum]
  ring

theorem lay_wk_fiber_self [NeZero q] {p k n : ℕ} (hp : 1 < p) (hq : q = p ^ (k + 1) * n)
    (hpn : p.Coprime n) {r' : ZMod q} (hr' : (p : ZMod q) ∣ r') :
    ∑ r ∈ Finset.univ.filter (fun r : ZMod q => (p : ZMod q) * r = r'),
      lay_wk q p (k + 1) r = (p : ℝ) * (lay_wk q p (k + 1) r' - 1) := by
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have h : (1 : ℝ) < p := by exact_mod_cast hp
    exact sub_ne_zero.2 (ne_of_gt h)
  have hlow : ∀ j ∈ Finset.range k,
      ∑ r ∈ Finset.univ.filter (fun r : ZMod q => (p : ZMod q) * r = r'),
        lay_ind q (p ^ (j + 1)) r = (p : ℝ) * lay_ind q (p ^ (j + 1 + 1)) r' := by
    intro j hj
    have hjk : j + 1 + 1 ≤ k + 1 := by
      have := Finset.mem_range.1 hj
      omega
    have hdvd : p * p ^ (j + 1) ∣ q := by
      rw [← pow_succ', hq]
      exact Dvd.dvd.mul_right (pow_dvd_pow p hjk) n
    rw [lay_ind_fiber_mul (by omega) hdvd hr', ← pow_succ']
  have htop := lay_ind_fiber_top hq hpn r'
  have hone : lay_ind q (p ^ (0 + 1)) r' = 1 := by
    apply lay_ind_of_dvd
    rw [zero_add, pow_one]
    exact hr'
  unfold lay_wk
  rw [Finset.sum_add_distrib, Finset.sum_comm, ← Finset.mul_sum, htop, Finset.sum_range_succ,
    htop, Finset.sum_congr rfl hlow, ← Finset.mul_sum, Finset.sum_range_succ' _ k, hone]
  field_simp
  ring

theorem lay_wk_eq_zero {p k : ℕ} (hk : k ≠ 0) {r : ZMod q} (h : ¬ (p : ZMod q) ∣ r) :
    lay_wk q p k r = 0 := by
  have hnd : ∀ i : ℕ, i ≠ 0 → lay_ind q (p ^ i) r = 0 := by
    intro i hi
    apply lay_ind_of_not_dvd
    intro hdiv
    exact h (Dvd.dvd.trans (Nat.cast_dvd_cast (dvd_pow_self p hi)) hdiv)
  unfold lay_wk
  rw [hnd k hk, Finset.sum_eq_zero (fun j _ => hnd (j + 1) (Nat.succ_ne_zero j))]
  ring

/-! ### The weight for `k = v_p(q)` -/

theorem lay_pow_dvd_iff {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : n ≠ 0) (i : ℕ) :
    p ^ i ∣ n ↔ i ≤ padicValNat p n := by
  rw [Nat.padicValNat_def (n := n)]
  exact Nat.pow_dvd_iff_le_multiplicity hp.ne_one hn

/-- The weight is harmonic at every prime `l ≠ p` of `q`. -/
theorem lay_w_fiber_ne [NeZero q] {p l : ℕ} (hp : p.Prime) (hl : l.Prime) (hlq : l ∣ q)
    (hne : l ≠ p) {r' : ZMod q} (hr' : (l : ZMod q) ∣ r') :
    ∑ r ∈ Finset.univ.filter (fun r : ZMod q => (l : ZMod q) * r = r'), lay_w q p r =
      (l : ℝ) * lay_w q p r' :=
  lay_wk_fiber_coprime _ hlq ((Nat.coprime_primes hp hl).2 (Ne.symm hne)) hr'

/-- At the prime `p` itself: `∑_{r : p r = r'} w(r) = p (w(r') - 1)` for `p ∣ r'`. -/
theorem lay_w_fiber_self [NeZero q] {p : ℕ} (hp : p.Prime) (hpq : p ∣ q) {r' : ZMod q}
    (hr' : (p : ZMod q) ∣ r') :
    ∑ r ∈ Finset.univ.filter (fun r : ZMod q => (p : ZMod q) * r = r'), lay_w q p r =
      (p : ℝ) * (lay_w q p r' - 1) := by
  have hq0 : q ≠ 0 := NeZero.ne q
  have hk1 : 1 ≤ padicValNat p q := (lay_pow_dvd_iff hp hq0 1).1 (by rw [pow_one]; exact hpq)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, padicValNat p q = k + 1 := ⟨padicValNat p q - 1, by omega⟩
  have h1 : p ^ (k + 1) ∣ q := by
    rw [← hk]
    exact (lay_pow_dvd_iff hp hq0 _).2 le_rfl
  have h2 : ¬ p ^ (k + 1 + 1) ∣ q := by
    rw [lay_pow_dvd_iff hp hq0, hk]
    omega
  obtain ⟨n, hn⟩ := h1
  have hpn : p.Coprime n := by
    rw [hp.coprime_iff_not_dvd]
    rintro ⟨n', rfl⟩
    exact h2 ⟨n', by rw [hn]; ring⟩
  unfold lay_w
  rw [hk]
  exact lay_wk_fiber_self hp.one_lt hn hpn hr'

/-- The weight vanishes off the multiples of `p`. -/
theorem lay_w_eq_zero [NeZero q] {p : ℕ} (hp : p.Prime) (hpq : p ∣ q) {r : ZMod q}
    (h : ¬ (p : ZMod q) ∣ r) : lay_w q p r = 0 := by
  have hk1 : 1 ≤ padicValNat p q :=
    (lay_pow_dvd_iff hp (NeZero.ne q) 1).1 (by rw [pow_one]; exact hpq)
  exact lay_wk_eq_zero (by omega) h

/-- On the class of `r ≥ 1` the weight is `λ(r, p)`. -/
theorem lay_w_natCast [NeZero q] {p : ℕ} (hp : p.Prime) {r : ℕ} (hr : r ≠ 0) :
    lay_w q p (r : ZMod q) = ((lam q r p : ℚ) : ℝ) := by
  have hq0 : q ≠ 0 := NeZero.ne q
  have hdvd : ∀ i : ℕ, i ≤ padicValNat p q →
      (((p ^ i : ℕ) : ZMod q) ∣ (r : ZMod q) ↔ i ≤ padicValNat p r) := by
    intro i hi
    rw [lay_natCast_dvd_iff ((pow_dvd_pow p hi).trans ((lay_pow_dvd_iff hp hq0 _).2 le_rfl)),
      lay_pow_dvd_iff hp hr]
  have hind : ∀ i : ℕ, i ≤ padicValNat p q →
      lay_ind q (p ^ i) (r : ZMod q) = if i ≤ padicValNat p r then 1 else 0 := by
    intro i hi
    by_cases h : i ≤ padicValNat p r
    · rw [lay_ind_of_dvd ((hdvd i hi).2 h)]
      simp only [h, ↓reduceIte]
    · rw [lay_ind_of_not_dvd (mt (hdvd i hi).1 h)]
      simp only [h, ↓reduceIte]
  have hsum : ∑ j ∈ Finset.range (padicValNat p q), lay_ind q (p ^ (j + 1)) (r : ZMod q) =
      ((min (padicValNat p q) (padicValNat p r) : ℕ) : ℝ) := by
    have h1 : ∀ j ∈ Finset.range (padicValNat p q), lay_ind q (p ^ (j + 1)) (r : ZMod q) =
        if j + 1 ≤ padicValNat p r then 1 else 0 := fun j hj =>
      hind (j + 1) (Nat.succ_le_of_lt (Finset.mem_range.1 hj))
    have h2 : (Finset.range (padicValNat p q)).filter (fun j => j + 1 ≤ padicValNat p r) =
        Finset.range (min (padicValNat p q) (padicValNat p r)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [Finset.sum_congr rfl h1, Finset.sum_boole, h2, Finset.card_range]
  unfold lay_w lay_wk
  rw [hsum, hind _ le_rfl]
  by_cases hlt : padicValNat p r < padicValNat p q
  · have hmin : min (padicValNat p q) (padicValNat p r) = padicValNat p r := by omega
    have hnle : ¬ padicValNat p q ≤ padicValNat p r := by omega
    simp only [lam, hlt, hnle, hmin, ↓reduceIte, mul_zero, add_zero, Rat.cast_natCast]
  · have hmin : min (padicValNat p q) (padicValNat p r) = padicValNat p q := by omega
    have hle : padicValNat p q ≤ padicValNat p r := by omega
    simp only [lam, hlt, hle, hmin, ↓reduceIte, mul_one]
    push_cast
    ring

/-- `c_p = ∑_r f(r) w(r)`. -/
theorem lay_okadaC [NeZero q] (f : ZMod q → ℚ) {p : ℕ} (hp : p.Prime) :
    ((okadaC q f p : ℚ) : ℝ) = ∑ x : ZMod q, (f x : ℝ) * lay_w q p x := by
  rw [← lay_sum_Icc (fun x : ZMod q => (f x : ℝ) * lay_w q p x)]
  unfold okadaC
  rw [Rat.cast_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr0 : r ≠ 0 := by
    rw [Finset.mem_Icc] at hr
    omega
  rw [Rat.cast_mul, lay_w_natCast hp hr0]

end Okada

/-- **The coefficient of `log p`.** For a prime `p ∣ q`, the sum of `g = okadaG q f` over the
residues divisible by `p` and by no other prime factor of `q` is `c_p`. -/
theorem okadaLayerSum : OkadaLayerSum := by
  intro q _ _ f _ p hp hpq
  rw [Okada.lay_okadaC f hp]
  exact Okada.lay_main f hp hpq (Okada.lay_w q p)
    (fun l hl hlq hne r' hr' => Okada.lay_w_fiber_ne hp hl hlq hne hr')
    (fun r' hr' => Okada.lay_w_fiber_self hp hpq hr')
    (fun r hr => Okada.lay_w_eq_zero hp hpq hr)

end Erdos

end PiFormula
