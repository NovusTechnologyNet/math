import Pilean.Erdos.OkadaWindow
import Pilean.Erdos.OkadaGlueWindow
import Pilean.Erdos.ArithSeries
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Okada's criterion: reduction to the units

`okadaUnitReduction : OkadaUnitReduction`: for `f` on `ℤ/q`, with `g = okadaG q f`,

  `S_N(f) - S'_N(g) → -(1/q) ∑_{p ∣ q} ℓ_p log p`   as `N → ∞`,

where `S_N(f) = ∑_{n < N} f(n)/n`, `S'_N(g) = ∑_{n < N, gcd(n, q) = 1} g(n)/n` and `ℓ_p` is the
sum of `g(r)` over the residues `r` divisible by `p` and by no other prime factor of `q`
(`Okada.layerSum`). Status: proved, no hypothesis left (the hypotheses `Odd q` and `f 0 = 0` of
the statement are not used, except that `okadaWindow` is stated for odd `q`).

Proof. For a finite set `m` of primes dividing `q` put `h_m = Arith.serH q f m`,
`A_m = {r : no prime of m divides r}` and `R_m(N) = ∑_{n < N, n ∈ A_m} h_m(n)/n` (`red_R`).
Then `R_∅ = S_N(f)` and `R_P = S'_N(g)` for `P` the set of all primes dividing `q`.

1. One prime `p ∉ m` (`red_step`). With `M = m ∪ {p}` and `v(r) = h_M(r)` for `r ∈ A_m`
   divisible by `p`, `v(r) = 0` otherwise (`red_v`): `h_m(r) = h_M(r) - h_M(p r)/p`
   (`Arith.serH_insert`) gives `[r ∈ A_m] h_m(r) - [r ∈ A_M] h_M(r) = v(r) - v(p r)/p`
   (`red_u_sub`), so `R_m(N) - R_M(N) = -∑_{N ≤ n < pN} v(n)/n` (`red_sum_shift`), which tends
   to `-(log p / q) ∑_r v(r)` by `okadaWindow`. The number `∑_r v(r)` is `red_kappa q f M p`.
2. `red_kappa q f M p` does not change when a further prime `p'` is inserted in `M`
   (`red_kappa_insert`): multiplication by `p'` is `p'`-to-one onto the multiples of `p'`
   (`red_card_fiber`), and the set of the `r` in question is stable under it
   (`red_sum_serH_insert`). For `M = P` it is `ℓ_p` (`red_kappa_primeFactors`).
3. Telescoping over the primes of `q` (`red_tendsto_sub`).
-/

open scoped BigOperators

open Filter Finset

namespace PiFormula

namespace Erdos

namespace Okada

open Arith

variable {q : ℕ}

/-! ## 1. Divisibility in `ℤ/q` by a divisor of `q` -/

/-- If `l ∣ q` and `l` divides `n` in `ℤ/q`, then `l` divides `n`. -/
theorem red_dvd_of_cast_dvd {l n : ℕ} (hl : l ∣ q) (h : (l : ZMod q) ∣ (n : ZMod q)) :
    l ∣ n := by
  obtain ⟨c, hc⟩ := h
  have h1 := congrArg (ZMod.castHom hl (ZMod l)) hc
  rw [map_mul, map_natCast, map_natCast, ZMod.natCast_self, zero_mul] at h1
  exact (ZMod.natCast_eq_zero_iff n l).1 h1

/-- `n` is prime to `q` exactly when no prime factor of `q` divides `n` in `ℤ/q`. -/
theorem red_coprime_iff [NeZero q] (n : ℕ) :
    n.Coprime q ↔ ∀ l ∈ q.primeFactors, ¬ (l : ZMod q) ∣ (n : ZMod q) := by
  constructor
  · intro h l hl hdvd
    have hl' := Nat.mem_primeFactors.1 hl
    have h1 : l ∣ n := red_dvd_of_cast_dvd hl'.2.1 hdvd
    exact Nat.Prime.not_coprime_iff_dvd.2 ⟨l, hl'.1, h1, hl'.2.1⟩ h
  · intro h
    by_contra hcop
    obtain ⟨p, hp, hp1, hp2⟩ := Nat.Prime.not_coprime_iff_dvd.1 hcop
    exact h p (Nat.mem_primeFactors.2 ⟨hp, hp2, NeZero.ne q⟩) (Nat.cast_dvd_cast hp1)

/-- For `p ∣ q`, multiplication by `p` on `ℤ/q` is `p`-to-one onto the multiples of `p`. -/
theorem red_card_fiber [NeZero q] {p : ℕ} (hpq : p ∣ q) {r' : ZMod q}
    (hr' : (p : ZMod q) ∣ r') :
    (univ.filter (fun r : ZMod q => (p : ZMod q) * r = r')).card = p := by
  obtain ⟨r₀, rfl⟩ := hr'
  have hker : (univ.filter (fun t : ZMod q => (p : ZMod q) * t = 0)).card = p := by
    have h := IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod q) p
    rw [Nat.card_eq_fintype_card (α := ZMod q), ZMod.card, Nat.gcd_eq_right hpq] at h
    refine Eq.trans (Eq.symm ?_) h
    refine Nat.subtype_card _ fun t => ?_
    simp only [mem_filter, mem_univ, true_and, AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply,
      nsmul_eq_mul]
  refine Eq.trans ?_ hker
  refine Finset.card_bij (fun r _ => r - r₀) ?_ ?_ ?_
  · intro r hr
    simp only [mem_filter, mem_univ, true_and] at hr ⊢
    rw [mul_sub, hr, sub_self]
  · intro a _ b _ h
    exact sub_left_injective h
  · intro t ht
    simp only [mem_filter, mem_univ, true_and] at ht
    refine ⟨t + r₀, ?_, add_sub_cancel_right t r₀⟩
    simp only [mem_filter, mem_univ, true_and]
    rw [mul_add, ht, zero_add]

/-- `h_P = g` for `P` the set of the prime factors of `q`. -/
theorem red_serH_primeFactors (f : ZMod q → ℚ) (r : ZMod q) :
    serH q f q.primeFactors r = okadaG q f r := by
  unfold serH okadaG
  refine tsum_congr fun j => ?_
  have hiff : j ∈ Nat.factoredNumbers q.primeFactors ↔ InM q j :=
    Nat.mem_factoredNumbers_iff_primeFactors_subset
  by_cases h : InM q j
  · simp only [h, hiff.2 h, ↓reduceIte]
  · simp only [h, mt hiff.1 h, ↓reduceIte]

/-! ## 2. The sums `R_m(N)` -/

open Classical in
/-- `h_m(r)` if no prime of `m` divides `r`, and `0` otherwise. -/
noncomputable def red_u (q : ℕ) (f : ZMod q → ℚ) (m : Finset ℕ) (r : ZMod q) : ℝ :=
  if ∀ l ∈ m, ¬ (l : ZMod q) ∣ r then serH q f m r else 0

/-- `R_m(N)`: the sum of `h_m(n)/n` over the `n < N` divisible by no prime of `m`. -/
noncomputable def red_R (q : ℕ) (f : ZMod q → ℚ) (m : Finset ℕ) (N : ℕ) : ℝ :=
  ∑ n ∈ range N, red_u q f m (n : ZMod q) / (n : ℝ)

open Classical in
/-- `h_M(r)` if `p` divides `r` and no other prime of `M` does, and `0` otherwise. -/
noncomputable def red_v (q : ℕ) (f : ZMod q → ℚ) (M : Finset ℕ) (p : ℕ) (r : ZMod q) : ℝ :=
  if (p : ZMod q) ∣ r ∧ ∀ l ∈ M, l ≠ p → ¬ (l : ZMod q) ∣ r then serH q f M r else 0

/-- The sum of `h_M(r)` over the `r` divisible by `p` and by no other prime of `M`. -/
noncomputable def red_kappa (q : ℕ) [NeZero q] (f : ZMod q → ℚ) (M : Finset ℕ) (p : ℕ) : ℝ :=
  ∑ r : ZMod q, red_v q f M p r

theorem red_R_empty (f : ZMod q → ℚ) (N : ℕ) : red_R q f ∅ N = partialSum q f N := by
  unfold red_R partialSum red_u
  refine Finset.sum_congr rfl fun n _ => ?_
  simp [serH_empty]

theorem red_R_primeFactors [NeZero q] (f : ZMod q → ℚ) (N : ℕ) :
    red_R q f q.primeFactors N = unitSum q (okadaG q f) N := by
  unfold red_R unitSum red_u
  refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs with h1 h2 h2
  · rw [red_serH_primeFactors]
  · exact absurd ((red_coprime_iff n).2 h1) h2
  · exact absurd ((red_coprime_iff n).1 h2) h1
  · exact zero_div _

open Classical in
theorem red_kappa_eq [NeZero q] (f : ZMod q → ℚ) (M : Finset ℕ) (p : ℕ) :
    red_kappa q f M p = ∑ r ∈ univ.filter (fun r : ZMod q =>
      (p : ZMod q) ∣ r ∧ ∀ l ∈ M, l ≠ p → ¬ (l : ZMod q) ∣ r), serH q f M r := by
  unfold red_kappa red_v
  rw [Finset.sum_filter]

/-- For `M` the set of the prime factors of `q`, the number `red_kappa` is the layer sum. -/
theorem red_kappa_primeFactors [NeZero q] (f : ZMod q → ℚ) (p : ℕ) :
    red_kappa q f q.primeFactors p = layerSum q f p := by
  classical
  rw [red_kappa_eq]
  unfold layerSum layer
  refine Finset.sum_congr ?_ fun r _ => red_serH_primeFactors f r
  ext r
  simp only [mem_filter, mem_univ, true_and]

/-! ## 3. One prime -/

/-- For a prime `p ∉ m`, a residue `p r` is divisible by a prime of `m` exactly when `r` is. -/
theorem red_A_mul_iff {m : Finset ℕ} {p : ℕ} (hp : p.Prime) (hpm : p ∉ m)
    (hm : ∀ l ∈ m, l.Prime) (r : ZMod q) :
    (∀ l ∈ m, ¬ (l : ZMod q) ∣ (p : ZMod q) * r) ↔ ∀ l ∈ m, ¬ (l : ZMod q) ∣ r := by
  constructor
  · intro h l hl hd
    exact h l hl (Dvd.dvd.mul_left hd _)
  · intro h l hl hd
    exact h l hl (dvd_of_dvd_prime_mul (hm l hl) hp (ne_of_mem_of_not_mem hl hpm) hd)

/-- `[r ∈ A_m] h_m(r) - [r ∈ A_M] h_M(r) = v(r) - v(p r)/p` for `M = m ∪ {p}`. -/
theorem red_u_sub [NeZero q] (f : ZMod q → ℚ) {m : Finset ℕ} {p : ℕ} (hp : p.Prime)
    (hpm : p ∉ m) (hm : ∀ l ∈ m, l.Prime) (r : ZMod q) :
    red_u q f m r - red_u q f (insert p m) r =
      red_v q f (insert p m) p r - red_v q f (insert p m) p ((p : ZMod q) * r) / p := by
  classical
  have hI : ∀ x : ZMod q, (∀ l ∈ insert p m, l ≠ p → ¬ (l : ZMod q) ∣ x) ↔
      ∀ l ∈ m, ¬ (l : ZMod q) ∣ x := by
    intro x
    constructor
    · intro h l hl
      exact h l (mem_insert_of_mem hl) (ne_of_mem_of_not_mem hl hpm)
    · intro h l hl hne
      rcases mem_insert.1 hl with e | e
      · exact absurd e hne
      · exact h l e
  have hJ : ∀ x : ZMod q, (∀ l ∈ insert p m, ¬ (l : ZMod q) ∣ x) ↔
      (¬ (p : ZMod q) ∣ x ∧ ∀ l ∈ m, ¬ (l : ZMod q) ∣ x) := by
    intro x
    simp only [mem_insert, forall_eq_or_imp]
  have hS := serH_insert f hp hpm r
  unfold red_u red_v
  simp only [hI, hJ, red_A_mul_iff hp hpm hm, dvd_mul_right, true_and]
  rw [← hS]
  by_cases hA : ∀ l ∈ m, ¬ (l : ZMod q) ∣ r
  · have hA' : (∀ l ∈ m, ¬ (l : ZMod q) ∣ r) = True := eq_true hA
    by_cases hd : (p : ZMod q) ∣ r
    · simp only [hA', hd, not_true_eq_false, and_self, false_and, ↓reduceIte]
      ring
    · simp only [hA', hd, not_false_eq_true, and_self, false_and, ↓reduceIte]
      ring
  · have hA' : (∀ l ∈ m, ¬ (l : ZMod q) ∣ r) = False := eq_false hA
    simp only [hA', and_false, ↓reduceIte]
    ring

/-- A sum over `n < pN` of a function supported on the multiples of `p`. -/
theorem red_sum_range_mul (G : ℕ → ℝ) {p : ℕ} (hp : 0 < p) (hG : ∀ n, ¬ p ∣ n → G n = 0)
    (N : ℕ) : ∑ n ∈ range (p * N), G n = ∑ n ∈ range N, G (p * n) := by
  have hinj : ∀ a ∈ range N, ∀ b ∈ range N, p * a = p * b → a = b :=
    fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp h
  rw [← Finset.sum_image (s := range N) (g := fun n => p * n) (f := G) hinj]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro x hx
    obtain ⟨n, hn, rfl⟩ := mem_image.1 hx
    exact mem_range.2 (Nat.mul_lt_mul_of_pos_left (mem_range.1 hn) hp)
  · intro x hx hx'
    by_contra h
    have hpx : p ∣ x := by
      by_contra h'
      exact h (hG x h')
    obtain ⟨n, rfl⟩ := hpx
    exact hx' (mem_image.2 ⟨n, mem_range.2 (lt_of_mul_lt_mul_left (mem_range.1 hx)
      (Nat.zero_le p)), rfl⟩)

/-- If `v` vanishes off the multiples of `p`, the sum of `(v(n) - v(p n)/p)/n` over `n < N` is
minus the sum of `v(n)/n` over `N ≤ n < pN`. -/
theorem red_sum_shift {p : ℕ} (hp : 0 < p) (hpq : p ∣ q) (v : ZMod q → ℝ)
    (hv : ∀ r : ZMod q, ¬ (p : ZMod q) ∣ r → v r = 0) (N : ℕ) :
    ∑ n ∈ range N, (v (n : ZMod q) - v ((p : ZMod q) * (n : ZMod q)) / p) / (n : ℝ) =
      -∑ n ∈ Ico N (p * N), v (n : ZMod q) / (n : ℝ) := by
  have h1 : ∑ n ∈ range (p * N), v (n : ZMod q) / (n : ℝ) =
      ∑ n ∈ range N, v ((p * n : ℕ) : ZMod q) / ((p * n : ℕ) : ℝ) :=
    red_sum_range_mul (fun n => v (n : ZMod q) / (n : ℝ)) hp
      (fun n hn => by rw [hv _ (fun h => hn (red_dvd_of_cast_dvd hpq h)), zero_div]) N
  rw [Finset.sum_Ico_eq_sub _ (Nat.le_mul_of_pos_left N hp), h1, neg_sub,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  push_cast
  rw [sub_div, div_div]

/-- The sum of `v(n)/n` over `N ≤ n < pN` tends to `(log p / q) ∑_r v(r)`. -/
theorem red_tendsto_window [NeZero q] (hq : Odd q) {p : ℕ} (hp : 0 < p) (v : ZMod q → ℝ) :
    Tendsto (fun N : ℕ => ∑ n ∈ Ico N (p * N), v (n : ZMod q) / (n : ℝ)) atTop
      (nhds ((∑ r : ZMod q, v r) * Real.log (p : ℝ) / (q : ℝ))) := by
  have h : ∀ N : ℕ, ∑ r : ZMod q, v r *
      (∑ n ∈ Ico N (p * N), if (n : ZMod q) = r then 1 / (n : ℝ) else 0) =
      ∑ n ∈ Ico N (p * N), v (n : ZMod q) / (n : ℝ) :=
    fun N => (sum_Ico_eq_sum_window q v N (p * N)).symm
  rw [mul_div_assoc, Finset.sum_mul]
  refine Tendsto.congr h ?_
  exact tendsto_finsetSum _ fun r _ => (okadaWindow q hq p hp r).const_mul _

/-- **One prime.** `R_m(N) - R_M(N) → -(log p / q) κ(M, p)` for `M = m ∪ {p}`. -/
theorem red_step [NeZero q] (hq : Odd q) (f : ZMod q → ℚ) {m : Finset ℕ} {p : ℕ}
    (hp : p.Prime) (hpq : p ∣ q) (hpm : p ∉ m) (hm : ∀ l ∈ m, l.Prime) :
    Tendsto (fun N : ℕ => red_R q f m N - red_R q f (insert p m) N) atTop
      (nhds (-(red_kappa q f (insert p m) p * Real.log (p : ℝ) / (q : ℝ)))) := by
  have hv : ∀ r : ZMod q, ¬ (p : ZMod q) ∣ r → red_v q f (insert p m) p r = 0 := by
    intro r hr
    simp only [red_v, hr, false_and, ↓reduceIte]
  have h : ∀ N : ℕ, -∑ n ∈ Ico N (p * N), red_v q f (insert p m) p (n : ZMod q) / (n : ℝ) =
      red_R q f m N - red_R q f (insert p m) N := by
    intro N
    rw [← red_sum_shift hp.pos hpq (red_v q f (insert p m) p) hv N]
    unfold red_R
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← sub_div, red_u_sub f hp hpm hm]
  refine Tendsto.congr h ?_
  exact (red_tendsto_window hq hp.pos _).neg

/-! ## 4. The coefficient of `log p` does not depend on the other primes -/

open Classical in
/-- If the set `B` of residues is stable under multiplication by the prime `p ∣ q` in both
directions, the sum of `h_M` over `B` is the sum of `h_{M ∪ p}` over the `r ∈ B` not divisible
by `p`. -/
theorem red_sum_serH_insert [NeZero q] (f : ZMod q → ℚ) {M : Finset ℕ} {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ q) (hpM : p ∉ M) (B : Finset (ZMod q))
    (hB : ∀ r : ZMod q, (p : ZMod q) * r ∈ B ↔ r ∈ B) :
    ∑ r ∈ B.filter (fun r => ¬ (p : ZMod q) ∣ r), serH q f (insert p M) r =
      ∑ r ∈ B, serH q f M r := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hmaps : ∀ r ∈ B, (p : ZMod q) * r ∈ B.filter (fun r' => (p : ZMod q) ∣ r') := by
    intro r hr
    exact mem_filter.2 ⟨(hB r).2 hr, dvd_mul_right _ _⟩
  have hfib : ∑ r ∈ B, serH q f (insert p M) ((p : ZMod q) * r) =
      ∑ r' ∈ B.filter (fun r' => (p : ZMod q) ∣ r'), (p : ℝ) * serH q f (insert p M) r' := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun r' hr' => ?_
    have hr'1 := mem_filter.1 hr'
    have hset : B.filter (fun r => (p : ZMod q) * r = r') =
        univ.filter (fun r : ZMod q => (p : ZMod q) * r = r') := by
      ext r
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨(hB r).1 ?_, h⟩
        rw [h]
        exact hr'1.1
    have hconst : ∀ r ∈ univ.filter (fun r : ZMod q => (p : ZMod q) * r = r'),
        serH q f (insert p M) ((p : ZMod q) * r) = serH q f (insert p M) r' := by
      intro r hr
      rw [(mem_filter.1 hr).2]
    rw [hset, Finset.sum_congr rfl hconst, Finset.sum_const, red_card_fiber hpq hr'1.2,
      nsmul_eq_mul]
  have hsub : ∑ r ∈ B, serH q f M r = ∑ r ∈ B, serH q f (insert p M) r -
      (∑ r ∈ B, serH q f (insert p M) ((p : ZMod q) * r)) / p := by
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← serH_insert f hp hpM r]
  have hdiv : (∑ r' ∈ B.filter (fun r' => (p : ZMod q) ∣ r'),
      (p : ℝ) * serH q f (insert p M) r') / p =
      ∑ r' ∈ B.filter (fun r' => (p : ZMod q) ∣ r'), serH q f (insert p M) r' := by
    rw [← Finset.mul_sum, mul_div_cancel_left₀ _ hp0]
  rw [hsub, hfib, hdiv, ← Finset.sum_filter_add_sum_filter_not B
    (fun r => (p : ZMod q) ∣ r) (fun r => serH q f (insert p M) r)]
  ring

/-- `κ(M ∪ p', p) = κ(M, p)` for a prime `p' ∣ q` not in `M`. -/
theorem red_kappa_insert [NeZero q] (f : ZMod q → ℚ) {M : Finset ℕ} {p p' : ℕ}
    (hp : p.Prime) (hp' : p'.Prime) (hp'q : p' ∣ q) (hpM : p ∈ M) (hp'M : p' ∉ M)
    (hM : ∀ l ∈ M, l.Prime) : red_kappa q f (insert p' M) p = red_kappa q f M p := by
  classical
  have hne : p ≠ p' := ne_of_mem_of_not_mem hpM hp'M
  have hB : ∀ r : ZMod q,
      (p' : ZMod q) * r ∈ univ.filter (fun r : ZMod q =>
        (p : ZMod q) ∣ r ∧ ∀ l ∈ M, l ≠ p → ¬ (l : ZMod q) ∣ r) ↔
      r ∈ univ.filter (fun r : ZMod q =>
        (p : ZMod q) ∣ r ∧ ∀ l ∈ M, l ≠ p → ¬ (l : ZMod q) ∣ r) := by
    intro r
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨dvd_of_dvd_prime_mul hp hp' hne h1,
        fun l hl hlp hd => h2 l hl hlp (Dvd.dvd.mul_left hd _)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨Dvd.dvd.mul_left h1 _, fun l hl hlp hd => h2 l hl hlp
        (dvd_of_dvd_prime_mul (hM l hl) hp' (ne_of_mem_of_not_mem hl hp'M) hd)⟩
  have key := red_sum_serH_insert f hp' hp'q hp'M _ hB
  rw [red_kappa_eq, red_kappa_eq, ← key]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext r
  simp only [mem_filter, mem_univ, true_and, mem_insert, forall_eq_or_imp]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h3⟩, h2 hne.symm⟩
  · rintro ⟨⟨h1, h3⟩, h2⟩
    exact ⟨h1, fun _ => h2, h3⟩

/-! ## 5. All the primes -/

/-- `R_∅(N) - R_m(N) → -(1/q) ∑_{p ∈ m} κ(m, p) log p` for a set `m` of primes dividing `q`. -/
theorem red_tendsto_sub [NeZero q] (hq : Odd q) (f : ZMod q → ℚ) :
    ∀ m : Finset ℕ, m ⊆ q.primeFactors →
      Tendsto (fun N : ℕ => red_R q f ∅ N - red_R q f m N) atTop
        (nhds (-((∑ p ∈ m, red_kappa q f m p * Real.log (p : ℝ)) / (q : ℝ)))) := by
  classical
  intro m
  induction m using Finset.induction_on with
  | empty =>
    intro _
    simp only [sub_self, Finset.sum_empty, zero_div, neg_zero]
    exact tendsto_const_nhds
  | insert p m hpm ih =>
    intro hsub
    have hp := Nat.mem_primeFactors.1 (hsub (mem_insert_self p m))
    have hm' : m ⊆ q.primeFactors := fun l hl => hsub (mem_insert_of_mem hl)
    have hmP : ∀ l ∈ m, l.Prime := fun l hl => (Nat.mem_primeFactors.1 (hm' hl)).1
    have hinsP : ∀ l ∈ insert p m, l.Prime :=
      fun l hl => (Nat.mem_primeFactors.1 (hsub hl)).1
    have h1 := ih hm'
    have h2 := red_step hq f hp.1 hp.2.1 hpm hmP
    have hsum : ∑ p' ∈ insert p m, red_kappa q f (insert p m) p' * Real.log (p' : ℝ) =
        red_kappa q f (insert p m) p * Real.log (p : ℝ) +
          ∑ p' ∈ m, red_kappa q f m p' * Real.log (p' : ℝ) := by
      rw [Finset.sum_insert hpm]
      congr 1
      refine Finset.sum_congr rfl fun p' hp' => ?_
      rw [red_kappa_insert f (hmP p' hp') hp.1 hp.2.1 hp' hpm hmP]
    have hlim : -((red_kappa q f (insert p m) p * Real.log (p : ℝ) +
        ∑ p' ∈ m, red_kappa q f m p' * Real.log (p' : ℝ)) / (q : ℝ)) =
        -((∑ p' ∈ m, red_kappa q f m p' * Real.log (p' : ℝ)) / (q : ℝ)) +
          -(red_kappa q f (insert p m) p * Real.log (p : ℝ) / (q : ℝ)) := by
      ring
    rw [hsum, hlim]
    refine Tendsto.congr (fun N => ?_) (h1.add h2)
    ring

end Okada

open Okada

/-- **Reduction to the units.** `S_N(f) - S'_N(g) → -(1/q) ∑_{p ∣ q} ℓ_p log p`, with
`g = okadaG q f` and `ℓ_p = Okada.layerSum q f p`. -/
theorem okadaUnitReduction : OkadaUnitReduction := by
  intro q _ hq f _
  have h := red_tendsto_sub hq f q.primeFactors subset_rfl
  have hsum : ∑ p ∈ q.primeFactors, red_kappa q f q.primeFactors p * Real.log (p : ℝ) =
      ∑ p ∈ q.primeFactors, layerSum q f p * Real.log (p : ℝ) :=
    Finset.sum_congr rfl fun p _ => by rw [red_kappa_primeFactors]
  rw [hsum] at h
  refine h.congr fun N => ?_
  rw [red_R_empty, red_R_primeFactors]

end Erdos

end PiFormula
