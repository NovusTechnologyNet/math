import Pilean.PiFormula.Bridge

/-!
# The private-prime argument in the Gaussian integers

Facts 1 and 2 of pi_formula_theorem.md, and their combination:

* `exists_gaussian_prime_above`: a rational prime `p ≡ 1 (mod 4)` is `π * conj π` for a
  Gaussian prime `π`.
* `sum_mul_mult_diff_eq_zero` (Fact 1): if `W ^ N` is real, then
  `∑ c_n (μ_π(n + i) - μ_π(n - i)) = 0`, where `μ_π` is the multiplicity of `π`.
* `mult_diff_ne_zero`, `mult_diff_eq_zero` (Fact 2): the difference is non-zero exactly
  when `p ∣ n² + 1`. (If `π` divided both `n + i` and `n - i`, it would divide their
  difference `2i`, which is impossible for odd `p`.)
* `coeff_eq_zero_of_private_prime`: in an arctangent relation, a term `arctan (1/n₀)`
  with a prime `p ≡ 1 (mod 4)` dividing `n₀² + 1` and no other `n² + 1` has coefficient 0.
-/

open Complex

namespace PiFormula

section Multiplicity

variable {π : GaussianInt}

theorem mult_mul (hπ : Prime π) {x y : GaussianInt} (hx : x ≠ 0) (hy : y ≠ 0) :
    multiplicity π (x * y) = multiplicity π x + multiplicity π y :=
  multiplicity_mul hπ (FiniteMultiplicity.of_prime_left hπ (mul_ne_zero hx hy))

theorem mult_prod (hπ : Prime π) {ι : Type*} (s : Finset ι) (f : ι → GaussianInt)
    (hf : ∀ n ∈ s, f n ≠ 0) :
    multiplicity π (∏ n ∈ s, f n) = ∑ n ∈ s, multiplicity π (f n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      mult_mul hπ (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.2 fun n hn => hf n (Finset.mem_insert_of_mem hn)),
      ih fun n hn => hf n (Finset.mem_insert_of_mem hn)]

theorem mult_spow (hπ : Prime π) (z : GaussianInt) (c : ℤ) :
    multiplicity π (spow z c) =
      c.toNat * multiplicity π z + (-c).toNat * multiplicity π (star z) := by
  unfold spow
  split_ifs with hc
  · rw [multiplicity_pow hπ, (Int.toNat_eq_zero (n := -c)).2 (by omega), zero_mul, add_zero]
  · rw [multiplicity_pow hπ, (Int.toNat_eq_zero (n := c)).2 (by omega), zero_mul, zero_add]

theorem star_spow (z : GaussianInt) (c : ℤ) : star (spow z c) = spow (star z) c := by
  unfold spow
  split_ifs <;> simp [star_pow]

theorem star_W {ι : Type*} (s : Finset ι) (f : ι → ℕ) (c : ι → ℤ) :
    star (W s f c) = ∏ n ∈ s, spow (star (gz (f n))) (c n) := by
  unfold W
  rw [← starRingEnd_apply, map_prod]
  exact Finset.prod_congr rfl fun n _ => by rw [starRingEnd_apply, star_spow]

/-- **Fact 1.** If `W ^ N` is fixed by conjugation (`N > 0`), then the multiplicities of a
Gaussian prime `π` in `n + i` and in `n - i` satisfy `∑ c_n (μ(n + i) - μ(n - i)) = 0`. -/
theorem sum_mul_mult_diff_eq_zero (hπ : Prime π) {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (c : ι → ℤ) {N : ℕ} (hN : 0 < N) (hstar : star (W s f c ^ N) = W s f c ^ N) :
    ∑ n ∈ s, c n * ((multiplicity π (gz (f n)) : ℤ) - multiplicity π (star (gz (f n)))) = 0 := by
  have hz : ∀ n, star (gz n) ≠ 0 := fun n => by simpa using gz_ne_zero n
  have hA : multiplicity π (W s f c ^ N) =
      N * ∑ n ∈ s, ((c n).toNat * multiplicity π (gz (f n)) +
        (-c n).toNat * multiplicity π (star (gz (f n)))) := by
    rw [multiplicity_pow hπ, W,
      mult_prod hπ _ _ fun n _ => spow_ne_zero (gz_ne_zero (f n)) _]
    simp only [mult_spow hπ]
  have hB : multiplicity π (star (W s f c ^ N)) =
      N * ∑ n ∈ s, ((c n).toNat * multiplicity π (star (gz (f n))) +
        (-c n).toNat * multiplicity π (gz (f n))) := by
    rw [star_pow, multiplicity_pow hπ, star_W,
      mult_prod hπ _ _ fun n _ => spow_ne_zero (hz (f n)) _]
    simp only [mult_spow hπ, star_star]
  have hAB : (multiplicity π (W s f c ^ N) : ℤ) = multiplicity π (star (W s f c ^ N)) := by
    rw [hstar]
  rw [hA, hB] at hAB
  push_cast at hAB
  have key : (N : ℤ) * ∑ n ∈ s, c n * ((multiplicity π (gz (f n)) : ℤ) -
      multiplicity π (star (gz (f n)))) = 0 := by
    rw [← sub_eq_zero] at hAB
    rw [← hAB, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    linear_combination ((multiplicity π (star (gz (f n))) : ℤ) - multiplicity π (gz (f n))) *
      Int.toNat_sub_toNat_neg (c n)
  rcases mul_eq_zero.1 key with h | h
  · exact absurd h (by exact_mod_cast hN.ne')
  · exact h

end Multiplicity

section Fact2

variable {π : GaussianInt} {p : ℕ}

theorem gz_mul_star (n : ℕ) : gz n * star (gz n) = ((n * n + 1 : ℕ) : GaussianInt) := by
  ext <;> simp [gz]

theorem gz_sub_star (n : ℕ) : gz n - star (gz n) = ⟨0, 2⟩ := by
  ext <;> simp [gz]

theorem norm_eq_of_mul_star (hpi : π * star π = (p : GaussianInt)) : π.norm = p := by
  have h := congrArg Zsqrtd.re ((Zsqrtd.norm_eq_mul_conj π).trans hpi)
  simpa using h

/-- If `π ∣ x` then `p ∣ N(x)`. -/
theorem natCast_dvd_norm (hpi : π * star π = (p : GaussianInt)) {x : GaussianInt} (h : π ∣ x) :
    (p : ℤ) ∣ x.norm := by
  obtain ⟨y, rfl⟩ := h
  rw [Zsqrtd.norm_mul, norm_eq_of_mul_star hpi]
  exact dvd_mul_right _ _

theorem dvd_of_dvd_natCast (hpi : π * star π = (p : GaussianInt)) (hp : p.Prime) {m : ℕ}
    (h : π ∣ (m : GaussianInt)) : p ∣ m := by
  have h1 := natCast_dvd_norm hpi h
  have h2 : ((m : GaussianInt)).norm = (m : ℤ) * m := by simp [Zsqrtd.norm_def]
  rw [h2] at h1
  have h3 : p ∣ m * m := by exact_mod_cast h1
  rcases (Nat.Prime.dvd_mul hp).1 h3 with h4 | h4 <;> exact h4

/-- **Fact 2, first half.** If `p ∣ n² + 1`, then `π` divides exactly one of `n ± i`. -/
theorem dvd_gz_iff_not_dvd_star (hπ : Prime π) (hpi : π * star π = (p : GaussianInt))
    (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} (hdiv : p ∣ n ^ 2 + 1) :
    (π ∣ gz n ↔ ¬ π ∣ star (gz n)) := by
  have hboth : ¬ (π ∣ gz n ∧ π ∣ star (gz n)) := by
    rintro ⟨h1, h2⟩
    have h3 := natCast_dvd_norm hpi (dvd_sub h1 h2)
    rw [gz_sub_star] at h3
    have h4 : (p : ℤ) ∣ 2 * 2 := by simpa [Zsqrtd.norm_def] using h3
    have h5 : p ∣ 2 * 2 := by exact_mod_cast h4
    have h6 : p ∣ 2 := by rcases (Nat.Prime.dvd_mul hp).1 h5 with h | h <;> exact h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h6)
  have hone : π ∣ gz n ∨ π ∣ star (gz n) := by
    apply hπ.dvd_or_dvd
    rw [gz_mul_star]
    exact (Dvd.intro _ hpi).trans (Nat.cast_dvd_cast (by rwa [sq] at hdiv))
  tauto

/-- **Fact 2, second half.** If `p ∤ n² + 1`, then `π` divides neither of `n ± i`. -/
theorem not_dvd_gz (hpi : π * star π = (p : GaussianInt)) (hp : p.Prime) {n : ℕ}
    (hndiv : ¬ p ∣ n ^ 2 + 1) : ¬ π ∣ gz n ∧ ¬ π ∣ star (gz n) := by
  rw [sq] at hndiv
  constructor
  · intro h
    exact hndiv (dvd_of_dvd_natCast hpi hp (gz_mul_star n ▸ dvd_mul_of_dvd_left h _))
  · intro h
    exact hndiv (dvd_of_dvd_natCast hpi hp (gz_mul_star n ▸ dvd_mul_of_dvd_right h _))

theorem mult_diff_eq_zero (hpi : π * star π = (p : GaussianInt)) (hp : p.Prime)
    {n : ℕ} (hndiv : ¬ p ∣ n ^ 2 + 1) :
    (multiplicity π (gz n) : ℤ) - multiplicity π (star (gz n)) = 0 := by
  obtain ⟨h1, h2⟩ := not_dvd_gz hpi hp hndiv
  rw [multiplicity_eq_zero_of_not_dvd h1, multiplicity_eq_zero_of_not_dvd h2]
  simp

theorem mult_diff_ne_zero (hπ : Prime π) (hpi : π * star π = (p : GaussianInt)) (hp : p.Prime)
    (hp2 : p ≠ 2) {n : ℕ} (hdiv : p ∣ n ^ 2 + 1) :
    (multiplicity π (gz n) : ℤ) - multiplicity π (star (gz n)) ≠ 0 := by
  have hiff := dvd_gz_iff_not_dvd_star hπ hpi hp hp2 hdiv
  have hfin1 := FiniteMultiplicity.of_prime_left hπ (gz_ne_zero n)
  have hfin2 := FiniteMultiplicity.of_prime_left hπ (by simpa using gz_ne_zero n :
    star (gz n) ≠ 0)
  by_cases h : π ∣ gz n
  · have hpos := (dvd_iff_multiplicity_pos hfin1).2 h
    rw [multiplicity_eq_zero_of_not_dvd (hiff.1 h)]
    omega
  · have hpos := (dvd_iff_multiplicity_pos hfin2).2 (by tauto)
    rw [multiplicity_eq_zero_of_not_dvd h]
    omega

end Fact2

/-- A rational prime `p ≡ 1 (mod 4)` is `π * conj π` for a Gaussian prime `π`. -/
theorem exists_gaussian_prime_above {p : ℕ} (hp : p.Prime) (h4 : p % 4 = 1) :
    ∃ π : GaussianInt, Prime π ∧ π * star π = (p : GaussianInt) := by
  have := Fact.mk hp
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
  set π : GaussianInt := ⟨a, b⟩ with hπdef
  have hab' : a * a + b * b = p := by rw [← hab]; ring
  have hpi : π * star π = (p : GaussianInt) := by
    rw [← hab']
    ext
    · simp [π]
    · simp [π]; ring
  have hnorm : π.norm = p := norm_eq_of_mul_star hpi
  refine ⟨π, ?_, hpi⟩
  have hirr : Irreducible π := by
    refine ⟨fun hu => ?_, fun x y hxy => ?_⟩
    · have := (Zsqrtd.norm_eq_one_iff).2 hu
      rw [hnorm] at this
      simp at this
      exact hp.one_lt.ne' this
    · have hn := congrArg Zsqrtd.norm hxy
      rw [Zsqrtd.norm_mul, hnorm] at hn
      have hn' : p = x.norm.natAbs * y.norm.natAbs := by
        rw [← Int.natAbs_mul, ← hn]; simp
      rw [hn'] at hp
      rcases Nat.prime_mul_iff.1 hp with ⟨_, hy⟩ | ⟨_, hx⟩
      · exact Or.inr ((Zsqrtd.norm_eq_one_iff).1 hy)
      · exact Or.inl ((Zsqrtd.norm_eq_one_iff).1 hx)
  exact hirr.prime

/-- **The private prime.** In an arctangent relation `∑ c_n arctan (1/n) = q π`, if a prime
`p ≡ 1 (mod 4)` divides `n₀² + 1` and no other `n² + 1` with `n` in the relation, then the
coefficient of `arctan (1/n₀)` is 0. -/
theorem coeff_eq_zero_of_private_prime {ι : Type*} {s : Finset ι} {f : ι → ℕ}
    (hs : ∀ n ∈ s, 0 < f n) {c : ι → ℤ}
    {q : ℚ} (h : ∑ n ∈ s, (c n : ℝ) * Real.arctan (1 / f n) = q * Real.pi)
    {p : ℕ} (hp : p.Prime) (h4 : p % 4 = 1) {n₀ : ι} (hn₀ : n₀ ∈ s)
    (hdiv : p ∣ f n₀ ^ 2 + 1) (hpriv : ∀ n ∈ s, n ≠ n₀ → ¬ p ∣ f n ^ 2 + 1) : c n₀ = 0 := by
  obtain ⟨π, hπ, hpi⟩ := exists_gaussian_prime_above hp h4
  have hp2 : p ≠ 2 := by omega
  have hsum := sum_mul_mult_diff_eq_zero hπ s f c q.den_pos (star_pow_W_eq s f hs c q h)
  rw [Finset.sum_eq_single n₀ (fun n hn hne => by
      rw [mult_diff_eq_zero hpi hp (hpriv n hn hne), mul_zero])
      (fun h => absurd hn₀ h)] at hsum
  rcases mul_eq_zero.1 hsum with h0 | h0
  · exact h0
  · exact absurd h0 (mult_diff_ne_zero hπ hpi hp hp2 hdiv)

end PiFormula
