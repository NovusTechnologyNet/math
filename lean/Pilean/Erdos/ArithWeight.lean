import Pilean.Erdos.ArithDefs
import Pilean.Erdos.ArithRing
import Pilean.Erdos.ArithSeries

/-!
# Theorem A from the abstract theorem, part 6: Lemma 2 (the main equation)

For `r ∈ ℤ/q` with components `r_p ∈ ℤ/p^(k_p)` put

  `W(r) = ∏_p w_p(r_p)`,   `w_p(x) = a_p [v_p(x) u_p + χ_p(x / p^(v_p(x)))]` for `x ≠ 0`,
  `w_p(0) = o(p) N_p [k_p u_p]`

(`wGlob`, `wLoc`), elements of `ℚ[S]`. Then

* `sum_wGlob_fiber`: `∑_{r : p r = r'} W(r) = p W(r')` for every prime `p ∣ q` and every `r'`
  divisible by `p`. This is a product of local statements: at the place `p` it is
  `sum_wLoc_fiber`, at the other places multiplication by `p` is a bijection that multiplies
  `w_{p'}` by a group element (`wLoc_natCast_mul`), and the group elements cancel by the
  definition of `u_p`.
* `wGlob_eq`: `W(r) = o(P - n) a_n N_{P - n} [cl(r)]` with `n = n(r)`.
* `sum_wGlob`: so `∑_r f(r) W(r) = o(P) ∑_{n ≠ ∅} a_n N_{P - n} g_n`, the left side of (M).

By `sum_eq_zero_of_harmonic` (applied to every coefficient of `W`), condition (a) gives
`∑_r f(r) W(r) = 0`: this is `mainEq`.
-/

set_option linter.unusedSectionVars false

open scoped BigOperators

open AddMonoidAlgebra (single)

namespace PiFormula

namespace Erdos

namespace Arith

section Weight

variable (q : ℕ) (χ : ∀ p : Idx q, ZMod p.1 → ZMod (2 ^ sExp q p))

/-- The local factor `w_p`. -/
noncomputable def wLoc (p : Idx q) (x : LocRing q p) : GRing (sExp q) :=
  (if x = 0 then single 0 (oRat q {p}) * normElt (sExp q) {p}
    else aElt (piVal q) (uVec q χ) p) * single (zLoc q χ p x) 1

/-- The weight `W`, as a function of the components. -/
noncomputable def wGlob (y : ∀ p : Idx q, LocRing q p) : GRing (sExp q) :=
  ∏ p, wLoc q χ p (y p)

variable {q}

theorem idx_prime (p : Idx q) : p.1.Prime := Nat.prime_of_mem_primeFactors p.2

theorem oRat_ne_zero (n : Finset (Idx q)) : oRat q n ≠ 0 := by
  unfold oRat
  rw [Finset.prod_ne_zero_iff]
  intro p _
  have h1 : (1 : ℚ) < (piVal q p : ℚ) := by exact_mod_cast one_lt_piVal p
  exact div_ne_zero (by linarith) (pow_ne_zero _ two_ne_zero)

theorem oRat_singleton (p : Idx q) :
    oRat q {p} = ((p.1 : ℚ) - 1) / 2 ^ sExp q p := by
  simp [oRat, piVal]

variable {χ}

theorem zLoc_zero (p : Idx q) : zLoc q χ p 0 = kExp q p • uVec q χ p := by
  simp [zLoc, locV_zero]

theorem zLoc_of_ne {p : Idx q} {x : LocRing q p} (hx : x ≠ 0) :
    zLoc q χ p x = locV p.1 (kExp q p) x • uVec q χ p +
      Pi.single p (χ p (locR p.1 (kExp q p) x)) := by
  simp [zLoc, hx]

theorem wLoc_zero (p : Idx q) :
    wLoc q χ p 0 = single 0 (oRat q {p}) * normElt (sExp q) {p} * single (zLoc q χ p 0) 1 := by
  simp [wLoc]

theorem wLoc_of_ne {p : Idx q} {x : LocRing q p} (hx : x ≠ 0) :
    wLoc q χ p x = aElt (piVal q) (uVec q χ) p * single (zLoc q χ p x) 1 := by
  simp [wLoc, hx]

theorem single_uVec_mul_neg (p : Idx q) :
    single (uVec q χ p) (1 : ℚ) * single (-uVec q χ p) 1 = 1 := by
  rw [AddMonoidAlgebra.single_mul_single, add_neg_cancel, one_mul]
  rfl

/-- Multiplication by another prime `p₀` multiplies `w_p` by the group element `χ_p(p₀)`. -/
theorem wLoc_natCast_mul (hχ : ∀ p, IsLogChar p.1 (sExp q p) (χ p)) {p p₀ : Idx q}
    (hne : p ≠ p₀) (x : LocRing q p) :
    wLoc q χ p ((p₀.1 : LocRing q p) * x) =
      single (Pi.single p (χ p (p₀.1 : ZMod p.1))) 1 * wLoc q χ p x := by
  have hndvd : ¬ p.1 ∣ p₀.1 := by
    intro h
    exact hne (Subtype.ext ((Nat.prime_dvd_prime_iff_eq (idx_prime p) (idx_prime p₀)).1 h))
  by_cases hx : x = 0
  · subst hx
    rw [mul_zero, wLoc_zero]
    have hins : InSub {p} (Pi.single p (χ p (p₀.1 : ZMod p.1)) : Grp (sExp q)) := by
      intro r hr
      have hrp : r ≠ p := by simpa using hr
      exact Pi.single_eq_of_ne hrp _
    linear_combination (-(single 0 (oRat q {p}) * single (zLoc q χ p 0) 1)) *
      single_mul_normElt hins
  · obtain ⟨h1, h2, h3⟩ := loc_natCast_mul (k := kExp q p) hndvd hx
    have hc0 : (p₀.1 : ZMod p.1) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact hndvd
    rw [wLoc_of_ne h1, wLoc_of_ne hx, zLoc_of_ne h1, zLoc_of_ne hx, h2, h3,
      (hχ p).mul _ _ hc0 (locR_ne_zero hx), Pi.single_add, mul_left_comm,
      AddMonoidAlgebra.single_mul_single, one_mul]
    congr 2
    abel

/-- The sum of the `[χ_p(t)]` over the non-zero residues `t` is `o(p) N_p`. -/
theorem sum_single_chi (hχ : ∀ p, IsLogChar p.1 (sExp q p) (χ p)) (p : Idx q) :
    ∑ t ∈ Finset.univ.erase (0 : ZMod p.1),
      single (Pi.single p (χ p t) : Grp (sExp q)) (1 : ℚ) =
      single 0 (oRat q {p}) * normElt (sExp q) {p} := by
  have hmaps : ∀ t ∈ Finset.univ.erase (0 : ZMod p.1),
      χ p t ∈ (Finset.univ : Finset (ZMod (2 ^ sExp q p))) := fun t _ => Finset.mem_univ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, normElt_singleton, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hcongr : ∀ t ∈ (Finset.univ.erase (0 : ZMod p.1)).filter (fun t => χ p t = c),
      single (Pi.single p (χ p t) : Grp (sExp q)) (1 : ℚ) = single (Pi.single p c) 1 := by
    intro t ht
    rw [(Finset.mem_filter.1 ht).2]
  have hset : (Finset.univ.erase (0 : ZMod p.1)).filter (fun t => χ p t = c) =
      Finset.univ.filter (fun t : ZMod p.1 => t ≠ 0 ∧ χ p t = c) := by
    ext t
    simp
  have hcard := (hχ p).card_fiber c
  have hp1 : 1 ≤ p.1 := (idx_prime p).one_lt.le
  have hcardQ : (((Finset.univ.filter (fun t : ZMod p.1 => t ≠ 0 ∧ χ p t = c)).card : ℕ) : ℚ) =
      oRat q {p} := by
    rw [oRat_singleton, eq_div_iff (pow_ne_zero _ two_ne_zero)]
    have h := congrArg (Nat.cast : ℕ → ℚ) hcard
    push_cast [Nat.cast_sub hp1] at h
    linear_combination h
  rw [Finset.sum_congr rfl hcongr, Finset.sum_const, hset, ← Nat.cast_smul_eq_nsmul ℚ, hcardQ,
    smul_eq_single_mul]

/-- The local identity at the place `p`: `∑_{x : p x = y} w_p(x) = p [-u_p] w_p(y)` for
`y = p x₀`. -/
theorem sum_wLoc_fiber (hχ : ∀ p, IsLogChar p.1 (sExp q p) (χ p)) (p : Idx q)
    (x₀ : LocRing q p) :
    ∑ x ∈ Finset.univ.filter (fun x : LocRing q p => (p.1 : LocRing q p) * x =
      (p.1 : LocRing q p) * x₀), wLoc q χ p x =
      single 0 (p.1 : ℚ) * single (-uVec q χ p) 1 * wLoc q χ p ((p.1 : LocRing q p) * x₀) := by
  have hk : kExp q p ≠ 0 := kExp_ne_zero p
  have hUV := single_uVec_mul_neg (χ := χ) p
  by_cases h0 : (p.1 : LocRing q p) * x₀ = 0
  · have hfil : Finset.univ.filter (fun x : LocRing q p => (p.1 : LocRing q p) * x =
        (p.1 : LocRing q p) * x₀) = Finset.univ.filter (fun x : LocRing q p =>
        (p.1 : LocRing q p) * x = (p.1 : LocRing q p) * 0) := by
      rw [h0, mul_zero]
    have hterm : ∀ t ∈ Finset.univ.erase (0 : ZMod p.1),
        wLoc q χ p (0 + locT p.1 (kExp q p) t) =
          aElt (piVal q) (uVec q χ) p * single ((kExp q p - 1) • uVec q χ p) 1 *
            single (Pi.single p (χ p t)) 1 := by
      intro t ht
      have ht0 : t ≠ 0 := Finset.ne_of_mem_erase ht
      obtain ⟨h1, h2, h3⟩ := loc_locT hk ht0
      rw [zero_add, wLoc_of_ne h1, zLoc_of_ne h1, h2, h3, mul_assoc,
        AddMonoidAlgebra.single_mul_single, one_mul]
    have e1 : single (kExp q p • uVec q χ p) (1 : ℚ) =
        single (uVec q χ p) 1 * single ((kExp q p - 1) • uVec q χ p) 1 := by
      rw [AddMonoidAlgebra.single_mul_single, one_mul, ← succ_nsmul',
        Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hk)]
    have ea : aElt (piVal q) (uVec q χ) p =
        single 0 (p.1 : ℚ) - single (uVec q χ p) 1 := by
      simp [aElt, piVal]
    rw [hfil, sum_fiber_p_mul hk, h0, wLoc_zero,
      ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : ZMod p.1)),
      Finset.sum_congr rfl hterm, ← Finset.mul_sum, sum_single_chi hχ p, locT_zero, zero_add,
      wLoc_zero, zLoc_zero, e1, ea]
    linear_combination (-(single 0 (p.1 : ℚ) * single ((kExp q p - 1) • uVec q χ p) 1 *
      (single 0 (oRat q {p}) * normElt (sExp q) {p}))) * hUV
  · have hterm : ∀ t : ZMod p.1, wLoc q χ p (x₀ + locT p.1 (kExp q p) t) =
        single (-uVec q χ p) 1 * wLoc q χ p ((p.1 : LocRing q p) * x₀) := by
      intro t
      have hpx : (p.1 : LocRing q p) * (x₀ + locT p.1 (kExp q p) t) =
          (p.1 : LocRing q p) * x₀ := by
        rw [mul_add, p_mul_locT hk, add_zero]
      have hne : (p.1 : LocRing q p) * (x₀ + locT p.1 (kExp q p) t) ≠ 0 := by
        rw [hpx]
        exact h0
      obtain ⟨h1, h2, h3⟩ := loc_p_mul hne
      rw [hpx] at h2 h3
      rw [wLoc_of_ne h1, wLoc_of_ne h0, zLoc_of_ne h1, zLoc_of_ne h0, h2, h3, mul_left_comm,
        AddMonoidAlgebra.single_mul_single, one_mul]
      congr 2
      rw [succ_nsmul]
      abel
    rw [sum_fiber_p_mul hk, Finset.sum_congr rfl (fun t _ => hterm t), Finset.sum_const,
      Finset.card_univ, ZMod.card, ← Nat.cast_smul_eq_nsmul ℚ, smul_eq_single_mul, mul_assoc]

/-- `∑_{r : p₀ r = p₀ r₀} W(r) = p₀ W(p₀ r₀)`. -/
theorem sum_wGlob_fiber [NeZero q] (hχ : ∀ p, IsLogChar p.1 (sExp q p) (χ p)) (p₀ : Idx q)
    (r₀ : ZMod q) :
    ∑ r ∈ Finset.univ.filter (fun r : ZMod q => (p₀.1 : ZMod q) * r = (p₀.1 : ZMod q) * r₀),
      wGlob q χ (crt q r) = single 0 (p₀.1 : ℚ) * wGlob q χ (crt q ((p₀.1 : ZMod q) * r₀)) := by
  classical
  have hcrt : ∀ (r : ZMod q) (p : Idx q),
      crt q ((p₀.1 : ZMod q) * r) p = (p₀.1 : LocRing q p) * crt q r p := by
    intro r p
    rw [map_mul, map_natCast]
    rfl
  have ha : ∑ r ∈ Finset.univ.filter
      (fun r : ZMod q => (p₀.1 : ZMod q) * r = (p₀.1 : ZMod q) * r₀), wGlob q χ (crt q r) =
      ∑ y ∈ Fintype.piFinset (fun p : Idx q => Finset.univ.filter (fun x : LocRing q p =>
        (p₀.1 : LocRing q p) * x = (p₀.1 : LocRing q p) * crt q r₀ p)), wGlob q χ y := by
    refine Finset.sum_equiv (crt q).toEquiv ?_ ?_
    · intro r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset,
        RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
      constructor
      · intro h p
        rw [← hcrt, ← hcrt, h]
      · intro h
        apply (crt q).injective
        funext p
        rw [hcrt, hcrt]
        exact h p
    · intro r _
      rfl
  have hfac : ∀ p : Idx q, ∑ x ∈ Finset.univ.filter (fun x : LocRing q p =>
      (p₀.1 : LocRing q p) * x = (p₀.1 : LocRing q p) * crt q r₀ p), wLoc q χ p x =
      (single (Pi.single p (uVec q χ p₀ p)) 1 *
        (if p = p₀ then single 0 (p₀.1 : ℚ) * single (-uVec q χ p₀) 1 else 1)) *
        wLoc q χ p ((p₀.1 : LocRing q p) * crt q r₀ p) := by
    intro p
    by_cases hp : p = p₀
    · subst hp
      rw [sum_wLoc_fiber hχ, uVec_self, Pi.single_zero]
      simp only [↓reduceIte]
      rw [show single (0 : Grp (sExp q)) (1 : ℚ) = 1 from rfl, one_mul]
    · have hunit : IsUnit (p₀.1 : LocRing q p) := by
        rw [ZMod.isUnit_iff_coprime]
        exact Nat.Coprime.pow_right _ ((Nat.coprime_primes (idx_prime p₀) (idx_prime p)).2
          (fun e => hp (Subtype.ext e.symm)))
      have hfil : Finset.univ.filter (fun x : LocRing q p =>
          (p₀.1 : LocRing q p) * x = (p₀.1 : LocRing q p) * crt q r₀ p) = {crt q r₀ p} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact hunit.mul_right_inj
      have hu : uVec q χ p₀ p + χ p (p₀.1 : ZMod p.1) = 0 := by
        simp [uVec, hp]
      simp only [hp, ↓reduceIte]
      rw [hfil, Finset.sum_singleton, wLoc_natCast_mul hχ hp, mul_one, ← mul_assoc,
        AddMonoidAlgebra.single_mul_single, one_mul, ← Pi.single_add, hu, Pi.single_zero]
      exact (one_mul _).symm
  have hsum : ∑ p : Idx q, (Pi.single p (uVec q χ p₀ p) : Grp (sExp q)) = uVec q χ p₀ :=
    Finset.univ_sum_single (uVec q χ p₀)
  rw [ha]
  unfold wGlob
  rw [← Finset.prod_univ_sum (fun p : Idx q => Finset.univ.filter (fun x : LocRing q p =>
      (p₀.1 : LocRing q p) * x = (p₀.1 : LocRing q p) * crt q r₀ p))
      (fun p x => wLoc q χ p x),
    Finset.prod_congr rfl (fun p _ => hfac p), Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    AddMonoidAlgebra.prod_single, Finset.prod_const_one, hsum, Finset.prod_ite_eq']
  simp only [Finset.mem_univ, ↓reduceIte]
  rw [Finset.prod_congr rfl (fun p _ => congrArg (wLoc q χ p) (hcrt r₀ p).symm),
    mul_left_comm (single (uVec q χ p₀) 1),
    single_uVec_mul_neg, mul_one]

/-- `W(r) = o(P - n) a_n N_{P - n} [cl(r)]` with `n = n(r)`. -/
theorem wGlob_eq (y : ∀ p : Idx q, LocRing q p) :
    wGlob q χ y = single 0 (oRat q (suppPi q y)ᶜ) *
      (aProd (piVal q) (uVec q χ) (suppPi q y) * normElt (sExp q) (suppPi q y)ᶜ *
        single (clPi q χ y) 1) := by
  classical
  have h1 : Finset.univ.filter (fun p : Idx q => y p = 0) = (suppPi q y)ᶜ := by
    ext p
    simp [suppPi]
  have h2 : Finset.univ.filter (fun p : Idx q => ¬ y p = 0) = suppPi q y := rfl
  have h3 : ∏ p ∈ (suppPi q y)ᶜ, oRat q {p} = oRat q (suppPi q y)ᶜ := by
    simp [oRat]
  have h4 : normElt (sExp q) (suppPi q y)ᶜ * single (zPi q χ y) 1 =
      normElt (sExp q) (suppPi q y)ᶜ * single (clPi q χ y) 1 := by
    have hsub : InSub (suppPi q y)ᶜ (zPi q χ y - clPi q χ y) := by
      intro p hp
      have hyp : y p ≠ 0 := by simpa [suppPi] using hp
      simp [clPi, hyp]
    have e : single (zPi q χ y) (1 : ℚ) =
        single (zPi q χ y - clPi q χ y) 1 * single (clPi q χ y) 1 := by
      rw [AddMonoidAlgebra.single_mul_single, sub_add_cancel, one_mul]
    rw [e, ← mul_assoc, mul_comm (normElt _ _), single_mul_normElt hsub]
  have hz : ∑ p, zLoc q χ p (y p) = zPi q χ y := rfl
  unfold wGlob wLoc
  rw [Finset.prod_mul_distrib, AddMonoidAlgebra.prod_single, Finset.prod_const_one, hz,
    Finset.prod_ite, h1, h2, Finset.prod_mul_distrib, AddMonoidAlgebra.prod_single,
    Finset.sum_const_zero, ← normElt_eq_prod, h3]
  unfold aProd
  linear_combination (single 0 (oRat q (suppPi q y)ᶜ) *
    ∏ p ∈ suppPi q y, aElt (piVal q) (uVec q χ) p) * h4

/-- `∑_r f(r) W(r) = o(P) ∑_{n ≠ ∅} a_n N_{P - n} g_n`. -/
theorem sum_wGlob [NeZero q] (f : ZMod q → ℚ) (hf0 : f 0 = 0) :
    ∑ r : ZMod q, single 0 (f r) * wGlob q χ (crt q r) =
      single 0 (oRat q Finset.univ) *
        ∑ n ∈ (Finset.univ : Finset (Idx q)).powerset.filter Finset.Nonempty,
          aProd (piVal q) (uVec q χ) n * normElt (sExp q) nᶜ * gElt q χ f n := by
  classical
  have hn : ∀ n : Finset (Idx q),
      ∑ r ∈ Finset.univ.filter (fun r : ZMod q => suppPi q (crt q r) = n),
        single 0 (f r) * wGlob q χ (crt q r) =
      single 0 (oRat q Finset.univ) *
        (aProd (piVal q) (uVec q χ) n * normElt (sExp q) nᶜ * gElt q χ f n) := by
    intro n
    have hg : ∑ r ∈ Finset.univ.filter (fun r : ZMod q => suppPi q (crt q r) = n),
        single (clPi q χ (crt q r)) (f r) = single 0 (oRat q n) * gElt q χ f n := by
      unfold gElt
      rw [smul_eq_single_mul, ← mul_assoc, AddMonoidAlgebra.single_mul_single, zero_add,
        mul_inv_cancel₀ (oRat_ne_zero n)]
      exact (one_mul _).symm
    have ho : single (0 : Grp (sExp q)) (oRat q Finset.univ) =
        single 0 (oRat q nᶜ) * single 0 (oRat q n) := by
      rw [AddMonoidAlgebra.single_mul_single, zero_add]
      congr 1
      unfold oRat
      rw [mul_comm]
      exact (Finset.prod_mul_prod_compl n _).symm
    have hterm : ∀ r ∈ Finset.univ.filter (fun r : ZMod q => suppPi q (crt q r) = n),
        single 0 (f r) * wGlob q χ (crt q r) =
        single 0 (oRat q nᶜ) * (aProd (piVal q) (uVec q χ) n * normElt (sExp q) nᶜ) *
          single (clPi q χ (crt q r)) (f r) := by
      intro r hr
      have hr' : suppPi q (crt q r) = n := (Finset.mem_filter.1 hr).2
      have e : single (clPi q χ (crt q r)) (f r) =
          single 0 (f r) * single (clPi q χ (crt q r)) 1 := by
        rw [AddMonoidAlgebra.single_mul_single, zero_add, mul_one]
      rw [wGlob_eq, hr', e]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hg, ho]
    ring
  have hempty : aProd (piVal q) (uVec q χ) ∅ * normElt (sExp q) (∅ : Finset (Idx q))ᶜ *
      gElt q χ f ∅ = 0 := by
    have h := hn ∅
    have hz : ∑ r ∈ Finset.univ.filter (fun r : ZMod q => suppPi q (crt q r) = ∅),
        single 0 (f r) * wGlob q χ (crt q r) = 0 := by
      refine Finset.sum_eq_zero fun r hr => ?_
      have hr' : suppPi q (crt q r) = ∅ := (Finset.mem_filter.1 hr).2
      have hr0 : r = 0 := by
        apply (crt q).injective
        rw [map_zero]
        funext p
        by_contra hp
        have : p ∈ suppPi q (crt q r) := Finset.mem_filter.2 ⟨Finset.mem_univ p, hp⟩
        rw [hr'] at this
        exact absurd this (Finset.notMem_empty p)
      rw [hr0, hf0, AddMonoidAlgebra.single_zero, zero_mul]
    rw [hz] at h
    exact single_zero_mul_cancel (oRat_ne_zero _) h.symm
  rw [← Finset.sum_fiberwise Finset.univ (fun r : ZMod q => suppPi q (crt q r)),
    Finset.sum_congr rfl (fun n _ => hn n), ← Finset.mul_sum, Finset.powerset_univ]
  congr 1
  symm
  refine Finset.sum_filter_of_ne fun n _ hne => ?_
  rw [Finset.nonempty_iff_ne_empty]
  rintro rfl
  exact hne hempty

end Weight

/-- **Lemma 2**: condition (a) gives the equation (M). -/
theorem mainEq : MainEqProp := by
  intro q _ _ χ hχ f hf0 ha
  classical
  have hzero : ∑ r : ZMod q, single 0 (f r) * wGlob q χ (crt q r) = 0 := by
    refine ext_coeff fun x => ?_
    rw [coeff_finset_sum]
    simp only [AddMonoidAlgebra.coeff_single_zero_mul]
    have hreal := sum_eq_zero_of_harmonic f
      (fun r => (((wGlob q χ (crt q r)).coeff x : ℚ) : ℝ)) ?_ ha
    · have h : ((∑ r : ZMod q, f r * (wGlob q χ (crt q r)).coeff x : ℚ) : ℝ) = 0 := by
        push_cast
        exact hreal
      have h' : ∑ r : ZMod q, f r * (wGlob q χ (crt q r)).coeff x = 0 := by exact_mod_cast h
      rw [h']
      rfl
    · intro p hp hpq r' hr'
      obtain ⟨r₀, rfl⟩ := hr'
      have hpm : p ∈ q.primeFactors := Nat.mem_primeFactors.2 ⟨hp, hpq, NeZero.ne q⟩
      have h := congrArg (fun z : GRing (sExp q) => z.coeff x)
        (sum_wGlob_fiber hχ ⟨p, hpm⟩ r₀)
      simp only [coeff_finset_sum, AddMonoidAlgebra.coeff_single_zero_mul] at h
      have h' := congrArg (fun z : ℚ => (z : ℝ)) h
      push_cast at h'
      exact h'
  rw [sum_wGlob f hf0] at hzero
  exact single_zero_mul_cancel (oRat_ne_zero _) hzero

end Arith

end Erdos

end PiFormula
