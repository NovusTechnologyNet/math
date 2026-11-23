import Pilean.Erdos.ArithDefs
import Pilean.Erdos.ArithRing

/-!
# Theorem A from the abstract theorem, part 7a: the counting behind Lemma 1

Paper: `02_proof_part_II.md`, fact (C1) of section 1. For a non-empty set `n` of primes of `q`
and `σ ∈ S_n`, the number of `r ∈ ℤ/q` with `n(r) = n` and `cl(r) = σ` has the parity of
`ν(n) = ∏_{p ∈ n} k_p` (`lem1_card_zmod`).

Route. Through `crt` the `r` become tuples `y = (y_p)`, `y_p ∈ ℤ/p^(k_p)`. Split the tuples by
the exponents `j_p = locV (y_p)`: `j_p < k_p` for `p ∈ n` and `j_p = k_p` otherwise, so there
are `ν(n)` tuples of exponents. For fixed exponents the component of `cl(r)` at `p ∈ n` is
`χ_p(locR (y_p))` plus a shift that depends on the exponents only (`lem1_zPi_apply`), so the
set of the `y` is a product of sets (`lem1_mem_fiber_iff`), each of odd size: `1` for `p ∉ n`,
and `p^(k_p - 1 - j_p) (p - 1)/2^(s_p)` for `p ∈ n` (`lem1_card_loc`).

Everything in this file is proved (no `sorry`).
-/

set_option linter.unusedSectionVars false

open scoped BigOperators

namespace PiFormula

namespace Erdos

namespace Arith

/-- The odd part of `p - 1`: `(p - 1)/2^(s_p)`. -/
def lem1_oddPart (q : ℕ) (p : Idx q) : ℕ := (p.1 - 1) / 2 ^ sExp q p

/-- The shift of the class that the exponents `j` produce: `∑_p j_p • u_p`. -/
def lem1_shift (q : ℕ) (χ : ∀ p : Idx q, ZMod p.1 → ZMod (2 ^ sExp q p)) (j : Idx q → ℕ) :
    Grp (sExp q) := ∑ p, j p • uVec q χ p

variable {q : ℕ} {χ : ∀ p : Idx q, ZMod p.1 → ZMod (2 ^ sExp q p)}

/-! ### The odd number `o(n)` -/

theorem lem1_two_pow_mul_oddPart (p : Idx q) : 2 ^ sExp q p * lem1_oddPart q p = p.1 - 1 :=
  Nat.mul_div_cancel' (two_pow_sExp_dvd p)

theorem lem1_oddPart_odd (p : Idx q) : Odd (lem1_oddPart q p) := by
  rw [← Nat.not_even_iff_odd]
  rintro ⟨m, hm⟩
  apply not_two_pow_sExp_succ_dvd p
  refine ⟨m, ?_⟩
  rw [← lem1_two_pow_mul_oddPart p, hm, pow_succ]
  ring

theorem lem1_prod_oddPart_odd (n : Finset (Idx q)) : Odd (∏ p ∈ n, lem1_oddPart q p) :=
  Finset.prod_induction _ Odd (fun _ _ => Odd.mul) odd_one fun p _ => lem1_oddPart_odd p

/-- `o(n)` is the natural number `∏_{p ∈ n} (p - 1)/2^(s_p)`. -/
theorem lem1_oRat_eq (n : Finset (Idx q)) :
    oRat q n = ((∏ p ∈ n, lem1_oddPart q p : ℕ) : ℚ) := by
  unfold oRat
  rw [Nat.cast_prod]
  refine Finset.prod_congr rfl fun p _ => ?_
  have hp1 : 1 ≤ p.1 := (Nat.prime_of_mem_primeFactors p.2).one_lt.le
  have h := congrArg (Nat.cast : ℕ → ℚ) (lem1_two_pow_mul_oddPart p)
  push_cast [Nat.cast_sub hp1] at h
  rw [div_eq_iff (pow_ne_zero _ two_ne_zero)]
  simp only [piVal, Int.cast_natCast]
  linear_combination -h

/-! ### The local count -/

/-- The number of `x ∈ ℤ/p^(k_p)` with exponent `j < k_p` and `χ_p` of the residue equal to `c`
is odd. -/
theorem lem1_card_loc (hq : Odd q) (hχ : ∀ p, IsLogChar p.1 (sExp q p) (χ p)) (p : Idx q)
    {j : ℕ} (hj : j < kExp q p) (c : ZMod (2 ^ sExp q p)) :
    Odd (Finset.univ.filter (fun x : LocRing q p =>
      locV p.1 (kExp q p) x = j ∧ χ p (locR p.1 (kExp q p) x) = c)).card := by
  have hk : kExp q p ≠ 0 := kExp_ne_zero p
  rw [card_locV_locR hk (fun t => χ p t = c) (kExp q p - 1 - j) j (by omega)]
  have h1 := (hχ p).card_fiber c
  have h2 : (Finset.univ.filter (fun t : ZMod p.1 => t ≠ 0 ∧ χ p t = c)).card =
      lem1_oddPart q p :=
    Nat.eq_of_mul_eq_mul_left (pow_pos two_pos _) (h1.trans (lem1_two_pow_mul_oddPart p).symm)
  rw [h2]
  exact Odd.mul (Odd.pow (Odd.of_dvd_nat hq (Nat.dvd_of_mem_primeFactors p.2)))
    (lem1_oddPart_odd p)

/-! ### The class in terms of the components -/

theorem lem1_mem_suppPi {y : ∀ p : Idx q, LocRing q p} {p : Idx q} :
    p ∈ suppPi q y ↔ y p ≠ 0 := by
  simp [suppPi]

/-- `cl(r)` lies in `S_{n(r)}`. -/
theorem lem1_inSub_clPi (y : ∀ p : Idx q, LocRing q p) : InSub (suppPi q y) (clPi q χ y) := by
  intro p hp
  have h0 : y p = 0 := by
    by_contra h
    exact hp (lem1_mem_suppPi.2 h)
  simp [clPi, h0]

/-- The component of the class at a place `p` with `y_p ≠ 0`: `χ_p` of the residue, plus the
shift that the exponents produce. -/
theorem lem1_zPi_apply (y : ∀ p : Idx q, LocRing q p) {p : Idx q} (hy : y p ≠ 0) :
    zPi q χ y p = lem1_shift q χ (fun p' => locV p'.1 (kExp q p') (y p')) p +
      χ p (locR p.1 (kExp q p) (y p)) := by
  have h1 : (∑ p' : Idx q, if y p' = 0 then (0 : Grp (sExp q))
      else Pi.single p' (χ p' (locR p'.1 (kExp q p') (y p')))) p =
      χ p (locR p.1 (kExp q p) (y p)) := by
    rw [Finset.sum_apply, Finset.sum_eq_single p]
    · rw [ite_eq_right hy, Pi.single_eq_same]
    · intro b _ hb
      split_ifs
      · rfl
      · exact Pi.single_eq_of_ne (Ne.symm hb) _
    · intro h
      exact absurd (Finset.mem_univ p) h
  rw [← h1]
  unfold zPi zLoc lem1_shift
  rw [Finset.sum_add_distrib, Pi.add_apply]

/-- For exponents `j` (`j_p < k_p` exactly for `p ∈ n`), the `y` with `n(y) = n`, `cl(y) = σ`
and exponents `j` are those that satisfy a condition on each component separately. -/
theorem lem1_mem_fiber_iff (n : Finset (Idx q)) {σ : Grp (sExp q)} (hσ : InSub n σ)
    (j : Idx q → ℕ) (hj : ∀ p, (p ∈ n → j p < kExp q p) ∧ (p ∉ n → j p = kExp q p))
    (y : ∀ p : Idx q, LocRing q p) :
    ((suppPi q y = n ∧ clPi q χ y = σ) ∧ (fun p : Idx q => locV p.1 (kExp q p) (y p)) = j) ↔
      ∀ p : Idx q, locV p.1 (kExp q p) (y p) = j p ∧
        (p ∈ n → χ p (locR p.1 (kExp q p) (y p)) = σ p - lem1_shift q χ j p) := by
  constructor
  · rintro ⟨⟨hs, hc⟩, hjy⟩ p
    refine ⟨congrFun hjy p, fun hp => ?_⟩
    have hyp : y p ≠ 0 := by
      rw [← hs] at hp
      exact lem1_mem_suppPi.1 hp
    have h := congrFun hc p
    unfold clPi at h
    rw [ite_eq_right hyp, lem1_zPi_apply y hyp, hjy] at h
    linear_combination h
  · intro h
    have hjy : (fun p : Idx q => locV p.1 (kExp q p) (y p)) = j := funext fun p => (h p).1
    have hmem : ∀ p : Idx q, p ∈ n ↔ y p ≠ 0 := by
      intro p
      constructor
      · intro hp hy0
        have h1 := (h p).1
        have h2 := (hj p).1 hp
        rw [hy0, locV_zero] at h1
        omega
      · intro hy0
        by_contra hp
        have h1 := (h p).1
        rw [(hj p).2 hp] at h1
        exact hy0 (locV_eq_iff.1 h1)
    refine ⟨⟨?_, ?_⟩, hjy⟩
    · ext p
      rw [lem1_mem_suppPi, hmem]
    · funext p
      unfold clPi
      by_cases hy0 : y p = 0
      · rw [ite_eq_left hy0]
        have hp : p ∉ n := fun hp => (hmem p).1 hp hy0
        exact (hσ p hp).symm
      · rw [ite_eq_right hy0, lem1_zPi_apply y hy0, hjy, (h p).2 ((hmem p).2 hy0)]
        ring

/-! ### The global count -/

/-- The number of tuples `y` with `n(y) = n` and `cl(y) = σ ∈ S_n` has the parity of
`∏_{p ∈ n} k_p`. -/
theorem lem1_card_pi (hq : Odd q) (hχ : ∀ p, IsLogChar p.1 (sExp q p) (χ p))
    (n : Finset (Idx q)) {σ : Grp (sExp q)} (hσ : InSub n σ) :
    (((Finset.univ.filter (fun y : ∀ p : Idx q, LocRing q p =>
      suppPi q y = n ∧ clPi q χ y = σ)).card : ℕ) : ZMod 2) =
      ((∏ p ∈ n, kExp q p : ℕ) : ZMod 2) := by
  have hmaps : Set.MapsTo
      (fun (y : ∀ p : Idx q, LocRing q p) (p : Idx q) => locV p.1 (kExp q p) (y p))
      ↑(Finset.univ.filter (fun y : ∀ p : Idx q, LocRing q p =>
        suppPi q y = n ∧ clPi q χ y = σ))
      ↑(Fintype.piFinset (fun p : Idx q =>
        if p ∈ n then Finset.range (kExp q p) else {kExp q p})) := by
    intro y hy
    have hy' := (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).2
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro p
    have hmem : p ∈ n ↔ y p ≠ 0 := by
      rw [← hy'.1]
      exact lem1_mem_suppPi
    beta_reduce
    split_ifs with hp
    · exact Finset.mem_range.2 (locV_lt (hmem.1 hp))
    · have h0 : y p = 0 := by
        by_contra h
        exact hp (hmem.2 h)
      rw [h0, locV_zero]
      exact Finset.mem_singleton_self _
  have hfib : ∀ j ∈ Fintype.piFinset (fun p : Idx q =>
      if p ∈ n then Finset.range (kExp q p) else {kExp q p}),
      ((((Finset.univ.filter (fun y : ∀ p : Idx q, LocRing q p =>
        suppPi q y = n ∧ clPi q χ y = σ)).filter
        (fun y => (fun p : Idx q => locV p.1 (kExp q p) (y p)) = j)).card : ℕ) : ZMod 2) =
        1 := by
    intro j hj
    rw [Fintype.mem_piFinset] at hj
    have hj' : ∀ p, (p ∈ n → j p < kExp q p) ∧ (p ∉ n → j p = kExp q p) := by
      intro p
      have h := hj p
      constructor
      · intro hp
        rw [ite_eq_left hp] at h
        exact Finset.mem_range.1 h
      · intro hp
        rw [ite_eq_right hp] at h
        exact Finset.mem_singleton.1 h
    have hset : (Finset.univ.filter (fun y : ∀ p : Idx q, LocRing q p =>
        suppPi q y = n ∧ clPi q χ y = σ)).filter
        (fun y => (fun p : Idx q => locV p.1 (kExp q p) (y p)) = j) =
        Fintype.piFinset (fun p : Idx q => Finset.univ.filter (fun x : LocRing q p =>
          locV p.1 (kExp q p) x = j p ∧
            (p ∈ n → χ p (locR p.1 (kExp q p) x) = σ p - lem1_shift q χ j p))) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
      exact lem1_mem_fiber_iff n hσ j hj' y
    rw [hset, Fintype.card_piFinset, ZMod.natCast_eq_one_iff_odd]
    refine Finset.prod_induction _ Odd (fun _ _ => Odd.mul) odd_one fun p _ => ?_
    by_cases hp : p ∈ n
    · have e : Finset.univ.filter (fun x : LocRing q p => locV p.1 (kExp q p) x = j p ∧
          (p ∈ n → χ p (locR p.1 (kExp q p) x) = σ p - lem1_shift q χ j p)) =
          Finset.univ.filter (fun x : LocRing q p => locV p.1 (kExp q p) x = j p ∧
            χ p (locR p.1 (kExp q p) x) = σ p - lem1_shift q χ j p) := by
        refine Finset.filter_congr fun x _ => ?_
        simp [hp]
      rw [e]
      exact lem1_card_loc hq hχ p ((hj' p).1 hp) _
    · have e : Finset.univ.filter (fun x : LocRing q p => locV p.1 (kExp q p) x = j p ∧
          (p ∈ n → χ p (locR p.1 (kExp q p) x) = σ p - lem1_shift q χ j p)) =
          Finset.univ.filter (fun x : LocRing q p => locV p.1 (kExp q p) x = kExp q p) := by
        refine Finset.filter_congr fun x _ => ?_
        simp [hp, (hj' p).2 hp]
      rw [e, card_locV_eq]
      exact odd_one
  rw [Finset.card_eq_sum_card_fiberwise hmaps, Nat.cast_sum, Finset.sum_congr rfl hfib,
    Finset.sum_const, nsmul_one]
  congr 1
  rw [Fintype.card_piFinset, ← Fintype.prod_ite_mem n (fun p => kExp q p)]
  refine Finset.prod_congr rfl fun p _ => ?_
  split_ifs
  · exact Finset.card_range _
  · exact Finset.card_singleton _

/-- The number of `r ∈ ℤ/q` with `n(r) = n` and `cl(r) = σ ∈ S_n` has the parity of
`∏_{p ∈ n} k_p`. -/
theorem lem1_card_zmod [NeZero q] (hq : Odd q) (hχ : ∀ p, IsLogChar p.1 (sExp q p) (χ p))
    (n : Finset (Idx q)) {σ : Grp (sExp q)} (hσ : InSub n σ) :
    (((Finset.univ.filter (fun r : ZMod q =>
      suppPi q (crt q r) = n ∧ clPi q χ (crt q r) = σ)).card : ℕ) : ZMod 2) =
      ((∏ p ∈ n, kExp q p : ℕ) : ZMod 2) := by
  rw [← lem1_card_pi hq hχ n hσ]
  congr 1
  refine Finset.card_equiv (crt q).toEquiv fun r => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, RingEquiv.toEquiv_eq_coe,
    EquivLike.coe_coe]

end Arith

end Erdos

end PiFormula
