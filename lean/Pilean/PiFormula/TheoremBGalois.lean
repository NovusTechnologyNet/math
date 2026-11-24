module

public import Pilean.PiFormula.TheoremBGamma

/-!
# The Galois table of Part II

The note calls two roots of unity equivalent when they have the same minimal polynomial over
`ℚ(i)`, and an equivalence class an orbit. Here `K = ℚ(i) ⊆ ℂ` (`Ki`), and the orbit of `r` is
`galOrbit r`, the roots of `minpoly K r` (`mem_galOrbit_iff`: `s` is in it iff
`minpoly K s = minpoly K r`).

**The table** (`galois_table`): the explicit multisets of `TheoremBGamma.lean`, namely
`orbit a` (roots of `Φ_m(κ X^N)`), `partner (orbit a)` and `selfOrb k b`, are Galois orbits,
and every root of unity lies in one of them. So `theoremBgamma` is Theorem B for all the
orbits of the note.

The proof:

* `Φ_m(κ X^N)` has its coefficients in `K` (`κ ∈ {±1, ±i}`) and vanishes at `r`, so the minimal
  polynomial divides it; equality follows from the degree bound
  `φ(n) ≤ [K(r) : ℚ] = 2 deg minpoly_K r` for any primitive `n`-th root of unity `ζ ∈ K(r)`
  (`totient_le_two_mul_natDegree`), with `ζ = i κ r` (order `4m`) when `N = 1`, `κ = ±1`, and
  `ζ = r` (order `4 m N`) when `N = 2^s`, `κ = ±i` (`galOrbit_typeA`, `galOrbit_typeB`).
* A partner orbit is again the root multiset of some `Φ_m(κ' X^N)` (`partner_cycPoly`).
* A root of unity of order `2^v m` (`m` odd) lies in an orbit of row `v`
  (`exists_explicit_orbit`); the key step is that for `s` of order `4m`, exactly one of `i s`,
  `-i s` has order `m` (`prim_I_mul_or`).
-/

@[expose] public section

open Polynomial IntermediateField Complex ComplexConjugate

namespace PiFormula

/-! ## 1. `ℚ(i)` and the degree bound -/

/-- `ℚ(i)` inside `ℂ`. -/
noncomputable abbrev Ki : IntermediateField ℚ ℂ := ℚ⟮Complex.I⟯

theorem finrank_Ki : Module.finrank ℚ Ki = 2 := by
  have hI := Complex.isPrimitiveRoot_I
  rw [IntermediateField.adjoin.finrank (hI.isIntegral (by norm_num)).tower_top,
    ← cyclotomic_eq_minpoly_rat hI (by norm_num), natDegree_cyclotomic]
  decide

theorem I_mem_Ki : I ∈ Ki := IntermediateField.mem_adjoin_simple_self ℚ I

/-- **Degree bound.** If `ζ ∈ K(r)` is a primitive `n`-th root of unity, then
`φ(n) ≤ 2 deg minpoly_K r`. -/
theorem totient_le_two_mul_natDegree {r : ℂ} (hint : IsIntegral Ki r)
    {ζ : ℂ} (hζ : ζ ∈ Ki⟮r⟯) {n : ℕ} (hζn : IsPrimitiveRoot ζ n) (hn : 0 < n) :
    n.totient ≤ 2 * (minpoly Ki r).natDegree := by
  have : FiniteDimensional Ki Ki⟮r⟯ := IntermediateField.adjoin.finiteDimensional hint
  have : FiniteDimensional ℚ Ki := IntermediateField.adjoin.finiteDimensional
    ((Complex.isPrimitiveRoot_I.isIntegral (by norm_num)).tower_top)
  have : FiniteDimensional ℚ Ki⟮r⟯ := Module.Finite.trans Ki Ki⟮r⟯
  have htower := Module.finrank_mul_finrank ℚ Ki Ki⟮r⟯
  rw [finrank_Ki, IntermediateField.adjoin.finrank hint] at htower
  have hmin : minpoly ℚ (⟨ζ, hζ⟩ : Ki⟮r⟯) = minpoly ℚ ζ :=
    (minpoly.algebraMap_eq (A := ℚ) (B := Ki⟮r⟯) (B' := ℂ) (algebraMap (Ki⟮r⟯) ℂ).injective
      ⟨ζ, hζ⟩).symm
  have hle := minpoly.natDegree_le (A := ℚ) (⟨ζ, hζ⟩ : Ki⟮r⟯)
  rw [hmin, ← cyclotomic_eq_minpoly_rat hζn hn, natDegree_cyclotomic, ← htower] at hle
  exact hle

theorem mem_adjoin_of_mem_Ki {r κ : ℂ} (h : κ ∈ Ki) : κ ∈ Ki⟮r⟯ :=
  IntermediateField.algebraMap_mem (Ki⟮r⟯) (⟨κ, h⟩ : Ki)

/-! ## 2. Galois orbits -/

/-- The orbit of `r` under `Gal(ℚ̄/ℚ(i))`: the roots of its minimal polynomial over `ℚ(i)`. -/
noncomputable def galOrbit (r : ℂ) : Multiset ℂ := ((minpoly Ki r).map (algebraMap Ki ℂ)).roots

/-- `s` is in the orbit of `r` iff `s` and `r` have the same minimal polynomial over `ℚ(i)`
(the note's definition of an orbit). -/
theorem mem_galOrbit_iff {r s : ℂ} (hr : IsIntegral Ki r) :
    s ∈ galOrbit r ↔ minpoly Ki s = minpoly Ki r := by
  rw [galOrbit, mem_roots_map (minpoly.ne_zero hr), ← aeval_def]
  constructor
  · intro h
    exact (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hr) h (minpoly.monic hr)).symm
  · intro h
    rw [← h]
    exact minpoly.aeval Ki s

/-! ## 3. `Φ_m(κ X^N)` over `K` -/

theorem pow_eq_one_of_mem_roots {m N : ℕ} (hm : 0 < m) {κ : ℂ} (hκ : κ ^ 4 = 1) (hN : N ≠ 0)
    {r : ℂ} (hr : r ∈ (cycPoly m N κ).roots) : r ^ (4 * m * N) = 1 := by
  have hκ0 : κ ≠ 0 := by intro h; rw [h] at hκ; norm_num at hκ
  have hω := ((mem_roots_cycPoly hm hκ0 hN).1 hr).pow_eq_one
  have h1 : (κ * r ^ N) ^ (m * 4) = 1 := by rw [pow_mul, hω, one_pow]
  rw [mul_pow, mul_comm m 4, pow_mul κ 4 m, hκ, one_pow, one_mul, ← pow_mul] at h1
  rw [← h1]
  congr 1
  ring

theorem isIntegral_of_mem_roots {m N : ℕ} (hm : 0 < m) {κ : ℂ} (hκ : κ ^ 4 = 1) (hN : N ≠ 0)
    {r : ℂ} (hr : r ∈ (cycPoly m N κ).roots) : IsIntegral Ki r :=
  IsIntegral.of_pow (n := 4 * m * N) (by positivity)
    (by rw [pow_eq_one_of_mem_roots hm hκ hN hr]; exact isIntegral_one)

/-- If the degree of the minimal polynomial is at least `φ(m) N`, the minimal polynomial of a
root of `Φ_m(κ X^N)` over `ℚ(i)` is `Φ_m(κ X^N)` made monic. -/
theorem minpoly_eq_of_mem_roots {m N : ℕ} (hN : N ≠ 0) {κ : ℂ} (hκK : κ ∈ Ki) (hκ0 : κ ≠ 0)
    {r : ℂ} (hr : r ∈ (cycPoly m N κ).roots) (hint : IsIntegral Ki r)
    (hdeg : m.totient * N ≤ (minpoly Ki r).natDegree) :
    minpoly Ki r = C ((⟨κ, hκK⟩ : Ki) ^ m.totient)⁻¹ *
      (cyclotomic m Ki).comp (C (⟨κ, hκK⟩ : Ki) * X ^ N) := by
  set κK : Ki := ⟨κ, hκK⟩ with hκKdef
  have hκK0 : κK ≠ 0 := by
    intro h; apply hκ0; have := congrArg (fun x : Ki => (x : ℂ)) h; simpa [κK] using this
  set q : Ki[X] := (cyclotomic m Ki).comp (C κK * X ^ N) with hq
  have hqmap : q.map (algebraMap Ki ℂ) = cycPoly m N κ := by
    rw [hq, Polynomial.map_comp, map_cyclotomic, cycPoly]
    simp [κK]
  have hqlead : q.leadingCoeff = κK ^ m.totient := by
    rw [hq, leadingCoeff_comp (by rw [natDegree_C_mul_X_pow N κK hκK0]; exact hN),
      (cyclotomic.monic m Ki).leadingCoeff, leadingCoeff_C_mul_X_pow, natDegree_cyclotomic,
      one_mul]
  have hqdeg : q.natDegree = m.totient * N := by
    rw [hq, natDegree_comp, natDegree_cyclotomic, natDegree_C_mul_X_pow N κK hκK0]
  set f : Ki[X] := C (κK ^ m.totient)⁻¹ * q with hf
  have hc0 : (κK ^ m.totient)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hκK0)
  have hmonic : f.Monic := by
    rw [Monic, hf, leadingCoeff_mul, leadingCoeff_C, hqlead, inv_mul_cancel₀ (pow_ne_zero _ hκK0)]
  have hfdeg : f.natDegree = m.totient * N := by rw [hf, natDegree_C_mul hc0, hqdeg]
  have hroot : (cycPoly m N κ).eval r = 0 := by
    have h0 : cycPoly m N κ ≠ 0 := by
      intro h; rw [h, roots_zero] at hr; exact (Multiset.notMem_zero r) hr
    exact (mem_roots h0).1 hr
  have haeval : aeval r f = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, hf, Polynomial.map_mul, map_C, hqmap, eval_mul, hroot,
      mul_zero]
  have hdvd := minpoly.dvd Ki r haeval
  exact (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hmonic hdvd
    (by rw [hfdeg]; exact hdeg)).symm

/-- If the degree of the minimal polynomial is at least `φ(m) N`, the orbit of a root of
`Φ_m(κ X^N)` is the root multiset of `Φ_m(κ X^N)`. -/
theorem galOrbit_eq_roots {m N : ℕ} (hN : N ≠ 0) {κ : ℂ} (hκK : κ ∈ Ki) (hκ0 : κ ≠ 0)
    {r : ℂ} (hr : r ∈ (cycPoly m N κ).roots) (hint : IsIntegral Ki r)
    (hdeg : m.totient * N ≤ (minpoly Ki r).natDegree) :
    galOrbit r = (cycPoly m N κ).roots := by
  have hmin := minpoly_eq_of_mem_roots hN hκK hκ0 hr hint hdeg
  set κK : Ki := ⟨κ, hκK⟩ with hκKdef
  have hκK0 : κK ≠ 0 := by
    intro h; apply hκ0; have := congrArg (fun x : Ki => (x : ℂ)) h; simpa [κK] using this
  have hqmap : ((cyclotomic m Ki).comp (C κK * X ^ N)).map (algebraMap Ki ℂ) = cycPoly m N κ := by
    rw [Polynomial.map_comp, map_cyclotomic, cycPoly]
    simp [κK]
  have hc0 : (κK ^ m.totient)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hκK0)
  rw [galOrbit, hmin, Polynomial.map_mul, map_C, hqmap, roots_C_mul _ (by simpa using hc0)]

/-- Conversely, the orbit being the roots of `Φ_m(κ X^N)` gives the degree bound. -/
theorem natDegree_minpoly_of_galOrbit {m N : ℕ} {κ : ℂ} (hκ0 : κ ≠ 0) {r : ℂ}
    (h : galOrbit r = (cycPoly m N κ).roots) : m.totient * N ≤ (minpoly Ki r).natDegree := by
  rw [← card_roots_cycPoly (m := m) (N := N) hκ0, ← h, galOrbit]
  exact (Polynomial.card_roots' _).trans natDegree_map_le

/-! ## 4. Orders -/

/-- A primitive 4th root times a primitive `m`-th root (`m` odd) is a primitive `4m`-th root. -/
theorem prim_four_mul {u ω : ℂ} {m : ℕ} (hm : Odd m) (hu : IsPrimitiveRoot u 4)
    (hω : IsPrimitiveRoot ω m) : IsPrimitiveRoot (u * ω) (4 * m) := by
  have hcop : Nat.Coprime 4 m := by
    have := (Nat.coprime_two_left.2 hm).pow_left 2
    simpa using this
  have hord : orderOf (u * ω) = 4 * m := by
    rw [(Commute.all _ _).orderOf_mul_eq_mul_orderOf_of_coprime
      (by rw [← hu.eq_orderOf, ← hω.eq_orderOf]; exact hcop), ← hu.eq_orderOf, ← hω.eq_orderOf]
  exact hord ▸ IsPrimitiveRoot.orderOf (u * ω)

/-- If `r^(2^s)` has even order `b`, then `r` has order `b 2^s`. -/
theorem orderOf_of_pow_two_pow {r : ℂ} {s b : ℕ} (hb : Even b) (h : orderOf (r ^ 2 ^ s) = b) :
    orderOf r = b * 2 ^ s := by
  rw [orderOf_pow' r (pow_ne_zero s two_ne_zero)] at h
  obtain ⟨t, hts, hg⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Nat.gcd_dvd_right (orderOf r) (2 ^ s))
  have ho : orderOf r = b * 2 ^ t := by
    rw [← h, ← hg, Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)]
  rcases eq_or_lt_of_le hts with rfl | hlt
  · exact ho
  · exfalso
    obtain ⟨b', hb'⟩ := hb
    have h1 : 2 ^ (t + 1) ∣ 2 ^ s := pow_dvd_pow 2 hlt
    have h2 : 2 ^ (t + 1) ∣ orderOf r := ⟨b', by rw [ho, hb', pow_succ]; ring⟩
    have h3 := Nat.dvd_gcd h2 h1
    rw [hg] at h3
    have := Nat.le_of_dvd (by positivity) h3
    have := Nat.pow_lt_pow_right (by norm_num : 1 < 2) (Nat.lt_succ_self t)
    omega

theorem totient_four_mul {m : ℕ} (hm : Odd m) : (4 * m).totient = 2 * m.totient := by
  have hcop : Nat.Coprime 4 m := by
    have := (Nat.coprime_two_left.2 hm).pow_left 2
    simpa using this
  rw [Nat.totient_mul hcop]
  rfl

theorem totient_two_pow_mul {m : ℕ} (hm : Odd m) (s : ℕ) :
    (4 * m * 2 ^ s).totient = 2 * 2 ^ s * m.totient := by
  have hcop : Nat.Coprime (2 ^ (s + 2)) m := (Nat.coprime_two_left.2 hm).pow_left _
  rw [show 4 * m * 2 ^ s = 2 ^ (s + 2) * m by ring, Nat.totient_mul hcop,
    Nat.totient_prime_pow Nat.prime_two (by omega), show s + 2 - 1 = s + 1 by omega,
    show (2 : ℕ) - 1 = 1 from rfl]
  ring

/-! ## 5. Each explicit orbit is a Galois orbit -/

/-- Type A: `N = 1`, `κ = ±1` (the orbits `O_m`, `O_2m`). -/
theorem galOrbit_typeA {m : ℕ} (hm : Odd m) {κ : ℂ} (hκ : κ = 1 ∨ κ = -1) {r : ℂ}
    (hr : r ∈ (cycPoly m 1 κ).roots) : galOrbit r = (cycPoly m 1 κ).roots := by
  have hκ4 : κ ^ 4 = 1 := by rcases hκ with rfl | rfl <;> norm_num
  have hκK : κ ∈ Ki := by
    rcases hκ with rfl | rfl
    · exact one_mem _
    · exact neg_mem (one_mem _)
  have hκ0 : κ ≠ 0 := by rcases hκ with rfl | rfl <;> norm_num
  have hint := isIntegral_of_mem_roots hm.pos hκ4 one_ne_zero hr
  refine galOrbit_eq_roots one_ne_zero hκK hκ0 hr hint ?_
  have hω := (mem_roots_cycPoly hm.pos hκ0 one_ne_zero).1 hr
  rw [pow_one] at hω
  have hζ : I * (κ * r) ∈ Ki⟮r⟯ :=
    mul_mem (mem_adjoin_of_mem_Ki I_mem_Ki)
      (mul_mem (mem_adjoin_of_mem_Ki hκK) (IntermediateField.mem_adjoin_simple_self Ki r))
  have h := totient_le_two_mul_natDegree hint hζ (prim_four_mul hm Complex.isPrimitiveRoot_I hω)
    (by have := hm.pos; omega)
  rw [totient_four_mul hm] at h
  omega

/-- Type B: `N = 2^s`, `κ = ±i` (partners of `O_m`, `O_2m`; the rows of order `8m` and
`2^(e+4) m`). -/
theorem galOrbit_typeB {m : ℕ} (hm : Odd m) (s : ℕ) {κ : ℂ} (hκ : κ = I ∨ κ = -I) {r : ℂ}
    (hr : r ∈ (cycPoly m (2 ^ s) κ).roots) : galOrbit r = (cycPoly m (2 ^ s) κ).roots := by
  have hκ4 : κ ^ 4 = 1 := by
    rcases hκ with rfl | rfl
    · exact Complex.I_pow_four
    · rw [neg_pow, Complex.I_pow_four]; norm_num
  have hκK : κ ∈ Ki := by
    rcases hκ with rfl | rfl
    · exact I_mem_Ki
    · exact neg_mem I_mem_Ki
  have hκ0 : κ ≠ 0 := by intro h; rw [h] at hκ4; norm_num at hκ4
  have hN : 2 ^ s ≠ 0 := pow_ne_zero s two_ne_zero
  have hint := isIntegral_of_mem_roots hm.pos hκ4 hN hr
  refine galOrbit_eq_roots hN hκK hκ0 hr hint ?_
  have hω := (mem_roots_cycPoly hm.pos hκ0 hN).1 hr
  -- `r^(2^s) = (-κ) (κ r^(2^s))` has order `4m`
  have hu : IsPrimitiveRoot (-κ) 4 := by
    rcases hκ with rfl | rfl
    · exact Complex.isPrimitiveRoot_neg_I
    · rw [neg_neg]; exact Complex.isPrimitiveRoot_I
  have hκsq : κ * κ = -1 := by rcases hκ with rfl | rfl <;> simp
  have hrN : r ^ 2 ^ s = -κ * (κ * r ^ 2 ^ s) := by linear_combination (r ^ 2 ^ s) * hκsq
  have h4m : IsPrimitiveRoot (r ^ 2 ^ s) (4 * m) := hrN ▸ prim_four_mul hm hu hω
  have hord := orderOf_of_pow_two_pow (s := s) (b := 4 * m) ⟨2 * m, by ring⟩ h4m.eq_orderOf.symm
  have hprim : IsPrimitiveRoot r (4 * m * 2 ^ s) := hord ▸ IsPrimitiveRoot.orderOf r
  have h := totient_le_two_mul_natDegree hint (IntermediateField.mem_adjoin_simple_self Ki r)
    hprim (by have := hm.pos; positivity)
  rw [totient_two_pow_mul hm s] at h
  nlinarith

/-! ## 6. Partners are roots of `Φ_m(κ' X^N)` -/

/-- `I conj (I conj r) = r`. -/
theorem partner_involutive : Function.Involutive (fun r : ℂ => I * conj r) := by
  intro r
  simp only [map_mul, Complex.conj_I, Complex.conj_conj]
  rw [← mul_assoc, show I * -I = 1 by rw [mul_neg, Complex.I_mul_I, neg_neg], one_mul]

theorem mem_partner_iff {S : Multiset ℂ} {s : ℂ} : s ∈ partner S ↔ I * conj s ∈ S := by
  rw [partner, Multiset.mem_map]
  constructor
  · rintro ⟨r, hr, rfl⟩
    have := partner_involutive r
    simp only at this
    rwa [this]
  · intro hs
    exact ⟨I * conj s, hs, partner_involutive s⟩

theorem isPrimitiveRoot_conj_iff {z : ℂ} {m : ℕ} :
    IsPrimitiveRoot (conj z) m ↔ IsPrimitiveRoot z m :=
  ⟨fun h => by simpa using h.map_of_injective (f := starRingEnd ℂ) (RingHom.injective _),
    fun h => h.map_of_injective (RingHom.injective _)⟩

theorem kappa'_pow_four {κ : ℂ} (hκ : κ ^ 4 = 1) (N : ℕ) : (conj κ * (-I) ^ N) ^ 4 = 1 := by
  rw [mul_pow, ← map_pow, hκ, map_one, one_mul, ← pow_mul, mul_comm, pow_mul, neg_pow,
    Complex.I_pow_four]
  norm_num

/-- The partner of the roots of `Φ_m(κ X^N)` is the roots of `Φ_m(κ' X^N)`,
`κ' = conj κ (-i)^N`. -/
theorem partner_cycPoly {m N : ℕ} (hm : 0 < m) (hN : 0 < N) {κ : ℂ} (hκ : κ ^ 4 = 1) :
    partner (cycPoly m N κ).roots = (cycPoly m N (conj κ * (-I) ^ N)).roots := by
  have hκ' := kappa'_pow_four hκ N
  have hκ0 : κ ≠ 0 := by intro h; rw [h] at hκ; norm_num at hκ
  have hκ'0 : conj κ * (-I) ^ N ≠ 0 := by intro h; rw [h] at hκ'; norm_num at hκ'
  rw [partner, Multiset.Nodup.ext ((nodup_roots_cycPoly hm hκ hN).map partner_involutive.injective)
    (nodup_roots_cycPoly hm hκ' hN)]
  intro s
  rw [← partner, mem_partner_iff, mem_roots_cycPoly hm hκ0 hN.ne',
    mem_roots_cycPoly hm hκ'0 hN.ne', ← isPrimitiveRoot_conj_iff (z := conj κ * (-I) ^ N * s ^ N)]
  have : κ * (I * conj s) ^ N = conj (conj κ * (-I) ^ N * s ^ N) := by
    simp only [map_mul, map_pow, Complex.conj_conj, map_neg, Complex.conj_I, neg_neg]
    ring
  rw [this]

/-! ## 7. The table -/

theorem galOrbit_orbit (a : Atom) {r : ℂ} (hr : r ∈ orbit a) : galOrbit r = orbit a := by
  rcases a with k | k | ⟨k, e⟩
  · exact galOrbit_typeA ⟨k, rfl⟩ (Or.inl rfl) hr
  · exact galOrbit_typeA ⟨k, rfl⟩ (Or.inr rfl) hr
  · have hκ : I * (-1) ^ 2 ^ e = I ∨ I * (-1) ^ 2 ^ e = -I := by
      rcases neg_one_pow_eq_or ℂ (2 ^ e) with h | h <;> rw [h] <;> simp
    exact galOrbit_typeB ⟨k, rfl⟩ (e + 2) hκ hr

/-- The constant `κ'` of the partner orbit. -/
theorem partner_orbit_eq (a : Atom) :
    partner (orbit a) = (cycPoly (mOf a) (Npow a) (conj (kappa a) * (-I) ^ Npow a)).roots :=
  partner_cycPoly (mOf_odd a).pos (Npow_pos a) (kappa_pow_four a)

theorem galOrbit_partner (a : Atom) {r : ℂ} (hr : r ∈ partner (orbit a)) :
    galOrbit r = partner (orbit a) := by
  rw [partner_orbit_eq] at hr ⊢
  rcases a with k | k | ⟨k, e⟩
  · simp only [mOf, Npow, kappa, map_one, one_mul, pow_one] at hr ⊢
    exact galOrbit_typeB ⟨k, rfl⟩ 0 (Or.inr rfl) (by simpa using hr)
  · simp only [mOf, Npow, kappa, map_neg, map_one, pow_one, neg_mul, one_mul, neg_neg] at hr ⊢
    exact galOrbit_typeB ⟨k, rfl⟩ 0 (Or.inl rfl) (by simpa using hr)
  · simp only [mOf, Npow, kappa] at hr ⊢
    have hI4 : (-I) ^ 2 ^ (e + 2) = 1 := by
      rw [show 2 ^ (e + 2) = 4 * 2 ^ e by ring, pow_mul, neg_pow, Complex.I_pow_four]; norm_num
    rw [hI4, mul_one] at hr ⊢
    have hκ : conj (I * (-1) ^ 2 ^ e) = I ∨ conj (I * (-1) ^ 2 ^ e) = -I := by
      rcases neg_one_pow_eq_or ℂ (2 ^ e) with h | h <;> rw [h] <;> simp
    exact galOrbit_typeB ⟨k, rfl⟩ (e + 2) hκ hr

theorem galOrbit_selfOrb (k : ℕ) (b : Bool) {r : ℂ} (hr : r ∈ selfOrb k b) :
    galOrbit r = selfOrb k b := by
  have hκ : kappaS b = I ∨ kappaS b = -I := by cases b <;> simp [kappaS]
  have h := galOrbit_typeB (m := 2 * k + 1) ⟨k, rfl⟩ 1 hκ (r := r) (by rw [pow_one]; exact hr)
  rw [pow_one] at h
  exact h

/-! ## 8. Every root of unity lies in an explicit orbit -/

/-- If `s` has order `j m` and `u^j = 1`, `(u s)^m = 1`, then `u s` has order `m`. -/
theorem prim_of_unit_mul {u s : ℂ} {j m : ℕ} (hj : 0 < j) (hu : u ^ j = 1)
    (hs : IsPrimitiveRoot s (j * m)) (h1 : (u * s) ^ m = 1) : IsPrimitiveRoot (u * s) m := by
  refine ⟨h1, fun l hl => ?_⟩
  have h2 : s ^ (j * l) = 1 := by
    have : (u * s) ^ (j * l) = 1 := by rw [mul_comm j l, pow_mul, hl, one_pow]
    rwa [mul_pow, pow_mul u j l, hu, one_pow, one_mul] at this
  exact Nat.dvd_of_mul_dvd_mul_left hj (hs.dvd_of_pow_eq_one _ h2)

/-- For `s` of order `4m` (`m` odd), `i s` or `-i s` has order `m`. -/
theorem prim_I_mul_or {s : ℂ} {m : ℕ} (hm : Odd m) (hs : IsPrimitiveRoot s (4 * m)) :
    IsPrimitiveRoot (I * s) m ∨ IsPrimitiveRoot (-I * s) m := by
  have hI4 : I ^ 4 = 1 := Complex.I_pow_four
  have hnI4 : (-I) ^ 4 = 1 := by rw [neg_pow, Complex.I_pow_four]; norm_num
  have h2m : s ^ (2 * m) = -1 := by
    have hsq : s ^ (2 * m) * s ^ (2 * m) = 1 := by
      rw [← pow_add, show 2 * m + 2 * m = 4 * m by ring, hs.pow_eq_one]
    rcases mul_self_eq_one_iff.1 hsq with h | h
    · exfalso
      have := hs.dvd_of_pow_eq_one _ h
      have := Nat.le_of_dvd (by have := hm.pos; omega) this
      have := hm.pos
      omega
    · exact h
  have hprod : (I * s) ^ m * (-I * s) ^ m = -1 := by
    rw [← mul_pow, show I * s * (-I * s) = s ^ 2 by
      rw [show I * s * (-I * s) = -(I * I) * s ^ 2 by ring, Complex.I_mul_I, neg_neg, one_mul],
      ← pow_mul, h2m]
  have hneg : (-I * s) ^ m = -(I * s) ^ m := by
    rw [show -I * s = -1 * (I * s) by ring, mul_pow, Odd.neg_one_pow hm, neg_one_mul]
  rw [hneg] at hprod
  have hA : (I * s) ^ m * (I * s) ^ m = 1 := by linear_combination -hprod
  rcases mul_self_eq_one_iff.1 hA with h | h
  · exact Or.inl (prim_of_unit_mul (by norm_num) hI4 hs h)
  · exact Or.inr (prim_of_unit_mul (by norm_num) hnI4 hs (by rw [hneg, h, neg_neg]))

theorem prim_neg_of_two_mul {r : ℂ} {m : ℕ} (hm : Odd m) (hr : IsPrimitiveRoot r (2 * m)) :
    IsPrimitiveRoot (-r) m := by
  have hrm : r ^ m = -1 := by
    have hsq : r ^ m * r ^ m = 1 := by rw [← pow_add, ← two_mul, hr.pow_eq_one]
    rcases mul_self_eq_one_iff.1 hsq with h | h
    · exfalso
      have := Nat.le_of_dvd hm.pos (hr.dvd_of_pow_eq_one _ h)
      have := hm.pos
      omega
    · exact h
  have := prim_of_unit_mul (u := -1) (j := 2) (by norm_num) (by norm_num) hr
    (by rw [mul_pow, Odd.neg_one_pow hm, hrm]; norm_num)
  simpa using this

/-- **Every root of unity lies in one of the explicit orbits.** -/
theorem exists_explicit_orbit {r : ℂ} {n : ℕ} (hn : 0 < n) (hr : r ^ n = 1) :
    (∃ a, r ∈ orbit a) ∨ (∃ a, r ∈ partner (orbit a)) ∨ (∃ k b, r ∈ selfOrb k b) := by
  have hfin : IsOfFinOrder r := isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, hr⟩
  have ho := hfin.orderOf_pos
  have hprim := IsPrimitiveRoot.orderOf r
  obtain ⟨v, m, hm, hvm⟩ := Nat.exists_eq_two_pow_mul_odd ho.ne'
  obtain ⟨k, rfl⟩ := hm
  rw [hvm] at hprim
  have hm : Odd (2 * k + 1) := ⟨k, rfl⟩
  have hm0 : 0 < 2 * k + 1 := by omega
  rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ 4 ≤ v by omega) with rfl | rfl | rfl | rfl | hv
  · -- order `m`: `O_m`
    left
    refine ⟨.P k, mem_orbit_iff.2 ?_⟩
    simpa [kappa, Npow, mOf] using hprim
  · -- order `2m`: `O_2m`
    left
    refine ⟨.Q k, mem_orbit_iff.2 ?_⟩
    simpa [kappa, Npow, mOf] using prim_neg_of_two_mul hm (by simpa using hprim)
  · -- order `4m`: partners of `O_m`, `O_2m`
    right; left
    have hc : IsPrimitiveRoot (conj r) (4 * (2 * k + 1)) :=
      isPrimitiveRoot_conj_iff.2 (by simpa using hprim)
    rcases prim_I_mul_or hm hc with h | h
    · exact ⟨.P k, mem_partner_iff.2 (mem_orbit_iff.2 (by simpa [kappa, Npow, mOf] using h))⟩
    · refine ⟨.Q k, mem_partner_iff.2 (mem_orbit_iff.2 ?_)⟩
      simp only [kappa, Npow, mOf, pow_one]
      rw [show -1 * (I * conj r) = -I * conj r by ring]
      exact h
  · -- order `8m`: self-paired
    right; right
    have h2 : IsPrimitiveRoot (r ^ 2) (4 * (2 * k + 1)) :=
      hprim.pow (by positivity) (by ring)
    have hm1 : (0 : ℕ) < 2 * k + 1 := hm0
    rcases prim_I_mul_or hm h2 with h | h
    · exact ⟨k, true, (mem_roots_cycPoly hm1 (by simp [kappaS]) (by norm_num)).2
        (by simpa [kappaS] using h)⟩
    · exact ⟨k, false, (mem_roots_cycPoly hm1 (by simp [kappaS]) (by norm_num)).2
        (by simpa [kappaS] using h)⟩
  · -- order `2^(e+4) m`: the rows `R k e`
    obtain ⟨e, rfl⟩ : ∃ e, v = e + 4 := ⟨v - 4, by omega⟩
    have hN : IsPrimitiveRoot (r ^ 2 ^ (e + 2)) (4 * (2 * k + 1)) :=
      hprim.pow (by positivity) (by ring)
    have hκ0 : kappa (.R k e) ≠ 0 := kappa_ne_zero _
    have hpart := partner_orbit_eq (.R k e)
    have hI4 : (-I) ^ 2 ^ (e + 2) = 1 := by
      rw [show 2 ^ (e + 2) = 4 * 2 ^ e by ring, pow_mul, neg_pow, Complex.I_pow_four]; norm_num
    simp only [mOf, Npow, kappa, hI4, mul_one] at hpart
    have hconj0 : conj (I * (-1) ^ 2 ^ e) ≠ 0 := by
      rw [_root_.map_ne_zero]; exact kappa_ne_zero (.R k e)
    rcases neg_one_pow_eq_or ℂ (2 ^ e) with hsg | hsg
    · -- `κ = i`
      rcases prim_I_mul_or hm hN with h | h
      · left
        refine ⟨.R k e, mem_orbit_iff.2 ?_⟩
        simpa [kappa, Npow, mOf, hsg] using h
      · right; left
        refine ⟨.R k e, ?_⟩
        rw [hpart, mem_roots_cycPoly hm0 hconj0 (by positivity)]
        simpa [hsg] using h
    · -- `κ = -i`
      rcases prim_I_mul_or hm hN with h | h
      · right; left
        refine ⟨.R k e, ?_⟩
        rw [hpart, mem_roots_cycPoly hm0 hconj0 (by positivity)]
        simpa [hsg] using h
      · left
        refine ⟨.R k e, mem_orbit_iff.2 ?_⟩
        simpa [kappa, Npow, mOf, hsg] using h

/-- **The Galois table.** The explicit orbits are orbits of `Gal(ℚ̄/ℚ(i))`, and the orbit of
every root of unity is one of them. -/
theorem galois_table :
    (∀ a r, r ∈ orbit a → galOrbit r = orbit a) ∧
      (∀ a r, r ∈ partner (orbit a) → galOrbit r = partner (orbit a)) ∧
      (∀ k b r, r ∈ selfOrb k b → galOrbit r = selfOrb k b) ∧
      (∀ (r : ℂ) (n : ℕ), 0 < n → r ^ n = 1 →
        (∃ a, galOrbit r = orbit a) ∨ (∃ a, galOrbit r = partner (orbit a)) ∨
          (∃ k b, galOrbit r = selfOrb k b)) := by
  refine ⟨fun a r hr => galOrbit_orbit a hr, fun a r hr => galOrbit_partner a hr,
    fun k b r hr => galOrbit_selfOrb k b hr, fun r n hn hr => ?_⟩
  rcases exists_explicit_orbit hn hr with ⟨a, ha⟩ | ⟨a, ha⟩ | ⟨k, b, hkb⟩
  · exact Or.inl ⟨a, galOrbit_orbit a ha⟩
  · exact Or.inr (Or.inl ⟨a, galOrbit_partner a ha⟩)
  · exact Or.inr (Or.inr ⟨k, b, galOrbit_selfOrb k b hkb⟩)

/-! ## 9. The note's definition, literally -/

/-- `orbit a` is an equivalence class: for `r ∈ orbit a`, a complex number `s` is in it iff `s`
and `r` have the same minimal polynomial over `ℚ(i)`. -/
theorem mem_orbit_iff_minpoly (a : Atom) {r : ℂ} (hr : r ∈ orbit a) (s : ℂ) :
    s ∈ orbit a ↔ minpoly Ki s = minpoly Ki r := by
  rw [← galOrbit_orbit a hr,
    mem_galOrbit_iff (isIntegral_of_mem_roots (mOf_odd a).pos (kappa_pow_four a)
      (Npow_pos a).ne' hr)]

theorem mem_partner_iff_minpoly (a : Atom) {r : ℂ} (hr : r ∈ partner (orbit a)) (s : ℂ) :
    s ∈ partner (orbit a) ↔ minpoly Ki s = minpoly Ki r := by
  have hint : IsIntegral Ki r := by
    rw [partner_orbit_eq] at hr
    exact isIntegral_of_mem_roots (mOf_odd a).pos (kappa'_pow_four (kappa_pow_four a) _)
      (Npow_pos a).ne' hr
  rw [← galOrbit_partner a hr, mem_galOrbit_iff hint]

theorem mem_selfOrb_iff_minpoly (k : ℕ) (b : Bool) {r : ℂ} (hr : r ∈ selfOrb k b) (s : ℂ) :
    s ∈ selfOrb k b ↔ minpoly Ki s = minpoly Ki r := by
  have hint : IsIntegral Ki r :=
    isIntegral_of_mem_roots (by omega) (kappaS_pow_four b) (by norm_num) hr
  rw [← galOrbit_selfOrb k b hr, mem_galOrbit_iff hint]

end PiFormula
