# Independent reading, batch 1 (nine statements)

Source read: `view_batch1.txt` only, plus general Mathlib/core knowledge. Notation: for a real number x, `⌊k/2⌋` is the natural-number floor division `k / 2`; `v_p` is `padicValNat p`.

## Summary table

| Theorem | Plain statement (one sentence) | Confidence |
|---|---|---|
| `PiFormula.theoremA` | If a finite rational combination of arctan(1/2^m) (m ≥ 1) and arctan(1/(2^m−1)) (m ≥ 1) equals qπ with q rational, then only arctan(1/2), arctan 1, arctan(1/3), arctan(1/7) occur, their coefficients satisfy b₁ − a₂ + 2a₃ = 0, and q = (a₁ + a₂ − a₃)/4. | high |
| `Unconditional.theoremC` | For every N > 0 divisible by 120, every N-periodic rational sequence ρ with Σ_{k≥1} ρ_k/(2^{⌊k/2⌋} k) = (real algebraic)·π is in fact 120-periodic; the Q-space of such ρ has dimension 13, and the subspace where the multiplier is rational has dimension 8. | high |
| `BaseB.no_pi_bailey` | If b ≥ 2 is not a power of 2, B ≥ 1, N ≥ 1, and Σ_{j≥0} b^{−Bj} Σ_{i=0}^{N−1} c_i/(Nj+i+1) = qπ with rational c_i and rational q, then q = 0. | high |
| `RatBase.hasRelation_iff` | For coprime 0 < q < p, some nonzero periodic rational ρ has Σ_{k≥1} ρ_k (q/p)^{⌊k/2⌋}/k equal to (real algebraic)·π (zero allowed) if and only if (p,q) is one of (2,1), (3,1), (4,1), (3,2), (4,3). | high |
| `Compendium.formula_29` | π² = Σ_{j≥0} 16^{−j} [16/(8j+1)² − 16/(8j+2)² − 8/(8j+3)² − 16/(8j+4)² − 4/(8j+5)² − 4/(8j+6)² + 2/(8j+7)²] (the series is summable). | high |
| `Erdos.erdos_pm_one_nat` | For odd non-square q, no q-periodic f: ℕ → ℤ with f = 0 on multiples of q and f = ±1 elsewhere has partial sums Σ_{n<N} f(n)/n tending to 0. | high |
| `Erdos.erdos_pm_one_lt_11025` | The same conclusion for every q with 2 ≤ q < 11025 (any parity, squares included). | high |
| `Erdos.okadaCriterionGeneral` | For q ≥ 1 and rational-valued f on Z/qZ: Σ_{n≥1} f(n mod q)/n converges to 0 iff (A) Σ_{m ≥ 1, every prime of m divides q} f(am)/m = 0 for every unit a mod q, and (B) Σ_{r=1}^{q} f(r)·λ_p(r) = 0 for every prime p | q, with λ_p(r) = v_p(r) if v_p(r) < v_p(q), else v_p(q) + 1/(p−1). | high (medium on whether every edge of the tsum was handled; see doubts) |
| `Erdos.exists_oddValued_sumIsZero_iff` | For odd q > 1: there is f: Z/qZ → ℚ with f(0) = 0, f(r) a rational with odd numerator and odd denominator for every r ≠ 0, and Σ f(n)/n converging to 0, iff q is a perfect square. | high |

---

## 1. `PiFormula.theoremA`

**Plain statement.** For all finitely supported b, a: ℕ → ℚ and all q ∈ ℚ, with b(0) = 0 and a(0) = 0: if

  Σ_{m} b(m)·arctan(1/2^m) + Σ_{m} a(m)·arctan(1/(2^m − 1)) = q·π   (in ℝ; the sums are finite, over the supports)

then
- b(m) = 0 for all m ≥ 2,
- a(m) = 0 for all m ≥ 4,
- b(1) − a(2) + 2a(3) = 0,
- q = (a(1) + a(2) − a(3))/4.

So the only arctangents that can appear are arctan(1/2) (b₁), arctan(1) = π/4 (a₁), arctan(1/3) (a₂), arctan(1/7) (a₃).

**Conventions.**
- `Finsupp.sum b g` = Σ over the support of b of g(m, b(m)); since g(m,0) = 0 this is the same as a sum over any finite superset. Arguments are real: `1 / 2 ^ m` and `1 / (2 ^ m - 1)` are real expressions.
- At m = 0: arctan(1/2⁰) = arctan 1 = π/4, which would trivially produce π; the hypothesis b(0) = 0 removes it. arctan(1/(2⁰ − 1)) = arctan(1/0) = arctan 0 = 0 by Lean's division by zero, so the a(0) term is 0 anyway; the hypothesis a(0) = 0 merely normalises the otherwise unconstrained (and invisible) coefficient. Without it the conclusion would still not mention a(0), so it costs nothing.
- The two families never share an argument for m ≥ 1 (2^m = 2^n − 1 only for m = 0, n = 1), so the coefficients are not ambiguous.

**Arithmetic check.** Using arctan(1/3) = π/4 − arctan(1/2) and arctan(1/7) = 2 arctan(1/2) − π/4, the value of the allowed combination is arctan(1/2)·(b₁ − a₂ + 2a₃) + (π/4)(a₁ + a₂ − a₃). The conclusion is exactly the statement that this equals qπ only when the arctan(1/2) coefficient vanishes — consistent.

**Edge cases / vacuity.** Hypotheses satisfiable (e.g. a₁ = 4, q = 1). Not vacuous. b = a = 0 gives q = 0, fine.

**What it does not say.** Only the necessary direction; the converse (every coefficient vector satisfying the two linear conditions gives qπ) is true by the identities above but is not stated. Only rational coefficients and rational multiples of π; nothing about algebraic multipliers or other arctangent arguments.

**Doubts.** None.

---

## 2. `PiFormula.Unconditional.theoremC`

**Plain statement.** Let N be a natural number with N > 0 and 120 | N. Define, for ρ: ℕ → ℚ, the real terms t_k(ρ) = ρ(k) / 2^{⌊k/2⌋} / k. Let

- algSpace N = { ρ : ρ(k+N) = ρ(k) for all k ≥ 0, and ∃ γ ∈ ℝ algebraic over ℚ with Σ_k t_k(ρ) = γπ (HasSum) },
- ratSpace N = the same with "∃ q ∈ ℚ, Σ t_k(ρ) = qπ".

Then (i) every ρ ∈ algSpace N satisfies ρ(k+120) = ρ(k) for all k; (ii) dim_ℚ algSpace N = 13; (iii) dim_ℚ ratSpace N = 8.

**Conventions.**
- `k / 2` is natural floor division, exponent of the real 2: t_k = ρ_k/(2^{⌊k/2⌋}·k). So t₁ = ρ₁, t₂ = ρ₂/4, t₃ = ρ₃/6, t₄ = ρ₄/16, t₅ = ρ₅/20, … (pairs k = 2j+1, 2j+2 share the factor 2^{−j}).
- k = 0: t₀ = ρ₀/1/0 = 0 by division by zero, so ρ(0) never enters the sum. It is not a free coordinate though: periodicity at k = 0 forces ρ(0) = ρ(N), so the spaces are not inflated by a dummy coordinate.
- HasSum is unconditional summability; for periodic ρ the terms decay geometrically, so it coincides with ordinary convergence here.
- `Module.finrank` is 0 for infinite-dimensional spaces; asserting 13 and 8 therefore also asserts finite-dimensionality.
- γ algebraic includes γ = 0, so algSpace contains all "zero relations" (ρ with sum 0); likewise q = 0 in ratSpace.
- Periodicity is for ℕ-indexed sequences starting at k = 0.

**Edge cases / vacuity.** N = 0 is excluded by 0 < N (with N = 0 periodicity would be vacuous and the space infinite-dimensional, finrank 0). By (i) the spaces are the same for all admissible N, i.e. effectively the N = 120 spaces. Statement not vacuous.

**What it does not say.** Nothing about periods N not divisible by 120 (although (i) suggests those spaces are subspaces of the 120 one, this is not stated for them). It gives dimensions but not explicit bases, and does not say which ρ give γ ≠ 0 (i.e. it doesn't separate π-formulas from zero relations). Algebraic γ, not algebraic coefficients ρ.

**Doubts.** None from the text.

---

## 3. `PiFormula.BaseB.no_pi_bailey`

**Plain statement.** Let b, B, N ∈ ℕ with b ≥ 2, b ≠ 2^k for every k ∈ ℕ, B ≥ 1, N ≥ 1. For every c: {0,…,N−1} → ℚ and every q ∈ ℚ, if

  Σ_{j=0}^{∞} ( Σ_{i=0}^{N−1} c_i / (b^{Bj} (Nj + i + 1)) ) = qπ   (HasSum over j ∈ ℕ)

then q = 0. Equivalently Σ_{k≥1} c_{(k−1) mod N} / (b^{B⌊(k−1)/N⌋} k) is never a nonzero rational multiple of π.

For N = 2: block j = b^{−Bj}[c₀/(2j+1) + c₁/(2j+2)].

**Conventions.** Denominators Nj+i+1 ≥ 1, computed in ℕ then cast, no division by zero. j starts at 0. HasSum over blocks (each block a finite sum); the series converges absolutely since b^B ≥ 2, so HasSum is not a restriction. Only b^B matters as base; b^B is a power of 2 iff b is.

**Edge cases.** b = 3, 5, 6, 7, 10, … included; b = 4, 8, 16 excluded. c = 0 gives q = 0 trivially. Not vacuous.

**What it does not say.** Only rational multiples of π (not algebraic multiples, not π·√3 etc.); degree 1 only (denominators to the first power); only this block shape (numerators c_i depend on i only, no polynomial-in-j numerators). It does not say anything about a zero value.

**Doubts.** None.

---

## 4. `PiFormula.RatBase.hasRelation_iff`

**Plain statement.** For natural p, q with 0 < q < p and gcd(p,q) = 1:

  [∃ N ≥ 1, ∃ ρ: ℕ → ℚ, N-periodic, ρ not identically 0, ∃ γ ∈ ℝ algebraic over ℚ, Σ_{k} ρ(k)(q/p)^{⌊k/2⌋}/k = γπ (HasSum)]
  ⟺ (p,q) ∈ {(2,1), (3,1), (4,1), (3,2), (4,3)}.

**Conventions.**
- (q/p) is real division, exponent ⌊k/2⌋ (natural floor); term at k = 0 is 0 (division by zero). The base-2 sequence of Theorem C is the case (p,q) = (2,1).
- ρ ≠ 0 means as a function ℕ → ℚ. Since ρ(0) = ρ(N), a ρ nonzero only "at 0" is impossible; so ρ ≠ 0 forces some ρ_k ≠ 0 with k ≥ 1. Good: the trivial witness ρ = δ₀ is ruled out.
- γ = 0 is allowed. So "HasRelation" means "a nonzero periodic ρ whose series is an algebraic multiple of π, possibly zero". A true HasRelation could be witnessed by a zero relation alone; it does not assert a formula for π with γ ≠ 0 exists. Conversely, the "⟹" direction is strong: for non-exceptional pairs there is not even a zero relation.
- 0 < q < p makes q/p ∈ (0,1), so the series converges absolutely; HasSum is not a restriction.

**Edge cases.** All five exceptional pairs satisfy the hypotheses. Pairs with gcd > 1 or q ≥ p are outside the statement. (p,q) = (4,1) corresponds to x = 1/4 rather than "base 4" in the sense b^{−k}.

**What it does not say.** Does not say for exceptional pairs that a γ ≠ 0 relation exists (that π itself has a formula), nor dimensions; does not cover q/p ≥ 1 or non-reduced fractions (harmless), or other exponent patterns than ⌊k/2⌋.

**Doubts.** None from the text; the question for the authors is whether their prose claim is "relations (including zero relations)" or "formulas for π" — the formal text is the former.

---

## 5. `PiFormula.Compendium.formula_29`

**Plain statement.** Unfolding `BaileyFormulaDeg x c s b B N a` = ∃ S, HasSum (baileyBlockDeg s b B N a) S ∧ x = c·S, with x = π², c = 1, s = 2, b = 16, B = 1, N = 8, a = (16, −16, −8, −16, −4, −4, 2, 0):

  π² = Σ_{j≥0} 16^{−j} [16/(8j+1)² − 16/(8j+2)² − 8/(8j+3)² − 16/(8j+4)² − 4/(8j+5)² − 4/(8j+6)² + 2/(8j+7)² + 0/(8j+8)²],

with the block series HasSum-summable.

**Conventions.** `![…]` index i ∈ Fin 8 pairs with denominator 8j+i+1 (index 0 ↔ 8j+1, index 7 ↔ 8j+8, coefficient 0). j starts at 0. Argument order of `BaileyFormulaDeg` is (x, c, s, b, B, N, a), so the "1" is the overall factor c and the "2" is the degree s.

**Arithmetic check.** j = 0 block ≈ 16 − 4 − 0.8889 − 1 − 0.16 − 0.1111 + 0.0408 = 9.8808; j = 1 block ≈ −0.01093; total ≈ 9.8699 vs π² ≈ 9.8696, with remaining blocks O(16^{−2}·small). Consistent with factor c = 1 (no hidden 1/8 or similar).

**Edge cases.** None; a concrete identity.

**What it does not say.** Only this identity; nothing general about degree-2 formulas.

**Doubts.** None.

---

## 6. `PiFormula.Erdos.erdos_pm_one_nat`

**Plain statement.** Let q ∈ ℕ be odd and not a perfect square. For every f: ℕ → ℤ with f(n+q) = f(n) for all n, f(n) = 0 whenever q | n, and f(n) ∈ {1, −1} whenever q ∤ n: the sequence N ↦ Σ_{n=0}^{N−1} f(n)/n (real) does not tend to 0.

**Conventions.** n = 0 term: f(0)/0 = 0 (and f(0) = 0 anyway, since q | 0). `Finset.range N` = {0,…,N−1}. Ordinary convergence of partial sums (Tendsto), the right notion for a conditionally convergent series.

**Edge cases.** q = 1 is a square, so excluded; smallest q is 3. The conclusion "does not tend to 0" includes the case where the partial sums diverge: if Σ_{r=1}^{q} f(r) ≠ 0 the partial sums diverge like a multiple of log N and the conclusion is trivial; the content is in the case Σ over a period = 0. Hypotheses are satisfiable.

**What it does not say.** Says the series is not 0, not that it converges; nothing for even q or square odd q (covered for q < 11025 by the next theorem only); only ±1 values (the stronger odd-rational version is theorem 9's ⟹ direction).

**Doubts.** None.

---

## 7. `PiFormula.Erdos.erdos_pm_one_lt_11025`

**Plain statement.** Same as 6 but for every q with 2 ≤ q < 11025, with no parity or square condition.

**Conventions.** As in 6. Note 11025 = 105²; the range includes all even q and the squares 4, 9, 16, …, 104².

**Edge cases.** q = 2: f(odd) = ±1, f(even) = 0; periodic f is ±(1,0,1,0,…) giving partial sums → ±∞, conclusion trivially true. q = 1 is excluded (there f ≡ 0 is forced, sums are 0, and the statement would be false — so the hypothesis 2 ≤ q is necessary).

**What it does not say.** A finite range only; no statement for q ≥ 11025 beyond what theorem 6 gives.

**Doubts.** None.

---

## 8. `PiFormula.Erdos.okadaCriterionGeneral`

**Plain statement.** Let q ≥ 1 and f: Z/qZ → ℚ. Then

  lim_{N→∞} Σ_{n=0}^{N−1} f(n mod q)/n = 0   (in ℝ; ordinary convergence of partial sums)

if and only if both:

(A) for every unit a ∈ (Z/qZ)^×:  Σ_{m ∈ M_q} f(a·m mod q)/m = 0, where M_q = { m ∈ ℕ : m ≥ 1 and every prime factor of m divides q } (written as a `tsum` over ℕ of an `if`);

(B) for every prime p with p | q:  Σ_{r=1}^{q} f(r mod q)·λ_p(r) = 0, where
  λ_p(r) = v_p(r) if v_p(r) < v_p(q), and λ_p(r) = v_p(q) + 1/(p−1) otherwise (in ℚ).

**Conventions.**
- n = 0 term of the partial sum is f(0)/0 = 0. Indices start at 0.
- `ZMod q` for q ≥ 1 is Fin q = Z/qZ (q = 0, which would be ℤ, is excluded). The coercion ℕ → ZMod q is reduction mod q. `IsUnit a` = a coprime to q.
- (A) uses `tsum` (∑'), which in Mathlib is defined to be 0 when the family is not summable. Here the family is summable: |f(am)/m| ≤ max|f|/m and Σ_{m∈M_q} 1/m = Π_{p|q} p/(p−1) < ∞ (finitely many primes). So the tsum is a genuine absolutely convergent sum; no silent zero. The `m ≠ 0` clause is needed because primeFactors 0 = ∅ ⊆ anything; even without it the term would be f(0)/0 = 0.
- (B): r runs over 1..q, so the residue 0 is represented by r = q (never by r = 0), avoiding v_p(0) = 0. For r = q, v_p(r) = v_p(q), so λ_p(q) = v_p(q) + 1/(p−1). p − 1 ≥ 1, no division by zero.
- Values rational only (Okada's theorem in the literature allows algebraic values); the sum notion is Tendsto of partial sums, not HasSum (which would be wrong for a conditionally convergent series).

**Small cases.**
- q = 1: ZMod 1 has one element 0, which is a unit. M_1 = {1}. (A) says f(0) = 0; (B) is vacuous. LHS: Σ_{1≤n<N} f(0)/n → 0 iff f(0) = 0 (harmonic divergence). Consistent, non-vacuous.
- q = 2: M_2 = {1,2,4,…}; (A) for a = 1: f(1) + Σ_{k≥1} f(0)/2^k = f(1) + f(0) = 0. (B) p = 2: λ(1) = 0 (v=0<1), λ(2) = 1 + 1 = 2, so 2f(0) = 0. Together f ≡ 0. LHS: with f(1) = −f(0) = c the series is c·log 2, zero iff c = 0; if f(0)+f(1) ≠ 0 it diverges. Consistent.
- Observe the criterion has no separate "Σ_{r} f(r) = 0" (convergence) condition; (A)∧(B) must imply it (as in q = 2, where (A) gives it). The iff as stated asserts this.

**Edge cases / vacuity.** Not vacuous for any q ≥ 1.

**What it does not say.** Only ℚ-valued f; nothing about the value of the series when nonzero, nor about convergence by itself (LHS is "converges to 0").

**Doubts.** (a) I verified summability of the (A) family by hand, not in Mathlib; if the authors' proof relies on it, it must be a lemma there — fine either way for the meaning, since the family is summable mathematically. (b) Whether the authors' prose says "Okada's theorem for algebraic values": the formal text is rational values only.

---

## 9. `PiFormula.Erdos.exists_oddValued_sumIsZero_iff`

**Plain statement.** Let q be odd with q > 1. Then

  [∃ f: Z/qZ → ℚ with f(0) = 0, and for every r ≠ 0 in Z/qZ, f(r) = u/v in lowest terms with u odd and v odd (v > 0), and lim_{N→∞} Σ_{n<N} f(n mod q)/n = 0]
  ⟺ q is a perfect square (∃ r ∈ ℕ, q = r²).

**Conventions.**
- `IsOddRat x` = Odd x.num ∧ Odd x.den: x is a 2-adic unit (in particular x ≠ 0). Examples: ±1, 3, 1/3, −5/7. It does not mean "odd function" (f(−r) = −f(r)), despite the name "oddValued".
- The condition is imposed on every nonzero residue, including residues not coprime to q (e.g. r = 3 mod 9).
- SumIsZero as in 8 (Tendsto of partial sums; n = 0 term is 0).

**Edge cases.** q = 9, 25, 49, …: the ⟸ direction asserts that some odd-rational-valued f works; such f need not be ±1-valued (and theorem 7 shows for q = 9, 25, … < 11025 that ±1-valued ones do not exist), so there is no contradiction. q = 1 excluded (1 is a square; there f(0) = 0 and no other residue, so f ≡ 0 would trivially work).

**What it does not say.** The ⟸ direction does NOT give a counterexample to the ±1 (Erdős) question for square q; it only gives odd-rational values. The ⟹ direction implies theorem 6 (±1 are odd rationals). Nothing for even q.

**Doubts.** None from the text.

---

## Points for the authors

1. `HasRelation` (theorem 4) and `algSpace` / `ratSpace` (theorem 2, Theorem C) allow γ = 0 / q = 0: "has a relation" can be witnessed by a zero relation alone, so the ⟸ direction of `hasRelation_iff` does not say π (or any nonzero algebraic multiple) has a formula in those five bases. Check the prose says "relation", not "formula for π".
2. In theorem 9, "odd-valued" means 2-adic-unit-valued (odd numerator and denominator), not ±1 and not odd function; the square-q direction does not produce a ±1 example.
3. Silent zero conventions checked and harmless: k = 0 / n = 0 terms vanish by x/0 = 0 (ρ(0) is still tied to ρ(N) by periodicity); arctan(1/(2⁰−1)) = 0; the `tsum` in Okada's condition (A) is a genuinely summable family, so no silent 0; Okada's (B) sums over r = 1..q, avoiding v_p(0). Theorem A's hypothesis b(0) = 0 is essential (arctan 1 = π/4), a(0) = 0 is cosmetic.
