module

public import Pilean.RatBase.LeftoverPrime

/-!
# Rational bases: the twelve triples left over by the size condition

`leftoverGood : LeftoverGood`: at each of the twelve triples `(p, q, m)` of `leftoverTriples`
(file `SmallDefs`), every root of unity `r` with `r²` of order `m` has a good prime in the base
`p/q`. At these triples the size condition `SizeCondR p q m` fails, so the reduction of
`ReductionR` does not apply.

Each triple is an instance of `hasGoodPrimeR_of_primitive` (file `LeftoverPrime`), with a
primitive prime factor `ℓ` of `p^m - q^m`, and a conjugation `ζ ↦ ζ ^ a` of the `N`-th roots of
unity that fixes the roots of order dividing `2m` and changes the sign of `√(pq)`. The square
root is a product of Gauss sums (file `LeftoverConj`), and the sign changes at one odd prime `π`
that divides `p q` to an odd power and does not divide `2m`:

| `(p, q, m)` | `ℓ` | `p q` | `π` | `N` | `a` |
|---|---|---|---|---|---|
| `(5, 2, 3)` | 13 | `2·5` | 5 | 120 | 97 |
| `(5, 2, 14)` | 1597 | `2·5` | 5 | 280 | 57 |
| `(5, 4, 6)` | 7 | `2²·5` | 5 | 60 | 37 |
| `(5, 4, 18)` | 3907 | `2²·5` | 5 | 180 | 37 |
| `(6, 5, 22)` | 23 | `2·(-3)·5·(-1)` | 5 | 1320 | 1057 |
| `(7, 2, 6)` | 13 | `2·(-7)·(-1)` | 7 | 168 | 73 |
| `(7, 3, 10)` | 11 | `(-3)·(-7)` | 7 | 420 | 241 |
| `(7, 5, 6)` | 13 | `5·(-7)·(-1)` | 5 | 420 | 337 |
| `(8, 7, 6)` | 19 | `2²·2·(-7)·(-1)` | 7 | 168 | 73 |
| `(8, 7, 10)` | 661 | `2²·2·(-7)·(-1)` | 7 | 280 | 241 |
| `(11, 7, 6)` | 31 | `(-7)·(-11)` | 7 | 924 | 661 |
| `(11, 10, 6)` | 37 | `2·5·(-11)·(-1)` | 5 | 1320 | 1057 |

Here `a ≡ 1` modulo `N/π` and `a ≡ 2 (mod 5)` or `a ≡ 3 (mod 7)`, a non-residue modulo `π`.
-/

@[expose] public section

open Complex Polynomial

namespace PiFormula

namespace RatBase

/-- The triple `(5, 2, 3)`: `ℓ = 13`. -/
theorem leftover_5_2_3 {r : ℂ} (hr : IsOfFinOrder r) (hord : orderOf (r ^ 2) = 3) :
    HasGoodPrimeR 5 2 r :=
  hasGoodPrimeR_of_primitive (ℓ := 13) (N := 120) (a := 97) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide) (by norm_num)
    (by decide) (by decide) (by decide)
    (fun ζ hζ => ((sqrtConj_two (by norm_num) hζ (by decide) (by decide)).mul
      (sqrtConj_five_flip (by norm_num) hζ (by decide) (by decide))).congr
        (by norm_num) (by norm_num)) hr hord

/-- The triple `(5, 2, 14)`: `ℓ = 1597`. -/
theorem leftover_5_2_14 {r : ℂ} (hr : IsOfFinOrder r) (hord : orderOf (r ^ 2) = 14) :
    HasGoodPrimeR 5 2 r :=
  hasGoodPrimeR_of_primitive (ℓ := 1597) (N := 280) (a := 57) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide) (by norm_num)
    (by decide) (by decide) (by decide)
    (fun ζ hζ => ((sqrtConj_two (by norm_num) hζ (by decide) (by decide)).mul
      (sqrtConj_five_flip (by norm_num) hζ (by decide) (by decide))).congr
        (by norm_num) (by norm_num)) hr hord

/-- The triple `(5, 4, 6)`: `ℓ = 7`. -/
theorem leftover_5_4_6 {r : ℂ} (hr : IsOfFinOrder r) (hord : orderOf (r ^ 2) = 6) :
    HasGoodPrimeR 5 4 r :=
  hasGoodPrimeR_of_primitive (ℓ := 7) (N := 60) (a := 37) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide) (by norm_num)
    (by decide) (by decide) (by decide)
    (fun ζ hζ => ((sqrtConj_sq ζ 37 2).mul
      (sqrtConj_five_flip (by norm_num) hζ (by decide) (by decide))).congr
        (by norm_num) (by norm_num)) hr hord

/-- The triple `(5, 4, 18)`: `ℓ = 3907`. -/
theorem leftover_5_4_18 {r : ℂ} (hr : IsOfFinOrder r) (hord : orderOf (r ^ 2) = 18) :
    HasGoodPrimeR 5 4 r :=
  hasGoodPrimeR_of_primitive (ℓ := 3907) (N := 180) (a := 37) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide) (by norm_num)
    (by decide) (by decide) (by decide)
    (fun ζ hζ => ((sqrtConj_sq ζ 37 2).mul
      (sqrtConj_five_flip (by norm_num) hζ (by decide) (by decide))).congr
        (by norm_num) (by norm_num)) hr hord

/-- The triple `(6, 5, 22)`: `ℓ = 23`. -/
theorem leftover_6_5_22 {r : ℂ} (hr : IsOfFinOrder r) (hord : orderOf (r ^ 2) = 22) :
    HasGoodPrimeR 6 5 r :=
  hasGoodPrimeR_of_primitive (ℓ := 23) (N := 1320) (a := 1057) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide) (by norm_num)
    (by decide) (by decide) (by decide)
    (fun ζ hζ => ((((sqrtConj_two (by norm_num) hζ (by decide) (by decide)).mul
      (sqrtConj_neg_three (by norm_num) hζ (by decide) (by decide))).mul
      (sqrtConj_five_flip (by norm_num) hζ (by decide) (by decide))).mul
      (sqrtConj_neg_one (by norm_num) hζ (by decide) (by decide))).congr
        (by norm_num) (by norm_num)) hr hord

/-- The triple `(7, 2, 6)`: `ℓ = 13`. -/
theorem leftover_7_2_6 {r : ℂ} (hr : IsOfFinOrder r) (hord : orderOf (r ^ 2) = 6) :
    HasGoodPrimeR 7 2 r :=
  hasGoodPrimeR_of_primitive (ℓ := 13) (N := 168) (a := 73) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide) (by norm_num)
    (by decide) (by decide) (by decide)
    (fun ζ hζ => (((sqrtConj_two (by norm_num) hζ (by decide) (by decide)).mul
      (sqrtConj_neg_seven_flip (by norm_num) hζ (by decide) (by decide))).mul
      (sqrtConj_neg_one (by norm_num) hζ (by decide) (by decide))).congr
        (by norm_num) (by norm_num)) hr hord

/-- The triple `(7, 3, 10)`: `ℓ = 11`. -/
theorem leftover_7_3_10 {r : ℂ} (hr : IsOfFinOrder r) (hord : orderOf (r ^ 2) = 10) :
    HasGoodPrimeR 7 3 r :=
  hasGoodPrimeR_of_primitive (ℓ := 11) (N := 420) (a := 241) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide) (by norm_num)
    (by decide) (by decide) (by decide)
    (fun ζ hζ => ((sqrtConj_neg_three (by norm_num) hζ (by decide) (by decide)).mul
      (sqrtConj_neg_seven_flip (by norm_num) hζ (by decide) (by decide))).congr
        (by norm_num) (by norm_num)) hr hord

/-- The triple `(7, 5, 6)`: `ℓ = 13`. -/
theorem leftover_7_5_6 {r : ℂ} (hr : IsOfFinOrder r) (hord : orderOf (r ^ 2) = 6) :
    HasGoodPrimeR 7 5 r :=
  hasGoodPrimeR_of_primitive (ℓ := 13) (N := 420) (a := 337) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide) (by norm_num)
    (by decide) (by decide) (by decide)
    (fun ζ hζ => (((sqrtConj_five_flip (by norm_num) hζ (by decide) (by decide)).mul
      (sqrtConj_neg_seven (by norm_num) hζ (by decide) (by decide))).mul
      (sqrtConj_neg_one (by norm_num) hζ (by decide) (by decide))).congr
        (by norm_num) (by norm_num)) hr hord

/-- The triple `(8, 7, 6)`: `ℓ = 19`. -/
theorem leftover_8_7_6 {r : ℂ} (hr : IsOfFinOrder r) (hord : orderOf (r ^ 2) = 6) :
    HasGoodPrimeR 8 7 r :=
  hasGoodPrimeR_of_primitive (ℓ := 19) (N := 168) (a := 73) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide) (by norm_num)
    (by decide) (by decide) (by decide)
    (fun ζ hζ => ((((sqrtConj_sq ζ 73 2).mul
      (sqrtConj_two (by norm_num) hζ (by decide) (by decide))).mul
      (sqrtConj_neg_seven_flip (by norm_num) hζ (by decide) (by decide))).mul
      (sqrtConj_neg_one (by norm_num) hζ (by decide) (by decide))).congr
        (by norm_num) (by norm_num)) hr hord

/-- The triple `(8, 7, 10)`: `ℓ = 661`. -/
theorem leftover_8_7_10 {r : ℂ} (hr : IsOfFinOrder r) (hord : orderOf (r ^ 2) = 10) :
    HasGoodPrimeR 8 7 r :=
  hasGoodPrimeR_of_primitive (ℓ := 661) (N := 280) (a := 241) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide) (by norm_num)
    (by decide) (by decide) (by decide)
    (fun ζ hζ => ((((sqrtConj_sq ζ 241 2).mul
      (sqrtConj_two (by norm_num) hζ (by decide) (by decide))).mul
      (sqrtConj_neg_seven_flip (by norm_num) hζ (by decide) (by decide))).mul
      (sqrtConj_neg_one (by norm_num) hζ (by decide) (by decide))).congr
        (by norm_num) (by norm_num)) hr hord

/-- The triple `(11, 7, 6)`: `ℓ = 31`. -/
theorem leftover_11_7_6 {r : ℂ} (hr : IsOfFinOrder r) (hord : orderOf (r ^ 2) = 6) :
    HasGoodPrimeR 11 7 r :=
  hasGoodPrimeR_of_primitive (ℓ := 31) (N := 924) (a := 661) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide) (by norm_num)
    (by decide) (by decide) (by decide)
    (fun ζ hζ => ((sqrtConj_neg_seven_flip (by norm_num) hζ (by decide) (by decide)).mul
      (sqrtConj_neg_eleven (by norm_num) hζ (by decide) (by decide))).congr
        (by norm_num) (by norm_num)) hr hord

/-- The triple `(11, 10, 6)`: `ℓ = 37`. -/
theorem leftover_11_10_6 {r : ℂ} (hr : IsOfFinOrder r) (hord : orderOf (r ^ 2) = 6) :
    HasGoodPrimeR 11 10 r :=
  hasGoodPrimeR_of_primitive (ℓ := 37) (N := 1320) (a := 1057) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide) (by norm_num)
    (by decide) (by decide) (by decide)
    (fun ζ hζ => ((((sqrtConj_two (by norm_num) hζ (by decide) (by decide)).mul
      (sqrtConj_five_flip (by norm_num) hζ (by decide) (by decide))).mul
      (sqrtConj_neg_eleven (by norm_num) hζ (by decide) (by decide))).mul
      (sqrtConj_neg_one (by norm_num) hζ (by decide) (by decide))).congr
        (by norm_num) (by norm_num)) hr hord

/-- **The twelve triples.** At each triple `(p, q, m)` of `leftoverTriples`, every root of unity
`r` with `r²` of order `m` has a good prime in the base `p/q`. -/
theorem leftoverGood : LeftoverGood := by
  intro p q m hmem r hr hord
  simp only [leftoverTriples, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
    at hmem
  rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact leftover_5_2_3 hr hord
  · exact leftover_5_2_14 hr hord
  · exact leftover_5_4_6 hr hord
  · exact leftover_5_4_18 hr hord
  · exact leftover_6_5_22 hr hord
  · exact leftover_7_2_6 hr hord
  · exact leftover_7_3_10 hr hord
  · exact leftover_7_5_6 hr hord
  · exact leftover_8_7_6 hr hord
  · exact leftover_8_7_10 hr hord
  · exact leftover_11_7_6 hr hord
  · exact leftover_11_10_6 hr hord

end RatBase

end PiFormula
