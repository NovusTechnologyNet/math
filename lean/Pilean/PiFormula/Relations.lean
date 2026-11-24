module

public import Pilean.PiFormula.NewFormula

/-!
# The 13 multiplicative relations (Part III, Step 3, of pi_formula_theorem.md)

With `ζ = ζ_120 = exp(2πi/120)`, `t = 1 + i` and `w_j = 1 - ζ^j / t`, the program
full_class_theorem.py finds 13 independent multiplicative relations `∏ w_j^(e_j) = ζ^m` among
the 24 roots of unity of `R0`. Each is proved here exactly, in the cleared form
`∏_{e_j > 0} (t - ζ^j)^(e_j) · t^(max(0, -∑e)) = ζ^m ∏_{e_j < 0} (t - ζ^j)^(-e_j) · t^(max(0, ∑e))`
(`relation_1` ... `relation_13`; the docstrings give `e` and `∑ e_j Log w_j = c · iπ`, with
`m = 60 c mod 120`).

Every relation involves only 20th roots of unity or only 24th roots of unity, so it is a
polynomial identity in `ζ_20 = ζ^6` modulo `Φ_20` or in `ζ_24 = ζ^5` modulo `Φ_24` (both of
degree 8). The quotients were computed by a script (sympy) and are checked here by
`linear_combination`.

That there are no further relations (rank 11) is proved in `Rank.lean`.
-/

@[expose] public section

open Complex

namespace PiFormula

/-- `ζ_120 = exp(2πi/120)`. -/
noncomputable def ζ120 : ℂ := Complex.exp (2 * Real.pi * I / 120)

theorem ζ120_prim : IsPrimitiveRoot ζ120 120 := Complex.isPrimitiveRoot_exp 120 (by norm_num)

theorem ζ120_pow_30 : ζ120 ^ 30 = I := by
  rw [ζ120, ← Complex.exp_nat_mul]
  rw [show ((30 : ℕ) : ℂ) * (2 * Real.pi * I / 120) = (Real.pi / 2 : ℝ) * I by push_cast; ring,
    Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

/-- `ζ_20 = ζ_120^6`. -/
noncomputable def z20 : ℂ := ζ120 ^ 6

/-- `ζ_24 = ζ_120^5`. -/
noncomputable def z24 : ℂ := ζ120 ^ 5

theorem z20_prim : IsPrimitiveRoot z20 20 := ζ120_prim.pow (by norm_num) (by norm_num)

theorem z24_prim : IsPrimitiveRoot z24 24 := ζ120_prim.pow (by norm_num) (by norm_num)

theorem I_z20 : I = z20 ^ 5 := by rw [z20, ← pow_mul, ζ120_pow_30]

theorem I_z24 : I = z24 ^ 6 := by rw [z24, ← pow_mul, ζ120_pow_30]

/-- `Φ_20(ζ_20) = 0`. -/
theorem cyc20 : z20 ^ 8 - z20 ^ 6 + z20 ^ 4 - z20 ^ 2 + 1 = 0 := by
  have h20 := z20_prim.pow_eq_one
  have hne : z20 ^ 10 ≠ 1 := z20_prim.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have h10 : z20 ^ 10 = -1 := by
    have : (z20 ^ 10 - 1) * (z20 ^ 10 + 1) = 0 := by linear_combination h20
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hne
    · linear_combination h
  have h5 := (z20_prim.pow (by norm_num) (show 20 = 4 * 5 by norm_num)).geom_sum_eq_zero
    (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h5
  linear_combination h5 - (z20 ^ 2 + z20 ^ 6) * h10

/-- `Φ_24(ζ_24) = 0`. -/
theorem cyc24 : z24 ^ 8 - z24 ^ 4 + 1 = 0 := by
  have h24 := z24_prim.pow_eq_one
  have hne : z24 ^ 12 ≠ 1 := z24_prim.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have h12 : z24 ^ 12 = -1 := by
    have : (z24 ^ 12 - 1) * (z24 ^ 12 + 1) = 0 := by linear_combination h24
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hne
    · linear_combination h
  have h3 := (z24_prim.pow (by norm_num) (show 24 = 8 * 3 by norm_num)).geom_sum_eq_zero
    (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h3
  linear_combination h3 - z24 ^ 4 * h12

/-- Relation 1: `-1[0] +1[30]`, `∑ e Log w = -1/2 · iπ`. -/
theorem relation_1 :
    (tC - ζ120 ^ 30) =
      ζ120 ^ 90 * (tC - 1) := by
  rw [show ζ120 ^ 30 = z20 ^ 5 by rw [z20, ← pow_mul],
    show ζ120 ^ 90 = z20 ^ 15 by rw [z20, ← pow_mul],
    show tC = 1 + z20 ^ 5 by rw [tC, I_z20]]
  linear_combination (-z20 ^ 12 - z20 ^ 10 + z20 ^ 2 + 1) * cyc20

/-- Relation 2: `-2[0] +1[20] +1[100]`, `∑ e Log w = -1/2 · iπ`. -/
theorem relation_2 :
    (tC - ζ120 ^ 20) * (tC - ζ120 ^ 100) =
      ζ120 ^ 90 * (tC - 1) ^ 2 := by
  rw [show ζ120 ^ 20 = z24 ^ 4 by rw [z24, ← pow_mul],
    show ζ120 ^ 90 = z24 ^ 18 by rw [z24, ← pow_mul],
    show ζ120 ^ 100 = z24 ^ 20 by rw [z24, ← pow_mul],
    show tC = 1 + z24 ^ 6 by rw [tC, I_z24]]
  linear_combination (-z24 ^ 22 - 2 * z24 ^ 18 + z24 ^ 16 - z24 ^ 14 + z24 ^ 10 - z24 ^ 8 +
      2 * z24 ^ 6 + 1) * cyc24

/-- Relation 3: `-2[0] +1[15] +1[75]`, `∑ e Log w = -1/2 · iπ`. -/
theorem relation_3 :
    (tC - ζ120 ^ 15) * (tC - ζ120 ^ 75) =
      ζ120 ^ 90 * (tC - 1) ^ 2 := by
  rw [show ζ120 ^ 15 = z24 ^ 3 by rw [z24, ← pow_mul],
    show ζ120 ^ 75 = z24 ^ 15 by rw [z24, ← pow_mul],
    show ζ120 ^ 90 = z24 ^ 18 by rw [z24, ← pow_mul],
    show tC = 1 + z24 ^ 6 by rw [tC, I_z24]]
  linear_combination (-z24 ^ 22 - z24 ^ 18 - z24 ^ 13 + 2 * z24 ^ 10 - z24 ^ 9 - z24 ^ 7 +
      2 * z24 ^ 6 + z24 ^ 4 - z24 ^ 3 + 1) * cyc24

/-- Relation 4: `-3[0] +1[12] +1[36] -1[60] +1[84] +1[108]`, `∑ e Log w = -1/2 · iπ`. -/
theorem relation_4 :
    (tC - ζ120 ^ 12) * (tC - ζ120 ^ 36) * (tC - ζ120 ^ 84) * (tC - ζ120 ^ 108) =
      ζ120 ^ 90 * (tC - 1) ^ 3 * (tC - ζ120 ^ 60) := by
  rw [show ζ120 ^ 12 = z20 ^ 2 by rw [z20, ← pow_mul],
    show ζ120 ^ 36 = z20 ^ 6 by rw [z20, ← pow_mul],
    show ζ120 ^ 60 = z20 ^ 10 by rw [z20, ← pow_mul],
    show ζ120 ^ 84 = z20 ^ 14 by rw [z20, ← pow_mul],
    show ζ120 ^ 90 = z20 ^ 15 by rw [z20, ← pow_mul],
    show ζ120 ^ 108 = z20 ^ 18 by rw [z20, ← pow_mul],
    show tC = 1 + z20 ^ 5 by rw [tC, I_z20]]
  linear_combination (-z20 ^ 35 + z20 ^ 34 - z20 ^ 33 + 3 * z20 ^ 32 - z20 ^ 31 + z20 ^ 30 +
      z20 ^ 29 - z20 ^ 28 + z20 ^ 27 - z20 ^ 25 - z20 ^ 23 - z20 ^ 22 + z20 ^ 21 - 3 * z20 ^ 20 -
      z20 ^ 19 - 2 * z20 ^ 18 + 2 * z20 ^ 17 - 2 * z20 ^ 16 + 2 * z20 ^ 15 - 3 * z20 ^ 14 -
      z20 ^ 13 + 3 * z20 ^ 12 - 3 * z20 ^ 11 + 6 * z20 ^ 10 - 3 * z20 ^ 9 + z20 ^ 7 - z20 ^ 6 +
      4 * z20 ^ 5 - z20 ^ 4 + 1) * cyc20

/-- Relation 5: `+1[10] -1[20]`, `∑ e Log w = 1/3 · iπ`. -/
theorem relation_5 :
    (tC - ζ120 ^ 10) =
      ζ120 ^ 20 * (tC - ζ120 ^ 20) := by
  rw [show ζ120 ^ 10 = z24 ^ 2 by rw [z24, ← pow_mul],
    show ζ120 ^ 20 = z24 ^ 4 by rw [z24, ← pow_mul],
    show tC = 1 + z24 ^ 6 by rw [tC, I_z24]]
  linear_combination (-z24 ^ 2 + 1) * cyc24

/-- Relation 6: `-2[0] +1[20] +1[50]`, `∑ e Log w = -5/6 · iπ`. -/
theorem relation_6 :
    (tC - ζ120 ^ 20) * (tC - ζ120 ^ 50) =
      ζ120 ^ 70 * (tC - 1) ^ 2 := by
  rw [show ζ120 ^ 20 = z24 ^ 4 by rw [z24, ← pow_mul],
    show ζ120 ^ 50 = z24 ^ 10 by rw [z24, ← pow_mul],
    show ζ120 ^ 70 = z24 ^ 14 by rw [z24, ← pow_mul],
    show tC = 1 + z24 ^ 6 by rw [tC, I_z24]]
  linear_combination (-z24 ^ 18 - z24 ^ 14 - z24 ^ 8 + 2 * z24 ^ 6 + 1) * cyc24

/-- Relation 7: `-4[12] +4[18] +1[60] -1[90]`, `∑ e Log w = -11/10 · iπ`. -/
theorem relation_7 :
    (tC - ζ120 ^ 18) ^ 4 * (tC - ζ120 ^ 60) =
      ζ120 ^ 54 * (tC - ζ120 ^ 12) ^ 4 * (tC - ζ120 ^ 90) := by
  rw [show ζ120 ^ 12 = z20 ^ 2 by rw [z20, ← pow_mul],
    show ζ120 ^ 18 = z20 ^ 3 by rw [z20, ← pow_mul],
    show ζ120 ^ 54 = z20 ^ 9 by rw [z20, ← pow_mul],
    show ζ120 ^ 60 = z20 ^ 10 by rw [z20, ← pow_mul],
    show ζ120 ^ 90 = z20 ^ 15 by rw [z20, ← pow_mul],
    show tC = 1 + z20 ^ 5 by rw [tC, I_z20]]
  linear_combination (z20 ^ 36 + z20 ^ 34 - 4 * z20 ^ 33 + 6 * z20 ^ 30 + 4 * z20 ^ 29 -
      6 * z20 ^ 28 - 4 * z20 ^ 27 - 8 * z20 ^ 26 + 8 * z20 ^ 25 + 5 * z20 ^ 24 + 8 * z20 ^ 23 -
      4 * z20 ^ 22 - 9 * z20 ^ 21 - 7 * z20 ^ 20 - 5 * z20 ^ 19 + 16 * z20 ^ 18 + 5 * z20 ^ 17 +
      9 * z20 ^ 16 - 17 * z20 ^ 15 - 12 * z20 ^ 14 + 9 * z20 ^ 12 + 17 * z20 ^ 11 - 8 * z20 ^ 10 -
      5 * z20 ^ 9 - 10 * z20 ^ 8 + 5 * z20 ^ 7 + 6 * z20 ^ 6 + z20 ^ 5 - 4 * z20 ^ 3 + z20 ^ 2 +
      1) * cyc20

/-- Relation 8: `-12[0] +4[12] +4[36] +4[42] -3[60] +4[84] -1[90]`, `∑ e Log w = -39/10 · iπ`. -/
theorem relation_8 :
    (tC - ζ120 ^ 12) ^ 4 * (tC - ζ120 ^ 36) ^ 4 * (tC - ζ120 ^ 42) ^ 4 * (tC - ζ120 ^ 84) ^ 4 =
      ζ120 ^ 6 * (tC - 1) ^ 12 * (tC - ζ120 ^ 60) ^ 3 * (tC - ζ120 ^ 90) := by
  rw [show ζ120 ^ 6 = z20 from rfl,
    show ζ120 ^ 12 = z20 ^ 2 by rw [z20, ← pow_mul],
    show ζ120 ^ 36 = z20 ^ 6 by rw [z20, ← pow_mul],
    show ζ120 ^ 42 = z20 ^ 7 by rw [z20, ← pow_mul],
    show ζ120 ^ 60 = z20 ^ 10 by rw [z20, ← pow_mul],
    show ζ120 ^ 84 = z20 ^ 14 by rw [z20, ← pow_mul],
    show ζ120 ^ 90 = z20 ^ 15 by rw [z20, ← pow_mul],
    show tC = 1 + z20 ^ 5 by rw [tC, I_z20]]
  linear_combination (z20 ^ 120 - 4 * z20 ^ 119 + 3 * z20 ^ 118 + 4 * z20 ^ 117 + z20 ^ 116 -
      4 * z20 ^ 115 - 35 * z20 ^ 114 + 40 * z20 ^ 113 + 49 * z20 ^ 112 - 44 * z20 ^ 111 -
      44 * z20 ^ 110 - 120 * z20 ^ 109 + 231 * z20 ^ 108 + 176 * z20 ^ 107 - 339 * z20 ^ 106 -
      36 * z20 ^ 105 - 210 * z20 ^ 104 + 536 * z20 ^ 103 + 418 * z20 ^ 102 - 1032 * z20 ^ 101 +
      458 * z20 ^ 100 - 564 * z20 ^ 99 + 256 * z20 ^ 98 + 1528 * z20 ^ 97 - 1777 * z20 ^ 96 +
      1372 * z20 ^ 95 - 1987 * z20 ^ 94 - 1261 * z20 ^ 93 + 5510 * z20 ^ 92 - 2881 * z20 ^ 91 +
      1282 * z20 ^ 90 - 3492 * z20 ^ 89 - 4092 * z20 ^ 88 + 12600 * z20 ^ 87 - 5707 * z20 ^ 86 +
      228 * z20 ^ 85 - 1003 * z20 ^ 84 - 10946 * z20 ^ 83 + 19100 * z20 ^ 82 - 7714 * z20 ^ 81 +
      612 * z20 ^ 80 + 6856 * z20 ^ 79 - 26573 * z20 ^ 78 + 23068 * z20 ^ 77 - 1988 * z20 ^ 76 -
      32 * z20 ^ 75 + 16441 * z20 ^ 74 - 47114 * z20 ^ 73 + 25775 * z20 ^ 72 + 11226 * z20 ^ 71 -
      8919 * z20 ^ 70 + 28352 * z20 ^ 69 - 59163 * z20 ^ 68 + 21936 * z20 ^ 67 + 22414 * z20 ^ 66 -
      23620 * z20 ^ 65 + 46952 * z20 ^ 64 - 56981 * z20 ^ 63 + 2668 * z20 ^ 62 + 28391 * z20 ^ 61 -
      31643 * z20 ^ 60 + 65152 * z20 ^ 59 - 47165 * z20 ^ 58 - 25960 * z20 ^ 57 + 34656 * z20 ^ 56 -
      29704 * z20 ^ 55 + 67516 * z20 ^ 54 - 33208 * z20 ^ 53 - 44891 * z20 ^ 52 + 39408 * z20 ^ 51 -
      26524 * z20 ^ 50 + 52328 * z20 ^ 49 - 13012 * z20 ^ 48 - 45812 * z20 ^ 47 + 33673 * z20 ^ 46 -
      25464 * z20 ^ 45 + 33567 * z20 ^ 44 + 8224 * z20 ^ 43 - 37128 * z20 ^ 42 + 17996 * z20 ^ 41 -
      21190 * z20 ^ 40 + 21364 * z20 ^ 39 + 19404 * z20 ^ 38 - 27844 * z20 ^ 37 + 3486 * z20 ^ 36 -
      12204 * z20 ^ 35 + 14336 * z20 ^ 34 + 17540 * z20 ^ 33 - 19388 * z20 ^ 32 - 2672 * z20 ^ 31 -
      3746 * z20 ^ 30 + 8656 * z20 ^ 29 + 9835 * z20 ^ 28 - 11336 * z20 ^ 27 - 2617 * z20 ^ 26 +
      304 * z20 ^ 25 + 4017 * z20 ^ 24 + 3668 * z20 ^ 23 - 5079 * z20 ^ 22 - 1112 * z20 ^ 21 +
      888 * z20 ^ 20 + 1316 * z20 ^ 19 + 897 * z20 ^ 18 - 1640 * z20 ^ 17 - 270 * z20 ^ 16 +
      432 * z20 ^ 15 + 284 * z20 ^ 14 + 132 * z20 ^ 13 - 359 * z20 ^ 12 - 36 * z20 ^ 11 +
      112 * z20 ^ 10 + 36 * z20 ^ 9 + 9 * z20 ^ 8 - 48 * z20 ^ 7 - 2 * z20 ^ 6 + 16 * z20 ^ 5 +
      2 * z20 ^ 4 - 3 * z20 ^ 2 + 1) * cyc20

/-- Relation 9: `+1[60] +4[66] -4[84] -1[90]`, `∑ e Log w = -7/10 · iπ`. -/
theorem relation_9 :
    (tC - ζ120 ^ 60) * (tC - ζ120 ^ 66) ^ 4 =
      ζ120 ^ 78 * (tC - ζ120 ^ 84) ^ 4 * (tC - ζ120 ^ 90) := by
  rw [show ζ120 ^ 60 = z20 ^ 10 by rw [z20, ← pow_mul],
    show ζ120 ^ 66 = z20 ^ 11 by rw [z20, ← pow_mul],
    show ζ120 ^ 78 = z20 ^ 13 by rw [z20, ← pow_mul],
    show ζ120 ^ 84 = z20 ^ 14 by rw [z20, ← pow_mul],
    show ζ120 ^ 90 = z20 ^ 15 by rw [z20, ← pow_mul],
    show tC = 1 + z20 ^ 5 by rw [tC, I_z20]]
  linear_combination (z20 ^ 76 + z20 ^ 74 - 4 * z20 ^ 67 - 2 * z20 ^ 66 - 4 * z20 ^ 65 -
      2 * z20 ^ 64 - 4 * z20 ^ 62 - z20 ^ 61 - 4 * z20 ^ 60 - z20 ^ 59 + 6 * z20 ^ 58 +
      8 * z20 ^ 57 + 8 * z20 ^ 56 + 8 * z20 ^ 55 + 2 * z20 ^ 54 + 12 * z20 ^ 53 + 12 * z20 ^ 52 +
      13 * z20 ^ 51 + 12 * z20 ^ 50 - 3 * z20 ^ 49 - 6 * z20 ^ 48 - 8 * z20 ^ 47 - 9 * z20 ^ 46 -
      4 * z20 ^ 45 - 15 * z20 ^ 44 - 30 * z20 ^ 43 - 24 * z20 ^ 42 - 30 * z20 ^ 41 - 7 * z20 ^ 40 -
      4 * z20 ^ 39 - 7 * z20 ^ 38 - 8 * z20 ^ 36 + 8 * z20 ^ 35 + 22 * z20 ^ 34 + 28 * z20 ^ 33 +
      30 * z20 ^ 32 + 24 * z20 ^ 31 + 4 * z20 ^ 30 + 22 * z20 ^ 29 + 8 * z20 ^ 28 + 18 * z20 ^ 27 +
      12 * z20 ^ 26 - 13 * z20 ^ 25 + 6 * z20 ^ 24 - 25 * z20 ^ 23 - 3 * z20 ^ 22 - 16 * z20 ^ 21 -
      14 * z20 ^ 20 - 21 * z20 ^ 18 + z20 ^ 17 - 16 * z20 ^ 16 - 5 * z20 ^ 13 + 8 * z20 ^ 12 -
      4 * z20 ^ 11 + 8 * z20 ^ 10 + 5 * z20 ^ 7 + 5 * z20 ^ 5 + z20 ^ 2 + 1) * cyc20

/-- Relation 10: `-4[36] +1[60] -1[90] +4[114]`, `∑ e Log w = 17/10 · iπ`. -/
theorem relation_10 :
    (tC - ζ120 ^ 60) * (tC - ζ120 ^ 114) ^ 4 =
      ζ120 ^ 102 * (tC - ζ120 ^ 36) ^ 4 * (tC - ζ120 ^ 90) := by
  rw [show ζ120 ^ 36 = z20 ^ 6 by rw [z20, ← pow_mul],
    show ζ120 ^ 60 = z20 ^ 10 by rw [z20, ← pow_mul],
    show ζ120 ^ 90 = z20 ^ 15 by rw [z20, ← pow_mul],
    show ζ120 ^ 102 = z20 ^ 17 by rw [z20, ← pow_mul],
    show ζ120 ^ 114 = z20 ^ 19 by rw [z20, ← pow_mul],
    show tC = 1 + z20 ^ 5 by rw [tC, I_z20]]
  linear_combination (-z20 ^ 78 - z20 ^ 76 + z20 ^ 73 + z20 ^ 71 + 2 * z20 ^ 68 + 2 * z20 ^ 66 +
      4 * z20 ^ 64 - z20 ^ 63 + 4 * z20 ^ 62 - z20 ^ 61 - 2 * z20 ^ 58 - 2 * z20 ^ 56 -
      12 * z20 ^ 54 + z20 ^ 53 - 12 * z20 ^ 52 + z20 ^ 51 - 6 * z20 ^ 50 - 4 * z20 ^ 49 -
      3 * z20 ^ 48 - 8 * z20 ^ 47 + 9 * z20 ^ 46 - 14 * z20 ^ 45 + 19 * z20 ^ 44 - 11 * z20 ^ 43 +
      9 * z20 ^ 42 + 11 * z20 ^ 41 + 2 * z20 ^ 40 + 20 * z20 ^ 39 + 2 * z20 ^ 38 + 16 * z20 ^ 37 -
      6 * z20 ^ 36 + 28 * z20 ^ 35 - 10 * z20 ^ 34 + 20 * z20 ^ 33 + 4 * z20 ^ 32 - 22 * z20 ^ 31 +
      24 * z20 ^ 30 - 31 * z20 ^ 29 + 16 * z20 ^ 28 - 13 * z20 ^ 27 - 16 * z20 ^ 26 -
      21 * z20 ^ 24 + 4 * z20 ^ 23 - 14 * z20 ^ 22 - 4 * z20 ^ 21 - 9 * z20 ^ 20 - 5 * z20 ^ 19 +
      z20 ^ 15 + 8 * z20 ^ 12 + 8 * z20 ^ 10 + 5 * z20 ^ 7 + 5 * z20 ^ 5 + z20 ^ 2 + 1) * cyc20

/-- Relation 11: `-2[5] +2[25] +1[45] -1[105]`, `∑ e Log w = -4/3 · iπ`. -/
theorem relation_11 :
    (tC - ζ120 ^ 25) ^ 2 * (tC - ζ120 ^ 45) =
      ζ120 ^ 40 * (tC - ζ120 ^ 5) ^ 2 * (tC - ζ120 ^ 105) := by
  rw [show ζ120 ^ 5 = z24 from rfl,
    show ζ120 ^ 25 = z24 ^ 5 by rw [z24, ← pow_mul],
    show ζ120 ^ 40 = z24 ^ 8 by rw [z24, ← pow_mul],
    show ζ120 ^ 45 = z24 ^ 9 by rw [z24, ← pow_mul],
    show ζ120 ^ 105 = z24 ^ 21 by rw [z24, ← pow_mul],
    show tC = 1 + z24 ^ 6 by rw [tC, I_z24]]
  linear_combination (z24 ^ 33 + z24 ^ 29 - 2 * z24 ^ 28 + 2 * z24 ^ 27 - 2 * z24 ^ 24 +
      3 * z24 ^ 23 - 2 * z24 ^ 22 + z24 ^ 19 - 3 * z24 ^ 18 + 2 * z24 ^ 16 - 2 * z24 ^ 15 -
      z24 ^ 14 + z24 ^ 13 + z24 ^ 12 - 4 * z24 ^ 11 + 3 * z24 ^ 10 - z24 ^ 9 - z24 ^ 8 +
      3 * z24 ^ 6 - 2 * z24 ^ 5 + z24 ^ 4 + 1) * cyc24

/-- Relation 12: `-2[0] +2[5] -1[45] +2[65] -1[105]`, `∑ e Log w = -1/6 · iπ`. -/
theorem relation_12 :
    (tC - ζ120 ^ 5) ^ 2 * (tC - ζ120 ^ 65) ^ 2 =
      ζ120 ^ 110 * (tC - 1) ^ 2 * (tC - ζ120 ^ 45) * (tC - ζ120 ^ 105) := by
  rw [show ζ120 ^ 5 = z24 from rfl,
    show ζ120 ^ 45 = z24 ^ 9 by rw [z24, ← pow_mul],
    show ζ120 ^ 65 = z24 ^ 13 by rw [z24, ← pow_mul],
    show ζ120 ^ 105 = z24 ^ 21 by rw [z24, ← pow_mul],
    show ζ120 ^ 110 = z24 ^ 22 by rw [z24, ← pow_mul],
    show tC = 1 + z24 ^ 6 by rw [tC, I_z24]]
  linear_combination (-z24 ^ 56 + z24 ^ 53 - z24 ^ 52 + z24 ^ 49 + z24 ^ 47 + z24 ^ 44 + z24 ^ 43 +
      z24 ^ 40 - z24 ^ 38 - z24 ^ 34 - 3 * z24 ^ 32 + z24 ^ 30 - 3 * z24 ^ 28 + z24 ^ 26 -
      2 * z24 ^ 25 + 2 * z24 ^ 24 - 2 * z24 ^ 23 - 2 * z24 ^ 21 + 6 * z24 ^ 20 - 4 * z24 ^ 19 +
      4 * z24 ^ 18 - 6 * z24 ^ 17 + 5 * z24 ^ 16 - 2 * z24 ^ 15 + 4 * z24 ^ 14 - 6 * z24 ^ 13 +
      7 * z24 ^ 12 - 6 * z24 ^ 11 + 4 * z24 ^ 10 + 2 * z24 ^ 8 - 6 * z24 ^ 7 + 5 * z24 ^ 6 -
      2 * z24 ^ 5 + z24 ^ 4 + z24 ^ 2 - 2 * z24 + 1) * cyc24

/-- Relation 13: `-1[0] +1[5] -1[45] +1[85]`, `∑ e Log w = 1/4 · iπ`. -/
theorem relation_13 :
    (tC - ζ120 ^ 5) * (tC - ζ120 ^ 85) =
      ζ120 ^ 15 * (tC - 1) * (tC - ζ120 ^ 45) := by
  rw [show ζ120 ^ 5 = z24 from rfl,
    show ζ120 ^ 15 = z24 ^ 3 by rw [z24, ← pow_mul],
    show ζ120 ^ 45 = z24 ^ 9 by rw [z24, ← pow_mul],
    show ζ120 ^ 85 = z24 ^ 17 by rw [z24, ← pow_mul],
    show tC = 1 + z24 ^ 6 by rw [tC, I_z24]]
  linear_combination (-z24 ^ 15 - z24 ^ 11 + 2 * z24 ^ 10 - z24 ^ 9 - z24 ^ 7 + 2 * z24 ^ 6 -
      z24 ^ 5 + z24 ^ 4 - z24 + 1) * cyc24
end PiFormula
