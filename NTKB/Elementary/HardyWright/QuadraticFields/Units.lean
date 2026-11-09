/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.QuadraticFields.NormEuclidean

/-!
# Unities of a quadratic field (Hardy–Wright, Theorem 240)

In `k(√m)` (`QuadraticAlgebra ℚ m 0`, integers = elements integral over `ℤ`), a *unity* is an integer
`ε` whose reciprocal is an integer.

* `isUnity_iff_norm` (Theorem 240): the norm of a unity is `±1`, and every integer whose norm is `±1`
  is a unity.
* `ncard_unities_of_neg` (Theorem 240): when `m < 0` there are only finitely many unities: four in
  `k(i)`, six in `k(ρ)` (`m = -3`), and two (`±1`) in every other complex field.
-/

namespace NTKB.HardyWright

open QuadraticAlgebra

variable {m : ℤ}

/-- The unities of `k(√m)`: integers whose reciprocal is an integer. -/
def unities (m : ℤ) : Set (QuadraticAlgebra ℚ m 0) :=
  {ε | IsIntegral ℤ ε ∧ ∃ ε' : QuadraticAlgebra ℚ m 0, IsIntegral ℤ ε' ∧ ε * ε' = 1}

lemma norm_mul_star' (z : QuadraticAlgebra ℚ m 0) :
    z * star z = ((norm z : ℚ) : QuadraticAlgebra ℚ m 0) := by
  rw [← algebraMap_norm_eq_mul_star]; rfl

/-- **Theorem 240.** An integer of `k(√m)` is a unity if and only if its norm is `±1`. -/
@[kb "hardywright2008" "Thm 240, p. 288"]
theorem isUnity_iff_norm {ε : QuadraticAlgebra ℚ m 0} (hε : IsIntegral ℤ ε) :
    ε ∈ unities m ↔ norm ε = 1 ∨ norm ε = -1 := by
  constructor
  · rintro ⟨-, ε', hε', h⟩
    obtain ⟨-, N, hN⟩ := isIntegral_iff_trace_norm.1 hε
    obtain ⟨-, N', hN'⟩ := isIntegral_iff_trace_norm.1 hε'
    have h1 := congrArg QuadraticAlgebra.norm h
    rw [map_mul, map_one, qnorm_eq, qnorm_eq, ← hN, ← hN'] at h1
    have : N * N' = 1 := by exact_mod_cast h1
    rcases Int.eq_one_or_neg_one_of_mul_eq_one this with h2 | h2
    · left; rw [qnorm_eq, ← hN, h2]; rfl
    · right; rw [qnorm_eq, ← hN, h2]; push_cast; rfl
  · intro h
    refine ⟨hε, norm ε • star ε, ?_, ?_⟩
    · obtain ⟨-, N, hN⟩ := isIntegral_iff_trace_norm.1 hε
      have hs : IsIntegral ℤ (star ε) := QuadraticAlgebra.isIntegral_star_iff.2 hε
      have : norm ε = (N : ℚ) := by rw [qnorm_eq, ← hN]
      rw [this, show ((N : ℚ) • star ε) = (N : ℤ) • star ε by rw [← Int.cast_smul_eq_zsmul ℚ]]
      exact hs.zsmul N
    · rw [mul_smul_comm, norm_mul_star']
      rcases h with h | h <;> rw [h] <;> ext <;> simp

/-- A unity of a complex field has norm `1`; in coordinates `ε = (A + B√m)/2` with
`A² - mB² = 4`. -/
lemma unities_coords (hm0 : m < 0) (hm : Squarefree m) {ε : QuadraticAlgebra ℚ m 0}
    (h : ε ∈ unities m) : ∃ A B : ℤ, ε = ⟨A / 2, B / 2⟩ ∧ A ^ 2 - m * B ^ 2 = 4 := by
  obtain ⟨A, B, rfl⟩ := exists_half_of_isIntegral hm h.1
  refine ⟨A, B, rfl, ?_⟩
  have hn := (isUnity_iff_norm h.1).1 h
  rw [qnorm_eq] at hn
  simp only at hn
  have hm' : (m : ℚ) < 0 := by exact_mod_cast hm0
  have : (A : ℚ) ^ 2 - m * B ^ 2 = 4 := by
    rcases hn with hn | hn
    · linear_combination 4 * hn
    · nlinarith [sq_nonneg (A : ℚ), sq_nonneg (B : ℚ)]
  exact_mod_cast this

lemma mem_unities_of_norm_one {ε : QuadraticAlgebra ℚ m 0} (hε : IsIntegral ℤ ε)
    (h : norm ε = 1) : ε ∈ unities m :=
  (isUnity_iff_norm hε).2 (Or.inl h)

/-- **Theorem 240** (the complex fields): `k(i)` has four unities, `k(ρ)` (`m = -3`) six, and every
other complex quadratic field `k(√m)` only the two unities `±1`. -/
@[kb "hardywright2008" "Thm 240, p. 288"]
theorem ncard_unities_of_neg (hm0 : m < 0) (hm : Squarefree m) :
    (unities m).ncard = if m = -1 then 4 else if m = -3 then 6 else 2 := by
  have hint : ∀ x y : ℤ, IsIntegral ℤ (⟨x, y⟩ : QuadraticAlgebra ℚ m 0) := isIntegral_mk_int
  split_ifs with h1 h3
  · subst h1
    have hS : unities (-1) = {⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩} := by
      ext ε
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro h
        obtain ⟨A, B, rfl, hAB⟩ := unities_coords (by norm_num) hm h
        obtain ⟨x, y, hxy⟩ := exists_int_of_isIntegral hm (by norm_num) h.1
        have hx : (A : ℚ) / 2 = x := congrArg QuadraticAlgebra.re hxy
        have hy : (B : ℚ) / 2 = y := congrArg QuadraticAlgebra.im hxy
        have hA : A = 2 * x := by have : (A : ℚ) = 2 * x := by linarith
                                  exact_mod_cast this
        have hB : B = 2 * y := by have : (B : ℚ) = 2 * y := by linarith
                                  exact_mod_cast this
        subst hA hB
        have h4 : x ^ 2 + y ^ 2 = 1 := by nlinarith
        have hx1 : -1 ≤ x := by nlinarith [sq_nonneg y]
        have hx2 : x ≤ 1 := by nlinarith [sq_nonneg y]
        have hy1 : -1 ≤ y := by nlinarith [sq_nonneg x]
        have hy2 : y ≤ 1 := by nlinarith [sq_nonneg x]
        rw [hxy]
        interval_cases x <;> interval_cases y <;> simp_all
      · rintro (rfl | rfl | rfl | rfl) <;>
          exact mem_unities_of_norm_one (by exact_mod_cast hint _ _) (by rw [qnorm_eq]; norm_num)
    rw [hS]
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair] <;>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or, ne_eq,
        QuadraticAlgebra.mk.injEq] <;> norm_num
  · subst h3
    have hhalf : ∀ x y : ℤ, Odd x → Odd y →
        IsIntegral ℤ (⟨x / 2, y / 2⟩ : QuadraticAlgebra ℚ (-3 : ℤ) 0) := fun x y hx hy ↦ by
      obtain ⟨k, rfl⟩ := hy
      obtain ⟨j, rfl⟩ := hx
      have := isIntegral_mk_half (m := -3) (by norm_num) (j - k) (2 * k + 1)
      convert this using 2 <;> push_cast <;> ring
    have hS : unities (-3) = {⟨1, 0⟩, ⟨-1, 0⟩, ⟨1 / 2, 1 / 2⟩, ⟨1 / 2, -1 / 2⟩, ⟨-1 / 2, 1 / 2⟩,
        ⟨-1 / 2, -1 / 2⟩} := by
      ext ε
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro h
        obtain ⟨A, B, rfl, hAB⟩ := unities_coords (by norm_num) hm h
        have hA1 : -2 ≤ A := by nlinarith [sq_nonneg B]
        have hA2 : A ≤ 2 := by nlinarith [sq_nonneg B]
        have hB1 : -1 ≤ B := by nlinarith [sq_nonneg A]
        have hB2 : B ≤ 1 := by nlinarith [sq_nonneg A]
        interval_cases A <;> interval_cases B <;> (try norm_num at hAB) <;>
          norm_num [QuadraticAlgebra.mk.injEq]
      · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
        · exact mem_unities_of_norm_one (by exact_mod_cast hint 1 0) (by rw [qnorm_eq]; norm_num)
        · exact mem_unities_of_norm_one (by exact_mod_cast hint (-1) 0) (by rw [qnorm_eq]; norm_num)
        · exact mem_unities_of_norm_one (by convert hhalf 1 1 odd_one odd_one using 2)
            (by rw [qnorm_eq]; norm_num)
        · exact mem_unities_of_norm_one
            (by convert hhalf 1 (-1) odd_one (by decide) using 2 <;> norm_num)
            (by rw [qnorm_eq]; norm_num)
        · exact mem_unities_of_norm_one
            (by convert hhalf (-1) 1 (by decide) odd_one using 2 <;> norm_num)
            (by rw [qnorm_eq]; norm_num)
        · exact mem_unities_of_norm_one
            (by convert hhalf (-1) (-1) (by decide) (by decide) using 2 <;> norm_num)
            (by rw [qnorm_eq]; norm_num)
    rw [hS]
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
      Set.ncard_insert_of_notMem, Set.ncard_pair] <;>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or, ne_eq,
        QuadraticAlgebra.mk.injEq] <;> norm_num
  · have hS : unities m = {1, -1} := by
      ext ε
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro h
        obtain ⟨A, B, rfl, hAB⟩ := unities_coords hm0 hm h
        have hB : B = 0 := by
          by_contra hB
          have hB1 : 1 ≤ B ^ 2 := by have := sq_pos_of_ne_zero hB; omega
          -- then `-m ≤ 4`, so `m ∈ {-1, -2, -3, -4}`; `-1, -3` are excluded, `-4` is not squarefree
          have hm4 : -4 ≤ m := by nlinarith [sq_nonneg A]
          have hm4' : m ≠ -4 := by
            rintro rfl
            have := hm 2 ⟨-1, by norm_num⟩
            rw [Int.isUnit_iff] at this
            omega
          have hm2 : m = -2 := by omega
          subst hm2
          have hA1 : -2 ≤ A := by nlinarith [sq_nonneg B]
          have hA2 : A ≤ 2 := by nlinarith [sq_nonneg B]
          have hB1' : -1 ≤ B := by nlinarith [sq_nonneg A]
          have hB2' : B ≤ 1 := by nlinarith [sq_nonneg A]
          interval_cases B <;> interval_cases A <;> simp_all
        subst hB
        have hA : A = 2 ∨ A = -2 := by
          have : (A - 2) * (A + 2) = 0 := by nlinarith
          rcases mul_eq_zero.1 this with h | h
          · left; linarith
          · right; linarith
        rcases hA with rfl | rfl
        · left; ext <;> simp
        · right; ext <;> simp
      · rintro (rfl | rfl)
        · exact mem_unities_of_norm_one (by simpa using hint 1 0) (by rw [qnorm_eq]; simp)
        · exact mem_unities_of_norm_one (by simpa using hint (-1) 0) (by rw [qnorm_eq]; simp)
    rw [hS, Set.ncard_pair]
    intro h
    have := congrArg QuadraticAlgebra.re h
    simp at this
    norm_num at this

end NTKB.HardyWright
