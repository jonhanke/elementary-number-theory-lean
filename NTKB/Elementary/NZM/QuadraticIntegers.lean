/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.QuadraticFields.NormEuclidean

/-!
# The integers of a quadratic field (Niven–Zuckerman–Montgomery, § 9.5)

**Theorem 9.20** (the integers). Let `m ≠ 1` be squarefree and `ℚ(√m)` the quadratic field, modelled as
Hardy–Wright's `QuadraticAlgebra ℚ m 0` (elements `⟨a, b⟩ = a + b√m`). If `m ≡ 2, 3 (mod 4)` the integers
are the `a + b√m` with `a, b ∈ ℤ`; if `m ≡ 1 (mod 4)` they are the `(a + b√m)/2` with `a, b ∈ ℤ` of the
same parity.

Hardy–Wright (`NTKB.HardyWright.exists_int_of_isIntegral`, `exists_half_of_isIntegral`,
`isIntegral_mk_int`, `isIntegral_mk_half`) give everything but the parity condition in the forward
direction; it follows from the norm `(a² - m b²)/4` being an integer.
-/

namespace NTKB.NZM

open NTKB.HardyWright

variable {m : ℤ}

/-- `A² ≡ A (mod 2)` read modulo `4`: `A² mod 4 = A mod 2`. -/
lemma sq_emod_four (A : ℤ) : A ^ 2 % 4 = A % 2 := by
  obtain ⟨a, rfl | rfl⟩ := Int.even_or_odd' A <;> ring_nf <;> omega

/-- For `m ≡ 1 (mod 4)` squarefree, the integers of `ℚ(√m)` are the `(A + B√m)/2` with `A ≡ B (mod 2)`. -/
theorem isIntegral_iff_half (hm : Squarefree m) (h1 : m % 4 = 1) (z : QuadraticAlgebra ℚ m 0) :
    IsIntegral ℤ z ↔ ∃ A B : ℤ, A % 2 = B % 2 ∧ z = ⟨A / 2, B / 2⟩ := by
  constructor
  · intro hz
    obtain ⟨A, B, rfl⟩ := exists_half_of_isIntegral hm hz
    obtain ⟨-, N, hN⟩ := isIntegral_iff_trace_norm.1 hz
    have h4 : (4 * N : ℤ) = A ^ 2 - m * B ^ 2 := by
      have : (4 * N : ℚ) = (A : ℚ) ^ 2 - m * (B : ℚ) ^ 2 := by
        simp only at hN; rw [hN]; ring
      exact_mod_cast this
    obtain ⟨k, hk⟩ : ∃ k, m = 4 * k + 1 := ⟨m / 4, by omega⟩
    subst hk
    have hA := sq_emod_four A
    have hB := sq_emod_four B
    refine ⟨A, B, ?_, rfl⟩
    have : A ^ 2 - B ^ 2 = 4 * (N + k * B ^ 2) := by linear_combination -h4
    omega
  · rintro ⟨A, B, hAB, rfl⟩
    obtain ⟨x, hx⟩ : ∃ x, A = 2 * x + B := ⟨(A - B) / 2, by omega⟩
    have := isIntegral_mk_half (m := m) h1 x B
    convert this using 2
    rw [hx]; push_cast; ring

/-- **Theorem 9.20** (the integers of `ℚ(√m)`, `m ≠ 1` squarefree): for `m ≡ 2, 3 (mod 4)` they are the
`a + b√m`, `a, b ∈ ℤ`; for `m ≡ 1 (mod 4)` they are the `(a + b√m)/2` with `a ≡ b (mod 2)`. -/
@[kb "nivenzuckermanmontgomery" "Thm 9.20, p. 425"]
theorem isIntegral_quadratic_iff (hm : Squarefree m) (z : QuadraticAlgebra ℚ m 0) :
    ((m % 4 = 2 ∨ m % 4 = 3) → (IsIntegral ℤ z ↔ ∃ a b : ℤ, z = ⟨a, b⟩)) ∧
    (m % 4 = 1 → (IsIntegral ℤ z ↔ ∃ a b : ℤ, a % 2 = b % 2 ∧ z = ⟨a / 2, b / 2⟩)) := by
  refine ⟨fun h ↦ ⟨exists_int_of_isIntegral hm h, ?_⟩, fun h ↦ isIntegral_iff_half hm h z⟩
  rintro ⟨a, b, rfl⟩
  exact isIntegral_mk_int a b

end NTKB.NZM
