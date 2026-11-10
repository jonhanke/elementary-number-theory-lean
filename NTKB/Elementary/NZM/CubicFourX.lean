/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Attr
import Mathlib.NumberTheory.FLT.Four
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
# Rational points on `y² = x³ - 4x` (Niven–Zuckerman–Montgomery, § 5.7)

* Theorem 5.24: the only rational solutions of `y² = x³ - 4x` are `(0, 0)`, `(2, 0)`, `(-2, 0)`
  (together with the point at infinity, which is not an affine solution).

Proof (following the book): for a solution with `x ≠ 0` put `m = y / x`; then
`m² x = x² - 4`, so `(2x - m²)² = m⁴ + 16`.  Writing `m = p / q` in lowest terms, `p⁴ + (2q)⁴`
is the square of a rational, hence of an integer, which by Fermat (`not_fermat_42`) forces
`p = 0`.  Hence `y = 0` and `x = ±2`.
-/

namespace NTKB.NZM

/-- If `m⁴ + 16 = n²` with `m, n` rational, then `m = 0` (Fermat's `a⁴ + b⁴ ≠ c²`). -/
theorem rat_quartic_sixteen {m n : ℚ} (h : m ^ 4 + 16 = n ^ 2) : m = 0 := by
  have hq : (m.den : ℚ) ≠ 0 := by exact_mod_cast m.den_pos.ne'
  have hm : (m.num : ℚ) = m * m.den := (div_eq_iff hq).mp (Rat.num_div_den m)
  have hsq : IsSquare (((m.num ^ 4 + (2 * (m.den : ℤ)) ^ 4 : ℤ)) : ℚ) := by
    refine ⟨n * (m.den : ℚ) ^ 2, ?_⟩
    push_cast
    rw [hm]
    linear_combination ((m.den : ℚ) ^ 4) * h
  obtain ⟨r, hr⟩ := Rat.isSquare_intCast_iff.mp hsq
  by_contra hm0
  have hnum : m.num ≠ 0 := Rat.num_ne_zero.mpr hm0
  have hden : (2 * (m.den : ℤ)) ≠ 0 := by
    have : (0 : ℤ) < m.den := by exact_mod_cast m.den_pos
    omega
  exact not_fermat_42 hnum hden (c := r) (by rw [hr]; ring)

/-- **Theorem 5.24.** The only rational solutions of `y² = x³ - 4x` are `(0, 0)`, `(2, 0)`
and `(-2, 0)`. -/
@[kb "nivenzuckermanmontgomery" "Thm 5.24, p. 271"]
theorem rational_solutions_y_sq_x_cubed_sub_four_x (x y : ℚ) :
    y ^ 2 = x ^ 3 - 4 * x ↔ (x, y) ∈ ({(0, 0), (2, 0), (-2, 0)} : Set (ℚ × ℚ)) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · intro h
    by_cases hx : x = 0
    · subst hx
      left
      refine ⟨rfl, ?_⟩
      nlinarith [sq_nonneg y]
    · have hm : (y / x) ^ 2 * x = x ^ 2 - 4 := by
        field_simp
        linear_combination h
      have h2 : (y / x) ^ 4 + 16 = (2 * x - (y / x) ^ 2) ^ 2 := by
        linear_combination (4 : ℚ) * hm
      have hy : y / x = 0 := rat_quartic_sixteen h2
      have hy0 : y = 0 := by
        rcases div_eq_zero_iff.mp hy with h0 | h0
        · exact h0
        · exact absurd h0 hx
      subst hy0
      have h3 : x * ((x - 2) * (x + 2)) = x * 0 := by linear_combination (-1 : ℚ) * h
      have h4 : (x - 2) * (x + 2) = 0 := mul_left_cancel₀ hx h3
      rcases mul_eq_zero.mp h4 with h0 | h0
      · right; left; exact ⟨by linarith, rfl⟩
      · right; right; exact ⟨by linarith, rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

end NTKB.NZM
