/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.ThreeSquares.Statements
import NTKB.Elementary.HardyWright.SumsOfSquares.ThreeSquares.Ternary
import NTKB.Elementary.HardyWright.SumsOfSquares.ThreeSquares.Construction

/-!
# Hardy–Wright, § 20.10: the three-square theorem (Legendre, Gauss)

A non-negative integer is the sum of three squares if and only if it is not of the form
`4ᵃ(8m + 7)` (`isSumOfPowers_two_three_iff`, `exists_sq_add_sq_add_sq_iff`).

The book states the theorem without proof. Necessity is `not_isSumOfPowers_two_three`.
Sufficiency is Dirichlet's proof: after removing factors `4`, `n ≢ 0, 4, 7 (mod 8)`;
`exists_form` gives `a, b, c` with `a > 0`, `ac - b² > 0`, `n(ac - b²) - c = 1`, so the ternary form
with matrix `[[a, b, 1], [b, c, 0], [1, 0, n]]` is positive definite of determinant `1` and takes the
value `n` at `(0, 0, 1)`; by `exists_sq_add_sq_add_sq_of_det_eq_one` its values are sums of three
squares.
-/

open Matrix

namespace NTKB.HardyWright

open ThreeSquares

/-- The matrix of Dirichlet's form. -/
def dirichletMatrix (a b c n : ℤ) : Matrix (Fin 3) (Fin 3) ℤ := !![a, b, 1; b, c, 0; 1, 0, n]

lemma exists_sq_add_sq_add_sq_of_mod_eight {n : ℕ}
    (hn : n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 6) :
    ∃ x y z : ℕ, n = x ^ 2 + y ^ 2 + z ^ 2 := by
  obtain ⟨a, b, c, ha, hd, hdet⟩ := exists_form n hn
  set M := dirichletMatrix a b c n with hM
  have hMs : M.IsSymm := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hMdet : M.det = 1 := by
    rw [hM]
    simp [dirichletMatrix, Matrix.det_fin_three]
    linear_combination hdet
  have hpos : ∀ x : Fin 3 → ℝ, x ≠ 0 → 0 < qf (M.map (Int.cast : ℤ → ℝ)) x := by
    intro x hx
    have hq : qf (M.map (Int.cast : ℤ → ℝ)) x = (a : ℝ) * x 0 ^ 2 + 2 * b * x 0 * x 1 +
        2 * x 0 * x 2 + c * x 1 ^ 2 + n * x 2 ^ 2 := by
      simp [qf, hM, dirichletMatrix, Fin.sum_univ_three]
      push_cast; ring
    have hdetR : (n : ℝ) * ((a : ℝ) * c - b ^ 2) - c = 1 := by exact_mod_cast hdet
    set d : ℝ := (a : ℝ) * c - b ^ 2 with hdd
    have haR : (0 : ℝ) < a := by exact_mod_cast ha
    have hd0 : (0 : ℝ) < d := by rw [hdd]; exact_mod_cast hd
    -- `a d q = d (a x₀ + b x₁ + x₂)² + (d x₁ - b x₂)² + a x₂²`
    have key : (a : ℝ) * d * qf (M.map (Int.cast : ℤ → ℝ)) x =
        d * (a * x 0 + b * x 1 + x 2) ^ 2 + (d * x 1 - b * x 2) ^ 2 + a * x 2 ^ 2 := by
      rw [hq, hdd]
      rw [hdd] at hdetR
      linear_combination (↑a * x 2 ^ 2) * hdetR
    have hnn : 0 ≤ d * (a * x 0 + b * x 1 + x 2) ^ 2 + (d * x 1 - b * x 2) ^ 2 := by positivity
    have hpos' : 0 < d * (a * x 0 + b * x 1 + x 2) ^ 2 + (d * x 1 - b * x 2) ^ 2 + a * x 2 ^ 2 := by
      by_contra hle
      push Not at hle
      have h2 : x 2 = 0 := by
        have : (a : ℝ) * x 2 ^ 2 = 0 := by
          apply le_antisymm _ (by positivity)
          nlinarith [sq_nonneg (d * x 1 - b * x 2), mul_nonneg hd0.le (sq_nonneg (a * x 0 + b * x 1 + x 2))]
        have := (mul_eq_zero.mp this).resolve_left haR.ne'
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      rw [h2] at hle
      have h1 : x 1 = 0 := by
        have h' : (d * x 1 - b * 0) ^ 2 = 0 := by
          apply le_antisymm _ (by positivity)
          nlinarith [mul_nonneg hd0.le (sq_nonneg (a * x 0 + b * x 1 + 0))]
        have : (d : ℝ) * x 1 = 0 := by simpa using h'
        exact (mul_eq_zero.mp this).resolve_left hd0.ne'
      rw [h1] at hle
      have h0 : x 0 = 0 := by
        have h' : (d : ℝ) * (a * x 0 + b * 0 + 0) ^ 2 = 0 := by
          apply le_antisymm _ (by positivity)
          nlinarith
        have : (a : ℝ) * x 0 = 0 := by
          have := (mul_eq_zero.mp h').resolve_left hd0.ne'
          simpa using this
        exact (mul_eq_zero.mp this).resolve_left haR.ne'
      apply hx
      ext i; fin_cases i
      · exact h0
      · exact h1
      · exact h2
    have : 0 < (a : ℝ) * d * qf (M.map (Int.cast : ℤ → ℝ)) x := by rw [key]; exact hpos'
    exact pos_of_mul_pos_right this (by positivity)
  obtain ⟨u, v, w, huvw⟩ := exists_sq_add_sq_add_sq_of_det_eq_one hMs hpos hMdet ![0, 0, 1]
  have hval : qZ M ![0, 0, 1] = n := by
    simp [qZ, hM, dirichletMatrix, dotProduct, mulVec, Fin.sum_univ_three]
  refine ⟨u.natAbs, v.natAbs, w.natAbs, ?_⟩
  have : (n : ℤ) = u ^ 2 + v ^ 2 + w ^ 2 := by rw [← hval, huvw]
  zify
  simpa [sq_abs] using this

/-- **The three-square theorem, sufficiency** (Legendre, Gauss). Every non-negative integer not of
the form `4ᵃ(8m + 7)` is the sum of three squares. -/
@[kb "hardywright2008" "Section 20.10, p. 428"]
theorem exists_sq_add_sq_add_sq_of_ne {n : ℕ} (hn : ∀ a m : ℕ, n ≠ 4 ^ a * (8 * m + 7)) :
    ∃ x y z : ℕ, n = x ^ 2 + y ^ 2 + z ^ 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  by_cases h0 : n = 0
  · exact ⟨0, 0, 0, by simp [h0]⟩
  by_cases h4 : 4 ∣ n
  · obtain ⟨k, rfl⟩ := h4
    have hk : ∀ a m : ℕ, k ≠ 4 ^ a * (8 * m + 7) := by
      intro a m hkm
      exact hn (a + 1) m (by rw [hkm, pow_succ]; ring)
    obtain ⟨x, y, z, hxyz⟩ := ih k (by omega) hk
    exact ⟨2 * x, 2 * y, 2 * z, by rw [hxyz]; ring⟩
  · have h7 : n % 8 ≠ 7 := by
      intro h7
      exact hn 0 (n / 8) (by simp; omega)
    exact exists_sq_add_sq_add_sq_of_mod_eight (by omega)

/-- **The three-square theorem** (Legendre, Gauss; Hardy–Wright § 20.10). A non-negative integer is
the sum of three squares if and only if it is not of the form `4ᵃ(8m + 7)`. -/
@[kb "hardywright2008" "Section 20.10, p. 428"]
theorem exists_sq_add_sq_add_sq_iff (n : ℕ) :
    (∃ x y z : ℕ, n = x ^ 2 + y ^ 2 + z ^ 2) ↔ ∀ a m : ℕ, n ≠ 4 ^ a * (8 * m + 7) := by
  refine ⟨?_, exists_sq_add_sq_add_sq_of_ne⟩
  rintro ⟨x, y, z, hxyz⟩ a m hn
  apply not_isSumOfPowers_two_three a m
  rw [← hn]
  exact ⟨![x, y, z], by simp [Fin.sum_univ_three, hxyz]⟩

/-- The three-square theorem in the language of § 20.1 (`IsSumOfPowers 2 3`). -/
@[kb "hardywright2008" "Section 20.10, p. 428"]
theorem isSumOfPowers_two_three_iff (n : ℕ) :
    IsSumOfPowers 2 3 n ↔ ∀ a m : ℕ, n ≠ 4 ^ a * (8 * m + 7) := by
  rw [← exists_sq_add_sq_add_sq_iff]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x 0, x 1, x 2, by rw [← hx, Fin.sum_univ_three]⟩
  · rintro ⟨x, y, z, h⟩
    exact ⟨![x, y, z], by simp [Fin.sum_univ_three, h]⟩

end NTKB.HardyWright
