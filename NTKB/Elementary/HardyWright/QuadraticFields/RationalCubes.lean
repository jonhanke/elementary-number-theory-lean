/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Attr
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Rat.Defs
import Aesop.BuiltinRules
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
/-!
# Rationals as sums of cubes; `x³ + y³ = u³ + v³` (Hardy–Wright §§ 13.6–13.7)

* Theorem 234 (`exists_three_pos_rat_cubes`): every positive rational is a sum of three positive
  rational cubes, by the book's construction (13.6.3)–(13.6.9) with `1 < t < 2`.
* Theorem 235 (`cube_add_cube_eq_iff`): apart from the trivial solutions `x = y = 0, u = -v` and
  `x = u, y = v`, the rational solutions of `x³ + y³ = u³ + v³` are exactly Euler's and Binet's
  (13.7.8), `λ ≠ 0`.
* § 13.7: Ramanujan's solution of `x³ + y³ + z³ = t³` (`ramanujan_cubes`), Euler's parametric
  solution (13.7.11) of `x⁴ + y⁴ = u⁴ + v⁴` (`euler_fourth_powers`; the book prints the formula for
  `u` with the sign of `3a²b⁵` wrong, it must be `-3a²b⁵`), and the numerical examples.
-/

namespace NTKB.HardyWright

/-- The identity behind Theorem 234: with `s = t + 1` and `r = 72 w³ t`, the three numbers
`w (s³ - 12t(t-1)) / s²`, `12 w t (t-1) / s²` and `w (12t - s²) / s` are the `x, y, z` of (13.6.9). -/
lemma rational_three_cubes_identity (w t : ℚ) (hs : t + 1 ≠ 0) :
    (w * ((t + 1) ^ 3 - 12 * t * (t - 1)) / (t + 1) ^ 2) ^ 3 +
      (12 * w * t * (t - 1) / (t + 1) ^ 2) ^ 3 + (w * (12 * t - (t + 1) ^ 2) / (t + 1)) ^ 3 =
      72 * w ^ 3 * t := by
  field_simp
  ring

/-- **Theorem 234.** Any positive rational is the sum of three positive rational cubes. -/
@[kb "hardywright2008" "Thm 234, p. 274"]
theorem exists_three_pos_rat_cubes {r : ℚ} (hr : 0 < r) :
    ∃ x y z : ℚ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x ^ 3 + y ^ 3 + z ^ 3 = r := by
  -- choose a rational `w > 0` with `r / 144 < w³ < r / 72`, so that `t = r / (72 w³) ∈ (1, 2)`
  have hlo : (0 : ℝ) ≤ ((r : ℝ) / 144) ^ ((1 : ℝ) / 3) := by positivity
  have hlt : ((r : ℝ) / 144) ^ ((1 : ℝ) / 3) < ((r : ℝ) / 72) ^ ((1 : ℝ) / 3) := by
    apply Real.rpow_lt_rpow (by positivity) _ (by norm_num)
    have : (0 : ℝ) < r := by exact_mod_cast hr
    linarith
  obtain ⟨w, hw1, hw2⟩ := exists_rat_btwn hlt
  have hw0 : (0 : ℝ) < w := lt_of_le_of_lt hlo hw1
  have hcube : ∀ {a : ℝ}, 0 ≤ a → (a ^ ((1 : ℝ) / 3)) ^ 3 = a := fun ha ↦ by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha]; norm_num
  have hw1' : (r : ℝ) / 144 < (w : ℝ) ^ 3 := by
    have := pow_lt_pow_left₀ hw1 hlo (by norm_num : (3 : ℕ) ≠ 0)
    rwa [hcube (by positivity)] at this
  have hw2' : (w : ℝ) ^ 3 < (r : ℝ) / 72 := by
    have := pow_lt_pow_left₀ hw2 hw0.le (by norm_num : (3 : ℕ) ≠ 0)
    rwa [hcube (by positivity)] at this
  have hw0' : (0 : ℚ) < w := by exact_mod_cast hw0
  have h1 : r / 144 < w ^ 3 := by exact_mod_cast hw1'
  have h2 : w ^ 3 < r / 72 := by exact_mod_cast hw2'
  set t : ℚ := r / (72 * w ^ 3) with ht
  have hw3 : 0 < w ^ 3 := by positivity
  have ht1 : 1 < t := by rw [ht, lt_div_iff₀ (by positivity)]; linarith
  have ht2 : t < 2 := by rw [ht, div_lt_iff₀ (by positivity)]; linarith
  have hrt : r = 72 * w ^ 3 * t := by rw [ht]; field_simp
  refine ⟨w * ((t + 1) ^ 3 - 12 * t * (t - 1)) / (t + 1) ^ 2, 12 * w * t * (t - 1) / (t + 1) ^ 2,
    w * (12 * t - (t + 1) ^ 2) / (t + 1), ?_, ?_, ?_, ?_⟩
  · apply div_pos (mul_pos hw0' _) (by positivity)
    have e : (t + 1) ^ 3 - 12 * t * (t - 1) = 8 - (t - 1) ^ 2 * (7 - t) := by ring
    rw [e]
    have h1 : (t - 1) ^ 2 < 1 := by nlinarith
    have h2 : 0 < 7 - t := by linarith
    nlinarith
  · apply div_pos _ (by positivity)
    have : 0 < t - 1 := by linarith
    positivity
  · apply div_pos (mul_pos hw0' _) (by positivity)
    nlinarith
  · rw [rational_three_cubes_identity w t (by positivity), hrt]

/-- Euler's and Binet's parametrization (13.7.8) of `x³ + y³ = u³ + v³`. -/
def eulerBinet (l a b : ℚ) : ℚ × ℚ × ℚ × ℚ :=
  (l * (1 - (a - 3 * b) * (a ^ 2 + 3 * b ^ 2)), l * ((a + 3 * b) * (a ^ 2 + 3 * b ^ 2) - 1),
    l * ((a + 3 * b) - (a ^ 2 + 3 * b ^ 2) ^ 2), l * ((a ^ 2 + 3 * b ^ 2) ^ 2 - (a - 3 * b)))

/-- **Theorem 235.** Apart from the trivial solutions `x = y = 0, u = -v` and `x = u, y = v`, the
general rational solution of `x³ + y³ = u³ + v³` is given by (13.7.8), where `λ, a, b` are any
rationals with `λ ≠ 0`. -/
@[kb "hardywright2008" "Thm 235, p. 278"]
theorem cube_add_cube_eq_iff (x y u v : ℚ) :
    x ^ 3 + y ^ 3 = u ^ 3 + v ^ 3 ↔
      (x = 0 ∧ y = 0 ∧ u = -v) ∨ (x = u ∧ y = v) ∨
        ∃ l a b : ℚ, l ≠ 0 ∧ (x, y, u, v) = eulerBinet l a b := by
  constructor
  · intro h
    -- `x = X - Y`, `y = X + Y`, `u = U - V`, `v = U + V` give `X(X² + 3Y²) = U(U² + 3V²)` (13.7.3)
    set X := (x + y) / 2
    set Y := (y - x) / 2
    set U := (u + v) / 2
    set V := (v - u) / 2
    have hx : x = X - Y := by simp only [X, Y]; ring
    have hy : y = X + Y := by simp only [X, Y]; ring
    have hu : u = U - V := by simp only [U, V]; ring
    have hv : v = U + V := by simp only [U, V]; ring
    have H : X * (X ^ 2 + 3 * Y ^ 2) = U * (U ^ 2 + 3 * V ^ 2) := by
      rw [hx, hy, hu, hv] at h; linear_combination h / 2
    by_cases hXY : X = 0 ∧ Y = 0
    · left
      obtain ⟨hX, hY⟩ := hXY
      rw [hX, hY] at H
      have hU : U = 0 := by
        have : U * (U ^ 2 + 3 * V ^ 2) = 0 := by linarith
        rcases mul_eq_zero.1 this with h | h
        · exact h
        · nlinarith [sq_nonneg U, sq_nonneg V]
      refine ⟨by rw [hx, hX, hY]; ring, by rw [hy, hX, hY]; ring, by rw [hu, hv, hU]; ring⟩
    right
    have hN : X ^ 2 + 3 * Y ^ 2 ≠ 0 := by
      intro h0
      apply hXY
      constructor <;> nlinarith [sq_nonneg X, sq_nonneg Y]
    -- `U + V√-3 = (a + b√-3)(X - Y√-3)`
    obtain ⟨a, b, hU, hV⟩ : ∃ a b : ℚ, U = a * X - 3 * b * Y ∧ V = b * X + a * Y := by
      obtain ⟨N, hN0, hNd⟩ : ∃ N : ℚ, N ≠ 0 ∧ N = X ^ 2 + 3 * Y ^ 2 := ⟨_, hN, rfl⟩
      refine ⟨(U * X + 3 * V * Y) / N, (V * X - U * Y) / N, ?_, ?_⟩
      · field_simp; rw [hNd]; ring
      · field_simp; rw [hNd]; ring
    have hN' : U ^ 2 + 3 * V ^ 2 = (a ^ 2 + 3 * b ^ 2) * (X ^ 2 + 3 * Y ^ 2) := by
      rw [hU, hV]; ring
    have hXU : X = U * (a ^ 2 + 3 * b ^ 2) := by
      apply mul_right_cancel₀ hN
      rw [H, hN']; ring
    set c := a * (a ^ 2 + 3 * b ^ 2) - 1
    set d := 3 * b * (a ^ 2 + 3 * b ^ 2)
    have hcd : c * X = d * Y := by
      simp only [c, d]
      have := hXU
      rw [hU] at this
      linear_combination -this
    by_cases h0 : c = 0 ∧ d = 0
    · -- `b = 0`, `a = 1`: the trivial solution `x = u`, `y = v`
      left
      obtain ⟨hc, hd⟩ := h0
      have hb : b = 0 := by
        rcases mul_eq_zero.1 hd with h | h
        · linarith
        · have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
          simp only [c, ha] at hc; norm_num at hc
      have ha : a = 1 := by
        simp only [c, hb] at hc
        have : (a - 1) * (a ^ 2 + a + 1) = 0 := by linear_combination hc
        rcases mul_eq_zero.1 this with h | h
        · linarith
        · nlinarith [sq_nonneg (a + 1 / 2)]
      have hUX : U = X := by rw [hU, ha, hb]; ring
      have hVY : V = Y := by rw [hV, ha, hb]; ring
      exact ⟨by rw [hx, hu, hUX, hVY], by rw [hy, hv, hUX, hVY]⟩
    · -- `X = λ d`, `Y = λ c` (13.7.5)
      right
      obtain ⟨l, hlX, hlY⟩ : ∃ l : ℚ, X = l * d ∧ Y = l * c := by
        by_cases hd : d = 0
        · have hc : c ≠ 0 := fun hc ↦ h0 ⟨hc, hd⟩
          refine ⟨Y / c, ?_, by field_simp⟩
          rw [hd, mul_zero]
          rw [hd, zero_mul] at hcd
          exact (mul_eq_zero.1 hcd).resolve_left hc
        · refine ⟨X / d, by field_simp, ?_⟩
          field_simp
          linear_combination -hcd
      have hl : l ≠ 0 := by
        rintro rfl
        exact hXY ⟨by rw [hlX]; ring, by rw [hlY]; ring⟩
      refine ⟨l, a, b, hl, ?_⟩
      simp only [eulerBinet, Prod.mk.injEq]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hx, hlX, hlY]; simp only [c, d]; ring
      · rw [hy, hlX, hlY]; simp only [c, d]; ring
      · rw [hu, hU, hV, hlX, hlY]; simp only [c, d]; ring
      · rw [hv, hU, hV, hlX, hlY]; simp only [c, d]; ring
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨l, a, b, -, h⟩)
    · ring
    · rfl
    · simp only [eulerBinet, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      ring

/-- (13.7.9) and § 13.6: `1³ + 12³ = 9³ + 10³` comes from `a = 10/19`, `b = -7/19`,
`λ = -361/42`; `a = b = 1`, `λ = 1/3` gives `3³ + 5³ = (-4)³ + 6³`, i.e. `6³ = 3³ + 4³ + 5³`. -/
theorem eulerBinet_examples :
    eulerBinet (-361 / 42) (10 / 19) (-7 / 19) = (1, 12, 9, 10) ∧
      eulerBinet (1 / 3) 1 1 = (3, 5, -4, 6) ∧ (6 : ℤ) ^ 3 = 3 ^ 3 + 4 ^ 3 + 5 ^ 3 := by
  refine ⟨?_, ?_, by norm_num⟩ <;> simp only [eulerBinet] <;> norm_num

/-- § 13.7: Ramanujan's solution of `x³ + y³ + z³ = t³`. -/
@[kb "hardywright2008" "§ 13.7, p. 279"]
theorem ramanujan_cubes {R : Type*} [CommRing R] (a b : R) :
    (3 * a ^ 2 + 5 * a * b - 5 * b ^ 2) ^ 3 + (4 * a ^ 2 - 4 * a * b + 6 * b ^ 2) ^ 3 +
      (5 * a ^ 2 - 5 * a * b - 3 * b ^ 2) ^ 3 = (6 * a ^ 2 - 4 * a * b + 4 * b ^ 2) ^ 3 := by
  ring

/-- § 13.7: the examples `17³ + 14³ + 7³ = 20³` (Ramanujan's formula with `a = 2, b = 1`),
`1³ + 6³ + 8³ = 9³`, `2³ + 34³ = 15³ + 33³`, `9³ + 15³ = 2³ + 16³`. -/
theorem cube_examples : (17 : ℤ) ^ 3 + 14 ^ 3 + 7 ^ 3 = 20 ^ 3 ∧ (1 : ℤ) ^ 3 + 6 ^ 3 + 8 ^ 3 = 9 ^ 3 ∧
    (2 : ℤ) ^ 3 + 34 ^ 3 = 15 ^ 3 + 33 ^ 3 ∧ (9 : ℤ) ^ 3 + 15 ^ 3 = 2 ^ 3 + 16 ^ 3 := by
  norm_num

/-- § 13.7, (13.7.11): Euler's parametric solution of `x⁴ + y⁴ = u⁴ + v⁴` (with the sign of the term
`3a²b⁵` in `u` corrected: the book prints `u` equal to `x`). -/
@[kb "hardywright2008" "§ 13.7, p. 279"]
theorem euler_fourth_powers {R : Type*} [CommRing R] (a b : R) :
    (a ^ 7 + a ^ 5 * b ^ 2 - 2 * a ^ 3 * b ^ 4 + 3 * a ^ 2 * b ^ 5 + a * b ^ 6) ^ 4 +
      (a ^ 6 * b - 3 * a ^ 5 * b ^ 2 - 2 * a ^ 4 * b ^ 3 + a ^ 2 * b ^ 5 + b ^ 7) ^ 4 =
    (a ^ 7 + a ^ 5 * b ^ 2 - 2 * a ^ 3 * b ^ 4 - 3 * a ^ 2 * b ^ 5 + a * b ^ 6) ^ 4 +
      (a ^ 6 * b + 3 * a ^ 5 * b ^ 2 - 2 * a ^ 4 * b ^ 3 + a ^ 2 * b ^ 5 + b ^ 7) ^ 4 := by
  ring

/-- § 13.7: with `a = 1, b = 2`, (13.7.11) gives `133⁴ + 134⁴ = 158⁴ + 59⁴`. -/
theorem euler_fourth_powers_example : (133 : ℤ) ^ 4 + 134 ^ 4 = 158 ^ 4 + 59 ^ 4 := by norm_num

end NTKB.HardyWright
