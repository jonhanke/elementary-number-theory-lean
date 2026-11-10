/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Attr
import Mathlib.Algebra.Ring.Rat
import Mathlib.Algebra.Field.Rat
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# Rational points on `y² = x³ + a x² + b x + c` (Niven–Zuckerman–Montgomery, § 5.7)

* Theorem 5.25: every rational point `(x₁, y₁)` on `y² = x³ + a x² + b x + c` with integral
  `a, b, c` has the form `x₁ = u/w²`, `y₁ = v/w³` with `w > 0` and `gcd(u, w) = gcd(v, w) = 1`.

Proof (differs slightly from the book): write `x₁ = X/D`, `y₁ = Y/E` in lowest terms.  Clearing
denominators gives `Y² D³ = E² (X³ + a X² D + b X D² + c D³)`.  Coprimality of `Y, E` gives
`E² ∣ D³`, and coprimality of `X, D` makes the bracket coprime to `D`, so `D³ ∣ E²`.  Hence
`D³ = E²`, so `D = w²`, `E = w³` for `w = E / D`.
-/

namespace NTKB.NZM

/-- Integer core of Theorem 5.25: if `Y² D³ = E² (X³ + a X² D + b X D² + c D³)` with `X, D`
coprime and `Y, E` coprime, `D, E > 0`, then `D = w²` and `E = w³` for some `w > 0`. -/
theorem rational_point_aux {a b c X D Y E : ℤ} (hD : 0 < D) (hE : 0 < E)
    (hXD : IsCoprime X D) (hYE : IsCoprime Y E)
    (hz : Y ^ 2 * D ^ 3 = E ^ 2 * (X ^ 3 + a * X ^ 2 * D + b * X * D ^ 2 + c * D ^ 3)) :
    ∃ w : ℤ, 0 < w ∧ D = w ^ 2 ∧ E = w ^ 3 := by
  -- E² ∣ D³
  have hc : IsCoprime (E ^ 2) (Y ^ 2) := hYE.symm.pow
  have h1 : E ^ 2 ∣ D ^ 3 := hc.dvd_of_dvd_mul_left ⟨_, hz⟩
  -- D³ ∣ E²
  have h3 : IsCoprime D (X ^ 3) := hXD.symm.pow_right
  obtain ⟨u, v, huv⟩ := h3
  have hS : IsCoprime D (X ^ 3 + a * X ^ 2 * D + b * X * D ^ 2 + c * D ^ 3) :=
    ⟨u - v * (a * X ^ 2 + b * X * D + c * D ^ 2), v, by linear_combination huv⟩
  have hS3 : IsCoprime (D ^ 3) (X ^ 3 + a * X ^ 2 * D + b * X * D ^ 2 + c * D ^ 3) :=
    hS.pow_left
  have hdiv : D ^ 3 ∣ E ^ 2 * (X ^ 3 + a * X ^ 2 * D + b * X * D ^ 2 + c * D ^ 3) :=
    ⟨Y ^ 2, by linear_combination (-1 : ℤ) * hz⟩
  have h2 : D ^ 3 ∣ E ^ 2 := hS3.dvd_of_dvd_mul_right hdiv
  have hD3 : 0 < D ^ 3 := by positivity
  have hE2 : 0 < E ^ 2 := by positivity
  have hDE : D ^ 3 = E ^ 2 :=
    le_antisymm (Int.le_of_dvd hE2 h2) (Int.le_of_dvd hD3 h1)
  -- D ∣ E
  have hsq : D ^ 2 ∣ E ^ 2 := by
    rw [← hDE]
    exact pow_dvd_pow D (by norm_num)
  have hdE : D ∣ E := by
    first
      | exact (Int.pow_dvd_pow_iff (by norm_num)).mp hsq
      | exact (pow_dvd_pow_iff_dvd (by norm_num)).mp hsq
  obtain ⟨w, hw⟩ := hdE
  have hD2 : D ^ 2 ≠ 0 := by positivity
  have hw2 : D = w ^ 2 := by
    have h4 : D ^ 2 * D = D ^ 2 * w ^ 2 := by
      linear_combination hDE + (E + D * w) * hw
    exact mul_left_cancel₀ hD2 h4
  have hw3 : E = w ^ 3 := by linear_combination hw + w * hw2
  have hw2pos : 0 < w ^ 2 := by rw [← hw2]; exact hD
  refine ⟨w, ?_, hw2, hw3⟩
  by_contra hneg
  push_neg at hneg
  nlinarith [mul_nonneg (neg_nonneg.mpr hneg) hw2pos.le, hw3, hE]

/-- **Theorem 5.25.** Every rational point `(x₁, y₁)` on `y² = x³ + a x² + b x + c` (integral
`a, b, c`) has the form `x₁ = u/w²`, `y₁ = v/w³` with integers `u, v, w`, `w > 0`,
`gcd(u, w) = gcd(v, w) = 1`. -/
@[kb "nivenzuckermanmontgomery" "Thm 5.25, p. 275"]
theorem rational_point_denominators {a b c : ℤ} {x₁ y₁ : ℚ}
    (h : y₁ ^ 2 = x₁ ^ 3 + a * x₁ ^ 2 + b * x₁ + c) :
    ∃ u v w : ℤ, 0 < w ∧ IsCoprime u w ∧ IsCoprime v w ∧ x₁ = u / w ^ 2 ∧ y₁ = v / w ^ 3 := by
  have hDq : (x₁.den : ℚ) ≠ 0 := by exact_mod_cast x₁.den_pos.ne'
  have hEq : (y₁.den : ℚ) ≠ 0 := by exact_mod_cast y₁.den_pos.ne'
  have hx' : (x₁.num : ℚ) = x₁ * (x₁.den : ℚ) := (div_eq_iff hDq).mp (Rat.num_div_den x₁)
  have hy' : (y₁.num : ℚ) = y₁ * (y₁.den : ℚ) := (div_eq_iff hEq).mp (Rat.num_div_den y₁)
  have hq : (y₁.num : ℚ) ^ 2 * (x₁.den : ℚ) ^ 3 =
      (y₁.den : ℚ) ^ 2 * ((x₁.num : ℚ) ^ 3 + a * (x₁.num : ℚ) ^ 2 * (x₁.den : ℚ)
        + b * (x₁.num : ℚ) * (x₁.den : ℚ) ^ 2 + c * (x₁.den : ℚ) ^ 3) := by
    rw [hx', hy']
    linear_combination ((y₁.den : ℚ) ^ 2 * (x₁.den : ℚ) ^ 3) * h
  have hz : y₁.num ^ 2 * ((x₁.den : ℕ) : ℤ) ^ 3 =
      ((y₁.den : ℕ) : ℤ) ^ 2 * (x₁.num ^ 3 + a * x₁.num ^ 2 * ((x₁.den : ℕ) : ℤ)
        + b * x₁.num * ((x₁.den : ℕ) : ℤ) ^ 2 + c * ((x₁.den : ℕ) : ℤ) ^ 3) := by
    exact_mod_cast hq
  have hD : (0 : ℤ) < ((x₁.den : ℕ) : ℤ) := by exact_mod_cast x₁.den_pos
  have hE : (0 : ℤ) < ((y₁.den : ℕ) : ℤ) := by exact_mod_cast y₁.den_pos
  obtain ⟨w, hw, hDw, hEw⟩ :=
    rational_point_aux hD hE (Rat.isCoprime_num_den x₁) (Rat.isCoprime_num_den y₁) hz
  refine ⟨x₁.num, y₁.num, w, hw, ?_, ?_, ?_, ?_⟩
  · exact (Rat.isCoprime_num_den x₁).of_isCoprime_of_dvd_right ⟨w, by rw [hDw]; ring⟩
  · exact (Rat.isCoprime_num_den y₁).of_isCoprime_of_dvd_right ⟨w ^ 2, by rw [hEw]; ring⟩
  · have hq1 : (x₁.den : ℚ) = (w : ℚ) ^ 2 := by exact_mod_cast hDw
    have := Rat.num_div_den x₁
    rw [hq1] at this
    exact this.symm
  · have hq2 : (y₁.den : ℚ) = (w : ℚ) ^ 3 := by exact_mod_cast hEw
    have := Rat.num_div_den y₁
    rw [hq2] at this
    exact this.symm

end NTKB.NZM
