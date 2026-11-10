/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Attr
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Convergents of `1/x`; Hurwitz's lemma (Niven–Zuckerman–Montgomery, §§ 7.5–7.6)

* Theorem 7.15: for a real number `x > 1`, the `n`-th convergent of `1/x` is the reciprocal of the
  `(n - 1)`-st convergent of `x`. Convergents are Mathlib's `Real.convergent` (which agree with the
  convergents of the simple continued fraction, `Real.convs_eq_convergent`).
* Lemma 7.16: if `x > 1` and `x + 1/x < √5`, then `x < (√5 + 1)/2` and `1/x > (√5 - 1)/2`.
-/

namespace NTKB.NZM

/-- **Theorem 7.15.** If `x > 1` is real, the `n`-th convergent of `1/x` is the reciprocal of the
`(n - 1)`-st convergent of `x` (and the `0`-th convergent of `1/x` is `0`). -/
@[kb "nivenzuckermanmontgomery" "Thm 7.15, p. 339"]
theorem convergent_one_div {x : ℝ} (hx : 1 < x) (n : ℕ) :
    (1 / x).convergent (n + 1) = (x.convergent n)⁻¹ ∧ (1 / x).convergent 0 = 0 := by
  have h0 : 0 < 1 / x := by positivity
  have h1 : 1 / x < 1 := by rw [div_lt_one (by linarith)]; exact hx
  have hfl : ⌊1 / x⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨h0.le, h1⟩
  have hfr : Int.fract (1 / x) = 1 / x := Int.fract_eq_self.mpr ⟨h0.le, h1⟩
  refine ⟨?_, by rw [Real.convergent_zero, hfl]; simp⟩
  rw [Real.convergent_succ, hfl, hfr, one_div, inv_inv]
  simp

/-- **Lemma 7.16.** If `x > 1` and `x + 1/x < √5`, then `x < (√5 + 1)/2` and `1/x > (√5 - 1)/2`. -/
@[kb "nivenzuckermanmontgomery" "Lemma 7.16, p. 342"]
theorem lt_golden_of_add_inv_lt {x : ℝ} (hx : 1 < x) (h : x + 1 / x < √5) :
    x < (√5 + 1) / 2 ∧ (√5 - 1) / 2 < 1 / x := by
  have hs : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < √5 := by positivity
  have hx0 : 0 < x := by linarith
  have hq : x ^ 2 - √5 * x + 1 < 0 := by
    have : x * (x + 1 / x) < x * √5 := mul_lt_mul_of_pos_left h hx0
    rw [mul_add, mul_one_div_cancel hx0.ne'] at this
    nlinarith
  -- `x² - √5 x + 1 = (x - (√5 + 1)/2)(x - (√5 - 1)/2)`
  have hfac : x ^ 2 - √5 * x + 1 = (x - (√5 + 1) / 2) * (x - (√5 - 1) / 2) := by
    linear_combination (-1 / 4 : ℝ) * hs
  have hlo : (√5 - 1) / 2 < x := by
    have : √5 < 3 := by nlinarith
    linarith
  have hup : x < (√5 + 1) / 2 := by
    by_contra hc
    push Not at hc
    have : 0 ≤ (x - (√5 + 1) / 2) * (x - (√5 - 1) / 2) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  refine ⟨hup, ?_⟩
  -- `1/x > 2/(√5 + 1) = (√5 - 1)/2`
  rw [lt_div_iff₀ hx0]
  have : (√5 - 1) / 2 * ((√5 + 1) / 2) = 1 := by linear_combination (1 / 4 : ℝ) * hs
  nlinarith
