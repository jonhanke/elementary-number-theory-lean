/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Analysis.Real.Sqrt
import NTKB.Attr

/-!
# Euclidean numbers are algebraic (Hardy–Wright, § 11.5)

Hardy and Wright observe that every length constructible with ruler and compasses ("Euclidean number")
is of *real quadratic type*: it is obtained from rational numbers by a finite number of rational
operations and extractions of square roots of positive numbers; and that every such number is algebraic
(stated without proof). We formalize the second, algebraic, statement and the worked example (11.5.2).
The first statement is about geometric constructions and is not formalized here.
-/

namespace NTKB.HardyWright

/-- Numbers of *real quadratic type* (Hardy–Wright § 11.5): the smallest set of reals containing the
rationals and closed under `+`, `-`, `×`, `⁻¹` and square roots (of nonnegative numbers; `√x = 0` for
`x < 0` in Mathlib). -/
inductive IsRealQuadraticType : ℝ → Prop
  | rat (q : ℚ) : IsRealQuadraticType q
  | add {x y : ℝ} : IsRealQuadraticType x → IsRealQuadraticType y → IsRealQuadraticType (x + y)
  | neg {x : ℝ} : IsRealQuadraticType x → IsRealQuadraticType (-x)
  | mul {x y : ℝ} : IsRealQuadraticType x → IsRealQuadraticType y → IsRealQuadraticType (x * y)
  | inv {x : ℝ} : IsRealQuadraticType x → IsRealQuadraticType x⁻¹
  | sqrt {x : ℝ} : IsRealQuadraticType x → IsRealQuadraticType √x

/-- **§ 11.5.** Every number of real quadratic type (in particular every Euclidean number) is algebraic. -/
@[kb "hardywright2008" "§ 11.5, p. 204"]
theorem IsRealQuadraticType.isAlgebraic {x : ℝ} (h : IsRealQuadraticType x) : IsAlgebraic ℚ x := by
  induction h with
  | rat q => exact isAlgebraic_algebraMap (A := ℝ) q
  | add _ _ hx hy =>
    exact (isAlgebraic_iff_isIntegral.mpr
      ((isAlgebraic_iff_isIntegral.mp hx).add (isAlgebraic_iff_isIntegral.mp hy)))
  | neg _ hx =>
    exact isAlgebraic_iff_isIntegral.mpr (isAlgebraic_iff_isIntegral.mp hx).neg
  | mul _ _ hx hy =>
    exact (isAlgebraic_iff_isIntegral.mpr
      ((isAlgebraic_iff_isIntegral.mp hx).mul (isAlgebraic_iff_isIntegral.mp hy)))
  | inv _ hx => exact IsAlgebraic.inv_iff.mpr hx
  | @sqrt x _ hx =>
    rcases le_or_gt 0 x with h0 | h0
    · exact IsAlgebraic.of_pow two_pos (by rw [Real.sq_sqrt h0]; exact hx)
    · rw [Real.sqrt_eq_zero'.mpr h0.le]; exact isAlgebraic_zero

/-- **(11.5.2).** `x = √(11 + 2√7) - √(11 - 2√7)` satisfies `x⁴ - 44x² + 112 = 0`. -/
@[kb "hardywright2008" "§ 11.5, p. 204"]
theorem sqrt_example :
    (√(11 + 2 * √7) - √(11 - 2 * √7)) ^ 4 - 44 * (√(11 + 2 * √7) - √(11 - 2 * √7)) ^ 2 + 112 = 0 := by
  have ht : √(7 : ℝ) ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have ht0 : 0 ≤ √(7 : ℝ) := Real.sqrt_nonneg _
  have ht3 : √(7 : ℝ) < 3 := by nlinarith
  have hy : √(11 + 2 * √7) ^ 2 = 11 + 2 * √7 := Real.sq_sqrt (by linarith)
  have hz : √(11 - 2 * √7) ^ 2 = 11 - 2 * √7 := Real.sq_sqrt (by linarith)
  have hyz : (√(11 + 2 * √7) * √(11 - 2 * √7)) ^ 2 = 93 := by
    rw [mul_pow, hy, hz]; nlinarith
  set y := √(11 + 2 * √7)
  set z := √(11 - 2 * √7)
  have hx2 : (y - z) ^ 2 = 22 - 2 * (y * z) := by linear_combination hy + hz
  rw [show (y - z) ^ 4 = ((y - z) ^ 2) ^ 2 by ring, hx2]
  linear_combination 4 * hyz

end NTKB.HardyWright
