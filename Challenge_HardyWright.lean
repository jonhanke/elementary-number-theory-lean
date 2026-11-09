/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import NTKB.Elementary.HardyWright.QuadraticFields.NormEuclidean
import NTKB.Elementary.HardyWright.QuadraticFields.Cubes
import NTKB.Elementary.HardyWright.Partitions.Basic
import NTKB.Elementary.HardyWright.Partitions.Ramanujan
import NTKB.Elementary.HardyWright.Partitions.RogersRamanujan
import NTKB.Elementary.HardyWright.SumsOfSquares.Jacobi.FourSquares

/-!
# Headline statements of elementary-number-theory-lean 0.1.0: Hardy and Wright

G. H. Hardy and E. M. Wright, *An Introduction to the Theory of Numbers* (6th edition, 2008). The main results of
the library for this book, one theorem each, with every proof a deliberate `sorry`: to check what is claimed, read
this file. `Solution_HardyWright.lean` proves the same statements from the library, and `lake comparator`
(configured by `comparator/HardyWright.json`) checks that each proved statement is exactly the one here and uses
only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

Each statement is the library's statement, copied. The statements were not yet reviewed by a human (see the README).

## Definitions used

Besides Mathlib, the statements use these definitions of the library; a reader checking a statement should check
these too:

* `NTKB.HardyWright.IsNormEuclidean` (Hardy–Wright's property (E) of `k(√m)`, § 14.7, with Mathlib's
  `QuadraticAlgebra ℚ m 0` for `k(√m)`)
* `NTKB.Apostol.qPoch` (the `q`-Pochhammer symbol `(q; q)_n = ∏_{k=1}^n (1 - q^k)`)
* `NTKB.HardyWright.sumFourSquaresCount` (`r₄(n)`, the number of `(a, b, c, d) ∈ ℤ⁴` with
  `a² + b² + c² + d² = n`)
-/

namespace NTKB.Headlines.HardyWright

open QuadraticAlgebra

/-- **The complex Euclidean quadratic fields** (Theorem 246). For a squarefree `m < 0`, the field `k(√m)` is
Euclidean (for integers `γ, γ₁` of `k(√m)` with `γ₁ ≠ 0` there is an integer `κ` with
`|N(γ - κγ₁)| < |N γ₁|`) exactly when `m` is `-1`, `-2`, `-3`, `-7` or `-11`. Mathlib has the Euclidean algorithm
of the Gaussian integers (`m = -1`) and that `ℤ[ζ₃]` is a principal ideal domain (`m = -3`), not the other cases nor
the exclusion of every other `m`. -/
theorem complex_euclidean_quadratic_fields {m : ℤ} (hm0 : m < 0) (hm : Squarefree m) :
    NTKB.HardyWright.IsNormEuclidean m ↔ m = -1 ∨ m = -2 ∨ m = -3 ∨ m = -7 ∨ m = -11 := by
  sorry

/-- **`x³ + y³ = 3z³`** (Theorem 232): the equation has no solution in integers except the trivial ones with
`z = 0`. Mathlib has Fermat's last theorem for exponent 3 (`fermatLastTheoremThree`), whose descent in `ℤ[ζ₃]`
does not give this equation. -/
theorem cube_add_cube_eq_three_mul_cube {x y z : ℤ} (h : x ^ 3 + y ^ 3 = 3 * z ^ 3) : z = 0 := by
  sorry

/-- **Jacobi's triple product identity** (Theorem 352). For `‖x‖ < 1` and `z ≠ 0`,
`∏_{n ≥ 1} (1 - x^{2n})(1 + x^{2n-1} z)(1 + x^{2n-1} z⁻¹) = ∑_{n ∈ ℤ} x^{n²} zⁿ`, the series converging
absolutely. Mathlib has Euler's pentagonal number theorem; Tau Ceti has the theta product `qTheta` with its
functional equations, but neither has the series expansion of the product. -/
theorem jacobi_triple_product {x z : ℂ} (hx : ‖x‖ < 1) (hz : z ≠ 0) :
    Summable (fun n : ℤ ↦ x ^ (n ^ 2) * z ^ n) ∧
    HasProd (fun n : ℕ ↦ (1 - x ^ (2 * n + 2)) * (1 + x ^ (2 * n + 1) * z) *
      (1 + x ^ (2 * n + 1) * z⁻¹)) (∑' n : ℤ, x ^ (n ^ 2) * z ^ n) := by
  sorry

/-- **Ramanujan's congruence modulo 5** (Theorem 359): `5 ∣ p(5m + 4)`. -/
theorem ramanujan_five (m : ℕ) : 5 ∣ Fintype.card (5 * m + 4).Partition := by
  sorry

/-- **Ramanujan's congruence modulo 7** (Theorem 360): `7 ∣ p(7m + 5)`. -/
theorem ramanujan_seven (m : ℕ) : 7 ∣ Fintype.card (7 * m + 5).Partition := by
  sorry

/-- **The first Rogers–Ramanujan identity** (Theorem 362). For `‖x‖ < 1`,
`∑_{s ≥ 0} x^{s²} / ((1 - x) ⋯ (1 - x^s)) = ∏_{m ≥ 0} 1 / ((1 - x^{5m+1})(1 - x^{5m+4}))`. -/
theorem rogers_ramanujan_one {x : ℂ} (hx : ‖x‖ < 1) :
    HasProd (fun m : ℕ ↦ 1 / ((1 - x ^ (5 * m + 1)) * (1 - x ^ (5 * m + 4))))
      (∑' s : ℕ, x ^ (s ^ 2) / NTKB.Apostol.qPoch x s) := by
  sorry

/-- **The second Rogers–Ramanujan identity** (Theorem 363). For `‖x‖ < 1`,
`∑_{s ≥ 0} x^{s(s+1)} / ((1 - x) ⋯ (1 - x^s)) = ∏_{m ≥ 0} 1 / ((1 - x^{5m+2})(1 - x^{5m+3}))`. -/
theorem rogers_ramanujan_two {x : ℂ} (hx : ‖x‖ < 1) :
    HasProd (fun m : ℕ ↦ 1 / ((1 - x ^ (5 * m + 2)) * (1 - x ^ (5 * m + 3))))
      (∑' s : ℕ, x ^ (s * (s + 1)) / NTKB.Apostol.qPoch x s) := by
  sorry

/-- **Jacobi's four-square theorem** (Theorem 386): for `n ≥ 1`, the number `r₄(n)` of representations of `n` as
`a² + b² + c² + d²` with integers `a, b, c, d` (order and signs counted) is `8` times the sum of the divisors of `n`
not divisible by `4`. Mathlib has Lagrange's theorem (`Nat.sum_four_squares`: `r₄(n) > 0`), not the count. -/
theorem jacobi_four_squares {n : ℕ} (hn : 0 < n) :
    NTKB.HardyWright.sumFourSquaresCount n = 8 * ∑ d ∈ n.divisors.filter (fun d => ¬ 4 ∣ d), d := by
  sorry

end NTKB.Headlines.HardyWright
