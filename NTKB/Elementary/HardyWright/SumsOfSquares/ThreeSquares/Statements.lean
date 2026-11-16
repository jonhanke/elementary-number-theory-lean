/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.NumberTheory.Divisors
import NTKB.Elementary.HardyWright.SumsOfSquares.Waring
import NTKB.Elementary.SpecialValues.FundamentalGaussSum
import NTKB.Elementary.HardyWright.ArithmeticFunctions.LatticePoints

/-!
# Hardy–Wright, §§ 20.10 and 20.13: statements

Statements fixed before the proofs.

* § 20.10 (Legendre–Gauss three-square theorem): `n` is a sum of three squares if and only if it is
  not of the form `4ᵃ(8m + 7)`. The book states it without proof; the necessity half is
  `not_isSumOfPowers_two_three`.
* § 20.13 (Jacobi): `r₈(n) = 16 ∑_{d ∣ n} (-1)^{n+d} d³` and
  `r₆(n) = 16 ∑_{d ∣ n} χ(n/d) d² - 4 ∑_{d ∣ n} χ(d) d²`, with `χ` the non-principal character
  modulo `4`. The book states both without proof.

`sumSquaresCount k n` (`ArithmeticFunctions/LatticePoints.lean`) counts `x ∈ ℤᵏ` with
`x₀² + ⋯ + x_{k-1}² = n` (order and signs counted), as the book's `r_k(n)`.
-/

open Finset

namespace NTKB.HardyWright

/-- The right side of Jacobi's formula for `r₈(n)` (Hardy–Wright (20.13.2)). -/
def jacobiEightSum (n : ℕ) : ℤ := 16 * ∑ d ∈ n.divisors, (-1) ^ (n + d) * (d : ℤ) ^ 3

/-- The right side of Jacobi's formula for `r₆(n)` (Hardy–Wright (20.13.1)), with `χ` the
non-principal character modulo `4` (`chi4`, valued in `ℂ`). -/
noncomputable def jacobiSixSum (n : ℕ) : ℂ :=
  16 * ∑ d ∈ n.divisors, chi4 (n / d : ℕ) * (d : ℂ) ^ 2 - 4 * ∑ d ∈ n.divisors, chi4 d * (d : ℂ) ^ 2

/-- The statement of Hardy–Wright (20.13.1) (Jacobi's formula for `r₆`). Proved as
`NTKB.HardyWright.jacobiSixSquares` (`Theta/SixSquares.lean`). -/
def JacobiSixSquares : Prop := ∀ n : ℕ, 0 < n → (sumSquaresCount 6 n : ℂ) = jacobiSixSum n

end NTKB.HardyWright
