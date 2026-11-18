/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TwelveProduct
import NTKB.Elementary.HardyWright.ArithmeticFunctions.LatticePoints
import Mathlib.NumberTheory.LegendreSymbol.ZModChar

/-!
# The formulas for `r₁₈(n)` and `r₂₀(n)` (the statements)

Beyond Hardy–Wright § 20.13 (which gives `r₆` and `r₈`). Source text unavailable: the two
formulas were derived from the theta series, by an exact fit of the coefficients of `qⁿ`,
`n ≤ 70`, in the span of the Eisenstein divisor sums and two cusp forms.
The cusp space here has dimension `2` in both weights (`9` and `10`), so each formula carries two
cusp forms. `χ` is the non-principal character modulo `4`, `q = e^{πiτ}`.

* `1385 r₁₈(n) = 4 (∑_{d ∣ n} χ(d) d⁸ + 256 ∑_{d ∣ n} χ(n/d) d⁸) + 48960 c₁₈(n) - 32 c₈(n)`, where
  `c₁₈(n)` is the coefficient of `qⁿ` in `θ(τ)⁶ η(τ)¹²` and `c₈(n) = ∑_{a² + b² = n} Re (a + bi)⁸` is
  the coefficient of `qⁿ` in the Gaussian lattice sum `C₈(τ) = ∑_{a, b ∈ ℤ} (a + bi)⁸ q^{a² + b²}`;
  both are cusp forms with the transformation laws of `θ¹⁸`. (`1385 = 5 · 277` and
  `L(9, χ) = 277 π⁹ / 8257536`.)
* `31 r₂₀(n) = 8 ∑_{d ∣ n} (-1)^{n + d + n/d + 1} d⁹ + 1296 c₂₀(n) - 16 c₂₀'(n)`, where `c₂₀(n)` is the
  coefficient of `qⁿ` in `θ⁸ η¹²` and `c₂₀'(n)` the coefficient of `qⁿ` in `θ² C₈`.

The statements are `EighteenSquaresFormula` and `TwentySquaresFormula`; they are named
statements, assumed nowhere.
-/

namespace NTKB.HardyWright

open TwelveSquares

/-- `∑_{d ∣ n} χ(d) d⁸`, `χ` the non-principal character modulo `4`. -/
def eighteenSumA (n : ℕ) : ℤ := ∑ d ∈ n.divisors, (ZMod.χ₄ (d : ZMod 4) : ℤ) * (d : ℤ) ^ 8

/-- `∑_{d ∣ n} χ(n/d) d⁸`. -/
def eighteenSumB (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, (ZMod.χ₄ ((n / d : ℕ) : ZMod 4) : ℤ) * (d : ℤ) ^ 8

/-- `Re (a + bi)⁸ = a⁸ - 28 a⁶ b² + 70 a⁴ b⁴ - 28 a² b⁶ + b⁸`. -/
def octicRe (a b : ℤ) : ℤ := a ^ 8 - 28 * a ^ 6 * b ^ 2 + 70 * a ^ 4 * b ^ 4 - 28 * a ^ 2 * b ^ 6 + b ^ 8

/-- `c₈(n) = ∑_{a² + b² = n} Re (a + bi)⁸`, the coefficient of `qⁿ` in
`C₈(τ) = ∑_{a, b ∈ ℤ} (a + bi)⁸ q^{a² + b²}`. -/
def octicCoeff (n : ℕ) : ℤ :=
  ∑ v ∈ (Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).filter
      (fun v : ℤ × ℤ => v.1 ^ 2 + v.2 ^ 2 = n), octicRe v.1 v.2

/-- `c₁₈(n)`: the coefficient of `qⁿ` in `θ⁶ η¹²`, as the convolution of `r₆` with the coefficients
of `η¹²`. -/
noncomputable def cuspEighteenCoeff (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n + 1), (sumSquaresCount 6 i : ℤ) * etaTwelveCoeff (n - i)

/-- `∑_{d ∣ n} (-1)^{n + d + n/d + 1} d⁹`. -/
def twentySum (n : ℕ) : ℤ := ∑ d ∈ n.divisors, (-1) ^ (n + d + n / d + 1) * (d : ℤ) ^ 9

/-- `c₂₀(n)`: the coefficient of `qⁿ` in `θ⁸ η¹²`. -/
noncomputable def cuspTwentyCoeff (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n + 1), (sumSquaresCount 8 i : ℤ) * etaTwelveCoeff (n - i)

/-- `c₂₀'(n)`: the coefficient of `qⁿ` in `θ² C₈`. -/
noncomputable def cuspTwentyCoeff' (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n + 1), (sumSquaresCount 2 i : ℤ) * octicCoeff (n - i)

/-- **The formula for `r₁₈`** (named statement; the Eisenstein part plus the two weight-`9` cusp
forms `θ⁶ η¹²` and `C₈`): for `n ≥ 1`,
`1385 r₁₈(n) = 4 (∑_{d ∣ n} χ(d) d⁸ + 256 ∑_{d ∣ n} χ(n/d) d⁸) + 48960 c₁₈(n) - 32 c₈(n)`. -/
def EighteenSquaresFormula : Prop :=
  ∀ n : ℕ, 0 < n →
    1385 * (sumSquaresCount 18 n : ℤ) = 4 * (eighteenSumA n + 256 * eighteenSumB n) +
      48960 * cuspEighteenCoeff n - 32 * octicCoeff n

/-- **The formula for `r₂₀`** (named statement; the Eisenstein part plus the two weight-`10` cusp
forms `θ⁸ η¹²` and `θ² C₈`): for `n ≥ 1`,
`31 r₂₀(n) = 8 ∑_{d ∣ n} (-1)^{n + d + n/d + 1} d⁹ + 1296 c₂₀(n) - 16 c₂₀'(n)`. -/
def TwentySquaresFormula : Prop :=
  ∀ n : ℕ, 0 < n →
    31 * (sumSquaresCount 20 n : ℤ) = 8 * twentySum n + 1296 * cuspTwentyCoeff n -
      16 * cuspTwentyCoeff' n

end NTKB.HardyWright
