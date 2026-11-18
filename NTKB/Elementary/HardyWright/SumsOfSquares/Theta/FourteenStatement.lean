/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TwelveProduct
import NTKB.Elementary.HardyWright.ArithmeticFunctions.LatticePoints
import Mathlib.NumberTheory.LegendreSymbol.ZModChar

/-!
# The formulas for `r₁₄(n)` and `r₁₆(n)` (the statements)

Beyond Hardy–Wright § 20.13 (which gives `r₆` and `r₈`). The two formulas were derived from the theta
series (no source text was available; the shapes below are checked by
computer for `n ≤ 59`), with `χ` the non-principal character modulo `4`:

* `61 r₁₄(n) = 4 (64 ∑_{d ∣ n} χ(n/d) d⁶ - ∑_{d ∣ n} χ(d) d⁶) + 1456 c₁₄(n)`, where `c₁₄(n)` is the
  coefficient of `qⁿ` (`q = e^{πiτ}`) in `θ(τ)² η(τ)¹²`, a cusp form of weight `7` on `Γ₀(4)` with
  character `χ`;
* `17 r₁₆(n) = 32 ∑_{d ∣ n} (-1)^{n+d} d⁷ + 512 c₁₆(n)`, `c₁₆(n)` the coefficient of `qⁿ` in
  `θ(τ)⁴ η(τ)¹²`, a cusp form of weight `8` on `Γ₀(4)`.

(`θ² η¹²` is the one cusp form of weight `7` here; `θ⁴ C = 4 θ² η¹²` for the weight-`5` form `C` of
`r₁₀`.) The statements are `GlaisherFourteenSquares` and `GlaisherSixteenSquares`; they are named
statements, assumed nowhere.
-/

namespace NTKB.HardyWright

open TwelveSquares

/-- `∑_{d ∣ n} χ(d) d⁶`, `χ` the non-principal character modulo `4`. -/
def fourteenSumA (n : ℕ) : ℤ := ∑ d ∈ n.divisors, (ZMod.χ₄ (d : ZMod 4) : ℤ) * (d : ℤ) ^ 6

/-- `∑_{d ∣ n} χ(n/d) d⁶`. -/
def fourteenSumB (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, (ZMod.χ₄ ((n / d : ℕ) : ZMod 4) : ℤ) * (d : ℤ) ^ 6

/-- `c₁₄(n)`: the coefficient of `qⁿ` in `θ² η¹²`, as the convolution of `r₂` with the coefficients
of `η¹²`. -/
noncomputable def cuspFourteenCoeff (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n + 1), (sumSquaresCount 2 i : ℤ) * etaTwelveCoeff (n - i)

/-- `∑_{d ∣ n} (-1)^{n+d} d⁷`. -/
def sixteenSum (n : ℕ) : ℤ := ∑ d ∈ n.divisors, (-1) ^ (n + d) * (d : ℤ) ^ 7

/-- `c₁₆(n)`: the coefficient of `qⁿ` in `θ⁴ η¹²`. -/
noncomputable def cuspSixteenCoeff (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n + 1), (sumSquaresCount 4 i : ℤ) * etaTwelveCoeff (n - i)

/-- **The formula for `r₁₄`** (named statement; the Eisenstein part plus the weight-`7` cusp form
`θ² η¹²`): for `n ≥ 1`,
`61 r₁₄(n) = 4 (64 ∑_{d ∣ n} χ(n/d) d⁶ - ∑_{d ∣ n} χ(d) d⁶) + 1456 c₁₄(n)`. -/
def GlaisherFourteenSquares : Prop :=
  ∀ n : ℕ, 0 < n →
    61 * (sumSquaresCount 14 n : ℤ) = 4 * (64 * fourteenSumB n - fourteenSumA n) +
      1456 * cuspFourteenCoeff n

/-- **The formula for `r₁₆`** (named statement): for `n ≥ 1`,
`17 r₁₆(n) = 32 ∑_{d ∣ n} (-1)^{n+d} d⁷ + 512 c₁₆(n)`. -/
def GlaisherSixteenSquares : Prop :=
  ∀ n : ℕ, 0 < n →
    17 * (sumSquaresCount 16 n : ℤ) = 32 * sixteenSum n + 512 * cuspSixteenCoeff n

end NTKB.HardyWright
