/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.ArithmeticFunctions.LatticePoints
import Mathlib.NumberTheory.LegendreSymbol.ZModChar

/-!
# Liouville's formula for `r₁₀(n)` (the statement)

Liouville's formula (see Grosswald, *Representations of Integers as Sums of Squares*, 1985), beyond
Hardy–Wright § 20.13 (which gives `r₆` and `r₈`): for `n ≥ 1`,

`5 r₁₀(n) = 4 ∑_{d ∣ n} χ(d) d⁴ + 64 ∑_{d ∣ n} χ(n/d) d⁴ + 8 ∑_{a ∈ ℤ[i], N(a) = n} a⁴`,

`χ` the non-principal character modulo `4`. The last sum is real; with `a = x + iy` its terms are
`Re (x + iy)⁴ = x⁴ - 6x²y² + y⁴` (`liouvilleCusp`). The formula was checked numerically for
`n ≤ 40`. It is recorded here as the statement `LiouvilleTenSquares`, proved in `TenSquares.lean`
(`liouvilleTenSquares`); the key step is the transformation law of the weight-`5` theta series
`∑_{a ∈ ℤ[i]} a⁴ q^{N(a)}` under `τ ↦ -1/τ` (`TenCusp.lean`). Glaisher's formula for `r₁₂` is proved
(`sumSquaresCount_twelve_eq`).
-/

namespace NTKB.HardyWright

/-- `∑_{a ∈ ℤ[i], N(a) = n} a⁴`, written with `a = x + iy` as `∑_{x² + y² = n} (x⁴ - 6x²y² + y⁴)`. -/
def liouvilleCusp (n : ℕ) : ℤ :=
  ∑ v ∈ ((Finset.Icc (-(n : ℤ)) n) ×ˢ (Finset.Icc (-(n : ℤ)) n)).filter
      (fun v : ℤ × ℤ => v.1 ^ 2 + v.2 ^ 2 = n),
    (v.1 ^ 4 - 6 * v.1 ^ 2 * v.2 ^ 2 + v.2 ^ 4)

/-- `∑_{d ∣ n} χ(d) d⁴`. -/
def liouvilleSumA (n : ℕ) : ℤ := ∑ d ∈ n.divisors, (ZMod.χ₄ (d : ZMod 4) : ℤ) * (d : ℤ) ^ 4

/-- `∑_{d ∣ n} χ(n/d) d⁴`. -/
def liouvilleSumB (n : ℕ) : ℤ := ∑ d ∈ n.divisors, (ZMod.χ₄ ((n / d : ℕ) : ZMod 4) : ℤ) * (d : ℤ) ^ 4

/-- **Liouville's formula for `r₁₀`** (the statement; proved as `liouvilleTenSquares`):
`5 r₁₀(n) = 4 ∑_{d ∣ n} χ(d) d⁴ + 64 ∑_{d ∣ n} χ(n/d) d⁴ + 8 ∑_{N(a) = n} a⁴` for `n ≥ 1`. -/
def LiouvilleTenSquares : Prop :=
  ∀ n : ℕ, 0 < n →
    5 * (sumSquaresCount 10 n : ℤ) = 4 * liouvilleSumA n + 64 * liouvilleSumB n + 8 * liouvilleCusp n

lemma liouvilleCusp_one : liouvilleCusp 1 = 4 := by decide

end NTKB.HardyWright
