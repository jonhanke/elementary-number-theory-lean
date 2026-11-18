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
import NTKB.Elementary.HardyWright.SumsOfSquares.ThreeSquares.Theorem
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.EightSquares
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.SixSquares
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TwelveSquares
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TenSquares
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.FourteenSquares
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.SixteenSquares
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.EighteenSquares

/-!
# Headline statements of elementary-number-theory-lean: Hardy and Wright

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
* `NTKB.HardyWright.sumSquaresCount` (`r_k(n)`, the number of `z ∈ ℤᵏ` with `z₁² + ⋯ + z_k² = n`)

The first eight statements are those of release 0.1.0; `three_squares` and `jacobi_eight_squares` are new in
release 0.3.0; `jacobi_six_squares` and `glaisher_twelve_squares` are new in release 0.4.0 (besides `sumSquaresCount`
they use only Mathlib's definitions: `ZMod.χ₄`, `HasSum`, `tprod`). New in release 0.4.1:
`liouville_ten_squares` (Liouville's formula for `r₁₀(n)`, stated as a conjecture of the library in 0.4.0 and now
proved; besides `sumSquaresCount` it uses only Mathlib's definitions).
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

/-- **The three-square theorem** (Section 20.10; Legendre, Gauss). A natural number is a sum of three squares if
and only if it is not of the form `4ᵃ(8m + 7)`. The book states it without proof; the library proves it by
Dirichlet's method (ternary forms of determinant 1, Minkowski's convex body theorem and Dirichlet's theorem on primes
in progressions). Mathlib has the two- and four-square theorems; neither Mathlib nor Tau Ceti has this one. -/
theorem three_squares (n : ℕ) :
    (∃ x y z : ℕ, n = x ^ 2 + y ^ 2 + z ^ 2) ↔ ∀ a m : ℕ, n ≠ 4 ^ a * (8 * m + 7) := by
  sorry

/-- **Jacobi's eight-square theorem** (Section 20.13, formula (20.13.2)): for `n ≥ 1`, the number `r₈(n)` of
`z ∈ ℤ⁸` with `z₁² + ⋯ + z₈² = n` is `16 ∑_{d ∣ n} (-1)^{n+d} d³`. The book states it without proof; the library
proves `θ⁸ = (E₄(τ/2) - 2E₄(τ) + 16E₄(2τ))/15` with modular forms of level one. Neither Mathlib nor Tau Ceti has
this count. -/
theorem jacobi_eight_squares {n : ℕ} (hn : 0 < n) :
    (NTKB.HardyWright.sumSquaresCount 8 n : ℤ) = 16 * ∑ d ∈ n.divisors, (-1) ^ (n + d) * (d : ℤ) ^ 3 := by
  sorry

/-- **Jacobi's six-square theorem** (Section 20.13, formula (20.13.1)): for `n ≥ 1`, the number `r₆(n)` of
`z ∈ ℤ⁶` with `z₁² + ⋯ + z₆² = n` is `16 ∑_{d ∣ n} χ(n/d) d² - 4 ∑_{d ∣ n} χ(d) d²`, with `χ` the non-principal
character modulo 4 (Mathlib's `ZMod.χ₄`). The book states it without proof; the library proves a theta identity for
`θ⁶` with an Eisenstein-type lattice sum of weight 3 by modular forms of level one. Neither Mathlib nor Tau Ceti has this count. -/
theorem jacobi_six_squares {n : ℕ} (hn : 0 < n) :
    (NTKB.HardyWright.sumSquaresCount 6 n : ℂ) =
      16 * ∑ d ∈ n.divisors, ((ZMod.χ₄ ((n / d : ℕ) : ZMod 4) : ℤ) : ℂ) * (d : ℂ) ^ 2 -
        4 * ∑ d ∈ n.divisors, ((ZMod.χ₄ (d : ZMod 4) : ℤ) : ℂ) * (d : ℂ) ^ 2 := by
  sorry

/-- **Glaisher's twelve-square theorem** (beyond the book; J. W. L. Glaisher, 1907; see E. Grosswald,
*Representations of Integers as Sums of Squares*, 1985). Let `a(n)` be the coefficients of
`q ∏_{m ≥ 1} (1 - q^{2m})¹² = η(2z)¹²` (`q = e^{2πiz}`), the cusp form of weight 6 and level 4. Then for `n ≥ 1`
`r₁₂(n) = 8 ∑_{d ∣ n} (-1)^{n + d + n/d + 1} d⁵ + 16 a(n)`. The coefficients `a(n)` are determined by the power
series identity on the unit disc. The library proves `κ θ¹² = L + c η(2z)¹²` with a lattice sum `L` of weight 6 by
modular forms of level one. Neither Mathlib nor Tau Ceti has this count (Tau Ceti has theta
series of lattices as modular forms, not this identity). -/
theorem glaisher_twelve_squares :
    ∃ a : ℕ → ℤ, (∀ q : ℂ, ‖q‖ < 1 →
        HasSum (fun n => (a n : ℂ) * q ^ n) (q * ∏' m : ℕ, (1 - q ^ (2 * (m + 1))) ^ 12)) ∧
      ∀ n : ℕ, 0 < n → (NTKB.HardyWright.sumSquaresCount 12 n : ℤ) =
        8 * ∑ d ∈ n.divisors, (-1) ^ (n + d + n / d + 1) * (d : ℤ) ^ 5 + 16 * a n := by
  sorry

/-- **Liouville's ten-square theorem** (beyond the book, which gives `r₆` and `r₈` in § 20.13; J. Liouville, 1866;
see E. Grosswald, *Representations of Integers as Sums of Squares*, 1985; new in 0.4.1). For `n ≥ 1`,
`5 r₁₀(n) = 4 ∑_{d ∣ n} χ(d) d⁴ + 64 ∑_{d ∣ n} χ(n/d) d⁴ + 8 ∑_{a ∈ ℤ[i], N(a) = n} a⁴`, with `χ` the non-principal
character modulo 4 (Mathlib's `ZMod.χ₄`); the last sum, over `a = x + iy` with `x² + y² = n`, is written as
`∑ (x⁴ - 6x²y² + y⁴)`. The library proves the transformation law of the weight-5 theta series `∑_{a ∈ ℤ[i]} a⁴ q^{N(a)}`
under `τ ↦ -1/τ` from Mathlib's functional equation of the two-variable Jacobi theta function, then the identity by
modular forms of level one, as for `r₆` and `r₁₂`. Neither Mathlib nor Tau Ceti has this count. -/
theorem liouville_ten_squares {n : ℕ} (hn : 0 < n) :
    5 * (NTKB.HardyWright.sumSquaresCount 10 n : ℤ) =
      4 * ∑ d ∈ n.divisors, (ZMod.χ₄ (d : ZMod 4) : ℤ) * (d : ℤ) ^ 4 +
        64 * ∑ d ∈ n.divisors, (ZMod.χ₄ ((n / d : ℕ) : ZMod 4) : ℤ) * (d : ℤ) ^ 4 +
        8 * ∑ v ∈ ((Finset.Icc (-(n : ℤ)) n) ×ˢ (Finset.Icc (-(n : ℤ)) n)).filter
            (fun v : ℤ × ℤ => v.1 ^ 2 + v.2 ^ 2 = n),
          (v.1 ^ 4 - 6 * v.1 ^ 2 * v.2 ^ 2 + v.2 ^ 4) := by
  sorry

/-- **The fourteen-square formula** (beyond the book, which gives `r₆` and `r₈` in § 20.13; Glaisher, 1907; see
E. Grosswald, *Representations of Integers as Sums of Squares*, 1985, Chapter 9; new in 0.5.0). Let `a(n)` be the
coefficients of `q ∏_{m ≥ 1} (1 - q^{2m})¹² = η(τ)¹²` (`q = e^{πiτ}`), as in `glaisher_twelve_squares`, and
`c(n) = ∑_{i ≤ n} r₂(i) a(n - i)` the coefficients of `θ² η¹²`, a cusp form of weight 7 on `Γ₀(4)`. Then for `n ≥ 1`,
`61 r₁₄(n) = 4 (64 ∑_{d ∣ n} χ(n/d) d⁶ - ∑_{d ∣ n} χ(d) d⁶) + 1456 c(n)`, with `χ` the non-principal character modulo
4 (Mathlib's `ZMod.χ₄`). The constants were derived by the library's authors from the theta series (not compared
with Grosswald's text; see the README, Known restrictions). The proof is the level-one method of `r₁₀` and `r₁₂`.
UPSTREAM_HW_R14 -/
theorem glaisher_fourteen_squares :
    ∃ a : ℕ → ℤ, (∀ q : ℂ, ‖q‖ < 1 →
        HasSum (fun n => (a n : ℂ) * q ^ n) (q * ∏' m : ℕ, (1 - q ^ (2 * (m + 1))) ^ 12)) ∧
      ∀ n : ℕ, 0 < n → 61 * (NTKB.HardyWright.sumSquaresCount 14 n : ℤ) =
        4 * (64 * ∑ d ∈ n.divisors, (ZMod.χ₄ ((n / d : ℕ) : ZMod 4) : ℤ) * (d : ℤ) ^ 6 -
          ∑ d ∈ n.divisors, (ZMod.χ₄ (d : ZMod 4) : ℤ) * (d : ℤ) ^ 6) +
        1456 * ∑ i ∈ Finset.range (n + 1), (NTKB.HardyWright.sumSquaresCount 2 i : ℤ) * a (n - i) := by
  sorry

/-- **The sixteen-square formula** (beyond the book; Glaisher, 1907; see E. Grosswald, *Representations of
Integers as Sums of Squares*, 1985, Chapter 9; new in 0.5.0). With `a(n)` as in `glaisher_fourteen_squares` and
`c(n) = ∑_{i ≤ n} r₄(i) a(n - i)` the coefficients of `θ⁴ η¹²`, a cusp form of weight 8 on `Γ₀(4)`, for `n ≥ 1`
`17 r₁₆(n) = 32 ∑_{d ∣ n} (-1)^{n+d} d⁷ + 512 c(n)`. As for `r₁₄`, the constants are the library's derivation (see
the README, Known restrictions). Neither Mathlib nor Tau Ceti has this count. -/
theorem glaisher_sixteen_squares :
    ∃ a : ℕ → ℤ, (∀ q : ℂ, ‖q‖ < 1 →
        HasSum (fun n => (a n : ℂ) * q ^ n) (q * ∏' m : ℕ, (1 - q ^ (2 * (m + 1))) ^ 12)) ∧
      ∀ n : ℕ, 0 < n → 17 * (NTKB.HardyWright.sumSquaresCount 16 n : ℤ) =
        32 * ∑ d ∈ n.divisors, (-1) ^ (n + d) * (d : ℤ) ^ 7 +
        512 * ∑ i ∈ Finset.range (n + 1), (NTKB.HardyWright.sumSquaresCount 4 i : ℤ) * a (n - i) := by
  sorry

/-- **The eighteen-square formula** (beyond the book, which gives `r₆` and `r₈` in § 20.13; new in 0.6.0). Let
`a(n)` be the coefficients of `q ∏_{m ≥ 1} (1 - q^{2m})¹² = η(τ)¹²` (`q = e^{πiτ}`), as in `glaisher_twelve_squares`,
`c₁₈(n) = ∑_{i ≤ n} r₆(i) a(n - i)` the coefficients of `θ⁶ η¹²`, and `c₈(n) = ∑_{x² + y² = n} Re (x + iy)⁸` the
coefficients of `∑_{x, y ∈ ℤ} (x + iy)⁸ q^{x² + y²}`; both are cusp forms of weight 9 on `Γ₀(4)` with the
transformation laws of `θ¹⁸`, and they span the cusp space. Then for `n ≥ 1`,
`1385 r₁₈(n) = 4 (∑_{d ∣ n} χ(d) d⁸ + 256 ∑_{d ∣ n} χ(n/d) d⁸) + 48960 c₁₈(n) - 32 c₈(n)`, with `χ` the non-principal
character modulo 4 (Mathlib's `ZMod.χ₄`). The shape and the constants were derived by the library's authors from the
theta series (not compared with the literature; see the README, Known restrictions). The proof is the level-one
method of `r₁₀` to `r₁₆`. Neither Mathlib nor Tau Ceti has this count. -/
theorem eighteen_squares :
    ∃ a : ℕ → ℤ, (∀ q : ℂ, ‖q‖ < 1 →
        HasSum (fun n => (a n : ℂ) * q ^ n) (q * ∏' m : ℕ, (1 - q ^ (2 * (m + 1))) ^ 12)) ∧
      ∀ n : ℕ, 0 < n → 1385 * (NTKB.HardyWright.sumSquaresCount 18 n : ℤ) =
        4 * (∑ d ∈ n.divisors, (ZMod.χ₄ (d : ZMod 4) : ℤ) * (d : ℤ) ^ 8 +
          256 * ∑ d ∈ n.divisors, (ZMod.χ₄ ((n / d : ℕ) : ZMod 4) : ℤ) * (d : ℤ) ^ 8) +
        48960 * ∑ i ∈ Finset.range (n + 1), (NTKB.HardyWright.sumSquaresCount 6 i : ℤ) * a (n - i) -
        32 * ∑ v ∈ (Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).filter
            (fun v : ℤ × ℤ => v.1 ^ 2 + v.2 ^ 2 = n),
          (v.1 ^ 8 - 28 * v.1 ^ 6 * v.2 ^ 2 + 70 * v.1 ^ 4 * v.2 ^ 4 - 28 * v.1 ^ 2 * v.2 ^ 6 + v.2 ^ 8) := by
  sorry

end NTKB.Headlines.HardyWright
