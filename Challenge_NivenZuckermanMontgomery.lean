/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import NTKB.Elementary.NZM.QuadraticForms
import NTKB.Elementary.NZM.LinearSystems
import NTKB.Elementary.NZM.Diophantine
import NTKB.Elementary.NZM.CubicFourX
import NTKB.Elementary.NZM.Galois
import NTKB.Elementary.NZM.Pell
import NTKB.Elementary.NZM.OmegaBound
import NTKB.Elementary.NZM.PartitionBounds
import NTKB.Elementary.NZM.SquarefreeSums
import NTKB.Elementary.NZM.Mann

/-!
# Headline statements of elementary-number-theory-lean 0.2.0: Niven, Zuckerman and Montgomery

I. Niven, H. S. Zuckerman and H. L. Montgomery, *An Introduction to the Theory of Numbers* (5th edition, 1991).
The main results of the library for this book, one theorem each, with every proof a deliberate `sorry`: to check
what is claimed, read this file. `Solution_NivenZuckermanMontgomery.lean` proves the same statements from the
library, and `lake comparator` (configured by `comparator/NivenZuckermanMontgomery.json`) checks that each proved
statement is exactly the one here and uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

Each statement is the library's statement, copied, except that the binary quadratic form of Theorem 3.13 is written
out with its coefficients and the two halves of Theorem 8.30 are joined in one statement. None of these results is
in Mathlib, Tau Ceti or PrimeNumberTheoremAnd (searched by name and by statement; related results are cited in the
docstrings). The statements were not yet reviewed by a human (see the README).

## Definitions used

Besides Mathlib, the statements use one definition of the library; a reader checking a statement should check it
too:

* `NTKB.HardyWright.cf` (the simple continued fraction `a₀ + 1/(a₁ + 1/(a₂ + ⋯))` with quotients `a₀, a₁, …`, as
  a Mathlib generalized continued fraction `GenContFract` whose partial numerators are all `1`; Mathlib's
  `GenContFract.convs`, `nums` and `dens` are its convergents `hₙ/kₙ`, their numerators `hₙ` and denominators `kₙ`)
-/

namespace NTKB.Headlines.NivenZuckermanMontgomery

open NTKB.HardyWright GenContFract Filter Topology Matrix
open scoped Pointwise

/-- **Proper representations by binary quadratic forms** (Theorem 3.13). Let `n ≠ 0` and `d` be integers. Some
binary quadratic form `ax² + bxy + cy²` of discriminant `b² - 4ac = d` properly represents `n` (that is, at a
relatively prime pair `x, y`) if and only if `d` is a square modulo `4|n|`. Tau Ceti has binary quadratic forms,
their discriminants and that a primitive form properly represents an integer prime to a given one, not this
criterion. -/
theorem proper_representation_iff {n : ℤ} (hn : n ≠ 0) (d : ℤ) :
    (∃ a b c x y : ℤ, b ^ 2 - 4 * a * c = d ∧ IsCoprime x y ∧ a * x ^ 2 + b * x * y + c * y ^ 2 = n) ↔
      ∃ s, s ^ 2 ≡ d [ZMOD 4 * |n|] := by
  sorry

/-- **The local-global principle for systems of linear equations** (Theorem 5.2). If a system `A x = b` of linear
equations with integer coefficients has a real solution and is solvable modulo every positive integer `q`, then it
has an integral solution. Mathlib has the Smith normal form of submodules of free modules over a principal ideal
domain (the proof uses it), not this theorem. -/
theorem linear_system_local_global {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hreal : ∃ x : Fin n → ℝ, (A.map (Int.cast : ℤ → ℝ)) *ᵥ x = fun i => (b i : ℝ))
    (hmod : ∀ q : ℕ, 0 < q → ∃ x : Fin n → ℤ, ∀ i, Int.ModEq q ((A *ᵥ x) i) (b i)) :
    ∃ x : Fin n → ℤ, A *ᵥ x = b := by
  sorry

/-- **A quartic equation** (Theorem 5.9). The integral solutions of `x⁴ + x³ + x² + x + 1 = y²` are exactly
`x = -1` and `x = 0` with `y = ±1`, and `x = 3` with `y = ±11`. -/
theorem quartic_eq_square (x y : ℤ) :
    x ^ 4 + x ^ 3 + x ^ 2 + x + 1 = y ^ 2 ↔
      (x = -1 ∧ (y = 1 ∨ y = -1)) ∨ (x = 0 ∧ (y = 1 ∨ y = -1)) ∨
        (x = 3 ∧ (y = 11 ∨ y = -11)) := by
  sorry

/-- **The rational points of `y² = x³ - 4x`** (Theorem 5.24): the only rational solutions are `(0, 0)`, `(2, 0)`
and `(-2, 0)` (with the point at infinity, the curve has four rational points; equivalently, `2` is not a
congruent number). Mathlib has Weierstrass curves and their group law and Fermat's last theorem for the exponent 4,
not this equation. -/
theorem rational_points_y_sq_eq_x_cube_sub_four_x (x y : ℚ) :
    y ^ 2 = x ^ 3 - 4 * x ↔ (x, y) ∈ ({(0, 0), (2, 0), (-2, 0)} : Set (ℚ × ℚ)) := by
  sorry

/-- **Galois's theorem on purely periodic continued fractions** (Theorem 7.20). Let `ξ = (P + √D)/Q` be a real
quadratic irrational (`P, Q` integers, `Q ≠ 0`, `D` a natural number which is not a square), `ξ' = (P - √D)/Q` its
conjugate, and `ξ = ⟨a₀, a₁, a₂, …⟩` its simple continued fraction (integers `aᵢ`, positive for `i ≥ 1`, whose
convergents tend to `ξ`). The expansion is purely periodic if and only if `ξ > 1` and `-1 < ξ' < 0`. Mathlib has
generalized continued fractions and the continued fraction of a real number, not periodicity. -/
theorem galois_purely_periodic {D : ℕ} {P Q : ℤ} {a : ℕ → ℤ} (hD : ¬IsSquare D) (hQ : Q ≠ 0)
    (ha : ∀ i, 1 ≤ i → 0 < a i)
    (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 ((P + √(D : ℝ)) / Q))) :
    (∃ r, 1 ≤ r ∧ ∀ i, a (i + r) = a i) ↔
      1 < (P + √(D : ℝ)) / Q ∧ -1 < (P - √(D : ℝ)) / Q ∧ (P - √(D : ℝ)) / Q < 0 := by
  sorry

/-- **Small values of `x² - dy²` come from convergents** (Theorem 7.24). Let `d` be a natural number which is not a
square and `√d = ⟨a₀, a₁, …⟩` its simple continued fraction. If `|N| < √d`, every solution of `s² - d t² = N` in
relatively prime positive integers `s, t` is `s = hₙ`, `t = kₙ` for a convergent `hₙ/kₙ` of `√d`. Mathlib has the
solutions of Pell's equation `x² - dy² = 1` (`Pell.Solution₁`), not their relation to continued fractions. -/
theorem eq_convergent_of_sq_sub_mul_sq {D : ℕ} {a : ℕ → ℤ} (hD : ¬IsSquare D) (ha : ∀ i, 1 ≤ i → 0 < a i)
    (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 √(D : ℝ))) {N s t : ℤ}
    (hN : |(N : ℝ)| < √(D : ℝ)) (hs : 0 < s) (ht : 0 < t) (hcop : IsCoprime s t)
    (h : s ^ 2 - D * t ^ 2 = N) :
    ∃ n, (cf (fun i ↦ (a i : ℝ))).nums n = s ∧ (cf (fun i ↦ (a i : ℝ))).dens n = t := by
  sorry

/-- **The maximal order of `ω(n)`** (Theorem 8.30). For every `ε > 0`, the number `ω(n)` of distinct prime factors
of `n` satisfies `ω(n) < (1 + ε) log n / log log n` for all large `n`, and `ω(n) > (1 - ε) log n / log log n` for
infinitely many `n`. Mathlib has `ω` (`ArithmeticFunction.cardDistinctFactors`) and Chebyshev's bounds, not this. -/
theorem omega_maximal_order {ε : ℝ} (hε : 0 < ε) :
    (∃ n₀ : ℕ, ∀ n : ℕ, n₀ < n →
      (ArithmeticFunction.cardDistinctFactors n : ℝ) < (1 + ε) * Real.log n / Real.log (Real.log n)) ∧
    {n : ℕ | (1 - ε) * Real.log n / Real.log (Real.log n) <
      (ArithmeticFunction.cardDistinctFactors n : ℝ)}.Infinite := by
  sorry

/-- **Bounds for the partition function** (Theorem 10.12): `2^√n < p(n) < exp(π √(2/3) √n)` for `n ≥ 4`. Mathlib
has partitions (`Nat.Partition`) and their generating function, not these bounds. -/
theorem partition_bounds {n : ℕ} (hn : 4 ≤ n) :
    (2 : ℝ) ^ √(n : ℝ) < Fintype.card (Nat.Partition n) ∧
      (Fintype.card (Nat.Partition n) : ℝ) < Real.exp (Real.pi * √(2 / 3) * √(n : ℝ)) := by
  sorry

/-- **Sums of two squarefree numbers** (Theorem 11.2): every integer `n > 1` is the sum of two squarefree positive
integers. -/
theorem exists_squarefree_add (n : ℕ) (hn : 1 < n) :
    ∃ a b, 0 < a ∧ 0 < b ∧ Squarefree a ∧ Squarefree b ∧ a + b = n := by
  sorry

/-- **Mann's `α + β` theorem** (Theorem 11.10). For sets `A`, `B` of natural numbers containing `0`, the
Schnirelmann density of `A + B` is at least `min(1, d(A) + d(B))`. Mathlib has the Schnirelmann density
(`schnirelmannDensity`) and the case `d(A) + d(B) ≥ 1` (then `A + B = ℕ`); Mann's theorem is listed there as a
to-do. -/
theorem mann_alpha_beta (A B : Set ℕ) [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    [DecidablePred (· ∈ A + B)] (hA : 0 ∈ A) (hB : 0 ∈ B) :
    min 1 (schnirelmannDensity A + schnirelmannDensity B) ≤ schnirelmannDensity (A + B) := by
  sorry

end NTKB.Headlines.NivenZuckermanMontgomery
