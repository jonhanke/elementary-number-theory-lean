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

/-!
# Proofs of the Hardy–Wright headline statements

The statements of `Challenge_HardyWright.lean`, proved by the library theorems. `lake comparator` checks that each
statement here is exactly the one in `Challenge_HardyWright.lean`.
-/

namespace NTKB.Headlines.HardyWright

open QuadraticAlgebra

theorem complex_euclidean_quadratic_fields {m : ℤ} (hm0 : m < 0) (hm : Squarefree m) :
    NTKB.HardyWright.IsNormEuclidean m ↔ m = -1 ∨ m = -2 ∨ m = -3 ∨ m = -7 ∨ m = -11 :=
  NTKB.HardyWright.isNormEuclidean_iff_of_neg hm0 hm

theorem cube_add_cube_eq_three_mul_cube {x y z : ℤ} (h : x ^ 3 + y ^ 3 = 3 * z ^ 3) : z = 0 :=
  NTKB.HardyWright.eq_zero_of_cube_add_cube_eq_three_mul_cube h

theorem jacobi_triple_product {x z : ℂ} (hx : ‖x‖ < 1) (hz : z ≠ 0) :
    Summable (fun n : ℤ ↦ x ^ (n ^ 2) * z ^ n) ∧
    HasProd (fun n : ℕ ↦ (1 - x ^ (2 * n + 2)) * (1 + x ^ (2 * n + 1) * z) *
      (1 + x ^ (2 * n + 1) * z⁻¹)) (∑' n : ℤ, x ^ (n ^ 2) * z ^ n) :=
  NTKB.HardyWright.jacobi_triple hx hz

theorem ramanujan_five (m : ℕ) : 5 ∣ Fintype.card (5 * m + 4).Partition :=
  NTKB.HardyWright.five_dvd_card_partition m

theorem ramanujan_seven (m : ℕ) : 7 ∣ Fintype.card (7 * m + 5).Partition :=
  NTKB.HardyWright.seven_dvd_card_partition m

theorem rogers_ramanujan_one {x : ℂ} (hx : ‖x‖ < 1) :
    HasProd (fun m : ℕ ↦ 1 / ((1 - x ^ (5 * m + 1)) * (1 - x ^ (5 * m + 4))))
      (∑' s : ℕ, x ^ (s ^ 2) / NTKB.Apostol.qPoch x s) :=
  NTKB.HardyWright.rogers_ramanujan_one hx

theorem rogers_ramanujan_two {x : ℂ} (hx : ‖x‖ < 1) :
    HasProd (fun m : ℕ ↦ 1 / ((1 - x ^ (5 * m + 2)) * (1 - x ^ (5 * m + 3))))
      (∑' s : ℕ, x ^ (s * (s + 1)) / NTKB.Apostol.qPoch x s) :=
  NTKB.HardyWright.rogers_ramanujan_two hx

theorem jacobi_four_squares {n : ℕ} (hn : 0 < n) :
    NTKB.HardyWright.sumFourSquaresCount n = 8 * ∑ d ∈ n.divisors.filter (fun d => ¬ 4 ∣ d), d :=
  NTKB.HardyWright.sumFourSquaresCount_eq hn

theorem three_squares (n : ℕ) :
    (∃ x y z : ℕ, n = x ^ 2 + y ^ 2 + z ^ 2) ↔ ∀ a m : ℕ, n ≠ 4 ^ a * (8 * m + 7) :=
  NTKB.HardyWright.exists_sq_add_sq_add_sq_iff n

theorem jacobi_eight_squares {n : ℕ} (hn : 0 < n) :
    (NTKB.HardyWright.sumSquaresCount 8 n : ℤ) = 16 * ∑ d ∈ n.divisors, (-1) ^ (n + d) * (d : ℤ) ^ 3 :=
  NTKB.HardyWright.sumSquaresCount_eight_eq hn

theorem jacobi_six_squares {n : ℕ} (hn : 0 < n) :
    (NTKB.HardyWright.sumSquaresCount 6 n : ℂ) =
      16 * ∑ d ∈ n.divisors, ((ZMod.χ₄ ((n / d : ℕ) : ZMod 4) : ℤ) : ℂ) * (d : ℂ) ^ 2 -
        4 * ∑ d ∈ n.divisors, ((ZMod.χ₄ (d : ZMod 4) : ℤ) : ℂ) * (d : ℂ) ^ 2 :=
  NTKB.HardyWright.sumSquaresCount_six_eq hn

theorem glaisher_twelve_squares :
    ∃ a : ℕ → ℤ, (∀ q : ℂ, ‖q‖ < 1 →
        HasSum (fun n => (a n : ℂ) * q ^ n) (q * ∏' m : ℕ, (1 - q ^ (2 * (m + 1))) ^ 12)) ∧
      ∀ n : ℕ, 0 < n → (NTKB.HardyWright.sumSquaresCount 12 n : ℤ) =
        8 * ∑ d ∈ n.divisors, (-1) ^ (n + d + n / d + 1) * (d : ℤ) ^ 5 + 16 * a n :=
  ⟨NTKB.HardyWright.TwelveSquares.etaTwelveCoeff, fun _ hq => NTKB.HardyWright.TwelveSquares.hasSum_etaTwelveCoeff hq,
    fun _ hn => NTKB.HardyWright.sumSquaresCount_twelve_eq hn⟩

end NTKB.Headlines.HardyWright
