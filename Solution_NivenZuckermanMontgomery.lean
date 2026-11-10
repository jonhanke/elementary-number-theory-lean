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
# Proofs of the Niven–Zuckerman–Montgomery headline statements

The statements of `Challenge_NivenZuckermanMontgomery.lean`, proved by the library theorems. `lake comparator`
checks that each statement here is exactly the one in `Challenge_NivenZuckermanMontgomery.lean`.
-/

namespace NTKB.Headlines.NivenZuckermanMontgomery

open NTKB.HardyWright GenContFract Filter Topology Matrix
open scoped Pointwise

theorem proper_representation_iff {n : ℤ} (hn : n ≠ 0) (d : ℤ) :
    (∃ a b c x y : ℤ, b ^ 2 - 4 * a * c = d ∧ IsCoprime x y ∧ a * x ^ 2 + b * x * y + c * y ^ 2 = n) ↔
      ∃ s, s ^ 2 ≡ d [ZMOD 4 * |n|] := by
  rw [← NTKB.NZM.exists_proper_rep_iff hn d]
  constructor
  · rintro ⟨a, b, c, x, y, hd, hxy, hf⟩
    exact ⟨(a, b, c), x, y, hd, hxy, hf⟩
  · rintro ⟨f, x, y, hd, hxy, hf⟩
    exact ⟨f.1, f.2.1, f.2.2, x, y, hd, hxy, hf⟩

theorem linear_system_local_global {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hreal : ∃ x : Fin n → ℝ, (A.map (Int.cast : ℤ → ℝ)) *ᵥ x = fun i => (b i : ℝ))
    (hmod : ∀ q : ℕ, 0 < q → ∃ x : Fin n → ℤ, ∀ i, Int.ModEq q ((A *ᵥ x) i) (b i)) :
    ∃ x : Fin n → ℤ, A *ᵥ x = b :=
  NTKB.NZM.exists_int_solution_of_real_of_forall_modEq A b hreal hmod

theorem quartic_eq_square (x y : ℤ) :
    x ^ 4 + x ^ 3 + x ^ 2 + x + 1 = y ^ 2 ↔
      (x = -1 ∧ (y = 1 ∨ y = -1)) ∨ (x = 0 ∧ (y = 1 ∨ y = -1)) ∨
        (x = 3 ∧ (y = 11 ∨ y = -11)) :=
  NTKB.NZM.quartic_eq_sq_iff x y

theorem rational_points_y_sq_eq_x_cube_sub_four_x (x y : ℚ) :
    y ^ 2 = x ^ 3 - 4 * x ↔ (x, y) ∈ ({(0, 0), (2, 0), (-2, 0)} : Set (ℚ × ℚ)) :=
  NTKB.NZM.rational_solutions_y_sq_x_cubed_sub_four_x x y

theorem galois_purely_periodic {D : ℕ} {P Q : ℤ} {a : ℕ → ℤ} (hD : ¬IsSquare D) (hQ : Q ≠ 0)
    (ha : ∀ i, 1 ≤ i → 0 < a i)
    (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 ((P + √(D : ℝ)) / Q))) :
    (∃ r, 1 ≤ r ∧ ∀ i, a (i + r) = a i) ↔
      1 < (P + √(D : ℝ)) / Q ∧ -1 < (P - √(D : ℝ)) / Q ∧ (P - √(D : ℝ)) / Q < 0 :=
  NTKB.NZM.purelyPeriodic_iff hD hQ ha hx

theorem eq_convergent_of_sq_sub_mul_sq {D : ℕ} {a : ℕ → ℤ} (hD : ¬IsSquare D) (ha : ∀ i, 1 ≤ i → 0 < a i)
    (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 √(D : ℝ))) {N s t : ℤ}
    (hN : |(N : ℝ)| < √(D : ℝ)) (hs : 0 < s) (ht : 0 < t) (hcop : IsCoprime s t)
    (h : s ^ 2 - D * t ^ 2 = N) :
    ∃ n, (cf (fun i ↦ (a i : ℝ))).nums n = s ∧ (cf (fun i ↦ (a i : ℝ))).dens n = t :=
  NTKB.NZM.eq_convergent_of_sq_sub_mul_sq hD ha hx hN hs ht hcop h

theorem omega_maximal_order {ε : ℝ} (hε : 0 < ε) :
    (∃ n₀ : ℕ, ∀ n : ℕ, n₀ < n →
      (ArithmeticFunction.cardDistinctFactors n : ℝ) < (1 + ε) * Real.log n / Real.log (Real.log n)) ∧
    {n : ℕ | (1 - ε) * Real.log n / Real.log (Real.log n) <
      (ArithmeticFunction.cardDistinctFactors n : ℝ)}.Infinite :=
  ⟨NTKB.NZM.omega_lt_of_large hε, NTKB.NZM.omega_gt_infinitely_often hε⟩

theorem partition_bounds {n : ℕ} (hn : 4 ≤ n) :
    (2 : ℝ) ^ √(n : ℝ) < Fintype.card (Nat.Partition n) ∧
      (Fintype.card (Nat.Partition n) : ℝ) < Real.exp (Real.pi * √(2 / 3) * √(n : ℝ)) :=
  NTKB.NZM.two_rpow_sqrt_lt_card_partition_lt_exp hn

theorem exists_squarefree_add (n : ℕ) (hn : 1 < n) :
    ∃ a b, 0 < a ∧ 0 < b ∧ Squarefree a ∧ Squarefree b ∧ a + b = n :=
  NTKB.NZM.exists_squarefree_add n hn

theorem mann_alpha_beta (A B : Set ℕ) [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    [DecidablePred (· ∈ A + B)] (hA : 0 ∈ A) (hB : 0 ∈ B) :
    min 1 (schnirelmannDensity A + schnirelmannDensity B) ≤ schnirelmannDensity (A + B) :=
  NTKB.NZM.theorem_11_10 A B hA hB

end NTKB.Headlines.NivenZuckermanMontgomery
