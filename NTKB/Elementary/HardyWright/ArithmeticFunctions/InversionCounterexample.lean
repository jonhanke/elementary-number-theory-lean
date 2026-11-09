/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.Lemma
import NTKB.Attr

/-!
# Hardy–Wright, Theorems 268 and 269: the conclusion fails for `0 < x < 1`

The book states Theorems 268 and 269 with the conclusion "for all positive x". Its own footnote
(an empty sum is `0`, so `G(x) = 0` for `0 < x < 1`) shows that for `0 < x < 1` the conclusion of
Theorem 268 reads `F(x) = 0`, which the hypothesis does not give; the book's proof uses
`∑_{d ∣ k} μ(d) = [k = 1]` with `k` running over `1, …, [x]`, which needs `[x] ≥ 1`.
The proved forms are `moebius_inversion_floor` and `moebius_inversion_floor_converse`
(conclusion for `x ≥ 1`). Counterexamples, both at `x = 1/2`:

* Theorem 268 with `F = 1`, `G(x) = [x]`;
* Theorem 269 with `G = 1`, `F(x) = ∑_{n ≤ x} μ(n)`.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius

namespace NTKB.HardyWright

private lemma floor_half : ⌊(1 / 2 : ℝ)⌋₊ = 0 := Nat.floor_eq_zero.mpr (by norm_num)

/-- Theorem 268 with the conclusion for all positive `x`, as printed, is false. -/
theorem not_moebius_inversion_floor_all_pos :
    ¬ ∀ F G : ℝ → ℝ, (∀ x > 0, G x = ∑ n ∈ Ioc 0 ⌊x⌋₊, F (x / n)) →
      ∀ x > 0, F x = ∑ n ∈ Ioc 0 ⌊x⌋₊, μ n • G (x / n) := by
  intro h
  have := h (fun _ => 1) (fun x => ∑ _n ∈ Ioc 0 ⌊x⌋₊, (1 : ℝ)) (fun _ _ => rfl) (1 / 2)
    (by norm_num)
  simp only [floor_half, Finset.Ioc_self, Finset.sum_empty] at this
  exact one_ne_zero this

/-- Theorem 269 with the conclusion for all positive `x`, as printed, is false. -/
theorem not_moebius_inversion_floor_converse_all_pos :
    ¬ ∀ F G : ℝ → ℝ, (∀ x > 0, F x = ∑ n ∈ Ioc 0 ⌊x⌋₊, μ n • G (x / n)) →
      ∀ x > 0, G x = ∑ n ∈ Ioc 0 ⌊x⌋₊, F (x / n) := by
  intro h
  have := h (fun x => ∑ n ∈ Ioc 0 ⌊x⌋₊, μ n • (1 : ℝ)) (fun _ => 1) (fun _ _ => rfl) (1 / 2)
    (by norm_num)
  simp only [floor_half, Finset.Ioc_self, Finset.sum_empty] at this
  exact one_ne_zero this

end NTKB.HardyWright
