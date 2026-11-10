/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.RingTheory.PowerSeries.Derivative
import NTKB.Attr
import NTKB.Analytic.Apostol.Partitions.Euler
import NTKB.Analytic.Apostol.Partitions.SigmaRecursion

/-!
# A recurrence for `σ(n)` (Niven–Zuckerman–Montgomery, § 10.1)

* **Theorem 10.11.** For `n ≥ 1`,
  `σ(n) - σ(n-1) - σ(n-2) + σ(n-5) + σ(n-7) - ⋯ = (-1)^{j+1} n` if `n = j(3j ± 1)/2`, and `0`
  otherwise (the sum extending as long as the arguments are positive).

With `e_m = [x^m] ∏ (1 - x^k)` (`PowerSeries.pentagonalSeries ℤ`, so `e_m = (-1)^j` if
`m = j(3j - 1)/2` for an integer `j`, and `e_m = 0` otherwise, by Euler's pentagonal number theorem)
the left side is `∑_{k=1}^n σ(k) e_{n-k}`, and the theorem says `∑_{k=1}^n σ(k) e_{n-k} = -n e_n`.

Proof: with `P = ∑ p(n) xⁿ`, `E = ∑ e_n xⁿ` and `S = ∑ σ(k) xᵏ` we have `P E = 1` (Euler) and
`x P' = S P` (Apostol, `n p(n) = ∑ σ(k) p(n-k)`). Differentiating `P E = 1` gives
`P (x E' + S E) = 0`, and multiplying by `E` gives `x E' + S E = 0`.
-/

open Finset PowerSeries
open scoped ArithmeticFunction.sigma

namespace NTKB.NZM

/-- `∑_{k ≥ 1} σ(k) xᵏ` (the coefficient at `0` is `σ(0) = 0`). -/
private noncomputable def sigmaPowerSeries : PowerSeries ℤ :=
  PowerSeries.mk fun k ↦ (σ 1 k : ℤ)

private theorem sum_range_succ_eq_sum_Icc (g : ℕ → ℤ) (h0 : g 0 = 0) (n : ℕ) :
    ∑ k ∈ range (n + 1), g k = ∑ k ∈ Icc 1 n, g k := by
  symm
  refine Finset.sum_subset (fun k hk ↦ ?_) (fun k hk hk' ↦ ?_)
  · simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢
    omega
  · simp only [Finset.mem_Icc, Finset.mem_range] at hk hk'
    have : k = 0 := by omega
    subst this
    exact h0

private theorem coeff_sigmaPowerSeries_mul (F : PowerSeries ℤ) (n : ℕ) :
    coeff n (sigmaPowerSeries * F) =
      ∑ k ∈ Icc 1 n, (σ 1 k : ℤ) * coeff (n - k) F := by
  rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j ↦ coeff i sigmaPowerSeries * coeff j F)]
  simp only [sigmaPowerSeries, coeff_mk]
  exact sum_range_succ_eq_sum_Icc _ (by simp) n

private theorem Icc_one_eq_Ioc_zero (n : ℕ) : Icc 1 n = Ioc 0 n := by
  ext k
  simp only [Finset.mem_Icc, Finset.mem_Ioc]
  omega

/-- `x P' = S P`: the power series form of `n p(n) = ∑_{k=1}^n σ(k) p(n - k)`. -/
private theorem X_mul_derivative_partitionSeries :
    X * d⁄dX (NTKB.Apostol.partitionSeries ℤ) =
      sigmaPowerSeries * NTKB.Apostol.partitionSeries ℤ := by
  ext n
  cases n with
  | zero =>
    rw [coeff_zero_X_mul, coeff_sigmaPowerSeries_mul, Finset.Icc_eq_empty (show ¬ (1 ≤ 0) by norm_num),
      Finset.sum_empty]
  | succ m =>
    rw [coeff_succ_X_mul, coeff_derivative, coeff_sigmaPowerSeries_mul]
    have hA := NTKB.Apostol.mul_card_partition_eq_sum_sigma (m + 1)
    have hA' : (((m + 1 : ℕ) : ℤ)) * (Fintype.card (m + 1).Partition : ℤ) =
        ∑ k ∈ Icc 1 (m + 1), (σ 1 k : ℤ) * (Fintype.card (m + 1 - k).Partition : ℤ) := by
      rw [Icc_one_eq_Ioc_zero]
      exact_mod_cast hA
    push_cast at hA'
    simp only [NTKB.Apostol.partitionSeries, coeff_mk]
    linear_combination hA'

/-- **Theorem 10.11.** For `n ≥ 1`, `∑_{k=1}^n σ(k) e_{n-k} = -n e_n`, where `e_m` is the
coefficient of `x^m` in `∏ (1 - x^k)`, i.e. the `m`-th coefficient of `pentagonalSeries ℤ`
(`e_m = (-1)^j` if `m = j(3j-1)/2`, else `0`). In the book's notation this reads
`σ(n) - σ(n-1) - σ(n-2) + σ(n-5) + σ(n-7) - ⋯ = -n e_n`. -/
@[kb "nivenzuckermanmontgomery" "Thm 10.11, p. 460"]
theorem sum_sigma_mul_pentagonal (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Icc 1 n, (σ 1 k : ℤ) * coeff (n - k) (pentagonalSeries ℤ) =
      -(n : ℤ) * coeff n (pentagonalSeries ℤ) := by
  set P := NTKB.Apostol.partitionSeries ℤ with hP
  set E := pentagonalSeries ℤ with hE
  have hPE : P * E = 1 := NTKB.Apostol.partitionSeries_mul_pentagonalSeries ℤ
  have hxP := X_mul_derivative_partitionSeries
  rw [← hP] at hxP
  have hleib : d⁄dX (P * E) = P * d⁄dX E + E * d⁄dX P := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  have hD : d⁄dX (P * E) = 0 := by
    rw [hPE]
    exact derivative_one
  have key : P * (X * d⁄dX E + sigmaPowerSeries * E) = 0 := by
    calc P * (X * d⁄dX E + sigmaPowerSeries * E)
        = X * (P * d⁄dX E + E * d⁄dX P) + E * (sigmaPowerSeries * P - X * d⁄dX P) := by ring
      _ = 0 := by
        rw [← hleib, hD, ← hxP, sub_self]
        ring
  have hH : X * d⁄dX E + sigmaPowerSeries * E = 0 := by
    calc X * d⁄dX E + sigmaPowerSeries * E
        = E * (P * (X * d⁄dX E + sigmaPowerSeries * E)) := by
          rw [← mul_assoc, mul_comm E P, hPE, one_mul]
      _ = 0 := by rw [key, mul_zero]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := congrArg (coeff (m + 1)) hH
  rw [map_add, coeff_succ_X_mul, coeff_derivative, coeff_sigmaPowerSeries_mul, map_zero] at h
  push_cast
  linear_combination h

/-- **Theorem 10.11** (explicit form, `n = j(3j - 1)/2` with `j ≠ 0` an integer; this covers both
`j(3j ± 1)/2`): the sum equals `(-1)^{j+1} n`. -/
@[kb "nivenzuckermanmontgomery" "Thm 10.11, p. 460"]
theorem sum_sigma_mul_pentagonal_of_pentagonal (j : ℤ) (hj : 1 ≤ pentagonal j) :
    ∑ k ∈ Icc 1 (pentagonal j), (σ 1 k : ℤ) * coeff (pentagonal j - k) (pentagonalSeries ℤ) =
      -(j.negOnePow : ℤ) * (pentagonal j : ℤ) := by
  rw [sum_sigma_mul_pentagonal _ hj, coeff_pentagonalSeries_pentagonal, Int.cast_id]; ring

/-- **Theorem 10.11** (explicit form, `n` not of the form `j(3j ± 1)/2`): the sum is `0`. -/
@[kb "nivenzuckermanmontgomery" "Thm 10.11, p. 460"]
theorem sum_sigma_mul_pentagonal_of_not_pentagonal (n : ℕ) (hn : 1 ≤ n)
    (h : n ∉ Set.range pentagonal) :
    ∑ k ∈ Icc 1 n, (σ 1 k : ℤ) * coeff (n - k) (pentagonalSeries ℤ) = 0 := by
  rw [sum_sigma_mul_pentagonal n hn, coeff_pentagonalSeries_eq_zero ℤ h, mul_zero]

end NTKB.NZM
