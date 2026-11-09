/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.PrimeCounting
import Aesop.BuiltinRules
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Basify
import NTKB.Attr

/-!
# Hardy–Wright: three printed statements that are false as printed

Recorded in `docs/updates-and-errata.md`; the correct forms are proved elsewhere in this library.

* Theorem 20 (§ 2.6, pdf page 40) prints `π(x) ≥ log x / (2 log 2)` for `x ≥ 1`; with `π(x)` the number
  of primes `≤ x` for real `x`, this fails at `x = 3/2` (the book's proof takes `N(x) = x`, so `x` an
  integer). Correct form: `NTKB.HardyWright.primeCounting_ge_log_div_and_nth_prime_lt` (with `⌊x⌋`).
* (13.7.11) (§ 13.7, pdf page 279) prints the same polynomial for `u` as for `x`; the identity
  `x⁴ + y⁴ = u⁴ + v⁴` then fails at `a = b = 1`. Correct form (sign of `3a²b⁵` in `u` negative):
  `NTKB.HardyWright.euler_fourth_powers`.
* Notes to Chapter XIII (pdf page 282) state the abc conjecture without the coprimality of `a, b`;
  so stated it is false (`a = b = 2^k`). The named hypothesis `NTKB.HardyWright.AbcConjecture` has it.
-/

namespace NTKB.HardyWright

/-- Theorem 20 as printed (real `x ≥ 1`) is false: `x = 3/2`. -/
theorem not_primeCounting_ge_log_div_real :
    ¬ ∀ x : ℝ, 1 ≤ x → Real.log x / (2 * Real.log 2) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  intro h
  have h1 := h (3 / 2) (by norm_num)
  have hfl : ⌊(3 / 2 : ℝ)⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (by norm_num)]
    norm_num
  rw [hfl] at h1
  have hpi : Nat.primeCounting 1 = 0 := by decide
  rw [hpi, Nat.cast_zero] at h1
  have hl : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)
  have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have : 0 < Real.log (3 / 2 : ℝ) / (2 * Real.log 2) := by positivity
  linarith

/-- (13.7.11) as printed (`u` equal to `x`) is not an identity: `a = b = 1`. -/
theorem not_euler_fourth_powers_printed :
    ¬ ∀ a b : ℤ,
      (a ^ 7 + a ^ 5 * b ^ 2 - 2 * a ^ 3 * b ^ 4 + 3 * a ^ 2 * b ^ 5 + a * b ^ 6) ^ 4 +
        (a ^ 6 * b - 3 * a ^ 5 * b ^ 2 - 2 * a ^ 4 * b ^ 3 + a ^ 2 * b ^ 5 + b ^ 7) ^ 4 =
      (a ^ 7 + a ^ 5 * b ^ 2 - 2 * a ^ 3 * b ^ 4 + 3 * a ^ 2 * b ^ 5 + a * b ^ 6) ^ 4 +
        (a ^ 6 * b + 3 * a ^ 5 * b ^ 2 - 2 * a ^ 4 * b ^ 3 + a ^ 2 * b ^ 5 + b ^ 7) ^ 4 := by
  intro h
  have := h 1 1
  norm_num at this

/-- The abc conjecture as printed in the notes to Chapter XIII (no coprimality) is false:
already for `ε = 1`, `a = b = 2^k`, `c = 2^(k+1)` have `r(abc) = 2`. -/
theorem not_abc_without_coprime :
    ¬ ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ a b c : ℕ, 0 < a → 0 < b → a + b = c →
      (c : ℝ) ≤ K * (((a * b * c).primeFactors.prod id : ℕ) : ℝ) ^ (1 + ε) := by
  intro h
  obtain ⟨K, hK⟩ := h 1 one_pos
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (4 * K) (by norm_num : (1 : ℝ) < 2)
  have hc := hK (2 ^ k) (2 ^ k) (2 ^ (k + 1)) (by positivity) (by positivity) (by ring)
  have hprod : 2 ^ k * 2 ^ k * 2 ^ (k + 1) = 2 ^ (3 * k + 1) := by ring
  rw [hprod, Nat.primeFactors_prime_pow (by omega) Nat.prime_two] at hc
  norm_num at hc
  have : (2 : ℝ) ^ k < 2 ^ (k + 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
  linarith

end NTKB.HardyWright
