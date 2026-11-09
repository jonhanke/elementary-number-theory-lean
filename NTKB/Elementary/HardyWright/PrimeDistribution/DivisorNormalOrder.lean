/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.PrimeDistribution.NormalOrder

/-!
# Hardy–Wright, Theorem 432: the normal order of `log d(n)`

[hardywright2008, § 22.13, Theorem 432]. For every `ε > 0`, almost all `n` satisfy
`(log n)^((1 - ε) log 2) < d(n) < (log n)^((1 + ε) log 2)`.

The proof is the book's: `2^ω(n) ≤ d(n) ≤ 2^Ω(n)` and Theorem 431 for `ω` and `Ω`.
-/

open Finset ArithmeticFunction Real Filter
open scoped Topology ArithmeticFunction.omega ArithmeticFunction.Omega

namespace NTKB.HardyWright

/-- `2^ω(n) ≤ d(n)` [hardywright2008, (22.13.1)]. -/
theorem two_pow_cardDistinctFactors_le_card_divisors {n : ℕ} (hn : n ≠ 0) :
    2 ^ ω n ≤ #n.divisors := by
  rw [Nat.card_divisors hn, cardDistinctFactors_eq_card_primeFactors, ← Finset.prod_const]
  refine Finset.prod_le_prod fun p hp ↦ ?_
  have : 0 < n.factorization p :=
    (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hp)
  omega

/-- `d(n) ≤ 2^Ω(n)` [hardywright2008, (22.13.1)]. -/
theorem card_divisors_le_two_pow_cardFactors {n : ℕ} (hn : n ≠ 0) :
    #n.divisors ≤ 2 ^ Ω n := by
  rw [Nat.card_divisors hn, cardFactors_eq_sum_factorization, Finsupp.sum,
    Nat.support_factorization, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod fun p _ ↦ Nat.lt_two_pow_self

private lemma two_pow_eq_rpow (k : ℕ) {n : ℕ} (hn : 1 < Real.log n) :
    (2 : ℝ) ^ k = Real.log n ^ ((k : ℝ) / Real.log (Real.log n) * Real.log 2) := by
  have hL : 0 < Real.log (Real.log n) := Real.log_pos hn
  rw [Real.rpow_def_of_pos (by linarith), ← Real.rpow_natCast,
    Real.rpow_def_of_pos two_pos]
  congr 1
  field_simp

/-- **Theorem 432.** For every `ε > 0` the number of `n ≤ x` *not* satisfying
`(log n)^((1 - ε) log 2) < d(n) < (log n)^((1 + ε) log 2)` is `o(x)`. -/
@[kb "hardywright2008" "Thm 432, p. 497"]
theorem tendsto_card_normalOrder_card_divisors {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun x : ℝ ↦
      (((Ioc 0 ⌊x⌋₊).filter fun n : ℕ ↦ ¬ (Real.log n ^ ((1 - ε) * Real.log 2) < #n.divisors ∧
        (#n.divisors : ℝ) < Real.log n ^ ((1 + ε) * Real.log 2))).card : ℝ) / x)
      atTop (𝓝 0) := by
  have hε2 : 0 < ε / 2 := by linarith
  have hA := tendsto_card_normalOrder_cardDistinctFactors hε2
  have hB := tendsto_card_normalOrder_cardFactors hε2
  have hC : Tendsto (fun x : ℝ ↦ (2 : ℝ) / x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hsum := (hA.add hB).add hC
  rw [add_zero, add_zero] at hsum
  refine squeeze_zero' (Eventually.of_forall fun x ↦ ?_) ?_ hsum
  · rcases le_or_gt x 0 with hx | hx
    · rw [Nat.floor_of_nonpos hx]; simp
    · positivity
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [← add_div, ← add_div]
  refine div_le_div_of_nonneg_right ?_ hx.le
  set S := Ioc 0 ⌊x⌋₊
  set A := S.filter fun n : ℕ ↦ ε / 2 * Real.log (Real.log n) <
    |(ω n : ℝ) - Real.log (Real.log n)|
  set B := S.filter fun n : ℕ ↦ ε / 2 * Real.log (Real.log n) <
    |(Ω n : ℝ) - Real.log (Real.log n)|
  have hsub : (S.filter fun n : ℕ ↦ ¬ (Real.log n ^ ((1 - ε) * Real.log 2) < #n.divisors ∧
      (#n.divisors : ℝ) < Real.log n ^ ((1 + ε) * Real.log 2))) ⊆ A ∪ B ∪ {1, 2} := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hnS, hbad⟩ := hn
    by_contra hnot
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, A, B,
      Finset.mem_filter, not_or, not_and, not_lt] at hnot
    obtain ⟨⟨hωn, hΩn⟩, hn1, hn2⟩ := hnot
    have hωn := hωn hnS
    have hΩn := hΩn hnS
    have hn0 : n ≠ 0 := by have := (Finset.mem_Ioc.1 hnS).1; omega
    have hn3 : (3 : ℝ) ≤ n := by
      have : 3 ≤ n := by omega
      exact_mod_cast this
    have hlog : 1 < Real.log n := by
      rw [Real.lt_log_iff_exp_lt (by linarith)]
      have := Real.exp_one_lt_d9
      linarith
    have hL : 0 < Real.log (Real.log n) := Real.log_pos hlog
    have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have h1 := two_pow_cardDistinctFactors_le_card_divisors hn0
    have h2 := card_divisors_le_two_pow_cardFactors hn0
    have h1' : (2 : ℝ) ^ ω n ≤ #n.divisors := by exact_mod_cast h1
    have h2' : (#n.divisors : ℝ) ≤ 2 ^ Ω n := by exact_mod_cast h2
    rw [two_pow_eq_rpow _ hlog] at h1' h2'
    apply hbad
    constructor
    · refine lt_of_lt_of_le ?_ h1'
      refine Real.rpow_lt_rpow_of_exponent_lt (by linarith) ?_
      refine mul_lt_mul_of_pos_right ?_ hlog2
      rw [lt_div_iff₀ hL]
      have := (abs_le.1 hωn).1
      nlinarith
    · refine lt_of_le_of_lt h2' ?_
      refine Real.rpow_lt_rpow_of_exponent_lt (by linarith) ?_
      refine mul_lt_mul_of_pos_right ?_ hlog2
      rw [div_lt_iff₀ hL]
      have := (abs_le.1 hΩn).2
      nlinarith
  calc ((S.filter _).card : ℝ) ≤ ((A ∪ B ∪ {1, 2}).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ (A.card : ℝ) + B.card + 2 := by
        have h := Finset.card_union_le (A ∪ B) {1, 2}
        have h' := Finset.card_union_le A B
        have h'' : ({1, 2} : Finset ℕ).card = 2 := rfl
        have : (A ∪ B ∪ {1, 2}).card ≤ A.card + B.card + 2 := by omega
        exact_mod_cast this

end NTKB.HardyWright
