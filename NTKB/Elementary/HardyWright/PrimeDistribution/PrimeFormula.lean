/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.PrimeDistribution.Elementary
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A formula for the `n`-th prime

`[hardywright2008, Theorem 419]`: with `a = ∑ pₘ 10^(-2^m)`, one has
`pₙ = ⌊10^(2^n) a⌋ - 10^(2^(n-1)) ⌊10^(2^(n-1)) a⌋`.

Throughout, the summation index `m` of the Lean code is the book's `m + 1`, so the book's `pₘ`
is `Nat.nth Nat.Prime (m - 1)`.
-/

open Finset

namespace NTKB.HardyWright

/-- The constant `a = ∑_{m ≥ 1} p_m 10^(-2^m)` of Theorem 419.
(The summation index `m` corresponds to the book's `m + 1`.) -/
noncomputable def moserConstant : ℝ :=
  ∑' m : ℕ, (Nat.nth Nat.Prime m : ℝ) * ((10 : ℝ) ^ (2 ^ (m + 1)))⁻¹

private noncomputable def term (m : ℕ) : ℝ :=
  (Nat.nth Nat.Prime m : ℝ) * ((10 : ℝ) ^ (2 ^ (m + 1)))⁻¹

private theorem nth_lt (m : ℕ) : (Nat.nth Nat.Prime m : ℝ) < 4 ^ (m + 1) := by
  simpa using primeCounting_ge_log_div_and_nth_prime_lt.2 (m + 1) (by omega)

private theorem term_pos (m : ℕ) : 0 < term m := by
  have := (Nat.prime_nth_prime m).pos
  unfold term; positivity

private theorem term_le (m : ℕ) : term m ≤ (2 / 5 : ℝ) ^ (m + 1) := by
  have h1 : (Nat.nth Nat.Prime m : ℝ) ≤ 4 ^ (m + 1) := (nth_lt m).le
  have h2 : (10 : ℝ) ^ (m + 1) ≤ 10 ^ (2 ^ (m + 1)) :=
    pow_le_pow_right₀ (by norm_num) (Nat.lt_two_pow_self).le
  calc term m ≤ 4 ^ (m + 1) * ((10 : ℝ) ^ (m + 1))⁻¹ :=
        mul_le_mul h1 (inv_anti₀ (by positivity) h2) (by positivity) (by positivity)
    _ = (2 / 5 : ℝ) ^ (m + 1) := by
        rw [← div_eq_mul_inv, ← div_pow]; norm_num

private theorem summable_term : Summable term := by
  refine Summable.of_nonneg_of_le (fun m ↦ (term_pos m).le) term_le ?_
  have : Summable fun m : ℕ ↦ (2 / 5 : ℝ) ^ m :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  simpa [pow_succ] using this.mul_right (2 / 5)

private theorem tail_term_le {j m : ℕ} (h : j < m) :
    (10 : ℝ) ^ (2 ^ (j + 1)) * term m ≤ (2 / 5 : ℝ) ^ (m + 1) := by
  have hEj : 2 ^ (j + 1) ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h
  have hm : m + 1 ≤ 2 ^ m := Nat.lt_two_pow_self
  have h3 : (10 : ℝ) ^ (2 ^ (j + 1)) * 10 ^ (m + 1) ≤ 10 ^ (2 ^ (m + 1)) := by
    rw [← pow_add]
    apply pow_le_pow_right₀ (by norm_num)
    rw [pow_succ]; omega
  have h4 : (10 : ℝ) ^ (2 ^ (j + 1)) * ((10 : ℝ) ^ (2 ^ (m + 1)))⁻¹ ≤ ((10 : ℝ) ^ (m + 1))⁻¹ := by
    rw [← div_eq_mul_inv, div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ (by positivity)]
    exact h3
  have h1 : (Nat.nth Nat.Prime m : ℝ) ≤ 4 ^ (m + 1) := (nth_lt m).le
  calc (10 : ℝ) ^ (2 ^ (j + 1)) * term m
      = (Nat.nth Nat.Prime m : ℝ) * ((10 : ℝ) ^ (2 ^ (j + 1)) * ((10 : ℝ) ^ (2 ^ (m + 1)))⁻¹) := by
        unfold term; ring
    _ ≤ 4 ^ (m + 1) * ((10 : ℝ) ^ (m + 1))⁻¹ :=
        mul_le_mul h1 h4 (by positivity) (by positivity)
    _ = (2 / 5 : ℝ) ^ (m + 1) := by
        rw [← div_eq_mul_inv, ← div_pow]; norm_num

/-- The integer part: `N j = ∑_{m ≤ j} p_m 10^(2^(j+1) - 2^(m+1))`. -/
private noncomputable def intPart (j : ℕ) : ℕ :=
  ∑ m ∈ range (j + 1), Nat.nth Nat.Prime m * 10 ^ (2 ^ (j + 1) - 2 ^ (m + 1))

private theorem intPart_succ (j : ℕ) :
    intPart (j + 1) = Nat.nth Nat.Prime (j + 1) + 10 ^ (2 ^ (j + 1)) * intPart j := by
  unfold intPart
  rw [sum_range_succ, mul_sum]
  have : 2 ^ (j + 1 + 1) - 2 ^ (j + 1 + 1) = 0 := Nat.sub_self _
  rw [this, pow_zero, mul_one, add_comm]
  congr 1
  apply sum_congr rfl
  intro m hm
  have hm' : m ≤ j := Nat.lt_succ_iff.mp (mem_range.mp hm)
  have hle : 2 ^ (m + 1) ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : 2 ^ (j + 1 + 1) - 2 ^ (m + 1) = 2 ^ (j + 1) + (2 ^ (j + 1) - 2 ^ (m + 1)) := by
    rw [pow_succ 2 (j + 1)]; omega
  rw [this, pow_add]; ring

private theorem floor_main (j : ℕ) :
    ⌊(10 : ℝ) ^ (2 ^ (j + 1)) * moserConstant⌋ = (intPart j : ℤ) := by
  have hs := summable_term
  have hsplit := hs.sum_add_tsum_nat_add (j + 1)
  have ha : moserConstant = ∑' m, term m := rfl
  set R : ℝ := ∑' m, (10 : ℝ) ^ (2 ^ (j + 1)) * term (m + (j + 1)) with hR
  have hfirst : (10 : ℝ) ^ (2 ^ (j + 1)) * ∑ i ∈ range (j + 1), term i = (intPart j : ℝ) := by
    unfold intPart
    push_cast
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    have hi' : i ≤ j := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have hle : 2 ^ (i + 1) ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_sub₀ _ (by norm_num) hle]
    unfold term
    field_simp
  have hmul : (10 : ℝ) ^ (2 ^ (j + 1)) * moserConstant = (intPart j : ℝ) + R := by
    rw [ha, ← hsplit, mul_add, hfirst, hR, tsum_mul_left]
  have hs2 : Summable fun m : ℕ ↦ (10 : ℝ) ^ (2 ^ (j + 1)) * term (m + (j + 1)) :=
    ((hs.comp_injective (add_left_injective (j + 1)))).mul_left _
  have hRpos : 0 < R :=
    hs2.tsum_pos (fun m ↦ by have := term_pos (m + (j + 1)); positivity) 0
      (by have := term_pos (0 + (j + 1)); positivity)
  have hg : Summable fun m : ℕ ↦ (2 / 5 : ℝ) ^ (m + 2) := by
    have : Summable fun m : ℕ ↦ (2 / 5 : ℝ) ^ m :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    exact (this.mul_right ((2 / 5 : ℝ) ^ 2)).congr (fun m ↦ by ring)
  have hRle : R ≤ ∑' m : ℕ, (2 / 5 : ℝ) ^ (m + 2) := by
    refine hs2.tsum_le_tsum (fun m ↦ ?_) hg
    refine (tail_term_le (by omega : j < m + (j + 1))).trans ?_
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hgsum : ∑' m : ℕ, (2 / 5 : ℝ) ^ (m + 2) = 4 / 15 := by
    have : ∀ m : ℕ, (2 / 5 : ℝ) ^ (m + 2) = (2 / 5) ^ 2 * (2 / 5) ^ m := fun m ↦ by ring
    rw [tsum_congr this]
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  rw [hmul, Int.floor_eq_iff]
  constructor
  · push_cast; linarith
  · push_cast; linarith

/-- **Theorem 419.** `p_n = ⌊10^(2^n) a⌋ - 10^(2^(n-1)) ⌊10^(2^(n-1)) a⌋`. -/
@[kb "hardywright2008" "Thm 419, p. 476"]
theorem nth_prime_eq_floor_moserConstant (n : ℕ) (hn : 1 ≤ n) :
    (Nat.nth Nat.Prime (n - 1) : ℤ) = ⌊(10 : ℝ) ^ (2 ^ n) * moserConstant⌋ -
      10 ^ (2 ^ (n - 1)) * ⌊(10 : ℝ) ^ (2 ^ (n - 1)) * moserConstant⌋ := by
  rcases Nat.eq_or_lt_of_le hn with h | h
  · -- n = 1
    subst h
    have h0 := floor_main 0
    have hs := summable_term
    have hsplit := hs.sum_add_tsum_nat_add 1
    have hpos : 0 < moserConstant := by
      have := hs.tsum_pos (fun m ↦ (term_pos m).le) 0 (term_pos 0)
      exact this
    have hlt : (10 : ℝ) * moserConstant < 1 := by
      by_contra hcon
      push Not at hcon
      have h1 : ⌊(10 : ℝ) ^ (2 ^ (0 + 1)) * moserConstant⌋ = (intPart 0 : ℤ) := h0
      have h2 : intPart 0 = 2 := by
        simp [intPart, Nat.nth_prime_zero_eq_two]
      rw [h2] at h1
      have := (Int.floor_eq_iff.mp h1).2
      have h3 : (10 : ℝ) ^ (2 ^ (0 + 1)) * moserConstant < 3 := by push_cast at this; linarith
      norm_num at h3
      linarith
    have hfl : ⌊(10 : ℝ) ^ (2 ^ (1 - 1)) * moserConstant⌋ = 0 := by
      rw [Int.floor_eq_iff]
      norm_num
      constructor <;> linarith
    rw [hfl]
    have h2 : intPart 0 = 2 := by simp [intPart, Nat.nth_prime_zero_eq_two]
    have h1 : ⌊(10 : ℝ) ^ (2 ^ 1) * moserConstant⌋ = 2 := by
      have := h0; rw [h2] at this; simpa using this
    rw [h1]; simp [Nat.nth_prime_zero_eq_two]
  · obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
    have e1 : j + 2 - 1 = j + 1 := by omega
    rw [e1]
    have h1 := floor_main (j + 1)
    have h2 := floor_main j
    rw [show j + 2 = (j + 1) + 1 from rfl, h1, h2, intPart_succ]
    push_cast
    ring

end NTKB.HardyWright
