/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import NTKB.Attr
import NTKB.Elementary.HardyWright.Partitions.Basic
import NTKB.Analytic.Apostol.Partitions.UpperBound

/-!
# Bounds on the partition function (Niven–Zuckerman–Montgomery, § 10.4)

Notation: `p(n) = Fintype.card (Nat.Partition n)`.

* **Theorem 10.12.** `2^√n < p(n) < exp(c √n)` with `c = π √(2/3)`; the first inequality for
  `n > 3` and the second for `n ≥ 1`, as in the book (the first fails at `n = 3`, where
  `p(3) = 3 < 2^√3`).

The upper bound is `NTKB.Apostol.card_partition_lt_exp`.  The lower bound is proved by
counting the partitions `∑ S + 1 + ⋯ + 1`, `S ⊆ {2, …, k + 1}`; the small cases use the
values `p(0), …, p(12)` obtained from Euler's pentagonal recurrence.
-/

namespace NTKB.NZM

open NTKB.HardyWright Finset

/-! ### Small values of `p(n)` from the pentagonal recurrence -/

private lemma rec_of_set {n : ℕ} (hn : n ≠ 0) (S : Finset ℤ)
    (hS : (Finset.Icc (-(n : ℤ)) n).filter (fun k ↦ pentagonal k ≤ n) = S) :
    ∑ k ∈ S, (k.negOnePow : ℤ) * (Fintype.card (n - pentagonal k).Partition : ℤ) = 0 := by
  rw [← hS]; exact card_partition_pentagonal_recurrence hn

private lemma pent2 : pentagonal 2 = 5 := by decide
private lemma pent1 : pentagonal 1 = 1 := by decide
private lemma pent0 : pentagonal 0 = 0 := by decide
private lemma pent3 : pentagonal 3 = 12 := by decide
private lemma pentm1 : pentagonal (-1) = 2 := by decide
private lemma pentm2 : pentagonal (-2) = 7 := by decide
private lemma neg2 : (2 : ℤ).negOnePow = 1 := by decide
private lemma neg3 : (3 : ℤ).negOnePow = -1 := by decide
private lemma neg1 : (1 : ℤ).negOnePow = -1 := by decide
private lemma neg0 : (0 : ℤ).negOnePow = 1 := by decide
private lemma negm1 : (-1 : ℤ).negOnePow = -1 := by decide
private lemma negm2 : (-2 : ℤ).negOnePow = 1 := by decide
private lemma card0 : Fintype.card (Nat.Partition 0) = 1 := by simp

/-- Expand the pentagonal recurrence at `n` over the explicit index set `S`. -/
local macro "pent_step " n:num S:term : tactic =>
  `(tactic| (
    have h := rec_of_set (n := $n) (by norm_num) $S (by decide)
    repeat rw [Finset.sum_insert (by decide)] at h
    rw [Finset.sum_singleton] at h
    try rw [pent2] at h
    try rw [pent1] at h
    try rw [pent0] at h
    try rw [pentm1] at h
    try rw [pentm2] at h
    try rw [pent3] at h
    try rw [neg2] at h
    try rw [neg1] at h
    try rw [neg0] at h
    try rw [negm1] at h
    try rw [negm2] at h
    try rw [neg3] at h
    simp only [Nat.reduceSub, Units.val_one, Units.val_neg, card0] at h))

/-- The values `p(0), …, p(12)`. -/
private lemma card_partition_table :
    Fintype.card (Nat.Partition 1) = 1 ∧ Fintype.card (Nat.Partition 2) = 2 ∧
    Fintype.card (Nat.Partition 3) = 3 ∧ Fintype.card (Nat.Partition 4) = 5 ∧
    Fintype.card (Nat.Partition 5) = 7 ∧ Fintype.card (Nat.Partition 6) = 11 ∧
    Fintype.card (Nat.Partition 7) = 15 ∧ Fintype.card (Nat.Partition 8) = 22 ∧
    Fintype.card (Nat.Partition 9) = 30 ∧ Fintype.card (Nat.Partition 10) = 42 ∧
    Fintype.card (Nat.Partition 11) = 56 ∧ Fintype.card (Nat.Partition 12) = 77 := by
  pent_step 1 {0, 1}
  have h1 : Fintype.card (Nat.Partition 1) = 1 := by omega
  pent_step 2 {-1, 0, 1}
  have h2 : Fintype.card (Nat.Partition 2) = 2 := by omega
  pent_step 3 {-1, 0, 1}
  have h3 : Fintype.card (Nat.Partition 3) = 3 := by omega
  pent_step 4 {-1, 0, 1}
  have h4 : Fintype.card (Nat.Partition 4) = 5 := by omega
  pent_step 5 {-1, 0, 1, 2}
  have h5 : Fintype.card (Nat.Partition 5) = 7 := by omega
  pent_step 6 {-1, 0, 1, 2}
  have h6 : Fintype.card (Nat.Partition 6) = 11 := by omega
  pent_step 7 {-2, -1, 0, 1, 2}
  have h7 : Fintype.card (Nat.Partition 7) = 15 := by omega
  pent_step 8 {-2, -1, 0, 1, 2}
  have h8 : Fintype.card (Nat.Partition 8) = 22 := by omega
  pent_step 9 {-2, -1, 0, 1, 2}
  have h9 : Fintype.card (Nat.Partition 9) = 30 := by omega
  pent_step 10 {-2, -1, 0, 1, 2}
  have h10 : Fintype.card (Nat.Partition 10) = 42 := by omega
  pent_step 11 {-2, -1, 0, 1, 2}
  have h11 : Fintype.card (Nat.Partition 11) = 56 := by omega
  pent_step 12 {-2, -1, 0, 1, 2, 3}
  have h12 : Fintype.card (Nat.Partition 12) = 77 := by omega
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

/-! ### Monotonicity -/

/-- `p(n) ≤ p(n + 1)` (add a part equal to `1`). -/
theorem card_partition_le_succ (n : ℕ) :
    Fintype.card (Nat.Partition n) ≤ Fintype.card (Nat.Partition (n + 1)) := by
  refine Fintype.card_le_of_injective
    (fun p : Nat.Partition n ↦ (⟨1 ::ₘ p.parts, ?_, ?_⟩ : Nat.Partition (n + 1))) ?_
  · intro i hi
    rcases Multiset.mem_cons.1 hi with rfl | hi
    · exact one_pos
    · exact p.parts_pos hi
  · rw [Multiset.sum_cons, p.parts_sum]; omega
  · intro p q h
    have := congrArg Nat.Partition.parts h
    exact Nat.Partition.ext (Multiset.cons_inj_right _ |>.1 this)

theorem card_partition_mono {m n : ℕ} (h : m ≤ n) :
    Fintype.card (Nat.Partition m) ≤ Fintype.card (Nat.Partition n) := by
  induction n, h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact ih.trans (card_partition_le_succ n)

/-! ### The counting argument -/

private lemma two_mul_sum_Icc (k : ℕ) : 2 * ∑ i ∈ Icc 2 (k + 1), i = k * (k + 3) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]; ring

/-- If `k (k + 3) ≤ 2 n` (i.e. `2 + 3 + ⋯ + (k + 1) ≤ n`) then `2^k ≤ p(n)`. -/
theorem two_pow_le_card_partition {k n : ℕ} (h : k * (k + 3) ≤ 2 * n) :
    2 ^ k ≤ Fintype.card (Nat.Partition n) := by
  classical
  have hsum : ∀ S ∈ (Icc 2 (k + 1)).powerset, ∑ i ∈ S, i ≤ n := by
    intro S hS
    have h1 : ∑ i ∈ S, i ≤ ∑ i ∈ Icc 2 (k + 1), i :=
      Finset.sum_le_sum_of_subset (Finset.mem_powerset.1 hS)
    have := two_mul_sum_Icc k
    omega
  have hge : ∀ S ∈ (Icc 2 (k + 1)).powerset, ∀ i ∈ S, 2 ≤ i := by
    intro S hS i hi
    exact (Finset.mem_Icc.1 (Finset.mem_powerset.1 hS hi)).1
  have key : Fintype.card ↥((Icc 2 (k + 1)).powerset) ≤
      Fintype.card (Nat.Partition n) := by
    refine Fintype.card_le_of_injective
      (fun S : ↥((Icc 2 (k + 1)).powerset) ↦
        (⟨S.1.val + Multiset.replicate (n - ∑ i ∈ S.1, i) 1, ?_, ?_⟩ : Nat.Partition n)) ?_
    · intro i hi
      rcases Multiset.mem_add.1 hi with hi | hi
      · exact lt_of_lt_of_le two_pos (hge S.1 S.2 i hi)
      · rw [Multiset.eq_of_mem_replicate hi]; exact one_pos
    · have := hsum S.1 S.2
      rw [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul, mul_one]
      have e : S.1.val.sum = ∑ i ∈ S.1, i := by
        rw [Finset.sum_eq_multiset_sum, Multiset.map_id']
      omega
    · intro S T hST
      have h1 := congrArg (fun p : Nat.Partition n ↦ p.parts.filter (2 ≤ ·)) hST
      have hf : ∀ U : ↥((Icc 2 (k + 1)).powerset),
          (U.1.val + Multiset.replicate (n - ∑ i ∈ U.1, i) 1).filter (2 ≤ ·) = U.1.val := by
        intro U
        rw [Multiset.filter_add, Multiset.filter_eq_self.2 (fun a ha ↦ hge U.1 U.2 a ha),
          Multiset.filter_eq_nil.2 (fun a ha ↦ by
            rw [Multiset.eq_of_mem_replicate ha]; omega), add_zero]
      simp only [hf] at h1
      exact Subtype.ext (Finset.val_inj.1 h1)
  have e : k + 1 + 1 - 2 = k := by omega
  rwa [Fintype.card_coe, Finset.card_powerset, Nat.card_Icc, e] at key

/-- Lower bounds for `p(n)` for small `n`, used to cover `4 ≤ n < 36`. -/
private def pLow (n : ℕ) : ℕ := [1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42, 56, 77].getD n 77

private lemma pLow_le (n : ℕ) : pLow n ≤ Fintype.card (Nat.Partition n) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := card_partition_table
  by_cases hn : n ≤ 12
  · interval_cases n <;> simp [pLow, *]
  · have : pLow n = 77 := by
      unfold pLow; rw [List.getD_eq_default]; simp; omega
    rw [this, ← h12]; exact card_partition_mono (by omega)

private lemma small_exists : ∀ n < 36, 4 ≤ n →
    ∃ a < 20, 4 * n ≤ a ^ 2 ∧ 2 ^ a < pLow n ^ 2 := by decide +kernel

private lemma lt_card_of_small {n : ℕ} (hn : 4 ≤ n) (h36 : n < 36) :
    (2 : ℝ) ^ √(n : ℝ) < Fintype.card (Nat.Partition n) := by
  obtain ⟨a, -, ha1, ha2⟩ := small_exists n h36 hn
  have hp : (pLow n : ℝ) ≤ Fintype.card (Nat.Partition n) := by exact_mod_cast pLow_le n
  have hsq : √(n : ℝ) ≤ (a : ℝ) / 2 := by
    rw [Real.sqrt_le_iff]
    have : (4 * n : ℝ) ≤ (a : ℝ) ^ 2 := by exact_mod_cast ha1
    refine ⟨by positivity, ?_⟩
    nlinarith
  have h2 : (2 : ℝ) ^ √(n : ℝ) ≤ (2 : ℝ) ^ ((a : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hsq
  refine lt_of_le_of_lt h2 (lt_of_lt_of_le ?_ hp)
  refine lt_of_pow_lt_pow_left₀ 2 (by positivity) ?_
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have : (2 : ℝ) ^ a < (pLow n : ℝ) ^ 2 := by exact_mod_cast ha2
  convert this using 2
  · push_cast; ring_nf; rw [Real.rpow_natCast]

/-- **Theorem 10.12** (lower bound). `2^√n < p(n)` for `n ≥ 4`. -/
@[kb "nivenzuckermanmontgomery" "Thm 10.12, p. 462"]
theorem two_rpow_sqrt_lt_card_partition {n : ℕ} (hn : 4 ≤ n) :
    (2 : ℝ) ^ √(n : ℝ) < Fintype.card (Nat.Partition n) := by
  by_cases h36 : n < 36
  · exact lt_card_of_small hn h36
  · rw [not_lt] at h36
    set s := Nat.sqrt n with hs
    have hs6 : 6 ≤ s := Nat.le_sqrt.2 (by omega)
    have hss : s * s ≤ n := Nat.sqrt_le n
    have hlt : n < (s + 1) * (s + 1) := Nat.lt_succ_sqrt n
    have hk : (s + 1) * (s + 1 + 3) ≤ 2 * n := by nlinarith
    have h1 := two_pow_le_card_partition hk
    have h2 : √(n : ℝ) < ((s + 1 : ℕ) : ℝ) := by
      rw [Real.sqrt_lt' (by positivity)]
      exact_mod_cast (by nlinarith : n < (s + 1) ^ 2)
    calc (2 : ℝ) ^ √(n : ℝ) < (2 : ℝ) ^ (((s + 1 : ℕ)) : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h2
      _ = (2 : ℝ) ^ (s + 1) := Real.rpow_natCast _ _
      _ ≤ _ := by exact_mod_cast h1

/-- **Theorem 10.12.** `2^√n < p(n) < exp(c √n)` with `c = π √(2/3)`, for `n ≥ 4` (the upper
bound holds for all `n ≥ 1`, and the lower bound fails for `n = 3`). -/
@[kb "nivenzuckermanmontgomery" "Thm 10.12, p. 462"]
theorem two_rpow_sqrt_lt_card_partition_lt_exp {n : ℕ} (hn : 4 ≤ n) :
    (2 : ℝ) ^ √(n : ℝ) < Fintype.card (Nat.Partition n) ∧
      (Fintype.card (Nat.Partition n) : ℝ) < Real.exp (Real.pi * √(2 / 3) * √(n : ℝ)) :=
  ⟨two_rpow_sqrt_lt_card_partition hn, NTKB.Apostol.card_partition_lt_exp (by omega)⟩

end NTKB.NZM
