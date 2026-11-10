/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import NTKB.Attr

/-!
# Sums of two squarefree integers (Niven–Zuckerman–Montgomery, § 11.1)

* **Lemma 11.3.** At least half of the integers `1, …, n` are squarefree (`Q(n) ≥ n/2`); in fact
  the inequality is strict (`lt_two_mul_card_squarefree`).
* **Theorem 11.2.** Every integer greater than `1` is a sum of two squarefree positive integers.

The book's proof of Theorem 11.2 uses `|A| + |B| ≥ n - 1` to conclude that `A` and `B` meet; this
needs the strict inequality `Q(n) > n/2`, which is what the proof of the lemma actually gives.
-/

namespace NTKB.NZM

open Finset

private lemma nonsqf_subset (n : ℕ) :
    (Ioc 0 n).filter (fun m => ¬ Squarefree m) ⊆
      (Ioc 0 n).filter (fun m => 2 ^ 2 ∣ m) ∪
      (range n).biUnion (fun k => (Ioc 0 n).filter (fun m => (2 * k + 3) ^ 2 ∣ m)) := by
  intro m hm
  rw [mem_filter] at hm
  obtain ⟨hmem, hns⟩ := hm
  rw [Nat.squarefree_iff_prime_squarefree] at hns
  push_neg at hns
  obtain ⟨p, hp, hpd⟩ := hns
  have hmem' := mem_Ioc.1 hmem
  rw [mem_union]
  rcases hp.eq_two_or_odd' with hp2 | hodd
  · left
    subst hp2
    exact mem_filter.2 ⟨hmem, by simpa [pow_two] using hpd⟩
  · right
    obtain ⟨j, hj⟩ := hodd
    have hp2 := hp.two_le
    have hpm : p * p ≤ m := Nat.le_of_dvd hmem'.1 hpd
    have hpn : p ≤ n := le_trans (Nat.le_mul_self p) (hpm.trans hmem'.2)
    rw [mem_biUnion]
    refine ⟨j - 1, mem_range.2 (by omega), mem_filter.2 ⟨hmem, ?_⟩⟩
    have h3 : 2 * (j - 1) + 3 = p := by omega
    rw [h3, pow_two]
    exact hpd

private lemma card_nonsqf_le_nat (n : ℕ) :
    ((Ioc 0 n).filter (fun m => ¬ Squarefree m)).card ≤
      n / 2 ^ 2 + ∑ k ∈ range n, n / (2 * k + 3) ^ 2 := by
  calc ((Ioc 0 n).filter (fun m => ¬ Squarefree m)).card
      ≤ ((Ioc 0 n).filter (fun m => 2 ^ 2 ∣ m) ∪
          (range n).biUnion
            (fun k => (Ioc 0 n).filter (fun m => (2 * k + 3) ^ 2 ∣ m))).card :=
        card_le_card (nonsqf_subset n)
    _ ≤ ((Ioc 0 n).filter (fun m => 2 ^ 2 ∣ m)).card +
          ((range n).biUnion
            (fun k => (Ioc 0 n).filter (fun m => (2 * k + 3) ^ 2 ∣ m))).card :=
        card_union_le _ _
    _ ≤ n / 2 ^ 2 + ∑ k ∈ range n, n / (2 * k + 3) ^ 2 := by
        apply add_le_add
        · exact le_of_eq (Nat.Ioc_filter_dvd_card_eq_div n _)
        · refine card_biUnion_le.trans ?_
          apply le_of_eq
          apply sum_congr rfl
          intro k _
          exact Nat.Ioc_filter_dvd_card_eq_div n _

private lemma sum_inv_sq_le (n : ℕ) :
    ∑ k ∈ range n, (1 : ℚ) / (2 * (k : ℚ) + 3) ^ 2 ≤ 1 / 4 - 1 / (4 * ((n : ℚ) + 1)) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [sum_range_succ]
    have hx : (0 : ℚ) ≤ n := Nat.cast_nonneg n
    have key : (1 : ℚ) / (2 * (n : ℚ) + 3) ^ 2 ≤
        1 / (4 * ((n : ℚ) + 1)) - 1 / (4 * (((n + 1 : ℕ) : ℚ) + 1)) := by
      push_cast
      rw [div_sub_div _ _ (by positivity) (by positivity),
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hx]
    linarith

private lemma two_mul_card_nonsqf_lt (n : ℕ) (hn : 0 < n) :
    2 * ((Ioc 0 n).filter (fun m => ¬ Squarefree m)).card < n := by
  have h1 := card_nonsqf_le_nat n
  have h2 := (Nat.cast_le (α := ℚ)).2 h1
  rw [Nat.cast_add, Nat.cast_sum] at h2
  have h3 : ((n / 2 ^ 2 : ℕ) : ℚ) ≤ (n : ℚ) / 4 := by
    calc ((n / 2 ^ 2 : ℕ) : ℚ) ≤ (n : ℚ) / ((2 ^ 2 : ℕ) : ℚ) := Nat.cast_div_le
      _ = (n : ℚ) / 4 := by norm_num
  have h4 : ∑ k ∈ range n, ((n / (2 * k + 3) ^ 2 : ℕ) : ℚ) ≤
      ∑ k ∈ range n, (n : ℚ) * (1 / (2 * (k : ℚ) + 3) ^ 2) := by
    apply sum_le_sum
    intro k _
    calc ((n / (2 * k + 3) ^ 2 : ℕ) : ℚ) ≤ (n : ℚ) / (((2 * k + 3) ^ 2 : ℕ) : ℚ) :=
          Nat.cast_div_le
      _ = (n : ℚ) * (1 / (2 * (k : ℚ) + 3) ^ 2) := by push_cast; ring
  have h5 : ∑ k ∈ range n, (n : ℚ) * (1 / (2 * (k : ℚ) + 3) ^ 2) =
      (n : ℚ) * ∑ k ∈ range n, (1 : ℚ) / (2 * (k : ℚ) + 3) ^ 2 := by
    rw [Finset.mul_sum]
  have hnq : (0 : ℚ) < n := Nat.cast_pos.2 hn
  have h6 := mul_le_mul_of_nonneg_left (sum_inv_sq_le n) hnq.le
  have h7 : 0 < (n : ℚ) * (1 / (4 * ((n : ℚ) + 1))) := by positivity
  have h8 : (2 * ((Ioc 0 n).filter (fun m => ¬ Squarefree m)).card : ℚ) < n := by
    rw [h5] at h4
    nlinarith [h2, h3, h4, h6, h7]
  exact_mod_cast h8

private lemma Icc_one_eq_Ioc_zero (n : ℕ) : Finset.Icc 1 n = Finset.Ioc 0 n := by
  ext m
  simp only [mem_Icc, mem_Ioc]
  omega

/-- **Lemma 11.3 (strict form).** For `n ≥ 1`, more than half of `1, …, n` are squarefree. -/
@[kb "nivenzuckermanmontgomery" "Lemma 11.3, p. 474"]
theorem lt_two_mul_card_squarefree (n : ℕ) (hn : 0 < n) :
    n < 2 * ((Finset.Icc 1 n).filter Squarefree).card := by
  rw [Icc_one_eq_Ioc_zero]
  have h := card_filter_add_card_filter_not (s := Ioc 0 n) Squarefree
  rw [Nat.card_Ioc, Nat.sub_zero] at h
  have h2 := two_mul_card_nonsqf_lt n hn
  omega

/-- **Lemma 11.3.** For every positive integer `n`, the number `Q(n)` of squarefree integers among
`1, …, n` satisfies `Q(n) ≥ n/2`. -/
@[kb "nivenzuckermanmontgomery" "Lemma 11.3, p. 474"]
theorem two_mul_card_squarefree_ge (n : ℕ) :
    n ≤ 2 * ((Finset.Icc 1 n).filter Squarefree).card := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; exact Nat.zero_le _
  · exact (lt_two_mul_card_squarefree n h).le

/-- **Theorem 11.2.** Every integer greater than `1` is a sum of two squarefree positive
integers. -/
@[kb "nivenzuckermanmontgomery" "Thm 11.2, p. 474"]
theorem exists_squarefree_add (n : ℕ) (hn : 1 < n) :
    ∃ a b, 0 < a ∧ 0 < b ∧ Squarefree a ∧ Squarefree b ∧ a + b = n := by
  have hlt := lt_two_mul_card_squarefree (n - 1) (by omega)
  have hcard :
      ((Finset.Icc 1 (n - 1)).filter (fun a => Squarefree (n - a))).card =
        ((Finset.Icc 1 (n - 1)).filter Squarefree).card := by
    symm
    refine Finset.card_bij' (fun a _ => n - a) (fun a _ => n - a) ?_ ?_ ?_ ?_
    · intro a ha
      rw [mem_filter, mem_Icc] at ha ⊢
      obtain ⟨⟨h1, h2⟩, h3⟩ := ha
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      have h4 : n - (n - a) = a := by omega
      rw [h4]
      exact h3
    · intro a ha
      rw [mem_filter, mem_Icc] at ha ⊢
      obtain ⟨⟨h1, h2⟩, h3⟩ := ha
      exact ⟨⟨by omega, by omega⟩, h3⟩
    · intro a ha
      rw [mem_filter, mem_Icc] at ha
      obtain ⟨⟨h1, h2⟩, _⟩ := ha
      show n - (n - a) = a
      omega
    · intro a ha
      rw [mem_filter, mem_Icc] at ha
      obtain ⟨⟨h1, h2⟩, _⟩ := ha
      show n - (n - a) = a
      omega
  have hne : (((Finset.Icc 1 (n - 1)).filter Squarefree) ∩
      ((Finset.Icc 1 (n - 1)).filter (fun a => Squarefree (n - a)))).Nonempty := by
    apply inter_nonempty_of_card_lt_card_add_card (s := Finset.Icc 1 (n - 1))
      (filter_subset _ _) (filter_subset _ _)
    rw [Nat.card_Icc, hcard]
    omega
  obtain ⟨a, ha⟩ := hne
  rw [mem_inter, mem_filter, mem_filter, mem_Icc] at ha
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, _, h4⟩ := ha
  exact ⟨a, n - a, by omega, by omega, h3, h4, by omega⟩

end NTKB.NZM
