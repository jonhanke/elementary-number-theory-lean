/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import NTKB.Attr
import NTKB.Elementary.HardyWright.Partitions.Signed

/-!
# Partitions: basic relations (Niven–Zuckerman–Montgomery, § 10.1)

Notation: `p(n) = Fintype.card (Nat.Partition n)`, `p_m(n) = (Nat.Partition.restricted n (· ≤ m)).card`
(partitions of `n` into parts `≤ m`), `p^d(n) = (Nat.Partition.distincts n).card`, and
`q^e(n)`, `q^o(n)` are `NTKB.HardyWright.evenDistinctCount`, `NTKB.HardyWright.oddDistinctCount`.

* **Theorem 10.1.** (A) `p_m(n) = p(n)` if `n ≤ m`; (B) `p_m(n) ≤ p(n)`;
  (C) `p_m(n) = p_{m-1}(n) + p_m(n - m)` for `n ≥ m ≥ 1`; (D) `p^d(n) = q^e(n) + q^o(n)`.

Theorem 10.3 (conjugate partitions) is `NTKB.HardyWright.card_partitions_parts_eq_card_partitions_largest`
and `NTKB.HardyWright.card_partitions_parts_le_eq_card_partitions_largest_le`; Theorem 10.4 is
`NTKB.HardyWright.evenDistinctCount_sub_oddDistinctCount`.
-/

namespace NTKB.NZM

open Nat.Partition

/-- **Theorem 10.1 (A).** If `n ≤ m` then `p_m(n) = p(n)`. -/
@[kb "nivenzuckermanmontgomery" "Thm 10.1, p. 447"]
theorem card_restricted_le_eq_card_partition {n m : ℕ} (h : n ≤ m) :
    (Nat.Partition.restricted n (· ≤ m)).card = Fintype.card (Nat.Partition n) := by
  have : Nat.Partition.restricted n (· ≤ m) = Finset.univ :=
    Finset.eq_univ_of_forall fun p => by
      simp only [Nat.Partition.restricted, Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun i hi => (Nat.Partition.le_of_mem_parts hi).trans h
  rw [this, Finset.card_univ]

/-- **Theorem 10.1 (B).** `p_m(n) ≤ p(n)`. -/
@[kb "nivenzuckermanmontgomery" "Thm 10.1, p. 447"]
theorem card_restricted_le_card_partition (n m : ℕ) :
    (Nat.Partition.restricted n (· ≤ m)).card ≤ Fintype.card (Nat.Partition n) :=
  Finset.card_le_univ _

/-- The recursion of Theorem 10.1 (C), indexed by `m + 1`. -/
theorem card_restricted_succ {n : ℕ} (m : ℕ) (hn : m + 1 ≤ n) :
    (Nat.Partition.restricted n (· ≤ m + 1)).card =
      (Nat.Partition.restricted n (· ≤ m)).card +
        (Nat.Partition.restricted (n - (m + 1)) (· ≤ m + 1)).card := by
  classical
  have h1 : 1 ≤ m + 1 := Nat.le_add_left 1 m
  set R := Nat.Partition.restricted n (· ≤ m + 1) with hR
  have hmem : ∀ p : n.Partition, p ∈ R ↔ ∀ i ∈ p.parts, i ≤ m + 1 := by
    intro p
    simp only [hR, Nat.Partition.restricted, Finset.mem_filter, Finset.mem_univ, true_and]
  have hmem' : ∀ (k : ℕ) (q : k.Partition),
      q ∈ Nat.Partition.restricted k (· ≤ m) ↔ ∀ i ∈ q.parts, i ≤ m := by
    intro k q
    simp only [Nat.Partition.restricted, Finset.mem_filter, Finset.mem_univ, true_and]
  have hmem'' : ∀ q : (n - (m + 1)).Partition,
      q ∈ Nat.Partition.restricted (n - (m + 1)) (· ≤ m + 1) ↔ ∀ i ∈ q.parts, i ≤ m + 1 := by
    intro q
    simp only [Nat.Partition.restricted, Finset.mem_filter, Finset.mem_univ, true_and]
  have hsplit := Finset.card_filter_add_card_filter_not (s := R) (fun p : n.Partition => m + 1 ∈ p.parts)
  have hA : R.filter (fun p : n.Partition => ¬ (m + 1 ∈ p.parts)) =
      Nat.Partition.restricted n (· ≤ m) := by
    ext p
    rw [Finset.mem_filter, hmem, hmem']
    constructor
    · rintro ⟨h, hnot⟩ i hi
      have := h i hi
      have hne : i ≠ m + 1 := fun e => hnot (e ▸ hi)
      omega
    · intro h
      refine ⟨fun i hi => by have := h i hi; omega, fun hm => ?_⟩
      have := h _ hm
      omega
  have hB : (R.filter (fun p : n.Partition => m + 1 ∈ p.parts)).card =
      (Nat.Partition.restricted (n - (m + 1)) (· ≤ m + 1)).card := by
    refine Finset.card_bij
      (fun p hp => partitionWithPartEquiv h1 hn ⟨p, (Finset.mem_filter.1 hp).2⟩) ?_ ?_ ?_
    · intro p hp
      rw [hmem'']
      intro i hi
      rw [partitionWithPartEquiv_apply_parts] at hi
      exact (hmem p).1 (Finset.mem_filter.1 hp).1 i (Multiset.mem_of_mem_erase hi)
    · intro p hp q hq hpq
      have := congrArg Subtype.val ((partitionWithPartEquiv h1 hn).injective hpq)
      exact this
    · intro b hb
      have hb' := (hmem'' b).1 hb
      refine ⟨((partitionWithPartEquiv h1 hn).symm b).1, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨(hmem _).2 ?_, ((partitionWithPartEquiv h1 hn).symm b).2⟩
        intro i hi
        rw [partitionWithPartEquiv_symm_apply_parts] at hi
        rcases Multiset.mem_cons.1 hi with rfl | hi
        · exact le_rfl
        · exact hb' i hi
      · exact (partitionWithPartEquiv h1 hn).apply_symm_apply b
  rw [← hsplit, hA, hB, add_comm]

/-- **Theorem 10.1 (C).** If `n ≥ m ≥ 1` then `p_m(n) = p_{m-1}(n) + p_m(n - m)`. -/
@[kb "nivenzuckermanmontgomery" "Thm 10.1, p. 447"]
theorem card_restricted_eq_add {n m : ℕ} (hm : 1 ≤ m) (hn : m ≤ n) :
    (Nat.Partition.restricted n (· ≤ m)).card =
      (Nat.Partition.restricted n (· ≤ m - 1)).card +
        (Nat.Partition.restricted (n - m) (· ≤ m)).card := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simpa only [Nat.add_sub_cancel] using card_restricted_succ (n := n) k hn

/-- **Theorem 10.1 (D).** `p^d(n) = q^e(n) + q^o(n)`: the partitions of `n` into distinct parts are
those with an even number of parts together with those with an odd number of parts. -/
@[kb "nivenzuckermanmontgomery" "Thm 10.1, p. 447"]
theorem card_distincts_eq_even_add_odd (n : ℕ) :
    (Nat.Partition.distincts n).card =
      NTKB.HardyWright.evenDistinctCount n + NTKB.HardyWright.oddDistinctCount n := by
  classical
  unfold NTKB.HardyWright.evenDistinctCount NTKB.HardyWright.oddDistinctCount
  have h : (Nat.Partition.distincts n).filter (fun p : n.Partition => Odd p.parts.card) =
      (Nat.Partition.distincts n).filter (fun p : n.Partition => ¬ Even p.parts.card) :=
    Finset.filter_congr fun p _ => (Nat.not_even_iff_odd).symm
  rw [h]
  exact (Finset.card_filter_add_card_filter_not (s := Nat.Partition.distincts n)
    (fun p : n.Partition => Even p.parts.card)).symm

end NTKB.NZM
