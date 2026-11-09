/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
import NTKB.Attr

/-!
# Partitions into distinct parts, signed count (Hardy–Wright, Chapter XIX, § 19.10)

Let `E(n)` (resp. `U(n)`) be the number of partitions of `n` into an even (resp. odd) number of
unequal parts.

* **Theorem 358.** `E(n) = U(n)` unless `n = k(3k ± 1)/2` for an integer `k`, i.e. `n = pentagonal k`
  (`pentagonal k = k(3k-1)/2`, `k ∈ ℤ`; `k` and `-k` give the two signs), and then
  `E(n) - U(n) = (-1)^k`.

Hardy–Wright deduce it from Euler's pentagonal identity (Theorem 353): the coefficient of `xⁿ` in
`∏ (1 - xⁿ)` is `∑ (-1)^ν` over the partitions of `n` into unequal parts, `ν` the number of parts
(19.10.1). Here we use Mathlib's `Nat.Partition.genFun` for the character `f i c = -1` if `c = 1` and
`0` otherwise: its coefficient at `n` is `∑ (-1)^{#parts}` over the partitions of `n` with distinct
parts (`coeff_genFun_signed`), and by `Nat.Partition.hasProd_genFun` it equals `∏ (1 - X^{n+1})`, which
Mathlib's pentagonal number theorem for power series (`PowerSeries.WithPiTopology.hasProd_one_sub_X_pow`)
identifies with `PowerSeries.pentagonalSeries`.
-/

open Finset PowerSeries
open scoped PowerSeries.WithPiTopology

namespace NTKB.HardyWright

/-- `E(n)`: the number of partitions of `n` into an even number of unequal parts. -/
def evenDistinctCount (n : ℕ) : ℕ :=
  ((Nat.Partition.distincts n).filter fun p ↦ Even p.parts.card).card

/-- `U(n)`: the number of partitions of `n` into an odd number of unequal parts. -/
def oddDistinctCount (n : ℕ) : ℕ :=
  ((Nat.Partition.distincts n).filter fun p ↦ Odd p.parts.card).card

/-- The character `f i c = -1` if `c = 1` and `0` otherwise. -/
def signedChar (_ c : ℕ) : ℤ := if c = 1 then -1 else 0

theorem prod_toFinsupp_signedChar {n : ℕ} (p : n.Partition) :
    p.parts.toFinsupp.prod signedChar = if p.parts.Nodup then (-1) ^ p.parts.card else 0 := by
  classical
  by_cases h : p.parts.Nodup
  · simp only [h, ↓reduceIte]
    rw [Finsupp.prod, Multiset.toFinsupp_support,
      prod_congr rfl (g := fun _ ↦ (-1 : ℤ)), prod_const, Multiset.toFinset_card_of_nodup h]
    intro a ha
    rw [Multiset.mem_toFinset] at ha
    simp [signedChar, Multiset.toFinsupp_apply, Multiset.count_eq_one_of_mem h ha]
  · simp only [h, ↓reduceIte]
    rw [Multiset.nodup_iff_count_le_one] at h
    push Not at h
    obtain ⟨a, ha⟩ := h
    rw [Finsupp.prod]
    refine prod_eq_zero (i := a) ?_ ?_
    · rw [Multiset.toFinsupp_support, Multiset.mem_toFinset]
      exact Multiset.count_pos.1 (by omega)
    · rw [Multiset.toFinsupp_apply, signedChar]
      simp only [show Multiset.count a p.parts ≠ 1 by omega, ↓reduceIte]

/-- The coefficient of `xⁿ` in the signed generating function is `∑ (-1)^ν` over the partitions of
`n` into unequal parts, `ν` the number of parts, which is `E(n) - U(n)` (19.10.1). -/
theorem coeff_genFun_signed (n : ℕ) :
    (Nat.Partition.genFun signedChar).coeff n =
      (evenDistinctCount n : ℤ) - oddDistinctCount n := by
  classical
  rw [Nat.Partition.coeff_genFun]
  simp_rw [prod_toFinsupp_signedChar]
  rw [← sum_filter, evenDistinctCount, oddDistinctCount, Nat.Partition.distincts]
  have h : ∀ p : n.Partition, ((-1 : ℤ) ^ p.parts.card) =
      if Even p.parts.card then 1 else -1 := fun p ↦ by
    split_ifs with he
    · exact he.neg_one_pow
    · exact (Nat.not_even_iff_odd.1 he).neg_one_pow
  simp_rw [h]
  rw [filter_filter, filter_filter, sum_ite]
  simp only [sum_const, nsmul_eq_mul, mul_one, mul_neg, Nat.not_even_iff_odd]
  rw [sub_eq_add_neg]
  simp only [filter_filter]

theorem genFun_signedChar_eq : Nat.Partition.genFun signedChar = pentagonalSeries ℤ := by
  have h := Nat.Partition.hasProd_genFun (R := ℤ) signedChar
  have h' : HasProd (fun i : ℕ ↦ (1 - X ^ (i + 1) : ℤ⟦X⟧)) (Nat.Partition.genFun signedChar) := by
    convert h using 1
    funext i
    rw [tsum_eq_single 0]
    · simp only [signedChar, zero_add, ↓reduceIte, sub_eq_add_neg]
      rw [mul_one]
      exact congrArg _ (neg_one_smul ℤ _).symm
    · intro j hj
      simp only [signedChar, show j + 1 ≠ 1 by omega, ↓reduceIte]
      exact zero_smul ℤ _
  exact h'.unique (WithPiTopology.hasProd_one_sub_X_pow ℤ)

/-- **Theorem 358.** Let `E(n)` and `U(n)` be the numbers of partitions of `n` into an even and an
odd number of unequal parts. Then `E(n) = U(n)` except when `n = k(3k ± 1)/2`
(`n = pentagonal k`, `k ∈ ℤ`), when `E(n) - U(n) = (-1)^k`. -/
@[kb "hardywright2008" "Thm 358, p. 397"]
theorem evenDistinctCount_sub_oddDistinctCount :
    (∀ k : ℤ, (evenDistinctCount (pentagonal k) : ℤ) - oddDistinctCount (pentagonal k) =
      (k.negOnePow : ℤ)) ∧
    ∀ n : ℕ, n ∉ Set.range pentagonal → evenDistinctCount n = oddDistinctCount n := by
  constructor
  · intro k
    rw [← coeff_genFun_signed, genFun_signedChar_eq, coeff_pentagonalSeries_pentagonal]
    rfl
  · intro n hn
    have h := coeff_genFun_signed n
    rw [genFun_signedChar_eq, coeff_pentagonalSeries_eq_zero ℤ hn] at h
    omega

end NTKB.HardyWright
