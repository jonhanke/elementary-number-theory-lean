/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.Partitions.Conjugate
import NTKB.Analytic.Apostol.Partitions.Euler
import NTKB.Analytic.Apostol.Partitions.JacobiTriple
import NTKB.Analytic.Apostol.Partitions.JacobiCube

/-!
# Partitions: conjugation, generating functions, Jacobi's identities (Hardy–Wright, Chapter XIX, §§ 19.2–19.10)

The statements of Hardy–Wright's Chapter XIX that coincide with results already formalised for
Apostol's Chapter 14 (`NTKB.Analytic.Apostol.Partitions.*`), in the notation of the book:

* Theorem 342: the number of partitions of `n` into `m` parts equals the number of partitions of
  `n` into parts the largest of which is `m` (reflection of the Ferrers graph in the diagonal,
  Mathlib's `Nat.Partition.conjugate`).
* Theorem 343: the number of partitions of `n` into at most `m` parts equals the number of
  partitions of `n` into parts which do not exceed `m` (the same bijection).
* (19.3.1): Euler's generating function `(1 - x)(1 - x²)(1 - x³)… · ∑ p(n) xⁿ = 1` as formal power
  series (Hardy–Wright prove it for `0 < x < 1` by a limit argument; the formal identity gives the
  same coefficients).
* (19.10.2): the recurrence `p(n) - p(n-1) - p(n-2) + p(n-5) + … = 0` coming from Euler's
  pentagonal number theorem.
* Theorem 352 (Jacobi's triple product identity): for `‖x‖ < 1` and `z ≠ 0`,
  `∏_{n ≥ 1} (1 - x^{2n})(1 + x^{2n-1} z)(1 + x^{2n-1} z⁻¹) = ∑_{n ∈ ℤ} x^{n²} zⁿ`, and the second
  form `1 + ∑_{n ≥ 1} x^{n²} (zⁿ + z⁻ⁿ)` of the series. This is the identity proved in
  `NTKB.Apostol.jacobi_triple_product` (via the finite `q`-binomial theorem and Tannery's theorem).
* Theorem 357 (Jacobi): `∏_{n ≥ 1} (1 - xⁿ)³ = ∑_{m ≥ 0} (-1)^m (2m + 1) x^{m(m+1)/2}`.
-/

open Finset PowerSeries
open scoped PowerSeries.WithPiTopology

namespace NTKB.HardyWright

/-! ### Theorems 342 and 343 -/

/-- **Theorem 342.** The number of partitions of `n` into `m` parts is equal to the number of
partitions of `n` into parts the largest of which is `m`. -/
@[kb "hardywright2008" "Thm 342, p. 381"]
theorem card_partitions_parts_eq_card_partitions_largest (n m : ℕ) :
    (Finset.univ.filter fun p : n.Partition => p.parts.card = m).card =
      (Finset.univ.filter fun p : n.Partition => p.parts.sup = m).card :=
  NTKB.Apostol.card_partition_card_parts_eq n m

/-- **Theorem 343.** The number of partitions of `n` into at most `m` parts is equal to the number of
partitions of `n` into parts which do not exceed `m`. -/
@[kb "hardywright2008" "Thm 343, p. 381"]
theorem card_partitions_parts_le_eq_card_partitions_largest_le (n m : ℕ) :
    (Finset.univ.filter fun p : n.Partition => p.parts.card ≤ m).card =
      (Finset.univ.filter fun p : n.Partition => p.parts.sup ≤ m).card := by
  refine Finset.card_bij' (fun p _ => p.conjugate) (fun p _ => p.conjugate) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    have h := NTKB.Apostol.card_parts_conjugate p.conjugate
    rw [Nat.Partition.conjugate_conjugate] at h
    rw [← h]; exact hp
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    rw [NTKB.Apostol.card_parts_conjugate]; exact hp
  · intro p _; exact Nat.Partition.conjugate_conjugate p
  · intro p _; exact Nat.Partition.conjugate_conjugate p

/-! ### The generating function of `p(n)` -/

/-- **(19.3.1).** Euler's generating function of `p(n)`, the number of partitions of `n`:
`(1 - x)(1 - x²)(1 - x³)… · (1 + ∑_{n ≥ 1} p(n) xⁿ) = 1`, as formal power series over any
topological commutative ring (in the book, for `0 < x < 1`; `p(0) = 1`). -/
@[kb "hardywright2008" "(19.3.1), p. 382"]
theorem tprod_one_sub_X_pow_mul_partitionSeries (R : Type*) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [T2Space R] :
    (∏' n : ℕ, (1 - X ^ (n + 1) : R⟦X⟧)) * NTKB.Apostol.partitionSeries R = 1 := by
  rw [mul_comm]; exact NTKB.Apostol.partitionSeries_mul_tprod_one_sub_X_pow R

/-- **(19.10.2).** For `n ≥ 1`, `p(n) - p(n-1) - p(n-2) + p(n-5) + … = 0`, i.e.
`∑_k (-1)^k p(n - k(3k-1)/2) = 0`, the sum over all integers `k` with `k(3k-1)/2 ≤ n`
(`pentagonal k = k(3k-1)/2`; positive and negative `k` give the two kinds of terms
`p(n - k(3k∓1)/2)` of the book). -/
@[kb "hardywright2008" "(19.10.2), p. 397"]
theorem card_partition_pentagonal_recurrence {n : ℕ} (hn : n ≠ 0) :
    ∑ k ∈ (Icc (-(n : ℤ)) n).filter (fun k ↦ pentagonal k ≤ n),
      (k.negOnePow : ℤ) * (Fintype.card (n - pentagonal k).Partition : ℤ) = 0 :=
  NTKB.Apostol.sum_negOnePow_card_partition_sub_pentagonal hn

/-! ### Jacobi's identities -/

/-- **Theorem 352** (Jacobi). If `‖x‖ < 1` and `z ≠ 0`, then
`∏_{n ≥ 1} (1 - x^{2n})(1 + x^{2n-1} z)(1 + x^{2n-1} z⁻¹) = ∑_{n ∈ ℤ} x^{n²} zⁿ`
(the series converging absolutely). -/
@[kb "hardywright2008" "Thm 352, p. 391"]
theorem jacobi_triple {x z : ℂ} (hx : ‖x‖ < 1) (hz : z ≠ 0) :
    Summable (fun n : ℤ ↦ x ^ (n ^ 2) * z ^ n) ∧
    HasProd (fun n : ℕ ↦ (1 - x ^ (2 * n + 2)) * (1 + x ^ (2 * n + 1) * z) *
      (1 + x ^ (2 * n + 1) * z⁻¹)) (∑' n : ℤ, x ^ (n ^ 2) * z ^ n) :=
  NTKB.Apostol.jacobi_triple_product hx hz

/-- **Theorem 352**, second form of the series: the product in the Jacobi triple product identity is
also `1 + ∑_{n ≥ 1} x^{n²} (zⁿ + z⁻ⁿ)`. -/
@[kb "hardywright2008" "Thm 352, p. 391"]
theorem jacobi_triple_symm {x z : ℂ} (hx : ‖x‖ < 1) (hz : z ≠ 0) :
    HasProd (fun n : ℕ ↦ (1 - x ^ (2 * n + 2)) * (1 + x ^ (2 * n + 1) * z) *
      (1 + x ^ (2 * n + 1) * z⁻¹))
      (1 + ∑' n : ℕ, x ^ ((n + 1) ^ 2) * (z ^ (n + 1) + z⁻¹ ^ (n + 1))) := by
  obtain ⟨hs, hp⟩ := jacobi_triple hx hz
  convert hp using 1
  set f : ℤ → ℂ := fun n ↦ x ^ (n ^ 2) * z ^ n with hf
  have h1 : Summable fun n : ℕ ↦ f n := hs.comp_injective Nat.cast_injective
  have h2 : Summable fun n : ℕ ↦ f (-((n : ℤ) + 1)) :=
    hs.comp_injective (fun a b h ↦ by simpa using h)
  have h1' : Summable fun n : ℕ ↦ f ((n + 1 : ℕ) : ℤ) := (summable_nat_add_iff 1).2 h1
  have e : ∀ n : ℕ, x ^ ((n + 1) ^ 2) * (z ^ (n + 1) + z⁻¹ ^ (n + 1)) =
      f ((n + 1 : ℕ) : ℤ) + f (-((n : ℤ) + 1)) := by
    intro n
    simp only [hf, zpow_neg, zpow_natCast, neg_sq, inv_pow]
    push_cast
    simp only [← zpow_natCast]
    push_cast
    ring_nf
  simp_rw [e]
  rw [tsum_of_nat_of_neg_add_one h1 h2, h1.tsum_eq_zero_add, h1'.tsum_add h2]
  simp [hf, add_assoc]

/-- **Theorem 357** (Jacobi). `∏_{n ≥ 1} (1 - xⁿ)³ = ∑_{m ≥ 0} (-1)^m (2m + 1) x^{m(m+1)/2}`
for `‖x‖ < 1`. -/
@[kb "hardywright2008" "Thm 357, p. 396"]
theorem jacobi_cube_identity {x : ℂ} (hx : ‖x‖ < 1) :
    HasProd (fun n : ℕ ↦ (1 - x ^ (n + 1)) ^ 3)
      (∑' m : ℕ, (-1) ^ m * (2 * m + 1) * x ^ (m * (m + 1) / 2)) :=
  NTKB.Apostol.apostol_thm_14_7 hx

end NTKB.HardyWright
