/-
Copyright (c) 2026 The Tau Ceti contributors. Released under Apache 2.0 license.
Copied into NTKB with credit from Tau Ceti (`TauCeti/NumberTheory/JacobiSum/Quartic.lean`, with
`one_add_pow_four_of_sq_eq_neg_one` from `TauCeti/NumberTheory/NumberField/Cyclotomic/Four/Basic.lean`
and `MulChar.apply_neg_one_mul_self` from `TauCeti/NumberTheory/MulChar/Basic.lean`; main
`d2083f0f`, staged 2026-11-08); NTKB does not depend on Tau Ceti. Changes: namespace
`NTKB.Port`, no module system, the helpers inlined (`sq_eq_neg_one_of_isPrimitiveRoot` added for
the older Mathlib).
-/
import Mathlib.NumberTheory.JacobiSum.Basic
import Aesop.BuiltinRules
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
/-!
# The Jacobi sum of a quartic character (port from Tau Ceti)

Let `χ` be a multiplicative character with `χ ^ 4 = 1` on a finite field `F` with `q ≡ 1 (mod 4)`
elements, with values in an integral domain `R`, and let `ι ∈ R` be a primitive fourth root of
unity. Then `χ (-1) J(χ, χ) ≡ -1` modulo `(1 + ι) ^ 3` (Ireland–Rosen, proof of Proposition 9.9.3),
and `g(χ, ψ) ^ 4 = q J(χ, χ) ^ 2` for `χ` of order `4` (Proposition 9.9.2).

The proof evaluates `J(χ, χ) = ∑ t, χ (t) χ (1 - t)` term by term: the terms `t = 0, 1` vanish,
the term `t = 1 / 2` is `χ (1 / 4) = χ (-1)` since `-4 = (1 + j) ^ 4` for a square root `j` of `-1`
in `F`, and the remaining terms pair up `t ↔ 1 - t`, each pair contributing `2` modulo `2 (1 + ι)`.
-/

open Finset

namespace NTKB.Port

variable {F R : Type*} [Field F] [Fintype F] [CommRing R] [IsDomain R]

/-- A square root `x` of `-1` satisfies `(1 + x)⁴ = -4`. -/
theorem one_add_pow_four_of_sq_eq_neg_one {S : Type*} [CommRing S] {x : S} (hx : x ^ 2 = -1) :
    (1 + x) ^ 4 = -4 := by
  linear_combination (x ^ 2 + 4 * x + 5) * hx

/-- A multiplicative character takes a value at `-1` whose square is `1`. -/
theorem MulChar.apply_neg_one_mul_self {R R' : Type*} [CommMonoid R] [HasDistribNeg R]
    [CommMonoidWithZero R'] (χ : MulChar R R') : χ (-1) * χ (-1) = 1 := by
  rw [← map_mul, neg_one_mul, neg_neg, map_one]

omit [Fintype F] in
/-- A primitive fourth root of unity in a domain squares to `-1`. -/
theorem sq_eq_neg_one_of_isPrimitiveRoot {ι : R} (hι : IsPrimitiveRoot ι 4) : ι ^ 2 = -1 := by
  have h4 : ι ^ 2 * ι ^ 2 = 1 := by rw [← pow_add]; exact hι.pow_eq_one
  have h2 : ι ^ 2 ≠ 1 := hι.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  exact (mul_self_eq_one_iff.1 h4).resolve_left h2

omit [Fintype F] [IsDomain R] in
/-- The middle term `t = 1 / 2` of `J(χ, χ)`. -/
private theorem apply_inv_two_mul_apply_one_sub_inv_two {χ : MulChar F R} (hχ : χ ^ 4 = 1)
    (h2 : (2 : F) ≠ 0) (hF : IsSquare (-1 : F)) : χ 2⁻¹ * χ (1 - 2⁻¹) = χ (-1) := by
  obtain ⟨j, hj⟩ := hF
  have hj4 := one_add_pow_four_of_sq_eq_neg_one (by linear_combination -hj : j ^ 2 = -1)
  have hj0 : 1 + j ≠ 0 := by
    intro h
    rw [h] at hj4
    exact h2 (pow_eq_zero_iff two_ne_zero |>.mp (by linear_combination hj4))
  have hχ' : χ (-4) = 1 := by
    rw [← hj4, map_pow, ← MulChar.pow_apply' χ (by norm_num), hχ, MulChar.one_apply hj0.isUnit]
  rw [show (1 : F) - 2⁻¹ = 2⁻¹ by linear_combination -(mul_inv_cancel₀ h2), ← map_mul,
    ← mul_one (χ _), ← hχ', ← map_mul]
  congr 1
  linear_combination (-1 - 2⁻¹ * 2) * mul_inv_cancel₀ h2

/-- The terms of `J(χ, χ)` off `t ∈ {0, 1, 1 / 2}` contribute `0` modulo `(1 + ι) ^ 3` after
subtracting `1` from each. -/
private theorem one_add_pow_three_dvd_sum_erase_inv_two [DecidableEq F] {χ : MulChar F R}
    (hχ : χ ^ 4 = 1) {ι : R} (hι : IsPrimitiveRoot ι 4) (h2 : (2 : F) ≠ 0) :
    (1 + ι) ^ 3 ∣ ∑ t ∈ (univ \ {0, 1}).erase 2⁻¹, (χ t * χ (1 - t) - 1) := by
  have hsq := sq_eq_neg_one_of_isPrimitiveRoot hι
  have hS (t : F) : t ∈ (univ \ {0, 1}).erase 2⁻¹ ↔ t ≠ 2⁻¹ ∧ t ≠ 0 ∧ t ≠ 1 := by
    simp [not_or]
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, map_sum]
  refine sum_involution (fun t _ ↦ 1 - t) (fun t ht ↦ ?_) (fun t ht _ h ↦ ?_)
    (fun t ht ↦ ?_) (fun t _ ↦ sub_sub_cancel 1 t)
  · obtain ⟨-, ht0, ht1⟩ := (hS t).mp ht
    obtain ⟨m, -, hm⟩ :=
      χ.exists_apply_eq_pow hχ hι (mul_ne_zero ht0 (sub_ne_zero.mpr (Ne.symm ht1)))
    obtain ⟨c, hc⟩ : 1 + ι ∣ χ t * χ (1 - t) - 1 := by
      rw [← map_mul, hm]
      refine (Dvd.intro ι (by linear_combination hsq) : 1 + ι ∣ ι - 1).trans ?_
      simpa using sub_dvd_pow_sub_pow ι 1 m
    rw [← map_add, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, sub_sub_cancel,
      mul_comm (χ (1 - t))]
    exact ⟨-ι * c, by linear_combination 2 * hc + c * (1 + ι) * (ι + 2) * hsq⟩
  · exact ((hS t).mp ht).1 (eq_inv_of_mul_eq_one_left (by linear_combination -h))
  · obtain ⟨hth, ht0, ht1⟩ := (hS t).mp ht
    refine (hS _).mpr ⟨fun h ↦ hth ?_, sub_ne_zero.mpr (Ne.symm ht1), fun h ↦ ht0 ?_⟩
    · linear_combination -h - mul_inv_cancel₀ h2
    · linear_combination -h

/-- **The Jacobi sum of a quartic character.** If `χ ^ 4 = 1` on a finite field `F` with
`#F ≡ 1 (mod 4)`, with values in an integral domain containing a primitive fourth root of unity
`ι`, then `χ (-1) J(χ, χ) ≡ -1` modulo `(1 + ι) ^ 3`. -/
theorem one_add_pow_three_dvd_apply_neg_one_mul_jacobiSum_add_one {χ : MulChar F R}
    (hχ : χ ^ 4 = 1) (hq : 4 ∣ Fintype.card F - 1) {ι : R} (hι : IsPrimitiveRoot ι 4) :
    (1 + ι) ^ 3 ∣ χ (-1) * jacobiSum χ χ + 1 := by
  classical
  have hlt := Fintype.one_lt_card (α := F)
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card F = 4 * k + 5 :=
    ⟨(Fintype.card F - 5) / 4, by omega⟩
  have h2 : (2 : F) ≠ 0 :=
    Ring.two_ne_zero (by rw [ne_eq, FiniteField.even_card_iff_char_two]; omega)
  have hF : IsSquare (-1 : F) := FiniteField.isSquare_neg_one_iff.mpr (by omega)
  have hmem : (2 : F)⁻¹ ∈ (univ \ {0, 1} : Finset F) := by
    simp only [mem_sdiff, mem_univ, mem_insert, mem_singleton, inv_eq_zero, inv_eq_one, h2,
      true_and, false_or]
    exact fun h ↦ one_ne_zero (by linear_combination h : (1 : F) = 0)
  have hJ : jacobiSum χ χ = χ (-1) + ∑ t ∈ (univ \ {0, 1}).erase 2⁻¹, (χ t * χ (1 - t) - 1) +
      (4 * k + 2 : ℕ) := by
    rw [jacobiSum_eq_sum_sdiff, ← add_sum_erase _ _ hmem,
      apply_inv_two_mul_apply_one_sub_inv_two hχ h2 hF, sum_sub_distrib, sum_const,
      card_erase_of_mem hmem, card_univ_sdiff, card_pair zero_ne_one, hk, nsmul_one,
      show 4 * k + 5 - 2 - 1 = 4 * k + 2 by omega]
    ring
  have hsq := sq_eq_neg_one_of_isPrimitiveRoot hι
  obtain ⟨c, hc⟩ := one_add_pow_three_dvd_sum_erase_inv_two hχ hι h2
  obtain ⟨d, hd⟩ : (1 + ι) ^ 3 ∣ (4 : R) :=
    Dvd.intro (-(1 + ι)) (by linear_combination -one_add_pow_four_of_sq_eq_neg_one hsq)
  rw [hJ, hc]
  push_cast
  rcases mul_self_eq_one_iff.mp (MulChar.apply_neg_one_mul_self χ) with h | h <;> rw [h]
  · exact ⟨c + d * (k + 1), by linear_combination ((k : R) + 1) * hd⟩
  · exact ⟨-c - d * k, by linear_combination -(k : R) * hd⟩

/-- **The fourth power of a quartic Gauss sum.** If `χ` has order `4` on a finite field `F` and
`ψ` is a primitive additive character of `F`, then `g(χ, ψ) ^ 4 = #F * J(χ, χ) ^ 2`. -/
theorem gaussSum_pow_four_eq_card_mul_jacobiSum_sq {χ : MulChar F R} (hχ : orderOf χ = 4)
    {ψ : AddChar F R} (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ ^ 4 = Fintype.card F * jacobiSum χ χ ^ 2 := by
  have h1 : χ ^ 2 ≠ 1 := fun h ↦ by
    have := Nat.le_of_dvd two_pos (hχ ▸ orderOf_dvd_of_pow_eq_one h)
    omega
  have hquad : (χ ^ 2).IsQuadratic := by
    rw [MulChar.isQuadratic_iff_sq_eq_one, ← pow_mul, show 2 * 2 = orderOf χ by omega,
      pow_orderOf_eq_one]
  have hneg : (χ ^ 2) (-1) = 1 := by
    rw [MulChar.pow_apply' χ two_ne_zero, ← map_pow, neg_one_sq, map_one]
  have hJ := jacobiSum_mul_nontrivial (by rwa [← sq]) ψ
  rw [← sq, ← sq] at hJ
  rw [show 4 = 2 * 2 by rfl, pow_mul, ← hJ, mul_pow, gaussSum_sq h1 hquad hψ, hneg, one_mul]

end NTKB.Port
