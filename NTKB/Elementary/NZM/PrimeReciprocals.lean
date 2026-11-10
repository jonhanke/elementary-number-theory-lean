/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Attr
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals

/-!
# A lower bound for the sum of prime reciprocals (Niven–Zuckerman–Montgomery, § 1.5)

* Theorem 1.19: for every real `y ≥ 2`, `∑_{p ≤ y} 1/p > log log y - 1`.

The proof follows the book: the Euler product over the primes `p ≤ y` dominates the harmonic sum
`∑_{n ≤ y} 1/n > log y`; taking logarithms and using `log (p/(p-1)) ≤ 1/(p-1) = 1/p + (1/(p-1) - 1/p)`
the error terms telescope to a sum less than `1`.
-/

open Finset

namespace NTKB.NZM

/-- The completely multiplicative function `n ↦ 1/n`, as a monoid homomorphism `ℕ →* ℝ`. -/
private noncomputable def invHom : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by simp
  map_mul' a b := by rw [Nat.cast_mul]; exact mul_inv _ _

theorem invHom_apply (n : ℕ) : invHom n = (n : ℝ)⁻¹ := rfl

theorem invHom_nonneg (n : ℕ) : 0 ≤ invHom n := by
  rw [invHom_apply]; exact inv_nonneg.2 (Nat.cast_nonneg n)

/-- For a prime `p`, `(1 - 1/p)⁻¹` is positive and its logarithm is at most `1/(p-1)`. -/
theorem prime_term {p : ℕ} (hp : p.Prime) :
    0 < (1 - (p : ℝ)⁻¹)⁻¹ ∧ Real.log ((1 - (p : ℝ)⁻¹)⁻¹) ≤ 1 / ((p : ℝ) - 1) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hp1' : (p : ℝ) - 1 ≠ 0 := hp1.ne'
  have h : 1 - (p : ℝ)⁻¹ = ((p : ℝ) - 1) / p := by
    rw [sub_div, div_self hp0.ne', one_div]
  have e : (1 - (p : ℝ)⁻¹)⁻¹ = 1 + 1 / ((p : ℝ) - 1) := by
    rw [h, inv_div, one_add_div hp1', sub_add_cancel]
  have hpos : 0 < (1 - (p : ℝ)⁻¹)⁻¹ := by
    rw [e]; have := one_div_pos.2 hp1; linarith
  refine ⟨hpos, ?_⟩
  calc Real.log ((1 - (p : ℝ)⁻¹)⁻¹) ≤ (1 - (p : ℝ)⁻¹)⁻¹ - 1 := Real.log_le_sub_one_of_pos hpos
    _ = 1 / ((p : ℝ) - 1) := by rw [e]; ring

/-- Telescoping: `∑_{2 ≤ n ≤ M} (1/(n-1) - 1/n) = 1 - 1/M`. -/
theorem sum_Icc_telescope (M : ℕ) (hM : 1 ≤ M) :
    ∑ n ∈ Icc 2 M, (1 / ((n : ℝ) - 1) - 1 / (n : ℝ)) = 1 - 1 / (M : ℝ) := by
  induction M, hM using Nat.le_induction with
  | base =>
    rw [Finset.Icc_eq_empty (by norm_num)]
    simp
  | succ M hM ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    have e : ((M + 1 : ℕ) : ℝ) - 1 = M := by push_cast; ring
    rw [e]
    ring

/-- The harmonic number as a real sum. -/
theorem harmonic_cast_eq (M : ℕ) :
    ((harmonic M : ℚ) : ℝ) = ∑ i ∈ Icc 1 M, invHom i := by
  rw [harmonic_eq_sum_Icc]
  simp [invHom_apply]

/-- **Theorem 1.19.** For every real `y ≥ 2`, `∑_{p ≤ y} 1/p > log log y - 1`, the sum being over
the primes `p ≤ y`. -/
@[kb "nivenzuckermanmontgomery" "Thm 1.19, p. 26"]
theorem sum_inv_primes_gt_log_log_sub_one {y : ℝ} (hy : 2 ≤ y) :
    Real.log (Real.log y) - 1 <
      ∑ p ∈ Finset.filter Nat.Prime (Finset.range (⌊y⌋₊ + 1)), (1 : ℝ) / p := by
  classical
  set M : ℕ := ⌊y⌋₊ with hMdef
  have hM2 : 2 ≤ M := Nat.le_floor (by exact_mod_cast hy)
  have hyM : y < (M : ℝ) + 1 := Nat.lt_floor_add_one y
  have hMpos : (0 : ℝ) < M := Nat.cast_pos.2 (by omega)
  have hS : Finset.filter Nat.Prime (Finset.range (M + 1)) = Nat.primesBelow (M + 1) := by
    ext p
    simp [Nat.mem_primesBelow]
  rw [hS]
  -- the Euler product dominates the harmonic sum
  have hnorm : ∀ {p : ℕ}, p.Prime → ‖invHom p‖ < 1 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    rw [Real.norm_of_nonneg (invHom_nonneg p), invHom_apply, inv_eq_one_div,
      div_lt_one (by linarith)]
    linarith
  obtain ⟨_, hsum⟩ :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
      (f := invHom) hnorm (M + 1)
  have hmem : ∀ n ∈ Icc 1 M, n ∈ (M + 1).smoothNumbers := by
    intro n hn
    have hn' := Finset.mem_Icc.1 hn
    exact Nat.mem_smoothNumbers_of_lt (by omega) (by omega)
  have hle := sum_le_hasSum ((Icc 1 M).subtype (fun n => n ∈ (M + 1).smoothNumbers))
    (fun i _ => invHom_nonneg i) hsum
  have hsub := Finset.sum_subtype_of_mem (s := Icc 1 M) (fun n : ℕ => invHom n)
    (p := fun n => n ∈ (M + 1).smoothNumbers) hmem
  have hle2 : ∑ n ∈ Icc 1 M, invHom n ≤
      ∏ p ∈ Nat.primesBelow (M + 1), (1 - invHom p)⁻¹ := (le_of_eq hsub.symm).trans hle
  have hprod_eq : ∏ p ∈ Nat.primesBelow (M + 1), (1 - invHom p)⁻¹ =
      ∏ p ∈ Nat.primesBelow (M + 1), (1 - (p : ℝ)⁻¹)⁻¹ :=
    Finset.prod_congr rfl (fun p _ => by rw [invHom_apply])
  have hH : Real.log ((M : ℝ) + 1) ≤ ((harmonic M : ℚ) : ℝ) := by
    have := log_add_one_le_harmonic M
    push_cast at this
    exact this
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have h1 : Real.log y < ∏ p ∈ Nat.primesBelow (M + 1), (1 - (p : ℝ)⁻¹)⁻¹ := by
    calc Real.log y < Real.log ((M : ℝ) + 1) := Real.log_lt_log (by linarith) hyM
      _ ≤ ((harmonic M : ℚ) : ℝ) := hH
      _ = ∑ i ∈ Icc 1 M, invHom i := harmonic_cast_eq M
      _ ≤ _ := hle2.trans hprod_eq.le
  have h2 : Real.log (Real.log y) <
      Real.log (∏ p ∈ Nat.primesBelow (M + 1), (1 - (p : ℝ)⁻¹)⁻¹) :=
    Real.log_lt_log hlogy h1
  have h3 : Real.log (∏ p ∈ Nat.primesBelow (M + 1), (1 - (p : ℝ)⁻¹)⁻¹) =
      ∑ p ∈ Nat.primesBelow (M + 1), Real.log ((1 - (p : ℝ)⁻¹)⁻¹) := by
    apply Real.log_prod
    intro p hp
    exact (prime_term (Nat.mem_primesBelow.1 hp).2).1.ne'
  have h4 : ∑ p ∈ Nat.primesBelow (M + 1), Real.log ((1 - (p : ℝ)⁻¹)⁻¹) ≤
      ∑ p ∈ Nat.primesBelow (M + 1), 1 / ((p : ℝ) - 1) :=
    Finset.sum_le_sum (fun p hp => (prime_term (Nat.mem_primesBelow.1 hp).2).2)
  have h5 : ∑ p ∈ Nat.primesBelow (M + 1), 1 / ((p : ℝ) - 1) =
      ∑ p ∈ Nat.primesBelow (M + 1), (1 : ℝ) / p +
        ∑ p ∈ Nat.primesBelow (M + 1), (1 / ((p : ℝ) - 1) - 1 / (p : ℝ)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  have h6 : ∑ p ∈ Nat.primesBelow (M + 1), (1 / ((p : ℝ) - 1) - 1 / (p : ℝ)) ≤
      ∑ n ∈ Icc 2 M, (1 / ((n : ℝ) - 1) - 1 / (n : ℝ)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro p hp
      obtain ⟨hlt, hpp⟩ := Nat.mem_primesBelow.1 hp
      exact Finset.mem_Icc.2 ⟨hpp.two_le, by omega⟩
    · intro n hn _
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.1 hn).1
      exact sub_nonneg.2 (one_div_le_one_div_of_le (by linarith) (by linarith))
  have h7 := sum_Icc_telescope M (by omega)
  have h8 : 0 < 1 / (M : ℝ) := one_div_pos.2 hMpos
  linarith

end NTKB.NZM
