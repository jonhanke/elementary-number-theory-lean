/-
Ireland–Rosen, Chapter 8, §6, Proposition 8.6.1: the number of solutions of
`x_1² + x_2² + ⋯ + x_r² = 1` in a finite field `F` with `q` elements, `q` odd, by Jacobi sums
(`N = q^{r-1} + J(ρ, …, ρ)`, `ρ` the quadratic character).
-/
import NTKB.IrelandRosen.R2.FermatCurve
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace NTKB.IrelandRosen

variable {F : Type*} [Field F] [Fintype F]

/-- For a character `ρ` of order `2`, `ρ(-1) = (-1)^{(q-1)/2}`. -/
lemma quadratic_apply_neg_one (hq : Odd (Fintype.card F)) {ρ : MulChar F ℂ}
    (hρ : orderOf ρ = 2) : ρ (-1) = (-1) ^ ((Fintype.card F - 1) / 2) := by
  have h2 : 2 ∣ Fintype.card F - 1 := by obtain ⟨k, hk⟩ := hq; omega
  have hN := numSolPow_eq_sum_range h2 hρ (-1 : F)
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, pow_zero,
    pow_one, bookChar_one, bookChar_of_ne_zero _ (neg_ne_zero.mpr (one_ne_zero (α := F)))] at hN
  try rw [MulChar.one_apply (Ne.isUnit (neg_ne_zero.mpr (one_ne_zero (α := F))))] at hN
  have hsq := FiniteField.isSquare_neg_one_iff (F := F)
  obtain ⟨k, hk⟩ := hq
  have hcases := numSolPow_neg_one (F := F) h2
  by_cases h4 : Fintype.card F % 4 = 3
  · have hns : ¬∃ x : F, x ^ 2 = -1 := by
      rintro ⟨x, hx⟩; exact (hsq.mp ⟨x, by rw [← hx]; ring⟩) h4
    rw [hcases, if_neg hns] at hN
    have : (Fintype.card F - 1) / 2 = 2 * (k / 2) + 1 := by omega
    rw [this, pow_succ, pow_mul]; norm_num
    linear_combination -hN
  · obtain ⟨x, hx⟩ := hsq.mpr h4
    have hs : ∃ y : F, y ^ 2 = -1 := ⟨x, by rw [hx]; ring⟩
    rw [hcases, if_pos hs] at hN
    have : (Fintype.card F - 1) / 2 = 2 * (k / 2) := by omega
    rw [this, pow_mul]; norm_num
    push_cast at hN
    linear_combination -hN

lemma quadratic_unique (h2 : 2 ∣ Fintype.card F - 1) {ρ : MulChar F ℂ} (hρ : orderOf ρ = 2)
    {ψ : MulChar F ℂ} (hψ2 : ψ ^ 2 = 1) (hψ1 : ψ ≠ 1) : ψ = ρ := by
  have h := (filter_pow_eq_one_eq_image h2 hρ).1
  have : ψ ∈ ({φ : MulChar F ℂ | φ ^ 2 = 1} : Finset _) := by simpa using hψ2
  rw [h] at this
  simp only [mem_image, mem_range] at this
  obtain ⟨i, hi, rfl⟩ := this
  interval_cases i
  · exact absurd (pow_zero ρ) hψ1
  · exact pow_one ρ

/-- `N(x_1² + ⋯ + x_r² = 1) = q^{r-1} + J(ρ, …, ρ)`. -/
lemma numSolDiag_sum_sq_eq (h2 : 2 ∣ Fintype.card F - 1) {ρ : MulChar F ℂ} (hρ : orderOf ρ = 2)
    (r : ℕ) :
    (numSolDiag (fun _ : Fin (r + 1) => (1 : F)) (fun _ => 2) 1 : ℂ) =
      (Fintype.card F : ℂ) ^ r + multiJacobiSum (fun _ : Fin (r + 1) => ρ) := by
  rw [numSolDiag_eq_main_add (fun _ => one_ne_zero) (fun _ => h2)]
  congr 1
  have hρ1 : ρ ≠ 1 := by rintro rfl; simp at hρ
  have hρ2 : ρ ^ 2 = 1 := by rw [← hρ]; exact pow_orderOf_eq_one ρ
  have hT : ({χ ∈ charTuples (F := F) (fun _ : Fin (r + 1) => 2) | ∀ i, χ i ≠ 1} : Finset _) =
      {fun _ => ρ} := by
    ext χ
    simp only [mem_filter, charTuples, Fintype.mem_piFinset, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨hpow, hne⟩
      funext i; exact quadratic_unique h2 hρ (hpow i) (hne i)
    · rintro rfl; exact ⟨fun _ => hρ2, fun _ => hρ1⟩
  rw [hT, sum_singleton]
  simp [multiJacobiSum]

/-- `J(ρ, …, ρ) = (ρ(-1) q)^k` for `2k + 1` copies of `ρ`. -/
lemma multiJacobiSum_quadratic_odd {ρ : MulChar F ℂ} (hρ : orderOf ρ = 2) (k : ℕ) :
    multiJacobiSum (fun _ : Fin (2 * k + 1) => ρ) = (ρ (-1) * Fintype.card F) ^ k := by
  obtain ⟨ψ, hψ⟩ := exists_isPrimitive_addChar (F := F)
  have hρ1 : ρ ≠ 1 := by rintro rfl; simp at hρ
  have hρ2 : ρ ^ 2 = 1 := by rw [← hρ]; exact pow_orderOf_eq_one ρ
  have hprod : ∏ _i : Fin (2 * k + 1), ρ = ρ := by
    rw [prod_const, card_univ, Fintype.card_fin, pow_succ, pow_mul, hρ2, one_pow, one_mul]
  have h3 := prod_gaussSum_eq_multiJacobiSum_mul (χ := fun _ : Fin (2 * k + 1) => ρ)
    (fun _ => hρ1) (by rw [hprod]; exact hρ1) ψ
  rw [hprod, prod_const, card_univ, Fintype.card_fin, pow_succ] at h3
  have hg := gaussSum_ne_zero_of_quadratic hρ1 hψ
  have hinv : ρ⁻¹ = ρ := by rw [inv_eq_iff_mul_eq_one, ← sq]; exact hρ2
  have hsq := gaussSum_mul_gaussSum_inv hρ1 hψ
  rw [hinv] at hsq
  have := mul_right_cancel₀ hg h3
  rw [← this, pow_mul, sq, hsq]
where
  gaussSum_ne_zero_of_quadratic {ρ : MulChar F ℂ} (hρ1 : ρ ≠ 1) {ψ : AddChar F ℂ}
      (hψ : ψ.IsPrimitive) : gaussSum ρ ψ ≠ 0 := by
    intro h
    have := norm_gaussSum hρ1 hψ
    rw [h, norm_zero] at this
    have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
    exact (Real.sqrt_pos.mpr hq).ne' this.symm

/-- **Proposition 8.6.1, `r` odd.** For `q` odd and `r = 2k + 1`,
`N(x_1² + ⋯ + x_r² = 1) = q^{r-1} + (-1)^{((r-1)/2)((q-1)/2)} q^{(r-1)/2}`. -/
@[kb "irelandrosen1990" "Prop 8.6.1, p. 113"]
theorem numSolDiag_sum_sq_odd (hq : Odd (Fintype.card F)) (k : ℕ) :
    (numSolDiag (fun _ : Fin (2 * k + 1) => (1 : F)) (fun _ => 2) 1 : ℂ) =
      (Fintype.card F : ℂ) ^ (2 * k) +
        (-1) ^ (k * ((Fintype.card F - 1) / 2)) * (Fintype.card F : ℂ) ^ k := by
  have h2 : 2 ∣ Fintype.card F - 1 := by obtain ⟨j, hj⟩ := hq; omega
  obtain ⟨ρ, hρ⟩ := exists_orderOf_eq h2
  rw [numSolDiag_sum_sq_eq h2 hρ, multiJacobiSum_quadratic_odd hρ, quadratic_apply_neg_one hq hρ,
    mul_pow, ← pow_mul, mul_comm ((Fintype.card F - 1) / 2) k]

/-- **Proposition 8.6.1, `r` even.** For `q` odd and `r = 2k + 2`,
`N(x_1² + ⋯ + x_r² = 1) = q^{r-1} - (-1)^{(r/2)((q-1)/2)} q^{r/2 - 1}`. -/
@[kb "irelandrosen1990" "Prop 8.6.1, p. 113"]
theorem numSolDiag_sum_sq_even (hq : Odd (Fintype.card F)) (k : ℕ) :
    (numSolDiag (fun _ : Fin (2 * k + 2) => (1 : F)) (fun _ => 2) 1 : ℂ) =
      (Fintype.card F : ℂ) ^ (2 * k + 1) -
        (-1) ^ ((k + 1) * ((Fintype.card F - 1) / 2)) * (Fintype.card F : ℂ) ^ k := by
  have h2 : 2 ∣ Fintype.card F - 1 := by obtain ⟨j, hj⟩ := hq; omega
  obtain ⟨ρ, hρ⟩ := exists_orderOf_eq h2
  obtain ⟨ψ, hψ⟩ := exists_isPrimitive_addChar (F := F)
  have hρ1 : ρ ≠ 1 := by rintro rfl; simp at hρ
  have hρ2 : ρ ^ 2 = 1 := by rw [← hρ]; exact pow_orderOf_eq_one ρ
  have hprod : ∏ _i : Fin (2 * k + 2), ρ = 1 := by
    rw [prod_const, card_univ, Fintype.card_fin, show 2 * k + 2 = 2 * (k + 1) by ring, pow_mul,
      hρ2, one_pow]
  rw [numSolDiag_sum_sq_eq h2 hρ (2 * k + 1)]
  have hJ := multiJacobiSum_eq_of_prod_eq_one (r := 2 * k) (χ := fun _ => ρ) (fun _ => hρ1) hprod hψ
  have hinit : (Fin.init fun _ : Fin (2 * k + 2) => ρ) = fun _ : Fin (2 * k + 1) => ρ := rfl
  rw [hinit, multiJacobiSum_quadratic_odd hρ] at hJ
  rw [hJ, quadratic_apply_neg_one hq hρ, mul_pow, ← pow_mul, add_mul, one_mul, pow_add]
  ring

end NTKB.IrelandRosen
