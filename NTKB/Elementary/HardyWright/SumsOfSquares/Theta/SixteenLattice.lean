/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.SixLattice

/-!
# Weighted lattice sums of weight `8`

The weight-`8` analogue of `SixLattice.lean`. For `w : ℤ² → ℂ` bounded,
`L_w(τ) = ∑_{v ∈ ℤ²} w(v) (v₀ τ + v₁)⁻⁸` (`Lsum8`; Mathlib's `eisSummand 8`).

* `Lsum8_smul`: `L_w(γ τ) = (cτ + d)⁸ L_{w ∘ γ⁻¹}(τ)` for `γ ∈ SL(2, ℤ)`;
* `mdiff_Lsum8`: `L_w` is holomorphic;
* the weight `W(m, n) = [m even, n odd] + [m odd, n even]` satisfies `L_W(-1/τ) = -τ⁸ L_W(τ)`
  (`Lsum8_W_S`) and `L_W(τ + 2) = L_W(τ)` (`Lsum8_W_T2`), the transformation laws of `θ(τ)¹⁶`;
  and `L_W(TS τ) = τ⁸ L_{W'}(τ)` with `W'` vanishing on `v₀` even (`Wp_eq_zero_of_even`).
-/

open ModularForm ModularGroup Complex Filter Topology EisensteinSeries Matrix
open scoped MatrixGroups Real UpperHalfPlane Manifold
open UpperHalfPlane hiding I

noncomputable section

namespace NTKB.HardyWright.SixteenSquares

open EightSquares (mdiff_of_eqOn coe_TS denom_TS)
open SixSquares (vmEquiv vecMul_SL_inv isOpen_strip)

/-! ### Lattice sums of weight `8` -/

/-- `L_w(τ) = ∑_{v ∈ ℤ²} w(v) (v₀ τ + v₁)⁻⁸`.
  **Restriction:** the lattice sum converges absolutely when the weight `w` is bounded (a hypothesis not enforced by
  the type; see `summable_Lsum8`); where it does not converge the value is $0$ by Lean's `tsum` convention, not the
  intended value. -/
def Lsum8 (w : (Fin 2 → ℤ) → ℂ) (z : ℍ) : ℂ := ∑' v, w v * eisSummand 8 v z

lemma summable_Lsum8 {w : (Fin 2 → ℤ) → ℂ} {B : ℝ} (hw : ∀ v, ‖w v‖ ≤ B) (z : ℍ) :
    Summable fun v => w v * eisSummand 8 v z := by
  refine Summable.of_norm_bounded
    ((summable_norm_eisSummand (k := 8) (by norm_num) z).mul_left B) fun v => ?_
  rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hw v) (norm_nonneg _)

/-- `L_w(A τ) = (cτ + d)⁸ L_{w ∘ A⁻¹}(τ)`. -/
lemma Lsum8_smul (w : (Fin 2 → ℤ) → ℂ) (A : SL(2, ℤ)) (z : ℍ) :
    Lsum8 w (A • z) = denom A z ^ 8 *
      Lsum8 (fun v => w (v ᵥ* ((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))) z := by
  simp only [Lsum8, eisSummand_SL2_apply]
  rw [← tsum_mul_left]
  rw [← (vmEquiv A).tsum_eq (fun u => denom A z ^ 8 *
    (w (u ᵥ* ((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) * eisSummand 8 u z))]
  refine tsum_congr fun v => ?_
  simp only [vmEquiv, Equiv.coe_fn_mk]
  rw [vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, vecMul_one]
  have : (denom A z) ^ (8 : ℤ) = (denom A z) ^ (8 : ℕ) := by norm_cast
  rw [this]; ring

/-! ### Holomorphy -/

lemma mdiff_Lsum8 {w : (Fin 2 → ℤ) → ℂ} {B : ℝ} (hw : ∀ v, ‖w v‖ ≤ B) : MDiff (Lsum8 w) := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hw 0)
  set F : (Fin 2 → ℤ) → ℂ → ℂ := fun v z => w v * (eisSummand 8 v ∘ ofComplex) z with hF
  have hdiff : DifferentiableOn ℂ (fun z => ∑' v, F v z) {z : ℂ | 0 < z.im} := by
    intro z0 hz0
    have hz0' : (0 : ℝ) < z0.im := hz0
    set A : ℝ := |z0.re| + 1
    set B' : ℝ := z0.im / 2
    have hB' : 0 < B' := by positivity
    set V := {z : ℂ | |z.re| < A ∧ B' < z.im}
    have hV : IsOpen V := isOpen_strip A B'
    have hzV : z0 ∈ V := ⟨by simp [A], by simp only [B']; linarith⟩
    have hVU : V ⊆ {z : ℂ | 0 < z.im} := fun z hz => by
      simp only [Set.mem_ofPred_eq] at hz ⊢; linarith [hz.2]
    have hd : DifferentiableOn ℂ (fun z => ∑' v, F v z) V := by
      refine differentiableOn_tsum_of_summable_norm
        (u := fun v => B * (r ⟨⟨A, B'⟩, hB'⟩ ^ (-(8 : ℝ)) * ‖v‖ ^ (-(8 : ℝ))))
        (((summable_one_div_norm_rpow (k := 8) (by norm_num)).mul_left _).mul_left B)
        (fun v => ((eisSummand_extension_differentiableOn 8 v).const_mul (w v)).mono hVU) hV ?_
      intro v z hz
      have hzU : 0 < z.im := hVU hz
      have hmem : ofComplex z ∈ verticalStrip A B' := by
        rw [ofComplex_apply_of_im_pos hzU]
        exact ⟨hz.1.le, hz.2.le⟩
      simp only [hF, Function.comp_apply, norm_mul]
      refine mul_le_mul (hw v) ?_ (norm_nonneg _) hB
      simp only [eisSummand, norm_zpow]
      have := summand_bound_of_mem_verticalStrip (k := 8) (by norm_num) v hB' hmem
      exact_mod_cast this
    exact (hd.differentiableAt (hV.mem_nhds hzV)).differentiableWithinAt
  refine mdiff_of_eqOn hdiff fun τ => ?_
  simp only [Lsum8, hF, Function.comp_apply, ofComplex_apply]

/-! ### The weight `W` -/

/-- `W(m, n) = [m even, n odd] + [m odd, n even]`. -/
def W (v : Fin 2 → ℤ) : ℂ :=
  (if Even (v 0) ∧ ¬ Even (v 1) then 1 else 0) + (if ¬ Even (v 0) ∧ Even (v 1) then 1 else 0)

lemma norm_W_le (v : Fin 2 → ℤ) : ‖W v‖ ≤ 1 := by
  unfold W
  by_cases h0 : Even (v 0) <;> by_cases h1 : Even (v 1) <;> simp [h0, h1]

lemma W_S (v : Fin 2 → ℤ) :
    W (v ᵥ* ((S⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) = W v := by
  rw [vecMul_SL_inv]
  simp only [S, Matrix.SpecialLinearGroup.coe_mk, of_apply, cons_val', cons_val_zero, cons_val_one,
    empty_val', cons_val_fin_one]
  simp only [W, cons_val_zero, cons_val_one]
  have e1 : v 0 * 0 - v 1 * 1 = -v 1 := by ring
  have e2 : -(v 0 * -1) + v 1 * 0 = v 0 := by ring
  simp only [e1, e2, even_neg]
  by_cases h0 : Even (v 0) <;> by_cases h1 : Even (v 1) <;> simp [h0, h1]

lemma Lsum8_W_S (z : ℍ) : Lsum8 W (S • z) = (z : ℂ) ^ 8 * Lsum8 W z := by
  rw [Lsum8_smul, denom_S]
  simp_rw [W_S]

lemma W_T2 (v : Fin 2 → ℤ) :
    W (v ᵥ* (((T ^ (2 : ℤ))⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) = W v := by
  rw [vecMul_SL_inv]
  simp only [coe_T_zpow, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one]
  simp only [W, cons_val_zero, cons_val_one]
  have e1 : v 0 * 1 - v 1 * 0 = v 0 := by ring
  have hev : Even (-(v 0 * 2) + v 1 * 1) ↔ Even (v 1) := by
    rw [show -(v 0 * 2) + v 1 * 1 = v 1 + 2 * (-(v 0)) by ring]
    exact Int.even_add.trans (by simp)
  simp only [e1, hev]

lemma Lsum8_W_T2 (z : ℍ) : Lsum8 W (T ^ (2 : ℤ) • z) = Lsum8 W z := by
  rw [Lsum8_smul]
  simp_rw [W_T2]
  have : denom (T ^ (2 : ℤ) : SL(2, ℤ)) z = 1 := by
    rw [ModularGroup.denom_apply, coe_T_zpow]; simp
  rw [this, one_pow, one_mul]

/-- `W' = W ∘ (TS)⁻¹`. -/
def Wp (v : Fin 2 → ℤ) : ℂ := W (v ᵥ* (((T * S)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))

lemma Lsum8_W_TS (z : ℍ) : Lsum8 W ((T * S) • z) = (z : ℂ) ^ 8 * Lsum8 Wp z := by
  rw [Lsum8_smul, denom_TS]; rfl

lemma norm_Wp_le (v : Fin 2 → ℤ) : ‖Wp v‖ ≤ 1 := norm_W_le _

lemma Wp_eq_zero_of_even (v : Fin 2 → ℤ) (h : Even (v 0)) : Wp v = 0 := by
  unfold Wp
  rw [vecMul_SL_inv, coe_TS]
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
  simp only [W, cons_val_zero, cons_val_one]
  have e1 : v 0 * 0 - v 1 * 1 = -v 1 := by ring
  have e2 : -(v 0 * -1) + v 1 * 1 = v 0 + v 1 := by ring
  simp only [e1, e2, even_neg]
  have h01 : Even (v 0 + v 1) ↔ Even (v 1) := by
    rw [Int.even_add]; exact ⟨fun h' => h'.mp h, fun h' => ⟨fun _ => h', fun _ => h⟩⟩
  by_cases h1 : Even (v 1) <;> simp [h1, h01]

end NTKB.HardyWright.SixteenSquares
