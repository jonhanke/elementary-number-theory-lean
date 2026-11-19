/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TenVanish
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.SixLattice

/-!
# Weighted lattice sums of weight `9`

For `w : ℤ² → ℂ` bounded, `L_w(τ) = ∑_{v ∈ ℤ²} w(v) (v₀ τ + v₁)⁻⁹` (`Lsum9`; Mathlib's
`eisSummand 9`).

* `Lsum9_smul`: `L_w(γ τ) = (cτ + d)⁹ L_{w ∘ γ⁻¹}(τ)` for `γ ∈ SL(2, ℤ)`;
* `mdiff_Lsum9`: `L_w` is holomorphic;
* the weight `W(m, n) = [m even] χ(n) + i [n even] χ(m)`, `χ` the non-principal character modulo
  `4`, satisfies `L_W(-1/τ) = -i τ⁹ L_W(τ)` (`Lsum9_W_S`) and `L_W(τ + 2) = L_W(τ)`
  (`Lsum9_W_T2`), the transformation laws of `θ(τ)¹⁸`; and `L_W(TS τ) = τ⁹ L_{W'}(τ)` with `W'`
  vanishing on `v₀` even (`Wp_eq_zero_of_even`).

This is the weight-nine analogue of `SixLattice.lean`.
-/

open ModularForm ModularGroup Complex Filter Topology EisensteinSeries Matrix
open scoped MatrixGroups Real UpperHalfPlane Manifold
open UpperHalfPlane hiding I

noncomputable section

namespace NTKB.HardyWright.EighteenSquares

open EightSquares (mdiff_of_eqOn coe_TS denom_TS)
open SixSquares (chiZ chiZ_neg chiZ_of_even chiZ_add_four_mul norm_ite_chiZ_le vmEquiv
  vecMul_SL_inv isOpen_strip)

/-- `L_w(τ) = ∑_{v ∈ ℤ²} w(v) (v₀ τ + v₁)⁻⁹`.
  **Restriction:** the lattice sum converges absolutely when the weight `w` is bounded (a hypothesis not enforced by
  the type; see `summable_Lsum9`); where it does not converge the value is $0$ by Lean's `tsum` convention, not the
  intended value. -/
def Lsum9 (w : (Fin 2 → ℤ) → ℂ) (z : ℍ) : ℂ := ∑' v, w v * eisSummand 9 v z

lemma summable_Lsum9 {w : (Fin 2 → ℤ) → ℂ} {B : ℝ} (hw : ∀ v, ‖w v‖ ≤ B) (z : ℍ) :
    Summable fun v => w v * eisSummand 9 v z := by
  refine Summable.of_norm_bounded
    ((summable_norm_eisSummand (k := 9) (by norm_num) z).mul_left B) fun v => ?_
  rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hw v) (norm_nonneg _)

/-- `L_w(A τ) = (cτ + d)⁹ L_{w ∘ A⁻¹}(τ)`. -/
lemma Lsum9_smul (w : (Fin 2 → ℤ) → ℂ) (A : SL(2, ℤ)) (z : ℍ) :
    Lsum9 w (A • z) = denom A z ^ 9 *
      Lsum9 (fun v => w (v ᵥ* ((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))) z := by
  simp only [Lsum9, eisSummand_SL2_apply]
  rw [← tsum_mul_left]
  rw [← (vmEquiv A).tsum_eq (fun u => denom A z ^ 9 *
    (w (u ᵥ* ((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) * eisSummand 9 u z))]
  refine tsum_congr fun v => ?_
  simp only [SixSquares.vmEquiv, Equiv.coe_fn_mk]
  rw [vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, vecMul_one]
  have : (denom A z) ^ (9 : ℤ) = (denom A z) ^ (9 : ℕ) := by norm_cast
  rw [this]; ring

lemma mdiff_Lsum9 {w : (Fin 2 → ℤ) → ℂ} {B : ℝ} (hw : ∀ v, ‖w v‖ ≤ B) : MDiff (Lsum9 w) := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hw 0)
  set F : (Fin 2 → ℤ) → ℂ → ℂ := fun v z => w v * (eisSummand 9 v ∘ ofComplex) z with hF
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
        (u := fun v => B * (r ⟨⟨A, B'⟩, hB'⟩ ^ (-(9 : ℝ)) * ‖v‖ ^ (-(9 : ℝ))))
        (((summable_one_div_norm_rpow (k := 9) (by norm_num)).mul_left _).mul_left B)
        (fun v => ((eisSummand_extension_differentiableOn 9 v).const_mul (w v)).mono hVU) hV ?_
      intro v z hz
      have hzU : 0 < z.im := hVU hz
      have hmem : ofComplex z ∈ verticalStrip A B' := by
        rw [ofComplex_apply_of_im_pos hzU]
        exact ⟨hz.1.le, hz.2.le⟩
      simp only [hF, Function.comp_apply, norm_mul]
      refine mul_le_mul (hw v) ?_ (norm_nonneg _) hB
      simp only [eisSummand, norm_zpow]
      have := summand_bound_of_mem_verticalStrip (k := 9) (by norm_num) v hB' hmem
      exact_mod_cast this
    exact (hd.differentiableAt (hV.mem_nhds hzV)).differentiableWithinAt
  refine mdiff_of_eqOn hdiff fun τ => ?_
  simp only [Lsum9, hF, Function.comp_apply, ofComplex_apply]

/-! ### The weight `W` -/

/-- `W(m, n) = [m even] χ(n) + i [n even] χ(m)`. -/
def W (v : Fin 2 → ℤ) : ℂ :=
  (if Even (v 0) then chiZ (v 1) else 0) + I * (if Even (v 1) then chiZ (v 0) else 0)

lemma norm_W_le (v : Fin 2 → ℤ) : ‖W v‖ ≤ 2 := by
  unfold W
  calc _ ≤ ‖(if Even (v 0) then chiZ (v 1) else 0)‖ + ‖I * (if Even (v 1) then chiZ (v 0) else 0)‖ :=
        norm_add_le _ _
    _ ≤ 1 + 1 := by
        gcongr
        · exact norm_ite_chiZ_le _ _
        · rw [norm_mul, Complex.norm_I, one_mul]; exact norm_ite_chiZ_le _ _
    _ = 2 := by norm_num

lemma W_S (v : Fin 2 → ℤ) :
    W (v ᵥ* ((S⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) = -I * W v := by
  rw [vecMul_SL_inv]
  simp only [S, Matrix.SpecialLinearGroup.coe_mk, of_apply, cons_val', cons_val_zero, cons_val_one,
    empty_val', cons_val_fin_one, head_cons, head_fin_const]
  simp only [W, cons_val_zero, cons_val_one, head_cons]
  have e1 : v 0 * 0 - v 1 * 1 = -v 1 := by ring
  have e2 : -(v 0 * -1) + v 1 * 0 = v 0 := by ring
  simp only [e1, e2, even_neg, chiZ_neg]
  have hI : I * I = -1 := I_mul_I
  split_ifs <;> first | ring1 | linear_combination (chiZ (v 0)) * hI

lemma Lsum9_W_S (z : ℍ) : Lsum9 W (S • z) = -I * (z : ℂ) ^ 9 * Lsum9 W z := by
  rw [Lsum9_smul, denom_S]
  simp_rw [W_S]
  rw [Lsum9, Lsum9]
  simp_rw [mul_assoc (-I)]
  rw [tsum_mul_left]
  ring

lemma W_T2 (v : Fin 2 → ℤ) :
    W (v ᵥ* (((T ^ (2 : ℤ))⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) = W v := by
  rw [vecMul_SL_inv]
  simp only [coe_T_zpow, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one, head_cons]
  simp only [W, cons_val_zero, cons_val_one, head_cons]
  have e1 : v 0 * 1 - v 1 * 0 = v 0 := by ring
  have hev : Even (-(v 0 * 2) + v 1 * 1) ↔ Even (v 1) := by
    rw [show -(v 0 * 2) + v 1 * 1 = v 1 + 2 * (-(v 0)) by ring]
    exact Int.even_add.trans (by simp [Int.even_mul])
  simp only [e1, hev]
  by_cases h0 : Even (v 0)
  · simp only [if_pos h0]
    obtain ⟨j, hj⟩ := h0
    rw [show -(v 0 * 2) + v 1 * 1 = v 1 + 4 * (-j) by rw [hj]; ring, chiZ_add_four_mul]
  · simp only [if_neg h0]

lemma Lsum9_W_T2 (z : ℍ) : Lsum9 W (T ^ (2 : ℤ) • z) = Lsum9 W z := by
  rw [Lsum9_smul]
  simp_rw [W_T2]
  have : denom (T ^ (2 : ℤ) : SL(2, ℤ)) z = 1 := by
    rw [ModularGroup.denom_apply, coe_T_zpow]; simp
  rw [this, one_pow, one_mul]

/-- `W' = W ∘ (TS)⁻¹`. -/
def Wp (v : Fin 2 → ℤ) : ℂ := W (v ᵥ* (((T * S)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))

lemma Lsum9_W_TS (z : ℍ) : Lsum9 W ((T * S) • z) = (z : ℂ) ^ 9 * Lsum9 Wp z := by
  rw [Lsum9_smul, denom_TS]; rfl

lemma norm_Wp_le (v : Fin 2 → ℤ) : ‖Wp v‖ ≤ 2 := norm_W_le _

lemma Wp_eq_zero_of_even (v : Fin 2 → ℤ) (h : Even (v 0)) : Wp v = 0 := by
  unfold Wp
  rw [vecMul_SL_inv, coe_TS]
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
    head_cons]
  simp only [W, cons_val_zero, cons_val_one, head_cons]
  have e1 : v 0 * 0 - v 1 * 1 = -v 1 := by ring
  have e2 : -(v 0 * -1) + v 1 * 1 = v 0 + v 1 := by ring
  simp only [e1, e2, even_neg]
  by_cases h1 : Even (v 1)
  · rw [if_pos h1, if_pos (h.add h1), chiZ_of_even (h.add h1), chiZ_of_even (even_neg.mpr h1)]
    ring
  · have h01 : ¬ Even (v 0 + v 1) := fun h' => h1 (by simpa using (Int.even_add.mp h').mp h)
    rw [if_neg h1, if_neg h01]; ring

end NTKB.HardyWright.EighteenSquares
