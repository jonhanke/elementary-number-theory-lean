/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.SixVanish

/-!
# Weighted lattice sums of weight `3`

For `w : ℤ² → ℂ` bounded, `L_w(τ) = ∑_{v ∈ ℤ²} w(v) (v₀ τ + v₁)⁻³` (`Lsum`; Mathlib's `eisSummand 3`).

* `Lsum_smul`: `L_w(γ τ) = (cτ + d)³ L_{w ∘ γ⁻¹}(τ)` for `γ ∈ SL(2, ℤ)` (reindexing `v ↦ v γ`);
* `mdiff_Lsum`: `L_w` is holomorphic (uniform bounds on vertical strips, as for Mathlib's
  Eisenstein series);
* the weight `W(m, n) = [m even] χ(n) - i [n even] χ(m)`, `χ` the non-principal character modulo
  `4`, satisfies `L_W(-1/τ) = i τ³ L_W(τ)` (`Lsum_W_S`) and `L_W(τ + 2) = L_W(τ)` (`Lsum_W_T2`),
  the transformation laws of `θ(τ)⁶`; and `L_W(TS τ) = τ³ L_{W'}(τ)` with `W'` vanishing on
  `v₀` even (`Wp_eq_zero_of_even`).
-/

open ModularForm ModularGroup Complex Filter Topology EisensteinSeries Matrix
open scoped MatrixGroups Real UpperHalfPlane Manifold
open UpperHalfPlane hiding I

noncomputable section

namespace NTKB.HardyWright.SixSquares

open EightSquares (mdiff_of_eqOn coe_TS denom_TS)

/-! ### The character modulo `4` on integers -/

/-- `χ(n)`, the non-principal character modulo `4`, for `n ∈ ℤ`. -/
def chiZ (n : ℤ) : ℂ := ((ZMod.χ₄ (n : ZMod 4) : ℤ) : ℂ)

lemma chiZ_eq (n : ℤ) : chiZ n = if n % 2 = 0 then 0 else if n % 4 = 1 then 1 else -1 := by
  rw [chiZ, ZMod.χ₄_int_eq_if_mod_four]; split_ifs <;> simp

lemma chiZ_of_even {n : ℤ} (h : Even n) : chiZ n = 0 := by
  rw [chiZ_eq, if_pos (Int.even_iff.mp h)]

lemma chiZ_add_four_mul (n k : ℤ) : chiZ (n + 4 * k) = chiZ n := by
  rw [chiZ_eq, chiZ_eq]
  have h2 : (n + 4 * k) % 2 = n % 2 := by omega
  have h4 : (n + 4 * k) % 4 = n % 4 := by omega
  rw [h2, h4]

lemma chiZ_neg (n : ℤ) : chiZ (-n) = -chiZ n := by
  rw [chiZ_eq, chiZ_eq]
  split_ifs <;> (try norm_num) <;> omega

lemma norm_chiZ_le (n : ℤ) : ‖chiZ n‖ ≤ 1 := by
  rw [chiZ_eq]; split_ifs <;> simp

lemma norm_ite_chiZ_le (p : Prop) [Decidable p] (n : ℤ) : ‖(if p then chiZ n else 0)‖ ≤ 1 := by
  split_ifs
  · exact norm_chiZ_le n
  · simp

/-! ### Lattice sums -/

/-- `L_w(τ) = ∑_{v ∈ ℤ²} w(v) (v₀ τ + v₁)⁻³`.
  **Restriction:** the lattice sum converges absolutely when the weight `w` is bounded (a hypothesis not enforced by
  the type; see `summable_Lsum`); where it does not converge the value is $0$ by Lean's `tsum` convention, not the
  intended value. -/
def Lsum (w : (Fin 2 → ℤ) → ℂ) (z : ℍ) : ℂ := ∑' v, w v * eisSummand 3 v z

lemma summable_Lsum {w : (Fin 2 → ℤ) → ℂ} {B : ℝ} (hw : ∀ v, ‖w v‖ ≤ B) (z : ℍ) :
    Summable fun v => w v * eisSummand 3 v z := by
  refine Summable.of_norm_bounded
    ((summable_norm_eisSummand (k := 3) (by norm_num) z).mul_left B) fun v => ?_
  rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hw v) (norm_nonneg _)

/-- `v ↦ v A` as a bijection of `ℤ²`. -/
def vmEquiv (A : SL(2, ℤ)) : (Fin 2 → ℤ) ≃ (Fin 2 → ℤ) where
  toFun v := v ᵥ* (A : Matrix (Fin 2) (Fin 2) ℤ)
  invFun v := v ᵥ* ((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
  left_inv v := by
    simp only
    rw [vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, vecMul_one]
  right_inv v := by
    simp only
    rw [vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, vecMul_one]

/-- `L_w(A τ) = (cτ + d)³ L_{w ∘ A⁻¹}(τ)`. -/
lemma Lsum_smul (w : (Fin 2 → ℤ) → ℂ) (A : SL(2, ℤ)) (z : ℍ) :
    Lsum w (A • z) = denom A z ^ 3 *
      Lsum (fun v => w (v ᵥ* ((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))) z := by
  simp only [Lsum, eisSummand_SL2_apply]
  rw [← tsum_mul_left]
  rw [← (vmEquiv A).tsum_eq (fun u => denom A z ^ 3 *
    (w (u ᵥ* ((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) * eisSummand 3 u z))]
  refine tsum_congr fun v => ?_
  simp only [vmEquiv, Equiv.coe_fn_mk]
  rw [vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, vecMul_one]
  have : (denom A z) ^ (3 : ℤ) = (denom A z) ^ (3 : ℕ) := by norm_cast
  rw [this]; ring

lemma vecMul_SL_inv (A : SL(2, ℤ)) (v : Fin 2 → ℤ) :
    v ᵥ* ((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      ![v 0 * A 1 1 - v 1 * A 1 0, -(v 0 * A 0 1) + v 1 * A 0 0] := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i; fin_cases i <;> simp [vecMul, dotProduct, Fin.sum_univ_two] <;> ring

/-! ### Holomorphy -/

lemma isOpen_strip (A B : ℝ) : IsOpen {z : ℂ | |z.re| < A ∧ B < z.im} :=
  (isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const).inter
    (isOpen_lt continuous_const Complex.continuous_im)

lemma mdiff_Lsum {w : (Fin 2 → ℤ) → ℂ} {B : ℝ} (hw : ∀ v, ‖w v‖ ≤ B) : MDiff (Lsum w) := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hw 0)
  set F : (Fin 2 → ℤ) → ℂ → ℂ := fun v z => w v * (eisSummand 3 v ∘ ofComplex) z with hF
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
        (u := fun v => B * (r ⟨⟨A, B'⟩, hB'⟩ ^ (-(3 : ℝ)) * ‖v‖ ^ (-(3 : ℝ))))
        (((summable_one_div_norm_rpow (k := 3) (by norm_num)).mul_left _).mul_left B)
        (fun v => ((eisSummand_extension_differentiableOn 3 v).const_mul (w v)).mono hVU) hV ?_
      intro v z hz
      have hzU : 0 < z.im := hVU hz
      have hmem : ofComplex z ∈ verticalStrip A B' := by
        rw [ofComplex_apply_of_im_pos hzU]
        exact ⟨hz.1.le, hz.2.le⟩
      simp only [hF, Function.comp_apply, norm_mul]
      refine mul_le_mul (hw v) ?_ (norm_nonneg _) hB
      simp only [eisSummand, norm_zpow]
      have := summand_bound_of_mem_verticalStrip (k := 3) (by norm_num) v hB' hmem
      exact_mod_cast this
    exact (hd.differentiableAt (hV.mem_nhds hzV)).differentiableWithinAt
  refine mdiff_of_eqOn hdiff fun τ => ?_
  simp only [Lsum, hF, Function.comp_apply, ofComplex_apply]

/-! ### The weight `W` -/

/-- `W(m, n) = [m even] χ(n) - i [n even] χ(m)`. -/
def W (v : Fin 2 → ℤ) : ℂ :=
  (if Even (v 0) then chiZ (v 1) else 0) - I * (if Even (v 1) then chiZ (v 0) else 0)

lemma norm_W_le (v : Fin 2 → ℤ) : ‖W v‖ ≤ 2 := by
  unfold W
  calc _ ≤ ‖(if Even (v 0) then chiZ (v 1) else 0)‖ + ‖I * (if Even (v 1) then chiZ (v 0) else 0)‖ :=
        norm_sub_le _ _
    _ ≤ 1 + 1 := by
        gcongr
        · exact norm_ite_chiZ_le _ _
        · rw [norm_mul, Complex.norm_I, one_mul]; exact norm_ite_chiZ_le _ _
    _ = 2 := by norm_num

lemma W_S (v : Fin 2 → ℤ) :
    W (v ᵥ* ((S⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) = I * W v := by
  rw [vecMul_SL_inv]
  simp only [S, Matrix.SpecialLinearGroup.coe_mk, of_apply, cons_val', cons_val_zero, cons_val_one,
    empty_val', cons_val_fin_one, head_cons, head_fin_const]
  simp only [W, cons_val_zero, cons_val_one, head_cons]
  have e1 : v 0 * 0 - v 1 * 1 = -v 1 := by ring
  have e2 : -(v 0 * -1) + v 1 * 0 = v 0 := by ring
  simp only [e1, e2, even_neg, chiZ_neg]
  have hI : I * I = -1 := I_mul_I
  split_ifs <;> first | ring1 | linear_combination (chiZ (v 0)) * hI

lemma Lsum_W_S (z : ℍ) : Lsum W (S • z) = I * (z : ℂ) ^ 3 * Lsum W z := by
  rw [Lsum_smul, denom_S]
  simp_rw [W_S]
  rw [Lsum, Lsum]
  simp_rw [mul_assoc I]
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

lemma Lsum_W_T2 (z : ℍ) : Lsum W (T ^ (2 : ℤ) • z) = Lsum W z := by
  rw [Lsum_smul]
  simp_rw [W_T2]
  have : denom (T ^ (2 : ℤ) : SL(2, ℤ)) z = 1 := by
    rw [ModularGroup.denom_apply, coe_T_zpow]; simp
  rw [this, one_pow, one_mul]

/-- `W' = W ∘ (TS)⁻¹`. -/
def Wp (v : Fin 2 → ℤ) : ℂ := W (v ᵥ* (((T * S)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))

lemma Lsum_W_TS (z : ℍ) : Lsum W ((T * S) • z) = (z : ℂ) ^ 3 * Lsum Wp z := by
  rw [Lsum_smul, denom_TS]; rfl

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

end NTKB.HardyWright.SixSquares
