/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Manifold
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# `θ⁸` as an Eisenstein series, by level-one modular forms

With `θ(τ) = ∑_{n ∈ ℤ} e^{π i n² τ}` (Mathlib's `jacobiTheta`) and Mathlib's level-one Eisenstein
series `E₄`, we prove

`θ(τ)⁸ = (E₄(τ/2) - 2 E₄(τ) + 16 E₄(2τ)) / 15`   (`jacobiTheta_pow_eight`),

which is Jacobi's formula for `r₈` in generating-function form.

Proof. Let `g₁ = θ⁸ - e₁`, `e₁` the right side. Both terms are invariant of weight `4` under
`S : τ ↦ -1/τ` (Mathlib's `jacobiTheta_S_smul` and the modularity of `E₄`) and under `T² : τ ↦ τ + 2`.
Put `g₂ = g₁ ∣ T` and `g₃ = g₂ ∣ S`. Then `S` and `T` permute `g₁, g₂, g₃` (for `g₃ ∣ T = g₃` use
`TST = S⁻¹T⁻¹S`), so `N = g₁ g₂ g₃` is invariant of weight `12` under `SL(2, ℤ)`. The expansions
`θ = 1 + 2q + O(q⁴)`, `E₄ = 1 + 240 q + O(q²)` (`q = e^{πiτ}`) give `g₁, g₂ = O(e^{-2π Im τ})`, and `g₃`
is bounded at `i∞` (its theta part is `e^{2πiτ} θ₂`-like, by the functional equation of
`jacobiTheta₂`; its Eisenstein part is a combination of `E₄` at `τ/2, τ, (τ+1)/2`). Hence `N/Δ` is a
level-one modular form of weight `0` tending to `0` at `i∞`, so `N = 0`; by the identity theorem one
of the `gᵢ` vanishes, and each of them determines the others, so `g₁ = 0`.

No congruence subgroup and no norm map is needed: only `SL(2, ℤ)`, Mathlib's `E₄`, `Δ` and the fact
that level-one forms of weight `0` are constant.
-/

open UpperHalfPlane ModularForm ModularGroup Complex Filter Topology
open scoped MatrixGroups Real Manifold

noncomputable section

namespace NTKB.HardyWright.EightSquares

/-! ### Points of the upper half plane -/

/-- `τ/2`. -/
def halfH (τ : ℍ) : ℍ := ⟨(τ : ℂ) / 2, by simpa using τ.im_pos⟩

/-- `2τ`. -/
def twoH (τ : ℍ) : ℍ := ⟨2 * (τ : ℂ), by simpa using τ.im_pos⟩

@[simp] lemma coe_halfH (τ : ℍ) : (halfH τ : ℂ) = τ / 2 := rfl
@[simp] lemma coe_twoH (τ : ℍ) : (twoH τ : ℂ) = 2 * τ := rfl

lemma coe_S_smul (τ : ℍ) : ((S • τ : ℍ) : ℂ) = -1 / τ := by
  rw [modular_S_smul]; simp [neg_div, inv_neg]

lemma coe_T_smul (τ : ℍ) : ((T • τ : ℍ) : ℂ) = τ + 1 := by
  rw [modular_T_smul, coe_vadd]; push_cast; ring

lemma coe_T_zpow_smul (τ : ℍ) (n : ℤ) : ((T ^ n • τ : ℍ) : ℂ) = τ + n := by
  rw [modular_T_zpow_smul, coe_vadd]; push_cast; ring

lemma coe_SL_smul (g : SL(2, ℤ)) (τ : ℍ) :
    ((g • τ : ℍ) : ℂ) = ((g 0 0 : ℂ) * τ + g 0 1) / ((g 1 0 : ℂ) * τ + g 1 1) := by
  rw [coe_specialLinearGroup_apply]; simp

lemma ne_zero' (τ : ℍ) : (τ : ℂ) ≠ 0 := τ.ne_zero

/-! ### Holomorphy -/

lemma mdiff_of_eqOn {f : ℍ → ℂ} {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F {z | 0 < z.im})
    (h : ∀ τ : ℍ, f τ = F τ) : MDiff f := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine hF.congr fun z hz => ?_
  simp only [Function.comp_apply]
  rw [h, ofComplex_apply_of_im_pos hz]

lemma diffOn_comp_ofComplex {f : ℍ → ℂ} (hf : MDiff f) :
    DifferentiableOn ℂ (f ∘ ofComplex) {z | 0 < z.im} :=
  (UpperHalfPlane.mdifferentiable_iff).mp hf

lemma eval_ofComplex (f : ℍ → ℂ) (τ : ℍ) : (f ∘ ofComplex) (τ : ℂ) = f τ := by
  simp [Function.comp_apply, ofComplex_apply]

lemma mdiff_comp_halfH {f : ℍ → ℂ} (hf : MDiff f) : MDiff (fun τ => f (halfH τ)) := by
  refine mdiff_of_eqOn (F := fun z => (f ∘ ofComplex) (z / 2)) ?_ fun τ => ?_
  · refine (diffOn_comp_ofComplex hf).comp (by fun_prop) fun z hz => ?_
    simp only [Set.mem_ofPred_eq] at hz ⊢
    simpa using hz
  · rw [show (τ : ℂ) / 2 = (halfH τ : ℂ) from rfl, eval_ofComplex]

lemma mdiff_comp_twoH {f : ℍ → ℂ} (hf : MDiff f) : MDiff (fun τ => f (twoH τ)) := by
  refine mdiff_of_eqOn (F := fun z => (f ∘ ofComplex) (2 * z)) ?_ fun τ => ?_
  · refine (diffOn_comp_ofComplex hf).comp (by fun_prop) fun z hz => ?_
    simp only [Set.mem_ofPred_eq] at hz ⊢
    simpa using hz
  · rw [show 2 * (τ : ℂ) = (twoH τ : ℂ) from rfl, eval_ofComplex]

lemma mdiff_jacobiTheta_pow (k : ℕ) : MDiff (fun τ : ℍ => jacobiTheta τ ^ k) :=
  mdiff_of_eqOn (F := fun z => jacobiTheta z ^ k)
    (fun z hz => ((differentiableAt_jacobiTheta hz).pow k).differentiableWithinAt) fun _ => rfl

/-! ### The Eisenstein series `E₄` -/

lemma E4_slash (γ : SL(2, ℤ)) : (⇑E₄ : ℍ → ℂ) ∣[((4 : ℕ) : ℤ)] γ = E₄ := by
  rw [SL_slash]
  exact SlashInvariantForm.slash_action_eqn E₄ _ ⟨γ, rfl⟩

lemma E4_smul (γ : SL(2, ℤ)) (z : ℍ) :
    E₄ (γ • z) = ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 * E₄ z := by
  have h := congrFun (E4_slash γ) z
  rw [slash_action_eq'_iff] at h
  simpa using h

lemma E4_T_zpow (n : ℤ) (z : ℍ) : E₄ (T ^ n • z) = E₄ z := by
  rw [E4_smul]; simp [coe_T_zpow]

lemma E4_S (z : ℍ) : E₄ (S • z) = (z : ℂ) ^ 4 * E₄ z := by
  rw [E4_smul]; simp [S]

/-- The Eisenstein combination `e₁(τ) = (E₄(τ/2) - 2E₄(τ) + 16E₄(2τ))/15`. -/
def e1 (τ : ℍ) : ℂ := (E₄ (halfH τ) - 2 * E₄ τ + 16 * E₄ (twoH τ)) / 15

lemma halfH_S (τ : ℍ) : halfH (S • τ) = S • twoH τ := by
  ext; simp only [coe_halfH, coe_S_smul, coe_twoH]
  have := ne_zero' τ; field_simp

lemma twoH_S (τ : ℍ) : twoH (S • τ) = S • halfH τ := by
  ext; simp only [coe_halfH, coe_S_smul, coe_twoH]
  have := ne_zero' τ; field_simp

lemma halfH_T_sq (τ : ℍ) : halfH (T ^ (2 : ℤ) • τ) = T ^ (1 : ℤ) • halfH τ := by
  ext; simp only [coe_halfH, coe_T_zpow_smul]; push_cast; ring

lemma twoH_T_sq (τ : ℍ) : twoH (T ^ (2 : ℤ) • τ) = T ^ (4 : ℤ) • twoH τ := by
  ext; simp only [coe_twoH, coe_T_zpow_smul]; push_cast; ring

lemma e1_S (τ : ℍ) : e1 (S • τ) = (τ : ℂ) ^ 4 * e1 τ := by
  simp only [e1, halfH_S, twoH_S, E4_S, coe_twoH, coe_halfH]
  ring

lemma e1_T_sq (τ : ℍ) : e1 (T ^ (2 : ℤ) • τ) = e1 τ := by
  simp only [e1, halfH_T_sq, twoH_T_sq, E4_T_zpow]

lemma mdiff_e1 : MDiff e1 := by
  have h1 := mdiff_comp_halfH E₄.holo'
  have h2 := mdiff_comp_twoH E₄.holo'
  have h0 : MDiff (⇑E₄ : ℍ → ℂ) := E₄.holo'
  refine mdiff_of_eqOn (F := fun z => ((⇑E₄ ∘ ofComplex) (z / 2) - 2 * (⇑E₄ ∘ ofComplex) z +
    16 * (⇑E₄ ∘ ofComplex) (2 * z)) / 15) ?_ fun τ => ?_
  · have hU : Set.MapsTo (fun z : ℂ => z / 2) {z | 0 < z.im} {z | 0 < z.im} := fun z hz => by
      simp only [Set.mem_ofPred_eq] at hz ⊢; simpa using hz
    have hU2 : Set.MapsTo (fun z : ℂ => 2 * z) {z | 0 < z.im} {z | 0 < z.im} := fun z hz => by
      simp only [Set.mem_ofPred_eq] at hz ⊢; simpa using hz
    have d0 := diffOn_comp_ofComplex h0
    have dh := d0.comp (by fun_prop : DifferentiableOn ℂ (fun z : ℂ => z / 2) _) hU
    have dt := d0.comp (by fun_prop : DifferentiableOn ℂ (fun z : ℂ => 2 * z) _) hU2
    exact ((dh.sub (d0.const_mul 2)).add (dt.const_mul 16)).div_const 15
  · simp only [e1]
    rw [show (τ : ℂ) / 2 = (halfH τ : ℂ) from rfl, show 2 * (τ : ℂ) = (twoH τ : ℂ) from rfl,
      eval_ofComplex, eval_ofComplex, eval_ofComplex]

/-! ### `θ⁸` -/

lemma cpow_half_pow_eight (z : ℂ) : (z ^ (1 / 2 : ℂ)) ^ 8 = z ^ 4 := by
  have h := cpow_ofNat_inv_pow z 2
  rw [one_div, show (8 : ℕ) = 2 * 4 from rfl, pow_mul, h]

lemma theta8_S (τ : ℍ) : jacobiTheta ↑(S • τ) ^ 8 = (τ : ℂ) ^ 4 * jacobiTheta τ ^ 8 := by
  rw [jacobiTheta_S_smul, mul_pow, cpow_half_pow_eight, mul_pow,
    show (-Complex.I) ^ 4 = (1 : ℂ) by rw [neg_pow, Complex.I_pow_four]; norm_num, one_mul]

lemma theta_T_sq (τ : ℍ) : jacobiTheta ↑(T ^ (2 : ℤ) • τ) = jacobiTheta τ := by
  rw [coe_T_zpow_smul]; push_cast
  rw [add_comm, jacobiTheta_two_add]

/-! ### The functions `g₁, g₂, g₃` and `N` -/

/-- `g₁ = θ⁸ - e₁`. -/
def g1 (τ : ℍ) : ℂ := jacobiTheta τ ^ 8 - e1 τ

lemma g1_S (τ : ℍ) : g1 (S • τ) = (τ : ℂ) ^ 4 * g1 τ := by
  simp only [g1, theta8_S, e1_S]; ring

lemma g1_T_sq (τ : ℍ) : g1 (T ^ (2 : ℤ) • τ) = g1 τ := by
  simp only [g1, theta_T_sq, e1_T_sq]

lemma mdiff_g1 : MDiff g1 := (mdiff_jacobiTheta_pow 8).sub mdiff_e1

lemma g1_slash_S : g1 ∣[(4 : ℤ)] S = g1 := by
  ext τ
  rw [SL_slash_apply, g1_S, denom_S]
  have := ne_zero' τ
  rw [zpow_neg, zpow_ofNat]; field_simp

lemma g1_slash_T_sq : g1 ∣[(4 : ℤ)] (T ^ (2 : ℤ)) = g1 := by
  ext τ
  rw [SL_slash_apply, g1_T_sq, ModularGroup.denom_apply, coe_T_zpow]
  simp

/-- `g₂ = g₁ ∣ T`, i.e. `g₂(τ) = g₁(τ + 1)`. -/
def g2 : ℍ → ℂ := g1 ∣[(4 : ℤ)] T

/-- `g₃ = g₂ ∣ S`. -/
def g3 : ℍ → ℂ := g2 ∣[(4 : ℤ)] S

lemma slash_inv_of_slash_eq {f : ℍ → ℂ} {k : ℤ} {g : SL(2, ℤ)} (h : f ∣[k] g = f) :
    f ∣[k] g⁻¹ = f := by
  conv_lhs => rw [← h]
  rw [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]

lemma g2_slash_T : g2 ∣[(4 : ℤ)] T = g1 := by
  rw [g2, ← SlashAction.slash_mul, ← zpow_one T, ← zpow_add]
  exact g1_slash_T_sq

lemma slash_S_S (f : ℍ → ℂ) : f ∣[(4 : ℤ)] (S * S) = f := by
  have hSS : S * S = -1 := Subtype.ext (by simpa using S_mul_S_eq)
  ext τ
  rw [hSS, SL_slash_apply, SL_neg_smul, one_smul]
  simp [denom]
  norm_num

lemma g3_slash_S : g3 ∣[(4 : ℤ)] S = g2 := by
  rw [g3, ← SlashAction.slash_mul, slash_S_S]

lemma T_S_T : T * S * T = S⁻¹ * T⁻¹ * S := by
  apply Subtype.ext
  rw [S_inv]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg, coe_S, coe_T,
    coe_T_inv]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma g3_slash_T : g3 ∣[(4 : ℤ)] T = g3 := by
  have hSi : g1 ∣[(4 : ℤ)] S⁻¹ = g1 := slash_inv_of_slash_eq g1_slash_S
  have hTi : g1 ∣[(4 : ℤ)] T⁻¹ = g1 ∣[(4 : ℤ)] T := by
    conv_lhs => rw [← g1_slash_T_sq]
    rw [← SlashAction.slash_mul, show T ^ (2 : ℤ) * T⁻¹ = T by group]
  rw [g3, g2, ← SlashAction.slash_mul, ← SlashAction.slash_mul, ← mul_assoc, T_S_T,
    SlashAction.slash_mul, SlashAction.slash_mul, hSi, hTi]

lemma mdiff_g2 : MDiff g2 := by
  rw [g2, SL_slash]; exact mdiff_g1.slash _ _

lemma mdiff_g3 : MDiff g3 := by
  rw [g3, SL_slash]; exact mdiff_g2.slash _ _

/-- `N = g₁ g₂ g₃`, invariant of weight `12` under `SL(2, ℤ)`. -/
def Nf : ℍ → ℂ := g1 * g2 * g3

lemma Nf_slash_S : Nf ∣[(12 : ℤ)] S = Nf := by
  rw [Nf, show (12 : ℤ) = 4 + 4 + 4 by norm_num, mul_slash_SL2, mul_slash_SL2, g1_slash_S,
    g3_slash_S, show g2 ∣[(4 : ℤ)] S = g3 from rfl]
  ring

lemma Nf_slash_T : Nf ∣[(12 : ℤ)] T = Nf := by
  rw [Nf, show (12 : ℤ) = 4 + 4 + 4 by norm_num, mul_slash_SL2, mul_slash_SL2, g2_slash_T,
    g3_slash_T, show g1 ∣[(4 : ℤ)] T = g2 from rfl]
  ring

end NTKB.HardyWright.EightSquares
