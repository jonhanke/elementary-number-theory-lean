/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.FourteenSeriesBounds
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TwelveBounds

/-!
# `θ¹⁴` and `θ²`: transformation laws and bounds

`θ(-1/τ)¹⁴ = i τ⁷ θ(τ)¹⁴`, `θ(TSτ)¹⁴ = τ⁷ thetaTS14 τ` with `thetaTS14` bounded on `Im τ ≥ 1`, and
`‖θ¹⁴ - 1 - 28 q‖ ≤ C e^{-2π Im τ}` (the weight-`7` analogue of the `θ¹⁰` part of `TenBounds.lean`);
the same for `θ²` (`theta2_S`, `theta2_TS`, `norm_theta2_sub_one_le`).
-/

open ModularForm ModularGroup Complex Filter Topology EisensteinSeries Matrix
open scoped MatrixGroups Real UpperHalfPlane Manifold
open UpperHalfPlane hiding I

noncomputable section

namespace NTKB.HardyWright.FourteenSquares

open EightSquares (K1 ne_zero' norm_jacobiTheta_sub_one_le' norm_jacobiTheta_sub_le mdiff_of_eqOn
  theta_T_sq coe_TS_smul jacobiTheta_one_add norm_jacobiTheta₂_half_le)
open SixSquares (exp_neg_pi_im_le_quarter norm_q norm_cexp_le_one_of_re one_div_neg_I_div)
open TwelveSquares (norm_one_add_pow_sub_le norm_sub_of_hasSum)

/-! ### `θ¹⁴` -/

lemma I_pow_seven : I ^ 7 = -I := by
  rw [show (7 : ℕ) = 4 + 3 by rfl, pow_add, I_pow_four, one_mul, pow_succ, I_sq]; ring

lemma cpow_half_pow_14 (z : ℂ) : (z ^ (1 / 2 : ℂ)) ^ 14 = z ^ 7 := by
  have h := cpow_ofNat_inv_pow z 2
  rw [one_div, show (14 : ℕ) = 2 * 7 from rfl, pow_mul, h]

lemma theta14_S (τ : ℍ) : jacobiTheta ↑(S • τ) ^ 14 = I * (τ : ℂ) ^ 7 * jacobiTheta τ ^ 14 := by
  rw [jacobiTheta_S_smul, mul_pow, cpow_half_pow_14]
  have : (-I * (τ : ℂ)) ^ 7 = I * (τ : ℂ) ^ 7 := by
    rw [mul_pow, neg_pow, I_pow_seven]; ring
  rw [this]

/-- The factor of `θ((τ-1)/τ)¹⁴`. -/
def thetaTS14 (τ : ℍ) : ℂ := I * (cexp (7 * π * I * τ / 2) * jacobiTheta₂ (-(τ : ℂ) / 2) τ ^ 14)

lemma theta14_TS (τ : ℍ) : jacobiTheta (((T * S) • τ : ℍ) : ℂ) ^ 14 = (τ : ℂ) ^ 7 * thetaTS14 τ := by
  have h0 := ne_zero' τ
  rw [coe_TS_smul, show ((τ : ℂ) - 1) / τ = 1 + (-1 / τ) by field_simp; ring, jacobiTheta_one_add,
    jacobiTheta₂_functional_equation]
  have e1' : -I * (-1 / (τ : ℂ)) = I / τ := by field_simp
  have e2 : -π * I * (1 / 2 : ℂ) ^ 2 / (-1 / (τ : ℂ)) = π * I * τ / 4 := by field_simp; ring
  have e3 : (1 / 2 : ℂ) / (-1 / (τ : ℂ)) = -(τ : ℂ) / 2 := by field_simp
  have e4 : -1 / (-1 / (τ : ℂ)) = τ := by field_simp
  rw [e1', e2, e3, e4, mul_pow, mul_pow, div_pow, cpow_half_pow_14, one_pow,
    ← Complex.exp_nat_mul]
  have hI : (I / (τ : ℂ)) ^ 7 = -I / (τ : ℂ) ^ 7 := by
    rw [div_pow, I_pow_seven]
  rw [hI, thetaTS14]
  have : ((14 : ℕ) : ℂ) * (π * I * τ / 4) = 7 * π * I * τ / 2 := by push_cast; ring
  rw [this]
  field_simp
  rw [show I ^ 2 = -1 from I_sq]
  ring

lemma norm_thetaTS14_le (τ : ℍ) (hτ : 1 ≤ τ.im) : ‖thetaTS14 τ‖ ≤ K1 ^ 14 := by
  have hJ := norm_jacobiTheta₂_half_le τ hτ
  have he : ‖cexp (7 * π * I * τ / 2)‖ ≤ 1 := by
    apply norm_cexp_le_one_of_re
    have : (7 * π * I * (τ : ℂ) / 2).re = -(7 * π * τ.im / 2) := by
      simp [Complex.mul_re, Complex.mul_im]; ring
    rw [this]; have := τ.im_pos; nlinarith [Real.pi_pos]
  rw [thetaTS14, norm_mul, Complex.norm_I, one_mul, norm_mul, norm_pow]
  calc ‖cexp (7 * π * I * τ / 2)‖ * ‖jacobiTheta₂ (-(τ : ℂ) / 2) τ‖ ^ 14 ≤ 1 * K1 ^ 14 := by
        gcongr
    _ = K1 ^ 14 := one_mul _

/-- `‖θ(τ)¹⁰ - 1 - 28 e^{πiτ}‖ ≤ Cθ e^{-2π Im τ}` for `Im τ ≥ 1`. -/
lemma norm_theta14_sub_le {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖jacobiTheta τ ^ 14 - 1 - 28 * cexp (π * I * τ)‖ ≤ (14 * 2 ^ 14 * 16 + 56) * rexp (-2 * π * τ.im) := by
  set w := jacobiTheta τ - 1 with hw
  have h1 := norm_jacobiTheta_sub_one_le' hτ
  have h4 := norm_jacobiTheta_sub_le hτ
  have hr := exp_neg_pi_im_le_quarter hτ
  have hwle : ‖w‖ ≤ 1 := by nlinarith [Real.exp_pos (-π * τ.im)]
  have hT := norm_one_add_pow_sub_le hwle 14
  rw [show 1 + w = jacobiTheta τ by rw [hw]; ring] at hT
  have e : jacobiTheta τ ^ 14 - 1 - 28 * cexp (π * I * τ) =
      (jacobiTheta τ ^ 14 - 1 - ((14 : ℕ) : ℂ) * w) +
        14 * (jacobiTheta τ - 1 - 2 * cexp (π * I * τ)) := by
    rw [hw]; push_cast; ring
  rw [e]
  have hsq : ‖w‖ ^ 2 ≤ 16 * rexp (-2 * π * τ.im) := by
    have : rexp (-2 * π * τ.im) = rexp (-π * τ.im) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [this]
    nlinarith [norm_nonneg w]
  have h44 : rexp (-4 * π * τ.im) ≤ rexp (-2 * π * τ.im) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  calc _ ≤ ‖jacobiTheta τ ^ 14 - 1 - ((14 : ℕ) : ℂ) * w‖ +
        ‖14 * (jacobiTheta τ - 1 - 2 * cexp (π * I * τ))‖ := norm_add_le _ _
    _ ≤ (14 : ℕ) * 2 ^ 14 * (16 * rexp (-2 * π * τ.im)) + 14 * (4 * rexp (-2 * π * τ.im)) := by
        rw [norm_mul, Complex.norm_ofNat]
        gcongr
        · exact hT.trans (by gcongr)
        · exact h4.trans (by gcongr)
    _ = (14 * 2 ^ 14 * 16 + 56) * rexp (-2 * π * τ.im) := by push_cast; ring

/-! ### `θ²` -/

lemma cpow_half_pow_two (z : ℂ) : (z ^ (1 / 2 : ℂ)) ^ 2 = z := by
  have h := cpow_ofNat_inv_pow z 2
  rwa [one_div]

lemma theta2_S (τ : ℍ) : jacobiTheta ↑(S • τ) ^ 2 = -I * (τ : ℂ) * jacobiTheta τ ^ 2 := by
  rw [jacobiTheta_S_smul, mul_pow, cpow_half_pow_two]

/-- The factor of `θ((τ-1)/τ)²`. -/
def thetaTS2 (τ : ℍ) : ℂ := -I * (cexp (π * I * τ / 2) * jacobiTheta₂ (-(τ : ℂ) / 2) τ ^ 2)

lemma theta2_TS (τ : ℍ) : jacobiTheta (((T * S) • τ : ℍ) : ℂ) ^ 2 = (τ : ℂ) * thetaTS2 τ := by
  have h0 := ne_zero' τ
  rw [coe_TS_smul, show ((τ : ℂ) - 1) / τ = 1 + (-1 / τ) by field_simp; ring, jacobiTheta_one_add,
    jacobiTheta₂_functional_equation]
  have e1' : -I * (-1 / (τ : ℂ)) = I / τ := by field_simp
  have e2 : -π * I * (1 / 2 : ℂ) ^ 2 / (-1 / (τ : ℂ)) = π * I * τ / 4 := by field_simp; ring
  have e3 : (1 / 2 : ℂ) / (-1 / (τ : ℂ)) = -(τ : ℂ) / 2 := by field_simp
  have e4 : -1 / (-1 / (τ : ℂ)) = τ := by field_simp
  rw [e1', e2, e3, e4, mul_pow, mul_pow, div_pow, cpow_half_pow_two, ← Complex.exp_nat_mul]
  rw [thetaTS2]
  have : ((2 : ℕ) : ℂ) * (π * I * τ / 4) = π * I * τ / 2 := by push_cast; ring
  rw [this]
  field_simp
  rw [show I ^ 2 = -1 from I_sq]
  ring

lemma norm_thetaTS2_le (τ : ℍ) (hτ : 1 ≤ τ.im) : ‖thetaTS2 τ‖ ≤ K1 ^ 2 := by
  have hJ := norm_jacobiTheta₂_half_le τ hτ
  have he : ‖cexp (π * I * τ / 2)‖ ≤ 1 := by
    apply norm_cexp_le_one_of_re
    have : (π * I * (τ : ℂ) / 2).re = -(π * τ.im / 2) := by
      simp [Complex.mul_re, Complex.mul_im]; ring
    rw [this]; have := τ.im_pos; nlinarith [Real.pi_pos]
  rw [thetaTS2, norm_mul, norm_neg, Complex.norm_I, one_mul, norm_mul, norm_pow]
  calc ‖cexp (π * I * τ / 2)‖ * ‖jacobiTheta₂ (-(τ : ℂ) / 2) τ‖ ^ 2 ≤ 1 * K1 ^ 2 := by
        gcongr
    _ = K1 ^ 2 := one_mul _

/-- `‖θ(τ)² - 1‖ ≤ 12 e^{-π Im τ}` for `Im τ ≥ 1`. -/
lemma norm_theta2_sub_one_le {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖jacobiTheta τ ^ 2 - 1‖ ≤ 12 * rexp (-π * τ.im) := by
  have h1 := norm_jacobiTheta_sub_one_le' hτ
  have hr := exp_neg_pi_im_le_quarter hτ
  set w := jacobiTheta τ - 1 with hw
  have hwle : ‖w‖ ≤ 1 := by nlinarith [Real.exp_pos (-π * τ.im)]
  have e : jacobiTheta τ ^ 2 - 1 = w * (w + 2) := by rw [hw]; ring
  rw [e, norm_mul]
  have h2 : ‖w + 2‖ ≤ 3 := (norm_add_le _ _).trans (by simp; linarith)
  calc ‖w‖ * ‖w + 2‖ ≤ (4 * rexp (-π * τ.im)) * 3 := by gcongr
    _ = _ := by ring

end NTKB.HardyWright.FourteenSquares
