/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.EighteenTheta
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.SixteenTheta
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TenBounds

/-!
# `θ²⁰`, `θ⁸` and `θ²`: transformation laws and bounds

`θ(-1/τ)²⁰ = -τ¹⁰ θ(τ)²⁰`, `θ(-1/τ)⁸ = τ⁴ θ(τ)⁸`, `θ(-1/τ)² = -iτ θ(τ)²` and the factors at the cusp
`1` (`thetaTS20`, `thetaTS8`, `thetaTS2`, bounded on `Im τ ≥ 1`). Bounds for `Im τ ≥ 1`, `q = e^{πiτ}`:
`‖θ²⁰ - 1 - 40 q - 760 q²‖ ≤ C ‖q‖³`, `‖θ⁸ - 1 - 16 q‖ ≤ C ‖q‖²`, `‖θ² - 1 - 4 q‖ ≤ C ‖q‖²` (the method
of `EighteenTheta.lean`).
-/

open ModularForm ModularGroup Complex Filter Topology EisensteinSeries Matrix
open scoped MatrixGroups Real UpperHalfPlane Manifold
open UpperHalfPlane hiding I

noncomputable section

namespace NTKB.HardyWright.TwentySquares

open EightSquares (K1 ne_zero' norm_jacobiTheta_sub_one_le' norm_jacobiTheta_sub_le mdiff_of_eqOn
  theta_T_sq coe_TS_smul jacobiTheta_one_add norm_jacobiTheta₂_half_le)
open SixSquares (exp_neg_pi_im_le_quarter norm_q norm_cexp_le_one_of_re one_div_neg_I_div)
open TwelveSquares (norm_one_add_pow_sub_le)
open SixteenSquares (cpow_half_pow_mul pow_add_le_quarter norm_one_add_pow_sub3_le)

/-! ### `θ²⁰` -/

lemma theta20_S (τ : ℍ) : jacobiTheta ↑(S • τ) ^ 20 = -((τ : ℂ) ^ 10 * jacobiTheta τ ^ 20) := by
  rw [jacobiTheta_S_smul, mul_pow, show (20 : ℕ) = 2 * 10 from rfl, cpow_half_pow_mul]
  have : (-I * (τ : ℂ)) ^ 10 = -(τ : ℂ) ^ 10 := by
    rw [mul_pow, neg_pow, show I ^ 10 = (I ^ 4) ^ 2 * I ^ 2 by ring, I_pow_four, I_sq]; ring
  rw [this]; ring

/-- The factor of `θ((τ-1)/τ)²⁰`. -/
def thetaTS20 (τ : ℍ) : ℂ := -(cexp (5 * π * I * τ) * jacobiTheta₂ (-(τ : ℂ) / 2) τ ^ 20)

lemma theta20_TS (τ : ℍ) :
    jacobiTheta (((T * S) • τ : ℍ) : ℂ) ^ 20 = (τ : ℂ) ^ 10 * thetaTS20 τ := by
  have h0 := ne_zero' τ
  rw [coe_TS_smul, show ((τ : ℂ) - 1) / τ = 1 + (-1 / τ) by field_simp; ring, jacobiTheta_one_add,
    jacobiTheta₂_functional_equation]
  have e1' : -I * (-1 / (τ : ℂ)) = I / τ := by field_simp
  have e2 : -π * I * (1 / 2 : ℂ) ^ 2 / (-1 / (τ : ℂ)) = π * I * τ / 4 := by field_simp; ring
  have e3 : (1 / 2 : ℂ) / (-1 / (τ : ℂ)) = -(τ : ℂ) / 2 := by field_simp
  have e4 : -1 / (-1 / (τ : ℂ)) = τ := by field_simp
  rw [e1', e2, e3, e4, mul_pow, mul_pow, div_pow, show (20 : ℕ) = 2 * 10 from rfl,
    cpow_half_pow_mul, one_pow, ← Complex.exp_nat_mul]
  have hI : (I / (τ : ℂ)) ^ 10 = -1 / (τ : ℂ) ^ 10 := by
    rw [div_pow, show I ^ 10 = (I ^ 4) ^ 2 * I ^ 2 by ring, I_pow_four, I_sq]; ring
  rw [hI, thetaTS20]
  have : ((2 * 10 : ℕ) : ℂ) * (π * I * τ / 4) = 5 * π * I * τ := by push_cast; ring
  rw [this]
  field_simp

lemma norm_thetaTS20_le (τ : ℍ) (hτ : 1 ≤ τ.im) : ‖thetaTS20 τ‖ ≤ K1 ^ 20 := by
  have hJ := norm_jacobiTheta₂_half_le τ hτ
  have he : ‖cexp (5 * π * I * τ)‖ ≤ 1 := by
    apply norm_cexp_le_one_of_re
    have : (5 * π * I * (τ : ℂ)).re = -(5 * π * τ.im) := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [this]; have := τ.im_pos; nlinarith [Real.pi_pos]
  rw [thetaTS20, norm_neg, norm_mul, norm_pow]
  calc ‖cexp (5 * π * I * τ)‖ * ‖jacobiTheta₂ (-(τ : ℂ) / 2) τ‖ ^ 20 ≤ 1 * K1 ^ 20 := by
        gcongr
    _ = K1 ^ 20 := one_mul _

/-! ### `θ⁸` -/

lemma theta8_S (τ : ℍ) : jacobiTheta ↑(S • τ) ^ 8 = (τ : ℂ) ^ 4 * jacobiTheta τ ^ 8 := by
  rw [jacobiTheta_S_smul, mul_pow, show (8 : ℕ) = 2 * 4 from rfl, cpow_half_pow_mul]
  have : (-I * (τ : ℂ)) ^ 4 = (τ : ℂ) ^ 4 := by
    rw [mul_pow, neg_pow, I_pow_four]; ring
  rw [this]

/-- The factor of `θ((τ-1)/τ)⁸`. -/
def thetaTS8 (τ : ℍ) : ℂ := cexp (2 * π * I * τ) * jacobiTheta₂ (-(τ : ℂ) / 2) τ ^ 8

lemma theta8_TS (τ : ℍ) :
    jacobiTheta (((T * S) • τ : ℍ) : ℂ) ^ 8 = (τ : ℂ) ^ 4 * thetaTS8 τ := by
  have h0 := ne_zero' τ
  rw [coe_TS_smul, show ((τ : ℂ) - 1) / τ = 1 + (-1 / τ) by field_simp; ring, jacobiTheta_one_add,
    jacobiTheta₂_functional_equation]
  have e1' : -I * (-1 / (τ : ℂ)) = I / τ := by field_simp
  have e2 : -π * I * (1 / 2 : ℂ) ^ 2 / (-1 / (τ : ℂ)) = π * I * τ / 4 := by field_simp; ring
  have e3 : (1 / 2 : ℂ) / (-1 / (τ : ℂ)) = -(τ : ℂ) / 2 := by field_simp
  have e4 : -1 / (-1 / (τ : ℂ)) = τ := by field_simp
  rw [e1', e2, e3, e4, mul_pow, mul_pow, div_pow, show (8 : ℕ) = 2 * 4 from rfl,
    cpow_half_pow_mul, one_pow, ← Complex.exp_nat_mul]
  have hI : (I / (τ : ℂ)) ^ 4 = 1 / (τ : ℂ) ^ 4 := by
    rw [div_pow, I_pow_four]
  rw [hI, thetaTS8]
  have : ((2 * 4 : ℕ) : ℂ) * (π * I * τ / 4) = 2 * π * I * τ := by push_cast; ring
  rw [this]
  field_simp

lemma norm_thetaTS8_le (τ : ℍ) (hτ : 1 ≤ τ.im) : ‖thetaTS8 τ‖ ≤ K1 ^ 8 := by
  have hJ := norm_jacobiTheta₂_half_le τ hτ
  have he : ‖cexp (2 * π * I * τ)‖ ≤ 1 := by
    apply norm_cexp_le_one_of_re
    have : (2 * π * I * (τ : ℂ)).re = -(2 * π * τ.im) := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [this]; have := τ.im_pos; nlinarith [Real.pi_pos]
  rw [thetaTS8, norm_mul, norm_pow]
  calc ‖cexp (2 * π * I * τ)‖ * ‖jacobiTheta₂ (-(τ : ℂ) / 2) τ‖ ^ 8 ≤ 1 * K1 ^ 8 := by
        gcongr
    _ = K1 ^ 8 := one_mul _

/-! ### `θ²` -/

lemma theta2_S (τ : ℍ) : jacobiTheta ↑(S • τ) ^ 2 = -I * (τ : ℂ) * jacobiTheta τ ^ 2 := by
  rw [jacobiTheta_S_smul, mul_pow, show (2 : ℕ) = 2 * 1 from rfl, cpow_half_pow_mul]
  have : (-I * (τ : ℂ)) ^ 1 = -I * (τ : ℂ) := by ring
  rw [this]

/-- The factor of `θ((τ-1)/τ)²`. -/
def thetaTS2 (τ : ℍ) : ℂ := -I * (cexp (π * I * τ / 2) * jacobiTheta₂ (-(τ : ℂ) / 2) τ ^ 2)

lemma theta2_TS (τ : ℍ) :
    jacobiTheta (((T * S) • τ : ℍ) : ℂ) ^ 2 = (τ : ℂ) * thetaTS2 τ := by
  have h0 := ne_zero' τ
  rw [coe_TS_smul, show ((τ : ℂ) - 1) / τ = 1 + (-1 / τ) by field_simp; ring, jacobiTheta_one_add,
    jacobiTheta₂_functional_equation]
  have e1' : -I * (-1 / (τ : ℂ)) = I / τ := by field_simp
  have e2 : -π * I * (1 / 2 : ℂ) ^ 2 / (-1 / (τ : ℂ)) = π * I * τ / 4 := by field_simp; ring
  have e3 : (1 / 2 : ℂ) / (-1 / (τ : ℂ)) = -(τ : ℂ) / 2 := by field_simp
  have e4 : -1 / (-1 / (τ : ℂ)) = τ := by field_simp
  rw [e1', e2, e3, e4, mul_pow, mul_pow, div_pow, TenSquares.cpow_half_sq, one_pow,
    ← Complex.exp_nat_mul]
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

/-! ### Bounds -/

/-- `‖θ(τ)²⁰ - 1 - 40 q - 760 q²‖ ≤ C ‖q‖³` for `Im τ ≥ 1`. -/
lemma norm_theta20_sub_le {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖jacobiTheta τ ^ 20 - 1 - 40 * cexp (π * I * τ) - 760 * cexp (π * I * τ) ^ 2‖ ≤
      (400 * 1048576 * 64 + 250) * ‖cexp (π * I * τ)‖ ^ 3 := by
  set q := cexp (π * I * τ) with hq
  set w := jacobiTheta τ - 1 with hw
  set e := w - 2 * q with he
  have hqn : ‖q‖ = rexp (-π * τ.im) := by
    rw [hq, Complex.norm_exp]; congr 1; simp [Complex.mul_re, Complex.mul_im]
  have hq4 := exp_neg_pi_im_le_quarter hτ
  have ht : ‖q‖ ≤ 1 / 4 := by rw [hqn]; exact hq4
  have h1 := norm_jacobiTheta_sub_one_le' hτ
  have h4 := norm_jacobiTheta_sub_le hτ
  have hq4' : rexp (-4 * π * τ.im) = ‖q‖ ^ 4 := by
    rw [hqn, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hwn : ‖w‖ ≤ 4 * ‖q‖ := by rw [hqn]; exact h1
  have hen : ‖e‖ ≤ 4 * ‖q‖ ^ 4 := by
    rw [← hq4']; exact h4
  have ht0 := norm_nonneg q
  have hwle : ‖w‖ ≤ 1 := by linarith
  have hT := norm_one_add_pow_sub3_le hwle 20
  rw [show 1 + w = jacobiTheta τ by rw [hw]; ring] at hT
  have eq1 : jacobiTheta τ ^ 20 - 1 - 40 * q - 760 * q ^ 2 =
      (jacobiTheta τ ^ 20 - 1 - ((20 : ℕ) : ℂ) * w - (((20 : ℕ) : ℂ) * (((20 : ℕ) : ℂ) - 1) / 2) * w ^ 2)
        + 20 * e + 760 * (q * e) + 190 * e ^ 2 := by
    rw [he, hw]; push_cast; ring
  rw [eq1]
  have hw3 : ‖w‖ ^ 3 ≤ (4 * ‖q‖) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hwn 3
  have b1 : ‖jacobiTheta τ ^ 20 - 1 - ((20 : ℕ) : ℂ) * w -
      (((20 : ℕ) : ℂ) * (((20 : ℕ) : ℂ) - 1) / 2) * w ^ 2‖ ≤ 400 * 1048576 * 64 * ‖q‖ ^ 3 := by
    refine hT.trans ?_
    push_cast
    nlinarith [pow_nonneg ht0 3]
  have b2 : ‖(20 : ℂ) * e‖ ≤ 20 * (4 * ‖q‖ ^ 4) := by
    rw [norm_mul]; simp only [Complex.norm_ofNat]; gcongr
  have b3 : ‖(760 : ℂ) * (q * e)‖ ≤ 760 * (‖q‖ * (4 * ‖q‖ ^ 4)) := by
    rw [norm_mul, norm_mul]; simp only [Complex.norm_ofNat]; gcongr
  have b4 : ‖(190 : ℂ) * e ^ 2‖ ≤ 190 * (4 * ‖q‖ ^ 4) ^ 2 := by
    rw [norm_mul, norm_pow]; simp only [Complex.norm_ofNat]
    gcongr
  have p3 : 0 ≤ ‖q‖ ^ 3 := by positivity
  have p4 : ‖q‖ ^ 4 ≤ ‖q‖ ^ 3 / 4 := by
    have := pow_add_le_quarter ht0 ht 3 1
    norm_num at this ⊢; linarith
  have p5 : ‖q‖ ^ 5 ≤ ‖q‖ ^ 3 / 16 := by
    have := pow_add_le_quarter ht0 ht 3 2
    norm_num at this ⊢; linarith
  have p8 : ‖q‖ ^ 8 ≤ ‖q‖ ^ 3 / 1024 := by
    have := pow_add_le_quarter ht0 ht 3 5
    norm_num at this ⊢; linarith
  calc _ ≤ ‖jacobiTheta τ ^ 20 - 1 - ((20 : ℕ) : ℂ) * w -
        (((20 : ℕ) : ℂ) * (((20 : ℕ) : ℂ) - 1) / 2) * w ^ 2‖ + ‖(20 : ℂ) * e‖ +
        ‖(760 : ℂ) * (q * e)‖ + ‖(190 : ℂ) * e ^ 2‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ 400 * 1048576 * 64 * ‖q‖ ^ 3 + 20 * (4 * ‖q‖ ^ 4) + 760 * (‖q‖ * (4 * ‖q‖ ^ 4)) +
        190 * (4 * ‖q‖ ^ 4) ^ 2 := by gcongr
    _ ≤ (400 * 1048576 * 64 + 250) * ‖q‖ ^ 3 := by nlinarith

/-- `‖θ(τ)⁸ - 1 - 16 q‖ ≤ 32770 ‖q‖²` for `Im τ ≥ 1`. -/
lemma norm_theta8_sub_le {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖jacobiTheta τ ^ 8 - 1 - 16 * cexp (π * I * τ)‖ ≤ 32770 * ‖cexp (π * I * τ)‖ ^ 2 := by
  set q := cexp (π * I * τ) with hq
  set w := jacobiTheta τ - 1 with hw
  set e := w - 2 * q with he
  have hqn : ‖q‖ = rexp (-π * τ.im) := by
    rw [hq, Complex.norm_exp]; congr 1; simp [Complex.mul_re, Complex.mul_im]
  have hq4 := exp_neg_pi_im_le_quarter hτ
  have ht : ‖q‖ ≤ 1 / 4 := by rw [hqn]; exact hq4
  have h1 := norm_jacobiTheta_sub_one_le' hτ
  have h4 := norm_jacobiTheta_sub_le hτ
  have hq4' : rexp (-4 * π * τ.im) = ‖q‖ ^ 4 := by
    rw [hqn, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hwn : ‖w‖ ≤ 4 * ‖q‖ := by rw [hqn]; exact h1
  have hen : ‖e‖ ≤ 4 * ‖q‖ ^ 4 := by rw [← hq4']; exact h4
  have ht0 := norm_nonneg q
  have hwle : ‖w‖ ≤ 1 := by linarith
  have hT := norm_one_add_pow_sub_le hwle 8
  rw [show 1 + w = jacobiTheta τ by rw [hw]; ring] at hT
  have eq1 : jacobiTheta τ ^ 8 - 1 - 16 * q =
      (jacobiTheta τ ^ 8 - 1 - ((8 : ℕ) : ℂ) * w) + 8 * e := by
    rw [he, hw]; push_cast; ring
  rw [eq1]
  have hw2 : ‖w‖ ^ 2 ≤ (4 * ‖q‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hwn 2
  have b2 : ‖(8 : ℂ) * e‖ ≤ 8 * (4 * ‖q‖ ^ 4) := by
    rw [norm_mul]; simp only [Complex.norm_ofNat]; gcongr
  have p2 : 0 ≤ ‖q‖ ^ 2 := by positivity
  have p4 : ‖q‖ ^ 4 ≤ ‖q‖ ^ 2 / 16 := by
    have := pow_add_le_quarter ht0 ht 2 2
    norm_num at this ⊢; linarith
  calc _ ≤ ‖jacobiTheta τ ^ 8 - 1 - ((8 : ℕ) : ℂ) * w‖ + ‖(8 : ℂ) * e‖ := norm_add_le _ _
    _ ≤ (8 : ℕ) * 2 ^ 8 * (4 * ‖q‖) ^ 2 + 8 * (4 * ‖q‖ ^ 4) := by
        gcongr
        exact hT.trans (by gcongr)
    _ ≤ 32770 * ‖q‖ ^ 2 := by push_cast; nlinarith

/-- `‖θ(τ)² - 1 - 4 q‖ ≤ 130 ‖q‖²` for `Im τ ≥ 1`. -/
lemma norm_theta2_sub_le {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖jacobiTheta τ ^ 2 - 1 - 4 * cexp (π * I * τ)‖ ≤ 130 * ‖cexp (π * I * τ)‖ ^ 2 := by
  set q := cexp (π * I * τ) with hq
  set w := jacobiTheta τ - 1 with hw
  set e := w - 2 * q with he
  have hqn : ‖q‖ = rexp (-π * τ.im) := by
    rw [hq, Complex.norm_exp]; congr 1; simp [Complex.mul_re, Complex.mul_im]
  have hq4 := exp_neg_pi_im_le_quarter hτ
  have ht : ‖q‖ ≤ 1 / 4 := by rw [hqn]; exact hq4
  have h1 := norm_jacobiTheta_sub_one_le' hτ
  have h4 := norm_jacobiTheta_sub_le hτ
  have hq4' : rexp (-4 * π * τ.im) = ‖q‖ ^ 4 := by
    rw [hqn, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hwn : ‖w‖ ≤ 4 * ‖q‖ := by rw [hqn]; exact h1
  have hen : ‖e‖ ≤ 4 * ‖q‖ ^ 4 := by rw [← hq4']; exact h4
  have ht0 := norm_nonneg q
  have hwle : ‖w‖ ≤ 1 := by linarith
  have hT := norm_one_add_pow_sub_le hwle 2
  rw [show 1 + w = jacobiTheta τ by rw [hw]; ring] at hT
  have eq1 : jacobiTheta τ ^ 2 - 1 - 4 * q =
      (jacobiTheta τ ^ 2 - 1 - ((2 : ℕ) : ℂ) * w) + 2 * e := by
    rw [he, hw]; push_cast; ring
  rw [eq1]
  have hw2 : ‖w‖ ^ 2 ≤ (4 * ‖q‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hwn 2
  have b2 : ‖(2 : ℂ) * e‖ ≤ 2 * (4 * ‖q‖ ^ 4) := by
    rw [norm_mul]; simp only [Complex.norm_ofNat]; gcongr
  have p2 : 0 ≤ ‖q‖ ^ 2 := by positivity
  have p4 : ‖q‖ ^ 4 ≤ ‖q‖ ^ 2 / 16 := by
    have := pow_add_le_quarter ht0 ht 2 2
    norm_num at this ⊢; linarith
  calc _ ≤ ‖jacobiTheta τ ^ 2 - 1 - ((2 : ℕ) : ℂ) * w‖ + ‖(2 : ℂ) * e‖ := norm_add_le _ _
    _ ≤ (2 : ℕ) * 2 ^ 2 * (4 * ‖q‖) ^ 2 + 2 * (4 * ‖q‖ ^ 4) := by
        gcongr
        exact hT.trans (by gcongr)
    _ ≤ 130 * ‖q‖ ^ 2 := by push_cast; nlinarith

end NTKB.HardyWright.TwentySquares
