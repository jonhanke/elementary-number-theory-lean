/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.OcticCusp
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.SixteenTheta
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TenBounds

/-!
# `θ¹⁸` and `θ⁶`: transformation laws and bounds

`θ(-1/τ)¹⁸ = -i τ⁹ θ(τ)¹⁸`, `θ(TSτ)¹⁸ = τ⁹ thetaTS18 τ` with `thetaTS18` bounded on `Im τ ≥ 1`;
`θ(-1/τ)⁶ = i τ³ θ(τ)⁶`, `θ(TSτ)⁶ = τ³ thetaTS6 τ`. Bounds for `Im τ ≥ 1`, `q = e^{πiτ}`:
`‖θ¹⁸ - 1 - 36 q - 612 q²‖ ≤ C ‖q‖³` and `‖θ⁶ - 1 - 12 q‖ ≤ C ‖q‖²`. (The method of
`SixteenTheta.lean` and `TenBounds.lean`.)
-/

open ModularForm ModularGroup Complex Filter Topology EisensteinSeries Matrix
open scoped MatrixGroups Real UpperHalfPlane Manifold
open UpperHalfPlane hiding I

noncomputable section

namespace NTKB.HardyWright.EighteenSquares

open EightSquares (K1 ne_zero' norm_jacobiTheta_sub_one_le' norm_jacobiTheta_sub_le mdiff_of_eqOn
  theta_T_sq coe_TS_smul jacobiTheta_one_add norm_jacobiTheta₂_half_le)
open SixSquares (exp_neg_pi_im_le_quarter norm_q norm_cexp_le_one_of_re one_div_neg_I_div)
open TwelveSquares (norm_one_add_pow_sub_le)
open SixteenSquares (cpow_half_pow_mul pow_add_le_quarter norm_one_add_pow_sub3_le)

lemma I_pow_nine : I ^ 9 = I := by
  rw [show I ^ 9 = (I ^ 4) ^ 2 * I by ring, I_pow_four]; ring

lemma I_pow_three' : I ^ 3 = -I := by
  rw [pow_succ, I_sq]; ring

/-! ### `θ¹⁸` -/

lemma theta18_S (τ : ℍ) : jacobiTheta ↑(S • τ) ^ 18 = -I * (τ : ℂ) ^ 9 * jacobiTheta τ ^ 18 := by
  rw [jacobiTheta_S_smul, mul_pow, show (18 : ℕ) = 2 * 9 from rfl, cpow_half_pow_mul]
  have : (-I * (τ : ℂ)) ^ 9 = -I * (τ : ℂ) ^ 9 := by
    rw [mul_pow, neg_pow, I_pow_nine]; ring
  rw [this]

/-- The factor of `θ((τ-1)/τ)¹⁸`. -/
def thetaTS18 (τ : ℍ) : ℂ := -I * (cexp (9 * π * I * τ / 2) * jacobiTheta₂ (-(τ : ℂ) / 2) τ ^ 18)

lemma theta18_TS (τ : ℍ) :
    jacobiTheta (((T * S) • τ : ℍ) : ℂ) ^ 18 = (τ : ℂ) ^ 9 * thetaTS18 τ := by
  have h0 := ne_zero' τ
  rw [coe_TS_smul, show ((τ : ℂ) - 1) / τ = 1 + (-1 / τ) by field_simp; ring, jacobiTheta_one_add,
    jacobiTheta₂_functional_equation]
  have e1' : -I * (-1 / (τ : ℂ)) = I / τ := by field_simp
  have e2 : -π * I * (1 / 2 : ℂ) ^ 2 / (-1 / (τ : ℂ)) = π * I * τ / 4 := by field_simp; ring
  have e3 : (1 / 2 : ℂ) / (-1 / (τ : ℂ)) = -(τ : ℂ) / 2 := by field_simp
  have e4 : -1 / (-1 / (τ : ℂ)) = τ := by field_simp
  rw [e1', e2, e3, e4, mul_pow, mul_pow, div_pow, show (18 : ℕ) = 2 * 9 from rfl,
    cpow_half_pow_mul, one_pow, ← Complex.exp_nat_mul]
  have hI : (I / (τ : ℂ)) ^ 9 = I / (τ : ℂ) ^ 9 := by
    rw [div_pow, I_pow_nine]
  rw [hI, thetaTS18]
  have : ((2 * 9 : ℕ) : ℂ) * (π * I * τ / 4) = 9 * π * I * τ / 2 := by push_cast; ring
  rw [this]
  field_simp
  rw [show I ^ 2 = -1 from I_sq]
  ring

lemma norm_thetaTS18_le (τ : ℍ) (hτ : 1 ≤ τ.im) : ‖thetaTS18 τ‖ ≤ K1 ^ 18 := by
  have hJ := norm_jacobiTheta₂_half_le τ hτ
  have he : ‖cexp (9 * π * I * τ / 2)‖ ≤ 1 := by
    apply norm_cexp_le_one_of_re
    have : (9 * π * I * (τ : ℂ) / 2).re = -(9 * π * τ.im / 2) := by
      simp [Complex.mul_re, Complex.mul_im]; ring
    rw [this]; have := τ.im_pos; nlinarith [Real.pi_pos]
  rw [thetaTS18, norm_mul, norm_neg, Complex.norm_I, one_mul, norm_mul, norm_pow]
  calc ‖cexp (9 * π * I * τ / 2)‖ * ‖jacobiTheta₂ (-(τ : ℂ) / 2) τ‖ ^ 18 ≤ 1 * K1 ^ 18 := by
        gcongr
    _ = K1 ^ 18 := one_mul _

/-! ### `θ⁶` -/

lemma theta6_S (τ : ℍ) : jacobiTheta ↑(S • τ) ^ 6 = I * (τ : ℂ) ^ 3 * jacobiTheta τ ^ 6 := by
  rw [jacobiTheta_S_smul, mul_pow, show (6 : ℕ) = 2 * 3 from rfl, cpow_half_pow_mul]
  have : (-I * (τ : ℂ)) ^ 3 = I * (τ : ℂ) ^ 3 := by
    rw [mul_pow, neg_pow, I_pow_three']; ring
  rw [this]

/-- The factor of `θ((τ-1)/τ)⁶`. -/
def thetaTS6 (τ : ℍ) : ℂ := I * (cexp (3 * π * I * τ / 2) * jacobiTheta₂ (-(τ : ℂ) / 2) τ ^ 6)

lemma theta6_TS (τ : ℍ) :
    jacobiTheta (((T * S) • τ : ℍ) : ℂ) ^ 6 = (τ : ℂ) ^ 3 * thetaTS6 τ := by
  have h0 := ne_zero' τ
  rw [coe_TS_smul, show ((τ : ℂ) - 1) / τ = 1 + (-1 / τ) by field_simp; ring, jacobiTheta_one_add,
    jacobiTheta₂_functional_equation]
  have e1' : -I * (-1 / (τ : ℂ)) = I / τ := by field_simp
  have e2 : -π * I * (1 / 2 : ℂ) ^ 2 / (-1 / (τ : ℂ)) = π * I * τ / 4 := by field_simp; ring
  have e3 : (1 / 2 : ℂ) / (-1 / (τ : ℂ)) = -(τ : ℂ) / 2 := by field_simp
  have e4 : -1 / (-1 / (τ : ℂ)) = τ := by field_simp
  rw [e1', e2, e3, e4, mul_pow, mul_pow, div_pow, show (6 : ℕ) = 2 * 3 from rfl,
    cpow_half_pow_mul, one_pow, ← Complex.exp_nat_mul]
  have hI : (I / (τ : ℂ)) ^ 3 = -I / (τ : ℂ) ^ 3 := by
    rw [div_pow, I_pow_three']
  rw [hI, thetaTS6]
  have : ((2 * 3 : ℕ) : ℂ) * (π * I * τ / 4) = 3 * π * I * τ / 2 := by push_cast; ring
  rw [this]
  field_simp
  rw [show I ^ 2 = -1 from I_sq]
  ring

lemma norm_thetaTS6_le (τ : ℍ) (hτ : 1 ≤ τ.im) : ‖thetaTS6 τ‖ ≤ K1 ^ 6 := by
  have hJ := norm_jacobiTheta₂_half_le τ hτ
  have he : ‖cexp (3 * π * I * τ / 2)‖ ≤ 1 := by
    apply norm_cexp_le_one_of_re
    have : (3 * π * I * (τ : ℂ) / 2).re = -(3 * π * τ.im / 2) := by
      simp [Complex.mul_re, Complex.mul_im]; ring
    rw [this]; have := τ.im_pos; nlinarith [Real.pi_pos]
  rw [thetaTS6, norm_mul, Complex.norm_I, one_mul, norm_mul, norm_pow]
  calc ‖cexp (3 * π * I * τ / 2)‖ * ‖jacobiTheta₂ (-(τ : ℂ) / 2) τ‖ ^ 6 ≤ 1 * K1 ^ 6 := by
        gcongr
    _ = K1 ^ 6 := one_mul _

/-! ### Bounds -/

/-- `‖θ(τ)¹⁸ - 1 - 36 q - 612 q²‖ ≤ C ‖q‖³` for `Im τ ≥ 1`. -/
lemma norm_theta18_sub_le {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖jacobiTheta τ ^ 18 - 1 - 36 * cexp (π * I * τ) - 612 * cexp (π * I * τ) ^ 2‖ ≤
      (324 * 262144 * 64 + 200) * ‖cexp (π * I * τ)‖ ^ 3 := by
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
  have hT := norm_one_add_pow_sub3_le hwle 18
  rw [show 1 + w = jacobiTheta τ by rw [hw]; ring] at hT
  have eq1 : jacobiTheta τ ^ 18 - 1 - 36 * q - 612 * q ^ 2 =
      (jacobiTheta τ ^ 18 - 1 - ((18 : ℕ) : ℂ) * w - (((18 : ℕ) : ℂ) * (((18 : ℕ) : ℂ) - 1) / 2) * w ^ 2)
        + 18 * e + 612 * (q * e) + 153 * e ^ 2 := by
    rw [he, hw]; push_cast; ring
  rw [eq1]
  have hw3 : ‖w‖ ^ 3 ≤ (4 * ‖q‖) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hwn 3
  have b1 : ‖jacobiTheta τ ^ 18 - 1 - ((18 : ℕ) : ℂ) * w -
      (((18 : ℕ) : ℂ) * (((18 : ℕ) : ℂ) - 1) / 2) * w ^ 2‖ ≤ 324 * 262144 * 64 * ‖q‖ ^ 3 := by
    refine hT.trans ?_
    push_cast
    nlinarith [pow_nonneg ht0 3]
  have b2 : ‖(18 : ℂ) * e‖ ≤ 18 * (4 * ‖q‖ ^ 4) := by
    rw [norm_mul]; simp only [Complex.norm_ofNat]; gcongr
  have b3 : ‖(612 : ℂ) * (q * e)‖ ≤ 612 * (‖q‖ * (4 * ‖q‖ ^ 4)) := by
    rw [norm_mul, norm_mul]; simp only [Complex.norm_ofNat]; gcongr
  have b4 : ‖(153 : ℂ) * e ^ 2‖ ≤ 153 * (4 * ‖q‖ ^ 4) ^ 2 := by
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
  calc _ ≤ ‖jacobiTheta τ ^ 18 - 1 - ((18 : ℕ) : ℂ) * w -
        (((18 : ℕ) : ℂ) * (((18 : ℕ) : ℂ) - 1) / 2) * w ^ 2‖ + ‖(18 : ℂ) * e‖ +
        ‖(612 : ℂ) * (q * e)‖ + ‖(153 : ℂ) * e ^ 2‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ 324 * 262144 * 64 * ‖q‖ ^ 3 + 18 * (4 * ‖q‖ ^ 4) + 612 * (‖q‖ * (4 * ‖q‖ ^ 4)) +
        153 * (4 * ‖q‖ ^ 4) ^ 2 := by gcongr
    _ ≤ (324 * 262144 * 64 + 200) * ‖q‖ ^ 3 := by nlinarith

/-- `‖θ(τ)⁶ - 1 - 12 q‖ ≤ 6150 ‖q‖²` for `Im τ ≥ 1`. -/
lemma norm_theta6_sub_le {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖jacobiTheta τ ^ 6 - 1 - 12 * cexp (π * I * τ)‖ ≤ 6150 * ‖cexp (π * I * τ)‖ ^ 2 := by
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
  have hT := norm_one_add_pow_sub_le hwle 6
  rw [show 1 + w = jacobiTheta τ by rw [hw]; ring] at hT
  have eq1 : jacobiTheta τ ^ 6 - 1 - 12 * q =
      (jacobiTheta τ ^ 6 - 1 - ((6 : ℕ) : ℂ) * w) + 6 * e := by
    rw [he, hw]; push_cast; ring
  rw [eq1]
  have hw2 : ‖w‖ ^ 2 ≤ (4 * ‖q‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hwn 2
  have b2 : ‖(6 : ℂ) * e‖ ≤ 6 * (4 * ‖q‖ ^ 4) := by
    rw [norm_mul]; simp only [Complex.norm_ofNat]; gcongr
  have p2 : 0 ≤ ‖q‖ ^ 2 := by positivity
  have p4 : ‖q‖ ^ 4 ≤ ‖q‖ ^ 2 / 16 := by
    have := pow_add_le_quarter ht0 ht 2 2
    norm_num at this ⊢; linarith
  calc _ ≤ ‖jacobiTheta τ ^ 6 - 1 - ((6 : ℕ) : ℂ) * w‖ + ‖(6 : ℂ) * e‖ := norm_add_le _ _
    _ ≤ (6 : ℕ) * 2 ^ 6 * (4 * ‖q‖) ^ 2 + 6 * (4 * ‖q‖ ^ 4) := by
        gcongr
        exact hT.trans (by gcongr)
    _ ≤ 6150 * ‖q‖ ^ 2 := by push_cast; nlinarith

end NTKB.HardyWright.EighteenSquares
