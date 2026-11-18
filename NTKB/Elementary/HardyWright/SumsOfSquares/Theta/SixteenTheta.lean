/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.SixteenSeriesBounds
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TwelveBounds

/-!
# `θ¹⁶` and `θ⁴`: transformation laws and bounds

`θ(-1/τ)¹⁶ = τ⁸ θ(τ)¹⁶`, `θ(TSτ)¹⁶ = τ⁸ thetaTS16 τ` with `thetaTS16` bounded on `Im τ ≥ 1`;
`θ(-1/τ)⁴ = -τ² θ(τ)⁴`, `θ(TSτ)⁴ = τ² thetaTS4 τ`. Bounds for `Im τ ≥ 1`:
`‖θ¹⁶ - 1 - 32 q - 480 q²‖ ≤ C ‖q‖³` and `‖θ⁴ - 1 - 8 q‖ ≤ C ‖q‖²`, `q = e^{πiτ}`.
-/

open ModularForm ModularGroup Complex Filter Topology EisensteinSeries Matrix
open scoped MatrixGroups Real UpperHalfPlane Manifold
open UpperHalfPlane hiding I

noncomputable section

namespace NTKB.HardyWright.SixteenSquares

open EightSquares (K1 ne_zero' norm_jacobiTheta_sub_one_le' norm_jacobiTheta_sub_le mdiff_of_eqOn
  theta_T_sq coe_TS_smul jacobiTheta_one_add norm_jacobiTheta₂_half_le)
open SixSquares (exp_neg_pi_im_le_quarter norm_q norm_cexp_le_one_of_re one_div_neg_I_div)
open TwelveSquares (norm_one_add_pow_sub_le)

lemma cpow_half_pow_mul (z : ℂ) (n : ℕ) : (z ^ (1 / 2 : ℂ)) ^ (2 * n) = z ^ n := by
  have h := cpow_ofNat_inv_pow z 2
  rw [one_div, pow_mul, h]

lemma cpow_half_pow_16 (z : ℂ) : (z ^ (1 / 2 : ℂ)) ^ 16 = z ^ 8 := cpow_half_pow_mul z 8

lemma cpow_half_pow_4 (z : ℂ) : (z ^ (1 / 2 : ℂ)) ^ 4 = z ^ 2 := cpow_half_pow_mul z 2

lemma I_pow_eight : I ^ 8 = 1 := by
  rw [show (8 : ℕ) = 4 * 2 from rfl, pow_mul, I_pow_four]; simp

/-! ### `θ¹⁶` -/

lemma theta16_S (τ : ℍ) : jacobiTheta ↑(S • τ) ^ 16 = (τ : ℂ) ^ 8 * jacobiTheta τ ^ 16 := by
  rw [jacobiTheta_S_smul, mul_pow, cpow_half_pow_16]
  have : (-I * (τ : ℂ)) ^ 8 = (τ : ℂ) ^ 8 := by
    rw [mul_pow, neg_pow, I_pow_eight]; ring
  rw [this]

/-- The factor of `θ((τ-1)/τ)¹⁶`. -/
def thetaTS16 (τ : ℍ) : ℂ := cexp (4 * π * I * τ) * jacobiTheta₂ (-(τ : ℂ) / 2) τ ^ 16

lemma theta16_TS (τ : ℍ) :
    jacobiTheta (((T * S) • τ : ℍ) : ℂ) ^ 16 = (τ : ℂ) ^ 8 * thetaTS16 τ := by
  have h0 := ne_zero' τ
  rw [coe_TS_smul, show ((τ : ℂ) - 1) / τ = 1 + (-1 / τ) by field_simp; ring, jacobiTheta_one_add,
    jacobiTheta₂_functional_equation]
  have e1' : -I * (-1 / (τ : ℂ)) = I / τ := by field_simp
  have e2 : -π * I * (1 / 2 : ℂ) ^ 2 / (-1 / (τ : ℂ)) = π * I * τ / 4 := by field_simp; ring
  have e3 : (1 / 2 : ℂ) / (-1 / (τ : ℂ)) = -(τ : ℂ) / 2 := by field_simp
  have e4 : -1 / (-1 / (τ : ℂ)) = τ := by field_simp
  rw [e1', e2, e3, e4, mul_pow, mul_pow, div_pow, cpow_half_pow_16, one_pow,
    ← Complex.exp_nat_mul]
  have hI : (I / (τ : ℂ)) ^ 8 = 1 / (τ : ℂ) ^ 8 := by
    rw [div_pow, I_pow_eight]
  rw [hI, thetaTS16]
  have : ((16 : ℕ) : ℂ) * (π * I * τ / 4) = 4 * π * I * τ := by push_cast; ring
  rw [this]
  field_simp

lemma norm_thetaTS16_le (τ : ℍ) (hτ : 1 ≤ τ.im) : ‖thetaTS16 τ‖ ≤ K1 ^ 16 := by
  have hJ := norm_jacobiTheta₂_half_le τ hτ
  have he : ‖cexp (4 * π * I * τ)‖ ≤ 1 := by
    apply norm_cexp_le_one_of_re
    have : (4 * π * I * (τ : ℂ)).re = -(4 * π * τ.im) := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [this]; have := τ.im_pos; nlinarith [Real.pi_pos]
  rw [thetaTS16, norm_mul, norm_pow]
  calc ‖cexp (4 * π * I * τ)‖ * ‖jacobiTheta₂ (-(τ : ℂ) / 2) τ‖ ^ 16 ≤ 1 * K1 ^ 16 := by
        gcongr
    _ = K1 ^ 16 := one_mul _

/-! ### `θ⁴` -/

lemma theta4_S (τ : ℍ) : jacobiTheta ↑(S • τ) ^ 4 = -((τ : ℂ) ^ 2 * jacobiTheta τ ^ 4) := by
  rw [jacobiTheta_S_smul, mul_pow, cpow_half_pow_4]
  have : (-I * (τ : ℂ)) ^ 2 = -(τ : ℂ) ^ 2 := by
    rw [mul_pow, neg_pow, I_sq]; ring
  rw [this]; ring

/-- The factor of `θ((τ-1)/τ)⁴`. -/
def thetaTS4 (τ : ℍ) : ℂ := -(cexp (π * I * τ) * jacobiTheta₂ (-(τ : ℂ) / 2) τ ^ 4)

lemma theta4_TS (τ : ℍ) :
    jacobiTheta (((T * S) • τ : ℍ) : ℂ) ^ 4 = (τ : ℂ) ^ 2 * thetaTS4 τ := by
  have h0 := ne_zero' τ
  rw [coe_TS_smul, show ((τ : ℂ) - 1) / τ = 1 + (-1 / τ) by field_simp; ring, jacobiTheta_one_add,
    jacobiTheta₂_functional_equation]
  have e1' : -I * (-1 / (τ : ℂ)) = I / τ := by field_simp
  have e2 : -π * I * (1 / 2 : ℂ) ^ 2 / (-1 / (τ : ℂ)) = π * I * τ / 4 := by field_simp; ring
  have e3 : (1 / 2 : ℂ) / (-1 / (τ : ℂ)) = -(τ : ℂ) / 2 := by field_simp
  have e4 : -1 / (-1 / (τ : ℂ)) = τ := by field_simp
  rw [e1', e2, e3, e4, mul_pow, mul_pow, div_pow, cpow_half_pow_4, one_pow,
    ← Complex.exp_nat_mul]
  have hI : (I / (τ : ℂ)) ^ 2 = -1 / (τ : ℂ) ^ 2 := by
    rw [div_pow, I_sq]
  rw [hI, thetaTS4]
  have : ((4 : ℕ) : ℂ) * (π * I * τ / 4) = π * I * τ := by push_cast; ring
  rw [this]
  field_simp

lemma norm_thetaTS4_le (τ : ℍ) (hτ : 1 ≤ τ.im) : ‖thetaTS4 τ‖ ≤ K1 ^ 4 := by
  have hJ := norm_jacobiTheta₂_half_le τ hτ
  have he : ‖cexp (π * I * τ)‖ ≤ 1 := by
    apply norm_cexp_le_one_of_re
    have : (π * I * (τ : ℂ)).re = -(π * τ.im) := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [this]; have := τ.im_pos; nlinarith [Real.pi_pos]
  rw [thetaTS4, norm_neg, norm_mul, norm_pow]
  calc ‖cexp (π * I * τ)‖ * ‖jacobiTheta₂ (-(τ : ℂ) / 2) τ‖ ^ 4 ≤ 1 * K1 ^ 4 := by
        gcongr
    _ = K1 ^ 4 := one_mul _

/-! ### Bounds -/

lemma pow_add_le_quarter {t : ℝ} (h0 : 0 ≤ t) (h : t ≤ 1 / 4) (m k : ℕ) :
    t ^ (m + k) ≤ t ^ m * (1 / 4) ^ k := by
  rw [pow_add]
  gcongr

/-- `‖(1 + w)ⁿ - 1 - n w - (n (n-1)/2) w²‖ ≤ n² 2ⁿ ‖w‖³` for `‖w‖ ≤ 1`. -/
lemma norm_one_add_pow_sub3_le {w : ℂ} (hw : ‖w‖ ≤ 1) (n : ℕ) :
    ‖(1 + w) ^ n - 1 - n * w - ((n : ℂ) * ((n : ℂ) - 1) / 2) * w ^ 2‖ ≤
      (n : ℝ) ^ 2 * 2 ^ n * ‖w‖ ^ 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (1 + w) ^ (n + 1) - 1 - ((n + 1 : ℕ) : ℂ) * w -
        (((n + 1 : ℕ) : ℂ) * (((n + 1 : ℕ) : ℂ) - 1) / 2) * w ^ 2 =
        (1 + w) * ((1 + w) ^ n - 1 - n * w - ((n : ℂ) * ((n : ℂ) - 1) / 2) * w ^ 2) +
          ((n : ℂ) * ((n : ℂ) - 1) / 2) * w ^ 3 := by push_cast; ring
    rw [e]
    have h1 : ‖1 + w‖ ≤ 2 := (norm_add_le _ _).trans (by rw [norm_one]; linarith)
    have hc : ‖(n : ℂ) * ((n : ℂ) - 1) / 2‖ ≤ (n : ℝ) ^ 2 := by
      have : (n : ℂ) * ((n : ℂ) - 1) / 2 = (((n : ℝ) * ((n : ℝ) - 1) / 2 : ℝ) : ℂ) := by
        push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        constructor <;> nlinarith
    have hn2 : (n : ℝ) + 1 ≤ 2 ^ n := by
      have := Nat.lt_two_pow_self (n := n)
      exact_mod_cast this
    have hw3 : 0 ≤ ‖w‖ ^ 3 := by positivity
    calc ‖(1 + w) * ((1 + w) ^ n - 1 - n * w - ((n : ℂ) * ((n : ℂ) - 1) / 2) * w ^ 2) +
          ((n : ℂ) * ((n : ℂ) - 1) / 2) * w ^ 3‖
        ≤ ‖1 + w‖ * ‖(1 + w) ^ n - 1 - n * w - ((n : ℂ) * ((n : ℂ) - 1) / 2) * w ^ 2‖ +
            ‖(n : ℂ) * ((n : ℂ) - 1) / 2‖ * ‖w‖ ^ 3 := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul, norm_pow]
      _ ≤ 2 * ((n : ℝ) ^ 2 * 2 ^ n * ‖w‖ ^ 3) + (n : ℝ) ^ 2 * ‖w‖ ^ 3 := by gcongr
      _ ≤ ((n + 1 : ℕ) : ℝ) ^ 2 * 2 ^ (n + 1) * ‖w‖ ^ 3 := by
          push_cast
          have : (n : ℝ) ^ 2 ≤ 2 * (2 * n + 1) * 2 ^ n := by
            have h0 : (0 : ℝ) ≤ n := n.cast_nonneg
            nlinarith [mul_le_mul_of_nonneg_left hn2 (by positivity : (0 : ℝ) ≤ 2 * (2 * n + 1))]
          have h3 : 2 * ((n : ℝ) ^ 2 * 2 ^ n) + (n : ℝ) ^ 2 ≤ ((n : ℝ) + 1) ^ 2 * 2 ^ (n + 1) := by
            have e2 : ((n : ℝ) + 1) ^ 2 * 2 ^ (n + 1) =
                2 * (n : ℝ) ^ 2 * 2 ^ n + 2 * (2 * n + 1) * 2 ^ n := by rw [pow_succ]; ring
            rw [e2]; linarith
          nlinarith [mul_le_mul_of_nonneg_right h3 hw3]

/-- `‖θ(τ)¹⁶ - 1 - 32 q - 480 q²‖ ≤ C ‖q‖³` for `Im τ ≥ 1`. -/
lemma norm_theta16_sub_le {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖jacobiTheta τ ^ 16 - 1 - 32 * cexp (π * I * τ) - 480 * cexp (π * I * τ) ^ 2‖ ≤
      (256 * 65536 * 64 + 200) * ‖cexp (π * I * τ)‖ ^ 3 := by
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
  have hT := norm_one_add_pow_sub3_le hwle 16
  rw [show 1 + w = jacobiTheta τ by rw [hw]; ring] at hT
  have eq1 : jacobiTheta τ ^ 16 - 1 - 32 * q - 480 * q ^ 2 =
      (jacobiTheta τ ^ 16 - 1 - ((16 : ℕ) : ℂ) * w - (((16 : ℕ) : ℂ) * (((16 : ℕ) : ℂ) - 1) / 2) * w ^ 2)
        + 16 * e + 480 * (q * e) + 120 * e ^ 2 := by
    rw [he, hw]; push_cast; ring
  rw [eq1]
  have hw3 : ‖w‖ ^ 3 ≤ (4 * ‖q‖) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hwn 3
  have b1 : ‖jacobiTheta τ ^ 16 - 1 - ((16 : ℕ) : ℂ) * w -
      (((16 : ℕ) : ℂ) * (((16 : ℕ) : ℂ) - 1) / 2) * w ^ 2‖ ≤ 256 * 65536 * 64 * ‖q‖ ^ 3 := by
    refine hT.trans ?_
    push_cast
    nlinarith [pow_nonneg ht0 3]
  have b2 : ‖(16 : ℂ) * e‖ ≤ 16 * (4 * ‖q‖ ^ 4) := by
    rw [norm_mul]; simp only [Complex.norm_ofNat]; gcongr
  have b3 : ‖(480 : ℂ) * (q * e)‖ ≤ 480 * (‖q‖ * (4 * ‖q‖ ^ 4)) := by
    rw [norm_mul, norm_mul]; simp only [Complex.norm_ofNat]; gcongr
  have b4 : ‖(120 : ℂ) * e ^ 2‖ ≤ 120 * (4 * ‖q‖ ^ 4) ^ 2 := by
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
  calc _ ≤ ‖jacobiTheta τ ^ 16 - 1 - ((16 : ℕ) : ℂ) * w -
        (((16 : ℕ) : ℂ) * (((16 : ℕ) : ℂ) - 1) / 2) * w ^ 2‖ + ‖(16 : ℂ) * e‖ +
        ‖(480 : ℂ) * (q * e)‖ + ‖(120 : ℂ) * e ^ 2‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ 256 * 65536 * 64 * ‖q‖ ^ 3 + 16 * (4 * ‖q‖ ^ 4) + 480 * (‖q‖ * (4 * ‖q‖ ^ 4)) +
        120 * (4 * ‖q‖ ^ 4) ^ 2 := by gcongr
    _ ≤ (256 * 65536 * 64 + 200) * ‖q‖ ^ 3 := by nlinarith

/-- `‖θ(τ)⁴ - 1 - 8 q‖ ≤ 1040 ‖q‖²` for `Im τ ≥ 1`. -/
lemma norm_theta4_sub_le {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖jacobiTheta τ ^ 4 - 1 - 8 * cexp (π * I * τ)‖ ≤ 1040 * ‖cexp (π * I * τ)‖ ^ 2 := by
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
  have hT := norm_one_add_pow_sub_le hwle 4
  rw [show 1 + w = jacobiTheta τ by rw [hw]; ring] at hT
  have eq1 : jacobiTheta τ ^ 4 - 1 - 8 * q =
      (jacobiTheta τ ^ 4 - 1 - ((4 : ℕ) : ℂ) * w) + 4 * e := by
    rw [he, hw]; push_cast; ring
  rw [eq1]
  have hw2 : ‖w‖ ^ 2 ≤ (4 * ‖q‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hwn 2
  have b2 : ‖(4 : ℂ) * e‖ ≤ 4 * (4 * ‖q‖ ^ 4) := by
    rw [norm_mul]; simp only [Complex.norm_ofNat]; gcongr
  have p2 : 0 ≤ ‖q‖ ^ 2 := by positivity
  have p4 : ‖q‖ ^ 4 ≤ ‖q‖ ^ 2 / 16 := by
    have := pow_add_le_quarter ht0 ht 2 2
    norm_num at this ⊢; linarith
  calc _ ≤ ‖jacobiTheta τ ^ 4 - 1 - ((4 : ℕ) : ℂ) * w‖ + ‖(4 : ℂ) * e‖ := norm_add_le _ _
    _ ≤ (4 : ℕ) * 2 ^ 4 * (4 * ‖q‖) ^ 2 + 4 * (4 * ‖q‖ ^ 4) := by
        gcongr
        exact hT.trans (by gcongr)
    _ ≤ 1040 * ‖q‖ ^ 2 := by push_cast; nlinarith

end NTKB.HardyWright.SixteenSquares
