/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TenSeriesBounds
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TenCuspSeries
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TenVanish
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TenCount

/-!
# Bounds for the proof of Liouville's `r₁₀` formula

`g(τ) = κ θ(τ)¹⁰ - L_W(τ) - c C(τ)` with `c = (20κ - π⁵/12 - π⁵/192)/4` (`gfun`), the constant `c`
chosen so that the coefficient of `q = e^{πiτ}` vanishes.

* `gfun_S`, `gfun_T_sq`: `g(-1/τ) = -i τ⁵ g(τ)`, `g(τ + 2) = g(τ)`;
* `norm_gfun_le`: `‖g(τ)‖ ≤ C e^{-2π Im τ}` for `Im τ ≥ 1`, from `θ¹⁰ = 1 + 20q + O(q²)`,
  `L_W = κ + (π⁵/12)(q + O(q²)) + (π⁵/192)(q + O(q²))` and `C = 4q + O(q²)`;
* `gfun_TS`, `norm_gTS_le`: `τ⁻⁵ g(TSτ)` is bounded on `Im τ ≥ 1`, `|Re τ| ≤ 1`.
-/

open ModularForm ModularGroup Complex Filter Topology EisensteinSeries Matrix
open scoped MatrixGroups Real UpperHalfPlane Manifold
open UpperHalfPlane hiding I

noncomputable section

namespace NTKB.HardyWright.TenSquares

open EightSquares (K1 ne_zero' norm_jacobiTheta_sub_one_le' norm_jacobiTheta_sub_le mdiff_of_eqOn
  theta_T_sq coe_TS_smul jacobiTheta_one_add norm_jacobiTheta₂_half_le)
open SixSquares (exp_neg_pi_im_le_quarter norm_q norm_cexp_le_one_of_re one_div_neg_I_div)
open TwelveSquares (norm_one_add_pow_sub_le norm_sub_of_hasSum)

/-! ### `θ¹⁰` -/

lemma I_pow_five : I ^ 5 = I := by rw [pow_succ, I_pow_four, one_mul]

lemma cpow_half_pow_ten (z : ℂ) : (z ^ (1 / 2 : ℂ)) ^ 10 = z ^ 5 := by
  have h := cpow_ofNat_inv_pow z 2
  rw [one_div, show (10 : ℕ) = 2 * 5 from rfl, pow_mul, h]

lemma theta10_S (τ : ℍ) : jacobiTheta ↑(S • τ) ^ 10 = -I * (τ : ℂ) ^ 5 * jacobiTheta τ ^ 10 := by
  rw [jacobiTheta_S_smul, mul_pow, cpow_half_pow_ten]
  have : (-I * (τ : ℂ)) ^ 5 = -I * (τ : ℂ) ^ 5 := by
    rw [mul_pow, neg_pow, I_pow_five]; ring
  rw [this]

/-- The factor of `θ((τ-1)/τ)¹⁰`. -/
def thetaTS (τ : ℍ) : ℂ := -I * (cexp (5 * π * I * τ / 2) * jacobiTheta₂ (-(τ : ℂ) / 2) τ ^ 10)

lemma theta10_TS (τ : ℍ) : jacobiTheta (((T * S) • τ : ℍ) : ℂ) ^ 10 = (τ : ℂ) ^ 5 * thetaTS τ := by
  have h0 := ne_zero' τ
  rw [coe_TS_smul, show ((τ : ℂ) - 1) / τ = 1 + (-1 / τ) by field_simp; ring, jacobiTheta_one_add,
    jacobiTheta₂_functional_equation]
  have e1' : -I * (-1 / (τ : ℂ)) = I / τ := by field_simp
  have e2 : -π * I * (1 / 2 : ℂ) ^ 2 / (-1 / (τ : ℂ)) = π * I * τ / 4 := by field_simp; ring
  have e3 : (1 / 2 : ℂ) / (-1 / (τ : ℂ)) = -(τ : ℂ) / 2 := by field_simp
  have e4 : -1 / (-1 / (τ : ℂ)) = τ := by field_simp
  rw [e1', e2, e3, e4, mul_pow, mul_pow, div_pow, cpow_half_pow_ten, one_pow,
    ← Complex.exp_nat_mul]
  have hI : (I / (τ : ℂ)) ^ 5 = I / (τ : ℂ) ^ 5 := by
    rw [div_pow, I_pow_five]
  rw [hI, thetaTS]
  have : ((10 : ℕ) : ℂ) * (π * I * τ / 4) = 5 * π * I * τ / 2 := by push_cast; ring
  rw [this]
  field_simp
  rw [show I ^ 2 = -1 from I_sq]
  ring

lemma norm_thetaTS_le (τ : ℍ) (hτ : 1 ≤ τ.im) : ‖thetaTS τ‖ ≤ K1 ^ 10 := by
  have hJ := norm_jacobiTheta₂_half_le τ hτ
  have he : ‖cexp (5 * π * I * τ / 2)‖ ≤ 1 := by
    apply norm_cexp_le_one_of_re
    have : (5 * π * I * (τ : ℂ) / 2).re = -(5 * π * τ.im / 2) := by
      simp [Complex.mul_re, Complex.mul_im]; ring
    rw [this]; have := τ.im_pos; nlinarith [Real.pi_pos]
  rw [thetaTS, norm_mul, norm_neg, Complex.norm_I, one_mul, norm_mul, norm_pow]
  calc ‖cexp (5 * π * I * τ / 2)‖ * ‖jacobiTheta₂ (-(τ : ℂ) / 2) τ‖ ^ 10 ≤ 1 * K1 ^ 10 := by
        gcongr
    _ = K1 ^ 10 := one_mul _

/-- `‖θ(τ)¹⁰ - 1 - 20 e^{πiτ}‖ ≤ Cθ e^{-2π Im τ}` for `Im τ ≥ 1`. -/
lemma norm_theta10_sub_le {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖jacobiTheta τ ^ 10 - 1 - 20 * cexp (π * I * τ)‖ ≤ (10 * 2 ^ 10 * 16 + 40) * rexp (-2 * π * τ.im) := by
  set w := jacobiTheta τ - 1 with hw
  have h1 := norm_jacobiTheta_sub_one_le' hτ
  have h4 := norm_jacobiTheta_sub_le hτ
  have hr := exp_neg_pi_im_le_quarter hτ
  have hwle : ‖w‖ ≤ 1 := by nlinarith [Real.exp_pos (-π * τ.im)]
  have hT := norm_one_add_pow_sub_le hwle 10
  rw [show 1 + w = jacobiTheta τ by rw [hw]; ring] at hT
  have e : jacobiTheta τ ^ 10 - 1 - 20 * cexp (π * I * τ) =
      (jacobiTheta τ ^ 10 - 1 - ((10 : ℕ) : ℂ) * w) +
        10 * (jacobiTheta τ - 1 - 2 * cexp (π * I * τ)) := by
    rw [hw]; push_cast; ring
  rw [e]
  have hsq : ‖w‖ ^ 2 ≤ 16 * rexp (-2 * π * τ.im) := by
    have : rexp (-2 * π * τ.im) = rexp (-π * τ.im) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [this]
    nlinarith [norm_nonneg w]
  have h44 : rexp (-4 * π * τ.im) ≤ rexp (-2 * π * τ.im) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  calc _ ≤ ‖jacobiTheta τ ^ 10 - 1 - ((10 : ℕ) : ℂ) * w‖ +
        ‖10 * (jacobiTheta τ - 1 - 2 * cexp (π * I * τ))‖ := norm_add_le _ _
    _ ≤ (10 : ℕ) * 2 ^ 10 * (16 * rexp (-2 * π * τ.im)) + 10 * (4 * rexp (-2 * π * τ.im)) := by
        rw [norm_mul, Complex.norm_ofNat]
        gcongr
        · exact hT.trans (by gcongr)
        · exact h4.trans (by gcongr)
    _ = (10 * 2 ^ 10 * 16 + 40) * rexp (-2 * π * τ.im) := by push_cast; ring

/-! ### The cusp form `C = 4q + O(q²)` -/

/-- `Cc = ∑ |c(n)/4| 2⁻ⁿ`. -/
def Cc : ℝ := ∑' n : ℕ, ‖(liouvilleCusp n : ℂ) / 4‖ * (1 / 2) ^ n

lemma Cc_nonneg : 0 ≤ Cc := tsum_nonneg fun n => by positivity

lemma hasSum_Cc : HasSum (fun n : ℕ => ‖(liouvilleCusp n : ℂ) / 4‖ * (1 / 2) ^ n) Cc := by
  refine Summable.hasSum ?_
  have hs := (hasSum_cuspSeriesR (x := 1 / 2) (by norm_num) (by norm_num)).summable.abs
  refine (hs.mul_left (1 / 4)).congr fun n => ?_
  rw [norm_div, Complex.norm_intCast, Complex.norm_ofNat, abs_mul,
    abs_of_pos (show (0 : ℝ) < (1 / 2) ^ n by positivity)]
  ring

lemma liouvilleCusp_zero : liouvilleCusp 0 = 0 := by decide

lemma norm_cusp_sub_le (τ : ℍ) (hτ : 1 ≤ τ.im) :
    ‖cusp τ - 4 * cexp (π * I * τ)‖ ≤ 16 * Cc * rexp (-2 * π * τ.im) := by
  have hq : ‖cexp (π * I * τ)‖ ≤ 1 / 2 := by
    rw [norm_q]; linarith [exp_neg_pi_im_le_quarter hτ]
  have hs : HasSum (fun n : ℕ => (liouvilleCusp n : ℂ) / 4 * cexp (π * I * τ) ^ n) (cusp τ / 4) := by
    have := (hasSum_cuspC τ.2).div_const 4
    refine this.congr_fun fun n => ?_
    ring
  have h := norm_sub_of_hasSum hs (by simp [liouvilleCusp_zero]) (by rw [liouvilleCusp_one]; norm_num)
    hq hasSum_Cc
  have e : ‖cexp (π * I * τ)‖ ^ 2 = rexp (-2 * π * τ.im) := by
    rw [norm_q, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [e] at h
  have e2 : cusp τ - 4 * cexp (π * I * τ) = 4 * (cusp τ / 4 - cexp (π * I * τ)) := by ring
  rw [e2, norm_mul, Complex.norm_ofNat]
  linarith

lemma norm_cusp_le (τ : ℍ) (hτ : 1 ≤ τ.im) : ‖cusp τ‖ ≤ 4 + 16 * Cc := by
  have h := norm_cusp_sub_le τ hτ
  have hq : ‖cexp (π * I * τ)‖ ≤ 1 := by
    rw [norm_q]; linarith [exp_neg_pi_im_le_quarter hτ]
  have he : rexp (-2 * π * τ.im) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hC := Cc_nonneg
  calc ‖cusp τ‖ = ‖(cusp τ - 4 * cexp (π * I * τ)) + 4 * cexp (π * I * τ)‖ := by ring_nf
    _ ≤ 16 * Cc * rexp (-2 * π * τ.im) + 4 * 1 := by
        refine (norm_add_le _ _).trans (add_le_add h ?_)
        rw [norm_mul, Complex.norm_ofNat]; gcongr
    _ ≤ 16 * Cc * 1 + 4 := by gcongr; norm_num
    _ = 4 + 16 * Cc := by ring

/-! ### `g = κ θ¹⁰ - L_W - c C` -/

/-- `c = (20κ - π⁵/12 - π⁵/192)/4`. -/
def cC : ℂ := (20 * kappa - π ^ 5 / 12 - π ^ 5 / 192) / 4

/-- `g(τ) = κ θ(τ)¹⁰ - L_W(τ) - c C(τ)`. -/
def gfun (τ : ℍ) : ℂ := kappa * jacobiTheta τ ^ 10 - Lsum5 W τ - cC * cusp τ

lemma gfun_S (τ : ℍ) : gfun (S • τ) = -I * (τ : ℂ) ^ 5 * gfun τ := by
  rw [gfun, gfun, theta10_S, Lsum5_W_S, cusp_S]; ring

lemma gfun_T_sq (τ : ℍ) : gfun (T ^ (2 : ℤ) • τ) = gfun τ := by
  rw [gfun, gfun, theta_T_sq, Lsum5_W_T2, cusp_T_sq]

/-- `τ⁻⁵ g(TSτ)`. -/
def gTS (τ : ℍ) : ℂ := kappa * thetaTS τ - Lsum5 Wp τ - cC * cuspTS τ

lemma gfun_TS (τ : ℍ) : gfun ((T * S) • τ) = (τ : ℂ) ^ 5 * gTS τ := by
  rw [gfun, theta10_TS, Lsum5_W_TS, cusp_TS, gTS]; ring

lemma mdiff_gfun : MDiff gfun := by
  have h1 : MDiff (fun τ : ℍ => kappa * jacobiTheta τ ^ 10) :=
    mdiff_of_eqOn (F := fun z => kappa * jacobiTheta z ^ 10)
      (fun z hz => (((differentiableAt_jacobiTheta hz).pow 10).const_mul kappa).differentiableWithinAt)
      fun _ => rfl
  have h3 : MDiff (fun τ : ℍ => cC * cusp τ) := (mdifferentiable_const).mul mdiff_cusp
  exact (h1.sub (mdiff_Lsum5 norm_W_le)).sub h3

/-- The constant of `norm_gfun_le`. -/
def Cg : ℝ := ‖kappa‖ * (10 * 2 ^ 10 * 16 + 40) + π ^ 5 / 12 * CB + π ^ 5 / 192 * CA +
  ‖cC‖ * (16 * Cc)

lemma norm_gfun_le (τ : ℍ) (hτ : 1 ≤ τ.im) : ‖gfun τ‖ ≤ Cg * rexp (-2 * π * τ.im) := by
  set q := cexp (π * I * τ) with hq
  have hqn : ‖q‖ = rexp (-π * τ.im) := norm_q τ
  have hq2 : ‖q‖ ≤ 1 / 2 := by rw [hqn]; linarith [exp_neg_pi_im_le_quarter hτ]
  have hqq : ‖q‖ ^ 2 = rexp (-2 * π * τ.im) := by
    rw [hqn, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e : gfun τ = kappa * (jacobiTheta τ ^ 10 - 1 - 20 * q) -
      π ^ 5 / 12 * (seriesB q - q) - π ^ 5 / 192 * (seriesA q - q) -
      cC * (cusp τ - 4 * q) := by
    rw [gfun, Lsum5_W_eq, cC]; ring
  rw [e]
  have h1 := norm_theta10_sub_le (τ := (τ : ℂ)) (by simpa using hτ)
  have h2 := norm_seriesB_sub_le hq2
  have h2' := norm_seriesA_sub_le hq2
  have h3 := norm_cusp_sub_le τ hτ
  have hi : (τ : ℂ).im = τ.im := rfl
  rw [hi] at h1
  rw [hqq] at h2 h2'
  have hp : ∀ c : ℝ, 0 < c → ‖(π : ℂ) ^ 5 / c‖ = π ^ 5 / c := fun c hc => by
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
      Complex.norm_real, Real.norm_of_nonneg hc.le]
  have hp12 : ‖(π : ℂ) ^ 5 / 12‖ = π ^ 5 / 12 := by exact_mod_cast hp 12 (by norm_num)
  have hp192 : ‖(π : ℂ) ^ 5 / 192‖ = π ^ 5 / 192 := by exact_mod_cast hp 192 (by norm_num)
  calc _ ≤ ‖kappa * (jacobiTheta τ ^ 10 - 1 - 20 * q)‖ +
        ‖(π : ℂ) ^ 5 / 12 * (seriesB q - q)‖ + ‖(π : ℂ) ^ 5 / 192 * (seriesA q - q)‖ +
        ‖cC * (cusp τ - 4 * q)‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ ‖kappa‖ * ((10 * 2 ^ 10 * 16 + 40) * rexp (-2 * π * τ.im)) +
          π ^ 5 / 12 * (CB * rexp (-2 * π * τ.im)) +
          π ^ 5 / 192 * (CA * rexp (-2 * π * τ.im)) +
          ‖cC‖ * (16 * Cc * rexp (-2 * π * τ.im)) := by
        rw [norm_mul, norm_mul, norm_mul, norm_mul, hp12, hp192]
        gcongr
    _ = Cg * rexp (-2 * π * τ.im) := by rw [Cg]; ring

/-- The constant of `norm_gTS_le`. -/
def MTS : ℝ := ‖kappa‖ * K1 ^ 10 + ML5 + ‖cC‖ * MTSc

lemma norm_gTS_le (τ : ℍ) (hτ : 1 ≤ τ.im) (hr : |τ.re| ≤ 1) : ‖gTS τ‖ ≤ MTS := by
  rw [gTS, MTS]
  calc ‖kappa * thetaTS τ - Lsum5 Wp τ - cC * cuspTS τ‖
      ≤ ‖kappa * thetaTS τ‖ + ‖Lsum5 Wp τ‖ + ‖cC * cuspTS τ‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ ‖kappa‖ * K1 ^ 10 + ML5 + ‖cC‖ * MTSc := by
        rw [norm_mul, norm_mul]
        gcongr
        · exact norm_thetaTS_le τ hτ
        · exact norm_Lsum5_Wp_le τ hτ hr
        · exact norm_cuspTS_le τ hτ

end NTKB.HardyWright.TenSquares
