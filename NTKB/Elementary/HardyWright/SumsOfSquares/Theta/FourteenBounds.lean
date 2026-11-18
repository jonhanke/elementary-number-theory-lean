/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.FourteenTheta
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TwelveBounds

/-!
# Bounds for the proof of the `r₁₄` formula

The cusp form `f = θ² η¹²` (weight `7`, the laws of `θ¹⁴`) and
`g(τ) = κ θ(τ)¹⁴ - L_W(τ) - c f(τ)` with `c = 28 κ - π⁷/360 + π⁷/23040` (`gfun`), the constant `c`
chosen so that the coefficient of `q = e^{πiτ}` vanishes.

* `gfun_S`, `gfun_T_sq`: `g(-1/τ) = i τ⁷ g(τ)`, `g(τ + 2) = g(τ)`;
* `norm_gfun_le`: `‖g(τ)‖ ≤ C e^{-2π Im τ}` for `Im τ ≥ 1`;
* `gfun_TS`, `norm_gTS_le`: `τ⁻⁷ g(TSτ)` is bounded on `Im τ ≥ 1`, `|Re τ| ≤ 1`.
-/

open ModularForm ModularGroup Complex Filter Topology EisensteinSeries Matrix
open scoped MatrixGroups Real UpperHalfPlane Manifold
open UpperHalfPlane hiding I

noncomputable section

namespace NTKB.HardyWright.FourteenSquares

open EightSquares (K1 ne_zero' norm_jacobiTheta_sub_one_le' norm_jacobiTheta_sub_le mdiff_of_eqOn
  theta_T_sq coe_TS_smul jacobiTheta_one_add norm_jacobiTheta₂_half_le)
open SixSquares (exp_neg_pi_im_le_quarter norm_q norm_cexp_le_one_of_re one_div_neg_I_div)
open TwelveSquares (norm_one_add_pow_sub_le norm_sub_of_hasSum eta12 eta12_S eta12_T_sq eta12_TS
  mdiff_eta12 norm_eta12_sub_le norm_eta12_le Ceta Ceta_nonneg)

/-! ### The cusp form `f = θ² η¹²` -/

/-- `f(τ) = θ(τ)² η(τ)¹²`. -/
def cuspF (τ : ℍ) : ℂ := jacobiTheta τ ^ 2 * eta12 τ

lemma cuspF_S (τ : ℍ) : cuspF (S • τ) = I * (τ : ℂ) ^ 7 * cuspF τ := by
  rw [cuspF, cuspF, theta2_S, eta12_S]
  ring

lemma cuspF_T_sq (τ : ℍ) : cuspF (T ^ (2 : ℤ) • τ) = cuspF τ := by
  rw [cuspF, cuspF, theta_T_sq, eta12_T_sq]

/-- `τ⁻⁷ f(TSτ)`. -/
def cuspFTS (τ : ℍ) : ℂ := thetaTS2 τ * eta12 τ

lemma cuspF_TS (τ : ℍ) : cuspF ((T * S) • τ) = (τ : ℂ) ^ 7 * cuspFTS τ := by
  rw [cuspF, theta2_TS, eta12_TS, cuspFTS]; ring

lemma mdiff_cuspF : MDiff cuspF := by
  have h1 : MDiff (fun τ : ℍ => jacobiTheta τ ^ 2) :=
    mdiff_of_eqOn (F := fun z => jacobiTheta z ^ 2)
      (fun z hz => ((differentiableAt_jacobiTheta hz).pow 2).differentiableWithinAt) fun _ => rfl
  exact h1.mul mdiff_eta12

lemma norm_cuspFTS_le (τ : ℍ) (hτ : 1 ≤ τ.im) : ‖cuspFTS τ‖ ≤ K1 ^ 2 * (1 + 4 * Ceta) := by
  rw [cuspFTS, norm_mul]
  gcongr
  · exact norm_thetaTS2_le τ hτ
  · exact norm_eta12_le τ hτ

/-- The constant of `norm_cuspF_sub_le`. -/
def Cf : ℝ := 12 * (1 + 2 * Ceta) + 4 * Ceta

lemma norm_cuspF_sub_le (τ : ℍ) (hτ : 1 ≤ τ.im) :
    ‖cuspF τ - cexp (π * I * τ)‖ ≤ Cf * rexp (-2 * π * τ.im) := by
  set q := cexp (π * I * τ) with hq
  have hqn : ‖q‖ = rexp (-π * τ.im) := norm_q τ
  have hqq : ‖q‖ ^ 2 = rexp (-2 * π * τ.im) := by
    rw [hqn, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hq1 : ‖q‖ ≤ 1 / 2 := by rw [hqn]; linarith [exp_neg_pi_im_le_quarter hτ]
  have hη : ‖eta12 τ - q‖ ≤ 4 * Ceta * ‖q‖ ^ 2 := by
    have := norm_eta12_sub_le τ hτ
    rwa [← hqq] at this
  have hθ := norm_theta2_sub_one_le (τ := (τ : ℂ)) (by simpa using hτ)
  have hi : (τ : ℂ).im = τ.im := rfl
  rw [hi, ← hqn] at hθ
  have hCeta := Ceta_nonneg
  have hηle : ‖eta12 τ‖ ≤ (1 + 2 * Ceta) * ‖q‖ := by
    have : ‖eta12 τ‖ ≤ ‖eta12 τ - q‖ + ‖q‖ := by
      calc ‖eta12 τ‖ = ‖(eta12 τ - q) + q‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    nlinarith [norm_nonneg q, mul_nonneg hCeta (mul_nonneg (norm_nonneg q) (by linarith : 0 ≤ 1 / 2 - ‖q‖))]
  have e : cuspF τ - q = (jacobiTheta τ ^ 2 - 1) * eta12 τ + (eta12 τ - q) := by
    rw [cuspF]; ring
  rw [e]
  calc _ ≤ ‖(jacobiTheta τ ^ 2 - 1) * eta12 τ‖ + ‖eta12 τ - q‖ := norm_add_le _ _
    _ ≤ (12 * ‖q‖) * ((1 + 2 * Ceta) * ‖q‖) + 4 * Ceta * ‖q‖ ^ 2 := by
        rw [norm_mul]
        gcongr
    _ = Cf * ‖q‖ ^ 2 := by rw [Cf]; ring
    _ = _ := by rw [hqq]

/-! ### `g = κ θ¹⁴ - L_W - c f` -/

/-- `c = 28 κ - π⁷/360 + π⁷/23040`. -/
def cF : ℂ := 28 * kappa - π ^ 7 / 360 + π ^ 7 / 23040

/-- `g(τ) = κ θ(τ)¹⁴ - L_W(τ) - c f(τ)`. -/
def gfun (τ : ℍ) : ℂ := kappa * jacobiTheta τ ^ 14 - Lsum7 W τ - cF * cuspF τ

lemma gfun_S (τ : ℍ) : gfun (S • τ) = I * (τ : ℂ) ^ 7 * gfun τ := by
  rw [gfun, gfun, theta14_S, Lsum7_W_S, cuspF_S]; ring

lemma gfun_T_sq (τ : ℍ) : gfun (T ^ (2 : ℤ) • τ) = gfun τ := by
  rw [gfun, gfun, theta_T_sq, Lsum7_W_T2, cuspF_T_sq]

/-- `τ⁻⁷ g(TSτ)`. -/
def gTS (τ : ℍ) : ℂ := kappa * thetaTS14 τ - Lsum7 Wp τ - cF * cuspFTS τ

lemma gfun_TS (τ : ℍ) : gfun ((T * S) • τ) = (τ : ℂ) ^ 7 * gTS τ := by
  rw [gfun, theta14_TS, Lsum7_W_TS, cuspF_TS, gTS]; ring

lemma mdiff_gfun : MDiff gfun := by
  have hθ : MDiff (fun τ : ℍ => jacobiTheta τ) :=
    mdiff_of_eqOn (F := fun z => jacobiTheta z)
      (fun z hz => (differentiableAt_jacobiTheta hz).differentiableWithinAt) fun _ => rfl
  have h1 : MDiff (fun τ : ℍ => kappa * jacobiTheta τ ^ 14) :=
    (mdifferentiable_const).mul (hθ.pow 14)
  have h3 : MDiff (fun τ : ℍ => cF * cuspF τ) := (mdifferentiable_const).mul mdiff_cuspF
  exact (h1.sub (mdiff_Lsum7 norm_W_le)).sub h3

/-- The constant of `norm_gfun_le`. -/
def Cg : ℝ := ‖kappa‖ * (14 * 2 ^ 14 * 16 + 56) + π ^ 7 / 360 * CB + π ^ 7 / 23040 * CA +
  ‖cF‖ * Cf

lemma norm_gfun_le (τ : ℍ) (hτ : 1 ≤ τ.im) : ‖gfun τ‖ ≤ Cg * rexp (-2 * π * τ.im) := by
  set q := cexp (π * I * τ) with hq
  have hqn : ‖q‖ = rexp (-π * τ.im) := norm_q τ
  have hq2 : ‖q‖ ≤ 1 / 2 := by rw [hqn]; linarith [exp_neg_pi_im_le_quarter hτ]
  have hqq : ‖q‖ ^ 2 = rexp (-2 * π * τ.im) := by
    rw [hqn, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e : gfun τ = kappa * (jacobiTheta τ ^ 14 - 1 - 28 * q) -
      π ^ 7 / 360 * (seriesB q - q) + π ^ 7 / 23040 * (seriesA q - q) -
      cF * (cuspF τ - q) := by
    rw [gfun, Lsum7_W_eq, cF]; ring
  rw [e]
  have h1 := norm_theta14_sub_le (τ := (τ : ℂ)) (by simpa using hτ)
  have h2 := norm_seriesB_sub_le hq2
  have h2' := norm_seriesA_sub_le hq2
  have h3 := norm_cuspF_sub_le τ hτ
  have hi : (τ : ℂ).im = τ.im := rfl
  rw [hi] at h1
  rw [hqq] at h2 h2'
  have hp : ∀ c : ℝ, 0 < c → ‖(π : ℂ) ^ 7 / c‖ = π ^ 7 / c := fun c hc => by
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
      Complex.norm_real, Real.norm_of_nonneg hc.le]
  have hp1 : ‖(π : ℂ) ^ 7 / 360‖ = π ^ 7 / 360 := by exact_mod_cast hp 360 (by norm_num)
  have hp2 : ‖(π : ℂ) ^ 7 / 23040‖ = π ^ 7 / 23040 := by exact_mod_cast hp 23040 (by norm_num)
  calc _ ≤ ‖kappa * (jacobiTheta τ ^ 14 - 1 - 28 * q)‖ +
        ‖(π : ℂ) ^ 7 / 360 * (seriesB q - q)‖ + ‖(π : ℂ) ^ 7 / 23040 * (seriesA q - q)‖ +
        ‖cF * (cuspF τ - q)‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ ‖kappa‖ * ((14 * 2 ^ 14 * 16 + 56) * rexp (-2 * π * τ.im)) +
          π ^ 7 / 360 * (CB * rexp (-2 * π * τ.im)) +
          π ^ 7 / 23040 * (CA * rexp (-2 * π * τ.im)) +
          ‖cF‖ * (Cf * rexp (-2 * π * τ.im)) := by
        rw [norm_mul, norm_mul, norm_mul, norm_mul, hp1, hp2]
        gcongr
    _ = Cg * rexp (-2 * π * τ.im) := by rw [Cg]; ring

/-- The constant of `norm_gTS_le`. -/
def MTS : ℝ := ‖kappa‖ * K1 ^ 14 + ML7 + ‖cF‖ * (K1 ^ 2 * (1 + 4 * Ceta))

lemma norm_gTS_le (τ : ℍ) (hτ : 1 ≤ τ.im) (hr : |τ.re| ≤ 1) : ‖gTS τ‖ ≤ MTS := by
  rw [gTS, MTS]
  calc ‖kappa * thetaTS14 τ - Lsum7 Wp τ - cF * cuspFTS τ‖
      ≤ ‖kappa * thetaTS14 τ‖ + ‖Lsum7 Wp τ‖ + ‖cF * cuspFTS τ‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ ‖kappa‖ * K1 ^ 14 + ML7 + ‖cF‖ * (K1 ^ 2 * (1 + 4 * Ceta)) := by
        rw [norm_mul, norm_mul]
        gcongr
        · exact norm_thetaTS14_le τ hτ
        · exact norm_Lsum7_Wp_le τ hτ hr
        · exact norm_cuspFTS_le τ hτ

end NTKB.HardyWright.FourteenSquares
