/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TwentyTheta
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TwentySeriesBounds
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TwentyVanish
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.EighteenBounds

/-!
# Bounds for the proof of the `r₂₀` formula

The two cusp forms `f₁ = θ⁸ η¹²` and `f₂ = θ² C₈` (weight `10`, the laws of `θ²⁰`) and
`g(τ) = κ θ(τ)²⁰ - L_W(τ) - c₁ f₁(τ) - c₂ f₂(τ)` (`gfun`), with `a = π¹⁰/181440`,
`c₁ = (40κ + 493a)/4`, `c₂ = (120κ - 497a)/16`: the constants make the coefficients of `q¹` and `q²`
(`q = e^{πiτ}`) vanish.

* `gfun_S`, `gfun_T_sq`: `g(-1/τ) = -τ¹⁰ g(τ)`, `g(τ + 2) = g(τ)`;
* `norm_gfun_le`: `‖g(τ)‖ ≤ C e^{-3π Im τ}` for `Im τ ≥ 1`;
* `gfun_TS`, `norm_gTS_le`: `τ⁻¹⁰ g(TSτ)` is bounded on `Im τ ≥ 1`, `|Re τ| ≤ 1`.
-/

open ModularForm ModularGroup Complex Filter Topology EisensteinSeries Matrix
open scoped MatrixGroups Real UpperHalfPlane Manifold
open UpperHalfPlane hiding I

noncomputable section

namespace NTKB.HardyWright.TwentySquares

open EightSquares (K1 ne_zero' norm_jacobiTheta_sub_one_le' norm_jacobiTheta_sub_le mdiff_of_eqOn
  theta_T_sq coe_TS_smul jacobiTheta_one_add norm_jacobiTheta₂_half_le)
open SixSquares (exp_neg_pi_im_le_quarter norm_q norm_cexp_le_one_of_re one_div_neg_I_div)
open TwelveSquares (eta12 eta12_S eta12_T_sq eta12_TS mdiff_eta12 norm_eta12_le Ceta Ceta_nonneg
  hasSum_eta12 hasSum_Ceta etaTwelveCoeff_zero etaTwelveCoeff_one etaTwelveCoeff_two)
open SixteenSquares (norm_eta12_sub3_le mdiff_theta)
open EighteenSquares (oct oct_S oct_T_sq oct_TS octTS mdiff_oct norm_octTS_le MTSc8 norm_oct_sub_le Co
  Co_nonneg)

lemma norm_theta_le_two (τ : ℍ) (hτ : 1 ≤ τ.im) : ‖jacobiTheta τ‖ ≤ 2 := by
  have hw := norm_jacobiTheta_sub_one_le' (τ := (τ : ℂ)) (by simpa using hτ)
  have hq4 := exp_neg_pi_im_le_quarter hτ
  have hi : (τ : ℂ).im = τ.im := rfl
  rw [hi] at hw
  calc ‖jacobiTheta τ‖ = ‖(jacobiTheta τ - 1) + 1‖ := by ring_nf
    _ ≤ ‖jacobiTheta τ - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ ≤ 2 := by rw [norm_one]; linarith

/-! ### The cusp form `f₁ = θ⁸ η¹²` -/

/-- `f₁(τ) = θ(τ)⁸ η(τ)¹²`. -/
def cuspF (τ : ℍ) : ℂ := jacobiTheta τ ^ 8 * eta12 τ

lemma cuspF_S (τ : ℍ) : cuspF (S • τ) = -((τ : ℂ) ^ 10 * cuspF τ) := by
  rw [cuspF, cuspF, theta8_S, eta12_S]; ring

lemma cuspF_T_sq (τ : ℍ) : cuspF (T ^ (2 : ℤ) • τ) = cuspF τ := by
  rw [cuspF, cuspF, theta_T_sq, eta12_T_sq]

/-- `τ⁻¹⁰ f₁(TSτ)`. -/
def cuspFTS (τ : ℍ) : ℂ := thetaTS8 τ * eta12 τ

lemma cuspF_TS (τ : ℍ) : cuspF ((T * S) • τ) = (τ : ℂ) ^ 10 * cuspFTS τ := by
  rw [cuspF, theta8_TS, eta12_TS, cuspFTS]; ring

lemma mdiff_cuspF : MDiff cuspF := (mdiff_theta.pow 8).mul mdiff_eta12

lemma norm_cuspFTS_le (τ : ℍ) (hτ : 1 ≤ τ.im) : ‖cuspFTS τ‖ ≤ K1 ^ 8 * (1 + 4 * Ceta) := by
  rw [cuspFTS, norm_mul]
  gcongr
  · exact norm_thetaTS8_le τ hτ
  · exact norm_eta12_le τ hτ

/-- The constant of `norm_cuspF_sub_le`. -/
def Cf : ℝ := 256 * (8 * Ceta) + 32770

lemma norm_cuspF_sub_le (τ : ℍ) (hτ : 1 ≤ τ.im) :
    ‖cuspF τ - cexp (π * I * τ) - 16 * cexp (π * I * τ) ^ 2‖ ≤ Cf * ‖cexp (π * I * τ)‖ ^ 3 := by
  set q := cexp (π * I * τ) with hq
  have hqn : ‖q‖ = rexp (-π * τ.im) := norm_q τ
  have ht0 := norm_nonneg q
  have hRb := norm_eta12_sub3_le τ hτ
  have hRa := norm_theta8_sub_le (τ := (τ : ℂ)) (by simpa using hτ)
  have hθ := norm_theta_le_two τ hτ
  have hA : ‖jacobiTheta τ ^ 8‖ ≤ 256 := by
    rw [norm_pow]
    calc ‖jacobiTheta τ‖ ^ 8 ≤ 2 ^ 8 := pow_le_pow_left₀ (norm_nonneg _) hθ 8
      _ = 256 := by norm_num
  have hCeta := Ceta_nonneg
  have e : cuspF τ - q - 16 * q ^ 2 = (eta12 τ - q) * jacobiTheta τ ^ 8 +
      q * (jacobiTheta τ ^ 8 - 1 - 16 * q) := by
    rw [cuspF]; ring
  rw [e]
  calc _ ≤ ‖(eta12 τ - q) * jacobiTheta τ ^ 8‖ + ‖q * (jacobiTheta τ ^ 8 - 1 - 16 * q)‖ :=
        norm_add_le _ _
    _ ≤ (8 * Ceta * ‖q‖ ^ 3) * 256 + ‖q‖ * (32770 * ‖q‖ ^ 2) := by
        rw [norm_mul, norm_mul]
        gcongr
    _ ≤ Cf * ‖q‖ ^ 3 := by
        have : 0 ≤ ‖q‖ ^ 3 := by positivity
        rw [Cf]; nlinarith

/-! ### The cusp form `f₂ = θ² C₈` -/

/-- `f₂(τ) = θ(τ)² C₈(τ)`. -/
def cuspG (τ : ℍ) : ℂ := jacobiTheta τ ^ 2 * oct τ

lemma cuspG_S (τ : ℍ) : cuspG (S • τ) = -((τ : ℂ) ^ 10 * cuspG τ) := by
  rw [cuspG, cuspG, theta2_S, oct_S]
  linear_combination ((τ : ℂ) ^ 10 * jacobiTheta τ ^ 2 * oct τ) * I_sq

lemma cuspG_T_sq (τ : ℍ) : cuspG (T ^ (2 : ℤ) • τ) = cuspG τ := by
  rw [cuspG, cuspG, theta_T_sq, oct_T_sq]

/-- `τ⁻¹⁰ f₂(TSτ)`. -/
def cuspGTS (τ : ℍ) : ℂ := thetaTS2 τ * octTS τ

lemma cuspG_TS (τ : ℍ) : cuspG ((T * S) • τ) = (τ : ℂ) ^ 10 * cuspGTS τ := by
  rw [cuspG, theta2_TS, oct_TS, cuspGTS]; ring

lemma mdiff_cuspG : MDiff cuspG := (mdiff_theta.pow 2).mul mdiff_oct

lemma norm_cuspGTS_le (τ : ℍ) (hτ : 1 ≤ τ.im) : ‖cuspGTS τ‖ ≤ K1 ^ 2 * MTSc8 := by
  rw [cuspGTS, norm_mul]
  gcongr
  · exact norm_thetaTS2_le τ hτ
  · exact norm_octTS_le τ hτ

/-- The constant of `norm_cuspG_sub_le`. -/
def Cg2 : ℝ := 4 * (8 * Co) + 130 * 36 + 256

lemma norm_cuspG_sub_le (τ : ℍ) (hτ : 1 ≤ τ.im) :
    ‖cuspG τ - 4 * cexp (π * I * τ) - 80 * cexp (π * I * τ) ^ 2‖ ≤ Cg2 * ‖cexp (π * I * τ)‖ ^ 3 := by
  set q := cexp (π * I * τ) with hq
  have hqn : ‖q‖ = rexp (-π * τ.im) := norm_q τ
  have ht : ‖q‖ ≤ 1 / 4 := by rw [hqn]; exact exp_neg_pi_im_le_quarter hτ
  have ht0 := norm_nonneg q
  have hO := norm_oct_sub_le τ hτ
  have h2 := norm_theta2_sub_le (τ := (τ : ℂ)) (by simpa using hτ)
  rw [← hq] at hO h2
  have hθ := norm_theta_le_two τ hτ
  have hA : ‖jacobiTheta τ ^ 2‖ ≤ 4 := by
    rw [norm_pow]
    calc ‖jacobiTheta τ‖ ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hθ 2
      _ = 4 := by norm_num
  have hP : ‖4 * q + 64 * q ^ 2‖ ≤ 36 * ‖q‖ := by
    calc ‖4 * q + 64 * q ^ 2‖ ≤ ‖4 * q‖ + ‖64 * q ^ 2‖ := norm_add_le _ _
      _ = 4 * ‖q‖ + 64 * ‖q‖ ^ 2 := by
          rw [norm_mul, norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_ofNat]
      _ ≤ 36 * ‖q‖ := by nlinarith
  have hCo := Co_nonneg
  have hA2 : ‖jacobiTheta τ‖ ^ 2 ≤ 4 := by rwa [norm_pow] at hA
  have e : cuspG τ - 4 * q - 80 * q ^ 2 = jacobiTheta τ ^ 2 * (oct τ - 4 * q - 64 * q ^ 2) +
      (jacobiTheta τ ^ 2 - 1 - 4 * q) * (4 * q + 64 * q ^ 2) + 256 * q ^ 3 := by
    rw [cuspG]; ring
  rw [e]
  calc _ ≤ ‖jacobiTheta τ ^ 2 * (oct τ - 4 * q - 64 * q ^ 2)‖ +
        ‖(jacobiTheta τ ^ 2 - 1 - 4 * q) * (4 * q + 64 * q ^ 2)‖ + ‖256 * q ^ 3‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ 4 * (8 * Co * ‖q‖ ^ 3) + (130 * ‖q‖ ^ 2) * (36 * ‖q‖) + 256 * ‖q‖ ^ 3 := by
        simp only [norm_mul, norm_pow, Complex.norm_ofNat]
        gcongr
    _ = Cg2 * ‖q‖ ^ 3 := by rw [Cg2]; ring

/-! ### `g = κ θ²⁰ - L_W - c₁ f₁ - c₂ f₂` -/

/-- `a = π¹⁰/181440`, the coefficient of `O - E` in `L_W`. -/
def aE : ℂ := π ^ 10 / 181440

/-- `c₁ = (40κ + 493a)/4`. -/
def c1 : ℂ := (40 * kappa + 493 * aE) / 4

/-- `c₂ = (120κ - 497a)/16`. -/
def c2 : ℂ := (120 * kappa - 497 * aE) / 16

/-- `g(τ) = κ θ(τ)²⁰ - L_W(τ) - c₁ f₁(τ) - c₂ f₂(τ)`. -/
def gfun (τ : ℍ) : ℂ := kappa * jacobiTheta τ ^ 20 - Lsum10 W τ - c1 * cuspF τ - c2 * cuspG τ

lemma gfun_S (τ : ℍ) : gfun (S • τ) = -((τ : ℂ) ^ 10 * gfun τ) := by
  rw [gfun, gfun, theta20_S, Lsum10_W_S, cuspF_S, cuspG_S]; ring

lemma gfun_T_sq (τ : ℍ) : gfun (T ^ (2 : ℤ) • τ) = gfun τ := by
  rw [gfun, gfun, theta_T_sq, Lsum10_W_T2, cuspF_T_sq, cuspG_T_sq]

/-- `τ⁻¹⁰ g(TSτ)`. -/
def gTS (τ : ℍ) : ℂ := kappa * thetaTS20 τ - Lsum10 Wp τ - c1 * cuspFTS τ - c2 * cuspGTS τ

lemma gfun_TS (τ : ℍ) : gfun ((T * S) • τ) = (τ : ℂ) ^ 10 * gTS τ := by
  rw [gfun, theta20_TS, Lsum10_W_TS, cuspF_TS, cuspG_TS, gTS]; ring

lemma mdiff_gfun : MDiff gfun := by
  have h1 : MDiff (fun τ : ℍ => kappa * jacobiTheta τ ^ 20) := fun τ =>
    (mdifferentiableAt_const (c := kappa)).mul ((mdiff_theta.pow 20) τ)
  have h3 : MDiff (fun τ : ℍ => c1 * cuspF τ) := fun τ =>
    (mdifferentiableAt_const (c := c1)).mul (mdiff_cuspF τ)
  have h4 : MDiff (fun τ : ℍ => c2 * cuspG τ) := fun τ =>
    (mdifferentiableAt_const (c := c2)).mul (mdiff_cuspG τ)
  exact ((h1.sub (mdiff_Lsum10 norm_W_le)).sub h3).sub h4

lemma norm_aE : ‖aE‖ = π ^ 10 / 181440 := by
  rw [aE, norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  norm_num

/-- The constant of `norm_gfun_le`. -/
def Cg : ℝ := ‖kappa‖ * (400 * 1048576 * 64 + 250) + π ^ 10 / 181440 * CL3 + ‖c1‖ * Cf + ‖c2‖ * Cg2

lemma norm_gfun_le (τ : ℍ) (hτ : 1 ≤ τ.im) : ‖gfun τ‖ ≤ Cg * rexp (-3 * π * τ.im) := by
  set q := cexp (π * I * τ) with hq
  have hqn : ‖q‖ = rexp (-π * τ.im) := norm_q τ
  have hq2 : ‖q‖ ≤ 1 / 2 := by rw [hqn]; linarith [exp_neg_pi_im_le_quarter hτ]
  have hqq : ‖q‖ ^ 3 = rexp (-3 * π * τ.im) := by
    rw [hqn, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e : gfun τ = kappa * (jacobiTheta τ ^ 20 - 1 - 40 * q - 760 * q ^ 2) -
      aE * (seriesO q - seriesE q - q - 513 * q ^ 2) -
      c1 * (cuspF τ - q - 16 * q ^ 2) - c2 * (cuspG τ - 4 * q - 80 * q ^ 2) := by
    rw [gfun, Lsum10_W_eq, c1, c2, aE]; ring
  rw [e]
  have h1 := norm_theta20_sub_le (τ := (τ : ℂ)) (by simpa using hτ)
  have h2 := norm_seriesOE_sub3_le hq2
  have h3 := norm_cuspF_sub_le τ hτ
  have h4 := norm_cuspG_sub_le τ hτ
  rw [← hq] at h1 h3 h4
  rw [hqq] at h1 h2 h3 h4
  calc _ ≤ ‖kappa * (jacobiTheta τ ^ 20 - 1 - 40 * q - 760 * q ^ 2)‖ +
        ‖aE * (seriesO q - seriesE q - q - 513 * q ^ 2)‖ +
        ‖c1 * (cuspF τ - q - 16 * q ^ 2)‖ + ‖c2 * (cuspG τ - 4 * q - 80 * q ^ 2)‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ ‖kappa‖ * ((400 * 1048576 * 64 + 250) * rexp (-3 * π * τ.im)) +
          π ^ 10 / 181440 * (CL3 * rexp (-3 * π * τ.im)) +
          ‖c1‖ * (Cf * rexp (-3 * π * τ.im)) + ‖c2‖ * (Cg2 * rexp (-3 * π * τ.im)) := by
        rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_aE]
        gcongr
    _ = Cg * rexp (-3 * π * τ.im) := by rw [Cg]; ring

/-- The constant of `norm_gTS_le`. -/
def MTS : ℝ := ‖kappa‖ * K1 ^ 20 + ML10 + ‖c1‖ * (K1 ^ 8 * (1 + 4 * Ceta)) + ‖c2‖ * (K1 ^ 2 * MTSc8)

lemma norm_gTS_le (τ : ℍ) (hτ : 1 ≤ τ.im) (hr : |τ.re| ≤ 1) : ‖gTS τ‖ ≤ MTS := by
  rw [gTS, MTS]
  calc ‖kappa * thetaTS20 τ - Lsum10 Wp τ - c1 * cuspFTS τ - c2 * cuspGTS τ‖
      ≤ ‖kappa * thetaTS20 τ‖ + ‖Lsum10 Wp τ‖ + ‖c1 * cuspFTS τ‖ + ‖c2 * cuspGTS τ‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ ‖kappa‖ * K1 ^ 20 + ML10 + ‖c1‖ * (K1 ^ 8 * (1 + 4 * Ceta)) + ‖c2‖ * (K1 ^ 2 * MTSc8) := by
        rw [norm_mul, norm_mul, norm_mul]
        gcongr
        · exact norm_thetaTS20_le τ hτ
        · exact norm_Lsum10_Wp_le τ hτ hr
        · exact norm_cuspFTS_le τ hτ
        · exact norm_cuspGTS_le τ hτ

end NTKB.HardyWright.TwentySquares
