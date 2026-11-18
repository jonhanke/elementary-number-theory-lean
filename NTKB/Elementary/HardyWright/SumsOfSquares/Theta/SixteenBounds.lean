/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.SixteenTheta
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.SixteenKappa

/-!
# Bounds for the proof of the `r₁₆` formula

The cusp form `f = θ⁴ η¹²` (weight `8`, the laws of `θ¹⁶`) and
`g(τ) = κ θ(τ)¹⁶ - L_W(τ) - c f(τ)` with `κ = 17 π⁸/80640` and `c = 32 κ - π⁸/2520` (`gfun`): the
constants make the coefficients of `q⁰`, `q¹` and `q²` (`q = e^{πiτ}`) vanish.

* `gfun_S`, `gfun_T_sq`: `g(-1/τ) = τ⁸ g(τ)`, `g(τ + 2) = g(τ)`;
* `norm_gfun_le`: `‖g(τ)‖ ≤ C e^{-3π Im τ}` for `Im τ ≥ 1`;
* `gfun_TS`, `norm_gTS_le`: `τ⁻⁸ g(TSτ)` is bounded on `Im τ ≥ 1`, `|Re τ| ≤ 1`.
-/

open ModularForm ModularGroup Complex Filter Topology EisensteinSeries Matrix
open scoped MatrixGroups Real UpperHalfPlane Manifold
open UpperHalfPlane hiding I

noncomputable section

namespace NTKB.HardyWright.SixteenSquares

open EightSquares (K1 ne_zero' norm_jacobiTheta_sub_one_le' norm_jacobiTheta_sub_le mdiff_of_eqOn
  theta_T_sq coe_TS_smul jacobiTheta_one_add norm_jacobiTheta₂_half_le)
open SixSquares (exp_neg_pi_im_le_quarter norm_q norm_cexp_le_one_of_re one_div_neg_I_div)
open TwelveSquares (eta12 eta12_S eta12_T_sq eta12_TS mdiff_eta12 norm_eta12_le Ceta Ceta_nonneg
  hasSum_eta12 hasSum_Ceta etaTwelveCoeff_zero etaTwelveCoeff_one etaTwelveCoeff_two)

/-! ### `η¹² = q + O(q³)` -/

/-- A power series with `c₀ = 0`, `c₁ = 1`, `c₂ = 0` is `q + O(q³)`. -/
lemma norm_sub_of_hasSum3 {c : ℕ → ℂ} {F q : ℂ} (hF : HasSum (fun n => c n * q ^ n) F)
    (h0 : c 0 = 0) (h1 : c 1 = 1) (h2 : c 2 = 0) (hq : ‖q‖ ≤ 1 / 2) {M : ℝ}
    (hM : HasSum (fun n => ‖c n‖ * (1 / 2) ^ n) M) : ‖F - q‖ ≤ 8 * M * ‖q‖ ^ 3 := by
  have h3 : HasSum (fun n => c (n + 3) * q ^ (n + 3)) (F - q) := by
    have := (hasSum_nat_add_iff' (f := fun n => c n * q ^ n) 3).mpr hF
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, h2] at this
    simpa using this
  have hM3 : HasSum (fun n => ‖c (n + 3)‖ * (1 / 2) ^ (n + 3))
      (M - (‖c 0‖ * (1 / 2) ^ 0 + ‖c 1‖ * (1 / 2) ^ 1 + ‖c 2‖ * (1 / 2) ^ 2)) := by
    have := (hasSum_nat_add_iff' (f := fun n => ‖c n‖ * (1 / 2 : ℝ) ^ n) 3).mpr hM
    simpa [Finset.sum_range_succ] using this
  have hMle : M - (‖c 0‖ * (1 / 2 : ℝ) ^ 0 + ‖c 1‖ * (1 / 2) ^ 1 + ‖c 2‖ * (1 / 2) ^ 2) ≤ M := by
    have : 0 ≤ ‖c 0‖ * (1 / 2 : ℝ) ^ 0 + ‖c 1‖ * (1 / 2) ^ 1 + ‖c 2‖ * (1 / 2) ^ 2 := by positivity
    linarith
  have hb : ∀ n, ‖c (n + 3) * q ^ (n + 3)‖ ≤ 8 * ‖q‖ ^ 3 * (‖c (n + 3)‖ * (1 / 2) ^ (n + 3)) := by
    intro n
    rw [norm_mul, norm_pow, pow_add, pow_add]
    have : ‖q‖ ^ n ≤ (1 / 2) ^ n := pow_le_pow_left₀ (norm_nonneg _) hq n
    calc ‖c (n + 3)‖ * (‖q‖ ^ n * ‖q‖ ^ 3) ≤ ‖c (n + 3)‖ * ((1 / 2) ^ n * ‖q‖ ^ 3) := by gcongr
      _ = 8 * ‖q‖ ^ 3 * (‖c (n + 3)‖ * ((1 / 2) ^ n * (1 / 2) ^ 3)) := by ring
  have ht := tsum_of_norm_bounded (hM3.mul_left (8 * ‖q‖ ^ 3)) hb
  rw [h3.tsum_eq] at ht
  have := mul_le_mul_of_nonneg_left hMle (by positivity : (0 : ℝ) ≤ 8 * ‖q‖ ^ 3)
  linarith

lemma norm_eta12_sub3_le (τ : ℍ) (hτ : 1 ≤ τ.im) :
    ‖eta12 τ - cexp (π * I * τ)‖ ≤ 8 * Ceta * ‖cexp (π * I * τ)‖ ^ 3 := by
  have hq : ‖cexp (π * I * τ)‖ ≤ 1 / 2 := by
    rw [norm_q]; linarith [exp_neg_pi_im_le_quarter hτ]
  exact norm_sub_of_hasSum3 (hasSum_eta12 τ) (by simp [etaTwelveCoeff_zero])
    (by simp [etaTwelveCoeff_one]) (by simp [etaTwelveCoeff_two]) hq hasSum_Ceta

/-! ### The cusp form `f = θ⁴ η¹²` -/

/-- `f(τ) = θ(τ)⁴ η(τ)¹²`. -/
def cuspF (τ : ℍ) : ℂ := jacobiTheta τ ^ 4 * eta12 τ

lemma cuspF_S (τ : ℍ) : cuspF (S • τ) = (τ : ℂ) ^ 8 * cuspF τ := by
  rw [cuspF, cuspF, theta4_S, eta12_S]; ring

lemma cuspF_T_sq (τ : ℍ) : cuspF (T ^ (2 : ℤ) • τ) = cuspF τ := by
  rw [cuspF, cuspF, theta_T_sq, eta12_T_sq]

/-- `τ⁻⁸ f(TSτ)`. -/
def cuspFTS (τ : ℍ) : ℂ := thetaTS4 τ * eta12 τ

lemma cuspF_TS (τ : ℍ) : cuspF ((T * S) • τ) = (τ : ℂ) ^ 8 * cuspFTS τ := by
  rw [cuspF, theta4_TS, eta12_TS, cuspFTS]; ring

lemma mdiff_theta : MDiff (fun τ : ℍ => jacobiTheta τ) :=
  mdiff_of_eqOn (F := fun z => jacobiTheta z)
    (fun z hz => (differentiableAt_jacobiTheta hz).differentiableWithinAt) fun _ => rfl

lemma mdiff_cuspF : MDiff cuspF := (mdiff_theta.pow 4).mul mdiff_eta12

lemma norm_cuspFTS_le (τ : ℍ) (hτ : 1 ≤ τ.im) : ‖cuspFTS τ‖ ≤ K1 ^ 4 * (1 + 4 * Ceta) := by
  rw [cuspFTS, norm_mul]
  gcongr
  · exact norm_thetaTS4_le τ hτ
  · exact norm_eta12_le τ hτ

/-- The constant of `norm_cuspF_sub_le`. -/
def Cf : ℝ := 16 * (8 * Ceta) + 1040

lemma norm_cuspF_sub_le (τ : ℍ) (hτ : 1 ≤ τ.im) :
    ‖cuspF τ - cexp (π * I * τ) - 8 * cexp (π * I * τ) ^ 2‖ ≤ Cf * ‖cexp (π * I * τ)‖ ^ 3 := by
  set q := cexp (π * I * τ) with hq
  have hqn : ‖q‖ = rexp (-π * τ.im) := norm_q τ
  have ht : ‖q‖ ≤ 1 / 4 := by rw [hqn]; exact exp_neg_pi_im_le_quarter hτ
  have ht0 := norm_nonneg q
  have hRb := norm_eta12_sub3_le τ hτ
  have hRa := norm_theta4_sub_le (τ := (τ : ℂ)) (by simpa using hτ)
  have hw := norm_jacobiTheta_sub_one_le' (τ := (τ : ℂ)) (by simpa using hτ)
  have hi : (τ : ℂ).im = τ.im := rfl
  rw [hi, ← hqn] at hw
  have hθ : ‖jacobiTheta τ‖ ≤ 2 := by
    calc ‖jacobiTheta τ‖ = ‖(jacobiTheta τ - 1) + 1‖ := by ring_nf
      _ ≤ ‖jacobiTheta τ - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 2 := by rw [norm_one]; linarith
  have hA : ‖jacobiTheta τ ^ 4‖ ≤ 16 := by
    rw [norm_pow]
    calc ‖jacobiTheta τ‖ ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hθ 4
      _ = 16 := by norm_num
  have hCeta := Ceta_nonneg
  have e : cuspF τ - q - 8 * q ^ 2 = (eta12 τ - q) * jacobiTheta τ ^ 4 +
      q * (jacobiTheta τ ^ 4 - 1 - 8 * q) := by
    rw [cuspF]; ring
  rw [e]
  calc _ ≤ ‖(eta12 τ - q) * jacobiTheta τ ^ 4‖ + ‖q * (jacobiTheta τ ^ 4 - 1 - 8 * q)‖ :=
        norm_add_le _ _
    _ ≤ (8 * Ceta * ‖q‖ ^ 3) * 16 + ‖q‖ * (1040 * ‖q‖ ^ 2) := by
        rw [norm_mul, norm_mul]
        gcongr
    _ ≤ Cf * ‖q‖ ^ 3 := by
        have : 0 ≤ ‖q‖ ^ 3 := by positivity
        rw [Cf]; nlinarith

/-! ### `g = κ θ¹⁶ - L_W - c f` -/

lemma kappa_eq : kappa = ((17 * Real.pi ^ 8 / 80640 : ℝ) : ℂ) := by
  rw [← kappaSixteenR_eq, kappa, kappaSixteenR, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  by_cases h : Even n <;> simp [h]

/-- `c = 32 κ - π⁸/2520`. -/
def cG : ℂ := 32 * kappa - π ^ 8 / 2520

/-- `g(τ) = κ θ(τ)¹⁶ - L_W(τ) - c f(τ)`. -/
def gfun (τ : ℍ) : ℂ := kappa * jacobiTheta τ ^ 16 - Lsum8 W τ - cG * cuspF τ

lemma gfun_S (τ : ℍ) : gfun (S • τ) = (τ : ℂ) ^ 8 * gfun τ := by
  rw [gfun, gfun, theta16_S, Lsum8_W_S, cuspF_S]; ring

lemma gfun_T_sq (τ : ℍ) : gfun (T ^ (2 : ℤ) • τ) = gfun τ := by
  rw [gfun, gfun, theta_T_sq, Lsum8_W_T2, cuspF_T_sq]

/-- `τ⁻⁸ g(TSτ)`. -/
def gTS (τ : ℍ) : ℂ := kappa * thetaTS16 τ - Lsum8 Wp τ - cG * cuspFTS τ

lemma gfun_TS (τ : ℍ) : gfun ((T * S) • τ) = (τ : ℂ) ^ 8 * gTS τ := by
  rw [gfun, theta16_TS, Lsum8_W_TS, cuspF_TS, gTS]; ring

lemma mdiff_gfun : MDiff gfun := by
  have h1 : MDiff (fun τ : ℍ => kappa * jacobiTheta τ ^ 16) :=
    (mdifferentiable_const).mul (mdiff_theta.pow 16)
  have h3 : MDiff (fun τ : ℍ => cG * cuspF τ) := (mdifferentiable_const).mul mdiff_cuspF
  exact (h1.sub (mdiff_Lsum8 norm_W_le)).sub h3

/-- The constant of `norm_gfun_le`. -/
def Cg : ℝ := ‖kappa‖ * (256 * 65536 * 64 + 200) + π ^ 8 / 2520 * CL3 + ‖cG‖ * Cf

lemma norm_gfun_le (τ : ℍ) (hτ : 1 ≤ τ.im) : ‖gfun τ‖ ≤ Cg * rexp (-3 * π * τ.im) := by
  set q := cexp (π * I * τ) with hq
  have hqn : ‖q‖ = rexp (-π * τ.im) := norm_q τ
  have hq2 : ‖q‖ ≤ 1 / 2 := by rw [hqn]; linarith [exp_neg_pi_im_le_quarter hτ]
  have hqq : ‖q‖ ^ 3 = rexp (-3 * π * τ.im) := by
    rw [hqn, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hk := kappa_eq
  have e : gfun τ = kappa * (jacobiTheta τ ^ 16 - 1 - 32 * q - 480 * q ^ 2) -
      π ^ 8 / 2520 * (seriesO q + seriesE q - q - 127 * q ^ 2) -
      cG * (cuspF τ - q - 8 * q ^ 2) := by
    rw [gfun, Lsum8_W_eq, cG]
    have : kappa = ((17 * Real.pi ^ 8 / 80640 : ℝ) : ℂ) := hk
    push_cast at this
    linear_combination (224 * q ^ 2) * this
  rw [e]
  have h1 := norm_theta16_sub_le (τ := (τ : ℂ)) (by simpa using hτ)
  have h2 := norm_seriesOE_sub3_le hq2
  have h3 := norm_cuspF_sub_le τ hτ
  have hp : ‖(π : ℂ) ^ 8 / 2520‖ = π ^ 8 / 2520 := by
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    norm_num
  rw [← hqq]
  calc _ ≤ ‖kappa * (jacobiTheta τ ^ 16 - 1 - 32 * q - 480 * q ^ 2)‖ +
        ‖(π : ℂ) ^ 8 / 2520 * (seriesO q + seriesE q - q - 127 * q ^ 2)‖ +
        ‖cG * (cuspF τ - q - 8 * q ^ 2)‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ ‖kappa‖ * ((256 * 65536 * 64 + 200) * ‖q‖ ^ 3) +
          π ^ 8 / 2520 * (CL3 * ‖q‖ ^ 3) + ‖cG‖ * (Cf * ‖q‖ ^ 3) := by
        rw [norm_mul, norm_mul, norm_mul, hp]
        gcongr
    _ = Cg * ‖q‖ ^ 3 := by rw [Cg]; ring

/-- The bound for `L_{W'}` on the strip `|Re τ| ≤ 1`, `Im τ ≥ 1`. -/
def ML8 : ℝ := ∑' v : Fin 2 → ℤ, r ⟨⟨1, 1⟩, one_pos⟩ ^ (-(8 : ℝ)) * ‖v‖ ^ (-(8 : ℝ))

lemma norm_Lsum8_Wp_le (τ : ℍ) (hτ : 1 ≤ τ.im) (hr : |τ.re| ≤ 1) : ‖Lsum8 Wp τ‖ ≤ ML8 := by
  have hs := (summable_one_div_norm_rpow (k := 8) (by norm_num)).mul_left
    (r ⟨⟨1, 1⟩, one_pos⟩ ^ (-(8 : ℝ)))
  refine tsum_of_norm_bounded hs.hasSum fun v => ?_
  rw [norm_mul]
  have hmem : τ ∈ verticalStrip 1 1 := ⟨hr, hτ⟩
  have hb := summand_bound_of_mem_verticalStrip (k := 8) (by norm_num) v one_pos hmem
  have he : ‖eisSummand 8 v τ‖ ≤ r ⟨⟨1, 1⟩, one_pos⟩ ^ (-(8 : ℝ)) * ‖v‖ ^ (-(8 : ℝ)) := by
    simp only [eisSummand, norm_zpow]
    exact_mod_cast hb
  calc ‖Wp v‖ * ‖eisSummand 8 v τ‖ ≤ 1 * (r ⟨⟨1, 1⟩, one_pos⟩ ^ (-(8 : ℝ)) * ‖v‖ ^ (-(8 : ℝ))) :=
        mul_le_mul (norm_Wp_le v) he (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _

/-- The constant of `norm_gTS_le`. -/
def MTS : ℝ := ‖kappa‖ * K1 ^ 16 + ML8 + ‖cG‖ * (K1 ^ 4 * (1 + 4 * Ceta))

lemma norm_gTS_le (τ : ℍ) (hτ : 1 ≤ τ.im) (hr : |τ.re| ≤ 1) : ‖gTS τ‖ ≤ MTS := by
  rw [gTS, MTS]
  calc ‖kappa * thetaTS16 τ - Lsum8 Wp τ - cG * cuspFTS τ‖
      ≤ ‖kappa * thetaTS16 τ‖ + ‖Lsum8 Wp τ‖ + ‖cG * cuspFTS τ‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ ‖kappa‖ * K1 ^ 16 + ML8 + ‖cG‖ * (K1 ^ 4 * (1 + 4 * Ceta)) := by
        rw [norm_mul, norm_mul]
        gcongr
        · exact norm_thetaTS16_le τ hτ
        · exact norm_Lsum8_Wp_le τ hτ hr
        · exact norm_cuspFTS_le τ hτ

end NTKB.HardyWright.SixteenSquares
