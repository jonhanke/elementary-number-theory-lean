/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.SixExpansion

/-!
# Bounds for the proof of Jacobi's `r₆` formula

`g(τ) = κ θ(τ)⁶ - L_W(τ)` (`gfun`).

* `gfun_S`, `gfun_T_sq`: `g(-1/τ) = i τ³ g(τ)`, `g(τ + 2) = g(τ)`;
* `norm_gfun_le`: `‖g(τ)‖ ≤ C e^{-π Im τ}` for `Im τ ≥ 1` (from `θ = 1 + O(e^{-π Im τ})` and the
  expansion `L_W = κ + π³ B(q) - (π³/4) A(q)` of `SixExpansion.lean`);
* `gfun_TS`, `norm_gfun_TS_le`: `τ⁻³ g(TSτ) = κ i e^{3πiτ/2} θ₂(-τ/2, τ)⁶ - L_{W'}(τ)` is bounded
  on `Im τ ≥ 1`, `|Re τ| ≤ 1`.
-/

open ModularForm ModularGroup Complex Filter Topology EisensteinSeries Matrix
open scoped MatrixGroups Real UpperHalfPlane Manifold
open UpperHalfPlane hiding I

noncomputable section

namespace NTKB.HardyWright.SixSquares

open EightSquares (coe_TS_smul jacobiTheta_one_add norm_jacobiTheta₂_half_le K1 ne_zero'
  exp_neg_pi_le_half norm_jacobiTheta_sub_one_le' mdiff_of_eqOn theta_T_sq)

/-! ### `θ⁶` under `S` and `TS` -/

lemma cpow_half_pow_six (z : ℂ) : (z ^ (1 / 2 : ℂ)) ^ 6 = z ^ 3 := by
  have h := cpow_ofNat_inv_pow z 2
  rw [one_div, show (6 : ℕ) = 2 * 3 from rfl, pow_mul, h]

lemma theta6_S (τ : ℍ) : jacobiTheta ↑(S • τ) ^ 6 = I * (τ : ℂ) ^ 3 * jacobiTheta τ ^ 6 := by
  rw [jacobiTheta_S_smul, mul_pow, cpow_half_pow_six]
  have : (-I * (τ : ℂ)) ^ 3 = I * (τ : ℂ) ^ 3 := by
    linear_combination (-I * (τ : ℂ) ^ 3) * I_sq
  rw [this]

lemma one_div_neg_I_div (w : ℂ) : 1 / (-I / w) = I * w := by
  rw [one_div_div, div_eq_iff (neg_ne_zero.mpr I_ne_zero)]
  linear_combination w * I_sq

/-- `θ((τ-1)/τ)⁶ = τ³ · i e^{3πiτ/2} θ₂(-τ/2, τ)⁶`. -/
lemma theta6_TS (τ : ℍ) : jacobiTheta (((T * S) • τ : ℍ) : ℂ) ^ 6 =
    (τ : ℂ) ^ 3 * (I * (cexp (3 * π * I * τ / 2) * jacobiTheta₂ (-(τ : ℂ) / 2) τ ^ 6)) := by
  have h0 := ne_zero' τ
  rw [coe_TS_smul, show ((τ : ℂ) - 1) / τ = 1 + (-1 / τ) by field_simp; ring, jacobiTheta_one_add,
    jacobiTheta₂_functional_equation]
  have e1' : -I * (-1 / (τ : ℂ)) = I / τ := by field_simp
  have e2 : -π * I * (1 / 2 : ℂ) ^ 2 / (-1 / (τ : ℂ)) = π * I * τ / 4 := by field_simp; ring
  have e3 : (1 / 2 : ℂ) / (-1 / (τ : ℂ)) = -(τ : ℂ) / 2 := by field_simp
  have e4 : -1 / (-1 / (τ : ℂ)) = τ := by field_simp
  rw [e1', e2, e3, e4, mul_pow, mul_pow, div_pow, cpow_half_pow_six, one_pow,
    ← Complex.exp_nat_mul]
  have hI : (I / (τ : ℂ)) ^ 3 = -I / (τ : ℂ) ^ 3 := by
    rw [div_pow, I_pow_three]
  rw [hI, one_div_neg_I_div]
  have : ((6 : ℕ) : ℂ) * (π * I * τ / 4) = 3 * π * I * τ / 2 := by push_cast; ring
  rw [this]
  ring

lemma norm_cexp_le_one_of_re {w : ℂ} (hw : w.re ≤ 0) : ‖cexp w‖ ≤ 1 := by
  rw [Complex.norm_exp, Real.exp_le_one_iff]; exact hw

lemma norm_theta6_TS_part_le (τ : ℍ) (hτ : 1 ≤ τ.im) :
    ‖I * (cexp (3 * π * I * τ / 2) * jacobiTheta₂ (-(τ : ℂ) / 2) τ ^ 6)‖ ≤ K1 ^ 6 := by
  have hJ := norm_jacobiTheta₂_half_le τ hτ
  have he : ‖cexp (3 * π * I * τ / 2)‖ ≤ 1 := by
    apply norm_cexp_le_one_of_re
    have : (3 * π * I * (τ : ℂ) / 2).re = -(3 * π * τ.im / 2) := by
      simp [Complex.mul_re, Complex.mul_im]; ring
    rw [this]; have := τ.im_pos; nlinarith [Real.pi_pos]
  rw [norm_mul, Complex.norm_I, one_mul, norm_mul, norm_pow]
  calc ‖cexp (3 * π * I * τ / 2)‖ * ‖jacobiTheta₂ (-(τ : ℂ) / 2) τ‖ ^ 6 ≤ 1 * K1 ^ 6 := by
        gcongr
    _ = K1 ^ 6 := one_mul _

/-! ### `θ⁶ - 1` -/

lemma norm_one_add_pow_six_sub_le {w : ℂ} (hw : ‖w‖ ≤ 1) : ‖(1 + w) ^ 6 - 1‖ ≤ 63 * ‖w‖ := by
  have e : (1 + w) ^ 6 - 1 = w * (6 + 15 * w + 20 * w ^ 2 + 15 * w ^ 3 + 6 * w ^ 4 + w ^ 5) := by
    ring
  rw [e, norm_mul, mul_comm]
  gcongr
  have h0 := norm_nonneg w
  have hp : ∀ k : ℕ, ‖w ^ k‖ ≤ 1 := fun k => by rw [norm_pow]; exact pow_le_one₀ h0 hw
  calc ‖(6 : ℂ) + 15 * w + 20 * w ^ 2 + 15 * w ^ 3 + 6 * w ^ 4 + w ^ 5‖
      ≤ ‖(6 : ℂ)‖ + ‖15 * w‖ + ‖20 * w ^ 2‖ + ‖15 * w ^ 3‖ + ‖6 * w ^ 4‖ + ‖w ^ 5‖ := by
        refine (norm_add_le _ _).trans ?_; gcongr
        refine (norm_add_le _ _).trans ?_; gcongr
        refine (norm_add_le _ _).trans ?_; gcongr
        refine (norm_add_le _ _).trans ?_; gcongr
        exact norm_add_le _ _
    _ ≤ 6 + 15 + 20 + 15 + 6 + 1 := by
        have h1 := hp 1; have h2 := hp 2; have h3 := hp 3; have h4 := hp 4; have h5 := hp 5
        simp only [norm_mul, Complex.norm_ofNat, pow_one] at h1 ⊢
        linarith
    _ = 63 := by norm_num

lemma exp_neg_pi_im_le_quarter {y : ℝ} (hy : 1 ≤ y) : rexp (-π * y) ≤ 1 / 4 := by
  have h2 : rexp (-π * y) ≤ rexp (-π) := Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have h3 : rexp (-π) ≤ rexp (-1) * rexp (-1) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith [Real.pi_gt_three])
  have h5 : rexp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    linarith [Real.add_one_le_exp (1 : ℝ)]
  nlinarith [Real.exp_pos (-1)]

lemma norm_theta6_sub_one_le {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖jacobiTheta τ ^ 6 - 1‖ ≤ 252 * rexp (-π * τ.im) := by
  have h1 := norm_jacobiTheta_sub_one_le' hτ
  have hq := exp_neg_pi_im_le_quarter hτ
  have hw : ‖jacobiTheta τ - 1‖ ≤ 1 := by linarith
  have := norm_one_add_pow_six_sub_le hw
  rw [show 1 + (jacobiTheta τ - 1) = jacobiTheta τ by ring] at this
  linarith

/-! ### The series `A` and `B` -/

/-- `K₂ = ∑_r r² 2⁻ʳ`. -/
def K2 : ℝ := ∑' r : ℕ, (r : ℝ) ^ 2 * (1 / 2) ^ r

lemma hasSum_K2 : HasSum (fun r : ℕ => (r : ℝ) ^ 2 * (1 / 2) ^ r) K2 :=
  (summable_pow_mul_geometric_of_norm_lt_one 2 (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).hasSum

lemma K2_nonneg : 0 ≤ K2 := tsum_nonneg fun r => by positivity

lemma pow_le_aux {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1 / 2) {r k a : ℕ} (hr : 1 ≤ r)
    (ha : k + 1 ≤ a) : ρ ^ (r * a) ≤ 2 * ρ * (1 / 2) ^ k * (1 / 2) ^ r := by
  have hρ1 : ρ ≤ 1 := by linarith
  have e : r + k ≤ r * a := by nlinarith
  obtain ⟨s, hs⟩ : ∃ s, r + k = s + 1 := ⟨r + k - 1, by omega⟩
  calc ρ ^ (r * a) ≤ ρ ^ (r + k) := pow_le_pow_of_le_one h0 hρ1 e
    _ = ρ * ρ ^ s := by rw [hs, pow_succ']
    _ ≤ ρ * (1 / 2) ^ s := by gcongr
    _ = 2 * ρ * (1 / 2) ^ (r + k) := by rw [hs, pow_succ]; ring
    _ = 2 * ρ * (1 / 2) ^ k * (1 / 2) ^ r := by rw [pow_add]; ring

lemma norm_inner_le {c : ℕ → ℂ} (hc : ∀ r, ‖c r‖ ≤ 1) {q : ℂ} (hq : ‖q‖ ≤ 1 / 2) {k a : ℕ}
    (ha : k + 1 ≤ a) :
    ‖∑' r : ℕ, c r * (r : ℂ) ^ 2 * q ^ (r * a)‖ ≤ 2 * ‖q‖ * (1 / 2) ^ k * K2 := by
  refine tsum_of_norm_bounded (hasSum_K2.mul_left (2 * ‖q‖ * (1 / 2) ^ k)) fun r => ?_
  rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_natCast]
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  · have := pow_le_aux (norm_nonneg q) hq hr ha
    calc ‖c r‖ * (r : ℝ) ^ 2 * ‖q‖ ^ (r * a) ≤ 1 * (r : ℝ) ^ 2 * (2 * ‖q‖ * (1 / 2) ^ k * (1 / 2) ^ r) := by
          gcongr; exact hc r
      _ = _ := by ring

lemma hasSum_outer (q : ℂ) :
    HasSum (fun k : ℕ => 2 * ‖q‖ * (1 / 2) ^ k * K2) (4 * K2 * ‖q‖) := by
  have := (hasSum_geometric_two.mul_left (2 * ‖q‖)).mul_right K2
  convert this using 1; ring

lemma norm_seriesA_le {q : ℂ} (hq : ‖q‖ ≤ 1 / 2) : ‖seriesA q‖ ≤ 4 * K2 * ‖q‖ :=
  tsum_of_norm_bounded (hasSum_outer q) fun k =>
    norm_inner_le (c := fun r => chiZ r) (fun r => norm_chiZ_le _) hq (by omega)

lemma norm_seriesB_term_le {q : ℂ} (hq : ‖q‖ ≤ 1 / 2) (k : ℕ) :
    ‖chiZ (2 * k + 1) * ∑' r : ℕ, (r : ℂ) ^ 2 * q ^ (r * (2 * k + 1))‖ ≤
      2 * ‖q‖ * (1 / 2) ^ k * K2 := by
  rw [norm_mul]
  have h := norm_inner_le (c := fun _ => 1) (fun _ => by simp) hq (k := k) (a := 2 * k + 1)
    (by omega)
  simp only [one_mul] at h
  calc ‖chiZ (2 * k + 1)‖ * _ ≤ 1 * (2 * ‖q‖ * (1 / 2) ^ k * K2) := by
        gcongr
        · exact norm_chiZ_le _
    _ = _ := one_mul _

lemma norm_seriesB_le {q : ℂ} (hq : ‖q‖ ≤ 1 / 2) : ‖seriesB q‖ ≤ 4 * K2 * ‖q‖ :=
  tsum_of_norm_bounded (hasSum_outer q) (norm_seriesB_term_le hq)

lemma summable_seriesB_terms {q : ℂ} (hq : ‖q‖ ≤ 1 / 2) :
    Summable fun k : ℕ => chiZ (2 * k + 1) * ∑' r : ℕ, (r : ℂ) ^ 2 * q ^ (r * (2 * k + 1)) :=
  Summable.of_norm_bounded (hasSum_outer q).summable (norm_seriesB_term_le hq)

/-! ### `g = κ θ⁶ - L_W` -/

/-- `g(τ) = κ θ(τ)⁶ - L_W(τ)`. -/
def gfun (τ : ℍ) : ℂ := kappa * jacobiTheta τ ^ 6 - Lsum W τ

lemma gfun_S (τ : ℍ) : gfun (S • τ) = I * (τ : ℂ) ^ 3 * gfun τ := by
  rw [gfun, gfun, theta6_S, Lsum_W_S]; ring

lemma gfun_T_sq (τ : ℍ) : gfun (T ^ (2 : ℤ) • τ) = gfun τ := by
  rw [gfun, gfun, theta_T_sq, Lsum_W_T2]

lemma gfun_TS (τ : ℍ) : gfun ((T * S) • τ) = (τ : ℂ) ^ 3 *
    (kappa * (I * (cexp (3 * π * I * τ / 2) * jacobiTheta₂ (-(τ : ℂ) / 2) τ ^ 6)) - Lsum Wp τ) := by
  rw [gfun, theta6_TS, Lsum_W_TS]; ring

lemma mdiff_gfun : MDiff gfun := by
  have h1 : MDiff (fun τ : ℍ => kappa * jacobiTheta τ ^ 6) :=
    mdiff_of_eqOn (F := fun z => kappa * jacobiTheta z ^ 6)
      (fun z hz => (((differentiableAt_jacobiTheta hz).pow 6).const_mul kappa).differentiableWithinAt)
      fun _ => rfl
  exact h1.sub (mdiff_Lsum norm_W_le)

lemma norm_q (τ : ℍ) : ‖cexp (π * I * τ)‖ = rexp (-π * τ.im) := by
  rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re, Complex.mul_im]

/-- The constant of `norm_gfun_le`. -/
def Cg6 : ℝ := 252 * ‖kappa‖ + π ^ 3 * (4 * K2) + π ^ 3 / 4 * (4 * K2)

lemma Cg6_nonneg : 0 ≤ Cg6 := by
  have := K2_nonneg; have := Real.pi_pos; rw [Cg6]; positivity

lemma norm_gfun_le (τ : ℍ) (hτ : 1 ≤ τ.im) : ‖gfun τ‖ ≤ Cg6 * rexp (-π * τ.im) := by
  set q := cexp (π * I * τ) with hq
  have hqn : ‖q‖ = rexp (-π * τ.im) := norm_q τ
  have hq2 : ‖q‖ ≤ 1 / 2 := by rw [hqn]; linarith [exp_neg_pi_im_le_quarter hτ]
  have e : gfun τ = kappa * (jacobiTheta τ ^ 6 - 1) - π ^ 3 * seriesB q + π ^ 3 / 4 * seriesA q := by
    rw [gfun, Lsum_W_eq]; ring
  rw [e]
  have h1 := norm_theta6_sub_one_le (τ := (τ : ℂ)) (by simpa using hτ)
  have hA := norm_seriesA_le hq2
  have hB := norm_seriesB_le hq2
  have hi : (τ : ℂ).im = τ.im := rfl
  rw [hi] at h1
  rw [hqn] at hA hB
  have hp : ‖(π : ℂ) ^ 3‖ = π ^ 3 := by
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have hp4 : ‖(π : ℂ) ^ 3 / 4‖ = π ^ 3 / 4 := by
    rw [norm_div, hp, Complex.norm_ofNat]
  calc ‖kappa * (jacobiTheta τ ^ 6 - 1) - π ^ 3 * seriesB q + π ^ 3 / 4 * seriesA q‖
      ≤ ‖kappa * (jacobiTheta τ ^ 6 - 1)‖ + ‖(π : ℂ) ^ 3 * seriesB q‖ +
          ‖(π : ℂ) ^ 3 / 4 * seriesA q‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ ‖kappa‖ * (252 * rexp (-π * τ.im)) + π ^ 3 * (4 * K2 * rexp (-π * τ.im)) +
          π ^ 3 / 4 * (4 * K2 * rexp (-π * τ.im)) := by
        rw [norm_mul, norm_mul, norm_mul, hp, hp4]
        gcongr
    _ = Cg6 * rexp (-π * τ.im) := by rw [Cg6]; ring

/-- The bound for `L_{W'}` on the strip `|Re τ| ≤ 1`, `Im τ ≥ 1`. -/
def ML : ℝ := ∑' v : Fin 2 → ℤ, 2 * (r ⟨⟨1, 1⟩, one_pos⟩ ^ (-(3 : ℝ)) * ‖v‖ ^ (-(3 : ℝ)))

lemma norm_Lsum_Wp_le (τ : ℍ) (hτ : 1 ≤ τ.im) (hr : |τ.re| ≤ 1) : ‖Lsum Wp τ‖ ≤ ML := by
  have hs := ((summable_one_div_norm_rpow (k := 3) (by norm_num)).mul_left
    (r ⟨⟨1, 1⟩, one_pos⟩ ^ (-(3 : ℝ)))).mul_left 2
  refine tsum_of_norm_bounded hs.hasSum fun v => ?_
  rw [norm_mul]
  have hmem : τ ∈ verticalStrip 1 1 := ⟨hr, hτ⟩
  have hb := summand_bound_of_mem_verticalStrip (k := 3) (by norm_num) v one_pos hmem
  have he : ‖eisSummand 3 v τ‖ ≤ r ⟨⟨1, 1⟩, one_pos⟩ ^ (-(3 : ℝ)) * ‖v‖ ^ (-(3 : ℝ)) := by
    simp only [eisSummand, norm_zpow]
    exact_mod_cast hb
  exact mul_le_mul (norm_Wp_le v) he (norm_nonneg _) (by norm_num)

/-- The constant of `norm_gfun_TS_le`. -/
def M3 : ℝ := ‖kappa‖ * K1 ^ 6 + ML

lemma norm_gfun_TS_le (τ : ℍ) (hτ : 1 ≤ τ.im) (hr : |τ.re| ≤ 1) :
    ‖kappa * (I * (cexp (3 * π * I * τ / 2) * jacobiTheta₂ (-(τ : ℂ) / 2) τ ^ 6)) - Lsum Wp τ‖ ≤
      M3 := by
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, M3]
  gcongr
  · exact norm_theta6_TS_part_le τ hτ
  · exact norm_Lsum_Wp_le τ hτ hr

end NTKB.HardyWright.SixSquares
