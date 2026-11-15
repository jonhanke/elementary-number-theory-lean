/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.EightModular
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Expansions at `i∞` for the proof of Jacobi's `r₈` formula

* `θ(τ) = 1 + 2q + O(q⁴)` and `θ(τ)⁸ = 1 + 16q + O(q²)`, `q = e^{πiτ}`, for `Im τ ≥ 1`;
* `E₄(z) = 1 + 240 Q + O(Q²)`, `Q = e^{2πiz}`, for `Im z ≥ ½`;
* hence `g₁(τ), g₂(τ) = O(e^{-2π Im τ})` (`norm_g1_le`, `norm_g2_le`).
-/

open ModularForm ModularGroup Complex Filter Topology
open scoped MatrixGroups Real UpperHalfPlane

noncomputable section

namespace NTKB.HardyWright.EightSquares

lemma exp_neg_pi_le_half : rexp (-π) ≤ 1 / 2 := by
  have h := Real.add_one_le_exp π
  have hp := Real.pi_gt_three
  rw [Real.exp_neg]
  rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  linarith

lemma exp_neg_mul_le_half {a y : ℝ} (ha : π ≤ a * y) : rexp (-(a * y)) ≤ 1 / 2 :=
  (Real.exp_le_exp.mpr (by linarith)).trans exp_neg_pi_le_half

lemma norm_cexp_pi_I_mul (τ : ℂ) (c : ℝ) : ‖cexp (c * π * I * τ)‖ = rexp (-(c * π) * τ.im) := by
  rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re, Complex.mul_im]

/-! ### `θ` -/

lemma norm_jacobiTheta_sub_one_le' {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖jacobiTheta τ - 1‖ ≤ 4 * rexp (-π * τ.im) := by
  have h := norm_jacobiTheta_sub_one_le (by linarith : 0 < τ.im)
  have hr : rexp (-π * τ.im) ≤ 1 / 2 := by
    rw [show -π * τ.im = -(π * τ.im) by ring]
    exact exp_neg_mul_le_half (by nlinarith [Real.pi_pos])
  have hr0 := Real.exp_pos (-π * τ.im)
  refine h.trans ?_
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  nlinarith

/-- `‖θ(τ) - 1 - 2e^{πiτ}‖ ≤ 4e^{-4π Im τ}` for `Im τ ≥ 1`. -/
lemma norm_jacobiTheta_sub_le {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖jacobiTheta τ - 1 - 2 * cexp (π * I * τ)‖ ≤ 4 * rexp (-4 * π * τ.im) := by
  have hτ0 : 0 < τ.im := by linarith
  set y := τ.im with hy
  set f : ℕ → ℂ := fun n => cexp (π * I * ((n : ℂ) + 1) ^ 2 * τ) with hf
  have hs : HasSum f ((jacobiTheta τ - 1) / 2) := hasSum_nat_jacobiTheta hτ0
  have key : ∀ a : ℝ, ((π : ℂ) * I * (a : ℂ) * τ).re = -(π * a * τ.im) := by
    intro a; simp [Complex.mul_re, Complex.mul_im]
  have hnorm : ∀ n : ℕ, ‖f n‖ = rexp (-π * ((n : ℝ) + 1) ^ 2 * y) := by
    intro n
    have : ((n : ℂ) + 1) ^ 2 = (((n : ℝ) + 1) ^ 2 : ℝ) := by push_cast; ring
    rw [hf]; dsimp only
    rw [Complex.norm_exp, this, key, hy]; congr 1; ring
  -- the tail from `n = 1`
  have hs1 : HasSum (fun n => f (n + 1)) ((jacobiTheta τ - 1) / 2 - f 0) := by
    have := (hasSum_nat_add_iff' 1).mpr hs
    simpa using this
  have hf0 : f 0 = cexp (π * I * τ) := by simp [hf]
  set r := rexp (-π * y) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r ≤ 1 / 2 := by
    rw [hr, show -π * y = -(π * y) by ring]; exact exp_neg_mul_le_half (by nlinarith [Real.pi_pos])
  have hbound : ∀ n : ℕ, ‖f (n + 1)‖ ≤ rexp (-4 * π * y) * (1 / 2) ^ n := by
    intro n
    rw [hnorm]
    have h1 : rexp (-π * (((n + 1 : ℕ) : ℝ) + 1) ^ 2 * y) ≤ rexp (-4 * π * y) * r ^ n := by
      rw [hr, ← Real.exp_nat_mul, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      push_cast
      have hn : (0 : ℝ) ≤ n := n.cast_nonneg
      nlinarith [Real.pi_pos, mul_nonneg (mul_nonneg hn hn) (mul_nonneg Real.pi_pos.le hτ0.le),
        mul_nonneg hn (mul_nonneg Real.pi_pos.le hτ0.le)]
    refine h1.trans ?_
    gcongr
  have hgeom : HasSum (fun n : ℕ => rexp (-4 * π * y) * (1 / 2 : ℝ) ^ n) (rexp (-4 * π * y) * 2) := by
    have := (hasSum_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).mul_left
      (rexp (-4 * π * y))
    convert this using 1; norm_num
  have htail : ‖(jacobiTheta τ - 1) / 2 - f 0‖ ≤ rexp (-4 * π * y) * 2 := by
    rw [← hs1.tsum_eq]
    exact tsum_of_norm_bounded hgeom hbound
  have : jacobiTheta τ - 1 - 2 * cexp (π * I * τ) = 2 * ((jacobiTheta τ - 1) / 2 - f 0) := by
    rw [hf0]; ring
  rw [this, norm_mul]
  simp only [Complex.norm_ofNat]
  linarith

/-- `‖(1 + w)⁸ - 1 - 8w‖ ≤ 256 ‖w‖²` for `‖w‖ ≤ 1`. -/
lemma norm_one_add_pow_eight_sub_le {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖(1 + w) ^ 8 - 1 - 8 * w‖ ≤ 256 * ‖w‖ ^ 2 := by
  have e : (1 + w) ^ 8 - 1 - 8 * w =
      w ^ 2 * (28 + 56 * w + 70 * w ^ 2 + 56 * w ^ 3 + 28 * w ^ 4 + 8 * w ^ 5 + w ^ 6) := by ring
  rw [e, norm_mul, norm_pow, mul_comm]
  gcongr
  have h0 := norm_nonneg w
  have hp : ∀ k : ℕ, ‖w ^ k‖ ≤ 1 := fun k => by rw [norm_pow]; exact pow_le_one₀ h0 hw
  calc ‖(28 : ℂ) + 56 * w + 70 * w ^ 2 + 56 * w ^ 3 + 28 * w ^ 4 + 8 * w ^ 5 + w ^ 6‖
      ≤ ‖(28 : ℂ)‖ + ‖56 * w‖ + ‖70 * w ^ 2‖ + ‖56 * w ^ 3‖ + ‖28 * w ^ 4‖ + ‖8 * w ^ 5‖ +
          ‖w ^ 6‖ := by
        refine (norm_add_le _ _).trans ?_; gcongr
        refine (norm_add_le _ _).trans ?_; gcongr
        refine (norm_add_le _ _).trans ?_; gcongr
        refine (norm_add_le _ _).trans ?_; gcongr
        refine (norm_add_le _ _).trans ?_; gcongr
        exact norm_add_le _ _
    _ ≤ 28 + 56 + 70 + 56 + 28 + 8 + 1 := by
        have h1 := hp 1; have h2 := hp 2; have h3 := hp 3; have h4 := hp 4; have h5 := hp 5
        have h6 := hp 6
        simp only [norm_mul, Complex.norm_ofNat, pow_one] at h1 ⊢
        linarith
    _ ≤ 256 := by norm_num

/-- `‖θ(τ)⁸ - 1 - 16e^{πiτ}‖ ≤ 4128 e^{-2π Im τ}` for `Im τ ≥ 1`. -/
lemma norm_theta8_sub_le {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖jacobiTheta τ ^ 8 - 1 - 16 * cexp (π * I * τ)‖ ≤ 4128 * rexp (-2 * π * τ.im) := by
  set w := jacobiTheta τ - 1 with hw
  have h1 := norm_jacobiTheta_sub_one_le' hτ
  have h4 := norm_jacobiTheta_sub_le hτ
  have hy : 0 < τ.im := by linarith
  have hr : rexp (-π * τ.im) ≤ 1 / 4 := by
    have := exp_neg_pi_le_half
    have h2 : rexp (-π * τ.im) ≤ rexp (-π) := Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    have h3 : rexp (-π) ≤ rexp (-1) * rexp (-1) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith [Real.pi_gt_three])
    have h5 : rexp (-1) ≤ 1 / 2 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      linarith [Real.add_one_le_exp (1 : ℝ)]
    nlinarith [Real.exp_pos (-1)]
  have hwle : ‖w‖ ≤ 1 := by nlinarith [Real.exp_pos (-π * τ.im)]
  have hT := norm_one_add_pow_eight_sub_le hwle
  rw [show 1 + w = jacobiTheta τ by rw [hw]; ring] at hT
  have e : jacobiTheta τ ^ 8 - 1 - 16 * cexp (π * I * τ) =
      (jacobiTheta τ ^ 8 - 1 - 8 * w) + 8 * (jacobiTheta τ - 1 - 2 * cexp (π * I * τ)) := by
    rw [hw]; ring
  rw [e]
  have hsq : ‖w‖ ^ 2 ≤ 16 * rexp (-2 * π * τ.im) := by
    have : rexp (-2 * π * τ.im) = rexp (-π * τ.im) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [this]
    nlinarith [norm_nonneg w]
  have h44 : rexp (-4 * π * τ.im) ≤ rexp (-2 * π * τ.im) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  calc _ ≤ ‖jacobiTheta τ ^ 8 - 1 - 8 * w‖ + ‖8 * (jacobiTheta τ - 1 - 2 * cexp (π * I * τ))‖ :=
        norm_add_le _ _
    _ ≤ 256 * (16 * rexp (-2 * π * τ.im)) + 8 * (4 * rexp (-2 * π * τ.im)) := by
        rw [norm_mul, Complex.norm_ofNat]
        gcongr
        · exact hT.trans (by gcongr)
        · exact h4.trans (by gcongr)
    _ = 4128 * rexp (-2 * π * τ.im) := by ring

/-! ### `E₄` -/

lemma bernoulli_four' : (bernoulli 4 : ℂ) = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]; push_cast; ring

/-- `E₄(z) = 1 + 240 ∑_{n ≥ 0} σ₃(n+1) Q^{n+1}`, `Q = e^{2πiz}`. -/
lemma E4_eq_tsum (z : ℍ) :
    E₄ z = 1 + 240 * ∑' n : ℕ, (ArithmeticFunction.sigma 3 (n + 1) : ℂ) *
      cexp (2 * π * I * z) ^ (n + 1) := by
  have h := EisensteinSeries.q_expansion_bernoulli (k := 4) (by norm_num) (by decide) z
  have hE : (E (by norm_num : 3 ≤ 4) : ℍ → ℂ) z = E₄ z := rfl
  rw [hE] at h
  rw [h, bernoulli_four']
  have hp : ∑' n : ℕ+, (ArithmeticFunction.sigma (4 - 1) n : ℂ) * cexp (2 * π * I * z) ^ (n : ℤ) =
      ∑' n : ℕ, (ArithmeticFunction.sigma 3 (n + 1) : ℂ) * cexp (2 * π * I * z) ^ (n + 1) := by
    rw [← Equiv.pnatEquivNat.symm.tsum_eq]
    refine tsum_congr fun n => ?_
    simp [Equiv.pnatEquivNat_symm_apply]
    norm_cast
  rw [hp]
  push_cast
  ring

lemma sigma_three_le' (n : ℕ) : (ArithmeticFunction.sigma 3 n : ℝ) ≤ (n : ℝ) ^ 4 := by
  rw [ArithmeticFunction.sigma_apply]
  push_cast
  calc ∑ d ∈ n.divisors, (d : ℝ) ^ 3 ≤ ∑ _d ∈ n.divisors, (n : ℝ) ^ 3 := by
        refine Finset.sum_le_sum fun d hd => ?_
        have := Nat.divisor_le hd
        gcongr
    _ = n.divisors.card * (n : ℝ) ^ 3 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ n * (n : ℝ) ^ 3 := by gcongr; exact_mod_cast Nat.card_divisors_le_self n
    _ = (n : ℝ) ^ 4 := by ring

/-- The constant `∑ (n+2)⁴ 2⁻ⁿ`. -/
def K0 : ℝ := ∑' n : ℕ, ((n : ℝ) + 2) ^ 4 * (1 / 2) ^ n

lemma summable_K0 : Summable fun n : ℕ => ((n : ℝ) + 2) ^ 4 * (1 / 2 : ℝ) ^ n := by
  have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 4 (r := 1 / 2)
    (by rw [Real.norm_eq_abs]; norm_num)
  have h2 := ((summable_nat_add_iff 2).mpr h).mul_left 4
  refine h2.congr fun n => ?_
  push_cast; rw [pow_add]; ring

lemma K0_nonneg : 0 ≤ K0 := tsum_nonneg fun n => by positivity

/-- `‖E₄(z) - 1 - 240 Q‖ ≤ 240 K₀ ‖Q‖²` for `Im z ≥ ½`. -/
lemma norm_E4_sub_le (z : ℍ) (hz : 1 / 2 ≤ z.im) :
    ‖E₄ z - 1 - 240 * cexp (2 * π * I * z)‖ ≤ 240 * K0 * rexp (-4 * π * z.im) := by
  set Q := cexp (2 * π * I * z) with hQ
  set r := rexp (-2 * π * z.im) with hr
  have hQn : ‖Q‖ = r := by
    rw [hQ, Complex.norm_exp]; congr 1; simp [Complex.mul_re, Complex.mul_im]
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r ≤ 1 / 2 := by
    rw [hr, show -2 * π * z.im = -((2 * z.im) * π) by ring]
    exact exp_neg_mul_le_half (by nlinarith [Real.pi_pos])
  set a : ℕ → ℂ := fun n => (ArithmeticFunction.sigma 3 n : ℂ) * Q ^ n with ha
  have hnorm : ∀ n, ‖a n‖ ≤ (n : ℝ) ^ 4 * r ^ n := by
    intro n
    rw [ha, norm_mul, norm_pow, hQn]
    gcongr
    rw [Complex.norm_natCast]; exact sigma_three_le' n
  have hsum : Summable fun n : ℕ => (n : ℝ) ^ 4 * r ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one 4 (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; linarith)
  have hsa : Summable a := Summable.of_norm_bounded hsum hnorm
  have hsa1 : Summable fun n => a (n + 1) := (summable_nat_add_iff 1).mpr hsa
  have hsplit : ∑' n : ℕ, a (n + 1) = Q + ∑' n : ℕ, a (n + 2) := by
    rw [hsa1.tsum_eq_zero_add]; simp [ha]
  have hE := E4_eq_tsum z
  have hE' : E₄ z - 1 - 240 * Q = 240 * ∑' n : ℕ, a (n + 2) := by
    rw [hE, show (fun n : ℕ => (ArithmeticFunction.sigma 3 (n + 1) : ℂ) * Q ^ (n + 1)) =
      fun n => a (n + 1) from rfl, hsplit]; ring
  rw [hE', norm_mul, Complex.norm_ofNat]
  have hb : ∀ n : ℕ, ‖a (n + 2)‖ ≤ r ^ 2 * (((n : ℝ) + 2) ^ 4 * (1 / 2) ^ n) := by
    intro n
    refine (hnorm (n + 2)).trans ?_
    push_cast
    rw [pow_add, show r ^ 2 * (((n : ℝ) + 2) ^ 4 * (1 / 2) ^ n) =
      ((n : ℝ) + 2) ^ 4 * ((1 / 2) ^ n * r ^ 2) by ring]
    gcongr
  have ht : ‖∑' n : ℕ, a (n + 2)‖ ≤ r ^ 2 * K0 :=
    tsum_of_norm_bounded (summable_K0.hasSum.mul_left (r ^ 2)) hb
  have hr2 : r ^ 2 = rexp (-4 * π * z.im) := by
    rw [hr, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [← hr2]
  nlinarith [K0_nonneg]

lemma norm_E4_sub_one_le (z : ℍ) (hz : 1 / 2 ≤ z.im) :
    ‖E₄ z - 1‖ ≤ (240 + 240 * K0) * rexp (-2 * π * z.im) := by
  have h := norm_E4_sub_le z hz
  have hQ : ‖cexp (2 * π * I * z)‖ = rexp (-2 * π * z.im) := by
    rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re, Complex.mul_im]
  have h44 : rexp (-4 * π * z.im) ≤ rexp (-2 * π * z.im) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  calc ‖E₄ z - 1‖ = ‖(E₄ z - 1 - 240 * cexp (2 * π * I * z)) + 240 * cexp (2 * π * I * z)‖ := by
        ring_nf
    _ ≤ ‖E₄ z - 1 - 240 * cexp (2 * π * I * z)‖ + ‖240 * cexp (2 * π * I * z)‖ := norm_add_le _ _
    _ ≤ 240 * K0 * rexp (-2 * π * z.im) + 240 * rexp (-2 * π * z.im) := by
        rw [norm_mul, Complex.norm_ofNat, hQ]
        gcongr
        exact h.trans (by gcongr; nlinarith [K0_nonneg])
    _ = (240 + 240 * K0) * rexp (-2 * π * z.im) := by ring

/-! ### `g₁` and `g₂` -/

/-- `‖e₁(τ) - 1 - 16 e^{πiτ}‖ ≤ C e^{-2π Im τ}` for `Im τ ≥ 1`. -/
lemma norm_e1_sub_le (τ : ℍ) (hτ : 1 ≤ τ.im) :
    ‖e1 τ - 1 - 16 * cexp (π * I * τ)‖ ≤ (16 * K0 + 3 * (240 + 240 * K0)) * rexp (-2 * π * τ.im) := by
  have hh : (halfH τ).im = τ.im / 2 := by
    change ((τ : ℂ) / 2).im = (τ : ℂ).im / 2; simp
  have ht : (twoH τ).im = 2 * τ.im := by
    change (2 * (τ : ℂ)).im = 2 * (τ : ℂ).im; simp
  have h1 := norm_E4_sub_le (halfH τ) (by rw [hh]; linarith)
  have h2 := norm_E4_sub_one_le τ (by linarith)
  have h3 := norm_E4_sub_one_le (twoH τ) (by rw [ht]; linarith)
  rw [hh] at h1; rw [ht] at h3
  have hq : cexp (2 * π * I * (halfH τ : ℂ)) = cexp (π * I * τ) := by
    rw [coe_halfH]; congr 1; ring
  rw [hq] at h1
  have e : e1 τ - 1 - 16 * cexp (π * I * τ) = ((E₄ (halfH τ) - 1 - 240 * cexp (π * I * τ)) -
      2 * (E₄ τ - 1) + 16 * (E₄ (twoH τ) - 1)) / 15 := by
    simp only [e1]; ring
  rw [e, norm_div, Complex.norm_ofNat]
  have hA : rexp (-4 * π * (τ.im / 2)) = rexp (-2 * π * τ.im) := by congr 1; ring
  have hB : rexp (-2 * π * (2 * τ.im)) ≤ rexp (-2 * π * τ.im) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  rw [hA] at h1
  have hK := K0_nonneg
  have hX := Real.exp_pos (-2 * π * τ.im)
  rw [div_le_iff₀ (by norm_num)]
  calc ‖(E₄ (halfH τ) - 1 - 240 * cexp (π * I * τ)) - 2 * (E₄ τ - 1) + 16 * (E₄ (twoH τ) - 1)‖
      ≤ ‖E₄ (halfH τ) - 1 - 240 * cexp (π * I * τ)‖ + 2 * ‖E₄ τ - 1‖ +
          16 * ‖E₄ (twoH τ) - 1‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, Complex.norm_ofNat]
        have := norm_sub_le (E₄ (halfH τ) - 1 - 240 * cexp (π * I * τ)) (2 * (E₄ τ - 1))
        rw [norm_mul, Complex.norm_ofNat] at this
        linarith
    _ ≤ 240 * K0 * rexp (-2 * π * τ.im) + 2 * ((240 + 240 * K0) * rexp (-2 * π * τ.im)) +
          16 * ((240 + 240 * K0) * rexp (-2 * π * τ.im)) := by
        gcongr
        exact h3.trans (by gcongr)
    _ ≤ (16 * K0 + 3 * (240 + 240 * K0)) * rexp (-2 * π * τ.im) * 15 := by nlinarith

/-- The constant of `norm_g1_le`. -/
def Cg : ℝ := 4128 + (16 * K0 + 3 * (240 + 240 * K0))

lemma norm_g1_le (τ : ℍ) (hτ : 1 ≤ τ.im) : ‖g1 τ‖ ≤ Cg * rexp (-2 * π * τ.im) := by
  have h1 := norm_theta8_sub_le (τ := (τ : ℂ)) (by simpa using hτ)
  have h2 := norm_e1_sub_le τ hτ
  have e : g1 τ = (jacobiTheta τ ^ 8 - 1 - 16 * cexp (π * I * τ)) -
      (e1 τ - 1 - 16 * cexp (π * I * τ)) := by simp only [g1]; ring
  rw [e]
  have hi : (τ : ℂ).im = τ.im := rfl
  rw [hi] at h1
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ 4128 * rexp (-2 * π * τ.im) + (16 * K0 + 3 * (240 + 240 * K0)) * rexp (-2 * π * τ.im) :=
        add_le_add h1 h2
    _ = Cg * rexp (-2 * π * τ.im) := by rw [Cg]; ring

lemma g2_apply (τ : ℍ) : g2 τ = g1 (T • τ) := by
  rw [g2, SL_slash_apply, ModularGroup.denom_apply]; simp [T]

lemma norm_g2_le (τ : ℍ) (hτ : 1 ≤ τ.im) : ‖g2 τ‖ ≤ Cg * rexp (-2 * π * τ.im) := by
  rw [g2_apply]
  have him : (T • τ).im = τ.im := by
    rw [UpperHalfPlane.modular_T_smul]; simp
  have := norm_g1_le (T • τ) (by rw [him]; exact hτ)
  rwa [him] at this

end NTKB.HardyWright.EightSquares
