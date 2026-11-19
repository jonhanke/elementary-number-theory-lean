/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TenCuspSeries
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.EighteenStatement

/-!
# The weight-`9` cusp form `C₈(τ) = ∑_{a ∈ ℤ[i]} a⁸ e^{πi N(a) τ}`

`octC τ = ∑_{(m, n) ∈ ℤ²} (m + in)⁸ e^{πiτ(m² + n²)}`, the coefficient of `z⁸` in
`θ(z, τ) θ(iz, τ)` (the method of `TenCusp.lean`, which does the same for `z⁴`). Its laws are those of
`θ¹⁸`:

* `octC_S`: `C₈(-1/τ) = -i τ⁹ C₈(τ)`; `octC_add_two`: `C₈(τ + 2) = C₈(τ)`;
* `octC_TS`: `C₈(1 - 1/τ) = -i τ⁹ D₈(τ)`, `D₈` the half-integer shift, bounded on `Im τ ≥ 1`;
* `mdiff_oct`: `C₈` is holomorphic on `ℍ`;
* `hasSum_octC`: `C₈(τ) = ∑ₙ c₈(n) qⁿ`, `q = e^{πiτ}`, `c₈ = octicCoeff`.
-/

open Complex Filter Topology ModularForm ModularGroup
open scoped Real UpperHalfPlane MatrixGroups Manifold
open UpperHalfPlane hiding I

noncomputable section

namespace NTKB.HardyWright.EighteenSquares

open TenSquares
open EightSquares (mdiff_of_eqOn coe_S_smul coe_T_zpow_smul coe_TS_smul ne_zero')

/-! ### The oct form `C₈` and its laws -/

/-- `C(τ) = ∑_{(m, n) ∈ ℤ²} (m + in)⁸ e^{πiτ(m² + n²)}`.
  **Restriction:** the lattice sum converges (absolutely) only for $\operatorname{Im}\tau > 0$; elsewhere the value
  is $0$ by Lean's `tsum` convention, not an analytic continuation or the intended value. -/
def octC (τ : ℂ) : ℂ :=
  ∑' v : ℤ × ℤ, ((v.1 : ℂ) + I * v.2) ^ 8 * cexp (π * I * τ * ((v.1 : ℂ) ^ 2 + (v.2 : ℂ) ^ 2))

/-- `D(τ) = ∑_{(m, n) ∈ ℤ²} (m + ½ + i(n + ½))⁸ e^{πiτ((m + ½)² + (n + ½)²)}`. -/
def octD (τ : ℂ) : ℂ :=
  ∑' v : ℤ × ℤ, (((v.1 : ℂ) + 1 / 2) + I * ((v.2 : ℂ) + 1 / 2)) ^ 8 *
    cexp (π * I * τ * (((v.1 : ℂ) + 1 / 2) ^ 2 + ((v.2 : ℂ) + 1 / 2) ^ 2))

lemma uf_pow_eight (α β : ℝ) (v : ℤ × ℤ) :
    uf α β v ^ 8 = (2 * π) ^ 8 * (((v.1 : ℂ) + α) + I * ((v.2 : ℂ) + β)) ^ 8 := by
  rw [uf, mul_pow, mul_pow, mul_pow, show I ^ 8 = (I ^ 4) ^ 2 by ring, I_pow_four]; ring

lemma sum_cf_zero8 (τ : ℂ) :
    ∑' v, cf (fun _ => 1) 0 0 τ v * uf 0 0 v ^ 8 = (2 * π) ^ 8 * octC τ := by
  rw [octC, ← tsum_mul_left]
  refine tsum_congr fun v => ?_
  rw [uf_pow_eight]
  simp only [cf, Complex.ofReal_zero, add_zero, one_mul]
  ring

lemma sum_cf_half8 (τ : ℂ) :
    ∑' v, cf (fun _ => 1) (1 / 2) (1 / 2) τ v * uf (1 / 2) (1 / 2) v ^ 8 =
      (2 * π) ^ 8 * octD τ := by
  rw [octD, ← tsum_mul_left]
  refine tsum_congr fun v => ?_
  rw [uf_pow_eight]
  simp only [cf, one_mul]
  push_cast
  ring

lemma sum_cf_sgn8 (τ : ℂ) :
    ∑' v, cf sgn 0 0 τ v * uf 0 0 v ^ 8 = (2 * π) ^ 8 * octC (1 + τ) := by
  rw [octC, ← tsum_mul_left]
  refine tsum_congr fun v => ?_
  rw [uf_pow_eight]
  simp only [cf, sgn, Complex.ofReal_zero, add_zero]
  have e : cexp (π * I * (1 + τ) * ((v.1 : ℂ) ^ 2 + (v.2 : ℂ) ^ 2)) =
      cexp (π * I * ((v.1 : ℂ) + v.2)) * cexp (π * I * τ * ((v.1 : ℂ) ^ 2 + (v.2 : ℂ) ^ 2)) := by
    have h1 := cexp_pi_I_sq v.1
    have h2 := cexp_pi_I_sq v.2
    calc cexp (π * I * (1 + τ) * ((v.1 : ℂ) ^ 2 + (v.2 : ℂ) ^ 2))
        = cexp (π * I * (v.1 : ℂ) ^ 2) * cexp (π * I * (v.2 : ℂ) ^ 2) *
            cexp (π * I * τ * ((v.1 : ℂ) ^ 2 + (v.2 : ℂ) ^ 2)) := by
          rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
      _ = cexp (π * I * v.1) * cexp (π * I * v.2) *
            cexp (π * I * τ * ((v.1 : ℂ) ^ 2 + (v.2 : ℂ) ^ 2)) := by rw [h1, h2]
      _ = _ := by rw [← Complex.exp_add]; congr 2; ring
  rw [e]
  ring

/-- **The `S`-law of `C₈`.** `C(-1/τ) = -i τ⁹ C(τ)`. -/
theorem octC_S {τ : ℂ} (hτ : 0 < τ.im) : octC (-1 / τ) = -I * τ ^ 9 * octC τ := by
  have hτ' := im_neg_inv_pos hτ
  have h0 := ne_zero_of_im_pos hτ
  have hfe : ∀ z, expSum (cf (fun _ => 1) 0 0 (-1 / τ)) (uf 0 0) (τ⁻¹ * z) =
      (-I * τ) * expSum (cf (fun _ => 1) 0 0 τ) (uf 0 0) z := by
    intro z
    rw [← theta_prod_zero _ _ hτ', ← theta_prod_zero _ _ hτ]
    have h := theta_prod_fe z (I * z) τ hτ
    have ex : cexp (π * I * (z ^ 2 + (I * z) ^ 2) / τ) = 1 := by
      rw [← Complex.exp_zero]
      congr 1
      rw [mul_pow, I_sq]
      ring
    rw [ex, mul_one] at h
    rw [show τ⁻¹ * z = z / τ by field_simp, show I * (z / τ) = I * z / τ by ring, h]
  have hc := coeff_eq_of_expSum_eq (expSummable_zero hτ') (expSummable_zero hτ) τ⁻¹ (-I * τ) hfe 8
  rw [sum_cf_zero8, sum_cf_zero8] at hc
  have hπ : (2 * (π : ℂ)) ^ 8 ≠ 0 := pow_ne_zero _ (mul_ne_zero two_ne_zero
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have h8 : τ⁻¹ ^ 8 * τ ^ 8 = 1 := by rw [← mul_pow, inv_mul_cancel₀ h0, one_pow]
  have hc' : τ ^ 8 * (τ⁻¹ ^ 8 * ((2 * π) ^ 8 * octC (-1 / τ))) =
      τ ^ 8 * (-I * τ * ((2 * π) ^ 8 * octC τ)) := by rw [hc]
  apply mul_left_cancel₀ hπ
  linear_combination hc' - ((2 * (π : ℂ)) ^ 8 * octC (-1 / τ)) * h8

/-- **The `TS`-law of `C₈`.** `C(1 - 1/τ) = -i τ⁹ D(τ)`. -/
theorem octC_TS {τ : ℂ} (hτ : 0 < τ.im) : octC (1 + -1 / τ) = -I * τ ^ 9 * octD τ := by
  have hτ' := im_neg_inv_pos hτ
  have h0 := ne_zero_of_im_pos hτ
  have hfe : ∀ z, expSum (cf sgn 0 0 (-1 / τ)) (uf 0 0) (τ⁻¹ * z) =
      (-I * τ) * expSum (cf (fun _ => 1) (1 / 2) (1 / 2) τ) (uf (1 / 2) (1 / 2)) z := by
    intro z
    rw [← theta_prod_half _ _ hτ', ← theta_prod_shift _ _ hτ]
    have h := theta_prod_fe (z + τ / 2) (I * z + τ / 2) τ hτ
    have ex : cexp (π * I * ((z + τ / 2) ^ 2 + (I * z + τ / 2) ^ 2) / τ) =
        cexp (π * I * τ / 2) * cexp (π * I * (1 + I) * z) := by
      rw [← Complex.exp_add]
      congr 1
      field_simp
      linear_combination (4 * z ^ 2) * I_sq
    rw [ex] at h
    rw [show τ⁻¹ * z + 1 / 2 = (z + τ / 2) / τ by field_simp,
      show I * (τ⁻¹ * z) + 1 / 2 = (I * z + τ / 2) / τ by field_simp, h]
    ring
  have hc := coeff_eq_of_expSum_eq (expSummable_sgn hτ') (expSummable_half hτ) τ⁻¹ (-I * τ) hfe 8
  rw [sum_cf_sgn8, sum_cf_half8] at hc
  have hπ : (2 * (π : ℂ)) ^ 8 ≠ 0 := pow_ne_zero _ (mul_ne_zero two_ne_zero
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have h8 : τ⁻¹ ^ 8 * τ ^ 8 = 1 := by rw [← mul_pow, inv_mul_cancel₀ h0, one_pow]
  have hc' : τ ^ 8 * (τ⁻¹ ^ 8 * ((2 * π) ^ 8 * octC (1 + -1 / τ))) =
      τ ^ 8 * (-I * τ * ((2 * π) ^ 8 * octD τ)) := by rw [hc]
  apply mul_left_cancel₀ hπ
  linear_combination hc' - ((2 * (π : ℂ)) ^ 8 * octC (1 + -1 / τ)) * h8

/-- `C(τ + 2) = C(τ)`. -/
theorem octC_add_two (τ : ℂ) : octC (τ + 2) = octC τ := by
  rw [octC, octC]
  refine tsum_congr fun v => ?_
  congr 1
  have : π * I * (τ + 2) * ((v.1 : ℂ) ^ 2 + (v.2 : ℂ) ^ 2) =
      π * I * τ * ((v.1 : ℂ) ^ 2 + (v.2 : ℂ) ^ 2) + ((v.1 ^ 2 + v.2 ^ 2 : ℤ) : ℂ) * (2 * π * I) := by
    push_cast; ring
  rw [this, Complex.exp_add, exp_int_mul_two_pi_mul_I, mul_one]

/-- The bound for `D₈` on `Im τ ≥ 1`. -/
def MD8 : ℝ := ∑' v, ‖cf (fun _ => 1) (1 / 2) (1 / 2) I v‖ * ‖uf (1 / 2) (1 / 2) v‖ ^ 8

lemma norm_octD_le {τ : ℂ} (hτ : 1 ≤ τ.im) : ‖(2 * π : ℂ) ^ 8 * octD τ‖ ≤ MD8 := by
  rw [← sum_cf_half8]
  have hI : (0 : ℝ) < I.im := by simp
  refine tsum_of_norm_bounded (summable_norm_mul_pow (expSummable_half hI) 8).hasSum fun v => ?_
  rw [norm_mul, norm_pow]
  gcongr
  exact norm_cf_one_anti _ _ (by simpa using hτ) v

/-! ### On the upper half-plane -/

/-- `C₈` on `ℍ`. -/
def oct (τ : ℍ) : ℂ := octC τ

/-- `-i D`, the factor of `C₈` at the oct `1`. -/
def octTS (τ : ℍ) : ℂ := -I * octD τ

lemma oct_S (τ : ℍ) : oct (S • τ) = -I * (τ : ℂ) ^ 9 * oct τ := by
  rw [oct, oct, coe_S_smul, octC_S τ.2]

lemma oct_T_sq (τ : ℍ) : oct (T ^ (2 : ℤ) • τ) = oct τ := by
  rw [oct, oct, coe_T_zpow_smul]
  push_cast
  exact octC_add_two _

lemma oct_TS (τ : ℍ) : oct ((T * S) • τ) = (τ : ℂ) ^ 9 * octTS τ := by
  rw [oct, octTS, coe_TS_smul]
  have h0 := ne_zero' τ
  rw [show ((τ : ℂ) - 1) / τ = 1 + -1 / τ by field_simp; ring, octC_TS τ.2]
  ring

/-- The constant of `norm_octTS_le`. -/
def MTSc8 : ℝ := MD8 / (2 * π) ^ 8

lemma norm_octTS_le (τ : ℍ) (hτ : 1 ≤ τ.im) : ‖octTS τ‖ ≤ MTSc8 := by
  have h := norm_octD_le (τ := (τ : ℂ)) hτ
  have hπ : (0 : ℝ) < (2 * π) ^ 8 := by positivity
  rw [norm_mul, norm_pow] at h
  have e : ‖(2 * π : ℂ)‖ = 2 * π := by
    rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  rw [e] at h
  rw [octTS, norm_mul, norm_neg, Complex.norm_I, one_mul, MTSc8, le_div_iff₀ hπ]
  linarith

/-! ### Holomorphy -/

lemma differentiableOn_octC : DifferentiableOn ℂ octC {z : ℂ | 0 < z.im} := by
  have hfun : octC = fun τ => ((2 * π : ℂ) ^ 8)⁻¹ *
      ∑' v, cf (fun _ => 1) 0 0 τ v * uf 0 0 v ^ 8 := by
    funext τ
    rw [sum_cf_zero8]
    have hπ : (2 * (π : ℂ)) ^ 8 ≠ 0 := pow_ne_zero _ (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    field_simp
  rw [hfun]
  refine DifferentiableOn.const_mul ?_ _
  intro z0 hz0
  have hz0' : (0 : ℝ) < z0.im := hz0
  set B : ℝ := z0.im / 2
  have hB : 0 < B := by positivity
  set V := {z : ℂ | B < z.im}
  have hV : IsOpen V := isOpen_lt continuous_const Complex.continuous_im
  have hzV : z0 ∈ V := by show B < z0.im; simp only [B]; linarith
  have hBI : (0 : ℝ) < (I * B).im := by simpa using hB
  have hd : DifferentiableOn ℂ (fun z => ∑' v, cf (fun _ => 1) 0 0 z v * uf 0 0 v ^ 8) V := by
    refine differentiableOn_tsum_of_summable_norm
      (summable_norm_mul_pow (expSummable_zero hBI) 8) (fun v => ?_) hV (fun v z hz => ?_)
    · refine DifferentiableOn.mul ?_ (differentiableOn_const _)
      refine DifferentiableOn.mul (differentiableOn_const _) ?_
      exact (((differentiableOn_const _).mul differentiableOn_id).mul
        (differentiableOn_const _)).cexp
    · rw [norm_mul, norm_pow]
      gcongr
      exact norm_cf_one_anti _ _ (by simpa using (le_of_lt hz)) v
  exact (hd.differentiableAt (hV.mem_nhds hzV)).differentiableWithinAt

lemma mdiff_oct : MDiff oct :=
  mdiff_of_eqOn differentiableOn_octC fun _ => rfl

/-! ### The `q`-expansion -/

lemma summable_octC_terms {τ : ℂ} (hτ : 0 < τ.im) :
    Summable fun v : ℤ × ℤ => ((v.1 : ℂ) + I * v.2) ^ 8 *
      cexp (π * I * τ * ((v.1 : ℂ) ^ 2 + (v.2 : ℂ) ^ 2)) := by
  have hs := (summable_norm_mul_pow (expSummable_zero hτ) 8)
  have hπ : (0 : ℝ) < (2 * π) ^ 8 := by positivity
  refine Summable.of_norm_bounded (hs.mul_left ((2 * π) ^ 8)⁻¹) fun v => ?_
  have e := uf_pow_eight 0 0 v
  simp only [Complex.ofReal_zero, add_zero] at e
  have hn : ‖uf 0 0 v‖ ^ 8 = (2 * π) ^ 8 * ‖((v.1 : ℂ) + I * v.2) ^ 8‖ := by
    rw [← norm_pow, e, norm_mul, norm_pow, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
  rw [hn, norm_mul]
  have hc : ‖cexp (π * I * τ * ((v.1 : ℂ) ^ 2 + (v.2 : ℂ) ^ 2))‖ = ‖cf (fun _ => 1) 0 0 τ v‖ := by
    simp [cf]
  rw [hc]
  field_simp
  rfl

/-- `octicRe` on pairs. -/
def rePoly8 (v : ℤ × ℤ) : ℤ := octicRe v.1 v.2

lemma I_pow_eight : I ^ 8 = 1 := by rw [show I ^ 8 = (I ^ 4) ^ 2 by ring, I_pow_four, one_pow]

lemma two_mul_rePoly8 (v : ℤ × ℤ) :
    ((v.1 : ℂ) + I * v.2) ^ 8 + ((v.1 : ℂ) - I * v.2) ^ 8 = 2 * (rePoly8 v : ℂ) := by
  simp only [rePoly8, octicRe]
  push_cast
  have h6 : I ^ 6 = -1 := by rw [show I ^ 6 = I ^ 4 * I ^ 2 by ring, I_pow_four, I_sq]; ring
  ring_nf
  rw [I_sq, I_pow_four, h6, I_pow_eight]
  ring

lemma abs_rePoly8_le (v : ℤ × ℤ) : ‖(rePoly8 v : ℂ)‖ ≤ ‖((v.1 : ℂ) + I * v.2) ^ 8‖ := by
  have hc : ((v.1 : ℂ) - I * v.2) = (starRingEnd ℂ) ((v.1 : ℂ) + I * v.2) := by
    simp [map_add, map_mul, Complex.conj_I]; ring
  have h := two_mul_rePoly8 v
  rw [hc, ← map_pow] at h
  have hn : ‖(starRingEnd ℂ) (((v.1 : ℂ) + I * v.2) ^ 8)‖ = ‖((v.1 : ℂ) + I * v.2) ^ 8‖ :=
    Complex.norm_conj _
  have h2 : ‖2 * (rePoly8 v : ℂ)‖ ≤ 2 * ‖((v.1 : ℂ) + I * v.2) ^ 8‖ := by
    rw [← h]; exact (norm_add_le _ _).trans (by rw [hn]; linarith)
  rw [norm_mul, Complex.norm_ofNat] at h2
  linarith

lemma octC_eq_octicRe {τ : ℂ} (hτ : 0 < τ.im) :
    octC τ = ∑' v : ℤ × ℤ, (rePoly8 v : ℂ) * cexp (π * I * τ * ((v.1 : ℂ) ^ 2 + (v.2 : ℂ) ^ 2)) := by
  have hs := summable_octC_terms hτ
  have hs' : Summable fun v : ℤ × ℤ => ((v.1 : ℂ) - I * v.2) ^ 8 *
      cexp (π * I * τ * ((v.1 : ℂ) ^ 2 + (v.2 : ℂ) ^ 2)) := by
    refine (conjEquiv.summable_iff.mpr hs).congr fun v => ?_
    simp [conjEquiv]
    ring_nf
  have h1 : octC τ = ∑' v : ℤ × ℤ, ((v.1 : ℂ) - I * v.2) ^ 8 *
      cexp (π * I * τ * ((v.1 : ℂ) ^ 2 + (v.2 : ℂ) ^ 2)) := by
    rw [octC, ← conjEquiv.tsum_eq]
    refine tsum_congr fun v => ?_
    simp [conjEquiv]
    ring_nf
  have h2 : 2 * octC τ = ∑' v : ℤ × ℤ, (2 * (rePoly8 v : ℂ)) *
      cexp (π * I * τ * ((v.1 : ℂ) ^ 2 + (v.2 : ℂ) ^ 2)) := by
    calc 2 * octC τ = octC τ + octC τ := two_mul _
      _ = (∑' v : ℤ × ℤ, ((v.1 : ℂ) + I * v.2) ^ 8 *
            cexp (π * I * τ * ((v.1 : ℂ) ^ 2 + (v.2 : ℂ) ^ 2))) +
          ∑' v : ℤ × ℤ, ((v.1 : ℂ) - I * v.2) ^ 8 *
            cexp (π * I * τ * ((v.1 : ℂ) ^ 2 + (v.2 : ℂ) ^ 2)) := congrArg₂ (· + ·) rfl h1
      _ = _ := by
        rw [← hs.tsum_add hs']
        refine tsum_congr fun v => ?_
        rw [← add_mul, two_mul_rePoly8]
  have h3 : ∑' v : ℤ × ℤ, (2 * (rePoly8 v : ℂ)) * cexp (π * I * τ * ((v.1 : ℂ) ^ 2 + (v.2 : ℂ) ^ 2)) =
      2 * ∑' v : ℤ × ℤ, (rePoly8 v : ℂ) * cexp (π * I * τ * ((v.1 : ℂ) ^ 2 + (v.2 : ℂ) ^ 2)) := by
    rw [← tsum_mul_left]; refine tsum_congr fun v => ?_; ring
  rw [h3] at h2
  exact mul_left_cancel₀ two_ne_zero h2

/-- **The `q`-expansion of `C₈`.** `C(τ) = ∑ₙ c(n) qⁿ`, `q = e^{πiτ}`. -/
theorem hasSum_octC {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℕ => (octicCoeff n : ℂ) * cexp (π * I * τ) ^ n) (octC τ) := by
  have hc : ∀ v : ℤ × ℤ, cexp (π * I * τ * ((v.1 : ℂ) ^ 2 + (v.2 : ℂ) ^ 2)) =
      cexp (π * I * τ) ^ normSq' v := cexp_eq_q_pow τ
  have hs : Summable fun v : ℤ × ℤ => (rePoly8 v : ℂ) * cexp (π * I * τ) ^ normSq' v := by
    have hn := summable_norm_iff.mpr (summable_octC_terms hτ)
    refine Summable.of_norm_bounded hn fun v => ?_
    rw [← hc, norm_mul, norm_mul]
    gcongr
    exact abs_rePoly8_le v
  have hsum : HasSum (fun v : ℤ × ℤ => (rePoly8 v : ℂ) * cexp (π * I * τ) ^ normSq' v) (octC τ) := by
    rw [octC_eq_octicRe hτ]
    simp only [hc]
    exact hs.hasSum
  have hfib := hsum.tsum_fiberwise normSq'
  convert hfib using 1
  funext n
  have hF := Finset.tsum_subtype' (((Finset.Icc (-(n : ℤ)) n) ×ˢ (Finset.Icc (-(n : ℤ)) n)).filter
      (fun v : ℤ × ℤ => v.1 ^ 2 + v.2 ^ 2 = n)) (fun v : ℤ × ℤ => (rePoly8 v : ℂ) * cexp (π * I * τ) ^ normSq' v)
  rw [← fiber_eq] at hF
  rw [hF, octicCoeff]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun v hv => ?_
  simp only [Finset.mem_filter] at hv
  have : normSq' v = n := by
    have := normSq'_cast v
    rw [hv.2] at this
    exact_mod_cast this
  rw [this, rePoly8]

end NTKB.HardyWright.EighteenSquares
