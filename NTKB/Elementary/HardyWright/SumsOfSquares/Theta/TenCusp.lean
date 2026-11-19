/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TenExpSum
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.EightSquares

/-!
# The weight-`5` cusp form `∑_{a ∈ ℤ[i]} a⁴ e^{πi N(a) τ}`

`cuspC τ = ∑_{(m, n) ∈ ℤ²} (m + in)⁴ e^{πiτ(m² + n²)}`. Its transformation laws are those of `θ¹⁰`:

* `cuspC_S`: `C(-1/τ) = -i τ⁵ C(τ)`;
* `cuspC_add_two`: `C(τ + 2) = C(τ)`;
* `cuspC_TS`: `C(1 - 1/τ) = -i τ⁵ D(τ)` with
  `D(τ) = ∑_{(m, n)} (m + ½ + i(n + ½))⁴ e^{πiτ((m + ½)² + (n + ½)²)}` bounded on `Im τ ≥ 1`.

The proof: `P(z, τ) = θ(z, τ) θ(iz, τ) = ∑_{(m, n)} e^{2πi(m + in)z} e^{πiτ(m² + n²)}` (Mathlib's
`jacobiTheta₂`), and Mathlib's functional equation `jacobiTheta₂_functional_equation` for the two
factors gives `P(z/τ, -1/τ) = -iτ P(z, τ)`: the Gaussian factors `e^{πiz²/τ}` and `e^{πi(iz)²/τ}`
cancel. The coefficient of `z⁴` (`TenExpSum.lean`) is the law for `C`. For `TS` the same argument
with the half-integer shifts `θ(z + ½, ·) θ(iz + ½, ·)` and `θ(z + τ/2, τ) θ(iz + τ/2, τ)`.
-/

open Complex Filter Topology ModularForm ModularGroup
open scoped Real UpperHalfPlane MatrixGroups Manifold
open UpperHalfPlane hiding I

noncomputable section

namespace NTKB.HardyWright.TenSquares

/-! ### Shifted Gaussian lattice sums as exponential sums -/

/-- `s(v) e^{πiτ((m + α)² + (n + β)²)}`, `v = (m, n)`. -/
def cf (s : ℤ × ℤ → ℂ) (α β : ℝ) (τ : ℂ) (v : ℤ × ℤ) : ℂ :=
  s v * cexp (π * I * τ * (((v.1 : ℂ) + α) ^ 2 + ((v.2 : ℂ) + β) ^ 2))

/-- `2πi((m + α) + i(n + β))`. -/
def uf (α β : ℝ) (v : ℤ × ℤ) : ℂ := 2 * π * I * (((v.1 : ℂ) + α) + I * ((v.2 : ℂ) + β))

lemma norm_cexp_quad (τ : ℂ) (x y : ℝ) :
    ‖cexp (π * I * τ * (((x : ℂ)) ^ 2 + ((y : ℂ)) ^ 2))‖ = Real.exp (-π * τ.im * (x ^ 2 + y ^ 2)) := by
  rw [Complex.norm_exp]
  congr 1
  have e : ((x : ℂ)) ^ 2 + ((y : ℂ)) ^ 2 = ((x ^ 2 + y ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
  ring

lemma norm_cf_le {s : ℤ × ℤ → ℂ} (hs : ∀ v, ‖s v‖ ≤ 1) (α β : ℝ) (τ : ℂ) (v : ℤ × ℤ) :
    ‖cf s α β τ v‖ ≤ Real.exp (-π * τ.im * (((v.1 : ℝ) + α) ^ 2 + ((v.2 : ℝ) + β) ^ 2)) := by
  rw [cf, norm_mul]
  have e : (((v.1 : ℂ) + α) ^ 2 + ((v.2 : ℂ) + β) ^ 2) =
      ((((v.1 : ℝ) + α : ℝ) : ℂ)) ^ 2 + ((((v.2 : ℝ) + β : ℝ) : ℂ)) ^ 2 := by push_cast; ring
  rw [e, norm_cexp_quad]
  calc ‖s v‖ * _ ≤ 1 * _ := by gcongr; exact hs v
    _ = _ := one_mul _

lemma norm_uf_le (α β : ℝ) (hα : |α| ≤ 1) (hβ : |β| ≤ 1) (v : ℤ × ℤ) :
    ‖uf α β v‖ ≤ 2 * π * (|(v.1 : ℝ)| + |(v.2 : ℝ)| + 2) := by
  rw [uf, norm_mul]
  have h2pi : ‖(2 * π * I : ℂ)‖ = 2 * π := by
    simp [abs_of_pos Real.pi_pos]
  rw [h2pi]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have e1 : ((v.1 : ℂ) + α) = (((v.1 : ℝ) + α : ℝ) : ℂ) := by push_cast; ring
  have e2 : ((v.2 : ℂ) + β) = (((v.2 : ℝ) + β : ℝ) : ℂ) := by push_cast; ring
  rw [e1, e2]
  calc ‖(((v.1 : ℝ) + α : ℝ) : ℂ) + I * (((v.2 : ℝ) + β : ℝ) : ℂ)‖
      ≤ ‖(((v.1 : ℝ) + α : ℝ) : ℂ)‖ + ‖I * (((v.2 : ℝ) + β : ℝ) : ℂ)‖ := norm_add_le _ _
    _ = |(v.1 : ℝ) + α| + |(v.2 : ℝ) + β| := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ (|(v.1 : ℝ)| + |α|) + (|(v.2 : ℝ)| + |β|) := add_le_add (abs_add_le _ _) (abs_add_le _ _)
    _ ≤ _ := by linarith

lemma sq_add_ge (x α : ℝ) (hα : |α| ≤ 1) : x ^ 2 - 2 * |x| ≤ (x + α) ^ 2 := by
  have h1 : -(|x| * 1) ≤ x * α := by
    have := abs_mul x α
    have h2 : |x * α| ≤ |x| * 1 := by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hα (abs_nonneg x)
    linarith [neg_abs_le (x * α)]
  nlinarith [sq_nonneg α]

/-- The summability hypothesis of `TenExpSum.lean` for the shifted Gaussian lattice sums. -/
theorem expSummable_cf {s : ℤ × ℤ → ℂ} (hs : ∀ v, ‖s v‖ ≤ 1) {α β : ℝ} (hα : |α| ≤ 1)
    (hβ : |β| ≤ 1) {τ : ℂ} (hτ : 0 < τ.im) : ExpSummable (cf s α β τ) (uf α β) := by
  intro R
  set y := τ.im with hy
  set S := y + |R| with hS
  set f : ℤ → ℝ := fun m => Real.exp (-π * (y * (m : ℝ) ^ 2 - 2 * S * |(m : ℝ)|)) with hf
  have hfs : Summable f := by
    have := summable_pow_mul_jacobiTheta₂_term_bound S hτ 0
    simpa [hf] using this
  have hf0 : ∀ m, 0 ≤ f m := fun m => (Real.exp_pos _).le
  have hprod : Summable fun v : ℤ × ℤ => f v.1 * f v.2 := hfs.mul_of_nonneg hfs hf0 hf0
  refine Summable.of_nonneg_of_le (fun v => by positivity) (fun v => ?_)
    (hprod.mul_left (Real.exp (4 * π * |R|)))
  have h1 := norm_cf_le hs α β τ v
  have h2 := norm_uf_le α β hα hβ v
  have h3 : R * ‖uf α β v‖ ≤ |R| * (2 * π * (|(v.1 : ℝ)| + |(v.2 : ℝ)| + 2)) :=
    (le_abs_self R |>.trans (le_refl _)) |> fun _ =>
      (mul_le_mul_of_nonneg_right (le_abs_self R) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left h2 (abs_nonneg R))
  have q1 := sq_add_ge (v.1 : ℝ) α hα
  have q2 := sq_add_ge (v.2 : ℝ) β hβ
  have hpy : 0 < π * y := mul_pos Real.pi_pos hτ
  calc ‖cf s α β τ v‖ * Real.exp (R * ‖uf α β v‖)
      ≤ Real.exp (-π * y * (((v.1 : ℝ) + α) ^ 2 + ((v.2 : ℝ) + β) ^ 2)) *
          Real.exp (|R| * (2 * π * (|(v.1 : ℝ)| + |(v.2 : ℝ)| + 2))) := by
        gcongr
    _ = Real.exp (-π * y * (((v.1 : ℝ) + α) ^ 2 + ((v.2 : ℝ) + β) ^ 2) +
          |R| * (2 * π * (|(v.1 : ℝ)| + |(v.2 : ℝ)| + 2))) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (4 * π * |R| + (-π * (y * (v.1 : ℝ) ^ 2 - 2 * S * |(v.1 : ℝ)|) +
          -π * (y * (v.2 : ℝ) ^ 2 - 2 * S * |(v.2 : ℝ)|))) := by
        refine Real.exp_le_exp.mpr ?_
        rw [hS]
        nlinarith [abs_nonneg R, abs_nonneg (v.1 : ℝ), abs_nonneg (v.2 : ℝ), Real.pi_pos]
    _ = Real.exp (4 * π * |R|) * (f v.1 * f v.2) := by
        rw [hf, Real.exp_add, Real.exp_add]

/-! ### Products of two theta functions -/

lemma summable_norm_theta_term (w τ : ℂ) (hτ : 0 < τ.im) :
    Summable fun n : ℤ => ‖jacobiTheta₂_term n w τ‖ := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (summable_pow_mul_jacobiTheta₂_term_bound |w.im| hτ 0)
  simpa only [pow_zero, one_mul] using norm_jacobiTheta₂_term_le hτ le_rfl le_rfl n

lemma theta_mul_theta (z τ a b : ℂ) (hτ : 0 < τ.im) :
    jacobiTheta₂ (z + a) τ * jacobiTheta₂ (I * z + b) τ =
      ∑' v : ℤ × ℤ, cexp (2 * π * I * (v.1 * a + v.2 * b) + π * I * τ * ((v.1 : ℂ) ^ 2 + (v.2 : ℂ) ^ 2)) *
        cexp (2 * π * I * ((v.1 : ℂ) + I * v.2) * z) := by
  unfold jacobiTheta₂
  rw [tsum_mul_tsum_of_summable_norm (summable_norm_theta_term _ _ hτ)
    (summable_norm_theta_term _ _ hτ)]
  refine tsum_congr fun v => ?_
  simp only [jacobiTheta₂_term]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

/-- The sign `(-1)^{m+n} = e^{πi(m + n)}`. -/
def sgn (v : ℤ × ℤ) : ℂ := cexp (π * I * ((v.1 : ℂ) + v.2))

lemma norm_sgn (v : ℤ × ℤ) : ‖sgn v‖ ≤ 1 := by
  rw [sgn, Complex.norm_exp]
  simp [Complex.mul_re]

lemma norm_one_le : ∀ _ : ℤ × ℤ, ‖(1 : ℂ)‖ ≤ 1 := fun _ => by simp

/-- `θ(z, τ) θ(iz, τ)`. -/
lemma theta_prod_zero (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiTheta₂ z τ * jacobiTheta₂ (I * z) τ = expSum (cf (fun _ => 1) 0 0 τ) (uf 0 0) z := by
  have h := theta_mul_theta z τ 0 0 hτ
  simp only [add_zero] at h
  rw [h, expSum]
  refine tsum_congr fun v => ?_
  simp only [cf, uf, one_mul, Complex.ofReal_zero, add_zero, mul_zero, zero_add]

/-- `θ(z + ½, τ) θ(iz + ½, τ)`. -/
lemma theta_prod_half (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiTheta₂ (z + 1 / 2) τ * jacobiTheta₂ (I * z + 1 / 2) τ =
      expSum (cf sgn 0 0 τ) (uf 0 0) z := by
  rw [theta_mul_theta z τ _ _ hτ, expSum]
  refine tsum_congr fun v => ?_
  simp only [cf, uf, sgn, Complex.ofReal_zero, add_zero]
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

/-- `e^{πiτ/2} e^{πi(1+i)z} θ(z + τ/2, τ) θ(iz + τ/2, τ)`. -/
lemma theta_prod_shift (z τ : ℂ) (hτ : 0 < τ.im) :
    cexp (π * I * τ / 2) * cexp (π * I * (1 + I) * z) *
        (jacobiTheta₂ (z + τ / 2) τ * jacobiTheta₂ (I * z + τ / 2) τ) =
      expSum (cf (fun _ => 1) (1 / 2) (1 / 2) τ) (uf (1 / 2) (1 / 2)) z := by
  rw [theta_mul_theta z τ _ _ hτ, expSum, ← tsum_mul_left]
  refine tsum_congr fun v => ?_
  simp only [cf, uf, one_mul]
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf

/-! ### The functional equation of the theta products -/

lemma neg_I_mul_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : -I * τ ≠ 0 := by
  have : τ ≠ 0 := fun h => by simp [h] at hτ
  exact mul_ne_zero (neg_ne_zero.mpr I_ne_zero) this

lemma cpow_half_sq (w : ℂ) : (w ^ (1 / 2 : ℂ)) ^ 2 = w := by
  rw [one_div]; exact cpow_ofNat_inv_pow w 2

lemma im_neg_inv_pos {τ : ℂ} (hτ : 0 < τ.im) : 0 < (-1 / τ).im := by
  have : τ ≠ 0 := fun h => by simp [h] at hτ
  rw [neg_div, neg_im, one_div, inv_im, neg_div, neg_neg]
  exact div_pos hτ (normSq_pos.mpr this)

/-- `θ(w₁, τ) θ(w₂, τ)` in terms of `θ(w₁/τ, -1/τ) θ(w₂/τ, -1/τ)`. -/
lemma theta_prod_fe (w₁ w₂ τ : ℂ) (hτ : 0 < τ.im) :
    jacobiTheta₂ (w₁ / τ) (-1 / τ) * jacobiTheta₂ (w₂ / τ) (-1 / τ) =
      (-I * τ) * cexp (π * I * (w₁ ^ 2 + w₂ ^ 2) / τ) * (jacobiTheta₂ w₁ τ * jacobiTheta₂ w₂ τ) := by
  rw [jacobiTheta₂_functional_equation w₁ τ, jacobiTheta₂_functional_equation w₂ τ]
  set A := jacobiTheta₂ (w₁ / τ) (-1 / τ)
  set B := jacobiTheta₂ (w₂ / τ) (-1 / τ)
  have h0 := neg_I_mul_ne_zero hτ
  have hs : ((-I * τ) ^ (1 / 2 : ℂ)) ≠ 0 := by
    intro h
    have := cpow_half_sq (-I * τ)
    rw [h] at this
    exact h0 (by rw [← this]; ring)
  have e : (-I * τ) * ((1 / (-I * τ) ^ (1 / 2 : ℂ)) * (1 / (-I * τ) ^ (1 / 2 : ℂ))) = 1 := by
    rw [div_mul_div_comm, one_mul, ← sq, cpow_half_sq]
    field_simp
    exact div_self (right_ne_zero_of_mul h0)
  have ex : cexp (π * I * (w₁ ^ 2 + w₂ ^ 2) / τ) * (cexp (-π * I * w₁ ^ 2 / τ) *
      cexp (-π * I * w₂ ^ 2 / τ)) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    ring
  linear_combination (-(A * B) * (cexp (π * I * (w₁ ^ 2 + w₂ ^ 2) / τ) *
    (cexp (-π * I * w₁ ^ 2 / τ) * cexp (-π * I * w₂ ^ 2 / τ)))) * e + (-(A * B)) * ex

/-! ### The cusp form `C` and its laws -/

/-- `C(τ) = ∑_{(m, n) ∈ ℤ²} (m + in)⁴ e^{πiτ(m² + n²)}`.
  **Restriction:** the lattice sum converges (absolutely) only for $\operatorname{Im}\tau > 0$; elsewhere the value
  is $0$ by Lean's `tsum` convention, not an analytic continuation or the intended value. -/
def cuspC (τ : ℂ) : ℂ :=
  ∑' v : ℤ × ℤ, ((v.1 : ℂ) + I * v.2) ^ 4 * cexp (π * I * τ * ((v.1 : ℂ) ^ 2 + (v.2 : ℂ) ^ 2))

/-- `D(τ) = ∑_{(m, n) ∈ ℤ²} (m + ½ + i(n + ½))⁴ e^{πiτ((m + ½)² + (n + ½)²)}`. -/
def cuspD (τ : ℂ) : ℂ :=
  ∑' v : ℤ × ℤ, (((v.1 : ℂ) + 1 / 2) + I * ((v.2 : ℂ) + 1 / 2)) ^ 4 *
    cexp (π * I * τ * (((v.1 : ℂ) + 1 / 2) ^ 2 + ((v.2 : ℂ) + 1 / 2) ^ 2))

lemma uf_pow_four (α β : ℝ) (v : ℤ × ℤ) :
    uf α β v ^ 4 = (2 * π) ^ 4 * (((v.1 : ℂ) + α) + I * ((v.2 : ℂ) + β)) ^ 4 := by
  rw [uf, mul_pow, mul_pow, mul_pow, I_pow_four]; ring

lemma sum_cf_zero (τ : ℂ) :
    ∑' v, cf (fun _ => 1) 0 0 τ v * uf 0 0 v ^ 4 = (2 * π) ^ 4 * cuspC τ := by
  rw [cuspC, ← tsum_mul_left]
  refine tsum_congr fun v => ?_
  rw [uf_pow_four]
  simp only [cf, Complex.ofReal_zero, add_zero, one_mul]
  ring

lemma sum_cf_half (τ : ℂ) :
    ∑' v, cf (fun _ => 1) (1 / 2) (1 / 2) τ v * uf (1 / 2) (1 / 2) v ^ 4 =
      (2 * π) ^ 4 * cuspD τ := by
  rw [cuspD, ← tsum_mul_left]
  refine tsum_congr fun v => ?_
  rw [uf_pow_four]
  simp only [cf, one_mul]
  push_cast
  ring

lemma cexp_pi_I_sq (m : ℤ) : cexp (π * I * (m : ℂ) ^ 2) = cexp (π * I * m) := by
  obtain ⟨k, hk⟩ := Int.even_mul_pred_self m
  have e : π * I * (m : ℂ) ^ 2 = π * I * m + k * (2 * π * I) := by
    have : ((m * (m - 1) : ℤ) : ℂ) = ((k + k : ℤ) : ℂ) := by rw [hk]
    push_cast at this
    linear_combination π * I * this
  rw [e, Complex.exp_add, exp_int_mul_two_pi_mul_I, mul_one]

lemma sum_cf_sgn (τ : ℂ) :
    ∑' v, cf sgn 0 0 τ v * uf 0 0 v ^ 4 = (2 * π) ^ 4 * cuspC (1 + τ) := by
  rw [cuspC, ← tsum_mul_left]
  refine tsum_congr fun v => ?_
  rw [uf_pow_four]
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

lemma expSummable_zero {τ : ℂ} (hτ : 0 < τ.im) : ExpSummable (cf (fun _ => 1) 0 0 τ) (uf 0 0) :=
  expSummable_cf norm_one_le (by simp) (by simp) hτ

lemma expSummable_sgn {τ : ℂ} (hτ : 0 < τ.im) : ExpSummable (cf sgn 0 0 τ) (uf 0 0) :=
  expSummable_cf norm_sgn (by simp) (by simp) hτ

lemma abs_half_le : |(1 / 2 : ℝ)| ≤ 1 := by rw [abs_of_pos (by norm_num)]; norm_num

lemma expSummable_half {τ : ℂ} (hτ : 0 < τ.im) :
    ExpSummable (cf (fun _ => 1) (1 / 2) (1 / 2) τ) (uf (1 / 2) (1 / 2)) :=
  expSummable_cf norm_one_le abs_half_le abs_half_le hτ

lemma ne_zero_of_im_pos {τ : ℂ} (hτ : 0 < τ.im) : τ ≠ 0 := fun h => by simp [h] at hτ

/-- **The `S`-law of `C`.** `C(-1/τ) = -i τ⁵ C(τ)`. -/
theorem cuspC_S {τ : ℂ} (hτ : 0 < τ.im) : cuspC (-1 / τ) = -I * τ ^ 5 * cuspC τ := by
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
  have hc := coeff_eq_of_expSum_eq (expSummable_zero hτ') (expSummable_zero hτ) τ⁻¹ (-I * τ) hfe 4
  rw [sum_cf_zero, sum_cf_zero] at hc
  have hπ : (2 * (π : ℂ)) ^ 4 ≠ 0 := pow_ne_zero _ (mul_ne_zero two_ne_zero
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have h4 : τ⁻¹ ^ 4 * τ ^ 4 = 1 := by rw [← mul_pow, inv_mul_cancel₀ h0, one_pow]
  have hc' : τ ^ 4 * (τ⁻¹ ^ 4 * ((2 * π) ^ 4 * cuspC (-1 / τ))) =
      τ ^ 4 * (-I * τ * ((2 * π) ^ 4 * cuspC τ)) := by rw [hc]
  apply mul_left_cancel₀ hπ
  linear_combination hc' - ((2 * (π : ℂ)) ^ 4 * cuspC (-1 / τ)) * h4

/-- **The `TS`-law of `C`.** `C(1 - 1/τ) = -i τ⁵ D(τ)`. -/
theorem cuspC_TS {τ : ℂ} (hτ : 0 < τ.im) : cuspC (1 + -1 / τ) = -I * τ ^ 5 * cuspD τ := by
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
  have hc := coeff_eq_of_expSum_eq (expSummable_sgn hτ') (expSummable_half hτ) τ⁻¹ (-I * τ) hfe 4
  rw [sum_cf_sgn, sum_cf_half] at hc
  have hπ : (2 * (π : ℂ)) ^ 4 ≠ 0 := pow_ne_zero _ (mul_ne_zero two_ne_zero
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have h4 : τ⁻¹ ^ 4 * τ ^ 4 = 1 := by rw [← mul_pow, inv_mul_cancel₀ h0, one_pow]
  have hc' : τ ^ 4 * (τ⁻¹ ^ 4 * ((2 * π) ^ 4 * cuspC (1 + -1 / τ))) =
      τ ^ 4 * (-I * τ * ((2 * π) ^ 4 * cuspD τ)) := by rw [hc]
  apply mul_left_cancel₀ hπ
  linear_combination hc' - ((2 * (π : ℂ)) ^ 4 * cuspC (1 + -1 / τ)) * h4

/-- `C(τ + 2) = C(τ)`. -/
theorem cuspC_add_two (τ : ℂ) : cuspC (τ + 2) = cuspC τ := by
  rw [cuspC, cuspC]
  refine tsum_congr fun v => ?_
  congr 1
  have : π * I * (τ + 2) * ((v.1 : ℂ) ^ 2 + (v.2 : ℂ) ^ 2) =
      π * I * τ * ((v.1 : ℂ) ^ 2 + (v.2 : ℂ) ^ 2) + ((v.1 ^ 2 + v.2 ^ 2 : ℤ) : ℂ) * (2 * π * I) := by
    push_cast; ring
  rw [this, Complex.exp_add, exp_int_mul_two_pi_mul_I, mul_one]
