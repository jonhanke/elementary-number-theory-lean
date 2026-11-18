/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.EighteenTheta
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.EighteenSeriesBounds
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.EighteenVanish
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.SixteenBounds

/-!
# Bounds for the proof of the `r₁₈` formula

The two cusp forms `f = θ⁶ η¹²` and `C₈` (weight `9`, the laws of `θ¹⁸`) and
`g(τ) = κ θ(τ)¹⁸ - L_W(τ) - c₁ f(τ) - c₂ C₈(τ)` (`gfun`), with `a = π⁹/20160`, `b = π⁹/5160960`,
`c₁ = (-36κ + 240a - 15b)/4`, `c₂ = (180κ - 244a + 11b)/16`: the constants make the coefficients
of `q¹` and `q²` (`q = e^{πiτ}`) vanish (the coefficient of `q⁰` vanishes by the choice of `κ`, the
row `0` of `L_W`).

* `gfun_S`, `gfun_T_sq`: `g(-1/τ) = -i τ⁹ g(τ)`, `g(τ + 2) = g(τ)`;
* `norm_gfun_le`: `‖g(τ)‖ ≤ C e^{-3π Im τ}` for `Im τ ≥ 1`;
* `gfun_TS`, `norm_gTS_le`: `τ⁻⁹ g(TSτ)` is bounded on `Im τ ≥ 1`, `|Re τ| ≤ 1`.
-/

open ModularForm ModularGroup Complex Filter Topology EisensteinSeries Matrix
open scoped MatrixGroups Real UpperHalfPlane Manifold
open UpperHalfPlane hiding I

noncomputable section

namespace NTKB.HardyWright

/-- `|Re (a + bi)⁸| ≤ (a² + b²)⁴`. -/
lemma abs_octicRe_le (a b : ℤ) : |(octicRe a b : ℝ)| ≤ ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) ^ 4 := by
  unfold octicRe
  push_cast
  set s : ℝ := (a : ℝ) ^ 2 with hs
  set t : ℝ := (b : ℝ) ^ 2 with ht
  have e : (a : ℝ) ^ 8 - 28 * (a : ℝ) ^ 6 * (b : ℝ) ^ 2 + 70 * (a : ℝ) ^ 4 * (b : ℝ) ^ 4 -
      28 * (a : ℝ) ^ 2 * (b : ℝ) ^ 6 + (b : ℝ) ^ 8 =
      s ^ 4 - 28 * s ^ 3 * t + 70 * s ^ 2 * t ^ 2 - 28 * s * t ^ 3 + t ^ 4 := by
    rw [hs, ht]; ring
  rw [e]
  have hs0 : 0 ≤ s := by positivity
  have ht0 : 0 ≤ t := by positivity
  have h1 : 0 ≤ s * t * (s - t) ^ 2 := by positivity
  have h2 : 0 ≤ (s ^ 2 - 6 * s * t + t ^ 2) ^ 2 := sq_nonneg _
  rw [abs_le]
  constructor <;> nlinarith [h1, h2]

/-- `|c₈(n)| ≤ n⁴ (2n + 1)²`. -/
lemma abs_octicCoeff_le (n : ℕ) : |(octicCoeff n : ℝ)| ≤ (n : ℝ) ^ 4 * (2 * n + 1) ^ 2 := by
  set S := ((Finset.Icc (-(n : ℤ)) n) ×ˢ (Finset.Icc (-(n : ℤ)) n)).filter
      (fun v : ℤ × ℤ => v.1 ^ 2 + v.2 ^ 2 = n) with hS
  have hcard : (S.card : ℝ) ≤ (2 * n + 1) ^ 2 := by
    have h1 : S.card ≤ ((Finset.Icc (-(n : ℤ)) n) ×ˢ (Finset.Icc (-(n : ℤ)) n)).card :=
      Finset.card_filter_le _ _
    rw [Finset.card_product, Int.card_Icc] at h1
    have : ((n : ℤ) + 1 - -(n : ℤ)).toNat = 2 * n + 1 := by omega
    rw [this] at h1
    exact_mod_cast (h1.trans_eq (by ring))
  have hterm : ∀ v ∈ S, |(octicRe v.1 v.2 : ℝ)| ≤ (n : ℝ) ^ 4 := by
    intro v hv
    have h : v.1 ^ 2 + v.2 ^ 2 = (n : ℤ) := (Finset.mem_filter.1 hv).2
    have h' : ((v.1 : ℝ)) ^ 2 + (v.2 : ℝ) ^ 2 = n := by exact_mod_cast h
    rw [← h']; exact abs_octicRe_le _ _
  unfold octicCoeff
  rw [← hS, Int.cast_sum]
  have hn4 : (0 : ℝ) ≤ (n : ℝ) ^ 4 := by positivity
  calc |∑ v ∈ S, ((octicRe v.1 v.2 : ℤ) : ℝ)|
      ≤ ∑ v ∈ S, |((octicRe v.1 v.2 : ℤ) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v ∈ S, (n : ℝ) ^ 4 := Finset.sum_le_sum hterm
    _ = S.card * (n : ℝ) ^ 4 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * n + 1) ^ 2 * (n : ℝ) ^ 4 := mul_le_mul_of_nonneg_right hcard hn4
    _ = _ := by ring

/-- The real series `∑ c₈(n) xⁿ` converges absolutely for `0 ≤ x < 1`. -/
lemma summable_octicCoeff_abs {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    Summable fun n : ℕ => |(octicCoeff n : ℝ)| * x ^ n := by
  have hn : ‖x‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx
  have h4 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 4 hn
  have h5 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 5 hn
  have h6 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 6 hn
  have hb : Summable fun n : ℕ => 4 * ((n : ℝ) ^ 6 * x ^ n) + 4 * ((n : ℝ) ^ 5 * x ^ n)
      + ((n : ℝ) ^ 4 * x ^ n) := ((h6.mul_left 4).add (h5.mul_left 4)).add h4
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hb
  have := mul_le_mul_of_nonneg_right (abs_octicCoeff_le n) (pow_nonneg hx0 n)
  refine this.trans (le_of_eq ?_)
  ring

lemma octicCoeff_zero : octicCoeff 0 = 0 := by decide

lemma octicCoeff_one : octicCoeff 1 = 4 := by decide

lemma octicCoeff_two : octicCoeff 2 = 64 := by decide

lemma octicCoeff_three : octicCoeff 3 = 0 := by decide

namespace EighteenSquares

open EightSquares (K1 ne_zero' norm_jacobiTheta_sub_one_le' norm_jacobiTheta_sub_le mdiff_of_eqOn
  theta_T_sq coe_TS_smul jacobiTheta_one_add norm_jacobiTheta₂_half_le)
open SixSquares (exp_neg_pi_im_le_quarter norm_q norm_cexp_le_one_of_re one_div_neg_I_div)
open TwelveSquares (eta12 eta12_S eta12_T_sq eta12_TS mdiff_eta12 norm_eta12_le Ceta Ceta_nonneg
  hasSum_eta12 hasSum_Ceta etaTwelveCoeff_zero etaTwelveCoeff_one etaTwelveCoeff_two)
open SixteenSquares (norm_eta12_sub3_le mdiff_theta)

/-! ### Power series to third order -/

/-- A power series with `c₀ = 0` is `c₁ q + c₂ q² + O(q³)`. -/
lemma norm_sub_of_hasSum3' {c : ℕ → ℂ} {F q : ℂ} (hF : HasSum (fun n => c n * q ^ n) F)
    (h0 : c 0 = 0) (hq : ‖q‖ ≤ 1 / 2) {M : ℝ}
    (hM : HasSum (fun n => ‖c n‖ * (1 / 2) ^ n) M) :
    ‖F - c 1 * q - c 2 * q ^ 2‖ ≤ 8 * M * ‖q‖ ^ 3 := by
  have h3 : HasSum (fun n => c (n + 3) * q ^ (n + 3)) (F - c 1 * q - c 2 * q ^ 2) := by
    have := (hasSum_nat_add_iff' (f := fun n => c n * q ^ n) 3).mpr hF
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, h0] at this
    convert this using 1
    ring
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

/-! ### The cusp form `C₈ = 4q + 64q² + O(q³)` -/

/-- `Co = ∑ |c₈(n)| 2⁻ⁿ`. -/
def Co : ℝ := ∑' n : ℕ, ‖(octicCoeff n : ℂ)‖ * (1 / 2) ^ n

lemma Co_nonneg : 0 ≤ Co := tsum_nonneg fun n => by positivity

lemma hasSum_Co : HasSum (fun n : ℕ => ‖(octicCoeff n : ℂ)‖ * (1 / 2) ^ n) Co := by
  refine Summable.hasSum ?_
  refine (summable_octicCoeff_abs (x := 1 / 2) (by norm_num) (by norm_num)).congr fun n => ?_
  rw [Complex.norm_intCast]

lemma norm_oct_sub_le (τ : ℍ) (hτ : 1 ≤ τ.im) :
    ‖oct τ - 4 * cexp (π * I * τ) - 64 * cexp (π * I * τ) ^ 2‖ ≤ 8 * Co * ‖cexp (π * I * τ)‖ ^ 3 := by
  have hq : ‖cexp (π * I * τ)‖ ≤ 1 / 2 := by
    rw [norm_q]; linarith [exp_neg_pi_im_le_quarter hτ]
  have h := norm_sub_of_hasSum3' (hasSum_octC τ.2) (by simp [octicCoeff_zero]) hq hasSum_Co
  simp only [octicCoeff_one, octicCoeff_two, Int.cast_ofNat] at h
  exact h

/-! ### The cusp form `f = θ⁶ η¹²` -/

/-- `f(τ) = θ(τ)⁶ η(τ)¹²`. -/
def cuspF (τ : ℍ) : ℂ := jacobiTheta τ ^ 6 * eta12 τ

lemma cuspF_S (τ : ℍ) : cuspF (S • τ) = -I * (τ : ℂ) ^ 9 * cuspF τ := by
  rw [cuspF, cuspF, theta6_S, eta12_S]; ring

lemma cuspF_T_sq (τ : ℍ) : cuspF (T ^ (2 : ℤ) • τ) = cuspF τ := by
  rw [cuspF, cuspF, theta_T_sq, eta12_T_sq]

/-- `τ⁻⁹ f(TSτ)`. -/
def cuspFTS (τ : ℍ) : ℂ := thetaTS6 τ * eta12 τ

lemma cuspF_TS (τ : ℍ) : cuspF ((T * S) • τ) = (τ : ℂ) ^ 9 * cuspFTS τ := by
  rw [cuspF, theta6_TS, eta12_TS, cuspFTS]; ring

lemma mdiff_cuspF : MDiff cuspF := (mdiff_theta.pow 6).mul mdiff_eta12

lemma norm_cuspFTS_le (τ : ℍ) (hτ : 1 ≤ τ.im) : ‖cuspFTS τ‖ ≤ K1 ^ 6 * (1 + 4 * Ceta) := by
  rw [cuspFTS, norm_mul]
  gcongr
  · exact norm_thetaTS6_le τ hτ
  · exact norm_eta12_le τ hτ

/-- The constant of `norm_cuspF_sub_le`. -/
def Cf : ℝ := 64 * (8 * Ceta) + 6150

lemma norm_cuspF_sub_le (τ : ℍ) (hτ : 1 ≤ τ.im) :
    ‖cuspF τ - cexp (π * I * τ) - 12 * cexp (π * I * τ) ^ 2‖ ≤ Cf * ‖cexp (π * I * τ)‖ ^ 3 := by
  set q := cexp (π * I * τ) with hq
  have hqn : ‖q‖ = rexp (-π * τ.im) := norm_q τ
  have ht : ‖q‖ ≤ 1 / 4 := by rw [hqn]; exact exp_neg_pi_im_le_quarter hτ
  have ht0 := norm_nonneg q
  have hRb := norm_eta12_sub3_le τ hτ
  have hRa := norm_theta6_sub_le (τ := (τ : ℂ)) (by simpa using hτ)
  have hw := norm_jacobiTheta_sub_one_le' (τ := (τ : ℂ)) (by simpa using hτ)
  have hi : (τ : ℂ).im = τ.im := rfl
  rw [hi, ← hqn] at hw
  have hθ : ‖jacobiTheta τ‖ ≤ 2 := by
    calc ‖jacobiTheta τ‖ = ‖(jacobiTheta τ - 1) + 1‖ := by ring_nf
      _ ≤ ‖jacobiTheta τ - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 2 := by rw [norm_one]; linarith
  have hA : ‖jacobiTheta τ ^ 6‖ ≤ 64 := by
    rw [norm_pow]
    calc ‖jacobiTheta τ‖ ^ 6 ≤ 2 ^ 6 := pow_le_pow_left₀ (norm_nonneg _) hθ 6
      _ = 64 := by norm_num
  have hCeta := Ceta_nonneg
  have e : cuspF τ - q - 12 * q ^ 2 = (eta12 τ - q) * jacobiTheta τ ^ 6 +
      q * (jacobiTheta τ ^ 6 - 1 - 12 * q) := by
    rw [cuspF]; ring
  rw [e]
  calc _ ≤ ‖(eta12 τ - q) * jacobiTheta τ ^ 6‖ + ‖q * (jacobiTheta τ ^ 6 - 1 - 12 * q)‖ :=
        norm_add_le _ _
    _ ≤ (8 * Ceta * ‖q‖ ^ 3) * 64 + ‖q‖ * (6150 * ‖q‖ ^ 2) := by
        rw [norm_mul, norm_mul]
        gcongr
    _ ≤ Cf * ‖q‖ ^ 3 := by
        have : 0 ≤ ‖q‖ ^ 3 := by positivity
        rw [Cf]; nlinarith

/-! ### `g = κ θ¹⁸ - L_W - c₁ f - c₂ C₈` -/

/-- `a = π⁹/20160`, the coefficient of `B` in `L_W`. -/
def aB : ℂ := π ^ 9 / 20160

/-- `b = π⁹/5160960`, the coefficient of `A` in `L_W`. -/
def bA : ℂ := π ^ 9 / 5160960

/-- `c₁ = (-36κ + 240a - 15b)/4`. -/
def c1 : ℂ := (-36 * kappa + 240 * aB - 15 * bA) / 4

/-- `c₂ = (180κ - 244a + 11b)/16`. -/
def c2 : ℂ := (180 * kappa - 244 * aB + 11 * bA) / 16

/-- `g(τ) = κ θ(τ)¹⁸ - L_W(τ) - c₁ f(τ) - c₂ C₈(τ)`. -/
def gfun (τ : ℍ) : ℂ := kappa * jacobiTheta τ ^ 18 - Lsum9 W τ - c1 * cuspF τ - c2 * oct τ

lemma gfun_S (τ : ℍ) : gfun (S • τ) = -I * (τ : ℂ) ^ 9 * gfun τ := by
  rw [gfun, gfun, theta18_S, Lsum9_W_S, cuspF_S, oct_S]; ring

lemma gfun_T_sq (τ : ℍ) : gfun (T ^ (2 : ℤ) • τ) = gfun τ := by
  rw [gfun, gfun, theta_T_sq, Lsum9_W_T2, cuspF_T_sq, oct_T_sq]

/-- `τ⁻⁹ g(TSτ)`. -/
def gTS (τ : ℍ) : ℂ := kappa * thetaTS18 τ - Lsum9 Wp τ - c1 * cuspFTS τ - c2 * octTS τ

lemma gfun_TS (τ : ℍ) : gfun ((T * S) • τ) = (τ : ℂ) ^ 9 * gTS τ := by
  rw [gfun, theta18_TS, Lsum9_W_TS, cuspF_TS, oct_TS, gTS]; ring

lemma mdiff_gfun : MDiff gfun := by
  have h1 : MDiff (fun τ : ℍ => kappa * jacobiTheta τ ^ 18) := fun τ =>
    (mdifferentiableAt_const (c := kappa)).mul ((mdiff_theta.pow 18) τ)
  have h3 : MDiff (fun τ : ℍ => c1 * cuspF τ) := fun τ =>
    (mdifferentiableAt_const (c := c1)).mul (mdiff_cuspF τ)
  have h4 : MDiff (fun τ : ℍ => c2 * oct τ) := fun τ =>
    (mdifferentiableAt_const (c := c2)).mul (mdiff_oct τ)
  exact ((h1.sub (mdiff_Lsum9 norm_W_le)).sub h3).sub h4

lemma norm_aB : ‖aB‖ = π ^ 9 / 20160 := by
  rw [aB, norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  norm_num

lemma norm_bA : ‖bA‖ = π ^ 9 / 5160960 := by
  rw [bA, norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  norm_num

/-- The constant of `norm_gfun_le`. -/
def Cg : ℝ := ‖kappa‖ * (324 * 262144 * 64 + 200) + π ^ 9 / 20160 * CB3 + π ^ 9 / 5160960 * CA3 +
  ‖c1‖ * Cf + ‖c2‖ * (8 * Co)

lemma norm_gfun_le (τ : ℍ) (hτ : 1 ≤ τ.im) : ‖gfun τ‖ ≤ Cg * rexp (-3 * π * τ.im) := by
  set q := cexp (π * I * τ) with hq
  have hqn : ‖q‖ = rexp (-π * τ.im) := norm_q τ
  have hq2 : ‖q‖ ≤ 1 / 2 := by rw [hqn]; linarith [exp_neg_pi_im_le_quarter hτ]
  have hqq : ‖q‖ ^ 3 = rexp (-3 * π * τ.im) := by
    rw [hqn, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e : gfun τ = kappa * (jacobiTheta τ ^ 18 - 1 - 36 * q - 612 * q ^ 2) -
      aB * (seriesB q - q - 256 * q ^ 2) - bA * (seriesA q - q - q ^ 2) -
      c1 * (cuspF τ - q - 12 * q ^ 2) - c2 * (oct τ - 4 * q - 64 * q ^ 2) := by
    rw [gfun, Lsum9_W_eq, c1, c2, aB, bA]; ring
  rw [e]
  have h1 := norm_theta18_sub_le (τ := (τ : ℂ)) (by simpa using hτ)
  have h2 := norm_seriesB_sub3_le hq2
  have h2' := norm_seriesA_sub3_le hq2
  have h3 := norm_cuspF_sub_le τ hτ
  have h4 := norm_oct_sub_le τ hτ
  rw [← hq] at h1 h3 h4
  rw [hqq] at h1 h2 h2' h3 h4
  calc _ ≤ ‖kappa * (jacobiTheta τ ^ 18 - 1 - 36 * q - 612 * q ^ 2)‖ +
        ‖aB * (seriesB q - q - 256 * q ^ 2)‖ + ‖bA * (seriesA q - q - q ^ 2)‖ +
        ‖c1 * (cuspF τ - q - 12 * q ^ 2)‖ + ‖c2 * (oct τ - 4 * q - 64 * q ^ 2)‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        refine (norm_sub_le _ _).trans ?_
        gcongr
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ ‖kappa‖ * ((324 * 262144 * 64 + 200) * rexp (-3 * π * τ.im)) +
          π ^ 9 / 20160 * (CB3 * rexp (-3 * π * τ.im)) +
          π ^ 9 / 5160960 * (CA3 * rexp (-3 * π * τ.im)) +
          ‖c1‖ * (Cf * rexp (-3 * π * τ.im)) + ‖c2‖ * (8 * Co * rexp (-3 * π * τ.im)) := by
        rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_aB, norm_bA]
        gcongr
    _ = Cg * rexp (-3 * π * τ.im) := by rw [Cg]; ring

/-- The constant of `norm_gTS_le`. -/
def MTS : ℝ := ‖kappa‖ * K1 ^ 18 + ML9 + ‖c1‖ * (K1 ^ 6 * (1 + 4 * Ceta)) + ‖c2‖ * MTSc8

lemma norm_gTS_le (τ : ℍ) (hτ : 1 ≤ τ.im) (hr : |τ.re| ≤ 1) : ‖gTS τ‖ ≤ MTS := by
  rw [gTS, MTS]
  calc ‖kappa * thetaTS18 τ - Lsum9 Wp τ - c1 * cuspFTS τ - c2 * octTS τ‖
      ≤ ‖kappa * thetaTS18 τ‖ + ‖Lsum9 Wp τ‖ + ‖c1 * cuspFTS τ‖ + ‖c2 * octTS τ‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ ‖kappa‖ * K1 ^ 18 + ML9 + ‖c1‖ * (K1 ^ 6 * (1 + 4 * Ceta)) + ‖c2‖ * MTSc8 := by
        rw [norm_mul, norm_mul, norm_mul]
        gcongr
        · exact norm_thetaTS18_le τ hτ
        · exact norm_Lsum9_Wp_le τ hτ hr
        · exact norm_cuspFTS_le τ hτ
        · exact norm_octTS_le τ hτ

end EighteenSquares

end NTKB.HardyWright
