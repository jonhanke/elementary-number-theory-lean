/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TwelveExpansion
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TwelveEta
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TwelveProduct
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.SixBounds

/-!
# Bounds for the proof of Glaisher's `r₁₂` formula

`g(τ) = κ θ(τ)¹² - L_W(τ) - c η(τ)¹²` with `c = 24κ - π⁶/60` (`gfun`), the constant `c` chosen
so that the coefficient of `q = e^{πiτ}` vanishes.

* `gfun_S`, `gfun_T_sq`: `g(-1/τ) = -τ⁶ g(τ)`, `g(τ + 2) = g(τ)`;
* `norm_gfun_le`: `‖g(τ)‖ ≤ C e^{-2π Im τ}` for `Im τ ≥ 1`, from
  `θ¹² = 1 + 24q + O(q²)`, `L_W = κ + (π⁶/60)(q + O(q²))` (`TwelveExpansion.lean`) and
  `η¹² = q + O(q²)` (the coefficients of `TwelveProduct.lean`);
* `gfun_TS`, `norm_gfun_TS_le`: `τ⁻⁶ g(TSτ)` is bounded on `Im τ ≥ 1`, `|Re τ| ≤ 1`.
-/

open ModularForm ModularGroup Complex Filter Topology EisensteinSeries Matrix
open scoped MatrixGroups Real UpperHalfPlane Manifold
open UpperHalfPlane hiding I

noncomputable section

namespace NTKB.HardyWright.TwelveSquares

open EightSquares (K1 ne_zero' exp_neg_pi_le_half norm_jacobiTheta_sub_one_le'
  norm_jacobiTheta_sub_le mdiff_of_eqOn theta_T_sq)
open SixSquares (theta6_S theta6_TS norm_theta6_TS_part_le exp_neg_pi_im_le_quarter norm_q
  pow_le_aux)

/-! ### `θ¹²` -/

lemma theta12_S (τ : ℍ) : jacobiTheta ↑(S • τ) ^ 12 = -((τ : ℂ) ^ 6 * jacobiTheta τ ^ 12) := by
  rw [show (12 : ℕ) = 6 * 2 from rfl, pow_mul, theta6_S]
  linear_combination ((τ : ℂ) ^ 6 * (jacobiTheta τ ^ 6) ^ 2) * I_sq

/-- The factor of `θ((τ-1)/τ)¹²`. -/
def thetaTS (τ : ℍ) : ℂ := (I * (cexp (3 * π * I * τ / 2) * jacobiTheta₂ (-(τ : ℂ) / 2) τ ^ 6)) ^ 2

lemma theta12_TS (τ : ℍ) : jacobiTheta (((T * S) • τ : ℍ) : ℂ) ^ 12 = (τ : ℂ) ^ 6 * thetaTS τ := by
  rw [show (12 : ℕ) = 6 * 2 from rfl, pow_mul, theta6_TS, thetaTS]
  ring

lemma norm_thetaTS_le (τ : ℍ) (hτ : 1 ≤ τ.im) : ‖thetaTS τ‖ ≤ K1 ^ 12 := by
  rw [thetaTS, norm_pow, show (12 : ℕ) = 6 * 2 from rfl, pow_mul]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_theta6_TS_part_le τ hτ) 2

/-- `‖(1 + w)ⁿ - 1 - n w‖ ≤ n 2ⁿ ‖w‖²` for `‖w‖ ≤ 1`. -/
lemma norm_one_add_pow_sub_le {w : ℂ} (hw : ‖w‖ ≤ 1) (n : ℕ) :
    ‖(1 + w) ^ n - 1 - n * w‖ ≤ n * 2 ^ n * ‖w‖ ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (1 + w) ^ (n + 1) - 1 - ((n + 1 : ℕ) : ℂ) * w =
        (1 + w) * ((1 + w) ^ n - 1 - n * w) + n * w ^ 2 := by push_cast; ring
    rw [e]
    have h1 : ‖1 + w‖ ≤ 2 := (norm_add_le _ _).trans (by rw [norm_one]; linarith)
    have hn : (n : ℝ) ≤ 2 ^ (n + 1) := by
      have := Nat.lt_two_pow_self (n := n + 1)
      exact_mod_cast (Nat.lt_succ_self n).le.trans this.le
    calc ‖(1 + w) * ((1 + w) ^ n - 1 - n * w) + n * w ^ 2‖
        ≤ ‖1 + w‖ * ‖(1 + w) ^ n - 1 - n * w‖ + n * ‖w‖ ^ 2 := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
      _ ≤ 2 * (n * 2 ^ n * ‖w‖ ^ 2) + 2 ^ (n + 1) * ‖w‖ ^ 2 := by
          gcongr
      _ = ((n + 1 : ℕ) : ℝ) * 2 ^ (n + 1) * ‖w‖ ^ 2 := by push_cast; ring

/-- `‖θ(τ)¹² - 1 - 24 e^{πiτ}‖ ≤ Cθ e^{-2π Im τ}` for `Im τ ≥ 1`. -/
lemma norm_theta12_sub_le {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖jacobiTheta τ ^ 12 - 1 - 24 * cexp (π * I * τ)‖ ≤ (12 * 2 ^ 12 * 16 + 48) * rexp (-2 * π * τ.im) := by
  set w := jacobiTheta τ - 1 with hw
  have h1 := norm_jacobiTheta_sub_one_le' hτ
  have h4 := norm_jacobiTheta_sub_le hτ
  have hr := exp_neg_pi_im_le_quarter hτ
  have hwle : ‖w‖ ≤ 1 := by nlinarith [Real.exp_pos (-π * τ.im)]
  have hT := norm_one_add_pow_sub_le hwle 12
  rw [show 1 + w = jacobiTheta τ by rw [hw]; ring] at hT
  have e : jacobiTheta τ ^ 12 - 1 - 24 * cexp (π * I * τ) =
      (jacobiTheta τ ^ 12 - 1 - ((12 : ℕ) : ℂ) * w) +
        12 * (jacobiTheta τ - 1 - 2 * cexp (π * I * τ)) := by
    rw [hw]; push_cast; ring
  rw [e]
  have hsq : ‖w‖ ^ 2 ≤ 16 * rexp (-2 * π * τ.im) := by
    have : rexp (-2 * π * τ.im) = rexp (-π * τ.im) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [this]
    nlinarith [norm_nonneg w]
  have h44 : rexp (-4 * π * τ.im) ≤ rexp (-2 * π * τ.im) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  calc _ ≤ ‖jacobiTheta τ ^ 12 - 1 - ((12 : ℕ) : ℂ) * w‖ +
        ‖12 * (jacobiTheta τ - 1 - 2 * cexp (π * I * τ))‖ := norm_add_le _ _
    _ ≤ (12 : ℕ) * 2 ^ 12 * (16 * rexp (-2 * π * τ.im)) + 12 * (4 * rexp (-2 * π * τ.im)) := by
        rw [norm_mul, Complex.norm_ofNat]
        gcongr
        · exact hT.trans (by gcongr)
        · exact h4.trans (by gcongr)
    _ = (12 * 2 ^ 12 * 16 + 48) * rexp (-2 * π * τ.im) := by push_cast; ring

/-! ### The series `O` and `E` -/

/-- `K₅ = ∑_r r⁵ 2⁻ʳ`. -/
def K5 : ℝ := ∑' r : ℕ, (r : ℝ) ^ 5 * (1 / 2) ^ r

lemma hasSum_K5 : HasSum (fun r : ℕ => (r : ℝ) ^ 5 * (1 / 2) ^ r) K5 :=
  (summable_pow_mul_geometric_of_norm_lt_one 5 (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).hasSum

lemma K5_nonneg : 0 ≤ K5 := tsum_nonneg fun r => by positivity

lemma pow_le_aux2 {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1 / 2) {r k a : ℕ} (hr : 1 ≤ r)
    (ha : k + 2 ≤ a) : ρ ^ (r * a) ≤ 2 * ρ ^ 2 * (1 / 2) ^ k * (1 / 2) ^ r := by
  have hρ1 : ρ ≤ 1 := by linarith
  have e : r + k + 1 ≤ r * a := by nlinarith
  obtain ⟨s, hs⟩ : ∃ s, r + k + 1 = s + 2 := ⟨r + k - 1, by omega⟩
  calc ρ ^ (r * a) ≤ ρ ^ (r + k + 1) := pow_le_pow_of_le_one h0 hρ1 e
    _ = ρ ^ 2 * ρ ^ s := by rw [hs, pow_add]; ring
    _ ≤ ρ ^ 2 * (1 / 2) ^ s := by gcongr
    _ = 2 * ρ ^ 2 * (1 / 2) ^ (r + k) := by
        have : r + k = s + 1 := by omega
        rw [this, pow_succ]; ring
    _ = 2 * ρ ^ 2 * (1 / 2) ^ k * (1 / 2) ^ r := by rw [pow_add]; ring

/-- An inner series `∑_r f(r)` with `‖f(r)‖ ≤ r⁵ ‖q‖^{ra}`, `a ≥ k + 1`. -/
lemma norm_inner_le1 {f : ℕ → ℂ} {q : ℂ} (hq : ‖q‖ ≤ 1 / 2) {k a : ℕ} (ha : k + 1 ≤ a)
    (hf : ∀ r, ‖f r‖ ≤ (r : ℝ) ^ 5 * ‖q‖ ^ (r * a)) :
    ‖∑' r, f r‖ ≤ 2 * ‖q‖ * (1 / 2) ^ k * K5 := by
  refine tsum_of_norm_bounded (hasSum_K5.mul_left (2 * ‖q‖ * (1 / 2) ^ k)) fun r => ?_
  refine (hf r).trans ?_
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  · have := pow_le_aux (norm_nonneg q) hq hr ha
    calc (r : ℝ) ^ 5 * ‖q‖ ^ (r * a) ≤ (r : ℝ) ^ 5 * (2 * ‖q‖ * (1 / 2) ^ k * (1 / 2) ^ r) := by
          gcongr
      _ = _ := by ring

/-- An inner series `∑_r f(r)` with `‖f(r)‖ ≤ r⁵ ‖q‖^{ra}`, `a ≥ k + 2`. -/
lemma norm_inner_le2 {f : ℕ → ℂ} {q : ℂ} (hq : ‖q‖ ≤ 1 / 2) {k a : ℕ} (ha : k + 2 ≤ a)
    (hf : ∀ r, ‖f r‖ ≤ (r : ℝ) ^ 5 * ‖q‖ ^ (r * a)) :
    ‖∑' r, f r‖ ≤ 2 * ‖q‖ ^ 2 * (1 / 2) ^ k * K5 := by
  refine tsum_of_norm_bounded (hasSum_K5.mul_left (2 * ‖q‖ ^ 2 * (1 / 2) ^ k)) fun r => ?_
  refine (hf r).trans ?_
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  · have := pow_le_aux2 (norm_nonneg q) hq hr ha
    calc (r : ℝ) ^ 5 * ‖q‖ ^ (r * a) ≤ (r : ℝ) ^ 5 * (2 * ‖q‖ ^ 2 * (1 / 2) ^ k * (1 / 2) ^ r) := by
          gcongr
      _ = _ := by ring

lemma hasSum_outer (c : ℝ) : HasSum (fun k : ℕ => 2 * c * (1 / 2) ^ k * K5) (4 * K5 * c) := by
  have := (hasSum_geometric_two.mul_left (2 * c)).mul_right K5
  convert this using 1; ring

lemma norm_term_O (q : ℂ) (a r : ℕ) : ‖(r : ℂ) ^ 5 * q ^ (r * a)‖ ≤ (r : ℝ) ^ 5 * ‖q‖ ^ (r * a) := by
  rw [norm_mul, norm_pow, norm_pow, Complex.norm_natCast]

lemma norm_term_E (q : ℂ) (a r : ℕ) :
    ‖(-1) ^ r * (r : ℂ) ^ 5 * q ^ (r * a)‖ ≤ (r : ℝ) ^ 5 * ‖q‖ ^ (r * a) := by
  rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, Complex.norm_natCast, norm_neg, norm_one,
    one_pow, one_mul]

lemma norm_seriesE_le {q : ℂ} (hq : ‖q‖ ≤ 1 / 2) : ‖seriesE q‖ ≤ 4 * K5 * ‖q‖ ^ 2 :=
  tsum_of_norm_bounded (hasSum_outer (‖q‖ ^ 2)) fun k => by
    have := norm_inner_le2 hq (k := k) (a := 2 * (k + 1)) (by omega) (norm_term_E q _)
    linarith

lemma summable_seriesO_terms {q : ℂ} (hq : ‖q‖ ≤ 1 / 2) :
    Summable fun k : ℕ => ∑' r : ℕ, (r : ℂ) ^ 5 * q ^ (r * (2 * k + 1)) :=
  Summable.of_norm_bounded (hasSum_outer ‖q‖).summable fun k =>
    norm_inner_le1 hq (k := k) (a := 2 * k + 1) (by omega) (norm_term_O q _)

/-- `K₅' = ∑_r (r+2)⁵ 2⁻ʳ`. -/
def K5' : ℝ := ∑' r : ℕ, ((r : ℝ) + 2) ^ 5 * (1 / 2) ^ r

lemma summable_K5' : Summable fun r : ℕ => ((r : ℝ) + 2) ^ 5 * (1 / 2 : ℝ) ^ r := by
  have h0 : Summable fun r : ℕ => (r : ℝ) ^ 5 * (1 / 2 : ℝ) ^ r :=
    summable_pow_mul_geometric_of_norm_lt_one 5 (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
  have h := (summable_nat_add_iff (f := fun r : ℕ => (r : ℝ) ^ 5 * (1 / 2 : ℝ) ^ r) 2).mpr h0
  refine (h.mul_left 4).congr fun r => ?_
  push_cast; rw [pow_add]; ring

lemma norm_first_row_sub_le {q : ℂ} (hq : ‖q‖ ≤ 1 / 2) :
    ‖∑' r : ℕ, (r : ℂ) ^ 5 * q ^ (r * (2 * 0 + 1)) - q‖ ≤ K5' * ‖q‖ ^ 2 := by
  have hq1 : ‖q‖ < 1 := by linarith
  have hs : Summable fun r : ℕ => (r : ℂ) ^ 5 * q ^ (r * (2 * 0 + 1)) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 5 hq1
  have h2 := (hasSum_nat_add_iff' 2).mpr hs.hasSum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h2
  have e : ∑' r : ℕ, (r : ℂ) ^ 5 * q ^ (r * (2 * 0 + 1)) - q =
      ∑' r : ℕ, (r : ℂ) ^ 5 * q ^ (r * (2 * 0 + 1)) -
        (0 + ((0 : ℕ) : ℂ) ^ 5 * q ^ (0 * (2 * 0 + 1)) + ((1 : ℕ) : ℂ) ^ 5 * q ^ (1 * (2 * 0 + 1))) := by
    simp
  rw [e, ← h2.tsum_eq]
  refine tsum_of_norm_bounded ((summable_K5'.hasSum).mul_right (‖q‖ ^ 2)) fun r => ?_
  rw [norm_mul, norm_pow, norm_pow]
  have hc : ‖((r + 2 : ℕ) : ℂ)‖ = (r : ℝ) + 2 := by
    rw [Complex.norm_natCast]; push_cast; ring
  rw [hc, show (r + 2) * (2 * 0 + 1) = r + 2 by ring, pow_add]
  have : ‖q‖ ^ r ≤ (1 / 2) ^ r := pow_le_pow_left₀ (norm_nonneg _) hq r
  calc ((r : ℝ) + 2) ^ 5 * (‖q‖ ^ r * ‖q‖ ^ 2) ≤ ((r : ℝ) + 2) ^ 5 * ((1 / 2) ^ r * ‖q‖ ^ 2) := by
        gcongr
    _ = _ := by ring

/-- The constant of `norm_seriesOE_sub_le`. -/
def CL : ℝ := K5' + 4 * K5 + 4 * K5

/-- `‖O(q) - E(q) - q‖ ≤ C ‖q‖²` for `‖q‖ ≤ 1/2`. -/
lemma norm_seriesOE_sub_le {q : ℂ} (hq : ‖q‖ ≤ 1 / 2) :
    ‖seriesO q - seriesE q - q‖ ≤ CL * ‖q‖ ^ 2 := by
  have hO := (summable_seriesO_terms hq).tsum_eq_zero_add
  have hrest : ‖∑' k : ℕ, ∑' r : ℕ, (r : ℂ) ^ 5 * q ^ (r * (2 * (k + 1) + 1))‖ ≤
      4 * K5 * ‖q‖ ^ 2 :=
    tsum_of_norm_bounded (hasSum_outer (‖q‖ ^ 2)) fun k => by
      have := norm_inner_le2 hq (k := k) (a := 2 * (k + 1) + 1) (by omega) (norm_term_O q _)
      linarith
  have e : seriesO q - seriesE q - q =
      (∑' r : ℕ, (r : ℂ) ^ 5 * q ^ (r * (2 * 0 + 1)) - q) +
        ∑' k : ℕ, ∑' r : ℕ, (r : ℂ) ^ 5 * q ^ (r * (2 * (k + 1) + 1)) - seriesE q := by
    rw [seriesO, hO]; push_cast; ring
  rw [e]
  have h1 := norm_first_row_sub_le hq
  have h3 := norm_seriesE_le hq
  calc _ ≤ ‖∑' r : ℕ, (r : ℂ) ^ 5 * q ^ (r * (2 * 0 + 1)) - q‖ +
        ‖∑' k : ℕ, ∑' r : ℕ, (r : ℂ) ^ 5 * q ^ (r * (2 * (k + 1) + 1))‖ + ‖seriesE q‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ K5' * ‖q‖ ^ 2 + 4 * K5 * ‖q‖ ^ 2 + 4 * K5 * ‖q‖ ^ 2 := by gcongr
    _ = CL * ‖q‖ ^ 2 := by rw [CL]; ring

/-! ### `η¹²` -/

/-- A power series with `c₀ = 0`, `c₁ = 1` is `q + O(q²)`. -/
lemma norm_sub_of_hasSum {c : ℕ → ℂ} {F q : ℂ} (hF : HasSum (fun n => c n * q ^ n) F)
    (h0 : c 0 = 0) (h1 : c 1 = 1) (hq : ‖q‖ ≤ 1 / 2) {M : ℝ}
    (hM : HasSum (fun n => ‖c n‖ * (1 / 2) ^ n) M) : ‖F - q‖ ≤ 4 * M * ‖q‖ ^ 2 := by
  have h2 : HasSum (fun n => c (n + 2) * q ^ (n + 2)) (F - q) := by
    have := (hasSum_nat_add_iff' (f := fun n => c n * q ^ n) 2).mpr hF
    rw [Finset.sum_range_succ, Finset.sum_range_one, h0, h1] at this
    simpa using this
  have hM2 : HasSum (fun n => ‖c (n + 2)‖ * (1 / 2) ^ (n + 2))
      (M - (‖c 0‖ * (1 / 2) ^ 0 + ‖c 1‖ * (1 / 2) ^ 1)) := by
    have := (hasSum_nat_add_iff' (f := fun n => ‖c n‖ * (1 / 2 : ℝ) ^ n) 2).mpr hM
    rwa [Finset.sum_range_succ, Finset.sum_range_one] at this
  have hMle : M - (‖c 0‖ * (1 / 2 : ℝ) ^ 0 + ‖c 1‖ * (1 / 2) ^ 1) ≤ M := by
    have : 0 ≤ ‖c 0‖ * (1 / 2 : ℝ) ^ 0 + ‖c 1‖ * (1 / 2) ^ 1 := by positivity
    linarith
  have hb : ∀ n, ‖c (n + 2) * q ^ (n + 2)‖ ≤ 4 * ‖q‖ ^ 2 * (‖c (n + 2)‖ * (1 / 2) ^ (n + 2)) := by
    intro n
    rw [norm_mul, norm_pow, pow_add, pow_add]
    have : ‖q‖ ^ n ≤ (1 / 2) ^ n := pow_le_pow_left₀ (norm_nonneg _) hq n
    calc ‖c (n + 2)‖ * (‖q‖ ^ n * ‖q‖ ^ 2) ≤ ‖c (n + 2)‖ * ((1 / 2) ^ n * ‖q‖ ^ 2) := by gcongr
      _ = 4 * ‖q‖ ^ 2 * (‖c (n + 2)‖ * ((1 / 2) ^ n * (1 / 2) ^ 2)) := by ring
  have ht := tsum_of_norm_bounded (hM2.mul_left (4 * ‖q‖ ^ 2)) hb
  rw [h2.tsum_eq] at ht
  have := mul_le_mul_of_nonneg_left hMle (by positivity : (0 : ℝ) ≤ 4 * ‖q‖ ^ 2)
  linarith

/-- `Cη = ∑ |a(n)| 2⁻ⁿ`. -/
def Ceta : ℝ := ∑' n : ℕ, |(etaTwelveCoeff n : ℝ)| * (1 / 2) ^ n

lemma Ceta_nonneg : 0 ≤ Ceta := tsum_nonneg fun n => by positivity

lemma hasSum_eta12 (τ : ℍ) :
    HasSum (fun n => (etaTwelveCoeff n : ℂ) * cexp (π * I * τ) ^ n) (eta12 τ) := by
  rw [eta12_eq]
  exact hasSum_etaTwelveCoeff (SixSquares.norm_cexp_pi_I_lt_one τ)

lemma hasSum_Ceta : HasSum (fun n => ‖(etaTwelveCoeff n : ℂ)‖ * (1 / 2) ^ n) Ceta := by
  have h : HasSum (fun n => |(etaTwelveCoeff n : ℝ)| * (1 / 2 : ℝ) ^ n) Ceta :=
    (summable_etaTwelveCoeff (by norm_num) (by norm_num)).hasSum
  convert h using 2 with n
  rw [Complex.norm_intCast]

lemma norm_eta12_sub_le (τ : ℍ) (hτ : 1 ≤ τ.im) :
    ‖eta12 τ - cexp (π * I * τ)‖ ≤ 4 * Ceta * rexp (-2 * π * τ.im) := by
  have hq : ‖cexp (π * I * τ)‖ ≤ 1 / 2 := by
    rw [norm_q]; linarith [exp_neg_pi_im_le_quarter hτ]
  have h := norm_sub_of_hasSum (hasSum_eta12 τ) (by simp [etaTwelveCoeff_zero])
    (by simp [etaTwelveCoeff_one]) hq hasSum_Ceta
  have e : ‖cexp (π * I * τ)‖ ^ 2 = rexp (-2 * π * τ.im) := by
    rw [norm_q, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  rwa [e] at h

lemma norm_eta12_le (τ : ℍ) (hτ : 1 ≤ τ.im) : ‖eta12 τ‖ ≤ 1 + 4 * Ceta := by
  have h := norm_eta12_sub_le τ hτ
  have hq : ‖cexp (π * I * τ)‖ ≤ 1 := by
    rw [norm_q]; linarith [exp_neg_pi_im_le_quarter hτ]
  have he : rexp (-2 * π * τ.im) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hC := Ceta_nonneg
  calc ‖eta12 τ‖ = ‖(eta12 τ - cexp (π * I * τ)) + cexp (π * I * τ)‖ := by ring_nf
    _ ≤ 4 * Ceta * rexp (-2 * π * τ.im) + 1 := (norm_add_le _ _).trans (add_le_add h hq)
    _ ≤ 4 * Ceta * 1 + 1 := by gcongr
    _ = 1 + 4 * Ceta := by ring

/-! ### `g = κ θ¹² - L_W - c η¹²` -/

/-- `c = 24κ - π⁶/60`. -/
def cEta : ℂ := 24 * kappa - π ^ 6 / 60

/-- `g(τ) = κ θ(τ)¹² - L_W(τ) - c η(τ)¹²`. -/
def gfun (τ : ℍ) : ℂ := kappa * jacobiTheta τ ^ 12 - Lsum6 W τ - cEta * eta12 τ

lemma gfun_S (τ : ℍ) : gfun (S • τ) = -((τ : ℂ) ^ 6 * gfun τ) := by
  rw [gfun, gfun, theta12_S, Lsum6_W_S, eta12_S]; ring

lemma gfun_T_sq (τ : ℍ) : gfun (T ^ (2 : ℤ) • τ) = gfun τ := by
  rw [gfun, gfun, theta_T_sq, Lsum6_W_T2, eta12_T_sq]

/-- `τ⁻⁶ g(TSτ)`. -/
def gTS (τ : ℍ) : ℂ := kappa * thetaTS τ - Lsum6 Wp τ - cEta * eta12 τ

lemma gfun_TS (τ : ℍ) : gfun ((T * S) • τ) = (τ : ℂ) ^ 6 * gTS τ := by
  rw [gfun, theta12_TS, Lsum6_W_TS, eta12_TS, gTS]; ring

lemma mdiff_gfun : MDiff gfun := by
  have h1 : MDiff (fun τ : ℍ => kappa * jacobiTheta τ ^ 12) :=
    mdiff_of_eqOn (F := fun z => kappa * jacobiTheta z ^ 12)
      (fun z hz => (((differentiableAt_jacobiTheta hz).pow 12).const_mul kappa).differentiableWithinAt)
      fun _ => rfl
  have h3 : MDiff (fun τ : ℍ => cEta * eta12 τ) := by
    have := mdiff_eta12
    exact (mdifferentiable_const).mul this
  exact (h1.sub (mdiff_Lsum6 norm_W_le)).sub h3

/-- The constant of `norm_gfun_le`. -/
def Cg : ℝ := ‖kappa‖ * (12 * 2 ^ 12 * 16 + 48) + π ^ 6 / 60 * CL + ‖cEta‖ * (4 * Ceta)

lemma norm_gfun_le (τ : ℍ) (hτ : 1 ≤ τ.im) : ‖gfun τ‖ ≤ Cg * rexp (-2 * π * τ.im) := by
  set q := cexp (π * I * τ) with hq
  have hqn : ‖q‖ = rexp (-π * τ.im) := norm_q τ
  have hq2 : ‖q‖ ≤ 1 / 2 := by rw [hqn]; linarith [exp_neg_pi_im_le_quarter hτ]
  have hqq : ‖q‖ ^ 2 = rexp (-2 * π * τ.im) := by
    rw [hqn, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e : gfun τ = kappa * (jacobiTheta τ ^ 12 - 1 - 24 * q) -
      π ^ 6 / 60 * (seriesO q - seriesE q - q) - cEta * (eta12 τ - q) := by
    rw [gfun, Lsum6_W_eq, cEta]; ring
  rw [e]
  have h1 := norm_theta12_sub_le (τ := (τ : ℂ)) (by simpa using hτ)
  have h2 := norm_seriesOE_sub_le hq2
  have h3 := norm_eta12_sub_le τ hτ
  have hi : (τ : ℂ).im = τ.im := rfl
  rw [hi] at h1
  rw [hqq] at h2
  have hp : ‖(π : ℂ) ^ 6 / 60‖ = π ^ 6 / 60 := by
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
      Complex.norm_ofNat]
  calc _ ≤ ‖kappa * (jacobiTheta τ ^ 12 - 1 - 24 * q)‖ +
        ‖(π : ℂ) ^ 6 / 60 * (seriesO q - seriesE q - q)‖ + ‖cEta * (eta12 τ - q)‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ ‖kappa‖ * ((12 * 2 ^ 12 * 16 + 48) * rexp (-2 * π * τ.im)) +
          π ^ 6 / 60 * (CL * rexp (-2 * π * τ.im)) +
          ‖cEta‖ * (4 * Ceta * rexp (-2 * π * τ.im)) := by
        rw [norm_mul, norm_mul, norm_mul, hp]
        gcongr
    _ = Cg * rexp (-2 * π * τ.im) := by rw [Cg]; ring

/-- The bound for `L_{W'}` on the strip `|Re τ| ≤ 1`, `Im τ ≥ 1`. -/
def ML6 : ℝ := ∑' v : Fin 2 → ℤ, r ⟨⟨1, 1⟩, one_pos⟩ ^ (-(6 : ℝ)) * ‖v‖ ^ (-(6 : ℝ))

lemma norm_Lsum6_Wp_le (τ : ℍ) (hτ : 1 ≤ τ.im) (hr : |τ.re| ≤ 1) : ‖Lsum6 Wp τ‖ ≤ ML6 := by
  have hs := (summable_one_div_norm_rpow (k := 6) (by norm_num)).mul_left
    (r ⟨⟨1, 1⟩, one_pos⟩ ^ (-(6 : ℝ)))
  refine tsum_of_norm_bounded hs.hasSum fun v => ?_
  rw [norm_mul]
  have hmem : τ ∈ verticalStrip 1 1 := ⟨hr, hτ⟩
  have hb := summand_bound_of_mem_verticalStrip (k := 6) (by norm_num) v one_pos hmem
  have he : ‖eisSummand 6 v τ‖ ≤ r ⟨⟨1, 1⟩, one_pos⟩ ^ (-(6 : ℝ)) * ‖v‖ ^ (-(6 : ℝ)) := by
    simp only [eisSummand, norm_zpow]
    exact_mod_cast hb
  calc ‖Wp v‖ * ‖eisSummand 6 v τ‖ ≤ 1 * (r ⟨⟨1, 1⟩, one_pos⟩ ^ (-(6 : ℝ)) * ‖v‖ ^ (-(6 : ℝ))) :=
        mul_le_mul (norm_Wp_le v) he (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _

/-- The constant of `norm_gTS_le`. -/
def MTS : ℝ := ‖kappa‖ * K1 ^ 12 + ML6 + ‖cEta‖ * (1 + 4 * Ceta)

lemma norm_gTS_le (τ : ℍ) (hτ : 1 ≤ τ.im) (hr : |τ.re| ≤ 1) : ‖gTS τ‖ ≤ MTS := by
  rw [gTS, MTS]
  calc ‖kappa * thetaTS τ - Lsum6 Wp τ - cEta * eta12 τ‖
      ≤ ‖kappa * thetaTS τ‖ + ‖Lsum6 Wp τ‖ + ‖cEta * eta12 τ‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ ‖kappa‖ * K1 ^ 12 + ML6 + ‖cEta‖ * (1 + 4 * Ceta) := by
        rw [norm_mul, norm_mul]
        gcongr
        · exact norm_thetaTS_le τ hτ
        · exact norm_Lsum6_Wp_le τ hτ hr
        · exact norm_eta12_le τ hτ

end NTKB.HardyWright.TwelveSquares
