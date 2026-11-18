/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TwentyBounds
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TwentyExpansion
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TwentyCount

/-!
# The formula for `r₂₀(n)` (beyond Hardy–Wright, § 20.13)

For `n ≥ 1`, `31 r₂₀(n) = 8 ∑_{d ∣ n} (-1)^{n+d+n/d+1} d⁹ + 1296 c₂₀(n) - 16 c₂₀'(n)`
(`twentySquaresFormula`), where `c₂₀(n)` is the coefficient of `qⁿ` in the cusp form `θ⁸ η¹²` and
`c₂₀'(n)` that in `θ² C₈`. The proof is the level-one method at weight `10`:

* `g = κ θ²⁰ - L_W - c₁ θ⁸ η¹² - c₂ θ² C₈` is `O(e^{-3π Im τ})`;
* `G = g²` is invariant of weight `20` under `S` and `T²` and `G ∣ TS` is bounded, so `G = 0`
  (`TwentyVanish.lean`);
* at `τ = it` this is an identity of real power series in `x = e^{-πt}`; comparing the coefficients
  (`TwentyCount.lean`, with the constants determined by `r₂₀(1), r₂₀(2), r₂₀(3)`) gives the
  formula.
-/

open ModularForm ModularGroup Complex Filter Topology EisensteinSeries Matrix
open scoped MatrixGroups Real UpperHalfPlane Manifold
open UpperHalfPlane hiding I

noncomputable section

namespace NTKB.HardyWright.TwentySquares

open EightSquares (ne_zero' denom_TS)

/-- `G = g²`. -/
def Gfun (τ : ℍ) : ℂ := gfun τ ^ 2

lemma Gfun_slash_S : Gfun ∣[(20 : ℤ)] S = Gfun := by
  ext τ
  rw [SL_slash_apply, Gfun, Gfun, gfun_S, denom_S]
  have := ne_zero' τ
  rw [_root_.zpow_neg, show (20 : ℤ) = ((20 : ℕ) : ℤ) from rfl, zpow_natCast, neg_sq, mul_pow,
    ← pow_mul]
  field_simp
  ring

lemma Gfun_slash_T_sq : Gfun ∣[(20 : ℤ)] (T ^ (2 : ℤ)) = Gfun := by
  ext τ
  rw [SL_slash_apply, Gfun, Gfun, gfun_T_sq, ModularGroup.denom_apply, coe_T_zpow]
  simp

lemma mdiff_Gfun : MDiff Gfun := mdiff_gfun.pow 2

lemma norm_Gfun_le (τ : ℍ) (hτ : 1 ≤ τ.im) :
    ‖Gfun τ‖ ≤ Cg ^ 2 * rexp (-6 * π * τ.im) := by
  rw [Gfun, norm_pow]
  have h := norm_gfun_le τ hτ
  have e : rexp (-6 * π * τ.im) = rexp (-3 * π * τ.im) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [e, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

lemma norm_Gfun_TS_le (τ : ℍ) (hτ : 1 ≤ τ.im) (hr : |τ.re| ≤ 1) :
    ‖(Gfun ∣[(20 : ℤ)] (T * S)) τ‖ ≤ MTS ^ 2 := by
  rw [SL_slash_apply, denom_TS, Gfun, gfun_TS]
  have := ne_zero' τ
  have e : ((τ : ℂ) ^ 10 * gTS τ) ^ 2 * (τ : ℂ) ^ (-(20 : ℤ)) = gTS τ ^ 2 := by
    rw [_root_.zpow_neg, show (20 : ℤ) = ((20 : ℕ) : ℤ) from rfl, zpow_natCast, mul_pow,
      ← pow_mul]
    field_simp
    ring
  rw [e, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_gTS_le τ hτ hr) 2

/-- **The theta identity.** `κ θ(τ)²⁰ = L_W(τ) + c₁ θ(τ)⁸ η(τ)¹² + c₂ θ(τ)² C₈(τ)`. -/
theorem kappa_mul_theta_pow_twenty (τ : ℍ) :
    kappa * jacobiTheta τ ^ 20 = Lsum10 W τ + c1 * cuspF τ + c2 * cuspG τ := by
  have hG := eq_zero_of_invariant20 mdiff_Gfun Gfun_slash_S Gfun_slash_T_sq norm_Gfun_le
    norm_Gfun_TS_le
  have h := congrFun hG τ
  simp only [Gfun, Pi.zero_apply] at h
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
  rw [gfun] at this
  linear_combination this

/-! ### Real values -/

/-- `κ = ∑_{n odd} n⁻¹⁰` as a real number. -/
def kappaR : ℝ := ∑' n : ℤ, (if Even n then 0 else 1) * (1 / (n : ℝ) ^ 10)

lemma kappa_eq_ofReal : kappa = (kappaR : ℂ) := by
  rw [kappa, kappaR, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  split_ifs <;> push_cast <;> ring

/-- The real constant `c₁`. -/
def c1R : ℝ := (40 * kappaR + 493 * (Real.pi ^ 10 / 181440)) / 4

/-- The real constant `c₂`. -/
def c2R : ℝ := (120 * kappaR - 497 * (Real.pi ^ 10 / 181440)) / 16

lemma c1_eq_ofReal : c1 = (c1R : ℂ) := by
  rw [c1, c1R, aE, kappa_eq_ofReal]; push_cast; ring

lemma c2_eq_ofReal : c2 = (c2R : ℂ) := by
  rw [c2, c2R, aE, kappa_eq_ofReal]; push_cast; ring

lemma seriesO_ofReal (x : ℝ) : seriesO (x : ℂ) = (NTKB.HardyWright.twentySeriesO x : ℂ) := by
  rw [seriesO, NTKB.HardyWright.twentySeriesO, Complex.ofReal_tsum]
  refine tsum_congr fun k => ?_
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun r => ?_
  push_cast; ring

lemma seriesE_ofReal (x : ℝ) : seriesE (x : ℂ) = (NTKB.HardyWright.twentySeriesE x : ℂ) := by
  rw [seriesE, NTKB.HardyWright.twentySeriesE, Complex.ofReal_tsum]
  refine tsum_congr fun k => ?_
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun r => ?_
  push_cast; ring

end NTKB.HardyWright.TwentySquares

namespace NTKB.HardyWright

open TwentySquares
open EighteenSquares (hasSum_octC)

/-- `κ θ(it)²⁰ = L_W(it) + c₁ θ⁸ η¹² + c₂ θ² C₈` as an identity of real power series in
`x = e^{-πt}`. -/
lemma theta_pow_twenty_real {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1 / 2) :
    kappaR * (∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 20 =
      kappaR + Real.pi ^ 10 / 181440 * (twentySeriesO x - twentySeriesE x) +
        c1R * ((∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 8 * TwelveSquares.etaSeriesR x) +
        c2R * ((∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 2 * octSeriesR x) := by
  have hx1' : x < 1 := by linarith
  set t := -Real.log x / π with ht
  have htpos : 0 < t := by
    have : Real.log x < 0 := Real.log_neg hx0 hx1'
    rw [ht]; exact div_pos (by linarith) Real.pi_pos
  have hxt : rexp (-π * t) = x := by
    rw [ht, show -π * (-Real.log x / π) = Real.log x by field_simp]; exact Real.exp_log hx0
  set τ : ℍ := ⟨I * t, by simpa using htpos⟩ with hτ
  have hτc : (τ : ℂ) = I * t := rfl
  have h := kappa_mul_theta_pow_twenty τ
  have hθ : jacobiTheta (τ : ℂ) = ((∑' m : ℤ, x ^ (m.natAbs ^ 2) : ℝ) : ℂ) := by
    rw [jacobiTheta, Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    rw [hτc, ← hxt, ← Real.exp_nat_mul, Complex.ofReal_exp]
    refine congrArg cexp ?_
    have hn : ((n.natAbs : ℕ) : ℂ) ^ 2 = (n : ℂ) ^ 2 := by
      have : ((n.natAbs : ℤ) : ℂ) ^ 2 = (n : ℂ) ^ 2 := by
        rw [← Int.cast_pow, Int.natAbs_sq]; push_cast; ring
      rwa [Int.cast_natCast] at this
    push_cast
    linear_combination (↑π * ↑t * (n : ℂ) ^ 2) * I_sq + (↑π * ↑t) * hn
  have hq : cexp (π * I * τ) = (x : ℂ) := by
    rw [hτc, ← hxt, Complex.ofReal_exp]
    refine congrArg cexp ?_
    push_cast
    linear_combination (↑π * ↑t) * I_sq
  have hη : TwelveSquares.eta12 τ = (TwelveSquares.etaSeriesR x : ℂ) := by
    have h1 := TwelveSquares.hasSum_eta12 τ
    rw [hq] at h1
    have h2 := (TwelveSquares.hasSum_etaSeriesR hx0.le hx1').map Complex.ofRealHom
      Complex.continuous_ofReal
    have h2' : HasSum (fun n : ℕ => (TwelveSquares.etaTwelveCoeff n : ℂ) * (x : ℂ) ^ n)
        (TwelveSquares.etaSeriesR x : ℂ) := by
      refine h2.congr_fun fun n => ?_
      simp
    exact h1.unique h2'
  have hC : EighteenSquares.oct τ = (octSeriesR x : ℂ) := by
    have h1 := hasSum_octC τ.2
    rw [hq] at h1
    have h2 := (hasSum_octSeriesR hx0.le hx1').map Complex.ofRealHom Complex.continuous_ofReal
    have h2' : HasSum (fun n : ℕ => (octicCoeff n : ℂ) * (x : ℂ) ^ n) (octSeriesR x : ℂ) := by
      refine h2.congr_fun fun n => ?_
      simp
    exact h1.unique h2'
  rw [Lsum10_W_eq, hq, kappa_eq_ofReal, seriesO_ofReal, seriesE_ofReal, TwentySquares.cuspF, TwentySquares.cuspG,
    hθ, hη, hC, c1_eq_ofReal, c2_eq_ofReal] at h
  generalize (∑' m : ℤ, x ^ (m.natAbs ^ 2)) = θR at h ⊢
  have h' : ((kappaR * θR ^ 20 : ℝ) : ℂ) =
      ((kappaR + Real.pi ^ 10 / 181440 * (twentySeriesO x - twentySeriesE x) +
        c1R * (θR ^ 8 * TwelveSquares.etaSeriesR x) +
        c2R * (θR ^ 2 * octSeriesR x) : ℝ) : ℂ) := by
    push_cast at h ⊢; linear_combination h
  exact Complex.ofReal_injective h'

/-- **The formula for `r₂₀`** (derived from the theta series; see `TwentySquaresFormula`). For
`n ≥ 1`,
`31 r₂₀(n) = 8 ∑_{d ∣ n} (-1)^{n+d+n/d+1} d⁹ + 1296 c₂₀(n) - 16 c₂₀'(n)`,
`c₂₀(n)` the coefficient of `qⁿ` (`q = e^{πiτ}`) in `θ(τ)⁸ η(τ)¹²` and `c₂₀'(n)` that in
`θ(τ)² C₈(τ)`. -/
theorem twentySquaresFormula : TwentySquaresFormula :=
  twentySquaresFormula_of_forall (fun _ hx0 hx1 => theta_pow_twenty_real hx0 hx1)

end NTKB.HardyWright
