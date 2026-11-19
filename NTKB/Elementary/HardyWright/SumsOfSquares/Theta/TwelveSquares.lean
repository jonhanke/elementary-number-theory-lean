/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TwelveBounds
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TwelveCount
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.SixSquares

/-!
# Glaisher's formula for `r₁₂(n)` (beyond Hardy–Wright, § 20.13)

For `n ≥ 1`,
`r₁₂(n) = 8 ∑_{d ∣ n} (-1)^{n + d + n/d + 1} d⁵ + 16 a(n)`,
where `a(n)` is the coefficient of `qⁿ` in `q ∏_{m ≥ 1} (1 - q^{2m})¹²` (that is, of `η(2z)¹²` in
`q = e^{2πiz}`) (`sumSquaresCount_twelve_eq`). The formula is Glaisher's (1907); see Grosswald,
*Representations of Integers as Sums of Squares* (1985). It goes beyond Hardy–Wright, whose § 20.13
gives `r₆` and `r₈`; it is recorded in the Hardy–Wright map under the notes to § 20.13. The proof is
the level-one method of `SixSquares.lean`, with the cusp form `η(τ)¹²` added:

* `L_W(τ) = ∑_{(m, n) ∈ ℤ²} W(m, n)(mτ + n)⁻⁶`, `W(m, n) = [m even, n odd] - [m odd, n even]`,
  transforms like `θ¹²` under `S` and `T²` (`TwelveLattice.lean`) and has the `q`-expansion
  `κ + (π⁶/60)(O(q) - E(q))` (`TwelveExpansion.lean`); `η¹²` (Mathlib's Dedekind `eta`) transforms
  the same way (`TwelveEta.lean`);
* `g = κ θ¹² - L_W - c η¹²` with `c = 24κ - π⁶/60` is `O(e^{-2π Im τ})`; `G = g²` is invariant of
  weight `12` under `S` and `T²` and `G ∣ TS` is bounded, so `G = 0` (`SixSquares.eq_zero_of_invariant`,
  the `Δ³` argument of `SixVanish.lean`, reused unchanged);
* at `τ = it` this is an identity of real power series in `x = e^{-πt}`; comparing coefficients
  (`TwelveCount.lean`, with `κ = ∑_{n odd} n⁻⁶ = π⁶/480` from `ζ(6) = π⁶/945`, hence `c = π⁶/30`)
  gives the formula.
-/

open ModularForm ModularGroup Complex Filter Topology EisensteinSeries Matrix
open scoped MatrixGroups Real UpperHalfPlane Manifold
open UpperHalfPlane hiding I

noncomputable section

namespace NTKB.HardyWright.TwelveSquares

open EightSquares (ne_zero' denom_TS)

/-- `G = g²`. -/
def Gfun (τ : ℍ) : ℂ := gfun τ ^ 2

lemma Gfun_slash_S : Gfun ∣[(12 : ℤ)] S = Gfun := by
  ext τ
  rw [SL_slash_apply, Gfun, Gfun, gfun_S, denom_S]
  have := ne_zero' τ
  rw [_root_.zpow_neg, show (12 : ℤ) = ((12 : ℕ) : ℤ) from rfl, zpow_natCast]
  field_simp

lemma Gfun_slash_T_sq : Gfun ∣[(12 : ℤ)] (T ^ (2 : ℤ)) = Gfun := by
  ext τ
  rw [SL_slash_apply, Gfun, Gfun, gfun_T_sq, ModularGroup.denom_apply, coe_T_zpow]
  simp

lemma mdiff_Gfun : MDiff Gfun := mdiff_gfun.pow 2

lemma norm_Gfun_le (τ : ℍ) (hτ : 1 ≤ τ.im) :
    ‖Gfun τ‖ ≤ Cg ^ 2 * rexp (-4 * π * τ.im) := by
  rw [Gfun, norm_pow]
  have h := norm_gfun_le τ hτ
  have e : rexp (-4 * π * τ.im) = rexp (-2 * π * τ.im) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [e, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

lemma norm_Gfun_TS_le (τ : ℍ) (hτ : 1 ≤ τ.im) (hr : |τ.re| ≤ 1) :
    ‖(Gfun ∣[(12 : ℤ)] (T * S)) τ‖ ≤ MTS ^ 2 := by
  rw [SL_slash_apply, denom_TS, Gfun, gfun_TS]
  have := ne_zero' τ
  have e : ((τ : ℂ) ^ 6 * gTS τ) ^ 2 * (τ : ℂ) ^ (-(12 : ℤ)) = gTS τ ^ 2 := by
    rw [_root_.zpow_neg, show (12 : ℤ) = ((12 : ℕ) : ℤ) from rfl, zpow_natCast, mul_pow, ← pow_mul]
    field_simp
    ring
  rw [e, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_gTS_le τ hτ hr) 2

/-- **The theta identity.** `κ θ(τ)¹² = L_W(τ) + c η(τ)¹²`, `c = 24κ - π⁶/60`. -/
theorem kappa_mul_theta_pow_twelve (τ : ℍ) :
    kappa * jacobiTheta τ ^ 12 = Lsum6 W τ + cEta * eta12 τ := by
  have hG := SixSquares.eq_zero_of_invariant mdiff_Gfun Gfun_slash_S Gfun_slash_T_sq norm_Gfun_le
    norm_Gfun_TS_le
  have h := congrFun hG τ
  simp only [Gfun, Pi.zero_apply] at h
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
  rw [gfun] at this
  linear_combination this

/-! ### Real values -/

lemma kappa_eq_ofReal : kappa = (kappaTwelveR : ℂ) := by
  rw [kappa, kappaTwelveR, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  split_ifs <;> push_cast <;> ring

lemma seriesO_ofReal (x : ℝ) : seriesO (x : ℂ) = (twelveSeriesO x : ℂ) := by
  rw [seriesO, twelveSeriesO, Complex.ofReal_tsum]
  refine tsum_congr fun k => ?_
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun r => ?_
  push_cast; ring

lemma seriesE_ofReal (x : ℝ) : seriesE (x : ℂ) = (twelveSeriesE x : ℂ) := by
  rw [seriesE, twelveSeriesE, Complex.ofReal_tsum]
  refine tsum_congr fun k => ?_
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun r => ?_
  push_cast; ring

/-- The real power series `∑ a(n) xⁿ`.
  **Restriction:** the series is the mathematical object only where it converges (absolutely, for $|x| < 1$);
  elsewhere the value is $0$ by Lean's `tsum` convention, not an analytic continuation or the intended value. -/
def etaSeriesR (x : ℝ) : ℝ := ∑' n : ℕ, (etaTwelveCoeff n : ℝ) * x ^ n

lemma hasSum_etaSeriesR {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    HasSum (fun n : ℕ => (etaTwelveCoeff n : ℝ) * x ^ n) (etaSeriesR x) := by
  have hs := summable_etaTwelveCoeff hx0 hx
  have : Summable fun n : ℕ => (etaTwelveCoeff n : ℝ) * x ^ n := by
    refine Summable.of_norm_bounded hs fun n => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hx0 n)]
  exact this.hasSum

end NTKB.HardyWright.TwelveSquares

namespace NTKB.HardyWright

open TwelveSquares

/-- `κ θ(it)¹² = L_W(it) + c η(it)¹²` as an identity of real power series in `x = e^{-πt}`. -/
lemma theta_pow_twelve_real {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1 / 2) :
    kappaTwelveR * (∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 12 =
      kappaTwelveR + Real.pi ^ 6 / 60 * (twelveSeriesO x - twelveSeriesE x) +
        Real.pi ^ 6 / 30 * etaSeriesR x := by
  have hx1' : x < 1 := by linarith
  set t := -Real.log x / π with ht
  have htpos : 0 < t := by
    have : Real.log x < 0 := Real.log_neg hx0 hx1'
    rw [ht]; exact div_pos (by linarith) Real.pi_pos
  have hxt : rexp (-π * t) = x := by
    rw [ht, show -π * (-Real.log x / π) = Real.log x by field_simp]; exact Real.exp_log hx0
  set τ : ℍ := ⟨I * t, by simpa using htpos⟩ with hτ
  have hτc : (τ : ℂ) = I * t := rfl
  have h := kappa_mul_theta_pow_twelve τ
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
  have hη : eta12 τ = (etaSeriesR x : ℂ) := by
    have h1 := hasSum_eta12 τ
    rw [hq] at h1
    have h2 := (hasSum_etaSeriesR hx0.le hx1').map Complex.ofRealHom Complex.continuous_ofReal
    have h2' : HasSum (fun n : ℕ => (etaTwelveCoeff n : ℂ) * (x : ℂ) ^ n) (etaSeriesR x : ℂ) := by
      refine h2.congr_fun fun n => ?_
      simp
    exact h1.unique h2'
  rw [Lsum6_W_eq, hq, kappa_eq_ofReal, hθ, seriesO_ofReal, seriesE_ofReal, hη, cEta,
    kappa_eq_ofReal, kappaTwelveR_eq] at h
  rw [kappaTwelveR_eq]
  generalize (∑' m : ℤ, x ^ (m.natAbs ^ 2)) = θR at h ⊢
  have h' : ((Real.pi ^ 6 / 480 * θR ^ 12 : ℝ) : ℂ) =
      ((Real.pi ^ 6 / 480 + Real.pi ^ 6 / 60 * (twelveSeriesO x - twelveSeriesE x) +
        Real.pi ^ 6 / 30 * etaSeriesR x : ℝ) : ℂ) := by
    push_cast at h ⊢; linear_combination h
  exact Complex.ofReal_injective h'

/-- **Glaisher's formula for `r₁₂`** (Glaisher 1907; see Grosswald 1985). For `n ≥ 1`, the number of representations of `n` as a sum of twelve
squares of integers (order and signs counted) is
`8 ∑_{d ∣ n} (-1)^{n + d + n/d + 1} d⁵ + 16 a(n)`, where `a(n)` is the coefficient of `qⁿ` in
`q ∏_{m ≥ 1} (1 - q^{2m})¹² = η(2z)¹²` (`q = e^{2πiz}`). -/
@[kb "glaisher1907" "r12"]
theorem sumSquaresCount_twelve_eq {n : ℕ} (hn : 0 < n) :
    (sumSquaresCount 12 n : ℤ) = 8 * glaisherSum n + 16 * etaTwelveCoeff n :=
  sumSquaresCount_twelve_eq_of_forall (P := etaSeriesR) (fun _ hx0 hx => hasSum_etaSeriesR hx0 hx)
    (fun _ hx0 hx1 => theta_pow_twelve_real hx0 hx1) hn

end NTKB.HardyWright
