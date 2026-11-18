/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.FourteenBounds
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.FourteenVanish
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.FourteenCount

/-!
# The formula for `r₁₄(n)` (beyond Hardy–Wright, § 20.13)

For `n ≥ 1`, `61 r₁₄(n) = 4 (64 ∑_{d ∣ n} χ(n/d) d⁶ - ∑_{d ∣ n} χ(d) d⁶) + 1456 c₁₄(n)`, where
`c₁₄(n)` is the coefficient of `qⁿ` in `θ² η¹²` (`glaisherFourteenSquares`). The proof is the
level-one method of `TenSquares.lean` with the cusp form `f = θ² η¹²` of `TwelveEta.lean` in place of
`C`:

* `L_W(τ) = ∑ W(m, n)(mτ + n)⁻⁷`, `W(m, n) = [m even] χ(n) - i [n even] χ(m)`, transforms like `θ¹⁴`
  under `S` and `T²` (`FourteenLattice.lean`), with `q`-expansion
  `κ + (π⁷/360) B(q) - (π⁷/23040) A(q)` (`FourteenExpansion.lean`);
* `g = κ θ¹⁴ - L_W - c θ² η¹²` is `O(e^{-2π Im τ})`, `G = g¹²` is invariant of weight `84` under `S`
  and `T²` and `G ∣ TS` is bounded, so `G = 0` (`FourteenVanish.lean`, the `Δ²¹` argument);
* at `τ = it` this is an identity of real power series in `x = e^{-πt}`; comparing the coefficients
  (`FourteenCount.lean`, with `κ` and `c` determined by `r₁₄(1) = 28`, `r₁₄(2) = 364`) gives the
  formula.
-/

open ModularForm ModularGroup Complex Filter Topology EisensteinSeries Matrix
open scoped MatrixGroups Real UpperHalfPlane Manifold
open UpperHalfPlane hiding I

noncomputable section

namespace NTKB.HardyWright.FourteenSquares

open EightSquares (ne_zero' denom_TS)
open TwelveSquares (eta12 hasSum_eta12 etaSeriesR hasSum_etaSeriesR)

/-- `G = g¹²`. -/
def Gfun (τ : ℍ) : ℂ := gfun τ ^ 12

lemma Gfun_slash_S : Gfun ∣[(84 : ℤ)] S = Gfun := by
  ext τ
  rw [SL_slash_apply, Gfun, Gfun, gfun_S, denom_S]
  have := ne_zero' τ
  rw [_root_.zpow_neg, show (84 : ℤ) = ((84 : ℕ) : ℤ) from rfl, zpow_natCast, mul_pow, mul_pow,
    ← pow_mul, show I ^ 12 = 1 by rw [show (12 : ℕ) = 4 * 3 from rfl, pow_mul, I_pow_four]; simp]
  field_simp
  ring

lemma Gfun_slash_T_sq : Gfun ∣[(84 : ℤ)] (T ^ (2 : ℤ)) = Gfun := by
  ext τ
  rw [SL_slash_apply, Gfun, Gfun, gfun_T_sq, ModularGroup.denom_apply, coe_T_zpow]
  simp

lemma mdiff_Gfun : MDiff Gfun := mdiff_gfun.pow 12

lemma norm_Gfun_le (τ : ℍ) (hτ : 1 ≤ τ.im) :
    ‖Gfun τ‖ ≤ Cg ^ 12 * rexp (-24 * π * τ.im) := by
  rw [Gfun, norm_pow]
  have h := norm_gfun_le τ hτ
  have e : rexp (-24 * π * τ.im) = rexp (-2 * π * τ.im) ^ 12 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [e, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 12

lemma norm_Gfun_TS_le (τ : ℍ) (hτ : 1 ≤ τ.im) (hr : |τ.re| ≤ 1) :
    ‖(Gfun ∣[(84 : ℤ)] (T * S)) τ‖ ≤ MTS ^ 12 := by
  rw [SL_slash_apply, denom_TS, Gfun, gfun_TS]
  have := ne_zero' τ
  have e : ((τ : ℂ) ^ 7 * gTS τ) ^ 12 * (τ : ℂ) ^ (-(84 : ℤ)) = gTS τ ^ 12 := by
    rw [_root_.zpow_neg, show (84 : ℤ) = ((84 : ℕ) : ℤ) from rfl, zpow_natCast, mul_pow, ← pow_mul]
    field_simp
    ring
  rw [e, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_gTS_le τ hτ hr) 12

/-- **The theta identity.** `κ θ(τ)¹⁴ = L_W(τ) + c θ(τ)² η(τ)¹²`. -/
theorem kappa_mul_theta_pow_fourteen (τ : ℍ) :
    kappa * jacobiTheta τ ^ 14 = Lsum7 W τ + cF * cuspF τ := by
  have hG := eq_zero_of_invariant84 mdiff_Gfun Gfun_slash_S Gfun_slash_T_sq norm_Gfun_le
    norm_Gfun_TS_le
  have h := congrFun hG τ
  simp only [Gfun, Pi.zero_apply] at h
  have := pow_eq_zero_iff (n := 12) (by norm_num) |>.mp h
  rw [gfun] at this
  linear_combination this

/-! ### Real values -/

/-- `κ = ∑_{n ∈ ℤ} χ(n) n⁻⁷` as a real number. -/
def kappaR : ℝ := ∑' n : ℤ, ((ZMod.χ₄ (n : ZMod 4) : ℤ) : ℝ) * (1 / (n : ℝ) ^ 7)

lemma kappa_eq_ofReal : kappa = (kappaR : ℂ) := by
  rw [kappa, kappaR, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  simp [SixSquares.chiZ]

lemma seriesA_ofReal (x : ℝ) : seriesA (x : ℂ) = (fourteenSeriesA x : ℂ) := by
  rw [seriesA, fourteenSeriesA, Complex.ofReal_tsum]
  refine tsum_congr fun k => ?_
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun r => ?_
  rw [SixSquares.chiZ_natCast]; push_cast; ring

lemma seriesB_ofReal {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    seriesB (x : ℂ) = (fourteenSeriesB x : ℂ) := by
  set g : ℕ → ℝ := fun k => chi4R (2 * k + 1) * ∑' r : ℕ, (r : ℝ) ^ 6 * x ^ (r * (2 * k + 1))
    with hg
  have hterm : ∀ k : ℕ, SixSquares.chiZ (2 * (k : ℤ) + 1) *
      ∑' r : ℕ, (r : ℂ) ^ 6 * (x : ℂ) ^ (r * (2 * k + 1)) = (g k : ℂ) := by
    intro k
    rw [hg]
    have : SixSquares.chiZ (2 * (k : ℤ) + 1) = SixSquares.chiZ ((2 * k + 1 : ℕ) : ℤ) := by
      push_cast; rfl
    rw [this, SixSquares.chiZ_natCast]
    push_cast
    norm_cast
  have hq : ‖(x : ℂ)‖ ≤ 1 / 2 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hx0]; exact hx
  have hsC := summable_seriesB_terms hq
  have hsR : Summable g := by
    rw [← Complex.summable_ofReal]
    exact hsC.congr hterm
  have ho : Summable fun k : ℕ =>
      chi4R (2 * k + 1 + 1) * ∑' r : ℕ, (r : ℝ) ^ 6 * x ^ (r * (2 * k + 1 + 1)) := by
    simp only [SixSquares.chi4R_even, zero_mul]; exact summable_zero
  have := tsum_even_add_odd (f := fun m : ℕ =>
    chi4R (m + 1) * ∑' r : ℕ, (r : ℝ) ^ 6 * x ^ (r * (m + 1))) hsR ho
  rw [fourteenSeriesB, ← this]
  simp only [SixSquares.chi4R_even, zero_mul, tsum_zero, add_zero]
  rw [seriesB, tsum_congr hterm, ← Complex.ofReal_tsum]

lemma cF_eq_ofReal :
    cF = ((28 * kappaR - Real.pi ^ 7 / 360 + Real.pi ^ 7 / 23040 : ℝ) : ℂ) := by
  rw [cF, kappa_eq_ofReal]; push_cast; ring

end NTKB.HardyWright.FourteenSquares

namespace NTKB.HardyWright

open FourteenSquares

/-- `κ θ(it)¹⁴ = L_W(it) + c θ(it)² η(it)¹²` as an identity of real power series in `x = e^{-πt}`. -/
lemma theta_pow_fourteen_real {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1 / 2) :
    kappaR * (∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 14 =
      kappaR + Real.pi ^ 7 / 360 * fourteenSeriesB x - Real.pi ^ 7 / 23040 * fourteenSeriesA x +
        (28 * kappaR - Real.pi ^ 7 / 360 + Real.pi ^ 7 / 23040) *
          ((∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 2 * TwelveSquares.etaSeriesR x) := by
  have hx1' : x < 1 := by linarith
  set t := -Real.log x / π with ht
  have htpos : 0 < t := by
    have : Real.log x < 0 := Real.log_neg hx0 hx1'
    rw [ht]; exact div_pos (by linarith) Real.pi_pos
  have hxt : rexp (-π * t) = x := by
    rw [ht, show -π * (-Real.log x / π) = Real.log x by field_simp]; exact Real.exp_log hx0
  set τ : ℍ := ⟨I * t, by simpa using htpos⟩ with hτ
  have hτc : (τ : ℂ) = I * t := rfl
  have h := kappa_mul_theta_pow_fourteen τ
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
  rw [Lsum7_W_eq, hq, kappa_eq_ofReal, hθ, seriesA_ofReal, seriesB_ofReal hx0.le hx1.le,
    cuspF, hθ, hη, cF_eq_ofReal] at h
  generalize (∑' m : ℤ, x ^ (m.natAbs ^ 2)) = θR at h ⊢
  have h' : ((kappaR * θR ^ 14 : ℝ) : ℂ) =
      ((kappaR + Real.pi ^ 7 / 360 * fourteenSeriesB x - Real.pi ^ 7 / 23040 * fourteenSeriesA x +
        (28 * kappaR - Real.pi ^ 7 / 360 + Real.pi ^ 7 / 23040) *
          (θR ^ 2 * TwelveSquares.etaSeriesR x) : ℝ) : ℂ) := by
    push_cast at h ⊢; linear_combination h
  exact Complex.ofReal_injective h'

/-- **The formula for `r₁₄`** (see `GlaisherFourteenSquares`; derived from the theta series). For
`n ≥ 1`, `61 r₁₄(n) = 4 (64 ∑_{d ∣ n} χ(n/d) d⁶ - ∑_{d ∣ n} χ(d) d⁶) + 1456 c₁₄(n)`, `c₁₄(n)` the
coefficient of `qⁿ` (`q = e^{πiτ}`) in the cusp form `θ(τ)² η(τ)¹²` of weight `7` on `Γ₀(4)`. -/
@[kb "grosswald1985" "r14"]
theorem glaisherFourteenSquares : GlaisherFourteenSquares :=
  glaisherFourteenSquares_of_forall (fun _ hx0 hx1 => theta_pow_fourteen_real hx0 hx1)

end NTKB.HardyWright
