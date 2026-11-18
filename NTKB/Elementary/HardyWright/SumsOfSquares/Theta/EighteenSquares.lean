/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.EighteenCount

/-!
# The formula for `r₁₈(n)` (beyond Hardy–Wright, § 20.13)

For `n ≥ 1`, `1385 r₁₈(n) = 4 (∑_{d ∣ n} χ(d) d⁸ + 256 ∑_{d ∣ n} χ(n/d) d⁸) + 48960 c₁₈(n) - 32 c₈(n)`
(`eighteenSquaresFormula`), where `c₁₈(n)` is the coefficient of `qⁿ` in the cusp form `θ⁶ η¹²`
and `c₈(n) = ∑_{a² + b² = n} Re (a + bi)⁸` is the coefficient of `qⁿ` in the Gaussian lattice sum
`C₈`. The proof is the level-one method of `TenSquares.lean` at weight `9`:

* `g = κ θ¹⁸ - L_W - c₁ θ⁶ η¹² - c₂ C₈` is `O(e^{-3π Im τ})`;
* `G = g⁴` is invariant of weight `36` under `S` and `T²` and `G ∣ TS` is bounded, so `G = 0`
  (`Δ³`-argument of `EighteenVanish.lean`);
* at `τ = it` this is an identity of real power series in `x = e^{-πt}`; comparing the coefficients
  (`EighteenCount.lean`, with the constants determined by `r₁₈(1), r₁₈(2), r₁₈(3)`) gives the
  formula.
-/

open ModularForm ModularGroup Complex Filter Topology EisensteinSeries Matrix
open scoped MatrixGroups Real UpperHalfPlane Manifold
open UpperHalfPlane hiding I

noncomputable section

namespace NTKB.HardyWright.EighteenSquares

open EightSquares (ne_zero' denom_TS)

/-- `G = g⁴`. -/
def Gfun (τ : ℍ) : ℂ := gfun τ ^ 4

lemma Gfun_slash_S : Gfun ∣[(36 : ℤ)] S = Gfun := by
  ext τ
  rw [SL_slash_apply, Gfun, Gfun, gfun_S, denom_S]
  have := ne_zero' τ
  rw [_root_.zpow_neg, show (36 : ℤ) = ((36 : ℕ) : ℤ) from rfl, zpow_natCast, mul_pow, mul_pow,
    ← pow_mul, neg_pow, I_pow_four]
  field_simp
  ring

lemma Gfun_slash_T_sq : Gfun ∣[(36 : ℤ)] (T ^ (2 : ℤ)) = Gfun := by
  ext τ
  rw [SL_slash_apply, Gfun, Gfun, gfun_T_sq, ModularGroup.denom_apply, coe_T_zpow]
  simp

lemma mdiff_Gfun : MDiff Gfun := mdiff_gfun.pow 4

lemma norm_Gfun_le (τ : ℍ) (hτ : 1 ≤ τ.im) :
    ‖Gfun τ‖ ≤ Cg ^ 4 * rexp (-12 * π * τ.im) := by
  rw [Gfun, norm_pow]
  have h := norm_gfun_le τ hτ
  have e : rexp (-12 * π * τ.im) = rexp (-3 * π * τ.im) ^ 4 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [e, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 4

lemma norm_Gfun_TS_le (τ : ℍ) (hτ : 1 ≤ τ.im) (hr : |τ.re| ≤ 1) :
    ‖(Gfun ∣[(36 : ℤ)] (T * S)) τ‖ ≤ MTS ^ 4 := by
  rw [SL_slash_apply, denom_TS, Gfun, gfun_TS]
  have := ne_zero' τ
  have e : ((τ : ℂ) ^ 9 * gTS τ) ^ 4 * (τ : ℂ) ^ (-(36 : ℤ)) = gTS τ ^ 4 := by
    rw [_root_.zpow_neg, show (36 : ℤ) = ((36 : ℕ) : ℤ) from rfl, zpow_natCast, mul_pow, ← pow_mul]
    field_simp
    ring
  rw [e, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_gTS_le τ hτ hr) 4

/-- **The theta identity.** `κ θ(τ)¹⁸ = L_W(τ) + c₁ θ(τ)⁶ η(τ)¹² + c₂ C₈(τ)`. -/
theorem kappa_mul_theta_pow_eighteen (τ : ℍ) :
    kappa * jacobiTheta τ ^ 18 = Lsum9 W τ + c1 * cuspF τ + c2 * oct τ := by
  have hG := eq_zero_of_invariant36 mdiff_Gfun Gfun_slash_S Gfun_slash_T_sq norm_Gfun_le
    norm_Gfun_TS_le
  have h := congrFun hG τ
  simp only [Gfun, Pi.zero_apply] at h
  have := pow_eq_zero_iff (n := 4) (by norm_num) |>.mp h
  rw [gfun] at this
  linear_combination this

/-! ### Real values -/

/-- `κ = ∑_{n ∈ ℤ} χ(n) n⁻⁹` as a real number. -/
def kappaR : ℝ := ∑' n : ℤ, ((ZMod.χ₄ (n : ZMod 4) : ℤ) : ℝ) * (1 / (n : ℝ) ^ 9)

lemma kappa_eq_ofReal : kappa = (kappaR : ℂ) := by
  rw [kappa, kappaR, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  simp [SixSquares.chiZ]

/-- The real constant `c₁`. -/
def c1R : ℝ := (-36 * kappaR + 240 * (Real.pi ^ 9 / 20160) - 15 * (Real.pi ^ 9 / 5160960)) / 4

/-- The real constant `c₂`. -/
def c2R : ℝ := (180 * kappaR - 244 * (Real.pi ^ 9 / 20160) + 11 * (Real.pi ^ 9 / 5160960)) / 16

lemma c1_eq_ofReal : c1 = (c1R : ℂ) := by
  rw [c1, c1R, aB, bA, kappa_eq_ofReal]; push_cast; ring

lemma c2_eq_ofReal : c2 = (c2R : ℂ) := by
  rw [c2, c2R, aB, bA, kappa_eq_ofReal]; push_cast; ring

lemma seriesA_ofReal (x : ℝ) : seriesA (x : ℂ) = (eighteenSeriesA x : ℂ) := by
  rw [seriesA, eighteenSeriesA, Complex.ofReal_tsum]
  refine tsum_congr fun k => ?_
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun r => ?_
  rw [SixSquares.chiZ_natCast]; push_cast; ring

lemma seriesB_ofReal {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    seriesB (x : ℂ) = (eighteenSeriesB x : ℂ) := by
  set g : ℕ → ℝ := fun k => chi4R (2 * k + 1) * ∑' r : ℕ, (r : ℝ) ^ 8 * x ^ (r * (2 * k + 1))
    with hg
  have hterm : ∀ k : ℕ, SixSquares.chiZ (2 * (k : ℤ) + 1) *
      ∑' r : ℕ, (r : ℂ) ^ 8 * (x : ℂ) ^ (r * (2 * k + 1)) = (g k : ℂ) := by
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
      chi4R (2 * k + 1 + 1) * ∑' r : ℕ, (r : ℝ) ^ 8 * x ^ (r * (2 * k + 1 + 1)) := by
    simp only [SixSquares.chi4R_even, zero_mul]; exact summable_zero
  have := tsum_even_add_odd (f := fun m : ℕ =>
    chi4R (m + 1) * ∑' r : ℕ, (r : ℝ) ^ 8 * x ^ (r * (m + 1))) hsR ho
  rw [eighteenSeriesB, ← this]
  simp only [SixSquares.chi4R_even, zero_mul, tsum_zero, add_zero]
  rw [seriesB, tsum_congr hterm, ← Complex.ofReal_tsum]

end NTKB.HardyWright.EighteenSquares

namespace NTKB.HardyWright

open EighteenSquares

/-- `κ θ(it)¹⁸ = L_W(it) + c₁ θ⁶ η¹² + c₂ C₈` as an identity of real power series in
`x = e^{-πt}`. -/
lemma theta_pow_eighteen_real {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1 / 2) :
    kappaR * (∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 18 =
      kappaR + Real.pi ^ 9 / 20160 * eighteenSeriesB x +
        Real.pi ^ 9 / 5160960 * eighteenSeriesA x +
        c1R * ((∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 6 * TwelveSquares.etaSeriesR x) +
        c2R * octSeriesR x := by
  have hx1' : x < 1 := by linarith
  set t := -Real.log x / π with ht
  have htpos : 0 < t := by
    have : Real.log x < 0 := Real.log_neg hx0 hx1'
    rw [ht]; exact div_pos (by linarith) Real.pi_pos
  have hxt : rexp (-π * t) = x := by
    rw [ht, show -π * (-Real.log x / π) = Real.log x by field_simp]; exact Real.exp_log hx0
  set τ : ℍ := ⟨I * t, by simpa using htpos⟩ with hτ
  have hτc : (τ : ℂ) = I * t := rfl
  have h := kappa_mul_theta_pow_eighteen τ
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
  have hC : oct τ = (octSeriesR x : ℂ) := by
    have h1 := hasSum_octC τ.2
    rw [hq] at h1
    have h2 := (hasSum_octSeriesR hx0.le hx1').map Complex.ofRealHom Complex.continuous_ofReal
    have h2' : HasSum (fun n : ℕ => (octicCoeff n : ℂ) * (x : ℂ) ^ n) (octSeriesR x : ℂ) := by
      refine h2.congr_fun fun n => ?_
      simp
    exact h1.unique h2'
  rw [Lsum9_W_eq, hq, kappa_eq_ofReal, seriesA_ofReal, seriesB_ofReal hx0.le hx1.le, cuspF,
    hθ, hη, hC, c1_eq_ofReal, c2_eq_ofReal] at h
  generalize (∑' m : ℤ, x ^ (m.natAbs ^ 2)) = θR at h ⊢
  have h' : ((kappaR * θR ^ 18 : ℝ) : ℂ) =
      ((kappaR + Real.pi ^ 9 / 20160 * eighteenSeriesB x +
        Real.pi ^ 9 / 5160960 * eighteenSeriesA x +
        c1R * (θR ^ 6 * TwelveSquares.etaSeriesR x) + c2R * octSeriesR x : ℝ) : ℂ) := by
    push_cast at h ⊢; linear_combination h
  exact Complex.ofReal_injective h'

/-- **The formula for `r₁₈`** (derived from the theta series; see `EighteenSquaresFormula`). For
`n ≥ 1`,
`1385 r₁₈(n) = 4 (∑_{d ∣ n} χ(d) d⁸ + 256 ∑_{d ∣ n} χ(n/d) d⁸) + 48960 c₁₈(n) - 32 c₈(n)`,
`c₁₈(n)` the coefficient of `qⁿ` (`q = e^{πiτ}`) in `θ(τ)⁶ η(τ)¹²` and
`c₈(n) = ∑_{a² + b² = n} Re (a + bi)⁸`. -/
theorem eighteenSquaresFormula : EighteenSquaresFormula :=
  eighteenSquaresFormula_of_forall (fun _ hx0 hx1 => theta_pow_eighteen_real hx0 hx1)

end NTKB.HardyWright
