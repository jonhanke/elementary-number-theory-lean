/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.SixteenBounds
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.SixteenVanish
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.SixteenCount

/-!
# The formula for `r₁₆(n)` (beyond Hardy–Wright, § 20.13)

For `n ≥ 1`, `17 r₁₆(n) = 32 ∑_{d ∣ n} (-1)^{n+d} d⁷ + 512 c₁₆(n)`, where `c₁₆(n)` is the
coefficient of `qⁿ` in `θ⁴ η¹²` (`glaisherSixteenSquares`). The proof is the level-one method of
`FourteenSquares.lean` at weight `8`, which lies on the boundary of the vanishing criterion, so that
`g = κ θ¹⁶ - L_W - c θ⁴ η¹²` must vanish to order `3` in `q = e^{πiτ}` (the coefficient of `q²`
vanishes because `κ = ∑_{n odd} n⁻⁸ = 17 π⁸/80640`, from `ζ(8) = π⁸/9450`, `SixteenKappa.lean`):

* `L_W(τ) = ∑ W(m, n)(mτ + n)⁻⁸`, `W(m, n) = [m even, n odd] + [m odd, n even]`, transforms like
  `θ¹⁶` under `S` and `T²` (`SixteenLattice.lean`), with `q`-expansion
  `κ + (π⁸/2520)(O(q) + E(q))` (`SixteenExpansion.lean`);
* `g` is `O(e^{-3π Im τ})`, `G = g²` is invariant of weight `16` under `S` and `T²` and `G ∣ TS` is
  bounded, so `G = 0` (`SixteenVanish.lean`, the `Δ⁴` argument);
* at `τ = it` this is an identity of real power series in `x = e^{-πt}`; comparing the coefficients
  (`SixteenCount.lean`, `κ` and `c` from `r₁₆(1) = 32`, `r₁₆(2) = 480`) gives the formula.
-/

open ModularForm ModularGroup Complex Filter Topology EisensteinSeries Matrix
open scoped MatrixGroups Real UpperHalfPlane Manifold
open UpperHalfPlane hiding I

noncomputable section

namespace NTKB.HardyWright.SixteenSquares

open EightSquares (ne_zero' denom_TS)

/-- `G = g²`. -/
def Gfun (τ : ℍ) : ℂ := gfun τ ^ 2

lemma Gfun_slash_S : Gfun ∣[(16 : ℤ)] S = Gfun := by
  ext τ
  rw [SL_slash_apply, Gfun, Gfun, gfun_S, denom_S]
  have := ne_zero' τ
  rw [_root_.zpow_neg, show (16 : ℤ) = ((16 : ℕ) : ℤ) from rfl, zpow_natCast, mul_pow, ← pow_mul]
  field_simp
  ring

lemma Gfun_slash_T_sq : Gfun ∣[(16 : ℤ)] (T ^ (2 : ℤ)) = Gfun := by
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
    ‖(Gfun ∣[(16 : ℤ)] (T * S)) τ‖ ≤ MTS ^ 2 := by
  rw [SL_slash_apply, denom_TS, Gfun, gfun_TS]
  have := ne_zero' τ
  have e : ((τ : ℂ) ^ 8 * gTS τ) ^ 2 * (τ : ℂ) ^ (-(16 : ℤ)) = gTS τ ^ 2 := by
    rw [_root_.zpow_neg, show (16 : ℤ) = ((16 : ℕ) : ℤ) from rfl, zpow_natCast, mul_pow, ← pow_mul]
    field_simp
    ring
  rw [e, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_gTS_le τ hτ hr) 2

/-- **The theta identity.** `κ θ(τ)¹⁶ = L_W(τ) + c θ(τ)⁴ η(τ)¹²`. -/
theorem kappa_mul_theta_pow_sixteen (τ : ℍ) :
    kappa * jacobiTheta τ ^ 16 = Lsum8 W τ + cG * cuspF τ := by
  have hG := eq_zero_of_invariant16 mdiff_Gfun Gfun_slash_S Gfun_slash_T_sq norm_Gfun_le
    norm_Gfun_TS_le
  have h := congrFun hG τ
  simp only [Gfun, Pi.zero_apply] at h
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
  rw [gfun] at this
  linear_combination this

/-! ### Real values -/

lemma seriesOE_ofReal {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    seriesO (x : ℂ) + seriesE (x : ℂ) = ((sixteenSeriesOE x : ℝ) : ℂ) := by
  have hx1 : x < 1 := by linarith
  have hq : ‖(x : ℂ)‖ ≤ 1 / 2 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hx0]; exact hx
  set f : ℕ → ℝ := fun m => ∑' r : ℕ, sixteenG x r (m + 1) with hf
  have hs : Summable fun p : ℕ × ℕ => sixteenG x p.2 (p.1 + 1) := by
    refine Summable.of_norm_bounded (summable_sixteen_majorant hx0 hx1) fun p => ?_
    rw [Real.norm_eq_abs]
    exact abs_sixteenG_le x p.2 (p.1 + 1) hx0
  have hfs : Summable f := hs.prod
  have hOr : ∀ k : ℕ, f (2 * k) = ∑' r : ℕ, (r : ℝ) ^ 7 * x ^ (r * (2 * k + 1)) := by
    intro k
    rw [hf]
    refine tsum_congr fun r => ?_
    have : ¬ Even (2 * k + 1) := by
      rw [Nat.not_even_iff_odd]; exact odd_two_mul_add_one k
    simp [sixteenG, this]
  have hEr : ∀ k : ℕ, f (2 * k + 1) = ∑' r : ℕ, (-1) ^ r * (r : ℝ) ^ 7 * x ^ (r * (2 * (k + 1))) := by
    intro k
    rw [hf]
    refine tsum_congr fun r => ?_
    have : Even (2 * k + 1 + 1) := ⟨k + 1, by ring⟩
    simp only [sixteenG, this, if_true]
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring]
    ring
  have hsO : Summable fun k : ℕ => f (2 * k) :=
    hfs.comp_injective (i := fun k : ℕ => 2 * k) (by intro a b h; simpa using h)
  have hsE : Summable fun k : ℕ => f (2 * k + 1) :=
    hfs.comp_injective (i := fun k : ℕ => 2 * k + 1) (by intro a b h; simpa using h)
  have hsum := tsum_even_add_odd hsO hsE
  have e1 : seriesO (x : ℂ) = ((∑' k : ℕ, f (2 * k) : ℝ) : ℂ) := by
    rw [seriesO, Complex.ofReal_tsum]
    refine tsum_congr fun k => ?_
    rw [hOr, Complex.ofReal_tsum]
    refine tsum_congr fun r => ?_
    push_cast; ring
  have e2 : seriesE (x : ℂ) = ((∑' k : ℕ, f (2 * k + 1) : ℝ) : ℂ) := by
    rw [seriesE, Complex.ofReal_tsum]
    refine tsum_congr fun k => ?_
    rw [hEr, Complex.ofReal_tsum]
    refine tsum_congr fun r => ?_
    push_cast; ring
  rw [e1, e2, ← Complex.ofReal_add, sixteenSeriesOE, ← hsum]

end NTKB.HardyWright.SixteenSquares

namespace NTKB.HardyWright

open SixteenSquares

/-- `κ θ(it)¹⁶ = L_W(it) + c θ(it)⁴ η(it)¹²` as an identity of real power series in `x = e^{-πt}`. -/
lemma theta_pow_sixteen_real {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1 / 2) :
    (17 * Real.pi ^ 8 / 80640) * (∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 16 =
      (17 * Real.pi ^ 8 / 80640) + Real.pi ^ 8 / 2520 * sixteenSeriesOE x +
        (32 * (17 * Real.pi ^ 8 / 80640) - Real.pi ^ 8 / 2520) *
          ((∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 4 * TwelveSquares.etaSeriesR x) := by
  have hx1' : x < 1 := by linarith
  set t := -Real.log x / π with ht
  have htpos : 0 < t := by
    have : Real.log x < 0 := Real.log_neg hx0 hx1'
    rw [ht]; exact div_pos (by linarith) Real.pi_pos
  have hxt : rexp (-π * t) = x := by
    rw [ht, show -π * (-Real.log x / π) = Real.log x by field_simp]; exact Real.exp_log hx0
  set τ : ℍ := ⟨I * t, by simpa using htpos⟩ with hτ
  have hτc : (τ : ℂ) = I * t := rfl
  have h := kappa_mul_theta_pow_sixteen τ
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
  rw [SixteenSquares.Lsum8_W_eq, hq, SixteenSquares.seriesOE_ofReal hx0.le hx1.le, hθ,
    SixteenSquares.cuspF, hθ, hη, SixteenSquares.cG, SixteenSquares.kappa_eq] at h
  generalize (∑' m : ℤ, x ^ (m.natAbs ^ 2)) = θR at h ⊢
  have h' : (((17 * Real.pi ^ 8 / 80640) * θR ^ 16 : ℝ) : ℂ) =
      (((17 * Real.pi ^ 8 / 80640) + Real.pi ^ 8 / 2520 * sixteenSeriesOE x +
        (32 * (17 * Real.pi ^ 8 / 80640) - Real.pi ^ 8 / 2520) *
          (θR ^ 4 * TwelveSquares.etaSeriesR x) : ℝ) : ℂ) := by
    push_cast at h ⊢; linear_combination h
  exact Complex.ofReal_injective h'

/-- **The formula for `r₁₆`** (see `GlaisherSixteenSquares`; derived from the theta series). For
`n ≥ 1`, `17 r₁₆(n) = 32 ∑_{d ∣ n} (-1)^{n+d} d⁷ + 512 c₁₆(n)`, `c₁₆(n)` the coefficient of `qⁿ`
(`q = e^{πiτ}`) in the cusp form `θ(τ)⁴ η(τ)¹²` of weight `8` on `Γ₀(4)`. -/
@[kb "grosswald1985" "r16"]
theorem glaisherSixteenSquares : GlaisherSixteenSquares :=
  glaisherSixteenSquares_of_forall (fun _ hx0 hx1 => theta_pow_sixteen_real hx0 hx1)

end NTKB.HardyWright
