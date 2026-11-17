/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TenBounds
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.SixSquares

/-!
# Liouville's formula for `r₁₀(n)` (beyond Hardy–Wright, § 20.13)

For `n ≥ 1`, `5 r₁₀(n) = 4 ∑_{d ∣ n} χ(d) d⁴ + 64 ∑_{d ∣ n} χ(n/d) d⁴ + 8 ∑_{a ∈ ℤ[i], N(a) = n} a⁴`,
`χ` the non-principal character modulo `4` (`liouvilleTenSquares`; Liouville, see Grosswald,
*Representations of Integers as Sums of Squares*, 1985). The proof is the level-one method of
`SixSquares.lean` and `TwelveSquares.lean`, with the cusp form `C(τ) = ∑_{a ∈ ℤ[i]} a⁴ e^{πi N(a) τ}`:

* `L_W(τ) = ∑ W(m, n)(mτ + n)⁻⁵`, `W(m, n) = [m even] χ(n) + i [n even] χ(m)`, transforms like
  `θ¹⁰` under `S` and `T²` (`TenLattice.lean`) and has the `q`-expansion
  `κ + (π⁵/12) B(q) + (π⁵/192) A(q)` (`TenExpansion.lean`);
* `C` transforms like `θ¹⁰` (`TenCusp.lean`: the coefficient of `z⁴` in the functional equation of
  `θ(z, τ) θ(iz, τ)`, in which the Gaussian factors cancel);
* `g = κ θ¹⁰ - L_W - c C` is `O(e^{-2π Im τ})`, `G = g⁴` is invariant of weight `20` under `S` and
  `T²` and `G ∣ TS` is bounded, so `G = 0` (`TenVanish.lean`, the `Δ⁵` argument);
* at `τ = it` this is an identity of real power series in `x = e^{-πt}`; comparing the coefficients
  (`TenCount.lean`, with `κ` and `c` determined by `r₁₀(1) = 20`, `r₁₀(2) = 180`) gives the formula.
-/

open ModularForm ModularGroup Complex Filter Topology EisensteinSeries Matrix
open scoped MatrixGroups Real UpperHalfPlane Manifold
open UpperHalfPlane hiding I

noncomputable section

namespace NTKB.HardyWright.TenSquares

open EightSquares (ne_zero' denom_TS)

/-- `G = g⁴`. -/
def Gfun (τ : ℍ) : ℂ := gfun τ ^ 4

lemma Gfun_slash_S : Gfun ∣[(20 : ℤ)] S = Gfun := by
  ext τ
  rw [SL_slash_apply, Gfun, Gfun, gfun_S, denom_S]
  have := ne_zero' τ
  rw [_root_.zpow_neg, show (20 : ℤ) = ((20 : ℕ) : ℤ) from rfl, zpow_natCast, mul_pow, mul_pow,
    ← pow_mul, neg_pow, I_pow_four]
  field_simp
  ring

lemma Gfun_slash_T_sq : Gfun ∣[(20 : ℤ)] (T ^ (2 : ℤ)) = Gfun := by
  ext τ
  rw [SL_slash_apply, Gfun, Gfun, gfun_T_sq, ModularGroup.denom_apply, coe_T_zpow]
  simp

lemma mdiff_Gfun : MDiff Gfun := mdiff_gfun.pow 4

lemma norm_Gfun_le (τ : ℍ) (hτ : 1 ≤ τ.im) :
    ‖Gfun τ‖ ≤ Cg ^ 4 * rexp (-8 * π * τ.im) := by
  rw [Gfun, norm_pow]
  have h := norm_gfun_le τ hτ
  have e : rexp (-8 * π * τ.im) = rexp (-2 * π * τ.im) ^ 4 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [e, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 4

lemma norm_Gfun_TS_le (τ : ℍ) (hτ : 1 ≤ τ.im) (hr : |τ.re| ≤ 1) :
    ‖(Gfun ∣[(20 : ℤ)] (T * S)) τ‖ ≤ MTS ^ 4 := by
  rw [SL_slash_apply, denom_TS, Gfun, gfun_TS]
  have := ne_zero' τ
  have e : ((τ : ℂ) ^ 5 * gTS τ) ^ 4 * (τ : ℂ) ^ (-(20 : ℤ)) = gTS τ ^ 4 := by
    rw [_root_.zpow_neg, show (20 : ℤ) = ((20 : ℕ) : ℤ) from rfl, zpow_natCast, mul_pow, ← pow_mul]
    field_simp
    ring
  rw [e, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_gTS_le τ hτ hr) 4

/-- **The theta identity.** `κ θ(τ)¹⁰ = L_W(τ) + c C(τ)`. -/
theorem kappa_mul_theta_pow_ten (τ : ℍ) :
    kappa * jacobiTheta τ ^ 10 = Lsum5 W τ + cC * cusp τ := by
  have hG := eq_zero_of_invariant20 mdiff_Gfun Gfun_slash_S Gfun_slash_T_sq norm_Gfun_le
    norm_Gfun_TS_le
  have h := congrFun hG τ
  simp only [Gfun, Pi.zero_apply] at h
  have := pow_eq_zero_iff (n := 4) (by norm_num) |>.mp h
  rw [gfun] at this
  linear_combination this

/-! ### Real values -/

/-- `κ = ∑_{n ∈ ℤ} χ(n) n⁻⁵` as a real number. -/
def kappaR : ℝ := ∑' n : ℤ, ((ZMod.χ₄ (n : ZMod 4) : ℤ) : ℝ) * (1 / (n : ℝ) ^ 5)

lemma kappa_eq_ofReal : kappa = (kappaR : ℂ) := by
  rw [kappa, kappaR, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  simp [SixSquares.chiZ]

lemma seriesA_ofReal (x : ℝ) : seriesA (x : ℂ) = (tenSeriesA x : ℂ) := by
  rw [seriesA, tenSeriesA, Complex.ofReal_tsum]
  refine tsum_congr fun k => ?_
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun r => ?_
  rw [SixSquares.chiZ_natCast]; push_cast; ring

lemma seriesB_ofReal {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    seriesB (x : ℂ) = (tenSeriesB x : ℂ) := by
  set g : ℕ → ℝ := fun k => chi4R (2 * k + 1) * ∑' r : ℕ, (r : ℝ) ^ 4 * x ^ (r * (2 * k + 1))
    with hg
  have hterm : ∀ k : ℕ, SixSquares.chiZ (2 * (k : ℤ) + 1) *
      ∑' r : ℕ, (r : ℂ) ^ 4 * (x : ℂ) ^ (r * (2 * k + 1)) = (g k : ℂ) := by
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
      chi4R (2 * k + 1 + 1) * ∑' r : ℕ, (r : ℝ) ^ 4 * x ^ (r * (2 * k + 1 + 1)) := by
    simp only [SixSquares.chi4R_even, zero_mul]; exact summable_zero
  have := tsum_even_add_odd (f := fun m : ℕ =>
    chi4R (m + 1) * ∑' r : ℕ, (r : ℝ) ^ 4 * x ^ (r * (m + 1))) hsR ho
  rw [tenSeriesB, ← this]
  simp only [SixSquares.chi4R_even, zero_mul, tsum_zero, add_zero]
  rw [seriesB, tsum_congr hterm, ← Complex.ofReal_tsum]

lemma cC_eq_ofReal : cC = ((20 * kappaR - Real.pi ^ 5 / 12 - Real.pi ^ 5 / 192) / 4 : ℝ) := by
  rw [cC, kappa_eq_ofReal]; push_cast; ring

end NTKB.HardyWright.TenSquares

namespace NTKB.HardyWright

open TenSquares

/-- `κ θ(it)¹⁰ = L_W(it) + c C(it)` as an identity of real power series in `x = e^{-πt}`. -/
lemma theta_pow_ten_real {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1 / 2) :
    kappaR * (∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 10 =
      kappaR + Real.pi ^ 5 / 12 * tenSeriesB x + Real.pi ^ 5 / 192 * tenSeriesA x +
        (20 * kappaR - Real.pi ^ 5 / 12 - Real.pi ^ 5 / 192) / 4 * cuspSeriesR x := by
  have hx1' : x < 1 := by linarith
  set t := -Real.log x / π with ht
  have htpos : 0 < t := by
    have : Real.log x < 0 := Real.log_neg hx0 hx1'
    rw [ht]; exact div_pos (by linarith) Real.pi_pos
  have hxt : rexp (-π * t) = x := by
    rw [ht, show -π * (-Real.log x / π) = Real.log x by field_simp]; exact Real.exp_log hx0
  set τ : ℍ := ⟨I * t, by simpa using htpos⟩ with hτ
  have hτc : (τ : ℂ) = I * t := rfl
  have h := kappa_mul_theta_pow_ten τ
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
  have hC : cusp τ = (cuspSeriesR x : ℂ) := by
    have h1 := hasSum_cuspC τ.2
    rw [hq] at h1
    have h2 := (hasSum_cuspSeriesR hx0.le hx1').map Complex.ofRealHom Complex.continuous_ofReal
    have h2' : HasSum (fun n : ℕ => (liouvilleCusp n : ℂ) * (x : ℂ) ^ n) (cuspSeriesR x : ℂ) := by
      refine h2.congr_fun fun n => ?_
      simp
    exact h1.unique h2'
  rw [Lsum5_W_eq, hq, kappa_eq_ofReal, hθ, seriesA_ofReal, seriesB_ofReal hx0.le hx1.le, hC,
    cC_eq_ofReal] at h
  generalize (∑' m : ℤ, x ^ (m.natAbs ^ 2)) = θR at h ⊢
  have h' : ((kappaR * θR ^ 10 : ℝ) : ℂ) =
      ((kappaR + Real.pi ^ 5 / 12 * tenSeriesB x + Real.pi ^ 5 / 192 * tenSeriesA x +
        (20 * kappaR - Real.pi ^ 5 / 12 - Real.pi ^ 5 / 192) / 4 * cuspSeriesR x : ℝ) : ℂ) := by
    push_cast at h ⊢; linear_combination h
  exact Complex.ofReal_injective h'

/-- **Liouville's formula for `r₁₀`** (Liouville; see Grosswald 1985). For `n ≥ 1`,
`5 r₁₀(n) = 4 ∑_{d ∣ n} χ(d) d⁴ + 64 ∑_{d ∣ n} χ(n/d) d⁴ + 8 ∑_{a ∈ ℤ[i], N(a) = n} a⁴`. -/
@[kb "grosswald1985" "r10"]
theorem liouvilleTenSquares : LiouvilleTenSquares :=
  liouvilleTenSquares_of_forall (fun _ hx0 hx1 => theta_pow_ten_real hx0 hx1)

end NTKB.HardyWright
