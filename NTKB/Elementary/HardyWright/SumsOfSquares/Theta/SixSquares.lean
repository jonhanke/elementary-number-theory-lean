/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.SixBounds
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.SixCount

/-!
# Hardy–Wright, § 20.13: Jacobi's formula for `r₆(n)`

`r₆(n) = 16 ∑_{d ∣ n} χ(n/d) d² - 4 ∑_{d ∣ n} χ(d) d²` for `n ≥ 1`, `χ` the non-principal character
modulo `4` (`sumSquaresCount_six_eq`, `jacobiSixSquares`). The book states the formula without
proof. The proof here uses only level-one modular forms (as for `r₈`, `EightSquares.lean`):

* `L_W(τ) = ∑_{(m, n) ∈ ℤ²} W(m, n)(mτ + n)⁻³` with `W(m, n) = [m even] χ(n) - i [n even] χ(m)`
  transforms like `θ⁶` under `S` and `T²` (`SixLattice.lean`), and has the `q`-expansion
  `κ + π³ B(q) - (π³/4) A(q)` (`SixExpansion.lean`, by the Lipschitz formula);
* `G = (κ θ⁶ - L_W)⁴` is invariant of weight `12` under `S` and `T²`, is `O(e^{-4π Im τ})`, and
  `G ∣ TS` is bounded; so `G = 0` (`SixVanish.lean`: `G (G∣T) (G∣TS) / Δ³` is a level-one form of
  weight `0` tending to `0`);
* at `τ = it` this is an identity of real power series in `x = e^{-πt}`; comparing coefficients
  (`SixCount.lean`) gives the formula, and the coefficient of `x` gives `κ = π³/16` on the way.
-/

open ModularForm ModularGroup Complex Filter Topology EisensteinSeries Matrix
open scoped MatrixGroups Real UpperHalfPlane Manifold
open UpperHalfPlane hiding I

noncomputable section

namespace NTKB.HardyWright.SixSquares

open EightSquares (ne_zero' denom_TS)

/-- `G = g⁴`. -/
def Gfun (τ : ℍ) : ℂ := gfun τ ^ 4

lemma Gfun_slash_S : Gfun ∣[(12 : ℤ)] S = Gfun := by
  ext τ
  rw [SL_slash_apply, Gfun, Gfun, gfun_S, denom_S]
  have := ne_zero' τ
  rw [_root_.zpow_neg, show (12 : ℤ) = ((12 : ℕ) : ℤ) from rfl, zpow_natCast, mul_pow, mul_pow,
    ← pow_mul, I_pow_four]
  field_simp
  ring

lemma Gfun_slash_T_sq : Gfun ∣[(12 : ℤ)] (T ^ (2 : ℤ)) = Gfun := by
  ext τ
  rw [SL_slash_apply, Gfun, Gfun, gfun_T_sq, ModularGroup.denom_apply, coe_T_zpow]
  simp

lemma mdiff_Gfun : MDiff Gfun := mdiff_gfun.pow 4

lemma norm_Gfun_le (τ : ℍ) (hτ : 1 ≤ τ.im) :
    ‖Gfun τ‖ ≤ Cg6 ^ 4 * rexp (-4 * π * τ.im) := by
  rw [Gfun, norm_pow]
  have h := norm_gfun_le τ hτ
  have e : rexp (-4 * π * τ.im) = rexp (-π * τ.im) ^ 4 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [e, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 4

lemma norm_Gfun_TS_le (τ : ℍ) (hτ : 1 ≤ τ.im) (hr : |τ.re| ≤ 1) :
    ‖(Gfun ∣[(12 : ℤ)] (T * S)) τ‖ ≤ M3 ^ 4 := by
  rw [SL_slash_apply, denom_TS, Gfun, gfun_TS]
  have := ne_zero' τ
  have e : ((τ : ℂ) ^ 3 * (kappa * (I * (cexp (3 * π * I * τ / 2) *
      jacobiTheta₂ (-(τ : ℂ) / 2) τ ^ 6)) - Lsum Wp τ)) ^ 4 * (τ : ℂ) ^ (-(12 : ℤ)) =
      (kappa * (I * (cexp (3 * π * I * τ / 2) * jacobiTheta₂ (-(τ : ℂ) / 2) τ ^ 6)) -
        Lsum Wp τ) ^ 4 := by
    rw [_root_.zpow_neg, show (12 : ℤ) = ((12 : ℕ) : ℤ) from rfl, zpow_natCast, mul_pow, ← pow_mul]
    field_simp
  rw [e, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_gfun_TS_le τ hτ hr) 4

/-- **Jacobi's identity for `θ⁶`.** `κ θ(τ)⁶ = L_W(τ)`. -/
theorem kappa_mul_theta_pow_six (τ : ℍ) : kappa * jacobiTheta τ ^ 6 = Lsum W τ := by
  have hG := eq_zero_of_invariant mdiff_Gfun Gfun_slash_S Gfun_slash_T_sq norm_Gfun_le
    norm_Gfun_TS_le
  have h := congrFun hG τ
  simp only [Gfun, Pi.zero_apply] at h
  have := pow_eq_zero_iff (n := 4) (by norm_num) |>.mp h
  rw [gfun, sub_eq_zero] at this
  exact this

/-! ### Real values -/

/-- `κ = ∑_{n ∈ ℤ} χ(n) n⁻³` as a real number. -/
def kappaR : ℝ := ∑' n : ℤ, ((ZMod.χ₄ (n : ZMod 4) : ℤ) : ℝ) * (1 / (n : ℝ) ^ 3)

lemma kappa_eq_ofReal : kappa = (kappaR : ℂ) := by
  rw [kappa, kappaR, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  simp [chiZ]

lemma chiZ_natCast (r : ℕ) : chiZ (r : ℤ) = (chi4R r : ℂ) := by
  simp [chiZ, chi4R]

lemma seriesA_ofReal (x : ℝ) : seriesA (x : ℂ) = (sixSeriesA x : ℂ) := by
  rw [seriesA, sixSeriesA, Complex.ofReal_tsum]
  refine tsum_congr fun k => ?_
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun r => ?_
  rw [chiZ_natCast]; push_cast; ring

lemma chi4R_even (k : ℕ) : chi4R (2 * k + 1 + 1) = 0 := by
  rw [chi4R, ZMod.χ₄_nat_eq_if_mod_four, if_pos (by omega)]; simp

lemma seriesB_ofReal {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    seriesB (x : ℂ) = (sixSeriesB x : ℂ) := by
  set g : ℕ → ℝ := fun k => chi4R (2 * k + 1) * ∑' r : ℕ, (r : ℝ) ^ 2 * x ^ (r * (2 * k + 1))
    with hg
  have hterm : ∀ k : ℕ, chiZ (2 * (k : ℤ) + 1) * ∑' r : ℕ, (r : ℂ) ^ 2 * (x : ℂ) ^ (r * (2 * k + 1)) =
      (g k : ℂ) := by
    intro k
    rw [hg]
    have : chiZ (2 * (k : ℤ) + 1) = chiZ ((2 * k + 1 : ℕ) : ℤ) := by push_cast; rfl
    rw [this, chiZ_natCast]
    push_cast
    norm_cast
  have hq : ‖(x : ℂ)‖ ≤ 1 / 2 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hx0]; exact hx
  have hsC := summable_seriesB_terms hq
  have hsR : Summable g := by
    rw [← Complex.summable_ofReal]
    exact hsC.congr hterm
  have ho : Summable fun k : ℕ =>
      chi4R (2 * k + 1 + 1) * ∑' r : ℕ, (r : ℝ) ^ 2 * x ^ (r * (2 * k + 1 + 1)) := by
    simp only [chi4R_even, zero_mul]; exact summable_zero
  have := tsum_even_add_odd (f := fun m : ℕ =>
    chi4R (m + 1) * ∑' r : ℕ, (r : ℝ) ^ 2 * x ^ (r * (m + 1))) hsR ho
  rw [sixSeriesB, ← this]
  simp only [chi4R_even, zero_mul, tsum_zero, add_zero]
  rw [seriesB, tsum_congr hterm, ← Complex.ofReal_tsum]

end NTKB.HardyWright.SixSquares

namespace NTKB.HardyWright

open SixSquares

/-- `κ θ(it)⁶ = L_W(it)` as an identity of real power series in `x = e^{-πt}`. -/
lemma theta_pow_six_real {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1 / 2) :
    kappaR * (∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 6 =
      kappaR - Real.pi ^ 3 / 4 * sixSeriesA x + Real.pi ^ 3 * sixSeriesB x := by
  have hx1' : x < 1 := by linarith
  set t := -Real.log x / π with ht
  have htpos : 0 < t := by
    have : Real.log x < 0 := Real.log_neg hx0 hx1'
    rw [ht]; exact div_pos (by linarith) Real.pi_pos
  have hxt : rexp (-π * t) = x := by
    rw [ht, show -π * (-Real.log x / π) = Real.log x by field_simp]; exact Real.exp_log hx0
  set τ : ℍ := ⟨I * t, by simpa using htpos⟩ with hτ
  have hτc : (τ : ℂ) = I * t := rfl
  have h := kappa_mul_theta_pow_six τ
  have hθ : jacobiTheta (τ : ℂ) = ((∑' m : ℤ, x ^ (m.natAbs ^ 2) : ℝ) : ℂ) := by
    rw [jacobiTheta, Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    rw [hτc, ← hxt, ← Real.exp_nat_mul, Complex.ofReal_exp]
    congr 1
    have hn : ((n.natAbs : ℕ) : ℂ) ^ 2 = (n : ℂ) ^ 2 := by
      have : ((n.natAbs : ℤ) : ℂ) ^ 2 = (n : ℂ) ^ 2 := by
        rw [← Int.cast_pow, Int.natAbs_sq]; push_cast; ring
      rwa [Int.cast_natCast] at this
    push_cast
    linear_combination (↑π * ↑t * (n : ℂ) ^ 2) * I_sq + (↑π * ↑t) * hn
  have hq : cexp (π * I * τ) = (x : ℂ) := by
    rw [hτc, ← hxt, Complex.ofReal_exp]
    congr 1
    push_cast
    linear_combination (↑π * ↑t) * I_sq
  rw [Lsum_W_eq] at h
  rw [hq] at h
  rw [kappa_eq_ofReal] at h
  rw [hθ] at h
  rw [seriesA_ofReal] at h
  rw [seriesB_ofReal hx0.le hx1.le] at h
  generalize (∑' m : ℤ, x ^ (m.natAbs ^ 2)) = θR at h ⊢
  have h' : ((kappaR * θR ^ 6 : ℝ) : ℂ) =
      ((kappaR + Real.pi ^ 3 * sixSeriesB x - Real.pi ^ 3 / 4 * sixSeriesA x : ℝ) : ℂ) := by
    push_cast; linear_combination h
  have := Complex.ofReal_injective h'
  rw [this]; ring

/-- **Jacobi's formula for `r₆`** (Hardy–Wright (20.13.1)). For `n ≥ 1`, the number of
representations of `n` as a sum of six squares of integers (order and signs counted) is
`16 ∑_{d ∣ n} χ(n/d) d² - 4 ∑_{d ∣ n} χ(d) d²`, `χ` the non-principal character modulo `4`. -/
@[kb "hardywright2008" "Section 20.13, p. 434"]
theorem sumSquaresCount_six_eq {n : ℕ} (hn : 0 < n) :
    (sumSquaresCount 6 n : ℂ) = jacobiSixSum n :=
  sumSquaresCount_six_eq_of_forall (κ := kappaR) (fun _ hx0 hx1 => theta_pow_six_real hx0 hx1) hn

/-- Hardy–Wright (20.13.1), the statement `JacobiSixSquares`. -/
theorem jacobiSixSquares : JacobiSixSquares := fun _ hn => sumSquaresCount_six_eq hn

end NTKB.HardyWright
