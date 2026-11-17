/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.SummableUniformlyOn

/-!
# Iterated derivatives of exponential sums

For families `c, u : ι → ℂ` with `∑ᵢ ‖cᵢ‖ e^{R ‖uᵢ‖} < ∞` for every `R`, the function
`f(z) = ∑ᵢ cᵢ e^{uᵢ z}` is entire and its `k`-th derivative is `∑ᵢ cᵢ uᵢᵏ e^{uᵢ z}`
(`iteratedDeriv_expSum`). Used to read off the Taylor coefficient of `z⁴` in products of
two-variable theta functions (the weight-`5` cusp form of Liouville's `r₁₀` formula).
-/

open Complex Filter Topology

noncomputable section

namespace NTKB.HardyWright.TenSquares

variable {ι : Type*}

/-- The summability hypothesis on an exponential sum. -/
def ExpSummable (c u : ι → ℂ) : Prop := ∀ R : ℝ, Summable fun i => ‖c i‖ * Real.exp (R * ‖u i‖)

/-- `∑ᵢ cᵢ e^{uᵢ z}`. -/
def expSum (c u : ι → ℂ) (z : ℂ) : ℂ := ∑' i, c i * cexp (u i * z)

lemma norm_cexp_mul_le (u z : ℂ) : ‖cexp (u * z)‖ ≤ Real.exp (‖u‖ * ‖z‖) := by
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.mpr ?_
  calc (u * z).re ≤ ‖u * z‖ := Complex.re_le_norm _
    _ = ‖u‖ * ‖z‖ := norm_mul _ _

lemma pow_le_factorial_mul_exp {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    t ^ k ≤ (k.factorial : ℝ) * Real.exp t := by
  have h := Real.pow_div_factorial_le_exp t ht k
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  rw [div_le_iff₀ hk] at h
  linarith

/-- The bound on the derivative terms on the ball of radius `R`. -/
lemma norm_term_le {c u : ℂ} (k : ℕ) {R : ℝ} {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖c * u ^ k * cexp (u * z)‖ ≤ k.factorial * (‖c‖ * Real.exp ((R + 1) * ‖u‖)) := by
  have h1 : ‖cexp (u * z)‖ ≤ Real.exp (R * ‖u‖) :=
    (norm_cexp_mul_le u z).trans (Real.exp_le_exp.mpr (by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)))
  have h2 : ‖u‖ ^ k ≤ k.factorial * Real.exp ‖u‖ := pow_le_factorial_mul_exp (norm_nonneg _) k
  rw [norm_mul, norm_mul, norm_pow]
  calc ‖c‖ * ‖u‖ ^ k * ‖cexp (u * z)‖
      ≤ ‖c‖ * (k.factorial * Real.exp ‖u‖) * Real.exp (R * ‖u‖) := by gcongr
    _ = k.factorial * (‖c‖ * Real.exp ((R + 1) * ‖u‖)) := by
        rw [add_mul, one_mul, Real.exp_add]; ring

lemma summable_term {c u : ι → ℂ} (h : ExpSummable c u) (k : ℕ) (z : ℂ) :
    Summable fun i => c i * u i ^ k * cexp (u i * z) :=
  Summable.of_norm_bounded ((h (‖z‖ + 1)).mul_left (k.factorial : ℝ))
    fun i => norm_term_le k le_rfl

lemma iteratedDerivWithin_term (c u : ℂ) (k : ℕ) :
    iteratedDerivWithin k (fun z => c * cexp (u * z)) Set.univ =
      fun z => c * u ^ k * cexp (u * z) := by
  rw [iteratedDerivWithin_univ]
  funext z
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_cexp_const_mul]
  ring

/-- **Iterated derivatives of an exponential sum.** -/
theorem iteratedDeriv_expSum {c u : ι → ℂ} (h : ExpSummable c u) (k : ℕ) (z : ℂ) :
    iteratedDeriv k (expSum c u) z = ∑' i, c i * u i ^ k * cexp (u i * z) := by
  rw [← iteratedDerivWithin_univ]
  have e : expSum c u = fun z => ∑' i, c i * cexp (u i * z) := rfl
  rw [e, iteratedDerivWithin_tsum k isOpen_univ (Set.mem_univ z)]
  · refine tsum_congr fun i => ?_
    rw [iteratedDerivWithin_term]
  · intro t _
    simpa using summable_term h 0 t
  · intro j _ _
    refine SummableLocallyUniformlyOn_of_locally_bounded isOpen_univ fun K _ hK => ?_
    obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
    refine ⟨fun i => j.factorial * (‖c i‖ * Real.exp ((R + 1) * ‖u i‖)),
      (h (R + 1)).mul_left _, fun i x hx => ?_⟩
    rw [iteratedDerivWithin_term]
    exact norm_term_le j (hR x hx)
  · intro _ j r _ _
    rw [iteratedDerivWithin_term]
    exact ((differentiable_const _).mul
      ((differentiable_id.const_mul _).cexp)).differentiableAt

lemma differentiable_expSum {c u : ι → ℂ} (h : ExpSummable c u) : Differentiable ℂ (expSum c u) := by
  intro z
  have hs : SummableLocallyUniformlyOn (fun i z => c i * cexp (u i * z)) Set.univ := by
    refine SummableLocallyUniformlyOn_of_locally_bounded isOpen_univ fun K _ hK => ?_
    obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
    refine ⟨fun i => (0 : ℕ).factorial * (‖c i‖ * Real.exp ((R + 1) * ‖u i‖)),
      (h (R + 1)).mul_left _, fun i x hx => ?_⟩
    have := norm_term_le (c := c i) (u := u i) 0 (hR x hx)
    simpa using this
  have hdo := SummableLocallyUniformlyOn.differentiableOn isOpen_univ hs (fun _ _ _ =>
    ((differentiable_const _).mul ((differentiable_id.const_mul _).cexp)).differentiableAt)
  exact (hdo z (Set.mem_univ z)).differentiableAt (isOpen_univ.mem_nhds (Set.mem_univ z))

lemma contDiff_expSum {c u : ι → ℂ} (h : ExpSummable c u) (n : ℕ∞) :
    ContDiff ℂ n (expSum c u) :=
  (differentiable_expSum h).contDiff.of_le (by exact_mod_cast le_top)

/-- The `k`-th derivative at `0`. -/
lemma iteratedDeriv_expSum_zero {c u : ι → ℂ} (h : ExpSummable c u) (k : ℕ) :
    iteratedDeriv k (expSum c u) 0 = ∑' i, c i * u i ^ k := by
  rw [iteratedDeriv_expSum h]
  simp

/-- Comparing `k`-th Taylor coefficients of `z ↦ f(a z)` and `z ↦ b g(z)` for exponential sums. -/
lemma coeff_eq_of_expSum_eq {ι' : Type*} {c u : ι → ℂ} {c' u' : ι' → ℂ} (h : ExpSummable c u)
    (h' : ExpSummable c' u') (a b : ℂ) (he : ∀ z, expSum c u (a * z) = b * expSum c' u' z) (k : ℕ) :
    a ^ k * ∑' i, c i * u i ^ k = b * ∑' i, c' i * u' i ^ k := by
  have e : (fun z => expSum c u (a * z)) = fun z => b * expSum c' u' z := funext he
  have h1 := congrFun (iteratedDeriv_comp_const_mul (contDiff_expSum h k) a) 0
  rw [e, iteratedDeriv_const_mul_field, mul_zero, iteratedDeriv_expSum_zero h,
    iteratedDeriv_expSum_zero h'] at h1
  exact h1.symm

end NTKB.HardyWright.TenSquares
