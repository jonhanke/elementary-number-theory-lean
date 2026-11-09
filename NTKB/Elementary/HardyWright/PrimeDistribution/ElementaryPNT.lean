/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.PrimeDistribution.Theorem436
import NTKB.Analytic.Apostol.Primes.PNTForms
import NTKB.Analytic.Apostol.Primes.ChebyshevForms

/-!
# The elementary proof of the prime number theorem (Hardy–Wright, Chapter XXII, § 22.16)

Hardy–Wright prove `V(ξ) = e^{-ξ} ψ(e^ξ) - 1 → 0` from (22.15.9), Theorem 435 and Theorem 436:
with `α = limsup |V(ξ)|` and `β = limsup ξ⁻¹ ∫₀^ξ |V(η)| dη`, (22.15.9) gives `α ≤ β` (22.15.11);
if `α > 0`, then splitting `[0, ξ]` into intervals of length `δ = (3α² + 4A₁)/(2α)` and using
Theorem 436 on the intervals that contain a zero of `V`, Theorem 435 on the others, gives
`β ≤ α' = α (2α² + 4A₁)/(3α² + 4A₁) < α`, a contradiction.

We avoid upper limits: `α` is the infimum of the eventual bounds of `|V|`, and the book's two steps
are `eventually_abs_selbergV_le_of_integral` ((22.15.10)–(22.15.11)) and the block estimate inside
`tendsto_selbergV`.

* **Theorem 434**: `ψ(x)/x → 1`; then **Theorem 6** (the prime number theorem, `π(x) log x / x → 1`)
  and **Theorem 8** (`p_n ~ n log n`) follow by the elementary equivalences of Theorem 420 and § 1.8
  (here Apostol's Theorems 4.4 and 4.5 in NTKB, which are proved from Chebyshev's estimates).

This proof does not use the analytic prime number theorem of `NTKB.Analytic.Apostol.PNT`.
-/

open Finset ArithmeticFunction Real Chebyshev MeasureTheory Filter Set
open scoped Topology

namespace NTKB.HardyWright

open NTKB.Apostol

/-- `∫₀^ζ |V| ≤ b ζ + D` for all `ζ ≥ 0` implies `∫₀^ξ |V(η)| (ξ - η) dη ≤ b ξ²/2 + D ξ`. -/
theorem integral_abs_selbergV_mul_sub_le {b D ξ : ℝ} (hξ : 0 ≤ ξ)
    (hW : ∀ ζ, 0 ≤ ζ → ∫ η in (0 : ℝ)..ζ, |selbergV η| ≤ b * ζ + D) :
    ∫ η in (0 : ℝ)..ξ, |selbergV η| * (ξ - η) ≤ b * ξ ^ 2 / 2 + D * ξ := by
  rw [integral_abs_selbergV_mul_sub_eq]
  have hWc : Continuous fun ζ ↦ ∫ η in (0 : ℝ)..ζ, |selbergV η| :=
    intervalIntegral.continuous_primitive (fun a b ↦ intervalIntegrable_abs_selbergV a b) 0
  calc ∫ ζ in (0 : ℝ)..ξ, ∫ η in (0 : ℝ)..ζ, |selbergV η|
      ≤ ∫ ζ in (0 : ℝ)..ξ, (b * ζ + D) :=
        intervalIntegral.integral_mono_on hξ (hWc.intervalIntegrable 0 ξ)
          ((continuous_const.mul continuous_id).add continuous_const |>.intervalIntegrable 0 ξ)
          fun ζ hζ ↦ hW ζ hζ.1
    _ = b * ξ ^ 2 / 2 + D * ξ := by
        rw [intervalIntegral.integral_add (f := fun ζ : ℝ ↦ b * ζ) (g := fun _ ↦ D)
          ((continuous_const.mul continuous_id).intervalIntegrable 0 ξ) intervalIntegrable_const,
          intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const,
          smul_eq_mul]
        ring

/-- Hardy–Wright (22.15.10)–(22.15.11): if `∫₀^ζ |V| ≤ b ζ` for all large `ζ`, then
`|V(ξ)| ≤ b + ε` for all large `ξ` (that is, `α ≤ β`). -/
theorem eventually_abs_selbergV_le_of_integral {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ᶠ ζ in atTop, ∫ η in (0 : ℝ)..ζ, |selbergV η| ≤ b * ζ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ ξ in atTop, |selbergV ξ| ≤ b + ε := by
  obtain ⟨K, hK0, hK⟩ := sq_mul_abs_selbergV_le
  obtain ⟨Z, hZ⟩ := eventually_atTop.1 h
  set c := Real.log 4 + 5 with hc
  have hc0 : 0 ≤ c := by have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith
  set D := c * max Z 0 with hD
  have hD0 : 0 ≤ D := mul_nonneg hc0 (le_max_right _ _)
  have hW : ∀ ζ, 0 ≤ ζ → ∫ η in (0 : ℝ)..ζ, |selbergV η| ≤ b * ζ + D := by
    intro ζ hζ
    by_cases hζZ : Z ≤ ζ
    · have := hZ ζ hζZ; linarith
    · have h1 := integral_abs_selbergV_le hζ
      have h2 : ζ ≤ max Z 0 := (not_le.1 hζZ).le.trans (le_max_left _ _)
      have h3 : c * ζ ≤ D := mul_le_mul_of_nonneg_left h2 hc0
      have h4 : 0 ≤ b * ζ := mul_nonneg hb hζ
      rw [sub_zero] at h1
      linarith
  refine eventually_atTop.2 ⟨max 1 ((2 * D + 2 * K) / ε), fun ξ hξ ↦ ?_⟩
  have hξ1 : 1 ≤ ξ := le_of_max_le_left hξ
  have hξ0 : 0 ≤ ξ := by linarith
  have hξε : (2 * D + 2 * K) / ε ≤ ξ := le_of_max_le_right hξ
  have hint := integral_abs_selbergV_mul_sub_le hξ0 hW
  have h9 := hK ξ hξ0
  have h1 : K * (1 + ξ) ≤ 2 * K * ξ := by nlinarith
  have h2 : 2 * D + 2 * K ≤ ε * ξ := by
    have := (div_le_iff₀ hε).1 hξε; linarith
  have h3 : ξ ^ 2 * |selbergV ξ| ≤ ξ ^ 2 * (b + ε) := by nlinarith
  exact le_of_mul_le_mul_left h3 (by positivity)

/-- Hardy–Wright § 22.16: `V(ξ) → 0` as `ξ → ∞`. -/
theorem tendsto_selbergV : Tendsto selbergV atTop (𝓝 0) := by
  set c := Real.log 4 + 5 with hc
  have hc0 : 0 ≤ c := by have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith
  have ii : ∀ a b : ℝ, IntervalIntegrable (fun t ↦ |selbergV t|) volume a b :=
    intervalIntegrable_abs_selbergV
  set S : Set ℝ := {a | 0 ≤ a ∧ ∀ᶠ η in atTop, |selbergV η| ≤ a} with hS
  have hSne : S.Nonempty := ⟨c, hc0, Eventually.of_forall abs_selbergV_le⟩
  have hSbdd : BddBelow S := ⟨0, fun a ha ↦ ha.1⟩
  set α := sInf S with hα
  have hα0 : 0 ≤ α := le_csInf hSne fun a ha ↦ ha.1
  have hαε : ∀ ε > 0, ∀ᶠ η in atTop, |selbergV η| ≤ α + ε := by
    intro ε hε
    obtain ⟨a, haS, ha⟩ := exists_lt_of_csInf_lt hSne (show α < α + ε by linarith)
    exact haS.2.mono fun η h ↦ h.trans ha.le
  suffices hα00 : α = 0 by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hαε (ε / 2) (by linarith)] with η hη
    rw [Real.dist_eq, sub_zero]
    linarith
  by_contra hne
  have hαpos : 0 < α := lt_of_le_of_ne hα0 (Ne.symm hne)
  obtain ⟨A₁, hA₁0, hA₁⟩ := abs_integral_selbergV_le
  obtain ⟨C, hC0, hC⟩ := integral_abs_selbergV_add_le
  set δ := (3 * α ^ 2 + 4 * A₁) / (2 * α) with hδ
  have hδpos : 0 < δ := by positivity
  have hδα : α < δ := by
    rw [hδ, lt_div_iff₀ (by positivity)]; nlinarith
  set α' := (α ^ 2 + 2 * A₁) / δ with hα'
  have hα'δ : α' * δ = α ^ 2 + 2 * A₁ := by rw [hα']; field_simp
  have hα'0 : 0 ≤ α' := by positivity
  have hαδ : α * δ = (3 * α ^ 2 + 4 * A₁) / 2 := by rw [hδ]; field_simp
  have hα'lt : α' < α := by
    have h2 : α' * δ < α * δ := by rw [hα'δ, hαδ]; nlinarith
    exact lt_of_mul_lt_mul_right h2 hδpos.le
  set ε := (α - α') / 6 with hε
  have hεpos : 0 < ε := by linarith
  -- the block estimate: `∫_ζ^{ζ+δ} |V| ≤ (α' + ε) δ` for large `ζ`
  have hblock : ∃ H ≥ (1 : ℝ), ∀ ζ ≥ H, ∫ η in ζ..ζ + δ, |selbergV η| ≤ (α' + ε) * δ := by
    obtain ⟨H₀, hH₀⟩ := eventually_atTop.1 (hαε (ε / 2) (by positivity))
    refine ⟨max (max H₀ 1) (2 * C * α / (ε * δ)), le_max_of_le_left (le_max_right _ _),
      fun ζ hζ ↦ ?_⟩
    have hζH₀ : H₀ ≤ ζ := (le_max_left _ _).trans ((le_max_left _ _).trans hζ)
    have hζ1 : 1 ≤ ζ := (le_max_right _ _).trans ((le_max_left _ _).trans hζ)
    have hζC : 2 * C * α / (ε * δ) ≤ ζ := (le_max_right _ _).trans hζ
    have hζ0 : 0 < ζ := by linarith
    have hbound : ∀ η, ζ ≤ η → |selbergV η| ≤ α + ε / 2 := fun η h ↦ hH₀ η (hζH₀.trans h)
    have hCζ : C * α / ζ ≤ ε * δ / 2 := by
      rw [div_le_iff₀ hζ0]
      rw [div_le_iff₀ (by positivity)] at hζC
      nlinarith
    by_cases hz : ∃ η₀ ∈ Icc ζ (ζ + δ - α), selbergV η₀ = 0
    · obtain ⟨η₀, hη₀, hV0⟩ := hz
      have hsplit : ∫ η in ζ..ζ + δ, |selbergV η| = (∫ η in ζ..η₀, |selbergV η|) +
          (∫ η in η₀..η₀ + α, |selbergV η|) + ∫ η in η₀ + α..ζ + δ, |selbergV η| := by
        rw [intervalIntegral.integral_add_adjacent_intervals (ii _ _) (ii _ _),
          intervalIntegral.integral_add_adjacent_intervals (ii _ _) (ii _ _)]
      have h1 : ∫ η in ζ..η₀, |selbergV η| ≤ (α + ε / 2) * (η₀ - ζ) :=
        integral_abs_selbergV_le_of_le hη₀.1 fun t ht ↦ hbound t ht.1
      have h2 : ∫ η in η₀..η₀ + α, |selbergV η| ≤ α ^ 2 / 2 + C * α / η₀ := by
        have := hC α η₀ hα0 (by linarith [hη₀.1]) hV0
        rw [intervalIntegral.integral_comp_add_left (fun t ↦ |selbergV t|) η₀, add_zero] at this
        exact this
      have h2' : C * α / η₀ ≤ C * α / ζ :=
        div_le_div_of_nonneg_left (by positivity) hζ0 hη₀.1
      have h3 : ∫ η in η₀ + α..ζ + δ, |selbergV η| ≤ (α + ε / 2) * (ζ + δ - (η₀ + α)) :=
        integral_abs_selbergV_le_of_le (by linarith [hη₀.2]) fun t ht ↦
          hbound t (by linarith [ht.1, hη₀.1])
      rw [hsplit]
      have h4 : (α + ε / 2) * (η₀ - ζ) + (α + ε / 2) * (ζ + δ - (η₀ + α)) =
          (α + ε / 2) * (δ - α) := by ring
      have h5 : ε / 2 * (δ - α) ≤ ε / 2 * δ := by nlinarith
      have h6 : (α' + ε) * δ = α ^ 2 + 2 * A₁ + ε * δ := by rw [add_mul, hα'δ]
      have h7 : (α + ε / 2) * (δ - α) = α * δ - α ^ 2 + ε / 2 * (δ - α) := by ring
      linarith
    · have hz' : ∀ η ∈ Icc ζ (ζ + δ - α), selbergV η ≠ 0 := fun η hη h0 ↦ hz ⟨η, hη, h0⟩
      have h1 := integral_abs_selbergV_le_of_ne_zero hA₁ hζ0.le (by linarith) hz'
      have h2 : ∫ η in ζ + δ - α..ζ + δ, |selbergV η| ≤ (α + ε / 2) * (ζ + δ - (ζ + δ - α)) :=
        integral_abs_selbergV_le_of_le (by linarith) fun t ht ↦ hbound t (by linarith [ht.1])
      rw [← intervalIntegral.integral_add_adjacent_intervals (ii ζ (ζ + δ - α)) (ii _ _)]
      have h5 : ε / 2 * α ≤ ε / 2 * δ := by nlinarith
      have h6 : (α' + ε) * δ = α ^ 2 + 2 * A₁ + ε * δ := by rw [add_mul, hα'δ]
      have h7 : (α + ε / 2) * (ζ + δ - (ζ + δ - α)) = α ^ 2 + ε / 2 * α := by ring
      have h8 : 0 ≤ ε * δ := by positivity
      linarith
  obtain ⟨H, hH1, hH⟩ := hblock
  -- summing the blocks
  have hiter : ∀ M : ℕ, ∫ η in H..H + M * δ, |selbergV η| ≤ M * ((α' + ε) * δ) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      have e : H + ((M + 1 : ℕ) : ℝ) * δ = H + M * δ + δ := by push_cast; ring
      rw [e, ← intervalIntegral.integral_add_adjacent_intervals (ii H (H + M * δ)) (ii _ _)]
      have := hH (H + M * δ) (by nlinarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)])
      push_cast
      linarith
  -- the mean value bound `∫₀^ξ |V| ≤ (α' + 2ε) ξ` for large `ξ`
  have havg : ∀ᶠ ξ in atTop, ∫ η in (0 : ℝ)..ξ, |selbergV η| ≤ (α' + 2 * ε) * ξ := by
    refine eventually_atTop.2 ⟨max H (c * (H + δ) / ε), fun ξ hξ ↦ ?_⟩
    have hξH : H ≤ ξ := le_of_max_le_left hξ
    have hξc : c * (H + δ) / ε ≤ ξ := le_of_max_le_right hξ
    set M := ⌊(ξ - H) / δ⌋₊ with hM
    have hM1 : (M : ℝ) * δ ≤ ξ - H := by
      have := Nat.floor_le (div_nonneg (by linarith : 0 ≤ ξ - H) hδpos.le)
      rwa [le_div_iff₀ hδpos] at this
    have hM2 : ξ - H < (M + 1) * δ := by
      have := Nat.lt_floor_add_one ((ξ - H) / δ)
      rwa [div_lt_iff₀ hδpos] at this
    rw [← intervalIntegral.integral_add_adjacent_intervals (ii 0 H) (ii H ξ),
      ← intervalIntegral.integral_add_adjacent_intervals (ii H (H + M * δ)) (ii _ ξ)]
    have h1 := integral_abs_selbergV_le (show (0 : ℝ) ≤ H by linarith)
    have h2 := hiter M
    have h3 := integral_abs_selbergV_le (show H + M * δ ≤ ξ by linarith)
    have hαε0 : 0 ≤ α' + ε := by linarith
    have h4 : (M : ℝ) * ((α' + ε) * δ) ≤ (α' + ε) * (ξ - H) := by nlinarith
    have h5 : c * (H + δ) ≤ ε * ξ := by
      have := (div_le_iff₀ hεpos).1 hξc; linarith
    have h6 : c * (ξ - (H + M * δ)) ≤ c * δ := by
      apply mul_le_mul_of_nonneg_left _ hc0; linarith
    have h7 : (α' + ε) * (ξ - H) ≤ (α' + ε) * ξ := by nlinarith
    rw [sub_zero] at h1
    nlinarith
  have hstepA := eventually_abs_selbergV_le_of_integral (by linarith : 0 ≤ α' + 2 * ε) havg hεpos
  have hmem : α' + 3 * ε ∈ S := ⟨by linarith, hstepA.mono fun η h ↦ by linarith⟩
  have := csInf_le hSbdd hmem
  linarith

/-- **Theorem 434.** `ψ(x) ~ x`, i.e. `ψ(x)/x → 1` (Hardy–Wright's elementary proof, §§ 22.14–22.16,
from Selberg's theorem). -/
@[kb "hardywright2008" "Thm 434, p. 500"]
theorem tendsto_psi_div_self : Tendsto (fun x ↦ ψ x / x) atTop (𝓝 1) := by
  have h := (tendsto_selbergV.comp Real.tendsto_log_atTop).add_const 1
  rw [zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp only [Function.comp, selbergV, Real.exp_log hx, Real.exp_neg]
  field_simp
  ring

/-- **Theorem 6** (the prime number theorem). `π(x) ~ x / log x`, i.e. `π(x) log x / x → 1`;
deduced from Theorem 434 as in the book (§ 22.4, Theorem 420). -/
@[kb "hardywright2008" "Thm 6, p. 29"]
theorem prime_number_theorem :
    Tendsto (fun x : ℝ ↦ (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x / x) atTop (𝓝 1) :=
  apostol_thm_4_4.1.mpr (apostol_thm_4_4.2.mpr tendsto_psi_div_self)

/-- **Theorem 8.** `p_n ~ n log n`: with `p_n = nth Nat.Prime (n - 1)` the `n`-th prime,
`p_{n} / (n log n) → 1` (written with the index shifted by one). -/
@[kb "hardywright2008" "Thm 8, p. 31"]
theorem nth_prime_asymptotic :
    Tendsto (fun n : ℕ ↦ (Nat.nth Nat.Prime n : ℝ) / (((n : ℝ) + 1) * Real.log ((n : ℝ) + 1)))
      atTop (𝓝 1) :=
  apostol_thm_4_5.2.mp (apostol_thm_4_5.1.mp prime_number_theorem)

end NTKB.HardyWright
