/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.PrimeDistribution.FunctionV

/-!
# Theorem 436, (22.15.9), and intervals without zeros of `V` (Hardy–Wright, §§ 22.15–22.16)

* **Theorem 436**: if `η₀ > 0` and `V(η₀) = 0`, then `|V(η₀ + τ)| ≤ τ + O(1/η₀)` for `τ ≥ 0`
  (the book's intermediate inequality), hence `∫₀^α |V(η₀ + τ)| dτ ≤ α²/2 + O(1/η₀)`. As in the
  book, it comes from (22.14.3): `∑_{n ≤ x} aₙ` increases with `x`, so for `x ≥ x₀ ≥ 1`
  `0 ≤ ψ(x) log x - ψ(x₀) log x₀ ≤ 2 (x log x - x₀ log x₀) + O(x)`.
* (22.15.9) `ξ² |V(ξ)| ≤ 2 ∫₀^ξ |V(η)| (ξ - η) dη + O(1 + ξ)` (from (22.15.7) by the substitution
  `x = e^ξ`, `t = x e^{-η}`), and `∫₀^ξ |V(η)| (ξ - η) dη = ∫₀^ξ ∫₀^ζ |V(η)| dη dζ` (by an
  integration by parts, where the book changes the order of integration).
* On an interval `[p, q] ⊆ [0, ∞)` without zeros of `V`, `V` changes sign at most once, so
  `∫_p^q |V| ≤ 2 A₁` with `A₁` from Theorem 435.
-/

open Finset ArithmeticFunction Real Chebyshev MeasureTheory Filter Set
open scoped Topology

namespace NTKB.HardyWright

open NTKB.Apostol

/-- For `1 ≤ y₀ ≤ y`: `ψ(y) log y - ψ(y₀) log y₀ ≤ 2 (y log y - y₀ log y₀) + O(y)`, from (22.14.3)
since `∑_{mn ≤ x} Λ(m) Λ(n)` increases with `x` (Hardy–Wright, proof of Theorem 436). -/
theorem psi_mul_log_sub_le :
    ∃ K ≥ 0, ∀ y₀ y : ℝ, 1 ≤ y₀ → y₀ ≤ y →
      ψ y * Real.log y - ψ y₀ * Real.log y₀ ≤
        2 * (y * Real.log y - y₀ * Real.log y₀) + K * y := by
  obtain ⟨K₂, hK₂⟩ := selberg_theorem'
  have hK₂0 : 0 ≤ K₂ := by
    have := (abs_nonneg _).trans (hK₂ 1 le_rfl); linarith
  have hc : 0 ≤ (Real.log 4 + 4) * (1 + Real.log 2) := by
    have := log_four_add_four_pos.le
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    positivity
  refine ⟨2 * K₂ + (Real.log 4 + 4) * (1 + Real.log 2), by positivity, fun y₀ y h0 h ↦ ?_⟩
  have hy : 1 ≤ y := h0.trans h
  have hy0 : 0 < y := by linarith
  have hy00 : 0 < y₀ := by linarith
  rw [psi_mul_log_eq hy0, psi_mul_log_eq hy00]
  have hT := hK₂ y hy
  have hT0 := hK₂ y₀ h0
  rw [sum_selbergCoeff_eq] at hT hT0
  have hP : ∑ n ∈ Ioc 0 ⌊y₀⌋₊, (Λ * Λ : ArithmeticFunction ℝ) n ≤
      ∑ n ∈ Ioc 0 ⌊y⌋₊, (Λ * Λ : ArithmeticFunction ℝ) n :=
    sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_right (Nat.floor_mono h))
      fun n _ _ ↦ vonMangoldt_mul_vonMangoldt_nonneg n
  obtain ⟨hD0, -⟩ := sum_vonMangoldt_mul_log_div_le h0
  obtain ⟨-, hD⟩ := sum_vonMangoldt_mul_log_div_le hy
  rw [abs_le] at hT hT0
  nlinarith

/-- **Theorem 436** (pointwise form, as in the book's proof). There is `C` such that, if `η₀ > 0`
and `V(η₀) = 0`, then `|V(η₀ + τ)| ≤ τ + C/η₀` for all `τ ≥ 0`. -/
@[kb "hardywright2008" "Thm 436, p. 506"]
theorem abs_selbergV_add_le :
    ∃ C ≥ 0, ∀ η₀ τ : ℝ, 0 < η₀ → 0 ≤ τ → selbergV η₀ = 0 →
      |selbergV (η₀ + τ)| ≤ τ + C / η₀ := by
  obtain ⟨K, hK0, hK⟩ := psi_mul_log_sub_le
  refine ⟨K + 1, by positivity, fun η₀ τ hη₀ hτ hV ↦ ?_⟩
  set y₀ := Real.exp η₀ with hy₀
  set y := Real.exp (η₀ + τ) with hy
  have h0 : 1 ≤ y₀ := Real.one_le_exp hη₀.le
  have h0y : y₀ ≤ y := Real.exp_le_exp.2 (by linarith)
  have hly₀ : Real.log y₀ = η₀ := Real.log_exp _
  have hly : Real.log y = η₀ + τ := Real.log_exp _
  have hR0 : psiRem y₀ = 0 := by
    rw [selbergV_eq] at hV
    exact (mul_eq_zero.1 hV).resolve_left (Real.exp_pos _).ne'
  have hψ0 : ψ y₀ = y₀ := by rw [psiRem] at hR0; linarith
  have hup := hK y₀ y h0 h0y
  have hlow : ψ y₀ * Real.log y₀ ≤ ψ y * Real.log y :=
    mul_le_mul (psi_mono h0y) (Real.log_le_log (by linarith) h0y)
      (Real.log_nonneg h0) (psi_nonneg _)
  rw [hψ0, hly₀, hly] at hup hlow
  -- `|R(y)| log y ≤ y log y - y₀ log y₀ + K y`
  have hpos : 0 < η₀ + τ := by linarith
  have hRy : |psiRem y| * (η₀ + τ) ≤ y * (η₀ + τ) - y₀ * η₀ + K * y := by
    have hmul : y₀ * η₀ ≤ y * (η₀ + τ) := mul_le_mul h0y (by linarith) hη₀.le (by linarith)
    have habs : |psiRem y * (η₀ + τ)| ≤ y * (η₀ + τ) - y₀ * η₀ + K * y := by
      rw [abs_le, psiRem]
      constructor <;> nlinarith
    rwa [abs_mul, abs_of_pos hpos] at habs
  -- divide by `y = e^{η₀ + τ}`
  set E := Real.exp (-τ) with hE
  have hyE : Real.exp (-(η₀ + τ)) * y = 1 := by
    rw [hy, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hy₀E : Real.exp (-(η₀ + τ)) * y₀ = E := by
    rw [hy₀, ← Real.exp_add, hE]; ring_nf
  have hV' : |selbergV (η₀ + τ)| * (η₀ + τ) ≤ (η₀ + τ) - E * η₀ + K := by
    rw [abs_selbergV_eq, mul_assoc]
    have := mul_le_mul_of_nonneg_left hRy (Real.exp_pos (-(η₀ + τ))).le
    calc _ ≤ Real.exp (-(η₀ + τ)) * (y * (η₀ + τ) - y₀ * η₀ + K * y) := this
      _ = (Real.exp (-(η₀ + τ)) * y) * (η₀ + τ) - (Real.exp (-(η₀ + τ)) * y₀) * η₀ +
            K * (Real.exp (-(η₀ + τ)) * y) := by ring
      _ = (η₀ + τ) - E * η₀ + K := by rw [hyE, hy₀E]; ring
  have hE1 : 1 - E ≤ τ := by have := Real.add_one_le_exp (-τ); linarith
  have hE0 : 0 < E := Real.exp_pos _
  have hE2 : E * τ ≤ 1 := by
    have h1 : τ + 1 ≤ Real.exp τ := Real.add_one_le_exp τ
    have h2 : E * Real.exp τ = 1 := by rw [hE, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
    nlinarith
  rw [← mul_le_mul_iff_of_pos_right hpos]
  have h6 : (τ + (K + 1) / η₀) * (η₀ + τ) = τ * (η₀ + τ) + (K + 1) + (K + 1) * τ / η₀ := by
    field_simp; ring
  rw [h6]
  have h3 : 0 ≤ (K + 1) * τ / η₀ := by positivity
  have h4 : (η₀ + τ) - E * η₀ = (1 - E) * (η₀ + τ) + E * τ := by ring
  have h5 : (1 - E) * (η₀ + τ) ≤ τ * (η₀ + τ) := mul_le_mul_of_nonneg_right hE1 hpos.le
  linarith

theorem measurable_abs_selbergV_comp_add (c : ℝ) : Measurable fun τ ↦ |selbergV (c + τ)| :=
  continuous_abs.measurable.comp (measurable_selbergV.comp (measurable_const_add c))

/-- **Theorem 436.** There is `C` such that, if `η₀ > 0` and `V(η₀) = 0`, then for `α ≥ 0`
`∫₀^α |V(η₀ + τ)| dτ ≤ α²/2 + C α/η₀`. -/
@[kb "hardywright2008" "Thm 436, p. 506"]
theorem integral_abs_selbergV_add_le :
    ∃ C ≥ 0, ∀ α η₀ : ℝ, 0 ≤ α → 0 < η₀ → selbergV η₀ = 0 →
      ∫ τ in (0 : ℝ)..α, |selbergV (η₀ + τ)| ≤ α ^ 2 / 2 + C * α / η₀ := by
  obtain ⟨C, hC0, hC⟩ := abs_selbergV_add_le
  refine ⟨C, hC0, fun α η₀ hα hη₀ hV ↦ ?_⟩
  calc ∫ τ in (0 : ℝ)..α, |selbergV (η₀ + τ)| ≤ ∫ τ in (0 : ℝ)..α, (τ + C / η₀) := by
        refine intervalIntegral.integral_mono_on hα
          (intervalIntegrable_of_bounded (measurable_abs_selbergV_comp_add η₀)
            fun t _ ↦ by rw [abs_abs]; exact abs_selbergV_le _)
          ((continuous_id.add continuous_const).intervalIntegrable 0 α) fun τ hτ ↦ ?_
        exact hC η₀ τ hη₀ hτ.1 hV
    _ = α ^ 2 / 2 + C * α / η₀ := by
        rw [intervalIntegral.integral_add (f := fun τ : ℝ ↦ τ) (g := fun _ ↦ C / η₀)
          (continuous_id.intervalIntegrable 0 α) intervalIntegrable_const,
          integral_id, intervalIntegral.integral_const, smul_eq_mul]
        ring

/-- `∫₀^ξ |V(η)| (ξ - η) dη = ∫₀^ξ ∫₀^ζ |V(η)| dη dζ` (integration by parts, using the right
continuity of `V`; Hardy–Wright change the order of integration). -/
theorem integral_abs_selbergV_mul_sub_eq (ξ : ℝ) :
    ∫ η in (0 : ℝ)..ξ, |selbergV η| * (ξ - η) =
      ∫ ζ in (0 : ℝ)..ξ, ∫ η in (0 : ℝ)..ζ, |selbergV η| := by
  set W : ℝ → ℝ := fun ζ ↦ ∫ η in (0 : ℝ)..ζ, |selbergV η| with hW
  have hWc : Continuous W :=
    intervalIntegral.continuous_primitive (fun a b ↦ intervalIntegrable_abs_selbergV a b) 0
  have hibp := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDeriv_right
    (u := W) (v := fun η ↦ ξ - η) (u' := fun η ↦ |selbergV η|) (v' := fun _ ↦ (-1 : ℝ))
    (a := 0) (b := ξ) hWc.continuousOn (continuous_const.sub continuous_id).continuousOn
    (fun x _ ↦ by
      refine (intervalIntegral.integral_hasDerivWithinAt_right
        (intervalIntegrable_abs_selbergV 0 x) (s := Ici x) (t := Ioi x) ?_ ?_).mono
          Ioi_subset_Ici_self
      · exact (continuous_abs.measurable.comp measurable_selbergV).stronglyMeasurable.stronglyMeasurableAtFilter
      · exact ((continuousWithinAt_selbergV x).abs).mono Ioi_subset_Ici_self)
    (fun x _ ↦ by
      have := (hasDerivAt_id x).const_sub ξ
      simpa using this.hasDerivWithinAt)
    (intervalIntegrable_abs_selbergV 0 ξ) intervalIntegrable_const
  have hint1 : IntervalIntegrable (fun η ↦ |selbergV η| * (ξ - η)) volume 0 ξ :=
    (intervalIntegrable_abs_selbergV 0 ξ).mul_continuousOn
      (continuous_const.sub continuous_id).continuousOn
  have hint2 : IntervalIntegrable (fun η ↦ W η * (-1)) volume 0 ξ :=
    (hWc.mul continuous_const).intervalIntegrable 0 ξ
  rw [intervalIntegral.integral_add hint1 hint2] at hibp
  simp only [hW, intervalIntegral.integral_same, sub_self, mul_zero, zero_mul, sub_zero,
    mul_neg, mul_one, intervalIntegral.integral_neg] at hibp
  linarith

/-- **(22.15.9)**: `ξ² |V(ξ)| ≤ 2 ∫₀^ξ |V(η)| (ξ - η) dη + O(1 + ξ)` for `ξ ≥ 0`. -/
@[kb "hardywright2008" "(22.15.9), p. 504"]
theorem sq_mul_abs_selbergV_le :
    ∃ K ≥ 0, ∀ ξ : ℝ, 0 ≤ ξ →
      ξ ^ 2 * |selbergV ξ| ≤
        2 * (∫ η in (0 : ℝ)..ξ, |selbergV η| * (ξ - η)) + K * (1 + ξ) := by
  obtain ⟨K, hK⟩ := abs_psiRem_mul_log_sq_le_integral
  refine ⟨max K 0, le_max_right _ _, fun ξ hξ ↦ ?_⟩
  have h := hK (Real.exp ξ) (Real.one_le_exp hξ)
  rw [Real.log_exp, integral_abs_psiRem_div_mul_log_eq hξ] at h
  have hK' : K * Real.exp ξ * (1 + ξ) ≤ max K 0 * Real.exp ξ * (1 + ξ) := by
    have : 0 ≤ Real.exp ξ * (1 + ξ) := by positivity
    nlinarith [le_max_left K 0]
  have h2 : |psiRem (Real.exp ξ)| * ξ ^ 2 ≤
      2 * (Real.exp ξ * ∫ η in (0 : ℝ)..ξ, |selbergV η| * (ξ - η)) +
        max K 0 * Real.exp ξ * (1 + ξ) := by linarith
  have h' := mul_le_mul_of_nonneg_left h2 (Real.exp_pos (-ξ)).le
  have he : Real.exp (-ξ) * Real.exp ξ = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [abs_selbergV_eq]
  calc ξ ^ 2 * (Real.exp (-ξ) * |psiRem (Real.exp ξ)|)
      = Real.exp (-ξ) * (|psiRem (Real.exp ξ)| * ξ ^ 2) := by ring
    _ ≤ Real.exp (-ξ) * (2 * (Real.exp ξ * (∫ η in (0 : ℝ)..ξ, |selbergV η| * (ξ - η))) +
          max K 0 * Real.exp ξ * (1 + ξ)) := h'
    _ = (Real.exp (-ξ) * Real.exp ξ) * (2 * (∫ η in (0 : ℝ)..ξ, |selbergV η| * (ξ - η))) +
          max K 0 * (Real.exp (-ξ) * Real.exp ξ) * (1 + ξ) := by ring
    _ = _ := by rw [he]; ring

/-- If `V` has no zero in `[p, q]` (`0 ≤ p ≤ q`), then `V` changes sign at most once there (from
negative to positive), so `∫_p^q |V| ≤ 2 A₁` by Theorem 435 (Hardy–Wright, § 22.16). -/
theorem integral_abs_selbergV_le_of_ne_zero {A₁ : ℝ}
    (hA : ∀ ξ₁ ξ₂ : ℝ, 0 ≤ ξ₁ → 0 ≤ ξ₂ → |∫ η in ξ₁..ξ₂, selbergV η| ≤ A₁)
    {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (hne : ∀ η ∈ Icc p q, selbergV η ≠ 0) :
    ∫ η in p..q, |selbergV η| ≤ 2 * A₁ := by
  have hA0 : 0 ≤ A₁ := (abs_nonneg _).trans (hA p p hp hp)
  set N := {t ∈ Icc p q | 0 < selbergV t} with hN
  by_cases hNe : N.Nonempty
  swap
  · -- `V < 0` on `[p, q]`
    have hneg : ∀ t ∈ uIcc p q, |selbergV t| = -selbergV t := by
      intro t ht
      rw [uIcc_of_le hpq] at ht
      have h1 : ¬ 0 < selbergV t := fun h ↦ hNe ⟨t, ht, h⟩
      exact abs_of_neg (lt_of_le_of_ne (not_lt.1 h1) (hne t ht))
    rw [intervalIntegral.integral_congr hneg, intervalIntegral.integral_neg]
    have := neg_le_abs (∫ η in p..q, selbergV η)
    have := hA p q hp (hp.trans hpq)
    linarith
  have hNbdd : BddBelow N := ⟨p, fun t ht ↦ ht.1.1⟩
  set s := sInf N with hs
  have hps : p ≤ s := le_csInf hNe fun t ht ↦ ht.1.1
  have hsq : s ≤ q := by
    obtain ⟨t, ht⟩ := hNe
    exact (csInf_le hNbdd ht).trans ht.1.2
  have hbefore : ∀ t, p ≤ t → t < s → selbergV t < 0 := by
    intro t hpt hts
    have ht : t ∈ Icc p q := ⟨hpt, hts.le.trans hsq⟩
    have h1 : ¬ 0 < selbergV t := fun h ↦ (not_le.2 hts) (csInf_le hNbdd ⟨ht, h⟩)
    exact lt_of_le_of_ne (not_lt.1 h1) (hne t ht)
  have hafter : ∀ t, s < t → t ≤ q → 0 < selbergV t := by
    intro t hst htq
    by_contra hcon
    have hVt : selbergV t < 0 :=
      lt_of_le_of_ne (not_lt.1 hcon) (hne t ⟨hps.trans hst.le, htq⟩)
    obtain ⟨t', ht'N, ht't⟩ := exists_lt_of_csInf_lt hNe hst
    obtain ⟨c, hc, hc0⟩ := exists_selbergV_eq_zero ht't.le ht'N.2.le hVt
    exact hne c ⟨ht'N.1.1.trans hc.1, hc.2.trans htq⟩ hc0
  rw [← intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_abs_selbergV p s)
    (intervalIntegrable_abs_selbergV s q)]
  have h1 : ∫ η in p..s, |selbergV η| = -∫ η in p..s, selbergV η := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr_ae ?_
    have hne' : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ s := by
      rw [ae_iff]; simp
    filter_upwards [hne'] with t hts ht
    rw [uIoc_of_le hps] at ht
    exact abs_of_neg (hbefore t ht.1.le (lt_of_le_of_ne ht.2 hts))
  have h2 : ∫ η in s..q, |selbergV η| = ∫ η in s..q, selbergV η := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht ↦ ?_)
    rw [uIoc_of_le hsq] at ht
    exact abs_of_pos (hafter t ht.1 ht.2)
  rw [h1, h2]
  have := neg_le_abs (∫ η in p..s, selbergV η)
  have := le_abs_self (∫ η in s..q, selbergV η)
  have := hA p s hp (hp.trans hps)
  have := hA s q (hp.trans hps) (hp.trans (hps.trans hsq))
  linarith

end NTKB.HardyWright
