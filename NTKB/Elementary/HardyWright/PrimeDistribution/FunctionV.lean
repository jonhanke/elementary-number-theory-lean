/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.PrimeDistribution.RemainderIntegral
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The function `V(ξ)` and Theorems 435, 436 (Hardy–Wright, Chapter XXII, §§ 22.6, 22.15, 22.16)

Hardy–Wright put (22.15.8) `V(ξ) = e^{-ξ} ψ(e^ξ) - 1 = e^{-ξ} R(e^ξ)` (`selbergV`). This file proves:

* (22.6.1) `∫₁ˣ ψ(t)/t² dt = log x + O(1)`, in the form `∫₁ˣ R(t)/t² dt = O(1)`;
* **Theorem 435**: `|∫_{ξ₁}^{ξ₂} V(η) dη| ≤ A₁` for all `ξ₁, ξ₂ ≥ 0`;
* **Theorem 436**: if `η₀ > 0` and `V(η₀) = 0`, then `|V(η₀ + τ)| ≤ τ + O(1/η₀)` for `τ ≥ 0`, hence
  `∫₀^α |V(η₀ + τ)| dτ ≤ α²/2 + O(1/η₀)`;
* (22.15.9) `ξ² |V(ξ)| ≤ 2 ∫₀^ξ ∫₀^ζ |V(η)| dη dζ + O(ξ)`, from (22.15.7) by the substitution
  `x = e^ξ`, `t = x e^{-η}` and an integration by parts (Hardy–Wright change the order of
  integration);
* the two properties of `V` used in § 22.16: `V` is bounded, and (since `V` decreases between the
  jumps of `ψ(e^η)` and jumps only upwards) a change of sign from positive to negative passes through
  a zero (`exists_selbergV_eq_zero`); so on an interval without zeros `∫ |V| ≤ 2 A₁`
  (`integral_abs_selbergV_le_of_ne_zero`).
-/

open Finset ArithmeticFunction Real Chebyshev MeasureTheory Filter Set
open scoped Topology

namespace NTKB.HardyWright

open NTKB.Apostol

/-- Hardy–Wright (22.15.8): `V(ξ) = e^{-ξ} ψ(e^ξ) - 1`. -/
noncomputable def selbergV (ξ : ℝ) : ℝ := Real.exp (-ξ) * ψ (Real.exp ξ) - 1

theorem selbergV_eq (ξ : ℝ) : selbergV ξ = Real.exp (-ξ) * psiRem (Real.exp ξ) := by
  rw [selbergV, psiRem, mul_sub, ← Real.exp_add, neg_add_cancel, Real.exp_zero]

theorem abs_selbergV_eq (ξ : ℝ) : |selbergV ξ| = Real.exp (-ξ) * |psiRem (Real.exp ξ)| := by
  rw [selbergV_eq, abs_mul, abs_of_pos (Real.exp_pos _)]

/-- `V` is bounded: `|V(ξ)| ≤ log 4 + 5`. -/
theorem abs_selbergV_le (ξ : ℝ) : |selbergV ξ| ≤ Real.log 4 + 5 := by
  rw [abs_selbergV_eq]
  have h := abs_psiRem_le (Real.exp_pos ξ).le
  calc Real.exp (-ξ) * |psiRem (Real.exp ξ)| ≤ Real.exp (-ξ) * ((Real.log 4 + 5) * Real.exp ξ) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = Real.log 4 + 5 := by
        rw [mul_comm, mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

theorem measurable_selbergV : Measurable selbergV :=
  ((Real.measurable_exp.comp measurable_neg).mul
    (measurable_psi.comp Real.measurable_exp)).sub_const 1

theorem intervalIntegrable_selbergV (a b : ℝ) : IntervalIntegrable selbergV volume a b :=
  intervalIntegrable_of_bounded measurable_selbergV fun t _ ↦ abs_selbergV_le t

theorem intervalIntegrable_abs_selbergV (a b : ℝ) :
    IntervalIntegrable (fun t ↦ |selbergV t|) volume a b :=
  intervalIntegrable_of_bounded (f := fun t ↦ |selbergV t|)
    (continuous_abs.measurable.comp measurable_selbergV) fun t _ ↦ by
    simp only [abs_abs]; exact abs_selbergV_le t

/-- `∫_a^b |V| ≤ (log 4 + 5)(b - a)`. -/
theorem integral_abs_selbergV_le {a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b, |selbergV t| ≤ (Real.log 4 + 5) * (b - a) := by
  calc ∫ t in a..b, |selbergV t| ≤ ∫ _ in a..b, (Real.log 4 + 5) :=
        intervalIntegral.integral_mono_on hab (intervalIntegrable_abs_selbergV a b)
          intervalIntegrable_const fun t _ ↦ abs_selbergV_le t
    _ = (Real.log 4 + 5) * (b - a) := by simp; ring

/-- `∫_a^b |V| ≤ B (b - a)` if `|V| ≤ B` on `[a, b]`. -/
theorem integral_abs_selbergV_le_of_le {a b B : ℝ} (hab : a ≤ b)
    (h : ∀ t ∈ Icc a b, |selbergV t| ≤ B) :
    ∫ t in a..b, |selbergV t| ≤ B * (b - a) := by
  calc ∫ t in a..b, |selbergV t| ≤ ∫ _ in a..b, B :=
        intervalIntegral.integral_mono_on hab (intervalIntegrable_abs_selbergV a b)
          intervalIntegrable_const h
    _ = B * (b - a) := by simp; ring

/-! ### Right continuity of `ψ` and of `V` -/

/-- `ψ` is constant on `[t, ⌊t⌋ + 1)`. -/
theorem psi_eventually_eq_nhdsGE {t : ℝ} (ht : 0 ≤ t) : ∀ᶠ s in 𝓝[≥] t, ψ s = ψ t := by
  filter_upwards [Ico_mem_nhdsGE (Nat.lt_floor_add_one t)] with s hs
  rw [psi_eq_psi_coe_floor s, psi_eq_psi_coe_floor t]
  congr 2
  exact (Nat.floor_eq_iff (ht.trans hs.1)).2
    ⟨(Nat.floor_le ht).trans hs.1, hs.2⟩

theorem continuousWithinAt_selbergV (ξ : ℝ) : ContinuousWithinAt selbergV (Ici ξ) ξ := by
  have hexp : Tendsto Real.exp (𝓝[≥] ξ) (𝓝[≥] (Real.exp ξ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (Real.continuous_exp.continuousWithinAt.tendsto)
      (eventually_nhdsWithin_of_forall fun s hs ↦ Real.exp_le_exp.2 hs)
  have hψ : ∀ᶠ s in 𝓝[≥] ξ, ψ (Real.exp s) = ψ (Real.exp ξ) :=
    hexp.eventually (psi_eventually_eq_nhdsGE (Real.exp_pos ξ).le)
  have hcont : ContinuousWithinAt (fun s ↦ Real.exp (-s) * ψ (Real.exp ξ) - 1) (Ici ξ) ξ :=
    ((Real.continuous_exp.comp continuous_neg).mul continuous_const |>.sub
      continuous_const).continuousWithinAt
  refine hcont.congr_of_eventuallyEq ?_ (by simp [selbergV])
  filter_upwards [hψ] with s hs
  simp [selbergV, hs]

/-! ### Zeros of `V` -/

/-- Since `ψ` is increasing, `V` can only become negative continuously: if `V(a) ≥ 0 > V(b)` with
`a ≤ b`, then `V` vanishes in `[a, b]` (Hardy–Wright, § 22.16). -/
theorem exists_selbergV_eq_zero {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ selbergV a)
    (hb : selbergV b < 0) : ∃ c ∈ Icc a b, selbergV c = 0 := by
  set S := {t ∈ Icc a b | 0 ≤ selbergV t} with hS
  have hSne : S.Nonempty := ⟨a, ⟨le_rfl, hab⟩, ha⟩
  have hSbdd : BddAbove S := ⟨b, fun t ht ↦ ht.1.2⟩
  set c := sSup S with hc
  have hac : a ≤ c := le_csSup hSbdd ⟨⟨le_rfl, hab⟩, ha⟩
  have hcb : c ≤ b := csSup_le hSne fun t ht ↦ ht.1.2
  refine ⟨c, ⟨hac, hcb⟩, le_antisymm ?_ ?_⟩
  · -- `V(c) ≤ 0`, by right continuity
    by_contra hpos
    replace hpos := not_le.1 hpos
    rcases eq_or_lt_of_le hcb with hcb' | hcb'
    · rw [hcb'] at hpos; linarith
    have hev : ∀ᶠ s in 𝓝[≥] c, 0 < selbergV s :=
      (continuousWithinAt_selbergV c).eventually (lt_mem_nhds hpos)
    obtain ⟨u, hu, hsub⟩ := (mem_nhdsGE_iff_exists_Ico_subset.1 hev)
    have hu' : c < u := hu
    set t := min ((c + u) / 2) b
    have hct : c < t := lt_min (by linarith) hcb'
    have htu : t < u := (min_le_left _ _).trans_lt (by linarith)
    have hVt : 0 < selbergV t := hsub ⟨hct.le, htu⟩
    have : t ∈ S := ⟨⟨hac.trans hct.le, min_le_right _ _⟩, hVt.le⟩
    have := le_csSup hSbdd this
    linarith
  · -- `V(c) ≥ 0`: `e^{-t} ψ(e^t) ≥ 1` for `t ∈ S` near `c` and `ψ(e^t) ≤ ψ(e^c)`
    set u := Real.exp (-c) * ψ (Real.exp c) with hu
    have hu0 : 0 ≤ u := mul_nonneg (Real.exp_pos _).le (psi_nonneg _)
    have key : ∀ t ∈ S, 1 ≤ Real.exp (c - t) * u := by
      intro t ht
      have htc : t ≤ c := le_csSup hSbdd ht
      have h1 : 1 ≤ Real.exp (-t) * ψ (Real.exp t) := by have := ht.2; unfold selbergV at this; linarith
      have h2 : ψ (Real.exp t) ≤ ψ (Real.exp c) := psi_mono (Real.exp_le_exp.2 htc)
      calc 1 ≤ Real.exp (-t) * ψ (Real.exp t) := h1
        _ ≤ Real.exp (-t) * ψ (Real.exp c) := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
        _ = Real.exp (c - t) * u := by
            rw [hu, ← mul_assoc, ← Real.exp_add]; ring_nf
    show 0 ≤ u - 1
    by_contra hlt
    replace hlt := not_le.1 hlt
    set δ := 1 - u with hδ
    have hδ0 : 0 < δ := by linarith
    set ε := min 1 (δ / 4) with hε
    have hε0 : 0 < ε := lt_min one_pos (by linarith)
    have hε1 : ε ≤ 1 := min_le_left _ _
    have hεδ : ε ≤ δ / 4 := min_le_right _ _
    obtain ⟨t, htS, hct⟩ := exists_lt_of_lt_csSup hSne (show c - ε < c by linarith)
    have htc : t ≤ c := le_csSup hSbdd htS
    have h1 := key t htS
    have hexp : Real.exp (c - t) ≤ 1 + 2 * ε := by
      have habs : |c - t| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      have := Real.abs_exp_sub_one_le habs
      have h3 : |c - t| ≤ ε := by rw [abs_le]; constructor <;> linarith
      rw [abs_le] at this
      linarith
    have : Real.exp (c - t) * u ≤ (1 + 2 * ε) * u := mul_le_mul_of_nonneg_right hexp hu0
    nlinarith

/-! ### Change of variables -/

/-- The substitution `t = e^η`: `∫_a^b V(η) dη = ∫_{e^a}^{e^b} R(t)/t² dt`. -/
theorem integral_selbergV_eq {a b : ℝ} (hab : a ≤ b) :
    ∫ η in a..b, selbergV η = ∫ t in Real.exp a..Real.exp b, psiRem t / t ^ 2 := by
  rw [intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le (Real.exp_le_exp.2 hab)]
  have himage : Real.exp '' Ioc a b = Ioc (Real.exp a) (Real.exp b) := by
    ext t
    constructor
    · rintro ⟨η, hη, rfl⟩
      exact ⟨Real.exp_lt_exp.2 hη.1, Real.exp_le_exp.2 hη.2⟩
    · intro ht
      have ht0 : 0 < t := (Real.exp_pos a).trans ht.1
      refine ⟨Real.log t, ⟨?_, ?_⟩, Real.exp_log ht0⟩
      · rw [Real.lt_log_iff_exp_lt ht0]; exact ht.1
      · rw [Real.log_le_iff_le_exp ht0]; exact ht.2
  rw [← himage, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc
    (fun η _ ↦ (Real.hasDerivAt_exp η).hasDerivWithinAt) Real.exp_injective.injOn]
  refine setIntegral_congr_fun measurableSet_Ioc fun η _ ↦ ?_
  simp only [smul_eq_mul, abs_of_pos (Real.exp_pos η), selbergV_eq]
  rw [Real.exp_neg]
  field_simp

/-- The substitution `x = e^ξ`, `t = x e^{-η}`:
`∫₁ˣ |R(x/t)| log t dt = x ∫₀^ξ |V(η)| (ξ - η) dη`. -/
theorem integral_abs_psiRem_div_mul_log_eq {ξ : ℝ} (hξ : 0 ≤ ξ) :
    ∫ t in (1 : ℝ)..Real.exp ξ, |psiRem (Real.exp ξ / t)| * Real.log t =
      Real.exp ξ * ∫ η in (0 : ℝ)..ξ, |selbergV η| * (ξ - η) := by
  rw [intervalIntegral.integral_of_le (Real.one_le_exp hξ), intervalIntegral.integral_of_le hξ,
    ← integral_Ico_eq_integral_Ioc (x := (0 : ℝ)) (y := ξ)]
  set φ : ℝ → ℝ := fun η ↦ Real.exp (ξ - η) with hφ
  have himage : φ '' Ico 0 ξ = Ioc 1 (Real.exp ξ) := by
    ext t
    constructor
    · rintro ⟨η, hη, rfl⟩
      exact ⟨Real.one_lt_exp_iff.2 (by linarith [hη.2]), Real.exp_le_exp.2 (by linarith [hη.1])⟩
    · intro ht
      have ht0 : 0 < t := lt_trans one_pos ht.1
      refine ⟨ξ - Real.log t, ⟨?_, ?_⟩, ?_⟩
      · have : Real.log t ≤ ξ := (Real.log_le_iff_le_exp ht0).2 ht.2
        linarith
      · have : 0 < Real.log t := Real.log_pos ht.1
        linarith
      · simp only [hφ, sub_sub_cancel, Real.exp_log ht0]
  have hderiv : ∀ η ∈ Ico (0 : ℝ) ξ, HasDerivWithinAt φ (-Real.exp (ξ - η)) (Ico 0 ξ) η := by
    intro η _
    have := ((hasDerivAt_id η).const_sub ξ).exp
    simp only [id, mul_neg, mul_one] at this
    exact this.hasDerivWithinAt
  have hinj : InjOn φ (Ico 0 ξ) := by
    intro u _ v _ h
    have := Real.exp_injective h
    linarith
  rw [← himage, integral_image_eq_integral_abs_deriv_smul measurableSet_Ico hderiv hinj,
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ico fun η _ ↦ ?_
  simp only [hφ, smul_eq_mul, abs_neg, abs_of_pos (Real.exp_pos _), abs_selbergV_eq,
    Real.log_exp]
  rw [show Real.exp ξ / Real.exp (ξ - η) = Real.exp η by rw [← Real.exp_sub]; ring_nf,
    Real.exp_sub, Real.exp_neg]
  field_simp

/-! ### (22.6.1) and Theorem 435 -/

/-- `∫₁ˣ ψ(t)/t² dt = ∑_{n ≤ x} Λ(n) (1/n - 1/x)` for `x ≥ 1`. -/
theorem integral_psi_div_sq {x : ℝ} (hx : 1 ≤ x) :
    ∫ t in (1 : ℝ)..x, ψ t / t ^ 2 = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * (1 / n - 1 / x) := by
  have hx0 : 0 < x := by linarith
  set g : ℕ → ℝ → ℝ := fun n t ↦ if (n : ℝ) ≤ t then Λ n / t ^ 2 else 0 with hg
  have h1 : ∀ t ∈ uIcc 1 x, ψ t / t ^ 2 = ∑ n ∈ Ioc 0 ⌊x⌋₊, g n t := by
    intro t ht
    rw [uIcc_of_le hx] at ht
    have ht0 : 0 ≤ t := by linarith [ht.1]
    simp only [hg]
    rw [← sum_filter, Chebyshev.psi, sum_div]
    congr 1
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_filter]
    constructor
    · rintro ⟨h0, hn⟩
      have hnt : (n : ℝ) ≤ t := (Nat.le_floor_iff ht0).1 hn
      exact ⟨⟨h0, Nat.floor_mono ht.2 |>.trans' hn⟩, hnt⟩
    · rintro ⟨⟨h0, _⟩, hnt⟩
      exact ⟨h0, Nat.le_floor hnt⟩
  have hgint : ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊, ∀ a b : ℝ, 1 ≤ a → 1 ≤ b →
      IntervalIntegrable (g n) volume a b := by
    intro n _ a b ha hb
    refine intervalIntegrable_of_bounded (M := Λ n) ?_ fun t ht ↦ ?_
    · exact Measurable.ite measurableSet_Ici (measurable_const.div (measurable_id.pow_const 2))
        measurable_const
    · have ht1 : 1 ≤ t := by
        rcases mem_uIcc.1 ht with h | h
        · exact ha.trans h.1
        · exact hb.trans h.1
      simp only [hg]
      split_ifs
      · rw [abs_div, abs_of_nonneg vonMangoldt_nonneg, abs_of_nonneg (by positivity)]
        exact div_le_self vonMangoldt_nonneg (one_le_pow₀ ht1)
      · simp [vonMangoldt_nonneg]
  rw [intervalIntegral.integral_congr h1,
    intervalIntegral.integral_finsetSum fun n hn ↦ hgint n hn 1 x le_rfl hx]
  refine sum_congr rfl fun n hn ↦ ?_
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ioc.1 hn).1
  have hnx : (n : ℝ) ≤ x :=
    (show (n : ℝ) ≤ ⌊x⌋₊ by exact_mod_cast (Finset.mem_Ioc.1 hn).2).trans (Nat.floor_le hx0.le)
  rw [← intervalIntegral.integral_add_adjacent_intervals (hgint n hn 1 n le_rfl hn1)
    (hgint n hn n x hn1 hx)]
  have hA : ∫ t in (1 : ℝ)..n, g n t = 0 := by
    rw [← intervalIntegral.integral_zero (a := (1 : ℝ)) (b := n)]
    refine intervalIntegral.integral_congr_ae ?_
    have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ (n : ℝ) := by
      rw [ae_iff]; simp
    filter_upwards [hne] with t htn ht
    rw [uIoc_of_le hn1] at ht
    have : t < n := lt_of_le_of_ne ht.2 htn
    simp [hg, not_le.2 this]
  have hB : ∫ t in (n : ℝ)..x, g n t = ∫ t in (n : ℝ)..x, Λ n / t ^ 2 := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [uIcc_of_le hnx] at ht
    simp [hg, ht.1]
  rw [hA, hB, zero_add]
  have hderiv : ∀ t ∈ uIcc (n : ℝ) x, HasDerivAt (fun t ↦ -(Λ n / t)) (Λ n / t ^ 2) t := by
    intro t ht
    rw [uIcc_of_le hnx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have := ((hasDerivAt_id t).inv ht0).const_mul (Λ n)
    convert this.neg using 1
    · ext s; simp [div_eq_mul_inv]
    · simp only [id]; field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv]
  · ring
  · refine (ContinuousOn.div continuousOn_const (continuousOn_id.pow 2) fun t ht ↦ ?_).intervalIntegrable
    rw [uIcc_of_le hnx] at ht
    have : 0 < t := by linarith [ht.1]
    exact pow_ne_zero 2 this.ne'

/-- **(22.6.1)**: `∫₁ˣ ψ(t)/t² dt = log x + O(1)`, i.e. `∫₁ˣ R(t)/t² dt = O(1)` for `x ≥ 1`. -/
@[kb "hardywright2008" "(22.6.1), p. 482"]
theorem abs_integral_psiRem_div_sq_le :
    ∃ A, ∀ x : ℝ, 1 ≤ x → |∫ t in (1 : ℝ)..x, psiRem t / t ^ 2| ≤ A := by
  obtain ⟨⟨M, hM⟩, -, -⟩ := apostol_thm_4_9
  refine ⟨|M| + (Real.log 4 + 4), fun x hx ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  have hsplit : ∀ t ∈ uIcc 1 x, psiRem t / t ^ 2 = ψ t / t ^ 2 - 1 / t := by
    intro t ht
    rw [uIcc_of_le hx] at ht
    have : t ≠ 0 := by linarith [ht.1]
    rw [psiRem]; field_simp
  have hint1 : IntervalIntegrable (fun t ↦ ψ t / t ^ 2) volume 1 x :=
    intervalIntegrable_of_bounded (f := fun t ↦ ψ t / t ^ 2) (M := (Real.log 4 + 4))
      (measurable_psi.div (measurable_id.pow_const 2)) fun t ht ↦ by
        rw [uIcc_of_le hx] at ht
        have ht1 : 1 ≤ t := ht.1
        have ht0 : 0 < t := by linarith
        rw [abs_div, abs_of_nonneg (psi_nonneg t), abs_of_nonneg (by positivity),
          div_le_iff₀ (by positivity)]
        have := psi_le_c t ht0.le
        have h4 : 0 ≤ Real.log 4 + 4 := log_four_add_four_pos.le
        have h5 : t ≤ t ^ 2 := by nlinarith
        have h6 := mul_le_mul_of_nonneg_left h5 h4
        linarith
  have hint2 : IntervalIntegrable (fun t : ℝ ↦ 1 / t) volume 1 x :=
    (ContinuousOn.div continuousOn_const continuousOn_id fun t ht ↦ by
      rw [uIcc_of_le hx] at ht; simp only [id]; linarith [ht.1]).intervalIntegrable
  rw [intervalIntegral.integral_congr hsplit, intervalIntegral.integral_sub hint1 hint2,
    integral_psi_div_sq hx, integral_one_div_of_pos one_pos hx0, div_one]
  have hsum : ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * (1 / n - 1 / x) =
      ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n - ψ x / x := by
    rw [Chebyshev.psi, sum_div, ← sum_sub_distrib]
    exact sum_congr rfl fun n _ ↦ by ring
  rw [hsum]
  have h1 := hM x hx
  have h2 : ψ x / x ≤ Real.log 4 + 4 := by
    rw [div_le_iff₀ hx0]; exact psi_le_c x hx0.le
  have h3 : 0 ≤ ψ x / x := div_nonneg (psi_nonneg x) hx0.le
  rw [abs_le] at h1 ⊢
  have := le_abs_self M
  have := neg_abs_le M
  constructor <;> linarith

/-- **Theorem 435.** There is a fixed `A₁` such that `|∫_{ξ₁}^{ξ₂} V(η) dη| ≤ A₁` for all
`ξ₁, ξ₂ ≥ 0`. -/
@[kb "hardywright2008" "Thm 435, p. 505"]
theorem abs_integral_selbergV_le :
    ∃ A₁ > 0, ∀ ξ₁ ξ₂ : ℝ, 0 ≤ ξ₁ → 0 ≤ ξ₂ → |∫ η in ξ₁..ξ₂, selbergV η| ≤ A₁ := by
  obtain ⟨A, hA⟩ := abs_integral_psiRem_div_sq_le
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 1 le_rfl)
  have h0 : ∀ ξ : ℝ, 0 ≤ ξ → |∫ η in (0 : ℝ)..ξ, selbergV η| ≤ A := by
    intro ξ hξ
    rw [integral_selbergV_eq hξ, Real.exp_zero]
    exact hA _ (Real.one_le_exp hξ)
  refine ⟨2 * A + 1, by linarith, fun ξ₁ ξ₂ h₁ h₂ ↦ ?_⟩
  rw [← intervalIntegral.integral_interval_sub_left (intervalIntegrable_selbergV 0 ξ₂)
    (intervalIntegrable_selbergV 0 ξ₁)]
  have := h0 ξ₁ h₁
  have := h0 ξ₂ h₂
  calc _ ≤ |∫ η in (0 : ℝ)..ξ₂, selbergV η| + |∫ η in (0 : ℝ)..ξ₁, selbergV η| := abs_sub _ _
    _ ≤ 2 * A + 1 := by linarith

end NTKB.HardyWright
