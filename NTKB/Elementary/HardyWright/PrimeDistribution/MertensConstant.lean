/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.PrimeDistribution.Mertens
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

open Finset MeasureTheory Filter
open scoped Topology

local notation "γ" => Real.eulerMascheroniConstant

namespace NTKB.HardyWright

/-- The coefficients `1/p` (for `p` prime), `0` otherwise. -/
private noncomputable def primeInv (k : ℕ) : ℝ := if k.Prime then 1 / (k : ℝ) else 0

/-- `∑_{p ≤ t} 1/p`, as a sum of `primeInv`. -/
private noncomputable def primeInvSum (t : ℝ) : ℝ := ∑ k ∈ Icc 0 ⌊t⌋₊, primeInv k

private lemma primeInv_nonneg (k : ℕ) : 0 ≤ primeInv k := by
  unfold primeInv; split_ifs <;> positivity

private lemma primeInvSum_eq (t : ℝ) :
    primeInvSum t = ∑ p ∈ Ioc 0 ⌊t⌋₊ with p.Prime, (1 : ℝ) / p := by
  unfold primeInvSum
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons, Finset.sum_filter]
  simp [primeInv]

private lemma primeInvSum_nonneg (t : ℝ) : 0 ≤ primeInvSum t :=
  Finset.sum_nonneg fun k _ ↦ primeInv_nonneg k

private lemma primeInvSum_le {t : ℝ} (ht : 1 ≤ t) : primeInvSum t ≤ 1 + Real.log t := by
  have h1 : primeInvSum t ≤ ((harmonic ⌊t⌋₊ : ℚ) : ℝ) := by
    rw [primeInvSum_eq, harmonic_eq_sum_Icc]
    push_cast
    rw [Finset.sum_filter]
    have : Ioc 0 ⌊t⌋₊ = Icc 1 ⌊t⌋₊ := rfl
    rw [this]
    refine Finset.sum_le_sum fun k hk ↦ ?_
    split_ifs <;> simp
  refine h1.trans ((harmonic_le_one_add_log _).trans ?_)
  have h0 : (0 : ℝ) < ⌊t⌋₊ := by exact_mod_cast Nat.floor_pos.mpr ht
  have := Real.log_le_log h0 (Nat.floor_le (by linarith : (0:ℝ) ≤ t))
  linarith

private lemma isBigO_primeInvSum {a ε : ℝ} (hε : 0 < ε) :
    (fun t : ℝ ↦ t ^ (-a) * primeInvSum t) =O[atTop] fun t : ℝ ↦ t ^ (-a + ε) := by
  refine Asymptotics.IsBigO.of_bound (1 + 1 / ε) ?_
  filter_upwards [eventually_ge_atTop 1] with t ht
  have ht0 : 0 < t := by linarith
  have h1 : 1 ≤ t ^ ε := Real.one_le_rpow ht hε.le
  have h2 : Real.log t ≤ t ^ ε / ε := Real.log_le_rpow_div ht0.le hε
  have hP := primeInvSum_le ht
  have hP0 := primeInvSum_nonneg t
  have e : t ^ (-a) * t ^ ε = t ^ (-a + ε) := by rw [← Real.rpow_add ht0]
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  calc t ^ (-a) * primeInvSum t ≤ t ^ (-a) * ((1 + 1 / ε) * t ^ ε) := by
        gcongr
        calc primeInvSum t ≤ 1 + Real.log t := hP
          _ ≤ 1 * t ^ ε + t ^ ε / ε := by linarith
          _ = _ := by ring
    _ = _ := by rw [← e]; ring

private lemma integrableOn_primeInvSum {s : ℝ} (hs : 1 < s) :
    IntegrableOn (fun t : ℝ ↦ t ^ (-s) * primeInvSum t) (Set.Ioi 1) := by
  have hcont : ContinuousOn (fun t : ℝ ↦ t ^ (-s)) (Set.Ici 1) :=
    ContinuousOn.rpow_const continuousOn_id fun x hx ↦ Or.inl (by
      have : (1 : ℝ) ≤ x := hx
      linarith)
  have hloc : LocallyIntegrableOn
      (fun t : ℝ ↦ t ^ (-s) * ∑ k ∈ Icc 0 ⌊t⌋₊, primeInv k) (Set.Ici 1) :=
    locallyIntegrableOn_mul_sum_Icc primeInv zero_le_one
      (hcont.locallyIntegrableOn measurableSet_Ici)
  have hε : 0 < (s - 1) / 2 := by linarith
  have := hloc.integrableOn_of_isBigO_atTop (isBigO_primeInvSum (a := s) hε)
    ⟨Set.Ioi 1, Ioi_mem_atTop 1, integrableOn_Ioi_rpow_of_lt
      (by linarith) one_pos⟩
  exact Iff.mp integrableOn_Ici_iff_integrableOn_Ioi this

private lemma term_eq {s : ℝ} (n : ℕ) :
    (n : ℝ) ^ (-(s - 1)) * primeInv n = if n.Prime then (n : ℝ) ^ (-s) else 0 := by
  unfold primeInv
  split_ifs with h
  · have hn : (0 : ℝ) < n := by exact_mod_cast h.pos
    rw [show -s = -(s - 1) + (-1) by ring, Real.rpow_add hn, Real.rpow_neg_one]; ring
  · simp

private lemma summable_nat_rpow_neg {s : ℝ} (hs : 1 < s) :
    Summable fun n : ℕ ↦ (n : ℝ) ^ (-s) := Real.summable_nat_rpow.2 (by linarith)

private lemma summable_primes_rpow {s : ℝ} (hs : 1 < s) :
    Summable fun p : Nat.Primes ↦ ((p : ℕ) : ℝ) ^ (-s) :=
  (summable_nat_rpow_neg hs).comp_injective Subtype.coe_injective

/-- Abel summation: `∑_p p^(-s) = (s - 1) ∫_1^∞ t^(-s) (∑_{p ≤ t} 1/p) dt`. -/
private lemma primeRpow_tsum_eq {s : ℝ} (hs : 1 < s) :
    ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-s) =
      (s - 1) * ∫ t in Set.Ioi 1, t ^ (-s) * primeInvSum t := by
  let f : ℝ → ℝ := fun t ↦ t ^ (-(s - 1))
  have hpos : ∀ t ∈ Set.Ici (1 : ℝ), 0 < t := fun t ht ↦ lt_of_lt_of_le one_pos ht
  have hderiv : ∀ t ∈ Set.Ici (1 : ℝ), deriv f t = -(s - 1) * t ^ (-s) := by
    intro t _
    simp only [f]
    rw [Real.deriv_rpow_const, show -(s - 1) - 1 = -s by ring]
  have hdiff : ∀ t ∈ Set.Ici (1 : ℝ), DifferentiableAt ℝ f t := fun t ht ↦
    DifferentiableAt.rpow_const differentiableAt_id (Or.inl (hpos t ht).ne')
  have hcont : ContinuousOn (fun t : ℝ ↦ -(s - 1) * t ^ (-s)) (Set.Ici 1) :=
    continuousOn_const.mul
      (ContinuousOn.rpow_const continuousOn_id fun x hx ↦ Or.inl (hpos x hx).ne')
  have hf_int : LocallyIntegrableOn (deriv f) (Set.Ici 1) :=
    (hcont.congr hderiv).locallyIntegrableOn measurableSet_Ici
  have hε : 0 < (s - 1) / 2 := by linarith
  have h_lim : Tendsto (fun n : ℕ ↦ f n * ∑ k ∈ Icc 0 n, primeInv k) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ ↦ t ^ (-(s - 1) + (s - 1) / 2)) atTop (𝓝 0) := by
      rw [show -(s - 1) + (s - 1) / 2 = -((s - 1) / 2) by ring]
      exact tendsto_rpow_neg_atTop hε
    have h2 := (isBigO_primeInvSum (a := s - 1) hε).trans_tendsto h1
    refine (h2.comp tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
    simp [primeInvSum, f]
  have hg_dom : (fun t : ℝ ↦ deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, primeInv k) =O[atTop]
      fun t : ℝ ↦ t ^ (-s + (s - 1) / 2) := by
    refine ((isBigO_primeInvSum (a := s) hε).const_mul_left (-(s - 1))).congr' ?_
      Filter.EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop 1] with t ht
    rw [hderiv t ht]; simp only [primeInvSum]; ring
  have hg_int : IntegrableAtFilter (fun t : ℝ ↦ t ^ (-s + (s - 1) / 2)) atTop :=
    ⟨Set.Ioi 1, Ioi_mem_atTop 1, integrableOn_Ioi_rpow_of_lt (by linarith) one_pos⟩
  have hA := tendsto_sum_mul_atTop_nhds_one_sub_integral₀ primeInv
    (by simp [primeInv]) hdiff hf_int h_lim hg_dom hg_int
  have hsum : Summable fun n : ℕ ↦ f n * primeInv n := by
    refine (summable_nat_rpow_neg hs).of_nonneg_of_le (fun n ↦ ?_) (fun n ↦ ?_)
    · exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (primeInv_nonneg n)
    · show (n : ℝ) ^ (-(s - 1)) * primeInv n ≤ _
      rw [term_eq]
      split_ifs
      · exact le_rfl
      · exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hT : Tendsto (fun n : ℕ ↦ ∑ k ∈ Icc 0 n, f k * primeInv k) atTop
      (𝓝 (∑' n : ℕ, f n * primeInv n)) := by
    have := (hsum.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
    refine this.congr fun n ↦ ?_
    have : range (n + 1) = Icc 0 n := by ext k; simp
    simp only [Function.comp, this]
  have hEq := tendsto_nhds_unique hT hA
  have h1 : ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-s) = ∑' n : ℕ, f n * primeInv n := by
    have : (fun n : ℕ ↦ f n * primeInv n) =
        Set.indicator {p : ℕ | p.Prime} (fun n : ℕ ↦ (n : ℝ) ^ (-s)) := by
      funext n
      show (n : ℝ) ^ (-(s - 1)) * primeInv n = _
      rw [term_eq, Set.indicator_apply]
      simp
    rw [this, ← tsum_subtype {p : ℕ | p.Prime} (fun n : ℕ ↦ (n : ℝ) ^ (-s))]
    rfl
  have hint : ∫ t in Set.Ioi 1, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, primeInv k =
      -(s - 1) * ∫ t in Set.Ioi 1, t ^ (-s) * primeInvSum t := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    simp only [primeInvSum]
    rw [hderiv t (Set.mem_Ici.2 (le_of_lt ht))]
    ring
  rw [h1, hEq, hint]
  ring

private lemma integrableOn_H (B : ℝ) {s : ℝ} (hs : 1 < s) :
    IntegrableOn
      (fun t : ℝ ↦ (primeInvSum t - Real.log (Real.log t) - B) * t ^ (-s)) (Set.Ioi 1) := by
  have h1 := integrableOn_primeInvSum hs
  have h2 := Real.integrableOn_log_log_mul_rpow hs
  have h3 : IntegrableOn (fun t : ℝ ↦ B * t ^ (-s)) (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul B
  refine ((h1.sub h2).sub h3).congr_fun (fun t _ ↦ ?_) measurableSet_Ioi
  simp only [Pi.sub_apply]; ring

private lemma norm_tail_le {H : ℝ → ℝ} {s T ε : ℝ} (hs : 1 < s) (hT : 1 ≤ T)
    (hH : ∀ t ≥ T, |H t| ≤ ε) :
    ‖∫ t in Set.Ioi T, H t * t ^ (-s)‖ ≤ ε * (T ^ (-(s - 1)) / (s - 1)) := by
  have hTp : 0 < T := by linarith
  have hg : IntegrableOn (fun t : ℝ ↦ ε * t ^ (-s)) (Set.Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hTp).const_mul ε
  calc ‖∫ t in Set.Ioi T, H t * t ^ (-s)‖ ≤ ∫ t in Set.Ioi T, ε * t ^ (-s) := by
        refine norm_integral_le_of_norm_le hg ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht' : T < t := ht
        have ht0 : 0 < t := by linarith
        rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _)]
        gcongr
        exact hH t ht'.le
    _ = ε * (T ^ (-(s - 1)) / (s - 1)) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hTp,
          show -s + 1 = -(s - 1) by ring, neg_div_neg_eq]

private lemma weighted_small {H : ℝ → ℝ} (hH : Tendsto H atTop (𝓝 0))
    (hint : ∀ s : ℝ, 1 < s → IntegrableOn (fun t ↦ H t * t ^ (-s)) (Set.Ioi 1)) :
    Tendsto (fun s : ℝ ↦ (s - 1) * ∫ t in Set.Ioi 1, H t * t ^ (-s)) (𝓝[>] 1) (𝓝 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := Metric.tendsto_atTop.1 hH (ε / 2) (by positivity)
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = max T₀ 2 := ⟨_, rfl⟩
  have hT2 : 2 ≤ T := hT ▸ le_max_right _ _
  have hT0 : T₀ ≤ T := hT ▸ le_max_left _ _
  have hHT : ∀ t ≥ T, |H t| ≤ ε / 2 := fun t ht ↦ by
    have := hT₀ t (hT0.trans ht)
    rw [Real.dist_eq, sub_zero] at this
    exact this.le
  have hTp : 0 < T := by linarith
  have hg0 : IntegrableOn (fun t : ℝ ↦ T ^ 2 * ‖H t * t ^ (-(2 : ℝ))‖) (Set.Ioi 1) :=
    Integrable.const_mul (Integrable.norm (hint 2 one_lt_two)) (T ^ 2)
  have hg : IntegrableOn (fun t : ℝ ↦ T ^ 2 * ‖H t * t ^ (-(2 : ℝ))‖) (Set.Ioc 1 T) :=
    hg0.mono_set Set.Ioc_subset_Ioi_self
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ∫ t in Set.Ioc 1 T, T ^ 2 * ‖H t * t ^ (-(2 : ℝ))‖ := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := hM ▸ setIntegral_nonneg measurableSet_Ioc fun t _ ↦ by positivity
  refine ⟨ε / (2 * (M + 1)), by positivity, fun s hs hdist ↦ ?_⟩
  have hs1 : 1 < s := hs
  have hsd : s - 1 < ε / (2 * (M + 1)) := by
    rw [Real.dist_eq, abs_of_pos (by linarith)] at hdist; exact hdist
  rw [Real.dist_eq, sub_zero]
  have hsplit : ∫ t in Set.Ioi 1, H t * t ^ (-s) =
      (∫ t in Set.Ioc 1 T, H t * t ^ (-s)) + ∫ t in Set.Ioi T, H t * t ^ (-s) := by
    rw [← setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi,
      Set.Ioc_union_Ioi_eq_Ioi (by linarith)]
    · exact (hint s hs1).mono_set Set.Ioc_subset_Ioi_self
    · exact (hint s hs1).mono_set (Set.Ioi_subset_Ioi (by linarith))
  have h1 : ‖∫ t in Set.Ioc 1 T, H t * t ^ (-s)‖ ≤ M := by
    rw [hM]
    refine norm_integral_le_of_norm_le hg ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht1 : 1 < t := ht.1
    have htT : t ≤ T := ht.2
    have ht0 : 0 < t := by linarith
    have e1 : t ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht1.le (by linarith)
    have e2 : 1 ≤ T ^ 2 * t ^ (-(2 : ℝ)) := by
      rw [Real.rpow_neg ht0.le, Real.rpow_two, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      · nlinarith
    have e3 : 0 ≤ t ^ (-s) := Real.rpow_nonneg ht0.le _
    have e4 : 0 ≤ t ^ (-(2 : ℝ)) := Real.rpow_nonneg ht0.le _
    rw [norm_mul, norm_mul, Real.norm_of_nonneg e3, Real.norm_of_nonneg e4]
    calc ‖H t‖ * t ^ (-s) ≤ ‖H t‖ * 1 := by gcongr
      _ ≤ ‖H t‖ * (T ^ 2 * t ^ (-(2 : ℝ))) := by gcongr
      _ = _ := by ring
  have h2 := norm_tail_le (H := H) hs1 (by linarith : 1 ≤ T) hHT
  have h3 : T ^ (-(s - 1)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hsp : 0 < s - 1 := by linarith
  have h4 : ε / 2 * (T ^ (-(s - 1)) / (s - 1)) ≤ ε / 2 * (1 / (s - 1)) := by gcongr
  have h5 : (s - 1) * M < ε / 2 := by
    have : (s - 1) * M ≤ ε / (2 * (M + 1)) * M := mul_le_mul_of_nonneg_right hsd.le hM0
    refine this.trans_lt ?_
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  rw [hsplit, abs_mul, abs_of_pos hsp]
  have h6 : |(∫ t in Set.Ioc 1 T, H t * t ^ (-s)) + ∫ t in Set.Ioi T, H t * t ^ (-s)| ≤
      M + ε / 2 * (1 / (s - 1)) :=
    (abs_add_le _ _).trans (add_le_add h1 (h2.trans h4))
  calc (s - 1) * |(∫ t in Set.Ioc 1 T, H t * t ^ (-s)) + ∫ t in Set.Ioi T, H t * t ^ (-s)|
      ≤ (s - 1) * (M + ε / 2 * (1 / (s - 1))) := by gcongr
    _ = (s - 1) * M + ε / 2 := by field_simp
    _ < ε := by linarith

private lemma primeRpow_add_log_eq {B s : ℝ} (hs : 1 < s) :
    ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-s) + Real.log (s - 1) - (B - γ) =
      (s - 1) * ∫ t in Set.Ioi 1,
        (primeInvSum t - Real.log (Real.log t) - B) * t ^ (-s) := by
  have h1 := integrableOn_primeInvSum hs
  have h2 := Real.integrableOn_log_log_mul_rpow hs
  have h3 : IntegrableOn (fun t : ℝ ↦ B * t ^ (-s)) (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul B
  have hK : ∫ t in Set.Ioi (1 : ℝ), t ^ (-s) = 1 / (s - 1) := by
    rw [integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow,
      show -s + 1 = -(s - 1) by ring, neg_div_neg_eq]
  have hint : ∫ t in Set.Ioi 1, (primeInvSum t - Real.log (Real.log t) - B) * t ^ (-s) =
      (∫ t in Set.Ioi 1, t ^ (-s) * primeInvSum t) -
        (∫ t in Set.Ioi 1, Real.log (Real.log t) * t ^ (-s)) - B * (1 / (s - 1)) := by
    have h12 : IntegrableOn
        (fun t : ℝ ↦ t ^ (-s) * primeInvSum t - Real.log (Real.log t) * t ^ (-s))
        (Set.Ioi 1) := h1.sub h2
    have e : (fun t : ℝ ↦ (primeInvSum t - Real.log (Real.log t) - B) * t ^ (-s)) =
        fun t : ℝ ↦ (t ^ (-s) * primeInvSum t - Real.log (Real.log t) * t ^ (-s)) -
          B * t ^ (-s) := funext fun t ↦ by ring
    rw [e, integral_sub h12 h3, integral_sub h1 h2, integral_const_mul, hK]
  have hγ := Real.eulerMascheroniConstant_eq_neg_integral_log_log hs
  have hsp : s - 1 ≠ 0 := by linarith
  rw [primeRpow_tsum_eq hs, hint, hγ]
  field_simp
  ring

private lemma tendsto_primeRpow_add_log {B : ℝ}
    (hB : Tendsto (fun x : ℝ ↦ primeInvSum x - Real.log (Real.log x) - B) atTop (𝓝 0)) :
    Tendsto (fun s : ℝ ↦ ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-s) + Real.log (s - 1))
      (𝓝[>] 1) (𝓝 (B - γ)) := by
  have h := weighted_small hB fun s hs ↦ integrableOn_H B hs
  refine tendsto_sub_nhds_zero_iff.1 (h.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (primeRpow_add_log_eq hs).symm

private lemma zeta_real_eq {s : ℝ} (hs : 1 < s) :
    riemannZeta (s : ℂ) =
      ((Real.exp (∑' p : Nat.Primes, -Real.log (1 - ((p : ℕ) : ℝ) ^ (-s))) : ℝ) : ℂ) := by
  have h := riemannZeta_eulerProduct_exp_log (s := (s : ℂ)) (by simpa using hs)
  rw [← h, Complex.ofReal_exp, Complex.ofReal_tsum]
  refine congrArg Complex.exp (tsum_congr fun p ↦ ?_)
  have hp : (1 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.one_lt
  have hq : ((p : ℕ) : ℝ) ^ (-s) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
  rw [Complex.ofReal_neg, Complex.ofReal_log (by linarith)]
  congr 2
  push_cast
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _)]
  simp

private lemma log_zeta_re {s : ℝ} (hs : 1 < s) :
    0 < (riemannZeta (s : ℂ)).re ∧ Real.log (riemannZeta (s : ℂ)).re =
      ∑' p : Nat.Primes, -Real.log (1 - ((p : ℕ) : ℝ) ^ (-s)) := by
  rw [zeta_real_eq hs, Complex.ofReal_re]
  exact ⟨Real.exp_pos _, Real.log_exp _⟩

private lemma tendsto_log_zeta_add_log :
    Tendsto (fun s : ℝ ↦ Real.log (riemannZeta (s : ℂ)).re + Real.log (s - 1))
      (𝓝[>] 1) (𝓝 0) := by
  have h0 := ZetaAsymptotics.tendsto_riemannZeta_sub_one_div_nhds_right
  have h1 : Tendsto (fun s : ℝ ↦ (riemannZeta (s : ℂ)).re - 1 / (s - 1)) (𝓝[>] 1) (𝓝 γ) := by
    have := (Complex.continuous_re.tendsto _).comp h0
    rw [Complex.ofReal_re] at this
    refine this.congr fun s ↦ ?_
    have e : (1 : ℂ) / ((s : ℂ) - 1) = ((1 / (s - 1) : ℝ) : ℂ) := by push_cast; ring
    simp only [Function.comp, e, Complex.sub_re, Complex.ofReal_re]
  have hs : Tendsto (fun s : ℝ ↦ s - 1) (𝓝[>] 1) (𝓝 0) := by
    have : Tendsto (fun s : ℝ ↦ s - 1) (𝓝 1) (𝓝 (1 - 1)) :=
      (continuous_id.sub continuous_const).tendsto 1
    simpa using this.mono_left nhdsWithin_le_nhds
  have h2 := ((hs.mul h1).add_const 1)
  have h3 := h2.log (by simp)
  simp only [zero_mul, zero_add, Real.log_one] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs1
  have hs1 : 1 < s := hs1
  have hz := (log_zeta_re hs1).1
  have hsp : s - 1 ≠ 0 := by linarith
  have : (s - 1) * ((riemannZeta (s : ℂ)).re - 1 / (s - 1)) + 1 =
      (s - 1) * (riemannZeta (s : ℂ)).re := by field_simp; ring
  rw [this, Real.log_mul hsp hz.ne']
  ring

private lemma abs_log_one_sub_add_le {u : ℝ} (h0 : 0 ≤ u) (h : u ≤ 1 / 2) :
    |Real.log (1 - u) + u| ≤ 2 * u ^ 2 := by
  have hu : |u| < 1 := by rw [abs_of_nonneg h0]; linarith
  have h1 := Real.abs_log_sub_add_sum_range_le hu 1
  have h2 : |u + Real.log (1 - u)| ≤ u ^ 2 / (1 - u) := by
    simpa [abs_of_nonneg h0] using h1
  rw [add_comm]
  refine h2.trans ?_
  rw [div_le_iff₀ (by linarith)]
  nlinarith [mul_nonneg (sq_nonneg u) (by linarith : 0 ≤ 1 - 2 * u)]

/-- The terms `log (1 - p^(-s)) + p^(-s)` of the absolutely convergent series. -/
private noncomputable def Fterm (s : ℝ) (p : Nat.Primes) : ℝ :=
  Real.log (1 - ((p : ℕ) : ℝ) ^ (-s)) + ((p : ℕ) : ℝ) ^ (-s)

private lemma rpow_le_inv {s : ℝ} (hs : 1 ≤ s) (p : Nat.Primes) :
    ((p : ℕ) : ℝ) ^ (-s) ≤ 1 / ((p : ℕ) : ℝ) := by
  have hp : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.one_lt.le
  calc ((p : ℕ) : ℝ) ^ (-s) ≤ ((p : ℕ) : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hp (by linarith)
    _ = 1 / ((p : ℕ) : ℝ) := by rw [Real.rpow_neg_one, one_div]

private lemma rpow_le_half {s : ℝ} (hs : 1 ≤ s) (p : Nat.Primes) :
    ((p : ℕ) : ℝ) ^ (-s) ≤ 1 / 2 := by
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.two_le
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
  refine (rpow_le_inv hs p).trans ?_
  rw [div_le_div_iff₀ hp0 two_pos]; linarith

private lemma Fterm_bound {s : ℝ} (hs : 1 ≤ s) (p : Nat.Primes) :
    ‖Fterm s p‖ ≤ 2 * (1 / ((p : ℕ) : ℝ) ^ 2) := by
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.two_le
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
  have hq0 : 0 ≤ ((p : ℕ) : ℝ) ^ (-s) := Real.rpow_nonneg hp0.le _
  have hq := rpow_le_inv hs p
  rw [Real.norm_eq_abs]
  refine (abs_log_one_sub_add_le hq0 (rpow_le_half hs p)).trans ?_
  have h : (((p : ℕ) : ℝ) ^ (-s)) ^ 2 ≤ (1 / ((p : ℕ) : ℝ)) ^ 2 := pow_le_pow_left₀ hq0 hq 2
  rw [one_div_pow] at h
  linarith

private lemma summable_Fterm_bound :
    Summable fun p : Nat.Primes ↦ 2 * (1 / ((p : ℕ) : ℝ) ^ 2) :=
  ((Real.summable_one_div_nat_pow.2 one_lt_two).mul_left 2).comp_injective Subtype.coe_injective

private lemma summable_Fterm {s : ℝ} (hs : 1 ≤ s) : Summable (Fterm s) :=
  Summable.of_norm_bounded summable_Fterm_bound (Fterm_bound hs)

/-- `F(s) = ∑_p (log (1 - p^(-s)) + p^(-s))`. -/
private noncomputable def Fs (s : ℝ) : ℝ := ∑' p : Nat.Primes, Fterm s p

private lemma continuousOn_Fs : ContinuousOn Fs (Set.Ici 1) := by
  refine continuousOn_tsum (fun p ↦ ?_) summable_Fterm_bound (fun p s hs ↦ Fterm_bound hs p)
  have hp : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.pos
  have hq : Continuous fun s : ℝ ↦ ((p : ℕ) : ℝ) ^ (-s) :=
    continuous_const.rpow continuous_neg (fun _ ↦ Or.inl hp.ne')
  unfold Fterm
  refine ContinuousOn.add (ContinuousOn.log (continuousOn_const.sub hq.continuousOn)
    fun s hs ↦ ?_) hq.continuousOn
  have := rpow_le_half hs p
  show 1 - ((p : ℕ) : ℝ) ^ (-s) ≠ 0
  intro h
  linarith

private lemma Fs_eq {s : ℝ} (hs : 1 < s) :
    Fs s = ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-s) - Real.log (riemannZeta (s : ℂ)).re := by
  have hsum := summable_Fterm hs.le
  have hG := summable_primes_rpow hs
  have hL : Summable fun p : Nat.Primes ↦ Real.log (1 - ((p : ℕ) : ℝ) ^ (-s)) := by
    refine (hsum.sub hG).congr fun p ↦ ?_
    simp [Fterm]
  rw [(log_zeta_re hs).2, tsum_neg]
  unfold Fs Fterm
  rw [Summable.tsum_add hL hG]
  ring

private lemma Fs_one_eq {B : ℝ}
    (hB : Tendsto (fun x : ℝ ↦ primeInvSum x - Real.log (Real.log x) - B) atTop (𝓝 0)) :
    Fs 1 = B - γ := by
  have h1 : Tendsto Fs (𝓝[>] 1) (𝓝 (Fs 1)) :=
    (continuousOn_Fs 1 (Set.mem_Ici.2 le_rfl)).tendsto.mono_left
      (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
  have h2 := (tendsto_primeRpow_add_log hB).sub tendsto_log_zeta_add_log
  have h3 : Tendsto Fs (𝓝[>] 1) (𝓝 (B - γ - 0)) := by
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [Fs_eq hs]; ring
  simpa using tendsto_nhds_unique h1 h3

private lemma tendsto_partial_sum_Fterm :
    Tendsto (fun x : ℝ ↦ ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime,
      (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) atTop (𝓝 (Fs 1)) := by
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ, a = fun n : ℕ ↦ Real.log (1 - 1 / (n : ℝ)) + 1 / (n : ℝ) :=
    ⟨_, rfl⟩
  have hFa : ∀ p : Nat.Primes, Fterm 1 p = a p := fun p ↦ by
    simp [Fterm, ha, Real.rpow_neg_one]
  have hsum : Summable (a ∘ ((↑) : {p : ℕ | p.Prime} → ℕ)) :=
    (summable_Fterm le_rfl).congr fun p ↦ hFa p
  have hind := summable_subtype_iff_indicator.1 hsum
  have hT := hind.hasSum.tendsto_sum_nat
  have heq : ∑' n, Set.indicator {p : ℕ | p.Prime} a n = Fs 1 := by
    rw [← tsum_subtype {p : ℕ | p.Prime} a]
    exact tsum_congr fun p ↦ (hFa p).symm
  rw [heq] at hT
  have := hT.comp ((tendsto_add_atTop_nat 1).comp (tendsto_nat_floor_atTop (α := ℝ)))
  refine this.congr fun x ↦ ?_
  simp only [Function.comp, Set.indicator_apply, Set.mem_ofPred_eq, ha]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ ↦ rfl
  ext p
  simp only [mem_filter, mem_range, mem_Ioc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h2.pos, by omega⟩, h2⟩
  · rintro ⟨⟨_, h1⟩, h2⟩
    exact ⟨by omega, h2⟩

private lemma tendsto_primeInvSum_aux {B : ℝ}
    (hB : Tendsto (fun x : ℝ ↦
      ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 : ℝ) / p - Real.log (Real.log x) - B) atTop (𝓝 0)) :
    Tendsto (fun x : ℝ ↦ primeInvSum x - Real.log (Real.log x) - B) atTop (𝓝 0) := by
  simpa only [primeInvSum_eq] using hB

/-- **Theorem 428.** `∑_{p ≤ x} 1/p = log log x + B₁ + o(1)` with the constant
`B₁ = γ + ∑_p (log (1 - 1/p) + 1/p)`. -/
@[kb "hardywright2008" "Thm 428, p. 485"]
theorem tendsto_sum_inv_primes_sub_log_log_eulerMascheroni :
    Tendsto (fun x : ℝ ↦ ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 : ℝ) / p - Real.log (Real.log x))
      atTop
      (𝓝 (γ + ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)))) := by
  obtain ⟨B, hB⟩ := tendsto_sum_inv_primes_sub_log_log
  have hF := Fs_one_eq (tendsto_primeInvSum_aux hB)
  have hF' : ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)) = B - γ := by
    rw [← hF]
    unfold Fs Fterm
    simp [Real.rpow_neg_one]
  rw [hF', show γ + (B - γ) = B by ring]
  simpa using hB.add_const B

/-- **Theorem 429** (Mertens). `∏_{p ≤ x} (1 - 1/p) ~ e^(-γ) / log x`. -/
@[kb "hardywright2008" "Thm 429, p. 485"]
theorem tendsto_prod_one_sub_inv_primes_mul_log :
    Tendsto (fun x : ℝ ↦ (∏ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 - 1 / (p : ℝ))) * Real.log x)
      atTop (𝓝 (Real.exp (-γ))) := by
  obtain ⟨B, hB⟩ := tendsto_sum_inv_primes_sub_log_log
  have hF := Fs_one_eq (tendsto_primeInvSum_aux hB)
  have h1 : Tendsto (fun x : ℝ ↦ ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime,
        (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)) -
      (∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 : ℝ) / p - Real.log (Real.log x))) atTop
      (𝓝 (Fs 1 - B)) :=
    tendsto_partial_sum_Fterm.sub (by simpa using hB.add_const B)
  have h2 := h1.rexp
  rw [hF, show B - γ - B = -γ by ring] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with x hx
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hpos : ∀ p ∈ (Ioc 0 ⌊x⌋₊).filter Nat.Prime, 0 < 1 - 1 / (p : ℝ) := fun p hp ↦ by
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.1 hp).2.two_le
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le two_pos h2
    linarith
  have e : ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)) -
      (∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 : ℝ) / p - Real.log (Real.log x)) =
      ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, Real.log (1 - 1 / (p : ℝ)) + Real.log (Real.log x) := by
    rw [Finset.sum_add_distrib]; ring
  rw [e, Real.exp_add, Real.exp_log hlog, Real.exp_sum]
  congr 1
  exact Finset.prod_congr rfl fun p hp ↦ Real.exp_log (hpos p hp)

end NTKB.HardyWright
