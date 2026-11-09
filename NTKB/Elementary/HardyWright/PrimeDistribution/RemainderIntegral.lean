/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.PrimeDistribution.Selberg
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# From a sum to an integral: (22.15.3) and (22.15.7) (Hardy–Wright, Chapter XXII, § 22.15)

With `R(x) = ψ(x) - x` and Selberg's coefficients `aₙ`, Hardy–Wright replace the sum on the right of
(22.15.2) by an integral:
(22.15.3) `∑_{n ≤ x} aₙ |R(x/n)| = 2 ∫₁ˣ |R(x/t)| log t dt + O(x log x)`,
which turns (22.15.2) into
(22.15.7) `|R(x)| log² x ≤ 2 ∫₁ˣ |R(x/t)| log t dt + O(x log x)`.

We prove the inequality `≤` of (22.15.3) (the direction used for (22.15.7)) by the book's two
stages: partial summation (22.5.1) against `cₙ = aₙ - 2 ∫_{n-1}^n log t dt`, whose partial sums are
`O(n)` by Selberg's theorem (22.14.3), together with the inequality
`| |R(t)| - |R(t')| | ≤ F(t) - F(t')` (`t ≥ t' > 0`) for the increasing function `F(t) = ψ(t) + t`
and (22.15.4) `∑_{n ≤ x} F(x/n) = O(x log x)`; then the comparison of
`|R(x/n)| ∫_{n-1}^n log t dt` with `∫_{n-1}^n |R(x/t)| log t dt`.
Error terms are written `O(x (1 + log x))` for `x ≥ 1`.
-/

open Finset ArithmeticFunction Real Chebyshev MeasureTheory

namespace NTKB.HardyWright

open NTKB.Apostol

/-- Partial summation (Hardy–Wright (22.5.1)) on `{1, …, N + 1}`:
`∑_{n ≤ N+1} cₙ fₙ = C(N+1) f(N+1) + ∑_{n ≤ N} C(n) (f(n) - f(n+1))`, `C(n) = ∑_{k ≤ n} c_k`. -/
theorem sum_Ioc_mul_eq_abel (c f : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Ioc 0 (N + 1), c n * f n = (∑ k ∈ Ioc 0 (N + 1), c k) * f (N + 1) +
      ∑ n ∈ Ioc 0 N, (∑ k ∈ Ioc 0 n, c k) * (f n - f (n + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Ioc_succ_top (by omega), ih, sum_Ioc_succ_top (by omega : 0 ≤ N + 1),
      sum_Ioc_succ_top (f := fun n ↦ (∑ k ∈ Ioc 0 n, c k) * (f n - f (n + 1))) (by omega : 0 ≤ N)]
    ring

/-- `∑_{n ∈ (0, N]} h(n) = ∑_{m < N} h(m + 1)`. -/
theorem sum_Ioc_eq_sum_range_succ {M : Type*} [AddCommMonoid M] (h : ℕ → M) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, h n = ∑ m ∈ range N, h (m + 1) := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_Ioc_succ_top (by omega), ih, sum_range_succ]

/-- The increasing function `F(t) = ψ(t) + t` of § 22.15. -/
noncomputable def psiAddId (t : ℝ) : ℝ := ψ t + t

theorem psiAddId_mono : Monotone psiAddId := fun _ _ h ↦ add_le_add (psi_mono h) h

/-- `F(t) ≤ (log 4 + 5) t` for `t ≥ 0`. -/
theorem psiAddId_le {t : ℝ} (ht : 0 ≤ t) : psiAddId t ≤ (Real.log 4 + 5) * t := by
  have := psi_le_c t ht; unfold psiAddId; linarith

theorem psiAddId_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ psiAddId t := add_nonneg (psi_nonneg t) ht

/-- `|R(t)| ≤ (log 4 + 5) t` for `t ≥ 0`. -/
theorem abs_psiRem_le {t : ℝ} (ht : 0 ≤ t) : |psiRem t| ≤ (Real.log 4 + 5) * t := by
  have h1 := psi_le_c t ht
  have h2 := psi_nonneg t
  have h3 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [psiRem, abs_le]; constructor <;> nlinarith

/-- `|R(t')| ≤ |R(t)| + F(t) - F(t')` and `|R(t)| ≤ |R(t')| + F(t) - F(t')` for `t' ≤ t`
(Hardy–Wright, § 22.15). -/
theorem abs_psiRem_le_add {t t' : ℝ} (h : t' ≤ t) :
    |psiRem t'| ≤ |psiRem t| + (psiAddId t - psiAddId t') ∧
      |psiRem t| ≤ |psiRem t'| + (psiAddId t - psiAddId t') := by
  have hψ := psi_mono h
  have key : |psiRem t - psiRem t'| ≤ psiAddId t - psiAddId t' := by
    rw [psiRem, psiRem, psiAddId, psiAddId, abs_le]; constructor <;> linarith
  constructor
  · have := abs_sub_abs_le_abs_sub (psiRem t') (psiRem t)
    rw [abs_sub_comm] at this; linarith
  · have := abs_sub_abs_le_abs_sub (psiRem t) (psiRem t'); linarith

theorem measurable_psi : Measurable ψ := psi_mono.measurable

/-- A measurable function bounded on `[[a, b]]` is interval integrable. -/
theorem intervalIntegrable_of_bounded {f : ℝ → ℝ} (hf : Measurable f) {a b M : ℝ}
    (h : ∀ t ∈ Set.uIcc a b, |f t| ≤ M) : IntervalIntegrable f volume a b := by
  refine IntegrableOn.intervalIntegrable ?_
  refine Measure.integrableOn_of_bounded (M := M) (by simp [Set.uIcc]) hf.aestronglyMeasurable ?_
  exact (ae_restrict_iff' measurableSet_uIcc).2
    (Filter.Eventually.of_forall fun t ht ↦ by simpa [Real.norm_eq_abs] using h t ht)

/-- The integrand `t ↦ |R(x/t)| log t` of (22.15.3). -/
theorem measurable_abs_psiRem_div_mul_log (x : ℝ) :
    Measurable fun t : ℝ ↦ |psiRem (x / t)| * Real.log t := by
  unfold psiRem
  exact (continuous_abs.measurable.comp ((measurable_psi.comp (measurable_const.div measurable_id)).sub
    (measurable_const.div measurable_id))).mul Real.measurable_log

theorem intervalIntegrable_abs_psiRem_div_mul_log {x a b : ℝ} (hx : 0 ≤ x) (ha : 1 ≤ a)
    (hb : 1 ≤ b) :
    IntervalIntegrable (fun t : ℝ ↦ |psiRem (x / t)| * Real.log t) volume a b := by
  refine intervalIntegrable_of_bounded (measurable_abs_psiRem_div_mul_log x)
    (M := (Real.log 4 + 5) * x * Real.log (max a b)) fun t ht ↦ ?_
  have ht1 : 1 ≤ t := by
    rcases Set.mem_uIcc.1 ht with h | h
    · exact ha.trans h.1
    · exact hb.trans h.1
  have htb : t ≤ max a b := by
    rcases Set.mem_uIcc.1 ht with h | h
    · exact h.2.trans (le_max_right _ _)
    · exact h.2.trans (le_max_left _ _)
  have ht0 : 0 < t := by linarith
  have hl0 : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hxt : x / t ≤ x := div_le_self hx ht1
  rw [abs_mul, abs_abs, abs_of_nonneg hl0]
  have hc : 0 ≤ Real.log 4 + 5 := by have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith
  refine mul_le_mul ((abs_psiRem_le (div_nonneg hx ht0.le)).trans ?_)
    (Real.log_le_log ht0 htb) hl0 (by positivity)
  exact mul_le_mul_of_nonneg_left hxt hc

/-- `∫_{n-1}^{n} log t dt` for `n ≥ 2`, and `0` for `n ≤ 1`. -/
noncomputable def logPiece (n : ℕ) : ℝ := if n ≤ 1 then 0 else ∫ t in ((n : ℝ) - 1)..n, Real.log t

theorem logPiece_eq {n : ℕ} (hn : 2 ≤ n) :
    logPiece n = n * Real.log n - (n - 1) * Real.log (n - 1) - 1 := by
  unfold logPiece
  split_ifs with h
  · omega
  · rw [integral_log]; ring_nf

theorem logPiece_nonneg (n : ℕ) : 0 ≤ logPiece n := by
  unfold logPiece
  split_ifs with h
  · exact le_rfl
  · refine intervalIntegral.integral_nonneg (by linarith) fun t ht ↦ Real.log_nonneg ?_
    have : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
    linarith [ht.1]

theorem logPiece_le (n : ℕ) : logPiece n ≤ n := by
  unfold logPiece
  split_ifs with h
  · exact Nat.cast_nonneg n
  · have hn : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
    calc ∫ t in ((n : ℝ) - 1)..n, Real.log t ≤ ∫ t in ((n : ℝ) - 1)..n, (n : ℝ) := by
          refine intervalIntegral.integral_mono_on (by linarith) intervalIntegral.intervalIntegrable_log'
            intervalIntegrable_const fun t ht ↦ ?_
          have := Real.log_le_sub_one_of_pos (show 0 < t by linarith [ht.1])
          linarith [ht.2]
      _ = n := by simp

/-- `∑_{k ≤ n} ∫_{k-1}^{k} log = n log n - n + 1` for `n ≥ 1`. -/
theorem sum_logPiece {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ Ioc 0 n, logPiece k = n * Real.log n - n + 1 := by
  induction n, hn using Nat.le_induction with
  | base => simp [logPiece]
  | succ n hn ih =>
    rw [sum_Ioc_succ_top (by omega), ih, logPiece_eq (by omega)]
    push_cast; ring

/-- (22.15.4): `∑_{n ≤ x} F(x/n) ≤ (log 4 + 5) x (1 + log x)`. -/
theorem sum_psiAddId_div_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, psiAddId (x / n) ≤ (Real.log 4 + 5) * x * (1 + Real.log x) := by
  have hx0 : 0 < x := by linarith
  calc ∑ n ∈ Ioc 0 ⌊x⌋₊, psiAddId (x / n) ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, (Real.log 4 + 5) * x * (1 / n) := by
        refine sum_le_sum fun n hn ↦ ?_
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Ioc.1 hn).1
        refine (psiAddId_le (by positivity)).trans (le_of_eq ?_)
        ring
    _ = (Real.log 4 + 5) * x * ∑ n ∈ Ioc 0 ⌊x⌋₊, (1 / n : ℝ) := by rw [mul_sum]
    _ ≤ (Real.log 4 + 5) * x * (1 + Real.log x) := by
        refine mul_le_mul_of_nonneg_left (sum_Ioc_inv_le_one_add_log hx) ?_
        have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
        positivity

/-- For a nonnegative antitone sequence `G`: `∑_{n ≤ M} n (G n - G (n+1)) ≤ ∑_{n ≤ M+1} G n`. -/
theorem sum_mul_sub_le_sum {G : ℕ → ℝ} (hG0 : ∀ n, 0 ≤ G n) (M : ℕ) :
    ∑ n ∈ Ioc 0 M, (n : ℝ) * (G n - G (n + 1)) ≤ ∑ n ∈ Ioc 0 (M + 1), G n := by
  have h := sum_Ioc_mul_eq_abel (fun _ ↦ (1 : ℝ)) G M
  simp only [one_mul, sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul, mul_one] at h
  rw [h]
  have := hG0 (M + 1)
  have : (0 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- (22.15.3), inequality `≤`, and hence **(22.15.7)**:
`|R(x)| log² x ≤ 2 ∫₁ˣ |R(x/t)| log t dt + O(x log x)` (here `O(x (1 + log x))`, `x ≥ 1`). -/
@[kb "hardywright2008" "(22.15.7), p. 504"]
theorem abs_psiRem_mul_log_sq_le_integral :
    ∃ K, ∀ x : ℝ, 1 ≤ x →
      |psiRem x| * Real.log x ^ 2 ≤
        2 * (∫ t in (1 : ℝ)..x, |psiRem (x / t)| * Real.log t) + K * x * (1 + Real.log x) := by
  obtain ⟨K₁, hK₁⟩ := abs_psiRem_mul_log_sq_le
  obtain ⟨K₂, hK₂⟩ := selberg_theorem'
  have hK₂0 : 0 ≤ K₂ := by
    have := (abs_nonneg _).trans (hK₂ 1 le_rfl); linarith
  set c := Real.log 4 + 5 with hc
  have hc0 : 0 ≤ c := by have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith
  refine ⟨K₁ + 2 * (K₂ + 2) * c + 4 * c, fun x hx ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hN1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  obtain ⟨M, hN⟩ : ∃ M, ⌊x⌋₊ = M + 1 := ⟨⌊x⌋₊ - 1, by omega⟩
  have hNx : ((M + 1 : ℕ) : ℝ) ≤ x := hN ▸ Nat.floor_le hx0.le
  set f : ℕ → ℝ := fun n ↦ |psiRem (x / n)| with hf
  set G : ℕ → ℝ := fun n ↦ psiAddId (x / n) with hG
  have hG0 : ∀ n, 0 ≤ G n := fun n ↦ psiAddId_nonneg (by positivity)
  -- `|f n - f (n+1)| ≤ G n - G (n+1)`
  have hfG : ∀ n : ℕ, 0 < n → |f n - f (n + 1)| ≤ G n - G (n + 1) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hle : x / ((n + 1 : ℕ) : ℝ) ≤ x / n :=
      div_le_div_of_nonneg_left hx0.le hn0 (by push_cast; linarith)
    obtain ⟨h1, h2⟩ := abs_psiRem_le_add hle
    rw [abs_le]; constructor <;> simp only [hf, hG] <;> linarith
  have hsumG := sum_psiAddId_div_le hx
  rw [hN] at hsumG
  -- the partial sums `C(n) = ∑_{k ≤ n} (aₖ - 2 ℓₖ)` are `O(n)`
  set C : ℕ → ℝ := fun n ↦ ∑ k ∈ Ioc 0 n, (selbergCoeff k - 2 * logPiece k) with hC
  have hCle : ∀ n : ℕ, 1 ≤ n → |C n| ≤ (K₂ + 2) * n := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h := hK₂ n hn1
    rw [Nat.floor_natCast] at h
    have : C n = (∑ k ∈ Ioc 0 n, selbergCoeff k - 2 * n * Real.log n) - 2 * (1 - n) := by
      simp only [hC, sum_sub_distrib, ← mul_sum, sum_logPiece hn]; ring
    rw [this]
    calc _ ≤ |∑ k ∈ Ioc 0 n, selbergCoeff k - 2 * n * Real.log n| + |2 * (1 - (n : ℝ))| :=
          abs_sub _ _
      _ ≤ K₂ * n + 2 * n := by
          refine add_le_add h ?_
          rw [abs_le]; constructor <;> linarith
      _ = (K₂ + 2) * n := by ring
  -- Stage 1: `∑ aₙ f n ≤ 2 ∑ ℓₙ f n + O(x (1 + log x))`
  have hstage1 : ∑ n ∈ Ioc 0 (M + 1), selbergCoeff n * f n ≤
      2 * ∑ n ∈ Ioc 0 (M + 1), logPiece n * f n + 2 * (K₂ + 2) * c * x * (1 + Real.log x) := by
    have habel := sum_Ioc_mul_eq_abel (fun k ↦ selbergCoeff k - 2 * logPiece k) f M
    have hsplit : ∑ n ∈ Ioc 0 (M + 1), (selbergCoeff n - 2 * logPiece n) * f n =
        ∑ n ∈ Ioc 0 (M + 1), selbergCoeff n * f n - 2 * ∑ n ∈ Ioc 0 (M + 1), logPiece n * f n := by
      rw [mul_sum, ← sum_sub_distrib]; exact sum_congr rfl fun n _ ↦ by ring
    rw [hsplit] at habel
    -- the boundary term
    have hb : (∑ k ∈ Ioc 0 (M + 1), (selbergCoeff k - 2 * logPiece k)) * f (M + 1) ≤
        (K₂ + 2) * c * x := by
      have h1 := hCle (M + 1) (by omega)
      have hM0 : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
      have h2 : f (M + 1) ≤ c * (x / ((M + 1 : ℕ) : ℝ)) := abs_psiRem_le (by positivity)
      have h3 : 0 ≤ f (M + 1) := abs_nonneg _
      calc _ ≤ |C (M + 1)| * f (M + 1) := mul_le_mul_of_nonneg_right (le_abs_self _) h3
        _ ≤ (K₂ + 2) * ((M + 1 : ℕ) : ℝ) * (c * (x / ((M + 1 : ℕ) : ℝ))) :=
            mul_le_mul h1 h2 h3 (by positivity)
        _ = (K₂ + 2) * c * x := by field_simp
    -- the sum term
    have hs : ∑ n ∈ Ioc 0 M, (∑ k ∈ Ioc 0 n, (selbergCoeff k - 2 * logPiece k)) *
        (f n - f (n + 1)) ≤ (K₂ + 2) * (c * x * (1 + Real.log x)) := by
      calc _ ≤ ∑ n ∈ Ioc 0 M, (K₂ + 2) * ((n : ℝ) * (G n - G (n + 1))) := by
            refine sum_le_sum fun n hn ↦ ?_
            have hn1 := (mem_Ioc.1 hn).1
            calc _ ≤ |C n * (f n - f (n + 1))| := le_abs_self _
              _ = |C n| * |f n - f (n + 1)| := abs_mul _ _
              _ ≤ (K₂ + 2) * n * (G n - G (n + 1)) :=
                  mul_le_mul (hCle n hn1) (hfG n hn1) (abs_nonneg _) (by positivity)
              _ = _ := by ring
        _ = (K₂ + 2) * ∑ n ∈ Ioc 0 M, (n : ℝ) * (G n - G (n + 1)) := by rw [mul_sum]
        _ ≤ (K₂ + 2) * ∑ n ∈ Ioc 0 (M + 1), G n :=
            mul_le_mul_of_nonneg_left (sum_mul_sub_le_sum hG0 M) (by linarith)
        _ ≤ (K₂ + 2) * (c * x * (1 + Real.log x)) := by
            exact mul_le_mul_of_nonneg_left hsumG (by linarith)
    have hxl : x ≤ x * (1 + Real.log x) := by nlinarith
    have hxl' := mul_le_mul_of_nonneg_left hxl (by positivity : 0 ≤ (K₂ + 2) * c)
    linarith
  -- Stage 2: `∑ ℓₙ f n ≤ ∫₁ˣ |R(x/t)| log t dt + O(x (1 + log x))`
  set h : ℝ → ℝ := fun t ↦ |psiRem (x / t)| * Real.log t with hh
  have hint : ∀ a b : ℝ, 1 ≤ a → 1 ≤ b → IntervalIntegrable h volume a b :=
    fun a b ha hb ↦ intervalIntegrable_abs_psiRem_div_mul_log hx0.le ha hb
  have hpiece : ∀ m : ℕ, logPiece (m + 2) * f (m + 2) ≤
      (∫ t in ((m : ℝ) + 1)..((m : ℝ) + 2), h t) + (G (m + 1) - G (m + 2)) * (m + 2) := by
    intro m
    have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hlp : logPiece (m + 2) = ∫ t in ((m : ℝ) + 1)..((m : ℝ) + 2), Real.log t := by
      unfold logPiece
      split_ifs with h
      · omega
      · push_cast; ring_nf
    have hGd : 0 ≤ G (m + 1) - G (m + 2) := by
      simp only [hG]
      apply sub_nonneg.2 (psiAddId_mono _)
      exact div_le_div_of_nonneg_left hx0.le (by positivity) (by push_cast; linarith)
    calc logPiece (m + 2) * f (m + 2)
        = ∫ t in ((m : ℝ) + 1)..((m : ℝ) + 2), f (m + 2) * Real.log t := by
          rw [hlp, intervalIntegral.integral_const_mul, mul_comm]
      _ ≤ ∫ t in ((m : ℝ) + 1)..((m : ℝ) + 2), (h t + (G (m + 1) - G (m + 2)) * Real.log t) := by
          refine intervalIntegral.integral_mono_on (by linarith)
            (intervalIntegral.intervalIntegrable_log'.const_mul _)
            ((hint _ _ hm1 (by linarith)).add (intervalIntegral.intervalIntegrable_log'.const_mul _))
            fun t ht ↦ ?_
          have ht1 : 1 ≤ t := hm1.trans ht.1
          have ht0 : 0 < t := by linarith
          have hlt : 0 ≤ Real.log t := Real.log_nonneg ht1
          -- `x/(m+2) ≤ x/t ≤ x/(m+1)`
          have h1 : x / (((m + 2 : ℕ) : ℝ)) ≤ x / t :=
            div_le_div_of_nonneg_left hx0.le ht0 (by push_cast; linarith [ht.2])
          have h2 : x / t ≤ x / (((m + 1 : ℕ) : ℝ)) :=
            div_le_div_of_nonneg_left hx0.le (by positivity) (by push_cast; linarith [ht.1])
          have h3 := (abs_psiRem_le_add h1).1
          have h4 := psiAddId_mono h2
          simp only [hh, hf, hG]
          nlinarith
      _ = (∫ t in ((m : ℝ) + 1)..((m : ℝ) + 2), h t) +
            (G (m + 1) - G (m + 2)) * logPiece (m + 2) := by
          rw [intervalIntegral.integral_add (hint _ _ hm1 (by linarith))
            (intervalIntegral.intervalIntegrable_log'.const_mul _),
            intervalIntegral.integral_const_mul, hlp]
      _ ≤ _ := by
          gcongr
          have := logPiece_le (m + 2); push_cast at this; linarith
  have hstage2 : ∑ n ∈ Ioc 0 (M + 1), logPiece n * f n ≤
      (∫ t in (1 : ℝ)..x, h t) + 2 * c * x * (1 + Real.log x) := by
    rw [sum_Ioc_eq_sum_range_succ, sum_range_succ']
    have hl1 : logPiece (0 + 1) = 0 := by simp [logPiece]
    rw [hl1, zero_mul, add_zero]
    -- the integral over `[1, M+1]` as a sum over unit intervals
    have hadj : ∑ m ∈ range M, ∫ t in ((m : ℝ) + 1)..((m : ℝ) + 2), h t =
        ∫ t in (1 : ℝ)..((M : ℝ) + 1), h t := by
      have := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := h)
        (a := fun k : ℕ ↦ (k : ℝ) + 1) (n := M) fun k _ ↦ hint _ _ (by
          linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) (by
          push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add] at this
      rw [← this]
      refine sum_congr rfl fun m _ ↦ ?_
      ring_nf
    have htail : (∫ t in (1 : ℝ)..((M : ℝ) + 1), h t) ≤ ∫ t in (1 : ℝ)..x, h t := by
      have hM1 : (1 : ℝ) ≤ (M : ℝ) + 1 := by linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
      have hMx : (M : ℝ) + 1 ≤ x := by exact_mod_cast hNx
      rw [← intervalIntegral.integral_add_adjacent_intervals (hint 1 _ le_rfl hM1)
        (hint _ x hM1 hx)]
      have : 0 ≤ ∫ t in ((M : ℝ) + 1)..x, h t :=
        intervalIntegral.integral_nonneg hMx fun t ht ↦
          mul_nonneg (abs_nonneg _) (Real.log_nonneg (hM1.trans ht.1))
      linarith
    have hGsum : ∑ m ∈ range M, (G (m + 1) - G (m + 2)) * ((m : ℝ) + 2) ≤
        2 * (c * x * (1 + Real.log x)) := by
      calc _ ≤ ∑ m ∈ range M, 2 * (((m + 1 : ℕ) : ℝ) * (G (m + 1) - G (m + 1 + 1))) := by
            refine sum_le_sum fun m _ ↦ ?_
            have hGd : 0 ≤ G (m + 1) - G (m + 2) := by
              simp only [hG]
              apply sub_nonneg.2 (psiAddId_mono _)
              exact div_le_div_of_nonneg_left hx0.le (by positivity) (by push_cast; linarith)
            push_cast
            nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
        _ = 2 * ∑ n ∈ Ioc 0 M, (n : ℝ) * (G n - G (n + 1)) := by
            rw [mul_sum, sum_Ioc_eq_sum_range_succ]
        _ ≤ 2 * ∑ n ∈ Ioc 0 (M + 1), G n :=
            mul_le_mul_of_nonneg_left (sum_mul_sub_le_sum hG0 M) (by norm_num)
        _ ≤ 2 * (c * x * (1 + Real.log x)) := by
            exact mul_le_mul_of_nonneg_left hsumG (by norm_num)
    calc ∑ m ∈ range M, logPiece (m + 1 + 1) * f (m + 1 + 1)
        ≤ ∑ m ∈ range M, ((∫ t in ((m : ℝ) + 1)..((m : ℝ) + 2), h t) +
            (G (m + 1) - G (m + 2)) * ((m : ℝ) + 2)) := sum_le_sum fun m _ ↦ hpiece m
      _ = (∫ t in (1 : ℝ)..((M : ℝ) + 1), h t) +
            ∑ m ∈ range M, (G (m + 1) - G (m + 2)) * ((m : ℝ) + 2) := by
          rw [sum_add_distrib, hadj]
      _ ≤ _ := by linarith
  have h22 := hK₁ x hx
  rw [hN] at h22
  have hxl : x ≤ x * (1 + Real.log x) := by nlinarith
  simp only [hf] at hstage1 hstage2
  have hI : (∫ t in (1 : ℝ)..x, h t) = ∫ t in (1 : ℝ)..x, |psiRem (x / t)| * Real.log t := rfl
  rw [hI] at hstage2
  rw [hc] at hstage1 hstage2 ⊢
  linear_combination h22 + hstage1 + 2 * hstage2

end NTKB.HardyWright
