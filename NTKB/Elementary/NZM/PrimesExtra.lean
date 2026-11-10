/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.PrimeDistribution.NormalOrder
import NTKB.Elementary.NZM.TotientSums
import NTKB.Elementary.HardyWright.PrimeDistribution.ElementaryPNT
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.Convergence
import NTKB.Attr

/-!
# Further results of Chapter 8 (Niven–Zuckerman–Montgomery)

* **Theorem 8.13.**  `σ_a ≤ c` if `∑_{n ≤ x} |a_n| = O(x^c)` (with `c ≥ 0`), and conversely the
  estimate holds for every real `c > max(0, σ_a)`
  (`abscissaOfAbsConv_le_of_sum_norm_isBigO`, `sum_norm_isBigO_of_abscissaOfAbsConv_lt`).
  The small closure `LSeriesSummable.isBigO_sum_norm` is adapted from Tau Ceti
  (`TauCeti/NumberTheory/LSeries/CoefficientGrowth.lean`).
* **Corollary 8.33** (Hardy–Ramanujan).  `|ω(n) - log log n| < (log log n)^{3/4}` for all but
  `O(x / (log log x)^{1/2})` integers `n ≤ x` (`card_bad_omega_le`), derived from the Turán
  variance bound `NTKB.HardyWright.sum_sq_cardDistinctFactors_sub_le` (Chebyshev's inequality).
* **Corollary 8.10.**  For `p'` the next prime after `p`, `limsup (p' - p) / log p ≥ 1` and
  `liminf (p' - p) / log p ≤ 1`, proved from the prime number theorem (already in NTKB, in the
  form `p_n ~ n log n`).  We use the 0-indexed enumeration `p_n = nth Nat.Prime n`, so `p'` is
  `p_{n+1}`.  The statements are phrased with frequently-quantifiers: for every `c < 1` one has
  `(p_{n+1} - p_n) > c log p_n` infinitely often, and for every `c > 1` one has
  `(p_{n+1} - p_n) < c log p_n` infinitely often.
-/

open Finset Filter Asymptotics ArithmeticFunction
open scoped Topology ArithmeticFunction.omega

namespace NTKB.NZM

/-! ## Theorem 8.13 -/

/-- Absolute convergence at a point of nonnegative real part bounds the absolute
coefficient sums by the corresponding power (adapted from Tau Ceti,
`LSeriesSummable.isBigO_sum_norm`). -/
theorem lseriesSummable_isBigO_sum_norm {f : ℕ → ℂ} {s : ℂ} (h : LSeriesSummable f s)
    (hs : 0 ≤ s.re) :
    (fun n ↦ ∑ k ∈ Icc 1 n, ‖f k‖) =O[atTop] fun n ↦ (n : ℝ) ^ s.re := by
  refine isBigO_iff.mpr ⟨∑' k, ‖LSeries.term f s k‖, Eventually.of_forall fun n ↦ ?_⟩
  rw [Real.norm_of_nonneg (sum_nonneg fun _ _ ↦ norm_nonneg _),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  calc
    ∑ k ∈ Icc 1 n, ‖f k‖
      = ∑ k ∈ Icc 1 n, ‖LSeries.term f s k‖ * (k : ℝ) ^ s.re := by
        apply sum_congr rfl
        intro k hk
        have hk0 : k ≠ 0 := by have := (mem_Icc.mp hk).1; omega
        rw [LSeries.norm_term_eq, ite_eq_right hk0, div_mul_cancel₀ _
          (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk0)) _).ne']
    _ ≤ ∑ k ∈ Icc 1 n, ‖LSeries.term f s k‖ * (n : ℝ) ^ s.re := by
        apply sum_le_sum
        intro k hk
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg k) (by exact_mod_cast (mem_Icc.mp hk).2) hs)
          (norm_nonneg _)
    _ = (∑ k ∈ Icc 1 n, ‖LSeries.term f s k‖) * (n : ℝ) ^ s.re :=
        (sum_mul _ _ _).symm
    _ ≤ (∑' k, ‖LSeries.term f s k‖) * (n : ℝ) ^ s.re :=
        mul_le_mul_of_nonneg_right (h.norm.sum_le_tsum _ (fun _ _ ↦ norm_nonneg _))
          (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- **NZM, Theorem 8.13 (first part).**  If `c ≥ 0` and `∑_{n ≤ x} ‖a_n‖ = O(x^c)` as
`x → ∞`, then the abscissa of absolute convergence of `∑ a_n n^{-s}` is at most `c`. -/
@[kb "nivenzuckermanmontgomery" "Thm 8.13, p. 376"]
theorem abscissaOfAbsConv_le_of_sum_norm_isBigO {f : ℕ → ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : (fun x : ℝ ↦ ∑ n ∈ Icc 1 ⌊x⌋₊, ‖f n‖) =O[atTop] fun x ↦ x ^ c) :
    LSeries.abscissaOfAbsConv f ≤ (c : EReal) := by
  have hN : (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, ‖f k‖) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ c := by
    have := h.comp_tendsto tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using this
  refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy ↦ ?_
  exact LSeriesSummable_of_sum_norm_bigO hN hc (by simpa using hy)

/-- **NZM, Theorem 8.13 (converse).**  If `c > 0` and `c > σ_a` (that is, `c > max(0, σ_a)`),
then `∑_{n ≤ x} ‖a_n‖ = O(x^c)`. -/
@[kb "nivenzuckermanmontgomery" "Thm 8.13, p. 376"]
theorem sum_norm_isBigO_of_abscissaOfAbsConv_lt {f : ℕ → ℂ} {c : ℝ} (hc : 0 < c)
    (h : LSeries.abscissaOfAbsConv f < (c : EReal)) :
    (fun x : ℝ ↦ ∑ n ∈ Icc 1 ⌊x⌋₊, ‖f n‖) =O[atTop] fun x ↦ x ^ c := by
  have hs : LSeriesSummable f (c : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using h)
  obtain ⟨K, hK⟩ := (lseriesSummable_isBigO_sum_norm hs (by simpa using hc.le)).bound
  obtain ⟨N, hN⟩ := eventually_atTop.1 hK
  refine isBigO_iff.mpr ⟨max K 0, ?_⟩
  filter_upwards [eventually_ge_atTop ((N : ℝ) + 1)] with x hx
  have hx0 : (0 : ℝ) ≤ x := by linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)]
  have hfl : N ≤ ⌊x⌋₊ := Nat.le_floor (by linarith)
  have h1 := hN ⌊x⌋₊ hfl
  simp only [Complex.ofReal_re] at h1
  have h2 : ((⌊x⌋₊ : ℕ) : ℝ) ^ c ≤ x ^ c :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hx0) hc.le
  have h3 : 0 ≤ ∑ n ∈ Icc 1 ⌊x⌋₊, ‖f n‖ := sum_nonneg fun _ _ ↦ norm_nonneg _
  rw [Real.norm_of_nonneg h3, Real.norm_of_nonneg (Real.rpow_nonneg hx0 _)]
  rw [Real.norm_of_nonneg h3, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] at h1
  have h4 : 0 ≤ ((⌊x⌋₊ : ℕ) : ℝ) ^ c := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc _ ≤ K * ((⌊x⌋₊ : ℕ) : ℝ) ^ c := h1
    _ ≤ max K 0 * ((⌊x⌋₊ : ℕ) : ℝ) ^ c := mul_le_mul_of_nonneg_right (le_max_left _ _) h4
    _ ≤ max K 0 * x ^ c := mul_le_mul_of_nonneg_left h2 (le_max_right _ _)

/-! ## Corollary 8.33 -/

/-- **NZM, Corollary 8.33 (Hardy–Ramanujan).**  The inequality
`|ω(n) - log log n| < (log log n)^{3/4}` fails for at most `C x / (log log x)^{1/2}` integers
`n ≤ x`, once `x ≥ x₀`.  (Derived from the Turán variance bound, which is centred at
`log log x`; for `√x < n ≤ x` one has `log log n = log log x + O(1)`.) -/
@[kb "nivenzuckermanmontgomery" "Cor 8.33, p. 398"]
theorem card_bad_omega_le :
    ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      (((Ioc 0 ⌊x⌋₊).filter fun n : ℕ ↦
          ¬ |(ω n : ℝ) - Real.log (Real.log n)| < (Real.log (Real.log n)) ^ (3 / 4 : ℝ)).card : ℝ) ≤
        C * x / (Real.log (Real.log x)) ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC⟩ := NTKB.HardyWright.sum_sq_cardDistinctFactors_sub_le
  refine ⟨max C 0 * 16 + 1, max 3 (Real.exp (Real.exp 16)), fun x hx ↦ ?_⟩
  have hx3 : 3 ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hL16 : 16 ≤ Real.log (Real.log x) := by
    have h1 : Real.exp (Real.exp 16) ≤ x := (le_max_right _ _).trans hx
    have h2 : Real.exp 16 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 h1
    exact (Real.le_log_iff_exp_le hlogx).2 h2
  set L := Real.log (Real.log x) with hLdef
  have hL0 : 0 < L := by linarith
  set q : ℝ := L ^ (1 / 4 : ℝ) with hqdef
  have hq : 0 < q := Real.rpow_pos_of_pos hL0 _
  have hq4 : q ^ 4 = L := by
    rw [hqdef, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  have hq3 : L ^ (3 / 4 : ℝ) = q ^ 3 := by
    rw [hqdef, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  have hq2 : L ^ (1 / 2 : ℝ) = q ^ 2 := by
    rw [hqdef, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  have hq2' : 2 ≤ q := by
    by_contra h
    push Not at h
    have := pow_lt_pow_left₀ h hq.le (by norm_num : (4 : ℕ) ≠ 0)
    norm_num at this
    linarith
  have hq3ge : 8 ≤ q ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hq2' 3
    norm_num at this; linarith
  rw [hq2]
  set B := Ioc 0 ⌊x⌋₊ with hB
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := B.filter fun n : ℕ ↦
      ¬ |(ω n : ℝ) - Real.log (Real.log n)| < (Real.log (Real.log n)) ^ (3 / 4 : ℝ))
    (fun n : ℕ ↦ n ≤ ⌊√x⌋₊)
  have h1 : ((B.filter fun n : ℕ ↦
      ¬ |(ω n : ℝ) - Real.log (Real.log n)| < (Real.log (Real.log n)) ^ (3 / 4 : ℝ)).filter
      fun n : ℕ ↦ n ≤ ⌊√x⌋₊).card ≤ ⌊√x⌋₊ := by
    calc _ ≤ (Ioc 0 ⌊√x⌋₊).card := by
          refine Finset.card_le_card fun n hn ↦ ?_
          simp only [hB, mem_filter, mem_Ioc] at hn ⊢
          exact ⟨hn.1.1.1, hn.2⟩
      _ = _ := by simp
  have h1' : (((B.filter fun n : ℕ ↦
      ¬ |(ω n : ℝ) - Real.log (Real.log n)| < (Real.log (Real.log n)) ^ (3 / 4 : ℝ)).filter
      fun n : ℕ ↦ n ≤ ⌊√x⌋₊).card : ℝ) ≤ √x :=
    (Nat.cast_le.2 h1).trans (Nat.floor_le (Real.sqrt_nonneg x))
  set S' := (B.filter fun n : ℕ ↦
      ¬ |(ω n : ℝ) - Real.log (Real.log n)| < (Real.log (Real.log n)) ^ (3 / 4 : ℝ)).filter
    fun n : ℕ ↦ ¬ n ≤ ⌊√x⌋₊ with hS'
  have hterm : ∀ n ∈ S', (q ^ 3 / 4) ^ 2 ≤ ((ω n : ℝ) - L) ^ 2 := by
    intro n hn
    simp only [hS', hB, mem_filter, mem_Ioc, not_le, not_lt] at hn
    obtain ⟨⟨⟨hn0, hnN⟩, hbad⟩, hnM⟩ := hn
    have hsq : √x < n := (Nat.floor_lt (Real.sqrt_nonneg x)).1 hnM
    have hsq1 : 1 ≤ √x := by
      rw [Real.one_le_sqrt]; linarith
    have hnx : (n : ℝ) ≤ x := (Nat.cast_le.2 hnN).trans (Nat.floor_le hx0.le)
    have hlogn0 : 0 < Real.log n := Real.log_pos (by linarith)
    have hlog1 : Real.log x / 2 < Real.log n := by
      rw [← Real.log_sqrt hx0.le]; exact Real.log_lt_log (Real.sqrt_pos.2 hx0) hsq
    have hℓ2 : L - Real.log 2 < Real.log (Real.log n) := by
      have : Real.log (Real.log x / 2) < Real.log (Real.log n) :=
        Real.log_lt_log (by positivity) hlog1
      rwa [Real.log_div hlogx.ne' two_ne_zero] at this
    have hℓ3 : Real.log (Real.log n) ≤ L :=
      Real.log_le_log hlogn0 (Real.log_le_log (by linarith) hnx)
    have hl2 := Real.log_two_lt_d9
    set u := Real.log (Real.log n) with hu
    have hu2 : L / 2 ≤ u := by linarith
    have hu3 : (L / 2) ^ (3 / 4 : ℝ) ≤ u ^ (3 / 4 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hu2 (by norm_num)
    have h23 : (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (3 / 4 : ℝ) ≤ 1)
      simpa using this
    have h23' : 0 < (2 : ℝ) ^ (3 / 4 : ℝ) := by positivity
    have hu4 : q ^ 3 / 2 ≤ u ^ (3 / 4 : ℝ) := by
      refine le_trans ?_ hu3
      rw [Real.div_rpow hL0.le (by norm_num), hq3]
      exact div_le_div_of_nonneg_left (by positivity) h23' h23
    have habs : q ^ 3 / 4 ≤ |(ω n : ℝ) - L| := by
      have h5 : |(ω n : ℝ) - u| ≤ |(ω n : ℝ) - L| + |L - u| := by
        have := abs_add_le ((ω n : ℝ) - L) (L - u)
        simpa using this
      have h6 : |L - u| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith
      linarith
    have h7 : (q ^ 3 / 4) ^ 2 ≤ |(ω n : ℝ) - L| ^ 2 :=
      pow_le_pow_left₀ (by positivity) habs 2
    rwa [sq_abs] at h7
  have hCx : ∑ n ∈ B, ((ω n : ℝ) - L) ^ 2 ≤ max C 0 * x * L := by
    refine (hC x hx3).trans ?_
    have : 0 ≤ x * L := by positivity
    nlinarith [le_max_left C 0]
  have h2 : (S'.card : ℝ) * (q ^ 3 / 4) ^ 2 ≤ max C 0 * x * L := by
    calc (S'.card : ℝ) * (q ^ 3 / 4) ^ 2 = ∑ _n ∈ S', (q ^ 3 / 4) ^ 2 := by simp
      _ ≤ ∑ n ∈ S', ((ω n : ℝ) - L) ^ 2 := Finset.sum_le_sum hterm
      _ ≤ ∑ n ∈ B, ((ω n : ℝ) - L) ^ 2 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ ↦ sq_nonneg _
          intro n hn
          simp only [hS', mem_filter] at hn
          exact hn.1.1
      _ ≤ _ := hCx
  have h5 : (S'.card : ℝ) * q ^ 2 ≤ 16 * (max C 0 * x) := by
    have hq4' : 0 < q ^ 4 := by positivity
    refine le_of_mul_le_mul_right ?_ hq4'
    rw [← hq4] at h2
    nlinarith [h2]
  have hsplit' : ((B.filter fun n : ℕ ↦
      ¬ |(ω n : ℝ) - Real.log (Real.log n)| < (Real.log (Real.log n)) ^ (3 / 4 : ℝ)).card : ℝ) =
      (((B.filter fun n : ℕ ↦
      ¬ |(ω n : ℝ) - Real.log (Real.log n)| < (Real.log (Real.log n)) ^ (3 / 4 : ℝ)).filter
        fun n : ℕ ↦ n ≤ ⌊√x⌋₊).card : ℝ) + S'.card := by
    rw [← Nat.cast_add, hsplit]
  have hq2s : q ^ 2 ≤ √x := by
    rw [Real.le_sqrt (by positivity) hx0.le]
    have hLx : L ≤ x := by
      have := Real.log_le_self hlogx.le
      linarith [Real.log_le_self hx0.le]
    calc (q ^ 2) ^ 2 = q ^ 4 := by ring
      _ = L := hq4
      _ ≤ x := hLx
  have hq2p : 0 < q ^ 2 := by positivity
  rw [le_div_iff₀ hq2p, hsplit']
  have hsx : √x * q ^ 2 ≤ x := by
    calc √x * q ^ 2 ≤ √x * √x := mul_le_mul_of_nonneg_left hq2s (Real.sqrt_nonneg _)
      _ = x := Real.mul_self_sqrt hx0.le
  nlinarith [mul_le_mul_of_nonneg_right h1' hq2p.le]

/-! ## Theorem 8.32 -/

/-- **NZM, Theorem 8.32.**  `∑_{n ≤ x} (ω(n) - log log n)² = O(x log log x)`, centred at
`log log n` (the book's form).  Derived from the Turán variance bound centred at `log log x`
(`NTKB.HardyWright.sum_sq_cardDistinctFactors_sub_le`) via `(a - c)² ≤ 2 (a - b)² + 2 (b - c)²`:
for `√x < n ≤ x` one has `|log log n - log log x| ≤ log 2`, while the `n ≤ √x` part is
crudely `O(x)` using `ω(n) ≤ log n / log 2`. -/
@[kb "nivenzuckermanmontgomery" "Thm 8.32, p. 396"]
theorem sum_sq_omega_sub_loglog_le :
    ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∑ n ∈ Ioc 0 ⌊x⌋₊, ((ω n : ℝ) - Real.log (Real.log n)) ^ 2 ≤
        C * x * Real.log (Real.log x) := by
  obtain ⟨C, hC⟩ := NTKB.HardyWright.sum_sq_cardDistinctFactors_sub_le
  refine ⟨66 + 2 * max C 0, max 3 (Real.exp (Real.exp 16)), fun x hx ↦ ?_⟩
  have hx3 : 3 ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hL16 : 16 ≤ Real.log (Real.log x) := by
    have h1 : Real.exp (Real.exp 16) ≤ x := (le_max_right _ _).trans hx
    have h2 : Real.exp 16 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 h1
    exact (Real.le_log_iff_exp_le hlogx).2 h2
  have hlogx16 : 16 ≤ Real.log x := by
    have := Real.add_one_le_exp (16 : ℝ)
    have h1 : Real.exp (Real.exp 16) ≤ x := (le_max_right _ _).trans hx
    have h2 : Real.exp 16 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 h1
    linarith
  set L := Real.log (Real.log x) with hLdef
  have hL0 : 0 < L := by linarith
  -- `(log x)^2 ≤ 16 √x`
  have hlog2 : (Real.log x) ^ 2 ≤ 16 * √x := by
    have hs1 : 0 < √x := Real.sqrt_pos.2 hx0
    have hs2 : 0 < √(√x) := Real.sqrt_pos.2 hs1
    have e : Real.log x = 4 * Real.log (√(√x)) := by
      rw [Real.log_sqrt hs1.le, Real.log_sqrt hx0.le]; ring
    have h1 : Real.log (√(√x)) ≤ √(√x) := Real.log_le_self hs2.le
    have h2 : Real.log x ≤ 4 * √(√x) := by rw [e]; linarith
    have h3 := pow_le_pow_left₀ hlogx.le h2 2
    have h4 : (√(√x)) ^ 2 = √x := Real.sq_sqrt hs1.le
    calc (Real.log x) ^ 2 ≤ (4 * √(√x)) ^ 2 := h3
      _ = 16 * √x := by rw [mul_pow, h4]; norm_num
  set B := Ioc 0 ⌊x⌋₊ with hB
  rw [← Finset.sum_filter_add_sum_filter_not B (fun n : ℕ ↦ n ≤ ⌊√x⌋₊)]
  have hsx : 0 ≤ √x := Real.sqrt_nonneg x
  have hsx2 : √x * √x = x := Real.mul_self_sqrt hx0.le
  -- small part
  have hsmall : ∑ n ∈ B.filter (fun n : ℕ ↦ n ≤ ⌊√x⌋₊),
      ((ω n : ℝ) - Real.log (Real.log n)) ^ 2 ≤ 64 * x * L := by
    have hterm : ∀ n ∈ B.filter (fun n : ℕ ↦ n ≤ ⌊√x⌋₊),
        ((ω n : ℝ) - Real.log (Real.log n)) ^ 2 ≤ 4 * (Real.log x) ^ 2 := by
      intro n hn
      simp only [hB, mem_filter, mem_Ioc] at hn
      obtain ⟨⟨hn0, -⟩, hnM⟩ := hn
      have hnsq : (n : ℝ) ≤ √x := (Nat.cast_le.2 hnM).trans (Nat.floor_le hsx)
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
      have hnx : (n : ℝ) ≤ x := by nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt hx0.le]
      have hlogn : Real.log n ≤ Real.log x := Real.log_le_log (by linarith) hnx
      have hlogn2 : Real.log n ≤ Real.log x / 2 := by
        rw [← Real.log_sqrt hx0.le]
        exact Real.log_le_log (by linarith) hnsq
      have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn1
      -- `ω n ≤ log n / log 2 ≤ 2 log n`
      have hω : (ω n : ℝ) ≤ Real.log x := by
        have h1 : (2 : ℝ) ^ (ω n) ≤ n := by exact_mod_cast two_pow_cardDistinctFactors_le n hn0
        have h2 : Real.log ((2 : ℝ) ^ (ω n)) ≤ Real.log n :=
          Real.log_le_log (by positivity) h1
        rw [Real.log_pow] at h2
        have h3 := Real.log_two_gt_d9
        nlinarith [(Nat.cast_nonneg (ω n) : (0 : ℝ) ≤ ω n)]
      have hω0 : (0 : ℝ) ≤ ω n := Nat.cast_nonneg _
      have hu1 : Real.log (Real.log n) ≤ Real.log x := by
        refine (Real.log_le_self hlogn0).trans hlogn
      have hu2 : -1 ≤ Real.log (Real.log n) := by
        rcases eq_or_lt_of_le hn1 with h | h
        · rw [← h]; simp
        · have h2 : (2 : ℝ) ≤ n := by
            have : 1 < n := by exact_mod_cast h
            exact_mod_cast this
          have h3 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) h2
          have h4 := Real.log_two_gt_d9
          have h5 := Real.log_two_lt_d9
          have h6 : Real.log (1 / 2) ≤ Real.log (Real.log n) :=
            Real.log_le_log (by norm_num) (by linarith)
          rw [one_div, Real.log_inv] at h6
          linarith
      have : |(ω n : ℝ) - Real.log (Real.log n)| ≤ 2 * Real.log x := by
        rw [abs_le]; constructor <;> linarith
      have h7 := pow_le_pow_left₀ (abs_nonneg _) this 2
      rw [sq_abs] at h7
      nlinarith
    have hcard : ((B.filter (fun n : ℕ ↦ n ≤ ⌊√x⌋₊)).card : ℝ) ≤ √x := by
      have : (B.filter (fun n : ℕ ↦ n ≤ ⌊√x⌋₊)).card ≤ ⌊√x⌋₊ := by
        calc _ ≤ (Ioc 0 ⌊√x⌋₊).card := by
              refine Finset.card_le_card fun n hn ↦ ?_
              simp only [hB, mem_filter, mem_Ioc] at hn ⊢
              exact ⟨hn.1.1, hn.2⟩
          _ = _ := by simp
      exact (Nat.cast_le.2 this).trans (Nat.floor_le hsx)
    calc _ ≤ ∑ _n ∈ B.filter (fun n : ℕ ↦ n ≤ ⌊√x⌋₊), 4 * (Real.log x) ^ 2 :=
          Finset.sum_le_sum hterm
      _ = ((B.filter (fun n : ℕ ↦ n ≤ ⌊√x⌋₊)).card : ℝ) * (4 * (Real.log x) ^ 2) := by simp
      _ ≤ √x * (4 * (16 * √x)) := by
          have h0 : 0 ≤ 4 * (Real.log x) ^ 2 := by positivity
          calc _ ≤ √x * (4 * (Real.log x) ^ 2) := mul_le_mul_of_nonneg_right hcard h0
            _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hsx
      _ = 64 * x := by linear_combination 64 * hsx2
      _ ≤ 64 * x * L := by nlinarith
  -- large part
  have hlarge : ∑ n ∈ B.filter (fun n : ℕ ↦ ¬ n ≤ ⌊√x⌋₊),
      ((ω n : ℝ) - Real.log (Real.log n)) ^ 2 ≤ (2 * max C 0 + 2) * x * L := by
    have hterm : ∀ n ∈ B.filter (fun n : ℕ ↦ ¬ n ≤ ⌊√x⌋₊),
        ((ω n : ℝ) - Real.log (Real.log n)) ^ 2 ≤ 2 * ((ω n : ℝ) - L) ^ 2 + 2 := by
      intro n hn
      simp only [hB, mem_filter, mem_Ioc, not_le] at hn
      obtain ⟨⟨hn0, hnN⟩, hnM⟩ := hn
      have hsq : √x < n := (Nat.floor_lt hsx).1 hnM
      have hsq1 : 1 ≤ √x := by rw [Real.one_le_sqrt]; linarith
      have hnx : (n : ℝ) ≤ x := (Nat.cast_le.2 hnN).trans (Nat.floor_le hx0.le)
      have hlogn0 : 0 < Real.log n := Real.log_pos (by linarith)
      have hlog1 : Real.log x / 2 < Real.log n := by
        rw [← Real.log_sqrt hx0.le]; exact Real.log_lt_log (Real.sqrt_pos.2 hx0) hsq
      have hℓ2 : L - Real.log 2 < Real.log (Real.log n) := by
        have : Real.log (Real.log x / 2) < Real.log (Real.log n) :=
          Real.log_lt_log (by positivity) hlog1
        rwa [Real.log_div hlogx.ne' two_ne_zero] at this
      have hℓ3 : Real.log (Real.log n) ≤ L :=
        Real.log_le_log hlogn0 (Real.log_le_log (by linarith) hnx)
      have hl2 := Real.log_two_lt_d9
      have hd : |L - Real.log (Real.log n)| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith
      have hd2 : (L - Real.log (Real.log n)) ^ 2 ≤ 1 := by
        have := pow_le_pow_left₀ (abs_nonneg _) hd 2
        rw [sq_abs] at this; simpa using this
      nlinarith [sq_nonneg ((ω n : ℝ) - L - (L - Real.log (Real.log n)))]
    have hCx : ∑ n ∈ B, ((ω n : ℝ) - L) ^ 2 ≤ max C 0 * x * L := by
      refine (hC x hx3).trans ?_
      have : 0 ≤ x * L := by positivity
      nlinarith [le_max_left C 0]
    have hcard : ((B.filter (fun n : ℕ ↦ ¬ n ≤ ⌊√x⌋₊)).card : ℝ) ≤ x := by
      have : (B.filter (fun n : ℕ ↦ ¬ n ≤ ⌊√x⌋₊)).card ≤ ⌊x⌋₊ := by
        calc _ ≤ B.card := Finset.card_filter_le _ _
          _ = _ := by simp [hB]
      exact (Nat.cast_le.2 this).trans (Nat.floor_le hx0.le)
    have hsub : ∑ n ∈ B.filter (fun n : ℕ ↦ ¬ n ≤ ⌊√x⌋₊), ((ω n : ℝ) - L) ^ 2 ≤
        ∑ n ∈ B, ((ω n : ℝ) - L) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun n _ _ ↦ sq_nonneg _
    calc _ ≤ ∑ n ∈ B.filter (fun n : ℕ ↦ ¬ n ≤ ⌊√x⌋₊), (2 * ((ω n : ℝ) - L) ^ 2 + 2) :=
          Finset.sum_le_sum hterm
      _ = 2 * ∑ n ∈ B.filter (fun n : ℕ ↦ ¬ n ≤ ⌊√x⌋₊), ((ω n : ℝ) - L) ^ 2 +
          2 * ((B.filter (fun n : ℕ ↦ ¬ n ≤ ⌊√x⌋₊)).card : ℝ) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]; simp [mul_comm]
      _ ≤ 2 * (max C 0 * x * L) + 2 * x := by nlinarith
      _ ≤ (2 * max C 0 + 2) * x * L := by nlinarith
  nlinarith

/-! ## Corollary 8.10 -/

section PrimeGaps

/-- The `n`-th prime (0-indexed) as a real number. -/
private noncomputable abbrev pr (n : ℕ) : ℝ := (Nat.nth Nat.Prime n : ℝ)

private lemma pr_pos (n : ℕ) : 0 < pr n := by
  exact_mod_cast (Nat.prime_nth_prime n).pos

private lemma pr_mono : Monotone pr := fun m n h ↦ by
  exact_mod_cast (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone h

private lemma logpr_nonneg (n : ℕ) : 0 ≤ Real.log (pr n) :=
  Real.log_nonneg (by exact_mod_cast (Nat.prime_nth_prime n).one_lt.le)

private lemma logpr_pos (n : ℕ) : 0 < Real.log (pr n) :=
  Real.log_pos (by exact_mod_cast (Nat.prime_nth_prime n).one_lt)

private lemma logpr_mono : Monotone fun n ↦ Real.log (pr n) := fun m _ h ↦
  Real.log_le_log (pr_pos m) (pr_mono h)

private lemma tendsto_succ_real : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
  tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop

private lemma tendsto_log_succ : Tendsto (fun n : ℕ ↦ Real.log ((n : ℝ) + 1)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_succ_real

/-- `log p_n / log (n + 1) → 1`, a consequence of the prime number theorem `p_n ~ n log n`. -/
private lemma tendsto_logpr_div :
    Tendsto (fun n : ℕ ↦ Real.log (pr n) / Real.log ((n : ℝ) + 1)) atTop (𝓝 1) := by
  have hR : Tendsto (fun n : ℕ ↦ pr n / (((n : ℝ) + 1) * Real.log ((n : ℝ) + 1))) atTop (𝓝 1) :=
    NTKB.HardyWright.nth_prime_asymptotic
  have hRl := hR.log one_ne_zero
  rw [Real.log_one] at hRl
  have h1 := (hRl.div_atTop tendsto_log_succ).add
    (NTKB.Apostol.tendsto_log_div_self.comp tendsto_log_succ)
  rw [add_zero] at h1
  have h2 := h1.const_add 1
  rw [add_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0, tendsto_log_succ.eventually_gt_atTop 0] with n hn ht
  have hn' : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hD : 0 < ((n : ℝ) + 1) * Real.log ((n : ℝ) + 1) := mul_pos hn' ht
  have hRp : 0 < pr n / (((n : ℝ) + 1) * Real.log ((n : ℝ) + 1)) := div_pos (pr_pos n) hD
  have : Real.log (pr n) = Real.log (pr n / (((n : ℝ) + 1) * Real.log ((n : ℝ) + 1))) +
      Real.log ((n : ℝ) + 1) + Real.log (Real.log ((n : ℝ) + 1)) := by
    rw [Real.log_div (pr_pos n).ne' hD.ne', Real.log_mul hn'.ne' ht.ne']
    ring
  simp only [Function.comp_apply]
  rw [this]
  field_simp
  ring

/-- `p_n / (n log p_n) → 1`. -/
private lemma tendsto_pr_div :
    Tendsto (fun n : ℕ ↦ pr n / ((n : ℝ) * Real.log (pr n))) atTop (𝓝 1) := by
  have hR : Tendsto (fun n : ℕ ↦ pr n / (((n : ℝ) + 1) * Real.log ((n : ℝ) + 1))) atTop (𝓝 1) :=
    NTKB.HardyWright.nth_prime_asymptotic
  have h2 : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) / n) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).add tendsto_one_div_atTop_nhds_zero_nat
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have : (n : ℝ) ≠ 0 := by positivity
    field_simp
  have h3 := (hR.mul h2).mul (tendsto_logpr_div.inv₀ one_ne_zero)
  rw [inv_one, mul_one, mul_one] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0, tendsto_log_succ.eventually_gt_atTop 0] with n hn ht
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hn'' : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlp : Real.log (pr n) ≠ 0 := (logpr_pos n).ne'
  have ht' : Real.log ((n : ℝ) + 1) ≠ 0 := ht.ne'
  field_simp

/-- **NZM, Corollary 8.10 (limsup part).**  For every `c < 1`, the gap to the next prime exceeds
`c log p` for infinitely many primes `p`; i.e. `limsup (p' - p) / log p ≥ 1`.  Here the primes are
enumerated as `p_n = nth Nat.Prime n` and `p' = p_{n+1}`.  Proved from the prime number theorem. -/
@[kb "nivenzuckermanmontgomery" "Cor 8.10, p. 372"]
theorem exists_large_prime_gap {c : ℝ} (hc : c < 1) :
    ∃ᶠ n : ℕ in atTop,
      c * Real.log (Nat.nth Nat.Prime n) < (Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n := by
  wlog hc0 : 0 ≤ c generalizing c
  · push Not at hc0
    refine (this (c := 0) zero_lt_one le_rfl).mono fun n hn ↦ ?_
    have := logpr_nonneg n
    change c * Real.log (pr n) < pr (n + 1) - pr n
    change 0 * Real.log (pr n) < pr (n + 1) - pr n at hn
    nlinarith
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hcon
  have hgap : ∀ n, N0 ≤ n → pr (n + 1) - pr n ≤ c * Real.log (pr n) := fun n hn ↦
    not_lt.1 (hN0 n hn)
  have hind : ∀ m, N0 ≤ m → pr m - pr N0 ≤ c * ((m : ℝ) - N0) * Real.log (pr m) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      have h1 := hgap m hm
      have h2 := logpr_mono (Nat.le_succ m)
      have h3 : (N0 : ℝ) ≤ m := by exact_mod_cast hm
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left h2 (mul_nonneg hc0 (sub_nonneg.2 h3)),
        mul_le_mul_of_nonneg_left h2 hc0]
  have hU : Tendsto (fun n : ℕ ↦ pr n / ((n : ℝ) * Real.log (pr n))) atTop (𝓝 1) := tendsto_pr_div
  have hV : Tendsto (fun n : ℕ ↦ pr N0 / ((n : ℝ) * Real.log (pr n)) + c) atTop (𝓝 (0 + c)) := by
    refine Tendsto.add (Tendsto.div_atTop tendsto_const_nhds ?_) tendsto_const_nhds
    exact Tendsto.atTop_mul_atTop₀ tendsto_natCast_atTop_atTop
      (Real.tendsto_log_atTop.comp NTKB.Apostol.tendsto_nth_prime)
  have hD : ∀ n : ℕ, 0 < n → 0 < (n : ℝ) * Real.log (pr n) := fun n hn ↦
    mul_pos (by exact_mod_cast hn) (logpr_pos n)
  have hle : ∀ᶠ n : ℕ in atTop,
      pr n / ((n : ℝ) * Real.log (pr n)) ≤ pr N0 / ((n : ℝ) * Real.log (pr n)) + c := by
    filter_upwards [eventually_ge_atTop N0, eventually_gt_atTop 0] with n hn hn0
    have h1 := hind n hn
    have h2 : c * ((n : ℝ) - N0) * Real.log (pr n) ≤ c * n * Real.log (pr n) := by
      have : (0 : ℝ) ≤ N0 := Nat.cast_nonneg _
      have h3 := mul_nonneg hc0 (logpr_nonneg n)
      nlinarith
    have hDn := hD n hn0
    rw [div_le_iff₀ hDn]
    have : (pr N0 / ((n : ℝ) * Real.log (pr n)) + c) * ((n : ℝ) * Real.log (pr n)) =
        pr N0 + c * ((n : ℝ) * Real.log (pr n)) := by
      have hl := (logpr_pos n).ne'
      have hn' : (n : ℝ) ≠ 0 := by positivity
      field_simp
    rw [this]
    nlinarith
  have := le_of_tendsto_of_tendsto hU hV hle
  linarith

/-- **NZM, Corollary 8.10 (liminf part).**  For every `c > 1`, the gap to the next prime is less
than `c log p` for infinitely many primes `p`; i.e. `liminf (p' - p) / log p ≤ 1`.
Here `p_n = nth Nat.Prime n` and `p' = p_{n+1}`.  Proved from the prime number theorem. -/
@[kb "nivenzuckermanmontgomery" "Cor 8.10, p. 372"]
theorem exists_small_prime_gap {c : ℝ} (hc : 1 < c) :
    ∃ᶠ n : ℕ in atTop,
      (Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n < c * Real.log (Nat.nth Nat.Prime n) := by
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hcon
  have hc0 : 0 ≤ c := by linarith
  have hgap : ∀ n, N0 ≤ n → c * Real.log (pr n) ≤ pr (n + 1) - pr n := fun n hn ↦
    not_lt.1 (hN0 n hn)
  have hind : ∀ M, N0 ≤ M → ∀ m, M ≤ m →
      c * ((m : ℝ) - M) * Real.log (pr M) ≤ pr m - pr M := by
    intro M hM m hm
    induction m, hm using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      have h1 := hgap m (hM.trans hm)
      have h2 := logpr_mono hm
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left h2 hc0]
  set δ : ℝ := (1 - 1 / c) / 2 with hδ
  have hc1 : 1 / c < 1 := by rw [div_lt_one (by linarith)]; exact hc
  have hc2 : 0 < 1 / c := by positivity
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hδ1 : δ < 1 := by rw [hδ]; linarith
  have hcδ : c * (1 - δ) = (c + 1) / 2 := by
    rw [hδ]; field_simp; ring
  have hM : Tendsto (fun N : ℕ ↦ ⌊δ * (N : ℝ)⌋₊) atTop atTop :=
    tendsto_nat_floor_mul_atTop δ hδ0
  have hfrac : Tendsto (fun N : ℕ ↦ (⌊δ * (N : ℝ)⌋₊ : ℝ) / N) atTop (𝓝 δ) :=
    (tendsto_nat_floor_mul_div_atTop hδ0.le).comp tendsto_natCast_atTop_atTop
  -- the ratio `log (M + 1) / log (N + 1) → 1`
  have hmid : Tendsto (fun N : ℕ ↦
      Real.log ((⌊δ * (N : ℝ)⌋₊ : ℝ) + 1) / Real.log ((N : ℝ) + 1)) atTop (𝓝 1) := by
    have hlow : Tendsto (fun N : ℕ ↦ 1 + (Real.log δ - Real.log 2) / Real.log ((N : ℝ) + 1))
        atTop (𝓝 1) := by
      have := (tendsto_const_nhds (x := (1 : ℝ))).add
        (tendsto_const_nhds (x := Real.log δ - Real.log 2) |>.div_atTop tendsto_log_succ)
      rwa [add_zero] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_ge_atTop 1, tendsto_log_succ.eventually_gt_atTop 0] with N hN ht
      have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have h1 : δ * N < (⌊δ * (N : ℝ)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
      have h2 : Real.log δ + Real.log N ≤ Real.log ((⌊δ * (N : ℝ)⌋₊ : ℝ) + 1) := by
        rw [← Real.log_mul hδ0.ne' (by positivity)]
        exact Real.log_le_log (by positivity) h1.le
      have h3 : Real.log ((N : ℝ) + 1) ≤ Real.log 2 + Real.log N := by
        rw [← Real.log_mul (by norm_num) (by positivity)]
        exact Real.log_le_log (by positivity) (by linarith)
      rw [le_div_iff₀ ht, add_mul, div_mul_cancel₀ _ ht.ne']
      linarith
    · filter_upwards [eventually_ge_atTop 1, tendsto_log_succ.eventually_gt_atTop 0] with N hN ht
      have h1 : (⌊δ * (N : ℝ)⌋₊ : ℝ) ≤ N := by
        refine (Nat.floor_le (by positivity)).trans ?_
        have : (0 : ℝ) ≤ N := Nat.cast_nonneg _
        nlinarith
      rw [div_le_one ht]
      exact Real.log_le_log (by positivity) (by linarith)
  have hρ : Tendsto (fun N : ℕ ↦
      Real.log (pr ⌊δ * (N : ℝ)⌋₊) / Real.log (pr N)) atTop (𝓝 1) := by
    have h := ((tendsto_logpr_div.comp hM).mul hmid).mul (tendsto_logpr_div.inv₀ one_ne_zero)
    rw [inv_one, mul_one, mul_one] at h
    refine h.congr' ?_
    filter_upwards [hM.eventually_ge_atTop 1, tendsto_log_succ.eventually_gt_atTop 0,
      eventually_ge_atTop 1] with N hM1 ht hN
    have hM' : (1 : ℝ) ≤ (⌊δ * (N : ℝ)⌋₊ : ℝ) := by exact_mod_cast hM1
    have hl1 : 0 < Real.log ((⌊δ * (N : ℝ)⌋₊ : ℝ) + 1) := Real.log_pos (by linarith)
    have hl2 := logpr_pos N
    have hl3 := logpr_pos ⌊δ * (N : ℝ)⌋₊
    simp only [Function.comp_apply]
    field_simp
  have hU : Tendsto (fun n : ℕ ↦ pr n / ((n : ℝ) * Real.log (pr n))) atTop (𝓝 1) := tendsto_pr_div
  have hL : Tendsto (fun N : ℕ ↦ c * (1 - (⌊δ * (N : ℝ)⌋₊ : ℝ) / N) *
      (Real.log (pr ⌊δ * (N : ℝ)⌋₊) / Real.log (pr N))) atTop (𝓝 (c * (1 - δ) * 1)) :=
    (tendsto_const_nhds.mul (tendsto_const_nhds.sub hfrac)).mul hρ
  have hle : ∀ᶠ N : ℕ in atTop, c * (1 - (⌊δ * (N : ℝ)⌋₊ : ℝ) / N) *
      (Real.log (pr ⌊δ * (N : ℝ)⌋₊) / Real.log (pr N)) ≤ pr N / ((N : ℝ) * Real.log (pr N)) := by
    filter_upwards [hM.eventually_ge_atTop N0, eventually_gt_atTop 0] with N hMN hN
    set M := ⌊δ * (N : ℝ)⌋₊ with hMdef
    have hMle : (M : ℝ) ≤ N := by
      refine (Nat.floor_le (by positivity)).trans ?_
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg _
      nlinarith
    have h1 := hind M hMN N (by exact_mod_cast hMle)
    have h2 := pr_pos M
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have hl2 := logpr_pos N
    have e : c * (1 - (M : ℝ) / N) * (Real.log (pr M) / Real.log (pr N)) =
        c * ((N : ℝ) - M) * Real.log (pr M) / ((N : ℝ) * Real.log (pr N)) := by
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have := le_of_tendsto_of_tendsto hL hU hle
  rw [hcδ] at this
  linarith

end PrimeGaps

end NTKB.NZM
