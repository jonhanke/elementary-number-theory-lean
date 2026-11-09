/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.ArithmeticFunctions.RamanujanSum
import NTKB.Attr
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# Hardy–Wright, § 17.5: the Dirichlet series of Ramanujan's sum

* Theorem 292: `∑_{n ≥ 1} c_n(m) n^{-s} = σ_{s-1}(m) / (m^{s-1} ζ(s))` for `s > 1` (here for complex
  `s` with `Re s > 1`), where `σ_{s-1}(m) = ∑_{d ∣ m} d^{s-1}`.
* Theorem 293: `∑_{n ≥ 1} c_n(m)/n² = 6 σ(m)/(π² m)`.

Proof as in the book: by Theorem 271, `c_n(m) = ∑_{d ∣ m, dd' = n} μ(d') d`, so the series is the
product of `∑ μ(d') d'^{-s} = 1/ζ(s)` and the finite sum `∑_{d ∣ m} d^{1-s}`.
-/

open Finset Complex ArithmeticFunction
open scoped Real ArithmeticFunction.Moebius ArithmeticFunction.sigma

namespace NTKB.HardyWright

/-- An `L`-series of a function supported on a finite set is the finite sum of its terms. -/
theorem LSeries_eq_sum_of_support_subset {f : ℕ → ℂ} {S : Finset ℕ} (hS : ∀ n ∉ S, f n = 0)
    (s : ℂ) : LSeries f s = ∑ n ∈ S, LSeries.term f s n := by
  rw [LSeries]
  exact tsum_eq_sum fun n hn => by
    rw [LSeries.term_def]; split_ifs <;> simp [hS n hn]

theorem LSeriesSummable_of_support_subset {f : ℕ → ℂ} {S : Finset ℕ} (hS : ∀ n ∉ S, f n = 0)
    (s : ℂ) : LSeriesSummable f s := by
  refine summable_of_ne_finset_zero (s := S) fun n hn => ?_
  rw [LSeries.term_def]; split_ifs <;> simp [hS n hn]

private lemma ramanujanSum_zero_left (m : ℕ) : ramanujanSumNat 0 m = 0 := by
  simp [ramanujanSumNat]

/-- **Theorem 292** (Hardy–Wright). For `Re s > 1` and `m ≥ 1`,
`∑_{n=1}^∞ c_n(m) n^{-s} = σ_{s-1}(m) / (m^{s-1} ζ(s))`, `σ_{s-1}(m) = ∑_{d ∣ m} d^{s-1}`. -/
@[kb "hardywright2008" "Thm 292, p. 347"]
theorem LSeries_ramanujanSum {m : ℕ} (hm : 0 < m) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => ramanujanSumNat n m) s =
      (∑ d ∈ m.divisors, (d : ℂ) ^ (s - 1)) / ((m : ℂ) ^ (s - 1) * riemannZeta s) := by
  set w : ℕ → ℂ := fun d => if d ∣ m ∧ d ≠ 0 then (d : ℂ) else 0 with hw
  have hconv : (fun n => ramanujanSumNat n m) =
      LSeries.convolution (fun n => (μ n : ℂ)) w := by
    funext n
    rw [LSeries.convolution_def]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [ramanujanSum_zero_left]
    beta_reduce
    rw [ramanujanSum_eq_sum n m hn, Nat.sum_divisorsAntidiagonal' (fun a b => (μ a : ℂ) * w b),
      sum_filter]
    refine sum_congr rfl fun d hd => ?_
    have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
    simp only [hw, hd0, ne_eq, not_false_eq_true, and_true]
    split_ifs <;> simp
  have hwS : ∀ n ∉ m.divisors, w n = 0 := by
    intro n hn
    simp only [hw, Nat.mem_divisors, not_and_or] at hn ⊢
    rw [ite_eq_right_of_eq_false _ _ (eq_false ?_)]
    rintro ⟨h1, h2⟩
    rcases hn with h | h
    · exact h h1
    · exact h hm.ne'
  rw [hconv, LSeries_convolution' (LSeriesSummable_moebius_iff.mpr hs)
    (LSeriesSummable_of_support_subset hwS s), LSeries_eq_sum_of_support_subset hwS s]
  have hμ : LSeries (fun n => (μ n : ℂ)) s = (riemannZeta s)⁻¹ := by
    have := LSeries_one_mul_Lseries_moebius hs
    rw [LSeries_one_eq_riemannZeta hs] at this
    exact eq_inv_of_mul_eq_one_right this
  rw [hμ]
  have hζ := riemannZeta_ne_zero_of_one_lt_re hs
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hmpow : (m : ℂ) ^ (s - 1) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hm0)
  -- `∑_{d ∣ m} d^{1-s} = m^{1-s} σ_{s-1}(m)`
  have hsum : ∑ d ∈ m.divisors, LSeries.term w s d =
      (∑ d ∈ m.divisors, (d : ℂ) ^ (s - 1)) / (m : ℂ) ^ (s - 1) := by
    rw [← Nat.sum_div_divisors m (fun d => (d : ℂ) ^ (s - 1)), Finset.sum_div]
    refine sum_congr rfl fun d hd => ?_
    have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
    have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast hd0
    have hdm : d ∣ m := Nat.dvd_of_mem_divisors hd
    rw [LSeries.term_of_ne_zero hd0]
    simp only [hw, hdm, ne_eq, hd0, not_false_eq_true, and_self, ↓reduceIte]
    have hmd : (m : ℂ) = ((m / d : ℕ) : ℂ) * d := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel hdm]
    have hdpow : (d : ℂ) ^ (s - 1) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hdc)
    rw [hmd, natCast_mul_natCast_cpow, cpow_sub _ _ hdc, cpow_one]
    have hds : (d : ℂ) ^ s ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hdc)
    have hmdpow : ((m / d : ℕ) : ℂ) ^ (s - 1) ≠ 0 := by
      have : ((m / d : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.div_pos (Nat.le_of_dvd hm hdm) (Nat.pos_of_ne_zero hd0)).ne'
      exact cpow_ne_zero_iff.mpr (Or.inl this)
    field_simp
  rw [hsum]
  field_simp

/-- **Theorem 293** (Hardy–Wright). For `m ≥ 1`, `∑_{n=1}^∞ c_n(m)/n² = 6 σ(m) / (π² m)`. -/
@[kb "hardywright2008" "Thm 293, p. 347"]
theorem tsum_ramanujanSum_div_sq {m : ℕ} (hm : 0 < m) :
    ∑' n : ℕ, ramanujanSumNat n m / (n : ℂ) ^ 2 = 6 * σ 1 m / (π ^ 2 * m) := by
  have h := LSeries_ramanujanSum hm (s := 2) (by norm_num)
  have hL : LSeries (fun n => ramanujanSumNat n m) 2 = ∑' n : ℕ, ramanujanSumNat n m / (n : ℂ) ^ 2 := by
    rw [LSeries]
    refine tsum_congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [ramanujanSum_zero_left]
    · rw [LSeries.term_of_ne_zero hn.ne', show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, cpow_natCast]
  rw [← hL, h, riemannZeta_two, sigma_one_apply]
  norm_num
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

end NTKB.HardyWright
