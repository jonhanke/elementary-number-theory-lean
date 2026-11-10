/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.Averages.DivisorSums
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Factorization.Basic
import NTKB.Attr

/-!
# Averages of `φ(n)/n` and reduced residues in intervals (Niven–Zuckerman–Montgomery, § 8.3)

All error terms are explicit inequalities.

* **Theorem 8.24.** For `x ≥ 2`, `∑_{n ≤ x} φ(n)/n = (6/π²) x + O(log x)`; the error is at most
  `7 log x` (`abs_sum_totient_div_sub_le`).
* **Theorem 8.29.** The number of integers `n` with `a < n ≤ a + N` and `gcd(n, q) = 1` is
  `(φ(q)/q) N + O(2 ^ ω(q))`; the error is at most `2 ^ ω(q)`
  (`abs_card_coprime_Ioc_sub_le`, stated in `ℚ`).
* **Theorem 8.30** (`ω(n) ≤ (1 + ε) log n / log log n`, sharp infinitely often) is stated as the
  proposition `OmegaOrderStatement`; the easy bound `2 ^ ω(n) ≤ n` is proved.
-/

open Finset ArithmeticFunction Real NTKB.Apostol
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace NTKB.NZM

/-! ## Helpers -/

/-- `φ(n)/n = ∑_{d ∣ n} μ(d)/d`. -/
theorem totient_div_eq_sum {K : Type*} [Field K] [CharZero K] (n : ℕ) (hn : 0 < n) :
    (n.totient : K) / n = ∑ d ∈ n.divisors, (μ d : K) / d := by
  have h := congrArg (fun z : ℤ ↦ (z : K)) (totient_eq_sum_moebius_mul hn)
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast] at h
  have hn0 : (n : K) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  rw [h, Finset.sum_div]
  refine sum_congr rfl fun d hd ↦ ?_
  have hd' : d ∣ n := Nat.dvd_of_mem_divisors hd
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hd0 : (d : K) ≠ 0 := Nat.cast_ne_zero.2 hdpos.ne'
  rw [Nat.cast_div hd' hd0]
  field_simp <;> ring

/-- Swapping `∑_{n ≤ N} ∑_{d ∣ n}`. -/
theorem sum_Ioc_sum_divisors (N : ℕ) (g : ℕ → ℝ) :
    ∑ n ∈ Ioc 0 N, ∑ d ∈ n.divisors, g d = ∑ d ∈ Ioc 0 N, ((N / d : ℕ) : ℝ) * g d := by
  have h := Finset.sum_comm' (s := Ioc 0 N) (t := fun n ↦ n.divisors) (t' := Ioc 0 N)
    (s' := fun d ↦ (Ioc 0 N).filter (fun n ↦ d ∣ n)) (f := fun _ d ↦ g d) (by
      intro n d
      simp only [Nat.mem_divisors, mem_Ioc, mem_filter]
      constructor
      · rintro ⟨⟨h1, h2⟩, hdn, _⟩
        exact ⟨⟨⟨h1, h2⟩, hdn⟩, ⟨Nat.pos_of_dvd_of_pos hdn h1, (Nat.le_of_dvd h1 hdn).trans h2⟩⟩
      · rintro ⟨⟨⟨h1, h2⟩, hdn⟩, _⟩
        exact ⟨⟨h1, h2⟩, hdn, h1.ne'⟩)
  rw [h]
  refine sum_congr rfl fun d _ ↦ ?_
  rw [sum_const, Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul]

/-! ## Theorem 8.24 -/

/-- **NZM, Theorem 8.24.** For `x ≥ 2`, `∑_{n ≤ x} φ(n)/n = (6/π²) x + O(log x)`; explicitly the
error is at most `7 log x`. -/
@[kb "nivenzuckermanmontgomery" "Thm 8.24, p. 390"]
theorem abs_sum_totient_div_sub_le {x : ℝ} (hx : 2 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, (n.totient : ℝ) / n - 6 / π ^ 2 * x| ≤ 7 * Real.log x := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hS : ∑ n ∈ Ioc 0 ⌊x⌋₊, (n.totient : ℝ) / n =
      ∑ d ∈ Ioc 0 ⌊x⌋₊, (μ d : ℝ) / d * (⌊x / d⌋₊ : ℝ) := by
    calc ∑ n ∈ Ioc 0 ⌊x⌋₊, (n.totient : ℝ) / n
        = ∑ n ∈ Ioc 0 ⌊x⌋₊, ∑ d ∈ n.divisors, (μ d : ℝ) / d :=
          sum_congr rfl fun n hn ↦ totient_div_eq_sum n (mem_Ioc.1 hn).1
      _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, ((⌊x⌋₊ / d : ℕ) : ℝ) * ((μ d : ℝ) / d) :=
          sum_Ioc_sum_divisors _ (fun d ↦ (μ d : ℝ) / d)
      _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, (μ d : ℝ) / d * (⌊x / d⌋₊ : ℝ) :=
          sum_congr rfl fun d _ ↦ by rw [← Nat.floor_div_natCast, mul_comm]
  rw [hS]
  set T := ∑ d ∈ Ioc 0 ⌊x⌋₊, (μ d : ℝ) / (d : ℝ) ^ 2 with hT
  -- the floor error
  have h1 : |∑ d ∈ Ioc 0 ⌊x⌋₊, (μ d : ℝ) / d * (⌊x / d⌋₊ : ℝ) - x * T| ≤ 1 + Real.log x := by
    have e : x * T = ∑ d ∈ Ioc 0 ⌊x⌋₊, (μ d : ℝ) / d * (x / d) := by
      rw [hT, mul_sum]
      exact sum_congr rfl fun d _ ↦ by ring
    rw [e, ← sum_sub_distrib]
    calc |∑ d ∈ Ioc 0 ⌊x⌋₊, ((μ d : ℝ) / d * (⌊x / d⌋₊ : ℝ) - (μ d : ℝ) / d * (x / d))|
        ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, |(μ d : ℝ) / d * (⌊x / d⌋₊ : ℝ) - (μ d : ℝ) / d * (x / d)| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, (1 / d : ℝ) := by
          refine sum_le_sum fun d hd ↦ ?_
          have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Ioc.1 hd).1
          rw [← mul_sub, abs_mul, abs_div, abs_of_nonneg hd0.le]
          calc |(μ d : ℝ)| / d * |(⌊x / d⌋₊ : ℝ) - x / d| ≤ 1 / d * 1 :=
                mul_le_mul (div_le_div_of_nonneg_right (by exact_mod_cast abs_moebius_le_one)
                  hd0.le) (abs_floor_sub_le (div_nonneg hx0.le hd0.le)) (abs_nonneg _)
                  (by positivity)
            _ = 1 / d := mul_one _
      _ ≤ 1 + Real.log x := sum_Ioc_inv_le_one_add_log hx1
  -- the tail of `∑ μ(d)/d²`
  have hN1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx1)
  have htail := abs_tsum_sub_sum_Ioc_le (c := fun n ↦ (μ n : ℝ) / (n : ℝ) ^ 2)
    (fun n ↦ by
      rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2)]
      exact div_le_div_of_nonneg_right (by exact_mod_cast abs_moebius_le_one) (by positivity))
    (by simp) (N := ⌊x⌋₊) (by omega)
  rw [hasSum_moebius_div_sq.tsum_eq] at htail
  have hNx : 1 / (⌊x⌋₊ : ℝ) ≤ 2 / x := by
    have h1 := Nat.lt_floor_add_one x
    have h0 : (0 : ℝ) < ⌊x⌋₊ := by exact_mod_cast hN1
    have h2 : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hN1
    rw [div_le_div_iff₀ h0 hx0]; linarith
  have hT2 : |x * T - 6 / π ^ 2 * x| ≤ 2 := by
    have : x * T - 6 / π ^ 2 * x = -(x * (6 / π ^ 2 - T)) := by ring
    rw [this, abs_neg, abs_mul, abs_of_nonneg hx0.le]
    calc x * |6 / π ^ 2 - T| ≤ x * (2 / x) :=
          mul_le_mul_of_nonneg_left (htail.trans hNx) hx0.le
      _ = 2 := by field_simp
  have h3 : (1 : ℝ) / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have h4 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  calc |∑ d ∈ Ioc 0 ⌊x⌋₊, (μ d : ℝ) / d * (⌊x / d⌋₊ : ℝ) - 6 / π ^ 2 * x|
      ≤ |∑ d ∈ Ioc 0 ⌊x⌋₊, (μ d : ℝ) / d * (⌊x / d⌋₊ : ℝ) - x * T| +
        |x * T - 6 / π ^ 2 * x| := abs_sub_le _ _ _
    _ ≤ (1 + Real.log x) + 2 := add_le_add h1 hT2
    _ ≤ 7 * Real.log x := by linarith

/-! ## Theorem 8.29 -/

/-- `∑_{d ∣ m} μ(d) = [m = 1]`. -/
theorem sum_moebius_divisors_ite (m : ℕ) (hm : 0 < m) :
    ∑ d ∈ m.divisors, (μ d : ℚ) = if m = 1 then 1 else 0 := by
  have h : ((μ : ArithmeticFunction ℚ) * (ζ : ArithmeticFunction ℚ)) m =
      (1 : ArithmeticFunction ℚ) m := by
    rw [coe_moebius_mul_coe_zeta]
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
    (fun a b ↦ (μ : ArithmeticFunction ℚ) a * (ζ : ArithmeticFunction ℚ) b),
    ArithmeticFunction.one_apply] at h
  rw [← h]
  refine sum_congr rfl fun d hd ↦ ?_
  have hd0 : m / d ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd hm (Nat.dvd_of_mem_divisors hd))
      (Nat.pos_of_mem_divisors hd)).ne'
  simp [intCoe_apply, natCoe_apply, zeta_apply, hd0]

/-- The coprimality indicator as a Möbius sum over the divisors of `q` dividing `n`. -/
theorem coprime_indicator_eq (q : ℕ) (hq : 0 < q) (n : ℤ) :
    (if Nat.Coprime n.natAbs q then (1 : ℚ) else 0) =
      ∑ d ∈ q.divisors.filter (fun d : ℕ ↦ (d : ℤ) ∣ n), (μ d : ℚ) := by
  have hg : 0 < Nat.gcd n.natAbs q := Nat.gcd_pos_of_pos_right _ hq
  have h := sum_moebius_divisors_ite (Nat.gcd n.natAbs q) hg
  have e1 : (if Nat.Coprime n.natAbs q then (1 : ℚ) else 0) =
      if Nat.gcd n.natAbs q = 1 then 1 else 0 := if_congr Iff.rfl rfl rfl
  rw [e1, ← h]
  refine sum_congr ?_ (fun _ _ ↦ rfl)
  ext d
  simp only [Nat.mem_divisors, mem_filter, Int.ofNat_dvd_left, Nat.dvd_gcd_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, _⟩
    exact ⟨⟨h2, hq.ne'⟩, h1⟩
  · rintro ⟨⟨h2, _⟩, h1⟩
    exact ⟨⟨h1, h2⟩, hg.ne'⟩

/-- The number of multiples of `d` in `(a, a + N]` is `N/d + O(1)` with error at most `1`. -/
theorem abs_card_dvd_Ioc_sub (a : ℤ) (N d : ℕ) (hd : 0 < d) :
    |(((Ioc a (a + N)).filter (fun n : ℤ ↦ (d : ℤ) ∣ n)).card : ℚ) - (N : ℚ) / d| ≤ 1 := by
  have hd' : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd
  have h := Int.Ioc_filter_dvd_card a (a + N) hd'
  simp only [Int.cast_add, Int.cast_natCast, add_div] at h
  have hy : 0 ≤ (N : ℚ) / d := by positivity
  have h1 := Int.floor_le ((a : ℚ) / d + (N : ℚ) / d)
  have h2 := Int.lt_floor_add_one ((a : ℚ) / d + (N : ℚ) / d)
  have h3 := Int.floor_le ((a : ℚ) / d)
  have h4 := Int.lt_floor_add_one ((a : ℚ) / d)
  have hv : 0 ≤ ⌊(a : ℚ) / d + (N : ℚ) / d⌋ - ⌊(a : ℚ) / d⌋ := by
    by_contra hneg
    push_neg at hneg
    have h5 : ⌊(a : ℚ) / d + (N : ℚ) / d⌋ - ⌊(a : ℚ) / d⌋ ≤ -1 := by omega
    have h6 : ((⌊(a : ℚ) / d + (N : ℚ) / d⌋ : ℤ) : ℚ) - ((⌊(a : ℚ) / d⌋ : ℤ) : ℚ) ≤ -1 := by
      exact_mod_cast h5
    linarith
  rw [max_eq_left hv] at h
  have hc : ((((Ioc a (a + N)).filter (fun n : ℤ ↦ (d : ℤ) ∣ n)).card : ℕ) : ℚ) =
      ((⌊(a : ℚ) / d + (N : ℚ) / d⌋ : ℤ) : ℚ) - ((⌊(a : ℚ) / d⌋ : ℤ) : ℚ) := by
    exact_mod_cast h
  rw [hc, abs_le]
  constructor <;> linarith

/-- `∑_{d ∣ q} |μ(d)| ≤ 2 ^ ω(q)` (in fact equality holds). -/
theorem sum_abs_moebius_divisors_le (q : ℕ) (hq : 0 < q) :
    ∑ d ∈ q.divisors, |(μ d : ℚ)| ≤ 2 ^ (cardDistinctFactors q) := by
  have e : ∀ d : ℕ, |(μ d : ℚ)| = if Squarefree d then 1 else 0 := by
    intro d
    have := abs_moebius (n := d)
    rw [← Int.cast_abs, this]
    split_ifs <;> simp
  simp_rw [e]
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
  have hcard : (q.divisors.filter (fun d ↦ Squarefree d)).card ≤ 2 ^ (cardDistinctFactors q) := by
    calc (q.divisors.filter (fun d ↦ Squarefree d)).card
        ≤ (q.primeFactors.powerset).card := by
          refine Finset.card_le_card_of_injOn Nat.primeFactors ?_ ?_
          · intro d hd
            have hd' := mem_filter.1 (Finset.mem_coe.1 hd)
            exact Finset.mem_coe.2 (mem_powerset.2
              (Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd'.1) hq.ne'))
          · intro a ha b hb hab
            have ha' := mem_filter.1 (Finset.mem_coe.1 ha)
            have hb' := mem_filter.1 (Finset.mem_coe.1 hb)
            rw [← Nat.prod_primeFactors_of_squarefree ha'.2,
              ← Nat.prod_primeFactors_of_squarefree hb'.2]
            exact congrArg (fun s ↦ ∏ p ∈ s, p) hab
      _ = 2 ^ q.primeFactors.card := Finset.card_powerset _
      _ = 2 ^ (cardDistinctFactors q) := by rw [cardDistinctFactors_eq_card_primeFactors]
  exact_mod_cast hcard

/-- **NZM, Theorem 8.29.** For `q > 0`, the number of integers `n` with `a < n ≤ a + N` and
`gcd(n, q) = 1` is `(φ(q)/q) N + O(2 ^ ω(q))`; explicitly the error is at most `2 ^ ω(q)`,
uniformly in the integer `a` and the natural number `N`. (Stated in `ℚ`.) -/
@[kb "nivenzuckermanmontgomery" "Thm 8.29, p. 393"]
theorem abs_card_coprime_Ioc_sub_le (q : ℕ) (hq : 0 < q) (a : ℤ) (N : ℕ) :
    |(((Ioc a (a + N)).filter (fun n : ℤ ↦ Nat.Coprime n.natAbs q)).card : ℚ) -
        (q.totient : ℚ) * N / q| ≤ 2 ^ (cardDistinctFactors q) := by
  have hcard : (((Ioc a (a + N)).filter (fun n : ℤ ↦ Nat.Coprime n.natAbs q)).card : ℚ) =
      ∑ d ∈ q.divisors, (μ d : ℚ) *
        (((Ioc a (a + N)).filter (fun n : ℤ ↦ (d : ℤ) ∣ n)).card : ℚ) := by
    calc (((Ioc a (a + N)).filter (fun n : ℤ ↦ Nat.Coprime n.natAbs q)).card : ℚ)
        = ∑ n ∈ Ioc a (a + N), (if Nat.Coprime n.natAbs q then (1 : ℚ) else 0) := by
          rw [Finset.card_filter, Nat.cast_sum]; simp
      _ = ∑ n ∈ Ioc a (a + N), ∑ d ∈ q.divisors.filter (fun d : ℕ ↦ (d : ℤ) ∣ n), (μ d : ℚ) :=
          sum_congr rfl fun n _ ↦ coprime_indicator_eq q hq n
      _ = ∑ n ∈ Ioc a (a + N), ∑ d ∈ q.divisors, if (d : ℤ) ∣ n then (μ d : ℚ) else 0 :=
          sum_congr rfl fun n _ ↦ sum_filter _ _
      _ = ∑ d ∈ q.divisors, ∑ n ∈ Ioc a (a + N), if (d : ℤ) ∣ n then (μ d : ℚ) else 0 :=
          sum_comm
      _ = ∑ d ∈ q.divisors, (μ d : ℚ) *
            (((Ioc a (a + N)).filter (fun n : ℤ ↦ (d : ℤ) ∣ n)).card : ℚ) :=
          sum_congr rfl fun d _ ↦ by
            rw [← sum_filter, sum_const, nsmul_eq_mul]; ring
  have hphi : (q.totient : ℚ) * N / q = ∑ d ∈ q.divisors, (μ d : ℚ) * ((N : ℚ) / d) := by
    have h := totient_div_eq_sum (K := ℚ) q hq
    calc (q.totient : ℚ) * N / q = (N : ℚ) * ((q.totient : ℚ) / q) := by ring
      _ = (N : ℚ) * ∑ d ∈ q.divisors, (μ d : ℚ) / d := by rw [h]
      _ = ∑ d ∈ q.divisors, (μ d : ℚ) * ((N : ℚ) / d) := by
          rw [mul_sum]; exact sum_congr rfl fun d _ ↦ by ring
  rw [hcard, hphi, ← sum_sub_distrib]
  calc |∑ d ∈ q.divisors, ((μ d : ℚ) *
          (((Ioc a (a + N)).filter (fun n : ℤ ↦ (d : ℤ) ∣ n)).card : ℚ) -
          (μ d : ℚ) * ((N : ℚ) / d))|
      ≤ ∑ d ∈ q.divisors, |(μ d : ℚ) *
          (((Ioc a (a + N)).filter (fun n : ℤ ↦ (d : ℤ) ∣ n)).card : ℚ) -
          (μ d : ℚ) * ((N : ℚ) / d)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ q.divisors, |(μ d : ℚ)| := by
        refine sum_le_sum fun d hd ↦ ?_
        rw [← mul_sub, abs_mul]
        have := abs_card_dvd_Ioc_sub a N d (Nat.pos_of_mem_divisors hd)
        calc |(μ d : ℚ)| * |(((Ioc a (a + N)).filter (fun n : ℤ ↦ (d : ℤ) ∣ n)).card : ℚ) -
              (N : ℚ) / d| ≤ |(μ d : ℚ)| * 1 :=
              mul_le_mul_of_nonneg_left this (abs_nonneg _)
          _ = |(μ d : ℚ)| := mul_one _
    _ ≤ 2 ^ (cardDistinctFactors q) := sum_abs_moebius_divisors_le q hq

/-! ## Theorem 8.30 -/

/-- `2 ^ ω(n) ≤ n` (each distinct prime factor is at least `2`; the easy half of the
order-of-magnitude statement of Theorem 8.30). -/
theorem two_pow_cardDistinctFactors_le (n : ℕ) (hn : 0 < n) :
    2 ^ (cardDistinctFactors n) ≤ n := by
  rw [cardDistinctFactors_eq_card_primeFactors]
  calc 2 ^ n.primeFactors.card = ∏ _p ∈ n.primeFactors, 2 := by rw [prod_const]
    _ ≤ ∏ p ∈ n.primeFactors, p :=
        Finset.prod_le_prod (fun p hp ↦ (Nat.prime_of_mem_primeFactors hp).two_le)
    _ ≤ n := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)

/-- **NZM, Theorem 8.30** (not proved here): for every `ε > 0`, `ω(n) < (1 + ε) log n / log log n`
for all large `n`, and `ω(n) > (1 - ε) log n / log log n` for infinitely many `n`. -/
@[kb "nivenzuckermanmontgomery" "Thm 8.30, p. 394"]
def OmegaOrderStatement : Prop :=
  (∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ < n →
      (cardDistinctFactors n : ℝ) < (1 + ε) * Real.log n / Real.log (Real.log n)) ∧
  (∀ ε : ℝ, 0 < ε → {n : ℕ | (1 - ε) * Real.log n / Real.log (Real.log n) <
      (cardDistinctFactors n : ℝ)}.Infinite)

end NTKB.NZM
