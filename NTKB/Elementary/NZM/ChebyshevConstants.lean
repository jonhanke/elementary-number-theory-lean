/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.PrimeDistribution.ElementaryPNT
import NTKB.Analytic.Apostol.Primes.MertensSecond
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import NTKB.Attr

/-!
# Chebyshev's constants and the average of `ω` (Niven–Zuckerman–Montgomery, Chapter 8)

* **Theorem 8.3** (`chebyshev_psi_bounds`).  With Chebyshev's constants
  `a₀ = (1/3) log 2 + (1/2) log 3 = 0.780355...` and `b₀ = (3/2) a₀ = 1.170533...`,
  for `a < a₀` and `b > b₀` we have `a x < ψ(x) < b x` for all large `x`.  Here this is deduced
  from the prime number theorem `ψ(x) / x → 1` (since `a₀ < 1 < b₀`), rather than by
  Chebyshev's elementary method.
* **Corollary 8.6** (`chebyshev_primeCounting_bounds`).  Likewise
  `a x / log x < π(x) < b x / log x` for all large `x`, deduced from the prime number theorem.
* **Theorem 8.26** (`sum_cardDistinctFactors_sub_isBigO`).  There are constants `b` (Mertens'
  constant, the same as in `NTKB.Apostol.apostol_thm_4_12`) and `C` with
  `|∑_{n ≤ x} ω(n) - x log log x - b x| ≤ C x / log x` for `x ≥ 5`.
-/

open Finset ArithmeticFunction Filter
open scoped Topology ArithmeticFunction.omega

namespace NTKB.NZM

/-! ## Theorem 8.3 and Corollary 8.6 -/

/-- Chebyshev's lower constant of the book, `a₀ = (1/3) log 2 + (1/2) log 3 = 0.780355…`. -/
noncomputable def chebyshevA : ℝ := (1 / 3) * Real.log 2 + (1 / 2) * Real.log 3

/-- Chebyshev's upper constant of the book, `b₀ = (3/2) a₀ = 1.170533…`. -/
noncomputable def chebyshevB : ℝ := (3 / 2) * chebyshevA

lemma chebyshevA_bounds : 2 / 3 < chebyshevA ∧ chebyshevA < 1 := by
  have h2l := Real.log_two_gt_d9
  have h2u := Real.log_two_lt_d9
  have h3 : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have u1 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 / 2 by norm_num)
  have l1 := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 3 / 2 by norm_num)
  norm_num at u1 l1 h2l h2u
  unfold chebyshevA
  rw [h3]
  constructor <;> linarith

/-- **Theorem 8.3** (Chebyshev).  For `a < a₀ = (1/3) log 2 + (1/2) log 3` and
`b > b₀ = (3/2) a₀` we have `a x < ψ(x) < b x` for all large `x`.  Deduced here from the prime
number theorem `ψ(x)/x → 1` rather than by Chebyshev's method. -/
@[kb "nivenzuckermanmontgomery" "Thm 8.3, p. 364"]
theorem chebyshev_psi_bounds {a b : ℝ} (ha : a < chebyshevA) (hb : chebyshevB < b) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ < x → a * x < Chebyshev.psi x ∧ Chebyshev.psi x < b * x := by
  obtain ⟨h1, h2⟩ := chebyshevA_bounds
  have hB : 1 < chebyshevB := by unfold chebyshevB; linarith
  have h := NTKB.HardyWright.tendsto_psi_div_self
  have e1 := h.eventually (lt_mem_nhds (show a < 1 by linarith))
  have e2 := h.eventually (gt_mem_nhds (show 1 < b by linarith))
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 ((e1.and e2).and (eventually_gt_atTop 0))
  refine ⟨max x₀ 0, fun x hx ↦ ?_⟩
  obtain ⟨⟨k1, k2⟩, k3⟩ := hx₀ x (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hx))
  rw [lt_div_iff₀ k3] at k1
  rw [div_lt_iff₀ k3] at k2
  exact ⟨k1, k2⟩

/-- **Corollary 8.6.**  For `a < a₀` and `b > b₀`, `a x / log x < π(x) < b x / log x` for all
large `x`.  Deduced here from the prime number theorem. -/
@[kb "nivenzuckermanmontgomery" "Cor 8.6, p. 366"]
theorem chebyshev_primeCounting_bounds {a b : ℝ} (ha : a < chebyshevA) (hb : chebyshevB < b) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ < x →
      a * x / Real.log x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧
        (Nat.primeCounting ⌊x⌋₊ : ℝ) < b * x / Real.log x := by
  obtain ⟨h1, h2⟩ := chebyshevA_bounds
  have hB : 1 < chebyshevB := by unfold chebyshevB; linarith
  have h := NTKB.HardyWright.prime_number_theorem
  have e1 := h.eventually (lt_mem_nhds (show a < 1 by linarith))
  have e2 := h.eventually (gt_mem_nhds (show 1 < b by linarith))
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 ((e1.and e2).and (eventually_gt_atTop 1))
  refine ⟨max x₀ 1, fun x hx ↦ ?_⟩
  obtain ⟨⟨k1, k2⟩, k3⟩ := hx₀ x (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hx))
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos k3
  rw [lt_div_iff₀ hx0] at k1
  rw [div_lt_iff₀ hx0] at k2
  constructor
  · rw [div_lt_iff₀ hl]; linarith
  · rw [lt_div_iff₀ hl]; linarith

/-! ## Theorem 8.26 -/

private abbrev primesLE (N : ℕ) : Finset ℕ := (Ioc 0 N).filter Nat.Prime

private lemma card_primesLE (N : ℕ) : (primesLE N).card = Nat.primeCounting N := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  congr 1
  ext p
  simp only [mem_filter, mem_Ioc, mem_range]
  constructor
  · rintro ⟨h, hp⟩; exact ⟨by omega, hp⟩
  · rintro ⟨h, hp⟩; exact ⟨⟨hp.pos, by omega⟩, hp⟩

private lemma omega_eq_sum {N n : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    ω n = ∑ p ∈ primesLE N, if p ∣ n then 1 else 0 := by
  rw [cardDistinctFactors_eq_card_primeFactors, ← Finset.card_filter]
  congr 1
  ext p
  simp only [Nat.mem_primeFactors, mem_filter, mem_Ioc]
  constructor
  · rintro ⟨hp, hpn, -⟩
    exact ⟨⟨⟨hp.pos, (Nat.le_of_dvd hn hpn).trans hnN⟩, hp⟩, hpn⟩
  · rintro ⟨⟨-, hp⟩, hpn⟩
    exact ⟨hp, hpn, hn.ne'⟩

private lemma sum_omega_eq (N : ℕ) :
    ∑ n ∈ Ioc 0 N, ω n = ∑ p ∈ primesLE N, N / p := by
  rw [Finset.sum_congr rfl fun n hn ↦
    omega_eq_sum (N := N) (mem_Ioc.1 hn).1 (mem_Ioc.1 hn).2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [← Nat.Ioc_filter_dvd_card_eq_div, Finset.card_filter]

private lemma cast_div_eq_floor (x : ℝ) (q : ℕ) :
    (((⌊x⌋₊ / q : ℕ)) : ℝ) = (⌊x / (q : ℝ)⌋₊ : ℝ) := by
  rw [Nat.floor_div_natCast]

private lemma sum_floor_bounds {x : ℝ} (hx : 0 ≤ x) :
    x * ∑ p ∈ primesLE ⌊x⌋₊, (1 : ℝ) / p - Nat.primeCounting ⌊x⌋₊ ≤
        ∑ p ∈ primesLE ⌊x⌋₊, (((⌊x⌋₊ / p : ℕ)) : ℝ) ∧
      ∑ p ∈ primesLE ⌊x⌋₊, (((⌊x⌋₊ / p : ℕ)) : ℝ) ≤ x * ∑ p ∈ primesLE ⌊x⌋₊, (1 : ℝ) / p := by
  have hp : ∀ p ∈ primesLE ⌊x⌋₊, 0 < (p : ℝ) := fun p hp ↦
    Nat.cast_pos.2 (Nat.Prime.pos (mem_filter.1 hp).2)
  constructor
  · have h1 : ∑ p ∈ primesLE ⌊x⌋₊, (x * (1 / (p : ℝ)) - 1) ≤
        ∑ p ∈ primesLE ⌊x⌋₊, (((⌊x⌋₊ / p : ℕ)) : ℝ) := by
      refine Finset.sum_le_sum fun p hpp ↦ ?_
      rw [cast_div_eq_floor]
      have := Nat.lt_floor_add_one (x / p)
      have e : x * (1 / (p : ℝ)) = x / p := by ring
      rw [e]; linarith
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, card_primesLE,
      nsmul_eq_mul, mul_one] at h1
    exact h1
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun p hpp ↦ ?_
    rw [cast_div_eq_floor]
    have := Nat.floor_le (div_nonneg hx (hp p hpp).le)
    calc _ ≤ x / p := this
      _ = x * (1 / p) := by ring

/-- Chebyshev-type upper bound `π(x) ≤ K x / log x` for `x ≥ 2` (from the prime number
theorem). -/
private lemma primeCounting_le_mul : ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x →
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ K * (x / Real.log x) := by
  have h := NTKB.HardyWright.prime_number_theorem
  have e1 := h.eventually (gt_mem_nhds (show (1 : ℝ) < 2 by norm_num))
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 (e1.and (eventually_ge_atTop 2))
  refine ⟨max 2 (Real.log x₀), fun x hx ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hxl : 0 < x / Real.log x := div_pos hx0 hl
  by_cases hxx : x₀ ≤ x
  · obtain ⟨k1, -⟩ := hx₀ x hxx
    rw [div_lt_iff₀ hx0] at k1
    calc (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ 2 * (x / Real.log x) := by
          rw [mul_div_assoc', le_div_iff₀ hl]; linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hxl.le
  · push_neg at hxx
    have hπ : (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ x := by
      rw [← card_primesLE]
      have : (primesLE ⌊x⌋₊).card ≤ (Ioc 0 ⌊x⌋₊).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      have h2 : ((Ioc 0 ⌊x⌋₊).card : ℝ) ≤ ⌊x⌋₊ := by simp
      exact (Nat.cast_le.2 this).trans (h2.trans (Nat.floor_le hx0.le))
    have hlog : Real.log x ≤ Real.log x₀ := Real.log_le_log hx0 hxx.le
    calc (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ x := hπ
      _ = Real.log x * (x / Real.log x) := by field_simp
      _ ≤ Real.log x₀ * (x / Real.log x) := mul_le_mul_of_nonneg_right hlog hxl.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hxl.le

/-- **Theorem 8.26.**  There are constants `b` and `C` such that
`|∑_{n ≤ x} ω(n) - x log log x - b x| ≤ C x / log x` for `x ≥ 5`.  The constant `b` is the
constant of Mertens' estimate `NTKB.Apostol.apostol_thm_4_12`
(`∑_{p ≤ x} 1/p = log log x + b + O(1/log x)`; in the book `b = B₁ / A`), as the first
conjunct records. -/
@[kb "nivenzuckermanmontgomery" "Thm 8.26, p. 391"]
theorem sum_cardDistinctFactors_sub_isBigO :
    ∃ b C : ℝ,
      (∀ x : ℝ, 2 ≤ x →
        |∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 : ℝ) / p - Real.log (Real.log x) - b| ≤
          C / Real.log x) ∧
      ∀ x : ℝ, 5 ≤ x →
        |(∑ n ∈ Ioc 0 ⌊x⌋₊, (ω n : ℝ)) - x * Real.log (Real.log x) - b * x| ≤
          C * (x / Real.log x) := by
  obtain ⟨A, C₁, hA⟩ := NTKB.Apostol.apostol_thm_4_12
  obtain ⟨K, hK⟩ := primeCounting_le_mul
  refine ⟨A, max C₁ 0 + max K 0, fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · have hl : 0 < Real.log x := Real.log_pos (by linarith)
    refine (hA x hx).trans ?_
    gcongr
    linarith [le_max_left C₁ 0, le_max_right K 0]
  · have hx2 : (2 : ℝ) ≤ x := by linarith
    have hx0 : 0 < x := by linarith
    have hl : 0 < Real.log x := Real.log_pos (by linarith)
    have hxl : 0 < x / Real.log x := div_pos hx0 hl
    have hm := hA x hx2
    have hπ := hK x hx2
    obtain ⟨b1, b2⟩ := sum_floor_bounds hx0.le
    have e : ∑ n ∈ Ioc 0 ⌊x⌋₊, (ω n : ℝ) =
        ∑ p ∈ primesLE ⌊x⌋₊, (((⌊x⌋₊ / p : ℕ)) : ℝ) := by
      rw [← Nat.cast_sum, sum_omega_eq, Nat.cast_sum]
    rw [e]
    have hm' : |x * (∑ p ∈ primesLE ⌊x⌋₊, (1 : ℝ) / p - Real.log (Real.log x) - A)| ≤
        C₁ * (x / Real.log x) := by
      rw [abs_mul, abs_of_pos hx0]
      calc x * |_| ≤ x * (C₁ / Real.log x) := mul_le_mul_of_nonneg_left hm hx0.le
        _ = _ := by ring
    have hm'' := abs_le.1 hm'
    have hC1 : C₁ * (x / Real.log x) ≤ max C₁ 0 * (x / Real.log x) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hxl.le
    have hK1 : K * (x / Real.log x) ≤ max K 0 * (x / Real.log x) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hxl.le
    rw [abs_le]
    constructor <;> nlinarith [hm''.1, hm''.2]
