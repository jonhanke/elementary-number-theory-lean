/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.Primes.Selberg

/-!
# Selberg's theorem and the remainder inequality (Hardy–Wright, Chapter XXII, §§ 22.14–22.15)

* **Theorem 433** (Selberg's theorem), in both of the book's forms:
  (22.14.2) `ψ(x) log x + ∑_{n ≤ x} Λ(n) ψ(x/n) = 2x log x + O(x)` and
  (22.14.3) `∑_{n ≤ x} Λ(n) log n + ∑_{mn ≤ x} Λ(m) Λ(n) = 2x log x + O(x)`.
  The form (22.14.2) is Apostol's Theorem 4.18 (`NTKB.Apostol.selberg_asymptotic_formula`, proved in
  NTKB through the Tatuzawa–Iseki identity, which is the book's Möbius-inversion argument in another
  arrangement); (22.14.3) follows as in the book, since `∑_{n ≤ x} Λ(n) ψ(x/n) = ∑_{mn ≤ x} Λ(m) Λ(n)`
  and `ψ(x) log x - ∑_{n ≤ x} Λ(n) log n = ∑_{n ≤ x} Λ(n) log(x/n) = O(x)` (22.14.4).
* With `R(x) = ψ(x) - x` (`psiRem`): (22.15.1) `R(x) log x + ∑_{n ≤ x} Λ(n) R(x/n) = O(x)` and
  (22.15.2) `|R(x)| log² x ≤ ∑_{n ≤ x} aₙ |R(x/n)| + O(x log x)`, where
  `aₙ = Λ(n) log n + ∑_{hk = n} Λ(h) Λ(k)` (`selbergCoeff`), with `∑_{n ≤ x} aₙ = 2x log x + O(x)`.

For `x ≥ 1` we write the error terms of (22.15.2) as `O(x (1 + log x))`, which is the book's
`O(x log x)` for `x ≥ 2`.
-/

open Finset ArithmeticFunction Real Chebyshev

namespace NTKB.HardyWright

open NTKB.Apostol

/-- The constant of Mathlib's Chebyshev bound `ψ(x) ≤ (log 4 + 4) x`. -/
theorem psi_le_c (x : ℝ) (hx : 0 ≤ x) : ψ x ≤ (Real.log 4 + 4) * x := psi_le_const_mul_self hx

theorem log_four_add_four_pos : 0 < Real.log 4 + 4 := by
  have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith

/-- The remainder `R(x) = ψ(x) - x` of the prime number theorem (Hardy–Wright, § 22.15). -/
noncomputable def psiRem (x : ℝ) : ℝ := ψ x - x

/-- Selberg's coefficients `aₙ = Λ(n) log n + ∑_{hk = n} Λ(h) Λ(k)` (Hardy–Wright, (22.15.2)). -/
noncomputable def selbergCoeff (n : ℕ) : ℝ := Λ n * Real.log n + (Λ * Λ : ArithmeticFunction ℝ) n

theorem vonMangoldt_mul_vonMangoldt_nonneg (n : ℕ) : 0 ≤ (Λ * Λ : ArithmeticFunction ℝ) n := by
  rw [ArithmeticFunction.mul_apply]
  exact sum_nonneg fun p _ ↦ mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg

theorem selbergCoeff_nonneg (n : ℕ) : 0 ≤ selbergCoeff n :=
  add_nonneg (mul_nonneg vonMangoldt_nonneg (Real.log_natCast_nonneg n))
    (vonMangoldt_mul_vonMangoldt_nonneg n)

/-- `∑_{n ≤ N} Λ(n) ∑_{m ≤ N/n} Λ(m) g(nm) = ∑_{k ≤ N} (Λ * Λ)(k) g(k)`. -/
theorem sum_vonMangoldt_sum_vonMangoldt (g : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, Λ n * ∑ m ∈ Ioc 0 (N / n), Λ m * g (n * m) =
      ∑ k ∈ Ioc 0 N, (Λ * Λ : ArithmeticFunction ℝ) k * g k := by
  have h := sum_Ioc_sum_divisorsAntidiagonal (fun a b ↦ Λ a * Λ b * g (a * b)) N
  calc _ = ∑ a ∈ Ioc 0 N, ∑ b ∈ Ioc 0 (N / a), Λ a * Λ b * g (a * b) := by
        refine sum_congr rfl fun n _ ↦ ?_
        rw [mul_sum]
        exact sum_congr rfl fun m _ ↦ by ring
    _ = _ := by
        rw [← h]
        refine sum_congr rfl fun k _ ↦ ?_
        rw [ArithmeticFunction.mul_apply, sum_mul]
        refine sum_congr rfl fun p hp ↦ ?_
        rw [(Nat.mem_divisorsAntidiagonal.1 hp).1]

/-- `∑_{n ≤ x} Λ(n) ψ(x/n) = ∑_{mn ≤ x} Λ(m) Λ(n)` (Hardy–Wright, § 22.14). -/
theorem sum_vonMangoldt_mul_psi_div (x : ℝ) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * ψ (x / n) =
      ∑ k ∈ Ioc 0 ⌊x⌋₊, (Λ * Λ : ArithmeticFunction ℝ) k := by
  have h := sum_vonMangoldt_sum_vonMangoldt (fun _ ↦ 1) ⌊x⌋₊
  simp only [mul_one] at h
  rw [← h]
  refine sum_congr rfl fun n _ ↦ ?_
  rw [Chebyshev.psi, Nat.floor_div_natCast]

/-- `log(N/n) ≤ ∑_{n ≤ m < N} 1/m` for `1 ≤ n ≤ N`. -/
theorem log_div_le_sum_Ico {n N : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    Real.log ((N : ℝ) / n) ≤ ∑ m ∈ Ico n N, (1 : ℝ) / m := by
  induction N, hnN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    rw [sum_Ico_succ_top hN]
    have hsplit : Real.log (((N + 1 : ℕ) : ℝ) / n) =
        Real.log ((N : ℝ) / n) + Real.log (((N : ℝ) + 1) / N) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1; push_cast; field_simp
    rw [hsplit]
    have : Real.log (((N : ℝ) + 1) / N) ≤ 1 / N := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((N : ℝ) + 1) / N by positivity)
      have : ((N : ℝ) + 1) / N - 1 = 1 / N := by field_simp; ring
      linarith
    linarith

/-- (22.14.4): `0 ≤ ∑_{n ≤ x} Λ(n) log(x/n) ≤ (log 4 + 4)(1 + log 2) x` for `x ≥ 1`. -/
theorem sum_vonMangoldt_mul_log_div_le {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * Real.log (x / n) ∧
      ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * Real.log (x / n) ≤ (Real.log 4 + 4) * (1 + Real.log 2) * x := by
  have hx0 : 0 < x := by linarith
  set N := ⌊x⌋₊ with hN
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxN : x < N + 1 := Nat.lt_floor_add_one x
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hc := log_four_add_four_pos
  set c := Real.log 4 + 4
  constructor
  · refine sum_nonneg fun n hn ↦ mul_nonneg vonMangoldt_nonneg (Real.log_nonneg ?_)
    have hn := mem_Ioc.1 hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
    rw [le_div_iff₀ hn0, one_mul]
    exact (show (n : ℝ) ≤ ⌊x⌋₊ by exact_mod_cast hn.2).trans hNx
  -- split `log(x/n) = log(x/N) + log(N/n)`
  have hsplit : ∀ n ∈ Ioc 0 N, Λ n * Real.log (x / n) =
      Λ n * Real.log (x / N) + Λ n * Real.log ((N : ℝ) / n) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Ioc.1 hn).1
    rw [← mul_add, ← Real.log_mul (by positivity) (by positivity)]
    congr 2; field_simp
  rw [sum_congr rfl hsplit, sum_add_distrib, ← sum_mul]
  have h1 : (∑ n ∈ Ioc 0 N, Λ n) * Real.log (x / N) ≤ c * x * Real.log 2 := by
    have hψ : ∑ n ∈ Ioc 0 N, Λ n = ψ x := rfl
    rw [hψ]
    have hl0 : 0 ≤ Real.log (x / N) := Real.log_nonneg (by rw [le_div_iff₀ hN0]; linarith)
    have hl2 : Real.log (x / N) ≤ Real.log 2 := by
      apply Real.log_le_log (by positivity)
      rw [div_le_iff₀ hN0]
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
      linarith
    exact mul_le_mul (psi_le_c x hx0.le) hl2 hl0 (by positivity)
  -- `∑_{n ≤ N} Λ(n) log(N/n) ≤ ∑_{m < N} ψ(m)/m ≤ c N`
  have h2 : ∑ n ∈ Ioc 0 N, Λ n * Real.log ((N : ℝ) / n) ≤ c * x := by
    calc ∑ n ∈ Ioc 0 N, Λ n * Real.log ((N : ℝ) / n)
        ≤ ∑ n ∈ Ioc 0 N, ∑ m ∈ Ico n N, Λ n * (1 / m) := by
          refine sum_le_sum fun n hn ↦ ?_
          have hn := mem_Ioc.1 hn
          rw [← mul_sum]
          exact mul_le_mul_of_nonneg_left (log_div_le_sum_Ico hn.1 hn.2) vonMangoldt_nonneg
      _ = ∑ m ∈ Ico 1 N, ∑ n ∈ Ioc 0 m, Λ n * (1 / m) := by
          refine sum_comm' fun n m ↦ ?_
          simp only [mem_Ioc, mem_Ico]
          omega
      _ = ∑ m ∈ Ico 1 N, ψ m * (1 / m) := by
          refine sum_congr rfl fun m _ ↦ ?_
          rw [← sum_mul, Chebyshev.psi, Nat.floor_natCast]
      _ ≤ ∑ m ∈ Ico 1 N, c := by
          refine sum_le_sum fun m hm ↦ ?_
          have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by simp at hm; omega)
          rw [mul_one_div, div_le_iff₀ hm0]
          exact psi_le_c m hm0.le
      _ ≤ c * x := by
          rw [sum_const, Nat.card_Ico, nsmul_eq_mul, mul_comm]
          refine mul_le_mul_of_nonneg_left ?_ hc.le
          have : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
          linarith
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith

/-- `ψ(x) log x = ∑_{n ≤ x} Λ(n) log n + ∑_{n ≤ x} Λ(n) log(x/n)` for `x > 0`. -/
theorem psi_mul_log_eq {x : ℝ} (hx0 : 0 < x) :
    ψ x * Real.log x = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * Real.log n +
      ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * Real.log (x / n) := by
  rw [← sum_add_distrib, Chebyshev.psi, sum_mul]
  refine sum_congr rfl fun n hn ↦ ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Ioc.1 hn).1
  rw [← mul_add, ← Real.log_mul hn0.ne' (by positivity), mul_div_cancel₀ _ hn0.ne']

/-- `∑_{n ≤ x} aₙ = ∑_{n ≤ x} Λ(n) log n + ∑_{n ≤ x} (Λ * Λ)(n)`. -/
theorem sum_selbergCoeff_eq (x : ℝ) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, selbergCoeff n = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * Real.log n +
      ∑ n ∈ Ioc 0 ⌊x⌋₊, (Λ * Λ : ArithmeticFunction ℝ) n := by
  rw [← sum_add_distrib]; rfl

/-- **Theorem 433** (Selberg's theorem), form (22.14.2):
`ψ(x) log x + ∑_{n ≤ x} Λ(n) ψ(x/n) = 2x log x + O(x)`. -/
@[kb "hardywright2008" "Thm 433, p. 497"]
theorem selberg_theorem :
    ∃ K, ∀ x : ℝ, 1 ≤ x →
      |ψ x * Real.log x + ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * ψ (x / n) - 2 * x * Real.log x| ≤ K * x :=
  selberg_asymptotic_formula

/-- **Theorem 433** (Selberg's theorem), form (22.14.3):
`∑_{n ≤ x} Λ(n) log n + ∑_{mn ≤ x} Λ(m) Λ(n) = 2x log x + O(x)`, i.e. `∑_{n ≤ x} aₙ = 2x log x + O(x)`
with `aₙ = Λ(n) log n + ∑_{hk = n} Λ(h) Λ(k)`. -/
@[kb "hardywright2008" "Thm 433, p. 497"]
theorem selberg_theorem' :
    ∃ K, ∀ x : ℝ, 1 ≤ x →
      |∑ n ∈ Ioc 0 ⌊x⌋₊, selbergCoeff n - 2 * x * Real.log x| ≤ K * x := by
  obtain ⟨K, hK⟩ := selberg_asymptotic_formula
  refine ⟨K + (Real.log 4 + 4) * (1 + Real.log 2), fun x hx ↦ ?_⟩
  obtain ⟨h0, h1⟩ := sum_vonMangoldt_mul_log_div_le hx
  have hx0 : 0 < x := by linarith
  have hsplit := psi_mul_log_eq hx0
  have hS : ∑ n ∈ Ioc 0 ⌊x⌋₊, selbergCoeff n = ψ x * Real.log x -
      ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * Real.log (x / n) + ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * ψ (x / n) := by
    rw [hsplit, sum_vonMangoldt_mul_psi_div, sum_selbergCoeff_eq]
    ring
  rw [hS]
  have := hK x hx
  rw [abs_le] at this ⊢
  constructor <;> nlinarith

/-- (22.15.1): `R(x) log x + ∑_{n ≤ x} Λ(n) R(x/n) = O(x)` for `x ≥ 1`. -/
@[kb "hardywright2008" "(22.15.1), p. 501"]
theorem psiRem_log_add_sum :
    ∃ K, ∀ x : ℝ, 1 ≤ x →
      |psiRem x * Real.log x + ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * psiRem (x / n)| ≤ K * x := by
  obtain ⟨K, hK⟩ := selberg_asymptotic_formula
  obtain ⟨⟨M, hM⟩, -, -⟩ := apostol_thm_4_9
  refine ⟨K + |M|, fun x hx ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  have h : psiRem x * Real.log x + ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * psiRem (x / n) =
      (ψ x * Real.log x + ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * ψ (x / n) - 2 * x * Real.log x) -
        x * (∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n - Real.log x) := by
    simp only [psiRem, mul_sub, sum_sub_distrib, mul_sum]
    have : ∑ i ∈ Ioc 0 ⌊x⌋₊, Λ i * (x / i) = ∑ i ∈ Ioc 0 ⌊x⌋₊, x * (Λ i / i) :=
      sum_congr rfl fun i _ ↦ by ring
    rw [this]
    ring
  rw [h]
  have h1 := hK x hx
  have h2 : |x * (∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n - Real.log x)| ≤ |M| * x := by
    rw [abs_mul, abs_of_pos hx0, mul_comm]
    exact mul_le_mul_of_nonneg_right ((hM x hx).trans (le_abs_self M)) hx0.le
  calc _ ≤ |ψ x * Real.log x + ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * ψ (x / n) - 2 * x * Real.log x| +
        |x * (∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n - Real.log x)| := abs_sub _ _
    _ ≤ K * x + |M| * x := add_le_add h1 h2
    _ = (K + |M|) * x := by ring

/-- (22.15.2): `|R(x)| log² x ≤ ∑_{n ≤ x} aₙ |R(x/n)| + O(x log x)` (here `O(x (1 + log x))`,
`x ≥ 1`). -/
@[kb "hardywright2008" "(22.15.2), p. 501"]
theorem abs_psiRem_mul_log_sq_le :
    ∃ K, ∀ x : ℝ, 1 ≤ x →
      |psiRem x| * Real.log x ^ 2 ≤
        ∑ n ∈ Ioc 0 ⌊x⌋₊, selbergCoeff n * |psiRem (x / n)| + K * x * (1 + Real.log x) := by
  obtain ⟨K, hK⟩ := psiRem_log_add_sum
  obtain ⟨⟨M, hM⟩, -, -⟩ := apostol_thm_4_9
  have hK0 : 0 ≤ K := by
    have := (abs_nonneg _).trans (hK 1 le_rfl); linarith
  refine ⟨K * (1 + |M|) + K, fun x hx ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  set E : ℝ → ℝ := fun y ↦ psiRem y * Real.log y + ∑ m ∈ Ioc 0 ⌊y⌋₊, Λ m * psiRem (y / m)
    with hE
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx
  -- the double sum
  have hdouble : ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * ∑ m ∈ Ioc 0 ⌊x / n⌋₊, Λ m * psiRem (x / n / m) =
      ∑ k ∈ Ioc 0 ⌊x⌋₊, (Λ * Λ : ArithmeticFunction ℝ) k * psiRem (x / k) := by
    rw [← sum_vonMangoldt_sum_vonMangoldt (fun k ↦ psiRem (x / k)) ⌊x⌋₊]
    refine sum_congr rfl fun n _ ↦ ?_
    rw [Nat.floor_div_natCast]
    congr 1
    refine sum_congr rfl fun m _ ↦ ?_
    rw [Nat.cast_mul, div_div]
  -- the identity `R(x) log² x = log x E(x) - ∑ Λ(n) E(x/n) - ∑ Λ(n) log n R(x/n) + ∑ (Λ*Λ) R`
  have hid : psiRem x * Real.log x ^ 2 = Real.log x * E x - ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * E (x / n) -
      ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * Real.log n * psiRem (x / n) +
      ∑ k ∈ Ioc 0 ⌊x⌋₊, (Λ * Λ : ArithmeticFunction ℝ) k * psiRem (x / k) := by
    rw [← hdouble]
    simp only [hE, mul_add, sum_add_distrib]
    have : ∀ n ∈ Ioc 0 ⌊x⌋₊, Λ n * (psiRem (x / n) * Real.log (x / n)) =
        Λ n * psiRem (x / n) * Real.log x - Λ n * Real.log n * psiRem (x / n) := by
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Ioc.1 hn).1
      rw [Real.log_div hx0.ne' hn0.ne']; ring
    rw [sum_congr rfl this, sum_sub_distrib, ← sum_mul]
    ring
  -- bounds on the error terms
  have hEx : |Real.log x * E x| ≤ K * x * Real.log x := by
    rw [abs_mul, abs_of_nonneg hl0]
    have := hK x hx
    nlinarith
  have hEn : |∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * E (x / n)| ≤ K * x * (Real.log x + |M|) := by
    calc |∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * E (x / n)| ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, |Λ n * E (x / n)| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * (K * (x / n)) := by
          refine sum_le_sum fun n hn ↦ ?_
          have hn := mem_Ioc.1 hn
          have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
          have hxn : 1 ≤ x / n := by
            rw [le_div_iff₀ hn0, one_mul]
            exact (show (n : ℝ) ≤ ⌊x⌋₊ by exact_mod_cast hn.2).trans (Nat.floor_le hx0.le)
          rw [abs_mul, abs_of_nonneg vonMangoldt_nonneg]
          exact mul_le_mul_of_nonneg_left (hK _ hxn) vonMangoldt_nonneg
      _ = K * x * ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n := by
          rw [mul_sum]; exact sum_congr rfl fun n _ ↦ by ring
      _ ≤ K * x * (Real.log x + |M|) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have := (abs_le.1 (hM x hx)).2
          have := le_abs_self M
          linarith
  have hmain : |-(∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * Real.log n * psiRem (x / n)) +
      ∑ k ∈ Ioc 0 ⌊x⌋₊, (Λ * Λ : ArithmeticFunction ℝ) k * psiRem (x / k)| ≤
      ∑ n ∈ Ioc 0 ⌊x⌋₊, selbergCoeff n * |psiRem (x / n)| := by
    rw [← sum_neg_distrib, ← sum_add_distrib]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n _ ↦ ?_)
    have h1 : 0 ≤ Λ n * Real.log n := mul_nonneg vonMangoldt_nonneg (Real.log_natCast_nonneg n)
    have h2 := vonMangoldt_mul_vonMangoldt_nonneg n
    calc |-(Λ n * Real.log n * psiRem (x / n)) +
          (Λ * Λ : ArithmeticFunction ℝ) n * psiRem (x / n)|
        ≤ |-(Λ n * Real.log n * psiRem (x / n))| +
          |(Λ * Λ : ArithmeticFunction ℝ) n * psiRem (x / n)| := abs_add_le _ _
      _ = selbergCoeff n * |psiRem (x / n)| := by
          rw [abs_neg, abs_mul (Λ n * Real.log n), abs_mul ((Λ * Λ : ArithmeticFunction ℝ) n),
            abs_of_nonneg h1, abs_of_nonneg h2, selbergCoeff]
          ring
  have habs : |psiRem x| * Real.log x ^ 2 = |psiRem x * Real.log x ^ 2| := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg (Real.log x))]
  rw [habs, hid]
  have hM0 := abs_nonneg M
  calc |Real.log x * E x - ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * E (x / n) -
        ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * Real.log n * psiRem (x / n) +
        ∑ k ∈ Ioc 0 ⌊x⌋₊, (Λ * Λ : ArithmeticFunction ℝ) k * psiRem (x / k)|
      = |Real.log x * E x - ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * E (x / n) +
        (-(∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * Real.log n * psiRem (x / n)) +
        ∑ k ∈ Ioc 0 ⌊x⌋₊, (Λ * Λ : ArithmeticFunction ℝ) k * psiRem (x / k))| := by ring_nf
    _ ≤ |Real.log x * E x| + |∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * E (x / n)| +
        ∑ n ∈ Ioc 0 ⌊x⌋₊, selbergCoeff n * |psiRem (x / n)| := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans le_rfl) hmain)
    _ ≤ K * x * Real.log x + K * x * (Real.log x + |M|) +
        ∑ n ∈ Ioc 0 ⌊x⌋₊, selbergCoeff n * |psiRem (x / n)| := by gcongr
    _ ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, selbergCoeff n * |psiRem (x / n)| +
        (K * (1 + |M|) + K) * x * (1 + Real.log x) := by
        nlinarith [mul_nonneg hK0 hx0.le, mul_nonneg (mul_nonneg hK0 hx0.le) hl0,
          mul_nonneg (mul_nonneg hK0 hx0.le) hM0,
          mul_nonneg (mul_nonneg (mul_nonneg hK0 hx0.le) hM0) hl0]

end NTKB.HardyWright
