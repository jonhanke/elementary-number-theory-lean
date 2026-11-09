/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.ArithmeticFunctions.Inversion
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Normed.Field.Instances

/-!
# Hardy–Wright, § 17.10: Lambert series

* `hasSum_lambert` (the rearrangement of Theorem 307): for `|a(n)| ≤ n` and `|x| < 1`,
  `∑ a(n) xⁿ/(1 - xⁿ) = ∑_N b(N) x^N`, `b(N) = ∑_{n ∣ N} a(n)`.
* Theorem 308: `∑ μ(n) xⁿ/(1 - xⁿ) = x`.
* Theorem 309: `∑ φ(n) xⁿ/(1 - xⁿ) = x/(1 - x)²`.

(The book deduces Theorems 308 and 309 from Theorem 307 and the Dirichlet series of `μ` and `φ`;
here directly from `∑_{d ∣ N} μ(d) = [N = 1]` and `∑_{d ∣ N} φ(d) = N`, the coefficient identities
behind those Dirichlet series.)
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace NTKB.HardyWright

/-- `∑_{m ≥ 1} y^m = y/(1-y)` for `|y| < 1`. -/
lemma hasSum_pnat_geometric {y : ℝ} (hy : |y| < 1) :
    HasSum (fun m : ℕ+ => y ^ (m : ℕ)) (y / (1 - y)) := by
  rw [hasSum_pnat_iff_hasSum_succ]
  have h := (hasSum_geometric_of_abs_lt_one hy).mul_left y
  rw [div_eq_mul_inv]
  exact h.congr_fun fun n => by simp [pow_succ, mul_comm]

/-- The rearrangement behind Theorem 307: for `|a(n)| ≤ n` and `|x| < 1`,
`∑ a(n) x^n/(1-x^n) = ∑_N (∑_{n ∣ N} a(n)) x^N`. -/
theorem hasSum_lambert {a : ℕ → ℝ} (ha : ∀ n, |a n| ≤ n) {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ+ => a n * x ^ (n : ℕ) / (1 - x ^ (n : ℕ)))
      (∑' N : ℕ+, (∑ d ∈ (N : ℕ).divisors, a d) * x ^ (N : ℕ)) := by
  set H : ℕ → ℕ → ℝ := fun n m => a n * x ^ (n * m) with hH
  have hsum : Summable fun c : ℕ+ × ℕ+ => H c.1 c.2 := by
    have h := summable_prod_mul_pow (𝕜 := ℝ) 1 (r := |x|) (by rwa [Real.norm_eq_abs, abs_abs])
    have h' : Summable fun c : ℕ+ × ℕ+ => ((c.1 : ℕ) : ℝ) * |x| ^ ((c.1 : ℕ) * (c.2 : ℕ)) := by
      have := (Equiv.prodComm ℕ+ ℕ+).summable_iff.mpr h
      refine this.congr fun c => ?_
      simp [mul_comm]
    refine Summable.of_norm_bounded h' fun c => ?_
    simp only [hH, Real.norm_eq_abs, abs_mul, abs_pow]
    gcongr
    exact ha _
  have h1 : ∀ n : ℕ+, a n * x ^ (n : ℕ) / (1 - x ^ (n : ℕ)) = ∑' m : ℕ+, H n m := by
    intro n
    have hxn : |x ^ (n : ℕ)| < 1 := by
      rw [abs_pow]; exact pow_lt_one₀ (abs_nonneg x) hx n.ne_zero
    rw [mul_div_assoc, ← (hasSum_pnat_geometric hxn).tsum_eq, ← tsum_mul_left]
    refine tsum_congr fun m => ?_
    simp only [hH, pow_mul]
  have hsum1 : Summable fun n : ℕ+ => ∑' m : ℕ+, H n m := hsum.prod
  rw [show (fun n : ℕ+ => a n * x ^ (n : ℕ) / (1 - x ^ (n : ℕ))) =
    fun n : ℕ+ => ∑' m : ℕ+, H n m from funext h1]
  have e : ∑' N : ℕ+, (∑ d ∈ (N : ℕ).divisors, a d) * x ^ (N : ℕ) =
      ∑' k : ℕ+, ∑ y ∈ (k : ℕ).divisorsAntidiagonal, H y.1 y.2 := by
    refine tsum_congr fun N => ?_
    rw [Nat.sum_divisorsAntidiagonal (fun i j => H i j), sum_mul]
    refine sum_congr rfl fun d hd => ?_
    simp only [hH, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
  rw [e, ← tsum_pnat_prod_eq_tsum_divisorsAntidiagonal H hsum, hsum.tsum_prod]
  exact hsum1.hasSum

/-- **Theorem 308** (Hardy–Wright). `∑_{n ≥ 1} μ(n) xⁿ/(1 - xⁿ) = x` (for `|x| < 1`). -/
@[kb "hardywright2008" "Thm 308, p. 359"]
theorem hasSum_moebius_lambert {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ+ => (μ n : ℝ) * x ^ (n : ℕ) / (1 - x ^ (n : ℕ))) x := by
  have h := hasSum_lambert (a := fun n => (μ n : ℝ)) (fun n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have : |(μ n : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs, abs_moebius]; split_ifs <;> norm_num
    exact this.trans (by exact_mod_cast hn)) hx
  convert h using 1
  have e : ∀ N : ℕ+, (∑ d ∈ (N : ℕ).divisors, (μ d : ℝ)) * x ^ (N : ℕ) =
      if N = 1 then x else 0 := by
    intro N
    have := congrArg (fun z : ℤ => (z : ℝ)) (sum_divisors_moebius N)
    push_cast at this
    rw [this]
    by_cases hN : N = 1
    · subst hN; simp
    · have : (N : ℕ) ≠ 1 := fun h => hN (PNat.coe_eq_one_iff.mp h)
      simp [hN, this]
  rw [tsum_congr e, tsum_ite_eq]

/-- **Theorem 309** (Hardy–Wright). `∑_{n ≥ 1} φ(n) xⁿ/(1 - xⁿ) = x/(1 - x)²` (for `|x| < 1`). -/
@[kb "hardywright2008" "Thm 309, p. 359"]
theorem hasSum_totient_lambert {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ+ => ((n : ℕ).totient : ℝ) * x ^ (n : ℕ) / (1 - x ^ (n : ℕ)))
      (x / (1 - x) ^ 2) := by
  have h := hasSum_lambert (a := fun n => (n.totient : ℝ)) (fun n => by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact_mod_cast Nat.totient_le n) hx
  convert h using 1
  have e : ∀ N : ℕ+, (∑ d ∈ (N : ℕ).divisors, (d.totient : ℝ)) * x ^ (N : ℕ) =
      ((N : ℕ) : ℝ) * x ^ (N : ℕ) := by
    intro N
    rw [← Nat.cast_sum, Nat.sum_totient]
  rw [tsum_congr e]
  have hg := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := x) (by rwa [Real.norm_eq_abs])
  rw [← hasSum_nat_add_iff' 1] at hg
  simp only [range_one, sum_singleton, Nat.cast_zero, zero_mul, sub_zero] at hg
  have hp : HasSum (fun N : ℕ+ => ((N : ℕ) : ℝ) * x ^ (N : ℕ)) (x / (1 - x) ^ 2) :=
    (hasSum_pnat_iff_hasSum_succ (f := fun N : ℕ => (N : ℝ) * x ^ N)).mpr hg
  exact hp.tsum_eq.symm

end NTKB.HardyWright
