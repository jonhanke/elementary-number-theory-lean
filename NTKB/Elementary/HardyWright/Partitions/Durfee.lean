/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.Partitions.EulerIdentities

/-!
# Hardy–Wright, § 19.7: Theorem 351

[hardywright2008, § 19.7, Theorem 351] (Euler). For `‖x‖ < 1`,
`1/((1 - x)(1 - x²)(1 - x³)⋯) = 1 + x/(1 - x)² + x⁴/((1 - x)²(1 - x²)²) + x⁹/(⋯)² + ⋯`.

The book's proof reads the coefficient of `x^n` on the right as the number of partitions of `n`
with a Durfee square of `i²` nodes. We give the generating-function form of the same count:
the coefficient of `t^n` in `∏_{k < 2n} (1 + x^k t) = ∏_{k < n} (1 + x^k t) ∏_{k < n} (1 + x^k (x^n t))`,
expanded by the `q`-binomial theorem (Theorem 348, Apostol's `qbinomial_theorem`), gives the
finite identity `[2n, n] = ∑_{i ≤ n} x^{i²} [n, i]²` (the Durfee decomposition of the partitions
in an `n × n` box), and `n → ∞` (Tannery's theorem, with `[n, i] → 1/((1 - x)⋯(1 - x^i))` and
`[2n, n] → 1/∏ (1 - x^k)`) gives Theorem 351.
-/

open Complex Finset Filter NTKB.Apostol Polynomial
open scoped Topology

namespace NTKB.HardyWright

namespace Durfee

variable {x : ℂ}

/-- The polynomial `∑_{j ≤ N} x^{j(j-1)/2} [N, j] w_j T^j`. -/
noncomputable def qPoly (x : ℂ) (N : ℕ) (w : ℕ → ℂ) : ℂ[X] :=
  ∑ j ∈ range (N + 1), C (x ^ (j.choose 2) * qBinom x N j * w j) * X ^ j

lemma eval_qPoly (x t : ℂ) (N : ℕ) (w : ℕ → ℂ) :
    (qPoly x N w).eval t =
      ∑ j ∈ range (N + 1), x ^ (j.choose 2) * qBinom x N j * w j * t ^ j := by
  simp [qPoly, eval_finsetSum]

lemma coeff_qPoly (x : ℂ) {N j : ℕ} (hj : j ≤ N) (w : ℕ → ℂ) :
    (qPoly x N w).coeff j = x ^ (j.choose 2) * qBinom x N j * w j := by
  rw [qPoly, finsetSum_coeff, sum_eq_single j]
  · simp only [coeff_C_mul_X_pow, ↓reduceIte]
  · intro b _ hb
    simp only [coeff_C_mul_X_pow, Ne.symm hb, ↓reduceIte]
  · intro h
    exact absurd (mem_range.2 (by omega)) h

lemma qBinom_symm {n s u : ℕ} (h : s + u = n) : qBinom x n s = qBinom x n u := by
  simp only [qBinom, show s ≤ n by omega, show u ≤ n by omega, ↓reduceIte,
    show n - s = u by omega, show n - u = s by omega]
  ring

lemma choose_two_exponent {n s u : ℕ} (h : s + u = n) :
    s.choose 2 + u.choose 2 + n * u = n.choose 2 + u ^ 2 := by
  have hs := add_two_mul_choose_two s
  have hu := add_two_mul_choose_two u
  have hn := add_two_mul_choose_two n
  subst h
  have : 2 * (s.choose 2 + u.choose 2 + (s + u) * u) = 2 * ((s + u).choose 2 + u ^ 2) := by
    zify at hs hu hn ⊢
    linear_combination hs + hu - hn
  omega

/-- The finite identity `[2n, n] = ∑_{i ≤ n} x^{i²} [n, i]²` (the case `m = n = k` of the
`q`-Vandermonde identity). -/
theorem qBinom_two_mul_eq_sum (hx : ‖x‖ < 1) (hx0 : x ≠ 0) (n : ℕ) :
    qBinom x (2 * n) n = ∑ i ∈ range (n + 1), x ^ (i ^ 2) * qBinom x n i ^ 2 := by
  have hpoly : qPoly x (2 * n) (fun _ ↦ 1) =
      qPoly x n (fun _ ↦ 1) * qPoly x n (fun u ↦ x ^ (n * u)) := by
    apply Polynomial.funext
    intro t
    rw [eval_mul, eval_qPoly, eval_qPoly, eval_qPoly]
    simp only [mul_one]
    rw [← qbinomial_theorem hx t (2 * n), ← qbinomial_theorem hx t n]
    have e3 : ∑ j ∈ range (n + 1), x ^ (j.choose 2) * qBinom x n j * x ^ (n * j) * t ^ j =
        ∏ k ∈ range n, (1 + x ^ k * (x ^ n * t)) := by
      rw [qbinomial_theorem hx (x ^ n * t) n]
      refine sum_congr rfl fun j _ ↦ ?_
      rw [mul_pow, ← pow_mul]
      ring
    rw [e3, two_mul, prod_range_add]
    congr 1
    refine prod_congr rfl fun k _ ↦ ?_
    rw [pow_add]
    ring
  have hc := congrArg (fun p : ℂ[X] ↦ p.coeff n) hpoly
  simp only at hc
  rw [coeff_qPoly x (by omega), coeff_mul] at hc
  have hsum : ∑ p ∈ antidiagonal n, (qPoly x n fun _ ↦ 1).coeff p.1 *
      (qPoly x n fun u ↦ x ^ (n * u)).coeff p.2 =
      ∑ p ∈ antidiagonal n, x ^ (n.choose 2) * (x ^ (p.2 ^ 2) * qBinom x n p.2 ^ 2) := by
    refine sum_congr rfl fun p hp ↦ ?_
    have hp' := mem_antidiagonal.1 hp
    rw [coeff_qPoly x (by omega), coeff_qPoly x (by omega), qBinom_symm hp']
    have e := choose_two_exponent hp'
    calc x ^ (p.1.choose 2) * qBinom x n p.2 * 1 *
          (x ^ (p.2.choose 2) * qBinom x n p.2 * x ^ (n * p.2))
        = x ^ (p.1.choose 2 + p.2.choose 2 + n * p.2) * qBinom x n p.2 ^ 2 := by
          rw [pow_add, pow_add]; ring
      _ = _ := by rw [e, pow_add]; ring
  rw [hsum, ← mul_sum, mul_one] at hc
  have hpow : x ^ (n.choose 2) ≠ 0 := pow_ne_zero _ hx0
  have h1 := mul_left_cancel₀ hpow hc
  rw [h1]
  have hswap := Finset.Nat.sum_antidiagonal_swap (n := n)
    (f := fun p : ℕ × ℕ ↦ x ^ (p.1 ^ 2) * qBinom x n p.1 ^ 2)
  simp only [Prod.fst_swap] at hswap
  rw [hswap, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

end Durfee

open Durfee in
/-- **Theorem 351** (Euler). For `‖x‖ < 1`,
`1/((1 - x)(1 - x²)(1 - x³)⋯) = 1 + x/(1 - x)² + x⁴/((1 - x)²(1 - x²)²) + ⋯`. -/
@[kb "hardywright2008" "Thm 351, p. 390"]
theorem hasSum_pow_sq_div_prod_sq {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun i : ℕ ↦ x ^ (i ^ 2) / (∏ k ∈ range i, (1 - x ^ (k + 1))) ^ 2)
      (1 / ∏' k : ℕ, (1 - x ^ (k + 1))) := by
  change HasSum (fun i : ℕ ↦ x ^ (i ^ 2) / qPoch x i ^ 2) (1 / qPochInf x)
  rcases eq_or_ne x 0 with rfl | hx0
  · have hq : ∀ i, qPoch (0 : ℂ) i = 1 := fun i ↦ by simp [qPoch]
    have hP : qPochInf (0 : ℂ) = 1 := by simp [qPochInf]
    rw [hP]
    have h := hasSum_single (f := fun i : ℕ ↦ (0 : ℂ) ^ (i ^ 2) / qPoch 0 i ^ 2) 0
      (fun i hi ↦ by simp [hq, hi])
    simpa [hq] using h
  set P := qPochInf x with hPdef
  have hP0 : P ≠ 0 := qPochInf_ne_zero hx
  obtain ⟨B, hB⟩ := exists_norm_qBinom_le hx
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 0)
  set F : ℕ → ℕ → ℂ := fun n u ↦ x ^ (u ^ 2) * qBinom x n u ^ 2 with hF
  have hfin : ∀ n, ∑' u, F n u = qBinom x (2 * n) n := fun n ↦ by
    rw [qBinom_two_mul_eq_sum hx hx0 n, tsum_eq_sum (s := range (n + 1))]
    intro u hu
    have : ¬ u ≤ n := by simpa using hu
    simp [hF, qBinom, this]
  have hpt : ∀ u, Tendsto (fun n ↦ F n u) atTop (𝓝 (x ^ (u ^ 2) / qPoch x u ^ 2)) := by
    intro u
    have hu0 := qPoch_ne_zero hx u
    have hlim : Tendsto (fun n : ℕ ↦ qPoch x n / (qPoch x u * qPoch x (n - u))) atTop
        (𝓝 (P / (qPoch x u * P))) :=
      (tendsto_qPoch hx).div (tendsto_const_nhds.mul ((tendsto_qPoch hx).comp
        (tendsto_sub_atTop_nat u))) (mul_ne_zero hu0 hP0)
    have e : x ^ (u ^ 2) / qPoch x u ^ 2 = x ^ (u ^ 2) * (P / (qPoch x u * P)) ^ 2 := by
      field_simp
    rw [e]
    refine ((hlim.pow 2).const_mul _).congr' ?_
    filter_upwards [eventually_ge_atTop u] with n hn
    simp [hF, qBinom, hn]
  have hbound : Summable fun u : ℕ ↦ B ^ 2 * ‖x‖ ^ u :=
    (summable_geometric_of_lt_one (norm_nonneg _) hx).mul_left _
  have hbd : ∀ n u, ‖F n u‖ ≤ B ^ 2 * ‖x‖ ^ u := fun n u ↦ by
    simp only [hF, norm_mul, norm_pow]
    have h1 : ‖x‖ ^ (u ^ 2) ≤ ‖x‖ ^ u :=
      pow_le_pow_of_le_one (norm_nonneg _) hx.le (Nat.le_self_pow two_ne_zero u)
    have h2 : ‖qBinom x n u‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hB n u) 2
    calc ‖x‖ ^ (u ^ 2) * ‖qBinom x n u‖ ^ 2 ≤ ‖x‖ ^ u * B ^ 2 :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = _ := mul_comm _ _
  have htann := tendsto_tsum_of_dominated_convergence hbound hpt (Eventually.of_forall hbd)
  have hcentral : Tendsto (fun n : ℕ ↦ qBinom x (2 * n) n) atTop (𝓝 (1 / P)) := by
    have h2n : Tendsto (fun n : ℕ ↦ 2 * n) atTop atTop :=
      tendsto_atTop_mono (fun n ↦ show id n ≤ 2 * n by simp only [id]; omega) tendsto_id
    have hlim : Tendsto (fun n : ℕ ↦ qPoch x (2 * n) / (qPoch x n * qPoch x n)) atTop
        (𝓝 (P / (P * P))) :=
      ((tendsto_qPoch hx).comp h2n).div ((tendsto_qPoch hx).mul (tendsto_qPoch hx))
        (mul_ne_zero hP0 hP0)
    have e : 1 / P = P / (P * P) := by field_simp
    rw [e]
    refine hlim.congr fun n ↦ ?_
    simp [qBinom, show n ≤ 2 * n by omega, show 2 * n - n = n by omega]
  have heq : ∑' u, x ^ (u ^ 2) / qPoch x u ^ 2 = 1 / P := by
    refine tendsto_nhds_unique htann ?_
    exact hcentral.congr fun n ↦ (hfin n).symm
  have hsum : Summable fun u : ℕ ↦ x ^ (u ^ 2) / qPoch x u ^ 2 := by
    refine Summable.of_norm_bounded hbound fun u ↦ ?_
    exact le_of_tendsto' ((hpt u).norm) fun n ↦ hbd n u
  rw [← heq]
  exact hsum.hasSum

end NTKB.HardyWright
