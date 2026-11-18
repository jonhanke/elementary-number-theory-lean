/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.FourteenCount

/-!
# The formula for `r₁₆`: the comparison of coefficients

From an identity of generating functions with unknown constants `κ` and `c`, valid for
`0 < x < 1/2`, the coefficients of `xᴺ` are compared. The two unknown constants are determined from
the values at `N = 1` and `N = 2` (`r₁₆(1) = 32`, `r₁₆(2) = 480`), and `GlaisherSixteenSquares`
follows (`glaisherSixteenSquares_of_forall`).
-/

open Finset Filter Topology

namespace NTKB.HardyWright

/-- The terms `[m even] (-1)^r r⁷ x^{rm} + [m odd] r⁷ x^{rm}` of `O(x) + E(x)`. -/
noncomputable def sixteenG (x : ℝ) (r m : ℕ) : ℝ :=
  (if Even m then (-1) ^ r else 1) * ((r : ℝ) ^ 7 * x ^ (r * m))

/-- `O(x) + E(x) = ∑_{m ≥ 1} ∑_{r} [m even] (-1)^r r⁷ x^{rm} + [m odd] r⁷ x^{rm}`. -/
noncomputable def sixteenSeriesOE (x : ℝ) : ℝ := ∑' k : ℕ, ∑' r : ℕ, sixteenG x r (k + 1)

/-- The coefficient of `xᴺ`: `∑_{d ∣ N} ([N/d even] (-1)^d + [N/d odd]) d⁷`. -/
noncomputable def sixteenCoeffR (N : ℕ) : ℝ :=
  ∑ d ∈ N.divisors, (if Even (N / d) then (-1) ^ d else 1) * (d : ℝ) ^ 7

lemma abs_sixteenG_le (x : ℝ) (r m : ℕ) (hx0 : 0 ≤ x) :
    |sixteenG x r m| ≤ (r : ℝ) ^ 7 * x ^ (r * m) := by
  unfold sixteenG
  have h2 : (0 : ℝ) ≤ (r : ℝ) ^ 7 * x ^ (r * m) := by positivity
  rw [abs_mul, abs_of_nonneg h2]
  have : |(if Even m then (-1 : ℝ) ^ r else 1)| ≤ 1 := by
    split_ifs
    · simp
    · simp
  nlinarith

lemma summable_sixteen_majorant {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    Summable fun p : ℕ × ℕ => (p.2 : ℝ) ^ 7 * x ^ (p.2 * (p.1 + 1)) := by
  have hM : Summable fun p : ℕ × ℕ => (p.1 : ℝ) ^ 7 * x ^ (p.1 * (p.2 + 1)) := by
    have hnn : ∀ p : ℕ × ℕ, 0 ≤ (p.1 : ℝ) ^ 7 * x ^ (p.1 * (p.2 + 1)) :=
      fun p => by positivity
    refine (summable_prod_of_nonneg hnn).2 ⟨fun r => ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos r with rfl | hr
      · simp
      · have hxr : x ^ r < 1 := pow_lt_one₀ hx0 hx hr.ne'
        refine ((summable_geometric_of_lt_one (pow_nonneg hx0 r) hxr).mul_left
          ((r : ℝ) ^ 7 * x ^ r)).congr fun k => ?_
        show _ = _
        rw [mul_add, mul_one, pow_add, pow_mul]; ring
    · have hb : Summable fun r : ℕ => (r : ℝ) ^ 7 * x ^ r * (1 - x)⁻¹ :=
        (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 7 (r := x)
          (by rw [Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx)).mul_right _
      have h1x : 0 < 1 - x := by linarith
      refine Summable.of_nonneg_of_le (fun r => tsum_nonneg fun k => hnn (r, k)) (fun r => ?_) hb
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · simp
      · have hxr : x ^ r < 1 := pow_lt_one₀ hx0 hx hr.ne'
        have hxr' : x ^ r ≤ x := pow_le_of_le_one hx0 hx.le hr.ne'
        have : ∑' k : ℕ, (r : ℝ) ^ 7 * x ^ (r * (k + 1)) =
            (r : ℝ) ^ 7 * x ^ r * (1 - x ^ r)⁻¹ := by
          rw [← tsum_geometric_of_lt_one (pow_nonneg hx0 r) hxr, ← tsum_mul_left]
          refine tsum_congr fun k => ?_
          rw [mul_add, mul_one, pow_add, pow_mul]; ring
        show ∑' k : ℕ, (r : ℝ) ^ 7 * x ^ (r * (k + 1)) ≤ _
        rw [this]
        exact mul_le_mul_of_nonneg_left (inv_anti₀ h1x (by linarith)) (by positivity)
  exact (Equiv.prodComm ℕ ℕ).summable_iff.mpr hM


lemma hasSum_sixteenCoeffR {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    HasSum (fun N : ℕ => sixteenCoeffR N * x ^ N) (sixteenSeriesOE x) := by
  have hs : Summable fun p : ℕ × ℕ => sixteenG x p.2 (p.1 + 1) := by
    refine Summable.of_norm_bounded (summable_sixteen_majorant hx0 hx) fun p => ?_
    rw [Real.norm_eq_abs]
    exact abs_sixteenG_le x p.2 (p.1 + 1) hx0
  have := hasSum_divisor_rearr (fun r m => sixteenG x r m) (by simp [sixteenG]) hs
  refine this.congr_fun fun N => ?_
  unfold sixteenCoeffR
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  unfold sixteenG
  rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
  ring

lemma sixteenCoeffR_eq (N : ℕ) : sixteenCoeffR N = (sixteenSum N : ℝ) := by
  unfold sixteenCoeffR sixteenSum
  push_cast
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdN : d * (N / d) = N := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
  set m := N / d with hm
  rcases Nat.even_or_odd m with he | ho
  · rw [if_pos he]
    have h1 : (-1 : ℝ) ^ N = 1 := by rw [← hdN]; exact (he.mul_left d).neg_one_pow
    rw [pow_add, h1, one_mul]
  · rw [if_neg (Nat.not_even_iff_odd.mpr ho)]
    have : Even (N + d) := by
      rw [← hdN]
      have : d * m + d = d * (m + 1) := by ring
      rw [this]
      exact (Odd.add_one ho).mul_left d
    rw [this.neg_one_pow]


open TwelveSquares in
lemma hasSum_cuspSixteenSeries {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    HasSum (fun n : ℕ => (cuspSixteenCoeff n : ℝ) * x ^ n)
      ((∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 4 * etaSeriesR x) := by
  have hx1 : x < 1 := by linarith
  have hf := hasSum_sumSquaresCount 4 hx0 hx1
  have hg := hasSum_etaSeriesR hx0 hx1
  have hfn : Summable fun k : ℕ => ‖(sumSquaresCount 4 k : ℝ) * x ^ k‖ := by
    refine hf.summable.congr fun k => ?_
    rw [Real.norm_of_nonneg (by positivity)]
  have hgn : Summable fun k : ℕ => ‖(etaTwelveCoeff k : ℝ) * x ^ k‖ := by
    have hC : Summable fun n : ℕ => ‖(etaTwelveCoeff n : ℂ)‖ * (1 / 2 : ℝ) ^ n :=
      hasSum_Ceta.summable
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) hC
    rw [norm_mul, norm_pow, Real.norm_of_nonneg hx0, Complex.norm_intCast, Real.norm_eq_abs]
    gcongr
  have h := hasSum_sum_range_mul_of_summable_norm hfn hgn
  rw [hf.tsum_eq, hg.tsum_eq] at h
  refine h.congr_fun fun n => ?_
  simp only [cuspSixteenCoeff]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have : x ^ n = x ^ k * x ^ (n - k) := by rw [← pow_add]; congr 1; omega
  rw [this]; ring

/-- `r₁₆(1) = 32`. -/
lemma sumSquaresCount_sixteen_one : sumSquaresCount 16 1 = 32 := by
  rw [sumSquaresCount_one_eq]

/-- `r₁₆(2) = 480`. -/
lemma sumSquaresCount_sixteen_two : sumSquaresCount 16 2 = 480 := by
  rw [sumSquaresCount_two_eq]

lemma cuspSixteenCoeff_one : cuspSixteenCoeff 1 = 1 := by
  simp [cuspSixteenCoeff, Finset.sum_range_succ, TwelveSquares.etaTwelveCoeff_zero,
    TwelveSquares.etaTwelveCoeff_one, sumSquaresCount_zero]

lemma cuspSixteenCoeff_two : cuspSixteenCoeff 2 = 8 := by
  have h1 : sumSquaresCount 4 1 = 8 := by rw [sumSquaresCount_one_eq]
  simp [cuspSixteenCoeff, Finset.sum_range_succ, TwelveSquares.etaTwelveCoeff_zero,
    TwelveSquares.etaTwelveCoeff_one, TwelveSquares.etaTwelveCoeff_two, sumSquaresCount_zero, h1]

lemma sixteenSum_one : sixteenSum 1 = 1 := by
  simp [sixteenSum]

lemma sixteenSum_two : sixteenSum 2 = 127 := by
  have : (Nat.divisors 2) = {1, 2} := by decide
  simp [sixteenSum, this]

lemma sixteen_coeff_eq_zero {κ c : ℝ}
    (h : ∀ x : ℝ, 0 < x → x < 1 / 2 → κ * (∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 16 =
      κ + Real.pi ^ 8 / 2520 * sixteenSeriesOE x +
        c * ((∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 4 * TwelveSquares.etaSeriesR x))
    {N : ℕ} (hN : 0 < N) :
    κ * (sumSquaresCount 16 N : ℝ) - Real.pi ^ 8 / 2520 * sixteenCoeffR N
      - c * (cuspSixteenCoeff N : ℝ) = 0 := by
  set a : ℕ → ℝ := fun N => κ * (sumSquaresCount 16 N : ℝ) - (if N = 0 then κ else 0)
    - Real.pi ^ 8 / 2520 * sixteenCoeffR N - c * (cuspSixteenCoeff N : ℝ) with ha
  have hHA : ∀ x : ℝ, 0 ≤ x → x ≤ 1 / 2 →
      HasSum (fun N : ℕ => a N * x ^ N)
        (κ * (∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 16 - κ - Real.pi ^ 8 / 2520 * sixteenSeriesOE x -
          c * ((∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 4 * TwelveSquares.etaSeriesR x)) := by
    intro x hx0 hx
    have hx1 : x < 1 := by linarith
    have h3 : HasSum (fun N : ℕ => (if N = 0 then κ else 0) * x ^ N) κ := by
      have := hasSum_ite_eq (0 : ℕ) κ
      refine this.congr_fun fun N => ?_
      by_cases hN : N = 0 <;> simp [hN]
    have := ((((hasSum_sumSquaresCount 16 hx0 hx1).mul_left κ).sub h3).sub
      ((hasSum_sixteenCoeffR hx0 hx1).mul_left (Real.pi ^ 8 / 2520))).sub
      ((hasSum_cuspSixteenSeries hx0 hx).mul_left c)
    refine this.congr_fun fun N => ?_
    simp only [ha]; ring
  have hzero : ∀ x : ℝ, 0 < x → x < 1 / 2 → ∑' N, a N * x ^ N = 0 := by
    intro x hx0 hx
    rw [(hHA x hx0.le hx.le).tsum_eq, h x hx0 hx]; ring
  have hs : Summable fun N => |a N| * (1 / 2 : ℝ) ^ N := by
    have := (hHA (1 / 2) (by norm_num) le_rfl).summable.abs
    refine this.congr fun N => ?_
    rw [abs_mul, abs_of_pos (show (0 : ℝ) < (1 / 2) ^ N by positivity)]
  have hn0 := eq_zero_of_tsum_pow_eq_zero hs hzero N
  simp only [ha, if_neg hN.ne'] at hn0
  linarith

theorem glaisherSixteenSquares_of_forall {κ c : ℝ}
    (h : ∀ x : ℝ, 0 < x → x < 1 / 2 → κ * (∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 16 =
      κ + Real.pi ^ 8 / 2520 * sixteenSeriesOE x +
        c * ((∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 4 * TwelveSquares.etaSeriesR x)) :
    GlaisherSixteenSquares := by
  have h1 := sixteen_coeff_eq_zero h (N := 1) one_pos
  have h2 := sixteen_coeff_eq_zero h (N := 2) two_pos
  rw [sumSquaresCount_sixteen_one, sixteenCoeffR_eq, sixteenSum_one, cuspSixteenCoeff_one] at h1
  rw [sumSquaresCount_sixteen_two, sixteenCoeffR_eq, sixteenSum_two, cuspSixteenCoeff_two] at h2
  push_cast at h1 h2
  have hκ : κ = 17 * Real.pi ^ 8 / 80640 := by linarith
  have hc : c = 512 * Real.pi ^ 8 / 80640 := by linarith
  intro n hn
  have h3 := sixteen_coeff_eq_zero h hn
  rw [hκ, hc, sixteenCoeffR_eq] at h3
  have hp : 0 < Real.pi ^ 8 := by positivity
  have h4 : Real.pi ^ 8 * (17 * (sumSquaresCount 16 n : ℝ) - (32 * (sixteenSum n : ℝ)
      + 512 * (cuspSixteenCoeff n : ℝ))) = 0 := by
    linear_combination 80640 * h3
  have h5 : 17 * (sumSquaresCount 16 n : ℝ) = 32 * (sixteenSum n : ℝ)
      + 512 * (cuspSixteenCoeff n : ℝ) := by
    rcases mul_eq_zero.1 h4 with h | h
    · exact absurd h hp.ne'
    · linarith
  exact_mod_cast h5

end NTKB.HardyWright
