/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TenCount
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TwelveSquares
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.FourteenStatement

/-!
# The formula for `r₁₄`: the comparison of coefficients

From an identity of generating functions with unknown constants `κ` and `c`, valid for
`0 < x < 1/2`, the coefficients of `xᴺ` are compared. The two unknown constants are determined from
the values at `N = 1` and `N = 2` (`r₁₄(1) = 28`, `r₁₄(2) = 364`), and `GlaisherFourteenSquares`
follows (`glaisherFourteenSquares_of_forall`).
-/

open Finset Filter Topology

namespace NTKB.HardyWright


/-- `A(x) = ∑_{k ≥ 1} ∑_{r ≥ 0} χ(r) r⁶ x^{rk}`.
  **Restriction:** the series is the mathematical object only where it converges (absolutely, for $|x| < 1$);
  elsewhere the value is $0$ by Lean's `tsum` convention, not an analytic continuation or the intended value. -/
noncomputable def fourteenSeriesA (x : ℝ) : ℝ :=
  ∑' k : ℕ, ∑' r : ℕ, chi4R r * (r : ℝ) ^ 6 * x ^ (r * (k + 1))

/-- `B(x) = ∑_{m ≥ 1} χ(m) ∑_{r ≥ 0} r⁶ x^{rm}`. -/
noncomputable def fourteenSeriesB (x : ℝ) : ℝ :=
  ∑' m : ℕ, chi4R (m + 1) * ∑' r : ℕ, (r : ℝ) ^ 6 * x ^ (r * (m + 1))

/-- The generating series of the cusp coefficients.
  **Restriction:** the series is the mathematical object only where it converges (absolutely, for $|x| < 1$);
  elsewhere the value is $0$ by Lean's `tsum` convention, not an analytic continuation or the intended value. -/
noncomputable def cuspFourteenSeries (x : ℝ) : ℝ := ∑' n : ℕ, (cuspFourteenCoeff n : ℝ) * x ^ n

/-- The divisor-sum coefficient `∑_{d ∣ N} χ(d) d⁴`. -/
noncomputable def fourteenCoeffA (N : ℕ) : ℝ := ∑ d ∈ N.divisors, chi4R d * (d : ℝ) ^ 6

/-- The divisor-sum coefficient `∑_{d ∣ N} χ(N/d) d⁴`. -/
noncomputable def fourteenCoeffB (N : ℕ) : ℝ := ∑ d ∈ N.divisors, chi4R (N / d) * (d : ℝ) ^ 6

lemma summable_fourteen_majorant {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    Summable fun p : ℕ × ℕ => (p.2 : ℝ) ^ 6 * x ^ (p.2 * (p.1 + 1)) := by
  have hM : Summable fun p : ℕ × ℕ => (p.1 : ℝ) ^ 6 * x ^ (p.1 * (p.2 + 1)) := by
    have hnn : ∀ p : ℕ × ℕ, 0 ≤ (p.1 : ℝ) ^ 6 * x ^ (p.1 * (p.2 + 1)) :=
      fun p => by positivity
    refine (summable_prod_of_nonneg hnn).2 ⟨fun r => ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos r with rfl | hr
      · simp
      · have hxr : x ^ r < 1 := pow_lt_one₀ hx0 hx hr.ne'
        refine ((summable_geometric_of_lt_one (pow_nonneg hx0 r) hxr).mul_left
          ((r : ℝ) ^ 6 * x ^ r)).congr fun k => ?_
        show _ = _
        rw [mul_add, mul_one, pow_add, pow_mul]; ring
    · have hb : Summable fun r : ℕ => (r : ℝ) ^ 6 * x ^ r * (1 - x)⁻¹ :=
        (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 6 (r := x)
          (by rw [Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx)).mul_right _
      have h1x : 0 < 1 - x := by linarith
      refine Summable.of_nonneg_of_le (fun r => tsum_nonneg fun k => hnn (r, k)) (fun r => ?_) hb
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · simp
      · have hxr : x ^ r < 1 := pow_lt_one₀ hx0 hx hr.ne'
        have hxr' : x ^ r ≤ x := pow_le_of_le_one hx0 hx.le hr.ne'
        have : ∑' k : ℕ, (r : ℝ) ^ 6 * x ^ (r * (k + 1)) =
            (r : ℝ) ^ 6 * x ^ r * (1 - x ^ r)⁻¹ := by
          rw [← tsum_geometric_of_lt_one (pow_nonneg hx0 r) hxr, ← tsum_mul_left]
          refine tsum_congr fun k => ?_
          rw [mul_add, mul_one, pow_add, pow_mul]; ring
        show ∑' k : ℕ, (r : ℝ) ^ 6 * x ^ (r * (k + 1)) ≤ _
        rw [this]
        exact mul_le_mul_of_nonneg_left (inv_anti₀ h1x (by linarith)) (by positivity)
  exact (Equiv.prodComm ℕ ℕ).summable_iff.mpr hM

lemma hasSum_fourteenCoeffA {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    HasSum (fun N : ℕ => fourteenCoeffA N * x ^ N) (fourteenSeriesA x) := by
  have hs : Summable fun p : ℕ × ℕ => chi4R p.2 * (p.2 : ℝ) ^ 6 * x ^ (p.2 * (p.1 + 1)) := by
    refine Summable.of_norm_bounded (summable_fourteen_majorant hx0 hx) fun p => ?_
    have h2 : (0 : ℝ) ≤ (p.2 : ℝ) ^ 6 * x ^ (p.2 * (p.1 + 1)) := by positivity
    rw [Real.norm_eq_abs, mul_assoc, abs_mul, abs_of_nonneg h2]
    have := abs_chi4R_le p.2
    nlinarith
  have := hasSum_divisor_rearr (fun r m => chi4R r * (r : ℝ) ^ 6 * x ^ (r * m)) (by simp) hs
  refine this.congr_fun fun N => ?_
  unfold fourteenCoeffA
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]

lemma hasSum_fourteenCoeffB {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    HasSum (fun N : ℕ => fourteenCoeffB N * x ^ N) (fourteenSeriesB x) := by
  have hs : Summable fun p : ℕ × ℕ =>
      chi4R (p.1 + 1) * ((p.2 : ℝ) ^ 6 * x ^ (p.2 * (p.1 + 1))) := by
    refine Summable.of_norm_bounded (summable_fourteen_majorant hx0 hx) fun p => ?_
    have h2 : (0 : ℝ) ≤ (p.2 : ℝ) ^ 6 * x ^ (p.2 * (p.1 + 1)) := by positivity
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2]
    have := abs_chi4R_le (p.1 + 1)
    nlinarith
  have := hasSum_divisor_rearr (fun r m => chi4R m * ((r : ℝ) ^ 6 * x ^ (r * m)))
    (by simp) hs
  have e : fourteenSeriesB x = ∑' k : ℕ, ∑' r : ℕ,
      chi4R (k + 1) * ((r : ℝ) ^ 6 * x ^ (r * (k + 1))) := by
    unfold fourteenSeriesB
    exact tsum_congr fun k => (tsum_mul_left).symm
  rw [e]
  refine this.congr_fun fun N => ?_
  unfold fourteenCoeffB
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
  ring


open TwelveSquares in
lemma hasSum_cuspFourteenSeries {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    HasSum (fun n : ℕ => (cuspFourteenCoeff n : ℝ) * x ^ n)
      ((∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 2 * etaSeriesR x) := by
  have hx1 : x < 1 := by linarith
  have hf := hasSum_sumSquaresCount 2 hx0 hx1
  have hg := hasSum_etaSeriesR hx0 hx1
  have hfn : Summable fun k : ℕ => ‖(sumSquaresCount 2 k : ℝ) * x ^ k‖ := by
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
  simp only [cuspFourteenCoeff]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have : x ^ n = x ^ k * x ^ (n - k) := by rw [← pow_add]; congr 1; omega
  rw [this]; ring

/-- `r₁₄(1) = 28`. -/
lemma sumSquaresCount_fourteen_one : sumSquaresCount 14 1 = 28 := by
  rw [sumSquaresCount_one_eq]

/-- `r₁₄(2) = 364`. -/
lemma sumSquaresCount_fourteen_two : sumSquaresCount 14 2 = 364 := by
  rw [sumSquaresCount_two_eq]

lemma cuspFourteenCoeff_one : cuspFourteenCoeff 1 = 1 := by
  simp [cuspFourteenCoeff, Finset.sum_range_succ, TwelveSquares.etaTwelveCoeff_zero,
    TwelveSquares.etaTwelveCoeff_one, sumSquaresCount_zero]

lemma cuspFourteenCoeff_two : cuspFourteenCoeff 2 = 4 := by
  have h1 : sumSquaresCount 2 1 = 4 := by rw [sumSquaresCount_one_eq]
  simp [cuspFourteenCoeff, Finset.sum_range_succ, TwelveSquares.etaTwelveCoeff_zero,
    TwelveSquares.etaTwelveCoeff_one, TwelveSquares.etaTwelveCoeff_two, sumSquaresCount_zero, h1]

lemma fourteen_coeff_eq_zero {κ c : ℝ}
    (h : ∀ x : ℝ, 0 < x → x < 1 / 2 → κ * (∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 14 =
      κ + Real.pi ^ 7 / 360 * fourteenSeriesB x - Real.pi ^ 7 / 23040 * fourteenSeriesA x +
        c * ((∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 2 * TwelveSquares.etaSeriesR x))
    {N : ℕ} (hN : 0 < N) :
    κ * (sumSquaresCount 14 N : ℝ) - Real.pi ^ 7 / 360 * fourteenCoeffB N
      + Real.pi ^ 7 / 23040 * fourteenCoeffA N - c * (cuspFourteenCoeff N : ℝ) = 0 := by
  set a : ℕ → ℝ := fun N => κ * (sumSquaresCount 14 N : ℝ) - (if N = 0 then κ else 0)
    - Real.pi ^ 7 / 360 * fourteenCoeffB N + Real.pi ^ 7 / 23040 * fourteenCoeffA N
    - c * (cuspFourteenCoeff N : ℝ) with ha
  have hHA : ∀ x : ℝ, 0 ≤ x → x ≤ 1 / 2 →
      HasSum (fun N : ℕ => a N * x ^ N)
        (κ * (∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 14 - κ - Real.pi ^ 7 / 360 * fourteenSeriesB x
          + Real.pi ^ 7 / 23040 * fourteenSeriesA x -
          c * ((∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 2 * TwelveSquares.etaSeriesR x)) := by
    intro x hx0 hx
    have hx1 : x < 1 := by linarith
    have h3 : HasSum (fun N : ℕ => (if N = 0 then κ else 0) * x ^ N) κ := by
      have := hasSum_ite_eq (0 : ℕ) κ
      refine this.congr_fun fun N => ?_
      by_cases hN : N = 0 <;> simp [hN]
    have := (((((hasSum_sumSquaresCount 14 hx0 hx1).mul_left κ).sub h3).sub
      ((hasSum_fourteenCoeffB hx0 hx1).mul_left (Real.pi ^ 7 / 360))).add
      ((hasSum_fourteenCoeffA hx0 hx1).mul_left (Real.pi ^ 7 / 23040))).sub
      ((hasSum_cuspFourteenSeries hx0 hx).mul_left c)
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

lemma fourteenCoeffA_one : fourteenCoeffA 1 = 1 := by
  simp [fourteenCoeffA, chi4R]

lemma fourteenCoeffB_one : fourteenCoeffB 1 = 1 := by
  simp [fourteenCoeffB, chi4R]

lemma fourteenCoeffA_two : fourteenCoeffA 2 = 1 := by
  have : (Nat.divisors 2) = {1, 2} := by decide
  simp [fourteenCoeffA, this, chi4R]

lemma fourteenCoeffB_two : fourteenCoeffB 2 = 64 := by
  have : (Nat.divisors 2) = {1, 2} := by decide
  simp [fourteenCoeffB, this, chi4R]
  norm_num

theorem glaisherFourteenSquares_of_forall {κ c : ℝ}
    (h : ∀ x : ℝ, 0 < x → x < 1 / 2 → κ * (∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 14 =
      κ + Real.pi ^ 7 / 360 * fourteenSeriesB x - Real.pi ^ 7 / 23040 * fourteenSeriesA x +
        c * ((∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 2 * TwelveSquares.etaSeriesR x)) :
    GlaisherFourteenSquares := by
  have h1 := fourteen_coeff_eq_zero h (N := 1) one_pos
  have h2 := fourteen_coeff_eq_zero h (N := 2) two_pos
  rw [sumSquaresCount_fourteen_one, fourteenCoeffA_one, fourteenCoeffB_one,
    cuspFourteenCoeff_one] at h1
  rw [sumSquaresCount_fourteen_two, fourteenCoeffA_two, fourteenCoeffB_two,
    cuspFourteenCoeff_two] at h2
  push_cast at h1 h2
  have hκ : κ = 61 * Real.pi ^ 7 / 92160 := by linarith
  have hc : c = 1456 * Real.pi ^ 7 / 92160 := by linarith
  intro n hn
  have h3 := fourteen_coeff_eq_zero h hn
  rw [hκ, hc] at h3
  have hp : 0 < Real.pi ^ 7 := by positivity
  have hA : (fourteenSumA n : ℝ) = fourteenCoeffA n := by
    simp [fourteenSumA, fourteenCoeffA, chi4R]
  have hB : (fourteenSumB n : ℝ) = fourteenCoeffB n := by
    simp [fourteenSumB, fourteenCoeffB, chi4R]
  have h4 : Real.pi ^ 7 * (61 * (sumSquaresCount 14 n : ℝ) - (4 * (64 * (fourteenSumB n : ℝ)
      - (fourteenSumA n : ℝ)) + 1456 * (cuspFourteenCoeff n : ℝ))) = 0 := by
    rw [hA, hB]; linear_combination 92160 * h3
  have h5 : 61 * (sumSquaresCount 14 n : ℝ) = 4 * (64 * (fourteenSumB n : ℝ)
      - (fourteenSumA n : ℝ)) + 1456 * (cuspFourteenCoeff n : ℝ) := by
    rcases mul_eq_zero.1 h4 with h | h
    · exact absurd h hp.ne'
    · linarith
  exact_mod_cast h5

end NTKB.HardyWright
