/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.EighteenCount
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TwelveCount
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.EighteenStatement

/-!
# The formula for `r₂₀`: the comparison of coefficients

From an identity of generating functions with unknown constants `κ`, `c₁`, `c₂`, valid for
`0 < x < 1/2`, the coefficients of `xᴺ` are compared. The constants are determined from the values
at `N = 1, 2, 3` (`r₂₀ = 40, 760, 9120`), and `TwentySquaresFormula` follows
(`twentySquaresFormula_of_forall`).
-/

open Finset Filter Topology

namespace NTKB.HardyWright

/-- `O(x) = ∑_{k ≥ 0} ∑_{r ≥ 0} r⁹ x^{r(2k+1)}`.
  **Restriction:** the series is the mathematical object only where it converges (absolutely, for $|x| < 1$);
  elsewhere the value is $0$ by Lean's `tsum` convention, not an analytic continuation or the intended value. -/
noncomputable def twentySeriesO (x : ℝ) : ℝ :=
  ∑' k : ℕ, ∑' r : ℕ, (r : ℝ) ^ 9 * x ^ (r * (2 * k + 1))

/-- `E(x) = ∑_{k ≥ 0} ∑_{r ≥ 0} (-1)^r r⁹ x^{2r(k+1)}`. -/
noncomputable def twentySeriesE (x : ℝ) : ℝ :=
  ∑' k : ℕ, ∑' r : ℕ, (-1) ^ r * (r : ℝ) ^ 9 * x ^ (r * (2 * (k + 1)))

lemma summable_twenty_majorant {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    Summable fun p : ℕ × ℕ => (p.2 : ℝ) ^ 9 * x ^ (p.2 * (p.1 + 1)) := by
  have hM : Summable fun p : ℕ × ℕ => (p.1 : ℝ) ^ 9 * x ^ (p.1 * (p.2 + 1)) := by
    have hnn : ∀ p : ℕ × ℕ, 0 ≤ (p.1 : ℝ) ^ 9 * x ^ (p.1 * (p.2 + 1)) :=
      fun p => by positivity
    refine (summable_prod_of_nonneg hnn).2 ⟨fun r => ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos r with rfl | hr
      · simp
      · have hxr : x ^ r < 1 := pow_lt_one₀ hx0 hx hr.ne'
        refine ((summable_geometric_of_lt_one (pow_nonneg hx0 r) hxr).mul_left
          ((r : ℝ) ^ 9 * x ^ r)).congr fun k => ?_
        show _ = _
        rw [mul_add, mul_one, pow_add, pow_mul]; ring
    · have hb : Summable fun r : ℕ => (r : ℝ) ^ 9 * x ^ r * (1 - x)⁻¹ :=
        (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 9 (r := x)
          (by rw [Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx)).mul_right _
      have h1x : 0 < 1 - x := by linarith
      refine Summable.of_nonneg_of_le (fun r => tsum_nonneg fun k => hnn (r, k)) (fun r => ?_) hb
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · simp
      · have hxr : x ^ r < 1 := pow_lt_one₀ hx0 hx hr.ne'
        have hxr' : x ^ r ≤ x := pow_le_of_le_one hx0 hx.le hr.ne'
        have : ∑' k : ℕ, (r : ℝ) ^ 9 * x ^ (r * (k + 1)) =
            (r : ℝ) ^ 9 * x ^ r * (1 - x ^ r)⁻¹ := by
          rw [← tsum_geometric_of_lt_one (pow_nonneg hx0 r) hxr, ← tsum_mul_left]
          refine tsum_congr fun k => ?_
          rw [mul_add, mul_one, pow_add, pow_mul]; ring
        show ∑' k : ℕ, (r : ℝ) ^ 9 * x ^ (r * (k + 1)) ≤ _
        rw [this]
        exact mul_le_mul_of_nonneg_left (inv_anti₀ h1x (by linarith)) (by positivity)
  exact (Equiv.prodComm ℕ ℕ).summable_iff.mpr hM

theorem hasSum_twentySum {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    HasSum (fun N : ℕ => (twentySum N : ℝ) * x ^ N) (twentySeriesO x - twentySeriesE x) := by
  set G : ℕ → ℕ → ℝ := fun r m =>
    (if m % 2 = 1 then 1 else -(-1) ^ r) * ((r : ℝ) ^ 9 * x ^ (r * m)) with hG
  have hs : Summable fun p : ℕ × ℕ => G p.2 (p.1 + 1) := by
    refine Summable.of_norm_bounded (summable_twenty_majorant hx0 hx) fun p => ?_
    have h2 : (0 : ℝ) ≤ (p.2 : ℝ) ^ 9 * x ^ (p.2 * (p.1 + 1)) := by positivity
    simp only [hG]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2]
    have : |(if (p.1 + 1) % 2 = 1 then (1 : ℝ) else -(-1) ^ p.2)| ≤ 1 := by
      split_ifs
      · simp
      · simp
    nlinarith
  have hD := hasSum_divisor_rearr G (by simp [hG]) hs
  have hU : Summable fun k : ℕ => ∑' r : ℕ, G r (k + 1) := hs.prod
  have hUe : Summable fun j : ℕ => ∑' r : ℕ, G r (2 * j + 1) :=
    hU.comp_injective (i := fun j : ℕ => 2 * j) (by intro a b h; simpa using h)
  have hUo : Summable fun j : ℕ => ∑' r : ℕ, G r (2 * j + 1 + 1) :=
    hU.comp_injective (i := fun j : ℕ => 2 * j + 1) (by intro a b h; simpa using h)
  have e1 : ∀ j : ℕ, ∑' r : ℕ, G r (2 * j + 1) = ∑' r : ℕ, (r : ℝ) ^ 9 * x ^ (r * (2 * j + 1)) := by
    intro j
    refine tsum_congr fun r => ?_
    simp only [hG]
    rw [if_pos (by omega), one_mul]
  have e2 : ∀ j : ℕ, ∑' r : ℕ, G r (2 * j + 1 + 1) =
      -∑' r : ℕ, (-1) ^ r * (r : ℝ) ^ 9 * x ^ (r * (2 * (j + 1))) := by
    intro j
    rw [← tsum_neg]
    refine tsum_congr fun r => ?_
    simp only [hG]
    rw [if_neg (by omega), show 2 * j + 1 + 1 = 2 * (j + 1) by ring]
    ring
  have eT : ∑' k : ℕ, ∑' r : ℕ, G r (k + 1) = twentySeriesO x - twentySeriesE x := by
    rw [← tsum_even_add_odd hUe hUo]
    simp only [e1, e2]
    rw [tsum_neg]
    rfl
  rw [eT] at hD
  refine hD.congr_fun fun N => ?_
  rw [twentySum]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨e, rfl⟩ := Nat.dvd_of_mem_divisors hd
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  rw [Nat.mul_div_cancel_left e hd0]
  simp only [hG]
  have hsg := glaisher_sign d e
  have hsg' : ((-1 : ℝ) ^ (d * e + d + e + 1)) = if e % 2 = 1 then 1 else -(-1) ^ d := by
    have := congrArg (Int.cast : ℤ → ℝ) hsg
    push_cast at this
    exact this
  rw [hsg']
  ring

open TwelveSquares in
lemma hasSum_cuspTwentySeries {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    HasSum (fun n : ℕ => (cuspTwentyCoeff n : ℝ) * x ^ n)
      ((∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 8 * etaSeriesR x) := by
  have hx1 : x < 1 := by linarith
  have hf := hasSum_sumSquaresCount 8 hx0 hx1
  have hg := hasSum_etaSeriesR hx0 hx1
  have hfn : Summable fun k : ℕ => ‖(sumSquaresCount 8 k : ℝ) * x ^ k‖ := by
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
  simp only [cuspTwentyCoeff]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have : x ^ n = x ^ k * x ^ (n - k) := by rw [← pow_add]; congr 1; omega
  rw [this]; ring

lemma hasSum_cuspTwentySeries' {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    HasSum (fun n : ℕ => (cuspTwentyCoeff' n : ℝ) * x ^ n)
      ((∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 2 * octSeriesR x) := by
  have hx1 : x < 1 := by linarith
  have hf := hasSum_sumSquaresCount 2 hx0 hx1
  have hg := hasSum_octSeriesR hx0 hx1
  have hfn : Summable fun k : ℕ => ‖(sumSquaresCount 2 k : ℝ) * x ^ k‖ := by
    refine hf.summable.congr fun k => ?_
    rw [Real.norm_of_nonneg (by positivity)]
  have hgn : Summable fun k : ℕ => ‖(octicCoeff k : ℝ) * x ^ k‖ := by
    refine (summable_octicCoeff_abs hx0 hx1).congr fun k => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hx0 k)]
  have h := hasSum_sum_range_mul_of_summable_norm hfn hgn
  rw [hf.tsum_eq, hg.tsum_eq] at h
  refine h.congr_fun fun n => ?_
  simp only [cuspTwentyCoeff']
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have : x ^ n = x ^ k * x ^ (n - k) := by rw [← pow_add]; congr 1; omega
  rw [this]; ring

lemma sumSquaresCount_twenty_one : sumSquaresCount 20 1 = 40 := by
  rw [sumSquaresCount_one_eq]

lemma sumSquaresCount_twenty_two : sumSquaresCount 20 2 = 760 := by
  rw [sumSquaresCount_two_eq]

lemma sumSquaresCount_twenty_three : sumSquaresCount 20 3 = 9120 := by
  rw [sumSquaresCount_three_eq]; decide

lemma twentySum_one : twentySum 1 = 1 := by
  simp [twentySum]

lemma twentySum_two : twentySum 2 = 513 := by
  have : (Nat.divisors 2) = {1, 2} := by decide
  simp [twentySum, this]

lemma twentySum_three : twentySum 3 = 19684 := by
  have : (Nat.divisors 3) = {1, 3} := by decide
  simp [twentySum, this]

lemma cuspTwentyCoeff_one : cuspTwentyCoeff 1 = 1 := by
  simp [cuspTwentyCoeff, Finset.sum_range_succ, TwelveSquares.etaTwelveCoeff_zero,
    TwelveSquares.etaTwelveCoeff_one, sumSquaresCount_zero]

lemma cuspTwentyCoeff_two : cuspTwentyCoeff 2 = 16 := by
  have h1 : sumSquaresCount 8 1 = 16 := by rw [sumSquaresCount_one_eq]
  simp [cuspTwentyCoeff, Finset.sum_range_succ, TwelveSquares.etaTwelveCoeff_zero,
    TwelveSquares.etaTwelveCoeff_one, TwelveSquares.etaTwelveCoeff_two, sumSquaresCount_zero, h1]

lemma cuspTwentyCoeff_three : cuspTwentyCoeff 3 = 100 := by
  have h1 : sumSquaresCount 8 1 = 16 := by rw [sumSquaresCount_one_eq]
  have h2 : sumSquaresCount 8 2 = 112 := by rw [sumSquaresCount_two_eq]
  simp [cuspTwentyCoeff, Finset.sum_range_succ, TwelveSquares.etaTwelveCoeff_zero,
    TwelveSquares.etaTwelveCoeff_one, TwelveSquares.etaTwelveCoeff_two,
    TwelveSquares.etaTwelveCoeff_three, sumSquaresCount_zero, h1, h2]

lemma cuspTwentyCoeff'_one : cuspTwentyCoeff' 1 = 4 := by
  have h1 : sumSquaresCount 2 1 = 4 := by rw [sumSquaresCount_one_eq]
  simp [cuspTwentyCoeff', Finset.sum_range_succ, sumSquaresCount_zero, h1, octicCoeff_zero,
    octicCoeff_one]

lemma cuspTwentyCoeff'_two : cuspTwentyCoeff' 2 = 80 := by
  have h1 : sumSquaresCount 2 1 = 4 := by rw [sumSquaresCount_one_eq]
  have h2 : sumSquaresCount 2 2 = 4 := by rw [sumSquaresCount_two_eq]
  simp [cuspTwentyCoeff', Finset.sum_range_succ, sumSquaresCount_zero, h1, h2, octicCoeff_zero,
    octicCoeff_one, octicCoeff_two]

lemma cuspTwentyCoeff'_three : cuspTwentyCoeff' 3 = 272 := by
  have h1 : sumSquaresCount 2 1 = 4 := by rw [sumSquaresCount_one_eq]
  have h2 : sumSquaresCount 2 2 = 4 := by rw [sumSquaresCount_two_eq]
  have h3 : sumSquaresCount 2 3 = 0 := by
    have := sumSquaresCount_three_eq 2
    simpa using this
  simp [cuspTwentyCoeff', Finset.sum_range_succ, sumSquaresCount_zero, h1, h2, h3,
    octicCoeff_zero, octicCoeff_one, octicCoeff_two, octicCoeff_three]

lemma twenty_coeff_eq_zero {κ c₁ c₂ : ℝ}
    (h : ∀ x : ℝ, 0 < x → x < 1 / 2 → κ * (∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 20 =
      κ + Real.pi ^ 10 / 181440 * (twentySeriesO x - twentySeriesE x) +
        c₁ * ((∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 8 * TwelveSquares.etaSeriesR x) +
        c₂ * ((∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 2 * octSeriesR x))
    {N : ℕ} (hN : 0 < N) :
    κ * (sumSquaresCount 20 N : ℝ) - Real.pi ^ 10 / 181440 * (twentySum N : ℝ)
      - c₁ * (cuspTwentyCoeff N : ℝ) - c₂ * (cuspTwentyCoeff' N : ℝ) = 0 := by
  set a : ℕ → ℝ := fun N => κ * (sumSquaresCount 20 N : ℝ) - (if N = 0 then κ else 0)
    - Real.pi ^ 10 / 181440 * (twentySum N : ℝ)
    - c₁ * (cuspTwentyCoeff N : ℝ) - c₂ * (cuspTwentyCoeff' N : ℝ) with ha
  have hHA : ∀ x : ℝ, 0 ≤ x → x ≤ 1 / 2 →
      HasSum (fun N : ℕ => a N * x ^ N)
        (κ * (∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 20 - κ
          - Real.pi ^ 10 / 181440 * (twentySeriesO x - twentySeriesE x)
          - c₁ * ((∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 8 * TwelveSquares.etaSeriesR x)
          - c₂ * ((∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 2 * octSeriesR x)) := by
    intro x hx0 hx
    have hx1 : x < 1 := by linarith
    have h3 : HasSum (fun N : ℕ => (if N = 0 then κ else 0) * x ^ N) κ := by
      have := hasSum_ite_eq (0 : ℕ) κ
      refine this.congr_fun fun N => ?_
      by_cases hN : N = 0 <;> simp [hN]
    have := (((((hasSum_sumSquaresCount 20 hx0 hx1).mul_left κ).sub h3).sub
      ((hasSum_twentySum hx0 hx1).mul_left (Real.pi ^ 10 / 181440))).sub
      ((hasSum_cuspTwentySeries hx0 hx).mul_left c₁)).sub
      ((hasSum_cuspTwentySeries' hx0 hx).mul_left c₂)
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

theorem twentySquaresFormula_of_forall {κ c₁ c₂ : ℝ}
    (h : ∀ x : ℝ, 0 < x → x < 1 / 2 → κ * (∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 20 =
      κ + Real.pi ^ 10 / 181440 * (twentySeriesO x - twentySeriesE x) +
        c₁ * ((∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 8 * TwelveSquares.etaSeriesR x) +
        c₂ * ((∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 2 * octSeriesR x)) :
    TwentySquaresFormula := by
  have h1 := twenty_coeff_eq_zero h (N := 1) one_pos
  have h2 := twenty_coeff_eq_zero h (N := 2) two_pos
  have h3 := twenty_coeff_eq_zero h (N := 3) three_pos
  rw [sumSquaresCount_twenty_one, twentySum_one, cuspTwentyCoeff_one,
    cuspTwentyCoeff'_one] at h1
  rw [sumSquaresCount_twenty_two, twentySum_two, cuspTwentyCoeff_two,
    cuspTwentyCoeff'_two] at h2
  rw [sumSquaresCount_twenty_three, twentySum_three, cuspTwentyCoeff_three,
    cuspTwentyCoeff'_three] at h3
  push_cast at h1 h2 h3
  have hp : 0 < Real.pi ^ 10 := by positivity
  have hκ : κ = 31 * (Real.pi ^ 10 / 181440) / 8 := by linarith
  have hc₁ : c₁ = 162 * (Real.pi ^ 10 / 181440) := by linarith
  have hc₂ : c₂ = -2 * (Real.pi ^ 10 / 181440) := by linarith
  intro n hn
  have h4 := twenty_coeff_eq_zero h hn
  rw [hκ, hc₁, hc₂] at h4
  have h5 : Real.pi ^ 10 * (31 * (sumSquaresCount 20 n : ℝ) - (8 * (twentySum n : ℝ)
      + 1296 * (cuspTwentyCoeff n : ℝ) - 16 * (cuspTwentyCoeff' n : ℝ))) = 0 := by
    linear_combination 181440 * 8 * h4
  have h6 : 31 * (sumSquaresCount 20 n : ℝ) = 8 * (twentySum n : ℝ)
      + 1296 * (cuspTwentyCoeff n : ℝ) - 16 * (cuspTwentyCoeff' n : ℝ) := by
    rcases mul_eq_zero.1 h5 with h | h
    · exact absurd h hp.ne'
    · linarith
  exact_mod_cast h6

end NTKB.HardyWright
