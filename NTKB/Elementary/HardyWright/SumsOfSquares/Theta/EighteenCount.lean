/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.EighteenBounds
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TenCount
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.FourteenCount

/-!
# The formula for `r₁₈`: the comparison of coefficients

From an identity of generating functions with unknown constants `κ`, `c₁`, `c₂`, valid for
`0 < x < 1/2`, the coefficients of `xᴺ` are compared. The three unknown constants are determined
from the values at `N = 1, 2, 3` (`r₁₈ = 36, 612, 6528`), and `EighteenSquaresFormula` follows
(`eighteenSquaresFormula_of_forall`).
-/

open Finset Filter Topology Polynomial

namespace NTKB.HardyWright

namespace TwelveSquares

open Polynomial in
lemma coeff_pow12 (m j : ℕ) : ((1 - X ^ m : ℤ[X]) ^ 12).coeff j =
    ∑ i ∈ range 13, (if m * i = j then (-1 : ℤ) ^ i * (Nat.choose 12 i : ℤ) else 0) := by
  rw [sub_eq_add_neg, add_comm, add_pow]
  have := map_sum (lcoeff ℤ j)
    (fun i => (-X ^ m : ℤ[X]) ^ i * 1 ^ (12 - i) * (Nat.choose 12 i : ℤ[X])) (range (12 + 1))
  simp only [lcoeff_apply] at this
  rw [this]
  refine sum_congr rfl fun i _ => ?_
  have e : (-X ^ m : ℤ[X]) ^ i * 1 ^ (12 - i) * (Nat.choose 12 i : ℤ[X]) =
      C ((-1 : ℤ) ^ i * (Nat.choose 12 i : ℤ)) * X ^ (m * i) := by
    rw [one_pow, mul_one, neg_eq_neg_one_mul, mul_pow, ← pow_mul, mul_comm m i, C_mul]
    simp [mul_comm, mul_assoc]
  rw [e, coeff_C_mul, coeff_X_pow]
  by_cases h : j = m * i <;> simp [h, eq_comm]

lemma etaTwelveCoeff_three : etaTwelveCoeff 3 = -12 := by
  have h2 : prodCoeff twoSucc 12 2 = -12 := by
    unfold prodCoeff prodPoly
    simp only [prod_range_succ, prod_range_zero, one_mul]
    have e1 : twoSucc 0 = 2 := rfl
    have e2 : twoSucc 1 = 4 := rfl
    rw [e1, e2, coeff_mul]
    have : Finset.antidiagonal 2 = {(0, 2), (1, 1), (2, 0)} := by decide
    rw [this]
    simp [coeff_pow12, sum_range_succ]
  unfold etaTwelveCoeff
  simpa using h2

end TwelveSquares

/-- `A(x) = ∑_{k ≥ 1} ∑_{r ≥ 0} χ(r) r⁸ x^{rk}`.
  **Restriction:** the series is the mathematical object only where it converges (absolutely, for $|x| < 1$);
  elsewhere the value is $0$ by Lean's `tsum` convention, not an analytic continuation or the intended value. -/
noncomputable def eighteenSeriesA (x : ℝ) : ℝ :=
  ∑' k : ℕ, ∑' r : ℕ, chi4R r * (r : ℝ) ^ 8 * x ^ (r * (k + 1))

/-- `B(x) = ∑_{m ≥ 1} χ(m) ∑_{r ≥ 0} r⁸ x^{rm}`. -/
noncomputable def eighteenSeriesB (x : ℝ) : ℝ :=
  ∑' m : ℕ, chi4R (m + 1) * ∑' r : ℕ, (r : ℝ) ^ 8 * x ^ (r * (m + 1))

/-- The generating series of the coefficients `c₈(n)`.
  **Restriction:** the series is the mathematical object only where it converges (absolutely, for $|x| < 1$);
  elsewhere the value is $0$ by Lean's `tsum` convention, not an analytic continuation or the intended value. -/
noncomputable def octSeriesR (x : ℝ) : ℝ := ∑' n : ℕ, (octicCoeff n : ℝ) * x ^ n

/-- The divisor-sum coefficient `∑_{d ∣ N} χ(d) d⁸`. -/
noncomputable def eighteenCoeffA (N : ℕ) : ℝ := ∑ d ∈ N.divisors, chi4R d * (d : ℝ) ^ 8

/-- The divisor-sum coefficient `∑_{d ∣ N} χ(N/d) d⁸`. -/
noncomputable def eighteenCoeffB (N : ℕ) : ℝ := ∑ d ∈ N.divisors, chi4R (N / d) * (d : ℝ) ^ 8

lemma summable_eighteen_majorant {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    Summable fun p : ℕ × ℕ => (p.2 : ℝ) ^ 8 * x ^ (p.2 * (p.1 + 1)) := by
  have hM : Summable fun p : ℕ × ℕ => (p.1 : ℝ) ^ 8 * x ^ (p.1 * (p.2 + 1)) := by
    have hnn : ∀ p : ℕ × ℕ, 0 ≤ (p.1 : ℝ) ^ 8 * x ^ (p.1 * (p.2 + 1)) :=
      fun p => by positivity
    refine (summable_prod_of_nonneg hnn).2 ⟨fun r => ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos r with rfl | hr
      · simp
      · have hxr : x ^ r < 1 := pow_lt_one₀ hx0 hx hr.ne'
        refine ((summable_geometric_of_lt_one (pow_nonneg hx0 r) hxr).mul_left
          ((r : ℝ) ^ 8 * x ^ r)).congr fun k => ?_
        show _ = _
        rw [mul_add, mul_one, pow_add, pow_mul]; ring
    · have hb : Summable fun r : ℕ => (r : ℝ) ^ 8 * x ^ r * (1 - x)⁻¹ :=
        (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 8 (r := x)
          (by rw [Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx)).mul_right _
      have h1x : 0 < 1 - x := by linarith
      refine Summable.of_nonneg_of_le (fun r => tsum_nonneg fun k => hnn (r, k)) (fun r => ?_) hb
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · simp
      · have hxr : x ^ r < 1 := pow_lt_one₀ hx0 hx hr.ne'
        have hxr' : x ^ r ≤ x := pow_le_of_le_one hx0 hx.le hr.ne'
        have : ∑' k : ℕ, (r : ℝ) ^ 8 * x ^ (r * (k + 1)) =
            (r : ℝ) ^ 8 * x ^ r * (1 - x ^ r)⁻¹ := by
          rw [← tsum_geometric_of_lt_one (pow_nonneg hx0 r) hxr, ← tsum_mul_left]
          refine tsum_congr fun k => ?_
          rw [mul_add, mul_one, pow_add, pow_mul]; ring
        show ∑' k : ℕ, (r : ℝ) ^ 8 * x ^ (r * (k + 1)) ≤ _
        rw [this]
        exact mul_le_mul_of_nonneg_left (inv_anti₀ h1x (by linarith)) (by positivity)
  exact (Equiv.prodComm ℕ ℕ).summable_iff.mpr hM

lemma hasSum_eighteenCoeffA {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    HasSum (fun N : ℕ => eighteenCoeffA N * x ^ N) (eighteenSeriesA x) := by
  have hs : Summable fun p : ℕ × ℕ => chi4R p.2 * (p.2 : ℝ) ^ 8 * x ^ (p.2 * (p.1 + 1)) := by
    refine Summable.of_norm_bounded (summable_eighteen_majorant hx0 hx) fun p => ?_
    have h2 : (0 : ℝ) ≤ (p.2 : ℝ) ^ 8 * x ^ (p.2 * (p.1 + 1)) := by positivity
    rw [Real.norm_eq_abs, mul_assoc, abs_mul, abs_of_nonneg h2]
    have := abs_chi4R_le p.2
    nlinarith
  have := hasSum_divisor_rearr (fun r m => chi4R r * (r : ℝ) ^ 8 * x ^ (r * m)) (by simp) hs
  refine this.congr_fun fun N => ?_
  unfold eighteenCoeffA
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]

lemma hasSum_eighteenCoeffB {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    HasSum (fun N : ℕ => eighteenCoeffB N * x ^ N) (eighteenSeriesB x) := by
  have hs : Summable fun p : ℕ × ℕ =>
      chi4R (p.1 + 1) * ((p.2 : ℝ) ^ 8 * x ^ (p.2 * (p.1 + 1))) := by
    refine Summable.of_norm_bounded (summable_eighteen_majorant hx0 hx) fun p => ?_
    have h2 : (0 : ℝ) ≤ (p.2 : ℝ) ^ 8 * x ^ (p.2 * (p.1 + 1)) := by positivity
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2]
    have := abs_chi4R_le (p.1 + 1)
    nlinarith
  have := hasSum_divisor_rearr (fun r m => chi4R m * ((r : ℝ) ^ 8 * x ^ (r * m)))
    (by simp) hs
  have e : eighteenSeriesB x = ∑' k : ℕ, ∑' r : ℕ,
      chi4R (k + 1) * ((r : ℝ) ^ 8 * x ^ (r * (k + 1))) := by
    unfold eighteenSeriesB
    exact tsum_congr fun k => (tsum_mul_left).symm
  rw [e]
  refine this.congr_fun fun N => ?_
  unfold eighteenCoeffB
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
  ring

lemma hasSum_octSeriesR {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    HasSum (fun n : ℕ => (octicCoeff n : ℝ) * x ^ n) (octSeriesR x) := by
  have hs : Summable fun n : ℕ => (octicCoeff n : ℝ) * x ^ n := by
    refine Summable.of_norm ((summable_octicCoeff_abs hx0 hx).congr fun n => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hx0 n)]
  exact hs.hasSum

open TwelveSquares in
lemma hasSum_cuspEighteenSeries {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    HasSum (fun n : ℕ => (cuspEighteenCoeff n : ℝ) * x ^ n)
      ((∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 6 * etaSeriesR x) := by
  have hx1 : x < 1 := by linarith
  have hf := hasSum_sumSquaresCount 6 hx0 hx1
  have hg := hasSum_etaSeriesR hx0 hx1
  have hfn : Summable fun k : ℕ => ‖(sumSquaresCount 6 k : ℝ) * x ^ k‖ := by
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
  simp only [cuspEighteenCoeff]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have : x ^ n = x ^ k * x ^ (n - k) := by rw [← pow_add]; congr 1; omega
  rw [this]; ring

/-- `r_k(3) = 8 C(k, 3)`. -/
lemma sumSquaresCount_three_eq (k : ℕ) : sumSquaresCount k 3 = 8 * k.choose 3 := by
  induction k with
  | zero =>
    have : {z : Fin 0 → ℤ | ∑ i, z i ^ 2 = ((3 : ℕ) : ℤ)} = ∅ := by
      ext z; simp
    rw [sumSquaresCount, this, Set.ncard_empty]; simp
  | succ k ih =>
    rw [sumSquaresCount_succ_small k 3 (by norm_num) (by norm_num), ih]
    show 8 * k.choose 3 + 2 * sumSquaresCount k 2 = _
    have hc : (k + 1).choose 3 = k.choose 2 + k.choose 3 := Nat.choose_succ_succ' k 2
    rw [sumSquaresCount_two_eq, hc, mul_add]
    have h2 : k.choose 2 * 2 = k * (k - 1) := by
      rw [Nat.choose_two_right]
      exact Nat.div_mul_cancel (Nat.even_mul_pred_self k).two_dvd
    have : 2 * (2 * k * (k - 1)) = 8 * k.choose 2 := by
      have : 2 * k * (k - 1) = 2 * (k * (k - 1)) := by ring
      rw [this, ← h2]; ring
    omega

lemma sumSquaresCount_eighteen_one : sumSquaresCount 18 1 = 36 := by
  rw [sumSquaresCount_one_eq]

lemma sumSquaresCount_eighteen_two : sumSquaresCount 18 2 = 612 := by
  rw [sumSquaresCount_two_eq]

lemma sumSquaresCount_eighteen_three : sumSquaresCount 18 3 = 6528 := by
  rw [sumSquaresCount_three_eq]; decide

lemma cuspEighteenCoeff_one : cuspEighteenCoeff 1 = 1 := by
  simp [cuspEighteenCoeff, Finset.sum_range_succ, TwelveSquares.etaTwelveCoeff_zero,
    TwelveSquares.etaTwelveCoeff_one, sumSquaresCount_zero]

lemma cuspEighteenCoeff_two : cuspEighteenCoeff 2 = 12 := by
  have h1 : sumSquaresCount 6 1 = 12 := by rw [sumSquaresCount_one_eq]
  simp [cuspEighteenCoeff, Finset.sum_range_succ, TwelveSquares.etaTwelveCoeff_zero,
    TwelveSquares.etaTwelveCoeff_one, TwelveSquares.etaTwelveCoeff_two, sumSquaresCount_zero, h1]

lemma cuspEighteenCoeff_three : cuspEighteenCoeff 3 = 48 := by
  have h1 : sumSquaresCount 6 1 = 12 := by rw [sumSquaresCount_one_eq]
  have h2 : sumSquaresCount 6 2 = 60 := by rw [sumSquaresCount_two_eq]
  simp [cuspEighteenCoeff, Finset.sum_range_succ, TwelveSquares.etaTwelveCoeff_zero,
    TwelveSquares.etaTwelveCoeff_one, TwelveSquares.etaTwelveCoeff_two,
    TwelveSquares.etaTwelveCoeff_three, sumSquaresCount_zero, h1, h2]

lemma eighteenCoeffA_one : eighteenCoeffA 1 = 1 := by
  simp [eighteenCoeffA, chi4R]

lemma eighteenCoeffB_one : eighteenCoeffB 1 = 1 := by
  simp [eighteenCoeffB, chi4R]

lemma eighteenCoeffA_two : eighteenCoeffA 2 = 1 := by
  have : (Nat.divisors 2) = {1, 2} := by decide
  simp [eighteenCoeffA, this, chi4R]

lemma eighteenCoeffB_two : eighteenCoeffB 2 = 256 := by
  have : (Nat.divisors 2) = {1, 2} := by decide
  simp [eighteenCoeffB, this, chi4R]
  norm_num

lemma eighteenCoeffA_three : eighteenCoeffA 3 = -6560 := by
  have : (Nat.divisors 3) = {1, 3} := by decide
  simp [eighteenCoeffA, this, chi4R]
  norm_num

lemma eighteenCoeffB_three : eighteenCoeffB 3 = 6560 := by
  have : (Nat.divisors 3) = {1, 3} := by decide
  simp [eighteenCoeffB, this, chi4R]
  norm_num

lemma eighteen_coeff_eq_zero {κ c₁ c₂ : ℝ}
    (h : ∀ x : ℝ, 0 < x → x < 1 / 2 → κ * (∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 18 =
      κ + Real.pi ^ 9 / 20160 * eighteenSeriesB x + Real.pi ^ 9 / 5160960 * eighteenSeriesA x +
        c₁ * ((∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 6 * TwelveSquares.etaSeriesR x) +
        c₂ * octSeriesR x)
    {N : ℕ} (hN : 0 < N) :
    κ * (sumSquaresCount 18 N : ℝ) - Real.pi ^ 9 / 20160 * eighteenCoeffB N
      - Real.pi ^ 9 / 5160960 * eighteenCoeffA N - c₁ * (cuspEighteenCoeff N : ℝ)
      - c₂ * (octicCoeff N : ℝ) = 0 := by
  set a : ℕ → ℝ := fun N => κ * (sumSquaresCount 18 N : ℝ) - (if N = 0 then κ else 0)
    - Real.pi ^ 9 / 20160 * eighteenCoeffB N - Real.pi ^ 9 / 5160960 * eighteenCoeffA N
    - c₁ * (cuspEighteenCoeff N : ℝ) - c₂ * (octicCoeff N : ℝ) with ha
  have hHA : ∀ x : ℝ, 0 ≤ x → x ≤ 1 / 2 →
      HasSum (fun N : ℕ => a N * x ^ N)
        (κ * (∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 18 - κ - Real.pi ^ 9 / 20160 * eighteenSeriesB x
          - Real.pi ^ 9 / 5160960 * eighteenSeriesA x
          - c₁ * ((∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 6 * TwelveSquares.etaSeriesR x)
          - c₂ * octSeriesR x) := by
    intro x hx0 hx
    have hx1 : x < 1 := by linarith
    have h3 : HasSum (fun N : ℕ => (if N = 0 then κ else 0) * x ^ N) κ := by
      have := hasSum_ite_eq (0 : ℕ) κ
      refine this.congr_fun fun N => ?_
      by_cases hN : N = 0 <;> simp [hN]
    have := ((((((hasSum_sumSquaresCount 18 hx0 hx1).mul_left κ).sub h3).sub
      ((hasSum_eighteenCoeffB hx0 hx1).mul_left (Real.pi ^ 9 / 20160))).sub
      ((hasSum_eighteenCoeffA hx0 hx1).mul_left (Real.pi ^ 9 / 5160960))).sub
      ((hasSum_cuspEighteenSeries hx0 hx).mul_left c₁)).sub
      ((hasSum_octSeriesR hx0 hx1).mul_left c₂)
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

theorem eighteenSquaresFormula_of_forall {κ c₁ c₂ : ℝ}
    (h : ∀ x : ℝ, 0 < x → x < 1 / 2 → κ * (∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 18 =
      κ + Real.pi ^ 9 / 20160 * eighteenSeriesB x + Real.pi ^ 9 / 5160960 * eighteenSeriesA x +
        c₁ * ((∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 6 * TwelveSquares.etaSeriesR x) +
        c₂ * octSeriesR x) :
    EighteenSquaresFormula := by
  have h1 := eighteen_coeff_eq_zero h (N := 1) one_pos
  have h2 := eighteen_coeff_eq_zero h (N := 2) two_pos
  have h3 := eighteen_coeff_eq_zero h (N := 3) three_pos
  rw [sumSquaresCount_eighteen_one, eighteenCoeffA_one, eighteenCoeffB_one,
    cuspEighteenCoeff_one, octicCoeff_one] at h1
  rw [sumSquaresCount_eighteen_two, eighteenCoeffA_two, eighteenCoeffB_two,
    cuspEighteenCoeff_two, octicCoeff_two] at h2
  rw [sumSquaresCount_eighteen_three, eighteenCoeffA_three, eighteenCoeffB_three,
    cuspEighteenCoeff_three, octicCoeff_three] at h3
  push_cast at h1 h2 h3
  have hp : 0 < Real.pi ^ 9 := by positivity
  have hκ : κ = 1385 * (Real.pi ^ 9 / 20160) / 1024 := by linarith
  have hc₁ : c₁ = 48960 * (Real.pi ^ 9 / 20160) / 1024 := by linarith
  have hc₂ : c₂ = -32 * (Real.pi ^ 9 / 20160) / 1024 := by linarith
  intro n hn
  have h4 := eighteen_coeff_eq_zero h hn
  rw [hκ, hc₁, hc₂] at h4
  have hA : (eighteenSumA n : ℝ) = eighteenCoeffA n := by
    simp [eighteenSumA, eighteenCoeffA, chi4R]
  have hB : (eighteenSumB n : ℝ) = eighteenCoeffB n := by
    simp [eighteenSumB, eighteenCoeffB, chi4R]
  have h5 : Real.pi ^ 9 * (1385 * (sumSquaresCount 18 n : ℝ) - (4 * ((eighteenSumA n : ℝ)
      + 256 * (eighteenSumB n : ℝ)) + 48960 * (cuspEighteenCoeff n : ℝ)
      - 32 * (octicCoeff n : ℝ))) = 0 := by
    rw [hA, hB]; linear_combination 20160 * 1024 * h4
  have h6 : 1385 * (sumSquaresCount 18 n : ℝ) = 4 * ((eighteenSumA n : ℝ)
      + 256 * (eighteenSumB n : ℝ)) + 48960 * (cuspEighteenCoeff n : ℝ)
      - 32 * (octicCoeff n : ℝ) := by
    rcases mul_eq_zero.1 h5 with h | h
    · exact absurd h hp.ne'
    · linarith
  exact_mod_cast h6

end NTKB.HardyWright
