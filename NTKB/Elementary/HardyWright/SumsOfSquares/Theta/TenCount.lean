/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.SixCount
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TenStatement

/-!
# Liouville's formula for `r₁₀`: the comparison of coefficients

From an identity of generating functions with unknown constants `κ` and `c`, valid for
`0 < x < 1/2`, the coefficients of `xᴺ` are compared. The two unknown constants are determined from
the values at `N = 1` and `N = 2`, and the statement `LiouvilleTenSquares` follows.
-/

open Finset Filter Topology

namespace NTKB.HardyWright

/-- `A(x) = ∑_{k ≥ 1} ∑_{r ≥ 0} χ(r) r⁴ x^{rk}`.
  **Restriction:** the series is the mathematical object only where it converges (absolutely, for $|x| < 1$);
  elsewhere the value is $0$ by Lean's `tsum` convention, not an analytic continuation or the intended value. -/
noncomputable def tenSeriesA (x : ℝ) : ℝ :=
  ∑' k : ℕ, ∑' r : ℕ, chi4R r * (r : ℝ) ^ 4 * x ^ (r * (k + 1))

/-- `B(x) = ∑_{m ≥ 1} χ(m) ∑_{r ≥ 0} r⁴ x^{rm}`. -/
noncomputable def tenSeriesB (x : ℝ) : ℝ :=
  ∑' m : ℕ, chi4R (m + 1) * ∑' r : ℕ, (r : ℝ) ^ 4 * x ^ (r * (m + 1))

/-- The generating series of the cusp coefficients.
  **Restriction:** the series is the mathematical object only where it converges (absolutely, for $|x| < 1$);
  elsewhere the value is $0$ by Lean's `tsum` convention, not an analytic continuation or the intended value. -/
noncomputable def cuspSeriesR (x : ℝ) : ℝ := ∑' n : ℕ, (liouvilleCusp n : ℝ) * x ^ n

/-- The divisor-sum coefficient `∑_{d ∣ N} χ(d) d⁴`. -/
noncomputable def tenCoeffA (N : ℕ) : ℝ := ∑ d ∈ N.divisors, chi4R d * (d : ℝ) ^ 4

/-- The divisor-sum coefficient `∑_{d ∣ N} χ(N/d) d⁴`. -/
noncomputable def tenCoeffB (N : ℕ) : ℝ := ∑ d ∈ N.divisors, chi4R (N / d) * (d : ℝ) ^ 4

lemma summable_ten_majorant {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    Summable fun p : ℕ × ℕ => (p.2 : ℝ) ^ 4 * x ^ (p.2 * (p.1 + 1)) := by
  have hM : Summable fun p : ℕ × ℕ => (p.1 : ℝ) ^ 4 * x ^ (p.1 * (p.2 + 1)) := by
    have hnn : ∀ p : ℕ × ℕ, 0 ≤ (p.1 : ℝ) ^ 4 * x ^ (p.1 * (p.2 + 1)) :=
      fun p => by positivity
    refine (summable_prod_of_nonneg hnn).2 ⟨fun r => ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos r with rfl | hr
      · simp
      · have hxr : x ^ r < 1 := pow_lt_one₀ hx0 hx hr.ne'
        refine ((summable_geometric_of_lt_one (pow_nonneg hx0 r) hxr).mul_left
          ((r : ℝ) ^ 4 * x ^ r)).congr fun k => ?_
        show _ = _
        rw [mul_add, mul_one, pow_add, pow_mul]; ring
    · have hb : Summable fun r : ℕ => (r : ℝ) ^ 4 * x ^ r * (1 - x)⁻¹ :=
        (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 4 (r := x)
          (by rw [Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx)).mul_right _
      have h1x : 0 < 1 - x := by linarith
      refine Summable.of_nonneg_of_le (fun r => tsum_nonneg fun k => hnn (r, k)) (fun r => ?_) hb
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · simp
      · have hxr : x ^ r < 1 := pow_lt_one₀ hx0 hx hr.ne'
        have hxr' : x ^ r ≤ x := pow_le_of_le_one hx0 hx.le hr.ne'
        have : ∑' k : ℕ, (r : ℝ) ^ 4 * x ^ (r * (k + 1)) =
            (r : ℝ) ^ 4 * x ^ r * (1 - x ^ r)⁻¹ := by
          rw [← tsum_geometric_of_lt_one (pow_nonneg hx0 r) hxr, ← tsum_mul_left]
          refine tsum_congr fun k => ?_
          rw [mul_add, mul_one, pow_add, pow_mul]; ring
        show ∑' k : ℕ, (r : ℝ) ^ 4 * x ^ (r * (k + 1)) ≤ _
        rw [this]
        exact mul_le_mul_of_nonneg_left (inv_anti₀ h1x (by linarith)) (by positivity)
  exact (Equiv.prodComm ℕ ℕ).summable_iff.mpr hM

lemma hasSum_tenCoeffA {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    HasSum (fun N : ℕ => tenCoeffA N * x ^ N) (tenSeriesA x) := by
  have hs : Summable fun p : ℕ × ℕ => chi4R p.2 * (p.2 : ℝ) ^ 4 * x ^ (p.2 * (p.1 + 1)) := by
    refine Summable.of_norm_bounded (summable_ten_majorant hx0 hx) fun p => ?_
    have h2 : (0 : ℝ) ≤ (p.2 : ℝ) ^ 4 * x ^ (p.2 * (p.1 + 1)) := by positivity
    rw [Real.norm_eq_abs, mul_assoc, abs_mul, abs_of_nonneg h2]
    have := abs_chi4R_le p.2
    nlinarith
  have := hasSum_divisor_rearr (fun r m => chi4R r * (r : ℝ) ^ 4 * x ^ (r * m)) (by simp) hs
  refine this.congr_fun fun N => ?_
  unfold tenCoeffA
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]

lemma hasSum_tenCoeffB {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    HasSum (fun N : ℕ => tenCoeffB N * x ^ N) (tenSeriesB x) := by
  have hs : Summable fun p : ℕ × ℕ =>
      chi4R (p.1 + 1) * ((p.2 : ℝ) ^ 4 * x ^ (p.2 * (p.1 + 1))) := by
    refine Summable.of_norm_bounded (summable_ten_majorant hx0 hx) fun p => ?_
    have h2 : (0 : ℝ) ≤ (p.2 : ℝ) ^ 4 * x ^ (p.2 * (p.1 + 1)) := by positivity
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2]
    have := abs_chi4R_le (p.1 + 1)
    nlinarith
  have := hasSum_divisor_rearr (fun r m => chi4R m * ((r : ℝ) ^ 4 * x ^ (r * m)))
    (by simp) hs
  have e : tenSeriesB x = ∑' k : ℕ, ∑' r : ℕ,
      chi4R (k + 1) * ((r : ℝ) ^ 4 * x ^ (r * (k + 1))) := by
    unfold tenSeriesB
    exact tsum_congr fun k => (tsum_mul_left).symm
  rw [e]
  refine this.congr_fun fun N => ?_
  unfold tenCoeffB
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
  ring

lemma abs_liouvilleCusp_le (n : ℕ) :
    |(liouvilleCusp n : ℝ)| ≤ 3 * (n : ℝ) ^ 2 * (2 * n + 1) ^ 2 := by
  set S := ((Finset.Icc (-(n : ℤ)) n) ×ˢ (Finset.Icc (-(n : ℤ)) n)).filter
      (fun v : ℤ × ℤ => v.1 ^ 2 + v.2 ^ 2 = n) with hS
  have hcard : (S.card : ℝ) ≤ (2 * n + 1) ^ 2 := by
    have h1 : S.card ≤ ((Finset.Icc (-(n : ℤ)) n) ×ˢ (Finset.Icc (-(n : ℤ)) n)).card :=
      Finset.card_filter_le _ _
    rw [Finset.card_product, Int.card_Icc] at h1
    have : ((n : ℤ) + 1 - -(n : ℤ)).toNat = 2 * n + 1 := by omega
    rw [this] at h1
    exact_mod_cast (h1.trans_eq (by ring))
  have hterm : ∀ v ∈ S,
      |((v.1 ^ 4 - 6 * v.1 ^ 2 * v.2 ^ 2 + v.2 ^ 4 : ℤ) : ℝ)| ≤ (n : ℝ) ^ 2 := by
    intro v hv
    have h : v.1 ^ 2 + v.2 ^ 2 = (n : ℤ) := (Finset.mem_filter.1 hv).2
    have h' : ((v.1 : ℝ)) ^ 2 + (v.2 : ℝ) ^ 2 = n := by exact_mod_cast h
    push_cast
    rw [abs_le]
    have c : (v.1 : ℝ) ^ 4 - 6 * (v.1 : ℝ) ^ 2 * (v.2 : ℝ) ^ 2 + (v.2 : ℝ) ^ 4
        = (n : ℝ) ^ 2 - 8 * ((v.1 : ℝ) ^ 2 * (v.2 : ℝ) ^ 2) := by
      rw [← h']; ring
    have d : 0 ≤ (v.1 : ℝ) ^ 2 * (v.2 : ℝ) ^ 2 := by positivity
    have e : 4 * ((v.1 : ℝ) ^ 2 * (v.2 : ℝ) ^ 2) ≤ (n : ℝ) ^ 2 := by
      rw [← h']; nlinarith [sq_nonneg ((v.1 : ℝ) ^ 2 - (v.2 : ℝ) ^ 2)]
    rw [c]
    constructor <;> nlinarith
  unfold liouvilleCusp
  rw [← hS, Int.cast_sum]
  have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  calc |∑ v ∈ S, (((v.1 ^ 4 - 6 * v.1 ^ 2 * v.2 ^ 2 + v.2 ^ 4 : ℤ)) : ℝ)|
      ≤ ∑ v ∈ S, |(((v.1 ^ 4 - 6 * v.1 ^ 2 * v.2 ^ 2 + v.2 ^ 4 : ℤ)) : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v ∈ S, (n : ℝ) ^ 2 := Finset.sum_le_sum hterm
    _ = S.card * (n : ℝ) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * n + 1) ^ 2 * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hcard hn2
    _ ≤ _ := by nlinarith [mul_nonneg hn2 (sq_nonneg (2 * (n : ℝ) + 1))]


lemma hasSum_cuspSeriesR {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    HasSum (fun n : ℕ => (liouvilleCusp n : ℝ) * x ^ n) (cuspSeriesR x) := by
  have hn : ‖x‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx
  have h2 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hn
  have h3 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 3 hn
  have h4 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 4 hn
  have hb : Summable fun n : ℕ => 12 * ((n : ℝ) ^ 4 * x ^ n) + 12 * ((n : ℝ) ^ 3 * x ^ n)
      + 3 * ((n : ℝ) ^ 2 * x ^ n) :=
    ((h4.mul_left 12).add (h3.mul_left 12)).add (h2.mul_left 3)
  refine (Summable.of_norm_bounded hb fun n => ?_).hasSum
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hx0 n)]
  have := mul_le_mul_of_nonneg_right (abs_liouvilleCusp_le n) (pow_nonneg hx0 n)
  refine this.trans (le_of_eq ?_)
  ring

/-- The solution set of `∑ zᵢ² = m` is finite. -/
lemma finite_sumSquares_set (k m : ℕ) : {z : Fin k → ℤ | ∑ i, z i ^ 2 = (m : ℤ)}.Finite :=
  (latticePoints k m).finite_toSet.subset fun z hz => by
    rw [mem_coe, mem_latticePoints]; exact le_of_eq (by simpa using hz)

/-- Prepend a first coordinate to a vector. -/
def consInt {k : ℕ} (t : ℤ) (w : Fin k → ℤ) : Fin (k + 1) → ℤ := Fin.cons t w

lemma consInt_injective {k : ℕ} (t : ℤ) : Function.Injective (consInt (k := k) t) :=
  fun a b h => by simpa [consInt] using congrArg Fin.tail h

/-- Dimension recursion for `r_k(n)`, `n = 1, 2, 3`: split off the first coordinate
`t ∈ {-1, 0, 1}`. -/
lemma sumSquaresCount_succ_small (k n : ℕ) (h1 : 1 ≤ n) (h4 : n < 4) :
    sumSquaresCount (k + 1) n = sumSquaresCount k n + 2 * sumSquaresCount k (n - 1) := by
  have hset : {z : Fin (k + 1) → ℤ | ∑ i, z i ^ 2 = (n : ℤ)} =
      (consInt 0 '' {w : Fin k → ℤ | ∑ i, w i ^ 2 = (n : ℤ)} ∪
        consInt 1 '' {w : Fin k → ℤ | ∑ i, w i ^ 2 = ((n - 1 : ℕ) : ℤ)}) ∪
        consInt (-1) '' {w : Fin k → ℤ | ∑ i, w i ^ 2 = ((n - 1 : ℕ) : ℤ)} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_image, consInt]
    constructor
    · intro h
      rw [Fin.sum_univ_succ] at h
      have hz : z 0 ^ 2 ≤ n := by
        have : 0 ≤ ∑ i : Fin k, z i.succ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
        linarith
      have : -1 ≤ z 0 ∧ z 0 ≤ 1 := by constructor <;> nlinarith
      have hc : z = consInt (z 0) (Fin.tail z) := (Fin.cons_self_tail z).symm
      have : z 0 = -1 ∨ z 0 = 0 ∨ z 0 = 1 := by omega
      rcases this with e | e | e
      · refine Or.inr ⟨Fin.tail z, ?_, by rw [hc, e]; rfl⟩
        rw [e] at h; push_cast [Nat.cast_sub h1]; simp only [Fin.tail]; linarith
      · refine Or.inl (Or.inl ⟨Fin.tail z, ?_, by rw [hc, e]; rfl⟩)
        rw [e] at h; simp only [Fin.tail]; linarith
      · refine Or.inl (Or.inr ⟨Fin.tail z, ?_, by rw [hc, e]; rfl⟩)
        rw [e] at h; push_cast [Nat.cast_sub h1]; simp only [Fin.tail]; linarith
    · rintro ((⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩) | ⟨w, hw, rfl⟩)
      · rw [Fin.sum_univ_succ]; simp [hw]
      · rw [Fin.sum_univ_succ]; simp; push_cast [Nat.cast_sub h1] at hw; linarith
      · rw [Fin.sum_univ_succ]; simp; push_cast [Nat.cast_sub h1] at hw; linarith
  have f0 := finite_sumSquares_set k n
  have f1 := finite_sumSquares_set k (n - 1)
  have d1 : Disjoint (consInt 0 '' {w : Fin k → ℤ | ∑ i, w i ^ 2 = (n : ℤ)})
      (consInt 1 '' {w : Fin k → ℤ | ∑ i, w i ^ 2 = ((n - 1 : ℕ) : ℤ)}) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, _, rfl⟩ ⟨b, _, hb⟩
    have := congrFun hb 0
    simp [consInt] at this
  have d2 : Disjoint (consInt 0 '' {w : Fin k → ℤ | ∑ i, w i ^ 2 = (n : ℤ)} ∪
      consInt 1 '' {w : Fin k → ℤ | ∑ i, w i ^ 2 = ((n - 1 : ℕ) : ℤ)})
      (consInt (-1) '' {w : Fin k → ℤ | ∑ i, w i ^ 2 = ((n - 1 : ℕ) : ℤ)}) := by
    rw [Set.disjoint_left]
    rintro _ (⟨a, _, rfl⟩ | ⟨a, _, rfl⟩) ⟨b, _, hb⟩ <;>
    · have := congrFun hb 0
      simp [consInt] at this
  unfold sumSquaresCount
  rw [hset, Set.ncard_union_eq d2 ((f0.image _).union (f1.image _)) (f1.image _),
    Set.ncard_union_eq d1 (f0.image _) (f1.image _),
    Set.ncard_image_of_injective _ (consInt_injective _),
    Set.ncard_image_of_injective _ (consInt_injective _),
    Set.ncard_image_of_injective _ (consInt_injective _)]
  ring

/-- `r_k(1) = 2k`. -/
lemma sumSquaresCount_one_eq (k : ℕ) : sumSquaresCount k 1 = 2 * k := by
  induction k with
  | zero =>
    have : {z : Fin 0 → ℤ | ∑ i, z i ^ 2 = ((1 : ℕ) : ℤ)} = ∅ := by
      ext z; simp
    rw [sumSquaresCount, this, Set.ncard_empty]
  | succ k ih =>
    rw [sumSquaresCount_succ_small k 1 le_rfl (by norm_num), ih]
    simp [sumSquaresCount_zero]; ring

/-- `r_k(2) = 2k(k-1)`. -/
lemma sumSquaresCount_two_eq (k : ℕ) : sumSquaresCount k 2 = 2 * k * (k - 1) := by
  induction k with
  | zero =>
    have : {z : Fin 0 → ℤ | ∑ i, z i ^ 2 = ((2 : ℕ) : ℤ)} = ∅ := by
      ext z; simp
    rw [sumSquaresCount, this, Set.ncard_empty]
  | succ k ih =>
    rw [sumSquaresCount_succ_small k 2 (by norm_num) (by norm_num), ih]
    show 2 * k * (k - 1) + 2 * sumSquaresCount k 1 = _
    rw [sumSquaresCount_one_eq]
    rcases k with _ | k
    · simp
    · simp; ring

lemma sumSquaresCount_ten_one : sumSquaresCount 10 1 = 20 := by
  rw [sumSquaresCount_one_eq]

lemma sumSquaresCount_ten_two : sumSquaresCount 10 2 = 180 := by
  rw [sumSquaresCount_two_eq]

lemma liouvilleCusp_two : liouvilleCusp 2 = -16 := by decide

lemma ten_coeff_eq_zero {κ c : ℝ}
    (h : ∀ x : ℝ, 0 < x → x < 1 / 2 → κ * (∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 10 =
      κ + Real.pi ^ 5 / 12 * tenSeriesB x + Real.pi ^ 5 / 192 * tenSeriesA x + c * cuspSeriesR x)
    {N : ℕ} (hN : 0 < N) :
    κ * (sumSquaresCount 10 N : ℝ) - Real.pi ^ 5 / 12 * tenCoeffB N
      - Real.pi ^ 5 / 192 * tenCoeffA N - c * (liouvilleCusp N : ℝ) = 0 := by
  set a : ℕ → ℝ := fun N => κ * (sumSquaresCount 10 N : ℝ) - (if N = 0 then κ else 0)
    - Real.pi ^ 5 / 12 * tenCoeffB N - Real.pi ^ 5 / 192 * tenCoeffA N
    - c * (liouvilleCusp N : ℝ) with ha
  have hHA : ∀ x : ℝ, 0 ≤ x → x < 1 →
      HasSum (fun N : ℕ => a N * x ^ N)
        (κ * (∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 10 - κ - Real.pi ^ 5 / 12 * tenSeriesB x
          - Real.pi ^ 5 / 192 * tenSeriesA x - c * cuspSeriesR x) := by
    intro x hx0 hx
    have h3 : HasSum (fun N : ℕ => (if N = 0 then κ else 0) * x ^ N) κ := by
      have := hasSum_ite_eq (0 : ℕ) κ
      refine this.congr_fun fun N => ?_
      by_cases hN : N = 0 <;> simp [hN]
    have := (((((hasSum_sumSquaresCount 10 hx0 hx).mul_left κ).sub h3).sub
      ((hasSum_tenCoeffB hx0 hx).mul_left (Real.pi ^ 5 / 12))).sub
      ((hasSum_tenCoeffA hx0 hx).mul_left (Real.pi ^ 5 / 192))).sub
      ((hasSum_cuspSeriesR hx0 hx).mul_left c)
    refine this.congr_fun fun N => ?_
    simp only [ha]; ring
  have hzero : ∀ x : ℝ, 0 < x → x < 1 / 2 → ∑' N, a N * x ^ N = 0 := by
    intro x hx0 hx
    rw [(hHA x hx0.le (by linarith)).tsum_eq, h x hx0 hx]; ring
  have hs : Summable fun N => |a N| * (1 / 2 : ℝ) ^ N := by
    have := (hHA (1 / 2) (by norm_num) (by norm_num)).summable.abs
    refine this.congr fun N => ?_
    rw [abs_mul, abs_of_pos (show (0 : ℝ) < (1 / 2) ^ N by positivity)]
  have hn0 := eq_zero_of_tsum_pow_eq_zero hs hzero N
  simp only [ha, if_neg hN.ne'] at hn0
  linarith

lemma tenCoeffA_one : tenCoeffA 1 = 1 := by
  simp [tenCoeffA, chi4R]

lemma tenCoeffB_one : tenCoeffB 1 = 1 := by
  simp [tenCoeffB, chi4R]

lemma tenCoeffA_two : tenCoeffA 2 = 1 := by
  have : (Nat.divisors 2) = {1, 2} := by decide
  simp [tenCoeffA, this, chi4R]

lemma tenCoeffB_two : tenCoeffB 2 = 16 := by
  have : (Nat.divisors 2) = {1, 2} := by decide
  simp [tenCoeffB, this, chi4R]
  norm_num

theorem liouvilleTenSquares_of_forall {κ c : ℝ}
    (h : ∀ x : ℝ, 0 < x → x < 1 / 2 → κ * (∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 10 =
      κ + Real.pi ^ 5 / 12 * tenSeriesB x + Real.pi ^ 5 / 192 * tenSeriesA x + c * cuspSeriesR x) :
    LiouvilleTenSquares := by
  have h1 := ten_coeff_eq_zero h (N := 1) one_pos
  have h2 := ten_coeff_eq_zero h (N := 2) two_pos
  rw [sumSquaresCount_ten_one, tenCoeffA_one, tenCoeffB_one, liouvilleCusp_one] at h1
  rw [sumSquaresCount_ten_two, tenCoeffA_two, tenCoeffB_two, liouvilleCusp_two] at h2
  push_cast at h1 h2
  have hκ : κ = 5 * Real.pi ^ 5 / 768 := by linarith
  have hc : c = Real.pi ^ 5 / 96 := by linarith
  intro n hn
  have h3 := ten_coeff_eq_zero h hn
  rw [hκ, hc] at h3
  have hp : 0 < Real.pi ^ 5 := by positivity
  have hA : (liouvilleSumA n : ℝ) = tenCoeffA n := by
    simp [liouvilleSumA, tenCoeffA, chi4R]
  have hB : (liouvilleSumB n : ℝ) = tenCoeffB n := by
    simp [liouvilleSumB, tenCoeffB, chi4R]
  have h4 : Real.pi ^ 5 * (5 * (sumSquaresCount 10 n : ℝ) - (4 * (liouvilleSumA n : ℝ)
      + 64 * (liouvilleSumB n : ℝ) + 8 * (liouvilleCusp n : ℝ))) = 0 := by
    rw [hA, hB]; linear_combination 768 * h3
  have h5 : 5 * (sumSquaresCount 10 n : ℝ) = 4 * (liouvilleSumA n : ℝ)
      + 64 * (liouvilleSumB n : ℝ) + 8 * (liouvilleCusp n : ℝ) := by
    rcases mul_eq_zero.1 h4 with h | h
    · exact absurd h hp.ne'
    · linarith
  exact_mod_cast h5

end NTKB.HardyWright
