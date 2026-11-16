/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Products `∏ (1 - q^{e(m)})^k` as power series

For an exponent sequence `e` with `e m ≥ m + 1` we define the coefficients of the formal
product `∏_{m ≥ 0} (1 - X^{e m})^k` by truncation: the `n`-th coefficient of the finite product
over `m < N` does not change once `N ≥ n`, because the factors with `m ≥ n` are `1 + O(X^{n+1})`.

To pass to the limit for `|q| < 1` we use the majorant `∏_{m < N} (1 + X^{e m})^k`, which has
nonnegative coefficients dominating those of the truncated products.  Evaluating at `ρ ∈ [0, 1)`
and using `1 + t ≤ exp t` bounds every coefficient: `|c_n| ρ^n ≤ exp (k / (1 - ρ))`.  This gives
absolute summability (comparison with a geometric series at a larger radius), and, together with
the dominated convergence theorem for series (`tendsto_tsum_of_dominated_convergence`) applied
to the truncated products, the identification of the power series with the infinite product.
-/

open Polynomial Finset Filter Topology

noncomputable section

namespace NTKB.HardyWright.TwelveSquares

/-- The truncated product `∏_{m < N} (1 - X^{e m})^k`. -/
def prodPoly (e : ℕ → ℕ) (k N : ℕ) : ℤ[X] := ∏ m ∈ range N, (1 - X ^ e m) ^ k

/-- The `n`-th coefficient of `∏_{m ≥ 0} (1 - X^{e m})^k` (when `e m ≥ m + 1`, the truncation at
`n` factors suffices). -/
def prodCoeff (e : ℕ → ℕ) (k n : ℕ) : ℤ := (prodPoly e k n).coeff n

theorem prodPoly_coeff_eq {e : ℕ → ℕ} (he : ∀ m, m + 1 ≤ e m) (k : ℕ) {n N : ℕ} (hN : n ≤ N) :
    (prodPoly e k N).coeff n = prodCoeff e k n := by
  induction N, hN using Nat.le_induction with
  | base => rfl
  | succ N hN ih =>
    rw [← ih]
    obtain ⟨T, hT⟩ : (1 - X ^ e N : ℤ[X]) - 1 ∣ (1 - X ^ e N) ^ k - 1 ^ k :=
      sub_dvd_pow_sub_pow _ _ _
    have h2 : (1 - X ^ e N : ℤ[X]) ^ k = 1 + X ^ e N * (-T) := by
      rw [one_pow] at hT
      linear_combination hT
    have h3 : prodPoly e k (N + 1) = prodPoly e k N * (1 - X ^ e N) ^ k := prod_range_succ _ _
    have h4 : ¬ e N ≤ n := by have := he N; omega
    rw [h3, h2, mul_add, mul_one, coeff_add, mul_left_comm, coeff_X_pow_mul']
    simp [h4]

/-- Coefficientwise domination `|A_i| ≤ A'_i`. -/
def CoeffDom (A A' : ℤ[X]) : Prop := ∀ i, |A.coeff i| ≤ A'.coeff i

lemma CoeffDom.mul {A A' B B' : ℤ[X]} (hA : CoeffDom A A') (hB : CoeffDom B B') :
    CoeffDom (A * B) (A' * B') := by
  intro n
  rw [coeff_mul, coeff_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  rw [abs_mul]
  exact mul_le_mul (hA _) (hB _) (abs_nonneg _) ((abs_nonneg _).trans (hA _))

lemma CoeffDom.pow {A A' : ℤ[X]} (hA : CoeffDom A A') (k : ℕ) : CoeffDom (A ^ k) (A' ^ k) := by
  induction k with
  | zero =>
    intro i
    simp only [pow_zero, coeff_one]
    split_ifs <;> simp
  | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul hA

lemma coeffDom_factor (a : ℕ) : CoeffDom (1 - X ^ a : ℤ[X]) (1 + X ^ a) := by
  intro i
  simp only [coeff_sub, coeff_add, coeff_one, coeff_X_pow]
  split_ifs <;> simp

/-- The majorant `∏_{m < N} (1 + X^{e m})^k`. -/
def majPoly (e : ℕ → ℕ) (k N : ℕ) : ℤ[X] := ∏ m ∈ range N, (1 + X ^ e m) ^ k

lemma coeffDom_prodPoly (e : ℕ → ℕ) (k N : ℕ) : CoeffDom (prodPoly e k N) (majPoly e k N) := by
  induction N with
  | zero =>
    intro i
    simp only [prodPoly, majPoly, prod_range_zero, coeff_one]
    split_ifs <;> simp
  | succ N ih =>
    unfold prodPoly majPoly at *
    rw [prod_range_succ, prod_range_succ]
    exact ih.mul ((coeffDom_factor _).pow k)

lemma aeval_majPoly (e : ℕ → ℕ) (k N : ℕ) (ρ : ℝ) :
    aeval ρ (majPoly e k N) = ∏ m ∈ range N, (1 + ρ ^ e m) ^ k := by
  simp [majPoly, map_prod]

lemma maj_eval_le {e : ℕ → ℕ} (he : ∀ m, m + 1 ≤ e m) (k N : ℕ) {ρ : ℝ} (h0 : 0 ≤ ρ)
    (h1 : ρ < 1) : (∏ m ∈ range N, (1 + ρ ^ e m) ^ k) ≤ Real.exp (k * (1 - ρ)⁻¹) := by
  have hgeo : ∑ m ∈ range N, ρ ^ m ≤ (1 - ρ)⁻¹ := by
    have := (summable_geometric_of_lt_one h0 h1).sum_le_tsum (range N)
      (fun m _ => pow_nonneg h0 m)
    rwa [tsum_geometric_of_lt_one h0 h1] at this
  calc ∏ m ∈ range N, (1 + ρ ^ e m) ^ k ≤ ∏ m ∈ range N, Real.exp (k * ρ ^ m) := by
        refine Finset.prod_le_prod₀ (fun m _ => by positivity) (fun m _ => ?_)
        have h1' : 1 + ρ ^ e m ≤ Real.exp (ρ ^ e m) := by
          linarith [Real.add_one_le_exp (ρ ^ e m)]
        calc (1 + ρ ^ e m) ^ k ≤ (Real.exp (ρ ^ e m)) ^ k :=
              pow_le_pow_left₀ (by positivity) h1' k
          _ = Real.exp (k * ρ ^ e m) := by rw [← Real.exp_nat_mul]
          _ ≤ Real.exp (k * ρ ^ m) := by
              apply Real.exp_le_exp.2
              apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg k)
              exact pow_le_pow_of_le_one h0 h1.le (by have := he m; omega)
    _ = Real.exp (∑ m ∈ range N, k * ρ ^ m) := (Real.exp_sum _ _).symm
    _ ≤ _ := by
        rw [← mul_sum]
        exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hgeo (Nat.cast_nonneg k))

lemma coeff_pow_le_aeval {A : ℤ[X]} (hA : ∀ i, 0 ≤ A.coeff i) (n : ℕ) {ρ : ℝ} (h0 : 0 ≤ ρ) :
    (A.coeff n : ℝ) * ρ ^ n ≤ aeval ρ A := by
  rw [aeval_eq_sum_range' (n := A.natDegree + n + 1) (by omega)]
  have hmem : n ∈ range (A.natDegree + n + 1) := by simp
  have := Finset.single_le_sum (f := fun i => A.coeff i • ρ ^ i)
    (fun i _ => by
      rw [zsmul_eq_mul]
      exact mul_nonneg (Int.cast_nonneg (hA i)) (pow_nonneg h0 i)) hmem
  simpa [zsmul_eq_mul] using this

lemma coeff_bound {e : ℕ → ℕ} (he : ∀ m, m + 1 ≤ e m) (k N n : ℕ) {ρ : ℝ} (h0 : 0 ≤ ρ)
    (h1 : ρ < 1) :
    |((prodPoly e k N).coeff n : ℝ)| * ρ ^ n ≤ Real.exp (k * (1 - ρ)⁻¹) := by
  have hnn : ∀ i, 0 ≤ (majPoly e k N).coeff i :=
    fun i => (abs_nonneg _).trans (coeffDom_prodPoly e k N i)
  have h2 : |((prodPoly e k N).coeff n : ℝ)| ≤ ((majPoly e k N).coeff n : ℝ) := by
    rw [← Int.cast_abs]; exact_mod_cast coeffDom_prodPoly e k N n
  calc _ ≤ ((majPoly e k N).coeff n : ℝ) * ρ ^ n :=
        mul_le_mul_of_nonneg_right h2 (pow_nonneg h0 n)
    _ ≤ aeval ρ (majPoly e k N) := coeff_pow_le_aeval hnn n h0
    _ ≤ _ := by rw [aeval_majPoly]; exact maj_eval_le he k N h0 h1

lemma coeff_bound' {e : ℕ → ℕ} (he : ∀ m, m + 1 ≤ e m) (k N n : ℕ) {r ρ : ℝ} (hr : 0 ≤ r)
    (hrρ : r < ρ) (h1 : ρ < 1) :
    |((prodPoly e k N).coeff n : ℝ)| * r ^ n ≤ Real.exp (k * (1 - ρ)⁻¹) * (r / ρ) ^ n := by
  have hρ : 0 < ρ := hr.trans_lt hrρ
  have h2 : ρ * (r / ρ) = r := by field_simp
  have h3 : r ^ n = ρ ^ n * (r / ρ) ^ n := by rw [← mul_pow, h2]
  rw [h3, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (coeff_bound he k N n hρ.le h1) (by positivity)

theorem summable_prodCoeff {e : ℕ → ℕ} (he : ∀ m, m + 1 ≤ e m) (k : ℕ) {ρ : ℝ} (h0 : 0 ≤ ρ)
    (h1 : ρ < 1) :
    Summable fun n => |(prodCoeff e k n : ℝ)| * ρ ^ n := by
  have hρ' : ρ < (1 + ρ) / 2 := by linarith
  have hρ'1 : (1 + ρ) / 2 < 1 := by linarith
  have hpos : 0 < (1 + ρ) / 2 := by linarith
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((summable_geometric_of_lt_one (div_nonneg h0 hpos.le)
      ((div_lt_one hpos).2 hρ')).mul_left (Real.exp (k * (1 - (1 + ρ) / 2)⁻¹)))
  exact coeff_bound' he k n n h0 hρ' hρ'1

lemma norm_intCast_mul_pow (c : ℤ) (q : ℂ) (n : ℕ) : ‖(c : ℂ) * q ^ n‖ = |(c : ℝ)| * ‖q‖ ^ n := by
  simp

theorem hasSum_prodCoeff {e : ℕ → ℕ} (he : ∀ m, m + 1 ≤ e m) (k : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n => (prodCoeff e k n : ℂ) * q ^ n) (∏' m : ℕ, (1 - q ^ e m) ^ k) := by
  have hρ : ‖q‖ < (1 + ‖q‖) / 2 := by linarith
  have hρ1 : (1 + ‖q‖) / 2 < 1 := by linarith
  have hpos : 0 < (1 + ‖q‖) / 2 := by linarith [norm_nonneg q]
  have hsumm : Summable fun m => ‖q ^ e m‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
      (summable_geometric_of_lt_one (norm_nonneg q) hq)
    rw [norm_pow]
    exact pow_le_pow_of_le_one (norm_nonneg q) hq.le (by have := he m; omega)
  have hmult : Multipliable fun m => 1 - q ^ e m := multipliable_one_sub_of_summable hsumm
  have hP : Tendsto (fun N => ∏ m ∈ range N, (1 - q ^ e m) ^ k) atTop
      (𝓝 (∏' m : ℕ, (1 - q ^ e m) ^ k)) :=
    (hmult.pow k).hasProd.tendsto_prod_nat
  have hD : Tendsto (fun N => ∑' n, ((prodPoly e k N).coeff n : ℂ) * q ^ n) atTop
      (𝓝 (∑' n, (prodCoeff e k n : ℂ) * q ^ n)) := by
    refine tendsto_tsum_of_dominated_convergence
      (bound := fun n => Real.exp (k * (1 - (1 + ‖q‖) / 2)⁻¹) * (‖q‖ / ((1 + ‖q‖) / 2)) ^ n)
      ?_ ?_ ?_
    · exact (summable_geometric_of_lt_one (div_nonneg (norm_nonneg q) hpos.le)
        ((div_lt_one hpos).2 hρ)).mul_left _
    · intro n
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop n] with N hN
      rw [prodPoly_coeff_eq he k hN]
    · refine Eventually.of_forall fun N n => ?_
      rw [norm_intCast_mul_pow]
      exact coeff_bound' he k N n (norm_nonneg q) hρ hρ1
  have hEval : ∀ N, ∑' n, ((prodPoly e k N).coeff n : ℂ) * q ^ n
      = ∏ m ∈ range N, (1 - q ^ e m) ^ k := by
    intro N
    have h : aeval q (prodPoly e k N) = ∏ m ∈ range N, (1 - q ^ e m) ^ k := by
      simp [prodPoly, map_prod]
    rw [← h, aeval_eq_sum_range]
    rw [tsum_eq_sum (s := range ((prodPoly e k N).natDegree + 1))]
    · simp [zsmul_eq_mul]
    · intro n hn
      have : (prodPoly e k N).natDegree < n := by simpa using hn
      simp [coeff_eq_zero_of_natDegree_lt this]
  have hlim := tendsto_nhds_unique (hD.congr hEval) hP
  have hs : Summable fun n => (prodCoeff e k n : ℂ) * q ^ n := by
    refine Summable.of_norm ?_
    simp only [norm_intCast_mul_pow]
    exact summable_prodCoeff he k (norm_nonneg q) hq
  rw [← hlim]
  exact hs.hasSum

/-- The exponents `2(m+1)`. -/
def twoSucc (m : ℕ) : ℕ := 2 * (m + 1)

lemma le_twoSucc (m : ℕ) : m + 1 ≤ twoSucc m := by unfold twoSucc; omega

/-- `a(n)`: the coefficient of `qⁿ` in `q ∏_{m ≥ 1} (1 - q^{2m})¹²`, i.e. of `η(2z)¹²` in
`q = e^{2πiz}`. -/
def etaTwelveCoeff (n : ℕ) : ℤ := if n = 0 then 0 else prodCoeff twoSucc 12 (n - 1)

theorem hasSum_etaTwelveCoeff {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n => (etaTwelveCoeff n : ℂ) * q ^ n)
      (q * ∏' m : ℕ, (1 - q ^ (2 * (m + 1))) ^ 12) := by
  have h := (hasSum_prodCoeff (e := twoSucc) le_twoSucc 12 hq).mul_left q
  rw [← hasSum_nat_add_iff' 1]
  have hsum0 : ∑ i ∈ range 1, ((etaTwelveCoeff i : ℂ) * q ^ i) = 0 := by
    simp [etaTwelveCoeff]
  rw [hsum0, sub_zero]
  have h' : HasSum (fun n => q * ((prodCoeff twoSucc 12 n : ℂ) * q ^ n))
      (q * ∏' m : ℕ, (1 - q ^ (2 * (m + 1))) ^ 12) := h
  convert h' using 1
  funext n
  simp [etaTwelveCoeff, pow_succ]
  ring

theorem summable_etaTwelveCoeff {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    Summable fun n => |(etaTwelveCoeff n : ℝ)| * ρ ^ n := by
  rw [← summable_nat_add_iff 1]
  refine ((summable_prodCoeff le_twoSucc 12 h0 h1).mul_left ρ).congr fun n => ?_
  simp [etaTwelveCoeff, pow_succ]
  ring

lemma etaTwelveCoeff_zero : etaTwelveCoeff 0 = 0 := by simp [etaTwelveCoeff]

lemma etaTwelveCoeff_one : etaTwelveCoeff 1 = 1 := by
  simp [etaTwelveCoeff, prodCoeff, prodPoly]

lemma etaTwelveCoeff_two : etaTwelveCoeff 2 = 0 := by
  have h : ((1 - X ^ 2 : ℤ[X]) ^ 12) = expand ℤ 2 ((1 - X) ^ 12) := by simp
  have h2 : prodCoeff twoSucc 12 1 = 0 := by
    unfold prodCoeff prodPoly
    rw [prod_range_one]
    have h3 : twoSucc 0 = 2 := rfl
    rw [h3, h, coeff_expand (by norm_num)]
    simp
  unfold etaTwelveCoeff
  simpa using h2

end NTKB.HardyWright.TwelveSquares
