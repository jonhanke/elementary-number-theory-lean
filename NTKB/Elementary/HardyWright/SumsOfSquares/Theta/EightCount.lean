/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.ThreeSquares.Statements
import NTKB.Elementary.HardyWright.SumsOfSquares.Jacobi.FourSquares
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Hardy–Wright, § 20.13: generating functions and the coefficients of `r₈`

* `hasSum_sumSquaresCount`: `∑ r_k(n) xⁿ = (∑_{m ∈ ℤ} x^{m²})ᵏ` for `0 ≤ x < 1`.
* `jacobiEightSum_eq`: `16 ∑_{d ∣ n} (-1)^{n+d} d³ = 16 (σ₃(n) - 2σ₃(n/2) + 16σ₃(n/4))`, the
  `q`-expansion coefficients of `(E₄(τ) - 2E₄(2τ) + 16E₄(4τ))/15`.
* `sumSquaresCount_eight_eq_of_forall`: Jacobi's formula for `r₈(n)` from the identity of
  generating functions on `0 < x < ½` (proved in `EightSquares.lean` with modular forms).
-/

open Finset Filter Topology

namespace NTKB.HardyWright

/-- `σ₃(n) - 2σ₃(n/2) + 16σ₃(n/4)` (the terms with `n/2`, `n/4` only when these are integers). -/
def eisensteinEightCoeff (n : ℕ) : ℤ :=
  (ArithmeticFunction.sigma 3 n : ℤ) - 2 * (if 2 ∣ n then (ArithmeticFunction.sigma 3 (n / 2) : ℤ) else 0)
    + 16 * (if 4 ∣ n then (ArithmeticFunction.sigma 3 (n / 4) : ℤ) else 0)

/-- `S(y) = ∑_{n ≥ 1} σ₃(n) yⁿ`. -/
noncomputable def sigmaThreeSeries (y : ℝ) : ℝ :=
  ∑' n : ℕ, (ArithmeticFunction.sigma 3 (n + 1) : ℝ) * y ^ (n + 1)

lemma hasSum_theta_pow_fin (k : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    HasSum (fun v : Fin k → ℤ => x ^ (∑ i, (v i).natAbs ^ 2))
      ((∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ k) := by
  have hx1 : |x| < 1 := by rw [abs_of_nonneg hx0]; exact hx
  have hθ : HasSum (fun m : ℤ => x ^ (m.natAbs ^ 2)) (∑' m : ℤ, x ^ (m.natAbs ^ 2)) :=
    (summable_theta hx1).of_norm.hasSum
  induction k with
  | zero => simp
  | succ k ih =>
    have hs : Summable fun p : ℤ × (Fin k → ℤ) =>
        x ^ (p.1.natAbs ^ 2) * x ^ (∑ i, (p.2 i).natAbs ^ 2) :=
      Summable.mul_of_nonneg (f := fun m : ℤ => x ^ (m.natAbs ^ 2))
        (g := fun v : Fin k → ℤ => x ^ (∑ i, (v i).natAbs ^ 2)) hθ.summable ih.summable
        (fun m => pow_nonneg hx0 _) (fun v => pow_nonneg hx0 _)
    have hp := hθ.mul ih hs
    have := (Fin.consEquiv (fun _ : Fin (k + 1) => ℤ)).symm.hasSum_iff.mpr hp
    rw [pow_succ']
    refine this.congr_fun fun v => ?_
    simp [Fin.sum_univ_succ, pow_add, Fin.tail]

lemma setOf_sq_sum_finite (k n : ℕ) : {v : Fin k → ℤ | ∑ i, v i ^ 2 = (n : ℤ)}.Finite := by
  refine (Set.Finite.pi (t := fun _ : Fin k => Set.Icc (-(n : ℤ)) n)
    fun _ => Set.finite_Icc _ _).subset ?_
  intro v hv i _
  simp only [Set.mem_ofPred_eq] at hv
  have : v i ^ 2 ≤ n := by
    rw [← hv]
    exact Finset.single_le_sum (f := fun i => v i ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)
  exact neg_le_and_le_of_sq_le this

/-- The generating function of `r_k`. -/
theorem hasSum_sumSquaresCount (k : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    HasSum (fun n : ℕ => (sumSquaresCount k n : ℝ) * x ^ n)
      ((∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ k) := by
  set F : (Fin k → ℤ) → ℕ := fun v => ∑ i, (v i).natAbs ^ 2 with hF
  have hsig := (Equiv.sigmaFiberEquiv F).hasSum_iff.mpr (hasSum_theta_pow_fin k hx0 hx)
  refine hsig.sigma fun n => ?_
  have hset : {v : Fin k → ℤ | F v = n} = {v : Fin k → ℤ | ∑ i, v i ^ 2 = (n : ℤ)} := by
    ext v
    simp only [hF, Set.mem_ofPred_eq]
    simp only [← Int.natAbs_sq (v _)]
    constructor
    · intro h; rw [← h]; push_cast; rfl
    · intro h; exact_mod_cast h
  have hfin : {v : Fin k → ℤ | F v = n}.Finite := hset ▸ setOf_sq_sum_finite k n
  have : Finite {v : Fin k → ℤ // F v = n} := hfin.to_subtype
  have := Fintype.ofFinite {v : Fin k → ℤ // F v = n}
  have hsum := hasSum_fintype (fun c : {v : Fin k → ℤ // F v = n} => x ^ F c.1)
  have e1 : ∑ c : {v : Fin k → ℤ // F v = n}, x ^ F c.1 = (sumSquaresCount k n : ℝ) * x ^ n := by
    rw [Finset.sum_congr rfl (fun c _ => by rw [c.2]), sum_const, card_univ, nsmul_eq_mul,
      Fintype.card_eq_nat_card]
    congr 1
    rw [sumSquaresCount, ← hset]
    exact_mod_cast (Nat.card_coe_set_eq {v : Fin k → ℤ | F v = n})
  rw [e1] at hsum
  exact hsum

/-- `σ₃(n)` as an integer. -/
def sigmaThreeInt (n : ℕ) : ℤ := ∑ d ∈ n.divisors, (d : ℤ) ^ 3

lemma sigma_three_cast (n : ℕ) : (ArithmeticFunction.sigma 3 n : ℤ) = sigmaThreeInt n := by
  simp [sigmaThreeInt, ArithmeticFunction.sigma_apply]

lemma sum_even_divisors_cube (n : ℕ) (hn : 0 < n) :
    ∑ d ∈ n.divisors.filter (fun d => 2 ∣ d), (d : ℤ) ^ 3 =
      if 2 ∣ n then 8 * sigmaThreeInt (n / 2) else 0 := by
  split_ifs with h2
  · obtain ⟨m, rfl⟩ := h2
    have hm : 0 < m := by omega
    rw [Nat.mul_div_cancel_left _ (by norm_num), sigmaThreeInt, mul_sum]
    refine sum_nbij' (fun d => d / 2) (fun e => 2 * e) ?_ ?_ ?_ ?_ ?_
    · intro d hd
      simp only [mem_filter, Nat.mem_divisors] at hd ⊢
      obtain ⟨⟨hd1, _⟩, ⟨c, rfl⟩⟩ := hd
      refine ⟨?_, hm.ne'⟩
      rw [Nat.mul_div_cancel_left _ (by norm_num)]
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hd1
    · intro e he
      simp only [mem_filter, Nat.mem_divisors] at he ⊢
      exact ⟨⟨Nat.mul_dvd_mul_left 2 he.1, by omega⟩, dvd_mul_right _ _⟩
    · intro d hd
      simp only [mem_filter] at hd
      omega
    · intro e he; omega
    · intro d hd
      simp only [mem_filter] at hd
      obtain ⟨c, rfl⟩ := hd.2
      rw [Nat.mul_div_cancel_left _ (by norm_num)]
      push_cast; ring
  · apply sum_eq_zero
    intro d hd
    simp only [mem_filter, Nat.mem_divisors] at hd
    exact absurd (dvd_trans hd.2 hd.1.1) h2

lemma odd_divisors_double (m : ℕ) (hm : 0 < m) :
    (2 * m).divisors.filter (fun d => ¬ 2 ∣ d) = m.divisors.filter (fun d => ¬ 2 ∣ d) := by
  ext d
  simp only [mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨h1, _⟩, h2⟩
    have hc : Nat.Coprime d 2 := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]; exact h2
    exact ⟨⟨hc.dvd_of_dvd_mul_left h1, by omega⟩, h2⟩
  · rintro ⟨⟨h1, _⟩, h2⟩
    exact ⟨⟨Dvd.dvd.mul_left h1 2, by omega⟩, h2⟩

lemma sigmaThreeInt_split (n : ℕ) :
    sigmaThreeInt n = ∑ d ∈ n.divisors.filter (fun d => 2 ∣ d), (d : ℤ) ^ 3 +
      ∑ d ∈ n.divisors.filter (fun d => ¬ 2 ∣ d), (d : ℤ) ^ 3 :=
  (sum_filter_add_sum_filter_not _ _ _).symm

lemma alt_sum_eq {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, (-1 : ℤ) ^ (n + d) * (d : ℤ) ^ 3 = eisensteinEightCoeff n := by
  have hcoef : eisensteinEightCoeff n = sigmaThreeInt n - 2 * (if 2 ∣ n then sigmaThreeInt (n / 2) else 0)
      + 16 * (if 4 ∣ n then sigmaThreeInt (n / 4) else 0) := by
    simp only [eisensteinEightCoeff, sigma_three_cast]
  rw [hcoef]
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | hodd
  · have hn2 : n = 2 * m := by omega
    subst hn2
    have hm0 : 0 < m := by omega
    have hsplit : ∑ d ∈ (2 * m).divisors, (-1 : ℤ) ^ (2 * m + d) * (d : ℤ) ^ 3 =
        ∑ d ∈ (2 * m).divisors.filter (fun d => 2 ∣ d), (d : ℤ) ^ 3 -
          ∑ d ∈ (2 * m).divisors.filter (fun d => ¬ 2 ∣ d), (d : ℤ) ^ 3 := by
      rw [← sum_filter_add_sum_filter_not _ (fun d => 2 ∣ d), sub_eq_add_neg, ← sum_neg_distrib]
      congr 1
      · refine sum_congr rfl fun d hd => ?_
        rw [mem_filter] at hd
        have : Even (2 * m + d) := by
          rw [Nat.even_add]; simp [even_iff_two_dvd.2 hd.2]
        rw [this.neg_one_pow, one_mul]
      · refine sum_congr rfl fun d hd => ?_
        rw [mem_filter] at hd
        have : Odd (2 * m + d) := by
          rw [Nat.odd_add]; simp [even_iff_two_dvd, hd.2]
        rw [this.neg_one_pow]; ring
    rw [hsplit, odd_divisors_double m hm0, sum_even_divisors_cube _ (by omega)]
    have h22 : 2 ∣ 2 * m := dvd_mul_right _ _
    have hd : 2 * m / 2 = m := by omega
    have hsm := sigmaThreeInt_split m
    have hs2m := sigmaThreeInt_split (2 * m)
    rw [odd_divisors_double m hm0, sum_even_divisors_cube _ (by omega), if_pos h22, hd] at hs2m
    rw [sum_even_divisors_cube _ hm0] at hsm
    simp only [h22, hd, if_true]
    by_cases h2m : 2 ∣ m
    · have h4 : 4 ∣ 2 * m := by omega
      have : 2 * m / 4 = m / 2 := by omega
      rw [if_pos h4, this]
      rw [if_pos h2m] at hsm
      linarith
    · have h4 : ¬ 4 ∣ 2 * m := by omega
      rw [if_neg h4]
      rw [if_neg h2m] at hsm
      linarith
  · have h2 : ¬ 2 ∣ n := by
      rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.2 hodd
    have h4 : ¬ 4 ∣ n := fun h => h2 (dvd_trans (by norm_num) h)
    rw [if_neg h2, if_neg h4]
    simp only [mul_zero, sub_zero, add_zero, sigmaThreeInt]
    refine sum_congr rfl fun d hd => ?_
    have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
    have hdo : Odd d := by
      rcases Nat.even_or_odd d with he | ho
      · exact absurd (dvd_trans (even_iff_two_dvd.1 he) hdn) h2
      · exact ho
    have : Even (n + d) := hodd.add_odd hdo
    rw [this.neg_one_pow, one_mul]

/-- The divisor identity behind Jacobi's formula. -/
theorem jacobiEightSum_eq {n : ℕ} (hn : 0 < n) : jacobiEightSum n = 16 * eisensteinEightCoeff n := by
  rw [jacobiEightSum, alt_sum_eq hn]

lemma sigma_three_le (n : ℕ) : (ArithmeticFunction.sigma 3 n : ℝ) ≤ (n : ℝ) ^ 4 := by
  rw [ArithmeticFunction.sigma_apply]
  push_cast
  have h2 : ∑ d ∈ n.divisors, (d : ℝ) ^ 3 ≤ n.divisors.card • ((n : ℝ) ^ 3) :=
    sum_le_card_nsmul _ _ _ fun d hd =>
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.divisor_le hd) 3
  have h3 : (n.divisors.card : ℝ) ≤ n := by exact_mod_cast Nat.card_divisors_le_self n
  rw [nsmul_eq_mul] at h2
  calc _ ≤ _ := h2
    _ ≤ (n : ℝ) * (n : ℝ) ^ 3 := mul_le_mul_of_nonneg_right h3 (by positivity)
    _ = _ := by ring

lemma summable_sigma_three {y : ℝ} (hy0 : 0 ≤ y) (hy : y < 1) :
    Summable fun n : ℕ => (ArithmeticFunction.sigma 3 (n + 1) : ℝ) * y ^ (n + 1) := by
  have h := (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ 4 * y ^ n) 1).2
    (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 4 (r := y)
      (by rw [Real.norm_eq_abs, abs_of_nonneg hy0]; exact hy))
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) h
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast sigma_three_le (n + 1)) (by positivity)

lemma hasSum_sigma_three_dvd {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) {j : ℕ} (hj : 0 < j) :
    HasSum (fun n : ℕ => if j ∣ n + 1 then
        (ArithmeticFunction.sigma 3 ((n + 1) / j) : ℝ) * x ^ (n + 1) else 0)
      (sigmaThreeSeries (x ^ j)) := by
  have hy : x ^ j < 1 := pow_lt_one₀ hx0 hx hj.ne'
  have hs := (summable_sigma_three (pow_nonneg hx0 j) hy).hasSum
  set e : ℕ → ℕ := fun m => j * (m + 1) - 1 with he
  have hinj : Function.Injective e := by
    intro a b h
    simp only [he] at h
    have : j * (a + 1) = j * (b + 1) := by
      have := Nat.mul_pos hj (by omega : 0 < a + 1)
      have := Nat.mul_pos hj (by omega : 0 < b + 1)
      omega
    have := Nat.eq_of_mul_eq_mul_left hj this
    omega
  rw [← hinj.hasSum_iff]
  · refine hs.congr_fun fun m => ?_
    have h1 : e m + 1 = j * (m + 1) := by
      have := Nat.mul_pos hj (by omega : 0 < m + 1)
      simp only [he]; omega
    simp only [Function.comp, h1, dvd_mul_right, if_true]
    rw [Nat.mul_div_cancel_left _ hj, pow_mul]
  · intro n hn
    by_cases hd : j ∣ n + 1
    · exfalso
      obtain ⟨c, hc⟩ := hd
      apply hn
      have hc0 : 0 < c := by
        rcases Nat.eq_zero_or_pos c with h | h
        · subst h; omega
        · exact h
      refine ⟨c - 1, ?_⟩
      simp only [he]
      rw [Nat.sub_add_cancel hc0]; omega
    · simp [hd]

lemma hasSum_eisensteinEightCoeff {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    HasSum (fun n : ℕ => (eisensteinEightCoeff (n + 1) : ℝ) * x ^ (n + 1))
      (sigmaThreeSeries x - 2 * sigmaThreeSeries (x ^ 2) + 16 * sigmaThreeSeries (x ^ 4)) := by
  have h1 : HasSum (fun n : ℕ => (ArithmeticFunction.sigma 3 (n + 1) : ℝ) * x ^ (n + 1))
      (sigmaThreeSeries x) := (summable_sigma_three hx0 hx).hasSum
  have h2 := hasSum_sigma_three_dvd hx0 hx (j := 2) (by norm_num)
  have h4 := hasSum_sigma_three_dvd hx0 hx (j := 4) (by norm_num)
  have := (h1.sub (h2.mul_left 2)).add (h4.mul_left 16)
  refine this.congr_fun fun n => ?_
  unfold eisensteinEightCoeff
  push_cast
  split_ifs <;> ring

lemma hasSum_eisensteinEightCoeff_nat {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    HasSum (fun n : ℕ => (eisensteinEightCoeff n : ℝ) * x ^ n)
      (sigmaThreeSeries x - 2 * sigmaThreeSeries (x ^ 2) + 16 * sigmaThreeSeries (x ^ 4)) := by
  have h := (hasSum_nat_add_iff (f := fun n : ℕ => (eisensteinEightCoeff n : ℝ) * x ^ n) 1).mp
    (hasSum_eisensteinEightCoeff hx0 hx)
  have h0 : eisensteinEightCoeff 0 = 0 := by
    simp [eisensteinEightCoeff]
  simpa [h0] using h

/-- `∑_{n ≥ 1} c(n) xⁿ = S(x) - 2 S(x²) + 16 S(x⁴)` with `c = eisensteinEightCoeff`. -/
theorem tsum_eisensteinEightCoeff {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    ∑' n : ℕ, (eisensteinEightCoeff (n + 1) : ℝ) * x ^ (n + 1) =
      sigmaThreeSeries x - 2 * sigmaThreeSeries (x ^ 2) + 16 * sigmaThreeSeries (x ^ 4) :=
  (hasSum_eisensteinEightCoeff hx0 hx).tsum_eq

/-- **Jacobi's formula for `r₈`**, from the identity of generating functions. -/
theorem sumSquaresCount_eight_eq_of_forall
    (h : ∀ x : ℝ, 0 < x → x < 1 / 2 → (∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 8 =
      1 + 16 * (sigmaThreeSeries x - 2 * sigmaThreeSeries (x ^ 2) + 16 * sigmaThreeSeries (x ^ 4)))
    {n : ℕ} (hn : 0 < n) : (sumSquaresCount 8 n : ℤ) = jacobiEightSum n := by
  set c : ℕ → ℝ := fun N => (eisensteinEightCoeff N : ℝ) with hc
  set a : ℕ → ℝ := fun N => (sumSquaresCount 8 N : ℝ) - (if N = 0 then 1 else 0) - 16 * c N
    with ha
  -- generating functions
  have hHS : ∀ x : ℝ, 0 ≤ x → x < 1 →
      HasSum (fun N : ℕ => c N * x ^ N)
        (sigmaThreeSeries x - 2 * sigmaThreeSeries (x ^ 2) + 16 * sigmaThreeSeries (x ^ 4)) := by
    intro x hx0 hx
    simpa [hc] using hasSum_eisensteinEightCoeff_nat hx0 hx
  have hHA : ∀ x : ℝ, 0 ≤ x → x < 1 →
      HasSum (fun N : ℕ => a N * x ^ N)
        ((∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 8 - 1 -
          16 * (sigmaThreeSeries x - 2 * sigmaThreeSeries (x ^ 2) + 16 * sigmaThreeSeries (x ^ 4))) := by
    intro x hx0 hx
    have h3 : HasSum (fun N : ℕ => (if N = 0 then (1 : ℝ) else 0) * x ^ N) 1 := by
      have := hasSum_ite_eq (0 : ℕ) (1 : ℝ)
      refine this.congr_fun fun N => ?_
      by_cases hN : N = 0 <;> simp [hN]
    have := ((hasSum_sumSquaresCount 8 hx0 hx).sub h3).sub ((hHS x hx0 hx).mul_left 16)
    refine this.congr_fun fun N => ?_
    simp only [ha]; ring
  have hzero : ∀ x : ℝ, 0 < x → x < 1 / 2 → ∑' N, a N * x ^ N = 0 := by
    intro x hx0 hx
    rw [(hHA x hx0.le (by linarith)).tsum_eq, h x hx0 hx]; ring
  have hs : Summable fun N => |a N| * (1 / 2 : ℝ) ^ N := by
    have := (hHA (1 / 2) (by norm_num) (by norm_num)).summable.abs
    refine this.congr fun N => ?_
    rw [abs_mul, abs_of_pos (show (0 : ℝ) < (1 / 2) ^ N by positivity)]
  have hn0 := eq_zero_of_tsum_pow_eq_zero hs hzero n
  have hnn : n ≠ 0 := hn.ne'
  simp only [ha, if_neg hnn, hc] at hn0
  rw [jacobiEightSum_eq hn]
  have : (sumSquaresCount 8 n : ℝ) = 16 * (eisensteinEightCoeff n : ℝ) := by linarith
  exact_mod_cast this

end NTKB.HardyWright
