/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Aesop.BuiltinRules
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
import NTKB.Attr

/-!
# Hardy–Wright, Chapter XVIII: the order of magnitude of `d(n)`, `σ(n)`, `φ(n)`

* Theorem 313: `liminf d(n) = 2`.
* Theorem 314: `d(n) = O((log n)^Δ)` is false for every `Δ`.
* Theorem 315: `d(n) = o(n^δ)` (hence `O(n^δ)`) for every `δ > 0`.
* Theorem 316: a multiplicative `f` with `f(p^m) → 0` as `p^m → ∞` tends to `0`.
* Theorem 321: `σ(n) ≥ n`.
* Theorem 322: `σ(n) = O(n^{1+δ})` for every `δ > 0`.
* Theorem 326: `limsup φ(n)/n = 1`.
* Theorem 327: `φ(n)/n^{1-δ} → ∞` for every `δ > 0`.
* Theorem 329: `A < σ(n) φ(n)/n² < 1` for `n > 1`, for a positive constant `A` (here `A = 1/2`).

Proofs are those of the book: Theorems 315 and 327 from Theorem 316, Theorem 322 from 327 and
329, Theorem 329 from `σ(n) φ(n)/n² = ∏_{p^a ∥ n} (1 - p^{-a-1})`.
-/

open ArithmeticFunction Finset Filter Topology Asymptotics
open scoped ArithmeticFunction.sigma

namespace NTKB.HardyWright


/-- Bound on the product of the factors `|f(q^{a_q})|` (Hardy–Wright's `A^C`). -/
private lemma prod_abs_le_pow {f : ArithmeticFunction ℝ} {A : ℝ} {B : ℕ} (hA : 1 ≤ A)
    (hfA : ∀ p m : ℕ, p.Prime → 0 < m → p ^ m ≤ B → |f (p ^ m)| ≤ A)
    (hf1 : ∀ p m : ℕ, p.Prime → 0 < m → B < p ^ m → |f (p ^ m)| < 1)
    (n : ℕ) (S : Finset ℕ) (hS : S ⊆ n.primeFactors) :
    ∏ q ∈ S, |f (q ^ n.factorization q)| ≤ A ^ B := by
  have hle : ∀ q ∈ S, |f (q ^ n.factorization q)| ≤ if q ≤ B then A else 1 := by
    intro q hq
    have hq' := hS hq
    have hp := Nat.prime_of_mem_primeFactors hq'
    have hm : 0 < n.factorization q :=
      Nat.Prime.factorization_pos_of_dvd hp (Nat.mem_primeFactors.mp hq').2.2
        (Nat.dvd_of_mem_primeFactors hq')
    split_ifs with hqB
    · by_cases hB : q ^ n.factorization q ≤ B
      · exact hfA q _ hp hm hB
      · exact (hf1 q _ hp hm (by omega)).le.trans hA
    · have : B < q ^ n.factorization q := by
        calc B < q := by omega
          _ = q ^ 1 := (pow_one q).symm
          _ ≤ q ^ n.factorization q := Nat.pow_le_pow_right hp.pos hm
      exact (hf1 q _ hp hm this).le
  calc ∏ q ∈ S, |f (q ^ n.factorization q)| ≤ ∏ q ∈ S, (if q ≤ B then A else 1) :=
        Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) hle
    _ = A ^ #(S.filter (· ≤ B)) := by rw [prod_ite, prod_const_one, mul_one, prod_const]
    _ ≤ A ^ B := by
        apply pow_le_pow_right₀ hA
        calc #(S.filter (· ≤ B)) ≤ #(Icc 1 B) := by
              apply card_le_card
              intro q hq
              simp only [mem_filter] at hq
              have := Nat.pos_of_mem_primeFactors (hS hq.1)
              simp only [mem_Icc]; omega
          _ = B := by simp

/-- **Theorem 316** (Hardy–Wright). If `f` is multiplicative and `f(p^m) → 0` as `p^m → ∞`
(through prime powers with `m ≥ 1`), then `f(n) → 0` as `n → ∞`. -/
@[kb "hardywright2008" "Thm 316, p. 362"]
theorem tendsto_zero_of_isMultiplicative {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative)
    (h : ∀ ε > 0, ∃ N : ℕ, ∀ p m : ℕ, p.Prime → 0 < m → N < p ^ m → |f (p ^ m)| < ε) :
    Tendsto (fun n => f n) atTop (𝓝 0) := by
  obtain ⟨B, hB⟩ := h 1 one_pos
  set A : ℝ := 1 + ∑ q ∈ range (B + 1), |f q| with hAdef
  have hA : 1 ≤ A := by
    have : 0 ≤ ∑ q ∈ range (B + 1), |f q| := sum_nonneg fun _ _ => abs_nonneg _
    linarith
  have hfA : ∀ p m : ℕ, p.Prime → 0 < m → p ^ m ≤ B → |f (p ^ m)| ≤ A := by
    intro p m _ _ hpm
    have : |f (p ^ m)| ≤ ∑ q ∈ range (B + 1), |f q| :=
      single_le_sum (f := fun q => |f q|) (fun _ _ => abs_nonneg _)
        (mem_range.mpr (Nat.lt_succ_of_le hpm))
    linarith
  have hApos : 0 < A ^ B := pow_pos (by linarith) B
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨Nε, hNε⟩ := h (ε / (2 * A ^ B)) (by positivity)
  set N := max Nε B + 1 with hN
  refine ⟨N ^ N + 1, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by
    have : 0 < N ^ N + 1 := Nat.succ_pos _
    omega
  rw [Real.dist_eq, sub_zero]
  -- some prime-power factor of `n` exceeds `N`
  obtain ⟨p, hp, hpN⟩ : ∃ p ∈ n.primeFactors, N < p ^ n.factorization p := by
    by_contra hcon
    push Not at hcon
    have h1 : n ≤ N ^ #n.primeFactors := by
      calc n = ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
            (Nat.prod_primeFactors_pow_factorization hn0)
        _ ≤ ∏ _p ∈ n.primeFactors, N := Finset.prod_le_prod hcon
        _ = N ^ #n.primeFactors := prod_const _
    have h2 : #n.primeFactors ≤ N := by
      calc #n.primeFactors ≤ #(Icc 1 N) := by
            apply card_le_card
            intro q hq
            have h1 := Nat.pos_of_mem_primeFactors hq
            have h2 := hcon q hq
            have hm : 0 < n.factorization q :=
              (Nat.prime_of_mem_primeFactors hq).factorization_pos_of_dvd hn0
                (Nat.dvd_of_mem_primeFactors hq)
            have : q ≤ q ^ n.factorization q := by
              calc q = q ^ 1 := (pow_one q).symm
                _ ≤ q ^ n.factorization q := Nat.pow_le_pow_right h1 hm
            simp only [mem_Icc]; omega
        _ = N := by simp
    have h3 : N ^ #n.primeFactors ≤ N ^ N := Nat.pow_le_pow_right (by omega) h2
    omega
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hm : 0 < n.factorization p :=
    hpp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hp)
  rw [hf.multiplicative_factorization f hn0, Finsupp.prod, Nat.support_factorization, abs_prod,
    ← mul_prod_erase _ _ hp]
  have hsmall : |f (p ^ n.factorization p)| < ε / (2 * A ^ B) :=
    hNε p _ hpp hm (by omega)
  have hrest := prod_abs_le_pow hA hfA (fun p m hp hm h => hB p m hp hm h) n _
    (erase_subset p n.primeFactors)
  calc |f (p ^ n.factorization p)| * ∏ q ∈ n.primeFactors.erase p, |f (q ^ n.factorization q)|
      ≤ ε / (2 * A ^ B) * A ^ B := by
        apply mul_le_mul hsmall.le hrest (prod_nonneg fun _ _ => abs_nonneg _) (by positivity)
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

/-- From `g(x) → 0` as `x → ∞`, a threshold `N` beyond which `|g(x)| < ε`. -/
lemma exists_nat_abs_lt_of_tendsto {g : ℝ → ℝ} (hg : Tendsto g atTop (𝓝 0)) {ε : ℝ}
    (hε : 0 < ε) : ∃ N : ℕ, ∀ x : ℝ, (N : ℝ) < x → |g x| < ε := by
  obtain ⟨X, hX⟩ := (Metric.tendsto_atTop.mp hg) ε hε
  obtain ⟨N, hN⟩ := exists_nat_ge X
  exact ⟨N, fun x hx => by simpa [Real.dist_eq] using hX x (by linarith)⟩

/-- `log x / x^δ → 0`. -/
lemma tendsto_log_div_rpow {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun x : ℝ => Real.log x / x ^ δ) atTop (𝓝 0) :=
  (isLittleO_log_rpow_atTop hδ).tendsto_div_nhds_zero

/-- `n ↦ d(n)/n^δ` as an arithmetic function. -/
noncomputable def divisorCountDivRpow (δ : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => (σ 0 n : ℝ) / (n : ℝ) ^ δ, by simp⟩

lemma divisorCountDivRpow_apply (δ : ℝ) (n : ℕ) :
    divisorCountDivRpow δ n = (σ 0 n : ℝ) / (n : ℝ) ^ δ := rfl

lemma isMultiplicative_divisorCountDivRpow (δ : ℝ) :
    (divisorCountDivRpow δ).IsMultiplicative := by
  refine ⟨by simp [divisorCountDivRpow_apply], fun {m n} hmn => ?_⟩
  simp only [divisorCountDivRpow_apply, isMultiplicative_sigma.map_mul_of_coprime hmn,
    Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
  exact mul_div_mul_comm _ _ _ _

/-- **Theorem 315** (Hardy–Wright). `d(n) = o(n^δ)` for every `δ > 0` (the book's proof via
Theorem 316 gives `o`, and remarks that `O` and `o` are here equivalent). -/
@[kb "hardywright2008" "Thm 315, p. 362"]
theorem card_divisors_isLittleO_rpow {δ : ℝ} (hδ : 0 < δ) :
    (fun n : ℕ => (σ 0 n : ℝ)) =o[atTop] fun n => (n : ℝ) ^ δ := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have htend : Tendsto (fun n => divisorCountDivRpow δ n) atTop (𝓝 0) := by
    refine tendsto_zero_of_isMultiplicative (isMultiplicative_divisorCountDivRpow δ) ?_
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_abs_lt_of_tendsto (tendsto_log_div_rpow hδ)
      (ε := ε * Real.log 2 / 2) (by positivity)
    refine ⟨max N 1, fun p m hp hm hpm => ?_⟩
    have hx : (N : ℝ) < ((p ^ m : ℕ) : ℝ) := by exact_mod_cast (le_max_left N 1).trans_lt hpm
    have hx0 : (0 : ℝ) < ((p ^ m : ℕ) : ℝ) := by exact_mod_cast pow_pos hp.pos m
    have h1 := hN _ hx
    rw [divisorCountDivRpow_apply, sigma_zero_apply_prime_pow hp]
    have hpow : (0 : ℝ) < ((p ^ m : ℕ) : ℝ) ^ δ := Real.rpow_pos_of_pos hx0 δ
    have hlog : (m : ℝ) * Real.log 2 ≤ Real.log ((p ^ m : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Real.log_pow]
      exact mul_le_mul_of_nonneg_left (Real.log_le_log two_pos (by exact_mod_cast hp.two_le))
        (Nat.cast_nonneg m)
    have hm1 : ((m + 1 : ℕ) : ℝ) ≤ 2 * Real.log ((p ^ m : ℕ) : ℝ) / Real.log 2 := by
      rw [le_div_iff₀ hlog2]
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have e : ((m + 1 : ℕ) : ℝ) = m + 1 := by push_cast; ring
      rw [e]
      nlinarith
    rw [abs_of_nonneg (by positivity)]
    rw [abs_of_nonneg (div_nonneg (Real.log_nonneg (by exact_mod_cast
      (Nat.one_le_iff_ne_zero.mpr (pow_pos hp.pos m).ne'))) hpow.le)] at h1
    calc ((m + 1 : ℕ) : ℝ) / ((p ^ m : ℕ) : ℝ) ^ δ
        ≤ 2 * Real.log ((p ^ m : ℕ) : ℝ) / Real.log 2 / ((p ^ m : ℕ) : ℝ) ^ δ := by
          gcongr
      _ = 2 / Real.log 2 * (Real.log ((p ^ m : ℕ) : ℝ) / ((p ^ m : ℕ) : ℝ) ^ δ) := by ring
      _ < 2 / Real.log 2 * (ε * Real.log 2 / 2) := by gcongr
      _ = ε := by field_simp
  rw [isLittleO_iff_tendsto']
  · exact htend
  · filter_upwards [eventually_gt_atTop 0] with n hn h0
    exfalso
    have : (0 : ℝ) < (n : ℝ) ^ δ := Real.rpow_pos_of_pos (by exact_mod_cast hn) δ
    linarith

/-- **Theorem 315** (Hardy–Wright), in the book's form `d(n) = O(n^δ)` for every `δ > 0`. -/
@[kb "hardywright2008" "Thm 315, p. 362"]
theorem card_divisors_isBigO_rpow {δ : ℝ} (hδ : 0 < δ) :
    (fun n : ℕ => (σ 0 n : ℝ)) =O[atTop] fun n => (n : ℝ) ^ δ :=
  (card_divisors_isLittleO_rpow hδ).isBigO


/-- `n ↦ n^{1-δ}/φ(n)` as an arithmetic function. -/
noncomputable def rpowDivTotient (δ : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => (n : ℝ) ^ (1 - δ) / n.totient, by simp⟩

lemma rpowDivTotient_apply (δ : ℝ) (n : ℕ) :
    rpowDivTotient δ n = (n : ℝ) ^ (1 - δ) / n.totient := rfl

lemma isMultiplicative_rpowDivTotient (δ : ℝ) : (rpowDivTotient δ).IsMultiplicative := by
  refine ⟨by simp [rpowDivTotient_apply], fun {m n} hmn => ?_⟩
  simp only [rpowDivTotient_apply, Nat.totient_mul hmn, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
  exact mul_div_mul_comm _ _ _ _

lemma tendsto_rpowDivTotient {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => rpowDivTotient δ n) atTop (𝓝 0) := by
  refine tendsto_zero_of_isMultiplicative (isMultiplicative_rpowDivTotient δ) ?_
  intro ε hε
  have hg : Tendsto (fun x : ℝ => 2 / x ^ δ) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_rpow_atTop hδ)
  obtain ⟨N, hN⟩ := exists_nat_abs_lt_of_tendsto hg hε
  refine ⟨N, fun p m hp hm hpm => ?_⟩
  have hx : (N : ℝ) < ((p ^ m : ℕ) : ℝ) := by exact_mod_cast hpm
  have hx0 : (0 : ℝ) < ((p ^ m : ℕ) : ℝ) := by exact_mod_cast pow_pos hp.pos m
  have h1 := hN _ hx
  have hpow : (0 : ℝ) < ((p ^ m : ℕ) : ℝ) ^ δ := Real.rpow_pos_of_pos hx0 δ
  rw [abs_of_pos (by positivity)] at h1
  rw [rpowDivTotient_apply, abs_of_nonneg (by positivity)]
  refine lt_of_le_of_lt ?_ h1
  -- `φ(p^m) ≥ p^m/2`
  have hφ : ((p ^ m : ℕ) : ℝ) / 2 ≤ ((p ^ m).totient : ℝ) := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [Nat.totient_prime_pow_succ hp]
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hp1 : ((p - 1 : ℕ) : ℝ) = p - 1 := by rw [Nat.cast_sub hp.one_le]; simp
    push_cast
    rw [hp1, pow_succ]
    have : (0 : ℝ) ≤ (p : ℝ) ^ k := by positivity
    nlinarith
  have hφ0 : (0 : ℝ) < ((p ^ m).totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (pow_pos hp.pos m)
  rw [Real.rpow_sub hx0, Real.rpow_one, div_div, div_le_div_iff₀ (by positivity) hpow]
  have : ((p ^ m : ℕ) : ℝ) * ((p ^ m : ℕ) : ℝ) ^ δ ≤
      2 * (((p ^ m : ℕ) : ℝ) ^ δ * ((p ^ m).totient : ℝ)) := by nlinarith
  linarith

/-- **Theorem 327** (Hardy–Wright). `φ(n)/n^{1-δ} → ∞` for every `δ > 0`. -/
@[kb "hardywright2008" "Thm 327, p. 371"]
theorem tendsto_totient_div_rpow {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => (n.totient : ℝ) / (n : ℝ) ^ (1 - δ)) atTop atTop := by
  have h := tendsto_rpowDivTotient hδ
  have hpos : ∀ᶠ n : ℕ in atTop, rpowDivTotient δ n ∈ Set.Ioi 0 := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [rpowDivTotient_apply]
    have h1 : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr hn
    have h2 : (0 : ℝ) < (n : ℝ) ^ (1 - δ) := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
    exact Set.mem_Ioi.mpr (div_pos h2 h1)
  have h' := (tendsto_nhdsWithin_iff.mpr ⟨h, hpos⟩).inv_tendsto_nhdsGT_zero
  refine h'.congr fun n => ?_
  simp [rpowDivTotient_apply, inv_div]

/-- `n ↦ σ(n) φ(n)/n²` as an arithmetic function. -/
noncomputable def sigmaTotientDivSq : ArithmeticFunction ℝ :=
  ⟨fun n => (σ 1 n : ℝ) * n.totient / (n : ℝ) ^ 2, by simp⟩

lemma sigmaTotientDivSq_apply (n : ℕ) :
    sigmaTotientDivSq n = (σ 1 n : ℝ) * n.totient / (n : ℝ) ^ 2 := rfl

lemma isMultiplicative_sigmaTotientDivSq : sigmaTotientDivSq.IsMultiplicative := by
  refine ⟨by simp [sigmaTotientDivSq_apply], fun {m n} hmn => ?_⟩
  simp only [sigmaTotientDivSq_apply, isMultiplicative_sigma.map_mul_of_coprime hmn,
    Nat.totient_mul hmn, Nat.cast_mul]
  ring

lemma sigmaTotientDivSq_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    sigmaTotientDivSq (p ^ (k + 1)) = 1 - 1 / (p : ℝ) ^ (k + 2) := by
  rw [sigmaTotientDivSq_apply, sigma_one_apply_prime_pow hp, Nat.totient_prime_pow_succ hp]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : ((p - 1 : ℕ) : ℝ) = p - 1 := by rw [Nat.cast_sub hp.one_le]; simp
  push_cast
  rw [hp1]
  have hgeom : (∑ i ∈ range (k + 1 + 1), (p : ℝ) ^ i) * (p - 1) = p ^ (k + 2) - 1 :=
    geom_sum_mul _ _
  have e : (∑ i ∈ range (k + 1 + 1), (p : ℝ) ^ i) * ((p : ℝ) ^ k * (p - 1)) =
      (p : ℝ) ^ k * (p ^ (k + 2) - 1) := by linear_combination (p : ℝ) ^ k * hgeom
  rw [e]
  field_simp
  ring

/-- `σ(n) φ(n) / n² = ∏_{p^a ∥ n} (1 - p^{-a-1})`. -/
theorem sigmaTotientDivSq_eq_prod {n : ℕ} (hn : n ≠ 0) :
    (σ 1 n : ℝ) * n.totient / (n : ℝ) ^ 2 =
      ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ) ^ (n.factorization p + 1)) := by
  rw [← sigmaTotientDivSq_apply, isMultiplicative_sigmaTotientDivSq.multiplicative_factorization
    _ hn, Finsupp.prod, Nat.support_factorization]
  refine prod_congr rfl fun p hp => ?_
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hm : 0 < n.factorization p := hpp.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hp)
  obtain ⟨k, hk⟩ : ∃ k, n.factorization p = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hm).symm⟩
  rw [hk, sigmaTotientDivSq_prime_pow hpp]

/-- `∏_{k=2}^M (1 - 1/k²) = (M+1)/(2M)`. -/
lemma prod_Icc_one_sub_inv_sq (M : ℕ) (hM : 1 ≤ M) :
    ∏ k ∈ Icc 2 M, (1 - 1 / (k : ℝ) ^ 2) = ((M : ℝ) + 1) / (2 * M) := by
  induction M, hM using Nat.le_induction with
  | base => norm_num
  | succ M hM ih =>
    rw [prod_Icc_succ_top (by omega), ih]
    have h1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have h2 : (M : ℝ) ≠ 0 := by linarith
    have h3 : (M : ℝ) + 1 ≠ 0 := by linarith
    push_cast
    field_simp
    ring

/-- For a finite set `S` of integers `≥ 2`, `∏_{k ∈ S} (1 - 1/k²) > 1/2`. -/
lemma one_half_lt_prod_one_sub_inv_sq (S : Finset ℕ) (hS : ∀ k ∈ S, 2 ≤ k) :
    1 / 2 < ∏ k ∈ S, (1 - 1 / (k : ℝ) ^ 2) := by
  set M := S.sup id + 1 with hM
  have hsub : S ⊆ Icc 2 M := by
    intro k hk
    simp only [mem_Icc]
    exact ⟨hS k hk, (le_sup (f := id) hk).trans (Nat.le_succ _)⟩
  have hfac : ∀ k ∈ Icc 2 M, 0 ≤ 1 - 1 / (k : ℝ) ^ 2 ∧ 1 - 1 / (k : ℝ) ^ 2 ≤ 1 := by
    intro k hk
    simp only [mem_Icc] at hk
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk.1
    constructor
    · rw [sub_nonneg, div_le_one (by positivity)]; nlinarith
    · have : 0 ≤ 1 / (k : ℝ) ^ 2 := by positivity
      linarith
  have h1 : ∏ k ∈ Icc 2 M, (1 - 1 / (k : ℝ) ^ 2) ≤ ∏ k ∈ S, (1 - 1 / (k : ℝ) ^ 2) := by
    rw [← prod_sdiff hsub]
    have h0 : 0 ≤ ∏ k ∈ S, (1 - 1 / (k : ℝ) ^ 2) :=
      prod_nonneg fun k hk => (hfac k (hsub hk)).1
    have h2 : ∏ k ∈ Icc 2 M \ S, (1 - 1 / (k : ℝ) ^ 2) ≤ 1 :=
      prod_le_one₀ (fun k hk => (hfac k (sdiff_subset hk)).1)
        (fun k hk => (hfac k (sdiff_subset hk)).2)
    nlinarith
  have hM1 : 1 ≤ M := by omega
  rw [prod_Icc_one_sub_inv_sq M hM1] at h1
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have : (1 : ℝ) / 2 < (M + 1) / (2 * M) := by
    rw [div_lt_div_iff₀ (by norm_num) (by positivity)]; linarith
  linarith

/-- **Theorem 329** (Hardy–Wright). There is a positive constant `A` with
`A < σ(n) φ(n)/n² < 1` for all `n > 1`. (Here `A = 1/2`; the book's footnote notes that the best
constant is `6/π²`.) -/
@[kb "hardywright2008" "Thm 329, p. 371"]
theorem exists_lt_sigma_mul_totient_div_sq :
    ∃ A > 0, ∀ n : ℕ, 1 < n →
      A < (σ 1 n : ℝ) * n.totient / (n : ℝ) ^ 2 ∧ (σ 1 n : ℝ) * n.totient / (n : ℝ) ^ 2 < 1 := by
  refine ⟨1 / 2, by norm_num, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by omega
  rw [sigmaTotientDivSq_eq_prod hn0]
  have hfac : ∀ p ∈ n.primeFactors,
      1 - 1 / (p : ℝ) ^ 2 ≤ 1 - 1 / (p : ℝ) ^ (n.factorization p + 1) ∧
      1 - 1 / (p : ℝ) ^ (n.factorization p + 1) < 1 ∧
      0 < 1 - 1 / (p : ℝ) ^ (n.factorization p + 1) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hm : 0 < n.factorization p :=
      hpp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hp)
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hpow : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ (n.factorization p + 1) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have hpos2 : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
    refine ⟨?_, ?_, ?_⟩
    · have := one_div_le_one_div_of_le hpos2 hpow
      linarith
    · have : 0 < 1 / (p : ℝ) ^ (n.factorization p + 1) := by positivity
      linarith
    · rw [sub_pos, div_lt_one (by positivity)]
      calc (1 : ℝ) < p := by linarith
        _ = p ^ 1 := (pow_one _).symm
        _ ≤ p ^ (n.factorization p + 1) := pow_le_pow_right₀ (by linarith) (by omega)
  constructor
  · calc (1 : ℝ) / 2 < ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ) ^ 2) :=
          one_half_lt_prod_one_sub_inv_sq _ fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
      _ ≤ _ := prod_le_prod₀ (fun p hp => by
          have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
          rw [sub_nonneg, div_le_one (by positivity)]; nlinarith) (fun p hp => (hfac p hp).1)
  · obtain ⟨p, hp⟩ : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hn
    rw [← mul_prod_erase _ _ hp]
    have h1 := (hfac p hp).2.1
    have h2 : ∏ q ∈ n.primeFactors.erase p, (1 - 1 / (q : ℝ) ^ (n.factorization q + 1)) ≤ 1 :=
      prod_le_one₀ (fun q hq => (hfac q (mem_of_mem_erase hq)).2.2.le)
        (fun q hq => (hfac q (mem_of_mem_erase hq)).2.1.le)
    have h3 := (hfac p hp).2.2
    have h4 : 0 ≤ ∏ q ∈ n.primeFactors.erase p, (1 - 1 / (q : ℝ) ^ (n.factorization q + 1)) :=
      prod_nonneg fun q hq => (hfac q (mem_of_mem_erase hq)).2.2.le
    nlinarith

/-- **Theorem 321** (Hardy–Wright). `σ(n) ≥ n`. -/
@[kb "hardywright2008" "Thm 321, p. 369"]
theorem le_sigma_one (n : ℕ) : n ≤ σ 1 n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [sigma_one_apply]
  exact single_le_sum (f := id) (fun _ _ => Nat.zero_le _) (Nat.mem_divisors_self n hn.ne')

/-- **Theorem 322** (Hardy–Wright). `σ(n) = O(n^{1+δ})` for every `δ > 0`. Proof (book): by
Theorem 329, `σ(n)/n^{1+δ} < n^{1-δ}/φ(n)`, which tends to `0` by Theorem 327. -/
@[kb "hardywright2008" "Thm 322, p. 369"]
theorem sigma_one_isBigO_rpow {δ : ℝ} (hδ : 0 < δ) :
    (fun n : ℕ => (σ 1 n : ℝ)) =O[atTop] fun n => (n : ℝ) ^ (1 + δ) := by
  have h := tendsto_rpowDivTotient hδ
  have hev : ∀ᶠ n : ℕ in atTop, rpowDivTotient δ n ≤ 1 := by
    have := (Metric.tendsto_atTop.mp h) 1 one_pos
    obtain ⟨N, hN⟩ := this
    filter_upwards [eventually_ge_atTop N] with n hn
    have := hN n hn
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans this.le
  obtain ⟨A, hA, hAn⟩ := exists_lt_sigma_mul_totient_div_sq
  refine IsBigO.of_bound 1 ?_
  filter_upwards [hev, eventually_gt_atTop 1] with n hn1 hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hφ : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hlt := (hAn n hn).2
  rw [div_lt_one (by positivity)] at hlt
  rw [rpowDivTotient_apply, div_le_one hφ] at hn1
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), one_mul]
  have hsplit : (n : ℝ) ^ 2 = (n : ℝ) ^ (1 + δ) * (n : ℝ) ^ (1 - δ) := by
    rw [← Real.rpow_add hn0]; norm_num
  have hpos : (0 : ℝ) < (n : ℝ) ^ (1 + δ) := Real.rpow_pos_of_pos hn0 _
  -- `σ(n) φ(n) < n^{1+δ} n^{1-δ} ≤ n^{1+δ} φ(n)`
  have : (σ 1 n : ℝ) * n.totient < (n : ℝ) ^ (1 + δ) * n.totient := by
    calc (σ 1 n : ℝ) * n.totient < (n : ℝ) ^ 2 := hlt
      _ = (n : ℝ) ^ (1 + δ) * (n : ℝ) ^ (1 - δ) := hsplit
      _ ≤ (n : ℝ) ^ (1 + δ) * n.totient := by gcongr
  exact (lt_of_mul_lt_mul_right this hφ.le).le


/-- Primes are frequent: for every `N` there is a prime `p ≥ N`. -/
lemma frequently_prime : ∃ᶠ n : ℕ in atTop, n.Prime :=
  Nat.frequently_atTop_iff_infinite.mpr Nat.infinite_setOfPred_prime

/-- **Theorem 313** (Hardy–Wright). The lower limit of `d(n)` is `2`: `d(n) ≥ 2` for `n > 1`
and `d(p) = 2` for every prime `p`. -/
@[kb "hardywright2008" "Thm 313, p. 361"]
theorem liminf_card_divisors : liminf (fun n => σ 0 n) atTop = 2 := by
  have hlow : ∀ᶠ n in atTop, 2 ≤ σ 0 n := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    rw [sigma_zero_apply]
    have : ({1, n} : Finset ℕ) ⊆ n.divisors := by
      intro d hd
      simp only [mem_insert, mem_singleton] at hd
      rcases hd with rfl | rfl <;> simp <;> omega
    calc 2 = #({1, n} : Finset ℕ) := by rw [card_pair (by omega)]
      _ ≤ _ := card_le_card this
  have hfreq : ∃ᶠ n in atTop, σ 0 n ≤ 2 :=
    frequently_prime.mono fun p hp => by rw [sigma_zero_apply, Nat.Prime.divisors hp,
      card_pair hp.one_lt.ne]
  apply le_antisymm
  · exact liminf_le_of_frequently_le hfreq (isBoundedUnder_of_eventually_ge
      (Eventually.of_forall fun n => Nat.zero_le _))
  · refine le_liminf_of_le ?_ hlow
    exact ⟨2, fun a ha => by
      obtain ⟨n, hn1, hn2⟩ := (hfreq.and_eventually ha).exists
      exact (show a ≤ σ 0 n from hn2).trans hn1⟩

/-- **Theorem 326** (Hardy–Wright). `limsup φ(n)/n = 1`. -/
@[kb "hardywright2008" "Thm 326, p. 371"]
theorem limsup_totient_div : limsup (fun n : ℕ => (n.totient : ℝ) / n) atTop = 1 := by
  have hle : ∀ n : ℕ, (n.totient : ℝ) / n ≤ 1 := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [div_le_one (by exact_mod_cast hn)]
    exact_mod_cast Nat.totient_le n
  have hge : ∀ n : ℕ, 0 ≤ (n.totient : ℝ) / n := fun n => by positivity
  have hbdd : IsBoundedUnder (· ≤ ·) atTop fun n : ℕ => (n.totient : ℝ) / n :=
    isBoundedUnder_of_eventually_le (a := 1) (Eventually.of_forall hle)
  apply le_antisymm
  · exact limsup_le_of_le (isBoundedUnder_of_eventually_ge (a := 0)
      (Eventually.of_forall hge)).isCoboundedUnder_le (Eventually.of_forall hle)
  · refine le_of_forall_sub_le fun ε hε => ?_
    refine le_limsup_of_frequently_le ?_ hbdd
    -- primes `p > 1/ε` have `φ(p)/p = 1 - 1/p ≥ 1 - ε`
    have hev : ∀ᶠ n : ℕ in atTop, 1 / ε < n := tendsto_natCast_atTop_atTop.eventually_gt_atTop _
    refine (frequently_prime.and_eventually hev).mono fun p ⟨hp, hpε⟩ => ?_
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one, sub_div, div_self hp0.ne']
    have : 1 / (p : ℝ) ≤ ε := by
      rw [div_le_iff₀ hp0]
      rw [div_lt_iff₀ hε] at hpε
      linarith
    linarith


/-- If `P` is a product of `k` different primes, then `d(P^m) = (m+1)^k`. -/
lemma card_divisors_prod_pow {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (m : ℕ) :
    σ 0 ((∏ p ∈ S, p) ^ m) = (m + 1) ^ #S := by
  rw [← prod_pow, isMultiplicative_sigma.map_prod (fun p => p ^ m) S, prod_congr rfl
    (fun p hp => sigma_zero_apply_prime_pow (hS p hp)), prod_const]
  intro p hp q hq hpq
  exact Nat.Coprime.pow m m ((Nat.coprime_primes (hS p hp) (hS q hq)).mpr hpq)

/-- **Theorem 314** (Hardy–Wright). `d(n) = O((log n)^Δ)` is false for every `Δ`. Proof (book):
along `n = P^m`, `P` a product of `k > Δ` different primes, `d(n) = (m+1)^k` while
`(log n)^Δ = (m log P)^Δ`. -/
@[kb "hardywright2008" "Thm 314, p. 361"]
theorem not_card_divisors_isBigO_log_rpow (Δ : ℝ) :
    ¬ (fun n : ℕ => (σ 0 n : ℝ)) =O[atTop] fun n => Real.log n ^ Δ := by
  intro h
  -- `k > Δ` different primes
  obtain ⟨k, hk⟩ := exists_nat_gt (max Δ 0)
  obtain ⟨S, hSsub, hScard⟩ := Nat.infinite_setOfPred_prime.exists_subset_card_eq k
  have hS : ∀ p ∈ S, p.Prime := fun p hp => hSsub hp
  set P := ∏ p ∈ S, p with hP
  have hk0 : 0 < k := by exact_mod_cast (le_max_right Δ 0).trans_lt hk
  have hP2 : 2 ≤ P := by
    obtain ⟨p, hp⟩ : S.Nonempty := card_pos.mp (hScard ▸ hk0)
    calc 2 ≤ p := (hS p hp).two_le
      _ ≤ P := Nat.le_of_dvd (prod_pos fun q hq => (hS q hq).pos) (dvd_prod_of_mem _ hp)
  have hlogP : 0 < Real.log P := Real.log_pos (by exact_mod_cast hP2)
  -- compose with `m ↦ P^m`
  have htend : Tendsto (fun m : ℕ => P ^ m) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by omega)
  have h2 := h.comp_tendsto htend
  obtain ⟨C, hC⟩ := h2.bound
  have hgrow : Tendsto (fun m : ℕ => (m : ℝ) ^ ((k : ℝ) - Δ)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith [le_max_left Δ 0])).comp tendsto_natCast_atTop_atTop
  obtain ⟨m, hm1, hm2, hm3⟩ := ((hgrow.eventually_gt_atTop (|C| * Real.log P ^ Δ)).and
    (hC.and (eventually_ge_atTop 1))).exists
  have hd : σ 0 (P ^ m) = (m + 1) ^ k := by rw [hP, card_divisors_prod_pow hS, hScard]
  simp only [Function.comp, hd, Real.norm_eq_abs] at hm2
  push_cast at hm2
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm3
  have hm0 : (0 : ℝ) < m := by linarith
  rw [Real.log_pow, Real.mul_rpow hm0.le hlogP.le] at hm2
  rw [abs_of_pos (by positivity), abs_of_pos (by positivity)] at hm2
  -- `m^k ≤ (m+1)^k ≤ C m^Δ (log P)^Δ`, so `m^{k-Δ} ≤ |C| (log P)^Δ`
  have h3 : (m : ℝ) ^ (k : ℝ) ≤ |C| * ((m : ℝ) ^ Δ * Real.log P ^ Δ) := by
    rw [Real.rpow_natCast]
    calc (m : ℝ) ^ k ≤ ((m : ℝ) + 1) ^ k := by gcongr; linarith
      _ ≤ C * ((m : ℝ) ^ Δ * Real.log P ^ Δ) := hm2
      _ ≤ |C| * ((m : ℝ) ^ Δ * Real.log P ^ Δ) := by gcongr; exact le_abs_self C
  have hmΔ : (0 : ℝ) < (m : ℝ) ^ Δ := Real.rpow_pos_of_pos hm0 Δ
  rw [Real.rpow_sub hm0] at hm1
  rw [div_eq_mul_inv] at hm1
  have : (m : ℝ) ^ (k : ℝ) ≤ |C| * Real.log P ^ Δ * (m : ℝ) ^ Δ := by linarith
  have h4 := (lt_mul_inv_iff₀ hmΔ).mp hm1
  linarith

end NTKB.HardyWright
