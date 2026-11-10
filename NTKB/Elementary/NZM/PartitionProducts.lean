/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Order.MonotoneConvergence
import NTKB.Attr
import NTKB.Elementary.NZM.Partitions

/-!
# Partition generating functions as real functions (Niven–Zuckerman–Montgomery, § 10.4)

Notation: `p(n) = Fintype.card (Nat.Partition n)`, `p_m(n) = (Nat.Partition.restricted n (· ≤ m)).card`
and `ψ_m(x) = ∏_{i=1}^m (1 - x^i)` is `NTKB.NZM.eulerPartialProd x m`.

* **Theorem 10.6.** For `0 < x < 1`, `∑ p_m(n) x^n = 1 / ψ_m(x)`.
* **Theorem 10.7.** For `0 < x < 1`, `lim_{m → ∞} ψ_m(x)` exists and is positive.
* **Theorem 10.8.** For `0 < x < 1`, `∑ p(n) x^n` converges, and equals `1 / lim ψ_m(x)`.

The proofs follow the real-analytic route: for 10.6 the recursion of Theorem 10.1 (C) with a
partial-sum bound for convergence, for 10.7 the bound `1 - t ≥ exp (-t / (1 - x))`, for 10.8 a
monotone-limit argument.
-/

namespace NTKB.NZM

open Finset Filter Topology

/-- The partial products `ψ_m(x) = ∏_{i=1}^m (1 - x^i)`. -/
noncomputable def eulerPartialProd (x : ℝ) (m : ℕ) : ℝ := ∏ i ∈ range m, (1 - x ^ (i + 1))

lemma eulerPartialProd_pos {x : ℝ} (h0 : 0 < x) (h1 : x < 1) (m : ℕ) :
    0 < eulerPartialProd x m :=
  Finset.prod_pos fun i _ => sub_pos.2 (pow_lt_one₀ h0.le h1 (Nat.succ_ne_zero i))

lemma eulerPartialProd_succ (x : ℝ) (m : ℕ) :
    eulerPartialProd x (m + 1) = eulerPartialProd x m * (1 - x ^ (m + 1)) := by
  simp [eulerPartialProd, Finset.prod_range_succ]

/-- For nonnegative `G`, shifting by `k` does not increase partial sums. -/
lemma sum_range_shift_le (G : ℕ → ℝ) (hG : ∀ n, 0 ≤ G n) (k N : ℕ) :
    ∑ n ∈ range N, (if k ≤ n then G (n - k) else 0) ≤ ∑ n ∈ range N, G n := by
  rw [← Finset.sum_filter]
  have hinj : Set.InjOn (fun n => n - k) ((range N).filter (fun n => k ≤ n) : Finset ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_filter, Finset.mem_range] at ha hb
    change _ ∧ _ at ha hb
    simp only at hab
    omega
  rw [← Finset.sum_image hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => hG i
  intro j hj
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hj ⊢
  obtain ⟨a, ⟨ha, _⟩, rfl⟩ := hj
  omega

lemma card_restricted_zero (n : ℕ) :
    ((Nat.Partition.restricted n (· ≤ 0)).card : ℝ) = if n = 0 then 1 else 0 := by
  split_ifs with h
  · subst h
    rw [card_restricted_le_eq_card_partition (le_refl 0)]
    simp
  · have : Nat.Partition.restricted n (· ≤ 0) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun p hp => ?_
      simp only [Nat.Partition.restricted, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      have hp0 : p.parts = 0 := by
        rw [Multiset.eq_zero_iff_forall_notMem]
        intro i hi
        exact (p.parts_pos hi).ne' (Nat.le_zero.1 (hp i hi))
      apply h
      rw [← p.parts_sum, hp0]
      simp
    rw [this]
    simp

/-- One step of the induction in Theorem 10.6. -/
lemma hasSum_restricted_succ {x : ℝ} (h0 : 0 < x) (h1 : x < 1) (m : ℕ) (S : ℝ)
    (hS : HasSum (fun n : ℕ => ((Nat.Partition.restricted n (· ≤ m)).card : ℝ) * x ^ n) S) :
    ∃ T, HasSum (fun n : ℕ => ((Nat.Partition.restricted n (· ≤ m + 1)).card : ℝ) * x ^ n) T ∧
      T * (1 - x ^ (m + 1)) = S := by
  set g : ℕ → ℝ := fun n => ((Nat.Partition.restricted n (· ≤ m + 1)).card : ℝ) * x ^ n with hg
  set f : ℕ → ℝ := fun n => ((Nat.Partition.restricted n (· ≤ m)).card : ℝ) * x ^ n with hf
  have hg0 : ∀ n, 0 ≤ g n := fun n => by positivity
  have hf0 : ∀ n, 0 ≤ f n := fun n => by positivity
  have hrec : ∀ n, g n = f n + x ^ (m + 1) * (if m + 1 ≤ n then g (n - (m + 1)) else 0) := by
    intro n
    by_cases h : m + 1 ≤ n
    · rw [if_pos h]
      simp only [hg, hf]
      rw [card_restricted_succ m h]
      have : x ^ n = x ^ (m + 1) * x ^ (n - (m + 1)) := by
        rw [← pow_add, Nat.add_sub_cancel' h]
      rw [this]
      push_cast
      ring
    · rw [if_neg h]
      simp only [hg, hf]
      rw [card_restricted_le_eq_card_partition (by omega : n ≤ m + 1),
        card_restricted_le_eq_card_partition (by omega : n ≤ m)]
      ring
  have hpos : 0 < 1 - x ^ (m + 1) := sub_pos.2 (pow_lt_one₀ h0.le h1 (Nat.succ_ne_zero m))
  have hsum : Summable g := by
    refine summable_of_sum_range_le (c := S / (1 - x ^ (m + 1))) hg0 fun N => ?_
    rw [le_div_iff₀ hpos]
    have h2 : ∑ n ∈ range N, g n = ∑ n ∈ range N, f n +
        x ^ (m + 1) * ∑ n ∈ range N, (if m + 1 ≤ n then g (n - (m + 1)) else 0) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun n _ => hrec n
    have h3 := sum_range_shift_le g hg0 (m + 1) N
    have h4 : ∑ n ∈ range N, f n ≤ S := sum_le_hasSum _ (fun i _ => hf0 i) hS
    have h5 : 0 ≤ x ^ (m + 1) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h3 h5]
  set T := ∑' n, g n with hT
  have hsh : HasSum (fun n : ℕ => if m + 1 ≤ n then g (n - (m + 1)) else 0) T := by
    rw [← hasSum_nat_add_iff' (m + 1)]
    have : ∑ i ∈ range (m + 1), (if m + 1 ≤ i then g (i - (m + 1)) else 0) = 0 :=
      Finset.sum_eq_zero fun i hi => by
        have : i < m + 1 := Finset.mem_range.1 hi
        exact if_neg (by omega)
    rw [this, sub_zero]
    simpa using hsum.hasSum
  have hall : HasSum g (S + x ^ (m + 1) * T) := by
    have := hS.add (hsh.mul_left (x ^ (m + 1)))
    convert this using 1
    funext n
    exact hrec n
  have := hsum.hasSum.unique hall
  exact ⟨T, hsum.hasSum, by linarith⟩

/-- **Theorem 10.6.** For `0 < x < 1`, `∑ p_m(n) x^n` converges to `1 / ∏_{i=1}^m (1 - x^i)`. -/
@[kb "nivenzuckermanmontgomery" "Thm 10.6, p. 457"]
theorem hasSum_card_restricted_mul_pow {x : ℝ} (h0 : 0 < x) (h1 : x < 1) (m : ℕ) :
    HasSum (fun n : ℕ => ((Nat.Partition.restricted n (· ≤ m)).card : ℝ) * x ^ n)
      (1 / ∏ i ∈ range m, (1 - x ^ (i + 1))) := by
  induction m with
  | zero =>
    have : (fun n : ℕ => ((Nat.Partition.restricted n (· ≤ 0)).card : ℝ) * x ^ n) =
        fun n => if n = 0 then 1 else 0 := by
      funext n
      rw [card_restricted_zero]
      split_ifs with h <;> simp [h]
    rw [this]
    simpa using hasSum_ite_eq 0 (1 : ℝ)
  | succ m ih =>
    obtain ⟨T, hT, hTS⟩ := hasSum_restricted_succ h0 h1 m _ ih
    have hpos : 0 < 1 - x ^ (m + 1) := sub_pos.2 (pow_lt_one₀ h0.le h1 (Nat.succ_ne_zero m))
    have hP : 0 < ∏ i ∈ range m, (1 - x ^ (i + 1)) := eulerPartialProd_pos h0 h1 m
    convert hT using 1
    rw [Finset.prod_range_succ]
    field_simp
    field_simp at hTS
    linarith

/-- The bound `1 - t ≥ exp (-t / (1 - x))` for `0 ≤ t ≤ x < 1`. -/
lemma exp_neg_div_le_one_sub {x t : ℝ} (ht : 0 ≤ t) (htx : t ≤ x) (h1 : x < 1) :
    Real.exp (-t / (1 - x)) ≤ 1 - t := by
  have hp : 0 < 1 - t := by linarith
  have hx : 0 < 1 - x := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hp
  have h2 : -t / (1 - x) ≤ Real.log (1 - t) := by
    refine le_trans ?_ hlog
    have e : 1 - (1 - t)⁻¹ = -(t / (1 - t)) := by field_simp; ring
    rw [e, neg_div]
    have : t / (1 - t) ≤ t / (1 - x) := div_le_div_of_nonneg_left ht hx (by linarith)
    linarith
  exact (Real.le_log_iff_exp_le hp).1 h2

lemma exp_le_eulerPartialProd {x : ℝ} (h0 : 0 < x) (h1 : x < 1) (m : ℕ) :
    Real.exp (-(∑ i ∈ range m, x ^ (i + 1)) / (1 - x)) ≤ eulerPartialProd x m := by
  have hx : 0 < 1 - x := by linarith
  induction m with
  | zero => simp [eulerPartialProd]
  | succ m ih =>
    rw [eulerPartialProd_succ, Finset.sum_range_succ]
    have ht : x ^ (m + 1) ≤ x := pow_le_of_le_one h0.le h1.le (Nat.succ_ne_zero m)
    have h2 := exp_neg_div_le_one_sub (pow_nonneg h0.le (m + 1)) ht h1
    have e : -(∑ i ∈ range m, x ^ (i + 1) + x ^ (m + 1)) / (1 - x) =
        -(∑ i ∈ range m, x ^ (i + 1)) / (1 - x) + -x ^ (m + 1) / (1 - x) := by ring
    rw [e, Real.exp_add]
    exact mul_le_mul ih h2 (Real.exp_pos _).le (eulerPartialProd_pos h0 h1 m).le

lemma sum_pow_succ_le {x : ℝ} (h0 : 0 < x) (h1 : x < 1) (m : ℕ) :
    ∑ i ∈ range m, x ^ (i + 1) ≤ x / (1 - x) := by
  have hs := (hasSum_geometric_of_lt_one h0.le h1).mul_left x
  have := sum_le_hasSum (range m) (fun i _ => by positivity) hs
  calc ∑ i ∈ range m, x ^ (i + 1) = ∑ i ∈ range m, x * x ^ i :=
        Finset.sum_congr rfl fun i _ => pow_succ' x i
    _ ≤ x * (1 - x)⁻¹ := this
    _ = x / (1 - x) := by rw [div_eq_mul_inv]

lemma antitone_eulerPartialProd {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    Antitone (eulerPartialProd x) := by
  refine antitone_nat_of_succ_le fun m => ?_
  rw [eulerPartialProd_succ]
  have := eulerPartialProd_pos h0 h1 m
  have : 0 < x ^ (m + 1) := by positivity
  nlinarith

/-- **Theorem 10.7.** For `0 < x < 1`, `lim_{m → ∞} ∏_{i=1}^m (1 - x^i)` exists and is positive. -/
@[kb "nivenzuckermanmontgomery" "Thm 10.7, p. 458"]
theorem exists_tendsto_eulerPartialProd {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    ∃ L : ℝ, 0 < L ∧ Tendsto (eulerPartialProd x) atTop (𝓝 L) := by
  have hx : 0 < 1 - x := by linarith
  have hbdd : BddBelow (Set.range (eulerPartialProd x)) :=
    ⟨0, by rintro _ ⟨m, rfl⟩; exact (eulerPartialProd_pos h0 h1 m).le⟩
  have hlim := tendsto_atTop_ciInf (antitone_eulerPartialProd h0 h1) hbdd
  refine ⟨_, ?_, hlim⟩
  have hc : ∀ m, Real.exp (-(x / (1 - x)) / (1 - x)) ≤ eulerPartialProd x m := by
    intro m
    refine le_trans (Real.exp_le_exp.2 ?_) (exp_le_eulerPartialProd h0 h1 m)
    have := sum_pow_succ_le h0 h1 m
    have : (∑ i ∈ range m, x ^ (i + 1)) / (1 - x) ≤ x / (1 - x) / (1 - x) :=
      div_le_div_of_nonneg_right this hx.le
    rw [neg_div, neg_div]
    linarith
  exact lt_of_lt_of_le (Real.exp_pos _) (le_ciInf hc)

/-- **Theorem 10.8.** For `0 < x < 1`, the series `∑ p(n) x^n` converges, and its sum is
`1 / L` where `L = lim_{m → ∞} ∏_{i=1}^m (1 - x^i)` (Theorem 10.7). -/
@[kb "nivenzuckermanmontgomery" "Thm 10.8, p. 459"]
theorem hasSum_card_partition_mul_pow {x L : ℝ} (h0 : 0 < x) (h1 : x < 1) (hL0 : 0 < L)
    (hL : Tendsto (eulerPartialProd x) atTop (𝓝 L)) :
    HasSum (fun n : ℕ => (Fintype.card (Nat.Partition n) : ℝ) * x ^ n) (1 / L) := by
  have hge : ∀ m, L ≤ eulerPartialProd x m := fun m =>
    (antitone_eulerPartialProd h0 h1).le_of_tendsto hL m
  have hnn : ∀ n : ℕ, 0 ≤ (Fintype.card (Nat.Partition n) : ℝ) * x ^ n := fun n => by positivity
  have hpm : ∀ m, HasSum (fun n : ℕ => ((Nat.Partition.restricted n (· ≤ m)).card : ℝ) * x ^ n)
      (1 / eulerPartialProd x m) := fun m => hasSum_card_restricted_mul_pow h0 h1 m
  have hbound : ∀ N, ∑ n ∈ range N, (Fintype.card (Nat.Partition n) : ℝ) * x ^ n ≤ 1 / L := by
    intro N
    calc ∑ n ∈ range N, (Fintype.card (Nat.Partition n) : ℝ) * x ^ n
        = ∑ n ∈ range N, ((Nat.Partition.restricted n (· ≤ N)).card : ℝ) * x ^ n := by
          refine Finset.sum_congr rfl fun n hn => ?_
          rw [card_restricted_le_eq_card_partition (Finset.mem_range.1 hn).le]
      _ ≤ 1 / eulerPartialProd x N :=
          sum_le_hasSum _ (fun i _ => by positivity) (hpm N)
      _ ≤ 1 / L := one_div_le_one_div_of_le hL0 (hge N)
  have hsum : Summable fun n : ℕ => (Fintype.card (Nat.Partition n) : ℝ) * x ^ n :=
    summable_of_sum_range_le hnn hbound
  set S := ∑' n : ℕ, (Fintype.card (Nat.Partition n) : ℝ) * x ^ n with hS
  have hS1 : S ≤ 1 / L := Real.tsum_le_of_sum_range_le hnn hbound
  have hSpos : 0 < S := by
    have := (hsum.hasSum).nonneg hnn
    have h0' : (Fintype.card (Nat.Partition 0) : ℝ) * x ^ 0 ≤ S :=
      le_hasSum hsum.hasSum 0 (fun i _ => hnn i)
    have : (Fintype.card (Nat.Partition 0) : ℝ) = 1 := by simp
    simp only [this, pow_zero, mul_one] at h0'
    linarith
  have hS2 : ∀ m, 1 / eulerPartialProd x m ≤ S := fun m =>
    hasSum_le (fun n => by
      have : (Nat.Partition.restricted n (· ≤ m)).card ≤ Fintype.card (Nat.Partition n) :=
        card_restricted_le_card_partition n m
      have h5 : 0 ≤ x ^ n := by positivity
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast this) h5) (hpm m) hsum.hasSum
  have hL2 : 1 / S ≤ L := by
    refine ge_of_tendsto hL (Eventually.of_forall fun m => ?_)
    have hp := eulerPartialProd_pos h0 h1 m
    rw [div_le_iff₀ hSpos]
    have := hS2 m
    rw [div_le_iff₀ hp] at this
    linarith
  have : S = 1 / L := by
    apply le_antisymm hS1
    rw [div_le_iff₀ hL0]
    rw [div_le_iff₀ hSpos] at hL2
    linarith
  rw [← this]
  exact hsum.hasSum

end NTKB.NZM
