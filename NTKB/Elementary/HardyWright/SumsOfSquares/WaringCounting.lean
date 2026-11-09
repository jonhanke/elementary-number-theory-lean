/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Waring
import NTKB.Attr
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Topology.Order.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Hardy–Wright, § 20.1: `k - 1` `k`th powers do not suffice

The number of `n ≤ N` which are sums of `k - 1` `k`th powers is at most `(N^{1/k} + 1)^{k-1}`
(here `N^{1/k}` is replaced by the integer `k`th root `t` of `N`, `tᵏ ≤ N < (t + 1)ᵏ`), so for
`k ≥ 2` most numbers are not representable by `k - 1` or fewer `k`th powers: the proportion of such
`n ≤ N` tends to `0` (`tendsto_card_isSumOfPowers_pred_div`).
-/

open Finset Filter Topology

namespace NTKB.HardyWright

/-- The integer `k`th root of `N`. -/
def intRoot (k N : ℕ) : ℕ := Nat.findGreatest (fun t => t ^ k ≤ N) N

lemma intRoot_pow_le {k : ℕ} (hk : k ≠ 0) (N : ℕ) : intRoot k N ^ k ≤ N :=
  Nat.findGreatest_spec (P := fun t => t ^ k ≤ N) (Nat.zero_le N) (by simp [zero_pow hk])

lemma lt_succ_intRoot_pow {k : ℕ} (hk : k ≠ 0) (N : ℕ) : N < (intRoot k N + 1) ^ k := by
  by_contra h
  push Not at h
  have hle : intRoot k N + 1 ≤ N := le_trans (Nat.le_self_pow hk _) h
  exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _) hle h

lemma le_intRoot {k M N : ℕ} (hk : k ≠ 0) (h : M ^ k ≤ N) : M ≤ intRoot k N :=
  Nat.le_findGreatest (le_trans (Nat.le_self_pow hk M) h) h

open Classical in
/-- The number of `n ≤ N` which are sums of `s` `k`th powers is at most `(t + 1)ˢ`,
`t = intRoot k N` (Hardy–Wright § 20.1). -/
lemma card_isSumOfPowers_le_pow {k : ℕ} (hk : k ≠ 0) (s N : ℕ) :
    ((range (N + 1)).filter fun n => IsSumOfPowers k s n).card ≤ (intRoot k N + 1) ^ s := by
  have hlt := lt_succ_intRoot_pow hk N
  generalize intRoot k N = t at hlt ⊢
  let F : (Fin s → Fin (t + 1)) → ℕ := fun x => ∑ i, ((x i : ℕ)) ^ k
  have hsub : ((range (N + 1)).filter fun n => IsSumOfPowers k s n) ⊆ univ.image F := by
    intro n hn
    simp only [mem_filter, mem_range] at hn
    obtain ⟨hn, x, rfl⟩ := hn
    have hle : ∀ i, x i ≤ t := by
      intro i
      by_contra h
      push Not at h
      have h1 : (t + 1) ^ k ≤ x i ^ k := Nat.pow_le_pow_left h k
      have h2 : x i ^ k ≤ ∑ j, x j ^ k :=
        single_le_sum (f := fun j => x j ^ k) (fun _ _ => Nat.zero_le _) (mem_univ i)
      omega
    exact mem_image.2 ⟨fun i => ⟨x i, Nat.lt_succ_of_le (hle i)⟩, mem_univ _, rfl⟩
  calc _ ≤ (univ.image F).card := card_le_card hsub
    _ ≤ (univ : Finset (Fin s → Fin (t + 1))).card := card_image_le
    _ = (t + 1) ^ s := by simp

open Classical in
/-- **§ 20.1** (Hardy–Wright). For `k ≥ 2`, most numbers are not the sum of `k - 1` (or fewer)
`k`th powers: the proportion of `n ≤ N` which are tends to `0`. -/
@[kb "hardywright2008" "Section 20.1, p. 412"]
theorem tendsto_card_isSumOfPowers_pred_div {k : ℕ} (hk : 2 ≤ k) :
    Tendsto (fun N : ℕ => (((range (N + 1)).filter fun n => IsSumOfPowers k (k - 1) n).card : ℝ) / N)
      atTop (𝓝 0) := by
  have hk0 : k ≠ 0 := by omega
  -- `t = intRoot k N` tends to infinity
  have htend : Tendsto (fun N => (intRoot k N : ℝ)) atTop atTop := by
    refine tendsto_natCast_atTop_atTop.comp (tendsto_atTop_atTop.2 fun M => ⟨M ^ k, fun N hN => ?_⟩)
    exact le_intRoot hk0 hN
  -- the bound `card/N ≤ (t + 1)^(k-1)/tᵏ ≤ 2^(k-1)/t`
  have hbound : ∀ᶠ N in atTop, (((range (N + 1)).filter fun n => IsSumOfPowers k (k - 1) n).card : ℝ)
      / N ≤ 2 ^ (k - 1) / (intRoot k N : ℝ) := by
    filter_upwards [htend.eventually_gt_atTop 0] with N hN
    have hN0 : (0 : ℝ) < N := by
      have := intRoot_pow_le hk0 N
      have : (0 : ℝ) < (intRoot k N : ℝ) ^ k := by positivity
      calc (0 : ℝ) < (intRoot k N : ℝ) ^ k := this
        _ ≤ N := by exact_mod_cast intRoot_pow_le hk0 N
    have hc : (((range (N + 1)).filter fun n => IsSumOfPowers k (k - 1) n).card : ℝ) ≤
        ((intRoot k N : ℝ) + 1) ^ (k - 1) := by exact_mod_cast card_isSumOfPowers_le_pow hk0 (k - 1) N
    have htk : (intRoot k N : ℝ) ^ k ≤ N := by exact_mod_cast intRoot_pow_le hk0 N
    have h1t : (1 : ℝ) ≤ (intRoot k N : ℝ) := by
      have : 0 < intRoot k N := by exact_mod_cast hN
      exact_mod_cast this
    set t := (intRoot k N : ℝ)
    have h2t : t + 1 ≤ 2 * t := by linarith
    have hpow : (t + 1) ^ (k - 1) ≤ 2 ^ (k - 1) * t ^ (k - 1) := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) h2t _
    rw [div_le_div_iff₀ hN0 hN]
    calc _ ≤ (t + 1) ^ (k - 1) * t := mul_le_mul_of_nonneg_right hc hN.le
      _ ≤ 2 ^ (k - 1) * t ^ (k - 1) * t := mul_le_mul_of_nonneg_right hpow hN.le
      _ = 2 ^ (k - 1) * t ^ k := by
          rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]
      _ ≤ 2 ^ (k - 1) * N := mul_le_mul_of_nonneg_left htk (by positivity)
  have hlim : Tendsto (fun N => (2 : ℝ) ^ (k - 1) / (intRoot k N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop htend
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun N => by positivity) hbound

end NTKB.HardyWright
