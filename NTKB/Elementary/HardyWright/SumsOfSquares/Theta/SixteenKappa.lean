/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TwelveCount

/-!
# `κ = ∑_{n ∈ ℤ odd} n⁻⁸ = 17 π⁸/80640`

From `ζ(8) = π⁸/9450` (Mathlib's `hasSum_zeta_nat`), as `kappaTwelveR_eq` for `ζ(6)`.
-/

open Finset Filter Topology

noncomputable section

namespace NTKB.HardyWright

/-- `κ = ∑_{n ∈ ℤ, n odd} n⁻⁸`. -/
def kappaSixteenR : ℝ := ∑' n : ℤ, (if Even n then 0 else 1) * (1 / (n : ℝ) ^ 8)

lemma hasSum_zeta_eight : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 8) (Real.pi ^ 8 / 9450) := by
  have h := hasSum_zeta_nat (k := 4) (by norm_num)
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
  have h6 : bernoulli' 6 = 1 / 42 := by
    rw [bernoulli'_def]
    norm_num [Finset.sum_range_succ, Nat.choose, h5]
  have h7 : bernoulli' 7 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
  have h8 : bernoulli' 8 = -1 / 30 := by
    rw [bernoulli'_def]
    norm_num [Finset.sum_range_succ, Nat.choose, h5, h6, h7]
  have hb : bernoulli 8 = -1 / 30 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), h8]
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub] at h
  rw [hb] at h
  convert h using 1
  norm_num [Nat.factorial]
  ring

theorem kappaSixteenR_eq : kappaSixteenR = 17 * Real.pi ^ 8 / 80640 := by
  set z : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ 8 with hz
  have hZ : HasSum z (Real.pi ^ 8 / 9450) := hasSum_zeta_eight
  have hEv : HasSum (fun k : ℕ => z (2 * k)) (Real.pi ^ 8 / 9450 / 256) := by
    have := hZ.mul_left (1 / 256)
    convert this using 1
    · ext k
      simp only [hz]
      push_cast
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · have : (k : ℝ) ≠ 0 := by positivity
        field_simp
        norm_num
    · ring
  have hOdS : Summable fun k : ℕ => z (2 * k + 1) :=
    hZ.summable.comp_injective (i := fun k : ℕ => 2 * k + 1) (by intro a b h; simpa using h)
  set S := ∑' k : ℕ, z (2 * k + 1) with hS
  have hOd : HasSum (fun k : ℕ => z (2 * k + 1)) S := hOdS.hasSum
  have hsum := HasSum.even_add_odd hEv hOd
  have hSval : S = Real.pi ^ 8 / 9450 * (255 / 256) := by
    have := hZ.unique hsum
    linarith
  set g : ℕ → ℝ := fun n => (if Even n then 0 else 1) * z n with hg
  have hgS : HasSum g S := by
    have : HasSum g (0 + S) := HasSum.even_add_odd (by
      have : (fun k : ℕ => g (2 * k)) = fun _ => 0 := by
        ext k
        simp [hg]
      rw [this]; exact hasSum_zero) (by
      refine hOd.congr_fun fun k => ?_
      simp [hg])
    simpa using this
  have h1 : HasSum (fun n : ℕ => (if Even (n : ℤ) then (0 : ℝ) else 1) * (1 / ((n : ℤ) : ℝ) ^ 8))
      S := by
    refine hgS.congr_fun fun n => ?_
    simp [hg, hz]
  have h2 : HasSum (fun n : ℕ =>
      (if Even (-((n : ℤ) + 1)) then (0 : ℝ) else 1) * (1 / ((-((n : ℤ) + 1) : ℤ) : ℝ) ^ 8)) S := by
    have h3 : HasSum (fun n : ℕ => g (n + 1)) S := by
      refine (hasSum_nat_add_iff (f := g) 1).mpr ?_
      have h0 : g 0 = 0 := by simp [hg]
      simpa [h0] using hgS
    refine h3.congr_fun fun n => ?_
    have hev : Even (-((n : ℤ) + 1)) ↔ Even (n + 1) := by
      have := Int.even_natCast (n + 1)
      push_cast at this
      rw [even_neg]; exact this
    simp only [hg, hz, hev]
    push_cast
    rw [show (-((n : ℝ) + 1)) ^ 8 = ((n : ℝ) + 1) ^ 8 by ring]
  have := HasSum.of_nat_of_neg_add_one
    (f := fun n : ℤ => (if Even n then (0 : ℝ) else 1) * (1 / (n : ℝ) ^ 8)) h1 h2
  unfold kappaSixteenR
  rw [this.tsum_eq, hSval]
  ring

end NTKB.HardyWright
