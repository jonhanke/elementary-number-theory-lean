/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Data.Set.Card
import Mathlib.Order.LiminfLimsup
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import NTKB.Attr

/-!
# Asymptotic density (Niven–Zuckerman–Montgomery, § 11.1)

* **Definition 11.1.** For a set `A` of positive integers with counting function
  `A(n) = #{a ∈ A : a ≤ n}`, the asymptotic density is `liminf A(n)/n`, and `A` has natural density
  `δ` if `A(n)/n → δ`.
* **Theorem 11.1.** If `a₁ < a₂ < ⋯` is an infinite sequence, its asymptotic density is
  `liminf n/aₙ`, and `A` has natural density `δ` iff `n/aₙ → δ`.

Mathlib has no asymptotic density (only the Schnirelmann density), so the notions are defined here.
Sequences are indexed from `0`: `a k` is the `(k+1)`-st term, so `n/aₙ` becomes `(k+1)/a k`.
-/

namespace NTKB.NZM

open Filter Topology

/-- The counting function `A(n) = #{a ∈ A : a ≤ n}` of a set of positive integers. -/
noncomputable def countingFn (A : Set ℕ) (n : ℕ) : ℕ := (A ∩ Set.Ioc 0 n).ncard

/-- **Definition 11.1.** The asymptotic density of `A`: `liminf A(n)/n`. -/
@[kb "nivenzuckermanmontgomery" "Def 11.1, p. 473"]
noncomputable def asymptoticDensity (A : Set ℕ) : ℝ :=
  liminf (fun n : ℕ => (countingFn A n : ℝ) / n) atTop

/-- **Definition 11.1.** `A` has natural density `δ` if `A(n)/n → δ`. -/
@[kb "nivenzuckermanmontgomery" "Def 11.1, p. 473"]
def HasNaturalDensity (A : Set ℕ) (δ : ℝ) : Prop :=
  Tendsto (fun n : ℕ => (countingFn A n : ℝ) / n) atTop (𝓝 δ)

section Sequence

variable {a : ℕ → ℕ}

private lemma countingFn_le (A : Set ℕ) (n : ℕ) : countingFn A n ≤ n := by
  unfold countingFn
  calc (A ∩ Set.Ioc 0 n).ncard ≤ (Set.Ioc 0 n).ncard :=
        Set.ncard_le_ncard Set.inter_subset_right (Set.finite_Ioc 0 n)
    _ = n := by
        rw [← Finset.coe_Ioc, Set.ncard_coe_finset]; simp

private lemma succ_le_countingFn (hm : StrictMono a) (hp : 0 < a 0) (k n : ℕ) (h : a k ≤ n) :
    k + 1 ≤ countingFn (Set.range a) n := by
  unfold countingFn
  have hsub : (((Finset.range (k + 1)).image a : Finset ℕ) : Set ℕ) ⊆
      Set.range a ∩ Set.Ioc 0 n := by
    intro x hx
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    refine ⟨⟨j, rfl⟩, ?_, ?_⟩
    · exact lt_of_lt_of_le hp (hm.monotone (Nat.zero_le j))
    · exact (hm.monotone (by omega : j ≤ k)).trans h
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, Finset.card_image_of_injective _ hm.injective,
    Finset.card_range] at this
  exact this

private lemma countingFn_le_of_lt (hm : StrictMono a) (k n : ℕ) (h : n < a k) :
    countingFn (Set.range a) n ≤ k := by
  unfold countingFn
  have hsub : Set.range a ∩ Set.Ioc 0 n ⊆
      (((Finset.range k).image a : Finset ℕ) : Set ℕ) := by
    rintro x ⟨⟨j, rfl⟩, -, hx⟩
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
    exact ⟨j, hm.lt_iff_lt.1 (lt_of_le_of_lt hx h), rfl⟩
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset] at this
  exact this.trans (Finset.card_image_le.trans (by simp))

private lemma countingFn_at (hm : StrictMono a) (hp : 0 < a 0) (k : ℕ) :
    countingFn (Set.range a) (a k) = k + 1 :=
  le_antisymm (countingFn_le_of_lt hm (k + 1) _ (hm (Nat.lt_succ_self k)))
    (succ_le_countingFn hm hp k _ le_rfl)

private lemma tendsto_countingFn (hm : StrictMono a) (hp : 0 < a 0) :
    Tendsto (countingFn (Set.range a)) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨a b, fun n hn => ?_⟩
  have := succ_le_countingFn hm hp b n hn
  omega

private lemma tendsto_a (hm : StrictMono a) : Tendsto a atTop atTop :=
  hm.tendsto_atTop

private lemma lower_bd (hm : StrictMono a) (hp : 0 < a 0) (n : ℕ) (hn : 0 < n) :
    ((countingFn (Set.range a) n + 1 : ℕ) : ℝ) / a (countingFn (Set.range a) n) - 1 / n ≤
      (countingFn (Set.range a) n : ℝ) / n := by
  set m := countingFn (Set.range a) n with hmdef
  have hlt : n < a m := by
    by_contra hcon
    have := succ_le_countingFn hm hp m n (not_lt.1 hcon)
    omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : ((m + 1 : ℕ) : ℝ) / a m ≤ ((m + 1 : ℕ) : ℝ) / n := by
    apply div_le_div_of_nonneg_left (by positivity) hnR
    exact_mod_cast hlt.le
  have h2 : ((m + 1 : ℕ) : ℝ) / n = (m : ℝ) / n + 1 / n := by
    push_cast; ring
  linarith

private lemma upper_bd (hm : StrictMono a) (hp : 0 < a 0) (n : ℕ) (_hn : 0 < n)
    (h1 : 1 ≤ countingFn (Set.range a) n) :
    (countingFn (Set.range a) n : ℝ) / n ≤
      ((countingFn (Set.range a) n - 1 + 1 : ℕ) : ℝ) / a (countingFn (Set.range a) n - 1) := by
  set m := countingFn (Set.range a) n with hmdef
  have hle : a (m - 1) ≤ n := by
    by_contra hcon
    have := countingFn_le_of_lt hm (m - 1) n (not_le.1 hcon)
    omega
  have hpos : 0 < a (m - 1) := lt_of_lt_of_le hp (hm.monotone (Nat.zero_le _))
  have hpR : (0 : ℝ) < a (m - 1) := by exact_mod_cast hpos
  have : m - 1 + 1 = m := by omega
  rw [this]
  apply div_le_div_of_nonneg_left (by positivity) hpR
  exact_mod_cast hle

private lemma ratio_bounds (A : Set ℕ) (n : ℕ) :
    0 ≤ (countingFn A n : ℝ) / n ∧ (countingFn A n : ℝ) / n ≤ 1 := by
  refine ⟨by positivity, ?_⟩
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · rw [div_le_one (by exact_mod_cast h)]
    exact_mod_cast countingFn_le A n

/-- **Theorem 11.1 (density).** For an infinite strictly increasing sequence of positive integers,
the asymptotic density of its set of terms is `liminf n/aₙ` (with `a k` the `(k+1)`-st term). -/
@[kb "nivenzuckermanmontgomery" "Thm 11.1, p. 473"]
theorem asymptoticDensity_range (hm : StrictMono a) (hp : 0 < a 0) :
    asymptoticDensity (Set.range a) =
      liminf (fun k : ℕ => ((k + 1 : ℕ) : ℝ) / a k) atTop := by
  unfold asymptoticDensity
  set f : ℕ → ℝ := fun n => (countingFn (Set.range a) n : ℝ) / n with hf
  set g : ℕ → ℝ := fun k => ((k + 1 : ℕ) : ℝ) / a k with hg
  have hga : ∀ k, g k = f (a k) := by
    intro k
    simp only [hf, hg, countingFn_at hm hp k]
  have hfb : IsBoundedUnder (· ≥ ·) atTop f :=
    isBoundedUnder_of ⟨0, fun n => (ratio_bounds _ n).1⟩
  have hfc : IsCoboundedUnder (· ≥ ·) atTop f :=
    isCoboundedUnder_ge_of_le atTop (fun n => (ratio_bounds _ n).2)
  have hgb : IsBoundedUnder (· ≥ ·) atTop g :=
    isBoundedUnder_of ⟨0, fun k => by rw [hga]; exact (ratio_bounds _ _).1⟩
  have hgc : IsCoboundedUnder (· ≥ ·) atTop g :=
    isCoboundedUnder_ge_of_le atTop (fun k => by rw [hga]; exact (ratio_bounds _ _).2)
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    have h1 : ∃ᶠ k in atTop, g k < liminf g atTop + ε :=
      frequently_lt_of_liminf_lt hgc (lt_add_of_pos_right _ hε)
    have h2 : ∃ᶠ n in atTop, f n < liminf g atTop + ε :=
      (tendsto_a hm).frequently (h1.mono fun k hk => by rwa [hga] at hk)
    exact liminf_le_of_frequently_le (h2.mono fun _ h => h.le) hfb
  · apply le_of_forall_pos_le_add
    intro ε hε
    have h1 : ∀ᶠ k in atTop, liminf g atTop - ε / 2 < g k :=
      eventually_lt_of_lt_liminf (by linarith) hgb
    have h1' := (tendsto_countingFn hm hp).eventually h1
    have h2 : ∀ᶠ n : ℕ in atTop, 1 / (n : ℝ) < ε / 2 :=
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).eventually (gt_mem_nhds (by linarith))
    have h3 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
    have h4 : ∀ᶠ n in atTop, liminf g atTop - ε ≤ f n := by
      filter_upwards [h1', h2, h3] with n hn1 hn2 hn3
      have := lower_bd hm hp n hn3
      have e : g (countingFn (Set.range a) n) =
          ((countingFn (Set.range a) n + 1 : ℕ) : ℝ) / a (countingFn (Set.range a) n) := rfl
      simp only [hf]
      linarith
    have := le_liminf_of_le hfc h4
    linarith

/-- **Theorem 11.1 (natural density).** The set of terms of an infinite strictly increasing
sequence has natural density `δ` iff `n/aₙ → δ`. -/
@[kb "nivenzuckermanmontgomery" "Thm 11.1, p. 473"]
theorem hasNaturalDensity_range_iff (hm : StrictMono a) (hp : 0 < a 0) (δ : ℝ) :
    HasNaturalDensity (Set.range a) δ ↔
      Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ) / a k) atTop (𝓝 δ) := by
  have hga : ∀ k, ((k + 1 : ℕ) : ℝ) / a k =
      (countingFn (Set.range a) (a k) : ℝ) / (a k : ℕ) := by
    intro k
    rw [countingFn_at hm hp k]
  constructor
  · intro h
    have := h.comp (tendsto_a hm)
    refine this.congr fun k => ?_
    simp only [Function.comp, hga]
  · intro h
    have hT := tendsto_countingFn hm hp
    have hlo : Tendsto (fun n : ℕ =>
        ((countingFn (Set.range a) n + 1 : ℕ) : ℝ) / a (countingFn (Set.range a) n) - 1 / n)
        atTop (𝓝 δ) := by
      have h1 := h.comp hT
      have h2 := tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
      simpa using (h1.sub h2)
    have hup : Tendsto (fun n : ℕ =>
        ((countingFn (Set.range a) n - 1 + 1 : ℕ) : ℝ) /
          a (countingFn (Set.range a) n - 1)) atTop (𝓝 δ) :=
      h.comp ((tendsto_sub_atTop_nat 1).comp hT)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      exact lower_bd hm hp n hn
    · filter_upwards [eventually_ge_atTop 1, hT.eventually_ge_atTop 1] with n hn hn1
      exact upper_bd hm hp n hn hn1

end Sequence

end NTKB.NZM
