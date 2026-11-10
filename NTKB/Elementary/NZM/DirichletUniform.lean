/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Attr
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Abscissa of absolute convergence and uniform convergence (Niven–Zuckerman–Montgomery, § 8.2)

Dirichlet series are Mathlib's `LSeries f s = ∑ f n / n ^ s` (coefficients `f : ℕ → ℂ`, the
term `n = 0` being `0`), restricted here to real `s` as in the book.

* **Theorem 8.11.**  `abscissaOfAbsConv f` is the unique extended real `σ_a` such that the
  series converges absolutely for real `s > σ_a` and not for real `s < σ_a`
  (`lseriesSummable_iff_abscissa`, `abscissaOfAbsConv_unique`); for real `c > σ_a` the partial
  sums converge uniformly on `[c, ∞)` (`tendstoUniformlyOn_LSeries`).
* **Corollary 8.12.**  `A(s)` is continuous on `(σ_a, ∞)` (`continuousOn_LSeries`).
-/

open Filter Topology LSeries

namespace NTKB.NZM

/-- **Theorem 8.11** (first part): absolute convergence holds for real `s > σ_a` and fails for
real `s < σ_a`, with `σ_a = abscissaOfAbsConv f`. -/
@[kb "nivenzuckermanmontgomery" "Thm 8.11, p. 375"]
theorem lseriesSummable_iff_abscissa (f : ℕ → ℂ) :
    (∀ s : ℝ, abscissaOfAbsConv f < s → LSeriesSummable f s) ∧
      (∀ s : ℝ, (s : EReal) < abscissaOfAbsConv f → ¬ LSeriesSummable f s) := by
  refine ⟨fun s hs => LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using hs),
    fun s hs h => ?_⟩
  have := h.abscissaOfAbsConv_le
  simp only [Complex.ofReal_re] at this
  exact (lt_irrefl _ (hs.trans_le this))

/-- **Theorem 8.11** (uniqueness of `σ_a`). -/
@[kb "nivenzuckermanmontgomery" "Thm 8.11, p. 375"]
theorem abscissaOfAbsConv_unique (f : ℕ → ℂ) (σ : EReal)
    (h₁ : ∀ s : ℝ, σ < s → LSeriesSummable f s)
    (h₂ : ∀ s : ℝ, (s : EReal) < σ → ¬ LSeriesSummable f s) :
    σ = abscissaOfAbsConv f := by
  obtain ⟨hA₁, hA₂⟩ := lseriesSummable_iff_abscissa f
  rcases lt_trichotomy σ (abscissaOfAbsConv f) with h | h | h
  · obtain ⟨s, hs₁, hs₂⟩ := EReal.exists_between_coe_real h
    exact absurd (h₁ s hs₁) (hA₂ s hs₂)
  · exact h
  · obtain ⟨s, hs₁, hs₂⟩ := EReal.exists_between_coe_real h
    exact absurd (hA₁ s hs₁) (h₂ s hs₂)

/-- **Theorem 8.11** (second part): for real `c > σ_a` the partial sums of the Dirichlet series
converge uniformly on `[c, ∞)`. -/
@[kb "nivenzuckermanmontgomery" "Thm 8.11, p. 375"]
theorem tendstoUniformlyOn_LSeries (f : ℕ → ℂ) {c : ℝ} (hc : abscissaOfAbsConv f < c) :
    TendstoUniformlyOn (fun N (s : ℝ) => ∑ n ∈ Finset.range N, term f s n)
      (fun s : ℝ => LSeries f s) atTop (Set.Ici c) := by
  have hsum : LSeriesSummable f c := (lseriesSummable_iff_abscissa f).1 c hc
  have hnorm : Summable fun n => ‖term f c n‖ := summable_norm_iff.mpr hsum
  refine tendstoUniformlyOn_tsum_nat hnorm fun n s hs => ?_
  exact norm_term_le_of_re_le_re f (by simpa using hs) n

/-- **Corollary 8.12.**  The Dirichlet series is a continuous function of real `s > σ_a`. -/
@[kb "nivenzuckermanmontgomery" "Cor 8.12, p. 375"]
theorem continuousOn_LSeries (f : ℕ → ℂ) :
    ContinuousOn (fun s : ℝ => LSeries f s) {s : ℝ | abscissaOfAbsConv f < s} := by
  have hterm : ∀ n, Continuous fun s : ℝ => term f s n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [term_zero]; exact continuous_const
    · have : (fun s : ℝ => term f s n) = fun s : ℝ => f n / (n : ℂ) ^ (s : ℂ) := by
        funext s; simp [term, hn]
      rw [this]
      have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      refine continuous_const.div (continuous_const.cpow Complex.continuous_ofReal
        fun _ => Or.inl (by simpa using Nat.pos_of_ne_zero hn)) fun s => ?_
      exact Complex.cpow_ne_zero_iff.2 (Or.inl hn')
  intro s₀ hs₀
  obtain ⟨c, hc₁, hc₂⟩ := EReal.exists_between_coe_real (show abscissaOfAbsConv f < s₀ from hs₀)
  have hU := tendstoUniformlyOn_LSeries f hc₁
  have hcont : ContinuousOn (fun s : ℝ => LSeries f s) (Set.Ici c) :=
    hU.continuousOn (Frequently.of_forall fun N =>
      (continuous_finsetSum _ fun n _ => hterm n).continuousOn)
  have hnhds : Set.Ici c ∈ 𝓝 s₀ := Ici_mem_nhds (by exact_mod_cast hc₂)
  exact (hcont.continuousAt hnhds).continuousWithinAt

end NTKB.NZM
