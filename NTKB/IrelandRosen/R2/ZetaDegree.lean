/-
Ireland–Rosen, Chapter 11, §3, Remark (1) after Theorem 2 and Exercise 11.17: the polynomial
`P(u) = ∏_χ (1 - α_χ u)` has degree `m^{-1}[(m - 1)^{n+1} + (-1)^{n+1}(m - 1)]`, i.e. this is the
number of tuples `(χ_0, …, χ_n)` with `χ_i^m = ε`, `χ_i ≠ ε`, `χ_0 ⋯ χ_n = ε` (and every `α_χ` is
nonzero).
-/
import NTKB.IrelandRosen.R2.ZetaExamples

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace NTKB.IrelandRosen

variable {F : Type*} [Field F] [Fintype F]

/-- `T_k = #{(χ_1, …, χ_k) : χ_i^m = ε, χ_i ≠ ε, ∏ χ_i = ε}`. -/
noncomputable def numTuples (F : Type*) [Field F] [Fintype F] (k m : ℕ) : ℕ :=
  #{χ ∈ charTuples (F := F) (fun _ : Fin k => m) | (∀ i, χ i ≠ 1) ∧ ∏ i, χ i = 1}

lemma card_nontrivial_pow_eq_one {m : ℕ} (hm : m ∣ Fintype.card F - 1) :
    #{χ : MulChar F ℂ | χ ^ m = 1 ∧ χ ≠ 1} = m - 1 := by
  have h : ({χ : MulChar F ℂ | χ ^ m = 1 ∧ χ ≠ 1} : Finset _) =
      ({χ : MulChar F ℂ | χ ^ m = 1} : Finset _).erase 1 := by
    ext χ; simp [and_comm]
  rw [h, card_erase_of_mem (by simp), card_filter_pow_eq_one hm]

/-- The recursion `T_{k+1} = (m - 1)^k - T_k`. -/
lemma numTuples_succ {m : ℕ} (hm : m ∣ Fintype.card F - 1) (k : ℕ) :
    numTuples F (k + 1) m + numTuples F k m = (m - 1) ^ k := by
  set H := ({χ : MulChar F ℂ | χ ^ m = 1 ∧ χ ≠ 1} : Finset _)
  have hH : #H = m - 1 := card_nontrivial_pow_eq_one hm
  -- tuples of length `k` with entries in `H`
  have hall : #(Fintype.piFinset fun _ : Fin k => H) = (m - 1) ^ k := by
    rw [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin, hH]
  have hTk : numTuples F k m = #{χ ∈ Fintype.piFinset (fun _ : Fin k => H) | ∏ i, χ i = 1} := by
    unfold numTuples
    congr 1
    ext χ
    simp [H, charTuples, Fintype.mem_piFinset, forall_and, and_assoc]
  -- a tuple of length `k + 1` with trivial product is determined by its first `k` entries
  have hTk1 : numTuples F (k + 1) m =
      #{χ ∈ Fintype.piFinset (fun _ : Fin k => H) | ∏ i, χ i ≠ 1} := by
    unfold numTuples
    refine Finset.card_nbij' (fun χ => Fin.init χ) (fun χ => Fin.snoc χ (∏ i, χ i)⁻¹) ?_ ?_ ?_ ?_
    · intro χ hχ
      simp only [mem_coe, mem_filter, charTuples, Fintype.mem_piFinset, mem_univ, true_and,
        H] at hχ ⊢
      obtain ⟨hpow, hne, hprod⟩ := hχ
      refine ⟨fun i => ⟨hpow _, hne _⟩, ?_⟩
      rw [Fin.prod_univ_castSucc] at hprod
      intro h
      change (∏ i, χ (Fin.castSucc i)) = 1 at h
      rw [h, one_mul] at hprod
      exact hne _ hprod
    · intro χ hχ
      simp only [mem_coe, mem_filter, charTuples, Fintype.mem_piFinset, mem_univ, true_and,
        H] at hχ ⊢
      obtain ⟨hmem, hprod⟩ := hχ
      have hpow : (∏ i, χ i) ^ m = 1 := by
        rw [← Finset.prod_pow]; exact Finset.prod_eq_one fun i _ => (hmem i).1
      refine ⟨fun i => ?_, fun i => ?_, ?_⟩
      · refine Fin.lastCases ?_ (fun j => ?_) i
        · rw [Fin.snoc_last, inv_pow, hpow, inv_one]
        · rw [Fin.snoc_castSucc]; exact (hmem j).1
      · refine Fin.lastCases ?_ (fun j => ?_) i
        · rw [Fin.snoc_last]; exact inv_ne_one.mpr hprod
        · rw [Fin.snoc_castSucc]; exact (hmem j).2
      · rw [Fin.prod_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        exact mul_inv_cancel _
    · intro χ hχ
      simp only [mem_coe, mem_filter] at hχ
      have hprod := hχ.2.2
      rw [Fin.prod_univ_castSucc] at hprod
      have : χ (Fin.last k) = (∏ i, Fin.init χ i)⁻¹ := eq_inv_of_mul_eq_one_right hprod
      conv_rhs => rw [← Fin.snoc_init_self χ]
      rw [this]
    · intro χ _
      exact Fin.init_snoc _ _
  rw [hTk1, hTk, add_comm, Finset.card_filter_add_card_filter_not, hall]

lemma numTuples_zero (m : ℕ) : numTuples F 0 m = 1 := by
  unfold numTuples
  rw [Finset.card_eq_one]
  refine ⟨fun i => i.elim0, ?_⟩
  ext χ
  simp only [mem_filter, mem_singleton, charTuples, Fintype.mem_piFinset, IsEmpty.forall_iff,
    univ_eq_empty, prod_empty, and_self, true_and]
  exact iff_of_true trivial (funext fun i => i.elim0)

/-- The closed form `m T_k = (m - 1)^k + (-1)^k (m - 1)`. -/
lemma numTuples_mul {m : ℕ} (hm : m ∣ Fintype.card F - 1) (k : ℕ) :
    (numTuples F k m : ℤ) * m = ((m : ℤ) - 1) ^ k + (-1) ^ k * ((m : ℤ) - 1) := by
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · rw [zero_dvd_iff, Nat.sub_eq_zero_iff_le] at hm
      exact absurd hm (not_le.mpr Fintype.one_lt_card)
    · exact h
  induction k with
  | zero => rw [numTuples_zero]; push_cast; ring
  | succ k ih =>
    have h := numTuples_succ hm k
    have h' : (numTuples F (k + 1) m : ℤ) = ((m : ℤ) - 1) ^ k - numTuples F k m := by
      have := congrArg (fun x : ℕ => (x : ℤ)) h
      push_cast [Nat.cast_sub hm1] at this
      linarith
    rw [h', sub_mul, ih]
    ring

/-- **Exercise 11.17 / Remark (1) after Theorem 2 of §11.3.** The number of factors of `P(u)`,
i.e. of tuples `(χ_0, …, χ_n)` with `χ_i^m = ε`, `χ_i ≠ ε`, `χ_0 ⋯ χ_n = ε`, is
`m^{-1}[(m - 1)^{n+1} + (-1)^{n+1}(m - 1)]`. -/
@[kb "irelandrosen1990" "Exercise 11.17, p. 171"]
theorem card_diagTuples_mul {n m : ℕ} (hm : m ∣ Fintype.card F - 1) :
    (#(diagTuples F n m) : ℤ) * m = ((m : ℤ) - 1) ^ (n + 1) + (-1) ^ (n + 1) * ((m : ℤ) - 1) :=
  numTuples_mul hm (n + 1)

/-- The polynomial `P(u) = ∏_χ (1 - α_χ u)` of Theorem 2 of §11.3. -/
noncomputable def diagP {n : ℕ} (a : Fin (n + 1) → F) (m : ℕ) (ψ : AddChar F ℂ) :
    Polynomial ℂ :=
  ∏ χ ∈ diagTuples F n m, (1 - Polynomial.C (diagAlpha a ψ χ) * Polynomial.X)

/-- **Remark (1) after Theorem 2 of §11.3.** `deg P = m^{-1}[(m - 1)^{n+1} + (-1)^{n+1}(m - 1)]`. -/
@[kb "irelandrosen1990" "Thm 2 (§11.3), Remark (1), p. 173"]
theorem natDegree_diagP_mul {n : ℕ} {a : Fin (n + 1) → F} (ha : ∀ i, a i ≠ 0) {m : ℕ}
    (hm : m ∣ Fintype.card F - 1) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    ((diagP a m ψ).natDegree : ℤ) * m =
      ((m : ℤ) - 1) ^ (n + 1) + (-1) ^ (n + 1) * ((m : ℤ) - 1) := by
  have hα : ∀ χ ∈ diagTuples F n m, diagAlpha a ψ χ ≠ 0 := by
    intro χ hχ h
    have := norm_diagAlpha ha hψ hχ
    rw [h, norm_zero] at this
    have hq : (0 : ℝ) < √(Fintype.card F) := Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
    exact (zpow_ne_zero _ hq.ne') this.symm
  have hfac : ∀ χ ∈ diagTuples F n m,
      (1 - Polynomial.C (diagAlpha a ψ χ) * Polynomial.X : Polynomial ℂ) =
        Polynomial.C (-diagAlpha a ψ χ) * Polynomial.X + Polynomial.C 1 := by
    intro χ _; rw [map_neg, Polynomial.C_1]; ring
  have hdeg : (diagP a m ψ).natDegree = #(diagTuples F n m) := by
    rw [diagP, Polynomial.natDegree_prod _ _ (fun χ hχ => by
      rw [hfac χ hχ]
      exact Polynomial.ne_zero_of_natDegree_gt (n := 0)
        (by rw [Polynomial.natDegree_linear (neg_ne_zero.mpr (hα χ hχ))]; norm_num))]
    rw [Finset.sum_congr rfl fun χ hχ => by
      rw [hfac χ hχ, Polynomial.natDegree_linear (neg_ne_zero.mpr (hα χ hχ))]]
    simp
  rw [hdeg]
  exact card_diagTuples_mul hm

end NTKB.IrelandRosen
