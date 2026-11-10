/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Attr
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.LinearRecurrence
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic.LinearCombination

/-!
# Linear recurrences and generating functions (Niven–Zuckerman–Montgomery, Appendix A.4)

* Theorem A.7 (formal version over a field): a sequence satisfies a linear recurrence of order `k`
  iff its generating function `u(z) = ∑ uₙ zⁿ` satisfies `u(z) · Q(z) = P(z)` with polynomials
  `P, Q`, `deg P < k`, `deg Q ≤ k`, `Q(0) = 1`.  The book works with convergent power series
  and a rational function `P/Q`; the analytic condition (positive radius of convergence) is
  automatic and the formal identity `u · Q = P` in `K⟦X⟧` is the algebraic content.
-/

namespace NTKB.NZM

open Polynomial

section A7

variable {K : Type*} [Field K]

/-- Coefficient extraction for `u · Q` at the index `n + k`, when `deg Q ≤ k`. -/
lemma coeff_mk_mul_poly {Q : K[X]} {k : ℕ} (hQ : Q.natDegree ≤ k) (u : ℕ → K) (n : ℕ) :
    PowerSeries.coeff (n + k) (PowerSeries.mk u * (Q : PowerSeries K)) =
      u (n + k) * Q.coeff 0 + ∑ i : Fin k, u (n + i) * Q.coeff (k - i) := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => PowerSeries.coeff a (PowerSeries.mk u) * PowerSeries.coeff b (Q : PowerSeries K))]
  simp only [PowerSeries.coeff_mk, Polynomial.coeff_coe]
  rw [← Finset.sum_range_add_sum_Ico _ (show n ≤ (n + k).succ by omega)]
  have h0 : ∑ a ∈ Finset.range n, u a * Q.coeff (n + k - a) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by have := Finset.mem_range.mp ha; omega),
      mul_zero]
  rw [h0, zero_add, Finset.sum_Ico_eq_sum_range]
  have e1 : (n + k).succ - n = k + 1 := by omega
  rw [e1, Finset.sum_range_succ, ← Fin.sum_univ_eq_sum_range
    (fun i => u (n + i) * Q.coeff (n + k - (n + i))) k]
  simp only [Nat.add_sub_add_left, Nat.sub_self]
  rw [add_comm]

/-- The polynomial `1 - ∑ cᵢ X^{k-i}` attached to the coefficients of a recurrence. -/
noncomputable def recPoly {k : ℕ} (c : Fin k → K) : K[X] :=
  1 - ∑ i : Fin k, C (c i) * X ^ (k - (i : ℕ))

lemma recPoly_coeff_zero {k : ℕ} (c : Fin k → K) : (recPoly c).coeff 0 = 1 := by
  rw [recPoly, coeff_sub, finsetSum_coeff]
  simp only [coeff_one_zero, coeff_C_mul, coeff_X_pow]
  rw [Finset.sum_eq_zero, sub_zero]
  intro i _
  have : (0 : ℕ) ≠ k - i := by have := i.2; omega
  simp [this]

lemma recPoly_coeff {k : ℕ} (c : Fin k → K) (i : Fin k) :
    (recPoly c).coeff (k - i) = - c i := by
  rw [recPoly, coeff_sub, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow]
  have h1 : (1 : K[X]).coeff (k - i) = 0 := by
    rw [coeff_one]; have := i.2; simp; omega
  rw [h1, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    have : k - (i : ℕ) ≠ k - j := by
      have := i.2; have := j.2
      intro h
      apply hj
      ext
      omega
    simp [this]
  · simp

lemma recPoly_natDegree_le {k : ℕ} (c : Fin k → K) : (recPoly c).natDegree ≤ k := by
  unfold recPoly
  refine (natDegree_sub_le _ _).trans (max_le (by simp) ?_)
  refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  simp

/-- **Theorem A.7** (formal version over a field).  A sequence `u` satisfies a linear recurrence
of order `k` iff its generating function satisfies `u(X) · Q(X) = P(X)` with polynomials
`deg P < k`, `deg Q ≤ k`, `Q(0) = 1`; here the recurrence has the Mathlib form
`u (n + k) = ∑ i : Fin k, c i * u (n + i)`, so `Q = 1 - b₁ X - ⋯ - b_k X^k` with `b_j = c_{k-j}`.
(The analytic hypothesis "positive radius of convergence" of the book is not needed in the formal
setting.) -/
@[kb "nivenzuckermanmontgomery" "Thm A.7, p. 494"]
theorem recurrence_iff_rational (u : ℕ → K) (k : ℕ) :
    (∃ c : Fin k → K, (⟨k, c⟩ : LinearRecurrence K).IsSolution u) ↔
      ∃ P Q : K[X], P.degree < k ∧ Q.natDegree ≤ k ∧ Q.coeff 0 = 1 ∧
        PowerSeries.mk u * (Q : PowerSeries K) = (P : PowerSeries K) := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨PowerSeries.trunc k (PowerSeries.mk u * (recPoly c : PowerSeries K)), recPoly c,
      ?_, recPoly_natDegree_le c, recPoly_coeff_zero c, ?_⟩
    · exact (degree_lt_iff_coeff_zero _ _).mpr fun m hm => by
        rw [PowerSeries.coeff_trunc, ite_eq_right_iff.mpr (fun h => absurd h (by omega))]
    · ext m
      rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
      split_ifs with h
      · rfl
      · obtain ⟨n, rfl⟩ : ∃ n, m = n + k := ⟨m - k, by omega⟩
        rw [coeff_mk_mul_poly (recPoly_natDegree_le c), recPoly_coeff_zero, mul_one,
          hc n]
        simp only [recPoly_coeff, mul_neg, Finset.sum_neg_distrib]
        rw [add_neg_eq_zero]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · rintro ⟨P, Q, hP, hQ, hQ0, h⟩
    refine ⟨fun i => - Q.coeff (k - i), fun n => ?_⟩
    have := coeff_mk_mul_poly hQ u n
    rw [h, Polynomial.coeff_coe, coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hP
      (by exact_mod_cast Nat.le_add_left k n)), hQ0, mul_one] at this
    show u (n + k) = ∑ i : Fin k, - Q.coeff (k - i) * u (n + i)
    have e : ∑ i : Fin k, - Q.coeff (k - i) * u (n + i)
        = - ∑ i : Fin k, u (n + i) * Q.coeff (k - i) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    linear_combination -this

end A7

section A10

open Classical in
/-- **Theorem A.10** (statement only; not proved here).  For a complex recurrence whose
characteristic polynomial has nonzero constant term (`b_k ≠ 0` in the book), a sequence is a
solution iff `uₙ = ∑ⱼ Bⱼ(n) λⱼⁿ` with `deg Bⱼ < mⱼ`, where `λⱼ` are the distinct roots of the
characteristic polynomial and `mⱼ` their multiplicities. -/
def SolutionsAreExpPoly (E : LinearRecurrence ℂ) : Prop :=
  E.charPoly.coeff 0 ≠ 0 → ∀ u : ℕ → ℂ, E.IsSolution u ↔
    ∃ B : ℂ → ℂ[X],
      (∀ l ∈ E.charPoly.roots.toFinset,
        (B l).degree < (E.charPoly.rootMultiplicity l : WithBot ℕ)) ∧
      ∀ n : ℕ, u n = ∑ l ∈ E.charPoly.roots.toFinset, (B l).eval (n : ℂ) * l ^ n

/-- The shift operator `(S u)ₙ = u_{n+1}` on complex sequences. -/
def shiftOp : Module.End ℂ (ℕ → ℂ) where
  toFun u := fun n => u (n + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma shiftOp_pow_apply (j : ℕ) (u : ℕ → ℂ) (n : ℕ) : (shiftOp ^ j) u n = u (n + j) := by
  induction j generalizing u with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, mul_apply_eq_comp, ih]
    simp [shiftOp, add_assoc]

lemma isSolution_iff_aeval (E : LinearRecurrence ℂ) (u : ℕ → ℂ) :
    E.IsSolution u ↔ aeval shiftOp E.charPoly u = 0 := by
  have key : ∀ n, aeval shiftOp E.charPoly u n = u (n + E.order) - ∑ i, E.coeffs i * u (n + i) := by
    intro n
    simp [LinearRecurrence.charPoly, aeval_monomial, shiftOp_pow_apply, LinearMap.sum_apply]
  constructor
  · intro h
    funext n
    rw [key, h n]; simp
  · intro h n
    have := congrFun h n
    rw [key] at this
    exact sub_eq_zero.mp this

/-- `(S - λ)` applied to `n^i λ^n`. -/
lemma shift_sub_apply (lam : ℂ) (i : ℕ) :
    (shiftOp - lam • (1 : Module.End ℂ (ℕ → ℂ))) (fun n : ℕ => (n : ℂ) ^ i * lam ^ n) =
      ∑ l ∈ Finset.range i, (lam * (i.choose l : ℂ)) • (fun n : ℕ => (n : ℂ) ^ l * lam ^ n) := by
  funext n
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, one_apply_eq_self, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, Finset.sum_apply, shiftOp, LinearMap.coe_mk, AddHom.coe_mk]
  have h1 : ((n + 1 : ℕ) : ℂ) ^ i = ∑ l ∈ Finset.range (i + 1), (n : ℂ) ^ l * (i.choose l) := by
    push_cast
    rw [add_pow]
    simp
  rw [h1, Finset.sum_range_succ]
  simp only [Nat.choose_self, Nat.cast_one, mul_one, Nat.sub_self]
  have : ∀ l ∈ Finset.range i, (n : ℂ) ^ l * (i.choose l) * lam ^ (n + 1) =
      lam * i.choose l * ((n : ℂ) ^ l * lam ^ n) := by
    intro l _; ring
  rw [add_mul, Finset.sum_mul, Finset.sum_congr rfl this]
  ring

lemma shift_sub_pow_apply_eq_zero (lam : ℂ) (m : ℕ) :
    ∀ i < m, ((shiftOp - lam • (1 : Module.End ℂ (ℕ → ℂ))) ^ m)
      (fun n : ℕ => (n : ℂ) ^ i * lam ^ n) = 0 := by
  induction m with
  | zero => intro i hi; omega
  | succ m ih =>
    intro i hi
    rw [pow_succ, mul_apply_eq_comp, shift_sub_apply, map_sum]
    refine Finset.sum_eq_zero fun l hl => ?_
    rw [map_smul, ih l (by have := Finset.mem_range.mp hl; omega), smul_zero]

lemma aeval_pow_X_sub_C (lam : ℂ) (m : ℕ) :
    aeval shiftOp ((X - C lam) ^ m) = (shiftOp - lam • (1 : Module.End ℂ (ℕ → ℂ))) ^ m := by
  simp [map_pow, aeval_X, aeval_C, Module.algebraMap_end_eq_smul_id]
  rfl

lemma aeval_dvd_expPoly {p : ℂ[X]} {lam : ℂ} {m : ℕ} (hdvd : (X - C lam) ^ m ∣ p) {B : ℂ[X]}
    (hB : B.degree < m) :
    aeval shiftOp p (fun n : ℕ => B.eval (n : ℂ) * lam ^ n) = 0 := by
  obtain ⟨T, rfl⟩ := hdvd
  rw [mul_comm, map_mul, mul_apply_eq_comp, aeval_pow_X_sub_C]
  have hv : (fun n : ℕ => B.eval (n : ℂ) * lam ^ n) =
      ∑ i ∈ Finset.range m, B.coeff i • (fun n : ℕ => (n : ℂ) ^ i * lam ^ n) := by
    funext n
    by_cases hB0 : B = 0
    · simp [hB0]
    · have hn : B.natDegree < m := (natDegree_lt_iff_degree_lt hB0).mpr hB
      rw [eval_eq_sum_range' hn, Finset.sum_mul, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  rw [hv, map_sum, map_sum]
  simp only [map_smul]
  rw [Finset.sum_eq_zero]
  intro i hi
  rw [shift_sub_pow_apply_eq_zero lam m i (Finset.mem_range.mp hi), map_zero, smul_zero]

open Classical in
/-- Converse half of **Theorem A.10**: every sequence `∑ⱼ Bⱼ(n) λⱼⁿ` with `deg Bⱼ < mⱼ` is a
solution of the recurrence. -/
@[kb "nivenzuckermanmontgomery" "Thm A.10, p. 497"]
theorem isSolution_of_expPoly (E : LinearRecurrence ℂ) (B : ℂ → ℂ[X])
    (hB : ∀ l ∈ E.charPoly.roots.toFinset,
      (B l).degree < (E.charPoly.rootMultiplicity l : WithBot ℕ)) :
    E.IsSolution (fun n : ℕ => ∑ l ∈ E.charPoly.roots.toFinset, (B l).eval (n : ℂ) * l ^ n) := by
  rw [isSolution_iff_aeval]
  have : (fun n : ℕ => ∑ l ∈ E.charPoly.roots.toFinset, (B l).eval (n : ℂ) * l ^ n) =
      ∑ l ∈ E.charPoly.roots.toFinset, (fun n : ℕ => (B l).eval (n : ℂ) * l ^ n) := by
    funext n; simp [Finset.sum_apply]
  rw [this, map_sum]
  exact Finset.sum_eq_zero fun l hl =>
    aeval_dvd_expPoly (pow_rootMultiplicity_dvd _ _) (hB l hl)

lemma aeval_mul_apply {V : Type*} [AddCommGroup V] [Module ℂ V] (T : Module.End ℂ V)
    (p r : ℂ[X]) (v : V) : aeval T (p * r) v = aeval T p (aeval T r v) := by
  rw [map_mul, mul_apply_eq_comp]

/-- Primary decomposition: if `∏ qᵢ (T)` kills `v` and the `qᵢ` are pairwise coprime, then
`v` is a sum of vectors killed by the individual `qᵢ (T)`. -/
lemma exists_decomp {ι V : Type*} [DecidableEq ι] [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) (q : ι → ℂ[X]) (s : Finset ι)
    (hq : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (q i) (q j)) (v : V)
    (hv : aeval T (∏ i ∈ s, q i) v = 0) :
    ∃ w : ι → V, (∀ i ∈ s, aeval T (q i) (w i) = 0) ∧ v = ∑ i ∈ s, w i := by
  induction s using Finset.induction_on generalizing v with
  | empty =>
    refine ⟨fun _ => 0, by simp, ?_⟩
    simpa using hv
  | insert a s ha ih =>
    rw [Finset.prod_insert ha] at hv
    have hcop : IsCoprime (q a) (∏ i ∈ s, q i) :=
      IsCoprime.prod_right fun j hj =>
        hq a (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
          (fun h => ha (h ▸ hj))
    obtain ⟨x, y, hxy⟩ := hcop
    have hvv : v = aeval T (x * q a) v + aeval T (y * ∏ i ∈ s, q i) v := by
      rw [← LinearMap.add_apply, ← map_add, hxy]
      simp [mul_comm]
    have hz1 : aeval T (q a) (aeval T (y * ∏ i ∈ s, q i) v) = 0 := by
      rw [← aeval_mul_apply, show q a * (y * ∏ i ∈ s, q i) = y * (q a * ∏ i ∈ s, q i) by ring,
        aeval_mul_apply, hv, map_zero]
    have hz2 : aeval T (∏ i ∈ s, q i) (aeval T (x * q a) v) = 0 := by
      rw [← aeval_mul_apply, show (∏ i ∈ s, q i) * (x * q a) = x * (q a * ∏ i ∈ s, q i) by ring,
        aeval_mul_apply, hv, map_zero]
    obtain ⟨w', hw1, hw2⟩ := ih (fun i hi j hj hij =>
      hq i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij) _ hz2
    refine ⟨fun i => if i = a then aeval T (y * ∏ i ∈ s, q i) v else w' i, ?_, ?_⟩
    · intro i hi
      by_cases hia : i = a
      · subst hia; simpa using hz1
      · simp only [hia, if_false]
        exact hw1 i ((Finset.mem_insert.mp hi).resolve_left hia)
    · have hs : ∑ i ∈ s, (if i = a then aeval T (y * ∏ i ∈ s, q i) v else w' i) =
          ∑ i ∈ s, w' i :=
        Finset.sum_congr rfl fun i hi => by
          have : i ≠ a := fun h => ha (h ▸ hi)
          simp [this]
      rw [Finset.sum_insert ha, if_pos rfl, hs, ← hw2, add_comm]
      exact hvv

lemma shift_sub_pow_twist (lam : ℂ) (j : ℕ) (f : ℕ → ℂ) :
    ((shiftOp - lam • (1 : Module.End ℂ (ℕ → ℂ))) ^ j) (fun n : ℕ => lam ^ n * f n) =
      lam ^ j • (fun n : ℕ => lam ^ n * (fwdDiff 1)^[j] f n) := by
  induction j generalizing f with
  | zero => simp
  | succ j ih =>
    have h1 : (shiftOp - lam • (1 : Module.End ℂ (ℕ → ℂ))) (fun n : ℕ => lam ^ n * f n) =
        lam • (fun n : ℕ => lam ^ n * fwdDiff 1 f n) := by
      funext n
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, one_apply_eq_self, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul, shiftOp, LinearMap.coe_mk, AddHom.coe_mk, fwdDiff]
      ring
    rw [pow_succ, mul_apply_eq_comp, h1, map_smul, ih, Function.iterate_succ_apply]
    funext n
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

lemma choose_eq_poly_eval (k n : ℕ) :
    (n.choose k : ℂ) = (descPochhammer ℂ k).eval (n : ℂ) / (k.factorial : ℂ) := by
  rw [descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
  have : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  push_cast
  field_simp

lemma factor_form {lam : ℂ} (hl : lam ≠ 0) (m : ℕ) (v : ℕ → ℂ)
    (hv : ((shiftOp - lam • (1 : Module.End ℂ (ℕ → ℂ))) ^ m) v = 0) :
    ∃ B : ℂ[X], B.degree < m ∧ ∀ n : ℕ, v n = B.eval (n : ℂ) * lam ^ n := by
  set g : ℕ → ℂ := fun n => v n / lam ^ n with hg
  have hvg : v = fun n : ℕ => lam ^ n * g n := by
    funext n
    simp only [hg]
    field_simp
  rw [hvg, shift_sub_pow_twist] at hv
  have hD : ∀ n, (fwdDiff 1)^[m] g n = 0 := by
    intro n
    have := congrFun hv n
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (pow_ne_zero _ hl)
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h (pow_ne_zero _ hl)
      · exact h
  have hD0 : (fwdDiff 1)^[m] g = 0 := funext hD
  have hz : ∀ j, (fwdDiff 1)^[m + j] g = 0 := by
    intro j
    rw [add_comm, Function.iterate_add_apply, hD0]
    exact Function.iterate_fixed (f := fwdDiff (1 : ℕ) (G := ℂ)) (x := (0 : ℕ → ℂ))
      (funext fun n => by simp [fwdDiff]) j
  have hnewton : ∀ n, g n = ∑ k ∈ Finset.range m, (n.choose k : ℂ) * (fwdDiff 1)^[k] g 0 := by
    intro n
    have h1 := shift_eq_sum_fwdDiff_iter 1 g n 0
    simp only [zero_add, smul_eq_mul, mul_one, nsmul_eq_mul] at h1
    rw [h1]
    rw [Finset.sum_subset (Finset.range_subset_range.mpr (show n + 1 ≤ n + 1 + m by omega)),
      ← Finset.sum_subset (Finset.range_subset_range.mpr (show m ≤ n + 1 + m by omega))]
    · intro k hk hk'
      simp only [Finset.mem_range, not_lt] at hk hk'
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk'
      rw [hz j]; simp
    · intro k hk hk'
      simp only [Finset.mem_range, not_lt] at hk hk'
      rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  set d : ℕ → ℂ := fun k => (fwdDiff 1)^[k] g 0 with hd
  refine ⟨∑ k ∈ Finset.range m, C (d k / (k.factorial : ℂ)) * descPochhammer ℂ k, ?_, ?_⟩
  · cases m with
    | zero => simp
    | succ m' =>
      have hnd : (∑ k ∈ Finset.range (m' + 1),
          C (d k / (k.factorial : ℂ)) * descPochhammer ℂ k).natDegree ≤ m' := by
        refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
        refine (natDegree_C_mul_le _ _).trans ?_
        rw [descPochhammer_natDegree]
        have := Finset.mem_range.mp hk
        omega
      exact lt_of_le_of_lt (degree_le_of_natDegree_le hnd) (by exact_mod_cast Nat.lt_succ_self m')
  · intro n
    rw [hvg]
    simp only
    rw [hnewton n, eval_finsetSum, mul_comm]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [eval_mul, eval_C, choose_eq_poly_eval]
    ring

open Classical in
/-- Forward half of **Theorem A.10**: every solution has the form `∑ⱼ Bⱼ(n) λⱼⁿ`, `deg Bⱼ < mⱼ`
(for a recurrence with `b_k ≠ 0`, i.e. nonzero constant term of the characteristic polynomial). -/
@[kb "nivenzuckermanmontgomery" "Thm A.10, p. 497"]
theorem expPoly_of_isSolution (E : LinearRecurrence ℂ) (h0 : E.charPoly.coeff 0 ≠ 0)
    (u : ℕ → ℂ) (hu : E.IsSolution u) :
    ∃ B : ℂ → ℂ[X],
      (∀ l ∈ E.charPoly.roots.toFinset,
        (B l).degree < (E.charPoly.rootMultiplicity l : WithBot ℕ)) ∧
      ∀ n : ℕ, u n = ∑ l ∈ E.charPoly.roots.toFinset, (B l).eval (n : ℂ) * l ^ n := by
  set s := E.charPoly.roots.toFinset with hs
  have hQ : E.charPoly = ∏ l ∈ s, (X - C l) ^ (E.charPoly.rootMultiplicity l) := by
    conv_lhs => rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq (E.charPoly_monic)
      IsAlgClosed.card_roots_eq_natDegree]
    rw [Finset.prod_multiset_map_count]
    exact Finset.prod_congr rfl fun l _ => by rw [count_roots]
  have hu' := (isSolution_iff_aeval E u).mp hu
  rw [hQ] at hu'
  have hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      IsCoprime ((X - C i) ^ (E.charPoly.rootMultiplicity i))
        ((X - C j) ^ (E.charPoly.rootMultiplicity j)) := fun i _ j _ hij =>
    ((pairwise_coprime_X_sub_C (s := fun x : ℂ => x) Function.injective_id) hij).pow
  obtain ⟨w, hw1, hw2⟩ := exists_decomp shiftOp
    (fun l => (X - C l) ^ (E.charPoly.rootMultiplicity l)) s hcop u hu'
  have hex : ∀ l ∈ s, ∃ B : ℂ[X], B.degree < (E.charPoly.rootMultiplicity l : WithBot ℕ) ∧
      ∀ n : ℕ, w l n = B.eval (n : ℂ) * l ^ n := by
    intro l hl
    have hl0 : l ≠ 0 := by
      rintro rfl
      have hr := (mem_roots'.mp (Multiset.mem_toFinset.mp hl)).2
      rw [IsRoot.def, ← coeff_zero_eq_eval_zero] at hr
      exact h0 hr
    refine factor_form hl0 _ (w l) ?_
    rw [← aeval_pow_X_sub_C]
    exact hw1 l hl
  choose! B hB1 hB2 using hex
  refine ⟨B, hB1, fun n => ?_⟩
  rw [hw2, Finset.sum_apply]
  exact Finset.sum_congr rfl fun l hl => hB2 l hl n

open Classical in
/-- **Theorem A.10.** -/
@[kb "nivenzuckermanmontgomery" "Thm A.10, p. 497"]
theorem solutionsAreExpPoly (E : LinearRecurrence ℂ) : SolutionsAreExpPoly E :=
  fun h0 u => ⟨expPoly_of_isSolution E h0 u, fun ⟨B, hB, hu⟩ => by
    have : u = fun n : ℕ => ∑ l ∈ E.charPoly.roots.toFinset, (B l).eval (n : ℂ) * l ^ n :=
      funext hu
    rw [this]
    exact isSolution_of_expPoly E B hB⟩

end A10

end NTKB.NZM
