/-
Ireland–Rosen, Chapter 10, §2: reduced polynomials (Lemma 2), power sums over a finite field
(Lemma 3), Chevalley's theorem (Theorem 1) and its projective corollary.

Chevalley's theorem is deduced, as in the book, from the divisibility of the number of zeros by
the characteristic, which is Mathlib's Chevalley–Warning theorem `FiniteField.char_dvd_card_solutions`.
-/
import Mathlib.FieldTheory.ChevalleyWarning
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import NTKB.Attr

open scoped Classical LinearAlgebra.Projectivization

set_option linter.unusedSectionVars false

namespace NTKB.IrelandRosen

open MvPolynomial

variable {F : Type*} [Field F] [Fintype F]

section Reduced

/-- The exponent reduction `k ↦ k'` with `x ^ k = x ^ k'` on `F` and `k' < q`. -/
private def reduceExp (q k : ℕ) : ℕ := if k = 0 then 0 else (k - 1) % (q - 1) + 1

private lemma reduceExp_lt {q : ℕ} (hq : 1 < q) (k : ℕ) : reduceExp q k < q := by
  unfold reduceExp
  have := Nat.mod_lt (k - 1) (show 0 < q - 1 by omega)
  split_ifs <;> omega

private lemma pow_reduceExp (x : F) (k : ℕ) : x ^ reduceExp (Fintype.card F) k = x ^ k := by
  unfold reduceExp
  split_ifs with hk
  · simp [hk]
  · by_cases hx : x = 0
    · simp [hx, hk]
    · rw [pow_succ, ← pow_eq_pow_mod _ (FiniteField.pow_card_sub_one_eq_one x hx),
        ← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hk)]

/-- **Lemma 2 (§10.2)**: every polynomial function on `F ^ σ` is given by a reduced polynomial,
one of degree `< q` in each variable. -/
@[kb "irelandrosen1990" "Lemma 2 (§10.2), p. 155"]
theorem exists_reduced_equiv {σ : Type*} (f : MvPolynomial σ F) :
    ∃ g : MvPolynomial σ F, (∀ i, g.degreeOf i < Fintype.card F) ∧
      ∀ x : σ → F, MvPolynomial.eval x g = MvPolynomial.eval x f := by
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have h0 : reduceExp (Fintype.card F) 0 = 0 := by simp [reduceExp]
  refine ⟨∑ d ∈ f.support, monomial (d.mapRange (reduceExp (Fintype.card F)) h0) (f.coeff d),
    fun i => ?_, fun x => ?_⟩
  · refine lt_of_le_of_lt (degreeOf_le_iff.2 fun m hm => ?_) (Nat.lt_succ_self _ |>.trans_le
      (Nat.succ_le_of_lt hq) |> fun _ => (by omega : Fintype.card F - 1 < Fintype.card F))
    obtain ⟨d, -, hd⟩ := Finset.mem_biUnion.1 (support_sum hm)
    have := Finset.mem_singleton.1 (support_monomial_subset hd)
    subst this
    have := reduceExp_lt hq (d i)
    simp only [Finsupp.mapRange_apply]
    omega
  · rw [map_sum]
    conv_rhs => rw [eval_eq]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [eval_monomial, Finsupp.prod_mapRange_index (fun _ => pow_zero _)]
    simp only [pow_reduceExp]
    rfl

/-- Uniqueness of reduced representatives. -/
@[kb "irelandrosen1990" "Lemma 2 (§10.2), p. 155"]
theorem reduced_eq_of_equiv {σ : Type*} [Finite σ] {g h : MvPolynomial σ F}
    (hg : ∀ i, g.degreeOf i < Fintype.card F) (hh : ∀ i, h.degreeOf i < Fintype.card F)
    (heq : ∀ x, eval x g = eval x h) : g = h := by
  rw [← sub_eq_zero]
  refine eq_zero_of_eval_zero_at_prod_finset _ (fun _ => Finset.univ) (fun i => ?_) fun x _ => ?_
  · exact lt_of_le_of_lt (degreeOf_sub_le i g h) (max_lt (hg i) (hh i))
  · simp [heq]

end Reduced

section PowerSums

lemma sum_pow_field (k : ℕ) :
    ∑ a : F, a ^ k = if k ≠ 0 ∧ (Fintype.card F - 1) ∣ k then -1 else 0 := by
  by_cases hk : k = 0
  · simp [hk]
  have : ∑ a : F, a ^ k = ∑ x : Fˣ, (x : F) ^ k := by
    let φ : Fˣ ↪ F := ⟨fun x ↦ x, Units.val_injective⟩
    have : Finset.univ.map φ = Finset.univ \ {0} := by
      ext x
      simpa only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and,
        Finset.mem_sdiff, Finset.mem_singleton, φ] using! isUnit_iff_ne_zero
    calc
      ∑ x : F, x ^ k = ∑ x ∈ Finset.univ \ {(0 : F)}, x ^ k := by
        rw [← Finset.sum_sdiff ({0} : Finset F).subset_univ, Finset.sum_singleton,
          zero_pow hk, add_zero]
      _ = ∑ x : Fˣ, (x : F) ^ k := by simp [φ, ← this, Finset.univ.sum_map φ]
  rw [this, FiniteField.sum_pow_units F k]
  simp [hk]

/-- **Lemma 3 (§10.2)**. -/
@[kb "irelandrosen1990" "Lemma 3 (§10.2), p. 155"]
theorem sum_prod_pow_eq_zero {n : ℕ} (i : Fin n → ℕ)
    (h : ∃ j, i j = 0 ∨ ¬ (Fintype.card F - 1) ∣ i j) :
    ∑ a : Fin n → F, ∏ j, a j ^ i j = 0 := by
  rw [← Fintype.prod_sum fun j (a : F) => a ^ i j]
  obtain ⟨j, hj⟩ := h
  refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
  rw [sum_pow_field, ite_eq_right_iff]
  rintro ⟨h1, h2⟩
  exact absurd h2 (hj.resolve_left h1)

/-- The remark after Lemma 3 (§10.2). -/
@[kb "irelandrosen1990" "Lemma 3 (§10.2), p. 155"]
theorem sum_prod_pow_of_forall {n : ℕ} (i : Fin n → ℕ)
    (h : ∀ j, i j ≠ 0 ∧ (Fintype.card F - 1) ∣ i j) :
    ∑ a : Fin n → F, ∏ j, a j ^ i j = ((Fintype.card F : F) - 1) ^ n := by
  rw [← Fintype.prod_sum fun j (a : F) => a ^ i j]
  simp [sum_pow_field, h]

end PowerSums

section Chevalley

/-- **Theorem 1 (§10.2), Chevalley**: a polynomial of degree `< n` in `n` variables with a zero
has at least two zeros. -/
@[kb "irelandrosen1990" "Thm 1 (§10.2), p. 154"]
theorem two_le_card_zeros {n : ℕ} (f : MvPolynomial (Fin n) F)
    (h0 : MvPolynomial.eval 0 f = 0) (hdeg : f.totalDegree < n) :
    2 ≤ Fintype.card {x : Fin n → F // MvPolynomial.eval x f = 0} := by
  obtain ⟨p, hp⟩ := CharP.exists F
  have hp2 := CharP.char_is_prime F p
  have hpos : 0 < Fintype.card {x : Fin n → F // MvPolynomial.eval x f = 0} :=
    Fintype.card_pos_iff.2 ⟨⟨0, h0⟩⟩
  have hdvd : p ∣ Fintype.card {x : Fin n → F // MvPolynomial.eval x f = 0} := by
    have := char_dvd_card_solutions p (f := f) (by simpa using hdeg)
    convert this
  exact hp2.two_le.trans (Nat.le_of_dvd hpos hdvd)

@[kb "irelandrosen1990" "Thm 1 (§10.2), p. 154"]
theorem exists_ne_zero_eval_eq_zero {n : ℕ} (f : MvPolynomial (Fin n) F)
    (h0 : MvPolynomial.eval 0 f = 0) (hdeg : f.totalDegree < n) :
    ∃ x : Fin n → F, x ≠ 0 ∧ MvPolynomial.eval x f = 0 := by
  obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.1 (two_le_card_zeros f h0 hdeg)
  by_cases ha : a.1 = 0
  · exact ⟨b.1, fun hb => hab (Subtype.ext (ha.trans hb.symm)), b.2⟩
  · exact ⟨a.1, ha, a.2⟩

lemma eval_smul_of_isHomogeneous {m : ℕ} {h : MvPolynomial (Fin m) F} {d : ℕ}
    (hh : h.IsHomogeneous d) (a : F) (x : Fin m → F) :
    eval (a • x) h = a ^ d * eval x h := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hd : ∑ i, e i = d := by
    by_contra hne
    exact (mem_support_iff.1 he) (hh.coeff_eq_zero (by rwa [Finsupp.degree_eq_sum]))
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hd]
  ring

/-- **Corollary to Theorem 1 (§10.2)**: a homogeneous polynomial of degree `0 < d < n + 1` in
`n + 1` variables has a zero in projective space. -/
@[kb "irelandrosen1990" "Thm 1 (§10.2), Cor, p. 154"]
theorem exists_projective_zero {n d : ℕ} {h : MvPolynomial (Fin (n + 1)) F}
    (hh : h.IsHomogeneous d) (hd0 : 0 < d) (hd : d < n + 1) :
    ∃ P : ℙ F (Fin (n + 1) → F), MvPolynomial.eval P.rep h = 0 := by
  have h0 : MvPolynomial.eval 0 h = 0 := by
    have := hh.coeff_eq_zero (d := 0) (by simpa using hd0.ne)
    simpa [MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq] using this
  obtain ⟨x, hx, hx0⟩ := exists_ne_zero_eval_eq_zero h h0 (lt_of_le_of_lt hh.totalDegree_le hd)
  refine ⟨Projectivization.mk F x hx, ?_⟩
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep F x hx
  rw [← ha, Units.smul_def, eval_smul_of_isHomogeneous hh, hx0, mul_zero]

end Chevalley

end NTKB.IrelandRosen
