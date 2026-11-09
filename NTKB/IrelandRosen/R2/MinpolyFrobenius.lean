/-
Ireland–Rosen, Chapter 11, §2, Proposition 11.2.4 (a): if `F ⊆ K` are finite fields, `q = #F`,
and `f` is the minimal polynomial over `F` of `α ∈ K`, of degree `d`, then
`f(x) = (x - α)(x - α^q) ⋯ (x - α^{q^{d-1}})`. (Parts (b), (c) are in Mathlib:
`trace_eq_finrank_mul_minpoly_nextCoeff`, `Algebra.norm_eq_norm_adjoin` with
`Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly`.)
-/
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Minpoly.Field
import NTKB.Attr

open Polynomial Finset

namespace NTKB.IrelandRosen

variable {F : Type*} [Field F] [Fintype F] {K : Type*} [Field K] [Fintype K] [Algebra F K]

/-- **Proposition 11.2.4 (a).** The minimal polynomial of `α` over `F` is
`∏_{i < d} (x - α^{q^i})`. -/
@[kb "irelandrosen1990" "Prop 11.2.4, p. 171"]
theorem minpoly_map_eq_prod (α : K) :
    (minpoly F α).map (algebraMap F K) =
      ∏ i ∈ range (minpoly F α).natDegree, (X - C (α ^ Fintype.card F ^ i)) := by
  classical
  set f := minpoly F α with hf
  set d := f.natDegree
  set q := Fintype.card F
  have hint : IsIntegral F α := .of_finite F α
  have hfm : f.Monic := minpoly.monic hint
  set σ := FiniteField.frobeniusAlgEquivOfAlgebraic F K
  have hσ : ∀ (i : ℕ) (x : K), (σ ^ i) x = x ^ q ^ i := by
    intro i x
    rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
  have hroot : ∀ i, aeval (α ^ q ^ i) f = 0 := by
    intro i
    rw [← hσ, ← AlgEquiv.coe_algHom, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  -- the conjugates `α^{q^i}`, `i < d`, are distinct
  have hinj : Set.InjOn (fun i => α ^ q ^ i) (range d : Set ℕ) := by
    have key : ∀ i j, i < j → j < d → α ^ q ^ i ≠ α ^ q ^ j := by
      intro i j hij hjd h
      have hk : α ^ q ^ (j - i) = α := by
        rw [← hσ, ← hσ] at h
        have : (σ ^ j) α = (σ ^ i) ((σ ^ (j - i)) α) := by
          rw [← AlgEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' hij.le]
        rw [this] at h
        rw [← hσ]
        exact ((σ ^ i).injective h).symm
      have hdvd : f ∣ X ^ Nat.card F ^ (j - i) - X := by
        apply minpoly.dvd
        simp only [map_sub, map_pow, aeval_X, Nat.card_eq_fintype_card]
        exact sub_eq_zero.mpr hk
      have hd : d ∣ j - i := (minpoly.irreducible hint).natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hdvd
      have := Nat.le_of_dvd (by omega) hd
      omega
    intro i hi j hj h
    simp only [coe_range, Set.mem_Iio] at hi hj
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact key i j hlt hj h
    · exact key j i hlt hi h.symm
  set M := (range d).val.map fun i => α ^ q ^ i
  have hM : M.Nodup := Multiset.Nodup.map_on (fun i hi j hj h => hinj hi hj h) (range d).nodup
  have hf0 : f.map (algebraMap F K) ≠ 0 := (hfm.map _).ne_zero
  have hle : M ≤ (f.map (algebraMap F K)).roots := by
    rw [Multiset.le_iff_subset hM]
    intro x hx
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hx
    rw [mem_roots hf0, IsRoot, eval_map_algebraMap]
    exact hroot i
  have hcard : Multiset.card (f.map (algebraMap F K)).roots ≤ Multiset.card M := by
    rw [Multiset.card_map, Finset.card_val, card_range]
    exact (card_roots' _).trans (natDegree_map_le)
  have hroots : M = (f.map (algebraMap F K)).roots := Multiset.eq_of_le_of_card_le hle hcard
  have hcard' : Multiset.card (f.map (algebraMap F K)).roots = (f.map (algebraMap F K)).natDegree := by
    rw [← hroots, Multiset.card_map, Finset.card_val, card_range, natDegree_map]
  rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hfm.map _) hcard', ← hroots,
    Multiset.map_map, Finset.prod_eq_multiset_prod]
  rfl

end NTKB.IrelandRosen
