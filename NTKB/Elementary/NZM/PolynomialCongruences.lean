/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Splits
import NTKB.Attr

/-!
# Polynomial congruences modulo a prime (Niven–Zuckerman–Montgomery, § 2.7)

* **Theorem 2.25.** A congruence `f(x) ≡ 0 (mod p)` of degree `≥ p` is either satisfied by every
  integer or equivalent to a monic one of degree `< p`.
* **Theorem 2.29.** A monic congruence `f(x) ≡ 0 (mod p)` of degree `n` has `n` solutions iff `f`
  divides `x^p - x` modulo `p`.

Polynomials with integer coefficients modulo `p` are polynomials over `ZMod p`; the solutions of the
congruence are the roots in `ZMod p`. The hypothesis `n ≤ p` is automatic in the book's Theorem 2.29
(both sides force it) and is not needed.
-/

open Polynomial

namespace NTKB.NZM

section Aux

variable {p : ℕ} [hp : Fact p.Prime]

/-- The roots of `X ^ p - X` over `ZMod p` are all the residues, each once. -/
theorem roots_X_pow_sub_X_zmod :
    (X ^ p - X : (ZMod p)[X]).roots = Finset.univ.val := by
  simpa using FiniteField.roots_X_pow_card_sub_X (ZMod p)

theorem X_pow_sub_X_zmod_ne_zero : (X ^ p - X : (ZMod p)[X]) ≠ 0 :=
  X_pow_sub_X_ne_zero hp.out.one_lt

theorem splits_X_pow_sub_X_zmod : Splits (X ^ p - X : (ZMod p)[X]) := by
  rw [splits_iff_card_roots, roots_X_pow_sub_X_zmod, ← Finset.card_def, Finset.card_univ,
    natDegree_X_pow_sub_X hp.out.one_lt, ZMod.card]

theorem monic_X_pow_sub_X_zmod : (X ^ p - X : (ZMod p)[X]).Monic := by
  apply monic_X_pow_sub
  rw [degree_X]
  exact_mod_cast hp.out.one_lt

end Aux

/-- **Theorem 2.29.** A monic polynomial `f` over `ZMod p` has `n = deg f` distinct roots in
`ZMod p` (the congruence `f(x) ≡ 0 (mod p)` has `n` solutions) if and only if `f` divides
`X ^ p - X` in `(ZMod p)[X]`. -/
@[kb "nivenzuckermanmontgomery" "Thm 2.29, p. 94"]
theorem card_roots_eq_natDegree_iff_dvd {p : ℕ} [Fact p.Prime] {f : (ZMod p)[X]}
    (hf : f.Monic) :
    f.roots.toFinset.card = f.natDegree ↔ f ∣ X ^ p - X := by
  constructor
  · intro h
    have hle : Multiset.card f.roots ≤ f.natDegree := card_roots' f
    have hge : f.roots.toFinset.card ≤ Multiset.card f.roots := Multiset.toFinset_card_le _
    have hcard : Multiset.card f.roots = f.natDegree := by omega
    have hsp : f.Splits := splits_iff_card_roots.mpr hcard
    have hnd : f.roots.Nodup :=
      Multiset.toFinset_card_eq_card_iff_nodup.mp (by omega)
    apply hsp.dvd_of_roots_le_roots hf.ne_zero
    rw [roots_X_pow_sub_X_zmod, Multiset.le_iff_subset hnd]
    intro a _
    simp
  · intro hd
    have hsp : f.Splits := splits_X_pow_sub_X_zmod.of_dvd X_pow_sub_X_zmod_ne_zero hd
    have hnd : f.roots.Nodup := by
      refine Multiset.nodup_of_le (roots.le_of_dvd X_pow_sub_X_zmod_ne_zero hd) ?_
      rw [roots_X_pow_sub_X_zmod]
      exact Finset.univ.nodup
    exact (Multiset.toFinset_card_eq_card_iff_nodup.mpr hnd).trans
      hsp.natDegree_eq_card_roots.symm

/-- **Theorem 2.25** (reduction step). Reducing `f` modulo the monic polynomial `X ^ p - X` gives
a polynomial of degree `< p` taking the same values as `f` on `ZMod p` (Fermat). -/
@[kb "nivenzuckermanmontgomery" "Thm 2.25, p. 92"]
theorem natDegree_modByMonic_lt_and_eval_eq {p : ℕ} [hp : Fact p.Prime] (f : (ZMod p)[X]) :
    (f %ₘ (X ^ p - X)).natDegree < p ∧ ∀ a : ZMod p, f.eval a = (f %ₘ (X ^ p - X)).eval a := by
  have hdeg : (X ^ p - X : (ZMod p)[X]).natDegree = p := natDegree_X_pow_sub_X hp.out.one_lt
  have hne : (X ^ p - X : (ZMod p)[X]) ≠ 1 := by
    intro h
    rw [h, natDegree_one] at hdeg
    exact hp.out.ne_zero hdeg.symm
  refine ⟨?_, ?_⟩
  · have := natDegree_modByMonic_lt f (monic_X_pow_sub_X_zmod (p := p)) hne
    rwa [hdeg] at this
  · intro a
    have h := congrArg (eval a) (modByMonic_add_div f (X ^ p - X : (ZMod p)[X]))
    simp only [eval_add, eval_mul, eval_sub, eval_pow, eval_X, ZMod.pow_card, sub_self,
      zero_mul, add_zero] at h
    exact h.symm

/-- **Theorem 2.25.** If `f` has degree `≥ p`, then either every residue is a solution of
`f(x) ≡ 0 (mod p)`, or there is a monic polynomial `g` of degree `< p` with exactly the same
solutions. -/
@[kb "nivenzuckermanmontgomery" "Thm 2.25, p. 92"]
theorem eval_eq_zero_or_exists_monic {p : ℕ} [hp : Fact p.Prime] (f : (ZMod p)[X])
    (_hf : p ≤ f.natDegree) :
    (∀ a : ZMod p, f.eval a = 0) ∨
      ∃ g : (ZMod p)[X], g.Monic ∧ g.natDegree < p ∧
        ∀ a : ZMod p, f.eval a = 0 ↔ g.eval a = 0 := by
  obtain ⟨hlt, heval⟩ := natDegree_modByMonic_lt_and_eval_eq f
  by_cases h : f %ₘ (X ^ p - X) = 0
  · left
    intro a
    rw [heval a, h, eval_zero]
  · right
    refine ⟨(f %ₘ (X ^ p - X)) * C (leadingCoeff (f %ₘ (X ^ p - X)))⁻¹,
      monic_mul_leadingCoeff_inv h, ?_, ?_⟩
    · rwa [natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.mpr h))]
    · intro a
      rw [heval a, eval_mul, eval_C]
      constructor
      · intro h0
        rw [h0, zero_mul]
      · intro h0
        exact (mul_eq_zero.mp h0).resolve_right (inv_ne_zero (leadingCoeff_ne_zero.mpr h))

end NTKB.NZM
