/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.FieldTheory.Finite.GaloisField
import NTKB.IrelandRosen.R1.FiniteFields

/-!
# Ireland–Rosen, Chapter 7, Section 1: roots of `x^q - x` and subfields of a finite field

* **Corollary 1 to Proposition 7.1.1**: if `F ⊆ K` with `F` a finite field of `q` elements, then
  `a ∈ K` lies in `F` iff `a^q = a`.
* **Corollary 2 to Proposition 7.1.1**: if `f ∣ x^q - x` in `F[x]` then `f` has `deg f` distinct
  roots in `F`.
* **Proposition 7.1.5**: the subfields of a finite field with `p^n` elements correspond to the
  divisors of `n`: each subfield has `p^d` elements with `d ∣ n`, and for each `d ∣ n` there is
  exactly one subfield with `p^d` elements, namely `{α | α^(p^d) = α}`.
-/

open Polynomial

namespace NTKB.IrelandRosen

/-- **Ireland–Rosen, Corollary 1 to Proposition 7.1.1.** If `F` is a finite subfield of a field
`K` with `q` elements, then `a ∈ K` lies in `F` iff `a^q = a`: the roots of `x^q - x` (at most
`q` of them) are the elements of `F`. -/
@[kb "irelandrosen1990" "Ch 7, Corollary 1 to Prop 7.1.1, p. 90"]
theorem mem_subfield_iff_pow_card_eq {K : Type*} [Field K] (F : Subfield K) [Finite F] (a : K) :
    a ∈ F ↔ a ^ Nat.card F = a := by
  classical
  have := Fintype.ofFinite F
  constructor
  · intro ha
    have := FiniteField.pow_card (⟨a, ha⟩ : F)
    rw [← Nat.card_eq_fintype_card] at this
    exact congrArg Subtype.val this
  · intro ha
    by_contra hnot
    have hq : 1 < Nat.card F := Finite.one_lt_card
    set g : K[X] := X ^ Nat.card F - X
    have hg0 : g ≠ 0 := X_pow_sub_X_ne_zero hq
    set S : Finset K := (Finset.univ : Finset F).map ⟨Subtype.val, Subtype.val_injective⟩
    have hsub : insert a S ⊆ g.roots.toFinset := by
      intro x hx
      rw [Multiset.mem_toFinset, mem_roots hg0, IsRoot.def, eval_sub, eval_pow, eval_X,
        sub_eq_zero]
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ha
      · obtain ⟨y, -, rfl⟩ := Finset.mem_map.mp hx
        have := FiniteField.pow_card y
        rw [← Nat.card_eq_fintype_card] at this
        exact congrArg Subtype.val this
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (fun h ↦ hnot (by
      obtain ⟨y, -, rfl⟩ := Finset.mem_map.mp h; exact y.2)), Finset.card_map,
      Finset.card_univ, ← Nat.card_eq_fintype_card] at hcard
    have := (Multiset.toFinset_card_le g.roots).trans (card_roots' g)
    rw [natDegree_X_pow_sub_X hq] at this
    omega

/-- **Ireland–Rosen, Corollary 2 to Proposition 7.1.1.** In `F[x]`, `F` a finite field with `q`
elements, a divisor `f` of `x^q - x` has `deg f` distinct roots in `F`. -/
@[kb "irelandrosen1990" "Ch 7, Corollary 2 to Prop 7.1.1, p. 91"]
theorem roots_nodup_and_card_of_dvd {F : Type*} [Field F] [Finite F] {f : F[X]}
    (hf : f ∣ X ^ Nat.card F - X) : f.roots.Nodup ∧ f.roots.card = f.natDegree := by
  classical
  have := Fintype.ofFinite F
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hg0 : (X ^ Nat.card F - X : F[X]) ≠ 0 := X_pow_sub_X_ne_zero hq
  obtain ⟨p, hp⟩ := CharP.exists F
  have hsep : (X ^ Nat.card F - X : F[X]).Separable := by
    apply galois_poly_separable p
    obtain ⟨m, -, hcard⟩ := FiniteField.card F p
    rw [Nat.card_eq_fintype_card, hcard]
    exact dvd_pow_self _ (PNat.ne_zero m)
  have hsplit : Splits (X ^ Nat.card F - X : F[X]) := by
    rw [splits_iff_card_roots, Nat.card_eq_fintype_card, FiniteField.roots_X_pow_card_sub_X,
      natDegree_X_pow_sub_X (by rwa [← Nat.card_eq_fintype_card])]
    rfl
  exact ⟨nodup_roots (hsep.of_dvd hf), ((hsplit.of_dvd hg0 hf).natDegree_eq_card_roots).symm⟩

section Prop715

variable {F : Type*} [Field F] [Finite F] {p : ℕ} [hp : Fact p.Prime] [CharP F p]

omit hp in
/-- A subfield of a finite field of characteristic `p` has `p^d` elements for some `d ≥ 1`. -/
theorem exists_card_subfield_eq_pow (E : Subfield F) : ∃ d, 0 < d ∧ Nat.card E = p ^ d := by
  have := Fintype.ofFinite E
  have : CharP E p := (RingHom.charP_iff_charP E.subtype p).mpr inferInstance
  obtain ⟨d, -, hd⟩ := FiniteField.card E p
  exact ⟨d, d.pos, by rw [Nat.card_eq_fintype_card, hd]⟩

/-- **Ireland–Rosen, Proposition 7.1.5, first half.** If `F` has `p^n` elements, every subfield
of `F` has `p^d` elements with `d ∣ n`. (`E*` is a subgroup of `F*`, so `p^d - 1 ∣ p^n - 1`, and
`d ∣ n` by Lemma 3.) -/
@[kb "irelandrosen1990" "Prop 7.1.5, p. 93"]
theorem exists_dvd_card_subfield {n : ℕ} (hF : Nat.card F = p ^ n) (E : Subfield F) :
    ∃ d, d ∣ n ∧ Nat.card E = p ^ d := by
  obtain ⟨d, -, hd⟩ := exists_card_subfield_eq_pow (p := p) E
  refine ⟨d, ?_, hd⟩
  rw [← pow_sub_one_dvd_pow_sub_one_iff hp.out.one_lt]
  -- Lagrange in `F*`
  have hinj : Function.Injective (Units.map (E.subtype : E →* F)) :=
    Units.map_injective (Subtype.val_injective)
  have := Subgroup.card_subgroup_dvd_card (Units.map (E.subtype : E →* F)).range
  rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_units, Nat.card_units, hd,
    hF] at this
  exact this

/-- The subfield `{α | α^(p^d) = α}` of a finite field of characteristic `p`. -/
def subfieldPowEq (F : Type*) [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] (d : ℕ) :
    Subfield F where
  carrier := {x | x ^ p ^ d = x}
  mul_mem' {a b} ha hb := by simp only [Set.mem_ofPred_eq] at *; rw [mul_pow, ha, hb]
  one_mem' := by simp
  add_mem' {a b} ha hb := by simp only [Set.mem_ofPred_eq] at *; rw [add_pow_char_pow, ha, hb]
  zero_mem' := by
    show (0 : F) ^ p ^ d = 0
    exact zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  neg_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    rw [show -a = 0 - a by ring, sub_pow_char_pow, ha, zero_pow
      (Nat.pos_iff_ne_zero.mp (pow_pos (Fact.out : p.Prime).pos d))]
  inv_mem' {a} ha := by simp only [Set.mem_ofPred_eq] at *; rw [inv_pow, ha]

omit [Finite F] in
theorem mem_subfieldPowEq {d : ℕ} {x : F} : x ∈ subfieldPowEq F p d ↔ x ^ p ^ d = x := Iff.rfl

/-- **Ireland–Rosen, Proposition 7.1.5, second half.** If `F` has `p^n` elements and `d ∣ n`,
there is exactly one subfield of `F` with `p^d` elements, namely `{α | α^(p^d) = α}`: it has
`p^d` elements because `x^(p^d) - x` divides `x^(p^n) - x` (Lemmas 2 and 3) and so has `p^d`
distinct roots (Corollary 2 to Proposition 7.1.1), and any subfield with `p^d` elements is
contained in it (Corollary 1). -/
@[kb "irelandrosen1990" "Prop 7.1.5, p. 93"]
theorem existsUnique_subfield_card_eq {n : ℕ} (hF : Nat.card F = p ^ n) {d : ℕ} (hd : d ∣ n) :
    ∃! E : Subfield F, Nat.card E = p ^ d := by
  classical
  have hp1 : 1 < p := hp.out.one_lt
  have hn0 : n ≠ 0 := by
    rintro rfl
    have : 1 < Nat.card F := Finite.one_lt_card
    rw [hF, pow_zero] at this
    exact lt_irrefl _ this
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hn0)
  have hpd : 1 < p ^ d := Nat.one_lt_pow hd0.ne' hp1
  -- `x^(p^d) - x ∣ x^(p^n) - x`
  have hdvd : (X ^ p ^ d - X : F[X]) ∣ X ^ Nat.card F - X := by
    rw [hF]
    have h1 : (X ^ (p ^ d - 1) - 1 : F[X]) ∣ X ^ (p ^ n - 1) - 1 :=
      X_pow_sub_one_dvd_X_pow_sub_one_iff.mpr
        ((pow_sub_one_dvd_pow_sub_one_iff hp1).mpr hd)
    have e1 : (X ^ p ^ d - X : F[X]) = X * (X ^ (p ^ d - 1) - 1) := by
      rw [mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel hpd.le]
    have e2 : (X ^ p ^ n - X : F[X]) = X * (X ^ (p ^ n - 1) - 1) := by
      have : 1 ≤ p ^ n := Nat.one_le_pow _ _ hp.out.pos
      rw [mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel this]
    rw [e1, e2]
    exact mul_dvd_mul_left X h1
  obtain ⟨hnodup, hcardroots⟩ := roots_nodup_and_card_of_dvd hdvd
  rw [natDegree_X_pow_sub_X hpd] at hcardroots
  -- the subfield `{α | α^(p^d) = α}` has `p^d` elements
  have hE : Nat.card (subfieldPowEq F p d) = p ^ d := by
    rw [← hcardroots, ← Multiset.toFinset_card_of_nodup hnodup, ← Nat.card_eq_finsetCard]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x ↦ ?_)
    rw [mem_subfieldPowEq, Multiset.mem_toFinset,
      mem_roots (X_pow_sub_X_ne_zero hpd), IsRoot.def, eval_sub, eval_pow, eval_X, sub_eq_zero]
  refine ⟨subfieldPowEq F p d, hE, fun E hEcard ↦ ?_⟩
  -- uniqueness: `E ⊆ {α | α^(p^d) = α}` by Corollary 1, and the cardinalities agree
  have hle : E ≤ subfieldPowEq F p d := fun x hx ↦ by
    rw [mem_subfieldPowEq, ← hEcard]
    exact (mem_subfield_iff_pow_card_eq E x).mp hx
  have hfin : (subfieldPowEq F p d : Set F).Finite := Set.toFinite _
  exact SetLike.coe_injective (Set.Finite.eq_of_subset_of_card_le hfin hle
    (show Nat.card (subfieldPowEq F p d) ≤ Nat.card E from (hE.trans hEcard.symm).le))

end Prop715

end NTKB.IrelandRosen
