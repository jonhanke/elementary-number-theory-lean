/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Basic.Rel
import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram
import Mathlib.Order.Lattice.Nat
import Aesop.BuiltinRules
import Mathlib.Algebra.Group.End
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.List.GetD
import Mathlib.Logic.Equiv.PartialEquiv
import Mathlib.Order.SuccPred.Nat
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
import NTKB.Attr

/-!
# Partitions into odd unequal parts and self-conjugate partitions (Hardy–Wright § 19.5)

* **Theorem 347.** The number of partitions of `n` into odd unequal parts equals the number of
  self-conjugate partitions of `n` [hardywright2008, § 19.5, Theorem 347].

The book's proof reads a self-conjugate Ferrers graph along "bent lines" (hooks of the diagonal
cells).  Formally, for a symmetric Young diagram `μ` let `D` be the set of `i` with `(i, i) ∈ μ`, and
`frob μ = {rowLen i - i - 1 | i ∈ D}` (Frobenius coordinates).  The hook of `(i, i)` has
`2 (rowLen i - i) - 1` cells and each cell `(r, c)` lies in the hook of `min r c`, so
`∑_{a ∈ frob μ} (2a+1) = μ.card` (`sum_frob`).  The map `frob` is injective on symmetric diagrams
(`eq_of_frob_eq`) and surjective onto all finite sets `A` of naturals: the diagram `psi A` with cells
`(r, c)` such that `m = min r c < |A|` and `max r c ≤ l_m + m`, where `l` is `A` sorted decreasingly,
is a symmetric Young diagram with `frob (psi A) = A`.  Finally partitions into odd unequal parts
correspond to finite sets `A` with `∑ (2a+1) = n` via `A ↦ {2a+1 | a ∈ A}`.
-/

namespace NTKB.HardyWright

namespace SelfConjugate

open YoungDiagram Finset

/-- The diagonal of a Young diagram: the `i` with `(i, i) ∈ μ`. -/
def diag (μ : YoungDiagram) : Finset ℕ := (μ.cells.filter fun c => c.1 = c.2).image Prod.fst

lemma mem_diag {μ : YoungDiagram} {i : ℕ} : i ∈ diag μ ↔ (i, i) ∈ μ := by
  simp only [diag, Finset.mem_image, Finset.mem_filter, mem_cells, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨h, rfl⟩, rfl⟩
    exact h
  · intro h
    exact ⟨i, i, ⟨h, rfl⟩, rfl⟩

lemma mem_diag_iff {μ : YoungDiagram} {i : ℕ} : i ∈ diag μ ↔ i < μ.rowLen i := by
  rw [mem_diag, mem_iff_lt_rowLen]

/-- Frobenius coordinates `rowLen i - i - 1` of the diagonal cells. -/
def frob (μ : YoungDiagram) : Finset ℕ := (diag μ).image fun i => μ.rowLen i - i - 1

lemma frob_injOn (μ : YoungDiagram) :
    Set.InjOn (fun i => μ.rowLen i - i - 1) (diag μ : Set ℕ) := by
  intro i hi j hj h
  simp only [Finset.mem_coe, mem_diag_iff] at hi hj
  simp only at h
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := μ.rowLen_anti i j hlt.le
    omega
  · have := μ.rowLen_anti j i hlt.le
    omega

lemma symm_mem {μ : YoungDiagram} (hs : μ.transpose = μ) (a b : ℕ) :
    (a, b) ∈ μ ↔ (b, a) ∈ μ := by
  have h := @YoungDiagram.mem_transpose μ (b, a)
  rw [hs] at h
  simpa using h.symm

lemma card_fiber {μ : YoungDiagram} (hs : μ.transpose = μ) {i : ℕ} (hi : i ∈ diag μ) :
    (μ.cells.filter fun c => min c.1 c.2 = i).card = 2 * (μ.rowLen i - i - 1) + 1 := by
  rw [mem_diag_iff] at hi
  have hset : (μ.cells.filter fun c => min c.1 c.2 = i) =
      (Finset.Ico i (μ.rowLen i)).map ⟨fun j => (i, j), fun a b h => by simpa using h⟩ ∪
      (Finset.Ioo i (μ.rowLen i)).map ⟨fun j => (j, i), fun a b h => by simpa using h⟩ := by
    ext ⟨r, c⟩
    simp only [Finset.mem_filter, mem_cells, Finset.mem_union, Finset.mem_map,
      Finset.mem_Ico, Finset.mem_Ioo]
    constructor
    · rintro ⟨hm, hmin⟩
      rcases le_total r c with h | h
      · left
        rw [min_eq_left h] at hmin
        rw [mem_iff_lt_rowLen, hmin] at hm
        exact ⟨c, ⟨by omega, hm⟩, Prod.ext hmin.symm rfl⟩
      · rw [min_eq_right h] at hmin
        rw [symm_mem hs, mem_iff_lt_rowLen, hmin] at hm
        rcases Nat.eq_or_lt_of_le h with h' | h'
        · left
          exact ⟨r, ⟨by omega, hm⟩, Prod.ext (by show i = r; omega) (by show r = c; omega)⟩
        · right
          exact ⟨r, ⟨by omega, hm⟩, Prod.ext rfl (by show i = c; omega)⟩
    · rintro (⟨j, ⟨h1, h2⟩, e⟩ | ⟨j, ⟨h1, h2⟩, e⟩)
      · have e1 : i = r := congrArg Prod.fst e
        have e2 : j = c := congrArg Prod.snd e
        rw [← e1, ← e2]
        exact ⟨mem_iff_lt_rowLen.2 h2, min_eq_left h1⟩
      · have e1 : j = r := congrArg Prod.fst e
        have e2 : i = c := congrArg Prod.snd e
        rw [← e1, ← e2]
        refine ⟨?_, min_eq_right h1.le⟩
        rw [symm_mem hs, mem_iff_lt_rowLen]
        exact h2
  rw [hset, Finset.card_union_of_disjoint, Finset.card_map, Finset.card_map]
  · simp
    omega
  · rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_map, Finset.mem_Ico, Finset.mem_Ioo] at hx hx'
    obtain ⟨j, hj, rfl⟩ := hx
    obtain ⟨k, hk, hk'⟩ := hx'
    have e1 : k = i := congrArg Prod.fst hk'
    have e2 : i = j := congrArg Prod.snd hk'
    omega

/-- The sum of the hook sizes over the diagonal of a symmetric diagram is its cardinality. -/
theorem sum_frob {μ : YoungDiagram} (hs : μ.transpose = μ) :
    ∑ a ∈ frob μ, (2 * a + 1) = μ.card := by
  rw [frob, Finset.sum_image (frob_injOn μ)]
  have hmap : ∀ c ∈ μ.cells, min c.1 c.2 ∈ diag μ := by
    rintro ⟨r, c⟩ hc
    rw [mem_cells] at hc
    rw [mem_diag]
    rcases le_total r c with h | h
    · rw [min_eq_left h]
      exact μ.up_left_mem le_rfl h hc
    · rw [min_eq_right h]
      exact μ.up_left_mem h le_rfl hc
  rw [YoungDiagram.card, Finset.card_eq_sum_card_fiberwise hmap]
  exact Finset.sum_congr rfl fun i hi => (card_fiber hs hi).symm

lemma eq_range_of_down {D : Finset ℕ} (h : ∀ i ∈ D, ∀ j ≤ i, j ∈ D) : D = range D.card := by
  have hsub : D ⊆ range D.card := by
    intro i hi
    rw [Finset.mem_range]
    by_contra hn
    have hs : range (i + 1) ⊆ D := fun j hj => h i hi j (by simp at hj; omega)
    have := Finset.card_le_card hs
    simp at this
    omega
  exact Finset.eq_of_subset_of_card_le hsub (by simp)

lemma diag_down (μ : YoungDiagram) : ∀ i ∈ diag μ, ∀ j ≤ i, j ∈ diag μ := by
  intro i hi j hj
  rw [mem_diag_iff] at hi ⊢
  have := μ.rowLen_anti j i hj
  omega

lemma card_frob (μ : YoungDiagram) : (frob μ).card = (diag μ).card :=
  Finset.card_image_of_injOn (frob_injOn μ)

lemma eq_of_image_eq {f g : ℕ → ℕ} {d : ℕ} (hf : ∀ i j, i < j → j < d → f j < f i)
    (hg : ∀ i j, i < j → j < d → g j < g i)
    (h : (range d).image f = (range d).image g) : ∀ i < d, f i = g i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    have h1 : f i ∈ (range d).image g := h ▸ Finset.mem_image_of_mem f (Finset.mem_range.2 hi)
    have h2 : g i ∈ (range d).image f := h ▸ Finset.mem_image_of_mem g (Finset.mem_range.2 hi)
    obtain ⟨k, hk, hk'⟩ := Finset.mem_image.1 h1
    obtain ⟨k', hk2, hk2'⟩ := Finset.mem_image.1 h2
    rw [Finset.mem_range] at hk hk2
    have hki : i ≤ k := by
      by_contra hlt
      push Not at hlt
      have := ih k hlt (hk)
      have := hf k i hlt hi
      omega
    have hki2 : i ≤ k' := by
      by_contra hlt
      push Not at hlt
      have := ih k' hlt hk2
      have := hg k' i hlt hi
      omega
    have e1 : g k ≤ g i := by
      rcases Nat.eq_or_lt_of_le hki with h' | h'
      · rw [h']
      · exact (hg i k h' hk).le
    have e2 : f k' ≤ f i := by
      rcases Nat.eq_or_lt_of_le hki2 with h' | h'
      · rw [h']
      · exact (hf i k' h' hk2).le
    omega

/-- A symmetric Young diagram is determined by its Frobenius coordinates. -/
theorem eq_of_frob_eq {μ ν : YoungDiagram} (hμ : μ.transpose = μ) (hν : ν.transpose = ν)
    (h : frob μ = frob ν) : μ = ν := by
  have hcard : (diag μ).card = (diag ν).card := by rw [← card_frob, ← card_frob, h]
  set d := (diag μ).card with hd
  have hDμ : diag μ = range d := eq_range_of_down (diag_down μ)
  have hDν : diag ν = range d := by
    rw [hcard]; exact eq_range_of_down (diag_down ν)
  have hrow : ∀ i < d, μ.rowLen i = ν.rowLen i := by
    have himg : (range d).image (fun i => μ.rowLen i - i - 1) =
        (range d).image (fun i => ν.rowLen i - i - 1) := by
      have := h
      simp only [frob, hDμ, hDν] at this
      exact this
    have := eq_of_image_eq (d := d) (f := fun i => μ.rowLen i - i - 1)
      (g := fun i => ν.rowLen i - i - 1) ?_ ?_ himg
    · intro i hi
      have h1 := this i hi
      have h2 : i ∈ diag μ := by rw [hDμ]; exact Finset.mem_range.2 hi
      have h3 : i ∈ diag ν := by rw [hDν]; exact Finset.mem_range.2 hi
      rw [mem_diag_iff] at h2 h3
      omega
    · intro i j hij hj
      have h2 : j ∈ diag μ := by rw [hDμ]; exact Finset.mem_range.2 hj
      rw [mem_diag_iff] at h2
      have := μ.rowLen_anti i j hij.le
      omega
    · intro i j hij hj
      have h2 : j ∈ diag ν := by rw [hDν]; exact Finset.mem_range.2 hj
      rw [mem_diag_iff] at h2
      have := ν.rowLen_anti i j hij.le
      omega
  have key : ∀ r c, r ≤ c → ((r, c) ∈ μ ↔ (r, c) ∈ ν) := by
    intro r c hrc
    by_cases hr : r < d
    · rw [mem_iff_lt_rowLen, mem_iff_lt_rowLen, hrow r hr]
    · have h1 : (r, r) ∉ μ := by
        rw [← mem_diag, hDμ]; simpa using hr
      have h2 : (r, r) ∉ ν := by
        rw [← mem_diag, hDν]; simpa using hr
      constructor
      · intro hc; exact absurd (μ.up_left_mem le_rfl hrc hc) h1
      · intro hc; exact absurd (ν.up_left_mem le_rfl hrc hc) h2
  ext ⟨r, c⟩
  show (r, c) ∈ μ ↔ (r, c) ∈ ν
  rcases le_total r c with hrc | hrc
  · exact key r c hrc
  · rw [symm_mem hμ, symm_mem hν]
    exact key c r hrc

/-! ### The diagram attached to a finite set -/

/-- The `m`-th largest element of `A` (and `0` if there is none). -/
def lv (A : Finset ℕ) (m : ℕ) : ℕ := (A.sort (· ≥ ·)).getD m 0

lemma lv_eq {A : Finset ℕ} {m : ℕ} (h : m < A.card) :
    lv A m = (A.sort (· ≥ ·))[m]'(by rwa [Finset.length_sort]) := by
  unfold lv
  exact List.getD_eq_getElem _ _ _

lemma lv_mem {A : Finset ℕ} {m : ℕ} (h : m < A.card) : lv A m ∈ A := by
  rw [lv_eq h, ← Finset.mem_sort (· ≥ ·)]
  exact List.getElem_mem _

lemma lv_lt {A : Finset ℕ} {i j : ℕ} (hij : i < j) (hj : j < A.card) : lv A j < lv A i := by
  have hlen : j < (A.sort (· ≥ ·)).length := by rwa [Finset.length_sort]
  have hp : (A.sort (· ≥ ·)).Pairwise (· > ·) :=
    ((Finset.pairwise_sort A (· ≥ ·)).and (Finset.sort_nodup A (· ≥ ·))).imp
      fun ⟨h1, h2⟩ => lt_of_le_of_ne h1 (Ne.symm h2)
  rw [lv_eq hj, lv_eq (hij.trans hj)]
  exact List.pairwise_iff_getElem.1 hp i j (hij.trans hlen) hlen hij

lemma lv_add_le {A : Finset ℕ} {i j : ℕ} (hij : i ≤ j) (hj : j < A.card) :
    lv A j + j ≤ lv A i + i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    have h1 := lv_lt (Nat.lt_add_one j) hj
    have h2 := ih (by omega)
    omega

lemma image_lv (A : Finset ℕ) : (range A.card).image (lv A) = A := by
  ext a
  rw [Finset.mem_image]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact lv_mem (Finset.mem_range.1 hm)
  · intro ha
    rw [← Finset.mem_sort (· ≥ ·)] at ha
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ha
    have hi' : i < A.card := by rwa [Finset.length_sort] at hi
    exact ⟨i, Finset.mem_range.2 hi', lv_eq hi'⟩

lemma lv_le {A : Finset ℕ} {m : ℕ} (h : m < A.card) : lv A m ≤ A.sup id :=
  Finset.le_sup (f := id) (lv_mem h)

/-- The cells of the symmetric diagram attached to `A`. -/
def psiCells (A : Finset ℕ) : Finset (ℕ × ℕ) :=
  ((range (A.sup id + A.card + 1)) ×ˢ (range (A.sup id + A.card + 1))).filter fun c =>
    min c.1 c.2 < A.card ∧ max c.1 c.2 ≤ lv A (min c.1 c.2) + min c.1 c.2

lemma mem_psiCells {A : Finset ℕ} {r c : ℕ} :
    (r, c) ∈ psiCells A ↔ min r c < A.card ∧ max r c ≤ lv A (min r c) + min r c := by
  simp only [psiCells, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · rintro ⟨h1, h2⟩
    have := lv_le h1
    refine ⟨⟨?_, ?_⟩, h1, h2⟩ <;> omega

/-- The symmetric Young diagram attached to a finite set `A` of naturals. -/
def psi (A : Finset ℕ) : YoungDiagram where
  cells := psiCells A
  isLowerSet := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ hxy hx
    obtain ⟨ha, hb⟩ := Prod.mk_le_mk.1 hxy
    rw [Finset.mem_coe, mem_psiCells] at hx ⊢
    have hm : min a' b' ≤ min a b := min_le_min ha hb
    have hM : max a' b' ≤ max a b := max_le_max ha hb
    have := lv_add_le hm hx.1
    exact ⟨by omega, by omega⟩

lemma mem_psi {A : Finset ℕ} {r c : ℕ} :
    (r, c) ∈ psi A ↔ min r c < A.card ∧ max r c ≤ lv A (min r c) + min r c :=
  mem_psiCells

lemma transpose_psi (A : Finset ℕ) : (psi A).transpose = psi A := by
  ext ⟨r, c⟩
  show (r, c) ∈ (psi A).transpose ↔ (r, c) ∈ psi A
  rw [mem_transpose]
  show (c, r) ∈ psi A ↔ _
  rw [mem_psi, mem_psi, min_comm, max_comm]

lemma diag_psi (A : Finset ℕ) : diag (psi A) = range A.card := by
  ext i
  rw [mem_diag, mem_psi, Finset.mem_range, min_self, max_self]
  exact ⟨fun h => h.1, fun h => ⟨h, by omega⟩⟩

lemma rowLen_psi {A : Finset ℕ} {i : ℕ} (hi : i < A.card) :
    (psi A).rowLen i = lv A i + i + 1 := by
  have h : ∀ j, j < (psi A).rowLen i ↔ j < lv A i + i + 1 := by
    intro j
    rw [← mem_iff_lt_rowLen, mem_psi]
    rcases le_total i j with hij | hji
    · rw [min_eq_left hij, max_eq_right hij]
      exact ⟨fun h => by omega, fun h => ⟨hi, by omega⟩⟩
    · rw [min_eq_right hji, max_eq_left hji]
      have := lv_add_le hji hi
      exact ⟨fun _ => by omega, fun _ => ⟨by omega, by omega⟩⟩
  exact le_antisymm (not_lt.1 fun hlt => lt_irrefl _ ((h _).1 hlt))
    (not_lt.1 fun hlt => lt_irrefl _ ((h _).2 hlt))

lemma frob_psi (A : Finset ℕ) : frob (psi A) = A := by
  unfold frob
  rw [diag_psi]
  conv_rhs => rw [← image_lv A]
  apply Finset.image_congr
  intro i hi
  have hi' := Finset.mem_range.1 (Finset.mem_coe.1 hi)
  simp only
  rw [rowLen_psi hi']
  omega

/-! ### Odd unequal parts and finite sets -/

/-- The partition of `n` with parts `2a+1`, `a ∈ A`. -/
def partOfFinset (A : Finset ℕ) (n : ℕ) (h : ∑ a ∈ A, (2 * a + 1) = n) : n.Partition where
  parts := A.val.map fun a => 2 * a + 1
  parts_pos := by
    intro i hi
    obtain ⟨a, _, rfl⟩ := Multiset.mem_map.1 hi
    omega
  parts_sum := by rw [← h]; rfl

lemma partOfFinset_mem (A : Finset ℕ) (n : ℕ) (h : ∑ a ∈ A, (2 * a + 1) = n) :
    partOfFinset A n h ∈ Nat.Partition.oddDistincts n := by
  simp only [Nat.Partition.oddDistincts, Nat.Partition.odds, Nat.Partition.distincts,
    Nat.Partition.restricted, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
    partOfFinset]
  constructor
  · intro i hi
    obtain ⟨a, _, rfl⟩ := Multiset.mem_map.1 hi
    exact Nat.not_even_iff_odd.2 ⟨a, rfl⟩
  · exact A.nodup.map (fun a b h => by omega)

lemma odd_nodup {n : ℕ} {q : n.Partition} (hq : q ∈ Nat.Partition.oddDistincts n) :
    (∀ x ∈ q.parts, x % 2 = 1) ∧ q.parts.Nodup := by
  simp only [Nat.Partition.oddDistincts, Nat.Partition.odds, Nat.Partition.distincts,
    Nat.Partition.restricted, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
    true_and] at hq
  refine ⟨fun x hx => ?_, hq.2⟩
  have := hq.1 x hx
  rw [Nat.not_even_iff_odd] at this
  exact Nat.odd_iff.1 this

lemma val_image_half {s : Multiset ℕ} (hodd : ∀ x ∈ s, x % 2 = 1) (hnd : s.Nodup) :
    (s.toFinset.image (· / 2)).val.map (fun a => 2 * a + 1) = s := by
  have hinj : (s.map (· / 2)).Nodup :=
    Multiset.Nodup.map_on (fun x hx y hy h => by
      have := hodd x hx
      have := hodd y hy
      have h' : x / 2 = y / 2 := h
      omega) hnd
  have : (s.toFinset.image (· / 2)).val = s.map (· / 2) := by
    rw [Finset.image_val, Multiset.toFinset_val, Multiset.dedup_eq_self.2 hnd,
      Multiset.dedup_eq_self.2 hinj]
  rw [this, Multiset.map_map]
  conv_rhs => rw [← Multiset.map_id s]
  apply Multiset.map_congr rfl
  intro x hx
  have := hodd x hx
  simp only [Function.comp, id]
  omega

lemma conj_iff {n : ℕ} (p : Nat.Partition n) :
    p.conjugate = p ↔ (ofPartition p).transpose = ofPartition p := by
  constructor
  · intro h
    have := congrArg YoungDiagram.ofPartition h
    simpa [Nat.Partition.conjugate] using this
  · intro h
    apply YoungDiagram.equivPartition.symm.injective
    apply Subtype.ext
    show ofPartition p.conjugate = ofPartition p
    simp [Nat.Partition.conjugate, h]

/-- The partition into odd unequal parts attached to a self-conjugate partition. -/
def toOdd (n : ℕ) (p : Nat.Partition n) (hp : p.conjugate = p) : n.Partition :=
  partOfFinset (frob (ofPartition p)) n
    (by rw [sum_frob ((conj_iff p).1 hp), card_ofPartition])

end SelfConjugate

open SelfConjugate in
/-- **Theorem 347.** The partitions of `n` into odd unequal parts are equinumerous with the
self-conjugate partitions of `n`. -/
@[kb "hardywright2008" "Thm 347, p. 388"]
theorem card_oddDistincts_eq_card_selfConjugate (n : ℕ) :
    (Nat.Partition.oddDistincts n).card =
      ((Finset.univ : Finset (Nat.Partition n)).filter fun p ↦ p.conjugate = p).card := by
  symm
  refine Finset.card_bij (fun p hp => toOdd n p (Finset.mem_filter.1 hp).2) ?_ ?_ ?_
  · intro p hp
    exact partOfFinset_mem _ _ _
  · intro p hp q hq h
    have h1 := congrArg Nat.Partition.parts h
    have h2 : (frob (YoungDiagram.ofPartition p)).val = (frob (YoungDiagram.ofPartition q)).val :=
      Multiset.map_injective (fun a b (h : 2 * a + 1 = 2 * b + 1) => by omega) h1
    have h3 := eq_of_frob_eq ((conj_iff p).1 (Finset.mem_filter.1 hp).2)
      ((conj_iff q).1 (Finset.mem_filter.1 hq).2) (Finset.val_inj.1 h2)
    exact YoungDiagram.equivPartition.symm.injective (Subtype.ext h3)
  · intro q hq
    obtain ⟨hodd, hnd⟩ := odd_nodup hq
    set A := q.parts.toFinset.image (· / 2) with hAdef
    have hA : A.val.map (fun a => 2 * a + 1) = q.parts := val_image_half hodd hnd
    have hsum : ∑ a ∈ A, (2 * a + 1) = n := by
      rw [Finset.sum_eq_multiset_sum, hA]
      exact q.parts_sum
    have hcard : (psi A).card = n := by
      rw [← sum_frob (transpose_psi A), frob_psi]
      exact hsum
    have hof : YoungDiagram.ofPartition ((psi A).toPartition hcard) = psi A :=
      YoungDiagram.ofPartition_toPartition hcard
    have hmem : (psi A).toPartition hcard ∈
        (Finset.univ : Finset (Nat.Partition n)).filter fun p ↦ p.conjugate = p := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, (conj_iff _).2 ?_⟩
      rw [hof]
      exact transpose_psi A
    refine ⟨(psi A).toPartition hcard, hmem, ?_⟩
    apply Nat.Partition.ext
    show (frob (YoungDiagram.ofPartition ((psi A).toPartition hcard))).val.map _ = q.parts
    rw [hof, frob_psi]
    exact hA

end NTKB.HardyWright
