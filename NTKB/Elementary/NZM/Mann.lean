/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Attr
import Mathlib.Combinatorics.Schnirelmann
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Tactic.Linarith

/-!
# Mann's `α + β` theorem (Niven–Zuckerman–Montgomery, § 11.2)

Fix `g`.  For a finite set `A` of naturals, `cnt A m = #(A ∩ [1, m])` is the counting function
`A(m)` of the book (the element `0` is not counted).  The hypothesis (11.4) of the book is
`MannCond θ g A B`: `θ m ≤ A(m) + B(m)` for `1 ≤ m ≤ g`.

The proof of Theorem 11.9 is an induction on `B(g)`, shifting `B` into `A`:

* Lemma 11.4: if `B ⊄ A`, replace `(A, B)` by `(A ∪ B, A ∩ B)`.
* `exists_a₀`: the number `a₀` of the book, used when `B ⊆ A` and `B(g) > 0`.
* Lemmas 11.5, 11.6: counting estimates below and around `a₀`.
* Lemmas 11.7, 11.8: the transformation `A₂ = A ∪ A'`, `B₂ = B \ B'` (with
  `B' = {b ∈ B : a₀ + b ∉ A}`, `A' = {a₀ + b : b ∈ B', a₀ + b ≤ g}`).
* Theorem 11.9: `θ g ≤ C(g)` for `C = A + B` (finite form, in `Finset ℕ`).
* Theorem 11.10: `min 1 (d A + d B) ≤ d (A + B)` for Mathlib's `schnirelmannDensity`.

Deviations: the finite form needs neither `0 < θ` nor `g ∉ A + B`.  The sets in Lemmas 11.5, 11.6
are described by the property `hmin` of `a₀` (for `a < a₀`, `a ∈ A`, `b ∈ B` one has `a + b ∈ A`)
rather than by the definition of `a₀`; `exists_a₀` shows that the book's `a₀` has it.
-/

open Finset
open scoped Pointwise

namespace NTKB.NZM

/-- The counting function `A(m) = #{a ∈ A : 1 ≤ a ≤ m}` (zero is not counted). -/
def cnt (S : Finset ℕ) (m : ℕ) : ℕ := #(S ∩ Ioc 0 m)

/-- Hypothesis (11.4): `θ m ≤ A(m) + B(m)` for `1 ≤ m ≤ g`. -/
def MannCond (θ : ℝ) (g : ℕ) (A B : Finset ℕ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → m ≤ g → θ * m ≤ cnt A m + cnt B m

lemma cnt_zero (S : Finset ℕ) : cnt S 0 = 0 := by simp [cnt]

lemma cnt_empty (m : ℕ) : cnt ∅ m = 0 := by simp [cnt]

lemma cnt_mono_set {S T : Finset ℕ} (h : S ⊆ T) (m : ℕ) : cnt S m ≤ cnt T m :=
  card_le_card (inter_subset_inter_right h)

lemma cnt_union_add_cnt_inter (A B : Finset ℕ) (m : ℕ) :
    cnt (A ∪ B) m + cnt (A ∩ B) m = cnt A m + cnt B m := by
  unfold cnt
  rw [← card_union_add_card_inter (A ∩ Ioc 0 m) (B ∩ Ioc 0 m)]
  have h1 : (A ∪ B) ∩ Ioc 0 m = A ∩ Ioc 0 m ∪ B ∩ Ioc 0 m := by
    ext x; simp only [mem_inter, mem_union]; tauto
  have h2 : (A ∩ B) ∩ Ioc 0 m = A ∩ Ioc 0 m ∩ (B ∩ Ioc 0 m) := by
    ext x; simp only [mem_inter]; tauto
  rw [h1, h2]

lemma cnt_split (S : Finset ℕ) {m n : ℕ} (h : m ≤ n) :
    cnt S n = cnt S m + #(S.filter fun a => m < a ∧ a ≤ n) := by
  unfold cnt
  rw [← card_union_of_disjoint]
  · congr 1
    ext x
    simp only [mem_inter, mem_union, mem_Ioc, mem_filter]
    by_cases hx : x ∈ S <;> simp only [hx, true_and, false_and, or_false]; omega
  · rw [disjoint_left]
    intro x hx hx'
    simp only [mem_inter, mem_Ioc, mem_filter] at hx hx'
    omega

lemma cnt_of_mem {S : Finset ℕ} {b : ℕ} (hb : b ∈ S) (hb0 : 0 < b) :
    cnt S b = cnt S (b - 1) + 1 := by
  rw [cnt_split S (Nat.sub_le b 1)]
  congr 1
  rw [card_eq_one]
  refine ⟨b, ?_⟩
  ext x
  simp only [mem_filter, mem_singleton]
  constructor
  · rintro ⟨_, h1, h2⟩; omega
  · rintro rfl; exact ⟨hb, by omega, le_rfl⟩

lemma exists_of_cnt_pos {S : Finset ℕ} {m : ℕ} (h : 0 < cnt S m) : ∃ b ∈ S, 0 < b ∧ b ≤ m := by
  obtain ⟨b, hb⟩ := card_pos.1 h
  rw [mem_inter, mem_Ioc] at hb
  exact ⟨b, hb.1, hb.2⟩

lemma MannCond.le {θ : ℝ} {g : ℕ} {A B : Finset ℕ} (h : MannCond θ g A B) {m : ℕ} (hm : m ≤ g) :
    θ * m ≤ cnt A m + cnt B m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm1
  · simp [cnt_zero]
  · exact h m hm1 hm

/-- Arithmetic of the chain `θ(b-1) + 1 + θ(z-b) ≥ θ z`. -/
lemma chain {θ : ℝ} (hθ : θ ≤ 1) {b z : ℕ} (hb : 1 ≤ b) (hbz : b ≤ z) {P Q : ℝ}
    (hP : θ * ((b - 1 : ℕ) : ℝ) ≤ P) (hQ : θ * ((z - b : ℕ) : ℝ) ≤ Q) : θ * z ≤ P + 1 + Q := by
  rw [Nat.cast_sub hb, Nat.cast_one] at hP
  rw [Nat.cast_sub hbz] at hQ
  nlinarith

/-- The number `a₀` of the book (before Lemma 11.5): the least `a ∈ A` for which some
`b ∈ B` has `a + b ∉ A`.  Here `B ⊆ A` and `B` contains a positive element. -/
theorem exists_a₀ {A B : Finset ℕ} (hA0 : 0 ∈ A) (hBA : B ⊆ A) (hpos : ∃ b ∈ B, 0 < b) :
    ∃ a₀ ∈ A, 1 ≤ a₀ ∧ (∃ b ∈ B, a₀ + b ∉ A) ∧ ∀ a ∈ A, a < a₀ → ∀ b ∈ B, a + b ∈ A := by
  classical
  obtain ⟨b, hbB, hb0⟩ := hpos
  have hex : ∃ a, a ∈ A ∧ ∃ b ∈ B, a + b ∉ A := by
    refine ⟨A.max' ⟨0, hA0⟩, max'_mem _ _, b, hbB, fun h => ?_⟩
    have := le_max' A _ h
    omega
  obtain ⟨ha0, b1, hb1, hnot⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, ha0, ?_, ⟨b1, hb1, hnot⟩, ?_⟩
  · by_contra hlt
    have h0 : Nat.find hex = 0 := by omega
    rw [h0, zero_add] at hnot
    exact hnot (hBA hb1)
  · intro a ha hlt b' hb'
    by_contra hh
    exact Nat.find_min hex hlt ⟨ha, b', hb', hh⟩

/-- Lemma 11.5. -/
@[kb "nivenzuckermanmontgomery" "Lemma 11.5, p. 478"]
theorem lemma_11_5 {A B : Finset ℕ} {a₀ : ℕ}
    (hmin : ∀ a ∈ A, a < a₀ → ∀ b ∈ B, a + b ∈ A) {b z : ℕ} (hb : b ∈ B) (hbz : b ≤ z)
    (hz : z < b + a₀) :
    (∀ a ∈ A, 1 ≤ a → a ≤ z - b → a + b ∈ A) ∧ cnt A b + cnt A (z - b) ≤ cnt A z := by
  have h1 : ∀ a ∈ A, 1 ≤ a → a ≤ z - b → a + b ∈ A :=
    fun a ha _ hab => hmin a ha (by omega) b hb
  refine ⟨h1, ?_⟩
  rw [cnt_split A hbz]
  have : cnt A (z - b) ≤ #(A.filter fun a => b < a ∧ a ≤ z) := by
    unfold cnt
    refine card_le_card_of_injOn (· + b) ?_ ?_
    · intro a ha
      simp only [coe_inter, Set.mem_inter_iff, mem_coe, mem_Ioc] at ha
      simp only [coe_filter, Set.mem_ofPred_eq]
      exact ⟨h1 a ha.1 ha.2.1 ha.2.2, by omega, by omega⟩
    · intro x _ y _ hxy
      simpa using hxy
  omega

/-- Lemma 11.6. -/
@[kb "nivenzuckermanmontgomery" "Lemma 11.6, p. 478"]
theorem lemma_11_6 {θ : ℝ} {g : ℕ} {A B : Finset ℕ} {a₀ : ℕ} (hθ : θ ≤ 1) (hBA : B ⊆ A)
    (hmin : ∀ a ∈ A, a < a₀ → ∀ b ∈ B, a + b ∈ A) (h : MannCond θ g A B) {y : ℕ} (hy : y ≤ g)
    (hlt : (cnt A y : ℝ) < θ * y) : a₀ ≤ y := by
  classical
  have hex : ∃ z, (cnt A z : ℝ) < θ * z := ⟨y, hlt⟩
  obtain ⟨z, hz, hzy, hzmin⟩ : ∃ z, (cnt A z : ℝ) < θ * z ∧ z ≤ y ∧
      ∀ k < z, θ * k ≤ cnt A k :=
    ⟨Nat.find hex, Nat.find_spec hex, Nat.find_min' hex hlt,
      fun k hk => not_lt.1 (Nat.find_min hex hk)⟩
  by_contra hna
  have hza0 : z < a₀ := by omega
  have hz0 : 0 < z := by
    rcases Nat.eq_zero_or_pos z with h0 | h0
    · rw [h0] at hz; simp [cnt_zero] at hz
    · exact h0
  have hBz : 0 < cnt B z := by
    have := h.le (hzy.trans hy : z ≤ g)
    have h2 : (0 : ℝ) < cnt B z := by linarith
    exact_mod_cast h2
  obtain ⟨b, hbB, hb0, hbz⟩ := exists_of_cnt_pos hBz
  obtain ⟨_, h5⟩ := lemma_11_5 (A := A) hmin hbB hbz (by omega)
  have h6 := cnt_of_mem (hBA hbB) hb0
  have h7 := chain hθ (b := b) (z := z) hb0 hbz
    (P := cnt A (b - 1)) (Q := cnt A (z - b))
    (hzmin _ (by omega)) (hzmin _ (by omega))
  have h8 : (cnt A b + cnt A (z - b) : ℕ) ≤ cnt A z := h5
  have h9 : (cnt A (b - 1) + 1 + cnt A (z - b) : ℕ) ≤ cnt A z := by omega
  have h10 : ((cnt A (b - 1) : ℕ) : ℝ) + 1 + cnt A (z - b) ≤ cnt A z := by exact_mod_cast h9
  linarith

/-- The set `B' = {b ∈ B : a₀ + b ∉ A}` of the book. -/
def bPrime (A B : Finset ℕ) (a₀ : ℕ) : Finset ℕ := B.filter fun b => a₀ + b ∉ A

/-- The set `A' = {a₀ + b : b ∈ B', a₀ + b ≤ g}` of the book. -/
def aPrime (g : ℕ) (A B : Finset ℕ) (a₀ : ℕ) : Finset ℕ :=
  ((bPrime A B a₀).image (a₀ + ·)).filter (· ≤ g)

/-- Lemma 11.7: `A₂ = A ∪ A'`, `B₂ = B \ B'` satisfy `C₂ ⊆ C` and `B₂(g) < B(g)`. -/
@[kb "nivenzuckermanmontgomery" "Lemma 11.7, p. 479"]
theorem lemma_11_7 {g : ℕ} {A B : Finset ℕ} {a₀ : ℕ} (ha0 : a₀ ∈ A)
    (hBg : ∀ b ∈ B, b ≤ g) (hex : ∃ b ∈ B, a₀ + b ∉ A) :
    (A ∪ aPrime g A B a₀) + (B \ bPrime A B a₀) ⊆ A + B ∧
      cnt (B \ bPrime A B a₀) g < cnt B g := by
  constructor
  · intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.1 hx
    obtain ⟨hbB, hbn⟩ := mem_sdiff.1 hb
    have hbA : a₀ + b ∈ A := by
      by_contra hh
      exact hbn (mem_filter.2 ⟨hbB, hh⟩)
    rcases mem_union.1 ha with ha | ha
    · exact mem_add.2 ⟨a, ha, b, hbB, rfl⟩
    · obtain ⟨hai, -⟩ := mem_filter.1 ha
      obtain ⟨b1, hb1, rfl⟩ := mem_image.1 hai
      exact mem_add.2 ⟨a₀ + b, hbA, b1, (mem_filter.1 hb1).1, by ring⟩
  · obtain ⟨b, hbB, hbA⟩ := hex
    have hb0 : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; exact hbA (by simpa using ha0))
    apply card_lt_card
    rw [ssubset_iff_of_subset (inter_subset_inter_right sdiff_subset)]
    exact ⟨b, mem_inter.2 ⟨hbB, mem_Ioc.2 ⟨hb0, hBg b hbB⟩⟩, fun hh =>
      (mem_sdiff.1 (mem_inter.1 hh).1).2 (mem_filter.2 ⟨hbB, hbA⟩)⟩

/-- Lemma 11.4: if `B ⊄ A`, shifting `B \ A` into `A` gives `A₂ = A ∪ B`, `B₂ = A ∩ B`. -/
@[kb "nivenzuckermanmontgomery" "Lemma 11.4, p. 478"]
theorem lemma_11_4 {θ : ℝ} {g : ℕ} {A B : Finset ℕ} (hA0 : 0 ∈ A) (hB0 : 0 ∈ B)
    (hAg : ∀ a ∈ A, a ≤ g) (hBg : ∀ b ∈ B, b ≤ g) (hBA : ¬ B ⊆ A) (h : MannCond θ g A B) :
    ∃ A₂ B₂ : Finset ℕ, 0 ∈ A₂ ∧ 0 ∈ B₂ ∧ (∀ a ∈ A₂, a ≤ g) ∧ (∀ b ∈ B₂, b ≤ g) ∧
      A₂ + B₂ ⊆ A + B ∧ cnt B₂ g < cnt B g ∧ MannCond θ g A₂ B₂ := by
  refine ⟨A ∪ B, A ∩ B, mem_union_left _ hA0, mem_inter.2 ⟨hA0, hB0⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rcases mem_union.1 ha with ha | ha
    · exact hAg a ha
    · exact hBg a ha
  · intro b hb
    exact hBg b (mem_inter.1 hb).2
  · intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.1 hx
    rcases mem_union.1 ha with ha | ha
    · exact mem_add.2 ⟨a, ha, b, (mem_inter.1 hb).2, rfl⟩
    · exact mem_add.2 ⟨b, (mem_inter.1 hb).1, a, ha, add_comm _ _⟩
  · obtain ⟨b, hbB, hbA⟩ := not_subset.1 hBA
    have hb0 : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; exact hbA hA0)
    apply card_lt_card
    rw [ssubset_iff_of_subset (inter_subset_inter_right inter_subset_right)]
    exact ⟨b, mem_inter.2 ⟨hbB, mem_Ioc.2 ⟨hb0, hBg b hbB⟩⟩, fun hh =>
      hbA (mem_inter.1 (mem_inter.1 hh).1).1⟩
  · intro m hm1 hmg
    have e : (cnt (A ∪ B) m : ℝ) + cnt (A ∩ B) m = cnt A m + cnt B m := by
      exact_mod_cast cnt_union_add_cnt_inter A B m
    have := h m hm1 hmg
    linarith

/-- Lemma 11.8: the sets `A₂`, `B₂` of Lemma 11.7 again satisfy (11.4). -/
@[kb "nivenzuckermanmontgomery" "Lemma 11.8, p. 479"]
theorem lemma_11_8 {θ : ℝ} {g : ℕ} {A B : Finset ℕ} {a₀ : ℕ} (hθ : θ ≤ 1) (hBA : B ⊆ A)
    (ha0 : a₀ ∈ A) (ha1 : 1 ≤ a₀) (hmin : ∀ a ∈ A, a < a₀ → ∀ b ∈ B, a + b ∈ A)
    (h : MannCond θ g A B) :
    MannCond θ g (A ∪ aPrime g A B a₀) (B \ bPrime A B a₀) := by
  classical
  intro m hm1 hmg
  set B' := bPrime A B a₀ with hB'
  set A' := aPrime g A B a₀ with hA'
  have hB'B : B' ⊆ B := filter_subset _ _
  have hB'0 : ∀ b ∈ B', 0 < b ∧ a₀ + b ∉ A := by
    intro b hb
    obtain ⟨hbB, hbn⟩ := mem_filter.1 hb
    exact ⟨Nat.pos_of_ne_zero (by rintro rfl; exact hbn (by simpa using ha0)), hbn⟩
  -- (1)
  have e1 : cnt (A ∪ A') m = cnt A m + cnt A' m := by
    have := cnt_union_add_cnt_inter A A' m
    have hd : A ∩ A' = ∅ := by
      ext x
      simp only [mem_inter, notMem_empty, iff_false, not_and]
      intro hxA hxA'
      obtain ⟨hai, -⟩ := mem_filter.1 hxA'
      obtain ⟨b1, hb1, rfl⟩ := mem_image.1 hai
      exact (hB'0 b1 hb1).2 hxA
    rw [hd, cnt_empty] at this
    omega
  -- (2)
  have e2 : cnt (B \ B') m + cnt B' m = cnt B m := by
    have := cnt_union_add_cnt_inter (B \ B') B' m
    rw [sdiff_union_of_subset hB'B, sdiff_inter_self, cnt_empty] at this
    omega
  -- (3)
  have e3 : cnt A' m = #(B'.filter fun b => a₀ + b ≤ m) := by
    unfold cnt
    have : A' ∩ Ioc 0 m = (B'.filter fun b => a₀ + b ≤ m).image (a₀ + ·) := by
      ext x
      simp only [mem_inter, mem_Ioc, mem_filter, mem_image, hA', aPrime]
      constructor
      · rintro ⟨⟨⟨b, hb, rfl⟩, _⟩, _, hxm⟩
        exact ⟨b, ⟨hb, hxm⟩, rfl⟩
      · rintro ⟨b, ⟨hb, hbm⟩, rfl⟩
        exact ⟨⟨⟨b, hb, rfl⟩, by omega⟩, by omega, hbm⟩
    rw [this, card_image_of_injective _ (add_right_injective a₀)]
  have e4 : cnt B' m = #(B'.filter fun b => a₀ + b ≤ m) +
      #(B'.filter fun b => m < a₀ + b ∧ b ≤ m) := by
    have h1 : cnt B' m = #(B'.filter fun b => b ≤ m) := by
      unfold cnt
      congr 1
      ext x
      simp only [mem_inter, mem_Ioc, mem_filter]
      constructor
      · rintro ⟨hx, _, h2⟩; exact ⟨hx, h2⟩
      · rintro ⟨hx, h2⟩; exact ⟨hx, (hB'0 x hx).1, h2⟩
    rw [h1, ← card_filter_add_card_filter_not (s := B'.filter fun b => b ≤ m)
      (fun b => a₀ + b ≤ m)]
    congr 1
    · congr 1; ext x
      simp only [mem_filter]
      constructor
      · rintro ⟨⟨hx, _⟩, h2⟩; exact ⟨hx, h2⟩
      · rintro ⟨hx, h2⟩; exact ⟨⟨hx, by omega⟩, h2⟩
    · congr 1; ext x
      simp only [mem_filter]
      constructor
      · rintro ⟨⟨hx, h1⟩, h2⟩; exact ⟨hx, by omega, h1⟩
      · rintro ⟨hx, h2, h1⟩; exact ⟨⟨hx, h1⟩, by omega⟩
  set D := #(B'.filter fun b => m < a₀ + b ∧ b ≤ m) with hD
  have key : cnt (A ∪ A') m + cnt (B \ B') m + D = cnt A m + cnt B m := by omega
  have hmc := h m hm1 hmg
  by_cases hD0 : D = 0
  · have : (cnt (A ∪ A') m : ℝ) + cnt (B \ B') m = cnt A m + cnt B m := by
      have : cnt (A ∪ A') m + cnt (B \ B') m = cnt A m + cnt B m := by omega
      exact_mod_cast this
    linarith
  · -- the main case
    have hDpos : 0 < D := Nat.pos_of_ne_zero hD0
    obtain ⟨b1, hb1⟩ := card_pos.1 hDpos
    obtain ⟨hb1B', hb1m, hb1le⟩ := mem_filter.1 hb1
    set T := B.filter fun b => 0 < b ∧ m < a₀ + b ∧ b ≤ m with hT
    have hTne : T.Nonempty :=
      ⟨b1, mem_filter.2 ⟨hB'B hb1B', (hB'0 b1 hb1B').1, hb1m, hb1le⟩⟩
    set b₀ := T.min' hTne with hb₀
    have hb₀T : b₀ ∈ T := min'_mem _ _
    obtain ⟨hb₀B, hb₀pos, hb₀m, hb₀le⟩ := mem_filter.1 hb₀T
    have hb₀min : ∀ b ∈ B, 0 < b → m < a₀ + b → b ≤ m → b₀ ≤ b :=
      fun b hb h1 h2 h3 => min'_le _ _ (mem_filter.2 ⟨hb, h1, h2, h3⟩)
    -- D + B(b₀ - 1) ≤ B(m)
    have hDB : D + cnt B (b₀ - 1) ≤ cnt B m := by
      rw [cnt_split B (show b₀ - 1 ≤ m by omega)]
      have : D ≤ #(B.filter fun a => b₀ - 1 < a ∧ a ≤ m) := by
        apply card_le_card
        intro x hx
        obtain ⟨hxB', hx1, hx2⟩ := mem_filter.1 hx
        have := hb₀min x (hB'B hxB') (hB'0 x hxB').1 hx1 hx2
        exact mem_filter.2 ⟨hB'B hxB', by omega, hx2⟩
      omega
    obtain ⟨-, h5⟩ := lemma_11_5 (A := A) hmin hb₀B hb₀le (by omega)
    have h6 := cnt_of_mem (hBA hb₀B) hb₀pos
    have hQ : θ * ((m - b₀ : ℕ) : ℝ) ≤ cnt A (m - b₀) := by
      by_contra hh
      have := lemma_11_6 hθ hBA hmin h (y := m - b₀) (by omega) (not_le.1 hh)
      omega
    have hP := h.le (show b₀ - 1 ≤ g by omega)
    have h7 := chain hθ (b := b₀) (z := m) hb₀pos hb₀le
      (P := (cnt A (b₀ - 1) : ℝ) + cnt B (b₀ - 1)) (Q := cnt A (m - b₀)) hP hQ
    have hnat : cnt A (b₀ - 1) + cnt B (b₀ - 1) + 1 + cnt A (m - b₀) ≤
        cnt (A ∪ A') m + cnt (B \ B') m := by omega
    have hreal : ((cnt A (b₀ - 1) : ℝ) + cnt B (b₀ - 1) + 1 + cnt A (m - b₀)) ≤
        cnt (A ∪ A') m + cnt (B \ B') m := by exact_mod_cast hnat
    linarith

/-- Strong induction on `B(g)` behind Theorem 11.9. -/
private theorem mann_aux {θ : ℝ} {g : ℕ} (hθ : θ ≤ 1) (k : ℕ) :
    ∀ A B : Finset ℕ, cnt B g = k → 0 ∈ A → 0 ∈ B → (∀ a ∈ A, a ≤ g) → (∀ b ∈ B, b ≤ g) →
      MannCond θ g A B → θ * g ≤ cnt (A + B) g := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro A B hk hA0 hB0 hAg hBg h
  by_cases hBA : B ⊆ A
  · rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · have hsub : A ⊆ A + B := fun a ha => mem_add.2 ⟨a, ha, 0, hB0, add_zero a⟩
      have h1 := h.le (le_refl g)
      have h2 : (cnt B g : ℝ) = 0 := by exact_mod_cast hk
      have h3 : (cnt A g : ℝ) ≤ cnt (A + B) g := by exact_mod_cast cnt_mono_set hsub g
      linarith
    · have hBpos : 0 < cnt B g := hk ▸ hkpos
      obtain ⟨b, hbB, hb0, -⟩ := exists_of_cnt_pos hBpos
      obtain ⟨a₀, ha0, ha1, hex, hmin⟩ := exists_a₀ hA0 hBA ⟨b, hbB, hb0⟩
      obtain ⟨hsub, hlt⟩ := lemma_11_7 (g := g) ha0 hBg hex
      have hcond := lemma_11_8 hθ hBA ha0 ha1 hmin h
      have hB0' : 0 ∈ B \ bPrime A B a₀ :=
        mem_sdiff.2 ⟨hB0, fun hh => (mem_filter.1 hh).2 (by simpa using ha0)⟩
      have hAg' : ∀ a ∈ A ∪ aPrime g A B a₀, a ≤ g := by
        intro a ha
        rcases mem_union.1 ha with ha | ha
        · exact hAg a ha
        · exact (mem_filter.1 ha).2
      have hBg' : ∀ b ∈ B \ bPrime A B a₀, b ≤ g := fun b hb => hBg b (mem_sdiff.1 hb).1
      have := ih _ (hk ▸ hlt) (A ∪ aPrime g A B a₀) (B \ bPrime A B a₀) rfl
        (mem_union_left _ hA0) hB0' hAg' hBg' hcond
      exact this.trans (by exact_mod_cast cnt_mono_set hsub g)
  · obtain ⟨A₂, B₂, hA2, hB2, hA2g, hB2g, hsub, hlt, hcond⟩ :=
      lemma_11_4 hA0 hB0 hAg hBg hBA h
    have := ih _ (hk ▸ hlt) A₂ B₂ rfl hA2 hB2 hA2g hB2g hcond
    exact this.trans (by exact_mod_cast cnt_mono_set hsub g)

/-- Theorem 11.9 (finite form of Mann's theorem).  `A`, `B` are finite sets of naturals `≤ g`
containing `0`, `C = A + B`; if `A(m) + B(m) ≥ θ m` for `1 ≤ m ≤ g` (with `θ ≤ 1`), then
`C(g) ≥ θ g`. -/
@[kb "nivenzuckermanmontgomery" "Thm 11.9, p. 480"]
theorem theorem_11_9 {θ : ℝ} {g : ℕ} (hθ : θ ≤ 1) {A B : Finset ℕ} (hA0 : 0 ∈ A) (hB0 : 0 ∈ B)
    (hAg : ∀ a ∈ A, a ≤ g) (hBg : ∀ b ∈ B, b ≤ g)
    (h : ∀ m : ℕ, 1 ≤ m → m ≤ g → θ * m ≤ cnt A m + cnt B m) :
    θ * g ≤ cnt (A + B) g :=
  mann_aux hθ _ A B rfl hA0 hB0 hAg hBg h

/-- Theorem 11.10 (Mann's `α + β` theorem): for sets `A`, `B` of naturals containing `0`,
`min 1 (d A + d B) ≤ d (A + B)` where `d` is the Schnirelmann density. -/
@[kb "nivenzuckermanmontgomery" "Thm 11.10, p. 480"]
theorem theorem_11_10 (A B : Set ℕ) [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    [DecidablePred (· ∈ A + B)] (hA : 0 ∈ A) (hB : 0 ∈ B) :
    min 1 (schnirelmannDensity A + schnirelmannDensity B) ≤ schnirelmannDensity (A + B) := by
  rw [le_schnirelmannDensity_iff]
  intro n hn
  set θ := min 1 (schnirelmannDensity A + schnirelmannDensity B) with hθ
  have hθ1 : θ ≤ 1 := min_le_left _ _
  have hθ2 : θ ≤ schnirelmannDensity A + schnirelmannDensity B := min_le_right _ _
  set Ag : Finset ℕ := (range (n + 1)).filter (· ∈ A) with hAg
  set Bg : Finset ℕ := (range (n + 1)).filter (· ∈ B) with hBg
  have hcnt : ∀ (S : Set ℕ) [DecidablePred (· ∈ S)] (m : ℕ), m ≤ n →
      cnt ((range (n + 1)).filter (· ∈ S)) m = #{a ∈ Ioc 0 m | a ∈ S} := by
    intro S _ m hm
    unfold cnt
    congr 1
    ext x
    simp only [mem_inter, mem_filter, mem_range, mem_Ioc]
    constructor
    · rintro ⟨⟨_, hxS⟩, h1, h2⟩; exact ⟨⟨h1, h2⟩, hxS⟩
    · rintro ⟨⟨h1, h2⟩, hxS⟩; exact ⟨⟨by omega, hxS⟩, h1, h2⟩
  have hmain := theorem_11_9 (θ := θ) (g := n) hθ1 (A := Ag) (B := Bg)
    (by simp [hAg, hA]) (by simp [hBg, hB])
    (fun a ha => Nat.lt_succ_iff.1 (mem_range.1 (mem_filter.1 ha).1))
    (fun a ha => Nat.lt_succ_iff.1 (mem_range.1 (mem_filter.1 ha).1))
    (by
      intro m _ hmn
      rw [hAg, hBg, hcnt A m hmn, hcnt B m hmn]
      have h1 := schnirelmannDensity_mul_le_card_filter (A := A) (n := m)
      have h2 := schnirelmannDensity_mul_le_card_filter (A := B) (n := m)
      have h3 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith)
  have hle : cnt (Ag + Bg) n ≤ #{a ∈ Ioc 0 n | a ∈ A + B} := by
    unfold cnt
    apply card_le_card
    intro x hx
    obtain ⟨hxs, hxI⟩ := mem_inter.1 hx
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.1 hxs
    exact mem_filter.2 ⟨hxI, Set.add_mem_add (mem_filter.1 ha).2 (mem_filter.1 hb).2⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [le_div_iff₀ hnpos]
  have : (cnt (Ag + Bg) n : ℝ) ≤ #{a ∈ Ioc 0 n | a ∈ A + B} := by exact_mod_cast hle
  linarith

end NTKB.NZM
