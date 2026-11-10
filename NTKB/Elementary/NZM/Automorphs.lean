/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.NZM.ReducedForms

/-!
# Small values and automorphs of reduced forms (Niven–Zuckerman–Montgomery, § 3.7)

* **Lemma 3.24.** If `f = (a, b, c)` is a reduced positive definite form, `gcd(x, y) = 1` and
  `f(x, y) ≤ c`, then `f(x, y) ∈ {a, c}` and `(x, y)` is one of `±(1, 0)`, `±(0, 1)`, `±(1, -1)`;
  the number of proper representations of `a` is `2` if `a < c`, `4` if `0 ≤ b < a = c`, `6` if
  `a = b = c`.
* **Theorem 3.26** (values). For a reduced positive definite form, `w(f) = 4` if `a = c` and `b = 0`,
  `w(f) = 6` if `a = b = c`, and `w(f) = 2` otherwise; hence `w(f) ∈ {2, 4, 6}` for every positive
  definite form. (The counting part of Theorem 3.26 is `automorphs_equiv_formMaps`.)

The proof is the book's: the columns of an automorph are proper representations of `a` and of `c`,
so they lie among the six points of Lemma 3.24, and the `36` candidate matrices are checked.
-/

namespace NTKB.NZM

open NTKB.Davenport

/-- The six points `±(1, 0)`, `±(0, 1)`, `±(1, -1)` of Lemma 3.24. -/
def sixPoints : Finset (ℤ × ℤ) := {(1, 0), (-1, 0), (0, 1), (0, -1), (1, -1), (-1, 1)}

/-- For a reduced positive definite form: `a > 0`, `c > 0`, `-a < b ≤ a ≤ c`, and `b ≥ 0` when
`a = c`. -/
lemma IsReducedForm.posDef_bounds {f : ℤ × ℤ × ℤ} (hf : IsReducedForm f) (hp : IsPosDef f) :
    0 < f.1 ∧ 0 < f.2.2 ∧ -f.1 < f.2.1 ∧ f.2.1 ≤ f.1 ∧ f.1 ≤ f.2.2 ∧ (f.1 = f.2.2 → 0 ≤ f.2.1) := by
  have ha : 0 < f.1 := by simpa [formEval] using hp 1 0 (by simp)
  have hc : 0 < f.2.2 := by simpa [formEval] using hp 0 1 (by simp)
  refine ⟨ha, hc, ?_⟩
  rcases hf with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
    simp only [abs_of_pos ha, abs_of_pos hc] at h1 h2 h3
  · exact ⟨h1, h2, h3.le, fun h ↦ absurd h h3.ne⟩
  · exact ⟨by linarith, h2, h3.le, fun _ ↦ h1⟩

/-- **Lemma 3.24** (the six points). If `f = (a, b, c)` is a reduced positive definite form, `x, y`
are coprime and `f(x, y) ≤ c`, then `(x, y)` is one of `±(1, 0)`, `±(0, 1)`, `±(1, -1)`. -/
theorem IsReducedForm.mem_sixPoints {f : ℤ × ℤ × ℤ} (hf : IsReducedForm f) (hp : IsPosDef f)
    {x y : ℤ} (hxy : IsCoprime x y) (hle : formEval f x y ≤ f.2.2) : (x, y) ∈ sixPoints := by
  obtain ⟨ha, hc, hb1, hb2, hac, -⟩ := hf.posDef_bounds hp
  obtain ⟨a, b, c⟩ := f
  simp only at ha hc hb1 hb2 hac hle
  simp only [formEval] at hle
  have key : 4 * a * (a * x ^ 2 + b * x * y + c * y ^ 2) =
      (2 * a * x + b * y) ^ 2 + (4 * a * c - b ^ 2) * y ^ 2 := by ring
  have hd : 3 * a * c ≤ 4 * a * c - b ^ 2 := by nlinarith
  have hle4 : 4 * a * (a * x ^ 2 + b * x * y + c * y ^ 2) ≤ 4 * a * c := by nlinarith
  by_cases hy0 : y = 0
  · subst hy0
    rcases Int.isUnit_iff.mp (isCoprime_zero_right.mp hxy) with rfl | rfl <;>
      simp only [sixPoints, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] <;> norm_num
  -- `|y| = 1`
  have hy1 : y = 1 ∨ y = -1 := by
    by_contra hne
    have hy : 2 ≤ y ∨ y ≤ -2 := by omega
    have hy2 : 4 ≤ y ^ 2 := by rcases hy with h | h <;> nlinarith
    have : 4 * (3 * a * c) ≤ (4 * a * c - b ^ 2) * y ^ 2 := by nlinarith
    nlinarith [sq_nonneg (2 * a * x + b * y)]
  -- `|x| ≤ 1`
  have hx1 : -1 ≤ x ∧ x ≤ 1 := by
    by_contra hne
    have hx : 2 ≤ x ∨ x ≤ -2 := by omega
    have h3 : 3 * a ≤ |2 * a * x + b * y| := by
      rcases hy1 with rfl | rfl <;> rcases hx with hx | hx
      · rw [abs_of_nonneg (by nlinarith)]; nlinarith
      · rw [abs_of_nonpos (by nlinarith)]; nlinarith
      · rw [abs_of_nonneg (by nlinarith)]; nlinarith
      · rw [abs_of_nonpos (by nlinarith)]; nlinarith
    have h9 : 9 * a ^ 2 ≤ (2 * a * x + b * y) ^ 2 := by
      rw [← sq_abs (2 * a * x + b * y)]; nlinarith [abs_nonneg (2 * a * x + b * y)]
    have hy2 : y ^ 2 = 1 := by rcases hy1 with rfl | rfl <;> norm_num
    rw [hy2] at key
    nlinarith
  have hx : x = -1 ∨ x = 0 ∨ x = 1 := by omega
  rcases hy1 with rfl | rfl <;> rcases hx with rfl | rfl | rfl <;> simp [sixPoints] <;> nlinarith

/-- **Lemma 3.24** (the values). Under the hypotheses of `IsReducedForm.mem_sixPoints`,
`f(x, y) = a` or `f(x, y) = c`. -/
theorem IsReducedForm.formEval_eq_of_le {f : ℤ × ℤ × ℤ} (hf : IsReducedForm f) (hp : IsPosDef f)
    {x y : ℤ} (hxy : IsCoprime x y) (hle : formEval f x y ≤ f.2.2) :
    formEval f x y = f.1 ∨ formEval f x y = f.2.2 := by
  have h6 := hf.mem_sixPoints hp hxy hle
  obtain ⟨ha, hc, hb1, hb2, hac, -⟩ := hf.posDef_bounds hp
  obtain ⟨a, b, c⟩ := f
  simp only [sixPoints, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h6
  simp only [formEval] at hle ⊢
  rcases h6 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    first | (left; ring1) | (right; ring1) | (right; linarith)

/-- The proper representations of `n` by `f`: coprime `(x, y)` with `f(x, y) = n`. -/
def properReps (f : ℤ × ℤ × ℤ) (n : ℤ) : Set (ℤ × ℤ) := {p | IsCoprime p.1 p.2 ∧ formEval f p.1 p.2 = n}

/-- All representations of `n` by `f`. -/
def reps (f : ℤ × ℤ × ℤ) (n : ℤ) : Set (ℤ × ℤ) := {p | formEval f p.1 p.2 = n}

/-- **Lemma 3.24** (the number of proper representations of `a`). For a reduced positive definite form
`(a, b, c)`, the proper representations of `a` are `±(1, 0)` if `a < c`; `±(1, 0), ±(0, 1)` if
`0 ≤ b < a = c`; and `±(1, 0), ±(0, 1), ±(1, -1)` if `a = b = c`. In particular their number is
`2`, `4` or `6`. -/
@[kb "nivenzuckermanmontgomery" "Lem 3.24, p. 170"]
theorem IsReducedForm.properReps_fst {f : ℤ × ℤ × ℤ} (hf : IsReducedForm f) (hp : IsPosDef f) :
    (f.1 < f.2.2 → properReps f f.1 = ↑({(1, 0), (-1, 0)} : Finset (ℤ × ℤ))) ∧
    (f.1 = f.2.2 → f.2.1 < f.1 →
      properReps f f.1 = ↑({(1, 0), (-1, 0), (0, 1), (0, -1)} : Finset (ℤ × ℤ))) ∧
    (f.1 = f.2.2 → f.2.1 = f.1 → properReps f f.1 = ↑sixPoints) := by
  obtain ⟨ha, hc, hb1, hb2, hac, hb0⟩ := hf.posDef_bounds hp
  have mem : ∀ x y : ℤ, (x, y) ∈ properReps f f.1 ↔ (x, y) ∈ sixPoints ∧ formEval f x y = f.1 := by
    intro x y
    constructor
    · rintro ⟨hco, hv⟩
      exact ⟨hf.mem_sixPoints hp hco (by rw [hv]; exact hac), hv⟩
    · rintro ⟨h6, hv⟩
      refine ⟨?_, hv⟩
      simp only [sixPoints, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h6
      rcases h6 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact isCoprime_one_left
      · exact ⟨-1, 0, by norm_num⟩
      · exact isCoprime_one_right
      · exact ⟨0, -1, by norm_num⟩
      · exact isCoprime_one_left
      · exact ⟨-1, 0, by norm_num⟩
  obtain ⟨a, b, c⟩ := f
  simp only at ha hc hb1 hb2 hac hb0 mem ⊢
  refine ⟨fun h ↦ ?_, fun h h' ↦ ?_, fun h h' ↦ ?_⟩ <;> ext ⟨x, y⟩ <;> rw [mem] <;>
    simp only [sixPoints, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, formEval] <;>
    constructor
  · rintro ⟨h6 | h6 | h6 | h6 | h6 | h6, hv⟩ <;> obtain ⟨rfl, rfl⟩ := h6 <;> norm_num at hv ⊢ <;>
      linarith
  · rintro (h6 | h6) <;> obtain ⟨rfl, rfl⟩ := h6 <;> norm_num
  · rintro ⟨h6 | h6 | h6 | h6 | h6 | h6, hv⟩ <;> obtain ⟨rfl, rfl⟩ := h6 <;> norm_num at hv ⊢ <;>
      linarith
  · rintro (h6 | h6 | h6 | h6) <;> obtain ⟨rfl, rfl⟩ := h6 <;> norm_num <;> linarith
  · rintro ⟨h6, hv⟩; exact h6
  · intro h6; refine ⟨h6, ?_⟩
    rcases h6 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      norm_num <;> linarith

/-! ### Theorem 3.26: the automorphs of a reduced form -/

/-- The columns of an automorph of a reduced positive definite form lie among the six points. -/
lemma IsReducedForm.automorph_cols {f : ℤ × ℤ × ℤ} (hf : IsReducedForm f) (hp : IsPosDef f)
    {M : ℤ × ℤ × ℤ × ℤ} (hM : M ∈ automorphs f) :
    (M.1, M.2.2.1) ∈ sixPoints ∧ (M.2.1, M.2.2.2) ∈ sixPoints := by
  obtain ⟨hdet, hfix⟩ := hM
  obtain ⟨ha, hc, -, -, hac, -⟩ := hf.posDef_bounds hp
  obtain ⟨α, β, γ, δ⟩ := M
  simp only at hdet hfix ⊢
  have e1 : formEval f α γ = f.1 := by
    rw [← formSubst_fst, hfix]
  have e2 : formEval f β δ = f.2.2 := by
    have : (formSubst f α β γ δ).2.2 = formEval f β δ := by simp only [formSubst, formEval]
    rw [← this, hfix]
  refine ⟨hf.mem_sixPoints hp ⟨δ, -β, by linear_combination hdet⟩ (by rw [e1]; exact hac),
    hf.mem_sixPoints hp ⟨-γ, α, by linear_combination hdet⟩ (by rw [e2])⟩

/-- **Theorem 3.26** (the automorphs of a reduced form, listed). For a reduced positive definite form
`f = (a, b, c)`: if `a = c` and `b = 0` the automorphs are `±I`, `±[[0, -1], [1, 0]]`; if `a = b = c`
they are `±I`, `±[[0, -1], [1, 1]]`, `±[[1, 1], [-1, 0]]`; otherwise they are `±I`. Matrices are
written `(m₁₁, m₁₂, m₂₁, m₂₂)`. -/
@[kb "nivenzuckermanmontgomery" "Thm 3.26, p. 173"]
theorem IsReducedForm.automorphs_eq {f : ℤ × ℤ × ℤ} (hf : IsReducedForm f) (hp : IsPosDef f) :
    (f.1 = f.2.2 → f.2.1 = 0 →
      automorphs f = ↑({(1, 0, 0, 1), (-1, 0, 0, -1), (0, -1, 1, 0), (0, 1, -1, 0)} :
        Finset (ℤ × ℤ × ℤ × ℤ))) ∧
    (f.1 = f.2.2 → f.2.1 = f.1 →
      automorphs f = ↑({(1, 0, 0, 1), (-1, 0, 0, -1), (0, -1, 1, 1), (0, 1, -1, -1), (1, 1, -1, 0),
        (-1, -1, 1, 0)} : Finset (ℤ × ℤ × ℤ × ℤ))) ∧
    (¬(f.1 = f.2.2 ∧ f.2.1 = 0) → ¬(f.1 = f.2.2 ∧ f.2.1 = f.1) →
      automorphs f = ↑({(1, 0, 0, 1), (-1, 0, 0, -1)} : Finset (ℤ × ℤ × ℤ × ℤ))) := by
  have cols := fun M (hM : M ∈ automorphs f) ↦ hf.automorph_cols hp hM
  obtain ⟨ha, hc, hb1, hb2, hac, hb0⟩ := hf.posDef_bounds hp
  obtain ⟨a, b, c⟩ := f
  simp only at ha hc hb1 hb2 hac hb0 cols ⊢
  -- membership in `automorphs` for an explicit matrix
  have memA : ∀ α β γ δ : ℤ, (α, β, γ, δ) ∈ automorphs (a, b, c) ↔
      α * δ - β * γ = 1 ∧ a * α ^ 2 + b * α * γ + c * γ ^ 2 = a ∧
        2 * a * α * β + b * (α * δ + β * γ) + 2 * c * γ * δ = b ∧
        a * β ^ 2 + b * β * δ + c * δ ^ 2 = c := by
    intro α β γ δ
    simp only [automorphs, formMaps, Set.mem_ofPred_eq, formSubst, Prod.mk.injEq]
  -- the inclusion `automorphs ⊆` candidates, uniformly: 36 cases
  have key : ∀ M ∈ automorphs (a, b, c), M ∈ ({(1, 0, 0, 1), (-1, 0, 0, -1), (0, -1, 1, 0),
      (0, 1, -1, 0), (0, -1, 1, 1), (0, 1, -1, -1), (1, 1, -1, 0), (-1, -1, 1, 0)} :
        Finset (ℤ × ℤ × ℤ × ℤ)) ∧
      ((M = (0, -1, 1, 0) ∨ M = (0, 1, -1, 0)) → a = c ∧ b = 0) ∧
      ((M = (0, -1, 1, 1) ∨ M = (0, 1, -1, -1) ∨ M = (1, 1, -1, 0) ∨ M = (-1, -1, 1, 0)) →
        a = c ∧ b = a) := by
    rintro ⟨α, β, γ, δ⟩ hM
    obtain ⟨c1, c2⟩ := cols _ hM
    rw [memA] at hM
    obtain ⟨hdet, e1, e2, e3⟩ := hM
    simp only [sixPoints, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at c1 c2
    rcases c1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases c2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    revert hdet e1 e2 e3 <;> norm_num <;> intros <;> first | omega | (constructor <;> omega) | skip
  refine ⟨fun h1 h2 ↦ ?_, fun h1 h2 ↦ ?_, fun h1 h2 ↦ ?_⟩ <;> ext ⟨α, β, γ, δ⟩ <;> constructor
  · intro hM
    obtain ⟨h8, hr, hs⟩ := key _ hM
    simp only [Finset.mem_insert, Finset.mem_singleton] at h8
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases h8 with h | h | h | h | h | h | h | h <;> rw [h] at hr hs ⊢ <;> simp at hr hs ⊢ <;> omega
  · intro h
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at h
    obtain ⟨rfl⟩ := h1; obtain ⟨rfl⟩ := h2
    rcases h with h | h | h | h <;> rw [h, memA] <;> exact ⟨by norm_num, by ring, by ring, by ring⟩
  · intro hM
    obtain ⟨h8, hr, hs⟩ := key _ hM
    simp only [Finset.mem_insert, Finset.mem_singleton] at h8
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases h8 with h | h | h | h | h | h | h | h <;> rw [h] at hr hs ⊢ <;> simp at hr hs ⊢ <;> omega
  · intro h
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at h
    obtain ⟨rfl⟩ := h1; subst h2
    rcases h with h | h | h | h | h | h <;> rw [h, memA] <;>
      exact ⟨by norm_num, by ring, by ring, by ring⟩
  · intro hM
    obtain ⟨h8, hr, hs⟩ := key _ hM
    simp only [Finset.mem_insert, Finset.mem_singleton] at h8
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases h8 with h | h | h | h | h | h | h | h <;> rw [h] at hr hs ⊢ <;> simp at hr hs ⊢ <;> omega
  · intro h
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h <;> rw [h, memA] <;> exact ⟨by norm_num, by ring, by ring, by ring⟩

/-! ### Theorem 3.27: `r_f(n) = w(f) H_f(n)` -/

/-- `H_f(n)` as a set: the integers `h` with `0 ≤ h < 2n`, `h² = d + 4nk`, such that the form
`nx² + hxy + ky²` is equivalent to `f` (`d` the discriminant of `f`). -/
def hSet (f : ℤ × ℤ × ℤ) (n : ℤ) : Set ℤ :=
  {h | 0 ≤ h ∧ h < 2 * n ∧ ∃ k, h ^ 2 = formDisc f + 4 * n * k ∧ FormEquiv f (n, h, k)}

/-- `H_f(n)`, the number of `h` in `hSet f n`. -/
noncomputable def hCount (f : ℤ × ℤ × ℤ) (n : ℤ) : ℕ := Nat.card (hSet f n)

/-- `r_f(n)`, the number of proper representations of `n` by `f`. -/
noncomputable def properRepCount (f : ℤ × ℤ × ℤ) (n : ℤ) : ℕ := Nat.card (properReps f n)

/-- `R_f(n)`, the number of representations of `n` by `f`. -/
noncomputable def repCount (f : ℤ × ℤ × ℤ) (n : ℤ) : ℕ := Nat.card (reps f n)

/-- A shear `[[1, t], [0, 1]]` on the right adds `2At` to the middle coefficient. -/
lemma formSubst_shear (f : ℤ × ℤ × ℤ) (α β γ δ t : ℤ) :
    formSubst f α (β + t * α) γ (δ + t * γ) =
      ((formSubst f α β γ δ).1, (formSubst f α β γ δ).2.1 + 2 * (formSubst f α β γ δ).1 * t,
        (formSubst f α β γ δ).2.2 + (formSubst f α β γ δ).2.1 * t +
          (formSubst f α β γ δ).1 * t ^ 2) := by
  obtain ⟨a, b, c⟩ := f
  simp only [formSubst, Prod.mk.injEq]
  refine ⟨trivial, by ring, by ring⟩

/-- The matrices of the modular group taking `f` to a form `(n, h, k)` with `0 ≤ h < 2n`. -/
def hMats (f : ℤ × ℤ × ℤ) (n : ℤ) : Set (ℤ × ℤ × ℤ × ℤ) :=
  {M | M.1 * M.2.2.2 - M.2.1 * M.2.2.1 = 1 ∧ (formSubst f M.1 M.2.1 M.2.2.1 M.2.2.2).1 = n ∧
    0 ≤ (formSubst f M.1 M.2.1 M.2.2.1 M.2.2.2).2.1 ∧
    (formSubst f M.1 M.2.1 M.2.2.1 M.2.2.2).2.1 < 2 * n}

/-- The first column gives a bijection from `hMats f n` onto the proper representations of `n`. -/
lemma hMats_equiv_properReps (f : ℤ × ℤ × ℤ) {n : ℤ} (hn : 0 < n) :
    Nonempty (hMats f n ≃ properReps f n) := by
  have hfst : ∀ α β γ δ, (formSubst f α β γ δ).1 = formEval f α γ := fun _ _ _ _ ↦ formSubst_fst ..
  refine ⟨Equiv.ofBijective (fun M ↦ ⟨(M.1.1, M.1.2.2.1), ?_, ?_⟩) ⟨?_, ?_⟩⟩
  · obtain ⟨⟨α, β, γ, δ⟩, hdet, -⟩ := M
    exact ⟨δ, -β, by simp only at hdet ⊢; linear_combination hdet⟩
  · obtain ⟨⟨α, β, γ, δ⟩, -, h1, -⟩ := M
    simp only at h1 ⊢; rw [← hfst α β γ δ, h1]
  · -- injective: same first column, so the second columns differ by a multiple of it
    rintro ⟨⟨α, β, γ, δ⟩, hdet, h1, h2, h3⟩ ⟨⟨α', β', γ', δ'⟩, hdet', h1', h2', h3'⟩ hEq
    simp only [Prod.mk.injEq] at hEq hdet hdet' h1 h1' h2 h2' h3 h3'
    obtain ⟨rfl, rfl⟩ := hEq
    -- `t = (β' - β) δ ... `: put `t = (β' - β) * δ - (δ' - δ) * β`
    set t := (β' - β) * δ - (δ' - δ) * β with ht
    have hβ : β' = β + t * α := by linear_combination -(β' - β) * hdet + β * (hdet' - hdet)
    have hδ : δ' = δ + t * γ := by linear_combination -(δ' - δ) * hdet + δ * (hdet' - hdet)
    have hsh := formSubst_shear f α β γ δ t
    rw [← hβ, ← hδ] at hsh
    rw [hsh] at h2' h3'
    simp only [h1] at h2' h3'
    have ht0 : t = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h <;> nlinarith
    simp only [ht0, zero_mul, add_zero] at hβ hδ
    subst hβ hδ; rfl
  · -- surjective
    rintro ⟨⟨x, y⟩, ⟨p, q, hpq⟩, hv⟩
    simp only at hpq hv
    set h0 := (formSubst f x (-q) y p).2.1
    set t := -(h0 / (2 * n))
    refine ⟨⟨(x, -q + t * x, y, p + t * y), ?_, ?_, ?_, ?_⟩, rfl⟩ <;> simp only
    · linear_combination hpq
    · rw [hfst]; exact hv
    · rw [formSubst_shear, hfst, hv]
      have e := Int.emod_def h0 (2 * n)
      have : 0 ≤ h0 % (2 * n) := Int.emod_nonneg _ (by omega)
      simp only [t]; nlinarith
    · rw [formSubst_shear, hfst, hv]
      have e := Int.emod_def h0 (2 * n)
      have : h0 % (2 * n) < 2 * n := Int.emod_lt_of_pos _ (by omega)
      simp only [t]; nlinarith

/-! ### Theorem 3.26: the values `2, 4, 6` -/

/-- A positive definite form has negative discriminant (Theorem 3.11). -/
lemma IsPosDef.formDisc_neg {f : ℤ × ℤ × ℤ} (hp : IsPosDef f) : formDisc f < 0 := by
  rcases lt_trichotomy (formDisc f) 0 with h | h | h
  · exact h
  · obtain ⟨-, x, y, hxy, h0⟩ := semidef_not_def_of_disc_eq_zero h
    exact absurd h0 (hp x y hxy).ne'
  · obtain ⟨-, x, y, hneg⟩ := isIndefinite_of_pos h
    have hxy : (x, y) ≠ (0, 0) := by
      rintro h0; simp only [Prod.mk.injEq] at h0; rw [h0.1, h0.2] at hneg; simp [formEval] at hneg
    exact absurd hneg (hp x y hxy).le.not_gt

/-- Equivalence preserves positive definiteness. -/
lemma IsPosDef.of_formEquiv {f g : ℤ × ℤ × ℤ} (hp : IsPosDef f) (h : FormEquiv f g) : IsPosDef g := by
  obtain ⟨α, β, γ, δ, hdet, rfl⟩ := h
  intro x y hxy
  rw [formEval_formSubst]
  refine hp _ _ fun h0 ↦ hxy ?_
  simp only [Prod.mk.injEq] at h0 ⊢
  constructor
  · linear_combination δ * h0.1 - β * h0.2 - x * hdet
  · linear_combination α * h0.2 - γ * h0.1 - y * hdet

/-- **Theorem 3.26** (values for reduced forms). For a reduced positive definite form `(a, b, c)`:
`w(f) = 4` if `a = c` and `b = 0`; `w(f) = 6` if `a = b = c`; `w(f) = 2` otherwise. -/
@[kb "nivenzuckermanmontgomery" "Thm 3.26, p. 173"]
theorem IsReducedForm.numAutomorphs_eq {f : ℤ × ℤ × ℤ} (hf : IsReducedForm f) (hp : IsPosDef f) :
    (f.1 = f.2.2 → f.2.1 = 0 → numAutomorphs f = 4) ∧
    (f.1 = f.2.2 → f.2.1 = f.1 → numAutomorphs f = 6) ∧
    (¬(f.1 = f.2.2 ∧ f.2.1 = 0) → ¬(f.1 = f.2.2 ∧ f.2.1 = f.1) → numAutomorphs f = 2) := by
  obtain ⟨h4, h6, h2⟩ := hf.automorphs_eq hp
  refine ⟨fun h h' ↦ ?_, fun h h' ↦ ?_, fun h h' ↦ ?_⟩ <;> unfold numAutomorphs
  · rw [h4 h h', Nat.card_coe_set_eq, Set.ncard_coe_finset]; decide
  · rw [h6 h h', Nat.card_coe_set_eq, Set.ncard_coe_finset]; decide
  · rw [h2 h h', Nat.card_coe_set_eq, Set.ncard_coe_finset]; decide

/-- **Theorem 3.26** (values). A positive definite form has `2`, `4` or `6` automorphs. -/
@[kb "nivenzuckermanmontgomery" "Thm 3.26, p. 173"]
theorem numAutomorphs_mem {f : ℤ × ℤ × ℤ} (hp : IsPosDef f) :
    numAutomorphs f = 2 ∨ numAutomorphs f = 4 ∨ numAutomorphs f = 6 := by
  have hns : ¬IsSquare (formDisc f) := by
    rintro ⟨r, hr⟩; have := hp.formDisc_neg; nlinarith [mul_self_nonneg r]
  obtain ⟨g, hfg, hg⟩ := exists_formEquiv_isReducedForm f hns
  have hgp := hp.of_formEquiv hfg
  obtain ⟨α, β, γ, δ, hdet, hgd⟩ := hfg
  have hM : (α, β, γ, δ) ∈ formMaps f g := ⟨hdet, hgd.symm⟩
  rw [(automorphs_equiv_formMaps hM).2.2]
  obtain ⟨h4, h6, h2⟩ := hg.numAutomorphs_eq hgp
  by_cases ha : g.1 = g.2.2 ∧ g.2.1 = 0
  · exact Or.inr (Or.inl (h4 ha.1 ha.2))
  by_cases hb : g.1 = g.2.2 ∧ g.2.1 = g.1
  · exact Or.inr (Or.inr (h6 hb.1 hb.2))
  exact Or.inl (h2 ha hb)

lemma finite_automorphs {f : ℤ × ℤ × ℤ} (hp : IsPosDef f) : Finite (automorphs f) := by
  have h := numAutomorphs_mem hp
  unfold numAutomorphs at h
  exact (Nat.card_pos_iff.mp (by omega)).2

/-! ### Theorem 3.27 (counting) -/

/-- The third coefficient `k = (h² - d)/(4n)` of the form `(n, h, k)` of discriminant `d`. -/
def kOf (f : ℤ × ℤ × ℤ) (n h : ℤ) : ℤ := (h ^ 2 - formDisc f) / (4 * n)

lemma hSet_finite (f : ℤ × ℤ × ℤ) (n : ℤ) : (hSet f n).Finite :=
  (Set.finite_Ico 0 (2 * n)).subset fun _ hh ↦ ⟨hh.1, hh.2.1⟩

/-- The image of `f` under a matrix of `hMats f n` is `(n, h, kOf f n h)`. -/
lemma formSubst_eq_of_mem_hMats {f : ℤ × ℤ × ℤ} {n : ℤ} (hn : 0 < n) {M : ℤ × ℤ × ℤ × ℤ}
    (hM : M ∈ hMats f n) :
    formSubst f M.1 M.2.1 M.2.2.1 M.2.2.2 =
      (n, (formSubst f M.1 M.2.1 M.2.2.1 M.2.2.2).2.1,
        kOf f n (formSubst f M.1 M.2.1 M.2.2.1 M.2.2.2).2.1) := by
  obtain ⟨hdet, h1, -, -⟩ := hM
  have hd := formDisc_formSubst f M.1 M.2.1 M.2.2.1 M.2.2.2
  rw [hdet, one_pow, one_mul] at hd
  set S := formSubst f M.1 M.2.1 M.2.2.1 M.2.2.2
  obtain ⟨A, B, C⟩ := S
  simp only [formDisc] at hd h1 ⊢
  subst h1
  simp only [Prod.mk.injEq, true_and, kOf]
  refine Int.eq_ediv_of_mul_eq_right (by omega) ?_
  simp only [formDisc]
  linear_combination -hd

/-- The map `M ↦ h` from `hMats f n` to `hSet f n`. -/
def hMatsToHSet (f : ℤ × ℤ × ℤ) {n : ℤ} (hn : 0 < n) (M : hMats f n) : hSet f n :=
  ⟨(formSubst f M.1.1 M.1.2.1 M.1.2.2.1 M.1.2.2.2).2.1, M.2.2.2.1, M.2.2.2.2,
    kOf f n (formSubst f M.1.1 M.1.2.1 M.1.2.2.1 M.1.2.2.2).2.1, by
      have e := formSubst_eq_of_mem_hMats hn M.2
      have hd := formDisc_formSubst f M.1.1 M.1.2.1 M.1.2.2.1 M.1.2.2.2
      rw [M.2.1, one_pow, one_mul, e] at hd
      simp only [formDisc] at hd ⊢
      linear_combination hd,
    ⟨M.1.1, M.1.2.1, M.1.2.2.1, M.1.2.2.2, M.2.1, (formSubst_eq_of_mem_hMats hn M.2).symm⟩⟩

/-- The fibre of `hMatsToHSet` over `h` is the set of matrices taking `f` to `(n, h, kOf f n h)`. -/
def hMatsFiberEquiv (f : ℤ × ℤ × ℤ) {n : ℤ} (hn : 0 < n) (h : hSet f n) :
    {M : hMats f n // hMatsToHSet f hn M = h} ≃ formMaps f (n, h.1, kOf f n h.1) where
  toFun M := ⟨M.1.1, M.1.2.1, by
    have e := formSubst_eq_of_mem_hMats hn M.1.2
    have hh := congrArg Subtype.val M.2
    simp only [hMatsToHSet] at hh
    rw [e, hh]⟩
  invFun N := ⟨⟨N.1, N.2.1, by rw [formSubst_fst, ← formSubst_fst, N.2.2], by
      rw [N.2.2]; exact h.2.1, by rw [N.2.2]; exact h.2.2.1⟩, Subtype.ext (by
      simp only [hMatsToHSet]; rw [N.2.2])⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma nat_card_fiber {f : ℤ × ℤ × ℤ} {n : ℤ} (hn : 0 < n) (h : hSet f n) :
    Nat.card {M : hMats f n // hMatsToHSet f hn M = h} = numAutomorphs f := by
  rw [Nat.card_congr (hMatsFiberEquiv f hn h)]
  obtain ⟨-, -, k, hk, α, β, γ, δ, hdet, hg⟩ := h.2
  have hkk : k = kOf f n h.1 := by
    simp only [kOf]
    refine Int.eq_ediv_of_mul_eq_right (by omega) ?_
    linear_combination -hk
  have hM : (α, β, γ, δ) ∈ formMaps f (n, h.1, kOf f n h.1) := ⟨hdet, by rw [← hkk]; exact hg.symm⟩
  obtain ⟨⟨e⟩, -, -⟩ := automorphs_equiv_formMaps hM
  exact (Nat.card_congr e).symm

lemma finite_fiber {f : ℤ × ℤ × ℤ} (hp : IsPosDef f) {n : ℤ} (hn : 0 < n) (h : hSet f n) :
    Finite {M : hMats f n // hMatsToHSet f hn M = h} := by
  have h1 := nat_card_fiber hn h
  have h2 := numAutomorphs_mem hp
  exact (Nat.card_pos_iff.mp (by omega)).2

lemma nat_card_hMats {f : ℤ × ℤ × ℤ} (hp : IsPosDef f) {n : ℤ} (hn : 0 < n) :
    Nat.card (hMats f n) = numAutomorphs f * hCount f n ∧ Finite (hMats f n) := by
  have : Fintype (hSet f n) := (hSet_finite f n).fintype
  have := finite_fiber hp hn
  have e := (Equiv.sigmaFiberEquiv (hMatsToHSet f hn)).symm
  refine ⟨?_, Finite.of_equiv _ e.symm⟩
  rw [Nat.card_congr e, Nat.card_sigma]
  simp only [nat_card_fiber hn, Finset.sum_const, Finset.card_univ, smul_eq_mul, hCount,
    Nat.card_eq_fintype_card]
  ring

/-- **Theorem 3.27** (first identity). For a positive definite form `f` and `n > 0`, the number
`r_f(n)` of proper representations of `n` by `f` is `w(f) H_f(n)`. -/
@[kb "nivenzuckermanmontgomery" "Thm 3.27, p. 174"]
theorem properRepCount_eq_mul {f : ℤ × ℤ × ℤ} (hp : IsPosDef f) {n : ℤ} (hn : 0 < n) :
    properRepCount f n = numAutomorphs f * hCount f n := by
  obtain ⟨e⟩ := hMats_equiv_properReps f hn
  rw [properRepCount, ← Nat.card_congr e, (nat_card_hMats hp hn).1]

lemma finite_properReps {f : ℤ × ℤ × ℤ} (hp : IsPosDef f) {n : ℤ} (hn : 0 < n) :
    Finite (properReps f n) := by
  obtain ⟨e⟩ := hMats_equiv_properReps f hn
  have := (nat_card_hMats hp hn).2
  exact Finite.of_equiv _ e

/-- `f(m u, m v) = m² f(u, v)`. -/
lemma formEval_mul (f : ℤ × ℤ × ℤ) (m u v : ℤ) : formEval f (m * u) (m * v) = m ^ 2 * formEval f u v := by
  simp only [formEval]; ring

/-- For a representation `(x, y)` of `n > 0` by a positive definite form, `g = gcd(x, y)` is positive,
`g² ∣ n` and `f(x/g, y/g) = n/g²`. -/
lemma gcd_facts {f : ℤ × ℤ × ℤ} (hp : IsPosDef f) {n : ℕ} (hn : 0 < n) {x y : ℤ}
    (hxy : formEval f x y = n) :
    0 < Int.gcd x y ∧ (Int.gcd x y) ^ 2 ∣ n ∧
      formEval f (x / Int.gcd x y) (y / Int.gcd x y) = ((n / (Int.gcd x y) ^ 2 : ℕ) : ℤ) := by
  set g := Int.gcd x y with hg
  have hg0 : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h | h
    · obtain ⟨hx, hy⟩ := Int.gcd_eq_zero_iff.mp h
      rw [hx, hy] at hxy; simp [formEval] at hxy; omega
    · exact h
  have ex : x = g * (x / g) := (Int.mul_ediv_cancel' (Int.gcd_dvd_left x y)).symm
  have ey : y = g * (y / g) := (Int.mul_ediv_cancel' (Int.gcd_dvd_right x y)).symm
  have e : (n : ℤ) = (g : ℤ) ^ 2 * formEval f (x / g) (y / g) := by
    rw [← formEval_mul, ← ex, ← ey, hxy]
  have hdvd : ((g ^ 2 : ℕ) : ℤ) ∣ (n : ℤ) := ⟨_, by push_cast; exact e⟩
  have hdvd' := Int.natCast_dvd_natCast.mp hdvd
  refine ⟨hg0, hdvd', ?_⟩
  rw [Int.natCast_div, e]
  push_cast
  rw [Int.mul_ediv_cancel_left _ (by positivity)]

/-- The representations of `n` with `gcd(x, y) = m` correspond to the proper representations of
`n/m²` (the bijection of Theorem 3.27, second part). -/
def repsSigmaEquiv (f : ℤ × ℤ × ℤ) (hp : IsPosDef f) {n : ℕ} (hn : 0 < n) :
    reps f n ≃ Σ m : {m : ℕ // m ∈ n.divisors.filter (fun m ↦ m ^ 2 ∣ n)},
      properReps f ((n / m.1 ^ 2 : ℕ) : ℤ) where
  toFun P := ⟨⟨Int.gcd P.1.1 P.1.2, by
      obtain ⟨-, h2, -⟩ := gcd_facts hp hn P.2
      rw [Finset.mem_filter, Nat.mem_divisors]
      exact ⟨⟨(dvd_pow_self _ two_ne_zero).trans h2, hn.ne'⟩, h2⟩⟩,
    ⟨(P.1.1 / Int.gcd P.1.1 P.1.2, P.1.2 / Int.gcd P.1.1 P.1.2),
      Int.isCoprime_iff_gcd_eq_one.mpr (Int.gcd_div_gcd_div_gcd (gcd_facts hp hn P.2).1),
      (gcd_facts hp hn P.2).2.2⟩⟩
  invFun Q := ⟨((Q.1.1 : ℤ) * Q.2.1.1, (Q.1.1 : ℤ) * Q.2.1.2), by
    have hm := Q.1.2
    rw [Finset.mem_filter] at hm
    show formEval f _ _ = _
    rw [formEval_mul, Q.2.2.2]
    have h' : ((n / Q.1.1 ^ 2 : ℕ) : ℤ) * (Q.1.1 : ℤ) ^ 2 = n := by
      exact_mod_cast Nat.div_mul_cancel hm.2
    linear_combination h'⟩
  left_inv P := by
    apply Subtype.ext
    simp only
    exact Prod.ext (Int.mul_ediv_cancel' (Int.gcd_dvd_left _ _))
      (Int.mul_ediv_cancel' (Int.gcd_dvd_right _ _))
  right_inv Q := by
    obtain ⟨⟨m, hm⟩, ⟨⟨u, v⟩, hco, hval⟩⟩ := Q
    have hgm : Int.gcd ((m : ℤ) * u) ((m : ℤ) * v) = m := by
      rw [Int.gcd_mul_left, Int.isCoprime_iff_gcd_eq_one.mp hco]; simp
    have hm0 : (m : ℤ) ≠ 0 := by
      rw [Finset.mem_filter, Nat.mem_divisors] at hm
      exact_mod_cast (Nat.pos_of_dvd_of_pos hm.1.1 hn).ne'
    refine Sigma.subtype_ext (Subtype.ext hgm) ?_
    simp only [hgm]
    exact Prod.ext (Int.mul_ediv_cancel_left _ hm0) (Int.mul_ediv_cancel_left _ hm0)

/-- **Theorem 3.27** (second identity). For a positive definite form `f` and `n > 0`,
`R_f(n) = ∑_{m² ∣ n} r_f(n/m²)`. -/
@[kb "nivenzuckermanmontgomery" "Thm 3.27, p. 174"]
theorem repCount_eq_sum {f : ℤ × ℤ × ℤ} (hp : IsPosDef f) {n : ℕ} (hn : 0 < n) :
    repCount f n = ∑ m ∈ n.divisors.filter (fun m ↦ m ^ 2 ∣ n), properRepCount f ((n / m ^ 2 : ℕ) : ℤ) := by
  have hfin : ∀ m : {m : ℕ // m ∈ n.divisors.filter (fun m ↦ m ^ 2 ∣ n)},
      Finite (properReps f ((n / m.1 ^ 2 : ℕ) : ℤ)) := by
    rintro ⟨m, hm⟩
    rw [Finset.mem_filter, Nat.mem_divisors] at hm
    have h0 : 0 < n / m ^ 2 := Nat.div_pos (Nat.le_of_dvd hn hm.2) (by
      have := Nat.pos_of_dvd_of_pos hm.1.1 hn; positivity)
    exact finite_properReps hp (by exact_mod_cast h0)
  rw [repCount, Nat.card_congr (repsSigmaEquiv f hp hn), Nat.card_sigma]
  exact Finset.sum_coe_sort (n.divisors.filter (fun m ↦ m ^ 2 ∣ n))
    (fun m ↦ properRepCount f ((n / m ^ 2 : ℕ) : ℤ))

end NTKB.NZM
