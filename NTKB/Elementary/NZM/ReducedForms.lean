/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.NZM.QuadraticForms

/-!
# Uniqueness of reduced positive definite forms (Niven–Zuckerman–Montgomery, § 3.7)

**Theorem 3.25.** Two equivalent reduced positive definite binary quadratic forms are equal.

The book derives this from Lemma 3.24 (where a reduced form takes small values). We use the same
inequality in the form: for a reduced form `(a, b, c)` with `a > 0` (so `|b| ≤ a ≤ c`),
`f(x, y) ≥ a - |b| + c` whenever `xy ≠ 0`, `f(x, 0) ≥ a` and `f(0, y) ≥ c` for `x, y ≠ 0`. Hence `a` is
the least nonzero value of `f` on `ℤ² \ {0}`, so equivalent reduced forms have the same `a`; then the
first column of the substitution is a vector where `f` takes the value `a`, which is `±(1, 0)` unless
`a = c`; this pins down `b`, and `c` follows from the discriminant.
-/

namespace NTKB.NZM

open NTKB.Davenport

/-- Lemma 3.24-type lower bounds for a reduced form `(a, b, c)` with `a, c > 0`. -/
theorem IsReducedForm.formEval_ge {f : ℤ × ℤ × ℤ} (hf : IsReducedForm f) (ha : 0 < f.1)
    (hc : 0 < f.2.2) {x y : ℤ} :
    (x ≠ 0 → y ≠ 0 → f.1 - |f.2.1| + f.2.2 ≤ formEval f x y) ∧
      (x ≠ 0 → y = 0 → f.1 ≤ formEval f x y) ∧ (x = 0 → y ≠ 0 → f.2.2 ≤ formEval f x y) := by
  obtain ⟨h1, h2⟩ := hf.abs_le_abs
  obtain ⟨a, b, c⟩ := f
  simp only at h1 h2 ha hc ⊢
  rw [abs_of_pos ha] at h1 h2
  rw [abs_of_pos hc] at h2
  simp only [formEval]
  have hbxy : -(|b| * |x| * |y|) ≤ b * x * y := by
    rw [← abs_mul, ← abs_mul]; exact neg_abs_le _
  have hx2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have hy2 : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
  have hb0 := abs_nonneg b
  have hab : 0 ≤ a - |b| := by linarith
  have hcb : 0 ≤ c - |b| := by linarith
  refine ⟨fun hx hy ↦ ?_, fun hx hy ↦ ?_, fun hx hy ↦ ?_⟩
  · have hX : 1 ≤ |x| := Int.one_le_abs hx
    have hY : 1 ≤ |y| := Int.one_le_abs hy
    have hX2 : 1 ≤ |x| ^ 2 := by nlinarith
    have hY2 : 1 ≤ |y| ^ 2 := by nlinarith
    rcases le_total |y| |x| with h | h
    · have k1 : |b| * |x| * |y| ≤ |b| * |x| ^ 2 := by
        have := mul_le_mul_of_nonneg_left h (mul_nonneg hb0 (abs_nonneg x)); nlinarith
      have k2 : (a - |b|) * 1 ≤ (a - |b|) * |x| ^ 2 := mul_le_mul_of_nonneg_left hX2 hab
      have k3 : c * 1 ≤ c * |y| ^ 2 := mul_le_mul_of_nonneg_left hY2 hc.le
      rw [hx2, hy2]; nlinarith
    · have k1 : |b| * |x| * |y| ≤ |b| * |y| ^ 2 := by
        have := mul_le_mul_of_nonneg_left h (mul_nonneg hb0 (abs_nonneg y)); nlinarith
      have k2 : a * 1 ≤ a * |x| ^ 2 := mul_le_mul_of_nonneg_left hX2 ha.le
      have k3 : (c - |b|) * 1 ≤ (c - |b|) * |y| ^ 2 := mul_le_mul_of_nonneg_left hY2 hcb
      rw [hx2, hy2]; nlinarith
  · subst hy
    have hX2 : 1 ≤ x ^ 2 := by rw [hx2]; have := Int.one_le_abs hx; nlinarith
    have := mul_le_mul_of_nonneg_left hX2 ha.le
    simp only [mul_zero, add_zero, zero_pow two_ne_zero]; linarith
  · subst hx
    have hY2 : 1 ≤ y ^ 2 := by rw [hy2]; have := Int.one_le_abs hy; nlinarith
    have := mul_le_mul_of_nonneg_left hY2 hc.le
    simp only [mul_zero, zero_add, zero_pow two_ne_zero, zero_mul]; linarith

/-- A reduced form with `a, c > 0` takes values `≥ a` at all nonzero integer vectors. -/
theorem IsReducedForm.fst_le_formEval {f : ℤ × ℤ × ℤ} (hf : IsReducedForm f) (ha : 0 < f.1)
    (hc : 0 < f.2.2) {x y : ℤ} (hxy : (x, y) ≠ (0, 0)) : f.1 ≤ formEval f x y := by
  obtain ⟨h1, h2⟩ := hf.abs_le_abs
  obtain ⟨g1, g2, g3⟩ := hf.formEval_ge ha hc (x := x) (y := y)
  rw [abs_of_pos ha] at h1 h2
  rw [abs_of_pos hc] at h2
  by_cases hx : x = 0
  · have hy : y ≠ 0 := fun hy ↦ hxy (by simp [hx, hy])
    have := g3 hx hy
    linarith
  · by_cases hy : y = 0
    · exact g2 hx hy
    · have := g1 hx hy
      linarith

/-- For a reduced form with `a > 0`: `-a < b ≤ a`. -/
lemma IsReducedForm.b_bounds {f : ℤ × ℤ × ℤ} (hf : IsReducedForm f) (ha : 0 < f.1) :
    -f.1 < f.2.1 ∧ f.2.1 ≤ f.1 := by
  rcases hf with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩ <;> simp only [abs_of_pos ha] at h1 h2 <;>
    constructor <;> linarith

/-- The value of `f` at the first column of a substitution is the first coefficient of the image. -/
lemma formSubst_fst (f : ℤ × ℤ × ℤ) (α β γ δ : ℤ) : (formSubst f α β γ δ).1 = formEval f α γ := by
  simp only [formSubst, formEval]

/-- The key step: if `g = f ∘ M` (`det M = 1`) with `f, g` reduced, `a_f = a_g > 0`, then `g = f` or
`c_f = a_f`. -/
lemma eq_or_snd_snd_eq_of_fst_eq {f : ℤ × ℤ × ℤ} (hf : IsReducedForm f) (ha : 0 < f.1)
    (hcpos : 0 < f.2.2) {α β γ δ : ℤ} (hdet : α * δ - β * γ = 1) (hg : IsReducedForm (formSubst f α β γ δ))
    (hfst : (formSubst f α β γ δ).1 = f.1) : formSubst f α β γ δ = f ∨ f.2.2 = f.1 := by
  obtain ⟨h1, h2⟩ := hf.abs_le_abs
  rw [abs_of_pos ha] at h1 h2
  have hval : formEval f α γ = f.1 := by rw [← formSubst_fst]; exact hfst
  obtain ⟨g1, g2, g3⟩ := hf.formEval_ge ha hcpos (x := α) (y := γ)
  rw [abs_of_pos hcpos] at h2
  by_cases hγ : γ = 0
  · -- `M = ±[[1, β'], [0, 1]]`: then `b_g = b_f + 2aαβ`, and both lie in `(-a, a]`
    subst hγ
    have hαδ : α * δ = 1 := by linarith
    have hδ : α = δ := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one hαδ with h | h <;> subst h <;> linarith
    subst hδ
    have hgb := hg.b_bounds (by rw [hfst]; exact ha)
    rw [hfst] at hgb
    have hfb := hf.b_bounds ha
    have e : (formSubst f α β 0 α).2.1 = f.2.1 + 2 * f.1 * (α * β) := by
      simp only [formSubst]; linear_combination f.2.1 * hαδ
    rw [e] at hgb
    have hk : α * β = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have : f.1 * (α * β) ≤ -f.1 := by nlinarith
        linarith
      · have : f.1 ≤ f.1 * (α * β) := by nlinarith
        linarith
    have hα0 : α ≠ 0 := by rintro rfl; simp at hαδ
    have hβ : β = 0 := by
      rcases mul_eq_zero.mp hk with h | h
      · exact absurd h hα0
      · exact h
    subst hβ
    left
    obtain ⟨a, b, c⟩ := f
    simp only [formSubst, Prod.mk.injEq]
    refine ⟨by linear_combination a * hαδ, by linear_combination b * hαδ,
      by linear_combination c * hαδ⟩
  · right
    by_cases hα : α = 0
    · -- `f(0, γ) = c = a`
      have := g3 hα hγ
      rw [hval] at this
      linarith
    · -- `f(α, γ) ≥ a - |b| + c`, so `c ≤ |b| ≤ a ≤ c`
      have := g1 hα hγ
      rw [hval] at this
      have hb := abs_nonneg f.2.1
      linarith

/-- **Theorem 3.25.** Two equivalent reduced positive definite binary quadratic forms are equal. -/
@[kb "nivenzuckermanmontgomery" "Thm 3.25, p. 171"]
theorem eq_of_formEquiv_of_isReducedForm {f g : ℤ × ℤ × ℤ} (hf : IsReducedForm f)
    (hg : IsReducedForm g) (hfp : IsPosDef f) (hgp : IsPosDef g) (hfg : FormEquiv f g) : f = g := by
  have haf : 0 < f.1 := by simpa [formEval] using hfp 1 0 (by simp)
  have hag : 0 < g.1 := by simpa [formEval] using hgp 1 0 (by simp)
  have hcf0 : 0 < f.2.2 := by simpa [formEval] using hfp 0 1 (by simp)
  have hcg0 : 0 < g.2.2 := by simpa [formEval] using hgp 0 1 (by simp)
  -- the first coefficients agree: each is the least value of the other form
  have hle : ∀ {f g : ℤ × ℤ × ℤ}, IsReducedForm f → 0 < f.1 → 0 < f.2.2 → FormEquiv f g →
      f.1 ≤ g.1 := by
    intro f g hf ha hc ⟨α, β, γ, δ, hdet, hgd⟩
    rw [hgd, formSubst_fst]
    refine hf.fst_le_formEval ha hc fun h ↦ ?_
    simp only [Prod.mk.injEq] at h
    rw [h.1, h.2] at hdet; simp at hdet
  have hfa : f.1 = g.1 :=
    le_antisymm (hle hf haf hcf0 hfg) (hle hg hag hcg0 (formEquiv_symm hfg))
  have hd : formDisc g = formDisc f := hfg.formDisc_eq
  obtain ⟨α, β, γ, δ, hdet, hgd⟩ := hfg
  rcases eq_or_snd_snd_eq_of_fst_eq hf haf hcf0 hdet (by rw [← hgd]; exact hg)
    (by rw [← hgd]; exact hfa.symm) with h | hcf
  · exact (hgd.trans h).symm
  obtain ⟨α', β', γ', δ', hdet', hfd⟩ := formEquiv_symm ⟨α, β, γ, δ, hdet, hgd⟩
  rcases eq_or_snd_snd_eq_of_fst_eq hg hag hcg0 hdet' (by rw [← hfd]; exact hf)
    (by rw [← hfd]; exact hfa) with h | hcg
  · exact hfd.trans h
  -- `a = c` for both forms, so `b ≥ 0` for both; equal discriminants give `b_f² = b_g²`
  have hbf : 0 ≤ f.2.1 := by
    rcases hf with ⟨-, -, h3⟩ | ⟨h1, -, -⟩
    · rw [hcf] at h3; exact absurd h3 (lt_irrefl _)
    · exact h1
  have hbg : 0 ≤ g.2.1 := by
    rcases hg with ⟨-, -, h3⟩ | ⟨h1, -, -⟩
    · rw [hcg] at h3; exact absurd h3 (lt_irrefl _)
    · exact h1
  have hb2 : g.2.1 ^ 2 = f.2.1 ^ 2 := by
    simp only [formDisc] at hd
    rw [hcf, hcg, ← hfa] at hd
    linarith
  have hb : g.2.1 = f.2.1 := (sq_eq_sq₀ hbg hbf).mp hb2
  obtain ⟨a, b, c⟩ := f
  obtain ⟨a', b', c'⟩ := g
  simp only at hfa hcf hcg hb
  simp only [Prod.mk.injEq]
  exact ⟨hfa, hb.symm, by rw [hcf, hcg, hfa]⟩

/-! ### Definition 3.10 and Theorem 3.26 (counting part) -/

/-- The unimodular substitutions `(m₁₁, m₁₂, m₂₁, m₂₂)` (`m₁₁m₂₂ - m₁₂m₂₁ = 1`) taking `f` to `g`:
`g(x, y) = f(m₁₁x + m₁₂y, m₂₁x + m₂₂y)`. -/
def formMaps (f g : ℤ × ℤ × ℤ) : Set (ℤ × ℤ × ℤ × ℤ) :=
  {M | M.1 * M.2.2.2 - M.2.1 * M.2.2.1 = 1 ∧ formSubst f M.1 M.2.1 M.2.2.1 M.2.2.2 = g}

/-- **Definition 3.10.** The automorphs of `f`: the matrices of the modular group taking `f` to itself;
`w(f)` (`numAutomorphs f`) is their number. -/
def automorphs (f : ℤ × ℤ × ℤ) : Set (ℤ × ℤ × ℤ × ℤ) := formMaps f f

/-- **Definition 3.10.** `w(f)`, the number of automorphs of `f`. -/
noncomputable def numAutomorphs (f : ℤ × ℤ × ℤ) : ℕ := Nat.card (automorphs f)

/-- The product of `2 × 2` matrices written as quadruples `(m₁₁, m₁₂, m₂₁, m₂₂)`. -/
def matMul (A B : ℤ × ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ × ℤ :=
  (A.1 * B.1 + A.2.1 * B.2.2.1, A.1 * B.2.1 + A.2.1 * B.2.2.2,
    A.2.2.1 * B.1 + A.2.2.2 * B.2.2.1, A.2.2.1 * B.2.1 + A.2.2.2 * B.2.2.2)

/-- The inverse of a unimodular matrix. -/
def matInv (A : ℤ × ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ × ℤ := (A.2.2.2, -A.2.1, -A.2.2.1, A.1)

lemma formSubst_matMul (f : ℤ × ℤ × ℤ) (A B : ℤ × ℤ × ℤ × ℤ) :
    formSubst f (matMul A B).1 (matMul A B).2.1 (matMul A B).2.2.1 (matMul A B).2.2.2 =
      formSubst (formSubst f A.1 A.2.1 A.2.2.1 A.2.2.2) B.1 B.2.1 B.2.2.1 B.2.2.2 := by
  rw [formSubst_formSubst]; rfl

lemma det_matMul (A B : ℤ × ℤ × ℤ × ℤ) :
    (matMul A B).1 * (matMul A B).2.2.2 - (matMul A B).2.1 * (matMul A B).2.2.1 =
      (A.1 * A.2.2.2 - A.2.1 * A.2.2.1) * (B.1 * B.2.2.2 - B.2.1 * B.2.2.1) := by
  simp only [matMul]; ring

lemma matMul_matInv {A : ℤ × ℤ × ℤ × ℤ} (h : A.1 * A.2.2.2 - A.2.1 * A.2.2.1 = 1) (B : ℤ × ℤ × ℤ × ℤ) :
    matMul (matMul B A) (matInv A) = B := by
  obtain ⟨a, b, c, d⟩ := A
  obtain ⟨p, q, r, s⟩ := B
  simp only at h
  simp only [matMul, matInv, Prod.mk.injEq]
  exact ⟨by linear_combination p * h, by linear_combination q * h, by linear_combination r * h,
    by linear_combination s * h⟩

lemma matMul_matInv_matMul {A : ℤ × ℤ × ℤ × ℤ} (h : A.1 * A.2.2.2 - A.2.1 * A.2.2.1 = 1)
    (B : ℤ × ℤ × ℤ × ℤ) : matMul (matMul B (matInv A)) A = B := by
  obtain ⟨a, b, c, d⟩ := A
  obtain ⟨p, q, r, s⟩ := B
  simp only at h
  simp only [matMul, matInv, Prod.mk.injEq]
  exact ⟨by linear_combination p * h, by linear_combination q * h, by linear_combination r * h,
    by linear_combination s * h⟩

/-- **Theorem 3.26** (counting part). If `M` takes `f` to `g`, then `A ↦ AM` is a bijection from the
automorphs of `f` onto the matrices of the modular group taking `f` to `g`, and `N ↦ N⁻¹` is a bijection
from these onto the matrices taking `g` to `f`; in particular `w(f) = w(g)` (the automorphs of `g` are
`M⁻¹AM`). -/
@[kb "nivenzuckermanmontgomery" "Thm 3.26, p. 173"]
theorem automorphs_equiv_formMaps {f g : ℤ × ℤ × ℤ} {M : ℤ × ℤ × ℤ × ℤ} (hM : M ∈ formMaps f g) :
    Nonempty (automorphs f ≃ formMaps f g) ∧ Nonempty (formMaps f g ≃ formMaps g f) ∧
      numAutomorphs f = numAutomorphs g := by
  obtain ⟨hdet, hfg⟩ := hM
  have hdetInv : (matInv M).1 * (matInv M).2.2.2 - (matInv M).2.1 * (matInv M).2.2.1 = 1 := by
    simp only [matInv]; linear_combination hdet
  -- `g ∘ M⁻¹ = f`
  have hgf : formSubst g (matInv M).1 (matInv M).2.1 (matInv M).2.2.1 (matInv M).2.2.2 = f := by
    rw [← hfg, ← formSubst_matMul]
    have : matMul M (matInv M) = (1, 0, 0, 1) := by
      obtain ⟨a, b, c, d⟩ := M
      simp only at hdet
      simp only [matMul, matInv, Prod.mk.injEq]
      refine ⟨by linear_combination hdet, by ring, by ring, by linear_combination hdet⟩
    rw [this]
    obtain ⟨a, b, c⟩ := f
    simp only [formSubst, Prod.mk.injEq]; refine ⟨by ring, by ring, by ring⟩
  -- automorphs of `f` ≃ maps `f → g`
  let e1 : automorphs f ≃ formMaps f g :=
    { toFun := fun A ↦ ⟨matMul A.1 M, by
        refine ⟨by rw [det_matMul, A.2.1, hdet, one_mul], ?_⟩
        rw [formSubst_matMul, A.2.2, hfg]⟩
      invFun := fun N ↦ ⟨matMul N.1 (matInv M), by
        refine ⟨by rw [det_matMul, N.2.1, hdetInv, one_mul], ?_⟩
        rw [formSubst_matMul, N.2.2, hgf]⟩
      left_inv := fun A ↦ Subtype.ext (matMul_matInv hdet A.1)
      right_inv := fun N ↦ Subtype.ext (matMul_matInv_matMul hdet N.1) }
  -- maps `f → g` ≃ maps `g → f` (inverse matrices)
  have hinv_det : ∀ N : ℤ × ℤ × ℤ × ℤ, N.1 * N.2.2.2 - N.2.1 * N.2.2.1 = 1 →
      (matInv N).1 * (matInv N).2.2.2 - (matInv N).2.1 * (matInv N).2.2.1 = 1 := by
    intro N hN; simp only [matInv]; linear_combination hN
  have hinv_map : ∀ {f g : ℤ × ℤ × ℤ} (N : ℤ × ℤ × ℤ × ℤ), N ∈ formMaps f g → matInv N ∈ formMaps g f := by
    intro f g N ⟨hN, hNfg⟩
    refine ⟨hinv_det N hN, ?_⟩
    rw [← hNfg, ← formSubst_matMul]
    have : matMul N (matInv N) = (1, 0, 0, 1) := by
      obtain ⟨a, b, c, d⟩ := N
      simp only at hN
      simp only [matMul, matInv, Prod.mk.injEq]
      refine ⟨by linear_combination hN, by ring, by ring, by linear_combination hN⟩
    rw [this]
    obtain ⟨a, b, c⟩ := f
    simp only [formSubst, Prod.mk.injEq]; refine ⟨by ring, by ring, by ring⟩
  have hinv_inv : ∀ N : ℤ × ℤ × ℤ × ℤ, matInv (matInv N) = N := by
    intro N; obtain ⟨a, b, c, d⟩ := N; simp [matInv]
  let e2 : formMaps f g ≃ formMaps g f :=
    { toFun := fun N ↦ ⟨matInv N.1, hinv_map N.1 N.2⟩
      invFun := fun N ↦ ⟨matInv N.1, hinv_map N.1 N.2⟩
      left_inv := fun N ↦ Subtype.ext (hinv_inv N.1)
      right_inv := fun N ↦ Subtype.ext (hinv_inv N.1) }
  -- automorphs of `g` ≃ maps `g → f` (by the first part with `M⁻¹`)
  let e3 : automorphs g ≃ formMaps g f :=
    { toFun := fun A ↦ ⟨matMul A.1 (matInv M), by
        refine ⟨by rw [det_matMul, A.2.1, hdetInv, one_mul], ?_⟩
        rw [formSubst_matMul, A.2.2, hgf]⟩
      invFun := fun N ↦ ⟨matMul N.1 M, by
        refine ⟨by rw [det_matMul, N.2.1, hdet, one_mul], ?_⟩
        rw [formSubst_matMul, N.2.2, hfg]⟩
      left_inv := fun A ↦ Subtype.ext (by
        have := matMul_matInv_matMul hdet A.1
        exact this)
      right_inv := fun N ↦ Subtype.ext (matMul_matInv hdet N.1) }
  refine ⟨⟨e1⟩, ⟨e2⟩, ?_⟩
  exact Nat.card_congr ((e1.trans e2).trans e3.symm)

end NTKB.NZM
