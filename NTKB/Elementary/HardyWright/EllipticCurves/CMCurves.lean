/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import NTKB.IrelandRosen.R5.MordellInfinite

/-!
# Hardy–Wright, Chapter XXV: congruent numbers, the automorphisms of `y² = x³ + Ax` and
`y² = x³ + B`, and Theorem 465

* **Section 25.1 (congruent numbers).** A positive rational `n` is a *congruent number* if it is
  the area of a right triangle with rational sides. `n` is congruent if and only if
  `y² = x³ - n²x` has a rational point with `y ≠ 0` (`isCongruentNumber_iff`), and if and only if
  it has one with `x > 0`, `y > 0` (`isCongruentNumber_iff_pos`). The bijection is
  `(a, b, c) ↦ (n(a + c)/b, 2n²(a + c)/b²)` with inverse `(x, y) ↦ ((x² - n²)/y, 2nx/y, (x² + n²)/y)`.
  Hardy–Wright state it for squarefree `n`; the statement holds for every positive rational `n`.
* **Section 25.2 (complex multiplication).** On `y² = x³ + Ax` over a field containing `i`
  (`i² = -1`), `(x, y) ↦ (-x, iy)` is an automorphism `cmI` of the group of points with
  `cmI (cmI P) = -P`; on `y² = x³ + B` over a field containing `ρ` (`ρ² + ρ + 1 = 0`),
  `(x, y) ↦ (ρx, y)` is an automorphism `cmRho` with `cmRho (cmRho P) + cmRho P + P = 0`. So
  `ℤ[i]` (resp. `ℤ[ρ]`) acts on the points. (That these are all the endomorphisms,
  `End(E) = ℤ[i]` resp. `ℤ[ρ]`, is stated in the book without proof and is not formalized.)
* **Theorem 465.** For `A ≠ 0`, `(X, Y) ↦ (12A/(X + Y), 36A(X - Y)/(X + Y))` is a bijection from
  the rational solutions of `X³ + Y³ = A` onto the rational solutions of `y² = x³ - 432A²` with
  `x ≠ 0` (`cubesEquivMordell`; the maps are `NTKB.IrelandRosen.CM.cubesToMordell` and
  `mordellToCubes` of Ireland–Rosen 17.10.1).
-/

namespace NTKB.HardyWright

open WeierstrassCurve

/-! ### Section 25.1: congruent numbers -/

/-- `n` is a **congruent number**: the area of a right triangle with rational sides. -/
def IsCongruentNumber (n : ℚ) : Prop :=
  ∃ a b c : ℚ, 0 < a ∧ 0 < b ∧ a ^ 2 + b ^ 2 = c ^ 2 ∧ a * b / 2 = n

/-- **Hardy–Wright §25.1.** A positive rational `n` is congruent if and only if `y² = x³ - n²x`
has a rational point with `y ≠ 0`. -/
@[kb "hardywright2008" "Section 25.1, p. 568"]
theorem isCongruentNumber_iff {n : ℚ} (hn : 0 < n) :
    IsCongruentNumber n ↔ ∃ x y : ℚ, y ≠ 0 ∧ y ^ 2 = x ^ 3 - n ^ 2 * x := by
  constructor
  · rintro ⟨a, b, c, ha, hb, h, hn⟩
    have hc : |c| ^ 2 = a ^ 2 + b ^ 2 := by rw [sq_abs]; exact h.symm
    have hc0 : 0 ≤ |c| := abs_nonneg c
    have hac : 0 < a + |c| := by linarith
    refine ⟨n * (a + |c|) / b, 2 * n ^ 2 * (a + |c|) / b ^ 2, by positivity, ?_⟩
    have hn' : n = a * b / 2 := hn.symm
    subst hn'
    have hb' : b ≠ 0 := hb.ne'
    field_simp
    linear_combination (-1) * hc
  · rintro ⟨x, y, hy, h⟩
    have hn0 : n ≠ 0 := hn.ne'
    have a1 : (x ^ 2 - n ^ 2) / y * (2 * n * x / y) / 2 = n := by
      field_simp
      linear_combination (-1) * h
    refine ⟨|(x ^ 2 - n ^ 2) / y|, |2 * n * x / y|, |(x ^ 2 + n ^ 2) / y|, ?_, ?_, ?_, ?_⟩
    · apply abs_pos.2
      intro e
      have h' : n = 0 := by rw [← a1, e]; simp
      exact hn0 h'
    · apply abs_pos.2
      intro e
      have h' : n = 0 := by rw [← a1, e]; simp
      exact hn0 h'
    · rw [sq_abs, sq_abs, sq_abs]
      field_simp
      linear_combination (4 * n ^ 2 * x ^ 2 * 0 : ℚ) + (-(4 * n ^ 2 * x ^ 2) + 4 * n ^ 2 * x ^ 2) * h
    · have hpos : 0 < (x ^ 2 - n ^ 2) / y * (2 * n * x / y) := by
        have : (x ^ 2 - n ^ 2) / y * (2 * n * x / y) = 2 * n := by linarith
        rw [this]; linarith
      rw [← abs_mul, abs_of_pos hpos]; linarith

/-- **Hardy–Wright §25.1**, the book's form: a positive rational `n` is congruent if and only if
`y² = x³ - n²x` has a rational point with `x > 0`, `y > 0`. -/
@[kb "hardywright2008" "Section 25.1, p. 568"]
theorem isCongruentNumber_iff_pos {n : ℚ} (hn : 0 < n) :
    IsCongruentNumber n ↔ ∃ x y : ℚ, 0 < x ∧ 0 < y ∧ y ^ 2 = x ^ 3 - n ^ 2 * x := by
  constructor
  · intro hc
    obtain ⟨a, b, c, ha, hb, h, hn'⟩ := hc
    have hc : |c| ^ 2 = a ^ 2 + b ^ 2 := by rw [sq_abs]; exact h.symm
    have hc0 : 0 ≤ |c| := abs_nonneg c
    have hac : 0 < a + |c| := by linarith
    refine ⟨n * (a + |c|) / b, 2 * n ^ 2 * (a + |c|) / b ^ 2, by positivity, by positivity, ?_⟩
    subst hn'
    have hb' : b ≠ 0 := hb.ne'
    field_simp
    linear_combination (-1) * hc
  · rintro ⟨x, y, -, hy, h⟩
    exact (isCongruentNumber_iff hn).2 ⟨x, y, hy.ne', h⟩

/-! ### Section 25.2: the automorphisms `[i]` and `[ρ]` -/

section CM

variable {K : Type*} [Field K] [DecidableEq K]

/-- Scaling `(x, y) ↦ (ux, vy)` on a Weierstrass curve with `a₁ = a₂ = a₃ = 0`, `v² = u³`:
the chord slope scales by `v/u`. -/
lemma slope_scale (W : WeierstrassCurve K) {u v : K} (hu : u ≠ 0) (hv : v ^ 2 = u ^ 3)
    (h1 : W.a₁ = 0) (h2 : W.a₂ = 0) (h3 : W.a₃ = 0) (h4 : W.a₄ * u ^ 3 = W.a₄ * u)
    (x₁ x₂ y₁ y₂ : K) :
    W.toAffine.slope (u * x₁) (u * x₂) (v * y₁) (v * y₂) =
      v / u * W.toAffine.slope x₁ x₂ y₁ y₂ := by
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hu (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0) |>.1 (by simpa using hv.symm))
  by_cases hx : x₁ = x₂
  · subst hx
    by_cases hy : y₁ = W.toAffine.negY x₁ y₂
    · have hy' : v * y₁ = W.toAffine.negY (u * x₁) (v * y₂) := by
        simp only [Affine.negY, h1, h3] at hy ⊢
        rw [hy]; ring
      rw [Affine.slope_of_Y_eq rfl hy, Affine.slope_of_Y_eq rfl hy']; ring
    · have hy' : ¬ v * y₁ = W.toAffine.negY (u * x₁) (v * y₂) := by
        intro e; apply hy
        simp only [Affine.negY, h1, h3] at e ⊢
        apply mul_left_cancel₀ hv0; linear_combination e
      rw [Affine.slope_of_Y_ne rfl hy, Affine.slope_of_Y_ne rfl hy']
      simp only [Affine.negY, h1, h2, h3]
      by_cases hy2 : y₁ - (-y₁ - 0 * x₁ - 0) = 0
      · have : v * y₁ - (-(v * y₁) - 0 * (u * x₁) - 0) = 0 := by linear_combination v * hy2
        rw [hy2, this]; simp
      · have : v * y₁ - (-(v * y₁) - 0 * (u * x₁) - 0) ≠ 0 := by
          intro e; apply hy2; apply mul_left_cancel₀ hv0; linear_combination e
        have eD : v * y₁ - (-(v * y₁) - 0 * (u * x₁) - 0) = v * (y₁ - (-y₁ - 0 * x₁ - 0)) := by
          ring
        rw [eD]
        field_simp
        congr 1
        have h4' : W.toAffine.a₄ * u ^ 3 = W.toAffine.a₄ * u := h4
        linear_combination (-(3 * x₁ ^ 2 + W.toAffine.a₄)) * hv - h4'
  · have hx' : u * x₁ ≠ u * x₂ := fun e => hx (mul_left_cancel₀ hu e)
    rw [Affine.slope_of_X_ne hx, Affine.slope_of_X_ne hx']
    have : x₁ - x₂ ≠ 0 := sub_ne_zero.2 hx
    field_simp

lemma addX_scale (W : WeierstrassCurve K) {u v : K} (hu : u ≠ 0) (hv : v ^ 2 = u ^ 3)
    (h1 : W.a₁ = 0) (h2 : W.a₂ = 0) (x₁ x₂ s : K) :
    W.toAffine.addX (u * x₁) (u * x₂) (v / u * s) = u * W.toAffine.addX x₁ x₂ s := by
  have : (v / u) ^ 2 = u := by field_simp; linear_combination hv
  simp only [Affine.addX, h1, h2, mul_pow, this]
  ring

lemma addY_scale (W : WeierstrassCurve K) {u v : K} (hu : u ≠ 0) (hv : v ^ 2 = u ^ 3)
    (h1 : W.a₁ = 0) (h2 : W.a₂ = 0) (h3 : W.a₃ = 0) (x₁ x₂ y₁ s : K) :
    W.toAffine.addY (u * x₁) (u * x₂) (v * y₁) (v / u * s) =
      v * W.toAffine.addY x₁ x₂ y₁ s := by
  simp only [Affine.addY, Affine.negY, Affine.negAddY, addX_scale W hu hv h1 h2, h1, h3]
  field_simp
  ring


/-- The scaling map on points. -/
noncomputable def scaleFun (W : WeierstrassCurve K) (u v : K)
    (hns : ∀ x y, W.toAffine.Nonsingular x y → W.toAffine.Nonsingular (u * x) (v * y)) :
    W.toAffine.Point → W.toAffine.Point
  | .zero => .zero
  | .some x y h => .some (u * x) (v * y) (hns x y h)

lemma scaleFun_add (W : WeierstrassCurve K) {u v : K} (hu : u ≠ 0) (hv : v ^ 2 = u ^ 3)
    (h1 : W.a₁ = 0) (h2 : W.a₂ = 0) (h3 : W.a₃ = 0) (h4 : W.a₄ * u ^ 3 = W.a₄ * u)
    (hns : ∀ x y, W.toAffine.Nonsingular x y → W.toAffine.Nonsingular (u * x) (v * y))
    (P Q : W.toAffine.Point) :
    scaleFun W u v hns (P + Q) = scaleFun W u v hns P + scaleFun W u v hns Q := by
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hu (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0) |>.1 (by simpa using hv.symm))
  rcases P with _ | @⟨x₁, y₁, h₁⟩
  · have h0 : scaleFun W u v hns 0 = 0 := rfl
    show scaleFun W u v hns (0 + Q) = scaleFun W u v hns 0 + _
    rw [zero_add, h0, zero_add]
  rcases Q with _ | @⟨x₂, y₂, h₂⟩
  · have h0 : scaleFun W u v hns 0 = 0 := rfl
    show scaleFun W u v hns (_ + 0) = _ + scaleFun W u v hns 0
    rw [add_zero, h0, add_zero]
  by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
  · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2]
    have : u * x₁ = u * x₂ ∧ v * y₁ = W.toAffine.negY (u * x₂) (v * y₂) := by
      refine ⟨by rw [hxy.1], ?_⟩
      have := hxy.2
      simp only [Affine.negY, h1, h3] at this ⊢
      rw [this]; ring
    exact (Affine.Point.add_of_Y_eq (h₁ := hns _ _ h₁) (h₂ := hns _ _ h₂) this.1 this.2).symm
  · have hxy' : ¬(u * x₁ = u * x₂ ∧ v * y₁ = W.toAffine.negY (u * x₂) (v * y₂)) := by
      rintro ⟨e1, e2⟩
      apply hxy
      refine ⟨mul_left_cancel₀ hu e1, ?_⟩
      simp only [Affine.negY, h1, h3] at e2 ⊢
      apply mul_left_cancel₀ hv0; linear_combination e2
    rw [Affine.Point.add_some hxy]
    show _ = Affine.Point.some _ _ (hns _ _ h₁) + Affine.Point.some _ _ (hns _ _ h₂)
    rw [Affine.Point.add_some hxy']
    simp only [scaleFun, Affine.Point.some.injEq]
    rw [slope_scale W hu hv h1 h2 h3 h4, addX_scale W hu hv h1 h2,
      addY_scale W hu hv h1 h2 h3]
    exact ⟨rfl, rfl⟩

/-- The additive map induced by a scaling `(x, y) ↦ (ux, vy)`. -/
noncomputable def scaleHom (W : WeierstrassCurve K) {u v : K} (hu : u ≠ 0) (hv : v ^ 2 = u ^ 3)
    (h1 : W.a₁ = 0) (h2 : W.a₂ = 0) (h3 : W.a₃ = 0) (h4 : W.a₄ * u ^ 3 = W.a₄ * u)
    (hns : ∀ x y, W.toAffine.Nonsingular x y → W.toAffine.Nonsingular (u * x) (v * y)) :
    W.toAffine.Point →+ W.toAffine.Point where
  toFun := scaleFun W u v hns
  map_zero' := rfl
  map_add' := scaleFun_add W hu hv h1 h2 h3 h4 hns

/-- `y² = x³ + Ax`. -/
def curveA (A : K) : WeierstrassCurve K := ⟨0, 0, 0, A, 0⟩

/-- `y² = x³ + B`. -/
def curveB (B : K) : WeierstrassCurve K := ⟨0, 0, 0, 0, B⟩

lemma nsA (A : K) {i : K} (hi : i ^ 2 = -1) (x y : K) (h : (curveA A).toAffine.Nonsingular x y) :
    (curveA A).toAffine.Nonsingular (-1 * x) (i * y) := by
  rw [Affine.nonsingular_iff] at h ⊢
  obtain ⟨he, hd⟩ := h
  simp only [curveA, Affine.equation_iff] at he hd ⊢
  refine ⟨by linear_combination y ^ 2 * hi - he, ?_⟩
  rcases hd with hd | hd
  · left; intro e; apply hd; linear_combination e
  · right; intro e; apply hd; linear_combination (-i) * e + (2 * y) * hi

/-- **Hardy–Wright §25.2.** `(x, y) ↦ (-x, iy)` on `y² = x³ + Ax`, `i² = -1`, as an additive map of
the group of points. -/
noncomputable def cmI (A : K) {i : K} (hi : i ^ 2 = -1) :
    (curveA A).toAffine.Point →+ (curveA A).toAffine.Point :=
  scaleHom (curveA A) (u := -1) (v := i) (by norm_num) (by rw [hi]; norm_num) rfl rfl rfl
    (by show A * (-1) ^ 3 = A * (-1); ring) (nsA A hi)

@[kb "hardywright2008" "Section 25.2, p. 575"]
theorem cmI_some (A : K) {i : K} (hi : i ^ 2 = -1) {x y : K}
    (h : (curveA A).toAffine.Nonsingular x y) :
    ∃ h' : (curveA A).toAffine.Nonsingular (-x) (i * y),
      cmI A hi (Affine.Point.some x y h) = Affine.Point.some (-x) (i * y) h' := by
  have h0 := nsA A hi x y h
  rw [neg_one_mul] at h0
  exact ⟨h0, by
    show Affine.Point.some _ _ _ = _
    simp only [Affine.Point.some.injEq, neg_one_mul]⟩

/-- `[i]² = -1`. -/
@[kb "hardywright2008" "Section 25.2, p. 575"]
theorem cmI_cmI (A : K) {i : K} (hi : i ^ 2 = -1) (P : (curveA A).toAffine.Point) :
    cmI A hi (cmI A hi P) = -P := by
  rcases P with _ | @⟨x, y, h⟩
  · show cmI A hi (cmI A hi 0) = -0
    rw [map_zero, map_zero, neg_zero]
  · obtain ⟨h1, e1⟩ := cmI_some A hi h
    obtain ⟨h2, e2⟩ := cmI_some A hi h1
    rw [e1, e2, Affine.Point.neg_some]
    rw [Affine.Point.some.injEq]
    refine ⟨neg_neg x, ?_⟩
    simp only [Affine.negY, curveA]
    linear_combination y * hi

lemma rho_ne_zero {ρ : K} (hρ : ρ ^ 2 + ρ + 1 = 0) : ρ ≠ 0 := by
  rintro rfl; simp at hρ

lemma nsB (B : K) {ρ : K} (hρ : ρ ^ 2 + ρ + 1 = 0) (x y : K)
    (h : (curveB B).toAffine.Nonsingular x y) :
    (curveB B).toAffine.Nonsingular (ρ * x) (1 * y) := by
  rw [Affine.nonsingular_iff] at h ⊢
  obtain ⟨he, hd⟩ := h
  simp only [curveB, Affine.equation_iff] at he hd ⊢
  refine ⟨by linear_combination he + (-(x ^ 3 * (ρ - 1))) * hρ, ?_⟩
  rcases hd with hd | hd
  · left; intro e; apply hd
    have h3 : ρ ^ 2 * (3 * x ^ 2) = 0 := by linear_combination (-1) * e
    have := (mul_eq_zero.1 h3).resolve_left (pow_ne_zero 2 (rho_ne_zero hρ))
    linear_combination (-1) * this
  · right; intro e; apply hd; linear_combination e

/-- **Hardy–Wright §25.2.** `(x, y) ↦ (ρx, y)` on `y² = x³ + B`, `ρ² + ρ + 1 = 0`, as an
additive map of the group of points. -/
noncomputable def cmRho (B : K) {ρ : K} (hρ : ρ ^ 2 + ρ + 1 = 0) :
    (curveB B).toAffine.Point →+ (curveB B).toAffine.Point :=
  scaleHom (curveB B) (u := ρ) (v := 1) (rho_ne_zero hρ)
    (by linear_combination (-(ρ - 1)) * hρ) rfl rfl rfl
    (by show (0 : K) * ρ ^ 3 = 0 * ρ; ring) (nsB B hρ)

@[kb "hardywright2008" "Section 25.2, p. 575"]
theorem cmRho_some (B : K) {ρ : K} (hρ : ρ ^ 2 + ρ + 1 = 0) {x y : K}
    (h : (curveB B).toAffine.Nonsingular x y) :
    ∃ h' : (curveB B).toAffine.Nonsingular (ρ * x) y,
      cmRho B hρ (Affine.Point.some x y h) = Affine.Point.some (ρ * x) y h' := by
  have h0 := nsB B hρ x y h
  rw [one_mul] at h0
  exact ⟨h0, by
    show Affine.Point.some _ _ _ = _
    simp only [Affine.Point.some.injEq, one_mul]⟩

/-- `[ρ]² + [ρ] + 1 = 0`. -/
@[kb "hardywright2008" "Section 25.2, p. 575"]
theorem cmRho_cmRho (B : K) {ρ : K} (hρ : ρ ^ 2 + ρ + 1 = 0) (P : (curveB B).toAffine.Point) :
    cmRho B hρ (cmRho B hρ P) + cmRho B hρ P + P = 0 := by
  rcases P with _ | @⟨x, y, h⟩
  · show cmRho B hρ (cmRho B hρ 0) + cmRho B hρ 0 + 0 = 0
    rw [map_zero, map_zero, add_zero, add_zero]
  · obtain ⟨h1, e1⟩ := cmRho_some B hρ h
    obtain ⟨h2, e2⟩ := cmRho_some B hρ h1
    rw [e1, e2]
    have hρ0 := rho_ne_zero hρ
    have hnon : ρ * (ρ * x) = ρ * x → 3 * x ^ 2 = 0 := by
      intro e
      have : ρ * x * (ρ - 1) = 0 := by linear_combination e
      rcases mul_eq_zero.1 this with h0 | h0
      · have : x = 0 := (mul_eq_zero.1 h0).resolve_left hρ0
        rw [this]; ring
      · have : ρ = 1 := by linear_combination h0
        subst this
        have : (3 : K) = 0 := by linear_combination hρ
        rw [this]; ring
    have hns : ¬(ρ * (ρ * x) = ρ * x ∧ y = (curveB B).toAffine.negY (ρ * x) y) := by
      rintro ⟨e, e2⟩
      have h3 := hnon e
      have hy : 2 * y = 0 := by
        simp only [Affine.negY, curveB] at e2; linear_combination e2
      have := (Affine.nonsingular_iff' _ _).1 h |>.2
      simp only [curveB] at this
      rcases this with h4 | h4
      · apply h4; linear_combination (-1) * h3
      · apply h4; linear_combination hy
    have key : Affine.Point.some _ _ h2 + Affine.Point.some _ _ h1 =
        -Affine.Point.some x y h := by
      rw [Affine.Point.add_some hns, Affine.Point.neg_some]
      have hs : (curveB B).toAffine.slope (ρ * (ρ * x)) (ρ * x) y y = 0 := by
        by_cases hx : ρ * (ρ * x) = ρ * x
        · by_cases hy : y = (curveB B).toAffine.negY (ρ * x) y
          · exact Affine.slope_of_Y_eq hx hy
          · rw [Affine.slope_of_Y_ne hx hy]
            have := hnon hx
            have e : 3 * (ρ * (ρ * x)) ^ 2 + 2 * (curveB B).a₂ * (ρ * (ρ * x)) +
                (curveB B).a₄ - (curveB B).a₁ * y = 0 := by
              show 3 * (ρ * (ρ * x)) ^ 2 + 2 * 0 * (ρ * (ρ * x)) + 0 - 0 * y = 0
              linear_combination ρ ^ 4 * this
            rw [e, zero_div]
        · rw [Affine.slope_of_X_ne hx]; simp
      simp only [Affine.Point.some.injEq]
      rw [hs]
      constructor
      · simp only [Affine.addX, curveB]; linear_combination (-x) * hρ
      · simp only [Affine.addY, Affine.negY, Affine.negAddY, Affine.addX, curveB]
        ring
    rw [key, neg_add_cancel]

end CM

/-! ### Theorem 465 -/

open NTKB.IrelandRosen.CM in
/-- **Hardy–Wright, Theorem 465.** For `A ≠ 0`, `(X, Y) ↦ (12A/(X + Y), 36A(X - Y)/(X + Y))` is a
bijection from the rational solutions of `X³ + Y³ = A` onto the rational solutions of
`y² = x³ - 432A²` with `x ≠ 0`; the inverse is `(x, y) ↦ ((36A + y)/(6x), (36A - y)/(6x))`. -/
@[kb "hardywright2008" "Thm 465, p. 576"]
noncomputable def cubesEquivMordell {A : ℤ} (hA : A ≠ 0) :
    {p : ℚ × ℚ // p.1 ^ 3 + p.2 ^ 3 = A} ≃
      {q : ℚ × ℚ // q.1 ≠ 0 ∧ q.2 ^ 2 = q.1 ^ 3 - 432 * (A : ℚ) ^ 2} where
  toFun p := ⟨cubesToMordell A p.1, by
    have hs := add_ne_zero_of_cubes hA p.2
    refine ⟨?_, ?_⟩
    · simp only [cubesToMordell]
      exact div_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast hA)) hs
    · have := cubesToMordell_mem hA p.2
      push_cast at this
      linarith⟩
  invFun q := ⟨mordellToCubes A q.1, mordellToCubes_mem q.2.1 (by
    have := q.2.2; push_cast; linarith)⟩
  left_inv p := Subtype.ext (mordellToCubes_cubesToMordell hA p.2)
  right_inv q := Subtype.ext (cubesToMordell_mordellToCubes hA q.2.1)

open NTKB.IrelandRosen.CM in
theorem cubesEquivMordell_apply {A : ℤ} (hA : A ≠ 0) (p : {p : ℚ × ℚ // p.1 ^ 3 + p.2 ^ 3 = A}) :
    (cubesEquivMordell hA p : ℚ × ℚ) = cubesToMordell A p := rfl

end NTKB.HardyWright
