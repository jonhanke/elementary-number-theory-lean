/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import NTKB.Elementary.HardyWright.SumsOfSquares.ThreeSquares.Minkowski

/-!
# Positive definite ternary forms of determinant one

Every value of a positive definite integral ternary quadratic form of determinant `1` is a sum of
three squares (Gauss; this is the reduction step of Dirichlet's proof of the three-square theorem).

Instead of Gauss's reduction theory the proof uses Minkowski's theorem twice
(`exists_ne_zero_qf_lt_one`): the ellipsoid `f(x) < 2` (determinant `1/8`) gives `v₁` with
`f(v₁) = 1`; the ellipsoid `f(x) + B(v₁, x)² < 2` (determinant `1/4`) gives `v₂` with `f(v₂) = 1` and
`B(v₁, v₂) = 0`. The third vector is the cross product `n = Av₁ × Av₂`: then `An = v₁ × v₂` (since
`det A = 1`), `B(vᵢ, n) = 0` and `f(n) = 1` by the Binet–Cauchy identity, and
`f(x) = B(v₁, x)² + B(v₂, x)² + B(n, x)²` because `v₁, v₂, n` is an orthonormal basis for `B`.
-/

open Matrix Real

namespace NTKB.HardyWright.ThreeSquares

variable {A : Matrix (Fin 3) (Fin 3) ℤ}

/-- The integral quadratic form `xᵀ A x`. -/
def qZ (A : Matrix (Fin 3) (Fin 3) ℤ) (x : Fin 3 → ℤ) : ℤ := x ⬝ᵥ (A *ᵥ x)

/-- Cast of an integral vector. -/
def castV (x : Fin 3 → ℤ) : Fin 3 → ℝ := fun i => (x i : ℝ)

lemma qf_map_cast (A : Matrix (Fin 3) (Fin 3) ℤ) (x : Fin 3 → ℤ) :
    qf (A.map (Int.cast : ℤ → ℝ)) (castV x) = (qZ A x : ℝ) := by
  simp only [qf, qZ, castV, dotProduct, mulVec, Fin.sum_univ_three, Matrix.map_apply]
  push_cast; ring

lemma mulVec_dot_symm (hA : A.IsSymm) (v w : Fin 3 → ℤ) : (A *ᵥ v) ⬝ᵥ w = v ⬝ᵥ (A *ᵥ w) := by
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hA.eq, dotProduct_comm]

/-- `Aᵀ (Av × Aw) = det A • (v × w)`, written for symmetric `A`. -/
lemma mulVec_cross_mulVec (hA : A.IsSymm) (v w : Fin 3 → ℤ) :
    A *ᵥ ((A *ᵥ v) ⨯₃ (A *ᵥ w)) = A.det • (v ⨯₃ w) := by
  have h10 : A 1 0 = A 0 1 := by
    have := congrFun (congrFun hA 0) 1; simpa [Matrix.transpose_apply] using this
  have h20 : A 2 0 = A 0 2 := by
    have := congrFun (congrFun hA 0) 2; simpa [Matrix.transpose_apply] using this
  have h21 : A 2 1 = A 1 2 := by
    have := congrFun (congrFun hA 1) 2; simpa [Matrix.transpose_apply] using this
  ext i
  fin_cases i <;>
  · simp only [cross_apply, mulVec, dotProduct, Fin.sum_univ_three, Matrix.det_fin_three,
      Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, h10, h20, h21]
    ring

/-- The matrix determinant lemma in the case used: `det (A + (Av)(Av)ᵀ) = det A · (1 + vᵀAv)`. -/
lemma det_add_vecMulVec (hA : A.IsSymm) (v : Fin 3 → ℤ) :
    (A + vecMulVec (A *ᵥ v) (A *ᵥ v)).det = A.det * (1 + qZ A v) := by
  have h10 : A 1 0 = A 0 1 := by
    have := congrFun (congrFun hA 0) 1; simpa [Matrix.transpose_apply] using this
  have h20 : A 2 0 = A 0 2 := by
    have := congrFun (congrFun hA 0) 2; simpa [Matrix.transpose_apply] using this
  have h21 : A 2 1 = A 1 2 := by
    have := congrFun (congrFun hA 1) 2; simpa [Matrix.transpose_apply] using this
  simp only [Matrix.det_fin_three, qZ, Matrix.add_apply, vecMulVec_apply, mulVec, dotProduct,
    Fin.sum_univ_three, h10, h20, h21]
  ring

lemma qZ_nonneg (hpos : ∀ x : Fin 3 → ℝ, x ≠ 0 → 0 < qf (A.map (Int.cast : ℤ → ℝ)) x)
    (x : Fin 3 → ℤ) : 0 ≤ qZ A x := by
  by_cases hx : x = 0
  · simp [qZ, hx]
  · have hc : castV x ≠ 0 := by
      intro h; apply hx; ext i; have := congrFun h i; simpa [castV] using this
    have := hpos _ hc
    rw [qf_map_cast] at this
    exact_mod_cast this.le

lemma qZ_pos (hpos : ∀ x : Fin 3 → ℝ, x ≠ 0 → 0 < qf (A.map (Int.cast : ℤ → ℝ)) x)
    {x : Fin 3 → ℤ} (hx : x ≠ 0) : 0 < qZ A x := by
  have hc : castV x ≠ 0 := by
    intro h; apply hx; ext i; have := congrFun h i; simpa [castV] using this
  have := hpos _ hc
  rw [qf_map_cast] at this
  exact_mod_cast this

lemma qZ_sub_smul (hA : A.IsSymm) (x v : Fin 3 → ℤ) (t : ℤ) :
    qZ A (x - t • v) = qZ A x - 2 * t * ((A *ᵥ v) ⬝ᵥ x) + t ^ 2 * qZ A v := by
  have hs := mulVec_dot_symm hA v x
  simp only [qZ] at *
  rw [mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, dotProduct_sub, smul_dotProduct,
    dotProduct_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
    smul_eq_mul]
  rw [hs]
  have : x ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (A *ᵥ x) := by
    rw [← mulVec_dot_symm hA x v, dotProduct_comm]
  rw [this]; ring

/-- **Determinant-one ternary forms are sums of three squares.** -/
theorem exists_sq_add_sq_add_sq_of_det_eq_one (hA : A.IsSymm)
    (hpos : ∀ x : Fin 3 → ℝ, x ≠ 0 → 0 < qf (A.map (Int.cast : ℤ → ℝ)) x) (hdet : A.det = 1)
    (x : Fin 3 → ℤ) : ∃ a b c : ℤ, qZ A x = a ^ 2 + b ^ 2 + c ^ 2 := by
  set AR := A.map (Int.cast : ℤ → ℝ) with hAR
  have hARs : AR.IsSymm := hA.map _
  have hdetR : AR.det = 1 := by
    simpa [hdet, hAR] using ((Int.castRingHom ℝ).map_det A).symm
  have hpi : (1 : ℝ) / 4 < π ^ 2 / 36 := by nlinarith [Real.pi_gt_three]
  -- Step 1: a vector `v₁` with `f(v₁) = 1`
  obtain ⟨v1, hv10, hv1lt⟩ := exists_ne_zero_qf_lt_one ((1 / 2 : ℝ) • AR)
    (by simp only [Matrix.IsSymm, Matrix.transpose_smul, hARs.eq])
    (by
      intro y hy
      have := hpos y hy
      simp only [qf, Matrix.smul_apply, smul_eq_mul] at this ⊢
      have e : ∑ i, ∑ j, 1 / 2 * AR i j * y i * y j = 1 / 2 * ∑ i, ∑ j, AR i j * y i * y j := by
        simp only [Finset.mul_sum]; congr 1; ext i; congr 1; ext j; ring
      rw [e]; positivity)
    (by rw [Matrix.det_smul, hdetR]; norm_num; linarith)
  have hq1 : qZ A v1 = 1 := by
    have e : qf ((1 / 2 : ℝ) • AR) (fun i => (v1 i : ℝ)) = qZ A v1 / 2 := by
      have := qf_map_cast A v1
      simp only [qf, Matrix.smul_apply, smul_eq_mul, castV] at this ⊢
      rw [← this, Finset.sum_div]; congr 1; ext i; rw [Finset.sum_div]; congr 1; ext j; ring
    rw [e] at hv1lt
    have h1 := qZ_pos hpos hv10
    have h2 : qZ A v1 < 2 := by exact_mod_cast (by linarith : (qZ A v1 : ℝ) < 2)
    omega
  set u1 := A *ᵥ v1 with hu1
  -- Step 2: a vector `v₂` with `f(v₂) = 1` and `B(v₁, v₂) = 0`
  set G2 : Matrix (Fin 3) (Fin 3) ℤ := A + vecMulVec u1 u1 with hG2
  have hG2s : G2.IsSymm := by
    simp only [hG2, Matrix.IsSymm, Matrix.transpose_add, hA.eq, transpose_vecMulVec]
  have hG2det : G2.det = 2 := by
    rw [hG2, hu1, det_add_vecMulVec hA, hdet, hq1]; norm_num
  have hqG2 : ∀ y : Fin 3 → ℤ, qZ G2 y = qZ A y + (u1 ⬝ᵥ y) ^ 2 := by
    intro y
    simp only [qZ, hG2, add_mulVec, dotProduct_add]
    congr 1
    simp only [dotProduct, mulVec, vecMulVec_apply, Fin.sum_univ_three]; ring
  set G2R := G2.map (Int.cast : ℤ → ℝ) with hG2R
  have hG2Rs : G2R.IsSymm := hG2s.map _
  have hG2Rdet : G2R.det = 2 := by
    simpa [hG2det, hG2R] using ((Int.castRingHom ℝ).map_det G2).symm
  have hqfG2 : ∀ y : Fin 3 → ℝ, qf G2R y = qf AR y + (∑ i, (u1 i : ℝ) * y i) ^ 2 := by
    intro y
    simp only [qf, hG2R, hAR, hG2, Matrix.map_apply, Matrix.add_apply, vecMulVec_apply,
      Fin.sum_univ_three]
    push_cast; ring
  obtain ⟨v2, hv20, hv2lt⟩ := exists_ne_zero_qf_lt_one ((1 / 2 : ℝ) • G2R)
    (by simp only [Matrix.IsSymm, Matrix.transpose_smul, hG2Rs.eq])
    (by
      intro y hy
      have h1 := hpos y hy
      have e : qf ((1 / 2 : ℝ) • G2R) y = qf G2R y / 2 := by
        simp only [qf, Matrix.smul_apply, smul_eq_mul]
        rw [Finset.sum_div]; congr 1; ext i; rw [Finset.sum_div]; congr 1; ext j; ring
      rw [e, hqfG2]; positivity)
    (by rw [Matrix.det_smul, hG2Rdet]; norm_num; linarith)
  have hv2 : qZ A v2 + (u1 ⬝ᵥ v2) ^ 2 < 2 := by
    have e : qf ((1 / 2 : ℝ) • G2R) (fun i => (v2 i : ℝ)) = qZ G2 v2 / 2 := by
      have := qf_map_cast G2 v2
      simp only [qf, Matrix.smul_apply, smul_eq_mul, castV, hG2R] at this ⊢
      rw [← this, Finset.sum_div]; congr 1; ext i; rw [Finset.sum_div]; congr 1; ext j; ring
    rw [e] at hv2lt
    rw [← hqG2]
    exact_mod_cast (by linarith : (qZ G2 v2 : ℝ) < 2)
  -- Cauchy–Schwarz: `B(v₁, v₂)² ≤ f(v₂)`
  have hCS : (u1 ⬝ᵥ v2) ^ 2 ≤ qZ A v2 := by
    have := qZ_nonneg hpos (v2 - (u1 ⬝ᵥ v2) • v1)
    rw [qZ_sub_smul hA, hq1, ← hu1] at this
    nlinarith
  have hpos2 := qZ_pos hpos hv20
  have hl2 : u1 ⬝ᵥ v2 = 0 := by
    by_contra h
    have : 1 ≤ (u1 ⬝ᵥ v2) ^ 2 := by
      have := pow_pos (abs_pos.mpr h) 2
      rw [sq_abs] at this; omega
    omega
  have hq2 : qZ A v2 = 1 := by rw [hl2] at hv2; omega
  set u2 := A *ᵥ v2 with hu2
  -- Step 3: the cross product
  set n := u1 ⨯₃ u2 with hn
  have hAn : A *ᵥ n = v1 ⨯₃ v2 := by
    rw [hn, hu1, hu2, mulVec_cross_mulVec hA, hdet, one_smul]
  have hu1v1 : u1 ⬝ᵥ v1 = 1 := by rw [hu1, mulVec_dot_symm hA]; exact hq1
  have hu2v2 : u2 ⬝ᵥ v2 = 1 := by rw [hu2, mulVec_dot_symm hA]; exact hq2
  have hu2v1 : u2 ⬝ᵥ v1 = 0 := by
    rw [hu2, mulVec_dot_symm hA, dotProduct_comm, ← hu1]; exact hl2
  have hqn : qZ A n = 1 := by
    simp only [qZ]
    rw [hAn, hn, cross_dot_cross, hu1v1, hu2v2, hl2, hu2v1]; ring
  -- Step 4: Parseval
  set l1 := u1 ⬝ᵥ x
  set l2 := u2 ⬝ᵥ x
  set l3 := (A *ᵥ n) ⬝ᵥ x
  refine ⟨l1, l2, l3, ?_⟩
  set y := x - l1 • v1 - l2 • v2 - l3 • n with hy
  have hBn1 : u1 ⬝ᵥ n = 0 := by rw [hn]; exact dot_self_cross u1 u2
  have hBn2 : u2 ⬝ᵥ n = 0 := by rw [hn]; exact dot_cross_self u1 u2
  have hn1 : (A *ᵥ n) ⬝ᵥ v1 = 0 := by
    rw [mulVec_dot_symm hA, ← hu1, dotProduct_comm]; exact hBn1
  have hn2 : (A *ᵥ n) ⬝ᵥ v2 = 0 := by
    rw [mulVec_dot_symm hA, ← hu2, dotProduct_comm]; exact hBn2
  have hnn : (A *ᵥ n) ⬝ᵥ n = 1 := by rw [mulVec_dot_symm hA]; exact hqn
  have hy1 : u1 ⬝ᵥ y = 0 := by
    simp only [hy, dotProduct_sub, dotProduct_smul, smul_eq_mul, hu1v1, hl2, hBn1]
    simp [l1]
  have hy2 : u2 ⬝ᵥ y = 0 := by
    simp only [hy, dotProduct_sub, dotProduct_smul, smul_eq_mul, hu2v2, hu2v1, hBn2]
    simp [l2]
  have hy3 : (A *ᵥ n) ⬝ᵥ y = 0 := by
    simp only [hy, dotProduct_sub, dotProduct_smul, smul_eq_mul, hn1, hn2, hnn]
    simp [l3]
  -- `y = 0`, since `u₁, u₂, An` are independent
  set W : Matrix (Fin 3) (Fin 3) ℤ := ![u1, u2, A *ᵥ n] with hW
  have hWdet : W.det = 1 := by
    rw [hW, ← triple_product_eq_det, triple_product_permutation, triple_product_permutation,
      ← hn]
    exact hnn
  have hWy : W *ᵥ y = 0 := by
    ext i
    fin_cases i
    · exact hy1
    · exact hy2
    · exact hy3
  have hy0 : y = 0 := Matrix.eq_zero_of_mulVec_eq_zero (by rw [hWdet]; norm_num) hWy
  have hx : x = l1 • v1 + l2 • v2 + l3 • n := by
    have : x - l1 • v1 - l2 • v2 - l3 • n = 0 := hy0
    rw [sub_eq_zero, sub_eq_iff_eq_add, sub_eq_iff_eq_add] at this
    rw [this]; abel
  -- expand `f(x)` in the orthonormal basis
  have hB : ∀ p q : Fin 3 → ℤ, p ⬝ᵥ (A *ᵥ q) = (A *ᵥ p) ⬝ᵥ q := fun p q =>
    (mulVec_dot_symm hA p q).symm
  have e1 : (A *ᵥ v1) ⬝ᵥ x = l1 := rfl
  have e2 : (A *ᵥ v2) ⬝ᵥ x = l2 := rfl
  calc qZ A x = x ⬝ᵥ (A *ᵥ x) := rfl
    _ = l1 * ((A *ᵥ v1) ⬝ᵥ x) + l2 * ((A *ᵥ v2) ⬝ᵥ x) + l3 * ((A *ᵥ n) ⬝ᵥ x) := by
        conv_lhs => rw [hx]
        rw [add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct, smul_dotProduct,
          ← hx, hB v1, hB v2, hB n]
        simp only [smul_eq_mul]
    _ = l1 ^ 2 + l2 ^ 2 + l3 ^ 2 := by rw [e1, e2]; ring

end NTKB.HardyWright.ThreeSquares
