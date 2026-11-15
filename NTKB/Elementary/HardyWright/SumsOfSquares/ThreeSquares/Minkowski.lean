/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Minkowski's theorem for ternary ellipsoids

A positive definite real symmetric `3 × 3` matrix `G` with `det G < π²/36` takes a value `< 1` at a
nonzero integral vector: the ellipsoid `xᵀ G x < 1` has volume `(4π/3)/√(det G) > 8`, and Minkowski's
convex body theorem (Mathlib's `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`)
applies to the lattice `ℤ³`. This is the only analytic input of the proof of the three-square
theorem in this directory.
-/

open MeasureTheory Matrix Real Module

namespace NTKB.HardyWright.ThreeSquares

/-- The quadratic form of a `3 × 3` matrix, written out. -/
def qf (G : Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 3 → ℝ) : ℝ :=
  ∑ i, ∑ j, G i j * x i * x j

lemma qf_eq_dotProduct (G : Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 3 → ℝ) :
    qf G x = x ⬝ᵥ (G *ᵥ x) := by
  simp only [qf, dotProduct, mulVec, Fin.sum_univ_three]; ring

/-- The Euclidean unit ball of `ℝ³`, written with coordinates. -/
def ball3 : Set (Fin 3 → ℝ) := {y | y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 < 1}

lemma convex_ball3 : Convex ℝ ball3 := by
  intro y hy z hz a b ha hb hab
  simp only [ball3, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
  have hb' : b = 1 - a := by linarith
  subst hb'
  set Y := y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2
  set Z := z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2
  have key : (a * y 0 + (1 - a) * z 0) ^ 2 + (a * y 1 + (1 - a) * z 1) ^ 2 +
      (a * y 2 + (1 - a) * z 2) ^ 2 = a * Y + (1 - a) * Z -
        a * (1 - a) * ((y 0 - z 0) ^ 2 + (y 1 - z 1) ^ 2 + (y 2 - z 2) ^ 2) := by
    simp only [Y, Z]; ring
  have hS : 0 ≤ a * (1 - a) * ((y 0 - z 0) ^ 2 + (y 1 - z 1) ^ 2 + (y 2 - z 2) ^ 2) :=
    mul_nonneg (mul_nonneg ha hb) (by positivity)
  have hlt : a * Y + (1 - a) * Z < 1 := by
    rcases le_total Y Z with h | h
    · nlinarith [mul_le_mul_of_nonneg_left h ha]
    · nlinarith [mul_le_mul_of_nonneg_left h hb]
  rw [key]; linarith

lemma volume_ball3 : volume ball3 = ENNReal.ofReal (4 * π / 3) := by
  have h := MeasureTheory.volume_sum_rpow_lt_one (Fin 3) (p := 2) (by norm_num)
  have hset : {x : Fin 3 → ℝ | ∑ i, |x i| ^ (2 : ℝ) < 1} = ball3 := by
    ext y
    simp only [Set.mem_ofPred_eq, ball3, Fin.sum_univ_three, Real.rpow_two, sq_abs]
  rw [hset] at h
  rw [h]
  congr 1
  have h32 : Gamma (1 / 2 + 1) = √π / 2 := by
    rw [Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]; ring
  have h52 : Gamma ((3 : ℕ) / 2 + 1) = 3 * √π / 4 := by
    have : ((3 : ℕ) : ℝ) / 2 + 1 = (1 / 2 + 1) + 1 := by norm_num
    rw [this, Real.Gamma_add_one (by norm_num), h32]; ring
  simp only [Fintype.card_fin]
  rw [show ((3 : ℕ) : ℝ) / 2 + 1 = ((3 : ℕ) : ℝ) / 2 + 1 from rfl]
  rw [show (1 : ℝ) / 2 + 1 = 1 / 2 + 1 from rfl, h32]
  rw [show ((3 : ℕ) : ℝ) / 2 + 1 = (3 : ℕ) / 2 + 1 from rfl] at h52
  rw [h52]
  have hs : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  have hs2 : √π ^ 2 = π := Real.sq_sqrt Real.pi_pos.le
  field_simp
  exact hs2

/-- **Minkowski's theorem for a ternary ellipsoid.** -/
theorem exists_ne_zero_qf_lt_one (G : Matrix (Fin 3) (Fin 3) ℝ) (hG : G.IsSymm)
    (hpos : ∀ x : Fin 3 → ℝ, x ≠ 0 → 0 < qf G x) (hdet : G.det < π ^ 2 / 36) :
    ∃ z : Fin 3 → ℤ, z ≠ 0 ∧ qf G (fun i => (z i : ℝ)) < 1 := by
  have h10 : G 1 0 = G 0 1 := by
    have := congrFun (congrFun hG 0) 1; simpa [Matrix.transpose_apply] using this
  have h20 : G 2 0 = G 0 2 := by
    have := congrFun (congrFun hG 0) 2; simpa [Matrix.transpose_apply] using this
  have h21 : G 2 1 = G 1 2 := by
    have := congrFun (congrFun hG 1) 2; simpa [Matrix.transpose_apply] using this
  set a := G 0 0
  set b := G 0 1
  set c := G 0 2
  set d := G 1 1
  set e := G 1 2
  set f := G 2 2
  have hqf : ∀ x : Fin 3 → ℝ, qf G x = a * x 0 ^ 2 + d * x 1 ^ 2 + f * x 2 ^ 2 +
      2 * b * x 0 * x 1 + 2 * c * x 0 * x 2 + 2 * e * x 1 * x 2 := by
    intro x
    simp only [qf, Fin.sum_univ_three, h10, h20, h21]; ring
  have hD : G.det = a * d * f + 2 * b * c * e - a * e ^ 2 - d * c ^ 2 - f * b ^ 2 := by
    rw [Matrix.det_fin_three, h10, h20, h21]; ring
  -- the leading minors are positive
  have ha : 0 < a := by
    have := hpos ![1, 0, 0] (by intro h; simpa using congrFun h 0)
    rw [hqf] at this; simpa using this
  set m := a * d - b ^ 2 with hm
  have hm0 : 0 < m := by
    have := hpos ![b, -a, 0] (by intro h; have := congrFun h 1; simp at this; linarith)
    rw [hqf] at this
    simp at this
    nlinarith
  set D := G.det with hDdef
  have hD0 : 0 < D := by
    have := hpos ![b * e - c * d, b * c - a * e, m]
      (by intro h; have := congrFun h 2; simp at this; linarith)
    rw [hqf] at this
    simp at this
    have key : a * d * f + 2 * b * c * e - a * e ^ 2 - d * c ^ 2 - f * b ^ 2 > 0 := by
      have hm' : m ≠ 0 := hm0.ne'
      nlinarith [this]
    rw [hD]; linarith
  -- the triangular map `T` with `|T x|² = xᵀ G x`
  set r1 := √a
  set r2 := √(m / a)
  set r3 := √(D / m)
  let M : Matrix (Fin 3) (Fin 3) ℝ :=
    !![r1, r1 * (b / a), r1 * (c / a); 0, r2, r2 * ((a * e - b * c) / m); 0, 0, r3]
  let T : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) := Matrix.toLin' M
  have hr1 : r1 ^ 2 = a := Real.sq_sqrt ha.le
  have hr2 : r2 ^ 2 = m / a := Real.sq_sqrt (div_pos hm0 ha).le
  have hr3 : r3 ^ 2 = D / m := Real.sq_sqrt (div_pos hD0 hm0).le
  have hT : ∀ x, (T x) 0 ^ 2 + (T x) 1 ^ 2 + (T x) 2 ^ 2 = qf G x := by
    intro x
    simp only [T, M, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
      Matrix.tail_cons, Matrix.head_fin_const]
    rw [hqf]
    have e1 : (r1 * x 0 + r1 * (b / a) * x 1 + r1 * (c / a) * x 2) ^ 2 =
        r1 ^ 2 * (x 0 + b / a * x 1 + c / a * x 2) ^ 2 := by ring
    have e2 : (0 * x 0 + r2 * x 1 + r2 * ((a * e - b * c) / m) * x 2) ^ 2 =
        r2 ^ 2 * (x 1 + (a * e - b * c) / m * x 2) ^ 2 := by ring
    have e3 : (0 * x 0 + 0 * x 1 + r3 * x 2) ^ 2 = r3 ^ 2 * x 2 ^ 2 := by ring
    rw [e1, e2, e3, hr1, hr2, hr3, hD]
    field_simp
    ring
  have hdetT : LinearMap.det T = r1 * r2 * r3 := by
    simp only [T, LinearMap.det_toLin', M, Matrix.det_fin_three]
    simp
  have hprod : r1 * r2 * r3 = √D := by
    simp only [r1, r2, r3]
    rw [← Real.sqrt_mul ha.le, ← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  have hsqrtD : √D < π / 6 := by
    rw [Real.sqrt_lt' (by positivity)]
    calc D < π ^ 2 / 36 := hdet
      _ = (π / 6) ^ 2 := by ring
  have hdet0 : LinearMap.det T ≠ 0 := by
    rw [hdetT, hprod]; exact (Real.sqrt_pos.mpr hD0).ne'
  -- the ellipsoid
  set K : Set (Fin 3 → ℝ) := T ⁻¹' ball3 with hK
  have hKmem : ∀ x, x ∈ K ↔ qf G x < 1 := by
    intro x; simp only [hK, Set.mem_preimage, ball3, Set.mem_ofPred_eq, hT]
  have hsymm : ∀ x ∈ K, -x ∈ K := by
    intro x hx
    rw [hKmem] at hx ⊢
    simpa [qf] using hx
  have hconv : Convex ℝ K := convex_ball3.linear_preimage T
  -- the lattice `ℤ³`
  let bas := Pi.basisFun ℝ (Fin 3)
  have hfund := ZSpan.isAddFundamentalDomain' bas volume
  have hvolF : volume (ZSpan.fundamentalDomain bas) = 1 := by
    rw [ZSpan.volume_fundamentalDomain]
    have : (Matrix.of bas) = 1 := by
      ext i j; simp [bas, Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [this, Matrix.det_one]; simp
  have hvolK : volume (ZSpan.fundamentalDomain bas) * 2 ^ finrank ℝ (Fin 3 → ℝ) < volume K := by
    rw [hvolF, hK, Measure.addHaar_preimage_linearMap _ hdet0, volume_ball3, hdetT, hprod,
      Module.finrank_fin_fun, one_mul, ← ENNReal.ofReal_mul (abs_nonneg _)]
    have hpos' : 0 < √D := Real.sqrt_pos.mpr hD0
    rw [abs_inv, abs_of_pos hpos']
    rw [show (2 : ENNReal) ^ 3 = ENNReal.ofReal 8 by norm_num]
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    rw [inv_mul_eq_div, lt_div_iff₀ hpos']
    nlinarith [Real.pi_gt_three]
  have : Countable (Submodule.span ℤ (Set.range bas)).toAddSubgroup := by
    change Countable (Submodule.span ℤ (Set.range bas))
    infer_instance
  obtain ⟨⟨x, hxL⟩, hx0, hxK⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure hfund hsymm hconv hvolK
  -- `x` has integer coordinates
  have hint : ∀ i, ∃ n : ℤ, (n : ℝ) = x i := by
    intro i
    have := (bas.mem_span_iff_repr_mem ℤ x).mp hxL i
    simpa [bas] using this
  choose z hz using hint
  refine ⟨z, ?_, ?_⟩
  · intro h
    apply hx0
    ext i
    simp [← hz i, h]
  · have : (fun i => (z i : ℝ)) = x := funext hz
    rw [this, ← hKmem]
    exact hxK

end NTKB.HardyWright.ThreeSquares
