/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Quaternion.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Star.Rat

/-!
# Hardy–Wright, § 20.6: the 24 unities (20.6.11)

The unities of the integral quaternions are exactly the `24` quaternions
`±1, ±i₁, ±i₂, ±i₃, ½(±1 ± i₁ ± i₂ ± i₃)` (`isUnit_iff_mem_unities`, `ncard_unities`).
They are listed through their doubled coordinates `2ε` (`unityCoords`).
-/

open Quaternion

namespace NTKB.HardyWright

/-- The doubled coordinates `2ε` of the `24` unities `±1, ±i₁, ±i₂, ±i₃, ½(±1 ± i₁ ± i₂ ± i₃)`. -/
def unityCoords : Finset (ℤ × ℤ × ℤ × ℤ) :=
  {(2, 0, 0, 0), (-2, 0, 0, 0), (0, 2, 0, 0), (0, -2, 0, 0),
   (0, 0, 2, 0), (0, 0, -2, 0), (0, 0, 0, 2), (0, 0, 0, -2),
   (1, 1, 1, 1), (1, 1, 1, -1), (1, 1, -1, 1), (1, 1, -1, -1),
   (1, -1, 1, 1), (1, -1, 1, -1), (1, -1, -1, 1), (1, -1, -1, -1),
   (-1, 1, 1, 1), (-1, 1, 1, -1), (-1, 1, -1, 1), (-1, 1, -1, -1),
   (-1, -1, 1, 1), (-1, -1, 1, -1), (-1, -1, -1, 1), (-1, -1, -1, -1)}

/-- The quaternion with coordinates `A/2`. -/
def halfQuat (A : ℤ × ℤ × ℤ × ℤ) : ℍ[ℚ] := ⟨A.1 / 2, A.2.1 / 2, A.2.2.1 / 2, A.2.2.2 / 2⟩

lemma halfQuat_injective : Function.Injective halfQuat := by
  rintro ⟨a0, a1, a2, a3⟩ ⟨b0, b1, b2, b3⟩ h
  simp only [halfQuat, QuaternionAlgebra.mk.injEq] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  have e : ∀ u v : ℤ, (u : ℚ) / 2 = v / 2 → u = v := fun u v huv => by
    have : (u : ℚ) = v := by linarith
    exact_mod_cast this
  simp [e _ _ h0, e _ _ h1, e _ _ h2, e _ _ h3]

/-- The set of the `24` unities (20.6.11), `quaternionUnities`. -/
def quaternionUnities : Set ℍ[ℚ] := halfQuat '' (unityCoords : Set (ℤ × ℤ × ℤ × ℤ))

/-- Every integral quaternion has doubled coordinates `A` of equal parity. -/
lemma exists_halfQuat (a : IntegralQuaternion) : ∃ A : ℤ × ℤ × ℤ × ℤ, (a : ℍ[ℚ]) = halfQuat A ∧
    A.2.1 % 2 = A.1 % 2 ∧ A.2.2.1 % 2 = A.1 % 2 ∧ A.2.2.2 % 2 = A.1 % 2 := by
  obtain ⟨k0, k1, k2, k3, h⟩ := a.2
  refine ⟨(k0, k0 + 2 * k1, k0 + 2 * k2, k0 + 2 * k3), ?_, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega⟩
  rw [h]; ext <;> simp [halfQuat] <;> ring

lemma normSq_halfQuat (A : ℤ × ℤ × ℤ × ℤ) :
    normSq (halfQuat A) = ((A.1 ^ 2 + A.2.1 ^ 2 + A.2.2.1 ^ 2 + A.2.2.2 ^ 2 : ℤ) : ℚ) / 4 := by
  rw [normSq_def']; simp only [halfQuat]; push_cast; ring

/-- The finite check behind (20.6.11): the solutions of `A₀² + A₁² + A₂² + A₃² = 4` in integers of
equal parity are the `24` doubled unities. -/
lemma mem_unityCoords_of_sum_sq : ∀ A ∈ (Finset.Icc (-2 : ℤ) 2 ×ˢ Finset.Icc (-2 : ℤ) 2 ×ˢ
    Finset.Icc (-2 : ℤ) 2 ×ˢ Finset.Icc (-2 : ℤ) 2),
    A.1 ^ 2 + A.2.1 ^ 2 + A.2.2.1 ^ 2 + A.2.2.2 ^ 2 = 4 → A.2.1 % 2 = A.1 % 2 →
      A.2.2.1 % 2 = A.1 % 2 → A.2.2.2 % 2 = A.1 % 2 → A ∈ unityCoords := by
  decide +kernel

lemma sum_sq_of_mem_unityCoords : ∀ A ∈ unityCoords, A.1 ^ 2 + A.2.1 ^ 2 + A.2.2.1 ^ 2 + A.2.2.2 ^ 2 = 4 := by
  decide +kernel

lemma unityCoords_card : unityCoords.card = 24 := by decide +kernel

/-- **(20.6.11)** (Hardy–Wright). The unities of the integral quaternions are exactly
`±1, ±i₁, ±i₂, ±i₃, ½(±1 ± i₁ ± i₂ ± i₃)`. -/
@[kb "hardywright2008" "Section 20.6, p. 422"]
theorem isUnit_iff_mem_unities (a : IntegralQuaternion) :
    IsUnit a ↔ (a : ℍ[ℚ]) ∈ quaternionUnities := by
  obtain ⟨A, hA, h1, h2, h3⟩ := exists_halfQuat a
  have hn : IsUnit a ↔ A.1 ^ 2 + A.2.1 ^ 2 + A.2.2.1 ^ 2 + A.2.2.2 ^ 2 = 4 := by
    rw [isUnit_iff_qnorm_eq_one, qnorm_eq_iff, hA, normSq_halfQuat]
    constructor
    · intro h
      have : ((A.1 ^ 2 + A.2.1 ^ 2 + A.2.2.1 ^ 2 + A.2.2.2 ^ 2 : ℤ) : ℚ) = ((4 : ℤ) : ℚ) := by
        push_cast at h ⊢; linarith
      exact_mod_cast this
    · intro h; rw [h]; norm_num
  rw [hn, hA, quaternionUnities, halfQuat_injective.mem_set_image, Finset.mem_coe]
  constructor
  · intro h
    have hb : ∀ t : ℤ, t ^ 2 ≤ 4 → t ∈ Finset.Icc (-2 : ℤ) 2 := fun t ht => by
      rw [Finset.mem_Icc]; constructor <;> nlinarith [sq_nonneg (t - 2), sq_nonneg (t + 2)]
    refine mem_unityCoords_of_sum_sq A ?_ h h1 h2 h3
    simp only [Finset.mem_product]
    refine ⟨hb _ ?_, hb _ ?_, hb _ ?_, hb _ ?_⟩ <;> nlinarith [sq_nonneg A.1, sq_nonneg A.2.1,
      sq_nonneg A.2.2.1, sq_nonneg A.2.2.2]
  · exact sum_sq_of_mem_unityCoords A

/-- **(20.6.11)** (Hardy–Wright). There are just `24` unities. -/
@[kb "hardywright2008" "Section 20.6, p. 422"]
theorem ncard_unities : quaternionUnities.ncard = 24 := by
  rw [quaternionUnities, Set.ncard_image_of_injective _ halfQuat_injective, Set.ncard_coe_finset,
    unityCoords_card]

end NTKB.HardyWright
