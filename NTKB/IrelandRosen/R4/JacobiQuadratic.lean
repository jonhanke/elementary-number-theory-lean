/-
Ireland–Rosen, Chapter 18, §3: the Jacobi sum `J(ρ, ψ)` with `ρ` the quadratic character.
-/
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import NTKB.Attr

/-!
# `J(ρ, ψ) = ψ(4) J(ψ, ψ)`

Ireland–Rosen, Chapter 18, §3, Lemma. Following the book: for a nontrivial character `ψ` of a
finite field `F` of odd characteristic and `ρ` the quadratic character,
`J(ρ, ψ) = ∑_{u+v=1} (1 + ρ(u)) ψ(v) = ∑_t ψ(1 - t²) = ψ(4) ∑_t ψ((1-t)/2) ψ((1+t)/2) = ψ(4) J(ψ, ψ)`.
-/

namespace NTKB.IrelandRosen

open Finset

section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {R : Type*} [CommRing R]

/-- `∑_t ψ(1 - t²) = ∑_x (1 + ρ(x)) ψ(1 - x)`, counting square roots. -/
lemma sum_apply_one_sub_sq (hF : ringChar F ≠ 2) (ψ : MulChar F R) :
    ∑ t : F, ψ (1 - t ^ 2) =
      ∑ x : F, (1 + ((quadraticChar F x : ℤ) : R)) * ψ (1 - x) := by
  have h1 : ∀ t : F, ψ (1 - t ^ 2) = ∑ x : F, if t ^ 2 = x then ψ (1 - x) else 0 := by
    intro t; simp
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hc := quadraticChar_card_sqrts hF x
  have hc' : (#{t : F | t ^ 2 = x} : ℤ) = quadraticChar F x + 1 := by
    rw [← hc]; simp
  have : ((#{t : F | t ^ 2 = x} : ℕ) : R) = 1 + ((quadraticChar F x : ℤ) : R) := by
    have := congrArg (Int.cast : ℤ → R) hc'
    push_cast at this
    rw [this]; ring
  rw [this]

end

/-- **Ireland–Rosen, Chapter 18, §3, Lemma.** For a finite field `F` of odd characteristic, the
quadratic character `ρ` and a nontrivial character `ψ`, `J(ρ, ψ) = ψ(4) J(ψ, ψ)`. -/
@[kb "irelandrosen1990" "Ch. 18, §3, Lemma, p. 316"]
theorem jacobiSum_quadraticChar_eq {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) {R : Type*} [CommRing R] [IsDomain R] {ψ : MulChar F R} (hψ : ψ ≠ 1) :
    jacobiSum ((quadraticChar F).ringHomComp (Int.castRingHom R)) ψ = ψ 4 * jacobiSum ψ ψ := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have h4 : (4 : F) = 2 * 2 := by norm_num
  -- `∑_x ψ(1 - x) = 0`
  have hsum : ∑ x : F, ψ (1 - x) = 0 := by
    rw [← MulChar.sum_eq_zero_of_ne_one hψ]
    exact (Equiv.subLeft (1 : F)).sum_comp (fun x => ψ x)
  have hJ : jacobiSum ((quadraticChar F).ringHomComp (Int.castRingHom R)) ψ =
      ∑ x : F, (1 + ((quadraticChar F x : ℤ) : R)) * ψ (1 - x) := by
    simp only [jacobiSum, MulChar.ringHomComp_apply, eq_intCast, add_mul, one_mul,
      Finset.sum_add_distrib, hsum, zero_add]
  rw [hJ, ← sum_apply_one_sub_sq hF ψ, jacobiSum, Finset.mul_sum]
  -- reindex by `s = (1 - t) / 2`
  let e : F ≃ F :=
    { toFun := fun t => (1 - t) / 2
      invFun := fun s => 1 - 2 * s
      left_inv := fun t => by field_simp; ring
      right_inv := fun s => by field_simp; ring }
  rw [← e.sum_comp (fun x => ψ 4 * (ψ x * ψ (1 - x)))]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hA : (1 : F) - t ^ 2 = 4 * (((1 - t) / 2) * (1 - (1 - t) / 2)) := by
    field_simp; ring
  show ψ (1 - t ^ 2) = ψ 4 * (ψ ((1 - t) / 2) * ψ (1 - (1 - t) / 2))
  rw [hA, map_mul, map_mul]

end NTKB.IrelandRosen
