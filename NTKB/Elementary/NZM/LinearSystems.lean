/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Attr
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Basic.Real.Basic

/-!
# Local-global principle for systems of linear equations (Niven–Zuckerman–Montgomery, § 5.2)

* **Theorem 5.2** (`exists_int_solution_of_real_of_forall_modEq`): if the system of linear
  equations `∑_j a_ij x_j = b_i` (`1 ≤ i ≤ m`, integer coefficients) has a real solution, and the
  congruences `∑_j a_ij x_j ≡ b_i (mod q)` have a solution for every modulus `q`, then the
  equations have an integral solution.

The proof follows the book's idea via the Smith normal form, in the module-theoretic form of
Mathlib (`Submodule.smithNormalForm`): with bases `e_i` of `ℤ^m` and `s_k e_{f(k)}` of the image
`A ℤ^n`, the coordinates of `b` outside the range of `f` vanish because of the real solution, and
the coordinate of `b` at `f(k)` is divisible by `s_k` by the congruence for `q = ∏ |s_k|`.
-/

open Matrix

namespace NTKB.NZM

/-- **Theorem 5.2.**  If the system `A x = b` (`A` an `m × n` integer matrix, `b ∈ ℤ^m`) has a
real solution, and for every modulus `q ≥ 1` the congruences `A x ≡ b (mod q)` have an integral
solution, then `A x = b` has an integral solution. -/
@[kb "nivenzuckermanmontgomery" "Thm 5.2, p. 226"]
theorem exists_int_solution_of_real_of_forall_modEq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ)
    (hreal : ∃ x : Fin n → ℝ, (A.map (Int.cast : ℤ → ℝ)) *ᵥ x = fun i => (b i : ℝ))
    (hmod : ∀ q : ℕ, 0 < q → ∃ x : Fin n → ℤ, ∀ i, Int.ModEq q ((A *ᵥ x) i) (b i)) :
    ∃ x : Fin n → ℤ, A *ᵥ x = b := by
  classical
  set N : Submodule ℤ (Fin m → ℤ) := LinearMap.range A.mulVecLin with hN
  obtain ⟨k, snf⟩ := N.smithNormalForm (Pi.basisFun ℤ (Fin m))
  have ha : ∀ j, snf.a j ≠ 0 := by
    intro j h0
    have := snf.snf j
    rw [h0, zero_smul] at this
    exact snf.bN.ne_zero j (Subtype.ext this)
  -- the modulus
  set q : ℕ := ∏ j, (snf.a j).natAbs with hq
  have hq0 : 0 < q := Finset.prod_pos fun j _ => Int.natAbs_pos.2 (ha j)
  have hdvdq : ∀ j, snf.a j ∣ (q : ℤ) := by
    intro j
    rw [hq, Nat.cast_prod]
    exact (Int.dvd_natAbs.2 dvd_rfl).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
  obtain ⟨x₀, hx₀⟩ := hmod q hq0
  -- `b = A x₀ + q y`
  have hy : ∃ y : Fin m → ℤ, b = A *ᵥ x₀ + (q : ℤ) • y := by
    refine ⟨fun i => (b i - (A *ᵥ x₀) i) / q, funext fun i => ?_⟩
    have hd : (q : ℤ) ∣ b i - (A *ᵥ x₀) i := (Int.ModEq.dvd (hx₀ i))
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Int.mul_ediv_cancel' hd]
    ring
  obtain ⟨y, hby⟩ := hy
  have hAx₀ : A *ᵥ x₀ ∈ N := ⟨x₀, rfl⟩
  -- coordinates of elements of `N` at `f j` are multiples of `a j`
  have hcoordN : ∀ v ∈ N, ∀ j, snf.a j ∣ snf.bM.repr v (snf.f j) := by
    intro v hv j
    have := congrFun (snf.repr_comp_embedding_eq_smul ⟨v, hv⟩) j
    simp only [Function.comp_apply, smul_eq_mul] at this
    rw [this]
    exact dvd_mul_right _ _
  have hcoord_f : ∀ j, snf.a j ∣ snf.bM.repr b (snf.f j) := by
    intro j
    rw [hby, map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    exact dvd_add (hcoordN _ hAx₀ j) ((hdvdq j).mul_right _)
  -- coordinates outside the range of `f` vanish, by the real solution
  obtain ⟨xr, hxr⟩ := hreal
  have hcoord_out : ∀ i, i ∉ Set.range snf.f → snf.bM.repr b i = 0 := by
    intro i hi
    set ℓ := snf.bM.coord i
    have hker : ∀ v ∈ N, ℓ v = 0 := fun v hv => snf.le_ker_coord_of_notMem_range hi hv
    set w : Fin m → ℤ := fun r => ℓ (Pi.single r 1) with hw
    have hℓ : ∀ v : Fin m → ℤ, ℓ v = ∑ r, v r * w r := by
      intro v
      rw [LinearMap.pi_apply_eq_sum_univ ℓ v]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [smul_eq_mul, hw]
      congr 2
      funext s
      simp [Pi.single_apply, eq_comm]
    have hcol : ∀ j, ∑ r, A r j * w r = 0 := by
      intro j
      have hmem : A *ᵥ Pi.single j 1 ∈ N := ⟨Pi.single j 1, rfl⟩
      rw [← hker _ hmem, hℓ]
      refine Finset.sum_congr rfl fun r _ => ?_
      simp [mulVec_single]
    have hreal0 : (∑ r, (b r : ℝ) * (w r : ℝ)) = 0 := by
      have e : ∀ r, (b r : ℝ) = ∑ j, (A r j : ℝ) * xr j := by
        intro r
        have := congrFun hxr r
        simp only [mulVec, dotProduct, Matrix.map_apply] at this
        exact this.symm
      simp_rw [e, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun j _ => ?_
      have : ∑ r, (A r j : ℝ) * xr j * (w r : ℝ) = xr j * ((∑ r, A r j * w r : ℤ) : ℝ) := by
        push_cast
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun r _ => by ring
      rw [this, hcol j, Int.cast_zero, mul_zero]
    have : ℓ b = 0 := by
      rw [hℓ]
      exact_mod_cast hreal0
    simpa [ℓ] using this
  -- conclude `b ∈ N`
  have hbN : b ∈ N := by
    rw [← snf.bM.sum_repr b]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : i ∈ Set.range snf.f
    · obtain ⟨j, rfl⟩ := hi
      obtain ⟨d, hd⟩ := hcoord_f j
      rw [hd, mul_comm, mul_smul, ← snf.snf j]
      exact Submodule.smul_mem _ _ (snf.bN j).2
    · rw [hcoord_out i hi, zero_smul]
      exact Submodule.zero_mem _
  obtain ⟨x, hx⟩ := hbN
  exact ⟨x, hx⟩

/-! ## Determinantal divisors and invariant factors (§ 5.3) -/

/-- The `k`-th **determinantal divisor** `d_k(A)` of an integer matrix: the greatest common
divisor (normalized, so nonnegative) of all `k × k` minors of `A`.  The minors are indexed by
injective maps `Fin k → Fin m`, `Fin k → Fin n` (row and column selections in any order; the
order only changes the sign of the minor). -/
@[kb "nivenzuckermanmontgomery" "Determinantal divisors, p. 230"]
noncomputable def determinantalDivisor {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (k : ℕ) : ℤ :=
  Finset.univ.gcd fun p : (Fin k ↪ Fin m) × (Fin k ↪ Fin n) => Matrix.det (A.submatrix p.1 p.2)

/-- `d_k(A)` divides every `k × k` minor of `A`. -/
theorem determinantalDivisor_dvd {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) {k : ℕ}
    (r : Fin k ↪ Fin m) (c : Fin k ↪ Fin n) : determinantalDivisor A k ∣ Matrix.det (A.submatrix r c) :=
  Finset.gcd_dvd (f := fun p : (Fin k ↪ Fin m) × (Fin k ↪ Fin n) =>
    Matrix.det (A.submatrix p.1 p.2)) (Finset.mem_univ (r, c))

/-- Every common divisor of the `k × k` minors divides `d_k(A)`. -/
theorem dvd_determinantalDivisor {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) {k : ℕ} {d : ℤ}
    (h : ∀ (r : Fin k ↪ Fin m) (c : Fin k ↪ Fin n), d ∣ Matrix.det (A.submatrix r c)) :
    d ∣ determinantalDivisor A k :=
  Finset.dvd_gcd fun p _ => h p.1 p.2

/-- `d_0(A) = 1` (the empty minor is `1`). -/
theorem determinantalDivisor_zero {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    determinantalDivisor A 0 = 1 := by
  have h : determinantalDivisor A 0 ∣ 1 := by
    simpa using determinantalDivisor_dvd A (Function.Embedding.ofIsEmpty : Fin 0 ↪ Fin m)
      (Function.Embedding.ofIsEmpty : Fin 0 ↪ Fin n)
  have hn : 0 ≤ determinantalDivisor A 0 := by
    unfold determinantalDivisor
    exact Int.nonneg_of_normalize_eq_self (Finset.normalize_gcd)
  rcases Int.isUnit_iff.1 (isUnit_of_dvd_one h) with h1 | h1
  · exact h1
  · omega

/-- The **invariant factors** of an integer matrix: `s_k = d_k(A) / d_{k-1}(A)` for `k ≥ 1`
(the diagonal entries of the Smith normal form of `A`, when `d_{k-1}(A) ≠ 0`). -/
@[kb "nivenzuckermanmontgomery" "Invariant factors, p. 229"]
noncomputable def invariantFactor {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (k : ℕ) : ℤ :=
  determinantalDivisor A k / determinantalDivisor A (k - 1)

end NTKB.NZM
