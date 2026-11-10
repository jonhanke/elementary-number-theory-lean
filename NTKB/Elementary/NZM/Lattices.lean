/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Attr
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# Lattices and a derivative lemma (Niven–Zuckerman–Montgomery, §§ 6.3–6.4)

* Lemma 6.17: `x^n g(x)` and all its derivatives at `0` are integers divisible by `n!`.
* Theorem 6.23: for nonsingular `A`, `B`, `B ℤⁿ ⊆ A ℤⁿ` iff `B = A K` with `K` an integer matrix.
  (Nonsingularity is not needed for this equivalence, so it is not assumed.)
* Corollary 6.24: `A ℤⁿ = B ℤⁿ` iff `B = A U` with `U` unimodular (integer matrix, `det = ±1`).
-/

open Polynomial

namespace NTKB.NZM

/-- **Lemma 6.17.** For `n` and an integer polynomial `g`, every derivative of `x^n g(x)`
evaluated at `0` is an integer divisible by `n!`. -/
@[kb "nivenzuckermanmontgomery" "Lemma 6.17, p. 309"]
theorem factorial_dvd_iterate_derivative_X_pow_mul (n : ℕ) (g : ℤ[X]) (j : ℕ) :
    ((n.factorial : ℕ) : ℤ) ∣ ((derivative^[j]) (X ^ n * g)).eval 0 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, coeff_iterate_derivative, zero_add,
    coeff_X_pow_mul']
  by_cases h : n ≤ j
  · simp only [h, ite_true, Nat.descFactorial_self, nsmul_eq_mul]
    exact Dvd.dvd.mul_right (Int.natCast_dvd_natCast.mpr (Nat.factorial_dvd_factorial h)) _
  · simp [h]

/-- The lattice `A ℤⁿ = {A u : u ∈ ℤⁿ}` of a real square matrix. -/
def matrixLattice {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Set (Fin n → ℝ) :=
  {v | ∃ u : Fin n → ℤ, v = A.mulVec (fun i => (u i : ℝ))}

lemma map_cast_mul {n : ℕ} (K L : Matrix (Fin n) (Fin n) ℤ) :
    (K * L).map (fun z => (z : ℝ)) = K.map (fun z => (z : ℝ)) * L.map (fun z => (z : ℝ)) := by
  ext i j
  simp [Matrix.mul_apply]

/-- **Theorem 6.23.** `B ℤⁿ ⊆ A ℤⁿ` iff `B = A K` for a matrix `K` with integer entries. -/
@[kb "nivenzuckermanmontgomery" "Thm 6.23, p. 315"]
theorem matrixLattice_subset_iff {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    matrixLattice B ⊆ matrixLattice A ↔
      ∃ K : Matrix (Fin n) (Fin n) ℤ, B = A * K.map (fun z => (z : ℝ)) := by
  constructor
  · intro h
    have hcol : ∀ j, ∃ u : Fin n → ℤ,
        B.mulVec (Pi.single j (1 : ℝ)) = A.mulVec (fun i => (u i : ℝ)) := by
      intro j
      apply h
      refine ⟨Pi.single j 1, ?_⟩
      congr 1
      ext i
      by_cases hij : i = j <;> simp [hij]
    choose u hu using hcol
    refine ⟨Matrix.of fun i j => u j i, ?_⟩
    ext i j
    have := congrFun (hu j) i
    simp only [Matrix.mulVec_single_one] at this
    rw [Matrix.mul_apply]
    simpa [Matrix.mulVec, dotProduct] using this
  · rintro ⟨K, rfl⟩ v ⟨u, rfl⟩
    refine ⟨K.mulVec u, ?_⟩
    rw [← Matrix.mulVec_mulVec]
    congr 1
    ext i
    simp [Matrix.mulVec, dotProduct]

/-- **Corollary 6.24.** `A ℤⁿ = B ℤⁿ` iff `B = A U` for a unimodular integer matrix `U`. -/
@[kb "nivenzuckermanmontgomery" "Cor 6.24, p. 315"]
theorem matrixLattice_eq_iff {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.det ≠ 0) (hB : B.det ≠ 0) :
    matrixLattice A = matrixLattice B ↔
      ∃ U : Matrix (Fin n) (Fin n) ℤ, (U.det = 1 ∨ U.det = -1) ∧
        B = A * U.map (fun z => (z : ℝ)) := by
  have _ := hB
  constructor
  · intro h
    obtain ⟨K, hK⟩ := (matrixLattice_subset_iff A B).mp h.symm.subset
    obtain ⟨L, hL⟩ := (matrixLattice_subset_iff B A).mp h.subset
    have hAu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
    have hKL : K * L = 1 := by
      have h1 : A * ((K * L).map (fun z => (z : ℝ))) = A * (1 : Matrix (Fin n) (Fin n) ℝ) := by
        rw [map_cast_mul, ← mul_assoc, ← hK, ← hL, mul_one]
      have h2 : (K * L).map (fun z => (z : ℝ)) = 1 := by
        have h3 := congrArg (fun M => A⁻¹ * M) h1
        simp only [← mul_assoc, Matrix.nonsing_inv_mul _ hAu, one_mul] at h3
        exact h3
      ext i j
      have := congrFun (congrFun h2 i) j
      simp only [Matrix.map_apply, Matrix.one_apply] at this ⊢
      by_cases hij : i = j <;> simp [hij] at this ⊢ <;> exact_mod_cast this
    refine ⟨K, ?_, hK⟩
    have hd : K.det * L.det = 1 := by rw [← Matrix.det_mul, hKL, Matrix.det_one]
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hd with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rintro ⟨U, hU, rfl⟩
    have hd : U.det * U.det = 1 := by rcases hU with h | h <;> rw [h] <;> norm_num
    have hUL : U * (U.det • U.adjugate) = 1 := by
      rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, hd, one_smul]
    apply Set.Subset.antisymm
    · refine (matrixLattice_subset_iff (A * U.map (fun z => (z : ℝ))) A).mpr
        ⟨U.det • U.adjugate, ?_⟩
      rw [mul_assoc, ← map_cast_mul, hUL]; simp
    · exact (matrixLattice_subset_iff A (A * U.map (fun z => (z : ℝ)))).mpr ⟨U, rfl⟩

end NTKB.NZM
