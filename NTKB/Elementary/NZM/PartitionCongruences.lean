/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
import Mathlib.RingTheory.PowerSeries.Expand
import NTKB.Attr
import NTKB.Analytic.Apostol.Partitions.Euler
import NTKB.Elementary.HardyWright.Partitions.Ramanujan

/-!
# A divisibility property of the Euler function (Niven–Zuckerman–Montgomery, § 10.6)

Throughout, `φ(x) = ∏_{n ≥ 1} (1 - xⁿ)`, as a formal power series over `ℤ`; by the pentagonal
number theorem (Mathlib, `PowerSeries.WithPiTopology.tprod_one_sub_X_pow`) it is
`PowerSeries.pentagonalSeries ℤ`.  The series `φ(x^p)` is `PowerSeries.expand p φ`.

* **Theorem 10.14.** For a prime `p`, `φ(x^p) / φ(x)^p = 1 + ∑_{j ≥ 1} a_j x^j` with integers `a_j`
  divisible by `p`.  Formally: `φ(x^p) = φ(x)^p · A` with `A ∈ ℤ⟦X⟧`, `A(0) = 1` and
  `p ∣ [x^j] A` for `j ≥ 1` (`A = φ(x^p) φ(x)^{-p}` is unique, `φ` being a non-zero-divisor).
  The book works with `0 < x < 1`, a statement about convergent series; as in the rest of the
  repository the formal power series version is proved (modulo `p`, `φ(x^p) = φ(x)^p` by Frobenius).
* **Theorem 10.15.** `x φ(x)⁴ = ∑_{m ≥ 1} b_m x^m` with integers `b_m`, and `5 ∣ b_m` if `5 ∣ m`
  (the book's `b_m = ∑ c_k d_{m-1-k}`, with Euler's and Jacobi's series; this is
  `NTKB.HardyWright.coeff_X_mul_pentagonal_mul_jacobi_five` over `ZMod 5`).

Definition 10.2 needs no new definitions: `p_m(n)` is `(Nat.Partition.restricted n (· ≤ m)).card`,
`p^o(n)` is `(Nat.Partition.odds n).card`, `p^d(n)` is `(Nat.Partition.distincts n).card`,
`q^e(n)`, `q^o(n)` are `NTKB.HardyWright.evenDistinctCount n`, `NTKB.HardyWright.oddDistinctCount n`
(see `NTKB/Elementary/NZM/Partitions.lean`).
-/

open PowerSeries

namespace NTKB.NZM

/-- Over `ZMod p`, `f(x^p) = f(x)^p`. -/
theorem expand_eq_pow_zmod (p : ℕ) [hp : Fact p.Prime] (f : (ZMod p)⟦X⟧) :
    expand p hp.out.ne_zero f = f ^ p := by
  have := map_frobenius_expand p hp.out.ne_zero (f := f)
  rw [ZMod.frobenius_zmod] at this
  exact this

theorem constantCoeff_pentagonalSeries_int : constantCoeff (pentagonalSeries ℤ) = 1 := by
  have := coeff_pentagonalSeries_pentagonal (R := ℤ) 0
  have h0 : pentagonal 0 = 0 := by simp [pentagonal_def]
  rw [h0, coeff_zero_eq_constantCoeff_apply] at this
  simpa using this

/-- **Theorem 10.14** (formal version). For a prime `p`, `φ(x^p) = φ(x)^p · A` where
`A = 1 + ∑_{j ≥ 1} a_j x^j` has integer coefficients with `p ∣ a_j`. -/
@[kb "nivenzuckermanmontgomery" "Thm 10.14, p. 467"]
theorem exists_expand_pentagonalSeries_eq_pow_mul (p : ℕ) [hp : Fact p.Prime] :
    ∃ A : ℤ⟦X⟧, expand p hp.out.ne_zero (pentagonalSeries ℤ) = pentagonalSeries ℤ ^ p * A ∧
      constantCoeff A = 1 ∧ ∀ j : ℕ, j ≠ 0 → (p : ℤ) ∣ coeff j A := by
  set φ := pentagonalSeries ℤ
  set P := NTKB.Apostol.partitionSeries ℤ
  have hPφ : P * φ = 1 := NTKB.Apostol.partitionSeries_mul_pentagonalSeries ℤ
  refine ⟨expand p hp.out.ne_zero φ * P ^ p, ?_, ?_, ?_⟩
  · calc expand p hp.out.ne_zero φ
        = expand p hp.out.ne_zero φ * (P * φ) ^ p := by rw [hPφ, one_pow, mul_one]
      _ = φ ^ p * (expand p hp.out.ne_zero φ * P ^ p) := by rw [mul_pow]; ring
  · rw [map_mul, map_pow, constantCoeff_expand]
    have h1 : constantCoeff P = 1 := by
      have := congrArg constantCoeff hPφ
      rw [map_mul, constantCoeff_pentagonalSeries_int, map_one, mul_one] at this
      exact this
    rw [h1, constantCoeff_pentagonalSeries_int]; simp
  · intro j hj
    have hmap : map (Int.castRingHom (ZMod p)) (expand p hp.out.ne_zero φ * P ^ p) = 1 := by
      rw [map_mul, map_pow, map_expand, expand_eq_pow_zmod, ← mul_pow, ← map_mul]
      have : map (Int.castRingHom (ZMod p)) (φ * P) = 1 := by
        rw [mul_comm, hPφ, map_one]
      rw [this, one_pow]
    have h := congrArg (coeff j) hmap
    rw [coeff_map, coeff_one] at h
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 (by simpa [hj] using h)

/-- **Theorem 10.15.** If `x φ(x)⁴ = ∑ b_m x^m` then `5 ∣ b_m` whenever `5 ∣ m`. -/
@[kb "nivenzuckermanmontgomery" "Thm 10.15, p. 469"]
theorem five_dvd_coeff_X_mul_pentagonalSeries_pow_four {m : ℕ} (hm : 5 ∣ m) :
    (5 : ℤ) ∣ coeff m (X * pentagonalSeries ℤ ^ 4) := by
  have e : (X : ℤ⟦X⟧) * pentagonalSeries ℤ ^ 4 =
      X * (pentagonalSeries ℤ * NTKB.HardyWright.jacobiSeries ℤ) := by
    rw [← NTKB.HardyWright.pentagonalSeries_pow_three]; ring
  rw [e]
  have h := NTKB.HardyWright.coeff_X_mul_pentagonal_mul_jacobi_five hm
  have h2 : ((coeff m (X * (pentagonalSeries ℤ * NTKB.HardyWright.jacobiSeries ℤ)) : ℤ) :
      ZMod 5) = 0 := by
    have := congrArg (coeff m) (show map (Int.castRingHom (ZMod 5))
        (X * (pentagonalSeries ℤ * NTKB.HardyWright.jacobiSeries ℤ)) =
        X * (pentagonalSeries (ZMod 5) * NTKB.HardyWright.jacobiSeries (ZMod 5)) by
      rw [map_mul, map_mul, map_X, NTKB.HardyWright.map_pentagonalSeries,
        NTKB.HardyWright.map_jacobiSeries])
    rw [coeff_map, h] at this
    simpa using this
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).1 h2

end NTKB.NZM
