/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import NTKB.Elementary.SpecialValues.ValueAtOne

/-!
# The formula for `L(k, χ)` as written in the original request, and checks of the constant

The original request asks for
$$L(k,\chi) = (-1)^{1+(k-\delta)/2}\,\frac{\tau(\chi)}{2}\left(\frac{2\pi}{f}\right)^{k}
  \frac{B_{k,\bar\chi}}{k!}$$
for primitive `χ` modulo `f`, `k ≥ 1`, `χ(-1) = (-1)^k`, `δ ∈ {0, 1}` the parity. This is the
statement `NTKB.IssueTwoLValueFormula` below, kept exactly as written. It is

* **true for even `χ`** (`δ = 0`): `issueTwoLValueFormula_of_even`;
* **false for every odd primitive `χ`** (`δ = 1`) and every odd `k`:
  `not_issueTwoLValueFormula_of_odd`. Washington (Chapter 4) has `τ(χ)/(2 i^δ)` in place of
  `τ(χ)/2`; that corrected statement is `NTKB.LFunction_natCast` (proved for all `k ≥ 1`).
  Smallest counterexample: `χ = χ_{-4}`, `k = 1`: `τ(χ_{-4}) = 2i`, `B_{1,χ_{-4}} = -1/2`, so the
  right side is `iπ/4`, while `L(1, χ_{-4}) = π/4`.

The constant of `NTKB.LFunction_natCast` is checked in Lean against Mathlib's independent
evaluation `ζ(2) = π²/6` (`LFunction_natCast_check_zeta_two`); numerical checks for small
conductors are recorded in `docs/results/special-values.md`.
-/

noncomputable section

open Complex
open scoped Real

namespace NTKB

variable {N : ℕ} [NeZero N]

/-- The formula for `L(k, χ)` exactly as written in the original request (no factor `i^δ`):
`L(k, χ) = (-1)^{1+(k-δ)/2} τ(χ)/2 · (2π/N)^k · B_{k,χ̄}/k!`, `δ = k mod 2`. -/
def IssueTwoLValueFormula (χ : DirichletCharacter ℂ N) (k : ℕ) : Prop :=
  DirichletCharacter.LFunction χ k =
    (-1) ^ (1 + (k - k % 2) / 2) * gaussSum χ ZMod.stdAddChar / 2 *
      (2 * π / N) ^ k * generalizedBernoulli χ⁻¹ k / k.factorial

/-- The issue's formula holds for even primitive characters (then `δ = 0`). -/
theorem issueTwoLValueFormula_of_even (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)
    {k : ℕ} (hk : 1 ≤ k) (hpar : χ (-1) = (-1) ^ k) (heven : χ.Even) :
    IssueTwoLValueFormula χ k := by
  have hk2 : k % 2 = 0 := by
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · omega
    · exfalso
      rw [DirichletCharacter.Even, hpar, hj, pow_succ, pow_mul] at heven
      norm_num at heven
  unfold IssueTwoLValueFormula
  rw [LFunction_natCast χ hχ hk hpar, hk2, pow_zero, mul_one]

/-- **The issue's formula is false for every odd primitive character** (and every admissible
`k`, necessarily odd): the correct constant has the extra factor `1/i`
(`NTKB.LFunction_natCast`), and `L(k, χ) ≠ 0`. -/
theorem not_issueTwoLValueFormula_of_odd (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)
    {k : ℕ} (hk : 1 ≤ k) (hpar : χ (-1) = (-1) ^ k) (hodd : χ.Odd) :
    ¬ IssueTwoLValueFormula χ k := by
  have hχ1 : χ ≠ 1 := by
    rintro rfl
    exact DirichletCharacter.Odd.not_even _ hodd DirichletCharacter.even_one
  have hk2 : k % 2 = 1 := by
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · exfalso
      rw [DirichletCharacter.Odd, hpar, hj, ← two_mul, pow_mul] at hodd
      norm_num at hodd
    · omega
  intro h
  unfold IssueTwoLValueFormula at h
  have hL := LFunction_natCast χ hχ hk hpar
  have hI : I ^ (k % 2) = I := by rw [hk2, pow_one]
  rw [hI] at hL
  have hne : DirichletCharacter.LFunction χ k ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1)
      (by simp only [natCast_re]; exact_mod_cast hk)
  set X := (-1) ^ (1 + (k - k % 2) / 2) * gaussSum χ ZMod.stdAddChar *
    (2 * π / N) ^ k * generalizedBernoulli χ⁻¹ k / k.factorial with hX
  have h1 : DirichletCharacter.LFunction χ k = X / 2 := by rw [h, hX]; ring
  have h2 : DirichletCharacter.LFunction χ k = X / (2 * I) := by rw [hL, hX]; ring
  have hX0 : X = 0 := by
    have h3 : X / 2 = X / (2 * I) := h1.symm.trans h2
    field_simp at h3
    have h4 : X * (I - 1) = 0 := by linear_combination h3
    rcases mul_eq_zero.mp h4 with h5 | h5
    · exact h5
    · exfalso
      have := congrArg re h5
      simp at this
  exact hne (by rw [h1, hX0, zero_div])

/-- Check of the constant of `NTKB.LFunction_natCast` against Mathlib's `ζ(2) = π²/6`: the
formula for the character modulo `1` at `k = 2` gives `π²/6`. -/
theorem LFunction_natCast_check_zeta_two (χ : DirichletCharacter ℂ 1) :
    (-1) ^ (1 + (2 - 2 % 2) / 2) * gaussSum χ ZMod.stdAddChar / (2 * I ^ (2 % 2)) *
        (2 * π / (1 : ℕ)) ^ 2 * generalizedBernoulli χ⁻¹ 2 / (Nat.factorial 2) =
      riemannZeta 2 := by
  have hprim : χ.IsPrimitive := by
    rw [χ.level_one]
    exact DirichletCharacter.isPrimitive_one_level_one
  have h := LFunction_natCast χ hprim (k := 2) (by norm_num)
    (by rw [χ.level_one]; simp)
  rw [← h, DirichletCharacter.LFunction_modOne_eq]
  norm_num

end NTKB
