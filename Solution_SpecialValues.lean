/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import NTKB.Elementary.SpecialValues.ValueAtZero
import NTKB.Elementary.SpecialValues.ValueAtOne
import NTKB.Elementary.SpecialValues.FundamentalGaussSum

/-!
# Proofs of the special values headline statements

The statements of `Challenge_SpecialValues.lean`, proved by the library theorems. `lake comparator` checks that each
statement here is exactly the one in `Challenge_SpecialValues.lean`.
-/

namespace NTKB.Headlines.SpecialValues

open Complex
open scoped Real

theorem LFunction_one_sub_nat {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {k : ℕ} (hk : 1 ≤ k) :
    DirichletCharacter.LFunction χ (1 - k) = -NTKB.generalizedBernoulli χ k / k :=
  NTKB.LFunction_one_sub_nat χ hk

theorem LFunction_natCast {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) {k : ℕ}
    (hk : 1 ≤ k) (hpar : χ (-1) = (-1) ^ k) :
    DirichletCharacter.LFunction χ k =
      (-1) ^ (1 + (k - k % 2) / 2) * gaussSum χ ZMod.stdAddChar / (2 * I ^ (k % 2)) *
        (2 * π / N) ^ k * NTKB.generalizedBernoulli χ⁻¹ k / k.factorial :=
  NTKB.LFunction_natCast χ hχ hk hpar

theorem gaussSum_kroneckerChar {D : ℤ} (hD : NTKB.IsFundamentalDiscriminant D) [NeZero D.natAbs] :
    gaussSum (NTKB.kroneckerChar D) ZMod.stdAddChar =
      if 0 < D then ((√(D : ℝ) : ℝ) : ℂ) else I * √(-D : ℝ) :=
  NTKB.gaussSum_kroneckerChar hD

end NTKB.Headlines.SpecialValues
