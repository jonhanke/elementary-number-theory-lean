/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import NTKB.Elementary.SpecialValues.ValueAtZero
import NTKB.Elementary.SpecialValues.ValueAtOne
import NTKB.Elementary.SpecialValues.FundamentalGaussSum

/-!
# Headline statements of elementary-number-theory-lean 0.1.0: special values of Dirichlet `L`-functions

The values of Dirichlet `L`-functions at the integers and Gauss's sign of quadratic Gauss sums (Washington,
*Introduction to Cyclotomic Fields*, Chapter 4; Ireland–Rosen, Chapters 6 and 16). The main results, one theorem
each, with every proof a deliberate `sorry`: to check what is claimed, read this file. `Solution_SpecialValues.lean`
proves the same statements from the library, and `lake comparator` (configured by `comparator/SpecialValues.json`)
checks that each proved statement is exactly the one here and uses only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

Each statement is the library's statement, copied. The statements were not yet reviewed by a human (see the README).

`L(s, χ)` is Mathlib's `DirichletCharacter.LFunction χ s`: the continuation of `∑ χ(n) n^{-s}` at level `N` (for
imprimitive `χ` the Euler factors at `p ∣ N` are removed). `τ(χ) = gaussSum χ ZMod.stdAddChar = ∑_a χ(a) e^{2πia/N}`.

## Definitions used

Besides Mathlib, the statements use these definitions of the library; a reader checking a statement should check
these too:

* `NTKB.generalizedBernoulli` (`B_{n,χ} = N^{n-1} ∑_{a=1}^{N} χ(a) B_n(a/N)`, with Mathlib's Bernoulli polynomials;
  for the character modulo `1` this is `B_n(1)`, so `B_1 = +1/2`)
* `NTKB.IsFundamentalDiscriminant` (`D ≡ 1 mod 4` squarefree, or `D = 4k` with `k ≡ 2, 3 mod 4` squarefree)
* `NTKB.kroneckerChar` (the Kronecker character `χ_D` modulo `|D|`, built from the Jacobi symbol and Mathlib's
  `ZMod.χ₄`, `ZMod.χ₈`, `ZMod.χ₈'`, with `NTKB.jacobiChar`, `NTKB.chi4`)
-/

namespace NTKB.Headlines.SpecialValues

open Complex
open scoped Real

/-- **`L(1 - k, χ) = -B_{k,χ}/k`** for every Dirichlet character `χ` and every `k ≥ 1` (Washington, Theorem 4.2),
with no primitivity or nontriviality hypothesis. Mathlib has the values `ζ(-k)` and the Hurwitz zeta function at
`-k` for `k ≥ 1` (`hurwitzZeta_neg_nat`); Tau Ceti has `B_{k,χ}` and the identity of the next theorem for the sum
over `ℤ` and `k ≥ 2`; neither has the value at `s = 0` of a general `L(s, χ)` nor this formula. -/
theorem LFunction_one_sub_nat {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {k : ℕ} (hk : 1 ≤ k) :
    DirichletCharacter.LFunction χ (1 - k) = -NTKB.generalizedBernoulli χ k / k := by
  sorry

/-- **`L(k, χ)` by Gauss sums.** For a primitive Dirichlet character `χ` modulo `N`, `k ≥ 1` with
`χ(-1) = (-1)^k` and `δ = k mod 2`: `L(k, χ) = (-1)^{1+(k-δ)/2} τ(χ)/(2 i^δ) (2π/N)^k B_{k,χ̄}/k!`. Tau Ceti has
`τ(χ) ∑_{n ∈ ℤ} χ̄(n) n^{-k} = -(2πi)^k B_{k,χ}/(k! N^{k-1})` for `k ≥ 2`
(`DirichletCharacter.gaussSum_mul_tsum_inv_pow_eq_generalizedBernoulli`); the case `k = 1` and the passage to
`L(k, χ)` are new here. -/
theorem LFunction_natCast {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) {k : ℕ}
    (hk : 1 ≤ k) (hpar : χ (-1) = (-1) ^ k) :
    DirichletCharacter.LFunction χ k =
      (-1) ^ (1 + (k - k % 2) / 2) * gaussSum χ ZMod.stdAddChar / (2 * I ^ (k % 2)) *
        (2 * π / N) ^ k * NTKB.generalizedBernoulli χ⁻¹ k / k.factorial := by
  sorry

/-- **Gauss's sign of the quadratic Gauss sum, for every fundamental discriminant** (Ireland–Rosen, Chapter 6, § 4
and Chapter 16): `τ(χ_D) = √D` if `D > 0` and `τ(χ_D) = i √|D|` if `D < 0`. Mathlib has `τ(χ)² = χ(-1) p`
(`gaussSum_sq`); Tau Ceti has the evaluation of `∑_{r mod N} e^{2πi r²/N}` for every `N`
(`sum_range_cexp_two_pi_I_sq_div`, ported here with credit), not the Gauss sums of Jacobi or Kronecker
characters. -/
theorem gaussSum_kroneckerChar {D : ℤ} (hD : NTKB.IsFundamentalDiscriminant D) [NeZero D.natAbs] :
    gaussSum (NTKB.kroneckerChar D) ZMod.stdAddChar =
      if 0 < D then ((√(D : ℝ) : ℝ) : ℂ) else I * √(-D : ℝ) := by
  sorry

end NTKB.Headlines.SpecialValues
