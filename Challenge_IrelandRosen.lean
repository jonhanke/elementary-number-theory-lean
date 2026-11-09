/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import NTKB.IrelandRosen.R2.HasseDavenport
import NTKB.IrelandRosen.R2.LastEntry
import NTKB.IrelandRosen.R3.Reciprocity
import NTKB.IrelandRosen.R3.Legendre
import NTKB.IrelandRosen.R3.SophieGermain

/-!
# Headline statements of elementary-number-theory-lean 0.1.0: Ireland and Rosen

K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory* (2nd edition, 1990). The main results
of the library for this book, one theorem each, with every proof a deliberate `sorry`: to check what is claimed,
read this file. `Solution_IrelandRosen.lean` proves the same statements from the library, and `lake comparator`
(configured by `comparator/IrelandRosen.json`) checks that each proved statement is exactly the one here and uses
only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

Each statement is the library's statement, copied (a local notation of the library for the sign `(-1)^n` in
`ℤ[i]` is written out). The statements were not yet reviewed by a human (see the README).

## Definitions used

Besides Mathlib, the statements use these definitions of the library; a reader checking a statement should check
these too:

* `NTKB.IrelandRosen.liftNorm`, `NTKB.IrelandRosen.liftTrace` (the lifts `χ ∘ N_{E/F}` and `ψ ∘ tr_{E/F}` of
  characters to an extension of finite fields)
* `NTKB.IrelandRosen.Gaussian.IsPrimary` (a nonunit `α ∈ ℤ[i]` with `α ≡ 1 mod (1 + i)³`),
  `NTKB.IrelandRosen.Gaussian.quarticSymbol` (the quartic residue symbol `χ_α(β)`, the product of
  `NTKB.IrelandRosen.Gaussian.quarticChar ρ β` over the irreducible factors `ρ` of `α`; `quarticChar π β` is `0` if
  `π ∣ β`, otherwise the unit `iʲ` with `β^{(N π - 1)/4} ≡ iʲ mod π`, with the exponent
  `NTKB.IrelandRosen.Gaussian.qexp π = (N π - 1)/4`)
* `NTKB.IrelandRosen.numLastEntry` (the number of points of `x²t² + y²t² + x²y² - t⁴ = 0` in `P²(F)`, with
  `NTKB.IrelandRosen.lastEntryForm`)
* `NTKB.IrelandRosen.Legendre.HasSol` (`ax² + by² + cz² = 0` has a nontrivial integral solution),
  `NTKB.IrelandRosen.Legendre.SqMod` (`m` is a square modulo `n`)
-/

namespace NTKB.Headlines.IrelandRosen

open NTKB.IrelandRosen

/-- **The Hasse–Davenport relation** (Chapter 11, § 3, Theorem 1). Let `F ⊆ E` be finite fields with `[E : F] = s`,
`χ` a multiplicative and `ψ` a nontrivial additive character of `F` with values in a domain. Then
`(-g(χ))^s = -g(χ')`, where `χ' = χ ∘ N_{E/F}` and the Gauss sums over `E` are taken with `ψ' = ψ ∘ tr_{E/F}`.
Mathlib has Gauss sums and `gaussSum_sq`, `gaussSum_mul_gaussSum_eq_card`; neither Mathlib nor Tau Ceti has this
relation. -/
theorem hasse_davenport {F : Type*} [Field F] [Fintype F] {E : Type*} [Field E] [Fintype E] [Algebra F E]
    {R : Type*} [CommRing R] [IsDomain R] (χ : MulChar F R) {ψ : AddChar F R} (hψ : ψ ≠ 1) :
    (-gaussSum χ ψ) ^ Module.finrank F E = -gaussSum (liftNorm (E := E) χ) (liftTrace ψ) := by
  sorry

/-- **The law of biquadratic reciprocity** (Chapter 9, § 9, Theorem 2). Let `λ` and `π` be relatively prime
primary elements of `ℤ[i]`. Then `χ_π(λ) = χ_λ(π) (-1)^{((N λ - 1)/4)((N π - 1)/4)}`. Tau Ceti has the quartic
residue symbol of `ℤ[i]` with its supplementary laws, and cubic reciprocity, but not this law. -/
theorem biquadratic_reciprocity {π μ : GaussianInt} (hπ : Gaussian.IsPrimary π) (hμ : Gaussian.IsPrimary μ)
    (hcop : IsCoprime π μ) :
    Gaussian.quarticSymbol π μ = Gaussian.quarticSymbol μ π *
      (((Int.negOnePow (((μ.norm - 1) / 4) * ((π.norm - 1) / 4)) : ℤˣ) : ℤ) : GaussianInt) := by
  sorry

/-- **Gauss's last entry** (Chapter 11, § 5). Let `p ≡ 1 (mod 4)` be prime and write `p = a² + b²` with `a` odd,
`b` even, `a ≡ 1 (mod 4)` if `4 ∣ b` and `a ≡ -1 (mod 4)` if `4 ∤ b`; this determines `a`. Then the curve
`x²t² + y²t² + x²y² - t⁴ = 0` has `p - 1 - 2a` points in `P²(𝔽_p)`. -/
theorem gauss_last_entry {p : ℕ} [Fact p.Prime] (hp : p % 4 = 1) :
    ∃ a b : ℤ, (p : ℤ) = a ^ 2 + b ^ 2 ∧ Odd a ∧ Even b ∧ (4 ∣ b → a ≡ 1 [ZMOD 4]) ∧
      (¬4 ∣ b → a ≡ -1 [ZMOD 4]) ∧
      (∀ a' b' : ℤ, (p : ℤ) = a' ^ 2 + b' ^ 2 → Odd a' → Even b' →
        (4 ∣ b' → a' ≡ 1 [ZMOD 4]) → (¬4 ∣ b' → a' ≡ -1 [ZMOD 4]) → a' = a) ∧
      (numLastEntry (ZMod p) : ℤ) = p - 1 - 2 * a := by
  sorry

/-- **Legendre's theorem** (Proposition 17.3.1). Let `a, b, c` be squarefree, pairwise relatively prime integers,
not all positive and not all negative. Then `ax² + by² + cz² = 0` has a nontrivial integral solution if and only if
`-ab` is a square modulo `c`, `-ac` modulo `b` and `-bc` modulo `a`. -/
theorem legendre {a b c : ℤ} (hsa : Squarefree a) (hsb : Squarefree b) (hsc : Squarefree c)
    (hab : IsCoprime a b) (hac : IsCoprime a c) (hbc : IsCoprime b c)
    (hpos : ¬ (0 < a ∧ 0 < b ∧ 0 < c)) (hneg : ¬ (a < 0 ∧ b < 0 ∧ c < 0)) :
    Legendre.HasSol a b c ↔
      Legendre.SqMod (-(a * b)) c ∧ Legendre.SqMod (-(a * c)) b ∧ Legendre.SqMod (-(b * c)) a := by
  sorry

/-- **Sophie Germain's theorem** (Proposition 17.4.1). If `p` is an odd prime such that `2p + 1` is also prime, then
`x^p + y^p + z^p = 0` has no integral solution with `p ∤ xyz`. -/
theorem sophie_germain {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : (2 * p + 1).Prime) :
    ¬ ∃ x y z : ℤ, x ^ p + y ^ p + z ^ p = 0 ∧ ¬ (p : ℤ) ∣ x * y * z := by
  sorry

end NTKB.Headlines.IrelandRosen
