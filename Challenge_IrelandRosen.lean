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
import NTKB.IrelandRosen.R4.CubicReciprocity
import NTKB.IrelandRosen.R4.QuarticCurve
import NTKB.IrelandRosen.R4.Bernoulli.Kummer
import NTKB.IrelandRosen.R4.Bernoulli.ClassNumber

/-!
# Headline statements of elementary-number-theory-lean: Ireland and Rosen

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

The first five statements are those of release 0.1.0; `cube_eq_two_iff`, `points_y_sq_eq_x_cube_sub_D_x`,
`kummer_congruences` and `class_number_bernoulli` are new in release 0.3.0 and use only Mathlib's definitions besides
those above (`bernoulli`, `legendreSym`, `Nat.totient`).
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

/-- **Two is a cubic residue modulo `p` exactly when `p = C² + 27D²`** (Proposition 9.6.2, from the law of cubic
reciprocity and its supplement, both proved in the library). For a prime `p ≡ 1 (mod 3)`, `x³ ≡ 2 (mod p)` has a
solution if and only if `p = C² + 27D²` for some integers `C, D`. Tau Ceti has cubic reciprocity; neither Mathlib
nor Tau Ceti has this consequence. -/
theorem cube_eq_two_iff {p : ℕ} (hp : p.Prime) (hp3 : p % 3 = 1) :
    (∃ x : ZMod p, x ^ 3 = 2) ↔ ∃ C D : ℤ, (p : ℤ) = C ^ 2 + 27 * D ^ 2 := by
  sorry

/-- **The number of points of `y² = x³ - Dx` over `𝔽_p`** (Chapter 18, § 4, Theorem 5). Let `p ≡ 1 (mod 4)` be
prime, `p = π π̄` with `π` primary in `ℤ[i]`, and `p ∤ D`. Then the number `N_p` of points of `y² = x³ - Dx` over
`𝔽_p` (the affine solutions and the point at infinity) is `p + 1 - conj(χ_π(D)) π - χ_π(D) π̄`, with `χ_π` the
quartic residue symbol. Since `|π|² = p`, it gives `|N_p - (p + 1)| ≤ 2 √p` for these curves (in the library:
`NTKB.IrelandRosen.abs_numPointsQuarticCurve_sub_le`; Tau Ceti has Hasse's bound for every elliptic curve over a
finite field). Neither Mathlib nor Tau Ceti has this formula. -/
theorem points_y_sq_eq_x_cube_sub_D_x {p : ℕ} [Fact p.Prime] (hp : p % 4 = 1) {π : GaussianInt}
    (hπ : Gaussian.IsPrimary π) (hπp : π.norm = p) {D : ℤ} (hD : ¬ (p : ℤ) ∣ D) :
    (((1 + (Finset.univ.filter fun xy : ZMod p × ZMod p => xy.2 ^ 2 = xy.1 ^ 3 - D * xy.1).card : ℕ) : ℤ) :
        GaussianInt) =
      p + 1 - star (Gaussian.quarticChar π D) * π - Gaussian.quarticChar π D * star π := by
  sorry

/-- **The Kummer congruences** (Chapter 15, § 2, Theorem 5). Let `p` be a prime, `e ≥ 1`, and `m, m'` positive
even integers with `p - 1 ∤ m` and `m' ≡ m (mod φ(pᵉ))`. Then
`(1 - p^(m'-1)) B_{m'}/m' ≡ (1 - p^(m-1)) B_m/m (mod pᵉ)`: the difference divided by `pᵉ` is a rational number whose
denominator is prime to `p`. Here `B_k` is Mathlib's `bernoulli k`. Mathlib has the theorem of von Staudt and
Clausen; neither Mathlib nor Tau Ceti has these congruences. -/
theorem kummer_congruences (p : ℕ) [Fact p.Prime] {e m m' : ℕ} (he : 1 ≤ e)
    (hm : Even m) (hm0 : m ≠ 0) (hm' : Even m') (hm'0 : m' ≠ 0) (hpm : ¬ p - 1 ∣ m)
    (hmm' : m' ≡ m [MOD (p ^ e).totient]) :
    ¬ p ∣ (((1 - (p : ℚ) ^ (m' - 1)) * bernoulli m' / m' -
      (1 - (p : ℚ) ^ (m - 1)) * bernoulli m / m) / (p : ℚ) ^ e).den := by
  sorry

/-- **The class number of `ℚ(√-p)` and a Bernoulli number** (Chapter 15, § 2, after Proposition 15.2.3), with the
class number in Jacobi's form. For a prime `p ≡ 3 (mod 4)`, `p > 3`, Jacobi's expression
`h = -(1/p) ∑_{j=1}^{p-1} j (j/p)` satisfies `h ≡ -2 B_{(p+1)/2} (mod p)`: the difference divided by `p` is a
rational number whose denominator is prime to `p`. That this `h` is the class number of `ℚ(√-p)` is Jacobi's class
number formula (Davenport, Chapter 6), which the book cites; the library proves that formula from two cited results
assumed as named statements (see the README, Known restrictions). Neither Mathlib nor Tau Ceti has this congruence.
-/
theorem class_number_bernoulli {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) (hp3 : 3 < p) :
    ¬ p ∣ ((-(1 / (p : ℚ)) * ∑ j ∈ Finset.Ico 1 p, (j : ℚ) * legendreSym p j -
      -2 * bernoulli ((p + 1) / 2)) / (p : ℚ)).den := by
  sorry

end NTKB.Headlines.IrelandRosen
