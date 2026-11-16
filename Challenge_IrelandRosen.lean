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
import NTKB.IrelandRosen.R4.Bernoulli.ClassNumberField
import NTKB.IrelandRosen.R5.HeckeGaussian
import NTKB.IrelandRosen.R5.HeckeEisenstein
import NTKB.IrelandRosen.R5.MordellClassNumber

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

* (since 0.4.0) `NTKB.IrelandRosen.CM.heckeCharQuartic D` (the Hecke character of `ℚ(i)` of `y² = x³ - Dx`:
  `α ↦ conj((D/α)₄) α'` for `α` prime to `2D`, `α'` the primary associate of `α`, and `0` otherwise),
  `NTKB.HardyWright.ZRho` (`ℤ[ω]`, `ω² = -1 - ω`, as Mathlib's `QuadraticAlgebra ℤ (-1) (-1)`),
  `NTKB.IrelandRosen.Eisenstein.IsPrimary` (`π ≡ 2 mod 3` in `ℤ[ω]`) and
  `NTKB.IrelandRosen.CM.heckeCharSextic D` (the Hecke character of `ℚ(ω)` of `y² = x³ + D`, completely multiplicative
  on the elements prime to `6D`, `0` on the others; at a prime `ρ` of rational prime norm it is
  `-conj((4D/ρ')₆) ρ'`, `ρ'` the primary associate, with the sextic residue symbol
  `NTKB.IrelandRosen.Eisenstein.sexticChar`, and at an inert prime `-ρ'`); the local polynomial and the places of `ℚ`
  are Mathlib's (`WeierstrassCurve.localPolynomial`, `IsDedekindDomain.HeightOneSpectrum`,
  `Rat.HeightOneSpectrum.primesEquiv`)

The first five statements are those of release 0.1.0; `cube_eq_two_iff`, `points_y_sq_eq_x_cube_sub_D_x`,
`kummer_congruences` and `class_number_bernoulli` are new in release 0.3.0 and use only Mathlib's definitions besides
those above (`bernoulli`, `legendreSym`, `Nat.totient`). New in release 0.4.0: `class_number_bernoulli_field` and
`mordell_class_number` (only Mathlib's definitions: `NumberField.classNumber`, `QuadraticAlgebra`), and the four local
forms of Theorems 7 and 8 of Chapter 18 (the Hecke characters above).
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

/-- **The class number of `ℚ(√-p)` and a Bernoulli number** (Chapter 15, § 2, after Proposition 15.2.3), new in
0.4.0 for the class number of the field itself, with no assumed input. For a prime `p ≡ 3 (mod 4)`, `p > 3`, and the
quadratic number field `K` of discriminant `-p`, `h(K) ≡ -2 B_{(p+1)/2} (mod p)`: the difference divided by `p` is a
rational number whose denominator is prime to `p`. Here `h(K)` is Mathlib's `NumberField.classNumber K` and `B_k`
Mathlib's `bernoulli k`. (The headline `class_number_bernoulli` of 0.3.0 has Jacobi's expression in place of
`h(K)`.) Neither Mathlib nor Tau Ceti has this congruence. -/
theorem class_number_bernoulli_field {K : Type} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
    (hp : p % 4 = 3) (hp3 : 3 < p) (hK : Module.finrank ℚ K = 2) (hD : NumberField.discr K = -p) :
    ¬ p ∣ (((NumberField.classNumber K : ℚ) - -2 * bernoulli ((p + 1) / 2)) / (p : ℚ)).den := by
  sorry

/-- **The Hecke character of `y² = x³ - Dx`, split primes** (Chapter 18, § 5, Theorem 7, local form). Let `v` be
the finite place of `ℚ` of a prime `p ∤ 2D` with `p = π π̄`, `π` primary in `ℤ[i]`. Then Mathlib's local polynomial of
the curve at `p` (`WeierstrassCurve.localPolynomial`, the Euler factor of `WeierstrassCurve.LFunction`, here mapped to
`ℤ[i]`) is the Euler factor `(1 - χ(π) X)(1 - χ(π̄) X)` of `L(s, χ)` at the two primes above `p` (`X = p^{-s}`),
where `χ = NTKB.IrelandRosen.CM.heckeCharQuartic D` is the book's Hecke character `χ((α)) = conj((D/α)₄) α` of
`ℚ(i)`. So the Euler factors of `L(E, s)` and `L(s, χ)` agree at every `p ∤ 2D`; the primes dividing `2D` are not
compared (see the README, Known restrictions). The library also proves that `χ` is a completely multiplicative function
of ideals with `N(χ(A)) = N(A)` (Proposition 18.5.1 for this `χ`). Mathlib has the local polynomials and the L-function of a Weierstrass curve and Hecke characters
as definitions; Tau Ceti has Hecke L-functions and the complex multiplication of `y² = x³ + ax`; neither links
the L-function of a curve to a Hecke character. -/
theorem hecke_character_quartic_curve_split (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    {D : ℤ} (hD : ¬ (((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) : ℤ) ∣ 2 * D) {π : GaussianInt} (hπ : Gaussian.IsPrimary π)
    (hπp : π.norm = ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ)) :
    ((((⟨0, 0, 0, -D, 0⟩ : WeierstrassCurve ℤ).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ)).map (Int.castRingHom GaussianInt) =
      (1 - Polynomial.C (CM.heckeCharQuartic D π) * Polynomial.X) *
        (1 - Polynomial.C (CM.heckeCharQuartic D (star π)) * Polynomial.X) := by
  sorry

/-- **The Hecke character of `y² = x³ - Dx`, inert primes** (Chapter 18, § 5, Theorem 7, local form). For the
finite place `v` of a prime `p ≡ 3 (mod 4)`, `p ∤ 2D`, the local polynomial of the curve at `p` is the Euler factor
`1 - χ((p)) X²` of `L(s, χ)` at the prime `(p)` of `ℤ[i]` (of norm `p²`). -/
theorem hecke_character_quartic_curve_inert (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    {D : ℤ} (hD : ¬ (((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) : ℤ) ∣ 2 * D) (hp3 : ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) % 4 = 3) :
    ((((⟨0, 0, 0, -D, 0⟩ : WeierstrassCurve ℤ).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ)).map (Int.castRingHom GaussianInt) =
      1 - Polynomial.C (CM.heckeCharQuartic D (((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) : GaussianInt)) * Polynomial.X ^ 2 := by
  sorry

/-- **The Hecke character of `y² = x³ + D`, split primes** (Chapter 18, § 5, Theorem 8, local form). Let `v` be
the finite place of `ℚ` of a prime `p ∤ 6D` with `p = π π̄`, `π` primary in `ℤ[ω]` (`π ≡ 2 (mod 3)`). Then the local
polynomial of the curve at `p`, mapped to `ℤ[ω]`, is `(1 - χ(π) X)(1 - χ(π̄) X)`, where
`χ = NTKB.IrelandRosen.CM.heckeCharSextic D` is the book's Hecke character of `ℚ(ω)` built from the sextic residue
symbol `(4D/π)₆`. The primes dividing `6D` are not compared (see the README, Known restrictions). -/
theorem hecke_character_cubic_curve_split (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    {D : ℤ} (hD : ¬ (((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) : ℤ) ∣ 6 * D) {π : NTKB.HardyWright.ZRho} (hπ : Eisenstein.IsPrimary π)
    (hπp : QuadraticAlgebra.norm π = ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ)) :
    ((((⟨0, 0, 0, 0, D⟩ : WeierstrassCurve ℤ).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ)).map (Int.castRingHom NTKB.HardyWright.ZRho) =
      (1 - Polynomial.C (CM.heckeCharSextic D π) * Polynomial.X) *
        (1 - Polynomial.C (CM.heckeCharSextic D (star π)) * Polynomial.X) := by
  sorry

/-- **The Hecke character of `y² = x³ + D`, inert primes** (Chapter 18, § 5, Theorem 8, local form). For the
finite place `v` of a prime `p ≡ 2 (mod 3)`, `p ∤ 6D`, the local polynomial of the curve at `p` is
`1 - χ((p)) X²`. -/
theorem hecke_character_cubic_curve_inert (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    {D : ℤ} (hD : ¬ (((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) : ℤ) ∣ 6 * D) (hp2 : ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) % 3 = 2) :
    ((((⟨0, 0, 0, 0, D⟩ : WeierstrassCurve ℤ).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ)).map (Int.castRingHom NTKB.HardyWright.ZRho) =
      1 - Polynomial.C (CM.heckeCharSextic D (((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) : NTKB.HardyWright.ZRho)) * Polynomial.X ^ 2 := by
  sorry

/-- **Integral points on `y² = x³ - d` and the class number of `ℚ(√-d)`** (Chapter 17, § 10, Proposition
17.10.2). Let `d > 1` be squarefree, `d ≡ 1, 2 (mod 4)`, and suppose `3` does not divide the class number of
`ℚ(√-d)` (Mathlib's `QuadraticAlgebra ℚ (-d) 0`). Then `y² = x³ - d` has a solution in integers if and only if
`d = 3t² ± 1` for an integer `t`. The proof is the book's (the ring of integers `ℤ[√-d]`, Proposition 13.1.1, is
proved in the library). Neither Mathlib nor Tau Ceti has this criterion. -/
theorem mordell_class_number {d : ℤ} [Fact (1 < d)] (hsq : Squarefree d) (h4 : d % 4 = 1 ∨ d % 4 = 2)
    (h3 : ¬ 3 ∣ NumberField.classNumber (QuadraticAlgebra ℚ ((-d : ℤ) : ℚ) 0)) :
    (∃ x y : ℤ, y ^ 2 = x ^ 3 - d) ↔ ∃ t : ℤ, d = 3 * t ^ 2 + 1 ∨ d = 3 * t ^ 2 - 1 := by
  sorry

end NTKB.Headlines.IrelandRosen
