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
import NTKB.IrelandRosen.R5.BadPrimesCM
import NTKB.IrelandRosen.R5.MordellInfinite

/-!
# Proofs of the Ireland–Rosen headline statements

The statements of `Challenge_IrelandRosen.lean`, proved by the library theorems. `lake comparator` checks that each
statement here is exactly the one in `Challenge_IrelandRosen.lean`.
-/

namespace NTKB.Headlines.IrelandRosen

open NTKB.IrelandRosen

theorem hasse_davenport {F : Type*} [Field F] [Fintype F] {E : Type*} [Field E] [Fintype E] [Algebra F E]
    {R : Type*} [CommRing R] [IsDomain R] (χ : MulChar F R) {ψ : AddChar F R} (hψ : ψ ≠ 1) :
    (-gaussSum χ ψ) ^ Module.finrank F E = -gaussSum (liftNorm (E := E) χ) (liftTrace ψ) :=
  NTKB.IrelandRosen.hasse_davenport χ hψ

theorem biquadratic_reciprocity {π μ : GaussianInt} (hπ : Gaussian.IsPrimary π) (hμ : Gaussian.IsPrimary μ)
    (hcop : IsCoprime π μ) :
    Gaussian.quarticSymbol π μ = Gaussian.quarticSymbol μ π *
      (((Int.negOnePow (((μ.norm - 1) / 4) * ((π.norm - 1) / 4)) : ℤˣ) : ℤ) : GaussianInt) :=
  Gaussian.quarticSymbol_reciprocity hπ hμ hcop

theorem gauss_last_entry {p : ℕ} [Fact p.Prime] (hp : p % 4 = 1) :
    ∃ a b : ℤ, (p : ℤ) = a ^ 2 + b ^ 2 ∧ Odd a ∧ Even b ∧ (4 ∣ b → a ≡ 1 [ZMOD 4]) ∧
      (¬4 ∣ b → a ≡ -1 [ZMOD 4]) ∧
      (∀ a' b' : ℤ, (p : ℤ) = a' ^ 2 + b' ^ 2 → Odd a' → Even b' →
        (4 ∣ b' → a' ≡ 1 [ZMOD 4]) → (¬4 ∣ b' → a' ≡ -1 [ZMOD 4]) → a' = a) ∧
      (numLastEntry (ZMod p) : ℤ) = p - 1 - 2 * a :=
  NTKB.IrelandRosen.gauss_last_entry hp

theorem legendre {a b c : ℤ} (hsa : Squarefree a) (hsb : Squarefree b) (hsc : Squarefree c)
    (hab : IsCoprime a b) (hac : IsCoprime a c) (hbc : IsCoprime b c)
    (hpos : ¬ (0 < a ∧ 0 < b ∧ 0 < c)) (hneg : ¬ (a < 0 ∧ b < 0 ∧ c < 0)) :
    Legendre.HasSol a b c ↔
      Legendre.SqMod (-(a * b)) c ∧ Legendre.SqMod (-(a * c)) b ∧ Legendre.SqMod (-(b * c)) a :=
  Legendre.legendre hsa hsb hsc hab hac hbc hpos hneg

theorem sophie_germain {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : (2 * p + 1).Prime) :
    ¬ ∃ x y z : ℤ, x ^ p + y ^ p + z ^ p = 0 ∧ ¬ (p : ℤ) ∣ x * y * z :=
  SophieGermain.sophie_germain hp hp2 hq

theorem cube_eq_two_iff {p : ℕ} (hp : p.Prime) (hp3 : p % 3 = 1) :
    (∃ x : ZMod p, x ^ 3 = 2) ↔ ∃ C D : ℤ, (p : ℤ) = C ^ 2 + 27 * D ^ 2 :=
  Eisenstein.exists_cube_eq_two_iff hp hp3

theorem points_y_sq_eq_x_cube_sub_D_x {p : ℕ} [Fact p.Prime] (hp : p % 4 = 1) {π : GaussianInt}
    (hπ : Gaussian.IsPrimary π) (hπp : π.norm = p) {D : ℤ} (hD : ¬ (p : ℤ) ∣ D) :
    (((1 + (Finset.univ.filter fun xy : ZMod p × ZMod p => xy.2 ^ 2 = xy.1 ^ 3 - D * xy.1).card : ℕ) : ℤ) :
        GaussianInt) =
      p + 1 - star (Gaussian.quarticChar π D) * π - Gaussian.quarticChar π D * star π :=
  numPointsQuarticCurve_eq hp hπ hπp hD

theorem kummer_congruences (p : ℕ) [Fact p.Prime] {e m m' : ℕ} (he : 1 ≤ e)
    (hm : Even m) (hm0 : m ≠ 0) (hm' : Even m') (hm'0 : m' ≠ 0) (hpm : ¬ p - 1 ∣ m)
    (hmm' : m' ≡ m [MOD (p ^ e).totient]) :
    ¬ p ∣ (((1 - (p : ℚ) ^ (m' - 1)) * bernoulli m' / m' -
      (1 - (p : ℚ) ^ (m - 1)) * bernoulli m / m) / (p : ℚ) ^ e).den :=
  kummer_congruence p he hm hm0 hm' hm'0 hpm hmm'

theorem class_number_bernoulli {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) (hp3 : 3 < p) :
    ¬ p ∣ ((-(1 / (p : ℚ)) * ∑ j ∈ Finset.Ico 1 p, (j : ℚ) * legendreSym p j -
      -2 * bernoulli ((p + 1) / 2)) / (p : ℚ)).den :=
  by simpa [PModEq, IsPIntegral, jacobiClassNumber] using jacobiClassNumber_pModEq p hp hp3

theorem class_number_bernoulli_field {K : Type} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
    (hp : p % 4 = 3) (hp3 : 3 < p) (hK : Module.finrank ℚ K = 2) (hD : NumberField.discr K = -p) :
    ¬ p ∣ (((NumberField.classNumber K : ℚ) - -2 * bernoulli ((p + 1) / 2)) / (p : ℚ)).den :=
  by simpa [PModEq, IsPIntegral] using classNumber_pModEq_bernoulli_unconditional hp hp3 hK hD

theorem hecke_character_quartic_curve_split (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    {D : ℤ} (hD : ¬ (((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) : ℤ) ∣ 2 * D) {π : GaussianInt} (hπ : Gaussian.IsPrimary π)
    (hπp : π.norm = ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ)) :
    ((((⟨0, 0, 0, -D, 0⟩ : WeierstrassCurve ℤ).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ)).map (Int.castRingHom GaussianInt) =
      (1 - Polynomial.C (CM.heckeCharQuartic D π) * Polynomial.X) *
        (1 - Polynomial.C (CM.heckeCharQuartic D (star π)) * Polynomial.X) :=
  CM.localPolynomial_quarticCurve_split v hD hπ hπp

theorem hecke_character_quartic_curve_inert (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    {D : ℤ} (hD : ¬ (((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) : ℤ) ∣ 2 * D) (hp3 : ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) % 4 = 3) :
    ((((⟨0, 0, 0, -D, 0⟩ : WeierstrassCurve ℤ).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ)).map (Int.castRingHom GaussianInt) =
      1 - Polynomial.C (CM.heckeCharQuartic D (((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) : GaussianInt)) * Polynomial.X ^ 2 :=
  CM.localPolynomial_quarticCurve_inert v hD hp3

theorem hecke_character_cubic_curve_split (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    {D : ℤ} (hD : ¬ (((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) : ℤ) ∣ 6 * D) {π : NTKB.HardyWright.ZRho} (hπ : Eisenstein.IsPrimary π)
    (hπp : QuadraticAlgebra.norm π = ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ)) :
    ((((⟨0, 0, 0, 0, D⟩ : WeierstrassCurve ℤ).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ)).map (Int.castRingHom NTKB.HardyWright.ZRho) =
      (1 - Polynomial.C (CM.heckeCharSextic D π) * Polynomial.X) *
        (1 - Polynomial.C (CM.heckeCharSextic D (star π)) * Polynomial.X) :=
  CM.localPolynomial_cubicCurve_split v hD hπ hπp

theorem hecke_character_cubic_curve_inert (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    {D : ℤ} (hD : ¬ (((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) : ℤ) ∣ 6 * D) (hp2 : ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) % 3 = 2) :
    ((((⟨0, 0, 0, 0, D⟩ : WeierstrassCurve ℤ).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ)).map (Int.castRingHom NTKB.HardyWright.ZRho) =
      1 - Polynomial.C (CM.heckeCharSextic D (((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) : NTKB.HardyWright.ZRho)) * Polynomial.X ^ 2 :=
  CM.localPolynomial_cubicCurve_inert v hD hp2

theorem mordell_class_number {d : ℤ} [Fact (1 < d)] (hsq : Squarefree d) (h4 : d % 4 = 1 ∨ d % 4 = 2)
    (h3 : ¬ 3 ∣ NumberField.classNumber (QuadraticAlgebra ℚ ((-d : ℤ) : ℚ) 0)) :
    (∃ x y : ℤ, y ^ 2 = x ^ 3 - d) ↔ ∃ t : ℤ, d = 3 * t ^ 2 + 1 ∨ d = 3 * t ^ 2 - 1 :=
  CM.exists_sq_eq_cube_sub_iff_unconditional hsq h4 h3

theorem hecke_character_quartic_curve_bad (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    {D : ℤ} (hD : (((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) : ℤ) ∣ 2 * D) (h12 : ¬ (((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) : ℤ) ^ 12 ∣ 64 * D ^ 3) :
    (((⟨0, 0, 0, -D, 0⟩ : WeierstrassCurve ℤ).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ) = 1 ∧
      ∀ π : GaussianInt, ¬ IsUnit π → π ∣ (((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) : GaussianInt) → CM.heckeCharQuartic D π = 0 :=
  ⟨CM.localPolynomial_quarticCurve_eq_one v hD h12, fun _ hπ hπp =>
    CM.heckeCharQuartic_eq_zero_of_dvd hπ (hπp.trans (by exact_mod_cast CM.intCast_dvd_of_dvd (A := GaussianInt) hD))⟩

theorem hecke_character_cubic_curve_bad (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    {D : ℤ} (hD : (((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) : ℤ) ∣ 6 * D) (h12 : ¬ (((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) : ℤ) ^ 12 ∣ 432 * D ^ 2) :
    (((⟨0, 0, 0, 0, D⟩ : WeierstrassCurve ℤ).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ) = 1 ∧
      ∀ π : NTKB.HardyWright.ZRho, ¬ IsUnit π → π ∣ (((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) : NTKB.HardyWright.ZRho) →
        CM.heckeCharSextic D π = 0 :=
  ⟨CM.localPolynomial_cubicCurve_eq_one v hD h12, fun _ hπ hπp =>
    CM.heckeCharSextic_eq_zero_of_dvd hπ
      (hπp.trans (by exact_mod_cast CM.intCast_dvd_of_dvd (A := NTKB.HardyWright.ZRho) hD))⟩

theorem infinite_points_mordell (hin : CM.MordellTorsionInput) {k : ℤ} (hk0 : k ≠ 0)
    (hk : ∀ d : ℤ, d ^ 6 ∣ k → IsUnit d) (hk1 : k ≠ 1) (hk432 : k ≠ -432) {x y : ℚ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : y ^ 2 = x ^ 3 + k) :
    {p : ℚ × ℚ | p.2 ^ 2 = p.1 ^ 3 + k}.Infinite :=
  CM.infinite_points_mordell_of_input hin hk0 hk hk1 hk432 hx hy hxy

theorem infinite_points_sum_cubes (hin : CM.MordellTorsionInput) {a : ℤ} (ha : 2 < a)
    (hcf : ∀ d : ℤ, d ^ 3 ∣ a → IsUnit d) {x y : ℚ} (hxy : x ^ 3 + y ^ 3 = a) :
    {p : ℚ × ℚ | p.1 ^ 3 + p.2 ^ 3 = a}.Infinite :=
  CM.infinite_points_sum_cubes_of_input hin ha hcf hxy

end NTKB.Headlines.IrelandRosen
