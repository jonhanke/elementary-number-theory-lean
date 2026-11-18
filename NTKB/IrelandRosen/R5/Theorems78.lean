/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.IrelandRosen.R5.EveryPrime

/-!
# Theorems 7 and 8 of Ireland–Rosen, Chapter 18, at every prime

For `y² = x³ - c⁴Dx` with `D` fourth-power free (resp. `y² = x³ + c⁶D` with `D` sixth-power free),
Mathlib's local polynomial at **every** prime `p` (the factor of `WeierstrassCurve.LFunction`) is
compared with the Euler factor of `L(s, χ)` at the primes above `p`, `χ` the Hecke character of
`D` (Ireland–Rosen, Chapter 18, §5): `(1 - χ(π) X)(1 - χ(π̄) X)` for `p = π π̄` split,
`1 - χ((p)) X²` for `p` inert, and `1` for `p ∣ 2D` (resp. `p ∣ 6D`), where `χ` vanishes.

* `theorem7_localPolynomial_everyPrime`: for `y² = x³ - c⁴Dx` the comparison holds at every
  prime.
* `theorem8_localPolynomial_everyPrime`: for `y² = x³ + c⁶D` the comparison holds at every prime
  except `p = 2` with `D ≡ 16 (mod 64)`; there the curve has good reduction and the local
  polynomial is `1 + 2X²` (`localPolynomial_cubicCurve_two_good`), the Euler factor at the inert
  prime `2` of norm `4` of the character with `χ((2)) = -2`: the book's character, defined modulo
  `12D`, is imprimitive at `2` for these `D` (for example `D = -432`, the curve `x³ + y³ = 1`).

The character is that of the power-free part `D`, not of `c⁴D` (resp. `c⁶D`): the curves are
isomorphic over `ℚ` (`localPolynomial_quarticCurve_pow_four_mul`), and at the primes dividing `c`
but not `2D` the curve has good reduction while the character of `c⁴D` vanishes.

The book compares the factors at the primes not dividing `2D` (resp. `6D`) only.
-/

namespace NTKB.IrelandRosen.CM

open Polynomial IsDedekindDomain NumberField QuadraticAlgebra

local notation "ℤ[ω]" => NTKB.HardyWright.ZRho

variable (v : HeightOneSpectrum (𝓞 ℚ))

lemma not_dvd_cubic_Δ_two {D : ℤ} (h16 : ¬ (16 : ℤ) ∣ D) : ¬ (2 : ℤ) ^ 12 ∣ 432 * D ^ 2 := by
  rintro ⟨k, hk⟩
  have h256 : (256 : ℤ) ∣ 27 * D ^ 2 := ⟨k, by linarith⟩
  have hc : IsCoprime (256 : ℤ) 27 := by
    rw [Int.isCoprime_iff_gcd_eq_one]; rfl
  have h' : ((2 : ℤ) ^ 4) ^ 2 ∣ D ^ 2 := by
    have := hc.dvd_of_dvd_mul_left h256
    norm_num; exact this
  rw [Int.pow_dvd_pow_iff (by norm_num)] at h'
  exact h16 (by norm_num at h'; exact h')

lemma dvd_of_dvd_mul_of_ne {p : ℕ} (hp : p.Prime) {a D : ℤ} (ha : ¬ (p : ℤ) ∣ a)
    (h : (p : ℤ) ∣ a * D) : (p : ℤ) ∣ D := by
  rcases (Nat.prime_iff_prime_int.1 hp).dvd_or_dvd h with h' | h'
  · exact absurd h' ha
  · exact h'

/-- **Ireland–Rosen, Chapter 18, Theorem 7, at every prime.** Let `D` be fourth-power free,
`c ≠ 0`, `E : y² = x³ - c⁴Dx`, `χ = heckeCharQuartic D`. At every finite place `v` above `p`,
Mathlib's local polynomial of `E` (the factor of `WeierstrassCurve.LFunction`) is the Euler factor
of `L(s, χ)` at the primes above `p`: `1` if `p ∣ 2D`; `(1 - χ(π) X)(1 - χ(π̄) X)` if `p = π π̄`
splits (`π` primary); `1 - χ((p)) X²` if `p ≡ 3 (mod 4)` is inert. -/
@[kb "irelandrosen1990" "Ch. 18, §5, Theorem 7, p. 322"]
theorem theorem7_localPolynomial_everyPrime {c D : ℤ} (hc : c ≠ 0) (hD : D ≠ 0)
    (hfree : ∀ p : ℕ, p.Prime → ¬ (p : ℤ) ^ 4 ∣ D) :
    ((placePrime v : ℤ) ∣ 2 * D →
      (((quarticCurve (c ^ 4 * D)).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ) = 1) ∧
    (∀ π : GaussianInt, Gaussian.IsPrimary π → π.norm = placePrime v →
      ¬ (placePrime v : ℤ) ∣ 2 * D →
      ((((quarticCurve (c ^ 4 * D)).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ)).map (Int.castRingHom GaussianInt) =
        (1 - C (heckeCharQuartic D π) * X) * (1 - C (heckeCharQuartic D (star π)) * X)) ∧
    (placePrime v % 4 = 3 → ¬ (placePrime v : ℤ) ∣ 2 * D →
      ((((quarticCurve (c ^ 4 * D)).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ)).map (Int.castRingHom GaussianInt) =
        1 - C (heckeCharQuartic D (placePrime v : GaussianInt)) * X ^ 2) := by
  rw [localPolynomial_quarticCurve_pow_four_mul v hc hD]
  refine ⟨fun hpD => ?_, fun π hπ hπp hpD => localPolynomial_quarticCurve_split v hpD hπ hπp,
    fun hp3 hpD => localPolynomial_quarticCurve_inert v hpD hp3⟩
  have hp : (placePrime v).Prime := Fact.out
  by_cases hp2 : placePrime v = 2
  · by_cases h4 : (4 : ℤ) ∣ D
    · have h16 : ¬ (16 : ℤ) ∣ D := by
        have := hfree 2 Nat.prime_two; norm_num at this; exact this
      exact localPolynomial_quarticCurve_eq_one_of_two_of_four_dvd v hp2 h4 h16
    · exact localPolynomial_quarticCurve_eq_one_of_two v hp2 h4
  · have h2 : ¬ (placePrime v : ℤ) ∣ 2 := by
      intro h
      have : placePrime v ∣ 2 := by exact_mod_cast h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
    exact localPolynomial_quarticCurve_eq_one_of_odd v hp2 (dvd_of_dvd_mul_of_ne hp h2 hpD)
      (hfree _ hp)

/-- **Ireland–Rosen, Chapter 18, Theorem 8, at every prime.** Let `D` be sixth-power free,
`c ≠ 0`, `E : y² = x³ + c⁶D`, `χ = heckeCharSextic D`. At every finite place `v` above `p`,
Mathlib's local polynomial of `E` is the Euler factor of `L(s, χ)` at the primes above `p`: `1` if
`p ∣ 6D`, except at `p = 2` for `D ≡ 16 (mod 64)` where it is `1 + 2X²` (good reduction, the
book's character being imprimitive there); `(1 - χ(π) X)(1 - χ(π̄) X)` if `p = π π̄` splits
(`π` primary); `1 - χ((p)) X²` if `p ≡ 2 (mod 3)` is inert. -/
@[kb "irelandrosen1990" "Ch. 18, §5, Theorem 8, p. 323"]
theorem theorem8_localPolynomial_everyPrime {c D : ℤ} (hc : c ≠ 0) (hD : D ≠ 0)
    (hfree : ∀ p : ℕ, p.Prime → ¬ (p : ℤ) ^ 6 ∣ D) :
    ((placePrime v : ℤ) ∣ 6 * D → ¬ (placePrime v = 2 ∧ D % 64 = 16) →
      (((cubicCurve (c ^ 6 * D)).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ) = 1) ∧
    (placePrime v = 2 → D % 64 = 16 →
      (((cubicCurve (c ^ 6 * D)).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ) = 1 + C 2 * X ^ 2) ∧
    (∀ π : ℤ[ω], Eisenstein.IsPrimary π → norm π = placePrime v →
      ¬ (placePrime v : ℤ) ∣ 6 * D →
      ((((cubicCurve (c ^ 6 * D)).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ)).map (Int.castRingHom ℤ[ω]) =
        (1 - C (heckeCharSextic D π) * X) * (1 - C (heckeCharSextic D (star π)) * X)) ∧
    (placePrime v % 3 = 2 → ¬ (placePrime v : ℤ) ∣ 6 * D →
      ((((cubicCurve (c ^ 6 * D)).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ)).map (Int.castRingHom ℤ[ω]) =
        1 - C (heckeCharSextic D (placePrime v : ℤ[ω])) * X ^ 2) := by
  rw [localPolynomial_cubicCurve_pow_six_mul v hc hD]
  refine ⟨fun hpD hex => ?_, fun hp2 h16 => localPolynomial_cubicCurve_two_good v hp2 h16,
    fun π hπ hπp hpD => localPolynomial_cubicCurve_split v hpD hπ hπp,
    fun hp3 hpD => localPolynomial_cubicCurve_inert v hpD hp3⟩
  have hp : (placePrime v).Prime := Fact.out
  by_cases hp2 : placePrime v = 2
  · have h64 : ¬ (64 : ℤ) ∣ D := by
      have := hfree 2 Nat.prime_two; norm_num at this; exact this
    by_cases h16 : (16 : ℤ) ∣ D
    · have hmod : D % 64 = 32 ∨ D % 64 = 48 := by
        have hne : D % 64 ≠ 16 := fun h => hex ⟨hp2, h⟩
        omega
      exact localPolynomial_cubicCurve_eq_one_of_two_of_mod v hp2 hmod
    · refine localPolynomial_cubicCurve_eq_one v hpD ?_
      rw [hp2]; exact_mod_cast not_dvd_cubic_Δ_two h16
  by_cases hp3 : placePrime v = 3
  · have h729 : ¬ (729 : ℤ) ∣ D := by
      have := hfree 3 Nat.prime_three; norm_num at this; exact this
    exact localPolynomial_cubicCurve_eq_one_of_three v hp3 h729
  · have h6 : ¬ (placePrime v : ℤ) ∣ 6 := by
      intro h
      have h' : placePrime v ∣ 2 * 3 := by exact_mod_cast h
      rcases (Nat.Prime.dvd_mul hp).1 h' with h'' | h''
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h'')
      · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h'')
    exact localPolynomial_cubicCurve_eq_one_of_ge_five v hp2 hp3 (dvd_of_dvd_mul_of_ne hp h6 hpD)
      (hfree _ hp)

end NTKB.IrelandRosen.CM
