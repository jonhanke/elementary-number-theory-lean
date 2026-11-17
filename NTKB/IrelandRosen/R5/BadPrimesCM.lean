/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.IrelandRosen.R5.BadPrimes
import NTKB.IrelandRosen.R5.HeckeGaussian
import NTKB.IrelandRosen.R5.HeckeEisenstein

/-!
# Theorems 7 and 8 of Ireland–Rosen, Chapter 18, at the primes dividing `2D` (resp. `6D`)

The Hecke characters `heckeCharQuartic D` and `heckeCharSextic D` are `0` on the elements not prime
to `2D` (resp. `6D`), so the Euler factor of `L(s, χ)` at a prime above `p ∣ 2D` (resp. `6D`) is `1`.
Mathlib's local polynomial of `E` at `p` is also `1` when the reduction of a minimal model is
additive; by `localPolynomial_rat_eq_one` this holds as soon as `p ∣ c₄` and `p¹² ∤ Δ`:

* `y² = x³ - Dx` (`Δ = 64 D³`, `c₄ = 48 D`): at every `p ∣ 2D` with `p¹² ∤ 64 D³`, that is,
  `p⁴ ∤ D` for odd `p` and `4 ∤ D` for `p = 2` (`localPolynomial_quarticCurve_eq_one`,
  `localPolynomial_quarticCurve_split_of_dvd`, `localPolynomial_quarticCurve_inert_of_dvd`);
* `y² = x³ + D` (`Δ = -432 D²`, `c₄ = 0`): at every `p ∣ 6D` with `p¹² ∤ 432 D²`, that is,
  `p⁶ ∤ D` for `p ≥ 5`, `16 ∤ D` for `p = 2` and `3⁵ ∤ D` for `p = 3`
  (`localPolynomial_cubicCurve_eq_one`, `localPolynomial_cubicCurve_split_of_dvd`,
  `localPolynomial_cubicCurve_inert_of_dvd`).

Not covered: `p = 2` with `v₂(D) ∈ {2, 3}` for `y² = x³ - Dx`, and `p = 2`
with `v₂(D) ∈ {4, 5}`, `p = 3` with `v₃(D) = 5` for `y² = x³ + D` (there `p¹² ∣ Δ` and Tate's
algorithm is needed; for `D = -432` the curve `y² = x³ - 432` even has good reduction at `2`), and
`D` not fourth-power free (resp. sixth-power free) at `p`, where the model is not minimal.
-/

namespace NTKB.IrelandRosen.CM

open Polynomial NTKB.HardyWright IsDedekindDomain NumberField

/-! ### The invariants -/

lemma quarticCurve_c₄ (D : ℤ) : (quarticCurve D).c₄ = 48 * D := by
  simp only [quarticCurve, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

lemma cubicCurve_c₄ (D : ℤ) : (cubicCurve D).c₄ = 0 := by
  simp only [cubicCurve, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

/-! ### The local polynomials -/

variable (v : HeightOneSpectrum (𝓞 ℚ))

/-- **`y² = x³ - Dx` at a prime of additive reduction.** For `p ∣ 2D` with `p¹² ∤ 64 D³`, Mathlib's
local polynomial at `p` is `1`. -/
theorem localPolynomial_quarticCurve_eq_one {D : ℤ} (hpD : (placePrime v : ℤ) ∣ 2 * D)
    (h12 : ¬ (placePrime v : ℤ) ^ 12 ∣ 64 * D ^ 3) :
    (((quarticCurve D).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ) = 1 := by
  refine localPolynomial_rat_eq_one v _ ?_ ?_ ?_
  · rw [quarticCurve_Δ]
    exact dvd_trans hpD ⟨32 * D ^ 2, by ring⟩
  · rw [quarticCurve_c₄]
    exact dvd_trans hpD ⟨24, by ring⟩
  · rwa [quarticCurve_Δ]

/-- **`y² = x³ + D` at a prime of additive reduction.** For `p ∣ 6D` with `p¹² ∤ 432 D²`, Mathlib's
local polynomial at `p` is `1`. -/
theorem localPolynomial_cubicCurve_eq_one {D : ℤ} (hpD : (placePrime v : ℤ) ∣ 6 * D)
    (h12 : ¬ (placePrime v : ℤ) ^ 12 ∣ 432 * D ^ 2) :
    (((cubicCurve D).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ) = 1 := by
  refine localPolynomial_rat_eq_one v _ ?_ ?_ ?_
  · rw [cubicCurve_Δ]
    exact dvd_trans hpD ⟨-72 * D, by ring⟩
  · rw [cubicCurve_c₄]; exact dvd_zero _
  · rw [cubicCurve_Δ]
    intro h
    exact h12 (by
      obtain ⟨c, hc⟩ := h
      exact ⟨-c, by linear_combination -hc⟩)

/-! ### The characters at the primes dividing `2D` (resp. `6D`) -/

/-- `χ(α) = 0` for a non-unit `α ∣ 2D`. -/
lemma heckeCharQuartic_eq_zero_of_dvd {D : ℤ} {α : GaussianInt} (hα : ¬ IsUnit α)
    (hd : α ∣ (2 * D : GaussianInt)) : heckeCharQuartic D α = 0 :=
  heckeCharQuartic_of_not_isCoprime fun h => hα (h.isUnit_of_dvd' dvd_rfl hd)

local notation "ℤ[ω]" => NTKB.HardyWright.ZRho

/-- `χ(α) = 0` for a non-unit `α ∣ 6D`. -/
lemma heckeCharSextic_eq_zero_of_dvd {D : ℤ} {α : ℤ[ω]} (hα : ¬ IsUnit α)
    (hd : α ∣ (6 * D : ℤ[ω])) : heckeCharSextic D α = 0 := by
  classical
  rw [heckeCharSextic, if_neg fun h => hα (h.isUnit_of_dvd' dvd_rfl hd)]

lemma intCast_dvd_of_dvd {A : Type*} [CommRing A] {p n : ℤ} (h : p ∣ n) : (p : A) ∣ (n : A) := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨c, by push_cast; ring⟩

/-- **Theorem 7 of Chapter 18 at a split prime dividing `2D`.** For `p ∣ 2D` with `p¹² ∤ 64 D³` and
`π, π̄` non-units dividing `p` in `ℤ[i]`, the local polynomial of `y² = x³ - Dx` at `p` is the
Euler factor `(1 - χ(π) X)(1 - χ(π̄) X) = 1` of `L(s, χ)`. -/
theorem localPolynomial_quarticCurve_split_of_dvd {D : ℤ} (hpD : (placePrime v : ℤ) ∣ 2 * D)
    (h12 : ¬ (placePrime v : ℤ) ^ 12 ∣ 64 * D ^ 3) {π : GaussianInt} (hπ : ¬ IsUnit π)
    (hπp : π ∣ (placePrime v : GaussianInt)) (hπ' : ¬ IsUnit (star π))
    (hπp' : star π ∣ (placePrime v : GaussianInt)) :
    ((((quarticCurve D).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ)).map (Int.castRingHom GaussianInt) =
      (1 - C (heckeCharQuartic D π) * X) * (1 - C (heckeCharQuartic D (star π)) * X) := by
  have hp : ((placePrime v : ℤ) : GaussianInt) ∣ ((2 * D : ℤ) : GaussianInt) := intCast_dvd_of_dvd hpD
  push_cast at hp
  rw [localPolynomial_quarticCurve_eq_one v hpD h12, heckeCharQuartic_eq_zero_of_dvd hπ (hπp.trans hp),
    heckeCharQuartic_eq_zero_of_dvd hπ' (hπp'.trans hp)]
  simp

/-- **Theorem 7 of Chapter 18 at an inert prime dividing `D`.** For `p ∣ 2D` with `p¹² ∤ 64 D³` and
`p` not a unit of `ℤ[i]`, the local polynomial is `1 - χ((p)) X² = 1`. -/
theorem localPolynomial_quarticCurve_inert_of_dvd {D : ℤ} (hpD : (placePrime v : ℤ) ∣ 2 * D)
    (h12 : ¬ (placePrime v : ℤ) ^ 12 ∣ 64 * D ^ 3) (hpu : ¬ IsUnit (placePrime v : GaussianInt)) :
    ((((quarticCurve D).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ)).map (Int.castRingHom GaussianInt) =
      1 - C (heckeCharQuartic D (placePrime v : GaussianInt)) * X ^ 2 := by
  have hp : ((placePrime v : ℤ) : GaussianInt) ∣ ((2 * D : ℤ) : GaussianInt) := intCast_dvd_of_dvd hpD
  push_cast at hp
  rw [localPolynomial_quarticCurve_eq_one v hpD h12, heckeCharQuartic_eq_zero_of_dvd hpu hp]
  simp

/-- **Theorem 8 of Chapter 18 at a split prime dividing `6D`.** For `p ∣ 6D` with `p¹² ∤ 432 D²` and
`π, π̄` non-units dividing `p` in `ℤ[ω]`, the local polynomial of `y² = x³ + D` at `p` is the
Euler factor `(1 - χ(π) X)(1 - χ(π̄) X) = 1` of `L(s, χ)`. -/
theorem localPolynomial_cubicCurve_split_of_dvd {D : ℤ} (hpD : (placePrime v : ℤ) ∣ 6 * D)
    (h12 : ¬ (placePrime v : ℤ) ^ 12 ∣ 432 * D ^ 2) {π : ℤ[ω]} (hπ : ¬ IsUnit π)
    (hπp : π ∣ (placePrime v : ℤ[ω])) (hπ' : ¬ IsUnit (star π))
    (hπp' : star π ∣ (placePrime v : ℤ[ω])) :
    ((((cubicCurve D).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ)).map (Int.castRingHom ℤ[ω]) =
      (1 - C (heckeCharSextic D π) * X) * (1 - C (heckeCharSextic D (star π)) * X) := by
  have hp : ((placePrime v : ℤ) : ℤ[ω]) ∣ ((6 * D : ℤ) : ℤ[ω]) := intCast_dvd_of_dvd hpD
  push_cast at hp
  rw [localPolynomial_cubicCurve_eq_one v hpD h12, heckeCharSextic_eq_zero_of_dvd hπ (hπp.trans hp),
    heckeCharSextic_eq_zero_of_dvd hπ' (hπp'.trans hp)]
  simp

/-- **Theorem 8 of Chapter 18 at an inert prime dividing `6D`.** For `p ∣ 6D` with `p¹² ∤ 432 D²`
and `p` not a unit of `ℤ[ω]`, the local polynomial is `1 - χ((p)) X² = 1`. -/
theorem localPolynomial_cubicCurve_inert_of_dvd {D : ℤ} (hpD : (placePrime v : ℤ) ∣ 6 * D)
    (h12 : ¬ (placePrime v : ℤ) ^ 12 ∣ 432 * D ^ 2) (hpu : ¬ IsUnit (placePrime v : ℤ[ω])) :
    ((((cubicCurve D).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ)).map (Int.castRingHom ℤ[ω]) =
      1 - C (heckeCharSextic D (placePrime v : ℤ[ω])) * X ^ 2 := by
  have hp : ((placePrime v : ℤ) : ℤ[ω]) ∣ ((6 * D : ℤ) : ℤ[ω]) := intCast_dvd_of_dvd hpD
  push_cast at hp
  rw [localPolynomial_cubicCurve_eq_one v hpD h12, heckeCharSextic_eq_zero_of_dvd hpu hp]
  simp

/-! ### The condition `p¹² ∤ Δ` in terms of `D` -/

lemma coprime_pow_of_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (a b : ℕ) :
    IsCoprime ((p : ℤ) ^ a) ((q : ℤ) ^ b) := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  have : Nat.Coprime (p ^ a) (q ^ b) :=
    Nat.Coprime.pow a b ((Nat.coprime_primes hp hq).2 hpq)
  simpa [Int.gcd, Int.natAbs_pow] using this

/-- For odd `p` with `p⁴ ∤ D`: `p¹² ∤ 64 D³`. -/
lemma not_dvd_quartic_Δ_of_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {D : ℤ}
    (h4 : ¬ (p : ℤ) ^ 4 ∣ D) : ¬ (p : ℤ) ^ 12 ∣ 64 * D ^ 3 := by
  intro h
  have hc : IsCoprime ((p : ℤ) ^ 12) ((2 : ℕ) ^ 6 : ℤ) :=
    by simpa using coprime_pow_of_prime hp Nat.prime_two hp2 12 6
  have h' : (p : ℤ) ^ 12 ∣ D ^ 3 := hc.dvd_of_dvd_mul_left (by norm_num; exact h)
  rw [show (12 : ℕ) = 4 * 3 from rfl, pow_mul, Int.pow_dvd_pow_iff (by norm_num)] at h'
  exact h4 h'

/-- For `p = 2` with `4 ∤ D`: `2¹² ∤ 64 D³`. -/
lemma not_dvd_quartic_Δ_two {D : ℤ} (h4 : ¬ (4 : ℤ) ∣ D) : ¬ (2 : ℤ) ^ 12 ∣ 64 * D ^ 3 := by
  intro h
  have h' : (2 : ℤ) ^ 6 ∣ D ^ 3 := by
    obtain ⟨c, hc⟩ := h
    exact ⟨c, by linarith⟩
  rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, Int.pow_dvd_pow_iff (by norm_num)] at h'
  exact h4 (by simpa using h')

/-- For `p ≥ 5` with `p⁶ ∤ D`: `p¹² ∤ 432 D²`. -/
lemma not_dvd_cubic_Δ_of_ge_five {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) {D : ℤ}
    (h6 : ¬ (p : ℤ) ^ 6 ∣ D) : ¬ (p : ℤ) ^ 12 ∣ 432 * D ^ 2 := by
  intro h
  have hc2 : IsCoprime ((p : ℤ) ^ 12) ((2 : ℕ) ^ 4 : ℤ) :=
    by simpa using coprime_pow_of_prime hp Nat.prime_two hp2 12 4
  have hc3 : IsCoprime ((p : ℤ) ^ 12) ((3 : ℕ) ^ 3 : ℤ) :=
    by simpa using coprime_pow_of_prime hp Nat.prime_three hp3 12 3
  have hc : IsCoprime ((p : ℤ) ^ 12) 432 := by
    have := hc2.mul_right hc3
    norm_num at this
    exact this
  have h' : (p : ℤ) ^ 12 ∣ D ^ 2 := hc.dvd_of_dvd_mul_left h
  rw [show (12 : ℕ) = 6 * 2 from rfl, pow_mul, Int.pow_dvd_pow_iff (by norm_num)] at h'
  exact h6 h'

/-- **Theorem 7 of Chapter 18 at an odd prime `p ∣ D`, `D` fourth-power free at `p`**: the local
polynomial is `1`. -/
theorem localPolynomial_quarticCurve_eq_one_of_odd {D : ℤ} (hp2 : placePrime v ≠ 2)
    (hpD : (placePrime v : ℤ) ∣ D) (h4 : ¬ (placePrime v : ℤ) ^ 4 ∣ D) :
    (((quarticCurve D).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ) = 1 :=
  localPolynomial_quarticCurve_eq_one v (dvd_mul_of_dvd_right hpD 2)
    (not_dvd_quartic_Δ_of_odd Fact.out hp2 h4)

/-- **Theorem 7 of Chapter 18 at `p = 2` for `4 ∤ D`**: the local polynomial is `1`. -/
theorem localPolynomial_quarticCurve_eq_one_of_two {D : ℤ} (hp2 : placePrime v = 2)
    (h4 : ¬ (4 : ℤ) ∣ D) :
    (((quarticCurve D).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ) = 1 := by
  refine localPolynomial_quarticCurve_eq_one v ?_ ?_
  · rw [hp2]; exact ⟨D, by push_cast; ring⟩
  · rw [hp2]; exact_mod_cast not_dvd_quartic_Δ_two h4

/-- **Theorem 8 of Chapter 18 at a prime `p ≥ 5`, `p ∣ D`, `D` sixth-power free at `p`**: the
local polynomial is `1`. -/
theorem localPolynomial_cubicCurve_eq_one_of_ge_five {D : ℤ} (hp2 : placePrime v ≠ 2)
    (hp3 : placePrime v ≠ 3) (hpD : (placePrime v : ℤ) ∣ D) (h6 : ¬ (placePrime v : ℤ) ^ 6 ∣ D) :
    (((cubicCurve D).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ) = 1 :=
  localPolynomial_cubicCurve_eq_one v (dvd_mul_of_dvd_right hpD 6)
    (not_dvd_cubic_Δ_of_ge_five Fact.out hp2 hp3 h6)

end NTKB.IrelandRosen.CM
