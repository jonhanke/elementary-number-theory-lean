/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.IrelandRosen.R5.Theorems78
import NTKB.IrelandRosen.R5.LFunctionRat
import NTKB.IrelandRosen.R5.HeckeSumGaussian
import NTKB.IrelandRosen.R5.HeckeSumEisenstein

/-!
# Theorems 7 and 8 of Ireland–Rosen, Chapter 18: `L(E, s) = L(s, χ)` as Dirichlet series

The global identity of formal Dirichlet series between Mathlib's `L`-function of the curve
(`WeierstrassCurve.LFunction`, the Euler product over all finite places of `ℚ`) and the Hecke
`L`-series `L(s, χ) = ∑_A χ(A) N(A)^{-s}` over the nonzero ideals `A` of `ℤ[i]` (resp. `ℤ[ω]`).
Each ideal has `4` (resp. `6`) generators and `χ` is a function of the ideal, so the `n`-th
coefficient of `L(s, χ)` is `(1/4) ∑_{N(α) = n} χ(α)` (resp. `(1/6) ∑_{N(α) = n} χ(α)`); we state
the identities with the factor `4` (resp. `6`) on the side of `L(E, s)`, in `ℤ[i]` (resp. `ℤ[ω]`).

* `theorem7_LFunction`: for `E : y² = x³ - c⁴Dx`, `D` fourth-power free, `c ≠ 0`, and every `n`,
  `4 a_E(n) = ∑_{α ∈ ℤ[i], N(α) = n} χ(α)`, `χ = heckeCharQuartic D`.
* `theorem8_LFunction`: for `E : y² = x³ + c⁶D`, `D` sixth-power free, `c ≠ 0`, `D ≢ 16 (mod 64)`,
  and every `n`, `6 a_E(n) = ∑_{α ∈ ℤ[ω], N(α) = n} χ(α)`, `χ = heckeCharSextic D`.
* `theorem8_LFunction_odd`: the same for every `D` and every odd `n`.
* `theorem8_LFunction_sixteen`: for `D ≡ 16 (mod 64)` the factor at `2` is `1 / (1 + 2·4^{-s})`:
  `6 a_E(4^j m) = (-2)^j ∑_{N(α) = m} χ(α)` and `a_E(2·4^j m) = 0` for odd `m`; that is,
  `L(E, s) = L(s, χ₀)` for the character `χ₀` equal to `χ` away from `2` with `χ₀((2)) = -2`.

The proof does not use unique factorization into ideals: both sides satisfy the same recursion at
every prime `p ∣ n` (`LFunction_recursion` for the curve, from the local polynomials at every prime
`theorem7_localPolynomial_everyPrime`, `theorem8_localPolynomial_everyPrime`; and
`heckeSumQuartic_split`, `heckeSumQuartic_inert`, ... for the character), so they agree by strong
induction on `n` (`eq_of_recursion`).
-/

namespace NTKB.IrelandRosen.CM

open Polynomial IsDedekindDomain NumberField ArithmeticFunction QuadraticAlgebra

local notation "ℤ[ω]" => NTKB.HardyWright.ZRho

/-- The finite place of `ℚ` above the prime `p`. -/
noncomputable def placeOf (p : ℕ) (hp : p.Prime) : HeightOneSpectrum (𝓞 ℚ) :=
  Rat.HeightOneSpectrum.primesEquiv.symm ⟨p, hp⟩

lemma placePrime_placeOf (p : ℕ) (hp : p.Prime) : placePrime (placeOf p hp) = p := by
  simp only [placeOf, placePrime]
  exact congrArg Subtype.val (Equiv.apply_symm_apply _ _)

lemma odd_div_of_dvd {n p : ℕ} (hn : Odd n) (hp : p ∣ n) : Odd (n / p) := by
  obtain ⟨k, rfl⟩ := hp
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · simp at hn
  · rw [Nat.mul_div_cancel_left _ hp0]
    exact (Nat.odd_mul.1 hn).2

/-- **Comparison by recursion.** Let `F : ℕ → S` with `F 0 = 0`, `F 1 = c`, and suppose that for
every prime `p` dividing `n` (with `n` in a set `P` closed under division) the local polynomial of
`W` at `p`, mapped to `S`, is `1 - s X + t X²` with `F n = s F(n/p) - t F(n/p²)` (the last term
`0` when `p² ∤ n`). Then `c a_W(n) = F n` for every `n` in `P`. -/
theorem eq_of_recursion {S : Type*} [CommRing S] (W : WeierstrassCurve ℚ) (c : S) (F : ℕ → S)
    (P : ℕ → Prop) (hP : ∀ n p, P n → p ∣ n → P (n / p)) (h0 : F 0 = 0) (h1 : F 1 = c)
    (hrec : ∀ n p (hp : p.Prime), P n → p ∣ n → ∃ s t : S,
      (ratLocalPolynomial W (placeOf p hp)).map (Int.castRingHom S) =
          1 - C s * X + C t * X ^ 2 ∧
        F n = s * F (n / p) - if p ^ 2 ∣ n then t * F (n / p ^ 2) else 0) :
    ∀ n, P n → c * (W.LFunction n : S) = F n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · interval_cases n
      · simp [h0]
      · simp [(LFunction_isMultiplicative W).map_one, h1]
    · have hn1 : n ≠ 1 := by omega
      have hn0 : n ≠ 0 := by omega
      set p := n.minFac with hpdef
      have hp : p.Prime := Nat.minFac_prime hn1
      have hpn : p ∣ n := Nat.minFac_dvd n
      obtain ⟨s, t, hpoly, hF⟩ := hrec n p hp hn hpn
      have hrecW := LFunction_recursion W (placeOf p hp) s t hpoly hn0
        (by rw [placePrime_placeOf]; exact hpn)
      rw [placePrime_placeOf] at hrecW
      have hp2 : 2 ≤ p := hp.two_le
      have hlt1 : n / p < n := Nat.div_lt_self (by omega) (by omega)
      have IH1 := ih (n / p) hlt1 (hP n p hn hpn)
      rw [hrecW, hF, mul_sub, ← mul_assoc, mul_comm c s, mul_assoc, IH1]
      congr 1
      split_ifs with h2
      · have hlt2 : n / p ^ 2 < n := Nat.div_lt_self (by omega) (by nlinarith)
        have hP2 : P (n / p ^ 2) := by
          have := hP (n / p) p (hP n p hn hpn) ((Nat.dvd_div_iff_mul_dvd hpn).2 (by
            rw [← pow_two]; exact h2))
          rwa [Nat.div_div_eq_div_mul, ← pow_two] at this
        rw [← mul_assoc, mul_comm c t, mul_assoc, ih _ hlt2 hP2]
      · simp

lemma prime_mod_four {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : p % 4 = 1 ∨ p % 4 = 3 := by
  have := hp.eq_one_or_self_of_dvd 2
  have hodd : p % 2 = 1 := by
    rcases Nat.even_or_odd p with h | h
    · exact absurd ((hp.even_iff).1 h) h2
    · exact Nat.odd_iff.1 h
  omega

/-- **Ireland–Rosen, Chapter 18, Theorem 7: `L(E, s) = L(s, χ)`.** Let `D` be fourth-power free,
`c ≠ 0`, `E : y² = x³ - c⁴Dx` and `χ = heckeCharQuartic D`. For every `n`, four times the `n`-th
coefficient of Mathlib's `L`-function of `E` is `∑_{α ∈ ℤ[i], N(α) = n} χ(α)`, i.e. four times the
`n`-th coefficient of `L(s, χ) = ∑_A χ(A) N(A)^{-s}`. -/
@[kb "irelandrosen1990" "Ch. 18, §5, Theorem 7, p. 322"]
theorem theorem7_LFunction {c D : ℤ} (hc : c ≠ 0) (hD : D ≠ 0)
    (hfree : ∀ p : ℕ, p.Prime → ¬ (p : ℤ) ^ 4 ∣ D) (n : ℕ) :
    (4 : GaussianInt) * (((quarticCurve (c ^ 4 * D)).baseChange ℚ).LFunction n : GaussianInt) =
      heckeSumQuartic D n := by
  refine eq_of_recursion _ 4 (heckeSumQuartic D) (fun _ => True) (fun _ _ _ _ => trivial)
    (heckeSumQuartic_zero D) (heckeSumQuartic_one D) ?_ n trivial
  intro n p hp _ hpn
  have hv : placePrime (placeOf p hp) = p := placePrime_placeOf p hp
  obtain ⟨h1, h2, h3⟩ := theorem7_localPolynomial_everyPrime (placeOf p hp) hc hD hfree
  rw [hv] at h1 h2 h3
  by_cases hbad : (p : ℤ) ∣ 2 * D
  · refine ⟨0, 0, ?_, ?_⟩
    · rw [ratLocalPolynomial, h1 hbad]; simp
    · rw [heckeSumQuartic_of_dvd_two_mul hp hbad hpn]; simp
  · have hp2 : p ≠ 2 := prime_ne_two_of_not_dvd hbad
    rcases prime_mod_four hp hp2 with h | h
    · have := Fact.mk hp
      obtain ⟨π, hπ, hπp⟩ := NTKB.IrelandRosen.exists_isPrimary_norm_eq h
      refine ⟨heckeCharQuartic D π + heckeCharQuartic D (star π),
        heckeCharQuartic D π * heckeCharQuartic D (star π), ?_,
        heckeSumQuartic_split hp hπ hπp hbad hpn⟩
      rw [ratLocalPolynomial, h2 π hπ hπp hbad]
      simp only [map_add, map_mul]
      ring
    · refine ⟨0, -heckeCharQuartic D (p : GaussianInt), ?_, ?_⟩
      · rw [ratLocalPolynomial, h3 h hbad]
        simp only [map_neg, _root_.map_zero, zero_mul, sub_zero]
        ring
      · rw [heckeSumQuartic_inert hp h hbad hpn]; split_ifs <;> simp

lemma prime_mod_three {p : ℕ} (hp : p.Prime) (h3 : p ≠ 3) : p % 3 = 1 ∨ p % 3 = 2 := by
  have : p % 3 ≠ 0 := by
    intro h
    have h3d : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
    exact h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h3d).symm
  omega

lemma three_dvd_six_mul (D : ℤ) : ((3 : ℕ) : ℤ) ∣ 6 * D := ⟨2 * D, by push_cast; ring⟩

lemma two_dvd_six_mul (D : ℤ) : ((2 : ℕ) : ℤ) ∣ 6 * D := ⟨3 * D, by push_cast; ring⟩

/-- Theorem 8 for the `n` with `D ≢ 16 (mod 64)` or `n` odd. -/
theorem theorem8_LFunction_aux {c D : ℤ} (hc : c ≠ 0) (hD : D ≠ 0)
    (hfree : ∀ p : ℕ, p.Prime → ¬ (p : ℤ) ^ 6 ∣ D) (n : ℕ) (hn : D % 64 ≠ 16 ∨ Odd n) :
    (6 : ℤ[ω]) * (((cubicCurve (c ^ 6 * D)).baseChange ℚ).LFunction n : ℤ[ω]) =
      heckeSumSextic D n := by
  refine eq_of_recursion _ 6 (heckeSumSextic D) (fun n => D % 64 ≠ 16 ∨ Odd n)
    (fun n p h hpn => h.imp id fun ho => odd_div_of_dvd ho hpn)
    (heckeSumSextic_zero D) (heckeSumSextic_one D) ?_ n hn
  intro n p hp hPn hpn
  have hv : placePrime (placeOf p hp) = p := placePrime_placeOf p hp
  obtain ⟨h1, -, h3, h4⟩ := theorem8_localPolynomial_everyPrime (placeOf p hp) hc hD hfree
  rw [hv] at h1 h3 h4
  by_cases hbad : (p : ℤ) ∣ 6 * D
  · have hex : ¬ (p = 2 ∧ D % 64 = 16) := by
      rintro ⟨rfl, h16⟩
      rcases hPn with h | h
      · exact h h16
      · exact (Nat.not_even_iff_odd.2 h) (even_iff_two_dvd.2 hpn)
    refine ⟨0, 0, ?_, ?_⟩
    · rw [ratLocalPolynomial, h1 hbad hex]; simp
    · rw [heckeSumSextic_of_dvd_six_mul hp hbad hpn]; simp
  · have hp3 : p ≠ 3 := by rintro rfl; exact hbad (three_dvd_six_mul D)
    rcases prime_mod_three hp hp3 with h | h
    · obtain ⟨π, hπ, hπp⟩ := NTKB.IrelandRosen.Eisenstein.exists_isPrimary_norm_eq hp h
      refine ⟨heckeCharSextic D π + heckeCharSextic D (star π),
        heckeCharSextic D π * heckeCharSextic D (star π), ?_,
        heckeSumSextic_split hp hπ hπp hbad hpn⟩
      rw [ratLocalPolynomial, h3 π hπ hπp hbad]
      simp only [map_add, map_mul]
      ring
    · refine ⟨0, -heckeCharSextic D (p : ℤ[ω]), ?_, ?_⟩
      · rw [ratLocalPolynomial, h4 h hbad]
        simp only [map_neg, _root_.map_zero, zero_mul, sub_zero]
        ring
      · rw [heckeSumSextic_inert hp h hbad hpn]; split_ifs <;> simp

/-- **Ireland–Rosen, Chapter 18, Theorem 8: `L(E, s) = L(s, χ)`.** Let `D` be sixth-power free,
`D ≢ 16 (mod 64)`, `c ≠ 0`, `E : y² = x³ + c⁶D` and `χ = heckeCharSextic D`. For every `n`, six
times the `n`-th coefficient of Mathlib's `L`-function of `E` is `∑_{α ∈ ℤ[ω], N(α) = n} χ(α)`,
i.e. six times the `n`-th coefficient of `L(s, χ) = ∑_A χ(A) N(A)^{-s}`. -/
@[kb "irelandrosen1990" "Ch. 18, §5, Theorem 8, p. 324"]
theorem theorem8_LFunction {c D : ℤ} (hc : c ≠ 0) (hD : D ≠ 0)
    (hfree : ∀ p : ℕ, p.Prime → ¬ (p : ℤ) ^ 6 ∣ D) (h16 : D % 64 ≠ 16) (n : ℕ) :
    (6 : ℤ[ω]) * (((cubicCurve (c ^ 6 * D)).baseChange ℚ).LFunction n : ℤ[ω]) =
      heckeSumSextic D n :=
  theorem8_LFunction_aux hc hD hfree n (Or.inl h16)

/-- **Theorem 8 at the odd `n`, for every sixth-power-free `D`.** -/
@[kb "irelandrosen1990" "Ch. 18, §5, Theorem 8, p. 324"]
theorem theorem8_LFunction_odd {c D : ℤ} (hc : c ≠ 0) (hD : D ≠ 0)
    (hfree : ∀ p : ℕ, p.Prime → ¬ (p : ℤ) ^ 6 ∣ D) {n : ℕ} (hn : Odd n) :
    (6 : ℤ[ω]) * (((cubicCurve (c ^ 6 * D)).baseChange ℚ).LFunction n : ℤ[ω]) =
      heckeSumSextic D n :=
  theorem8_LFunction_aux hc hD hfree n (Or.inr hn)

/-- **Theorem 8 for `D ≡ 16 (mod 64)`: the exact factor at `2`.** Here `E` has good reduction at
`2` with local polynomial `1 + 2X²` while the book's character vanishes at `2`; the identity holds
with the Euler factor `1 / (1 + 2·4^{-s})` at `2`, the factor of the inert prime `2` for a character
with `χ₀((2)) = -2`: for odd `m`, `6 a_E(4^j m) = (-2)^j ∑_{N(α) = m} χ(α)` and `a_E(2·4^j m) = 0`. -/
@[kb "irelandrosen1990" "Ch. 18, §5, Theorem 8, p. 324"]
theorem theorem8_LFunction_sixteen {c D : ℤ} (hc : c ≠ 0) (hD : D ≠ 0)
    (hfree : ∀ p : ℕ, p.Prime → ¬ (p : ℤ) ^ 6 ∣ D) (h16 : D % 64 = 16) (j : ℕ) {m : ℕ}
    (hm : Odd m) :
    (6 : ℤ[ω]) * (((cubicCurve (c ^ 6 * D)).baseChange ℚ).LFunction (4 ^ j * m) : ℤ[ω]) =
        (-2) ^ j * heckeSumSextic D m ∧
      ((cubicCurve (c ^ 6 * D)).baseChange ℚ).LFunction (2 * 4 ^ j * m) = 0 := by
  set W := (cubicCurve (c ^ 6 * D)).baseChange ℚ
  set v := placeOf 2 Nat.prime_two
  have hv : placePrime v = 2 := placePrime_placeOf 2 Nat.prime_two
  obtain ⟨-, h2, -, -⟩ := theorem8_localPolynomial_everyPrime v hc hD hfree
  have hpoly : (ratLocalPolynomial W v).map (Int.castRingHom ℤ) =
      1 - C (0 : ℤ) * X + C (2 : ℤ) * X ^ 2 := by
    rw [ratLocalPolynomial, h2 hv h16]; simp
  obtain ⟨e0, e1, erec⟩ := localPowerSeries_coeff_of_eq W v (0 : ℤ) 2 hpoly
  simp only [Int.cast_id] at e0 e1 erec
  have hcoeff : ∀ i : ℕ, PowerSeries.coeff (2 * i) (ratLocalPowerSeries W v) = (-2) ^ i ∧
      PowerSeries.coeff (2 * i + 1) (ratLocalPowerSeries W v) = 0 := by
    intro i
    induction i with
    | zero => exact ⟨by simpa using e0, by simpa using e1⟩
    | succ i ih =>
      refine ⟨?_, ?_⟩
      · rw [show 2 * (i + 1) = 2 * i + 2 by ring, erec, ih.1]; ring
      · rw [show 2 * (i + 1) + 1 = (2 * i + 1) + 2 by ring, erec, ih.2]; ring
  have hcop : ∀ e : ℕ, Nat.Coprime (2 ^ e) m := fun e =>
    Nat.Coprime.pow_left e ((Nat.coprime_two_left).2 hm)
  have hmul := LFunction_isMultiplicative W
  have hpow : ∀ e, W.LFunction (2 ^ e) = PowerSeries.coeff e (ratLocalPowerSeries W v) := by
    intro e; rw [← LFunction_apply_prime_pow W v e, hv]
  refine ⟨?_, ?_⟩
  · rw [show 4 ^ j = 2 ^ (2 * j) by rw [pow_mul]; norm_num, hmul.map_mul_of_coprime (hcop _),
      hpow, (hcoeff j).1, ← theorem8_LFunction_odd hc hD hfree hm]
    push_cast
    ring
  · rw [show 2 * 4 ^ j = 2 ^ (2 * j + 1) by rw [pow_succ, pow_mul]; norm_num; ring,
      hmul.map_mul_of_coprime (hcop _), hpow, (hcoeff j).2, zero_mul]

end NTKB.IrelandRosen.CM
