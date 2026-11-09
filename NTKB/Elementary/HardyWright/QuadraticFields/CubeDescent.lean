/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Attr
import Mathlib.NumberTheory.FLT.Three
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID

/-!
# The descent in `k(ρ)` for `ξ³ + η³ + ε λ^e γ³ = 0` (Hardy–Wright §§ 13.4–13.5)

Let `K` be a number field with `IsCyclotomicExtension {3} ℚ K` (the field `k(ρ)` of Hardy–Wright),
`ζ` a primitive cube root of unity, `η` the corresponding unit of `𝓞 K` and `λ = η - 1` (the prime
`1 - ρ` of the book, up to sign).

Hardy–Wright prove Theorem 227 (`ξ³ + η³ + ζ³ = 0` has no solution in non-zero integers of `k(ρ)`)
and Theorem 232 (`x³ + y³ = 3z³` has only the trivial solutions) by the same descent: there is no
solution of
`ξ³ + η³ + ε λ^e γ³ = 0`, `(ξ, η) = 1`, `λ ∤ ξ η γ`,
when `e = 3n` (§ 13.4) or `e = 3n + 2` (§ 13.5). We prove both at once (`Sol`, `not_sol`): the
base cases `e ≤ 3` are Theorem 230 and its § 13.5 analogue (`not_sol_of_le_three`) and the descent
step `e ↦ e - 3` for `e ≥ 5` is Theorem 231 (`sol_descent`). The case `e ≡ 1 (mod 3)` is excluded by
`1³ + 2³ + 9·(-1)³ = 0` (§ 13.5).

The descent step is adapted from Mathlib's `Mathlib/NumberTheory/FLT/Three.lean` (Riccardo Brasca,
Sanyam Gupta, Omar Haddad, David Lowry-Duda, Lorenzo Luccioli, Pietro Monticone, Alexis Saurin,
Florent Schaffhauser), where the exponent of `λ` is the multiplicity of `λ` in `c` with `e ≡ 0`; here
the exponent `e` is explicit, which covers the equation `x³ + y³ = 3z³` as well.
-/

namespace NTKB.HardyWright.CubeDescent

open NumberField IsCyclotomicExtension.Rat.Three

variable {K : Type*} [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3)

local notation3 "η" => (IsPrimitiveRoot.isUnit (hζ.toInteger_isPrimitiveRoot) (by decide)).unit
local notation3 "λ" => hζ.toInteger - 1

/-- A solution of `a³ + b³ = u λ^e w³` with `a, b` coprime and `λ ∤ a, b, w` (Hardy–Wright (13.4.4)
and (13.5.1), with `ε = -u`). -/
structure Sol (e : ℕ) where
  /-- first unknown -/
  a : 𝓞 K
  /-- second unknown -/
  b : 𝓞 K
  /-- third unknown -/
  w : 𝓞 K
  /-- the unit -/
  u : (𝓞 K)ˣ
  ha : ¬ λ ∣ a
  hb : ¬ λ ∣ b
  hw : ¬ λ ∣ w
  coprime : IsCoprime a b
  H : a ^ 3 + b ^ 3 = u * λ ^ e * w ^ 3

variable {hζ}

lemma eta_cube : (η : 𝓞 K) ^ 3 = 1 := by
  rw [coe_eta]; exact hζ.toInteger_cube_eq_one

lemma lambda_sq_eq : (λ) ^ 2 = -3 * (η : 𝓞 K) := by
  have h := eta_sq hζ
  rw [coe_eta] at h ⊢
  linear_combination h

/-- `3 = -η² λ²`: the rational prime `3` is an associate of `λ²`. -/
lemma three_eq : (3 : 𝓞 K) = -(η : 𝓞 K) ^ 2 * (λ) ^ 2 := by
  rw [lambda_sq_eq]
  have h := eta_cube (hζ := hζ)
  linear_combination (-3 : 𝓞 K) * h

/-- The factorisation `a³ + b³ = (a + b)(a + ηb)(a + η²b)`. -/
lemma cube_add_cube_eq_mul (a b : 𝓞 K) :
    a ^ 3 + b ^ 3 = (a + b) * (a + η * b) * (a + η ^ 2 * b) := by
  have h1 := eta_sq hζ
  have h2 := eta_cube (hζ := hζ)
  rw [coe_eta] at h1 h2 ⊢
  linear_combination (-(a ^ 2 * b) - a * b ^ 2) * h1 + (-(a * b ^ 2) - b ^ 3) * h2

lemma add_eta_mul (a b : 𝓞 K) : a + η * b = (a + b) + λ * b := by rw [coe_eta]; ring

lemma add_eta_sq_mul (a b : 𝓞 K) :
    a + η ^ 2 * b = (a + b) + λ * (-(η : 𝓞 K) ^ 2 * b) := by
  have h2 := eta_cube (hζ := hζ)
  rw [coe_eta] at h2 ⊢
  linear_combination b * h2

section cyc

variable [NumberField K] [IsCyclotomicExtension {3} ℚ K]

lemma lambda_prime : Prime (λ) := hζ.zeta_sub_one_prime'

lemma lambda_not_dvd_two : ¬ λ ∣ (2 : 𝓞 K) := by
  have hζ' : IsPrimitiveRoot ζ (3 ^ (0 + 1)) := by rwa [zero_add, pow_one]
  have : IsCyclotomicExtension {3 ^ (0 + 1)} ℚ K := by rwa [zero_add, pow_one]
  exact hζ'.toInteger_sub_one_not_dvd_two (by decide)

lemma lambda_not_dvd_one : ¬ λ ∣ (1 : 𝓞 K) := fun h ↦ (lambda_prime (hζ := hζ)).not_isUnit
  (isUnit_of_dvd_one h)

/-- `λ` divides a rational integer `n` if and only if `3 ∣ n`. -/
lemma lambda_dvd_intCast_iff (n : ℤ) : λ ∣ (n : 𝓞 K) ↔ (3 : ℤ) ∣ n := by
  rw [← Ideal.norm_dvd_iff (hζ.prime_norm_toInteger_sub_one_of_prime_ne_two' (by decide)),
    hζ.norm_toInteger_sub_one_of_prime_ne_two' (by decide)]
  simp

/-- If `λ ∤ x`, then `x³ ≡ ±1 (mod λ⁴)` (Hardy–Wright, Theorem 228, Mathlib's form). -/
lemma cube_congr {x : 𝓞 K} (h : ¬ λ ∣ x) : λ ^ 4 ∣ x ^ 3 - 1 ∨ λ ^ 4 ∣ x ^ 3 + 1 :=
  lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd hζ h

/-- If `λ ∤ a, b`, then either `λ ∤ a³ + b³` or `λ⁴ ∣ a³ + b³`. -/
lemma not_dvd_or_pow_four_dvd {a b : 𝓞 K} (ha : ¬ λ ∣ a) (hb : ¬ λ ∣ b) :
    ¬ λ ∣ a ^ 3 + b ^ 3 ∨ λ ^ 4 ∣ a ^ 3 + b ^ 3 := by
  rcases cube_congr ha with ⟨x, hx⟩ | ⟨x, hx⟩ <;> rcases cube_congr hb with ⟨y, hy⟩ | ⟨y, hy⟩
  · left
    rintro ⟨z, hz⟩
    exact lambda_not_dvd_two ⟨z - λ ^ 3 * (x + y), by linear_combination hz - hx - hy⟩
  · right; exact ⟨x + y, by linear_combination hx + hy⟩
  · right; exact ⟨x + y, by linear_combination hx + hy⟩
  · left
    rintro ⟨z, hz⟩
    exact lambda_not_dvd_two ⟨λ ^ 3 * (x + y) - z, by linear_combination -hz + hx + hy⟩

/-- Theorem 230 and the step "(a)" of § 13.5: there is no solution with `1 ≤ e ≤ 3`. -/
theorem not_sol_of_le_three {e : ℕ} (he : 1 ≤ e) (he' : e ≤ 3) (S : Sol hζ e) : False := by
  have hp := lambda_prime (hζ := hζ)
  rcases not_dvd_or_pow_four_dvd S.ha S.hb with h | h
  · apply h
    rw [S.H]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) _) _
  · rw [S.H, show 4 = e + (4 - e) by omega, pow_add, mul_assoc, mul_left_comm,
      mul_dvd_mul_iff_left (pow_ne_zero _ hp.ne_zero), Units.dvd_mul_left] at h
    exact S.hw (hp.dvd_of_dvd_pow (dvd_trans (dvd_pow_self _ (by omega)) h))

/-- In a solution with `e ≥ 4`, after multiplying `b` by a power of `η` we may suppose
`λ² ∣ a + b` (the factor divisible by `λ²` in § 13.4). -/
lemma exists_sq_dvd {e : ℕ} (he : 4 ≤ e) (S : Sol hζ e) :
    ∃ b' : 𝓞 K, S.a ^ 3 + b' ^ 3 = S.u * λ ^ e * S.w ^ 3 ∧ IsCoprime S.a b' ∧ ¬ λ ∣ b' ∧
      λ ^ 2 ∣ S.a + b' := by
  have hp := lambda_prime (hζ := hζ)
  have hc := eta_cube (hζ := hζ)
  -- `λ ∣ a + b`
  have h1 : λ ∣ S.a + S.b := by
    have : λ ∣ S.a ^ 3 + S.b ^ 3 := by
      rw [S.H]; exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) _) _
    rw [cube_add_cube_eq_mul (hζ := hζ)] at this
    rcases hp.dvd_or_dvd this with h | h
    · rcases hp.dvd_or_dvd h with h | h
      · exact h
      · rw [add_eta_mul (hζ := hζ)] at h; exact (dvd_add_left (dvd_mul_right _ _)).1 h
    · rw [add_eta_sq_mul (hζ := hζ)] at h; exact (dvd_add_left (dvd_mul_right _ _)).1 h
  by_cases h0 : λ ^ 2 ∣ S.a + S.b
  · exact ⟨S.b, S.H, S.coprime, S.hb, h0⟩
  by_cases h2 : λ ^ 2 ∣ S.a + η * S.b
  · refine ⟨η * S.b, ?_, ?_, ?_, h2⟩
    · rw [mul_pow, hc, one_mul, S.H]
    · exact (isCoprime_mul_unit_left_right (Units.isUnit η) _ _).2 S.coprime
    · intro h; exact S.hb (Units.dvd_mul_left.1 h)
  by_cases h3 : λ ^ 2 ∣ S.a + η ^ 2 * S.b
  · refine ⟨η ^ 2 * S.b, ?_, ?_, ?_, h3⟩
    · rw [mul_pow, ← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, hc, one_pow, one_mul, S.H]
    · exact (isCoprime_mul_unit_left_right ((Units.isUnit η).pow 2) _ _).2 S.coprime
    · intro h
      exact S.hb ((IsUnit.dvd_mul_left ((Units.isUnit η).pow 2)).1 h)
  exfalso
  obtain ⟨x, hx⟩ := h1
  have hx' : ¬ λ ∣ x := fun ⟨k, hk⟩ ↦ h0 ⟨k, by rw [hx, hk]; ring⟩
  have hy : λ ∣ S.a + η * S.b := by rw [add_eta_mul (hζ := hζ), hx]; exact dvd_add (dvd_mul_right _ _) (dvd_mul_right _ _)
  have hz : λ ∣ S.a + η ^ 2 * S.b := by
    rw [add_eta_sq_mul (hζ := hζ), hx]; exact dvd_add (dvd_mul_right _ _) (dvd_mul_right _ _)
  obtain ⟨y, hy⟩ := hy
  obtain ⟨z, hz⟩ := hz
  have hy' : ¬ λ ∣ y := fun ⟨k, hk⟩ ↦ h2 ⟨k, by rw [hy, hk]; ring⟩
  have hz' : ¬ λ ∣ z := fun ⟨k, hk⟩ ↦ h3 ⟨k, by rw [hz, hk]; ring⟩
  have H := S.H
  have hpow : λ ^ e = λ ^ 3 * λ ^ (e - 3) := by rw [← pow_add]; congr 1; omega
  rw [cube_add_cube_eq_mul (hζ := hζ), hx, hy, hz, hpow] at H
  have H' : x * y * z = S.u * λ ^ (e - 3) * S.w ^ 3 := by
    apply mul_left_cancel₀ (pow_ne_zero 3 hp.ne_zero)
    linear_combination H
  have : λ ∣ x * y * z := by
    rw [H']; exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) _) _
  rcases hp.dvd_or_dvd this with h | h
  · rcases hp.dvd_or_dvd h with h | h
    · exact hx' h
    · exact hy' h
  · exact hz' h

attribute [local instance] IsCyclotomicExtension.Rat.three_pid

omit [NumberField K] [IsCyclotomicExtension {3} ℚ K] in
/-- A prime dividing `λ c a` and `λ c' b` (`c, c'` units, `a, b` coprime) divides `λ`. -/
lemma prime_dvd_lambda {p a b c c' : 𝓞 K} (hp : Prime p) (hc : IsUnit c) (hc' : IsUnit c')
    (hab : IsCoprime a b) (h1 : p ∣ λ * c * a) (h2 : p ∣ λ * c' * b) : p ∣ λ := by
  by_contra hl
  have h1' : p ∣ a := by
    rcases hp.dvd_or_dvd h1 with h | h
    · rcases hp.dvd_or_dvd h with h | h
      · exact absurd h hl
      · exact absurd (isUnit_of_dvd_unit h hc) hp.not_isUnit
    · exact h
  have h2' : p ∣ b := by
    rcases hp.dvd_or_dvd h2 with h | h
    · rcases hp.dvd_or_dvd h with h | h
      · exact absurd h hl
      · exact absurd (isUnit_of_dvd_unit h hc') hp.not_isUnit
    · exact h
  exact hp.not_isUnit (hab.isUnit_of_dvd' h1' h2')

/-- If `λ ∤ r` and every prime dividing both `r` and `s` divides `λ`, then `r, s` are coprime. -/
lemma isCoprime_of_lambda {r s : 𝓞 K} (hr : ¬ λ ∣ r)
    (H : ∀ p : 𝓞 K, Prime p → p ∣ r → p ∣ s → p ∣ λ) : IsCoprime r s := by
  refine isCoprime_of_prime_dvd (fun h ↦ hr (h.1 ▸ dvd_zero _)) (fun p hp hpr hps ↦ hr ?_)
  exact ((hp.associated_of_dvd (lambda_prime (hζ := hζ)) (H p hp hpr hps)).dvd_iff_dvd_left).1 hpr

/-- Theorem 231 and the step "(b)" of § 13.5: a solution with `e ≥ 5` gives a solution with
`e - 3`. -/
theorem sol_descent {e : ℕ} (he : 5 ≤ e) (S : Sol hζ e) : Nonempty (Sol hζ (e - 3)) := by
  have hp := lambda_prime (hζ := hζ)
  have hl0 := hp.ne_zero
  have hc := eta_cube (hζ := hζ)
  have hsq := eta_sq hζ
  have hηu : IsUnit (η : 𝓞 K) := Units.isUnit η
  obtain ⟨b, H, hcop, hb, hab⟩ := exists_sq_dvd (by omega) S
  set a := S.a with ha_def
  have ha := S.ha
  obtain ⟨m, hm⟩ := hab
  -- `a + ηb = λ y`, `a + η²b = λ z`, with `λ ∤ y z`
  obtain ⟨y, hy⟩ : λ ∣ a + η * b := by
    rw [add_eta_mul (hζ := hζ), hm]; exact ⟨λ * m + b, by ring⟩
  obtain ⟨z, hz⟩ : λ ∣ a + η ^ 2 * b := by
    rw [add_eta_sq_mul (hζ := hζ), hm]; exact ⟨λ * m + -(η : 𝓞 K) ^ 2 * b, by ring⟩
  have hy' : ¬ λ ∣ y := by
    rintro ⟨k, hk⟩
    have e1 := add_eta_mul (hζ := hζ) a b
    have : λ * b = λ * (λ * (k - m)) := by linear_combination -e1 + hy + λ * hk - hm
    exact hb ⟨_, mul_left_cancel₀ hl0 this⟩
  have hz' : ¬ λ ∣ z := by
    rintro ⟨k, hk⟩
    have e1 := add_eta_sq_mul (hζ := hζ) a b
    have : λ * (-(η : 𝓞 K) ^ 2 * b) = λ * (λ * (k - m)) := by
      linear_combination -e1 + hz + λ * hk - hm
    have h' : λ ∣ -(η : 𝓞 K) ^ 2 * b := ⟨_, mul_left_cancel₀ hl0 this⟩
    rw [neg_mul, dvd_neg] at h'
    exact hb ((IsUnit.dvd_mul_left (hηu.pow 2)).1 h')
  -- `(a + b) y z = u λ^(e-2) w³`
  have hpow : λ ^ e = λ ^ 2 * λ ^ (e - 2) := by rw [← pow_add]; congr 1; omega
  have H2 : (a + b) * (y * z) = S.u * λ ^ (e - 2) * S.w ^ 3 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hl0)
    have := cube_add_cube_eq_mul (hζ := hζ) a b
    rw [hy, hz, H, hpow] at this
    linear_combination -this
  have hyz : ¬ λ ∣ y * z := fun h ↦ (hp.dvd_or_dvd h).elim hy' hz'
  obtain ⟨x, hx⟩ : λ ^ (e - 2) ∣ a + b := by
    refine hp.pow_dvd_of_dvd_mul_right _ hyz ?_
    rw [H2]; exact Dvd.dvd.mul_right (Dvd.dvd.mul_left dvd_rfl _) _
  have hxyz : x * y * z = S.u * S.w ^ 3 := by
    apply mul_left_cancel₀ (pow_ne_zero (e - 2) hl0)
    rw [hx] at H2
    linear_combination H2
  have hx' : ¬ λ ∣ x := by
    intro h
    apply S.hw
    apply hp.dvd_of_dvd_pow (n := 3)
    have : λ ∣ x * y * z := Dvd.dvd.mul_right (Dvd.dvd.mul_right h _) _
    rwa [hxyz, Units.dvd_mul_left] at this
  -- pairwise coprimality
  have hxy : IsCoprime x y := isCoprime_of_lambda hx' fun p hpp hpx hpy ↦ by
    have h1 : p ∣ a + b := hx ▸ Dvd.dvd.mul_left hpx _
    have h2 : p ∣ a + η * b := hy ▸ Dvd.dvd.mul_left hpy _
    refine prime_dvd_lambda hpp (isUnit_one.neg) isUnit_one hcop ?_ ?_
    · have e2 : λ * -1 * a = (a + η * b) - η * (a + b) := by rw [coe_eta]; ring
      rw [e2]; exact dvd_sub h2 (Dvd.dvd.mul_left h1 _)
    · have e2 : λ * 1 * b = (a + η * b) - (a + b) := by rw [coe_eta]; ring
      rw [e2]; exact dvd_sub h2 h1
  have hxz : IsCoprime x z := isCoprime_of_lambda hx' fun p hpp hpx hpz ↦ by
    have h1 : p ∣ a + b := hx ▸ Dvd.dvd.mul_left hpx _
    have h2 : p ∣ a + η ^ 2 * b := hz ▸ Dvd.dvd.mul_left hpz _
    refine prime_dvd_lambda hpp (hηu.pow 2) (hηu.pow 2).neg hcop ?_ ?_
    · have e2 : λ * η ^ 2 * a = (a + η ^ 2 * b) - η ^ 2 * (a + b) := by
        rw [coe_eta] at hc ⊢; linear_combination a * hc
      rw [e2]; exact dvd_sub h2 (Dvd.dvd.mul_left h1 _)
    · have e2 : λ * -(η ^ 2 : 𝓞 K) * b = (a + η ^ 2 * b) - (a + b) := by
        rw [coe_eta] at hc ⊢; linear_combination -b * hc
      rw [e2]; exact dvd_sub h2 h1
  have hyz' : IsCoprime y z := isCoprime_of_lambda hy' fun p hpp hpy hpz ↦ by
    have h1 : p ∣ a + η * b := hy ▸ Dvd.dvd.mul_left hpy _
    have h2 : p ∣ a + η ^ 2 * b := hz ▸ Dvd.dvd.mul_left hpz _
    refine prime_dvd_lambda hpp isUnit_one.neg hηu hcop ?_ ?_
    · have e2 : λ * -1 * a = (a + η ^ 2 * b) - η * (a + η * b) := by rw [coe_eta]; ring
      rw [e2]; exact dvd_sub h2 (Dvd.dvd.mul_left h1 _)
    · have e2 : λ * η * b = (a + η ^ 2 * b) - (a + η * b) := by rw [coe_eta]; ring
      rw [e2]; exact dvd_sub h2 h1
  -- each of `x, y, z` is an associate of a cube
  have hw3 : Associated (S.w ^ 3) (x * y * z) := ⟨S.u, by rw [hxyz, mul_comm]⟩
  obtain ⟨T, hT⟩ := exists_associated_pow_of_associated_pow_mul (hxz.mul_left hyz') hw3
  obtain ⟨X, u₁, hX⟩ := exists_associated_pow_of_associated_pow_mul hxy hT
  obtain ⟨Y, u₂, hY⟩ := exists_associated_pow_of_associated_pow_mul hxy.symm (mul_comm x y ▸ hT)
  obtain ⟨Z, u₃, hZ⟩ := exists_associated_pow_of_associated_pow_mul (hxz.mul_left hyz').symm
    (mul_comm (x * y) z ▸ hw3)
  have hX' : ¬ λ ∣ X := fun h ↦ hx' (hX ▸ Dvd.dvd.mul_right (dvd_pow h (by decide)) _)
  have hY' : ¬ λ ∣ Y := fun h ↦ hy' (hY ▸ Dvd.dvd.mul_right (dvd_pow h (by decide)) _)
  have hZ' : ¬ λ ∣ Z := fun h ↦ hz' (hZ ▸ Dvd.dvd.mul_right (dvd_pow h (by decide)) _)
  have hYZ : IsCoprime Y Z := by
    rw [← hY, ← hZ] at hyz'
    have h1 := (hyz'.of_mul_left_left).of_mul_right_left
    exact (IsCoprime.pow_iff (by decide) (by decide)).1 h1
  -- the key relation `λ^(e-3) X³ u₁ + η Y³ u₂ + η² Z³ u₃ = 0`
  have hpow3 : λ ^ (e - 2) = λ * λ ^ (e - 3) := by rw [← pow_succ']; congr 1; omega
  have key : λ ^ (e - 3) * (X ^ 3 * u₁) + η * (Y ^ 3 * u₂) + η ^ 2 * (Z ^ 3 * u₃) = 0 := by
    apply mul_left_cancel₀ hl0
    rw [hX, hY, hZ]
    have e0 : (a + b) + η * (a + η * b) + η ^ 2 * (a + η ^ 2 * b) = 0 := by
      rw [coe_eta] at hsq hc ⊢
      linear_combination (a + b) * hsq + (b * hζ.toInteger) * hc
    rw [hx, hy, hz, hpow3] at e0
    linear_combination e0
  -- units `u₄ = η u₃ / u₂` and `u₅ = -u₁ / (η u₂)`
  set u₄ : (𝓞 K)ˣ := η * u₃ * u₂⁻¹ with hu₄
  set u₅ : (𝓞 K)ˣ := -(u₁ * u₂⁻¹ * η⁻¹) with hu₅
  have key2 : Y ^ 3 + u₄ * Z ^ 3 = u₅ * λ ^ (e - 3) * X ^ 3 := by
    have h2 : (u₂ : 𝓞 K) * (u₂⁻¹ : (𝓞 K)ˣ) = 1 := by simp
    have h3 : (η : 𝓞 K) * (η⁻¹ : (𝓞 K)ˣ) = 1 := by simp
    simp only [hu₄, hu₅, Units.val_mul, Units.val_neg]
    linear_combination (u₂⁻¹ : (𝓞 K)ˣ) * (η⁻¹ : (𝓞 K)ˣ) * key
      - Y ^ 3 * h2 - (u₂⁻¹ : (𝓞 K)ˣ) * Y ^ 3 * u₂ * h3
      - (u₂⁻¹ : (𝓞 K)ˣ) * Z ^ 3 * u₃ * (η : 𝓞 K) * h3
  -- `u₄ = ±1`
  have hu₄' : u₄ = 1 ∨ u₄ = -1 := by
    apply eq_one_or_neg_one_of_unit_of_congruent hζ
    have h4 : λ ^ 2 ∣ λ ^ 4 := pow_dvd_pow _ (by decide)
    have h5 : λ ^ 2 ∣ λ ^ (e - 3) := pow_dvd_pow _ (by omega)
    obtain ⟨t, ht⟩ : λ ^ 2 ∣ Y ^ 3 + u₄ * Z ^ 3 := by
      rw [key2]; exact Dvd.dvd.mul_right (Dvd.dvd.mul_left h5 _) _
    rcases cube_congr hY' with HY | HY <;> rcases cube_congr hZ' with HZ | HZ <;>
      obtain ⟨r, hr⟩ := h4.trans HY <;> obtain ⟨s, hs⟩ := h4.trans HZ
    · exact ⟨-1, t - r - u₄ * s, by push_cast; linear_combination ht - hr - (u₄ : 𝓞 K) * hs⟩
    · exact ⟨1, -t + r + u₄ * s, by push_cast; linear_combination -ht + hr + (u₄ : 𝓞 K) * hs⟩
    · exact ⟨1, t - r - u₄ * s, by push_cast; linear_combination ht - hr - (u₄ : 𝓞 K) * hs⟩
    · exact ⟨-1, -t + r + u₄ * s, by push_cast; linear_combination -ht + hr + (u₄ : 𝓞 K) * hs⟩
  have hu₄3 : (u₄ : 𝓞 K) ^ 3 = u₄ := by
    rcases hu₄' with h | h
    · simp [h]
    · simp [h]; norm_num
  exact ⟨{
    a := Y
    b := u₄ * Z
    w := X
    u := u₅
    ha := hY'
    hb := fun h ↦ hZ' (Units.dvd_mul_left.1 h)
    hw := hX'
    coprime := (isCoprime_mul_unit_left_right u₄.isUnit _ _).2 hYZ
    H := by rw [mul_pow, hu₄3, key2] }⟩

/-- **The descent of §§ 13.4–13.5.** There is no solution of `a³ + b³ = u λ^e w³` with `a, b`
coprime and `λ ∤ a b w` when `e ≥ 1` and `e ≢ 1 (mod 3)`. -/
theorem not_sol : ∀ e : ℕ, 1 ≤ e → e % 3 ≠ 1 → Sol hζ e → False := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro he1 he3 S
    by_cases he : e ≤ 3
    · exact not_sol_of_le_three he1 he S
    · have he5 : 5 ≤ e := by omega
      obtain ⟨S'⟩ := sol_descent he5 S
      exact ih (e - 3) (by omega) (by omega) (by omega) S'

end cyc

end NTKB.HardyWright.CubeDescent
