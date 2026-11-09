/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.QuadraticFields.Lucas

/-!
# Theorem 180 from the arithmetic of `k(√5)` (Hardy–Wright § 15.4)

`u_n = (ω^n - ω̄^n)/(ω - ω̄)`, `ω - ω̄ = √5`. If `p = 5n ± 1` then `ω^(p-1) ≡ ω̄^(p-1) ≡ 1 (mod p)`
(15.4.7), so `u_{p-1} ≡ 0 (mod p)`; if `q = 5n ± 2` then `ω^(q+1) ≡ Nω`, `ω̄^(q+1) ≡ Nω̄ (mod q)`
(15.4.6), so `u_{q+1} ≡ 0 (mod q)`. This is the book's second proof of Theorem 180 (the statement is
`prime_dvd_fib`).
-/

namespace NTKB.HardyWright

open QuadraticAlgebra

/-- Binet's formula in `ℤ[ω]`: `√5 u_n = ω^n - ω̄^n`. -/
lemma sqrtFive_mul_fib (n : ℕ) :
    sqrtFive * (Nat.fib n : ZGold) = omG ^ n - (star omG) ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simp
    · ext <;> simp [sqrtFive, omG]
    · have h1 := ih n (by omega)
      have h2 := ih (n + 1) (by omega)
      have hω : omG ^ 2 = omG + 1 := by ext <;> simp [omG, sq]
      have hω' : (star omG) ^ 2 = star omG + 1 := by ext <;> simp [omG, sq]
      rw [Nat.fib_add_two, Nat.cast_add, mul_add, h1, h2]
      linear_combination (-(omG ^ n)) * hω + (star omG) ^ n * hω'

lemma isUnit_star_omG : IsUnit (star omG) := by
  rw [qa_isUnit_iff, QuadraticAlgebra.norm_star, norm_omG]; rfl

lemma norm_star_omG : norm (star omG) = -1 := by rw [QuadraticAlgebra.norm_star, norm_omG]

/-- From `p ∣ √5 u` in `ℤ[ω]` (with `p ≠ 5` prime) deduce `p ∣ u`. -/
lemma dvd_of_dvd_sqrtFive_mul {p : ℕ} (hp : p.Prime) (hp5 : p ≠ 5) {u : ℕ}
    (h : (p : ZGold) ∣ sqrtFive * (u : ZGold)) : p ∣ u := by
  have h5 : (p : ZGold) ∣ ((5 * u : ℤ) : ZGold) := by
    have := dvd_mul_of_dvd_right h sqrtFive
    rw [← mul_assoc, sqrtFive_sq] at this
    push_cast; exact this
  have h5' : (p : ℤ) ∣ 5 * u := gold_int_dvd_of_dvd h5
  have : p ∣ 5 * u := by exact_mod_cast h5'
  exact (Nat.Coprime.dvd_of_dvd_mul_left
    ((Nat.coprime_primes hp Nat.prime_five).2 hp5) this)

/-- **§ 15.4** (Theorem 180 again): `u_{p-1} ≡ 0 (mod p)` for primes `p = 5n ± 1`, and
`u_{q+1} ≡ 0 (mod q)` for primes `q = 5n ± 2`, proved in `k(√5)`. -/
@[kb "hardywright2008" "§ 15.4, p. 309"]
theorem prime_dvd_fib_of_gold {p : ℕ} (hp : p.Prime) :
    ((p % 5 = 1 ∨ p % 5 = 4) → p ∣ Nat.fib (p - 1)) ∧
      ((p % 5 = 2 ∨ p % 5 = 3) → p ∣ Nat.fib (p + 1)) := by
  have hp5 : ∀ h : p % 5 ≠ 0, p ≠ 5 := fun h h5 ↦ h (by rw [h5])
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := Fact.mk hp
    have hp2 : p ≠ 2 := by rintro rfl; omega
    have cancel : ∀ x : ZGold, IsUnit x → (p : ZGold) ∣ x ^ (p - 1) - 1 := fun x hx ↦ by
      have h1 := (gold_dvd_pow_sub hp2 x).1 h
      have e : x ^ p - x = x * (x ^ (p - 1) - 1) := by
        conv_lhs => rw [show p = p - 1 + 1 by have := hp.two_le; omega, pow_succ]
        ring
      rw [e] at h1
      exact (IsUnit.dvd_mul_left hx).1 h1
    have := dvd_sub (cancel omG isUnit_omG) (cancel (star omG) isUnit_star_omG)
    rw [sub_sub_sub_cancel_right, ← sqrtFive_mul_fib] at this
    exact dvd_of_dvd_sqrtFive_mul hp (hp5 (by omega)) this
  · have h1 := gold_fermat_q hp h omG
    have h2 := gold_fermat_q hp h (star omG)
    rw [norm_omG] at h1
    rw [norm_star_omG] at h2
    have := dvd_sub h1 h2
    rw [sub_sub_sub_cancel_right, ← sqrtFive_mul_fib] at this
    exact dvd_of_dvd_sqrtFive_mul hp (hp5 (by omega)) this

end NTKB.HardyWright
