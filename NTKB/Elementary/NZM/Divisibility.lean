/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Attr
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Div
import Mathlib.FieldTheory.Finite.Basic

/-!
# Greatest common divisors; products of consecutive integers (Niven–Zuckerman–Montgomery, §§ 1.2, 1.4)

* Theorem 1.4: `g = (b, c)` is the least positive value of `bx + cy`, and the positive common divisor
  of `b` and `c` that is divisible by every common divisor.
* Theorem 1.7: if `d > 0` divides `a` and `b` then `(a/d, b/d) = (a, b)/d`; `(a/g, b/g) = 1`.
* Theorem 1.9: `(a, b) = (b, a) = (a, -b) = (a, b + ax)`.
* Theorem 2.50: `ℤ/m` is a field if and only if `m` is prime.
* Theorem 1.21: the product of any `k` consecutive integers is divisible by `k!` (any integer start;
  for a positive start this is `Nat.factorial_dvd_ascFactorial`, and the general case follows because
  `∏ (x + i)` is a polynomial with integer coefficients, so its values at `n` and `n + k! t` agree modulo
  `k!`).
-/

namespace NTKB.NZM

open Finset

/-- **Theorem 1.4.** If `b, c` are not both `0`, then `g = (b, c)` is (A) the least positive value of
`bx + cy` (`x, y` integers), and (B) a positive common divisor of `b` and `c` divisible by every common
divisor. -/
@[kb "nivenzuckermanmontgomery" "Thm 1.4, p. 8"]
theorem gcd_least_pos_comb {b c : ℤ} (h : b ≠ 0 ∨ c ≠ 0) :
    ((∃ x y : ℤ, b * x + c * y = Int.gcd b c) ∧
      ∀ x y : ℤ, 0 < b * x + c * y → (Int.gcd b c : ℤ) ≤ b * x + c * y) ∧
    (0 < Int.gcd b c ∧ (Int.gcd b c : ℤ) ∣ b ∧ (Int.gcd b c : ℤ) ∣ c ∧
      ∀ d : ℤ, d ∣ b → d ∣ c → d ∣ (Int.gcd b c : ℤ)) := by
  refine ⟨⟨⟨_, _, (Int.gcd_eq_gcd_ab b c).symm⟩, fun x y hpos ↦ ?_⟩,
    Int.gcd_pos_iff.mpr h, Int.gcd_dvd_left b c, Int.gcd_dvd_right b c, fun d hb hc ↦ ?_⟩
  · exact Int.le_of_dvd hpos (dvd_add (dvd_mul_of_dvd_left (Int.gcd_dvd_left b c) x)
      (dvd_mul_of_dvd_left (Int.gcd_dvd_right b c) y))
  · have h1 : d.natAbs ∣ Int.gcd b c :=
      Int.dvd_gcd (Int.natAbs_dvd.mpr hb) (Int.natAbs_dvd.mpr hc)
    rw [← Int.natAbs_dvd_natAbs]
    simpa using h1

/-- **Theorem 1.7.** If `d > 0` divides `a` and `b`, then `(a/d, b/d) = (a, b)/d`; in particular
`(a/g, b/g) = 1` for `g = (a, b) > 0`. -/
@[kb "nivenzuckermanmontgomery" "Thm 1.7, p. 9"]
theorem gcd_div_of_dvd {a b : ℤ} {d : ℕ} (ha : (d : ℤ) ∣ a) (hb : (d : ℤ) ∣ b) :
    Int.gcd (a / d) (b / d) = Int.gcd a b / d ∧
      (0 < Int.gcd a b → Int.gcd (a / Int.gcd a b) (b / Int.gcd a b) = 1) := by
  refine ⟨?_, Int.gcd_div_gcd_div_gcd⟩
  rw [Int.gcd_div ha hb, Int.natAbs_natCast]

/-- **Theorem 1.9.** `(a, b) = (b, a) = (a, -b) = (a, b + ax)` for every integer `x`. -/
@[kb "nivenzuckermanmontgomery" "Thm 1.9, p. 10"]
theorem gcd_symm_neg_add_mul (a b x : ℤ) :
    Int.gcd a b = Int.gcd b a ∧ Int.gcd a b = Int.gcd a (-b) ∧ Int.gcd a b = Int.gcd a (b + a * x) :=
  ⟨Int.gcd_comm a b, Int.gcd_neg.symm, (Int.gcd_add_mul_left_right a b x).symm⟩

/-- **Theorem 1.21.** The product of any `k` consecutive integers `n, n + 1, …, n + k - 1` is divisible
by `k!`. -/
@[kb "nivenzuckermanmontgomery" "Thm 1.21, p. 37"]
theorem factorial_dvd_prod_consecutive (n : ℤ) (k : ℕ) :
    (k.factorial : ℤ) ∣ ∏ i ∈ range k, (n + i) := by
  open Polynomial in
  set Q : ℤ[X] := ∏ i ∈ range k, (X + C (i : ℤ)) with hQ
  have hev : ∀ x : ℤ, Q.eval x = ∏ i ∈ range k, (x + i) := by
    intro x; simp [hQ, eval_prod]
  -- a positive start `m = n + k! (|n| + 1) ≥ 1`
  set m : ℤ := n + k.factorial * (|n| + 1) with hm
  have hf : (1 : ℤ) ≤ k.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hm1 : 1 ≤ m := by
    have := neg_abs_le n
    nlinarith [abs_nonneg n]
  have hpos : k.factorial ∣ (m.toNat).ascFactorial k := Nat.factorial_dvd_ascFactorial _ _
  have hmval : (k.factorial : ℤ) ∣ Q.eval m := by
    rw [hev]
    have e : ((m.toNat).ascFactorial k : ℤ) = ∏ i ∈ range k, (m + i) := by
      rw [Nat.ascFactorial_eq_prod_range]; push_cast
      rw [Int.toNat_of_nonneg (by linarith)]
    rw [← e]; exact_mod_cast hpos
  have hdiff : (k.factorial : ℤ) ∣ Q.eval m - Q.eval n := by
    refine dvd_trans ?_ (Polynomial.sub_dvd_eval_sub m n Q)
    exact ⟨|n| + 1, by rw [hm]; ring⟩
  rw [← hev]
  have := dvd_sub hmval hdiff
  simpa using this

/-- **Theorem 2.50.** `ℤ/m` is a commutative ring (Mathlib's instance `ZMod.commRing`), and it is a field
if and only if `m` is a prime. -/
@[kb "nivenzuckermanmontgomery" "Thm 2.50, p. 125"]
theorem zmod_isField_iff_prime (m : ℕ) : IsField (ZMod m) ↔ m.Prime := by
  constructor
  · intro h
    have hdom := h.isDomain
    have hm1 : m ≠ 1 := by
      intro h1; subst h1
      exact absurd h.exists_pair_ne (by simp)
    have hm0 : m ≠ 0 := by
      intro h0; subst h0
      exact Int.not_isField h
    by_contra hp
    obtain ⟨d, hd, hd2, hdm⟩ := Nat.exists_dvd_of_not_prime2 (by omega) hp
    obtain ⟨e, he⟩ := hd
    have he1 : e < m := by
      rcases Nat.lt_or_ge e m with h' | h'
      · exact h'
      · nlinarith
    have he0 : 0 < e := by
      rcases Nat.eq_zero_or_pos e with h' | h'
      · subst h'; simp at he; omega
      · exact h'
    have hprod : (d : ZMod m) * (e : ZMod m) = 0 := by
      rw [← Nat.cast_mul, ← he, ZMod.natCast_self]
    rcases mul_eq_zero.mp hprod with h' | h'
    · rw [ZMod.natCast_eq_zero_iff] at h'
      exact absurd (Nat.le_of_dvd (by omega) h') (by omega)
    · rw [ZMod.natCast_eq_zero_iff] at h'
      exact absurd (Nat.le_of_dvd he0 h') (by omega)
  · intro h
    have : Fact m.Prime := ⟨h⟩
    exact Field.toIsField _

end NTKB.NZM
