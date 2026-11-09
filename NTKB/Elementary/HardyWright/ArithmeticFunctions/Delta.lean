/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Aesop.BuiltinRules
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import NTKB.Attr

/-!
# Hardy–Wright, § 16.9: the function `δ(n) = ∑_{d ∣ n} χ(d)`

`χ(n)` is `0` for even `n` and `(-1)^{(n-1)/2}` for odd `n`: Mathlib's `ZMod.χ₄`, read on natural
numbers. Hardy and Wright write

* (16.9.1)–(16.9.2): `δ(n) = ∑_{d ∣ n} χ(d) = d₁(n) - d₃(n)`, `d₁`, `d₃` the numbers of divisors
  `≡ 1` and `≡ 3 (mod 4)`;
* (16.9.5): for `n = 2^a ∏ p^r ∏ q^s` (`p ≡ 1`, `q ≡ 3 (mod 4)`),
  `δ(n) = ∏ (r + 1) ∏ (1 + (-1)^s)/2`: `δ(n) = 0` unless every `s` is even, and then
  `δ(n) = d(∏ p^r)`.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta

namespace NTKB.HardyWright

/-- `χ(n)`, the non-principal character modulo `4` on natural numbers. -/
abbrev chi4 (n : ℕ) : ℤ := ZMod.χ₄ (n : ZMod 4)

/-- `δ(n) = ∑_{d ∣ n} χ(d)` (Hardy–Wright (16.9.1)). -/
def chi4DivisorSum (n : ℕ) : ℤ := ∑ d ∈ n.divisors, chi4 d

lemma chi4_eq (n : ℕ) : chi4 n = if n % 2 = 0 then 0 else if n % 4 = 1 then 1 else -1 :=
  ZMod.χ₄_nat_eq_if_mod_four n

/-- **(16.9.2)** (Hardy–Wright). `δ(n) = d₁(n) - d₃(n)`. -/
@[kb "hardywright2008" "(16.9.2), p. 332"]
theorem chi4DivisorSum_eq_card_sub_card (n : ℕ) :
    chi4DivisorSum n = #(n.divisors.filter (· % 4 = 1)) - #(n.divisors.filter (· % 4 = 3)) := by
  rw [chi4DivisorSum]
  have h : ∀ d, chi4 d = (if d % 4 = 1 then 1 else 0) - (if d % 4 = 3 then 1 else 0) := by
    intro d
    rw [chi4_eq]
    have := Nat.mod_lt d (show 0 < 4 by norm_num)
    have h2 : d % 2 = d % 4 % 2 := (Nat.mod_mod_of_dvd d (by norm_num)).symm
    interval_cases h : d % 4 <;> simp_all
  simp only [h, sum_sub_distrib, sum_boole]

/-- `χ` as a (completely) multiplicative arithmetic function. -/
def chi4Fun : ArithmeticFunction ℤ := ⟨chi4, by simp [chi4]⟩

lemma chi4Fun_apply (n : ℕ) : chi4Fun n = chi4 n := rfl

lemma isMultiplicative_chi4Fun : chi4Fun.IsMultiplicative :=
  ⟨by simp [chi4Fun_apply, chi4], fun {m n} _ => by
    simp only [chi4Fun_apply, chi4, Nat.cast_mul, map_mul]⟩

lemma chi4DivisorSum_eq_mul_zeta (n : ℕ) : chi4DivisorSum n = (chi4Fun * ζ) n := by
  rw [coe_mul_zeta_apply, chi4DivisorSum]; rfl

lemma isMultiplicative_chi4DivisorSum :
    (chi4Fun * (ζ : ArithmeticFunction ℤ)).IsMultiplicative :=
  isMultiplicative_chi4Fun.mul isMultiplicative_zeta.natCast

/-- `δ(p^k) = ∑_{i ≤ k} χ(p)^i`. -/
lemma chi4DivisorSum_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    chi4DivisorSum (p ^ k) = ∑ i ∈ range (k + 1), chi4 p ^ i := by
  rw [chi4DivisorSum, Nat.sum_divisors_prime_pow hp]
  refine sum_congr rfl fun i _ => ?_
  simp only [chi4, Nat.cast_pow, map_pow]

/-- The local factor of (16.9.5). -/
def chi4LocalFactor (p a : ℕ) : ℤ :=
  if p % 4 = 1 then a + 1 else if p % 4 = 3 then (if Even a then 1 else 0) else 1

lemma sum_range_neg_one_pow (k : ℕ) :
    ∑ i ∈ range (k + 1), (-1 : ℤ) ^ i = if Even k then 1 else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih]
    rcases Nat.even_or_odd k with h | h
    · have h' : ¬ Even (k + 1) := Nat.not_even_iff_odd.mpr h.add_one
      simp [h, h', pow_succ, h.neg_one_pow]
    · have h' : Even (k + 1) := h.add_one
      have h'' : ¬ Even k := Nat.not_even_iff_odd.mpr h
      simp [h', h'', pow_succ, h.neg_one_pow]

lemma chi4DivisorSum_prime_pow_eq {p : ℕ} (hp : p.Prime) (k : ℕ) :
    chi4DivisorSum (p ^ k) = chi4LocalFactor p k := by
  rw [chi4DivisorSum_prime_pow hp, chi4LocalFactor]
  rcases hp.eq_two_or_odd' with rfl | hodd
  · have : chi4 2 = 0 := by decide
    rw [this, Finset.sum_range_succ']
    simp
  · have h4 : p % 4 = 1 ∨ p % 4 = 3 := by
      have := Nat.mod_lt p (show 0 < 4 by norm_num)
      have h2 : p % 2 = p % 4 % 2 := (Nat.mod_mod_of_dvd p (by norm_num)).symm
      rw [Nat.odd_iff] at hodd
      omega
    rcases h4 with h | h
    · have hc : chi4 p = 1 := ZMod.χ₄_nat_one_mod_four h
      simp [hc, h]
    · have hc : chi4 p = -1 := ZMod.χ₄_nat_three_mod_four h
      rw [hc, sum_range_neg_one_pow]
      simp [h]

/-- **(16.9.5)** (Hardy–Wright). For `n ≥ 1`, `δ(n) = ∏_{p^a ∥ n} e(p, a)` where `e(2, a) = 1`,
`e(p, r) = r + 1` for `p ≡ 1 (mod 4)` and `e(q, s) = (1 + (-1)^s)/2` (that is, `1` for even `s`,
`0` for odd `s`) for `q ≡ 3 (mod 4)`. -/
@[kb "hardywright2008" "(16.9.5), p. 333"]
theorem chi4DivisorSum_eq_prod {n : ℕ} (hn : n ≠ 0) :
    chi4DivisorSum n = ∏ p ∈ n.primeFactors, chi4LocalFactor p (n.factorization p) := by
  rw [chi4DivisorSum_eq_mul_zeta, isMultiplicative_chi4DivisorSum.multiplicative_factorization _ hn,
    Finsupp.prod, Nat.support_factorization]
  refine prod_congr rfl fun p hp => ?_
  rw [← chi4DivisorSum_eq_mul_zeta, chi4DivisorSum_prime_pow_eq (Nat.prime_of_mem_primeFactors hp)]

/-- (16.9.5), first case: if some prime `q ≡ 3 (mod 4)` divides `n` to an odd power (`v` is not a
square), then `δ(n) = 0`. -/
@[kb "hardywright2008" "(16.9.5), p. 333"]
theorem chi4DivisorSum_eq_zero {n : ℕ} (hn : n ≠ 0) {q : ℕ} (hq : q ∈ n.primeFactors)
    (hq3 : q % 4 = 3) (hodd : Odd (n.factorization q)) : chi4DivisorSum n = 0 := by
  rw [chi4DivisorSum_eq_prod hn]
  refine prod_eq_zero hq ?_
  simp [chi4LocalFactor, hq3, Nat.not_even_iff_odd.mpr hodd]

/-- (16.9.5), second case: if every prime `q ≡ 3 (mod 4)` divides `n` to an even power (`v` is a
square), then `δ(n) = d(μ)`, `μ = ∏_{p ≡ 1 (mod 4)} p^r` the part of `n` composed of primes
`≡ 1 (mod 4)`. -/
@[kb "hardywright2008" "(16.9.5), p. 333"]
theorem chi4DivisorSum_eq_card_divisors {n : ℕ} (hn : n ≠ 0)
    (heven : ∀ q ∈ n.primeFactors, q % 4 = 3 → Even (n.factorization q)) :
    chi4DivisorSum n = (∏ p ∈ n.primeFactors with p % 4 = 1, p ^ n.factorization p).divisors.card := by
  rw [chi4DivisorSum_eq_prod hn, ← sigma_zero_apply,
    isMultiplicative_sigma.map_prod (fun p => p ^ n.factorization p)]
  · rw [prod_filter]
    push_cast
    refine prod_congr rfl fun p hp => ?_
    have hpp := Nat.prime_of_mem_primeFactors hp
    rw [sigma_zero_apply_prime_pow hpp, chi4LocalFactor]
    by_cases h1 : p % 4 = 1
    · simp [h1]
    · by_cases h3 : p % 4 = 3
      · simp [h3, heven p hp h3]
      · simp [h1, h3]
  · intro p hp q hq hpq
    simp only [coe_filter, Set.mem_ofPred_eq] at hp hq
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp.1)
      (Nat.prime_of_mem_primeFactors hq.1)).mpr hpq)

end NTKB.HardyWright
