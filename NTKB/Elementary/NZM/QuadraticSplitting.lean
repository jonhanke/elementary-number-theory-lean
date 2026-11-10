/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Attr
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# Rational primes in a quadratic field with unique factorization
(Niven–Zuckerman–Montgomery, Theorem 9.29 (a))

* **Theorem 9.29 (a)** (`prime_or_mul_of_finrank_two`): in a quadratic field whose ring of
  integers has unique factorization, every rational prime `p` is either a prime or a product of
  two primes.  The proof uses the norm: `|N(p)| = p²`, the norm of a non-unit is `> 1`, and the
  norm is multiplicative, so `p` has at most two prime factors.

The remaining parts of Theorem 9.29 (the Legendre symbol criterion, the prime `2`, ramified
primes) are recorded as the proposition `NTKB.NZM.Theorem929` in `EisensteinDescent.lean`.
-/

open NumberField

namespace NTKB.NZM

variable {K : Type*} [Field K] [NumberField K]

/-- The absolute value of the norm, `|N(x)|`, of an integer of a number field. -/
private noncomputable def absN (x : 𝓞 K) : ℕ := (Algebra.norm ℤ x).natAbs

private lemma absN_mul (x y : 𝓞 K) : absN (x * y) = absN x * absN y := by
  simp [absN, map_mul, Int.natAbs_mul]

private lemma absN_eq_one_iff (x : 𝓞 K) : absN x = 1 ↔ IsUnit x := by
  rw [absN, ← Ideal.absNorm_span_singleton, Ideal.absNorm_eq_one_iff, Ideal.span_singleton_eq_top]

private lemma absN_natCast (n : ℕ) : absN (n : 𝓞 K) = n ^ Module.finrank ℚ K := by
  rw [absN, show (n : 𝓞 K) = algebraMap ℤ (𝓞 K) n by simp, Algebra.norm_algebraMap,
    RingOfIntegers.rank]
  simp [Int.natAbs_pow]

private lemma absN_multiset_prod (s : Multiset (𝓞 K)) : absN s.prod = (s.map absN).prod := by
  induction s using Multiset.induction_on with
  | empty => simp [absN]
  | cons a s ih => simp [absN_mul, ih]

private lemma pow_card_dvd_prod (p : ℕ) (s : Multiset ℕ) (h : ∀ a ∈ s, p ∣ a) :
    p ^ s.card ∣ s.prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.card_cons, pow_succ, Multiset.prod_cons, mul_comm (p ^ _)]
    exact mul_dvd_mul (h a (Multiset.mem_cons_self _ _))
      (ih fun b hb => h b (Multiset.mem_cons_of_mem hb))

/-- **Theorem 9.29 (a).**  In a quadratic field `K` (degree `2` over `ℚ`) whose ring of integers
has unique factorization, every rational prime `p` is either a prime of `𝓞 K` or a product of two
primes of `𝓞 K`. -/
@[kb "nivenzuckermanmontgomery" "Thm 9.29, p. 433"]
theorem prime_or_mul_of_finrank_two (hK : Module.finrank ℚ K = 2)
    [UniqueFactorizationMonoid (𝓞 K)] {p : ℕ} (hp : p.Prime) :
    Prime (p : 𝓞 K) ∨ ∃ π₁ π₂ : 𝓞 K, Prime π₁ ∧ Prime π₂ ∧ (p : 𝓞 K) = π₁ * π₂ := by
  classical
  have hNp : absN (p : 𝓞 K) = p ^ 2 := by rw [absN_natCast, hK]
  have hp0 : (p : 𝓞 K) ≠ 0 := by
    intro h
    rw [h] at hNp
    simp [absN] at hNp
    exact hp.ne_zero (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hNp.symm)
  set f := UniqueFactorizationMonoid.factors (p : 𝓞 K) with hf
  have hassoc := UniqueFactorizationMonoid.factors_prod hp0
  rw [← hf] at hassoc
  have hprime : ∀ π ∈ f, Prime π := fun π hπ => UniqueFactorizationMonoid.prime_of_factor π hπ
  -- the norm of the product
  have hNprod : absN f.prod = p ^ 2 := by
    obtain ⟨u, hu⟩ := hassoc
    have : absN (f.prod * (u : 𝓞 K)) = absN f.prod := by
      rw [absN_mul, (absN_eq_one_iff _).2 u.isUnit, mul_one]
    rw [← this, hu, hNp]
  -- each factor has norm divisible by `p`
  have hpdvd : ∀ π ∈ f, p ∣ absN π := by
    intro π hπ
    have h1 : absN π ∣ p ^ 2 := by
      rw [← hNprod, absN_multiset_prod]
      exact Multiset.dvd_prod (Multiset.mem_map_of_mem _ hπ)
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).1 h1
    rcases k with _ | k
    · exact absurd ((absN_eq_one_iff π).1 (by simpa using hk')) (hprime π hπ).not_isUnit
    · rw [hk']; exact dvd_pow_self _ (Nat.succ_ne_zero _)
  have hcard : f.card ≤ 2 := by
    have h := pow_card_dvd_prod p (f.map absN) (by simpa using hpdvd)
    rw [Multiset.card_map, ← absN_multiset_prod, hNprod] at h
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h
  have hpu : ¬ IsUnit (p : 𝓞 K) := by
    rw [← absN_eq_one_iff, hNp]
    intro h
    have := hp.one_lt
    nlinarith
  interval_cases hc : f.card
  · exact absurd (hassoc.isUnit_iff.1 (by simp [Multiset.card_eq_zero.1 hc])) hpu
  · obtain ⟨π, hπ⟩ := Multiset.card_eq_one.1 hc
    rw [hπ, Multiset.prod_singleton] at hassoc
    exact Or.inl (hassoc.prime (hprime π (by simp [hπ])))
  · obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.1 hc
    rw [hab] at hassoc
    simp only [Multiset.insert_eq_cons, Multiset.prod_cons, Multiset.prod_singleton] at hassoc
    obtain ⟨u, hu⟩ := hassoc
    have ha : Prime a := hprime a (by simp [hab])
    have hb : Prime b := hprime b (by simp [hab])
    refine Or.inr ⟨a, b * u, ha, (Associated.prime ⟨u, rfl⟩ hb), ?_⟩
    rw [← hu, mul_assoc]

end NTKB.NZM
