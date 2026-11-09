/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Attr
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.Zsqrtd.Basic
import Aesop.BuiltinRules
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
/-!
# Primes of a field divide exactly one rational prime (Hardy–Wright, Theorem 250)

The argument of § 15.1: a prime `π` divides its norm, a positive rational integer, hence (being prime)
one of its rational prime factors `p`; it cannot divide two rational primes `p ≠ p'`, since then it
would divide `px - p'y = 1`.

* `exists_nat_prime_dvd`, `eq_of_prime_dvd_nat_prime`: the two halves, in any commutative ring.
* `existsUnique_nat_prime_dvd` (Theorem 250): in the ring of integers of a number field (in
  particular of a quadratic field `k(√m)`, simple or not), every prime divides exactly one positive
  rational prime.
* `zsqrtd_irreducible_of_natAbs_norm_prime` (Theorem 241 for `ℤ[√d]`): an integer of `ℤ[√d]` whose norm is
  `±` a rational prime is irreducible.
-/

namespace NTKB.HardyWright

open NumberField

section ring

variable {R : Type*} [CommRing R] {π : R}

/-- A prime `π` dividing a positive integer `n` divides one of its rational prime factors. -/
lemma exists_nat_prime_dvd (hπ : Prime π) {n : ℕ} (hn : n ≠ 0) (h : π ∣ (n : R)) :
    ∃ p : ℕ, p.Prime ∧ π ∣ (p : R) := by
  rw [← Nat.prod_primeFactorsList hn, Nat.cast_list_prod] at h
  obtain ⟨a, ha, hπa⟩ := hπ.dvd_prod_iff.1 h
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 ha
  exact ⟨q, Nat.prime_of_mem_primeFactorsList hq, hπa⟩

/-- A prime `π` cannot divide two different rational primes. -/
lemma eq_of_prime_dvd_nat_prime (hπ : Prime π) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h1 : π ∣ (p : R)) (h2 : π ∣ (q : R)) : p = q := by
  by_contra hne
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hne)
  have : (u : R) * p + v * q = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → R) huv
  exact hπ.not_isUnit (isUnit_of_dvd_one (this ▸ dvd_add (h1.mul_left _) (h2.mul_left _)))

end ring

/-- **Theorem 250.** Any prime `π` of (the ring of integers of) a number field, in particular of a
quadratic field `k(√m)`, is a divisor of just one positive rational prime. -/
@[kb "hardywright2008" "Thm 250, p. 302"]
theorem existsUnique_nat_prime_dvd {K : Type*} [Field K] [NumberField K] {π : 𝓞 K}
    (hπ : Prime π) : ∃! p : ℕ, p.Prime ∧ π ∣ (p : 𝓞 K) := by
  have hn : Ideal.absNorm (Ideal.span {π}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hπ.ne_zero
  have hdvd : π ∣ (Ideal.absNorm (Ideal.span {π}) : 𝓞 K) :=
    Ideal.mem_span_singleton.1 (Ideal.absNorm_mem _)
  obtain ⟨p, hp, hπp⟩ := exists_nat_prime_dvd hπ hn hdvd
  exact ⟨p, ⟨hp, hπp⟩, fun q ⟨hq, hπq⟩ ↦ eq_of_prime_dvd_nat_prime hπ hq hp hπq hπp⟩

/-- Theorem 241 for `ℤ[√d]`: an element whose norm is `±` a rational prime is irreducible. -/
lemma zsqrtd_irreducible_of_natAbs_norm_prime {d : ℤ} {π : ℤ√d} (h : π.norm.natAbs.Prime) :
    Irreducible π := by
  refine ⟨fun hu ↦ ?_, fun a b hab ↦ ?_⟩
  · rw [← Zsqrtd.norm_eq_one_iff] at hu
    exact h.one_lt.ne' hu
  · rw [hab, Zsqrtd.norm_mul, Int.natAbs_mul] at h
    rcases Nat.prime_mul_iff.1 h with ⟨-, h1⟩ | ⟨-, h1⟩
    · exact Or.inr (Zsqrtd.norm_eq_one_iff.1 h1)
    · exact Or.inl (Zsqrtd.norm_eq_one_iff.1 h1)

/-- In `ℤ[√d]`, an element divides (the image of) its norm. -/
lemma zsqrtd_dvd_natAbs_norm {d : ℤ} (π : ℤ√d) : π ∣ ((π.norm.natAbs : ℤ) : ℤ√d) := by
  rcases Int.natAbs_eq π.norm with h | h
  · rw [← h, Zsqrtd.norm_eq_mul_conj]; exact dvd_mul_right _ _
  · rw [show (π.norm.natAbs : ℤ) = -π.norm by omega, Int.cast_neg, Zsqrtd.norm_eq_mul_conj]
    exact (dvd_mul_right _ _).neg_right

end NTKB.HardyWright
