/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.QuadraticFields.QuadInt

/-!
# Fields in which the fundamental theorem is false (Hardy–Wright §§ 14.6, 15.7)

The integers of `k(√-5)` are `a + b√-5` (`QuadraticAlgebra ℤ (-5) 0`), those of `k(√10)` are
`a + b√10` (`QuadraticAlgebra ℤ 10 0`).

* § 14.6 (i) (`sqrtNegFive_two_factorizations`): `2, 3, 1 ± √-5` are irreducible ("prime" in the
  book's sense), `6 = 2·3 = (1 + √-5)(1 - √-5)`, and `2` is associated with neither `1 ± √-5`;
  `not_ufm_sqrtNegFive`: factorisation in `k(√-5)` is not unique.
* § 14.6 (ii) (`sqrtTen_two_factorizations`, `not_ufm_sqrtTen`): the same for
  `6 = 2·3 = (4 + √10)(4 - √10)` in `k(√10)`.
* § 14.6 (`sqrtNegFive_no_bezout`): there are no integers `λ₁, λ₂` of `k(√-5)` with
  `3λ₁ + (1 + √-5)λ₂ = 1`, although `3` and `1 + √-5` have no common factor.
* § 15.7 (`sqrtNegFive_not_principal`): the ideal `[3, -1 + √-5]` of `k(√-5)` is not the class of
  multiples of one integer (so property E fails in `k(√-5)`).
-/

namespace NTKB.HardyWright

open QuadraticAlgebra

/-- The integers `a + b√-5` of `k(√-5)`. -/
abbrev ZSqrtNeg5 := QuadraticAlgebra ℤ (-5) 0

/-- The integers `a + b√10` of `k(√10)`. -/
abbrev ZSqrt10 := QuadraticAlgebra ℤ 10 0

lemma sqrtNegFive_norm (z : ZSqrtNeg5) : norm z = z.re ^ 2 + 5 * z.im ^ 2 := by
  rw [norm_def]; ring

lemma sqrtTen_norm (z : ZSqrt10) : norm z = z.re ^ 2 - 10 * z.im ^ 2 := by
  rw [norm_def]; ring

/-- An element of `ℤ[ω]` whose norm is `±n²` (`n` prime) with no element of norm `±n` is
irreducible. -/
lemma qa_irreducible_of_norm_sq {a b : ℤ} {π : QuadraticAlgebra ℤ a b} {n : ℕ} (hn : n.Prime)
    (hN : (norm π).natAbs = n ^ 2) (h : ∀ z : QuadraticAlgebra ℤ a b, (norm z).natAbs ≠ n) :
    Irreducible π := by
  refine ⟨fun hu ↦ ?_, fun x y hxy ↦ ?_⟩
  · rw [qa_isUnit_iff, hN] at hu
    have h4 : 4 ≤ n ^ 2 := by have := hn.two_le; nlinarith
    omega
  · have h2 := congrArg (fun z ↦ (norm z).natAbs) hxy
    simp only [map_mul, Int.natAbs_mul] at h2
    rw [hN] at h2
    obtain ⟨k, hk, hkn⟩ := (Nat.dvd_prime_pow hn).1 (Dvd.intro _ h2.symm)
    interval_cases k
    · exact Or.inl (qa_isUnit_iff.2 (by simpa using hkn))
    · exact absurd (by simpa using hkn) (h x)
    · right
      rw [hkn] at h2
      have : 0 < n ^ 2 := pow_pos hn.pos 2
      exact qa_isUnit_iff.2 (by nlinarith)

/-- An element of `ℤ[ω]` whose norm is `±pq` (`p, q` primes) with no element of norm `±p` or `±q` is
irreducible. -/
lemma qa_irreducible_of_norm_mul {a b : ℤ} {π : QuadraticAlgebra ℤ a b} {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hN : (norm π).natAbs = p * q)
    (h : ∀ z : QuadraticAlgebra ℤ a b, (norm z).natAbs ≠ p ∧ (norm z).natAbs ≠ q) :
    Irreducible π := by
  refine ⟨fun hu ↦ ?_, fun x y hxy ↦ ?_⟩
  · rw [qa_isUnit_iff, hN] at hu
    exact hp.one_lt.ne' (Nat.eq_one_of_mul_eq_one_right hu)
  · have h2 := congrArg (fun z ↦ (norm z).natAbs) hxy
    simp only [map_mul, Int.natAbs_mul] at h2
    rw [hN] at h2
    have hx : (norm x).natAbs ∣ p * q := Dvd.intro _ h2.symm
    rw [Nat.dvd_mul] at hx
    obtain ⟨d1, d2, hd1, hd2, hd⟩ := hx
    rcases (Nat.dvd_prime hp).1 hd1 with e1 | e1 <;> rcases (Nat.dvd_prime hq).1 hd2 with e2 | e2 <;>
      rw [e1, e2] at hd
    · exact Or.inl (qa_isUnit_iff.2 (by simpa using hd.symm))
    · exact absurd (by simpa using hd.symm) (h x).2
    · exact absurd (by simpa using hd.symm) (h x).1
    · right
      rw [← hd] at h2
      have : 0 < p * q := Nat.mul_pos hp.pos hq.pos
      exact qa_isUnit_iff.2 (by nlinarith)

lemma sqrtNegFive_norm_ne {n : ℕ} (hn : n = 2 ∨ n = 3) (z : ZSqrtNeg5) : (norm z).natAbs ≠ n := by
  rw [sqrtNegFive_norm]
  intro h
  have hnn : 0 ≤ z.re ^ 2 + 5 * z.im ^ 2 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
  have h' : z.re ^ 2 + 5 * z.im ^ 2 = n := by rw [← h, Int.natAbs_of_nonneg hnn]
  have hn3 : (n : ℤ) ≤ 3 := by rcases hn with rfl | rfl <;> norm_num
  have hb : z.im = 0 := by
    by_contra hb
    have : 1 ≤ z.im ^ 2 := by have := sq_pos_of_ne_zero hb; omega
    nlinarith [sq_nonneg z.re]
  rw [hb] at h'
  have : -2 ≤ z.re ∧ z.re ≤ 2 := by constructor <;> nlinarith
  obtain ⟨h1, h2⟩ := this
  interval_cases z.re <;> rcases hn with rfl | rfl <;> norm_num at h'

lemma sqrtTen_norm_ne {n : ℕ} (hn : n = 2 ∨ n = 3) (z : ZSqrt10) : (norm z).natAbs ≠ n := by
  rw [sqrtTen_norm]
  intro h
  -- `a² ≡ ±2, ±3 (mod 10)` is impossible
  rcases Int.natAbs_eq (z.re ^ 2 - 10 * z.im ^ 2) with h' | h' <;> rw [h] at h' <;>
  · have := congrArg (Int.cast : ℤ → ZMod 10) h'
    push_cast at this
    generalize (z.re : ZMod 10) = u at this
    generalize (z.im : ZMod 10) = v at this
    rcases hn with rfl | rfl <;> revert u v <;> decide

/-- **§ 14.6 (i).** In `k(√-5)` the numbers `2, 3, 1 + √-5, 1 - √-5` are irreducible, and
`6 = 2·3 = (1 + √-5)(1 - √-5)` are two decompositions of `6` into primes which are essentially
different (`2` is associated with neither `1 ± √-5`). -/
@[kb "hardywright2008" "§ 14.6, p. 292"]
theorem sqrtNegFive_two_factorizations :
    Irreducible (2 : ZSqrtNeg5) ∧ Irreducible (3 : ZSqrtNeg5) ∧
      Irreducible (⟨1, 1⟩ : ZSqrtNeg5) ∧ Irreducible (⟨1, -1⟩ : ZSqrtNeg5) ∧
      (2 : ZSqrtNeg5) * 3 = ⟨1, 1⟩ * ⟨1, -1⟩ ∧
      ¬ Associated (2 : ZSqrtNeg5) ⟨1, 1⟩ ∧ ¬ Associated (2 : ZSqrtNeg5) ⟨1, -1⟩ := by
  have h2 := sqrtNegFive_norm_ne (n := 2) (Or.inl rfl)
  have h3 := sqrtNegFive_norm_ne (n := 3) (Or.inr rfl)
  refine ⟨qa_irreducible_of_norm_sq Nat.prime_two (by rw [sqrtNegFive_norm]; rfl) h2,
    qa_irreducible_of_norm_sq Nat.prime_three (by rw [sqrtNegFive_norm]; rfl) h3,
    qa_irreducible_of_norm_mul Nat.prime_two Nat.prime_three (by rw [sqrtNegFive_norm]; rfl)
      fun z ↦ ⟨h2 z, h3 z⟩,
    qa_irreducible_of_norm_mul Nat.prime_two Nat.prime_three (by rw [sqrtNegFive_norm]; rfl)
      fun z ↦ ⟨h2 z, h3 z⟩, by ext <;> simp, fun h ↦ ?_, fun h ↦ ?_⟩
  · have := qa_natAbs_norm_eq_of_associated h
    rw [sqrtNegFive_norm, sqrtNegFive_norm] at this
    norm_num at this
  · have := qa_natAbs_norm_eq_of_associated h
    rw [sqrtNegFive_norm, sqrtNegFive_norm] at this
    norm_num at this

/-- Factorisation in `k(√-5)` is not unique: `2` is irreducible but not prime. -/
theorem not_ufm_sqrtNegFive : ¬ UniqueFactorizationMonoid ZSqrtNeg5 := by
  intro h
  obtain ⟨h2, -, -, -, he, -, -⟩ := sqrtNegFive_two_factorizations
  have hp := UniqueFactorizationMonoid.irreducible_iff_prime.1 h2
  have : (2 : ZSqrtNeg5) ∣ ⟨1, 1⟩ * ⟨1, -1⟩ := ⟨3, he.symm⟩
  rcases hp.dvd_or_dvd this with ⟨t, ht⟩ | ⟨t, ht⟩ <;>
  · have := congrArg QuadraticAlgebra.re ht
    simp at this
    omega

/-- **§ 14.6.** In `k(√-5)` there are no integers `λ₁, λ₂` with `3λ₁ + (1 + √-5)λ₂ = 1`. -/
@[kb "hardywright2008" "§ 14.6, p. 293"]
theorem sqrtNegFive_no_bezout : ¬ ∃ x y : ZSqrtNeg5, 3 * x + ⟨1, 1⟩ * y = 1 := by
  rintro ⟨⟨a, b⟩, ⟨c, d⟩, h⟩
  have h1 := congrArg QuadraticAlgebra.re h
  have h2 := congrArg QuadraticAlgebra.im h
  simp at h1 h2
  omega

/-- **§ 15.7.** The lattice `[3, -1 + √-5]` is an ideal of `k(√-5)` which is not the class of
multiples `{ρ}` of any integer `ρ` (so it is not similar to the lattice of all integers). -/
@[kb "hardywright2008" "§ 15.7, p. 316"]
theorem sqrtNegFive_not_principal :
    ¬ (Ideal.span {(3 : ZSqrtNeg5), ⟨-1, 1⟩}).IsPrincipal := by
  rintro ⟨γ, hγ⟩
  change Ideal.span {(3 : ZSqrtNeg5), ⟨-1, 1⟩} = Ideal.span {γ} at hγ
  have h3 : γ ∣ 3 := Ideal.mem_span_singleton.1 (hγ ▸ Ideal.subset_span (by simp))
  have hw : γ ∣ ⟨-1, 1⟩ := Ideal.mem_span_singleton.1 (hγ ▸ Ideal.subset_span (by simp))
  have n3 : (norm γ).natAbs ∣ 9 := by
    have := Int.natAbs_dvd_natAbs.2 (map_dvd QuadraticAlgebra.norm h3)
    have e : (QuadraticAlgebra.norm (3 : ZSqrtNeg5)).natAbs = 9 := by rw [sqrtNegFive_norm]; rfl
    rwa [e] at this
  have nw : (norm γ).natAbs ∣ 6 := by
    have := Int.natAbs_dvd_natAbs.2 (map_dvd QuadraticAlgebra.norm hw)
    have e : (QuadraticAlgebra.norm (⟨-1, 1⟩ : ZSqrtNeg5)).natAbs = 6 := by
      rw [sqrtNegFive_norm]; rfl
    rwa [e] at this
  have n1 : (norm γ).natAbs ∣ 3 := by
    have := Nat.dvd_gcd n3 nw
    simpa using this
  rcases (Nat.dvd_prime Nat.prime_three).1 n1 with h | h
  · -- `γ` is a unity, so `1 = 3x + (-1 + √-5)y`
    have hu : IsUnit γ := qa_isUnit_iff.2 h
    have h1 : (1 : ZSqrtNeg5) ∈ Ideal.span {(3 : ZSqrtNeg5), ⟨-1, 1⟩} := by
      rw [hγ, Ideal.span_singleton_eq_top.2 hu]; trivial
    rw [Ideal.mem_span_pair] at h1
    obtain ⟨⟨a, b⟩, ⟨c, d⟩, h⟩ := h1
    have e1 := congrArg QuadraticAlgebra.re h
    have e2 := congrArg QuadraticAlgebra.im h
    simp at e1 e2
    omega
  · exact sqrtNegFive_norm_ne (Or.inr rfl) γ h

/-- **§ 14.6 (ii).** In `k(√10)` the numbers `2, 3, 4 + √10, 4 - √10` are irreducible, and
`6 = 2·3 = (4 + √10)(4 - √10)` are two essentially different decompositions of `6`. -/
@[kb "hardywright2008" "§ 14.6, p. 292"]
theorem sqrtTen_two_factorizations :
    Irreducible (2 : ZSqrt10) ∧ Irreducible (3 : ZSqrt10) ∧
      Irreducible (⟨4, 1⟩ : ZSqrt10) ∧ Irreducible (⟨4, -1⟩ : ZSqrt10) ∧
      (2 : ZSqrt10) * 3 = ⟨4, 1⟩ * ⟨4, -1⟩ ∧
      ¬ Associated (2 : ZSqrt10) ⟨4, 1⟩ ∧ ¬ Associated (2 : ZSqrt10) ⟨4, -1⟩ := by
  have h2 := sqrtTen_norm_ne (n := 2) (Or.inl rfl)
  have h3 := sqrtTen_norm_ne (n := 3) (Or.inr rfl)
  refine ⟨qa_irreducible_of_norm_sq Nat.prime_two (by rw [sqrtTen_norm]; rfl) h2,
    qa_irreducible_of_norm_sq Nat.prime_three (by rw [sqrtTen_norm]; rfl) h3,
    qa_irreducible_of_norm_mul Nat.prime_two Nat.prime_three (by rw [sqrtTen_norm]; rfl)
      fun z ↦ ⟨h2 z, h3 z⟩,
    qa_irreducible_of_norm_mul Nat.prime_two Nat.prime_three (by rw [sqrtTen_norm]; rfl)
      fun z ↦ ⟨h2 z, h3 z⟩, by ext <;> simp, fun h ↦ ?_, fun h ↦ ?_⟩
  · have := qa_natAbs_norm_eq_of_associated h
    rw [sqrtTen_norm, sqrtTen_norm] at this
    norm_num at this
  · have := qa_natAbs_norm_eq_of_associated h
    rw [sqrtTen_norm, sqrtTen_norm] at this
    norm_num at this

/-- Factorisation in `k(√10)` is not unique. -/
theorem not_ufm_sqrtTen : ¬ UniqueFactorizationMonoid ZSqrt10 := by
  intro h
  obtain ⟨h2, -, -, -, he, -, -⟩ := sqrtTen_two_factorizations
  have hp := UniqueFactorizationMonoid.irreducible_iff_prime.1 h2
  have : (2 : ZSqrt10) ∣ ⟨4, 1⟩ * ⟨4, -1⟩ := ⟨3, he.symm⟩
  rcases hp.dvd_or_dvd this with ⟨t, ht⟩ | ⟨t, ht⟩ <;>
  · have := congrArg QuadraticAlgebra.im ht
    simp at this
    omega

end NTKB.HardyWright
