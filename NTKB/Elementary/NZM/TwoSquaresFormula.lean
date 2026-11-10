/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.NZM.TwoSquaresCount
import NTKB.Elementary.HardyWright.CompositeModuli.Roots

/-!
# The formula for the number of proper representations as a sum of two squares
(Niven–Zuckerman–Montgomery, § 3.6)

**Theorem 3.22**: for `n > 0`, `r(n) = 2 ^ (t + 2)` if `2² ∤ n` and no prime `q ≡ 3 (mod 4)` divides
`n` (where `t` is the number of distinct primes `p ≡ 1 (mod 4)` dividing `n`), and `r(n) = 0`
otherwise.

By Theorem 3.21, `r(n) = 4 N(n)`, where `N(n)` counts the solutions of `s² ≡ -1 (mod n)`. We show
that `N` is multiplicative over the prime power factorization (Chinese remainder theorem, Hardy–Wright
Theorem 122) and compute it on prime powers: `N(2) = 1`, `N(2^a) = 0` for `a ≥ 2`, `N(q^c) = 0` for
`q ≡ 3 (mod 4)`, and `N(p^b) = 2` for `p ≡ 1 (mod 4)` (each of the two roots modulo `p` lifts
uniquely, by Hensel's lemma in the form of Hardy–Wright Theorem 123).
-/

namespace NTKB.NZM

open Polynomial Finset NTKB.HardyWright

lemma rootCount_sq_add_one_eq (m : ℕ) :
    rootCount (X ^ 2 + 1) m = Nat.card {x : ZMod m // x ^ 2 + 1 = 0} := by
  unfold rootCount
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x ↦ by simp)

/-- If `d ∣ m` and the congruence has no roots modulo `d`, it has none modulo `m`. -/
lemma rootCount_sq_add_one_eq_zero_of_dvd {d m : ℕ} (hdm : d ∣ m)
    (h : ∀ x : ZMod d, x ^ 2 + 1 ≠ 0) : rootCount (X ^ 2 + 1) m = 0 := by
  rw [rootCount_sq_add_one_eq]
  have : IsEmpty {x : ZMod m // x ^ 2 + 1 = 0} := by
    refine ⟨fun ⟨x, hx⟩ ↦ h (ZMod.castHom hdm (ZMod d) x) ?_⟩
    have := congrArg (ZMod.castHom hdm (ZMod d)) hx
    rwa [map_add, map_pow, map_one, map_zero] at this
  exact Nat.card_of_isEmpty

lemma negOneSqrtCount_two : negOneSqrtCount 2 = 1 := by
  unfold negOneSqrtCount
  rw [rootCount_sq_add_one_eq, Nat.card_eq_fintype_card]
  decide

lemma negOneSqrtCount_two_pow {a : ℕ} (ha : 2 ≤ a) : negOneSqrtCount (2 ^ a) = 0 := by
  refine rootCount_sq_add_one_eq_zero_of_dvd (d := 4) ?_ (by decide)
  exact (pow_dvd_pow 2 ha : 2 ^ 2 ∣ 2 ^ a)

lemma negOneSqrtCount_prime_pow_three {q a : ℕ} (hq : q.Prime) (hq3 : q % 4 = 3) (ha : 1 ≤ a) :
    negOneSqrtCount (q ^ a) = 0 := by
  have : Fact q.Prime := ⟨hq⟩
  refine rootCount_sq_add_one_eq_zero_of_dvd (d := q) (dvd_pow_self q (by omega)) fun x hx ↦ ?_
  have : IsSquare (-1 : ZMod q) := ⟨x, by linear_combination -hx⟩
  exact (ZMod.exists_sq_eq_neg_one_iff.1 this) hq3

lemma negOneSqrtCount_prime_one {p : ℕ} (hp : p.Prime) (h : p % 4 = 1) :
    negOneSqrtCount p = 2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  unfold negOneSqrtCount
  rw [rootCount_sq_add_one_eq, Nat.card_eq_fintype_card, Fintype.card_subtype]
  obtain ⟨y, hy⟩ := ZMod.exists_sq_eq_neg_one_iff.2 (show p % 4 ≠ 3 by omega)
  have hne : y ≠ -y := by
    intro h2
    have h3 : (2 : ZMod p) * y = 0 := by linear_combination h2
    have hy0 : y ≠ 0 := by
      rintro rfl
      have : (-1 : ZMod p) = 0 := by simpa using hy
      exact one_ne_zero (neg_eq_zero.1 this)
    have h2z : (2 : ZMod p) ≠ 0 := by
      intro h4
      have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h4
      rw [ZMod.natCast_eq_zero_iff] at this
      have := Nat.le_of_dvd (by norm_num) this
      have := hp.two_le
      omega
    exact (mul_ne_zero h2z hy0) h3
  have : (Finset.univ.filter fun x : ZMod p ↦ x ^ 2 + 1 = 0) = {y, -y} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hx
      have : x ^ 2 = y ^ 2 := by linear_combination hx + hy
      exact sq_eq_sq_iff_eq_or_eq_neg.1 this
    · rintro (rfl | rfl) <;> linear_combination -hy
  rw [this, Finset.card_pair hne]

lemma negOneSqrtCount_prime_pow_one {p a : ℕ} (hp : p.Prime) (h : p % 4 = 1) (ha : 1 ≤ a) :
    negOneSqrtCount (p ^ a) = 2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  induction a, ha using Nat.le_induction with
  | base => rw [pow_one]; exact negOneSqrtCount_prime_one hp h
  | succ a ha ih =>
    unfold negOneSqrtCount at ih ⊢
    rw [rootCount_prime_pow _ hp (by omega), Nat.add_sub_cancel]
    have h1 : ∀ ξ ∈ (range (p ^ a)).filter
        (fun ξ : ℕ ↦ (p : ℤ) ^ a ∣ (X ^ 2 + 1 : ℤ[X]).eval ((ξ : ℕ) : ℤ)),
        numLifts (X ^ 2 + 1) p (a + 1) ((ξ : ℕ) : ℤ) = 1 := by
      intro ξ hξ
      simp only [Finset.mem_filter, Finset.mem_range] at hξ
      have hξ' : (p : ℤ) ^ (a + 1 - 1) ∣ (X ^ 2 + 1 : ℤ[X]).eval ((ξ : ℕ) : ℤ) := by
        rw [Nat.add_sub_cancel]; exact hξ.2
      refine numLifts_eq_one _ hp (by omega) hξ' ?_
      have hpZ := Nat.prime_iff_prime_int.1 hp
      have hpξ : ¬(p : ℤ) ∣ (ξ : ℤ) := by
        intro hd
        have h2 : (p : ℤ) ∣ (ξ : ℤ) ^ 2 + 1 :=
          (dvd_pow_self (p : ℤ) (show a ≠ 0 by omega)).trans (by simpa using hξ.2)
        have h1 : (p : ℤ) ∣ (ξ : ℤ) ^ 2 := dvd_pow hd (by omega)
        have := dvd_sub h2 h1
        simp only [add_sub_cancel_left] at this
        exact hpZ.not_dvd_one this
      simp only [derivative_add, derivative_X_pow, derivative_one, add_zero, eval_mul, eval_C,
        eval_pow, eval_X]
      intro hd
      rcases hpZ.dvd_or_dvd hd with hd | hd
      · have h2 : p ∣ 2 := by
          have : (p : ℤ) ∣ ((2 : ℕ) : ℤ) := by simpa using hd
          exact_mod_cast this
        have := Nat.le_of_dvd (by norm_num) h2
        have := hp.two_le
        omega
      · exact hpξ (by simpa using hd)
    rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul, mul_one]
    refine Eq.trans ?_ ih
    rw [rootCount_eq_card_range _ (pow_pos hp.pos a)]
    push_cast
    rfl

/-- `N(n)` is the product of `N(p^{v_p(n)})` over the primes `p ∣ n`. -/
lemma negOneSqrtCount_eq_prod {n : ℕ} (hn : n ≠ 0) :
    negOneSqrtCount n = ∏ p ∈ n.primeFactors, negOneSqrtCount (p ^ n.factorization p) := by
  unfold negOneSqrtCount
  conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn]
  refine rootCount_prod _ _ _ fun p hp q hq hpq ↦ ?_
  have hp' := Nat.prime_of_mem_primeFactors hp
  have hq' := Nat.prime_of_mem_primeFactors hq
  exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp' hq').2 hpq)

/-- **Theorem 3.22**. For `n > 0`, `r(n) = 2 ^ (t + 2)`, where `t` is the number of primes
`p ≡ 1 (mod 4)` dividing `n`, if `4 ∤ n` and no prime `q ≡ 3 (mod 4)` divides `n`; otherwise
`r(n) = 0`. -/
@[kb "nivenzuckermanmontgomery" "Thm 3.22, p. 166"]
theorem properSqRepCount_eq {n : ℕ} (hn : 0 < n) :
    properSqRepCount n =
      if n.factorization 2 ≤ 1 ∧ ∀ q ∈ n.primeFactors, q % 4 ≠ 3 then
        2 ^ (#(n.primeFactors.filter fun p ↦ p % 4 = 1) + 2)
      else 0 := by
  classical
  rw [properSqRepCount_eq_four_mul hn, negOneSqrtCount_eq_prod hn.ne']
  split_ifs with h
  · obtain ⟨h2, hq⟩ := h
    have : ∀ p ∈ n.primeFactors, negOneSqrtCount (p ^ n.factorization p) =
        if p % 4 = 1 then 2 else 1 := by
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpos : 0 < n.factorization p :=
        hpp.factorization_pos_of_dvd hn.ne' (Nat.dvd_of_mem_primeFactors hp)
      rcases hpp.eq_two_or_odd' with rfl | hodd
      · have : n.factorization 2 = 1 := by omega
        rw [this]; simpa using negOneSqrtCount_two
      · have h4 : p % 4 = 1 := by
          have := hq p hp
          have := Nat.odd_iff.1 hodd
          omega
        rw [if_pos h4]; exact negOneSqrtCount_prime_pow_one hpp h4 hpos
    rw [Finset.prod_congr rfl this, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one,
      mul_one, pow_add]
    ring
  · have : ∃ p ∈ n.primeFactors, negOneSqrtCount (p ^ n.factorization p) = 0 := by
      by_cases h2 : n.factorization 2 ≤ 1
      · have hq : ∃ q ∈ n.primeFactors, q % 4 = 3 := by
          by_contra hc
          push Not at hc
          exact h ⟨h2, hc⟩
        obtain ⟨q, hq, hq3⟩ := hq
        have hqp := Nat.prime_of_mem_primeFactors hq
        exact ⟨q, hq, negOneSqrtCount_prime_pow_three hqp hq3
          (hqp.factorization_pos_of_dvd hn.ne' (Nat.dvd_of_mem_primeFactors hq))⟩
      · refine ⟨2, ?_, negOneSqrtCount_two_pow (by omega)⟩
        simp only [Nat.mem_primeFactors]
        refine ⟨Nat.prime_two, ?_, hn.ne'⟩
        by_contra hc
        exact h2 (by simp [Nat.factorization_eq_zero_of_not_dvd hc])
    obtain ⟨p, hp, hz⟩ := this
    rw [Finset.prod_eq_zero hp hz, mul_zero]

end NTKB.NZM
