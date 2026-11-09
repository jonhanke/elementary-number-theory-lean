/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Aesop.BuiltinRules
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Bound
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import NTKB.Attr

/-!
# Hardy–Wright, Chapter XVI: the functions `μ(n)`, `d(n)`, `σ(n)`; perfect numbers

* Theorem 264: `∑_{d ∣ n} |μ(d)| = 2^k`, `k` the number of different prime factors of `n`.
* Theorems 274 and 275: the closed forms of `σ_k(n)` and `σ(n)` as products of quotients
  `(p^{(a+1)k} - 1)/(p^k - 1)` (Mathlib has the products of geometric sums).
* Theorem 276 (Euclid): if `2^{n+1} - 1` is prime, then `2^n (2^{n+1} - 1)` is perfect.
* Theorem 277 (Euler): every even perfect number is of that form.

The proofs of Theorems 276 and 277 are those of Hardy and Wright (§ 16.8), through
`σ(2^n b) = (2^{n+1} - 1) σ(b)` for odd `b`.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.sigma ArithmeticFunction.omega

namespace NTKB.HardyWright

/-- **Theorem 264** (Hardy–Wright). If `k` is the number of different prime factors of `n`, then
`∑_{d ∣ n} |μ(d)| = 2^k`. (The book states it for `n > 1`; it holds for every `n ≥ 1`.)
Proof: `|μ(d)|` is the indicator of the squarefree divisors, which are the products of the subsets
of the set of prime factors of `n`. -/
@[kb "hardywright2008" "Thm 264, p. 323"]
theorem sum_divisors_abs_moebius {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, |μ d| = 2 ^ ω n := by
  have h1 : ∑ d ∈ n.divisors, |μ d| = ∑ d ∈ n.divisors with Squarefree d, (1 : ℤ) := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun d _ => abs_moebius
  rw [h1, Nat.sum_divisors_filter_squarefree hn, Finset.sum_const, Finset.card_powerset,
    cardDistinctFactors_eq_card_primeFactors, Nat.factors_eq]
  simp only [nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat]
  rfl

/-- **Theorem 274** (Hardy–Wright). If `k > 0` and `n = ∏ pᵢ^{aᵢ}`, then
`σ_k(n) = ∏ (pᵢ^{(aᵢ+1)k} - 1)/(pᵢ^k - 1)` (each quotient is exact). -/
@[kb "hardywright2008" "Thm 274, p. 330"]
theorem sigma_eq_prod_div {k n : ℕ} (hk : 0 < k) (hn : n ≠ 0) :
    σ k n = ∏ p ∈ n.primeFactors,
      (p ^ ((n.factorization p + 1) * k) - 1) / (p ^ k - 1) := by
  rw [sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp2 : 2 ≤ p ^ k := by
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    calc 2 ≤ p := this
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ k := Nat.pow_le_pow_right (by omega) hk
  have := Nat.geomSum_eq hp2 (n.factorization p + 1)
  simp only [← pow_mul] at this
  rw [mul_comm (n.factorization p + 1) k, ← this]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]

/-- **Theorem 275** (Hardy–Wright). If `n = ∏ pᵢ^{aᵢ}`, then
`σ(n) = ∏ (pᵢ^{aᵢ+1} - 1)/(pᵢ - 1)` (each quotient is exact). -/
@[kb "hardywright2008" "Thm 275, p. 330"]
theorem sigma_one_eq_prod_div {n : ℕ} (hn : n ≠ 0) :
    σ 1 n = ∏ p ∈ n.primeFactors, (p ^ (n.factorization p + 1) - 1) / (p - 1) := by
  simpa using sigma_eq_prod_div (k := 1) one_pos hn

/-- `1 + 2 + ⋯ + 2^n = 2^{n+1} - 1`. -/
private lemma sum_divisors_two_pow (n : ℕ) : ∑ d ∈ (2 ^ n).divisors, d = 2 ^ (n + 1) - 1 := by
  rw [Nat.sum_divisors_prime_pow Nat.prime_two, Nat.geomSum_eq le_rfl]
  simp

/-- For odd `b`, `σ(2^n b) = (2^{n+1} - 1) σ(b)`. -/
private lemma sum_divisors_two_pow_mul {n b : ℕ} (hb : Odd b) :
    ∑ d ∈ (2 ^ n * b).divisors, d = (2 ^ (n + 1) - 1) * ∑ d ∈ b.divisors, d := by
  rw [Nat.Coprime.sum_divisors_mul ((Nat.coprime_two_left.mpr hb).pow_left n),
    sum_divisors_two_pow]

/-- **Theorem 276** (Euclid; Hardy–Wright). If `2^{n+1} - 1` is prime, then `2^n (2^{n+1} - 1)` is
perfect. -/
@[kb "hardywright2008" "Thm 276, p. 330"]
theorem perfect_two_pow_mul_mersenne {n : ℕ} (hp : (2 ^ (n + 1) - 1).Prime) :
    (2 ^ n * (2 ^ (n + 1) - 1)).Perfect := by
  have h1 : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
  have hodd : Odd (2 ^ (n + 1) - 1) := by
    rcases hp.eq_two_or_odd' with h | h
    · have : 2 ^ (n + 1) = 3 := by omega
      have h4 : 2 ^ (n + 1) % 2 = 0 := by
        rw [pow_succ]; simp
      omega
    · exact h
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul (Nat.mul_pos (by positivity) hp.pos),
    sum_divisors_two_pow_mul hodd, Nat.Prime.sum_divisors hp, Nat.sub_add_cancel h1, pow_succ]
  ring

/-- **Theorem 277** (Euler; Hardy–Wright). Every even perfect number is a Euclid number
`2^n (2^{n+1} - 1)` with `2^{n+1} - 1` prime. -/
@[kb "hardywright2008" "Thm 277, p. 331"]
theorem eq_two_pow_mul_mersenne_of_even_perfect {N : ℕ} (hev : Even N) (hN : N.Perfect) :
    ∃ n, (2 ^ (n + 1) - 1).Prime ∧ N = 2 ^ n * (2 ^ (n + 1) - 1) := by
  have hN0 : N ≠ 0 := hN.2.ne'
  obtain ⟨n, b, hb, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hN0
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb
  have hn : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_mul] at hev
    exact (Nat.not_even_iff_odd.mpr hb) hev
  -- `σ(N) = 2N` and `σ(N) = (2^{n+1} - 1) σ(b)`
  have hσ := (Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN
  rw [sum_divisors_two_pow_mul hb] at hσ
  set M := 2 ^ (n + 1) - 1 with hM
  have h2 : 2 ≤ n + 1 := by omega
  have hM3 : 3 ≤ M := by
    have : 4 ≤ 2 ^ (n + 1) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) h2
    omega
  have hσ' : M * ∑ d ∈ b.divisors, d = 2 ^ (n + 1) * b := by rw [hσ]; ring
  -- the fraction `b/σ(b) = M/2^{n+1}` is in lowest terms
  have hcop : M.Coprime (2 ^ (n + 1)) := by
    have h1 : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
    have : 2 ^ (n + 1) = M + 1 := by omega
    rw [this]
    exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right M)
  obtain ⟨c, rfl⟩ : M ∣ b := hcop.dvd_of_dvd_mul_left ⟨_, hσ'.symm⟩
  have hc0 : c ≠ 0 := by rintro rfl; simp at hb0
  have hσc : ∑ d ∈ (M * c).divisors, d = 2 ^ (n + 1) * c := by
    have hMpos : 0 < M := by omega
    have := hσ'
    rw [show 2 ^ (n + 1) * (M * c) = M * (2 ^ (n + 1) * c) by ring] at this
    exact Nat.eq_of_mul_eq_mul_left hMpos this
  -- if `c > 1`, then `σ(b) ≥ b + c + 1 > 2^{n+1} c`
  have hc1 : c = 1 := by
    by_contra hc1
    have hc2 : 2 ≤ c := by omega
    have hsub : ({1, c, M * c} : Finset ℕ) ⊆ (M * c).divisors := by
      intro d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rw [Nat.mem_divisors]
      refine ⟨?_, by positivity⟩
      rcases hd with rfl | rfl | rfl
      · exact one_dvd _
      · exact dvd_mul_left _ _
      · exact dvd_rfl
    have hle := Finset.sum_le_sum_of_subset (f := id) hsub
    have hne1 : (1 : ℕ) ∉ ({c, M * c} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      constructor <;> nlinarith
    have hne2 : c ∉ ({M * c} : Finset ℕ) := by
      simp only [Finset.mem_singleton]
      nlinarith
    rw [Finset.sum_insert hne1, Finset.sum_insert hne2, Finset.sum_singleton] at hle
    simp only [id] at hle
    rw [hσc] at hle
    have : 2 ^ (n + 1) = M + 1 := by
      have h1 : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
      omega
    rw [this] at hle
    nlinarith
  subst hc1
  rw [mul_one] at hσc hb ⊢
  refine ⟨n, ?_, rfl⟩
  -- `σ(M) = M + 1` forces `M` prime
  rw [Nat.sum_divisors_eq_sum_properDivisors_add_self] at hσc
  have : ∑ i ∈ M.properDivisors, i = 1 := by
    have h1 : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
    omega
  exact Nat.sum_properDivisors_eq_one_iff_prime.mp this

end NTKB.HardyWright
