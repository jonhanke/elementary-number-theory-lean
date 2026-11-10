/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Attr
import NTKB.Elementary.NZM.Lucas
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Smeval
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Polynomial functions, singular lifting, and some definitions (Niven–Zuckerman–Montgomery)

* Theorem 2.28: every function `ZMod p → ZMod p` is given by a polynomial of degree `≤ p - 1`
  (with the uniqueness of such a polynomial).
* Theorem 2.24: lifting of singular roots of `f(x) ≡ 0 (mod pʲ)`.
* Definitions: triangular numbers, integer-valued polynomials, powerful numbers, Lucas probable
  primes and Lucas pseudoprimes, each with a small sanity lemma.
-/

open Polynomial

namespace NTKB.NZM

/-! ### Theorem 2.28 -/

/-- **Theorem 2.28.** Every function `F` from residue classes mod `p` to residue classes mod `p`
is a polynomial function of degree at most `p - 1`. -/
@[kb "nivenzuckermanmontgomery" "Thm 2.28, p. 94"]
theorem exists_polynomial_eval_eq (p : ℕ) [Fact p.Prime] (F : ZMod p → ZMod p) :
    ∃ P : Polynomial (ZMod p), P.natDegree ≤ p - 1 ∧ ∀ x : ZMod p, P.eval x = F x := by
  have hp1 : 1 ≤ p - 1 := by
    have := (Fact.out : p.Prime).two_le
    omega
  refine ⟨∑ a : ZMod p, C (F a) * (1 - (X - C a) ^ (p - 1)), ?_, ?_⟩
  · refine natDegree_sum_le_of_forall_le _ _ (fun a _ => ?_)
    refine (natDegree_C_mul_le _ _).trans ?_
    refine (natDegree_sub_le _ _).trans ?_
    have : ((X - C a : Polynomial (ZMod p)) ^ (p - 1)).natDegree ≤ p - 1 :=
      (natDegree_pow_le).trans (by
        have : (X - C a : Polynomial (ZMod p)).natDegree ≤ 1 :=
          (natDegree_sub_le _ _).trans (by simp)
        simp)
    simp
  · intro x
    rw [eval_finsetSum,Finset.sum_eq_single x]
    · simp [zero_pow (by omega : p - 1 ≠ 0)]
    · intro a _ hax
      have : x - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hax)
      simp [ZMod.pow_card_sub_one_eq_one this]
    · simp

/-- Uniqueness in Theorem 2.28: two polynomials over `ZMod p` of degree `≤ p - 1` inducing the same
function are equal. -/
@[kb "nivenzuckermanmontgomery" "Thm 2.28, p. 94"]
theorem polynomial_eq_of_eval_eq (p : ℕ) [Fact p.Prime] {P Q : Polynomial (ZMod p)}
    (hP : P.natDegree ≤ p - 1) (hQ : Q.natDegree ≤ p - 1) (h : ∀ x : ZMod p, P.eval x = Q.eval x) :
    P = Q := by
  have hp1 : 1 ≤ p - 1 := by
    have := (Fact.out : p.Prime).two_le
    omega
  refine Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq (s := (Finset.univ : Finset (ZMod p)))
    ?_ (fun x _ => h x)
  rw [Finset.card_univ, ZMod.card]
  have h1 : (P - Q).natDegree ≤ p - 1 := (natDegree_sub_le _ _).trans (max_le hP hQ)
  have h2 : (P - Q).degree ≤ ((p - 1 : ℕ) : WithBot ℕ) := degree_le_of_natDegree_le h1
  refine lt_of_le_of_lt h2 ?_
  exact_mod_cast (by have := (Fact.out : p.Prime).two_le; omega : p - 1 < p)

/-! ### Theorem 2.24 -/

/-- **Theorem 2.24.** Let `f ∈ ℤ[x]`, `p` a prime, `pʲ ∣ f(a)`, `p^τ ∥ f'(a)` and `j ≥ 2τ + 1`.
(1) If `b ≡ a (mod p^(j-τ))` then `f(b) ≡ f(a) (mod pʲ)` and `p^τ ∥ f'(b)`.
(2) There is a `t`, unique mod `p`, with `f(a + t p^(j-τ)) ≡ 0 (mod p^(j+1))`: precisely, the
integers `s` with `p^(j+1) ∣ f(a + s p^(j-τ))` form the residue class `t` mod `p`. -/
@[kb "nivenzuckermanmontgomery" "Thm 2.24, p. 89"]
theorem lift_singular_root (f : Polynomial ℤ) {p : ℕ} (hp : p.Prime) {a : ℤ} {j τ : ℕ}
    (hj : 2 * τ + 1 ≤ j) (hfa : (p : ℤ) ^ j ∣ f.eval a)
    (hd : (p : ℤ) ^ τ ∣ (derivative f).eval a) (hd' : ¬ (p : ℤ) ^ (τ + 1) ∣ (derivative f).eval a) :
    (∀ b : ℤ, (p : ℤ) ^ (j - τ) ∣ b - a →
      (p : ℤ) ^ j ∣ f.eval b - f.eval a ∧ (p : ℤ) ^ τ ∣ (derivative f).eval b ∧
        ¬ (p : ℤ) ^ (τ + 1) ∣ (derivative f).eval b) ∧
    ∃ t : ℤ, ∀ s : ℤ, (p : ℤ) ^ (j + 1) ∣ f.eval (a + s * (p : ℤ) ^ (j - τ)) ↔ s ≡ t [ZMOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨k, rfl⟩ : ∃ k, j = τ + k := ⟨j - τ, by omega⟩
  have e : τ + k - τ = k := by omega
  simp only [e]
  have hk : τ + 1 ≤ k := by omega
  obtain ⟨d, hdk⟩ : ∃ d, 2 * k = (τ + k + 1) + d := ⟨2 * k - (τ + k + 1), by omega⟩
  obtain ⟨u, hu⟩ := hfa
  obtain ⟨v, hv⟩ := hd
  have hpv : ¬ (p : ℤ) ∣ v := by
    rintro ⟨w, rfl⟩
    exact hd' ⟨w, by rw [hv]; ring⟩
  have h1 : (p : ℤ) ^ τ * (p : ℤ) ^ k = (p : ℤ) ^ (τ + k) := (pow_add _ _ _).symm
  have h2 : ((p : ℤ) ^ k) ^ 2 = (p : ℤ) ^ (τ + k + 1) * (p : ℤ) ^ d := by
    rw [← pow_add, ← pow_mul]
    congr 1
    omega
  have key : ∀ s : ℤ, ∃ c : ℤ, f.eval (a + s * (p : ℤ) ^ k) =
      (p : ℤ) ^ (τ + k) * (u + s * v) + (p : ℤ) ^ (τ + k + 1) * c := by
    intro s
    obtain ⟨c, hc⟩ := binomExpansion f a (s * (p : ℤ) ^ k)
    refine ⟨c * s ^ 2 * (p : ℤ) ^ d, ?_⟩
    rw [hc, hu, hv]
    linear_combination (v * s) * h1 + (c * s ^ 2) * h2
  refine ⟨?_, ?_⟩
  · intro b hb
    obtain ⟨s, hs⟩ := hb
    have hb' : b = a + s * (p : ℤ) ^ k := by linear_combination hs
    obtain ⟨c, hc⟩ := key s
    have hdd : (p : ℤ) ^ k ∣ (derivative f).eval b - (derivative f).eval a :=
      dvd_trans ⟨s, hs⟩ (Polynomial.sub_dvd_eval_sub b a (derivative f))
    refine ⟨⟨s * v + p * c, ?_⟩, ?_, ?_⟩
    · rw [hb', hc, hu]
      ring
    · have : (derivative f).eval b = ((derivative f).eval b - (derivative f).eval a) +
          (derivative f).eval a := by ring
      rw [this]
      exact dvd_add (dvd_trans (pow_dvd_pow _ (by omega)) hdd) ⟨v, hv⟩
    · intro h
      apply hd'
      have : (derivative f).eval a = (derivative f).eval b -
          ((derivative f).eval b - (derivative f).eval a) := by ring
      rw [this]
      exact dvd_sub h (dvd_trans (pow_dvd_pow _ hk) hdd)
  · have hv0 : ((v : ℤ) : ZMod p) ≠ 0 := fun h =>
      hpv ((ZMod.intCast_zmod_eq_zero_iff_dvd v p).mp h)
    set x : ZMod p := -((u : ℤ) : ZMod p) / ((v : ℤ) : ZMod p) with hx
    refine ⟨((x.val : ℕ) : ℤ), fun s => ?_⟩
    have hT : ((((x.val : ℕ) : ℤ)) : ZMod p) = x := by simp
    obtain ⟨c, hc⟩ := key s
    have e1 : (p : ℤ) ^ (τ + k + 1) = (p : ℤ) ^ (τ + k) * p := pow_succ _ _
    have h3 : (p : ℤ) ^ (τ + k + 1) ∣ f.eval (a + s * (p : ℤ) ^ k) ↔ (p : ℤ) ∣ u + s * v := by
      rw [hc, dvd_add_left (dvd_mul_right _ _), e1, mul_dvd_mul_iff_left (pow_ne_zero _ hp0)]
    have h4 : (p : ℤ) ∣ u + s * v ↔ ((s : ℤ) : ZMod p) = x := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hx, eq_div_iff hv0]
      push_cast
      constructor <;> intro h <;> linear_combination h
    rw [h3, h4, ← ZMod.intCast_eq_intCast_iff, hT]

/-! ### Triangular numbers -/

/-- The `n`-th triangular number `n (n + 1) / 2`. -/
@[kb "nivenzuckermanmontgomery" "Problem 1.48, p. 19"]
def triangular (n : ℕ) : ℕ := n * (n + 1) / 2

/-- The triangular number `n (n + 1) / 2` is the sum `1 + 2 + ⋯ + n`. -/
theorem triangular_eq_sum (n : ℕ) : triangular n = ∑ i ∈ Finset.range n, (i + 1) := by
  induction n with
  | zero => simp [triangular]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    unfold triangular
    have : (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) := by ring
    rw [this, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]

/-! ### Integer-valued polynomials -/

/-- A polynomial with rational coefficients is *integer-valued* if it takes integer values at
all integers. -/
@[kb "nivenzuckermanmontgomery" "Def (integer-valued), p. 38"]
def IsIntegerValued (f : Polynomial ℚ) : Prop :=
  ∀ n : ℤ, ∃ m : ℤ, f.eval (n : ℚ) = m

/-- The binomial polynomial `X (X - 1) ⋯ (X - k + 1) / k!` (as a rational polynomial) is
integer-valued. -/
theorem isIntegerValued_binomial (k : ℕ) :
    IsIntegerValued (C (1 / (k.factorial : ℚ)) * descPochhammer ℚ k) := by
  intro n
  refine ⟨Ring.choose n k, ?_⟩
  have h1 : (descPochhammer ℚ k).eval (n : ℚ) = (((descPochhammer ℤ k).eval n : ℤ) : ℚ) := by
    rw [← descPochhammer_map (Int.castRingHom ℚ) k, eval_intCast_map]
    rfl
  have h2 : (descPochhammer ℤ k).eval n = (k.factorial : ℤ) * Ring.choose n k := by
    rw [eval_eq_smeval, Ring.descPochhammer_eq_factorial_smul_choose, nsmul_eq_mul]
  rw [eval_mul, eval_C, h1, h2]
  have : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  push_cast
  field_simp

/-- Polynomials with integer coefficients are integer-valued. -/
theorem isIntegerValued_map_int (g : Polynomial ℤ) : IsIntegerValued (g.map (Int.castRingHom ℚ)) := by
  intro n
  exact ⟨g.eval n, by rw [eval_intCast_map]; rfl⟩

/-! ### Powerful numbers -/

/-- A positive integer `a` is *powerful* if `p² ∣ a` whenever `p ∣ a` (`p` prime). -/
@[kb "nivenzuckermanmontgomery" "Problem 5.12, p. 219"]
def IsPowerful (a : ℕ) : Prop :=
  0 < a ∧ ∀ p : ℕ, p.Prime → p ∣ a → p ^ 2 ∣ a

/-- Positive squares are powerful. -/
theorem isPowerful_sq {n : ℕ} (hn : 0 < n) : IsPowerful (n ^ 2) := by
  refine ⟨by positivity, fun p hp h => ?_⟩
  exact pow_dvd_pow_of_dvd (hp.dvd_of_dvd_pow h) 2

/-! ### Lucas probable primes and pseudoprimes -/

/-- A *Lucas probable prime* (for the parameters `a, b`, `D = a² + 4b`): an odd positive integer
`n` with Jacobi symbol `(D / n) = -1` and `n ∣ U_{n+1}(a, b)`. -/
@[kb "nivenzuckermanmontgomery" "Def (Lucas probable prime), p. 203"]
def IsLucasProbablePrime (a b : ℤ) (n : ℕ) : Prop :=
  Odd n ∧ jacobiSym (a ^ 2 + 4 * b) n = -1 ∧ (n : ℤ) ∣ lucasU a b (n + 1)

/-- A *Lucas pseudoprime* is a composite Lucas probable prime. -/
@[kb "nivenzuckermanmontgomery" "Def (Lucas pseudoprime), p. 203"]
def IsLucasPseudoprime (a b : ℤ) (n : ℕ) : Prop :=
  IsLucasProbablePrime a b n ∧ 1 < n ∧ ¬ n.Prime

/-- Sanity check (Theorem 4.12): an odd prime `p` with `(D/p) = -1` is a Lucas probable prime. -/
theorem isLucasProbablePrime_of_prime {a b : ℤ} {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hD : legendreSym p (a ^ 2 + 4 * b) = -1) : IsLucasProbablePrime a b p := by
  refine ⟨hp.out.odd_of_ne_two hp2, ?_, prime_dvd_lucasU_succ hp2 hD⟩
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  exact hD

end NTKB.NZM
