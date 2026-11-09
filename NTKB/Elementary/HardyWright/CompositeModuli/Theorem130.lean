/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.RingTheory.Polynomial.Vieta
import NTKB.Elementary.HardyWright.CompositeModuli.Bauer

/-!
# Homogeneous products of the residues prime to `p^a` (Hardy–Wright, § 8.8 (2))

* Theorem 130: if `A_{2v+1}` is the sum of the products, `2v + 1` at a time, of the numbers of
  `t(p^a)` (`p` an odd prime), and `2v` is not a multiple of `p - 1`, then
  `A_{2v+1} ≡ 0 (mod p^{2a})`.

Following the book: `f(x) = f_{p^a}(x)` satisfies `f(x) = f(p^a - x)`, so
`f(-x) - f(x) = f(p^a + x) - f(x) ≡ p^a f'(x) (mod p^{2a})`, while by Theorem 126
`p^a f'(x) ≡ p^{2a-1} (p - 1) x^{p-2} (x^{p-1} - 1)^{p^{a-1}-1} (mod p^{2a})`; and the left side is
`2 (A_1 x^{φ-1} + A_3 x^{φ-3} + ⋯)`.
-/

open Polynomial Finset

namespace NTKB.HardyWright

lemma coeff_comp_neg_X {R : Type*} [CommRing R] (f : R[X]) (n : ℕ) :
    (f.comp (-X)).coeff n = (-1) ^ n * f.coeff n := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => rw [add_comp, coeff_add, coeff_add, hp, hq, mul_add]
  | monomial k a =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp, neg_pow,
      show ((-1 : R[X]) ^ k * X ^ k) = C ((-1 : R) ^ k) * X ^ k by simp, ← mul_assoc, ← C_mul,
      coeff_C_mul, coeff_C_mul, coeff_X_pow]
    split_ifs with h
    · subst h; ring
    · simp

/-- Taylor's formula to first order: `f(x + c) = f(x) + c f'(x) + c² K(x)`. -/
lemma exists_comp_X_add_C (f : ℤ[X]) (c : ℤ) :
    ∃ K : ℤ[X], f.comp (X + C c) = f + derivative f * C c + K * (C c) ^ 2 := by
  obtain ⟨K, hK⟩ := binomExpansion (f.map (C : ℤ →+* ℤ[X])) X (C c)
  refine ⟨K, ?_⟩
  rw [eval_map, eval_map, derivative_map, eval_map, eval₂_C_X, eval₂_C_X] at hK
  exact hK

/-- `f_n(n - x) = f_n(x)` for `n > 2`: `t ↦ n - t` permutes `t(n)` and `φ(n)` is even. -/
lemma bauerPoly_comp_sub {n : ℕ} (hn : 2 < n) : (bauerPoly n).comp (C (n : ℤ) - X) = bauerPoly n := by
  classical
  set T := (range n).filter (·.Coprime n) with hT
  have hcard : T.card = n.totient := by
    rw [hT, Nat.totient_eq_card_coprime]
    congr 1
    ext x; simp [Nat.coprime_comm]
  have hmem : ∀ t ∈ T, 1 ≤ t ∧ t < n ∧ t.Coprime n := by
    intro t ht
    simp only [hT, Finset.mem_filter, Finset.mem_range] at ht
    refine ⟨Nat.one_le_iff_ne_zero.2 ?_, ht.1, ht.2⟩
    rintro rfl
    have := ht.2
    rw [Nat.coprime_zero_left] at this
    omega
  have hT' : ∀ t, t ∈ T ↔ t < n ∧ t.Coprime n := fun t ↦ by simp [hT]
  rw [bauerPoly, Polynomial.prod_comp]
  have h1 : ∀ t ∈ T, (X - C (t : ℤ)).comp (C (n : ℤ) - X) = (-1) * (X - C (((n - t : ℕ) : ℤ))) := by
    intro t ht
    obtain ⟨-, h2, -⟩ := hmem t ht
    rw [sub_comp, X_comp, C_comp, Nat.cast_sub h2.le, C_sub]
    ring
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, Finset.prod_const, hcard,
    (Nat.totient_even hn).neg_one_pow, one_mul]
  refine Finset.prod_nbij' (fun t ↦ n - t) (fun t ↦ n - t) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    obtain ⟨h1, h2, h3⟩ := hmem t ht
    exact (hT' _).2 ⟨by omega, (Nat.coprime_self_sub_left h2.le).2 h3⟩
  · intro t ht
    obtain ⟨h1, h2, h3⟩ := hmem t ht
    exact (hT' _).2 ⟨by omega, (Nat.coprime_self_sub_left h2.le).2 h3⟩
  · intro t ht; obtain ⟨h1, h2, -⟩ := hmem t ht; omega
  · intro t ht; obtain ⟨h1, h2, -⟩ := hmem t ht; omega
  · intro t _; rfl

/-- The elementary symmetric functions `A_k` of the numbers of `t(p^a)`. -/
noncomputable def residueEsymm (n k : ℕ) : ℤ :=
  (((range n).filter (·.Coprime n)).val.map (Nat.cast : ℕ → ℤ)).esymm k

/-- **Theorem 130** [hardywright2008]: let `p` be an odd prime and `A_{2v+1}` the sum of the
products, `2v + 1` at a time, of the numbers of `t(p^a)`. If `2v` is not a multiple of `p - 1`,
then `A_{2v+1} ≡ 0 (mod p^{2a})`. -/
@[kb "hardywright2008" "Thm 130, p. 133"]
theorem prime_pow_two_mul_dvd_residueEsymm (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) {a v : ℕ}
    (ha : 1 ≤ a) (hv : ¬(p - 1) ∣ 2 * v) :
    (p : ℤ) ^ (2 * a) ∣ residueEsymm (p ^ a) (2 * v + 1) := by
  classical
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  set n := p ^ a with hn
  have hn2 : 2 < n := by
    calc 2 < p := by omega
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ a := Nat.pow_le_pow_right hp.out.pos ha
  set s := ((range n).filter (·.Coprime n)).val.map (Nat.cast : ℕ → ℤ) with hs
  have hcard : Multiset.card s = n.totient := by
    rw [hs, Multiset.card_map, Finset.card_val, Nat.totient_eq_card_coprime]
    congr 1
    ext x; simp [Nat.coprime_comm]
  have hφ : n.totient = p ^ (a - 1) * (p - 1) := Nat.totient_prime_pow hp.out (by omega)
  -- if `2v + 1 > φ(p^a)` there is nothing to prove
  rcases Nat.lt_or_ge n.totient (2 * v + 1) with hlt | hle
  · rw [residueEsymm, ← hs, Multiset.esymm, Multiset.powersetCard_eq_empty _ (by omega)]
    simp
  set f := bauerPoly n with hf
  set j := n.totient - (2 * v + 1) with hj
  -- `f(-x) = f(p^a + x)`
  have hsym : f.comp (-X) = f.comp (X + C (n : ℤ)) := by
    conv_lhs => rw [hf, ← bauerPoly_comp_sub hn2, comp_assoc]
    congr 1
    rw [sub_comp, C_comp, X_comp]; ring
  obtain ⟨K, hK⟩ := exists_comp_X_add_C f (n : ℤ)
  -- Theorem 126: `f = H + p^a G`
  obtain ⟨G, hG⟩ : C ((p ^ a : ℕ) : ℤ) ∣ f - (X ^ (p - 1) - 1) ^ (p ^ (a - 1)) := by
    rw [← map_eq_map_iff_C_dvd, hf, bauerPoly_prime_pow p hp2 ha]
    simp
  set H : ℤ[X] := (X ^ (p - 1) - 1) ^ (p ^ (a - 1)) with hH
  have hf' : derivative f = derivative H + C ((p ^ a : ℕ) : ℤ) * derivative G := by
    have : f = H + C ((p ^ a : ℕ) : ℤ) * G := by linear_combination hG
    rw [this, derivative_add, derivative_C_mul]
  have hmain : f.comp (-X) - f = C (n : ℤ) * derivative H +
      C ((p : ℤ) ^ (2 * a)) * (derivative G + K) := by
    rw [hsym, hK, hf', hn]
    have : (C ((p : ℤ) ^ (2 * a)) : ℤ[X]) = C ((p ^ a : ℕ) : ℤ) * C ((p ^ a : ℕ) : ℤ) := by
      rw [← C_mul]; push_cast; ring_nf
    rw [this]
    ring
  -- compare the coefficients of `x^j`, `j = φ - (2v + 1)`
  have hcoef := congrArg (coeff · j) hmain
  simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_comp_neg_X] at hcoef
  -- the coefficient of `x^j` in `f` is `-A_{2v+1}`
  have hfj : f.coeff j = -residueEsymm n (2 * v + 1) := by
    have := Multiset.prod_X_sub_C_coeff s (k := j) (by omega)
    rw [hcard, show n.totient - j = 2 * v + 1 by omega] at this
    have hprod : f = (s.map fun t ↦ X - C t).prod := by
      rw [hf, bauerPoly, Finset.prod_eq_multiset_prod, hs, Multiset.map_map]; rfl
    rw [hprod, this, residueEsymm, ← hs, pow_succ, pow_mul, neg_one_sq, one_pow]
    ring
  -- `j` is odd and the coefficient of `x^j` in `H'` vanishes
  have hjodd : Odd j := by
    have he : Even n.totient := Nat.totient_even hn2
    rw [hj]
    exact Nat.Even.sub_odd (by omega) he ⟨v, rfl⟩
  have hH' : (derivative H).coeff j = 0 := by
    set N := p ^ (a - 1)
    have hexp : ((X : ℤ[X]) ^ (p - 1) - 1) ^ (N - 1) = expand ℤ (p - 1) ((X - 1) ^ (N - 1)) := by
      rw [map_pow, map_sub, expand_X, map_one]
    have hder : derivative H = C ((N : ℤ) * ((p - 1 : ℕ) : ℤ)) *
        (X ^ (p - 2) * expand ℤ (p - 1) ((X - 1) ^ (N - 1))) := by
      rw [hH, derivative_pow, derivative_sub, derivative_X_pow, derivative_one, sub_zero, hexp,
        show p - 1 - 1 = p - 2 by omega, C_mul]
      ring
    rw [hder, coeff_C_mul, coeff_X_pow_mul', coeff_expand (by omega)]
    split_ifs with h1 h2
    · -- `(p - 1) ∣ j - (p - 2)` would give `(p - 1) ∣ 2v`
      exfalso
      apply hv
      have hφd : p - 1 ∣ n.totient := by rw [hφ]; exact dvd_mul_left _ _
      have hm : p - 1 ∣ (j - (p - 2)) + (p - 1) := dvd_add h2 dvd_rfl
      have e : j - (p - 2) + (p - 1) + 2 * v = n.totient := by omega
      exact (Nat.dvd_add_right hm).1 (e ▸ hφd)
    · rw [mul_zero]
    · rw [mul_zero]
  rw [hfj, hjodd.neg_one_pow, hH', mul_zero, zero_add] at hcoef
  -- `2 A_{2v+1} ≡ 0 (mod p^{2a})`
  have h2 : (p : ℤ) ^ (2 * a) ∣ 2 * residueEsymm n (2 * v + 1) :=
    ⟨(derivative G).coeff j + K.coeff j, by linear_combination hcoef⟩

  have hcop : IsCoprime ((p : ℤ) ^ (2 * a)) 2 := by
    refine IsCoprime.pow_left ?_
    rw [Int.isCoprime_iff_gcd_eq_one]
    have : Nat.Coprime p 2 := (Nat.coprime_primes hp.out Nat.prime_two).2 hp2
    exact_mod_cast this
  exact hcop.dvd_of_dvd_mul_left h2

end NTKB.HardyWright
