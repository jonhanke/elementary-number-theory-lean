/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Data.Nat.Squarefree
import NTKB.Attr

/-!
# Ireland–Rosen, Chapter 2: a second proof that there are infinitely many primes

The proof following Proposition 2.2.1 (pdf p. 29): if `p_1, …, p_l` were all the primes, every
`n ≤ N` would be `a b²` with `a` squarefree, hence a product of a subset of the `p_i` (`2^l`
choices), and `b ≤ √N`. So `N ≤ 2^l √N`, false for `N` large (we take `N = 4^(l+1)`).
Mathlib's theorem is `Nat.infinite_setOf_prime` (Euclid's proof); this file records the book's
second proof.
-/

namespace NTKB.IrelandRosen

/-- **Ireland–Rosen, Chapter 2, second proof of infinitely many primes** (after
Proposition 2.2.1): by counting `n ≤ N` written as `a b²` with `a` squarefree. -/
@[kb "irelandrosen1990" "Ch 2, Section 2, second proof of Theorem 1, p. 29"]
theorem infinite_setOf_prime_of_squarefree_count : {p : ℕ | p.Prime}.Infinite := by
  classical
  intro hfin
  set P := hfin.toFinset with hP
  -- choose `n = b^2 * a` with `a` squarefree (Proposition 2.2.1)
  choose b a hab hsq using (exists_sq_mul_squarefree : ∀ n : ℕ, _)
  -- the map `n ↦ (primes of a, b)`
  let φ : ℕ → Finset ℕ × ℕ := fun n ↦ ((a n).primeFactors, b n)
  have hmaps : ∀ n ∈ Finset.Icc 1 (4 ^ (P.card + 1)),
      φ n ∈ P.powerset ×ˢ Finset.Icc 1 (2 ^ (P.card + 1)) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    simp only [Finset.mem_product, Finset.mem_powerset, Finset.mem_Icc, φ]
    refine ⟨fun p hp ↦ ?_, ?_, ?_⟩
    · rw [hP, Set.Finite.mem_toFinset]; exact Nat.prime_of_mem_primeFactors hp
    · rcases Nat.eq_zero_or_pos (b n) with h0 | h0
      · have := hab n; rw [h0] at this; simp at this; omega
      · exact h0
    · have h1 : b n ^ 2 ≤ n := by
        have := hab n
        rcases Nat.eq_zero_or_pos (a n) with h0 | h0
        · rw [h0] at this; simp at this; omega
        · calc b n ^ 2 ≤ b n ^ 2 * a n := Nat.le_mul_of_pos_right _ h0
            _ = n := this
      have h2 : b n ^ 2 ≤ (2 ^ (P.card + 1)) ^ 2 := by
        calc b n ^ 2 ≤ n := h1
          _ ≤ 4 ^ (P.card + 1) := hn.2
          _ = (2 ^ (P.card + 1)) ^ 2 := by
            rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul, ← pow_mul, mul_comm]
      exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h2
  have hinj : Set.InjOn φ (Finset.Icc 1 (4 ^ (P.card + 1)) : Set ℕ) := by
    intro m _ n _ hmn
    simp only [φ, Prod.mk.injEq] at hmn
    rw [← hab m, ← hab n, ← Nat.prod_primeFactors_of_squarefree (hsq m),
      ← Nat.prod_primeFactors_of_squarefree (hsq n), hmn.1, hmn.2]
  have hcard := Finset.card_le_card_of_injOn φ hmaps hinj
  rw [Nat.card_Icc, Finset.card_product, Finset.card_powerset, Nat.card_Icc] at hcard
  simp only [Nat.add_sub_cancel] at hcard
  -- `4^(l+1) ≤ 2^l * 2^(l+1)` is false
  have : 2 ^ P.card * 2 ^ (P.card + 1) < 4 ^ (P.card + 1) := by
    rw [← pow_add, show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

end NTKB.IrelandRosen
