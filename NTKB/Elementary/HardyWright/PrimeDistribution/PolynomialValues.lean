/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.PrimeDistribution.Elementary
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.NumberTheory.FermatPsp
import Mathlib.RingTheory.Int.Basic

/-!
# Polynomial-exponential values are composite infinitely often

`[hardywright2008, Theorem 22]`: if `f(n) = P(n, 1ⁿ, 2ⁿ, …, kⁿ)` for an integral polynomial `P`
and `f(n) → ∞`, then `f(n)` is composite for infinitely many `n`.
-/

open Filter

namespace NTKB.HardyWright

private theorem eval_modEq {σ : Type*} (P : MvPolynomial σ ℤ) (p : ℤ) (x y : σ → ℤ)
    (h : ∀ i, x i ≡ y i [ZMOD p]) :
    MvPolynomial.eval x P ≡ MvPolynomial.eval y P [ZMOD p] := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [Int.ModEq.refl]
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp => simpa using hp.mul (h i)

/-- **Theorem 22.** If `f(n) = P(n, 1^n, 2^n, ..., k^n)` for a polynomial `P` with integer
coefficients and `f(n) → ∞`, then `f(n)` is composite for infinitely many `n`. -/
@[kb "hardywright2008" "Thm 22, p. 41"]
theorem infinite_not_prime_polynomial_exp {k : ℕ} (P : MvPolynomial (Fin (k + 1)) ℤ)
    (hP : Tendsto (fun n : ℕ ↦ MvPolynomial.eval
      (fun i : Fin (k + 1) ↦ if i = 0 then (n : ℤ) else (i : ℤ) ^ n) P) atTop atTop) :
    Set.Infinite {n : ℕ | ¬ Prime (MvPolynomial.eval
      (fun i : Fin (k + 1) ↦ if i = 0 then (n : ℤ) else (i : ℤ) ^ n) P)} := by
  set f : ℕ → ℤ := fun n ↦ MvPolynomial.eval
      (fun i : Fin (k + 1) ↦ if i = 0 then (n : ℤ) else (i : ℤ) ^ n) P with hf
  intro hfin
  obtain ⟨N, hN⟩ := hfin.bddAbove
  have hprime : ∀ n, N < n → Prime (f n) := by
    intro n hn
    by_contra h
    exact absurd (hN h) (by omega)
  obtain ⟨n, hn⟩ := ((hP.eventually_gt_atTop (k : ℤ)).and (eventually_gt_atTop N)).exists
  obtain ⟨hnk, hnN⟩ := hn
  have hpr := hprime n hnN
  set p : ℕ := (f n).natAbs with hp
  have hpp : Nat.Prime p := Int.prime_iff_natAbs_prime.mp hpr
  have hpk : k < p := by omega
  have hfp : f n = p := by omega
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hpp
  obtain ⟨M, hM⟩ := (hP.eventually_gt_atTop (p : ℤ)).exists_forall_of_atTop
  set m : ℕ := n + (M + N + 1) * (p * (p - 1)) with hm
  have hp2 := hpp.two_le
  have h1le : 1 ≤ p * (p - 1) := Nat.mul_pos (by omega) (by omega)
  have hmM : M ≤ m := by
    nlinarith [Nat.zero_le (M + N + 1), Nat.zero_le n]
  have hmN : N < m := by
    nlinarith [Nat.zero_le (M + N + 1), Nat.zero_le n]
  have hcong : f m ≡ f n [ZMOD p] := by
    apply eval_modEq
    intro i
    by_cases hi : i = 0
    · simp only [hi, ite_true]
      rw [hm]; push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
      refine Int.ModEq.symm (Int.modEq_iff_dvd.mpr ?_)
      exact ⟨((M : ℤ) + N + 1) * ((p : ℤ) - 1), by ring⟩
    · simp only [hi, ite_false]
      have hi1 : 1 ≤ (i : ℕ) := Nat.one_le_iff_ne_zero.mpr (fun h => hi (Fin.ext h))
      have hik : (i : ℕ) ≤ k := Nat.lt_succ_iff.mp i.2
      have hcop : IsCoprime ((i : ℕ) : ℤ) (p : ℤ) := by
        rw [Int.isCoprime_iff_gcd_eq_one]
        have : Nat.Coprime (i : ℕ) p :=
          (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hpp).mpr
            (fun h => by have := Nat.le_of_dvd (by omega) h; omega)))
        simpa using this
      have h1 := Int.ModEq.pow_card_sub_one_eq_one hpp hcop
      have h2 : ((i : ℕ) : ℤ) ^ m = ((i : ℕ) : ℤ) ^ n *
          (((i : ℕ) : ℤ) ^ (p - 1)) ^ ((M + N + 1) * p) := by
        rw [← pow_mul, ← pow_add]; congr 1; rw [hm]; ring
      show ((i : ℕ) : ℤ) ^ m ≡ ((i : ℕ) : ℤ) ^ n [ZMOD p]
      rw [h2]
      have h4 := (h1.pow ((M + N + 1) * p)).mul_left (((i : ℕ) : ℤ) ^ n)
      simpa using h4
  have hdvd : (p : ℤ) ∣ f m := by
    have h0 : f n ≡ 0 [ZMOD p] := by
      rw [hfp]; exact Int.modEq_zero_iff_dvd.mpr dvd_rfl
    exact Int.modEq_zero_iff_dvd.mp (hcong.trans h0)
  have hassoc := hpZ.associated_of_dvd (hprime m hmN) hdvd
  have hgt := hM m hmM
  rcases Int.associated_iff.mp hassoc with h | h <;> omega

end NTKB.HardyWright
