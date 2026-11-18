/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Attr
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Algebra.Order.Antidiag.Nat

/-!
# Hardy–Wright, § 17.4: formal products of Dirichlet series

Hardy and Wright multiply Dirichlet series formally (Section 17.4): the coefficient of `n^{-s}` in a
finite or infinite product is collected from the products of indices equal to `n`. Mathlib's ring
of arithmetic functions (`ArithmeticFunction R`, multiplication the Dirichlet convolution) is the
ring of formal Dirichlet series with this product.

* Theorem 285: for a multiplicative `f`, the formal Dirichlet series `∑ f(n) n^{-s}` is the formal
  product over the primes of the local series `1 + f(p) p^{-s} + f(p²) p^{-2s} + ⋯`. The infinite
  product is the limit of the finite products over the primes `p < N`: the finite product is `f`
  on the `N`-smooth numbers (`localFactor_prod_primesBelow`), so its coefficient of `n^{-s}` is
  `f(n)` as soon as `N > n` (`formal_euler_product`).
* The coefficient of `ζ(s)^k` (formal `k`-th power of `∑ n^{-s}`) is the number `d_k(n)` of
  ordered factorizations of `n` into `k` factors (`zeta_pow_apply`), used for Theorem 299.

Source text unavailable: the statements follow
the map's paraphrase of Theorem 285 and of the definition of `d_k(n)`.
-/

open Finset

namespace NTKB.HardyWright

namespace ArithmeticFunction

open _root_.ArithmeticFunction
open scoped _root_.ArithmeticFunction.zeta

variable {R : Type*} [CommSemiring R]

/-- The local factor at `p` of an arithmetic function `f`: the formal Dirichlet series
`1 + f(p) p^{-s} + f(p²) p^{-2s} + ⋯` (when `f 1 = 1`), as the arithmetic function equal to `f`
on the powers of `p` and to `0` elsewhere. -/
noncomputable def localFactor (f : ArithmeticFunction R) (p : ℕ) : ArithmeticFunction R :=
  ⟨fun n => by classical exact if ∃ i : ℕ, p ^ i = n then f n else 0, by simp⟩

theorem localFactor_apply (f : ArithmeticFunction R) (p n : ℕ) [Decidable (∃ i : ℕ, p ^ i = n)] :
    localFactor f p n = if ∃ i : ℕ, p ^ i = n then f n else 0 := by
  simp only [localFactor, coe_mk]
  congr 1

/-- A prime power times a number not divisible by the prime is `(p+1)`-smooth iff the cofactor
is `p`-smooth. -/
theorem mul_pow_mem_smoothNumbers_succ_iff {p e m : ℕ} (hp : p.Prime) (hm : ¬ p ∣ m) :
    p ^ e * m ∈ (p + 1).smoothNumbers ↔ m ∈ p.smoothNumbers := by
  rw [Nat.mem_smoothNumbers', Nat.mem_smoothNumbers']
  constructor
  · intro h q hq hqm
    have h1 := h q hq (Dvd.dvd.mul_left hqm _)
    have : q ≠ p := by rintro rfl; exact hm hqm
    omega
  · intro h q hq hqd
    rcases (Nat.Prime.dvd_mul hq).1 hqd with h2 | h2
    · have := (Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h2)
      omega
    · have := h q hq h2
      omega

open scoped Classical in
/-- One step of the finite Euler product: multiplying by the local factor at a prime `p`. -/
theorem mul_localFactor_apply {f g : ArithmeticFunction R} (hf : f.IsMultiplicative) {p : ℕ}
    (hp : p.Prime) (hg : ∀ m, g m = if m ∈ p.smoothNumbers then f m else 0)
    (n : ℕ) :
    (g * localFactor f p) n = if n ∈ (p + 1).smoothNumbers then f n else 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Nat.smoothNumbers]
  set e := n.factorization p with he
  set m := n / p ^ e with hmdef
  have hm : ¬ p ∣ m := Nat.not_dvd_ordCompl hp hn
  have hnm : n = p ^ e * m := (Nat.ordProj_mul_ordCompl_eq_self n p).symm
  have hm0 : m ≠ 0 := by rintro h; rw [h] at hnm; simp at hnm; exact hn hnm
  rw [ArithmeticFunction.mul_apply, Finset.sum_eq_single (m, p ^ e)]
  · have hex : ∃ i : ℕ, p ^ i = p ^ e := ⟨e, rfl⟩
    have hc : Nat.Coprime (p ^ e) m :=
      Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)
    have hfn : f n = f (p ^ e) * f m := by
      conv_lhs => rw [hnm]
      exact hf.map_mul_of_coprime hc
    have hiff := mul_pow_mem_smoothNumbers_succ_iff (e := e) hp hm
    rw [← hnm] at hiff
    show g m * localFactor f p (p ^ e) = _
    rw [hg, localFactor_apply]
    by_cases hms : m ∈ p.smoothNumbers
    · simp only [hex, hms, hiff.2 hms, ite_true, hfn, mul_comm]
    · simp only [hex, hms, show n ∉ (p + 1).smoothNumbers from fun h => hms (hiff.1 h),
        ite_true, ite_false, zero_mul]
  · rintro ⟨a, b⟩ hab hne
    rw [Nat.mem_divisorsAntidiagonal] at hab
    rw [localFactor_apply]
    by_cases hb : ∃ i : ℕ, p ^ i = b
    · obtain ⟨i, rfl⟩ := hb
      by_cases has : a ∈ p.smoothNumbers
      · exfalso
        have ha0 : a ≠ 0 := Nat.ne_zero_of_mem_smoothNumbers has
        have hpa : ¬ p ∣ a := fun h => by
          have := Nat.mem_smoothNumbers'.1 has p hp h
          omega
        have hfa : a.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpa
        have hie : i = e := by
          have := congrArg (fun x => x.factorization p) hab.1
          simp only [Nat.factorization_mul ha0 (pow_ne_zero i hp.ne_zero),
            Nat.Prime.factorization_pow hp] at this
          simp [hfa] at this
          omega
        subst hie
        apply hne
        have : a = m := by
          have h2 : a * p ^ e = m * p ^ e := by rw [hab.1, hnm, mul_comm]
          exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos e) h2
        rw [this]
      · rw [hg, ite_eq_right has, zero_mul]
    · rw [ite_eq_right hb, mul_zero]
  · intro h
    exfalso
    apply h
    rw [Nat.mem_divisorsAntidiagonal]
    exact ⟨by rw [mul_comm]; exact hnm.symm, hn⟩

open scoped Classical in
/-- `localFactor_prod_primesBelow` with the classical decidability instance. -/
theorem localFactor_prod_primesBelow_aux {f : ArithmeticFunction R} (hf : f.IsMultiplicative)
    (N n : ℕ) :
    (∏ p ∈ N.primesBelow, localFactor f p) n = if n ∈ N.smoothNumbers then f n else 0 := by
  induction N generalizing n with
  | zero =>
    simp only [Nat.primesBelow_zero, prod_empty, ArithmeticFunction.one_apply,
      Nat.smoothNumbers_zero, Set.mem_singleton_iff]
    by_cases h : n = 1 <;> simp [h, hf.map_one]
  | succ N ih =>
    rw [Nat.primesBelow_succ]
    by_cases hN : N.Prime
    · rw [ite_eq_left hN, prod_insert (Nat.notMem_primesBelow N), mul_comm]
      exact mul_localFactor_apply hf hN (fun m => ih m) n
    · rw [ite_eq_right hN]
      simpa only [Nat.smoothNumbers_succ hN] using ih n

/-- **Finite Euler products of formal Dirichlet series.** For a multiplicative `f`, the formal
product of the local factors of `f` at the primes `p < N` is `f` on the `N`-smooth numbers and `0`
elsewhere. -/
theorem localFactor_prod_primesBelow {f : ArithmeticFunction R} (hf : f.IsMultiplicative)
    (N n : ℕ) [Decidable (n ∈ N.smoothNumbers)] :
    (∏ p ∈ N.primesBelow, localFactor f p) n = if n ∈ N.smoothNumbers then f n else 0 := by
  classical
  convert localFactor_prod_primesBelow_aux hf N n

/-- **Theorem 285** (Hardy–Wright). For a multiplicative `f` (so `f(1) = 1`), the formal Dirichlet
series `∑ f(n) n^{-s}` is the formal product over all primes `p` of the local series
`1 + f(p) p^{-s} + f(p²) p^{-2s} + ⋯`: the coefficient of `n^{-s}` in the product over the primes
`p < N` equals `f(n)` for every `N > n`. -/
@[kb "hardywright2008" "Thm 285, p. 344"]
theorem formal_euler_product {f : ArithmeticFunction R} (hf : f.IsMultiplicative) {N n : ℕ}
    (hn : n < N) : (∏ p ∈ N.primesBelow, localFactor f p) n = f n := by
  rcases Nat.eq_zero_or_pos n with rfl | h0
  · simp
  · classical
    rw [localFactor_prod_primesBelow hf N n]
    simp [Nat.mem_smoothNumbers_of_lt h0 hn]

/-- Peeling off the last factor: `d_{k+1}(n) = ∑_{a ∣ n} d_k(a)`. -/
theorem card_finMulAntidiag_succ (k n : ℕ) (hn : n ≠ 0) :
    (Nat.finMulAntidiag (k + 1) n).card =
      ∑ a ∈ n.divisors, (Nat.finMulAntidiag k a).card := by
  rw [card_eq_sum_card_fiberwise (f := fun g : Fin (k + 1) → ℕ => ∏ i : Fin k, g i.castSucc)
    (t := n.divisors)]
  · refine sum_congr rfl fun a ha => ?_
    have ha' := Nat.mem_divisors.mp ha
    have ha0 : a ≠ 0 := ne_zero_of_dvd_ne_zero ha'.2 ha'.1
    refine card_nbij' (fun g => Fin.init g) (fun g => Fin.snoc g (n / a)) ?_ ?_ ?_ ?_
    · intro g hg
      simp only [mem_coe, mem_filter, Nat.mem_finMulAntidiag] at hg ⊢
      exact ⟨hg.2, ha0⟩
    · intro g hg
      simp only [mem_coe, mem_filter, Nat.mem_finMulAntidiag] at hg ⊢
      simp only [Fin.snoc_castSucc, Fin.prod_univ_castSucc, Fin.snoc_last]
      refine ⟨⟨?_, hn⟩, hg.1⟩
      rw [hg.1, Nat.mul_div_cancel' ha'.1]
    · intro g hg
      simp only [mem_coe, mem_filter, Nat.mem_finMulAntidiag] at hg
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.snoc_last]
        have h1 := hg.1.1
        rw [Fin.prod_univ_castSucc, hg.2] at h1
        rw [← h1]; simp [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero ha0)]
      · simp [Fin.init]
    · intro g hg
      funext i
      simp [Fin.init]
  · intro g hg
    simp only [mem_coe, Nat.mem_finMulAntidiag] at hg
    simp only [mem_coe, Nat.mem_divisors]
    refine ⟨?_, hn⟩
    rw [← hg.1, Fin.prod_univ_castSucc]
    exact dvd_mul_right _ _

/-- The coefficient of the formal `k`-th power of `ζ(s) = ∑ n^{-s}` at `n` is the number `d_k(n)`
of ordered factorizations `n = n₁ n₂ ⋯ n_k` into `k` factors (Hardy–Wright § 17.7, before
Theorem 299). -/
theorem zeta_pow_apply (k n : ℕ) :
    ((ζ : ArithmeticFunction ℕ) ^ k) n = (Nat.finMulAntidiag k n).card := by
  induction k generalizing n with
  | zero =>
    rw [pow_zero, _root_.ArithmeticFunction.one_apply]
    by_cases h : n = 1
    · subst h; simp [Nat.finMulAntidiag_one]
    · simp [h, Nat.finMulAntidiag_zero_left h]
  | succ k ih =>
    rcases eq_or_ne n 0 with rfl | hn
    · simp [Nat.finMulAntidiag_zero_right]
    rw [pow_succ, _root_.ArithmeticFunction.mul_apply, card_finMulAntidiag_succ k n hn,
      Nat.sum_divisorsAntidiagonal (fun a b => ((ζ : ArithmeticFunction ℕ) ^ k) a * ζ b)]
    refine sum_congr rfl fun a ha => ?_
    have ha' := Nat.mem_divisors.mp ha
    have : n / a ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) ha'.1)
      (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero ha'.2 ha'.1))).ne'
    rw [ih, zeta_apply_ne this, mul_one]


end ArithmeticFunction

end NTKB.HardyWright
