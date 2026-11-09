/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.ArithmeticFunctions.Delta
import NTKB.Elementary.HardyWright.ArithmeticFunctions.Order
import NTKB.Attr
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Mathlib.NumberTheory.ArithmeticFunction.Liouville
import Mathlib.Algebra.Order.Star.Int

/-!
# Hardy–Wright, § 17.8: Dirichlet series identities

All for `s > 1` in the book; here for complex `s` with `Re s > 1`.

* Theorem 300: `ζ(2s)/ζ(s) = ∑ λ(n) n^{-s}` (`λ` the Liouville function).
* Theorem 303: `ζ(s)/ζ(ks) = ∑ q_k(n) n^{-s}` (`q_k` the indicator of the `k`-th-power-free numbers).
* Theorem 304 (Ramanujan): `ζ(s)⁴/ζ(2s) = ∑ d(n)² n^{-s}`.

The book proves these by comparing the Euler factors (Theorems 280, 286). Here each is reduced to
an identity of Dirichlet convolutions of multiplicative functions, checked on prime powers (the
Euler factors), and Mathlib's product theorem for `L`-series (Theorem 284, `LSeries_mul'`). The
`L`-series of the indicator of the `k`-th powers is `ζ(ks)` (`LSeries_powIndicator`).
-/

open Finset ArithmeticFunction Complex
open scoped ArithmeticFunction.zeta ArithmeticFunction.sigma

namespace NTKB.HardyWright

/-- `n ≠ 0` is a `k`-th power iff every exponent in its factorization is divisible by `k`. -/
lemma exists_pow_eq_iff_dvd_factorization {n k : ℕ} (hn : n ≠ 0) :
    (∃ m, m ^ k = n) ↔ ∀ p ∈ n.primeFactors, k ∣ n.factorization p := by
  constructor
  · rintro ⟨m, rfl⟩ p _
    rw [Nat.factorization_pow]
    exact dvd_mul_right k _
  · intro h
    refine ⟨n.factorization.prod fun a b => a ^ (b / k), ?_⟩
    rw [← powMonoidHom_apply, map_finsuppProd]
    nth_rw 2 [← Nat.prod_factorization_pow_eq_self hn]
    refine Finsupp.prod_congr fun p hp => ?_
    rw [powMonoidHom_apply, ← pow_mul, Nat.div_mul_cancel (h p (by simpa using hp))]

/-- `(f * g)(p^a) = ∑_{i ≤ a} f(p^i) g(p^{a-i})`. -/
lemma mul_apply_prime_pow {R : Type*} [Semiring R] (f g : ArithmeticFunction R) {p : ℕ}
    (hp : p.Prime) (a : ℕ) :
    (f * g) (p ^ a) = ∑ i ∈ range (a + 1), f (p ^ i) * g (p ^ (a - i)) := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun x y => f x * g y), Nat.sum_divisors_prime_pow hp]
  refine sum_congr rfl fun i hi => ?_
  rw [Nat.pow_div (by simpa [Nat.lt_succ_iff] using hi) hp.pos]

/-- The indicator of the `k`-th powers `1, 2^k, 3^k, …`. -/
noncomputable def powIndicator (k : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n ≠ 0 ∧ ∀ p ∈ n.primeFactors, k ∣ n.factorization p then 1 else 0, by simp⟩

lemma powIndicator_apply (k n : ℕ) : powIndicator k n =
    if n ≠ 0 ∧ ∀ p ∈ n.primeFactors, k ∣ n.factorization p then 1 else 0 := rfl

lemma powIndicator_apply_eq_one_iff {k n : ℕ} :
    powIndicator k n = 1 ↔ n ≠ 0 ∧ ∃ m, m ^ k = n := by
  rw [powIndicator_apply]
  split_ifs with h
  · simp only [true_iff]
    exact ⟨h.1, (exists_pow_eq_iff_dvd_factorization h.1).mpr h.2⟩
  · simp only [zero_ne_one, false_iff, not_and]
    intro hn hm
    exact h ⟨hn, (exists_pow_eq_iff_dvd_factorization hn).mp hm⟩

lemma powIndicator_apply_pow {k : ℕ} {m : ℕ} (hm : m ≠ 0) :
    powIndicator k (m ^ k) = 1 :=
  powIndicator_apply_eq_one_iff.mpr ⟨pow_ne_zero _ hm, m, rfl⟩

lemma not_dvd_of_coprime_of_mem {m n p : ℕ} (hmn : m.Coprime n) (hp : p ∈ m.primeFactors) :
    ¬ p ∣ n :=
  (Nat.Prime.coprime_iff_not_dvd (Nat.prime_of_mem_primeFactors hp)).mp
    (Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hp) hmn)

lemma isMultiplicative_powIndicator (k : ℕ) : (powIndicator k).IsMultiplicative := by
  refine ⟨by simp [powIndicator_apply], fun {m n} hmn => ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp [powIndicator_apply]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [powIndicator_apply]
  have hmn0 : m * n ≠ 0 := mul_ne_zero hm hn
  have key : (∀ p ∈ (m * n).primeFactors, k ∣ (m * n).factorization p) ↔
      (∀ p ∈ m.primeFactors, k ∣ m.factorization p) ∧
        (∀ p ∈ n.primeFactors, k ∣ n.factorization p) := by
    rw [Nat.primeFactors_mul hm hn]
    constructor
    · intro h
      refine ⟨fun p hp => ?_, fun p hp => ?_⟩
      · have := h p (mem_union_left _ hp)
        rwa [Nat.factorization_mul_apply_of_coprime hmn,
          Nat.factorization_eq_zero_of_not_dvd (not_dvd_of_coprime_of_mem hmn hp),
          add_zero] at this
      · have := h p (mem_union_right _ hp)
        rwa [Nat.factorization_mul_apply_of_coprime hmn,
          Nat.factorization_eq_zero_of_not_dvd (not_dvd_of_coprime_of_mem hmn.symm hp),
          zero_add] at this
    · rintro ⟨h1, h2⟩ p hp
      rw [Nat.factorization_mul_apply_of_coprime hmn]
      rcases mem_union.mp hp with hp | hp
      · rw [Nat.factorization_eq_zero_of_not_dvd (not_dvd_of_coprime_of_mem hmn hp), add_zero]
        exact h1 p hp
      · rw [Nat.factorization_eq_zero_of_not_dvd (not_dvd_of_coprime_of_mem hmn.symm hp), zero_add]
        exact h2 p hp
  rw [powIndicator_apply, powIndicator_apply, powIndicator_apply]
  simp only [ne_eq, hmn0, hm, hn, not_false_eq_true, true_and]
  simp only [key]
  by_cases hA : ∀ p ∈ m.primeFactors, k ∣ m.factorization p <;>
  by_cases hB : ∀ p ∈ n.primeFactors, k ∣ n.factorization p
  · simp only [eq_true hA, eq_true hB, and_self, ↓reduceIte, mul_one]
  · simp only [eq_true hA, eq_false hB, and_false, ↓reduceIte, mul_zero]
  · simp only [eq_false hA, eq_true hB, and_true, ↓reduceIte, zero_mul]
  · simp only [eq_false hA, eq_false hB, and_false, ↓reduceIte, mul_zero]

lemma powIndicator_prime_pow {k : ℕ} {p : ℕ} (hp : p.Prime) (a : ℕ) :
    powIndicator k (p ^ a) = if k ∣ a then 1 else 0 := by
  rw [powIndicator_apply]
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  rw [Nat.primeFactors_prime_pow ha.ne' hp, hp.factorization_pow]
  simp [hp.ne_zero]

/-- `∑ (m^k)^{-s} = ζ(ks)`: the `L`-series of the indicator of the `k`-th powers. -/
theorem LSeries_powIndicator {k : ℕ} (hk : k ≠ 0) {s : ℂ} (hs : 1 < ((k : ℂ) * s).re) :
    LSeries (fun n => powIndicator k n) s = riemannZeta ((k : ℂ) * s) := by
  rw [← LSeries_one_eq_riemannZeta hs, LSeries, LSeries]
  rw [← (Nat.pow_left_injective hk).tsum_eq (f := LSeries.term (fun n => powIndicator k n) s)]
  · refine tsum_congr fun m => ?_
    rcases eq_or_ne m 0 with rfl | hm
    · simp [LSeries.term, hk]
    rw [LSeries.term_of_ne_zero (pow_ne_zero _ hm), LSeries.term_of_ne_zero hm,
      powIndicator_apply_pow hm, Pi.one_apply, Nat.cast_pow, ← natCast_cpow_natCast_mul]
  · intro n hn
    rw [Function.mem_support] at hn
    have hn0 : n ≠ 0 := by rintro rfl; simp at hn
    rw [LSeries.term_of_ne_zero hn0] at hn
    have : powIndicator k n ≠ 0 := fun h => hn (by rw [h, zero_div])
    rw [powIndicator_apply] at this
    split_ifs at this with h
    · obtain ⟨m, hm⟩ := (exists_pow_eq_iff_dvd_factorization h.1).mpr h.2
      exact ⟨m, hm⟩
    · exact absurd rfl this

lemma LSeriesSummable_of_abs_le_one {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable f s :=
  LSeriesSummable_of_le_const_mul_rpow (x := 1) hs ⟨1, fun n _ => by simpa using hf n⟩

lemma norm_powIndicator_le (k n : ℕ) : ‖powIndicator k n‖ ≤ 1 := by
  rw [powIndicator_apply]; split_ifs <;> simp

/-- The Liouville function as a complex arithmetic function. -/
noncomputable def liouvilleC : ArithmeticFunction ℂ := ⟨fun n => (liouville n : ℂ), by simp⟩

lemma liouvilleC_apply (n : ℕ) : liouvilleC n = (liouville n : ℂ) := rfl

lemma isMultiplicative_liouvilleC : liouvilleC.IsMultiplicative :=
  ⟨by simp [liouvilleC_apply, liouville_apply_one], fun {m n} _ => by
    simp [liouvilleC_apply, liouville_apply_mul]⟩

lemma liouvilleC_prime_pow {p : ℕ} (hp : p.Prime) (i : ℕ) : liouvilleC (p ^ i) = (-1) ^ i := by
  rw [liouvilleC_apply, liouville_apply (pow_ne_zero _ hp.ne_zero),
    cardFactors_apply_prime_pow hp]
  push_cast; rfl

/-- `∑_{d ∣ n} λ(d) = 1` if `n` is a square and `0` otherwise. -/
lemma liouvilleC_mul_zeta : liouvilleC * (ζ : ArithmeticFunction ℂ) = powIndicator 2 := by
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _
    (isMultiplicative_liouvilleC.mul isMultiplicative_zeta.natCast) _
    (isMultiplicative_powIndicator 2)).mpr fun p a hp => ?_
  rw [mul_apply_prime_pow _ _ hp, powIndicator_prime_pow hp]
  simp only [liouvilleC_prime_pow hp, natCoe_apply, zeta_apply, pow_ne_zero _ hp.ne_zero,
    ↓reduceIte, Nat.cast_one, mul_one]
  have h := congrArg (fun z : ℤ => (z : ℂ)) (sum_range_neg_one_pow a)
  push_cast at h
  rw [h]
  simp [even_iff_two_dvd]

lemma norm_liouvilleC_le (n : ℕ) : ‖liouvilleC n‖ ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [liouvilleC_apply, liouville_apply hn]
  simp

lemma LSeries_zetaC {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (ζ : ArithmeticFunction ℂ) n) s = riemannZeta s := by
  simp only [natCoe_apply]
  exact LSeries_zeta_eq_riemannZeta hs

lemma LSeriesSummable_zetaC {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (ζ : ArithmeticFunction ℂ) n) s := by
  simp only [natCoe_apply]
  exact LSeriesSummable_zeta_iff.mpr hs

/-- **Theorem 300** (Hardy–Wright). For `s > 1` (here complex `s`, `Re s > 1`),
`ζ(2s)/ζ(s) = ∑ λ(n) n^{-s}`, `λ(n) = (-1)^{Ω(n)}` the Liouville function. Proof: the Euler factors
of both sides agree; equivalently `∑_{d ∣ n} λ(d)` is the indicator of the squares. -/
@[kb "hardywright2008" "Thm 300, p. 354"]
theorem LSeries_liouville {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (liouville n : ℂ)) s = riemannZeta (2 * s) / riemannZeta s := by
  have h2s : 1 < ((2 : ℕ) * s).re := by simp; linarith
  have hmul := LSeries_mul' (f := liouvilleC) (g := (ζ : ArithmeticFunction ℂ))
    (LSeriesSummable_of_abs_le_one norm_liouvilleC_le hs) (LSeriesSummable_zetaC hs)
  rw [liouvilleC_mul_zeta, LSeries_powIndicator two_ne_zero h2s, LSeries_zetaC hs] at hmul
  rw [eq_div_iff (riemannZeta_ne_zero_of_one_lt_re hs)]
  push_cast at hmul
  exact hmul.symm

/-- `q_k(n)`: `1` if `n` has no `k`-th power factor other than `1`, else `0` (Hardy–Wright § 17.8;
for `k = 2` the indicator `|μ(n)|` of the squarefree numbers). -/
noncomputable def powerFreeIndicator (k : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun n => by classical exact if n ≠ 0 ∧ ∀ m : ℕ, m ^ k ∣ n → m = 1 then 1 else 0, by simp⟩

lemma powerFree_iff {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0) :
    (∀ m : ℕ, m ^ k ∣ n → m = 1) ↔ ∀ p ∈ n.primeFactors, n.factorization p < k := by
  constructor
  · intro h p hp
    by_contra hlt
    have hpp := Nat.prime_of_mem_primeFactors hp
    have : p ^ k ∣ n := (hpp.pow_dvd_iff_le_factorization hn).mpr (not_lt.mp hlt)
    exact hpp.one_lt.ne' (h p this)
  · intro h m hm
    by_contra hm1
    have hm0 : m ≠ 0 := by rintro rfl; simp [zero_pow hk] at hm; exact hn hm
    obtain ⟨p, hpp, hpm⟩ := Nat.exists_prime_and_dvd hm1
    have hpk : p ^ k ∣ n := (pow_dvd_pow_of_dvd hpm k).trans hm
    have := (hpp.pow_dvd_iff_le_factorization hn).mp hpk
    exact absurd (h p (Nat.mem_primeFactors.mpr ⟨hpp, (dvd_pow_self p hk).trans hpk, hn⟩)) (not_lt.mpr this)

open Classical in
lemma powerFreeIndicator_apply {k n : ℕ} : powerFreeIndicator k n =
    if n ≠ 0 ∧ ∀ m : ℕ, m ^ k ∣ n → m = 1 then 1 else 0 := by
  simp only [powerFreeIndicator, coe_mk]

lemma powerFreeIndicator_apply' {k : ℕ} (hk : k ≠ 0) (n : ℕ) : powerFreeIndicator k n =
    if n ≠ 0 ∧ ∀ p ∈ n.primeFactors, n.factorization p < k then 1 else 0 := by
  rw [powerFreeIndicator_apply]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp only [ne_eq, hn, not_false_eq_true, true_and, powerFree_iff hn hk]

/-- For coprime nonzero `m, n`, a condition on all exponents of `mn` splits. -/
lemma forall_primeFactors_mul_iff (P : ℕ → Prop) {m n : ℕ} (hmn : m.Coprime n) (hm : m ≠ 0)
    (hn : n ≠ 0) :
    (∀ p ∈ (m * n).primeFactors, P ((m * n).factorization p)) ↔
      (∀ p ∈ m.primeFactors, P (m.factorization p)) ∧
        (∀ p ∈ n.primeFactors, P (n.factorization p)) := by
  rw [Nat.primeFactors_mul hm hn]
  have e1 : ∀ p ∈ m.primeFactors, (m * n).factorization p = m.factorization p := fun p hp => by
    rw [Nat.factorization_mul_apply_of_coprime hmn,
      Nat.factorization_eq_zero_of_not_dvd (not_dvd_of_coprime_of_mem hmn hp), add_zero]
  have e2 : ∀ p ∈ n.primeFactors, (m * n).factorization p = n.factorization p := fun p hp => by
    rw [Nat.factorization_mul_apply_of_coprime hmn,
      Nat.factorization_eq_zero_of_not_dvd (not_dvd_of_coprime_of_mem hmn.symm hp), zero_add]
  constructor
  · intro h
    exact ⟨fun p hp => e1 p hp ▸ h p (mem_union_left _ hp),
      fun p hp => e2 p hp ▸ h p (mem_union_right _ hp)⟩
  · rintro ⟨h1, h2⟩ p hp
    rcases mem_union.mp hp with hp | hp
    · exact (e1 p hp).symm ▸ h1 p hp
    · exact (e2 p hp).symm ▸ h2 p hp

lemma isMultiplicative_powerFreeIndicator {k : ℕ} (hk : k ≠ 0) :
    (powerFreeIndicator k).IsMultiplicative := by
  refine ⟨by simp [powerFreeIndicator_apply' hk], fun {m n} hmn => ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp [powerFreeIndicator_apply' hk]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [powerFreeIndicator_apply' hk]
  rw [powerFreeIndicator_apply' hk, powerFreeIndicator_apply' hk, powerFreeIndicator_apply' hk]
  simp only [ne_eq, mul_ne_zero hm hn, hm, hn, not_false_eq_true, true_and]
  simp only [forall_primeFactors_mul_iff (· < k) hmn hm hn]
  by_cases hA : ∀ p ∈ m.primeFactors, m.factorization p < k <;>
  by_cases hB : ∀ p ∈ n.primeFactors, n.factorization p < k
  · simp only [eq_true hA, eq_true hB, and_self, ↓reduceIte, mul_one]
  · simp only [eq_true hA, eq_false hB, and_false, ↓reduceIte, mul_zero]
  · simp only [eq_false hA, eq_true hB, and_true, ↓reduceIte, zero_mul]
  · simp only [eq_false hA, eq_false hB, and_false, ↓reduceIte, mul_zero]

lemma powerFreeIndicator_prime_pow {k : ℕ} (hk : k ≠ 0) {p : ℕ} (hp : p.Prime) (a : ℕ) :
    powerFreeIndicator k (p ^ a) = if a < k then 1 else 0 := by
  rw [powerFreeIndicator_apply' hk]
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [Nat.pos_of_ne_zero hk]
  rw [Nat.primeFactors_prime_pow ha.ne' hp, hp.factorization_pow]
  simp [hp.ne_zero]

lemma norm_powerFreeIndicator_le (k n : ℕ) : ‖powerFreeIndicator k n‖ ≤ 1 := by
  rw [powerFreeIndicator_apply]
  split_ifs <;> simp

/-- `∑_{d^k ∣ n} q_k(n/d^k) = 1`. -/
lemma powerFreeIndicator_mul_powIndicator {k : ℕ} (hk : k ≠ 0) :
    powerFreeIndicator k * powIndicator k = (ζ : ArithmeticFunction ℂ) := by
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _
    ((isMultiplicative_powerFreeIndicator hk).mul (isMultiplicative_powIndicator k)) _
    isMultiplicative_zeta.natCast).mpr fun p a hp => ?_
  rw [mul_apply_prime_pow _ _ hp]
  simp only [powerFreeIndicator_prime_pow hk hp, powIndicator_prime_pow hp, natCoe_apply,
    zeta_apply, pow_ne_zero _ hp.ne_zero, ↓reduceIte, Nat.cast_one, ite_mul, one_mul, zero_mul]
  have : (range (a + 1)).filter (fun i => i < k ∧ k ∣ a - i) = {a % k} := by
    ext i
    simp only [mem_filter, mem_range, mem_singleton]
    constructor
    · rintro ⟨h1, h2, h3⟩
      have hmod : i ≡ a [MOD k] := (Nat.modEq_iff_dvd' (by omega)).mpr h3
      rw [← Nat.mod_eq_of_lt h2]
      exact hmod
    · rintro rfl
      refine ⟨by have := Nat.mod_le a k; omega, Nat.mod_lt a (Nat.pos_of_ne_zero hk), ?_⟩
      exact (Nat.modEq_iff_dvd' (Nat.mod_le a k)).mp (Nat.mod_modEq a k)
  have h2 : ∀ x, (if x < k then if k ∣ a - x then (1 : ℂ) else 0 else 0) =
      if (x < k ∧ k ∣ a - x) then 1 else 0 := fun x => by
    by_cases h1 : x < k <;> by_cases h3 : k ∣ a - x <;> simp [h1, h3]
  rw [sum_congr rfl fun x _ => h2 x, ← sum_filter, this, sum_singleton]

/-- **Theorem 303** (Hardy–Wright). For `k ≥ 1` and `s > 1` (here complex `s`, `Re s > 1`),
`ζ(s)/ζ(ks) = ∑ q_k(n) n^{-s}`, `q_k(n) = 1` if `n` has no `k`-th power factor (other than `1`)
and `0` otherwise. -/
@[kb "hardywright2008" "Thm 303, p. 355"]
theorem LSeries_powerFreeIndicator {k : ℕ} (hk : k ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => powerFreeIndicator k n) s = riemannZeta s / riemannZeta (k * s) := by
  have hks : 1 < ((k : ℂ) * s).re := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    simp only [mul_re, natCast_re, natCast_im, zero_mul, sub_zero]
    nlinarith
  have hmul := LSeries_mul' (f := powerFreeIndicator k) (g := powIndicator k)
    (LSeriesSummable_of_abs_le_one (norm_powerFreeIndicator_le k) hs)
    (LSeriesSummable_of_abs_le_one (norm_powIndicator_le k) hs)
  rw [powerFreeIndicator_mul_powIndicator hk, LSeries_zetaC hs, LSeries_powIndicator hk hks] at hmul
  rw [eq_div_iff (riemannZeta_ne_zero_of_one_lt_re hks)]
  exact hmul.symm

/-- `d(n)²` as a complex arithmetic function. -/
noncomputable def divisorCountSq : ArithmeticFunction ℂ := ⟨fun n => (σ 0 n : ℂ) ^ 2, by simp⟩

lemma divisorCountSq_apply (n : ℕ) : divisorCountSq n = (σ 0 n : ℂ) ^ 2 := rfl

lemma isMultiplicative_divisorCountSq : divisorCountSq.IsMultiplicative :=
  ⟨by simp [divisorCountSq_apply], fun {m n} h => by
    simp [divisorCountSq_apply, isMultiplicative_sigma.map_mul_of_coprime h, mul_pow]⟩

/-- `6 ∑_{i ≤ a, a - i even} (i+1)² = (a+1)(a+2)(a+3)`. -/
lemma six_mul_sum_sq_parity (a : ℕ) :
    6 * ∑ i ∈ range (a + 1), (if 2 ∣ a - i then (i + 1) ^ 2 else 0) = (a + 1) * (a + 2) * (a + 3) := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    rcases a with _ | _ | a
    · simp
    · simp [sum_range_succ]
    · have h := ih a (by omega)
      rw [sum_range_succ, sum_range_succ]
      have e : ∑ i ∈ range (a + 1), (if 2 ∣ a + 1 + 1 - i then (i + 1) ^ 2 else 0) =
          ∑ i ∈ range (a + 1), (if 2 ∣ a - i then (i + 1) ^ 2 else 0) := by
        refine sum_congr rfl fun i hi => ?_
        have hi' : i ≤ a := Nat.lt_succ_iff.mp (mem_range.mp hi)
        simp only [show a + 1 + 1 - i = a - i + 2 by omega, Nat.dvd_add_self_right]
      rw [e, show a + 1 + 1 - (a + 1) = 1 by omega, show a + 1 + 1 - (a + 1 + 1) = 0 by omega]
      simp only [Nat.dvd_one, OfNat.ofNat_ne_one, ↓reduceIte, add_zero, dvd_zero]
      nlinarith [h]

lemma two_mul_sum_range_add_one (a : ℕ) :
    2 * ∑ i ∈ range (a + 1), (i + 1) = (a + 1) * (a + 2) := by
  induction a with
  | zero => simp
  | succ b ihb => rw [sum_range_succ, mul_add, ihb]; ring

/-- `6 ∑_{i ≤ a} (i+1)(a-i+1) = (a+1)(a+2)(a+3)`. -/
lemma six_mul_sum_mul (a : ℕ) :
    6 * ∑ i ∈ range (a + 1), (i + 1) * (a - i + 1) = (a + 1) * (a + 2) * (a + 3) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [sum_range_succ]
    have e : ∑ i ∈ range (a + 1), (i + 1) * (a + 1 - i + 1) =
        ∑ i ∈ range (a + 1), (i + 1) * (a - i + 1) + ∑ i ∈ range (a + 1), (i + 1) := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun i hi => ?_
      have hi' : i ≤ a := Nat.lt_succ_iff.mp (mem_range.mp hi)
      rw [show a + 1 - i + 1 = (a - i + 1) + 1 by omega]
      ring
    have hg := two_mul_sum_range_add_one a
    rw [e, show a + 1 - (a + 1) + 1 = 1 by omega]
    nlinarith [ih, hg]

/-- `∑_{d² ∣ n} d(n/d²)² = (d * d)(n)`, the coefficient of `ζ(s)⁴`. -/
lemma divisorCountSq_mul_powIndicator :
    divisorCountSq * powIndicator 2 =
      (σ 0 : ArithmeticFunction ℂ) * (σ 0 : ArithmeticFunction ℂ) := by
  have hσ : ((σ 0 : ArithmeticFunction ℕ) : ArithmeticFunction ℂ).IsMultiplicative :=
    isMultiplicative_sigma.natCast
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _
    (isMultiplicative_divisorCountSq.mul (isMultiplicative_powIndicator 2)) _
    (hσ.mul hσ)).mpr fun p a hp => ?_
  rw [mul_apply_prime_pow _ _ hp, mul_apply_prime_pow _ _ hp]
  simp only [divisorCountSq_apply, powIndicator_prime_pow hp, natCoe_apply,
    sigma_zero_apply_prime_pow hp, mul_ite, mul_one, mul_zero]
  have h1 := six_mul_sum_sq_parity a
  have h2 := six_mul_sum_mul a
  have : ∑ i ∈ range (a + 1), (if 2 ∣ a - i then (i + 1) ^ 2 else 0) =
      ∑ i ∈ range (a + 1), (i + 1) * (a - i + 1) := by omega
  exact_mod_cast this

/-- **Theorem 304** (Ramanujan; Hardy–Wright). For `s > 1` (here complex `s`, `Re s > 1`),
`ζ(s)⁴/ζ(2s) = ∑ d(n)² n^{-s}`. -/
@[kb "hardywright2008" "Thm 304, p. 355"]
theorem LSeries_card_divisors_sq {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (σ 0 n : ℂ) ^ 2) s = riemannZeta s ^ 4 / riemannZeta (2 * s) := by
  have h2s : 1 < ((2 : ℕ) * s).re := by simp; linarith
  -- `∑ d(n) n^{-s} = ζ(s)²`
  have hσ0 : (σ 0 : ArithmeticFunction ℂ) = (ζ : ArithmeticFunction ℂ) * ζ := by
    rw [← natCoe_mul, ← zeta_mul_pow_eq_sigma, pow_zero_eq_zeta]
  have hζ := LSeriesSummable_zetaC hs
  have hσsum : LSeriesSummable (fun n => (σ 0 : ArithmeticFunction ℂ) n) s := by
    rw [hσ0]; exact LSeriesSummable_mul hζ hζ
  have hLσ : LSeries (fun n => (σ 0 : ArithmeticFunction ℂ) n) s = riemannZeta s ^ 2 := by
    rw [hσ0, LSeries_mul' hζ hζ, LSeries_zetaC hs, sq]
  have hdsq : LSeriesSummable (fun n => divisorCountSq n) s := by
    set δ := (s.re - 1) / 4 with hδ
    have hδ0 : 0 < δ := by rw [hδ]; linarith
    have h1 := card_divisors_isBigO_rpow hδ0
    refine LSeriesSummable_of_isBigO_rpow (x := 1 + 2 * δ) (by rw [hδ]; linarith) ?_
    rw [← Asymptotics.isBigO_norm_left]
    refine (h1.mul h1).congr (fun n => ?_) (fun n => ?_)
    · simp [divisorCountSq_apply, sq]
    · rw [← Real.rpow_add' (Nat.cast_nonneg n) (by linarith)]
      ring_nf
  have hmul := LSeries_mul' hdsq (LSeriesSummable_of_abs_le_one (norm_powIndicator_le 2) hs)
  rw [divisorCountSq_mul_powIndicator, LSeries_mul' hσsum hσsum, hLσ,
    LSeries_powIndicator two_ne_zero h2s] at hmul
  rw [eq_div_iff (riemannZeta_ne_zero_of_one_lt_re (by simpa using h2s))]
  push_cast at hmul
  simp only [divisorCountSq_apply] at hmul
  rw [← hmul]; ring

end NTKB.HardyWright
