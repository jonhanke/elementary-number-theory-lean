/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import NTKB.Elementary.HardyWright.CompositeModuli.Bauer

/-!
# The generalized Wilson theorem (Hardy–Wright, § 8.8 (1))

* Theorem 129 (Gauss): `∏_{t ∈ t(m)} t ≡ ±1 (mod m)`, with the negative sign exactly when `m` is
  `4`, `p^a` or `2 p^a` for an odd prime `p` (`m > 2`; for `m ≤ 2` both signs agree).

As in the book, the constant terms of Bauer's congruences (Theorems 126, 127) give
`∏ t ≡ (-1)^{φ(m)/(p-1)} (mod p^a)` for every `p^a ∥ m`, and the exponents are even except in the
special cases.
-/

open Polynomial Finset

namespace NTKB.HardyWright

/-- The constant term of `f_m(x)` is `(-1)^{φ(m)} ∏_{t ∈ t(m)} t`. -/
lemma bauerPoly_map_eval_zero (m : ℕ) {R : Type*} [CommRing R] :
    ((bauerPoly m).map (Int.castRingHom R)).eval 0 =
      (-1) ^ m.totient * ((∏ t ∈ (range m).filter (·.Coprime m), t : ℕ) : R) := by
  rw [bauerPoly, Polynomial.map_prod, eval_prod, Nat.cast_prod]
  have : ∀ t ∈ (range m).filter (·.Coprime m), ((X - C (t : ℤ)).map (Int.castRingHom R)).eval 0 =
      (-1) * (t : R) := fun t _ ↦ by simp
  have hcard : ((range m).filter (·.Coprime m)).card = m.totient := by
    rw [Nat.totient_eq_card_coprime]
    congr 1
    ext x; simp [Nat.coprime_comm]
  rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib, Finset.prod_const, hcard]

/-- For `p^a ∥ m`, `p` odd, `m > 2`: `∏_{t ∈ t(m)} t ≡ (-1)^{φ(m)/(p-1)} (mod p^a)`. -/
lemma prod_coprime_mod_prime_pow (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) {m a : ℕ} (hm : 2 < m)
    (ha : 1 ≤ a) (hpa : p ^ a ∣ m) (hpa1 : ¬p ^ (a + 1) ∣ m) :
    ((∏ t ∈ (range m).filter (·.Coprime m), t : ℕ) : ZMod (p ^ a)) =
      (-1) ^ (m.totient / (p - 1)) := by
  have h := congrArg (eval 0) (bauerPoly_map_prime_pow p hp2 (by omega) ha hpa hpa1)
  rw [bauerPoly_map_eval_zero, (Nat.totient_even hm).neg_one_pow, one_mul] at h
  rw [h]
  simp [zero_pow (by have := hp.out.two_le; omega : p - 1 ≠ 0)]

/-- For `2^a ∥ m`, `m > 2`: `∏_{t ∈ t(m)} t ≡ (-1)^{φ(m)/2} (mod 2^a)`. -/
lemma prod_coprime_mod_two_pow {m a : ℕ} (hm : 2 < m) (ha : 1 ≤ a) (hpa : 2 ^ a ∣ m)
    (hpa1 : ¬2 ^ (a + 1) ∣ m) :
    ((∏ t ∈ (range m).filter (·.Coprime m), t : ℕ) : ZMod (2 ^ a)) = (-1) ^ (m.totient / 2) := by
  have h := congrArg (eval 0) (bauerPoly_map_two_pow hm ha hpa hpa1)
  rw [bauerPoly_map_eval_zero, (Nat.totient_even hm).neg_one_pow, one_mul] at h
  rw [h]
  simp

/-- The special moduli `4`, `p^a`, `2 p^a` (`p` an odd prime, `a ≥ 1`) of Theorem 129. -/
def IsWilsonModulus (m : ℕ) : Prop :=
  m = 4 ∨ ∃ p a : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ a ∧ (m = p ^ a ∨ m = 2 * p ^ a)

/-- `φ(p^a M)/(p - 1) = p^{a-1} φ(M)` for `(p^a, M) = 1`. -/
lemma totient_prime_pow_mul_div {p a M : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (hcop : (p ^ a).Coprime M) :
    (p ^ a * M).totient / (p - 1) = p ^ (a - 1) * M.totient := by
  rw [Nat.totient_mul hcop, Nat.totient_prime_pow hp (by omega),
    show p ^ (a - 1) * (p - 1) * M.totient = (p - 1) * (p ^ (a - 1) * M.totient) by ring,
    Nat.mul_div_cancel_left _ (by have := hp.two_le; omega)]

open Classical in
/-- **Theorem 129** [hardywright2008] (Gauss's generalization of Wilson's theorem): for `m > 2`,
`∏_{t ∈ t(m)} t ≡ -1 (mod m)` if `m` is `4`, `p^a` or `2 p^a` with `p` an odd prime, and
`≡ +1 (mod m)` otherwise. -/
@[kb "hardywright2008" "Thm 129, p. 132"]
theorem prod_coprime_eq_ite (m : ℕ) (hm : 2 < m) :
    ((∏ t ∈ (range m).filter (·.Coprime m), t : ℕ) : ZMod m) =
      if IsWilsonModulus m then -1 else 1 := by
  classical
  set P := ∏ t ∈ (range m).filter (·.Coprime m), t
  set s : ℤ := if IsWilsonModulus m then -1 else 1 with hs
  suffices h : (m : ℤ) ∣ s - P by
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub (P : ℤ) s m).2 h
    push_cast at this
    rw [this, hs]
    split_ifs <;> simp
  -- it suffices to check the congruence modulo every `p^a ∥ m`
  have hm0 : m ≠ 0 := by omega
  conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hm0]
  push_cast
  refine Finset.prod_dvd_of_coprime ?_ fun p hp ↦ ?_
  · intro p hp q hq hpq
    simp only [Function.onFun]
    exact_mod_cast Nat.isCoprime_iff_coprime.2 (Nat.coprime_pow_primes _ _
      (Nat.prime_of_mem_primeFactors hp) (Nat.prime_of_mem_primeFactors hq) hpq)
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpm := Nat.dvd_of_mem_primeFactors hp
  obtain ⟨a, ha_def⟩ : ∃ a, m.factorization p = a := ⟨_, rfl⟩
  rw [ha_def]
  have ha : 1 ≤ a := ha_def ▸ hpp.factorization_pos_of_dvd hm0 hpm
  have hpa : p ^ a ∣ m := ha_def ▸ Nat.ordProj_dvd m p
  have hpa1 : ¬p ^ (a + 1) ∣ m := ha_def ▸ Nat.pow_succ_factorization_not_dvd hm0 hpp
  obtain ⟨M, hmM, hM0, hcop⟩ := exists_eq_prime_pow_mul hpp hm0 hpa hpa1
  suffices hz : ((P : ℕ) : ZMod (p ^ a)) = ((s : ℤ) : ZMod (p ^ a)) by
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub (P : ℤ) s (p ^ a)).1 (by exact_mod_cast hz)
    exact_mod_cast this
  have : Fact p.Prime := ⟨hpp⟩
  have hMp : ¬p ∣ M := fun h ↦ (Nat.Prime.coprime_iff_not_dvd hpp).1
    (Nat.Coprime.coprime_dvd_left (dvd_pow_self p (by omega)) hcop) h
  rcases eq_or_ne p 2 with rfl | hp2
  · -- `p = 2`
    rw [prod_coprime_mod_two_pow hm ha hpa hpa1]
    rcases Nat.lt_or_ge a 2 with ha1 | ha2
    · -- `a = 1`: modulo `2` both sides are `1`
      have h1 : a = 1 := by omega
      subst h1
      have hneg : (-1 : ZMod (2 ^ 1)) = 1 := rfl
      rw [hneg, one_pow, hs]
      split_ifs <;> simp [hneg]
    · -- `a ≥ 2`: the sign is `-1` exactly for `m = 4`
      have hk : m.totient / 2 = 2 ^ (a - 2) * M.totient := by
        rw [hmM, Nat.totient_mul hcop, Nat.totient_prime_pow Nat.prime_two (by omega),
          show a - 1 = (a - 2) + 1 by omega, pow_succ,
          show 2 ^ (a - 2) * 2 * (2 - 1) * M.totient = 2 * (2 ^ (a - 2) * M.totient) by ring,
          Nat.mul_div_cancel_left _ two_pos]
      rw [hk]
      have h4a : 4 ≤ 2 ^ a := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha2
      by_cases h4 : m = 4
      · have hW : IsWilsonModulus m := Or.inl h4
        have hle : 2 ^ a ≤ 4 := by
          rw [← h4, hmM]; exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hM0)
        have h2a : 2 ^ a = 2 ^ 2 := by omega
        have ha2' : a = 2 := Nat.pow_right_injective le_rfl h2a
        have hM1 : M = 1 := by
          have : 2 ^ a * M = 2 ^ a * 1 := by rw [mul_one, ← hmM, h4, h2a]; norm_num
          exact Nat.eq_of_mul_eq_mul_left (by positivity) this
        rw [ha2', hM1, hs, if_pos hW]
        simp
      · have hW : ¬IsWilsonModulus m := by
          rintro (h | ⟨q, b, hq, hq2, hb, h | h⟩)
          · exact h4 h
          · have : 2 ∣ q ^ b := h ▸ hpm
            exact hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1
              (Nat.prime_two.dvd_of_dvd_pow this)).symm
          · have h4m : 4 ∣ m := (pow_dvd_pow 2 ha2).trans hpa
            rw [h, show (4 : ℕ) = 2 * 2 by norm_num] at h4m
            have : 2 ∣ q ^ b := Nat.dvd_of_mul_dvd_mul_left two_pos h4m
            exact hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1
              (Nat.prime_two.dvd_of_dvd_pow this)).symm
        have heven : Even (2 ^ (a - 2) * M.totient) := by
          rcases Nat.lt_or_ge a 3 with ha3 | ha3
          · have ha2' : a = 2 := by omega
            have hM1 : M ≠ 1 := by
              rintro rfl; apply h4; rw [hmM, ha2']; norm_num
            have hMo : M % 2 = 1 := Nat.two_dvd_ne_zero.1 hMp
            exact (Nat.totient_even (by omega)).mul_left _
          · exact (Nat.even_pow.2 ⟨even_two, by omega⟩).mul_right _
        rw [heven.neg_one_pow, hs, if_neg hW]
        simp
  · -- `p` odd: the exponent `φ(m)/(p - 1) = p^{a-1} φ(M)` is odd exactly when `M ≤ 2`
    rw [prod_coprime_mod_prime_pow p hp2 hm ha hpa hpa1]
    have hk : m.totient / (p - 1) = p ^ (a - 1) * M.totient := by
      rw [hmM]; exact totient_prime_pow_mul_div hpp ha hcop
    rw [hk]
    have hpodd : Odd p := hpp.odd_of_ne_two hp2
    by_cases hM2 : M ≤ 2
    · have hW : IsWilsonModulus m := by
        refine Or.inr ⟨p, a, hpp, hp2, ha, ?_⟩
        interval_cases M
        · exact absurd rfl hM0
        · left; rw [hmM, mul_one]
        · right; rw [hmM, mul_comm]
      have hφ : M.totient = 1 := by interval_cases M <;> simp_all
      rw [hφ, mul_one, (hpodd.pow).neg_one_pow, hs, if_pos hW]
      simp
    · have hW : ¬IsWilsonModulus m := by
        rintro (h | ⟨q, b, hq, hq2, hb, h | h⟩)
        · -- `p ∣ 4` is impossible
          rw [h, show (4 : ℕ) = 2 ^ 2 by norm_num] at hpm
          exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1
            (hpp.dvd_of_dvd_pow hpm))
        · -- `m = q^b` forces `q = p` and `M = 1`
          have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hpp hq).1
            (hpp.dvd_of_dvd_pow (h ▸ hpm))
          subst hpq
          have hMd : M ∣ p ^ b := ⟨p ^ a, by rw [← h, hmM, mul_comm]⟩
          have := Nat.Coprime.eq_one_of_dvd
            (Nat.Coprime.pow_right b ((Nat.coprime_comm.1
              ((Nat.Prime.coprime_iff_not_dvd hpp).2 hMp)))) hMd
          omega
        · -- `m = 2 q^b` forces `q = p` and `M ∣ 2`
          have hpq : p = q := by
            have h2 : p ∣ 2 * q ^ b := h ▸ hpm
            rcases (Nat.Prime.dvd_mul hpp).1 h2 with h2 | h2
            · exact absurd ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 h2) hp2
            · exact (Nat.prime_dvd_prime_iff_eq hpp hq).1 (hpp.dvd_of_dvd_pow h2)
          subst hpq
          have hMd : M ∣ 2 * p ^ b := ⟨p ^ a, by rw [← h, hmM, mul_comm]⟩
          have hMd2 : M ∣ 2 := Nat.Coprime.dvd_of_dvd_mul_right
            (Nat.Coprime.pow_right b ((Nat.coprime_comm.1
              ((Nat.Prime.coprime_iff_not_dvd hpp).2 hMp)))) hMd
          have := Nat.le_of_dvd two_pos hMd2
          omega
      have heven : Even (p ^ (a - 1) * M.totient) :=
        (Nat.totient_even (by omega)).mul_left _
      rw [heven.neg_one_pow, hs, if_neg hW]
      simp

end NTKB.HardyWright
