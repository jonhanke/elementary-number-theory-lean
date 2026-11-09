/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.QuadraticFields.SqrtFiveFermat

/-!
# Lucas's test for the primality of `M_{4n+3}` (Hardy–Wright § 15.5, Theorem 259)

`r_1, r_2, r_3, … = 3, 7, 47, …`, `r_{m+1} = r_m² - 2`, so that `r_m = ω^(2^m) + ω̄^(2^m)` with
`ω = (1 + √5)/2`, `ω̄ = -1/ω`. Here `lucasR m = r_{m+1}`.

* Theorem 259 (`lucas_test`): if `p` is a prime `4n + 3` and `M = 2^p - 1`, then `M` is prime if and
  only if `r_{p-1} ≡ 0 (mod M)`.

Mathlib has the other test of § 15.5 (`4, 14, 194, …`, `LucasLehmer.s`), `lucas_lehmer_sufficiency`.
The proof is the book's: for `M` prime, `M ≡ 2 (mod 5)` and (15.4.6) give `ω^(M+1) ≡ Nω = -1`; for the
converse, the order of `ω` modulo any prime factor `r` of `M` is `2^(p+1)`, and (15.4.5)/(15.4.6)
force `r = M`.
-/

namespace NTKB.HardyWright

open QuadraticAlgebra

/-- Lucas's sequence `3, 7, 47, …`; `lucasR m` is Hardy–Wright's `r_{m+1}`. -/
def lucasR : ℕ → ℤ
  | 0 => 3
  | n + 1 => lucasR n ^ 2 - 2

/-- `ω = (1 + √5)/2` in `ℤ[ω]`. -/
def omG : ZGold := ⟨0, 1⟩

lemma omG_mul_star : omG * star omG = -1 := by ext <;> simp [omG]

lemma isUnit_omG : IsUnit omG := (omegaUnit).isUnit

lemma norm_omG : norm omG = -1 := by rw [gold_norm]; simp [omG]

/-- `r_{m+1} = ω^(2^(m+1)) + ω̄^(2^(m+1))`. -/
lemma lucasR_eq (m : ℕ) :
    (lucasR m : ZGold) = omG ^ 2 ^ (m + 1) + (star omG) ^ 2 ^ (m + 1) := by
  induction m with
  | zero => ext <;> simp [lucasR, omG, sq]
  | succ m ih =>
    have hprod : (omG * star omG) ^ 2 ^ (m + 1) = 1 := by
      rw [omG_mul_star]
      exact Even.neg_one_pow (by rw [pow_succ]; exact even_two.mul_left _)
    rw [lucasR, Int.cast_sub, Int.cast_pow, ih, pow_succ 2 (m + 1), pow_mul, pow_mul]
    rw [mul_pow] at hprod
    push_cast
    linear_combination 2 * hprod

/-- `ω^(2^(p-1)) r_{p-1} = ω^(2^p) + 1`. -/
lemma omG_pow_mul_lucasR {p : ℕ} (hp : 2 ≤ p) :
    omG ^ 2 ^ (p - 1) * (lucasR (p - 2) : ZGold) = omG ^ 2 ^ p + 1 := by
  have e1 : p - 2 + 1 = p - 1 := by omega
  have e2 : 2 ^ p = 2 ^ (p - 1) * 2 := by rw [← pow_succ]; congr 1; omega
  rw [lucasR_eq, e1, mul_add, ← pow_add, ← two_mul, mul_comm 2, ← e2, ← mul_pow, omG_mul_star]
  congr 1
  exact Even.neg_one_pow (by rw [show p - 1 = p - 2 + 1 by omega, pow_succ]; exact even_two.mul_left _)

lemma gold_int_dvd_of_dvd {n : ℕ} {z : ℤ} (h : (n : ZGold) ∣ (z : ZGold)) : (n : ℤ) ∣ z := by
  obtain ⟨t, ht⟩ := h
  have := congrArg QuadraticAlgebra.re ht
  simp at this
  exact ⟨t.re, this⟩

lemma mersenne_mod_five {p : ℕ} (hp4 : p % 4 = 3) : (2 ^ p - 1) % 5 = 2 := by
  have h : 2 ^ p % 5 = 3 := by
    rw [← Nat.div_add_mod p 4, hp4, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  omega

/-- **Theorem 259** (Lucas). If `p` is a prime `4n + 3` and `M = 2^p - 1`, then `M` is prime if
`r_{p-1} ≡ 0 (mod M)`, and otherwise composite. -/
@[kb "hardywright2008" "Thm 259, p. 310"]
theorem lucas_test {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) :
    (2 ^ p - 1).Prime ↔ ((2 ^ p - 1 : ℕ) : ℤ) ∣ lucasR (p - 2) := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  set M := 2 ^ p - 1 with hM
  have hM5 := mersenne_mod_five hp4
  have h2p : 8 ≤ 2 ^ p := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp3
  have hM1 : M + 1 = 2 ^ p := by omega
  have hunit : ∀ k : ℕ, IsUnit (omG ^ k) := fun k ↦ isUnit_omG.pow k
  constructor
  · -- (1) `M` prime: `ω^(M+1) ≡ Nω = -1 (mod M)`
    intro hMp
    have h := gold_fermat_q hMp (by omega) omG
    rw [norm_omG, hM1] at h
    have h' : (M : ZGold) ∣ omG ^ 2 ^ (p - 1) * (lucasR (p - 2) : ZGold) := by
      rw [omG_pow_mul_lucasR (by omega)]; simpa using h
    exact gold_int_dvd_of_dvd ((IsUnit.dvd_mul_left (hunit _)).1 h')
  · -- (2) the order of `ω` modulo a prime factor `r` of `M` is `2^(p+1)`
    intro hdiv
    have hMne1 : M ≠ 1 := by omega
    set r := M.minFac
    have hr : r.Prime := Nat.minFac_prime hMne1
    have hrM : r ∣ M := Nat.minFac_dvd M
    have hrle : r ≤ M := Nat.minFac_le (by omega)
    have h2e : 2 ∣ 2 ^ p := dvd_pow_self 2 (by omega)
    have hModd : M % 2 = 1 := by omega
    have hr2 : r ≠ 2 := by rintro h; rw [h] at hrM; omega
    have hr5 : r % 5 ≠ 0 := by
      intro h
      have : 5 ∣ r := Nat.dvd_of_mod_eq_zero h
      have h5 := (Nat.prime_dvd_prime_iff_eq Nat.prime_five hr).1 this
      rw [← h5] at hrM; omega
    have hdvd : (r : ZGold) ∣ omG ^ 2 ^ p + 1 := by
      rw [← omG_pow_mul_lucasR (by omega)]
      refine dvd_mul_of_dvd_right ?_ _
      have : (M : ZGold) ∣ (lucasR (p - 2) : ZGold) := by
        obtain ⟨t, ht⟩ := hdiv
        exact ⟨t, by rw [ht]; push_cast; ring⟩
      exact dvd_trans (Nat.cast_dvd_cast hrM) this
    let I := Ideal.span {(r : ZGold)}
    let u := Ideal.Quotient.mk I omG
    have hmk : ∀ x y : ZGold, (r : ZGold) ∣ x - y → Ideal.Quotient.mk I x = Ideal.Quotient.mk I y :=
      fun x y h ↦ Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 h)
    have hu1 : u ^ 2 ^ p = -1 := by
      have := hmk (omG ^ 2 ^ p) (-1) (by simpa using hdvd)
      simpa [u] using this
    have hne : (-1 : ZGold ⧸ I) ≠ 1 := by
      intro h
      have h2 : Ideal.Quotient.mk I (2 : ZGold) = 0 := by
        rw [show (2 : ZGold) = 1 - (-1) by ring, map_sub, map_one, map_neg, map_one, h, sub_self]
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h2
      have := gold_int_dvd_of_dvd (z := 2) (by exact_mod_cast h2)
      have := Int.le_of_dvd (by norm_num) this
      have : r ≤ 2 := by exact_mod_cast this
      have := hr.two_le
      omega
    have hord : orderOf u = 2 ^ (p + 1) := by
      have := Fact.mk Nat.prime_two
      refine orderOf_eq_prime_pow (by rw [hu1]; exact hne) ?_
      rw [pow_succ, pow_mul, hu1, neg_one_sq]
    have hdvd_ord : ∀ n : ℕ, (r : ZGold) ∣ omG ^ n - 1 → 2 ^ (p + 1) ∣ n := fun n h ↦ by
      rw [← hord]
      apply orderOf_dvd_of_pow_eq_one
      have := hmk _ _ h
      simpa [u] using this
    rcases (show r % 5 = 1 ∨ r % 5 = 4 ∨ r % 5 = 2 ∨ r % 5 = 3 by omega) with h | h | h | h
    · -- `r ≡ ±1`: `ω^(r-1) ≡ 1`, so `2^(p+1) ∣ r - 1`, impossible
      exfalso
      have := Fact.mk hr
      have h1 := (gold_dvd_pow_sub hr2 omG).1 (Or.inl h)
      have e : omG ^ r - omG = omG * (omG ^ (r - 1) - 1) := by
        conv_lhs => rw [show r = r - 1 + 1 by have := hr.two_le; omega, pow_succ]
        ring
      rw [e] at h1
      have h2 := hdvd_ord (r - 1) ((IsUnit.dvd_mul_left isUnit_omG).1 h1)
      have := Nat.le_of_dvd (by have := hr.two_le; omega) h2
      rw [pow_succ] at this
      omega
    · exfalso
      have := Fact.mk hr
      have h1 := (gold_dvd_pow_sub hr2 omG).1 (Or.inr h)
      have e : omG ^ r - omG = omG * (omG ^ (r - 1) - 1) := by
        conv_lhs => rw [show r = r - 1 + 1 by have := hr.two_le; omega, pow_succ]
        ring
      rw [e] at h1
      have h2 := hdvd_ord (r - 1) ((IsUnit.dvd_mul_left isUnit_omG).1 h1)
      have := Nat.le_of_dvd (by have := hr.two_le; omega) h2
      rw [pow_succ] at this
      omega
    all_goals
      -- `r ≡ ±2`: `ω^(r+1) ≡ -1`, so `2^(p+1) ∣ 2(r+1)`, hence `r = M`
      have h1 := gold_fermat_q hr (by omega) omG
      rw [norm_omG] at h1
      have h2 : (r : ZGold) ∣ omG ^ (2 * (r + 1)) - 1 := by
        have e : omG ^ (2 * (r + 1)) - 1 =
            (omG ^ (r + 1) - ((-1 : ℤ) : ZGold)) * (omG ^ (r + 1) - 1) := by
          rw [mul_comm 2, pow_mul]; push_cast; ring
        rw [e]; exact dvd_mul_of_dvd_left h1 _
      have h3 := hdvd_ord _ h2
      have h3' : 2 ^ p ∣ r + 1 := by
        rw [pow_succ, mul_comm 2 (r + 1)] at h3
        exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h3
      have h4 := Nat.le_of_dvd (by omega) h3'
      have hrM' : r = M := by omega
      rw [← hrM']; exact hr

end NTKB.HardyWright
