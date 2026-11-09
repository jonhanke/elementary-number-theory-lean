/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.Fermat
import Mathlib.FieldTheory.Finite.Basic
import NTKB.Attr

/-!
# Tests for primality (Hardy–Wright, §§ 6.14 and 6.15)

* Theorem 101: if `p > 2` is prime, `h < p`, `n = h p + 1` or `h p² + 1`, `2^h ≢ 1` and
  `2^{n-1} ≡ 1 (mod n)`, then `n` is prime.
* Theorem 102 (Proth's test): if `m ≥ 2`, `h < 2^m` and `n = h 2^m + 1` is a quadratic non-residue
  of an odd prime `p`, then `n` is prime if and only if `p^{(n-1)/2} ≡ -1 (mod n)`.
* § 6.14 (Pépin's test, both directions): `F_k` is prime if and only if
  `3^{(F_k - 1)/2} ≡ -1 (mod F_k)` (Mathlib's `Nat.pepin_primality'` is the sufficiency).
* Theorem 103 (Euler): if `k > 1` and `p = 4k + 3` is prime, then `2p + 1` is prime if and only if
  `2^p ≡ 1 (mod 2p + 1)`; then `2p + 1 ∣ M_p` and `M_p` is composite.
-/

namespace NTKB.HardyWright

/-- If an odd prime `p` divides `φ(n)` but not `n`, then `n` has a prime factor `P ≡ 1 (mod p)`
(the step "p divides at least one of `P₁ - 1, …, P_k - 1`" of the proof of Theorem 101). -/
lemma exists_prime_dvd_modEq_one_of_dvd_totient {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (hpn : ¬p ∣ n) (hpφ : p ∣ n.totient) : ∃ P, P.Prime ∧ P ∣ n ∧ p ∣ P - 1 := by
  rw [Nat.totient_eq_prod_factorization hn, Prime.dvd_finsuppProd_iff hp.prime] at hpφ
  obtain ⟨P, hP, hdvd⟩ := hpφ
  rw [Nat.support_factorization, Nat.mem_primeFactors] at hP
  refine ⟨P, hP.1, hP.2.1, ?_⟩
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
  · have : p = P := (Nat.prime_dvd_prime_iff_eq hp hP.1).1 (hp.dvd_of_dvd_pow h)
    exact absurd (this ▸ hP.2.1) hpn
  · exact h

/-- If `y^{p^b} = 1` and `y ≠ 1` for a unit `y` of `ZMod n`, then `p ∣ φ(n)`. -/
lemma prime_dvd_totient_of_pow_eq_one {n p b : ℕ} [NeZero n] (hp : p.Prime) (y : (ZMod n)ˣ)
    (hy : y ^ p ^ b = 1) (hy1 : y ≠ 1) : p ∣ n.totient := by
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hy)
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact hy1 (orderOf_eq_one_iff.1 (by simpa using hi))
  have : orderOf y ∣ n.totient := by
    rw [← ZMod.card_units_eq_totient]; exact orderOf_dvd_card
  exact (dvd_pow_self p hi0).trans (hi ▸ this)

/-- **Theorem 101** [hardywright2008]: if `p > 2` is prime, `h < p`, `n = h p^b + 1` with
`b = 1` or `b = 2`, `2^h ≢ 1 (mod n)` and `2^{n-1} ≡ 1 (mod n)`, then `n` is prime. -/
@[kb "hardywright2008" "Thm 101, p. 98"]
theorem prime_of_two_pow_modEq_one {p h b n : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hhp : h < p)
    (hb : b = 1 ∨ b = 2) (hn : n = h * p ^ b + 1) (h1 : ¬2 ^ h ≡ 1 [MOD n])
    (h2 : 2 ^ (n - 1) ≡ 1 [MOD n]) : n.Prime := by
  have hh0 : h ≠ 0 := by rintro rfl; exact h1 rfl
  have hb0 : b ≠ 0 := by omega
  have hpb : 0 < p ^ b := pow_pos hp.pos b
  have hn2 : 2 ≤ n := by rw [hn]; nlinarith [Nat.one_le_iff_ne_zero.2 hh0]
  have : NeZero n := ⟨by omega⟩
  -- the order of `2^h` modulo `n` divides `p^b` and is not `1`, so `p ∣ φ(n)` (Theorem 88)
  have h2' : (2 : ZMod n) ^ (n - 1) = 1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 h2
    push_cast at this; exact this
  have h1' : (2 : ZMod n) ^ h ≠ 1 := by
    intro h'
    apply h1
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast; exact h'
  have hu : IsUnit (2 : ZMod n) := IsUnit.of_pow_eq_one h2' (by omega)
  have hnm1 : n - 1 = h * p ^ b := by omega
  have hpφ : p ∣ n.totient := by
    refine prime_dvd_totient_of_pow_eq_one hp (hu.unit ^ h) ?_ ?_ (b := b)
    · ext; simp [← pow_mul, ← hnm1, h2']
    · intro h'; apply h1'; simpa using congrArg Units.val h'
  have hpn : ¬p ∣ n := by
    intro hd
    have : p ∣ h * p ^ b := dvd_mul_of_dvd_right (dvd_pow_self p hb0) h
    have := (Nat.dvd_add_right this).1 (hn ▸ hd)
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  -- so `n` has a prime factor `P ≡ 1 (mod p)`; write `n = P m`
  obtain ⟨P, hP, hPn, hpP⟩ := exists_prime_dvd_modEq_one_of_dvd_totient hp (by omega) hpn hpφ
  obtain ⟨m, rfl⟩ := hPn
  obtain ⟨x, hx⟩ := hpP
  have hP2 := hP.two_le
  have hx1 : 1 ≤ x := by
    rcases Nat.eq_zero_or_pos x with rfl | h; · omega
    · exact h
  have hPx : P = p * x + 1 := by omega
  -- `m ≡ 1 (mod p)`
  have hm : m % p = 1 := by
    have e : P * m = p * (x * m) + m := by rw [hPx]; ring
    have e2 : h * p ^ b + 1 = p * (h * p ^ (b - 1)) + 1 := by
      rw [← mul_assoc, mul_comm p h, mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega)]
    have := hn.symm.trans e
    rw [e2] at this
    have h3 := congrArg (· % p) this
    simp only [Nat.mul_add_mod] at h3
    rw [Nat.mod_eq_of_lt (by omega : 1 < p)] at h3
    exact h3.symm
  obtain ⟨y, hy⟩ : ∃ y, m = p * y + 1 := ⟨m / p, by have := Nat.div_add_mod m p; omega⟩
  rcases Nat.eq_zero_or_pos y with rfl | hy1
  · simpa [hy] using hP
  exfalso
  -- `n = (x p + 1)(y p + 1)` is impossible
  have key : h * p ^ b = p * (x * y * p + x + y) := by
    have : h * p ^ b + 1 = (p * x + 1) * (p * y + 1) := by rw [← hn, ← hPx, ← hy]
    nlinarith
  rcases hb with rfl | rfl
  · -- `b = 1`: `h = x y p + x + y > p`
    rw [pow_one, mul_comm h p] at key
    have := Nat.eq_of_mul_eq_mul_left hp.pos key
    nlinarith
  · -- `b = 2`: `h p = x y p + x + y`
    rw [sq, ← mul_assoc, mul_comm h p, mul_assoc] at key
    have key2 := Nat.eq_of_mul_eq_mul_left hp.pos key
    have hdvd : p ∣ x + y := by
      have : p ∣ x * y * p + (x + y) := ⟨h, by rw [← add_assoc]; linarith⟩
      exact (Nat.dvd_add_right (dvd_mul_left p _)).1 this
    have hxy : p ≤ x + y := Nat.le_of_dvd (by omega) hdvd
    have hxy2 : x * y + 1 ≤ h := by nlinarith
    -- `x y ≤ p - 2`, which forces `x = 1` or `y = 1`, and then `x y ≥ p - 1`
    rcases Nat.lt_or_ge x 2 with hx2 | hx2
    · have hx : x = 1 := by omega
      subst hx
      have : p ∣ y + 1 := by
        have : p ∣ 1 * y * p + (1 + y) := ⟨h, by rw [← add_assoc]; linarith⟩
        rw [add_comm 1 y] at this
        exact (Nat.dvd_add_right (dvd_mul_left p _)).1 this
      have := Nat.le_of_dvd (by omega) this
      nlinarith
    rcases Nat.lt_or_ge y 2 with hy2 | hy2
    · have hy : y = 1 := by omega
      subst hy
      have : p ∣ x + 1 := by
        have : p ∣ x * 1 * p + (x + 1) := ⟨h, by rw [← add_assoc]; linarith⟩
        exact (Nat.dvd_add_right (dvd_mul_left p _)).1 this
      have := Nat.le_of_dvd (by omega) this
      nlinarith
    · nlinarith

/-- **Theorem 102** [hardywright2008] (Proth's test): let `m ≥ 2`, `h < 2^m` and let
`n = h 2^m + 1` be a quadratic non-residue modulo some odd prime `p`. Then `n` is prime if and only
if `p^{(n-1)/2} ≡ -1 (mod n)`. -/
@[kb "hardywright2008" "Thm 102, p. 99"]
theorem prime_iff_pow_half_eq_neg_one {p m h n : ℕ} [hpf : Fact p.Prime] (hp2 : p ≠ 2)
    (hm : 2 ≤ m) (hh : h < 2 ^ m) (hn : n = h * 2 ^ m + 1) (hnr : ¬IsSquare (n : ZMod p)) :
    n.Prime ↔ (p : ZMod n) ^ ((n - 1) / 2) = -1 := by
  have hh0 : h ≠ 0 := by
    rintro rfl; apply hnr; rw [hn]; simp
  have h4 : 4 ∣ 2 ^ m := by
    rw [show 4 = 2 ^ 2 by norm_num]; exact Nat.pow_dvd_pow 2 hm
  have hn4 : n % 4 = 1 := by
    obtain ⟨c, hc⟩ := h4; rw [hn, hc, show h * (4 * c) = 4 * (h * c) by ring]; omega
  have hn5 : 5 ≤ n := by
    have h1 : 4 ≤ 2 ^ m := Nat.le_of_dvd (by positivity) h4
    have h2 : 2 ^ m ≤ h * 2 ^ m := Nat.le_mul_of_pos_left _ (by omega)
    omega
  obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hhalf : (n - 1) / 2 = h * 2 ^ k := by
    rw [hn, Nat.add_sub_cancel, hk, pow_succ, ← mul_assoc, Nat.mul_div_cancel _ two_pos]
  constructor
  · -- necessity: `(p/n) = (n/p) = -1` by reciprocity (`n ≡ 1 (mod 4)`), then Euler's criterion
    intro hnp
    have := Fact.mk hnp
    have hrec := legendreSym.quadratic_reciprocity_one_mod_four hn4 hp2 (p := n) (q := p)
    have hnr' : legendreSym p n = -1 := (legendreSym.eq_neg_one_iff' p).2 hnr
    have := legendreSym.eq_pow n p
    rw [← hrec, hnr'] at this
    have hdiv : (n - 1) / 2 = n / 2 := by omega
    rw [hdiv]
    push_cast at this
    exact this.symm
  · -- sufficiency: every prime factor `P` of `n` is `≡ 1 (mod 2^m)`
    intro hpow
    obtain ⟨P, hP, hPn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
    have := Fact.mk hP
    have hP2 : P ≠ 2 := by
      rintro rfl
      have : 2 ∣ n := hPn
      omega
    have : Fact (2 < P) := ⟨by have := hP.two_le; omega⟩
    -- reduce `p^{(n-1)/2} ≡ -1` modulo `P`
    have hpowP : (p : ZMod P) ^ ((n - 1) / 2) = -1 := by
      have := congrArg (ZMod.castHom hPn (ZMod P)) hpow
      rwa [map_pow, map_natCast, map_neg, map_one] at this
    -- the order of `p^h` modulo `P` is exactly `2^m`, and it divides `P - 1`
    have hord : orderOf ((p : ZMod P) ^ h) = 2 ^ m := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rw [hk]
      apply orderOf_eq_prime_pow
      · rw [← pow_mul, ← hhalf, hpowP]; exact ZMod.neg_one_ne_one
      · rw [← pow_mul, pow_succ, ← mul_assoc, pow_mul, ← hhalf, hpowP]
        norm_num
    have hp0 : (p : ZMod P) ^ h ≠ 0 := by
      intro h0
      rw [hhalf, pow_mul, h0, zero_pow (by positivity)] at hpowP
      exact one_ne_zero (neg_eq_zero.1 hpowP.symm)
    have h2m : 2 ^ m ∣ P - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one hp0
    -- `n / P ≡ 1 (mod 2^m)`, so `n = (2^m x + 1)(2^m y + 1)` and `h = 2^m x y + x + y < 2^m`
    obtain ⟨x, hx⟩ := h2m
    obtain ⟨Q, rfl⟩ := hPn
    have hPx : P = 2 ^ m * x + 1 := by have := hP.two_le; omega
    have hQ : Q % 2 ^ m = 1 := by
      have e : (2 ^ m * x + 1) * Q = 2 ^ m * (x * Q) + Q := by ring
      have e2 : h * 2 ^ m + 1 = 2 ^ m * h + 1 := by ring
      have := hn.symm.trans (hPx ▸ e)
      rw [e2] at this
      have h3 := congrArg (· % 2 ^ m) this
      simp only [Nat.mul_add_mod] at h3
      rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))] at h3
      exact h3.symm
    obtain ⟨y, hy⟩ : ∃ y, Q = 2 ^ m * y + 1 :=
      ⟨Q / 2 ^ m, by have := Nat.div_add_mod Q (2 ^ m); omega⟩
    rcases Nat.eq_zero_or_pos y with rfl | hy1
    · simpa [hy] using hP
    exfalso
    have hx1 : 1 ≤ x := by
      rcases Nat.eq_zero_or_pos x with rfl | h; · have := hP.two_le; omega
      · exact h
    have key : h * 2 ^ m = 2 ^ m * (2 ^ m * x * y + x + y) := by
      have : h * 2 ^ m + 1 = (2 ^ m * x + 1) * (2 ^ m * y + 1) := by rw [← hn, ← hPx, ← hy]
      nlinarith
    rw [mul_comm h] at key
    have := Nat.eq_of_mul_eq_mul_left (by positivity) key
    nlinarith

/-- **Pépin's test** [hardywright2008, § 6.14]: for `k ≥ 1` the Fermat number `F_k` is prime if
and only if `3^{(F_k - 1)/2} ≡ -1 (mod F_k)`; the case `h = 1`, `m = 2^k`, `p = 3` of
Theorem 102. -/
@[kb "hardywright2008" "§ 6.14, p. 100"]
theorem fermatNumber_prime_iff {k : ℕ} (hk : 1 ≤ k) :
    (Nat.fermatNumber k).Prime ↔
      (3 : ZMod (Nat.fermatNumber k)) ^ ((Nat.fermatNumber k - 1) / 2) = -1 := by
  have hm : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  -- `F_k ≡ 2 (mod 3)` is a non-residue of `3`
  have hF : ((Nat.fermatNumber k : ℕ) : ZMod 3) = 2 := by
    obtain ⟨j, hj⟩ : ∃ j, 2 ^ k = 2 * j := ⟨2 ^ (k - 1), by
      rw [← pow_succ', Nat.sub_add_cancel hk]⟩
    rw [Nat.fermatNumber, hj, pow_mul]
    push_cast
    rw [show (4 : ZMod 3) = 1 by decide, one_pow]
    decide
  have h2 : ¬IsSquare (2 : ZMod 3) := by decide
  have hnr : ¬IsSquare ((Nat.fermatNumber k : ℕ) : ZMod 3) := by
    rw [hF]; exact h2
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := prime_iff_pow_half_eq_neg_one (p := 3) (m := 2 ^ k) (h := 1) (by norm_num) hm
    (Nat.one_lt_two_pow (by omega)) (by rw [Nat.fermatNumber, one_mul]) hnr
  simpa using this

/-- **Theorem 103** [hardywright2008] (Euler): if `k > 1` and `p = 4k + 3` is prime, then `2p + 1`
is prime if and only if `2^p ≡ 1 (mod 2p + 1)`. (The hypothesis `k > 1` is only needed for the second
part, `dvd_mersenne_and_not_prime`.) -/
@[kb "hardywright2008" "Thm 103, p. 100"]
theorem prime_two_mul_add_one_iff {k p : ℕ} (_hk : 1 < k) (hpk : p = 4 * k + 3) (hp : p.Prime) :
    (2 * p + 1).Prime ↔ 2 ^ p ≡ 1 [MOD 2 * p + 1] := by
  constructor
  · -- `P = 2p + 1 ≡ 7 (mod 8)`, so `2` is a residue of `P` (Theorem 95) and `2^p ≡ 1` (Theorem 83)
    intro hP
    have := Fact.mk hP
    have h2 : IsSquare (2 : ZMod (2 * p + 1)) :=
      (ZMod.exists_sq_eq_two_iff (by omega)).2 (Or.inr (by omega))
    have h20 : (2 : ZMod (2 * p + 1)) ≠ 0 := by
      intro h0
      have : 2 * p + 1 ∣ 2 := (ZMod.natCast_eq_zero_iff 2 _).1 (by exact_mod_cast h0)
      have := Nat.le_of_dvd (by norm_num) this
      omega
    have := (ZMod.euler_criterion (2 * p + 1) h20).1 h2
    rw [show (2 * p + 1) / 2 = p by omega] at this
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    exact this
  · -- Theorem 101 with `h = 2`, `n = 2p + 1`
    intro h2p
    refine prime_of_two_pow_modEq_one (p := p) (h := 2) (b := 1) hp (by omega) (by omega)
      (Or.inl rfl) (by ring) ?_ ?_
    · intro h4
      have := Nat.ModEq.symm h4
      rw [Nat.ModEq, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
      omega
    · rw [show 2 * p + 1 - 1 = p * 2 by omega, pow_mul]
      simpa using h2p.pow 2

/-- **Theorem 103** [hardywright2008], second part: if moreover `2p + 1` is prime, then
`2p + 1 ∣ M_p = 2^p - 1` and `M_p` is composite. -/
@[kb "hardywright2008" "Thm 103, p. 100"]
theorem dvd_mersenne_and_not_prime {k p : ℕ} (hk : 1 < k) (hpk : p = 4 * k + 3) (hp : p.Prime)
    (hP : (2 * p + 1).Prime) : 2 * p + 1 ∣ 2 ^ p - 1 ∧ ¬(2 ^ p - 1).Prime := by
  have h := (prime_two_mul_add_one_iff hk hpk hp).1 hP
  have hdvd : 2 * p + 1 ∣ 2 ^ p - 1 := (Nat.modEq_iff_dvd' Nat.one_le_two_pow).1 h.symm
  refine ⟨hdvd, fun hM ↦ ?_⟩
  -- `M_p > 2p + 1` since `p > 3`
  have hlt : 2 * p + 1 < 2 ^ p - 1 := by
    have : ∀ q, 11 ≤ q → 2 * q + 2 < 2 ^ q := by
      intro q hq
      induction q, hq using Nat.le_induction with
      | base => norm_num
      | succ q hq ih => rw [pow_succ]; omega
    have := this p (by omega)
    omega
  rcases (Nat.dvd_prime hM).1 hdvd with h1 | h1 <;> omega

end NTKB.HardyWright
