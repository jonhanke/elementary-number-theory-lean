/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.QuadraticFields.SqrtFive

/-!
# Fermat's theorem in `k(√5)` (Hardy–Wright, Theorem 258)

Let `p` and `q` denote rational primes `5n ± 1` and `5n ± 2`, `π` a prime of `k(√5)`,
`φ(π) = |Nπ| - 1`.

* (15.4.5) `gold_fermat_p`: `π ∣ p`, `(a, π) = 1` ⟹ `a^(p-1) ≡ 1 (mod π)`.
* (15.4.6) `gold_fermat_q`: `a^(q+1) ≡ Na (mod q)` (also for `q = 2`).
* (15.4.7) `gold_fermat_p'`: `π ∣ p`, `(a, π) = (a, π̄) = 1` ⟹ `a^(p-1) ≡ 1 (mod p)`.
* (15.4.4) `gold_fermat`: `π` not an associate of `√5`, `(a, π) = 1` ⟹ `a^φ(π) ≡ 1 (mod π)`.

The proof is the book's: `2a = c + d√5`, `(2a)^p ≡ c + d·5^((p-1)/2)√5 (mod p)` and
`5^((p-1)/2) ≡ ±1` by Euler's criterion and quadratic reciprocity (`five_pow_half`).
-/

namespace NTKB.HardyWright

open QuadraticAlgebra

lemma gold_int_dvd_pow_sub (p : ℕ) [Fact p.Prime] (l : ℤ) : (p : ZGold) ∣ (l : ZGold) ^ p - l := by
  have h : (p : ℤ) ∣ l ^ p - l := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.pow_card, sub_self]
  have := (Int.castRingHom ZGold).map_dvd h
  simpa using this

/-- `2a = c + d√5` with `c = 2x + y`, `d = y`. -/
lemma gold_two_mul_eq (a : ZGold) :
    2 * a = ((2 * a.re + a.im : ℤ) : ZGold) + (a.im : ZGold) * sqrtFive := by
  ext <;> simp [sqrtFive] <;> ring

lemma gold_two_mul_star_eq (a : ZGold) :
    2 * star a = ((2 * a.re + a.im : ℤ) : ZGold) - (a.im : ZGold) * sqrtFive := by
  ext <;> simp [sqrtFive] <;> ring

/-- The core of (15.4.8) and (15.4.10): for a prime `p ≠ 2`, `a^p ≡ a (mod p)` if `p ≡ ±1` and
`a^p ≡ ā (mod p)` if `p ≡ ±2 (mod 5)`. -/
lemma gold_dvd_pow_sub {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (a : ZGold) :
    ((p % 5 = 1 ∨ p % 5 = 4) → (p : ZGold) ∣ a ^ p - a) ∧
      ((p % 5 = 2 ∨ p % 5 = 3) → (p : ZGold) ∣ a ^ p - star a) := by
  have hodd : p = 2 * (p / 2) + 1 := by
    rcases hp.out.eq_two_or_odd' with h | h
    · exact absurd h hp2
    · have := Nat.odd_iff.1 h; omega
  -- `√5^p ≡ ε √5 (mod p)` when `5^((p-1)/2) ≡ ε`
  have hs : ∀ ε : ℤ, (5 : ZMod p) ^ (p / 2) = ε →
      (p : ZGold) ∣ sqrtFive ^ p - (ε : ZGold) * sqrtFive := by
    intro ε hε
    have h1 : (p : ℤ) ∣ 5 ^ (p / 2) - ε := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [hε, sub_self]
    have h2 : (p : ZGold) ∣ (5 : ZGold) ^ (p / 2) - ε := by
      simpa using (Int.castRingHom ZGold).map_dvd h1
    have e : sqrtFive ^ p - (ε : ZGold) * sqrtFive = sqrtFive * ((5 : ZGold) ^ (p / 2) - ε) := by
      conv_lhs => rw [hodd, pow_succ, pow_mul, sq, sqrtFive_sq]
      ring
    rw [e]
    exact dvd_mul_of_dvd_right h2 _
  -- `(2a)^p ≡ c + d √5^p (mod p)`
  set c : ℤ := 2 * a.re + a.im
  set d : ℤ := a.im
  have hfrob : (p : ZGold) ∣ (2 * a) ^ p - ((c : ZGold) + (d : ZGold) * sqrtFive ^ p) := by
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp.out (c : ZGold) ((d : ZGold) * sqrtFive)
    rw [gold_two_mul_eq, hr]
    have e : (c : ZGold) ^ p + ((d : ZGold) * sqrtFive) ^ p + p * c * (d * sqrtFive) * r -
        ((c : ZGold) + (d : ZGold) * sqrtFive ^ p) =
        ((c : ZGold) ^ p - c) + ((d : ZGold) ^ p - d) * sqrtFive ^ p +
          p * (c * (d * sqrtFive) * r) := by ring
    rw [e]
    exact dvd_add (dvd_add (gold_int_dvd_pow_sub p c)
      (dvd_mul_of_dvd_left (gold_int_dvd_pow_sub p d) _)) (dvd_mul_right _ _)
  have h2p : (p : ZGold) ∣ (2 : ZGold) ^ p - 2 := by
    have := gold_int_dvd_pow_sub p 2; push_cast at this; exact this
  have hcop : IsCoprime (p : ZGold) 2 := by
    have : IsCoprime (p : ℤ) 2 := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      have : Nat.Coprime p 2 := (Nat.coprime_primes hp.out Nat.prime_two).2 hp2
      exact_mod_cast this
    have := this.map (Int.castRingHom ZGold)
    simpa using this
  -- from `p ∣ (2a)^p - 2a'` deduce `p ∣ a^p - a'`
  have finish : ∀ a' : ZGold, (p : ZGold) ∣ (2 * a) ^ p - 2 * a' → (p : ZGold) ∣ a ^ p - a' := by
    intro a' h
    have : (p : ZGold) ∣ 2 * (a ^ p - a') := by
      have e : 2 * (a ^ p - a') = ((2 * a) ^ p - 2 * a') - ((2 : ZGold) ^ p - 2) * a ^ p := by ring
      rw [e]; exact dvd_sub h (dvd_mul_of_dvd_left h2p _)
    exact hcop.dvd_of_dvd_mul_left this
  have h5 := five_pow_half (p := p) hp2
  refine ⟨fun h ↦ finish a ?_, fun h ↦ finish (star a) ?_⟩
  · have := hs 1 (by rw [h5.1 h]; simp)
    have e2 := gold_two_mul_eq a
    convert dvd_add hfrob (dvd_mul_of_dvd_right this (d : ZGold)) using 1
    push_cast
    linear_combination (-1 : ZGold) * e2
  · have := hs (-1) (by rw [h5.2 h]; simp)
    have e2 := gold_two_mul_star_eq a
    convert dvd_add hfrob (dvd_mul_of_dvd_right this (d : ZGold)) using 1
    push_cast
    linear_combination (-1 : ZGold) * e2

/-- `a² ≡ ā (mod 2)` (§ 15.4, the case `q = 2`). -/
lemma gold_two_dvd_sq_sub_star (a : ZGold) : (2 : ZGold) ∣ a ^ 2 - star a := by
  obtain ⟨e, f⟩ := a
  obtain ⟨k1, hk1⟩ := Int.even_mul_pred_self e
  obtain ⟨k2, hk2⟩ := Int.even_mul_pred_self f
  obtain ⟨k3, hk3⟩ := Int.even_mul_succ_self f
  refine ⟨⟨k1 + k2, e * f + k3⟩, ?_⟩
  ext <;> simp [sq] <;> linarith

/-- **Theorem 258**, (15.4.5): if `π ∣ p`, `p` a rational prime `5n ± 1`, and `(a, π) = 1`, then
`a^(p-1) ≡ 1 (mod π)`. -/
@[kb "hardywright2008" "Thm 258, p. 307"]
theorem gold_fermat_p {p : ℕ} (hp : p.Prime) (hp5 : p % 5 = 1 ∨ p % 5 = 4) {π a : ZGold}
    (hπ : Prime π) (hπp : π ∣ (p : ZGold)) (ha : ¬ π ∣ a) : π ∣ a ^ (p - 1) - 1 := by
  have := Fact.mk hp
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h := dvd_trans hπp ((gold_dvd_pow_sub hp2 a).1 hp5)
  have e : a ^ p - a = a * (a ^ (p - 1) - 1) := by
    conv_lhs => rw [show p = p - 1 + 1 by have := hp.two_le; omega, pow_succ]
    ring
  rw [e] at h
  exact (hπ.dvd_or_dvd h).resolve_left ha

/-- **Theorem 258**, (15.4.6): if `q` is a rational prime `5n ± 2`, then `a^(q+1) ≡ Na (mod q)`. -/
@[kb "hardywright2008" "Thm 258, p. 307"]
theorem gold_fermat_q {q : ℕ} (hq : q.Prime) (hq5 : q % 5 = 2 ∨ q % 5 = 3) (a : ZGold) :
    (q : ZGold) ∣ a ^ (q + 1) - ((norm a : ℤ) : ZGold) := by
  have hN : ((norm a : ℤ) : ZGold) = a * star a := by rw [← algebraMap_norm_eq_mul_star]; rfl
  rw [hN]
  by_cases hq2 : q = 2
  · subst hq2
    have e : a ^ (2 + 1) - a * star a = a * (a ^ 2 - star a) := by ring
    rw [e]; push_cast
    exact dvd_mul_of_dvd_right (gold_two_dvd_sq_sub_star a) _
  · have := Fact.mk hq
    have h := (gold_dvd_pow_sub hq2 a).2 hq5
    have e : a ^ (q + 1) - a * star a = a * (a ^ q - star a) := by ring
    rw [e]
    exact dvd_mul_of_dvd_right h _

/-- A prime dividing a rational prime `p ≡ ±1 (mod 5)` has norm `±p`. -/
lemma gold_natAbs_norm_of_dvd {p : ℕ} (hp : p.Prime) (hp5 : p % 5 = 1 ∨ p % 5 = 4) {π : ZGold}
    (hπ : Prime π) (hπp : π ∣ (p : ZGold)) : (norm π).natAbs = p := by
  obtain ⟨p', hp', hπp', hcase⟩ := qa_prime_cases hπ
  have hpp' : p' = p := eq_of_prime_dvd_nat_prime hπ hp' hp hπp' hπp
  subst hpp'
  rcases hcase with h | h
  · exact h
  · exfalso
    have h2 := qa_natAbs_norm_eq_of_associated h
    simp only [QuadraticAlgebra.norm_natCast, Int.natAbs_pow, Int.natAbs_natCast] at h2
    rcases gold_prime_iff.1 (h.prime hπ) with h' | ⟨q, hq, hq5, h'⟩ | ⟨r, hr, -, h'⟩
    · have h3 := qa_natAbs_norm_eq_of_associated h'
      rw [gold_natAbs_norm_sqrtFive, QuadraticAlgebra.norm_natCast] at h3
      simp only [Int.natAbs_pow, Int.natAbs_natCast] at h3
      have : p' ∣ 5 := ⟨p', by rw [← h3]; ring⟩
      have := (Nat.prime_dvd_prime_iff_eq hp' Nat.prime_five).1 this
      omega
    · have h3 := qa_natAbs_norm_eq_of_associated h'
      simp only [QuadraticAlgebra.norm_natCast, Int.natAbs_pow, Int.natAbs_natCast] at h3
      have := Nat.pow_left_injective (n := 2) (by norm_num) h3
      subst this; omega
    · rw [QuadraticAlgebra.norm_natCast] at h'
      simp only [Int.natAbs_pow, Int.natAbs_natCast] at h'
      rw [← h', sq] at hr
      rcases Nat.prime_mul_iff.1 hr with ⟨-, h1⟩ | ⟨-, h1⟩ <;> exact hp'.one_lt.ne' h1

/-- **Theorem 258**, (15.4.7): if `π ∣ p` (`p` a rational prime `5n ± 1`), `(a, π) = 1` and
`(a, π̄) = 1`, then `a^(p-1) ≡ 1 (mod p)`. -/
@[kb "hardywright2008" "Thm 258, p. 307"]
theorem gold_fermat_p' {p : ℕ} (hp : p.Prime) (hp5 : p % 5 = 1 ∨ p % 5 = 4) {π a : ZGold}
    (hπ : Prime π) (hπp : π ∣ (p : ZGold)) (ha : ¬ π ∣ a) (ha' : ¬ star π ∣ a) :
    (p : ZGold) ∣ a ^ (p - 1) - 1 := by
  have := Fact.mk hp
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have hNπ := gold_natAbs_norm_of_dvd hp hp5 hπ hπp
  have hsπ : Prime (star π) := gold_prime_of_natAbs_norm_prime (by
    rw [QuadraticAlgebra.norm_star, hNπ]; exact hp)
  -- `p = ±π π̄`, so `(a, p) = 1`
  have hpdvd : (p : ZGold) ∣ π * star π := by
    rw [← algebraMap_norm_eq_mul_star]
    rcases Int.natAbs_eq (norm π) with h | h
    · rw [h, hNπ]; exact dvd_rfl
    · rw [h, hNπ]; exact ⟨-1, by simp⟩
  have hcop : IsCoprime (p : ZGold) a := by
    refine isCoprime_of_prime_dvd (fun h ↦ hp.ne_zero (by exact_mod_cast h.1))
      fun r hr hrp hra ↦ ?_
    rcases hr.dvd_or_dvd (dvd_trans hrp hpdvd) with h | h
    · exact ha ((hr.associated_of_dvd hπ h).dvd_iff_dvd_left.1 hra)
    · exact ha' ((hr.associated_of_dvd hsπ h).dvd_iff_dvd_left.1 hra)
  have h := (gold_dvd_pow_sub hp2 a).1 hp5
  have e : a ^ p - a = a * (a ^ (p - 1) - 1) := by
    conv_lhs => rw [show p = p - 1 + 1 by have := hp.two_le; omega, pow_succ]
    ring
  rw [e] at h
  exact hcop.dvd_of_dvd_mul_left h

/-- An integer not divisible by `2` has odd norm. -/
lemma gold_norm_odd {a : ZGold} (ha : ¬ (2 : ZGold) ∣ a) : (2 : ZGold) ∣ ((norm a : ℤ) : ZGold) - 1 := by
  obtain ⟨e, f⟩ := a
  have hnot : ¬ (2 ∣ e ∧ 2 ∣ f) := by
    rintro ⟨⟨e', rfl⟩, ⟨f', rfl⟩⟩
    exact ha ⟨⟨e', f'⟩, by ext <;> simp⟩
  have hN : (e ^ 2 + e * f - f ^ 2) % 2 = 1 := by
    rcases Int.emod_two_eq_zero_or_one e with he | he <;>
      rcases Int.emod_two_eq_zero_or_one f with hf | hf
    · exact absurd ⟨Int.dvd_of_emod_eq_zero he, Int.dvd_of_emod_eq_zero hf⟩ hnot
    all_goals
      have h1 : e ^ 2 % 2 = e % 2 := by rw [sq, Int.mul_emod, he]; norm_num
      have h2 : f ^ 2 % 2 = f % 2 := by rw [sq, Int.mul_emod, hf]; norm_num
      have h3 : e * f % 2 = (e % 2) * (f % 2) % 2 := Int.mul_emod _ _ _
      rw [he, hf] at h3
      norm_num at h3
      omega
  obtain ⟨k, hk⟩ : ∃ k, e ^ 2 + e * f - f ^ 2 = 2 * k + 1 := ⟨(e ^ 2 + e * f - f ^ 2) / 2, by omega⟩
  rw [gold_norm_mk, hk]
  exact ⟨k, by push_cast; ring⟩

/-- **Theorem 258**, (15.4.4): if `π` is a prime of `k(√5)` other than `√5` (up to associates),
`φ(π) = |Nπ| - 1` and `(a, π) = 1`, then `a^φ(π) ≡ 1 (mod π)`. -/
@[kb "hardywright2008" "Thm 258, p. 307"]
theorem gold_fermat {π a : ZGold} (hπ : Prime π) (h5 : ¬ Associated π sqrtFive) (ha : ¬ π ∣ a) :
    π ∣ a ^ ((norm π).natAbs - 1) - 1 := by
  rcases gold_prime_iff.1 hπ with h | ⟨q, hq, hq5, h⟩ | ⟨p, hp, hp5, h⟩
  · exact absurd h h5
  · have hn : (norm π).natAbs = q ^ 2 := by
      rw [qa_natAbs_norm_eq_of_associated h, QuadraticAlgebra.norm_natCast]
      simp [Int.natAbs_pow]
    rw [hn]
    have hqa : ¬ (q : ZGold) ∣ a := fun hd ↦ ha (dvd_trans h.dvd hd)
    by_cases hq2 : q = 2
    · subst hq2
      -- `a³ ≡ Na ≡ 1 (mod 2)`
      have h1 := gold_fermat_q hq hq5 a
      have hodd := gold_norm_odd (a := a) (by exact_mod_cast hqa)
      have : (2 : ZGold) ∣ a ^ (2 ^ 2 - 1) - 1 := by
        convert dvd_add h1 hodd using 1
        push_cast; ring
      exact dvd_trans h.dvd (by exact_mod_cast this)
    · have := Fact.mk hq
      -- `a^q ≡ ā`, so `a^(q²) ≡ a (mod q)`
      have hstar : ∀ y : ZGold, (q : ZGold) ∣ y ^ q - star y :=
        fun y ↦ (gold_dvd_pow_sub hq2 y).2 hq5
      have h1 : (q : ZGold) ∣ (a ^ q) ^ q - (star a) ^ q :=
        dvd_trans (hstar a) (sub_dvd_pow_sub_pow _ _ _)
      have h2 := hstar (star a)
      rw [star_star] at h2
      have h3 : (q : ZGold) ∣ a ^ (q ^ 2) - a := by
        rw [sq, pow_mul]
        convert dvd_add h1 h2 using 1
        ring
      have e : a ^ (q ^ 2) - a = a * (a ^ (q ^ 2 - 1) - 1) := by
        conv_lhs => rw [show q ^ 2 = q ^ 2 - 1 + 1 by have := Nat.one_le_pow 2 q hq.pos; omega, pow_succ]
        ring
      rw [e] at h3
      exact (hπ.dvd_or_dvd (dvd_trans h.dvd h3)).resolve_left ha
  · have hπp : π ∣ (p : ZGold) := by
      have := qa_dvd_natAbs_norm π
      rwa [h, Int.cast_natCast] at this
    rw [h]
    exact gold_fermat_p hp hp5 hπ hπp ha

end NTKB.HardyWright
