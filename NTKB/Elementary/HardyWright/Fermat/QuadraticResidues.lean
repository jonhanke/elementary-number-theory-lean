/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic.NormNum.Prime
import NTKB.Attr

/-!
# Quadratic residues of small numbers and the least non-residue (Hardy–Wright, §§ 6.7, 6.11, 6.13)

* Theorem 96: `-3` is a quadratic residue of primes `6n + 1` and a non-residue of primes `6n + 5`.
* Theorem 97: `5` is a quadratic residue of primes `10n ± 1` and a non-residue of primes `10n ± 3`.
  (The machine-read text of the book prints "7"; the book's proof in § 6.13 treats `5`, and the
  statement with `7` is false, e.g. `7` is not a residue of `11`.)
* Note to § 6.7: the least positive quadratic non-residue `q` of an odd prime `p` satisfies
  `q² < p + q`.
-/

namespace NTKB.HardyWright

open ZMod

private lemma not_isSquare_two_zmod_three : ¬IsSquare ((2 : ℤ) : ZMod 3) := by decide

private lemma squares_zmod_five : IsSquare (1 : ZMod 5) ∧ ¬IsSquare (2 : ZMod 5) ∧
    ¬IsSquare (3 : ZMod 5) ∧ IsSquare (4 : ZMod 5) := by decide

/-- **Theorem 96** [hardywright2008]: for a prime `p > 3`, `-3` is a quadratic residue of `p` if and
only if `p` has the form `6n + 1` (so it is a non-residue of the primes `6n + 5`). Hardy and Wright
use Gauss's lemma; here the value `(-3/p) = (p/3)` comes from the law of reciprocity. -/
@[kb "hardywright2008" "Thm 96, p. 95"]
theorem isSquare_neg_three_iff {p : ℕ} [hp : Fact p.Prime] (hp3 : 3 < p) :
    IsSquare (-3 : ZMod p) ↔ p % 6 = 1 := by
  have hp2 : p ≠ 2 := by omega
  have hodd : p % 2 = 1 := Nat.odd_iff.1 (hp.out.odd_of_ne_two hp2)
  have h3 : ((-3 : ℤ) : ZMod p) ≠ 0 := by
    rw [Int.cast_neg, neg_ne_zero, Ne, show ((3 : ℤ) : ZMod p) = ((3 : ℕ) : ZMod p) by simp,
      ZMod.natCast_eq_zero_iff]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).1 h
    omega
  have hp3' : p % 3 ≠ 0 := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp.out).1 (Nat.dvd_of_mod_eq_zero h)
    omega
  have h2 := not_isSquare_two_zmod_three
  -- `(-3/p) = (-1/p)(3/p) = (-1)^{(p-1)/2} (-1)^{(p-1)/2} (p/3) = (p/3)`
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hval : legendreSym p (-3) = legendreSym 3 p := by
    rw [legendreSym.at_neg hp2, show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num,
      legendreSym.quadratic_reciprocity' (by norm_num : 3 ≠ 2) hp2,
      ZMod.χ₄_nat_eq_if_mod_four, if_neg (by omega)]
    have : (3 : ℕ) / 2 * (p / 2) = p / 2 := by omega
    rw [this]
    rcases Nat.even_or_odd (p / 2) with h | h
    · rw [h.neg_one_pow, if_pos (by have := Nat.even_iff.1 h; omega)]; ring
    · rw [h.neg_one_pow, if_neg (by have := Nat.odd_iff.1 h; omega)]; ring
  rw [show (-3 : ZMod p) = ((-3 : ℤ) : ZMod p) by simp, ← legendreSym.eq_one_iff p h3, hval,
    legendreSym.mod 3 p]
  rcases (by omega : p % 3 = 1 ∨ p % 3 = 2) with h | h
  · have : (p : ℤ) % ((3 : ℕ) : ℤ) = 1 := by omega
    rw [this, legendreSym.at_one]
    simp only [true_iff]
    omega
  · have : (p : ℤ) % ((3 : ℕ) : ℤ) = 2 := by omega
    have h2 : legendreSym 3 2 = -1 := (legendreSym.eq_neg_one_iff 3).2 h2
    rw [this, h2]
    constructor
    · intro h; exact absurd h (by norm_num)
    · intro h'; omega

/-- **Theorem 96** [hardywright2008], as stated: `-3` is a residue of the primes `6n + 1` and a
non-residue of the primes `6n + 5`. -/
@[kb "hardywright2008" "Thm 96, p. 95"]
theorem isSquare_neg_three_of_mod_six {p : ℕ} [Fact p.Prime] (hp3 : 3 < p) :
    (p % 6 = 1 → IsSquare (-3 : ZMod p)) ∧ (p % 6 = 5 → ¬IsSquare (-3 : ZMod p)) := by
  rw [isSquare_neg_three_iff hp3]
  exact ⟨id, fun h h' ↦ by omega⟩

/-- **Theorem 97** [hardywright2008] (with `5`, as proved in § 6.13): for an odd prime `p ≠ 5`,
`5` is a quadratic residue of `p` if and only if `p` has the form `10n ± 1`. -/
@[kb "hardywright2008" "Thm 97, p. 95"]
theorem isSquare_five_iff {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    IsSquare (5 : ZMod p) ↔ p % 10 = 1 ∨ p % 10 = 9 := by
  have hsq := squares_zmod_five
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  -- `(5/p) = (p/5)` since `5 ≡ 1 (mod 4)`, and the residues of `5` are `1` and `4`
  have := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 5) (q := p) (by norm_num) hp2
  rw [show ((5 : ℕ) : ZMod p) = 5 by norm_num] at this
  rw [← this, ← ZMod.natCast_mod]
  have hodd : p % 2 = 1 := Nat.odd_iff.1 (hp.out.odd_of_ne_two hp2)
  have h50 : p % 5 ≠ 0 := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp.out).1 (Nat.dvd_of_mod_eq_zero h)
    omega
  have : p % 5 < 5 := Nat.mod_lt _ (by norm_num)
  interval_cases h : p % 5
  · omega
  · rw [Nat.cast_one]; exact ⟨fun _ ↦ by omega, fun _ ↦ hsq.1⟩
  · rw [Nat.cast_ofNat]; exact ⟨fun h' ↦ absurd h' hsq.2.1, fun h' ↦ by omega⟩
  · rw [Nat.cast_ofNat]; exact ⟨fun h' ↦ absurd h' hsq.2.2.1, fun h' ↦ by omega⟩
  · rw [Nat.cast_ofNat]; exact ⟨fun _ ↦ by omega, fun _ ↦ hsq.2.2.2⟩

/-- The note to § 6.7 [hardywright2008]: the least positive quadratic non-residue `q` of an odd
prime `p` satisfies `q² < p + q`. -/
@[kb "hardywright2008" "§ 6.7 notes, p. 101"]
theorem sq_lt_add_of_least_nonresidue {p q : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hq0 : 0 < q)
    (hq : ¬IsSquare (q : ZMod p)) (hmin : ∀ r, 0 < r → r < q → IsSquare (r : ZMod p)) :
    q ^ 2 < p + q := by
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  -- `q < p` and `q ≥ 2`
  have hqp0 : q % p ≠ 0 := by
    intro h
    apply hq
    rw [← ZMod.natCast_mod, h, Nat.cast_zero]
    exact ⟨0, by simp⟩
  have hqp : q < p := by
    by_contra h
    push Not at h
    apply hq
    rw [← ZMod.natCast_mod]
    exact hmin _ (Nat.pos_of_ne_zero hqp0) (lt_of_lt_of_le (Nat.mod_lt _ (by omega)) h)
  have hq2 : 2 ≤ q := by
    by_contra h
    have : q = 1 := by omega
    exact hq (this ▸ ⟨1, by simp⟩)
  -- `m = [p/q] + 1` satisfies `p < m q < p + q`
  obtain ⟨m, hm_def⟩ : ∃ m, m = p / q + 1 := ⟨_, rfl⟩
  have hdiv := Nat.div_add_mod p q
  have hpq0 : p % q ≠ 0 := by
    intro h
    have hd : q ∣ p := Nat.dvd_of_mod_eq_zero h
    rcases (Nat.dvd_prime hp.out).1 hd with h1 | h1 <;> omega
  have hpq : p % q < q := Nat.mod_lt _ (by omega)
  have hmq : m * q = p + (q - p % q) := by
    rw [hm_def, add_mul, one_mul, mul_comm]; omega
  -- `m q - p` is a positive number below `q`, hence a residue, and so is `m q`
  have hres : IsSquare ((m * q : ℕ) : ZMod p) := by
    have := hmin (q - p % q) (by omega) (by omega)
    rw [hmq, Nat.cast_add, ZMod.natCast_self, zero_add]
    exact this
  -- `m` is prime to `p`, and is a non-residue (Theorem 85)
  have hm0 : (m : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have := Nat.le_of_dvd (by rw [hm_def]; exact Nat.succ_pos _) hd
    have : p / q ≤ p / 2 := Nat.div_le_div_left hq2 (by norm_num)
    omega
  have hq0' : (q : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd; exact hqp0 (Nat.mod_eq_zero_of_dvd hd)
  have hmnr : ¬IsSquare (m : ZMod p) := by
    intro hms
    have h1 : legendreSym p m = 1 := (legendreSym.eq_one_iff' p hm0).2 hms
    have h2 : legendreSym p q = -1 := (legendreSym.eq_neg_one_iff' p).2 hq
    have h3 : legendreSym p ((m * q : ℕ) : ℤ) = 1 :=
      (legendreSym.eq_one_iff' p (by rw [Nat.cast_mul]; exact mul_ne_zero hm0 hq0')).2 hres
    rw [Nat.cast_mul, legendreSym.mul, h1, h2] at h3
    norm_num at h3
  -- hence `q ≤ m`, i.e. `q (q - 1) ≤ p`, with equality impossible
  have hqm : q ≤ m := by
    by_contra h
    push Not at h
    exact hmnr (hmin m (by rw [hm_def]; exact Nat.succ_pos _) h)
  have hle : q * (q - 1) ≤ p := by
    have : q - 1 ≤ p / q := by omega
    calc q * (q - 1) ≤ q * (p / q) := Nat.mul_le_mul_left q this
      _ ≤ p := Nat.mul_div_le p q
  have hne : q * (q - 1) ≠ p := by
    intro h
    have hd : q ∣ p := ⟨q - 1, h.symm⟩
    rcases (Nat.dvd_prime hp.out).1 hd with h1 | h1 <;> omega
  have : q * (q - 1) < p := lt_of_le_of_ne hle hne
  have e : q ^ 2 = q * (q - 1) + q := by
    rw [sq, Nat.mul_sub, mul_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_left q (by omega))]
  omega

end NTKB.HardyWright
