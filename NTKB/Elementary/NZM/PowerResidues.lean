/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Attr
import NTKB.IrelandRosen.R1.PowerResidues
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Congruences, power residues, quadratic reciprocity applications (Niven–Zuckerman–Montgomery)

* Theorem 2.3 (part C): `x ≡ y (mod m_i)` for all `i` iff `x ≡ y (mod [m_1, …, m_r])`.
* Lemma 2.22: if `k k' ≡ 1 (mod φ(m))` and `(a, m) = 1` then `a^(k k') ≡ a (mod m)`.
* Definition 2.8: `n`-th power residues modulo `p`; with Theorem 2.37 as a criterion
  (`a` is an `n`-th power residue mod a prime `p` iff `a^((p-1)/(n,p-1)) ≡ 1`).
* Theorem 2.45: if `a, b` have order `2^j` modulo a prime then `ab` has order `2^j'`, `j' < j`.
* Theorem 3.5: for an odd prime `p` and a prime `q > p`, `(p/q) = (r/p)` with `r` the reduction of
  `q` modulo `p` (resp. `4p`).
-/

namespace NTKB.NZM

/-- **Theorem 2.3, part C.** `x ≡ y (mod m_i)` for every `i` in a finite index set iff
`x ≡ y (mod [m_i])`, the least common multiple of the `m_i`. (Stated for arbitrary integer
moduli; the book assumes them positive.) -/
@[kb "nivenzuckermanmontgomery" "Thm 2.3, p. 49"]
theorem modEq_finset_lcm_iff {ι : Type*} (s : Finset ι) (m : ι → ℤ) (x y : ℤ) :
    (∀ i ∈ s, x ≡ y [ZMOD m i]) ↔ x ≡ y [ZMOD s.lcm m] := by
  simp only [Int.modEq_iff_dvd, Finset.lcm_dvd_iff]

/-- **Lemma 2.22.** If `m > 0`, `(a, m) = 1`, and `k, k'` are positive integers with
`k k' ≡ 1 (mod φ(m))`, then `a^(k k') ≡ a (mod m)`. -/
@[kb "nivenzuckermanmontgomery" "Lemma 2.22, p. 84"]
theorem pow_mul_modEq_self {m : ℕ} (hm : 0 < m) {a : ℤ} (ha : Int.gcd a m = 1) {k k' : ℕ}
    (hk : 0 < k) (hk' : 0 < k') (hkk : k * k' ≡ 1 [MOD Nat.totient m]) :
    a ^ (k * k') ≡ a [ZMOD m] := by
  have : NeZero m := ⟨hm.ne'⟩
  have hcop : IsCoprime a (m : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr ha
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : ((u : ZMod m)) * (a : ZMod m) = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod m) huv
    simpa using this
  have hunit : IsUnit (a : ZMod m) :=
    ⟨⟨(a : ZMod m), (u : ZMod m), by rw [mul_comm]; exact h1, h1⟩, rfl⟩
  obtain ⟨x, hx⟩ := hunit
  have hN : 1 ≤ k * k' := Nat.mul_pos hk hk'
  obtain ⟨r, hr⟩ : Nat.totient m ∣ k * k' - 1 :=
    (Nat.modEq_iff_dvd' hN).mp hkk.symm
  have hkr : k * k' = Nat.totient m * r + 1 := Nat.eq_add_of_sub_eq hN hr
  have h3 : x ^ (k * k') = x := by
    rw [hkr, pow_succ, pow_mul, ZMod.pow_totient, one_pow, one_mul]
  have h4 : ((a ^ (k * k') : ℤ) : ZMod m) = ((a : ℤ) : ZMod m) := by
    push_cast
    rw [← hx, ← Units.val_pow_eq_pow_val, h3]
  exact (ZMod.intCast_eq_intCast_iff _ _ m).mp h4

/-- **Definition 2.8.** If `(a, p) = 1` and `x^n ≡ a (mod p)` has a solution then `a` is called an
`n`-th power residue modulo `p`. -/
@[kb "nivenzuckermanmontgomery" "Def 2.8, p. 100"]
def IsPowerResidue (n p : ℕ) (a : ℤ) : Prop :=
  Int.gcd a p = 1 ∧ ∃ x : ℤ, x ^ n ≡ a [ZMOD p]

theorem gcd_eq_one_iff_not_dvd {p : ℕ} (hp : p.Prime) (a : ℤ) :
    Int.gcd a p = 1 ↔ ¬ (p : ℤ) ∣ a := by
  rw [← Int.isCoprime_iff_gcd_eq_one, ← (Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd]
  exact ⟨IsCoprime.symm, IsCoprime.symm⟩

/-- **Theorem 2.37** (solvability criterion): for a prime `p`, `n ≥ 1` and `(a, p) = 1`,
`a` is an `n`-th power residue mod `p` iff `a^((p-1)/(n,p-1)) ≡ 1 (mod p)`. -/
@[kb "nivenzuckermanmontgomery" "Thm 2.37, p. 101"]
theorem isPowerResidue_iff_pow_eq_one (p : ℕ) [hp : Fact p.Prime] {n : ℕ} (hn : n ≠ 0) {a : ℤ}
    (ha : Int.gcd a p = 1) :
    IsPowerResidue n p a ↔ a ^ ((p - 1) / Nat.gcd n (p - 1)) ≡ 1 [ZMOD p] := by
  have hne : (a : ZMod p) ≠ 0 := by
    intro h
    exact (gcd_eq_one_iff_not_dvd hp.out a).mp ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h)
  have key : (∃ x : ℤ, x ^ n ≡ a [ZMOD p]) ↔ ∃ y : ZMod p, y ^ n = (a : ZMod p) := by
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨(x : ZMod p), ?_⟩
      have := (ZMod.intCast_eq_intCast_iff _ _ p).mpr hx
      push_cast at this
      exact this
    · rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := ZMod.intCast_surjective y
      refine ⟨x, ?_⟩
      rw [← ZMod.intCast_eq_intCast_iff]
      push_cast
      exact hy
  have h2 := NTKB.IrelandRosen.exists_pow_eq_iff_finiteField (F := ZMod p) hne hn
  rw [Nat.card_zmod] at h2
  simp only [IsPowerResidue, ha, true_and]
  rw [key, h2]
  constructor
  · intro h
    refine (ZMod.intCast_eq_intCast_iff (a ^ ((p - 1) / Nat.gcd n (p - 1))) 1 p).mp ?_
    push_cast
    exact h
  · intro h
    have := (ZMod.intCast_eq_intCast_iff _ _ p).mpr h
    push_cast at this
    exact this

/-- **Theorem 2.45.** If `a` and `b` (necessarily nonzero) both have order `2^j` modulo a prime `p`,
with `j > 0`, then `ab` has order `2^j'` for some `j' < j`. -/
@[kb "nivenzuckermanmontgomery" "Thm 2.45, p. 111"]
theorem exists_orderOf_mul_two_pow_lt (p : ℕ) [Fact p.Prime] {a b : ZMod p} {j : ℕ} (hj : 0 < j)
    (ha : orderOf a = 2 ^ j) (hb : orderOf b = 2 ^ j) :
    ∃ j' < j, orderOf (a * b) = 2 ^ j' := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have key : ∀ c : ZMod p, orderOf c = 2 ^ (i + 1) → c ^ (2 ^ i) = -1 := by
    intro c hc
    have h2 : (c ^ (2 ^ i)) * (c ^ (2 ^ i)) = 1 := by
      rw [← pow_add, ← two_mul, ← pow_succ']
      exact orderOf_dvd_iff_pow_eq_one.mp (by simp [hc])
    rcases mul_self_eq_one_iff.mp h2 with h | h
    · exfalso
      have hd : orderOf c ∣ 2 ^ i := orderOf_dvd_iff_pow_eq_one.mpr h
      rw [hc] at hd
      have hle := Nat.le_of_dvd (by positivity) hd
      rw [pow_succ] at hle
      have hpos : 0 < 2 ^ i := by positivity
      omega
    · exact h
  have hab : (a * b) ^ (2 ^ i) = 1 := by
    rw [mul_pow, key a ha, key b hb]
    simp
  obtain ⟨k, hk, hk2⟩ :=
    (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_iff_pow_eq_one.mpr hab)
  exact ⟨k, Nat.lt_succ_of_le hk, hk2⟩

/-- **Theorem 3.5.** Let `p` be an odd prime and `q > p` a prime. If `p = 4n + 1`, let `q = kp + r`,
`0 < r < p`; if `p = 4n + 3`, let `r` be the unique number with `0 < r < 4p`, `r ≡ 1 (mod 4)` and
`q = 4kp + r` or `q = 4kp - r`. In both cases `(p/q) = (r/p)`. (Here `(p/q)` is
`legendreSym q p` and `(r/p)` is `legendreSym p r`; the book's "`q = 4kp + r`" in the second case
is read as `q = 4kp ± r`, as its proof does.) -/
@[kb "nivenzuckermanmontgomery" "Thm 3.5, p. 139"]
theorem legendreSym_eq_of_reduction (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hp2 : p ≠ 2)
    (hpq : p < q) (k : ℕ) (r : ℤ)
    (h : (p % 4 = 1 ∧ (q : ℤ) = k * p + r ∧ 0 < r ∧ r < p) ∨
      (p % 4 = 3 ∧ 0 < r ∧ r < 4 * p ∧ r % 4 = 1 ∧
        ((q : ℤ) = 4 * k * p + r ∨ (q : ℤ) = 4 * k * p - r))) :
    legendreSym q p = legendreSym p r := by
  have hp_two : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hq2 : q ≠ 2 := by omega
  rcases h with ⟨hp1, hq, -, -⟩ | ⟨hp3, -, -, hr4, hq | hq⟩
  · have hq' : (q : ℤ) = r + p * k := by rw [hq]; ring
    rw [legendreSym.quadratic_reciprocity_one_mod_four hp1 hq2,
      legendreSym.mod p (q : ℤ), legendreSym.mod p r, hq', Int.add_mul_emod_self_left]
  · have hq' : (q : ℤ) = r + p * (4 * k) := by rw [hq]; ring
    have hq4 : q % 4 = 1 := by
      have e : (q : ℤ) = r + 4 * ((k : ℤ) * p) := by rw [hq]; ring
      generalize (k : ℤ) * p = t at e
      omega
    rw [← legendreSym.quadratic_reciprocity_one_mod_four (p := q) (q := p) hq4 hp2,
      legendreSym.mod p (q : ℤ), legendreSym.mod p r, hq', Int.add_mul_emod_self_left]
  · have hq' : (q : ℤ) = -r + p * (4 * k) := by rw [hq]; ring
    have hq3 : q % 4 = 3 := by
      have e : (q : ℤ) = -r + 4 * ((k : ℤ) * p) := by rw [hq]; ring
      generalize (k : ℤ) * p = t at e
      omega
    have hmod : legendreSym p (q : ℤ) = legendreSym p (-r) := by
      rw [legendreSym.mod p (q : ℤ), legendreSym.mod p (-r), hq', Int.add_mul_emod_self_left]
    rw [legendreSym.quadratic_reciprocity_three_mod_four hp3 hq3, hmod,
      legendreSym.at_neg hp2, ZMod.χ₄_nat_three_mod_four hp3]
    ring

end NTKB.NZM
