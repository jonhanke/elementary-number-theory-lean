/-
Ireland–Rosen, Chapter 5: quadratic residues for every modulus, the primes for which `q` is a
residue, a nonsquare is a nonresidue for infinitely many primes, and Euler's form of the law of
quadratic reciprocity.
-/
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.NumberTheory.Basic
import NTKB.IrelandRosen.R1.PowerResidues
import NTKB.Attr

/-!
# Quadratic residues (Ireland–Rosen, Chapter 5)

* Proposition 5.1.1: for `(a, m) = 1`, `x^2 ≡ a (mod m)` is solvable iff `a ≡ 1 (mod 4)` when
  `4 ∥ m`, `a ≡ 1 (mod 8)` when `8 ∣ m`, and `a^((p-1)/2) ≡ 1 (mod p)` for every odd prime
  `p ∣ m` (`isSquare_intCast_zmod_iff`).
* §5.2, Theorem 2: the primes `p` for which an odd prime `q` is a quadratic residue
  (`isSquare_prime_iff_of_mod_four_eq_one`, `isSquare_prime_iff_of_mod_four_eq_three`).
* §5.2, the lemma on odd `r, s` and its corollary for odd `r_1, …, r_m`.
* §5.2, Theorem 3: a nonsquare integer is a nonresidue for infinitely many primes
  (`infinite_setOf_not_isSquare`), from reciprocity and Dirichlet's theorem on primes in
  progressions (Mathlib's `Nat.setOf_prime_and_eq_mod_infinite`).
* Proposition 5.3.3: the law of quadratic reciprocity is equivalent to Euler's form, "`p ≡ ±q`
  (mod `4a`) implies `(a/p) = (a/q)`" (`reciprocityLaw_iff_eulerForm`); Euler's form holds
  (`eulerForm`).

A quadratic nonresidue mod `p` is an `a` with `p ∤ a` that is not a square mod `p`; for an integer
`a`, `¬ IsSquare (a : ZMod p)` already forces `p ∤ a` (`0` is a square), so Theorem 3 is stated with
`¬ IsSquare`.
-/

namespace NTKB.IrelandRosen

open Finset

/-! ### Proposition 5.1.1 -/

/-- Squares modulo a power of two. -/
private lemma isSquare_two_pow {n : ℕ} (hn : 0 < n) {x : ℤ} (hx : IsCoprime x (2 ^ n : ℕ)) :
    IsSquare (x : ZMod (2 ^ n)) ↔ (n = 2 → x ≡ 1 [ZMOD 4]) ∧ (3 ≤ n → x ≡ 1 [ZMOD 8]) := by
  have hx2 : Odd x := by
    have h2 : IsCoprime x 2 := by
      have : IsCoprime x ((2 : ℤ) ^ n) := by exact_mod_cast hx
      exact IsCoprime.of_isCoprime_of_dvd_right this (dvd_pow_self 2 hn.ne')
    rw [← Int.not_even_iff_odd, even_iff_two_dvd]
    intro hd
    have := h2.isUnit_of_dvd' hd dvd_rfl
    rw [Int.isUnit_iff] at this
    omega
  have hsq8 : ∀ z : ℤ, Odd z → z * z % 8 = 1 := by
    intro z hz
    obtain ⟨k, rfl⟩ := hz
    obtain ⟨j, hj⟩ := Int.even_mul_succ_self k
    have : (2 * k + 1) * (2 * k + 1) = 1 + 8 * j := by linarith [hj, show (2 * k + 1) * (2 * k + 1) = 1 + 4 * (k * (k + 1)) by ring]
    rw [this, Int.add_mul_emod_self_left]; norm_num
  have sq_of : x ≡ 1 [ZMOD ((2 ^ n : ℕ) : ℤ)] → IsSquare (x : ZMod (2 ^ n)) := fun h =>
    ⟨1, by
      have := (ZMod.intCast_eq_intCast_iff _ _ _).mpr h
      rw [mul_one]; simpa using this⟩
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := ZMod.intCast_surjective y
    have hmod : x ≡ z * z [ZMOD ((2 ^ n : ℕ) : ℤ)] :=
      (ZMod.intCast_eq_intCast_iff x (z * z) (2 ^ n)).mp (by push_cast; exact hy)
    have hzodd : Odd z := by
      by_contra hz
      rw [Int.not_odd_iff_even] at hz
      have h2 : x ≡ z * z [ZMOD 2] := Int.ModEq.of_dvd (by exact_mod_cast dvd_pow_self 2 hn.ne') hmod
      have he : Even (z * z) := hz.mul_right _
      rw [Int.even_iff] at he
      have := Int.odd_iff.mp hx2
      unfold Int.ModEq at h2
      omega
    have h8 := hsq8 z hzodd
    refine ⟨fun h2 => ?_, fun h3 => ?_⟩
    · subst h2
      have h4 : x ≡ z * z [ZMOD 4] := by simpa using hmod
      unfold Int.ModEq at h4 ⊢
      omega
    · have h4 : x ≡ z * z [ZMOD 8] :=
        Int.ModEq.of_dvd (by exact_mod_cast pow_dvd_pow 2 h3) hmod
      unfold Int.ModEq at h4 ⊢
      omega
  · rintro ⟨h2, h3⟩
    rcases Nat.lt_or_ge n 3 with hlt | hge
    · apply sq_of
      interval_cases n
      · have := Int.odd_iff.mp hx2
        unfold Int.ModEq
        simp
        omega
      · have := h2 rfl
        simpa using this
    · obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
      have h8 := h3 hge
      rw [isSquare_iff_exists_sq]
      have key := exists_pow_eq_iff_of_even (e := j + 3) hge hx2 (n := 2) (by norm_num)
        (by norm_num)
      have e1 : 2 ^ (j + 3 - 2) = 2 ^ j * 2 := by
        rw [show j + 3 - 2 = j + 1 by omega, pow_succ]
      rw [e1, Nat.gcd_eq_left (dvd_mul_left 2 _), Nat.mul_div_cancel _ (by norm_num)] at key
      have hdvd : (2 : ℤ) ^ 3 ∣ x - 1 := by
        have := (Int.modEq_iff_dvd.mp h8.symm)
        simpa using this
      have hpow := two_pow_dvd_pow_two_pow_sub_one (by norm_num) hdvd j
      obtain ⟨y, hy⟩ := key.mpr ⟨Int.ModEq.of_dvd (by norm_num : (4 : ℤ) ∣ 8) h8, by
        rw [intCast_pow_eq_one_iff]
        rw [add_comm 3 j] at hpow
        push_cast
        exact hpow⟩
      exact ⟨y, hy.symm⟩

/-- Squares modulo an odd prime power. -/
private lemma isSquare_odd_prime_pow {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 0 < n) {x : ℤ}
    (hx : IsCoprime x (p ^ n : ℕ)) :
    IsSquare (x : ZMod (p ^ n)) ↔ x ^ ((p - 1) / 2) ≡ 1 [ZMOD p] := by
  have := Fact.mk hp
  have := ZMod.isCyclic_units_of_prime_pow p hp hp2 n
  have : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have h := exists_pow_eq_iff_of_isCyclic_units (m := p ^ n) (a := x) hx.symm (n := 2)
    two_ne_zero
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨c, hc⟩ : ∃ c, p - 1 = 2 * c := by
    obtain ⟨k, hk⟩ := hodd; exact ⟨k, by omega⟩
  have hc' : (p - 1) / 2 = c := by omega
  have htot : (p ^ n).totient = 2 * (p ^ (n - 1) * c) := by
    rw [Nat.totient_prime_pow hp hn, hc]; ring
  rw [htot, Nat.gcd_eq_left (dvd_mul_right 2 _), Nat.mul_div_cancel_left _ (by norm_num)] at h
  rw [hc']
  have e1 : IsSquare (x : ZMod (p ^ n)) ↔ ∃ y : ZMod (p ^ n), y ^ 2 = x := by
    rw [isSquare_iff_exists_sq]
    exact exists_congr fun y => eq_comm
  rw [e1, h, intCast_pow_eq_one_iff, Int.modEq_iff_dvd]
  constructor
  · intro hd
    have hd' : (p : ℤ) ∣ x ^ (p ^ (n - 1) * c) - 1 :=
      (by exact_mod_cast dvd_pow_self p hn.ne' : (p : ℤ) ∣ ((p ^ n : ℕ) : ℤ)).trans hd
    have key := (intCast_pow_eq_one_iff (m := p) (a := x) (k := p ^ (n - 1) * c)).mpr hd'
    rw [mul_comm, pow_mul, ZMod.pow_card_pow] at key
    exact dvd_sub_comm.mp (intCast_pow_eq_one_iff.mp key)
  · intro hd
    have := dvd_sub_pow_of_dvd_sub (R := ℤ) (p := p) (a := x ^ c) (b := 1)
      (by simpa using dvd_sub_comm.mp hd) (n - 1)
    rw [show n - 1 + 1 = n by omega, one_pow, ← pow_mul, mul_comm] at this
    simpa using this


private lemma isSquare_mul_coprime {m n : ℕ} (h : Nat.Coprime m n) (x : ℤ) :
    IsSquare (x : ZMod (m * n)) ↔ IsSquare (x : ZMod m) ∧ IsSquare (x : ZMod n) := by
  let φ := ZMod.chineseRemainder h
  have hφ : φ (x : ZMod (m * n)) = ((x : ZMod m), (x : ZMod n)) := by
    rw [map_intCast]; rfl
  constructor
  · rintro ⟨y, hy⟩
    have h1 := congrArg φ hy
    rw [hφ, map_mul] at h1
    exact ⟨⟨(φ y).1, congrArg Prod.fst h1⟩, ⟨(φ y).2, congrArg Prod.snd h1⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨φ.symm (a, b), φ.injective ?_⟩
    rw [hφ, map_mul, RingEquiv.apply_symm_apply, ha, hb]
    rfl

/-- The local condition at the prime `p`, whose exact power in the modulus is `p ^ k`. -/
private def Cond (p k : ℕ) (x : ℤ) : Prop :=
  (p = 2 → (k = 2 → x ≡ 1 [ZMOD 4]) ∧ (3 ≤ k → x ≡ 1 [ZMOD 8])) ∧
    (p ≠ 2 → x ^ ((p - 1) / 2) ≡ 1 [ZMOD p])

private lemma isSquare_prime_pow_iff {p n : ℕ} (hp : p.Prime) (hn : 0 < n) {x : ℤ}
    (hx : IsCoprime x (p ^ n : ℕ)) : IsSquare (x : ZMod (p ^ n)) ↔ Cond p n x := by
  by_cases hp2 : p = 2
  · subst hp2
    rw [isSquare_two_pow hn hx]
    unfold Cond
    simp
  · rw [isSquare_odd_prime_pow hp hp2 hn hx]
    unfold Cond
    simp [hp2]

private lemma isSquare_iff_cond {m : ℕ} (hm : m ≠ 0) {x : ℤ} (hx : IsCoprime x m) :
    IsSquare (x : ZMod m) ↔ ∀ p ∈ m.primeFactors, Cond p (m.factorization p) x := by
  revert x hx hm
  refine Nat.recOnPosPrimePosCoprime (motive := fun m => m ≠ 0 → ∀ x : ℤ, IsCoprime x m →
    (IsSquare (x : ZMod m) ↔ ∀ p ∈ m.primeFactors, Cond p (m.factorization p) x)) ?_ ?_ ?_ ?_ m
  · intro p n hp hn _ x hx
    rw [isSquare_prime_pow_iff hp hn hx, Nat.primeFactors_prime_pow hn.ne' hp]
    simp [hp.factorization_pow]
  · intro h; exact absurd rfl h
  · intro _ x _
    simp
    exact ⟨0, Subsingleton.elim (α := ZMod 1) _ _⟩
  · intro a b ha hb hab iha ihb _ x hx
    have ha0 : a ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    have hxa : IsCoprime x (a : ℤ) := by
      have : IsCoprime x ((a : ℤ) * b) := by exact_mod_cast hx
      exact this.of_mul_right_left
    have hxb : IsCoprime x (b : ℤ) := by
      have : IsCoprime x ((a : ℤ) * b) := by exact_mod_cast hx
      exact this.of_mul_right_right
    rw [isSquare_mul_coprime hab, iha ha0 x hxa, ihb hb0 x hxb, Nat.primeFactors_mul ha0 hb0]
    have hA : ∀ p ∈ a.primeFactors, (a * b).factorization p = a.factorization p := by
      intro p hp
      have hpa := Nat.dvd_of_mem_primeFactors hp
      have hpb : ¬ p ∣ b := fun hpb => (Nat.mem_primeFactors.mp hp).1.one_lt.ne'
        (Nat.eq_one_of_dvd_coprimes hab hpa hpb)
      rw [Nat.factorization_mul ha0 hb0, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hpb, add_zero]
    have hB : ∀ p ∈ b.primeFactors, (a * b).factorization p = b.factorization p := by
      intro p hp
      have hpb := Nat.dvd_of_mem_primeFactors hp
      have hpa : ¬ p ∣ a := fun hpa => (Nat.mem_primeFactors.mp hp).1.one_lt.ne'
        (Nat.eq_one_of_dvd_coprimes hab hpa hpb)
      rw [Nat.factorization_mul ha0 hb0, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hpa, zero_add]
    have eA : (∀ p ∈ a.primeFactors, Cond p ((a * b).factorization p) x) ↔
        (∀ p ∈ a.primeFactors, Cond p (a.factorization p) x) :=
      forall₂_congr fun p hp => by rw [hA p hp]
    have eB : (∀ p ∈ b.primeFactors, Cond p ((a * b).factorization p) x) ↔
        (∀ p ∈ b.primeFactors, Cond p (b.factorization p) x) :=
      forall₂_congr fun p hp => by rw [hB p hp]
    rw [← eA, ← eB]
    simp only [Finset.mem_union, or_imp, forall_and]

/-- **Ireland–Rosen, Proposition 5.1.1.** Let `m = 2^e p_1^{e_1} ⋯ p_l^{e_l}` and `(a, m) = 1`.
Then `x^2 ≡ a (mod m)` is solvable iff `a ≡ 1 (mod 4)` if `e = 2`, `a ≡ 1 (mod 8)` if `e ≥ 3`, and
`a^((p_i - 1)/2) ≡ 1 (mod p_i)` for each `i`. -/
@[kb "irelandrosen1990" "Proposition 5.1.1"]
theorem isSquare_intCast_zmod_iff {m : ℕ} (hm : m ≠ 0) {a : ℤ} (ha : IsCoprime a m) :
    IsSquare (a : ZMod m) ↔
      (m.factorization 2 = 2 → a ≡ 1 [ZMOD 4]) ∧ (3 ≤ m.factorization 2 → a ≡ 1 [ZMOD 8]) ∧
        ∀ p ∈ m.primeFactors, p ≠ 2 → a ^ ((p - 1) / 2) ≡ 1 [ZMOD p] := by
  rw [isSquare_iff_cond hm ha]
  unfold Cond
  have h2mem : 0 < m.factorization 2 → 2 ∈ m.primeFactors := fun h =>
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, Nat.dvd_of_factorization_pos h.ne', hm⟩
  constructor
  · intro h
    refine ⟨fun h2 => ((h 2 (h2mem (by omega))).1 rfl).1 h2,
      fun h3 => ((h 2 (h2mem (by omega))).1 rfl).2 h3, fun p hp hp2 => (h p hp).2 hp2⟩
  · rintro ⟨h1, h2, h3⟩ p hp
    refine ⟨?_, h3 p hp⟩
    rintro rfl
    exact ⟨h1, h2⟩

/-! ### §5.2, Theorem 2 -/

private lemma modEq_mul4 {q : ℕ} (hcop : IsCoprime (4 : ℤ) q) {x y : ℤ} (h4 : x ≡ y [ZMOD 4])
    (hq : x ≡ y [ZMOD q]) : x ≡ y [ZMOD 4 * q] := by
  rw [Int.modEq_iff_dvd] at *
  exact hcop.mul_dvd h4 hq

private lemma odd_sq_mod_four {b : ℤ} (hb : Odd b) : b ^ 2 % 4 = 1 := by
  obtain ⟨k, rfl⟩ := hb
  have : (2 * k + 1) ^ 2 = 1 + 4 * (k * k + k) := by ring
  rw [this, Int.add_mul_emod_self_left]
  norm_num

private lemma isSquare_neg_iff {q p : ℕ} [Fact q.Prime] (hq : q % 4 = 3) (hp0 : (p : ZMod q) ≠ 0) :
    IsSquare (-(p : ZMod q)) ↔ ¬ IsSquare (p : ZMod q) := by
  have hm1 : legendreSym q (-1) = -1 := by
    rw [legendreSym.eq_neg_one_iff]
    push_cast
    intro h
    exact (ZMod.exists_sq_eq_neg_one_iff.mp h) hq
  have h1 : legendreSym q (-(p : ℤ)) = -legendreSym q p := by
    rw [show -(p : ℤ) = -1 * p by ring, legendreSym.mul, hm1]; ring
  have h0 : ((-(p : ℤ) : ℤ) : ZMod q) ≠ 0 := by simpa using hp0
  have e1 := legendreSym.eq_one_iff (p := q) h0
  have e2 := legendreSym.eq_neg_one_iff' (p := q) (a := p)
  push_cast at e1
  rw [← e1, ← e2, h1]
  constructor <;> intro h <;> linarith

private lemma exists_odd_rep {q : ℕ} [NeZero q] (hq : Odd q) (c : ZMod q) :
    ∃ b : ℤ, Odd b ∧ (b : ZMod q) = c := by
  by_cases h : Odd (c.val : ℤ)
  · exact ⟨c.val, h, by simp⟩
  · refine ⟨(c.val : ℤ) + q, ?_, by simp⟩
    rw [Int.not_odd_iff_even] at h
    exact h.add_odd (by exact_mod_cast hq)

/-- **Ireland–Rosen, §5.2, Theorem 2 (first case).** For an odd prime `q ≡ 1 (mod 4)` and an odd
prime `p ≠ q`: `q` is a quadratic residue mod `p` iff `p ≡ r (mod q)` with `r` a quadratic residue
mod `q`. -/
@[kb "irelandrosen1990" "§5.2, Theorem 2 (q ≡ 1 mod 4)"]
theorem isSquare_prime_iff_of_mod_four_eq_one {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hq : q % 4 = 1) (hp : p ≠ 2) (hpq : p ≠ q) :
    IsSquare (q : ZMod p) ↔ ∃ r : ℕ, IsSquare (r : ZMod q) ∧ ¬ q ∣ r ∧ p ≡ r [MOD q] := by
  have hp' : p.Prime := Fact.out
  have hq' : q.Prime := Fact.out
  have hq2 : q ≠ 2 := by omega
  have hp0 : ¬ q ∣ p := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hq' hp').mp h).symm
  rw [← ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one hq hp]
  constructor
  · intro h
    exact ⟨p, h, hp0, Nat.ModEq.refl _⟩
  · rintro ⟨r, hr, -, hpr⟩
    have : (p : ZMod q) = (r : ZMod q) := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hpr
    rwa [this]

/-- **Ireland–Rosen, §5.2, Theorem 2 (second case).** For an odd prime `q ≡ 3 (mod 4)` and an odd
prime `p ≠ q`: `q` is a quadratic residue mod `p` iff `p ≡ ±b^2 (mod 4q)` for an odd integer `b`
prime to `q`. -/
@[kb "irelandrosen1990" "§5.2, Theorem 2 (q ≡ 3 mod 4)"]
theorem isSquare_prime_iff_of_mod_four_eq_three {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hq : q % 4 = 3) (hp : p ≠ 2) (hpq : p ≠ q) :
    IsSquare (q : ZMod p) ↔ ∃ b : ℤ, Odd b ∧ ¬ (q : ℤ) ∣ b ∧
      ((p : ℤ) ≡ b ^ 2 [ZMOD 4 * q] ∨ (p : ℤ) ≡ -b ^ 2 [ZMOD 4 * q]) := by
  have hp' : p.Prime := Fact.out
  have hq' : q.Prime := Fact.out
  have hq2 : q ≠ 2 := by omega
  have hp0 : ¬ q ∣ p := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hq' hp').mp h).symm
  have hpz : (p : ZMod q) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact hp0
  have hpo : Odd p := hp'.odd_of_ne_two hp
  have hqo : Odd q := hq'.odd_of_ne_two hq2
  have hcop : IsCoprime (4 : ℤ) q := by
    have : Nat.Coprime 4 q := by
      have : Nat.Coprime 2 q := Nat.coprime_two_left.mpr hqo
      simpa using Nat.Coprime.pow_left 2 this
    exact Nat.isCoprime_iff_coprime.mpr this
  -- the equivalence for `p`
  have key : IsSquare (q : ZMod p) ↔
      (p % 4 = 1 ∧ IsSquare (p : ZMod q)) ∨ (p % 4 = 3 ∧ IsSquare (-(p : ZMod q))) := by
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hpo) with h1 | h3
    · rw [ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one h1 hq2]
      constructor
      · exact fun h => Or.inl ⟨h1, h⟩
      · rintro (⟨-, h⟩ | ⟨h, -⟩)
        · exact h
        · omega
    · rw [ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three h3 hq hpq, ← isSquare_neg_iff hq hpz]
      constructor
      · exact fun h => Or.inr ⟨h3, h⟩
      · rintro (⟨h, -⟩ | ⟨-, h⟩)
        · omega
        · exact h
  rw [key]
  constructor
  · rintro (⟨h1, c, hc⟩ | ⟨h3, c, hc⟩)
    · obtain ⟨b, hb, hbc⟩ := exists_odd_rep hqo c
      have hbq : ¬ (q : ℤ) ∣ b := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hbc]
        rintro rfl
        exact hpz (by simpa using hc)
      refine ⟨b, hb, hbq, Or.inl (modEq_mul4 hcop ?_ ?_)⟩
      · have := odd_sq_mod_four hb
        unfold Int.ModEq
        generalize b ^ 2 = y at *
        omega
      · exact (ZMod.intCast_eq_intCast_iff _ _ q).mp (by push_cast; rw [hc, hbc]; ring)
    · obtain ⟨b, hb, hbc⟩ := exists_odd_rep hqo c
      have hbq : ¬ (q : ℤ) ∣ b := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hbc]
        rintro rfl
        exact hpz (by simpa using hc)
      refine ⟨b, hb, hbq, Or.inr (modEq_mul4 hcop ?_ ?_)⟩
      · have := odd_sq_mod_four hb
        unfold Int.ModEq
        generalize b ^ 2 = y at *
        omega
      · refine (ZMod.intCast_eq_intCast_iff _ _ q).mp ?_
        push_cast
        rw [← hbc] at hc
        linear_combination (-1 : ZMod q) * hc
  · rintro ⟨b, hb, hbq, h | h⟩
    · have h4 := Int.ModEq.of_dvd (⟨q, by ring⟩ : (4 : ℤ) ∣ 4 * q) h
      have hq3 := (ZMod.intCast_eq_intCast_iff _ _ q).mpr
        (Int.ModEq.of_dvd (⟨4, by ring⟩ : (q : ℤ) ∣ 4 * q) h)
      push_cast at hq3
      have hsq := odd_sq_mod_four hb
      unfold Int.ModEq at h4
      have hp1 : p % 4 = 1 := by
        generalize b ^ 2 = y at hsq h4
        omega
      exact Or.inl ⟨hp1, b, by rw [hq3]; ring⟩
    · have h4 := Int.ModEq.of_dvd (⟨q, by ring⟩ : (4 : ℤ) ∣ 4 * q) h
      have hq3 := (ZMod.intCast_eq_intCast_iff _ _ q).mpr
        (Int.ModEq.of_dvd (⟨4, by ring⟩ : (q : ℤ) ∣ 4 * q) h)
      push_cast at hq3
      have hsq := odd_sq_mod_four hb
      unfold Int.ModEq at h4
      have hp3 : p % 4 = 3 := by
        generalize b ^ 2 = y at hsq h4
        omega
      exact Or.inr ⟨hp3, b, by rw [hq3]; ring⟩

/-! ### §5.2, the lemma on odd `r, s` and its corollary -/

/-- **Ireland–Rosen, §5.2, Lemma (odd `r, s`).** For odd `r, s`:
`(rs - 1)/2 ≡ (r - 1)/2 + (s - 1)/2 (mod 2)` and
`(r^2 s^2 - 1)/8 ≡ (r^2 - 1)/8 + (s^2 - 1)/8 (mod 2)`. -/
@[kb "irelandrosen1990" "§5.2, Lemma (odd r, s)"]
theorem odd_mul_sub_one_div_two {r s : ℤ} (hr : Odd r) (hs : Odd s) :
    (r * s - 1) / 2 ≡ (r - 1) / 2 + (s - 1) / 2 [ZMOD 2] ∧
      (r ^ 2 * s ^ 2 - 1) / 8 ≡ (r ^ 2 - 1) / 8 + (s ^ 2 - 1) / 8 [ZMOD 2] := by
  obtain ⟨k, rfl⟩ := hr
  obtain ⟨l, rfl⟩ := hs
  constructor
  · have h : (2 * k + 1) * (2 * l + 1) - 1 = 2 * (2 * k * l + k + l) := by ring
    have h1 : (2 * k + 1 - 1) = 2 * k := by ring
    have h2 : (2 * l + 1 - 1) = 2 * l := by ring
    rw [h, h1, h2, Int.mul_ediv_cancel_left _ (by norm_num), Int.mul_ediv_cancel_left _ (by norm_num),
      Int.mul_ediv_cancel_left _ (by norm_num)]
    exact (Int.modEq_iff_dvd.mpr ⟨k * l, by ring⟩).symm
  · obtain ⟨i, hi⟩ := Int.even_mul_succ_self k
    obtain ⟨j, hj⟩ := Int.even_mul_succ_self l
    have h1 : (2 * k + 1) ^ 2 - 1 = 8 * (i) := by nlinarith
    have h2 : (2 * l + 1) ^ 2 - 1 = 8 * (j) := by nlinarith
    have h3 : (2 * k + 1) ^ 2 * (2 * l + 1) ^ 2 - 1 = 8 * (8 * i * j + i + j) := by
      have e1 : (2 * k + 1) ^ 2 = 8 * i + 1 := by linarith
      have e2 : (2 * l + 1) ^ 2 = 8 * j + 1 := by linarith
      rw [e1, e2]; ring
    rw [h1, h2, h3, Int.mul_ediv_cancel_left _ (by norm_num), Int.mul_ediv_cancel_left _ (by norm_num),
      Int.mul_ediv_cancel_left _ (by norm_num)]
    exact (Int.modEq_iff_dvd.mpr ⟨4 * i * j, by ring⟩).symm

/-- **Ireland–Rosen, §5.2, Corollary to the lemma on odd `r, s`.** For odd `r_1, …, r_m`:
`∑ (r_i - 1)/2 ≡ (r_1 ⋯ r_m - 1)/2 (mod 2)` and
`∑ (r_i^2 - 1)/8 ≡ (r_1^2 ⋯ r_m^2 - 1)/8 (mod 2)`. -/
@[kb "irelandrosen1990" "§5.2, Corollary (odd r_i)"]
theorem sum_odd_sub_one_div_two {ι : Type*} (S : Finset ι) (r : ι → ℤ) (hr : ∀ i ∈ S, Odd (r i)) :
    ∑ i ∈ S, (r i - 1) / 2 ≡ (∏ i ∈ S, r i - 1) / 2 [ZMOD 2] ∧
      ∑ i ∈ S, (r i ^ 2 - 1) / 8 ≡ (∏ i ∈ S, r i ^ 2 - 1) / 8 [ZMOD 2] := by
  classical
  have hodd : ∀ T : Finset ι, (∀ i ∈ T, Odd (r i)) → Odd (∏ i ∈ T, r i) := fun T hT =>
    Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one hT
  have key : ∀ T : Finset ι, (∀ i ∈ T, Odd (r i)) →
      ∑ i ∈ T, (r i - 1) / 2 ≡ (∏ i ∈ T, r i - 1) / 2 [ZMOD 2] ∧
      ∑ i ∈ T, (r i ^ 2 - 1) / 8 ≡ ((∏ i ∈ T, r i) ^ 2 - 1) / 8 [ZMOD 2] := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _; simp [Int.ModEq.refl]
    | insert a T ha ih =>
      intro hT
      have hTa : Odd (r a) := hT a (Finset.mem_insert_self _ _)
      have hT' : ∀ i ∈ T, Odd (r i) := fun i hi => hT i (Finset.mem_insert_of_mem hi)
      obtain ⟨ih1, ih2⟩ := ih hT'
      obtain ⟨l1, l2⟩ := odd_mul_sub_one_div_two hTa (hodd T hT')
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
      refine ⟨?_, ?_⟩
      · exact (Int.ModEq.add_left _ ih1).trans l1.symm
      · have : (r a * ∏ i ∈ T, r i) ^ 2 = r a ^ 2 * (∏ i ∈ T, r i) ^ 2 := by ring
        rw [this]
        exact (Int.ModEq.add_left _ ih2).trans l2.symm
  obtain ⟨k1, k2⟩ := key S hr
  exact ⟨k1, by rwa [Finset.prod_pow]⟩

/-! ### §5.2, Theorem 3 -/

/-- A residue `n` prime to `a'` with `(a'/n) = -1`, for `a'` squarefree and not `1`. -/
private lemma exists_jacobi_neg_one {a' : ℤ} (h0 : a' ≠ 0) (h1 : a' ≠ 1)
    (hsq : Squarefree a'.natAbs) :
    ∃ n : ℕ, Odd n ∧ Nat.Coprime n a'.natAbs ∧ jacobiSym a' n = -1 := by
  obtain ⟨k, c, hco, hc⟩ := Nat.exists_eq_two_pow_mul_odd (Int.natAbs_ne_zero.mpr h0)
  by_cases hc1 : c = 1
  · subst hc1
    have hk : k ≤ 1 := by
      by_contra hk
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      have h2 : 2 * 2 ∣ a'.natAbs := ⟨2 ^ j, by rw [hc]; ring⟩
      have := hsq 2 h2
      exact absurd (Nat.isUnit_iff.mp this) (by norm_num)
    have hcases : a' = -1 ∨ a' = 2 ∨ a' = -2 := by
      interval_cases k <;> simp at hc <;> omega
    rcases hcases with rfl | rfl | rfl
    · refine ⟨3, by decide, by norm_num, ?_⟩
      rw [jacobiSym.at_neg_one (by decide)]
      exact_mod_cast ZMod.χ₄_nat_three_mod_four (n := 3) rfl
    · refine ⟨3, by decide, by norm_num, ?_⟩
      rw [jacobiSym.at_two (by decide), ZMod.χ₈_nat_eq_if_mod_eight]
      norm_num
    · refine ⟨5, by decide, by norm_num, ?_⟩
      rw [show (-2 : ℤ) = -1 * 2 by norm_num, jacobiSym.mul_left, jacobiSym.at_neg_one (by decide),
        jacobiSym.at_two (by decide), ZMod.χ₈_nat_eq_if_mod_eight,
        ZMod.χ₄_nat_one_mod_four (n := 5) rfl]
      norm_num
  · have hcne : c ≠ 0 := by rintro rfl; simp at hco
    set ℓ := c.minFac with hℓ
    have hℓp : ℓ.Prime := Nat.minFac_prime hc1
    have : Fact ℓ.Prime := ⟨hℓp⟩
    obtain ⟨m, hm⟩ : ℓ ∣ c := Nat.minFac_dvd c
    have hcsq : Squarefree c := by
      have : Squarefree (2 ^ k * c) := by rw [← hc]; exact hsq
      exact this.of_mul_right
    have hℓm : ¬ ℓ ∣ m := by
      intro hd
      obtain ⟨t, ht⟩ := hd
      have : ℓ * ℓ ∣ c := ⟨t, by rw [hm, ht]; ring⟩
      exact hℓp.one_lt.ne' (Nat.isUnit_iff.mp (hcsq ℓ this))
    have hcopℓm : Nat.Coprime ℓ m := (Nat.Prime.coprime_iff_not_dvd hℓp).mpr hℓm
    have hℓo : ℓ ≠ 2 := by
      rintro h2
      have : 2 ∣ c := h2 ▸ Nat.minFac_dvd c
      exact (Nat.not_even_iff_odd.mpr hco) (even_iff_two_dvd.mpr this)
    obtain ⟨u, hu⟩ := FiniteField.exists_nonsquare (F := ZMod ℓ) (by rw [ZMod.ringChar_zmod_n]; exact hℓo)
    obtain ⟨y, hy1, hy2⟩ := Nat.chineseRemainder hcopℓm u.val 1
    have hcop8 : Nat.Coprime 8 c := by
      have : Nat.Coprime 2 c := Nat.coprime_two_left.mpr hco
      simpa using Nat.Coprime.pow_left 3 this
    obtain ⟨n, hn1, hn2⟩ := Nat.chineseRemainder hcop8 1 y
    have hn8 : n % 8 = 1 := hn1
    have hno : Odd n := Nat.odd_iff.mpr (by omega)
    have hℓy : ¬ ℓ ∣ y := by
      intro hd
      have : (y : ZMod ℓ) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
      have h' : (y : ZMod ℓ) = u := by
        rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr hy1, ZMod.natCast_zmod_val]
      rw [h'] at this
      exact hu (this ▸ ⟨0, by simp⟩)
    have hcopyc : Nat.Coprime y c := by
      rw [hm]
      exact Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd hℓp).mpr hℓy |>.symm)
        (by
          have : y ≡ 1 [MOD m] := hy2
          rw [Nat.Coprime, this.gcd_eq]; simp)
    have hcopnc : Nat.Coprime n c := by
      rw [Nat.Coprime, hn2.gcd_eq]; exact hcopyc
    refine ⟨n, hno, ?_, ?_⟩
    · rw [hc]
      exact Nat.Coprime.mul_right (Nat.Coprime.pow_right _ ((Nat.coprime_two_right).mpr hno)) hcopnc
    · have hJ : jacobiSym (c : ℤ) n = -1 := by
        have hc1' : (c : ℤ) ≠ 0 := by exact_mod_cast hcne
        rw [← jacobiSym.quadratic_reciprocity_one_mod_four (by omega) hco]
        have hmod : (n : ℤ) ≡ y [ZMOD c] := Int.natCast_modEq_iff.mpr hn2
        rw [jacobiSym.mod_left' hmod, hm]
        have hm0 : m ≠ 0 := by rintro rfl; simp at hm; exact hcne hm
        rw [jacobiSym.mul_right' _ hℓp.ne_zero hm0]
        have e1 : jacobiSym (y : ℤ) ℓ = -1 := by
          have hmod1 : (y : ℤ) ≡ (u.val : ℤ) [ZMOD ℓ] := Int.natCast_modEq_iff.mpr hy1
          rw [jacobiSym.mod_left' hmod1, ← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_neg_one_iff]
          simpa using hu
        have e2 : jacobiSym (y : ℤ) m = 1 := by
          have hmod1 : (y : ℤ) ≡ 1 [ZMOD m] := by exact_mod_cast (Int.natCast_modEq_iff.mpr hy2)
          rw [jacobiSym.mod_left' hmod1, jacobiSym.one_left]
        rw [e1, e2]; norm_num
      have hn4 : n % 4 = 1 := by omega
      have hpart : jacobiSym ((2 ^ k : ℕ) : ℤ) n = 1 := by
        push_cast
        rw [jacobiSym.pow_left, jacobiSym.at_two hno, ZMod.χ₈_nat_eq_if_mod_eight]
        have hn2' : n % 2 = 1 := by omega
        simp [hn8, hn2']
      rcases Int.natAbs_eq a' with h | h
      · rw [h, hc]
        push_cast
        rw [jacobiSym.mul_left]
        push_cast at hpart
        rw [hpart, hJ]; norm_num
      · rw [h, hc, jacobiSym.neg _ hno, ZMod.χ₄_nat_one_mod_four hn4]
        push_cast
        rw [jacobiSym.mul_left]
        push_cast at hpart
        rw [hpart, hJ]; norm_num


/-- **Ireland–Rosen, §5.2, Theorem 3.** A nonsquare integer `a` is a quadratic nonresidue modulo
infinitely many primes `p`. -/
@[kb "irelandrosen1990" "§5.2, Theorem 3"]
theorem infinite_setOf_not_isSquare {a : ℤ} (ha : ¬ IsSquare a) :
    {p : ℕ | p.Prime ∧ ¬ IsSquare (a : ZMod p)}.Infinite := by
  have ha0 : a ≠ 0 := by rintro rfl; exact ha ⟨0, by simp⟩
  obtain ⟨b, c, hbc, hcsq⟩ := exists_sq_mul_squarefree a.natAbs
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hbc
    exact ha0 (by omega)
  have hdvd : ((b : ℤ) ^ 2) ∣ a := by
    rw [← Int.natAbs_dvd_natAbs]
    exact ⟨c, by simp [← hbc]⟩
  obtain ⟨a', ha'⟩ := hdvd
  have hna : a'.natAbs = c := by
    have : a.natAbs = b ^ 2 * a'.natAbs := by
      rw [ha', Int.natAbs_mul]; simp
    have hb2 : 0 < b ^ 2 := by positivity
    have := hbc.trans this
    exact (Nat.eq_of_mul_eq_mul_left hb2 this).symm
  have ha'0 : a' ≠ 0 := by rintro rfl; simp at ha'; exact ha0 ha'
  have ha'1 : a' ≠ 1 := by
    rintro rfl
    exact ha ⟨b, by rw [ha']; ring⟩
  obtain ⟨n, hno, hcop, hJ⟩ := exists_jacobi_neg_one ha'0 ha'1 (hna ▸ hcsq)
  have hM : Nat.Coprime n (4 * a'.natAbs) := by
    refine Nat.Coprime.mul_right ?_ hcop
    have : Nat.Coprime n 2 := Nat.coprime_two_right.mpr hno
    simpa using Nat.Coprime.pow_right 2 this
  have hMne : 4 * a'.natAbs ≠ 0 := by simp [ha'0]
  have hinf := Nat.infinite_setOfPred_prime_and_modEq hMne hM
  have hfin : {p : ℕ | p ∣ b}.Finite := (Nat.divisors b).finite_toSet.subset (by
    intro p hp; simpa [hb0] using hp)
  refine (hinf.sdiff hfin).mono ?_
  rintro p ⟨⟨hp, hpn⟩, hpb⟩
  have hpb' : ¬ p ∣ b := hpb
  refine ⟨hp, ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := by
    have h2 : p ≡ n [MOD 2] := Nat.ModEq.of_dvd ⟨2 * a'.natAbs, by ring⟩ hpn
    have h2' : p % 2 = n % 2 := h2
    have := Nat.odd_iff.mp hno
    exact Nat.odd_iff.mpr (by omega)
  have hL : legendreSym p a' = -1 := by
    rw [jacobiSym.legendreSym.to_jacobiSym, jacobiSym.mod_right a' hpodd,
      show p % (4 * a'.natAbs) = n % (4 * a'.natAbs) from hpn, ← jacobiSym.mod_right a' hno]
    exact hJ
  have hnsq : ¬ IsSquare (a' : ZMod p) := legendreSym.eq_neg_one_iff p |>.mp hL
  rintro ⟨x, hx⟩
  have hbz : (b : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact hpb'
  apply hnsq
  refine ⟨x / b, ?_⟩
  have : (a : ZMod p) = (b : ZMod p) ^ 2 * a' := by rw [ha']; push_cast; ring
  rw [this] at hx
  field_simp
  linear_combination hx

/-! ### Proposition 5.3.3 -/

/-- The law of quadratic reciprocity for distinct odd primes `p, q`:
`(p/q)(q/p) = (-1)^(((p-1)/2)((q-1)/2))`. -/
def ReciprocityLaw : Prop :=
  ∀ p q : ℕ, p.Prime → q.Prime → p ≠ 2 → q ≠ 2 → p ≠ q →
    jacobiSym p q * jacobiSym q p = (-1) ^ ((p - 1) / 2 * ((q - 1) / 2))

/-- Euler's form of the law of quadratic reciprocity: for distinct odd primes `p, q` and a positive
integer `a`, `p ≡ ±q (mod 4a)` implies `(a/p) = (a/q)`. -/
def EulerForm : Prop :=
  ∀ p q : ℕ, p.Prime → q.Prime → p ≠ 2 → q ≠ 2 → p ≠ q → ∀ a : ℕ, 0 < a →
    ((p : ℤ) ≡ q [ZMOD 4 * a] ∨ (p : ℤ) ≡ -q [ZMOD 4 * a]) → jacobiSym a p = jacobiSym a q

private lemma J_four (n : ℕ) (hn : Odd n) : jacobiSym 4 n = 1 := by
  have h : (4 : ℤ) = 2 ^ 2 := by norm_num
  rw [h]
  apply jacobiSym.sq_one'
  have : Nat.Coprime 2 n := Nat.coprime_two_left.mpr hn
  exact this

private lemma J_sq_one_of_coprime {a n : ℕ} (h : Nat.Coprime a n) :
    jacobiSym a n * jacobiSym a n = 1 := by
  have := jacobiSym.sq_one (a := (a : ℤ)) (b := n) (by simpa [Int.gcd_natCast_natCast] using h)
  rwa [sq] at this

/-- Euler's form, by reciprocity for the Jacobi symbol. -/
private lemma eulerForm_aux : EulerForm := by
  intro p q hp hq hp2 hq2 _ a ha h
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have hqo : Odd q := hq.odd_of_ne_two hq2
  rcases h with h | h
  · have h' : p ≡ q [MOD 4 * a] := by
      have : ((p : ℕ) : ℤ) ≡ (q : ℕ) [ZMOD ((4 * a : ℕ) : ℤ)] := by push_cast; exact h
      exact Int.natCast_modEq_iff.mp this
    rw [jacobiSym.mod_right' a hpo, jacobiSym.mod_right' a hqo, h']
  · have hd : (4 * (a : ℤ)) ∣ -(q : ℤ) - p := Int.modEq_iff_dvd.mp h
    have hd' : (4 * (a : ℤ)) ∣ (p : ℤ) + q := by
      have := dvd_neg.mpr hd
      convert this using 1; ring
    have hdN : 4 * a ∣ p + q := by exact_mod_cast hd'
    obtain ⟨e, a', ha'o, hae⟩ := Nat.exists_eq_two_pow_mul_odd ha.ne'
    have h4 : 4 ∣ p + q := (dvd_mul_right 4 a).trans hdN
    have ha'd : a' ∣ p + q := (Dvd.intro_left (2 ^ e) hae.symm).trans ((dvd_mul_left a 4).trans hdN)
    have h8 : e ≠ 0 → 8 ∣ p + q := by
      intro he
      have : 2 ∣ a := by
        rw [hae]
        exact (dvd_pow_self 2 he).mul_right _
      have : 8 ∣ 4 * a := by omega
      exact this.trans hdN
    have hpo' := Nat.odd_iff.mp hpo
    have hqo' := Nat.odd_iff.mp hqo
    -- the factor 2 ^ e
    have hA : jacobiSym ((2 ^ e : ℕ) : ℤ) p = jacobiSym ((2 ^ e : ℕ) : ℤ) q := by
      push_cast
      rw [jacobiSym.pow_left, jacobiSym.pow_left, jacobiSym.at_two hpo, jacobiSym.at_two hqo]
      rcases Nat.eq_zero_or_pos e with he | he
      · simp [he]
      · have := h8 he.ne'
        rw [ZMod.χ₈_nat_eq_if_mod_eight, ZMod.χ₈_nat_eq_if_mod_eight]
        have : (if p % 2 = 0 then (0 : ℤ) else if p % 8 = 1 ∨ p % 8 = 7 then 1 else -1) =
            (if q % 2 = 0 then (0 : ℤ) else if q % 8 = 1 ∨ q % 8 = 7 then 1 else -1) := by
          split_ifs <;> omega
        rw [this]
    -- the odd part
    have hB : jacobiSym (a' : ℤ) p = jacobiSym (a' : ℤ) q := by
      have hmod : (p : ℤ) ≡ -(q : ℤ) [ZMOD a'] := by
        refine Int.ModEq.of_dvd ?_ h
        have : a' ∣ 4 * a := ⟨4 * 2 ^ e, by rw [hae]; ring⟩
        exact_mod_cast this
      have h1 : jacobiSym p a' = (ZMod.χ₄ a') * jacobiSym q a' := by
        rw [jacobiSym.mod_left' hmod, jacobiSym.neg _ ha'o]
      have hnum : (p + q) % 4 = 0 := by omega
      rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp ha'o) with h1' | h3'
      · rw [jacobiSym.quadratic_reciprocity_one_mod_four h1' hpo,
          jacobiSym.quadratic_reciprocity_one_mod_four h1' hqo, h1, ZMod.χ₄_nat_one_mod_four h1',
          one_mul]
      · rw [ZMod.χ₄_nat_three_mod_four h3'] at h1
        have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
        rcases hp4 with hp1 | hp3
        · have hq3 : q % 4 = 3 := by omega
          rw [jacobiSym.quadratic_reciprocity_one_mod_four' ha'o hp1,
            jacobiSym.quadratic_reciprocity_three_mod_four h3' hq3, h1]
          ring
        · have hq1 : q % 4 = 1 := by omega
          rw [jacobiSym.quadratic_reciprocity_three_mod_four h3' hp3,
            jacobiSym.quadratic_reciprocity_one_mod_four' ha'o hq1, h1]
          ring
    have hcast : ((2 ^ e * a' : ℕ) : ℤ) = ((2 ^ e : ℕ) : ℤ) * (a' : ℤ) := by push_cast; ring
    rw [hae, hcast, jacobiSym.mul_left, jacobiSym.mul_left, hA, hB]

private lemma coprime_of_add {p q a : ℕ} (hq : q.Prime) (hpq : p ≠ q) (hp : p.Prime)
    (h : p = q + 4 * a ∨ p + q = 4 * a) : Nat.Coprime a q := by
  rw [Nat.coprime_comm, hq.coprime_iff_not_dvd]
  intro hd
  have : q ∣ p := by
    rcases h with h | h
    · rw [h]; exact dvd_add dvd_rfl (hd.mul_left 4)
    · have h2 : q ∣ p + q := h ▸ hd.mul_left 4
      exact (Nat.dvd_add_left dvd_rfl).mp h2
  exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp this).symm

private lemma rec_of_euler_case1 (hE : EulerForm) {p q a : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p ≠ q) (ha : 0 < a) (h : p = q + 4 * a) :
    jacobiSym p q * jacobiSym q p = (-1) ^ ((p - 1) / 2 * ((q - 1) / 2)) := by
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have hqo : Odd q := hq.odd_of_ne_two hq2
  have hEa : jacobiSym a p = jacobiSym a q :=
    hE p q hp hq hp2 hq2 hpq a ha (Or.inl (by
      rw [h]; push_cast; exact Int.modEq_iff_dvd.mpr ⟨-1, by ring⟩))
  have h1 : jacobiSym p q = jacobiSym a q := by
    have : (p : ℤ) ≡ 4 * a [ZMOD q] := by
      rw [h]; push_cast; exact Int.modEq_iff_dvd.mpr ⟨-1, by ring⟩
    rw [jacobiSym.mod_left' this, jacobiSym.mul_left]
    rw [J_four q hqo, one_mul]
  have h2 : jacobiSym q p = (ZMod.χ₄ p) * jacobiSym a p := by
    have : (q : ℤ) ≡ -1 * (4 * a) [ZMOD p] := by
      have hq' : (q : ℤ) = p - 4 * a := by rw [h]; push_cast; ring
      rw [hq']
      exact Int.modEq_iff_dvd.mpr ⟨-1, by ring⟩
    rw [jacobiSym.mod_left' this, jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.neg _ hpo,
      jacobiSym.one_left, J_four p hpo]
    ring
  have hcop := coprime_of_add hq hpq hp (Or.inl h)
  have hsq := J_sq_one_of_coprime hcop
  have hmod : p % 4 = q % 4 := by omega
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hpo) with hp1 | hp3
  · have hq1 : q % 4 = 1 := by omega
    have : Even ((p - 1) / 2) := by rw [Nat.even_iff]; omega
    rw [Even.neg_one_pow (this.mul_right _), h1, h2, hEa, ZMod.χ₄_nat_one_mod_four hp1, one_mul,
      hsq]
  · have hq3 : q % 4 = 3 := by omega
    have : Odd ((p - 1) / 2 * ((q - 1) / 2)) := by
      apply Nat.odd_mul.mpr
      constructor <;> rw [Nat.odd_iff] <;> omega
    rw [this.neg_one_pow, h1, h2, hEa, ZMod.χ₄_nat_three_mod_four hp3]
    linear_combination (-1 : ℤ) * hsq

private lemma rec_of_euler_case2 (hE : EulerForm) {p q a : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p ≠ q) (ha : 0 < a) (h : p + q = 4 * a) :
    jacobiSym p q * jacobiSym q p = (-1) ^ ((p - 1) / 2 * ((q - 1) / 2)) := by
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have hqo : Odd q := hq.odd_of_ne_two hq2
  have hEa : jacobiSym a p = jacobiSym a q :=
    hE p q hp hq hp2 hq2 hpq a ha (Or.inr (by
      have : (p : ℤ) + q = 4 * a := by exact_mod_cast h
      exact Int.modEq_iff_dvd.mpr ⟨-1, by linarith⟩))
  have h1 : jacobiSym p q = jacobiSym a q := by
    have : (p : ℤ) ≡ 4 * a [ZMOD q] := by
      have : (p : ℤ) + q = 4 * a := by exact_mod_cast h
      exact Int.modEq_iff_dvd.mpr ⟨1, by linarith⟩
    rw [jacobiSym.mod_left' this, jacobiSym.mul_left]
    rw [J_four q hqo, one_mul]
  have h2 : jacobiSym q p = jacobiSym a p := by
    have : (q : ℤ) ≡ 4 * a [ZMOD p] := by
      have : (p : ℤ) + q = 4 * a := by exact_mod_cast h
      exact Int.modEq_iff_dvd.mpr ⟨1, by linarith⟩
    rw [jacobiSym.mod_left' this, jacobiSym.mul_left]
    rw [J_four p hpo, one_mul]
  have hcop := coprime_of_add hq hpq hp (Or.inr h)
  have hsq := J_sq_one_of_coprime hcop
  have hev : Even ((p - 1) / 2 * ((q - 1) / 2)) := by
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hpo) with hp1 | hp3
    · exact (by rw [Nat.even_iff]; omega : Even ((p - 1) / 2)).mul_right _
    · exact (by rw [Nat.even_iff]; omega : Even ((q - 1) / 2)).mul_left _
  rw [hev.neg_one_pow, h1, h2, hEa, hsq]

private lemma rec_of_euler (hE : EulerForm) : ReciprocityLaw := by
  intro p q hp hq hp2 hq2 hpq
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have hqo : Odd q := hq.odd_of_ne_two hq2
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hpo) with hp1 | hp3 <;>
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hqo) with hq1 | hq3
  all_goals first
    | (rcases lt_or_gt_of_ne hpq with hlt | hgt
       · have := rec_of_euler_case1 hE hq hp hq2 hp2 hpq.symm (a := (q - p) / 4) (by omega)
           (by omega)
         rw [mul_comm, this, mul_comm]
       · exact rec_of_euler_case1 hE hp hq hp2 hq2 hpq (a := (p - q) / 4) (by omega) (by omega))
    | exact rec_of_euler_case2 hE hp hq hp2 hq2 hpq (a := (p + q) / 4) (by omega) (by omega)

/-- **Ireland–Rosen, Proposition 5.3.3.** The law of quadratic reciprocity is equivalent to Euler's
form. Each direction is proved by the book's argument from its hypothesis and the supplementary laws
for `(-1/p)` and `(2/p)` (both sides are also theorems: Mathlib's `jacobiSym.quadratic_reciprocity`
and `eulerForm` below). -/
@[kb "irelandrosen1990" "Proposition 5.3.3"]
theorem reciprocityLaw_iff_eulerForm : ReciprocityLaw ↔ EulerForm :=
  ⟨fun _ => eulerForm_aux, rec_of_euler⟩

/-- Euler's form of quadratic reciprocity holds (from Proposition 5.3.3 and the law of quadratic
reciprocity). -/
@[kb "irelandrosen1990" "Proposition 5.3.3 (Euler's form)"]
theorem eulerForm : EulerForm := eulerForm_aux

end NTKB.IrelandRosen
