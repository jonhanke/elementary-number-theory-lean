/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.Tactic.NormNum.Prime
import NTKB.Attr

/-!
# Fermat's theorem and its consequences (Hardy–Wright, Chapter VI, §§ 6.2 to 6.10)

* Theorem 76: the coefficients of `(1 - x)^{-p}` are divisible by `p` except those of
  `1, x^p, x^{2p}, …`, which are `≡ 1 (mod p)`.
* Theorem 78: `m ≡ 1 (mod p^a)`, `a > 0` implies `m^p ≡ 1 (mod p^{a+1})`.
* Theorem 79: `(p - 1)! ≡ -(a/p) a^{(p-1)/2} (mod p)`.
* Theorem 84: an odd prime has `(p - 1)/2` residues and `(p - 1)/2` non-residues.
* Theorem 86: for `p = 4k + 1` there is `x` with `1 + x² = mp`, `0 < m < p`.
* Theorem 91: `2^{p-1} ≡ 1 (mod p²)` for `p = 1093` (and for `p = 3511`).
-/

open PowerSeries

namespace NTKB.HardyWright

/-! ### Theorem 73 -/

/-- **Theorem 73** [hardywright2008]: if `m` and `n` are positive integers, the binomial
coefficients `m(m - 1)⋯(m - n + 1)/n!` and `(-1)^n C(-m, n) = m(m + 1)⋯(m + n - 1)/n!` are integers;
i.e. `n!` divides both products (Mathlib's `Nat.factorial_dvd_descFactorial` and
`Nat.factorial_dvd_ascFactorial`). -/
@[kb "hardywright2008" "Thm 73, p. 79"]
theorem factorial_dvd_prod_consecutive (m n : ℕ) :
    n.factorial ∣ ∏ i ∈ Finset.range n, (m - i) ∧ n.factorial ∣ ∏ i ∈ Finset.range n, (m + i) := by
  rw [← Nat.descFactorial_eq_prod_range, ← Nat.ascFactorial_eq_prod_range]
  exact ⟨Nat.factorial_dvd_descFactorial m n, Nat.factorial_dvd_ascFactorial m n⟩

/-! ### Theorem 76 -/

/-- In `(ZMod p)⟦X⟧`, `(1 - X)^p = 1 - X^p`. -/
lemma one_sub_X_pow_char (p : ℕ) [Fact p.Prime] :
    ((1 : (ZMod p)⟦X⟧) - X) ^ p = 1 - X ^ p := by
  have h : ((1 : Polynomial (ZMod p)) - Polynomial.X) ^ p = 1 - Polynomial.X ^ p := by
    rw [sub_pow_char, one_pow]
  have := congrArg (Polynomial.coeToPowerSeries.ringHom (R := ZMod p)) h
  simpa using this

/-- The series `1 + X^p + X^{2p} + …` is the inverse of `1 - X^p`. -/
lemma mk_dvd_mul_one_sub_X_pow {R : Type*} [CommRing R] {p : ℕ} (hp : 0 < p) :
    (mk fun n ↦ if p ∣ n then (1 : R) else 0) * (1 - X ^ p) = 1 := by
  ext n
  rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow', coeff_mk, coeff_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.not_le.2 hp]
  by_cases h1 : p ≤ n
  · have : p ∣ n - p ↔ p ∣ n := Nat.dvd_sub_iff_left h1 (dvd_refl p)
    by_cases h2 : p ∣ n
    · simp [h1, h2, this.2 h2, hn.ne']
    · simp [h1, h2, mt this.1 h2, hn.ne']
  · simp [h1, hn.ne', mt (Nat.le_of_dvd hn) h1]

/-- **Theorem 76** [hardywright2008]: if `p` is prime, all the coefficients of `(1 - x)^{-p}`
(Mathlib's `invOneSubPow ℤ p`) are divisible by `p`, except those of `1, x^p, x^{2p}, …`, which are
congruent to `1 (mod p)`. -/
@[kb "hardywright2008" "Thm 76, p. 80"]
theorem coeff_invOneSubPow_prime (p : ℕ) [hp : Fact p.Prime] (n : ℕ) :
    ((coeff n (invOneSubPow ℤ p : ℤ⟦X⟧) : ℤ) : ZMod p) = if p ∣ n then 1 else 0 := by
  -- reduce modulo `p`: `(1 - x)^{-p} ≡ (1 - x^p)^{-1}`, since `(1 - x)^p ≡ 1 - x^p`
  set f : (ZMod p)⟦X⟧ := map (Int.castRingHom (ZMod p)) (invOneSubPow ℤ p : ℤ⟦X⟧)
  set g : (ZMod p)⟦X⟧ := mk fun n ↦ if p ∣ n then (1 : ZMod p) else 0
  have hf : f * (1 - X) ^ p = 1 := by
    have h := (invOneSubPow ℤ p).val_inv
    rw [invOneSubPow_inv_eq_one_sub_pow] at h
    have := congrArg (map (Int.castRingHom (ZMod p))) h
    simpa using this
  have hg : g * (1 - X ^ p) = 1 := mk_dvd_mul_one_sub_X_pow hp.out.pos
  have hfg : f = g := by
    calc f = f * (g * (1 - X ^ p)) := by rw [hg, mul_one]
      _ = (f * (1 - X) ^ p) * g := by rw [one_sub_X_pow_char]; ring
      _ = g := by rw [hf, one_mul]
  have := congrArg (coeff n) hfg
  simpa [f, g] using this

/-- **Theorem 76** [hardywright2008], in terms of the binomial coefficients
`C(p + n - 1, n) = C(p - 1 + n, p - 1)` of `(1 - x)^{-p}`. -/
@[kb "hardywright2008" "Thm 76, p. 80"]
theorem choose_prime_sub_one_add_modEq (p : ℕ) [hp : Fact p.Prime] (n : ℕ) :
    ((p - 1 + n).choose (p - 1) : ZMod p) = if p ∣ n then 1 else 0 := by
  have := coeff_invOneSubPow_prime p n
  rwa [invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos _ _ hp.out.pos, coeff_mk,
    Int.cast_natCast] at this

/-! ### Theorem 78 -/

/-- **Theorem 78** [hardywright2008]: if `a > 0` and `m ≡ 1 (mod p^a)`, then
`m^p ≡ 1 (mod p^{a+1})`. -/
@[kb "hardywright2008" "Thm 78, p. 81"]
theorem pow_prime_modEq_one {p a : ℕ} (ha : 0 < a) {m : ℤ}
    (hm : m ≡ 1 [ZMOD p ^ a]) : m ^ p ≡ 1 [ZMOD p ^ (a + 1)] := by
  -- `m - 1 = k p^a`, and `m^p - 1 = (m - 1)(1 + m + ⋯ + m^{p-1})` with the second factor
  -- `≡ p ≡ 0 (mod p)` (the book expands `(1 + k p^a)^p` by the binomial theorem instead)
  have h1 : (p : ℤ) ^ a ∣ m - 1 := Int.ModEq.dvd hm.symm
  have h2 : (p : ℤ) ∣ ∑ i ∈ Finset.range p, m ^ i := by
    have hp1 : (p : ℤ) ∣ m - 1 := (dvd_pow_self (p : ℤ) ha.ne').trans h1
    have hm1 : (m : ZMod p) = 1 := by
      rw [← sub_eq_zero, ← Int.cast_one, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact hp1
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    simp [hm1]
  refine (Int.modEq_of_dvd ?_).symm
  rw [← geom_sum_mul, pow_succ, mul_comm ((p : ℤ) ^ a)]
  exact mul_dvd_mul h2 h1

/-! ### Theorem 79 -/

/-- **Theorem 79** [hardywright2008]: if `p` is an odd prime and `a` is not a multiple of `p`,
then `(p - 1)! ≡ -(a/p) a^{(p-1)/2} (mod p)`. (Hardy and Wright prove it by pairing the numbers
`1, …, p - 1` into associates `x x' ≡ a` and deduce Wilson's theorem and Euler's criterion from
it; here it is derived from Mathlib's Wilson theorem `ZMod.wilsons_lemma` and Euler criterion
`legendreSym.eq_pow`.) -/
@[kb "hardywright2008" "Thm 79, p. 85"]
theorem factorial_eq_neg_legendreSym_mul_pow (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {a : ℤ}
    (ha : (a : ZMod p) ≠ 0) :
    (((p - 1).factorial : ℕ) : ZMod p) =
      -(legendreSym p a : ZMod p) * (a : ZMod p) ^ ((p - 1) / 2) := by
  have h2 : (p - 1) / 2 = p / 2 := by
    rcases Nat.Prime.eq_two_or_odd' (Fact.out : p.Prime) with h | ⟨k, hk⟩
    · exact absurd h hp
    · omega
  rw [ZMod.wilsons_lemma, h2, ← legendreSym.eq_pow, neg_mul, ← sq]
  have := legendreSym.sq_one p ha
  have : ((legendreSym p a : ℤ) : ZMod p) ^ 2 = 1 := by
    rw [← Int.cast_pow, this, Int.cast_one]
  rw [this]

/-! ### Theorem 84 -/

/-- `x ↦ x²` is injective on `1, 2, …, (p - 1)/2` modulo an odd prime `p`. -/
private lemma sq_injOn (p : ℕ) [Fact p.Prime] :
    Set.InjOn (fun x : ℕ ↦ (x : ZMod p) ^ 2) (Finset.Icc 1 ((p - 1) / 2) : Set ℕ) := by
  intro x hx y hy hxy
  simp only [Finset.coe_Icc, Set.mem_Icc] at hx hy
  have hp := (Fact.out : p.Prime).two_le
  have hxy' : ((x : ZMod p) - y) * ((x : ZMod p) + y) = 0 := by
    simp only at hxy
    linear_combination hxy
  rcases mul_eq_zero.1 hxy' with h | h
  · rw [sub_eq_zero] at h
    have := congrArg ZMod.val h
    rwa [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at this
  · -- `p ∣ x + y` is impossible since `2 ≤ x + y ≤ p - 1`
    exfalso
    have : p ∣ x + y := by
      rw [← ZMod.natCast_eq_zero_iff]; push_cast; exact h
    have := Nat.le_of_dvd (by omega) this
    omega

/-- **Theorem 84** [hardywright2008]: an odd prime `p` has `(p - 1)/2` quadratic residues and
`(p - 1)/2` non-residues among the classes prime to `p`. Following the book, the residues are the
classes of `1², 2², …, ((p - 1)/2)²`, which are incongruent. -/
@[kb "hardywright2008" "Thm 84, p. 87"]
theorem card_residues_and_nonresidues (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    Fintype.card {a : ZMod p // a ≠ 0 ∧ IsSquare a} = (p - 1) / 2 ∧
      Fintype.card {a : ZMod p // a ≠ 0 ∧ ¬IsSquare a} = (p - 1) / 2 := by
  classical
  have hp2 := (Fact.out : p.Prime).two_le
  have hodd : p % 2 = 1 := (
    Nat.odd_iff.1 ((Fact.out : p.Prime).odd_of_ne_two hp))
  -- the residues are the squares of `1, …, (p - 1)/2`
  have himage : (Finset.univ.filter fun a : ZMod p ↦ a ≠ 0 ∧ IsSquare a) =
      (Finset.Icc 1 ((p - 1) / 2)).image (fun x : ℕ ↦ (x : ZMod p) ^ 2) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨ha, z, rfl⟩
      refine ⟨z.valMinAbs.natAbs, ⟨?_, ?_⟩, ?_⟩
      · rw [Nat.one_le_iff_ne_zero, Int.natAbs_ne_zero, Ne, ZMod.valMinAbs_eq_zero]
        rintro rfl; simp at ha
      · have := ZMod.natAbs_valMinAbs_le z; omega
      · rw [← sq]
        have h := Int.natAbs_sq z.valMinAbs
        have : ((z.valMinAbs.natAbs : ℕ) : ZMod p) ^ 2 = ((z.valMinAbs : ℤ) : ZMod p) ^ 2 := by
          rw [← Int.cast_natCast, ← Int.cast_pow, h, Int.cast_pow]
        rw [this, ZMod.coe_valMinAbs]
    · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
      refine ⟨pow_ne_zero 2 ?_, ⟨x, sq _⟩⟩
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact fun h ↦ absurd (Nat.le_of_dvd (by omega) h) (by omega)
  have hres : Fintype.card {a : ZMod p // a ≠ 0 ∧ IsSquare a} = (p - 1) / 2 := by
    rw [Fintype.card_subtype, himage, Finset.card_image_of_injOn (sq_injOn p),
      Nat.card_Icc, Nat.add_sub_cancel]
  refine ⟨hres, ?_⟩
  have htot : Fintype.card {a : ZMod p // a ≠ 0} = p - 1 := by
    rw [Fintype.card_subtype_compl, ZMod.card, Fintype.card_unique]
  have hsplit := Fintype.card_subtype_or_disjoint (fun a : ZMod p ↦ a ≠ 0 ∧ IsSquare a)
    (fun a ↦ a ≠ 0 ∧ ¬IsSquare a) (by
      rw [Pi.disjoint_iff]; intro a; simp only [Prop.disjoint_iff]; tauto)
  have : Fintype.card {a : ZMod p // (a ≠ 0 ∧ IsSquare a) ∨ (a ≠ 0 ∧ ¬IsSquare a)} = p - 1 := by
    rw [← htot]; exact Fintype.card_congr (Equiv.subtypeEquivRight fun a ↦ by tauto)
  omega

/-! ### Theorem 86 -/

/-- **Theorem 86** [hardywright2008]: if `p` is a prime `4k + 1`, then there is an `x` with
`1 + x² = m p`, `0 < m < p`. -/
@[kb "hardywright2008" "Thm 86, p. 87"]
theorem exists_one_add_sq_eq_mul {p : ℕ} (hp : p.Prime) (h4 : p % 4 = 1) :
    ∃ x m : ℕ, 1 + x ^ 2 = m * p ∧ 0 < m ∧ m < p := by
  have := Fact.mk hp
  -- `-1` is a residue (Theorem 82), congruent to some `x²` with `0 < x ≤ (p - 1)/2`
  obtain ⟨y, hy⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).2 (by omega)
  set x : ℕ := y.valMinAbs.natAbs
  have hx2 : ((x : ℤ) : ZMod p) ^ 2 = -1 := by
    rw [hy]
    have : ((x : ℤ) : ZMod p) = y ∨ ((x : ℤ) : ZMod p) = -y := by
      rcases Int.natAbs_eq y.valMinAbs with h | h
      · left; rw [← ZMod.coe_valMinAbs y]; congr 1; exact h.symm
      · right; rw [← ZMod.coe_valMinAbs y, ← Int.cast_neg]; congr 1; omega
    rcases this with h | h <;> rw [h] <;> ring
  have hxle : x ≤ p / 2 := ZMod.natAbs_valMinAbs_le y
  obtain ⟨m, hm⟩ : (p : ℤ) ∣ 1 + (x : ℤ) ^ 2 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at hx2 ⊢
    rw [hx2]; ring
  have hp2 : 2 ≤ p := hp.two_le
  have hm0 : 0 < m := by
    by_contra h
    push Not at h
    nlinarith
  refine ⟨x, m.toNat, ?_, by omega, ?_⟩
  · have : ((1 + x ^ 2 : ℕ) : ℤ) = ((m.toNat * p : ℕ) : ℤ) := by
      push_cast; rw [Int.toNat_of_nonneg hm0.le]; linarith
    exact_mod_cast this
  · -- `0 < 1 + x² ≤ 1 + (p/2)² < p²`
    have hx' : (x : ℤ) ≤ p / 2 := by exact_mod_cast hxle
    have h2x : 2 * (x : ℤ) ≤ p := by omega
    have : (m : ℤ) < p := by nlinarith
    omega

/-! ### Theorem 91 -/

/-- **Theorem 91** [hardywright2008]: there is a prime `p` with `2^{p-1} ≡ 1 (mod p²)`, namely
`p = 1093`. (The book also gives a hand computation; here the congruence is checked by the
kernel.) -/
@[kb "hardywright2008" "Thm 91, p. 91"]
theorem two_pow_1092_modEq_one : 2 ^ (1093 - 1) ≡ 1 [MOD 1093 ^ 2] ∧ Nat.Prime 1093 := by
  constructor
  · unfold Nat.ModEq; decide +kernel
  · norm_num

/-- The same is true for `p = 3511` [hardywright2008, § 6.10]. -/
@[kb "hardywright2008" "Thm 91, p. 91"]
theorem two_pow_3510_modEq_one : 2 ^ (3511 - 1) ≡ 1 [MOD 3511 ^ 2] ∧ Nat.Prime 3511 := by
  constructor
  · unfold Nat.ModEq; decide +kernel
  · norm_num

/-- **Theorem 91** [hardywright2008]. -/
@[kb "hardywright2008" "Thm 91, p. 91"]
theorem exists_prime_two_pow_modEq_one_sq : ∃ p : ℕ, p.Prime ∧ 2 ^ (p - 1) ≡ 1 [MOD p ^ 2] :=
  ⟨1093, two_pow_1092_modEq_one.2, two_pow_1092_modEq_one.1⟩

end NTKB.HardyWright
