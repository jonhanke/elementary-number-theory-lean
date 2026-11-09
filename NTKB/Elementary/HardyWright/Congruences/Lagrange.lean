/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.NumberTheory.Bernoulli
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import NTKB.Attr

/-!
# General properties of congruences (Hardy–Wright, Chapter VII)

Hardy and Wright say that two integral polynomials are congruent modulo `m` when their
coefficients are; `f ≡ 0 (mod m)` is `C m ∣ f` in `ℤ[X]`. Results:

* Theorem 104: if `f g ≡ 0 (mod p^a)` and `f ≢ 0 (mod p)`, then `g ≡ 0 (mod p^a)`; for `a = 1`
  this is part (i), `f g ≡ 0 (mod p)` implies `f ≡ 0` or `g ≡ 0`.
* Theorem 109: if `d ∣ p - 1`, then `x^d ≡ 1 (mod p)` has exactly `d` roots.
* Theorem 112 in the form `(x - 1)(x - 2)⋯(x - (p - 1)) ≡ x^{p-1} - 1 (mod p)` (Mathlib has it for
  the units of a field, `Lagrange.nodal_subgroup_eq_X_pow_card_sub_one`).
* Theorem 113: the coefficients `A_1, …, A_{p-2}` of `(x - 1)⋯(x - (p - 1))` are divisible by `p`.
* Theorem 114: for `p = 4n + 3`, `((p - 1)/2)! ≡ (-1)^ν (mod p)`, `ν` the number of
  non-residues below `p/2`.
* Theorem 120: if `k` is a prime `3n + 1`, then `B_k ≡ 1/6 (mod 1)`.
-/

open Polynomial Finset

namespace NTKB.HardyWright

/-! ### Theorem 104 -/

/-- **Theorem 104** [hardywright2008]: (ii) if `f(x) g(x) ≡ 0 (mod p^a)` and `f(x) ≢ 0 (mod p)`,
then `g(x) ≡ 0 (mod p^a)`; congruence of integral polynomials means congruence of all
coefficients, i.e. divisibility by the constant `C m` in `ℤ[X]`. (The book removes multiples of `p`
and compares leading coefficients; here part (i) is applied `a` times.) -/
@[kb "hardywright2008" "Thm 104, p. 104"]
theorem C_pow_dvd_of_C_pow_dvd_mul {p : ℕ} (hp : p.Prime) (a : ℕ) {f g : ℤ[X]}
    (h : C ((p : ℤ) ^ a) ∣ f * g) (hf : ¬C (p : ℤ) ∣ f) : C ((p : ℤ) ^ a) ∣ g := by
  have hpC : Prime (C (p : ℤ)) := Polynomial.prime_C_iff.2 (Nat.prime_iff_prime_int.1 hp)
  induction a generalizing g with
  | zero => simp
  | succ a ih =>
    have h1 : C (p : ℤ) ∣ f * g :=
      (map_dvd C (dvd_pow_self (p : ℤ) (Nat.succ_ne_zero a))).trans h
    obtain ⟨g', rfl⟩ := (hpC.dvd_or_dvd h1).resolve_left hf
    have h2 : C ((p : ℤ) ^ a) ∣ f * g' := by
      rw [pow_succ, C_mul, mul_left_comm f, mul_comm (C ((p : ℤ) ^ a))] at h
      exact (mul_dvd_mul_iff_left hpC.ne_zero).1 h
    rw [pow_succ, C_mul, mul_comm (C ((p : ℤ) ^ a))]
    exact mul_dvd_mul_left _ (ih h2)

/-- **Theorem 104** [hardywright2008], part (i): if `f(x) g(x) ≡ 0 (mod p)`, then
`f(x) ≡ 0` or `g(x) ≡ 0 (mod p)`. -/
@[kb "hardywright2008" "Thm 104, p. 104"]
theorem C_dvd_or_C_dvd_of_C_dvd_mul {p : ℕ} (hp : p.Prime) {f g : ℤ[X]}
    (h : C (p : ℤ) ∣ f * g) : C (p : ℤ) ∣ f ∨ C (p : ℤ) ∣ g :=
  (Polynomial.prime_C_iff.2 (Nat.prime_iff_prime_int.1 hp)).dvd_or_dvd h

/-! ### Theorem 109 -/

/-- **Theorem 109** [hardywright2008]: if `d ∣ p - 1`, then `x^d ≡ 1 (mod p)` has exactly `d`
roots. (The book compares root counts of `x^{p-1} - 1 = (x^d - 1)(x^{p-1-d} + ⋯ + 1)`; here the
count is that of the kernel of `u ↦ u^d` on the cyclic group `(ZMod p)ˣ`.) -/
@[kb "hardywright2008" "Thm 109, p. 108"]
theorem card_pow_eq_one_of_dvd (p : ℕ) [hp : Fact p.Prime] {d : ℕ} (hd : d ∣ p - 1) :
    Nat.card {x : ZMod p // x ^ d = 1} = d := by
  have hd0 : d ≠ 0 := by
    rintro rfl
    have := hp.out.two_le
    simp only [zero_dvd_iff] at hd
    omega
  have hker : Nat.card (powMonoidHom d : (ZMod p)ˣ →* (ZMod p)ˣ).ker = d := by
    rw [IsCyclic.card_powMonoidHom_ker, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime hp.out, Nat.gcd_eq_right hd]
  refine Eq.trans ?_ hker
  refine Nat.card_congr
    { toFun := fun x ↦ ⟨(IsUnit.of_pow_eq_one x.2 hd0).unit, by
        rw [MonoidHom.mem_ker, powMonoidHom_apply]; ext; simp [x.2]⟩
      invFun := fun u ↦ ⟨u.1, by
        have := u.2; rw [MonoidHom.mem_ker, powMonoidHom_apply] at this
        simpa using congrArg Units.val this⟩
      left_inv := fun x ↦ by simp
      right_inv := fun u ↦ by ext; simp }

/-! ### Theorems 112 and 113 -/

/-- The roots of `x^{p-1} - 1` modulo `p` are `1, 2, …, p - 1`. -/
lemma roots_X_pow_sub_one_eq (p : ℕ) [hp : Fact p.Prime] :
    ((X : (ZMod p)[X]) ^ (p - 1) - 1).roots = (Icc 1 (p - 1)).val.map (Nat.cast : ℕ → ZMod p) := by
  have hp2 := hp.out.two_le
  have hne := (monic_X_pow_sub_C (1 : ZMod p) (by omega : p - 1 ≠ 0)).ne_zero
  rw [C_1] at hne
  have hnodup : ((Icc 1 (p - 1)).val.map (Nat.cast : ℕ → ZMod p)).Nodup := by
    refine Multiset.Nodup.map_on (fun x hx y hy hxy ↦ ?_) (Icc 1 (p - 1)).nodup
    simp only [Finset.mem_val, Finset.mem_Icc] at hx hy
    rw [← ZMod.val_natCast_of_lt (by omega : x < p), hxy, ZMod.val_natCast_of_lt (by omega)]
  symm
  refine Multiset.eq_of_le_of_card_le ((Multiset.le_iff_subset hnodup).2 fun x hx ↦ ?_) ?_
  · obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.1 hx
    simp only [Finset.mem_val, Finset.mem_Icc] at hi
    rw [mem_roots hne, IsRoot, eval_sub, eval_pow, eval_X, eval_one, sub_eq_zero]
    refine ZMod.pow_card_sub_one_eq_one ?_
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h ↦ absurd (Nat.le_of_dvd (by omega) h) (by omega)
  · rw [Multiset.card_map, Finset.card_val, Nat.card_Icc, Nat.add_sub_cancel]
    refine (card_roots' _).trans ?_
    rw [← C_1, natDegree_X_pow_sub_C]

/-- **Theorem 112** [hardywright2008]: `x^{p-1} - 1 ≡ (x - 1)(x - 2)⋯(x - p + 1) (mod p)`. -/
@[kb "hardywright2008" "Thm 112, p. 109"]
theorem prod_X_sub_C_Icc_eq (p : ℕ) [hp : Fact p.Prime] :
    ∏ i ∈ Icc 1 (p - 1), (X - C (i : ZMod p)) = X ^ (p - 1) - 1 := by
  have hp2 := hp.out.two_le
  have hmon := monic_X_pow_sub_C (1 : ZMod p) (by omega : p - 1 ≠ 0)
  rw [C_1] at hmon
  have hroots := roots_X_pow_sub_one_eq p
  have hcard : ((X : (ZMod p)[X]) ^ (p - 1) - 1).roots.card =
      ((X : (ZMod p)[X]) ^ (p - 1) - 1).natDegree := by
    rw [hroots, ← C_1, natDegree_X_pow_sub_C]; simp
  have := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon hcard
  rw [hroots, Multiset.map_map] at this
  rw [← this, Finset.prod_eq_multiset_prod]
  rfl

/-- The polynomial `(x - 1)(x - 2)⋯(x - (p - 1))` with integer coefficients, whose coefficients are
`±` the numbers `A_l` of [hardywright2008, (7.6.1)]. -/
noncomputable def lagrangePoly (p : ℕ) : ℤ[X] := ∏ i ∈ Icc 1 (p - 1), (X - C (i : ℤ))

lemma lagrangePoly_map (p : ℕ) [Fact p.Prime] :
    (lagrangePoly p).map (Int.castRingHom (ZMod p)) = X ^ (p - 1) - 1 := by
  rw [lagrangePoly, Polynomial.map_prod, ← prod_X_sub_C_Icc_eq]
  simp

/-- **Theorem 113** [hardywright2008]: for a prime `p` the coefficients of `x^1, …, x^{p-2}`
in `(x - 1)(x - 2)⋯(x - (p - 1))` — that is, `A_{p-2}, …, A_1` up to sign — are divisible by `p`. -/
@[kb "hardywright2008" "Thm 113, p. 109"]
theorem prime_dvd_coeff_lagrangePoly (p : ℕ) [hp : Fact p.Prime] {j : ℕ} (hj1 : 1 ≤ j)
    (hj2 : j ≤ p - 2) : (p : ℤ) ∣ (lagrangePoly p).coeff j := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← eq_intCast (Int.castRingHom (ZMod p)), ← coeff_map,
    lagrangePoly_map, coeff_sub, coeff_X_pow, coeff_one, if_neg (by omega), if_neg (by omega),
    sub_zero]

/-- **Theorem 113** [hardywright2008], with the elementary symmetric functions
`A_l = ∑_{i₁ < ⋯ < i_l} i₁ ⋯ i_l` of `1, 2, …, p - 1`: `p ∣ A_l` for `1 ≤ l ≤ p - 2`. -/
@[kb "hardywright2008" "Thm 113, p. 109"]
theorem prime_dvd_esymm (p : ℕ) [hp : Fact p.Prime] {l : ℕ} (hl1 : 1 ≤ l) (hl2 : l ≤ p - 2) :
    (p : ℤ) ∣ ((Icc 1 (p - 1)).val.map (Nat.cast : ℕ → ℤ)).esymm l := by
  have hcard : Multiset.card ((Icc 1 (p - 1)).val.map (Nat.cast : ℕ → ℤ)) = p - 1 := by simp
  have h := Multiset.prod_X_sub_C_coeff ((Icc 1 (p - 1)).val.map (Nat.cast : ℕ → ℤ))
    (k := p - 1 - l) (by omega)
  rw [hcard, Nat.sub_sub_self (by omega), Multiset.map_map] at h
  have h2 := prime_dvd_coeff_lagrangePoly p (j := p - 1 - l) (by omega) (by omega)
  rw [lagrangePoly, Finset.prod_eq_multiset_prod] at h2
  change (p : ℤ) ∣ ((Multiset.map ((fun t ↦ X - C t) ∘ (Nat.cast : ℕ → ℤ))
    (Icc 1 (p - 1)).val).prod.coeff (p - 1 - l)) at h2
  rw [h] at h2
  exact ((isUnit_neg_one (α := ℤ)).pow _).dvd_mul_left.1 h2

/-! ### Theorem 114 -/

/-- **Theorem 114** [hardywright2008]: if `p` is a prime `4n + 3`, then
`((p - 1)/2)! ≡ (-1)^ν (mod p)`, where `ν` is the number of quadratic non-residues of `p` less
than `p/2`. -/
@[kb "hardywright2008" "Thm 114, p. 112"]
theorem half_factorial_eq_neg_one_pow (p : ℕ) [hp : Fact p.Prime] (hp4 : p % 4 = 3) :
    ((((p - 1) / 2).factorial : ℕ) : ZMod p) =
      (-1) ^ #{a ∈ Icc (1 : ℕ) ((p - 1) / 2) | ¬IsSquare ((a : ℕ) : ZMod p)} := by
  classical
  set w := (p - 1) / 2 with hw
  set F : ZMod p := ((w.factorial : ℕ) : ZMod p) with hF
  set ν := #{a ∈ Icc (1 : ℕ) w | ¬IsSquare ((a : ℕ) : ZMod p)} with hν
  have hp2 : p ≠ 2 := by omega
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  -- (7.7.1): `(w!)² ≡ 1`, since `(p - 1)! ≡ (-1)^w (w!)²` and `w` is odd
  have hsq : F ^ 2 = 1 := by
    have h := ZMod.factorial_eq_neg_one_pow_mul_half_factorial_sq hodd
    have hwodd : Odd w := Nat.odd_iff.2 (by omega)
    rw [ZMod.wilsons_lemma, ← hw, hwodd.neg_one_pow, neg_one_mul, neg_inj] at h
    exact h.symm
  have hF1 : F = 1 ∨ F = -1 := mul_self_eq_one_iff.1 (by rw [← sq]; exact hsq)
  -- by Theorem 85, the character of `w! = 1 ⋅ 2 ⋯ w` is `(-1)^ν`
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have hprod : F = ∏ a ∈ Icc 1 w, (a : ZMod p) := by
    rw [hF, ← Nat.cast_prod, ← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_id_eq_factorial]
  have hχ : quadraticChar (ZMod p) F = (-1) ^ ν := by
    rw [hprod, map_prod]
    have : ∀ a ∈ Icc 1 w, quadraticChar (ZMod p) (a : ZMod p) =
        if IsSquare (a : ZMod p) then 1 else -1 := by
      intro a ha
      rw [Finset.mem_Icc] at ha
      have ha0 : (a : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        exact fun h ↦ absurd (Nat.le_of_dvd (by omega) h) (by omega)
      rw [quadraticChar_apply, quadraticCharFun, if_neg ha0]
    rw [Finset.prod_congr rfl this, Finset.prod_ite, Finset.prod_const_one, one_mul,
      Finset.prod_const]
  rcases hF1 with h1 | h1
  · rw [h1, map_one] at hχ
    rw [h1]
    have := congrArg (Int.cast : ℤ → ZMod p) hχ
    push_cast at this
    exact this
  · rw [h1, quadraticChar_neg_one hchar, ZMod.card, ZMod.χ₄_nat_three_mod_four hp4] at hχ
    rw [h1]
    have := congrArg (Int.cast : ℤ → ZMod p) hχ
    push_cast at this
    exact this

/-! ### Theorem 120 -/

/-- **Theorem 120** [hardywright2008] (Rado): if `k` is a prime of the form `3n + 1`, then
`B_k ≡ 1/6 (mod 1)`, where `B_k = (-1)^{k-1} β_{2k}` is the Bernoulli number in the book's
numbering (`β_{2k}` is Mathlib's `bernoulli (2 * k)`). As in the book, it is the case of von
Staudt's theorem (Mathlib's `bernoulli.vonStaudt_clausen`) in which only `p = 2, 3` satisfy
`(p - 1) ∣ 2k`. -/
@[kb "hardywright2008" "Thm 120, p. 118"]
theorem bernoulli_eq_one_sixth_add_int {k : ℕ} (hk : k.Prime) (hk3 : k % 3 = 1) :
    ∃ z : ℤ, (-1 : ℚ) ^ (k - 1) * bernoulli (2 * k) = 1 / 6 + z := by
  have hk7 : 7 ≤ k := by
    have := hk.two_le
    rcases (by omega : k = 4 ∨ 7 ≤ k) with h | h
    · subst h; exact absurd hk (by decide)
    · exact h
  have hkodd : k % 2 = 1 := Nat.odd_iff.1 (hk.odd_of_ne_two (by omega))
  -- `(p - 1) ∣ 2k` with `p` prime only for `p = 2, 3` (`k + 1` is even, `3 ∣ 2k + 1`)
  have hset : ((range (2 * k + 2)).filter fun p ↦ p.Prime ∧ (p - 1) ∣ 2 * k) = {2, 3} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hp1, hp, hd⟩
      obtain ⟨d₁, d₂, h₁, h₂, hd₁₂⟩ := Nat.dvd_mul.1 hd
      have hd₁ : d₁ = 1 ∨ d₁ = 2 := (Nat.dvd_prime Nat.prime_two).1 h₁
      have hd₂ : d₂ = 1 ∨ d₂ = k := (Nat.dvd_prime hk).1 h₂
      have hp2 := hp.two_le
      rcases hd₁ with e1 | e1 <;> rcases hd₂ with e2 | e2 <;> rw [e1, e2] at hd₁₂
      · left; omega
      · -- `p = k + 1` is even
        exfalso
        have : 2 ∣ p := ⟨(k + 1) / 2, by omega⟩
        rcases (Nat.dvd_prime hp).1 this with h | h <;> omega
      · right; omega
      · -- `p = 2k + 1` is divisible by `3`
        exfalso
        have : 3 ∣ p := ⟨(2 * k + 1) / 3, by omega⟩
        rcases (Nat.dvd_prime hp).1 this with h | h <;> omega
    · rintro (rfl | rfl)
      · exact ⟨by omega, Nat.prime_two, by simp⟩
      · exact ⟨by omega, Nat.prime_three, ⟨k, by ring⟩⟩
  obtain ⟨m, hm⟩ := Bernoulli.vonStaudt_clausen k
  rw [hset, Finset.sum_pair (by norm_num)] at hm
  refine ⟨m - 1, ?_⟩
  rw [show k - 1 = 2 * ((k - 1) / 2) by omega, pow_mul, neg_one_sq, one_pow, one_mul]
  push_cast at hm ⊢
  linarith

end NTKB.HardyWright
