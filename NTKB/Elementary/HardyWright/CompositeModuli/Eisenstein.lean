/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Choose.Sum
import NTKB.Elementary.HardyWright.Congruences.Wolstenholme

/-!
# The residues of `2^{p-1}` and `(p - 1)!` modulo `p²` (Hardy–Wright, § 8.9)

* Theorem 132 (Eisenstein): for an odd prime `p`,
  `(2^{p-1} - 1)/p ≡ 1 + 1/3 + 1/5 + ⋯ + 1/(p - 2) (mod p)`, the fractions being associates
  modulo `p`; that is, `2^{p-1} ≡ 1 + p (1 + 1/3 + ⋯ + 1/(p - 2)) (mod p²)`.
* Theorem 133: for an odd prime `p`, `(p - 1)! ≡ (-1)^{(p-1)/2} 2^{2p-2} (((p - 1)/2)!)² (mod p²)`.
-/

open Finset

namespace NTKB.HardyWright

/-- `C(p - 1, k) ≡ (-1)^k (mod p)` for `k ≤ p - 1`. -/
lemma choose_pred_eq_neg_one_pow (p : ℕ) [hp : Fact p.Prime] {k : ℕ} (hk : k ≤ p - 1) :
    (((p - 1).choose k : ℕ) : ZMod p) = (-1) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := Nat.choose_succ_succ' (p - 1) k
    rw [Nat.sub_add_cancel hp.out.one_lt.le] at h
    have h0 : ((p.choose (k + 1) : ℕ) : ZMod p) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact hp.out.dvd_choose_self (by omega) (by omega)
    rw [h, Nat.cast_add, ih (by omega)] at h0
    rw [pow_succ]
    linear_combination h0

/-- `C(p, l) / p ≡ (-1)^{l-1}/l (mod p)` for `0 < l < p`. -/
lemma choose_div_prime_eq (p : ℕ) [hp : Fact p.Prime] {l : ℕ} (hl : l ∈ Icc 1 (p - 1)) :
    ((p.choose l / p : ℕ) : ZMod p) = (-1) ^ (l - 1) * (l : ZMod p)⁻¹ := by
  rw [Finset.mem_Icc] at hl
  have hdvd : p ∣ p.choose l := hp.out.dvd_choose_self (by omega) (by omega)
  -- `l C(p, l) = p C(p - 1, l - 1)`
  have h := Nat.add_one_mul_choose_eq (p - 1) (l - 1)
  rw [Nat.sub_add_cancel hp.out.one_lt.le, Nat.sub_add_cancel hl.1] at h
  have h2 : l * (p.choose l / p) = (p - 1).choose (l - 1) := by
    have hp0 := hp.out.pos
    apply Nat.eq_of_mul_eq_mul_left hp0
    rw [h, ← mul_assoc, mul_comm p l, mul_assoc, Nat.mul_div_cancel' hdvd, mul_comm]
  have hu : (l : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h ↦ absurd (Nat.le_of_dvd (by omega) h) (by omega)
  have h3 := congrArg (Nat.cast : ℕ → ZMod p) h2
  rw [Nat.cast_mul, choose_pred_eq_neg_one_pow p (by omega)] at h3
  rw [← h3]
  field_simp

/-- **Theorem 132** [hardywright2008] (Eisenstein): for an odd prime `p`,
`(2^{p-1} - 1)/p ≡ 1 + 1/3 + 1/5 + ⋯ + 1/(p - 2) (mod p)`, the fractions being associates
modulo `p`. Following the book: `2^p - 2 = ∑_{0<l<p} C(p, l)` with `C(p, l)/p ≡ (-1)^{l-1}/l`, and
`1 + 1/2 + ⋯ + 1/(p - 1) ≡ 0` by (7.8.2). -/
@[kb "hardywright2008" "Thm 132, p. 135"]
theorem fermatQuotient_two_eq (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    (((2 ^ (p - 1) - 1) / p : ℕ) : ZMod p) = ∑ l ∈ (Icc 1 (p - 2)).filter Odd, (l : ZMod p)⁻¹ := by
  classical
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have hodd : p % 2 = 1 := Nat.odd_iff.1 (hp.out.odd_of_ne_two hp2)
  set Q := (2 ^ (p - 1) - 1) / p with hQ
  have hdvdQ : p ∣ 2 ^ (p - 1) - 1 := by
    have := ZMod.pow_card_sub_one_eq_one (p := p) (a := 2) (by
      rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_num, Ne, ZMod.natCast_eq_zero_iff]
      exact fun h ↦ absurd (Nat.le_of_dvd (by norm_num) h) (by omega))
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub Nat.one_le_two_pow]
    push_cast; rw [this, sub_self]
  -- `2 Q = ∑_{0<l<p} C(p, l)/p`
  have hsum : 2 * Q = ∑ l ∈ Icc 1 (p - 1), p.choose l / p := by
    have h1 := Nat.sum_range_choose p
    have h2 : ∑ l ∈ range (p + 1), p.choose l = ∑ l ∈ Icc 1 (p - 1), p.choose l + 2 := by
      rw [Finset.sum_range_succ, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
      rw [show Ico (0 + 1) p = Icc 1 (p - 1) by ext; simp; omega]
      simp; ring
    have h3 : ∑ l ∈ Icc 1 (p - 1), p.choose l = p * ∑ l ∈ Icc 1 (p - 1), p.choose l / p := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l hl ↦ ?_
      rw [Finset.mem_Icc] at hl
      exact (Nat.mul_div_cancel' (hp.out.dvd_choose_self (by omega) (by omega))).symm
    have h4 : 2 ^ p = 2 * (p * Q) + 2 := by
      rw [hQ, Nat.mul_div_cancel' hdvdQ, Nat.mul_sub, mul_one, ← pow_succ',
        Nat.sub_add_cancel hp.out.one_lt.le]
      have : 2 ≤ 2 ^ p := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have : p * (2 * Q) = p * ∑ l ∈ Icc 1 (p - 1), p.choose l / p := by
      rw [← h3]; linarith
    exact Nat.eq_of_mul_eq_mul_left hp.out.pos this
  -- reduce modulo `p`
  have h2 : (2 : ZMod p) ≠ 0 := by
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_num, Ne, ZMod.natCast_eq_zero_iff]
    exact fun h ↦ absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
  have hcast := congrArg (Nat.cast : ℕ → ZMod p) hsum
  rw [Nat.cast_mul, Nat.cast_sum, Finset.sum_congr rfl fun l hl ↦ choose_div_prime_eq p hl] at hcast
  -- `(-1)^{l-1}/l = 2 [l odd]/l - 1/l`, and `∑ 1/l = 0`
  have hsplit : ∀ l ∈ Icc 1 (p - 1), (-1 : ZMod p) ^ (l - 1) * (l : ZMod p)⁻¹ =
      2 * (if Odd l then (l : ZMod p)⁻¹ else 0) - (l : ZMod p)⁻¹ := by
    intro l hl
    rw [Finset.mem_Icc] at hl
    rcases Nat.even_or_odd l with h | h
    · rw [if_neg (Nat.not_odd_iff_even.2 h), (Nat.Even.sub_odd (by omega) h odd_one).neg_one_pow]
      ring
    · rw [if_pos h, (Nat.Odd.sub_odd h odd_one).neg_one_pow]; ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_inv_eq_zero_mod_prime p hp2, sub_zero, ← Finset.sum_filter] at hcast
  have hfilt : (Icc 1 (p - 1)).filter Odd = (Icc 1 (p - 2)).filter Odd := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨⟨h1, ?_⟩, h3⟩
      rcases Nat.lt_or_ge l (p - 1) with h | h; · omega
      exfalso
      have : l = p - 1 := by omega
      rw [this] at h3
      exact Nat.not_odd_iff_even.2 (Nat.Odd.sub_odd (Nat.odd_iff.2 hodd) odd_one) h3
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, by omega⟩, h3⟩
  rw [hfilt] at hcast
  exact mul_left_cancel₀ h2 hcast

/-! ### Theorem 133 -/

/-- First-order expansion: if `ε² = 0`, then
`∏ (a_i + ε) = ∏ a_i + ε ∑_i ∏_{j ≠ i} a_j`. -/
lemma prod_add_of_sq_eq_zero {R ι : Type*} [CommRing R] [DecidableEq ι] {ε : R} (hε : ε ^ 2 = 0)
    (s : Finset ι) (a : ι → R) :
    ∏ i ∈ s, (a i + ε) = ∏ i ∈ s, a i + ε * ∑ i ∈ s, ∏ j ∈ s.erase i, a j := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, Finset.prod_insert hb, ih, Finset.sum_insert hb,
      Finset.erase_insert hb]
    have : ∀ i ∈ s, ∏ j ∈ (insert b s).erase i, a j = a b * ∏ j ∈ s.erase i, a j := by
      intro i hi
      rw [Finset.erase_insert_of_ne (fun h : b = i ↦ hb (h ▸ hi)), Finset.prod_insert
        (fun h ↦ hb (Finset.mem_of_mem_erase h))]
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
    linear_combination (∑ i ∈ s, ∏ j ∈ s.erase i, a j) * hε

/-- `1 + 1/2 + ⋯ + 1/n ≡ -2 (2^{p-1} - 1)/p (mod p)` for `p = 2n + 1`: by (7.8.2) and Theorem 132,
the even terms of `∑ 1/l` are `-(1 + 1/3 + ⋯ + 1/(p - 2))`. -/
lemma sum_inv_half_eq (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    ∑ i ∈ Icc 1 ((p - 1) / 2), (i : ZMod p)⁻¹ =
      -2 * (((2 ^ (p - 1) - 1) / p : ℕ) : ZMod p) := by
  classical
  have hodd : p % 2 = 1 := Nat.odd_iff.1 (hp.out.odd_of_ne_two hp2)
  set n := (p - 1) / 2 with hn
  have h2 : (2 : ZMod p) ≠ 0 := by
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_num, Ne, ZMod.natCast_eq_zero_iff]
    exact fun h ↦ absurd (Nat.le_of_dvd (by norm_num) h) (by have := hp.out.two_le; omega)
  have hH := sum_inv_eq_zero_mod_prime p hp2
  rw [← Finset.sum_filter_add_sum_filter_not _ Odd] at hH
  have hO := fermatQuotient_two_eq p hp2
  have hfilt : (Icc 1 (p - 1)).filter Odd = (Icc 1 (p - 2)).filter Odd := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.odd_iff]
    omega
  rw [hfilt, ← hO] at hH
  -- the even `l = 2i`, `1 ≤ i ≤ n`
  have himage : (Icc 1 (p - 1)).filter (fun l ↦ ¬Odd l) = (Icc 1 n).image (2 * ·) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Nat.not_odd_iff_even,
      Nat.even_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨l / 2, ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨i, ⟨h1, h2⟩, rfl⟩; exact ⟨⟨by omega, by omega⟩, by omega⟩
  rw [himage, Finset.sum_image (fun x _ y _ h ↦ by simpa using h)] at hH
  have : ∑ i ∈ Icc 1 n, (((2 * i : ℕ) : ZMod p))⁻¹ = 2⁻¹ * ∑ i ∈ Icc 1 n, (i : ZMod p)⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    push_cast; rw [mul_inv]
  rw [this] at hH
  have h22 : (2 : ZMod p) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  linear_combination 2 * hH - (∑ i ∈ Icc 1 n, (i : ZMod p)⁻¹) * h22

/-- **Theorem 133** [hardywright2008]: for an odd prime `p`,
`(p - 1)! ≡ (-1)^{(p-1)/2} 2^{2p-2} (((p - 1)/2)!)² (mod p²)`. With `p = 2n + 1`: modulo `p²`,
`(p - 1)(p - 2)⋯(p - n) ≡ (-1)^n n! (1 - p (1 + 1/2 + ⋯ + 1/n))`, and
`1 + 1/2 + ⋯ + 1/n ≡ -2 (2^{p-1} - 1)/p (mod p)` by (7.8.2) and Theorem 132, while
`2^{2p-2} ≡ 1 + 2 (2^{p-1} - 1) (mod p²)`. (The book argues with the odd numbers
`(p - 2)(p - 4)⋯(p - 2n)`; the ingredients are the same.) -/
@[kb "hardywright2008" "Thm 133, p. 135"]
theorem factorial_eq_mod_prime_sq (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    (((p - 1).factorial : ℕ) : ZMod (p ^ 2)) =
      (-1) ^ ((p - 1) / 2) * 2 ^ (2 * p - 2) * ((((p - 1) / 2).factorial : ℕ) : ZMod (p ^ 2)) ^ 2 := by
  classical
  have hodd : p % 2 = 1 := Nat.odd_iff.1 (hp.out.odd_of_ne_two hp2)
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  set n := (p - 1) / 2 with hn
  have hn1 : 1 ≤ n := by omega
  have hp2n : p = 2 * n + 1 := by omega
  set Q := (2 ^ (p - 1) - 1) / p with hQ
  have hdvdQ : p ∣ 2 ^ (p - 1) - 1 := by
    have := ZMod.pow_card_sub_one_eq_one (p := p) (a := 2) (by
      rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_num, Ne, ZMod.natCast_eq_zero_iff]
      exact fun h ↦ absurd (Nat.le_of_dvd (by norm_num) h) (by omega))
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub Nat.one_le_two_pow]
    push_cast; rw [this, sub_self]
  have h2pow : 2 ^ (p - 1) = 1 + p * Q := by
    rw [hQ, Nat.mul_div_cancel' hdvdQ]; have := Nat.one_le_two_pow (n := p - 1); omega
  -- `(p - 1)! = n! ⋅ (p - 1)(p - 2)⋯(p - n)`
  have hsplit : (p - 1).factorial = n.factorial * ∏ i ∈ Icc 1 n, (p - i) := by
    have e1 : ∏ i ∈ Icc 1 n, (p - i) = ∏ j ∈ Ico (n + 1) p, j := by
      rw [← Finset.Ico_add_one_right_eq_Icc,
        Finset.prod_Ico_reflect (fun j ↦ j) 1 (by omega : n + 1 ≤ p + 1)]
      congr 1; ext; simp; omega
    rw [e1, ← Finset.prod_Ico_id_eq_factorial, ← Finset.prod_Ico_id_eq_factorial,
      Nat.sub_add_cancel (by omega : 1 ≤ p), Finset.prod_Ico_consecutive _ (by omega) (by omega)]
  set R := ZMod (p ^ 2)
  have hpp : (p : R) ^ 2 = 0 := by exact_mod_cast ZMod.natCast_self (p ^ 2)
  have hprodn : ∏ i ∈ Icc 1 n, (i : R) = (n.factorial : R) := by
    rw [← Nat.cast_prod, ← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_id_eq_factorial]
  -- first-order expansion of `∏ (p - i)` modulo `p²`
  set T : ℕ := ∑ i ∈ Icc 1 n, ∏ j ∈ (Icc 1 n).erase i, j with hT
  have hexp : ∏ i ∈ Icc 1 n, ((p - i : ℕ) : R) =
      (-1) ^ n * (n.factorial : R) + (p : R) * ((-1) ^ (n - 1) * (T : R)) := by
    have : ∀ i ∈ Icc 1 n, ((p - i : ℕ) : R) = -(i : R) + p := by
      intro i hi; rw [Finset.mem_Icc] at hi; rw [Nat.cast_sub (by omega)]; ring
    have hneg1 : ∀ s : Finset ℕ, ∏ i ∈ s, (-(i : R)) = (-1) ^ s.card * ∏ i ∈ s, (i : R) := by
      intro s
      rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ ↦ by ring
    rw [Finset.prod_congr rfl this, prod_add_of_sq_eq_zero hpp]
    congr 1
    · rw [hneg1, Nat.card_Icc, Nat.add_sub_cancel, hprodn]
    · congr 1
      rw [hT, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [hneg1, Finset.card_erase_of_mem hi, Nat.card_Icc, Nat.add_sub_cancel, Nat.cast_prod]

  -- `T ≡ n! (1 + 1/2 + ⋯ + 1/n) ≡ -2 Q n! (mod p)`
  have hTp : (T : ZMod p) = ((n.factorial : ℕ) : ZMod p) * (-2 * (Q : ZMod p)) := by
    rw [← sum_inv_half_eq p hp2, ← hn, Finset.mul_sum, hT, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have h := Finset.prod_erase_mul (Icc 1 n) (fun j : ℕ ↦ (j : ZMod p)) hi
    have hfact : ∏ j ∈ Icc 1 n, (j : ZMod p) = ((n.factorial : ℕ) : ZMod p) := by
      rw [← Nat.cast_prod, ← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_id_eq_factorial]
    rw [hfact] at h
    rw [Finset.mem_Icc] at hi
    have hu : (i : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact fun h ↦ absurd (Nat.le_of_dvd (by omega) h) (by omega)
    rw [← h, Nat.cast_prod, mul_assoc, mul_inv_cancel₀ hu, mul_one]
  -- hence `p T ≡ -2 p Q n! (mod p²)`
  have hpT : (p : R) * (T : R) = (p : R) * ((n.factorial : R) * (-2 * (Q : R))) := by
    have hd : (p : ℤ) ∣ (T : ℤ) - (n.factorial : ℤ) * (-2 * (Q : ℤ)) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hTp, sub_self]
    obtain ⟨c, hc⟩ := hd
    have : (T : R) = (n.factorial : R) * (-2 * (Q : R)) + (p : R) * c := by
      have := congrArg (Int.cast : ℤ → R) hc
      push_cast at this
      linear_combination this
    rw [this]
    linear_combination (c : R) * hpp
  have h2R : (2 : R) ^ (p - 1) = 1 + (p : R) * Q := by exact_mod_cast congrArg (Nat.cast (R := R)) h2pow
  have hcast := congrArg (Nat.cast (R := R)) hsplit
  rw [Nat.cast_mul, Nat.cast_prod, hexp] at hcast
  rw [hcast, show 2 * p - 2 = (p - 1) * 2 by omega, pow_mul, h2R]
  have hneg : ((-1 : R) ^ n) = -(-1) ^ (n - 1) := by
    obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [hm, Nat.add_sub_cancel, pow_succ]; ring
  rw [hneg]
  linear_combination ((-1 : R) ^ (n - 1) * (n.factorial : R)) * hpT +
    ((-1 : R) ^ (n - 1) * (n.factorial : R) ^ 2 * (Q : R) ^ 2) * hpp

end NTKB.HardyWright
