/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Data.Nat.Prime.Factorial
import NTKB.Elementary.HardyWright.Congruences.Lagrange

/-!
# Wolstenholme's theorem (Hardy–Wright, § 7.8)

* (7.8.2): `1/1 + 1/2 + ⋯ + 1/(p - 1) ≡ 0 (mod p)` for an odd prime `p`, `1/i` being the associate
  of `i` modulo `p`.
* Theorem 115 (Wolstenholme): if `p > 3`, the numerator of `1 + 1/2 + ⋯ + 1/(p - 1)` is divisible by
  `p²`.
* Theorem 116: the same with associates modulo `p²`.
* Theorem 117: if `p > 3`, the numerator of `1 + 1/2² + ⋯ + 1/(p - 1)²` is divisible by `p`.

Following the book, put `x = p` in `(x - 1)(x - 2)⋯(x - (p - 1)) = x^{p-1} - A_1 x^{p-2} + ⋯ + A_{p-1}`
(`lagrangePoly p`): since `A_{p-1} = (p - 1)!` and `p ∣ A_1, …, A_{p-3}` (Theorem 113), `p² ∣ A_{p-2}`,
and `A_{p-2} = (p - 1)! (1 + 1/2 + ⋯ + 1/(p - 1))`.
-/

open Polynomial Finset

namespace NTKB.HardyWright

/-- `A_{p-2} = ∑_i ∏_{j ≠ i} j`, the sum of the products of `p - 2` of the numbers `1, …, p - 1`. -/
def wolstenholmeNum (p : ℕ) : ℤ := ∑ a ∈ Icc 1 (p - 1), ∏ b ∈ (Icc 1 (p - 1)).erase a, (b : ℤ)

lemma lagrangePoly_monic (p : ℕ) : (lagrangePoly p).Monic :=
  monic_prod_of_monic _ _ fun _ _ ↦ monic_X_sub_C _

lemma lagrangePoly_natDegree (p : ℕ) : (lagrangePoly p).natDegree = p - 1 := by
  rw [lagrangePoly, natDegree_prod_of_monic _ _ fun _ _ ↦ monic_X_sub_C _]
  simp only [natDegree_X_sub_C, Finset.sum_const, Nat.card_Icc, smul_eq_mul, mul_one]
  omega

lemma prod_Icc_id (p : ℕ) : ∏ b ∈ Icc 1 (p - 1), b = (p - 1).factorial := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_id_eq_factorial]

/-- `(p - 1)(p - 2)⋯1 = (p - 1)!`: the value of `lagrangePoly p` at `p`. -/
lemma lagrangePoly_eval_self (p : ℕ) (hp : 1 ≤ p) :
    (lagrangePoly p).eval (p : ℤ) = ((p - 1).factorial : ℕ) := by
  rw [lagrangePoly, eval_prod]
  have h1 : ∀ i ∈ Icc 1 (p - 1), eval (p : ℤ) (X - C (i : ℤ)) = ((p - i : ℕ) : ℤ) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    simp [Nat.cast_sub (by omega : i ≤ p)]
  rw [Finset.prod_congr rfl h1, ← Nat.cast_prod]
  congr 1
  have hIcc : Icc 1 (p - 1) = Ico 1 p := by ext; simp; omega
  rw [hIcc, Finset.prod_Ico_reflect (fun j ↦ j) 1 (Nat.le_succ p), Nat.add_sub_cancel,
    show p + 1 - p = 1 by omega, ← hIcc,
    prod_Icc_id]

/-- The value at `0` is `(-1)^{p-1} (p - 1)!`. -/
lemma lagrangePoly_eval_zero (p : ℕ) :
    (lagrangePoly p).eval 0 = (-1) ^ (p - 1) * ((p - 1).factorial : ℕ) := by
  rw [lagrangePoly, eval_prod]
  have : ∀ i ∈ Icc 1 (p - 1), eval 0 (X - C (i : ℤ)) = (-1) * (i : ℤ) := by
    intro i _; simp
  rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc,
    Nat.add_sub_cancel, ← Nat.cast_prod, prod_Icc_id]

/-- The coefficient of `x` in `lagrangePoly p` is `-A_{p-2}` (for odd `p`). -/
lemma lagrangePoly_coeff_one (p : ℕ) (hp : Odd p) :
    (lagrangePoly p).coeff 1 = -wolstenholmeNum p := by
  classical
  have h := coeff_derivative (lagrangePoly p) 0
  simp only [zero_add, Nat.cast_zero, mul_one] at h
  rw [← h, coeff_zero_eq_eval_zero, lagrangePoly, derivative_prod_finset, eval_finsetSum,
    wolstenholmeNum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  rw [derivative_sub, derivative_X, derivative_C, sub_zero, mul_one, eval_prod]
  have : ∀ i ∈ (Icc 1 (p - 1)).erase a, eval 0 (X - C (i : ℤ)) = (-1) * (i : ℤ) := by
    intro i _; simp
  rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_erase_of_mem ha, Nat.card_Icc, Nat.add_sub_cancel]
  obtain ⟨k, rfl⟩ := hp
  rw [show 2 * k + 1 - 1 - 1 = 2 * k - 1 by omega]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp at ha
  · rw [Odd.neg_one_pow ⟨k - 1, by omega⟩]; ring

/-- `p² ∣ A_{p-2}` for `p > 3`: the heart of Wolstenholme's theorem. -/
theorem prime_sq_dvd_wolstenholmeNum (p : ℕ) [hp : Fact p.Prime] (hp3 : 3 < p) :
    (p : ℤ) ^ 2 ∣ wolstenholmeNum p := by
  have hodd : Odd p := hp.out.odd_of_ne_two (by omega)
  set c := (lagrangePoly p).coeff with hc
  -- `(p - 1)! = ∑_j c_j p^j` and `c_0 = (p - 1)!`
  have heval := lagrangePoly_eval_self p (by omega)
  rw [eval_eq_sum_range, lagrangePoly_natDegree, Nat.sub_add_cancel (by omega)] at heval
  have hc0 : c 0 = ((p - 1).factorial : ℕ) := by
    rw [hc, coeff_zero_eq_eval_zero, lagrangePoly_eval_zero,
      (Nat.Odd.sub_odd hodd odd_one).neg_one_pow, one_mul]
  obtain ⟨n, hn⟩ : ∃ n, p = n + 2 := ⟨p - 2, by omega⟩
  rw [hn, Finset.sum_range_succ', Finset.sum_range_succ', ← hn] at heval
  simp only [zero_add, pow_zero, mul_one, pow_one, ← hc] at heval
  rw [hc0, add_eq_right] at heval
  -- every term `c_j p^j` with `j ≥ 2` is divisible by `p³`
  have hterms : (p : ℤ) ^ 3 ∣ ∑ k ∈ range n, c (k + 1 + 1) * (p : ℤ) ^ (k + 1 + 1) := by
    refine Finset.dvd_sum fun k hk ↦ ?_
    rw [Finset.mem_range] at hk
    rcases Nat.lt_or_ge (k + 2) (p - 1) with h | h
    · -- `p ∣ c_{k+2}` by Theorem 113
      have h113 := prime_dvd_coeff_lagrangePoly p (j := k + 1 + 1) (by omega) (by omega)
      have := mul_dvd_mul h113 (pow_dvd_pow (p : ℤ) (by omega : 2 ≤ k + 1 + 1))
      rw [← pow_succ'] at this
      exact this

    · -- the leading coefficient `c_{p-1} = 1`, and `p - 1 ≥ 3`
      exact dvd_mul_of_dvd_right (pow_dvd_pow _ (by omega)) _
  have h1 : (p : ℤ) ^ 3 ∣ c 1 * p := by
    have : c 1 * p = -(∑ k ∈ range n, c (k + 1 + 1) * (p : ℤ) ^ (k + 1 + 1)) := by linarith
    rw [this]; exact (dvd_neg).2 hterms
  have h2 : (p : ℤ) ^ 2 ∣ c 1 := by
    rw [pow_succ] at h1
    exact (mul_dvd_mul_iff_right (by exact_mod_cast hp.out.ne_zero)).1 h1
  rw [hc, lagrangePoly_coeff_one p hodd, dvd_neg] at h2
  exact h2

/-- If `q D = N` with `D, N` integers, `k ∣ N` and `k` prime to `D`, then `k` divides the numerator
of `q`. -/
lemma dvd_num_of_mul_eq {q : ℚ} {D N k : ℤ} (h : q * D = N) (hkN : k ∣ N) (hkD : IsCoprime k D) :
    k ∣ q.num := by
  have : q.num * D = N * q.den := by
    have e := Rat.mul_den_eq_num q
    have : ((q.num * D : ℤ) : ℚ) = ((N * q.den : ℤ) : ℚ) := by
      push_cast; rw [← e, ← h]; ring
    exact_mod_cast this
  exact hkD.dvd_of_dvd_mul_right (this ▸ dvd_mul_of_dvd_left hkN _)

lemma isCoprime_prime_pow_factorial (p : ℕ) (hp : p.Prime) (e : ℕ) :
    IsCoprime ((p : ℤ) ^ e) (((p - 1).factorial : ℕ) : ℤ) := by
  have : Nat.Coprime p (p - 1).factorial :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 fun h ↦ by
      have := (Nat.Prime.dvd_factorial hp).1 h; have := hp.one_lt; omega
  exact_mod_cast Nat.isCoprime_iff_coprime.2 (this.pow_left e)

/-- `(p - 1)! (1 + 1/2 + ⋯ + 1/(p - 1)) = A_{p-2}`. -/
lemma factorial_mul_harmonic (p : ℕ) :
    (∑ a ∈ Icc 1 (p - 1), (1 : ℚ) / a) * ((((p - 1).factorial : ℕ) : ℤ) : ℚ) =
      wolstenholmeNum p := by
  classical
  rw [wolstenholmeNum, Finset.sum_mul]
  push_cast
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  have ha0 : (a : ℚ) ≠ 0 := by rw [Finset.mem_Icc] at ha; exact_mod_cast (by omega : a ≠ 0)
  have h := Finset.prod_erase_mul (Icc 1 (p - 1)) (fun b : ℕ ↦ (b : ℚ)) ha
  have hfact : ∏ b ∈ Icc 1 (p - 1), (b : ℚ) = (((p - 1).factorial : ℕ) : ℚ) := by
    rw [← Nat.cast_prod, prod_Icc_id]
  rw [← hfact, ← h]
  field_simp

/-- **Theorem 115** [hardywright2008] (Wolstenholme): if `p > 3` is prime, the numerator of
`1 + 1/2 + 1/3 + ⋯ + 1/(p - 1)` is divisible by `p²`. -/
@[kb "hardywright2008" "Thm 115, p. 112"]
theorem prime_sq_dvd_num_harmonic (p : ℕ) [hp : Fact p.Prime] (hp3 : 3 < p) :
    (p : ℤ) ^ 2 ∣ (∑ a ∈ Icc 1 (p - 1), (1 : ℚ) / a).num :=
  dvd_num_of_mul_eq (factorial_mul_harmonic p) (prime_sq_dvd_wolstenholmeNum p hp3)
    (isCoprime_prime_pow_factorial p hp.out 2)

/-! ### Associates: (7.8.2) and Theorem 116 -/

lemma isUnit_natCast_of_lt {p m a : ℕ} (hp : p.Prime) (hm : ∃ e, m = p ^ e)
    (ha : a ∈ Icc 1 (p - 1)) : IsUnit (a : ZMod m) := by
  obtain ⟨e, rfl⟩ := hm
  rw [Finset.mem_Icc] at ha
  refine (ZMod.isUnit_iff_coprime _ _).2 (Nat.Coprime.pow_right _ ?_)
  exact (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h ↦ by
    have := Nat.le_of_dvd (by omega) h; omega))

/-- Modulo `m = p^e`, `A_{p-2} ≡ (p - 1)! (1/1 + 1/2 + ⋯ + 1/(p - 1))` with associates `1/i`. -/
lemma wolstenholmeNum_cast {p m : ℕ} (hp : p.Prime) (hm : ∃ e, m = p ^ e) :
    ((wolstenholmeNum p : ℤ) : ZMod m) =
      (((p - 1).factorial : ℕ) : ZMod m) * ∑ a ∈ Icc 1 (p - 1), (a : ZMod m)⁻¹ := by
  classical
  rw [wolstenholmeNum, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  have h := Finset.prod_erase_mul (Icc 1 (p - 1)) (fun b : ℕ ↦ (b : ZMod m)) ha
  have hfact : ∏ x ∈ Icc 1 (p - 1), (x : ZMod m) = (((p - 1).factorial : ℕ) : ZMod m) := by
    rw [← Nat.cast_prod, prod_Icc_id]
  rw [hfact] at h
  rw [← h, mul_assoc, ZMod.mul_inv_of_unit _ (isUnit_natCast_of_lt hp hm ha), mul_one]

lemma isUnit_factorial {p m : ℕ} (hp : p.Prime) (hm : ∃ e, m = p ^ e) :
    IsUnit (((p - 1).factorial : ℕ) : ZMod m) := by
  obtain ⟨e, rfl⟩ := hm
  refine (ZMod.isUnit_iff_coprime _ _).2 (Nat.Coprime.pow_right _ ?_)
  exact (Nat.Prime.coprime_iff_not_dvd hp).2 (fun h ↦ by
    have := (Nat.Prime.dvd_factorial hp).1 h; have := hp.one_lt; omega) |> Nat.coprime_comm.1

lemma sum_inv_eq_zero_of_dvd {p m : ℕ} (hp : p.Prime) (hm : ∃ e, m = p ^ e)
    (h : (m : ℤ) ∣ wolstenholmeNum p) : ∑ a ∈ Icc 1 (p - 1), (a : ZMod m)⁻¹ = 0 := by
  have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h
  rw [wolstenholmeNum_cast hp hm] at h0
  exact (isUnit_factorial hp hm).mul_right_eq_zero.1 h0

/-- [hardywright2008, (7.8.2)]: for an odd prime `p`, `1/1 + 1/2 + ⋯ + 1/(p - 1) ≡ 0 (mod p)`,
`1/i` being the associate of `i` modulo `p`. (The book pairs `1/i` with `1/(p - i)`; here it is
the case `j = 1` of Theorem 113.) -/
@[kb "hardywright2008" "(7.8.2), p. 113"]
theorem sum_inv_eq_zero_mod_prime (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    ∑ a ∈ Icc 1 (p - 1), (a : ZMod p)⁻¹ = 0 := by
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  have h113 := prime_dvd_coeff_lagrangePoly p (j := 1) le_rfl
    (by have := hp.out.two_le; omega)
  rw [lagrangePoly_coeff_one p hodd, dvd_neg] at h113
  exact sum_inv_eq_zero_of_dvd hp.out ⟨1, (pow_one p).symm⟩ h113

/-- **Theorem 116** [hardywright2008]: if `p > 3` and `1/i` is the associate of `i` modulo `p²`,
then `1/1 + 1/2 + ⋯ + 1/(p - 1) ≡ 0 (mod p²)`. -/
@[kb "hardywright2008" "Thm 116, p. 113"]
theorem sum_inv_eq_zero_mod_prime_sq (p : ℕ) [hp : Fact p.Prime] (hp3 : 3 < p) :
    ∑ a ∈ Icc 1 (p - 1), (a : ZMod (p ^ 2))⁻¹ = 0 :=
  sum_inv_eq_zero_of_dvd hp.out ⟨2, rfl⟩ (by simpa using prime_sq_dvd_wolstenholmeNum p hp3)

/-! ### Theorem 117 -/

/-- A sum over `1, …, p - 1` of a function vanishing at `0` is the sum over `ZMod p`. -/
lemma sum_Icc_eq_sum_zmod {M : Type*} [AddCommMonoid M] (p : ℕ) [hp : Fact p.Prime]
    (g : ZMod p → M) (hg : g 0 = 0) :
    ∑ a ∈ Icc 1 (p - 1), g (a : ZMod p) = ∑ x, g x := by
  classical
  have himage : (Icc 1 (p - 1)).image (Nat.cast : ℕ → ZMod p) = Finset.univ.erase 0 := by
    ext x
    simp only [Finset.mem_image, Finset.mem_Icc, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact fun h ↦ absurd (Nat.le_of_dvd (by omega) h) (by omega)
    · intro hx
      refine ⟨x.val, ⟨?_, ?_⟩, ZMod.natCast_zmod_val x⟩
      · exact Nat.one_le_iff_ne_zero.2 ((ZMod.val_ne_zero x).2 hx)
      · have := ZMod.val_lt x; omega
  have hinj : Set.InjOn (Nat.cast : ℕ → ZMod p) (Icc 1 (p - 1) : Set ℕ) := by
    intro x hx y hy hxy
    simp only [Finset.coe_Icc, Set.mem_Icc] at hx hy
    have hp2 := hp.out.two_le
    rw [← ZMod.val_natCast_of_lt (by omega : x < p), hxy, ZMod.val_natCast_of_lt (by omega)]
  rw [← Finset.sum_image (f := g) hinj, himage, Finset.sum_erase _ hg]

/-- **Theorem 117** [hardywright2008]: if `p > 3` is prime, the numerator of
`1 + 1/2² + 1/3² + ⋯ + 1/(p - 1)²` is divisible by `p`. (The book writes the numerator as
`A_{p-2}² - 2 A_{p-1} A_{p-3}`; here `∑ 1/i² ≡ ∑ i² ≡ 0 (mod p)` with associates.) -/
@[kb "hardywright2008" "Thm 117, p. 114"]
theorem prime_dvd_num_sum_inv_sq (p : ℕ) [hp : Fact p.Prime] (hp3 : 3 < p) :
    (p : ℤ) ∣ (∑ a ∈ Icc 1 (p - 1), (1 : ℚ) / a ^ 2).num := by
  classical
  set N2 : ℤ := ∑ a ∈ Icc 1 (p - 1), (∏ b ∈ (Icc 1 (p - 1)).erase a, (b : ℤ)) ^ 2 with hN2
  -- `(p - 1)!² ∑ 1/i² = N2` in `ℚ`
  have hQ : (∑ a ∈ Icc 1 (p - 1), (1 : ℚ) / a ^ 2) * (((((p - 1).factorial : ℕ) : ℤ) ^ 2 : ℤ) : ℚ)
      = N2 := by
    rw [hN2, Finset.sum_mul]
    push_cast
    refine Finset.sum_congr rfl fun a ha ↦ ?_
    have ha0 : (a : ℚ) ≠ 0 := by rw [Finset.mem_Icc] at ha; exact_mod_cast (by omega : a ≠ 0)
    have h := Finset.prod_erase_mul (Icc 1 (p - 1)) (fun b : ℕ ↦ (b : ℚ)) ha
    have hfact : ∏ b ∈ Icc 1 (p - 1), (b : ℚ) = (((p - 1).factorial : ℕ) : ℚ) := by
      rw [← Nat.cast_prod, prod_Icc_id]
    rw [← hfact, ← h]
    field_simp
  -- `N2 ≡ (p - 1)!² ∑ (1/i)² ≡ (p - 1)!² ∑ i² ≡ 0 (mod p)`
  have hN2p : (p : ℤ) ∣ N2 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have e : ((N2 : ℤ) : ZMod p) = (((p - 1).factorial : ℕ) : ZMod p) ^ 2 *
        ∑ a ∈ Icc 1 (p - 1), ((a : ZMod p)⁻¹) ^ 2 := by
      rw [hN2, Finset.mul_sum]
      push_cast
      refine Finset.sum_congr rfl fun a ha ↦ ?_
      have h := Finset.prod_erase_mul (Icc 1 (p - 1)) (fun b : ℕ ↦ (b : ZMod p)) ha
      have hfact : ∏ x ∈ Icc 1 (p - 1), (x : ZMod p) = (((p - 1).factorial : ℕ) : ZMod p) := by
        rw [← Nat.cast_prod, prod_Icc_id]
      rw [hfact] at h
      have hu : IsUnit (a : ZMod p) := isUnit_natCast_of_lt hp.out ⟨1, (pow_one p).symm⟩ ha
      rw [← h, ← mul_pow, mul_assoc, ZMod.mul_inv_of_unit _ hu, mul_one]
    rw [e, sum_Icc_eq_sum_zmod p (fun x ↦ (x⁻¹) ^ 2) (by simp),
      Fintype.sum_equiv (Equiv.inv (ZMod p)) (fun x ↦ (x⁻¹) ^ 2) (fun x ↦ x ^ 2) (fun x ↦ rfl),
      FiniteField.sum_pow_lt_card_sub_one (ZMod p) 2 (by rw [ZMod.card]; omega), mul_zero]
  exact dvd_num_of_mul_eq hQ hN2p
    (by simpa using (isCoprime_prime_pow_factorial p hp.out 1).pow_right (n := 2))

end NTKB.HardyWright
