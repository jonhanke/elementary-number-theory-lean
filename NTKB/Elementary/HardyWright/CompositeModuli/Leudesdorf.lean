/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.CompositeModuli.Theorem130
import NTKB.Elementary.HardyWright.Congruences.Wolstenholme
import NTKB.Elementary.HardyWright.Residues.TrigSums

/-!
# Sums of reciprocals of residues (Hardy–Wright, §§ 8.7 and 8.8 (3))

* Theorem 131: if `p` is prime and `2v < p - 3`, the numerator of
  `1 + 1/2^{2v+1} + ⋯ + 1/(p - 1)^{2v+1}` is divisible by `p²`.
* Theorem 128 (Leudesdorf), cases (8.7.1) and (8.7.2): for `S_m = ∑_{t ∈ t(m)} 1/t`, the numerator
  of `S_m` is divisible by `m²` if `(m, 6) = 1`, and by `m²/3` if `m` is odd and `3 ∣ m`.

Both rest on the pairing `t ↔ n - t` used by Hardy and Wright (`f(x) = f(n - x)`): modulo `n²`,
`1/(n - t)^e ≡ -1/t^e - e n/t^{e+1}` for odd `e`, so `2 ∑ 1/t^e ≡ -e n ∑ 1/t^{e+1} (mod n²)`, and
the last sum only matters modulo `n`. (The book argues with power series in § 8.8 and with Bauer's
congruence in § 8.7; the pairing is the same symmetry.)
-/

open Finset

namespace NTKB.HardyWright

variable {n : ℕ}

/-- In `ZMod (n²)`, `n x = 0` as soon as `x ≡ 0 (mod n)`. -/
lemma natCast_mul_eq_zero_of_cast_eq_zero (x : ZMod (n ^ 2))
    (hx : ZMod.castHom (dvd_pow_self n two_ne_zero) (ZMod n) x = 0) : (n : ZMod (n ^ 2)) * x = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have : NeZero (n ^ 2) := ⟨by positivity⟩
  rw [← ZMod.natCast_zmod_val x, map_natCast, ZMod.natCast_eq_zero_iff] at hx
  obtain ⟨k, hk⟩ := hx
  rw [← ZMod.natCast_zmod_val x, hk, Nat.cast_mul, ← mul_assoc, ← Nat.cast_mul, ← sq,
    ZMod.natCast_self, zero_mul]

/-- `(1 + ε)^e = 1 + e ε` when `ε² = 0`. -/
lemma one_add_pow_of_sq_eq_zero {R : Type*} [CommRing R] {ε : R} (hε : ε ^ 2 = 0) (e : ℕ) :
    (1 + ε) ^ e = 1 + e * ε := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination (e : R) * hε

/-- The pairing step: modulo `n²`, `1/(n - t)^e = -1/t^e - e n/t^{e+1}` for odd `e`. -/
lemma inv_sub_pow_eq (u : ZMod (n ^ 2)) (hu : IsUnit u) {e : ℕ} (he : Odd e) :
    ((n : ZMod (n ^ 2)) - u)⁻¹ ^ e = -(u⁻¹ ^ e) - e * n * u⁻¹ ^ (e + 1) := by
  have hn2 : (n : ZMod (n ^ 2)) ^ 2 = 0 := by exact_mod_cast ZMod.natCast_self (n ^ 2)
  have hε2 : ((n : ZMod (n ^ 2)) * u⁻¹) ^ 2 = 0 := by rw [mul_pow, hn2, zero_mul]
  have huu : u * u⁻¹ = 1 := ZMod.mul_inv_of_unit u hu
  -- `(n - u)⁻¹ = -u⁻¹ (1 + n u⁻¹)`
  have hinv : ((n : ZMod (n ^ 2)) - u)⁻¹ = -u⁻¹ * (1 + n * u⁻¹) :=
    ZMod.inv_eq_of_mul_eq_one (n ^ 2) _ _ (by
      linear_combination (1 + (n : ZMod (n ^ 2)) * u⁻¹) * huu - u⁻¹ ^ 2 * hn2)
  rw [hinv, mul_pow, one_add_pow_of_sq_eq_zero hε2, he.neg_pow]
  ring

/-- The residues `0 ≤ t < n` prime to `n > 1` satisfy `1 ≤ t < n`, and `n - t` is again one. -/
lemma mem_filter_coprime {n t : ℕ} (hn : 1 < n) (ht : t ∈ (range n).filter (·.Coprime n)) :
    1 ≤ t ∧ t < n ∧ t.Coprime n ∧ n - t ∈ (range n).filter (·.Coprime n) := by
  simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
  have h1 : 1 ≤ t := by
    refine Nat.one_le_iff_ne_zero.2 ?_
    rintro rfl
    have := ht.2
    rw [Nat.coprime_zero_left] at this
    omega
  exact ⟨h1, ht.1, ht.2, by omega, (Nat.coprime_self_sub_left ht.1.le).2 ht.2⟩

lemma isUnit_cast_sq {n t : ℕ} (ht : t.Coprime n) : IsUnit (t : ZMod (n ^ 2)) :=
  (ZMod.isUnit_iff_coprime _ _).2 (Nat.Coprime.pow_right 2 ht)

/-- `2 ∑_{t ∈ t(n)} 1/t^e ≡ -e n ∑_{t ∈ t(n)} 1/t^{e+1} (mod n²)` for odd `e`. -/
theorem two_mul_sum_inv_pow (hn : 1 < n) {e : ℕ} (he : Odd e) :
    2 * ∑ t ∈ (range n).filter (·.Coprime n), (t : ZMod (n ^ 2))⁻¹ ^ e =
      -(e * n) * ∑ t ∈ (range n).filter (·.Coprime n), (t : ZMod (n ^ 2))⁻¹ ^ (e + 1) := by
  classical
  set T := (range n).filter (·.Coprime n)
  have hre : ∑ t ∈ T, (t : ZMod (n ^ 2))⁻¹ ^ e =
      ∑ t ∈ T, (((n - t : ℕ) : ZMod (n ^ 2)))⁻¹ ^ e := by
    refine Finset.sum_nbij' (fun t ↦ n - t) (fun t ↦ n - t) ?_ ?_ ?_ ?_ ?_
    · intro t ht; exact (mem_filter_coprime hn ht).2.2.2
    · intro t ht; exact (mem_filter_coprime hn ht).2.2.2
    · intro t ht; have := mem_filter_coprime hn ht; omega
    · intro t ht; have := mem_filter_coprime hn ht; omega
    · intro t ht
      have := mem_filter_coprime hn ht
      rw [Nat.sub_sub_self this.2.1.le]
  have hpair : ∀ t ∈ T, (((n - t : ℕ) : ZMod (n ^ 2)))⁻¹ ^ e =
      -((t : ZMod (n ^ 2))⁻¹ ^ e) - e * n * (t : ZMod (n ^ 2))⁻¹ ^ (e + 1) := by
    intro t ht
    have := mem_filter_coprime hn ht
    rw [Nat.cast_sub this.2.1.le]
    exact inv_sub_pow_eq _ (isUnit_cast_sq this.2.2.1) he
  rw [two_mul]
  nth_rewrite 2 [hre]
  rw [Finset.sum_congr rfl hpair, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
  ring

/-- The image in `ZMod n` of the inverse of a unit of `ZMod n²`. -/
lemma castHom_inv_of_coprime {n t : ℕ} (ht : t.Coprime n) :
    ZMod.castHom (dvd_pow_self n two_ne_zero) (ZMod n) ((t : ZMod (n ^ 2))⁻¹) = (t : ZMod n)⁻¹ := by
  set φ := ZMod.castHom (dvd_pow_self n two_ne_zero) (ZMod n)
  have h1 : φ ((t : ZMod (n ^ 2))⁻¹) * (t : ZMod n) = 1 := by
    rw [← map_natCast φ, ← map_mul, mul_comm, ZMod.mul_inv_of_unit _ (isUnit_cast_sq ht), map_one]
  have hu : IsUnit (t : ZMod n) := (ZMod.isUnit_iff_coprime _ _).2 ht
  calc φ ((t : ZMod (n ^ 2))⁻¹) = φ ((t : ZMod (n ^ 2))⁻¹) * ((t : ZMod n) * (t : ZMod n)⁻¹) := by
        rw [ZMod.mul_inv_of_unit _ hu, mul_one]
    _ = (t : ZMod n)⁻¹ := by rw [← mul_assoc, h1, one_mul]

/-- The numbers `0 ≤ t < p` prime to the prime `p` are `1, …, p - 1`. -/
lemma filter_coprime_range_prime {p : ℕ} (hp : p.Prime) :
    (range p).filter (·.Coprime p) = Icc 1 (p - 1) := by
  ext t
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  have := hp.two_le
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨Nat.one_le_iff_ne_zero.2 (by rintro rfl; exact h2 (dvd_zero p)), by omega⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, fun h ↦ absurd (Nat.le_of_dvd (by omega) h) (by omega)⟩

/-- **Theorem 131** [hardywright2008]: if `p` is prime and `2v < p - 3`, the numerator of
`S_{2v+1} = 1 + 1/2^{2v+1} + ⋯ + 1/(p - 1)^{2v+1}` is divisible by `p²`. -/
@[kb "hardywright2008" "Thm 131, p. 134"]
theorem prime_sq_dvd_num_sum_inv_pow (p : ℕ) [hp : Fact p.Prime] {v : ℕ} (hv : 2 * v < p - 3) :
    (p : ℤ) ^ 2 ∣ (∑ k ∈ Icc 1 (p - 1), (1 : ℚ) / k ^ (2 * v + 1)).num := by
  classical
  have hp5 : 5 ≤ p := by
    have : p ≠ 4 := by rintro rfl; exact absurd hp.out (by decide)
    omega
  set e := 2 * v + 1 with he
  have heo : Odd e := ⟨v, rfl⟩
  have hT := filter_coprime_range_prime hp.out
  -- `∑ 1/k^e ≡ 0 (mod p²)` with associates
  have hS : ∑ k ∈ Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ e = 0 := by
    have h2 := two_mul_sum_inv_pow (n := p) (by omega) heo
    rw [hT] at h2
    -- the sum of `1/k^{e+1}` vanishes modulo `p`
    have hY : (p : ZMod (p ^ 2)) * ∑ k ∈ Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ (e + 1) = 0 := by
      apply natCast_mul_eq_zero_of_cast_eq_zero
      rw [map_sum]
      have : ∀ k ∈ Icc 1 (p - 1), ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)
          (((k : ZMod (p ^ 2))⁻¹) ^ (e + 1)) = ((k : ZMod p)⁻¹) ^ (e + 1) := by
        intro k hk
        rw [map_pow, castHom_inv_of_coprime]
        rw [← hT] at hk
        exact (Finset.mem_filter.1 hk).2
      rw [Finset.sum_congr rfl this, sum_Icc_eq_sum_zmod p (fun x ↦ (x⁻¹) ^ (e + 1))
        (by simp [he]),
        Fintype.sum_equiv (Equiv.inv (ZMod p)) (fun x ↦ (x⁻¹) ^ (e + 1)) (fun x ↦ x ^ (e + 1))
          (fun x ↦ rfl),
        FiniteField.sum_pow_lt_card_sub_one (ZMod p) (e + 1) (by rw [ZMod.card]; omega)]
    have h2u : IsUnit (2 : ZMod (p ^ 2)) := by
      have : ((2 : ℕ) : ZMod (p ^ 2)) = 2 := by norm_num
      rw [← this]
      exact isUnit_cast_sq ((Nat.coprime_primes Nat.prime_two hp.out).2 (by omega))
    have : 2 * ∑ k ∈ Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ e = 0 := by
      rw [h2, neg_mul, mul_assoc, hY, mul_zero, neg_zero]
    exact h2u.mul_right_eq_zero.1 this
  -- numerator: `(p - 1)!^e ∑ 1/k^e` is an integer `≡ 0 (mod p²)`
  set N : ℤ := ∑ k ∈ Icc 1 (p - 1), (∏ j ∈ (Icc 1 (p - 1)).erase k, (j : ℤ)) ^ e with hN
  have hQ : (∑ k ∈ Icc 1 (p - 1), (1 : ℚ) / k ^ e) *
      (((((p - 1).factorial : ℕ) : ℤ) ^ e : ℤ) : ℚ) = N := by
    rw [hN, Finset.sum_mul]
    push_cast
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hk0 : (k : ℚ) ≠ 0 := by rw [Finset.mem_Icc] at hk; exact_mod_cast (by omega : k ≠ 0)
    have h := Finset.prod_erase_mul (Icc 1 (p - 1)) (fun b : ℕ ↦ (b : ℚ)) hk
    have hfact : ∏ b ∈ Icc 1 (p - 1), (b : ℚ) = (((p - 1).factorial : ℕ) : ℚ) := by
      rw [← Nat.cast_prod, prod_Icc_id]
    rw [← hfact, ← h, mul_pow]
    field_simp
  have hNp : (p : ℤ) ^ 2 ∣ N := by
    have : ((p ^ 2 : ℕ) : ℤ) ∣ N := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      have e1 : ((N : ℤ) : ZMod (p ^ 2)) = (((p - 1).factorial : ℕ) : ZMod (p ^ 2)) ^ e *
          ∑ k ∈ Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ e := by
        rw [hN, Finset.mul_sum]
        push_cast
        refine Finset.sum_congr rfl fun k hk ↦ ?_
        have h := Finset.prod_erase_mul (Icc 1 (p - 1)) (fun b : ℕ ↦ (b : ZMod (p ^ 2))) hk
        have hfact : ∏ x ∈ Icc 1 (p - 1), (x : ZMod (p ^ 2)) =
            (((p - 1).factorial : ℕ) : ZMod (p ^ 2)) := by
          rw [← Nat.cast_prod, prod_Icc_id]
        rw [hfact] at h
        have hu : IsUnit (k : ZMod (p ^ 2)) := by
          rw [← hT] at hk; exact isUnit_cast_sq (Finset.mem_filter.1 hk).2
        rw [← h, ← mul_pow, mul_assoc, ZMod.mul_inv_of_unit _ hu, mul_one]
      rw [e1, hS, mul_zero]
    exact_mod_cast this
  exact dvd_num_of_mul_eq hQ hNp
    ((isCoprime_prime_pow_factorial p hp.out 2).pow_right (n := e))

/-! ### Theorem 128 (Leudesdorf), the cases `2 ∤ m` -/

/-- For odd `m`, `3 ∑_{u ∈ (ZMod m)ˣ} u² = 0`: multiplying by the unit `2` permutes the units. -/
lemma three_mul_sum_units_sq {m : ℕ} [NeZero m] (hm : Odd m) :
    3 * ∑ u : (ZMod m)ˣ, ((u : ZMod m)) ^ 2 = 0 := by
  have h2 : IsUnit (2 : ZMod m) := by
    have : ((2 : ℕ) : ZMod m) = 2 := by norm_num
    rw [← this, ZMod.isUnit_iff_coprime]
    exact Nat.coprime_two_left.2 hm
  have hsum : ∑ u : (ZMod m)ˣ, ((((h2.unit * u : (ZMod m)ˣ)) : ZMod m)) ^ 2 =
      ∑ u : (ZMod m)ˣ, ((u : ZMod m)) ^ 2 :=
    Fintype.sum_equiv (Equiv.mulLeft h2.unit) _ _ (fun u ↦ rfl)
  simp only [Units.val_mul, IsUnit.unit_spec, mul_pow] at hsum
  rw [← Finset.mul_sum] at hsum
  linear_combination hsum

/-- `∑_{t ∈ t(m)} 1/t² ≡ ∑ u² (mod m)`, and hence `3 ∑_{t ∈ t(m)} 1/t² ≡ 0 (mod m)` for odd `m`. -/
lemma three_mul_sum_inv_sq_eq_zero {m : ℕ} (hm1 : 1 < m) (hm : Odd m) :
    3 * ∑ t ∈ (range m).filter (·.Coprime m), ((t : ZMod m)⁻¹) ^ 2 = 0 := by
  have : NeZero m := ⟨by omega⟩
  have h := (isReducedResidueSystem_filter m).sum_eq (fun x : ZMod m ↦ (x⁻¹) ^ 2)
  simp only [Int.cast_natCast] at h
  rw [← Finset.sum_coe_sort, h]
  have : ∑ u : (ZMod m)ˣ, (((u : ZMod m))⁻¹) ^ 2 = ∑ u : (ZMod m)ˣ, ((u : ZMod m)) ^ 2 :=
    Fintype.sum_equiv (Equiv.inv (ZMod m)ˣ) _ _ (fun u ↦ by simp [Units.val_inv_eq_inv_val])
  rw [this, three_mul_sum_units_sq hm]

/-- For odd `m > 1`, `3 ∑_{t ∈ t(m)} 1/t ≡ 0 (mod m²)` (associates modulo `m²`). -/
lemma three_mul_sum_inv_eq_zero {m : ℕ} (hm1 : 1 < m) (hm : Odd m) :
    3 * ∑ t ∈ (range m).filter (·.Coprime m), (t : ZMod (m ^ 2))⁻¹ = 0 := by
  set T := (range m).filter (·.Coprime m)
  have h2 := two_mul_sum_inv_pow (n := m) hm1 odd_one
  simp only [pow_one, Nat.cast_one, one_mul, zero_add] at h2
  -- `m ⋅ 3 ∑ 1/t² ≡ 0 (mod m²)`
  have hY : (m : ZMod (m ^ 2)) * (3 * ∑ t ∈ T, ((t : ZMod (m ^ 2))⁻¹) ^ 2) = 0 := by
    apply natCast_mul_eq_zero_of_cast_eq_zero
    rw [map_mul, map_ofNat, map_sum]
    have : ∀ t ∈ T, ZMod.castHom (dvd_pow_self m two_ne_zero) (ZMod m)
        (((t : ZMod (m ^ 2))⁻¹) ^ 2) = ((t : ZMod m)⁻¹) ^ 2 := by
      intro t ht
      rw [map_pow, castHom_inv_of_coprime (Finset.mem_filter.1 ht).2]
    rw [Finset.sum_congr rfl this]
    exact three_mul_sum_inv_sq_eq_zero hm1 hm
  have h2u : IsUnit (2 : ZMod (m ^ 2)) := by
    have : ((2 : ℕ) : ZMod (m ^ 2)) = 2 := by norm_num
    rw [← this]
    exact isUnit_cast_sq (Nat.coprime_two_left.2 hm)
  have : 2 * (3 * ∑ t ∈ T, (t : ZMod (m ^ 2))⁻¹) = 0 := by
    rw [mul_left_comm, h2]
    linear_combination -hY
  exact h2u.mul_right_eq_zero.1 this

/-- Clearing denominators: `(∏_{t ∈ t(m)} t) ∑ 1/t = ∑_t ∏_{t' ≠ t} t'`, and modulo `m²` this is
`(∏ t) ∑ 1/t` with associates. -/
lemma sum_inv_coprime_num {m : ℕ} (hm1 : 1 < m) :
    (∑ t ∈ (range m).filter (·.Coprime m), (1 : ℚ) / t) *
        (((∏ t ∈ (range m).filter (·.Coprime m), t : ℕ) : ℤ) : ℚ) =
      ((∑ t ∈ (range m).filter (·.Coprime m),
        ∏ t' ∈ ((range m).filter (·.Coprime m)).erase t, t' : ℕ) : ℤ) ∧
    ((∑ t ∈ (range m).filter (·.Coprime m),
        ∏ t' ∈ ((range m).filter (·.Coprime m)).erase t, t' : ℕ) : ZMod (m ^ 2)) =
      ((∏ t ∈ (range m).filter (·.Coprime m), t : ℕ) : ZMod (m ^ 2)) *
        ∑ t ∈ (range m).filter (·.Coprime m), (t : ZMod (m ^ 2))⁻¹ := by
  classical
  set T := (range m).filter (·.Coprime m)
  constructor
  · rw [Finset.sum_mul]
    push_cast
    refine Finset.sum_congr rfl fun t ht ↦ ?_
    have ht0 : (t : ℚ) ≠ 0 := by
      have := (mem_filter_coprime hm1 ht).1; positivity
    rw [← Finset.prod_erase_mul T (fun b : ℕ ↦ (b : ℚ)) ht]
    field_simp
  · rw [Finset.mul_sum, Nat.cast_sum]
    refine Finset.sum_congr rfl fun t ht ↦ ?_
    rw [Nat.cast_prod, Nat.cast_prod,
      ← Finset.prod_erase_mul T (fun b : ℕ ↦ (b : ZMod (m ^ 2))) ht, mul_assoc,
      ZMod.mul_inv_of_unit _ (isUnit_cast_sq (mem_filter_coprime hm1 ht).2.2.1), mul_one]

lemma isCoprime_sq_prod_coprime {m : ℕ} (k : ℕ) (hk : k ∣ m ^ 2) :
    IsCoprime (k : ℤ) ((∏ t ∈ (range m).filter (·.Coprime m), t : ℕ) : ℤ) := by
  rw [Nat.isCoprime_iff_coprime]
  refine Nat.Coprime.coprime_dvd_left hk (Nat.Coprime.pow_left 2 ?_)
  refine Nat.Coprime.prod_right fun t ht ↦ ?_
  exact Nat.coprime_comm.1 (Finset.mem_filter.1 ht).2

/-- **Theorem 128** [hardywright2008] (Leudesdorf), (8.7.1): if `2 ∤ m` and `3 ∤ m`, then the
numerator of `S_m = ∑_{t ∈ t(m)} 1/t` is divisible by `m²`. -/
@[kb "hardywright2008" "Thm 128, p. 130"]
theorem sq_dvd_num_sum_inv_coprime (m : ℕ) (h2 : ¬2 ∣ m) (h3 : ¬3 ∣ m) :
    (m : ℤ) ^ 2 ∣ (∑ t ∈ (range m).filter (·.Coprime m), (1 : ℚ) / t).num := by
  rcases Nat.lt_or_ge m 2 with hm | hm1
  · interval_cases m
    · exact absurd (dvd_zero 2) h2
    · simp
  have hodd : Odd m := Nat.odd_iff.2 (by omega)
  obtain ⟨hQ, hZ⟩ := sum_inv_coprime_num hm1
  refine dvd_num_of_mul_eq hQ ?_ (by exact_mod_cast isCoprime_sq_prod_coprime (m ^ 2) dvd_rfl)
  have h3u : IsUnit (3 : ZMod (m ^ 2)) := by
    have : ((3 : ℕ) : ZMod (m ^ 2)) = 3 := by norm_num
    rw [← this]
    exact isUnit_cast_sq ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3)
  have hS := h3u.mul_right_eq_zero.1 (three_mul_sum_inv_eq_zero hm1 hodd)
  rw [hS, mul_zero, ZMod.natCast_eq_zero_iff] at hZ
  exact_mod_cast Int.natCast_dvd_natCast.2 hZ

/-- **Theorem 128** [hardywright2008] (Leudesdorf), (8.7.2): if `2 ∤ m` and `3 ∣ m`, then the
numerator of `S_m = ∑_{t ∈ t(m)} 1/t` is divisible by `m²/3`. -/
@[kb "hardywright2008" "Thm 128, p. 130"]
theorem sq_div_three_dvd_num_sum_inv (m : ℕ) (h2 : ¬2 ∣ m) (h3 : 3 ∣ m) :
    ((m ^ 2 / 3 : ℕ) : ℤ) ∣ (∑ t ∈ (range m).filter (·.Coprime m), (1 : ℚ) / t).num := by
  have hm1 : 1 < m := by
    rcases h3 with ⟨c, rfl⟩
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · exact absurd (dvd_zero 2) h2
    · omega
  have hodd : Odd m := Nat.odd_iff.2 (by omega)
  obtain ⟨hQ, hZ⟩ := sum_inv_coprime_num hm1
  have hk : m ^ 2 / 3 ∣ m ^ 2 := Nat.div_dvd_of_dvd (dvd_pow h3 two_ne_zero)
  refine dvd_num_of_mul_eq hQ ?_ (by exact_mod_cast isCoprime_sq_prod_coprime _ hk)
  set N := ∑ t ∈ (range m).filter (·.Coprime m),
    ∏ t' ∈ ((range m).filter (·.Coprime m)).erase t, t'
  -- `m² ∣ 3 N`
  have h3N : m ^ 2 ∣ 3 * N := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, hZ, Nat.cast_ofNat, mul_left_comm,
      three_mul_sum_inv_eq_zero hm1 hodd, mul_zero]
  have hm3 : m ^ 2 = 3 * (m ^ 2 / 3) := (Nat.mul_div_cancel' (dvd_pow h3 two_ne_zero)).symm
  rw [hm3] at h3N
  exact_mod_cast Int.natCast_dvd_natCast.2 (Nat.dvd_of_mul_dvd_mul_left (by norm_num) h3N)

end NTKB.HardyWright
