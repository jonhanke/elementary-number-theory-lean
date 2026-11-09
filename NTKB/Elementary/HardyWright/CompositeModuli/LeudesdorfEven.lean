/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.CompositeModuli.Leudesdorf

/-!
# Leudesdorf's theorem for even `m` (Hardy–Wright, § 8.7, cases (8.7.3)–(8.7.5))

With `S_m = ∑_{t ∈ t(m)} 1/t`, `2 S_m ≡ -m ∑_{t ∈ t(m)} 1/t² (mod m²)` (`two_mul_sum_inv_pow`), and
`∑ 1/t² ≡ ∑ t² (mod m)`. For `m = 2^a M` (`M` odd), `∑_{t ∈ t(m)} t² ≡ φ(M) ∑_{u ∈ t(2^a)} u² (mod 2^a)`
with `2 ∑_{u ∈ t(2^a)} u² ≡ 0 (mod 2^a)`, and `3 ∑_{t ∈ t(m)} t² ≡ 0 (mod M)`.
-/

open Finset

namespace NTKB.HardyWright

/-- `3 ∑_{i < N} (2i + 1)² = N (4N² - 1)`. -/
lemma three_mul_sum_odd_sq (N : ℕ) : 3 * ∑ i ∈ range N, (2 * i + 1) ^ 2 + N = 4 * N ^ 3 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add]
    nlinarith [ih]

/-- The numbers `0 ≤ t < 2^a` prime to `2^a` (`a ≥ 1`) are the odd numbers `2i + 1`, `i < 2^{a-1}`. -/
lemma filter_coprime_two_pow {a : ℕ} (ha : 1 ≤ a) :
    (range (2 ^ a)).filter (·.Coprime (2 ^ a)) = (range (2 ^ (a - 1))).image (fun i ↦ 2 * i + 1) := by
  have h2a : 2 ^ a = 2 * 2 ^ (a - 1) := by rw [← pow_succ', Nat.sub_add_cancel ha]
  ext t
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image,
    coprime_prime_pow_iff Nat.prime_two (by omega : 0 < a)]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨t / 2, by omega, by omega⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨by omega, by omega⟩

/-- `2 ∑_{u ∈ t(2^a)} u² ≡ 0 (mod 2^a)`. -/
lemma two_pow_dvd_two_mul_sum_sq {a : ℕ} (ha : 1 ≤ a) :
    2 ^ a ∣ 2 * ∑ t ∈ (range (2 ^ a)).filter (·.Coprime (2 ^ a)), t ^ 2 := by
  rw [filter_coprime_two_pow ha, Finset.sum_image (fun x _ y _ h ↦ by simpa using h)]
  have h := three_mul_sum_odd_sq (2 ^ (a - 1))
  have h2a : 2 ^ a = 2 * 2 ^ (a - 1) := by rw [← pow_succ', Nat.sub_add_cancel ha]
  -- `2^a ∣ 6 ∑ = 2N (4N² - 1)`, and `(2^a, 3) = 1`
  have h6 : 2 ^ a ∣ 3 * (2 * ∑ i ∈ range (2 ^ (a - 1)), (2 * i + 1) ^ 2) := by
    refine ⟨4 * (2 ^ (a - 1)) ^ 2 - 1, ?_⟩
    have : 3 * (2 * ∑ i ∈ range (2 ^ (a - 1)), (2 * i + 1) ^ 2) =
        2 * (4 * (2 ^ (a - 1)) ^ 3) - 2 * 2 ^ (a - 1) := by omega
    rw [this, h2a, Nat.mul_sub, pow_succ]
    ring_nf
  exact (Nat.Coprime.dvd_of_dvd_mul_left
    (Nat.Coprime.pow_left a ((Nat.coprime_primes Nat.prime_two Nat.prime_three).2 (by norm_num)))
    h6)

/-- If `(n, M) = 1`: `∑_{t ∈ t(nM)} t² ≡ φ(M) ∑_{t ∈ t(n)} t² (mod n)` (the numbers `T n + t M`
form `t(nM)` by Theorem 61, and `t M` runs through `t(n)` by Theorem 58). -/
lemma sum_sq_mul_coprime {n M : ℕ} [NeZero n] [NeZero M] (hcop : n.Coprime M) :
    ∑ t ∈ (range (n * M)).filter (·.Coprime (n * M)), ((t : ZMod n)) ^ 2 =
      M.totient * ∑ t ∈ (range n).filter (·.Coprime n), ((t : ZMod n)) ^ 2 := by
  classical
  have : NeZero (n * M) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne M)⟩
  set π : ZMod (n * M) →+* ZMod n := ZMod.castHom (dvd_mul_right _ _) (ZMod n)
  set G : ZMod (n * M) → ZMod n := fun x ↦ (π x) ^ 2
  set ι := {t // t ∈ (range n).filter (·.Coprime n)}
  set κ := {T // T ∈ (range M).filter (·.Coprime M)}
  have hι := isReducedResidueSystem_filter n
  have hκ := isReducedResidueSystem_filter M
  have hm := isReducedResidueSystem_filter (n * M)
  have hcrt := hι.crt hcop hκ
  have h1 : ∑ t ∈ (range (n * M)).filter (·.Coprime (n * M)), ((t : ZMod n)) ^ 2 =
      ∑ t : {t // t ∈ (range (n * M)).filter (·.Coprime (n * M))}, G ((t : ℕ) : ℤ) := by
    rw [← Finset.sum_coe_sort]
    simp [G, π]
  rw [h1, hm.sum_eq G, ← hcrt.sum_eq G, Fintype.sum_prod_type]
  have h0 : ((n : ℕ) : ZMod n) = 0 := ZMod.natCast_self _
  have h2 : ∀ (t : ι) (T : κ), G ((((T : ℕ) : ℤ) * ((n : ℕ) : ℤ) + ((t : ℕ) : ℤ) * (M : ℤ) : ℤ)) =
      (((t : ℕ) : ZMod n) * (M : ZMod n)) ^ 2 := by
    intro t T
    simp only [G]
    rw [map_intCast]
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
    rw [h0, mul_zero, zero_add]
  simp only [h2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  congr 1
  · rw [Fintype.card_coe, Nat.totient_eq_card_coprime]
    congr 2
    ext x; simp [Nat.coprime_comm]
  · have hι' := hι.mul (k := (M : ℤ)) (Nat.isCoprime_iff_coprime.2 hcop.symm)
    have e1 := hι'.sum_eq (fun x : ZMod n ↦ x ^ 2)
    have e2 := hι.sum_eq (fun x : ZMod n ↦ x ^ 2)
    have := e1.trans e2.symm
    simp only [Int.cast_mul, Int.cast_natCast] at this
    rw [← Finset.sum_coe_sort ((range n).filter (·.Coprime n))]
    simpa only [mul_comm ((M : ℕ) : ZMod n)] using this

/-- For `m > 1`: `∑_{t ∈ t(m)} 1/t² ≡ ∑_{t ∈ t(m)} t² (mod m)`. -/
lemma sum_inv_sq_eq_sum_sq {m : ℕ} (hm1 : 1 < m) :
    ∑ t ∈ (range m).filter (·.Coprime m), ((t : ZMod m)⁻¹) ^ 2 =
      ∑ t ∈ (range m).filter (·.Coprime m), ((t : ZMod m)) ^ 2 := by
  have : NeZero m := ⟨by omega⟩
  have h1 := (isReducedResidueSystem_filter m).sum_eq (fun x : ZMod m ↦ (x⁻¹) ^ 2)
  have h2 := (isReducedResidueSystem_filter m).sum_eq (fun x : ZMod m ↦ x ^ 2)
  simp only [Int.cast_natCast] at h1 h2
  rw [← Finset.sum_coe_sort ((range m).filter (·.Coprime m)) (fun t ↦ ((t : ZMod m)⁻¹) ^ 2), h1,
    ← Finset.sum_coe_sort ((range m).filter (·.Coprime m)) (fun t ↦ ((t : ZMod m)) ^ 2), h2]
  exact Fintype.sum_equiv (Equiv.inv (ZMod m)ˣ) _ _ (fun u ↦ by simp [Units.val_inv_eq_inv_val])

/-- If `m ∣ c ∑_{t ∈ t(m)} t²` then `m² ∣ 2c N`, `N = ∑_t ∏_{t' ≠ t} t'` the numerator of `S_m`. -/
lemma sq_dvd_two_mul_num_of_dvd {m c : ℕ} (hm1 : 1 < m)
    (hc : m ∣ c * ∑ t ∈ (range m).filter (·.Coprime m), t ^ 2) :
    m ^ 2 ∣ 2 * c * ∑ t ∈ (range m).filter (·.Coprime m),
      ∏ t' ∈ ((range m).filter (·.Coprime m)).erase t, t' := by
  set T := (range m).filter (·.Coprime m)
  obtain ⟨-, hZ⟩ := sum_inv_coprime_num hm1
  have h2 := two_mul_sum_inv_pow (n := m) hm1 odd_one
  simp only [pow_one, Nat.cast_one, one_mul, zero_add] at h2
  have hY : (m : ZMod (m ^ 2)) * ((c : ZMod (m ^ 2)) * ∑ t ∈ T, ((t : ZMod (m ^ 2))⁻¹) ^ 2) = 0 := by
    apply natCast_mul_eq_zero_of_cast_eq_zero
    rw [map_mul, map_natCast, map_sum]
    have : ∀ t ∈ T, ZMod.castHom (dvd_pow_self m two_ne_zero) (ZMod m)
        (((t : ZMod (m ^ 2))⁻¹) ^ 2) = ((t : ZMod m)⁻¹) ^ 2 := by
      intro t ht
      rw [map_pow, castHom_inv_of_coprime (Finset.mem_filter.1 ht).2]
    rw [Finset.sum_congr rfl this, sum_inv_sq_eq_sum_sq hm1]
    have := (ZMod.natCast_eq_zero_iff (c * ∑ t ∈ T, t ^ 2) m).2 hc
    push_cast at this
    exact this
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, Nat.cast_mul, hZ]
  have : (2 : ZMod (m ^ 2)) * ∑ t ∈ T, (t : ZMod (m ^ 2))⁻¹ =
      -(m : ZMod (m ^ 2)) * ∑ t ∈ T, ((t : ZMod (m ^ 2))⁻¹) ^ 2 := h2
  push_cast
  linear_combination ((c : ZMod (m ^ 2)) * ∏ t ∈ T, (t : ZMod (m ^ 2))) * this -
    (∏ t ∈ T, (t : ZMod (m ^ 2))) * hY

/-- `∑_{t ∈ t(n)} t² ≡ ∑_{u ∈ (ZMod n)ˣ} u²`, so `3 ∑_{t ∈ t(n)} t² ≡ 0 (mod n)` for odd `n`. -/
lemma three_mul_sum_sq_filter {n : ℕ} [NeZero n] (hn : Odd n) :
    3 * ∑ t ∈ (range n).filter (·.Coprime n), ((t : ZMod n)) ^ 2 = 0 := by
  have h := (isReducedResidueSystem_filter n).sum_eq (fun x : ZMod n ↦ x ^ 2)
  simp only [Int.cast_natCast] at h
  rw [← Finset.sum_coe_sort ((range n).filter (·.Coprime n)) (fun t ↦ ((t : ZMod n)) ^ 2), h]
  exact three_mul_sum_units_sq hn

/-- For `m = 2^a M` with `M` odd and `a ≥ 1`: `2^a ∣ 2 ∑_{t ∈ t(m)} t²`, `2^a ∣ ∑ t²` if `M > 1`,
and `M ∣ 3 ∑ t²`. -/
lemma sum_sq_filter_dvd {a M : ℕ} (ha : 1 ≤ a) (hM : Odd M) :
    (2 ^ a ∣ 2 * ∑ t ∈ (range (2 ^ a * M)).filter (·.Coprime (2 ^ a * M)), t ^ 2) ∧
    (1 < M → 2 ^ a ∣ ∑ t ∈ (range (2 ^ a * M)).filter (·.Coprime (2 ^ a * M)), t ^ 2) ∧
    (M ∣ 3 * ∑ t ∈ (range (2 ^ a * M)).filter (·.Coprime (2 ^ a * M)), t ^ 2) := by
  have hM0 : M ≠ 0 := by rintro rfl; simp at hM
  have : NeZero M := ⟨hM0⟩
  have : NeZero (2 ^ a) := ⟨by positivity⟩
  have hcop : (2 ^ a).Coprime M := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hM)
  set Z := ∑ t ∈ (range (2 ^ a * M)).filter (·.Coprime (2 ^ a * M)), t ^ 2
  -- modulo `2^a`
  have hA : (Z : ZMod (2 ^ a)) = M.totient *
      ∑ t ∈ (range (2 ^ a)).filter (·.Coprime (2 ^ a)), ((t : ZMod (2 ^ a))) ^ 2 := by
    rw [← sum_sq_mul_coprime hcop]; simp only [Z, Nat.cast_sum, Nat.cast_pow]
  have h2 : (2 : ZMod (2 ^ a)) *
      ∑ t ∈ (range (2 ^ a)).filter (·.Coprime (2 ^ a)), ((t : ZMod (2 ^ a))) ^ 2 = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ (2 ^ a)).2 (two_pow_dvd_two_mul_sum_sq ha)
    push_cast at this; exact this
  refine ⟨?_, fun hM1 ↦ ?_, ?_⟩
  · rw [← ZMod.natCast_eq_zero_iff]; push_cast
    rw [hA, mul_left_comm, h2, mul_zero]
  · obtain ⟨k, hk⟩ := Nat.totient_even (show 2 < M by obtain ⟨j, rfl⟩ := hM; omega)
    rw [← ZMod.natCast_eq_zero_iff, hA, hk, show k + k = k * 2 by ring, Nat.cast_mul, mul_assoc,
      Nat.cast_ofNat, h2, mul_zero]
  · -- modulo `M`
    have hB : (Z : ZMod M) = ((2 ^ a).totient : ZMod M) *
        ∑ t ∈ (range M).filter (·.Coprime M), ((t : ZMod M)) ^ 2 := by
      rw [← sum_sq_mul_coprime hcop.symm, mul_comm M]; simp only [Z, Nat.cast_sum, Nat.cast_pow]
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, hB, Nat.cast_ofNat, mul_left_comm,
      three_mul_sum_sq_filter hM, mul_zero]

/-- From `m² ∣ 2cN` and `2c ∣ m²` to the numerator of `S_m`. -/
lemma dvd_num_sum_inv_of {m c : ℕ} (hm1 : 1 < m) (hc : 2 * c ∣ m ^ 2)
    (h : m ∣ c * ∑ t ∈ (range m).filter (·.Coprime m), t ^ 2) :
    ((m ^ 2 / (2 * c) : ℕ) : ℤ) ∣ (∑ t ∈ (range m).filter (·.Coprime m), (1 : ℚ) / t).num := by
  obtain ⟨hQ, -⟩ := sum_inv_coprime_num hm1
  have hk : m ^ 2 / (2 * c) ∣ m ^ 2 := Nat.div_dvd_of_dvd hc
  refine dvd_num_of_mul_eq hQ ?_ (by exact_mod_cast isCoprime_sq_prod_coprime _ hk)
  have h2 := sq_dvd_two_mul_num_of_dvd hm1 h
  rw [← Nat.mul_div_cancel' hc, mul_comm] at h2
  have hc0 : 0 < 2 * c := Nat.pos_of_ne_zero (by rintro h0; rw [h0] at hc; simp at hc; omega)
  exact_mod_cast Int.natCast_dvd_natCast.2
    (Nat.dvd_of_mul_dvd_mul_right hc0 (by simpa [mul_comm] using h2))

/-- Splitting `m = 2^a M` with `M` odd. -/
lemma exists_two_pow_mul_odd {m : ℕ} (hm : m ≠ 0) (h2 : 2 ∣ m) :
    ∃ a M, 1 ≤ a ∧ Odd M ∧ m = 2 ^ a * M := by
  obtain ⟨M, hmM, hM0, hcop⟩ := exists_eq_prime_pow_mul Nat.prime_two hm (Nat.ordProj_dvd m 2)
    (Nat.pow_succ_factorization_not_dvd hm Nat.prime_two)
  refine ⟨m.factorization 2, M, Nat.Prime.factorization_pos_of_dvd Nat.prime_two hm h2, ?_, hmM⟩
  have : ¬2 ∣ M := fun h ↦ by
    have := Nat.Coprime.coprime_dvd_left (dvd_pow_self 2
      (Nat.Prime.factorization_pos_of_dvd Nat.prime_two hm h2).ne') hcop
    exact absurd (Nat.dvd_gcd dvd_rfl h) (by rw [this]; norm_num)
  exact Nat.odd_iff.2 (by omega)

/-- **Theorem 128** [hardywright2008] (Leudesdorf), (8.7.3): if `2 ∣ m`, `3 ∤ m` and `m` is not a
power of `2`, the numerator of `S_m = ∑_{t ∈ t(m)} 1/t` is divisible by `m²/2`. -/
@[kb "hardywright2008" "Thm 128, p. 130"]
theorem sq_div_two_dvd_num_sum_inv (m : ℕ) (h2 : 2 ∣ m) (h3 : ¬3 ∣ m)
    (hpow : ∀ a, m ≠ 2 ^ a) :
    ((m ^ 2 / 2 : ℕ) : ℤ) ∣ (∑ t ∈ (range m).filter (·.Coprime m), (1 : ℚ) / t).num := by
  have hm0 : m ≠ 0 := fun h ↦ h3 (h ▸ dvd_zero 3)
  obtain ⟨a, M, ha, hM, rfl⟩ := exists_two_pow_mul_odd hm0 h2
  have hM1 : 1 < M := by
    rcases Nat.lt_or_ge M 2 with h | h
    · have : M = 1 := by obtain ⟨j, rfl⟩ := hM; omega
      exact absurd (by rw [this, mul_one]) (hpow a)
    · exact h
  obtain ⟨-, hA, hB⟩ := sum_sq_filter_dvd ha hM
  have hM3 : ¬3 ∣ M := fun h ↦ h3 (dvd_mul_of_dvd_right h _)
  have hBM : M ∣ ∑ t ∈ (range (2 ^ a * M)).filter (·.Coprime (2 ^ a * M)), t ^ 2 :=
    (Nat.Coprime.dvd_of_dvd_mul_left ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hM3 |>
      Nat.Coprime.symm) hB)
  have hm1 : 1 < 2 ^ a * M := by
    have : 1 ≤ 2 ^ a := Nat.one_le_two_pow; nlinarith
  have := dvd_num_sum_inv_of (c := 1) hm1 ?_ ?_
  · simpa using this
  · exact dvd_pow (dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) _) two_ne_zero
  · rw [one_mul]
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
      (Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hM)) (hA hM1) hBM

/-- **Theorem 128** [hardywright2008] (Leudesdorf), (8.7.4): if `2 ∣ m` and `3 ∣ m`, the numerator
of `S_m = ∑_{t ∈ t(m)} 1/t` is divisible by `m²/6`. -/
@[kb "hardywright2008" "Thm 128, p. 130"]
theorem sq_div_six_dvd_num_sum_inv (m : ℕ) (h2 : 2 ∣ m) (h3 : 3 ∣ m) (hm0 : m ≠ 0) :
    ((m ^ 2 / 6 : ℕ) : ℤ) ∣ (∑ t ∈ (range m).filter (·.Coprime m), (1 : ℚ) / t).num := by
  obtain ⟨a, M, ha, hM, rfl⟩ := exists_two_pow_mul_odd hm0 h2
  have hM3 : 3 ∣ M := (Nat.Coprime.dvd_of_dvd_mul_left
    (Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_three Nat.prime_two).2 (by norm_num)))
    h3)
  have hM1 : 1 < M := by obtain ⟨c, rfl⟩ := hM3; obtain ⟨j, hj⟩ := hM; omega
  obtain ⟨-, hA, hB⟩ := sum_sq_filter_dvd ha hM
  have hm1 : 1 < 2 ^ a * M := by
    have : 1 ≤ 2 ^ a := Nat.one_le_two_pow; nlinarith
  have := dvd_num_sum_inv_of (c := 3) hm1 ?_ ?_
  · simpa using this
  · rw [show 2 * 3 = 6 by norm_num]
    exact dvd_pow (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3) two_ne_zero
  · exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hM))
      ((hA hM1).mul_left 3) hB

/-- **Theorem 128** [hardywright2008] (Leudesdorf), (8.7.5): if `m = 2^a`, the numerator of
`S_m = ∑_{t ∈ t(m)} 1/t` is divisible by `m²/4`. -/
@[kb "hardywright2008" "Thm 128, p. 130"]
theorem sq_div_four_dvd_num_sum_inv {a : ℕ} (ha : 1 ≤ a) :
    (((2 ^ a) ^ 2 / 4 : ℕ) : ℤ) ∣
      (∑ t ∈ (range (2 ^ a)).filter (·.Coprime (2 ^ a)), (1 : ℚ) / t).num := by
  have hm1 : 1 < 2 ^ a := Nat.one_lt_two_pow (by omega)
  have := dvd_num_sum_inv_of (c := 2) hm1 ?_ (two_pow_dvd_two_mul_sum_sq ha)
  · simpa using this
  · rw [show 2 * 2 = 2 ^ 2 by norm_num, ← pow_mul]
    exact Nat.pow_dvd_pow 2 (by omega)

end NTKB.HardyWright
