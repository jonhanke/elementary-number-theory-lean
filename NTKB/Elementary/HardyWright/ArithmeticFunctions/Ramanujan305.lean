/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.ArithmeticFunctions.DirichletSeries

/-!
# Hardy–Wright, Theorem 305 (Ramanujan)

If `s`, `s - a`, `s - b`, `s - a - b` all exceed `1` (here: complex `s, a, b` with real parts of
`s`, `s - a`, `s - b`, `s - a - b` greater than `1`), then
`ζ(s) ζ(s-a) ζ(s-b) ζ(s-a-b) / ζ(2s-a-b) = ∑ σ_a(n) σ_b(n) n^{-s}`, `σ_a(n) = ∑_{d ∣ n} d^a`.

As for Theorems 300–304 the proof compares Euler factors: the identity of Dirichlet convolutions
`(σ_a σ_b) * h = 1 * P_a * P_b * P_{a+b}` (`P_c(n) = n^c`, `h(m²) = m^{a+b}`, `h = 0` off the
squares) is checked on prime powers (`ramanujan_local`, an identity of polynomials in `p^a`, `p^b`).
-/

open Finset ArithmeticFunction Complex
open scoped ArithmeticFunction.zeta ArithmeticFunction.sigma

namespace NTKB.HardyWright

/-- `n ↦ n^c` (and `0 ↦ 0`) as a complex arithmetic function. -/
noncomputable def powC (c : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else (n : ℂ) ^ c, by simp⟩

lemma powC_apply {c : ℂ} {n : ℕ} (hn : n ≠ 0) : powC c n = (n : ℂ) ^ c := by
  simp [powC, hn]

lemma isMultiplicative_powC (c : ℂ) : (powC c).IsMultiplicative := by
  refine ⟨by simp [powC], fun {m n} _ => ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp [powC]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [powC]
  rw [powC_apply (mul_ne_zero hm hn), powC_apply hm, powC_apply hn, Nat.cast_mul,
    natCast_mul_natCast_cpow]

lemma powC_prime_pow {c : ℂ} {p : ℕ} (hp : p.Prime) (i : ℕ) :
    powC c (p ^ i) = ((p : ℂ) ^ c) ^ i := by
  rw [powC_apply (pow_ne_zero _ hp.ne_zero), Nat.cast_pow, ← natCast_cpow_natCast_mul,
    cpow_nat_mul]

lemma norm_powC_le (c : ℂ) (n : ℕ) : ‖powC c n‖ ≤ (n : ℝ) ^ c.re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [powC, coe_mk, ↓reduceIte, norm_zero, Nat.cast_zero]
    exact Real.rpow_nonneg le_rfl _
  rw [powC_apply hn, norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]

lemma LSeriesSummable_powC {c s : ℂ} (h : 1 < (s - c).re) : LSeriesSummable (fun n => powC c n) s :=
  LSeriesSummable_of_le_const_mul_rpow (x := 1 + c.re) (by simp at h; linarith)
    ⟨1, fun n _ => by simpa using norm_powC_le c n⟩

/-- `∑ n^c n^{-s} = ζ(s - c)`. -/
lemma LSeries_powC {c s : ℂ} (h : 1 < (s - c).re) :
    LSeries (fun n => powC c n) s = riemannZeta (s - c) := by
  rw [← LSeries_one_eq_riemannZeta h, LSeries, LSeries]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, powC_apply hn, Pi.one_apply,
    cpow_sub _ _ hn', one_div_div]

/-- `σ_a = 1 * P_a`, `σ_a(n) = ∑_{d ∣ n} d^a`. -/
noncomputable def sigmaC (a : ℂ) : ArithmeticFunction ℂ := (ζ : ArithmeticFunction ℂ) * powC a

lemma sigmaC_apply (a : ℂ) {n : ℕ} : sigmaC a n = ∑ d ∈ n.divisors, (d : ℂ) ^ a := by
  rw [sigmaC, coe_zeta_mul_apply]
  exact sum_congr rfl fun d hd => powC_apply (Nat.pos_of_mem_divisors hd).ne'

lemma sigmaC_prime_pow (a : ℂ) {p : ℕ} (hp : p.Prime) (j : ℕ) :
    sigmaC a (p ^ j) = ∑ u ∈ range (j + 1), ((p : ℂ) ^ a) ^ u := by
  rw [sigmaC, coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp]
  exact sum_congr rfl fun u _ => powC_prime_pow hp u

/-- `h(m²) = m^{a+b}`, `h(n) = 0` if `n` is not a square. -/
noncomputable def sqWeight (a b : ℂ) : ArithmeticFunction ℂ :=
  (powIndicator 2).pmul (powC ((a + b) / 2))

lemma sqWeight_prime_pow (a b : ℂ) {p : ℕ} (hp : p.Prime) (i : ℕ) :
    sqWeight a b (p ^ i) = if 2 ∣ i then ((p : ℂ) ^ a * (p : ℂ) ^ b) ^ (i / 2) else 0 := by
  rw [sqWeight, pmul_apply, powIndicator_prime_pow hp, powC_prime_pow hp]
  split_ifs with h
  · obtain ⟨l, rfl⟩ := h
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [one_mul, Nat.mul_div_cancel_left l two_pos, pow_mul, ← cpow_nat_mul, Nat.cast_ofNat,
      mul_div_cancel₀ _ two_ne_zero, cpow_add _ _ hp0]
  · simp

lemma isMultiplicative_sqWeight (a b : ℂ) : (sqWeight a b).IsMultiplicative :=
  (isMultiplicative_powIndicator 2).pmul (isMultiplicative_powC _)

lemma norm_sqWeight_le (a b : ℂ) (n : ℕ) : ‖sqWeight a b n‖ ≤ (n : ℝ) ^ ((a + b) / 2).re := by
  rw [sqWeight, pmul_apply, norm_mul]
  calc ‖powIndicator 2 n‖ * ‖powC ((a + b) / 2) n‖ ≤ 1 * (n : ℝ) ^ ((a + b) / 2).re :=
        mul_le_mul (norm_powIndicator_le 2 n) (norm_powC_le _ n) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- `∑ h(n) n^{-s} = ∑ m^{a+b} m^{-2s} = ζ(2s - a - b)`. -/
lemma LSeries_sqWeight {a b s : ℂ} (h : 1 < (2 * s - a - b).re) :
    LSeries (fun n => sqWeight a b n) s = riemannZeta (2 * s - a - b) := by
  rw [← LSeries_one_eq_riemannZeta h, LSeries, LSeries]
  rw [← (Nat.pow_left_injective two_ne_zero).tsum_eq (f := LSeries.term (fun n => sqWeight a b n) s)]
  · refine tsum_congr fun m => ?_
    rcases eq_or_ne m 0 with rfl | hm
    · simp [LSeries.term]
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
    rw [LSeries.term_of_ne_zero (pow_ne_zero _ hm), LSeries.term_of_ne_zero hm, sqWeight, pmul_apply,
      powIndicator_apply_pow hm, one_mul, powC_apply (pow_ne_zero _ hm), Pi.one_apply, Nat.cast_pow,
      ← natCast_cpow_natCast_mul, ← natCast_cpow_natCast_mul, Nat.cast_ofNat,
      mul_div_cancel₀ _ two_ne_zero, show 2 * s - a - b = 2 * s - (a + b) by ring, cpow_sub _ _ hm',
      one_div_div]
  · intro n hn
    rw [Function.mem_support] at hn
    have hn0 : n ≠ 0 := by rintro rfl; simp at hn
    rw [LSeries.term_of_ne_zero hn0, sqWeight, pmul_apply] at hn
    have : powIndicator 2 n ≠ 0 := fun h => hn (by rw [h, zero_mul, zero_div])
    rw [powIndicator_apply] at this
    split_ifs at this with h'
    · obtain ⟨m, hm⟩ := (exists_pow_eq_iff_dvd_factorization h'.1).mpr h'.2
      exact ⟨m, hm⟩
    · exact absurd rfl this

set_option maxHeartbeats 1600000 in
/-- The local (Euler factor) identity behind Ramanujan's formula, Hardy–Wright Theorem 305:
with `x = p^a`, `y = p^b`, the coefficient of `p^{-ks}` in
`∑ σ_a(n) σ_b(n) n^{-s} · ζ(2s - a - b)` equals that in `ζ(s) ζ(s-a) ζ(s-b) ζ(s-a-b)`. -/
theorem ramanujan_local (x y : ℂ) (k : ℕ) :
    ∑ j ∈ range (k + 1),
        (if 2 ∣ k - j then
          (∑ u ∈ range (j + 1), x ^ u) * (∑ v ∈ range (j + 1), y ^ v) * (x * y) ^ ((k - j) / 2)
        else 0) =
      ∑ i ∈ range (k + 1), ∑ j ∈ range (i + 1), ∑ m ∈ range (j + 1),
        x ^ (j - m) * y ^ (i - j) * (x * y) ^ (k - i) := by
  have hL : ∑ j ∈ range (k + 1),
        (if 2 ∣ k - j then
          (∑ u ∈ range (j + 1), x ^ u) * (∑ v ∈ range (j + 1), y ^ v) * (x * y) ^ ((k - j) / 2)
        else 0) =
      ∑ t ∈ ((range (k+1) ×ˢ range (k+1) ×ˢ range (k+1)).filter
          (fun t : ℕ × ℕ × ℕ => 2 * t.1 ≤ k ∧ t.2.1 ≤ k - 2 * t.1 ∧ t.2.2 ≤ k - 2 * t.1)),
        x ^ t.2.1 * y ^ t.2.2 * (x * y) ^ t.1 := by
    rw [← sum_filter]
    have h1 : ∑ j ∈ (range (k+1)).filter (fun j => 2 ∣ k - j),
        (∑ u ∈ range (j + 1), x ^ u) * (∑ v ∈ range (j + 1), y ^ v) * (x * y) ^ ((k - j) / 2)
        = ∑ l ∈ (range (k+1)).filter (fun l => 2 * l ≤ k),
        (∑ u ∈ range (k - 2*l + 1), x ^ u) * (∑ v ∈ range (k - 2*l + 1), y ^ v) * (x * y) ^ l := by
      apply sum_nbij' (fun j => (k - j) / 2) (fun l => k - 2 * l)
      · intro j hj; simp only [mem_filter, mem_range] at hj ⊢; omega
      · intro l hl; simp only [mem_filter, mem_range] at hl ⊢; omega
      · intro j hj; simp only [mem_filter, mem_range] at hj; omega
      · intro l hl; simp only [mem_filter, mem_range] at hl; omega
      · intro j hj
        simp only [mem_filter, mem_range] at hj
        have h2 : k - 2 * ((k - j) / 2) = j := by omega
        rw [h2]
    have h3 : ∀ l ∈ (range (k+1)).filter (fun l => 2 * l ≤ k),
        (∑ u ∈ range (k - 2*l + 1), x ^ u) * (∑ v ∈ range (k - 2*l + 1), y ^ v) * (x * y) ^ l
        = ∑ t ∈ (range (k+1) ×ˢ range (k+1)).filter
            (fun t : ℕ × ℕ => t.1 ≤ k - 2 * l ∧ t.2 ≤ k - 2 * l), x ^ t.1 * y ^ t.2 * (x * y) ^ l := by
      intro l hl
      have : (range (k+1) ×ˢ range (k+1)).filter
            (fun t : ℕ × ℕ => t.1 ≤ k - 2 * l ∧ t.2 ≤ k - 2 * l)
            = range (k - 2*l + 1) ×ˢ range (k - 2*l + 1) := by
        ext t; simp only [mem_filter, mem_product, mem_range]; omega
      rw [this, sum_product, sum_mul, sum_mul]
      apply sum_congr rfl; intro u _
      rw [mul_sum, sum_mul]
    rw [h1, sum_congr rfl h3, sum_filter (fun t : ℕ × ℕ × ℕ => _), sum_product]
    rw [sum_filter]
    apply sum_congr rfl; intro l hl
    by_cases hl2 : 2 * l ≤ k
    · simp only [hl2, ite_true, true_and]
      rw [sum_filter, sum_product]
    · simp [hl2]
  have hR : ∑ i ∈ range (k + 1), ∑ j ∈ range (i + 1), ∑ m ∈ range (j + 1),
        x ^ (j - m) * y ^ (i - j) * (x * y) ^ (k - i) =
      ∑ t ∈ ((range (k+1) ×ˢ range (k+1) ×ˢ range (k+1)).filter
          (fun t : ℕ × ℕ × ℕ => t.2.1 ≤ t.1 ∧ t.2.2 ≤ t.2.1)),
        x ^ (t.2.1 - t.2.2) * y ^ (t.1 - t.2.1) * (x * y) ^ (k - t.1) := by
    rw [sum_filter, sum_product]
    apply sum_congr rfl; intro i hi
    rw [sum_product]
    simp only [mem_range] at hi
    have e : ∀ (n : ℕ), n < k + 1 → ∀ (G : ℕ → ℂ), ∑ j ∈ range (n+1), G j = ∑ j ∈ range (k+1), if j ≤ n then G j else 0 := by
      intro n hn G
      rw [← sum_filter]
      apply sum_congr _ (fun _ _ => rfl)
      ext j; simp only [mem_filter, mem_range]; omega
    rw [e i hi]
    apply sum_congr rfl; intro j hj
    simp only [mem_range] at hj
    by_cases hji : j ≤ i
    · simp only [hji, true_and, ite_true]
      rw [e j hj]
    · simp [hji]
  rw [hL, hR]
  refine sum_nbij'
    (fun t : ℕ × ℕ × ℕ =>
      let i4 := (t.2.1 + t.1 + (t.2.2 + t.1) - k) + t.1
      let i := k - i4
      let j := i - (t.2.2 + t.1 - i4)
      (i, j, j - (t.2.1 + t.1 - i4)))
    (fun t : ℕ × ℕ × ℕ =>
      let A := (t.2.1 - t.2.2) + (k - t.1)
      let B := (t.1 - t.2.1) + (k - t.1)
      let l := (k - t.1) - (A + B - k)
      (l, A - l, B - l)) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    simp only [mem_filter, mem_product, mem_range] at ht ⊢
    omega
  · intro t ht
    simp only [mem_filter, mem_product, mem_range] at ht ⊢
    omega
  · intro t ht
    simp only [mem_filter, mem_product, mem_range] at ht
    ext <;> simp only <;> omega
  · intro t ht
    simp only [mem_filter, mem_product, mem_range] at ht
    ext <;> simp only <;> omega
  · intro t ht
    simp only [mem_filter, mem_product, mem_range] at ht
    obtain ⟨l, u, v⟩ := t
    simp only at ht ⊢
    have key : ∀ a b c a' b' c' : ℕ, a + c = a' + c' → b + c = b' + c' →
        x ^ a * y ^ b * (x * y) ^ c = x ^ a' * y ^ b' * (x * y) ^ c' := by
      intro a b c a' b' c' h1 h2
      have e1 : x ^ a * y ^ b * (x * y) ^ c = x ^ (a + c) * y ^ (b + c) := by
        rw [pow_add, pow_add, mul_pow]; ring
      have e2 : x ^ a' * y ^ b' * (x * y) ^ c' = x ^ (a' + c') * y ^ (b' + c') := by
        rw [pow_add, pow_add, mul_pow]; ring
      rw [e1, e2, h1, h2]
    apply key <;> omega

/-- The coefficient identity of Theorem 305: `(σ_a σ_b) * h = 1 * P_a * P_b * P_{a+b}`. -/
lemma sigmaC_pmul_mul_sqWeight (a b : ℂ) :
    (sigmaC a).pmul (sigmaC b) * sqWeight a b =
      (ζ : ArithmeticFunction ℂ) * powC a * powC b * powC (a + b) := by
  have hσ : ∀ c, (sigmaC c).IsMultiplicative := fun c =>
    isMultiplicative_zeta.natCast.mul (isMultiplicative_powC c)
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _
    (((hσ a).pmul (hσ b)).mul (isMultiplicative_sqWeight a b)) _
    (((isMultiplicative_zeta.natCast.mul (isMultiplicative_powC a)).mul
      (isMultiplicative_powC b)).mul (isMultiplicative_powC _))).mpr fun p k hp => ?_
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  set x := (p : ℂ) ^ a
  set y := (p : ℂ) ^ b
  have hxy : (p : ℂ) ^ (a + b) = x * y := cpow_add _ _ hp0
  rw [mul_apply_prime_pow _ _ hp, mul_apply_prime_pow _ _ hp]
  simp only [pmul_apply, sigmaC_prime_pow _ hp, sqWeight_prime_pow _ _ hp, powC_prime_pow hp, hxy,
    mul_ite, mul_zero]
  rw [ramanujan_local x y k]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_apply_prime_pow _ _ hp, sum_mul]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_apply_prime_pow _ _ hp, sum_mul, sum_mul]
  refine sum_congr rfl fun m _ => ?_
  simp only [natCoe_apply, zeta_apply, pow_ne_zero _ hp.ne_zero, ↓reduceIte, Nat.cast_one,
    one_mul, powC_prime_pow hp]
  rfl

/-- `|σ_a(n)| ≤ d(n) n^{max(Re a, 0)}`. -/
lemma norm_sigmaC_le (a : ℂ) {n : ℕ} (hn : n ≠ 0) :
    ‖sigmaC a n‖ ≤ (σ 0 n : ℝ) * (n : ℝ) ^ max a.re 0 := by
  rw [sigmaC_apply, ArithmeticFunction.sigma_zero_apply, ← nsmul_eq_mul, ← sum_const]
  refine (norm_sum_le _ _).trans (sum_le_sum fun d hd => ?_)
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  have hdn : (d : ℝ) ≤ n := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.dvd_of_mem_divisors hd)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
  rw [norm_natCast_cpow_of_pos hd0]
  calc (d : ℝ) ^ a.re ≤ (d : ℝ) ^ max a.re 0 := Real.rpow_le_rpow_of_exponent_le hd1 (le_max_left _ _)
    _ ≤ (n : ℝ) ^ max a.re 0 := Real.rpow_le_rpow (by positivity) hdn (le_max_right _ _)

lemma LSeriesSummable_sigmaC_pmul {a b s : ℂ} (hs : 1 + max a.re 0 + max b.re 0 < s.re) :
    LSeriesSummable (fun n => (sigmaC a).pmul (sigmaC b) n) s := by
  set δ := (s.re - 1 - max a.re 0 - max b.re 0) / 4 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have h1 := card_divisors_isBigO_rpow hδ0
  refine LSeriesSummable_of_isBigO_rpow (x := 1 + 2 * δ + max a.re 0 + max b.re 0)
    (by rw [hδ]; linarith) ?_
  have h2 : (fun n : ℕ => (σ 0 n : ℝ) * (n : ℝ) ^ max a.re 0 * ((σ 0 n : ℝ) * (n : ℝ) ^ max b.re 0))
      =O[Filter.atTop] fun n : ℕ => (n : ℝ) ^ δ * (n : ℝ) ^ max a.re 0 *
        ((n : ℝ) ^ δ * (n : ℝ) ^ max b.re 0) :=
    (h1.mul (Asymptotics.isBigO_refl _ _)).mul (h1.mul (Asymptotics.isBigO_refl _ _))
  refine Asymptotics.IsBigO.trans ?_ (h2.trans (Asymptotics.IsBigO.of_bound 1 ?_))
  · refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    rw [pmul_apply, norm_mul, one_mul, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul (norm_sigmaC_le a hn.ne') (norm_sigmaC_le b hn.ne') (norm_nonneg _)
      (by positivity)
  · filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [one_mul, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity),
      ← Real.rpow_add hn', ← Real.rpow_add hn', ← Real.rpow_add hn']
    apply le_of_eq; congr 1; ring

/-- **Theorem 305** (Ramanujan; Hardy–Wright). If `s`, `s - a`, `s - b`, `s - a - b` all have real
part greater than `1`, then
`∑ σ_a(n) σ_b(n) n^{-s} = ζ(s) ζ(s-a) ζ(s-b) ζ(s-a-b) / ζ(2s-a-b)`, `σ_a(n) = ∑_{d ∣ n} d^a`. -/
@[kb "hardywright2008" "Thm 305, p. 356"]
theorem LSeries_sigma_mul_sigma {a b s : ℂ} (h1 : 1 < s.re) (h2 : 1 < (s - a).re)
    (h3 : 1 < (s - b).re) (h4 : 1 < (s - a - b).re) :
    LSeries (fun n => (∑ d ∈ n.divisors, (d : ℂ) ^ a) * (∑ d ∈ n.divisors, (d : ℂ) ^ b)) s =
      riemannZeta s * riemannZeta (s - a) * riemannZeta (s - b) * riemannZeta (s - a - b) /
        riemannZeta (2 * s - a - b) := by
  simp only [sub_re] at h2 h3 h4
  have hmax : 1 + max a.re 0 + max b.re 0 < s.re := by
    rcases le_total a.re 0 with ha | ha <;> rcases le_total b.re 0 with hb | hb <;>
      simp [ha, hb] <;> linarith
  have h2s : 1 < (2 * s - a - b).re := by simp; linarith
  have hσ := LSeriesSummable_sigmaC_pmul hmax
  have hh : LSeriesSummable (fun n => sqWeight a b n) s :=
    LSeriesSummable_of_le_const_mul_rpow (x := 1 + ((a + b) / 2).re) (by simp; linarith)
      ⟨1, fun n _ => by simpa using norm_sqWeight_le a b n⟩
  have hζ := LSeriesSummable_zetaC h1
  have hPa : LSeriesSummable (fun n => powC a n) s := LSeriesSummable_powC (by simp; linarith)
  have hPb : LSeriesSummable (fun n => powC b n) s := LSeriesSummable_powC (by simp; linarith)
  have hPab : LSeriesSummable (fun n => powC (a + b) n) s := LSeriesSummable_powC (by simp; linarith)
  have hmul := LSeries_mul' hσ hh
  rw [sigmaC_pmul_mul_sqWeight, LSeries_mul' (LSeriesSummable_mul (LSeriesSummable_mul hζ hPa) hPb)
    hPab, LSeries_mul' (LSeriesSummable_mul hζ hPa) hPb, LSeries_mul' hζ hPa, LSeries_zetaC h1,
    LSeries_powC (by simp; linarith), LSeries_powC (by simp; linarith),
    LSeries_powC (by simp; linarith), LSeries_sqWeight h2s] at hmul
  have hcongr : LSeries (fun n => (∑ d ∈ n.divisors, (d : ℂ) ^ a) * (∑ d ∈ n.divisors, (d : ℂ) ^ b)) s
      = LSeries (fun n => (sigmaC a).pmul (sigmaC b) n) s := by
    congr 1; funext n; rw [pmul_apply, sigmaC_apply, sigmaC_apply]
  rw [hcongr, eq_div_iff (riemannZeta_ne_zero_of_one_lt_re h2s), ← hmul,
    show s - (a + b) = s - a - b by ring]

end NTKB.HardyWright
