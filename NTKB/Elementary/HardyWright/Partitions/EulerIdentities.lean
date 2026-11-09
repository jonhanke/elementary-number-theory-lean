/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.Partitions.JacobiTriple

/-!
# Euler's identities and finite `q`-identities (Hardy–Wright, Chapter XIX, §§ 19.5–19.6)

For complex `x` with `‖x‖ < 1` (in the book the identities are formal, or for small `x`):

* Theorem 348: `(1 + ax)(1 + ax²)…(1 + axʲ) = ∑_{m=0}^{j} a^m x^{m(m+1)/2} · (1 - xʲ)…(1 - x^{j-m+1}) /
  ((1 - x)…(1 - x^m))` (`prod_one_add_mul_pow_eq_sum_qBinom`; the quotient is the Gaussian binomial coefficient `qBinom x j m`,
  `qBinom_eq_prod_div`).
* Theorem 349: `1/((1 - ax)…(1 - axʲ)) = ∑_{m ≥ 0} a^m x^m (1 - xʲ)…(1 - x^{j+m-1}) /
  ((1 - x)…(1 - x^m))` for `j ≥ 1` and `‖ax‖ < 1` (`hasSum_one_div_prod_one_sub_mul_pow`).
* Theorem 350: `1/((1 - x)(1 - x²)…) = ∑_{m ≥ 0} x^m / ((1 - x)…(1 - x^m))` (`hasSum_one_div_tprod_one_sub_pow`), the case `a = 1`,
  `j → ∞` of a more general infinite identity `hasSum_inv_tprod_one_sub_mul_pow` (`‖ax‖ < 1`).
* The infinite Euler identity `∏_{k ≥ 0} (1 + a q^k) = ∑_{m ≥ 0} a^m q^{m(m-1)/2} / ((1 - q)…(1 - q^m))`
  for every complex `a` (`hasProd_one_add_mul_pow`), and its consequences: (19.5.1)
  `(1 + ax)(1 + ax³)(1 + ax⁵)… = ∑ a^m x^{m²} / ((1 - x²)…(1 - x^{2m}))` for every `a`, and the two
  Theorems 345 (`a = 1`) and 346 (`a = x`).

Hardy–Wright prove (19.5.1) by comparing coefficients of a power series in `a` and Theorem 348 by a
recurrence in `j`. Here Theorem 348 is the `q`-binomial theorem `NTKB.Apostol.qbinomial_theorem`
(`q = x`, `t = ax`); Theorem 349 follows from the `q`-Pascal rule, which gives
`S_{J+1} = S_J + a x^{J+2} S_{J+1}` for `S_J(a) = ∑ (ax)^m [J+m, m]_x`; the infinite identities
follow from the finite ones by Tannery's theorem (dominated convergence for series), using
`[N, m]_q → 1/(q;q)_m` as `N → ∞` and the uniform bound on the Gaussian binomial coefficients.
-/

open Complex Finset Filter NTKB.Apostol
open scoped Topology

namespace NTKB.HardyWright

/-! ### Elementary lemmas -/

theorem choose_two_add_self (m : ℕ) : m.choose 2 + m = m * (m + 1) / 2 := by
  have h : 2 * (m.choose 2 + m) = m * (m + 1) := by
    have := two_mul_choose_two m
    zify
    linear_combination this
  rw [← h]; omega

theorem add_two_mul_choose_two (m : ℕ) : m + 2 * m.choose 2 = m ^ 2 := by
  have := two_mul_choose_two m
  zify
  linear_combination this

theorem qPoch_eq_mul_prod {x : ℂ} {j m : ℕ} (h : m ≤ j) :
    qPoch x j = qPoch x (j - m) * ∏ i ∈ range m, (1 - x ^ (j - i)) := by
  obtain ⟨d, rfl⟩ : ∃ d, j = d + m := ⟨j - m, by omega⟩
  rw [Nat.add_sub_cancel, qPoch, qPoch, prod_range_add]
  congr 1
  rw [← prod_range_reflect]
  refine prod_congr rfl fun i hi ↦ ?_
  have := mem_range.1 hi
  congr 2
  omega

/-- The Gaussian binomial coefficient is the quotient `(1 - xʲ)…(1 - x^{j-m+1}) / ((1 - x)…(1 - x^m))`
of the book (Theorem 348). -/
theorem qBinom_eq_prod_div {x : ℂ} (hx : ‖x‖ < 1) {j m : ℕ} (h : m ≤ j) :
    qBinom x j m = (∏ i ∈ range m, (1 - x ^ (j - i))) / ∏ i ∈ range m, (1 - x ^ (i + 1)) := by
  have e : qPoch x m = ∏ i ∈ range m, (1 - x ^ (i + 1)) := rfl
  have h1 := qPoch_ne_zero hx (j - m)
  have h2 := qPoch_ne_zero hx m
  rw [e] at h2
  rw [qBinom]
  simp only [h, ↓reduceIte]
  rw [qPoch_eq_mul_prod h, e]
  field_simp

/-! ### Theorem 348 -/

/-- **Theorem 348.** For `‖x‖ < 1`,
`(1 + ax)(1 + ax²)…(1 + axʲ) = ∑_{m=0}^{j} a^m x^{m(m+1)/2} ·
(1 - xʲ)(1 - x^{j-1})…(1 - x^{j-m+1}) / ((1 - x)(1 - x²)…(1 - x^m))`. -/
@[kb "hardywright2008" "Thm 348, p. 389"]
theorem prod_one_add_mul_pow_eq_sum_qBinom {x : ℂ} (hx : ‖x‖ < 1) (a : ℂ) (j : ℕ) :
    ∏ k ∈ range j, (1 + a * x ^ (k + 1)) =
      ∑ m ∈ range (j + 1), a ^ m * x ^ (m * (m + 1) / 2) *
        ((∏ i ∈ range m, (1 - x ^ (j - i))) / ∏ i ∈ range m, (1 - x ^ (i + 1))) := by
  have h := qbinomial_theorem hx (a * x) j
  rw [prod_congr rfl (fun k _ ↦ show 1 + x ^ k * (a * x) = 1 + a * x ^ (k + 1) by ring)] at h
  rw [h]
  refine sum_congr rfl fun m hm ↦ ?_
  rw [qBinom_eq_prod_div hx (Nat.lt_succ_iff.1 (mem_range.1 hm)), ← choose_two_add_self, pow_add,
    mul_pow]
  ring

/-! ### Theorem 349 -/

section Thm349

variable {x a : ℂ}

/-- `S_J(a) = ∑_{m ≥ 0} (ax)^m [J+m, m]_x`. -/
noncomputable def eulerS (x a : ℂ) (J : ℕ) : ℂ := ∑' m : ℕ, (a * x) ^ m * qBinom x (J + m) m

theorem summable_eulerS (hx : ‖x‖ < 1) (ha : ‖a * x‖ < 1) (J : ℕ) :
    Summable fun m : ℕ ↦ (a * x) ^ m * qBinom x (J + m) m := by
  obtain ⟨B, hB⟩ := exists_norm_qBinom_le hx
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (norm_nonneg _) ha).mul_right B) fun m ↦ ?_
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (hB _ _) (by positivity)

theorem eulerS_succ (hx : ‖x‖ < 1) (ha : ‖a * x‖ < 1) (J : ℕ) :
    eulerS x a (J + 1) = eulerS x a J + a * x ^ (J + 2) * eulerS x a (J + 1) := by
  have h1 := summable_eulerS hx ha J
  have h2 := summable_eulerS hx ha (J + 1)
  have key : ∀ m : ℕ, (a * x) ^ (m + 1) * qBinom x (J + 1 + (m + 1)) (m + 1) =
      (a * x) ^ (m + 1) * qBinom x (J + (m + 1)) (m + 1) +
        a * x ^ (J + 2) * ((a * x) ^ m * qBinom x (J + 1 + m) m) := by
    intro m
    rw [show J + 1 + (m + 1) = (J + 1 + m) + 1 by omega,
      qBinom_succ_succ hx (by omega : m ≤ J + 1 + m), show J + 1 + m - m = J + 1 by omega,
      show J + (m + 1) = J + 1 + m by omega]
    ring
  have A : eulerS x a (J + 1) =
      1 + ∑' m : ℕ, (a * x) ^ (m + 1) * qBinom x (J + 1 + (m + 1)) (m + 1) := by
    unfold eulerS
    rw [h2.tsum_eq_zero_add]
    simp only [pow_zero, one_mul, add_zero, qBinom_zero_right hx]
  have Bq : eulerS x a J =
      1 + ∑' m : ℕ, (a * x) ^ (m + 1) * qBinom x (J + (m + 1)) (m + 1) := by
    unfold eulerS
    rw [h1.tsum_eq_zero_add]
    simp only [pow_zero, one_mul, add_zero, qBinom_zero_right hx]
  have hsum : ∑' m : ℕ, (a * x) ^ (m + 1) * qBinom x (J + 1 + (m + 1)) (m + 1) =
      ∑' m : ℕ, (a * x) ^ (m + 1) * qBinom x (J + (m + 1)) (m + 1) +
        a * x ^ (J + 2) * eulerS x a (J + 1) := by
    rw [tsum_congr key, ((summable_nat_add_iff 1).2 h1).tsum_add (h2.mul_left _), tsum_mul_left]
    rfl
  linear_combination A - Bq + hsum

theorem eulerS_mul_prod (hx : ‖x‖ < 1) (ha : ‖a * x‖ < 1) (J : ℕ) :
    eulerS x a J * ∏ k ∈ range (J + 1), (1 - a * x ^ (k + 1)) = 1 := by
  induction J with
  | zero =>
    have : eulerS x a 0 = ∑' m : ℕ, (a * x) ^ m := by
      unfold eulerS
      refine tsum_congr fun m ↦ ?_
      rw [zero_add, qBinom_self hx, mul_one]
    rw [this, tsum_geometric_of_norm_lt_one ha]
    have : 1 - a * x ≠ 0 := by
      intro h
      have : a * x = 1 := (sub_eq_zero.1 h).symm
      rw [this, norm_one] at ha
      exact lt_irrefl _ ha
    simp only [zero_add, prod_range_one, pow_one]
    exact inv_mul_cancel₀ this
  | succ J ih =>
    rw [prod_range_succ]
    have hs := eulerS_succ hx ha J
    linear_combination (∏ k ∈ range (J + 1), (1 - a * x ^ (k + 1))) * hs + ih

/-- **Theorem 349.** For `j ≥ 1`, `‖x‖ < 1`, `‖ax‖ < 1`,
`1 / ((1 - ax)(1 - ax²)…(1 - axʲ)) = ∑_{m ≥ 0} a^m x^m (1 - xʲ)(1 - x^{j+1})…(1 - x^{j+m-1}) /
((1 - x)(1 - x²)…(1 - x^m))`. -/
@[kb "hardywright2008" "Thm 349, p. 389"]
theorem hasSum_one_div_prod_one_sub_mul_pow (hx : ‖x‖ < 1) (ha : ‖a * x‖ < 1) {j : ℕ} (hj : 1 ≤ j) :
    HasSum (fun m : ℕ ↦ (a * x) ^ m *
      ((∏ i ∈ range m, (1 - x ^ (j + i))) / ∏ i ∈ range m, (1 - x ^ (i + 1))))
      (1 / ∏ k ∈ range j, (1 - a * x ^ (k + 1))) := by
  obtain ⟨J, rfl⟩ : ∃ J, j = J + 1 := ⟨j - 1, by omega⟩
  have hS := (summable_eulerS hx ha J).hasSum
  have h1 : eulerS x a J = 1 / ∏ k ∈ range (J + 1), (1 - a * x ^ (k + 1)) :=
    eq_one_div_of_mul_eq_one_left (eulerS_mul_prod hx ha J)
  rw [← h1]
  convert hS using 2 with m
  rw [qBinom_eq_prod_div hx (by omega : m ≤ J + m)]
  congr 2
  rw [← prod_range_reflect]
  refine prod_congr rfl fun i hi ↦ ?_
  have := mem_range.1 hi
  congr 2
  omega
  rfl

end Thm349

/-! ### Theorem 350 and the infinite version -/

section Infinite

variable {x a : ℂ}

theorem summable_norm_mul_pow_succ (hx : ‖x‖ < 1) :
    Summable fun k : ℕ ↦ ‖a * x ^ (k + 1)‖ := by
  refine ((summable_geometric_of_lt_one (norm_nonneg _) hx).mul_left ‖a * x‖).congr fun k ↦ ?_
  simp only [norm_mul, norm_pow]
  ring

theorem multipliable_one_sub_mul_pow (hx : ‖x‖ < 1) :
    Multipliable fun k : ℕ ↦ (1 - a * x ^ (k + 1)) :=
  multipliable_one_sub_of_summable (summable_norm_mul_pow_succ hx)

/-- The infinite form of Theorem 349 (`j → ∞`): for `‖x‖ < 1`, `‖ax‖ < 1`,
`1 / ∏_{k ≥ 1} (1 - a x^k) = ∑_{m ≥ 0} (ax)^m / ((1 - x)(1 - x²)…(1 - x^m))`. -/
theorem hasSum_inv_tprod_one_sub_mul_pow (hx : ‖x‖ < 1) (ha : ‖a * x‖ < 1) :
    HasSum (fun m : ℕ ↦ (a * x) ^ m / qPoch x m)
      (1 / ∏' k : ℕ, (1 - a * x ^ (k + 1))) := by
  set P := qPochInf x with hP
  have hP0 : P ≠ 0 := qPochInf_ne_zero hx
  obtain ⟨B, hB⟩ := exists_norm_qBinom_le hx
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 0)
  have hbound : Summable fun m : ℕ ↦ B * ‖a * x‖ ^ m :=
    (summable_geometric_of_lt_one (norm_nonneg _) ha).mul_left B
  have hpt : ∀ m : ℕ, Tendsto (fun J : ℕ ↦ (a * x) ^ m * qBinom x (J + m) m) atTop
      (𝓝 ((a * x) ^ m / qPoch x m)) := by
    intro m
    have hm0 := qPoch_ne_zero hx m
    have hlim : Tendsto (fun J : ℕ ↦ qPoch x (J + m) / (qPoch x m * qPoch x J)) atTop
        (𝓝 (P / (qPoch x m * P))) :=
      ((tendsto_qPoch hx).comp (tendsto_add_atTop_nat m)).div
        ((tendsto_const_nhds).mul (tendsto_qPoch hx)) (mul_ne_zero hm0 hP0)
    have e : (a * x) ^ m / qPoch x m = (a * x) ^ m * (P / (qPoch x m * P)) := by
      field_simp
    rw [e]
    refine (hlim.const_mul _).congr fun J ↦ ?_
    simp only [qBinom, Nat.le_add_left m J, ↓reduceIte, Nat.add_sub_cancel]
  have hbd : ∀ J m : ℕ, ‖(a * x) ^ m * qBinom x (J + m) m‖ ≤ B * ‖a * x‖ ^ m := fun J m ↦ by
    rw [norm_mul, norm_pow, mul_comm B]
    exact mul_le_mul_of_nonneg_left (hB _ _) (by positivity)
  have htann := tendsto_tsum_of_dominated_convergence hbound hpt (Eventually.of_forall hbd)
  have hsum : Summable fun m : ℕ ↦ (a * x) ^ m / qPoch x m := by
    refine Summable.of_norm_bounded (g := fun m ↦ B * ‖a * x‖ ^ m) hbound fun m ↦ ?_
    have hle := le_of_tendsto' ((hpt m).norm) fun J ↦ hbd J m
    simpa [norm_div, norm_pow] using hle
  have hmul := multipliable_one_sub_mul_pow (a := a) hx
  have hprod := (hmul.hasProd.tendsto_prod_nat).comp (tendsto_add_atTop_nat 1)
  have hlim := htann.mul hprod
  have hconst : Tendsto (fun J : ℕ ↦ eulerS x a J * ∏ k ∈ range (J + 1), (1 - a * x ^ (k + 1)))
      atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr fun J ↦ ?_
    exact (eulerS_mul_prod hx ha J).symm
  have heq := tendsto_nhds_unique hlim hconst
  have : ∑' m : ℕ, (a * x) ^ m / qPoch x m = 1 / ∏' k : ℕ, (1 - a * x ^ (k + 1)) :=
    eq_one_div_of_mul_eq_one_left heq
  rw [← this]
  exact hsum.hasSum

/-- **Theorem 350.** For `‖x‖ < 1`,
`1 / ((1 - x)(1 - x²)(1 - x³)…) = 1 + x/(1 - x) + x²/((1 - x)(1 - x²)) + …`
(the case `a = 1`, `j → ∞` of Theorem 349). -/
@[kb "hardywright2008" "Thm 350, p. 389"]
theorem hasSum_one_div_tprod_one_sub_pow (hx : ‖x‖ < 1) :
    HasSum (fun m : ℕ ↦ x ^ m / ∏ i ∈ range m, (1 - x ^ (i + 1)))
      (1 / ∏' k : ℕ, (1 - x ^ (k + 1))) := by
  have h := hasSum_inv_tprod_one_sub_mul_pow (a := 1) hx (by simpa using hx)
  simpa [qPoch] using h

end Infinite

/-! ### The infinite Euler identity and (19.5.1) -/

section EulerInfinite

variable {q : ℂ}

theorem summable_norm_mul_pow_choose_two (hq : ‖q‖ < 1) (a : ℂ) :
    Summable fun m : ℕ ↦ ‖a ^ m * q ^ (m.choose 2)‖ := by
  refine summable_of_ratio_norm_eventually_le (r := 1 / 2) (by norm_num) ?_
  have ht : Tendsto (fun m : ℕ ↦ ‖a‖ * ‖q‖ ^ m) atTop (𝓝 (‖a‖ * 0)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hq).const_mul _
  rw [mul_zero] at ht
  filter_upwards [ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))] with m hm
  have e : ‖a ^ (m + 1) * q ^ ((m + 1).choose 2)‖ =
      (‖a‖ * ‖q‖ ^ m) * ‖a ^ m * q ^ (m.choose 2)‖ := by
    simp only [choose_two_succ, norm_mul, norm_pow, pow_succ, pow_add]
    ring
  rw [norm_norm, norm_norm, e]
  exact mul_le_mul_of_nonneg_right hm.le (norm_nonneg _)

/-- **The infinite Euler identity.** For `‖q‖ < 1` and every complex `a`,
`∏_{k ≥ 0} (1 + a q^k) = ∑_{m ≥ 0} a^m q^{m(m-1)/2} / ((1 - q)(1 - q²)…(1 - q^m))`.
(Here `m(m-1)/2` is written `m.choose 2`.) It is the limit `N → ∞` of the finite `q`-binomial
theorem `NTKB.Apostol.qbinomial_theorem`. -/
theorem hasProd_one_add_mul_pow (hq : ‖q‖ < 1) (a : ℂ) :
    HasProd (fun k : ℕ ↦ 1 + a * q ^ k)
      (∑' m : ℕ, a ^ m * q ^ (m.choose 2) / qPoch q m) := by
  set P := qPochInf q with hP
  have hP0 : P ≠ 0 := qPochInf_ne_zero hq
  obtain ⟨B, hB⟩ := exists_norm_qBinom_le hq
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 0)
  have hbound := (summable_norm_mul_pow_choose_two hq a).mul_left B
  set G : ℕ → ℕ → ℂ := fun N j ↦ q ^ (j.choose 2) * qBinom q N j * a ^ j with hG
  set g : ℕ → ℂ := fun j ↦ a ^ j * q ^ (j.choose 2) / qPoch q j with hg
  have hpt : ∀ j : ℕ, Tendsto (fun N ↦ G N j) atTop (𝓝 (g j)) := by
    intro j
    have hj0 := qPoch_ne_zero hq j
    have hlim : Tendsto (fun N : ℕ ↦ qPoch q N / (qPoch q j * qPoch q (N - j))) atTop
        (𝓝 (P / (qPoch q j * P))) :=
      ((tendsto_qPoch hq)).div
        ((tendsto_const_nhds).mul ((tendsto_qPoch hq).comp (tendsto_sub_atTop_nat j)))
        (mul_ne_zero hj0 hP0)
    have e : g j = q ^ (j.choose 2) * (P / (qPoch q j * P)) * a ^ j := by
      simp only [hg]; field_simp
    rw [e]
    refine ((hlim.const_mul _).mul_const _).congr' ?_
    filter_upwards [eventually_ge_atTop j] with N hN
    simp only [hG, qBinom, hN, ↓reduceIte]
  have hbd : ∀ᶠ N in atTop, ∀ j, ‖G N j‖ ≤ B * ‖a ^ j * q ^ (j.choose 2)‖ :=
    Eventually.of_forall fun N j ↦ by
      simp only [hG, norm_mul]
      calc ‖q ^ j.choose 2‖ * ‖qBinom q N j‖ * ‖a ^ j‖
          ≤ ‖q ^ j.choose 2‖ * B * ‖a ^ j‖ := by gcongr; exact hB _ _
        _ = B * (‖a ^ j‖ * ‖q ^ j.choose 2‖) := by ring
  have htann := tendsto_tsum_of_dominated_convergence hbound hpt hbd
  have hfin : ∀ N : ℕ, ∏ k ∈ range N, (1 + a * q ^ k) = ∑' j, G N j := by
    intro N
    rw [prod_congr rfl (fun k _ ↦ show 1 + a * q ^ k = 1 + q ^ k * a by ring),
      qbinomial_theorem hq a N, tsum_eq_sum (s := range (N + 1))]
    intro j hj
    have : N < j := by simpa using hj
    simp [hG, qBinom_of_lt this]
  have hgeom : Summable fun k : ℕ ↦ ‖a * q ^ k‖ := by
    refine ((summable_geometric_of_lt_one (norm_nonneg _) hq).mul_left ‖a‖).congr fun k ↦ ?_
    rw [norm_mul, norm_pow]
  have hmul := multipliable_one_add_of_summable hgeom
  have hA := hmul.hasProd.tendsto_prod_nat
  have heq := tendsto_nhds_unique (hA.congr hfin) htann
  rw [← heq]
  exact hmul.hasProd

end EulerInfinite

/-- **(19.5.1).** For `‖x‖ < 1` and every complex `a`,
`(1 + ax)(1 + ax³)(1 + ax⁵)… = 1 + ax/(1 - x²) + a²x⁴/((1 - x²)(1 - x⁴)) + …`, i.e.
`∏_{k ≥ 0} (1 + a x^{2k+1}) = ∑_{m ≥ 0} a^m x^{m²} / ((1 - x²)(1 - x⁴)…(1 - x^{2m}))`
(`qPoch (x ^ 2) m = (1 - x²)(1 - x⁴)…(1 - x^{2m})`). -/
@[kb "hardywright2008" "(19.5.1), p. 386"]
theorem hasProd_one_add_mul_pow_odd {x : ℂ} (hx : ‖x‖ < 1) (a : ℂ) :
    HasProd (fun k : ℕ ↦ 1 + a * x ^ (2 * k + 1))
      (∑' m : ℕ, a ^ m * x ^ (m ^ 2) / qPoch (x ^ 2) m) := by
  have hq : ‖x ^ 2‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hx two_ne_zero
  have h := hasProd_one_add_mul_pow hq (a * x)
  convert h using 1
  · funext k
    rw [← pow_mul, pow_succ, pow_mul]
    ring
  · refine tsum_congr fun m ↦ ?_
    rw [mul_pow, ← pow_mul, mul_assoc, ← pow_add, add_two_mul_choose_two]

/-- **Theorem 345** (Euler). For `‖x‖ < 1`,
`(1 + x)(1 + x³)(1 + x⁵)… = 1 + x/(1 - x²) + x⁴/((1 - x²)(1 - x⁴)) + x⁹/((1 - x²)(1 - x⁴)(1 - x⁶)) + …`
(the case `a = 1` of (19.5.1)). -/
@[kb "hardywright2008" "Thm 345, p. 385"]
theorem tprod_one_add_pow_odd_eq_tsum {x : ℂ} (hx : ‖x‖ < 1) :
    HasProd (fun k : ℕ ↦ 1 + x ^ (2 * k + 1))
      (∑' m : ℕ, x ^ (m ^ 2) / ∏ i ∈ range m, (1 - (x ^ 2) ^ (i + 1))) := by
  simpa [qPoch] using hasProd_one_add_mul_pow_odd hx 1

/-- **Theorem 346** (Euler). For `‖x‖ < 1`,
`(1 + x²)(1 + x⁴)(1 + x⁶)… = 1 + x²/(1 - x²) + x⁶/((1 - x²)(1 - x⁴)) + x¹²/((1 - x²)(1 - x⁴)(1 - x⁶)) + …`
(the case `a = x` of (19.5.1); the exponents of the numerators are `m(m+1)`). -/
@[kb "hardywright2008" "Thm 346, p. 386"]
theorem tprod_one_add_pow_even_eq_tsum {x : ℂ} (hx : ‖x‖ < 1) :
    HasProd (fun k : ℕ ↦ 1 + x ^ (2 * k + 2))
      (∑' m : ℕ, x ^ (m * (m + 1)) / ∏ i ∈ range m, (1 - (x ^ 2) ^ (i + 1))) := by
  have h := hasProd_one_add_mul_pow_odd hx x
  convert h using 1
  · funext k; ring
  · refine tsum_congr fun m ↦ ?_
    have e : x ^ m * x ^ (m ^ 2) = x ^ (m * (m + 1)) := by
      rw [← pow_add]; congr 1; ring
    rw [← e]
    rfl

end NTKB.HardyWright
