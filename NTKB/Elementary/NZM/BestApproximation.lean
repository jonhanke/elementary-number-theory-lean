/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.ContinuedFractions.Approximation

/-!
# Continued fractions with a real last term; best approximations
(Niven–Zuckerman–Montgomery, §§ 7.3 and 7.5)

As elsewhere in `NTKB`, a continued fraction with quotients `a₀, a₁, …` is
`NTKB.HardyWright.cf a`, and the convergents `hₙ/kₙ` are its `nums`/`dens`.

* Theorem 7.3: the finite continued fraction `⟨a₀, …, a_m, x⟩` is `(x hₘ + hₘ₋₁)/(x kₘ + kₘ₋₁)`.
  The value of `⟨a₀, …, a_m, x⟩` is the `(m+1)`-st convergent of the continued fraction whose quotients
  are `a₀, …, a_m, x`. The pairs `(hₘ, kₘ)`, `(hₘ₋₁, kₘ₋₁)` are `contsAux (m + 1)`, `contsAux m`
  (with `h₋₁ = 1`, `k₋₁ = 0`), so the book's index is shifted by one (`n = m + 1`); the case `n = 0`
  of the book is the trivial `⟨x⟩ = x`.
* Theorem 7.13: if `0 < b` and `|ξ b - a| < |ξ kₙ - hₙ|` then `b ≥ kₙ₊₁`; if moreover
  `kₙ < kₙ₊₁` (automatic for `n ≥ 1`) and `|ξ - a/b| < |ξ - hₙ/kₙ|` then `b > kₙ`.
-/

namespace NTKB.NZM

open NTKB.HardyWright GenContFract Filter Topology

/-- **Theorem 7.3.** `⟨a₀, …, a_m, x⟩ = (x hₘ + hₘ₋₁)/(x kₘ + kₘ₋₁)` for every real `x`
(the book assumes `x > 0`, which is not needed for the identity). -/
@[kb "nivenzuckermanmontgomery" "Thm 7.3, p. 329"]
theorem finite_cf_value (a : ℕ → ℝ) (m : ℕ) (x : ℝ) :
    (cf (fun i ↦ if i ≤ m then a i else x)).convs (m + 1) =
      (x * ((cf a).contsAux (m + 1)).a + ((cf a).contsAux m).a) /
        (x * ((cf a).contsAux (m + 1)).b + ((cf a).contsAux m).b) := by
  set b : ℕ → ℝ := fun i ↦ if i ≤ m then a i else x with hb
  have hc : ∀ k ≤ m + 1, (cf b).contsAux k = (cf a).contsAux k :=
    cf_contsAux_congr (fun i hi ↦ by simp [hb, show i ≤ m by omega])
  have hbx : b (m + 1) = x := by simp [hb]
  rw [cf_convs, num_eq_conts_a, den_eq_conts_b, nth_cont_eq_succ_nth_contAux,
    show (cf b).contsAux (m + 1 + 1) = _ from cf_contsAux_add_two b m, hbx, hc (m + 1) le_rfl,
    hc m (by omega)]

variable {a : ℕ → ℤ} {ξ : ℝ}

/-- The core of Theorem 7.13: the best-approximation property of `hₙ/kₙ` for denominators `b < kₙ₊₁`,
stated as a contradiction. -/
private lemma best_aux (ha : ∀ i, 1 ≤ i → 0 < a i)
    (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 ξ)) (n : ℕ)
    {p q : ℤ} (hq : 0 < q)
    (hlt : (q : ℝ) < (cf (fun i ↦ (a i : ℝ))).dens (n + 1))
    (h : |(q : ℝ) * ξ - p| <
      |(cf (fun i ↦ (a i : ℝ))).dens n * ξ - (cf (fun i ↦ (a i : ℝ))).nums n|) : False := by
  obtain ⟨P1, Q1, hP1, hQ1⟩ := cf_nums_dens_int a (n + 1)
  obtain ⟨P0, Q0, hP0, hQ0⟩ := cf_nums_dens_int a n
  have hdet := cf_nums_mul_dens_sub (fun i ↦ (a i : ℝ)) n
  rw [hP1, hQ1, hP0, hQ0] at hdet
  have hdetZ : P1 * Q0 - P0 * Q1 = (-1) ^ n := by exact_mod_cast hdet
  have hp := pos_fin ha (n + 1)
  have hQ1pos : (0 : ℝ) < Q1 := by rw [← hQ1]; exact cf_dens_pos hp (n + 1) le_rfl
  have hQ0pos : (1 : ℝ) ≤ Q0 := by
    rw [← hQ0]; exact cf_dens_one_le (pos_finZ ha (n + 1)) n (by omega)
  rw [hQ1] at hlt
  rw [hQ0, hP0] at h
  obtain ⟨D1, hD1, e1⟩ := sign_err ha hx (n + 1)
  obtain ⟨D0, hD0, e0⟩ := sign_err ha hx n
  rw [hP1, hQ1] at e1
  rw [hP0, hQ0] at e0
  have hopp : ((Q1 : ℝ) * ξ - P1) * (Q0 * ξ - P0) < 0 := by
    have : ((Q1 : ℝ) * ξ - P1) * (Q0 * ξ - P0) = -1 / (D1 * D0) := by
      rw [e1, e0, div_mul_div_comm, ← pow_add, show n + 1 + n = 2 * n + 1 by ring, pow_succ,
        pow_mul]
      simp
    rw [this]
    exact div_neg_of_neg_of_pos (by norm_num) (mul_pos hD1 hD0)
  set ε : ℤ := (-1) ^ n with hε
  have hε2 : ε * ε = 1 := by rw [hε, ← mul_pow]; simp
  set μ : ℤ := ε * (p * Q0 - q * P0) with hμ
  set ν : ℤ := ε * (q * P1 - p * Q1) with hν
  have hpμν : p = μ * P1 + ν * P0 := by
    simp only [hμ, hν]; linear_combination (-p) * hε2 + (-(ε * p)) * hdetZ
  have hqμν : q = μ * Q1 + ν * Q0 := by
    simp only [hμ, hν]; linear_combination (-q) * hε2 + (-(ε * q)) * hdetZ
  have hpq : (q : ℝ) * ξ - p = μ * (Q1 * ξ - P1) + ν * (Q0 * ξ - P0) := by
    rw [hpμν, hqμν]; push_cast; ring
  have hQ0Z : 1 ≤ Q0 := by exact_mod_cast hQ0pos
  have hQ1Z : 0 < Q1 := by exact_mod_cast hQ1pos
  have hqZ : q < Q1 := by exact_mod_cast hlt
  have hν1 : ν ≠ 0 → (1 : ℝ) ≤ |(ν : ℝ)| := fun hν0 ↦ by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hν0
  by_cases hν0 : ν = 0
  · rw [hν0, zero_mul, add_zero] at hqμν
    have : 0 < μ := by
      by_contra hc; push Not at hc; nlinarith
    nlinarith
  by_cases hμ0 : μ = 0
  · rw [hpq, hμ0] at h
    simp only [Int.cast_zero, zero_mul, zero_add, abs_mul] at h
    nlinarith [abs_nonneg ((Q0 : ℝ) * ξ - P0), hν1 hν0]
  have hμν : μ * ν < 0 := by
    rcases lt_or_gt_of_ne hμ0 with h1 | h1 <;> rcases lt_or_gt_of_ne hν0 with h2 | h2
    · exfalso; nlinarith
    · nlinarith
    · nlinarith
    · exfalso
      have : Q1 + Q0 ≤ q := by rw [hqμν]; nlinarith
      omega
  have hμνr : (μ : ℝ) * ν < 0 := by exact_mod_cast hμν
  have hsame : 0 ≤ (μ * ((Q1 : ℝ) * ξ - P1)) * (ν * (Q0 * ξ - P0)) := by
    have : (μ * ((Q1 : ℝ) * ξ - P1)) * (ν * (Q0 * ξ - P0)) =
        ((μ : ℝ) * ν) * (((Q1 : ℝ) * ξ - P1) * (Q0 * ξ - P0)) := by ring
    rw [this]; exact (mul_pos_of_neg_of_neg hμνr hopp).le
  have hsum : |(μ : ℝ) * (Q1 * ξ - P1) + ν * (Q0 * ξ - P0)| =
      |(μ : ℝ) * (Q1 * ξ - P1)| + |(ν : ℝ) * (Q0 * ξ - P0)| := by
    rw [abs_add_eq_add_abs_iff]
    rcases mul_nonneg_iff.mp hsame with h | h
    · left; exact h
    · right; exact h
  rw [hpq, hsum, abs_mul, abs_mul] at h
  nlinarith [abs_nonneg (μ : ℝ), abs_nonneg ((Q1 : ℝ) * ξ - P1),
    abs_nonneg ((Q0 : ℝ) * ξ - P0), hν1 hν0]

/-- **Theorem 7.13** (second assertion). If `ξ` is the value of an infinite simple continued fraction
with convergents `hₙ/kₙ`, `b > 0`, and `|ξ b - a| < |ξ kₙ - hₙ|` for some `n ≥ 0`, then `kₙ₊₁ ≤ b`. -/
@[kb "nivenzuckermanmontgomery" "Thm 7.13, p. 338"]
theorem dens_succ_le_of_abs_lt (ha : ∀ i, 1 ≤ i → 0 < a i)
    (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 ξ)) (n : ℕ)
    {p q : ℤ} (hq : 0 < q)
    (h : |(q : ℝ) * ξ - p| <
      |(cf (fun i ↦ (a i : ℝ))).dens n * ξ - (cf (fun i ↦ (a i : ℝ))).nums n|) :
    (cf (fun i ↦ (a i : ℝ))).dens (n + 1) ≤ q := by
  by_contra hc
  exact best_aux ha hx n hq (not_le.mp hc) h

/-- **Theorem 7.13** (first assertion). Under the hypotheses above and `kₙ < kₙ₊₁` (which holds for
`n ≥ 1`, see `best_approximation_of_one_le`, and for `n = 0` when `a₁ > 1`), if
`|ξ - p/q| < |ξ - hₙ/kₙ|` with `q > 0` then `q > kₙ`. -/
theorem lt_of_abs_sub_lt (ha : ∀ i, 1 ≤ i → 0 < a i)
    (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 ξ)) (n : ℕ)
    (hk : (cf (fun i ↦ (a i : ℝ))).dens n < (cf (fun i ↦ (a i : ℝ))).dens (n + 1))
    {p q : ℤ} (hq : 0 < q)
    (h : |ξ - (p : ℝ) / q| < |ξ - (cf (fun i ↦ (a i : ℝ))).convs n|) :
    (cf (fun i ↦ (a i : ℝ))).dens n < q := by
  by_contra hc
  push Not at hc
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hk0 : 0 < (cf (fun i ↦ (a i : ℝ))).dens n := cf_dens_pos (pos_fin ha n) n le_rfl
  have h2 : |(q : ℝ) * ξ - p| <
      |(cf (fun i ↦ (a i : ℝ))).dens n * ξ - (cf (fun i ↦ (a i : ℝ))).nums n| := by
    have e1 : (q : ℝ) * ξ - p = q * (ξ - p / q) := by field_simp
    have e2 : (cf (fun i ↦ (a i : ℝ))).dens n * ξ - (cf (fun i ↦ (a i : ℝ))).nums n =
        (cf (fun i ↦ (a i : ℝ))).dens n * (ξ - (cf (fun i ↦ (a i : ℝ))).convs n) := by
      rw [cf_convs]; field_simp
    rw [e1, e2, abs_mul, abs_mul, abs_of_pos hqpos, abs_of_pos hk0]
    exact lt_of_lt_of_le (mul_lt_mul_of_pos_left h hqpos)
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (abs_nonneg _))
  have := dens_succ_le_of_abs_lt ha hx n hq h2
  linarith

/-- **Theorem 7.13** (first assertion, for `n ≥ 1`, as in the book): if `|ξ - p/q| < |ξ - hₙ/kₙ|`
with `q > 0` and `n ≥ 1`, then `q > kₙ`. -/
@[kb "nivenzuckermanmontgomery" "Thm 7.13, p. 338"]
theorem best_approximation_of_one_le (ha : ∀ i, 1 ≤ i → 0 < a i)
    (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 ξ)) {n : ℕ} (hn : 1 ≤ n)
    {p q : ℤ} (hq : 0 < q)
    (h : |ξ - (p : ℝ) / q| < |ξ - (cf (fun i ↦ (a i : ℝ))).convs n|) :
    (cf (fun i ↦ (a i : ℝ))).dens n < q :=
  lt_of_abs_sub_lt ha hx n ((cf_dens_le_dens_succ (pos_finZ ha (n + 1)) le_rfl).2 hn) hq h

end NTKB.NZM
