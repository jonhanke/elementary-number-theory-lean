/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.ContinuedFractions.Infinite
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational

/-!
# Approximation by convergents (Hardy–Wright, § 10.15 and §§ 11.8, 11.9)

Throughout, `x = [a₀, a₁, …]` is the value of an infinite simple continued fraction (so `x` is
irrational, Theorem 170), with convergents `pₙ/qₙ`.

* Theorem 182: if `n ≥ 1`, `0 < q ≤ qₙ` and `p/q ≠ pₙ/qₙ`, then `|pₙ - qₙ x| < |p - qx|`.
* Theorem 181: under the same hypotheses `|pₙ/qₙ - x| < |p/q - x|`.
* Theorem 183: of two consecutive convergents, one at least satisfies `|p/q - x| < 1/(2q²)`.
* Theorem 194: `√5` in Hurwitz's theorem (Theorem 193, Mathlib's
  `Real.infinite_rat_abs_sub_lt_one_div_sqrt_five_mul_den_sq_of_irrational`) is best possible: for
  `ξ = (√5 - 1)/2` and `A > √5`, `|ξ - p/q| < 1/(A q²)` has only finitely many solutions.
* Theorem 195: of any three consecutive convergents, one at least satisfies `|p/q - x| < 1/(√5 q²)`.

Hardy–Wright state Theorems 181 to 183 also for finite continued fractions (rational `x`); here only the
irrational case is formalized. Theorems 181 and 182 are proved for `n ≥ 1` (Hardy–Wright assume `n > 1`
to avoid a complication that only occurs for rational `x`).
-/

namespace NTKB.HardyWright

open GenContFract Filter Topology

variable {a : ℕ → ℤ} {x : ℝ}

/-- The sign of the error: `qₙ x - pₙ = (-1)ⁿ/D` with `D > 0`. -/
lemma sign_err (ha : ∀ i, 1 ≤ i → 0 < a i)
    (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 x)) (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧
      (cf (fun i ↦ (a i : ℝ))).dens n * x - (cf (fun i ↦ (a i : ℝ))).nums n = (-1) ^ n / D := by
  obtain ⟨D, hD1, -, -, e2⟩ := cf_sub_convs_eq ha hx n
  have := cf_dens_pos (pos_fin ha (n + 1)) (n + 1) le_rfl
  exact ⟨D, by linarith, e2⟩

/-- **Theorem 182.** If `n ≥ 1`, `0 < q ≤ qₙ` and `p/q ≠ pₙ/qₙ`, then `|pₙ - qₙ x| < |p - q x|`:
the convergents are best approximations of the second kind. -/
@[kb "hardywright2008" "Thm 182, p. 194"]
theorem abs_nums_sub_lt (ha : ∀ i, 1 ≤ i → 0 < a i)
    (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 x)) {n : ℕ} (hn : 1 ≤ n)
    {p q : ℤ} (hq : 0 < q) (hqn : (q : ℝ) ≤ (cf (fun i ↦ (a i : ℝ))).dens n)
    (hne : (p : ℝ) / q ≠ (cf (fun i ↦ (a i : ℝ))).convs n) :
    |(cf (fun i ↦ (a i : ℝ))).nums n - (cf (fun i ↦ (a i : ℝ))).dens n * x| < |p - q * x| := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨P1, Q1, hP1, hQ1⟩ := cf_nums_dens_int a (m + 1)
  obtain ⟨P0, Q0, hP0, hQ0⟩ := cf_nums_dens_int a m
  have hdet := cf_nums_mul_dens_sub (fun i ↦ (a i : ℝ)) m
  rw [hP1, hQ1, hP0, hQ0] at hdet
  have hdetZ : P1 * Q0 - P0 * Q1 = (-1) ^ m := by exact_mod_cast hdet
  have hp := pos_fin ha (m + 1)
  have hQ1pos : (0 : ℝ) < Q1 := by rw [← hQ1]; exact cf_dens_pos hp (m + 1) le_rfl
  have hQ0pos : (1 : ℝ) ≤ Q0 := by rw [← hQ0]; exact cf_dens_one_le (pos_finZ ha (m + 1)) m (by omega)
  rw [hQ1] at hqn
  rw [hP1, hQ1]
  rw [cf_convs, hP1, hQ1] at hne
  -- the errors `e₁ = p_{m+1} - q_{m+1} x`, `e₀ = p_m - q_m x` have opposite signs, `|e₁| < |e₀|`
  obtain ⟨D1, hD1, e1⟩ := sign_err ha hx (m + 1)
  obtain ⟨D0, hD0, e0⟩ := sign_err ha hx m
  rw [hP1, hQ1] at e1
  rw [hP0, hQ0] at e0
  have hdec := (cf_abs_sub_convs_bounds ha hx m).2.2.2.1
  rw [hP1, hQ1, hP0, hQ0] at hdec
  have hopp : ((P1 : ℝ) - Q1 * x) * (P0 - Q0 * x) < 0 := by
    have : ((P1 : ℝ) - Q1 * x) * (P0 - Q0 * x) = -1 / (D1 * D0) := by
      rw [show (P1 : ℝ) - Q1 * x = -(Q1 * x - P1) by ring, show (P0 : ℝ) - Q0 * x = -(Q0 * x - P0) by ring,
        e1, e0, neg_mul_neg, div_mul_div_comm, ← pow_add, show m + 1 + m = 2 * m + 1 by ring, pow_succ,
        pow_mul]
      simp
    rw [this]
    exact div_neg_of_neg_of_pos (by norm_num) (mul_pos hD1 hD0)
  have habs1 : |(P1 : ℝ) - Q1 * x| = |(Q1 : ℝ) * x - P1| := abs_sub_comm _ _
  have habs0 : |(P0 : ℝ) - Q0 * x| = |(Q0 : ℝ) * x - P0| := abs_sub_comm _ _
  -- `(p, q) = μ (p_{m+1}, q_{m+1}) + ν (p_m, q_m)`
  set ε : ℤ := (-1) ^ m with hε
  have hε2 : ε * ε = 1 := by rw [hε, ← mul_pow]; simp
  set μ : ℤ := ε * (p * Q0 - q * P0) with hμ
  set ν : ℤ := ε * (q * P1 - p * Q1) with hν
  have hpμν : p = μ * P1 + ν * P0 := by
    simp only [hμ, hν]; linear_combination (-p) * hε2 + (-(ε * p)) * hdetZ
  have hqμν : q = μ * Q1 + ν * Q0 := by
    simp only [hμ, hν]; linear_combination (-q) * hε2 + (-(ε * q)) * hdetZ
  have hpq : (p : ℝ) - q * x = μ * (P1 - Q1 * x) + ν * (P0 - Q0 * x) := by
    rw [hpμν, hqμν]; push_cast; ring
  have hQ0Z : 1 ≤ Q0 := by exact_mod_cast hQ0pos
  have hqnZ : q ≤ Q1 := by exact_mod_cast hqn
  by_cases hν0 : ν = 0
  · exfalso; apply hne
    rw [hν0, zero_mul, add_zero] at hpμν hqμν
    rw [hpμν, hqμν]; push_cast
    have hμ0 : (μ : ℝ) ≠ 0 := by
      intro h; have : μ = 0 := by exact_mod_cast h
      rw [this] at hqμν; omega
    field_simp
  by_cases hμ0 : μ = 0
  · rw [hpq, hμ0]
    simp only [Int.cast_zero, zero_mul, zero_add, abs_mul]
    have : (1 : ℝ) ≤ |(ν : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hν0
    rw [habs1, habs0] at *
    nlinarith [abs_nonneg ((Q0 : ℝ) * x - P0)]
  -- `μ` and `ν` have opposite signs
  have hμν : μ * ν < 0 := by
    rcases lt_or_gt_of_ne hμ0 with h1 | h1 <;> rcases lt_or_gt_of_ne hν0 with h2 | h2
    · exfalso; nlinarith
    · nlinarith
    · nlinarith
    · exfalso
      have : Q1 + Q0 ≤ q := by rw [hqμν]; nlinarith
      omega
  have hμνr : (μ : ℝ) * ν < 0 := by exact_mod_cast hμν
  have hsame : 0 ≤ (μ * ((P1 : ℝ) - Q1 * x)) * (ν * (P0 - Q0 * x)) := by
    have : (μ * ((P1 : ℝ) - Q1 * x)) * (ν * (P0 - Q0 * x)) =
        ((μ : ℝ) * ν) * (((P1 : ℝ) - Q1 * x) * (P0 - Q0 * x)) := by ring
    rw [this]; exact (mul_pos_of_neg_of_neg hμνr hopp).le
  have hsum : |(μ : ℝ) * (P1 - Q1 * x) + ν * (P0 - Q0 * x)| =
      |(μ : ℝ) * (P1 - Q1 * x)| + |(ν : ℝ) * (P0 - Q0 * x)| := by
    rw [abs_add_eq_add_abs_iff]
    rcases mul_nonneg_iff.mp hsame with h | h
    · left; exact h
    · right; exact h
  rw [hpq, hsum, abs_mul, abs_mul]
  have hν1 : (1 : ℝ) ≤ |(ν : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hν0
  rw [habs1, habs0]
  nlinarith [abs_nonneg (μ : ℝ), abs_nonneg ((Q1 : ℝ) * x - P1), abs_nonneg ((Q0 : ℝ) * x - P0)]

/-- **Theorem 181.** If `n ≥ 1`, `0 < q ≤ qₙ` and `p/q ≠ pₙ/qₙ`, then `|pₙ/qₙ - x| < |p/q - x|`. -/
@[kb "hardywright2008" "Thm 181, p. 194"]
theorem abs_convs_sub_lt (ha : ∀ i, 1 ≤ i → 0 < a i)
    (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 x)) {n : ℕ} (hn : 1 ≤ n)
    {p q : ℤ} (hq : 0 < q) (hqn : (q : ℝ) ≤ (cf (fun i ↦ (a i : ℝ))).dens n)
    (hne : (p : ℝ) / q ≠ (cf (fun i ↦ (a i : ℝ))).convs n) :
    |(cf (fun i ↦ (a i : ℝ))).convs n - x| < |(p : ℝ) / q - x| := by
  have h := abs_nums_sub_lt ha hx hn hq hqn hne
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hd := cf_dens_pos (pos_fin ha n) n le_rfl
  rw [cf_convs]
  have e1 : (cf (fun i ↦ (a i : ℝ))).nums n / (cf (fun i ↦ (a i : ℝ))).dens n - x =
      ((cf (fun i ↦ (a i : ℝ))).nums n - (cf (fun i ↦ (a i : ℝ))).dens n * x) /
        (cf (fun i ↦ (a i : ℝ))).dens n := by field_simp
  have e2 : (p : ℝ) / q - x = (p - q * x) / q := by field_simp
  rw [e1, e2, abs_div, abs_div, abs_of_pos hd, abs_of_pos hqr]
  calc _ ≤ |(cf (fun i ↦ (a i : ℝ))).nums n - (cf (fun i ↦ (a i : ℝ))).dens n * x| / q :=
        div_le_div_of_nonneg_left (abs_nonneg _) hqr hqn
    _ < _ := div_lt_div_of_pos_right h hqr

/-- **Theorem 183** (Vahlen). Of any two consecutive convergents to `x`, one at least satisfies
`|p/q - x| < 1/(2q²)`. -/
@[kb "hardywright2008" "Thm 183, p. 196"]
theorem abs_convs_sub_lt_or (ha : ∀ i, 1 ≤ i → 0 < a i)
    (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 x)) (n : ℕ) :
    |(cf (fun i ↦ (a i : ℝ))).convs n - x| < 1 / (2 * (cf (fun i ↦ (a i : ℝ))).dens n ^ 2) ∨
      |(cf (fun i ↦ (a i : ℝ))).convs (n + 1) - x| <
        1 / (2 * (cf (fun i ↦ (a i : ℝ))).dens (n + 1) ^ 2) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hp := pos_fin ha (n + 1)
  have hq0 := cf_dens_pos hp n (by omega)
  have hq1 := cf_dens_pos hp (n + 1) le_rfl
  set q0 := (cf (fun i ↦ (a i : ℝ))).dens n
  set q1 := (cf (fun i ↦ (a i : ℝ))).dens (n + 1)
  -- `|x - xₙ| + |x - x_{n+1}| = 1/(qₙ q_{n+1})`
  obtain ⟨D0, hD0, -, e0, -⟩ := cf_sub_convs_eq ha hx n
  obtain ⟨D1, hD1, -, e1, -⟩ := cf_sub_convs_eq ha hx (n + 1)
  have hD0' : 0 < D0 := by linarith
  have hD1' : 0 < D1 := by
    have := cf_dens_pos (pos_fin ha (n + 2)) (n + 2) le_rfl; linarith
  have hsum : |(cf (fun i ↦ (a i : ℝ))).convs n - x| +
      |(cf (fun i ↦ (a i : ℝ))).convs (n + 1) - x| = 1 / (q0 * q1) := by
    rw [← abs_convs_succ_sub ha n, abs_sub_comm _ x, abs_sub_comm _ x,
      show (cf (fun i ↦ (a i : ℝ))).convs (n + 1) - (cf (fun i ↦ (a i : ℝ))).convs n =
        (x - (cf (fun i ↦ (a i : ℝ))).convs n) - (x - (cf (fun i ↦ (a i : ℝ))).convs (n + 1)) by ring,
      e0, e1, pow_succ]
    have hA : 0 < 1 / (q0 * D0) := by positivity
    have hB : 0 < 1 / (q1 * D1) := by positivity
    rcases neg_one_pow_eq_or ℝ n with h | h <;> rw [h]
    · rw [show (1 : ℝ) / (q0 * D0) - 1 * -1 / (q1 * D1) = 1 / (q0 * D0) + 1 / (q1 * D1) by ring,
        show (1 : ℝ) * -1 / (q1 * D1) = -(1 / (q1 * D1)) by ring, abs_neg, abs_of_pos hA,
        abs_of_pos hB, abs_of_pos (by positivity)]
    · rw [show (-1 : ℝ) / (q0 * D0) - -1 * -1 / (q1 * D1) = -(1 / (q0 * D0) + 1 / (q1 * D1)) by ring,
        show (-1 : ℝ) * -1 / (q1 * D1) = 1 / (q1 * D1) by ring,
        show (-1 : ℝ) / (q0 * D0) = -(1 / (q0 * D0)) by ring, abs_neg, abs_neg, abs_of_pos hA,
        abs_of_pos hB, abs_of_pos (by positivity)]
  -- hence `(q_{n+1} - qₙ)² ≤ 0`
  have hle : 1 / (2 * q0 ^ 2) + 1 / (2 * q1 ^ 2) ≤ 1 / (q0 * q1) := by linarith
  have heq : q1 = q0 := by
    have : (q1 - q0) ^ 2 ≤ 0 := by
      have h' : (q1 ^ 2 + q0 ^ 2) / (2 * q0 ^ 2 * q1 ^ 2) ≤ 2 * q0 * q1 / (2 * q0 ^ 2 * q1 ^ 2) := by
        have e1 : 1 / (2 * q0 ^ 2) + 1 / (2 * q1 ^ 2) = (q1 ^ 2 + q0 ^ 2) / (2 * q0 ^ 2 * q1 ^ 2) := by
          field_simp
        have e2 : 1 / (q0 * q1) = 2 * q0 * q1 / (2 * q0 ^ 2 * q1 ^ 2) := by field_simp
        rw [← e1, ← e2]; exact hle
      rw [div_le_div_iff_of_pos_right (by positivity)] at h'
      nlinarith
    nlinarith [sq_nonneg (q1 - q0)]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `n = 0`, `q₁ = a₁ = 1`, `x₁ = a₀ + 1` and `x > a₀ + 1/2`
    have ha1 : (a 1 : ℝ) = 1 := by
      have : q1 = a 1 := by simp [q1]
      rw [← this, heq]; simp [q0]
    have hx1 : (cf (fun i ↦ (a i : ℝ))).convs 1 = a 0 + 1 := by
      rw [cf_convs]; simp only [cf_nums_one, cf_dens_one, ha1]; ring
    have ht := cf_tendsto_tail ha hx
    obtain ⟨-, hlt⟩ := cf_value_mem_Ioo (fun i hi ↦ ha (i + 1) (by omega)) ht
    have hx0 := (cf_value_mem_Ioo ha hx).1
    have hx01 := (cf_value_mem_Ioo ha hx).2
    simp only [zero_add] at hlt
    rw [ha1] at hlt
    have hxa : 1 / 2 < x - a 0 := by
      have hpos : 0 < x - a 0 := by linarith
      rw [div_lt_iff₀ hpos] at hlt
      linarith
    rw [hx1, show q1 = 1 by rw [heq]; simp [q0]] at h2
    rw [abs_of_pos (by linarith)] at h2
    norm_num at h2
    linarith
  · have h' := (cf_dens_le_dens_succ (pos_finZ ha (n + 1)) (n := n) le_rfl).2 hn
    have : q0 < q1 := h'
    rw [heq] at this
    exact lt_irrefl _ this

/-- **Theorem 194.** In Hurwitz's theorem (Theorem 193) the number `√5` is best possible: for
`ξ = (√5 - 1)/2` and any `A > √5`, the inequality `|ξ - p/q| < 1/(A q²)` has only a finite number of
solutions `(p, q)` with `q > 0`. -/
@[kb "hardywright2008" "Thm 194, p. 210"]
theorem finite_abs_sub_lt_of_sqrt_five_lt {A : ℝ} (hA : √5 < A) :
    {pq : ℤ × ℤ | 0 < pq.2 ∧ |(√5 - 1) / 2 - pq.1 / pq.2| < 1 / (A * pq.2 ^ 2)}.Finite := by
  set s := √(5 : ℝ) with hs
  have hs2 : s ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by norm_num)
  have hs1 : s < 3 := by nlinarith
  have hA0 : 0 < A := hs0.trans hA
  have hirr : Irrational s := by
    have := Nat.Prime.irrational_sqrt Nat.prime_five
    simpa using this
  set K : ℝ := 1 / (A * (A - s)) with hK
  obtain ⟨M, hM⟩ := exists_nat_gt K
  refine (((Set.finite_Icc (-(M : ℤ) - 1) (M + 1)).prod (Set.finite_Icc (1 : ℤ) M))).subset ?_
  rintro ⟨p, q⟩ ⟨hq, hpq⟩
  simp only at hq hpq
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  -- `e = p - q ξ`, `|e| < 1/(A q)`
  set e : ℝ := p - q * ((s - 1) / 2) with he
  have he1 : |e| < 1 / (A * q) := by
    have : (s - 1) / 2 - p / q = -(e / q) := by simp only [he]; field_simp; ring
    rw [this, abs_neg, abs_div, abs_of_pos hqr, div_lt_iff₀ hqr] at hpq
    calc |e| < 1 / (A * q ^ 2) * q := hpq
      _ = 1 / (A * q) := by field_simp
  -- `N = p² + pq - q² = (p - qξ)(p - qξ')` is a nonzero integer
  have hN : ((p ^ 2 + p * q - q ^ 2 : ℤ) : ℝ) = e * (e + q * s) := by
    simp only [he]; push_cast; linear_combination ((q : ℝ) ^ 2 / 4) * hs2
  have hN0 : p ^ 2 + p * q - q ^ 2 ≠ 0 := by
    intro h0
    apply hirr
    refine ⟨((2 * p + q : ℤ) : ℚ) / q, ?_⟩
    have h0' : ((p ^ 2 + p * q - q ^ 2 : ℤ) : ℝ) = 0 := by exact_mod_cast h0
    rw [hN] at h0'
    push_cast
    rcases mul_eq_zero.mp h0' with h | h
    · simp only [he] at h
      field_simp
      linarith
    · -- `e + q s = 0` is impossible: then `2p + q = -q s` ... both signs give `(2p+q)² = 5q²`
      exfalso
      simp only [he] at h
      have : (2 * p + q : ℝ) = -(q * s) := by linarith
      have h5 : ((2 * p + q : ℤ) : ℝ) ^ 2 = 5 * (q : ℝ) ^ 2 := by
        push_cast; rw [this]; nlinarith
      have hrat : s = -(2 * p + q) / q := by field_simp; linarith
      exact hirr ⟨-(2 * p + q) / q, by rw [hrat]; push_cast; ring⟩
  have hN1 : (1 : ℝ) ≤ |e * (e + q * s)| := by
    rw [← hN, ← Int.cast_abs]; exact_mod_cast Int.one_le_abs hN0
  -- `1 ≤ |e| (|e| + q s) < 1/(A² q²) + s/A`, so `q² < K`
  have hbound : (1 : ℝ) < 1 / (A * q) * (1 / (A * q) + q * s) := by
    calc (1 : ℝ) ≤ |e| * (|e| + q * s) := by
          rw [abs_mul] at hN1
          refine hN1.trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
          calc |e + q * s| ≤ |e| + |q * s| := abs_add_le _ _
            _ = |e| + q * s := by rw [abs_of_pos (mul_pos hqr hs0)]
      _ < 1 / (A * q) * (1 / (A * q) + q * s) := by
          have h0 := abs_nonneg e
          have hpos : 0 < 1 / (A * q) := by positivity
          have := mul_pos (sub_pos.mpr he1) (show 0 < 1 / (A * q) + |e| + q * s by
            have := mul_pos hqr hs0; linarith)
          nlinarith
  have hqK : (q : ℝ) ^ 2 < K := by
    rw [hK, lt_div_iff₀ (by nlinarith)]
    have e1 : 1 / (A * q) * (1 / (A * q) + q * s) = 1 / (A ^ 2 * q ^ 2) + s / A := by
      field_simp
    rw [e1] at hbound
    have : A * (A - s) * q ^ 2 < 1 := by
      have h1 : 1 - s / A < 1 / (A ^ 2 * q ^ 2) := by linarith
      rw [show 1 - s / A = (A - s) / A by field_simp, div_lt_div_iff₀ hA0 (by positivity)] at h1
      nlinarith
    linarith
  have hqM : q ≤ M := by
    have : (q : ℝ) < M := by nlinarith
    exact_mod_cast this.le
  have hpM : |(p : ℝ)| ≤ M + 1 := by
    have h1 : |e| < 1 := by
      calc |e| < 1 / (A * q) := he1
        _ ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
    have h2 : |q * ((s - 1) / 2)| ≤ q := by
      rw [abs_of_pos (by nlinarith)]; nlinarith
    have : (p : ℝ) = e + q * ((s - 1) / 2) := by simp only [he]; ring
    rw [this]
    calc |e + q * ((s - 1) / 2)| ≤ |e| + |q * ((s - 1) / 2)| := abs_add_le _ _
      _ ≤ 1 + q := by linarith
      _ ≤ M + 1 := by have : (q : ℝ) ≤ M := by exact_mod_cast hqM
                      linarith
  have hpM' : |p| ≤ M + 1 := by
    have : ((|p| : ℤ) : ℝ) ≤ ((M + 1 : ℤ) : ℝ) := by push_cast; exact hpM
    exact_mod_cast this
  simp only [Set.mem_prod, Set.mem_Icc]
  exact ⟨⟨by linarith [neg_abs_le p], by linarith [le_abs_self p]⟩, ⟨hq, hqM⟩⟩

/-- The error formula `|x - xₖ| = 1/(qₖ² (a'_{k+1} + q_{k-1}/qₖ))` (Hardy–Wright (11.9.1)), with
`q_{k-1} = (contsAux k).b`. -/
lemma abs_sub_convs_eq (ha : ∀ i, 1 ≤ i → 0 < a i)
    (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 x)) (k : ℕ) {y : ℝ}
    (hy : Tendsto (fun t ↦ (cf (fun i ↦ ((a (k + 1 + i) : ℤ) : ℝ))).convs t) atTop (𝓝 y)) :
    |(cf (fun i ↦ (a i : ℝ))).convs k - x| =
      1 / ((cf (fun i ↦ (a i : ℝ))).dens k ^ 2 *
        (y + ((cf (fun i ↦ (a i : ℝ))).contsAux k).b / (cf (fun i ↦ (a i : ℝ))).dens k)) := by
  have e := cf_value_eq_completeQuotient ha hx k hy
  have hdet := cf_contsAux_det (fun i ↦ (a i : ℝ)) k
  have hP : (cf (fun i ↦ (a i : ℝ))).nums k = ((cf (fun i ↦ (a i : ℝ))).contsAux (k + 1)).a := by
    rw [num_eq_conts_a, nth_cont_eq_succ_nth_contAux]
  have hQ : (cf (fun i ↦ (a i : ℝ))).dens k = ((cf (fun i ↦ (a i : ℝ))).contsAux (k + 1)).b := by
    rw [den_eq_conts_b, nth_cont_eq_succ_nth_contAux]
  have hQpos := cf_dens_pos (pos_fin ha k) k le_rfl
  have hR : 0 ≤ ((cf (fun i ↦ (a i : ℝ))).contsAux k).b := by
    rcases k with _ | k
    · simp [zeroth_contAux_eq_one_zero]
    · have := cf_dens_pos (pos_fin ha k) k le_rfl
      rw [den_eq_conts_b, nth_cont_eq_succ_nth_contAux] at this; exact this.le
  have hy1 : 0 < y := by
    have := (cf_value_mem_Ioo (fun i hi ↦ ha (k + 1 + i) (by omega)) hy).1
    have h : (0 : ℝ) < a (k + 1 + 0) := by exact_mod_cast ha (k + 1 + 0) (by omega)
    linarith
  rw [cf_convs, hP] at *
  rw [hQ] at hQpos ⊢
  set P := ((cf (fun i ↦ (a i : ℝ))).contsAux (k + 1)).a
  set Q := ((cf (fun i ↦ (a i : ℝ))).contsAux (k + 1)).b
  set P' := ((cf (fun i ↦ (a i : ℝ))).contsAux k).a
  set Q' := ((cf (fun i ↦ (a i : ℝ))).contsAux k).b
  have hW : 0 < y * Q + Q' := by nlinarith
  have hdiff : P / Q - x = -((-1) ^ k / (Q * (y * Q + Q'))) := by
    rw [e]; field_simp; linear_combination (-1 : ℝ) * hdet
  rw [hdiff, abs_neg, abs_div, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_pos (mul_pos hQpos hW)]
  congr 1
  field_simp

/-- If `A + B ≤ √5` and `1/A + 1/B ≤ √5` with `A > 0`, `0 < B ≤ 1`, then `B ≥ (√5 - 1)/2`. -/
lemma sqrt_five_aux {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (hB1 : B ≤ 1) (h1 : A + B ≤ √5)
    (h2 : 1 / A + 1 / B ≤ √5) : (√5 - 1) / 2 ≤ B := by
  have hs2 : √(5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < √(5 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs3 : 2 < √(5 : ℝ) := by nlinarith
  -- `1 = A · (1/A) ≤ (√5 - B)(√5 - 1/B)`
  have hiA : 0 < 1 / A := by positivity
  have hiB : 0 < 1 / B := by positivity
  have hprod : A * (1 / A) ≤ (√5 - B) * (√5 - 1 / B) :=
    mul_le_mul (by linarith) (by linarith) hiA.le (by linarith)
  rw [mul_one_div_cancel hA.ne'] at hprod
  have hBB : B * (1 / B) = 1 := mul_one_div_cancel hB.ne'
  -- so `B + 1/B ≤ √5`, i.e. `B² - √5 B + 1 ≤ 0`
  have h3 : B + 1 / B ≤ √5 := by nlinarith
  have h4 : B ^ 2 - √5 * B + 1 ≤ 0 := by nlinarith
  nlinarith

/-- **Theorem 195.** Of any three consecutive convergents to `x`, one at least satisfies
`|p/q - x| < 1/(√5 q²)`. -/
@[kb "hardywright2008" "Thm 195, p. 210"]
theorem abs_convs_sub_lt_sqrt_five (ha : ∀ i, 1 ≤ i → 0 < a i)
    (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 x)) (n : ℕ) :
    |(cf (fun i ↦ (a i : ℝ))).convs n - x| < 1 / (√5 * (cf (fun i ↦ (a i : ℝ))).dens n ^ 2) ∨
      |(cf (fun i ↦ (a i : ℝ))).convs (n + 1) - x| <
        1 / (√5 * (cf (fun i ↦ (a i : ℝ))).dens (n + 1) ^ 2) ∨
      |(cf (fun i ↦ (a i : ℝ))).convs (n + 2) - x| <
        1 / (√5 * (cf (fun i ↦ (a i : ℝ))).dens (n + 2) ^ 2) := by
  -- the complete quotients `α k = a'_k`
  choose α hα using fun k ↦ cf_convs_tendsto (fun i (hi : 1 ≤ i) ↦ ha (k + i) (by omega))
  set Q : ℕ → ℝ := fun k ↦ (cf (fun i ↦ (a i : ℝ))).dens k with hQdef
  set R : ℕ → ℝ := fun k ↦ ((cf (fun i ↦ (a i : ℝ))).contsAux k).b with hRdef
  have hQpos : ∀ k, 0 < Q k := fun k ↦ cf_dens_pos (pos_fin ha k) k le_rfl
  have hRQ : ∀ k, R (k + 1) = Q k := fun k ↦ by
    simp only [hRdef, hQdef, den_eq_conts_b, nth_cont_eq_succ_nth_contAux]
  have hrec : ∀ k, Q (k + 1) = a (k + 1) * Q k + R k := by
    intro k
    simp only [hQdef, hRdef, den_eq_conts_b, nth_cont_eq_succ_nth_contAux]
    rw [cf_contsAux_add_two]
  have hmono : ∀ k, Q k ≤ Q (k + 1) := fun k ↦
    (cf_dens_le_dens_succ (pos_finZ ha (k + 1)) (n := k) le_rfl).1
  -- `α (k+1) = a_{k+1} + 1/α (k+2)`
  have hαrec : ∀ k, α (k + 1) = a (k + 1) + 1 / α (k + 2) := by
    intro k
    have ht := cf_tendsto_tail (fun i hi ↦ ha (k + 1 + i) (by omega)) (hα (k + 1))
    have e : (fun i ↦ ((a (k + 1 + (i + 1)) : ℤ) : ℝ)) = fun i ↦ ((a (k + 2 + i) : ℤ) : ℝ) := by
      funext i; rw [show k + 1 + (i + 1) = k + 2 + i by ring]
    rw [e] at ht
    have h := tendsto_nhds_unique (hα (k + 2)) ht
    have hpos : 0 < α (k + 1) - a (k + 1 + 0) := by
      have := (cf_value_mem_Ioo (fun i hi ↦ ha (k + 1 + i) (by omega)) (hα (k + 1))).1
      simp only [add_zero] at this ⊢; linarith
    rw [h]; simp only [add_zero] at hpos ⊢; field_simp
    ring
  have hα1 : ∀ k, 1 < α (k + 1) := by
    intro k
    have := (cf_value_mem_Ioo (fun i hi ↦ ha (k + 1 + i) (by omega)) (hα (k + 1))).1
    have h : (1 : ℝ) ≤ a (k + 1 + 0) := by exact_mod_cast ha (k + 1 + 0) (by omega)
    linarith
  -- the error in terms of `s k = α (k+1) + R k / Q k`
  have herr : ∀ k, |(cf (fun i ↦ (a i : ℝ))).convs k - x| = 1 / (Q k ^ 2 * (α (k + 1) + R k / Q k)) :=
    fun k ↦ abs_sub_convs_eq ha hx k (hα (k + 1))
  have hRnn : ∀ k, 0 ≤ R k := by
    intro k; rcases k with _ | k
    · simp [hRdef, zeroth_contAux_eq_one_zero]
    · rw [hRQ]; exact (hQpos k).le
  have hfail : ∀ k, ¬(|(cf (fun i ↦ (a i : ℝ))).convs k - x| < 1 / (√5 * Q k ^ 2)) →
      α (k + 1) + R k / Q k ≤ √5 := by
    intro k hk
    push Not at hk
    rw [herr k] at hk
    have hs : 0 < α (k + 1) + R k / Q k := by
      have := hα1 k; have := div_nonneg (hRnn k) (hQpos k).le; linarith
    have hq2 := pow_pos (hQpos k) 2
    rw [div_le_div_iff₀ (by positivity) (by positivity)] at hk
    nlinarith
  -- two consecutive failures give `q_k/q_{k+1} > (√5 - 1)/2`
  have htwo : ∀ k, α (k + 1) + R k / Q k ≤ √5 → α (k + 2) + R (k + 1) / Q (k + 1) ≤ √5 →
      (√5 - 1) / 2 < Q k / Q (k + 1) := by
    intro k h1 h2
    rw [hRQ] at h2
    have hA := hα1 (k + 1)
    have hB : 0 < Q k / Q (k + 1) := div_pos (hQpos k) (hQpos (k + 1))
    have hB1 : Q k / Q (k + 1) ≤ 1 := (div_le_one (hQpos (k + 1))).mpr (hmono k)
    -- `α (k+1) + R k/Q k = 1/α (k+2) + Q (k+1)/Q k`
    have e : α (k + 1) + R k / Q k = 1 / α (k + 2) + 1 / (Q k / Q (k + 1)) := by
      rw [hαrec k, one_div_div, hrec k]
      have := (hQpos k).ne'
      have := (show 0 < α (k + 2) by linarith).ne'
      field_simp
      ring
    rw [e] at h1
    have hle := sqrt_five_aux (by linarith) hB hB1 h2 h1
    refine lt_of_le_of_ne hle ?_
    -- `q_k/q_{k+1}` is rational, `(√5 - 1)/2` is not
    intro heq
    obtain ⟨u, v, hu, hv⟩ := cf_nums_dens_int a k
    obtain ⟨u', v', hu', hv'⟩ := cf_nums_dens_int a (k + 1)
    have hirr := Nat.Prime.irrational_sqrt Nat.prime_five
    apply hirr
    refine ⟨2 * v / v' + 1, ?_⟩
    have hv'0 : (v' : ℝ) ≠ 0 := by rw [← hv']; exact (hQpos (k + 1)).ne'
    have hQk : Q k = v := hv
    have hQk1 : Q (k + 1) = v' := hv'
    rw [hQk, hQk1] at heq
    push_cast
    rw [mul_div_assoc, ← heq]; ring
  by_contra hcon
  push Not at hcon
  obtain ⟨h0, h1, h2⟩ := hcon
  have f0 := hfail n (not_lt.mpr h0)
  have f1 := hfail (n + 1) (not_lt.mpr h1)
  have f2 := hfail (n + 2) (not_lt.mpr h2)
  have b1 := htwo n f0 f1
  have b2 := htwo (n + 1) f1 f2
  -- `a_{n+2} = q_{n+2}/q_{n+1} - q_n/q_{n+1} < (√5 + 1)/2 - (√5 - 1)/2 = 1`
  have hs2 : √(5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs3 : 2 < √(5 : ℝ) := by nlinarith [Real.sqrt_nonneg (5 : ℝ)]
  have hc : 0 < (√5 - 1) / 2 := by linarith
  have hkey : (a (n + 2) : ℝ) = 1 / (Q (n + 1) / Q (n + 2)) - Q n / Q (n + 1) := by
    rw [one_div_div, hrec (n + 1), hRQ]
    field_simp [(hQpos (n + 1)).ne']
    ring
  have hinv : 1 / (Q (n + 1) / Q (n + 2)) < (√5 + 1) / 2 := by
    rw [div_lt_iff₀ (div_pos (hQpos (n + 1)) (hQpos (n + 2)))]
    nlinarith
  have ha2 : (1 : ℝ) ≤ a (n + 2) := by exact_mod_cast ha (n + 2) (by omega)
  linarith

end NTKB.HardyWright
