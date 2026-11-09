/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.ContinuedFractions.Periodic
import Mathlib.NumberTheory.Pell

/-!
# Pell's equation `x² - D y² = ±1` and the period of the continued fraction of `√D`

Hardy–Wright treat the equation `x² - m y² = 1` through the units of `k(√m)` (§ 14.5, see the notes to
Chapter XIV); its classical link with the continued fraction of `√D` is the following, which we prove from
the results of Chapter X (and Legendre's criterion, Theorem 184, which is Mathlib's
`Real.exists_rat_eq_convergent`).

Let `D` be a positive integer which is not a square and `√D = [a₀, a₁, a₂, …]`, with convergents
`pₙ/qₙ` and complete quotients `a'ₙ`.

* `pell_index_iff`: `pₙ² - D qₙ² = ±1` if and only if `a'_{n+1} = a₀ + √D`, and then
  `pₙ² - D qₙ² = (-1)^{n+1}`.
* `eq_convergent_of_pell`: every solution of `x² - D y² = ±1` in positive integers is a convergent,
  `x = pₙ`, `y = qₙ`.
* `pell_period`: there is `l ≥ 1` (the length of the period) such that `a_l = 2a₀`,
  `a_{l+i} = aᵢ` for `i ≥ 1` (so `√D = [a₀, \overline{a₁, …, a_{l-1}, 2a₀}]`), every other such index is a
  multiple of `l`, `p_{kl-1}² - D q_{kl-1}² = (-1)^{kl}`, and the positive solutions of `x² - D y² = ±1`
  are exactly the pairs `(p_{kl-1}, q_{kl-1})`, `k ≥ 1`.
-/

namespace NTKB.HardyWright

open GenContFract Filter Topology

variable {a : ℕ → ℤ}

/-- For a continued fraction with all quotients positive, the pairs `contsAux k = (p_{k-1}, q_{k-1})` are
integral with `p_{k-1} ≥ 1`, `q_{k-1} ≥ 0`. -/
lemma cf_contsAux_int_pos (ha0 : ∀ i, 0 < a i) (k : ℕ) :
    ∃ P Q : ℤ, ((cf (fun i ↦ (a i : ℝ))).contsAux k).a = P ∧
      ((cf (fun i ↦ (a i : ℝ))).contsAux k).b = Q ∧ 1 ≤ P ∧ 0 ≤ Q := by
  rcases k with _ | k
  · exact ⟨1, 0, by simp [zeroth_contAux_eq_one_zero], by simp [zeroth_contAux_eq_one_zero], le_rfl,
      le_rfl⟩
  · obtain ⟨p, q, hp, hq⟩ := cf_nums_dens_int a k
    refine ⟨p, q, by rw [← nth_cont_eq_succ_nth_contAux, ← num_eq_conts_a, hp],
      by rw [← nth_cont_eq_succ_nth_contAux, ← den_eq_conts_b, hq], ?_, ?_⟩
    · have := cf_nums_pos (a := fun i ↦ (a i : ℝ)) (N := k)
        (fun i _ ↦ by exact_mod_cast ha0 i) k le_rfl
      rw [hp] at this
      exact_mod_cast this
    · have := cf_dens_pos (a := fun i ↦ (a i : ℝ)) (N := k)
        (fun i _ _ ↦ by exact_mod_cast ha0 i) k le_rfl
      rw [hq] at this
      exact_mod_cast this.le

/-- `p_{k-1} + q_{k-1} r < p_k + q_k r` for `r > 0`, when all quotients are positive. -/
lemma cf_contsAux_lt (ha0 : ∀ i, 0 < a i) {r : ℝ} (hr : 0 < r) (k : ℕ) :
    ((cf (fun i ↦ (a i : ℝ))).contsAux k).a + ((cf (fun i ↦ (a i : ℝ))).contsAux k).b * r <
      ((cf (fun i ↦ (a i : ℝ))).contsAux (k + 1)).a +
        ((cf (fun i ↦ (a i : ℝ))).contsAux (k + 1)).b * r := by
  rcases k with _ | k
  · rw [zeroth_contAux_eq_one_zero, first_contAux_eq_h_one, cf_h]
    have : (1 : ℝ) ≤ a 0 := by exact_mod_cast ha0 0
    show (1 : ℝ) + 0 * r < a 0 + 1 * r
    linarith
  · rw [cf_contsAux_add_two]
    simp only
    obtain ⟨P1, Q1, h1, h1', hP1, hQ1⟩ := cf_contsAux_int_pos ha0 (k + 1)
    obtain ⟨P0, Q0, h0, h0', hP0, hQ0⟩ := cf_contsAux_int_pos ha0 k
    rw [h1, h1', h0, h0']
    have ha : (1 : ℝ) ≤ a (k + 1) := by exact_mod_cast ha0 (k + 1)
    have hP1' : (1 : ℝ) ≤ P1 := by exact_mod_cast hP1
    have hQ1' : (0 : ℝ) ≤ Q1 := by exact_mod_cast hQ1
    have hP0' : (1 : ℝ) ≤ P0 := by exact_mod_cast hP0
    have hQ0' : (0 : ℝ) ≤ Q0 := by exact_mod_cast hQ0
    have : (0 : ℝ) ≤ P1 + Q1 * r := by positivity
    nlinarith

section Sqrt

variable {D : ℕ}

/-- The quotients of `√D` are all positive (`a₀ = ⌊√D⌋ ≥ 1`). -/
lemma sqrt_cf_pos (hD : ¬IsSquare D) (ha : ∀ i, 1 ≤ i → 0 < a i)
    (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 √(D : ℝ))) : ∀ i, 0 < a i := by
  intro i
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [← (cf_floor_value_eq ha hx).1]
    have hD1 : 1 ≤ D := by
      rcases Nat.eq_zero_or_pos D with h | h
      · exact absurd ⟨0, by simp [h]⟩ hD
      · exact h
    exact Int.floor_pos.mpr (Real.one_le_sqrt.mpr (by exact_mod_cast hD1))
  · exact ha i hi

/-- `2 ≤ D` for a non-square natural number `D`. -/
lemma two_le_of_not_isSquare (hD : ¬IsSquare D) : 2 ≤ D := by
  by_contra h
  interval_cases D
  · exact hD ⟨0, rfl⟩
  · exact hD ⟨1, rfl⟩

/-- The key identity `a'_{n+1} (D qₙ² - pₙ²) = M + (-1)ⁿ √D`, with `M = p_{n-1} pₙ - D q_{n-1} qₙ`. -/
lemma sqrt_cq_identity (hD : ¬IsSquare D) (ha : ∀ i, 1 ≤ i → 0 < a i)
    (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 √(D : ℝ))) (n : ℕ) {α : ℝ}
    (hα : Tendsto (fun t ↦ (cf (fun i ↦ ((a (n + 1 + i) : ℤ) : ℝ))).convs t) atTop (𝓝 α)) :
    ∃ P Q P' Q' : ℤ, (cf (fun i ↦ (a i : ℝ))).nums n = P ∧ (cf (fun i ↦ (a i : ℝ))).dens n = Q ∧
      1 ≤ P' ∧ 0 ≤ Q' ∧ 1 ≤ Q ∧ P' * Q - Q' * P = (-1) ^ n ∧
      (P' : ℝ) + Q' * √(D : ℝ) < P + Q * √(D : ℝ) ∧
      α * (D * Q ^ 2 - P ^ 2) = (P' * P - D * Q' * Q) + (-1) ^ n * √(D : ℝ) ∧ 1 < α := by
  have ha0 := sqrt_cf_pos hD ha hx
  have e := cf_value_eq_completeQuotient ha hx n hα
  obtain ⟨P, Q, hP, hQ⟩ := cf_nums_dens_int a n
  obtain ⟨P', Q', hP', hQ', h1P', h0Q'⟩ := cf_contsAux_int_pos ha0 n
  have hPa : ((cf (fun i ↦ (a i : ℝ))).contsAux (n + 1)).a = P := by
    rw [← nth_cont_eq_succ_nth_contAux, ← num_eq_conts_a, hP]
  have hQb : ((cf (fun i ↦ (a i : ℝ))).contsAux (n + 1)).b = Q := by
    rw [← nth_cont_eq_succ_nth_contAux, ← den_eq_conts_b, hQ]
  have hdet := cf_contsAux_det (fun i ↦ (a i : ℝ)) n
  rw [hP', hQ', hPa, hQb] at hdet
  rw [hPa, hQb, hP', hQ'] at e
  have hsD : (0 : ℝ) < √(D : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (two_le_of_not_isSquare hD).trans' (by norm_num))
  have hlt := cf_contsAux_lt ha0 hsD n
  rw [hP', hQ', hPa, hQb] at hlt
  have hQ1 : 1 ≤ Q := by
    have := cf_dens_one_le (pos_finZ ha n) n le_rfl
    rw [hQ] at this; exact_mod_cast this
  have hα1 : 1 < α := by
    have := (cf_value_mem_Ioo (fun i hi ↦ ha (n + 1 + i) (by omega)) hα).1
    have h : (1 : ℝ) ≤ a (n + 1 + 0) := by exact_mod_cast ha (n + 1 + 0) (by omega)
    linarith
  have hW : (0 : ℝ) < α * Q + Q' := by
    have : (1 : ℝ) ≤ Q := by exact_mod_cast hQ1
    have : (0 : ℝ) ≤ Q' := by exact_mod_cast h0Q'
    nlinarith
  refine ⟨P, Q, P', Q', hP, hQ, h1P', h0Q', hQ1, by exact_mod_cast hdet, hlt, ?_, hα1⟩
  have hs : √(D : ℝ) ^ 2 = D := Real.sq_sqrt (by positivity)
  have e' : √(D : ℝ) * (α * Q + Q') = α * P + P' := by
    rw [e, div_mul_cancel₀ _ hW.ne']
  rw [← hdet]
  linear_combination (Q * √(D : ℝ) + P) * e' + (-α * Q ^ 2 - Q' * Q) * hs

/-- If `r + s √D = 0` with integers `r, s`, then `s = 0` (and `r = 0`). -/
lemma int_add_mul_sqrt_eq_zero (hD : ¬IsSquare D) {r s : ℤ} (h : (r : ℝ) + s * √(D : ℝ) = 0) :
    r = 0 ∧ s = 0 := by
  have hirr : Irrational √(D : ℝ) := irrational_sqrt_natCast_iff.mpr hD
  have hs : s = 0 := by
    by_contra hs
    apply hirr
    refine ⟨-r / s, ?_⟩
    push_cast
    rw [div_eq_iff (by exact_mod_cast hs)]
    linarith
  subst hs
  simpa using h

/-- **Pell's equation and the complete quotients.** For `√D = [a₀, a₁, …]` (`D` not a square),
`pₙ² - D qₙ² = ±1` if and only if the complete quotient `a'_{n+1}` equals `a₀ + √D`; and then
`pₙ² - D qₙ² = (-1)^{n+1}`. -/
theorem pell_index_iff (hD : ¬IsSquare D) (ha : ∀ i, 1 ≤ i → 0 < a i)
    (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 √(D : ℝ))) (n : ℕ) {α : ℝ}
    (hα : Tendsto (fun t ↦ (cf (fun i ↦ ((a (n + 1 + i) : ℤ) : ℝ))).convs t) atTop (𝓝 α)) :
    (((cf (fun i ↦ (a i : ℝ))).nums n ^ 2 - D * (cf (fun i ↦ (a i : ℝ))).dens n ^ 2 = 1 ∨
        (cf (fun i ↦ (a i : ℝ))).nums n ^ 2 - D * (cf (fun i ↦ (a i : ℝ))).dens n ^ 2 = -1) ↔
      α = a 0 + √(D : ℝ)) ∧
    (α = a 0 + √(D : ℝ) →
      (cf (fun i ↦ (a i : ℝ))).nums n ^ 2 - D * (cf (fun i ↦ (a i : ℝ))).dens n ^ 2 = (-1) ^ (n + 1)) := by
  obtain ⟨P, Q, P', Q', hP, hQ, h1P', h0Q', hQ1, hdet, hlt, hid, hα1⟩ :=
    sqrt_cq_identity hD ha hx n hα
  rw [hP, hQ]
  have hs : √(D : ℝ) ^ 2 = D := Real.sq_sqrt (by positivity)
  have hfl : ⌊√(D : ℝ)⌋ = a 0 := (cf_floor_value_eq ha hx).1
  obtain ⟨N, hN⟩ : ∃ N : ℤ, N = P ^ 2 - D * Q ^ 2 := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℤ, M = P' * P - D * Q' * Q := ⟨_, rfl⟩
  have hNr : (N : ℝ) = P ^ 2 - D * Q ^ 2 := by rw [hN]; push_cast; ring
  have hMr : (M : ℝ) = P' * P - D * Q' * Q := by rw [hM]; push_cast; ring
  rw [← hNr]
  -- the converse direction
  have hconv : α = a 0 + √(D : ℝ) → N = (-1) ^ (n + 1) := by
    intro h
    rw [h] at hid
    have : ((-(a 0) * N - M : ℤ) : ℝ) + ((-N - (-1) ^ n : ℤ) : ℝ) * √(D : ℝ) = 0 := by
      push_cast
      linear_combination hid - (a 0 + √(D : ℝ)) * hNr - hMr
    have := (int_add_mul_sqrt_eq_zero hD this).2
    rw [pow_succ]; linarith
  refine ⟨⟨fun hN1 ↦ ?_, fun h ↦ ?_⟩, fun h ↦ by rw [hconv h]; push_cast; ring⟩
  · -- `N = ±1`
    have hN1' : N = 1 ∨ N = -1 := by
      rcases hN1 with h | h
      · left; exact_mod_cast h
      · right; exact_mod_cast h
    have hNsq : N * N = 1 := by rcases hN1' with h | h <;> rw [h] <;> norm_num
    have hNsq' : (N : ℝ) * N = 1 := by exact_mod_cast hNsq
    obtain ⟨ε, hε⟩ : ∃ ε : ℤ, ε = (-1) ^ n := ⟨_, rfl⟩
    have hεsq : ε * ε = 1 := by rw [hε, ← mul_pow]; simp
    have hεr : (ε : ℝ) = (-1) ^ n := by rw [hε]; push_cast; ring
    have hdet' : (P' : ℝ) * Q - Q' * P = ε := by rw [hε]; exact_mod_cast hdet
    -- `α = u + v √D` and `β = u - v √D = -(p_{n-1} + q_{n-1} √D)/(pₙ + qₙ √D)`
    obtain ⟨u, hu⟩ : ∃ u : ℤ, u = -N * M := ⟨_, rfl⟩
    obtain ⟨v, hv⟩ : ∃ v : ℤ, v = -N * ε := ⟨_, rfl⟩
    have h' : α * (-N) = M + ε * √(D : ℝ) := by
      rw [hNr, hMr, hεr]; linear_combination hid
    have hαuv : α = u + v * √(D : ℝ) := by
      rw [hu, hv]; push_cast
      linear_combination (-(N : ℝ)) * h' - α * hNsq'
    have hsD : 0 < √(D : ℝ) :=
      Real.sqrt_pos.mpr (by exact_mod_cast (two_le_of_not_isSquare hD).trans' (by norm_num))
    have hP'pos : (0 : ℝ) < P' + Q' * √(D : ℝ) := by
      have : (1 : ℝ) ≤ P' := by exact_mod_cast h1P'
      have : (0 : ℝ) ≤ Q' := by exact_mod_cast h0Q'
      nlinarith
    have hPQ : (0 : ℝ) < P + Q * √(D : ℝ) := hP'pos.trans hlt
    have hβ : ((u : ℝ) - v * √(D : ℝ)) * (P + Q * √(D : ℝ)) = -(P' + Q' * √(D : ℝ)) := by
      rw [hu, hv]; push_cast
      rw [hMr]
      linear_combination ((N : ℝ) * ε * Q) * hs - ((N : ℝ) * (Q * D + P * √(D : ℝ))) * hdet' -
        ((P' : ℝ) + Q' * √(D : ℝ)) * hNsq' + ((N : ℝ) * (P' + Q' * √(D : ℝ))) * hNr
    have hβlt : -1 < (u : ℝ) - v * √(D : ℝ) ∧ (u : ℝ) - v * √(D : ℝ) < 0 := by
      have h1 : (u : ℝ) - v * √(D : ℝ) = -(P' + Q' * √(D : ℝ)) / (P + Q * √(D : ℝ)) := by
        rw [eq_div_iff hPQ.ne', hβ]
      rw [h1]
      constructor
      · rw [lt_div_iff₀ hPQ]; linarith
      · exact div_neg_of_neg_of_pos (by linarith) hPQ
    -- `v = 1` and `u = a₀`
    have hv1 : v = 1 ∨ v = -1 := by
      have : v * v = 1 := by
        rw [hv]; linear_combination (ε * ε) * hNsq + hεsq
      rcases Int.eq_one_or_neg_one_of_mul_eq_one this with h | h <;> simp [h]
    have hv1' : v = 1 := by
      rcases hv1 with h | h
      · exact h
      · exfalso
        rw [h] at hαuv hβlt
        push_cast at hαuv hβlt
        linarith [hβlt.1]
    rw [hv1'] at hαuv hβlt
    push_cast at hαuv hβlt
    have hu0 : u = a 0 := by
      rw [← hfl, eq_comm, Int.floor_eq_iff]
      constructor <;> linarith [hβlt.1, hβlt.2]
    rw [hαuv, hu0, one_mul]
  · rw [hconv h]
    rcases neg_one_pow_eq_or ℤ (n + 1) with h' | h' <;> rw [h'] <;> simp

/-- Every solution of `x² - D y² = ±1` in positive integers is a convergent of `√D`: `x = pₙ`, `y = qₙ`
(by Legendre's criterion, Theorem 184). -/
theorem eq_convergent_of_pell (hD : ¬IsSquare D) (ha : ∀ i, 1 ≤ i → 0 < a i)
    (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 √(D : ℝ))) {X Y : ℤ}
    (hX : 0 < X) (hY : 0 < Y) (h : X ^ 2 - D * Y ^ 2 = 1 ∨ X ^ 2 - D * Y ^ 2 = -1) :
    ∃ n, (cf (fun i ↦ (a i : ℝ))).nums n = X ∧ (cf (fun i ↦ (a i : ℝ))).dens n = Y := by
  have hcop : IsCoprime X Y := by
    rcases h with h | h
    · exact ⟨X, -(D * Y), by linear_combination h⟩
    · exact ⟨-X, D * Y, by linear_combination -h⟩
  have hden : ((X / Y : ℚ).den : ℤ) = Y :=
    Rat.den_div_eq_of_coprime hY (Int.isCoprime_iff_gcd_eq_one.mp hcop)
  have hD2 : (2 : ℝ) ≤ D := by exact_mod_cast two_le_of_not_isSquare hD
  have hs1 : 1 < √(D : ℝ) := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  have hs : √(D : ℝ) ^ 2 = D := Real.sq_sqrt (by positivity)
  have hXY : Y ≤ X := by
    have : Y ^ 2 ≤ X ^ 2 := by
      have hD2' : (2 : ℤ) ≤ D := by exact_mod_cast two_le_of_not_isSquare hD
      rcases h with h | h <;> nlinarith
    nlinarith
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hYr : (0 : ℝ) < Y := by exact_mod_cast hY
  have hXYr : (Y : ℝ) ≤ X := by exact_mod_cast hXY
  have hsum : 2 * (Y : ℝ) < X + Y * √(D : ℝ) := by nlinarith
  have hprod : |(X : ℝ) - Y * √(D : ℝ)| * (X + Y * √(D : ℝ)) = 1 := by
    rw [← abs_of_pos (show (0 : ℝ) < X + Y * √(D : ℝ) by linarith), ← abs_mul]
    have : ((X : ℝ) - Y * √(D : ℝ)) * (X + Y * √(D : ℝ)) = ((X ^ 2 - D * Y ^ 2 : ℤ) : ℝ) := by
      push_cast; linear_combination (-(Y : ℝ) ^ 2) * hs
    rw [this]
    rcases h with h | h <;> rw [h] <;> simp
  have hlt : |√(D : ℝ) - ((X / Y : ℚ) : ℝ)| < 1 / (2 * ((X / Y : ℚ).den : ℝ) ^ 2) := by
    have hd : ((X / Y : ℚ).den : ℝ) = Y := by exact_mod_cast hden
    rw [hd]
    push_cast
    have e : √(D : ℝ) - X / Y = -((X - Y * √(D : ℝ)) / Y) := by field_simp; ring
    rw [e, abs_neg, abs_div, abs_of_pos hYr]
    have hpos : (0 : ℝ) < X + Y * √(D : ℝ) := by linarith
    have h1 : |(X : ℝ) - Y * √(D : ℝ)| = 1 / (X + Y * √(D : ℝ)) := by
      rw [eq_div_iff hpos.ne', hprod]
    rw [h1, div_div, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  obtain ⟨n, hn⟩ := Real.exists_rat_eq_convergent hlt
  refine ⟨n, ?_⟩
  have hc := cf_convs_eq_convergent ha hx n
  rw [← hn] at hc
  obtain ⟨p, q, hp, hq⟩ := cf_nums_dens_int a n
  have hqpos : 0 < q := by
    have := cf_dens_pos (pos_fin ha n) n le_rfl
    rw [hq] at this; exact_mod_cast this
  rw [cf_convs, hp, hq] at hc
  push_cast at hc
  obtain ⟨h1, h2⟩ := eq_of_div_eq_div (cf_isCoprime_nums_dens a n hp hq) hcop hqpos hY hc
  rw [hp, hq, h1, h2]; exact ⟨rfl, rfl⟩

/-- `m` is a *Pell index* of the continued fraction `[a₀, a₁, …]`: `m ≥ 1`, `a_m = 2a₀` and
`a_{m+i} = aᵢ` for `i ≥ 1`, i.e. the complete quotient `a'_m` is `[2a₀, a₁, a₂, …]`. -/
def IsPellIndex (a : ℕ → ℤ) (m : ℕ) : Prop :=
  1 ≤ m ∧ a m = 2 * a 0 ∧ ∀ i, 1 ≤ i → a (m + i) = a i

/-- `[2a₀, a₁, a₂, …] = a₀ + [a₀, a₁, a₂, …]`. -/
lemma cf_tendsto_double_head (ha : ∀ i, 1 ≤ i → 0 < a i) {x : ℝ}
    (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 x)) :
    Tendsto (fun t ↦ (cf (fun i ↦ ((if i = 0 then 2 * a 0 else a i : ℤ) : ℝ))).convs t) atTop
      (𝓝 (a 0 + x)) := by
  have hb : ∀ i, 1 ≤ i → 0 < (if i = 0 then 2 * a 0 else a i) := fun i hi ↦ by
    simp only [show i ≠ 0 by omega, ite_false]; exact ha i hi
  have e : ∀ t, (cf (fun i ↦ ((if i = 0 then 2 * a 0 else a i : ℤ) : ℝ))).convs t =
      a 0 + (cf (fun i ↦ (a i : ℝ))).convs t := by
    intro t
    rcases t with _ | t
    · simp; ring
    · rw [cf_value_succ (fun i h1 _ ↦ hb i h1), cf_value_succ (fun i h1 _ ↦ ha i h1)]
      simp only [ite_true, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false]
      push_cast; ring
  simp_rw [e]
  exact tendsto_const_nhds.add hx

/-- `a'_{n+1} = a₀ + √D` if and only if `n + 1` is a Pell index. -/
lemma cq_eq_iff_isPellIndex (ha : ∀ i, 1 ≤ i → 0 < a i)
    (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 √(D : ℝ))) (n : ℕ) {α : ℝ}
    (hα : Tendsto (fun t ↦ (cf (fun i ↦ ((a (n + 1 + i) : ℤ) : ℝ))).convs t) atTop (𝓝 α)) :
    α = a 0 + √(D : ℝ) ↔ IsPellIndex a (n + 1) := by
  have hb := cf_tendsto_double_head ha hx
  constructor
  · intro h
    rw [h] at hα
    have := cf_eq_of_tendsto (fun i hi ↦ ha (n + 1 + i) (by omega))
      (fun i hi ↦ by simp only [show i ≠ 0 by omega, ite_false]; exact ha i hi) hα hb
    refine ⟨by omega, ?_, fun i hi ↦ ?_⟩
    · have := congrFun this 0; simpa using this
    · have := congrFun this i; simpa [show i ≠ 0 by omega] using this
  · rintro ⟨-, h0, h⟩
    have e : (fun i ↦ ((a (n + 1 + i) : ℤ) : ℝ)) =
        fun i ↦ ((if i = 0 then 2 * a 0 else a i : ℤ) : ℝ) := by
      funext i
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · simp [h0]
      · simp [show i ≠ 0 by omega, h i hi]
    rw [e] at hα
    exact tendsto_nhds_unique hα hb

/-- `pₙ² - D qₙ² = ±1` if and only if `n + 1` is a Pell index, and then `pₙ² - D qₙ² = (-1)^{n+1}`. -/
theorem pell_iff_isPellIndex (hD : ¬IsSquare D) (ha : ∀ i, 1 ≤ i → 0 < a i)
    (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 √(D : ℝ))) (n : ℕ) :
    (((cf (fun i ↦ (a i : ℝ))).nums n ^ 2 - D * (cf (fun i ↦ (a i : ℝ))).dens n ^ 2 = 1 ∨
        (cf (fun i ↦ (a i : ℝ))).nums n ^ 2 - D * (cf (fun i ↦ (a i : ℝ))).dens n ^ 2 = -1) ↔
      IsPellIndex a (n + 1)) ∧
    (IsPellIndex a (n + 1) →
      (cf (fun i ↦ (a i : ℝ))).nums n ^ 2 - D * (cf (fun i ↦ (a i : ℝ))).dens n ^ 2 =
        (-1) ^ (n + 1)) := by
  obtain ⟨α, hα⟩ := cf_convs_tendsto (fun i (hi : 1 ≤ i) ↦ ha (n + 1 + i) (by omega))
  obtain ⟨h1, h2⟩ := pell_index_iff hD ha hx n hα
  have h3 := cq_eq_iff_isPellIndex ha hx n hα
  exact ⟨h1.trans h3, fun h ↦ h2 (h3.mpr h)⟩

lemma IsPellIndex.add {m₁ m₂ : ℕ} (h₁ : IsPellIndex a m₁) (h₂ : IsPellIndex a m₂) :
    IsPellIndex a (m₁ + m₂) := by
  refine ⟨by have := h₁.1; omega, by rw [h₁.2.2 m₂ h₂.1, h₂.2.1], fun i hi ↦ ?_⟩
  rw [add_assoc, h₁.2.2 (m₂ + i) (by omega), h₂.2.2 i hi]

lemma IsPellIndex.sub {m l : ℕ} (hm : IsPellIndex a m) (hl : IsPellIndex a l) (hlm : l < m) :
    IsPellIndex a (m - l) := by
  refine ⟨by omega, ?_, fun i hi ↦ ?_⟩
  · rw [← hl.2.2 (m - l) (by omega), show l + (m - l) = m by omega, hm.2.1]
  · rw [← hl.2.2 (m - l + i) (by omega), show l + (m - l + i) = m + i by omega, hm.2.2 i hi]

/-- **Pell's equation and the period of `√D`.** Let `D` be a positive integer which is not a square and
`√D = [a₀, a₁, a₂, …]` with convergents `pₙ/qₙ`. There is `l ≥ 1` (the length of the period) with
`a_l = 2a₀` and `a_{l+i} = aᵢ` for `i ≥ 1`, i.e. `√D = [a₀, a₁, …, a_{l-1}, 2a₀]` with the part after `a₀`
repeated, minimal in the sense that every index `m` with the same property is a multiple of `l`. Moreover
`p_{kl-1}² - D q_{kl-1}² = (-1)^{kl}` for `k ≥ 1`, and the solutions of `x² - D y² = ±1` in positive
integers are exactly the pairs `(p_{kl-1}, q_{kl-1})`, `k ≥ 1`. -/
theorem pell_period (hD : ¬IsSquare D) (ha : ∀ i, 1 ≤ i → 0 < a i)
    (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 √(D : ℝ))) :
    ∃ l : ℕ, 1 ≤ l ∧ a l = 2 * a 0 ∧ (∀ i, 1 ≤ i → a (l + i) = a i) ∧
      (∀ m, 1 ≤ m → a m = 2 * a 0 → (∀ i, 1 ≤ i → a (m + i) = a i) → l ∣ m) ∧
      (∀ k, 1 ≤ k → (cf (fun i ↦ (a i : ℝ))).nums (k * l - 1) ^ 2 -
        D * (cf (fun i ↦ (a i : ℝ))).dens (k * l - 1) ^ 2 = (-1) ^ (k * l)) ∧
      ∀ X Y : ℤ, 0 < X → 0 < Y →
        ((X ^ 2 - D * Y ^ 2 = 1 ∨ X ^ 2 - D * Y ^ 2 = -1) ↔
          ∃ k, 1 ≤ k ∧ (cf (fun i ↦ (a i : ℝ))).nums (k * l - 1) = X ∧
            (cf (fun i ↦ (a i : ℝ))).dens (k * l - 1) = Y) := by
  -- a Pell index exists, since `x² - D y² = 1` has a nontrivial solution
  have hex : ∃ m, IsPellIndex a m := by
    obtain ⟨x, y, hxy, hy⟩ := Pell.exists_of_not_isSquare (d := (D : ℤ))
      (by exact_mod_cast (two_le_of_not_isSquare hD).trans' (by norm_num))
      (by rwa [Int.isSquare_natCast_iff])
    have hY : 0 < |y| := abs_pos.mpr hy
    have hX : 0 < |x| := by
      have : x ≠ 0 := by
        rintro rfl
        have : (0 : ℤ) ≤ D * y ^ 2 := by positivity
        linarith
      exact abs_pos.mpr this
    obtain ⟨n, hn1, hn2⟩ := eq_convergent_of_pell hD ha hx hX hY
      (Or.inl (by rw [sq_abs, sq_abs]; exact hxy))
    refine ⟨n + 1, ((pell_iff_isPellIndex hD ha hx n).1.mp (Or.inl ?_))⟩
    rw [hn1, hn2]
    have : ((|x| ^ 2 - D * |y| ^ 2 : ℤ) : ℝ) = 1 := by rw [sq_abs, sq_abs, hxy]; simp
    exact_mod_cast this
  classical
  have hlP : IsPellIndex a (Nat.find hex) := Nat.find_spec hex
  have hmin : ∀ m, m < Nat.find hex → ¬IsPellIndex a m := fun m hm ↦ Nat.find_min hex hm
  set l := Nat.find hex with hl
  have hdvd : ∀ m, IsPellIndex a m → l ∣ m := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      rcases lt_trichotomy m l with h | h | h
      · exact absurd hm (hmin m h)
      · rw [h]
      · have := ih (m - l) (by have := hlP.1; omega) (hm.sub hlP h)
        have h' : m = (m - l) + l := by omega
        rw [h']; exact dvd_add this dvd_rfl
  have hmul : ∀ k, 1 ≤ k → IsPellIndex a (k * l) := by
    intro k hk
    induction k with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk'
      · simpa using hlP
      · rw [add_mul, one_mul]; exact (ih hk').add hlP
  have hl1 := hlP.1
  refine ⟨l, hl1, hlP.2.1, hlP.2.2, fun m hm h0 h ↦ hdvd m ⟨hm, h0, h⟩, fun k hk ↦ ?_, ?_⟩
  · have hkl : 1 ≤ k * l := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have := (pell_iff_isPellIndex hD ha hx (k * l - 1)).2
    rw [show k * l - 1 + 1 = k * l by omega] at this
    exact this (hmul k hk)
  · intro X Y hX hY
    constructor
    · intro h
      obtain ⟨n, hn1, hn2⟩ := eq_convergent_of_pell hD ha hx hX hY h
      have hP : IsPellIndex a (n + 1) := by
        refine (pell_iff_isPellIndex hD ha hx n).1.mp ?_
        rw [hn1, hn2]
        rcases h with h | h
        · left; exact_mod_cast h
        · right; exact_mod_cast h
      obtain ⟨k, hk⟩ := hdvd (n + 1) hP
      refine ⟨k, ?_, ?_⟩
      · rcases Nat.eq_zero_or_pos k with rfl | h
        · simp at hk
        · exact h
      · rw [show k * l - 1 = n by rw [mul_comm]; omega]; exact ⟨hn1, hn2⟩
    · rintro ⟨k, hk, h1, h2⟩
      have hkl : 1 ≤ k * l := Nat.one_le_iff_ne_zero.mpr (by positivity)
      have := (pell_iff_isPellIndex hD ha hx (k * l - 1)).2
      rw [show k * l - 1 + 1 = k * l by omega] at this
      have h3 := this (hmul k hk)
      rw [h1, h2] at h3
      have h4 : ((X ^ 2 - D * Y ^ 2 : ℤ) : ℝ) = (((-1) ^ (k * l) : ℤ) : ℝ) := by
        push_cast; exact h3
      have h5 : X ^ 2 - D * Y ^ 2 = (-1) ^ (k * l) := by exact_mod_cast h4
      rw [h5]
      exact neg_one_pow_eq_or ℤ (k * l)

end Sqrt

end NTKB.HardyWright
