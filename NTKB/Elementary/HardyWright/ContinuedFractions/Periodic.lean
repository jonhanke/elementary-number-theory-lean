/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.ContinuedFractions.Equivalence
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# Periodic continued fractions (Hardy–Wright, Chapter X, § 10.12)

A simple continued fraction `[a₀, a₁, …]` is *periodic* if `a_{l+k} = a_l` for a fixed `k > 0` and all
`l ≥ L`. A *quadratic surd* is an irrational root of a quadratic equation with integral coefficients.

* Theorem 176: a periodic continued fraction is a quadratic surd.
* Theorem 177 (Lagrange): the continued fraction of a quadratic surd is periodic. We follow Hardy–Wright's
  proof: the complete quotients `a'ₙ` satisfy equations `Aₙ y² + Bₙ y + Cₙ = 0` whose integral
  coefficients are bounded independently of `n`, so some equation occurs three times and two of the
  corresponding complete quotients coincide.
-/

namespace NTKB.HardyWright

open GenContFract Filter Topology

variable {a : ℕ → ℤ}

/-- The complete quotient formula `x = (a'_{n+2} p_{n+1} + pₙ)/(a'_{n+2} q_{n+1} + qₙ)` with the integers
`p_{n+1}, q_{n+1}, pₙ, qₙ` and the determinant. -/
lemma cf_value_eq_cq_int (ha : ∀ i, 1 ≤ i → 0 < a i) {x : ℝ}
    (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 x)) (n : ℕ) {y : ℝ}
    (hy : Tendsto (fun t ↦ (cf (fun i ↦ ((a (n + 2 + i) : ℤ) : ℝ))).convs t) atTop (𝓝 y)) :
    ∃ p1 q1 p0 q0 : ℤ, (cf (fun i ↦ (a i : ℝ))).nums (n + 1) = p1 ∧
      (cf (fun i ↦ (a i : ℝ))).dens (n + 1) = q1 ∧ (cf (fun i ↦ (a i : ℝ))).nums n = p0 ∧
      (cf (fun i ↦ (a i : ℝ))).dens n = q0 ∧ x = (y * p1 + p0) / (y * q1 + q0) ∧
      p1 * q0 - p0 * q1 = (-1) ^ n ∧ 0 < q0 ∧ 0 < q1 ∧ 1 < y := by
  have hy' : Tendsto (fun t ↦ (cf (fun i ↦ ((a (n + 1 + 1 + i) : ℤ) : ℝ))).convs t) atTop (𝓝 y) := by
    simpa only [show n + 1 + 1 = n + 2 by ring] using hy
  have e := cf_value_eq_completeQuotient ha hx (n + 1) hy'
  obtain ⟨p1, q1, hp1, hq1⟩ := cf_nums_dens_int a (n + 1)
  obtain ⟨p0, q0, hp0, hq0⟩ := cf_nums_dens_int a n
  rw [← nth_cont_eq_succ_nth_contAux, ← nth_cont_eq_succ_nth_contAux, ← num_eq_conts_a,
    ← num_eq_conts_a, ← den_eq_conts_b, ← den_eq_conts_b, hp1, hq1, hp0, hq0] at e
  have hdet := cf_nums_mul_dens_sub (fun i ↦ (a i : ℝ)) n
  rw [hp1, hq1, hp0, hq0] at hdet
  have hp := pos_fin ha (n + 2)
  have hq1pos : (0 : ℝ) < q1 := by rw [← hq1]; exact cf_dens_pos hp (n + 1) (by omega)
  have hq0pos : (0 : ℝ) < q0 := by rw [← hq0]; exact cf_dens_pos hp n (by omega)
  have hy1 : 1 < y := by
    have := (cf_value_mem_Ioo (fun i hi ↦ ha (n + 2 + i) (by omega)) hy).1
    have h' : (1 : ℝ) ≤ a (n + 2 + 0) := by exact_mod_cast ha (n + 2 + 0) (by omega)
    linarith
  exact ⟨p1, q1, p0, q0, hp1, hq1, hp0, hq0, e, by exact_mod_cast hdet, by exact_mod_cast hq0pos,
    by exact_mod_cast hq1pos, hy1⟩

/-- A simple continued fraction is periodic: `a_{l+k} = a_l` for some `k > 0` and all `l ≥ L`. -/
def IsPeriodic (a : ℕ → ℤ) : Prop :=
  ∃ L k : ℕ, 0 < k ∧ ∀ l, L ≤ l → a (l + k) = a l

/-- **Theorem 176.** A periodic continued fraction is a quadratic surd, i.e. an irrational root of a
quadratic equation with integral coefficients. -/
@[kb "hardywright2008" "Thm 176, p. 184"]
theorem quadratic_of_isPeriodic (ha : ∀ i, 1 ≤ i → 0 < a i) {x : ℝ}
    (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 x)) (hper : IsPeriodic a) :
    Irrational x ∧ ∃ A B C : ℤ, A ≠ 0 ∧ A * x ^ 2 + B * x + C = 0 := by
  have hirr := (irrational_iff_exists_unique_cf x).2 a ha hx
  refine ⟨hirr, ?_⟩
  obtain ⟨L, k, hk, hper⟩ := hper
  -- the purely periodic tail `c = [a_{L+2}, a_{L+3}, …]` and its value `ω`
  set c : ℕ → ℤ := fun i ↦ a (L + 2 + i) with hc
  have hcpos : ∀ i, 1 ≤ i → 0 < c i := fun i _ ↦ ha (L + 2 + i) (by omega)
  have hcper : ∀ i, c (k + i) = c i := by
    intro i; simp only [hc]
    rw [show L + 2 + (k + i) = (L + 2 + i) + k by ring]
    exact hper _ (by omega)
  obtain ⟨ω, hω⟩ := cf_convs_tendsto hcpos
  -- `ω = [c₀, …, c_{k-1}, ω]`
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have htail : Tendsto (fun t ↦ (cf (fun i ↦ ((c (k' + 1 + i) : ℤ) : ℝ))).convs t) atTop (𝓝 ω) := by
    have e : (fun i ↦ ((c (k' + 1 + i) : ℤ) : ℝ)) = fun i ↦ (c i : ℝ) := by
      funext i; rw [hcper]
    rw [e]; exact hω
  have e := cf_value_eq_completeQuotient (a := c) (fun i hi ↦ hcpos i hi) hω k' htail
  -- integers `p', q', p'', q''`
  obtain ⟨p', q', hp', hq'⟩ := cf_nums_dens_int c k'
  rw [← nth_cont_eq_succ_nth_contAux, ← num_eq_conts_a, ← den_eq_conts_b, hp', hq'] at e
  obtain ⟨p'', q'', hp'', hq'', hq''nn⟩ : ∃ p'' q'' : ℤ,
      ((cf (fun i ↦ (c i : ℝ))).contsAux k').a = p'' ∧
      ((cf (fun i ↦ (c i : ℝ))).contsAux k').b = q'' ∧ 0 ≤ q'' := by
    rcases k' with _ | k'
    · exact ⟨1, 0, by simp [zeroth_contAux_eq_one_zero], by simp [zeroth_contAux_eq_one_zero], le_rfl⟩
    · obtain ⟨p, q, hp, hq⟩ := cf_nums_dens_int c k'
      refine ⟨p, q, by rw [← nth_cont_eq_succ_nth_contAux, ← num_eq_conts_a, hp],
        by rw [← nth_cont_eq_succ_nth_contAux, ← den_eq_conts_b, hq], ?_⟩
      have := cf_dens_pos (pos_fin hcpos k') k' le_rfl
      rw [hq] at this; exact_mod_cast this.le
  rw [hp'', hq''] at e
  have hq'pos : (0 : ℝ) < q' := by rw [← hq']; exact cf_dens_pos (pos_fin hcpos k') k' le_rfl
  have hω1 : 0 < ω := by
    have := (cf_value_mem_Ioo hcpos hω).1
    have h : (0 : ℝ) < c 0 := by exact_mod_cast ha (L + 2 + 0) (by omega)
    linarith
  have hW : (0 : ℝ) < ω * q' + q'' := by
    have : (0 : ℝ) ≤ q'' := by exact_mod_cast hq''nn
    nlinarith
  -- `q' ω² + (q'' - p') ω - p'' = 0`
  have hωeq : (q' : ℝ) * ω ^ 2 + (q'' - p') * ω - p'' = 0 := by
    have := e
    rw [eq_div_iff hW.ne'] at this
    linear_combination this
  -- `x` is equivalent to `ω`, so `ω = (a₁ x + b₁)/(c₁ x + d₁)`
  have hcx : Tendsto (fun t ↦ (cf (fun i ↦ ((a (L + 2 + i) : ℤ) : ℝ))).convs t) atTop (𝓝 ω) := hω
  obtain ⟨a₁, b₁, c₁, d₁, hdet, hne, hωx⟩ := (isEquivalent_completeQuotient ha hx L hcx).symm
  have hsub : (q' : ℝ) * (a₁ * x + b₁) ^ 2 + (q'' - p') * (a₁ * x + b₁) * (c₁ * x + d₁) -
      p'' * (c₁ * x + d₁) ^ 2 = 0 := by
    generalize hN : (a₁ : ℝ) * x + b₁ = N at hωx ⊢
    generalize hDn : (c₁ : ℝ) * x + d₁ = Dn at hωx hne ⊢
    rw [hωx] at hωeq
    field_simp at hωeq
    linear_combination hωeq
  refine ⟨q' * a₁ ^ 2 + (q'' - p') * a₁ * c₁ - p'' * c₁ ^ 2,
    2 * q' * a₁ * b₁ + (q'' - p') * (a₁ * d₁ + b₁ * c₁) - 2 * p'' * c₁ * d₁,
    q' * b₁ ^ 2 + (q'' - p') * b₁ * d₁ - p'' * d₁ ^ 2, ?_, ?_⟩
  · intro hA
    have hquad : ((q' * a₁ ^ 2 + (q'' - p') * a₁ * c₁ - p'' * c₁ ^ 2 : ℤ) : ℝ) * x ^ 2 +
        ((2 * q' * a₁ * b₁ + (q'' - p') * (a₁ * d₁ + b₁ * c₁) - 2 * p'' * c₁ * d₁ : ℤ) : ℝ) * x +
        ((q' * b₁ ^ 2 + (q'' - p') * b₁ * d₁ - p'' * d₁ ^ 2 : ℤ) : ℝ) = 0 := by
      push_cast
      linear_combination hsub
    rw [hA] at hquad
    simp only [Int.cast_zero, zero_mul, zero_add] at hquad
    set B := 2 * q' * a₁ * b₁ + (q'' - p') * (a₁ * d₁ + b₁ * c₁) - 2 * p'' * c₁ * d₁
    set C := q' * b₁ ^ 2 + (q'' - p') * b₁ * d₁ - p'' * d₁ ^ 2
    have hB : B = 0 := by
      by_contra hB
      apply hirr
      refine ⟨-C / B, ?_⟩
      push_cast
      rw [div_eq_iff (by exact_mod_cast hB)]
      linear_combination -hquad
    rw [hB] at hquad
    simp only [Int.cast_zero, zero_mul, zero_add] at hquad
    have hC : C = 0 := by exact_mod_cast hquad
    -- `q' (a₁ d₁ - b₁ c₁)² = d₁² A - c₁ d₁ B + c₁² C`
    have key : q' * (a₁ * d₁ - b₁ * c₁) ^ 2 =
        d₁ ^ 2 * (q' * a₁ ^ 2 + (q'' - p') * a₁ * c₁ - p'' * c₁ ^ 2) - c₁ * d₁ * B + c₁ ^ 2 * C := by
      simp only [B, C]; ring
    rw [hA, hB, hC] at key
    have : q' = 0 := by
      rcases hdet with h | h <;> rw [h] at key <;> simpa using key
    have : (q' : ℝ) = 0 := by exact_mod_cast this
    linarith
  · push_cast
    linear_combination hsub

/-- Three roots of a genuine quadratic equation are not pairwise distinct. -/
lemma three_roots {A B C y₁ y₂ y₃ : ℝ} (hA : A ≠ 0) (h₁ : A * y₁ ^ 2 + B * y₁ + C = 0)
    (h₂ : A * y₂ ^ 2 + B * y₂ + C = 0) (h₃ : A * y₃ ^ 2 + B * y₃ + C = 0) :
    y₁ = y₂ ∨ y₁ = y₃ ∨ y₂ = y₃ := by
  by_contra h
  push Not at h
  obtain ⟨h12, h13, h23⟩ := h
  have e2 : A * (y₁ + y₂) + B = 0 := by
    have : (y₁ - y₂) * (A * (y₁ + y₂) + B) = 0 := by linear_combination h₁ - h₂
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h12)
  have e3 : A * (y₁ + y₃) + B = 0 := by
    have : (y₁ - y₃) * (A * (y₁ + y₃) + B) = 0 := by linear_combination h₁ - h₃
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h13)
  have : A * (y₂ - y₃) = 0 := by linear_combination e2 - e3
  exact h23 (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hA))

/-- **Theorem 177** (Lagrange). The continued fraction which represents a quadratic surd is periodic. -/
@[kb "hardywright2008" "Thm 177, p. 185"]
theorem isPeriodic_of_quadratic (ha : ∀ i, 1 ≤ i → 0 < a i) {x : ℝ}
    (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 x)) {A B C : ℤ} (hA : A ≠ 0)
    (hquad : A * x ^ 2 + B * x + C = 0) : IsPeriodic a := by
  have hirr := (irrational_iff_exists_unique_cf x).2 a ha hx
  -- the complete quotients `α n = a'_{n+2}` and the integers `p_{n+1}, q_{n+1}, pₙ, qₙ`
  choose α hα using fun n ↦ cf_convs_tendsto (fun i (hi : 1 ≤ i) ↦ ha (n + 2 + i) (by omega))
  choose p1 q1 p0 q0 hp1 hq1 hp0 hq0 he hdet hq0pos hq1pos hα1 using
    fun n ↦ cf_value_eq_cq_int ha hx n (hα n)
  -- the equation `Aₙ y² + Bₙ y + Cₙ = 0` of `α n`
  set An : ℕ → ℤ := fun n ↦ A * p1 n ^ 2 + B * p1 n * q1 n + C * q1 n ^ 2 with hAn
  set Bn : ℕ → ℤ := fun n ↦ 2 * A * p1 n * p0 n + B * (p1 n * q0 n + p0 n * q1 n) +
    2 * C * q1 n * q0 n with hBn
  set Cn : ℕ → ℤ := fun n ↦ A * p0 n ^ 2 + B * p0 n * q0 n + C * q0 n ^ 2 with hCn
  have heq : ∀ n, (An n : ℝ) * α n ^ 2 + Bn n * α n + Cn n = 0 := by
    intro n
    have hW : (0 : ℝ) < α n * q1 n + q0 n := by
      have h1 : (0 : ℝ) < q1 n := by exact_mod_cast hq1pos n
      have h0 : (0 : ℝ) < q0 n := by exact_mod_cast hq0pos n
      nlinarith [hα1 n]
    have h := hquad
    rw [he n] at h
    field_simp at h
    simp only [hAn, hBn, hCn]
    push_cast
    linear_combination h
  -- `Aₙ ≠ 0`, since `x` is irrational
  have hAn0 : ∀ n, An n ≠ 0 := by
    intro n h
    have h' : (A : ℝ) * p1 n ^ 2 + B * p1 n * q1 n + C * q1 n ^ 2 = 0 := by
      have := congrArg (fun z : ℤ ↦ (z : ℝ)) h
      simpa [hAn] using this
    have hq : (0 : ℝ) < q1 n := by exact_mod_cast hq1pos n
    have hfac : (x * q1 n - p1 n) * (A * (x * q1 n + p1 n) + B * q1 n) = 0 := by
      linear_combination (q1 n : ℝ) ^ 2 * hquad - h'
    rcases mul_eq_zero.mp hfac with h1 | h1
    · exact hirr ⟨p1 n / q1 n, by push_cast; field_simp; linarith⟩
    · apply hirr
      refine ⟨(-B * q1 n - A * p1 n) / (A * q1 n), ?_⟩
      have hA' : (A : ℝ) ≠ 0 := by exact_mod_cast hA
      push_cast
      field_simp
      linear_combination -h1
  -- the bounds `|Aₙ|, |Cₙ| ≤ K = |2Ax + B| + |A|`
  set K : ℝ := |2 * (A : ℝ) * x + B| + |(A : ℝ)| with hK
  have hbound : ∀ (p q : ℤ), 0 < q → |(q : ℝ) * x - p| * q ≤ 1 → |(q : ℝ) * x - p| ≤ 1 →
      |(A * p ^ 2 + B * p * q + C * q ^ 2 : ℝ)| ≤ K := by
    intro p q _ h1 h2
    set e : ℝ := p - q * x
    have hexp : (A * p ^ 2 + B * p * q + C * q ^ 2 : ℝ) =
        q ^ 2 * (A * x ^ 2 + B * x + C) + e * q * (2 * A * x + B) + A * e ^ 2 := by
      simp only [e]; ring
    rw [hexp, hquad, mul_zero, zero_add]
    have he1 : |e * q| ≤ 1 := by
      rw [abs_mul, abs_of_pos (show (0 : ℝ) < q by exact_mod_cast ‹0 < q›)]
      simpa [e, abs_sub_comm] using h1
    have he2 : |e| ^ 2 ≤ 1 := by
      have : |e| ≤ 1 := by simpa [e, abs_sub_comm] using h2
      nlinarith [abs_nonneg e]
    calc |e * q * (2 * A * x + B) + A * e ^ 2| ≤ |e * q * (2 * A * x + B)| + |A * e ^ 2| :=
          abs_add_le _ _
      _ = |e * q| * |2 * A * x + B| + |(A : ℝ)| * |e| ^ 2 := by
          rw [abs_mul (e * q), abs_mul (A : ℝ), abs_pow]
      _ ≤ 1 * |2 * A * x + B| + |(A : ℝ)| * 1 := by
          gcongr
      _ = K := by ring
  -- the error estimates `|qₖ x - pₖ| qₖ < 1` and `|qₖ x - pₖ| < 1`
  have herr : ∀ k, |(cf (fun i ↦ (a i : ℝ))).dens k * x - (cf (fun i ↦ (a i : ℝ))).nums k| *
      (cf (fun i ↦ (a i : ℝ))).dens k ≤ 1 ∧
      |(cf (fun i ↦ (a i : ℝ))).dens k * x - (cf (fun i ↦ (a i : ℝ))).nums k| ≤ 1 := by
    intro k
    obtain ⟨D, hD1, -, -, e2⟩ := cf_sub_convs_eq ha hx k
    have hq := cf_dens_one_le (pos_finZ ha (k + 1)) k (by omega)
    have hmono := (cf_dens_le_dens_succ (pos_finZ ha (k + 1)) (n := k) le_rfl).1
    rw [e2, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos (by linarith)]
    constructor
    · rw [div_mul_eq_mul_div, one_mul, div_le_one (by linarith)]; linarith
    · rw [div_le_one (by linarith)]; linarith
  have hAb : ∀ n, |(An n : ℝ)| ≤ K := by
    intro n
    have := herr (n + 1)
    rw [hp1 n, hq1 n] at this
    have h := hbound (p1 n) (q1 n) (hq1pos n) this.1 this.2
    simpa [hAn] using h
  have hCb : ∀ n, |(Cn n : ℝ)| ≤ K := by
    intro n
    have := herr n
    rw [hp0 n, hq0 n] at this
    have h := hbound (p0 n) (q0 n) (hq0pos n) this.1 this.2
    simpa [hCn] using h
  -- the discriminant is invariant
  have hdisc : ∀ n, Bn n ^ 2 - 4 * An n * Cn n = B ^ 2 - 4 * A * C := by
    intro n
    have h1 : Bn n ^ 2 - 4 * An n * Cn n =
        (B ^ 2 - 4 * A * C) * (p1 n * q0 n - p0 n * q1 n) ^ 2 := by
      simp only [hAn, hBn, hCn]; ring
    rw [h1, hdet n, ← pow_mul, mul_comm n 2, pow_mul]
    simp
  -- integer bounds
  obtain ⟨M, hM⟩ : ∃ M : ℕ, K ≤ M := exists_nat_ge K
  have hAbZ : ∀ n, |An n| ≤ M := fun n ↦ by
    have := (hAb n).trans hM; exact_mod_cast this
  have hCbZ : ∀ n, |Cn n| ≤ M := fun n ↦ by
    have := (hCb n).trans hM; exact_mod_cast this
  set M2 : ℤ := 4 * M ^ 2 + |B ^ 2 - 4 * A * C| with hM2
  have hBbZ : ∀ n, |Bn n| ≤ M2 := by
    intro n
    have h1 : Bn n ^ 2 ≤ M2 := by
      have := hdisc n
      have h2 : |An n * Cn n| ≤ M ^ 2 := by
        rw [abs_mul, sq]; exact mul_le_mul (hAbZ n) (hCbZ n) (abs_nonneg _) (by positivity)
      have h3 := le_abs_self (B ^ 2 - 4 * A * C)
      have h4 := le_abs_self (An n * Cn n)
      nlinarith
    have h5 : |Bn n| ≤ Bn n ^ 2 := by
      rcases eq_or_ne (Bn n) 0 with h | h
      · simp [h]
      · rw [← sq_abs]; nlinarith [Int.one_le_abs h]
    linarith
  -- pigeonhole
  set box : Finset (ℤ × ℤ × ℤ) :=
    Finset.Icc (-(M : ℤ)) M ×ˢ Finset.Icc (-M2) M2 ×ˢ Finset.Icc (-(M : ℤ)) M with hbox
  have hmem : ∀ n, (An n, Bn n, Cn n) ∈ box := by
    intro n
    simp only [hbox, Finset.mem_product, Finset.mem_Icc]
    exact ⟨abs_le.mp (hAbZ n), abs_le.mp (hBbZ n), abs_le.mp (hCbZ n)⟩
  let f : ℕ → box := fun n ↦ ⟨(An n, Bn n, Cn n), hmem n⟩
  obtain ⟨t, ht⟩ := Finite.exists_infinite_fiber f
  have hS : (f ⁻¹' {t}).Infinite := Set.infinite_coe_iff.mp ht
  obtain ⟨n1, hn1, -⟩ := hS.exists_gt 0
  obtain ⟨n2, hn2, h12⟩ := hS.exists_gt n1
  obtain ⟨n3, hn3, h23⟩ := hS.exists_gt n2
  simp only [Set.mem_preimage, Set.mem_singleton_iff, f] at hn1 hn2 hn3
  have e12 := congrArg Subtype.val (hn1.trans hn2.symm)
  have e13 := congrArg Subtype.val (hn1.trans hn3.symm)
  simp only [Prod.mk.injEq] at e12 e13
  obtain ⟨hA2, hB2, hC2⟩ := e12
  obtain ⟨hA3, hB3, hC3⟩ := e13
  have r1 := heq n1
  have r2 := heq n2
  have r3 := heq n3
  rw [← hA2, ← hB2, ← hC2] at r2
  rw [← hA3, ← hB3, ← hC3] at r3
  have hA1 : (An n1 : ℝ) ≠ 0 := by exact_mod_cast hAn0 n1
  -- two of the complete quotients coincide, hence the continued fraction is periodic
  have key : ∀ i j, i < j → α i = α j → IsPeriodic a := by
    intro i j hij hαij
    have htail := cf_eq_of_tendsto (fun t ht ↦ ha (i + 2 + t) (by omega))
      (fun t ht ↦ ha (j + 2 + t) (by omega)) (hα i) (hαij ▸ hα j)
    refine ⟨i + 2, j - i, by omega, fun l hl ↦ ?_⟩
    have := congrFun htail (l - (i + 2))
    rw [show i + 2 + (l - (i + 2)) = l by omega, show j + 2 + (l - (i + 2)) = l + (j - i) by omega]
      at this
    exact this.symm
  rcases three_roots hA1 r1 r2 r3 with h | h | h
  · exact key n1 n2 h12 h
  · exact key n1 n3 (h12.trans h23) h
  · exact key n2 n3 h23 h

/-- **§ 10.13** (Hardy–Wright (10.13.5) to (10.13.7)). If `a, c` are positive integers and `b = ac`, the
periodic continued fraction `x = [b, a, b, a, …]` satisfies `x² - bx - c = 0`, so
`x = (b + √(b² + 4c))/2`. -/
@[kb "hardywright2008" "§ 10.13, p. 188"]
theorem cf_alternating_value {a c : ℤ} (ha : 0 < a) (hc : 0 < c) {x : ℝ}
    (hx : Tendsto (fun t ↦ (cf (fun i ↦ ((if Even i then a * c else a : ℤ) : ℝ))).convs t) atTop
      (𝓝 x)) :
    x ^ 2 - (a * c) * x - c = 0 ∧ x = (a * c + √((a * c) ^ 2 + 4 * c)) / 2 := by
  set q : ℕ → ℤ := fun i ↦ if Even i then a * c else a with hq
  have hqpos : ∀ i, 1 ≤ i → 0 < q i := fun i _ ↦ by
    simp only [hq]; split_ifs <;> positivity
  have htail : (fun i ↦ ((q (1 + 1 + i) : ℤ) : ℝ)) = fun i ↦ ((q i : ℤ) : ℝ) := by
    funext i; simp only [hq, show 1 + 1 + i = i + 2 by ring, Nat.even_add, even_two, iff_true]
  have hy : Tendsto (fun t ↦ (cf (fun i ↦ ((q (1 + 1 + i) : ℤ) : ℝ))).convs t) atTop (𝓝 x) := by
    rw [htail]; exact hx
  have e := cf_value_eq_completeQuotient hqpos hx 1 hy
  rw [← nth_cont_eq_succ_nth_contAux, ← nth_cont_eq_succ_nth_contAux, ← num_eq_conts_a,
    ← num_eq_conts_a, ← den_eq_conts_b, ← den_eq_conts_b] at e
  simp only [cf_nums_one, cf_dens_one, cf_nums_zero, cf_dens_zero, hq, Even.zero, ite_true,
    show ¬Even 1 from Nat.not_even_one, ite_false] at e
  push_cast at e
  have hx0 : (a * c : ℝ) < x := by
    have := (cf_value_mem_Ioo hqpos hx).1
    simpa [hq] using this
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hcr : (0 : ℝ) < c := by exact_mod_cast hc
  have hxpos : 0 < x := by nlinarith
  have hden : 0 < x * a + 1 := add_pos (mul_pos hxpos har) one_pos
  have hquad : x ^ 2 - (a * c) * x - c = 0 := by
    rw [eq_div_iff hden.ne'] at e
    have : (a : ℝ) * (x ^ 2 - (a * c) * x - c) = 0 := by linear_combination e
    exact (mul_eq_zero.mp this).resolve_left har.ne'
  refine ⟨hquad, ?_⟩
  -- the positive root
  have hD : (0 : ℝ) ≤ (a * c) ^ 2 + 4 * c := by positivity
  have hs := Real.sq_sqrt hD
  have hs0 := Real.sqrt_nonneg ((a * c : ℝ) ^ 2 + 4 * c)
  have hfac : (x - (a * c + √((a * c) ^ 2 + 4 * c)) / 2) *
      (x - (a * c - √((a * c) ^ 2 + 4 * c)) / 2) = 0 := by
    linear_combination hquad + (-1 / 4 : ℝ) * hs
  rcases mul_eq_zero.mp hfac with h | h
  · linarith
  · exfalso
    have : x = (a * c - √((a * c) ^ 2 + 4 * c)) / 2 := by linarith
    have hac : (0 : ℝ) < a * c := by positivity
    nlinarith

end NTKB.HardyWright
