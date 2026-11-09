/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.ContinuedFractions.Simple
import Mathlib.NumberTheory.DiophantineApproximation.ContinuedFractions
import Mathlib.Algebra.ContinuedFractions.Computation.ApproximationCorollaries
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Cauchy

/-!
# Infinite simple continued fractions (Hardy–Wright, Chapter X, §§ 10.8 and 10.9)

For integers `a₀, a₁, …` with `aₙ > 0` for `n ≥ 1`, the convergents `xₙ = [a₀, …, aₙ]` tend to a limit
`x`, the value `[a₀, a₁, …]` of the infinite simple continued fraction. We express "`[a₀, a₁, …] = x`" as
`Tendsto (fun n ↦ (cf (fun i ↦ (a i : ℝ))).convs n) atTop (𝓝 x)`; the `n`-th complete quotient
`a'ₙ = [aₙ, a_{n+1}, …]` is the value of the continued fraction with quotients `fun i ↦ a (n + i)`.

* Theorems 165 and 166: every infinite simple continued fraction converges.
* Theorem 167: its value is greater than every even and less than every odd convergent.
* Theorem 168: if `[a₀, a₁, …] = x` then `a₀ = ⌊x⌋` and `aₙ = ⌊a'ₙ⌋`.
* Theorem 169: two infinite simple continued fractions with the same value are identical.
* Theorem 170: every irrational number is the value of exactly one infinite simple continued fraction, and
  the value of an infinite simple continued fraction is irrational.
* Theorem 171: `x = (a'_{n+1} pₙ + pₙ₋₁)/(a'_{n+1} qₙ + qₙ₋₁)`, the bounds
  `1/(qₙ(qₙ₊₁ + qₙ)) < |x - pₙ/qₙ| < 1/(qₙ qₙ₊₁) ≤ 1/qₙ²`, and the strict decrease of `|qₙ x - pₙ|` and of
  `|x - pₙ/qₙ|`.
-/

namespace NTKB.HardyWright

open GenContFract Filter Topology

/-! ### Splitting a continued fraction after the `n`-th quotient -/

section Split

variable {K : Type*} [Field K]

/-- `[a₀, …, a_{n+1+k}]` in terms of `[a_{n+1}, …, a_{n+1+k}]`: with `C m = contsAux m` (so `C (n + 1) =
(pₙ, qₙ)` and `C n = (pₙ₋₁, qₙ₋₁)`), `C (n + 2 + k) = P · C (n + 1) + Q · C n` where `P/Q` is the `k`-th
convergent of the tail. -/
lemma cf_contsAux_split (a : ℕ → K) (n k : ℕ) :
    ((cf a).contsAux (n + 2 + k)).a =
        (cf fun i ↦ a (n + 1 + i)).nums k * ((cf a).contsAux (n + 1)).a +
          (cf fun i ↦ a (n + 1 + i)).dens k * ((cf a).contsAux n).a ∧
      ((cf a).contsAux (n + 2 + k)).b =
        (cf fun i ↦ a (n + 1 + i)).nums k * ((cf a).contsAux (n + 1)).b +
          (cf fun i ↦ a (n + 1 + i)).dens k * ((cf a).contsAux n).b := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ =>
      rw [add_zero, cf_contsAux_add_two]
      simp
    | 1, _ =>
      rw [show n + 2 + 1 = (n + 1) + 2 by ring, cf_contsAux_add_two, show n + 1 + 1 = n + 2 by ring,
        cf_contsAux_add_two]
      simp only [cf_nums_one, cf_dens_one, add_zero]
      rw [show n + 1 + 1 = n + 2 by ring]
      constructor <;> ring
    | k + 2, ih =>
      obtain ⟨h1, h1'⟩ := ih (k + 1) (by omega)
      obtain ⟨h0, h0'⟩ := ih k (by omega)
      rw [show n + 2 + (k + 2) = (n + k + 2) + 2 by ring, cf_contsAux_add_two,
        show n + k + 2 + 1 = n + 2 + (k + 1) by ring, show n + k + 2 = n + 2 + k by ring, h1, h1', h0,
        h0', cf_nums_add_two (fun i ↦ a (n + 1 + i)) k, cf_dens_add_two (fun i ↦ a (n + 1 + i)) k,
        show n + 2 + (k + 1) = n + 1 + (k + 2) by ring]
      constructor <;> ring

/-- `pₙ qₙ₋₁ - pₙ₋₁ qₙ = (-1)ⁿ⁻¹` in terms of `contsAux` (valid also for `n = 0`, with `p₋₁ = 1`,
`q₋₁ = 0`). -/
lemma cf_contsAux_det (a : ℕ → K) (n : ℕ) :
    ((cf a).contsAux n).a * ((cf a).contsAux (n + 1)).b -
      ((cf a).contsAux n).b * ((cf a).contsAux (n + 1)).a = (-1) ^ n := by
  induction n with
  | zero => simp [zeroth_contAux_eq_one_zero, first_contAux_eq_h_one]
  | succ n ih =>
    rw [cf_contsAux_add_two, pow_succ, ← ih]
    simp only
    ring

end Split

/-! ### Convergence -/

section Convergence

variable {a : ℕ → ℤ}

/-- Positivity hypothesis of the finite theory, from that of the infinite one. -/
lemma pos_fin (ha : ∀ i, 1 ≤ i → 0 < a i) (N : ℕ) : ∀ i, 1 ≤ i → i ≤ N → (0 : ℝ) < a i :=
  fun i h _ ↦ by exact_mod_cast ha i h

lemma pos_finZ (ha : ∀ i, 1 ≤ i → 0 < a i) (N : ℕ) : ∀ i, 1 ≤ i → i ≤ N → 0 < a i :=
  fun i h _ ↦ ha i h

lemma shift_eq (a : ℕ → ℤ) (n : ℕ) :
    (fun i ↦ ((a (n + (i + 1)) : ℤ) : ℝ)) = fun i ↦ ((a (n + 1 + i) : ℤ) : ℝ) := by
  funext i; rw [show n + (i + 1) = n + 1 + i by ring]

/-- After an even convergent `x₂ⱼ`, all later convergents lie in `[x₂ⱼ, x₂ⱼ₊₁]`. -/
lemma convs_between_even (ha : ∀ i, 1 ≤ i → 0 < a i) {j m : ℕ} (h : 2 * j ≤ m) :
    (cf (fun i ↦ (a i : ℝ))).convs (2 * j) ≤ (cf (fun i ↦ (a i : ℝ))).convs m ∧ (cf (fun i ↦ (a i : ℝ))).convs m ≤ (cf (fun i ↦ (a i : ℝ))).convs (2 * j + 1) := by
  have hp := pos_fin ha (m + 2 * j + 2)
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' m
  · exact ⟨cf_convs_even_le hp (by omega) (by omega),
      (cf_convs_even_lt_odd hp (by omega) (by omega)).le⟩
  · exact ⟨(cf_convs_even_lt_odd hp (by omega) (by omega)).le,
      cf_convs_odd_le hp (by omega) (by omega)⟩

/-- After an odd convergent `x₂ⱼ₊₁`, all later convergents lie in `[x₂ⱼ₊₂, x₂ⱼ₊₁]`. -/
lemma convs_between_odd (ha : ∀ i, 1 ≤ i → 0 < a i) {j m : ℕ} (h : 2 * j + 1 ≤ m) :
    (cf (fun i ↦ (a i : ℝ))).convs (2 * j + 2) ≤ (cf (fun i ↦ (a i : ℝ))).convs m ∧ (cf (fun i ↦ (a i : ℝ))).convs m ≤ (cf (fun i ↦ (a i : ℝ))).convs (2 * j + 1) := by
  have hp := pos_fin ha (m + 2 * j + 3)
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' m
  · refine ⟨?_, (cf_convs_even_lt_odd hp (by omega) (by omega)).le⟩
    have := cf_convs_even_le hp (m := j + 1) (n := i) (by omega) (by omega)
    rwa [show 2 * (j + 1) = 2 * j + 2 by ring] at this
  · refine ⟨?_, cf_convs_odd_le hp (by omega) (by omega)⟩
    have := cf_convs_even_lt_odd hp (m := j + 1) (n := i) (by omega) (by omega)
    rw [show 2 * (j + 1) = 2 * j + 2 by ring] at this
    exact this.le

/-- `|xₙ₊₁ - xₙ| = 1/(qₙ qₙ₊₁)`. -/
lemma abs_convs_succ_sub (ha : ∀ i, 1 ≤ i → 0 < a i) (n : ℕ) :
    |(cf (fun i ↦ (a i : ℝ))).convs (n + 1) - (cf (fun i ↦ (a i : ℝ))).convs n| =
      1 / ((cf (fun i ↦ (a i : ℝ))).dens n * (cf (fun i ↦ (a i : ℝ))).dens (n + 1)) := by
  have hp := pos_fin ha (n + 1)
  rw [cf_convs_succ_sub hp le_rfl, abs_div, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_pos (mul_pos (cf_dens_pos hp n (by omega)) (cf_dens_pos hp (n + 1) le_rfl))]

/-- For `n ≤ m`, `|xₘ - xₙ| ≤ 1/(qₙ qₙ₊₁)`. -/
lemma abs_convs_sub_le (ha : ∀ i, 1 ≤ i → 0 < a i) {n m : ℕ} (h : n ≤ m) :
    |(cf (fun i ↦ (a i : ℝ))).convs m - (cf (fun i ↦ (a i : ℝ))).convs n| ≤
      1 / ((cf (fun i ↦ (a i : ℝ))).dens n * (cf (fun i ↦ (a i : ℝ))).dens (n + 1)) := by
  rw [← abs_convs_succ_sub ha n]
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
  · obtain ⟨h1, h2⟩ := convs_between_even ha h
    obtain ⟨-, h3⟩ := convs_between_even ha (le_refl (2 * j))
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · obtain ⟨h1, h2⟩ := convs_between_odd ha h
    obtain ⟨h3, -⟩ := convs_between_odd ha (le_refl (2 * j + 1))
    have h4 := convs_between_odd ha (le_refl (2 * j + 1))
    have h5 : (cf (fun i ↦ (a i : ℝ))).convs (2 * j + 2) ≤ (cf (fun i ↦ (a i : ℝ))).convs (2 * j + 1) := h4.1.trans h4.2
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith

/-- **Theorem 165.** If `a₀, a₁, …` are integers with `aₙ > 0` for `n ≥ 1`, the convergents
`xₙ = [a₀, …, aₙ]` tend to a limit. -/
@[kb "hardywright2008" "Thm 165, p. 177"]
theorem cf_convs_tendsto (ha : ∀ i, 1 ≤ i → 0 < a i) : ∃ x : ℝ, Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 x) := by
  refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff'.mpr fun ε hε ↦ ?_)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, fun m hm ↦ ?_⟩
  rw [Real.dist_eq]
  refine (abs_convs_sub_le ha hm).trans_lt ?_
  have hp := pos_finZ ha (N + 1)
  have h1 := cf_dens_one_le hp N (by omega)
  have h2 := (cf_le_dens hp (n := N + 1) le_rfl).1
  push_cast at h2
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
  rw [div_lt_iff₀ (mul_pos (by linarith) (by linarith))]
  rw [div_lt_iff₀ hε] at hN
  have : (N : ℝ) + 1 ≤ (cf fun i ↦ (a i : ℝ)).dens N * (cf fun i ↦ (a i : ℝ)).dens (N + 1) := by
    nlinarith
  nlinarith

/-- **Theorem 166.** All infinite simple continued fractions are convergent. -/
@[kb "hardywright2008" "Thm 166, p. 177"]
theorem cf_convergent (ha : ∀ i, 1 ≤ i → 0 < a i) : ∃ x : ℝ, Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 x) :=
  cf_convs_tendsto ha

/-- **Theorem 167.** An infinite simple continued fraction is less than any of its odd convergents and
greater than any of its even convergents. -/
@[kb "hardywright2008" "Thm 167, p. 178"]
theorem cf_even_lt_value_lt_odd (ha : ∀ i, 1 ≤ i → 0 < a i) {x : ℝ} (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 x))
    (n : ℕ) : (cf (fun i ↦ (a i : ℝ))).convs (2 * n) < x ∧ x < (cf (fun i ↦ (a i : ℝ))).convs (2 * n + 1) := by
  have hp := pos_fin ha (2 * n + 3)
  constructor
  · have h1 : (cf (fun i ↦ (a i : ℝ))).convs (2 * (n + 1)) ≤ x :=
      ge_of_tendsto hx (eventually_atTop.mpr ⟨2 * (n + 1), fun m hm ↦ (convs_between_even ha hm).1⟩)
    exact (cf_convs_even_lt hp (lt_add_one n) (by omega)).trans_le h1
  · have h1 : x ≤ (cf (fun i ↦ (a i : ℝ))).convs (2 * (n + 1) + 1) :=
      le_of_tendsto hx (eventually_atTop.mpr ⟨2 * (n + 1) + 1, fun m hm ↦
        (convs_between_odd ha (j := n + 1) hm).2⟩)
    exact h1.trans_lt (cf_convs_odd_lt hp (lt_add_one n) (by omega))

/-- The value of an infinite simple continued fraction lies strictly between `a₀` and `a₀ + 1`. -/
lemma cf_value_mem_Ioo (ha : ∀ i, 1 ≤ i → 0 < a i) {x : ℝ} (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 x)) :
    (a 0 : ℝ) < x ∧ x < a 0 + 1 := by
  obtain ⟨h0, h1⟩ := cf_even_lt_value_lt_odd ha hx 0
  simp only [mul_zero, cf_convs_zero, zero_add] at h0 h1
  refine ⟨h0, h1.trans_le ?_⟩
  rw [cf_convs]
  simp only [cf_nums_one, cf_dens_one]
  have ha1 : (1 : ℝ) ≤ a 1 := by exact_mod_cast ha 1 le_rfl
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- If `[a₀, a₁, …] = x` then `[a₁, a₂, …] = 1/(x - a₀)`, i.e. `x = a₀ + 1/a'₁`. -/
lemma cf_tendsto_tail (ha : ∀ i, 1 ≤ i → 0 < a i) {x : ℝ} (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 x)) :
    Tendsto (fun t ↦ (cf (fun i ↦ ((a (i + 1) : ℤ) : ℝ))).convs t) atTop (𝓝 (1 / (x - a 0))) := by
  have hx0 := (cf_value_mem_Ioo ha hx).1
  have e : ∀ k, (cf (fun i ↦ ((a (i + 1) : ℤ) : ℝ))).convs k = 1 / ((cf (fun i ↦ (a i : ℝ))).convs (k + 1) - a 0) := by
    intro k
    rw [cf_value_succ (pos_finZ ha (k + 1))]
    simp
  simp_rw [e]
  refine Tendsto.div tendsto_const_nhds ?_ (by linarith)
  exact ((hx.comp (tendsto_add_atTop_nat 1)).sub tendsto_const_nhds)

/-- **Theorem 168.** If `[a₀, a₁, …] = x` then `a₀ = ⌊x⌋`, and `aₙ = ⌊a'ₙ⌋` for the complete quotients
`a'ₙ = [aₙ, a_{n+1}, …]`. -/
@[kb "hardywright2008" "Thm 168, p. 178"]
theorem cf_floor_value_eq (ha : ∀ i, 1 ≤ i → 0 < a i) {x : ℝ} (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 x)) :
    ⌊x⌋ = a 0 ∧ ∀ n (y : ℝ), Tendsto (fun t ↦ (cf (fun i ↦ ((a (n + i) : ℤ) : ℝ))).convs t) atTop (𝓝 y) → ⌊y⌋ = a n := by
  have key : ∀ (b : ℕ → ℤ), (∀ i, 1 ≤ i → 0 < b i) → ∀ y : ℝ, Tendsto (fun t ↦ (cf (fun i ↦ (b i : ℝ))).convs t) atTop (𝓝 y) →
      ⌊y⌋ = b 0 := by
    intro b hb y hy
    obtain ⟨h0, h1⟩ := cf_value_mem_Ioo hb hy
    rw [Int.floor_eq_iff]
    exact ⟨h0.le, h1⟩
  refine ⟨key a ha x hx, fun n y hy ↦ ?_⟩
  have := key (fun i ↦ a (n + i)) (fun i hi ↦ ha (n + i) (by omega)) y hy
  simpa using this

/-- **Theorem 169.** Two infinite simple continued fractions which have the same value are identical. -/
@[kb "hardywright2008" "Thm 169, p. 178"]
theorem cf_eq_of_tendsto {a b : ℕ → ℤ} (ha : ∀ i, 1 ≤ i → 0 < a i) (hb : ∀ i, 1 ≤ i → 0 < b i)
    {x : ℝ} (hxa : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 x)) (hxb : Tendsto (fun t ↦ (cf (fun i ↦ (b i : ℝ))).convs t) atTop (𝓝 x)) : a = b := by
  have key : ∀ n, ∃ y : ℝ, Tendsto (fun t ↦ (cf (fun i ↦ ((a (n + i) : ℤ) : ℝ))).convs t) atTop (𝓝 y) ∧
      Tendsto (fun t ↦ (cf (fun i ↦ ((b (n + i) : ℤ) : ℝ))).convs t) atTop (𝓝 y) := by
    intro n
    induction n with
    | zero => exact ⟨x, by simpa using hxa, by simpa using hxb⟩
    | succ n ih =>
      obtain ⟨y, hya, hyb⟩ := ih
      have hea := (cf_floor_value_eq (fun i hi ↦ ha (n + i) (by omega)) hya).1
      have heb := (cf_floor_value_eq (fun i hi ↦ hb (n + i) (by omega)) hyb).1
      simp only [add_zero] at hea heb
      have ta := cf_tendsto_tail (fun i hi ↦ ha (n + i) (by omega)) hya
      have tb := cf_tendsto_tail (fun i hi ↦ hb (n + i) (by omega)) hyb
      simp only [add_zero] at ta tb
      rw [← hea, heb] at ta
      rw [shift_eq] at ta tb
      exact ⟨_, ta, tb⟩
  funext n
  obtain ⟨y, hya, hyb⟩ := key n
  have h1 := (cf_floor_value_eq (fun i hi ↦ ha (n + i) (by omega)) hya).1
  have h2 := (cf_floor_value_eq (fun i hi ↦ hb (n + i) (by omega)) hyb).1
  simp only [add_zero] at h1 h2
  rw [← h1, ← h2]

/-! ### Theorem 170 -/

/-- The quotients produced by the continued fraction algorithm (auxiliary; it is Mathlib's
`Real.convergent` recursion read off at the level of quotients). -/
private noncomputable def quot : ℝ → ℕ → ℤ
  | ξ, 0 => ⌊ξ⌋
  | ξ, n + 1 => quot (Int.fract ξ)⁻¹ n

private lemma quot_pos : ∀ (n : ℕ) (ξ : ℝ), Irrational ξ → 0 < quot ξ (n + 1) := by
  intro n
  induction n with
  | zero =>
    intro ξ hξ
    have hf0 : Int.fract ξ ≠ 0 := by
      rw [Int.fract, sub_ne_zero]; exact hξ.ne_int _
    have h0 : 0 < Int.fract ξ := lt_of_le_of_ne (Int.fract_nonneg ξ) (Ne.symm hf0)
    have h1 : 1 < (Int.fract ξ)⁻¹ := one_lt_inv₀ h0 |>.mpr (Int.fract_lt_one ξ)
    show 0 < ⌊(Int.fract ξ)⁻¹⌋
    exact Int.floor_pos.mpr h1.le
  | succ n ih =>
    intro ξ hξ
    exact ih _ (by
      rw [Int.fract]
      exact (Irrational.sub_intCast hξ _).inv)

private lemma quot_convs : ∀ (n : ℕ) (ξ : ℝ), Irrational ξ →
    (cf (fun i ↦ (quot ξ i : ℝ))).convs n = ξ.convergent n := by
  intro n
  induction n with
  | zero => intro ξ _; simp [quot]
  | succ n ih =>
    intro ξ hξ
    have hξ' : Irrational (Int.fract ξ)⁻¹ := by rw [Int.fract]; exact (Irrational.sub_intCast hξ _).inv
    rw [cf_value_succ (fun i h1 _ ↦ by
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      exact quot_pos j ξ hξ)]
    have : (fun i ↦ (quot ξ (i + 1) : ℝ)) = fun i ↦ (quot (Int.fract ξ)⁻¹ i : ℝ) := rfl
    rw [this, ih _ hξ', Real.convergent_succ]
    simp [quot]

private lemma quot_tendsto (x : ℝ) (hx : Irrational x) :
    Tendsto (fun t ↦ (cf (fun i ↦ (quot x i : ℝ))).convs t) atTop (𝓝 x) := by
  have h := GenContFract.of_convergence (K := ℝ) x
  have e : (fun t ↦ (cf (fun i ↦ (quot x i : ℝ))).convs t) = fun t ↦ (GenContFract.of x).convs t := by
    funext t; rw [quot_convs t x hx, Real.convs_eq_convergent]
  rw [e]; exact h

/-- **Theorem 170.** Every irrational number can be expressed in just one way as an infinite simple
continued fraction; and the value of an infinite simple continued fraction is irrational. -/
@[kb "hardywright2008" "Thm 170, p. 179"]
theorem irrational_iff_exists_unique_cf (x : ℝ) :
    (Irrational x → ∃! a : ℕ → ℤ, (∀ i, 1 ≤ i → 0 < a i) ∧ Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 x)) ∧
      ∀ a : ℕ → ℤ, (∀ i, 1 ≤ i → 0 < a i) → Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 x) → Irrational x := by
  refine ⟨fun hx ↦ ⟨quot x, ⟨fun i hi ↦ ?_, ?_⟩, fun b ⟨hb, hbx⟩ ↦ ?_⟩, fun a ha hax ↦ ?_⟩
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    exact quot_pos j x hx
  · exact quot_tendsto x hx
  · refine cf_eq_of_tendsto hb (fun i hi ↦ ?_) hbx ?_
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      exact quot_pos j x hx
    · exact quot_tendsto x hx
  · -- Hardy–Wright: the algorithm would terminate if `x` were rational
    rintro ⟨q₀, rfl⟩
    have key : ∀ n, ∃ q : ℚ, Tendsto (fun t ↦ (cf (fun i ↦ ((a (n + i) : ℤ) : ℝ))).convs t) atTop (𝓝 (q : ℝ)) ∧
        q.den + n ≤ q₀.den := by
      intro n
      induction n with
      | zero => exact ⟨q₀, by simpa using hax, by simp⟩
      | succ n ih =>
        obtain ⟨q, hq, hqd⟩ := ih
        have han : ∀ i, 1 ≤ i → 0 < a (n + i) := fun i hi ↦ ha (n + i) (by omega)
        obtain ⟨h0, h1⟩ := cf_value_mem_Ioo han hq
        simp only [add_zero] at h0 h1
        have hfl : ⌊q⌋ = a n := by
          rw [← Rat.floor_cast (α := ℝ), Int.floor_eq_iff]; exact ⟨h0.le, h1⟩
        have hf : Int.fract q = q - a n := by rw [Int.fract, hfl]
        have hf0 : 0 < Int.fract q := by
          rw [hf]; exact_mod_cast (show ((a n : ℚ) : ℝ) < q by exact_mod_cast h0) |> sub_pos.mpr
        refine ⟨(Int.fract q)⁻¹, ?_, ?_⟩
        · have := cf_tendsto_tail han hq
          simp only [add_zero] at this
          rw [shift_eq] at this
          convert this using 2
          rw [hf]; push_cast; rw [one_div]
        · have hd := Rat.den_inv_of_ne_zero hf0.ne'
          have h1 := Rat.num_lt_denom_iff.mpr (Int.fract_lt_one q)
          have h2 : 0 < (Int.fract q).num := Rat.num_pos.mpr hf0
          rw [Rat.den_intFract] at h1
          omega
    obtain ⟨q, -, hq⟩ := key (q₀.den + 1)
    have := q.den_pos
    omega

/-- The convergents of the infinite simple continued fraction of `x` are Mathlib's `Real.convergent`s. -/
theorem cf_convs_eq_convergent {a : ℕ → ℤ} (ha : ∀ i, 1 ≤ i → 0 < a i) {x : ℝ}
    (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 x)) (n : ℕ) :
    (cf (fun i ↦ (a i : ℝ))).convs n = x.convergent n := by
  have hirr := (irrational_iff_exists_unique_cf x).2 a ha hx
  have hq : ∀ i, 1 ≤ i → 0 < quot x i := fun i hi ↦ by
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    exact quot_pos j x hirr
  rw [cf_eq_of_tendsto ha hq hx (quot_tendsto x hirr), quot_convs n x hirr]

/-! ### Theorem 171 -/

/-- The complete quotient formula `x = (a'_{n+1} pₙ + pₙ₋₁)/(a'_{n+1} qₙ + qₙ₋₁)` for an infinite simple
continued fraction (Hardy–Wright (10.5.1) and § 10.9), with `(pₙ, qₙ) = contsAux (n + 1)` and
`(pₙ₋₁, qₙ₋₁) = contsAux n`. -/
theorem cf_value_eq_completeQuotient (ha : ∀ i, 1 ≤ i → 0 < a i) {x : ℝ}
    (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 x)) (n : ℕ) {y : ℝ}
    (hy : Tendsto (fun t ↦ (cf (fun i ↦ ((a (n + 1 + i) : ℤ) : ℝ))).convs t) atTop (𝓝 y)) :
    x = (y * ((cf (fun i ↦ (a i : ℝ))).contsAux (n + 1)).a +
          ((cf (fun i ↦ (a i : ℝ))).contsAux n).a) /
        (y * ((cf (fun i ↦ (a i : ℝ))).contsAux (n + 1)).b +
          ((cf (fun i ↦ (a i : ℝ))).contsAux n).b) := by
  set C := (cf (fun i ↦ (a i : ℝ))).contsAux
  have hpt : ∀ i, 1 ≤ i → 0 < a (n + 1 + i) := fun i hi ↦ ha (n + 1 + i) (by omega)
  have hy1 : 1 ≤ y := by
    have := (cf_value_mem_Ioo hpt hy).1
    have h : (1 : ℝ) ≤ a (n + 1 + 0) := by exact_mod_cast ha (n + 1 + 0) (by omega)
    linarith
  -- `C (n + 1) = (pₙ, qₙ)`, `qₙ > 0`, `qₙ₋₁ ≥ 0`
  have hqn : 0 < (C (n + 1)).b := by
    have := cf_dens_pos (pos_fin ha n) n le_rfl
    rwa [den_eq_conts_b, nth_cont_eq_succ_nth_contAux] at this
  have hqn1 : 0 ≤ (C n).b := by
    rcases n with _ | n
    · simp [C, zeroth_contAux_eq_one_zero]
    · have := cf_dens_pos (pos_fin ha n) n le_rfl
      rw [den_eq_conts_b, nth_cont_eq_succ_nth_contAux] at this
      exact this.le
  have hden : 0 < y * (C (n + 1)).b + (C n).b := by nlinarith
  -- the finite formula
  have e : ∀ k, (cf (fun i ↦ (a i : ℝ))).convs (n + 1 + k) =
      ((cf (fun i ↦ ((a (n + 1 + i) : ℤ) : ℝ))).convs k * (C (n + 1)).a + (C n).a) /
        ((cf (fun i ↦ ((a (n + 1 + i) : ℤ) : ℝ))).convs k * (C (n + 1)).b + (C n).b) := by
    intro k
    obtain ⟨h1, h2⟩ := cf_contsAux_split (fun i ↦ (a i : ℝ)) n k
    have hQ := cf_dens_pos (pos_fin hpt k) k le_rfl
    rw [cf_convs, num_eq_conts_a, den_eq_conts_b, nth_cont_eq_succ_nth_contAux,
      show n + 1 + k + 1 = n + 2 + k by ring, h1, h2, cf_convs (fun i ↦ (a (n + 1 + i) : ℝ))]
    field_simp
    rfl
  have lim1 : Tendsto (fun k ↦ (cf (fun i ↦ (a i : ℝ))).convs (n + 1 + k)) atTop (𝓝 x) :=
    hx.comp (tendsto_atTop_mono (fun k ↦ Nat.le_add_left k (n + 1)) tendsto_id)
  have lim2 : Tendsto (fun k ↦ ((cf (fun i ↦ ((a (n + 1 + i) : ℤ) : ℝ))).convs k * (C (n + 1)).a + (C n).a) /
      ((cf (fun i ↦ ((a (n + 1 + i) : ℤ) : ℝ))).convs k * (C (n + 1)).b + (C n).b)) atTop
      (𝓝 ((y * (C (n + 1)).a + (C n).a) / (y * (C (n + 1)).b + (C n).b))) := by
    refine Tendsto.div ?_ ?_ hden.ne'
    · exact (hy.mul tendsto_const_nhds).add tendsto_const_nhds
    · exact (hy.mul tendsto_const_nhds).add tendsto_const_nhds
  simp_rw [e] at lim1
  exact tendsto_nhds_unique lim1 lim2

/-- The error of the `n`-th convergent of an infinite simple continued fraction: with
`q'ₙ₊₁ = a'_{n+1} qₙ + qₙ₋₁` (Hardy–Wright § 10.7), `qₙ₊₁ < q'ₙ₊₁ < qₙ₊₁ + qₙ`,
`x - pₙ/qₙ = (-1)ⁿ/(qₙ q'ₙ₊₁)` and `qₙ x - pₙ = (-1)ⁿ/q'ₙ₊₁`. -/
theorem cf_sub_convs_eq (ha : ∀ i, 1 ≤ i → 0 < a i) {x : ℝ}
    (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 x)) (n : ℕ) :
    ∃ D : ℝ, (cf (fun i ↦ (a i : ℝ))).dens (n + 1) < D ∧
      D < (cf (fun i ↦ (a i : ℝ))).dens (n + 1) + (cf (fun i ↦ (a i : ℝ))).dens n ∧
      x - (cf (fun i ↦ (a i : ℝ))).convs n = (-1) ^ n / ((cf (fun i ↦ (a i : ℝ))).dens n * D) ∧
      (cf (fun i ↦ (a i : ℝ))).dens n * x - (cf (fun i ↦ (a i : ℝ))).nums n = (-1) ^ n / D := by
  have hpt : ∀ i, 1 ≤ i → 0 < a (n + 1 + i) := fun i hi ↦ ha (n + 1 + i) (by omega)
  obtain ⟨y, hy⟩ := cf_convs_tendsto hpt
  have e := cf_value_eq_completeQuotient ha hx n hy
  set C := (cf (fun i ↦ (a i : ℝ))).contsAux with hC
  have hP : (cf (fun i ↦ (a i : ℝ))).nums n = (C (n + 1)).a := by
    rw [num_eq_conts_a, nth_cont_eq_succ_nth_contAux]
  have hQ : (cf (fun i ↦ (a i : ℝ))).dens n = (C (n + 1)).b := by
    rw [den_eq_conts_b, nth_cont_eq_succ_nth_contAux]
  have hQ1 : (cf (fun i ↦ (a i : ℝ))).dens (n + 1) = a (n + 1) * (C (n + 1)).b + (C n).b := by
    rw [den_eq_conts_b, nth_cont_eq_succ_nth_contAux, hC, cf_contsAux_add_two]
  have det := cf_contsAux_det (fun i ↦ (a i : ℝ)) n
  rw [← hC] at det
  have hqn : 0 < (C (n + 1)).b := by
    rw [← hQ]; exact cf_dens_pos (pos_fin ha n) n le_rfl
  have hqn1 : 0 ≤ (C n).b := by
    rcases n with _ | n
    · simp [hC, zeroth_contAux_eq_one_zero]
    · have := cf_dens_pos (pos_fin ha n) n le_rfl
      rw [den_eq_conts_b, nth_cont_eq_succ_nth_contAux] at this
      exact this.le
  obtain ⟨hy0, hy1⟩ := cf_value_mem_Ioo hpt hy
  simp only [add_zero] at hy0 hy1
  have hD : 0 < y * (C (n + 1)).b + (C n).b := by
    have : (1 : ℝ) ≤ a (n + 1) := by exact_mod_cast ha (n + 1) (by omega)
    nlinarith
  have hDne := hD.ne'
  have hqne := hqn.ne'
  refine ⟨y * (C (n + 1)).b + (C n).b, ?_, ?_, ?_, ?_⟩
  · rw [hQ1]; nlinarith
  · rw [hQ1, hQ]; nlinarith
  · rw [e, cf_convs, hP, hQ]
    field_simp
    linear_combination det
  · rw [e, hP, hQ, eq_div_iff hDne, sub_mul, mul_assoc, div_mul_cancel₀ _ hDne]
    linear_combination det

/-- **Theorem 171.** The results of Theorems 163 and 164 hold for infinite simple continued fractions: the
differences `|qₙ x - pₙ|` and `|x - pₙ/qₙ|` decrease strictly, and
`1/(qₙ(qₙ₊₁ + qₙ)) < |x - pₙ/qₙ| < 1/(qₙ qₙ₊₁) ≤ 1/qₙ²` (Hardy–Wright (10.9.1)). -/
@[kb "hardywright2008" "Thm 171, p. 180"]
theorem cf_abs_sub_convs_bounds (ha : ∀ i, 1 ≤ i → 0 < a i) {x : ℝ}
    (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 x)) (n : ℕ) :
    1 / ((cf (fun i ↦ (a i : ℝ))).dens n *
        ((cf (fun i ↦ (a i : ℝ))).dens (n + 1) + (cf (fun i ↦ (a i : ℝ))).dens n)) <
        |x - (cf (fun i ↦ (a i : ℝ))).convs n| ∧
      |x - (cf (fun i ↦ (a i : ℝ))).convs n| <
        1 / ((cf (fun i ↦ (a i : ℝ))).dens n * (cf (fun i ↦ (a i : ℝ))).dens (n + 1)) ∧
      1 / ((cf (fun i ↦ (a i : ℝ))).dens n * (cf (fun i ↦ (a i : ℝ))).dens (n + 1)) ≤
        1 / (cf (fun i ↦ (a i : ℝ))).dens n ^ 2 ∧
      |(cf (fun i ↦ (a i : ℝ))).dens (n + 1) * x - (cf (fun i ↦ (a i : ℝ))).nums (n + 1)| <
        |(cf (fun i ↦ (a i : ℝ))).dens n * x - (cf (fun i ↦ (a i : ℝ))).nums n| ∧
      |x - (cf (fun i ↦ (a i : ℝ))).convs (n + 1)| < |x - (cf (fun i ↦ (a i : ℝ))).convs n| := by
  obtain ⟨D, hD1, hD2, e1, e2⟩ := cf_sub_convs_eq ha hx n
  obtain ⟨D', hD1', -, e1', e2'⟩ := cf_sub_convs_eq ha hx (n + 1)
  have hp := pos_fin ha (n + 2)
  have hq0 := cf_dens_pos hp n (by omega)
  have hq1 := cf_dens_pos hp (n + 1) (by omega)
  have hmono := (cf_dens_le_dens_succ (pos_finZ ha (n + 2)) (n := n) (by omega)).1
  have hq2 : (cf (fun i ↦ (a i : ℝ))).dens (n + 2) ≥
      (cf (fun i ↦ (a i : ℝ))).dens (n + 1) + (cf (fun i ↦ (a i : ℝ))).dens n := by
    rw [cf_dens_add_two]
    have : (1 : ℝ) ≤ a (n + 2) := by exact_mod_cast ha (n + 2) (by omega)
    nlinarith
  set q0 := (cf (fun i ↦ (a i : ℝ))).dens n
  set q1 := (cf (fun i ↦ (a i : ℝ))).dens (n + 1)
  have hD0 : 0 < D := by linarith
  have hD0' : 0 < D' := by linarith
  have habs : ∀ (m : ℕ) (r : ℝ), 0 < r → |(-1 : ℝ) ^ m / r| = 1 / r := by
    intro m r hr
    rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos hr]
  rw [e1, e2, e1', e2', habs _ _ (mul_pos hq0 hD0), habs _ _ hD0, habs _ _ hD0',
    habs _ _ (mul_pos hq1 hD0')]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact one_div_lt_one_div_of_lt (mul_pos hq0 hD0) (mul_lt_mul_of_pos_left hD2 hq0)
  · exact one_div_lt_one_div_of_lt (mul_pos hq0 hq1) (mul_lt_mul_of_pos_left hD1 hq0)
  · rw [sq]
    exact one_div_le_one_div_of_le (mul_pos hq0 hq0) (mul_le_mul_of_nonneg_left hmono hq0.le)
  · exact one_div_lt_one_div_of_lt hD0 (by linarith)
  · have : D < D' := by linarith
    exact one_div_lt_one_div_of_lt (mul_pos hq0 hD0) (by nlinarith)

end Convergence

end NTKB.HardyWright
