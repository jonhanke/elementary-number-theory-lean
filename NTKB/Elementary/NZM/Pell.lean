/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.ContinuedFractions.Pell

/-!
# The continued fraction of `√d` and Pell's equation (Niven–Zuckerman–Montgomery, §§ 7.7–7.8)

Niven–Zuckerman–Montgomery expand a quadratic irrational `ξ₀ = (m₀ + √d)/q₀` (with `q₀ ∣ d - m₀²`) by
the recursion (7.13)

  `aᵢ = ⌊ξᵢ⌋`, `m_{i+1} = aᵢ qᵢ - mᵢ`, `q_{i+1} = (d - m_{i+1}²)/qᵢ`, `ξ_{i+1} = (m_{i+1} + √d)/q_{i+1}`.

We define this recursion (`mq`), prove that the `qᵢ` are nonzero integers with `qᵢ ∣ d - mᵢ²` and that
`ξ_{i+1} = 1/(ξᵢ - aᵢ)` (equations (7.7)); for `ξ₀ = √d` (`m₀ = 0`, `q₀ = 1`) the `ξᵢ` are the complete
quotients of the continued fraction of `√d` (in the Hardy–Wright formalization of `NTKB`, where an
infinite simple continued fraction is a sequence `a : ℕ → ℤ` with positive terms after `a₀` whose
convergents tend to the value).

* Theorem 7.22: `hₙ² - d kₙ² = (-1)^{n-1} q_{n+1}`.
* Theorem 7.21 (the statements about the `qᵢ`): `qᵢ = 1` if and only if the period `r` divides `i`, and
  `qᵢ = -1` for no `i` (the shape `√d = ⟨a₀, a₁, …, a_{r-1}, 2a₀⟩` with the bar over `a₁ … 2a₀` is
  `NTKB.HardyWright.pell_period`).
* Theorem 7.24: if `|N| < √d`, every positive solution of `x² - d y² = N` with `(x, y) = 1` is a convergent.
  The book's proof: Legendre's criterion (Theorem 7.14, Mathlib's `Real.exists_rat_eq_convergent`) for
  `√d` if `N > 0`, and for `1/√d` if `N < 0`, with Theorem 7.15 (the convergents of `1/x` are the
  reciprocals of those of `x`), which for Mathlib's `Real.convergent` is the defining recursion.
-/

namespace NTKB.NZM

open NTKB.HardyWright GenContFract Filter Topology

/-! ### The recursion (7.13) -/

/-- The pairs `(mᵢ, qᵢ)` of the recursion (7.13) of Niven–Zuckerman–Montgomery, started at
`ξ₀ = (m₀ + √d)/q₀`: `m_{i+1} = aᵢ qᵢ - mᵢ`, `q_{i+1} = (d - m_{i+1}²)/qᵢ` with
`aᵢ = ⌊(mᵢ + √d)/qᵢ⌋`. -/
noncomputable def mq (d : ℕ) (m₀ q₀ : ℤ) : ℕ → ℤ × ℤ
  | 0 => (m₀, q₀)
  | n + 1 =>
    let m := (mq d m₀ q₀ n).1
    let q := (mq d m₀ q₀ n).2
    let a := ⌊((m : ℝ) + √(d : ℝ)) / q⌋
    (a * q - m, (d - (a * q - m) ^ 2) / q)

/-- The real numbers `ξᵢ = (mᵢ + √d)/qᵢ` of the recursion (7.13). -/
noncomputable def xi (d : ℕ) (m₀ q₀ : ℤ) (n : ℕ) : ℝ :=
  (((mq d m₀ q₀ n).1 : ℤ) + √(d : ℝ)) / ((mq d m₀ q₀ n).2 : ℤ)

variable {d : ℕ} {m₀ q₀ : ℤ}

lemma mq_zero : mq d m₀ q₀ 0 = (m₀, q₀) := rfl

lemma mq_succ_fst (n : ℕ) :
    (mq d m₀ q₀ (n + 1)).1 = ⌊xi d m₀ q₀ n⌋ * (mq d m₀ q₀ n).2 - (mq d m₀ q₀ n).1 := rfl

lemma mq_succ_snd (n : ℕ) :
    (mq d m₀ q₀ (n + 1)).2 = (d - (mq d m₀ q₀ (n + 1)).1 ^ 2) / (mq d m₀ q₀ n).2 := rfl

/-- The `qᵢ` are nonzero integers with `qᵢ ∣ d - mᵢ²` (the induction in the proof of Theorem 7.19). -/
theorem mq_snd_ne_zero_dvd (hd : ¬IsSquare d) (hq₀ : q₀ ≠ 0) (hdvd : q₀ ∣ d - m₀ ^ 2) (n : ℕ) :
    (mq d m₀ q₀ n).2 ≠ 0 ∧ (mq d m₀ q₀ n).2 ∣ d - (mq d m₀ q₀ n).1 ^ 2 := by
  induction n with
  | zero => exact ⟨hq₀, hdvd⟩
  | succ n ih =>
    obtain ⟨hq, hdv⟩ := ih
    set m := (mq d m₀ q₀ n).1
    set q := (mq d m₀ q₀ n).2
    set a := ⌊xi d m₀ q₀ n⌋
    have hm' : (mq d m₀ q₀ (n + 1)).1 = a * q - m := mq_succ_fst n
    have hdv' : q ∣ (d : ℤ) - (mq d m₀ q₀ (n + 1)).1 ^ 2 := by
      rw [hm']
      have : (d : ℤ) - (a * q - m) ^ 2 = (d - m ^ 2) + q * (2 * a * m - a ^ 2 * q) := by ring
      rw [this]
      exact dvd_add hdv (dvd_mul_right _ _)
    obtain ⟨c, hc⟩ := hdv'
    have hq' : (mq d m₀ q₀ (n + 1)).2 = c := by
      rw [mq_succ_snd, hc, Int.mul_ediv_cancel_left _ hq]
    rw [hq']
    refine ⟨?_, ⟨q, by rw [hc]; ring⟩⟩
    rintro rfl
    apply hd
    refine ⟨((mq d m₀ q₀ (n + 1)).1).natAbs, ?_⟩
    have h0 : (d : ℤ) = (mq d m₀ q₀ (n + 1)).1 ^ 2 := by linarith [hc, mul_zero q]
    have : ((d : ℕ) : ℤ) = (((mq d m₀ q₀ (n + 1)).1).natAbs * ((mq d m₀ q₀ (n + 1)).1).natAbs : ℕ) := by
      push_cast
      rw [h0, abs_mul_abs_self]
      ring
    exact_mod_cast this

/-- `q_{i+1} qᵢ = d - m_{i+1}²`. -/
lemma mq_snd_mul (hd : ¬IsSquare d) (hq₀ : q₀ ≠ 0) (hdvd : q₀ ∣ d - m₀ ^ 2) (n : ℕ) :
    (mq d m₀ q₀ (n + 1)).2 * (mq d m₀ q₀ n).2 = d - (mq d m₀ q₀ (n + 1)).1 ^ 2 := by
  obtain ⟨hq, -⟩ := mq_snd_ne_zero_dvd hd hq₀ hdvd n
  set q := (mq d m₀ q₀ n).2
  have hdv' : q ∣ (d : ℤ) - (mq d m₀ q₀ (n + 1)).1 ^ 2 := by
    rw [mq_succ_fst]
    have := (mq_snd_ne_zero_dvd hd hq₀ hdvd n).2
    have e : (d : ℤ) - (⌊xi d m₀ q₀ n⌋ * q - (mq d m₀ q₀ n).1) ^ 2 =
        (d - (mq d m₀ q₀ n).1 ^ 2) + q * (2 * ⌊xi d m₀ q₀ n⌋ * (mq d m₀ q₀ n).1 -
          ⌊xi d m₀ q₀ n⌋ ^ 2 * q) := by ring
    rw [e]
    exact dvd_add this (dvd_mul_right _ _)
  rw [mq_succ_snd]
  exact Int.ediv_mul_cancel hdv'

/-- Equations (7.7) for the recursion (7.13): `ξ_{i+1} = 1/(ξᵢ - aᵢ)` with `aᵢ = ⌊ξᵢ⌋`. -/
theorem xi_succ (hd : ¬IsSquare d) (hq₀ : q₀ ≠ 0) (hdvd : q₀ ∣ d - m₀ ^ 2) (n : ℕ) :
    xi d m₀ q₀ (n + 1) = 1 / (xi d m₀ q₀ n - ⌊xi d m₀ q₀ n⌋) := by
  have hirr : Irrational √(d : ℝ) := irrational_sqrt_natCast_iff.mpr hd
  have hq := (mq_snd_ne_zero_dvd hd hq₀ hdvd n).1
  have hq1 := (mq_snd_ne_zero_dvd hd hq₀ hdvd (n + 1)).1
  have hmul := mq_snd_mul hd hq₀ hdvd n
  have hm := mq_succ_fst (d := d) (m₀ := m₀) (q₀ := q₀) n
  set m := (mq d m₀ q₀ n).1
  set q := (mq d m₀ q₀ n).2
  set m' := (mq d m₀ q₀ (n + 1)).1
  set q' := (mq d m₀ q₀ (n + 1)).2
  set a := ⌊xi d m₀ q₀ n⌋
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hq'r : (q' : ℝ) ≠ 0 := by exact_mod_cast hq1
  have hs : √(d : ℝ) ^ 2 = d := Real.sq_sqrt (by positivity)
  have hne : √(d : ℝ) - m' ≠ 0 := by
    intro h
    exact hirr ⟨m', by simpa using (sub_eq_zero.mp h).symm⟩
  have hmulr : (q' : ℝ) * q = d - (m' : ℝ) ^ 2 := by exact_mod_cast hmul
  have hmr : (m' : ℝ) = a * q - m := by exact_mod_cast hm
  have e1 : xi d m₀ q₀ n - a = (√(d : ℝ) - m') / q := by
    rw [show xi d m₀ q₀ n = (m + √(d : ℝ)) / q from rfl, hmr]
    field_simp
    ring
  rw [e1, one_div_div]
  simp only [xi]
  rw [div_eq_div_iff hq'r hne]
  linear_combination hs - hmulr

/-! ### The expansion of `√d` -/

section Sqrt

variable {D : ℕ} {a : ℕ → ℤ}

/-- With `ξ₀ = √d` (`m₀ = 0`, `q₀ = 1`) the recursion (7.13) gives the continued fraction of `√d`: the
`n`-th quotient is `⌊ξₙ⌋` and the complete quotient `⟨aₙ, a_{n+1}, …⟩` is `ξₙ`. -/
theorem sqrt_tail_tendsto_xi (hD : ¬IsSquare D) (ha : ∀ i, 1 ≤ i → 0 < a i)
    (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 √(D : ℝ))) (n : ℕ) :
    Tendsto (fun t ↦ (cf (fun i ↦ ((a (n + i) : ℤ) : ℝ))).convs t) atTop (𝓝 (xi D 0 1 n)) ∧
      a n = ⌊xi D 0 1 n⌋ := by
  have hdvd : (1 : ℤ) ∣ D - 0 ^ 2 := one_dvd _
  have key : ∀ n, Tendsto (fun t ↦ (cf (fun i ↦ ((a (n + i) : ℤ) : ℝ))).convs t) atTop
      (𝓝 (xi D 0 1 n)) := by
    intro n
    induction n with
    | zero =>
      have e : xi D 0 1 0 = √(D : ℝ) := by simp [xi, mq_zero]
      simpa [e] using hx
    | succ n ih =>
      have hb : ∀ i, 1 ≤ i → 0 < a (n + i) := fun i hi ↦ ha (n + i) (by omega)
      have h1 := cf_tendsto_tail hb ih
      have h0 : ⌊xi D 0 1 n⌋ = a (n + 0) := (cf_floor_value_eq hb ih).1
      rw [xi_succ hD one_ne_zero hdvd n, h0]
      have e : (fun i ↦ ((a (n + 1 + i) : ℤ) : ℝ)) = fun i ↦ ((a (n + (i + 1)) : ℤ) : ℝ) := by
        funext i; congr 2; omega
      rw [e]
      exact h1
  refine ⟨key n, ?_⟩
  have hb : ∀ i, 1 ≤ i → 0 < a (n + i) := fun i hi ↦ ha (n + i) (by omega)
  simpa using ((cf_floor_value_eq hb (key n)).1).symm

/-- **Theorem 7.22.** Let `d` be a positive integer which is not a square, `√d = ⟨a₀, a₁, …⟩` with
convergents `hₙ/kₙ`, and `qₙ` given by (7.13) with `ξ₀ = √d`, `q₀ = 1`, `m₀ = 0`. Then
`hₙ² - d kₙ² = (-1)^{n-1} q_{n+1}` (stated for `n ≥ 0`; for `n = -1` it reads `1 = q₀`). -/
@[kb "nivenzuckermanmontgomery" "Thm 7.22, p. 351"]
theorem sq_sub_mul_sq_convergent (hD : ¬IsSquare D) (ha : ∀ i, 1 ≤ i → 0 < a i)
    (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 √(D : ℝ))) (n : ℕ) :
    (cf (fun i ↦ (a i : ℝ))).nums n ^ 2 - D * (cf (fun i ↦ (a i : ℝ))).dens n ^ 2 =
      (-1) ^ (n + 1) * ((mq D 0 1 (n + 1)).2 : ℝ) := by
  have hdvd : (1 : ℤ) ∣ D - 0 ^ 2 := one_dvd _
  obtain ⟨P, Q, P', Q', hP, hQ, -, -, -, -, -, hid, -⟩ :=
    sqrt_cq_identity hD ha hx n (sqrt_tail_tendsto_xi hD ha hx (n + 1)).1
  have hq := (mq_snd_ne_zero_dvd hD one_ne_zero hdvd (n + 1)).1
  set m := (mq D 0 1 (n + 1)).1
  set q := (mq D 0 1 (n + 1)).2
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hxi : xi D 0 1 (n + 1) = (m + √(D : ℝ)) / q := rfl
  rw [hxi, div_mul_eq_mul_div, div_eq_iff hqr] at hid
  have key : ((m * (D * Q ^ 2 - P ^ 2) - q * (P' * P - D * Q' * Q) : ℤ) : ℝ) +
      ((D * Q ^ 2 - P ^ 2 - q * (-1) ^ n : ℤ) : ℝ) * √(D : ℝ) = 0 := by
    push_cast; linear_combination hid
  have h2 := (int_add_mul_sqrt_eq_zero hD key).2
  rw [hP, hQ]
  have h3 : ((D * Q ^ 2 - P ^ 2 : ℤ) : ℝ) = ((q * (-1) ^ n : ℤ) : ℝ) := by
    rw [sub_eq_zero.mp h2]
  push_cast at h3
  rw [pow_succ]
  linear_combination -h3

/-- **Theorem 7.21** (the statements on the `qᵢ`). Let `d` be a positive integer which is not a square,
`√d = ⟨a₀, a₁, …⟩`, and `qᵢ` given by (7.13) with `ξ₀ = √d`, `q₀ = 1`, `m₀ = 0`. Then `a₀ = ⌊√d⌋` and
there is `r ≥ 1`, the length of the shortest period, with `√d = ⟨a₀, \overline{a₁, …, a_{r-1}, 2a₀}⟩`
(that is, `a_r = 2a₀` and `a_{r+i} = aᵢ` for `i ≥ 1`, and every `m ≥ 1` with this property is a multiple
of `r`), such that `qᵢ = 1` if and only if `r ∣ i`, and `qᵢ = -1` for no `i`. -/
@[kb "nivenzuckermanmontgomery" "Thm 7.21, p. 350"]
theorem sqrt_cf_period_mq (hD : ¬IsSquare D) (ha : ∀ i, 1 ≤ i → 0 < a i)
    (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 √(D : ℝ))) :
    a 0 = ⌊√(D : ℝ)⌋ ∧ ∃ r : ℕ, 1 ≤ r ∧ a r = 2 * a 0 ∧ (∀ i, 1 ≤ i → a (r + i) = a i) ∧
      (∀ m, 1 ≤ m → a m = 2 * a 0 → (∀ i, 1 ≤ i → a (m + i) = a i) → r ∣ m) ∧
      ∀ i, ((mq D 0 1 i).2 = 1 ↔ r ∣ i) ∧ (mq D 0 1 i).2 ≠ -1 := by
  refine ⟨((cf_floor_value_eq ha hx).1).symm, ?_⟩
  obtain ⟨r, hr1, hr2, hr3, hr4, -, -⟩ := pell_period hD ha hx
  refine ⟨r, hr1, hr2, hr3, hr4, ?_⟩
  -- `IsPellIndex a i ↔ r ∣ i` for `i ≥ 1`
  have hpi : ∀ i, 1 ≤ i → (IsPellIndex a i ↔ r ∣ i) := by
    intro i hi
    constructor
    · rintro ⟨h1, h2, h3⟩; exact hr4 i h1 h2 h3
    · rintro ⟨k, rfl⟩
      have hk : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with rfl | h
        · simp at hi
        · exact h
      have hr : IsPellIndex a r := ⟨hr1, hr2, hr3⟩
      induction k, hk using Nat.le_induction with
      | base => simpa using hr
      | succ k hk ih =>
        rw [mul_add, mul_one]
        exact (ih (by nlinarith)).add hr
  intro i
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [mq_zero]
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  have h722 := sq_sub_mul_sq_convergent hD ha hx n
  obtain ⟨hiff, hval⟩ := pell_iff_isPellIndex hD ha hx n
  rw [← hpi (n + 1) (by omega)]
  have hsign : ((-1 : ℝ) ^ (n + 1)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  constructor
  · constructor
    · intro hq
      apply hiff.mp
      rw [h722, hq]
      rcases neg_one_pow_eq_or ℝ (n + 1) with h | h <;> rw [h] <;> simp
    · intro hP
      have := hval hP
      rw [h722] at this
      have hne : ((-1 : ℝ) ^ (n + 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
      have : ((mq D 0 1 (n + 1)).2 : ℝ) = 1 := by
        have := mul_left_cancel₀ hne (this.trans (mul_one _).symm)
        exact this
      exact_mod_cast this
  · intro hq
    have hP : IsPellIndex a (n + 1) := by
      apply hiff.mp
      rw [h722, hq]
      rcases neg_one_pow_eq_or ℝ (n + 1) with h | h <;> rw [h] <;> simp
    have := hval hP
    rw [h722, hq] at this
    have hne : ((-1 : ℝ) ^ (n + 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
    have := mul_left_cancel₀ hne (this.trans (mul_one _).symm)
    norm_num at this

end Sqrt

/-! ### Theorem 7.24 -/

/-- The first step of the proof of Theorem 7.24: if `E, M > 0` are coprime, `ρ > 0`, and
`E² - ρ² M² = α` with `0 < α < ρ`, then `E/M` is a convergent of `ρ` (Legendre's criterion, Theorem 7.14). -/
theorem exists_convergent_of_sq_sub_sq {ρ α : ℝ} (hρ : 0 < ρ) {E M : ℤ} (hE : 0 < E) (hM : 0 < M)
    (hcop : IsCoprime E M) (hα : 0 < α) (hαρ : α < ρ) (h : (E : ℝ) ^ 2 - ρ ^ 2 * M ^ 2 = α) :
    ∃ n, ρ.convergent n = (E / M : ℚ) := by
  have hden : ((E / M : ℚ).den : ℤ) = M :=
    Rat.den_div_eq_of_coprime hM (Int.isCoprime_iff_gcd_eq_one.mp hcop)
  have hEr : (0 : ℝ) < E := by exact_mod_cast hE
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hfac : ((E : ℝ) - M * ρ) * (E + M * ρ) = α := by linear_combination h
  have hpos : 0 < (E : ℝ) - M * ρ := by
    by_contra hc
    push Not at hc
    have : ((E : ℝ) - M * ρ) * (E + M * ρ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hc (by positivity)
    linarith
  have hlt : |ρ - ((E / M : ℚ) : ℝ)| < 1 / (2 * ((E / M : ℚ).den : ℝ) ^ 2) := by
    have hd : ((E / M : ℚ).den : ℝ) = M := by exact_mod_cast hden
    rw [hd]
    push_cast
    have e : ρ - E / M = -(((E : ℝ) - M * ρ) / M) := by field_simp; ring
    rw [e, abs_neg, abs_of_pos (div_pos hpos hMr), div_lt_div_iff₀ hMr (by positivity)]
    -- `2 M δ ρ < δ (E + M ρ) = α < ρ`
    have h1 : 2 * M * ((E : ℝ) - M * ρ) * ρ < α := by
      rw [← hfac]; nlinarith
    have h2 : 2 * M * ((E : ℝ) - M * ρ) < 1 := by
      by_contra hc; push Not at hc; nlinarith
    nlinarith
  obtain ⟨n, hn⟩ := Real.exists_rat_eq_convergent hlt
  exact ⟨n, hn.symm⟩

section Sqrt

variable {D : ℕ} {a : ℕ → ℤ}

/-- If `x/y` (coprime, `y > 0`) is Mathlib's `n`-th convergent of `√D`, then `x = hₙ`, `y = kₙ`. -/
lemma nums_dens_eq_of_convergent (ha : ∀ i, 1 ≤ i → 0 < a i)
    (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 √(D : ℝ))) {X Y : ℤ}
    (hY : 0 < Y) (hcop : IsCoprime X Y) {n : ℕ} (hn : (√(D : ℝ)).convergent n = (X / Y : ℚ)) :
    (cf (fun i ↦ (a i : ℝ))).nums n = X ∧ (cf (fun i ↦ (a i : ℝ))).dens n = Y := by
  have hc := cf_convs_eq_convergent ha hx n
  rw [hn] at hc
  obtain ⟨p, q, hp, hq⟩ := cf_nums_dens_int a n
  have hqpos : 0 < q := by
    have := cf_dens_pos (pos_fin ha n) n le_rfl
    rw [hq] at this; exact_mod_cast this
  rw [cf_convs, hp, hq] at hc
  push_cast at hc
  obtain ⟨h1, h2⟩ := eq_of_div_eq_div (cf_isCoprime_nums_dens a n hp hq) hcop hqpos hY hc
  rw [hp, hq, h1, h2]; exact ⟨rfl, rfl⟩

/-- **Theorem 7.24.** Let `d` be a positive integer which is not a square, `√d = ⟨a₀, a₁, …⟩` with
convergents `hₙ/kₙ`, and `N` an integer with `|N| < √d`. Then every positive solution `x = s`, `y = t` of
`x² - d y² = N` with `(s, t) = 1` is `s = hₙ`, `t = kₙ` for some `n`. -/
@[kb "nivenzuckermanmontgomery" "Thm 7.24, p. 352"]
theorem eq_convergent_of_sq_sub_mul_sq (hD : ¬IsSquare D) (ha : ∀ i, 1 ≤ i → 0 < a i)
    (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 √(D : ℝ))) {N s t : ℤ}
    (hN : |(N : ℝ)| < √(D : ℝ)) (hs : 0 < s) (ht : 0 < t) (hcop : IsCoprime s t)
    (h : s ^ 2 - D * t ^ 2 = N) :
    ∃ n, (cf (fun i ↦ (a i : ℝ))).nums n = s ∧ (cf (fun i ↦ (a i : ℝ))).dens n = t := by
  have hD2 : (2 : ℝ) ≤ D := by exact_mod_cast two_le_of_not_isSquare hD
  have hsq : √(D : ℝ) ^ 2 = D := Real.sq_sqrt (by positivity)
  have hs1 : 1 < √(D : ℝ) := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  have hsr : (0 : ℝ) < s := by exact_mod_cast hs
  have htr : (0 : ℝ) < t := by exact_mod_cast ht
  have hr : (s : ℝ) ^ 2 - D * t ^ 2 = N := by exact_mod_cast h
  rcases lt_trichotomy N 0 with hN0 | hN0 | hN0
  · -- `N < 0`: `t/s` is a convergent of `1/√d`
    have hNr : (N : ℝ) < 0 := by exact_mod_cast hN0
    rw [abs_of_neg hNr] at hN
    have hρ : (0 : ℝ) < 1 / √(D : ℝ) := by positivity
    have hα : (0 : ℝ) < -N / D := div_pos (by linarith) (by linarith)
    have hαρ : -(N : ℝ) / D < 1 / √(D : ℝ) := by
      rw [div_lt_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    have heq : (t : ℝ) ^ 2 - (1 / √(D : ℝ)) ^ 2 * s ^ 2 = -N / D := by
      rw [div_pow, hsq]; field_simp; linarith
    obtain ⟨m, hm⟩ := exists_convergent_of_sq_sub_sq hρ ht hs hcop.symm hα hαρ heq
    have hfl : ⌊1 / √(D : ℝ)⌋ = 0 := by
      rw [Int.floor_eq_zero_iff]
      exact ⟨hρ.le, by rw [div_lt_one (by linarith)]; exact hs1⟩
    rcases m with _ | n
    · rw [Real.convergent_zero, hfl] at hm
      have : ((t / s : ℚ) : ℝ) = 0 := by rw [← hm]; simp
      push_cast at this
      exact absurd this (div_pos htr hsr).ne'
    · rw [Real.convergent_succ, hfl, Int.fract_eq_self.mpr ⟨hρ.le, by
        rw [div_lt_one (by linarith)]; exact hs1⟩, one_div, inv_inv] at hm
      refine ⟨n, nums_dens_eq_of_convergent ha hx ht hcop ?_⟩
      have h0 : ((t / s : ℚ)) ≠ 0 := div_ne_zero (by exact_mod_cast ht.ne') (by exact_mod_cast hs.ne')
      have : ((√(D : ℝ)).convergent n)⁻¹ = (t / s : ℚ) := by simpa using hm
      rw [← inv_inv ((√(D : ℝ)).convergent n), this, inv_div]
  · -- `N = 0` is impossible
    exfalso
    subst hN0
    have hirr : Irrational √(D : ℝ) := irrational_sqrt_natCast_iff.mpr hD
    apply hirr
    refine ⟨(s / t : ℚ), ?_⟩
    push_cast
    rw [div_eq_iff htr.ne']
    have h1 : ((s : ℝ) - t * √(D : ℝ)) * (s + t * √(D : ℝ)) = 0 := by
      linear_combination hr + (-(t : ℝ) ^ 2) * hsq
    rcases mul_eq_zero.mp h1 with h1 | h1
    · linarith
    · nlinarith [Real.sqrt_nonneg (D : ℝ)]
  · -- `N > 0`: `s/t` is a convergent of `√d`
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
    rw [abs_of_pos hNr] at hN
    obtain ⟨n, hn⟩ := exists_convergent_of_sq_sub_sq (by linarith) hs ht hcop hNr hN
      (by rw [hsq]; exact hr)
    exact ⟨n, nums_dens_eq_of_convergent ha hx ht hcop hn⟩

/-- **Theorem 7.25.** Let `d` be a positive integer which is not a square, `√d = ⟨a₀, a₁, …⟩` with
convergents `hₙ/kₙ`, and `r` the length of the period (as in Theorem 7.21). If `r` is even, then
`x² - d y² = -1` has no solution in positive integers and the positive solutions of `x² - d y² = 1` are
`x = h_{nr-1}`, `y = k_{nr-1}`, `n = 1, 2, 3, …`. If `r` is odd, then `x = h_{nr-1}`, `y = k_{nr-1}` give
all positive solutions of `x² - d y² = -1` for `n = 1, 3, 5, …` and all positive solutions of
`x² - d y² = 1` for `n = 2, 4, 6, …`. -/
@[kb "nivenzuckermanmontgomery" "Thm 7.25, p. 353"]
theorem pell_solutions_of_period (hD : ¬IsSquare D) (ha : ∀ i, 1 ≤ i → 0 < a i)
    (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 √(D : ℝ))) :
    ∃ r : ℕ, 1 ≤ r ∧ a r = 2 * a 0 ∧ (∀ i, 1 ≤ i → a (r + i) = a i) ∧
      (∀ m, 1 ≤ m → a m = 2 * a 0 → (∀ i, 1 ≤ i → a (m + i) = a i) → r ∣ m) ∧
      (Even r → (∀ X Y : ℤ, 0 < X → 0 < Y → X ^ 2 - D * Y ^ 2 ≠ -1) ∧
        ∀ X Y : ℤ, 0 < X → 0 < Y → (X ^ 2 - D * Y ^ 2 = 1 ↔
          ∃ n, 1 ≤ n ∧ (cf (fun i ↦ (a i : ℝ))).nums (n * r - 1) = X ∧
            (cf (fun i ↦ (a i : ℝ))).dens (n * r - 1) = Y)) ∧
      (Odd r → (∀ X Y : ℤ, 0 < X → 0 < Y → (X ^ 2 - D * Y ^ 2 = -1 ↔
          ∃ n, Odd n ∧ (cf (fun i ↦ (a i : ℝ))).nums (n * r - 1) = X ∧
            (cf (fun i ↦ (a i : ℝ))).dens (n * r - 1) = Y)) ∧
        ∀ X Y : ℤ, 0 < X → 0 < Y → (X ^ 2 - D * Y ^ 2 = 1 ↔
          ∃ n, Even n ∧ 1 ≤ n ∧ (cf (fun i ↦ (a i : ℝ))).nums (n * r - 1) = X ∧
            (cf (fun i ↦ (a i : ℝ))).dens (n * r - 1) = Y)) := by
  obtain ⟨r, hr1, hr2, hr3, hr4, hsign, hsol⟩ := pell_period hD ha hx
  -- the value of `X² - D Y²` at `(h_{nr-1}, k_{nr-1})`
  have hval : ∀ X Y : ℤ, ∀ n, 1 ≤ n → (cf (fun i ↦ (a i : ℝ))).nums (n * r - 1) = X →
      (cf (fun i ↦ (a i : ℝ))).dens (n * r - 1) = Y → X ^ 2 - D * Y ^ 2 = (-1) ^ (n * r) := by
    intro X Y n hn hX hY
    have := hsign n hn
    rw [hX, hY] at this
    exact_mod_cast this
  refine ⟨r, hr1, hr2, hr3, hr4, ?_, ?_⟩
  · intro hr
    refine ⟨fun X Y hX hY h ↦ ?_, fun X Y hX hY ↦ ⟨fun h ↦ ?_, ?_⟩⟩
    · obtain ⟨n, hn, h1, h2⟩ := (hsol X Y hX hY).mp (Or.inr h)
      have := hval X Y n hn h1 h2
      rw [h, (hr.mul_left n).neg_one_pow] at this
      norm_num at this
    · exact (hsol X Y hX hY).mp (Or.inl h)
    · rintro ⟨n, hn, h1, h2⟩
      rw [hval X Y n hn h1 h2, (hr.mul_left n).neg_one_pow]
  · intro hr
    refine ⟨fun X Y hX hY ↦ ⟨fun h ↦ ?_, ?_⟩, fun X Y hX hY ↦ ⟨fun h ↦ ?_, ?_⟩⟩
    · obtain ⟨n, hn, h1, h2⟩ := (hsol X Y hX hY).mp (Or.inr h)
      refine ⟨n, ?_, h1, h2⟩
      have := hval X Y n hn h1 h2
      rw [h] at this
      rcases Nat.even_or_odd n with hn' | hn'
      · rw [(hn'.mul_right r).neg_one_pow] at this; norm_num at this
      · exact hn'
    · rintro ⟨n, hn, h1, h2⟩
      rw [hval X Y n hn.pos h1 h2, (hn.mul hr).neg_one_pow]
    · obtain ⟨n, hn, h1, h2⟩ := (hsol X Y hX hY).mp (Or.inl h)
      refine ⟨n, ?_, hn, h1, h2⟩
      have := hval X Y n hn h1 h2
      rw [h] at this
      rcases Nat.even_or_odd n with hn' | hn'
      · exact hn'
      · rw [(hn'.mul hr).neg_one_pow] at this; norm_num at this
    · rintro ⟨n, hn, hn1, h1, h2⟩
      rw [hval X Y n hn1 h1 h2, (hn.mul_right r).neg_one_pow]

end Sqrt

end NTKB.NZM
