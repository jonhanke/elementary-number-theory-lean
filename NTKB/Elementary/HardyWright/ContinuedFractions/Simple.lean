/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.ContinuedFractions.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.RingTheory.Coprime.Basic

/-!
# Simple continued fractions (Hardy–Wright, Chapter X, §§ 10.4 to 10.6)

A *simple* continued fraction `[a₀, a₁, …, a_N]` has integral quotients with `a₁, …, a_N > 0`
(`a₀` may be negative). We take quotients `a : ℕ → ℤ`, so the continued fraction is
`cf (fun i ↦ (a i : ℝ))`, and its value is the `N`-th convergent.

* Theorem 155: `qₙ ≥ qₙ₋₁` for `n ≥ 1`, strictly for `n > 1`.
* Theorem 156: `qₙ ≥ n`, strictly for `n > 3`.
* Theorem 157: `pₙ` and `qₙ` are coprime integers.
* Theorem 158: a number with an expansion with an odd (even) number of convergents has one with an even
  (odd) number.
* Theorem 159: the `n`-th complete quotient `a'ₙ = [aₙ, …, a_N]` has integral part `aₙ`, except that
  `a_{N-1} = [a'_{N-1}] - 1` when `a_N = 1`.
* Theorem 160: two finite simple continued fractions with the same value, whose last quotients exceed `1`,
  are identical.
* Theorem 161 (Hardy–Wright's proof, by Euclid's algorithm): every rational number has a finite simple
  expansion, which may be taken with last quotient greater than `1`.
* Theorem 162: a rational number has exactly two finite simple expansions, one with an even and one with an
  odd number of convergents; in one the last quotient is `1`, in the other it is greater than `1`.
-/

namespace NTKB.HardyWright

open GenContFract

section Field

variable {K : Type*} [Field K]

/-- Removing the first quotient: `p_{n+1}(a₀, …) = a₀ pₙ(a₁, …) + qₙ(a₁, …)` and
`q_{n+1}(a₀, …) = pₙ(a₁, …)`. -/
lemma cf_nums_dens_succ (a : ℕ → K) (n : ℕ) :
    (cf a).nums (n + 1) =
        a 0 * (cf (fun i ↦ a (i + 1))).nums n + (cf (fun i ↦ a (i + 1))).dens n ∧
      (cf a).dens (n + 1) = (cf (fun i ↦ a (i + 1))).nums n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp; ring
    | 1, _ =>
      show (cf a).nums (0 + 2) = _ ∧ (cf a).dens (0 + 2) = _
      rw [cf_nums_add_two, cf_dens_add_two]
      simp; ring
    | n + 2, ih =>
      obtain ⟨h1, h1'⟩ := ih (n + 1) (by omega)
      obtain ⟨h0, h0'⟩ := ih n (by omega)
      show (cf a).nums ((n + 1) + 2) = _ ∧ (cf a).dens ((n + 1) + 2) = _
      rw [cf_nums_add_two a (n + 1), cf_dens_add_two a (n + 1), h1, h1', h0, h0',
        cf_nums_add_two (fun i ↦ a (i + 1)) n, cf_dens_add_two (fun i ↦ a (i + 1)) n]
      simp only [show n + 2 + 1 = n + 1 + 2 from rfl]
      exact ⟨by ring, trivial⟩

/-- `[a₀, a₁, …, a_{n+1}] = a₀ + 1/[a₁, …, a_{n+1}]` (Hardy–Wright (10.1.3)), provided the numerator of
`[a₁, …, a_{n+1}]` does not vanish. -/
lemma cf_convs_succ (a : ℕ → K) (n : ℕ) (h : (cf (fun i ↦ a (i + 1))).nums n ≠ 0) :
    (cf a).convs (n + 1) = a 0 + 1 / (cf (fun i ↦ a (i + 1))).convs n := by
  obtain ⟨h1, h2⟩ := cf_nums_dens_succ a n
  rw [cf_convs, cf_convs, h1, h2, one_div_div]
  field_simp

/-- The continuant recurrence on Mathlib's auxiliary pairs `contsAux` (`contsAux (n + 1) = (pₙ, qₙ)`,
`contsAux 0 = (1, 0)`). -/
lemma cf_contsAux_add_two (a : ℕ → K) (n : ℕ) :
    (cf a).contsAux (n + 2) =
      ⟨a (n + 1) * ((cf a).contsAux (n + 1)).a + ((cf a).contsAux n).a,
        a (n + 1) * ((cf a).contsAux (n + 1)).b + ((cf a).contsAux n).b⟩ := by
  rw [contsAux_recurrence (cf_s_get? a n) rfl rfl]; simp

lemma cf_contsAux_congr {a b : ℕ → K} {N : ℕ} (h : ∀ i < N, a i = b i) :
    ∀ k ≤ N, (cf a).contsAux k = (cf b).contsAux k := by
  intro k hk
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, hk, ih with
    | 0, _, _ => simp [zeroth_contAux_eq_one_zero]
    | 1, hk, _ => simp [first_contAux_eq_h_one, h 0 (by omega)]
    | k + 2, hk, ih =>
      rw [cf_contsAux_add_two, cf_contsAux_add_two, ih (k + 1) (by omega) (by omega),
        ih k (by omega) (by omega), h (k + 1) (by omega)]

/-- Replacing the last quotient `a_N` by the two quotients `a_N - 1, 1` does not change `p_N, q_N`. -/
lemma cf_nums_dens_split_last {a b : ℕ → K} {N : ℕ} (hlt : ∀ i < N, b i = a i)
    (hN : b N = a N - 1) (hN1 : b (N + 1) = 1) :
    (cf b).nums (N + 1) = (cf a).nums N ∧ (cf b).dens (N + 1) = (cf a).dens N := by
  rcases N with _ | N
  · simp [hN, hN1]
  · have hc := cf_contsAux_congr (a := b) (b := a) (N := N + 1) hlt
    have e : (cf b).contsAux (N + 1 + 2) = (cf a).contsAux (N + 2) := by
      rw [cf_contsAux_add_two b (N + 1), show N + 1 + 1 = N + 2 from rfl, cf_contsAux_add_two b N,
        cf_contsAux_add_two a N, hN1, hN, hc (N + 1) le_rfl, hc N (by omega)]
      congr 1 <;> ring
    simp only [num_eq_conts_a, den_eq_conts_b, nth_cont_eq_succ_nth_contAux]
    rw [e]
    exact ⟨rfl, rfl⟩

end Field

section Ordered

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- If `a₀, …, a_N > 0` then all numerators `p₀, …, p_N` are positive. -/
lemma cf_nums_pos {a : ℕ → K} {N : ℕ} (hpos : ∀ i ≤ N, 0 < a i) :
    ∀ n ≤ N, 0 < (cf a).nums n := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, hn, ih with
    | 0, hn, _ => simpa using hpos 0 hn
    | 1, hn, _ =>
      simp only [cf_nums_one]
      exact add_pos (mul_pos (hpos 1 hn) (hpos 0 (by omega))) one_pos
    | n + 2, hn, ih =>
      rw [cf_nums_add_two]
      exact add_pos (mul_pos (hpos (n + 2) hn) (ih (n + 1) (by omega) (by omega)))
        (ih n (by omega) (by omega))

end Ordered

/-! ### Theorems 155 to 157 -/

section Simple

variable {a : ℕ → ℤ} {N : ℕ}

/-- For a simple continued fraction, `qₙ ≥ 1`. -/
lemma cf_dens_one_le (hpos : ∀ i, 1 ≤ i → i ≤ N → 0 < a i) :
    ∀ n ≤ N, (1 : ℝ) ≤ (cf (fun i ↦ (a i : ℝ))).dens n := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, hn, ih with
    | 0, _, _ => simp
    | 1, hn, _ =>
      simp only [cf_dens_one]; exact_mod_cast hpos 1 le_rfl hn
    | n + 2, hn, ih =>
      rw [cf_dens_add_two]
      have h1 : (1 : ℝ) ≤ a (n + 2) := by exact_mod_cast hpos (n + 2) (by omega) hn
      have := ih (n + 1) (by omega) (by omega)
      have := ih n (by omega) (by omega)
      nlinarith

/-- **Theorem 155.** For a simple continued fraction, `qₙ₋₁ ≤ qₙ` for `n ≥ 1`, with strict inequality
for `n > 1` (stated with `n + 1` for `n`). -/
@[kb "hardywright2008" "Thm 155, p. 169"]
theorem cf_dens_le_dens_succ (hpos : ∀ i, 1 ≤ i → i ≤ N → 0 < a i) {n : ℕ} (hn : n + 1 ≤ N) :
    (cf (fun i ↦ (a i : ℝ))).dens n ≤ (cf (fun i ↦ (a i : ℝ))).dens (n + 1) ∧
      (1 ≤ n → (cf (fun i ↦ (a i : ℝ))).dens n < (cf (fun i ↦ (a i : ℝ))).dens (n + 1)) := by
  have hq := cf_dens_one_le hpos
  rcases n with _ | n
  · simp only [zero_add, cf_dens_zero, cf_dens_one]
    exact ⟨by exact_mod_cast hpos 1 le_rfl hn, fun h ↦ absurd h (by omega)⟩
  · rw [cf_dens_add_two]
    have h1 : (1 : ℝ) ≤ a (n + 2) := by exact_mod_cast hpos (n + 2) (by omega) hn
    have := hq (n + 1) (by omega)
    have := hq n (by omega)
    constructor
    · nlinarith
    · intro; nlinarith

/-- **Theorem 156.** For a simple continued fraction, `qₙ ≥ n`, with strict inequality for `n > 3`. -/
@[kb "hardywright2008" "Thm 156, p. 169"]
theorem cf_le_dens (hpos : ∀ i, 1 ≤ i → i ≤ N → 0 < a i) {n : ℕ} (hn : n ≤ N) :
    (n : ℝ) ≤ (cf (fun i ↦ (a i : ℝ))).dens n ∧ (3 < n → (n : ℝ) < (cf (fun i ↦ (a i : ℝ))).dens n) := by
  have hq := cf_dens_one_le hpos
  -- `q_{n+2} ≥ q_{n+1} + q_n`
  have step : ∀ m, m + 2 ≤ N → (cf (fun i ↦ (a i : ℝ))).dens (m + 1) + (cf (fun i ↦ (a i : ℝ))).dens m
      ≤ (cf (fun i ↦ (a i : ℝ))).dens (m + 2) := by
    intro m hm
    rw [cf_dens_add_two]
    have h1 : (1 : ℝ) ≤ a (m + 2) := by exact_mod_cast hpos (m + 2) (by omega) hm
    have := hq (m + 1) (by omega)
    nlinarith
  have weak : ∀ m ≤ N, (m : ℝ) ≤ (cf (fun i ↦ (a i : ℝ))).dens m := by
    intro m hm
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      match m, hm, ih with
      | 0, _, _ => simp
      | 1, hm, _ => simpa using hq 1 hm
      | m + 2, hm, ih =>
        have := step m hm
        have := ih (m + 1) (by omega) (by omega)
        have := hq m (by omega)
        push_cast at *
        linarith
  refine ⟨weak n hn, fun h3 ↦ ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have := step m hn
  have := weak (m + 1) (by omega)
  have := weak m (by omega)
  push_cast at *
  have : (2 : ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
  linarith

/-- The numerators and denominators of a continued fraction with integral quotients are integers. -/
lemma cf_nums_dens_int (a : ℕ → ℤ) (n : ℕ) :
    ∃ p q : ℤ, (cf (fun i ↦ (a i : ℝ))).nums n = p ∧ (cf (fun i ↦ (a i : ℝ))).dens n = q := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => exact ⟨a 0, 1, by simp, by simp⟩
    | 1, _ => exact ⟨a 1 * a 0 + 1, a 1, by simp, by simp⟩
    | n + 2, ih =>
      obtain ⟨p1, q1, hp1, hq1⟩ := ih (n + 1) (by omega)
      obtain ⟨p0, q0, hp0, hq0⟩ := ih n (by omega)
      exact ⟨a (n + 2) * p1 + p0, a (n + 2) * q1 + q0,
        by rw [cf_nums_add_two, hp1, hp0]; push_cast; ring,
        by rw [cf_dens_add_two, hq1, hq0]; push_cast; ring⟩

/-- **Theorem 157.** The convergents of a simple continued fraction are in their lowest terms: the
integers `pₙ` and `qₙ` are coprime (this holds for any integral quotients). -/
@[kb "hardywright2008" "Thm 157, p. 169"]
theorem cf_isCoprime_nums_dens (a : ℕ → ℤ) (n : ℕ) {p q : ℤ}
    (hp : (cf (fun i ↦ (a i : ℝ))).nums n = p) (hq : (cf (fun i ↦ (a i : ℝ))).dens n = q) :
    IsCoprime p q := by
  obtain ⟨p', q', hp', hq'⟩ := cf_nums_dens_int a (n + 1)
  have h := cf_nums_mul_dens_sub (fun i ↦ (a i : ℝ)) n
  rw [hp, hq, hp', hq'] at h
  have h' : p' * q - p * q' = (-1) ^ n := by exact_mod_cast h
  refine ⟨-(q' * (-1) ^ n), p' * (-1) ^ n, ?_⟩
  have : ((-1 : ℤ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; simp
  linear_combination ((-1 : ℤ) ^ n) * h' + this

end Simple

/-! ### The value of a finite simple continued fraction and its integral part -/

section Value

lemma not_last_one {c : ℕ → ℤ} {K : ℕ} (h : K = 0 ∨ 1 < c K) : ¬(K = 1 ∧ c 1 = 1) := by
  rintro ⟨rfl, h1⟩; rcases h with h | h <;> omega

@[simp] lemma cf_convs_zero {K : Type*} [Field K] (a : ℕ → K) : (cf a).convs 0 = a 0 := by
  simp

/-- Bounds for the value of a simple continued fraction `[c₀, …, c_K]`: it lies in `[c₀, c₀ + 1]`,
strictly above `c₀` when `K ≥ 1`, and strictly below `c₀ + 1` unless `K = 1` and `c₁ = 1`. Moreover the
numerator of `[c₀, …, c_K]` is nonzero when `c₀ ≥ 1`. -/
lemma cf_value_bounds {c : ℕ → ℤ} {K : ℕ} (hc : ∀ i, 1 ≤ i → i ≤ K → 0 < c i) :
    (c 0 : ℝ) ≤ (cf (fun i ↦ (c i : ℝ))).convs K ∧
      (cf (fun i ↦ (c i : ℝ))).convs K ≤ c 0 + 1 ∧
      (1 ≤ K → (c 0 : ℝ) < (cf (fun i ↦ (c i : ℝ))).convs K) ∧
      (¬(K = 1 ∧ c 1 = 1) → (cf (fun i ↦ (c i : ℝ))).convs K < c 0 + 1) := by
  induction K generalizing c with
  | zero => simp
  | succ K ih =>
    have hc' : ∀ i, 1 ≤ i → i ≤ K → 0 < c (i + 1) := fun i h1 h2 ↦ hc (i + 1) (by omega) (by omega)
    obtain ⟨l1, -, l3, -⟩ := ih (c := fun i ↦ c (i + 1)) hc'
    have hc1 : (1 : ℝ) ≤ c 1 := by exact_mod_cast hc 1 le_rfl (by omega)
    have hnum : (cf (fun i ↦ (c (i + 1) : ℝ))).nums K ≠ 0 :=
      (cf_nums_pos (a := fun i ↦ (c (i + 1) : ℝ)) (N := K)
        (fun i hi ↦ by exact_mod_cast hc (i + 1) (by omega) (by omega)) K le_rfl).ne'
    rw [cf_convs_succ (fun i ↦ (c i : ℝ)) K hnum]
    simp only [zero_add] at l1 l3 ⊢
    set y := (cf (fun i ↦ (c (i + 1) : ℝ))).convs K
    have hy : 1 ≤ y := hc1.trans l1
    have hy0 : 0 < y := by linarith
    have h1 : 0 < 1 / y := by positivity
    have h2 : 1 / y ≤ 1 := by rw [div_le_one hy0]; exact hy
    refine ⟨by linarith, by linarith, fun _ ↦ by linarith, fun h ↦ ?_⟩
    have hy1 : 1 < y := by
      rcases K with _ | K
      · have : c 1 ≠ 1 := fun h' ↦ h ⟨rfl, h'⟩
        have : (1 : ℝ) < c 1 := by
          have := hc 1 le_rfl le_rfl
          exact_mod_cast (show 1 < c 1 by omega)
        simpa [y] using this
      · exact lt_of_le_of_lt hc1 (l3 (by omega))
    have : 1 / y < 1 := by rw [div_lt_one hy0]; exact hy1
    linarith

/-- The integral part of `[c₀, …, c_K]` is `c₀`, unless `K = 1` and `c₁ = 1` (then `[c₀, 1] = c₀ + 1`). -/
lemma cf_floor_value {c : ℕ → ℤ} {K : ℕ} (hc : ∀ i, 1 ≤ i → i ≤ K → 0 < c i)
    (hK : ¬(K = 1 ∧ c 1 = 1)) : ⌊(cf (fun i ↦ (c i : ℝ))).convs K⌋ = c 0 := by
  obtain ⟨l1, -, -, l4⟩ := cf_value_bounds hc
  rw [Int.floor_eq_iff]
  exact ⟨l1, l4 hK⟩

/-- `[c₀, 1] = c₀ + 1`. -/
lemma cf_value_last_one {c : ℕ → ℤ} (h : c 1 = 1) :
    (cf (fun i ↦ (c i : ℝ))).convs 1 = c 0 + 1 := by
  rw [cf_convs]; simp [h]

/-- The complete quotient `a'ₙ = [aₙ, a_{n+1}, …, a_N]` and the identity
`[a₀, …, a_N] = [a₀, …, a_{n-1}, a'ₙ]` in the form `[a₀, …, a_N] = a₀ + 1/a'₁`. -/
lemma cf_value_succ {a : ℕ → ℤ} {N : ℕ} (hpos : ∀ i, 1 ≤ i → i ≤ N + 1 → 0 < a i) :
    (cf (fun i ↦ (a i : ℝ))).convs (N + 1) = a 0 + 1 / (cf (fun i ↦ (a (i + 1) : ℝ))).convs N := by
  have hnum : (cf (fun i ↦ (a (i + 1) : ℝ))).nums N ≠ 0 :=
    (cf_nums_pos (a := fun i ↦ (a (i + 1) : ℝ)) (N := N)
      (fun i hi ↦ by exact_mod_cast hpos (i + 1) (by omega) (by omega)) N le_rfl).ne'
  exact cf_convs_succ (fun i ↦ (a i : ℝ)) N hnum

/-- **Theorem 159.** The `n`-th complete quotient `a'ₙ = [aₙ, …, a_N]` of a simple continued fraction
satisfies `aₙ = ⌊a'ₙ⌋`, except that `a_{N-1} = ⌊a'_{N-1}⌋ - 1` when `a_N = 1`. -/
@[kb "hardywright2008" "Thm 159, p. 171"]
theorem cf_floor_completeQuotient {a : ℕ → ℤ} {N : ℕ} (hpos : ∀ i, 1 ≤ i → i ≤ N → 0 < a i)
    {n : ℕ} (hn : n ≤ N) :
    (¬(n + 1 = N ∧ a N = 1) → ⌊(cf (fun i ↦ (a (n + i) : ℝ))).convs (N - n)⌋ = a n) ∧
      (n + 1 = N → a N = 1 → ⌊(cf (fun i ↦ (a (n + i) : ℝ))).convs (N - n)⌋ - 1 = a n) := by
  have hc : ∀ i, 1 ≤ i → i ≤ N - n → 0 < a (n + i) := fun i h1 h2 ↦ hpos (n + i) (by omega) (by omega)
  refine ⟨fun h ↦ ?_, fun h1 h2 ↦ ?_⟩
  · have := cf_floor_value (c := fun i ↦ a (n + i)) hc (fun h' ↦ h ⟨by omega, by
      rw [← h'.2]; congr 1; try omega⟩)
    simpa using this
  · have hN : N - n = 1 := by omega
    rw [hN, cf_value_last_one (c := fun i ↦ a (n + i)) (by rw [← h2]; congr 1; try omega)]
    simp

/-- **Theorem 160.** If two finite simple continued fractions `[a₀, …, a_N]` and `[b₀, …, b_M]` have the
same value, and `a_N > 1`, `b_M > 1` (only needed when `N ≥ 1`, resp. `M ≥ 1`), then `M = N` and the
fractions are identical. -/
@[kb "hardywright2008" "Thm 160, p. 171"]
theorem cf_eq_of_value_eq {a b : ℕ → ℤ} {N M : ℕ} (ha : ∀ i, 1 ≤ i → i ≤ N → 0 < a i)
    (hb : ∀ i, 1 ≤ i → i ≤ M → 0 < b i) (haN : N = 0 ∨ 1 < a N) (hbM : M = 0 ∨ 1 < b M)
    (h : (cf (fun i ↦ (a i : ℝ))).convs N = (cf (fun i ↦ (b i : ℝ))).convs M) :
    M = N ∧ ∀ i ≤ N, a i = b i := by
  induction N generalizing a b M with
  | zero =>
    rcases M with _ | M
    · simp only [cf_convs_zero, Int.cast_inj] at h
      exact ⟨rfl, fun i hi ↦ by obtain rfl : i = 0 := (by omega); exact h⟩
    · exfalso
      obtain ⟨-, -, l3, l4⟩ := cf_value_bounds hb
      have h0 := l3 (by omega)
      have h1 := l4 (not_last_one hbM)
      rw [cf_convs_zero] at h
      rw [← h] at h0 h1
      have : b 0 < a 0 := by exact_mod_cast h0
      have : a 0 < b 0 + 1 := by exact_mod_cast h1
      omega
  | succ N ih =>
    rcases M with _ | M
    · exfalso
      obtain ⟨-, -, l3, l4⟩ := cf_value_bounds ha
      have h0 := l3 (by omega)
      have h1 := l4 (not_last_one haN)
      rw [h, cf_convs_zero] at h0 h1
      have : a 0 < b 0 := by exact_mod_cast h0
      have : b 0 < a 0 + 1 := by exact_mod_cast h1
      omega
    · -- equal integral parts
      have hfa := cf_floor_value ha (not_last_one haN)
      have hfb := cf_floor_value hb (not_last_one hbM)
      have h0 : a 0 = b 0 := by rw [← hfa, ← hfb, h]
      rw [cf_value_succ ha, cf_value_succ hb, h0] at h
      have h' := add_left_cancel h
      rw [one_div, one_div, inv_inj] at h'
      obtain ⟨hMN, hi⟩ := ih (a := fun i ↦ a (i + 1)) (b := fun i ↦ b (i + 1)) (M := M)
        (fun i h1 h2 ↦ ha (i + 1) (by omega) (by omega))
        (fun i h1 h2 ↦ hb (i + 1) (by omega) (by omega))
        (by rcases haN with h'' | h'' <;> [omega; exact Or.inr h''])
        (by rcases hbM with h'' | h'' <;> [omega; exact Or.inr h'']) h'
      refine ⟨by omega, fun i hi' ↦ ?_⟩
      rcases i with _ | i
      · exact h0
      · exact hi i (by omega)

/-- **Theorem 158.** If `x` is represented by a simple continued fraction with `N + 1` convergents, it is
also represented by one with `M + 1` convergents, where `M` and `N` have different parity: if `a_N ≥ 2`
(or `N = 0`), `[a₀, …, a_N] = [a₀, …, a_N - 1, 1]`, and if `a_N = 1`, `N ≥ 1`,
`[a₀, …, a_{N-1}, 1] = [a₀, …, a_{N-2}, a_{N-1} + 1]`. -/
@[kb "hardywright2008" "Thm 158, p. 170"]
theorem cf_exists_other_parity {a : ℕ → ℤ} {N : ℕ} (ha : ∀ i, 1 ≤ i → i ≤ N → 0 < a i) :
    ∃ (M : ℕ) (b : ℕ → ℤ), (M = N + 1 ∨ M + 1 = N) ∧ (∀ i, 1 ≤ i → i ≤ M → 0 < b i) ∧
      (cf (fun i ↦ (b i : ℝ))).convs M = (cf (fun i ↦ (a i : ℝ))).convs N := by
  by_cases hlast : N = 0 ∨ 1 < a N
  · -- split the last quotient
    refine ⟨N + 1, fun i ↦ if i < N then a i else if i = N then a N - 1 else 1, Or.inl rfl,
      fun i h1 h2 ↦ ?_, ?_⟩
    · by_cases hi : i < N
      · simp only [hi, ite_true]; exact ha i h1 hi.le
      · by_cases hiN : i = N
        · subst hiN; simp only [lt_irrefl, ite_false, ite_true]
          rcases hlast with h | h <;> omega
        · simp [hi, hiN]
    · obtain ⟨h1, h2⟩ := cf_nums_dens_split_last (K := ℝ) (N := N)
        (a := fun i ↦ (a i : ℝ)) (b := fun i ↦ ((if i < N then a i else if i = N then a N - 1 else 1 : ℤ) : ℝ))
        (fun i hi ↦ by simp [hi]) (by simp) (by simp)
      rw [cf_convs, cf_convs, h1, h2]
  · -- merge the last two quotients
    push Not at hlast
    obtain ⟨hN0, haN⟩ := hlast
    have haN1 : a N = 1 := by have := ha N (by omega) le_rfl; omega
    obtain ⟨K, rfl⟩ : ∃ K, N = K + 1 := ⟨N - 1, by omega⟩
    refine ⟨K, fun i ↦ if i < K then a i else a K + 1, Or.inr rfl, fun i h1 h2 ↦ ?_, ?_⟩
    · by_cases hi : i < K
      · simp only [hi, ite_true]; exact ha i h1 (by omega)
      · have := ha K (by omega) (by omega)
        have hiK : i = K := by omega
        subst hiK; simp only [lt_irrefl, ite_false]; omega
    · obtain ⟨h1, h2⟩ := cf_nums_dens_split_last (K := ℝ) (N := K)
        (a := fun i ↦ ((if i < K then a i else a K + 1 : ℤ) : ℝ)) (b := fun i ↦ (a i : ℝ))
        (fun i hi ↦ by simp [hi]) (by simp) (by simp [haN1])
      rw [cf_convs, cf_convs, h1, h2]

/-- **Theorem 161** (Hardy–Wright's proof by Euclid's algorithm). Every rational number is the value of
a finite simple continued fraction, whose last quotient may be taken greater than `1` (or the fraction has
a single quotient). -/
@[kb "hardywright2008" "Thm 161, p. 173"]
theorem exists_cf_eq_rat (x : ℚ) :
    ∃ (N : ℕ) (a : ℕ → ℤ), (∀ i, 1 ≤ i → i ≤ N → 0 < a i) ∧ (N = 0 ∨ 1 < a N) ∧
      (cf (fun i ↦ (a i : ℝ))).convs N = x := by
  induction h : x.den using Nat.strong_induction_on generalizing x with
  | _ d ih =>
    by_cases hfr : Int.fract x = 0
    · refine ⟨0, fun _ ↦ ⌊x⌋, fun i h1 h2 ↦ absurd h2 (by omega), Or.inl rfl, ?_⟩
      rw [Int.fract, sub_eq_zero] at hfr
      simp only [cf_convs, cf_nums_zero, cf_dens_zero, div_one]
      exact_mod_cast hfr.symm
    · have hf0 : 0 < Int.fract x := lt_of_le_of_ne (Int.fract_nonneg x) (Ne.symm hfr)
      have hf1 : Int.fract x < 1 := Int.fract_lt_one x
      set y := (Int.fract x)⁻¹ with hy
      have hy1 : 1 < y := by rw [hy]; exact one_lt_inv₀ hf0 |>.mpr hf1
      have hden : y.den < d := by
        rw [hy, Rat.den_inv_of_ne_zero hfr, ← h, ← Rat.den_intFract x]
        have h1 := Rat.num_lt_denom_iff.mpr hf1
        have h2 : 0 < (Int.fract x).num := Rat.num_pos.mpr hf0
        omega
      obtain ⟨K, c, hc, hcK, hcy⟩ := ih y.den hden y rfl
      have hfl := cf_floor_value hc (not_last_one hcK)
      have hc0 : 1 ≤ c 0 := by
        rw [← hfl, hcy, Int.le_floor]
        exact_mod_cast hy1.le
      refine ⟨K + 1, fun i ↦ if i = 0 then ⌊x⌋ else c (i - 1), fun i h1 h2 ↦ ?_, Or.inr ?_, ?_⟩
      · simp only [show i ≠ 0 by omega, ite_false]
        rcases (show i - 1 = 0 ∨ 1 ≤ i - 1 by omega) with h' | h'
        · rw [h']; omega
        · exact hc (i - 1) h' (by omega)
      · simp only [show K + 1 ≠ 0 by omega, ite_false, Nat.add_sub_cancel]
        rcases hcK with h'' | h''
        · subst h''
          have : (c 0 : ℝ) = y := by simpa [cf_convs] using hcy
          have : (1 : ℝ) < c 0 := by rw [this]; exact_mod_cast hy1
          exact_mod_cast this
        · exact h''
      · rw [cf_value_succ (fun i h1 h2 ↦ by
          simp only [show i ≠ 0 by omega, ite_false]
          rcases (show i - 1 = 0 ∨ 1 ≤ i - 1 by omega) with h' | h'
          · rw [h']; omega
          · exact hc (i - 1) h' (by omega))]
        simp only [ite_true, Nat.add_sub_cancel, Nat.add_eq_zero_iff, one_ne_zero, and_false,
          ite_false]
        rw [hcy, hy]
        push_cast
        rw [one_div, inv_inv, Int.fract, Rat.floor_cast]
        ring

/-- **Theorem 162.** A rational number `x` can be expressed as a finite simple continued fraction in just
two ways, one with an even and the other with an odd number of convergents; in one form the last quotient
is `1`, in the other it is greater than `1` (or the fraction has a single quotient). -/
@[kb "hardywright2008" "Thm 162, p. 174"]
theorem cf_rat_two_expansions (x : ℚ) :
    ∃ (N : ℕ) (a : ℕ → ℤ) (M : ℕ) (b : ℕ → ℤ),
      (∀ i, 1 ≤ i → i ≤ N → 0 < a i) ∧ (cf (fun i ↦ (a i : ℝ))).convs N = x ∧ (N = 0 ∨ 1 < a N) ∧
      (∀ i, 1 ≤ i → i ≤ M → 0 < b i) ∧ (cf (fun i ↦ (b i : ℝ))).convs M = x ∧ 1 ≤ M ∧ b M = 1 ∧
      M = N + 1 ∧
      ∀ (L : ℕ) (c : ℕ → ℤ), (∀ i, 1 ≤ i → i ≤ L → 0 < c i) →
        (cf (fun i ↦ (c i : ℝ))).convs L = x →
        (L = N ∧ ∀ i ≤ N, c i = a i) ∨ (L = M ∧ ∀ i ≤ M, c i = b i) := by
  obtain ⟨N, a, ha, haN, hax⟩ := exists_cf_eq_rat x
  set b : ℕ → ℤ := fun i ↦ if i < N then a i else if i = N then a N - 1 else 1 with hbdef
  have hb : ∀ i, 1 ≤ i → i ≤ N + 1 → 0 < b i := by
    intro i h1 h2
    by_cases hi : i < N
    · simp only [hbdef, hi, ite_true]; exact ha i h1 hi.le
    · by_cases hiN : i = N
      · subst hiN; simp only [hbdef, lt_irrefl, ite_false, ite_true]
        rcases haN with h | h <;> omega
      · simp [hbdef, hi, hiN]
  have hbx : (cf (fun i ↦ (b i : ℝ))).convs (N + 1) = x := by
    obtain ⟨h1, h2⟩ := cf_nums_dens_split_last (K := ℝ) (N := N)
      (a := fun i ↦ (a i : ℝ)) (b := fun i ↦ (b i : ℝ))
      (fun i hi ↦ by simp [hbdef, hi]) (by simp [hbdef]) (by simp [hbdef])
    rw [cf_convs, h1, h2, ← cf_convs, hax]
  refine ⟨N, a, N + 1, b, ha, hax, haN, hb, hbx, by omega, by simp [hbdef], rfl, ?_⟩
  intro L c hc hcx
  by_cases hcL : L = 0 ∨ 1 < c L
  · left
    obtain ⟨h1, h2⟩ := cf_eq_of_value_eq ha hc haN hcL (hax.trans hcx.symm)
    exact ⟨h1, fun i hi ↦ (h2 i hi).symm⟩
  · right
    push Not at hcL
    obtain ⟨hL0, hcL1⟩ := hcL
    have hcL1 : c L = 1 := by have := hc L (by omega) le_rfl; omega
    obtain ⟨K, rfl⟩ : ∃ K, L = K + 1 := ⟨L - 1, by omega⟩
    -- merge the last two quotients of `c`
    set c' : ℕ → ℤ := fun i ↦ if i < K then c i else c K + 1 with hc'def
    have hc' : ∀ i, 1 ≤ i → i ≤ K → 0 < c' i := by
      intro i h1 h2
      by_cases hi : i < K
      · simp only [hc'def, hi, ite_true]; exact hc i h1 (by omega)
      · have := hc K (by omega) (by omega)
        have hiK : i = K := by omega
        subst hiK; simp only [hc'def, lt_irrefl, ite_false]; omega
    have hc'x : (cf (fun i ↦ (c' i : ℝ))).convs K = x := by
      obtain ⟨h1, h2⟩ := cf_nums_dens_split_last (K := ℝ) (N := K)
        (a := fun i ↦ (c' i : ℝ)) (b := fun i ↦ (c i : ℝ))
        (fun i hi ↦ by simp [hc'def, hi]) (by simp [hc'def]) (by simp [hcL1])
      rw [cf_convs, ← h1, ← h2, ← cf_convs, hcx]
    have hc'K : K = 0 ∨ 1 < c' K := by
      rcases K with _ | K
      · exact Or.inl rfl
      · right; have := hc (K + 1) (by omega) (by omega); simp only [hc'def, lt_irrefl, ite_false]
        omega
    obtain ⟨hKN, hi⟩ := cf_eq_of_value_eq ha hc' haN hc'K (hax.trans hc'x.symm)
    subst hKN
    refine ⟨rfl, fun i hi' ↦ ?_⟩
    by_cases h1 : i < K
    · have := hi i h1.le; simp only [hc'def, h1, ite_true] at this
      simp only [hbdef, h1, ite_true]; exact this.symm
    · by_cases h2 : i = K
      · subst h2
        have := hi i le_rfl; simp only [hc'def, lt_irrefl, ite_false] at this
        simp only [hbdef, lt_irrefl, ite_false, ite_true]; omega
      · have h3 : i = K + 1 := by omega
        subst h3; simp [hbdef, hcL1]

end Value

end NTKB.HardyWright
