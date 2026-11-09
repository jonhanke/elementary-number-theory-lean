/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Algebra.ContinuedFractions.Determinant
import Mathlib.Algebra.ContinuedFractions.ConvergentsEquiv
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Seq.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NTKB.Attr

/-!
# Continued fractions with given quotients (Hardy–Wright, Chapter X, §§ 10.1 to 10.3)

Hardy and Wright study the continued fraction `[a₀, a₁, a₂, …] = a₀ + 1/(a₁ + 1/(a₂ + ⋯))` for an
*arbitrary* sequence of quotients `a₀, a₁, …`. We encode it as Mathlib's generalized continued fraction
`NTKB.HardyWright.cf a` with head `a 0` and partial numerators all equal to `1`; this is only a constructor,
the convergents `pₙ / qₙ` are Mathlib's `GenContFract.nums`, `GenContFract.dens` and `GenContFract.convs`.
The finite continued fraction `[a₀, a₁, …, a_N]` has value `(cf a).convs N`, since the `n`-th convergent
only depends on `a₀, …, aₙ` (`convs_congr`).

* Theorem 150: `pₙ qₙ₋₁ - pₙ₋₁ qₙ = (-1)ⁿ⁻¹`.
* Theorem 151: `pₙ qₙ₋₂ - pₙ₋₂ qₙ = (-1)ⁿ aₙ`.
* Theorem 152: when `a₁, …, a_N > 0`, the even convergents increase strictly, the odd ones decrease strictly.
* Theorem 153: every odd convergent is greater than every even convergent.
* Theorem 154: the value lies above every even and below every odd convergent (other than itself).
-/

namespace NTKB.HardyWright

open GenContFract

variable {K : Type*}

section One

variable [One K]

/-- The continued fraction `a₀ + 1/(a₁ + 1/(a₂ + ⋯))` with quotients `a₀, a₁, a₂, …`, as a Mathlib
generalized continued fraction whose partial numerators are all `1` (Hardy–Wright, (10.1.1)). -/
def cf (a : ℕ → K) : GenContFract K :=
  ⟨a 0, Stream'.Seq.ofStream fun n ↦ ⟨1, a (n + 1)⟩⟩

@[simp] lemma cf_h (a : ℕ → K) : (cf a).h = a 0 := rfl

@[simp] lemma cf_s_get? (a : ℕ → K) (n : ℕ) : (cf a).s.get? n = some ⟨1, a (n + 1)⟩ := rfl

lemma cf_not_terminatedAt (a : ℕ → K) (n : ℕ) : ¬(cf a).TerminatedAt n := by
  simp [terminatedAt_iff_s_none]

lemma cf_isSimpContFract (a : ℕ → K) : (cf a).IsSimpContFract := by
  intro n a' h
  simp only [partNums, Stream'.Seq.map_get?, cf_s_get?, Option.map_some, Option.some.injEq] at h
  exact h.symm

end One

section Field

variable [Field K] (a : ℕ → K)

@[simp] lemma cf_nums_zero : (cf a).nums 0 = a 0 := zeroth_num_eq_h

@[simp] lemma cf_dens_zero : (cf a).dens 0 = 1 := zeroth_den_eq_one

@[simp] lemma cf_nums_one : (cf a).nums 1 = a 1 * a 0 + 1 := by
  rw [first_num_eq (cf_s_get? a 0)]; simp

@[simp] lemma cf_dens_one : (cf a).dens 1 = a 1 := by
  rw [first_den_eq (cf_s_get? a 0)]

/-- The recurrence `pₙ = aₙ pₙ₋₁ + pₙ₋₂` (Hardy–Wright (10.2.1)). -/
lemma cf_nums_add_two (n : ℕ) :
    (cf a).nums (n + 2) = a (n + 2) * (cf a).nums (n + 1) + (cf a).nums n := by
  rw [nums_recurrence (cf_s_get? a (n + 1)) rfl rfl]; simp

/-- The recurrence `qₙ = aₙ qₙ₋₁ + qₙ₋₂` (Hardy–Wright (10.2.2)). -/
lemma cf_dens_add_two (n : ℕ) :
    (cf a).dens (n + 2) = a (n + 2) * (cf a).dens (n + 1) + (cf a).dens n := by
  rw [dens_recurrence (cf_s_get? a (n + 1)) rfl rfl]; simp

lemma cf_convs (n : ℕ) : (cf a).convs n = (cf a).nums n / (cf a).dens n := conv_eq_num_div_den

/-- The `n`-th numerator and denominator only depend on `a₀, …, aₙ`. -/
lemma cf_nums_dens_congr {a b : ℕ → K} {N : ℕ} (h : ∀ i ≤ N, a i = b i) :
    ∀ n ≤ N, (cf a).nums n = (cf b).nums n ∧ (cf a).dens n = (cf b).dens n := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, hn, ih with
    | 0, _, _ => simp [h 0 (Nat.zero_le _)]
    | 1, hn, _ => simp [h 0 (Nat.zero_le _), h 1 hn]
    | n + 2, hn, ih =>
      obtain ⟨h1, h1'⟩ := ih (n + 1) (by omega) (by omega)
      obtain ⟨h0, h0'⟩ := ih n (by omega) (by omega)
      simp only [cf_nums_add_two, cf_dens_add_two, h1, h1', h0, h0', h (n + 2) hn, and_self]

/-- The `n`-th convergent only depends on `a₀, …, aₙ`. -/
lemma convs_congr {a b : ℕ → K} {n : ℕ} (h : ∀ i ≤ n, a i = b i) :
    (cf a).convs n = (cf b).convs n := by
  obtain ⟨h1, h2⟩ := cf_nums_dens_congr h n le_rfl
  rw [cf_convs, cf_convs, h1, h2]

/-- **Theorem 150** in the form `pₙ₊₁ qₙ - pₙ qₙ₊₁ = (-1)ⁿ` (Hardy–Wright (10.2.5), with `n + 1` for `n`). -/
@[kb "hardywright2008" "Thm 150, p. 167"]
theorem cf_nums_mul_dens_sub (n : ℕ) :
    (cf a).nums (n + 1) * (cf a).dens n - (cf a).nums n * (cf a).dens (n + 1) = (-1) ^ n := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [cf_nums_add_two, cf_dens_add_two, pow_succ, ← ih]; ring

/-- **Theorem 151** in the form `pₙ₊₂ qₙ - pₙ qₙ₊₂ = (-1)ⁿ aₙ₊₂` (Hardy–Wright (10.2.7), with `n + 2` for
`n`). -/
@[kb "hardywright2008" "Thm 151, p. 168"]
theorem cf_nums_mul_dens_sub_two (n : ℕ) :
    (cf a).nums (n + 2) * (cf a).dens n - (cf a).nums n * (cf a).dens (n + 2) =
      (-1) ^ n * a (n + 2) := by
  rw [cf_nums_add_two, cf_dens_add_two, ← cf_nums_mul_dens_sub]; ring

end Field

section Ordered

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K] {a : ℕ → K} {N : ℕ}

/-- If `a₁, …, aₙ > 0` then `qₙ > 0`, and `qₙ ≥ qₙ₋₁`-type facts follow; here: `qₙ > 0`. -/
lemma cf_dens_pos (hpos : ∀ i, 1 ≤ i → i ≤ N → 0 < a i) : ∀ n ≤ N, 0 < (cf a).dens n := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, hn, ih with
    | 0, _, _ => simp
    | 1, hn, _ => simpa using hpos 1 le_rfl hn
    | n + 2, hn, ih =>
      rw [cf_dens_add_two]
      exact add_pos (mul_pos (hpos (n + 2) (by omega) hn) (ih (n + 1) (by omega) (by omega)))
        (ih n (by omega) (by omega))

/-- `xₙ₊₁ - xₙ = (-1)ⁿ / (qₙ qₙ₊₁)` (Hardy–Wright (10.2.6)). -/
lemma cf_convs_succ_sub (hpos : ∀ i, 1 ≤ i → i ≤ N → 0 < a i) {n : ℕ} (hn : n + 1 ≤ N) :
    (cf a).convs (n + 1) - (cf a).convs n = (-1) ^ n / ((cf a).dens n * (cf a).dens (n + 1)) := by
  have h0 := (cf_dens_pos hpos n (by omega)).ne'
  have h1 := (cf_dens_pos hpos (n + 1) hn).ne'
  rw [cf_convs, cf_convs, ← cf_nums_mul_dens_sub a]
  field_simp

/-- `xₙ₊₂ - xₙ = (-1)ⁿ aₙ₊₂ / (qₙ qₙ₊₂)` (Hardy–Wright (10.2.8)). -/
lemma cf_convs_add_two_sub (hpos : ∀ i, 1 ≤ i → i ≤ N → 0 < a i) {n : ℕ} (hn : n + 2 ≤ N) :
    (cf a).convs (n + 2) - (cf a).convs n =
      (-1) ^ n * a (n + 2) / ((cf a).dens n * (cf a).dens (n + 2)) := by
  have h0 := (cf_dens_pos hpos n (by omega)).ne'
  have h2 := (cf_dens_pos hpos (n + 2) hn).ne'
  rw [cf_convs, cf_convs, ← cf_nums_mul_dens_sub_two a]
  field_simp

/-- **Theorem 152** (even convergents). If `a₁, …, a_N > 0`, the even convergents `x₀, x₂, …` (up to
`x_N`) increase strictly. -/
@[kb "hardywright2008" "Thm 152, p. 168"]
theorem cf_convs_even_lt (hpos : ∀ i, 1 ≤ i → i ≤ N → 0 < a i) {m n : ℕ} (hmn : m < n)
    (hn : 2 * n ≤ N) : (cf a).convs (2 * m) < (cf a).convs (2 * n) := by
  induction n, hmn using Nat.le_induction with
  | base =>
    have := cf_convs_add_two_sub hpos (n := 2 * m) (by omega)
    have h0 := cf_dens_pos hpos (2 * m) (by omega)
    have h2 := cf_dens_pos hpos (2 * m + 2) (by omega)
    have ha := hpos (2 * m + 2) (by omega) (by omega)
    rw [show 2 * (m + 1) = 2 * m + 2 by ring]
    rw [pow_mul, neg_one_sq, one_pow, one_mul] at this
    have : 0 < (cf a).convs (2 * m + 2) - (cf a).convs (2 * m) := by rw [this]; exact div_pos (by assumption) (mul_pos h0 h2)
    linarith
  | succ n hmn ih =>
    have := cf_convs_add_two_sub hpos (n := 2 * n) (by omega)
    have h0 := cf_dens_pos hpos (2 * n) (by omega)
    have h2 := cf_dens_pos hpos (2 * n + 2) (by omega)
    have ha := hpos (2 * n + 2) (by omega) (by omega)
    rw [pow_mul, neg_one_sq, one_pow, one_mul] at this
    have : 0 < (cf a).convs (2 * n + 2) - (cf a).convs (2 * n) := by rw [this]; exact div_pos (by assumption) (mul_pos h0 h2)
    rw [show 2 * (n + 1) = 2 * n + 2 by ring]
    linarith [ih (by omega)]

/-- **Theorem 152** (odd convergents). If `a₁, …, a_N > 0`, the odd convergents `x₁, x₃, …` (up to
`x_N`) decrease strictly. -/
@[kb "hardywright2008" "Thm 152, p. 168"]
theorem cf_convs_odd_lt (hpos : ∀ i, 1 ≤ i → i ≤ N → 0 < a i) {m n : ℕ} (hmn : m < n)
    (hn : 2 * n + 1 ≤ N) : (cf a).convs (2 * n + 1) < (cf a).convs (2 * m + 1) := by
  induction n, hmn using Nat.le_induction with
  | base =>
    have := cf_convs_add_two_sub hpos (n := 2 * m + 1) (by omega)
    have h0 := cf_dens_pos hpos (2 * m + 1) (by omega)
    have h2 := cf_dens_pos hpos (2 * m + 1 + 2) (by omega)
    have ha := hpos (2 * m + 1 + 2) (by omega) (by omega)
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by ring]
    rw [pow_succ, pow_mul, neg_one_sq, one_pow, one_mul] at this
    have : 0 < (cf a).convs (2 * m + 1) - (cf a).convs (2 * m + 1 + 2) := by
      rw [← neg_sub, this]
      rw [neg_one_mul, neg_div, neg_neg]
      exact div_pos ha (mul_pos h0 h2)
    linarith
  | succ n hmn ih =>
    have := cf_convs_add_two_sub hpos (n := 2 * n + 1) (by omega)
    have h0 := cf_dens_pos hpos (2 * n + 1) (by omega)
    have h2 := cf_dens_pos hpos (2 * n + 1 + 2) (by omega)
    have ha := hpos (2 * n + 1 + 2) (by omega) (by omega)
    rw [pow_succ, pow_mul, neg_one_sq, one_pow, one_mul] at this
    have : 0 < (cf a).convs (2 * n + 1) - (cf a).convs (2 * n + 1 + 2) := by
      rw [← neg_sub, this]
      rw [neg_one_mul, neg_div, neg_neg]
      exact div_pos ha (mul_pos h0 h2)
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by ring]
    linarith [ih (by omega)]

lemma cf_convs_even_le (hpos : ∀ i, 1 ≤ i → i ≤ N → 0 < a i) {m n : ℕ} (hmn : m ≤ n)
    (hn : 2 * n ≤ N) : (cf a).convs (2 * m) ≤ (cf a).convs (2 * n) := by
  rcases hmn.lt_or_eq with h | rfl
  · exact (cf_convs_even_lt hpos h hn).le
  · exact le_rfl

lemma cf_convs_odd_le (hpos : ∀ i, 1 ≤ i → i ≤ N → 0 < a i) {m n : ℕ} (hmn : m ≤ n)
    (hn : 2 * n + 1 ≤ N) : (cf a).convs (2 * n + 1) ≤ (cf a).convs (2 * m + 1) := by
  rcases hmn.lt_or_eq with h | rfl
  · exact (cf_convs_odd_lt hpos h hn).le
  · exact le_rfl

/-- An odd convergent exceeds the preceding even one: `x₂ₙ < x₂ₙ₊₁`. -/
lemma cf_convs_even_lt_succ (hpos : ∀ i, 1 ≤ i → i ≤ N → 0 < a i) {n : ℕ} (hn : 2 * n + 1 ≤ N) :
    (cf a).convs (2 * n) < (cf a).convs (2 * n + 1) := by
  have := cf_convs_succ_sub hpos (n := 2 * n) hn
  have h0 := cf_dens_pos hpos (2 * n) (by omega)
  have h1 := cf_dens_pos hpos (2 * n + 1) hn
  rw [pow_mul, neg_one_sq, one_pow] at this
  have : 0 < (cf a).convs (2 * n + 1) - (cf a).convs (2 * n) := by
    rw [this]; exact div_pos one_pos (mul_pos h0 h1)
  linarith

/-- An odd convergent exceeds the following even one: `x₂ₙ₊₂ < x₂ₙ₊₁`. -/
lemma cf_convs_even_succ_lt (hpos : ∀ i, 1 ≤ i → i ≤ N → 0 < a i) {n : ℕ} (hn : 2 * n + 2 ≤ N) :
    (cf a).convs (2 * n + 2) < (cf a).convs (2 * n + 1) := by
  have := cf_convs_succ_sub hpos (n := 2 * n + 1) hn
  have h0 := cf_dens_pos hpos (2 * n + 1) (by omega)
  have h1 := cf_dens_pos hpos (2 * n + 1 + 1) hn
  rw [pow_succ, pow_mul, neg_one_sq, one_pow, one_mul] at this
  have : (cf a).convs (2 * n + 1 + 1) - (cf a).convs (2 * n + 1) < 0 := by
    rw [this, neg_div]; simp only [Left.neg_neg_iff]; exact div_pos one_pos (mul_pos h0 h1)
  linarith

/-- **Theorem 153.** If `a₁, …, a_N > 0`, every odd convergent is greater than every even convergent. -/
@[kb "hardywright2008" "Thm 153, p. 168"]
theorem cf_convs_even_lt_odd (hpos : ∀ i, 1 ≤ i → i ≤ N → 0 < a i) {m n : ℕ} (hm : 2 * m ≤ N)
    (hn : 2 * n + 1 ≤ N) : (cf a).convs (2 * m) < (cf a).convs (2 * n + 1) := by
  rcases le_or_gt m n with h | h
  · exact (cf_convs_even_le hpos h (by omega)).trans_lt (cf_convs_even_lt_succ hpos hn)
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have := cf_convs_even_succ_lt hpos (n := k) (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 by ring]
    exact this.trans_le (cf_convs_odd_le hpos (by omega) (by omega))

/-- **Theorem 154.** If `a₁, …, a_N > 0`, the value `x = x_N = [a₀, …, a_N]` is greater than every even
convergent and less than every odd convergent, except that `x_N` itself equals `x`. -/
@[kb "hardywright2008" "Thm 154, p. 168"]
theorem cf_convs_even_lt_value_lt_odd (hpos : ∀ i, 1 ≤ i → i ≤ N → 0 < a i) :
    (∀ m, 2 * m < N → (cf a).convs (2 * m) < (cf a).convs N) ∧
      (∀ n, 2 * n + 1 < N → (cf a).convs N < (cf a).convs (2 * n + 1)) := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' N
  · exact ⟨fun m hm ↦ cf_convs_even_lt hpos (by omega) le_rfl,
      fun n hn ↦ cf_convs_even_lt_odd hpos le_rfl (by omega)⟩
  · exact ⟨fun m hm ↦ cf_convs_even_lt_odd hpos (by omega) le_rfl,
      fun n hn ↦ cf_convs_odd_lt hpos (by omega) le_rfl⟩

end Ordered

end NTKB.HardyWright
