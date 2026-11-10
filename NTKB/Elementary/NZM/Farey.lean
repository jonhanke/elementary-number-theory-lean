/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Attr
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Int.Order.Basic

/-!
# Farey fractions (Niven–Zuckerman–Montgomery, §§ 6.1–6.2)

Fractions `a/b` are encoded by integer pairs with `b > 0`, and inequalities between fractions are
expressed by cross-multiplication.

* Theorem 6.4: if `a'b - ab' = 1` and `a/b < x/y < a'/b'`, then `y ≥ b + b'`, with equality only
  for `x = a + a'`.
* Theorem 6.1 (Farey form): adjacent fractions of order `n` satisfy `a'b - ab' = 1` and
  `b + b' > n`.
* Theorem 6.7: the gaps between a Farey fraction and the mediant are `1/(b(b+d)) ≤ 1/(b(n+1))`.
-/

namespace NTKB.NZM

/-- **Corollary 6.2 (part).** If `a'b - ab' = 1` then `gcd(a, b) = 1`. -/
theorem isCoprime_left_of_det {a b a' b' : ℤ} (hdet : a' * b - a * b' = 1) : IsCoprime a b :=
  ⟨-b', a', by linarith⟩

/-- **Corollary 6.2 (part).** If `a'b - ab' = 1` then `gcd(a', b') = 1`. -/
theorem isCoprime_right_of_det {a b a' b' : ℤ} (hdet : a' * b - a * b' = 1) : IsCoprime a' b' :=
  ⟨b, -a, by linarith⟩

/-- **Theorem 6.4.** If `a'b - ab' = 1`, `b, b' > 0`, and `a/b < x/y < a'/b'` with `y > 0`, then
`y ≥ b + b'`, and `y = b + b'` only if `x = a + a'`. -/
@[kb "nivenzuckermanmontgomery" "Thm 6.4, p. 298"]
theorem mediant_least_denominator {a b a' b' x y : ℤ} (hb : 0 < b) (hb' : 0 < b')
    (hdet : a' * b - a * b' = 1) (hy : 0 < y) (h1 : a * y < x * b) (h2 : x * b' < a' * y) :
    b + b' ≤ y ∧ (y = b + b' → x = a + a') := by
  have hp1 : 1 ≤ a' * y - b' * x := by linarith
  have hq1 : 1 ≤ b * x - a * y := by linarith
  have hyeq : y = b * (a' * y - b' * x) + b' * (b * x - a * y) := by
    linear_combination (-y) * hdet
  have k1 := mul_le_mul_of_nonneg_left hp1 hb.le
  have k2 := mul_le_mul_of_nonneg_left hq1 hb'.le
  refine ⟨by linarith, fun hyb => ?_⟩
  -- `b (p - 1) + b' (q - 1) = 0` with both terms `≥ 0`
  have hz : b * (a' * y - b' * x - 1) + b' * (b * x - a * y - 1) = 0 := by linarith
  have h3 : 0 ≤ b * (a' * y - b' * x - 1) := mul_nonneg hb.le (by linarith)
  have h4 : 0 ≤ b' * (b * x - a * y - 1) := mul_nonneg hb'.le (by linarith)
  have e2 : a' * y - b' * x = 1 := by
    have : b * (a' * y - b' * x - 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hb.ne'
    · linarith
  have e1 : b * x - a * y = 1 := by
    have : b' * (b * x - a * y - 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hb'.ne'
    · linarith
  have : (b + b') * (x - a - a') = 0 := by
    subst hyb
    linear_combination e1 - e2
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · linarith

/-- **Theorem 6.1 (Farey form).** Let `a/b < a'/b'` be reduced fractions with denominators at most
`n`, with no fraction of denominator at most `n` strictly between them (i.e. adjacent in the Farey
sequence of order `n`).  Then `a'b - ab' = 1` and `b + b' > n`. -/
@[kb "nivenzuckermanmontgomery" "Thm 6.1, p. 298"]
theorem farey_adjacent {n : ℕ} {a b a' b' : ℤ} (hb : 0 < b) (hbn : b ≤ n) (hb' : 0 < b')
    (hb'n : b' ≤ n) (hab : IsCoprime a b) (hab' : IsCoprime a' b') (hlt : a * b' < a' * b)
    (hadj : ∀ x y : ℤ, 0 < y → y ≤ n → ¬ (a * y < x * b ∧ x * b' < a' * y)) :
    a' * b - a * b' = 1 ∧ (n : ℤ) < b + b' := by
  obtain ⟨u, v, huv⟩ := hab
  -- solve `b x - a y = 1` with `n - b < y ≤ n`
  have hdiv : b * (((n : ℤ) + u) / b) + ((n : ℤ) + u) % b = n + u := by rw [Int.emod_def]; ring
  have hr0 : 0 ≤ ((n : ℤ) + u) % b := Int.emod_nonneg _ hb.ne'
  have hrb : ((n : ℤ) + u) % b < b := Int.emod_lt_of_pos _ hb
  generalize ((n : ℤ) + u) / b = t at hdiv
  generalize ((n : ℤ) + u) % b = r at hdiv hr0 hrb
  obtain ⟨y, hy⟩ : ∃ y : ℤ, y = n - r := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : ℤ, x = v + a * t := ⟨_, rfl⟩
  have hcop : b * x - a * y = 1 := by
    have : y = b * t - u := by linarith
    rw [this, hx]; linear_combination huv
  have hyn : y ≤ n := by linarith
  have hyb : (n : ℤ) < b + y := by linarith
  have hypos : 0 < y := by linarith
  have hlt1 : a * y < x * b := by linarith [show x * b = b * x by ring]
  have hna := hadj x y hypos hyn
  have hge : a' * y ≤ x * b' := by
    by_contra hcon
    exact hna ⟨hlt1, by linarith⟩
  -- equality
  have heq : x * b' = a' * y := by
    by_contra hne
    have hgt : 1 ≤ x * b' - a' * y := by
      have : a' * y < x * b' := lt_of_le_of_ne hge (Ne.symm hne)
      linarith
    have hdet1 : 1 ≤ a' * b - a * b' := by linarith
    have k1 : b * 1 ≤ b * (x * b' - a' * y) := mul_le_mul_of_nonneg_left hgt hb.le
    have k2 : y * 1 ≤ y * (a' * b - a * b') := mul_le_mul_of_nonneg_left hdet1 hypos.le
    have k3 : b' = b * (x * b' - a' * y) + y * (a' * b - a * b') := by
      linear_combination (-b') * hcop
    linarith
  -- both fractions are reduced, so `y = b'` and `x = a'`
  have hxy : IsCoprime x y := ⟨b, -a, by linear_combination hcop⟩
  have hd1 : y ∣ b' := IsCoprime.dvd_of_dvd_mul_left hxy.symm ⟨a', by linear_combination heq⟩
  have hd2 : b' ∣ y := IsCoprime.dvd_of_dvd_mul_left hab'.symm ⟨x, by linear_combination -heq⟩
  have h3 : y ≤ b' := Int.le_of_dvd hb' hd1
  have h4 : b' ≤ y := Int.le_of_dvd hypos hd2
  have hyb' : y = b' := le_antisymm h3 h4
  have hxa : x = a' := by
    rw [hyb'] at heq
    exact mul_right_cancel₀ hb'.ne' heq
  rw [hyb', hxa] at hcop
  exact ⟨by linear_combination hcop, by rw [← hyb']; exact hyb⟩

/-- **Theorem 6.7 (gaps).** If `c b - a d = 1` with `b, d > 0`, then the mediant
`(a+c)/(b+d)` is at distance exactly `1/(b(b+d))` from `a/b` and `1/(d(b+d))` from `c/d`. -/
theorem mediant_sub_eq {a b c d : ℤ} (hb : 0 < b) (hd : 0 < d) (hdet : c * b - a * d = 1) :
    ((a + c : ℚ) / (b + d) - a / b = 1 / (b * (b + d))) ∧
    ((c : ℚ) / d - (a + c) / (b + d) = 1 / (d * (b + d))) := by
  have hb' : (0 : ℚ) < b := by exact_mod_cast hb
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  have hdet' : (c : ℚ) * b - a * d = 1 := by exact_mod_cast hdet
  have hbd : (0 : ℚ) < b + d := by positivity
  constructor
  · have : ((a + c : ℚ) / (b + d) - a / b) = (c * b - a * d) / (b * (b + d)) := by
      field_simp
      ring
    rw [this, hdet']
  · have : ((c : ℚ) / d - (a + c) / (b + d)) = (c * b - a * d) / (d * (b + d)) := by
      field_simp
      ring
    rw [this, hdet']

/-- **Theorem 6.7.** If `a/b` and `c/d` are adjacent Farey fractions of order `n` (so
`c b - a d = 1` and `b + d > n`), then
`(a+c)/(b+d) - a/b = 1/(b(b+d)) ≤ 1/(b(n+1))` and
`c/d - (a+c)/(b+d) = 1/(d(b+d)) ≤ 1/(d(n+1))`. -/
theorem mediant_sub_le {n : ℕ} {a b c d : ℤ} (hb : 0 < b) (hd : 0 < d)
    (hdet : c * b - a * d = 1) (hn : (n : ℤ) < b + d) :
    ((a + c : ℚ) / (b + d) - a / b ≤ 1 / (b * (n + 1))) ∧
    ((c : ℚ) / d - (a + c) / (b + d) ≤ 1 / (d * (n + 1))) := by
  obtain ⟨e1, e2⟩ := mediant_sub_eq hb hd hdet
  have hb' : (0 : ℚ) < b := by exact_mod_cast hb
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  have hn' : (n : ℚ) + 1 ≤ b + d := by
    have : (n : ℤ) + 1 ≤ b + d := hn
    exact_mod_cast this
  have hn0 : (0 : ℚ) < (n : ℚ) + 1 := by positivity
  rw [e1, e2]
  constructor
  · apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul_of_nonneg_left hn' hb'.le
  · apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul_of_nonneg_left hn' hd'.le

/-- **Theorem 6.7.** If `a/b < c/d` are Farey fractions of order `n` (reduced, denominators in
`[1, n]`) with no other Farey fraction of order `n` between them, then
`(a+c)/(b+d) - a/b = 1/(b(b+d)) ≤ 1/(b(n+1))` and `c/d - (a+c)/(b+d) = 1/(d(b+d)) ≤ 1/(d(n+1))`. -/
@[kb "nivenzuckermanmontgomery" "Thm 6.7, p. 301"]
theorem farey_mediant_gap {n : ℕ} {a b c d : ℤ} (hb : 0 < b) (hbn : b ≤ n) (hd : 0 < d)
    (hdn : d ≤ n) (hab : IsCoprime a b) (hcd : IsCoprime c d) (hlt : a * d < c * b)
    (hadj : ∀ x y : ℤ, 0 < y → y ≤ n → ¬ (a * y < x * b ∧ x * d < c * y)) :
    ((a + c : ℚ) / (b + d) - a / b = 1 / (b * (b + d)) ∧
        (a + c : ℚ) / (b + d) - a / b ≤ 1 / (b * (n + 1))) ∧
      ((c : ℚ) / d - (a + c) / (b + d) = 1 / (d * (b + d)) ∧
        (c : ℚ) / d - (a + c) / (b + d) ≤ 1 / (d * (n + 1))) := by
  obtain ⟨hdet, hn⟩ := farey_adjacent hb hbn hd hdn hab hcd hlt hadj
  obtain ⟨e1, e2⟩ := mediant_sub_eq hb hd hdet
  obtain ⟨l1, l2⟩ := mediant_sub_le hb hd hdet hn
  exact ⟨⟨e1, l1⟩, ⟨e2, l2⟩⟩

end NTKB.NZM
