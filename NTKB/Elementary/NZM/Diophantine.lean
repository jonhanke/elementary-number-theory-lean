/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Attr
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Some Diophantine equations (Niven–Zuckerman–Montgomery, § 5.4)

* Theorem 5.6: `15 x² - 7 y² = 9` has no integer solutions.  Reduce mod 3 to get `3 ∣ y`, then
  `9 ∣ 15 x²` gives `3 ∣ x`; dividing by 9 yields `15 x₁² - 7 y₁² = 1`, impossible mod 3.
* Theorem 5.7: `x³ + 2y³ + 4z³ = 9w³` has only the trivial solution.  Cubes are `0, ±1` mod 9, so
  any solution has `3 ∣ x, y, z`, hence `3 ∣ w`; infinite descent finishes.
* Theorem 5.8: `y² = x³ + 7` has no integer solutions.  Even `x` fails mod 8; for odd `x` one gets
  `x ≡ 1 (mod 4)`, so `x² - 2x + 4 ≡ 3 (mod 4)` has a prime factor `q ≡ 3 (mod 4)` dividing
  `y² + 1`, contradicting that `-1` is not a square mod `q`.
* Theorem 5.9: `x⁴ + x³ + x² + x + 1 = y²` is squeezed between consecutive squares
  `(2x²+x)²` and `(2x²+x+1)²` (after multiplying by 4) unless `-1 ≤ x ≤ 3`; the remaining
  values are checked by hand.
-/

namespace NTKB.NZM

/-- **Theorem 5.6.** The equation `15 x² - 7 y² = 9` has no solution in integers. -/
@[kb "nivenzuckermanmontgomery" "Thm 5.6, p. 234"]
theorem no_solution_fifteen_sq_sub_seven_sq : ¬ ∃ x y : ℤ, 15 * x ^ 2 - 7 * y ^ 2 = 9 := by
  rintro ⟨x, y, h⟩
  -- `3 ∣ 7 y²`, hence `3 ∣ y`
  have hy : (3 : ℤ) ∣ y := by
    have : (3 : ℤ) ∣ 7 * y ^ 2 := ⟨5 * x ^ 2 - 3, by linarith⟩
    rcases Int.prime_three.dvd_or_dvd this with h7 | h7
    · norm_num at h7
    · exact Int.prime_three.dvd_of_dvd_pow h7
  obtain ⟨b, rfl⟩ := hy
  -- then `9 ∣ 15 x²`, hence `3 ∣ x`
  have hx : (3 : ℤ) ∣ x := by
    have : (3 : ℤ) ∣ 5 * x ^ 2 := ⟨1 + 7 * b ^ 2, by linarith⟩
    rcases Int.prime_three.dvd_or_dvd this with h5 | h5
    · norm_num at h5
    · exact Int.prime_three.dvd_of_dvd_pow h5
  obtain ⟨a, rfl⟩ := hx
  -- `15 a² - 7 b² = 1` has no solution modulo `3`
  have h1 : 15 * a ^ 2 - 7 * b ^ 2 = 1 := by linarith
  have h3 := congrArg (Int.cast : ℤ → ZMod 3) h1
  push_cast at h3
  revert h3
  generalize (a : ZMod 3) = A
  generalize (b : ZMod 3) = B
  revert A B
  decide

/-- Cubes mod 9: a sum `a³ + 2b³ + 4c³` vanishing in `ZMod 9` forces `3 ∣ a, b, c`. -/
private lemma zmod9_cubes : ∀ a b c : ZMod 9, a ^ 3 + 2 * b ^ 3 + 4 * c ^ 3 = 0 →
    3 * a = 0 ∧ 3 * b = 0 ∧ 3 * c = 0 := by decide

private lemma three_dvd_of_cubes {x y z : ℤ} (h : 9 ∣ x ^ 3 + 2 * y ^ 3 + 4 * z ^ 3) :
    3 ∣ x ∧ 3 ∣ y ∧ 3 ∣ z := by
  have h0 : (((x ^ 3 + 2 * y ^ 3 + 4 * z ^ 3 : ℤ)) : ZMod 9) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h
  push_cast at h0
  obtain ⟨ha, hb, hc⟩ := zmod9_cubes _ _ _ h0
  have h9 : ∀ t : ℤ, ((3 * t : ℤ) : ZMod 9) = 0 → 3 ∣ t := by
    intro t ht
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at ht
    omega
  exact ⟨h9 x (by push_cast; exact ha), h9 y (by push_cast; exact hb), h9 z (by push_cast; exact hc)⟩

private lemma descent : ∀ n : ℕ, ∀ x y z w : ℤ,
    x.natAbs + y.natAbs + z.natAbs + w.natAbs = n →
    x ^ 3 + 2 * y ^ 3 + 4 * z ^ 3 = 9 * w ^ 3 → x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x y z w hn h
    obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩, ⟨c, rfl⟩⟩ := three_dvd_of_cubes ⟨w ^ 3, h⟩
    have h3 : (3 : ℤ) ∣ w ^ 3 := ⟨a ^ 3 + 2 * b ^ 3 + 4 * c ^ 3, by linarith⟩
    obtain ⟨d, rfl⟩ := Int.prime_three.dvd_of_dvd_pow h3
    have h' : a ^ 3 + 2 * b ^ 3 + 4 * c ^ 3 = 9 * d ^ 3 := by nlinarith
    by_cases hz : n = 0
    · subst hz; omega
    · have := ih (a.natAbs + b.natAbs + c.natAbs + d.natAbs) (by omega) a b c d rfl h'
      omega

/-- **Theorem 5.7.** If `x³ + 2y³ + 4z³ = 9w³` in integers, then `x = y = z = w = 0`. -/
@[kb "nivenzuckermanmontgomery" "Thm 5.7, p. 235"]
theorem cubic_form_only_trivial (x y z w : ℤ) (h : x ^ 3 + 2 * y ^ 3 + 4 * z ^ 3 = 9 * w ^ 3) :
    x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0 :=
  descent _ x y z w rfl h

/-- A natural number `≡ 3 (mod 4)` has a prime factor `≡ 3 (mod 4)`. -/
private lemma exists_prime_factor_mod_four_three :
    ∀ n : ℕ, n % 4 = 3 → ∃ q, q.Prime ∧ q ∣ n ∧ q % 4 = 3 := by
  intro n
  induction n using induction_on_primes with
  | zero => intro h; omega
  | one => intro h; omega
  | prime_mul p a hp ih =>
    intro h
    by_cases hp3 : p % 4 = 3
    · exact ⟨p, hp, dvd_mul_right _ _, hp3⟩
    · have hp2 : p ≠ 2 := by rintro rfl; omega
      have hodd : p % 2 = 1 := by
        rcases hp.eq_two_or_odd with h2 | h2
        · exact absurd h2 hp2
        · exact h2
      have hp1 : p % 4 = 1 := by omega
      have ha : a % 4 = 3 := by
        have : (p * a) % 4 = (p % 4) * (a % 4) % 4 := Nat.mul_mod _ _ _
        rw [hp1] at this; omega
      obtain ⟨q, hq, hqa, hq3⟩ := ih ha
      exact ⟨q, hq, dvd_mul_of_dvd_right hqa _, hq3⟩

/-- **Theorem 5.8.** The equation `y² = x³ + 7` has no solution in integers. -/
@[kb "nivenzuckermanmontgomery" "Thm 5.8, p. 236"]
theorem no_solution_sq_eq_cube_add_seven : ¬ ∃ x y : ℤ, y ^ 2 = x ^ 3 + 7 := by
  rintro ⟨x, y, h⟩
  -- squares mod 8
  have hy8 : y ^ 2 % 8 = 0 ∨ y ^ 2 % 8 = 1 ∨ y ^ 2 % 8 = 4 := by
    have : y % 8 = 0 ∨ y % 8 = 1 ∨ y % 8 = 2 ∨ y % 8 = 3 ∨ y % 8 = 4 ∨ y % 8 = 5 ∨
        y % 8 = 6 ∨ y % 8 = 7 := by omega
    rcases this with h | h | h | h | h | h | h | h <;> simp [pow_two, Int.mul_emod, h]
  have hx2 : x % 2 = 1 := by
    by_contra hx
    obtain ⟨k, rfl⟩ : 2 ∣ x := by omega
    have : y ^ 2 = 8 * k ^ 3 + 7 := by rw [h]; ring
    omega
  have hx4 : x % 4 = 1 ∨ x % 4 = 3 := by omega
  have hx3 : x ^ 3 % 4 = x % 4 := by
    rcases hx4 with h | h <;> simp [pow_succ, Int.mul_emod, h]
  have hy4 : y ^ 2 % 4 = 0 := by omega
  have hx1 : x % 4 = 1 := by omega
  -- the factor x² - 2x + 4
  have hpos : 0 < x ^ 2 - 2 * x + 4 := by nlinarith [sq_nonneg (x - 1)]
  have hmod : (x ^ 2 - 2 * x + 4) % 4 = 3 := by
    have : x ^ 2 % 4 = 1 := by simp [pow_two, Int.mul_emod, hx1]
    omega
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = x ^ 2 - 2 * x + 4 := ⟨_, Int.toNat_of_nonneg hpos.le⟩
  have hn4 : n % 4 = 3 := by omega
  obtain ⟨q, hq, hqn, hq3⟩ := exists_prime_factor_mod_four_three n hn4
  have hdvd : (q : ℤ) ∣ y ^ 2 + 1 := by
    have : y ^ 2 + 1 = (x + 2) * n := by rw [hn, h]; ring
    rw [this]
    exact Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mpr hqn) _
  have : Fact q.Prime := ⟨hq⟩
  have h0 : (((y ^ 2 + 1 : ℤ)) : ZMod q) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hdvd
  push_cast at h0
  exact ZMod.mod_four_ne_three_of_sq_eq_neg_one (eq_neg_of_add_eq_zero_left h0) hq3

/-- **Theorem 5.9.** The integer solutions of `x⁴ + x³ + x² + x + 1 = y²` are exactly
`x = -1, 0` with `y = ±1`, and `x = 3` with `y = ±11`. -/
@[kb "nivenzuckermanmontgomery" "Thm 5.9, p. 236"]
theorem quartic_eq_sq_iff (x y : ℤ) :
    x ^ 4 + x ^ 3 + x ^ 2 + x + 1 = y ^ 2 ↔
      (x = -1 ∧ (y = 1 ∨ y = -1)) ∨ (x = 0 ∧ (y = 1 ∨ y = -1)) ∨
        (x = 3 ∧ (y = 11 ∨ y = -11)) := by
  constructor
  · intro h
    have hb : -1 ≤ x ∧ x ≤ 3 := by
      by_contra hx
      have hxx : x < -1 ∨ 3 < x := by omega
      -- (2|y|)² lies strictly between consecutive squares
      set m := 2 * x ^ 2 + x with hm
      have hm0 : 0 ≤ m := by rcases hxx with h1 | h1 <;> nlinarith
      have e : (2 * y) ^ 2 = 4 * (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) := by rw [h]; ring
      have lo : m ^ 2 < |2 * y| ^ 2 := by
        rw [sq_abs, e, hm]; nlinarith [sq_nonneg (3 * x + 2)]
      have hi : |2 * y| ^ 2 < (m + 1) ^ 2 := by
        rw [sq_abs, e, hm]
        rcases hxx with h1 | h1 <;> nlinarith
      have a1 : m < |2 * y| := lt_of_pow_lt_pow_left₀ 2 (abs_nonneg _) lo
      have a2 : |2 * y| < m + 1 := lt_of_pow_lt_pow_left₀ 2 (by linarith) hi
      omega
    obtain ⟨h1, h2⟩ := hb
    have hxs : x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by omega
    rcases hxs with rfl | rfl | rfl | rfl | rfl
    · have : (y - 1) * (y + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h
      · left; exact ⟨rfl, Or.inl (by omega)⟩
      · left; exact ⟨rfl, Or.inr (by omega)⟩
    · have : (y - 1) * (y + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h
      · right; left; exact ⟨rfl, Or.inl (by omega)⟩
      · right; left; exact ⟨rfl, Or.inr (by omega)⟩
    · exfalso
      have : y ^ 2 = 5 := by linarith
      have h3 : -3 < y := by nlinarith
      have h4 : y < 3 := by nlinarith
      interval_cases y <;> omega
    · exfalso
      have : y ^ 2 = 31 := by linarith
      have h3 : -6 < y := by nlinarith
      have h4 : y < 6 := by nlinarith
      interval_cases y <;> omega
    · have : (y - 11) * (y + 11) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h
      · right; right; exact ⟨rfl, Or.inl (by omega)⟩
      · right; right; exact ⟨rfl, Or.inr (by omega)⟩
  · rintro (⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩) <;> norm_num

end NTKB.NZM
