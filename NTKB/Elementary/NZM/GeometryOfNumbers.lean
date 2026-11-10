/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Attr
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases

/-!
# Geometry of numbers: applications (Niven–Zuckerman–Montgomery, §§ 6.3–6.4)

* Lemma 6.10: for positive integers `x, y` the two Hurwitz-type inequalities cannot both hold.
* Theorem 6.25 (Dirichlet, simultaneous approximation).  The book derives it from Minkowski's
  theorem with the bound `0 < b ≤ n` and `|x_i - a_i/b| < 1/(b n^{1/k})`.  Here it is proved by
  pigeonhole in the form `n = m^k`, i.e. `0 < b ≤ m^k` and `|x_i - a_i/b| < 1/(b m)`.  This is
  exactly the book statement when `n` is a perfect `k`-th power (`n^{1/k} = m`); the general
  statement is recorded as the proposition `SimultaneousApproximationStatement`.
* Corollary 6.27: `2·4^r` is not a sum of four positive squares, and every `n > 169` is a sum of
  five positive squares.
-/

namespace NTKB.NZM

/-- **Lemma 6.10.** For positive integers `x, y`, the inequalities
`1/(xy) ≥ (1/√5)(1/x² + 1/y²)` and `1/(x(x+y)) ≥ (1/√5)(1/x² + 1/(x+y)²)` cannot both hold. -/
@[kb "nivenzuckermanmontgomery" "Lemma 6.10, p. 303"]
theorem not_both_hurwitz_ineq (x y : ℕ) (hx : 0 < x) (hy : 0 < y) :
    ¬ ((1 / Real.sqrt 5) * (1 / (x : ℝ) ^ 2 + 1 / (y : ℝ) ^ 2) ≤ 1 / ((x : ℝ) * y) ∧
       (1 / Real.sqrt 5) * (1 / (x : ℝ) ^ 2 + 1 / ((x : ℝ) + y) ^ 2) ≤
         1 / ((x : ℝ) * ((x : ℝ) + y))) := by
  rintro ⟨h1, h2⟩
  have hx' : (0 : ℝ) < x := by exact_mod_cast hx
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy
  have hs : (0 : ℝ) < Real.sqrt 5 := by positivity
  have hs2 : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  have hxy : (0 : ℝ) < x + y := by positivity
  have e1 : (x : ℝ) ^ 2 + y ^ 2 ≤ Real.sqrt 5 * (x * y) := by
    have : (1 / Real.sqrt 5) * (1 / (x : ℝ) ^ 2 + 1 / (y : ℝ) ^ 2) =
        ((x : ℝ) ^ 2 + y ^ 2) / (Real.sqrt 5 * (x ^ 2 * y ^ 2)) := by
      field_simp
      ring
    rw [this, div_le_div_iff₀ (by positivity) (by positivity)] at h1
    have h3 : ((x : ℝ) ^ 2 + y ^ 2) * (x * y) ≤ (Real.sqrt 5 * (x * y)) * (x * y) := by
      nlinarith [h1]
    exact le_of_mul_le_mul_right h3 (by positivity)
  have e2 : ((x : ℝ) + y) ^ 2 + x ^ 2 ≤ Real.sqrt 5 * (x * (x + y)) := by
    have : (1 / Real.sqrt 5) * (1 / (x : ℝ) ^ 2 + 1 / ((x : ℝ) + y) ^ 2) =
        (((x : ℝ) + y) ^ 2 + x ^ 2) / (Real.sqrt 5 * (x ^ 2 * (x + y) ^ 2)) := by
      field_simp
    rw [this, div_le_div_iff₀ (by positivity) (by positivity)] at h2
    have h3 : (((x : ℝ) + y) ^ 2 + x ^ 2) * (x * (x + y)) ≤
        (Real.sqrt 5 * (x * (x + y))) * (x * (x + y)) := by
      nlinarith [h2]
    exact le_of_mul_le_mul_right h3 (by positivity)
  -- (2y - (√5 - 1) x)² ≤ 0
  have hsq : (2 * (y : ℝ) - (Real.sqrt 5 - 1) * x) ^ 2 ≤ 0 := by
    nlinarith [e1, e2, hs2]
  have hz : 2 * (y : ℝ) - (Real.sqrt 5 - 1) * x = 0 := by
    have := sq_nonneg (2 * (y : ℝ) - (Real.sqrt 5 - 1) * x)
    exact pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm hsq this)
  have hirr : Irrational (Real.sqrt 5) := by
    have := Nat.Prime.irrational_sqrt (p := 5) (by decide)
    simpa using this
  apply hirr
  refine ⟨((2 * y + x : ℕ) : ℚ) / x, ?_⟩
  push_cast
  field_simp
  linarith

/-- **Theorem 6.25 (pigeonhole form).** For reals `x_1, …, x_k` and a positive integer `m` there
are integers `a_i` and `b` with `0 < b ≤ m^k` and `|x_i - a_i/b| < 1/(b m)`. -/
@[kb "nivenzuckermanmontgomery" "Thm 6.25, p. 316"]
theorem simultaneous_approximation {k : ℕ} (x : Fin k → ℝ) (m : ℕ) (hm : 0 < m) :
    ∃ (a : Fin k → ℤ) (b : ℕ), 0 < b ∧ b ≤ m ^ k ∧
      ∀ i, |x i - (a i : ℝ) / b| < 1 / ((b : ℝ) * m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  let f : Fin (m ^ k + 1) → (Fin k → Fin m) := fun j i =>
    ⟨⌊(m : ℝ) * Int.fract (((j : ℕ) : ℝ) * x i)⌋₊, by
      have h0 : 0 ≤ Int.fract (((j : ℕ) : ℝ) * x i) := Int.fract_nonneg _
      have h1 := Int.fract_lt_one (((j : ℕ) : ℝ) * x i)
      rw [Nat.floor_lt (by positivity)]
      nlinarith⟩
  have hcard : Fintype.card (Fin k → Fin m) < Fintype.card (Fin (m ^ k + 1)) := by
    simp
  obtain ⟨j, j', hne, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have key : ∀ j j' : ℕ, j < j' → j' ≤ m ^ k →
      (∀ i, ⌊(m : ℝ) * Int.fract ((j : ℝ) * x i)⌋₊ = ⌊(m : ℝ) * Int.fract ((j' : ℝ) * x i)⌋₊) →
      ∃ (a : Fin k → ℤ) (b : ℕ), 0 < b ∧ b ≤ m ^ k ∧
        ∀ i, |x i - (a i : ℝ) / b| < 1 / ((b : ℝ) * m) := by
    intro j j' hjj hj' hfl
    have hb : 0 < j' - j := by omega
    refine ⟨fun i => ⌊(j' : ℝ) * x i⌋ - ⌊(j : ℝ) * x i⌋, j' - j, hb, by omega, fun i => ?_⟩
    have hbR : (0 : ℝ) < ((j' - j : ℕ) : ℝ) := by exact_mod_cast hb
    have hcast : (((j' - j : ℕ)) : ℝ) = (j' : ℝ) - j := by
      rw [Nat.cast_sub hjj.le]
    have p1 := Nat.floor_le (mul_nonneg hm'.le (Int.fract_nonneg ((j : ℝ) * x i)))
    have p2 := Nat.lt_floor_add_one ((m : ℝ) * Int.fract ((j : ℝ) * x i))
    have q1 := Nat.floor_le (mul_nonneg hm'.le (Int.fract_nonneg ((j' : ℝ) * x i)))
    have q2 := Nat.lt_floor_add_one ((m : ℝ) * Int.fract ((j' : ℝ) * x i))
    have hfi' : (⌊(m : ℝ) * Int.fract ((j : ℝ) * x i)⌋₊ : ℝ) =
        (⌊(m : ℝ) * Int.fract ((j' : ℝ) * x i)⌋₊ : ℝ) := by exact_mod_cast hfl i
    have hd : |(Int.fract ((j' : ℝ) * x i) - Int.fract ((j : ℝ) * x i)) * m| < 1 :=
      abs_lt.mpr ⟨by linarith, by linarith⟩
    rw [abs_mul, abs_of_pos hm'] at hd
    have hF := Int.floor_add_fract ((j' : ℝ) * x i)
    have hG := Int.floor_add_fract ((j : ℝ) * x i)
    have heq : x i - (((⌊(j' : ℝ) * x i⌋ - ⌊(j : ℝ) * x i⌋ : ℤ) : ℝ)) / ((j' - j : ℕ) : ℝ) =
        (Int.fract ((j' : ℝ) * x i) - Int.fract ((j : ℝ) * x i)) / ((j' - j : ℕ) : ℝ) := by
      rw [eq_div_iff hbR.ne', sub_mul, div_mul_cancel₀ _ hbR.ne']
      push_cast
      rw [hcast]
      linarith
    rw [heq, abs_div, abs_of_pos hbR, div_lt_div_iff₀ hbR (by positivity)]
    nlinarith [mul_lt_mul_of_pos_right hd hbR]
  have hval : ∀ i, ⌊(m : ℝ) * Int.fract (((j : ℕ) : ℝ) * x i)⌋₊ =
      ⌊(m : ℝ) * Int.fract (((j' : ℕ) : ℝ) * x i)⌋₊ := fun i => by
    have := congrArg Fin.val (congrFun hf i)
    simpa [f] using this
  have hne' : (j : ℕ) ≠ j' := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hne' with h | h
  · exact key j j' h (by have := j'.isLt; omega) hval
  · exact key j' j h (by have := j.isLt; omega) (fun i => (hval i).symm)

/-- **Theorem 6.25** (book form), as a proposition: for reals `x_1, …, x_k` and a positive integer
`n` there are integers `a_i`, `b` with `0 < b ≤ n` and `|x_i - a_i/b| < 1/(b n^{1/k})`. -/
def SimultaneousApproximationStatement : Prop :=
  ∀ (k : ℕ) (x : Fin k → ℝ) (n : ℕ), 0 < n →
    ∃ (a : Fin k → ℤ) (b : ℕ), 0 < b ∧ b ≤ n ∧
      ∀ i, |x i - (a i : ℝ) / b| < 1 / ((b : ℝ) * (n : ℝ) ^ (1 / (k : ℝ)))

/-- **Theorem 6.25**, book form for `n = m^k`, `k ≥ 1` (where `n^{1/k} = m`). -/
@[kb "nivenzuckermanmontgomery" "Thm 6.25, p. 316"]
theorem simultaneous_approximation_book_pow {k : ℕ} (hk : 0 < k) (x : Fin k → ℝ) (m : ℕ)
    (hm : 0 < m) :
    ∃ (a : Fin k → ℤ) (b : ℕ), 0 < b ∧ b ≤ m ^ k ∧
      ∀ i, |x i - (a i : ℝ) / b| < 1 / ((b : ℝ) * ((m ^ k : ℕ) : ℝ) ^ (1 / (k : ℝ))) := by
  obtain ⟨a, b, hb, hbk, h⟩ := simultaneous_approximation x m hm
  have hroot : ((m ^ k : ℕ) : ℝ) ^ (1 / (k : ℝ)) = m := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    have : (k : ℝ) * (1 / (k : ℝ)) = 1 := by
      have : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
      field_simp
    rw [this, Real.rpow_one]
  refine ⟨a, b, hb, hbk, fun i => ?_⟩
  rw [hroot]
  exact h i

lemma sq_mod_eight (a : ℕ) :
    (a % 2 = 1 → a ^ 2 % 8 = 1) ∧ (a % 2 = 0 → a ^ 2 % 8 = 0 ∨ a ^ 2 % 8 = 4) := by
  rw [Nat.pow_mod]
  have h8 : a % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have h2 : a % 2 = (a % 8) % 2 := by omega
  rw [h2]
  generalize a % 8 = r at *
  interval_cases r <;> simp

lemma even_of_sum_sq_mod_eight (a b c d : ℕ) (h : (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) % 8 = 0) :
    a % 2 = 0 ∧ b % 2 = 0 ∧ c % 2 = 0 ∧ d % 2 = 0 := by
  have ha := sq_mod_eight a
  have hb := sq_mod_eight b
  have hc := sq_mod_eight c
  have hd := sq_mod_eight d
  omega

/-- Part of **Corollary 6.27**: `2·4^r` is not a sum of four positive squares. -/
theorem not_sum_four_pos_sq_two_mul_four_pow (r : ℕ) :
    ∀ a b c d : ℕ, 0 < a → 0 < b → 0 < c → 0 < d →
      a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≠ 2 * 4 ^ r := by
  induction r with
  | zero =>
    intro a b c d ha hb hc hd h
    have := pow_pos ha 2
    have := pow_pos hb 2
    have := pow_pos hc 2
    have := pow_pos hd 2
    simp at h
    omega
  | succ r ih =>
    intro a b c d ha hb hc hd h
    have hmod : (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) % 8 = 0 := by
      rw [h, pow_succ]; omega
    obtain ⟨h1, h2, h3, h4⟩ := even_of_sum_sq_mod_eight a b c d hmod
    obtain ⟨a', rfl⟩ : ∃ a', a = 2 * a' := ⟨a / 2, by omega⟩
    obtain ⟨b', rfl⟩ : ∃ b', b = 2 * b' := ⟨b / 2, by omega⟩
    obtain ⟨c', rfl⟩ : ∃ c', c = 2 * c' := ⟨c / 2, by omega⟩
    obtain ⟨d', rfl⟩ : ∃ d', d = 2 * d' := ⟨d / 2, by omega⟩
    refine ih a' b' c' d' (by omega) (by omega) (by omega) (by omega) ?_
    rw [pow_succ] at h
    ring_nf at h ⊢
    omega

/-- Representation of `n > 169` as five positive squares. -/
theorem sum_five_pos_sq_of_gt_169 (n : ℕ) (hn : 169 < n) :
    ∃ v w x y z : ℕ, 0 < v ∧ 0 < w ∧ 0 < x ∧ 0 < y ∧ 0 < z ∧
      v ^ 2 + w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = n := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares (n - 169)
  have hn' : n = 169 + (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by omega
  subst hn'
  rcases Nat.eq_zero_or_pos a with rfl | ha <;> rcases Nat.eq_zero_or_pos b with rfl | hb <;>
    rcases Nat.eq_zero_or_pos c with rfl | hc <;> rcases Nat.eq_zero_or_pos d with rfl | hd <;>
    first
    | (exfalso; omega)
    | exact ⟨13, a, b, c, d, by norm_num, ha, hb, hc, hd, by ring⟩
    | exact ⟨5, 12, a, b, c, by norm_num, by norm_num, ha, hb, hc, by ring⟩
    | exact ⟨5, 12, a, b, d, by norm_num, by norm_num, ha, hb, hd, by ring⟩
    | exact ⟨5, 12, a, c, d, by norm_num, by norm_num, ha, hc, hd, by ring⟩
    | exact ⟨5, 12, b, c, d, by norm_num, by norm_num, hb, hc, hd, by ring⟩
    | exact ⟨12, 4, 3, a, b, by norm_num, by norm_num, by norm_num, ha, hb, by ring⟩
    | exact ⟨12, 4, 3, a, c, by norm_num, by norm_num, by norm_num, ha, hc, by ring⟩
    | exact ⟨12, 4, 3, a, d, by norm_num, by norm_num, by norm_num, ha, hd, by ring⟩
    | exact ⟨12, 4, 3, b, c, by norm_num, by norm_num, by norm_num, hb, hc, by ring⟩
    | exact ⟨12, 4, 3, b, d, by norm_num, by norm_num, by norm_num, hb, hd, by ring⟩
    | exact ⟨12, 4, 3, c, d, by norm_num, by norm_num, by norm_num, hc, hd, by ring⟩
    | exact ⟨10, 8, 2, 1, a, by norm_num, by norm_num, by norm_num, by norm_num, ha, by ring⟩
    | exact ⟨10, 8, 2, 1, b, by norm_num, by norm_num, by norm_num, by norm_num, hb, by ring⟩
    | exact ⟨10, 8, 2, 1, c, by norm_num, by norm_num, by norm_num, by norm_num, hc, by ring⟩
    | exact ⟨10, 8, 2, 1, d, by norm_num, by norm_num, by norm_num, by norm_num, hd, by ring⟩

/-- **Corollary 6.27.** Infinitely many positive integers are not sums of four positive squares
(e.g. `2·4^r`), and every `n > 169` is a sum of five positive squares. -/
@[kb "nivenzuckermanmontgomery" "Cor 6.27, p. 318"]
theorem corollary_6_27 :
    Set.Infinite {n : ℕ | 0 < n ∧ ¬ ∃ a b c d : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
        a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n} ∧
    ∀ n : ℕ, 169 < n → ∃ v w x y z : ℕ, 0 < v ∧ 0 < w ∧ 0 < x ∧ 0 < y ∧ 0 < z ∧
      v ^ 2 + w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = n := by
  refine ⟨?_, sum_five_pos_sq_of_gt_169⟩
  refine Set.infinite_of_injective_forall_mem (f := fun r : ℕ => 2 * 4 ^ r) ?_ ?_
  · intro r s hrs
    simpa using hrs
  · intro r
    refine ⟨by positivity, ?_⟩
    rintro ⟨a, b, c, d, ha, hb, hc, hd, h⟩
    exact not_sum_four_pos_sq_two_mul_four_pow r a b c d ha hb hc hd h

end NTKB.NZM
