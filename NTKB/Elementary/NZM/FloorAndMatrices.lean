/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Attr
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Linarith

/-!
# The greatest integer function, unimodular matrices, the birthday product
(Niven–Zuckerman–Montgomery)

* Theorem 4.1: properties of `[x] = ⌊x⌋` (parts `thm_4_1_a` ... `thm_4_1_h`).
* Definition 5.1, Theorem 5.3: unimodular matrices.  The equivalence of `det = ±1` with
  invertibility over `ℤ` is proved; the factorization into elementary matrices is only stated
  (`UnimodularElementaryProduct`, a `Prop`).
* Lemma 2.21: probability that `k` independent choices from `{1, …, n}` are distinct.
-/

namespace NTKB.NZM

/-! ### Theorem 4.1 -/

/-- Theorem 4.1 (a): `[x] ≤ x < [x] + 1`. -/
@[kb "nivenzuckermanmontgomery" "Thm 4.1, p. 180"]
theorem thm_4_1_a (x : ℝ) : (⌊x⌋ : ℝ) ≤ x ∧ x < ⌊x⌋ + 1 :=
  ⟨Int.floor_le x, Int.lt_floor_add_one x⟩

/-- Theorem 4.1 (b): `[x + m] = [x] + m` for an integer `m`. -/
@[kb "nivenzuckermanmontgomery" "Thm 4.1, p. 180"]
theorem thm_4_1_b (x : ℝ) (m : ℤ) : ⌊x + m⌋ = ⌊x⌋ + m := by
  simp

/-- Theorem 4.1 (c): `[x] + [y] ≤ [x + y] ≤ [x] + [y] + 1`. -/
@[kb "nivenzuckermanmontgomery" "Thm 4.1, p. 180"]
theorem thm_4_1_c (x y : ℝ) : ⌊x⌋ + ⌊y⌋ ≤ ⌊x + y⌋ ∧ ⌊x + y⌋ ≤ ⌊x⌋ + ⌊y⌋ + 1 := by
  constructor
  · apply Int.le_floor.2
    push_cast
    linarith [Int.floor_le x, Int.floor_le y]
  · have h : ⌊x + y⌋ < ⌊x⌋ + ⌊y⌋ + 2 := by
      apply Int.floor_lt.2
      push_cast
      linarith [Int.lt_floor_add_one x, Int.lt_floor_add_one y]
    omega

/-- Theorem 4.1 (d): `[x] + [-x]` is `0` or `-1`; it is `0` iff `x` is an integer. -/
@[kb "nivenzuckermanmontgomery" "Thm 4.1, p. 180"]
theorem thm_4_1_d (x : ℝ) : ⌊x⌋ + ⌊-x⌋ = 0 ∨ ⌊x⌋ + ⌊-x⌋ = -1 := by
  have h1 := Int.floor_le_ceil x
  have h2 := Int.ceil_le_floor_add_one x
  rw [Int.floor_neg]
  omega

/-- Theorem 4.1 (e): `[[x]/m] = [x/m]` for a positive integer `m`. -/
@[kb "nivenzuckermanmontgomery" "Thm 4.1, p. 180"]
theorem thm_4_1_e (x : ℝ) (m : ℕ) (hm0 : 0 < m) : ⌊(⌊x⌋ : ℝ) / m⌋ = ⌊x / m⌋ := by
  have hm : (0 : ℝ) < m := by exact_mod_cast hm0
  set k := ⌊x / m⌋ with hk
  rw [Int.floor_eq_iff]
  constructor
  · have h1 : (k : ℝ) ≤ x / m := Int.floor_le _
    have h2 : (k : ℝ) * m ≤ x := (le_div_iff₀ hm).1 h1
    have h3 : k * (m : ℤ) ≤ ⌊x⌋ := Int.le_floor.2 (by push_cast; exact h2)
    exact (le_div_iff₀ hm).2 (by exact_mod_cast h3)
  · have h1 : x / m < k + 1 := Int.lt_floor_add_one _
    have h2 : x < ((k : ℝ) + 1) * m := (div_lt_iff₀ hm).1 h1
    exact (div_lt_iff₀ hm).2 (lt_of_le_of_lt (Int.floor_le x) h2)

/-- Theorem 4.1 (f): `-[-x]` is the least integer `≥ x` (i.e. `⌈x⌉`). -/
@[kb "nivenzuckermanmontgomery" "Thm 4.1, p. 180"]
theorem thm_4_1_f (x : ℝ) :
    x ≤ ((-⌊-x⌋ : ℤ) : ℝ) ∧ ∀ n : ℤ, x ≤ n → -⌊-x⌋ ≤ n := by
  rw [Int.floor_neg, neg_neg]
  exact ⟨Int.le_ceil x, fun n h => Int.ceil_le.2 h⟩

lemma nearest_aux (x : ℝ) (n : ℤ) : |x - ⌊x + 1 / 2⌋| ≤ |x - n| := by
  have hf1 : (⌊x + 1 / 2⌋ : ℝ) ≤ x + 1 / 2 := Int.floor_le _
  have hf2 : x + 1 / 2 < (⌊x + 1 / 2⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hb : |x - ⌊x + 1 / 2⌋| ≤ 1 / 2 := by
    rw [abs_le]; constructor <;> linarith
  rcases lt_trichotomy n ⌊x + 1 / 2⌋ with h | h | h
  · have h' : (n : ℝ) + 1 ≤ ⌊x + 1 / 2⌋ := by exact_mod_cast h
    have : |x - ⌊x + 1 / 2⌋| ≤ x - n := by
      rw [abs_le]; constructor <;> linarith
    exact le_trans this (le_abs_self _)
  · rw [h]
  · have h' : (⌊x + 1 / 2⌋ : ℝ) + 1 ≤ n := by exact_mod_cast h
    have : |x - ⌊x + 1 / 2⌋| ≤ n - x := by
      rw [abs_le]; constructor <;> linarith
    exact le_trans this (by rw [abs_sub_comm]; exact le_abs_self _)

/-- Theorem 4.1 (g): `[x + 1/2]` is a nearest integer to `x`. -/
@[kb "nivenzuckermanmontgomery" "Thm 4.1, p. 180"]
theorem thm_4_1_g (x : ℝ) : |x - ⌊x + 1 / 2⌋| ≤ 1 / 2 ∧ ∀ n : ℤ, |x - ⌊x + 1 / 2⌋| ≤ |x - n| := by
  refine ⟨?_, nearest_aux x⟩
  have hf1 : (⌊x + 1 / 2⌋ : ℝ) ≤ x + 1 / 2 := Int.floor_le _
  have hf2 : x + 1 / 2 < (⌊x + 1 / 2⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  rw [abs_le]; constructor <;> linarith

/-- Theorem 4.1 (g'): `-[-x + 1/2]` is also a nearest integer to `x`. -/
@[kb "nivenzuckermanmontgomery" "Thm 4.1, p. 180"]
theorem thm_4_1_g' (x : ℝ) :
    |x - ((-⌊-x + 1 / 2⌋ : ℤ) : ℝ)| ≤ 1 / 2 ∧
      ∀ n : ℤ, |x - ((-⌊-x + 1 / 2⌋ : ℤ) : ℝ)| ≤ |x - n| := by
  have key : ∀ n : ℤ, |x - ((-⌊-x + 1 / 2⌋ : ℤ) : ℝ)| ≤ |x - n| := by
    intro n
    have h := nearest_aux (-x) (-n)
    simp only [Int.cast_neg] at h
    rw [Int.cast_neg, show x - -((⌊-x + 1 / 2⌋ : ℤ) : ℝ) = -(-x - ⌊-x + 1 / 2⌋) by ring,
      abs_neg, show x - (n : ℝ) = -(-x - -(n : ℝ)) by ring, abs_neg]
    exact h
  refine ⟨?_, key⟩
  have hf1 : (⌊-x + 1 / 2⌋ : ℝ) ≤ -x + 1 / 2 := Int.floor_le _
  have hf2 : -x + 1 / 2 < (⌊-x + 1 / 2⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  rw [Int.cast_neg, abs_le]; constructor <;> linarith

/-- Theorem 4.1 (h): the number of multiples of `a` among `1, …, n` is `[n/a]`. -/
@[kb "nivenzuckermanmontgomery" "Thm 4.1, p. 180"]
theorem thm_4_1_h (a n : ℕ) (ha : 0 < a) :
    (((Finset.Ioc 0 n).filter (fun m => a ∣ m)).card : ℤ) = ⌊(n : ℝ) / a⌋ := by
  rw [Nat.Ioc_filter_dvd_card_eq_div]
  have hpos : (0 : ℝ) < a := by exact_mod_cast ha
  symm
  rw [Int.floor_eq_iff, Int.cast_natCast]
  constructor
  · exact Nat.cast_div_le
  · apply (div_lt_iff₀ hpos).2
    have h3 : n < (n / a + 1) * a := by
      rw [mul_comm]; exact Nat.lt_mul_div_succ n ha
    exact_mod_cast h3

/-- Theorem 4.1 (1), the other two forms: `x - 1 < [x] ≤ x` and `0 ≤ x - [x] < 1`. -/
@[kb "nivenzuckermanmontgomery" "Thm 4.1, p. 180"]
theorem thm_4_1_a' (x : ℝ) :
    (x - 1 < ⌊x⌋ ∧ (⌊x⌋ : ℝ) ≤ x) ∧ (0 ≤ x - ⌊x⌋ ∧ x - ⌊x⌋ < 1) := by
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  exact ⟨⟨by linarith, h1⟩, by linarith, by linarith⟩

/-- Theorem 4.1 (2): for `x ≥ 0`, `[x]` is the number of positive integers `i ≤ x`. -/
@[kb "nivenzuckermanmontgomery" "Thm 4.1, p. 180"]
theorem thm_4_1_sum (x : ℝ) (hx : 0 ≤ x) :
    (Nat.card {i : ℕ | 1 ≤ i ∧ (i : ℝ) ≤ x} : ℤ) = ⌊x⌋ := by
  have : {i : ℕ | 1 ≤ i ∧ (i : ℝ) ≤ x} = ↑(Finset.Icc 1 ⌊x⌋₊) := by
    ext i
    simp only [Set.mem_setOf_eq, Finset.coe_Icc, Set.mem_Icc, Nat.le_floor_iff hx]
  rw [this, Nat.card_coe_set_eq, Set.ncard_coe_finset, Nat.card_Icc, Nat.add_sub_cancel]
  exact Int.natCast_floor_eq_floor hx

/-- Theorem 4.1 (5), exact form: `[x] + [-x] = 0` if `x` is an integer and `-1` otherwise. -/
@[kb "nivenzuckermanmontgomery" "Thm 4.1, p. 180"]
theorem thm_4_1_d' (x : ℝ) :
    ((∃ n : ℤ, x = n) → ⌊x⌋ + ⌊-x⌋ = 0) ∧ ((¬∃ n : ℤ, x = n) → ⌊x⌋ + ⌊-x⌋ = -1) := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨n, rfl⟩
    rw [← Int.cast_neg, Int.floor_intCast, Int.floor_intCast]; ring
  · rcases thm_4_1_d x with h0 | h1
    · exfalso
      rw [Int.floor_neg] at h0
      have hc : ⌈x⌉ = ⌊x⌋ := by omega
      exact h ⟨⌊x⌋, le_antisymm (by rw [← hc]; exact Int.le_ceil x) (Int.floor_le x)⟩
    · exact h1

/-- Theorem 4.1 (8), ties: if an integer `m` is as near to `x` as `[x + 1/2]`, then
`m ≤ [x + 1/2]` (of two equally near integers, `[x + 1/2]` is the larger). -/
@[kb "nivenzuckermanmontgomery" "Thm 4.1, p. 180"]
theorem thm_4_1_g_tie (x : ℝ) (m : ℤ) (h : |x - m| = |x - ⌊x + 1 / 2⌋|) : m ≤ ⌊x + 1 / 2⌋ := by
  by_contra hlt
  push Not at hlt
  have hm : ((⌊x + 1 / 2⌋ : ℤ) : ℝ) + 1 ≤ m := by exact_mod_cast hlt
  have hf1 : (⌊x + 1 / 2⌋ : ℝ) ≤ x + 1 / 2 := Int.floor_le _
  have hf2 : x + 1 / 2 < (⌊x + 1 / 2⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have e1 : |x - m| = m - x := by rw [abs_sub_comm]; exact abs_of_pos (by linarith)
  have e2 : |x - ⌊x + 1 / 2⌋| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
  linarith

/-- Theorem 4.1 (9), ties: of two integers equally near to `x`, `-[-x + 1/2]` is the smaller. -/
@[kb "nivenzuckermanmontgomery" "Thm 4.1, p. 180"]
theorem thm_4_1_g'_tie (x : ℝ) (m : ℤ) (h : |x - m| = |x - ((-⌊-x + 1 / 2⌋ : ℤ) : ℝ)|) :
    -⌊-x + 1 / 2⌋ ≤ m := by
  have h' : |-x - ((-m : ℤ) : ℝ)| = |-x - ⌊-x + 1 / 2⌋| := by
    rw [show -x - ((-m : ℤ) : ℝ) = -(x - m) by push_cast; ring, abs_neg, h, Int.cast_neg,
      show x - -((⌊-x + 1 / 2⌋ : ℤ) : ℝ) = -(-x - ⌊-x + 1 / 2⌋) by ring, abs_neg]
  have := thm_4_1_g_tie (-x) (-m) h'
  omega

/-! ### Definition 5.1, Theorem 5.3 -/

/-- Definition 5.1: an integer square matrix is unimodular if its determinant is `±1`. -/
@[kb "nivenzuckermanmontgomery" "Def 5.1, p. 227"]
def IsUnimodular {n : Type*} [Fintype n] [DecidableEq n] (U : Matrix n n ℤ) : Prop :=
  U.det = 1 ∨ U.det = -1

/-- The elementary (row-operation) integer matrices: adding `c` times row `j` to row `i`,
swapping two rows, negating a row.  Right multiplication by the same matrices performs the
corresponding column operations. -/
def elementaryMatrices (n : Type*) [Fintype n] [DecidableEq n] : Set (Matrix n n ℤ) :=
  {M | (∃ i j : n, ∃ c : ℤ, i ≠ j ∧ M = 1 + Matrix.of fun a b => if a = i ∧ b = j then c else 0) ∨
    (∃ i j : n, i ≠ j ∧ M = Matrix.of fun a b => if Equiv.swap i j a = b then 1 else 0) ∨
    (∃ i : n, M = Matrix.diagonal (Function.update (1 : n → ℤ) i (-1)))}

/-- Theorem 5.3, the factorization part (stated only, not proved here): a unimodular matrix is a
product of elementary matrices (the converse direction is not part of this statement). -/
def UnimodularElementaryProduct : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (U : Matrix n n ℤ),
    IsUnimodular U → U ∈ Submonoid.closure (elementaryMatrices n)

/-- Theorem 5.3 (first equivalences): for an integer square matrix `U`, `det U = ±1` iff
`U` is invertible over `ℤ`, iff `U V = 1` for some integer matrix `V`, iff `V U = 1`. -/
@[kb "nivenzuckermanmontgomery" "Thm 5.3, p. 227"]
theorem isUnimodular_iff_isUnit {n : Type*} [Fintype n] [DecidableEq n] (U : Matrix n n ℤ) :
    IsUnimodular U ↔ IsUnit U := by
  rw [Matrix.isUnit_iff_isUnit_det, Int.isUnit_iff]
  rfl

/-- Theorem 5.3: `det U = ±1` iff there is an integer matrix `V` with `U V = 1`
(i.e. `U⁻¹` has integer entries). -/
@[kb "nivenzuckermanmontgomery" "Thm 5.3, p. 227"]
theorem isUnimodular_iff_exists_inverse {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℤ) : IsUnimodular U ↔ ∃ V : Matrix n n ℤ, U * V = 1 := by
  rw [isUnimodular_iff_isUnit]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨↑u⁻¹, u.mul_inv⟩
  · rintro ⟨V, hV⟩
    exact ⟨⟨U, V, hV, mul_eq_one_comm.1 hV⟩, rfl⟩

/-- Theorem 5.3: `det U = ±1` iff `V U = 1` for some integer matrix `V`. -/
@[kb "nivenzuckermanmontgomery" "Thm 5.3, p. 227"]
theorem isUnimodular_iff_exists_left_inverse {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℤ) : IsUnimodular U ↔ ∃ V : Matrix n n ℤ, V * U = 1 := by
  rw [isUnimodular_iff_exists_inverse]
  constructor
  · rintro ⟨V, hV⟩; exact ⟨V, mul_eq_one_comm.1 hV⟩
  · rintro ⟨V, hV⟩; exact ⟨V, mul_eq_one_comm.1 hV⟩

/-! ### Lemma 2.21 -/

lemma cast_descFactorial_eq_prod (n k : ℕ) :
    (n.descFactorial k : ℚ) = ∏ j ∈ Finset.range k, ((n : ℚ) - j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, ← ih, Nat.descFactorial_succ, Nat.cast_mul, mul_comm]
    by_cases hk : k ≤ n
    · rw [Nat.cast_sub hk]
    · have : n.descFactorial k = 0 := Nat.descFactorial_eq_zero_iff_lt.2 (by omega)
      simp [this]

/-- Lemma 2.21: the number of injective maps `Fin k → Fin n`, divided by the total `n ^ k`, equals
`∏_{j < k} (1 - j/n)`. -/
@[kb "nivenzuckermanmontgomery" "Lemma 2.21, p. 79"]
theorem lemma_2_21 (n k : ℕ) (hn : 0 < n) :
    (Fintype.card (Fin k ↪ Fin n) : ℚ) / (n : ℚ) ^ k =
      ∏ j ∈ Finset.range k, (1 - (j : ℚ) / n) := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin,
    cast_descFactorial_eq_prod,
    Finset.prod_congr rfl (fun (j : ℕ) _ => (show 1 - (j : ℚ) / n = (n - j) / n by field_simp)),
    Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]

end NTKB.NZM
