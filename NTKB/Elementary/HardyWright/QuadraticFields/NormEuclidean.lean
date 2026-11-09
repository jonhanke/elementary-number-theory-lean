/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Attr
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Aesop.BuiltinRules
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.QuadraticAlgebra.Int
import Mathlib.Algebra.QuadraticAlgebra.Integral
import Mathlib.Data.Int.Interval
import Mathlib.Data.Rat.Floor
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Bound
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
/-!
# Euclidean quadratic fields (Hardy–Wright §§ 14.7–14.9)

The quadratic field `k(√m)` is Mathlib's `QuadraticAlgebra ℚ m 0` (`ω² = m`), its integers are the
elements integral over `ℤ`, and the norm is `QuadraticAlgebra.norm`, `N(r + s√m) = r² - m s²`.

* `IsNormEuclidean m`: Hardy–Wright's property (E) of § 14.7, "given integers `γ, γ₁ ≠ 0` there is an
  integer `κ` with `|N(γ - κγ₁)| < |Nγ₁|`" (the field is *Euclidean* in the book, *norm-Euclidean* in
  the notes). `isNormEuclidean_iff` is the equivalent form (E′): every `ξ` of the field has an integer
  `κ` with `|N(ξ - κ)| < 1`.
* The integers of `k(√m)`, `m` squarefree: `exists_int_of_isIntegral` (`m ≡ 2, 3 (mod 4)`: they are
  `x + y√m`) and `exists_half_of_isIntegral` (in general they are `(A + B√m)/2`); conversely
  `isIntegral_mk_int`, `isIntegral_mk_half`.
* Theorem 246 (`isNormEuclidean_iff_of_neg`): for `m < 0` squarefree, `k(√m)` is Euclidean exactly
  for `m = -1, -2, -3, -7, -11`.
* Theorem 248 (`isNormEuclidean_of_mem`): `k(√m)` is Euclidean for `m = 2, 3, 5, 6, 7, 13, 17, 21, 29`.
* § 14.8 (`not_isNormEuclidean_23`): `k(√23)` is not Euclidean.
* Theorem 249 (`finite_isNormEuclidean`): there are only finitely many Euclidean fields `k(√m)` with
  `m > 0`, `m ≡ 2, 3 (mod 4)`.
-/

namespace NTKB.HardyWright

open QuadraticAlgebra

/-- Hardy–Wright's property (E) (§ 14.7): in `k(√m)`, for integers `γ, γ₁` with `γ₁ ≠ 0` there is an
integer `κ` with `|N(γ - κγ₁)| < |N γ₁|`. The field is then called *Euclidean* (in modern terms,
*norm-Euclidean*). -/
def IsNormEuclidean (m : ℤ) : Prop :=
  ∀ γ γ₁ : QuadraticAlgebra ℚ m 0, IsIntegral ℤ γ → IsIntegral ℤ γ₁ → γ₁ ≠ 0 →
    ∃ κ : QuadraticAlgebra ℚ m 0, IsIntegral ℤ κ ∧ |norm (γ - κ * γ₁)| < |norm γ₁|

variable {m : ℤ}

lemma qnorm_eq (z : QuadraticAlgebra ℚ m 0) : norm z = z.re ^ 2 - m * z.im ^ 2 := by
  rw [norm_def]; ring

lemma qtrace_eq (z : QuadraticAlgebra ℚ m 0) : trace z = 2 * z.re := by
  rw [trace_def]; ring

/-- An element of `k(√m)` is an integer if and only if its trace and norm are rational integers. -/
lemma isIntegral_iff_trace_norm {z : QuadraticAlgebra ℚ m 0} :
    IsIntegral ℤ z ↔ (∃ A : ℤ, (A : ℚ) = 2 * z.re) ∧ ∃ N : ℤ, (N : ℚ) = z.re ^ 2 - m * z.im ^ 2 := by
  rw [QuadraticAlgebra.isIntegral_iff, qtrace_eq, qnorm_eq]
  simp [Set.mem_range]

lemma isIntegral_mk_int (x y : ℤ) : IsIntegral ℤ (⟨x, y⟩ : QuadraticAlgebra ℚ m 0) :=
  isIntegral_iff_trace_norm.2 ⟨⟨2 * x, by push_cast; ring⟩, ⟨x ^ 2 - m * y ^ 2, by push_cast; ring⟩⟩

lemma isIntegral_mk_half (hm : m % 4 = 1) (x y : ℤ) :
    IsIntegral ℤ (⟨x + y / 2, y / 2⟩ : QuadraticAlgebra ℚ m 0) := by
  obtain ⟨k, hk⟩ : ∃ k, m = 4 * k + 1 := ⟨m / 4, by omega⟩
  refine isIntegral_iff_trace_norm.2 ⟨⟨2 * x + y, by push_cast; ring⟩,
    ⟨x ^ 2 + x * y - k * y ^ 2, ?_⟩⟩
  simp only [hk]; push_cast; ring

/-- If `d² ∣ 4m` with `m` squarefree and `d` odd, then `d = 1`. -/
private lemma eq_one_of_sq_dvd_of_odd (hm : Squarefree m) {d : ℕ} (hd : Odd d)
    (h : (d : ℤ) ^ 2 ∣ 4 * m) : d = 1 := by
  have hcop : IsCoprime ((d : ℤ) ^ 2) 4 := by
    have : IsCoprime (d : ℤ) 2 := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      have := Nat.Coprime.symm ((Nat.coprime_two_left).2 hd)
      exact_mod_cast this
    exact (this.pow_right (n := 2)).pow_left
  have h' : (d : ℤ) * d ∣ m := by rw [← sq]; exact hcop.dvd_of_dvd_mul_left h
  have := hm _ h'
  rw [Int.isUnit_iff] at this
  omega

/-- The imaginary part of an integer of `k(√m)` (`m` squarefree) is a half-integer. -/
lemma exists_im_half (hm : Squarefree m) {z : QuadraticAlgebra ℚ m 0} (hz : IsIntegral ℤ z) :
    ∃ B : ℤ, z.im = B / 2 := by
  obtain ⟨e, he, -⟩ := QuadraticAlgebra.Int.exists_im_den_sq_mul (a := m) (b := 0) (z := z)
    (by simpa using hz)
  rw [discr_def] at he
  set d := z.im.den
  rcases Nat.even_or_odd d with ⟨d', hd'⟩ | hd
  · -- `d = 2d'`, `d'² ∣ m`, so `d' = 1`
    have h1 : (d' : ℤ) * d' ∣ m := ⟨e, by
      have : (4 : ℤ) * m = 4 * (d' * d' * e) := by rw [show (4 : ℤ) * m = _ by simpa using he]; push_cast [hd']; ring
      linarith⟩
    have := hm _ h1
    rw [Int.isUnit_iff] at this
    have hd1 : d' = 1 := by omega
    have hden : (z.im.den : ℚ) = 2 := by
      have : z.im.den = 2 := by omega
      simp [this]
    exact ⟨z.im.num, by rw [← hden, Rat.num_div_den]⟩
  · have h1 := eq_one_of_sq_dvd_of_odd hm hd ⟨e, by simpa using he⟩
    have e1 : (z.im.num : ℚ) = z.im := Rat.intCast_num_of_den_eq_one h1
    refine ⟨2 * z.im.num, ?_⟩
    push_cast; rw [e1]; ring

/-- The integers of `k(√m)` (`m` squarefree) are `(A + B√m)/2` with `A, B` rational integers. -/
lemma exists_half_of_isIntegral (hm : Squarefree m) {z : QuadraticAlgebra ℚ m 0}
    (hz : IsIntegral ℤ z) : ∃ A B : ℤ, z = ⟨A / 2, B / 2⟩ := by
  obtain ⟨B, hB⟩ := exists_im_half hm hz
  obtain ⟨⟨A, hA⟩, -⟩ := isIntegral_iff_trace_norm.1 hz
  exact ⟨A, B, by ext <;> simp [hB, hA]⟩

/-- For `m` squarefree, `m ≡ 2, 3 (mod 4)`, the integers of `k(√m)` are `x + y√m` (Theorem 238). -/
lemma exists_int_of_isIntegral (hm : Squarefree m) (h4 : m % 4 = 2 ∨ m % 4 = 3)
    {z : QuadraticAlgebra ℚ m 0} (hz : IsIntegral ℤ z) : ∃ x y : ℤ, z = ⟨x, y⟩ := by
  obtain ⟨e, he, he4⟩ := QuadraticAlgebra.Int.exists_im_den_sq_mul (a := m) (b := 0) (z := z)
    (by simpa using hz)
  rw [discr_def] at he
  have hd : z.im.den = 1 := by
    rcases Nat.even_or_odd z.im.den with ⟨d', hd'⟩ | hd
    · exfalso
      have hm' : m = d' * d' * e := by
        have : (4 : ℤ) * m = 4 * (d' * d' * e) := by
          rw [show (4 : ℤ) * m = _ by simpa using he]; push_cast [hd']; ring
        linarith
      have := hm d' ⟨e, by rw [hm']⟩
      rw [Int.isUnit_iff] at this
      rcases this with h | h <;> rw [h] at hm' <;> omega
    · exact eq_one_of_sq_dvd_of_odd hm hd ⟨e, by simpa using he⟩
  have him : z.im ∈ Set.range (algebraMap ℤ ℚ) :=
    ⟨z.im.num, by simp [← Rat.den_eq_one_iff, hd]⟩
  obtain ⟨w, hw⟩ := (QuadraticAlgebra.Int.mem_range_iff_im_mem_range (a := m) (b := 0) (z := z)
    hz).2 him
  refine ⟨w.re, w.im, ?_⟩
  rw [← hw]
  ext
  · exact QuadraticAlgebra.Int.re_algebraMap w
  · exact QuadraticAlgebra.Int.im_algebraMap w

lemma qf_natCast_eq_mk (n : ℕ) : (n : QuadraticAlgebra ℚ m 0) = ⟨((n : ℤ) : ℚ), ((0 : ℤ) : ℚ)⟩ := by
  ext <;> simp

/-- Property (E′) of § 14.7: when `m` is not a square, `k(√m)` is Euclidean if and only if for every
`ξ` of the field there is an integer `κ` with `|N(ξ - κ)| < 1`. -/
lemma isNormEuclidean_iff (hm : ¬ IsSquare (m : ℚ)) :
    IsNormEuclidean m ↔
      ∀ ξ : QuadraticAlgebra ℚ m 0, ∃ κ, IsIntegral ℤ κ ∧ |norm (ξ - κ)| < 1 := by
  haveI : Fact (¬ IsSquare (m : ℚ)) := ⟨hm⟩
  constructor
  · intro H ξ
    set n : ℕ := ξ.re.den * ξ.im.den with hn
    have hn0 : (n : ℚ) ≠ 0 := by rw [hn]; push_cast; positivity
    let γ : QuadraticAlgebra ℚ m 0 :=
      ⟨((ξ.re.num * ξ.im.den : ℤ) : ℚ), ((ξ.im.num * ξ.re.den : ℤ) : ℚ)⟩
    have hγ : γ = (n : QuadraticAlgebra ℚ m 0) * ξ := by
      have h1 := Rat.mul_den_eq_num ξ.re
      have h2 := Rat.mul_den_eq_num ξ.im
      ext
      · simp only [γ, hn]; push_cast; simp; rw [← h1]; ring
      · simp only [γ, hn]; push_cast; simp; rw [← h2]; ring
    have hn1 : (n : QuadraticAlgebra ℚ m 0) ≠ 0 := by
      intro h0
      apply hn0
      have := congrArg QuadraticAlgebra.re h0
      simpa using this
    obtain ⟨κ, hκ, hlt⟩ := H γ n (isIntegral_mk_int _ _)
      (by rw [qf_natCast_eq_mk]; exact isIntegral_mk_int _ _) hn1
    refine ⟨κ, hκ, ?_⟩
    rw [hγ, show (n : QuadraticAlgebra ℚ m 0) * ξ - κ * n = n * (ξ - κ) by ring, map_mul,
      QuadraticAlgebra.norm_natCast, abs_mul] at hlt
    have hpos : 0 < |(n : ℚ) ^ 2| := by positivity
    by_contra hge
    push Not at hge
    nlinarith
  · intro H γ γ₁ _ _ h0
    obtain ⟨κ, hκ, hlt⟩ := H (γ / γ₁)
    refine ⟨κ, hκ, ?_⟩
    have e : γ - κ * γ₁ = (γ / γ₁ - κ) * γ₁ := by field_simp
    rw [e, map_mul, abs_mul]
    have : 0 < |norm γ₁| := abs_pos.2 ((norm_eq_zero_iff_eq_zero).not.2 h0)
    nlinarith

lemma not_isSquare_of_neg (hm : m < 0) : ¬ IsSquare (m : ℚ) := by
  rintro ⟨r, hr⟩
  have : (m : ℚ) < 0 := by exact_mod_cast hm
  nlinarith [mul_self_nonneg r]

/-- An integer strictly between two consecutive squares is not a square. -/
lemma not_isSquare_of_between {k n : ℤ} (hn : 0 ≤ n) (h1 : n ^ 2 < k) (h2 : k < (n + 1) ^ 2) :
    ¬ IsSquare (k : ℚ) := by
  rw [Rat.isSquare_intCast_iff]
  rintro ⟨r, rfl⟩
  have h1' : n ^ 2 < |r| ^ 2 := by rw [sq_abs]; nlinarith
  have h2' : |r| ^ 2 < (n + 1) ^ 2 := by rw [sq_abs]; nlinarith
  have := (pow_lt_pow_iff_left₀ hn (abs_nonneg r) (by norm_num : (2 : ℕ) ≠ 0)).1 h1'
  have := (pow_lt_pow_iff_left₀ (abs_nonneg r) (by linarith) (by norm_num : (2 : ℕ) ≠ 0)).1 h2'
  omega

lemma sq_le_quarter {x : ℚ} (h : |x| ≤ 1 / 2) : x ^ 2 ≤ 1 / 4 := by
  have := abs_le.1 h
  nlinarith

/-- The inequalities of § 14.8: if `|δ|, |σ| ≤ 1/2`, `0 < n < 8` and `nσ² ≠ 5/4`, then
`|(δ - x)² - nσ²| < 1` for one of `x = 0, 1, -1` (the book's `P(x, 0)`, `N(x, 0)`). -/
lemma exists_abs_sub_sq_lt_one {δ σ n : ℚ} (hδ : |δ| ≤ 1 / 2) (hσ : |σ| ≤ 1 / 2) (hn0 : 0 < n)
    (hn : n < 8) (h5 : n * σ ^ 2 ≠ 5 / 4) : ∃ x : ℤ, |(δ - x) ^ 2 - n * σ ^ 2| < 1 := by
  by_contra! H
  have h0 := H 0
  have h1 := H 1
  have h2 := H (-1)
  push_cast at h0 h1 h2
  have hδ' := abs_le.1 hδ
  have hδ2 := sq_le_quarter hδ
  have hσ2 := sq_le_quarter hσ
  have hnσ : n * σ ^ 2 < 2 := by nlinarith
  have hnσ0 : 0 ≤ n * σ ^ 2 := by positivity
  -- `N(0, 0)`: `nσ² ≥ 1 + δ²`
  have N0 : 1 + δ ^ 2 ≤ n * σ ^ 2 := by
    rcases le_abs.1 h0 with h | h
    · nlinarith
    · linarith
  -- `N(1, 0)`
  have N1 : 1 + (δ - 1) ^ 2 ≤ n * σ ^ 2 := by
    rcases le_abs.1 h1 with h | h
    · exfalso
      have hd : δ = -1 / 2 := by nlinarith
      subst hd
      exact h5 (le_antisymm (by nlinarith) (by nlinarith))
    · linarith
  -- `N(-1, 0)`
  have N2 : 1 + (δ + 1) ^ 2 ≤ n * σ ^ 2 := by
    rcases le_abs.1 h2 with h | h
    · exfalso
      have hd : δ = 1 / 2 := by nlinarith
      subst hd
      exact h5 (le_antisymm (by nlinarith) (by nlinarith))
    · linarith
  rcases le_total 0 δ with hd | hd <;> nlinarith

/-- § 14.8, the case `m ≢ 1 (mod 4)` of Theorem 248: `k(√m)` is Euclidean when `0 < m < 8`. -/
lemma isNormEuclidean_of_lt_eight (hm0 : 0 < m) (hm8 : m < 8) (hsq : ¬ IsSquare (m : ℚ))
    (h5 : ∀ σ : ℚ, (m : ℚ) * σ ^ 2 ≠ 5 / 4) : IsNormEuclidean m := by
  rw [isNormEuclidean_iff hsq]
  intro ξ
  obtain ⟨x, hx⟩ := exists_abs_sub_sq_lt_one (abs_sub_round ξ.re) (abs_sub_round ξ.im)
    (by exact_mod_cast hm0) (by exact_mod_cast hm8) (h5 _)
  refine ⟨⟨((round ξ.re + x : ℤ) : ℚ), ((round ξ.im : ℤ) : ℚ)⟩, isIntegral_mk_int _ _, ?_⟩
  rw [qnorm_eq]
  convert hx using 2
  simp only [QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub]
  push_cast; ring

/-- § 14.8, the case `m ≡ 1 (mod 4)` of Theorem 248: `k(√m)` is Euclidean when `0 < m < 32`. -/
lemma isNormEuclidean_of_lt_thirtytwo (hm1 : m % 4 = 1) (hm0 : 0 < m) (hm8 : m < 32)
    (hsq : ¬ IsSquare (m : ℚ)) (h5 : ∀ σ : ℚ, |σ| ≤ 1 / 2 → (m / 4 : ℚ) * σ ^ 2 ≠ 5 / 4) :
    IsNormEuclidean m := by
  rw [isNormEuclidean_iff hsq]
  intro ξ
  set y := round (2 * ξ.im)
  set x₀ := round (ξ.re - y / 2)
  obtain ⟨x, hx⟩ := exists_abs_sub_sq_lt_one (abs_sub_round (ξ.re - y / 2))
    (abs_sub_round (2 * ξ.im)) (n := m / 4) (by positivity)
    (by have : (m : ℚ) < 32 := by exact_mod_cast hm8
        linarith) (h5 _ (abs_sub_round _))
  refine ⟨⟨((x₀ + x : ℤ) : ℚ) + (y : ℚ) / 2, (y : ℚ) / 2⟩, isIntegral_mk_half hm1 _ _, ?_⟩
  rw [qnorm_eq]
  convert hx using 2
  simp only [QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub]
  push_cast; ring

/-- **Theorem 248.** `k(√m)` is Euclidean when `m = 2, 3, 5, 6, 7, 13, 17, 21, 29`. -/
@[kb "hardywright2008" "Thm 248, p. 296"]
theorem isNormEuclidean_of_mem (hm : m ∈ ({2, 3, 5, 6, 7, 13, 17, 21, 29} : Finset ℤ)) :
    IsNormEuclidean m := by
  -- `nσ² = 5/4` would make `5m` a rational square
  have key : ∀ σ : ℚ, (m : ℚ) * σ ^ 2 = 5 / 4 → IsSquare ((5 * m : ℤ) : ℚ) := fun σ h ↦
    ⟨2 * m * σ, by push_cast; linear_combination (-4 * (m : ℚ)) * h⟩
  have key' : ∀ σ : ℚ, (m / 4 : ℚ) * σ ^ 2 = 5 / 4 → IsSquare ((5 * m : ℤ) : ℚ) := fun σ h ↦
    ⟨m * σ, by push_cast; linear_combination (-4 * (m : ℚ)) * h⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact isNormEuclidean_of_lt_eight (by norm_num) (by norm_num)
      (not_isSquare_of_between (n := 1) (by norm_num) (by norm_num) (by norm_num))
      fun σ h ↦ not_isSquare_of_between (n := 3) (by norm_num) (by norm_num) (by norm_num) (key σ h)
  · exact isNormEuclidean_of_lt_eight (by norm_num) (by norm_num)
      (not_isSquare_of_between (n := 1) (by norm_num) (by norm_num) (by norm_num))
      fun σ h ↦ not_isSquare_of_between (n := 3) (by norm_num) (by norm_num) (by norm_num) (key σ h)
  · refine isNormEuclidean_of_lt_thirtytwo (by norm_num) (by norm_num) (by norm_num)
      (not_isSquare_of_between (n := 2) (by norm_num) (by norm_num) (by norm_num)) fun σ hσ h ↦ ?_
    have := sq_le_quarter hσ
    push_cast at h
    nlinarith
  · exact isNormEuclidean_of_lt_eight (by norm_num) (by norm_num)
      (not_isSquare_of_between (n := 2) (by norm_num) (by norm_num) (by norm_num))
      fun σ h ↦ not_isSquare_of_between (n := 5) (by norm_num) (by norm_num) (by norm_num) (key σ h)
  · exact isNormEuclidean_of_lt_eight (by norm_num) (by norm_num)
      (not_isSquare_of_between (n := 2) (by norm_num) (by norm_num) (by norm_num))
      fun σ h ↦ not_isSquare_of_between (n := 5) (by norm_num) (by norm_num) (by norm_num) (key σ h)
  · exact isNormEuclidean_of_lt_thirtytwo (by norm_num) (by norm_num) (by norm_num)
      (not_isSquare_of_between (n := 3) (by norm_num) (by norm_num) (by norm_num))
      fun σ _ h ↦ not_isSquare_of_between (n := 8) (by norm_num) (by norm_num) (by norm_num)
        (key' σ h)
  · exact isNormEuclidean_of_lt_thirtytwo (by norm_num) (by norm_num) (by norm_num)
      (not_isSquare_of_between (n := 4) (by norm_num) (by norm_num) (by norm_num))
      fun σ _ h ↦ not_isSquare_of_between (n := 9) (by norm_num) (by norm_num) (by norm_num)
        (key' σ h)
  · exact isNormEuclidean_of_lt_thirtytwo (by norm_num) (by norm_num) (by norm_num)
      (not_isSquare_of_between (n := 4) (by norm_num) (by norm_num) (by norm_num))
      fun σ _ h ↦ not_isSquare_of_between (n := 10) (by norm_num) (by norm_num) (by norm_num)
        (key' σ h)
  · exact isNormEuclidean_of_lt_thirtytwo (by norm_num) (by norm_num) (by norm_num)
      (not_isSquare_of_between (n := 5) (by norm_num) (by norm_num) (by norm_num))
      fun σ _ h ↦ not_isSquare_of_between (n := 12) (by norm_num) (by norm_num) (by norm_num)
        (key' σ h)

lemma one_le_sq_sub_half (x : ℤ) : (1 : ℚ) / 4 ≤ (1 / 2 - x) ^ 2 := by
  have h : (1 : ℤ) ≤ (1 - 2 * x) ^ 2 := by
    have : 1 - 2 * x ≠ 0 := by omega
    nlinarith [sq_pos_of_ne_zero this, Int.one_le_abs this, sq_abs (1 - 2 * x)]
  have h' : (1 : ℚ) ≤ (1 - 2 * x) ^ 2 := by exact_mod_cast h
  nlinarith

lemma one_le_sq_sub_quarter (x : ℤ) : (1 : ℚ) / 16 ≤ (1 / 4 - x / 2) ^ 2 := by
  have h : (1 : ℤ) ≤ (1 - 2 * x) ^ 2 := by
    have : 1 - 2 * x ≠ 0 := by omega
    nlinarith [sq_pos_of_ne_zero this, Int.one_le_abs this, sq_abs (1 - 2 * x)]
  have h' : (1 : ℚ) ≤ (1 - 2 * x) ^ 2 := by exact_mod_cast h
  nlinarith

/-- **Theorem 246.** There are just five complex Euclidean quadratic fields, `k(√m)` with
`m = -1, -2, -3, -7, -11`. -/
@[kb "hardywright2008" "Thm 246, p. 294"]
theorem isNormEuclidean_iff_of_neg (hm0 : m < 0) (hm : Squarefree m) :
    IsNormEuclidean m ↔ m = -1 ∨ m = -2 ∨ m = -3 ∨ m = -7 ∨ m = -11 := by
  rw [isNormEuclidean_iff (not_isSquare_of_neg hm0)]
  have hm0' : (m : ℚ) < 0 := by exact_mod_cast hm0
  constructor
  · intro H
    by_contra hne
    push Not at hne
    by_cases h4 : m % 4 = 1
    · -- (ii) `ξ = 1/4 + √m/4`
      have hm15 : m ≤ -15 := by omega
      have hm15' : (m : ℚ) ≤ -15 := by exact_mod_cast hm15
      obtain ⟨κ, hκ, hlt⟩ := H ⟨1 / 4, 1 / 4⟩
      obtain ⟨A, B, rfl⟩ := exists_half_of_isIntegral hm hκ
      rw [qnorm_eq] at hlt
      simp only [QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub] at hlt
      have h1 := one_le_sq_sub_quarter A
      have h2 := one_le_sq_sub_quarter B
      rw [abs_lt] at hlt
      nlinarith
    · -- (i) `ξ = 1/2 + √m/2`
      have h4' : m % 4 = 2 ∨ m % 4 = 3 := by
        rcases (show m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 by omega) with h | h | h | h
        · exfalso
          have := hm 2 ⟨m / 4, by omega⟩
          rw [Int.isUnit_iff] at this
          omega
        · exact absurd h h4
        · exact Or.inl h
        · exact Or.inr h
      have hm3 : m ≤ -3 := by omega
      have hm3' : (m : ℚ) ≤ -3 := by exact_mod_cast hm3
      obtain ⟨κ, hκ, hlt⟩ := H ⟨1 / 2, 1 / 2⟩
      obtain ⟨x, y, rfl⟩ := exists_int_of_isIntegral hm h4' hκ
      rw [qnorm_eq] at hlt
      simp only [QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub] at hlt
      have h1 := one_le_sq_sub_half x
      have h2 := one_le_sq_sub_half y
      rw [abs_lt] at hlt
      nlinarith
  · intro hm' ξ
    have hr := abs_sub_round ξ.re
    have hs := abs_sub_round ξ.im
    rcases hm' with rfl | rfl | rfl | rfl | rfl
    · refine ⟨⟨((round ξ.re : ℤ) : ℚ), ((round ξ.im : ℤ) : ℚ)⟩, isIntegral_mk_int _ _, ?_⟩
      rw [qnorm_eq, abs_lt]
      simp only [QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub]
      have := sq_le_quarter hr
      have := sq_le_quarter hs
      push_cast
      constructor <;> nlinarith [sq_nonneg (ξ.re - round ξ.re), sq_nonneg (ξ.im - round ξ.im)]
    · refine ⟨⟨((round ξ.re : ℤ) : ℚ), ((round ξ.im : ℤ) : ℚ)⟩, isIntegral_mk_int _ _, ?_⟩
      rw [qnorm_eq, abs_lt]
      simp only [QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub]
      have := sq_le_quarter hr
      have := sq_le_quarter hs
      push_cast
      constructor <;> nlinarith [sq_nonneg (ξ.re - round ξ.re), sq_nonneg (ξ.im - round ξ.im)]
    all_goals
      set y := round (2 * ξ.im)
      have h1 := sq_le_quarter (abs_sub_round (ξ.re - y / 2))
      have h2 := sq_le_quarter (abs_sub_round (2 * ξ.im))
      refine ⟨⟨((round (ξ.re - y / 2) : ℤ) : ℚ) + (y : ℚ) / 2, (y : ℚ) / 2⟩,
        isIntegral_mk_half (by norm_num) _ _, ?_⟩
      rw [qnorm_eq, abs_lt]
      simp only [QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub]
      push_cast
      constructor <;> nlinarith [sq_nonneg (ξ.re - y / 2 - round (ξ.re - y / 2)),
        sq_nonneg (2 * ξ.im - y)]

/-- § 14.8: `k(√23)` is not Euclidean (take `r = 0`, `s = 7/23`). -/
@[kb "hardywright2008" "§ 14.8, p. 298"]
theorem not_isNormEuclidean_23 : ¬ IsNormEuclidean 23 := by
  have hsq : ¬ IsSquare ((23 : ℤ) : ℚ) :=
    not_isSquare_of_between (n := 4) (by norm_num) (by norm_num) (by norm_num)
  rw [isNormEuclidean_iff hsq]
  intro H
  obtain ⟨κ, hκ, hlt⟩ := H ⟨0, 7 / 23⟩
  have hsf : Squarefree (23 : ℤ) := (Int.prime_iff_natAbs_prime.2 (by norm_num)).squarefree
  obtain ⟨x, y, rfl⟩ := exists_int_of_isIntegral hsf (by norm_num) hκ
  rw [qnorm_eq] at hlt
  simp only [QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub] at hlt
  -- `ν = 23x² - (23y - 7)²` satisfies `|ν| < 23` and `ν ≡ -3 (mod 23)`
  set w : ℤ := x ^ 2 + 14 * y - 23 * y ^ 2
  have hν : |((23 * w - 49 : ℤ) : ℚ)| < 23 := by
    have e : ((23 * w - 49 : ℤ) : ℚ) = 23 * ((0 : ℚ) - x) ^ 2 * 1 - 23 * (23 : ℚ) * (7 / 23 - y) ^ 2 := by
      simp only [w]; push_cast; ring
    rw [e, abs_lt] at *
    push_cast at hlt
    constructor <;> nlinarith [hlt.1, hlt.2]
  have hν' : |23 * w - 49| < 23 := by exact_mod_cast hν
  have hw : w = 2 ∨ w = 3 := by rw [abs_lt] at hν'; omega
  -- `23x² - Y² = -3` or `20` with `Y = 23y - 7`: impossible modulo `9` and `16`
  have e : 23 * x ^ 2 - (23 * y - 7) ^ 2 = 23 * w - 49 := by simp only [w]; ring
  rcases hw with hw | hw <;> rw [hw] at e <;> norm_num at e
  · have := congrArg (fun t : ℤ ↦ (t : ZMod 9)) e
    push_cast at this
    generalize (x : ZMod 9) = a at this
    generalize (y : ZMod 9) = b at this
    revert a b; decide
  · have := congrArg (fun t : ℤ ↦ (t : ZMod 16)) e
    push_cast at this
    generalize (x : ZMod 16) = a at this
    generalize (y : ZMod 16) = b at this
    revert a b; decide

/-- For `2 ≤ c ≤ 5` and `m > 100` there is an odd `t` with `cm < t² < (c + 1)m`. -/
lemma exists_odd_sq_between {c : ℤ} (hc2 : 2 ≤ c) (hc5 : c ≤ 5) (hm : 100 < m) :
    ∃ t : ℤ, Odd t ∧ c * m < t ^ 2 ∧ t ^ 2 < (c + 1) * m := by
  set n := (c * m).toNat with hn
  have hn' : (n : ℤ) = c * m := Int.toNat_of_nonneg (by nlinarith)
  set s := n.sqrt
  have h1 : s ^ 2 ≤ n := by rw [sq]; exact Nat.sqrt_le n
  have h2 : n < (s + 1) ^ 2 := by rw [sq]; exact Nat.lt_succ_sqrt n
  have h1' : (s : ℤ) ^ 2 ≤ c * m := by rw [← hn']; exact_mod_cast h1
  have h2' : c * m < ((s : ℤ) + 1) ^ 2 := by rw [← hn']; exact_mod_cast h2
  have hs0 : (0 : ℤ) ≤ s := by positivity
  have hs : 4 * (s : ℤ) + 4 < m := by nlinarith
  rcases Int.even_or_odd ((s : ℤ) + 1) with he | ho
  · refine ⟨s + 2, by rw [show (s : ℤ) + 2 = s + 1 + 1 by ring]; exact he.add_one, ?_, ?_⟩ <;>
      nlinarith
  · exact ⟨s + 1, ho, h2', by nlinarith⟩

/-- The heart of Theorem 249: `k(√m)` is not Euclidean when `m > 100`, `m ≡ 2, 3 (mod 4)`. -/
lemma not_isNormEuclidean_of_large (hm : 100 < m) (hsf : Squarefree m)
    (h4 : m % 4 = 2 ∨ m % 4 = 3) : ¬ IsNormEuclidean m := by
  have hsq : ¬ IsSquare (m : ℚ) := by
    rw [Rat.isSquare_intCast_iff]
    rintro ⟨r, rfl⟩
    have := hsf r dvd_rfl
    rw [Int.isUnit_iff] at this
    rcases this with rfl | rfl <;> norm_num at hm
  rw [isNormEuclidean_iff hsq]
  intro H
  -- `c = 5` when `m ≡ 3`, `c = 2` when `m ≡ 2 (mod 4)`
  obtain ⟨c, hc2, hc5, hc⟩ : ∃ c : ℤ, 2 ≤ c ∧ c ≤ 5 ∧ ((m % 4 = 3 ∧ c = 5) ∨ (m % 4 = 2 ∧ c = 2)) := by
    rcases h4 with h | h
    · exact ⟨2, by norm_num, by norm_num, Or.inr ⟨h, rfl⟩⟩
    · exact ⟨5, by norm_num, by norm_num, Or.inl ⟨h, rfl⟩⟩
  obtain ⟨t, ⟨k, rfl⟩, ht1, ht2⟩ := exists_odd_sq_between hc2 hc5 hm
  have hm0 : (0 : ℚ) < m := by exact_mod_cast (show (0 : ℤ) < m by omega)
  obtain ⟨κ, hκ, hlt⟩ := H ⟨0, ((2 * k + 1 : ℤ) : ℚ) / m⟩
  obtain ⟨x, y, rfl⟩ := exists_int_of_isIntegral hsf h4 hκ
  rw [qnorm_eq] at hlt
  simp only [QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub] at hlt
  -- `z² - m x² = t² + m K`, `|z² - m x²| < m`, with `z = t - my`
  set K : ℤ := -2 * (2 * k + 1) * y + m * y ^ 2 - x ^ 2
  have hE : |(((2 * k + 1) ^ 2 + m * K : ℤ) : ℚ)| < m := by
    have e : (((2 * k + 1) ^ 2 + m * K : ℤ) : ℚ) =
        -((m : ℚ) * (((0 : ℚ) - x) ^ 2 - m * (((2 * k + 1 : ℤ) : ℚ) / m - y) ^ 2)) := by
      simp only [K]; push_cast; field_simp; ring
    rw [e, abs_neg, abs_mul, abs_of_pos hm0]
    nlinarith [abs_nonneg (((0 : ℚ) - x) ^ 2 - m * (((2 * k + 1 : ℤ) : ℚ) / m - y) ^ 2)]
  have hE' : |(2 * k + 1) ^ 2 + m * K| < m := by exact_mod_cast hE
  rw [abs_lt] at hE'
  have hK : K = -c ∨ K = -(c + 1) := by
    have hlo : -(c + 2) < K := by
      by_contra h; push Not at h; nlinarith
    have hhi : K < 1 - c := by
      by_contra h; push Not at h; nlinarith
    omega
  -- `t² - z² = m(c - x²)` or `m(c + 1 - x²)`, impossible modulo `8`
  have key : (2 * k + 1) ^ 2 - (2 * k + 1 - m * y) ^ 2 = m * (-K - x ^ 2) := by
    simp only [K]; ring
  obtain ⟨j, hj⟩ : ∃ j, m = 4 * j + m % 4 := ⟨m / 4, by omega⟩
  rcases hc with ⟨h4', rfl⟩ | ⟨h4', rfl⟩ <;> rw [h4'] at hj <;> rcases hK with hK | hK <;>
    rw [hK, hj] at key <;>
    · have := congrArg (fun u : ℤ ↦ (u : ZMod 8)) key
      push_cast at this
      generalize (k : ZMod 8) = a at this
      generalize (y : ZMod 8) = b at this
      generalize (x : ZMod 8) = d at this
      generalize (j : ZMod 8) = e at this
      revert a b d e; decide

/-- **Theorem 249.** The number of Euclidean fields `k(√m)` with `m > 0`, `m ≡ 2` or `3 (mod 4)`
(`m` squarefree) is finite. -/
@[kb "hardywright2008" "Thm 249, p. 298"]
theorem finite_isNormEuclidean :
    {m : ℤ | 0 < m ∧ Squarefree m ∧ (m % 4 = 2 ∨ m % 4 = 3) ∧ IsNormEuclidean m}.Finite := by
  apply (Set.finite_Icc (0 : ℤ) 100).subset
  rintro m ⟨hm0, hsf, h4, hE⟩
  refine ⟨hm0.le, ?_⟩
  by_contra hlt
  push Not at hlt
  exact not_isNormEuclidean_of_large hlt hsf h4 hE

end NTKB.HardyWright
