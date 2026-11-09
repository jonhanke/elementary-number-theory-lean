/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.Partitions.JacobiTriple

/-!
# Special cases of Jacobi's identity (Hardy–Wright, Chapter XIX, §§ 19.4, 19.9)

Hardy–Wright write `x^k` for `x`, `-x^l` and `x^l` for `z` in Jacobi's identity (Theorem 352) and
obtain (19.9.1) and (19.9.2) with `k, l` half-integers allowed. We parametrise by natural numbers
`a = k - l ≥ 1` and `b = k + l ≥ 1` (so `k = (a+b)/2`, `l = (b-a)/2`): for `‖x‖ < 1`,

* (19.9.1): `∏_{n ≥ 0} (1 - x^{(a+b)n+a})(1 - x^{(a+b)n+b})(1 - x^{(a+b)n+a+b}) =
  ∑_{n ∈ ℤ} (-1)^n x^{((a+b)n² + (b-a)n)/2}`;
* (19.9.2): `∏_{n ≥ 0} (1 + x^{(a+b)n+a})(1 + x^{(a+b)n+b})(1 - x^{(a+b)n+a+b}) =
  ∑_{n ∈ ℤ} x^{((a+b)n² + (b-a)n)/2}`.

The exponent `((a+b)n² + (b-a)n)/2` is an integer division of an even integer (`jacobiExp`,
`two_mul_jacobiExp`) and appears as an integer power (`zpow`) of `x`; it is never negative. The proof
applies `NTKB.Apostol.jacobi_triple_product` to `X = y^{a+b}` and `w = ± y^{b-a}` where `y² = x`
(for `x = 0` both sides are `1`). Theorems 355 (`(a, b) = (1, 4)`) and 356 (`(a, b) = (2, 3)`) are
stated with explicit exponents `n(5n+3)/2` and `n(5n+1)/2`, and Euler's identity (19.9.3)/Theorem 353
is the case `(a, b) = (1, 2)` in the form of a product over the blocks `3n+1, 3n+2, 3n+3`
(`jacobi_special_one_two`).

Theorem 354, `(1 - x²)(1 - x⁴)(1 - x⁶)… / ((1 - x)(1 - x³)(1 - x⁵)…) = 1 + x + x³ + x⁶ + …`, follows
the book: Theorem 352 with `x ↦ y²` and `z = y` gives `∏ (1 - x^{n+1})(1 + x^{n+1})(1 + xⁿ) =
2 ∑_{n ≥ 0} x^{n(n+1)/2}`, and (19.4.7) `∏ (1 + xⁿ) · ∏ (1 - x^{2n-1}) = 1` (since `1 + xⁿ = (1 - x^{2n})/(1 - xⁿ)`
and `∏ (1 - xⁿ)` is the product of the odd and even parts).
-/

open Complex Finset Filter NTKB.Apostol
open scoped Topology

namespace NTKB.HardyWright

/-! ### The exponent -/

/-- The exponent `((a+b)n² + (b-a)n)/2` of (19.9.1), (19.9.2) (integer division of an even integer). -/
def jacobiExp (a b : ℕ) (n : ℤ) : ℤ := (((a + b : ℕ) : ℤ) * n ^ 2 + ((b : ℤ) - a) * n) / 2

theorem two_mul_jacobiExp (a b : ℕ) (n : ℤ) :
    2 * jacobiExp a b n = ((a + b : ℕ) : ℤ) * n ^ 2 + ((b : ℤ) - a) * n := by
  obtain ⟨k, hk⟩ := Int.even_mul_succ_self n
  have h : ((a + b : ℕ) : ℤ) * n ^ 2 + ((b : ℤ) - a) * n =
      2 * (((a + b : ℕ) : ℤ) * k - a * n) := by
    push_cast
    linear_combination ((a : ℤ) + b) * hk
  rw [jacobiExp, h, Int.mul_ediv_cancel_left _ (by norm_num)]

theorem jacobiExp_zero (a b : ℕ) : jacobiExp a b 0 = 0 := by simp [jacobiExp]

theorem jacobiExp_pos {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) {n : ℤ} (hn : n ≠ 0) :
    0 < jacobiExp a b n := by
  have h := two_mul_jacobiExp a b n
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  push_cast at h
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · have h1 : n ≤ -1 := by omega
    nlinarith [mul_nonneg (sub_nonneg.2 ha') (sq_nonneg n), mul_nonneg (by linarith : (0 : ℤ) ≤ a)
      (by nlinarith : (0 : ℤ) ≤ n ^ 2 - n), mul_nonneg (by linarith : (0 : ℤ) ≤ b)
      (by nlinarith : (0 : ℤ) ≤ n ^ 2 + n), mul_pos (by linarith : (0 : ℤ) < b)
      (by nlinarith : (0 : ℤ) < n ^ 2 + n + 1)]
  · have h1 : 1 ≤ n := by omega
    nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ a) (by nlinarith : (0 : ℤ) ≤ n ^ 2 - n),
      mul_pos (by linarith : (0 : ℤ) < b) (by nlinarith : (0 : ℤ) < n ^ 2 + n)]

/-! ### Theorems (19.9.1) and (19.9.2) -/

section Core

/-- The case `x = y²`, `y ≠ 0`; `ε = ±1` is the sign. -/
theorem jacobi_special_aux {y : ℂ} (hy : ‖y‖ < 1) (hy0 : y ≠ 0) {ε : ℂ} (hε : ε * ε = 1) {a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Summable (fun n : ℤ ↦ ε ^ n * (y ^ 2) ^ jacobiExp a b n) ∧
    HasProd (fun n : ℕ ↦ (1 - (y ^ 2) ^ ((a + b) * n + a + b)) *
        (1 + ε * (y ^ 2) ^ ((a + b) * n + b)) * (1 + ε * (y ^ 2) ^ ((a + b) * n + a)))
      (∑' n : ℤ, ε ^ n * (y ^ 2) ^ jacobiExp a b n) := by
  have hε0 : ε ≠ 0 := left_ne_zero_of_mul_eq_one hε
  have hX : ‖y ^ (a + b)‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hy (by omega)
  have hw : ε * y ^ ((b : ℤ) - a) ≠ 0 := mul_ne_zero hε0 (zpow_ne_zero _ hy0)
  obtain ⟨hs, hp⟩ := jacobi_triple_product hX hw
  have hterm : ∀ n : ℤ, (y ^ (a + b)) ^ (n ^ 2) * (ε * y ^ ((b : ℤ) - a)) ^ n =
      ε ^ n * (y ^ 2) ^ jacobiExp a b n := by
    intro n
    have e1 : (y ^ (a + b)) ^ (n ^ 2) = y ^ (((a + b : ℕ) : ℤ) * n ^ 2) := by
      rw [← zpow_natCast y (a + b), ← zpow_mul]
    have e2 : (y ^ ((b : ℤ) - a)) ^ n = y ^(((b : ℤ) - a) * n) := by rw [← zpow_mul]
    have e3 : (y ^ 2) ^ jacobiExp a b n =
        y ^ (((a + b : ℕ) : ℤ) * n ^ 2 + ((b : ℤ) - a) * n) := by
      rw [← zpow_natCast y 2, ← zpow_mul, ← two_mul_jacobiExp]
      norm_num
    rw [mul_zpow, e1, e2, e3, zpow_add₀ hy0]
    ring
  have p1 : ∀ n : ℕ, (y ^ (a + b)) ^ (2 * n + 1) * y ^ ((b : ℤ) - a) =
      (y ^ 2) ^ ((a + b) * n + b) := by
    intro n
    rw [← pow_mul y 2, ← pow_mul y (a + b), ← zpow_natCast y ((a + b) * (2 * n + 1)),
      ← zpow_natCast y (2 * ((a + b) * n + b)), ← zpow_add₀ hy0]
    congr 1; push_cast; ring
  have p2 : ∀ n : ℕ, (y ^ (a + b)) ^ (2 * n + 1) * (y ^ ((b : ℤ) - a))⁻¹ =
      (y ^ 2) ^ ((a + b) * n + a) := by
    intro n
    rw [← zpow_neg, ← pow_mul y 2, ← pow_mul y (a + b),
      ← zpow_natCast y ((a + b) * (2 * n + 1)), ← zpow_natCast y (2 * ((a + b) * n + a)),
      ← zpow_add₀ hy0]
    congr 1; push_cast; ring
  have hfac : ∀ n : ℕ, (1 - (y ^ (a + b)) ^ (2 * (n + 1))) *
      (1 + (y ^ (a + b)) ^ (2 * n + 1) * (ε * y ^ ((b : ℤ) - a))) *
      (1 + (y ^ (a + b)) ^ (2 * n + 1) * (ε * y ^ ((b : ℤ) - a))⁻¹) =
      (1 - (y ^ 2) ^ ((a + b) * n + a + b)) * (1 + ε * (y ^ 2) ^ ((a + b) * n + b)) *
        (1 + ε * (y ^ 2) ^ ((a + b) * n + a)) := by
    intro n
    have q0 : (y ^ (a + b)) ^ (2 * (n + 1)) = (y ^ 2) ^ ((a + b) * n + a + b) := by
      rw [← pow_mul, ← pow_mul]; congr 1; ring
    have q1 : (y ^ (a + b)) ^ (2 * n + 1) * (ε * y ^ ((b : ℤ) - a)) =
        ε * (y ^ 2) ^ ((a + b) * n + b) := by rw [mul_left_comm, p1]
    have q2 : (y ^ (a + b)) ^ (2 * n + 1) * (ε * y ^ ((b : ℤ) - a))⁻¹ =
        ε * (y ^ 2) ^ ((a + b) * n + a) := by
      rw [mul_inv, inv_eq_of_mul_eq_one_right hε, mul_left_comm, p2]
    rw [q0, q1, q2]
  refine ⟨hs.congr hterm, ?_⟩
  rw [funext hfac, tsum_congr hterm] at hp
  exact hp

/-- The core statement for `x` with `‖x‖ < 1` (including `x = 0`), a sign `ε = ±1`. -/
theorem jacobi_special_core {x : ℂ} (hx : ‖x‖ < 1) {ε : ℂ} (hε : ε * ε = 1) {a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Summable (fun n : ℤ ↦ ε ^ n * x ^ jacobiExp a b n) ∧
    HasProd (fun n : ℕ ↦ (1 - x ^ ((a + b) * n + a + b)) * (1 + ε * x ^ ((a + b) * n + b)) *
        (1 + ε * x ^ ((a + b) * n + a)))
      (∑' n : ℤ, ε ^ n * x ^ jacobiExp a b n) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · have hz : ∀ n : ℤ, n ≠ 0 → ε ^ n * (0 : ℂ) ^ jacobiExp a b n = 0 := fun n hn ↦ by
      rw [zero_zpow _ (jacobiExp_pos ha hb hn).ne', mul_zero]
    have hsum : ∑' n : ℤ, ε ^ n * (0 : ℂ) ^ jacobiExp a b n = 1 := by
      rw [tsum_eq_single 0 hz]; simp [jacobiExp_zero]
    refine ⟨summable_of_ne_finset_zero (s := {0}) fun n hn ↦ hz n (by simpa using hn), ?_⟩
    have hf : (fun n : ℕ ↦ (1 - (0 : ℂ) ^ ((a + b) * n + a + b)) *
        (1 + ε * (0 : ℂ) ^ ((a + b) * n + b)) * (1 + ε * (0 : ℂ) ^ ((a + b) * n + a))) =
        fun _ ↦ 1 := by
      funext n
      rw [zero_pow (by omega), zero_pow (by omega), zero_pow (by omega)]
      simp
    rw [hf, hsum]
    exact hasProd_one
  · obtain ⟨y, rfl⟩ : ∃ y : ℂ, y ^ 2 = x := ⟨x ^ (2⁻¹ : ℂ), cpow_ofNat_inv_pow x 2⟩
    have hy : ‖y‖ < 1 := by
      have h : ‖y‖ ^ 2 = ‖y ^ 2‖ := (norm_pow _ _).symm
      nlinarith [norm_nonneg y]
    exact jacobi_special_aux hy (fun h ↦ hx0 (by rw [h]; norm_num)) hε ha hb

end Core

/-- **(19.9.1).** For `‖x‖ < 1` and natural numbers `a, b ≥ 1` (Hardy–Wright's `k = (a+b)/2`,
`l = (b-a)/2`):
`∏_{n ≥ 0} (1 - x^{(a+b)n+a})(1 - x^{(a+b)n+b})(1 - x^{(a+b)n+a+b}) =
∑_{n ∈ ℤ} (-1)^n x^{((a+b)n² + (b-a)n)/2}`. -/
@[kb "hardywright2008" "(19.9.1), p. 394"]
theorem jacobi_special_sub {x : ℂ} (hx : ‖x‖ < 1) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Summable (fun n : ℤ ↦ (-1 : ℂ) ^ n * x ^ jacobiExp a b n) ∧
    HasProd (fun n : ℕ ↦ (1 - x ^ ((a + b) * n + a)) * (1 - x ^ ((a + b) * n + b)) *
        (1 - x ^ ((a + b) * n + a + b)))
      (∑' n : ℤ, (-1 : ℂ) ^ n * x ^ jacobiExp a b n) := by
  obtain ⟨h1, h2⟩ := jacobi_special_core hx (ε := -1) (by norm_num) ha hb
  refine ⟨h1, ?_⟩
  convert h2 using 1
  funext n
  ring

/-- **(19.9.2).** For `‖x‖ < 1` and natural numbers `a, b ≥ 1`:
`∏_{n ≥ 0} (1 + x^{(a+b)n+a})(1 + x^{(a+b)n+b})(1 - x^{(a+b)n+a+b}) =
∑_{n ∈ ℤ} x^{((a+b)n² + (b-a)n)/2}`. -/
@[kb "hardywright2008" "(19.9.2), p. 394"]
theorem jacobi_special_add {x : ℂ} (hx : ‖x‖ < 1) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Summable (fun n : ℤ ↦ x ^ jacobiExp a b n) ∧
    HasProd (fun n : ℕ ↦ (1 + x ^ ((a + b) * n + a)) * (1 + x ^ ((a + b) * n + b)) *
        (1 - x ^ ((a + b) * n + a + b)))
      (∑' n : ℤ, x ^ jacobiExp a b n) := by
  obtain ⟨h1, h2⟩ := jacobi_special_core hx (ε := 1) (by norm_num) ha hb
  simp only [one_zpow, one_mul] at h1 h2
  refine ⟨h1, ?_⟩
  convert h2 using 1
  funext n
  ring

/-- **Theorem 355.** For `‖x‖ < 1`,
`∏_{n ≥ 0} (1 - x^{5n+1})(1 - x^{5n+4})(1 - x^{5n+5}) = ∑_{n ∈ ℤ} (-1)^n x^{n(5n+3)/2}`
(the case `(a, b) = (1, 4)` of (19.9.1); `n(5n+3)` is even). -/
@[kb "hardywright2008" "Thm 355, p. 395"]
theorem hasProd_five_one_four {x : ℂ} (hx : ‖x‖ < 1) :
    Summable (fun n : ℤ ↦ (-1 : ℂ) ^ n * x ^ (n * (5 * n + 3) / 2)) ∧
    HasProd (fun n : ℕ ↦ (1 - x ^ (5 * n + 1)) * (1 - x ^ (5 * n + 4)) * (1 - x ^ (5 * n + 5)))
      (∑' n : ℤ, (-1 : ℂ) ^ n * x ^ (n * (5 * n + 3) / 2)) := by
  have e0 : ∀ n : ℤ, jacobiExp 1 4 n = n * (5 * n + 3) / 2 := fun n ↦ by
    rw [jacobiExp]; congr 1; push_cast; ring
  have h := jacobi_special_sub hx (a := 1) (b := 4) le_rfl (by norm_num)
  have e : (fun n : ℤ ↦ (-1 : ℂ) ^ n * x ^ jacobiExp 1 4 n) =
      fun n : ℤ ↦ (-1 : ℂ) ^ n * x ^ (n * (5 * n + 3) / 2) := by
    funext n; rw [e0 n]
  rw [e] at h
  refine ⟨h.1, ?_⟩
  convert h.2 using 1

/-- **Theorem 356.** For `‖x‖ < 1`,
`∏_{n ≥ 0} (1 - x^{5n+2})(1 - x^{5n+3})(1 - x^{5n+5}) = ∑_{n ∈ ℤ} (-1)^n x^{n(5n+1)/2}`
(the case `(a, b) = (2, 3)` of (19.9.1); `n(5n+1)` is even). -/
@[kb "hardywright2008" "Thm 356, p. 395"]
theorem hasProd_five_two_three {x : ℂ} (hx : ‖x‖ < 1) :
    Summable (fun n : ℤ ↦ (-1 : ℂ) ^ n * x ^ (n * (5 * n + 1) / 2)) ∧
    HasProd (fun n : ℕ ↦ (1 - x ^ (5 * n + 2)) * (1 - x ^ (5 * n + 3)) * (1 - x ^ (5 * n + 5)))
      (∑' n : ℤ, (-1 : ℂ) ^ n * x ^ (n * (5 * n + 1) / 2)) := by
  have e0 : ∀ n : ℤ, jacobiExp 2 3 n = n * (5 * n + 1) / 2 := fun n ↦ by
    rw [jacobiExp]; congr 1; push_cast; ring
  have h := jacobi_special_sub hx (a := 2) (b := 3) (by norm_num) (by norm_num)
  have e : (fun n : ℤ ↦ (-1 : ℂ) ^ n * x ^ jacobiExp 2 3 n) =
      fun n : ℤ ↦ (-1 : ℂ) ^ n * x ^ (n * (5 * n + 1) / 2) := by
    funext n; rw [e0 n]
  rw [e] at h
  refine ⟨h.1, ?_⟩
  convert h.2 using 1

/-- Euler's identity in the form (19.9.3) before regrouping (the case `(a, b) = (1, 2)` of (19.9.1)):
`∏_{n ≥ 0} (1 - x^{3n+1})(1 - x^{3n+2})(1 - x^{3n+3}) = ∑_{n ∈ ℤ} (-1)^n x^{n(3n+1)/2}`. -/
theorem jacobi_special_one_two {x : ℂ} (hx : ‖x‖ < 1) :
    HasProd (fun n : ℕ ↦ (1 - x ^ (3 * n + 1)) * (1 - x ^ (3 * n + 2)) * (1 - x ^ (3 * n + 3)))
      (∑' n : ℤ, (-1 : ℂ) ^ n * x ^ (n * (3 * n + 1) / 2)) := by
  have e0 : ∀ n : ℤ, jacobiExp 1 2 n = n * (3 * n + 1) / 2 := fun n ↦ by
    rw [jacobiExp]; congr 1; push_cast; ring
  have h := (jacobi_special_sub hx (a := 1) (b := 2) le_rfl (by norm_num)).2
  have e : (fun n : ℤ ↦ (-1 : ℂ) ^ n * x ^ jacobiExp 1 2 n) =
      fun n : ℤ ↦ (-1 : ℂ) ^ n * x ^ (n * (3 * n + 1) / 2) := by
    funext n; rw [e0 n]
  rw [e] at h
  convert h using 1

/-! ### (19.4.7) and Theorem 354 -/

section Thm354

variable {x : ℂ}

theorem summable_norm_pow_lin (hx : ‖x‖ < 1) (p q : ℕ) (hp : 0 < p) :
    Summable fun n : ℕ ↦ ‖x ^ (p * n + q)‖ := by
  have hr : ‖x‖ ^ p < 1 := pow_lt_one₀ (norm_nonneg _) hx hp.ne'
  refine ((summable_geometric_of_lt_one (by positivity) hr).mul_left (‖x‖ ^ q)).congr fun n ↦ ?_
  rw [norm_pow, pow_add, pow_mul]
  ring

theorem hasProd_one_sub_pow_lin (hx : ‖x‖ < 1) (p q : ℕ) (hp : 0 < p) :
    HasProd (fun n : ℕ ↦ 1 - x ^ (p * n + q)) (∏' n : ℕ, (1 - x ^ (p * n + q))) :=
  (multipliable_one_sub_of_summable (f := fun n : ℕ ↦ x ^ (p * n + q))
    (summable_norm_pow_lin hx p q hp)).hasProd

theorem tprod_one_sub_pow_lin_ne_zero (hx : ‖x‖ < 1) (p q : ℕ) (hp : 0 < p) (hq : 1 ≤ q) :
    ∏' n : ℕ, (1 - x ^ (p * n + q)) ≠ 0 := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have h := tprod_one_add_ne_zero_of_summable (f := fun n : ℕ ↦ -x ^ (p * n + (q' + 1)))
    (fun n ↦ by rw [← sub_eq_add_neg]; exact one_sub_pow_ne_zero hx (p * n + q'))
    (by simpa using summable_norm_pow_lin hx p (q' + 1) hp)
  simpa [← sub_eq_add_neg] using h

theorem prod_range_two_mul (f : ℕ → ℂ) (N : ℕ) :
    ∏ k ∈ range (2 * N), f k = ∏ k ∈ range N, (f (2 * k) * f (2 * k + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, prod_range_succ, prod_range_succ, ih,
      prod_range_succ]
    ring

/-- `∏_{n ≥ 1} (1 - xⁿ) = ∏_{n ≥ 1} (1 - x^{2n-1}) · ∏_{n ≥ 1} (1 - x^{2n})`. -/
theorem qPochInf_eq_mul (hx : ‖x‖ < 1) :
    qPochInf x = (∏' n : ℕ, (1 - x ^ (2 * n + 1))) * ∏' n : ℕ, (1 - x ^ (2 * n + 2)) := by
  have hprod := (hasProd_one_sub_pow_lin hx 2 1 two_pos).mul (hasProd_one_sub_pow_lin hx 2 2 two_pos)
  have t1 := hprod.tendsto_prod_nat
  have t2 : Tendsto (fun N : ℕ ↦ qPoch x (2 * N)) atTop (𝓝 (qPochInf x)) :=
    (tendsto_qPoch hx).comp (tendsto_atTop_atTop.2 fun b ↦ ⟨b, fun n hn ↦ by omega⟩)
  have e : (fun N : ℕ ↦ qPoch x (2 * N)) =
      fun N ↦ ∏ k ∈ range N, ((1 - x ^ (2 * k + 1)) * (1 - x ^ (2 * k + 2))) := by
    funext N
    rw [qPoch, prod_range_two_mul]
  rw [e] at t2
  exact tendsto_nhds_unique t2 t1

theorem hasProd_one_add_pow_succ (hx : ‖x‖ < 1) :
    HasProd (fun n : ℕ ↦ 1 + x ^ (n + 1))
      ((∏' n : ℕ, (1 - x ^ (2 * n + 2))) / qPochInf x) := by
  have hQ : HasProd (fun n : ℕ ↦ 1 - x ^ (n + 1)) (qPochInf x) :=
    (multipliable_one_sub_pow_succ hx).hasProd
  have h := (hasProd_one_sub_pow_lin hx 2 2 two_pos).div₀ hQ (qPochInf_ne_zero hx)
  convert h using 1
  funext n
  rw [eq_div_iff (one_sub_pow_ne_zero hx n)]
  ring

/-- **(19.4.7).** For `‖x‖ < 1`, `(1 + x)(1 + x²)(1 + x³)… = 1 / ((1 - x)(1 - x³)(1 - x⁵)…)`,
i.e. `∏_{n ≥ 1} (1 + xⁿ) · ∏_{n ≥ 1} (1 - x^{2n-1}) = 1`. -/
@[kb "hardywright2008" "(19.4.7), p. 385"]
theorem tprod_one_add_pow_mul_tprod_one_sub_odd (hx : ‖x‖ < 1) :
    (∏' n : ℕ, (1 + x ^ (n + 1))) * ∏' n : ℕ, (1 - x ^ (2 * n + 1)) = 1 := by
  rw [(hasProd_one_add_pow_succ hx).tprod_eq]
  have hO := tprod_one_sub_pow_lin_ne_zero hx 2 1 two_pos le_rfl
  have hE := tprod_one_sub_pow_lin_ne_zero hx 2 2 two_pos (by norm_num)
  rw [qPochInf_eq_mul hx]
  field_simp

/-- The key identity for Theorem 354: with `x = y²`,
`∏_{n ≥ 1} (1 - x^{2n}) · ∏_{n ≥ 1} (1 + xⁿ) = ∑_{n ≥ 0} x^{n(n+1)/2}`. -/
theorem tprod_mul_tprod_eq_tsum_triangular {x y : ℂ} (hxy : y ^ 2 = x) (hy : ‖y‖ < 1)
    (hy0 : y ≠ 0) :
    (∏' n : ℕ, (1 - x ^ (2 * n + 2))) * ∏' n : ℕ, (1 + x ^ (n + 1)) =
      ∑' n : ℕ, x ^ (n * (n + 1) / 2) := by
  have hx : ‖x‖ < 1 := by
    rw [← hxy, norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hy two_ne_zero
  obtain ⟨hs, hp⟩ := jacobi_triple_product hy (w := y) hy0
  have hfac : ∀ n : ℕ, (1 - y ^ (2 * (n + 1))) * (1 + y ^ (2 * n + 1) * y) *
      (1 + y ^ (2 * n + 1) * y⁻¹) = (1 - x ^ (2 * n + 2)) * (1 + x ^ n) := by
    intro n
    have hinv : y ^ (2 * n + 1) * y⁻¹ = x ^ n := by
      rw [pow_succ, mul_assoc, mul_inv_cancel₀ hy0, mul_one, ← hxy, ← pow_mul]
    rw [hinv, ← hxy]
    ring
  rw [funext hfac] at hp
  -- the series
  set f : ℤ → ℂ := fun m ↦ y ^ (m ^ 2) * y ^ m with hf
  have hterm : ∀ n : ℕ, f n + f (-((n : ℤ) + 1)) = 2 * x ^ (n * (n + 1) / 2) := by
    intro n
    have hev : 2 * (n * (n + 1) / 2) = n * (n + 1) :=
      Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self n)
    have hx' : x ^ (n * (n + 1) / 2) = y ^ ((n * (n + 1) : ℕ) : ℤ) := by
      rw [← hxy, ← pow_mul, hev, zpow_natCast]
    have h1 : f n = y ^ ((n * (n + 1) : ℕ) : ℤ) := by
      simp only [hf]
      rw [← zpow_add₀ hy0]
      congr 1; push_cast; ring
    have h2 : f (-((n : ℤ) + 1)) = y ^ ((n * (n + 1) : ℕ) : ℤ) := by
      simp only [hf]
      rw [← zpow_add₀ hy0]
      congr 1; push_cast; ring
    rw [h1, h2, hx']
    ring
  have hsum : ∑' m : ℤ, f m = 2 * ∑' n : ℕ, x ^ (n * (n + 1) / 2) := by
    rw [← tsum_nat_add_neg_add_one hs, ← tsum_mul_left]
    exact tsum_congr hterm
  -- the product `∏ (1 + xⁿ) = 2 ∏ (1 + x^{n+1})`
  have hMs : HasProd (fun n : ℕ ↦ 1 + x ^ (n + 1)) (∏' n : ℕ, (1 + x ^ (n + 1))) :=
    (multipliable_one_add_of_summable (f := fun n : ℕ ↦ x ^ (n + 1))
      (by simpa using summable_norm_pow_lin hx 1 1 one_pos)).hasProd
  have hD : HasProd (fun n : ℕ ↦ 1 + x ^ n) (∏' n : ℕ, (1 + x ^ n)) :=
    (multipliable_one_add_of_summable (f := fun n : ℕ ↦ x ^ n)
      (by simpa using summable_norm_pow_lin hx 1 0 one_pos)).hasProd
  have hDM : ∏' n : ℕ, (1 + x ^ n) = 2 * ∏' n : ℕ, (1 + x ^ (n + 1)) := by
    have t1 := hD.tendsto_prod_nat.comp (tendsto_add_atTop_nat 1)
    have t2 := hMs.tendsto_prod_nat.const_mul 2
    have e : (fun N : ℕ ↦ ∏ n ∈ range (N + 1), (1 + x ^ n)) =
        fun N ↦ 2 * ∏ n ∈ range N, (1 + x ^ (n + 1)) := by
      funext N
      rw [prod_range_succ']
      simp only [pow_zero]
      norm_num
      ring
    exact tendsto_nhds_unique (e ▸ t1) t2
  have hprod := (hasProd_one_sub_pow_lin hx 2 2 two_pos).mul hD
  have heq := hprod.unique hp
  rw [hsum, hDM] at heq
  have h2 : (2 : ℂ) * ((∏' n : ℕ, (1 - x ^ (2 * n + 2))) * ∏' n : ℕ, (1 + x ^ (n + 1))) =
      2 * ∑' n : ℕ, x ^ (n * (n + 1) / 2) := by
    linear_combination heq
  exact mul_left_cancel₀ two_ne_zero h2

/-- **Theorem 354.** For `‖x‖ < 1`,
`(1 - x²)(1 - x⁴)(1 - x⁶)… / ((1 - x)(1 - x³)(1 - x⁵)…) = 1 + x + x³ + x⁶ + x¹⁰ + …`
(the exponents on the right are the triangular numbers `n(n+1)/2`). -/
@[kb "hardywright2008" "Thm 354, p. 395"]
theorem hasProd_eq_tsum_triangular (hx : ‖x‖ < 1) :
    HasProd (fun n : ℕ ↦ (1 - x ^ (2 * n + 2)) / (1 - x ^ (2 * n + 1)))
      (∑' n : ℕ, x ^ (n * (n + 1) / 2)) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · have hz : ∀ n : ℕ, n ≠ 0 → (0 : ℂ) ^ (n * (n + 1) / 2) = 0 := fun n hn ↦ by
      refine zero_pow (Nat.pos_iff_ne_zero.1 (Nat.div_pos ?_ two_pos))
      nlinarith [Nat.pos_of_ne_zero hn]
    have hsum : ∑' n : ℕ, (0 : ℂ) ^ (n * (n + 1) / 2) = 1 := by
      rw [tsum_eq_single 0 hz]; simp
    have hf : (fun n : ℕ ↦ (1 - (0 : ℂ) ^ (2 * n + 2)) / (1 - (0 : ℂ) ^ (2 * n + 1))) =
        fun _ ↦ 1 := by
      funext n
      rw [zero_pow (by omega), zero_pow (by omega)]
      simp
    rw [hf, hsum]
    exact hasProd_one
  · obtain ⟨y, hy2⟩ : ∃ y : ℂ, y ^ 2 = x := ⟨x ^ (2⁻¹ : ℂ), cpow_ofNat_inv_pow x 2⟩
    have hy : ‖y‖ < 1 := by
      have h : ‖y‖ ^ 2 = ‖x‖ := by rw [← norm_pow, hy2]
      nlinarith [norm_nonneg y]
    have hy0 : y ≠ 0 := fun h ↦ hx0 (by rw [← hy2, h]; norm_num)
    have hO := tprod_one_sub_pow_lin_ne_zero hx 2 1 two_pos le_rfl
    have hdiv := (hasProd_one_sub_pow_lin hx 2 2 two_pos).div₀
      (hasProd_one_sub_pow_lin hx 2 1 two_pos) hO
    have key := tprod_mul_tprod_eq_tsum_triangular hy2 hy hy0
    have hM := tprod_one_add_pow_mul_tprod_one_sub_odd hx
    have hM' : (∏' n : ℕ, (1 + x ^ (n + 1))) = 1 / ∏' n : ℕ, (1 - x ^ (2 * n + 1)) :=
      eq_one_div_of_mul_eq_one_left hM
    rw [← key, hM', mul_one_div]
    exact hdiv

end Thm354

end NTKB.HardyWright
