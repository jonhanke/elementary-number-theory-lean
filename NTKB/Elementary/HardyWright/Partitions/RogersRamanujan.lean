/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.Partitions.JacobiSpecial
import NTKB.Elementary.HardyWright.Partitions.EulerIdentities

/-!
# The Rogers–Ramanujan identities (Hardy–Wright, Chapter XIX, §§ 19.13–19.14)

For complex `x` with `‖x‖ < 1`:

* **Theorem 362**: `1 + ∑_{s ≥ 1} x^{s²}/((1 - x)⋯(1 - x^s)) = ∏_{m ≥ 0} 1/((1 - x^{5m+1})(1 - x^{5m+4}))`;
* **Theorem 363**: `1 + ∑_{s ≥ 1} x^{s(s+1)}/((1 - x)⋯(1 - x^s)) = ∏_{m ≥ 0} 1/((1 - x^{5m+2})(1 - x^{5m+3}))`.

We follow Rogers' proof as given in the book (§ 19.14). With `P_r = ∏_{s=1}^r (1 - x^s)⁻¹`,
`Q_r(a) = ∏_{s ≥ r} (1 - a x^s)⁻¹` and `λ(r) = r(5r+1)/2`, the auxiliary functions
`H_m(a) = ∑_r (-1)^r a^{2r} x^{λ(r) - mr} (1 - a^m x^{2mr}) P_r Q_r(a)` satisfy (19.14.2)–(19.14.3)
`H₁(a) = H₂(ax)` and `H₂(a) - H₁(a) = a H₁(ax)`, so (19.14.4) `H₂(a) = H₂(ax) + a H₂(ax²)`.

The book then "expands `H₂` in powers of `a`" and equates coefficients. Instead of developing
`H₂` as a power series in `a` we use the explicit solution `G(a) = ∑_s a^s x^{s(s-1)} P_s` of
(19.14.4) (the book's result of the coefficient comparison) and show `H₂ = G` on `‖a‖ < 1`:
`D = H₂ - G` satisfies (19.14.4) and `D(a) = O(a)` near `0`, which forces `D = 0` near `0`, and
then everywhere by (19.14.4) again. Finally `H₂(x)` and `H₁(x) = H₂(x²)` are evaluated by
Theorems 356 and 355, as in the book.
-/

open Complex Finset Filter
open scoped Topology

namespace NTKB.HardyWright

open NTKB.Apostol

variable {x : ℂ}

/-! ### Euler's expansion of `∏_{k ≥ 0} (1 - b x^k)⁻¹` -/

theorem summable_norm_mul_pow (hx : ‖x‖ < 1) (b : ℂ) : Summable fun k : ℕ ↦ ‖b * x ^ k‖ := by
  refine ((summable_geometric_of_lt_one (norm_nonneg _) hx).mul_left ‖b‖).congr fun k ↦ ?_
  simp [norm_mul, norm_pow]

theorem multipliable_one_sub_mul_pow' (hx : ‖x‖ < 1) (b : ℂ) :
    Multipliable fun k : ℕ ↦ (1 - b * x ^ k) :=
  multipliable_one_sub_of_summable (summable_norm_mul_pow hx b)

theorem one_sub_mul_pow_ne_zero (hx : ‖x‖ < 1) {b : ℂ} (hb : ‖b‖ < 1) (k : ℕ) :
    1 - b * x ^ k ≠ 0 := by
  intro h
  have h1 : b * x ^ k = 1 := by linear_combination -h
  have : ‖b * x ^ k‖ < 1 := by
    rw [norm_mul, norm_pow]
    calc ‖b‖ * ‖x‖ ^ k ≤ ‖b‖ * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hx.le) (norm_nonneg _)
      _ < 1 := by rwa [mul_one]
  rw [h1, norm_one] at this
  exact lt_irrefl _ this

theorem tprod_one_sub_mul_pow_ne_zero (hx : ‖x‖ < 1) {b : ℂ} (hb : ‖b‖ < 1) :
    ∏' k : ℕ, (1 - b * x ^ k) ≠ 0 := by
  have h := tprod_one_add_ne_zero_of_summable (f := fun k : ℕ ↦ -(b * x ^ k))
    (fun k ↦ by rw [← sub_eq_add_neg]; exact one_sub_mul_pow_ne_zero hx hb k)
    (by simpa using summable_norm_mul_pow hx b)
  simpa [← sub_eq_add_neg] using h

/-- Euler: `∑_{m ≥ 0} b^m / ((1 - x)⋯(1 - x^m)) = ∏_{k ≥ 0} (1 - b x^k)⁻¹` for `‖b‖ < 1`. -/
theorem hasSum_mul_inv_qPoch (hx : ‖x‖ < 1) {b : ℂ} (hb : ‖b‖ < 1) :
    HasSum (fun m : ℕ ↦ b ^ m * (qPoch x m)⁻¹) (∏' k : ℕ, (1 - b * x ^ k))⁻¹ := by
  rcases eq_or_ne x 0 with rfl | hx0
  · have hq : ∀ m, qPoch 0 m = 1 := fun m ↦ by simp [qPoch]
    have hp : ∏' k : ℕ, (1 - b * (0 : ℂ) ^ k) = 1 - b := by
      rw [tprod_eq_mulSingle 0 fun k hk ↦ by simp [hk]]; simp
    simp only [hq, inv_one, mul_one, hp]
    rw [← one_div]
    have := hasSum_geometric_of_norm_lt_one hb
    rwa [← one_div] at this
  · have h := hasSum_inv_tprod_one_sub_mul_pow (a := b / x) hx (by rwa [div_mul_cancel₀ _ hx0])
    rw [div_mul_cancel₀ _ hx0] at h
    have e : ∏' k : ℕ, (1 - b / x * x ^ (k + 1)) = ∏' k : ℕ, (1 - b * x ^ k) := by
      congr 1; ext k; rw [pow_succ]; field_simp
    rw [e, one_div] at h
    simpa [div_eq_mul_inv] using h

/-! ### The functions `P_r`, `Q_r(a)`, `H_m(a)`, `G(a)` -/

/-- `Q_r(a) = ∏_{s ≥ r} (1 - a x^s)⁻¹`. -/
noncomputable def rrQ (x a : ℂ) (r : ℕ) : ℂ := (∏' k : ℕ, (1 - a * x ^ (k + r)))⁻¹

/-- `λ(r) = r(5r+1)/2`. -/
def rrLam (r : ℕ) : ℕ := r * (5 * r + 1) / 2

/-- The terms of Rogers' function `H_m(a)` (Hardy–Wright (19.14.1)). -/
noncomputable def rrTerm (x : ℂ) (m : ℕ) (a : ℂ) (r : ℕ) : ℂ :=
  (-1) ^ r * a ^ (2 * r) * x ^ (rrLam r - m * r) * (1 - a ^ m * x ^ (2 * m * r)) *
    (qPoch x r)⁻¹ * rrQ x a r

/-- Rogers' function `H_m(a) = ∑_r (-1)^r a^{2r} x^{λ(r) - mr} (1 - a^m x^{2mr}) P_r Q_r(a)`. -/
noncomputable def rrH (x : ℂ) (m : ℕ) (a : ℂ) : ℂ := ∑' r : ℕ, rrTerm x m a r

/-- The solution `G(a) = ∑_s a^s x^{s(s-1)} P_s` of `G(a) = G(ax) + a G(ax²)`. -/
noncomputable def rrG (x a : ℂ) : ℂ := ∑' s : ℕ, a ^ s * x ^ (s * (s - 1)) * (qPoch x s)⁻¹

theorem rrQ_eq (x a : ℂ) (r : ℕ) :
    rrQ x a r = (∏' k : ℕ, (1 - (a * x ^ r) * x ^ k))⁻¹ := by
  unfold rrQ; congr 2; ext k; rw [pow_add]; ring

theorem norm_mul_pow_le (hx : ‖x‖ < 1) (a : ℂ) (r : ℕ) : ‖a * x ^ r‖ ≤ ‖a‖ := by
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hx.le)

theorem hasSum_rrQ (hx : ‖x‖ < 1) {a : ℂ} (ha : ‖a‖ < 1) (r : ℕ) :
    HasSum (fun m : ℕ ↦ (a * x ^ r) ^ m * (qPoch x m)⁻¹) (rrQ x a r) := by
  rw [rrQ_eq]
  exact hasSum_mul_inv_qPoch hx ((norm_mul_pow_le hx a r).trans_lt ha)

/-- `Q_r(ax) = Q_{r+1}(a)`. -/
theorem rrQ_mul_x (x a : ℂ) (r : ℕ) : rrQ x (a * x) r = rrQ x a (r + 1) := by
  unfold rrQ; congr 2; ext k; ring

/-- `(1 - a x^r) Q_r(a) = Q_{r+1}(a)`. -/
theorem rrQ_succ (hx : ‖x‖ < 1) {a : ℂ} (ha : ‖a‖ < 1) (r : ℕ) :
    (1 - a * x ^ r) * rrQ x a r = rrQ x a (r + 1) := by
  have hm : Multipliable fun k : ℕ ↦ (1 - (a * x ^ r) * x ^ (k + 1)) :=
    multipliable_one_sub_of_summable (f := fun k : ℕ ↦ (a * x ^ r) * x ^ (k + 1))
      ((summable_nat_add_iff (f := fun k : ℕ ↦ ‖a * x ^ r * x ^ k‖) 1).2
        (summable_norm_mul_pow hx (a * x ^ r)))
  have hsplit := tprod_eq_zero_mul' (f := fun k : ℕ ↦ 1 - (a * x ^ r) * x ^ k) hm
  have hne : 1 - a * x ^ r ≠ 0 := by
    have := one_sub_mul_pow_ne_zero hx ((norm_mul_pow_le hx a r).trans_lt ha) 0
    simpa using this
  rw [rrQ_eq, rrQ_eq, hsplit]
  have e : ∏' k : ℕ, (1 - a * x ^ r * x ^ (k + 1)) = ∏' k : ℕ, (1 - a * x ^ (r + 1) * x ^ k) := by
    congr 1; ext k; ring
  rw [e]
  simp only [pow_zero, mul_one]
  rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]

/-- `(1 - x^{r+1}) P_{r+1} = P_r`. -/
theorem qPoch_inv_succ (hx : ‖x‖ < 1) (r : ℕ) :
    (1 - x ^ (r + 1)) * (qPoch x (r + 1))⁻¹ = (qPoch x r)⁻¹ := by
  rw [qPoch_succ, mul_inv, mul_comm, mul_assoc, inv_mul_cancel₀ (one_sub_pow_ne_zero hx r),
    mul_one]

theorem rrLam_succ (r : ℕ) : rrLam (r + 1) = rrLam r + 5 * r + 3 := by
  unfold rrLam
  have h1 : (r + 1) * (5 * (r + 1) + 1) = r * (5 * r + 1) + 2 * (5 * r + 3) := by ring
  rw [h1, Nat.add_mul_div_left _ _ two_pos]
  ring

theorem three_mul_le_rrLam (r : ℕ) : 3 * r ≤ rrLam r := by
  unfold rrLam
  rw [Nat.le_div_iff_mul_le two_pos]
  rcases r with _ | r
  · simp
  · nlinarith

/-- `2 λ(r) = r(5r+1)`. -/
theorem two_mul_rrLam (r : ℕ) : 2 * rrLam r = r * (5 * r + 1) := by
  unfold rrLam
  refine Nat.mul_div_cancel' ?_
  rcases Nat.even_or_odd r with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · exact ⟨k * (5 * (k + k) + 1), by ring⟩
  · exact ⟨(2 * k + 1) * (5 * k + 3), by ring⟩

/-! ### Uniform bounds -/

theorem exists_norm_qPoch_inv_le (hx : ‖x‖ < 1) : ∃ C > 0, ∀ n, ‖(qPoch x n)⁻¹‖ ≤ C := by
  obtain ⟨δ, hδ, hle⟩ := exists_le_norm_qPoch hx
  refine ⟨δ⁻¹, inv_pos.2 hδ, fun n ↦ ?_⟩
  rw [norm_inv]
  exact inv_anti₀ hδ (hle n)

/-- `‖Q_r(a)‖ ≤ C/(1 - ‖a‖)`. -/
theorem norm_rrQ_le (hx : ‖x‖ < 1) {C : ℝ} (hC : ∀ n, ‖(qPoch x n)⁻¹‖ ≤ C) {a : ℂ}
    (ha : ‖a‖ < 1) (r : ℕ) : ‖rrQ x a r‖ ≤ C / (1 - ‖a‖) := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hg : HasSum (fun m : ℕ ↦ C * ‖a‖ ^ m) (C * (1 - ‖a‖)⁻¹) :=
    (hasSum_geometric_of_lt_one (norm_nonneg _) ha).mul_left C
  refine ((hasSum_rrQ hx ha r).norm_le_of_bounded hg fun m ↦ ?_).trans_eq (by rw [div_eq_mul_inv])
  rw [norm_mul, norm_pow]
  calc ‖a * x ^ r‖ ^ m * ‖(qPoch x m)⁻¹‖ ≤ ‖a‖ ^ m * C :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (norm_mul_pow_le hx a r) m) (hC m)
          (norm_nonneg _) (by positivity)
    _ = C * ‖a‖ ^ m := by ring

/-- `‖Q₀(a) - 1‖ ≤ C ‖a‖/(1 - ‖a‖)`. -/
theorem norm_rrQ_zero_sub_one_le (hx : ‖x‖ < 1) {C : ℝ} (hC : ∀ n, ‖(qPoch x n)⁻¹‖ ≤ C)
    {a : ℂ} (ha : ‖a‖ < 1) : ‖rrQ x a 0 - 1‖ ≤ C * ‖a‖ / (1 - ‖a‖) := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have h := hasSum_rrQ hx ha 0
  simp only [pow_zero, mul_one] at h
  have h1 := (hasSum_nat_add_iff' 1).2 h
  simp only [range_one, sum_singleton, pow_zero, qPoch_zero, inv_one, mul_one] at h1
  have hg : HasSum (fun m : ℕ ↦ C * ‖a‖ * ‖a‖ ^ m) (C * ‖a‖ * (1 - ‖a‖)⁻¹) :=
    (hasSum_geometric_of_lt_one (norm_nonneg _) ha).mul_left (C * ‖a‖)
  refine (h1.norm_le_of_bounded hg fun m ↦ ?_).trans_eq (by rw [div_eq_mul_inv])
  rw [norm_mul, norm_pow, pow_succ]
  calc ‖a‖ ^ m * ‖a‖ * ‖(qPoch x (m + 1))⁻¹‖ ≤ ‖a‖ ^ m * ‖a‖ * C :=
        mul_le_mul_of_nonneg_left (hC _) (by positivity)
    _ = C * ‖a‖ * ‖a‖ ^ m := by ring

theorem norm_pow_rrLam_sub_le (hx : ‖x‖ < 1) {m : ℕ} (hm : m ≤ 2) (r : ℕ) :
    ‖x ^ (rrLam r - m * r)‖ ≤ ‖x‖ ^ r := by
  rw [norm_pow]
  refine pow_le_pow_of_le_one (norm_nonneg _) hx.le ?_
  have := three_mul_le_rrLam r
  have : m * r ≤ 2 * r := Nat.mul_le_mul_right r hm
  omega

theorem norm_rrTerm_le (hx : ‖x‖ < 1) {C : ℝ} (hC : ∀ n, ‖(qPoch x n)⁻¹‖ ≤ C) {m : ℕ}
    (hm : m ≤ 2) {a : ℂ} (ha : ‖a‖ < 1) (r : ℕ) :
    ‖rrTerm x m a r‖ ≤ ‖a‖ ^ (2 * r) * (2 * C * (C / (1 - ‖a‖))) * ‖x‖ ^ r := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have h1 : ‖1 - a ^ m * x ^ (2 * m * r)‖ ≤ 2 := by
    calc ‖1 - a ^ m * x ^ (2 * m * r)‖ ≤ ‖(1 : ℂ)‖ + ‖a ^ m * x ^ (2 * m * r)‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by
          rw [norm_one, norm_mul, norm_pow, norm_pow]
          gcongr
          exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) ha.le) (by positivity)
            (pow_le_one₀ (norm_nonneg _) hx.le)
      _ = 2 := by norm_num
  unfold rrTerm
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have hq := norm_rrQ_le hx hC ha r
  have hx' := norm_pow_rrLam_sub_le hx hm r
  rw [norm_pow] at hx'
  have hQ0 : 0 ≤ C / (1 - ‖a‖) := div_nonneg hC0 (by linarith)
  have hP := hC r
  calc ‖a‖ ^ (2 * r) * ‖x‖ ^ (rrLam r - m * r) * ‖1 - a ^ m * x ^ (2 * m * r)‖ *
        ‖(qPoch x r)⁻¹‖ * ‖rrQ x a r‖
      ≤ ‖a‖ ^ (2 * r) * ‖x‖ ^ r * 2 * C * (C / (1 - ‖a‖)) := by gcongr
    _ = ‖a‖ ^ (2 * r) * (2 * C * (C / (1 - ‖a‖))) * ‖x‖ ^ r := by ring

theorem summable_of_norm_le_geom (hx : ‖x‖ < 1) {f : ℕ → ℂ} {K : ℝ}
    (h : ∀ r, ‖f r‖ ≤ K * ‖x‖ ^ r) : Summable f :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one (norm_nonneg _) hx).mul_left K) h

theorem summable_rrTerm (hx : ‖x‖ < 1) {m : ℕ} (hm : m ≤ 2) {a : ℂ} (ha : ‖a‖ < 1) :
    Summable (rrTerm x m a) := by
  obtain ⟨C, -, hC⟩ := exists_norm_qPoch_inv_le hx
  refine summable_of_norm_le_geom hx (K := 2 * C * (C / (1 - ‖a‖))) fun r ↦ ?_
  refine (norm_rrTerm_le hx hC hm ha r).trans ?_
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have : 0 ≤ 2 * C * (C / (1 - ‖a‖)) := by
    have : 0 < 1 - ‖a‖ := by linarith
    positivity
  have h1 : ‖a‖ ^ (2 * r) ≤ 1 := pow_le_one₀ (norm_nonneg _) ha.le
  have h2 : 0 ≤ ‖x‖ ^ r := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h1 (mul_nonneg this h2)]

/-! ### The functional equations (19.14.2)–(19.14.4) -/

/-- (19.14.3), first part: `H₁(a) = H₂(ax)`. -/
theorem rrH_one (hx : ‖x‖ < 1) {a : ℂ} (ha : ‖a‖ < 1) : rrH x 1 a = rrH x 2 (a * x) := by
  obtain ⟨C, -, hC⟩ := exists_norm_qPoch_inv_le hx
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hQ := norm_rrQ_le hx hC ha
  have hQ1 : ∀ r, ‖rrQ x a (r + 1)‖ ≤ C / (1 - ‖a‖) := fun r ↦ hQ (r + 1)
  have hK : 0 ≤ C * (C / (1 - ‖a‖)) := by
    have : 0 < 1 - ‖a‖ := by linarith
    positivity
  set A : ℕ → ℂ := fun r ↦ (-1) ^ r * a ^ (2 * r) * x ^ rrLam r * (qPoch x r)⁻¹ * rrQ x a (r + 1)
  set B : ℕ → ℂ := fun r ↦
    (-1) ^ r * a ^ (2 * r) * x ^ (rrLam r - r) * (1 - x ^ r) * (qPoch x r)⁻¹ * rrQ x a r
  have hA : Summable A := by
    refine summable_of_norm_le_geom hx (K := C * (C / (1 - ‖a‖))) fun r ↦ ?_
    simp only [A, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    have h1 : ‖a‖ ^ (2 * r) ≤ 1 := pow_le_one₀ (norm_nonneg _) ha.le
    have h2 : ‖x‖ ^ rrLam r ≤ ‖x‖ ^ r := pow_le_pow_of_le_one (norm_nonneg _) hx.le
      (by have := three_mul_le_rrLam r; omega)
    have hP := hC r
    have hQr := hQ1 r
    calc ‖a‖ ^ (2 * r) * ‖x‖ ^ rrLam r * ‖(qPoch x r)⁻¹‖ * ‖rrQ x a (r + 1)‖
        ≤ 1 * ‖x‖ ^ r * C * (C / (1 - ‖a‖)) := by gcongr
      _ = C * (C / (1 - ‖a‖)) * ‖x‖ ^ r := by ring
  have hB : Summable B := by
    refine summable_of_norm_le_geom hx (K := 2 * C * (C / (1 - ‖a‖))) fun r ↦ ?_
    simp only [B, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    have h1 : ‖a‖ ^ (2 * r) ≤ 1 := pow_le_one₀ (norm_nonneg _) ha.le
    have h2 : ‖x‖ ^ (rrLam r - r) ≤ ‖x‖ ^ r := pow_le_pow_of_le_one (norm_nonneg _) hx.le
      (by have := three_mul_le_rrLam r; omega)
    have h3 : ‖1 - x ^ r‖ ≤ 2 := by
      calc ‖1 - x ^ r‖ ≤ ‖(1 : ℂ)‖ + ‖x ^ r‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := by
            rw [norm_one, norm_pow]; gcongr; exact pow_le_one₀ (norm_nonneg _) hx.le
        _ = 2 := by norm_num
    calc ‖a‖ ^ (2 * r) * ‖x‖ ^ (rrLam r - r) * ‖1 - x ^ r‖ * ‖(qPoch x r)⁻¹‖ * ‖rrQ x a r‖
        ≤ 1 * ‖x‖ ^ r * 2 * C * (C / (1 - ‖a‖)) := by have := hQ r; have := hC r; gcongr
      _ = 2 * C * (C / (1 - ‖a‖)) * ‖x‖ ^ r := by ring
  -- `T₁(r) = A(r) + B(r)` and `T₂(ax)(s) = A(s) + B(s+1)`
  have hT : ∀ r, rrTerm x 1 a r = A r + B r := by
    intro r
    obtain ⟨e, he⟩ : ∃ e, rrLam r = e + 2 * r := ⟨rrLam r - 2 * r, by
      have := three_mul_le_rrLam r; omega⟩
    have hQs := rrQ_succ hx ha r
    simp only [rrTerm, A, B, he, ← hQs, show e + 2 * r - 1 * r = e + r by omega,
      show e + 2 * r - r = e + r by omega]
    ring
  have hU : ∀ s, rrTerm x 2 (a * x) s = A s + B (s + 1) := by
    intro s
    obtain ⟨e, he⟩ : ∃ e, rrLam s = e + 2 * s := ⟨rrLam s - 2 * s, by
      have := three_mul_le_rrLam s; omega⟩
    have hP := qPoch_inv_succ hx s
    have hl1 : rrLam (s + 1) - (s + 1) = e + 6 * s + 2 := by rw [rrLam_succ, he]; omega
    simp only [rrTerm, A, B, rrQ_mul_x, he, hl1, show e + 2 * s - 2 * s = e by omega]
    rw [← hP]
    ring
  have hB0 : B 0 = 0 := by simp [B]
  unfold rrH
  rw [tsum_congr hT, tsum_congr hU, hA.tsum_add hB, hA.tsum_add ((summable_nat_add_iff 1).2 hB),
    tsum_eq_zero_add' ((summable_nat_add_iff 1).2 hB), hB0, zero_add]

/-- (19.14.2) for `m = 2`: `H₂(a) - H₁(a) = a H₁(ax)`. -/
theorem rrH_two_sub (hx : ‖x‖ < 1) {a : ℂ} (ha : ‖a‖ < 1) :
    rrH x 2 a - rrH x 1 a = a * rrH x 1 (a * x) := by
  obtain ⟨C, -, hC⟩ := exists_norm_qPoch_inv_le hx
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hQ := norm_rrQ_le hx hC ha
  set A : ℕ → ℂ := fun r ↦
    (-1) ^ r * a ^ (2 * r + 1) * x ^ (rrLam r + r) * (qPoch x r)⁻¹ * rrQ x a (r + 1)
  set B : ℕ → ℂ := fun r ↦
    (-1) ^ r * a ^ (2 * r) * x ^ (rrLam r - 2 * r) * (1 - x ^ r) * (qPoch x r)⁻¹ * rrQ x a r
  have hA : Summable A := by
    refine summable_of_norm_le_geom hx (K := C * (C / (1 - ‖a‖))) fun r ↦ ?_
    simp only [A, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    have h1 : ‖a‖ ^ (2 * r + 1) ≤ 1 := pow_le_one₀ (norm_nonneg _) ha.le
    have h2 : ‖x‖ ^ (rrLam r + r) ≤ ‖x‖ ^ r := pow_le_pow_of_le_one (norm_nonneg _) hx.le
      (Nat.le_add_left r _)
    calc ‖a‖ ^ (2 * r + 1) * ‖x‖ ^ (rrLam r + r) * ‖(qPoch x r)⁻¹‖ * ‖rrQ x a (r + 1)‖
        ≤ 1 * ‖x‖ ^ r * C * (C / (1 - ‖a‖)) := by have := hQ (r + 1); have := hC r; gcongr
      _ = C * (C / (1 - ‖a‖)) * ‖x‖ ^ r := by ring
  have hB : Summable B := by
    refine summable_of_norm_le_geom hx (K := 2 * C * (C / (1 - ‖a‖))) fun r ↦ ?_
    simp only [B, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    have h1 : ‖a‖ ^ (2 * r) ≤ 1 := pow_le_one₀ (norm_nonneg _) ha.le
    have h2 : ‖x‖ ^ (rrLam r - 2 * r) ≤ ‖x‖ ^ r := pow_le_pow_of_le_one (norm_nonneg _) hx.le
      (by have := three_mul_le_rrLam r; omega)
    have h3 : ‖1 - x ^ r‖ ≤ 2 := by
      calc ‖1 - x ^ r‖ ≤ ‖(1 : ℂ)‖ + ‖x ^ r‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := by
            rw [norm_one, norm_pow]; gcongr; exact pow_le_one₀ (norm_nonneg _) hx.le
        _ = 2 := by norm_num
    calc ‖a‖ ^ (2 * r) * ‖x‖ ^ (rrLam r - 2 * r) * ‖1 - x ^ r‖ * ‖(qPoch x r)⁻¹‖ *
          ‖rrQ x a r‖
        ≤ 1 * ‖x‖ ^ r * 2 * C * (C / (1 - ‖a‖)) := by have := hQ r; have := hC r; gcongr
      _ = 2 * C * (C / (1 - ‖a‖)) * ‖x‖ ^ r := by ring
  have hT : ∀ r, rrTerm x 2 a r - rrTerm x 1 a r = A r + B r := by
    intro r
    obtain ⟨e, he⟩ : ∃ e, rrLam r = e + 2 * r := ⟨rrLam r - 2 * r, by
      have := three_mul_le_rrLam r; omega⟩
    have hQs := rrQ_succ hx ha r
    simp only [rrTerm, A, B, he, ← hQs, show e + 2 * r - 1 * r = e + r by omega,
      show e + 2 * r - 2 * r = e by omega]
    ring
  have hU : ∀ s, a * rrTerm x 1 (a * x) s = A s + B (s + 1) := by
    intro s
    obtain ⟨e, he⟩ : ∃ e, rrLam s = e + 2 * s := ⟨rrLam s - 2 * s, by
      have := three_mul_le_rrLam s; omega⟩
    have hP := qPoch_inv_succ hx s
    have hl1 : rrLam (s + 1) - 2 * (s + 1) = e + 5 * s + 1 := by rw [rrLam_succ, he]; omega
    simp only [rrTerm, A, B, rrQ_mul_x, he, hl1, show e + 2 * s - 1 * s = e + s by omega]
    rw [← hP]
    ring
  have hB0 : B 0 = 0 := by simp [B]
  unfold rrH
  rw [← (summable_rrTerm hx (le_refl 2) ha).tsum_sub (summable_rrTerm hx one_le_two ha),
    tsum_congr hT, ← tsum_mul_left, tsum_congr hU, hA.tsum_add hB,
    hA.tsum_add ((summable_nat_add_iff 1).2 hB),
    tsum_eq_zero_add' ((summable_nat_add_iff 1).2 hB), hB0, zero_add]

/-- (19.14.4): `H₂(a) = H₂(ax) + a H₂(ax²)`. -/
theorem rrH_two_eq (hx : ‖x‖ < 1) {a : ℂ} (ha : ‖a‖ < 1) :
    rrH x 2 a = rrH x 2 (a * x) + a * rrH x 2 (a * x * x) := by
  have hax : ‖a * x‖ < 1 := (norm_mul_pow_le hx a 1).trans_lt ha |>.trans_le' (by simp)
  have h1 := rrH_one hx ha
  have h2 := rrH_two_sub hx ha
  have h3 := rrH_one hx hax
  rw [h3] at h2
  linear_combination h2 + h1

theorem summable_rrG_term (hx : ‖x‖ < 1) {C : ℝ} (hC : ∀ n, ‖(qPoch x n)⁻¹‖ ≤ C) {b : ℂ}
    (hb : ‖b‖ < 1) : Summable fun s : ℕ ↦ b ^ s * x ^ (s * (s - 1)) * (qPoch x s)⁻¹ := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one (norm_nonneg _) hb).mul_left C)
    fun s ↦ ?_
  simp only [norm_mul, norm_pow]
  calc ‖b‖ ^ s * ‖x‖ ^ (s * (s - 1)) * ‖(qPoch x s)⁻¹‖ ≤ ‖b‖ ^ s * 1 * C := by
        gcongr
        · exact pow_le_one₀ (norm_nonneg _) hx.le
        · exact hC s
    _ = C * ‖b‖ ^ s := by ring

/-- `G(a) = G(ax) + a G(ax²)`. -/
theorem rrG_eq (hx : ‖x‖ < 1) {a : ℂ} (ha : ‖a‖ < 1) :
    rrG x a = rrG x (a * x) + a * rrG x (a * x * x) := by
  obtain ⟨C, -, hC⟩ := exists_norm_qPoch_inv_le hx
  have hax : ‖a * x‖ < 1 := (norm_mul_pow_le hx a 1).trans_lt ha |>.trans_le' (by simp)
  have haxx : ‖a * x * x‖ < 1 := (norm_mul_pow_le hx (a * x) 1).trans_lt hax |>.trans_le' (by simp)
  unfold rrG
  set g : ℕ → ℂ := fun s ↦ a ^ s * x ^ (s * (s - 1)) * (qPoch x s)⁻¹ with hg
  set g1 : ℕ → ℂ := fun s ↦ (a * x) ^ s * x ^ (s * (s - 1)) * (qPoch x s)⁻¹ with hg1
  set g2 : ℕ → ℂ := fun s ↦ (a * x * x) ^ s * x ^ (s * (s - 1)) * (qPoch x s)⁻¹ with hg2
  have sg := summable_rrG_term hx hC ha
  have sg1 := summable_rrG_term hx hC hax
  have sg2 := summable_rrG_term hx hC haxx
  have hpt : ∀ s, g (s + 1) = g1 (s + 1) + a * g2 s := by
    intro s
    have hP := qPoch_inv_succ hx s
    have e1 : (s + 1) * (s + 1 - 1) = s * (s - 1) + 2 * s := by
      cases s with
      | zero => simp
      | succ k => simp only [Nat.add_sub_cancel]; ring
    simp only [hg, hg1, hg2, e1]
    rw [← hP]
    ring
  rw [tsum_eq_zero_add' ((summable_nat_add_iff 1).2 sg),
    tsum_eq_zero_add' ((summable_nat_add_iff 1).2 sg1), tsum_congr hpt,
    ((summable_nat_add_iff 1).2 sg1).tsum_add (sg2.mul_left a), tsum_mul_left]
  simp only [hg, hg1, pow_zero, zero_mul, qPoch_zero, inv_one, mul_one]
  ring

/-! ### `H₂ = G` -/

theorem rrTerm_zero (x : ℂ) (m : ℕ) (a : ℂ) : rrTerm x m a 0 = (1 - a ^ m) * rrQ x a 0 := by
  simp [rrTerm, rrLam, qPoch_zero]

theorem exists_norm_rrH_two_sub_one_le (hx : ‖x‖ < 1) :
    ∃ K ≥ 0, ∀ a : ℂ, ‖a‖ ≤ 1 / 2 → ‖rrH x 2 a - 1‖ ≤ K * ‖a‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_qPoch_inv_le hx
  have hxl : 0 < 1 - ‖x‖ := by linarith
  refine ⟨2 * C + C + 2 * C ^ 2 / (1 - ‖x‖), by positivity, fun a ha ↦ ?_⟩
  have ha1 : ‖a‖ < 1 := ha.trans_lt (by norm_num)
  have hQa : C / (1 - ‖a‖) ≤ 2 * C := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hs := summable_rrTerm hx (le_refl 2) ha1
  rw [rrH, tsum_eq_zero_add' ((summable_nat_add_iff 1).2 hs), rrTerm_zero]
  have hq0 := norm_rrQ_zero_sub_one_le hx hC ha1
  have hq := norm_rrQ_le hx hC ha1 0
  -- the tail
  have htail : ‖∑' r : ℕ, rrTerm x 2 a (r + 1)‖ ≤ ‖a‖ * (2 * C ^ 2) * (1 - ‖x‖)⁻¹ := by
    have hg : HasSum (fun r : ℕ ↦ ‖a‖ * (2 * C ^ 2) * ‖x‖ ^ r) (‖a‖ * (2 * C ^ 2) * (1 - ‖x‖)⁻¹) :=
      (hasSum_geometric_of_lt_one (norm_nonneg _) hx).mul_left _
    refine tsum_of_norm_bounded hg fun r ↦ ?_
    refine (norm_rrTerm_le hx hC (le_refl 2) ha1 (r + 1)).trans ?_
    have h1 : ‖a‖ ^ (2 * (r + 1)) ≤ ‖a‖ / 2 := by
      calc ‖a‖ ^ (2 * (r + 1)) ≤ ‖a‖ ^ 2 :=
            pow_le_pow_of_le_one (norm_nonneg _) ha1.le (by omega)
        _ ≤ ‖a‖ / 2 := by nlinarith [norm_nonneg a]
    have h2 : ‖x‖ ^ (r + 1) ≤ ‖x‖ ^ r := pow_le_pow_of_le_one (norm_nonneg _) hx.le (by omega)
    have h3 : 0 ≤ 2 * C * (C / (1 - ‖a‖)) := by
      have : 0 < 1 - ‖a‖ := by linarith
      positivity
    calc ‖a‖ ^ (2 * (r + 1)) * (2 * C * (C / (1 - ‖a‖))) * ‖x‖ ^ (r + 1)
        ≤ (‖a‖ / 2) * (2 * C * (2 * C)) * ‖x‖ ^ r := by gcongr
      _ = ‖a‖ * (2 * C ^ 2) * ‖x‖ ^ r := by ring
  have e : (1 - a ^ 2) * rrQ x a 0 + ∑' r : ℕ, rrTerm x 2 a (r + 1) - 1 =
      (rrQ x a 0 - 1) - a ^ 2 * rrQ x a 0 + ∑' r : ℕ, rrTerm x 2 a (r + 1) := by ring
  rw [e]
  have ha2 : ‖a ^ 2 * rrQ x a 0‖ ≤ C * ‖a‖ := by
    rw [norm_mul, norm_pow]
    have : ‖a‖ ^ 2 ≤ ‖a‖ / 2 := by nlinarith [norm_nonneg a]
    calc ‖a‖ ^ 2 * ‖rrQ x a 0‖ ≤ (‖a‖ / 2) * (2 * C) :=
          mul_le_mul this (hq.trans hQa) (norm_nonneg _) (by positivity)
      _ = C * ‖a‖ := by ring
  have hq0' : ‖rrQ x a 0 - 1‖ ≤ 2 * C * ‖a‖ := by
    refine hq0.trans ?_
    rw [div_le_iff₀ (by linarith)]
    have : 1 / 2 ≤ 1 - ‖a‖ := by linarith
    nlinarith [mul_nonneg hC0.le (norm_nonneg a)]
  calc ‖rrQ x a 0 - 1 - a ^ 2 * rrQ x a 0 + ∑' r : ℕ, rrTerm x 2 a (r + 1)‖
      ≤ ‖rrQ x a 0 - 1‖ + ‖a ^ 2 * rrQ x a 0‖ + ‖∑' r : ℕ, rrTerm x 2 a (r + 1)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ 2 * C * ‖a‖ + C * ‖a‖ + ‖a‖ * (2 * C ^ 2) * (1 - ‖x‖)⁻¹ := by gcongr
    _ = (2 * C + C + 2 * C ^ 2 / (1 - ‖x‖)) * ‖a‖ := by field_simp

theorem exists_norm_rrG_sub_one_le (hx : ‖x‖ < 1) :
    ∃ K ≥ 0, ∀ a : ℂ, ‖a‖ ≤ 1 / 2 → ‖rrG x a - 1‖ ≤ K * ‖a‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_qPoch_inv_le hx
  refine ⟨2 * C, by positivity, fun a ha ↦ ?_⟩
  have ha1 : ‖a‖ < 1 := ha.trans_lt (by norm_num)
  have sg := summable_rrG_term hx hC ha1
  rw [rrG, tsum_eq_zero_add' ((summable_nat_add_iff 1).2 sg)]
  simp only [pow_zero, zero_mul, qPoch_zero, inv_one, mul_one, add_sub_cancel_left]
  have hg : HasSum (fun s : ℕ ↦ ‖a‖ * C * (1 / 2 : ℝ) ^ s) (‖a‖ * C * (1 - 1 / 2)⁻¹) :=
    (hasSum_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  refine (tsum_of_norm_bounded hg fun s ↦ ?_).trans (le_of_eq (by norm_num; ring))
  simp only [norm_mul, norm_pow]
  calc ‖a‖ ^ (s + 1) * ‖x‖ ^ ((s + 1) * (s + 1 - 1)) * ‖(qPoch x (s + 1))⁻¹‖
      ≤ (‖a‖ * (1 / 2) ^ s) * 1 * C := by
        gcongr
        · rw [pow_succ, mul_comm]; gcongr
        · exact pow_le_one₀ (norm_nonneg _) hx.le
        · exact hC _
    _ = ‖a‖ * C * (1 / 2) ^ s := by ring

/-- `H₂(a) = ∑_s a^s x^{s(s-1)} P_s` for `‖a‖ < 1` (the book's expansion of `H₂` in powers of
`a`, obtained from (19.14.4)). -/
theorem rrH_two_eq_rrG (hx : ‖x‖ < 1) {a : ℂ} (ha : ‖a‖ < 1) : rrH x 2 a = rrG x a := by
  set D : ℂ → ℂ := fun b ↦ rrH x 2 b - rrG x b with hD
  have hFE : ∀ b : ℂ, ‖b‖ < 1 → D b = D (b * x) + b * D (b * x * x) := by
    intro b hb
    simp only [hD]
    rw [rrH_two_eq hx hb, rrG_eq hx hb]
    ring
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_norm_rrH_two_sub_one_le hx
  obtain ⟨K₂, hK₂0, hK₂⟩ := exists_norm_rrG_sub_one_le hx
  have hK : ∀ b : ℂ, ‖b‖ ≤ 1 / 2 → ‖D b‖ ≤ (K₁ + K₂) * ‖b‖ := by
    intro b hb
    have : D b = (rrH x 2 b - 1) - (rrG x b - 1) := by simp only [hD]; ring
    rw [this]
    calc _ ≤ ‖rrH x 2 b - 1‖ + ‖rrG x b - 1‖ := norm_sub_le _ _
      _ ≤ K₁ * ‖b‖ + K₂ * ‖b‖ := add_le_add (hK₁ b hb) (hK₂ b hb)
      _ = (K₁ + K₂) * ‖b‖ := by ring
  set t := min (1 / 2 : ℝ) ((1 - ‖x‖) / 2) with ht
  have ht0 : 0 < t := lt_min (by norm_num) (by linarith)
  have ht12 : t ≤ 1 / 2 := min_le_left _ _
  have htx : t ≤ (1 - ‖x‖) / 2 := min_le_right _ _
  set θ := ‖x‖ + t * ‖x‖ ^ 2 with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ < 1 := by
    have : t * ‖x‖ ^ 2 ≤ t := mul_le_of_le_one_right ht0.le
      (pow_le_one₀ (norm_nonneg _) hx.le)
    linarith
  have hiter : ∀ n : ℕ, ∀ b : ℂ, ‖b‖ ≤ t → ‖D b‖ ≤ (K₁ + K₂) * θ ^ n * ‖b‖ := by
    intro n
    induction n with
    | zero => intro b hb; simpa using hK b (hb.trans ht12)
    | succ n ih =>
      intro b hb
      have hb1 : ‖b‖ < 1 := hb.trans_lt (by linarith)
      have hbx : ‖b * x‖ ≤ t := (norm_mul_pow_le hx b 1).trans hb |>.trans_eq' (by simp)
      have hbxx : ‖b * x * x‖ ≤ t :=
        (norm_mul_pow_le hx (b * x) 1).trans hbx |>.trans_eq' (by simp)
      rw [hFE b hb1]
      have h1 := ih _ hbx
      have h2 := ih _ hbxx
      have hn : 0 ≤ (K₁ + K₂) * θ ^ n := by positivity
      calc ‖D (b * x) + b * D (b * x * x)‖ ≤ ‖D (b * x)‖ + ‖b‖ * ‖D (b * x * x)‖ :=
            (norm_add_le _ _).trans_eq (by rw [norm_mul])
        _ ≤ (K₁ + K₂) * θ ^ n * ‖b * x‖ + ‖b‖ * ((K₁ + K₂) * θ ^ n * ‖b * x * x‖) := by
            gcongr
        _ = (K₁ + K₂) * θ ^ n * ‖b‖ * (‖x‖ + ‖b‖ * ‖x‖ ^ 2) := by
            simp only [norm_mul]; ring
        _ ≤ (K₁ + K₂) * θ ^ n * ‖b‖ * θ := by
            gcongr
            rw [hθ]
            have := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖x‖)
            linarith
        _ = (K₁ + K₂) * θ ^ (n + 1) * ‖b‖ := by ring
  have hsmall : ∀ b : ℂ, ‖b‖ ≤ t → D b = 0 := by
    intro b hb
    have hlim : Tendsto (fun n : ℕ ↦ (K₁ + K₂) * θ ^ n * ‖b‖) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).const_mul (K₁ + K₂)
      simpa using this.mul_const ‖b‖
    have : ‖D b‖ ≤ 0 := ge_of_tendsto' hlim fun n ↦ hiter n b hb
    exact norm_le_zero_iff.1 this
  have hext : ∀ k : ℕ, ∀ b : ℂ, ‖b‖ < 1 → ‖b‖ * ‖x‖ ^ k ≤ t → D b = 0 := by
    intro k
    induction k with
    | zero => intro b _ hb; exact hsmall b (by simpa using hb)
    | succ k ih =>
      intro b hb1 hb
      have hbx1 : ‖b * x‖ < 1 := (norm_mul_pow_le hx b 1).trans_lt hb1 |>.trans_le' (by simp)
      have hbxx1 : ‖b * x * x‖ < 1 :=
        (norm_mul_pow_le hx (b * x) 1).trans_lt hbx1 |>.trans_le' (by simp)
      rw [hFE b hb1, ih (b * x) hbx1 (by rw [norm_mul, mul_assoc, ← pow_succ']; exact hb),
        ih (b * x * x) hbxx1 ?_]
      · ring
      · rw [norm_mul, norm_mul, mul_assoc, mul_assoc, ← pow_succ', ← pow_succ']
        refine le_trans ?_ hb
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one (norm_nonneg _) hx.le (by omega)) (norm_nonneg _)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one ht0 hx
  have := hext k a ha (by
    calc ‖a‖ * ‖x‖ ^ k ≤ 1 * ‖x‖ ^ k :=
          mul_le_mul_of_nonneg_right ha.le (by positivity)
      _ ≤ t := by rw [one_mul]; exact hk.le)
  simpa [hD, sub_eq_zero] using this

/-! ### Evaluation at `a = x` and `a = x²` -/

/-- `P_r Q_r(x) = ∏_{n ≥ 1} (1 - xⁿ)⁻¹`. -/
theorem qPoch_inv_mul_rrQ_self (hx : ‖x‖ < 1) (r : ℕ) :
    (qPoch x r)⁻¹ * rrQ x x r = (qPochInf x)⁻¹ := by
  have hm : Multipliable fun n : ℕ ↦ (1 - x ^ (n + r + 1)) :=
    multipliable_one_sub_of_summable (f := fun n : ℕ ↦ x ^ (n + r + 1))
      ((summable_norm_pow_lin hx 1 (r + 1) one_pos).congr fun n ↦ by ring_nf)
  have h := Multipliable.prod_mul_tprod_nat_mul' (f := fun k : ℕ ↦ 1 - x ^ (k + 1)) (k := r) hm
  rw [rrQ, ← mul_inv, qPochInf, ← h, qPoch]
  congr 2
  congr 1; ext k; ring

/-- The five residue classes: `∏_{n ≥ 1} (1 - xⁿ) = ∏_{j=1}^{5} ∏_{n ≥ 0} (1 - x^{5n+j})`. -/
theorem qPochInf_eq_five (hx : ‖x‖ < 1) :
    qPochInf x = (∏' n : ℕ, (1 - x ^ (5 * n + 1))) * (∏' n : ℕ, (1 - x ^ (5 * n + 2))) *
      (∏' n : ℕ, (1 - x ^ (5 * n + 3))) * (∏' n : ℕ, (1 - x ^ (5 * n + 4))) *
      ∏' n : ℕ, (1 - x ^ (5 * n + 5)) := by
  have hprod := ((((hasProd_one_sub_pow_lin hx 5 1 (by norm_num)).mul
    (hasProd_one_sub_pow_lin hx 5 2 (by norm_num))).mul
    (hasProd_one_sub_pow_lin hx 5 3 (by norm_num))).mul
    (hasProd_one_sub_pow_lin hx 5 4 (by norm_num))).mul
    (hasProd_one_sub_pow_lin hx 5 5 (by norm_num))
  have t1 := hprod.tendsto_prod_nat
  have t2 : Tendsto (fun N : ℕ ↦ qPoch x (5 * N)) atTop (𝓝 (qPochInf x)) :=
    (tendsto_qPoch hx).comp (tendsto_atTop_atTop.2 fun b ↦ ⟨b, fun n hn ↦ by omega⟩)
  have e : (fun N : ℕ ↦ qPoch x (5 * N)) = fun N ↦ ∏ k ∈ range N,
      ((1 - x ^ (5 * k + 1)) * (1 - x ^ (5 * k + 2)) * (1 - x ^ (5 * k + 3)) *
        (1 - x ^ (5 * k + 4)) * (1 - x ^ (5 * k + 5))) := by
    funext N
    induction N with
    | zero => simp [qPoch]
    | succ N ih =>
      rw [show 5 * (N + 1) = 5 * N + 1 + 1 + 1 + 1 + 1 by ring, qPoch_succ, qPoch_succ,
        qPoch_succ, qPoch_succ, qPoch_succ, ih, prod_range_succ]
      ring_nf
  rw [e] at t2
  exact tendsto_nhds_unique t2 t1

/-- `H₂(x) = ∏(1 - xⁿ)⁻¹ ∑_{n ∈ ℤ} (-1)ⁿ x^{n(5n+1)/2}`. -/
theorem rrH_two_self (hx : ‖x‖ < 1) :
    rrH x 2 x = (qPochInf x)⁻¹ * ∑' n : ℤ, (-1 : ℂ) ^ n * x ^ (n * (5 * n + 1) / 2) := by
  have hS := (hasProd_five_two_three hx).1.hasSum.nat_add_neg_add_one
  have hterm : ∀ r : ℕ, rrTerm x 2 x r = (qPochInf x)⁻¹ *
      ((-1 : ℂ) ^ (r : ℤ) * x ^ ((r : ℤ) * (5 * (r : ℤ) + 1) / 2) +
        (-1 : ℂ) ^ (-((r : ℤ) + 1)) * x ^ ((-((r : ℤ) + 1)) * (5 * (-((r : ℤ) + 1)) + 1) / 2)) := by
    intro r
    obtain ⟨e, he⟩ : ∃ e, rrLam r = e + 2 * r := ⟨rrLam r - 2 * r, by
      have := three_mul_le_rrLam r; omega⟩
    have h2 := two_mul_rrLam r
    have ex1 : (r : ℤ) * (5 * (r : ℤ) + 1) / 2 = ((e + 2 * r : ℕ) : ℤ) := by
      rw [← he]
      have : (r : ℤ) * (5 * (r : ℤ) + 1) = 2 * (rrLam r : ℤ) := by exact_mod_cast h2.symm
      rw [this, Int.mul_ediv_cancel_left _ two_ne_zero]
    have ex2 : (-((r : ℤ) + 1)) * (5 * (-((r : ℤ) + 1)) + 1) / 2 = ((e + 6 * r + 2 : ℕ) : ℤ) := by
      have : (-((r : ℤ) + 1)) * (5 * (-((r : ℤ) + 1)) + 1) = 2 * ((e + 6 * r + 2 : ℕ) : ℤ) := by
        have h3 : ((2 * rrLam r : ℕ) : ℤ) = ((r * (5 * r + 1) : ℕ) : ℤ) := by rw [h2]
        push_cast at h3 ⊢
        rw [he] at h3
        push_cast at h3
        nlinarith
      rw [this, Int.mul_ediv_cancel_left _ two_ne_zero]
    rw [ex1, ex2, zpow_natCast, zpow_natCast, zpow_natCast,
      show (-((r : ℤ) + 1)) = -((r + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
    rw [show rrTerm x 2 x r = ((-1) ^ r * x ^ (2 * r) * x ^ e * (1 - x ^ 2 * x ^ (2 * 2 * r))) *
        ((qPoch x r)⁻¹ * rrQ x x r) by
          simp only [rrTerm, he, show e + 2 * r - 2 * r = e by omega]; ring,
      qPoch_inv_mul_rrQ_self hx r]
    have hinv : ((-1 : ℂ) ^ (r + 1))⁻¹ = -(-1) ^ r := by
      rw [← inv_pow, inv_neg, inv_one, pow_succ]; ring
    rw [hinv]
    ring
  rw [rrH, tsum_congr hterm, tsum_mul_left, hS.tsum_eq]

/-- `H₁(x) = ∏(1 - xⁿ)⁻¹ ∑_{n ∈ ℤ} (-1)ⁿ x^{n(5n+3)/2}`. -/
theorem rrH_one_self (hx : ‖x‖ < 1) :
    rrH x 1 x = (qPochInf x)⁻¹ * ∑' n : ℤ, (-1 : ℂ) ^ n * x ^ (n * (5 * n + 3) / 2) := by
  have hS := (hasProd_five_one_four hx).1.hasSum.nat_add_neg_add_one
  have hterm : ∀ r : ℕ, rrTerm x 1 x r = (qPochInf x)⁻¹ *
      ((-1 : ℂ) ^ (r : ℤ) * x ^ ((r : ℤ) * (5 * (r : ℤ) + 3) / 2) +
        (-1 : ℂ) ^ (-((r : ℤ) + 1)) * x ^ ((-((r : ℤ) + 1)) * (5 * (-((r : ℤ) + 1)) + 3) / 2)) := by
    intro r
    obtain ⟨e, he⟩ : ∃ e, rrLam r = e + 2 * r := ⟨rrLam r - 2 * r, by
      have := three_mul_le_rrLam r; omega⟩
    have h2 := two_mul_rrLam r
    have h3 : ((2 * rrLam r : ℕ) : ℤ) = ((r * (5 * r + 1) : ℕ) : ℤ) := by rw [h2]
    push_cast at h3
    rw [he] at h3
    push_cast at h3
    have ex1 : (r : ℤ) * (5 * (r : ℤ) + 3) / 2 = ((e + 3 * r : ℕ) : ℤ) := by
      have : (r : ℤ) * (5 * (r : ℤ) + 3) = 2 * ((e + 3 * r : ℕ) : ℤ) := by push_cast; nlinarith
      rw [this, Int.mul_ediv_cancel_left _ two_ne_zero]
    have ex2 : (-((r : ℤ) + 1)) * (5 * (-((r : ℤ) + 1)) + 3) / 2 = ((e + 5 * r + 1 : ℕ) : ℤ) := by
      have : (-((r : ℤ) + 1)) * (5 * (-((r : ℤ) + 1)) + 3) = 2 * ((e + 5 * r + 1 : ℕ) : ℤ) := by
        push_cast; nlinarith
      rw [this, Int.mul_ediv_cancel_left _ two_ne_zero]
    rw [ex1, ex2, zpow_natCast, zpow_natCast, zpow_natCast,
      show (-((r : ℤ) + 1)) = -((r + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
    rw [show rrTerm x 1 x r = ((-1) ^ r * x ^ (2 * r) * x ^ (e + r) * (1 - x ^ 1 * x ^ (2 * 1 * r))) *
        ((qPoch x r)⁻¹ * rrQ x x r) by
          simp only [rrTerm, he, show e + 2 * r - 1 * r = e + r by omega]; ring,
      qPoch_inv_mul_rrQ_self hx r]
    have hinv : ((-1 : ℂ) ^ (r + 1))⁻¹ = -(-1) ^ r := by
      rw [← inv_pow, inv_neg, inv_one, pow_succ]; ring
    rw [hinv]
    ring
  rw [rrH, tsum_congr hterm, tsum_mul_left, hS.tsum_eq]

/-- **Theorem 362** (first Rogers–Ramanujan identity). For `‖x‖ < 1`,
`1 + x/(1 - x) + x⁴/((1 - x)(1 - x²)) + x⁹/((1 - x)(1 - x²)(1 - x³)) + ⋯ =
∏_{m ≥ 0} 1/((1 - x^{5m+1})(1 - x^{5m+4}))`. -/
@[kb "hardywright2008" "Thm 362, p. 402"]
theorem rogers_ramanujan_one (hx : ‖x‖ < 1) :
    HasProd (fun m : ℕ ↦ 1 / ((1 - x ^ (5 * m + 1)) * (1 - x ^ (5 * m + 4))))
      (∑' s : ℕ, x ^ (s ^ 2) / qPoch x s) := by
  have hG : ∑' s : ℕ, x ^ (s ^ 2) / qPoch x s = rrG x x := by
    unfold rrG
    congr 1; ext s
    rw [div_eq_mul_inv, ← pow_add]
    congr 2
    cases s with
    | zero => simp
    | succ k => simp only [Nat.add_sub_cancel]; ring
  rw [hG, ← rrH_two_eq_rrG hx hx, rrH_two_self hx, ← (hasProd_five_two_three hx).2.tprod_eq]
  have h14 := (hasProd_one_sub_pow_lin hx 5 1 (by norm_num)).mul
    (hasProd_one_sub_pow_lin hx 5 4 (by norm_num))
  have hne1 := tprod_one_sub_pow_lin_ne_zero hx 5 1 (by norm_num) le_rfl
  have hne4 := tprod_one_sub_pow_lin_ne_zero hx 5 4 (by norm_num) (by norm_num)
  have hne2 := tprod_one_sub_pow_lin_ne_zero hx 5 2 (by norm_num) (by norm_num)
  have hne3 := tprod_one_sub_pow_lin_ne_zero hx 5 3 (by norm_num) (by norm_num)
  have hne5 := tprod_one_sub_pow_lin_ne_zero hx 5 5 (by norm_num) (by norm_num)
  have h := hasProd_one.div₀ h14 (mul_ne_zero hne1 hne4)
  have h235 := (((hasProd_one_sub_pow_lin hx 5 2 (by norm_num)).mul
    (hasProd_one_sub_pow_lin hx 5 3 (by norm_num))).mul
    (hasProd_one_sub_pow_lin hx 5 5 (by norm_num)))
  rw [h235.tprod_eq, qPochInf_eq_five hx]
  convert h using 1
  field_simp

/-- **Theorem 363** (second Rogers–Ramanujan identity). For `‖x‖ < 1`,
`1 + x²/(1 - x) + x⁶/((1 - x)(1 - x²)) + x¹²/((1 - x)(1 - x²)(1 - x³)) + ⋯ =
∏_{m ≥ 0} 1/((1 - x^{5m+2})(1 - x^{5m+3}))`. -/
@[kb "hardywright2008" "Thm 363, p. 403"]
theorem rogers_ramanujan_two (hx : ‖x‖ < 1) :
    HasProd (fun m : ℕ ↦ 1 / ((1 - x ^ (5 * m + 2)) * (1 - x ^ (5 * m + 3))))
      (∑' s : ℕ, x ^ (s * (s + 1)) / qPoch x s) := by
  have hxx : ‖x * x‖ < 1 := (norm_mul_pow_le hx x 1).trans_lt hx |>.trans_le' (by simp)
  have hG : ∑' s : ℕ, x ^ (s * (s + 1)) / qPoch x s = rrG x (x * x) := by
    unfold rrG
    congr 1; ext s
    rw [div_eq_mul_inv, ← pow_two, ← pow_mul, ← pow_add]
    congr 2
    cases s with
    | zero => simp
    | succ k => simp only [Nat.add_sub_cancel]; ring
  rw [hG, ← rrH_two_eq_rrG hx hxx, ← rrH_one hx hx, rrH_one_self hx,
    ← (hasProd_five_one_four hx).2.tprod_eq]
  have h23 := (hasProd_one_sub_pow_lin hx 5 2 (by norm_num)).mul
    (hasProd_one_sub_pow_lin hx 5 3 (by norm_num))
  have hne1 := tprod_one_sub_pow_lin_ne_zero hx 5 1 (by norm_num) le_rfl
  have hne4 := tprod_one_sub_pow_lin_ne_zero hx 5 4 (by norm_num) (by norm_num)
  have hne2 := tprod_one_sub_pow_lin_ne_zero hx 5 2 (by norm_num) (by norm_num)
  have hne3 := tprod_one_sub_pow_lin_ne_zero hx 5 3 (by norm_num) (by norm_num)
  have hne5 := tprod_one_sub_pow_lin_ne_zero hx 5 5 (by norm_num) (by norm_num)
  have h := hasProd_one.div₀ h23 (mul_ne_zero hne2 hne3)
  have h145 := (((hasProd_one_sub_pow_lin hx 5 1 (by norm_num)).mul
    (hasProd_one_sub_pow_lin hx 5 4 (by norm_num))).mul
    (hasProd_one_sub_pow_lin hx 5 5 (by norm_num)))
  rw [h145.tprod_eq, qPochInf_eq_five hx]
  convert h using 1
  field_simp

end NTKB.HardyWright

