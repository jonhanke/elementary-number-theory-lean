/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TenExpansion
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TwelveBounds

/-!
# Bounds for the weight-five series

For `‖q‖ ≤ 1/2`:

* `norm_seriesA_sub_le`, `norm_seriesB_sub_le`: `A(q) = q + O(q²)` and `B(q) = q + O(q²)` with
  explicit constants `CA`, `CB` (the term `k = 0`, `r = 1` of each series equals `q`, all other terms
  have exponent at least `2`);
* `norm_Lsum5_Wp_le`: the lattice sum `L_{W'}` is bounded by `ML5` on the strip `|Re τ| ≤ 1`,
  `Im τ ≥ 1` (uniform bound for Eisenstein summands on vertical strips).

This ports `TwelveBounds.lean` and `SixBounds.lean` to the exponent `r⁴`.
-/

open ModularForm ModularGroup Complex Filter Topology EisensteinSeries Matrix
open scoped MatrixGroups Real UpperHalfPlane Manifold
open UpperHalfPlane hiding I

noncomputable section

namespace NTKB.HardyWright.TenSquares

open TwelveSquares (pow_le_aux2)
open SixSquares (chiZ chiZ_eq norm_chiZ_le)

lemma K4_nonneg : 0 ≤ K4 := tsum_nonneg fun r => by positivity

/-- An inner series `∑_r f(r)` with `‖f(r)‖ ≤ r⁴ ‖q‖^{ra}`, `a ≥ k + 1`. -/
lemma norm_inner4_le1 {f : ℕ → ℂ} {q : ℂ} (hq : ‖q‖ ≤ 1 / 2) {k a : ℕ} (ha : k + 1 ≤ a)
    (hf : ∀ r, ‖f r‖ ≤ (r : ℝ) ^ 4 * ‖q‖ ^ (r * a)) :
    ‖∑' r, f r‖ ≤ 2 * ‖q‖ * (1 / 2) ^ k * K4 := by
  refine tsum_of_norm_bounded (hasSum_K4.mul_left (2 * ‖q‖ * (1 / 2) ^ k)) fun r => ?_
  refine (hf r).trans ?_
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  · have := pow_le_aux5 (norm_nonneg q) hq hr ha
    calc (r : ℝ) ^ 4 * ‖q‖ ^ (r * a) ≤ (r : ℝ) ^ 4 * (2 * ‖q‖ * (1 / 2) ^ k * (1 / 2) ^ r) := by
          gcongr
      _ = _ := by ring

/-- An inner series `∑_r f(r)` with `‖f(r)‖ ≤ r⁴ ‖q‖^{ra}`, `a ≥ k + 2`. -/
lemma norm_inner4_le2 {f : ℕ → ℂ} {q : ℂ} (hq : ‖q‖ ≤ 1 / 2) {k a : ℕ} (ha : k + 2 ≤ a)
    (hf : ∀ r, ‖f r‖ ≤ (r : ℝ) ^ 4 * ‖q‖ ^ (r * a)) :
    ‖∑' r, f r‖ ≤ 2 * ‖q‖ ^ 2 * (1 / 2) ^ k * K4 := by
  refine tsum_of_norm_bounded (hasSum_K4.mul_left (2 * ‖q‖ ^ 2 * (1 / 2) ^ k)) fun r => ?_
  refine (hf r).trans ?_
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  · have := pow_le_aux2 (norm_nonneg q) hq hr ha
    calc (r : ℝ) ^ 4 * ‖q‖ ^ (r * a) ≤ (r : ℝ) ^ 4 * (2 * ‖q‖ ^ 2 * (1 / 2) ^ k * (1 / 2) ^ r) := by
          gcongr
      _ = _ := by ring

lemma hasSum_outer4 (c : ℝ) : HasSum (fun k : ℕ => 2 * c * (1 / 2) ^ k * K4) (4 * K4 * c) := by
  have := (hasSum_geometric_two.mul_left (2 * c)).mul_right K4
  convert this using 1; ring

lemma norm_term_A (q : ℂ) (a r : ℕ) :
    ‖chiZ r * (r : ℂ) ^ 4 * q ^ (r * a)‖ ≤ (r : ℝ) ^ 4 * ‖q‖ ^ (r * a) := by
  rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_natCast]
  have := norm_chiZ_le (r : ℤ)
  calc ‖chiZ r‖ * (r : ℝ) ^ 4 * ‖q‖ ^ (r * a) ≤ 1 * (r : ℝ) ^ 4 * ‖q‖ ^ (r * a) := by gcongr
    _ = _ := by ring

lemma norm_term_B (q : ℂ) (a r : ℕ) :
    ‖(r : ℂ) ^ 4 * q ^ (r * a)‖ ≤ (r : ℝ) ^ 4 * ‖q‖ ^ (r * a) := by
  rw [norm_mul, norm_pow, norm_pow, Complex.norm_natCast]

/-- `K₄' = ∑_r (r+2)⁴ 2⁻ʳ`. -/
def K4' : ℝ := ∑' r : ℕ, ((r : ℝ) + 2) ^ 4 * (1 / 2) ^ r

lemma summable_K4' : Summable fun r : ℕ => ((r : ℝ) + 2) ^ 4 * (1 / 2 : ℝ) ^ r := by
  have h0 : Summable fun r : ℕ => (r : ℝ) ^ 4 * (1 / 2 : ℝ) ^ r :=
    summable_pow_mul_geometric_of_norm_lt_one 4 (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
  have h := (summable_nat_add_iff (f := fun r : ℕ => (r : ℝ) ^ 4 * (1 / 2 : ℝ) ^ r) 2).mpr h0
  refine (h.mul_left 4).congr fun r => ?_
  push_cast; rw [pow_add]; ring

lemma K4'_nonneg : 0 ≤ K4' := tsum_nonneg fun r => by positivity

/-- A first row `∑_r f(r)` with `f 0 = 0`, `f 1 = q` and `‖f r‖ ≤ r⁴ ‖q‖^r` is `q + O(q²)`. -/
lemma norm_first_row_sub_le {f : ℕ → ℂ} {q : ℂ} (hq : ‖q‖ ≤ 1 / 2)
    (hf : ∀ r, ‖f r‖ ≤ (r : ℝ) ^ 4 * ‖q‖ ^ r) (h0 : f 0 = 0) (h1 : f 1 = q) :
    ‖∑' r, f r - q‖ ≤ K4' * ‖q‖ ^ 2 := by
  have hq1 : ‖‖q‖‖ < 1 := by rw [norm_norm]; linarith
  have hs : Summable f :=
    Summable.of_norm_bounded (summable_pow_mul_geometric_of_norm_lt_one 4 hq1) hf
  have h2 := (hasSum_nat_add_iff' 2).mpr hs.hasSum
  have e : ∑' r, f r - q = ∑' r : ℕ, f (r + 2) := by
    rw [h2.tsum_eq]
    simp [Finset.sum_range_succ, h0, h1]
  rw [e]
  refine tsum_of_norm_bounded ((summable_K4'.hasSum).mul_right (‖q‖ ^ 2)) fun r => ?_
  refine (hf (r + 2)).trans ?_
  have hc : (((r + 2 : ℕ) : ℝ)) = (r : ℝ) + 2 := by push_cast; ring
  rw [hc, pow_add]
  have : ‖q‖ ^ r ≤ (1 / 2) ^ r := pow_le_pow_left₀ (norm_nonneg _) hq r
  calc ((r : ℝ) + 2) ^ 4 * (‖q‖ ^ r * ‖q‖ ^ 2) ≤ ((r : ℝ) + 2) ^ 4 * ((1 / 2) ^ r * ‖q‖ ^ 2) := by
        gcongr
    _ = _ := by ring

/-- The constant of `norm_seriesA_sub_le`. -/
def CA : ℝ := K4' + 4 * K4

lemma CA_nonneg : 0 ≤ CA := by
  unfold CA; have := K4'_nonneg; have := K4_nonneg; positivity

/-- The constant of `norm_seriesB_sub_le`. -/
def CB : ℝ := K4' + 4 * K4

lemma CB_nonneg : 0 ≤ CB := by
  unfold CB; have := K4'_nonneg; have := K4_nonneg; positivity

lemma norm_seriesA_sub_le {q : ℂ} (hq : ‖q‖ ≤ 1 / 2) : ‖seriesA q - q‖ ≤ CA * ‖q‖ ^ 2 := by
  have hs : Summable fun k : ℕ => ∑' r : ℕ, chiZ r * (r : ℂ) ^ 4 * q ^ (r * (k + 1)) :=
    Summable.of_norm_bounded (hasSum_outer4 ‖q‖).summable fun k =>
      norm_inner4_le1 hq (k := k) (a := k + 1) le_rfl (norm_term_A q _)
  have hA := hs.tsum_eq_zero_add
  have hrest : ‖∑' k : ℕ, ∑' r : ℕ, chiZ r * (r : ℂ) ^ 4 * q ^ (r * (k + 1 + 1))‖ ≤
      4 * K4 * ‖q‖ ^ 2 :=
    tsum_of_norm_bounded (hasSum_outer4 (‖q‖ ^ 2)) fun k => by
      have := norm_inner4_le2 hq (k := k) (a := k + 1 + 1) (by omega) (norm_term_A q _)
      linarith
  have h1 : ‖∑' r : ℕ, chiZ r * (r : ℂ) ^ 4 * q ^ (r * (0 + 1)) - q‖ ≤ K4' * ‖q‖ ^ 2 := by
    refine norm_first_row_sub_le (f := fun r : ℕ => chiZ r * (r : ℂ) ^ 4 * q ^ (r * (0 + 1))) hq
      (fun r => by simpa using norm_term_A q 1 r) (by simp [chiZ_eq]) ?_
    have : chiZ 1 = 1 := by rw [chiZ_eq]; norm_num
    simp [this]
  have e : seriesA q - q =
      (∑' r : ℕ, chiZ r * (r : ℂ) ^ 4 * q ^ (r * (0 + 1)) - q) +
        ∑' k : ℕ, ∑' r : ℕ, chiZ r * (r : ℂ) ^ 4 * q ^ (r * (k + 1 + 1)) := by
    rw [seriesA, hA]; ring
  rw [e]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ K4' * ‖q‖ ^ 2 + 4 * K4 * ‖q‖ ^ 2 := add_le_add h1 hrest
    _ = CA * ‖q‖ ^ 2 := by rw [CA]; ring

lemma norm_seriesB_sub_le {q : ℂ} (hq : ‖q‖ ≤ 1 / 2) : ‖seriesB q - q‖ ≤ CB * ‖q‖ ^ 2 := by
  have hB := (summable_seriesB_terms hq).tsum_eq_zero_add
  have hrest : ‖∑' k : ℕ, chiZ (2 * ((k + 1 : ℕ) : ℤ) + 1) *
      ∑' r : ℕ, (r : ℂ) ^ 4 * q ^ (r * (2 * (k + 1) + 1))‖ ≤ 4 * K4 * ‖q‖ ^ 2 :=
    tsum_of_norm_bounded (hasSum_outer4 (‖q‖ ^ 2)) fun k => by
      have h := norm_inner4_le2 hq (k := k) (a := 2 * (k + 1) + 1) (by omega) (norm_term_B q _)
      rw [norm_mul]
      calc ‖chiZ (2 * ((k + 1 : ℕ) : ℤ) + 1)‖ * _ ≤ 1 * (2 * ‖q‖ ^ 2 * (1 / 2) ^ k * K4) := by
            gcongr
            exact norm_chiZ_le _
        _ = _ := by ring
  have hχ : chiZ (2 * ((0 : ℕ) : ℤ) + 1) = 1 := by
    rw [show (2 * ((0 : ℕ) : ℤ) + 1) = 1 by norm_num, chiZ_eq]; norm_num
  have h1 : ‖∑' r : ℕ, (r : ℂ) ^ 4 * q ^ (r * (2 * 0 + 1)) - q‖ ≤ K4' * ‖q‖ ^ 2 := by
    refine norm_first_row_sub_le (f := fun r : ℕ => (r : ℂ) ^ 4 * q ^ (r * (2 * 0 + 1))) hq
      (fun r => by simpa using norm_term_B q 1 r) (by simp) (by simp)
  have e : seriesB q - q =
      (∑' r : ℕ, (r : ℂ) ^ 4 * q ^ (r * (2 * 0 + 1)) - q) +
        ∑' k : ℕ, chiZ (2 * ((k + 1 : ℕ) : ℤ) + 1) *
          ∑' r : ℕ, (r : ℂ) ^ 4 * q ^ (r * (2 * (k + 1) + 1)) := by
    rw [seriesB, hB, hχ]; ring
  rw [e]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ K4' * ‖q‖ ^ 2 + 4 * K4 * ‖q‖ ^ 2 := add_le_add h1 hrest
    _ = CB * ‖q‖ ^ 2 := by rw [CB]; ring

/-! ### The bound for `L_{W'}` -/

/-- The bound for `L_{W'}` on the strip `|Re τ| ≤ 1`, `Im τ ≥ 1`. -/
def ML5 : ℝ := ∑' v : Fin 2 → ℤ, 2 * (r ⟨⟨1, 1⟩, one_pos⟩ ^ (-(5 : ℝ)) * ‖v‖ ^ (-(5 : ℝ)))

lemma norm_Lsum5_Wp_le (τ : ℍ) (hτ : 1 ≤ τ.im) (hr : |τ.re| ≤ 1) : ‖Lsum5 Wp τ‖ ≤ ML5 := by
  have hs := ((summable_one_div_norm_rpow (k := 5) (by norm_num)).mul_left
    (r ⟨⟨1, 1⟩, one_pos⟩ ^ (-(5 : ℝ)))).mul_left 2
  refine tsum_of_norm_bounded hs.hasSum fun v => ?_
  rw [norm_mul]
  have hmem : τ ∈ verticalStrip 1 1 := ⟨hr, hτ⟩
  have hb := summand_bound_of_mem_verticalStrip (k := 5) (by norm_num) v one_pos hmem
  have he : ‖eisSummand 5 v τ‖ ≤ r ⟨⟨1, 1⟩, one_pos⟩ ^ (-(5 : ℝ)) * ‖v‖ ^ (-(5 : ℝ)) := by
    simp only [eisSummand, norm_zpow]
    exact_mod_cast hb
  exact mul_le_mul (norm_Wp_le v) he (norm_nonneg _) (by norm_num)

end NTKB.HardyWright.TenSquares
