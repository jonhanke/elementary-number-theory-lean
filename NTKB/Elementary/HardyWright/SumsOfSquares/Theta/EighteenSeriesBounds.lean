/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.EighteenExpansion
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TwelveBounds
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.SixteenSeriesBounds

/-!
# Bounds for the weight-nine series

For `‖q‖ ≤ 1/2`: `A(q) = q + q² + O(q³)` and `B(q) = q + 256 q² + O(q³)` with explicit constants
`CA3`, `CB3`; and `norm_Lsum9_Wp_le`: the lattice sum `L_{W'}` is bounded by `ML9` on the strip
`|Re τ| ≤ 1`, `Im τ ≥ 1`.
-/

open ModularForm ModularGroup Complex Filter Topology EisensteinSeries Matrix
open scoped MatrixGroups Real UpperHalfPlane Manifold
open UpperHalfPlane hiding I

noncomputable section

namespace NTKB.HardyWright.EighteenSquares

open TwelveSquares (pow_le_aux2)
open SixteenSquares (pow_le_aux3)
open SixSquares (chiZ chiZ_eq norm_chiZ_le)

lemma K8_nonneg : 0 ≤ K8 := tsum_nonneg fun r => by positivity

lemma norm_inner8_le1_e18 {f : ℕ → ℂ} {q : ℂ} (hq : ‖q‖ ≤ 1 / 2) {k a : ℕ} (ha : k + 1 ≤ a)
    (hf : ∀ r, ‖f r‖ ≤ (r : ℝ) ^ 8 * ‖q‖ ^ (r * a)) :
    ‖∑' r, f r‖ ≤ 2 * ‖q‖ * (1 / 2) ^ k * K8 := by
  refine tsum_of_norm_bounded (hasSum_K8.mul_left (2 * ‖q‖ * (1 / 2) ^ k)) fun r => ?_
  refine (hf r).trans ?_
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  · have := pow_le_aux9 (norm_nonneg q) hq hr ha
    calc (r : ℝ) ^ 8 * ‖q‖ ^ (r * a) ≤ (r : ℝ) ^ 8 * (2 * ‖q‖ * (1 / 2) ^ k * (1 / 2) ^ r) := by
          gcongr
      _ = _ := by ring

lemma norm_inner8_le3_e18 {f : ℕ → ℂ} {q : ℂ} (hq : ‖q‖ ≤ 1 / 2) {k a : ℕ} (ha : k + 3 ≤ a)
    (hf : ∀ r, ‖f r‖ ≤ (r : ℝ) ^ 8 * ‖q‖ ^ (r * a)) :
    ‖∑' r, f r‖ ≤ 2 * ‖q‖ ^ 3 * (1 / 2) ^ k * K8 := by
  refine tsum_of_norm_bounded (hasSum_K8.mul_left (2 * ‖q‖ ^ 3 * (1 / 2) ^ k)) fun r => ?_
  refine (hf r).trans ?_
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  · have := pow_le_aux3 (norm_nonneg q) hq hr ha
    calc (r : ℝ) ^ 8 * ‖q‖ ^ (r * a) ≤ (r : ℝ) ^ 8 * (2 * ‖q‖ ^ 3 * (1 / 2) ^ k * (1 / 2) ^ r) := by
          gcongr
      _ = _ := by ring

lemma hasSum_outer8_e18 (c : ℝ) :
    HasSum (fun k : ℕ => 2 * c * (1 / 2) ^ k * K8) (4 * K8 * c) := by
  have := (hasSum_geometric_two.mul_left (2 * c)).mul_right K8
  convert this using 1; ring

lemma norm_termA_e18 (q : ℂ) (a r : ℕ) :
    ‖chiZ r * (r : ℂ) ^ 8 * q ^ (r * a)‖ ≤ (r : ℝ) ^ 8 * ‖q‖ ^ (r * a) := by
  rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_natCast]
  have := norm_chiZ_le (r : ℤ)
  calc ‖chiZ r‖ * (r : ℝ) ^ 8 * ‖q‖ ^ (r * a) ≤ 1 * (r : ℝ) ^ 8 * ‖q‖ ^ (r * a) := by gcongr
    _ = _ := by ring

lemma norm_termB_e18 (q : ℂ) (a r : ℕ) :
    ‖(r : ℂ) ^ 8 * q ^ (r * a)‖ ≤ (r : ℝ) ^ 8 * ‖q‖ ^ (r * a) := by
  rw [norm_mul, norm_pow, norm_pow, Complex.norm_natCast]

/-- `K₈' = ∑_r (r+3)⁸ 2⁻ʳ`. -/
def K8' : ℝ := ∑' r : ℕ, ((r : ℝ) + 3) ^ 8 * (1 / 2) ^ r

lemma summable_K8' : Summable fun r : ℕ => ((r : ℝ) + 3) ^ 8 * (1 / 2 : ℝ) ^ r := by
  have h0 : Summable fun r : ℕ => (r : ℝ) ^ 8 * (1 / 2 : ℝ) ^ r :=
    summable_pow_mul_geometric_of_norm_lt_one 8 (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
  have h := (summable_nat_add_iff (f := fun r : ℕ => (r : ℝ) ^ 8 * (1 / 2 : ℝ) ^ r) 3).mpr h0
  refine (h.mul_left 8).congr fun r => ?_
  push_cast; rw [pow_add]; ring

lemma K8'_nonneg : 0 ≤ K8' := tsum_nonneg fun r => by positivity

/-- `K₈'' = ∑_r (r+2)⁸ 2⁻ʳ`. -/
def K8'' : ℝ := ∑' r : ℕ, ((r : ℝ) + 2) ^ 8 * (1 / 2) ^ r

lemma summable_K8'' : Summable fun r : ℕ => ((r : ℝ) + 2) ^ 8 * (1 / 2 : ℝ) ^ r := by
  have h0 : Summable fun r : ℕ => (r : ℝ) ^ 8 * (1 / 2 : ℝ) ^ r :=
    summable_pow_mul_geometric_of_norm_lt_one 8 (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
  have h := (summable_nat_add_iff (f := fun r : ℕ => (r : ℝ) ^ 8 * (1 / 2 : ℝ) ^ r) 2).mpr h0
  refine (h.mul_left 4).congr fun r => ?_
  push_cast; rw [pow_add]; ring

lemma K8''_nonneg : 0 ≤ K8'' := tsum_nonneg fun r => by positivity

/-- A first row with `f 0 = 0`, `f 1 = q`, `f 2 = c q²` is `q + c q² + O(q³)`. -/
lemma norm_first3_e18 {f : ℕ → ℂ} {q : ℂ} (c : ℂ) (hq : ‖q‖ ≤ 1 / 2)
    (hf : ∀ r, ‖f r‖ ≤ (r : ℝ) ^ 8 * ‖q‖ ^ r) (h0 : f 0 = 0) (h1 : f 1 = q)
    (h2 : f 2 = c * q ^ 2) :
    ‖∑' r, f r - (q + c * q ^ 2)‖ ≤ K8' * ‖q‖ ^ 3 := by
  have hq1 : ‖‖q‖‖ < 1 := by rw [norm_norm]; linarith
  have hs : Summable f :=
    Summable.of_norm_bounded (summable_pow_mul_geometric_of_norm_lt_one 8 hq1) hf
  have h3 := (hasSum_nat_add_iff' 3).mpr hs.hasSum
  have e : ∑' r, f r - (q + c * q ^ 2) = ∑' r : ℕ, f (r + 3) := by
    rw [h3.tsum_eq]
    simp [Finset.sum_range_succ, h0, h1, h2]
  rw [e]
  refine tsum_of_norm_bounded ((summable_K8'.hasSum).mul_right (‖q‖ ^ 3)) fun r => ?_
  refine (hf (r + 3)).trans ?_
  have hc : (((r + 3 : ℕ) : ℝ)) = (r : ℝ) + 3 := by push_cast; ring
  rw [hc, pow_add]
  have : ‖q‖ ^ r ≤ (1 / 2) ^ r := pow_le_pow_left₀ (norm_nonneg _) hq r
  calc ((r : ℝ) + 3) ^ 8 * (‖q‖ ^ r * ‖q‖ ^ 3) ≤ ((r : ℝ) + 3) ^ 8 * ((1 / 2) ^ r * ‖q‖ ^ 3) := by
        gcongr
    _ = _ := by ring

/-- A row with `f 0 = 0`, `f 1 = q²`, `‖f r‖ ≤ r⁸ ‖q‖^{2r}` is `q² + O(q³)`. -/
lemma norm_second_e18 {f : ℕ → ℂ} {q : ℂ} (hq : ‖q‖ ≤ 1 / 2)
    (hf : ∀ r, ‖f r‖ ≤ (r : ℝ) ^ 8 * ‖q‖ ^ (r * 2)) (h0 : f 0 = 0) (h1 : f 1 = q ^ 2) :
    ‖∑' r, f r - q ^ 2‖ ≤ K8'' * ‖q‖ ^ 3 := by
  have hq1 : ‖q‖ < 1 := by linarith
  have hs : Summable f := by
    refine Summable.of_norm_bounded (g := fun r : ℕ => (r : ℝ) ^ 8 * (‖q‖ ^ 2) ^ r) ?_ fun r => ?_
    · exact summable_pow_mul_geometric_of_norm_lt_one 8 (by
        rw [Real.norm_of_nonneg (by positivity)]; nlinarith [norm_nonneg q])
    · refine (hf r).trans (le_of_eq ?_)
      rw [← pow_mul, mul_comm r 2]
  have h2 := (hasSum_nat_add_iff' 2).mpr hs.hasSum
  have e : ∑' r, f r - q ^ 2 = ∑' r : ℕ, f (r + 2) := by
    rw [h2.tsum_eq]
    simp [Finset.sum_range_succ, h0, h1]
  rw [e]
  refine tsum_of_norm_bounded ((summable_K8''.hasSum).mul_right (‖q‖ ^ 3)) fun r => ?_
  refine (hf (r + 2)).trans ?_
  have h4 : (‖q‖ ^ ((r + 2) * 2)) ≤ ‖q‖ ^ 3 * (1 / 2) ^ r := by
    have hn := norm_nonneg q
    have e1 : (r + 2) * 2 = 3 + (2 * r + 1) := by ring
    rw [e1, pow_add]
    gcongr
    calc ‖q‖ ^ (2 * r + 1) ≤ (1 / 2) ^ (2 * r + 1) := pow_le_pow_left₀ hn hq _
      _ ≤ (1 / 2) ^ r := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hr7 : ((r + 2 : ℕ) : ℝ) = (r : ℝ) + 2 := by push_cast; ring
  rw [hr7]
  calc ((r : ℝ) + 2) ^ 8 * ‖q‖ ^ ((r + 2) * 2) ≤ ((r : ℝ) + 2) ^ 8 * (‖q‖ ^ 3 * (1 / 2) ^ r) := by
        gcongr
    _ = _ := by ring

/-- The constant of `norm_seriesA_sub3_le`. -/
def CA3 : ℝ := K8' + K8'' + 4 * K8

lemma CA3_nonneg : 0 ≤ CA3 := by
  unfold CA3; have := K8'_nonneg; have := K8''_nonneg; have := K8_nonneg; positivity

/-- The constant of `norm_seriesB_sub3_le`. -/
def CB3 : ℝ := K8' + 4 * K8

lemma CB3_nonneg : 0 ≤ CB3 := by
  unfold CB3; have := K8'_nonneg; have := K8_nonneg; positivity

lemma norm_seriesA_sub3_le {q : ℂ} (hq : ‖q‖ ≤ 1 / 2) :
    ‖seriesA q - q - q ^ 2‖ ≤ CA3 * ‖q‖ ^ 3 := by
  have hs : Summable fun k : ℕ => ∑' r : ℕ, chiZ r * (r : ℂ) ^ 8 * q ^ (r * (k + 1)) :=
    Summable.of_norm_bounded (hasSum_outer9 q).summable fun k =>
      norm_inner8_le1_e18 hq (k := k) (a := k + 1) (by omega) (norm_termA_e18 q _)
  have hA := hs.tsum_eq_zero_add
  have hs1 : Summable fun k : ℕ => ∑' r : ℕ, chiZ r * (r : ℂ) ^ 8 * q ^ (r * (k + 1 + 1)) :=
    (summable_nat_add_iff 1).mpr hs
  have hA1 := hs1.tsum_eq_zero_add
  have hrest : ‖∑' k : ℕ, ∑' r : ℕ, chiZ r * (r : ℂ) ^ 8 * q ^ (r * (k + 1 + 1 + 1))‖ ≤
      4 * K8 * ‖q‖ ^ 3 :=
    tsum_of_norm_bounded (hasSum_outer8_e18 (‖q‖ ^ 3)) fun k => by
      have := norm_inner8_le3_e18 hq (k := k) (a := k + 1 + 1 + 1) (by omega) (norm_termA_e18 q _)
      linarith
  have h1 : ‖∑' r : ℕ, chiZ r * (r : ℂ) ^ 8 * q ^ (r * (0 + 1)) - (q + 0 * q ^ 2)‖ ≤
      K8' * ‖q‖ ^ 3 := by
    refine norm_first3_e18 (f := fun r : ℕ => chiZ r * (r : ℂ) ^ 8 * q ^ (r * (0 + 1))) 0 hq
      (fun r => by simpa using norm_termA_e18 q 1 r) (by simp [chiZ_eq]) ?_ ?_
    · have : chiZ 1 = 1 := by rw [chiZ_eq]; norm_num
      simp [this]
    · have : chiZ 2 = 0 := by rw [chiZ_eq]; norm_num
      simp [this]
  have h2 : ‖∑' r : ℕ, chiZ r * (r : ℂ) ^ 8 * q ^ (r * (0 + 1 + 1)) - q ^ 2‖ ≤
      K8'' * ‖q‖ ^ 3 := by
    refine norm_second_e18 (f := fun r : ℕ => chiZ r * (r : ℂ) ^ 8 * q ^ (r * (0 + 1 + 1))) hq
      (fun r => by simpa using norm_termA_e18 q 2 r) (by simp [chiZ_eq]) ?_
    have : chiZ 1 = 1 := by rw [chiZ_eq]; norm_num
    simp [this]
  have e : seriesA q - q - q ^ 2 =
      (∑' r : ℕ, chiZ r * (r : ℂ) ^ 8 * q ^ (r * (0 + 1)) - (q + 0 * q ^ 2)) +
      (∑' r : ℕ, chiZ r * (r : ℂ) ^ 8 * q ^ (r * (0 + 1 + 1)) - q ^ 2) +
        ∑' k : ℕ, ∑' r : ℕ, chiZ r * (r : ℂ) ^ 8 * q ^ (r * (k + 1 + 1 + 1)) := by
    rw [seriesA, hA, hA1]; ring
  rw [e]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ ‖∑' r : ℕ, chiZ r * (r : ℂ) ^ 8 * q ^ (r * (0 + 1)) - (q + 0 * q ^ 2)‖ +
        ‖∑' r : ℕ, chiZ r * (r : ℂ) ^ 8 * q ^ (r * (0 + 1 + 1)) - q ^ 2‖ +
        ‖∑' k : ℕ, ∑' r : ℕ, chiZ r * (r : ℂ) ^ 8 * q ^ (r * (k + 1 + 1 + 1))‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ K8' * ‖q‖ ^ 3 + K8'' * ‖q‖ ^ 3 + 4 * K8 * ‖q‖ ^ 3 := by gcongr
    _ = CA3 * ‖q‖ ^ 3 := by rw [CA3]; ring

lemma norm_seriesB_sub3_le {q : ℂ} (hq : ‖q‖ ≤ 1 / 2) :
    ‖seriesB q - q - 256 * q ^ 2‖ ≤ CB3 * ‖q‖ ^ 3 := by
  have hB := (summable_seriesB_terms hq).tsum_eq_zero_add
  have hrest : ‖∑' k : ℕ, chiZ (2 * ((k + 1 : ℕ) : ℤ) + 1) *
      ∑' r : ℕ, (r : ℂ) ^ 8 * q ^ (r * (2 * (k + 1) + 1))‖ ≤ 4 * K8 * ‖q‖ ^ 3 :=
    tsum_of_norm_bounded (hasSum_outer8_e18 (‖q‖ ^ 3)) fun k => by
      have h := norm_inner8_le3_e18 hq (k := k) (a := 2 * (k + 1) + 1) (by omega)
        (norm_termB_e18 q _)
      rw [norm_mul]
      calc ‖chiZ (2 * ((k + 1 : ℕ) : ℤ) + 1)‖ * _ ≤ 1 * (2 * ‖q‖ ^ 3 * (1 / 2) ^ k * K8) := by
            gcongr
            exact norm_chiZ_le _
        _ = _ := by ring
  have hχ : chiZ (2 * ((0 : ℕ) : ℤ) + 1) = 1 := by
    rw [show (2 * ((0 : ℕ) : ℤ) + 1) = 1 by norm_num, chiZ_eq]; norm_num
  have h1 : ‖∑' r : ℕ, (r : ℂ) ^ 8 * q ^ (r * (2 * 0 + 1)) - (q + 256 * q ^ 2)‖ ≤
      K8' * ‖q‖ ^ 3 := by
    refine norm_first3_e18 (f := fun r : ℕ => (r : ℂ) ^ 8 * q ^ (r * (2 * 0 + 1))) 256 hq
      (fun r => by simpa using norm_termB_e18 q 1 r) (by simp) (by simp) ?_
    norm_num
  have e : seriesB q - q - 256 * q ^ 2 =
      (∑' r : ℕ, (r : ℂ) ^ 8 * q ^ (r * (2 * 0 + 1)) - (q + 256 * q ^ 2)) +
        ∑' k : ℕ, chiZ (2 * ((k + 1 : ℕ) : ℤ) + 1) *
          ∑' r : ℕ, (r : ℂ) ^ 8 * q ^ (r * (2 * (k + 1) + 1)) := by
    rw [seriesB, hB, hχ]; ring
  rw [e]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ K8' * ‖q‖ ^ 3 + 4 * K8 * ‖q‖ ^ 3 := add_le_add h1 hrest
    _ = CB3 * ‖q‖ ^ 3 := by rw [CB3]; ring

/-! ### The bound for `L_{W'}` -/

/-- The bound for `L_{W'}` on the strip `|Re τ| ≤ 1`, `Im τ ≥ 1`. -/
def ML9 : ℝ := ∑' v : Fin 2 → ℤ, 2 * (r ⟨⟨1, 1⟩, one_pos⟩ ^ (-(9 : ℝ)) * ‖v‖ ^ (-(9 : ℝ)))

lemma norm_Lsum9_Wp_le (τ : ℍ) (hτ : 1 ≤ τ.im) (hr : |τ.re| ≤ 1) : ‖Lsum9 Wp τ‖ ≤ ML9 := by
  have hs := ((summable_one_div_norm_rpow (k := 9) (by norm_num)).mul_left
    (r ⟨⟨1, 1⟩, one_pos⟩ ^ (-(9 : ℝ)))).mul_left 2
  refine tsum_of_norm_bounded hs.hasSum fun v => ?_
  rw [norm_mul]
  have hmem : τ ∈ verticalStrip 1 1 := ⟨hr, hτ⟩
  have hb := summand_bound_of_mem_verticalStrip (k := 9) (by norm_num) v one_pos hmem
  have he : ‖eisSummand 9 v τ‖ ≤ r ⟨⟨1, 1⟩, one_pos⟩ ^ (-(9 : ℝ)) * ‖v‖ ^ (-(9 : ℝ)) := by
    simp only [eisSummand, norm_zpow]
    exact_mod_cast hb
  exact mul_le_mul (norm_Wp_le v) he (norm_nonneg _) (by norm_num)

end NTKB.HardyWright.EighteenSquares
