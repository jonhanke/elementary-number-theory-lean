/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.SixteenExpansion
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TwelveBounds

/-!
# Bounds for the weight-`8` series

For `‖q‖ ≤ 1/2`: `‖O(q) + E(q) - q - 127 q²‖ ≤ C ‖q‖³` (`norm_seriesOE_sub3_le`). The terms of
exponent at most `2` are `q` (from `O`, `r = 1`), `128 q²` (from `O`, `r = 2`) and `-q²` (from `E`,
`r = 1`); every other term has exponent at least `3`. This is the third-order version of
`TwelveBounds.lean` (needed because weight `8` is on the boundary of the vanishing criterion).
-/

open ModularForm ModularGroup Complex Filter Topology EisensteinSeries Matrix
open scoped MatrixGroups Real UpperHalfPlane Manifold
open UpperHalfPlane hiding I

noncomputable section

namespace NTKB.HardyWright.SixteenSquares

open TwelveSquares (pow_le_aux2)
open SixSquares (norm_cexp_pi_I_lt_one)

/-- `K₇ = ∑_r r⁷ 2⁻ʳ`. -/
def K7 : ℝ := ∑' r : ℕ, (r : ℝ) ^ 7 * (1 / 2) ^ r

lemma hasSum_K7 : HasSum (fun r : ℕ => (r : ℝ) ^ 7 * (1 / 2) ^ r) K7 :=
  (summable_pow_mul_geometric_of_norm_lt_one 7 (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).hasSum

lemma K7_nonneg : 0 ≤ K7 := tsum_nonneg fun r => by positivity

lemma pow_le_aux1 {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1 / 2) {r k a : ℕ} (hr : 1 ≤ r)
    (ha : k + 1 ≤ a) : ρ ^ (r * a) ≤ 2 * ρ * (1 / 2) ^ k * (1 / 2) ^ r := by
  have hρ1 : ρ ≤ 1 := by linarith
  have e : r + k ≤ r * a := by nlinarith
  obtain ⟨s, hs⟩ : ∃ s, r + k = s + 1 := ⟨r + k - 1, by omega⟩
  calc ρ ^ (r * a) ≤ ρ ^ (r + k) := pow_le_pow_of_le_one h0 hρ1 e
    _ = ρ * ρ ^ s := by rw [hs, pow_succ']
    _ ≤ ρ * (1 / 2) ^ s := by gcongr
    _ = 2 * ρ * (1 / 2) ^ (r + k) := by rw [hs, pow_succ]; ring
    _ = 2 * ρ * (1 / 2) ^ k * (1 / 2) ^ r := by rw [pow_add]; ring

lemma pow_le_aux3 {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1 / 2) {r k a : ℕ} (hr : 1 ≤ r)
    (ha : k + 3 ≤ a) : ρ ^ (r * a) ≤ 2 * ρ ^ 3 * (1 / 2) ^ k * (1 / 2) ^ r := by
  have hρ1 : ρ ≤ 1 := by linarith
  have e : r + k + 2 ≤ r * a := by nlinarith
  obtain ⟨s, hs⟩ : ∃ s, r + k + 2 = s + 3 := ⟨r + k - 1, by omega⟩
  calc ρ ^ (r * a) ≤ ρ ^ (r + k + 2) := pow_le_pow_of_le_one h0 hρ1 e
    _ = ρ ^ 3 * ρ ^ s := by rw [hs, pow_add]; ring
    _ ≤ ρ ^ 3 * (1 / 2) ^ s := by gcongr
    _ = 2 * ρ ^ 3 * (1 / 2) ^ (r + k) := by
        have : r + k = s + 1 := by omega
        rw [this, pow_succ]; ring
    _ = 2 * ρ ^ 3 * (1 / 2) ^ k * (1 / 2) ^ r := by rw [pow_add]; ring

lemma norm_inner7_le1 {f : ℕ → ℂ} {q : ℂ} (hq : ‖q‖ ≤ 1 / 2) {k a : ℕ} (ha : k + 1 ≤ a)
    (hf : ∀ r, ‖f r‖ ≤ (r : ℝ) ^ 7 * ‖q‖ ^ (r * a)) :
    ‖∑' r, f r‖ ≤ 2 * ‖q‖ * (1 / 2) ^ k * K7 := by
  refine tsum_of_norm_bounded (hasSum_K7.mul_left (2 * ‖q‖ * (1 / 2) ^ k)) fun r => ?_
  refine (hf r).trans ?_
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  · have := pow_le_aux1 (norm_nonneg q) hq hr ha
    calc (r : ℝ) ^ 7 * ‖q‖ ^ (r * a) ≤ (r : ℝ) ^ 7 * (2 * ‖q‖ * (1 / 2) ^ k * (1 / 2) ^ r) := by
          gcongr
      _ = _ := by ring

lemma norm_inner7_le2 {f : ℕ → ℂ} {q : ℂ} (hq : ‖q‖ ≤ 1 / 2) {k a : ℕ} (ha : k + 2 ≤ a)
    (hf : ∀ r, ‖f r‖ ≤ (r : ℝ) ^ 7 * ‖q‖ ^ (r * a)) :
    ‖∑' r, f r‖ ≤ 2 * ‖q‖ ^ 2 * (1 / 2) ^ k * K7 := by
  refine tsum_of_norm_bounded (hasSum_K7.mul_left (2 * ‖q‖ ^ 2 * (1 / 2) ^ k)) fun r => ?_
  refine (hf r).trans ?_
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  · have := pow_le_aux2 (norm_nonneg q) hq hr ha
    calc (r : ℝ) ^ 7 * ‖q‖ ^ (r * a) ≤ (r : ℝ) ^ 7 * (2 * ‖q‖ ^ 2 * (1 / 2) ^ k * (1 / 2) ^ r) := by
          gcongr
      _ = _ := by ring

lemma norm_inner7_le3 {f : ℕ → ℂ} {q : ℂ} (hq : ‖q‖ ≤ 1 / 2) {k a : ℕ} (ha : k + 3 ≤ a)
    (hf : ∀ r, ‖f r‖ ≤ (r : ℝ) ^ 7 * ‖q‖ ^ (r * a)) :
    ‖∑' r, f r‖ ≤ 2 * ‖q‖ ^ 3 * (1 / 2) ^ k * K7 := by
  refine tsum_of_norm_bounded (hasSum_K7.mul_left (2 * ‖q‖ ^ 3 * (1 / 2) ^ k)) fun r => ?_
  refine (hf r).trans ?_
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  · have := pow_le_aux3 (norm_nonneg q) hq hr ha
    calc (r : ℝ) ^ 7 * ‖q‖ ^ (r * a) ≤ (r : ℝ) ^ 7 * (2 * ‖q‖ ^ 3 * (1 / 2) ^ k * (1 / 2) ^ r) := by
          gcongr
      _ = _ := by ring

lemma hasSum_outer7 (c : ℝ) : HasSum (fun k : ℕ => 2 * c * (1 / 2) ^ k * K7) (4 * K7 * c) := by
  have := (hasSum_geometric_two.mul_left (2 * c)).mul_right K7
  convert this using 1; ring

lemma norm_term_O7 (q : ℂ) (a r : ℕ) : ‖(r : ℂ) ^ 7 * q ^ (r * a)‖ ≤ (r : ℝ) ^ 7 * ‖q‖ ^ (r * a) := by
  rw [norm_mul, norm_pow, norm_pow, Complex.norm_natCast]

lemma norm_term_E7 (q : ℂ) (a r : ℕ) :
    ‖(-1) ^ r * (r : ℂ) ^ 7 * q ^ (r * a)‖ ≤ (r : ℝ) ^ 7 * ‖q‖ ^ (r * a) := by
  rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, Complex.norm_natCast, norm_neg, norm_one,
    one_pow, one_mul]

lemma summable_seriesO_terms {q : ℂ} (hq : ‖q‖ ≤ 1 / 2) :
    Summable fun k : ℕ => ∑' r : ℕ, (r : ℂ) ^ 7 * q ^ (r * (2 * k + 1)) :=
  Summable.of_norm_bounded (hasSum_outer7 ‖q‖).summable fun k =>
    norm_inner7_le1 hq (k := k) (a := 2 * k + 1) (by omega) (norm_term_O7 q _)

lemma summable_seriesE_terms {q : ℂ} (hq : ‖q‖ ≤ 1 / 2) :
    Summable fun k : ℕ => ∑' r : ℕ, (-1) ^ r * (r : ℂ) ^ 7 * q ^ (r * (2 * (k + 1))) :=
  Summable.of_norm_bounded (hasSum_outer7 (‖q‖ ^ 2)).summable fun k => by
    have := norm_inner7_le2 hq (k := k) (a := 2 * (k + 1)) (by omega) (norm_term_E7 q _)
    linarith

/-- `K₇' = ∑_r (r+3)⁷ 2⁻ʳ`. -/
def K7' : ℝ := ∑' r : ℕ, ((r : ℝ) + 3) ^ 7 * (1 / 2) ^ r

lemma summable_K7' : Summable fun r : ℕ => ((r : ℝ) + 3) ^ 7 * (1 / 2 : ℝ) ^ r := by
  have h0 : Summable fun r : ℕ => (r : ℝ) ^ 7 * (1 / 2 : ℝ) ^ r :=
    summable_pow_mul_geometric_of_norm_lt_one 7 (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
  have h := (summable_nat_add_iff (f := fun r : ℕ => (r : ℝ) ^ 7 * (1 / 2 : ℝ) ^ r) 3).mpr h0
  refine (h.mul_left 8).congr fun r => ?_
  push_cast; rw [pow_add]; ring

/-- `K₇'' = ∑_s (s+2)⁷ 2⁻ˢ`. -/
def K7'' : ℝ := ∑' r : ℕ, ((r : ℝ) + 2) ^ 7 * (1 / 2) ^ r

lemma summable_K7'' : Summable fun r : ℕ => ((r : ℝ) + 2) ^ 7 * (1 / 2 : ℝ) ^ r := by
  have h0 : Summable fun r : ℕ => (r : ℝ) ^ 7 * (1 / 2 : ℝ) ^ r :=
    summable_pow_mul_geometric_of_norm_lt_one 7 (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
  have h := (summable_nat_add_iff (f := fun r : ℕ => (r : ℝ) ^ 7 * (1 / 2 : ℝ) ^ r) 2).mpr h0
  refine (h.mul_left 4).congr fun r => ?_
  push_cast; rw [pow_add]; ring

/-- The first row of `O`: `∑_r r⁷ q^r = q + 128 q² + O(q³)`. -/
lemma norm_firstO_sub_le {q : ℂ} (hq : ‖q‖ ≤ 1 / 2) :
    ‖∑' r : ℕ, (r : ℂ) ^ 7 * q ^ (r * (2 * 0 + 1)) - (q + 128 * q ^ 2)‖ ≤ K7' * ‖q‖ ^ 3 := by
  have hq1 : ‖q‖ < 1 := by linarith
  have hs : Summable fun r : ℕ => (r : ℂ) ^ 7 * q ^ (r * (2 * 0 + 1)) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 7 hq1
  have h2 := (hasSum_nat_add_iff' 3).mpr hs.hasSum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h2
  have e : ∑' r : ℕ, (r : ℂ) ^ 7 * q ^ (r * (2 * 0 + 1)) - (q + 128 * q ^ 2) =
      ∑' r : ℕ, (r : ℂ) ^ 7 * q ^ (r * (2 * 0 + 1)) -
        (0 + ((0 : ℕ) : ℂ) ^ 7 * q ^ (0 * (2 * 0 + 1)) + ((1 : ℕ) : ℂ) ^ 7 * q ^ (1 * (2 * 0 + 1))
          + ((2 : ℕ) : ℂ) ^ 7 * q ^ (2 * (2 * 0 + 1))) := by
    congr 1
    norm_num
  rw [e, ← h2.tsum_eq]
  refine tsum_of_norm_bounded ((summable_K7'.hasSum).mul_right (‖q‖ ^ 3)) fun r => ?_
  rw [norm_mul, norm_pow, norm_pow]
  have hc : ‖((r + 3 : ℕ) : ℂ)‖ = (r : ℝ) + 3 := by
    rw [Complex.norm_natCast]; push_cast; ring
  rw [hc, show (r + 3) * (2 * 0 + 1) = r + 3 by ring, pow_add]
  have : ‖q‖ ^ r ≤ (1 / 2) ^ r := pow_le_pow_left₀ (norm_nonneg _) hq r
  calc ((r : ℝ) + 3) ^ 7 * (‖q‖ ^ r * ‖q‖ ^ 3) ≤ ((r : ℝ) + 3) ^ 7 * ((1 / 2) ^ r * ‖q‖ ^ 3) := by
        gcongr
    _ = _ := by ring

/-- The first row of `E`: `∑_r (-1)^r r⁷ q^{2r} = -q² + O(q³)`. -/
lemma norm_firstE_sub_le {q : ℂ} (hq : ‖q‖ ≤ 1 / 2) :
    ‖∑' r : ℕ, (-1) ^ r * (r : ℂ) ^ 7 * q ^ (r * (2 * (0 + 1))) - (-q ^ 2)‖ ≤ K7'' * ‖q‖ ^ 3 := by
  have hq1 : ‖q‖ < 1 := by linarith
  have hs : Summable fun r : ℕ => (-1) ^ r * (r : ℂ) ^ 7 * q ^ (r * (2 * (0 + 1))) := by
    refine Summable.of_norm_bounded (g := fun r : ℕ => (r : ℝ) ^ 7 * (‖q‖ ^ 2) ^ r) ?_ fun r => ?_
    · exact summable_pow_mul_geometric_of_norm_lt_one 7 (by
        rw [Real.norm_of_nonneg (by positivity)]; nlinarith [norm_nonneg q])
    · refine (norm_term_E7 q 2 r).trans (le_of_eq ?_)
      rw [← pow_mul, mul_comm r 2]
  have h2 := (hasSum_nat_add_iff' 2).mpr hs.hasSum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h2
  have e : ∑' r : ℕ, (-1) ^ r * (r : ℂ) ^ 7 * q ^ (r * (2 * (0 + 1))) - (-q ^ 2) =
      ∑' r : ℕ, (-1) ^ r * (r : ℂ) ^ 7 * q ^ (r * (2 * (0 + 1))) -
        (0 + (-1) ^ 0 * ((0 : ℕ) : ℂ) ^ 7 * q ^ (0 * (2 * (0 + 1))) +
          (-1) ^ 1 * ((1 : ℕ) : ℂ) ^ 7 * q ^ (1 * (2 * (0 + 1)))) := by
    simp
  rw [e, ← h2.tsum_eq]
  refine tsum_of_norm_bounded ((summable_K7''.hasSum).mul_right (‖q‖ ^ 3)) fun r => ?_
  refine (norm_term_E7 q _ _).trans ?_
  have hc : ‖((r + 2 : ℕ) : ℂ)‖ = (r : ℝ) + 2 := by
    rw [Complex.norm_natCast]; push_cast; ring
  have h4 : (‖q‖ ^ ((r + 2) * (2 * (0 + 1)))) ≤ ‖q‖ ^ 3 * (1 / 2) ^ r := by
    have hn := norm_nonneg q
    have e1 : (r + 2) * (2 * (0 + 1)) = 3 + (2 * r + 1) := by ring
    rw [e1, pow_add]
    gcongr
    calc ‖q‖ ^ (2 * r + 1) ≤ (1 / 2) ^ (2 * r + 1) := pow_le_pow_left₀ hn hq _
      _ ≤ (1 / 2) ^ r := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hr7 : ((r + 2 : ℕ) : ℝ) = (r : ℝ) + 2 := by push_cast; ring
  rw [hr7]
  calc ((r : ℝ) + 2) ^ 7 * ‖q‖ ^ ((r + 2) * (2 * (0 + 1))) ≤ ((r : ℝ) + 2) ^ 7 * (‖q‖ ^ 3 * (1 / 2) ^ r) := by
        gcongr
    _ = _ := by ring

/-- The constant of `norm_seriesOE_sub3_le`. -/
def CL3 : ℝ := K7' + 4 * K7 + K7'' + 4 * K7

/-- `‖O(q) + E(q) - q - 127 q²‖ ≤ C ‖q‖³` for `‖q‖ ≤ 1/2`. -/
lemma norm_seriesOE_sub3_le {q : ℂ} (hq : ‖q‖ ≤ 1 / 2) :
    ‖seriesO q + seriesE q - q - 127 * q ^ 2‖ ≤ CL3 * ‖q‖ ^ 3 := by
  have hO := (summable_seriesO_terms hq).tsum_eq_zero_add
  have hE := (summable_seriesE_terms hq).tsum_eq_zero_add
  have hOr : ‖∑' k : ℕ, ∑' r : ℕ, (r : ℂ) ^ 7 * q ^ (r * (2 * (k + 1) + 1))‖ ≤
      4 * K7 * ‖q‖ ^ 3 :=
    tsum_of_norm_bounded (hasSum_outer7 (‖q‖ ^ 3)) fun k => by
      have := norm_inner7_le3 hq (k := k) (a := 2 * (k + 1) + 1) (by omega) (norm_term_O7 q _)
      linarith
  have hEr : ‖∑' k : ℕ, ∑' r : ℕ, (-1) ^ r * (r : ℂ) ^ 7 * q ^ (r * (2 * (k + 1 + 1)))‖ ≤
      4 * K7 * ‖q‖ ^ 3 :=
    tsum_of_norm_bounded (hasSum_outer7 (‖q‖ ^ 3)) fun k => by
      have := norm_inner7_le3 hq (k := k) (a := 2 * (k + 1 + 1)) (by omega) (norm_term_E7 q _)
      linarith
  have e : seriesO q + seriesE q - q - 127 * q ^ 2 =
      (∑' r : ℕ, (r : ℂ) ^ 7 * q ^ (r * (2 * 0 + 1)) - (q + 128 * q ^ 2)) +
        ∑' k : ℕ, ∑' r : ℕ, (r : ℂ) ^ 7 * q ^ (r * (2 * (k + 1) + 1)) +
      ((∑' r : ℕ, (-1) ^ r * (r : ℂ) ^ 7 * q ^ (r * (2 * (0 + 1))) - (-q ^ 2)) +
        ∑' k : ℕ, ∑' r : ℕ, (-1) ^ r * (r : ℂ) ^ 7 * q ^ (r * (2 * (k + 1 + 1)))) := by
    rw [seriesO, seriesE, hO, hE]; push_cast; ring
  rw [e]
  have h1 := norm_firstO_sub_le hq
  have h3 := norm_firstE_sub_le hq
  calc _ ≤ ‖∑' r : ℕ, (r : ℂ) ^ 7 * q ^ (r * (2 * 0 + 1)) - (q + 128 * q ^ 2)‖ +
        ‖∑' k : ℕ, ∑' r : ℕ, (r : ℂ) ^ 7 * q ^ (r * (2 * (k + 1) + 1))‖ +
      (‖∑' r : ℕ, (-1) ^ r * (r : ℂ) ^ 7 * q ^ (r * (2 * (0 + 1))) - (-q ^ 2)‖ +
        ‖∑' k : ℕ, ∑' r : ℕ, (-1) ^ r * (r : ℂ) ^ 7 * q ^ (r * (2 * (k + 1 + 1)))‖) := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        · exact norm_add_le _ _
        · exact norm_add_le _ _
    _ ≤ K7' * ‖q‖ ^ 3 + 4 * K7 * ‖q‖ ^ 3 + (K7'' * ‖q‖ ^ 3 + 4 * K7 * ‖q‖ ^ 3) := by gcongr
    _ = CL3 * ‖q‖ ^ 3 := by rw [CL3]; ring

end NTKB.HardyWright.SixteenSquares
