/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TenLattice
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.SixExpansion

/-!
# The `q`-expansion of the weight-five lattice sum `L_W`

With `q = e^{πiτ}`, `κ = ∑_{n ∈ ℤ} χ(n) n⁻⁵` (the row `m = 0`),
`A(q) = ∑_{k ≥ 1} ∑_r χ(r) r⁴ q^{rk}` and `B(q) = ∑_{m ≥ 1 odd} χ(m) ∑_r r⁴ q^{rm}`:

`L_W(τ) = κ + (π⁵/12) B(q) + (π⁵/192) A(q)`   (`Lsum5_W_eq`).

Each row `∑_n W(m, n)(mτ + n)⁻⁵` (`m ≥ 1`) is split into residue classes of `n` (modulo `4` for
`m` even, modulo `2` for `m` odd) and evaluated by the Lipschitz formula
`∑_n (z + n)⁻⁵ = -(4/3) π⁵ i ∑_r r⁴ e^{2πirz}` (Mathlib's `EisensteinSeries.qExpansion_identity`);
the rows `-m` and `m` agree. This is the weight-five analogue of `SixExpansion.lean`. The final
lemma `summable_seriesB_terms` records the summability of the terms of `B` for `‖q‖ ≤ 1/2`.
-/

open ModularForm ModularGroup Complex Filter Topology EisensteinSeries Matrix
open scoped MatrixGroups Real UpperHalfPlane Manifold
open UpperHalfPlane hiding I

noncomputable section

namespace NTKB.HardyWright.TenSquares

open SixSquares (chiZ chiZ_eq chiZ_neg chiZ_of_even chiZ_add_four_mul norm_chiZ_le tsum_int_split
  I_pow_sub_neg_I_pow norm_cexp_pi_I_lt_one)

/-! ### The Lipschitz formula in weight `5` -/

lemma lip5 (z : ℍ) : ∑' n : ℤ, 1 / ((z : ℂ) + n) ^ 5 =
    -(4 / 3) * π ^ 5 * I * ∑' n : ℕ, (n : ℂ) ^ 4 * cexp (2 * π * I * z) ^ n := by
  have h := EisensteinSeries.qExpansion_identity (k := 4) (by norm_num) z
  rw [show (4 + 1 : ℕ) = 5 from rfl] at h
  rw [h]
  congr 1
  rw [show ((Nat.factorial 4 : ℕ) : ℂ) = 24 by norm_num [Nat.factorial]]
  have : (-2 * (π : ℂ) * I) ^ 5 = -32 * π ^ 5 * I := by
    rw [show (-2 * (π : ℂ) * I) ^ 5 = -32 * π ^ 5 * (I ^ 4 * I) by ring, I_pow_four]; ring
  rw [this]; ring

lemma lip5' (w : ℂ) (hw : 0 < w.im) : ∑' n : ℤ, 1 / (w + n) ^ 5 =
    -(4 / 3) * π ^ 5 * I * ∑' n : ℕ, (n : ℂ) ^ 4 * cexp (2 * π * I * w) ^ n :=
  lip5 ⟨w, hw⟩

/-- A residue class: `∑_j (c + jN + b)⁻⁵ = (-(4/3) π⁵ i / N⁵) ∑_r r⁴ e^{2πir(c+b)/N}`. -/
lemma class_sum5 (c : ℂ) (hc : 0 < c.im) (N : ℕ) (hN : 0 < N) (b : ℤ) :
    ∑' j : ℤ, 1 / (c + (j * N + b)) ^ 5 =
      -(4 / 3) * π ^ 5 * I / (N : ℂ) ^ 5 *
        ∑' r : ℕ, (r : ℂ) ^ 4 * cexp (2 * π * I * ((c + b) / N)) ^ r := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hw : 0 < ((c + b) / N).im := by
    have : ((c + b) / (N : ℂ)).im = c.im / N := by
      rw [show (N : ℂ) = ((N : ℝ) : ℂ) by push_cast; rfl, Complex.div_ofReal_im]; simp
    rw [this]; exact div_pos hc (by exact_mod_cast hN)
  have e : ∀ j : ℤ, 1 / (c + (j * N + b)) ^ 5 = 1 / (N : ℂ) ^ 5 * (1 / ((c + b) / N + j) ^ 5) := by
    intro j
    rw [show (c + b) / N + j = (c + (j * N + b)) / N by field_simp; ring, div_pow]
    field_simp
  simp_rw [e]
  rw [tsum_mul_left, lip5' _ hw]
  ring

/-! ### Rows -/

/-- The row `m` of `L_W`. -/
def row (z : ℍ) (m : ℤ) : ℂ := ∑' n : ℤ, W ![m, n] * eisSummand 5 ![m, n] z

lemma eisSummand_five (m n : ℤ) (z : ℍ) :
    eisSummand 5 ![m, n] z = 1 / ((m : ℂ) * z + n) ^ 5 := by
  simp only [eisSummand, cons_val_zero, cons_val_one, head_cons]
  rw [_root_.zpow_neg, one_div]
  norm_cast

lemma summable_row (z : ℍ) (m : ℤ) : Summable fun n : ℤ => W ![m, n] * eisSummand 5 ![m, n] z := by
  have hs := summable_Lsum5 (w := W) norm_W_le z
  exact hs.comp_injective (i := fun n : ℤ => ![m, n]) fun a b h => by
    simpa using congrFun h 1

lemma W_even_row (k : ℕ) (n : ℤ) : W ![2 * ((k : ℤ) + 1), n] = chiZ n := by
  have h1 : Even (2 * ((k : ℤ) + 1)) := even_two_mul _
  simp [W, h1, chiZ_of_even h1]

lemma W_odd_row (k : ℕ) (n : ℤ) :
    W ![2 * (k : ℤ) + 1, n] = I * (if Even n then chiZ (2 * k + 1) else 0) := by
  have h1 : ¬ Even (2 * (k : ℤ) + 1) := Int.not_even_iff_odd.mpr (odd_two_mul_add_one _)
  simp only [W, cons_val_zero, cons_val_one, h1, if_false]
  ring

lemma W_neg (v : Fin 2 → ℤ) : W (-v) = -W v := by
  simp only [W, Pi.neg_apply, even_neg, chiZ_neg]
  split_ifs <;> ring

lemma eisSummand_neg (v : Fin 2 → ℤ) (z : ℍ) : eisSummand 5 (-v) z = -eisSummand 5 v z := by
  simp only [eisSummand, Pi.neg_apply, Int.cast_neg]
  rw [show -((v 0 : ℂ)) * z + -(v 1 : ℂ) = -((v 0 : ℂ) * z + v 1) by ring]
  exact Odd.neg_zpow ⟨-3, by norm_num⟩ _

lemma row_neg (z : ℍ) (m : ℤ) : row z (-m) = row z m := by
  rw [row, row, ← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun n => ?_
  simp only [Equiv.neg_apply]
  have h : (![-m, -n] : Fin 2 → ℤ) = -![m, n] := by
    ext i; fin_cases i <;> simp
  rw [h, W_neg, eisSummand_neg]; ring

/-- The row `0`: `κ = ∑_n χ(n) n⁻⁵`. -/
def kappa : ℂ := ∑' n : ℤ, chiZ n * (1 / (n : ℂ) ^ 5)

lemma row_zero (z : ℍ) : row z 0 = kappa := by
  rw [row, kappa]
  refine tsum_congr fun n => ?_
  rw [eisSummand_five]
  simp only [W, cons_val_zero, cons_val_one, head_cons, Int.cast_zero, zero_mul, zero_add]
  have h0 : Even (0 : ℤ) := ⟨0, rfl⟩
  simp [h0, chiZ_of_even h0]

lemma summable_pow4 {w : ℂ} (hw : ‖w‖ < 1) : Summable fun r : ℕ => (r : ℂ) ^ 4 * w ^ r :=
  summable_pow_mul_geometric_of_norm_lt_one 4 hw

/-- The even row `m = 2(k+1)`. -/
lemma row_even (z : ℍ) (k : ℕ) : row z (2 * ((k : ℤ) + 1)) =
    π ^ 5 / 384 * ∑' r : ℕ, chiZ r * (r : ℂ) ^ 4 * cexp (π * I * z) ^ (r * (k + 1)) := by
  set m : ℤ := 2 * ((k : ℤ) + 1) with hm
  have hmc : ((m : ℤ) : ℂ) = 2 * ((k : ℂ) + 1) := by rw [hm]; push_cast; ring
  have hc : 0 < ((m : ℂ) * z).im := by
    rw [hmc]
    have : ((2 * ((k : ℂ) + 1)) * (z : ℂ)).im = (2 * ((k : ℝ) + 1)) * z.im := by
      simp [Complex.mul_im]
    rw [this]; exact mul_pos (by positivity) z.im_pos
  rw [row, tsum_int_split 4 (summable_row z m)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp only [hm, W_even_row, eisSummand_five]
  have hχ : ∀ (j : ℤ) (b : ℤ), chiZ (j * 4 + b) = chiZ b := fun j b => by
    rw [show j * 4 + b = b + 4 * j by ring, chiZ_add_four_mul]
  push_cast
  simp only [hχ]
  have c0 : chiZ 0 = 0 := chiZ_of_even ⟨0, rfl⟩
  have c1 : chiZ 1 = 1 := by rw [chiZ_eq]; norm_num
  have c2 : chiZ 2 = 0 := chiZ_of_even even_two
  have c3 : chiZ 3 = -1 := by rw [chiZ_eq]; norm_num
  rw [c0, c1, c2, c3]
  simp only [zero_mul, tsum_zero, one_mul, neg_one_mul, tsum_neg, zero_add, add_zero]
  have h1 := class_sum5 _ hc 4 (by norm_num) 1
  have h3 := class_sum5 _ hc 4 (by norm_num) 3
  push_cast at h1 h3
  rw [hmc] at h1 h3
  rw [h1, h3]
  -- the two exponentials
  set q := cexp (π * I * z) with hq
  have e1 : cexp (2 * π * I * (((m : ℂ) * z + 1) / 4)) = I * q ^ (k + 1) := by
    have : I * cexp (((k + 1 : ℕ) : ℂ) * (π * I * z)) =
        cexp (π / 2 * I + ((k + 1 : ℕ) : ℂ) * (π * I * z)) := by
      rw [Complex.exp_add, exp_pi_div_two_mul_I]
    rw [hq, ← Complex.exp_nat_mul, this, hmc]
    congr 1; push_cast; ring
  have e3 : cexp (2 * π * I * (((m : ℂ) * z + 3) / 4)) = -I * q ^ (k + 1) := by
    have : cexp (3 * π / 2 * I) = -I := by
      rw [show 3 * (π : ℂ) / 2 * I = π * I + π / 2 * I by ring, Complex.exp_add,
        Complex.exp_pi_mul_I, exp_pi_div_two_mul_I]; ring
    have h' : -I * cexp (((k + 1 : ℕ) : ℂ) * (π * I * z)) =
        cexp (3 * π / 2 * I + ((k + 1 : ℕ) : ℂ) * (π * I * z)) := by
      rw [Complex.exp_add, this]
    rw [hq, ← Complex.exp_nat_mul, h', hmc]
    congr 1; push_cast; ring
  rw [hmc] at e1 e3
  rw [e1, e3]
  have hq1 : ‖q ^ (k + 1)‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) (norm_cexp_pi_I_lt_one z) (by omega)
  have hs1 : Summable fun r : ℕ => (r : ℂ) ^ 4 * (I * q ^ (k + 1)) ^ r :=
    summable_pow4 (by rw [norm_mul, Complex.norm_I, one_mul]; exact hq1)
  have hs3 : Summable fun r : ℕ => (r : ℂ) ^ 4 * (-I * q ^ (k + 1)) ^ r :=
    summable_pow4 (by rw [norm_mul, norm_neg, Complex.norm_I, one_mul]; exact hq1)
  rw [← mul_neg, ← mul_add, ← tsum_neg, ← hs1.tsum_add hs3.neg]
  rw [show (4 : ℂ) ^ 5 = 1024 by norm_num, ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun r => ?_
  rw [mul_pow, mul_pow, ← pow_mul, show (k + 1) * r = r * (k + 1) by ring]
  have := I_pow_sub_neg_I_pow r
  linear_combination (-(π ^ 5 * I) / 768 * (r : ℂ) ^ 4 * q ^ (r * (k + 1))) * this +
    (-(π ^ 5) / 384 * chiZ r * (r : ℂ) ^ 4 * q ^ (r * (k + 1))) * I_sq

/-- The odd row `m = 2k + 1`. -/
lemma row_odd (z : ℍ) (k : ℕ) : row z (2 * (k : ℤ) + 1) =
    π ^ 5 / 24 * chiZ (2 * k + 1) * ∑' r : ℕ, (r : ℂ) ^ 4 * cexp (π * I * z) ^ (r * (2 * k + 1)) := by
  set m : ℤ := 2 * (k : ℤ) + 1 with hm
  have hmc : ((m : ℤ) : ℂ) = 2 * (k : ℂ) + 1 := by rw [hm]; push_cast; ring
  have hc : 0 < ((m : ℂ) * z).im := by
    rw [hmc]
    have : ((2 * (k : ℂ) + 1) * (z : ℂ)).im = (2 * (k : ℝ) + 1) * z.im := by
      simp [Complex.mul_im]
    rw [this]; exact mul_pos (by positivity) z.im_pos
  rw [row, tsum_int_split 2 (summable_row z m)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp only [hm, W_odd_row, eisSummand_five]
  push_cast
  have hev : ∀ j : ℤ, Even (j * 2) := fun j => ⟨j, by ring⟩
  have hod : ∀ j : ℤ, ¬ Even (j * 2 + 1) := fun j =>
    Int.not_even_iff_odd.mpr ⟨j, by ring⟩
  simp only [hev, hod, if_true, if_false, mul_zero, zero_mul, tsum_zero, add_zero]
  have h0 := class_sum5 _ hc 2 (by norm_num) 0
  push_cast at h0
  simp only [add_zero] at h0 ⊢
  rw [hmc] at h0
  rw [tsum_mul_left, h0]
  set q := cexp (π * I * z) with hq
  have e0 : cexp (2 * π * I * ((m : ℂ) * z / 2)) = q ^ (2 * k + 1) := by
    rw [hq, ← Complex.exp_nat_mul, hmc]
    congr 1; push_cast; ring
  rw [hmc] at e0
  rw [e0]
  rw [show (2 : ℂ) ^ 5 = 32 by norm_num]
  simp_rw [← pow_mul, show ∀ r : ℕ, (2 * k + 1) * r = r * (2 * k + 1) from fun r => by ring]
  have hI : I * I = -1 := I_mul_I
  linear_combination (-(π ^ 5 / 24) * chiZ (2 * k + 1) *
    ∑' r : ℕ, (r : ℂ) ^ 4 * q ^ (r * (2 * k + 1))) * hI

/-! ### The expansion -/

/-- `A(q) = ∑_{k ≥ 1} ∑_r χ(r) r⁴ q^{rk}`. -/
def seriesA (q : ℂ) : ℂ := ∑' k : ℕ, ∑' r : ℕ, chiZ r * (r : ℂ) ^ 4 * q ^ (r * (k + 1))

/-- `B(q) = ∑_{m ≥ 1 odd} χ(m) ∑_r r⁴ q^{rm}`. -/
def seriesB (q : ℂ) : ℂ :=
  ∑' k : ℕ, chiZ (2 * k + 1) * ∑' r : ℕ, (r : ℂ) ^ 4 * q ^ (r * (2 * k + 1))

lemma summable_rows (z : ℍ) : Summable (row z) := by
  have hs := summable_Lsum5 (w := W) norm_W_le z
  have hp : Summable fun p : ℤ × ℤ => W ![p.1, p.2] * eisSummand 5 ![p.1, p.2] z := by
    exact (finTwoArrowEquiv ℤ).summable_iff.mp (hs.congr fun v => by
        simp [show ![v 0, v 1] = v from List.ofFn_inj.mp rfl])
  exact hp.prod

lemma Lsum5_eq_tsum_row (z : ℍ) : Lsum5 W z = ∑' m : ℤ, row z m := by
  have hs := summable_Lsum5 (w := W) norm_W_le z
  rw [Lsum5, ← (finTwoArrowEquiv ℤ).symm.tsum_eq]
  have hp : Summable fun p : ℤ × ℤ => W ![p.1, p.2] * eisSummand 5 ![p.1, p.2] z :=
    (finTwoArrowEquiv ℤ).summable_iff.mp (hs.congr fun v => by
      simp [show ![v 0, v 1] = v from List.ofFn_inj.mp rfl])
  simp only [finTwoArrowEquiv_symm_apply]
  rw [Summable.tsum_prod hp]
  rfl

lemma tsum_row_eq (z : ℍ) : ∑' m : ℤ, row z m = kappa + 2 * ∑' n : ℕ, row z (n + 1) := by
  have hr := summable_rows z
  have h1 : Summable fun n : ℕ => row z (n + 1) :=
    hr.comp_injective (i := fun n : ℕ => ((n : ℤ) + 1)) fun a b h => by simp only at h; omega
  have h2 : Summable fun n : ℕ => row z (-(n + 1)) :=
    hr.comp_injective (i := fun n : ℕ => -((n : ℤ) + 1)) fun a b h => by simp only at h; omega
  rw [tsum_of_add_one_of_neg_add_one h1 h2, row_zero]
  have : ∀ n : ℕ, row z (-((n : ℤ) + 1)) = row z ((n : ℤ) + 1) := fun n => row_neg z _
  rw [tsum_congr this]
  ring

lemma tsum_row_succ (z : ℍ) : ∑' n : ℕ, row z (n + 1) =
    ∑' k : ℕ, row z (2 * (k : ℤ) + 1) + ∑' k : ℕ, row z (2 * ((k : ℤ) + 1)) := by
  have hr := summable_rows z
  have h1 : Summable fun n : ℕ => row z (n + 1) :=
    hr.comp_injective (i := fun n : ℕ => ((n : ℤ) + 1)) fun a b h => by simp only at h; omega
  have he : Summable fun k : ℕ => row z (((2 * k : ℕ) : ℤ) + 1) :=
    h1.comp_injective (i := fun k : ℕ => 2 * k) fun a b h => by simp only at h; omega
  have ho : Summable fun k : ℕ => row z (((2 * k + 1 : ℕ) : ℤ) + 1) :=
    h1.comp_injective (i := fun k : ℕ => 2 * k + 1) fun a b h => by simp only at h; omega
  have := tsum_even_add_odd (f := fun n : ℕ => row z ((n : ℤ) + 1)) he ho
  rw [← this]
  have e1 : ∀ k : ℕ, row z (((2 * k : ℕ) : ℤ) + 1) = row z (2 * (k : ℤ) + 1) := fun k => by
    rw [show (((2 * k : ℕ) : ℤ) + 1) = 2 * (k : ℤ) + 1 by push_cast; ring]
  have e2 : ∀ k : ℕ, row z (((2 * k + 1 : ℕ) : ℤ) + 1) = row z (2 * ((k : ℤ) + 1)) := fun k => by
    rw [show (((2 * k + 1 : ℕ) : ℤ) + 1) = 2 * ((k : ℤ) + 1) by push_cast; ring]
  rw [tsum_congr e1, tsum_congr e2]

/-- **The `q`-expansion of `L_W`.**
`L_W(τ) = κ + (π⁵/12) B(q) + (π⁵/192) A(q)`, `q = e^{πiτ}`. -/
theorem Lsum5_W_eq (z : ℍ) :
    Lsum5 W z =
      kappa + π ^ 5 / 12 * seriesB (cexp (π * I * z)) + π ^ 5 / 192 * seriesA (cexp (π * I * z)) := by
  rw [Lsum5_eq_tsum_row, tsum_row_eq, tsum_row_succ]
  simp only [row_odd, row_even]
  rw [tsum_mul_left, seriesA, seriesB]
  have : ∀ k : ℕ, π ^ 5 / 24 * chiZ (2 * (k : ℤ) + 1) *
      ∑' r : ℕ, (r : ℂ) ^ 4 * cexp (π * I * z) ^ (r * (2 * k + 1)) =
      π ^ 5 / 24 * (chiZ (2 * (k : ℤ) + 1) *
      ∑' r : ℕ, (r : ℂ) ^ 4 * cexp (π * I * z) ^ (r * (2 * k + 1))) := fun k => by ring
  rw [tsum_congr this, tsum_mul_left]
  ring

/-! ### Summability of the terms of `B` -/

/-- `K₄ = ∑_r r⁴ 2⁻ʳ`. -/
def K4 : ℝ := ∑' r : ℕ, (r : ℝ) ^ 4 * (1 / 2) ^ r

lemma hasSum_K4 : HasSum (fun r : ℕ => (r : ℝ) ^ 4 * (1 / 2) ^ r) K4 :=
  (summable_pow_mul_geometric_of_norm_lt_one 4 (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).hasSum

lemma pow_le_aux5 {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1 / 2) {r k a : ℕ} (hr : 1 ≤ r)
    (ha : k + 1 ≤ a) : ρ ^ (r * a) ≤ 2 * ρ * (1 / 2) ^ k * (1 / 2) ^ r := by
  have hρ1 : ρ ≤ 1 := by linarith
  have e : r + k ≤ r * a := by nlinarith
  obtain ⟨s, hs⟩ : ∃ s, r + k = s + 1 := ⟨r + k - 1, by omega⟩
  calc ρ ^ (r * a) ≤ ρ ^ (r + k) := pow_le_pow_of_le_one h0 hρ1 e
    _ = ρ * ρ ^ s := by rw [hs, pow_succ']
    _ ≤ ρ * (1 / 2) ^ s := by gcongr
    _ = 2 * ρ * (1 / 2) ^ (r + k) := by rw [hs, pow_succ]; ring
    _ = 2 * ρ * (1 / 2) ^ k * (1 / 2) ^ r := by rw [pow_add]; ring

lemma norm_inner5_le {q : ℂ} (hq : ‖q‖ ≤ 1 / 2) {k a : ℕ} (ha : k + 1 ≤ a) :
    ‖∑' r : ℕ, (r : ℂ) ^ 4 * q ^ (r * a)‖ ≤ 2 * ‖q‖ * (1 / 2) ^ k * K4 := by
  refine tsum_of_norm_bounded (hasSum_K4.mul_left (2 * ‖q‖ * (1 / 2) ^ k)) fun r => ?_
  rw [norm_mul, norm_pow, norm_pow, Complex.norm_natCast]
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  · have := pow_le_aux5 (norm_nonneg q) hq hr ha
    calc (r : ℝ) ^ 4 * ‖q‖ ^ (r * a) ≤ (r : ℝ) ^ 4 * (2 * ‖q‖ * (1 / 2) ^ k * (1 / 2) ^ r) := by
          gcongr
      _ = _ := by ring

lemma hasSum_outer5 (q : ℂ) :
    HasSum (fun k : ℕ => 2 * ‖q‖ * (1 / 2) ^ k * K4) (4 * K4 * ‖q‖) := by
  have := (hasSum_geometric_two.mul_left (2 * ‖q‖)).mul_right K4
  convert this using 1; ring

lemma norm_seriesB_term_le {q : ℂ} (hq : ‖q‖ ≤ 1 / 2) (k : ℕ) :
    ‖chiZ (2 * k + 1) * ∑' r : ℕ, (r : ℂ) ^ 4 * q ^ (r * (2 * k + 1))‖ ≤
      2 * ‖q‖ * (1 / 2) ^ k * K4 := by
  rw [norm_mul]
  have h := norm_inner5_le hq (k := k) (a := 2 * k + 1) (by omega)
  calc ‖chiZ (2 * k + 1)‖ * _ ≤ 1 * (2 * ‖q‖ * (1 / 2) ^ k * K4) := by
        gcongr
        · exact norm_chiZ_le _
    _ = _ := one_mul _

lemma summable_seriesB_terms {q : ℂ} (hq : ‖q‖ ≤ 1 / 2) :
    Summable fun k : ℕ => chiZ (2 * k + 1) * ∑' r : ℕ, (r : ℂ) ^ 4 * q ^ (r * (2 * k + 1)) :=
  Summable.of_norm_bounded (hasSum_outer5 q).summable (norm_seriesB_term_le hq)

end NTKB.HardyWright.TenSquares
