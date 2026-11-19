/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TwentyLattice
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.SixExpansion

/-!
# The `q`-expansion of the weight-`10` lattice sum `L_W`

With `q = e^{πiτ}`, `κ = ∑_{n odd} n⁻¹⁰` (the row `m = 0`),
`O(q) = ∑_{k ≥ 0} ∑_r r⁹ q^{r(2k+1)}` and `E(q) = ∑_{k ≥ 0} ∑_r (-1)^r r⁹ q^{2r(k+1)}`:

`L_W(τ) = κ + (π¹⁰/60) (O(q) - E(q))`   (`Lsum10_W_eq`).

Each row `∑_n W(m, n)(mτ + n)⁻¹⁰` (`m ≥ 1`) is split into the residue classes of `n` modulo `2`
and evaluated by the Lipschitz formula `∑_n (z + n)⁻¹⁰ = -(8π¹⁰/15) ∑_r r⁹ e^{2πirz}` (Mathlib's
`EisensteinSeries.qExpansion_identity`); the rows `-m` and `m` agree.
-/

open ModularForm ModularGroup Complex Filter Topology EisensteinSeries Matrix
open scoped MatrixGroups Real UpperHalfPlane Manifold
open UpperHalfPlane hiding I

noncomputable section

namespace NTKB.HardyWright.TwentySquares

open SixSquares (tsum_int_split norm_cexp_pi_I_lt_one)

/-! ### The Lipschitz formula in weight `10` -/

lemma lip10 (z : ℍ) : ∑' n : ℤ, 1 / ((z : ℂ) + n) ^ 10 =
    -(8 * π ^ 10 / 2835) * ∑' n : ℕ, (n : ℂ) ^ 9 * cexp (2 * π * I * z) ^ n := by
  have h := EisensteinSeries.qExpansion_identity (k := 9) (by norm_num) z
  rw [show (9 + 1 : ℕ) = 10 from rfl] at h
  rw [h]
  congr 1
  rw [show ((Nat.factorial 9 : ℕ) : ℂ) = 362880 by norm_num [Nat.factorial]]
  have : (-2 * (π : ℂ) * I) ^ 10 = -(1024 * π ^ 10) := by
    have e : (-2 * (π : ℂ) * I) ^ 10 = 1024 * π ^ 10 * (I ^ 2) ^ 5 := by ring
    rw [e, I_sq]; ring
  rw [this]; ring

lemma lip10' (w : ℂ) (hw : 0 < w.im) : ∑' n : ℤ, 1 / (w + n) ^ 10 =
    -(8 * π ^ 10 / 2835) * ∑' n : ℕ, (n : ℂ) ^ 9 * cexp (2 * π * I * w) ^ n :=
  lip10 ⟨w, hw⟩

/-- A residue class: `∑_j (c + jN + b)⁻¹⁰ = (-(8π¹⁰/15) / N¹⁰) ∑_r r⁹ e^{2πir(c+b)/N}`. -/
lemma class_sum10 (c : ℂ) (hc : 0 < c.im) (N : ℕ) (hN : 0 < N) (b : ℤ) :
    ∑' j : ℤ, 1 / (c + (j * N + b)) ^ 10 =
      -(8 * π ^ 10 / 2835) / (N : ℂ) ^ 10 *
        ∑' r : ℕ, (r : ℂ) ^ 9 * cexp (2 * π * I * ((c + b) / N)) ^ r := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hw : 0 < ((c + b) / N).im := by
    have : ((c + b) / (N : ℂ)).im = c.im / N := by
      rw [show (N : ℂ) = ((N : ℝ) : ℂ) by push_cast; rfl, Complex.div_ofReal_im]; simp
    rw [this]; exact div_pos hc (by exact_mod_cast hN)
  have e : ∀ j : ℤ, 1 / (c + (j * N + b)) ^ 10 = 1 / (N : ℂ) ^ 10 * (1 / ((c + b) / N + j) ^ 10) := by
    intro j
    rw [show (c + b) / N + j = (c + (j * N + b)) / N by field_simp; ring, div_pow]
    field_simp
  simp_rw [e]
  rw [tsum_mul_left, lip10' _ hw]
  ring

/-! ### Rows -/

/-- The row `m` of `L_W`. -/
def row (z : ℍ) (m : ℤ) : ℂ := ∑' n : ℤ, W ![m, n] * eisSummand 10 ![m, n] z

lemma eisSummand_ten (m n : ℤ) (z : ℍ) :
    eisSummand 10 ![m, n] z = 1 / ((m : ℂ) * z + n) ^ 10 := by
  simp only [eisSummand, cons_val_zero, cons_val_one]
  rw [_root_.zpow_neg, one_div]
  norm_cast

lemma summable_row (z : ℍ) (m : ℤ) :
    Summable fun n : ℤ => W ![m, n] * eisSummand 10 ![m, n] z := by
  have hs := summable_Lsum10 (w := W) norm_W_le z
  exact hs.comp_injective (i := fun n : ℤ => ![m, n]) fun a b h => by
    simpa using congrFun h 1

lemma W_even_row (k : ℕ) (n : ℤ) : W ![2 * ((k : ℤ) + 1), n] = if Even n then 0 else 1 := by
  have h1 : Even (2 * ((k : ℤ) + 1)) := even_two_mul _
  by_cases hn : Even n <;> simp [W, h1, hn]

lemma W_odd_row (k : ℕ) (n : ℤ) : W ![2 * (k : ℤ) + 1, n] = -(if Even n then 1 else 0) := by
  have h1 : ¬ Even (2 * (k : ℤ) + 1) := Int.not_even_iff_odd.mpr (odd_two_mul_add_one _)
  by_cases hn : Even n <;> simp [W, h1, hn]

lemma W_neg (v : Fin 2 → ℤ) : W (-v) = W v := by
  simp only [W, Pi.neg_apply, even_neg]

lemma eisSummand_neg10 (v : Fin 2 → ℤ) (z : ℍ) : eisSummand 10 (-v) z = eisSummand 10 v z := by
  simp only [eisSummand, Pi.neg_apply, Int.cast_neg]
  rw [show -((v 0 : ℂ)) * z + -(v 1 : ℂ) = -((v 0 : ℂ) * z + v 1) by ring]
  exact Even.neg_zpow ⟨-5, by norm_num⟩ _

lemma row_neg (z : ℍ) (m : ℤ) : row z (-m) = row z m := by
  rw [row, row, ← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun n => ?_
  simp only [Equiv.neg_apply]
  have h : (![-m, -n] : Fin 2 → ℤ) = -![m, n] := by
    ext i; fin_cases i <;> simp
  rw [h, W_neg, eisSummand_neg10]

/-- The row `0`: `κ = ∑_{n odd} n⁻¹⁰`. -/
def kappa : ℂ := ∑' n : ℤ, (if Even n then 0 else 1) * (1 / (n : ℂ) ^ 10)

lemma row_zero (z : ℍ) : row z 0 = kappa := by
  rw [row, kappa]
  refine tsum_congr fun n => ?_
  rw [eisSummand_ten]
  have h0 : Even (0 : ℤ) := ⟨0, rfl⟩
  by_cases hn : Even n <;> simp [W, h0, hn]

/-- The even row `m = 2(k+1)`. -/
lemma row_even (z : ℍ) (k : ℕ) : row z (2 * ((k : ℤ) + 1)) =
    -(π ^ 10 / 362880) * ∑' r : ℕ, (-1) ^ r * (r : ℂ) ^ 9 * cexp (π * I * z) ^ (r * (2 * (k + 1))) := by
  set m : ℤ := 2 * ((k : ℤ) + 1) with hm
  have hmc : ((m : ℤ) : ℂ) = 2 * ((k : ℂ) + 1) := by rw [hm]; push_cast; ring
  have hc : 0 < ((m : ℂ) * z).im := by
    rw [hmc]
    have : ((2 * ((k : ℂ) + 1)) * (z : ℂ)).im = (2 * ((k : ℝ) + 1)) * z.im := by
      simp [Complex.mul_im]
    rw [this]; exact mul_pos (by positivity) z.im_pos
  rw [row, tsum_int_split 2 (summable_row z m)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp only [hm, W_even_row, eisSummand_ten]
  push_cast
  have hev : ∀ j : ℤ, Even (j * 2) := fun j => ⟨j, by ring⟩
  have hod : ∀ j : ℤ, ¬ Even (j * 2 + 1) := fun j =>
    Int.not_even_iff_odd.mpr ⟨j, by ring⟩
  simp only [add_zero, hev, hod, ite_true, ite_false, zero_mul, tsum_zero, zero_add, one_mul]
  have h1 := class_sum10 _ hc 2 (by norm_num) 1
  push_cast at h1
  rw [hmc] at h1
  rw [h1]
  set q := cexp (π * I * z) with hq
  have e1 : cexp (2 * π * I * ((2 * ((k : ℂ) + 1) * z + 1) / 2)) = -q ^ (2 * (k + 1)) := by
    rw [hq, ← Complex.exp_nat_mul, show 2 * π * I * ((2 * ((k : ℂ) + 1) * z + 1) / 2) =
      π * I + ((2 * (k + 1) : ℕ) : ℂ) * (π * I * z) by push_cast; ring, Complex.exp_add,
      Complex.exp_pi_mul_I]
    ring
  rw [e1, show (2 : ℂ) ^ 10 = 1024 by norm_num, ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun r => ?_
  rw [neg_pow, ← pow_mul, mul_comm (2 * (k + 1)) r]
  ring

/-- The odd row `m = 2k + 1`. -/
lemma row_odd (z : ℍ) (k : ℕ) : row z (2 * (k : ℤ) + 1) =
    π ^ 10 / 362880 * ∑' r : ℕ, (r : ℂ) ^ 9 * cexp (π * I * z) ^ (r * (2 * k + 1)) := by
  set m : ℤ := 2 * (k : ℤ) + 1 with hm
  have hmc : ((m : ℤ) : ℂ) = 2 * (k : ℂ) + 1 := by rw [hm]; push_cast; ring
  have hc : 0 < ((m : ℂ) * z).im := by
    rw [hmc]
    have : ((2 * (k : ℂ) + 1) * (z : ℂ)).im = (2 * (k : ℝ) + 1) * z.im := by
      simp [Complex.mul_im]
    rw [this]; exact mul_pos (by positivity) z.im_pos
  rw [row, tsum_int_split 2 (summable_row z m)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp only [hm, W_odd_row, eisSummand_ten]
  push_cast
  have hev : ∀ j : ℤ, Even (j * 2) := fun j => ⟨j, by ring⟩
  have hod : ∀ j : ℤ, ¬ Even (j * 2 + 1) := fun j =>
    Int.not_even_iff_odd.mpr ⟨j, by ring⟩
  simp only [add_zero, hev, hod, ite_true, ite_false, neg_zero, zero_mul, tsum_zero, neg_mul,
    one_mul, tsum_neg]
  have h0 := class_sum10 _ hc 2 (by norm_num) 0
  push_cast at h0
  simp only [add_zero] at h0
  rw [hmc] at h0
  rw [h0]
  set q := cexp (π * I * z) with hq
  have e0 : cexp (2 * π * I * ((2 * (k : ℂ) + 1) * z / 2)) = q ^ (2 * k + 1) := by
    rw [hq, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  rw [e0, show (2 : ℂ) ^ 10 = 1024 by norm_num]
  simp_rw [← pow_mul, show ∀ r : ℕ, (2 * k + 1) * r = r * (2 * k + 1) from fun r => by ring]
  ring

/-! ### The expansion -/

/-- `O(q) = ∑_{k ≥ 0} ∑_r r⁹ q^{r(2k+1)}`.
  **Restriction:** the series is the mathematical object only where it converges (absolutely, for $|q| < 1$);
  elsewhere the value is $0$ by Lean's `tsum` convention, not an analytic continuation or the intended value. -/
def seriesO (q : ℂ) : ℂ := ∑' k : ℕ, ∑' r : ℕ, (r : ℂ) ^ 9 * q ^ (r * (2 * k + 1))

/-- `E(q) = ∑_{k ≥ 0} ∑_r (-1)^r r⁹ q^{2r(k+1)}`. -/
def seriesE (q : ℂ) : ℂ := ∑' k : ℕ, ∑' r : ℕ, (-1) ^ r * (r : ℂ) ^ 9 * q ^ (r * (2 * (k + 1)))

lemma summable_pairs (z : ℍ) :
    Summable fun p : ℤ × ℤ => W ![p.1, p.2] * eisSummand 10 ![p.1, p.2] z := by
  have hs := summable_Lsum10 (w := W) norm_W_le z
  exact (finTwoArrowEquiv ℤ).summable_iff.mp (hs.congr fun v => by
    simp [show ![v 0, v 1] = v from List.ofFn_inj.mp rfl])

lemma summable_rows (z : ℍ) : Summable (row z) := (summable_pairs z).prod

lemma Lsum10_eq_tsum_row (z : ℍ) : Lsum10 W z = ∑' m : ℤ, row z m := by
  rw [Lsum10, ← (finTwoArrowEquiv ℤ).symm.tsum_eq]
  simp only [finTwoArrowEquiv_symm_apply]
  rw [Summable.tsum_prod (summable_pairs z)]
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

/-- **The `q`-expansion of `L_W`.** `L_W(τ) = κ + (π¹⁰/60)(O(q) - E(q))`, `q = e^{πiτ}`. -/
theorem Lsum10_W_eq (z : ℍ) :
    Lsum10 W z = kappa + π ^ 10 / 181440 *
      (seriesO (cexp (π * I * z)) - seriesE (cexp (π * I * z))) := by
  rw [Lsum10_eq_tsum_row, tsum_row_eq, tsum_row_succ]
  simp only [row_odd, row_even]
  rw [tsum_mul_left, tsum_mul_left, seriesO, seriesE]
  ring

end NTKB.HardyWright.TwentySquares
