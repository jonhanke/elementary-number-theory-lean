/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.ArithmeticFunctions.SumTwoSquares
import NTKB.Elementary.HardyWright.ArithmeticFunctions.Squarefree
import Mathlib.Computability.Reduce
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Hardy–Wright, § 18.7: lattice points in a disc and in a ball

* Theorem 339 (Gauss): `r(1) + ⋯ + r(n) = π n + O(√n)`; the average order of `r(n)` is `π`.
* Theorem 340: `r₃(1) + ⋯ + r₃(n) = (4/3) π n^{3/2} + O(n)`.

Proof as in the book: attach to each lattice point `z` with `|z|² ≤ n` the unit cube with `z` as
its "south-west corner"; the union of these cubes contains the ball of radius `√n - √k` and is
contained in the ball of radius `√n + √k` (`k` the dimension), and its volume is the number of
lattice points.
-/

open Finset MeasureTheory Metric Filter Topology Asymptotics

namespace NTKB.HardyWright

variable {k : ℕ}

/-- The lattice points `z ∈ ℤ^k` with `z₁² + ⋯ + z_k² ≤ n`. -/
def latticePoints (k n : ℕ) : Finset (Fin k → ℤ) :=
  (Fintype.piFinset fun _ => Icc (-(n : ℤ)) n).filter fun z => ∑ i, z i ^ 2 ≤ n

lemma abs_le_of_sq_le {a : ℤ} {n : ℕ} (h : a ^ 2 ≤ n) : |a| ≤ n := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have : |a| ≤ a ^ 2 := by
    rw [sq, ← abs_mul_abs_self]; exact le_mul_of_one_le_left (abs_nonneg _) (Int.one_le_abs ha)
  linarith

lemma mem_latticePoints {n : ℕ} {z : Fin k → ℤ} :
    z ∈ latticePoints k n ↔ ∑ i, z i ^ 2 ≤ n := by
  simp only [latticePoints, mem_filter, Fintype.mem_piFinset, mem_Icc, and_iff_right_iff_imp]
  intro h i
  have : z i ^ 2 ≤ n := le_trans (single_le_sum (f := fun i => z i ^ 2)
    (fun j _ => sq_nonneg (z j)) (mem_univ i)) h
  exact abs_le.mp (abs_le_of_sq_le this)

/-- The unit cube with south-west corner `z`. -/
def unitCube (z : Fin k → ℤ) : Set (EuclideanSpace ℝ (Fin k)) :=
  WithLp.ofLp ⁻¹' Set.univ.pi fun i => Set.Ico (z i : ℝ) (z i + 1)

lemma measurableSet_unitCube (z : Fin k → ℤ) : MeasurableSet (unitCube z) :=
  (MeasurableSet.univ_pi fun _ => measurableSet_Ico).preimage (WithLp.measurable_ofLp 2 _)

lemma volume_unitCube (z : Fin k → ℤ) : volume (unitCube z) = 1 := by
  rw [unitCube, (PiLp.volume_preserving_ofLp (Fin k)).measure_preimage
    (MeasurableSet.univ_pi fun _ => measurableSet_Ico).nullMeasurableSet, Real.volume_pi_Ico]
  simp

lemma mem_unitCube {z : Fin k → ℤ} {y : EuclideanSpace ℝ (Fin k)} :
    y ∈ unitCube z ↔ ∀ i, (z i : ℝ) ≤ y i ∧ y i < z i + 1 := by
  simp [unitCube, Set.mem_pi]

lemma unitCube_disjoint {z w : Fin k → ℤ} (h : z ≠ w) : Disjoint (unitCube z) (unitCube w) := by
  rw [Set.disjoint_left]
  intro y hz hw
  apply h
  funext i
  obtain ⟨h1, h2⟩ := mem_unitCube.mp hz i
  obtain ⟨h3, h4⟩ := mem_unitCube.mp hw i
  have e1 : ⌊y i⌋ = z i := Int.floor_eq_iff.mpr ⟨h1, h2⟩
  have e2 : ⌊y i⌋ = w i := Int.floor_eq_iff.mpr ⟨h3, h4⟩
  rw [← e1, e2]

/-- The volume of the union of the cubes is the number of lattice points. -/
lemma volume_iUnion_unitCube (n : ℕ) :
    volume (⋃ z ∈ latticePoints k n, unitCube z) = #(latticePoints k n) := by
  rw [measure_biUnion_finset (fun z _ w _ h => unitCube_disjoint h)
    (fun z _ => measurableSet_unitCube z)]
  simp [volume_unitCube]

/-- The point `z` of `ℤ^k` as a point of Euclidean space. -/
def latticeVec (z : Fin k → ℤ) : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 fun i => (z i : ℝ)

lemma norm_latticeVec (z : Fin k → ℤ) : ‖latticeVec z‖ = √(∑ i, ((z i : ℝ)) ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  simp [latticeVec, Real.norm_eq_abs, sq_abs]

lemma norm_sub_latticeVec_le {z : Fin k → ℤ} {y : EuclideanSpace ℝ (Fin k)}
    (hy : y ∈ unitCube z) : ‖y - latticeVec z‖ ≤ √k := by
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  calc ∑ i, ‖(y - latticeVec z).ofLp i‖ ^ 2 ≤ ∑ _i : Fin k, (1 : ℝ) := by
        refine sum_le_sum fun i _ => ?_
        obtain ⟨h1, h2⟩ := mem_unitCube.mp hy i
        simp only [latticeVec, WithLp.ofLp_sub, Pi.sub_apply, Real.norm_eq_abs, sq_abs]
        have : 0 ≤ y i - z i := by linarith
        have : y i - z i < 1 := by linarith
        nlinarith
    _ = k := by simp

/-- The union of the cubes lies in the closed ball of radius `√n + √k`. -/
lemma iUnion_unitCube_subset (n : ℕ) :
    (⋃ z ∈ latticePoints k n, unitCube z) ⊆ closedBall 0 (√n + √k) := by
  intro y hy
  simp only [Set.mem_iUnion] at hy
  obtain ⟨z, hz, hyz⟩ := hy
  rw [mem_closedBall, dist_zero_right]
  have h1 : ‖latticeVec z‖ ≤ √n := by
    rw [norm_latticeVec]
    apply Real.sqrt_le_sqrt
    have := mem_latticePoints.mp hz
    exact_mod_cast this
  calc ‖y‖ = ‖latticeVec z + (y - latticeVec z)‖ := by rw [add_sub_cancel]
    _ ≤ ‖latticeVec z‖ + ‖y - latticeVec z‖ := norm_add_le _ _
    _ ≤ √n + √k := add_le_add h1 (norm_sub_latticeVec_le hyz)

/-- The ball of radius `√n - √k` lies in the union of the cubes. -/
lemma ball_subset_iUnion_unitCube (n : ℕ) :
    ball 0 (√n - √k) ⊆ ⋃ z ∈ latticePoints k n, unitCube z := by
  intro y hy
  rw [mem_ball, dist_zero_right] at hy
  set z : Fin k → ℤ := fun i => ⌊y i⌋ with hzdef
  have hyz : y ∈ unitCube z := mem_unitCube.mpr fun i => ⟨Int.floor_le _, Int.lt_floor_add_one _⟩
  simp only [Set.mem_iUnion]
  refine ⟨z, ?_, hyz⟩
  rw [mem_latticePoints]
  have h1 : ‖latticeVec z‖ < √n := by
    calc ‖latticeVec z‖ = ‖y - (y - latticeVec z)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖y‖ + ‖y - latticeVec z‖ := norm_sub_le _ _
      _ < (√n - √k) + √k := add_lt_add_of_lt_of_le hy (norm_sub_latticeVec_le hyz)
      _ = √n := by ring
  rw [norm_latticeVec] at h1
  have h2 : ∑ i, ((z i : ℝ)) ^ 2 < n := by
    have := (Real.sqrt_lt_sqrt_iff (sum_nonneg fun i _ => sq_nonneg _)).mp h1
    exact this
  have h3 : ((∑ i, z i ^ 2 : ℤ) : ℝ) < n := by push_cast; exact h2
  have : ∑ i, z i ^ 2 < n := by exact_mod_cast h3
  omega

lemma volume_ball_le_card (n : ℕ) :
    volume (ball (0 : EuclideanSpace ℝ (Fin k)) (√n - √k)) ≤ #(latticePoints k n) := by
  rw [← volume_iUnion_unitCube]; exact measure_mono (ball_subset_iUnion_unitCube n)

lemma card_le_volume_closedBall (n : ℕ) :
    (#(latticePoints k n) : ENNReal) ≤ volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) (√n + √k)) := by
  rw [← volume_iUnion_unitCube]; exact measure_mono (iUnion_unitCube_subset n)

/-- `r_k(m)`: the number of `z ∈ ℤ^k` with `z₁² + ⋯ + z_k² = m`. -/
noncomputable def sumSquaresCount (k m : ℕ) : ℕ := {z : Fin k → ℤ | ∑ i, z i ^ 2 = m}.ncard

lemma card_latticePoints_eq_sum (k n : ℕ) :
    #(latticePoints k n) = ∑ m ∈ range (n + 1), sumSquaresCount k m := by
  rw [card_eq_sum_card_fiberwise (f := fun z => (∑ i, z i ^ 2).toNat) (t := range (n + 1))]
  · refine sum_congr rfl fun m hm => ?_
    rw [sumSquaresCount, ← Set.ncard_coe_finset]
    congr 1
    ext z
    simp only [coe_filter, mem_latticePoints, Set.mem_ofPred_eq]
    have h0 : 0 ≤ ∑ i, z i ^ 2 := sum_nonneg fun i _ => sq_nonneg _
    have hm' := mem_range.mp hm
    constructor
    · rintro ⟨_, h⟩; omega
    · intro h; omega
  · intro z hz
    have := mem_latticePoints.mp hz
    have h0 : 0 ≤ ∑ i, z i ^ 2 := sum_nonneg fun i _ => sq_nonneg _
    simp only [coe_range, Set.mem_Iio]
    omega

lemma sumSquaresCount_two (m : ℕ) : sumSquaresCount 2 m = sumTwoSquaresCount m := by
  rw [sumSquaresCount, sumTwoSquaresCount,
    ← Set.ncard_image_of_injective _ (piFinTwoEquiv fun _ => ℤ).injective]
  congr 1
  ext ⟨a, b⟩
  simp only [Set.mem_image, Set.mem_ofPred_eq, piFinTwoEquiv_apply, Prod.mk.injEq]
  constructor
  · rintro ⟨z, hz, rfl, rfl⟩
    rw [← hz, Fin.sum_univ_two]
  · intro h
    refine ⟨![a, b], ?_, rfl, rfl⟩
    rw [Fin.sum_univ_two]; simpa using h

lemma sumSquaresCount_zero (k : ℕ) : sumSquaresCount k 0 = 1 := by
  have : {z : Fin k → ℤ | ∑ i, z i ^ 2 = ((0 : ℕ) : ℤ)} = {0} := by
    ext z
    simp only [Set.mem_ofPred_eq, Nat.cast_zero, Set.mem_singleton_iff]
    rw [sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (z i)]
    simp only [mem_univ, true_implies, pow_eq_zero_iff two_ne_zero.symm.symm]
    exact ⟨fun h => funext h, fun h i => by rw [h]; rfl⟩
  rw [sumSquaresCount, this, Set.ncard_singleton]

lemma sum_range_succ_eq_add_sum_Ioc (f : ℕ → ℝ) (n : ℕ) :
    ∑ m ∈ range (n + 1), f m = f 0 + ∑ m ∈ Ioc 0 n, f m := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih, sum_Ioc_succ_top (by omega)]; ring

/-- `∑_{1 ≤ m ≤ n} r_k(m) = #(lattice points) - 1`. -/
lemma sum_sumSquaresCount_eq (k n : ℕ) :
    ∑ m ∈ Ioc 0 n, (sumSquaresCount k m : ℝ) = #(latticePoints k n) - 1 := by
  rw [card_latticePoints_eq_sum, Nat.cast_sum, sum_range_succ_eq_add_sum_Ioc, sumSquaresCount_zero]
  push_cast; ring

lemma real_bounds_of_volume {c r₁ r₂ : ℝ} {N : ℕ} {d : ℕ} (hc : 0 ≤ c) (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂)
    (h1 : ENNReal.ofReal r₁ ^ d * ENNReal.ofReal c ≤ N)
    (h2 : (N : ENNReal) ≤ ENNReal.ofReal r₂ ^ d * ENNReal.ofReal c) :
    r₁ ^ d * c ≤ N ∧ (N : ℝ) ≤ r₂ ^ d * c := by
  rw [← ENNReal.ofReal_pow hr₁, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_natCast,
    ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg _)] at h1
  rw [← ENNReal.ofReal_pow hr₂, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_natCast,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
  exact ⟨h1, h2⟩

/-- **Theorem 339** (Gauss; Hardy–Wright). `r(1) + r(2) + ⋯ + r(n) = π n + O(√n)`. -/
@[kb "hardywright2008" "Thm 339, p. 376"]
theorem sum_sumTwoSquaresCount_sub_isBigO :
    (fun n : ℕ => ∑ m ∈ Ioc 0 n, (sumTwoSquaresCount m : ℝ) - Real.pi * n) =O[atTop]
      fun n => √(n : ℝ) := by
  refine Asymptotics.IsBigO.of_bound 20 ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  simp only [← sumSquaresCount_two]
  rw [sum_sumSquaresCount_eq, Real.norm_eq_abs, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hs2 : √2 ≤ √(n : ℝ) := Real.sqrt_le_sqrt hn'
  have hv1 := volume_ball_le_card (k := 2) n
  have hv2 := card_le_volume_closedBall (k := 2) n
  rw [EuclideanSpace.volume_ball_fin_two, Nat.cast_ofNat] at hv1
  rw [EuclideanSpace.volume_closedBall_fin_two, Nat.cast_ofNat] at hv2
  obtain ⟨h1, h2⟩ := real_bounds_of_volume (r₁ := √n - √2) (r₂ := √n + √2) Real.pi_pos.le
    (sub_nonneg.mpr hs2) (by positivity) hv1 hv2
  set s := √(n : ℝ)
  have hs : s ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  have ht : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have ht2 : √2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hpi := Real.pi_lt_d2
  have hs1 : 1 ≤ s := by rw [Real.one_le_sqrt]; linarith
  have e1 : (s - √2) ^ 2 * Real.pi = Real.pi * n - 2 * (√2 * Real.pi) * s + 2 * Real.pi := by
    rw [← hs]; ring_nf; rw [ht]; ring
  have e2 : (s + √2) ^ 2 * Real.pi = Real.pi * n + 2 * (√2 * Real.pi) * s + 2 * Real.pi := by
    rw [← hs]; ring_nf; rw [ht]; ring
  have hq : √2 * Real.pi ≤ 5 := by nlinarith [Real.pi_pos, Real.sqrt_nonneg 2]
  have hq0 : 0 ≤ √2 * Real.pi := by positivity
  have hqs : (√2 * Real.pi) * s ≤ 5 * s := by nlinarith
  rw [abs_le]
  constructor <;> nlinarith [Real.pi_pos]

/-- **Theorem 339** (Hardy–Wright), first form: the average order of `r(n)` is `π`,
`(r(1) + ⋯ + r(n))/n → π`. -/
@[kb "hardywright2008" "Thm 339, p. 376"]
theorem tendsto_sum_sumTwoSquaresCount_div :
    Tendsto (fun n : ℕ => (∑ m ∈ Ioc 0 n, (sumTwoSquaresCount m : ℝ)) / n) atTop (𝓝 Real.pi) := by
  have h1 := sum_sumTwoSquaresCount_sub_isBigO
  have h2 : (fun n : ℕ => √(n : ℝ)) =o[atTop] fun n => (n : ℝ) := by
    exact isLittleO_sqrt_id.comp_tendsto tendsto_natCast_atTop_atTop
  have h3 := (h1.trans_isLittleO h2).tendsto_div_nhds_zero
  have h4 := h3.add (tendsto_const_nhds (x := Real.pi))
  rw [zero_add] at h4
  refine h4.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  ring

/-- **Theorem 340** (Hardy–Wright). With `r₃(m)` the number of integral solutions of
`x² + y² + z² = m` (here `(x, y, z)` written as `Fin 3 → ℤ`),
`r₃(1) + r₃(2) + ⋯ + r₃(n) = (4/3) π n^{3/2} + O(n)`. -/
@[kb "hardywright2008" "Thm 340, p. 376"]
theorem sum_sumSquaresCount_three_sub_isBigO :
    (fun n : ℕ => ∑ m ∈ Ioc 0 n, (sumSquaresCount 3 m : ℝ) - 4 / 3 * Real.pi * (n : ℝ) ^ ((3 : ℝ) / 2))
      =O[atTop] fun n => (n : ℝ) := by
  refine Asymptotics.IsBigO.of_bound 100 ?_
  filter_upwards [eventually_ge_atTop 3] with n hn
  rw [sum_sumSquaresCount_eq, Real.norm_eq_abs, Real.norm_of_nonneg (Nat.cast_nonneg _)]
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hs3 : √3 ≤ √(n : ℝ) := Real.sqrt_le_sqrt hn'
  have hv1 := volume_ball_le_card (k := 3) n
  have hv2 := card_le_volume_closedBall (k := 3) n
  rw [EuclideanSpace.volume_ball_fin_three, Nat.cast_ofNat] at hv1
  rw [EuclideanSpace.volume_closedBall_fin_three, Nat.cast_ofNat] at hv2
  obtain ⟨h1, h2⟩ := real_bounds_of_volume (r₁ := √n - √3) (r₂ := √n + √3) (by positivity)
    (sub_nonneg.mpr hs3) (by positivity) hv1 hv2
  have hpow : (n : ℝ) ^ ((3 : ℝ) / 2) = √(n : ℝ) ^ 3 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    norm_num
  rw [hpow]
  set s := √(n : ℝ)
  set c := Real.pi * 4 / 3 with hc
  have hs : s ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  have ht : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have ht2 : √3 < 7 / 4 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hpi := Real.pi_lt_d2
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 5 := by rw [hc]; linarith
  have hs1 : 1 ≤ s := by rw [Real.one_le_sqrt]; linarith
  have hsn : s ≤ n := by nlinarith
  have e1 : (s - √3) ^ 3 * c = c * s ^ 3 - 3 * (c * √3) * n + 9 * c * s - 3 * (c * √3) := by
    have : √3 ^ 3 = 3 * √3 := by rw [pow_succ, ht]
    rw [← hs]; ring_nf; rw [ht, this]; ring
  have e2 : (s + √3) ^ 3 * c = c * s ^ 3 + 3 * (c * √3) * n + 9 * c * s + 3 * (c * √3) := by
    have : √3 ^ 3 = 3 * √3 := by rw [pow_succ, ht]
    rw [← hs]; ring_nf; rw [ht, this]; ring
  have hq : c * √3 ≤ 9 := by nlinarith [Real.sqrt_nonneg 3]
  have hq0 : 0 ≤ c * √3 := by positivity
  have hqn : (c * √3) * n ≤ 9 * n := by nlinarith
  have hcs : c * s ≤ 5 * n := by nlinarith
  have h4 : 4 / 3 * Real.pi * s ^ 3 = c * s ^ 3 := by rw [hc]; ring
  rw [h4, abs_le]
  constructor <;> nlinarith

end NTKB.HardyWright
