/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.EightCount

/-!
# Hardy–Wright, § 20.13: the coefficients of `r₆`

Jacobi's formula for `r₆(n)` from an identity of generating functions with an unknown
constant `κ` (which is determined to be `π³/16` using `r₆(1) = 12`).
-/

open Finset Filter Topology

namespace NTKB.HardyWright

/-- The character `χ` modulo `4`, real valued, on natural numbers. -/
def chi4R (n : ℕ) : ℝ := ((ZMod.χ₄ (n : ZMod 4) : ℤ) : ℝ)

/-- `A(x) = ∑_{k ≥ 1} ∑_{r ≥ 0} χ(r) r² x^{rk}`. -/
noncomputable def sixSeriesA (x : ℝ) : ℝ :=
  ∑' k : ℕ, ∑' r : ℕ, chi4R r * (r : ℝ) ^ 2 * x ^ (r * (k + 1))

/-- `B(x) = ∑_{m ≥ 1} χ(m) ∑_{r ≥ 0} r² x^{rm}`. -/
noncomputable def sixSeriesB (x : ℝ) : ℝ :=
  ∑' m : ℕ, chi4R (m + 1) * ∑' r : ℕ, (r : ℝ) ^ 2 * x ^ (r * (m + 1))

lemma abs_chi4R_le (n : ℕ) : |chi4R n| ≤ 1 := by
  unfold chi4R
  rw [ZMod.χ₄_nat_eq_if_mod_four]
  split_ifs <;> simp

lemma chi4_cast_eq (n : ℕ) : ((chi4 n : ℤ) : ℂ) = (chi4R n : ℂ) := by
  simp [chi4R]

/-- The divisor-sum coefficient `∑_{d ∣ N} χ(d) d²`. -/
noncomputable def sixCoeffA (N : ℕ) : ℝ := ∑ d ∈ N.divisors, chi4R d * (d : ℝ) ^ 2

/-- The divisor-sum coefficient `∑_{d ∣ N} χ(N/d) d²`. -/
noncomputable def sixCoeffB (N : ℕ) : ℝ := ∑ d ∈ N.divisors, chi4R (N / d) * (d : ℝ) ^ 2

lemma summable_six_majorant {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    Summable fun p : ℕ × ℕ => (p.2 : ℝ) ^ 2 * x ^ (p.2 * (p.1 + 1)) := by
  have hM : Summable fun p : ℕ × ℕ => (p.1 : ℝ) ^ 2 * x ^ (p.1 * (p.2 + 1)) := by
    have hnn : ∀ p : ℕ × ℕ, 0 ≤ (p.1 : ℝ) ^ 2 * x ^ (p.1 * (p.2 + 1)) :=
      fun p => by positivity
    refine (summable_prod_of_nonneg hnn).2 ⟨fun r => ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos r with rfl | hr
      · simp
      · have hxr : x ^ r < 1 := pow_lt_one₀ hx0 hx hr.ne'
        refine ((summable_geometric_of_lt_one (pow_nonneg hx0 r) hxr).mul_left
          ((r : ℝ) ^ 2 * x ^ r)).congr fun k => ?_
        show _ = _
        rw [mul_add, mul_one, pow_add, pow_mul]; ring
    · have hb : Summable fun r : ℕ => (r : ℝ) ^ 2 * x ^ r * (1 - x)⁻¹ :=
        (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 (r := x)
          (by rw [Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx)).mul_right _
      have h1x : 0 < 1 - x := by linarith
      refine Summable.of_nonneg_of_le (fun r => tsum_nonneg fun k => hnn (r, k)) (fun r => ?_) hb
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · simp
      · have hxr : x ^ r < 1 := pow_lt_one₀ hx0 hx hr.ne'
        have hxr' : x ^ r ≤ x := pow_le_of_le_one hx0 hx.le hr.ne'
        have : ∑' k : ℕ, (r : ℝ) ^ 2 * x ^ (r * (k + 1)) =
            (r : ℝ) ^ 2 * x ^ r * (1 - x ^ r)⁻¹ := by
          rw [← tsum_geometric_of_lt_one (pow_nonneg hx0 r) hxr, ← tsum_mul_left]
          refine tsum_congr fun k => ?_
          rw [mul_add, mul_one, pow_add, pow_mul]; ring
        show ∑' k : ℕ, (r : ℝ) ^ 2 * x ^ (r * (k + 1)) ≤ _
        rw [this]
        exact mul_le_mul_of_nonneg_left (inv_anti₀ h1x (by linarith)) (by positivity)
  exact (Equiv.prodComm ℕ ℕ).summable_iff.mpr hM

/-- Rearrangement of a double series into a divisor sum. -/
lemma hasSum_divisor_rearr (G : ℕ → ℕ → ℝ) (hG0 : ∀ m, G 0 m = 0)
    (hs : Summable fun p : ℕ × ℕ => G p.2 (p.1 + 1)) :
    HasSum (fun N : ℕ => ∑ d ∈ N.divisors, G d (N / d)) (∑' k : ℕ, ∑' r : ℕ, G r (k + 1)) := by
  set ψ : ℕ × ℕ → ℕ := fun p => p.2 * (p.1 + 1) with hψ
  have hsig := (Equiv.sigmaFiberEquiv ψ).hasSum_iff.mpr hs.hasSum
  have htot : ∑' p : ℕ × ℕ, G p.2 (p.1 + 1) = ∑' k : ℕ, ∑' r : ℕ, G r (k + 1) :=
    hs.tsum_prod
  rw [← htot]
  refine hsig.sigma fun N => ?_
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have : ∀ c : {p : ℕ × ℕ // ψ p = 0}, G c.1.2 (c.1.1 + 1) = 0 := by
      intro c
      have h := c.2
      simp only [hψ] at h
      have : c.1.2 = 0 := by
        rcases Nat.mul_eq_zero.1 h with h | h
        · exact h
        · omega
      rw [this, hG0]
    simp only [Nat.divisors_zero, Finset.sum_empty]
    exact (hasSum_zero).congr_fun fun c => this c
  · set T : Finset (ℕ × ℕ) := (N.divisorsAntidiagonal).image (fun q : ℕ × ℕ => (q.2 - 1, q.1))
      with hT
    have hset : {p : ℕ × ℕ | ψ p = N} = (T : Set (ℕ × ℕ)) := by
      ext ⟨k, r⟩
      simp only [Set.mem_ofPred_eq, hT, Finset.coe_image, Set.mem_image, Finset.mem_coe,
        Nat.mem_divisorsAntidiagonal, Prod.exists, Prod.mk.injEq, hψ]
      constructor
      · intro h
        exact ⟨r, k + 1, ⟨h, hN.ne'⟩, by omega, rfl⟩
      · rintro ⟨a, b, ⟨h1, _⟩, h2, h3⟩
        subst h3
        have hb : 0 < b := by
          rcases Nat.eq_zero_or_pos b with rfl | hb
          · simp at h1; omega
          · exact hb
        rw [← h2]
        rw [Nat.sub_add_cancel hb]
        exact h1.symm ▸ by ring
    have hv : ∑ p ∈ T, G p.2 (p.1 + 1) = ∑ d ∈ N.divisors, G d (N / d) := by
      rw [hT, Finset.sum_image]
      · rw [← Nat.sum_divisorsAntidiagonal (fun a b => G a b)]
        refine Finset.sum_congr rfl fun q hq => ?_
        rw [Nat.mem_divisorsAntidiagonal] at hq
        have : 0 < q.2 := by
          rcases Nat.eq_zero_or_pos q.2 with h | h
          · rw [h, mul_zero] at hq; omega
          · exact h
        simp only
        rw [Nat.sub_add_cancel this]
      · intro q hq q' hq' h
        simp only [Finset.mem_coe, Nat.mem_divisorsAntidiagonal] at hq hq'
        simp only [Prod.mk.injEq] at h
        have h1 : 0 < q.2 := Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hq; omega
        have h2 : 0 < q'.2 := Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hq'; omega
        exact Prod.ext h.2 (by omega)
    rw [← hv]
    have key : HasSum (fun p : ℕ × ℕ => (T : Set (ℕ × ℕ)).indicator
        (fun p : ℕ × ℕ => G p.2 (p.1 + 1)) p) (∑ p ∈ T, G p.2 (p.1 + 1)) := by
      have : HasSum (fun p : ℕ × ℕ => (T : Set (ℕ × ℕ)).indicator
          (fun p : ℕ × ℕ => G p.2 (p.1 + 1)) p)
          (∑ p ∈ T, (T : Set (ℕ × ℕ)).indicator (fun p : ℕ × ℕ => G p.2 (p.1 + 1)) p) :=
        hasSum_sum_of_ne_finset_zero
          (fun p hp => Set.indicator_of_notMem (by simpa using hp) _)
      rwa [Finset.sum_congr rfl
        (fun p hp => Set.indicator_of_mem (Finset.mem_coe.2 hp) _)] at this
    rw [← hset] at key
    exact (hasSum_subtype_iff_indicator (s := {p : ℕ × ℕ | ψ p = N})
      (f := fun p : ℕ × ℕ => G p.2 (p.1 + 1))).2 key

lemma hasSum_sixCoeffA {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    HasSum (fun N : ℕ => sixCoeffA N * x ^ N) (sixSeriesA x) := by
  have hs : Summable fun p : ℕ × ℕ => chi4R p.2 * (p.2 : ℝ) ^ 2 * x ^ (p.2 * (p.1 + 1)) := by
    refine Summable.of_norm_bounded (summable_six_majorant hx0 hx) fun p => ?_
    have h2 : (0 : ℝ) ≤ (p.2 : ℝ) ^ 2 * x ^ (p.2 * (p.1 + 1)) := by positivity
    rw [Real.norm_eq_abs, mul_assoc, abs_mul, abs_of_nonneg h2]
    have := abs_chi4R_le p.2
    nlinarith
  have := hasSum_divisor_rearr (fun r m => chi4R r * (r : ℝ) ^ 2 * x ^ (r * m)) (by simp) hs
  refine this.congr_fun fun N => ?_
  unfold sixCoeffA
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]

lemma hasSum_sixCoeffB {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    HasSum (fun N : ℕ => sixCoeffB N * x ^ N) (sixSeriesB x) := by
  have hs : Summable fun p : ℕ × ℕ =>
      chi4R (p.1 + 1) * ((p.2 : ℝ) ^ 2 * x ^ (p.2 * (p.1 + 1))) := by
    refine Summable.of_norm_bounded (summable_six_majorant hx0 hx) fun p => ?_
    have h2 : (0 : ℝ) ≤ (p.2 : ℝ) ^ 2 * x ^ (p.2 * (p.1 + 1)) := by positivity
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2]
    have := abs_chi4R_le (p.1 + 1)
    nlinarith
  have := hasSum_divisor_rearr (fun r m => chi4R m * ((r : ℝ) ^ 2 * x ^ (r * m)))
    (by simp) hs
  have e : sixSeriesB x = ∑' k : ℕ, ∑' r : ℕ,
      chi4R (k + 1) * ((r : ℝ) ^ 2 * x ^ (r * (k + 1))) := by
    unfold sixSeriesB
    exact tsum_congr fun k => (tsum_mul_left).symm
  rw [e]
  refine this.congr_fun fun N => ?_
  unfold sixCoeffB
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
  ring

lemma sumSquaresCount_six_one : sumSquaresCount 6 1 = 12 := by
  have hset : {z : Fin 6 → ℤ | ∑ i, z i ^ 2 = ((1 : ℕ) : ℤ)} =
      ↑((Fintype.piFinset fun _ : Fin 6 => ({-1, 0, 1} : Finset ℤ)).filter
        (fun z : Fin 6 → ℤ => ∑ i, z i ^ 2 = 1)) := by
    ext z
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, Fintype.mem_piFinset, Nat.cast_one]
    constructor
    · intro h
      refine ⟨fun i => ?_, h⟩
      have : z i ^ 2 ≤ 1 := by
        rw [← h]
        exact Finset.single_le_sum (f := fun i => z i ^ 2) (fun j _ => by positivity)
          (Finset.mem_univ i)
      have h1 : -1 ≤ z i ∧ z i ≤ 1 := by constructor <;> nlinarith
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    · exact fun h => h.2
  rw [sumSquaresCount, hset, Set.ncard_coe_finset]
  decide +kernel

lemma six_coeff_eq_zero {κ : ℝ}
    (h : ∀ x : ℝ, 0 < x → x < 1 / 2 → κ * (∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 6 =
      κ - Real.pi ^ 3 / 4 * sixSeriesA x + Real.pi ^ 3 * sixSeriesB x) {N : ℕ} (hN : 0 < N) :
    κ * (sumSquaresCount 6 N : ℝ) + Real.pi ^ 3 / 4 * sixCoeffA N - Real.pi ^ 3 * sixCoeffB N = 0 := by
  set a : ℕ → ℝ := fun N => κ * (sumSquaresCount 6 N : ℝ) - (if N = 0 then κ else 0)
    + Real.pi ^ 3 / 4 * sixCoeffA N - Real.pi ^ 3 * sixCoeffB N with ha
  have hHA : ∀ x : ℝ, 0 ≤ x → x < 1 →
      HasSum (fun N : ℕ => a N * x ^ N)
        (κ * (∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 6 - κ + Real.pi ^ 3 / 4 * sixSeriesA x
          - Real.pi ^ 3 * sixSeriesB x) := by
    intro x hx0 hx
    have h3 : HasSum (fun N : ℕ => (if N = 0 then κ else 0) * x ^ N) κ := by
      have := hasSum_ite_eq (0 : ℕ) κ
      refine this.congr_fun fun N => ?_
      by_cases hN : N = 0 <;> simp [hN]
    have := ((((hasSum_sumSquaresCount 6 hx0 hx).mul_left κ).sub h3).add
      ((hasSum_sixCoeffA hx0 hx).mul_left (Real.pi ^ 3 / 4))).sub
      ((hasSum_sixCoeffB hx0 hx).mul_left (Real.pi ^ 3))
    refine this.congr_fun fun N => ?_
    simp only [ha]; ring
  have hzero : ∀ x : ℝ, 0 < x → x < 1 / 2 → ∑' N, a N * x ^ N = 0 := by
    intro x hx0 hx
    rw [(hHA x hx0.le (by linarith)).tsum_eq, h x hx0 hx]; ring
  have hs : Summable fun N => |a N| * (1 / 2 : ℝ) ^ N := by
    have := (hHA (1 / 2) (by norm_num) (by norm_num)).summable.abs
    refine this.congr fun N => ?_
    rw [abs_mul, abs_of_pos (show (0 : ℝ) < (1 / 2) ^ N by positivity)]
  have hn0 := eq_zero_of_tsum_pow_eq_zero hs hzero N
  simp only [ha, if_neg hN.ne'] at hn0
  linarith

lemma sixCoeffA_one : sixCoeffA 1 = 1 := by
  simp [sixCoeffA, chi4R]

lemma sixCoeffB_one : sixCoeffB 1 = 1 := by
  simp [sixCoeffB, chi4R]

lemma kappa_eq {κ : ℝ}
    (h : ∀ x : ℝ, 0 < x → x < 1 / 2 → κ * (∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 6 =
      κ - Real.pi ^ 3 / 4 * sixSeriesA x + Real.pi ^ 3 * sixSeriesB x) :
    κ = Real.pi ^ 3 / 16 := by
  have h1 := six_coeff_eq_zero h (N := 1) one_pos
  rw [sumSquaresCount_six_one, sixCoeffA_one, sixCoeffB_one] at h1
  push_cast at h1
  linarith

/-- **Jacobi's formula for `r₆`**, from an identity of generating functions with an unknown
constant `κ`. -/
theorem sumSquaresCount_six_eq_of_forall {κ : ℝ}
    (h : ∀ x : ℝ, 0 < x → x < 1 / 2 → κ * (∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 6 =
      κ - Real.pi ^ 3 / 4 * sixSeriesA x + Real.pi ^ 3 * sixSeriesB x)
    {n : ℕ} (hn : 0 < n) : (sumSquaresCount 6 n : ℂ) = jacobiSixSum n := by
  have hκ := kappa_eq h
  have h1 := six_coeff_eq_zero h hn
  rw [hκ] at h1
  have hp : 0 < Real.pi ^ 3 := by positivity
  have h2 : Real.pi ^ 3 * ((sumSquaresCount 6 n : ℝ) - (16 * sixCoeffB n - 4 * sixCoeffA n)) = 0 := by
    linear_combination 16 * h1
  have h3 : (sumSquaresCount 6 n : ℝ) = 16 * sixCoeffB n - 4 * sixCoeffA n := by
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h hp.ne'
    · linarith
  have h4 : (sumSquaresCount 6 n : ℂ) = ((16 * sixCoeffB n - 4 * sixCoeffA n : ℝ) : ℂ) := by
    rw [← h3]; simp
  rw [h4, jacobiSixSum]
  unfold sixCoeffA sixCoeffB
  push_cast
  simp only [chi4_cast_eq]

theorem jacobiSixSquares_of_forall {κ : ℝ}
    (h : ∀ x : ℝ, 0 < x → x < 1 / 2 → κ * (∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 6 =
      κ - Real.pi ^ 3 / 4 * sixSeriesA x + Real.pi ^ 3 * sixSeriesB x) :
    JacobiSixSquares :=
  fun _ hn => sumSquaresCount_six_eq_of_forall h hn

end NTKB.HardyWright
