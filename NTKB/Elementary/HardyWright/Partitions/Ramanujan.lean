/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.Partitions.Basic
import NTKB.Analytic.Apostol.Partitions.Euler
import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Ramanujan's congruences `p(5m + 4) ≡ 0 (mod 5)` and `p(7m + 5) ≡ 0 (mod 7)`
(Hardy–Wright, Chapter XIX, § 19.12)

* Jacobi's identity (Theorem 357) as an identity of formal power series with integer coefficients,
  `(∑ₖ (-1)ᵏ x^{k(3k-1)/2})³ = ∑_{m ≥ 0} (-1)^m (2m+1) x^{m(m+1)/2}` (`pentagonalSeries_pow_three`),
  obtained from the analytic identity (Apostol's Theorem 14.7, Theorem 357 here) and Euler's
  pentagonal number theorem (Theorem 353, in Mathlib) by the uniqueness of power series
  coefficients.
* **Theorem 359**: `5 ∣ p(5m + 4)`. As in the book: modulo 5, `x ∏(1 - xⁿ)⁴ = x ∏(1 - xⁿ) ∏(1 - xⁿ)³`
  is the product of Euler's and Jacobi's series, and a term `x^k`, `k = 1 + r(3r-1)/2 + s(s+1)/2`,
  with `5 ∣ k` has `5 ∣ 2s + 1`; and `x P(x) = x ∏(1 - xⁿ)⁴ · P(x)⁵`, where `P(x)⁵ ≡ P(x⁵)` only
  involves powers `x^{5j}` (the book writes this as `(1 - x)⁻⁵ ≡ (1 - x⁵)⁻¹`).
* **Theorem 360**: `7 ∣ p(7m + 5)`, "in the same way", from the square of Jacobi's series:
  `x² P(x) = x² ∏(1 - xⁿ)⁶ · P(x)⁷`, and `7 ∣ 2 + s(s+1)/2 + t(t+1)/2` forces
  `7 ∣ (2s + 1)(2t + 1)`.
-/

open PowerSeries Finset Filter Function
open scoped Topology

namespace NTKB.HardyWright

/-! ### Jacobi's series as a formal power series -/

theorem triangular_strictMono : StrictMono fun m : ℕ ↦ m * (m + 1) / 2 := by
  refine strictMono_nat_of_lt_succ fun m ↦ ?_
  have h1 : (m + 1) * (m + 1 + 1) / 2 = m * (m + 1) / 2 + (m + 1) := by
    rw [show (m + 1) * (m + 1 + 1) = m * (m + 1) + 2 * (m + 1) by ring,
      Nat.add_mul_div_left _ _ two_pos]
  rw [h1]; omega

theorem triangular_injective : Injective fun m : ℕ ↦ m * (m + 1) / 2 :=
  triangular_strictMono.injective

theorem two_mul_triangular (m : ℕ) : 2 * (m * (m + 1) / 2) = m * (m + 1) :=
  Nat.mul_div_cancel' (Nat.even_mul_succ_self m).two_dvd

/-- Jacobi's series `∑_{m ≥ 0} (-1)^m (2m + 1) x^{m(m+1)/2}` as a formal power series. -/
noncomputable def jacobiSeries (R : Type*) [CommRing R] : R⟦X⟧ :=
  PowerSeries.mk (extend (fun m : ℕ ↦ m * (m + 1) / 2) (fun m ↦ (-1) ^ m * (2 * m + 1 : R)) 0)

theorem coeff_jacobiSeries_triangular (R : Type*) [CommRing R] (m : ℕ) :
    coeff (m * (m + 1) / 2) (jacobiSeries R) = (-1) ^ m * (2 * m + 1 : R) := by
  rw [jacobiSeries, coeff_mk, triangular_injective.extend_apply]

theorem coeff_jacobiSeries_eq_zero (R : Type*) [CommRing R] {n : ℕ}
    (h : ∀ m : ℕ, m * (m + 1) / 2 ≠ n) : coeff n (jacobiSeries R) = 0 := by
  rw [jacobiSeries, coeff_mk, extend_apply' _ _ _ fun ⟨m, hm⟩ ↦ h m hm]
  rfl

theorem map_jacobiSeries {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    map f (jacobiSeries R) = jacobiSeries S := by
  ext n
  rw [coeff_map]
  by_cases h : ∃ m : ℕ, m * (m + 1) / 2 = n
  · obtain ⟨m, rfl⟩ := h
    rw [coeff_jacobiSeries_triangular, coeff_jacobiSeries_triangular]
    simp only [map_mul, map_pow, map_neg, map_one, map_add, map_natCast, map_ofNat]
  · have h' : ∀ m : ℕ, m * (m + 1) / 2 ≠ n := fun m hm ↦ h ⟨m, hm⟩
    rw [coeff_jacobiSeries_eq_zero R h', coeff_jacobiSeries_eq_zero S h', map_zero]

theorem map_pentagonalSeries {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    map f (pentagonalSeries R) = pentagonalSeries S := by
  ext n
  rw [coeff_map]
  by_cases h : n ∈ Set.range pentagonal
  · obtain ⟨k, rfl⟩ := h
    rw [coeff_pentagonalSeries_pentagonal, coeff_pentagonalSeries_pentagonal]
    simp
  · rw [coeff_pentagonalSeries_eq_zero R h, coeff_pentagonalSeries_eq_zero S h, map_zero]

/-! ### Uniqueness of the coefficients of a convergent power series -/

/-- If `∑ aₙ yⁿ` and `∑ bₙ yⁿ` converge absolutely at `y = 1/2` and agree for `‖y‖ < 1/2`,
then `a = b`. -/
theorem coeff_eq_of_tsum_eq {a b : ℕ → ℂ}
    (ha : Summable fun n ↦ ‖a n‖ * (1 / 2 : ℝ) ^ n) (hb : Summable fun n ↦ ‖b n‖ * (1 / 2 : ℝ) ^ n)
    (h : ∀ y : ℂ, ‖y‖ < 1 / 2 → ∑' n, a n * y ^ n = ∑' n, b n * y ^ n) : a = b := by
  set pa := FormalMultilinearSeries.ofScalars ℂ a
  set pb := FormalMultilinearSeries.ofScalars ℂ b
  have hra : ((1 / 2 : NNReal) : ENNReal) ≤ pa.radius := by
    refine pa.le_radius_of_summable ?_
    simpa [pa, FormalMultilinearSeries.ofScalars_norm] using ha
  have hrb : ((1 / 2 : NNReal) : ENNReal) ≤ pb.radius := by
    refine pb.le_radius_of_summable ?_
    simpa [pb, FormalMultilinearSeries.ofScalars_norm] using hb
  have hpos : (0 : ENNReal) < ((1 / 2 : NNReal) : ENNReal) := by simp
  have hfa := (pa.hasFPowerSeriesOnBall (hpos.trans_le hra)).hasFPowerSeriesAt
  have hfb := (pb.hasFPowerSeriesOnBall (hpos.trans_le hrb)).hasFPowerSeriesAt
  have heq : pa.sum =ᶠ[𝓝 0] pb.sum := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (show (0 : ℝ) < 1 / 2 by norm_num)] with y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    simp only [FormalMultilinearSeries.sum, pa, pb, FormalMultilinearSeries.ofScalars_apply_eq,
      smul_eq_mul]
    exact h y hy
  have := hfa.eq_formalMultilinearSeries_of_eventually hfb heq
  exact FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ this

/-- Cauchy product of two absolutely convergent power series. -/
theorem tsum_coeff_mul {F G : ℂ⟦X⟧} {y : ℂ} (hF : Summable fun n ↦ ‖coeff n F * y ^ n‖)
    (hG : Summable fun n ↦ ‖coeff n G * y ^ n‖) :
    (Summable fun n ↦ ‖coeff n (F * G) * y ^ n‖) ∧
      ∑' n, coeff n (F * G) * y ^ n = (∑' n, coeff n F * y ^ n) * ∑' n, coeff n G * y ^ n := by
  have hterm : ∀ n, coeff n (F * G) * y ^ n =
      ∑ kl ∈ antidiagonal n, (coeff kl.1 F * y ^ kl.1) * (coeff kl.2 G * y ^ kl.2) := by
    intro n
    rw [coeff_mul, sum_mul]
    refine sum_congr rfl fun kl hkl ↦ ?_
    rw [← mem_antidiagonal.1 hkl, pow_add]; ring
  set f : ℕ → ℂ := fun n ↦ coeff n F * y ^ n
  set g : ℕ → ℂ := fun n ↦ coeff n G * y ^ n
  refine ⟨(summable_norm_sum_mul_antidiagonal_of_summable_norm (f := f) (g := g) hF hG).congr
    fun n ↦ by rw [hterm], ?_⟩
  rw [tsum_congr hterm]
  exact (tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (f := f) (g := g) hF hG).symm

/-! ### Jacobi's identity for formal power series -/

theorem summable_norm_coeff_pentagonalSeries {y : ℂ} (hy : ‖y‖ < 1) :
    Summable fun n ↦ ‖coeff n (pentagonalSeries ℂ) * y ^ n‖ := by
  refine (summable_geometric_of_lt_one (norm_nonneg y) hy).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    fun n ↦ ?_
  by_cases hn : n ∈ Set.range pentagonal
  · obtain ⟨k, rfl⟩ := hn
    rw [coeff_pentagonalSeries_pentagonal, norm_mul, norm_pow]
    simp
  · simp [coeff_pentagonalSeries_eq_zero ℂ hn]

theorem norm_coeff_jacobiSeries_le (n : ℕ) : ‖coeff n (jacobiSeries ℂ)‖ ≤ 2 * n + 1 := by
  by_cases h : ∃ m : ℕ, m * (m + 1) / 2 = n
  · obtain ⟨m, rfl⟩ := h
    rw [coeff_jacobiSeries_triangular, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    have hm : m ≤ m * (m + 1) / 2 := by
      rw [Nat.le_div_iff_mul_le two_pos]
      rcases m with _ | m
      · simp
      · exact Nat.mul_le_mul_left _ (by omega)
    have : ‖(2 * (m : ℂ) + 1)‖ = 2 * m + 1 := by
      rw [show (2 * (m : ℂ) + 1) = ((2 * m + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
      push_cast; ring
    rw [this]
    have : (m : ℝ) ≤ ((m * (m + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast hm
    linarith
  · have h' : ∀ m : ℕ, m * (m + 1) / 2 ≠ n := fun m hm ↦ h ⟨m, hm⟩
    rw [coeff_jacobiSeries_eq_zero ℂ h', norm_zero]; positivity

theorem summable_norm_coeff_jacobiSeries {y : ℂ} (hy : ‖y‖ < 1) :
    Summable fun n ↦ ‖coeff n (jacobiSeries ℂ) * y ^ n‖ := by
  have h1 : Summable fun n : ℕ ↦ (n : ℝ) ^ 1 * ‖y‖ ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (by rwa [norm_norm])
  have h2 := summable_geometric_of_lt_one (norm_nonneg y) hy
  refine ((h1.mul_left 2).add h2).of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun n ↦ ?_
  rw [norm_mul, norm_pow]
  have := norm_coeff_jacobiSeries_le n
  have h0 : 0 ≤ ‖y‖ ^ n := by positivity
  simp only [pow_one]
  nlinarith

/-- The value of Jacobi's series: `∑ₙ cₙ yⁿ = ∑_{m ≥ 0} (-1)^m (2m+1) y^{m(m+1)/2}`. -/
theorem tsum_coeff_jacobiSeries (y : ℂ) :
    ∑' n, coeff n (jacobiSeries ℂ) * y ^ n =
      ∑' m : ℕ, (-1) ^ m * (2 * m + 1 : ℂ) * y ^ (m * (m + 1) / 2) := by
  rw [← tsum_extend_zero triangular_injective
    (fun m : ℕ ↦ (-1) ^ m * (2 * m + 1 : ℂ) * y ^ (m * (m + 1) / 2))]
  congr 1
  ext n
  by_cases h : ∃ m : ℕ, m * (m + 1) / 2 = n
  · obtain ⟨m, rfl⟩ := h
    rw [coeff_jacobiSeries_triangular, triangular_injective.extend_apply]
  · have h' : ∀ m : ℕ, m * (m + 1) / 2 ≠ n := fun m hm ↦ h ⟨m, hm⟩
    rw [coeff_jacobiSeries_eq_zero ℂ h', zero_mul, extend_apply' _ _ _ fun ⟨m, hm⟩ ↦ h' m hm]
    rfl

/-- **Theorem 357** (Jacobi), for formal power series: the cube of Euler's series
`∑ₖ (-1)ᵏ x^{k(3k-1)/2}` (= `∏(1 - xⁿ)` by Theorem 353) is Jacobi's series
`∑_{m ≥ 0} (-1)^m (2m+1) x^{m(m+1)/2}`, over any commutative ring. -/
@[kb "hardywright2008" "Thm 357, p. 396"]
theorem pentagonalSeries_pow_three (R : Type*) [CommRing R] :
    pentagonalSeries R ^ 3 = jacobiSeries R := by
  -- over `ℂ`, by comparing the two convergent series
  have hC : pentagonalSeries ℂ ^ 3 = jacobiSeries ℂ := by
    ext1 n
    have key := coeff_eq_of_tsum_eq (a := fun n ↦ coeff n (pentagonalSeries ℂ ^ 3))
      (b := fun n ↦ coeff n (jacobiSeries ℂ)) ?_ ?_ ?_
    · exact congrFun key n
    · have hE := summable_norm_coeff_pentagonalSeries (y := (1 / 2 : ℂ)) (by norm_num)
      have h3 := (tsum_coeff_mul (tsum_coeff_mul hE hE).1 hE).1
      have e : pentagonalSeries ℂ ^ 3 =
          pentagonalSeries ℂ * pentagonalSeries ℂ * pentagonalSeries ℂ := by ring
      simp only [e]
      refine h3.congr fun n ↦ ?_
      rw [norm_mul, norm_pow]; norm_num
    · refine (summable_norm_coeff_jacobiSeries (y := (1 / 2 : ℂ)) (by norm_num)).congr fun n ↦ ?_
      rw [norm_mul, norm_pow]; norm_num
    · intro y hy
      have hy1 : ‖y‖ < 1 := hy.trans (by norm_num)
      have hE := summable_norm_coeff_pentagonalSeries hy1
      obtain ⟨h2, e2⟩ := tsum_coeff_mul hE hE
      obtain ⟨-, e3⟩ := tsum_coeff_mul h2 hE
      have hpent : ∑' n, coeff n (pentagonalSeries ℂ) * y ^ n = ∏' n : ℕ, (1 - y ^ (n + 1)) := by
        rw [← eulerFunction_eq_tprod hy1]; rfl
      have hprod := hasProd_eulerFunction hy1
      have hcube : HasProd (fun n : ℕ ↦ (1 - y ^ (n + 1)) ^ 3) (eulerFunction y ^ 3) := by
        have := (hprod.mul hprod).mul hprod
        simpa [pow_three', mul_assoc] using this
      have hJ := jacobi_cube_identity hy1
      have hval := hcube.unique hJ
      rw [show pentagonalSeries ℂ ^ 3 =
          pentagonalSeries ℂ * pentagonalSeries ℂ * pentagonalSeries ℂ by ring,
        e3, e2, tsum_coeff_jacobiSeries, hpent,
        ← eulerFunction_eq_tprod hy1, ← hval]
      ring
  -- transport to `ℤ` and then to `R`
  have hZ : pentagonalSeries ℤ ^ 3 = jacobiSeries ℤ := by
    have hinj : Injective (PowerSeries.map (Int.castRingHom ℂ)) := by
      intro F G hFG
      ext n
      have := congrArg (coeff n) hFG
      simpa [coeff_map] using this
    apply hinj
    rw [map_pow, map_pentagonalSeries, map_jacobiSeries, hC]
  have := congrArg (PowerSeries.map (Int.castRingHom R)) hZ
  rwa [map_pow, map_pentagonalSeries, map_jacobiSeries] at this

/-! ### Frobenius: the `p`-th power of a power series over `ZMod p` -/

theorem coeff_pow_char_eq_zero (p : ℕ) [hp : Fact p.Prime] (f : (ZMod p)⟦X⟧) {k : ℕ}
    (hk : ¬ p ∣ k) : coeff k (f ^ p) = 0 := by
  set g := trunc (k + 1) f
  have h1 : coeff k (f ^ p) = coeff k ((g : (ZMod p)⟦X⟧) ^ p) := by
    have := congrArg (fun q ↦ Polynomial.coeff q k) (trunc_trunc_pow f (k + 1) p)
    simp only [coeff_trunc, Nat.lt_succ_self, ite_true] at this
    exact this.symm
  rw [h1, ← Polynomial.coe_pow, Polynomial.coeff_coe, ← Polynomial.map_frobenius_expand p,
    Polynomial.coeff_map, Polynomial.coeff_expand hp.out.pos]
  simp [hk]

/-! ### Theorems 359 and 360 -/

/-- Partition numbers as coefficients. -/
theorem coeff_partitionSeries (R : Type*) [CommRing R] (n : ℕ) :
    coeff n (NTKB.Apostol.partitionSeries R) = (Fintype.card n.Partition : R) := by
  rw [NTKB.Apostol.partitionSeries, coeff_mk]

/-- `2 · ω(k) = k(3k - 1)` for the pentagonal numbers, in any commutative ring. -/
theorem two_mul_pentagonal_cast {R : Type*} [CommRing R] (k : ℤ) :
    2 * (pentagonal k : R) = (k : R) * (3 * k - 1) := by
  have := congrArg (Int.cast : ℤ → R) (two_mul_natCast_pentagonal k)
  push_cast at this
  exact this

theorem two_mul_triangular_cast {R : Type*} [CommRing R] (m : ℕ) :
    2 * ((m * (m + 1) / 2 : ℕ) : R) = (m : R) * (m + 1) := by
  have := congrArg (Nat.cast : ℕ → R) (two_mul_triangular m)
  push_cast at this
  exact this

/-- In `x ∏(1 - xⁿ)⁴ = x · (Euler's series) · (Jacobi's series)`, the coefficient of `x^{5j}`
vanishes modulo 5 (Hardy–Wright, § 19.12). -/
theorem coeff_X_mul_pentagonal_mul_jacobi_five {i : ℕ} (hi : 5 ∣ i) :
    coeff i (X * (pentagonalSeries (ZMod 5) * jacobiSeries (ZMod 5))) = 0 := by
  rcases i with _ | i
  · simp
  rw [coeff_succ_X_mul, coeff_mul]
  refine sum_eq_zero fun ab hab ↦ ?_
  rw [mem_antidiagonal] at hab
  by_cases ha : ab.1 ∈ Set.range pentagonal
  swap
  · rw [coeff_pentagonalSeries_eq_zero _ ha, zero_mul]
  by_cases hb : ∃ s : ℕ, s * (s + 1) / 2 = ab.2
  swap
  · rw [coeff_jacobiSeries_eq_zero _ fun t ht ↦ hb ⟨t, ht⟩, mul_zero]
  obtain ⟨k, hk⟩ := ha
  obtain ⟨s, hs⟩ := hb
  rw [← hs, coeff_jacobiSeries_triangular]
  -- `5 ∣ 1 + ω(k) + s(s+1)/2` forces `5 ∣ 2s + 1`
  have hcast : ((i + 1 : ℕ) : ZMod 5) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hi
  have hsum : (i + 1 : ℕ) = 1 + pentagonal k + s * (s + 1) / 2 := by rw [hk, hs]; omega
  rw [hsum] at hcast
  push_cast at hcast
  have h8 : (8 : ZMod 5) + 4 * ((k : ZMod 5) * (3 * k - 1)) + 4 * ((s : ZMod 5) * (s + 1)) = 0 := by
    rw [← two_mul_pentagonal_cast, ← two_mul_triangular_cast]
    linear_combination 8 * hcast
  have key : ∀ u v : ZMod 5, 8 + 4 * (u * (3 * u - 1)) + 4 * (v * (v + 1)) = 0 → 2 * v + 1 = 0 := by
    decide
  rw [key _ _ h8, mul_zero, mul_zero]

/-- **Theorem 359** (Ramanujan). `p(5m + 4) ≡ 0 (mod 5)`. -/
@[kb "hardywright2008" "Thm 359, p. 399"]
theorem five_dvd_card_partition (m : ℕ) : 5 ∣ Fintype.card (5 * m + 4).Partition := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set P := NTKB.Apostol.partitionSeries (ZMod 5)
  set E := pentagonalSeries (ZMod 5)
  have hPE : P * E = 1 := NTKB.Apostol.partitionSeries_mul_pentagonalSeries (ZMod 5)
  have hid : X * P = (X * (E * jacobiSeries (ZMod 5))) * P ^ 5 := by
    rw [← pentagonalSeries_pow_three]
    linear_combination (-(X * P * (1 + P * E + (P * E) ^ 2 + (P * E) ^ 3))) * hPE
  have hcoeff : coeff (5 * m + 5) (X * P) = 0 := by
    rw [hid, coeff_mul]
    refine sum_eq_zero fun ij hij ↦ ?_
    rw [mem_antidiagonal] at hij
    by_cases h5 : 5 ∣ ij.2
    · have : 5 ∣ ij.1 := by omega
      rw [coeff_X_mul_pentagonal_mul_jacobi_five this, zero_mul]
    · rw [coeff_pow_char_eq_zero 5 P h5, mul_zero]
  rw [show 5 * m + 5 = (5 * m + 4) + 1 by ring, coeff_succ_X_mul, coeff_partitionSeries] at hcoeff
  exact (ZMod.natCast_eq_zero_iff _ _).1 hcoeff

/-- In `x² ∏(1 - xⁿ)⁶ = x² · (Jacobi's series)²`, the coefficient of `x^{7j}` vanishes modulo 7. -/
theorem coeff_X_sq_mul_jacobi_sq_seven {i : ℕ} (hi : 7 ∣ i) :
    coeff i (X ^ 2 * (jacobiSeries (ZMod 7) * jacobiSeries (ZMod 7))) = 0 := by
  rcases i with _ | _ | i
  · simp
  · omega
  rw [show i + 1 + 1 = i + 2 by ring, coeff_X_pow_mul']
  simp only [show 2 ≤ i + 2 by omega, ite_true, show i + 2 - 2 = i by omega]
  rw [coeff_mul]
  refine sum_eq_zero fun ab hab ↦ ?_
  rw [mem_antidiagonal] at hab
  by_cases ha : ∃ s : ℕ, s * (s + 1) / 2 = ab.1
  swap
  · rw [coeff_jacobiSeries_eq_zero _ fun t ht ↦ ha ⟨t, ht⟩, zero_mul]
  by_cases hb : ∃ t : ℕ, t * (t + 1) / 2 = ab.2
  swap
  · rw [coeff_jacobiSeries_eq_zero _ fun t ht ↦ hb ⟨t, ht⟩, mul_zero]
  obtain ⟨s, hs⟩ := ha
  obtain ⟨t, ht⟩ := hb
  rw [← hs, ← ht, coeff_jacobiSeries_triangular, coeff_jacobiSeries_triangular]
  have hcast : ((i + 2 : ℕ) : ZMod 7) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hi
  have hsum : (i + 2 : ℕ) = 2 + s * (s + 1) / 2 + t * (t + 1) / 2 := by rw [hs, ht]; omega
  rw [hsum] at hcast
  push_cast at hcast
  have h8 : (16 : ZMod 7) + 4 * ((s : ZMod 7) * (s + 1)) + 4 * ((t : ZMod 7) * (t + 1)) = 0 := by
    rw [← two_mul_triangular_cast, ← two_mul_triangular_cast]
    linear_combination 8 * hcast
  have key : ∀ u v : ZMod 7, 16 + 4 * (u * (u + 1)) + 4 * (v * (v + 1)) = 0 →
      (2 * u + 1) * (2 * v + 1) = 0 := by
    decide
  have := key _ _ h8
  linear_combination ((-1) ^ s * (-1) ^ t : ZMod 7) * this

/-- **Theorem 360** (Ramanujan). `p(7m + 5) ≡ 0 (mod 7)`. -/
@[kb "hardywright2008" "Thm 360, p. 399"]
theorem seven_dvd_card_partition (m : ℕ) : 7 ∣ Fintype.card (7 * m + 5).Partition := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  set P := NTKB.Apostol.partitionSeries (ZMod 7)
  set E := pentagonalSeries (ZMod 7)
  have hPE : P * E = 1 := NTKB.Apostol.partitionSeries_mul_pentagonalSeries (ZMod 7)
  have hid : X ^ 2 * P = (X ^ 2 * (jacobiSeries (ZMod 7) * jacobiSeries (ZMod 7))) * P ^ 7 := by
    rw [← pentagonalSeries_pow_three]
    linear_combination (-(X ^ 2 * P * (1 + P * E + (P * E) ^ 2 + (P * E) ^ 3 + (P * E) ^ 4 +
      (P * E) ^ 5))) * hPE
  have hcoeff : coeff (7 * m + 7) (X ^ 2 * P) = 0 := by
    rw [hid, coeff_mul]
    refine sum_eq_zero fun ij hij ↦ ?_
    rw [mem_antidiagonal] at hij
    by_cases h7 : 7 ∣ ij.2
    · have : 7 ∣ ij.1 := by omega
      rw [coeff_X_sq_mul_jacobi_sq_seven this, zero_mul]
    · rw [coeff_pow_char_eq_zero 7 P h7, mul_zero]
  rw [coeff_X_pow_mul'] at hcoeff
  simp only [show 2 ≤ 7 * m + 7 by omega, ite_true, show 7 * m + 7 - 2 = 7 * m + 5 by omega]
    at hcoeff
  rw [coeff_partitionSeries] at hcoeff
  exact (ZMod.natCast_eq_zero_iff _ _).1 hcoeff

end NTKB.HardyWright
