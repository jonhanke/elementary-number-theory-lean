/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.ArithmeticFunctions.SumTwoSquares
import NTKB.Elementary.HardyWright.ArithmeticFunctions.Order
import NTKB.Elementary.HardyWright.ArithmeticFunctions.Lambert
import NTKB.Elementary.HardyWright.ArithmeticFunctions.DirichletSeries
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# Hardy–Wright: consequences of Theorem 278 for `r(n)`

* Theorem 306: `∑ r(n) n^{-s} = 4 ζ(s) L(s)`, `L(s) = 1^{-s} - 3^{-s} + 5^{-s} - ⋯`.
* Theorem 311: `∑ r(n) xⁿ = 4 (x/(1-x) - x³/(1-x³) + x⁵/(1-x⁵) - ⋯)`.
* Theorem 336: `liminf r(n) = 0`.
* Theorem 338: `r(n) = O(n^δ)` for every `δ > 0`.
* Theorem 341: `∑_{v ≤ x} r(v) = 4 ([x] - [x/3] + [x/5] - ⋯)`.
-/

open Finset Filter Topology Asymptotics ArithmeticFunction
open scoped ArithmeticFunction.sigma ArithmeticFunction.zeta

namespace NTKB.HardyWright

lemma abs_chi4_le_one (n : ℕ) : |chi4 n| ≤ 1 := by
  rw [chi4_eq]; split_ifs <;> simp

lemma chi4DivisorSum_le_card_divisors (n : ℕ) : chi4DivisorSum n ≤ σ 0 n := by
  rw [chi4DivisorSum, sigma_zero_apply, card_eq_sum_ones, Nat.cast_sum]
  exact sum_le_sum fun d _ => by have := abs_chi4_le_one d; simp only [Nat.cast_one]; linarith [le_abs_self (chi4 d)]

/-- `r(n) ≤ 4 d(n)` (Hardy–Wright § 18.7). -/
lemma sumTwoSquaresCount_le {n : ℕ} (hn : 0 < n) : sumTwoSquaresCount n ≤ 4 * σ 0 n := by
  have h := sumTwoSquaresCount_eq hn
  have := chi4DivisorSum_le_card_divisors n
  have : (sumTwoSquaresCount n : ℤ) ≤ 4 * σ 0 n := by rw [h]; linarith
  exact_mod_cast this

/-- `r(n) = 0` for `n ≡ 3 (mod 4)`. -/
lemma sumTwoSquaresCount_eq_zero_of_mod_four_eq_three {n : ℕ} (hn : n % 4 = 3) :
    sumTwoSquaresCount n = 0 := by
  have hempty : {x : ℤ × ℤ | x.1 ^ 2 + x.2 ^ 2 = n} = ∅ := by
    ext ⟨a, b⟩
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    have h1 := congrArg (fun z : ℤ => (z : ZMod 4)) h
    push_cast at h1
    have h3 : ((n : ℕ) : ZMod 4) = 3 := by
      rw [← ZMod.natCast_mod, hn]; rfl
    rw [h3] at h1
    have key : ∀ x y : ZMod 4, x ^ 2 + y ^ 2 ≠ 3 := by decide
    exact key _ _ h1
  rw [sumTwoSquaresCount, hempty, Set.ncard_empty]

/-- **Theorem 336** (Hardy–Wright). The lower limit of `r(n)` is `0` (`r(n) = 0` for
`n ≡ 3 (mod 4)`; the book prints it as `lim r(n) = 0`, meaning the lower limit). -/
@[kb "hardywright2008" "Thm 336, p. 375"]
theorem liminf_sumTwoSquaresCount : liminf (fun n => sumTwoSquaresCount n) atTop = 0 := by
  refine le_antisymm ?_ (Nat.zero_le _)
  refine liminf_le_of_frequently_le ?_ (isBoundedUnder_of_eventually_ge
    (Eventually.of_forall fun n => Nat.zero_le _))
  rw [Nat.frequently_atTop_iff_infinite]
  refine Set.infinite_of_not_bddAbove fun ⟨B, hB⟩ => ?_
  have := hB (show 4 * B + 3 ∈ {n | sumTwoSquaresCount n ≤ 0} from by
    simp only [Set.mem_ofPred_eq, nonpos_iff_eq_zero]
    exact sumTwoSquaresCount_eq_zero_of_mod_four_eq_three (by omega))
  omega

/-- **Theorem 338** (Hardy–Wright). `r(n) = O(n^δ)` for every `δ > 0`. -/
@[kb "hardywright2008" "Thm 338, p. 375"]
theorem sumTwoSquaresCount_isBigO_rpow {δ : ℝ} (hδ : 0 < δ) :
    (fun n : ℕ => (sumTwoSquaresCount n : ℝ)) =O[atTop] fun n => (n : ℝ) ^ δ := by
  refine IsBigO.trans ?_ ((card_divisors_isBigO_rpow hδ).const_mul_left 4)
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by positivity), one_mul]
  exact_mod_cast sumTwoSquaresCount_le hn

/-- **Theorem 341** (Hardy–Wright). `∑_{1 ≤ v ≤ x} r(v) = 4 ([x] - [x/3] + [x/5] - ⋯)
= 4 ∑_{u ≤ x} χ(u) [x/u]`, whether `x` is an integer or not. -/
@[kb "hardywright2008" "Thm 341, p. 378"]
theorem sum_sumTwoSquaresCount_eq (x : ℝ) :
    ∑ v ∈ Ioc 0 ⌊x⌋₊, (sumTwoSquaresCount v : ℤ) =
      4 * ∑ u ∈ Ioc 0 ⌊x⌋₊, chi4 u * ⌊x / u⌋₊ := by
  rcases le_or_gt x 0 with hx | hx
  · simp [Nat.floor_eq_zero.mpr (by linarith : x < 1)]
  rw [sum_congr rfl fun v hv => sumTwoSquaresCount_eq (mem_Ioc.mp hv).1, ← mul_sum]
  congr 1
  simp only [chi4DivisorSum_eq_mul_zeta]
  rw [sum_Ioc_mul_zeta_eq_sum]
  refine sum_congr rfl fun u _ => ?_
  rw [chi4Fun_apply, Nat.floor_div_natCast]

/-- **Theorem 306** (Hardy–Wright). For `s > 1` (here complex `s`, `Re s > 1`),
`∑ r(n) n^{-s} = 4 ζ(s) L(s)`, `L(s) = ∑ χ(n) n^{-s} = 1^{-s} - 3^{-s} + 5^{-s} - ⋯`. -/
@[kb "hardywright2008" "Thm 306, p. 356"]
theorem LSeries_sumTwoSquaresCount {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (sumTwoSquaresCount n : ℂ)) s =
      4 * riemannZeta s * LSeries (fun n => (chi4 n : ℂ)) s := by
  have hcongr : LSeries (fun n => (sumTwoSquaresCount n : ℂ)) s =
      LSeries ((4 : ℂ) • fun n => ((chi4Fun : ArithmeticFunction ℂ) * (ζ : ArithmeticFunction ℂ)) n) s := by
    refine LSeries_congr (fun {n} hn => ?_) s
    have h := sumTwoSquaresCount_eq (Nat.pos_of_ne_zero hn)
    rw [chi4DivisorSum_eq_mul_zeta] at h
    have h' := congrArg (fun z : ℤ => (z : ℂ)) h
    push_cast at h'
    rw [Pi.smul_apply, smul_eq_mul, h', coe_mul_zeta_apply, coe_mul_zeta_apply]
    push_cast
    simp [intCoe_apply]
  have hχ : LSeriesSummable (fun n => (chi4Fun : ArithmeticFunction ℂ) n) s :=
    LSeriesSummable_of_abs_le_one (fun n => by
      rw [intCoe_apply, Complex.norm_intCast]; exact_mod_cast abs_chi4_le_one n) hs
  rw [hcongr, LSeries_smul, LSeries_mul' hχ (LSeriesSummable_zetaC hs), LSeries_zetaC hs]
  have : LSeries (fun n => (chi4Fun : ArithmeticFunction ℂ) n) s =
      LSeries (fun n => (chi4 n : ℂ)) s := by
    rfl
  rw [this]; ring

/-- **Theorem 311** (Hardy–Wright). For `|x| < 1`,
`∑_{n ≥ 1} r(n) xⁿ = 4 (x/(1-x) - x³/(1-x³) + x⁵/(1-x⁵) - ⋯) = 4 ∑ χ(n) xⁿ/(1-xⁿ)`. -/
@[kb "hardywright2008" "Thm 311, p. 359"]
theorem hasSum_sumTwoSquaresCount_mul_pow {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ+ => (sumTwoSquaresCount n : ℝ) * x ^ (n : ℕ))
      (4 * ∑' n : ℕ+, (chi4 n : ℝ) * x ^ (n : ℕ) / (1 - x ^ (n : ℕ))) := by
  have hL := hasSum_lambert (a := fun n => (chi4 n : ℝ)) (fun n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [chi4]
    · have := abs_chi4_le_one n
      have : |(chi4 n : ℝ)| ≤ 1 := by exact_mod_cast this
      exact this.trans (by exact_mod_cast hn)) hx
  rw [hL.tsum_eq]
  have e : ∀ N : ℕ+, (sumTwoSquaresCount N : ℝ) * x ^ (N : ℕ) =
      4 * ((∑ d ∈ (N : ℕ).divisors, (chi4 d : ℝ)) * x ^ (N : ℕ)) := by
    intro N
    have h := sumTwoSquaresCount_eq N.pos
    have h' := congrArg (fun z : ℤ => (z : ℝ)) h
    push_cast [chi4DivisorSum] at h'
    rw [h']; ring
  have hsum : Summable fun N : ℕ+ => (sumTwoSquaresCount N : ℝ) * x ^ (N : ℕ) := by
    have hg : Summable fun n : ℕ => (n : ℝ) ^ 1 * |x| ^ n :=
      summable_pow_mul_geometric_of_norm_lt_one 1 (by rwa [Real.norm_eq_abs, abs_abs])
    have hg' : Summable fun N : ℕ+ => 4 * (((N : ℕ) : ℝ) * |x| ^ (N : ℕ)) :=
      ((hg.comp_injective PNat.coe_injective).mul_left 4).congr fun N => by simp
    refine Summable.of_norm_bounded hg' fun N => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (Nat.cast_nonneg _)]
    have h1 : (sumTwoSquaresCount N : ℝ) ≤ 4 * ((N : ℕ) : ℝ) := by
      have := sumTwoSquaresCount_le N.pos
      have h2 : σ 0 (N : ℕ) ≤ (N : ℕ) := by
        rw [sigma_zero_apply]; exact Nat.card_divisors_le_self _
      exact_mod_cast this.trans (Nat.mul_le_mul_left 4 h2)
    have : 0 ≤ |x| ^ (N : ℕ) := by positivity
    nlinarith
  rw [← tsum_mul_left, ← tsum_congr e]
  exact hsum.hasSum

/-- If `P` is a product of `k` different primes `≡ 1 (mod 4)`, then `r(P^m) = 4 (m+1)^k`. -/
lemma sumTwoSquaresCount_prod_pow {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime ∧ p % 4 = 1) (m : ℕ) :
    (sumTwoSquaresCount ((∏ p ∈ S, p) ^ m) : ℤ) = 4 * (m + 1) ^ #S := by
  have hpos : 0 < (∏ p ∈ S, p) ^ m :=
    pow_pos (prod_pos fun p hp => (hS p hp).1.pos) m
  rw [sumTwoSquaresCount_eq hpos, chi4DivisorSum_eq_mul_zeta, ← prod_pow,
    isMultiplicative_chi4DivisorSum.map_prod (fun p => p ^ m) S]
  · rw [prod_congr rfl fun p hp => by
      rw [← chi4DivisorSum_eq_mul_zeta, chi4DivisorSum_prime_pow_eq (hS p hp).1, chi4LocalFactor,
        ite_eq_left_of_eq_true _ _ (eq_true (hS p hp).2)]]
    rw [prod_const]
  · intro p hp q hq hpq
    exact Nat.Coprime.pow m m ((Nat.coprime_primes (hS p hp).1 (hS q hq).1).mpr hpq)

/-- **Theorem 337** (Hardy–Wright). `r(n) = O((log n)^Δ)` is false for every `Δ`. Proof (book):
along `n = P^m`, `P` a product of `k > Δ` primes `≡ 1 (mod 4)`, `r(n) = 4 d(n) = 4 (m+1)^k`. -/
@[kb "hardywright2008" "Thm 337, p. 375"]
theorem not_sumTwoSquaresCount_isBigO_log_rpow (Δ : ℝ) :
    ¬ (fun n : ℕ => (sumTwoSquaresCount n : ℝ)) =O[atTop] fun n => Real.log n ^ Δ := by
  intro h
  obtain ⟨k, hk⟩ := exists_nat_gt (max Δ 0)
  have hinf : {p : ℕ | p.Prime ∧ p % 4 = 1}.Infinite := by
    convert Nat.infinite_setOfPred_prime_modEq_one (k := 4) (by norm_num) using 3
    rfl
  obtain ⟨S, hSsub, hScard⟩ := hinf.exists_subset_card_eq k
  have hS : ∀ p ∈ S, p.Prime ∧ p % 4 = 1 := fun p hp => hSsub hp
  set P := ∏ p ∈ S, p with hP
  have hk0 : 0 < k := by exact_mod_cast (le_max_right Δ 0).trans_lt hk
  have hP2 : 2 ≤ P := by
    obtain ⟨p, hp⟩ : S.Nonempty := card_pos.mp (hScard ▸ hk0)
    calc 2 ≤ p := (hS p hp).1.two_le
      _ ≤ P := Nat.le_of_dvd (prod_pos fun q hq => (hS q hq).1.pos) (dvd_prod_of_mem _ hp)
  have hlogP : 0 < Real.log P := Real.log_pos (by exact_mod_cast hP2)
  have htend : Tendsto (fun m : ℕ => P ^ m) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by omega)
  obtain ⟨C, hC⟩ := (h.comp_tendsto htend).bound
  have hgrow : Tendsto (fun m : ℕ => (m : ℝ) ^ ((k : ℝ) - Δ)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith [le_max_left Δ 0])).comp tendsto_natCast_atTop_atTop
  obtain ⟨m, hm1, hm2, hm3⟩ := ((hgrow.eventually_gt_atTop (|C| * Real.log P ^ Δ)).and
    (hC.and (eventually_ge_atTop 1))).exists
  have hd : (sumTwoSquaresCount (P ^ m) : ℝ) = 4 * (m + 1) ^ k := by
    have := sumTwoSquaresCount_prod_pow hS m
    rw [hScard] at this
    exact_mod_cast this
  simp only [Function.comp, hd, Real.norm_eq_abs] at hm2
  push_cast at hm2
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm3
  have hm0 : (0 : ℝ) < m := by linarith
  rw [Real.log_pow, Real.mul_rpow hm0.le hlogP.le] at hm2
  rw [abs_of_pos (by positivity), abs_of_pos (by positivity)] at hm2
  have h3 : (m : ℝ) ^ (k : ℝ) ≤ |C| * ((m : ℝ) ^ Δ * Real.log P ^ Δ) := by
    rw [Real.rpow_natCast]
    calc (m : ℝ) ^ k ≤ ((m : ℝ) + 1) ^ k := by gcongr; linarith
      _ ≤ 4 * ((m : ℝ) + 1) ^ k := by
          have : (0 : ℝ) ≤ ((m : ℝ) + 1) ^ k := by positivity
          linarith
      _ ≤ C * ((m : ℝ) ^ Δ * Real.log P ^ Δ) := hm2
      _ ≤ |C| * ((m : ℝ) ^ Δ * Real.log P ^ Δ) := by gcongr; exact le_abs_self C
  have hmΔ : (0 : ℝ) < (m : ℝ) ^ Δ := Real.rpow_pos_of_pos hm0 Δ
  rw [Real.rpow_sub hm0, div_eq_mul_inv] at hm1
  have h4 := (lt_mul_inv_iff₀ hmΔ).mp hm1
  linarith

/-! ### Theorem 312 -/

lemma summable_abs_pow_natAbs {x : ℝ} (hx : |x| < 1) :
    Summable fun m : ℤ => |x| ^ m.natAbs := by
  have hg : Summable fun n : ℕ => |x| ^ n :=
    summable_geometric_of_lt_one (abs_nonneg x) hx
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · simpa using hg
  · refine (hg.comp_injective (add_left_injective 1)).congr fun n => ?_
    simp only [Function.comp]
    congr 1

lemma summable_theta {x : ℝ} (hx : |x| < 1) :
    Summable fun m : ℤ => ‖x ^ (m.natAbs ^ 2)‖ := by
  refine (summable_abs_pow_natAbs hx).of_nonneg_of_le (fun m => norm_nonneg _) fun m => ?_
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_of_le_one (abs_nonneg x) hx.le (by nlinarith [Nat.zero_le m.natAbs])

lemma sumTwoSquaresCount_zero : sumTwoSquaresCount 0 = 1 := by
  have : {x : ℤ × ℤ | x.1 ^ 2 + x.2 ^ 2 = ((0 : ℕ) : ℤ)} = {(0, 0)} := by
    ext ⟨a, b⟩
    simp only [Set.mem_ofPred_eq, Nat.cast_zero, Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · intro h
      have ha : a ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
      have hb : b ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
      exact ⟨pow_eq_zero_iff two_ne_zero |>.mp ha, pow_eq_zero_iff two_ne_zero |>.mp hb⟩
    · rintro ⟨rfl, rfl⟩; norm_num
  rw [sumTwoSquaresCount, this, Set.ncard_singleton]

/-- `θ(x)² = ∑_{n ≥ 0} r(n) xⁿ`, `θ(x) = ∑_{m ∈ ℤ} x^{m²}`: each pair `(m₁, m₂)` with
`m₁² + m₂² = n` contributes `xⁿ` (Hardy–Wright, end of § 17.10). -/
lemma hasSum_sumTwoSquaresCount_mul_pow_nat {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ => (sumTwoSquaresCount n : ℝ) * x ^ n)
      ((∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 2) := by
  set f : ℤ → ℝ := fun m => x ^ (m.natAbs ^ 2) with hf
  set F : ℤ × ℤ → ℕ := fun p => p.1.natAbs ^ 2 + p.2.natAbs ^ 2 with hF
  have hprod : HasSum (fun p : ℤ × ℤ => f p.1 * f p.2) ((∑' m, f m) ^ 2) := by
    rw [sq, tsum_mul_tsum_of_summable_norm (summable_theta hx) (summable_theta hx)]
    exact (summable_mul_of_summable_norm (summable_theta hx) (summable_theta hx)).hasSum
  have hval : ∀ p : ℤ × ℤ, f p.1 * f p.2 = x ^ F p := fun p => by simp [hf, hF, pow_add]
  simp only [hval] at hprod
  have hsig := (Equiv.sigmaFiberEquiv F).hasSum_iff.mpr hprod
  refine hsig.sigma fun n => ?_
  -- the fibre over `n` is finite, with `r(n)` elements
  have hset : {p : ℤ × ℤ | F p = n} = {p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 2 = n} := by
    ext p
    simp only [hF, Set.mem_ofPred_eq]
    constructor
    · intro h; rw [← Int.natAbs_sq p.1, ← Int.natAbs_sq p.2]; exact_mod_cast h
    · intro h; rw [← Int.natAbs_sq p.1, ← Int.natAbs_sq p.2] at h; exact_mod_cast h
  have hfin : {p : ℤ × ℤ | F p = n}.Finite := by
    rw [hset]
    refine ((Icc (-(n : ℤ)) n ×ˢ Icc (-(n : ℤ)) n : Finset (ℤ × ℤ)).finite_toSet).subset
      fun p hp => ?_
    obtain ⟨h1, h2⟩ := abs_re_le_of_norm (z := ⟨p.1, p.2⟩) (n := n)
      (by rw [norm_eq_sq_add_sq]; exact hp)
    simp only [coe_product, coe_Icc, Set.mem_prod, Set.mem_Icc]
    exact ⟨abs_le.mp h1, abs_le.mp h2⟩
  have : Finite {p : ℤ × ℤ // F p = n} := hfin.to_subtype
  have := Fintype.ofFinite {p : ℤ × ℤ // F p = n}
  have hsum := hasSum_fintype (fun c : {p : ℤ × ℤ // F p = n} => x ^ F c.1)
  have e1 : ∑ c : {p : ℤ × ℤ // F p = n}, x ^ F c.1 = (sumTwoSquaresCount n : ℝ) * x ^ n := by
    rw [Finset.sum_congr rfl (fun c _ => by rw [c.2]), sum_const, card_univ, nsmul_eq_mul,
      Fintype.card_eq_nat_card]
    congr 1
    rw [sumTwoSquaresCount, ← hset]
    exact_mod_cast (Nat.card_coe_set_eq {p : ℤ × ℤ | F p = n})
  rw [e1] at hsum
  exact hsum

/-- `∑_{m ∈ ℤ} x^{m²} = 1 + 2x + 2x⁴ + 2x⁹ + ⋯`. -/
lemma tsum_int_theta {x : ℝ} (hx : |x| < 1) :
    ∑' m : ℤ, x ^ (m.natAbs ^ 2) = 1 + 2 * ∑' m : ℕ+, x ^ ((m : ℕ) ^ 2) := by
  set S := ∑' m : ℕ+, x ^ ((m : ℕ) ^ 2) with hS
  have hsP : Summable fun m : ℕ+ => x ^ ((m : ℕ) ^ 2) := by
    have hg : Summable fun m : ℕ+ => |x| ^ (m : ℕ) :=
      (summable_geometric_of_lt_one (abs_nonneg x) hx).comp_injective PNat.coe_injective
    refine Summable.of_norm_bounded hg fun m => ?_
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_of_le_one (abs_nonneg x) hx.le (by nlinarith [m.pos])
  have hsucc : HasSum (fun n : ℕ => x ^ ((n + 1) ^ 2)) S :=
    (hasSum_pnat_iff_hasSum_succ (f := fun n : ℕ => x ^ (n ^ 2))).mp hsP.hasSum
  have hf1 : HasSum (fun n : ℕ => x ^ (((n : ℤ)).natAbs ^ 2)) (S + 1) := by
    have : HasSum (fun n : ℕ => x ^ (n ^ 2)) (S + 1) := by
      refine (hasSum_nat_add_iff' (f := fun n : ℕ => x ^ (n ^ 2)) 1).mp ?_
      rw [sum_range_one]
      convert hsucc using 1
      simp
    exact this.congr_fun fun n => by simp
  have hf2 : HasSum (fun n : ℕ => x ^ ((-((n : ℤ) + 1)).natAbs ^ 2)) S := by
    refine hsucc.congr_fun fun n => ?_
    have : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
    simp only [this]
  rw [(HasSum.of_nat_of_neg_add_one (f := fun m : ℤ => x ^ (m.natAbs ^ 2)) hf1 hf2).tsum_eq]
  ring

/-- **Theorem 312** (Jacobi; Hardy–Wright). For `|x| < 1`,
`(1 + 2x + 2x⁴ + 2x⁹ + ⋯)² = 1 + 4 (x/(1-x) - x³/(1-x³) + x⁵/(1-x⁵) - ⋯)`. -/
@[kb "hardywright2008" "Thm 312, p. 359"]
theorem jacobi_theta_sq {x : ℝ} (hx : |x| < 1) :
    (1 + 2 * ∑' m : ℕ+, x ^ ((m : ℕ) ^ 2)) ^ 2 =
      1 + 4 * ∑' n : ℕ+, (chi4 n : ℝ) * x ^ (n : ℕ) / (1 - x ^ (n : ℕ)) := by
  rw [← tsum_int_theta hx, ← (hasSum_sumTwoSquaresCount_mul_pow_nat hx).tsum_eq,
    (hasSum_sumTwoSquaresCount_mul_pow_nat hx).summable.tsum_eq_zero_add,
    ← (hasSum_sumTwoSquaresCount_mul_pow hx).tsum_eq, sumTwoSquaresCount_zero]
  have hp := (hasSum_pnat_iff_hasSum_succ (f := fun n : ℕ => (sumTwoSquaresCount n : ℝ) * x ^ n)).mpr
    ((hasSum_sumTwoSquaresCount_mul_pow_nat hx).summable.comp_injective
      (add_left_injective 1)).hasSum
  rw [hp.tsum_eq]
  simp

end NTKB.HardyWright
