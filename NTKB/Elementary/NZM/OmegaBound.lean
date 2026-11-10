/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.NZM.TotientSums
import NTKB.Elementary.HardyWright.PrimeDistribution.Elementary
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Primorial
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import NTKB.Attr

/-!
# The maximal order of `ω(n)` (Niven–Zuckerman–Montgomery, Theorem 8.30)

For every `ε > 0`, `ω(n) < (1 + ε) log n / log log n` for all large `n`, and
`ω(n) > (1 - ε) log n / log log n` for infinitely many `n`.

The proof follows the book: the extremal integers are the primorials `P_y = ∏_{p ≤ y} p`, with
`log P_y = θ(y)` and `ω(P_y) = π(y)`.  Only Chebyshev-type input is needed (not the prime number
theorem): `θ(y) ≍ y` and `π(y) = θ(y)/log y + O(y / log² y)`, which together give
`π(y) log θ(y) / θ(y) → 1` (`tendsto_primeCounting_log_theta_div_theta`).

* `omega_lt_of_large` is the upper bound, `omega_gt_infinitely_often` the lower bound, and
  `omegaOrderStatement` is `OmegaOrderStatement` itself.
-/

open Finset Real Chebyshev Filter
open scoped Topology

namespace NTKB.NZM

/-! ## The key limit -/

/-- `π(x) log θ(x) / θ(x) → 1`; this is (8.53) of the book in the form needed here. -/
theorem tendsto_primeCounting_log_theta_div_theta :
    Tendsto (fun x : ℝ ↦ (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log (θ x) / θ x) atTop (𝓝 1) := by
  obtain ⟨A, hA, B, hB, hAB⟩ := NTKB.HardyWright.theta_psi_order
  obtain ⟨C, hC⟩ := primeCounting_sub_theta_div_log_isBigO
  set M : ℝ := |Real.log A| + |Real.log B| with hM
  have hM0 : 0 ≤ M := by positivity
  have hC' : ∀ᶠ x : ℝ in atTop, |(Nat.primeCounting ⌊x⌋₊ : ℝ) - θ x / Real.log x| ≤
      max C 0 * (x / Real.log x ^ 2) := by
    filter_upwards [hC.bound, eventually_gt_atTop 1] with x hx hx1
    have hl : 0 < Real.log x := Real.log_pos hx1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < x / Real.log x ^ 2)]
      at hx
    exact hx.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hlogθ : ∀ x : ℝ, 2 ≤ x → |Real.log (θ x) - Real.log x| ≤ M := by
    intro x hx
    obtain ⟨⟨h1, h2⟩, -⟩ := hAB x hx
    have hx0 : 0 < x := by linarith
    have e1 : Real.log (A * x) ≤ Real.log (θ x) := Real.log_le_log (by positivity) h1.le
    have e2 : Real.log (θ x) ≤ Real.log (B * x) :=
      Real.log_le_log (by nlinarith) h2.le
    rw [Real.log_mul hA.ne' hx0.ne'] at e1
    rw [Real.log_mul hB.ne' hx0.ne'] at e2
    rw [abs_le]
    have := neg_abs_le (Real.log A)
    have := le_abs_self (Real.log B)
    have := abs_nonneg (Real.log A)
    have := abs_nonneg (Real.log B)
    constructor <;> linarith
  have hlim1 : Tendsto (fun x : ℝ ↦ Real.log (θ x) / Real.log x) atTop (𝓝 1) := by
    rw [← tendsto_sub_nhds_zero_iff]
    refine squeeze_zero_norm' ?_ ((tendsto_const_nhds (x := M)).div_atTop Real.tendsto_log_atTop)
    filter_upwards [eventually_ge_atTop 2] with x hx
    have hl : 0 < Real.log x := Real.log_pos (by linarith)
    have : Real.log (θ x) / Real.log x - 1 = (Real.log (θ x) - Real.log x) / Real.log x := by
      field_simp
    rw [this, Real.norm_eq_abs, abs_div, abs_of_pos hl]
    exact div_le_div_of_nonneg_right (hlogθ x hx) hl.le
  have hlim2 : Tendsto (fun x : ℝ ↦
      ((Nat.primeCounting ⌊x⌋₊ : ℝ) - θ x / Real.log x) * Real.log (θ x) / θ x) atTop (𝓝 0) := by
    have hl1 := (tendsto_const_nhds (x := (1 : ℝ))).div_atTop Real.tendsto_log_atTop
    have hl2 : Tendsto (fun x : ℝ ↦ M / Real.log x ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop two_ne_zero).comp Real.tendsto_log_atTop)
    have hT := ((hl1.add hl2).const_mul (max C 0 / A))
    rw [add_zero, mul_zero] at hT
    refine squeeze_zero_norm' ?_ hT
    filter_upwards [hC', eventually_ge_atTop 2] with x hE hx
    obtain ⟨⟨h1, -⟩, -⟩ := hAB x hx
    have hx0 : 0 < x := by linarith
    have hl : 0 < Real.log x := Real.log_pos (by linarith)
    have hAx : 0 < A * x := by positivity
    have hθ0 : 0 < θ x := hAx.trans h1
    have hlg := hlogθ x hx
    have hlg' : |Real.log (θ x)| ≤ Real.log x + M := by
      have := abs_le.1 hlg
      rw [abs_le]
      constructor <;> linarith [this.1, this.2]
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hθ0]
    calc |(Nat.primeCounting ⌊x⌋₊ : ℝ) - θ x / Real.log x| * |Real.log (θ x)| / θ x
        ≤ (max C 0 * (x / Real.log x ^ 2)) * (Real.log x + M) / (A * x) := by
          gcongr <;> first | exact hE | exact hlg' | exact h1.le
      _ = max C 0 / A * (1 / Real.log x + M / Real.log x ^ 2) := by
          field_simp
  have := hlim1.add hlim2
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with x hx
  obtain ⟨⟨h1, -⟩, -⟩ := hAB x hx
  have hl : Real.log x ≠ 0 := (Real.log_pos (by linarith)).ne'
  have hθ0 : θ x ≠ 0 := (lt_trans (by positivity : 0 < A * x) h1).ne'
  field_simp
  ring

/-- The natural-number form of `tendsto_primeCounting_log_theta_div_theta`. -/
theorem tendsto_primeCounting_log_theta_div_theta_nat :
    Tendsto (fun y : ℕ ↦ (Nat.primeCounting y : ℝ) * Real.log (θ y) / θ y) atTop (𝓝 1) := by
  have h := tendsto_primeCounting_log_theta_div_theta.comp tendsto_natCast_atTop_atTop
  refine h.congr fun y ↦ ?_
  simp [Nat.floor_natCast]

/-! ## Helper lemmas -/

theorem sum_eq_sdiff_add_inter (S P : Finset ℕ) (f : ℕ → ℝ) :
    ∑ p ∈ S, f p = ∑ p ∈ S \ P, f p + ∑ p ∈ S ∩ P, f p := by
  have := Finset.sum_sdiff (f := f) (Finset.inter_subset_left (s₁ := S) (s₂ := P))
  rw [Finset.sdiff_inter_self_left] at this
  linarith

/-- If `S` is a set of primes with the same cardinality as the set of primes `≤ y`, then
`θ(y) ≤ ∑_{p ∈ S} log p`: the product of the first `k` primes is the smallest product of `k`
distinct primes. -/
theorem theta_le_sum_log {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (y : ℕ)
    (hcard : S.card = Nat.primeCounting y) : θ y ≤ ∑ p ∈ S, Real.log p := by
  set P := Nat.primesLE y with hP
  have hPc : P.card = S.card := by rw [hcard, Nat.primesLE_card_eq_primeCounting]
  rw [theta_eq_sum_primesLE_log, ← hP]
  have hc : (S \ P).card = (P \ S).card := by
    have h1 := Finset.card_sdiff_add_card_inter S P
    have h2 := Finset.card_sdiff_add_card_inter P S
    rw [Finset.inter_comm] at h2
    omega
  have e1 := sum_eq_sdiff_add_inter S P (fun p : ℕ ↦ Real.log p)
  have e2 := sum_eq_sdiff_add_inter P S (fun p : ℕ ↦ Real.log p)
  rw [Finset.inter_comm] at e2
  have hlow : (S \ P).card • Real.log y ≤ ∑ p ∈ S \ P, Real.log p := by
    refine Finset.card_nsmul_le_sum _ _ _ fun p hp ↦ ?_
    rw [Finset.mem_sdiff, hP, Nat.mem_primesLE] at hp
    have hyp : y ≤ p := by
      by_contra hlt
      exact hp.2 ⟨by omega, hS p hp.1⟩
    rcases Nat.eq_zero_or_pos y with h0 | h0
    · subst h0
      simpa using Real.log_natCast_nonneg p
    · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hyp)
  have hup : ∑ p ∈ P \ S, Real.log p ≤ (P \ S).card • Real.log y := by
    refine Finset.sum_le_card_nsmul _ _ _ fun p hp ↦ ?_
    rw [Finset.mem_sdiff, hP, Nat.mem_primesLE] at hp
    exact Real.log_le_log (by exact_mod_cast hp.1.2.pos) (by exact_mod_cast hp.1.1)
  rw [hc] at hlow
  linarith

/-- `∑_{p ∣ n} log p ≤ log n`. -/
theorem sum_log_primeFactors_le {n : ℕ} (hn : 0 < n) :
    ∑ p ∈ n.primeFactors, Real.log p ≤ Real.log n := by
  have hne : ∀ p ∈ n.primeFactors, (p : ℝ) ≠ 0 := fun p hp ↦
    Nat.cast_ne_zero.2 (Nat.prime_of_mem_primeFactors hp).ne_zero
  rw [← Real.log_prod hne]
  have hpos : 0 < ∏ p ∈ n.primeFactors, (p : ℝ) :=
    Finset.prod_pos fun p hp ↦ by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  refine Real.log_le_log hpos ?_
  have := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
  have h2 : ((∏ p ∈ n.primeFactors, p : ℕ) : ℝ) ≤ n := by exact_mod_cast this
  simpa [Nat.cast_prod] using h2

/-- `u / log u` is increasing for `u ≥ e`. -/
theorem div_log_le_div_log {T L : ℝ} (hT : Real.exp 1 ≤ T) (hTL : T ≤ L) :
    T / Real.log T ≤ L / Real.log L := by
  have hT0 : 0 < T := (Real.exp_pos 1).trans_le hT
  have hL0 : 0 < L := hT0.trans_le hTL
  have hlT : 0 < Real.log T := Real.log_pos (lt_of_lt_of_le (Real.one_lt_exp_iff.2 one_pos) hT)
  have hlL : 0 < Real.log L := Real.log_pos (lt_of_lt_of_le (Real.one_lt_exp_iff.2 one_pos)
    (hT.trans hTL))
  have h := Real.log_div_self_antitoneOn hT (hT.trans hTL) hTL
  simp only at h
  rw [div_le_div_iff₀ hlT hlL]
  rw [div_le_div_iff₀ hL0 hT0] at h
  nlinarith

/-! ## The upper bound -/

/-- **NZM, Theorem 8.30 (upper bound).** For `ε > 0` and all large `n`,
`ω(n) < (1 + ε) log n / log log n`. -/
@[kb "nivenzuckermanmontgomery" "Thm 8.30, p. 394"]
theorem omega_lt_of_large {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ < n →
      (ArithmeticFunction.cardDistinctFactors n : ℝ) <
        (1 + ε) * Real.log n / Real.log (Real.log n) := by
  obtain ⟨A, hA, B, hB, hAB⟩ := NTKB.HardyWright.theta_psi_order
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.1
    (tendsto_primeCounting_log_theta_div_theta_nat.eventually (gt_mem_nhds
      (by linarith : (1 : ℝ) < 1 + ε / 2)))
  -- θ y is large for large y
  obtain ⟨Y₁, hY₁⟩ := Filter.eventually_atTop.1
    ((tendsto_natCast_atTop_atTop.const_mul_atTop hA).eventually_gt_atTop (Real.exp 1))
  set K : ℕ := max (max Y₀ Y₁) 2 + 1 with hK
  -- L / log L is large for large L
  obtain ⟨X₁, hX₁⟩ := Filter.eventually_atTop.1
    ((Real.isLittleO_log_id_atTop.bound (c := 1 / ((K : ℝ) + 2)) (by positivity)).and
      (eventually_gt_atTop (Real.exp 1)))
  refine ⟨⌈Real.exp (max X₁ 1)⌉₊, fun n hn ↦ ?_⟩
  have hnR : Real.exp (max X₁ 1) < n := by
    have := Nat.lt_of_ceil_lt hn
    exact this
  have hn0 : 0 < n := by
    have : (0 : ℝ) < n := (Real.exp_pos _).trans hnR
    exact_mod_cast this
  set L := Real.log n with hL
  have hLX : max X₁ 1 < L := by
    rw [hL]; exact (Real.lt_log_iff_exp_lt (by exact_mod_cast hn0)).2 hnR
  obtain ⟨hLbd, hLe⟩ := hX₁ L ((le_max_left _ _).trans hLX.le)
  have hLpos : 0 < L := by linarith [le_max_right X₁ 1]
  have hlogL : 0 < Real.log L := Real.log_pos (by linarith [le_max_right X₁ 1])
  have hbig : (K : ℝ) + 1 < L / Real.log L := by
    simp only [id] at hLbd
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlogL, abs_of_pos hLpos] at hLbd
    rw [lt_div_iff₀ hlogL]
    have h1 : ((K : ℝ) + 2) * Real.log L ≤ L := by
      have := mul_le_mul_of_nonneg_left hLbd (by positivity : (0 : ℝ) ≤ (K : ℝ) + 2)
      have e : ((K : ℝ) + 2) * (1 / ((K : ℝ) + 2) * L) = L := by field_simp
      linarith
    nlinarith
  have hpos : 0 < L / Real.log L := by positivity
  set k := ArithmeticFunction.cardDistinctFactors n with hk
  by_cases hsmall : k ≤ K
  · calc (k : ℝ) ≤ K := by exact_mod_cast hsmall
      _ < L / Real.log L := by linarith
      _ ≤ (1 + ε) * L / Real.log L := by
          rw [mul_div_assoc]
          nlinarith
  · push Not at hsmall
    obtain ⟨y, hy⟩ := Nat.surjective_primeCounting k
    have hyk : k ≤ y + 1 := by
      rw [← hy, ← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_range]
      calc (Finset.filter Nat.Prime (Finset.range (y + 1))).card
          ≤ (Finset.range (y + 1)).card := Finset.card_filter_le _ _
        _ = y + 1 := Finset.card_range _
    have hyY : max (max Y₀ Y₁) 2 ≤ y := by omega
    have hy0 : Y₀ ≤ y := (le_max_left _ _).trans ((le_max_left _ _).trans hyY)
    have hy1 : Y₁ ≤ y := (le_max_right _ _).trans ((le_max_left _ _).trans hyY)
    have hy2 : 2 ≤ y := (le_max_right _ _).trans hyY
    set T := θ y with hT
    have hTe : Real.exp 1 < T := by
      have h1 := hY₁ y hy1
      have h2 := (hAB (y : ℝ) (by exact_mod_cast hy2)).1.1
      linarith
    have hlogT : 0 < Real.log T := Real.log_pos (lt_of_lt_of_le (Real.one_lt_exp_iff.2 one_pos)
      hTe.le)
    have hT0 : 0 < T := (Real.exp_pos 1).trans hTe
    have hlim := hY₀ y hy0
    have hcard : n.primeFactors.card = Nat.primeCounting y := by
      rw [hy, hk, ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors]
    have hTL : T ≤ L := (theta_le_sum_log (fun p hp ↦ Nat.prime_of_mem_primeFactors hp) y
      hcard).trans (sum_log_primeFactors_le hn0)
    have hk1 : (k : ℝ) < (1 + ε / 2) * (T / Real.log T) := by
      rw [hy] at hlim
      rw [div_lt_iff₀ hT0] at hlim
      rw [mul_div_assoc', lt_div_iff₀ hlogT]
      linarith
    have h2 := div_log_le_div_log hTe.le hTL
    calc (k : ℝ) < (1 + ε / 2) * (T / Real.log T) := hk1
      _ ≤ (1 + ε / 2) * (L / Real.log L) := by gcongr
      _ ≤ (1 + ε) * L / Real.log L := by
          rw [mul_div_assoc]
          nlinarith

/-! ## The lower bound -/

/-- **NZM, Theorem 8.30 (lower bound).** For `ε > 0`, `ω(n) > (1 - ε) log n / log log n` for
infinitely many `n` (namely for the primorials `n = ∏_{p ≤ y} p`, `y` large). -/
@[kb "nivenzuckermanmontgomery" "Thm 8.30, p. 394"]
theorem omega_gt_infinitely_often {ε : ℝ} (hε : 0 < ε) :
    {n : ℕ | (1 - ε) * Real.log n / Real.log (Real.log n) <
      (ArithmeticFunction.cardDistinctFactors n : ℝ)}.Infinite := by
  obtain ⟨A, hA, B, hB, hAB⟩ := NTKB.HardyWright.theta_psi_order
  refine Set.infinite_of_forall_exists_gt fun a ↦ ?_
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.1
    (tendsto_primeCounting_log_theta_div_theta_nat.eventually (lt_mem_nhds
      (by linarith : 1 - ε < 1)))
  obtain ⟨Y₁, hY₁⟩ := Filter.eventually_atTop.1
    ((tendsto_natCast_atTop_atTop.const_mul_atTop hA).eventually_gt_atTop
      (max (Real.exp 1) (Real.log a)))
  set y : ℕ := max (max Y₀ Y₁) 2 with hy
  have hy0 : Y₀ ≤ y := (le_max_left _ _).trans (le_max_left _ _)
  have hy1 : Y₁ ≤ y := (le_max_right _ _).trans (le_max_left _ _)
  have hy2 : 2 ≤ y := le_max_right _ _
  have hAy := hY₁ y hy1
  have hθ := (hAB (y : ℝ) (by exact_mod_cast hy2)).1.1
  set T := θ y with hT
  have hTe : Real.exp 1 < T := lt_of_le_of_lt (le_max_left _ _) (hAy.trans hθ)
  have hTa : Real.log a < T := lt_of_le_of_lt (le_max_right _ _) (hAy.trans hθ)
  have hlogT : 0 < Real.log T := Real.log_pos (lt_of_lt_of_le (Real.one_lt_exp_iff.2 one_pos)
    hTe.le)
  have hT0 : 0 < T := (Real.exp_pos 1).trans hTe
  have hn : Real.log (primorial y) = T := by
    rw [hT, theta_eq_log_primorial, Nat.floor_natCast]
  have hω : ArithmeticFunction.cardDistinctFactors (primorial y) = Nat.primeCounting y := by
    rw [ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors, primeFactors_primorial,
      Nat.primesLE_card_eq_primeCounting]
  refine ⟨primorial y, ?_, ?_⟩
  · show (1 - ε) * Real.log (primorial y) / Real.log (Real.log (primorial y)) <
      (ArithmeticFunction.cardDistinctFactors (primorial y) : ℝ)
    rw [hn, hω]
    have h := hY₀ y hy0
    rw [lt_div_iff₀ hT0] at h
    rw [div_lt_iff₀ hlogT]
    linarith
  · by_contra hle
    push Not at hle
    have hpos : 0 < primorial y := by
      rw [primorial]
      exact Finset.prod_pos fun p hp ↦ (Finset.mem_filter.1 hp).2.pos
    have ha : 0 < a := lt_of_lt_of_le hpos hle
    have h1 : Real.log (primorial y) ≤ Real.log a :=
      Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hle)
    rw [hn] at h1
    linarith

/-- **NZM, Theorem 8.30.** `ω(n) < (1 + ε) log n / log log n` for large `n`, and
`ω(n) > (1 - ε) log n / log log n` infinitely often. -/
@[kb "nivenzuckermanmontgomery" "Thm 8.30, p. 394"]
theorem omegaOrderStatement : OmegaOrderStatement :=
  ⟨fun _ hε ↦ omega_lt_of_large hε, fun _ hε ↦ omega_gt_infinitely_often hε⟩

end NTKB.NZM
