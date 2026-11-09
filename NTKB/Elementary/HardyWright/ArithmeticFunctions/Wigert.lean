/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.ArithmeticFunctions.Order
import NTKB.Attr
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Hardy–Wright, Theorem 317 (Wigert): the maximal order of `d(n)`

`limsup log d(n) log log n / log n = log 2`: for every `ε > 0`,
`d(n) < 2^{(1+ε) log n / log log n}` for all large `n`, and
`d(n) > 2^{(1-ε) log n / log log n}` for infinitely many `n`.

Proof as in the book (§ 18.1). The upper bound: for every `δ > 0`,
`log d(n) ≤ δ log n + 2^{1/δ}/(δ log 2)` (18.1.3), applied with `δ = (1 + ε/2) log 2 / log log n`.
The lower bound: `n` the product of the primes `≤ P`, so `d(n) = 2^{π(P)}` and `log n = θ(P)`, with
Chebyshev's lower bound `θ(P) ≥ A P` (the book's Theorem 414; Mathlib's `Chebyshev.theta_ge`).
-/

open Finset Filter Topology Asymptotics Real
open scoped ArithmeticFunction.sigma

namespace NTKB.HardyWright

/-- The local factor bound of (18.1.3): for `p ≥ 2`, `a ≥ 1`, `δ > 0`,
`(a+1)/p^{aδ} ≤ 1` if `p^δ ≥ 2`, and `≤ 1 + 1/(δ log 2)` in any case. -/
lemma local_factor_le {p a : ℕ} (hp : 2 ≤ p) {δ : ℝ} (hδ : 0 < δ) :
    ((a : ℝ) + 1) / ((p : ℝ) ^ δ) ^ a ≤ if 2 ≤ (p : ℝ) ^ δ then 1 else 1 + 1 / (δ * log 2) := by
  have hlog2 : 0 < log 2 := log_pos one_lt_two
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hq1 : (2 : ℝ) ^ δ ≤ (p : ℝ) ^ δ := rpow_le_rpow (by norm_num) hp' hδ.le
  have hqpos : 0 < (p : ℝ) ^ δ := rpow_pos_of_pos (by linarith) δ
  split_ifs with h
  · rw [div_le_one (pow_pos hqpos a)]
    calc (a : ℝ) + 1 ≤ 2 ^ a := by
          have := Nat.lt_two_pow_self (n := a)
          exact_mod_cast this
      _ ≤ ((p : ℝ) ^ δ) ^ a := pow_le_pow_left₀ (by norm_num) h a
  · -- `p^{aδ} ≥ 2^{aδ} = e^{aδ log 2} ≥ 1 + aδ log 2`
    have hc : 0 < δ * log 2 := mul_pos hδ hlog2
    have h1 : 1 + a * (δ * log 2) ≤ ((p : ℝ) ^ δ) ^ a := by
      calc 1 + a * (δ * log 2) ≤ exp (a * (δ * log 2)) := by linarith [add_one_le_exp (a * (δ * log 2))]
        _ = ((2 : ℝ) ^ δ) ^ a := by
            rw [← rpow_natCast, ← rpow_mul (by norm_num), rpow_def_of_pos (by norm_num)]
            ring_nf
        _ ≤ ((p : ℝ) ^ δ) ^ a := pow_le_pow_left₀ (by positivity) hq1 a
    have h2 : 0 < 1 + a * (δ * log 2) := by positivity
    calc ((a : ℝ) + 1) / ((p : ℝ) ^ δ) ^ a ≤ ((a : ℝ) + 1) / (1 + a * (δ * log 2)) :=
          div_le_div_of_nonneg_left (by positivity) h2 h1
      _ ≤ 1 + 1 / (δ * log 2) := by
          rw [div_le_iff₀ h2]
          have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
          field_simp
          nlinarith [mul_nonneg this (mul_nonneg hc.le hc.le)]

/-- (18.1.3) with `δ` free: for `δ > 0` and `n ≥ 1`,
`log d(n) ≤ δ log n + 2^{1/δ}/(δ log 2)`. -/
theorem log_card_divisors_le {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : 0 < n) :
    log (σ 0 n) ≤ δ * log n + (2 : ℝ) ^ (1 / δ) / (δ * log 2) := by
  have hlog2 : 0 < log 2 := log_pos one_lt_two
  set K : ℝ := 1 + 1 / (δ * log 2) with hK
  have hK1 : 1 ≤ K := by rw [hK]; have : 0 < 1 / (δ * log 2) := by positivity
                         linarith
  have hn0 : n ≠ 0 := hn.ne'
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hnδ : 0 < (n : ℝ) ^ δ := rpow_pos_of_pos hnr δ
  -- `d(n)/n^δ = ∏ (a+1)/p^{aδ}`
  have hprod : (σ 0 n : ℝ) / (n : ℝ) ^ δ = ∏ p ∈ n.primeFactors,
      ((n.factorization p : ℝ) + 1) / ((p : ℝ) ^ δ) ^ (n.factorization p) := by
    rw [← divisorCountDivRpow_apply, (isMultiplicative_divisorCountDivRpow δ).multiplicative_factorization
      _ hn0, Finsupp.prod, Nat.support_factorization]
    refine prod_congr rfl fun p hp => ?_
    have hpp := Nat.prime_of_mem_primeFactors hp
    rw [divisorCountDivRpow_apply, ArithmeticFunction.sigma_zero_apply_prime_pow hpp]
    push_cast
    congr 1
    rw [← rpow_natCast, ← rpow_natCast, ← rpow_mul (Nat.cast_nonneg p),
      ← rpow_mul (Nat.cast_nonneg p), mul_comm]
  -- each factor is at most `1` or `K`
  set T : Finset ℕ := n.primeFactors.filter fun p => ¬ 2 ≤ ((p : ℕ) : ℝ) ^ δ with hT
  have hbound : (σ 0 n : ℝ) / (n : ℝ) ^ δ ≤ K ^ #T := by
    rw [hprod]
    calc ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) / ((p : ℝ) ^ δ) ^ (n.factorization p)
        ≤ ∏ p ∈ n.primeFactors, (if 2 ≤ (p : ℝ) ^ δ then 1 else K) :=
          prod_le_prod₀ (fun p _ => by positivity) fun p hp =>
            local_factor_le (Nat.prime_of_mem_primeFactors hp).two_le hδ
      _ = K ^ #T := by
          rw [prod_ite, prod_const_one, one_mul, prod_const]
  -- there are at most `2^{1/δ}` primes `p` with `p^δ < 2`
  have hTcard : (#T : ℝ) ≤ (2 : ℝ) ^ (1 / δ) := by
    have hsub : T ⊆ Icc 1 ⌊(2 : ℝ) ^ (1 / δ)⌋₊ := by
      intro p hp
      simp only [hT, mem_filter, not_le] at hp
      have hpp := Nat.prime_of_mem_primeFactors hp.1
      simp only [mem_Icc]
      refine ⟨hpp.one_le, Nat.le_floor ?_⟩
      have : (p : ℝ) = ((p : ℝ) ^ δ) ^ (1 / δ) := by
        rw [← rpow_mul (Nat.cast_nonneg p), mul_one_div_cancel hδ.ne', rpow_one]
      rw [this]
      exact (rpow_le_rpow (by positivity) hp.2.le (by positivity))
    calc (#T : ℝ) ≤ #(Icc 1 ⌊(2 : ℝ) ^ (1 / δ)⌋₊) := by exact_mod_cast card_le_card hsub
      _ = ⌊(2 : ℝ) ^ (1 / δ)⌋₊ := by simp
      _ ≤ (2 : ℝ) ^ (1 / δ) := Nat.floor_le (by positivity)
  -- take logarithms
  have hd : (0 : ℝ) < σ 0 n := by exact_mod_cast ArithmeticFunction.sigma_pos 0 n hn0
  have h1 : log ((σ 0 n : ℝ) / (n : ℝ) ^ δ) ≤ #T * log K := by
    rw [← log_pow]
    exact log_le_log (div_pos hd hnδ) hbound
  rw [log_div hd.ne' hnδ.ne', log_rpow hnr] at h1
  have hlogK : log K ≤ 1 / (δ * log 2) := by
    have := log_le_sub_one_of_pos (by linarith : 0 < K)
    rw [hK] at this ⊢; linarith
  have hlogK0 : 0 ≤ log K := log_nonneg hK1
  calc log (σ 0 n) ≤ δ * log n + #T * log K := by linarith
    _ ≤ δ * log n + (2 : ℝ) ^ (1 / δ) * (1 / (δ * log 2)) := by
        gcongr
    _ = δ * log n + (2 : ℝ) ^ (1 / δ) / (δ * log 2) := by ring

/-- **Theorem 317** (Wigert; Hardy–Wright), upper half: for every `ε > 0`,
`d(n) < 2^{(1+ε) log n / log log n}` for all large `n`, i.e.
`log d(n) < (1 + ε) log 2 · log n / log log n`. -/
@[kb "hardywright2008" "Thm 317, p. 364"]
theorem eventually_log_card_divisors_lt {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, log (σ 0 n) < (1 + ε) * log 2 * log n / log (log n) := by
  have hlog2 : 0 < log 2 := log_pos one_lt_two
  set ε' := ε / 2 with hε'
  have hε'0 : 0 < ε' := by rw [hε']; linarith
  set θ := 1 / (1 + ε') with hθ
  have hθ1 : θ < 1 := by rw [hθ, div_lt_one (by linarith)]; linarith
  have hθ0 : 0 < θ := by rw [hθ]; positivity
  set c := ε' * (1 + ε') * log 2 ^ 3 with hc
  have hc0 : 0 < c := by positivity
  -- `(log L)² ≤ (c/2) L^{1-θ}` for large `L`
  have hlo := (isLittleO_log_rpow_rpow_atTop 2 (by linarith : (0 : ℝ) < 1 - θ)).bound
    (by positivity : (0 : ℝ) < c / 2)
  have hL : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hL.eventually hlo, hL.eventually (eventually_gt_atTop (exp 1)),
    eventually_gt_atTop 0] with n hn1 hn2 hn0
  set L := log (n : ℝ) with hLdef
  have hL1 : 1 < L := by
    have : 1 < exp 1 := by have := add_one_lt_exp (x := 1) one_ne_zero; linarith
    linarith
  have hLpos : 0 < L := by linarith
  set M := log L with hM
  have hMpos : 0 < M := log_pos hL1
  set δ := (1 + ε') * log 2 / M with hδ
  have hδ0 : 0 < δ := by positivity
  have hmain := log_card_divisors_le hδ0 hn0
  rw [← hLdef] at hmain
  -- `2^{1/δ} = L^θ` and `1/(δ log 2) = M/((1+ε') (log 2)²)`
  have h2 : (2 : ℝ) ^ (1 / δ) = L ^ θ := by
    rw [rpow_def_of_pos (by norm_num), rpow_def_of_pos hLpos, hδ, hθ]
    congr 1
    field_simp
    exact hM
  rw [h2] at hmain
  simp only [Real.norm_eq_abs] at hn1
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at hn1
  -- `L^θ M² ≤ (c/2) L`
  have h3 : L ^ θ * M ^ 2 ≤ c / 2 * L := by
    have : L ^ θ * L ^ (1 - θ) = L := by rw [← rpow_add hLpos]; simp
    calc L ^ θ * M ^ 2 ≤ L ^ θ * (c / 2 * L ^ (1 - θ)) := by
          have : (M : ℝ) ^ (2 : ℝ) = M ^ 2 := by norm_cast
          rw [← this]; gcongr
      _ = c / 2 * L := by rw [mul_left_comm, this]
  have hLθ : 0 < L ^ θ := rpow_pos_of_pos hLpos θ
  -- assemble
  have e1 : δ * L = (1 + ε') * log 2 * L / M := by rw [hδ]; ring
  have e2 : L ^ θ / (δ * log 2) = L ^ θ * M ^ 2 / ((1 + ε') * log 2 ^ 2 * M) := by
    rw [hδ]; field_simp
  rw [e1, e2] at hmain
  have h4 : L ^ θ * M ^ 2 / ((1 + ε') * log 2 ^ 2 * M) < ε' * log 2 * L / M := by
    rw [div_lt_div_iff₀ (by positivity) hMpos]
    have : c / 2 * L < c * L := by nlinarith
    calc L ^ θ * M ^ 2 * M ≤ c / 2 * L * M := by gcongr
      _ < c * L * M := by nlinarith
      _ = ε' * log 2 * L * ((1 + ε') * log 2 ^ 2 * M) := by rw [hc]; ring
  calc log (σ 0 n) ≤ (1 + ε') * log 2 * L / M + L ^ θ * M ^ 2 / ((1 + ε') * log 2 ^ 2 * M) :=
        hmain
    _ < (1 + ε') * log 2 * L / M + ε' * log 2 * L / M := by linarith
    _ = (1 + ε) * log 2 * L / M := by rw [hε']; ring

/-- `d(p₁ p₂ ⋯ p_r) = 2^r` for the product of the primes `≤ P`. -/
lemma card_divisors_primorial (P : ℕ) : σ 0 (primorial P) = 2 ^ Nat.primeCounting P := by
  rw [primorial, ArithmeticFunction.isMultiplicative_sigma.map_prod_of_prime _
    (fun p hp => (mem_filter.mp hp).2)]
  rw [prod_congr rfl fun p hp => by
    rw [ArithmeticFunction.sigma_zero_apply, Nat.Prime.divisors (mem_filter.mp hp).2,
      card_pair (mem_filter.mp hp).2.one_lt.ne]]
  rw [prod_const, ← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_range]

/-- Chebyshev: `θ(x) ≥ (log 2 / 2) x` for large `x`. -/
lemma eventually_theta_ge :
    ∀ᶠ P : ℕ in atTop, log 2 / 2 * P ≤ Chebyshev.theta P := by
  have hlog2 : 0 < log 2 := log_pos one_lt_two
  -- `log (P + 1) + 2 √P log P = o(P)`
  have h1 : (fun x : ℝ => log x) =o[atTop] fun x => x := isLittleO_log_id_atTop
  have h2 : (fun x : ℝ => √x * log x) =o[atTop] fun x => x := by
    have h3 : (fun x : ℝ => log x) =o[atTop] fun x => x ^ (1 / 2 : ℝ) :=
      isLittleO_log_rpow_atTop (by norm_num)
    have h4 := (isBigO_refl (fun x : ℝ => √x) atTop).mul_isLittleO h3
    refine h4.congr' (Eventually.of_forall fun x => rfl) ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [sqrt_eq_rpow, ← rpow_add hx]; norm_num
  have hb := ((h1.add (h2.const_mul_left 2)).bound (by positivity : (0 : ℝ) < log 2 / 4))
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hb,
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (4 : ℝ))] with P hP hP4
  have hθ := Chebyshev.theta_ge P
  simp only [Real.norm_eq_abs] at hP
  have hPr : (4 : ℝ) ≤ P := hP4
  have hlogP : 0 ≤ log (P : ℝ) := log_nonneg (by linarith)
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by linarith)] at hP
  have hlog1 : log ((P : ℝ) + 1) ≤ log 2 + log P := by
    rw [← log_mul (by norm_num) (by linarith)]
    exact log_le_log (by linarith) (by linarith)
  nlinarith

/-- **Theorem 317** (Wigert; Hardy–Wright), lower half: for every `ε > 0`,
`d(n) > 2^{(1-ε) log n / log log n}` for infinitely many `n` (`n` the product of the first primes),
i.e. `log d(n) > (1 - ε) log 2 · log n / log log n` frequently. -/
@[kb "hardywright2008" "Thm 317, p. 364"]
theorem frequently_log_card_divisors_gt {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ n : ℕ in atTop, (1 - ε) * log 2 * log n / log (log n) < log (σ 0 n) := by
  have hlog2 : 0 < log 2 := log_pos one_lt_two
  set A := log 2 / 2 with hA
  have hA0 : 0 < A := by positivity
  set B := -log A with hB
  have hθ : Tendsto (fun P : ℕ => Chebyshev.theta P) atTop atTop := by
    refine tendsto_atTop_mono' atTop eventually_theta_ge ?_
    exact (tendsto_natCast_atTop_atTop.const_mul_atTop hA0)
  have hM : Tendsto (fun P : ℕ => log (Chebyshev.theta P)) atTop atTop :=
    tendsto_log_atTop.comp hθ
  rw [frequently_atTop]
  intro N
  obtain ⟨P, hP⟩ := (eventually_theta_ge.and ((hM.eventually (eventually_gt_atTop
    (max (|B| / ε) 1))).and ((hθ.eventually (eventually_gt_atTop (log N))).and
      (eventually_ge_atTop 2)))).exists
  obtain ⟨hθP, hMP, hlogN, hP2⟩ := hP
  set n := primorial P
  have hlogn : log (n : ℝ) = Chebyshev.theta P := by
    rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast]
  refine ⟨n, ?_, ?_⟩
  · -- `n ≥ N`
    have : log (N : ℝ) < log n := by rw [hlogn]; exact hlogN
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [h]; exact Nat.zero_le _
    have := (log_lt_log_iff (by exact_mod_cast h) (by exact_mod_cast primorial_pos P)).mp this
    exact_mod_cast this.le
  · set L := Chebyshev.theta P
    set M := log L
    have hMpos : 1 < M := lt_of_le_of_lt (le_max_right _ _) hMP
    have hP2r : (2 : ℝ) ≤ P := by exact_mod_cast hP2
    have hLpos : 0 < L := lt_of_lt_of_le (by positivity) hθP
    have hB0 : 0 < B := by
      rw [hB, neg_pos]
      exact log_neg hA0 (by rw [hA]; linarith [log_two_lt_d9])
    rw [hlogn, card_divisors_primorial, Nat.cast_pow, Nat.cast_ofNat, log_pow]
    -- `θ(P) ≤ π(P) log P` and `log P ≤ log θ(P) - log A`
    have hθπ := Chebyshev.theta_le_pi_mul_log P
    have hlogP : 0 < log (P : ℝ) := log_pos (by linarith)
    have hlogPM : log (P : ℝ) ≤ M + B := by
      have : (P : ℝ) ≤ L / A := by rw [le_div_iff₀ hA0, hA]; linarith
      have := log_le_log (by linarith) this
      rw [log_div hLpos.ne' hA0.ne'] at this
      rw [hB]; linarith
    have hπ : L / (M + B) ≤ (Nat.primeCounting P : ℝ) := by
      rw [div_le_iff₀ (by linarith)]
      calc L ≤ Nat.primeCounting P * log (P : ℝ) := hθπ
        _ ≤ Nat.primeCounting P * (M + B) := by gcongr
    have hkey : (1 - ε) * (M + B) < M := by
      have hMB : |B| / ε < M := lt_of_le_of_lt (le_max_left _ _) hMP
      rw [div_lt_iff₀ hε] at hMB
      rw [abs_of_pos hB0] at hMB
      rcases le_or_gt 1 ε with h1 | h1
      · nlinarith
      · nlinarith
    calc (1 - ε) * log 2 * L / M < log 2 * (L / (M + B)) := by
          rw [div_lt_iff₀ (by linarith), mul_assoc, mul_div_assoc', div_mul_eq_mul_div,
            lt_div_iff₀ (by linarith)]
          have : 0 < log 2 * L := by positivity
          nlinarith
      _ ≤ log 2 * Nat.primeCounting P := by gcongr
      _ = Nat.primeCounting P * log 2 := by ring

/-- **Theorem 317** (Wigert; Hardy–Wright). `limsup log d(n) log log n / log n = log 2`. -/
@[kb "hardywright2008" "Thm 317, p. 364"]
theorem limsup_log_card_divisors :
    limsup (fun n : ℕ => log (σ 0 n) * log (log n) / log n) atTop = log 2 := by
  have hlog2 : 0 < log 2 := log_pos one_lt_two
  set f := fun n : ℕ => log (σ 0 n) * log (log n) / log n with hf
  -- for large `n`, `log n > 1`, `log log n > 0`
  have hL : ∀ᶠ n : ℕ in atTop, 1 < log (n : ℝ) :=
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_gt_atTop 1)
  have hup : ∀ ε > 0, ∀ᶠ n in atTop, f n ≤ (1 + ε) * log 2 := by
    intro ε hε
    filter_upwards [eventually_log_card_divisors_lt hε, hL] with n hn hn1
    have hM : 0 < log (log (n : ℝ)) := log_pos hn1
    simp only [hf]
    rw [div_le_iff₀ (by linarith)]
    rw [lt_div_iff₀ hM] at hn
    nlinarith
  have hnonneg : ∀ᶠ n in atTop, 0 ≤ f n := by
    filter_upwards [hL, eventually_gt_atTop 0] with n hn1 hn0
    have hd : (1 : ℝ) ≤ σ 0 n := by exact_mod_cast ArithmeticFunction.sigma_pos 0 n hn0.ne'
    have : 0 ≤ log (σ 0 n : ℝ) := log_nonneg hd
    have : 0 < log (log (n : ℝ)) := log_pos hn1
    simp only [hf]; positivity
  have hbdd : IsBoundedUnder (· ≤ ·) atTop f :=
    isBoundedUnder_of_eventually_le (hup 1 one_pos)
  have hcobdd : IsCoboundedUnder (· ≤ ·) atTop f :=
    (isBoundedUnder_of_eventually_ge hnonneg).isCoboundedUnder_le
  apply le_antisymm
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have := limsup_le_of_le hcobdd (hup (ε / log 2) (by positivity))
    calc limsup f atTop ≤ (1 + ε / log 2) * log 2 := this
      _ = log 2 + ε := by field_simp
  · refine le_of_forall_sub_le fun ε hε => ?_
    refine le_limsup_of_frequently_le ?_ hbdd
    have hfr := frequently_log_card_divisors_gt (ε := ε / log 2) (by positivity)
    refine (hfr.and_eventually hL).mono fun n ⟨hn, hn1⟩ => ?_
    have hM : 0 < log (log (n : ℝ)) := log_pos hn1
    simp only [hf]
    rw [le_div_iff₀ (by linarith)]
    rw [div_lt_iff₀ hM] at hn
    have : (log 2 - ε) = (1 - ε / log 2) * log 2 := by field_simp
    rw [this]
    nlinarith

end NTKB.HardyWright
