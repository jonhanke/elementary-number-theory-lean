/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.PrimeDistribution.ElementaryPNT
import NTKB.Analytic.Apostol.Primes.PNTImpliesMertens
import NTKB.Analytic.Apostol.Primes.MertensSecond
import NTKB.Analytic.Apostol.PNT.MertensProduct

/-!
# The series and product of primes, and consequences of the prime number theorem
(Hardy–Wright, Chapter XXII, §§ 22.7, 22.17, 22.19)

* **Theorem 427**: `∑_{p ≤ x} 1/p = log log x + B₁ + o(1)` (from Apostol's Theorem 4.12);
* **§ 22.7**: `∏_{p ≤ x} (1 - 1/p) → 0` (from Apostol's Theorem 13.13, the Mertens product
  estimate) and `π(x) = o(x)`;
* **Theorem 335** (§ 22.17): `M(x) = o(x)`, from Apostol's Theorem 4.14 and the elementary
  Theorem 434 `ψ(x)/x → 1`;
* **Theorem 426**: the `liminf`/`limsup` of `π(x) log x / x` are `1` and the limit, if it exists,
  is `1` (consequence of the prime number theorem, Theorem 6);
* **(22.19.2)**, **(22.19.3)**: for `ε > 0` and large `x` there is a prime in `(x, (1+ε)x)`, and
  `(π(2x) - π(x)) / π(x) → 1`; both follow from `π(cx) / π(x) → c`, a consequence of Theorem 6.

All the uses of the prime number theorem go through the elementary
`NTKB.HardyWright.prime_number_theorem` and `tendsto_psi_div_self`.
-/

open Finset ArithmeticFunction Real Chebyshev Filter
open scoped Topology

namespace NTKB.HardyWright

open NTKB.Apostol

/-- **Theorem 427.** `∑_{p ≤ x} 1/p = log log x + B₁ + o(1)` for a constant `B₁`. -/
@[kb "hardywright2008" "Thm 427, p. 485"]
theorem tendsto_sum_inv_primes_sub_log_log :
    ∃ B₁ : ℝ, Tendsto
      (fun x : ℝ ↦ ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 : ℝ) / p - Real.log (Real.log x) - B₁)
      atTop (𝓝 0) := by
  obtain ⟨A, C, hA⟩ := apostol_thm_4_12
  refine ⟨A, squeeze_zero_norm' (a := fun x : ℝ ↦ C / Real.log x) ?_
    ((tendsto_const_nhds (x := C)).div_atTop Real.tendsto_log_atTop)⟩
  filter_upwards [eventually_ge_atTop 2] with x hx
  rw [Real.norm_eq_abs]; exact hA x hx

/-- **Section 22.7.** `∏_{p ≤ x} (1 - 1/p) → 0` as `x → ∞`, so that the product over all primes
diverges to `0`. -/
@[kb "hardywright2008" "Section 22.7, p. 483"]
theorem tendsto_prod_one_sub_inv_primes :
    Tendsto (fun x : ℝ ↦ ∏ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 - 1 / (p : ℝ))) atTop (𝓝 0) := by
  obtain ⟨c, -, C, hC⟩ := apostol_thm_13_13
  have hlog := Real.tendsto_log_atTop
  have h1 : Tendsto (fun x : ℝ ↦ c / Real.log x + C / Real.log x ^ 2) atTop (𝓝 0) := by
    have h2 : Tendsto (fun x : ℝ ↦ C / Real.log x ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop two_ne_zero).comp hlog)
    simpa using (tendsto_const_nhds.div_atTop hlog).add h2
  refine squeeze_zero_norm' ?_ h1
  filter_upwards [eventually_ge_atTop 2] with x hx
  have h := hC x hx
  have h' := abs_le.1 h
  have hm : 0 < mertensProd x := mertensProd_pos x
  show ‖mertensProd x‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_pos hm]
  linarith [h'.2]

/-- **Section 22.7** (consequence of Theorem 6). `π(x) = o(x)`, i.e. `π(x)/x → 0`. -/
@[kb "hardywright2008" "Section 22.7, p. 483"]
theorem tendsto_primeCounting_div_self :
    Tendsto (fun x : ℝ ↦ (Nat.primeCounting ⌊x⌋₊ : ℝ) / x) atTop (𝓝 0) := by
  have h := prime_number_theorem.mul
    ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop Real.tendsto_log_atTop)
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  have : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have : x ≠ 0 := by positivity
  field_simp

/-- **Theorem 335** (§ 22.17). `M(x) = ∑_{n ≤ x} μ(n) = o(x)`. -/
@[kb "hardywright2008" "Thm 335, p. 508"]
theorem tendsto_mertens_div_self : Tendsto (fun x : ℝ ↦ mertens x / x) atTop (𝓝 0) :=
  tendsto_mertens_div_of_psi tendsto_psi_div_self

/-- **Theorem 426.** `liminf π(x) log x / x ≤ 1 ≤ limsup π(x) log x / x` (in fact both equal `1`
by Theorem 6), and if `π(x) log x / x` tends to a limit, the limit is `1`. -/
@[kb "hardywright2008" "Thm 426, p. 482"]
theorem primeCounting_mul_log_div_limits :
    (∀ L : ℝ, Tendsto (fun x : ℝ ↦ (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x / x) atTop (𝓝 L) →
      L = 1) ∧
    Filter.liminf (fun x : ℝ ↦ (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x / x) atTop ≤ 1 ∧
    1 ≤ Filter.limsup (fun x : ℝ ↦ (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x / x) atTop := by
  refine ⟨fun L hL ↦ tendsto_nhds_unique hL prime_number_theorem, ?_, ?_⟩
  · rw [prime_number_theorem.liminf_eq]
  · rw [prime_number_theorem.limsup_eq]

/-- Consequence of Theorem 6: `π(c x) / π(x) → c` for every `c > 0`. -/
theorem tendsto_primeCounting_mul_div {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ ↦ (Nat.primeCounting ⌊c * x⌋₊ : ℝ) / Nat.primeCounting ⌊x⌋₊) atTop (𝓝 c) := by
  have hF := prime_number_theorem
  have hG : Tendsto (fun x : ℝ ↦ (Nat.primeCounting ⌊c * x⌋₊ : ℝ) * Real.log (c * x) / (c * x))
      atTop (𝓝 1) := hF.comp (tendsto_id.const_mul_atTop hc)
  have hρ : Tendsto (fun x : ℝ ↦ Real.log (c * x) / Real.log x) atTop (𝓝 1) := by
    have h0 : Tendsto (fun x : ℝ ↦ Real.log c / Real.log x) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
    have h1 := (tendsto_const_nhds (x := (1 : ℝ))).add h0
    rw [add_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0, eventually_gt_atTop 1] with x hx0 hx
    have : Real.log x ≠ 0 := (Real.log_pos hx).ne'
    rw [Real.log_mul hc.ne' hx0.ne']
    field_simp
    ring
  have hlim := (tendsto_const_nhds (x := c)).mul hG |>.div (hF.mul hρ)
    (by norm_num : (1 : ℝ) * 1 ≠ 0)
  rw [mul_one, mul_one, div_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [hF.eventually_ne (one_ne_zero (α := ℝ)), eventually_gt_atTop 0,
    hρ.eventually_ne (one_ne_zero (α := ℝ))] with x h1 hx0 h2
  simp only [ne_eq, div_eq_zero_iff, mul_eq_zero, not_or] at h1 h2
  obtain ⟨⟨hb, hL⟩, -⟩ := h1
  obtain ⟨hM, -⟩ := h2
  have hcx : c * x ≠ 0 := by positivity
  have hx' : x ≠ 0 := hx0.ne'
  have hc' : c ≠ 0 := hc.ne'
  have hb' : (Nat.primeCounting ⌊x⌋₊ : ℝ) ≠ 0 := hb
  simp only [Pi.div_apply]
  field_simp

/-- If `π(a) < π(b)` there is a prime `p` with `a < p ≤ b`. -/
theorem exists_prime_of_primeCounting_lt {a b : ℕ} (h : Nat.primeCounting a < Nat.primeCounting b) :
    ∃ p : ℕ, p.Prime ∧ a < p ∧ p ≤ b := by
  induction b with
  | zero =>
    have h0 : Nat.primeCounting 0 = 0 := by decide
    omega
  | succ b ih =>
    by_cases hp : (b + 1).Prime
    · by_cases hab : a < b + 1
      · exact ⟨b + 1, hp, hab, le_rfl⟩
      · exfalso
        have := Nat.monotone_primeCounting (not_lt.1 hab)
        omega
    · have : Nat.primeCounting (b + 1) = Nat.primeCounting b := by
        simp [Nat.primeCounting, Nat.primeCounting', Nat.count_succ, hp]
      rw [this] at h
      obtain ⟨p, hp1, hp2, hp3⟩ := ih h
      exact ⟨p, hp1, hp2, by omega⟩

/-- **(22.19.2).** For every `ε > 0` and all large `x` there is a prime `p` with
`x < p < (1 + ε) x`. -/
@[kb "hardywright2008" "(22.19.2), p. 513"]
theorem eventually_exists_prime_between {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) < (1 + ε) * x := by
  have hc : (0 : ℝ) < 1 + ε / 2 := by positivity
  have hr := tendsto_primeCounting_mul_div hc
  have hgt : ∀ᶠ x : ℝ in atTop,
      (1 : ℝ) < (Nat.primeCounting ⌊(1 + ε / 2) * x⌋₊ : ℝ) / Nat.primeCounting ⌊x⌋₊ :=
    hr.eventually (lt_mem_nhds (by linarith))
  filter_upwards [hgt, eventually_ge_atTop 2] with x h1 hx2
  have hx0 : 0 < x := by linarith
  have hb : 0 < Nat.primeCounting ⌊x⌋₊ := by
    have h2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx2)
    have := Nat.monotone_primeCounting h2
    have h22 : Nat.primeCounting 2 = 1 := by decide
    omega
  have hb' : (0 : ℝ) < Nat.primeCounting ⌊x⌋₊ := by exact_mod_cast hb
  rw [lt_div_iff₀ hb', one_mul] at h1
  have h1' : Nat.primeCounting ⌊x⌋₊ < Nat.primeCounting ⌊(1 + ε / 2) * x⌋₊ := by exact_mod_cast h1
  obtain ⟨p, hp, hp1, hp2⟩ := exists_prime_of_primeCounting_lt h1'
  refine ⟨p, hp, ?_, ?_⟩
  · calc x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
      _ ≤ p := by exact_mod_cast hp1
  · have : (p : ℝ) ≤ ⌊(1 + ε / 2) * x⌋₊ := by exact_mod_cast hp2
    have h3 : (⌊(1 + ε / 2) * x⌋₊ : ℝ) ≤ (1 + ε / 2) * x := Nat.floor_le (by positivity)
    nlinarith

/-- **(22.19.3).** `(π(2x) - π(x)) / π(x) → 1`: the number of primes between `x` and `2x` is
asymptotically `π(x)`. -/
@[kb "hardywright2008" "(22.19.3), p. 513"]
theorem tendsto_primeCounting_two_mul_sub_div :
    Tendsto (fun x : ℝ ↦
      ((Nat.primeCounting ⌊2 * x⌋₊ : ℝ) - Nat.primeCounting ⌊x⌋₊) / Nat.primeCounting ⌊x⌋₊)
      atTop (𝓝 1) := by
  have h := (tendsto_primeCounting_mul_div (c := 2) two_pos).sub_const 1
  rw [show (2 : ℝ) - 1 = 1 by norm_num] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with x hx2
  have hb : 0 < Nat.primeCounting ⌊x⌋₊ := by
    have h2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx2)
    have := Nat.monotone_primeCounting h2
    have h22 : Nat.primeCounting 2 = 1 := by decide
    omega
  have hb' : (Nat.primeCounting ⌊x⌋₊ : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  field_simp

end NTKB.HardyWright
