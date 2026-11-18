/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.ArithmeticFunctions.Ramanujan305
import NTKB.Elementary.HardyWright.ArithmeticFunctions.FormalEulerProduct
import Mathlib.Data.Nat.Totient

/-!
# Hardy–Wright, §§ 17.5–17.8: more Dirichlet series of the zeta function

For real `s` in the book; here for complex `s`.

* Theorem 288: `ζ(s-1)/ζ(s) = ∑ φ(n) n^{-s}` for `Re s > 2`.
* Theorem 290: `ζ(s) ζ(s-1) = ∑ σ(n) n^{-s}` for `Re s > 2`.
* Theorem 299: `ζ(s)^k = ∑ d_k(n) n^{-s}` for `Re s > 1`, `d_k(n)` the number of ordered
  factorizations of `n` into `k` factors.
* Theorem 301: `ζ(s)²/ζ(2s) = ∑ 2^{ω(n)} n^{-s}` for `Re s > 1`, `ω(n)` the number of distinct prime
  factors of `n`.

As for Theorems 300 to 305 (`DirichletSeries.lean`, `Ramanujan305.lean`), each is an identity of
Dirichlet convolutions (`∑_{d ∣ n} φ(d) = n`, `σ = 1 * P_1`, `d_k = 1 * ⋯ * 1`,
`2^ω = q_2 * 1` with `q_2` the indicator of the squarefree numbers), and Mathlib's product theorem
for `L`-series (Theorem 284, `LSeries_mul'`). Prime-power checks replace the book's comparison of
Euler factors. Source text unavailable: the
statements follow the map's one-line paraphrases.
-/

open Finset ArithmeticFunction Complex
open scoped ArithmeticFunction.zeta ArithmeticFunction.sigma ArithmeticFunction.omega

namespace NTKB.HardyWright

/-! ### Theorem 288 -/

/-- Euler's function `φ` as a complex arithmetic function. -/
noncomputable def totientC : ArithmeticFunction ℂ := ⟨fun n => (Nat.totient n : ℂ), by simp⟩

lemma totientC_apply (n : ℕ) : totientC n = (Nat.totient n : ℂ) := rfl

/-- `∑_{d ∣ n} φ(d) = n`, as `φ * 1 = P_1`. -/
lemma totientC_mul_zeta : totientC * (ζ : ArithmeticFunction ℂ) = powC 1 := by
  ext n
  rw [coe_mul_zeta_apply]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [powC_apply hn, cpow_one]
  simp only [totientC_apply]
  exact_mod_cast Nat.sum_totient n

lemma LSeriesSummable_totientC {s : ℂ} (hs : 2 < s.re) :
    LSeriesSummable (fun n => totientC n) s :=
  LSeriesSummable_of_le_const_mul_rpow (x := 2) hs ⟨1, fun n _ => by
    rw [totientC_apply, Complex.norm_natCast, one_mul, show (2 : ℝ) - 1 = 1 by norm_num,
      Real.rpow_one]
    exact_mod_cast Nat.totient_le n⟩

/-- **Theorem 288** (Hardy–Wright). For `s > 2` (here complex `s`, `Re s > 2`),
`ζ(s-1)/ζ(s) = ∑ φ(n) n^{-s}`. -/
@[kb "hardywright2008" "Thm 288, p. 346"]
theorem LSeries_totient {s : ℂ} (hs : 2 < s.re) :
    LSeries (fun n => (Nat.totient n : ℂ)) s = riemannZeta (s - 1) / riemannZeta s := by
  have hs1 : 1 < s.re := by linarith
  have hmul := LSeries_mul' (LSeriesSummable_totientC hs) (LSeriesSummable_zetaC hs1)
  rw [totientC_mul_zeta, LSeries_powC (by simp; linarith), LSeries_zetaC hs1] at hmul
  rw [eq_div_iff (riemannZeta_ne_zero_of_one_lt_re hs1)]
  exact hmul.symm

/-! ### Theorem 290 -/

/-- `σ(n) = ∑_{d ∣ n} d`, as `σ = 1 * P_1`. -/
lemma sigma_one_natCoe : ((σ 1 : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) =
    (ζ : ArithmeticFunction ℂ) * powC 1 := by
  ext n
  rw [coe_zeta_mul_apply, natCoe_apply, sigma_one_apply]
  push_cast
  exact sum_congr rfl fun d hd => by
    rw [powC_apply (Nat.pos_of_mem_divisors hd).ne', cpow_one]

/-- **Theorem 290** (Hardy–Wright). For `s > 2` (here complex `s`, `Re s > 2`),
`ζ(s) ζ(s-1) = ∑ σ(n) n^{-s}`, `σ(n)` the sum of the divisors of `n`. -/
@[kb "hardywright2008" "Thm 290, p. 346"]
theorem LSeries_sigma_one {s : ℂ} (hs : 2 < s.re) :
    LSeries (fun n => (σ 1 n : ℂ)) s = riemannZeta s * riemannZeta (s - 1) := by
  have hs1 : 1 < s.re := by linarith
  have hs2 : 1 < (s - 1).re := by simp; linarith
  have hmul := LSeries_mul' (LSeriesSummable_zetaC hs1) (LSeriesSummable_powC (c := 1) hs2)
  rw [← sigma_one_natCoe, LSeries_zetaC hs1, LSeries_powC hs2] at hmul
  simpa only [natCoe_apply] using hmul

/-! ### Theorem 299 -/

lemma natCoe_zeta_pow (k : ℕ) :
    (((ζ : ArithmeticFunction ℕ) ^ k : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) =
      (ζ : ArithmeticFunction ℂ) ^ k := by
  induction k with
  | zero => simp only [pow_zero, natCoe_one]
  | succ k ih => rw [pow_succ, natCoe_mul, ih, pow_succ]

/-- **Theorem 299** (Hardy–Wright). For `s > 1` (here complex `s`, `Re s > 1`) and every `k`,
`ζ(s)^k = ∑ d_k(n) n^{-s}`, where `d_k(n)` is the number of ordered factorizations
`n = n₁ n₂ ⋯ n_k` of `n` into `k` factors (`Nat.finMulAntidiag k n`). -/
@[kb "hardywright2008" "Thm 299, p. 353"]
theorem LSeries_card_finMulAntidiag (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => ((Nat.finMulAntidiag k n).card : ℂ)) s = riemannZeta s ^ k := by
  have hcoe : (fun n => ((Nat.finMulAntidiag k n).card : ℂ)) =
      fun n => ((ζ : ArithmeticFunction ℂ) ^ k) n := by
    funext n
    rw [← natCoe_zeta_pow, natCoe_apply, ArithmeticFunction.zeta_pow_apply]
  rw [hcoe]
  clear hcoe
  have key : LSeriesSummable (fun n => ((ζ : ArithmeticFunction ℂ) ^ k) n) s ∧
      LSeries (fun n => ((ζ : ArithmeticFunction ℂ) ^ k) n) s = riemannZeta s ^ k := by
    induction k with
    | zero =>
      simp only [pow_zero]
      refine ⟨?_, ?_⟩
      · exact LSeriesSummable_of_le_const_mul_rpow (x := 1) hs ⟨1, fun n _ => by
          rw [ArithmeticFunction.one_apply]; split_ifs <;> simp⟩
      · have : (fun n => (1 : ArithmeticFunction ℂ) n) = LSeries.delta := by
          funext n; rw [ArithmeticFunction.one_apply]; simp [LSeries.delta]
        rw [this, LSeries_delta, Pi.one_apply]
    | succ k ih =>
      obtain ⟨h1, h2⟩ := ih
      rw [pow_succ]
      exact ⟨LSeriesSummable_mul h1 (LSeriesSummable_zetaC hs), by
        rw [LSeries_mul' h1 (LSeriesSummable_zetaC hs), h2, LSeries_zetaC hs, pow_succ]⟩
  exact key.2

/-! ### Theorem 301 -/

/-- `2^{ω(n)}` (and `0 ↦ 0`) as a complex arithmetic function. -/
noncomputable def twoPowOmega : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else (2 : ℂ) ^ ω n, by simp⟩

lemma twoPowOmega_apply {n : ℕ} (hn : n ≠ 0) : twoPowOmega n = (2 : ℂ) ^ ω n := by
  simp [twoPowOmega, hn]

lemma isMultiplicative_twoPowOmega : twoPowOmega.IsMultiplicative := by
  refine ⟨by simp [twoPowOmega], fun {m n} hmn => ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp [twoPowOmega]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [twoPowOmega]
  rw [twoPowOmega_apply (mul_ne_zero hm hn), twoPowOmega_apply hm, twoPowOmega_apply hn,
    cardDistinctFactors_mul hmn, pow_add]

/-- `2^{ω(n)} = ∑_{d ∣ n} q_2(d)`: the number of squarefree divisors of `n`. -/
lemma powerFreeIndicator_two_mul_zeta :
    powerFreeIndicator 2 * (ζ : ArithmeticFunction ℂ) = twoPowOmega := by
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _
    ((isMultiplicative_powerFreeIndicator two_ne_zero).mul isMultiplicative_zeta.natCast) _
    isMultiplicative_twoPowOmega).mpr fun p a hp => ?_
  rw [mul_apply_prime_pow _ _ hp, twoPowOmega_apply (pow_ne_zero _ hp.ne_zero)]
  simp only [powerFreeIndicator_prime_pow two_ne_zero hp, natCoe_apply, zeta_apply,
    pow_ne_zero _ hp.ne_zero, ↓reduceIte, Nat.cast_one, mul_one]
  rcases a with _ | a
  · simp; rfl
  rw [cardDistinctFactors_apply_prime_pow hp (Nat.succ_ne_zero a), sum_range_succ']
  rw [sum_eq_single_of_mem 0 (by simp) fun i _ hi => by simp; omega]
  norm_num

/-- **Theorem 301** (Hardy–Wright). For `s > 1` (here complex `s`, `Re s > 1`),
`ζ(s)²/ζ(2s) = ∑ 2^{ω(n)} n^{-s}`, `ω(n)` the number of distinct prime factors of `n`. -/
@[kb "hardywright2008" "Thm 301, p. 354"]
theorem LSeries_two_pow_cardDistinctFactors {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (2 : ℂ) ^ ω n) s = riemannZeta s ^ 2 / riemannZeta (2 * s) := by
  have h2s : 1 < ((2 : ℕ) * s).re := by simp; linarith
  have hq := LSeriesSummable_of_abs_le_one (norm_powerFreeIndicator_le 2) hs
  have hζ := LSeriesSummable_zetaC hs
  have hw : LSeriesSummable (fun n => twoPowOmega n) s := by
    rw [← powerFreeIndicator_two_mul_zeta]; exact LSeriesSummable_mul hq hζ
  have hcongr : LSeries (fun n => (2 : ℂ) ^ ω n) s = LSeries (fun n => twoPowOmega n) s :=
    LSeries_congr (fun {n} hn => (twoPowOmega_apply hn).symm) s
  -- `2^ω * (squares) = q_2 * 1 * (squares) = 1 * 1 = d`
  have hmul := LSeries_mul' hw (LSeriesSummable_of_abs_le_one (norm_powIndicator_le 2) hs)
  rw [← powerFreeIndicator_two_mul_zeta, mul_assoc, mul_comm (ζ : ArithmeticFunction ℂ),
    ← mul_assoc, powerFreeIndicator_mul_powIndicator two_ne_zero, LSeries_mul' hζ hζ,
    LSeries_zetaC hs, powerFreeIndicator_two_mul_zeta,
    LSeries_powIndicator two_ne_zero h2s] at hmul
  rw [hcongr, eq_div_iff (riemannZeta_ne_zero_of_one_lt_re (by simpa using h2s))]
  push_cast at hmul
  rw [sq, hmul]

end NTKB.HardyWright
