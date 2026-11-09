/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Polynomial.Eval.Coeff
import NTKB.Attr

/-!
# Lemmas for the transcendence of `e` (Hardy–Wright, § 11.13)

Hardy and Wright write `φ(h)` for the result of replacing each power `h^r` of a polynomial `φ(h)` by
`r!` (a symbolic, "umbral", evaluation). We call it `hEval φ`.

* Theorem 203: if `m ≥ 1`, `f` is an integral polynomial, `F₁(x) = x^{m-1} f(x)/(m-1)!` and
  `F₂(x) = x^m f(x)/(m-1)!`, then `F₁(h)` and `F₂(h)` are integers, `F₁(h) ≡ f(0)` and
  `F₂(h) ≡ 0 (mod m)` (Hardy–Wright state it for `m ≥ 2`).
-/

namespace NTKB.HardyWright

open Polynomial
open scoped Nat

/-- Hardy–Wright's symbolic evaluation `φ(h)`: replace each `h^r` by `r!`. -/
noncomputable def hEval (F : ℝ[X]) : ℝ := F.sum fun r c ↦ c * (r ! : ℝ)

lemma hEval_add (F G : ℝ[X]) : hEval (F + G) = hEval F + hEval G :=
  Polynomial.sum_add_index _ _ _ (fun _ ↦ by simp) (fun _ _ _ ↦ by ring)

lemma hEval_monomial (n : ℕ) (a : ℝ) : hEval (monomial n a) = a * (n ! : ℝ) :=
  Polynomial.sum_monomial_index _ _ (by simp)

/-- `(C c · X^k · g)(h) = c · ∑ₗ gₗ (l + k)!`. -/
lemma hEval_C_mul_X_pow_mul (c : ℝ) (k : ℕ) (g : ℝ[X]) :
    hEval (C c * X ^ k * g) = c * g.sum fun l b ↦ b * ((l + k)! : ℝ) := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [mul_add, hEval_add, hp, hq,
      Polynomial.sum_add_index _ _ _ (fun _ ↦ by simp) (fun _ _ _ ↦ by ring)]
    ring
  | monomial n a =>
    rw [show C c * X ^ k * monomial n a = monomial (n + k) (c * a) by
      rw [← monomial_one_right_eq_X_pow, C_mul_monomial, monomial_mul_monomial]; ring_nf,
      hEval_monomial, Polynomial.sum_monomial_index _ _ (by simp)]
    ring

private lemma dvd_ascFactorial_succ (m l : ℕ) : m ∣ m.ascFactorial (l + 1) := by
  induction l with
  | zero => simp [Nat.ascFactorial_succ]
  | succ l ih => rw [Nat.ascFactorial_succ]; exact dvd_mul_of_dvd_right ih _

/-- `(m-1)! · m(m+1)⋯(m+l-1) = (l + m - 1)!`. -/
private lemma factorial_mul_ascFactorial' (m l : ℕ) (hm : 1 ≤ m) :
    ((m - 1)! : ℝ) * (m.ascFactorial l : ℝ) = ((l + (m - 1))! : ℝ) := by
  have := Nat.factorial_mul_ascFactorial (m - 1) l
  rw [Nat.sub_add_cancel hm] at this
  rw [add_comm l]; exact_mod_cast this

/-- **Theorem 203.** If `m ≥ 1`, `f(x)` is an integral polynomial and `F₁(x) = x^{m-1} f(x)/(m-1)!`,
`F₂(x) = x^m f(x)/(m-1)!`, then `F₁(h)` and `F₂(h)` are integers, and `F₁(h) ≡ f(0)`,
`F₂(h) ≡ 0 (mod m)`. -/
@[kb "hardywright2008" "Thm 203, p. 220"]
theorem hEval_integral (f : ℤ[X]) {m : ℕ} (hm : 1 ≤ m) :
    (∃ z : ℤ, hEval (C (1 / ((m - 1)! : ℝ)) * X ^ (m - 1) * f.map (Int.castRingHom ℝ)) = z ∧
      z ≡ f.coeff 0 [ZMOD m]) ∧
    (∃ z : ℤ, hEval (C (1 / ((m - 1)! : ℝ)) * X ^ m * f.map (Int.castRingHom ℝ)) = z ∧
      z ≡ 0 [ZMOD m]) := by
  have hf0 : ((m - 1)! : ℝ) ≠ 0 := by positivity
  -- write the sums over `range (natDegree f + 1)`
  have hsum : ∀ (k : ℕ), (f.map (Int.castRingHom ℝ)).sum (fun l b ↦ b * ((l + k)! : ℝ)) =
      ∑ l ∈ Finset.range (f.natDegree + 1), (f.coeff l : ℝ) * ((l + k)! : ℝ) := by
    intro k
    rw [Polynomial.sum_over_range' _ (fun _ ↦ by simp) (f.natDegree + 1)]
    · simp
    · rw [natDegree_map_eq_of_injective (RingHom.injective_int (Int.castRingHom ℝ))]; omega
  refine ⟨⟨∑ l ∈ Finset.range (f.natDegree + 1), f.coeff l * m.ascFactorial l, ?_, ?_⟩,
    ⟨∑ l ∈ Finset.range (f.natDegree + 1), f.coeff l * m.ascFactorial (l + 1), ?_, ?_⟩⟩
  · rw [hEval_C_mul_X_pow_mul, hsum]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [← factorial_mul_ascFactorial' m l hm]
    field_simp
  · rw [Finset.sum_range_succ', Nat.ascFactorial_zero, Nat.cast_one, mul_one]
    have : (m : ℤ) ∣ ∑ l ∈ Finset.range f.natDegree, f.coeff (l + 1) * (m.ascFactorial (l + 1) : ℤ) :=
      Finset.dvd_sum fun l _ ↦ dvd_mul_of_dvd_right (by exact_mod_cast dvd_ascFactorial_succ m l) _
    exact (Int.modEq_zero_iff_dvd.mpr this).add_right _ |>.trans (by simp [Int.ModEq])
  · rw [hEval_C_mul_X_pow_mul, hsum]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    have := factorial_mul_ascFactorial' m (l + 1) hm
    rw [show l + 1 + (m - 1) = l + m by omega] at this
    rw [← this]
    field_simp
  · exact Int.modEq_zero_iff_dvd.mpr (Finset.dvd_sum fun l _ ↦
      dvd_mul_of_dvd_right (by exact_mod_cast dvd_ascFactorial_succ m l) _)

/-! ### Theorem 202 -/

lemma hEval_zero : hEval 0 = 0 := by simp [hEval]

lemma hEval_C_mul (c : ℝ) (F : ℝ[X]) : hEval (C c * F) = c * hEval F := by
  have := hEval_C_mul_X_pow_mul c 0 F
  simp only [pow_zero, mul_one, add_zero] at this
  rw [this]; rfl

lemma hEval_sum {ι : Type*} (s : Finset ι) (F : ι → ℝ[X]) :
    hEval (∑ i ∈ s, F i) = ∑ i ∈ s, hEval (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hEval_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hEval_add, ih]

/-- Hardy–Wright's `u_r(x) = x/(r+1) + x²/((r+1)(r+2)) + ⋯`. -/
noncomputable def uR (r : ℕ) (x : ℝ) : ℝ := ∑' j : ℕ, x ^ (j + 1) * (r ! : ℝ) / ((r + j + 1)! : ℝ)

/-- Hardy–Wright's `εᵣ(x)`, defined by `uᵣ(x) = e^{|x|} εᵣ(x)`. -/
noncomputable def epsR (r : ℕ) (x : ℝ) : ℝ := uR r x / Real.exp |x|

private lemma term_bound (r j : ℕ) (x : ℝ) :
    |x ^ (j + 1) * (r ! : ℝ) / ((r + j + 1)! : ℝ)| ≤ |x| ^ (j + 1) / ((j + 1)! : ℝ) := by
  rw [abs_div, abs_mul, abs_pow, abs_of_pos (by positivity : (0 : ℝ) < r !),
    abs_of_pos (by positivity : (0 : ℝ) < (r + j + 1)!), mul_div_assoc,
    div_eq_mul_one_div (|x| ^ (j + 1))]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  have := Nat.factorial_mul_factorial_dvd_factorial_add r (j + 1)
  have h := Nat.le_of_dvd (Nat.factorial_pos _) this
  rw [show r + (j + 1) = r + j + 1 by ring] at h
  have h' : ((r ! * (j + 1)! : ℕ) : ℝ) ≤ ((r + j + 1)! : ℕ) := by exact_mod_cast h
  push_cast at h'
  nlinarith [Nat.factorial_pos (j + 1)]

private lemma hasSum_exp_abs (x : ℝ) :
    HasSum (fun j : ℕ ↦ |x| ^ (j + 1) / ((j + 1)! : ℝ)) (Real.exp |x| - 1) := by
  have hs : HasSum (fun n : ℕ ↦ |x| ^ n / (n ! : ℝ)) (Real.exp |x|) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp |x|
  have := (hasSum_nat_add_iff' 1).mpr hs
  simpa using this

private lemma summable_uR (r : ℕ) (x : ℝ) :
    Summable fun j : ℕ ↦ x ^ (j + 1) * (r ! : ℝ) / ((r + j + 1)! : ℝ) :=
  Summable.of_norm_bounded (hasSum_exp_abs x).summable fun j ↦ by
    rw [Real.norm_eq_abs]; exact term_bound r j x

/-- **(11.13.1)**: `|εᵣ(x)| < 1`. -/
theorem abs_epsR_lt_one (r : ℕ) (x : ℝ) : |epsR r x| < 1 := by
  unfold epsR
  rw [abs_div, abs_of_pos (Real.exp_pos _), div_lt_one (Real.exp_pos _)]
  have hs' := hasSum_exp_abs x
  have hn : Summable fun j : ℕ ↦ ‖x ^ (j + 1) * (r ! : ℝ) / ((r + j + 1)! : ℝ)‖ :=
    Summable.of_nonneg_of_le (fun j ↦ norm_nonneg _)
      (fun j ↦ by rw [Real.norm_eq_abs]; exact term_bound r j x) hs'.summable
  calc |uR r x| = ‖∑' j : ℕ, x ^ (j + 1) * (r ! : ℝ) / ((r + j + 1)! : ℝ)‖ := by
        rw [Real.norm_eq_abs]; rfl
    _ ≤ ∑' j : ℕ, ‖x ^ (j + 1) * (r ! : ℝ) / ((r + j + 1)! : ℝ)‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' j : ℕ, |x| ^ (j + 1) / ((j + 1)! : ℝ) :=
        hn.tsum_le_tsum (fun j ↦ by rw [Real.norm_eq_abs]; exact term_bound r j x) hs'.summable
    _ = Real.exp |x| - 1 := hs'.tsum_eq
    _ < Real.exp |x| := by linarith

/-- `(x + h)^r = ∑_{n ≤ r} xⁿ r!/n!` (symbolically, `h^k = k!`). -/
lemma hEval_X_add_C_pow (r : ℕ) (x : ℝ) :
    hEval ((X + C x) ^ r) = ∑ n ∈ Finset.range (r + 1), x ^ n * (r ! : ℝ) / (n ! : ℝ) := by
  rw [add_comm, add_pow, hEval_sum]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  rw [Finset.mem_range] at hn
  rw [show C x ^ n * X ^ (r - n) * ((r.choose n : ℕ) : ℝ[X]) =
      C (x ^ n * (r.choose n : ℝ)) * X ^ (r - n) * 1 by
    rw [← C_pow, ← map_natCast C, C_mul]; ring]
  rw [hEval_C_mul_X_pow_mul, show (1 : ℝ[X]) = monomial 0 1 by simp,
    Polynomial.sum_monomial_index _ _ (by simp), zero_add, one_mul]
  have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ r by omega)
  have h' : ((r.choose n : ℕ) : ℝ) * (n ! : ℝ) * ((r - n)! : ℝ) = (r ! : ℝ) := by exact_mod_cast h
  have hn0 : (n ! : ℝ) ≠ 0 := by positivity
  rw [eq_div_iff hn0, ← h']
  ring

/-- `e^x r! = (x + h)^r + uᵣ(x) x^r`. -/
lemma exp_mul_factorial (r : ℕ) (x : ℝ) :
    Real.exp x * (r ! : ℝ) = hEval ((X + C x) ^ r) + uR r x * x ^ r := by
  have hs : HasSum (fun n : ℕ ↦ x ^ n / (n ! : ℝ)) (Real.exp x) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp x
  have hs2 := hs.mul_left (r ! : ℝ)
  rw [mul_comm, hEval_X_add_C_pow, uR, ← hs2.tsum_eq, ← hs2.summable.sum_add_tsum_nat_add (r + 1),
    ← tsum_mul_right]
  congr 1
  · refine Finset.sum_congr rfl fun n _ ↦ ?_; ring
  · refine tsum_congr fun j ↦ ?_
    rw [show j + (r + 1) = r + j + 1 by ring, pow_succ, show r + j + 1 = j + 1 + r by ring, pow_add]
    ring_nf

/-- **Theorem 202.** If `φ(x) = ∑ cᵣ x^r` is any polynomial and `ψ(x) = ∑ cᵣ εᵣ(x) x^r`, then
`e^x φ(h) = φ(x + h) + ψ(x) e^{|x|}` (in Hardy–Wright's symbolic notation `h^r = r!`; `|εᵣ(x)| < 1` is
`abs_epsR_lt_one`). -/
@[kb "hardywright2008" "Thm 202, p. 219"]
theorem exp_mul_hEval (φ : ℝ[X]) (x : ℝ) :
    Real.exp x * hEval φ =
      hEval (φ.comp (X + C x)) + (φ.sum fun r c ↦ c * epsR r x * x ^ r) * Real.exp |x| := by
  rw [comp_eq_sum_left, Polynomial.sum_def, Polynomial.sum_def, hEval_sum,
    Finset.sum_mul, ← Finset.sum_add_distrib, hEval, Polynomial.sum_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [hEval_C_mul, epsR]
  have := exp_mul_factorial r x
  have he := (Real.exp_pos |x|).ne'
  field_simp
  linear_combination φ.coeff r * this

end NTKB.HardyWright
