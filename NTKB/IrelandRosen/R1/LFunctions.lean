/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import NTKB.Elementary.SpecialValues.ValueAtZero

/-!
# Ireland–Rosen, Chapter 16: two facts on Dirichlet L-functions

* **Proposition 16.5.3**: `F(s) = ∏_χ L(s, χ) ≥ 1` for real `s > 1`, the product over all
  Dirichlet characters modulo `m`. The book's proof: `log L(s, χ) = G(s, χ) =
  ∑_p ∑_k χ(p^k) p^(-ks)/k`, and summing over `χ` gives `φ(m) ∑_{p^k ≡ 1} p^(-ks)/k ≥ 0`
  (orthogonality, Proposition 16.3.2 (ii)); exponentiate. Here `G(s, χ)` is
  `∑_p -log(1 - χ(p) p^(-s))` (Mathlib's `DirichletCharacter.LSeries_eulerProduct_exp_log`) and
  the series in `k` is the Taylor series of `-log(1 - z)`.
* **Proposition 16.6.2**: `L(1 - k, χ) = -B_{k,χ}/k` for `k ≥ 1`; this is NTKB's
  `NTKB.LFunction_one_sub_nat` (special values), restated here with the book's citation. It holds
  for every Dirichlet character, not only the nontrivial ones of the book.
-/

open Complex DirichletCharacter

open scoped ComplexOrder

namespace NTKB.IrelandRosen

/-- For `z = χ(p) x` with `0 ≤ x < 1` real, `∑_χ -log(1 - χ(p) x)` is a nonnegative real number
(`φ(m) ∑_{p^k ≡ 1} x^k/k`). -/
theorem zero_le_sum_neg_log_one_sub {m : ℕ} [NeZero m] (a : ZMod m) {x : ℝ} (hx0 : 0 ≤ x)
    (hx1 : x < 1) :
    0 ≤ ∑ χ : DirichletCharacter ℂ m, -log (1 - χ a * x) := by
  have hnorm : ∀ χ : DirichletCharacter ℂ m, ‖χ a * (x : ℂ)‖ < 1 := fun χ ↦ by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hx0]
    calc ‖χ a‖ * x ≤ 1 * x := by gcongr; exact χ.norm_le_one a
      _ < 1 := by linarith
  have hsum : HasSum (fun n : ℕ ↦ ∑ χ : DirichletCharacter ℂ m, (χ a * x) ^ n / n)
      (∑ χ : DirichletCharacter ℂ m, -log (1 - χ a * x)) :=
    hasSum_sum fun χ _ ↦ hasSum_taylorSeries_neg_log (hnorm χ)
  refine hsum.nonneg fun n ↦ ?_
  have : ∑ χ : DirichletCharacter ℂ m, (χ a * x) ^ n / n =
      ((if a ^ n = 1 then (m.totient : ℝ) else 0) * x ^ n / n : ℝ) := by
    simp_rw [mul_pow, ← map_pow, mul_div_assoc, ← Finset.sum_mul, sum_characters_eq]
    split_ifs <;> push_cast <;> ring
  rw [this, Complex.zero_le_real]
  split_ifs <;> positivity

/-- **Ireland–Rosen, Proposition 16.5.3.** For real `s > 1`, the product `∏_χ L(s, χ)` over all
Dirichlet characters modulo `m` is a real number `≥ 1` (stated in the order of `ℂ`, where
`1 ≤ z` means that `z` is real and at least `1`). -/
@[kb "irelandrosen1990" "Prop 16.5.3, p. 270"]
theorem one_le_prod_LSeries {m : ℕ} [NeZero m] {s : ℝ} (hs : 1 < s) :
    1 ≤ ∏ χ : DirichletCharacter ℂ m, LSeries (fun n ↦ χ n) s := by
  have hs' : 1 < (s : ℂ).re := by simpa using hs
  -- `L(s, χ) = exp G(s, χ)`
  rw [Finset.prod_congr rfl fun χ _ ↦ (LSeries_eulerProduct_exp_log χ hs').symm,
    ← Complex.exp_sum,
    ← Summable.tsum_finsetSum fun χ _ ↦ summable_neg_log_one_sub_mul_prime_cpow χ hs']
  -- the exponent is a nonnegative real number
  have hnonneg : 0 ≤ ∑' p : Nat.Primes, ∑ χ : DirichletCharacter ℂ m,
      -log (1 - χ p * (p : ℂ) ^ (-(s : ℂ))) := by
    refine tsum_nonneg fun p ↦ ?_
    have hp : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
    have hx : ((p : ℂ) ^ (-(s : ℂ))) = (((p : ℝ) ^ (-s) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (by positivity)]; push_cast; rfl
    simp_rw [hx]
    refine zero_le_sum_neg_log_one_sub _ (by positivity) ?_
    exact Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
  generalize (∑' p : Nat.Primes, ∑ χ : DirichletCharacter ℂ m,
      -log (1 - χ p * (p : ℂ) ^ (-(s : ℂ)))) = z at hnonneg ⊢
  have hz : z = (z.re : ℂ) := Complex.eq_re_of_ofReal_le (r := 0) (by simpa using hnonneg)
  have hre : 0 ≤ z.re := by
    rw [hz] at hnonneg; exact Complex.zero_le_real.mp hnonneg
  rw [hz, ← Complex.ofReal_exp, ← Complex.ofReal_one, Complex.real_le_real]
  exact Real.one_le_exp hre

/-- **Ireland–Rosen, Proposition 16.6.2.** `L(1 - k, χ) = -B_{k,χ}/k` for every Dirichlet
character `χ` and every `k ≥ 1`. This is `NTKB.LFunction_one_sub_nat` (Washington, Theorem 4.2),
where `B_{k,χ}` is NTKB's `generalizedBernoulli` (defined through Bernoulli polynomials; the book
defines it by the generating function `∑_a χ(a) t e^(at)/(e^(mt) - 1)`). -/
@[kb "irelandrosen1990" "Prop 16.6.2, p. 275"]
theorem LFunction_one_sub_nat_eq {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) {k : ℕ}
    (hk : 1 ≤ k) :
    LFunction χ (1 - k) = -NTKB.generalizedBernoulli χ k / k :=
  NTKB.LFunction_one_sub_nat χ hk

end NTKB.IrelandRosen
