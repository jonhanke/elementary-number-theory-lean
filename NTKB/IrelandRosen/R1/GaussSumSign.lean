/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.IrelandRosen.R1.TrigProduct

/-!
# Ireland–Rosen, Chapter 6, Section 4: the product behind the sign of the Gauss sum

Let `p` be an odd prime and `ζ = e^(2πi/p)`.

* **Proposition 6.4.2**: `∏_{k=1}^{(p-1)/2} (ζ^(2k-1) - ζ^(-(2k-1)))² = (-1)^((p-1)/2) p`.
  Book's proof: `p = ∏_{r=1}^{p-1} (1 - ζ^r)` (divide `x^p - 1` by `x - 1`, put `x = 1`), and the
  residues `±(4k - 2)`, `k = 1, …, (p-1)/2`, run over the nonzero classes modulo `p`.
* **Proposition 6.4.3**: `∏_{k=1}^{(p-1)/2} (ζ^(2k-1) - ζ^(-(2k-1)))` is `√p` if `p ≡ 1 (4)` and
  `i√p` if `p ≡ 3 (4)`. Book's proof: the product is `(2i)^((p-1)/2) ∏ sin((4k-2)π/p)`, and
  exactly `⌊p/4⌋` of the sines are negative.
-/

open Complex Finset Real

namespace NTKB.IrelandRosen

/-- `∏_{r=1}^{n-1} (1 - μ^r) = n` for a primitive `n`-th root of unity `μ` (divide
`x^n - 1 = ∏ (x - μ^r)` by `x - 1` and put `x = 1`). -/
theorem prod_one_sub_pow_eq {μ : ℂ} {n : ℕ} (hμ : IsPrimitiveRoot μ n) (hn : 0 < n) :
    ∏ k ∈ range (n - 1), (1 - μ ^ (k + 1)) = n := by
  have h1 := Polynomial.X_pow_sub_one_eq_prod hn hμ
  rw [prod_nthRootsFinset_eq_prod_range hμ hn (fun ζ ↦ Polynomial.X - Polynomial.C ζ)] at h1
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [prod_range_succ', pow_zero, Polynomial.C_1,
    ← geom_sum_mul (Polynomial.X : Polynomial ℂ) (n' + 1)] at h1
  have h2 := mul_right_cancel₀ (by simpa using Polynomial.X_sub_C_ne_zero (1 : ℂ)) h1
  have h3 := congrArg (Polynomial.eval 1) h2
  simp [Polynomial.eval_prod] at h3
  rw [Nat.add_sub_cancel, ← h3]
  push_cast
  ring

/-- `∏_{j<2m} f j = ∏_{k<m} f(2k) f(2k+1)`. -/
theorem prod_range_two_mul {M : Type*} [CommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∏ j ∈ range (2 * m), f j = ∏ k ∈ range m, (f (2 * k) * f (2 * k + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, prod_range_succ, prod_range_succ, ih,
      prod_range_succ, mul_assoc]

/-- Proposition 6.4.2, indexed by `k = 0, …, (p-3)/2` (the factor `ζ^(2k+1) - ζ^(-(2k+1))`). -/
theorem prod_range_zeta_sub_inv_sq {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    ∏ k ∈ range ((p - 1) / 2),
      (cexp (2 * π * I / p) ^ (2 * k + 1) - (cexp (2 * π * I / p) ^ (2 * k + 1))⁻¹) ^ 2 =
      (-1) ^ ((p - 1) / 2) * p := by
  set ζ := cexp (2 * π * I / p)
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  set m := (p - 1) / 2 with hm
  have hpm : p = 2 * m + 1 := by obtain ⟨t, rfl⟩ := hodd; omega
  have hζ : IsPrimitiveRoot ζ p := Complex.isPrimitiveRoot_exp p hp0.ne'
  have hζ0 : ζ ≠ 0 := Complex.exp_ne_zero _
  have hζ2 : IsPrimitiveRoot (ζ ^ 2) p := hζ.pow_of_coprime 2 (Nat.coprime_two_left.mpr hodd)
  -- `p = ∏_{r=1}^{p-1} (1 - ζ^(2r))`
  have hP := prod_one_sub_pow_eq hζ2 hp0
  rw [show p - 1 = 2 * m by omega, prod_range_two_mul] at hP
  -- pair `r = 2k+1` with `r = p - (2k+1)`
  have hreflect : ∏ k ∈ range m, (1 - (ζ ^ 2) ^ (2 * k + 1 + 1)) =
      ∏ k ∈ range m, (1 - ((ζ ^ 2) ^ (2 * k + 1))⁻¹) := by
    rw [← prod_range_reflect]
    refine prod_congr rfl fun k hk ↦ ?_
    have hk := mem_range.mp hk
    congr 1
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_add, show 2 * (m - 1 - k) + 1 + 1 + (2 * k + 1) = p by omega,
      ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hsplit : ∏ k ∈ range m, ((1 - (ζ ^ 2) ^ (2 * k + 1)) * (1 - (ζ ^ 2) ^ (2 * k + 1 + 1))) =
      ∏ k ∈ range m, (-(ζ ^ (2 * k + 1) - (ζ ^ (2 * k + 1))⁻¹) ^ 2) := by
    rw [prod_mul_distrib, hreflect, ← prod_mul_distrib]
    refine prod_congr rfl fun k _ ↦ ?_
    have : ζ ^ (2 * k + 1) ≠ 0 := pow_ne_zero _ hζ0
    rw [← pow_mul, mul_comm 2 (2 * k + 1), pow_mul]
    field_simp
    ring
  rw [hsplit, prod_neg] at hP
  -- multiply by `(-1)^m`
  have h1 : ((-1 : ℂ) ^ m) * (-1) ^ m = 1 := by rw [← mul_pow]; simp
  calc _ = ((-1 : ℂ) ^ m * (-1) ^ m) *
        ∏ k ∈ range m, (ζ ^ (2 * k + 1) - (ζ ^ (2 * k + 1))⁻¹) ^ 2 := by
        rw [h1, one_mul]
    _ = (-1) ^ m * p := by
        rw [card_range] at hP
        rw [mul_assoc, hP]

/-- **Ireland–Rosen, Proposition 6.4.2.** For an odd prime `p` and `ζ = e^(2πi/p)`,
`∏_{k=1}^{(p-1)/2} (ζ^(2k-1) - ζ^(-(2k-1)))² = (-1)^((p-1)/2) p`. -/
@[kb "irelandrosen1990" "Prop 6.4.2, p. 85"]
theorem prod_zeta_sub_inv_sq {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    ∏ k ∈ Icc 1 ((p - 1) / 2),
      (cexp (2 * π * I / p) ^ (2 * k - 1) - (cexp (2 * π * I / p) ^ (2 * k - 1))⁻¹) ^ 2 =
      (-1) ^ ((p - 1) / 2) * p := by
  rw [← Finset.Ico_add_one_right_eq_Icc, prod_Ico_eq_prod_range, Nat.add_sub_cancel,
    ← prod_range_zeta_sub_inv_sq hp]
  refine prod_congr rfl fun k _ ↦ ?_
  rw [show 2 * (1 + k) - 1 = 2 * k + 1 by omega]

/-- `ζ^j - ζ^(-j) = 2i sin(2πj/p)` for `ζ = e^(2πi/p)`. -/
theorem zeta_pow_sub_inv_eq_sin (p j : ℕ) :
    cexp (2 * π * I / p) ^ j - (cexp (2 * π * I / p) ^ j)⁻¹ =
      2 * I * (Real.sin (2 * π * j / p) : ℂ) := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_neg]
  have := eisensteinF_eq_sin ((j : ℂ) / p)
  rw [eisensteinF] at this
  rw [show (j : ℂ) * (2 * π * I / p) = 2 * π * I * (j / p) by ring, this]
  push_cast
  ring_nf

/-- The sign in Proposition 6.4.3: exactly `⌊p/4⌋` of the numbers `sin(2π(2k+1)/p)`,
`0 ≤ k < (p-1)/2`, are negative (and none vanishes). -/
theorem zero_lt_neg_one_pow_mul_prod_sin {p : ℕ} (hp0 : 0 < p) (hodd : Odd p) :
    0 < (-1) ^ (p / 4) * ∏ k ∈ range ((p - 1) / 2), Real.sin (2 * π * (2 * k + 1 : ℕ) / p) := by
  set m := (p - 1) / 2
  set t := p / 4
  have hpm : p = 2 * m + 1 := by obtain ⟨u, rfl⟩ := hodd; omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  rw [show m = (m - t) + t by omega, prod_range_add]
  have h1 : 0 < ∏ k ∈ range (m - t), Real.sin (2 * π * (2 * k + 1 : ℕ) / p) := by
    refine prod_pos fun k hk ↦ ?_
    have hk := mem_range.mp hk
    have h4 : 2 * (2 * k + 1) < p := by omega
    have h4R : (2 * (2 * k + 1 : ℕ) : ℝ) < p := by exact_mod_cast h4
    apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
    rw [div_lt_iff₀ hpR]
    nlinarith [Real.pi_pos]
  have h2 : 0 < ∏ j ∈ range t, -Real.sin (2 * π * (2 * (m - t + j) + 1 : ℕ) / p) := by
    refine prod_pos fun j hj ↦ ?_
    have hj := mem_range.mp hj
    set k := m - t + j
    have h4 : p < 2 * (2 * k + 1) := by omega
    have h5 : 2 * (2 * k + 1) < 2 * p := by omega
    have h4R : (p : ℝ) < (2 * (2 * k + 1) : ℕ) := by exact_mod_cast h4
    have h5R : ((2 * (2 * k + 1) : ℕ) : ℝ) < 2 * p := by exact_mod_cast h5
    push_cast at h4R h5R
    rw [← Real.sin_sub_pi]
    apply Real.sin_pos_of_pos_of_lt_pi
    · rw [sub_pos, lt_div_iff₀ hpR]; push_cast; nlinarith [Real.pi_pos]
    · rw [sub_lt_iff_lt_add, div_lt_iff₀ hpR]; push_cast; nlinarith [Real.pi_pos]
  rw [prod_neg, card_range] at h2
  rw [mul_left_comm]
  exact mul_pos h1 h2

/-- **Ireland–Rosen, Proposition 6.4.3.** For an odd prime `p` and `ζ = e^(2πi/p)`,
`∏_{k=1}^{(p-1)/2} (ζ^(2k-1) - ζ^(-(2k-1)))` equals `√p` if `p ≡ 1 (mod 4)` and `i√p` if
`p ≡ 3 (mod 4)`. -/
@[kb "irelandrosen1990" "Prop 6.4.3, p. 85"]
theorem prod_zeta_sub_inv {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    ∏ k ∈ Icc 1 ((p - 1) / 2),
      (cexp (2 * π * I / p) ^ (2 * k - 1) - (cexp (2 * π * I / p) ^ (2 * k - 1))⁻¹) =
      if p % 4 = 1 then (Real.sqrt p : ℂ) else I * Real.sqrt p := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  set m := (p - 1) / 2 with hm
  set t := p / 4 with ht
  have hpm : p = 2 * m + 1 := by obtain ⟨u, rfl⟩ := hodd; omega
  set R := ∏ k ∈ range m, Real.sin (2 * π * (2 * k + 1 : ℕ) / p) with hR
  -- the product is `(2i)^m R`
  have hprod : ∏ k ∈ Icc 1 m,
      (cexp (2 * π * I / p) ^ (2 * k - 1) - (cexp (2 * π * I / p) ^ (2 * k - 1))⁻¹) =
      (2 * I) ^ m * (R : ℂ) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, prod_Ico_eq_prod_range, Nat.add_sub_cancel, hR]
    push_cast
    rw [← card_range m, ← prod_const, card_range, ← prod_mul_distrib]
    refine prod_congr rfl fun k _ ↦ ?_
    rw [show 2 * (1 + k) - 1 = 2 * k + 1 by omega, zeta_pow_sub_inv_eq_sin]
    push_cast
    ring_nf
  -- its square is `(-1)^m p` (Proposition 6.4.2), so `4^m R² = p`
  have hsq := prod_zeta_sub_inv_sq hp
  rw [prod_pow, hprod, mul_pow, ← pow_mul, mul_comm m 2, pow_mul, mul_pow, I_sq] at hsq
  have h4 : (4 : ℝ) ^ m * R ^ 2 = p := by
    have : ((4 : ℝ) ^ m * R ^ 2 : ℝ) = ((p : ℝ) : ℂ) := by
      have h1 : ((-1 : ℂ) ^ m) * (-1) ^ m = 1 := by rw [← mul_pow]; simp
      calc ((4 : ℝ) ^ m * R ^ 2 : ℝ) = ((-1 : ℂ) ^ m * (-1) ^ m) * ((4 : ℝ) ^ m * R ^ 2 : ℝ) := by
            rw [h1, one_mul]
        _ = (-1) ^ m * ((2 ^ 2 * -1) ^ m * (R : ℂ) ^ 2) := by
            rw [mul_pow (2 ^ 2 : ℂ) (-1)]; push_cast; ring
        _ = ((p : ℝ) : ℂ) := by rw [hsq, ← hm, ← mul_assoc, h1, one_mul]; push_cast; rfl
    exact_mod_cast this
  -- `2^m |R| = √p` and `|R| = (-1)^t R`
  have hsign := zero_lt_neg_one_pow_mul_prod_sin hp0 hodd
  rw [← hm, ← ht, ← hR] at hsign
  have habs : |R| = (-1) ^ t * R := by
    rw [← abs_of_pos hsign, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hsqrt : (2 : ℝ) ^ m * |R| = Real.sqrt p := by
    rw [← h4, show (4 : ℝ) ^ m * R ^ 2 = ((2 : ℝ) ^ m * |R|) ^ 2 by
      rw [mul_pow, sq_abs, ← pow_mul, mul_comm m 2, pow_mul]; norm_num,
      Real.sqrt_sq (by positivity)]
  have hu : ((-1 : ℂ) ^ t) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  have hRval : (2 : ℂ) ^ m * R = (-1) ^ t * (Real.sqrt p : ℝ) := by
    rw [← hsqrt, habs]
    push_cast
    linear_combination (-((2 : ℂ) ^ m * R)) * hu
  rw [hprod, mul_pow, mul_comm ((2 : ℂ) ^ m), mul_assoc, hRval]
  split_ifs with h1
  · have : m = 2 * t := by omega
    rw [this, pow_mul, I_sq]
    linear_combination (Real.sqrt p : ℂ) * hu
  · have : m = 2 * t + 1 := by omega
    rw [this, pow_succ, pow_mul, I_sq]
    linear_combination (I * Real.sqrt p) * hu

end NTKB.IrelandRosen
