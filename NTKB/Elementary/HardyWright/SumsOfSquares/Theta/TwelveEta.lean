/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TwelveLattice
import Mathlib.NumberTheory.ModularForms.Discriminant

/-!
# The cusp form `η(τ)¹²`

`η¹²` (Mathlib's Dedekind `eta`) transforms like `θ¹²` under `S` and `T²`:

* `eta12_S`: `η(-1/τ)¹² = -τ⁶ η(τ)¹²`, from Mathlib's `η(-1/z) = (√i)⁻¹ √z η(z)`
  (`ModularForm.eta_comp_eq_csqrt_I_inv`);
* `eta12_T`: `η(τ + 1)¹² = -η(τ)¹²`; hence `η¹²` is `T²`-invariant and `η((τ-1)/τ)¹² = τ⁶ η(τ)¹²`;
* `eta12_eq`: `η(τ)¹² = q ∏_{m ≥ 1} (1 - q^{2m})¹²` with `q = e^{πiτ}`, i.e. `η(2z)¹²` in the
  variable `e^{2πiz}`, `z = τ/2`.
-/

open ModularForm ModularGroup Complex Filter Topology
open scoped MatrixGroups Real UpperHalfPlane Manifold
open UpperHalfPlane hiding I

noncomputable section

namespace NTKB.HardyWright.TwelveSquares

open EightSquares (mdiff_of_eqOn coe_S_smul coe_T_smul coe_T_zpow_smul ne_zero')

/-- `η(τ)¹²`. -/
def eta12 (τ : ℍ) : ℂ := ModularForm.eta τ ^ 12

lemma csqrt_pow_twelve (z : ℂ) : Complex.sqrt z ^ 12 = z ^ 6 := by
  rw [Complex.sqrt, show (12 : ℕ) = 2 * 6 from rfl, pow_mul, cpow_ofNat_inv_pow]

lemma csqrt_I_pow_twelve : Complex.sqrt I ^ 12 = -1 := by
  rw [csqrt_pow_twelve, show (6 : ℕ) = 2 * 3 from rfl, pow_mul, I_sq]; norm_num

lemma eta12_S (τ : ℍ) : eta12 (S • τ) = -((τ : ℂ) ^ 6 * eta12 τ) := by
  have he : ModularForm.eta (-1 / (τ : ℂ)) =
      (Complex.sqrt I)⁻¹ * (Complex.sqrt τ * ModularForm.eta τ) :=
    ModularForm.eta_comp_eq_csqrt_I_inv τ.2
  rw [eta12, eta12, coe_S_smul, he, mul_pow, mul_pow, inv_pow, csqrt_I_pow_twelve,
    csqrt_pow_twelve]
  ring

lemma eta_add_one (z : ℂ) : ModularForm.eta (z + 1) = cexp (2 * π * I / 24) * ModularForm.eta z := by
  have hq1 : ∀ n : ℕ, ModularForm.eta_q n (z + 1) = ModularForm.eta_q n z := by
    intro n
    rw [ModularForm.eta_q_eq_pow, ModularForm.eta_q_eq_pow, mul_add, mul_one, Complex.exp_add,
      Complex.exp_two_pi_mul_I, mul_one]
  have h24 : Function.Periodic.qParam 24 (z + 1) = cexp (2 * π * I / 24) * Function.Periodic.qParam 24 z := by
    simp only [Function.Periodic.qParam]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [ModularForm.eta, ModularForm.eta, h24]
  simp only [hq1]
  ring

lemma eta12_add_one (z : ℂ) : ModularForm.eta (z + 1) ^ 12 = -ModularForm.eta z ^ 12 := by
  rw [eta_add_one, mul_pow, ← Complex.exp_nat_mul]
  have : ((12 : ℕ) : ℂ) * (2 * π * I / 24) = π * I := by push_cast; ring
  rw [this, Complex.exp_pi_mul_I]
  ring

lemma eta12_T (τ : ℍ) : eta12 (T • τ) = -eta12 τ := by
  rw [eta12, eta12, coe_T_smul, eta12_add_one]

lemma eta12_T_sq (τ : ℍ) : eta12 (T ^ (2 : ℤ) • τ) = eta12 τ := by
  rw [eta12, eta12, coe_T_zpow_smul]
  push_cast
  rw [show (τ : ℂ) + 2 = ((τ : ℂ) + 1) + 1 by ring, eta12_add_one, eta12_add_one]
  ring

lemma eta12_TS (τ : ℍ) : eta12 ((T * S) • τ) = (τ : ℂ) ^ 6 * eta12 τ := by
  rw [mul_smul, eta12_T, eta12_S]
  ring

lemma diffOn_eta12 : DifferentiableOn ℂ (fun z => ModularForm.eta z ^ 12) {z : ℂ | 0 < z.im} := by
  intro z hz
  have h : DifferentiableAt ℂ ModularForm.eta z :=
    differentiableAt_eta_of_mem_upperHalfPlaneSet hz
  exact (h.pow 12).differentiableWithinAt

lemma mdiff_eta12 : MDiff eta12 :=
  mdiff_of_eqOn diffOn_eta12 fun τ => by rw [eta12]

/-- `η(τ)¹² = q ∏_{m ≥ 0} (1 - q^{2(m+1)})¹²`, `q = e^{πiτ}`. -/
lemma eta12_eq (τ : ℍ) : eta12 τ =
    cexp (π * I * τ) * ∏' m : ℕ, (1 - cexp (π * I * τ) ^ (2 * (m + 1))) ^ 12 := by
  have hm : Multipliable fun n : ℕ => 1 - ModularForm.eta_q n (τ : ℂ) :=
    ModularForm.multipliableLocallyUniformlyOn_eta.multipliable τ.2
  have h1 : (∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ))) ^ 12 =
      ∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ)) ^ 12 := (hm.tprod_pow 12).symm
  have h2 : Function.Periodic.qParam 24 (τ : ℂ) ^ 12 = cexp (π * I * τ) := by
    simp only [Function.Periodic.qParam]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h3 : ∀ m : ℕ, ModularForm.eta_q m (τ : ℂ) = cexp (π * I * τ) ^ (2 * (m + 1)) := by
    intro m
    rw [ModularForm.eta_q_eq_pow, pow_mul, ← Complex.exp_nat_mul (π * I * τ) 2,
      show ((2 : ℕ) : ℂ) * (π * I * τ) = 2 * π * I * τ by push_cast; ring]
  rw [eta12, ModularForm.eta, mul_pow, h1, h2]
  simp only [h3]

end NTKB.HardyWright.TwelveSquares
