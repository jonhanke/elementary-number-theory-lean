/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TenCusp
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.TenStatement

/-!
# The cusp form `C` on the upper half-plane

* `cusp τ = C(τ)` for `τ ∈ ℍ`, with `cusp_S`, `cusp_T_sq`, `cusp_TS` (the laws of `θ¹⁰`) and the
  bound `norm_cuspTS_le` at the cusp `1`;
* `mdiff_cusp`: `C` is holomorphic;
* `hasSum_cuspC`: `C(τ) = ∑ₙ c(n) qⁿ`, `q = e^{πiτ}`, with `c(n) = ∑_{x² + y² = n} (x⁴ - 6x²y² + y⁴)`
  (`liouvilleCusp`, the real part of `∑_{N(a) = n} a⁴`).
-/

open Complex Filter Topology ModularForm ModularGroup
open scoped Real UpperHalfPlane MatrixGroups Manifold
open UpperHalfPlane hiding I

noncomputable section

namespace NTKB.HardyWright.TenSquares

open EightSquares (mdiff_of_eqOn coe_S_smul coe_T_zpow_smul coe_TS_smul ne_zero')

/-! ### Norms -/

lemma norm_cf_one (α β : ℝ) (τ : ℂ) (v : ℤ × ℤ) :
    ‖cf (fun _ => 1) α β τ v‖ = Real.exp (-π * τ.im * (((v.1 : ℝ) + α) ^ 2 + ((v.2 : ℝ) + β) ^ 2)) := by
  rw [cf, norm_mul, norm_one, one_mul]
  have e : (((v.1 : ℂ) + α) ^ 2 + ((v.2 : ℂ) + β) ^ 2) =
      ((((v.1 : ℝ) + α : ℝ) : ℂ)) ^ 2 + ((((v.2 : ℝ) + β : ℝ) : ℂ)) ^ 2 := by push_cast; ring
  rw [e, norm_cexp_quad]

lemma norm_cf_one_anti (α β : ℝ) {τ τ' : ℂ} (h : τ'.im ≤ τ.im) (v : ℤ × ℤ) :
    ‖cf (fun _ => 1) α β τ v‖ ≤ ‖cf (fun _ => 1) α β τ' v‖ := by
  rw [norm_cf_one, norm_cf_one]
  refine Real.exp_le_exp.mpr ?_
  have : 0 ≤ ((v.1 : ℝ) + α) ^ 2 + ((v.2 : ℝ) + β) ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h this) Real.pi_pos.le
  linarith

lemma summable_norm_mul_pow {s : ℤ × ℤ → ℂ} {α β : ℝ} {τ : ℂ}
    (h : ExpSummable (cf s α β τ) (uf α β)) (k : ℕ) :
    Summable fun v => ‖cf s α β τ v‖ * ‖uf α β v‖ ^ k := by
  refine Summable.of_nonneg_of_le (fun v => by positivity) (fun v => ?_)
    ((h (0 + 1)).mul_left (k.factorial : ℝ))
  have := norm_term_le (c := cf s α β τ v) (u := uf α β v) k (R := 0) (z := 0) (by simp)
  simpa [norm_mul, norm_pow, mul_assoc] using this

/-- The bound for `D` on `Im τ ≥ 1`. -/
def MD : ℝ := ∑' v, ‖cf (fun _ => 1) (1 / 2) (1 / 2) I v‖ * ‖uf (1 / 2) (1 / 2) v‖ ^ 4

lemma norm_cuspD_le {τ : ℂ} (hτ : 1 ≤ τ.im) : ‖(2 * π : ℂ) ^ 4 * cuspD τ‖ ≤ MD := by
  rw [← sum_cf_half]
  have hI : (0 : ℝ) < I.im := by simp
  refine tsum_of_norm_bounded (summable_norm_mul_pow (expSummable_half hI) 4).hasSum fun v => ?_
  rw [norm_mul, norm_pow]
  gcongr
  exact norm_cf_one_anti _ _ (by simpa using hτ) v

/-! ### On the upper half-plane -/

/-- `C` on `ℍ`. -/
def cusp (τ : ℍ) : ℂ := cuspC τ

/-- `-i D`, the factor of `C` at the cusp `1`. -/
def cuspTS (τ : ℍ) : ℂ := -I * cuspD τ

lemma cusp_S (τ : ℍ) : cusp (S • τ) = -I * (τ : ℂ) ^ 5 * cusp τ := by
  rw [cusp, cusp, coe_S_smul, cuspC_S τ.2]

lemma cusp_T_sq (τ : ℍ) : cusp (T ^ (2 : ℤ) • τ) = cusp τ := by
  rw [cusp, cusp, coe_T_zpow_smul]
  push_cast
  exact cuspC_add_two _

lemma cusp_TS (τ : ℍ) : cusp ((T * S) • τ) = (τ : ℂ) ^ 5 * cuspTS τ := by
  rw [cusp, cuspTS, coe_TS_smul]
  have h0 := ne_zero' τ
  rw [show ((τ : ℂ) - 1) / τ = 1 + -1 / τ by field_simp; ring, cuspC_TS τ.2]
  ring

/-- The constant of `norm_cuspTS_le`. -/
def MTSc : ℝ := MD / (2 * π) ^ 4

lemma norm_cuspTS_le (τ : ℍ) (hτ : 1 ≤ τ.im) : ‖cuspTS τ‖ ≤ MTSc := by
  have h := norm_cuspD_le (τ := (τ : ℂ)) hτ
  have hπ : (0 : ℝ) < (2 * π) ^ 4 := by positivity
  rw [norm_mul, norm_pow] at h
  have e : ‖(2 * π : ℂ)‖ = 2 * π := by
    rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  rw [e] at h
  rw [cuspTS, norm_mul, norm_neg, Complex.norm_I, one_mul, MTSc, le_div_iff₀ hπ]
  linarith

/-! ### Holomorphy -/

lemma differentiableOn_cuspC : DifferentiableOn ℂ cuspC {z : ℂ | 0 < z.im} := by
  have hfun : cuspC = fun τ => ((2 * π : ℂ) ^ 4)⁻¹ *
      ∑' v, cf (fun _ => 1) 0 0 τ v * uf 0 0 v ^ 4 := by
    funext τ
    rw [sum_cf_zero]
    have hπ : (2 * (π : ℂ)) ^ 4 ≠ 0 := pow_ne_zero _ (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    field_simp
  rw [hfun]
  refine DifferentiableOn.const_mul ?_ _
  intro z0 hz0
  have hz0' : (0 : ℝ) < z0.im := hz0
  set B : ℝ := z0.im / 2
  have hB : 0 < B := by positivity
  set V := {z : ℂ | B < z.im}
  have hV : IsOpen V := isOpen_lt continuous_const Complex.continuous_im
  have hzV : z0 ∈ V := by show B < z0.im; simp only [B]; linarith
  have hBI : (0 : ℝ) < (I * B).im := by simpa using hB
  have hd : DifferentiableOn ℂ (fun z => ∑' v, cf (fun _ => 1) 0 0 z v * uf 0 0 v ^ 4) V := by
    refine differentiableOn_tsum_of_summable_norm
      (summable_norm_mul_pow (expSummable_zero hBI) 4) (fun v => ?_) hV (fun v z hz => ?_)
    · refine DifferentiableOn.mul ?_ (differentiableOn_const _)
      refine DifferentiableOn.mul (differentiableOn_const _) ?_
      exact (((differentiableOn_const _).mul differentiableOn_id).mul
        (differentiableOn_const _)).cexp
    · rw [norm_mul, norm_pow]
      gcongr
      exact norm_cf_one_anti _ _ (by simpa using (le_of_lt hz)) v
  exact (hd.differentiableAt (hV.mem_nhds hzV)).differentiableWithinAt

lemma mdiff_cusp : MDiff cusp :=
  mdiff_of_eqOn differentiableOn_cuspC fun _ => rfl

/-! ### The `q`-expansion -/

/-- `x⁴ - 6x²y² + y⁴`, the real part of `(x + iy)⁴`. -/
def rePoly (v : ℤ × ℤ) : ℤ := v.1 ^ 4 - 6 * v.1 ^ 2 * v.2 ^ 2 + v.2 ^ 4

/-- The swap `(m, n) ↦ (m, -n)`. -/
def conjEquiv : ℤ × ℤ ≃ ℤ × ℤ := Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)

lemma summable_cuspC_terms {τ : ℂ} (hτ : 0 < τ.im) :
    Summable fun v : ℤ × ℤ => ((v.1 : ℂ) + I * v.2) ^ 4 *
      cexp (π * I * τ * ((v.1 : ℂ) ^ 2 + (v.2 : ℂ) ^ 2)) := by
  have hs := (summable_norm_mul_pow (expSummable_zero hτ) 4)
  have hπ : (0 : ℝ) < (2 * π) ^ 4 := by positivity
  refine Summable.of_norm_bounded (hs.mul_left ((2 * π) ^ 4)⁻¹) fun v => ?_
  have e := uf_pow_four 0 0 v
  simp only [Complex.ofReal_zero, add_zero] at e
  have hn : ‖uf 0 0 v‖ ^ 4 = (2 * π) ^ 4 * ‖((v.1 : ℂ) + I * v.2) ^ 4‖ := by
    rw [← norm_pow, e, norm_mul, norm_pow, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
  rw [hn, norm_mul]
  have hc : ‖cexp (π * I * τ * ((v.1 : ℂ) ^ 2 + (v.2 : ℂ) ^ 2))‖ = ‖cf (fun _ => 1) 0 0 τ v‖ := by
    simp [cf]
  rw [hc]
  field_simp
  rfl

lemma cuspC_eq_rePoly {τ : ℂ} (hτ : 0 < τ.im) :
    cuspC τ = ∑' v : ℤ × ℤ, (rePoly v : ℂ) * cexp (π * I * τ * ((v.1 : ℂ) ^ 2 + (v.2 : ℂ) ^ 2)) := by
  have hs := summable_cuspC_terms hτ
  have hs' : Summable fun v : ℤ × ℤ => ((v.1 : ℂ) - I * v.2) ^ 4 *
      cexp (π * I * τ * ((v.1 : ℂ) ^ 2 + (v.2 : ℂ) ^ 2)) := by
    refine (conjEquiv.summable_iff.mpr hs).congr fun v => ?_
    simp [conjEquiv]
    ring_nf
  have h1 : cuspC τ = ∑' v : ℤ × ℤ, ((v.1 : ℂ) - I * v.2) ^ 4 *
      cexp (π * I * τ * ((v.1 : ℂ) ^ 2 + (v.2 : ℂ) ^ 2)) := by
    rw [cuspC, ← conjEquiv.tsum_eq]
    refine tsum_congr fun v => ?_
    simp [conjEquiv]
    ring_nf
  have h2 : 2 * cuspC τ = ∑' v : ℤ × ℤ, (2 * (rePoly v : ℂ)) *
      cexp (π * I * τ * ((v.1 : ℂ) ^ 2 + (v.2 : ℂ) ^ 2)) := by
    calc 2 * cuspC τ = cuspC τ + cuspC τ := two_mul _
      _ = (∑' v : ℤ × ℤ, ((v.1 : ℂ) + I * v.2) ^ 4 *
            cexp (π * I * τ * ((v.1 : ℂ) ^ 2 + (v.2 : ℂ) ^ 2))) +
          ∑' v : ℤ × ℤ, ((v.1 : ℂ) - I * v.2) ^ 4 *
            cexp (π * I * τ * ((v.1 : ℂ) ^ 2 + (v.2 : ℂ) ^ 2)) := congrArg₂ (· + ·) rfl h1
      _ = _ := by
        rw [← hs.tsum_add hs']
        refine tsum_congr fun v => ?_
        simp only [rePoly]
        push_cast
        ring_nf
        rw [I_sq, I_pow_four]
        ring
  have h3 : ∑' v : ℤ × ℤ, (2 * (rePoly v : ℂ)) * cexp (π * I * τ * ((v.1 : ℂ) ^ 2 + (v.2 : ℂ) ^ 2)) =
      2 * ∑' v : ℤ × ℤ, (rePoly v : ℂ) * cexp (π * I * τ * ((v.1 : ℂ) ^ 2 + (v.2 : ℂ) ^ 2)) := by
    rw [← tsum_mul_left]; refine tsum_congr fun v => ?_; ring
  rw [h3] at h2
  exact mul_left_cancel₀ two_ne_zero h2

/-- `m² + n²` as a natural number. -/
def normSq' (v : ℤ × ℤ) : ℕ := (v.1 ^ 2 + v.2 ^ 2).toNat

lemma normSq'_cast (v : ℤ × ℤ) : ((normSq' v : ℕ) : ℤ) = v.1 ^ 2 + v.2 ^ 2 :=
  Int.toNat_of_nonneg (by positivity)

lemma cexp_eq_q_pow (τ : ℂ) (v : ℤ × ℤ) :
    cexp (π * I * τ * ((v.1 : ℂ) ^ 2 + (v.2 : ℂ) ^ 2)) = cexp (π * I * τ) ^ normSq' v := by
  rw [← Complex.exp_nat_mul]
  congr 1
  have : ((normSq' v : ℕ) : ℂ) = (v.1 : ℂ) ^ 2 + (v.2 : ℂ) ^ 2 := by
    have := congrArg (fun x : ℤ => (x : ℂ)) (normSq'_cast v)
    push_cast at this
    exact this
  rw [this]; ring

lemma fiber_eq (n : ℕ) : normSq' ⁻¹' {n} = ↑(((Finset.Icc (-(n : ℤ)) n) ×ˢ (Finset.Icc (-(n : ℤ)) n)).filter
      (fun v : ℤ × ℤ => v.1 ^ 2 + v.2 ^ 2 = n)) := by
  ext v
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.coe_filter, Finset.mem_product,
    Finset.mem_Icc, Set.mem_ofPred_eq]
  have hc := normSq'_cast v
  constructor
  · intro h
    rw [h] at hc
    have h1 : v.1 ^ 2 ≤ n := by nlinarith [sq_nonneg v.2]
    have h2 : v.2 ^ 2 ≤ n := by nlinarith [sq_nonneg v.1]
    refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, hc.symm⟩ <;> nlinarith [sq_nonneg (v.1 + 1), sq_nonneg (v.1 - 1),
      sq_nonneg (v.2 + 1), sq_nonneg (v.2 - 1)]
  · rintro ⟨_, h⟩
    rw [h] at hc
    exact_mod_cast hc

/-- **The `q`-expansion of `C`.** `C(τ) = ∑ₙ c(n) qⁿ`, `q = e^{πiτ}`. -/
theorem hasSum_cuspC {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℕ => (liouvilleCusp n : ℂ) * cexp (π * I * τ) ^ n) (cuspC τ) := by
  have hc : ∀ v : ℤ × ℤ, cexp (π * I * τ * ((v.1 : ℂ) ^ 2 + (v.2 : ℂ) ^ 2)) =
      cexp (π * I * τ) ^ normSq' v := cexp_eq_q_pow τ
  have hs : Summable fun v : ℤ × ℤ => (rePoly v : ℂ) * cexp (π * I * τ) ^ normSq' v := by
    have hn := summable_norm_iff.mpr (summable_cuspC_terms hτ)
    refine Summable.of_norm_bounded hn fun v => ?_
    rw [← hc, norm_mul, norm_mul]
    gcongr
    -- `|x⁴ - 6x²y² + y⁴| ≤ |x + iy|⁴`
    have e : ‖((v.1 : ℂ) + I * v.2) ^ 4‖ = ((v.1 : ℝ) ^ 2 + (v.2 : ℝ) ^ 2) ^ 2 := by
      rw [norm_pow]
      have : ‖(v.1 : ℂ) + I * v.2‖ = Real.sqrt ((v.1 : ℝ) ^ 2 + (v.2 : ℝ) ^ 2) := by
        rw [Complex.norm_def, Complex.normSq_apply]
        congr 1
        simp; ring
      rw [this, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (by positivity)]
    rw [e, Complex.norm_intCast, rePoly]
    push_cast
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg ((v.1 : ℝ) ^ 2 - (v.2 : ℝ) ^ 2), sq_nonneg ((v.1 : ℝ) * v.2),
      sq_nonneg ((v.1 : ℝ) ^ 2 + (v.2 : ℝ) ^ 2)]
  have hsum : HasSum (fun v : ℤ × ℤ => (rePoly v : ℂ) * cexp (π * I * τ) ^ normSq' v) (cuspC τ) := by
    rw [cuspC_eq_rePoly hτ]
    simp only [hc]
    exact hs.hasSum
  have hfib := hsum.tsum_fiberwise normSq'
  convert hfib using 1
  funext n
  have hF := Finset.tsum_subtype' (((Finset.Icc (-(n : ℤ)) n) ×ˢ (Finset.Icc (-(n : ℤ)) n)).filter
      (fun v : ℤ × ℤ => v.1 ^ 2 + v.2 ^ 2 = n)) (fun v : ℤ × ℤ => (rePoly v : ℂ) * cexp (π * I * τ) ^ normSq' v)
  rw [← fiber_eq] at hF
  rw [hF, liouvilleCusp]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun v hv => ?_
  simp only [Finset.mem_filter] at hv
  have : normSq' v = n := by
    have := normSq'_cast v
    rw [hv.2] at this
    exact_mod_cast this
  rw [this, rePoly]
  push_cast
  ring

end NTKB.HardyWright.TenSquares
