/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.EightBounds
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.EightCount

/-!
# Hardy–Wright, § 20.13: Jacobi's formula for `r₈(n)`

`r₈(n) = 16 ∑_{d ∣ n} (-1)^{n+d} d³` for `n ≥ 1` (`sumSquaresCount_eight_eq`). The book states the
formula without proof. The proof here (see `EightModular.lean` for the plan):

* `g₃` is bounded at `i∞` (`norm_g3_le`): its theta part is `e^{2πiτ} θ₂(…)⁸` by the functional
  equation of `jacobiTheta₂`, its Eisenstein part is `(E₄((τ+1)/2) - 2E₄(τ) + E₄(τ/2))/15`;
* `N/Δ` is a level-one modular form of weight `0` (`quotientForm`), hence constant, and it tends to
  `0` at `i∞`, so `N = 0`; by the identity theorem `g₁ = 0` (`jacobiTheta_pow_eight`);
* at `τ = it` this is an identity of real power series in `x = e^{-πt}`, and `EightCount.lean`
  compares coefficients.
-/

open ModularForm ModularGroup Complex Filter Topology Asymptotics
open scoped MatrixGroups Real UpperHalfPlane Manifold
open UpperHalfPlane hiding I

noncomputable section

namespace NTKB.HardyWright.EightSquares

/-! ### `g₃` is bounded at `i∞` -/

/-- `T S = [[1, -1], [1, 0]]`. -/
lemma coe_TS : ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, -1; 1, 0] := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_S, coe_T]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma SL_smul_eq_of (g : SL(2, ℤ)) (τ : ℍ) (z : ℂ)
    (h : z * ((g 1 0 : ℂ) * τ + g 1 1) = (g 0 0 : ℂ) * τ + g 0 1) : ((g • τ : ℍ) : ℂ) = z := by
  have hd : ((g 1 0 : ℂ) * τ + g 1 1) ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero g τ
    simpa [ModularGroup.denom_apply] using this
  rw [coe_SL_smul, eq_comm, eq_div_iff hd]; exact h

lemma coe_TS_smul (τ : ℍ) : (((T * S) • τ : ℍ) : ℂ) = ((τ : ℂ) - 1) / τ := by
  apply SL_smul_eq_of
  rw [coe_TS]; simp
  have := ne_zero' τ
  field_simp
  ring

lemma denom_TS (τ : ℍ) : denom ((T * S : SL(2, ℤ)) : GL (Fin 2) ℝ) τ = τ := by
  rw [ModularGroup.denom_apply, coe_TS]; simp

lemma g3_eq_slash : g3 = g1 ∣[(4 : ℤ)] (T * S) := by
  rw [g3, g2, SlashAction.slash_mul]

/-- `γ₁ = [[1, -1], [2, -1]]`. -/
def γ1 : SL(2, ℤ) := ⟨!![1, -1; 2, -1], by simp [Matrix.det_fin_two]⟩

/-- `γ₃ = [[2, -1], [1, 0]]`. -/
def γ3 : SL(2, ℤ) := ⟨!![2, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

/-- `(τ + 1)/2`. -/
def w1 (τ : ℍ) : ℍ := ⟨((τ : ℂ) + 1) / 2, by simpa using τ.im_pos⟩

lemma halfH_TS (τ : ℍ) : halfH ((T * S) • τ) = γ1 • w1 τ := by
  ext
  rw [coe_halfH, coe_TS_smul, eq_comm]
  apply SL_smul_eq_of
  simp only [γ1, w1, UpperHalfPlane.coe_mk]
  simp
  have := ne_zero' τ
  field_simp
  ring

lemma twoH_TS (τ : ℍ) : twoH ((T * S) • τ) = γ3 • halfH τ := by
  ext
  rw [coe_twoH, coe_TS_smul, eq_comm]
  apply SL_smul_eq_of
  simp only [γ3, coe_halfH]
  simp
  have := ne_zero' τ
  field_simp
  ring

lemma e1_TS (τ : ℍ) : e1 ((T * S) • τ) =
    (τ : ℂ) ^ 4 * ((E₄ (w1 τ) - 2 * E₄ τ + E₄ (halfH τ)) / 15) := by
  have h1 : E₄ (γ1 • w1 τ) = (τ : ℂ) ^ 4 * E₄ (w1 τ) := by
    rw [E4_smul]; congr 2; simp [γ1, w1]; ring
  have h3 : E₄ (γ3 • halfH τ) = ((τ : ℂ) / 2) ^ 4 * E₄ (halfH τ) := by
    rw [E4_smul]; congr 2; simp [γ3]
  have h2 : E₄ ((T * S) • τ) = (τ : ℂ) ^ 4 * E₄ τ := by
    rw [E4_smul, coe_TS]; simp
  simp only [e1, halfH_TS, twoH_TS, h1, h2, h3]
  ring

lemma jacobiTheta_one_add (z : ℂ) : jacobiTheta (1 + z) = jacobiTheta₂ (1 / 2) z := by
  rw [jacobiTheta, jacobiTheta₂]
  refine tsum_congr fun n => ?_
  rw [jacobiTheta₂_term]
  have hpar : ∃ m : ℤ, (n : ℂ) ^ 2 = n + 2 * m := ⟨(n ^ 2 - n) / 2, by
    have : (2 : ℤ) ∣ n ^ 2 - n := by
      have := Int.even_mul_pred_self n
      rw [show n ^ 2 - n = n * (n - 1) by ring]; exact this.two_dvd
    obtain ⟨k, hk⟩ := this
    rw [hk, Int.mul_ediv_cancel_left _ (by norm_num)]
    have : ((n ^ 2 - n : ℤ) : ℂ) = ((2 * k : ℤ) : ℂ) := by rw [hk]
    push_cast at this ⊢; linear_combination this⟩
  obtain ⟨m, hm⟩ := hpar
  have : (π : ℂ) * I * n ^ 2 * (1 + z) =
      2 * π * I * n * (1 / 2) + π * I * n ^ 2 * z + (m : ℂ) * (2 * π * I) := by
    rw [mul_add, mul_one, hm]; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The theta part of `g₃`: `θ((τ-1)/τ)⁸ τ⁻⁴ = e^{2πiτ} θ₂(-τ/2, τ)⁸`. -/
lemma theta8_TS (τ : ℍ) : jacobiTheta (((T * S) • τ : ℍ) : ℂ) ^ 8 =
    (τ : ℂ) ^ 4 * (cexp (2 * π * I * τ) * jacobiTheta₂ (-(τ : ℂ) / 2) τ ^ 8) := by
  have h0 := ne_zero' τ
  rw [coe_TS_smul, show ((τ : ℂ) - 1) / τ = 1 + (-1 / τ) by field_simp; ring, jacobiTheta_one_add,
    jacobiTheta₂_functional_equation]
  have e1' : -I * (-1 / (τ : ℂ)) = I / τ := by field_simp
  have e2 : -π * I * (1 / 2 : ℂ) ^ 2 / (-1 / (τ : ℂ)) = π * I * τ / 4 := by field_simp; ring
  have e3 : (1 / 2 : ℂ) / (-1 / (τ : ℂ)) = -(τ : ℂ) / 2 := by field_simp
  have e4 : -1 / (-1 / (τ : ℂ)) = τ := by field_simp
  rw [e1', e2, e3, e4, mul_pow, mul_pow, div_pow, cpow_half_pow_eight, one_pow,
    ← Complex.exp_nat_mul]
  have hI : (I / (τ : ℂ)) ^ 4 = 1 / (τ : ℂ) ^ 4 := by
    rw [div_pow, Complex.I_pow_four]
  rw [hI]
  have : ((8 : ℕ) : ℂ) * (π * I * τ / 4) = 2 * π * I * τ := by push_cast; ring
  rw [this]
  field_simp

/-- `K₁ = e^{2π} ∑_{n ∈ ℤ} e^{-π|n|}`. -/
def K1 : ℝ := rexp (2 * π) * ∑' n : ℤ, rexp (-π) ^ n.natAbs

lemma summable_exp_natAbs : Summable fun n : ℤ => rexp (-π) ^ n.natAbs := by
  have hr : rexp (-π) < 1 := by rw [Real.exp_lt_one_iff]; linarith [Real.pi_pos]
  have hs := summable_geometric_of_lt_one (Real.exp_pos (-π)).le hr
  exact Summable.of_nat_of_neg (by simpa using hs) (by simpa using hs)

lemma norm_jacobiTheta₂_half_le (τ : ℍ) (hτ : 1 ≤ τ.im) :
    ‖jacobiTheta₂ (-(τ : ℂ) / 2) τ‖ ≤ K1 := by
  have hb : ∀ n : ℤ, ‖jacobiTheta₂_term n (-(τ : ℂ) / 2) τ‖ ≤ rexp (2 * π) * rexp (-π) ^ n.natAbs := by
    intro n
    rw [norm_jacobiTheta₂_term, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hi : (-(τ : ℂ) / 2).im = -τ.im / 2 := by simp [neg_div]
    have hi' : (τ : ℂ).im = τ.im := rfl
    rw [hi, hi']
    have key : (n : ℝ) ^ 2 - n ≥ |(n : ℝ)| - 2 := by
      rcases le_or_gt 0 n with h | h
      · rw [abs_of_nonneg (by exact_mod_cast h)]; nlinarith
      · rw [abs_of_neg (by exact_mod_cast h)]; nlinarith
    have hnn : (n : ℝ) ^ 2 - n ≥ 0 := by
      rcases le_or_gt 0 n with h | h
      · rcases eq_or_lt_of_le h with h' | h'
        · rw [← h']; simp
        · have : (1 : ℝ) ≤ n := by exact_mod_cast h'
          nlinarith
      · have : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
        nlinarith
    have hna : ((n.natAbs : ℕ) : ℝ) = |(n : ℝ)| := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [hna]
    have hp := Real.pi_pos
    nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ τ.im from hτ) (mul_nonneg hp.le hnn)]
  have hs : HasSum (fun n : ℤ => rexp (2 * π) * rexp (-π) ^ n.natAbs) K1 :=
    summable_exp_natAbs.hasSum.mul_left _
  rw [jacobiTheta₂]
  exact tsum_of_norm_bounded hs hb

/-- The bound for `E₄` at `i∞`. -/
def ME : ℝ := 1 + (240 + 240 * K0)

lemma norm_E4_le (z : ℍ) (hz : 1 / 2 ≤ z.im) : ‖E₄ z‖ ≤ ME := by
  have h := norm_E4_sub_one_le z hz
  have he : rexp (-2 * π * z.im) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos]
  have hK := K0_nonneg
  calc ‖E₄ z‖ = ‖(E₄ z - 1) + 1‖ := by ring_nf
    _ ≤ ‖E₄ z - 1‖ + 1 := by simpa using norm_add_le (E₄ z - 1) 1
    _ ≤ (240 + 240 * K0) * 1 + 1 := by gcongr; exact h.trans (by gcongr)
    _ = ME := by rw [ME]; ring

lemma norm_g3_le (τ : ℍ) (hτ : 1 ≤ τ.im) : ‖g3 τ‖ ≤ K1 ^ 8 + 4 * ME / 15 := by
  have h0 := ne_zero' τ
  have hform : g3 τ = cexp (2 * π * I * τ) * jacobiTheta₂ (-(τ : ℂ) / 2) τ ^ 8 -
      (E₄ (w1 τ) - 2 * E₄ τ + E₄ (halfH τ)) / 15 := by
    rw [g3_eq_slash, SL_slash_apply, denom_TS]
    simp only [g1]
    rw [theta8_TS, e1_TS]
    rw [zpow_neg, zpow_ofNat]
    field_simp
  rw [hform]
  have hexp : ‖cexp (2 * π * I * τ)‖ ≤ 1 := by
    rw [Complex.norm_exp]
    rw [Real.exp_le_one_iff]
    have : (2 * π * I * (τ : ℂ)).re = -(2 * π * τ.im) := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [this]; nlinarith [Real.pi_pos, τ.im_pos]
  have hJ := norm_jacobiTheta₂_half_le τ hτ
  have hw1 : 1 / 2 ≤ (w1 τ).im := by
    change 1 / 2 ≤ (((τ : ℂ) + 1) / 2).im
    have : (((τ : ℂ) + 1) / 2).im = τ.im / 2 := by simp
    rw [this]; linarith
  have hh : 1 / 2 ≤ (halfH τ).im := by
    change 1 / 2 ≤ ((τ : ℂ) / 2).im
    have : ((τ : ℂ) / 2).im = τ.im / 2 := by simp
    rw [this]; linarith
  have a1 := norm_E4_le (w1 τ) hw1
  have a2 := norm_E4_le τ (by linarith)
  have a3 := norm_E4_le (halfH τ) hh
  have hK1 : 0 ≤ K1 := le_trans (norm_nonneg _) hJ
  calc _ ≤ ‖cexp (2 * π * I * τ) * jacobiTheta₂ (-(τ : ℂ) / 2) τ ^ 8‖ +
        ‖(E₄ (w1 τ) - 2 * E₄ τ + E₄ (halfH τ)) / 15‖ := norm_sub_le _ _
    _ ≤ 1 * K1 ^ 8 + (ME + 2 * ME + ME) / 15 := by
        rw [norm_mul, norm_pow, norm_div, Complex.norm_ofNat]
        gcongr
        refine (norm_add_le _ _).trans ?_
        refine add_le_add ?_ a3
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, Complex.norm_ofNat]
        linarith
    _ = K1 ^ 8 + 4 * ME / 15 := by ring

/-! ### `N / Δ` is a level-one modular form of weight `0` -/

lemma Nf_slash (γ : SL(2, ℤ)) : Nf ∣[(12 : ℤ)] γ = Nf :=
  SlashInvariantForm.slash_action_generators_SL2Z Nf_slash_S Nf_slash_T γ

lemma Delta_slash (γ : SL(2, ℤ)) : (ModularForm.discriminant : ℍ → ℂ) ∣[(12 : ℤ)] γ =
    ModularForm.discriminant :=
  SlashInvariantForm.slash_action_generators_SL2Z discriminant_S_invariant
    discriminant_T_invariant γ

/-- `N / Δ`. -/
def Qf (τ : ℍ) : ℂ := Nf τ / ModularForm.discriminant τ

lemma Qf_slash (γ : SL(2, ℤ)) : Qf ∣[(0 : ℤ)] γ = Qf := by
  ext τ
  have hN := congrFun (Nf_slash γ) τ
  have hD := congrFun (Delta_slash γ) τ
  rw [slash_action_eq'_iff] at hN hD
  rw [SL_slash_apply, Qf, Qf, hN, hD]
  have hd : ((γ 1 0 : ℂ) * τ + γ 1 1) ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero γ τ
    simpa [ModularGroup.denom_apply] using this
  have := discriminant_ne_zero τ
  field_simp
  simp

lemma mdiff_Nf : MDiff Nf := (mdiff_g1.mul mdiff_g2).mul mdiff_g3

lemma mdiff_Qf : MDiff Qf := by
  have hN := diffOn_comp_ofComplex mdiff_Nf
  have hD := diffOn_comp_ofComplex (CuspForm.discriminant.holo')
  refine mdiff_of_eqOn (F := fun z => (Nf ∘ ofComplex) z / (⇑CuspForm.discriminant ∘ ofComplex) z)
    (hN.div hD fun z hz => ?_) fun τ => ?_
  · simp only [Function.comp_apply, CuspForm.coe_discriminant]
    exact discriminant_ne_zero _
  · simp only [Qf]; rw [eval_ofComplex, eval_ofComplex]; rfl

lemma Cg_nonneg : 0 ≤ Cg := by have := K0_nonneg; rw [Cg]; positivity

lemma ME_nonneg : 0 ≤ ME := by have := K0_nonneg; rw [ME]; positivity

/-- `N/Δ = O(e^{-2π Im τ})` at `i∞`. -/
lemma Qf_isBigO : Qf =O[atImInfty] fun τ => rexp (-2 * π * τ.im) := by
  obtain ⟨c, hc, hcb⟩ := exp_isBigO_discriminant.exists_pos
  rw [IsBigOWith] at hcb
  have hev : ∀ᶠ τ : ℍ in atImInfty, 1 ≤ τ.im :=
    (tendsto_comap : Tendsto (fun τ : ℍ => τ.im) atImInfty atTop).eventually
      (eventually_ge_atTop 1)
  refine IsBigO.of_bound (Cg * Cg * (K1 ^ 8 + 4 * ME / 15) * c) ?_
  filter_upwards [hcb, hev] with τ hD hτ
  have hE := Real.exp_pos (-2 * π * τ.im)
  rw [Real.norm_of_nonneg hE.le] at hD
  have hDpos : 0 < ‖ModularForm.discriminant τ‖ := norm_pos_iff.mpr (discriminant_ne_zero τ)
  rw [Qf, norm_div, Real.norm_of_nonneg hE.le, div_le_iff₀ hDpos]
  have h1 := norm_g1_le τ hτ
  have h2 := norm_g2_le τ hτ
  have h3 := norm_g3_le τ hτ
  have hN : ‖Nf τ‖ ≤ Cg * rexp (-2 * π * τ.im) * (Cg * rexp (-2 * π * τ.im)) *
      (K1 ^ 8 + 4 * ME / 15) := by
    simp only [Nf, Pi.mul_apply, norm_mul]
    have := Cg_nonneg
    gcongr
  calc ‖Nf τ‖ ≤ Cg * rexp (-2 * π * τ.im) * (Cg * rexp (-2 * π * τ.im)) *
      (K1 ^ 8 + 4 * ME / 15) := hN
    _ = Cg * Cg * (K1 ^ 8 + 4 * ME / 15) * rexp (-2 * π * τ.im) * rexp (-2 * π * τ.im) := by ring
    _ ≤ Cg * Cg * (K1 ^ 8 + 4 * ME / 15) * rexp (-2 * π * τ.im) *
        (c * ‖ModularForm.discriminant τ‖) := by
        have : 0 ≤ Cg * Cg * (K1 ^ 8 + 4 * ME / 15) * rexp (-2 * π * τ.im) := by
          have := Cg_nonneg; have := ME_nonneg; positivity
        exact mul_le_mul_of_nonneg_left hD this
    _ = _ := by ring

lemma tendsto_exp_atImInfty : Tendsto (fun τ : ℍ => rexp (-2 * π * τ.im)) atImInfty (𝓝 0) := by
  have h : Tendsto (fun τ : ℍ => τ.im) atImInfty atTop := tendsto_comap
  have h2 : Tendsto (fun t : ℝ => rexp (-2 * π * t)) atTop (𝓝 0) := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (show (0 : ℝ) < 2 * π by positivity))
    refine this.congr fun t => ?_
    simp only [Function.comp_apply, id]; congr 1; ring
  exact h2.comp h

lemma Qf_tendsto : Tendsto Qf atImInfty (𝓝 0) :=
  Qf_isBigO.trans_tendsto tendsto_exp_atImInfty

/-- `N / Δ` as a level-one modular form of weight `0`. -/
def quotientForm : ModularForm 𝒮ℒ 0 where
  toFun := Qf
  slash_action_eq' γ hγ := by
    obtain ⟨g, rfl⟩ := hγ
    exact Qf_slash g
  holo' := mdiff_Qf
  bdd_at_cusps' hc := by
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [Qf_slash γ]
    have hb : (fun τ : ℍ => rexp (-2 * π * τ.im)) =O[atImInfty] (1 : ℍ → ℝ) :=
      IsBigO.of_bound 1 (Eventually.of_forall fun τ => by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]
        simp only [Pi.one_apply, norm_one, one_mul, Real.exp_le_one_iff]
        nlinarith [Real.pi_pos, τ.im_pos])
    exact Qf_isBigO.trans hb

lemma Nf_eq_zero (τ : ℍ) : Nf τ = 0 := by
  obtain ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const quotientForm
  have hQ : Qf = fun _ => c := by
    have : (⇑quotientForm : ℍ → ℂ) = Qf := rfl
    rw [← this, hc]; rfl
  have hc0 : c = 0 := by
    have h := Qf_tendsto
    rw [hQ] at h
    exact tendsto_nhds_unique tendsto_const_nhds h
  have hq := congrFun hQ τ
  rw [hc0, Qf, div_eq_zero_iff] at hq
  exact hq.resolve_right (discriminant_ne_zero τ)

/-! ### The identity theorem -/

lemma isPreconnected_U : IsPreconnected {z : ℂ | 0 < z.im} :=
  (convex_halfSpace_gt Complex.imLm.isLinear 0).isPreconnected

lemma analytic_comp {f : ℍ → ℂ} (hf : MDiff f) :
    AnalyticOnNhd ℂ (f ∘ ofComplex) {z : ℂ | 0 < z.im} :=
  (diffOn_comp_ofComplex hf).analyticOnNhd isOpen_upperHalfPlaneSet

lemma eq_zero_of_comp {f : ℍ → ℂ} (h : ∀ z ∈ {z : ℂ | 0 < z.im}, (f ∘ ofComplex) z = 0) :
    f = 0 := by
  ext τ
  have := h _ τ.im_pos
  rwa [eval_ofComplex] at this

lemma g1_eq_zero : g1 = 0 := by
  have hN : ∀ z ∈ {z : ℂ | 0 < z.im},
      ((g1 ∘ ofComplex) * (g2 ∘ ofComplex)) z * (g3 ∘ ofComplex) z = 0 := by
    intro z hz
    have := Nf_eq_zero (ofComplex z)
    simpa [Nf] using this
  rcases AnalyticOnNhd.eq_zero_or_eq_zero_of_mul_eq_zero
      ((analytic_comp mdiff_g1).mul (analytic_comp mdiff_g2)) (analytic_comp mdiff_g3) hN
      isPreconnected_U with h12 | h3
  · rcases AnalyticOnNhd.eq_zero_or_eq_zero_of_mul_eq_zero (analytic_comp mdiff_g1)
        (analytic_comp mdiff_g2) (fun z hz => h12 z hz) isPreconnected_U with h1 | h2
    · exact eq_zero_of_comp h1
    · have : g2 = 0 := eq_zero_of_comp h2
      rw [← g2_slash_T, this, SlashAction.zero_slash]
  · have : g3 = 0 := eq_zero_of_comp h3
    have h2 : g2 = 0 := by rw [← g3_slash_S, this, SlashAction.zero_slash]
    rw [← g2_slash_T, h2, SlashAction.zero_slash]

/-- **Jacobi's identity** `θ(τ)⁸ = (E₄(τ/2) - 2E₄(τ) + 16E₄(2τ))/15`. -/
theorem jacobiTheta_pow_eight (τ : ℍ) : jacobiTheta τ ^ 8 = e1 τ := by
  have := congrFun g1_eq_zero τ
  simp only [g1, Pi.zero_apply, sub_eq_zero] at this
  exact this

end NTKB.HardyWright.EightSquares

namespace NTKB.HardyWright

open EightSquares

/-- `θ(it)⁸ = e₁(it)` as an identity of real power series in `x = e^{-πt}`. -/
lemma theta_pow_eight_real {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    (∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 8 =
      1 + 16 * (sigmaThreeSeries x - 2 * sigmaThreeSeries (x ^ 2) + 16 * sigmaThreeSeries (x ^ 4)) := by
  set t := -Real.log x / π with ht
  have htpos : 0 < t := by
    have : Real.log x < 0 := Real.log_neg hx0 hx1
    rw [ht]; exact div_pos (by linarith) Real.pi_pos
  have hxt : rexp (-π * t) = x := by
    rw [ht, show -π * (-Real.log x / π) = Real.log x by field_simp]; exact Real.exp_log hx0
  set τ : ℍ := ⟨I * t, by simpa using htpos⟩ with hτ
  have hτc : (τ : ℂ) = I * t := rfl
  have h := jacobiTheta_pow_eight τ
  have hθ : jacobiTheta (τ : ℂ) = ((∑' m : ℤ, x ^ (m.natAbs ^ 2) : ℝ) : ℂ) := by
    rw [jacobiTheta, Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    rw [hτc, ← hxt, ← Real.exp_nat_mul, Complex.ofReal_exp]
    congr 1
    have hn : ((n.natAbs : ℕ) : ℂ) ^ 2 = (n : ℂ) ^ 2 := by
      have : ((n.natAbs : ℤ) : ℂ) ^ 2 = (n : ℂ) ^ 2 := by
        rw [← Int.cast_pow, Int.natAbs_sq]; push_cast; ring
      rwa [Int.cast_natCast] at this
    push_cast
    linear_combination (↑π * ↑t * (n : ℂ) ^ 2) * I_sq + (↑π * ↑t) * hn
  have hq : ∀ k : ℕ, ∀ z : ℍ, (z : ℂ) = (k : ℂ) * (I * t) / 2 →
      cexp (2 * π * I * z) = ((x ^ k : ℝ) : ℂ) := by
    intro k z hz
    rw [hz, ← hxt, ← Real.exp_nat_mul, Complex.ofReal_exp]
    congr 1
    push_cast
    linear_combination (↑π * ↑t * (k : ℂ)) * I_sq
  have hE : ∀ k : ℕ, ∀ z : ℍ, (z : ℂ) = (k : ℂ) * (I * t) / 2 →
      E₄ z = ((1 + 240 * sigmaThreeSeries (x ^ k) : ℝ) : ℂ) := by
    intro k z hz
    rw [E4_eq_tsum, hq k z hz, sigmaThreeSeries]
    push_cast
    rfl
  have h1 := hE 1 (halfH τ) (by rw [coe_halfH, hτc]; push_cast; ring)
  have h2 := hE 2 τ (by rw [hτc]; push_cast; ring)
  have h4 := hE 4 (twoH τ) (by rw [coe_twoH, hτc]; push_cast; ring)
  rw [pow_one] at h1
  rw [hθ, e1, h1, h2, h4] at h
  have h' : (((∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 8 : ℝ) : ℂ) =
      (((1 + 240 * sigmaThreeSeries x - 2 * (1 + 240 * sigmaThreeSeries (x ^ 2)) +
        16 * (1 + 240 * sigmaThreeSeries (x ^ 4))) / 15 : ℝ) : ℂ) := by
    push_cast at h ⊢; rw [h]
  have := Complex.ofReal_injective h'
  rw [this]; ring

/-- **Jacobi's formula for `r₈`** (Hardy–Wright (20.13.2)). For `n ≥ 1`, the number of
representations of `n` as a sum of eight squares of integers (order and signs counted) is
`16 ∑_{d ∣ n} (-1)^{n+d} d³`. -/
@[kb "hardywright2008" "Section 20.13, p. 434"]
theorem sumSquaresCount_eight_eq {n : ℕ} (hn : 0 < n) :
    (sumSquaresCount 8 n : ℤ) = jacobiEightSum n :=
  sumSquaresCount_eight_eq_of_forall (fun _ hx0 hx1 => theta_pow_eight_real hx0 (by linarith)) hn

end NTKB.HardyWright
