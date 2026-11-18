/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.SixVanish

/-!
# A vanishing criterion for weight-`16` functions invariant under `S` and `T²`

`eq_zero_of_invariant16`: let `G : ℍ → ℂ` be holomorphic with `G ∣₁₆ S = G` and `G ∣₁₆ T² = G`. If
`‖G(τ)‖ ≤ C e^{-6π Im τ}` for `Im τ ≥ 1` and `‖(G ∣₁₆ TS)(τ)‖ ≤ M` for `Im τ ≥ 1`, `|Re τ| ≤ 1`,
then `G = 0`.

This is the argument of `EightModular.lean` and `EightSquares.lean` (for `θ⁸`) at weight `16`:
`G₂ = G ∣ T`, `G₃ = G₂ ∣ S` are permuted with `G` by `S` and `T`, so `N = G G₂ G₃` is invariant of
weight `48` under `SL(2, ℤ)`, `N = O(e^{-16π Im τ})`, and `N / Δ⁴` is a level-one modular form of
weight `0` tending to `0` at `i∞`. Used for `G = (κ θ¹⁰ - L)⁴` in the proof of Liouville's `r₁₀`
formula.
-/

open ModularForm ModularGroup Complex Filter Topology Asymptotics
open scoped MatrixGroups Real UpperHalfPlane Manifold
open UpperHalfPlane hiding I

noncomputable section

namespace NTKB.HardyWright.SixteenSquares

open EightSquares (ne_zero' slash_inv_of_slash_eq T_S_T mdiff_of_eqOn diffOn_comp_ofComplex
  eval_ofComplex tendsto_exp_atImInfty isPreconnected_U analytic_comp eq_zero_of_comp)

section Vanish

variable {G : ℍ → ℂ}

lemma slash_S_S_16 (f : ℍ → ℂ) : f ∣[(16 : ℤ)] (S * S) = f := by
  have hSS : S * S = -1 := Subtype.ext (by simpa using S_mul_S_eq)
  ext τ
  rw [hSS, SL_slash_apply, SL_neg_smul, one_smul]
  simp [denom]
  norm_num

lemma slash_T_apply_16 (f : ℍ → ℂ) (τ : ℍ) : (f ∣[(16 : ℤ)] T) τ = f (T • τ) := by
  rw [SL_slash_apply, ModularGroup.denom_apply]; simp [T]

lemma im_T_smul (τ : ℍ) : (T • τ).im = τ.im := by
  rw [UpperHalfPlane.modular_T_smul]; simp

/-- `N = G (G ∣ T) (G ∣ TS)`. -/
def prodN (G : ℍ → ℂ) : ℍ → ℂ := G * (G ∣[(16 : ℤ)] T) * ((G ∣[(16 : ℤ)] T) ∣[(16 : ℤ)] S)

lemma prodN_slash_S (hS : G ∣[(16 : ℤ)] S = G) : prodN G ∣[(48 : ℤ)] S = prodN G := by
  have h3S : ((G ∣[(16 : ℤ)] T) ∣[(16 : ℤ)] S) ∣[(16 : ℤ)] S = G ∣[(16 : ℤ)] T := by
    rw [← SlashAction.slash_mul (16 : ℤ) S S (G ∣[(16 : ℤ)] T), slash_S_S_16]
  rw [prodN, show (48 : ℤ) = 16 + 16 + 16 by norm_num, mul_slash_SL2, mul_slash_SL2, hS, h3S]
  ring

lemma G3_slash_T (hS : G ∣[(16 : ℤ)] S = G) (hT2 : G ∣[(16 : ℤ)] (T ^ (2 : ℤ)) = G) :
    ((G ∣[(16 : ℤ)] T) ∣[(16 : ℤ)] S) ∣[(16 : ℤ)] T = (G ∣[(16 : ℤ)] T) ∣[(16 : ℤ)] S := by
  have hSi : G ∣[(16 : ℤ)] S⁻¹ = G := slash_inv_of_slash_eq hS
  have hTi : G ∣[(16 : ℤ)] T⁻¹ = G ∣[(16 : ℤ)] T := by
    conv_lhs => rw [← hT2]
    rw [← SlashAction.slash_mul, show T ^ (2 : ℤ) * T⁻¹ = T by group]
  rw [← SlashAction.slash_mul, ← SlashAction.slash_mul, ← mul_assoc, T_S_T,
    SlashAction.slash_mul, SlashAction.slash_mul, hSi, hTi]

lemma prodN_slash_T (hS : G ∣[(16 : ℤ)] S = G) (hT2 : G ∣[(16 : ℤ)] (T ^ (2 : ℤ)) = G) :
    prodN G ∣[(48 : ℤ)] T = prodN G := by
  have h2T : (G ∣[(16 : ℤ)] T) ∣[(16 : ℤ)] T = G := by
    rw [← SlashAction.slash_mul, ← zpow_one T, ← zpow_add]; exact hT2
  rw [prodN, show (48 : ℤ) = 16 + 16 + 16 by norm_num, mul_slash_SL2, mul_slash_SL2, h2T,
    G3_slash_T hS hT2]
  ring

lemma slash_zpow_of_slash_eq {f : ℍ → ℂ} {g : SL(2, ℤ)} (h : f ∣[(16 : ℤ)] g = f) (n : ℤ) :
    f ∣[(16 : ℤ)] (g ^ n) = f := by
  induction n using Int.induction_on with
  | zero => rw [zpow_zero, SlashAction.slash_one]
  | succ n ih => rw [zpow_add_one, SlashAction.slash_mul, ih, h]
  | pred n ih => rw [zpow_sub_one, SlashAction.slash_mul, ih, slash_inv_of_slash_eq h]

lemma slash_T_zpow_apply_16 (f : ℍ → ℂ) (n : ℤ) (τ : ℍ) :
    (f ∣[(16 : ℤ)] (T ^ n)) τ = f (T ^ n • τ) := by
  rw [SL_slash_apply, ModularGroup.denom_apply, coe_T_zpow]; simp

/-- A bound on the strip `|Re τ| ≤ 1` extends to `Im τ ≥ 1` for `T`-invariant functions. -/
lemma bound_of_strip {F : ℍ → ℂ} (hF : F ∣[(16 : ℤ)] T = F) {M : ℝ}
    (h : ∀ τ : ℍ, 1 ≤ τ.im → |τ.re| ≤ 1 → ‖F τ‖ ≤ M) (τ : ℍ) (hτ : 1 ≤ τ.im) : ‖F τ‖ ≤ M := by
  obtain ⟨n, hn⟩ := ModularGroup_T_zpow_mem_verticalStrip τ (N := 1) one_pos
  have e : F τ = F (T ^ (((1 : ℕ) : ℤ) * n) • τ) := by
    rw [← slash_T_zpow_apply_16 F, slash_zpow_of_slash_eq hF]
  rw [e]
  exact h _ (le_trans hτ hn.2) (by simpa using hn.1)

lemma prodN_slash (hS : G ∣[(16 : ℤ)] S = G) (hT2 : G ∣[(16 : ℤ)] (T ^ (2 : ℤ)) = G)
    (γ : SL(2, ℤ)) : prodN G ∣[(48 : ℤ)] γ = prodN G :=
  SlashInvariantForm.slash_action_generators_SL2Z (prodN_slash_S hS) (prodN_slash_T hS hT2) γ

/-- `Δ⁴`. -/
def Delta4 (τ : ℍ) : ℂ := ModularForm.discriminant τ ^ 4

lemma Delta4_ne_zero (τ : ℍ) : Delta4 τ ≠ 0 := pow_ne_zero _ (discriminant_ne_zero τ)

lemma Delta4_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    Delta4 (γ • τ) = ((γ 1 0 : ℂ) * τ + γ 1 1) ^ 48 * Delta4 τ := by
  have hD := congrFun (EightSquares.Delta_slash γ) τ
  rw [slash_action_eq'_iff] at hD
  rw [Delta4, Delta4]
  have hD' : ModularForm.discriminant (γ • τ) =
      ((γ 1 0 : ℂ) * τ + γ 1 1) ^ 12 * ModularForm.discriminant τ := by simpa using hD
  rw [hD']; ring

/-- `N / Δ⁴`. -/
def quotQ (G : ℍ → ℂ) (τ : ℍ) : ℂ := prodN G τ / Delta4 τ

lemma quotQ_slash (hS : G ∣[(16 : ℤ)] S = G) (hT2 : G ∣[(16 : ℤ)] (T ^ (2 : ℤ)) = G)
    (γ : SL(2, ℤ)) : quotQ G ∣[(0 : ℤ)] γ = quotQ G := by
  ext τ
  have hN := congrFun (prodN_slash hS hT2 γ) τ
  rw [slash_action_eq'_iff] at hN
  rw [SL_slash_apply, quotQ, quotQ, Delta4_smul]
  have hN' : prodN G (γ • τ) = ((γ 1 0 : ℂ) * τ + γ 1 1) ^ 48 * prodN G τ := by simpa using hN
  rw [hN']
  have hd : ((γ 1 0 : ℂ) * τ + γ 1 1) ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero γ τ
    simpa [ModularGroup.denom_apply] using this
  have := Delta4_ne_zero τ
  field_simp
  simp

lemma mdiff_prodN (hG : MDiff G) : MDiff (prodN G) := by
  have h2 : MDiff (G ∣[(16 : ℤ)] T) := by rw [SL_slash]; exact hG.slash _ _
  have h3 : MDiff ((G ∣[(16 : ℤ)] T) ∣[(16 : ℤ)] S) := by rw [SL_slash]; exact h2.slash _ _
  exact (hG.mul h2).mul h3

lemma mdiff_Delta4 : MDiff Delta4 := by
  have h : MDiff (⇑CuspForm.discriminant : ℍ → ℂ) := CuspForm.discriminant.holo'
  have : Delta4 = (⇑CuspForm.discriminant : ℍ → ℂ) ^ 4 := by
    funext τ; simp [Delta4, CuspForm.coe_discriminant]
  rw [this]
  exact h.pow 4

lemma mdiff_quotQ (hG : MDiff G) : MDiff (quotQ G) := by
  have hN := diffOn_comp_ofComplex (mdiff_prodN hG)
  have hD := diffOn_comp_ofComplex mdiff_Delta4
  have hdiv : DifferentiableOn ℂ (fun z => (prodN G ∘ ofComplex) z / (Delta4 ∘ ofComplex) z)
      {z : ℂ | 0 < z.im} :=
    hN.div hD fun z _ => Delta4_ne_zero _
  refine mdiff_of_eqOn hdiv fun τ => ?_
  change prodN G τ / Delta4 τ = (prodN G ∘ ofComplex) (τ : ℂ) / (Delta4 ∘ ofComplex) (τ : ℂ)
  rw [eval_ofComplex, eval_ofComplex]

lemma eventually_one_le_im : ∀ᶠ τ : ℍ in atImInfty, 1 ≤ τ.im :=
  (tendsto_comap : Tendsto (fun τ : ℍ => τ.im) atImInfty atTop).eventually
    (eventually_ge_atTop 1)

lemma quotQ_isBigO {C M : ℝ}
    (h1 : ∀ τ : ℍ, 1 ≤ τ.im → ‖G τ‖ ≤ C * rexp (-6 * π * τ.im))
    (h3 : ∀ τ : ℍ, 1 ≤ τ.im → ‖((G ∣[(16 : ℤ)] T) ∣[(16 : ℤ)] S) τ‖ ≤ M) :
    quotQ G =O[atImInfty] fun τ => rexp (-2 * π * τ.im) := by
  obtain ⟨c, hc, hcb⟩ := exp_isBigO_discriminant.exists_pos
  rw [IsBigOWith] at hcb
  have hC : ∀ τ : ℍ, 1 ≤ τ.im → 0 ≤ C := fun τ hτ =>
    nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (h1 τ hτ)) (Real.exp_pos _)
  have hM : ∀ τ : ℍ, 1 ≤ τ.im → 0 ≤ M := fun τ hτ => (norm_nonneg _).trans (h3 τ hτ)
  refine IsBigO.of_bound (C * C * M * c ^ 4) ?_
  filter_upwards [hcb, eventually_one_le_im] with τ hD hτ
  have hC0 := hC τ hτ
  have hM0 := hM τ hτ
  set e := rexp (-2 * π * τ.im) with he
  have hE : 0 < e := Real.exp_pos _
  have he1 : e ≤ 1 := by
    rw [he, Real.exp_le_one_iff]; nlinarith [Real.pi_pos, τ.im_pos]
  have he3 : e ^ 2 ≤ e := by
    calc e ^ 2 = e * e := by ring
      _ ≤ e * 1 := by gcongr
      _ = e := mul_one e
  rw [Real.norm_of_nonneg hE.le] at hD
  have hDpos : 0 < ‖Delta4 τ‖ := norm_pos_iff.mpr (Delta4_ne_zero τ)
  rw [quotQ, norm_div, Real.norm_of_nonneg hE.le, div_le_iff₀ hDpos]
  have hT : 1 ≤ (T • τ).im := by rw [im_T_smul]; exact hτ
  have g1 := h1 τ hτ
  have g2 : ‖(G ∣[(16 : ℤ)] T) τ‖ ≤ C * rexp (-6 * π * τ.im) := by
    rw [slash_T_apply_16]; have := h1 _ hT; rwa [im_T_smul] at this
  have g3 := h3 τ hτ
  have h4 : rexp (-6 * π * τ.im) = e ^ 3 := by
    rw [he, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [h4] at g1 g2
  have hN : ‖prodN G τ‖ ≤ C * e ^ 3 * (C * e ^ 3) * M := by
    simp only [prodN, Pi.mul_apply, norm_mul]
    gcongr
  have hD5 : e ^ 4 ≤ c ^ 4 * ‖Delta4 τ‖ := by
    rw [Delta4, norm_pow, ← mul_pow]
    exact pow_le_pow_left₀ hE.le hD 4
  calc ‖prodN G τ‖ ≤ C * e ^ 3 * (C * e ^ 3) * M := hN
    _ = (C * C * M) * (e ^ 2 * e ^ 4) := by ring
    _ ≤ (C * C * M) * (e * (c ^ 4 * ‖Delta4 τ‖)) := by
        have : 0 ≤ C * C * M := by positivity
        exact mul_le_mul_of_nonneg_left (mul_le_mul he3 hD5 (by positivity) hE.le) this
    _ = _ := by ring

/-- `N / Δ⁴` as a level-one modular form of weight `0`. -/
def quotForm (hG : MDiff G) (hS : G ∣[(16 : ℤ)] S = G) (hT2 : G ∣[(16 : ℤ)] (T ^ (2 : ℤ)) = G)
    {C M : ℝ} (h1 : ∀ τ : ℍ, 1 ≤ τ.im → ‖G τ‖ ≤ C * rexp (-6 * π * τ.im))
    (h3 : ∀ τ : ℍ, 1 ≤ τ.im → ‖((G ∣[(16 : ℤ)] T) ∣[(16 : ℤ)] S) τ‖ ≤ M) :
    ModularForm 𝒮ℒ 0 where
  toFun := quotQ G
  slash_action_eq' γ hγ := by
    obtain ⟨g, rfl⟩ := hγ
    exact quotQ_slash hS hT2 g
  holo' := mdiff_quotQ hG
  bdd_at_cusps' hc := by
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [quotQ_slash hS hT2 γ]
    have hb : (fun τ : ℍ => rexp (-2 * π * τ.im)) =O[atImInfty] (1 : ℍ → ℝ) :=
      IsBigO.of_bound 1 (Eventually.of_forall fun τ => by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]
        simp only [Pi.one_apply, norm_one, one_mul, Real.exp_le_one_iff]
        nlinarith [Real.pi_pos, τ.im_pos])
    exact (quotQ_isBigO h1 h3).trans hb

/-- **Vanishing criterion.** A holomorphic `G : ℍ → ℂ` with `G ∣₁₆ S = G`, `G ∣₁₆ T² = G`,
`‖G(τ)‖ ≤ C e^{-6π Im τ}` for `Im τ ≥ 1` and `‖(G ∣₁₆ TS)(τ)‖ ≤ M` for `Im τ ≥ 1`, `|Re τ| ≤ 1`
is zero (`G ∣₁₆ TS` is `T`-invariant, so the strip suffices). -/
theorem eq_zero_of_invariant16 (hG : MDiff G) (hS : G ∣[(16 : ℤ)] S = G)
    (hT2 : G ∣[(16 : ℤ)] (T ^ (2 : ℤ)) = G) {C M : ℝ}
    (h1 : ∀ τ : ℍ, 1 ≤ τ.im → ‖G τ‖ ≤ C * rexp (-6 * π * τ.im))
    (h3 : ∀ τ : ℍ, 1 ≤ τ.im → |τ.re| ≤ 1 → ‖(G ∣[(16 : ℤ)] (T * S)) τ‖ ≤ M) : G = 0 := by
  have h3' : ∀ τ : ℍ, 1 ≤ τ.im → ‖((G ∣[(16 : ℤ)] T) ∣[(16 : ℤ)] S) τ‖ ≤ M :=
    bound_of_strip (G3_slash_T hS hT2) fun τ hτ hr => by
      rw [← SlashAction.slash_mul]; exact h3 τ hτ hr
  set F := quotForm hG hS hT2 h1 h3'
  obtain ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const F
  have hQ : quotQ G = fun _ => c := by
    have : (⇑F : ℍ → ℂ) = quotQ G := rfl
    rw [← this, hc]; rfl
  have hc0 : c = 0 := by
    have h := (quotQ_isBigO h1 h3').trans_tendsto tendsto_exp_atImInfty
    rw [hQ] at h
    exact tendsto_nhds_unique tendsto_const_nhds h
  have hN : ∀ τ, prodN G τ = 0 := by
    intro τ
    have hq := congrFun hQ τ
    rw [hc0, quotQ, div_eq_zero_iff] at hq
    exact hq.resolve_right (Delta4_ne_zero τ)
  have m2 : MDiff (G ∣[(16 : ℤ)] T) := by rw [SL_slash]; exact hG.slash _ _
  have m3 : MDiff ((G ∣[(16 : ℤ)] T) ∣[(16 : ℤ)] S) := by rw [SL_slash]; exact m2.slash _ _
  have h2T : (G ∣[(16 : ℤ)] T) ∣[(16 : ℤ)] T = G := by
    rw [← SlashAction.slash_mul, ← zpow_one T, ← zpow_add]; exact hT2
  have h3S : ((G ∣[(16 : ℤ)] T) ∣[(16 : ℤ)] S) ∣[(16 : ℤ)] S = G ∣[(16 : ℤ)] T := by
    rw [← SlashAction.slash_mul (16 : ℤ) S S (G ∣[(16 : ℤ)] T), slash_S_S_16]
  have hNz : ∀ z ∈ {z : ℂ | 0 < z.im}, ((G ∘ ofComplex) * ((G ∣[(16 : ℤ)] T) ∘ ofComplex)) z *
      (((G ∣[(16 : ℤ)] T) ∣[(16 : ℤ)] S) ∘ ofComplex) z = 0 := by
    intro z _
    have := hN (ofComplex z)
    simpa [prodN] using this
  rcases AnalyticOnNhd.eq_zero_or_eq_zero_of_mul_eq_zero
      ((analytic_comp hG).mul (analytic_comp m2)) (analytic_comp m3) hNz
      isPreconnected_U with h12 | h33
  · rcases AnalyticOnNhd.eq_zero_or_eq_zero_of_mul_eq_zero (analytic_comp hG)
        (analytic_comp m2) (fun z hz => h12 z hz) isPreconnected_U with h1' | h2'
    · exact eq_zero_of_comp h1'
    · have : G ∣[(16 : ℤ)] T = 0 := eq_zero_of_comp h2'
      rw [← h2T, this, SlashAction.zero_slash]
  · have : (G ∣[(16 : ℤ)] T) ∣[(16 : ℤ)] S = 0 := eq_zero_of_comp h33
    have h2 : G ∣[(16 : ℤ)] T = 0 := by rw [← h3S, this, SlashAction.zero_slash]
    rw [← h2T, h2, SlashAction.zero_slash]

end Vanish

end NTKB.HardyWright.SixteenSquares
