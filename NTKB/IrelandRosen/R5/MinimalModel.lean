/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.IrelandRosen.R5.BadPrimes

/-!
# Minimal models and Mathlib's local polynomial

Two general facts over a discrete valuation ring `R` with fraction field `K`, used for Theorems 7
and 8 of Ireland–Rosen, Chapter 18, at the primes where the given model is not obviously minimal.

* `localPolynomial_smul`: Mathlib's `WeierstrassCurve.localPolynomial` is invariant under a change
  of variables over `K`, for a curve with `Δ ≠ 0` and integral `j`-invariant (`c₄³ = j Δ` with
  `j ∈ R`; then no model has multiplicative reduction). Two minimal models differ by a change of
  variables with `u` a unit and `r, s, t` integral (Mathlib's
  `variableChange_integral_of_u_integral`), so their reductions are isomorphic.
* `localPolynomial_eq_one_of_noSmallerModel`: if `Δ, c₄ ∈ 𝔪` for an integral model `W₀` and no
  change of variables with `u ∈ 𝔪` keeps the model integral (`NoSmallerModel`), the model is minimal,
  the reduction is additive and the local polynomial is `1`. This extends
  `localPolynomial_eq_one_of_additive` (where `v(Δ) < 12` gives minimality) to the cases
  `v(Δ) ≥ 12` that occur at `2` and `3` for `y² = x³ - Dx` and `y² = x³ + D`.

The integrality lemmas `r_integral_of_mem`, `s_integral_of_mem`, `t_integral_of_mem` are
Mathlib's `r_integral_of_u_integral` etc. (David Kurniadi Angdinata and the Mathlib authors,
`Mathlib/AlgebraicGeometry/EllipticCurve/Reduction.lean`) with `u` an element of `R` instead of a
unit: the monic polynomials of the proof only use that `u` is integral.
-/

namespace NTKB.IrelandRosen.CM

open WeierstrassCurve Polynomial IsLocalRing

section DVR

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

open IsDedekindDomain.HeightOneSpectrum
open scoped WithZero

/-! ### Integrality of `r, s, t` for integral `u` -/

section UIntegral

variable {R} {W W' : WeierstrassCurve K} [IsIntegral R W] [IsIntegral R W']
  {CK : VariableChange K} (hCK : CK • W = W') {u : R} (hu : algebraMap R K u = CK.u)

include hCK hu

lemma r_integral_of_mem : ∃ r : R, algebraMap R K r = CK.r := by
  refine IsIntegrallyClosed.isIntegral_iff.mp ⟨X ^ 4 - C (integralModel R W).b₄ * X ^ 2 -
    C (u ^ 6 * (integralModel R W').b₆ + 2 * (integralModel R W).b₆) * X -
    C ((integralModel R W).b₈ - u ^ 8 * (integralModel R W').b₈), by monicity!, ?_⟩
  simp [map_ofNat, hu, ← hCK, integralModel_b₄_eq, integralModel_b₆_eq,
    integralModel_b₈_eq, variableChange_b₆, variableChange_b₈]
  ring1

lemma s_integral_of_mem : ∃ s : R, algebraMap R K s = CK.s := by
  rcases r_integral_of_mem hCK hu with ⟨r, hr⟩
  refine IsIntegrallyClosed.isIntegral_iff.mp ⟨X ^ 2 + C (integralModel R W).a₁ * X +
    C (u ^ 2 * (integralModel R W').a₂ - (integralModel R W).a₂ - 3 * r), by monicity!, ?_⟩
  simp [map_ofNat, hu, hr, ← hCK, integralModel_a₁_eq, integralModel_a₂_eq,
    variableChange_a₂]
  ring1

lemma t_integral_of_mem : ∃ t : R, algebraMap R K t = CK.t := by
  rcases r_integral_of_mem hCK hu with ⟨r, hr⟩
  refine IsIntegrallyClosed.isIntegral_iff.mp ⟨X ^ 2 +
    C ((integralModel R W).a₃ + r * (integralModel R W).a₁) * X +
    C (u ^ 6 * (integralModel R W').a₆ - (integralModel R W).a₆ - r * (integralModel R W).a₄
      - r ^ 2 * (integralModel R W).a₂ - r ^ 3), by monicity!, ?_⟩
  simp [hu, hr, ← hCK, integralModel_a₁_eq, integralModel_a₂_eq, integralModel_a₃_eq,
    integralModel_a₄_eq, integralModel_a₆_eq, variableChange_a₆]
  ring1

end UIntegral

/-! ### Two minimal models -/

/-- Two minimal models related by a change of variables have discriminants of the same valuation. -/
lemma valuation_Δ_eq_of_isMinimal {W₁ W₂ : WeierstrassCurve K} [h₁ : IsMinimal R W₁]
    [h₂ : IsMinimal R W₂] (C : VariableChange K) (hC : C • W₁ = W₂) :
    (IsDiscreteValuationRing.maximalIdeal R).valuation K W₁.Δ =
      (IsDiscreteValuationRing.maximalIdeal R).valuation K W₂.Δ := by
  have hi₂ : IsIntegral R (C • W₁) := hC ▸ inferInstance
  have hback : C⁻¹ • W₂ = W₁ := by rw [← hC, smul_smul, inv_mul_cancel, one_smul]
  have hi₁ : IsIntegral R (C⁻¹ • W₂) := hback ▸ inferInstance
  have e₁ : (valuation_Δ_aux R ((1 : VariableChange K) • W₁) : ℤᵐ⁰) =
      (IsDiscreteValuationRing.maximalIdeal R).valuation K W₁.Δ := by
    rw [one_smul, valuation_Δ_aux_eq_of_isIntegral]
  have e₂ : (valuation_Δ_aux R ((1 : VariableChange K) • W₂) : ℤᵐ⁰) =
      (IsDiscreteValuationRing.maximalIdeal R).valuation K W₂.Δ := by
    rw [one_smul, valuation_Δ_aux_eq_of_isIntegral]
  have e₁₂ : (valuation_Δ_aux R (C • W₁) : ℤᵐ⁰) =
      (IsDiscreteValuationRing.maximalIdeal R).valuation K W₂.Δ := by
    rw [valuation_Δ_aux_eq_of_isIntegral, hC]
  have e₂₁ : (valuation_Δ_aux R (C⁻¹ • W₂) : ℤᵐ⁰) =
      (IsDiscreteValuationRing.maximalIdeal R).valuation K W₁.Δ := by
    rw [valuation_Δ_aux_eq_of_isIntegral, hback]
  rcases le_total ((IsDiscreteValuationRing.maximalIdeal R).valuation K W₁.Δ)
      ((IsDiscreteValuationRing.maximalIdeal R).valuation K W₂.Δ) with h | h
  · refine le_antisymm h ?_
    have := h₁.val_Δ_maximal.2 hi₂ (by rw [← Subtype.coe_le_coe, e₁, e₁₂]; exact h)
    rwa [← Subtype.coe_le_coe, e₁, e₁₂] at this
  · refine le_antisymm ?_ h
    have := h₂.val_Δ_maximal.2 hi₁ (by rw [← Subtype.coe_le_coe, e₂, e₂₁]; exact h)
    rwa [← Subtype.coe_le_coe, e₂, e₂₁] at this

/-- If a change of variables preserves the valuation of `Δ ≠ 0`, then `v(u) = 1`. -/
lemma valuation_u_eq_one {W : WeierstrassCurve K} (hΔ : W.Δ ≠ 0) (C : VariableChange K)
    (h : (IsDiscreteValuationRing.maximalIdeal R).valuation K W.Δ =
      (IsDiscreteValuationRing.maximalIdeal R).valuation K (C • W).Δ) :
    (IsDiscreteValuationRing.maximalIdeal R).valuation K (C.u : K) = 1 := by
  have hv0 : (IsDiscreteValuationRing.maximalIdeal R).valuation K W.Δ ≠ 0 := by
    rwa [Ne, map_eq_zero]
  rw [variableChange_Δ, map_mul, map_pow, Units.val_inv_eq_inv_val, map_inv₀] at h
  have h' : ((IsDiscreteValuationRing.maximalIdeal R).valuation K (C.u : K))⁻¹ ^ 12 = 1 := by
    have := mul_right_cancel₀ hv0 (h.symm.trans (one_mul _).symm)
    exact this
  rw [inv_pow, inv_eq_one] at h'
  rcases pow_eq_one_iff.1 h' with h'' | h''
  · exact h''
  · norm_num at h''

/-- A curve with `c₄³ = j Δ`, `j ∈ R`, `Δ ≠ 0`: no model has multiplicative reduction. -/
lemma not_hasMultiplicativeReduction_of_c₄_pow {W : WeierstrassCurve K} (hΔ : W.Δ ≠ 0) (j : R)
    (hj : W.c₄ ^ 3 = algebraMap R K j * W.Δ) (C : VariableChange K) :
    ¬ HasMultiplicativeReduction R (C • W) := by
  intro h
  have hj' : (C • W).c₄ ^ 3 = algebraMap R K j * (C • W).Δ := by
    rw [variableChange_c₄, variableChange_Δ, mul_pow, hj]
    ring
  have h1 := h.multiplicativeReduction
  have h2 := h.badReduction
  have := congrArg ((IsDiscreteValuationRing.maximalIdeal R).valuation K) hj'
  rw [map_pow, h1, one_pow, map_mul] at this
  have hjle : (IsDiscreteValuationRing.maximalIdeal R).valuation K (algebraMap R K j) ≤ 1 :=
    valuation_le_one _ j
  have : (1 : ℤᵐ⁰) < 1 := by
    calc (1 : ℤᵐ⁰) = _ := this
      _ ≤ 1 * (IsDiscreteValuationRing.maximalIdeal R).valuation K (C • W).Δ :=
          mul_le_mul_left hjle _
      _ < 1 := by rw [one_mul]; exact h2
  exact lt_irrefl _ this

/-- **Invariance of Mathlib's local polynomial under a change of variables**, for a curve with
`Δ ≠ 0` and integral `j`-invariant (`c₄³ = j Δ`, `j ∈ R`) and finite residue field. -/
theorem localPolynomial_smul [Finite (ResidueField R)] (W : WeierstrassCurve K) (hΔ : W.Δ ≠ 0)
    (j : R) (hj : W.c₄ ^ 3 = algebraMap R K j * W.Δ) (C : VariableChange K) :
    (C • W).localPolynomial R = W.localPolynomial R := by
  set C₁ := (W.exists_isMinimal R).choose with hC₁
  set C₂ := ((C • W).exists_isMinimal R).choose with hC₂
  have hm₁ : W.minimal R = C₁ • W := rfl
  have hm₂ : (C • W).minimal R = (C₂ * C) • W := by
    rw [← smul_smul]; rfl
  set W₁ := W.minimal R with hW₁
  set W₂ := (C • W).minimal R with hW₂
  set C' := (C₂ * C) * C₁⁻¹ with hC'
  have hC'W : C' • W₁ = W₂ := by
    rw [hm₁, hm₂, hC', smul_smul, mul_assoc, inv_mul_cancel, mul_one]
  have hv := valuation_Δ_eq_of_isMinimal R C' hC'W
  have hΔ₁ : W₁.Δ ≠ 0 := by
    rw [hm₁, variableChange_Δ]
    exact mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) hΔ
  have hu := valuation_u_eq_one R hΔ₁ C' (by rw [hC'W]; exact hv)
  obtain ⟨u, hu'⟩ := exists_unit_of_valuation_eq_one R hu
  obtain ⟨CR, hCR⟩ := variableChange_integral_of_u_integral (W := W₁) (W' := W₂) hC'W hu'
  have hint : integralModel R W₂ = CR • integralModel R W₁ := by
    have hinj := IsFractionRing.injective R K
    have hmap : (CR • integralModel R W₁).map (algebraMap R K) = W₂ := by
      rw [← map_variableChange]
      have h1 : (integralModel R W₁).map (algebraMap R K) = W₁ := baseChange_integralModel_eq R W₁
      rw [h1, ← hC'W, ← hCR]
      rfl
    ext
    · exact hinj ((integralModel_a₁_eq R W₂).trans (congrArg (·.a₁) hmap).symm)
    · exact hinj ((integralModel_a₂_eq R W₂).trans (congrArg (·.a₂) hmap).symm)
    · exact hinj ((integralModel_a₃_eq R W₂).trans (congrArg (·.a₃) hmap).symm)
    · exact hinj ((integralModel_a₄_eq R W₂).trans (congrArg (·.a₄) hmap).symm)
    · exact hinj ((integralModel_a₆_eq R W₂).trans (congrArg (·.a₆) hmap).symm)
  have hred : W₂.reduction R = (CR.map (residue R)) • W₁.reduction R := by
    rw [reduction, reduction, hint, map_variableChange]
  have hgood : HasGoodReduction R W₂ ↔ HasGoodReduction R W₁ := by
    rw [hasGoodReduction_iff, hasGoodReduction_iff, hv]
    exact ⟨fun h => ⟨inferInstance, h.2⟩, fun h => ⟨inferInstance, h.2⟩⟩
  have hnm₁ : ¬ HasMultiplicativeReduction R W₁ := by
    rw [hm₁]; exact not_hasMultiplicativeReduction_of_c₄_pow R hΔ j hj C₁
  have hnm₂ : ¬ HasMultiplicativeReduction R W₂ := by
    rw [hm₂]; exact not_hasMultiplicativeReduction_of_c₄_pow R hΔ j hj _
  have hns₁ : ¬ HasSplitMultiplicativeReduction R W₁ :=
    fun h => hnm₁ h.toHasMultiplicativeReduction
  have hns₂ : ¬ HasSplitMultiplicativeReduction R W₂ :=
    fun h => hnm₂ h.toHasMultiplicativeReduction
  by_cases hg₁ : HasGoodReduction R W₁
  · have hg₂ : HasGoodReduction R W₂ := hgood.2 hg₁
    have hΔr₁ : (W₁.reduction R).Δ ≠ 0 :=
      ((W₁.reduction R).isElliptic_iff.1 ((hasGoodReduction_iff_isElliptic_reduction R).1 hg₁)).ne_zero
    have hΔr₂ : (W₂.reduction R).Δ ≠ 0 :=
      ((W₂.reduction R).isElliptic_iff.1 ((hasGoodReduction_iff_isElliptic_reduction R).1 hg₂)).ne_zero
    have hcard : Nat.card (W₂.reduction R).toAffine.Point =
        Nat.card (W₁.reduction R).toAffine.Point := by
      rw [card_point_eq _ hΔr₂, card_point_eq _ hΔr₁, hred, card_equation_variableChange]
    unfold localPolynomial
    rw [ite_cond_eq_true _ _ (eq_true (show HasGoodReduction R ((C • W).minimal R) from hg₂)),
      ite_cond_eq_true _ _ (eq_true (show HasGoodReduction R (W.minimal R) from hg₁))]
    rw [hcard]
  · have hg₂ : ¬ HasGoodReduction R W₂ := fun h => hg₁ (hgood.1 h)
    unfold localPolynomial
    rw [ite_cond_eq_false _ _ (eq_false (show ¬ HasGoodReduction R ((C • W).minimal R) from hg₂)),
      ite_cond_eq_false _ _ (eq_false (show ¬ HasGoodReduction R (W.minimal R) from hg₁)),
      ite_cond_eq_false _ _
        (eq_false (show ¬ HasSplitMultiplicativeReduction R ((C • W).minimal R) from hns₂)),
      ite_cond_eq_false _ _
        (eq_false (show ¬ HasSplitMultiplicativeReduction R (W.minimal R) from hns₁)),
      ite_cond_eq_false _ _
        (eq_false (show ¬ HasMultiplicativeReduction R ((C • W).minimal R) from hnm₂)),
      ite_cond_eq_false _ _ (eq_false (show ¬ HasMultiplicativeReduction R (W.minimal R) from hnm₁))]

/-! ### Additive reduction without the bound `v(Δ) < 12` -/

/-- No change of variables `(u, r, s, t)` with `u ∈ 𝔪`, `u ≠ 0`, `r, s, t ∈ R` turns the integral
model `W₀` into an integral model (the five coefficients of `(u, r, s, t) • W₀`, multiplied by
`u, u², u³, u⁴, u⁶`, are the expressions below). -/
def NoSmallerModel (W₀ : WeierstrassCurve R) : Prop :=
  ∀ u r s t : R, u ∈ maximalIdeal R → u ≠ 0 →
    u ∣ W₀.a₁ + 2 * s →
    u ^ 2 ∣ W₀.a₂ - s * W₀.a₁ + 3 * r - s ^ 2 →
    u ^ 3 ∣ W₀.a₃ + r * W₀.a₁ + 2 * t →
    u ^ 4 ∣ W₀.a₄ - s * W₀.a₃ + 2 * r * W₀.a₂ - (t + r * s) * W₀.a₁ + 3 * r ^ 2 - 2 * s * t →
    u ^ 6 ∣ W₀.a₆ + r * W₀.a₄ + r ^ 2 * W₀.a₂ + r ^ 3 - t * W₀.a₃ - t ^ 2 - r * t * W₀.a₁ →
    False

/-- **Additive reduction from minimality by hand.** If `Δ ≠ 0`, `Δ, c₄ ∈ 𝔪` and no smaller
integral model exists (`NoSmallerModel`), the local polynomial is `1`. -/
theorem localPolynomial_eq_one_of_noSmallerModel (W₀ : WeierstrassCurve R) (hΔ0 : W₀.Δ ≠ 0)
    (hΔ : W₀.Δ ∈ maximalIdeal R) (hc : W₀.c₄ ∈ maximalIdeal R) (hns : NoSmallerModel R W₀) :
    (W₀.map (algebraMap R K)).localPolynomial R = 1 := by
  set W := W₀.map (algebraMap R K) with hWdef
  let hWi : IsIntegral R W := isIntegral_map R W₀
  set v := IsDiscreteValuationRing.maximalIdeal R
  have hinj := IsFractionRing.injective R K
  have hvΔ : v.valuation K W.Δ < 1 := by
    rw [hWdef, map_Δ]; exact (valuation_lt_one_iff_mem v _).2 hΔ
  have hvc : v.valuation K W.c₄ < 1 := by
    rw [hWdef, map_c₄]; exact (valuation_lt_one_iff_mem v _).2 hc
  have hWΔ0 : W.Δ ≠ 0 := by
    rw [hWdef, map_Δ, Ne, map_eq_zero_iff _ hinj]; exact hΔ0
  have hvΔ0 : v.valuation K W.Δ ≠ 0 := by rwa [Ne, map_eq_zero]
  set C0 := (W.exists_isMinimal R).choose with hC0
  have hspec : IsMinimal R (C0 • W) := (W.exists_isMinimal R).choose_spec
  set W' := C0 • W with hW'
  have hmin : W.minimal R = W' := rfl
  have hΔ' : v.valuation K W'.Δ = (v.valuation K (C0.u : K))⁻¹ ^ 12 * v.valuation K W.Δ := by
    rw [hW', variableChange_Δ, map_mul, map_pow, Units.val_inv_eq_inv_val, map_inv₀]
  -- maximality: `val(Δ) ≤ val(Δ')`
  have hle : v.valuation K W.Δ ≤ v.valuation K W'.Δ := by
    have hmax := hspec.val_Δ_maximal
    have hback : C0⁻¹ • W' = W := by rw [hW', smul_smul, inv_mul_cancel, one_smul]
    have hP : IsIntegral R (C0⁻¹ • W') := hback ▸ hWi
    have hfj : (valuation_Δ_aux R (C0⁻¹ • W') : ℤᵐ⁰) = v.valuation K W.Δ := by
      have := @valuation_Δ_aux_eq_of_isIntegral R _ _ _ K _ _ _ (C0⁻¹ • W') hP
      rw [this, hback]
    let _ : IsIntegral R W' := inferInstance
    by_contra hlt
    push Not at hlt
    have h1 : valuation_Δ_aux R ((1 : VariableChange K) • W') ≤ valuation_Δ_aux R (C0⁻¹ • W') := by
      rw [← Subtype.coe_le_coe, hfj, one_smul, valuation_Δ_aux_eq_of_isIntegral]
      exact hlt.le
    have h2 := hmax.2 hP h1
    rw [← Subtype.coe_le_coe, hfj] at h2
    simp only [one_smul] at h2
    rw [valuation_Δ_aux_eq_of_isIntegral] at h2
    exact absurd h2 (not_le.mpr hlt)
  set t := v.valuation K (C0.u : K) with ht
  have ht_le : t ≤ 1 := by
    rw [hΔ'] at hle
    have : 1 * v.valuation K W.Δ ≤ t⁻¹ ^ 12 * v.valuation K W.Δ := by rwa [one_mul]
    have h1 : (1 : ℤᵐ⁰) ≤ t⁻¹ ^ 12 := le_of_mul_le_mul_right this (zero_lt_iff.2 hvΔ0)
    by_contra h
    push Not at h
    have : t⁻¹ < 1 := inv_lt_one_of_one_lt₀ h
    have : t⁻¹ ^ 12 < 1 := pow_lt_one₀ zero_le this (by norm_num)
    exact absurd h1 (not_le.mpr this)
  have ht1 : t = 1 := by
    refine le_antisymm ht_le ?_
    by_contra h
    push Not at h
    -- a smaller integral model: contradiction with `hns`
    obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_lift_of_le_one (A := R) ht_le
    have ham : a ∈ maximalIdeal R := by
      have : v.valuation K (algebraMap R K a) < 1 := by rw [ha]; exact h
      exact (valuation_lt_one_iff_mem v a).1 this
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at ha
      exact C0.u.ne_zero ha.symm
    have : IsIntegral R W' := inferInstance
    have hCW : C0 • W = W' := rfl
    obtain ⟨r, hr⟩ := r_integral_of_mem hCW ha
    obtain ⟨s, hs⟩ := s_integral_of_mem hCW ha
    obtain ⟨tt, htt⟩ := t_integral_of_mem hCW ha
    have hI : integralModel R W = W₀ := integralModel_map R W₀
    have hua : (C0.u : K) ≠ 0 := C0.u.ne_zero
    set I := integralModel R W' with hI'
    have e1 : algebraMap R K I.a₁ = (C0 • W).a₁ := integralModel_a₁_eq R W'
    have e2 : algebraMap R K I.a₂ = (C0 • W).a₂ := integralModel_a₂_eq R W'
    have e3 : algebraMap R K I.a₃ = (C0 • W).a₃ := integralModel_a₃_eq R W'
    have e4 : algebraMap R K I.a₄ = (C0 • W).a₄ := integralModel_a₄_eq R W'
    have e6 : algebraMap R K I.a₆ = (C0 • W).a₆ := integralModel_a₆_eq R W'
    rw [variableChange_a₁, Units.val_inv_eq_inv_val] at e1
    rw [variableChange_a₂, Units.val_inv_eq_inv_val] at e2
    rw [variableChange_a₃, Units.val_inv_eq_inv_val] at e3
    rw [variableChange_a₄, Units.val_inv_eq_inv_val] at e4
    rw [variableChange_a₆, Units.val_inv_eq_inv_val] at e6
    simp only [hWdef, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at e1 e2 e3 e4 e6
    refine hns a r s tt ham ha0 ⟨I.a₁, hinj ?_⟩ ⟨I.a₂, hinj ?_⟩ ⟨I.a₃, hinj ?_⟩ ⟨I.a₄, hinj ?_⟩
      ⟨I.a₆, hinj ?_⟩
    · simp only [map_add, map_mul, map_ofNat, hs, ha, e1]; field_simp
    · simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, hs, hr, ha, e2]; field_simp
    · simp only [map_add, map_mul, map_pow, map_ofNat, hr, htt, ha, e3]; field_simp
    · simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, hr, hs, htt, ha, e4]; field_simp
    · simp only [map_add, map_sub, map_mul, map_pow, hr, htt, ha, e6]; field_simp
  have ht1' : v.valuation K (C0.u : K) = 1 := ht1
  have hvΔ' : v.valuation K W'.Δ < 1 := by
    rw [hΔ', ht1, inv_one, one_pow, one_mul]; exact hvΔ
  have hvc' : v.valuation K W'.c₄ < 1 := by
    rw [hW', variableChange_c₄, map_mul, map_pow, Units.val_inv_eq_inv_val, map_inv₀, ht1',
      inv_one, one_pow, one_mul]
    exact hvc
  haveI hadd : HasAdditiveReduction R W' :=
    { hspec with badReduction := hvΔ', additiveReduction := hvc' }
  have hng : ¬ HasGoodReduction R (W.minimal R) := hadd.not_hasGoodReduction
  have hnm : ¬ HasMultiplicativeReduction R (W.minimal R) := hadd.not_hasMultiplicativeReduction
  have hns' : ¬ HasSplitMultiplicativeReduction R (W.minimal R) :=
    fun h => hnm h.toHasMultiplicativeReduction
  unfold localPolynomial
  rw [if_neg hng, if_neg hns', if_neg hnm]

end DVR

end NTKB.IrelandRosen.CM
