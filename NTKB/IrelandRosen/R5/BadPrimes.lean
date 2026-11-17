/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.IrelandRosen.R5.LocalPolynomial

/-!
# The local polynomial at a prime of additive reduction

Mathlib's `WeierstrassCurve.localPolynomial R W` is `1` when the minimal model has additive
reduction. We show (`localPolynomial_eq_one_of_additive`) that this is the case for a curve coming
from an integral model `W₀` over the discrete valuation ring `R` with `Δ` and `c₄` in the maximal
ideal and `Δ` not divisible by the `12`-th power of an element of the maximal ideal: then `W₀` is
already minimal (a change of variables multiplies `Δ` by `u⁻¹²`), and its reduction is additive.

At a finite place `v` of `ℚ` above `p` (`localPolynomial_rat_eq_one`): for a curve with integer
coefficients with `p ∣ Δ`, `p ∣ c₄` and `p¹² ∤ Δ` the local polynomial is `1`.
-/

namespace NTKB.IrelandRosen.CM

open WeierstrassCurve Polynomial IsLocalRing

section DVR

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

open IsDedekindDomain.HeightOneSpectrum
open scoped WithZero

/-- **Additive reduction.** If `Δ, c₄ ∈ 𝔪` and no `a ∈ 𝔪` has `a¹² ∣ Δ`, the local polynomial is `1`. -/
theorem localPolynomial_eq_one_of_additive (W₀ : WeierstrassCurve R)
    (hΔ : W₀.Δ ∈ maximalIdeal R) (hc : W₀.c₄ ∈ maximalIdeal R)
    (h12 : ∀ a ∈ maximalIdeal R, ¬ a ^ 12 ∣ W₀.Δ) :
    (W₀.map (algebraMap R K)).localPolynomial R = 1 := by
  set W := W₀.map (algebraMap R K) with hWdef
  let hWi : IsIntegral R W := isIntegral_map R W₀
  set v := IsDiscreteValuationRing.maximalIdeal R
  have hΔ0 : W₀.Δ ≠ 0 := by
    intro h; exact h12 0 (Ideal.zero_mem _) (by rw [h]; exact dvd_zero _)
  have hvΔ : v.valuation K W.Δ < 1 := by
    rw [hWdef, map_Δ]; exact (valuation_lt_one_iff_mem v _).2 hΔ
  have hvc : v.valuation K W.c₄ < 1 := by
    rw [hWdef, map_c₄]; exact (valuation_lt_one_iff_mem v _).2 hc
  have hvΔ0 : v.valuation K W.Δ ≠ 0 := by
    rw [hWdef, map_Δ, Ne, map_eq_zero]
    exact fun h => hΔ0 (IsFractionRing.injective R K (by rw [h, map_zero]))
  set C0 := (W.exists_isMinimal R).choose with hC0
  have hspec : IsMinimal R (C0 • W) := (W.exists_isMinimal R).choose_spec
  set W' := C0 • W with hW'
  have hmin : W.minimal R = W' := rfl
  -- `val(Δ') = val(u)⁻¹² val(Δ)`
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
  -- integrality of `Δ'`
  have hΔ'1 : v.valuation K W'.Δ ≤ 1 := by
    letI : IsIntegral R W' := inferInstance
    obtain ⟨r, hr⟩ := Δ_integral_of_isIntegral R W'
    rw [← hr]; exact valuation_le_one _ r
  -- hence `val(u) = 1`
  set t := v.valuation K (C0.u : K) with ht
  have ht0 : t ≠ 0 := by rw [ht, Ne, map_eq_zero]; exact C0.u.ne_zero
  have ht_le : t ≤ 1 := by
    rw [hΔ'] at hle
    have : 1 * v.valuation K W.Δ ≤ t⁻¹ ^ 12 * v.valuation K W.Δ := by rwa [one_mul]
    have h1 : (1 : ℤᵐ⁰) ≤ t⁻¹ ^ 12 := le_of_mul_le_mul_right this (zero_lt_iff.2 hvΔ0)
    by_contra h
    push Not at h
    have : t⁻¹ < 1 := inv_lt_one_of_one_lt₀ h
    have : t⁻¹ ^ 12 < 1 := pow_lt_one₀ zero_le' this (by norm_num)
    exact absurd h1 (not_le.mpr this)
  have ht1 : t = 1 := by
    refine le_antisymm ht_le ?_
    by_contra h
    push Not at h
    -- `u ∈ 𝔪` and `u¹² ∣ Δ`
    obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_lift_of_le_one (A := R) ht_le
    have ham : a ∈ maximalIdeal R := by
      have : v.valuation K (algebraMap R K a) < 1 := by rw [ha]; exact h
      exact (valuation_lt_one_iff_mem v a).1 this
    have hq : v.valuation K (W.Δ / (C0.u : K) ^ 12) ≤ 1 := by
      rw [map_div₀, map_pow]
      rw [hΔ'] at hΔ'1
      rwa [inv_pow, inv_mul_eq_div] at hΔ'1
    obtain ⟨b, hb⟩ := IsDiscreteValuationRing.exists_lift_of_le_one (A := R) hq
    apply h12 a ham
    refine ⟨b, IsFractionRing.injective R K ?_⟩
    rw [map_mul, map_pow, ha, hb, ← map_Δ]
    have hu : (C0.u : K) ^ 12 ≠ 0 := pow_ne_zero _ C0.u.ne_zero
    field_simp
    rfl
  -- the minimal model has additive reduction
  have ht1' : v.valuation K (C0.u : K) = 1 := ht1
  have hvΔ' : v.valuation K W'.Δ < 1 := by
    rw [hΔ', ht1, inv_one, one_pow, one_mul]; exact hvΔ
  have hvc' : v.valuation K W'.c₄ < 1 := by
    rw [hW', variableChange_c₄, map_mul, map_pow, Units.val_inv_eq_inv_val, map_inv₀, ht1',
      inv_one, one_pow, one_mul]
    exact hvc
  haveI hadd : HasAdditiveReduction R W' := { hspec with badReduction := hvΔ', additiveReduction := hvc' }
  have hng : ¬ HasGoodReduction R (W.minimal R) := hadd.not_hasGoodReduction
  have hnm : ¬ HasMultiplicativeReduction R (W.minimal R) := hadd.not_hasMultiplicativeReduction
  have hns : ¬ HasSplitMultiplicativeReduction R (W.minimal R) := fun h => hnm h.toHasMultiplicativeReduction
  unfold localPolynomial
  rw [if_neg hng, if_neg hns, if_neg hnm]

end DVR

/-! ### The finite places of `ℚ` -/

section Rat

open IsDedekindDomain NumberField Rat.HeightOneSpectrum

variable (v : HeightOneSpectrum (𝓞 ℚ))

lemma algebraMap_mem_maximalIdeal_iff (n : ℤ) :
    algebraMap ℤ (v.adicCompletionIntegers ℚ) n ∈ maximalIdeal (v.adicCompletionIntegers ℚ) ↔
      (placePrime v : ℤ) ∣ n := by
  rw [← residue_eq_zero_iff]
  constructor
  · intro h
    have h' := congrArg (residueFieldEquiv v) h
    rw [map_zero] at h'
    have h'' : (residueFieldEquiv v : _ →+* ZMod (placePrime v)).comp
        ((residue _).comp (algebraMap ℤ (v.adicCompletionIntegers ℚ))) n = 0 := h'
    rwa [residueFieldEquiv_comp, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] at h''
  · intro h
    apply (residueFieldEquiv v).injective
    rw [map_zero]
    have : (residueFieldEquiv v : _ →+* ZMod (placePrime v)).comp
        ((residue _).comp (algebraMap ℤ (v.adicCompletionIntegers ℚ))) n = 0 := by
      rw [residueFieldEquiv_comp, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact h
    exact this

lemma dvd_of_pow_dvd_algebraMap {n : ℤ} {k : ℕ} {a : v.adicCompletionIntegers ℚ}
    (ha : a ∈ maximalIdeal (v.adicCompletionIntegers ℚ))
    (hd : a ^ k ∣ algebraMap ℤ (v.adicCompletionIntegers ℚ) n) :
    ((placePrime v : ℤ) ^ k) ∣ n := by
  let p := placePrime v
  let e := adicCompletionIntegers.padicIntEquiv v
  have he : ∀ m : ℤ, e (algebraMap ℤ _ m) = (m : ℤ_[p]) := fun m => by
    rw [algebraMap_int_eq, eq_intCast, map_intCast]
  have hea : e a ∈ maximalIdeal ℤ_[p] := by
    rw [mem_maximalIdeal, mem_nonunits_iff] at ha ⊢
    intro h
    apply ha
    have := h.map (adicCompletionIntegers.padicIntEquiv v).symm
    simpa using this
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hea
  obtain ⟨b, hb⟩ := hea
  have hd' : (e a) ^ k ∣ (n : ℤ_[p]) := by
    rw [← he, ← map_pow]; exact map_dvd e hd
  rw [hb, mul_pow] at hd'
  obtain ⟨c, hc⟩ := hd'
  have hnorm : ‖(n : ℤ_[p])‖ ≤ (p : ℝ) ^ (-(k : ℕ) : ℤ) := by
    rw [hc, norm_mul, norm_mul, norm_pow, PadicInt.norm_p, zpow_neg, zpow_natCast, inv_pow]
    have h1 : ‖b ^ k‖ ≤ 1 := PadicInt.norm_le_one _
    have h2 : ‖c‖ ≤ 1 := PadicInt.norm_le_one _
    have h3 : (0 : ℝ) ≤ ((p : ℝ) ^ k)⁻¹ := by positivity
    calc ((p : ℝ) ^ k)⁻¹ * ‖b ^ k‖ * ‖c‖ ≤ ((p : ℝ) ^ k)⁻¹ * 1 * 1 := by gcongr
      _ = ((p : ℝ) ^ k)⁻¹ := by ring
  have := PadicInt.norm_int_le_pow_iff_dvd.1 hnorm
  exact_mod_cast this

/-- **The local polynomial at a place of additive reduction.** For a Weierstrass curve with integer
coefficients with `p ∣ Δ`, `p ∣ c₄` and `p¹² ∤ Δ`, Mathlib's local polynomial at the place `v` above
`p` is `1`. -/
theorem localPolynomial_rat_eq_one (W : WeierstrassCurve ℤ) (hΔ : (placePrime v : ℤ) ∣ W.Δ)
    (hc : (placePrime v : ℤ) ∣ W.c₄) (h12 : ¬ (placePrime v : ℤ) ^ 12 ∣ W.Δ) :
    ((W.baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ) = 1 := by
  set Rv := v.adicCompletionIntegers ℚ
  set W₀ := W.map (algebraMap ℤ Rv) with hW₀
  have h1 : (W.baseChange ℚ).baseChange (v.adicCompletion ℚ) =
      W₀.map (algebraMap Rv (v.adicCompletion ℚ)) := by
    rw [baseChange, baseChange, WeierstrassCurve.map_map, hW₀, WeierstrassCurve.map_map]
    exact congrArg W.map (Subsingleton.elim _ _)
  rw [h1]
  refine localPolynomial_eq_one_of_additive Rv W₀ ?_ ?_ ?_
  · rw [hW₀, map_Δ]; exact (algebraMap_mem_maximalIdeal_iff v _).2 hΔ
  · rw [hW₀, map_c₄]; exact (algebraMap_mem_maximalIdeal_iff v _).2 hc
  · intro a ha hd
    rw [hW₀, map_Δ] at hd
    exact h12 (dvd_of_pow_dvd_algebraMap v ha hd)

end Rat

end NTKB.IrelandRosen.CM
