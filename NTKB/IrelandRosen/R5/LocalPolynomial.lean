/-
Ireland–Rosen, Chapter 18, §5 (setting): the local factor of Mathlib's L-function of a Weierstrass
curve at a prime of good reduction, in terms of the point count of the reduction.
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.RingHoms
import NTKB.Attr

/-!
# The local polynomial at a prime of good reduction

Mathlib's `WeierstrassCurve.localPolynomial R W` is defined through a minimal model chosen by
choice. We show that it is the expected polynomial whenever `W` comes from a Weierstrass curve `W₀`
over the discrete valuation ring `R` with unit discriminant:

* `card_point_eq`: over a finite field, `#W(F) = 1 + #{(x, y) : W(x, y) = 0}` when `Δ ≠ 0`;
* `card_equation_variableChange`: the affine point count is invariant under a change of variables;
* `localPolynomial_of_isUnit_Δ`: `localPolynomial R (W₀.map (algebraMap R K)) = 1 - a X + q X²` with
  `q = #κ` and `a = q - #{(x, y) ∈ κ² : W̄₀(x, y) = 0}`;
* `localPolynomial_rat_of_isUnit`: the same at a finite place `v` of `ℚ` above the prime `p`, for a
  curve with integer coefficients and `p ∤ Δ`, with the point count over `ZMod p`.
-/

namespace NTKB.IrelandRosen.CM

open WeierstrassCurve Polynomial IsLocalRing

/-! ### Point counts over a field -/

section Field

variable {F : Type*} [Field F]

/-- The affine solutions of the Weierstrass equation, as a type. -/
abbrev AffineSolutions (W : WeierstrassCurve F) : Type _ :=
  {xy : F × F // W.toAffine.Equation xy.1 xy.2}

/-- The points of a Weierstrass curve with nonzero discriminant: the point at infinity and the
affine solutions. -/
noncomputable def pointEquivOption (W : WeierstrassCurve F) (hΔ : W.Δ ≠ 0) :
    W.toAffine.Point ≃ Option (AffineSolutions W) where
  toFun
    | .zero => none
    | .some x y h => some ⟨(x, y), h.1⟩
  invFun
    | none => .zero
    | some xy => .some xy.1.1 xy.1.2
        ((W.toAffine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).1 xy.2)
  left_inv P := by cases P <;> rfl
  right_inv o := by rcases o with _ | ⟨⟨x, y⟩, h⟩ <;> rfl

lemma card_point_eq [Finite F] (W : WeierstrassCurve F) (hΔ : W.Δ ≠ 0) :
    Nat.card W.toAffine.Point = Nat.card (AffineSolutions W) + 1 := by
  rw [Nat.card_congr (pointEquivOption W hΔ), Finite.card_option]

/-- The Weierstrass polynomial after a change of variables. -/
lemma equation_variableChange_iff (W : WeierstrassCurve F) (C : VariableChange F) (x y : F) :
    (C • W).toAffine.Equation x y ↔
      W.toAffine.Equation (C.u ^ 2 * x + C.r) (C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t) := by
  rw [Affine.equation_iff', Affine.equation_iff']
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  have h6 : (C.u : F) ^ 6 ≠ 0 := pow_ne_zero _ hu
  have key : (C.u : F) ^ 6 * (y ^ 2 + (C • W).a₁ * x * y +
      (C • W).a₃ * y - (x ^ 3 + (C • W).a₂ * x ^ 2 + (C • W).a₄ * x + (C • W).a₆)) =
      (C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t) ^ 2 +
        W.a₁ * (C.u ^ 2 * x + C.r) * (C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t) +
        W.a₃ * (C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t) -
        ((C.u ^ 2 * x + C.r) ^ 3 + W.a₂ * (C.u ^ 2 * x + C.r) ^ 2 +
          W.a₄ * (C.u ^ 2 * x + C.r) + W.a₆) := by
    simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
      variableChange_a₆, Units.val_inv_eq_inv_val]
    field_simp
    ring
  rw [← key, mul_eq_zero, or_iff_right h6]

/-- The affine change of coordinates `(x, y) ↦ (u²x + r, u³y + u²sx + t)`. -/
noncomputable def variableChangeEquiv (C : VariableChange F) : F × F ≃ F × F where
  toFun xy := (C.u ^ 2 * xy.1 + C.r, C.u ^ 3 * xy.2 + C.u ^ 2 * C.s * xy.1 + C.t)
  invFun XY := ((XY.1 - C.r) / C.u ^ 2,
    (XY.2 - C.t - C.s * (XY.1 - C.r)) / C.u ^ 3)
  left_inv xy := by
    have hu : (C.u : F) ≠ 0 := C.u.ne_zero
    ext <;> simp <;> field_simp <;> ring
  right_inv XY := by
    have hu : (C.u : F) ≠ 0 := C.u.ne_zero
    ext <;> simp <;> field_simp <;> ring

lemma card_equation_variableChange (W : WeierstrassCurve F) (C : VariableChange F) :
    Nat.card (AffineSolutions (C • W)) = Nat.card (AffineSolutions W) :=
  Nat.card_congr <| (variableChangeEquiv C).subtypeEquiv fun xy =>
    equation_variableChange_iff W C xy.1 xy.2

/-- Point counts are preserved by ring isomorphisms of the base field. -/
lemma card_equation_map {F' : Type*} [Field F'] (W : WeierstrassCurve F) (σ : F ≃+* F') :
    Nat.card (AffineSolutions (W.map (σ : F →+* F'))) = Nat.card (AffineSolutions W) := by
  refine (Nat.card_congr <| (Equiv.prodCongr σ.toEquiv σ.toEquiv).subtypeEquiv fun xy => ?_).symm
  simp only [Affine.equation_iff, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, Equiv.prodCongr_apply,
    Prod.map_fst, Prod.map_snd, RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe, RingEquiv.coe_toRingHom]
  simp only [← map_pow, ← map_mul, ← map_add]
  exact σ.injective.eq_iff.symm

end Field

/-! ### Discrete valuation rings -/

section DVR

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

open IsDedekindDomain.HeightOneSpectrum
open scoped WithZero

omit [IsDomain R] [IsDiscreteValuationRing R] in
lemma isIntegral_map (W₀ : WeierstrassCurve R) : IsIntegral R (W₀.map (algebraMap R K)) :=
  isIntegral_of_exists_lift R ⟨W₀.a₁, rfl⟩ ⟨W₀.a₂, rfl⟩ ⟨W₀.a₃, rfl⟩ ⟨W₀.a₄, rfl⟩ ⟨W₀.a₆, rfl⟩

lemma integralModel_map (W₀ : WeierstrassCurve R) :
    letI := isIntegral_map R (K := K) W₀
    integralModel R (W₀.map (algebraMap R K)) = W₀ := by
  letI := isIntegral_map R (K := K) W₀
  have hinj := IsFractionRing.injective R K
  ext
  · exact hinj (integralModel_a₁_eq R _)
  · exact hinj (integralModel_a₂_eq R _)
  · exact hinj (integralModel_a₃_eq R _)
  · exact hinj (integralModel_a₄_eq R _)
  · exact hinj (integralModel_a₆_eq R _)

lemma valuation_algebraMap_eq_one {r : R} (hr : IsUnit r) :
    (IsDiscreteValuationRing.maximalIdeal R).valuation K (algebraMap R K r) = 1 :=
  (valuation_eq_one_iff_notMem _).2 fun h => (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    (Ideal.eq_top_of_isUnit_mem _ h hr)

/-- If the valuation of `x` and of `x⁻¹` are at most one, `x` comes from a unit of `R`. -/
lemma exists_unit_of_valuation_eq_one {x : K}
    (hx : (IsDiscreteValuationRing.maximalIdeal R).valuation K x = 1) :
    ∃ a : Rˣ, algebraMap R K a = x := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_lift_of_le_one (A := R) hx.le
  obtain ⟨b, hb⟩ := IsDiscreteValuationRing.exists_lift_of_le_one (A := R) (x := x⁻¹)
    (by rw [map_inv₀, hx, inv_one])
  have hab : a * b = 1 := IsFractionRing.injective R K (by
    rw [map_mul, ha, hb, mul_inv_cancel₀ hx0, map_one])
  exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha⟩

/-- The local polynomial of a curve with good reduction, from an integral model with unit
discriminant: `1 - a X + q X²`, `q = #κ`, `a = q - #{(x, y) ∈ κ² : W̄₀(x, y) = 0}`. -/
theorem localPolynomial_of_isUnit_Δ [Finite (ResidueField R)] (W₀ : WeierstrassCurve R) (hΔ : IsUnit W₀.Δ) :
    (W₀.map (algebraMap R K)).localPolynomial R =
      1 - C ((Nat.card (ResidueField R) : ℤ) -
          Nat.card (AffineSolutions (W₀.map (residue R)))) * X +
        C (Nat.card (ResidueField R) : ℤ) * X ^ 2 := by
  set W := W₀.map (algebraMap R K) with hWdef
  letI hWi : IsIntegral R W := isIntegral_map R W₀
  set v := IsDiscreteValuationRing.maximalIdeal R
  have hW1 : v.valuation K W.Δ = 1 := by
    rw [hWdef, map_Δ]; exact valuation_algebraMap_eq_one R hΔ
  obtain ⟨Cm, hCm⟩ := W.exists_isMinimal R
  have hmin : W.minimal R = (W.exists_isMinimal R).choose • W := rfl
  set C0 := (W.exists_isMinimal R).choose with hC0
  have hspec : IsMinimal R (C0 • W) := (W.exists_isMinimal R).choose_spec
  set W' := C0 • W with hW'
  -- the discriminant of the minimal model has valuation one
  have hW'1 : v.valuation K W'.Δ = 1 := by
    have hmax := hspec.val_Δ_maximal
    have hback : C0⁻¹ • W' = W := by rw [hW', smul_smul, inv_mul_cancel, one_smul]
    have hP : IsIntegral R (C0⁻¹ • W') := hback ▸ hWi
    have hfj : (valuation_Δ_aux R (C0⁻¹ • W') : ℤᵐ⁰) = 1 := by
      have := @valuation_Δ_aux_eq_of_isIntegral R _ _ _ K _ _ _ (C0⁻¹ • W') hP
      rw [this, hback]; exact hW1
    have h1 : valuation_Δ_aux R ((1 : VariableChange K) • W') ≤ valuation_Δ_aux R (C0⁻¹ • W') := by
      rw [← Subtype.coe_le_coe, hfj]; exact (valuation_Δ_aux R _).2
    have h2 := hmax.2 hP h1
    rw [← Subtype.coe_le_coe, hfj] at h2
    simp only [one_smul] at h2
    letI : IsIntegral R W' := inferInstance
    rw [valuation_Δ_aux_eq_of_isIntegral] at h2
    refine le_antisymm ?_ h2
    obtain ⟨r, hr⟩ := Δ_integral_of_isIntegral R W'
    rw [← hr]; exact valuation_le_one _ r
  haveI hgood : HasGoodReduction R W' := { hspec with goodReduction := hW'1 }
  -- the change of variables is integral
  have hu : v.valuation K (C0.u : K) = 1 := by
    have h := hW'1
    rw [hW', variableChange_Δ, map_mul, map_pow, hW1, mul_one, Units.val_inv_eq_inv_val,
      map_inv₀, inv_pow, inv_eq_one] at h
    rcases pow_eq_one_iff.1 h with h | h
    · exact h
    · norm_num at h
  obtain ⟨u, hu'⟩ := exists_unit_of_valuation_eq_one R hu
  obtain ⟨CR, hCR⟩ := variableChange_integral_of_u_integral (W := W) (W' := W') rfl hu'
  have hint : integralModel R W' = CR • W₀ := by
    have hinj := IsFractionRing.injective R K
    have hmap : (CR • W₀).map (algebraMap R K) = W' := by
      rw [← map_variableChange, ← hWdef]
      exact congrArg (· • W) hCR
    ext
    · exact hinj ((integralModel_a₁_eq R W').trans (congrArg (·.a₁) hmap).symm)
    · exact hinj ((integralModel_a₂_eq R W').trans (congrArg (·.a₂) hmap).symm)
    · exact hinj ((integralModel_a₃_eq R W').trans (congrArg (·.a₃) hmap).symm)
    · exact hinj ((integralModel_a₄_eq R W').trans (congrArg (·.a₄) hmap).symm)
    · exact hinj ((integralModel_a₆_eq R W').trans (congrArg (·.a₆) hmap).symm)
  have hred : W'.reduction R = (CR.map (residue R)) • (W₀.map (residue R)) := by
    rw [reduction, hint, map_variableChange]
  have hΔres : (W₀.map (residue R)).Δ ≠ 0 := by
    rw [map_Δ, residue_ne_zero_iff_isUnit]; exact hΔ
  have hΔred : (W'.reduction R).Δ ≠ 0 := by
    rw [hred, variableChange_Δ]
    exact mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) hΔres
  -- unfold the local polynomial
  have hcard : Nat.card ((W.minimal R).reduction R).toAffine.Point =
      Nat.card (AffineSolutions (W₀.map (residue R))) + 1 := by
    change Nat.card (W'.reduction R).toAffine.Point = _
    rw [card_point_eq _ hΔred, hred, card_equation_variableChange]
  unfold localPolynomial
  rw [ite_cond_eq_true _ _ (eq_true (show HasGoodReduction R (W.minimal R) from hgood)), hcard]
  simp only [Nat.cast_add, Nat.cast_one, add_sub_add_right_eq_sub]

end DVR

/-! ### The finite places of `ℚ` -/

section Rat

open IsDedekindDomain NumberField Rat.HeightOneSpectrum

variable (v : HeightOneSpectrum (𝓞 ℚ))

/-- The rational prime `p` below the finite place `v` of `ℚ`. -/
noncomputable abbrev placePrime : ℕ := (primesEquiv v : ℕ)

instance placePrime_fact : Fact (placePrime v).Prime := ⟨(primesEquiv v).2⟩

/-- The residue field of the completion of `ℤ` at `v` is `ZMod p`. -/
noncomputable def residueFieldEquiv :
    ResidueField (v.adicCompletionIntegers ℚ) ≃+* ZMod (placePrime v) :=
  (ResidueField.mapEquiv (adicCompletionIntegers.padicIntEquiv v).toAlgEquiv.toRingEquiv).trans
    PadicInt.residueField

lemma card_residueField : Nat.card (ResidueField (v.adicCompletionIntegers ℚ)) = placePrime v :=
  (Nat.card_congr (residueFieldEquiv v).toEquiv).trans (Nat.card_zmod _)

instance : Finite (ResidueField (v.adicCompletionIntegers ℚ)) :=
  Finite.of_equiv _ (residueFieldEquiv v).symm.toEquiv

lemma residueFieldEquiv_comp :
    ((residueFieldEquiv v : _ →+* ZMod (placePrime v)).comp
      ((residue (v.adicCompletionIntegers ℚ)).comp (algebraMap ℤ (v.adicCompletionIntegers ℚ)))) =
      Int.castRingHom _ :=
  Subsingleton.elim _ _

/-- **The local polynomial at a finite place of `ℚ`.** For a Weierstrass curve with integer
coefficients and `p ∤ Δ`, Mathlib's local polynomial at the place `v` above `p` is
`1 - a_p X + p X²` with `a_p = p - #{(x, y) ∈ 𝔽_p² : W(x, y) = 0}`. -/
theorem localPolynomial_rat (W : WeierstrassCurve ℤ) (hΔ : ¬ (placePrime v : ℤ) ∣ W.Δ) :
    ((W.baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ) =
      1 - C ((placePrime v : ℤ) -
          Nat.card (AffineSolutions (W.map (Int.castRingHom (ZMod (placePrime v)))))) * X +
        C (placePrime v : ℤ) * X ^ 2 := by
  set Rv := v.adicCompletionIntegers ℚ
  set W₀ := W.map (algebraMap ℤ Rv) with hW₀
  have h1 : (W.baseChange ℚ).baseChange (v.adicCompletion ℚ) =
      W₀.map (algebraMap Rv (v.adicCompletion ℚ)) := by
    rw [baseChange, baseChange, WeierstrassCurve.map_map, hW₀, WeierstrassCurve.map_map]
    exact congrArg W.map (Subsingleton.elim _ _)
  have hu : IsUnit W₀.Δ := by
    rw [hW₀, map_Δ, ← residue_ne_zero_iff_isUnit]
    intro h
    have h' := congrArg (residueFieldEquiv v) h
    rw [map_zero] at h'
    have h'' : (residueFieldEquiv v : _ →+* ZMod (placePrime v)).comp
        ((residue Rv).comp (algebraMap ℤ Rv)) W.Δ = 0 := h'
    rw [residueFieldEquiv_comp, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] at h''
    exact hΔ h''
  rw [h1, localPolynomial_of_isUnit_Δ Rv W₀ hu, card_residueField]
  congr 4
  rw [← card_equation_map _ (residueFieldEquiv v), hW₀, WeierstrassCurve.map_map, WeierstrassCurve.map_map,
    Subsingleton.elim (((residueFieldEquiv v : _ →+* ZMod (placePrime v)).comp (residue Rv)).comp
      (algebraMap ℤ Rv)) (Int.castRingHom _)]

end Rat

end NTKB.IrelandRosen.CM
