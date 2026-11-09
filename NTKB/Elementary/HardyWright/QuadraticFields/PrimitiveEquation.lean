/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Attr
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.RingTheory.Polynomial.Content
import Aesop.BuiltinRules
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
/-!
# Primitive equations of algebraic numbers (Hardy–Wright § 14.2, Theorems 236–237)

An integral polynomial `a₀xⁿ + ⋯ + aₙ` is *primitive* (Hardy–Wright) if `a₀ > 0` and
`(a₀, …, aₙ) = 1`, i.e. `f.IsPrimitive ∧ 0 < f.leadingCoeff`. Let `ξ` be an element of a field `K` of
characteristic `0`, algebraic over `ℚ` of degree `n`.

* Theorem 237 (`exists_primitive_mul`): if `f(ξ) = 0` for a primitive `f` of degree `n` and `g(ξ) = 0`
  for a primitive `g`, then `g = f h` with `h` primitive.
* Theorem 236 (`existsUnique_primitive`, `leadingCoeff_eq_one_of_isIntegral`): `ξ` satisfies a unique
  primitive equation of degree `n`, and its leading coefficient is `1` when `ξ` is an algebraic integer.
-/

namespace NTKB.HardyWright

open Polynomial

variable {K : Type*} [Field K] [CharZero K] {ξ : K}

/-- Hardy–Wright's primitive polynomials: positive leading coefficient, coprime coefficients. -/
abbrev IsPrimitivePos (f : ℤ[X]) : Prop := f.IsPrimitive ∧ 0 < f.leadingCoeff

lemma aeval_map_rat (f : ℤ[X]) : aeval ξ (f.map (Int.castRingHom ℚ)) = aeval ξ f := by
  rw [show Int.castRingHom ℚ = algebraMap ℤ ℚ from rfl, aeval_map_algebraMap]

/-- A rational polynomial of degree `n = deg ξ` vanishing at `ξ` is a constant multiple of the
minimal polynomial. -/
lemma minpoly_dvd_of_natDegree (hξ : IsAlgebraic ℚ ξ) {p : ℚ[X]} (hp0 : p ≠ 0)
    (hp : aeval ξ p = 0) (hdeg : p.natDegree = (minpoly ℚ ξ).natDegree) :
    p ∣ minpoly ℚ ξ := by
  obtain ⟨k, hk⟩ := minpoly.dvd ℚ ξ hp
  have hk0 : k ≠ 0 := by rintro rfl; rw [mul_zero] at hk; exact hp0 hk
  have hm0 : minpoly ℚ ξ ≠ 0 := minpoly.ne_zero hξ.isIntegral
  have hdk : k.natDegree = 0 := by
    have := congrArg natDegree hk
    rw [natDegree_mul hm0 hk0, hdeg] at this
    omega
  rw [natDegree_eq_zero] at hdk
  obtain ⟨c, rfl⟩ := hdk
  have hc : c ≠ 0 := by rintro rfl; exact hk0 (by simp)
  exact ⟨C c⁻¹, by rw [hk, mul_assoc, ← C_mul, mul_inv_cancel₀ hc, C_1, mul_one]⟩

/-- **Theorem 237.** Let `ξ` be algebraic of degree `n`, `f(ξ) = 0` a primitive equation of degree `n`
and `g(ξ) = 0` any primitive equation. Then `g = f h` for some primitive polynomial `h`. -/
@[kb "hardywright2008" "Thm 237, p. 285"]
theorem exists_primitive_mul (hξ : IsAlgebraic ℚ ξ) {f g : ℤ[X]} (hf : IsPrimitivePos f)
    (hfdeg : f.natDegree = (minpoly ℚ ξ).natDegree) (hfξ : aeval ξ f = 0)
    (hg : IsPrimitivePos g) (hgξ : aeval ξ g = 0) : ∃ h : ℤ[X], IsPrimitivePos h ∧ g = f * h := by
  have hinj : Function.Injective (Int.castRingHom ℚ) := RingHom.injective_int _
  have hf0 : f ≠ 0 := hf.1.ne_zero
  have hfq0 : f.map (Int.castRingHom ℚ) ≠ 0 := (Polynomial.map_ne_zero_iff hinj).2 hf0
  -- `f ∣ g` over `ℚ`, hence over `ℤ` (Gauss's lemma, Theorem 104 (i))
  have h1 : f.map (Int.castRingHom ℚ) ∣ minpoly ℚ ξ :=
    minpoly_dvd_of_natDegree hξ hfq0 (by rw [aeval_map_rat]; exact hfξ)
      (by rw [natDegree_map_eq_of_injective hinj, hfdeg])
  have h2 : minpoly ℚ ξ ∣ g.map (Int.castRingHom ℚ) := minpoly.dvd ℚ ξ (by rw [aeval_map_rat]; exact hgξ)
  obtain ⟨h, rfl⟩ := (IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast f g hf.1).2 (h1.trans h2)
  refine ⟨h, ⟨fun r hr ↦ hg.1 r (dvd_mul_of_dvd_right hr f), ?_⟩, rfl⟩
  have := hg.2
  rw [leadingCoeff_mul] at this
  exact pos_of_mul_pos_right this hf.2.le

/-- **Theorem 236.** An algebraic number `ξ` of degree `n` satisfies a unique primitive equation of
degree `n`. -/
@[kb "hardywright2008" "Thm 236, p. 284"]
theorem existsUnique_primitive (hξ : IsAlgebraic ℚ ξ) :
    ∃! f : ℤ[X], IsPrimitivePos f ∧ f.natDegree = (minpoly ℚ ξ).natDegree ∧ aeval ξ f = 0 := by
  have hinj : Function.Injective (Int.castRingHom ℚ) := RingHom.injective_int _
  set q := minpoly ℚ ξ
  have hq0 : q ≠ 0 := minpoly.ne_zero hξ.isIntegral
  -- clear denominators
  obtain ⟨b, hbM, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) q
  set f0 := IsLocalization.integerNormalization (nonZeroDivisors ℤ) q
  have hb0 : ((b : ℤ) : ℚ) ≠ 0 := by
    have := nonZeroDivisors.ne_zero hbM
    exact_mod_cast this
  have hf0map : f0.map (Int.castRingHom ℚ) = C ((b : ℤ) : ℚ) * q := by
    have : f0.map (Int.castRingHom ℚ) = b • q := hb
    rw [this, zsmul_eq_mul, ← C_eq_intCast]
  have hf0deg : f0.natDegree = q.natDegree := by
    rw [← natDegree_map_eq_of_injective hinj, hf0map, natDegree_C_mul hb0]
  have hf0ξ : aeval ξ f0 = 0 := by
    rw [← aeval_map_rat, hf0map, map_mul, minpoly.aeval, mul_zero]
  have hf00 : f0 ≠ 0 := by
    intro h; rw [h, Polynomial.map_zero] at hf0map
    exact (mul_ne_zero (C_ne_zero.2 hb0) hq0) hf0map.symm
  -- its primitive part
  set f1 := f0.primPart
  have hf1 : f1.IsPrimitive := isPrimitive_primPart f0
  have hf1deg : f1.natDegree = q.natDegree := by rw [natDegree_primPart, hf0deg]
  have hf1ξ : aeval ξ f1 = 0 := by
    have e := eq_C_content_mul_primPart f0
    have hc : (f0.content : K) ≠ 0 := by exact_mod_cast (content_eq_zero_iff.not.2 hf00)
    rw [e, map_mul, aeval_C] at hf0ξ
    simpa [hc] using hf0ξ
  have hf10 : f1 ≠ 0 := hf1.ne_zero
  -- make the leading coefficient positive
  have key : ∃ f : ℤ[X], IsPrimitivePos f ∧ f.natDegree = q.natDegree ∧ aeval ξ f = 0 := by
    rcases lt_or_gt_of_ne (leadingCoeff_ne_zero.2 hf10) with h | h
    · refine ⟨-f1, ⟨fun r hr ↦ hf1 r ((dvd_neg).1 hr), by rw [leadingCoeff_neg]; linarith⟩, by rw [natDegree_neg, hf1deg],
        by rw [map_neg, hf1ξ, neg_zero]⟩
    · exact ⟨f1, ⟨hf1, h⟩, hf1deg, hf1ξ⟩
  obtain ⟨f, hf, hfdeg, hfξ⟩ := key
  refine ⟨f, ⟨hf, hfdeg, hfξ⟩, fun g ⟨hg, hgdeg, hgξ⟩ ↦ ?_⟩
  obtain ⟨h, hh, rfl⟩ := exists_primitive_mul hξ hf hfdeg hfξ hg hgξ
  have hh0 : h ≠ 0 := hh.1.ne_zero
  have hdeg : h.natDegree = 0 := by
    rw [natDegree_mul hf.1.ne_zero hh0, hfdeg] at hgdeg; omega
  rw [natDegree_eq_zero] at hdeg
  obtain ⟨c, rfl⟩ := hdeg
  have hc : IsUnit c := by
    have := hh.1
    rw [isPrimitive_iff_isUnit_of_C_dvd] at this
    exact this c dvd_rfl
  have hc1 : c = 1 := by
    rcases Int.isUnit_iff.1 hc with rfl | rfl
    · rfl
    · have := hh.2; simp at this
  rw [hc1, C_1, mul_one]

/-- **Theorem 236**, second part: if `ξ` is an algebraic integer, the leading coefficient of its
primitive equation of degree `n` is `1`. -/
@[kb "hardywright2008" "Thm 236, p. 284"]
theorem leadingCoeff_eq_one_of_isIntegral (hξ : IsIntegral ℤ ξ) {f : ℤ[X]} (hf : IsPrimitivePos f)
    (hfdeg : f.natDegree = (minpoly ℚ ξ).natDegree) (hfξ : aeval ξ f = 0) : f.leadingCoeff = 1 := by
  have hξ' : IsAlgebraic ℚ ξ := (IsIntegral.tower_top (A := ℚ) hξ).isAlgebraic
  obtain ⟨p, hpm, hpξ⟩ := hξ
  obtain ⟨h, hh, hph⟩ := exists_primitive_mul hξ' hf hfdeg hfξ
    ⟨hpm.isPrimitive, by rw [hpm.leadingCoeff]; norm_num⟩ (by rwa [aeval_def])
  have := hpm.leadingCoeff
  rw [hph, leadingCoeff_mul] at this
  exact Int.eq_one_of_mul_eq_one_right hf.2.le this

end NTKB.HardyWright
