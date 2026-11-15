/-
Ireland–Rosen, Chapter 9, §4: the Jacobi sum and the Gauss sum of the cubic residue character.
-/
import NTKB.IrelandRosen.R4.CubicChar
import NTKB.IrelandRosen.R2.Cubic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# `J(χ_π, χ_π) = π` and `g(χ_π)³ = pπ` (Ireland–Rosen, Chapter 9, §4)

For a prime `π` of `ℤ[ω]` of prime norm `p ≠ 3`, `ℤ[ω]/π = ℤ/p`, so the cubic residue character
`χ_π` is a multiplicative character of order 3 of `ZMod p` with values in `ℤ[ω]` (`cubicMulChar`).
For `π` primary, Lemma 1 of §4: `J(χ_π, χ_π) = π`; its corollary: `g(χ_π)³ = pπ`, for the Gauss
sum taken in any domain `R` in which `3 ≠ 0`, through a ring homomorphism `ℤ[ω] → R`. The book's
complex Gauss sum is the case `R = ℂ`, `toComplex : ℤ[ω] → ℂ`, `ω ↦ e^{2πi/3}`.
-/

namespace NTKB.IrelandRosen

open NTKB.HardyWright QuadraticAlgebra

local notation "ℤ[ω]" => NTKB.HardyWright.ZRho

namespace Eisenstein

set_option linter.unusedSectionVars false

/-- The embedding `ℤ[ω] → ℂ`, `a + bω ↦ a + b e^{2πi/3}`. -/
noncomputable def toComplex : ℤ[ω] →+* ℂ :=
  (QuadraticAlgebra.lift (R := ℤ) (a := -1) (b := -1) (A := ℂ)
    ⟨omega3, by rw [← sq, omega3_sq]; simp; ring⟩ : ℤ[ω] →ₐ[ℤ] ℂ).toRingHom

lemma toComplex_apply (x : ℤ[ω]) : toComplex x = x.re + x.im * omega3 := by
  simp [toComplex]

lemma toComplex_injective : Function.Injective toComplex := by
  intro x y h
  rw [toComplex_apply, toComplex_apply] at h
  obtain ⟨h1, h2⟩ := add_mul_omega3_inj h
  ext <;> assumption

lemma toComplex_star (x : ℤ[ω]) : toComplex (star x) = starRingEnd ℂ (toComplex x) := by
  have hc : starRingEnd ℂ omega3 = -1 - omega3 := by
    apply Complex.ext <;> simp [omega3_re_im.1]
    norm_num
  rw [toComplex_apply, toComplex_apply]
  simp [hc]
  ring

variable (π : ℤ[ω]) [Fact (norm π).natAbs.Prime]

lemma prime_norm : (norm π).natAbs.Prime := Fact.out

lemma prime_of_fact : Prime π := prime_of_natAbs_norm_prime (prime_norm π)

omit [Fact (norm π).natAbs.Prime] in
lemma intCast_emod_sub (n : ℤ) (N : ℕ) :
    (((n % N : ℤ)) : ℤ[ω]) - n = -((N : ℤ[ω]) * ((n / N : ℤ) : ℤ[ω])) := by
  have h' : (((n % N : ℤ)) : ℤ[ω]) = ((n - N * (n / N) : ℤ) : ℤ[ω]) := by rw [Int.emod_def]
  rw [h']; push_cast; ring

omit [Fact (norm π).natAbs.Prime] in
lemma dvd_natAbs_norm_cast : π ∣ (((norm π).natAbs : ℕ) : ℤ[ω]) := by
  simpa using qa_dvd_natAbs_norm π

omit [Fact (norm π).natAbs.Prime] in
lemma dvd_natCast_mod_sub (n : ℕ) :
    π ∣ (((n % (norm π).natAbs : ℕ)) : ℤ[ω]) - n := by
  have h := Nat.mod_add_div n (norm π).natAbs
  have h' : (n : ℤ[ω]) = ((n % (norm π).natAbs : ℕ) : ℤ[ω]) +
      (((norm π).natAbs : ℕ) : ℤ[ω]) * ((n / (norm π).natAbs : ℕ) : ℤ[ω]) := by
    exact_mod_cast h.symm
  have : (((n % (norm π).natAbs : ℕ)) : ℤ[ω]) - n =
      -((((norm π).natAbs : ℕ) : ℤ[ω]) * ((n / (norm π).natAbs : ℕ) : ℤ[ω])) := by
    linear_combination -h'
  rw [this]; exact (dvd_mul_of_dvd_left (dvd_natAbs_norm_cast π) _).neg_right

/-- The cubic residue character `χ_π` as a multiplicative character on `ZMod p = ℤ[ω]/π`, for `π`
of prime norm `p ≠ 3`. -/
noncomputable def cubicMulChar (h3 : (norm π).natAbs ≠ 3) :
    MulChar (ZMod (norm π).natAbs) ℤ[ω] where
  toFun t := cubicChar π (t.val : ℤ[ω])
  map_one' := by
    have : Fact (1 < (norm π).natAbs) := ⟨(prime_norm π).one_lt⟩
    show cubicChar π (((1 : ZMod (norm π).natAbs).val : ℕ) : ℤ[ω]) = 1
    rw [ZMod.val_one, Nat.cast_one]
    exact cubicChar_one (prime_of_fact π) h3
  map_mul' s t := by
    show cubicChar π (((s * t).val : ℕ) : ℤ[ω]) =
      cubicChar π ((s.val : ℕ) : ℤ[ω]) * cubicChar π ((t.val : ℕ) : ℤ[ω])
    rw [ZMod.val_mul, ← cubicChar_mul (prime_of_fact π) h3, ← Nat.cast_mul]
    exact cubicChar_congr (dvd_natCast_mod_sub π _)
  map_nonunit' t ht := by
    show cubicChar π ((t.val : ℕ) : ℤ[ω]) = 0
    have : t = 0 := by
      by_contra h; exact ht (isUnit_iff_ne_zero.2 h)
    subst this
    simp [cubicChar_of_dvd (dvd_zero π)]

variable {π} (h3 : (norm π).natAbs ≠ 3)

lemma cubicMulChar_apply (t : ZMod (norm π).natAbs) :
    cubicMulChar π h3 t = cubicChar π (t.val : ℤ[ω]) := rfl

lemma cubicMulChar_intCast (n : ℤ) : cubicMulChar π h3 n = cubicChar π n := by
  rw [cubicMulChar_apply]
  refine cubicChar_congr ?_
  have hv : (((n : ZMod (norm π).natAbs).val : ℕ) : ℤ) = n % (norm π).natAbs :=
    ZMod.val_intCast n
  have : (((n : ZMod (norm π).natAbs).val : ℕ) : ℤ[ω]) - (n : ℤ[ω]) =
      -((((norm π).natAbs : ℕ) : ℤ[ω]) * ((n / (norm π).natAbs : ℤ) : ℤ[ω])) := by
    rw [← Int.cast_natCast, hv]
    exact intCast_emod_sub n _
  rw [this]; exact (dvd_mul_of_dvd_left (dvd_natAbs_norm_cast π) _).neg_right

lemma cubicMulChar_natCast (n : ℕ) : cubicMulChar π h3 n = cubicChar π n := by
  rw [cubicMulChar_apply, ZMod.val_natCast]
  exact cubicChar_congr (dvd_natCast_mod_sub π n)

/-- Modulo `π`, `χ_π(t) ≡ t ^ ((p - 1) / 3)`. -/
lemma toZMod_cubicMulChar (t : ZMod (norm π).natAbs) :
    toZMod (prime_norm π) (cubicMulChar π h3 t) = t ^ cexp π := by
  by_cases ht : t = 0
  · subst ht
    rw [MulChar.map_zero, map_zero, zero_pow (cexp_pos (prime_of_fact π) h3).ne']
  have hα : ¬ π ∣ ((t.val : ℕ) : ℤ[ω]) := by
    rw [← toZMod_eq_zero_iff (prime_norm π), map_natCast, ZMod.natCast_zmod_val]; exact ht
  obtain ⟨-, hd⟩ := cubicChar_spec (prime_of_fact π) h3 hα
  rw [← toZMod_eq_iff (prime_norm π), map_pow, map_natCast, ZMod.natCast_zmod_val] at hd
  rw [cubicMulChar_apply, ← hd]

lemma cubicMulChar_pow_three : cubicMulChar π h3 ^ 3 = 1 := by
  refine MulChar.ext fun u => ?_
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
  have hα : ¬ π ∣ ((((u : ZMod (norm π).natAbs)).val : ℕ) : ℤ[ω]) := by
    rw [← toZMod_eq_zero_iff (prime_norm π), map_natCast, ZMod.natCast_zmod_val]; exact u.ne_zero
  exact (cubicChar_spec (prime_of_fact π) h3 hα).1

lemma cubicMulChar_unit_pow_three (g : (ZMod (norm π).natAbs)ˣ) :
    (cubicMulChar π h3 (g : ZMod (norm π).natAbs)) ^ 3 = 1 := by
  rw [← MulChar.pow_apply_coe, cubicMulChar_pow_three, MulChar.one_apply_coe]

lemma isUnit_cubicMulChar {t : ZMod (norm π).natAbs} (ht : t ≠ 0) :
    IsUnit (cubicMulChar π h3 t) := by
  have := cubicMulChar_unit_pow_three h3 (Units.mk0 t ht)
  simp only [Units.val_mk0] at this
  exact IsUnit.of_mul_eq_one (cubicMulChar π h3 t ^ 2) (by rw [← pow_succ']; exact this)

/-- There is `g` with `χ_π(g) ≠ 1` (a generator of `(ZMod p)ˣ`). -/
lemma exists_cubicMulChar_ne_one :
    ∃ g : (ZMod (norm π).natAbs)ˣ, cubicMulChar π h3 (g : ZMod (norm π).natAbs) ≠ 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod (norm π).natAbs)ˣ)
  refine ⟨g, fun h => ?_⟩
  have h' := congrArg (toZMod (prime_norm π)) h
  rw [toZMod_cubicMulChar, map_one] at h'
  have hg1 : g ^ cexp π = 1 := by ext; simpa using h'
  have hord : orderOf g = (norm π).natAbs - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  have hk := cexp_pos (prime_of_fact π) h3
  have h3k := three_mul_cexp (prime_of_fact π) h3
  have hd : (norm π).natAbs - 1 ∣ cexp π := by
    rw [← hord]; exact orderOf_dvd_of_pow_eq_one hg1
  have := Nat.le_of_dvd hk hd
  omega

theorem orderOf_cubicMulChar : orderOf (cubicMulChar π h3) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime (cubicMulChar_pow_three h3) fun h => ?_
  obtain ⟨g, hg⟩ := exists_cubicMulChar_ne_one h3
  apply hg
  rw [h, MulChar.one_apply_coe]

lemma cubicMulChar_ne_one : cubicMulChar π h3 ≠ 1 := by
  intro h
  have := orderOf_cubicMulChar h3
  rw [h, orderOf_one] at this; omega

lemma cubicMulChar_sq_ne_one : cubicMulChar π h3 ^ 2 ≠ 1 := by
  intro h
  have := orderOf_dvd_of_pow_eq_one h
  rw [orderOf_cubicMulChar h3] at this; omega

lemma sum_pow_mul_one_sub_pow {p : ℕ} [Fact p.Prime] (k : ℕ) (hk : 2 * k < p - 1) :
    ∑ t : ZMod p, t ^ k * (1 - t) ^ k = 0 := by
  have hexp : ∀ t : ZMod p, t ^ k * (1 - t) ^ k =
      ∑ m ∈ Finset.range (k + 1), ((-1) ^ m * (k.choose m : ZMod p)) * t ^ (k + m) := by
    intro t
    rw [sub_eq_add_neg, add_comm, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [one_pow, mul_one, neg_pow, pow_add]; ring
  simp_rw [hexp]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun m hm => ?_
  rw [← Finset.mul_sum, FiniteField.sum_pow_lt_card_sub_one, mul_zero]
  · rw [ZMod.card]; rw [Finset.mem_range] at hm; omega

/-- `J(χ_π, χ_π) ≡ 0 (mod π)`. -/
lemma dvd_jacobiSum_cubicMulChar :
    π ∣ jacobiSum (cubicMulChar π h3) (cubicMulChar π h3) := by
  rw [← toZMod_eq_zero_iff (prime_norm π), jacobiSum, map_sum]
  simp_rw [map_mul, toZMod_cubicMulChar]
  refine sum_pow_mul_one_sub_pow _ ?_
  have h := three_mul_cexp (prime_of_fact π) h3
  have := cexp_pos (prime_of_fact π) h3
  omega

lemma cubicMulChar_inv :
    (cubicMulChar π h3)⁻¹ = (cubicMulChar π h3).ringHomComp (starRingEnd ℤ[ω]) := by
  refine MulChar.ext fun u => ?_
  rw [MulChar.inv_apply_eq_inv, MulChar.ringHomComp_apply, starRingEnd_apply]
  obtain ⟨w, hw⟩ := isUnit_cubicMulChar h3 u.ne_zero
  have hw3 : (w : ℤ[ω]) ^ 3 = 1 := by rw [hw]; exact cubicMulChar_unit_pow_three h3 u
  rw [← hw, Ring.inverse_unit, star_eq_sq_of_pow_three hw3]
  exact Units.inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hw3)

omit [Fact (norm π).natAbs.Prime] in
lemma ringHomComp_ringHomComp {R' R'' : Type*} [CommRing R'] [CommRing R'']
    (χ : MulChar (ZMod (norm π).natAbs) ℤ[ω]) (f : ℤ[ω] →+* R') (g : R' →+* R'') :
    (χ.ringHomComp f).ringHomComp g = χ.ringHomComp (g.comp f) := by
  ext; rfl

/-- `J(χ_π, χ_π)` has norm `p`. -/
theorem natAbs_norm_jacobiSum :
    (norm (jacobiSum (cubicMulChar π h3) (cubicMulChar π h3))).natAbs = (norm π).natAbs := by
  set χ := cubicMulChar π h3
  let f : ℤ[ω] →+* ℂ := toComplex
  have hf : Function.Injective f := toComplex_injective
  have hchar : ringChar ℂ ≠ ringChar (ZMod (norm π).natAbs) := by
    rw [ringChar.eq_zero, ZMod.ringChar_zmod_n]; exact (prime_norm π).ne_zero.symm
  have h1 : χ.ringHomComp f ≠ 1 := (MulChar.ringHomComp_ne_one_iff hf).2 (cubicMulChar_ne_one h3)
  have h2 : χ.ringHomComp f * χ.ringHomComp f ≠ 1 := by
    rw [← MulChar.ringHomComp_mul, MulChar.ringHomComp_ne_one_iff hf, ← sq]
    exact cubicMulChar_sq_ne_one h3
  have H := jacobiSum_mul_jacobiSum_inv hchar h1 h1 h2
  rw [MulChar.ringHomComp_inv, cubicMulChar_inv, ringHomComp_ringHomComp, jacobiSum_ringHomComp,
    jacobiSum_ringHomComp] at H
  change f _ * (f.comp (starRingEnd ℤ[ω])) _ = _ at H
  rw [RingHom.comp_apply, ← map_mul, ZMod.card, ← map_natCast f, starRingEnd_apply,
    mul_star] at H
  have H' := hf H
  have : norm (jacobiSum χ χ) = (((norm π).natAbs : ℕ) : ℤ) :=
    Int.cast_injective (α := ℤ[ω]) (by rw [Int.cast_natCast]; exact H')
  rw [this, Int.natAbs_natCast]

lemma isPrimitiveRoot_omega : IsPrimitiveRoot omega 3 := by
  refine IsPrimitiveRoot.mk_of_lt omega (by norm_num) omega_cube fun l hl hl3 => ?_
  interval_cases l
  · rw [pow_one]; exact omega_ne_one
  · exact omega_sq_ne_one

lemma isPrimary_jacobiSum :
    IsPrimary (jacobiSum (cubicMulChar π h3) (cubicMulChar π h3)) := by
  have h3d : 3 ∣ Fintype.card (ZMod (norm π).natAbs) - 1 := by
    rw [ZMod.card]; exact ⟨cexp π, (three_mul_cexp (prime_of_fact π) h3).symm⟩
  obtain ⟨z, -, hz⟩ := exists_jacobiSum_eq_neg_one_add (by norm_num) (cubicMulChar_pow_three h3)
    (cubicMulChar_pow_three h3) h3d isPrimitiveRoot_omega
  unfold IsPrimary
  refine ⟨-1 - z * omega, ?_⟩
  rw [hz]
  linear_combination z * omega_sq

/-- **Lemma 1 of §4.** For a primary prime `π` of prime norm, `J(χ_π, χ_π) = π`. -/
@[kb "irelandrosen1990" "Ch. 9, §4, Lemma 1, p. 126"]
theorem jacobiSum_cubicMulChar (hP : IsPrimary π) :
    jacobiSum (cubicMulChar π h3) (cubicMulChar π h3) = π := by
  obtain ⟨γ, hγ⟩ := dvd_jacobiSum_cubicMulChar h3
  have hN := natAbs_norm_jacobiSum h3
  have hprim := isPrimary_jacobiSum h3
  rw [hγ, map_mul, Int.natAbs_mul] at hN
  rw [hγ] at hprim ⊢
  have hγu : IsUnit γ := by
    rw [qa_isUnit_iff]
    exact (Nat.mul_eq_left (prime_norm π).ne_zero).1 hN
  rw [mul_comm] at hprim
  have := unit_eq_of_isPrimary hγu isUnit_one hprim (by rw [one_mul]; exact hP)
  rw [this, mul_one]

lemma map_ne_one_of_pow_three {R : Type*} [CommRing R] (f : ℤ[ω] →+* R) (h3R : (3 : R) ≠ 0) {u : ℤ[ω]}
    (hu : u ^ 3 = 1) (hne : u ≠ 1) : f u ≠ 1 := by
  intro h
  obtain ⟨c, hc⟩ := sub_dvd_three hu (one_pow 3) hne
  have := congrArg f hc
  rw [map_mul, map_sub, h, map_one, sub_self, zero_mul, map_ofNat] at this
  exact h3R this

lemma orderOf_cubicMulChar_ringHomComp {R : Type*} [CommRing R] [IsDomain R] (f : ℤ[ω] →+* R)
    (h3R : (3 : R) ≠ 0) : orderOf ((cubicMulChar π h3).ringHomComp f) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime (by rw [MulChar.ringHomComp_pow]; simp [cubicMulChar_pow_three h3])
    fun h => ?_
  obtain ⟨g, hg⟩ := exists_cubicMulChar_ne_one h3
  have := congrArg (fun χ : MulChar (ZMod (norm π).natAbs) R => χ (g : ZMod (norm π).natAbs)) h
  simp only [MulChar.ringHomComp_apply, MulChar.one_apply_coe] at this
  exact map_ne_one_of_pow_three f h3R (cubicMulChar_unit_pow_three h3 g) hg this

/-- **Corollary to Lemma 1 of §4.** `g(χ_π)³ = pπ`, for the Gauss sum with values in a domain `R`
with `3 ≠ 0`, through a ring homomorphism `f : ℤ[ω] → R` and a primitive additive character. -/
@[kb "irelandrosen1990" "Ch. 9, §4, Corollary, p. 126"]
theorem gaussSum_cubicMulChar_pow_three (hP : IsPrimary π) {R : Type*} [CommRing R] [IsDomain R]
    (f : ℤ[ω] →+* R) (h3R : (3 : R) ≠ 0) {ψ : AddChar (ZMod (norm π).natAbs) R}
    (hψ : ψ.IsPrimitive) :
    gaussSum ((cubicMulChar π h3).ringHomComp f) ψ ^ 3 = ((norm π).natAbs : R) * f π := by
  have hord := orderOf_cubicMulChar_ringHomComp h3 f h3R
  have hm1 : cubicMulChar π h3 (-1) = 1 := by
    have := cubicMulChar_intCast h3 (-1)
    simpa [cubicChar_neg_one (prime_of_fact π) h3] using this
  have H := gaussSum_pow_eq_prod_jacobiSum (χ := (cubicMulChar π h3).ringHomComp f) (ψ := ψ)
    (by rw [hord]; norm_num) hψ
  rw [hord] at H
  rw [show Finset.Ico 1 (3 - 1) = {1} by decide, Finset.prod_singleton, pow_one,
    jacobiSum_ringHomComp, jacobiSum_cubicMulChar h3 hP, MulChar.ringHomComp_apply, hm1,
    map_one, ZMod.card, one_mul] at H
  exact H

/-- **Corollary to Lemma 1 of §4**, the book's complex form: `g(χ_π)³ = pπ` with
`g(χ_π) = ∑ₜ χ_π(t) e^{2πit/p}`. -/
@[kb "irelandrosen1990" "Ch. 9, §4, Corollary, p. 126"]
theorem gaussSum_cubicMulChar_pow_three_complex (hP : IsPrimary π) :
    gaussSum ((cubicMulChar π h3).ringHomComp toComplex) ZMod.stdAddChar ^ 3 =
      ((norm π).natAbs : ℂ) * toComplex π := by
  have : NeZero (norm π).natAbs := ⟨(prime_norm π).ne_zero⟩
  exact gaussSum_cubicMulChar_pow_three h3 hP toComplex (by norm_num)
    (ZMod.isPrimitive_stdAddChar _)

end Eisenstein

end NTKB.IrelandRosen
