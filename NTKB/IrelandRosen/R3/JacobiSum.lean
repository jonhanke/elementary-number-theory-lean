/-
Ireland–Rosen, Chapter 9, §9: Jacobi and Gauss sums of the quartic character.
-/
import NTKB.IrelandRosen.R3.QuarticSymbol
import NTKB.Port.QuarticJacobiSum

/-!
# Jacobi and Gauss sums of the quartic residue character

Ireland–Rosen, Chapter 9, §9, Propositions 9.9.1 to 9.9.5. Let `π` be a primary irreducible of
`ℤ[i]` of prime norm `p` (so `p ≡ 1 (mod 4)`). The quartic residue character `χ_π` is viewed as a
multiplicative character of the residue field `ℤ[i]/π = ZMod p` (`quarticMulChar`).

* `J(χ_π, χ_π) = χ_π(-1) J(χ_π, ψ)` with `ψ = χ_π²` the Legendre symbol (Proposition 9.9.1);
* `g(χ_π)⁴ = p J(χ_π, χ_π)²` (Proposition 9.9.2);
* `-χ_π(-1) J(χ_π, χ_π)` is primary (Proposition 9.9.3) and equals `π` (Proposition 9.9.4);
* `g(χ_π)⁴ = π³ π̄` (Proposition 9.9.5).

Gauss sums are taken with values in any integral domain `R'` with a ring homomorphism
`φ : ℤ[i] → R'` and a primitive additive character `ψ` of `ZMod p` (for the book, `R' = ℂ` and
`ψ(t) = e^{2πit/p}`), and `(2 : R') ≠ 0`. The congruence `J ≡ ... (mod (1 + i)³)` behind
Proposition 9.9.3 is ported from Tau Ceti (`NTKB.Port.one_add_pow_three_dvd_apply_neg_one_mul_jacobiSum_add_one`).
-/

namespace NTKB.IrelandRosen

open Zsqrtd

local notation "ℤ[i]" => GaussianInt

namespace Gaussian

variable {π : ℤ[i]} [hp : Fact (Nat.Prime π.norm.natAbs)]

omit hp in
lemma intCast_emod_sub (n : ℤ) (N : ℕ) :
    (((n % N : ℤ)) : ℤ[i]) - n = -((N : ℤ[i]) * ((n / N : ℤ) : ℤ[i])) := by
  have h' : (((n % N : ℤ)) : ℤ[i]) = ((n - N * (n / N) : ℤ) : ℤ[i]) := by rw [Int.emod_def]
  rw [h']; push_cast; ring

omit hp in
lemma dvd_natCast_mod_sub (n : ℕ) :
    π ∣ (((n % π.norm.natAbs : ℕ)) : ℤ[i]) - n := by
  have h := Nat.mod_add_div n π.norm.natAbs
  have h' : (n : ℤ[i]) = ((n % π.norm.natAbs : ℕ) : ℤ[i]) +
      ((π.norm.natAbs : ℕ) : ℤ[i]) * ((n / π.norm.natAbs : ℕ) : ℤ[i]) := by exact_mod_cast h.symm
  have : (((n % π.norm.natAbs : ℕ)) : ℤ[i]) - n =
      -(((π.norm.natAbs : ℕ) : ℤ[i]) * ((n / π.norm.natAbs : ℕ) : ℤ[i])) := by
    linear_combination -h'
  rw [this]; exact (dvd_mul_of_dvd_left (dvd_natAbs_norm π) _).neg_right

lemma irreducible_of_fact : Irreducible π := irreducible_of_prime_norm hp.out

/-- The quartic residue character `χ_π` as a multiplicative character on `ZMod p = ℤ[i]/π`,
for `π` of prime norm `p ≠ 2`. -/
noncomputable def quarticMulChar (π : ℤ[i]) [Fact (Nat.Prime π.norm.natAbs)]
    (hp2 : π.norm.natAbs ≠ 2) : MulChar (ZMod π.norm.natAbs) ℤ[i] where
  toFun t := quarticChar π (t.val : ℤ[i])
  map_one' := by
    haveI : Fact (1 < π.norm.natAbs) := ⟨(Fact.out : Nat.Prime _).one_lt⟩
    show quarticChar π (((1 : ZMod π.norm.natAbs).val : ℕ) : ℤ[i]) = 1
    rw [ZMod.val_one, Nat.cast_one]
    exact quarticChar_one irreducible_of_fact hp2
  map_mul' s t := by
    show quarticChar π (((s * t).val : ℕ) : ℤ[i]) =
      quarticChar π ((s.val : ℕ) : ℤ[i]) * quarticChar π ((t.val : ℕ) : ℤ[i])
    rw [ZMod.val_mul, ← quarticChar_mul irreducible_of_fact hp2, ← Nat.cast_mul]
    exact quarticChar_congr (dvd_natCast_mod_sub _)
  map_nonunit' t ht := by
    show quarticChar π ((t.val : ℕ) : ℤ[i]) = 0
    have : t = 0 := by
      by_contra h; exact ht (isUnit_iff_ne_zero.2 h)
    subst this
    simp [quarticChar_of_dvd (dvd_zero π)]

variable (hp2 : π.norm.natAbs ≠ 2)

lemma quarticMulChar_apply (t : ZMod π.norm.natAbs) :
    quarticMulChar π hp2 t = quarticChar π (t.val : ℤ[i]) := rfl

lemma quarticMulChar_natCast (n : ℕ) :
    quarticMulChar π hp2 (n : ZMod π.norm.natAbs) = quarticChar π (n : ℤ[i]) := by
  rw [quarticMulChar_apply, ZMod.val_natCast]
  exact quarticChar_congr (dvd_natCast_mod_sub n)

lemma quarticMulChar_intCast (n : ℤ) :
    quarticMulChar π hp2 (n : ZMod π.norm.natAbs) = quarticChar π (n : ℤ[i]) := by
  rw [quarticMulChar_apply]
  refine quarticChar_congr ?_
  have hv : (((n : ZMod π.norm.natAbs).val : ℕ) : ℤ) = n % π.norm.natAbs := ZMod.val_intCast n
  have : (((n : ZMod π.norm.natAbs).val : ℕ) : ℤ[i]) - (n : ℤ[i]) =
      -(((π.norm.natAbs : ℕ) : ℤ[i]) * ((n / π.norm.natAbs : ℤ) : ℤ[i])) := by
    rw [← Int.cast_natCast, hv]
    exact intCast_emod_sub n _
  rw [this]; exact (dvd_mul_of_dvd_left (dvd_natAbs_norm π) _).neg_right

lemma qexp_pos (hp2 : π.norm.natAbs ≠ 2) : 0 < qexp π := by
  have h4 := four_mul_qexp irreducible_of_fact hp2
  have := (Fact.out : Nat.Prime π.norm.natAbs).two_le
  omega

/-- Modulo `π`, `χ_π(t) ≡ t ^ ((p - 1) / 4)`. -/
lemma toZMod_quarticMulChar (t : ZMod π.norm.natAbs) :
    toZMod hp.out (quarticMulChar π hp2 t) = t ^ qexp π := by
  by_cases ht : t = 0
  · subst ht
    rw [MulChar.map_zero, map_zero, zero_pow (qexp_pos hp2).ne']
  have hα : ¬ π ∣ ((t.val : ℕ) : ℤ[i]) := by
    rw [← toZMod_eq_zero_iff hp.out, map_natCast, ZMod.natCast_zmod_val]; exact ht
  obtain ⟨-, hd⟩ := quarticChar_spec irreducible_of_fact hp2 hα
  rw [← toZMod_eq_iff hp.out, map_pow, map_natCast, ZMod.natCast_zmod_val] at hd
  rw [quarticMulChar_apply, ← hd]

lemma unit_pow_four {u : ℤ[i]} (hu : IsUnit u) : u ^ 4 = 1 := by
  rcases isUnit_iff_eq.1 hu with rfl | rfl | rfl | rfl
  · simp
  · norm_num
  · exact I_pow_four
  · rw [Even.neg_pow (by decide), I_pow_four]

lemma quarticMulChar_pow_four : quarticMulChar π hp2 ^ 4 = 1 := by
  refine MulChar.ext fun u => ?_
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
  have hα : ¬ π ∣ ((((u : ZMod π.norm.natAbs)).val : ℕ) : ℤ[i]) := by
    rw [← toZMod_eq_zero_iff hp.out, map_natCast, ZMod.natCast_zmod_val]; exact u.ne_zero
  exact unit_pow_four (quarticChar_spec irreducible_of_fact hp2 hα).1

lemma isUnit_quarticMulChar {t : ZMod π.norm.natAbs} (ht : t ≠ 0) :
    IsUnit (quarticMulChar π hp2 t) := by
  have hα : ¬ π ∣ ((t.val : ℕ) : ℤ[i]) := by
    rw [← toZMod_eq_zero_iff hp.out, map_natCast, ZMod.natCast_zmod_val]; exact ht
  exact (quarticChar_spec irreducible_of_fact hp2 hα).1

/-- There is `g` with `χ_π(g)² = -1` (a generator of `(ZMod p)ˣ`). -/
lemma exists_quarticMulChar_sq_eq_neg_one :
    ∃ g : (ZMod π.norm.natAbs)ˣ, quarticMulChar π hp2 g ^ 2 = -1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod π.norm.natAbs)ˣ)
  refine ⟨g, ?_⟩
  have hu := isUnit_quarticMulChar hp2 g.ne_zero
  have h4 := four_mul_qexp irreducible_of_fact hp2
  have hk := qexp_pos hp2
  -- `χ(g)² ≠ 1`, as `g ^ (2k) ≠ 1` for a generator `g` of order `4k`
  have hne : quarticMulChar π hp2 g ^ 2 ≠ 1 := by
    intro h
    have h' := congrArg (toZMod hp.out) h
    rw [map_pow, toZMod_quarticMulChar, map_one, ← pow_mul] at h'
    have hg1 : g ^ (qexp π * 2) = 1 := by ext; simpa using h'
    have hord : orderOf g = π.norm.natAbs - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
    have := Nat.le_of_dvd (by positivity) (hord ▸ orderOf_dvd_of_pow_eq_one hg1)
    omega
  rcases isUnit_iff_eq.1 hu with h | h | h | h <;> rw [h] at hne ⊢
  · simp at hne
  · simp at hne
  · exact I_sq
  · rw [neg_sq, I_sq]

/-- `χ_π` has order `4`. -/
lemma orderOf_quarticMulChar : orderOf (quarticMulChar π hp2) = 4 := by
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := quarticMulChar π hp2) ?_
    (by simpa using quarticMulChar_pow_four hp2)
  · simpa using h
  · intro h
    rw [pow_one] at h
    obtain ⟨g, hg⟩ := exists_quarticMulChar_sq_eq_neg_one hp2
    have := congrArg (fun χ : MulChar (ZMod π.norm.natAbs) ℤ[i] => χ (g : ZMod π.norm.natAbs)) h
    simp only [pow_one, MulChar.pow_apply_coe, MulChar.one_apply_coe] at this
    rw [hg] at this
    have := congrArg Zsqrtd.re this; simp at this

/-! ### `π` divides `J(χ_π, χ_π)` (Exercise 11 of Chapter 4) -/

/-- `∑_{t ∈ F_p} t ^ k (1 - t) ^ k = 0` for `2k < p - 1`. -/
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

/-- `J(χ_π, χ_π) ≡ 0 (mod π)` (proof of Proposition 9.9.4). -/
lemma dvd_jacobiSum_quarticMulChar :
    π ∣ jacobiSum (quarticMulChar π hp2) (quarticMulChar π hp2) := by
  rw [← toZMod_eq_zero_iff hp.out, jacobiSum, map_sum]
  simp_rw [map_mul, toZMod_quarticMulChar]
  refine sum_pow_mul_one_sub_pow _ ?_
  have h4 := four_mul_qexp irreducible_of_fact hp2
  have := qexp_pos hp2
  omega

/-! ### The norm of `J(χ_π, χ_π)` -/

lemma quarticMulChar_inv :
    (quarticMulChar π hp2)⁻¹ = (quarticMulChar π hp2).ringHomComp (starRingEnd ℤ[i]) := by
  refine MulChar.ext fun u => ?_
  rw [MulChar.inv_apply_eq_inv, MulChar.ringHomComp_apply, starRingEnd_apply]
  obtain ⟨w, hw⟩ := isUnit_quarticMulChar hp2 u.ne_zero
  rw [← hw, Ring.inverse_unit]
  exact Units.inv_eq_of_mul_eq_one_right (by rw [hw]; exact unit_mul_star ⟨w, hw⟩)

lemma quarticMulChar_ne_one : quarticMulChar π hp2 ≠ 1 := by
  intro h
  have := orderOf_quarticMulChar hp2
  rw [h, orderOf_one] at this; omega

lemma quarticMulChar_sq_ne_one : quarticMulChar π hp2 ^ 2 ≠ 1 := by
  intro h
  have := orderOf_dvd_of_pow_eq_one h
  rw [orderOf_quarticMulChar hp2] at this; omega

omit hp in
lemma ringHomComp_ringHomComp {R' R'' : Type*} [CommRing R'] [CommRing R'']
    (χ : MulChar (ZMod π.norm.natAbs) ℤ[i]) (f : ℤ[i] →+* R') (g : R' →+* R'') :
    (χ.ringHomComp f).ringHomComp g = χ.ringHomComp (g.comp f) := by
  ext; rfl

/-- `J(χ_π, χ_π)` has norm `p` (the corollary to Theorem 1 of Chapter 8, used in the proof of
Proposition 9.9.4). -/
theorem natAbs_norm_jacobiSum :
    (jacobiSum (quarticMulChar π hp2) (quarticMulChar π hp2)).norm.natAbs = π.norm.natAbs := by
  set χ := quarticMulChar π hp2
  let f : ℤ[i] →+* ℂ := GaussianInt.toComplex
  have hf : Function.Injective f := GaussianInt.toComplex_injective
  have hchar : ringChar ℂ ≠ ringChar (ZMod π.norm.natAbs) := by
    rw [ringChar.eq_zero, ZMod.ringChar_zmod_n]; exact (Fact.out : Nat.Prime _).ne_zero.symm
  have h1 : χ.ringHomComp f ≠ 1 := (MulChar.ringHomComp_ne_one_iff hf).2 (quarticMulChar_ne_one hp2)
  have h2 : χ.ringHomComp f * χ.ringHomComp f ≠ 1 := by
    rw [← MulChar.ringHomComp_mul, MulChar.ringHomComp_ne_one_iff hf, ← sq]
    exact quarticMulChar_sq_ne_one hp2
  have H := jacobiSum_mul_jacobiSum_inv hchar h1 h1 h2
  rw [MulChar.ringHomComp_inv, quarticMulChar_inv, ringHomComp_ringHomComp, jacobiSum_ringHomComp,
    jacobiSum_ringHomComp] at H
  change f _ * (f.comp (starRingEnd ℤ[i])) _ = _ at H
  rw [RingHom.comp_apply, ← map_mul, ZMod.card, ← map_natCast f, starRingEnd_apply,
    ← Zsqrtd.norm_eq_mul_conj] at H
  have H' := hf H
  have : (jacobiSum χ χ).norm = ((π.norm.natAbs : ℕ) : ℤ) :=
    Int.cast_injective (α := ℤ[i]) (by rw [Int.cast_natCast]; exact H')
  rw [this, Int.natAbs_natCast]

lemma isPrimitiveRoot_I : IsPrimitiveRoot I 4 := by
  refine IsPrimitiveRoot.mk_of_lt I (by norm_num) I_pow_four fun l hl hl4 => ?_
  interval_cases l
  · intro h; have := congrArg Zsqrtd.re h; simp at this
  · rw [I_sq]; intro h; have := congrArg Zsqrtd.re h; simp at this
  · intro h; have := congrArg Zsqrtd.im h; simp [pow_succ] at this

/-- **Proposition 9.9.3.** `-χ_π(-1) J(χ_π, χ_π)` is primary. -/
@[kb "irelandrosen1990" "Prop 9.9.3, p. 135"]
theorem isPrimary_neg_mul_jacobiSum :
    IsPrimary (-(quarticMulChar π hp2 (-1)) *
      jacobiSum (quarticMulChar π hp2) (quarticMulChar π hp2)) := by
  set χ := quarticMulChar π hp2
  have h4 : 4 ∣ Fintype.card (ZMod π.norm.natAbs) - 1 := by
    rw [ZMod.card]; exact ⟨qexp π, (four_mul_qexp irreducible_of_fact hp2).symm⟩
  have H := NTKB.Port.one_add_pow_three_dvd_apply_neg_one_mul_jacobiSum_add_one
    (quarticMulChar_pow_four hp2) h4 isPrimitiveRoot_I
  refine ⟨fun hu => ?_, ?_⟩
  · have := isUnit_iff_natAbs_norm.1 hu
    rw [natAbs_norm_mul, natAbs_norm_jacobiSum, isUnit_iff_natAbs_norm.1
      ((isUnit_quarticMulChar hp2 (neg_ne_zero.2 one_ne_zero)).neg)] at this
    exact (Fact.out : Nat.Prime π.norm.natAbs).one_lt.ne' (by simpa using this)
  · unfold IsPrimary'
    rw [show -χ (-1) * jacobiSum χ χ - 1 = -(χ (-1) * jacobiSum χ χ + 1) by ring, dvd_neg]
    exact H

/-- **Proposition 9.9.4.** For a primary irreducible `π` of prime norm,
`-χ_π(-1) J(χ_π, χ_π) = π`. -/
@[kb "irelandrosen1990" "Prop 9.9.4, p. 135"]
theorem neg_mul_jacobiSum_eq (hP : IsPrimary π) :
    -(quarticMulChar π hp2 (-1)) * jacobiSum (quarticMulChar π hp2) (quarticMulChar π hp2) = π := by
  set χ := quarticMulChar π hp2
  obtain ⟨γ, hγ⟩ := dvd_jacobiSum_quarticMulChar hp2
  have hN := natAbs_norm_jacobiSum hp2
  rw [hγ, natAbs_norm_mul] at hN
  have hγu : IsUnit γ := by
    rw [isUnit_iff_natAbs_norm]
    exact (Nat.mul_eq_left (natAbs_norm_pos irreducible_of_fact.ne_zero).ne').1 hN
  have hu : IsUnit (-(χ (-1)) * γ) :=
    ((isUnit_quarticMulChar hp2 (neg_ne_zero.2 one_ne_zero)).neg).mul hγu
  have hprim := (isPrimary_neg_mul_jacobiSum hp2).2
  rw [hγ, show -(χ (-1)) * (π * γ) = (-(χ (-1)) * γ) * π by ring] at hprim ⊢
  have := unit_eq_of_isPrimary' hu isUnit_one hprim (by rw [one_mul]; exact hP.2)
  rw [this, one_mul]

lemma not_dvd_two (hp2 : π.norm.natAbs ≠ 2) : ¬ π ∣ 2 := by
  intro h
  have := norm_dvd_norm h
  have h2' : ((2 : ℤ[i])).norm.natAbs = 2 ^ 2 := by rw [norm_def]; norm_num
  rw [h2'] at this
  have hp' : Nat.Prime π.norm.natAbs := Fact.out
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp' Nat.prime_two).1 (hp'.dvd_of_dvd_pow this))

/-- `χ_π ²` is the Legendre symbol modulo `p`. -/
theorem quarticMulChar_sq_apply (a : ℤ) :
    (quarticMulChar π hp2 ^ 2) a = (legendreSym π.norm.natAbs a : ℤ[i]) := by
  set χ := quarticMulChar π hp2
  have hp' : Nat.Prime π.norm.natAbs := Fact.out
  have hodd : π.norm.natAbs % 2 = 1 := (hp'.eq_two_or_odd).resolve_left hp2
  have h2k : 2 * qexp π = π.norm.natAbs / 2 := by
    have := four_mul_qexp irreducible_of_fact hp2; omega
  by_cases ha : (a : ZMod π.norm.natAbs) = 0
  · rw [ha, MulChar.map_zero, (legendreSym.eq_zero_iff _ _).2 ha]
    simp
  have hu := isUnit_quarticMulChar hp2 ha
  rw [MulChar.pow_apply' _ two_ne_zero]
  have hmod : toZMod hp.out (χ a ^ 2) = toZMod hp.out (legendreSym π.norm.natAbs a : ℤ[i]) := by
    rw [map_pow, toZMod_quarticMulChar, ← pow_mul, mul_comm, h2k, map_intCast, legendreSym.eq_pow]
  rw [toZMod_eq_iff] at hmod
  have hl := legendreSym.eq_one_or_neg_one π.norm.natAbs ha
  have hsq : χ a ^ 2 = 1 ∨ χ a ^ 2 = -1 := by
    rcases isUnit_iff_eq.1 hu with h | h | h | h <;> rw [h] <;> simp [I_sq]
  have h2 := not_dvd_two hp2
  rcases hsq with h | h <;> rcases hl with h' | h' <;> rw [h, h'] at hmod ⊢
  · rfl
  · exfalso; apply h2; convert hmod using 1; norm_num
  · exfalso; apply h2; rw [← dvd_neg]; convert hmod using 1; norm_num
  · rfl

/-! ### Gauss sums -/

section Gauss

variable {R' : Type*} [CommRing R'] [IsDomain R'] (φ : ℤ[i] →+* R')

lemma orderOf_quarticMulChar_ringHomComp (h2 : (2 : R') ≠ 0) :
    orderOf ((quarticMulChar π hp2).ringHomComp φ) = 4 := by
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := (quarticMulChar π hp2).ringHomComp φ) ?_
    (by rw [MulChar.ringHomComp_pow]; simp [quarticMulChar_pow_four hp2])
  · simpa using h
  · intro h
    rw [pow_one, MulChar.ringHomComp_pow] at h
    obtain ⟨g, hg⟩ := exists_quarticMulChar_sq_eq_neg_one hp2
    have := congrArg (fun χ : MulChar (ZMod π.norm.natAbs) R' => χ (g : ZMod π.norm.natAbs)) h
    simp only [MulChar.ringHomComp_apply, MulChar.pow_apply_coe, MulChar.one_apply_coe] at this
    rw [hg, map_neg, map_one] at this
    exact h2 (by linear_combination -this)

/-- **Proposition 9.9.2.** `g(χ_π)⁴ = p J(χ_π, χ_π)²`, for Gauss sums with values in any domain
`R'` with `2 ≠ 0` (through `φ : ℤ[i] → R'`) and a primitive additive character `ψ`. -/
@[kb "irelandrosen1990" "Prop 9.9.2, p. 135"]
theorem gaussSum_pow_four_eq (h2 : (2 : R') ≠ 0) {ψ : AddChar (ZMod π.norm.natAbs) R'}
    (hψ : ψ.IsPrimitive) :
    gaussSum ((quarticMulChar π hp2).ringHomComp φ) ψ ^ 4 =
      π.norm.natAbs * φ (jacobiSum (quarticMulChar π hp2) (quarticMulChar π hp2)) ^ 2 := by
  rw [NTKB.Port.gaussSum_pow_four_eq_card_mul_jacobiSum_sq
    (orderOf_quarticMulChar_ringHomComp hp2 φ h2) hψ, jacobiSum_ringHomComp, ZMod.card]

lemma jacobiSum_quarticMulChar_eq (hP : IsPrimary π) :
    jacobiSum (quarticMulChar π hp2) (quarticMulChar π hp2) =
      -(quarticMulChar π hp2 (-1)) * π := by
  have h := neg_mul_jacobiSum_eq hp2 hP
  have hc := NTKB.Port.MulChar.apply_neg_one_mul_self (quarticMulChar π hp2)
  linear_combination (-(quarticMulChar π hp2 (-1))) * h +
    (-(jacobiSum (quarticMulChar π hp2) (quarticMulChar π hp2))) * hc

/-- **Proposition 9.9.5.** For primary `π` of prime norm, `g(χ_π)⁴ = π³ π̄`. -/
@[kb "irelandrosen1990" "Prop 9.9.5, p. 135"]
theorem gaussSum_pow_four_eq_pow_three_mul_star (hP : IsPrimary π) (h2 : (2 : R') ≠ 0)
    {ψ : AddChar (ZMod π.norm.natAbs) R'} (hψ : ψ.IsPrimitive) :
    gaussSum ((quarticMulChar π hp2).ringHomComp φ) ψ ^ 4 = φ (π ^ 3 * star π) := by
  rw [gaussSum_pow_four_eq hp2 φ h2 hψ, jacobiSum_quarticMulChar_eq hp2 hP]
  have hsq : (-(quarticMulChar π hp2 (-1))) ^ 2 = 1 := by
    rw [neg_sq, sq, NTKB.Port.MulChar.apply_neg_one_mul_self]
  have hN : ((π.norm.natAbs : ℕ) : ℤ[i]) = π * star π := by
    rw [← Int.cast_natCast, natAbs_norm, Zsqrtd.norm_eq_mul_conj]
  rw [← map_natCast φ, ← map_pow, ← map_mul, mul_pow, hsq, one_mul, hN]
  ring_nf

end Gauss

/-- **Proposition 9.9.1.** `J(χ_π, χ_π) = χ_π(-1) J(χ_π, ψ)`, where `ψ = χ_π²` is the Legendre
symbol (`quarticMulChar_sq_apply`). -/
@[kb "irelandrosen1990" "Prop 9.9.1, p. 134"]
theorem jacobiSum_eq_mul_jacobiSum_sq :
    jacobiSum (quarticMulChar π hp2) (quarticMulChar π hp2) =
      quarticMulChar π hp2 (-1) * jacobiSum (quarticMulChar π hp2) (quarticMulChar π hp2 ^ 2) := by
  set χ := quarticMulChar π hp2
  have hchar : ringChar ℂ ≠ ringChar (ZMod π.norm.natAbs) := by
    rw [ringChar.eq_zero, ZMod.ringChar_zmod_n]; exact (Fact.out : Nat.Prime _).ne_zero.symm
  let ψ := AddChar.FiniteField.primitiveChar (ZMod π.norm.natAbs) ℂ hchar
  let φ : ℤ[i] →+* CyclotomicField ψ.n ℂ := (algebraMap ℂ _).comp GaussianInt.toComplex
  have hφ : Function.Injective φ :=
    (algebraMap ℂ _).injective.comp GaussianInt.toComplex_injective
  have h2 : (2 : CyclotomicField ψ.n ℂ) ≠ 0 := two_ne_zero
  have hord := orderOf_quarticMulChar_ringHomComp hp2 φ h2
  have H1 := gaussSum_pow_eq_prod_jacobiSum (χ := χ.ringHomComp φ) (ψ := ψ.char) (by rw [hord]; norm_num) ψ.prim
  rw [hord] at H1
  rw [show Finset.Ico 1 (4 - 1) = {1, 2} by decide, Finset.prod_insert (by decide :
    1 ∉ ({2} : Finset ℕ)), Finset.prod_singleton, pow_one, MulChar.ringHomComp_pow,
    jacobiSum_ringHomComp, jacobiSum_ringHomComp, MulChar.ringHomComp_apply, ZMod.card,
    gaussSum_pow_four_eq hp2 φ h2 ψ.prim] at H1
  have hJ0 : φ (jacobiSum χ χ) ≠ 0 := by
    rw [map_ne_zero_iff _ hφ]
    intro h
    have := natAbs_norm_jacobiSum hp2
    rw [h] at this
    exact (Fact.out : Nat.Prime π.norm.natAbs).ne_zero (by simpa using this.symm)
  have hp0 : ((π.norm.natAbs : ℕ) : CyclotomicField ψ.n ℂ) ≠ 0 := by
    exact_mod_cast (Fact.out : Nat.Prime π.norm.natAbs).ne_zero
  apply hφ
  rw [map_mul]
  apply mul_left_cancel₀ (mul_ne_zero hp0 hJ0)
  linear_combination H1

end Gaussian

end NTKB.IrelandRosen
