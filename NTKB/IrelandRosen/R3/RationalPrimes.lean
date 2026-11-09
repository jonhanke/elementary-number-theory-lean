/-
Ireland–Rosen, Chapter 9, §9: biquadratic reciprocity with a rational prime.
-/
import NTKB.IrelandRosen.R3.JacobiSum

/-!
# Biquadratic reciprocity with a rational prime (Propositions 9.9.6 and 9.9.7)

Let `π` be a primary irreducible of prime norm `p`.

* For a prime `q ≡ 3 (mod 4)`, `χ_π(-q) = χ_q(π)` (Proposition 9.9.6).
* For a prime `q ≡ 1 (mod 4)`, `q ≠ p`, `χ_π(q) = χ_q(π)`, the right side being the generalized
  symbol (Proposition 9.9.7).

The book computes `g(χ_π) ^ q` modulo `q` in the ring of algebraic integers. We take instead a
field `L` of characteristic `q` containing the residue field `ℤ[i]/λ` of a prime `λ ∣ q` and the
`p`-th roots of unity (a cyclotomic extension of `ℤ[i]/λ`), so that congruences modulo `λ` become
equalities in `L`, and use Frobenius (`gaussSum_frob`).
-/

namespace NTKB.IrelandRosen

open Zsqrtd

local notation "ℤ[i]" => GaussianInt

namespace Gaussian

/-! ### A field of characteristic `q` with a primitive additive character of `ZMod p` -/

lemma dvd_natCast_iff_of_dvd {ρ : ℤ[i]} (hρ : Irreducible ρ) {q : ℕ} (hq : q.Prime)
    (hρq : ρ ∣ (q : ℤ[i])) (n : ℕ) : ρ ∣ (n : ℤ[i]) ↔ q ∣ n := by
  constructor
  · intro h
    by_contra hn
    have hcop : IsCoprime (q : ℤ) (n : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hq).2 hn)
    obtain ⟨a, b, hab⟩ := hcop
    have : ρ ∣ (1 : ℤ[i]) := by
      have e : ((a : ℤ[i]) * (q : ℤ[i]) + (b : ℤ[i]) * (n : ℤ[i])) = 1 := by exact_mod_cast hab
      rw [← e]; exact dvd_add (dvd_mul_of_dvd_right hρq _) (dvd_mul_of_dvd_right h _)
    exact hρ.not_isUnit (isUnit_of_dvd_one this)
  · rintro ⟨m, rfl⟩
    rw [Nat.cast_mul]; exact dvd_mul_of_dvd_left hρq _

/-- For a prime `λ ∣ q` of `ℤ[i]` and a prime `p ≠ q`, there is a field `L` of characteristic `q`
with a ring homomorphism `φ : ℤ[i] → L` of kernel `(λ)` and a primitive additive character of
`ZMod p` with values in `L`. -/
theorem exists_field_charP {ρ : ℤ[i]} (hρ : Irreducible ρ) {q : ℕ} (hq : q.Prime)
    (hρq : ρ ∣ (q : ℤ[i])) (p : ℕ) [Fact p.Prime] (hpq : q ≠ p) :
    ∃ (L : Type) (_ : Field L) (_ : CharP L q) (φ : ℤ[i] →+* L) (ψ : AddChar (ZMod p) L),
      ψ.IsPrimitive ∧ ∀ x, φ x = 0 ↔ ρ ∣ x := by
  haveI := isMaximal_span hρ
  letI : Field (ℤ[i] ⧸ Ideal.span {ρ}) := Ideal.Quotient.field _
  haveI : Finite (ℤ[i] ⧸ Ideal.span {ρ}) := Nat.finite_of_card_ne_zero (by
    rw [(card_quotient_of_irreducible hρ).2]; exact (natAbs_norm_pos hρ.ne_zero).ne')
  haveI hK : CharP (ℤ[i] ⧸ Ideal.span {ρ}) q := ⟨fun n => by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {ρ})), Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton, dvd_natCast_iff_of_dvd hρ hq hρq]⟩
  have hchar : ringChar (ℤ[i] ⧸ Ideal.span {ρ}) ≠ ringChar (ZMod p) := by
    rw [ringChar.eq (ℤ[i] ⧸ Ideal.span {ρ}) q, ZMod.ringChar_zmod_n]; exact hpq
  let ψ := AddChar.FiniteField.primitiveChar (ZMod p) (ℤ[i] ⧸ Ideal.span {ρ}) hchar
  refine ⟨CyclotomicField ψ.n (ℤ[i] ⧸ Ideal.span {ρ}), inferInstance, ?_,
    (algebraMap (ℤ[i] ⧸ Ideal.span {ρ}) _).comp (Ideal.Quotient.mk _), ψ.char, ψ.prim, ?_⟩
  · exact charP_of_injective_algebraMap (algebraMap (ℤ[i] ⧸ Ideal.span {ρ}) _).injective q
  · intro x
    have hinj := (algebraMap (ℤ[i] ⧸ Ideal.span {ρ}) (CyclotomicField ψ.n
      (ℤ[i] ⧸ Ideal.span {ρ}))).injective
    rw [RingHom.comp_apply, map_eq_zero_iff _ hinj,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

/-! ### Frobenius -/

section Frobenius

variable {L : Type*} [Field L] (q : ℕ) [Fact q.Prime] [CharP L q]

lemma intCast_pow_char (n : ℤ) : (n : L) ^ q = n := by
  rw [← map_intCast (ZMod.castHom (dvd_refl q) L), ← map_pow, ZMod.pow_card]

/-- For `q ≡ 3 (mod 4)` and `φ : ℤ[i] → L` with `L` of characteristic `q`,
`φ(ᾱ) = φ(α) ^ q` (Exercise 45: `π̄ ≡ π ^ q (mod q)`). -/
lemma map_star_eq_pow (hq3 : q % 4 = 3) (φ : ℤ[i] →+* L) (x : ℤ[i]) :
    φ (star x) = φ x ^ q := by
  have hI : I ^ q = -I := by
    obtain ⟨t, ht⟩ : ∃ t, q = 4 * t + 3 := ⟨q / 4, by omega⟩
    rw [ht, pow_add, pow_mul, I_pow_four, one_pow, one_mul, pow_succ, I_sq]; ring
  conv_rhs => rw [eq_re_add_im x]
  rw [map_add, map_mul, add_pow_char, mul_pow, map_intCast, map_intCast, intCast_pow_char,
    intCast_pow_char, ← map_pow, hI]
  have : star x = (x.re : ℤ[i]) + (x.im : ℤ[i]) * (-I) := by ext <;> simp
  rw [this, map_add, map_mul, map_intCast, map_intCast]

end Frobenius

/-! ### The Gauss sum to the power `q` -/

section GaussPow

variable {π : ℤ[i]} [hp : Fact (Nat.Prime π.norm.natAbs)] (hp2 : π.norm.natAbs ≠ 2)
  {L : Type*} [Field L] (q : ℕ) [Fact q.Prime] [CharP L q] (φ : ℤ[i] →+* L)
  {ψ : AddChar (ZMod π.norm.natAbs) L}

lemma ringHomComp_pow_four : ((quarticMulChar π hp2).ringHomComp φ) ^ 4 = 1 := by
  rw [MulChar.ringHomComp_pow, quarticMulChar_pow_four]; ext; simp

/-- For `q ≡ 1 (mod 4)`, `χ_π(q) g(χ_π) ^ q = g(χ_π)`. -/
lemma gaussSum_pow_char_of_mod_four_eq_one (hq1 : q % 4 = 1) (hpq : q ≠ π.norm.natAbs) :
    φ (quarticChar π q) * gaussSum ((quarticMulChar π hp2).ringHomComp φ) ψ ^ q =
      gaussSum ((quarticMulChar π hp2).ringHomComp φ) ψ := by
  set χ' := (quarticMulChar π hp2).ringHomComp φ
  have hχq : χ' ^ q = χ' := by
    obtain ⟨t, ht⟩ : ∃ t, q = 4 * t + 1 := ⟨q / 4, by omega⟩
    rw [ht, pow_succ, pow_mul, ringHomComp_pow_four, one_pow, one_mul]
  have hqu : IsUnit (q : ZMod π.norm.natAbs) := by
    rw [isUnit_iff_ne_zero, Ne, ZMod.natCast_eq_zero_iff]
    intro h
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp.out (Fact.out : q.Prime)).1 h).symm
  rw [gaussSum_frob, hχq, AddChar.pow_mulShift, ← quarticMulChar_natCast hp2]
  have := gaussSum_mulShift χ' ψ hqu.unit
  rw [IsUnit.unit_spec] at this
  rw [← this, MulChar.ringHomComp_apply]

/-- For `q ≡ 3 (mod 4)`, `g(χ_π) ^ (q + 1) = χ_π(-q) p`. -/
lemma gaussSum_pow_char_succ_of_mod_four_eq_three (hq3 : q % 4 = 3) (hψ : ψ.IsPrimitive) :
    gaussSum ((quarticMulChar π hp2).ringHomComp φ) ψ ^ (q + 1) =
      φ (quarticChar π (-(q : ℤ[i]))) * π.norm.natAbs := by
  set χ' := (quarticMulChar π hp2).ringHomComp φ
  have hpq : q ≠ π.norm.natAbs := by
    have := natAbs_norm_mod_four_eq_one (irreducible_of_fact (π := π)) hp2; omega
  have h4 := ringHomComp_pow_four hp2 φ
  have hχq : χ' ^ q = χ'⁻¹ := by
    obtain ⟨t, ht⟩ : ∃ t, q = 4 * t + 3 := ⟨q / 4, by omega⟩
    rw [ht, pow_add, pow_mul, h4, one_pow, one_mul]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, h4])
  have hqu : IsUnit (q : ZMod π.norm.natAbs) := by
    rw [isUnit_iff_ne_zero, Ne, ZMod.natCast_eq_zero_iff]
    intro h
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp.out (Fact.out : q.Prime)).1 h).symm
  have hχ1 : χ' ≠ 1 := by
    intro h
    have := orderOf_quarticMulChar_ringHomComp hp2 φ (by
      intro h2
      have := (CharP.cast_eq_zero_iff L q 2).1 (by exact_mod_cast h2)
      have := Nat.le_of_dvd (by norm_num) this
      have := (Fact.out : q.Prime).two_le
      interval_cases q <;> simp_all)
    rw [show (quarticMulChar π hp2).ringHomComp φ = 1 from h, orderOf_one] at this; omega
  -- `g(χ') ^ q = gaussSum χ'⁻¹ (mulShift ψ q)`
  have hfrob : gaussSum χ' ψ ^ q = gaussSum χ'⁻¹ (AddChar.mulShift ψ (q : ZMod π.norm.natAbs)) := by
    rw [gaussSum_frob, hχq, AddChar.pow_mulShift]
  have hshift := gaussSum_mulShift χ'⁻¹ ψ hqu.unit
  rw [IsUnit.unit_spec] at hshift
  have hcard := gaussSum_mul_gaussSum_eq_card hχ1 hψ
  rw [gaussSum_inv_right] at hcard
  -- `χ'⁻¹ (a) χ' (a) = 1` for units `a`
  have hinv : ∀ a : (ZMod π.norm.natAbs)ˣ, χ'⁻¹ (a : ZMod π.norm.natAbs) * χ' a = 1 := by
    intro a; rw [← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply_coe]
  have hm1 := hinv (-1)
  have hmq := hinv hqu.unit
  simp only [Units.val_neg, Units.val_one, IsUnit.unit_spec] at hm1 hmq
  rw [ZMod.card] at hcard
  have hval : χ' (-(q : ZMod π.norm.natAbs)) = φ (quarticChar π (-(q : ℤ[i]))) := by
    rw [MulChar.ringHomComp_apply, show -(q : ZMod π.norm.natAbs) = ((-(q : ℤ) : ℤ) :
      ZMod π.norm.natAbs) by push_cast; ring, quarticMulChar_intCast]
    push_cast; rfl
  rw [← hval, show -(q : ZMod π.norm.natAbs) = (-1) * q by ring, map_mul, pow_succ, hfrob]
  linear_combination (χ' (-1) * χ' q) * hcard +
    (χ' (-1) * χ' q * gaussSum χ' ψ * χ'⁻¹ (-1)) * hshift -
    (gaussSum χ'⁻¹ (AddChar.mulShift ψ (q : ZMod π.norm.natAbs)) * gaussSum χ' ψ *
      χ'⁻¹ (q : ZMod π.norm.natAbs) * χ' q) * hm1 -
    (gaussSum χ'⁻¹ (AddChar.mulShift ψ (q : ZMod π.norm.natAbs)) * gaussSum χ' ψ) * hmq

end GaussPow

/-! ### Propositions 9.9.6 and 9.9.7 -/

lemma two_ne_zero_of_charP {L : Type*} [Field L] {q : ℕ} [Fact q.Prime] [CharP L q]
    (hq : q ≠ 2) : (2 : L) ≠ 0 := by
  intro h2
  have := (CharP.cast_eq_zero_iff L q 2).1 (by exact_mod_cast h2)
  exact hq ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this)

lemma not_dvd_of_prime_norm_ne {π ρ : ℤ[i]} (hπ : π.norm.natAbs.Prime) (hρ : Irreducible ρ)
    (hne : ρ.norm.natAbs ≠ π.norm.natAbs) : ¬ ρ ∣ π := by
  intro h
  have := norm_dvd_norm h
  rcases (Nat.dvd_prime hπ).1 this with h1 | h1
  · exact natAbs_norm_ne_one_of_irreducible hρ h1
  · exact hne h1

lemma quarticChar_pow {ρ : ℤ[i]} (hρ : Irreducible ρ) (h2 : ρ.norm.natAbs ≠ 2) (α : ℤ[i])
    (n : ℕ) : quarticChar ρ (α ^ n) = quarticChar ρ α ^ n := by
  induction n with
  | zero => simpa using quarticChar_one hρ h2
  | succ n ih => rw [pow_succ, quarticChar_mul hρ h2, ih, pow_succ]

lemma unit_pow_three {u : ℤ[i]} (hu : IsUnit u) : u ^ 3 = star u := by
  have h4 := unit_pow_four hu
  have hs := unit_mul_star hu
  have hu0 : u ≠ 0 := hu.ne_zero
  apply mul_left_cancel₀ hu0
  rw [hs, ← pow_succ', h4]

/-- **Proposition 9.9.6.** Let `π` be a primary irreducible of prime norm and `q ≡ 3 (mod 4)` a
rational prime. Then `χ_π(-q) = χ_q(π)`. -/
@[kb "irelandrosen1990" "Prop 9.9.6, p. 135"]
theorem quarticChar_natCast_eq_quarticChar_neg {π : ℤ[i]} (hP : IsPrimary π)
    (hpπ : π.norm.natAbs.Prime) {q : ℕ} (hq : q.Prime) (hq3 : q % 4 = 3) :
    quarticChar (q : ℤ[i]) π = quarticChar π (-(q : ℤ[i])) := by
  haveI := Fact.mk hpπ
  haveI := Fact.mk hq
  have hp1 := hP.2.natAbs_norm_mod_four
  have hp2 : π.norm.natAbs ≠ 2 := by omega
  have hqirr : Irreducible (q : ℤ[i]) :=
    (GaussianInt.prime_of_nat_prime_of_mod_four_eq_three q hq3).irreducible
  have hq2 : (q : ℤ[i]).norm.natAbs ≠ 2 := by rw [natAbs_norm_natCast]; nlinarith [hq.two_le]
  have hpq : q ≠ π.norm.natAbs := by omega
  obtain ⟨L, _, _, φ, ψ, hψ, hker⟩ := exists_field_charP hqirr hq dvd_rfl π.norm.natAbs hpq
  have h2L : (2 : L) ≠ 0 := two_ne_zero_of_charP (by omega)
  have h4 := gaussSum_pow_four_eq_pow_three_mul_star hp2 φ hP h2L hψ
  have hq' := gaussSum_pow_char_succ_of_mod_four_eq_three hp2 q φ hq3 hψ
  obtain ⟨m, hm⟩ : ∃ m, q + 1 = 4 * m := ⟨(q + 1) / 4, by omega⟩
  have hqπ : ¬ (q : ℤ[i]) ∣ π := not_dvd_of_prime_norm_ne hpπ hqirr (by
    rw [natAbs_norm_natCast]; intro h; rw [← h, sq] at hpπ
    exact Nat.not_prime_mul hq.one_lt.ne' hq.one_lt.ne' hpπ)
  have hπ0 : φ π ≠ 0 := by rw [Ne, hker]; exact hqπ
  have hstar : φ (star π) = φ π ^ q := map_star_eq_pow q hq3 φ π
  have hN : ((π.norm.natAbs : ℕ) : L) = φ π ^ (q + 1) := by
    rw [← map_natCast φ, ← Int.cast_natCast, natAbs_norm, Zsqrtd.norm_eq_mul_conj, map_mul, hstar,
      pow_succ']
  rw [hm, pow_mul, h4, map_mul, map_pow, hstar, hN] at hq'
  have hexp : (3 + q) * m = (q + 1) + (q - 1) * m := by
    have : 1 ≤ q := hq.one_lt.le
    zify [this] at hm ⊢; linear_combination (-1 : ℤ) * hm
  have key : φ π ^ ((q - 1) * m) = φ (quarticChar π (-(q : ℤ[i]))) := by
    rw [← pow_add, ← pow_mul, hexp, pow_add] at hq'
    exact mul_left_cancel₀ (pow_ne_zero _ hπ0) (hq'.trans (mul_comm _ _))
  have hqexp : qexp (q : ℤ[i]) = (q - 1) * m := by
    rw [qexp, natAbs_norm_natCast]
    have : q ^ 2 - 1 = 4 * ((q - 1) * m) := by
      have : 1 ≤ q := hq.one_lt.le
      zify [this, Nat.one_le_pow 2 q (by omega)] at hm ⊢
      linear_combination (q - 1 : ℤ) * hm
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  obtain ⟨hu, hspec⟩ := quarticChar_spec hqirr hq2 hqπ
  rw [← hker, map_sub, sub_eq_zero, hqexp, map_pow, key] at hspec
  have hπq : ¬ π ∣ -(q : ℤ[i]) := by
    rw [dvd_neg]; intro h
    have := norm_dvd_norm h
    rw [natAbs_norm_natCast] at this
    exact hpq ((Nat.prime_dvd_prime_iff_eq hpπ hq).1 (hpπ.dvd_of_dvd_pow this)).symm
  have hu' := (quarticChar_spec (irreducible_of_prime_norm hpπ) hp2 hπq).1
  refine (eq_of_isUnit_of_dvd_sub hqirr hq2 hu' hu ?_).symm
  rw [← hker, map_sub, hspec, sub_self]

/-- **Proposition 9.9.7.** Let `π` be a primary irreducible of prime norm `p` and `q ≡ 1 (mod 4)`
a rational prime, `q ≠ p`. Then `χ_π(q) = χ_q(π)` (on the right, the generalized symbol: `q` is not
irreducible in `ℤ[i]`). -/
@[kb "irelandrosen1990" "Prop 9.9.7, p. 136"]
theorem quarticChar_natCast_eq_quarticSymbol {π : ℤ[i]} (hP : IsPrimary π)
    (hpπ : π.norm.natAbs.Prime) {q : ℕ} (hq : q.Prime) (hq1 : q % 4 = 1)
    (hpq : q ≠ π.norm.natAbs) :
    quarticChar π (q : ℤ[i]) = quarticSymbol (q : ℤ[i]) π := by
  haveI := Fact.mk hpπ
  haveI := Fact.mk hq
  have hp1 := hP.2.natAbs_norm_mod_four
  have hp2 : π.norm.natAbs ≠ 2 := by omega
  have hπirr := irreducible_of_prime_norm hpπ
  obtain ⟨ρ, hρ, hqρ, -⟩ := exists_irreducible_eq_mul_star hq hq1
  have hρ0 := hρ.ne_zero
  have hs0 : star ρ ≠ 0 := fun h => hρ0 (by simpa using congrArg star h)
  have hNρ : ρ.norm.natAbs = q := by
    have := congrArg (fun x : ℤ[i] => x.norm.natAbs) hqρ
    simp only [natAbs_norm_natCast, natAbs_norm_mul, natAbs_norm_star] at this
    exact Nat.pow_left_injective two_ne_zero (show ρ.norm.natAbs ^ 2 = q ^ 2 by rw [this, sq])
  have hρ2 : ρ.norm.natAbs ≠ 2 := by omega
  have hρq : ρ ∣ (q : ℤ[i]) := ⟨star ρ, hqρ⟩
  obtain ⟨L, _, _, φ, ψ, hψ, hker⟩ := exists_field_charP hρ hq hρq π.norm.natAbs hpq
  have h2L : (2 : L) ≠ 0 := two_ne_zero_of_charP (by omega)
  have h4 := gaussSum_pow_four_eq_pow_three_mul_star hp2 φ hP h2L hψ
  have hq' := gaussSum_pow_char_of_mod_four_eq_one hp2 q φ (ψ := ψ) hq1 hpq
  have hρπ : ¬ ρ ∣ π := not_dvd_of_prime_norm_ne hpπ hρ (by rw [hNρ]; exact hpq)
  have hρπ' : ¬ ρ ∣ star π := by
    intro h; apply hρπ
    have := norm_dvd_norm h
    exact absurd (natAbs_norm_star π ▸ this) (by
      intro h'
      rcases (Nat.dvd_prime hpπ).1 h' with h1 | h1
      · exact natAbs_norm_ne_one_of_irreducible hρ h1
      · exact hpq (hNρ ▸ h1))
  have hρA : ¬ ρ ∣ π ^ 3 * star π := by
    intro h
    rcases hρ.prime.dvd_or_dvd h with h | h
    · exact hρπ (hρ.prime.dvd_of_dvd_pow h)
    · exact hρπ' h
  have hg0 : gaussSum ((quarticMulChar π hp2).ringHomComp φ) ψ ≠ 0 := by
    intro h; rw [h, zero_pow (by norm_num)] at h4
    exact hρA ((hker _).1 h4.symm)
  -- `χ_π(q) g ^ (q - 1) = 1` and `g ^ (q - 1) = (π³ π̄) ^ ((q - 1) / 4)`
  obtain ⟨t, ht⟩ : ∃ t, q = 4 * t + 1 := ⟨q / 4, by omega⟩
  have hqexp : qexp ρ = t := by rw [qexp, hNρ, ht]; omega
  have hgq : ∀ x : L, x ^ q = (x ^ 4) ^ t * x := fun x => by rw [← pow_mul, ← pow_succ, ← ht]
  rw [hgq, h4, ← mul_assoc] at hq'
  have h1 : φ (quarticChar π q) * φ (π ^ 3 * star π) ^ t = 1 :=
    mul_right_cancel₀ hg0 (by rw [hq', one_mul])
  obtain ⟨hu, hspec⟩ := quarticChar_spec hρ hρ2 hρA
  rw [← hker, map_sub, sub_eq_zero, hqexp, map_pow] at hspec
  rw [hspec, ← map_mul] at h1
  have hπq : ¬ π ∣ (q : ℤ[i]) := by
    intro h
    have := norm_dvd_norm h
    rw [natAbs_norm_natCast] at this
    exact hpq ((Nat.prime_dvd_prime_iff_eq hpπ hq).1 (hpπ.dvd_of_dvd_pow this)).symm
  have hu' := (quarticChar_spec hπirr hp2 hπq).1
  have hprod : quarticChar π q * quarticChar ρ (π ^ 3 * star π) = 1 := by
    refine eq_of_isUnit_of_dvd_sub hρ hρ2 (hu'.mul hu) isUnit_one ?_
    rw [← hker, map_sub, h1, map_one, sub_self]
  -- so `χ_ρ(π)³ χ_ρ(π̄) = conj χ_π(q)`
  have hstar : quarticChar ρ (π ^ 3 * star π) = star (quarticChar π q) := by
    apply mul_left_cancel₀ hu'.ne_zero
    rw [hprod, unit_mul_star hu']
  rw [quarticChar_mul hρ hρ2, quarticChar_pow hρ hρ2,
    unit_pow_three (quarticChar_spec hρ hρ2 hρπ).1] at hstar
  have hconj : quarticChar ρ (star π) = star (quarticChar (star ρ) π) := by
    have := quarticChar_star (irreducible_star hρ) (by rwa [natAbs_norm_star]) π
    rwa [star_star] at this
  rw [hconj, ← star_mul'] at hstar
  have hfin := star_injective hstar
  rw [show quarticSymbol (q : ℤ[i]) π = quarticSymbol (ρ * star ρ) π by rw [hqρ],
    quarticSymbol_mul_left hρ0 hs0, quarticSymbol_of_irreducible hρ,
    quarticSymbol_of_irreducible (irreducible_star hρ)]
  exact hfin.symm

end Gaussian

end NTKB.IrelandRosen
