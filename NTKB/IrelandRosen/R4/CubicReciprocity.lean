/-
Ireland–Rosen, Chapter 9, §3, §4 and §6: the law of cubic reciprocity, its supplement, and the
cubic character of 2.
-/
import NTKB.IrelandRosen.R4.CubicJacobi

/-!
# The law of cubic reciprocity (Ireland–Rosen, Chapter 9)

* `cubicChar_natCast_mul_eq_sq` (the computation of §4): for a primary prime `π` of prime norm
  `p` and a prime `ρ` with `ρ ∤ 3p`, `χ_ρ(pπ) = χ_π(N ρ)²`. The book raises `g(χ_π)³ = pπ` to the
  power `(N ρ - 1)/3` and reads it modulo `ρ` in the ring of algebraic integers; as for biquadratic
  reciprocity (`NTKB/IrelandRosen/R3/RationalPrimes.lean`) we take the Gauss sum in a field `L` of
  characteristic `ℓ` (the rational prime below `ρ`) containing `ℤ[ω]/ρ` and the `p`-th roots of
  unity, so that congruences modulo `ρ` become equalities in `L`, and use Frobenius
  (`gaussSum_frob`): `g ^ (N ρ) = χ_π(N ρ)⁻¹ g`.
* `cubic_reciprocity` (**Theorem 1**): for primary primes `π₁, π₂` with `N π₁ ≠ N π₂`,
  `χ_π₁(π₂) = χ_π₂(π₁)`. The three cases of remark (a): two rational primes (the corollary to
  Proposition 9.3.4), a rational and a complex prime (the computation with `ρ = q`,
  `N ρ = q²`), two complex primes (the computation applied twice, then the cube roots of unity
  `χ_π₂(p₁)`, `χ_π₁(p₂)` are eliminated; the book eliminates them through `χ_π̄₁(p₂) = χ_π₁(p₂)`,
  which comes to the same).
* `cubicChar_natCast_one_sub_omega` (**Theorem 1'**, the case the book proves): for a rational
  prime `q = 3m - 1`, `χ_q(1 - ω) = ω^{2m}`.
* `exists_cube_eq_two_iff_dvd_sub_one` (**Proposition 9.6.1**) and `exists_cube_eq_two_iff`
  (**Proposition 9.6.2**): for `p ≡ 1 (mod 3)`, `x³ ≡ 2 (mod p)` is solvable iff
  `p = C² + 27D²`.
-/

namespace NTKB.IrelandRosen

open NTKB.HardyWright QuadraticAlgebra

local notation "ℤ[ω]" => NTKB.HardyWright.ZRho

namespace Eisenstein

set_option linter.style.haveILetI false

/-! ### A field of characteristic `ℓ` with a primitive additive character of `ZMod p` -/

lemma dvd_natCast_iff_of_dvd {ρ : ℤ[ω]} (hρ : Prime ρ) {q : ℕ} (hq : q.Prime)
    (hρq : ρ ∣ (q : ℤ[ω])) (n : ℕ) : ρ ∣ (n : ℤ[ω]) ↔ q ∣ n := by
  constructor
  · intro h
    by_contra hn
    have hcop : IsCoprime (q : ℤ) (n : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hq).2 hn)
    obtain ⟨a, b, hab⟩ := hcop
    have : ρ ∣ (1 : ℤ[ω]) := by
      have e : ((a : ℤ[ω]) * (q : ℤ[ω]) + (b : ℤ[ω]) * (n : ℤ[ω])) = 1 := by exact_mod_cast hab
      rw [← e]; exact dvd_add (dvd_mul_of_dvd_right hρq _) (dvd_mul_of_dvd_right h _)
    exact hρ.not_isUnit (isUnit_of_dvd_one this)
  · rintro ⟨m, rfl⟩
    rw [Nat.cast_mul]; exact dvd_mul_of_dvd_left hρq _

/-- For a prime `ρ ∣ q` of `ℤ[ω]` and a prime `p ≠ q`, there is a field `L` of characteristic `q`
with a ring homomorphism `φ : ℤ[ω] → L` of kernel `(ρ)` and a primitive additive character of
`ZMod p` with values in `L`. -/
theorem exists_field_charP {ρ : ℤ[ω]} (hρ : Prime ρ) {q : ℕ} (hq : q.Prime)
    (hρq : ρ ∣ (q : ℤ[ω])) (p : ℕ) [Fact p.Prime] (hpq : q ≠ p) :
    ∃ (L : Type) (_ : Field L) (_ : CharP L q) (φ : ℤ[ω] →+* L) (ψ : AddChar (ZMod p) L),
      ψ.IsPrimitive ∧ ∀ x, φ x = 0 ↔ ρ ∣ x := by
  obtain ⟨hmax, hcard⟩ := card_quotient hρ
  letI : Field (ℤ[ω] ⧸ Ideal.span {ρ}) := Ideal.Quotient.field _
  haveI : Finite (ℤ[ω] ⧸ Ideal.span {ρ}) := Nat.finite_of_card_ne_zero (by
    rw [hcard]; intro h0
    rw [Int.natAbs_eq_zero] at h0
    exact hρ.ne_zero (qa_norm_eq_zero h0))
  haveI hK : CharP (ℤ[ω] ⧸ Ideal.span {ρ}) q := ⟨fun n => by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {ρ})), Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton, dvd_natCast_iff_of_dvd hρ hq hρq]⟩
  have hchar : ringChar (ℤ[ω] ⧸ Ideal.span {ρ}) ≠ ringChar (ZMod p) := by
    rw [ringChar.eq (ℤ[ω] ⧸ Ideal.span {ρ}) q, ZMod.ringChar_zmod_n]; exact hpq
  let ψ := AddChar.FiniteField.primitiveChar (ZMod p) (ℤ[ω] ⧸ Ideal.span {ρ}) hchar
  refine ⟨CyclotomicField ψ.n (ℤ[ω] ⧸ Ideal.span {ρ}), inferInstance, ?_,
    (algebraMap (ℤ[ω] ⧸ Ideal.span {ρ}) _).comp (Ideal.Quotient.mk _), ψ.char, ψ.prim, ?_⟩
  · exact charP_of_injective_algebraMap (algebraMap (ℤ[ω] ⧸ Ideal.span {ρ}) _).injective q
  · intro x
    have hinj := (algebraMap (ℤ[ω] ⧸ Ideal.span {ρ}) (CyclotomicField ψ.n
      (ℤ[ω] ⧸ Ideal.span {ρ}))).injective
    rw [RingHom.comp_apply, map_eq_zero_iff _ hinj,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

/-- Iterated Frobenius: `g(χ, ψ) ^ (ℓ ^ n) = g(χ ^ (ℓ ^ n), ψ ^ (ℓ ^ n))` in characteristic `ℓ`. -/
lemma gaussSum_pow_char_pow {F : Type*} [Field F] [Fintype F] {L : Type*} [CommRing L]
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP L ℓ] (χ : MulChar F L) (ψ : AddChar F L) (n : ℕ) :
    gaussSum χ ψ ^ (ℓ ^ n) = gaussSum (χ ^ (ℓ ^ n)) (ψ ^ (ℓ ^ n)) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_mul, ih, gaussSum_frob, ← pow_mul, ← pow_mul]

/-- **The computation of §4.** For a primary prime `π` of prime norm `p` and a prime `ρ` with
`N ρ ≠ 3` and `ρ ∤ p`: `χ_ρ(pπ) = χ_π(N ρ)²`. -/
@[kb "irelandrosen1990" "Ch. 9, §4, proof of Theorem 1, p. 127"]
theorem cubicChar_natCast_mul_eq_sq {π : ℤ[ω]} (hp : (norm π).natAbs.Prime) (hP : IsPrimary π)
    {ρ : ℤ[ω]} (hρ : Prime ρ) (hρ3 : (norm ρ).natAbs ≠ 3)
    (hρp : ¬ ρ ∣ ((norm π).natAbs : ℤ[ω])) :
    cubicChar ρ (((norm π).natAbs : ℤ[ω]) * π) = cubicChar π ((norm ρ).natAbs : ℤ[ω]) ^ 2 := by
  haveI := Fact.mk hp
  have hπ : Prime π := prime_of_natAbs_norm_prime hp
  have h3 : (norm π).natAbs ≠ 3 :=
    (natAbs_norm_ne_three_iff hπ).2 (hP.not_dvd_three hπ dvd_rfl)
  set p := (norm π).natAbs with hpdef
  set N := (norm ρ).natAbs with hNdef
  obtain ⟨ℓ, hℓ, hρℓ, hNcases⟩ := prime_natAbs_norm_cases hρ
  obtain ⟨k, hk⟩ : ∃ k, N = ℓ ^ k := by
    rcases hNcases with h | ⟨h, -⟩
    · exact ⟨1, by rw [pow_one]; exact h⟩
    · exact ⟨2, h⟩
  haveI := Fact.mk hℓ
  have hℓp : ℓ ≠ p := by
    rintro rfl; exact hρp hρℓ
  obtain ⟨L, _, _, φ, ψ, hψ, hker⟩ := exists_field_charP hρ hℓ hρℓ p hℓp
  have hρ3' : ¬ ρ ∣ 3 := (natAbs_norm_ne_three_iff hρ).1 hρ3
  have h3L : (3 : L) ≠ 0 := by
    intro h; apply hρ3'; rw [← hker, map_ofNat]; exact h
  set χ' := (cubicMulChar π h3).ringHomComp φ with hχ'
  have hg3 := gaussSum_cubicMulChar_pow_three h3 hP φ h3L hψ
  rw [← hχ'] at hg3
  have hχ3 : χ' ^ 3 = 1 := by
    rw [hχ', MulChar.ringHomComp_pow, ← orderOf_cubicMulChar h3, pow_orderOf_eq_one]
    ext; simp
  have hNmod : N % 3 = 1 := natAbs_norm_mod_three hρ hρ3
  have hχN : χ' ^ (ℓ ^ k) = χ' := by
    obtain ⟨t, ht⟩ : ∃ t, ℓ ^ k = 3 * t + 1 := ⟨ℓ ^ k / 3, by omega⟩
    rw [ht, pow_succ, pow_mul, hχ3, one_pow, one_mul]
  have hpN : ¬ p ∣ N := by
    intro h
    rw [hk] at h
    exact hℓp ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow h)).symm
  have hNu : IsUnit (N : ZMod p) := by
    rw [isUnit_iff_ne_zero, Ne, ZMod.natCast_eq_zero_iff]; exact hpN
  -- Frobenius: `g ^ N = χ'⁻¹(N) g`
  have hfrob : gaussSum χ' ψ ^ N = χ'⁻¹ (N : ZMod p) * gaussSum χ' ψ := by
    have h1 := gaussSum_pow_char_pow ℓ χ' ψ k
    rw [hχN, AddChar.pow_mulShift, ← hk] at h1
    have h2 := gaussSum_mulShift_eq χ' ψ hNu.unit
    rw [IsUnit.unit_spec] at h2
    rw [h1]; exact_mod_cast h2
  -- `χ'⁻¹(N) = φ(χ_π(N))²`
  have hinv : χ'⁻¹ = χ' ^ 2 := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_succ', hχ3]
  have hval : χ'⁻¹ (N : ZMod p) = φ (cubicChar π (N : ℤ[ω]) ^ 2) := by
    rw [hinv, MulChar.pow_apply' _ two_ne_zero, hχ', MulChar.ringHomComp_apply,
      cubicMulChar_natCast, map_pow]
  -- `ρ ∤ pπ`
  have hπp : π ∣ (p : ℤ[ω]) := qa_dvd_natAbs_norm π
  have hρπ : ¬ ρ ∣ π := fun h => hρp (h.trans hπp)
  have hρA : ¬ ρ ∣ (p : ℤ[ω]) * π := fun h =>
    (hρ.dvd_or_dvd h).elim hρp hρπ
  have hg0 : gaussSum χ' ψ ≠ 0 := by
    intro h
    rw [h, zero_pow (by norm_num), ← map_natCast φ, ← map_mul] at hg3
    exact hρA ((hker _).1 hg3.symm)
  -- `g ^ (N - 1) = (pπ) ^ ((N - 1)/3)`
  have hN1 : 1 ≤ N := by omega
  have hc := three_mul_cexp hρ hρ3
  have key : φ (((p : ℤ[ω]) * π) ^ cexp ρ) = φ (cubicChar π (N : ℤ[ω]) ^ 2) := by
    rw [map_pow, map_mul, map_natCast, ← hg3, ← pow_mul, hc, ← hval]
    apply mul_right_cancel₀ hg0
    rw [← pow_succ, Nat.sub_add_cancel hN1, hfrob]
  obtain ⟨hu, hspec⟩ := cubicChar_spec hρ hρ3 hρA
  have hπN : ¬ π ∣ (N : ℤ[ω]) := by
    intro h
    obtain ⟨c, hc'⟩ := h
    have := congrArg (fun x : ℤ[ω] => (norm x).natAbs) hc'
    simp only [map_mul, Int.natAbs_mul, QuadraticAlgebra.norm_natCast, Int.natAbs_pow,
      Int.natAbs_natCast] at this
    exact hpN (hp.dvd_of_dvd_pow ⟨(norm c).natAbs, this⟩)
  have hv := (cubicChar_spec hπ h3 hπN).1
  refine eq_of_pow_three_eq_one_of_dvd_sub hρ hρ3 hu (by rw [← pow_mul, mul_comm, pow_mul, hv,
    one_pow]) ?_
  rw [← hker, map_sub, ← key, sub_eq_zero]
  rw [← hker, map_sub, sub_eq_zero] at hspec
  exact hspec.symm

/-- A primary prime is a rational prime `q ≡ 2 (mod 3)` or has prime norm. -/
lemma IsPrimary.cases {π : ℤ[ω]} (hπ : Prime π) (hP : IsPrimary π) :
    (∃ q : ℕ, q.Prime ∧ q % 3 = 2 ∧ π = q) ∨ (norm π).natAbs.Prime := by
  rcases rho_prime_iff.1 hπ with h | ⟨q, hq, hq3, h⟩ | ⟨p, hp, -, h⟩
  · exfalso
    apply hP.not_dvd_three hπ dvd_rfl
    exact h.dvd.trans ⟨_, three_eq_lam⟩
  · left
    refine ⟨q, hq, hq3, ?_⟩
    obtain ⟨u, hu⟩ := h
    have hq' : Prime (q : ℤ[ω]) := prime_natCast_of_mod_three_eq_two hq hq3
    have hq3' : (norm (q : ℤ[ω])).natAbs ≠ 3 := natAbs_norm_natCast_ne_three hq
    obtain ⟨v, -, hv⟩ := existsUnique_isPrimary_unit_mul hq' hq3'
    have h1 : IsPrimary (((1 : ℤ[ω]ˣ) : ℤ[ω]) * q) := by
      rw [Units.val_one, one_mul, ← Int.cast_natCast, isPrimary_intCast_iff]; omega
    have h2 : IsPrimary (((u⁻¹ : ℤ[ω]ˣ) : ℤ[ω]) * q) := by
      rw [← hu, mul_comm, mul_assoc, Units.mul_inv, mul_one]; exact hP
    have := (hv 1 h1).trans (hv u⁻¹ h2).symm
    rw [← hu, ← inv_inv u, ← this, inv_one, Units.val_one, mul_one]
  · right
    rw [h, Int.natAbs_natCast]; exact hp

/-- Theorem 1 for a rational prime `q ≡ 2 (mod 3)` and a primary prime `π` of prime norm. -/
theorem cubic_reciprocity_natCast {q : ℕ} (hq : q.Prime) (hq3 : q % 3 = 2) {π : ℤ[ω]}
    (hp : (norm π).natAbs.Prime) (hP : IsPrimary π) (hN : q ^ 2 ≠ (norm π).natAbs) :
    cubicChar (q : ℤ[ω]) π = cubicChar π (q : ℤ[ω]) := by
  have hπ : Prime π := prime_of_natAbs_norm_prime hp
  have h3 : (norm π).natAbs ≠ 3 :=
    (natAbs_norm_ne_three_iff hπ).2 (hP.not_dvd_three hπ dvd_rfl)
  have hp3 := natAbs_norm_mod_three hπ h3
  have hqp : q ≠ (norm π).natAbs := by rintro h; omega
  have hq' : Prime (q : ℤ[ω]) := prime_natCast_of_mod_three_eq_two hq hq3
  have hq3' : (norm (q : ℤ[ω])).natAbs ≠ 3 := natAbs_norm_natCast_ne_three hq
  have hqZ : ¬ (q : ℤ) ∣ ((norm π).natAbs : ℤ) := fun h =>
    hqp ((Nat.prime_dvd_prime_iff_eq hq hp).1 (Int.natCast_dvd_natCast.1 h))
  have hρp : ¬ (q : ℤ[ω]) ∣ ((norm π).natAbs : ℤ[ω]) := by
    intro h
    have := natAbs_norm_dvd h
    rw [natAbs_norm_natCast, natAbs_norm_natCast] at this
    exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).1 ((Nat.pow_dvd_pow_iff two_ne_zero).1 this))
  have k := cubicChar_natCast_mul_eq_sq hp hP hq' hq3' hρp
  rw [cubicChar_mul hq' hq3', natAbs_norm_natCast, Nat.cast_pow, cubicChar_pow hπ h3] at k
  have hc : cubicChar (q : ℤ[ω]) ((norm π).natAbs : ℤ[ω]) = 1 := by
    rw [← Int.cast_natCast]; exact cubicChar_natCast_intCast hq hq3 hqZ
  rw [hc, one_mul] at k
  have hπq : ¬ π ∣ (q : ℤ[ω]) := by
    intro h
    have := natAbs_norm_dvd h
    rw [natAbs_norm_natCast] at this
    exact hqp ((Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow this)).symm
  have hv := (cubicChar_spec hπ h3 hπq).1
  rw [k]
  linear_combination cubicChar π (q : ℤ[ω]) * hv

/-- **Theorem 1 (the law of cubic reciprocity).** Let `π₁` and `π₂` be primary primes of `ℤ[ω]`
with `N π₁ ≠ N π₂` (a primary prime has norm `≠ 3`). Then `χ_π₁(π₂) = χ_π₂(π₁)`. -/
@[kb "irelandrosen1990" "Ch. 9, §3, Theorem 1 (cubic reciprocity), p. 125"]
theorem cubic_reciprocity {π₁ π₂ : ℤ[ω]} (h₁ : Prime π₁) (h₂ : Prime π₂) (hP₁ : IsPrimary π₁)
    (hP₂ : IsPrimary π₂) (hN : (norm π₁).natAbs ≠ (norm π₂).natAbs) :
    cubicChar π₁ π₂ = cubicChar π₂ π₁ := by
  rcases IsPrimary.cases h₁ hP₁ with ⟨q₁, hq₁, hq₁3, rfl⟩ | hp₁ <;>
  rcases IsPrimary.cases h₂ hP₂ with ⟨q₂, hq₂, hq₂3, rfl⟩ | hp₂
  · -- two rational primes
    have hne : q₁ ≠ q₂ := by rintro rfl; exact hN rfl
    have c₁ := cubicChar_natCast_intCast hq₁ hq₁3 (n := (q₂ : ℤ)) (fun h => hne
      ((Nat.prime_dvd_prime_iff_eq hq₁ hq₂).1 (Int.natCast_dvd_natCast.1 h)))
    have c₂ := cubicChar_natCast_intCast hq₂ hq₂3 (n := (q₁ : ℤ)) (fun h => hne
      ((Nat.prime_dvd_prime_iff_eq hq₂ hq₁).1 (Int.natCast_dvd_natCast.1 h)).symm)
    rw [Int.cast_natCast] at c₁ c₂
    rw [c₁, c₂]
  · exact cubic_reciprocity_natCast hq₁ hq₁3 hp₂ hP₂ (by
      rw [natAbs_norm_natCast] at hN; exact hN)
  · exact (cubic_reciprocity_natCast hq₂ hq₂3 hp₁ hP₁ (by
      rw [natAbs_norm_natCast] at hN; exact hN.symm)).symm
  · -- two complex primes
    have hπ₁3 := (natAbs_norm_ne_three_iff h₁).2 (hP₁.not_dvd_three h₁ dvd_rfl)
    have hπ₂3 := (natAbs_norm_ne_three_iff h₂).2 (hP₂.not_dvd_three h₂ dvd_rfl)
    have hnd : ∀ {π ρ : ℤ[ω]}, (norm π).natAbs.Prime → (norm ρ).natAbs.Prime →
        (norm π).natAbs ≠ (norm ρ).natAbs → ¬ ρ ∣ ((norm π).natAbs : ℤ[ω]) := by
      intro π ρ hπ hρ hne h
      have := natAbs_norm_dvd h
      rw [natAbs_norm_natCast] at this
      exact hne ((Nat.prime_dvd_prime_iff_eq hρ hπ).1 (hρ.dvd_of_dvd_pow this)).symm
    have k₁ := cubicChar_natCast_mul_eq_sq hp₁ hP₁ h₂ hπ₂3 (hnd hp₁ hp₂ hN)
    have k₂ := cubicChar_natCast_mul_eq_sq hp₂ hP₂ h₁ hπ₁3 (hnd hp₂ hp₁ (Ne.symm hN))
    rw [cubicChar_mul h₂ hπ₂3] at k₁
    rw [cubicChar_mul h₁ hπ₁3] at k₂
    have ha := (cubicChar_spec h₂ hπ₂3 (hnd hp₁ hp₂ hN)).1
    have hb := (cubicChar_spec h₁ hπ₁3 (hnd hp₂ hp₁ (Ne.symm hN))).1
    linear_combination (-cubicChar π₁ π₂) * hb + cubicChar π₂ π₁ * ha +
      cubicChar π₁ ((norm π₂).natAbs : ℤ[ω]) ^ 2 * k₂ -
      cubicChar π₂ ((norm π₁).natAbs : ℤ[ω]) ^ 2 * k₁

/-- **Theorem 1' (supplement to cubic reciprocity), the case of a rational prime.** For a rational
prime `q ≡ 2 (mod 3)`, `q = 3m - 1`: `χ_q(1 - ω) = ω^{2m}`. -/
@[kb "irelandrosen1990" "Ch. 9, §3, Theorem 1', p. 125"]
theorem cubicChar_natCast_one_sub_omega {q : ℕ} (hq : q.Prime) (hq3 : q % 3 = 2) :
    cubicChar q (1 - omega) = omega ^ (2 * ((q + 1) / 3)) := by
  have hq' : Prime (q : ℤ[ω]) := prime_natCast_of_mod_three_eq_two hq hq3
  have hq3' : (norm (q : ℤ[ω])).natAbs ≠ 3 := natAbs_norm_natCast_ne_three hq
  obtain ⟨m, hm⟩ : ∃ m, q + 1 = 3 * m := ⟨(q + 1) / 3, by omega⟩
  have hm1 : 1 ≤ m := by have := hq.two_le; omega
  rw [hm, Nat.mul_div_cancel_left _ (by norm_num)]
  -- `(1 - ω)² = -3ω`
  have hsq : (1 - omega) ^ 2 = ((-3 : ℤ) : ℤ[ω]) * omega := by
    have := omega_sq; push_cast; linear_combination this
  have h3 : ¬ (q : ℤ) ∣ -3 := by
    rw [Int.dvd_neg]; intro h
    have := Int.le_of_dvd (by norm_num) h
    have h' : q ∣ 3 := by exact_mod_cast h
    have := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 h'
    omega
  have key : cubicChar q (1 - omega) ^ 2 = omega ^ cexp q := by
    rw [← cubicChar_pow hq' hq3', hsq, cubicChar_mul hq' hq3',
      cubicChar_natCast_intCast hq hq3 h3, one_mul, cubicChar_omega hq' hq3']
  have hnd : ¬ (q : ℤ[ω]) ∣ 1 - omega := by
    intro h
    have := natAbs_norm_dvd h
    rw [natAbs_norm_natCast, show (1 - omega : ℤ[ω]) = lamRho from rfl, rho_natAbs_norm_lam] at this
    have := Nat.le_of_dvd (by norm_num) this
    have := hq.two_le
    nlinarith
  have hv := (cubicChar_spec hq' hq3' hnd).1
  have hcexp : cexp (q : ℤ[ω]) = 3 * m ^ 2 - 2 * m := by
    rw [cexp, natAbs_norm_natCast]
    have hq1 : q = 3 * m - 1 := by omega
    subst hq1
    have : (3 * m - 1) ^ 2 - 1 = 3 * (3 * m ^ 2 - 2 * m) := by
      zify [show 1 ≤ 3 * m by omega, show 2 * m ≤ 3 * m ^ 2 by nlinarith,
        Nat.one_le_pow 2 (3 * m - 1) (by omega)]
      push_cast [show 1 ≤ 3 * m by omega]; ring
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  have hexp : 2 * cexp (q : ℤ[ω]) = 2 * m + 3 * (2 * m ^ 2 - 2 * m) := by
    rw [hcexp]
    zify [show 2 * m ≤ 3 * m ^ 2 by nlinarith, show 2 * m ≤ 2 * m ^ 2 by nlinarith]
    ring
  calc cubicChar q (1 - omega) = (cubicChar q (1 - omega) ^ 2) ^ 2 := by
        linear_combination (-cubicChar q (1 - omega)) * hv
    _ = omega ^ (2 * m) := by
        rw [key, ← pow_mul, mul_comm, hexp, pow_add, pow_mul omega 3, omega_cube, one_pow, mul_one]

/-- **Proposition 9.6.1.** For a primary prime `π` of prime norm, `x³ ≡ 2 (mod π)` is solvable
iff `π ≡ 1 (mod 2)`. -/
@[kb "irelandrosen1990" "Prop 9.6.1, p. 130"]
theorem exists_cube_eq_two_iff_dvd_sub_one {π : ℤ[ω]} (hp : (norm π).natAbs.Prime)
    (hP : IsPrimary π) : (∃ x : ℤ[ω], π ∣ x ^ 3 - 2) ↔ (2 : ℤ[ω]) ∣ π - 1 := by
  have hπ : Prime π := prime_of_natAbs_norm_prime hp
  have h3 : (norm π).natAbs ≠ 3 :=
    (natAbs_norm_ne_three_iff hπ).2 (hP.not_dvd_three hπ dvd_rfl)
  have hp3 := natAbs_norm_mod_three hπ h3
  have h2 : Prime ((2 : ℕ) : ℤ[ω]) := prime_natCast_of_mod_three_eq_two Nat.prime_two (by norm_num)
  have h23 : (norm ((2 : ℕ) : ℤ[ω])).natAbs ≠ 3 := natAbs_norm_natCast_ne_three Nat.prime_two
  have hπ2 : ¬ π ∣ ((2 : ℕ) : ℤ[ω]) := by
    intro h
    have := natAbs_norm_dvd h
    rw [natAbs_norm_natCast] at this
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow this)
    omega
  have h2π : ¬ ((2 : ℕ) : ℤ[ω]) ∣ π := by
    intro h
    have := natAbs_norm_dvd h
    rw [natAbs_norm_natCast] at this
    rcases hp.eq_one_or_self_of_dvd _ this with h4 | h4
    · norm_num at h4
    · rw [← h4] at hp; norm_num at hp
  -- reciprocity with the rational prime `2`
  have hrec := cubic_reciprocity_natCast Nat.prime_two (by norm_num) hp hP (by
    intro h; rw [← h] at hp; norm_num at hp)
  have e2 : ((2 : ℕ) : ℤ[ω]) = 2 := by norm_num
  rw [← e2, ← cubicChar_eq_one_iff hπ h3 hπ2, ← hrec]
  have hc : cexp ((2 : ℕ) : ℤ[ω]) = 1 := by rw [cexp, natAbs_norm_natCast]; norm_num
  constructor
  · intro h1
    have := (cubicChar_spec h2 h23 h2π).2
    rwa [hc, pow_one, h1, e2] at this
  · intro h
    exact cubicChar_eq_of_dvd h2 h23 h2π (one_pow 3) (by rw [hc, pow_one, e2]; exact h)

/-- **Proposition 9.6.2.** For a prime `p ≡ 1 (mod 3)`, `x³ ≡ 2 (mod p)` is solvable iff
`p = C² + 27D²` for some integers `C, D`. -/
@[kb "irelandrosen1990" "Prop 9.6.2, p. 130"]
theorem exists_cube_eq_two_iff {p : ℕ} (hp : p.Prime) (hp3 : p % 3 = 1) :
    (∃ x : ZMod p, x ^ 3 = 2) ↔ ∃ C D : ℤ, (p : ℤ) = C ^ 2 + 27 * D ^ 2 := by
  -- `p = π π̄` with `π` primary
  obtain ⟨π₀, hπ₀, hpπ, -⟩ := exists_prime_eq_mul_star hp hp3
  have hN₀ : (norm π₀).natAbs = p := by
    have := congrArg (fun x : ℤ[ω] => (norm x).natAbs) hpπ
    simp only [natAbs_norm_natCast, map_mul, Int.natAbs_mul, natAbs_norm_star] at this
    exact Nat.pow_left_injective two_ne_zero (show (norm π₀).natAbs ^ 2 = p ^ 2 by rw [sq]; linarith)
  obtain ⟨u, hu, -⟩ := existsUnique_isPrimary_unit_mul hπ₀ (by rw [hN₀]; omega)
  set π := (u : ℤ[ω]) * π₀ with hπdef
  have hN : (norm π).natAbs = p := by
    rw [hπdef, map_mul, Int.natAbs_mul, qa_norm_unit, one_mul, hN₀]
  subst hN
  have hp' := hp
  haveI : NeZero (norm π).natAbs := ⟨hp'.ne_zero⟩
  -- solvability modulo `p` is solvability modulo `π`
  have hsolv : (∃ x : ZMod (norm π).natAbs, x ^ 3 = 2) ↔ ∃ y : ℤ[ω], π ∣ y ^ 3 - 2 := by
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨(x.val : ℤ[ω]), (toZMod_eq_zero_iff hp' _).1 ?_⟩
      rw [map_sub, map_pow, map_natCast, ZMod.natCast_zmod_val, hx, map_ofNat, sub_self]
    · rintro ⟨y, hy⟩
      refine ⟨toZMod hp' y, ?_⟩
      have := (toZMod_eq_zero_iff hp' _).2 hy
      rw [map_sub, map_pow, map_ofNat, sub_eq_zero] at this
      exact this
  rw [hsolv, exists_cube_eq_two_iff_dvd_sub_one hp' hu]
  -- `π = a + bω` with `a ≡ 2`, `b ≡ 0 (mod 3)` and `p = a² - ab + b²`
  obtain ⟨ha3, hb3⟩ := (isPrimary_iff π).1 hu
  have hnorm : ((norm π).natAbs : ℤ) = π.re ^ 2 - π.re * π.im + π.im ^ 2 := by
    rw [Int.natAbs_of_nonneg (rho_norm_nonneg π), rho_norm]
  have h2dvd : (2 : ℤ[ω]) ∣ π - 1 ↔ 2 ∣ π.re - 1 ∧ 2 ∣ π.im := by
    rw [show (2 : ℤ[ω]) = ((2 : ℤ) : ℤ[ω]) by norm_num, intCast_dvd_iff]
    simp
  rw [h2dvd]
  have hpodd : (norm π).natAbs % 2 = 1 := by
    have := natAbs_norm_mod_three (prime_of_natAbs_norm_prime hp') (by omega)
    rcases hp'.eq_two_or_odd with h | h
    · omega
    · exact h
  constructor
  · rintro ⟨-, ⟨b', hb'⟩⟩
    obtain ⟨D, hD⟩ : ∃ D, b' = 3 * D := ⟨b' / 3, by omega⟩
    refine ⟨π.re - 3 * D, D, ?_⟩
    rw [hnorm, hb', hD]; ring
  · rintro ⟨C, D, hCD⟩
    have h1 : 4 * ((norm π).natAbs : ℤ) = (2 * π.re - π.im) ^ 2 + 27 * (π.im / 3) ^ 2 := by
      obtain ⟨t, ht⟩ : ∃ t, π.im = 3 * t := ⟨π.im / 3, by omega⟩
      rw [hnorm, ht, show 3 * t / 3 = t by omega]; ring
    have h2 : 4 * ((norm π).natAbs : ℤ) = (2 * C) ^ 2 + 27 * (2 * D) ^ 2 := by
      rw [hCD]; ring
    obtain ⟨-, hB⟩ := sq_eq_sq_of_four_mul_prime hp' h1 h2
    have hbeven : 2 ∣ π.im := by
      obtain ⟨t, ht⟩ : ∃ t, π.im = 3 * t := ⟨π.im / 3, by omega⟩
      rw [ht, show 3 * t / 3 = t by omega] at hB
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 hB with h | h
      · exact ⟨3 * D, by rw [ht, h]; ring⟩
      · exact ⟨-3 * D, by rw [ht, h]; ring⟩
    refine ⟨?_, hbeven⟩
    obtain ⟨b', hb'⟩ := hbeven
    have : ((norm π).natAbs : ℤ) % 2 = 1 := by exact_mod_cast hpodd
    rw [hnorm, hb'] at this
    have : π.re ^ 2 % 2 = 1 := by
      have e : π.re ^ 2 - π.re * (2 * b') + (2 * b') ^ 2 = π.re ^ 2 + 2 * (2 * b' ^ 2 - π.re * b') :=
        by ring
      rw [e] at this; omega
    rcases Int.emod_two_eq_zero_or_one π.re with h | h
    · exfalso
      have : π.re ^ 2 % 2 = 0 := by
        rw [sq, Int.mul_emod, h]; norm_num
      omega
    · omega

end Eisenstein

end NTKB.IrelandRosen
