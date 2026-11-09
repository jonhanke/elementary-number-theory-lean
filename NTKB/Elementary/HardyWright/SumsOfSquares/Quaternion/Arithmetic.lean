/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Quaternion.Basic

/-!
# Hardy–Wright, §§ 20.8–20.9: ideals, highest common right-hand divisors, prime quaternions

`γ = αβ` makes `β` a *right-hand divisor* of `γ`; the statements below spell this out as
`∃ λ, γ = λ * β`. A *right-ideal* of the book (closed under sums and under `α ↦ λα`) is a Mathlib
`Ideal IntegralQuaternion` (`Submodule IntegralQuaternion IntegralQuaternion`, a left ideal in
Mathlib's convention). A *prime* quaternion of the book (a non-unity whose factorizations
`π = αβ` all have `α` or `β` a unity) is Mathlib's `Irreducible`.

* Theorem 374: every right-ideal is principal (`ideal_eq_mul_singleton`).
* Theorem 375: highest common right-hand divisors (`exists_highestCommonRightDivisor`,
  `IsHighestCommonRightDivisor.unique`).
* Theorem 376: `(α, m)_r = 1 ↔ (Nα, m) = 1` (`rightCoprime_natCast_iff`).
* Theorem 378: a rational prime is not a prime quaternion (`not_irreducible_natCast`).
* Theorem 377: `π` is prime if and only if `Nπ` is a rational prime (`irreducible_iff_prime_qnorm`).
* Theorem 370 (the second proof, § 20.9): every prime is a sum of four squares
  (`Nat.Prime.sum_four_squares_of_quaternions`).
* Theorem 379: `4p` is a sum of four odd squares for every odd prime `p`.
-/

open Quaternion

namespace NTKB.HardyWright

/-- **Theorem 374** (Hardy–Wright). Every right-ideal of integral quaternions is principal: it is
the set of left-hand multiples `λδ` of one of its elements `δ`. -/
@[kb "hardywright2008" "Thm 374, p. 424"]
theorem ideal_eq_mul_singleton (I : Ideal IntegralQuaternion) :
    ∃ δ ∈ I, ∀ x, x ∈ I ↔ ∃ l, x = l * δ := by
  classical
  by_cases h0 : ∀ x ∈ I, x = 0
  · refine ⟨0, I.zero_mem, fun x => ⟨fun hx => ⟨0, by simp [h0 x hx]⟩, ?_⟩⟩
    rintro ⟨l, rfl⟩; simp
  push Not at h0
  have hex : ∃ n, ∃ x ∈ I, x ≠ 0 ∧ qnorm x = n := by
    obtain ⟨x, hx, hx0⟩ := h0
    exact ⟨_, x, hx, hx0, rfl⟩
  obtain ⟨δ, hδI, hδ0, hδn⟩ := Nat.find_spec hex
  refine ⟨δ, hδI, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · obtain ⟨l, c, hxc, hc⟩ := exists_eq_mul_add_qnorm_lt x hδ0
    have hcI : c ∈ I := by
      have : c = x - l • δ := by rw [smul_eq_mul, hxc]; abel
      rw [this]; exact I.sub_mem hx (I.smul_mem l hδI)
    by_cases hc0 : c = 0
    · exact ⟨l, by rw [hxc, hc0, add_zero]⟩
    · exact absurd (hδn ▸ hc) (not_lt.2 (Nat.find_min' hex ⟨c, hcI, hc0, rfl⟩))
  · rintro ⟨l, rfl⟩; exact I.smul_mem l hδI

/-- Theorem 374 in Mathlib's language: every ideal is principal. -/
lemma ideal_isPrincipal (I : Ideal IntegralQuaternion) : Submodule.IsPrincipal I := by
  obtain ⟨δ, -, h⟩ := ideal_eq_mul_singleton I
  refine ⟨δ, Submodule.ext fun x => ?_⟩
  rw [h x, Submodule.mem_span_singleton]
  exact ⟨fun ⟨l, hl⟩ => ⟨l, hl.symm⟩, fun ⟨l, hl⟩ => ⟨l, hl.symm⟩⟩

/-- `δ` is a highest common right-hand divisor of `α` and `β` (Hardy–Wright § 20.8): a common
right-hand divisor of which every common right-hand divisor is a right-hand divisor. -/
def IsHighestCommonRightDivisor (a b δ : IntegralQuaternion) : Prop :=
  (∃ x, a = x * δ) ∧ (∃ y, b = y * δ) ∧
    ∀ δ', (∃ x, a = x * δ') → (∃ y, b = y * δ') → ∃ z, δ = z * δ'

/-- **Theorem 375** (Hardy–Wright), existence. Two integral quaternions have a highest common
right-hand divisor `δ`, of the form `δ = μα + νβ` with `μ, ν` integral. -/
@[kb "hardywright2008" "Thm 375, p. 425"]
theorem exists_highestCommonRightDivisor (a b : IntegralQuaternion) :
    ∃ δ, IsHighestCommonRightDivisor a b δ ∧ ∃ μ ν, δ = μ * a + ν * b := by
  obtain ⟨δ, hδI, h⟩ := ideal_eq_mul_singleton (Ideal.span {a, b})
  obtain ⟨μ, ν, hμν⟩ := Ideal.mem_span_pair.1 hδI
  refine ⟨δ, ⟨(h a).1 (Ideal.subset_span (by simp)), (h b).1 (Ideal.subset_span (by simp)), ?_⟩,
    μ, ν, hμν.symm⟩
  rintro δ' ⟨x, rfl⟩ ⟨y, rfl⟩
  exact ⟨μ * x + ν * y, by rw [← hμν, add_mul, mul_assoc, mul_assoc]⟩

/-- **Theorem 375** (Hardy–Wright), uniqueness. If `α, β` are not both `0`, their highest common
right-hand divisor is unique up to a left-hand unity factor. -/
@[kb "hardywright2008" "Thm 375, p. 425"]
theorem IsHighestCommonRightDivisor.unique {a b δ δ' : IntegralQuaternion} (hab : a ≠ 0 ∨ b ≠ 0)
    (hδ : IsHighestCommonRightDivisor a b δ) (hδ' : IsHighestCommonRightDivisor a b δ') :
    ∃ ε, IsUnit ε ∧ δ' = ε * δ := by
  obtain ⟨l', hl'⟩ := hδ.2.2 δ' hδ'.1 hδ'.2.1
  obtain ⟨l, hl⟩ := hδ'.2.2 δ hδ.1 hδ.2.1
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, -⟩ := hδ
    rcases hab with h | h
    · exact h (by simpa using hx)
    · exact h (by simpa using hy)
  have h1 : (1 - l' * l) * δ = 0 := by
    rw [sub_mul, one_mul, mul_assoc, ← hl, ← hl', sub_self]
  have h2 : qnorm (1 - l' * l) = 0 := by
    have := congrArg qnorm h1
    rw [qnorm_mul, (qnorm_eq_zero).2 rfl] at this
    exact (mul_eq_zero.1 this).resolve_right (fun h => hδ0 (qnorm_eq_zero.1 h))
  have h3 : l' * l = 1 := by
    have := (qnorm_eq_zero).1 h2
    exact (sub_eq_zero.1 this).symm
  have h4 : qnorm l = 1 := by
    have := congrArg qnorm h3
    rw [qnorm_mul, qnorm_one] at this
    exact Nat.eq_one_of_mul_eq_one_left this
  exact ⟨l, isUnit_iff_qnorm_eq_one.2 h4, hl⟩

/-- `(α, β)_r = 1` (Hardy–Wright (20.8.3)): `μα + νβ = 1` for some integral `μ, ν`. -/
def RightCoprime (a b : IntegralQuaternion) : Prop := ∃ μ ν, μ * a + ν * b = 1

/-- Twice the real part of an integral quaternion is a rational integer. -/
lemma exists_two_mul_re (a : IntegralQuaternion) : ∃ t : ℤ, 2 * (a : ℍ[ℚ]).re = t := by
  obtain ⟨k0, k1, k2, k3, h⟩ := a.2
  exact ⟨k0, by rw [h]; simp; ring⟩

/-- `N(1 - mν) = 1 - m t + m² Nν` with `t = 2 Re ν` (the computation in the proof of Theorem 376). -/
lemma qnorm_one_sub_natCast_mul (m : ℕ) (ν : IntegralQuaternion) :
    ∃ t : ℤ, (qnorm (1 - (m : IntegralQuaternion) * ν) : ℤ) = 1 - m * t + m ^ 2 * qnorm ν := by
  obtain ⟨k0, k1, k2, k3, hk⟩ := ν.2
  refine ⟨k0, ?_⟩
  have hν : (qnorm ν : ℚ) = hurwitzNorm k0 k1 k2 k3 := by rw [qnorm_cast, hk, normSq_hurwitzMk]
  have : ((qnorm (1 - (m : IntegralQuaternion) * ν) : ℤ) : ℚ) =
      ((1 - m * k0 + m ^ 2 * qnorm ν : ℤ) : ℚ) := by
    push_cast
    rw [hν, qnorm_cast, AddSubgroupClass.coe_sub, Subring.coe_mul, hk, normSq_def']
    simp [hurwitzNorm]
    ring
  exact_mod_cast this

/-- **Theorem 376** (Hardy–Wright). For an integral quaternion `α` and a positive integer `m`,
`(α, m)_r = 1` if and only if `(Nα, m) = 1`. -/
@[kb "hardywright2008" "Thm 376, p. 426"]
theorem rightCoprime_natCast_iff (a : IntegralQuaternion) {m : ℕ} (_hm : 0 < m) :
    RightCoprime a m ↔ Nat.Coprime (qnorm a) m := by
  constructor
  · rintro ⟨μ, ν, h⟩
    -- `Nμ Nα = N(1 - νm) = 1 - m t + m² Nν`
    obtain ⟨t, ht⟩ := qnorm_one_sub_natCast_mul m ν
    have e : μ * a = 1 - (m : IntegralQuaternion) * ν := by
      rw [natCast_mul_comm, ← h]; abel
    rw [← e, qnorm_mul] at ht
    rw [← Nat.isCoprime_iff_coprime]
    refine ⟨qnorm μ, t - m * qnorm ν, ?_⟩
    push_cast at ht
    linear_combination ht
  · intro h
    obtain ⟨δ, ⟨⟨x, hx⟩, ⟨y, hy⟩, -⟩, μ, ν, hδ⟩ := exists_highestCommonRightDivisor a m
    by_cases hu : IsUnit δ
    · obtain ⟨u, rfl⟩ := hu
      refine ⟨(↑u⁻¹ : IntegralQuaternion) * μ, (↑u⁻¹ : IntegralQuaternion) * ν, ?_⟩
      rw [mul_assoc, mul_assoc, ← mul_add, ← hδ, Units.inv_mul]
    · exfalso
      have hn1 : qnorm δ ≠ 1 := fun h1 => hu (isUnit_iff_qnorm_eq_one.2 h1)
      have hda : qnorm δ ∣ qnorm a := ⟨qnorm x, by rw [hx, qnorm_mul, mul_comm]⟩
      have hdm : qnorm δ ∣ m ^ 2 := ⟨qnorm y, by rw [← qnorm_natCast, hy, qnorm_mul, mul_comm]⟩
      have hcop : Nat.Coprime (qnorm a) (m ^ 2) := Nat.Coprime.pow_right 2 h
      exact hn1 (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hda hcop) hdm)

lemma not_isUnit_of_qnorm_ne_one {a : IntegralQuaternion} (h : qnorm a ≠ 1) : ¬ IsUnit a :=
  fun hu => h (isUnit_iff_qnorm_eq_one.1 hu)

/-- **Theorem 378** (Hardy–Wright), in the form proved in the book: a rational prime `p` is a product
`p = δ₂δ` of two integral quaternions neither of which is a unity. -/
lemma exists_mul_eq_natCast_prime {p : ℕ} (hp : p.Prime) :
    ∃ δ₂ δ : IntegralQuaternion, (p : IntegralQuaternion) = δ₂ * δ ∧ ¬ IsUnit δ₂ ∧ ¬ IsUnit δ := by
  rcases hp.eq_two_or_odd with rfl | hodd
  · -- `2 = (1 + i₁)(1 - i₁)`
    have h1 : (⟨1, 1, 0, 0⟩ : ℍ[ℚ]) ∈ integralQuaternions := lipschitz_le_integral ⟨1, 1, 0, 0, by
      ext <;> simp⟩
    have h2 : (⟨1, -1, 0, 0⟩ : ℍ[ℚ]) ∈ integralQuaternions := lipschitz_le_integral ⟨1, -1, 0, 0,
      by ext <;> simp⟩
    refine ⟨⟨_, h1⟩, ⟨_, h2⟩, Subtype.ext ?_, not_isUnit_of_qnorm_ne_one ?_,
      not_isUnit_of_qnorm_ne_one ?_⟩
    · rw [SubringClass.coe_natCast, Subring.coe_mul]
      ext <;> simp only [re_natCast, imI_natCast, imJ_natCast, imK_natCast, Quaternion.re_mul,
        Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;> norm_num
    · rw [Ne, qnorm_eq_iff, normSq_def']; norm_num
    · rw [Ne, qnorm_eq_iff, normSq_def']; norm_num
  · -- `α = 1 + s i₁ - r i₃` has norm `1 + r² + s² ≡ 0 (mod p)`
    have := Fact.mk hp
    obtain ⟨r, s, k, hk0, hkp, hrs⟩ := Int.exists_sq_add_sq_add_one_eq_mul p
    have hα : (⟨1, s, 0, -r⟩ : ℍ[ℚ]) ∈ integralQuaternions := lipschitz_le_integral ⟨1, s, 0, -r, by
      ext <;> simp⟩
    let α : IntegralQuaternion := ⟨_, hα⟩
    have hαn : qnorm α = k * p := by
      rw [qnorm_eq_iff, normSq_def']; push_cast [← hrs]; simp [α]; ring
    have hnc : ¬ RightCoprime α p := by
      rw [rightCoprime_natCast_iff α hp.pos, hαn]
      intro h
      have := Nat.Coprime.coprime_mul_left h
      exact hp.one_lt.ne' ((Nat.coprime_self p).1 this)
    obtain ⟨δ, ⟨⟨δ₁, hδ₁⟩, ⟨δ₂, hδ₂⟩, -⟩, μ, ν, hδ⟩ := exists_highestCommonRightDivisor α p
    have hδu : ¬ IsUnit δ := by
      rintro ⟨u, rfl⟩
      refine hnc ⟨(↑u⁻¹ : IntegralQuaternion) * μ, (↑u⁻¹ : IntegralQuaternion) * ν, ?_⟩
      rw [mul_assoc, mul_assoc, ← mul_add, ← hδ, Units.inv_mul]
    refine ⟨δ₂, δ, hδ₂, ?_, hδu⟩
    -- if `δ₂` were a unity, `p` would divide every coordinate of `α`, in particular `1`
    rintro ⟨u, hu⟩
    have : α = (δ₁ * (↑u⁻¹ : IntegralQuaternion)) * p := by
      rw [hδ₁, hδ₂, ← hu, mul_assoc, ← mul_assoc _ (u : IntegralQuaternion), Units.inv_mul, one_mul]
    obtain ⟨l0, l1, l2, l3, hl⟩ := (δ₁ * (↑u⁻¹ : IntegralQuaternion)).2
    have hre := congrArg (fun z : IntegralQuaternion => (z : ℍ[ℚ]).re) this
    simp only [α, Subring.coe_mul, SubringClass.coe_natCast, hl] at hre
    simp at hre
    have h2 : ((2 : ℤ) : ℚ) = ((l0 * p : ℤ) : ℚ) := by push_cast; linarith
    have h2' := Int.cast_injective h2
    have : (p : ℤ) ∣ 2 := ⟨l0, by rw [h2']; ring⟩
    have h3 : p ≤ 2 := Nat.le_of_dvd (by norm_num) (by exact_mod_cast this)
    have := hp.two_le
    omega

/-- **Theorem 378** (Hardy–Wright). A rational prime is not a prime quaternion. -/
@[kb "hardywright2008" "Thm 378, p. 426"]
theorem not_irreducible_natCast {p : ℕ} (hp : p.Prime) : ¬ Irreducible (p : IntegralQuaternion) := by
  obtain ⟨δ₂, δ, h, h₂, h₁⟩ := exists_mul_eq_natCast_prime hp
  intro hirr
  rcases hirr.isUnit_or_isUnit h with h' | h'
  · exact h₂ h'
  · exact h₁ h'

/-- In a factorization `p = δ₂δ` into non-unities, `Nδ = p`. -/
lemma qnorm_eq_of_mul_eq_natCast_prime {p : ℕ} (hp : p.Prime) {δ₂ δ : IntegralQuaternion}
    (h : (p : IntegralQuaternion) = δ₂ * δ) (h₂ : ¬ IsUnit δ₂) (h₁ : ¬ IsUnit δ) : qnorm δ = p := by
  have := congrArg qnorm h
  rw [qnorm_natCast, qnorm_mul] at this
  have hd : qnorm δ ∣ p ^ 2 := ⟨qnorm δ₂, by rw [this, mul_comm]⟩
  rcases (Nat.dvd_prime_pow hp).1 hd with ⟨i, hi, hδi⟩
  interval_cases i
  · exact absurd (isUnit_iff_qnorm_eq_one.2 (by simpa using hδi)) h₁
  · simpa using hδi
  · rw [hδi] at this
    have : qnorm δ₂ = 1 := by
      have hp2 : 0 < p ^ 2 := pow_pos hp.pos 2
      nlinarith [this]
    exact absurd (isUnit_iff_qnorm_eq_one.2 this) h₂

/-- **Theorem 377** (Hardy–Wright). An integral quaternion `π` is prime if and only if its norm is a
rational prime. -/
@[kb "hardywright2008" "Thm 377, p. 426"]
theorem irreducible_iff_prime_qnorm (π : IntegralQuaternion) : Irreducible π ↔ (qnorm π).Prime := by
  constructor
  · intro hπ
    have hπ0 : π ≠ 0 := hπ.ne_zero
    have hn1 : qnorm π ≠ 1 := fun h => hπ.not_isUnit (isUnit_iff_qnorm_eq_one.2 h)
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hn1
    -- `π` and `p` have a common right-hand divisor `π'` which is not a unity
    have hnc : ¬ RightCoprime π p := by
      rw [rightCoprime_natCast_iff π hp.pos]
      intro h
      exact hp.one_lt.ne' ((Nat.coprime_self p).1 (Nat.Coprime.coprime_dvd_left hpd h))
    obtain ⟨π', ⟨⟨x, hx⟩, ⟨l, hl⟩, -⟩, μ, ν, hπ'⟩ := exists_highestCommonRightDivisor π p
    have hπ'u : ¬ IsUnit π' := by
      rintro ⟨u, rfl⟩
      refine hnc ⟨(↑u⁻¹ : IntegralQuaternion) * μ, (↑u⁻¹ : IntegralQuaternion) * ν, ?_⟩
      rw [mul_assoc, mul_assoc, ← mul_add, ← hπ', Units.inv_mul]
    have hxu : IsUnit x := (hπ.isUnit_or_isUnit hx).resolve_right hπ'u
    have hnπ : qnorm π' = qnorm π := by rw [hx, qnorm_unit_mul hxu]
    -- `p = λπ'`, `p² = Nλ Nπ`
    by_cases hlu : IsUnit l
    · -- then `π = (x λ⁻¹) p` is a product of two non-unities, by Theorem 378
      exfalso
      obtain ⟨δ₂, δ, hpd', h₂, h₁⟩ := exists_mul_eq_natCast_prime hp
      obtain ⟨u, rfl⟩ := hlu
      have hπp : π = (x * (↑u⁻¹ : IntegralQuaternion) * δ₂) * δ := by
        rw [mul_assoc (x * _), ← hpd', hl, ← mul_assoc, mul_assoc x, Units.inv_mul, mul_one, hx]
      rcases hπ.isUnit_or_isUnit hπp with h | h
      · apply h₂
        have hn : qnorm (x * (↑u⁻¹ : IntegralQuaternion) * δ₂) = qnorm δ₂ := by
          rw [qnorm_mul, qnorm_mul, isUnit_iff_qnorm_eq_one.1 hxu,
            isUnit_iff_qnorm_eq_one.1 (Units.isUnit u⁻¹), one_mul, one_mul]
        exact isUnit_iff_qnorm_eq_one.2 (hn ▸ isUnit_iff_qnorm_eq_one.1 h)
      · exact h₁ h
    · rw [← hnπ, qnorm_eq_of_mul_eq_natCast_prime hp hl hlu hπ'u]; exact hp
  · intro hp
    refine ⟨fun hu => hp.one_lt.ne' (isUnit_iff_qnorm_eq_one.1 hu), fun a b hab => ?_⟩
    have := congrArg qnorm hab
    rw [qnorm_mul] at this
    rcases (Nat.prime_mul_iff.1 (this ▸ hp)) with ⟨-, hb⟩ | ⟨-, ha⟩
    · exact Or.inr (isUnit_iff_qnorm_eq_one.2 hb)
    · exact Or.inl (isUnit_iff_qnorm_eq_one.2 ha)

/-- **Theorem 370** (Hardy–Wright), the second proof (§ 20.9, by quaternions): every prime is the sum
of four squares. -/
@[kb "hardywright2008" "Thm 370, p. 418"]
theorem Nat.Prime.sum_four_squares_of_quaternions {p : ℕ} (hp : p.Prime) :
    ∃ a b c d : ℤ, (p : ℤ) = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  obtain ⟨δ₂, δ, h, h₂, h₁⟩ := exists_mul_eq_natCast_prime hp
  have hδ := qnorm_eq_of_mul_eq_natCast_prime hp h h₂ h₁
  obtain ⟨ε, hε, b0, b1, b2, b3, hb⟩ := exists_isUnit_hasIntCoords_mul δ
  refine ⟨b0, b1, b2, b3, ?_⟩
  have : ((p : ℤ) : ℚ) = ((b0 ^ 2 + b1 ^ 2 + b2 ^ 2 + b3 ^ 2 : ℤ) : ℚ) := by
    rw [Int.cast_natCast, ← hδ, ← qnorm_mul_unit hε, qnorm_cast, hb, normSq_def']
    push_cast; ring
  exact Int.cast_injective this

/-- **Theorem 379** (Hardy–Wright). If `p` is an odd prime, then `4p` is the sum of four odd integral
squares. -/
@[kb "hardywright2008" "Thm 379, p. 428"]
theorem four_mul_prime_eq_sum_four_odd_sq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ a b c d : ℕ, Odd a ∧ Odd b ∧ Odd c ∧ Odd d ∧ 4 * p = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  obtain ⟨δ₂, δ, h, h₂, h₁⟩ := exists_mul_eq_natCast_prime hp
  have hδ := qnorm_eq_of_mul_eq_natCast_prime hp h h₂ h₁
  have hodd : qnorm δ % 2 = 1 := by rw [hδ]; exact hp.eq_two_or_odd.resolve_left hp2
  obtain ⟨ε, hε, hnot⟩ := exists_isUnit_not_hasIntCoords_mul hodd
  rcases (mem_integralQuaternions_iff _).1 (δ * ε).2 with hint | ⟨b0, b1, b2, b3, hb⟩
  · exact absurd hint hnot
  refine ⟨(2 * b0 + 1).natAbs, (2 * b1 + 1).natAbs, (2 * b2 + 1).natAbs, (2 * b3 + 1).natAbs,
    by simp [Int.natAbs_odd], by simp [Int.natAbs_odd], by simp [Int.natAbs_odd],
    by simp [Int.natAbs_odd], ?_⟩
  have : (((4 * p : ℕ) : ℤ) : ℚ) = (((2 * b0 + 1) ^ 2 + (2 * b1 + 1) ^ 2 + (2 * b2 + 1) ^ 2 +
      (2 * b3 + 1) ^ 2 : ℤ) : ℚ) := by
    rw [Int.cast_natCast, Nat.cast_mul, ← hδ, ← qnorm_mul_unit hε, qnorm_cast, hb, normSq_def']
    push_cast; ring
  have h' := Int.cast_injective this
  zify
  simp only [sq_abs]
  push_cast at h'
  linarith

end NTKB.HardyWright
