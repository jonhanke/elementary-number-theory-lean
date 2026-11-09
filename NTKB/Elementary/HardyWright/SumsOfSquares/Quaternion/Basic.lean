/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Waring
import NTKB.Attr
import Mathlib.Algebra.Quaternion
import Mathlib.Computability.Reduce
import Mathlib.Tactic.LinearCombination

/-!
# Hardy–Wright, §§ 20.6–20.7: integral quaternions

Quaternions are Mathlib's `ℍ[ℚ]` (`i₁ i₂ = i₃` etc., (20.6.2)); conjugate and norm are Mathlib's
`star` and `Quaternion.normSq` ((20.6.6)–(20.6.8)).

A quaternion is *integral* (Hardy–Wright § 20.6) if its coordinates are all rational integers or
all halves of odd integers. Equivalently (20.6.13) it is `k₀ρ + k₁i₁ + k₂i₂ + k₃i₃` with integers
`kᵢ`, `ρ = ½(1 + i₁ + i₂ + i₃)`; this is the form used to define the subring `integralQuaternions`
(the equivalence with the book's definition is `mem_integralQuaternions_iff`). Its elements form
the type `IntegralQuaternion`, with the norm `qnorm : IntegralQuaternion → ℕ`.

* § 20.6: integral quaternions are closed under products; unities are the integral quaternions of
  norm `1` (`isUnit_iff_qnorm_eq_one`); the 24 unities (20.6.11) (`isUnit_iff_mem_unities`).
* Theorem 371: every integral quaternion has an associate with integral coordinates; an odd one has
  an associate with non-integral coordinates.
* Theorem 372: `N(κ - mλ) < m²` for a suitable `λ`.
* Theorem 373: division with remainder, `α = λβ + γ`, `Nγ < Nβ`.
-/

open Quaternion

namespace NTKB.HardyWright

/-- The quaternion `k₀ρ + k₁i₁ + k₂i₂ + k₃i₃`, `ρ = ½(1 + i₁ + i₂ + i₃)` (Hardy–Wright (20.6.13)). -/
def hurwitzMk (k₀ k₁ k₂ k₃ : ℤ) : ℍ[ℚ] := ⟨k₀ / 2, k₀ / 2 + k₁, k₀ / 2 + k₂, k₀ / 2 + k₃⟩

@[simp] lemma hurwitzMk_re (k₀ k₁ k₂ k₃ : ℤ) : (hurwitzMk k₀ k₁ k₂ k₃).re = k₀ / 2 := rfl
@[simp] lemma hurwitzMk_imI (k₀ k₁ k₂ k₃ : ℤ) : (hurwitzMk k₀ k₁ k₂ k₃).imI = k₀ / 2 + k₁ := rfl
@[simp] lemma hurwitzMk_imJ (k₀ k₁ k₂ k₃ : ℤ) : (hurwitzMk k₀ k₁ k₂ k₃).imJ = k₀ / 2 + k₂ := rfl
@[simp] lemma hurwitzMk_imK (k₀ k₁ k₂ k₃ : ℤ) : (hurwitzMk k₀ k₁ k₂ k₃).imK = k₀ / 2 + k₃ := rfl

/-- The integral quaternions of Hardy–Wright § 20.6, as a subring of `ℍ[ℚ]`. -/
def integralQuaternions : Subring ℍ[ℚ] where
  carrier := {a | ∃ k₀ k₁ k₂ k₃ : ℤ, a = hurwitzMk k₀ k₁ k₂ k₃}
  mul_mem' := by
    rintro _ _ ⟨k0, k1, k2, k3, rfl⟩ ⟨l0, l1, l2, l3, rfl⟩
    refine ⟨-k0 * l0 - k0 * (l1 + l2 + l3) - l0 * (k1 + k2 + k3) - 2 * (k1 * l1 + k2 * l2 + k3 * l3),
      k0 * l0 + k0 * (l1 + l3) + l0 * (k1 + k2) + k2 * l3 - k3 * l2 + (k1 * l1 + k2 * l2 + k3 * l3),
      k0 * l0 + k0 * (l1 + l2) + l0 * (k2 + k3) - k1 * l3 + k3 * l1 + (k1 * l1 + k2 * l2 + k3 * l3),
      k0 * l0 + k0 * (l2 + l3) + l0 * (k1 + k3) + k1 * l2 - k2 * l1 + (k1 * l1 + k2 * l2 + k3 * l3),
      ?_⟩
    ext <;> simp <;> ring
  one_mem' := ⟨2, -1, -1, -1, by ext <;> simp⟩
  add_mem' := by
    rintro _ _ ⟨k0, k1, k2, k3, rfl⟩ ⟨l0, l1, l2, l3, rfl⟩
    exact ⟨k0 + l0, k1 + l1, k2 + l2, k3 + l3, by ext <;> simp <;> ring⟩
  zero_mem' := ⟨0, 0, 0, 0, by ext <;> simp⟩
  neg_mem' := by
    rintro _ ⟨k0, k1, k2, k3, rfl⟩
    exact ⟨-k0, -k1, -k2, -k3, by ext <;> simp <;> ring⟩

/-- The integral quaternions (Hardy–Wright § 20.6). -/
abbrev IntegralQuaternion := integralQuaternions

/-- A quaternion has integral coordinates. -/
def HasIntCoords (a : ℍ[ℚ]) : Prop := ∃ b₀ b₁ b₂ b₃ : ℤ, a = ⟨b₀, b₁, b₂, b₃⟩

/-- The quaternions with integral coordinates form a subring. -/
def lipschitzQuaternions : Subring ℍ[ℚ] where
  carrier := {a | HasIntCoords a}
  mul_mem' := by
    rintro _ _ ⟨a0, a1, a2, a3, rfl⟩ ⟨b0, b1, b2, b3, rfl⟩
    exact ⟨a0 * b0 - a1 * b1 - a2 * b2 - a3 * b3, a0 * b1 + a1 * b0 + a2 * b3 - a3 * b2,
      a0 * b2 - a1 * b3 + a2 * b0 + a3 * b1, a0 * b3 + a1 * b2 - a2 * b1 + a3 * b0,
      by ext <;> simp <;> ring⟩
  one_mem' := ⟨1, 0, 0, 0, by ext <;> simp⟩
  add_mem' := by
    rintro _ _ ⟨a0, a1, a2, a3, rfl⟩ ⟨b0, b1, b2, b3, rfl⟩
    exact ⟨a0 + b0, a1 + b1, a2 + b2, a3 + b3, by ext <;> simp⟩
  zero_mem' := ⟨0, 0, 0, 0, by ext <;> simp⟩
  neg_mem' := by
    rintro _ ⟨a0, a1, a2, a3, rfl⟩
    exact ⟨-a0, -a1, -a2, -a3, by ext <;> simp⟩

lemma hasIntCoords_iff_mem_lipschitz (a : ℍ[ℚ]) : HasIntCoords a ↔ a ∈ lipschitzQuaternions :=
  Iff.rfl

lemma lipschitz_le_integral : lipschitzQuaternions ≤ integralQuaternions := by
  rintro _ ⟨b0, b1, b2, b3, rfl⟩
  exact ⟨2 * b0, b1 - b0, b2 - b0, b3 - b0, by ext <;> simp⟩

/-- **§ 20.6** (Hardy–Wright): the book's definition of an integral quaternion — coordinates all
rational integers, or all halves of odd rational integers. -/
@[kb "hardywright2008" "Section 20.6, p. 421"]
theorem mem_integralQuaternions_iff (a : ℍ[ℚ]) :
    a ∈ integralQuaternions ↔ HasIntCoords a ∨
      ∃ b₀ b₁ b₂ b₃ : ℤ, a = ⟨b₀ + 1 / 2, b₁ + 1 / 2, b₂ + 1 / 2, b₃ + 1 / 2⟩ := by
  constructor
  · rintro ⟨k0, k1, k2, k3, rfl⟩
    rcases Int.even_or_odd' k0 with ⟨t, rfl | rfl⟩
    · exact Or.inl ⟨t, t + k1, t + k2, t + k3, by ext <;> simp⟩
    · exact Or.inr ⟨t, t + k1, t + k2, t + k3, by ext <;> simp <;> ring⟩
  · rintro (h | ⟨b0, b1, b2, b3, rfl⟩)
    · exact lipschitz_le_integral h
    · exact ⟨2 * b0 + 1, b1 - b0, b2 - b0, b3 - b0, by ext <;> simp <;> ring⟩

/-! ### The norm -/

/-- The norm of `k₀ρ + k₁i₁ + k₂i₂ + k₃i₃`. -/
def hurwitzNorm (k₀ k₁ k₂ k₃ : ℤ) : ℤ :=
  k₀ ^ 2 + k₀ * (k₁ + k₂ + k₃) + k₁ ^ 2 + k₂ ^ 2 + k₃ ^ 2

lemma normSq_hurwitzMk (k₀ k₁ k₂ k₃ : ℤ) :
    normSq (hurwitzMk k₀ k₁ k₂ k₃) = hurwitzNorm k₀ k₁ k₂ k₃ := by
  rw [normSq_def']
  simp only [hurwitzMk, hurwitzNorm]
  push_cast
  ring

lemma four_mul_hurwitzNorm (k₀ k₁ k₂ k₃ : ℤ) : 4 * hurwitzNorm k₀ k₁ k₂ k₃ =
    k₀ ^ 2 + (k₀ + 2 * k₁) ^ 2 + (k₀ + 2 * k₂) ^ 2 + (k₀ + 2 * k₃) ^ 2 := by
  unfold hurwitzNorm; ring

lemma hurwitzNorm_nonneg (k₀ k₁ k₂ k₃ : ℤ) : 0 ≤ hurwitzNorm k₀ k₁ k₂ k₃ := by
  have := four_mul_hurwitzNorm k₀ k₁ k₂ k₃
  nlinarith [sq_nonneg k₀, sq_nonneg (k₀ + 2 * k₁), sq_nonneg (k₀ + 2 * k₂), sq_nonneg (k₀ + 2 * k₃)]

/-- The norm of an integral quaternion is a rational integer (Hardy–Wright § 20.6). -/
lemma exists_normSq_eq (a : IntegralQuaternion) : ∃ n : ℕ, normSq (a : ℍ[ℚ]) = n := by
  obtain ⟨k0, k1, k2, k3, h⟩ := a.2
  refine ⟨(hurwitzNorm k0 k1 k2 k3).toNat, ?_⟩
  rw [h, normSq_hurwitzMk]
  have := hurwitzNorm_nonneg k0 k1 k2 k3
  exact_mod_cast (Int.toNat_of_nonneg this).symm

/-- The norm `Nα` of an integral quaternion, as a natural number (Hardy–Wright (20.6.7)). -/
noncomputable def qnorm (a : IntegralQuaternion) : ℕ := (exists_normSq_eq a).choose

lemma qnorm_cast (a : IntegralQuaternion) :
    (qnorm a : ℚ) = normSq (a : ℍ[ℚ]) := (exists_normSq_eq a).choose_spec.symm

lemma qnorm_eq_iff (a : IntegralQuaternion) (n : ℕ) : qnorm a = n ↔ normSq (a : ℍ[ℚ]) = n := by
  rw [← qnorm_cast]; exact_mod_cast Iff.rfl

/-- `N(αβ) = Nα · Nβ` (Hardy–Wright (20.6.8)). -/
@[simp] lemma qnorm_mul (a b : IntegralQuaternion) : qnorm (a * b) = qnorm a * qnorm b := by
  have : (qnorm (a * b) : ℚ) = qnorm a * qnorm b := by
    rw [qnorm_cast, qnorm_cast, qnorm_cast, Subring.coe_mul, map_mul]
  exact_mod_cast this

@[simp] lemma qnorm_eq_zero {a : IntegralQuaternion} : qnorm a = 0 ↔ a = 0 := by
  rw [qnorm_eq_iff]
  push_cast
  rw [normSq_eq_zero]
  exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩

lemma qnorm_pos {a : IntegralQuaternion} : 0 < qnorm a ↔ a ≠ 0 := by
  rw [Nat.pos_iff_ne_zero, Ne, qnorm_eq_zero]

@[simp] lemma qnorm_one : qnorm 1 = 1 := by
  rw [qnorm_eq_iff]; simp

@[simp] lemma qnorm_natCast (m : ℕ) : qnorm (m : IntegralQuaternion) = m ^ 2 := by
  rw [qnorm_eq_iff]; push_cast; simp

@[simp] lemma qnorm_neg (a : IntegralQuaternion) : qnorm (-a) = qnorm a := by
  have : (qnorm (-a) : ℚ) = qnorm a := by
    rw [qnorm_cast, qnorm_cast, Subring.coe_neg, normSq_def', normSq_def']; simp
  exact_mod_cast this

lemma star_mem_integralQuaternions {a : ℍ[ℚ]} (h : a ∈ integralQuaternions) :
    star a ∈ integralQuaternions := by
  obtain ⟨k0, k1, k2, k3, rfl⟩ := h
  exact ⟨k0, -k0 - k1, -k0 - k2, -k0 - k3, by ext <;> simp <;> ring⟩

/-- The conjugate `ᾱ` of an integral quaternion (Hardy–Wright (20.6.6)). -/
def qconj (a : IntegralQuaternion) : IntegralQuaternion := ⟨star a, star_mem_integralQuaternions a.2⟩

@[simp] lemma coe_qconj (a : IntegralQuaternion) :
    ((qconj a : IntegralQuaternion) : ℍ[ℚ]) = star (a : ℍ[ℚ]) :=
  rfl

/-- `α ᾱ = Nα` (Hardy–Wright (20.6.5)). -/
lemma mul_qconj (a : IntegralQuaternion) : a * qconj a = (qnorm a : IntegralQuaternion) := by
  apply Subtype.ext
  rw [Subring.coe_mul, coe_qconj, self_mul_star, ← qnorm_cast]
  norm_cast

lemma qconj_mul (a : IntegralQuaternion) : qconj a * a = (qnorm a : IntegralQuaternion) := by
  apply Subtype.ext
  rw [Subring.coe_mul, coe_qconj, star_mul_self, ← qnorm_cast]
  norm_cast

@[simp] lemma qnorm_qconj (a : IntegralQuaternion) : qnorm (qconj a) = qnorm a := by
  have : (qnorm (qconj a) : ℚ) = qnorm a := by
    rw [qnorm_cast, qnorm_cast, coe_qconj, normSq_star]
  exact_mod_cast this

lemma qconj_mul_qconj (a b : IntegralQuaternion) : qconj (a * b) = qconj b * qconj a :=
  Subtype.ext (by simp only [coe_qconj, Subring.coe_mul, star_mul])

/-- **§ 20.6** (Hardy–Wright). An integral quaternion is a unity (`α` and `α⁻¹` both integral) if and
only if its norm is `1`. -/
@[kb "hardywright2008" "Section 20.6, p. 422"]
theorem isUnit_iff_qnorm_eq_one {a : IntegralQuaternion} : IsUnit a ↔ qnorm a = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have := congrArg qnorm u.mul_inv
    rw [qnorm_mul, qnorm_one] at this
    exact Nat.eq_one_of_mul_eq_one_right this
  · intro h
    refine ⟨⟨a, qconj a, ?_, ?_⟩, rfl⟩
    · rw [mul_qconj, h, Nat.cast_one]
    · rw [qconj_mul, h, Nat.cast_one]

/-- Associates have equal norms. -/
lemma qnorm_mul_unit {a ε : IntegralQuaternion} (hε : IsUnit ε) : qnorm (a * ε) = qnorm a := by
  rw [qnorm_mul, isUnit_iff_qnorm_eq_one.1 hε, mul_one]

lemma qnorm_unit_mul {a ε : IntegralQuaternion} (hε : IsUnit ε) : qnorm (ε * a) = qnorm a := by
  rw [qnorm_mul, isUnit_iff_qnorm_eq_one.1 hε, one_mul]

/-- Rational integers are central. -/
lemma natCast_mul_comm (m : ℕ) (a : IntegralQuaternion) : (m : IntegralQuaternion) * a = a * m :=
  (Nat.cast_commute m a)

/-! ### Theorem 371 -/

/-- An odd integer is `±1 + 4t`. -/
lemma exists_sign_add_four_mul {A : ℤ} (h : A % 2 = 1) :
    ∃ s t : ℤ, (s = 1 ∨ s = -1) ∧ A = s + 4 * t := by
  have : A % 4 = 1 ∨ A % 4 = 3 := by omega
  rcases this with h1 | h3
  · exact ⟨1, A / 4, Or.inl rfl, by omega⟩
  · exact ⟨-1, (A + 1) / 4, Or.inr rfl, by omega⟩

/-- **Theorem 371** (Hardy–Wright), first part. Every integral quaternion has an associate with
integral coordinates. -/
@[kb "hardywright2008" "Thm 371, p. 422"]
theorem exists_isUnit_hasIntCoords_mul (a : IntegralQuaternion) :
    ∃ ε : IntegralQuaternion, IsUnit ε ∧ HasIntCoords ((a * ε : IntegralQuaternion) : ℍ[ℚ]) := by
  obtain ⟨k0, k1, k2, k3, ha⟩ := a.2
  rcases Int.emod_two_eq_zero_or_one k0 with h0 | h1
  · -- integral coordinates already
    refine ⟨1, isUnit_one, ?_⟩
    obtain ⟨t, rfl⟩ : 2 ∣ k0 := Int.dvd_of_emod_eq_zero h0
    rw [mul_one, ha]
    exact ⟨t, t + k1, t + k2, t + k3, by ext <;> simp⟩
  · -- `α = γ + 2β` with `γ = ½(±1 ± i₁ ± i₂ ± i₃)` a unity and `β` with integral coordinates
    obtain ⟨s0, t0, hs0, e0⟩ := exists_sign_add_four_mul (A := k0) h1
    obtain ⟨s1, t1, hs1, e1⟩ := exists_sign_add_four_mul (A := k0 + 2 * k1) (by omega)
    obtain ⟨s2, t2, hs2, e2⟩ := exists_sign_add_four_mul (A := k0 + 2 * k2) (by omega)
    obtain ⟨s3, t3, hs3, e3⟩ := exists_sign_add_four_mul (A := k0 + 2 * k3) (by omega)
    have hsq : ∀ s : ℤ, (s = 1 ∨ s = -1) → (s : ℚ) ^ 2 = 1 := by
      rintro s (rfl | rfl) <;> norm_num
    let γq : ℍ[ℚ] := ⟨s0 / 2, s1 / 2, s2 / 2, s3 / 2⟩
    have hγ : γq ∈ integralQuaternions := by
      refine (mem_integralQuaternions_iff _).2 (Or.inr ⟨(s0 - 1) / 2, (s1 - 1) / 2, (s2 - 1) / 2,
        (s3 - 1) / 2, ?_⟩)
      have key : ∀ s : ℤ, (s = 1 ∨ s = -1) → ((((s - 1) / 2 : ℤ) : ℚ) + 2⁻¹ = s / 2) := by
        rintro s (rfl | rfl) <;> norm_num
      ext <;> simp [γq, key _ hs0, key _ hs1, key _ hs2, key _ hs3]
    let γ : IntegralQuaternion := ⟨γq, hγ⟩
    have hγn : qnorm γ = 1 := by
      rw [qnorm_eq_iff, normSq_def']
      simp only [γ, γq]
      have h0 := hsq _ hs0; have h1 := hsq _ hs1; have h2 := hsq _ hs2; have h3 := hsq _ hs3
      push_cast
      linear_combination (1 / 4 : ℚ) * (h0 + h1 + h2 + h3)
    refine ⟨qconj γ, isUnit_iff_qnorm_eq_one.2 (by rw [qnorm_qconj, hγn]), ?_⟩
    -- `α γ̄ = 1 + β (2γ̄)`
    let β : ℍ[ℚ] := ⟨t0, t1, t2, t3⟩
    have hdec : (a : ℍ[ℚ]) = γq + (2 : ℚ) • β := by
      rw [ha]
      ext <;> simp [γq, β, hurwitzMk]
      · rw [e0]; push_cast; ring
      · have : ((k0 + 2 * k1 : ℤ) : ℚ) = ((s1 + 4 * t1 : ℤ) : ℚ) := by rw [e1]
        push_cast at this; linarith
      · have : ((k0 + 2 * k2 : ℤ) : ℚ) = ((s2 + 4 * t2 : ℤ) : ℚ) := by rw [e2]
        push_cast at this; linarith
      · have : ((k0 + 2 * k3 : ℤ) : ℚ) = ((s3 + 4 * t3 : ℤ) : ℚ) := by rw [e3]
        push_cast at this; linarith
    have hγγ : γq * star γq = 1 := by
      have := mul_qconj γ
      rw [hγn, Nat.cast_one] at this
      exact congrArg Subtype.val this
    have hprod : ((a * qconj γ : IntegralQuaternion) : ℍ[ℚ]) = 1 + β * ((2 : ℚ) • star γq) := by
      rw [Subring.coe_mul, coe_qconj, hdec, add_mul, mul_smul_comm, smul_mul_assoc]
      exact congrArg (· + _) hγγ
    rw [hasIntCoords_iff_mem_lipschitz, hprod]
    refine add_mem (one_mem _) (mul_mem ⟨t0, t1, t2, t3, rfl⟩ ⟨s0, -s1, -s2, -s3, ?_⟩)
    ext <;> simp [γq] <;> ring

/-- A quaternion `α` with integral coordinates is odd (`Nα` odd) exactly when the sum of its
coordinates is odd, and then `αρ` has non-integral coordinates. -/
lemma not_hasIntCoords_mul_rho {b0 b1 b2 b3 : ℤ} (h : (b0 + b1 + b2 + b3) % 2 = 1) :
    ¬ HasIntCoords ((⟨b0, b1, b2, b3⟩ : ℍ[ℚ]) * ⟨1 / 2, 1 / 2, 1 / 2, 1 / 2⟩) := by
  rintro ⟨c0, c1, c2, c3, hc⟩
  have hre := congrArg QuaternionAlgebra.re hc
  simp at hre
  have : ((b0 - b1 - b2 - b3 : ℤ) : ℚ) = ((2 * c0 : ℤ) : ℚ) := by push_cast; linarith
  have := Int.cast_injective this
  omega

/-- **Theorem 371** (Hardy–Wright), second part. If `α` is odd (`Nα` odd), then `α` has an associate
with non-integral coordinates. -/
@[kb "hardywright2008" "Thm 371, p. 422"]
theorem exists_isUnit_not_hasIntCoords_mul {a : IntegralQuaternion} (ha : qnorm a % 2 = 1) :
    ∃ ε : IntegralQuaternion, IsUnit ε ∧ ¬ HasIntCoords ((a * ε : IntegralQuaternion) : ℍ[ℚ]) := by
  obtain ⟨ε, hε, b0, b1, b2, b3, hb⟩ := exists_isUnit_hasIntCoords_mul a
  -- the associate `αε = b` has integral coordinates and odd norm; multiply by `ρ`
  have hρ : (⟨1 / 2, 1 / 2, 1 / 2, 1 / 2⟩ : ℍ[ℚ]) ∈ integralQuaternions :=
    ⟨1, 0, 0, 0, by ext <;> simp⟩
  let ρ : IntegralQuaternion := ⟨_, hρ⟩
  have hρn : qnorm ρ = 1 := by rw [qnorm_eq_iff, normSq_def']; simp [ρ]; norm_num
  refine ⟨ε * ρ, hε.mul (isUnit_iff_qnorm_eq_one.2 hρn), ?_⟩
  rw [← mul_assoc, Subring.coe_mul, hb]
  apply not_hasIntCoords_mul_rho
  have hn : qnorm (a * ε) = qnorm a := qnorm_mul_unit hε
  have hq : ((qnorm (a * ε) : ℤ) : ℚ) = ((b0 ^ 2 + b1 ^ 2 + b2 ^ 2 + b3 ^ 2 : ℤ) : ℚ) := by
    rw [Int.cast_natCast, qnorm_cast, hb, normSq_def']; push_cast; ring
  have hq' := Int.cast_injective hq
  rw [hn] at hq'
  have : (b0 ^ 2 + b1 ^ 2 + b2 ^ 2 + b3 ^ 2) % 2 = 1 := by omega
  have e : ∀ x : ℤ, x ^ 2 % 2 = x % 2 := fun x => by
    rcases Int.emod_two_eq_zero_or_one x with h | h <;> simp [pow_two, Int.mul_emod, h]
  have := e b0; have := e b1; have := e b2; have := e b3
  omega

/-! ### Theorems 372 and 373 -/

lemma hurwitzMk_sub_mul (k0 k1 k2 k3 l0 l1 l2 l3 : ℤ) (m : ℕ) :
    hurwitzMk k0 k1 k2 k3 - (m : ℍ[ℚ]) * hurwitzMk l0 l1 l2 l3 =
      hurwitzMk (k0 - m * l0) (k1 - m * l1) (k2 - m * l2) (k3 - m * l3) := by
  ext <;> simp <;> ring

/-- **Theorem 372** (Hardy–Wright). If `κ` is an integral quaternion and `m` a positive integer, there
is an integral quaternion `λ` with `N(κ - mλ) < m²`. -/
@[kb "hardywright2008" "Thm 372, p. 423"]
theorem exists_qnorm_sub_natCast_mul_lt (κ : IntegralQuaternion) {m : ℕ} (hm : 0 < m) :
    ∃ l : IntegralQuaternion, qnorm (κ - (m : IntegralQuaternion) * l) < m ^ 2 := by
  obtain ⟨k0, k1, k2, k3, hκ⟩ := κ.2
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  obtain ⟨l0, hl0⟩ := exists_two_mul_abs_sub_le k0 m hm'
  obtain ⟨l1, hl1⟩ := exists_two_mul_abs_sub_le (k0 + 2 * k1 - m * l0) (2 * m) (by linarith)
  obtain ⟨l2, hl2⟩ := exists_two_mul_abs_sub_le (k0 + 2 * k2 - m * l0) (2 * m) (by linarith)
  obtain ⟨l3, hl3⟩ := exists_two_mul_abs_sub_le (k0 + 2 * k3 - m * l0) (2 * m) (by linarith)
  refine ⟨⟨hurwitzMk l0 l1 l2 l3, l0, l1, l2, l3, rfl⟩, ?_⟩
  have hcoe : ((κ - (m : IntegralQuaternion) * ⟨hurwitzMk l0 l1 l2 l3, l0, l1, l2, l3, rfl⟩ :
      IntegralQuaternion) : ℍ[ℚ]) =
      hurwitzMk (k0 - m * l0) (k1 - m * l1) (k2 - m * l2) (k3 - m * l3) := by
    rw [AddSubgroupClass.coe_sub, Subring.coe_mul, hκ, ← hurwitzMk_sub_mul]
    rfl
  have hN : ((qnorm (κ - (m : IntegralQuaternion) * ⟨hurwitzMk l0 l1 l2 l3, l0, l1, l2, l3, rfl⟩) :
      ℤ) : ℚ) = ((hurwitzNorm (k0 - m * l0) (k1 - m * l1) (k2 - m * l2) (k3 - m * l3) : ℤ) : ℚ) := by
    rw [Int.cast_natCast, qnorm_cast, hcoe, normSq_hurwitzMk]
  have hN' := Int.cast_injective hN
  have h4 := four_mul_hurwitzNorm (k0 - m * l0) (k1 - m * l1) (k2 - m * l2) (k3 - m * l3)
  -- the four doubled coordinates are bounded by `m/2, m, m, m`
  have b0 : 4 * (k0 - m * l0) ^ 2 ≤ (m : ℤ) ^ 2 := by
    have := abs_le.1 (show |2 * (k0 - m * l0)| ≤ m by rw [abs_mul]; simpa using hl0)
    nlinarith
  have bnd : ∀ c : ℤ, 2 * |c| ≤ 2 * m → c ^ 2 ≤ (m : ℤ) ^ 2 := fun c hc => by
    have := abs_le.1 (show |c| ≤ m by linarith)
    nlinarith
  have b1 := bnd (k0 - m * l0 + 2 * (k1 - m * l1)) (by
    have : k0 - ↑m * l0 + 2 * (k1 - ↑m * l1) = k0 + 2 * k1 - m * l0 - 2 * m * l1 := by ring
    rw [this]; exact hl1)
  have b2 := bnd (k0 - m * l0 + 2 * (k2 - m * l2)) (by
    have : k0 - ↑m * l0 + 2 * (k2 - ↑m * l2) = k0 + 2 * k2 - m * l0 - 2 * m * l2 := by ring
    rw [this]; exact hl2)
  have b3 := bnd (k0 - m * l0 + 2 * (k3 - m * l3)) (by
    have : k0 - ↑m * l0 + 2 * (k3 - ↑m * l3) = k0 + 2 * k3 - m * l0 - 2 * m * l3 := by ring
    rw [this]; exact hl3)
  have : (16 : ℤ) * (qnorm (κ - (m : IntegralQuaternion) *
      ⟨hurwitzMk l0 l1 l2 l3, l0, l1, l2, l3, rfl⟩) : ℤ) < 16 * (m : ℤ) ^ 2 := by
    rw [hN']; nlinarith
  exact_mod_cast (show ((qnorm _ : ℕ) : ℤ) < (m : ℤ) ^ 2 by linarith)

/-- **Theorem 373** (Hardy–Wright). If `α, β` are integral quaternions and `β ≠ 0`, there are integral
quaternions `λ, γ` with `α = λβ + γ` and `Nγ < Nβ`. -/
@[kb "hardywright2008" "Thm 373, p. 424"]
theorem exists_eq_mul_add_qnorm_lt (a : IntegralQuaternion) {b : IntegralQuaternion} (hb : b ≠ 0) :
    ∃ l c : IntegralQuaternion, a = l * b + c ∧ qnorm c < qnorm b := by
  have hm : 0 < qnorm b := qnorm_pos.2 hb
  obtain ⟨l, hl⟩ := exists_qnorm_sub_natCast_mul_lt (a * qconj b) hm
  refine ⟨l, a - l * b, by abel, ?_⟩
  have hkey : (a - l * b) * qconj b = a * qconj b - (qnorm b : IntegralQuaternion) * l := by
    rw [sub_mul, mul_assoc, mul_qconj, natCast_mul_comm]
  have := congrArg qnorm hkey
  rw [qnorm_mul, qnorm_qconj] at this
  rw [← this] at hl
  have : qnorm (a - l * b) * qnorm b < qnorm b * qnorm b := by rw [← sq]; exact hl
  exact lt_of_mul_lt_mul_right this (Nat.zero_le _)

end NTKB.HardyWright
