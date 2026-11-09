/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.QuadraticFields.RationalPrimes
import Mathlib.Algebra.QuadraticAlgebra.Int

/-!
# Arithmetic of `ℤ[ω]`, `ω² = a + bω`, from the norm (Hardy–Wright §§ 14.4, 14.7, 15.1)

Generic facts about Mathlib's `QuadraticAlgebra ℤ a b` used for `k(√2)` and `k(√5)`:

* `euclideanDomainOfNorm`: the Euclidean algorithm of § 12.8, § 14.7 (Theorem 245): a ring with a
  multiplicative integral norm `N` and the property (E), `|N(γ - κγ₁)| < |Nγ₁|`, is a Euclidean
  domain (hence has unique factorization).
* `exists_sub_mul_lt_of_round`: property (E) for `QuadraticAlgebra ℤ a b` follows from (E′) in the
  quadratic field `QuadraticAlgebra ℚ a b`.
* Theorem 241 (`qa_irreducible_of_natAbs_norm_prime`): an integer whose norm is `±` a rational prime
  is irreducible; Theorem 240 (`qa_isUnit_iff`): the unities are the integers of norm `±1`.
-/

namespace NTKB.HardyWright

open QuadraticAlgebra

/-- The Euclidean algorithm (§ 14.7, property (E)): a nontrivial commutative ring with a
multiplicative norm `N : R → ℤ`, `N x = 0 → x = 0`, such that for `y ≠ 0` there is `q` with
`|N(x - qy)| < |N y|`, is a Euclidean domain. -/
@[instance_reducible]
noncomputable def euclideanDomainOfNorm (R : Type*) [CommRing R] [Nontrivial R] (N : R → ℤ)
    (hmul : ∀ x y, N (x * y) = N x * N y) (h0 : ∀ x, N x = 0 → x = 0)
    (hdiv : ∀ x y, y ≠ 0 → ∃ q, |N (x - q * y)| < |N y|) : EuclideanDomain R := by
  classical
  exact
  { (inferInstance : CommRing R), (inferInstance : Nontrivial R) with
    quotient := fun x y ↦ if hy : y = 0 then 0 else (hdiv x y hy).choose
    quotient_zero := fun x ↦ by simp
    remainder := fun x y ↦ x - y * (if hy : y = 0 then 0 else (hdiv x y hy).choose)
    quotient_mul_add_remainder_eq := fun x y ↦ by ring
    r := fun a b ↦ (N a).natAbs < (N b).natAbs
    r_wellFounded := (measure fun a ↦ (N a).natAbs).wf
    remainder_lt := fun x y hy ↦ by
      simp only [hy, dite_false]
      have := (hdiv x y hy).choose_spec
      rw [mul_comm] at this
      zify
      simpa using this
    mul_left_not_lt := fun a b hb ↦ by
      simp only [hmul, Int.natAbs_mul, not_lt]
      have : 1 ≤ (N b).natAbs := Int.natAbs_pos.2 (fun h ↦ hb (h0 b h))
      exact Nat.le_mul_of_pos_right _ this }

variable {a b : ℤ}

lemma qa_norm_eq_zero [Fact (∀ r : ℚ, r ^ 2 ≠ a + b * r)] {x : QuadraticAlgebra ℤ a b}
    (h : norm x = 0) : x = 0 := by
  have h' : norm (algebraMap (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b) x) = 0 := by
    rw [QuadraticAlgebra.Int.norm_algebraMap_eq, h, Int.cast_zero]
  rw [norm_eq_zero_iff_eq_zero] at h'
  exact (FaithfulSMul.algebraMap_injective (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b))
    (by rw [h', map_zero])

/-- Property (E′) in the field gives property (E) in `ℤ[ω]`. -/
lemma exists_sub_mul_lt_of_round [Fact (∀ r : ℚ, r ^ 2 ≠ a + b * r)]
    (hround : ∀ ξ : QuadraticAlgebra ℚ a b, ∃ q : QuadraticAlgebra ℤ a b,
      |norm (ξ - algebraMap _ _ q)| < 1)
    (x y : QuadraticAlgebra ℤ a b) (hy : y ≠ 0) : ∃ q, |norm (x - q * y)| < |norm y| := by
  set f := algebraMap (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b)
  have hfy : f y ≠ 0 := fun h ↦ hy
    ((FaithfulSMul.algebraMap_injective (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b))
      (by rw [h, map_zero]))
  obtain ⟨q, hq⟩ := hround (f x / f y)
  refine ⟨q, ?_⟩
  have e : f (x - q * y) = (f x / f y - f q) * f y := by
    rw [map_sub, map_mul]; field_simp
  have hn : ((norm (x - q * y) : ℤ) : ℚ) = norm (f x / f y - f q) * norm (f y) := by
    rw [← QuadraticAlgebra.Int.norm_algebraMap_eq, e, map_mul]
  have hpos : 0 < |norm (f y)| := abs_pos.2 ((norm_eq_zero_iff_eq_zero).not.2 hfy)
  have hfy' : norm (f y) = ((norm y : ℤ) : ℚ) := QuadraticAlgebra.Int.norm_algebraMap_eq y
  have : |((norm (x - q * y) : ℤ) : ℚ)| < |((norm y : ℤ) : ℚ)| := by
    rw [hn, abs_mul, ← hfy']
    nlinarith [abs_nonneg (norm (f x / f y - f q))]
  exact_mod_cast this

lemma qa_isUnit_iff {x : QuadraticAlgebra ℤ a b} : IsUnit x ↔ (norm x).natAbs = 1 := by
  rw [isUnit_iff_norm_isUnit, Int.isUnit_iff_natAbs_eq]

/-- Theorem 241 in `ℤ[ω]`: an integer whose norm is `±` a rational prime is irreducible. -/
lemma qa_irreducible_of_natAbs_norm_prime {π : QuadraticAlgebra ℤ a b}
    (h : (norm π).natAbs.Prime) : Irreducible π := by
  refine ⟨fun hu ↦ ?_, fun x y hxy ↦ ?_⟩
  · rw [qa_isUnit_iff] at hu
    exact h.one_lt.ne' hu
  · rw [hxy, map_mul, Int.natAbs_mul] at h
    rcases Nat.prime_mul_iff.1 h with ⟨-, h1⟩ | ⟨-, h1⟩
    · exact Or.inr (qa_isUnit_iff.2 h1)
    · exact Or.inl (qa_isUnit_iff.2 h1)

/-- An integer of `ℤ[ω]` divides (the image of) its norm. -/
lemma qa_dvd_natAbs_norm (π : QuadraticAlgebra ℤ a b) :
    π ∣ (((norm π).natAbs : ℤ) : QuadraticAlgebra ℤ a b) := by
  have e : ((norm π : ℤ) : QuadraticAlgebra ℤ a b) = π * star π := by
    rw [← algebraMap_norm_eq_mul_star]; rfl
  rcases Int.natAbs_eq (norm π) with h | h
  · rw [← h, e]; exact dvd_mul_right _ _
  · rw [show ((norm π).natAbs : ℤ) = -norm π by omega, Int.cast_neg, e]
    exact (dvd_mul_right _ _).neg_right

lemma qa_norm_unit (u : (QuadraticAlgebra ℤ a b)ˣ) : (norm (u : QuadraticAlgebra ℤ a b)).natAbs = 1 :=
  qa_isUnit_iff.1 u.isUnit

lemma qa_natAbs_norm_eq_of_associated {π σ : QuadraticAlgebra ℤ a b} (h : Associated π σ) :
    (norm π).natAbs = (norm σ).natAbs := by
  obtain ⟨u, rfl⟩ := h
  rw [map_mul, Int.natAbs_mul, qa_norm_unit, mul_one]

/-- If `σ ∣ τ`, `σ ≠ 0` and `|Nσ| = |Nτ|`, then `σ` and `τ` are associated. -/
lemma qa_associated_of_dvd [Fact (∀ r : ℚ, r ^ 2 ≠ a + b * r)] {σ τ : QuadraticAlgebra ℤ a b}
    (hσ : σ ≠ 0) (h : σ ∣ τ) (hn : (norm σ).natAbs = (norm τ).natAbs) : Associated σ τ := by
  obtain ⟨k, rfl⟩ := h
  have : (norm k).natAbs = 1 := by
    rw [map_mul, Int.natAbs_mul] at hn
    have h0 : (norm σ).natAbs ≠ 0 := fun h ↦ hσ (qa_norm_eq_zero (Int.natAbs_eq_zero.1 h))
    exact (Nat.mul_eq_left h0).1 hn.symm
  exact ⟨(qa_isUnit_iff.2 this).unit, rfl⟩

/-- A prime `π` of `ℤ[ω]` divides a rational prime `p` with `|Nπ| = p` or `|Nπ| = p²`; in the latter
case `π` is associated with `p`. -/
lemma qa_prime_cases [Fact (∀ r : ℚ, r ^ 2 ≠ a + b * r)] {π : QuadraticAlgebra ℤ a b}
    (hπ : Prime π) : ∃ p : ℕ, p.Prime ∧ π ∣ (p : QuadraticAlgebra ℤ a b) ∧
      ((norm π).natAbs = p ∨ Associated π (p : QuadraticAlgebra ℤ a b)) := by
  have hn0 : (norm π).natAbs ≠ 0 := fun h ↦ hπ.ne_zero (qa_norm_eq_zero (Int.natAbs_eq_zero.1 h))
  obtain ⟨p, hp, hπp⟩ := exists_nat_prime_dvd hπ hn0 (by
    have := qa_dvd_natAbs_norm π; rwa [Int.cast_natCast] at this)
  refine ⟨p, hp, hπp, ?_⟩
  obtain ⟨l, hl⟩ := hπp
  have hN : (norm π).natAbs * (norm l).natAbs = p ^ 2 := by
    have h1 := congrArg (fun z ↦ (norm z).natAbs) hl
    simp only [map_mul, Int.natAbs_mul, QuadraticAlgebra.norm_natCast, Int.natAbs_pow,
      Int.natAbs_natCast] at h1
    rw [← h1]
  obtain ⟨k, hk, hkp⟩ := (Nat.dvd_prime_pow hp).1 (Dvd.intro _ hN)
  interval_cases k
  · exact absurd (qa_isUnit_iff.2 (by simpa using hkp)) hπ.not_isUnit
  · left; simpa using hkp
  · right
    have hl1 : (norm l).natAbs = 1 := by
      rw [hkp] at hN
      have : 0 < p ^ 2 := pow_pos hp.pos 2
      nlinarith
    exact ⟨(qa_isUnit_iff.2 hl1).unit, hl.symm⟩

end NTKB.HardyWright
