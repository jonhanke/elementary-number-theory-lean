/-
Ireland–Rosen, Chapter 9, §1–§3: the ring `ℤ[ω]`, its primes and residue fields.
-/
import NTKB.Elementary.HardyWright.QuadraticFields.Eisenstein
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# The ring `ℤ[ω]` (Ireland–Rosen, Chapter 9, §1–§3)

`ℤ[ω]`, `ω = e^{2πi/3}`, is `NTKB.HardyWright.ZRho` (Mathlib's `QuadraticAlgebra ℤ (-1) (-1)`,
`ω² = -1 - ω`), already shown Euclidean with its primes listed (Hardy–Wright, Theorems 246 and 255).
Here: the units (Proposition 9.1.1), the primes (Propositions 9.1.2 and 9.1.4), the residue fields
(Proposition 9.2.1, and `toZMod`, the reduction modulo a prime of prime norm `p`), Fermat's little
theorem (Proposition 9.3.1) and primary primes (Proposition 9.3.5).

The book's `π ≡ 2 (mod 3)` for a primary prime is `IsPrimary π := 3 ∣ π - 2`.
-/

namespace NTKB.IrelandRosen

open NTKB.HardyWright QuadraticAlgebra

local notation "ℤ[ω]" => NTKB.HardyWright.ZRho

namespace Eisenstein

/-- `ω = e^{2πi/3}`, a root of `x² + x + 1`. -/
def omega : ℤ[ω] := ⟨0, 1⟩

lemma omega_sq : omega ^ 2 = -1 - omega := by
  ext <;> simp [omega, sq]

lemma omega_cube : omega ^ 3 = 1 := by
  ext <;> simp [omega, pow_succ]

lemma star_omega : star omega = omega ^ 2 := by
  ext <;> simp [omega, sq]

lemma eq_re_add_im (x : ℤ[ω]) : x = (x.re : ℤ[ω]) + (x.im : ℤ[ω]) * omega := by
  ext <;> simp [omega]

lemma natAbs_norm_star (x : ℤ[ω]) : (norm (star x)).natAbs = (norm x).natAbs := by
  rw [QuadraticAlgebra.norm_star]

lemma mul_star (x : ℤ[ω]) : x * star x = ((QuadraticAlgebra.norm x : ℤ) : ℤ[ω]) := by
  rw [← algebraMap_norm_eq_mul_star]; rfl

/-- `ω ^ 2` as a pair. -/
lemma omega_sq_eq : omega ^ 2 = ⟨-1, -1⟩ := by
  ext <;> simp [omega, sq]

lemma isUnit_omega : IsUnit omega :=
  IsUnit.of_mul_eq_one (omega ^ 2) (by rw [← pow_succ']; exact omega_cube)

/-- Divisibility implies divisibility of the norms. -/
lemma natAbs_norm_dvd {x y : ℤ[ω]} (h : x ∣ y) : (norm x).natAbs ∣ (norm y).natAbs := by
  obtain ⟨z, rfl⟩ := h
  rw [map_mul, Int.natAbs_mul]; exact dvd_mul_right _ _

lemma natAbs_norm_natCast (n : ℕ) : (norm (n : ℤ[ω])).natAbs = n ^ 2 := by
  simp [QuadraticAlgebra.norm_natCast, Int.natAbs_pow]

/-- **Proposition 9.1.1.** The units of `ℤ[ω]` are `±1, ±ω, ±ω²`. -/
@[kb "irelandrosen1990" "Prop 9.1.1, p. 120"]
theorem isUnit_iff_eq {u : ℤ[ω]} :
    IsUnit u ↔ u = 1 ∨ u = -1 ∨ u = omega ∨ u = -omega ∨ u = omega ^ 2 ∨ u = -omega ^ 2 := by
  constructor
  · intro h
    rw [qa_isUnit_iff] at h
    have h' : norm u = 1 := by have := rho_norm_nonneg u; omega
    rw [rho_norm] at h'
    have h1 : u.re ^ 2 ≤ 1 := by nlinarith [sq_nonneg (2 * u.im - u.re)]
    have h2 : u.im ^ 2 ≤ 1 := by nlinarith [sq_nonneg (2 * u.re - u.im)]
    have hr : -1 ≤ u.re ∧ u.re ≤ 1 := ⟨by nlinarith, by nlinarith⟩
    have hi : -1 ≤ u.im ∧ u.im ≤ 1 := ⟨by nlinarith, by nlinarith⟩
    obtain ⟨a, b⟩ := u
    simp only at hr hi h'
    obtain ⟨hr1, hr2⟩ := hr
    obtain ⟨hi1, hi2⟩ := hi
    rw [omega_sq_eq]
    interval_cases a <;> interval_cases b <;>
      simp_all [omega, QuadraticAlgebra.ext_iff]
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact isUnit_one
    · exact isUnit_one.neg
    · exact isUnit_omega
    · exact isUnit_omega.neg
    · exact isUnit_omega.pow 2
    · exact (isUnit_omega.pow 2).neg

/-- **Proposition 9.1.2.** A prime `π` of `ℤ[ω]` has `N π = p` or `N π = p²` for a rational
prime `p`; in the second case `π` is associate to `p`. -/
@[kb "irelandrosen1990" "Prop 9.1.2, p. 121"]
theorem prime_natAbs_norm_cases {π : ℤ[ω]} (hπ : Prime π) :
    ∃ p : ℕ, p.Prime ∧ π ∣ (p : ℤ[ω]) ∧
      ((norm π).natAbs = p ∨ ((norm π).natAbs = p ^ 2 ∧ Associated π (p : ℤ[ω]))) := by
  obtain ⟨p, hp, hπp, h⟩ := qa_prime_cases hπ
  refine ⟨p, hp, hπp, ?_⟩
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr ⟨by rw [qa_natAbs_norm_eq_of_associated h, natAbs_norm_natCast], h⟩

/-- **Proposition 9.1.3.** If `N π` is a rational prime, `π` is prime. -/
@[kb "irelandrosen1990" "Prop 9.1.3, p. 121"]
theorem prime_of_natAbs_norm_prime {π : ℤ[ω]} (h : (norm π).natAbs.Prime) : Prime π :=
  rho_prime_of_natAbs_norm_prime h

/-- **Proposition 9.1.4 (a).** A rational prime `q ≡ 2 (mod 3)` is prime in `ℤ[ω]`. -/
@[kb "irelandrosen1990" "Prop 9.1.4, p. 121"]
theorem prime_natCast_of_mod_three_eq_two {q : ℕ} (hq : q.Prime) (hq3 : q % 3 = 2) :
    Prime (q : ℤ[ω]) :=
  rho_prime_iff.2 (Or.inr (Or.inl ⟨q, hq, hq3, Associated.refl _⟩))

/-- A rational prime is neither `x²` nor (if `≡ 1 mod 3`) `3 x²`. -/
lemma natCast_ne_sq_and_three_mul_sq {p : ℕ} (hp : p.Prime) (hp3 : p % 3 = 1) (x : ℤ) :
    (p : ℤ) ≠ x ^ 2 ∧ (p : ℤ) ≠ 3 * x ^ 2 := by
  constructor
  · intro h
    have h' : p = x.natAbs ^ 2 := by
      have := congrArg Int.natAbs h
      simpa [Int.natAbs_pow] using this
    exact not_prime_pow (by norm_num) (Nat.prime_iff.1 (h' ▸ hp))
  · intro h
    omega

/-- **Proposition 9.1.4 (b).** A rational prime `p ≡ 1 (mod 3)` is `π π̄` with `π` prime and
`π`, `π̄` not associate. -/
@[kb "irelandrosen1990" "Prop 9.1.4, p. 121"]
theorem exists_prime_eq_mul_star {p : ℕ} (hp : p.Prime) (hp3 : p % 3 = 1) :
    ∃ π : ℤ[ω], Prime π ∧ (p : ℤ[ω]) = π * star π ∧ ¬ Associated π (star π) := by
  obtain ⟨a, b, hab⟩ := exists_sq_sub_mul_add_sq hp hp3
  have hN : norm (⟨a, b⟩ : ℤ[ω]) = p := by rw [rho_norm]; simpa using hab.symm
  have hNat : (norm (⟨a, b⟩ : ℤ[ω])).natAbs = p := by rw [hN]; simp
  refine ⟨⟨a, b⟩, rho_prime_of_natAbs_norm_prime (hNat ▸ hp), ?_, ?_⟩
  · rw [mul_star, hN]; simp
  · rintro ⟨u, hu⟩
    have key := natCast_ne_sq_and_three_mul_sq hp hp3
    have hu' := isUnit_iff_eq.1 u.isUnit
    have h1 := congrArg QuadraticAlgebra.re hu
    have h2 := congrArg QuadraticAlgebra.im hu
    rcases hu' with h | h | h | h | h | h <;> rw [h] at h1 h2 <;>
      simp [omega, sq] at h1 h2
    · have e : b = 0 := by omega
      subst e
      exact (key a).1 (by rw [hab]; ring)
    · have e : b = 2 * a := by omega
      subst e
      exact (key a).2 (by rw [hab]; ring)
    · have e : a = 0 := by omega
      subst e
      exact (key b).1 (by rw [hab]; ring)
    · have e : a = 2 * b := by omega
      subst e
      exact (key b).2 (by rw [hab]; ring)
    · have e : b = a := by omega
      subst e
      exact (key b).1 (by rw [hab]; ring)
    · have e : b = -a := by omega
      subst e
      exact (key a).2 (by rw [hab]; ring)

/-- **Proposition 9.1.4 (c).** `3 = -ω² (1 - ω)²` and `1 - ω` is prime. -/
@[kb "irelandrosen1990" "Prop 9.1.4, p. 121"]
theorem three_eq_and_prime_one_sub_omega :
    (3 : ℤ[ω]) = -omega ^ 2 * (1 - omega) ^ 2 ∧ Prime (1 - omega) := by
  constructor
  · ext <;> simp [omega, sq]
  · have : (1 - omega : ℤ[ω]) = lamRho := by ext <;> simp [omega, lamRho]
    rw [this]
    exact rho_prime_of_natAbs_norm_prime (by rw [rho_natAbs_norm_lam]; norm_num)

lemma isUnit_one_one : IsUnit (⟨1, 1⟩ : ℤ[ω]) := qa_isUnit_iff.2 (by rw [rho_norm]; rfl)

/-- For a prime `π`, `N π ≠ 3` iff `π` is not associate to `1 - ω`, iff `π ∤ 3`. -/
theorem natAbs_norm_ne_three_iff {π : ℤ[ω]} (hπ : Prime π) :
    (norm π).natAbs ≠ 3 ↔ ¬ π ∣ 3 := by
  constructor
  · intro h hd
    apply h
    rw [three_eq_lam] at hd
    have hl : π ∣ lamRho := by
      rcases hπ.dvd_or_dvd hd with h1 | h1
      · exact h1
      · rcases hπ.dvd_or_dvd h1 with h2 | h2
        · exact h2
        · exact absurd (isUnit_of_dvd_unit h2 isUnit_one_one) hπ.not_isUnit
    have := natAbs_norm_dvd hl
    rw [rho_natAbs_norm_lam] at this
    rcases (Nat.dvd_prime Nat.prime_three).1 this with h1 | h1
    · exact absurd (qa_isUnit_iff.2 h1) hπ.not_isUnit
    · exact h1
  · intro h hN
    apply h
    have := qa_dvd_natAbs_norm π
    rw [hN] at this
    simpa using this

/-- For a prime `π` with `N π ≠ 3`, `N π ≡ 1 (mod 3)`. -/
theorem natAbs_norm_mod_three {π : ℤ[ω]} (hπ : Prime π) (h3 : (norm π).natAbs ≠ 3) :
    (norm π).natAbs % 3 = 1 := by
  rcases rho_prime_iff.1 hπ with h | ⟨q, hq, hq3, h⟩ | ⟨p, hp, hp3, h⟩
  · exact absurd (by rw [qa_natAbs_norm_eq_of_associated h, rho_natAbs_norm_lam]) h3
  · rw [qa_natAbs_norm_eq_of_associated h, natAbs_norm_natCast, sq, Nat.mul_mod, hq3]
  · have : (norm π).natAbs = p := by rw [h]; simp
    omega

/-- `n ∣ x` in `ℤ[ω]` for `n` a rational integer iff `n` divides both coordinates. -/
lemma intCast_dvd_iff (n : ℤ) (x : ℤ[ω]) : (n : ℤ[ω]) ∣ x ↔ n ∣ x.re ∧ n ∣ x.im := by
  constructor
  · rintro ⟨y, rfl⟩
    simp
  · rintro ⟨⟨k, hk⟩, ⟨l, hl⟩⟩
    exact ⟨⟨k, l⟩, by ext <;> simp [hk, hl]⟩

/-- The cardinality of `ℤ[ω] ⧸ (x)` is `|N x|`. -/
lemma natCard_quotient_span (x : ℤ[ω]) :
    Nat.card (ℤ[ω] ⧸ Ideal.span {x}) = (norm x).natAbs := by
  have : IsDedekindDomain ℤ[ω] := IsPrincipalIdealRing.isDedekindDomain _
  have : Infinite ℤ[ω] := Module.Free.infinite ℤ ℤ[ω]
  have hx : Algebra.norm ℤ x = QuadraticAlgebra.norm x := by
    rw [Algebra.norm_eq_matrix_det (QuadraticAlgebra.basis (-1 : ℤ) (-1)), Matrix.det_fin_two]
    simp [Algebra.leftMulMatrix_eq_repr_mul, QuadraticAlgebra.basis_repr_apply, rho_norm]
    ring
  rw [← hx, ← Ideal.absNorm_span_singleton, Ideal.absNorm_eq_natCard]

/-- **Proposition 9.2.1.** For a prime `π`, `ℤ[ω]/π` is a field with `N π` elements. -/
@[kb "irelandrosen1990" "Prop 9.2.1, p. 122"]
theorem card_quotient {π : ℤ[ω]} (hπ : Prime π) :
    (Ideal.span {π}).IsMaximal ∧ Nat.card (ℤ[ω] ⧸ Ideal.span {π}) = (norm π).natAbs :=
  ⟨PrincipalIdealRing.isMaximal_of_irreducible hπ.irreducible, natCard_quotient_span π⟩

/-- Reduction modulo a prime `π` of prime norm `p`: a ring homomorphism `ℤ[ω] → ℤ/p` with
kernel `(π)`. -/
theorem exists_toZMod {π : ℤ[ω]} (hp : (norm π).natAbs.Prime) :
    ∃ f : ℤ[ω] →+* ZMod (norm π).natAbs, ∀ x, f x = 0 ↔ π ∣ x := by
  have hπ : Prime π := rho_prime_of_natAbs_norm_prime hp
  have := (card_quotient hπ).1
  letI : Field (ℤ[ω] ⧸ Ideal.span {π}) :=
    Ideal.Quotient.field (Ideal.span {π})
  have hcard := natCard_quotient_span π
  have : Finite (ℤ[ω] ⧸ Ideal.span {π}) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  letI := Fintype.ofFinite (ℤ[ω] ⧸ Ideal.span {π})
  have hc : Fintype.card (ℤ[ω] ⧸ Ideal.span {π}) = (norm π).natAbs := by
    rw [Fintype.card_eq_nat_card, hcard]
  let e := ZMod.ringEquivOfPrime (ℤ[ω] ⧸ Ideal.span {π}) hp hc
  refine ⟨e.symm.toRingHom.comp (Ideal.Quotient.mk _), fun x => ?_⟩
  rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]

/-- The reduction map of `exists_toZMod`. -/
noncomputable def toZMod {π : ℤ[ω]} (hp : (norm π).natAbs.Prime) :
    ℤ[ω] →+* ZMod (norm π).natAbs :=
  (exists_toZMod hp).choose

lemma toZMod_eq_zero_iff {π : ℤ[ω]} (hp : (norm π).natAbs.Prime) (x : ℤ[ω]) :
    toZMod hp x = 0 ↔ π ∣ x :=
  (exists_toZMod hp).choose_spec x

lemma toZMod_eq_iff {π : ℤ[ω]} (hp : (norm π).natAbs.Prime) (x y : ℤ[ω]) :
    toZMod hp x = toZMod hp y ↔ π ∣ x - y := by
  rw [← sub_eq_zero, ← map_sub, toZMod_eq_zero_iff]

/-- **Proposition 9.3.1.** If `π` is prime and `π ∤ α`, then `α ^ (N π - 1) ≡ 1 (mod π)`. -/
@[kb "irelandrosen1990" "Prop 9.3.1, p. 123"]
theorem pow_natAbs_norm_sub_one_modEq {π α : ℤ[ω]} (hπ : Prime π) (hα : ¬ π ∣ α) :
    π ∣ α ^ ((norm π).natAbs - 1) - 1 := by
  obtain ⟨hmax, hcard⟩ := card_quotient hπ
  have := hmax
  letI := Ideal.Quotient.field (Ideal.span {π})
  have : Finite (ℤ[ω] ⧸ Ideal.span {π}) := Nat.finite_of_card_ne_zero (by
    rw [hcard]; intro h; exact hπ.ne_zero (qa_norm_eq_zero (Int.natAbs_eq_zero.1 h)))
  letI := Fintype.ofFinite (ℤ[ω] ⧸ Ideal.span {π})
  have hne : Ideal.Quotient.mk (Ideal.span {π}) α ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have := FiniteField.pow_card_sub_one_eq_one _ hne
  rw [Fintype.card_eq_nat_card, hcard, ← map_pow, ← map_one (Ideal.Quotient.mk _),
    Ideal.Quotient.eq, Ideal.mem_span_singleton] at this
  exact this

/-- **Definition (§3).** `α` is primary if `α ≡ 2 (mod 3)`. -/
@[kb "irelandrosen1990" "Ch. 9, §3, Definition (primary), p. 124"]
def IsPrimary (α : ℤ[ω]) : Prop := (3 : ℤ[ω]) ∣ α - 2

/-- `a + bω` is primary iff `a ≡ 2` and `b ≡ 0 (mod 3)`. -/
theorem isPrimary_iff (α : ℤ[ω]) : IsPrimary α ↔ α.re % 3 = 2 ∧ α.im % 3 = 0 := by
  have := intCast_dvd_iff 3 (α - 2)
  rw [Int.cast_ofNat] at this
  unfold IsPrimary
  rw [this]
  simp only [QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub]
  simp
  omega

lemma IsPrimary.not_dvd_three {π α : ℤ[ω]} (hπ : Prime π) (hα : IsPrimary α) (h : π ∣ α) :
    ¬ π ∣ 3 := by
  intro h3
  have h2 : π ∣ α - 2 := h3.trans hα
  have h1 : π ∣ 1 := by
    have : π ∣ 3 - (α - (α - 2)) := dvd_sub h3 (dvd_sub h h2)
    convert this using 1; ring
  exact hπ.not_isUnit (isUnit_of_dvd_one h1)

lemma IsPrimary.star {α : ℤ[ω]} (h : IsPrimary α) : IsPrimary (star α) := by
  rw [isPrimary_iff] at *
  simp only [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
  omega

lemma isPrimary_intCast_iff (n : ℤ) : IsPrimary (n : ℤ[ω]) ↔ n % 3 = 2 := by
  rw [isPrimary_iff]; simp

/-- The primary condition on `u * α` for the six units `u`. -/
lemma isPrimary_unit_mul_iff (α : ℤ[ω]) :
    (IsPrimary (1 * α) ↔ α.re % 3 = 2 ∧ α.im % 3 = 0) ∧
    (IsPrimary (-1 * α) ↔ (-α.re) % 3 = 2 ∧ (-α.im) % 3 = 0) ∧
    (IsPrimary (omega * α) ↔ (-α.im) % 3 = 2 ∧ (α.re - α.im) % 3 = 0) ∧
    (IsPrimary (-omega * α) ↔ α.im % 3 = 2 ∧ (α.im - α.re) % 3 = 0) ∧
    (IsPrimary (omega ^ 2 * α) ↔ (α.im - α.re) % 3 = 2 ∧ (-α.re) % 3 = 0) ∧
    (IsPrimary (-omega ^ 2 * α) ↔ (α.re - α.im) % 3 = 2 ∧ α.re % 3 = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [isPrimary_iff] <;> simp [omega, sq] <;> omega

lemma exists_unit_mul_isPrimary {α : ℤ[ω]} (h : (α.re + α.im) % 3 ≠ 0) :
    ∃ v : ℤ[ω], IsUnit v ∧ IsPrimary (v * α) := by
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := isPrimary_unit_mul_iff α
  by_cases h1 : α.re % 3 = 2 ∧ α.im % 3 = 0
  · exact ⟨1, isUnit_one, c1.2 h1⟩
  by_cases h2 : (-α.re) % 3 = 2 ∧ (-α.im) % 3 = 0
  · exact ⟨-1, isUnit_one.neg, c2.2 h2⟩
  by_cases h3 : (-α.im) % 3 = 2 ∧ (α.re - α.im) % 3 = 0
  · exact ⟨omega, isUnit_omega, c3.2 h3⟩
  by_cases h4 : α.im % 3 = 2 ∧ (α.im - α.re) % 3 = 0
  · exact ⟨-omega, isUnit_omega.neg, c4.2 h4⟩
  by_cases h5 : (α.im - α.re) % 3 = 2 ∧ (-α.re) % 3 = 0
  · exact ⟨omega ^ 2, isUnit_omega.pow 2, c5.2 h5⟩
  · have h6 : (α.re - α.im) % 3 = 2 ∧ α.re % 3 = 0 := by
      clear c1 c2 c3 c4 c5 c6
      generalize α.re = a at *
      generalize α.im = b at *
      have ha : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
      have hb : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
      rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;> omega
    exact ⟨-omega ^ 2, (isUnit_omega.pow 2).neg, c6.2 h6⟩

lemma unit_eq_of_isPrimary {α u v : ℤ[ω]} (hu : IsUnit u) (hv : IsUnit v)
    (hu' : IsPrimary (u * α)) (hv' : IsPrimary (v * α)) : u = v := by
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := isPrimary_unit_mul_iff α
  rcases isUnit_iff_eq.1 hu with rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases isUnit_iff_eq.1 hv with rfl | rfl | rfl | rfl | rfl | rfl <;>
  first | rfl | (simp only [c1, c2, c3, c4, c5, c6] at hu' hv'; omega)

/-- **Proposition 9.3.5.** If `π` is prime with `N π ≠ 3`, exactly one associate of `π` is
primary. (The book states it for `N π = p ≡ 1 (mod 3)`; for `π` associate to a rational prime
`q ≡ 2 (mod 3)` the primary associate is `q`.) -/
@[kb "irelandrosen1990" "Prop 9.3.5, p. 124"]
theorem existsUnique_isPrimary_unit_mul {π : ℤ[ω]} (hπ : Prime π) (h3 : (norm π).natAbs ≠ 3) :
    ∃! u : ℤ[ω]ˣ, IsPrimary (u * π) := by
  have hmod := natAbs_norm_mod_three hπ h3
  have hN : ((norm π).natAbs : ℤ) = π.re ^ 2 - π.re * π.im + π.im ^ 2 := by
    rw [← rho_norm]; exact Int.natAbs_of_nonneg (rho_norm_nonneg π)
  have hs : (π.re + π.im) % 3 ≠ 0 := by
    intro h0
    obtain ⟨k, hk⟩ : (3 : ℤ) ∣ π.re + π.im := Int.dvd_of_emod_eq_zero h0
    have hb : π.im = 3 * k - π.re := by omega
    have : ((norm π).natAbs : ℤ) = 3 * (π.re ^ 2 - 3 * k * π.re + 3 * k ^ 2) := by
      rw [hN, hb]; ring
    omega
  obtain ⟨v, hv, hvp⟩ := exists_unit_mul_isPrimary hs
  refine ⟨hv.unit, ?_, fun u hu => ?_⟩
  · simpa using hvp
  · exact Units.ext (unit_eq_of_isPrimary u.isUnit hv hu (by simpa using hvp))

end Eisenstein

end NTKB.IrelandRosen
