/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.QuadraticFields.QuadInt
import NTKB.Elementary.HardyWright.QuadraticFields.NormEuclidean
import NTKB.Elementary.HardyWright.Fermat.QuadraticResidues

/-!
# The primes of `k(ρ)` (Hardy–Wright § 15.3)

The integers of `k(ρ)`, `ρ = e^(2πi/3)`, are `a + bρ`; here they are Mathlib's
`QuadraticAlgebra ℤ (-1) (-1)` (`ρ² = -1 - ρ`), with norm `N(a + bρ) = a² - ab + b²`. (Chapter XIII
uses the isomorphic ring of integers `𝓞 K` of a cyclotomic field `K`, as Mathlib's proof of Fermat's
theorem for cubes does.)

* `instEuclideanDomainRho`: `k(ρ)` is Euclidean (Theorem 246, `m = -3`; Theorem 219).
* Theorem 254 (`exists_sq_sub_mul_add_sq`): a rational prime `3n + 1` is `a² - ab + b²`.
* Theorem 255 (`rho_prime_iff`): the primes of `k(ρ)` are `1 - ρ` and its associates, the rational
  primes `3n + 2` and their associates, and the factors `a + bρ` of the rational primes `3n + 1`.
-/

namespace NTKB.HardyWright

open QuadraticAlgebra

/-- The integers `a + bρ` of `k(ρ)`. -/
abbrev ZRho := QuadraticAlgebra ℤ (-1) (-1)

instance factRho : Fact (∀ r : ℚ, r ^ 2 ≠ ((-1 : ℤ) : ℚ) + ((-1 : ℤ) : ℚ) * r) :=
  ⟨fun r hr ↦ by push_cast at hr; nlinarith [sq_nonneg (r + 1 / 2)]⟩

lemma rho_norm (z : ZRho) : norm z = z.re ^ 2 - z.re * z.im + z.im ^ 2 := by
  rw [norm_def]; ring

lemma rho_norm_nonneg (z : ZRho) : 0 ≤ norm z := by
  rw [rho_norm]; nlinarith [sq_nonneg (z.re - z.im), sq_nonneg z.re, sq_nonneg z.im]

lemma rho_round (ξ : QuadraticAlgebra ℚ ((-1 : ℤ) : ℚ) ((-1 : ℤ) : ℚ)) :
    ∃ q : ZRho, |norm (ξ - algebraMap _ _ q)| < 1 := by
  set y := round ξ.im
  set x := round (ξ.re - (ξ.im - y) / 2)
  refine ⟨⟨x, y⟩, ?_⟩
  have h1 := sq_le_quarter (abs_sub_round (ξ.re - (ξ.im - y) / 2))
  have h2 := sq_le_quarter (abs_sub_round ξ.im)
  rw [norm_def, abs_lt]
  simp only [QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub,
    QuadraticAlgebra.Int.re_algebraMap, QuadraticAlgebra.Int.im_algebraMap]
  push_cast
  constructor <;> nlinarith [sq_nonneg (ξ.re - (ξ.im - y) / 2 - x), sq_nonneg (ξ.im - y)]

/-- `k(ρ)` is Euclidean; `ℤ[ρ]` is a Euclidean domain. -/
noncomputable instance instEuclideanDomainRho : EuclideanDomain ZRho :=
  euclideanDomainOfNorm ZRho QuadraticAlgebra.norm (map_mul QuadraticAlgebra.norm)
    (fun _ h ↦ qa_norm_eq_zero h) (exists_sub_mul_lt_of_round rho_round)

/-- `λ = 1 - ρ`. -/
def lamRho : ZRho := ⟨1, -1⟩

lemma rho_natAbs_norm_lam : (norm lamRho).natAbs = 3 := by
  rw [rho_norm]; rfl

/-- `3 = -ρ² λ²`. -/
lemma three_eq_lam : (3 : ZRho) = lamRho * (lamRho * ⟨1, 1⟩) := by
  ext <;> simp [lamRho]

lemma rho_prime_of_natAbs_norm_prime {π : ZRho} (h : (norm π).natAbs.Prime) : Prime π :=
  irreducible_iff_prime.1 (qa_irreducible_of_natAbs_norm_prime h)

/-- `a² - ab + b²` is never `2 (mod 3)` (`4N = (2a - b)² + 3b²`). -/
lemma rho_norm_mod_three (x y : ℤ) : (x ^ 2 - x * y + y ^ 2) % 3 ≠ 2 := by
  intro h
  have h' : ((x ^ 2 - x * y + y ^ 2 : ℤ) : ZMod 3) = ((2 : ℤ) : ZMod 3) := by
    rw [ZMod.intCast_eq_intCast_iff']; simpa using h
  push_cast at h'
  generalize (x : ZMod 3) = u at h'
  generalize (y : ZMod 3) = v at h'
  revert u v; decide

/-- A rational prime `p > 3` with `p ∣ c² + 3` is not a prime of `k(ρ)`: `c² + 3 = (c + √-3)(c - √-3)`,
`√-3 = 1 + 2ρ`. -/
lemma rho_not_prime_of_dvd {p : ℕ} (hp3 : 3 < p) {c : ℤ} (hc : (p : ℤ) ∣ c ^ 2 + 3) :
    ¬ Prime (p : ZRho) := by
  intro hpp
  have hdvd : (p : ZRho) ∣ (⟨c + 1, 2⟩ : ZRho) * ⟨c - 1, -2⟩ := by
    obtain ⟨t, ht⟩ := hc
    rw [show ((⟨c + 1, 2⟩ : ZRho) * ⟨c - 1, -2⟩) = ((c ^ 2 + 3 : ℤ) : ZRho) by
      ext <;> simp [sq] <;> ring, ht]
    push_cast
    exact dvd_mul_right _ _
  have hp1 : ¬ (p : ℤ) ∣ 2 := by
    intro h
    have := Int.le_of_dvd (by norm_num) h
    have : p ≤ 2 := by exact_mod_cast this
    omega
  rcases hpp.dvd_or_dvd hdvd with ⟨t, ht⟩ | ⟨t, ht⟩
  · apply hp1
    have := congrArg QuadraticAlgebra.im ht
    simp at this
    exact ⟨t.im, by linarith⟩
  · apply hp1
    have := congrArg QuadraticAlgebra.im ht
    simp at this
    exact ⟨-t.im, by linarith⟩

/-- For a rational prime `p ≡ 1 (mod 3)`, `p` is not a prime of `k(ρ)`. -/
lemma rho_not_prime_of_mod_three {p : ℕ} (hp : p.Prime) (hp3 : p % 3 = 1) : ¬ Prime (p : ZRho) := by
  have := Fact.mk hp
  have hp3' : 3 < p := by
    rcases (show p = 1 ∨ p = 4 ∨ 4 < p by omega) with h | h | h
    · exact absurd h hp.one_lt.ne'
    · subst h; norm_num at hp
    · omega
  have hp6 : p % 6 = 1 := by
    have := Nat.odd_iff.1 (hp.odd_of_ne_two (by omega)); omega
  obtain ⟨c, hc⟩ := (isSquare_neg_three_iff hp3').2 hp6
  refine rho_not_prime_of_dvd hp3' (c := c.val) ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 ?_)
  push_cast
  rw [ZMod.natCast_zmod_val, ← sq] at *
  rw [← hc]; ring

/-- **Theorem 254.** A rational prime `3n + 1` is expressible in the form `a² - ab + b²`. -/
@[kb "hardywright2008" "Thm 254, p. 306"]
theorem exists_sq_sub_mul_add_sq {p : ℕ} (hp : p.Prime) (hp3 : p % 3 = 1) :
    ∃ a b : ℤ, (p : ℤ) = a ^ 2 - a * b + b ^ 2 := by
  have hnp := rho_not_prime_of_mod_three hp hp3
  rw [← irreducible_iff_prime, irreducible_iff] at hnp
  push Not at hnp
  have hnu : ¬ IsUnit (p : ZRho) := by
    rw [qa_isUnit_iff, QuadraticAlgebra.norm_natCast]
    simp only [Int.natAbs_pow, Int.natAbs_natCast]
    intro h
    rw [pow_eq_one_iff] at h
    rcases h with h | h
    · exact hp.one_lt.ne' h
    · norm_num at h
  obtain ⟨α, β, hαβ, hα, hβ⟩ := hnp hnu
  have hN : (norm α).natAbs * (norm β).natAbs = p ^ 2 := by
    have := congrArg (fun z ↦ (QuadraticAlgebra.norm z).natAbs) hαβ
    simp only [map_mul, Int.natAbs_mul, QuadraticAlgebra.norm_natCast, Int.natAbs_pow,
      Int.natAbs_natCast] at this
    exact this.symm
  obtain ⟨k, hk, hkp⟩ := (Nat.dvd_prime_pow hp).1 (Dvd.intro _ hN)
  interval_cases k
  · exact absurd (qa_isUnit_iff.2 (by simpa using hkp)) hα
  · refine ⟨α.re, α.im, ?_⟩
    rw [← rho_norm, ← Int.natAbs_of_nonneg (rho_norm_nonneg α), hkp, pow_one]
  · exfalso
    rw [hkp] at hN
    have : 0 < p ^ 2 := pow_pos hp.pos 2
    exact hβ (qa_isUnit_iff.2 (by nlinarith))

/-- **Theorem 255.** The primes of `k(ρ)` are (1) `1 - ρ` and its associates, (2) the rational primes
`3n + 2` and their associates, (3) the factors `a + bρ` of the rational primes `p = 3n + 1`, i.e.
the integers of norm `p`. -/
@[kb "hardywright2008" "Thm 255, p. 306"]
theorem rho_prime_iff {π : ZRho} :
    Prime π ↔ Associated π lamRho ∨
      (∃ q : ℕ, q.Prime ∧ q % 3 = 2 ∧ Associated π (q : ZRho)) ∨
      ∃ p : ℕ, p.Prime ∧ p % 3 = 1 ∧ norm π = p := by
  have hN : ∀ z : ZRho, ((norm z).natAbs : ℤ) = norm z :=
    fun z ↦ Int.natAbs_of_nonneg (rho_norm_nonneg z)
  constructor
  · intro hπ
    obtain ⟨p, hp, hπp, hcase⟩ := qa_prime_cases hπ
    rcases hcase with hNπ | hassoc
    · by_cases h3 : p = 3
      · left
        subst h3
        have h3' : ((3 : ℕ) : ZRho) = lamRho * (lamRho * ⟨1, 1⟩) := by
          rw [← three_eq_lam]; rfl
        rw [h3'] at hπp
        have hl : π ∣ lamRho := by
          rcases hπ.dvd_or_dvd hπp with h | h
          · exact h
          · rcases hπ.dvd_or_dvd h with h | h
            · exact h
            · exfalso
              exact hπ.not_isUnit (isUnit_of_dvd_unit h (qa_isUnit_iff.2 (by rw [rho_norm]; rfl)))
        exact qa_associated_of_dvd hπ.ne_zero hl (by rw [hNπ, rho_natAbs_norm_lam])
      · right; right
        refine ⟨p, hp, ?_, by rw [← hN, hNπ]⟩
        have hm := rho_norm_mod_three π.re π.im
        rw [← rho_norm, ← hN, hNπ] at hm
        have h0 : p % 3 ≠ 0 := fun h0 ↦ h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
          (Nat.dvd_of_mod_eq_zero h0)).symm
        omega
    · right; left
      refine ⟨p, hp, ?_, hassoc⟩
      have hpp : Prime (p : ZRho) := hassoc.prime hπ
      have h3 : p ≠ 3 := by
        rintro rfl
        have h3' : ((3 : ℕ) : ZRho) = lamRho * (lamRho * ⟨1, 1⟩) := by
          rw [← three_eq_lam]; rfl
        have : ((3 : ℕ) : ZRho) ∣ lamRho := by
          rcases hpp.dvd_or_dvd (dvd_of_eq h3') with h | h
          · exact h
          · rcases hpp.dvd_or_dvd h with h | h
            · exact h
            · exact absurd (isUnit_of_dvd_unit h (qa_isUnit_iff.2 (by rw [rho_norm]; rfl)))
                hpp.not_isUnit
        obtain ⟨t, ht⟩ := this
        have := congrArg (fun z ↦ (norm z).natAbs) ht
        simp only [map_mul, Int.natAbs_mul, rho_natAbs_norm_lam, QuadraticAlgebra.norm_natCast,
          Int.natAbs_pow, Int.natAbs_natCast] at this
        omega
      have h1 : p % 3 ≠ 1 := fun h1 ↦ rho_not_prime_of_mod_three hp h1 hpp
      have h0 : p % 3 ≠ 0 := fun h0 ↦ h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
        (Nat.dvd_of_mod_eq_zero h0)).symm
      omega
  · rintro (h | ⟨q, hq, hq3, h⟩ | ⟨p, hp, -, h⟩)
    · exact h.symm.prime (rho_prime_of_natAbs_norm_prime (by
        rw [rho_natAbs_norm_lam]; norm_num))
    · refine h.symm.prime (irreducible_iff_prime.1 ⟨fun hu ↦ ?_, fun α β hαβ ↦ ?_⟩)
      · rw [qa_isUnit_iff, QuadraticAlgebra.norm_natCast] at hu
        simp at hu
        exact hq.one_lt.ne' (by simpa using hu)
      · have hNq := congrArg (fun z ↦ (QuadraticAlgebra.norm z).natAbs) hαβ
        simp only [map_mul, Int.natAbs_mul, QuadraticAlgebra.norm_natCast, Int.natAbs_pow,
          Int.natAbs_natCast] at hNq
        obtain ⟨k, hk, hkq⟩ := (Nat.dvd_prime_pow hq).1 (Dvd.intro _ hNq.symm)
        interval_cases k
        · exact Or.inl (qa_isUnit_iff.2 (by simpa using hkq))
        · exfalso
          have hm := rho_norm_mod_three α.re α.im
          rw [pow_one] at hkq
          rw [← rho_norm, ← hN, hkq] at hm
          omega
        · right
          rw [hkq] at hNq
          have : 0 < q ^ 2 := pow_pos hq.pos 2
          exact qa_isUnit_iff.2 (by nlinarith)
    · exact rho_prime_of_natAbs_norm_prime (by rw [h, Int.natAbs_natCast]; exact hp)

end NTKB.HardyWright
