/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Attr
import NTKB.Elementary.HardyWright.QuadraticFields.Cubes
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Lemmas 9.30–9.34 on `x³ + y³ = z³` in `ℚ(√-3)` (Niven–Zuckerman–Montgomery, § 9.10)

The field `ℚ(√-3)` is modelled, as in `NTKB.HardyWright.CubeDescent`, by a number field `K` with
`IsCyclotomicExtension {3} ℚ K`; `ω = ζ` is a primitive cube root of unity, `λ = ζ - 1` is Mathlib's
prime above `3`, and the book's prime `θ = √-3 = ω - ω²` (`theta`) is an associate of `λ`
(`theta_associated`); also `θ² = -3` (`theta_sq`).  Divisibility by `θ` is transported to
divisibility by `λ` (`theta_dvd_iff`, `theta_pow_dvd_iff`) and the results of Mathlib
(`lambda_dvd_or_dvd_sub_one_or_dvd_add_one`, `lambda_pow_four_dvd_cube_sub_one_of_dvd_sub_one`,
`eq_one_or_neg_one_of_unit_of_congruent`) and of `NTKB.HardyWright.CubeDescent` (`not_sol`) are used.

* Lemma 9.30 (`lemma_9_30`), Lemma 9.31 (`lemma_9_31_sub_one`, `lemma_9_31_add_one`,
  `lemma_9_31_cube_add`, `lemma_9_31_cube_sub`), Lemma 9.32 (`lemma_9_32`),
  Lemma 9.33 (`lemma_9_33`), Lemma 9.34 (`lemma_9_34`).
* Theorem 9.29 is stated as the proposition `Theorem929` (not proved).

Deviations.  "g.c.d. `(a, b, c) = 1`" is phrased as: every common divisor is a unit.  The "exactly
one" of Lemma 9.30 is stated with explicit exclusion clauses.  Lemma 9.34 is stated with the
normalisations the book says one may presume (`a, b` coprime, `θ ∤ c`), and for every `r ≥ 2`
(indeed the proof works for `r ≥ 1`); the reduction to this case, by dividing by the g.c.d.,
is not formalised.  Lemma 9.34 is derived from the descent `NTKB.HardyWright.CubeDescent.not_sol`
rather than re-proved.
-/

namespace NTKB.NZM

open NumberField IsCyclotomicExtension.Rat.Three NTKB.HardyWright NTKB.HardyWright.CubeDescent

section field

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]
  {ζ : K} (hζ : IsPrimitiveRoot ζ 3)

local notation3 "η" => (IsPrimitiveRoot.isUnit (hζ.toInteger_isPrimitiveRoot) (by decide)).unit
local notation3 "λ" => hζ.toInteger - 1

/-- The prime `θ = √-3 = ω - ω²` of the book (§ 9.10), as an element of `𝓞 K`. -/
noncomputable def theta : 𝓞 K := hζ.toInteger - hζ.toInteger ^ 2

local notation3 "θ" => theta hζ

lemma theta_eq : θ = -(η : 𝓞 K) * λ := by
  simp only [theta, coe_eta]; ring

/-- `θ² = -3`, i.e. `θ = √-3`. -/
lemma theta_sq : θ ^ 2 = -3 := by
  rw [theta_eq (hζ := hζ), mul_pow, lambda_sq_eq (hζ := hζ)]
  linear_combination (-3 : 𝓞 K) * eta_cube (hζ := hζ)

/-- `θ` and `λ` are associates (equation (9.14)). -/
lemma theta_associated : Associated (λ) θ :=
  ⟨-η, by rw [theta_eq (hζ := hζ), Units.val_neg]; ring⟩

lemma theta_ne_zero : θ ≠ 0 := by
  rw [theta_eq (hζ := hζ)]
  exact mul_ne_zero (neg_ne_zero.2 (Units.ne_zero _)) (lambda_prime (hζ := hζ)).ne_zero

lemma theta_pow_dvd_iff (n : ℕ) {x : 𝓞 K} : θ ^ n ∣ x ↔ λ ^ n ∣ x :=
  (((theta_associated (hζ := hζ)).pow_pow (n := n)).dvd_iff_dvd_left).symm

lemma theta_dvd_iff {x : 𝓞 K} : θ ∣ x ↔ λ ∣ x :=
  ((theta_associated (hζ := hζ)).dvd_iff_dvd_left).symm

lemma theta_not_isUnit : ¬ IsUnit θ := fun hu ↦
  lambda_not_dvd_one (hζ := hζ) ((theta_dvd_iff (hζ := hζ)).1 hu.dvd)

/-- **Lemma 9.30.** Every integer of `ℚ(√-3)` is congruent to exactly one of `0, 1, -1`
modulo `θ`. -/
@[kb "nivenzuckermanmontgomery" "Lemma 9.30, p. 441"]
theorem lemma_9_30 (ξ : 𝓞 K) :
    (θ ∣ ξ ∨ θ ∣ ξ - 1 ∨ θ ∣ ξ + 1) ∧ ¬ (θ ∣ ξ ∧ θ ∣ ξ - 1) ∧ ¬ (θ ∣ ξ ∧ θ ∣ ξ + 1) ∧
      ¬ (θ ∣ ξ - 1 ∧ θ ∣ ξ + 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [theta_dvd_iff (hζ := hζ), theta_dvd_iff (hζ := hζ), theta_dvd_iff (hζ := hζ)]
    exact lambda_dvd_or_dvd_sub_one_or_dvd_add_one hζ ξ
  · rintro ⟨h1, h2⟩
    rw [theta_dvd_iff (hζ := hζ)] at h1 h2
    apply lambda_not_dvd_one (hζ := hζ)
    convert dvd_sub h1 h2 using 1; ring
  · rintro ⟨h1, h2⟩
    rw [theta_dvd_iff (hζ := hζ)] at h1 h2
    apply lambda_not_dvd_one (hζ := hζ)
    convert dvd_sub h2 h1 using 1; ring
  · rintro ⟨h1, h2⟩
    rw [theta_dvd_iff (hζ := hζ)] at h1 h2
    apply lambda_not_dvd_two (hζ := hζ)
    convert dvd_sub h2 h1 using 1; ring

/-- **Lemma 9.31** (first part): `ξ ≡ 1 (mod θ)` implies `ξ³ ≡ 1 (mod θ⁴)`. -/
@[kb "nivenzuckermanmontgomery" "Lemma 9.31, p. 441"]
theorem lemma_9_31_sub_one {x : 𝓞 K} (h : θ ∣ x - 1) : θ ^ 4 ∣ x ^ 3 - 1 := by
  rw [theta_pow_dvd_iff (hζ := hζ)]
  rw [theta_dvd_iff (hζ := hζ)] at h
  exact lambda_pow_four_dvd_cube_sub_one_of_dvd_sub_one hζ h

/-- **Lemma 9.31** (second part): `ξ ≡ -1 (mod θ)` implies `ξ³ ≡ -1 (mod θ⁴)`. -/
@[kb "nivenzuckermanmontgomery" "Lemma 9.31, p. 441"]
theorem lemma_9_31_add_one {x : 𝓞 K} (h : θ ∣ x + 1) : θ ^ 4 ∣ x ^ 3 + 1 := by
  rw [theta_pow_dvd_iff (hζ := hζ)]
  rw [theta_dvd_iff (hζ := hζ)] at h
  exact lambda_pow_four_dvd_cube_add_one_of_dvd_add_one hζ h

/-- **Lemma 9.31** (third part): if `θ ∤ x, y` and `θ ∣ x³ + y³` then `θ⁴ ∣ x³ + y³`. -/
@[kb "nivenzuckermanmontgomery" "Lemma 9.31, p. 441"]
theorem lemma_9_31_cube_add {x y : 𝓞 K} (hx : ¬ θ ∣ x) (hy : ¬ θ ∣ y) (h : θ ∣ x ^ 3 + y ^ 3) :
    θ ^ 4 ∣ x ^ 3 + y ^ 3 := by
  rw [theta_dvd_iff (hζ := hζ)] at hx hy h
  rw [theta_pow_dvd_iff (hζ := hζ)]
  rcases not_dvd_or_pow_four_dvd (hζ := hζ) hx hy with h' | h'
  · exact absurd h h'
  · exact h'

/-- **Lemma 9.31** (fourth part): if `θ ∤ x, y` and `θ ∣ x³ - y³` then `θ⁴ ∣ x³ - y³`. -/
@[kb "nivenzuckermanmontgomery" "Lemma 9.31, p. 441"]
theorem lemma_9_31_cube_sub {x y : 𝓞 K} (hx : ¬ θ ∣ x) (hy : ¬ θ ∣ y) (h : θ ∣ x ^ 3 - y ^ 3) :
    θ ^ 4 ∣ x ^ 3 - y ^ 3 := by
  have e : x ^ 3 - y ^ 3 = x ^ 3 + (-y) ^ 3 := by ring
  rw [e] at h ⊢
  exact lemma_9_31_cube_add (hζ := hζ) hx (fun h' ↦ hy (dvd_neg.1 h')) h

/-- If `θ ∤ x` then `x³ ≡ e (mod λ⁴)` for `e = ±1` (an integer). -/
lemma cube_cong_int {x : 𝓞 K} (hx : ¬ θ ∣ x) :
    ∃ e : ℤ, (e = 1 ∨ e = -1) ∧ λ ^ 4 ∣ x ^ 3 - (e : 𝓞 K) := by
  rw [theta_dvd_iff (hζ := hζ)] at hx
  rcases cube_congr (hζ := hζ) hx with h | h
  · exact ⟨1, Or.inl rfl, by rw [Int.cast_one]; exact h⟩
  · exact ⟨-1, Or.inr rfl, by rw [Int.cast_neg, Int.cast_one, sub_neg_eq_add]; exact h⟩

lemma dvd_third {x y z : 𝓞 K} (h : x ^ 3 + y ^ 3 + z ^ 3 = 0) (hx : θ ∣ x) (hy : θ ∣ y) :
    θ ∣ z := by
  rw [theta_dvd_iff (hζ := hζ)] at hx hy ⊢
  have e : z ^ 3 = -(x ^ 3 + y ^ 3) := by linear_combination h
  have : λ ∣ z ^ 3 := by
    rw [e]; exact dvd_neg.2 (dvd_add (dvd_pow hx (by norm_num)) (dvd_pow hy (by norm_num)))
  exact (lambda_prime (hζ := hζ)).dvd_of_dvd_pow this

lemma exists_dvd_of_cube_sum {a b c : 𝓞 K} (h : a ^ 3 + b ^ 3 + c ^ 3 = 0) :
    θ ∣ a ∨ θ ∣ b ∨ θ ∣ c := by
  by_contra hn
  push_neg at hn
  obtain ⟨ha, hb, hc⟩ := hn
  obtain ⟨e1, he1, d1⟩ := cube_cong_int (hζ := hζ) ha
  obtain ⟨e2, he2, d2⟩ := cube_cong_int (hζ := hζ) hb
  obtain ⟨e3, he3, d3⟩ := cube_cong_int (hζ := hζ) hc
  have hd : λ ^ 4 ∣ -(((e1 + e2 + e3 : ℤ)) : 𝓞 K) := by
    have := dvd_add (dvd_add d1 d2) d3
    convert this using 1
    push_cast
    linear_combination (-1 : 𝓞 K) * h
  rw [dvd_neg] at hd
  have h1 := lambda_pow_four_not_dvd_one hζ
  have h3 := lambda_pow_four_not_dvd_three hζ
  rcases he1 with rfl | rfl <;> rcases he2 with rfl | rfl <;> rcases he3 with rfl | rfl <;>
    push_cast at hd
  · apply h3; convert hd using 1 <;> norm_num
  · apply h1; convert hd using 1 <;> norm_num
  · apply h1; convert hd using 1 <;> norm_num
  · apply h1; convert (dvd_neg.2 hd) using 1 <;> norm_num
  · apply h1; convert hd using 1 <;> norm_num
  · apply h1; convert (dvd_neg.2 hd) using 1 <;> norm_num
  · apply h1; convert (dvd_neg.2 hd) using 1 <;> norm_num
  · apply h3; convert (dvd_neg.2 hd) using 1 <;> norm_num

/-- **Lemma 9.32.** If `a³ + b³ + c³ = 0` with `gcd (a, b, c) = 1` (every common divisor is a unit)
then `θ` divides one and only one of `a, b, c`. -/
@[kb "nivenzuckermanmontgomery" "Lemma 9.32, p. 442"]
theorem lemma_9_32 {a b c : 𝓞 K} (h : a ^ 3 + b ^ 3 + c ^ 3 = 0)
    (hgcd : ∀ d : 𝓞 K, d ∣ a → d ∣ b → d ∣ c → IsUnit d) :
    (θ ∣ a ∧ ¬ θ ∣ b ∧ ¬ θ ∣ c) ∨ (¬ θ ∣ a ∧ θ ∣ b ∧ ¬ θ ∣ c) ∨
      (¬ θ ∣ a ∧ ¬ θ ∣ b ∧ θ ∣ c) := by
  have hab : b ^ 3 + c ^ 3 + a ^ 3 = 0 := by linear_combination h
  have hac : a ^ 3 + c ^ 3 + b ^ 3 = 0 := by linear_combination h
  by_cases hA : θ ∣ a <;> by_cases hB : θ ∣ b <;> by_cases hC : θ ∣ c
  · exact absurd (hgcd θ hA hB hC) (theta_not_isUnit (hζ := hζ))
  · exact absurd (dvd_third (hζ := hζ) h hA hB) hC
  · exact absurd (dvd_third (hζ := hζ) hac hA hC) hB
  · exact Or.inl ⟨hA, hB, hC⟩
  · exact absurd (dvd_third (hζ := hζ) hab hB hC) hA
  · exact Or.inr (Or.inl ⟨hA, hB, hC⟩)
  · exact Or.inr (Or.inr ⟨hA, hB, hC⟩)
  · exact absurd (exists_dvd_of_cube_sum (hζ := hζ) h) (by tauto)

/-- **Lemma 9.33.** If `a³ + ε₁ b³ + ε₂ (θ^r c)³ = 0` with `r > 0` and `θ ∤ a b c`, for units
`ε₁, ε₂`, then `ε₁ = ±1` and `r ≥ 2`. -/
@[kb "nivenzuckermanmontgomery" "Lemma 9.33, p. 442"]
theorem lemma_9_33 {a b c : 𝓞 K} {u v : (𝓞 K)ˣ} {r : ℕ} (hr : 0 < r)
    (ha : ¬ θ ∣ a) (hb : ¬ θ ∣ b) (hc : ¬ θ ∣ c)
    (h : a ^ 3 + u * b ^ 3 + v * (θ ^ r * c) ^ 3 = 0) :
    (u = 1 ∨ u = -1) ∧ 2 ≤ r := by
  have hdiv : θ ^ 3 ∣ (θ ^ r * c) ^ 3 := by
    rw [mul_pow]
    exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd (dvd_pow_self θ hr.ne') 3) _
  have h3 : λ ^ 3 ∣ a ^ 3 + u * b ^ 3 := by
    have e : a ^ 3 + u * b ^ 3 = -(v * (θ ^ r * c) ^ 3) := by linear_combination h
    rw [e, dvd_neg]
    exact Dvd.dvd.mul_left ((theta_pow_dvd_iff (hζ := hζ) 3).1 hdiv) _
  obtain ⟨ea, hea, da⟩ := cube_cong_int (hζ := hζ) ha
  obtain ⟨eb, heb, db⟩ := cube_cong_int (hζ := hζ) hb
  have hsq : (eb : 𝓞 K) ^ 2 = 1 := by rcases heb with rfl | rfl <;> simp
  have h34 : λ ^ 3 ∣ λ ^ 4 := pow_dvd_pow _ (by norm_num)
  have h4 : λ ^ 3 ∣ (ea : 𝓞 K) + u * eb := by
    have e : (ea : 𝓞 K) + u * eb = (a ^ 3 + u * b ^ 3) - (a ^ 3 - ea) - u * (b ^ 3 - eb) := by
      ring
    rw [e]
    exact dvd_sub (dvd_sub h3 (h34.trans da)) (Dvd.dvd.mul_left (h34.trans db) _)
  have h5 : λ ^ 2 ∣ (u : 𝓞 K) - ((-ea * eb : ℤ) : 𝓞 K) := by
    have e : (u : 𝓞 K) - ((-ea * eb : ℤ) : 𝓞 K) = eb * (ea + u * eb) := by
      push_cast; linear_combination (-(u : 𝓞 K)) * hsq
    rw [e]
    exact Dvd.dvd.mul_left ((pow_dvd_pow _ (by norm_num)).trans h4) _
  have hu := eq_one_or_neg_one_of_unit_of_congruent hζ u ⟨-ea * eb, h5⟩
  refine ⟨hu, ?_⟩
  by_contra hlt
  have hr1 : r = 1 := by omega
  subst hr1
  rw [pow_one] at h
  have hθ0 := theta_ne_zero (hζ := hζ)
  have key : ∀ b' : 𝓞 K, ¬ θ ∣ b' → a ^ 3 + b' ^ 3 = -(v * (θ * c) ^ 3) → False := by
    intro b' hb' h'
    have hd0 : θ ∣ a ^ 3 + b' ^ 3 := by
      rw [h']
      exact dvd_neg.2 (Dvd.dvd.mul_left (dvd_pow (dvd_mul_right θ c) (by norm_num)) _)
    have hd := lemma_9_31_cube_add (hζ := hζ) ha hb' hd0
    have e : -(v * (θ * c) ^ 3) = θ ^ 3 * (-(v * c ^ 3)) := by ring
    have hd' : θ ^ 3 * θ ∣ θ ^ 3 * (-(v * c ^ 3)) := by
      rw [← pow_succ]; rwa [h', e] at hd
    have h6 := (mul_dvd_mul_iff_left (pow_ne_zero 3 hθ0)).1 hd'
    rw [dvd_neg, Units.dvd_mul_left, theta_dvd_iff (hζ := hζ)] at h6
    exact hc ((theta_dvd_iff (hζ := hζ)).2 ((lambda_prime (hζ := hζ)).dvd_of_dvd_pow h6))
  rcases hu with hu | hu
  · refine key b hb ?_
    rw [hu, Units.val_one] at h
    linear_combination h
  · refine key (-b) (fun h' ↦ hb (dvd_neg.1 h')) ?_
    rw [hu, Units.val_neg, Units.val_one] at h
    linear_combination h

/-- **Lemma 9.34.** There are no `a, b, c` with `a, b` coprime, `θ ∤ c`, a unit `ε` and an integer
`r ≥ 2` such that `a³ + b³ + ε (θ^r c)³ = 0`. -/
@[kb "nivenzuckermanmontgomery" "Lemma 9.34, p. 443"]
theorem lemma_9_34 {a b c : 𝓞 K} {u : (𝓞 K)ˣ} {r : ℕ} (hr : 2 ≤ r) (hab : IsCoprime a b)
    (hc : ¬ θ ∣ c) : a ^ 3 + b ^ 3 + u * (θ ^ r * c) ^ 3 ≠ 0 := by
  intro h
  have hthl : θ = λ * (-(η : 𝓞 K)) := by rw [theta_eq (hζ := hζ)]; ring
  have hlth : λ ∣ u * (θ ^ r * c) ^ 3 := by
    refine Dvd.dvd.mul_left (dvd_pow (Dvd.dvd.mul_right (dvd_pow ?_ (by omega)) _) (by norm_num)) _
    exact (theta_dvd_iff (hζ := hζ)).1 dvd_rfl
  have ha : ¬ λ ∣ a := fun hla ↦ by
    have e : b ^ 3 = -(u * (θ ^ r * c) ^ 3) - a ^ 3 := by linear_combination h
    have : λ ∣ b ^ 3 := by
      rw [e]; exact dvd_sub (dvd_neg.2 hlth) (dvd_pow hla (by norm_num))
    exact (lambda_prime (hζ := hζ)).not_isUnit
      (hab.isUnit_of_dvd' hla ((lambda_prime (hζ := hζ)).dvd_of_dvd_pow this))
  have hb : ¬ λ ∣ b := fun hlb ↦ by
    have e : a ^ 3 = -(u * (θ ^ r * c) ^ 3) - b ^ 3 := by linear_combination h
    have : λ ∣ a ^ 3 := by
      rw [e]; exact dvd_sub (dvd_neg.2 hlth) (dvd_pow hlb (by norm_num))
    exact (lambda_prime (hζ := hζ)).not_isUnit
      (hab.isUnit_of_dvd' ((lambda_prime (hζ := hζ)).dvd_of_dvd_pow this) hlb)
  have hw : ¬ λ ∣ c := fun h' ↦ hc ((theta_dvd_iff (hζ := hζ)).2 h')
  let U : (𝓞 K)ˣ := -u * (-η) ^ (3 * r)
  have hH : a ^ 3 + b ^ 3 = U * λ ^ (3 * r) * c ^ 3 := by
    have e : a ^ 3 + b ^ 3 = -(u * (θ ^ r * c) ^ 3) := by linear_combination h
    rw [e, hthl]
    simp only [U, Units.val_mul, Units.val_neg, Units.val_pow_eq_pow_val]
    generalize hζ.toInteger - 1 = L
    generalize ((η : (𝓞 K)ˣ) : 𝓞 K) = E
    rw [mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm r 3]
    ring
  exact not_sol (hζ := hζ) (3 * r) (by omega) (by omega) ⟨a, b, c, U, ha, hb, hw, hab, hH⟩

end field

/-- **Theorem 9.29** (statement only): for a quadratic field `K = ℚ(√m)` (`m` squarefree, `m ≠ 1`)
whose ring of integers has unique factorisation, (A) every rational prime is a prime or a product
of two primes of `𝓞 K`; (C) for odd `p ∤ m`, `p` is a product of two primes iff `(m/p) = 1`, and
then the two primes are not associates; (D) the behaviour of `2` according to `m mod 8`;
(E) a prime `p ∣ m` is an associate of the square of a prime.  Part (B) (that these primes and
their associates are all the primes of `𝓞 K`) is not included.  Part (A) is proved as
`prime_or_mul_of_finrank_two` (`QuadraticSplitting.lean`). -/
@[kb "nivenzuckermanmontgomery" "Thm 9.29, p. 433"]
def Theorem929 (K : Type*) [Field K] [NumberField K] (m : ℤ) : Prop :=
  Squarefree m → m ≠ 1 → (∃ s : K, s ^ 2 = (m : K)) → Module.finrank ℚ K = 2 →
    UniqueFactorizationMonoid (𝓞 K) →
    (∀ p : ℕ, p.Prime →
      Prime (p : 𝓞 K) ∨ ∃ π₁ π₂ : 𝓞 K, Prime π₁ ∧ Prime π₂ ∧ (p : 𝓞 K) = π₁ * π₂) ∧
    (∀ p : ℕ, p.Prime → p ≠ 2 → ¬ (p : ℤ) ∣ m →
      ((∃ π₁ π₂ : 𝓞 K, Prime π₁ ∧ Prime π₂ ∧ (p : 𝓞 K) = π₁ * π₂) ↔ jacobiSym m p = 1) ∧
      (∀ π₁ π₂ : 𝓞 K, Prime π₁ → Prime π₂ → (p : 𝓞 K) = π₁ * π₂ → ¬ Associated π₁ π₂)) ∧
    (m % 4 = 3 → ∃ π : 𝓞 K, Prime π ∧ Associated (2 : 𝓞 K) (π ^ 2)) ∧
    (m % 8 = 5 → Prime (2 : 𝓞 K)) ∧
    (m % 8 = 1 → ∃ π₁ π₂ : 𝓞 K, Prime π₁ ∧ Prime π₂ ∧ ¬ Associated π₁ π₂ ∧
      (2 : 𝓞 K) = π₁ * π₂) ∧
    (∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → ∃ π : 𝓞 K, Prime π ∧ Associated (p : 𝓞 K) (π ^ 2))

end NTKB.NZM
