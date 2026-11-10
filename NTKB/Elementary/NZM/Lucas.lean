/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Attr
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.QuadraticAlgebra.Defs
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Linear recurrences and Lucas functions (Niven–Zuckerman–Montgomery, § 4.4)

* Theorem 4.11: for the recurrence `uₙ = a uₙ₋₁ + b uₙ₋₂` with a double characteristic root `λ`
  (`a² + 4b = 0`, `b ≠ 0`), `uₙ = (α + β n) λⁿ` with `α = u₀`, `(α + β) λ = u₁`.
* The Lucas functions `Uₙ(a, b)`, `Vₙ(a, b)` of (4.10), and the identity (4.11)
  `(λ - μ) Uₙ = λⁿ - μⁿ` for `λ + μ = a`, `λ μ = -b`.
* Theorem 4.12: if `p` is an odd prime with `(a² + 4b / p) = -1`, then `p ∣ U_{p+1}(a, b)`.
  Instead of the binomial expansion of `λⁿ - μⁿ` we work in the ring `(ℤ/p)[δ]`, `δ² = a² + 4b`,
  where the Frobenius `x ↦ xᵖ` swaps `λ` and `μ` (as `δᵖ = (D/p) δ = -δ` by Euler's criterion),
  so `λ^{p+1} = λμ = μ^{p+1}`.
-/

namespace NTKB.NZM

/-! ### Theorem 4.11 -/

/-- **Theorem 4.11.** Let `u` satisfy `u_{n+2} = a u_{n+1} + b uₙ` with `a² + 4b = 0`, `b ≠ 0`, and let
`λ` be a root of `z² - a z - b` (a double root, `λ = a/2 ≠ 0`). Then `uₙ = (α + β n) λⁿ` where
`α = u₀` and `β = u₁/λ - u₀` (i.e. `(α + β) λ = u₁`). -/
@[kb "nivenzuckermanmontgomery" "Thm 4.11, p. 200"]
theorem recurrence_double_root {a b lam : ℂ} (hab : a ^ 2 + 4 * b = 0) (hb : b ≠ 0)
    (hlam : lam ^ 2 - a * lam - b = 0) {u : ℕ → ℂ}
    (hu : ∀ n, u (n + 2) = a * u (n + 1) + b * u n) (n : ℕ) :
    u n = (u 0 + (u 1 / lam - u 0) * n) * lam ^ n := by
  have h2 : (2 * lam - a) ^ 2 = 0 := by linear_combination 4 * hlam + hab
  have h3 : 2 * lam - a = 0 := (pow_eq_zero_iff (two_ne_zero)).mp h2
  have ha : a = 2 * lam := by linear_combination -h3
  subst ha
  have hb' : b = -lam ^ 2 := by linear_combination -hlam
  subst hb'
  have hl : lam ≠ 0 := by
    intro h
    apply hb
    simp [h]
  have hc : u 1 = (u 0 + (u 1 / lam - u 0)) * lam := by
    have : u 1 / lam * lam = u 1 := div_mul_cancel₀ _ hl
    linear_combination (-1) * this
  have claim : ∀ m : ℕ,
      u m = (u 0 + (u 1 / lam - u 0) * (m : ℂ)) * lam ^ m ∧
      u (m + 1) = (u 0 + (u 1 / lam - u 0) * ((m + 1 : ℕ) : ℂ)) * lam ^ (m + 1) := by
    intro m
    induction m with
    | zero =>
      refine ⟨by simp, ?_⟩
      simp only [Nat.cast_zero, zero_add, Nat.cast_one, mul_one, pow_one]
      exact hc
    | succ m ih =>
      refine ⟨ih.2, ?_⟩
      show u (m + 2) = (u 0 + (u 1 / lam - u 0) * ((m + 2 : ℕ) : ℂ)) * lam ^ (m + 2)
      have e := hu m
      have h0 := ih.1
      have h1 := ih.2
      push_cast at h0 h1 ⊢
      linear_combination e + (2 * lam) * h1 + (-lam ^ 2) * h0
  exact (claim n).1

/-! ### Theorem 4.10 -/

/-- **Theorem 4.10** (existence and uniqueness of `α, β` in (4.4)).  If `λ ≠ μ`, the system
`α + β = x₀`, `α λ + β μ = x₁` has exactly one solution `(α, β)`. -/
@[kb "nivenzuckermanmontgomery" "Thm 4.10, p. 199"]
theorem exists_unique_coeffs {lam mu : ℂ} (hne : lam ≠ mu) (x₀ x₁ : ℂ) :
    ∃! p : ℂ × ℂ, p.1 + p.2 = x₀ ∧ p.1 * lam + p.2 * mu = x₁ := by
  have hd : mu - lam ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hq : (x₁ - x₀ * lam) / (mu - lam) * (mu - lam) = x₁ - x₀ * lam :=
    div_mul_cancel₀ _ hd
  refine ⟨(x₀ - (x₁ - x₀ * lam) / (mu - lam), (x₁ - x₀ * lam) / (mu - lam)), ⟨?_, ?_⟩, ?_⟩
  · show (x₀ - (x₁ - x₀ * lam) / (mu - lam)) + (x₁ - x₀ * lam) / (mu - lam) = x₀
    ring
  · show (x₀ - (x₁ - x₀ * lam) / (mu - lam)) * lam + (x₁ - x₀ * lam) / (mu - lam) * mu = x₁
    linear_combination hq
  · rintro ⟨α, β⟩ ⟨h0, h1⟩
    change α + β = x₀ at h0
    change α * lam + β * mu = x₁ at h1
    have hβ : β = (x₁ - x₀ * lam) / (mu - lam) := by
      rw [eq_div_iff hd]
      linear_combination h1 - lam * h0
    refine Prod.ext ?_ ?_
    · show α = x₀ - (x₁ - x₀ * lam) / (mu - lam)
      linear_combination h0 - hβ
    · exact hβ

/-- **Theorem 4.10.** Let `u₀, u₁` be complex, and let `λ ≠ μ` be the two roots of `z² - a z - b`.
If `u_{n+2} = a u_{n+1} + b uₙ` and `α + β = u₀`, `α λ + β μ = u₁` (equations (4.4)), then
`uₙ = α λⁿ + β μⁿ` for all `n ≥ 0`. -/
@[kb "nivenzuckermanmontgomery" "Thm 4.10, p. 199"]
theorem recurrence_distinct_roots {a b lam mu α β : ℂ} (hlam : lam ^ 2 - a * lam - b = 0)
    (hmu : mu ^ 2 - a * mu - b = 0) (hne : lam ≠ mu) {u : ℕ → ℂ}
    (hu : ∀ n, u (n + 2) = a * u (n + 1) + b * u n) (h0 : α + β = u 0)
    (h1 : α * lam + β * mu = u 1) (n : ℕ) :
    u n = α * lam ^ n + β * mu ^ n := by
  have claim : ∀ m : ℕ, u m = α * lam ^ m + β * mu ^ m ∧
      u (m + 1) = α * lam ^ (m + 1) + β * mu ^ (m + 1) := by
    intro m
    induction m with
    | zero =>
      refine ⟨?_, ?_⟩
      · linear_combination (-1 : ℂ) * h0
      · show u 1 = α * lam ^ 1 + β * mu ^ 1
        linear_combination (-1 : ℂ) * h1
    | succ m ih =>
      refine ⟨ih.2, ?_⟩
      show u (m + 2) = α * lam ^ (m + 2) + β * mu ^ (m + 2)
      have e := hu m
      have g0 := ih.1
      have g1 := ih.2
      linear_combination e + a * g1 + b * g0 - (α * lam ^ m) * hlam - (β * mu ^ m) * hmu
  exact (claim n).1

/-- **Theorem 4.10** (converse).  For any `α, β, λ, μ`, the sequence `α λⁿ + β μⁿ` satisfies the
recurrence with `a = λ + μ`, `b = -λ μ`. -/
@[kb "nivenzuckermanmontgomery" "Thm 4.10, p. 199"]
theorem recurrence_of_distinct_roots_converse (lam mu α β : ℂ) (n : ℕ) :
    α * lam ^ (n + 2) + β * mu ^ (n + 2) =
      (lam + mu) * (α * lam ^ (n + 1) + β * mu ^ (n + 1)) +
        (-(lam * mu)) * (α * lam ^ n + β * mu ^ n) := by
  ring

/-! ### Lucas functions -/

/-- The Lucas function `Uₙ(a, b)` of (4.10): `U₀ = 0`, `U₁ = 1`, `U_{n+2} = a U_{n+1} + b Uₙ`. -/
def lucasU (a b : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => a * lucasU a b (n + 1) + b * lucasU a b n

/-- The Lucas function `Vₙ(a, b)` of (4.10): `V₀ = 2`, `V₁ = a`, `V_{n+2} = a V_{n+1} + b Vₙ`. -/
def lucasV (a b : ℤ) : ℕ → ℤ
  | 0 => 2
  | 1 => a
  | n + 2 => a * lucasV a b (n + 1) + b * lucasV a b n

@[simp] lemma lucasU_zero (a b : ℤ) : lucasU a b 0 = 0 := rfl
@[simp] lemma lucasU_one (a b : ℤ) : lucasU a b 1 = 1 := rfl
lemma lucasU_add_two (a b : ℤ) (n : ℕ) :
    lucasU a b (n + 2) = a * lucasU a b (n + 1) + b * lucasU a b n := rfl

@[simp] lemma lucasV_zero (a b : ℤ) : lucasV a b 0 = 2 := rfl
@[simp] lemma lucasV_one (a b : ℤ) : lucasV a b 1 = a := rfl
lemma lucasV_add_two (a b : ℤ) (n : ℕ) :
    lucasV a b (n + 2) = a * lucasV a b (n + 1) + b * lucasV a b n := rfl

/-- (4.11) In a commutative ring, if `λ + μ = a` and `λ μ = -b`, then `(λ - μ) Uₙ(a, b) = λⁿ - μⁿ`
(that is, `Uₙ = (λⁿ - μⁿ)/(λ - μ)`). -/
@[kb "nivenzuckermanmontgomery" "(4.11), p. 201"]
theorem sub_mul_lucasU {R : Type*} [CommRing R] {a b : ℤ} {lam mu : R}
    (hs : lam + mu = (a : R)) (hp : lam * mu = -(b : R)) (n : ℕ) :
    (lam - mu) * (lucasU a b n : R) = lam ^ n - mu ^ n := by
  have key : ∀ m : ℕ, (lam - mu) * (lucasU a b m : R) = lam ^ m - mu ^ m ∧
      (lam - mu) * (lucasU a b (m + 1) : R) = lam ^ (m + 1) - mu ^ (m + 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      refine ⟨ih.2, ?_⟩
      obtain ⟨h0, h1⟩ := ih
      rw [show m + 1 + 1 = m + 2 from rfl, lucasU_add_two]
      push_cast
      linear_combination (a : R) * h1 + (b : R) * h0 - (lam ^ (m + 1) - mu ^ (m + 1)) * hs +
        (lam ^ m - mu ^ m) * hp
  exact (key n).1

/-- (4.11) In a commutative ring, if `λ + μ = a` and `λ μ = -b`, then `Vₙ(a, b) = λⁿ + μⁿ`. -/
@[kb "nivenzuckermanmontgomery" "(4.11), p. 201"]
theorem lucasV_eq_pow_add_pow {R : Type*} [CommRing R] {a b : ℤ} {lam mu : R}
    (hs : lam + mu = (a : R)) (hp : lam * mu = -(b : R)) (n : ℕ) :
    (lucasV a b n : R) = lam ^ n + mu ^ n := by
  have key : ∀ m : ℕ, (lucasV a b m : R) = lam ^ m + mu ^ m ∧
      (lucasV a b (m + 1) : R) = lam ^ (m + 1) + mu ^ (m + 1) := by
    intro m
    induction m with
    | zero =>
      refine ⟨?_, ?_⟩
      · simp [one_add_one_eq_two]
      · simpa using hs.symm
    | succ m ih =>
      refine ⟨ih.2, ?_⟩
      obtain ⟨h0, h1⟩ := ih
      rw [show m + 1 + 1 = m + 2 from rfl, lucasV_add_two]
      push_cast
      linear_combination (a : R) * h1 + (b : R) * h0 - (lam ^ (m + 1) + mu ^ (m + 1)) * hs +
        (lam ^ m + mu ^ m) * hp
  exact (key n).1

/-! ### Theorem 4.12 -/

/-- **Theorem 4.12.** Let `a, b` be integers, `D = a² + 4b`, and `p` an odd prime with `(D/p) = -1`.
Then `p ∣ U_{p+1}(a, b)`.  (Proved in `(ℤ/p)[δ]`, `δ² = D`, via the Frobenius, rather than by the
binomial expansion of the book.) -/
@[kb "nivenzuckermanmontgomery" "Thm 4.12, p. 202"]
theorem prime_dvd_lucasU_succ {a b : ℤ} {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hD : legendreSym p (a ^ 2 + 4 * b) = -1) : (p : ℤ) ∣ lucasU a b (p + 1) := by
  -- Euler's criterion
  obtain ⟨D, hDd⟩ : ∃ D : ZMod p, D = (a : ZMod p) ^ 2 + 4 * (b : ZMod p) := ⟨_, rfl⟩
  have hε : D ^ (p / 2) = -1 := by
    have h := legendreSym.eq_pow p (a ^ 2 + 4 * b)
    rw [hD] at h
    push_cast at h
    rw [hDd]
    exact h.symm
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2)
  have : CharP (QuadraticAlgebra (ZMod p) D 0) p :=
    charP_of_injective_algebraMap QuadraticAlgebra.algebraMap_injective p
  obtain ⟨t, ht⟩ : ∃ t : ZMod p, t = (2 : ZMod p)⁻¹ := ⟨_, rfl⟩
  have h2t : 2 * t = 1 := by rw [ht]; exact mul_inv_cancel₀ h2
  -- notation for the images in the quadratic algebra
  obtain ⟨T, hTd⟩ : ∃ T : QuadraticAlgebra (ZMod p) D 0,
      T = algebraMap (ZMod p) (QuadraticAlgebra (ZMod p) D 0) t := ⟨_, rfl⟩
  obtain ⟨ω, hωd⟩ : ∃ ω : QuadraticAlgebra (ZMod p) D 0, ω = ⟨0, 1⟩ := ⟨_, rfl⟩
  have hT : 2 * T = 1 := by
    have := congrArg (algebraMap (ZMod p) (QuadraticAlgebra (ZMod p) D 0)) h2t
    rw [map_mul, map_one, map_ofNat] at this
    rw [hTd]
    exact this
  have hω2 : ω ^ 2 = algebraMap (ZMod p) (QuadraticAlgebra (ZMod p) D 0) D := by
    rw [hωd]; ext <;> simp [sq]
  have hω2' : ω ^ 2 = (a : QuadraticAlgebra (ZMod p) D 0) ^ 2 +
      4 * (b : QuadraticAlgebra (ZMod p) D 0) := by
    have := congrArg (algebraMap (ZMod p) (QuadraticAlgebra (ZMod p) D 0)) hDd
    rw [hω2, this, map_add, map_mul, map_pow, map_ofNat, map_intCast, map_intCast]
  -- the roots
  obtain ⟨lam, hlamd⟩ : ∃ lam : QuadraticAlgebra (ZMod p) D 0,
      lam = T * ((a : QuadraticAlgebra (ZMod p) D 0) + ω) := ⟨_, rfl⟩
  obtain ⟨mu, hmud⟩ : ∃ mu : QuadraticAlgebra (ZMod p) D 0,
      mu = T * ((a : QuadraticAlgebra (ZMod p) D 0) - ω) := ⟨_, rfl⟩
  have hs : lam + mu = (a : QuadraticAlgebra (ZMod p) D 0) := by
    rw [hlamd, hmud]
    linear_combination (a : QuadraticAlgebra (ZMod p) D 0) * hT
  have hpr : lam * mu = -(b : QuadraticAlgebra (ZMod p) D 0) := by
    rw [hlamd, hmud]
    linear_combination (-T ^ 2) * hω2' +
      (-(b : QuadraticAlgebra (ZMod p) D 0) * (1 + 2 * T)) * hT
  have hlm : lam - mu = ω := by
    rw [hlamd, hmud]
    linear_combination ω * hT
  -- Frobenius
  have hωp : ω ^ p = -ω := by
    have e : ω ^ p = ω ^ (2 * (p / 2) + 1) := by congr 1; omega
    rw [e, pow_succ, pow_mul, hω2, ← map_pow, hε, map_neg, map_one, neg_one_mul]
  have hTp : T ^ p = T := by rw [hTd, ← map_pow, ZMod.pow_card]
  have haA : ∀ c : ℤ, (c : QuadraticAlgebra (ZMod p) D 0) ^ p = c := by
    intro c
    have : (c : QuadraticAlgebra (ZMod p) D 0) =
        algebraMap (ZMod p) (QuadraticAlgebra (ZMod p) D 0) (c : ZMod p) := by simp
    rw [this, ← map_pow, ZMod.pow_card]
  have hlp : lam ^ p = mu := by
    rw [hlamd, hmud, mul_pow, add_pow_char, hTp, haA, hωp, sub_eq_add_neg]
  have hmp : mu ^ p = lam := by
    rw [hlamd, hmud, mul_pow, sub_pow_char, hTp, haA, hωp, sub_neg_eq_add]
  have key := sub_mul_lucasU (a := a) (b := b) hs hpr (p + 1)
  rw [pow_succ, pow_succ, hlp, hmp, mul_comm mu lam, sub_self, hlm] at key
  have hcast : ((lucasU a b (p + 1) : ℤ) : QuadraticAlgebra (ZMod p) D 0) =
      algebraMap (ZMod p) (QuadraticAlgebra (ZMod p) D 0) ((lucasU a b (p + 1) : ℤ) : ZMod p) := by
    simp
  rw [hcast, mul_comm] at key
  have := congrArg QuadraticAlgebra.im key
  rw [hωd] at this
  have hz : ((lucasU a b (p + 1) : ℤ) : ZMod p) = 0 := by simpa using this
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz

end NTKB.NZM
