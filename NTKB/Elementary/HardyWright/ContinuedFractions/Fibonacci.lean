/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.ContinuedFractions.Basic
import Mathlib.Algebra.QuadraticAlgebra.Defs
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Algebra
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic.NormNum.LegendreSymbol

/-!
# Some special continued fractions; Fibonacci numbers (Hardy–Wright, Chapter X, §§ 10.13 and 10.14)

* Theorem 178: the convergents of `[b, a, b, a, …]` with `b = ac` are
  `pₙ = c^{-⌊(n+1)/2⌋} u_{n+2}`, `qₙ = c^{-⌊(n+1)/2⌋} u_{n+1}`, where `uₙ = (xⁿ - yⁿ)/(x - y)` and
  `x, y` are the roots of `t² - bt - c = 0`.
* Theorem 180: every prime `p` divides some (hence infinitely many) Fibonacci numbers; `p ∣ u_{p-1}` if
  `p ≡ ±1 (mod 5)` and `p ∣ u_{p+1}` if `p ≡ ±2 (mod 5)`. Hardy–Wright expand `2^{n-1} uₙ` by the
  binomial theorem modulo `p`; we use the same computation in the ring `(ℤ/p)[√5]`, where
  `(1 + √5)^p = 1 + 5^{(p-1)/2} √5` (binomial theorem in characteristic `p`) and
  `5^{(p-1)/2} = (5/p)` (Euler's criterion; Hardy–Wright's Theorem 97 via quadratic reciprocity).
-/

namespace NTKB.HardyWright

open GenContFract

/-! ### Theorem 178 -/

/-- **Theorem 178.** Let `a, c` be integers, `b = ac`, and `x ≠ y` the roots of `t² - bt - c = 0` (so
`x + y = b`, `xy = -c`), `uₙ = (xⁿ - yⁿ)/(x - y)`. The `n`-th convergent `pₙ/qₙ` of
`[b, a, b, a, …]` satisfies `c^{⌊(n+1)/2⌋} pₙ = u_{n+2}` and `c^{⌊(n+1)/2⌋} qₙ = u_{n+1}`. -/
@[kb "hardywright2008" "Thm 178, p. 188"]
theorem cf_alternating_convs (a c : ℤ) {x y : ℝ} (hxy : x ≠ y) (hsum : x + y = a * c)
    (hprod : x * y = -c) (n : ℕ) :
    (c : ℝ) ^ ((n + 1) / 2) * (cf (fun i ↦ if Even i then (a * c : ℝ) else a)).nums n =
        (x ^ (n + 2) - y ^ (n + 2)) / (x - y) ∧
      (c : ℝ) ^ ((n + 1) / 2) * (cf (fun i ↦ if Even i then (a * c : ℝ) else a)).dens n =
        (x ^ (n + 1) - y ^ (n + 1)) / (x - y) := by
  set q : ℕ → ℝ := fun i ↦ if Even i then (a * c : ℝ) else a with hq
  have hxy' : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hx2 : x ^ 2 = a * c * x + c := by
    have : y = a * c - x := by linarith
    rw [this] at hprod
    linear_combination -hprod
  have hy2 : y ^ 2 = a * c * y + c := by
    have : x = a * c - y := by linarith
    rw [this] at hprod
    linear_combination -hprod
  have hqe : ∀ m, q (2 * m + 2) = a * c := fun m ↦ by
    simp only [hq, show Even (2 * m + 2) from ⟨m + 1, by ring⟩, ite_true]
  have hqo : ∀ m, q (2 * m + 3) = a := fun m ↦ by
    simp only [hq, show ¬Even (2 * m + 3) from by
      rw [Nat.not_even_iff_odd]; exact ⟨m + 1, by ring⟩, ite_false]
  -- the even and odd cases together
  have key : ∀ m : ℕ,
      (c : ℝ) ^ m * (cf q).nums (2 * m) * (x - y) = x ^ (2 * m + 2) - y ^ (2 * m + 2) ∧
      (c : ℝ) ^ m * (cf q).dens (2 * m) * (x - y) = x ^ (2 * m + 1) - y ^ (2 * m + 1) ∧
      (c : ℝ) ^ (m + 1) * (cf q).nums (2 * m + 1) * (x - y) = x ^ (2 * m + 3) - y ^ (2 * m + 3) ∧
      (c : ℝ) ^ (m + 1) * (cf q).dens (2 * m + 1) * (x - y) = x ^ (2 * m + 2) - y ^ (2 * m + 2) := by
    intro m
    induction m with
    | zero =>
      simp only [mul_zero, zero_add, pow_zero, one_mul, cf_nums_zero, cf_dens_zero, pow_one,
        cf_nums_one, cf_dens_one, hq, Even.zero, ite_true, show ¬Even 1 from Nat.not_even_one,
        ite_false]
      refine ⟨by linear_combination -(x - y) * hsum, ?_, ?_, ?_⟩
      · trivial
      · linear_combination (-(x - y) * (x + y + a * c)) * hsum + (x - y) * hprod
      · linear_combination -(x - y) * hsum
    | succ m ih =>
      obtain ⟨h0, h0', h1, h1'⟩ := ih
      have g1 : (c : ℝ) ^ (m + 1) * (cf q).nums (2 * m + 2) * (x - y) =
          x ^ (2 * m + 4) - y ^ (2 * m + 4) := by
        rw [cf_nums_add_two, hqe]
        linear_combination (a * c : ℝ) * h1 + (c : ℝ) * h0 - x ^ (2 * m + 2) * hx2 +
          y ^ (2 * m + 2) * hy2
      have g2 : (c : ℝ) ^ (m + 1) * (cf q).dens (2 * m + 2) * (x - y) =
          x ^ (2 * m + 3) - y ^ (2 * m + 3) := by
        rw [cf_dens_add_two, hqe]
        linear_combination (a * c : ℝ) * h1' + (c : ℝ) * h0' - x ^ (2 * m + 1) * hx2 +
          y ^ (2 * m + 1) * hy2
      have g3 : (c : ℝ) ^ (m + 1 + 1) * (cf q).nums (2 * m + 1 + 2) * (x - y) =
          x ^ (2 * m + 5) - y ^ (2 * m + 5) := by
        rw [cf_nums_add_two, show 2 * m + 1 + 2 = 2 * m + 3 by ring, hqo,
          show 2 * m + 1 + 1 = 2 * m + 2 by ring]
        linear_combination (a * c : ℝ) * g1 + (c : ℝ) * h1 - x ^ (2 * m + 3) * hx2 +
          y ^ (2 * m + 3) * hy2
      have g4 : (c : ℝ) ^ (m + 1 + 1) * (cf q).dens (2 * m + 1 + 2) * (x - y) =
          x ^ (2 * m + 4) - y ^ (2 * m + 4) := by
        rw [cf_dens_add_two, show 2 * m + 1 + 2 = 2 * m + 3 by ring, hqo,
          show 2 * m + 1 + 1 = 2 * m + 2 by ring]
        linear_combination (a * c : ℝ) * g2 + (c : ℝ) * h1' - x ^ (2 * m + 2) * hx2 +
          y ^ (2 * m + 2) * hy2
      exact ⟨g1, g2, g3, g4⟩
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · obtain ⟨h0, h0', -, -⟩ := key m
    rw [show (2 * m + 1) / 2 = m by omega, eq_div_iff hxy', eq_div_iff hxy']
    exact ⟨h0, h0'⟩
  · obtain ⟨-, -, h1, h1'⟩ := key m
    rw [show (2 * m + 1 + 1) / 2 = m + 1 by omega, eq_div_iff hxy', eq_div_iff hxy',
      show 2 * m + 1 + 2 = 2 * m + 3 by ring, show 2 * m + 1 + 1 = 2 * m + 2 by ring]
    exact ⟨h1, h1'⟩

/-! ### Theorem 180 -/

/-- In a commutative ring, if `φ + ψ = 1` and `φψ = -1` then `φ^{n+1} = u_{n+1} φ + uₙ`. -/
lemma pow_succ_eq_fib {R : Type*} [CommRing R] {φ ψ : R} (hs : φ + ψ = 1) (hp : φ * ψ = -1)
    (n : ℕ) : φ ^ (n + 1) = (Nat.fib (n + 1) : R) * φ + Nat.fib n := by
  have hφ2 : φ ^ 2 = φ + 1 := by linear_combination φ * hs - hp
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Nat.fib_add_two]
    push_cast
    linear_combination (Nat.fib (n + 1) : R) * hφ2

/-- In a commutative ring, if `φ + ψ = 1` and `φψ = -1` then `φⁿ - ψⁿ = uₙ (φ - ψ)` (Binet). -/
lemma pow_sub_pow_eq_fib {R : Type*} [CommRing R] {φ ψ : R} (hs : φ + ψ = 1) (hp : φ * ψ = -1)
    (n : ℕ) : φ ^ n - ψ ^ n = (Nat.fib n : R) * (φ - ψ) := by
  rcases n with _ | n
  · simp
  · rw [pow_succ_eq_fib hs hp, pow_succ_eq_fib (by rw [add_comm]; exact hs)
      (by rw [mul_comm]; exact hp)]
    ring

open QuadraticAlgebra in
/-- The two residues of a prime `p ≠ 2, 5` modulo the Fibonacci period: with `ε = 5^{(p-1)/2}`,
`p ∣ u_{p-1}` if `ε = 1` and `p ∣ u_{p+1}` if `ε = -1`. -/
lemma fib_dvd_of_eps {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    ((5 : ZMod p) ^ (p / 2) = 1 → p ∣ Nat.fib (p - 1)) ∧
      ((5 : ZMod p) ^ (p / 2) = -1 → p ∣ Nat.fib (p + 1)) := by
  have : CharP (QuadraticAlgebra (ZMod p) 5 0) p :=
    charP_of_injective_algebraMap QuadraticAlgebra.algebraMap_injective p
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)
  obtain ⟨t, ht⟩ : ∃ t : ZMod p, t = (2 : ZMod p)⁻¹ := ⟨_, rfl⟩
  have h2t : 2 * t = 1 := by rw [ht]; exact mul_inv_cancel₀ h2
  obtain ⟨φ, hφd⟩ : ∃ φ : QuadraticAlgebra (ZMod p) 5 0, φ = ⟨t, t⟩ := ⟨_, rfl⟩
  obtain ⟨ψ, hψd⟩ : ∃ ψ : QuadraticAlgebra (ZMod p) 5 0, ψ = ⟨t, -t⟩ := ⟨_, rfl⟩
  obtain ⟨ω, hωd⟩ : ∃ ω : QuadraticAlgebra (ZMod p) 5 0, ω = ⟨0, 1⟩ := ⟨_, rfl⟩
  have hs : φ + ψ = 1 := by
    rw [hφd, hψd]; ext <;> simp <;> linear_combination h2t
  have hpr : φ * ψ = -1 := by
    rw [hφd, hψd]; ext <;> simp <;> linear_combination -(2 * t + 1) * h2t
  have hφψ : φ - ψ = ω := by
    rw [hφd, hψd, hωd]; ext <;> simp; linear_combination h2t
  have hω2 : ω ^ 2 = algebraMap (ZMod p) _ 5 := by
    rw [hωd]; ext <;> simp [sq]
  set ε : ZMod p := (5 : ZMod p) ^ (p / 2) with hε
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2)
  have hωp : ω ^ p = algebraMap (ZMod p) _ ε * ω := by
    have : ω ^ p = ω ^ (2 * (p / 2) + 1) := by congr 1; omega
    rw [this, pow_succ, pow_mul, hω2, ← map_pow]
  have htp : t ^ p = t := ZMod.pow_card t
  have hφ : φ = algebraMap (ZMod p) _ t * (1 + ω) := by
    rw [hφd, hωd]; ext <;> simp
  have hφp : φ ^ p = algebraMap (ZMod p) _ t * (1 + algebraMap (ZMod p) _ ε * ω) := by
    rw [hφ, mul_pow, add_pow_char, one_pow, hωp, ← map_pow, htp]
  have hψ : ψ = 1 - φ := by rw [← hs]; ring
  have hψp : ψ ^ p = 1 - φ ^ p := by rw [hψ, sub_pow_char, one_pow]
  have hωne : ∀ r : ZMod p, algebraMap (ZMod p) _ r * ω = 0 → r = 0 := by
    intro r h
    have := congrArg QuadraticAlgebra.im h
    rw [hωd] at this
    simpa using this
  have hfib : ∀ n, (Nat.fib n : QuadraticAlgebra (ZMod p) 5 0) =
      algebraMap (ZMod p) _ (Nat.fib n : ZMod p) := by
    intro n; simp
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · -- `ε = 1`: `φ^p = φ`, `ψ^p = ψ`
    simp only [h, map_one, one_mul] at hφp
    rw [← hφ] at hφp
    have hψp' : ψ ^ p = ψ := by rw [hψp, hφp, hψ]
    have hφ1 : φ ^ (p - 1) = 1 := by
      have : φ ^ (p - 1) * φ = φ := by rw [← pow_succ, Nat.sub_add_cancel hp.out.one_lt.le, hφp]
      calc φ ^ (p - 1) = φ ^ (p - 1) * (φ * (-ψ)) := by rw [mul_neg, hpr, neg_neg, mul_one]
        _ = (φ ^ (p - 1) * φ) * (-ψ) := by ring
        _ = 1 := by rw [this, mul_neg, hpr, neg_neg]
    have hψ1 : ψ ^ (p - 1) = 1 := by
      have : ψ ^ (p - 1) * ψ = ψ := by rw [← pow_succ, Nat.sub_add_cancel hp.out.one_lt.le, hψp']
      calc ψ ^ (p - 1) = ψ ^ (p - 1) * (ψ * (-φ)) := by
            rw [mul_neg, mul_comm ψ φ, hpr, neg_neg, mul_one]
        _ = (ψ ^ (p - 1) * ψ) * (-φ) := by ring
        _ = 1 := by rw [this, mul_neg, mul_comm ψ φ, hpr, neg_neg]
    have := pow_sub_pow_eq_fib hs hpr (p - 1)
    rw [hφ1, hψ1, sub_self, hφψ, hfib] at this
    have := hωne _ this.symm
    exact (ZMod.natCast_eq_zero_iff _ _).mp this
  · -- `ε = -1`: `φ^p = ψ`, `ψ^p = φ`
    rw [h] at hφp
    have hφp' : φ ^ p = ψ := by
      rw [hφp, hψd, hωd]; ext <;> simp
    have hψp' : ψ ^ p = φ := by rw [hψp, hφp', ← hs]; ring
    have := pow_sub_pow_eq_fib hs hpr (p + 1)
    rw [pow_succ, pow_succ, hφp', hψp', mul_comm φ ψ, sub_self, hφψ, hfib] at this
    have := hωne _ this.symm
    exact (ZMod.natCast_eq_zero_iff _ _).mp this

lemma legendreSym_five_one [Fact (Nat.Prime 5)] : legendreSym 5 1 = 1 := by norm_num
lemma legendreSym_five_four [Fact (Nat.Prime 5)] : legendreSym 5 4 = 1 := by norm_num
lemma legendreSym_five_two [Fact (Nat.Prime 5)] : legendreSym 5 2 = -1 := by norm_num
lemma legendreSym_five_three [Fact (Nat.Prime 5)] : legendreSym 5 3 = -1 := by norm_num

/-- `5^{(p-1)/2} ≡ (5/p) = (p/5) (mod p)`, which is `1` for `p ≡ ±1` and `-1` for `p ≡ ±2 (mod 5)`
(Hardy–Wright's Theorem 97, by quadratic reciprocity). -/
lemma five_pow_half {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    ((p % 5 = 1 ∨ p % 5 = 4) → (5 : ZMod p) ^ (p / 2) = 1) ∧
      ((p % 5 = 2 ∨ p % 5 = 3) → (5 : ZMod p) ^ (p / 2) = -1) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hrec : legendreSym p 5 = legendreSym 5 p :=
    legendreSym.quadratic_reciprocity_one_mod_four (p := 5) (q := p) (by norm_num) hp2
  have heq := legendreSym.eq_pow p 5
  have hmod : legendreSym 5 p = legendreSym 5 ((p % 5 : ℕ) : ℤ) := by
    rw [legendreSym.mod 5 (p : ℤ)]; congr 1
  push_cast at heq
  rw [← heq, hrec, hmod]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases h with h | h <;> rw [h]
    · rw [Nat.cast_one, legendreSym_five_one]; simp
    · rw [show ((4 : ℕ) : ℤ) = 4 by rfl, legendreSym_five_four]; simp
  · rcases h with h | h <;> rw [h]
    · rw [show ((2 : ℕ) : ℤ) = 2 by rfl, legendreSym_five_two]; simp
    · rw [show ((3 : ℕ) : ℤ) = 3 by rfl, legendreSym_five_three]; simp

/-- **Theorem 180.** Every prime `p` divides some Fibonacci number, and therefore infinitely many of them.
In particular `u_{p-1} ≡ 0 (mod p)` if `p = 5m ± 1`, and `u_{p+1} ≡ 0 (mod p)` if `p = 5m ± 2`. -/
@[kb "hardywright2008" "Thm 180, p. 192"]
theorem prime_dvd_fib (p : ℕ) [hp : Fact p.Prime] :
    {n : ℕ | 0 < n ∧ p ∣ Nat.fib n}.Infinite ∧
      ((p % 5 = 1 ∨ p % 5 = 4) → p ∣ Nat.fib (p - 1)) ∧
      ((p % 5 = 2 ∨ p % 5 = 3) → p ∣ Nat.fib (p + 1)) := by
  have hmain : ((p % 5 = 1 ∨ p % 5 = 4) → p ∣ Nat.fib (p - 1)) ∧
      ((p % 5 = 2 ∨ p % 5 = 3) → p ∣ Nat.fib (p + 1)) := by
    by_cases hp2 : p = 2
    · subst hp2; exact ⟨by omega, fun _ ↦ by decide⟩
    obtain ⟨h1, h2⟩ := fib_dvd_of_eps hp2
    obtain ⟨e1, e2⟩ := five_pow_half hp2
    exact ⟨fun h ↦ h1 (e1 h), fun h ↦ h2 (e2 h)⟩
  refine ⟨?_, hmain⟩
  -- some `u_n` with `n > 0` is divisible by `p`
  obtain ⟨n, hn, hdvd⟩ : ∃ n, 0 < n ∧ p ∣ Nat.fib n := by
    by_cases hp5 : p = 5
    · exact ⟨5, by norm_num, by subst hp5; decide⟩
    have h5 : p % 5 ≠ 0 := by
      intro h
      have : 5 ∣ p := Nat.dvd_of_mod_eq_zero h
      exact hp5 ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hp.out).mp this).symm
    have hp1 := hp.out.two_le
    rcases (show p % 5 = 1 ∨ p % 5 = 4 ∨ p % 5 = 2 ∨ p % 5 = 3 by omega) with h | h | h | h
    · exact ⟨p - 1, by omega, hmain.1 (Or.inl h)⟩
    · exact ⟨p - 1, by omega, hmain.1 (Or.inr h)⟩
    · exact ⟨p + 1, by omega, hmain.2 (Or.inl h)⟩
    · exact ⟨p + 1, by omega, hmain.2 (Or.inr h)⟩
  -- `u_n ∣ u_{kn}`
  refine Set.infinite_of_forall_exists_gt fun m ↦ ⟨n * (m + 1), ⟨by positivity,
    hdvd.trans (Nat.fib_dvd _ _ (dvd_mul_right n _))⟩, by nlinarith⟩

end NTKB.HardyWright
