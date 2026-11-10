/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Attr
import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# The linear Diophantine equation `a x + b y = c` (Niven–Zuckerman–Montgomery, § 5.1)

* Theorem 5.1: `a x + b y = c` is solvable in integers iff `gcd(a, b) ∣ c`; if `(x₁, y₁)` is a
  solution then all solutions are `x = x₁ + k b/g`, `y = y₁ - k a/g` (`g = gcd(a, b)`), and there are
  infinitely many of them when `(a, b) ≠ (0, 0)`.
-/

namespace NTKB.NZM

/-- **Theorem 5.1 (solvability).** `a x + b y = c` has an integer solution iff `gcd(a, b) ∣ c`. -/
@[kb "nivenzuckermanmontgomery" "Thm 5.1, p. 212"]
theorem linear_diophantine_solvable_iff {a b c : ℤ} :
    (∃ x y : ℤ, a * x + b * y = c) ↔ (Int.gcd a b : ℤ) ∣ c := by
  constructor
  · rintro ⟨x, y, h⟩
    rw [← h]
    exact dvd_add (dvd_mul_of_dvd_left (Int.gcd_dvd_left ..) _)
      (dvd_mul_of_dvd_left (Int.gcd_dvd_right ..) _)
  · rintro ⟨k, hk⟩
    have hb := Int.gcd_eq_gcd_ab a b
    exact ⟨Int.gcdA a b * k, Int.gcdB a b * k, by linear_combination (-1 : ℤ) * hk - k * hb⟩

/-- Reduction by the gcd: with `g = gcd(a, b)`, `a/g` and `b/g` are coprime and not both zero. -/
theorem gcd_reduce_aux {a b : ℤ} (hab : a ≠ 0 ∨ b ≠ 0) :
    IsCoprime (a / (Int.gcd a b : ℤ)) (b / (Int.gcd a b : ℤ)) ∧
      a = a / (Int.gcd a b : ℤ) * (Int.gcd a b : ℤ) ∧
      b = b / (Int.gcd a b : ℤ) * (Int.gcd a b : ℤ) ∧
      (Int.gcd a b : ℤ) ≠ 0 ∧
      (a / (Int.gcd a b : ℤ) ≠ 0 ∨ b / (Int.gcd a b : ℤ) ≠ 0) := by
  have hg : 0 < Int.gcd a b := by
    apply Nat.pos_of_ne_zero
    intro h0
    rw [Int.gcd_eq_zero_iff] at h0
    rcases hab with ha | hb
    · exact ha h0.1
    · exact hb h0.2
  have hg0 : (Int.gcd a b : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
  have ha : a = a / (Int.gcd a b : ℤ) * (Int.gcd a b : ℤ) :=
    (Int.ediv_mul_cancel (Int.gcd_dvd_left ..)).symm
  have hb : b = b / (Int.gcd a b : ℤ) * (Int.gcd a b : ℤ) :=
    (Int.ediv_mul_cancel (Int.gcd_dvd_right ..)).symm
  refine ⟨Int.isCoprime_iff_gcd_eq_one.mpr (Int.gcd_div_gcd_div_gcd hg), ha, hb, hg0, ?_⟩
  by_contra hcon
  push_neg at hcon
  rcases hab with h | h
  · apply h
    calc a = a / (Int.gcd a b : ℤ) * (Int.gcd a b : ℤ) := ha
      _ = 0 := by rw [hcon.1, zero_mul]
  · apply h
    calc b = b / (Int.gcd a b : ℤ) * (Int.gcd a b : ℤ) := hb
      _ = 0 := by rw [hcon.2, zero_mul]

/-- Parametrization of solutions, for the reduced coefficients `a', b'` and `a = a' g`,
`b = b' g`. -/
theorem linear_diophantine_aux {a b a' b' g c x₁ y₁ : ℤ} (hg : g ≠ 0) (hc : IsCoprime a' b')
    (hn : a' ≠ 0 ∨ b' ≠ 0) (ha : a = a' * g) (hb : b = b' * g) (h₁ : a * x₁ + b * y₁ = c)
    (x y : ℤ) : a * x + b * y = c ↔ ∃ k : ℤ, x = x₁ + k * b' ∧ y = y₁ - k * a' := by
  subst ha hb
  constructor
  · intro h
    have e0 : g * (a' * (x - x₁) + b' * (y - y₁)) = 0 := by linear_combination h - h₁
    have e : a' * (x - x₁) + b' * (y - y₁) = 0 := (mul_eq_zero.mp e0).resolve_left hg
    rcases hn with ha0 | hb0
    · have hd : a' ∣ b' * (y - y₁) := ⟨-(x - x₁), by linear_combination e⟩
      obtain ⟨m, hm⟩ := hc.dvd_of_dvd_mul_left hd
      refine ⟨-m, ?_, ?_⟩
      · have h2 : a' * (x - (x₁ + -m * b')) = 0 := by linear_combination e - b' * hm
        have h3 := (mul_eq_zero.mp h2).resolve_left ha0
        linarith
      · linear_combination hm
    · have hd : b' ∣ a' * (x - x₁) := ⟨-(y - y₁), by linear_combination e⟩
      obtain ⟨k, hk⟩ := hc.symm.dvd_of_dvd_mul_left hd
      refine ⟨k, ?_, ?_⟩
      · linear_combination hk
      · have h2 : b' * (y - (y₁ - k * a')) = 0 := by linear_combination e - a' * hk
        have h3 := (mul_eq_zero.mp h2).resolve_left hb0
        linarith
  · rintro ⟨k, rfl, rfl⟩
    linear_combination h₁

/-- **Theorem 5.1 (parametrization).** If `(x₁, y₁)` is a solution of `a x + b y = c` (with
`(a, b) ≠ (0, 0)`), then the solutions are exactly `x = x₁ + k b/g`, `y = y₁ - k a/g`,
`k ∈ ℤ`, where `g = gcd(a, b)`. -/
@[kb "nivenzuckermanmontgomery" "Thm 5.1, p. 212"]
theorem linear_diophantine_solutions {a b c x₁ y₁ : ℤ} (hab : a ≠ 0 ∨ b ≠ 0)
    (h₁ : a * x₁ + b * y₁ = c) (x y : ℤ) :
    a * x + b * y = c ↔
      ∃ k : ℤ, x = x₁ + k * (b / Int.gcd a b) ∧ y = y₁ - k * (a / Int.gcd a b) := by
  obtain ⟨hc, ha, hb, hg, hn⟩ := gcd_reduce_aux hab
  exact linear_diophantine_aux hg hc hn ha hb h₁ x y

theorem linear_diophantine_inj_aux {x₁ y₁ A B : ℤ} (hn : A ≠ 0 ∨ B ≠ 0) :
    Function.Injective (fun k : ℤ => (x₁ + k * B, y₁ - k * A)) := by
  intro k k' hkk
  have h1 : x₁ + k * B = x₁ + k' * B := congrArg Prod.fst hkk
  have h2 : y₁ - k * A = y₁ - k' * A := congrArg Prod.snd hkk
  rcases hn with h | h
  · have h3 : (k - k') * A = 0 := by linear_combination (-1 : ℤ) * h2
    have h4 := (mul_eq_zero.mp h3).resolve_right h
    linarith
  · have h3 : (k - k') * B = 0 := by linear_combination h1
    have h4 := (mul_eq_zero.mp h3).resolve_right h
    linarith

/-- **Theorem 5.1 (infinitely many solutions).** If `gcd(a, b) ∣ c` and `(a, b) ≠ (0, 0)`, the
equation `a x + b y = c` has infinitely many integer solutions. -/
@[kb "nivenzuckermanmontgomery" "Thm 5.1, p. 212"]
theorem linear_diophantine_infinite {a b c : ℤ} (hab : a ≠ 0 ∨ b ≠ 0)
    (hc : (Int.gcd a b : ℤ) ∣ c) : {p : ℤ × ℤ | a * p.1 + b * p.2 = c}.Infinite := by
  obtain ⟨x₁, y₁, h₁⟩ := linear_diophantine_solvable_iff.mpr hc
  obtain ⟨_, _, _, _, hn⟩ := gcd_reduce_aux hab
  refine Set.infinite_of_injective_forall_mem
    (f := fun k : ℤ => (x₁ + k * (b / (Int.gcd a b : ℤ)), y₁ - k * (a / (Int.gcd a b : ℤ))))
    (linear_diophantine_inj_aux hn) ?_
  intro k
  show a * (x₁ + k * (b / (Int.gcd a b : ℤ))) + b * (y₁ - k * (a / (Int.gcd a b : ℤ))) = c
  exact (linear_diophantine_solutions hab h₁ _ _).mpr ⟨k, rfl, rfl⟩

end NTKB.NZM
