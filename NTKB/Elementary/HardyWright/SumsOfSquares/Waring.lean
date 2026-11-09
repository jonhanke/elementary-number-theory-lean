/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Lattice.Nat
import Aesop.BuiltinRules
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import NTKB.Attr

/-!
# Hardy–Wright, § 20.1, § 20.10 and § 21.1: Waring's numbers `g(k)` and `G(k)`

`IsSumOfPowers k s n` says that `n = x₁ᵏ + ⋯ + x_sᵏ` with non-negative integers `xᵢ` (some of
them may be `0`, so for `k ≥ 1` this is "the sum of `s` or fewer `k`th powers", the book's
`n = B_s` of § 21.1). `waringNumber k` is the book's `g(k)`, the least `s` such that every `n` is the
sum of `s` `k`th powers, and `asymptoticWaringNumber k` is `G(k)`, the least `s` such that all
sufficiently large `n` are (both are `sInf` of the corresponding set of `s`, which is `0` when the set
is empty; every theorem below that bounds them from below is also stated for each admissible `s`).

* § 20.1: `G(k) ≤ g(k)` (`asymptoticWaringNumber_le_waringNumber`).
* § 20.10: no number `4ᵃ(8m + 7)` is the sum of three squares (`not_isSumOfPowers_two_three`).
* Theorem 380: `g(2) = G(2) = 4` (`waringNumber_two`, `asymptoticWaringNumber_two`).
* Identity (21.1.1) (`six_mul_sum_sq_sq`) and Theorem 387: `g(4)` exists and is at most `50`
  (`isSumOfPowers_four_fifty`, `waringNumber_four_le`); every `n ≤ 80` is `B₁₉`.
-/

open Finset Filter

namespace NTKB.HardyWright

/-- `n` is the sum of `s` non-negative `k`th powers (Hardy–Wright § 20.1; zeros allowed). -/
def IsSumOfPowers (k s n : ℕ) : Prop := ∃ x : Fin s → ℕ, ∑ i, x i ^ k = n

/-- Waring's number `g(k)` (Hardy–Wright § 20.1): the least `s` such that every non-negative
integer is the sum of `s` `k`th powers. -/
noncomputable def waringNumber (k : ℕ) : ℕ := sInf {s | ∀ n, IsSumOfPowers k s n}

/-- The number `G(k)` (Hardy–Wright § 20.1): the least `s` such that all sufficiently large integers
are sums of `s` `k`th powers. -/
noncomputable def asymptoticWaringNumber (k : ℕ) : ℕ :=
  sInf {s | ∀ᶠ n in atTop, IsSumOfPowers k s n}

lemma isSumOfPowers_zero (k : ℕ) : IsSumOfPowers k 0 0 := ⟨Fin.elim0, by simp⟩

lemma isSumOfPowers_pow (k x : ℕ) : IsSumOfPowers k 1 (x ^ k) := ⟨fun _ => x, by simp⟩

lemma IsSumOfPowers.add {k s t m n : ℕ} (hm : IsSumOfPowers k s m) (hn : IsSumOfPowers k t n) :
    IsSumOfPowers k (s + t) (m + n) := by
  obtain ⟨x, rfl⟩ := hm
  obtain ⟨y, rfl⟩ := hn
  exact ⟨Fin.append x y, by simp [Fin.sum_univ_add]⟩

lemma IsSumOfPowers.mono {k s t n : ℕ} (hk : k ≠ 0) (h : IsSumOfPowers k s n) (hst : s ≤ t) :
    IsSumOfPowers k t n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hst
  have h0 : IsSumOfPowers k d 0 := ⟨fun _ => 0, by simp [zero_pow hk]⟩
  simpa using h.add h0

/-- `r` is the sum of `r` copies of `1ᵏ`. -/
lemma isSumOfPowers_self (k r : ℕ) : IsSumOfPowers k r r := ⟨fun _ => 1, by simp⟩

/-- `c · xᵏ` is the sum of `c` `k`th powers. -/
lemma isSumOfPowers_mul_pow (k c x : ℕ) : IsSumOfPowers k c (c * x ^ k) := ⟨fun _ => x, by simp⟩

/-- A sum of `m` numbers each of which is a sum of `s` `k`th powers is a sum of `m * s`. -/
lemma isSumOfPowers_sum {k s : ℕ} : ∀ {m : ℕ} (f : Fin m → ℕ), (∀ i, IsSumOfPowers k s (f i)) →
    IsSumOfPowers k (m * s) (∑ i, f i)
  | 0, _, _ => by simpa using isSumOfPowers_zero k
  | m + 1, f, h => by
    rw [Fin.sum_univ_castSucc, Nat.succ_mul]
    exact (isSumOfPowers_sum _ fun i => h _).add (h _)

/-- `G(k) ≤ g(k)` whenever `g(k)` exists (Hardy–Wright § 20.1). -/
@[kb "hardywright2008" "Section 20.1, p. 412"]
theorem asymptoticWaringNumber_le_waringNumber {k : ℕ} (h : ∃ s, ∀ n, IsSumOfPowers k s n) :
    asymptoticWaringNumber k ≤ waringNumber k :=
  Nat.sInf_le (s := {s | ∀ᶠ n in atTop, IsSumOfPowers k s n})
    (Filter.Eventually.of_forall (Nat.sInf_mem (s := {s | ∀ n, IsSumOfPowers k s n}) h))

/-- If `n` is not the sum of `b - 1` `k`th powers for arbitrarily large `n`, then every `s` for
which all large numbers are sums of `s` `k`th powers is at least `b`. -/
lemma le_of_frequently_not {k b s : ℕ} (hk : k ≠ 0)
    (hb : ∀ n₀, ∃ n ≥ n₀, ¬ IsSumOfPowers k (b - 1) n)
    (hs : ∀ᶠ n in atTop, IsSumOfPowers k s n) : b ≤ s := by
  by_contra hlt
  obtain ⟨N, hN⟩ := eventually_atTop.1 hs
  obtain ⟨n, hn, hnot⟩ := hb N
  exact hnot ((hN n hn).mono hk (by omega))

/-- Lower bound for `G(k)` as a number, from a lower bound for every admissible `s`. -/
lemma le_asymptoticWaringNumber {k b : ℕ} (hex : ∃ s, ∀ᶠ n in atTop, IsSumOfPowers k s n)
    (h : ∀ s, (∀ᶠ n in atTop, IsSumOfPowers k s n) → b ≤ s) : b ≤ asymptoticWaringNumber k :=
  le_csInf hex fun s hs => h s hs

lemma le_waringNumber {k b : ℕ} (hex : ∃ s, ∀ n, IsSumOfPowers k s n)
    (h : ∀ s, (∀ n, IsSumOfPowers k s n) → b ≤ s) : b ≤ waringNumber k :=
  le_csInf hex fun s hs => h s hs

/-- For `d > 0`, every integer is within `d/2` of a multiple of `d`. -/
lemma exists_two_mul_abs_sub_le (x d : ℤ) (hd : 0 < d) : ∃ q : ℤ, 2 * |x - d * q| ≤ d := by
  have h1 := Int.emod_nonneg x hd.ne'
  have h2 := Int.emod_lt_of_pos x hd
  have h3 : x % d + d * (x / d) = x := by rw [Int.emod_def]; ring
  by_cases h : 2 * (x % d) ≤ d
  · refine ⟨x / d, ?_⟩
    rw [abs_of_nonneg (by linarith)]; linarith
  · refine ⟨x / d + 1, ?_⟩
    rw [abs_of_nonpos (by nlinarith)]; nlinarith

/-! ### Squares: § 20.10 and Theorem 380 -/

lemma isSumOfPowers_two_four (n : ℕ) : IsSumOfPowers 2 4 n := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares n
  exact ⟨![a, b, c, d], by simp [Fin.sum_univ_four, h]⟩

lemma not_isSumOfPowers_two_three_of_mod_eight {n : ℕ} (hn : n % 8 = 7) :
    ¬ IsSumOfPowers 2 3 n := by
  rintro ⟨x, hx⟩
  rw [Fin.sum_univ_three] at hx
  have h := congrArg (fun z : ℕ => (z : ZMod 8)) hx
  push_cast at h
  have h7 : ((n : ℕ) : ZMod 8) = 7 := by rw [← ZMod.natCast_mod, hn]; rfl
  rw [h7] at h
  have key : ∀ a b c : ZMod 8, a ^ 2 + b ^ 2 + c ^ 2 ≠ 7 := by decide
  exact key _ _ _ h

lemma even_of_sq_add_sq_add_sq_mod_four {a b c : ℕ} (h : (a ^ 2 + b ^ 2 + c ^ 2) % 4 = 0) :
    2 ∣ a ∧ 2 ∣ b ∧ 2 ∣ c := by
  have key : ∀ x y z : ZMod 4, x ^ 2 + y ^ 2 + z ^ 2 = 0 → 2 * x = 0 ∧ 2 * y = 0 ∧ 2 * z = 0 := by
    decide
  have h' : ((a ^ 2 + b ^ 2 + c ^ 2 : ℕ) : ZMod 4) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]; omega
  push_cast at h'
  obtain ⟨ha, hb, hc⟩ := key _ _ _ h'
  have conv : ∀ x : ℕ, 2 * (x : ZMod 4) = 0 → 2 ∣ x := by
    intro x hx
    have : ((2 * x : ℕ) : ZMod 4) = 0 := by push_cast; exact hx
    rw [ZMod.natCast_eq_zero_iff] at this
    omega
  exact ⟨conv a ha, conv b hb, conv c hc⟩

/-- **§ 20.10** (Hardy–Wright). No number `4ᵃ(8m + 7)` is the sum of three squares. -/
@[kb "hardywright2008" "Section 20.10, p. 428"]
theorem not_isSumOfPowers_two_three (a m : ℕ) : ¬ IsSumOfPowers 2 3 (4 ^ a * (8 * m + 7)) := by
  induction a with
  | zero => exact not_isSumOfPowers_two_three_of_mod_eight (by omega)
  | succ a ih =>
    rintro ⟨x, hx⟩
    rw [Fin.sum_univ_three] at hx
    have h4 : (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) % 4 = 0 := by
      rw [hx, pow_succ]; simp [Nat.mul_assoc, Nat.mul_left_comm]
    obtain ⟨⟨u, hu⟩, ⟨v, hv⟩, ⟨w, hw⟩⟩ := even_of_sq_add_sq_add_sq_mod_four h4
    apply ih
    refine ⟨![u, v, w], ?_⟩
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]
    have e : 4 ^ (a + 1) * (8 * m + 7) = 4 * (4 ^ a * (8 * m + 7)) := by ring
    rw [hu, hv, hw, e] at hx
    have : 4 * (u ^ 2 + v ^ 2 + w ^ 2) = 4 * (4 ^ a * (8 * m + 7)) := by rw [← hx]; ring
    omega

/-- **Theorem 380** (Hardy–Wright), first half: `g(2) = 4`. -/
@[kb "hardywright2008" "Thm 380, p. 428"]
theorem waringNumber_two : waringNumber 2 = 4 := by
  refine le_antisymm (Nat.sInf_le fun n => isSumOfPowers_two_four n) ?_
  refine le_waringNumber ⟨4, isSumOfPowers_two_four⟩ fun s hs => ?_
  by_contra hlt
  exact not_isSumOfPowers_two_three_of_mod_eight (n := 7) rfl ((hs 7).mono two_ne_zero (by omega))

/-- **Theorem 380** (Hardy–Wright), second half: `G(2) = 4`; more precisely, every `s` for which
all large numbers are sums of `s` squares is at least `4`. -/
@[kb "hardywright2008" "Thm 380, p. 428"]
theorem four_le_of_eventually_isSumOfPowers_two {s : ℕ}
    (hs : ∀ᶠ n in atTop, IsSumOfPowers 2 s n) : 4 ≤ s :=
  le_of_frequently_not two_ne_zero
    (fun n₀ => ⟨8 * n₀ + 7, by omega, not_isSumOfPowers_two_three_of_mod_eight (by omega)⟩) hs

@[kb "hardywright2008" "Thm 380, p. 428"]
theorem asymptoticWaringNumber_two : asymptoticWaringNumber 2 = 4 := by
  refine le_antisymm (Nat.sInf_le (Eventually.of_forall isSumOfPowers_two_four)) ?_
  exact le_asymptoticWaringNumber ⟨4, Eventually.of_forall isSumOfPowers_two_four⟩
    fun s hs => four_le_of_eventually_isSumOfPowers_two hs

/-! ### Biquadrates: identity (21.1.1) and Theorem 387 -/

/-- **Identity (21.1.1)** (Hardy–Wright). -/
@[kb "hardywright2008" "Section 21.1, p. 438"]
theorem six_mul_sum_sq_sq {R : Type*} [CommRing R] (a b c d : R) :
    6 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 =
      (a + b) ^ 4 + (a - b) ^ 4 + (c + d) ^ 4 + (c - d) ^ 4 + (a + c) ^ 4 + (a - c) ^ 4 +
      (b + d) ^ 4 + (b - d) ^ 4 + (a + d) ^ 4 + (a - d) ^ 4 + (b + c) ^ 4 + (b - c) ^ 4 := by
  ring

/-- `6 x² = B₁₂` (Hardy–Wright (21.1.2)). -/
lemma isSumOfPowers_four_six_mul_sq (x : ℕ) : IsSumOfPowers 4 12 (6 * x ^ 2) := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares x
  let A : ℤ := a
  let B : ℤ := b
  let C : ℤ := c
  let D : ℤ := d
  refine ⟨![(A + B).natAbs, (A - B).natAbs, (C + D).natAbs, (C - D).natAbs, (A + C).natAbs,
    (A - C).natAbs, (B + D).natAbs, (B - D).natAbs, (A + D).natAbs, (A - D).natAbs,
    (B + C).natAbs, (B - C).natAbs], ?_⟩
  have h4 : ∀ z : ℤ, ((z.natAbs ^ 4 : ℕ) : ℤ) = z ^ 4 := fun z => by
    rw [Nat.cast_pow, Int.natCast_natAbs, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]
  apply Nat.cast_injective (R := ℤ)
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Nat.cast_add, h4, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ← h]
  push_cast
  simp only [A, B, C, D]
  ring

/-- Every `n ≤ 80` is the sum of `19` biquadrates (Hardy–Wright § 21.1). -/
@[kb "hardywright2008" "Thm 387, p. 438"]
theorem isSumOfPowers_four_nineteen_of_le {n : ℕ} (hn : n ≤ 80) : IsSumOfPowers 4 19 n := by
  have h := (isSumOfPowers_mul_pow 4 (n / 16) 2).add (isSumOfPowers_self 4 (n % 16))
  have hn' : n / 16 * 2 ^ 4 + n % 16 = n := by omega
  rw [hn'] at h
  exact h.mono (by norm_num) (by omega)

/-- **Theorem 387** (Hardy–Wright). Every non-negative integer is the sum of `50` biquadrates. -/
@[kb "hardywright2008" "Thm 387, p. 438"]
theorem isSumOfPowers_four_fifty (n : ℕ) : IsSumOfPowers 4 50 n := by
  rcases le_or_gt n 80 with hn | hn
  · exact (isSumOfPowers_four_nineteen_of_le hn).mono (by norm_num) (by norm_num)
  -- `n = 6N + t` with `t ∈ {0, 1, 2, 81, 16, 17}` a sum of two biquadrates.
  obtain ⟨t, ht2, htmod, htle⟩ : ∃ t, IsSumOfPowers 4 2 t ∧ t % 6 = n % 6 ∧ t ≤ 81 := by
    have hlt : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
    interval_cases h : n % 6
    · exact ⟨0, ⟨![0, 0], by simp⟩, rfl, by norm_num⟩
    · exact ⟨1, ⟨![1, 0], by simp⟩, rfl, by norm_num⟩
    · exact ⟨2, ⟨![1, 1], by simp⟩, rfl, by norm_num⟩
    · exact ⟨81, ⟨![3, 0], by simp⟩, rfl, le_rfl⟩
    · exact ⟨16, ⟨![2, 0], by simp⟩, rfl, by norm_num⟩
    · exact ⟨17, ⟨![2, 1], by simp⟩, rfl, by norm_num⟩
  obtain ⟨x, hx⟩ := isSumOfPowers_two_four ((n - t) / 6)
  have h48 : IsSumOfPowers 4 (4 * 12) (∑ i, 6 * x i ^ 2) :=
    isSumOfPowers_sum _ fun i => isSumOfPowers_four_six_mul_sq (x i)
  have hsum : ∑ i, 6 * x i ^ 2 + t = n := by
    rw [← Finset.mul_sum, hx]; omega
  rw [← hsum]
  exact h48.add ht2

/-- **Theorem 387** (Hardy–Wright). `g(4)` exists and `g(4) ≤ 50`. -/
@[kb "hardywright2008" "Thm 387, p. 438"]
theorem waringNumber_four_le : waringNumber 4 ≤ 50 := Nat.sInf_le isSumOfPowers_four_fifty

end NTKB.HardyWright
