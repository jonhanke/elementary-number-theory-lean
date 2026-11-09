/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Data.Set.Card
import Aesop.BuiltinRules
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Bound
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import NTKB.Attr

/-!
# Hardy–Wright, § 21.11: further problems of Diophantine analysis

* The counterexample `27⁵ + 84⁵ + 110⁵ + 133⁵ = 144⁵` to Euler's conjecture.
* Identity (21.11.3)/(21.11.4): `(9q⁴)³ + (3q - 9q⁴)³ + (1 - 9q³)³ = 1` and its homogeneous form,
  and the consequence that `η¹²` is a sum of three positive cubes when `0 < ξ` and `9ξ³ < η³`.
* The identities in the footnote on biquadrates, the examples (21.11.5), (21.11.16), (21.11.17),
  and the identity (21.11.6) for fifth powers.
* Theorem 412: for every `r` there is a number that is a sum of two positive cubes in at least `r`
  different ways.  The proof follows the book: the two identities (21.11.9)–(21.11.12) are
  composed to give a map on pairs of positive rationals preserving the sum of the cubes and
  dividing the ratio `x / y` by roughly `4`; iterating from a very large ratio gives `r` pairs with
  strictly decreasing ratios, and clearing denominators gives integers.
-/

namespace NTKB.HardyWright

/-- Euler's conjecture fails for fifth powers: `27⁵ + 84⁵ + 110⁵ + 133⁵ = 144⁵`. -/
@[kb "hardywright2008" "Section 21.11, p. 459"]
theorem euler_conjecture_counterexample :
    27 ^ 5 + 84 ^ 5 + 110 ^ 5 + 133 ^ 5 = 144 ^ 5 := by norm_num

/-- Identity (21.11.3) (Hardy–Wright): `(9q⁴)³ + (3q - 9q⁴)³ + (1 - 9q³)³ = 1`. -/
@[kb "hardywright2008" "Section 21.11, p. 459"]
theorem three_cubes_identity {R : Type*} [CommRing R] (q : R) :
    (9 * q ^ 4) ^ 3 + (3 * q - 9 * q ^ 4) ^ 3 + (1 - 9 * q ^ 3) ^ 3 = 1 := by ring

/-- Identity (21.11.4) (Hardy–Wright), the homogeneous form of (21.11.3):
`(9ξ⁴)³ + (3ξη³ - 9ξ⁴)³ + (η⁴ - 9ξ³η)³ = (η⁴)³`. -/
@[kb "hardywright2008" "Section 21.11, p. 459"]
theorem three_cubes_identity_homogeneous {R : Type*} [CommRing R] (ξ η : R) :
    (9 * ξ ^ 4) ^ 3 + (3 * ξ * η ^ 3 - 9 * ξ ^ 4) ^ 3 + (η ^ 4 - 9 * ξ ^ 3 * η) ^ 3 =
      (η ^ 4) ^ 3 := by ring

/-- Consequence of (21.11.4) (Hardy–Wright): if `0 < ξ` and `9ξ³ < η³` then `η¹²` is a sum of three
positive cubes. -/
@[kb "hardywright2008" "Section 21.11, p. 459"]
theorem exists_three_positive_cubes_eq_pow_twelve (ξ η : ℕ) (hξ : 0 < ξ) (h : 9 * ξ ^ 3 < η ^ 3) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a ^ 3 + b ^ 3 + c ^ 3 = η ^ 12 := by
  have hξ3 : 0 < ξ ^ 3 := by positivity
  have h1 : 3 * ξ ^ 3 ≤ η ^ 3 := by linarith
  have h2 : 9 * ξ ^ 3 ≤ η ^ 3 := h.le
  have hη : 0 < η := by
    rcases Nat.eq_zero_or_pos η with rfl | hη
    · simp at h
    · exact hη
  refine ⟨9 * ξ ^ 4, 3 * ξ * (η ^ 3 - 3 * ξ ^ 3), η * (η ^ 3 - 9 * ξ ^ 3), by positivity,
    Nat.mul_pos (by positivity) (Nat.sub_pos_of_lt (by linarith)),
    Nat.mul_pos hη (Nat.sub_pos_of_lt h), ?_⟩
  zify [h1, h2]
  ring

/-- First identity of the footnote on biquadrates (Hardy–Wright):
`(4x⁴ - y⁴)⁴ + 2(4x³y)⁴ + 2(2xy³)⁴ = (4x⁴ + y⁴)⁴`. -/
@[kb "hardywright2008" "Section 21.11, p. 459"]
theorem biquadrate_identity_one {R : Type*} [CommRing R] (x y : R) :
    (4 * x ^ 4 - y ^ 4) ^ 4 + 2 * (4 * x ^ 3 * y) ^ 4 + 2 * (2 * x * y ^ 3) ^ 4 =
      (4 * x ^ 4 + y ^ 4) ^ 4 := by ring

/-- Second identity of the footnote on biquadrates (Hardy–Wright):
`(x² - y²)⁴ + (2xy + y²)⁴ + (2xy + x²)⁴ = 2(x² + xy + y²)⁴`. -/
@[kb "hardywright2008" "Section 21.11, p. 459"]
theorem biquadrate_identity_two {R : Type*} [CommRing R] (x y : R) :
    (x ^ 2 - y ^ 2) ^ 4 + (2 * x * y + y ^ 2) ^ 4 + (2 * x * y + x ^ 2) ^ 4 =
      2 * (x ^ 2 + x * y + y ^ 2) ^ 4 := by ring

/-- (21.11.5) (Hardy–Wright): `30⁴ + 120⁴ + 272⁴ + 315⁴ = 353⁴`. -/
@[kb "hardywright2008" "Section 21.11, p. 459"]
theorem four_biquadrates_example : 30 ^ 4 + 120 ^ 4 + 272 ^ 4 + 315 ^ 4 = 353 ^ 4 := by norm_num

/-- (21.11.6) (Hardy–Wright):
`(75y⁵ - x⁵)⁵ + (x⁵ + 25y⁵)⁵ + (x⁵ - 25y⁵)⁵ + (10x³y²)⁵ + (50xy⁴)⁵ = (x⁵ + 75y⁵)⁵`. -/
@[kb "hardywright2008" "Section 21.11, p. 460"]
theorem fifth_power_identity {R : Type*} [CommRing R] (x y : R) :
    (75 * y ^ 5 - x ^ 5) ^ 5 + (x ^ 5 + 25 * y ^ 5) ^ 5 + (x ^ 5 - 25 * y ^ 5) ^ 5
      + (10 * x ^ 3 * y ^ 2) ^ 5 + (50 * x * y ^ 4) ^ 5 = (x ^ 5 + 75 * y ^ 5) ^ 5 := by ring

/-- (21.11.16) (Hardy–Wright): `49⁵ + 75⁵ + 107⁵ = 39⁵ + 92⁵ + 100⁵`. -/
@[kb "hardywright2008" "Section 21.11, p. 461"]
theorem fifth_power_three_three_example :
    49 ^ 5 + 75 ^ 5 + 107 ^ 5 = 39 ^ 5 + 92 ^ 5 + 100 ^ 5 := by norm_num

/-- (21.11.17) (Hardy–Wright): `3⁶ + 19⁶ + 22⁶ = 10⁶ + 15⁶ + 23⁶`. -/
@[kb "hardywright2008" "Section 21.11, p. 461"]
theorem sixth_power_three_three_example :
    3 ^ 6 + 19 ^ 6 + 22 ^ 6 = 10 ^ 6 + 15 ^ 6 + 23 ^ 6 := by norm_num

/-! ### Theorem 412 -/

/-- The first identity pair (21.11.9)–(21.11.10): `(x, y) ↦ (X, Y)`. -/
private def half1 (p : ℚ × ℚ) : ℚ × ℚ :=
  (p.1 * (p.1 ^ 3 + 2 * p.2 ^ 3) / (p.1 ^ 3 - p.2 ^ 3),
    p.2 * (2 * p.1 ^ 3 + p.2 ^ 3) / (p.1 ^ 3 - p.2 ^ 3))

/-- The second identity pair (21.11.11)–(21.11.12): `(X, Y) ↦ (x₂, y₂)`. -/
private def half2 (p : ℚ × ℚ) : ℚ × ℚ :=
  (p.1 * (p.1 ^ 3 - 2 * p.2 ^ 3) / (p.1 ^ 3 + p.2 ^ 3),
    p.2 * (2 * p.1 ^ 3 - p.2 ^ 3) / (p.1 ^ 3 + p.2 ^ 3))

/-- The composite step, (21.11.13). -/
private def step (p : ℚ × ℚ) : ℚ × ℚ := half2 (half1 p)

private lemma half1_spec {t b : ℚ} (hb : 0 < b) (ht : 2 ≤ t) :
    0 < (half1 (t * b, b)).1 ∧ 0 < (half1 (t * b, b)).2 ∧
    (half1 (t * b, b)).1 ^ 3 - (half1 (t * b, b)).2 ^ 3 = (t * b) ^ 3 + b ^ 3 ∧
    (half1 (t * b, b)).1 / (half1 (t * b, b)).2 = t * (t ^ 3 + 2) / (2 * t ^ 3 + 1) := by
  have ht0 : 0 < t := by linarith
  have hb3 : 0 < b ^ 3 := by positivity
  have ht3 : (2 : ℚ) ^ 3 ≤ t ^ 3 := pow_le_pow_left₀ (by norm_num) ht 3
  norm_num at ht3
  have hd : 0 < (t * b) ^ 3 - b ^ 3 := by
    have : (t * b) ^ 3 - b ^ 3 = (t ^ 3 - 1) * b ^ 3 := by ring
    rw [this]; exact mul_pos (by linarith) hb3
  have hn1 : 0 < (t * b) ^ 3 + 2 * b ^ 3 := by positivity
  have hn2 : 0 < 2 * (t * b) ^ 3 + b ^ 3 := by positivity
  have h2t : 0 < 2 * t ^ 3 + 1 := by positivity
  have h31 : t ^ 3 - 1 ≠ 0 := by linarith
  have hb' : b ≠ 0 := hb.ne'
  have hd' : t ^ 3 * b ^ 3 - b ^ 3 ≠ 0 := by
    have := hd.ne'; rwa [mul_pow] at this
  have hn2' : 2 * (t ^ 3 * b ^ 3) + b ^ 3 ≠ 0 := by
    have := hn2.ne'; rwa [mul_pow] at this
  have h2t' := h2t.ne'
  simp only [half1]
  refine ⟨div_pos (mul_pos (by positivity) hn1) hd, div_pos (mul_pos hb hn2) hd, ?_, ?_⟩
  · simp only [mul_pow]
    field_simp
    ring
  · simp only [mul_pow]
    field_simp

private lemma half2_spec {u y : ℚ} (hy : 0 < y) (hu : 2 ≤ u) :
    0 < (half2 (u * y, y)).1 ∧ 0 < (half2 (u * y, y)).2 ∧
    (half2 (u * y, y)).1 ^ 3 + (half2 (u * y, y)).2 ^ 3 = (u * y) ^ 3 - y ^ 3 ∧
    (half2 (u * y, y)).1 / (half2 (u * y, y)).2 = u * (u ^ 3 - 2) / (2 * u ^ 3 - 1) := by
  have hu0 : 0 < u := by linarith
  have hy3 : 0 < y ^ 3 := by positivity
  have hu3 : (2 : ℚ) ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ (by norm_num) hu 3
  norm_num at hu3
  have hD : 0 < (u * y) ^ 3 + y ^ 3 := by positivity
  have h1 : 0 < (u * y) ^ 3 - 2 * y ^ 3 := by
    have : (u * y) ^ 3 - 2 * y ^ 3 = (u ^ 3 - 2) * y ^ 3 := by ring
    rw [this]; exact mul_pos (by linarith) hy3
  have h2 : 0 < 2 * (u * y) ^ 3 - y ^ 3 := by
    have : 2 * (u * y) ^ 3 - y ^ 3 = (2 * u ^ 3 - 1) * y ^ 3 := by ring
    rw [this]; exact mul_pos (by linarith) hy3
  have h3 : 0 < 2 * u ^ 3 - 1 := by linarith
  simp only [half2]
  refine ⟨div_pos (mul_pos (by positivity) h1) hD, div_pos (mul_pos hy h2) hD, ?_, ?_⟩
  · have hD' := hD.ne'
    field_simp
    ring
  · have hy' : y ≠ 0 := hy.ne'
    have hD' := hD.ne'
    have h2' := h2.ne'
    have h3' := h3.ne'
    field_simp

private lemma g_bounds {t : ℚ} (ht : 8 ≤ t) :
    t / 2 ≤ t * (t ^ 3 + 2) / (2 * t ^ 3 + 1) ∧
      t * (t ^ 3 + 2) / (2 * t ^ 3 + 1) ≤ t / 2 + 1 := by
  have ht0 : 0 < t := by linarith
  have h3 : t ≤ t ^ 3 := by nlinarith [mul_pos ht0 ht0]
  have hd : 0 < 2 * t ^ 3 + 1 := by positivity
  constructor
  · rw [le_div_iff₀ hd]; nlinarith
  · rw [div_le_iff₀ hd]; nlinarith

private lemma h_bounds {u : ℚ} (hu : 2 ≤ u) :
    u / 2 - 1 ≤ u * (u ^ 3 - 2) / (2 * u ^ 3 - 1) ∧
      u * (u ^ 3 - 2) / (2 * u ^ 3 - 1) ≤ u / 2 := by
  have hu0 : 0 < u := by linarith
  have h4 : 4 ≤ u ^ 2 := by nlinarith
  have h3 : 4 * u ≤ u ^ 3 := by nlinarith [mul_le_mul_of_nonneg_left h4 hu0.le]
  have hd : 0 < 2 * u ^ 3 - 1 := by linarith
  constructor
  · rw [le_div_iff₀ hd]; nlinarith
  · rw [div_le_iff₀ hd]; nlinarith

private lemma step_spec (p : ℚ × ℚ) (hb : 0 < p.2) (ht : 8 ≤ p.1 / p.2) :
    0 < (step p).1 ∧ 0 < (step p).2 ∧
    (step p).1 ^ 3 + (step p).2 ^ 3 = p.1 ^ 3 + p.2 ^ 3 ∧
    p.1 / p.2 / 8 ≤ (step p).1 / (step p).2 ∧ (step p).1 / (step p).2 < p.1 / p.2 := by
  obtain ⟨a, b⟩ := p
  simp only at hb ht ⊢
  obtain ⟨t, rfl⟩ : ∃ t, a = t * b := ⟨a / b, by field_simp⟩
  have e : t * b / b = t := by field_simp
  rw [e] at ht ⊢
  obtain ⟨hX, hY, hc1, hr1⟩ := half1_spec hb (by linarith : 2 ≤ t)
  obtain ⟨hg1, hg2⟩ := g_bounds ht
  set q := half1 (t * b, b) with hq
  have hu : 2 ≤ q.1 / q.2 := by rw [hr1]; linarith
  obtain ⟨u, hu'⟩ : ∃ u, q.1 = u * q.2 := ⟨q.1 / q.2, by field_simp⟩
  have hqe : q = (u * q.2, q.2) := Prod.ext hu' rfl
  have hur : q.1 / q.2 = u := by rw [hu']; field_simp
  rw [hur] at hu hr1
  obtain ⟨hx2, hy2, hc2, hr2⟩ := half2_spec hY hu
  obtain ⟨hh1, hh2⟩ := h_bounds hu
  have hstep : step (t * b, b) = half2 (u * q.2, q.2) := by
    rw [step, ← hq, ← hqe]
  rw [hstep]
  refine ⟨hx2, hy2, ?_, ?_, ?_⟩
  · rw [hc2, ← hu']
    rw [hq] at hc1 ⊢
    linarith
  · rw [hr2]
    rw [← hr1] at hg1 hg2
    linarith
  · rw [hr2]
    rw [← hr1] at hg1 hg2
    linarith

private lemma iterate_spec (k : ℕ) : ∀ p : ℚ × ℚ, 0 < p.1 → 0 < p.2 → 8 ^ k ≤ p.1 / p.2 →
    (∀ i ≤ k, 0 < (step^[i] p).1 ∧ 0 < (step^[i] p).2 ∧
      (step^[i] p).1 ^ 3 + (step^[i] p).2 ^ 3 = p.1 ^ 3 + p.2 ^ 3 ∧
      1 ≤ (step^[i] p).1 / (step^[i] p).2) ∧
    (∀ i j, i < j → j ≤ k →
      (step^[j] p).1 / (step^[j] p).2 < (step^[i] p).1 / (step^[i] p).2) := by
  induction k with
  | zero =>
    intro p h1 h2 h3
    refine ⟨?_, fun i j hij hj => absurd hij (by omega)⟩
    intro i hi
    obtain rfl : i = 0 := by omega
    simp only [Function.iterate_zero, id_eq]
    refine ⟨h1, h2, by simp, ?_⟩
    rw [pow_zero] at h3
    exact h3
  | succ k ih =>
    intro p h1 h2 h3
    have h8 : 8 ≤ p.1 / p.2 := by
      calc (8 : ℚ) = 8 ^ 1 := by norm_num
        _ ≤ 8 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        _ ≤ _ := h3
    obtain ⟨s1, s2, s3, s4, s5⟩ := step_spec p h2 h8
    have h4 : 8 ^ k ≤ (step p).1 / (step p).2 := by
      have : (8 : ℚ) ^ (k + 1) = 8 * 8 ^ k := by ring
      linarith
    obtain ⟨ihA, ihB⟩ := ih (step p) s1 s2 h4
    refine ⟨?_, ?_⟩
    · intro i hi
      cases i with
      | zero =>
        simp only [Function.iterate_zero, id_eq]
        exact ⟨h1, h2, by simp, by linarith⟩
      | succ i =>
        obtain ⟨a, b, c, d⟩ := ihA i (by omega)
        rw [Function.iterate_succ_apply]
        exact ⟨a, b, c.trans s3, d⟩
    · intro i j hij hj
      cases j with
      | zero => omega
      | succ j =>
        rw [Function.iterate_succ_apply]
        cases i with
        | zero =>
          simp only [Function.iterate_zero, id_eq]
          rcases Nat.eq_zero_or_pos j with rfl | hj0
          · simpa using s5
          · have := ihB 0 j hj0 (by omega)
            simp only [Function.iterate_zero, id_eq] at this
            linarith
        | succ i =>
          rw [Function.iterate_succ_apply]
          exact ihB i j (by omega) (by omega)

private lemma exists_common_denominator {m : ℕ} (q : Fin m → ℚ) (hq : ∀ i, 0 < q i) :
    ∃ D : ℕ, 0 < D ∧ ∀ i, ∃ n : ℕ, (D : ℚ) * q i = n := by
  refine ⟨∏ i, (q i).den, Finset.prod_pos (fun i _ => (q i).den_pos), fun i => ?_⟩
  have hd : (q i).den ∣ ∏ j, (q j).den :=
    Finset.dvd_prod_of_mem (fun j => (q j).den) (Finset.mem_univ i)
  obtain ⟨c, hc⟩ := hd
  refine ⟨c * (q i).num.toNat, ?_⟩
  have hnum : (0 : ℤ) ≤ (q i).num := Rat.num_nonneg.2 (hq i).le
  have h1 : ((q i).num.toNat : ℚ) = (q i).num := by exact_mod_cast Int.toNat_of_nonneg hnum
  rw [hc]
  push_cast
  calc ((q i).den : ℚ) * c * q i = c * (q i * (q i).den) := by ring
    _ = _ := by rw [Rat.mul_den_eq_num, ← h1]

/-- **Theorem 412** (Hardy–Wright). Whatever `r`, there are numbers which are representable as sums
of two positive cubes in at least `r` different ways (the pairs `(x, y)` with `x ≤ y` being counted).

The proof composes the two identities (21.11.9)–(21.11.12): starting with a pair of positive
rationals whose ratio is at least `8 ^ r`, each application of the composite step keeps the pair
positive, preserves the sum of the cubes, and strictly decreases the ratio (while keeping it
at least `1`).  Clearing denominators gives integers. -/
@[kb "hardywright2008" "Thm 412, p. 461"]
theorem exists_many_sum_two_cubes (r : ℕ) :
    ∃ n : ℕ, r ≤ ({p : ℕ × ℕ | 0 < p.1 ∧ 0 < p.2 ∧ p.1 ≤ p.2 ∧
      p.1 ^ 3 + p.2 ^ 3 = n} : Set (ℕ × ℕ)).ncard := by
  set p : ℚ × ℚ := ((8 : ℚ) ^ r, 1) with hp
  obtain ⟨hA, hB⟩ := iterate_spec r p (by simp [hp]) one_pos (by simp [hp])
  -- the rational pairs
  set a : Fin (r + 1) → ℚ := fun i => (step^[i.val] p).1 with ha
  set b : Fin (r + 1) → ℚ := fun i => (step^[i.val] p).2 with hb
  have hfacts : ∀ i : Fin (r + 1), 0 < a i ∧ 0 < b i ∧ a i ^ 3 + b i ^ 3 = p.1 ^ 3 + p.2 ^ 3 ∧
      1 ≤ a i / b i := fun i => hA i.val (by have := i.isLt; omega)
  obtain ⟨Da, hDa, hDa'⟩ := exists_common_denominator a (fun i => (hfacts i).1)
  obtain ⟨Db, hDb, hDb'⟩ := exists_common_denominator b (fun i => (hfacts i).2.1)
  set D : ℕ := Da * Db with hD
  have hDpos : (0 : ℚ) < D := by
    rw [hD]; push_cast; exact mul_pos (by exact_mod_cast hDa) (by exact_mod_cast hDb)
  have hAint : ∀ i, ∃ n : ℕ, (D : ℚ) * a i = n := by
    intro i
    obtain ⟨n, hn⟩ := hDa' i
    refine ⟨Db * n, ?_⟩
    rw [hD]; push_cast
    rw [← hn]; ring
  have hBint : ∀ i, ∃ n : ℕ, (D : ℚ) * b i = n := by
    intro i
    obtain ⟨n, hn⟩ := hDb' i
    refine ⟨Da * n, ?_⟩
    rw [hD]; push_cast
    rw [← hn]; ring
  choose A hAe using hAint
  choose B hBe using hBint
  have hApos : ∀ i, 0 < A i := fun i => by
    have : (0 : ℚ) < A i := by rw [← hAe i]; exact mul_pos hDpos (hfacts i).1
    exact_mod_cast this
  have hBpos : ∀ i, 0 < B i := fun i => by
    have : (0 : ℚ) < B i := by rw [← hBe i]; exact mul_pos hDpos (hfacts i).2.1
    exact_mod_cast this
  have hBA : ∀ i, B i ≤ A i := fun i => by
    have h := (one_le_div (hfacts i).2.1).1 (hfacts i).2.2.2
    have : (B i : ℚ) ≤ A i := by
      rw [← hAe i, ← hBe i]; exact mul_le_mul_of_nonneg_left h hDpos.le
    exact_mod_cast this
  have hsum : ∀ i, A i ^ 3 + B i ^ 3 = A 0 ^ 3 + B 0 ^ 3 := fun i => by
    have e : ∀ j, ((A j : ℚ)) ^ 3 + (B j : ℚ) ^ 3 = (D : ℚ) ^ 3 * (p.1 ^ 3 + p.2 ^ 3) := by
      intro j
      rw [← hAe j, ← hBe j, ← (hfacts j).2.2.1]; ring
    have := (e i).trans (e 0).symm
    exact_mod_cast this
  have hratio : ∀ i, (A i : ℚ) / B i = a i / b i := fun i => by
    rw [← hAe i, ← hBe i]
    exact mul_div_mul_left _ _ hDpos.ne'
  set f : Fin (r + 1) → ℕ × ℕ := fun i => (B i, A i) with hf
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hA' : A i = A j := congrArg Prod.snd hij
    have hB' : B i = B j := congrArg Prod.fst hij
    have hr : a i / b i = a j / b j := by
      rw [← hratio i, ← hratio j, hA', hB']
    have hi := i.isLt
    have hj := j.isLt
    rcases lt_or_gt_of_ne hne with h | h
    · have := hB i.val j.val h (by omega)
      simp only [ha, hb] at hr
      linarith
    · have := hB j.val i.val h (by omega)
      simp only [ha, hb] at hr
      linarith
  set n : ℕ := B 0 ^ 3 + A 0 ^ 3 with hn
  refine ⟨n, ?_⟩
  have hsub : (↑(Finset.univ.image f : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) ⊆
      {p : ℕ × ℕ | 0 < p.1 ∧ 0 < p.2 ∧ p.1 ≤ p.2 ∧ p.1 ^ 3 + p.2 ^ 3 = n} := by
    intro x hx
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx
    obtain ⟨i, rfl⟩ := hx
    refine ⟨hBpos i, hApos i, hBA i, ?_⟩
    show B i ^ 3 + A i ^ 3 = n
    rw [hn, add_comm, hsum i, add_comm]
  have hfin : {p : ℕ × ℕ | 0 < p.1 ∧ 0 < p.2 ∧ p.1 ≤ p.2 ∧ p.1 ^ 3 + p.2 ^ 3 = n}.Finite := by
    refine Set.Finite.subset
      (Finset.finite_toSet (Finset.range (n + 1) ×ˢ Finset.range (n + 1))) ?_
    rintro ⟨x, y⟩ ⟨hx, hy, hxy, hs⟩
    simp only at hx hy hxy hs
    have h1 := Nat.le_self_pow (n := 3) (by norm_num) x
    have h2 := Nat.le_self_pow (n := 3) (by norm_num) y
    simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio]
    constructor <;> omega
  calc r ≤ r + 1 := Nat.le_succ r
    _ = (Finset.univ.image f).card := by
      rw [Finset.card_image_of_injective _ hinj]; simp
    _ = (↑(Finset.univ.image f : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)).ncard :=
      (Set.ncard_coe_finset _).symm
    _ ≤ _ := Set.ncard_le_ncard hsub hfin

end NTKB.HardyWright
