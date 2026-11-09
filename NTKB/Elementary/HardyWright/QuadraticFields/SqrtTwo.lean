/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.QuadraticFields.QuadInt
import NTKB.Elementary.HardyWright.QuadraticFields.NormEuclidean
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Algebra.Order.Star.Real

/-!
# The field `k(√2)` (Hardy–Wright §§ 14.5, 15.4)

The integers of `k(√2)` are `x + y√2`, here Mathlib's `QuadraticAlgebra ℤ 2 0` (`ω = √2`), with norm
`N(x + y√2) = x² - 2y²`.

* `instEuclideanDomainSqrtTwo`: `k(√2)` is Euclidean (Theorem 248 for `m = 2`, in `ℤ[√2]`), hence has
  unique factorization (Theorem 245).
* Theorem 243 (`sqrtTwo_units`): the unities of `k(√2)` are `±(1 + √2)^n`, `n ∈ ℤ`.
* Theorem 244 (`sq_sub_two_mul_sq_eq_one_iff`, `sq_sub_two_mul_sq_eq_neg_one_iff`): the solutions of
  `x² - 2y² = 1` are `x + y√2 = ±(1 + √2)^(2n)`, those of `x² - 2y² = -1` are `±(1 + √2)^(2n+1)`.
* Theorem 256 (`sqrtTwo_prime_iff`): the primes of `k(√2)` are `√2`, the rational primes `8n ± 3`, and
  the factors `a + b√2` of the rational primes `8n ± 1` (and their associates).
-/

namespace NTKB.HardyWright

open QuadraticAlgebra

/-- The integers `x + y√2` of `k(√2)`. -/
abbrev ZSqrt2 := QuadraticAlgebra ℤ 2 0

instance factSqrtTwo : Fact (∀ r : ℚ, r ^ 2 ≠ ((2 : ℤ) : ℚ) + ((0 : ℤ) : ℚ) * r) :=
  ⟨fun r hr ↦ not_isSquare_of_between (k := 2) (n := 1) (by norm_num) (by norm_num) (by norm_num)
    ⟨r, by push_cast at hr; linear_combination -hr⟩⟩

lemma sqrtTwo_norm (z : ZSqrt2) : norm z = z.re ^ 2 - 2 * z.im ^ 2 := by
  rw [norm_def]; ring

lemma sqrtTwo_round (ξ : QuadraticAlgebra ℚ ((2 : ℤ) : ℚ) ((0 : ℤ) : ℚ)) :
    ∃ q : ZSqrt2, |norm (ξ - algebraMap _ _ q)| < 1 := by
  refine ⟨⟨round ξ.re, round ξ.im⟩, ?_⟩
  have h1 := sq_le_quarter (abs_sub_round ξ.re)
  have h2 := sq_le_quarter (abs_sub_round ξ.im)
  rw [norm_def, abs_lt]
  simp only [QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub,
    QuadraticAlgebra.Int.re_algebraMap, QuadraticAlgebra.Int.im_algebraMap]
  push_cast
  constructor <;> nlinarith [sq_nonneg (ξ.re - round ξ.re), sq_nonneg (ξ.im - round ξ.im)]

/-- `k(√2)` is Euclidean (Theorem 248, `m = 2`); in particular `ℤ[√2]` is a Euclidean domain. -/
noncomputable instance instEuclideanDomainSqrtTwo : EuclideanDomain ZSqrt2 :=
  euclideanDomainOfNorm ZSqrt2 QuadraticAlgebra.norm (map_mul QuadraticAlgebra.norm) (fun _ h ↦ qa_norm_eq_zero h)
    (exists_sub_mul_lt_of_round sqrtTwo_round)

/-- The real embedding `x + y√2 ↦ x + y√2`. -/
noncomputable def sqrtTwoToReal : ZSqrt2 →ₐ[ℤ] ℝ :=
  QuadraticAlgebra.lift ⟨Real.sqrt 2, by
    rw [Real.mul_self_sqrt (by norm_num)]; simp⟩

lemma sqrtTwoToReal_apply (z : ZSqrt2) : sqrtTwoToReal z = z.re + z.im * Real.sqrt 2 := by
  simp [sqrtTwoToReal, QuadraticAlgebra.lift_apply_apply, zsmul_eq_mul]

lemma sqrt_two_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

lemma sqrtTwoToReal_injective : Function.Injective sqrtTwoToReal := by
  intro z w h
  rw [sqrtTwoToReal_apply, sqrtTwoToReal_apply] at h
  have hi : z.im = w.im := by
    by_contra hne
    have hne' : ((z.im : ℝ) - w.im) ≠ 0 := by exact_mod_cast sub_ne_zero.2 hne
    apply irrational_sqrt_two
    refine ⟨(w.re - z.re : ℚ) / (z.im - w.im), ?_⟩
    push_cast
    field_simp
    linear_combination -h
  have hr : z.re = w.re := by
    rw [hi] at h
    exact_mod_cast add_right_cancel h
  ext <;> assumption

/-- `ω = 1 + √2`. -/
def wTwo : ZSqrt2 := ⟨1, 1⟩

/-- `1 + √2` as a unity, with inverse `-1 + √2`. -/
def wTwoUnit : ZSqrt2ˣ where
  val := ⟨1, 1⟩
  inv := ⟨-1, 1⟩
  val_inv := by ext <;> simp
  inv_val := by ext <;> simp

lemma sqrtTwoToReal_wTwo : sqrtTwoToReal (wTwoUnit : ZSqrt2) = 1 + Real.sqrt 2 := by
  rw [sqrtTwoToReal_apply]; simp [wTwoUnit]

lemma one_lt_wTwo : 1 < 1 + Real.sqrt 2 := by
  have := Real.sqrt_pos.2 (show (0 : ℝ) < 2 by norm_num); linarith

lemma sqrtTwoToReal_zpow (n : ℤ) :
    sqrtTwoToReal ((wTwoUnit ^ n : ZSqrt2ˣ) : ZSqrt2) = (1 + Real.sqrt 2) ^ n := by
  have h : ∀ u : ZSqrt2ˣ, sqrtTwoToReal (u : ZSqrt2) ≠ 0 := fun u h0 ↦ by
    have := congrArg sqrtTwoToReal (Units.mul_inv u)
    rw [map_mul, h0, zero_mul, map_one] at this
    exact zero_ne_one this
  let f : ZSqrt2ˣ →* ℝˣ := Units.map sqrtTwoToReal.toRingHom.toMonoidHom
  have hf : ∀ u : ZSqrt2ˣ, ((f u : ℝˣ) : ℝ) = sqrtTwoToReal (u : ZSqrt2) := fun u ↦ rfl
  rw [← hf, map_zpow, Units.val_zpow_eq_zpow_val, hf, sqrtTwoToReal_wTwo]

/-- Step (i) of the proof of Theorem 243: there is no unity strictly between `1` and `1 + √2`. -/
lemma not_unit_between {ε : ZSqrt2} (hε : IsUnit ε) (h1 : 1 < sqrtTwoToReal ε)
    (h2 : sqrtTwoToReal ε < 1 + Real.sqrt 2) : False := by
  have hN := qa_isUnit_iff.1 hε
  rw [sqrtTwoToReal_apply] at h1 h2
  set x := ε.re
  set y := ε.im
  have hs := sqrt_two_sq
  have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs1 : Real.sqrt 2 < 3 / 2 := by nlinarith
  -- `x - y√2 = ±1/(x + y√2)`, so `|x - y√2| < 1`
  have hN' : ((x : ℝ) + y * Real.sqrt 2) * (x - y * Real.sqrt 2) = 1 ∨
      ((x : ℝ) + y * Real.sqrt 2) * (x - y * Real.sqrt 2) = -1 := by
    have : (x ^ 2 - 2 * y ^ 2 : ℤ) = 1 ∨ (x ^ 2 - 2 * y ^ 2 : ℤ) = -1 := by
      rw [← sqrtTwo_norm]; omega
    rcases this with h | h
    · left; have := congrArg (Int.cast : ℤ → ℝ) h; push_cast at this; nlinarith
    · right; have := congrArg (Int.cast : ℤ → ℝ) h; push_cast at this; nlinarith
  have hc : -1 < (x : ℝ) - y * Real.sqrt 2 ∧ (x : ℝ) - y * Real.sqrt 2 < 1 := by
    rcases hN' with h | h <;> constructor <;> nlinarith
  have hx1 : (0 : ℝ) < 2 * x := by linarith [hc.1]
  have hx2 : (2 * x : ℝ) < 2 + Real.sqrt 2 := by linarith [hc.2]
  have hx : x = 1 := by
    have : (0 : ℤ) < 2 * x := by exact_mod_cast hx1
    have : (2 * x : ℝ) < 4 := by linarith
    have : 2 * x < 4 := by exact_mod_cast this
    omega
  rw [hx] at h1 h2
  push_cast at h1 h2
  have hy0 : (0 : ℝ) < y := by
    by_contra h; push Not at h; nlinarith
  have hy1 : (y : ℝ) < 1 := by
    by_contra h; push Not at h; nlinarith
  have : (0 : ℤ) < y := by exact_mod_cast hy0
  have : y < 1 := by exact_mod_cast hy1
  omega

/-- **Theorem 243.** The unities of `k(√2)` are the numbers `±(1 + √2)^n`, `n ∈ ℤ`. -/
@[kb "hardywright2008" "Thm 243, p. 289"]
theorem sqrtTwo_units (u : ZSqrt2ˣ) : ∃ n : ℤ, u = wTwoUnit ^ n ∨ u = -wTwoUnit ^ n := by
  have hpos : ∀ v : ZSqrt2ˣ, 0 < sqrtTwoToReal (v : ZSqrt2) → ∃ n : ℤ, v = wTwoUnit ^ n := by
    intro v hv
    obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow hv one_lt_wTwo
    refine ⟨n, ?_⟩
    set e := v * wTwoUnit ^ (-n)
    have he : sqrtTwoToReal (e : ZSqrt2) = sqrtTwoToReal (v : ZSqrt2) / (1 + Real.sqrt 2) ^ n := by
      rw [Units.val_mul, map_mul, sqrtTwoToReal_zpow, zpow_neg, div_eq_mul_inv]
    have hw : (0 : ℝ) < (1 + Real.sqrt 2) ^ n := zpow_pos (by linarith [one_lt_wTwo]) n
    have he1 : 1 ≤ sqrtTwoToReal (e : ZSqrt2) := by
      rw [he, le_div_iff₀ hw]; linarith
    have he2 : sqrtTwoToReal (e : ZSqrt2) < 1 + Real.sqrt 2 := by
      have h3 := hn2
      rw [zpow_add_one₀ (by linarith [one_lt_wTwo])] at h3
      rw [he, div_lt_iff₀ hw]
      linarith [mul_comm (1 + Real.sqrt 2) ((1 + Real.sqrt 2) ^ n)]
    rcases he1.lt_or_eq with he1 | he1
    · exact (not_unit_between e.isUnit he1 he2).elim
    · have : (e : ZSqrt2) = 1 := sqrtTwoToReal_injective (by rw [← he1, map_one])
      have he' : e = 1 := Units.ext this
      calc v = e * wTwoUnit ^ n := by simp [e]
        _ = wTwoUnit ^ n := by rw [he', one_mul]
  have h0 : sqrtTwoToReal (u : ZSqrt2) ≠ 0 := fun h0 ↦ by
    have := congrArg sqrtTwoToReal (Units.mul_inv u)
    rw [map_mul, h0, zero_mul, map_one] at this
    exact zero_ne_one this
  rcases h0.lt_or_gt with h | h
  · obtain ⟨n, hn⟩ := hpos (-u) (by rw [Units.val_neg, map_neg]; linarith)
    exact ⟨n, Or.inr (by rw [← hn, neg_neg])⟩
  · obtain ⟨n, hn⟩ := hpos u h
    exact ⟨n, Or.inl hn⟩

lemma norm_wTwo_zpow (n : ℤ) :
    QuadraticAlgebra.norm ((wTwoUnit ^ n : ZSqrt2ˣ) : ZSqrt2) = (((-1 : ℤˣ) ^ n : ℤˣ) : ℤ) := by
  let f : ZSqrt2ˣ →* ℤˣ := Units.map (QuadraticAlgebra.norm : ZSqrt2 →* ℤ)
  have hf : ∀ u : ZSqrt2ˣ, ((f u : ℤˣ) : ℤ) = QuadraticAlgebra.norm (u : ZSqrt2) := fun u ↦ rfl
  have hw : f wTwoUnit = -1 := Units.ext (by rw [hf]; simp [wTwoUnit, sqrtTwo_norm])
  rw [← hf, map_zpow, hw]

lemma isUnit_of_norm {x y : ℤ} (h : x ^ 2 - 2 * y ^ 2 = 1 ∨ x ^ 2 - 2 * y ^ 2 = -1) :
    IsUnit (⟨x, y⟩ : ZSqrt2) := by
  rw [qa_isUnit_iff, sqrtTwo_norm]
  rcases h with h | h <;> simp [h]

lemma sqrtTwo_norm_mk (x y : ℤ) : QuadraticAlgebra.norm (⟨x, y⟩ : ZSqrt2) = x ^ 2 - 2 * y ^ 2 :=
  sqrtTwo_norm _

/-- The unity `x + y√2` (`x² - 2y² = ±1`) is `±(1 + √2)^k` for some `k`, as an element. -/
lemma exists_eq_zpow {x y : ℤ} (h : x ^ 2 - 2 * y ^ 2 = 1 ∨ x ^ 2 - 2 * y ^ 2 = -1) :
    ∃ k : ℤ, (⟨x, y⟩ : ZSqrt2) = ((wTwoUnit ^ k : ZSqrt2ˣ) : ZSqrt2) ∨
      (⟨x, y⟩ : ZSqrt2) = -((wTwoUnit ^ k : ZSqrt2ˣ) : ZSqrt2) := by
  obtain ⟨k, hk⟩ := sqrtTwo_units (isUnit_of_norm h).unit
  refine ⟨k, ?_⟩
  rcases hk with hk | hk
  · left; rw [← hk]; rfl
  · right; rw [← Units.val_neg, ← hk]; rfl

lemma norm_pm_wTwo_zpow {z : ZSqrt2} {k : ℤ} (h : z = ((wTwoUnit ^ k : ZSqrt2ˣ) : ZSqrt2) ∨
    z = -((wTwoUnit ^ k : ZSqrt2ˣ) : ZSqrt2)) :
    QuadraticAlgebra.norm z = (((-1 : ℤˣ) ^ k : ℤˣ) : ℤ) := by
  rcases h with rfl | rfl
  · exact norm_wTwo_zpow k
  · rw [QuadraticAlgebra.norm_neg, norm_wTwo_zpow]

/-- **Theorem 244.** All rational integral solutions of `x² - 2y² = 1` are given by
`x + y√2 = ±(1 + √2)^(2n)`, `n ∈ ℤ`. -/
@[kb "hardywright2008" "Thm 244, p. 290"]
theorem sq_sub_two_mul_sq_eq_one_iff (x y : ℤ) :
    x ^ 2 - 2 * y ^ 2 = 1 ↔ ∃ n : ℤ, (⟨x, y⟩ : ZSqrt2) = ((wTwoUnit ^ (2 * n) : ZSqrt2ˣ) : ZSqrt2) ∨
      (⟨x, y⟩ : ZSqrt2) = -((wTwoUnit ^ (2 * n) : ZSqrt2ˣ) : ZSqrt2) := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := exists_eq_zpow (Or.inl h)
    have hN := norm_pm_wTwo_zpow hk
    rw [sqrtTwo_norm_mk, h] at hN
    have hk2 : Even k := by
      by_contra ho
      rw [Int.not_even_iff_odd] at ho
      rw [ho.neg_one_zpow] at hN
      norm_num at hN
    obtain ⟨n, rfl⟩ := hk2
    exact ⟨n, by rwa [← two_mul] at hk⟩
  · rintro ⟨n, h⟩
    have hN := norm_pm_wTwo_zpow h
    rwa [sqrtTwo_norm_mk, (even_two_mul n).neg_one_zpow, Units.val_one] at hN

/-- **Theorem 244**, the equation `x² - 2y² = -1`: its solutions are `x + y√2 = ±(1 + √2)^(2n+1)`. -/
@[kb "hardywright2008" "Thm 244, p. 290"]
theorem sq_sub_two_mul_sq_eq_neg_one_iff (x y : ℤ) :
    x ^ 2 - 2 * y ^ 2 = -1 ↔
      ∃ n : ℤ, (⟨x, y⟩ : ZSqrt2) = ((wTwoUnit ^ (2 * n + 1) : ZSqrt2ˣ) : ZSqrt2) ∨
        (⟨x, y⟩ : ZSqrt2) = -((wTwoUnit ^ (2 * n + 1) : ZSqrt2ˣ) : ZSqrt2) := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := exists_eq_zpow (Or.inr h)
    have hN := norm_pm_wTwo_zpow hk
    rw [sqrtTwo_norm_mk, h] at hN
    have hk2 : Odd k := by
      by_contra he
      rw [Int.not_odd_iff_even] at he
      rw [he.neg_one_zpow] at hN
      norm_num at hN
    obtain ⟨n, rfl⟩ := hk2
    exact ⟨n, hk⟩
  · rintro ⟨n, h⟩
    have hN := norm_pm_wTwo_zpow h
    rwa [sqrtTwo_norm_mk, (odd_two_mul_add_one n).neg_one_zpow, Units.val_neg, Units.val_one] at hN

/-- `x² - 2y²` is never `±3` or `±5` modulo `8` (every square is `0, 1` or `4 (mod 8)`). -/
lemma sq_sub_two_mul_sq_mod_eight {x y : ℤ} {p : ℕ} (h : (x ^ 2 - 2 * y ^ 2).natAbs = p) :
    p % 8 ≠ 3 ∧ p % 8 ≠ 5 := by
  have key : ∀ r : ℕ, r = 3 ∨ r = 5 → p % 8 = r → False := by
    rintro r hr hp
    rcases Int.natAbs_eq (x ^ 2 - 2 * y ^ 2) with h' | h' <;> rw [h] at h' <;>
    · have := congrArg (Int.cast : ℤ → ZMod 8) h'
      push_cast at this
      rw [← ZMod.natCast_mod, hp] at this
      generalize (x : ZMod 8) = u at this
      generalize (y : ZMod 8) = v at this
      rcases hr with rfl | rfl <;> revert u v <;> decide
  exact ⟨fun h3 ↦ key 3 (Or.inl rfl) h3, fun h5 ↦ key 5 (Or.inr rfl) h5⟩

lemma sqrtTwo_prime_of_natAbs_norm_prime {π : ZSqrt2} (h : (QuadraticAlgebra.norm π).natAbs.Prime) :
    Prime π :=
  irreducible_iff_prime.1 (qa_irreducible_of_natAbs_norm_prime h)

/-- A rational prime `p` with `p ∣ c² - 2` for some `c` is not a prime of `k(√2)`. -/
lemma not_prime_of_dvd_sq_sub_two {p : ℕ} (hp : p.Prime) {c : ℤ} (hc : (p : ℤ) ∣ c ^ 2 - 2) :
    ¬ Prime (p : ZSqrt2) := by
  intro hpp
  have hdvd : (p : ZSqrt2) ∣ (⟨c, -1⟩ : ZSqrt2) * ⟨c, 1⟩ := by
    obtain ⟨t, ht⟩ := hc
    rw [show ((⟨c, -1⟩ : ZSqrt2) * ⟨c, 1⟩) = ((c ^ 2 - 2 : ℤ) : ZSqrt2) by ext <;> simp [sq]; ring,
      ht]
    push_cast
    exact dvd_mul_right _ _
  have hp1 : ¬ (p : ℤ) ∣ 1 := by
    rw [Int.natCast_dvd_ofNat]; exact hp.one_lt.ne' ∘ Nat.dvd_one.1
  rcases hpp.dvd_or_dvd hdvd with ⟨t, ht⟩ | ⟨t, ht⟩
  · apply hp1
    have := congrArg QuadraticAlgebra.im ht
    simp at this
    exact ⟨-t.im, by linarith⟩
  · apply hp1
    have := congrArg QuadraticAlgebra.im ht
    simp at this
    exact ⟨t.im, by linarith⟩

/-- **Theorem 256.** The primes of `k(√2)` are (1) `√2`, (2) the rational primes `8n ± 3`, (3) the
factors `a + b√2` of the rational primes `p = 8n ± 1`, i.e. the integers with `|a² - 2b²| = p`
(and the associates of these numbers). -/
@[kb "hardywright2008" "Thm 256, p. 306"]
theorem sqrtTwo_prime_iff {π : ZSqrt2} :
    Prime π ↔ Associated π ⟨0, 1⟩ ∨
      (∃ q : ℕ, q.Prime ∧ (q % 8 = 3 ∨ q % 8 = 5) ∧ Associated π (q : ZSqrt2)) ∨
      ∃ p : ℕ, p.Prime ∧ (p % 8 = 1 ∨ p % 8 = 7) ∧ (QuadraticAlgebra.norm π).natAbs = p := by
  have hs : (QuadraticAlgebra.norm (⟨0, 1⟩ : ZSqrt2)).natAbs = 2 := by
    rw [sqrtTwo_norm_mk]; rfl
  constructor
  · intro hπ
    obtain ⟨p, hp, hπp, hcase⟩ := qa_prime_cases hπ
    rcases hcase with hN | hassoc
    · rcases hp.eq_two_or_odd' with rfl | hodd
      · left
        have h2 : (2 : ℕ) = ((⟨0, 1⟩ : ZSqrt2) * ⟨0, 1⟩ : ZSqrt2) := by ext <;> simp
        rw [h2] at hπp
        have := hπ.dvd_or_dvd hπp
        exact qa_associated_of_dvd hπ.ne_zero (this.elim id id) (by rw [hN, hs])
      · right; right
        refine ⟨p, hp, ?_, hN⟩
        have := sq_sub_two_mul_sq_mod_eight (x := π.re) (y := π.im) (p := p)
          (by rw [sqrtTwo_norm] at hN; exact hN)
        have := Nat.odd_iff.1 hodd
        omega
    · right; left
      refine ⟨p, hp, ?_, hassoc⟩
      have hpp : Prime (p : ZSqrt2) := hassoc.prime hπ
      by_contra h
      have : p = 2 ∨ p % 8 = 1 ∨ p % 8 = 7 := by
        rcases hp.eq_two_or_odd' with h2 | hodd
        · exact Or.inl h2
        · have := Nat.odd_iff.1 hodd; omega
      obtain ⟨c, hc⟩ : ∃ c : ℤ, (p : ℤ) ∣ c ^ 2 - 2 := by
        rcases this with rfl | h17
        · exact ⟨0, by norm_num⟩
        · have := Fact.mk hp
          obtain ⟨c, hc⟩ := (ZMod.exists_sq_eq_two_iff (by rintro rfl; omega)).2 h17
          refine ⟨c.val, (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 ?_⟩
          push_cast
          rw [ZMod.natCast_zmod_val, ← sq] at *
          rw [← hc]; ring
      exact not_prime_of_dvd_sq_sub_two hp hc hpp
  · rintro (h | ⟨q, hq, hq8, h⟩ | ⟨p, hp, -, h⟩)
    · exact h.symm.prime (sqrtTwo_prime_of_natAbs_norm_prime (by rw [hs]; norm_num))
    · refine h.symm.prime (irreducible_iff_prime.1 ⟨fun hu ↦ ?_, fun α β hαβ ↦ ?_⟩)
      · rw [qa_isUnit_iff, QuadraticAlgebra.norm_natCast] at hu
        simp at hu
        exact hq.one_lt.ne' (by simpa using hu)
      · have hN := congrArg (fun z ↦ (QuadraticAlgebra.norm z).natAbs) hαβ
        simp only [map_mul, Int.natAbs_mul, QuadraticAlgebra.norm_natCast, Int.natAbs_pow,
          Int.natAbs_natCast] at hN
        obtain ⟨k, hk, hkq⟩ := (Nat.dvd_prime_pow hq).1 (Dvd.intro _ hN.symm)
        interval_cases k
        · exact Or.inl (qa_isUnit_iff.2 (by simpa using hkq))
        · exfalso
          have := sq_sub_two_mul_sq_mod_eight (x := α.re) (y := α.im) (p := q)
            (by rw [sqrtTwo_norm] at hkq; simpa using hkq)
          omega
        · right
          rw [hkq] at hN
          have : 0 < q ^ 2 := pow_pos hq.pos 2
          exact qa_isUnit_iff.2 (by nlinarith)
    · exact sqrtTwo_prime_of_natAbs_norm_prime (by rw [h]; exact hp)

end NTKB.HardyWright
