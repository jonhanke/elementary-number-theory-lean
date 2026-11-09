/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.QuadraticFields.RationalPrimes
import Mathlib.NumberTheory.Zsqrtd.QuadraticReciprocity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int

/-!
# The primes of `k(i)` and Fermat's theorem in `k(i)` (Hardy–Wright §§ 15.1–15.2)

The integers of `k(i)` are Mathlib's Gaussian integers `ℤ[i]` (`GaussianInt = ℤ√(-1)`).

* Theorem 252 (`gaussianInt_prime_iff`): the primes of `k(i)` are `1 + i` and its associates, the
  rational primes `4n + 3` and their associates, and the factors `a + bi` (of norm `p`) of the rational
  primes `p = 4n + 1`.
* § 15.1 (`sq_add_sq_unique`): the representation of a prime as a sum of two squares is unique up to
  order and signs (the eight variations (15.1.3)).
* Theorem 253 (`gaussianInt_fermat`): if `π` is a prime of odd norm and `π ∤ a`, then
  `a^φ(π) ≡ 1 (mod π)`, `φ(π) = Nπ - 1`.
-/

namespace NTKB.HardyWright

open GaussianInt Zsqrtd

local notation "ℤ[i]" => GaussianInt

/-- `i ∈ ℤ[i]`. -/
def gaussI : ℤ[i] := ⟨0, 1⟩

lemma gaussI_sq : gaussI ^ 2 = -1 := by ext <;> simp [gaussI, sq]

lemma gauss_prime_of_natAbs_norm_prime {π : ℤ[i]} (h : π.norm.natAbs.Prime) : Prime π :=
  irreducible_iff_prime.1 (zsqrtd_irreducible_of_natAbs_norm_prime h)

lemma gauss_natAbs_norm_eq (π : ℤ[i]) : (π.norm.natAbs : ℤ) = π.norm :=
  Int.natAbs_of_nonneg (GaussianInt.norm_nonneg π)

lemma gauss_norm_mk (a b : ℤ) : (⟨a, b⟩ : ℤ[i]).norm = a ^ 2 + b ^ 2 := by
  rw [Zsqrtd.norm_def]; ring

/-- Units of `ℤ[i]` are `±1, ±i`, in coordinates. -/
lemma gauss_eq_of_norm_eq_one {e f : ℤ} (h : e ^ 2 + f ^ 2 = 1) :
    (e = 1 ∧ f = 0) ∨ (e = -1 ∧ f = 0) ∨ (e = 0 ∧ f = 1) ∨ (e = 0 ∧ f = -1) := by
  have he : -1 ≤ e ∧ e ≤ 1 := by constructor <;> nlinarith [sq_nonneg f]
  have hf : -1 ≤ f ∧ f ≤ 1 := by constructor <;> nlinarith [sq_nonneg e]
  obtain ⟨he1, he2⟩ := he
  obtain ⟨hf1, hf2⟩ := hf
  interval_cases e <;> interval_cases f <;> simp_all

/-- If `σ ∣ τ` and both have the same norm, they are associated. -/
lemma gauss_associated_of_dvd_of_norm_eq {σ τ : ℤ[i]} (hσ : σ ≠ 0) (h : σ ∣ τ) (hn : σ.norm = τ.norm) :
    Associated σ τ := by
  obtain ⟨k, rfl⟩ := h
  have : k.norm = 1 := by
    rw [Zsqrtd.norm_mul] at hn
    have h0 : σ.norm ≠ 0 := by
      rwa [Ne, Zsqrtd.norm_eq_zero_iff (by norm_num)]
    exact (mul_right_eq_self₀.1 hn.symm).resolve_right h0
  exact ⟨((Zsqrtd.norm_eq_one_iff' (by norm_num) k).1 this).unit, rfl⟩

lemma gauss_associated_of_mul_eq {a b u : ℤ[i]} (hu : u.norm = 1) (h : a * u = b) : Associated a b :=
  ⟨((Zsqrtd.norm_eq_one_iff' (by norm_num) u).1 hu).unit, h⟩

/-- A sum of two squares is not `3 (mod 4)`. -/
lemma gauss_sq_add_sq_mod_four {a b : ℤ} {p : ℕ} (h : a ^ 2 + b ^ 2 = p) : p % 4 ≠ 3 := by
  intro h3
  have := congrArg (Int.cast : ℤ → ZMod 4) h
  push_cast at this
  rw [← ZMod.natCast_mod, h3] at this
  generalize (a : ZMod 4) = x at this
  generalize (b : ZMod 4) = y at this
  revert x y; decide

/-- **Theorem 252.** The primes of `k(i)` are (1) `1 + i` and its associates, (2) the rational primes
`4n + 3` and their associates, (3) the factors `a + bi` of the rational primes `p = 4n + 1`, i.e.
the integers of norm `p`. -/
@[kb "hardywright2008" "Thm 252, p. 303"]
theorem gaussianInt_prime_iff {π : ℤ[i]} :
    Prime π ↔ Associated π ⟨1, 1⟩ ∨ (∃ q : ℕ, q.Prime ∧ q % 4 = 3 ∧ Associated π (q : ℤ[i])) ∨
      ∃ p : ℕ, p.Prime ∧ p % 4 = 1 ∧ π.norm = p := by
  constructor
  · intro hπ
    have hn0 : π.norm.natAbs ≠ 0 := by
      rw [Ne, Int.natAbs_eq_zero, Zsqrtd.norm_eq_zero_iff (by norm_num)]; exact hπ.ne_zero
    obtain ⟨p, hp, hπp⟩ := exists_nat_prime_dvd hπ hn0 (by
      have := zsqrtd_dvd_natAbs_norm π; rwa [Int.cast_natCast] at this)
    obtain ⟨l, hl⟩ := hπp
    have hN : π.norm.natAbs * l.norm.natAbs = p ^ 2 := by
      have h1 := congrArg Zsqrtd.norm hl
      rw [Zsqrtd.norm_natCast, Zsqrtd.norm_mul] at h1
      have h2 := congrArg Int.natAbs h1
      rw [Int.natAbs_mul, Int.natAbs_mul] at h2
      simp only [Int.natAbs_natCast] at h2
      rw [sq, h2]
    obtain ⟨k, hk, hkp⟩ := (Nat.dvd_prime_pow hp).1 (Dvd.intro _ hN)
    interval_cases k
    · exact absurd (Zsqrtd.norm_eq_one_iff.1 (by simpa using hkp)) hπ.not_isUnit
    · -- `Nπ = p`
      simp only [pow_one] at hkp
      have hnp : π.norm = p := by rw [← gauss_natAbs_norm_eq, hkp]
      have h2 : π.re ^ 2 + π.im ^ 2 = p := by
        rw [← hnp, Zsqrtd.norm_def]; ring
      rcases hp.eq_two_or_odd' with rfl | hodd
      · -- `p = 2`: `π = ±1 ± i`
        left
        push_cast at h2
        have h1 : -1 ≤ π.re ∧ π.re ≤ 1 := by
          constructor <;> nlinarith [sq_nonneg π.im, sq_nonneg (π.re - 1), sq_nonneg (π.re + 1)]
        have h1' : -1 ≤ π.im ∧ π.im ≤ 1 := by
          constructor <;> nlinarith [sq_nonneg π.re, sq_nonneg (π.im - 1), sq_nonneg (π.im + 1)]
        obtain ⟨a, b⟩ := π
        simp only at h1 h1' h2
        obtain ⟨ha1, ha2⟩ := h1
        obtain ⟨hb1, hb2⟩ := h1'
        interval_cases a <;> interval_cases b <;> norm_num at h2
        · exact gauss_associated_of_mul_eq (u := -1) (by decide) (by ext <;> simp)
        · exact gauss_associated_of_mul_eq (u := ⟨0, -1⟩) (by decide) (by ext <;> simp)
        · exact gauss_associated_of_mul_eq (u := ⟨0, 1⟩) (by decide) (by ext <;> simp)
        · exact gauss_associated_of_mul_eq (u := 1) (by decide) (by ext <;> simp)
      · right; right
        refine ⟨p, hp, ?_, hnp⟩
        have := gauss_sq_add_sq_mod_four h2
        have := Nat.odd_iff.1 hodd
        omega
    · -- `Nπ = p²`: `π` is associated with `p`, which is then prime, so `p ≡ 3 (mod 4)`
      right; left
      have hl1 : l.norm.natAbs = 1 := by
        rw [hkp] at hN
        have : 0 < p ^ 2 := pow_pos hp.pos 2
        nlinarith
      have hassoc : Associated π (p : ℤ[i]) := ⟨(Zsqrtd.norm_eq_one_iff.1 hl1).unit, hl.symm⟩
      have hpp : Prime (p : ℤ[i]) := hassoc.prime hπ
      have := Fact.mk hp
      exact ⟨p, hp, (GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime p).1 hpp, hassoc⟩
  · rintro (h | ⟨q, hq, hq3, h⟩ | ⟨p, hp, -, h⟩)
    · exact h.symm.prime (gauss_prime_of_natAbs_norm_prime (by rw [gauss_norm_mk]; norm_num))
    · have := Fact.mk hq
      exact h.symm.prime (GaussianInt.prime_of_nat_prime_of_mod_four_eq_three q hq3)
    · exact gauss_prime_of_natAbs_norm_prime (by rw [h]; simpa using hp)

lemma gauss_norm_unit (u : ℤ[i]ˣ) : (u : ℤ[i]).norm = 1 :=
  (Zsqrtd.norm_eq_one_iff' (d := -1) (by norm_num) (u : ℤ[i])).2 u.isUnit

lemma gauss_norm_eq_of_associated {π σ : ℤ[i]} (h : Associated π σ) : π.norm = σ.norm := by
  obtain ⟨u, rfl⟩ := h
  rw [Zsqrtd.norm_mul, gauss_norm_unit, mul_one]

/-- If `σ * u = π` with `u` a unit, then `σ` is `±π` or `±iπ` in coordinates. -/
lemma gauss_coords_of_mul_unit {a b c d : ℤ} (u : ℤ[i]ˣ) (h : (⟨c, d⟩ : ℤ[i]) * u = ⟨a, b⟩) :
    ((c = a ∨ c = -a) ∧ (d = b ∨ d = -b)) ∨ ((c = b ∨ c = -b) ∧ (d = a ∨ d = -a)) := by
  have hu := gauss_norm_unit u
  generalize (u : ℤ[i]) = w at h hu
  obtain ⟨e, f⟩ := w
  rw [gauss_norm_mk] at hu
  have hre := congrArg Zsqrtd.re h
  have him := congrArg Zsqrtd.im h
  simp only [Zsqrtd.re_mul, Zsqrtd.im_mul] at hre him
  rcases gauss_eq_of_norm_eq_one hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left; constructor <;> left <;> linarith
  · left; constructor <;> right <;> linarith
  · right; constructor
    · left; linarith
    · right; linarith
  · right; constructor
    · right; linarith
    · left; linarith

/-- § 15.1: the expression of a prime `p` as a sum of two squares is unique, apart from the eight
variations `(±a)² + (±b)² = (±b)² + (±a)²` (15.1.3). -/
@[kb "hardywright2008" "§ 15.1, p. 303"]
theorem sq_add_sq_unique {p : ℕ} (hp : p.Prime) {a b c d : ℤ} (h1 : a ^ 2 + b ^ 2 = p)
    (h2 : c ^ 2 + d ^ 2 = p) :
    ((c = a ∨ c = -a) ∧ (d = b ∨ d = -b)) ∨ ((c = b ∨ c = -b) ∧ (d = a ∨ d = -a)) := by
  set π : ℤ[i] := ⟨a, b⟩
  set σ : ℤ[i] := ⟨c, d⟩
  have hnπ : π.norm = p := by rw [gauss_norm_mk, h1]
  have hnσ : σ.norm = p := by rw [gauss_norm_mk, h2]
  have hpπ : Prime π := gauss_prime_of_natAbs_norm_prime (by rw [hnπ]; simpa using hp)
  have hpσ : Prime σ := gauss_prime_of_natAbs_norm_prime (by rw [hnσ]; simpa using hp)
  have hdiv : σ ∣ π * star π := by
    rw [← Zsqrtd.norm_eq_mul_conj, hnπ, ← hnσ, Zsqrtd.norm_eq_mul_conj]
    exact dvd_mul_right _ _
  rcases hpσ.dvd_or_dvd hdiv with h | h
  · obtain ⟨u, hu⟩ := gauss_associated_of_dvd_of_norm_eq hpσ.ne_zero h (by rw [hnσ, hnπ])
    exact gauss_coords_of_mul_unit u hu
  · have hns : (star π).norm = p := by rw [Zsqrtd.norm_conj, hnπ]
    obtain ⟨u, hu⟩ := gauss_associated_of_dvd_of_norm_eq hpσ.ne_zero h (by rw [hnσ, hns])
    have hu' : (⟨c, d⟩ : ℤ[i]) * u = ⟨a, -b⟩ := by rw [hu]; rfl
    rcases gauss_coords_of_mul_unit u hu' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact ⟨h1, by rcases h2 with h2 | h2 <;> [right; left] <;> linarith⟩
    · right; exact ⟨by rcases h1 with h1 | h1 <;> [right; left] <;> linarith, h2⟩

/-- Fermat's theorem in `ℤ`: `p ∣ l^p - l`. -/
lemma int_dvd_pow_sub_self (p : ℕ) [Fact p.Prime] (l : ℤ) : (p : ℤ) ∣ l ^ p - l := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.pow_card, sub_self]

lemma gauss_int_dvd_pow_sub (p : ℕ) [Fact p.Prime] (l : ℤ) : (p : ℤ[i]) ∣ (l : ℤ[i]) ^ p - l := by
  have := (Int.castRingHom ℤ[i]).map_dvd (int_dvd_pow_sub_self p l)
  simpa using this

lemma gauss_eq_re_add_im (x : ℤ[i]) : x = (x.re : ℤ[i]) + (x.im : ℤ[i]) * gaussI := by
  ext <;> simp [gaussI]

/-- `(a + bi)^p ≡ a + b i^p (mod p)`. -/
lemma gauss_dvd_pow_sub_frob' (p : ℕ) [hp : Fact p.Prime] (l m : ℤ) :
    (p : ℤ[i]) ∣ ((l : ℤ[i]) + m * gaussI) ^ p - ((l : ℤ[i]) + (m : ℤ[i]) * gaussI ^ p) := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp.out (l : ℤ[i]) ((m : ℤ[i]) * gaussI)
  have e : ((l : ℤ[i]) + m * gaussI) ^ p - ((l : ℤ[i]) + (m : ℤ[i]) * gaussI ^ p) =
      ((l : ℤ[i]) ^ p - l) + ((m : ℤ[i]) ^ p - m) * gaussI ^ p + p * l * (m * gaussI) * r := by
    rw [hr]; ring
  rw [e]
  exact dvd_add (dvd_add (gauss_int_dvd_pow_sub p _) (dvd_mul_of_dvd_left (gauss_int_dvd_pow_sub p _) _))
    (by rw [mul_assoc, mul_assoc]; exact dvd_mul_right _ _)

lemma gauss_dvd_pow_sub_frob (p : ℕ) [Fact p.Prime] (x : ℤ[i]) :
    (p : ℤ[i]) ∣ x ^ p - ((x.re : ℤ[i]) + (x.im : ℤ[i]) * gaussI ^ p) := by
  have := gauss_dvd_pow_sub_frob' p x.re x.im
  rwa [← gauss_eq_re_add_im] at this

lemma gaussI_pow_four : gaussI ^ 4 = 1 := by
  rw [show 4 = 2 * 2 by rfl, pow_mul, gaussI_sq]; norm_num

lemma gaussI_pow_of_mod_four_eq_one {p : ℕ} (h : p % 4 = 1) : gaussI ^ p = gaussI := by
  rw [← Nat.div_add_mod p 4, h, pow_add, pow_mul, gaussI_pow_four, one_pow, one_mul, pow_one]

lemma gaussI_pow_of_mod_four_eq_three {p : ℕ} (h : p % 4 = 3) : gaussI ^ p = -gaussI := by
  rw [← Nat.div_add_mod p 4, h, pow_add, pow_mul, gaussI_pow_four, one_pow, one_mul,
    show 3 = 2 + 1 by rfl, pow_add, gaussI_sq]; ring

/-- For `p ≡ 1 (mod 4)`: `a^p ≡ a (mod p)`. -/
lemma gauss_dvd_pow_sub_self_one (p : ℕ) [Fact p.Prime] (hp : p % 4 = 1) (x : ℤ[i]) :
    (p : ℤ[i]) ∣ x ^ p - x := by
  have := gauss_dvd_pow_sub_frob p x
  rwa [gaussI_pow_of_mod_four_eq_one hp, ← gauss_eq_re_add_im] at this

/-- For `q ≡ 3 (mod 4)`: `a^q ≡ ā (mod q)`, hence `a^(q²) ≡ a (mod q)`. -/
lemma gauss_dvd_pow_sub_self_three (q : ℕ) [Fact q.Prime] (hq : q % 4 = 3) (x : ℤ[i]) :
    (q : ℤ[i]) ∣ x ^ (q ^ 2) - x := by
  have hstar : ∀ y : ℤ[i], (q : ℤ[i]) ∣ y ^ q - star y := fun y ↦ by
    have := gauss_dvd_pow_sub_frob q y
    rw [gaussI_pow_of_mod_four_eq_three hq] at this
    convert this using 2
    ext <;> simp [gaussI]
  have h1 : (q : ℤ[i]) ∣ (x ^ q) ^ q - (star x) ^ q :=
    dvd_trans (hstar x) (sub_dvd_pow_sub_pow _ _ _)
  have h2 := hstar (star x)
  rw [star_star] at h2
  rw [sq, pow_mul]
  convert dvd_add h1 h2 using 1
  ring

/-- **Theorem 253** (Fermat's theorem in `k(i)`). If `π` is a prime of `k(i)` of odd norm (a rational
prime `4n + 3` or a divisor of a rational prime `4n + 1`, up to associates) and `(a, π) = 1`, then
`a^φ(π) ≡ 1 (mod π)`, where `φ(π) = Nπ - 1`. -/
@[kb "hardywright2008" "Thm 253, p. 304"]
theorem gaussianInt_fermat {π a : ℤ[i]} (hπ : Prime π) (hodd : Odd π.norm) (ha : ¬ π ∣ a) :
    π ∣ a ^ (π.norm.natAbs - 1) - 1 := by
  -- `π ∣ a^(Nπ) - a`
  have key : π ∣ a ^ π.norm.natAbs - a := by
    rcases gaussianInt_prime_iff.1 hπ with h | ⟨q, hq, hq3, h⟩ | ⟨p, hp, hp1, h⟩
    · exfalso
      rw [gauss_norm_eq_of_associated h, gauss_norm_mk] at hodd
      norm_num [Int.odd_iff] at hodd
    · have := Fact.mk hq
      have hn : π.norm.natAbs = q ^ 2 := by
        rw [gauss_norm_eq_of_associated h, Zsqrtd.norm_natCast, Int.natAbs_mul, Int.natAbs_natCast, sq]
      rw [hn]
      exact dvd_trans h.dvd (gauss_dvd_pow_sub_self_three q hq3 a)
    · have := Fact.mk hp
      have hn : π.norm.natAbs = p := by rw [h]; simp
      have hπp : π ∣ (p : ℤ[i]) := by
        have := zsqrtd_dvd_natAbs_norm π
        rwa [hn, Int.cast_natCast] at this
      rw [hn]
      exact dvd_trans hπp (gauss_dvd_pow_sub_self_one p hp1 a)
  have hpos : 1 ≤ π.norm.natAbs := by
    rcases hodd with ⟨k, hk⟩
    omega
  have e : a ^ π.norm.natAbs - a = a * (a ^ (π.norm.natAbs - 1) - 1) := by
    conv_lhs => rw [show π.norm.natAbs = π.norm.natAbs - 1 + 1 by omega, pow_succ]
    ring
  rw [e] at key
  exact (hπ.dvd_or_dvd key).resolve_left ha

end NTKB.HardyWright
