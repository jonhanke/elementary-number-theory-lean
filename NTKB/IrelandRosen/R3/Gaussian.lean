/-
Ireland–Rosen, Chapter 9, §7: the Gaussian integers `ℤ[i]`.
-/
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Aesop.BuiltinRules
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Logic.Equiv.PartialEquiv
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Bound
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
import NTKB.Attr

/-!
# Biquadratic reciprocity, preliminaries: the Gaussian integers

Ireland–Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 9, §7. We work in
Mathlib's `GaussianInt` (`ℤ√(-1)`, a Euclidean domain). The element `i` is `Zsqrtd.sqrtd`.

* the units of `ℤ[i]` are `±1, ±i` (`isUnit_iff_eq`);
* a divisibility criterion: `β ∣ α` iff `N β` divides both coordinates of `α β̄` (`dvd_iff_norm_dvd`);
* `1 + i` and the prime `2 = -i (1 + i)²` (Lemma 3);
* primary elements (`IsPrimary`, the book's definition: a nonunit `≡ 1 mod (1 + i)³`), their
  description by congruences (Lemma 6) and the unique primary associate (Lemma 7).
-/

namespace NTKB.IrelandRosen

open Zsqrtd

local notation "ℤ[i]" => GaussianInt

namespace Gaussian

/-- The Gaussian integer `i`. -/
abbrev I : ℤ[i] := Zsqrtd.sqrtd

@[simp] lemma I_re : I.re = 0 := rfl
@[simp] lemma I_im : I.im = 1 := rfl

lemma I_sq : I ^ 2 = -1 := by ext <;> simp [sq]

lemma I_mul_I : I * I = -1 := by rw [← sq, I_sq]

lemma I_pow_four : I ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, I_sq]; norm_num

lemma ext_iff' {x y : ℤ[i]} : x = y ↔ x.re = y.re ∧ x.im = y.im := Zsqrtd.ext_iff

lemma eq_re_add_im (x : ℤ[i]) : x = (x.re : ℤ[i]) + (x.im : ℤ[i]) * I := by
  ext <;> simp

@[simp] lemma norm_def (x : ℤ[i]) : x.norm = x.re ^ 2 + x.im ^ 2 := by
  rw [Zsqrtd.norm_def]; ring

lemma norm_nonneg (x : ℤ[i]) : 0 ≤ x.norm := by rw [norm_def]; positivity

lemma natAbs_norm (x : ℤ[i]) : (x.norm.natAbs : ℤ) = x.norm :=
  Int.natAbs_of_nonneg (norm_nonneg x)

/-! ### Units -/

lemma isUnit_iff_norm_eq_one {x : ℤ[i]} : IsUnit x ↔ x.norm = 1 :=
  (Zsqrtd.norm_eq_one_iff' (by norm_num) x).symm

/-- The units of `ℤ[i]` are `1, -1, i, -i`. -/
@[kb "irelandrosen1990" "Ch. 9, §7 (units of Z[i]), p. 131"]
theorem isUnit_iff_eq {x : ℤ[i]} : IsUnit x ↔ x = 1 ∨ x = -1 ∨ x = I ∨ x = -I := by
  rw [isUnit_iff_norm_eq_one, norm_def]
  constructor
  · intro h
    have h1 : x.re ^ 2 ≤ 1 := by nlinarith [sq_nonneg x.im]
    have h2 : x.im ^ 2 ≤ 1 := by nlinarith [sq_nonneg x.re]
    have hr : -1 ≤ x.re ∧ x.re ≤ 1 := ⟨by nlinarith, by nlinarith⟩
    have hi : -1 ≤ x.im ∧ x.im ≤ 1 := ⟨by nlinarith, by nlinarith⟩
    obtain ⟨re, im⟩ := x
    simp only at hr hi h ⊢
    simp only [ext_iff', I_re, I_im, Zsqrtd.re_one, Zsqrtd.im_one, Zsqrtd.re_neg, Zsqrtd.im_neg]
    have : re = -1 ∨ re = 0 ∨ re = 1 := by omega
    have : im = -1 ∨ im = 0 ∨ im = 1 := by omega
    rcases this with h' | h' | h' <;> rcases ‹re = -1 ∨ re = 0 ∨ re = 1› with h'' | h'' | h'' <;>
      subst h' h'' <;> simp_all
  · rintro (rfl | rfl | rfl | rfl) <;> simp

lemma isUnit_I : IsUnit I := isUnit_iff_eq.2 (by simp)

/-! ### A divisibility criterion -/

/-- `β ∣ α` iff the norm of `β` divides both coordinates of `α β̄`. -/
theorem dvd_iff_norm_dvd {α β : ℤ[i]} (hβ : β ≠ 0) :
    β ∣ α ↔ β.norm ∣ (α * star β).re ∧ β.norm ∣ (α * star β).im := by
  rw [← Zsqrtd.intCast_dvd, Zsqrtd.norm_eq_mul_conj]
  have hs : star β ≠ 0 := by
    intro h; apply hβ; simpa using congrArg star h
  constructor
  · rintro ⟨γ, rfl⟩
    exact ⟨γ, by ring⟩
  · rintro ⟨γ, hγ⟩
    refine ⟨γ, mul_right_cancel₀ hs ?_⟩
    rw [hγ]; ring

/-! ### `1 + i` -/

/-- The element `1 + i` (written `λ` in some texts). -/
abbrev onePlusI : ℤ[i] := 1 + I

@[simp] lemma onePlusI_re : onePlusI.re = 1 := rfl
@[simp] lemma onePlusI_im : onePlusI.im = 1 := rfl

lemma norm_onePlusI : onePlusI.norm = 2 := by rw [norm_def]; norm_num

lemma onePlusI_ne_zero : onePlusI ≠ 0 := by
  intro h; have := congrArg Zsqrtd.re h; simp at this

/-- `1 + i ∣ a + b i` iff `a ≡ b (mod 2)`. -/
lemma onePlusI_dvd_iff (α : ℤ[i]) : onePlusI ∣ α ↔ 2 ∣ α.re + α.im := by
  rw [dvd_iff_norm_dvd onePlusI_ne_zero, norm_onePlusI]
  simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_star, Zsqrtd.im_star, onePlusI_re,
    onePlusI_im]
  constructor
  · rintro ⟨h, -⟩; convert h using 1; ring
  · intro h; refine ⟨by convert h using 1; ring, ?_⟩
    obtain ⟨k, hk⟩ := h
    exact ⟨α.im - k, by linear_combination -hk⟩

lemma onePlusI_sq : onePlusI ^ 2 = 2 * I := by ext <;> simp [sq]

lemma onePlusI_cube : onePlusI ^ 3 = -2 + 2 * I := by ext <;> simp [pow_succ]

/-- **Lemma 3 of §7** (factorization part): `2 = -i (1 + i)²`. -/
@[kb "irelandrosen1990" "Ch. 9, §7, Lemma 3, p. 131"]
theorem two_eq_neg_I_mul_onePlusI_sq : (2 : ℤ[i]) = -I * onePlusI ^ 2 := by
  ext <;> simp [sq]

lemma norm_onePlusI_cube : (onePlusI ^ 3).norm = 8 := by
  rw [norm_def]; simp [pow_succ]

/-- `(1 + i)³ ∣ a + b i` iff `a + b ≡ 0` and `a - b ≡ 0 (mod 4)`. -/
lemma onePlusI_cube_dvd_iff (α : ℤ[i]) :
    onePlusI ^ 3 ∣ α ↔ 4 ∣ α.re + α.im ∧ 4 ∣ α.re - α.im := by
  constructor
  · rintro ⟨γ, rfl⟩
    rw [onePlusI_cube]
    simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_neg,
      Zsqrtd.im_neg, I_re, I_im]
    norm_num
    exact ⟨⟨-γ.im, by ring⟩, ⟨-γ.re, by ring⟩⟩
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    refine ⟨⟨-v, -u⟩, ?_⟩
    rw [onePlusI_cube]
    ext <;> simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_neg,
      Zsqrtd.im_neg, I_re, I_im] <;> norm_num <;> linarith

/-! ### Primary elements -/

/-- The congruence `α ≡ 1 (mod (1 + i)³)` (no nonunit condition; `1` satisfies it). -/
def IsPrimary' (α : ℤ[i]) : Prop := onePlusI ^ 3 ∣ α - 1

/-- **Definition (§7).** A nonunit `α ∈ ℤ[i]` is *primary* if `α ≡ 1 (mod (1 + i)³)`. -/
@[kb "irelandrosen1990" "Ch. 9, §7, Definition (primary), p. 132"]
def IsPrimary (α : ℤ[i]) : Prop := ¬ IsUnit α ∧ IsPrimary' α

lemma isPrimary'_iff (α : ℤ[i]) :
    IsPrimary' α ↔ 4 ∣ α.re - 1 + α.im ∧ 4 ∣ α.re - 1 - α.im := by
  rw [IsPrimary', onePlusI_cube_dvd_iff]; simp

/-- **Lemma 6 of §7.** A nonunit `a + b i` is primary iff `a ≡ 1, b ≡ 0 (mod 4)` or
`a ≡ 3, b ≡ 2 (mod 4)`. -/
@[kb "irelandrosen1990" "Ch. 9, §7, Lemma 6, p. 132"]
theorem isPrimary_iff (α : ℤ[i]) :
    IsPrimary α ↔ ¬ IsUnit α ∧
      ((α.re % 4 = 1 ∧ α.im % 4 = 0) ∨ (α.re % 4 = 3 ∧ α.im % 4 = 2)) := by
  rw [IsPrimary, isPrimary'_iff]
  apply and_congr_right; intro _; omega

lemma isPrimary'_one : IsPrimary' 1 := by simp [IsPrimary']

lemma IsPrimary'.mul {α β : ℤ[i]} (hα : IsPrimary' α) (hβ : IsPrimary' β) :
    IsPrimary' (α * β) := by
  unfold IsPrimary' at *
  have : α * β - 1 = (α - 1) * β + (β - 1) := by ring
  rw [this]; exact dvd_add (dvd_mul_of_dvd_left hα _) hβ

lemma isPrimary'_prod {ι : Type*} (s : Finset ι) (f : ι → ℤ[i]) (h : ∀ i ∈ s, IsPrimary' (f i)) :
    IsPrimary' (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isPrimary'_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma isPrimary'_multiset_prod (s : Multiset ℤ[i]) (h : ∀ x ∈ s, IsPrimary' x) :
    IsPrimary' s.prod := by
  induction s using Multiset.induction_on with
  | empty => simpa using isPrimary'_one
  | cons a s ih =>
    rw [Multiset.prod_cons]
    exact (h a (Multiset.mem_cons_self _ _)).mul (ih fun x hx => h x (Multiset.mem_cons_of_mem hx))

lemma IsPrimary'.not_onePlusI_dvd {α : ℤ[i]} (h : IsPrimary' α) : ¬ onePlusI ∣ α := by
  rw [isPrimary'_iff] at h; rw [onePlusI_dvd_iff]; omega

lemma IsPrimary'.star {α : ℤ[i]} (h : IsPrimary' α) : IsPrimary' (star α) := by
  rw [isPrimary'_iff] at *; simp only [Zsqrtd.re_star, Zsqrtd.im_star]; omega

lemma IsPrimary'.re_odd {α : ℤ[i]} (h : IsPrimary' α) : α.re % 2 = 1 := by
  rw [isPrimary'_iff] at h; omega

lemma IsPrimary'.im_even {α : ℤ[i]} (h : IsPrimary' α) : 2 ∣ α.im := by
  rw [isPrimary'_iff] at h; omega

/-- A unit that is `≡ 1 (mod (1 + i)³)` is `1`. -/
lemma IsPrimary'.eq_one_of_isUnit {u : ℤ[i]} (h : IsPrimary' u) (hu : IsUnit u) : u = 1 := by
  rw [isPrimary'_iff] at h
  rcases isUnit_iff_eq.1 hu with rfl | rfl | rfl | rfl <;> simp_all

lemma isPrimary'_unit_mul_iff (α : ℤ[i]) :
    (IsPrimary' (1 * α) ↔ 4 ∣ α.re - 1 + α.im ∧ 4 ∣ α.re - 1 - α.im) ∧
    (IsPrimary' (-1 * α) ↔ 4 ∣ -α.re - 1 - α.im ∧ 4 ∣ -α.re - 1 + α.im) ∧
    (IsPrimary' (I * α) ↔ 4 ∣ -α.im - 1 + α.re ∧ 4 ∣ -α.im - 1 - α.re) ∧
    (IsPrimary' (-I * α) ↔ 4 ∣ α.im - 1 - α.re ∧ 4 ∣ α.im - 1 + α.re) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [isPrimary'_iff] <;> simp <;> omega

lemma exists_isPrimary'_unit_mul {α : ℤ[i]} (h2 : ¬ onePlusI ∣ α) :
    ∃ u : ℤ[i], IsUnit u ∧ IsPrimary' (u * α) := by
  rw [onePlusI_dvd_iff] at h2
  obtain ⟨c1, c2, c3, c4⟩ := isPrimary'_unit_mul_iff α
  by_cases h1 : 4 ∣ α.re - 1 + α.im ∧ 4 ∣ α.re - 1 - α.im
  · exact ⟨1, isUnit_one, c1.2 h1⟩
  by_cases h1' : 4 ∣ -α.re - 1 - α.im ∧ 4 ∣ -α.re - 1 + α.im
  · exact ⟨-1, isUnit_one.neg, c2.2 h1'⟩
  by_cases h3 : 4 ∣ -α.im - 1 + α.re ∧ 4 ∣ -α.im - 1 - α.re
  · exact ⟨I, isUnit_I, c3.2 h3⟩
  · exact ⟨-I, isUnit_I.neg, c4.2 (by omega)⟩

lemma unit_eq_of_isPrimary' {α u v : ℤ[i]} (hu : IsUnit u) (hv : IsUnit v)
    (hu' : IsPrimary' (u * α)) (hv' : IsPrimary' (v * α)) : u = v := by
  obtain ⟨c1, c2, c3, c4⟩ := isPrimary'_unit_mul_iff α
  rcases isUnit_iff_eq.1 hu with rfl | rfl | rfl | rfl <;>
  rcases isUnit_iff_eq.1 hv with rfl | rfl | rfl | rfl <;>
  first | rfl | (simp only [c1, c2, c3, c4] at hu' hv'; omega)

/-- **Lemma 7 of §7.** If `α` is a nonunit not divisible by `1 + i`, there is a unique unit `u`
with `u α` primary. -/
@[kb "irelandrosen1990" "Ch. 9, §7, Lemma 7, p. 132"]
theorem existsUnique_isPrimary_unit_mul {α : ℤ[i]} (hα : ¬ IsUnit α) (h2 : ¬ onePlusI ∣ α) :
    ∃! u : ℤ[i], IsUnit u ∧ IsPrimary (u * α) := by
  obtain ⟨u, hu, hu'⟩ := exists_isPrimary'_unit_mul h2
  refine ⟨u, ⟨hu, fun h => hα (isUnit_of_mul_isUnit_right h), hu'⟩, ?_⟩
  rintro v ⟨hv, -, hv'⟩
  exact unit_eq_of_isPrimary' hv hu hv' hu'

end Gaussian

end NTKB.IrelandRosen
