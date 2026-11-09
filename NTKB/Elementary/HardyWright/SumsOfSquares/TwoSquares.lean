/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Multiplicity
import Aesop.BuiltinRules
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Bound
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import NTKB.Attr

/-!
# Hardy–Wright, § 20.3: primitive representations by two squares

`n = x² + y²` is a *primitive* representation when `(x, y) = 1`.

* Theorem 367: if `p = 4m + 3` divides `n`, then `n` has no primitive representation
  (`not_primitive_sq_add_sq`).
* Theorem 368: if `p = 4m + 3` divides `n` to an odd power, then `n` has no representation
  (`not_sq_add_sq_of_odd_multiplicity`).

Both follow the book: Theorem 367 because `-1` would be a quadratic residue of `p` (Theorem 82 is
Mathlib's `ZMod.exists_sq_eq_neg_one_iff`), Theorem 368 by dividing out `(x, y)` and applying 367.
-/

namespace NTKB.HardyWright

/-- **Theorem 367** (Hardy–Wright). If `p = 4m + 3` is prime and `p ∣ n`, then `n` has no primitive
representation `n = x² + y²`, `(x, y) = 1`. -/
@[kb "hardywright2008" "Thm 367, p. 415"]
theorem not_primitive_sq_add_sq {p : ℕ} (hp : p.Prime) (h3 : p % 4 = 3) {n : ℤ} (hpn : (p : ℤ) ∣ n)
    {x y : ℤ} (hxy : IsCoprime x y) (hn : n = x ^ 2 + y ^ 2) : False := by
  have := Fact.mk hp
  -- `p ∤ x`: otherwise `p ∣ y²`, so `p ∣ y`
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hx : ((x : ℤ) : ZMod p) ≠ 0 := by
    intro hx0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hx0
    have hy2 : (p : ℤ) ∣ y ^ 2 := by
      have : (p : ℤ) ∣ x ^ 2 + y ^ 2 := hn ▸ hpn
      exact (dvd_add_right (dvd_pow hx0 two_ne_zero)).1 this
    have hy := hpZ.dvd_of_dvd_pow hy2
    exact hpZ.not_isUnit (hxy.isUnit_of_dvd' hx0 hy)
  -- `y ≡ l x (mod p)` and `x²(1 + l²) ≡ 0`, so `-1` is a square mod `p`
  have hsum : ((x : ZMod p)) ^ 2 + ((y : ZMod p)) ^ 2 = 0 := by
    have : ((x ^ 2 + y ^ 2 : ℤ) : ZMod p) = 0 := by
      rw [← hn, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hpn
    push_cast at this; exact this
  have hsq : IsSquare (-1 : ZMod p) := ⟨(y : ZMod p) / x, by
    field_simp
    linear_combination -hsum⟩
  exact (ZMod.exists_sq_eq_neg_one_iff (p := p)).1 hsq h3

/-- **Theorem 368** (Hardy–Wright). If `p = 4m + 3` is prime and divides `n ≠ 0` to an odd power,
then `n` is not a sum of two squares. -/
@[kb "hardywright2008" "Thm 368, p. 415"]
theorem not_sq_add_sq_of_odd_multiplicity {p : ℕ} (hp : p.Prime) (h3 : p % 4 = 3) {n : ℕ}
    (hn : n ≠ 0) (hodd : Odd (multiplicity p n)) {x y : ℤ} (hxy : (n : ℤ) = x ^ 2 + y ^ 2) : False := by
  have := Fact.mk hp
  -- `x = dX`, `y = dY`, `(X, Y) = 1`, `n = d² N`
  have hd0 : 0 < Int.gcd x y := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    rw [Int.gcd_eq_zero_iff] at h0
    rw [h0.1, h0.2] at hxy; simp at hxy; exact hn hxy
  obtain ⟨g, X, Y, hg, hXY, hx, hy⟩ := Int.exists_gcd_one' hd0
  have hN : (n : ℤ) = (g : ℤ) ^ 2 * (X ^ 2 + Y ^ 2) := by rw [hxy, hx, hy]; ring
  set N := (X ^ 2 + Y ^ 2).toNat with hNdef
  have hNcast : (N : ℤ) = X ^ 2 + Y ^ 2 := Int.toNat_of_nonneg (by positivity)
  have hnN : n = g ^ 2 * N := by
    have : (n : ℤ) = ((g ^ 2 * N : ℕ) : ℤ) := by push_cast; rw [hNcast, hN]
    exact_mod_cast this
  have hN0 : N ≠ 0 := by rintro h; rw [h, mul_zero] at hnN; exact hn hnN
  have hv : multiplicity p n = 2 * multiplicity p g + multiplicity p N := by
    rw [hnN, Nat.multiplicity_mul (pow_ne_zero 2 hg.ne') hN0, Nat.multiplicity_pow]
  -- the exponent of `p` in `N` is `c - 2γ`, which is odd, hence positive
  have hvN : 0 < multiplicity p N := by
    rw [hv] at hodd; obtain ⟨k, hk⟩ := hodd; omega
  have hpN : p ∣ N := dvd_of_one_le_multiplicity hvN
  exact not_primitive_sq_add_sq hp h3 (n := X ^ 2 + Y ^ 2)
    (by rw [← hNcast]; exact_mod_cast hpN) (Int.isCoprime_iff_gcd_eq_one.2 hXY) rfl

end NTKB.HardyWright
