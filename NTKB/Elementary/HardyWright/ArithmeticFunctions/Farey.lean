/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.ArithmeticFunctions.Average

/-!
# Hardy–Wright, § 18.5: the number of terms of the Farey series

The Farey series `F_n` of order `n` (Hardy–Wright § 3.1) is the set of fractions `h/k` with
`0 ≤ h ≤ k ≤ n` (Mathlib has no Farey series). It has `Φ(n) + 1` terms (§ 18.5), so by
Theorem 330:

* Theorem 331: the number of terms of `F_n` is approximately `3n²/π²`; more precisely it is
  `3n²/π² + O(n log n)`.

(The definition here is local to this file, as the set of values; a fuller treatment of the Farey
series belongs to Chapter III.)
-/

open Finset Filter Topology Asymptotics Real

namespace NTKB.HardyWright

/-- The Farey series of order `n`: the rationals `h/k` with `0 ≤ h ≤ k`, `1 ≤ k ≤ n`. -/
def fareySeries (n : ℕ) : Finset ℚ :=
  ((Icc 0 n ×ˢ Icc 1 n).filter fun x => x.1 ≤ x.2).image fun x => (x.1 : ℚ) / x.2

/-- The reduced pairs `(h, k)`: `0 ≤ h ≤ k`, `1 ≤ k ≤ n`, `(h, k) = 1`. -/
def fareyPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 0 n ×ˢ Icc 1 n).filter fun x => x.1 ≤ x.2 ∧ Nat.Coprime x.1 x.2)

lemma fareySeries_eq_image (n : ℕ) :
    fareySeries n = (fareyPairs n).image fun x => (x.1 : ℚ) / x.2 := by
  apply le_antisymm
  · intro q hq
    simp only [fareySeries, mem_image, mem_filter, mem_product, mem_Icc] at hq
    obtain ⟨⟨h, k⟩, ⟨⟨⟨_, hh⟩, hk1, hk⟩, hhk⟩, rfl⟩ := hq
    simp only [fareyPairs, mem_image, mem_filter, mem_product, mem_Icc]
    set g := Nat.gcd h k with hg
    have hg0 : 0 < g := Nat.gcd_pos_of_pos_right h hk1
    refine ⟨⟨h / g, k / g⟩, ⟨⟨⟨Nat.zero_le _, (Nat.div_le_self _ _).trans hh⟩,
      Nat.div_pos (Nat.le_of_dvd hk1 (Nat.gcd_dvd_right h k)) hg0, (Nat.div_le_self _ _).trans hk⟩,
      Nat.div_le_div_right hhk, Nat.coprime_div_gcd_div_gcd hg0⟩, ?_⟩
    simp only
    rw [Nat.cast_div (Nat.gcd_dvd_left h k) (by exact_mod_cast hg0.ne'),
      Nat.cast_div (Nat.gcd_dvd_right h k) (by exact_mod_cast hg0.ne')]
    have : (g : ℚ) ≠ 0 := by exact_mod_cast hg0.ne'
    field_simp
  · intro q hq
    simp only [fareyPairs, mem_image, mem_filter, mem_product, mem_Icc] at hq
    obtain ⟨x, ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5, _⟩, rfl⟩ := hq
    simp only [fareySeries, mem_image, mem_filter, mem_product, mem_Icc]
    exact ⟨x, ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩, rfl⟩

lemma injOn_fareyPairs (n : ℕ) :
    Set.InjOn (fun x : ℕ × ℕ => (x.1 : ℚ) / x.2) (fareyPairs n) := by
  intro x hx y hy hxy
  simp only [fareyPairs, coe_filter, mem_product, mem_Icc, Set.mem_ofPred_eq] at hx hy
  simp only at hxy
  have hx0 : (0 : ℤ) < x.2 := by exact_mod_cast hx.1.2.1
  have hy0 : (0 : ℤ) < y.2 := by exact_mod_cast hy.1.2.1
  have e1 := Rat.num_div_eq_of_coprime (a := (x.1 : ℤ)) hx0 (by simpa using hx.2.2)
  have e2 := Rat.num_div_eq_of_coprime (a := (y.1 : ℤ)) hy0 (by simpa using hy.2.2)
  have d1 := Rat.den_div_eq_of_coprime (a := (x.1 : ℤ)) hx0 (by simpa using hx.2.2)
  have d2 := Rat.den_div_eq_of_coprime (a := (y.1 : ℤ)) hy0 (by simpa using hy.2.2)
  push_cast at e1 e2 d1 d2
  rw [hxy] at e1 d1
  ext
  · have := e1.symm.trans e2; exact_mod_cast this
  · have := d1.symm.trans d2; exact_mod_cast this

lemma card_fareyPairs (n : ℕ) (hn : 1 ≤ n) :
    #(fareyPairs n) = 1 + ∑ q ∈ Ioc 0 n, q.totient := by
  rw [← card_coprime_fractionPairs]
  have hsplit : fareyPairs n = {(0, 1)} ∪ (fractionPairs n).filter fun x => Nat.Coprime x.1 x.2 := by
    ext ⟨h, k⟩
    simp only [fareyPairs, fractionPairs, mem_union, mem_singleton, mem_filter, mem_product,
      mem_Icc, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨_, h2⟩, h3, h4⟩, h5, h6⟩
      rcases Nat.eq_zero_or_pos h with rfl | hh
      · left; exact ⟨rfl, (Nat.coprime_zero_left k).mp h6⟩
      · right; exact ⟨⟨⟨⟨hh, h2⟩, h3, h4⟩, h5⟩, h6⟩
    · rintro (⟨rfl, rfl⟩ | ⟨⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩, h6⟩)
      · exact ⟨⟨⟨le_rfl, Nat.zero_le _⟩, le_rfl, hn⟩, Nat.zero_le _, Nat.coprime_zero_left 1 |>.mpr rfl⟩
      · exact ⟨⟨⟨Nat.zero_le _, h2⟩, h3, h4⟩, h5, h6⟩
  rw [hsplit, card_union_of_disjoint, card_singleton]
  rw [disjoint_singleton_left]
  simp [fractionPairs]

/-- The number of terms of the Farey series of order `n` is `Φ(n) + 1`. -/
theorem card_fareySeries (n : ℕ) (hn : 1 ≤ n) :
    #(fareySeries n) = 1 + ∑ q ∈ Ioc 0 n, q.totient := by
  rw [fareySeries_eq_image, card_image_of_injOn (injOn_fareyPairs n), card_fareyPairs n hn]

/-- **Theorem 331** (Hardy–Wright). The number of terms in the Farey series of order `n` is
approximately `3n²/π²`; precisely, it is `3n²/π² + O(n log n)`. -/
@[kb "hardywright2008" "Thm 331, p. 373"]
theorem card_fareySeries_sub_isBigO :
    (fun n : ℕ => (#(fareySeries n) : ℝ) - 3 * (n : ℝ) ^ 2 / π ^ 2) =O[atTop]
      fun n => (n : ℝ) * log n := by
  have h := sum_totient_sub_isBigO
  have h1 : (fun _ : ℕ => (1 : ℝ)) =O[atTop] fun n => (n : ℝ) * log n := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 3] with n hn
    have := one_le_log_of_three_le hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    rw [norm_one, Real.norm_of_nonneg (by positivity), one_mul]
    nlinarith
  refine (h.add h1).congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [card_fareySeries n hn]
  push_cast
  ring

/-- **Theorem 331** (Hardy–Wright), as an asymptotic equivalence: `#F_n ~ 3n²/π²`. -/
@[kb "hardywright2008" "Thm 331, p. 373"]
theorem card_fareySeries_isEquivalent :
    (fun n : ℕ => (#(fareySeries n) : ℝ)) ~[atTop] fun n => 3 * (n : ℝ) ^ 2 / π ^ 2 := by
  show (_ - _) =o[atTop] _
  refine card_fareySeries_sub_isBigO.trans_isLittleO ?_
  have hlo : (fun n : ℕ => (n : ℝ) * log n) =o[atTop] fun n => (n : ℝ) ^ 2 := by
    have h1 : (fun n : ℕ => log (n : ℝ)) =o[atTop] fun n => (n : ℝ) :=
      isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
    simpa [sq] using (isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).mul_isLittleO h1
  refine hlo.trans_isBigO ?_
  refine IsBigO.of_bound (π ^ 2 / 3) (Eventually.of_forall fun n => ?_)
  have hpi : 0 < π ^ 2 := by positivity
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  field_simp
  rfl

end NTKB.HardyWright
