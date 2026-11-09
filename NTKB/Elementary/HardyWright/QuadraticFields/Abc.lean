/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Attr
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Aesop.BuiltinRules
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.Sheaves.Presheaf
/-!
# The abc conjecture and Fermat's equation (Hardy–Wright, notes to Chapter XIII, § 13.7)

The notes state the abc conjecture of Oesterlé and Masser: for `ε > 0` there is `K(ε)` such that
`c ≤ K(ε) r(abc)^(1+ε)` whenever `a + b = c` in positive integers, `r(m)` the product of the distinct
prime factors of `m`. (The coprimality of `a` and `b`, omitted in the book's sentence, is part of the
conjecture: without it `a = b = 2^k` would contradict it.) The conjecture is assumed here as the named
hypothesis `AbcConjecture`, not proved.

* `fermat_finite_of_abc`: the abc conjecture implies that Fermat's equation `xⁿ + yⁿ = zⁿ` has
  only finitely many solutions in coprime positive integers `x, y, z` and `n ≥ 4`: `r(xⁿyⁿzⁿ) ≤ xyz < z³`
  gives `zⁿ ≤ K z^(3(1+ε))`, and `ε = 1/6`, `n ≥ 4` give `zⁿ ≤ K⁸`. (The book writes
  `ε = 1/2`, but its exponent `7/2 = 3(1 + 1/6)` needs `ε = 1/6`.)
-/

namespace NTKB.HardyWright

/-- The abc conjecture (Oesterlé, Masser), an assumed hypothesis: for every `ε > 0` there is `K` with
`c ≤ K r(abc)^(1+ε)` for all coprime positive integers `a, b` with `a + b = c`, where
`r(m) = ∏_{p ∣ m} p`. -/
structure AbcConjecture : Prop where
  bound : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ a b c : ℕ, 0 < a → 0 < b → a + b = c → Nat.Coprime a b →
    (c : ℝ) ≤ K * (((a * b * c).primeFactors.prod id : ℕ) : ℝ) ^ (1 + ε)

/-- The radical `∏_{p ∣ m} p` of `(xyz)ⁿ` is at most `xyz`. -/
lemma radical_pow_le {x y z n : ℕ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hn : n ≠ 0) :
    (x ^ n * y ^ n * z ^ n).primeFactors.prod id ≤ x * y * z := by
  rw [← mul_pow, ← mul_pow, Nat.primeFactors_pow _ hn]
  exact Nat.le_of_dvd (by positivity) (Nat.prod_primeFactors_dvd _)

/-- **Notes to Chapter XIII (§ 13.7).** The abc conjecture implies that Fermat's equation
`xⁿ + yⁿ = zⁿ` has at most finitely many solutions in coprime positive integers `x, y, z` with
`n ≥ 4`. -/
@[kb "hardywright2008" "Notes 13.7, p. 282"]
theorem fermat_finite_of_abc (habc : AbcConjecture) :
    {s : ℕ × ℕ × ℕ × ℕ | 0 < s.1 ∧ 0 < s.2.1 ∧ Nat.Coprime s.1 s.2.1 ∧ 4 ≤ s.2.2.2 ∧
      s.1 ^ s.2.2.2 + s.2.1 ^ s.2.2.2 = s.2.2.1 ^ s.2.2.2}.Finite := by
  obtain ⟨K, hK⟩ := habc.bound (1 / 6) (by norm_num)
  set B := ⌈K ^ 8⌉₊
  -- every solution has `zⁿ ≤ K⁸`
  have key : ∀ x y z n : ℕ, 0 < x → 0 < y → Nat.Coprime x y → 4 ≤ n → x ^ n + y ^ n = z ^ n →
      x < z ∧ y < z ∧ ((z : ℝ) ^ n ≤ K ^ 8) := by
    intro x y z n hx hy hxy hn h
    have hn0 : n ≠ 0 := by omega
    have hxz : x < z := by
      have : x ^ n < z ^ n := by rw [← h]; have := pow_pos hy n; omega
      exact lt_of_pow_lt_pow_left₀ n (Nat.zero_le _) this
    have hyz : y < z := by
      have : y ^ n < z ^ n := by rw [← h]; have := pow_pos hx n; omega
      exact lt_of_pow_lt_pow_left₀ n (Nat.zero_le _) this
    have hz0 : 0 < z := by omega
    refine ⟨hxz, hyz, ?_⟩
    have habc' := hK (x ^ n) (y ^ n) (z ^ n) (pow_pos hx n) (pow_pos hy n) h (hxy.pow n n)
    have hrad := radical_pow_le hx hy hz0 hn0
    have hxyz : x * y * z < z ^ 3 := by
      have : x * y < z * z := Nat.mul_lt_mul'' hxz hyz
      calc x * y * z < z * z * z := Nat.mul_lt_mul_of_pos_right this hz0
        _ = z ^ 3 := by ring
    set R := (x ^ n * y ^ n * z ^ n).primeFactors.prod id
    have hR : (R : ℝ) ≤ (z : ℝ) ^ 3 := by exact_mod_cast (hrad.trans hxyz.le)
    have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
    have hz1 : (1 : ℝ) ≤ z := by exact_mod_cast hz0
    have hzn : (0 : ℝ) < (z : ℝ) ^ n := by positivity
    push_cast at habc'
    have hKpos : 0 < K := by
      by_contra hK0
      push Not at hK0
      have : K * (R : ℝ) ^ (1 + 1 / 6 : ℝ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hK0 (Real.rpow_nonneg hR0 _)
      linarith
    -- `r(abc)^(7/6) ≤ z^(7/2) ≤ z^(7n/8)`
    have h1 : (R : ℝ) ^ (1 + 1 / 6 : ℝ) ≤ (z : ℝ) ^ (7 * n / 8 : ℝ) := by
      calc (R : ℝ) ^ (1 + 1 / 6 : ℝ) ≤ ((z : ℝ) ^ 3) ^ (1 + 1 / 6 : ℝ) :=
            Real.rpow_le_rpow hR0 hR (by norm_num)
        _ = (z : ℝ) ^ (7 / 2 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
        _ ≤ (z : ℝ) ^ (7 * n / 8 : ℝ) := by
            apply Real.rpow_le_rpow_of_exponent_le hz1
            have : (4 : ℝ) ≤ n := by exact_mod_cast hn
            linarith
    have h2 : (z : ℝ) ^ n ≤ K * (z : ℝ) ^ (7 * n / 8 : ℝ) :=
      le_trans habc' (mul_le_mul_of_nonneg_left h1 hKpos.le)
    -- `z^(n/8) < K`
    have hsplit : (z : ℝ) ^ n = (z : ℝ) ^ (7 * n / 8 : ℝ) * (z : ℝ) ^ (n / 8 : ℝ) := by
      rw [← Real.rpow_add (by positivity), ← Real.rpow_natCast]; congr 1; ring
    have hpos : (0 : ℝ) < (z : ℝ) ^ (7 * n / 8 : ℝ) := by positivity
    have h3 : (z : ℝ) ^ (n / 8 : ℝ) ≤ K := by
      rw [hsplit, mul_comm K] at h2
      exact le_of_mul_le_mul_left h2 hpos
    have h4 : ((z : ℝ) ^ (n / 8 : ℝ)) ^ (8 : ℕ) = (z : ℝ) ^ n := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      rw [← Real.rpow_natCast]; congr 1; push_cast; ring
    rw [← h4]
    exact pow_le_pow_left₀ (by positivity) h3 8
  -- hence all coordinates are below `B = ⌈K⁸⌉`
  apply ((Set.finite_Iic B).prod ((Set.finite_Iic B).prod ((Set.finite_Iic B).prod
    (Set.finite_Iic B)))).subset
  rintro ⟨x, y, z, n⟩ ⟨hx, hy, hxy, hn, h⟩
  dsimp only at hx hy hxy hn h
  obtain ⟨hxz, hyz, hzn⟩ := key x y z n hx hy hxy hn h
  have hznB : z ^ n ≤ B := by
    have : ((z ^ n : ℕ) : ℝ) ≤ B := by
      push_cast
      exact le_trans hzn (Nat.le_ceil _)
    exact_mod_cast this
  have hz2 : 2 ≤ z := by omega
  have hzle : z ≤ z ^ n := Nat.le_self_pow (by omega) z
  have hnle : n < z ^ n := lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_left hz2 n)
  simp only [Set.mem_prod, Set.mem_Iic]
  refine ⟨by omega, by omega, by omega, by omega⟩

end NTKB.HardyWright
