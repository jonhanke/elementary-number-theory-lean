/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Waring
import NTKB.Attr
import Mathlib.Computability.Reduce
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.Data.Nat.Bitwise

/-!
# Hardy–Wright, §§ 21.2–21.4: cubes, sixth and eighth powers

* Theorem 389: every `n > 10²⁵` is the sum of `13` cubes (`isSumOfPowers_three_thirteen_of_gt`).
* Theorem 388: `G(3) ≤ 13` (`eventually_isSumOfPowers_three_thirteen`).
* Theorem 390: `g(3) ≤ 13` (`isSumOfPowers_three_thirteen`, `waringNumber_three_le`).
* Identity (21.4.1) and Theorem 391: `g(6) ≤ 184 g(3) + 59 ≤ 2451`.
* Identity (21.4.2) and Theorem 392: `g(8) ≤ 840 g(4) + 273 ≤ 42273`.

The proof of Theorem 390 uses, as the book does, the table "every number up to `40000` is the sum
of `9` cubes, and every number from `240` to `40000` of `8`". Here it is checked by the kernel
(`decide +kernel`) as an identity between bit masks: bit `n` of `cubeMask j` is set exactly when
`n ≤ 40000` is found to be a sum of `j` cubes `c³`, `c ≤ 34`.
Constants of the proofs are recomputed by `docs/scripts/cubes_constants.py`.
-/

open Finset Filter

namespace NTKB.HardyWright

/-! ### Theorems 388 and 389 -/

/-- `x³ ≡ x (mod 6)`. -/
lemma zmod_six_cube (a : ZMod 6) : a ^ 3 = a := by revert a; decide

/-- `(Z + x)³ + (Z - x)³ = 2Z³ + 6Zx²`. -/
lemma cube_add_cube_sub {Z x : ℕ} (hx : x ≤ Z) :
    (Z + x) ^ 3 + (Z - x) ^ 3 = 2 * Z ^ 3 + 6 * Z * x ^ 2 := by
  have : ((Z + x) ^ 3 + (Z - x) ^ 3 : ℕ) = ((2 * Z ^ 3 + 6 * Z * x ^ 2 : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub hx]; ring
  exact_mod_cast this

/-- The heart of Theorems 388 and 389 (Hardy–Wright § 21.2): if `z ≡ 1 (mod 6)` and
`11z⁹ + (z³ + 1)³ + 125z³ ≤ n ≤ 14z⁹`, then `n` is the sum of `13` cubes. -/
lemma isSumOfPowers_three_thirteen_of_mem {z n : ℕ} (hz : z % 6 = 1)
    (h1 : 11 * z ^ 9 + (z ^ 3 + 1) ^ 3 + 125 * z ^ 3 ≤ n) (h2 : n ≤ 14 * z ^ 9) :
    IsSumOfPowers 3 13 n := by
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = z ^ 3 := ⟨_, rfl⟩
  have hz9 : z ^ 9 = Z ^ 3 := by rw [hZ, ← pow_mul]
  rw [hz9] at h1 h2
  rw [← hZ] at h1
  have hz7 : 7 ≤ z := by
    by_contra h
    have : z = 1 := by omega
    subst this
    simp at hZ; subst hZ; omega
  have hZ1 : 1 < Z := by rw [hZ]; exact Nat.one_lt_pow (by norm_num) (by omega)
  have hcop : Nat.Coprime 6 Z := by
    rw [hZ]
    refine Nat.Coprime.pow_right 3 ?_
    rw [Nat.Coprime, Nat.gcd_rec, hz]; rfl
  -- `n ≡ 6r (mod z³)`, `1 ≤ r ≤ z³`
  obtain ⟨y, -, hy⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hZ1
  set r0 := (y * n) % Z with hr0
  set r := if r0 = 0 then Z else r0 with hr
  have hr1 : 1 ≤ r ∧ r ≤ Z := by
    rw [hr]; split_ifs with h
    · exact ⟨by omega, le_rfl⟩
    · exact ⟨Nat.one_le_iff_ne_zero.2 h, (Nat.mod_lt _ (by omega)).le⟩
  have hrmod : r ≡ y * n [MOD Z] := by
    rw [hr]; split_ifs with h
    · exact ((Nat.modEq_zero_iff_dvd.2 (dvd_refl Z)).trans (by rw [Nat.ModEq, Nat.zero_mod, ← h])).symm.symm
    · exact Nat.mod_modEq _ _
  have h6r : 6 * r ≡ n [MOD Z] := by
    have h6y : 6 * y ≡ 1 [MOD Z] := by rw [Nat.ModEq, hy, Nat.mod_eq_of_lt hZ1]
    calc 6 * r ≡ 6 * (y * n) [MOD Z] := hrmod.mul_left 6
      _ = (6 * y) * n := by ring
      _ ≡ 1 * n [MOD Z] := h6y.mul_right n
      _ = n := one_mul n
  -- `n ≡ s + 4 (mod 6)`, `0 ≤ s ≤ 5`
  set s := (n + 2) % 6 with hs
  have hs5 : s ≤ 5 := by omega
  set N := (r + 1) ^ 3 + (r - 1) ^ 3 + 2 * (Z - r) ^ 3 + (s * z) ^ 3 with hN
  have hN5 : IsSumOfPowers 3 5 N :=
    ⟨![r + 1, r - 1, Z - r, Z - r, s * z], by simp [Fin.sum_univ_five, hN]; ring⟩
  -- bounds: `0 < N < (z³ + 1)³ + 3z⁹ + 125z³`
  have hb1 : (r + 1) ^ 3 ≤ (Z + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hb2 : (r - 1) ^ 3 < Z ^ 3 := Nat.pow_lt_pow_left (by omega) (by norm_num)
  have hb3 : (Z - r) ^ 3 < Z ^ 3 := Nat.pow_lt_pow_left (by omega) (by norm_num)
  have hb4 : (s * z) ^ 3 ≤ 125 * Z := by
    rw [mul_pow, hZ]; exact Nat.mul_le_mul_right _ (by
      calc s ^ 3 ≤ 5 ^ 3 := Nat.pow_le_pow_left hs5 3
        _ = 125 := by norm_num)
  have hNlt : N + 8 * Z ^ 3 < n := by rw [hN]; omega
  have hNpos : 8 ≤ N := by
    have : 2 ^ 3 ≤ (r + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    rw [hN]; omega
  -- `6z³` divides `n - N - 8z⁹`
  have hNcast : (N : ℤ) = ((r : ℤ) + 1) ^ 3 + ((r : ℤ) - 1) ^ 3 + 2 * ((Z : ℤ) - r) ^ 3 +
      ((s : ℤ) * z) ^ 3 := by
    rw [hN]; push_cast [Nat.cast_sub hr1.1, Nat.cast_sub hr1.2]; ring
  have hdZ : (Z : ℤ) ∣ (n : ℤ) - N - 8 * (Z : ℤ) ^ 3 := by
    obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd.1 h6r)
    push_cast at ht
    have hZz : (Z : ℤ) = (z : ℤ) ^ 3 := by rw [hZ]; push_cast; ring
    refine ⟨t - (2 * (Z : ℤ) ^ 2 - 6 * Z * r + 6 * (r : ℤ) ^ 2 + (s : ℤ) ^ 3) - 8 * (Z : ℤ) ^ 2, ?_⟩
    rw [hNcast, show (n : ℤ) = 6 * r + Z * t by linarith, mul_pow (s : ℤ), ← hZz]
    ring
  have hd6 : (6 : ℤ) ∣ (n : ℤ) - N - 8 * (Z : ℤ) ^ 3 := by
    suffices key : (((n : ℤ) - N - 8 * (Z : ℤ) ^ 3 : ℤ) : ZMod 6) = 0 by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 6).1 key
      exact_mod_cast this
    have hz6 : ((z : ℤ) : ZMod 6) = 1 := by
      have : ((z : ℕ) : ZMod 6) = ((z % 6 : ℕ) : ZMod 6) := (ZMod.natCast_mod z 6).symm
      rw [hz] at this; simpa using this
    have hn6 : ((n : ℤ) : ZMod 6) = ((s : ℤ) : ZMod 6) + 4 := by
      have : ((n + 2 : ℕ) : ZMod 6) = ((s : ℕ) : ZMod 6) := by rw [hs, ZMod.natCast_mod]
      push_cast at this ⊢
      have h6 : (6 : ZMod 6) = 0 := rfl
      linear_combination this - h6
    have hZz : ((Z : ℤ) : ZMod 6) = 1 := by
      rw [hZ]; push_cast; rw [show ((z : ℕ) : ZMod 6) = ((z : ℤ) : ZMod 6) by simp, hz6]; norm_num
    rw [hNcast]
    push_cast
    rw [zmod_six_cube, zmod_six_cube, zmod_six_cube, zmod_six_cube]
    simp only [Int.cast_natCast] at hz6 hZz hn6 ⊢
    rw [hn6, hZz, hz6]
    have h6 : (6 : ZMod 6) = 0 := rfl
    linear_combination -h6
  have hd : ((6 * Z : ℕ) : ℤ) ∣ (n : ℤ) - N - 8 * (Z : ℤ) ^ 3 := by
    push_cast
    exact IsCoprime.mul_dvd (Int.isCoprime_iff_gcd_eq_one.2 (by exact_mod_cast hcop)) hd6 hdZ
  obtain ⟨m, hm⟩ : 6 * Z ∣ n - N - 8 * Z ^ 3 := by
    have : ((n - N - 8 * Z ^ 3 : ℕ) : ℤ) = (n : ℤ) - N - 8 * (Z : ℤ) ^ 3 := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    rw [← this] at hd
    exact Int.natCast_dvd_natCast.1 hd
  -- `0 < m < z⁶`
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, mul_zero] at hm; omega
    · exact h
  have hmZ : m < Z ^ 2 := by
    by_contra h
    push Not at h
    have : 6 * Z * Z ^ 2 ≤ 6 * Z * m := Nat.mul_le_mul_left _ h
    have : 6 * Z * Z ^ 2 = 6 * Z ^ 3 := by ring
    omega
  -- `m = x₁² + x₂² + x₃² + x₄²` with `xᵢ < z³`
  obtain ⟨a, b, c, d, habcd⟩ := Nat.sum_four_squares m
  have hlt : ∀ x : ℕ, x ^ 2 ≤ m → x ≤ Z := fun x hx => by
    have : x ^ 2 < Z ^ 2 := lt_of_le_of_lt hx hmZ
    exact (Nat.pow_lt_pow_iff_left (by norm_num)).1 this |>.le
  have ha := hlt a (by omega)
  have hb := hlt b (by omega)
  have hc := hlt c (by omega)
  have hd' := hlt d (by omega)
  have h8 : IsSumOfPowers 3 8 (8 * Z ^ 3 + 6 * Z * m) := by
    refine ⟨![Z + a, Z - a, Z + b, Z - b, Z + c, Z - c, Z + d, Z - d], ?_⟩
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
    have e1 := cube_add_cube_sub ha
    have e2 := cube_add_cube_sub hb
    have e3 := cube_add_cube_sub hc
    have e4 := cube_add_cube_sub hd'
    rw [← habcd]
    have : 6 * Z * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) =
        6 * Z * a ^ 2 + 6 * Z * b ^ 2 + 6 * Z * c ^ 2 + 6 * Z * d ^ 2 := by ring
    omega
  have := hN5.add h8
  convert this using 1
  omega

/-- `14 z⁹ - (11 (z + 6)⁹ + ((z + 6)³ + 1)³ + 125 (z + 6)³)` is positive for `z ≥ 373`
(Hardy–Wright § 21.3: the intervals `I_z` overlap from `z = 373` on). -/
lemma phi_succ_lt_psi (w : ℕ) :
    11 * (379 + w) ^ 9 + ((379 + w) ^ 3 + 1) ^ 3 + 125 * (379 + w) ^ 3 < 14 * (373 + w) ^ 9 := by
  have : ((14 * (373 + w) ^ 9 : ℕ) : ℤ) - ((11 * (379 + w) ^ 9 + ((379 + w) ^ 3 + 1) ^ 3 +
      125 * (379 + w) ^ 3 : ℕ) : ℤ) =
      20496335081028474732998 + 1234120680603685025292 * (w : ℤ) +
      21040037041166485419 * (w : ℤ) ^ 2 + 179672708833071028 * (w : ℤ) ^ 3 +
      912735542528919 * (w : ℤ) ^ 4 + 2948835751830 * (w : ℤ) ^ 5 + 6153199077 * (w : ℤ) ^ 6 +
      8068104 * (w : ℤ) ^ 7 + 6066 * (w : ℤ) ^ 8 + 2 * (w : ℤ) ^ 9 := by
    push_cast; ring
  have hpos : (0 : ℤ) < 20496335081028474732998 + 1234120680603685025292 * (w : ℤ) +
      21040037041166485419 * (w : ℤ) ^ 2 + 179672708833071028 * (w : ℤ) ^ 3 +
      912735542528919 * (w : ℤ) ^ 4 + 2948835751830 * (w : ℤ) ^ 5 + 6153199077 * (w : ℤ) ^ 6 +
      8068104 * (w : ℤ) ^ 7 + 6066 * (w : ℤ) ^ 8 + 2 * (w : ℤ) ^ 9 := by positivity
  have := this ▸ hpos
  omega

/-- **Theorem 389** (Hardy–Wright). Every `n > 10²⁵` is the sum of `13` cubes. -/
@[kb "hardywright2008" "Thm 389, p. 441"]
theorem isSumOfPowers_three_thirteen_of_gt {n : ℕ} (hn : 10 ^ 25 < n) : IsSumOfPowers 3 13 n := by
  classical
  let φ : ℕ → ℕ := fun z => 11 * z ^ 9 + (z ^ 3 + 1) ^ 3 + 125 * z ^ 3
  let P : ℕ → Prop := fun t => φ (373 + 6 * t) ≤ n
  have hP0 : P 0 := by
    show 11 * (373 + 6 * 0) ^ 9 + ((373 + 6 * 0) ^ 3 + 1) ^ 3 + 125 * (373 + 6 * 0) ^ 3 ≤ n
    norm_num; omega
  set t := Nat.findGreatest P n with ht
  have hPt : P t := Nat.findGreatest_spec (Nat.zero_le n) hP0
  refine isSumOfPowers_three_thirteen_of_mem (z := 373 + 6 * t) (by omega) hPt ?_
  by_contra hlt
  push Not at hlt
  -- then `φ(z + 6) < 14 z⁹ < n`, against the maximality of `t`
  have h1 : P (t + 1) := by
    have := phi_succ_lt_psi (6 * t)
    show φ (373 + 6 * (t + 1)) ≤ n
    simp only [φ]
    rw [show 373 + 6 * (t + 1) = 379 + 6 * t by ring]
    omega
  have h2 : t + 1 ≤ n := by
    have : 373 + 6 * (t + 1) ≤ φ (373 + 6 * (t + 1)) := by
      simp only [φ]
      have : 373 + 6 * (t + 1) ≤ (373 + 6 * (t + 1)) ^ 9 := Nat.le_self_pow (by norm_num) _
      omega
    have := h1
    simp only [P] at this
    omega
  exact Nat.findGreatest_is_greatest (Nat.lt_succ_self t) h2 h1

/-- **Theorem 388** (Hardy–Wright). `G(3) ≤ 13`: all sufficiently large numbers are sums of `13`
cubes. -/
@[kb "hardywright2008" "Thm 388, p. 439"]
theorem eventually_isSumOfPowers_three_thirteen : ∀ᶠ n in atTop, IsSumOfPowers 3 13 n :=
  eventually_atTop.2 ⟨10 ^ 25 + 1, fun _ hn => isSumOfPowers_three_thirteen_of_gt (by omega)⟩

@[kb "hardywright2008" "Thm 388, p. 439"]
theorem asymptoticWaringNumber_three_le : asymptoticWaringNumber 3 ≤ 13 :=
  Nat.sInf_le eventually_isSumOfPowers_three_thirteen

/-! ### Theorem 390 -/

/-- One step of the table: from the bit mask of sums of `j` cubes to that of sums of `j + 1` cubes
(cubes `c³` with `c ≤ 34`, since `35³ > 40000`). -/
def cubeStep (m : ℕ) : ℕ := (List.range 35).foldl (fun acc c => acc ||| (m <<< (c ^ 3))) 0

/-- Bit mask of the numbers `≤ 40000` found to be sums of `j` cubes. -/
def cubeMask : ℕ → ℕ
  | 0 => 1
  | j + 1 => cubeStep (cubeMask j) &&& (2 ^ 40001 - 1)

lemma testBit_foldl_cube (m n : ℕ) : ∀ (L : List ℕ) (acc : ℕ),
    (L.foldl (fun acc c => acc ||| (m <<< (c ^ 3))) acc).testBit n = true →
      acc.testBit n = true ∨ ∃ c ∈ L, c ^ 3 ≤ n ∧ m.testBit (n - c ^ 3) = true
  | [], acc, h => Or.inl h
  | c :: L, acc, h => by
    rcases testBit_foldl_cube m n L _ h with h' | ⟨c', hc', h'⟩
    · rw [Nat.testBit_lor, Bool.or_eq_true] at h'
      rcases h' with h' | h'
      · exact Or.inl h'
      · rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_iff] at h'
        exact Or.inr ⟨c, List.mem_cons_self .., h'.1, h'.2⟩
    · exact Or.inr ⟨c', List.mem_cons_of_mem _ hc', h'⟩

lemma isSumOfPowers_of_testBit_cubeMask : ∀ (j n : ℕ), (cubeMask j).testBit n = true →
    IsSumOfPowers 3 j n
  | 0, n, h => by
    have : n = 0 := by
      simp only [cubeMask] at h
      rw [show (1 : ℕ) = 2 ^ 0 from rfl, Nat.testBit_two_pow, decide_eq_true_iff] at h
      exact h.symm
    subst this; exact isSumOfPowers_zero 3
  | j + 1, n, h => by
    simp only [cubeMask, Nat.testBit_land, Bool.and_eq_true] at h
    rcases testBit_foldl_cube (cubeMask j) n (List.range 35) 0 h.1 with h' | ⟨c, -, hc, h'⟩
    · simp at h'
    · have := (isSumOfPowers_of_testBit_cubeMask j _ h').add (isSumOfPowers_pow 3 c)
      rwa [Nat.sub_add_cancel hc] at this

/-- The table: every `n` with `240 ≤ n ≤ 40000` is the sum of `8` cubes. -/
lemma cubeMask_eight : (cubeMask 8 >>> 240) &&& (2 ^ 39761 - 1) = 2 ^ 39761 - 1 := by
  decide +kernel

/-- The table: every `n < 240` is the sum of `9` cubes. -/
lemma cubeMask_nine : cubeMask 9 &&& (2 ^ 240 - 1) = 2 ^ 240 - 1 := by
  decide +kernel

lemma isSumOfPowers_three_eight_of_le {n : ℕ} (h1 : 240 ≤ n) (h2 : n ≤ 40000) :
    IsSumOfPowers 3 8 n := by
  apply isSumOfPowers_of_testBit_cubeMask
  have := congrArg (fun m => m.testBit (n - 240)) cubeMask_eight
  simp only [Nat.testBit_land, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one] at this
  rw [show 240 + (n - 240) = n by omega] at this
  have hlt : decide (n - 240 < 39761) = true := by simp; omega
  rw [hlt, Bool.and_true] at this
  exact this

lemma isSumOfPowers_three_nine_of_lt {n : ℕ} (h : n < 240) : IsSumOfPowers 3 9 n := by
  apply isSumOfPowers_of_testBit_cubeMask
  have := congrArg (fun m => m.testBit n) cubeMask_nine
  simp only [Nat.testBit_land, Nat.testBit_two_pow_sub_one] at this
  have hlt : decide (n < 240) = true := by simp; omega
  rw [hlt, Bool.and_true] at this
  exact this

/-- One greedy step: `N = m³ + R` with `R ≤ 3M² + 3M` whenever `N ≤ B < (M + 1)³`. -/
lemma exists_cube_add_le {N B M : ℕ} (hN : N ≤ B) (hM : B < (M + 1) ^ 3) :
    ∃ m R, N = m ^ 3 + R ∧ R ≤ 3 * M ^ 2 + 3 * M := by
  classical
  set m := Nat.findGreatest (fun m => m ^ 3 ≤ N) N with hm
  have hm3 : m ^ 3 ≤ N := Nat.findGreatest_spec (P := fun m => m ^ 3 ≤ N) (Nat.zero_le N) (by simp)
  have hm1 : N < (m + 1) ^ 3 := by
    by_contra h
    push Not at h
    have hle : m + 1 ≤ N := le_trans (Nat.le_self_pow (by norm_num) _) h
    exact Nat.findGreatest_is_greatest (Nat.lt_succ_self m) hle h
  have hmM : m ≤ M := by
    by_contra h
    have : (M + 1) ^ 3 ≤ m ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega
  refine ⟨m, N - m ^ 3, by omega, ?_⟩
  have : (m + 1) ^ 3 = m ^ 3 + 3 * m ^ 2 + 3 * m + 1 := by ring
  have h2 : 3 * m ^ 2 ≤ 3 * M ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hmM 2)
  omega

/-- **Theorem 390** (Hardy–Wright). Every non-negative integer is the sum of `13` cubes. -/
@[kb "hardywright2008" "Thm 390, p. 443"]
theorem isSumOfPowers_three_thirteen (n : ℕ) : IsSumOfPowers 3 13 n := by
  rcases lt_or_ge (10 ^ 25) n with hbig | hsmall
  · exact isSumOfPowers_three_thirteen_of_gt hbig
  rcases lt_or_ge n 240 with h240 | h240
  · exact (isSumOfPowers_three_nine_of_lt h240).mono (by norm_num) (by norm_num)
  -- `n = 240 + N`, and five greedy cubes reduce `N` below `35000`
  obtain ⟨m0, R0, e0, b0⟩ := exists_cube_add_le (N := n - 240) (B := 10 ^ 25) (M := 215443469)
    (by omega) (by norm_num)
  obtain ⟨m1, R1, e1, b1⟩ := exists_cube_add_le (N := R0) (M := 518317) b0 (by norm_num)
  obtain ⟨m2, R2, e2, b2⟩ := exists_cube_add_le (N := R1) (M := 9306) b1 (by norm_num)
  obtain ⟨m3, R3, e3, b3⟩ := exists_cube_add_le (N := R2) (M := 638) b2 (by norm_num)
  obtain ⟨m4, R4, e4, b4⟩ := exists_cube_add_le (N := R3) (M := 106) b3 (by norm_num)
  norm_num at b4
  have h8 := isSumOfPowers_three_eight_of_le (n := 240 + R4) (by omega) (by omega)
  have := ((((h8.add (isSumOfPowers_pow 3 m4)).add (isSumOfPowers_pow 3 m3)).add
    (isSumOfPowers_pow 3 m2)).add (isSumOfPowers_pow 3 m1)).add (isSumOfPowers_pow 3 m0)
  convert this using 1
  omega

/-- **Theorem 390** (Hardy–Wright). `g(3) ≤ 13`. -/
@[kb "hardywright2008" "Thm 390, p. 443"]
theorem waringNumber_three_le : waringNumber 3 ≤ 13 := Nat.sInf_le isSumOfPowers_three_thirteen

/-! ### Theorems 391 and 392 -/

/-- A list of pairs `(c, t)` gives `∑ c tᵏ` as the sum of `∑ c` `k`th powers, `k` even. -/
lemma isSumOfPowers_of_list {k : ℕ} (hk : Even k) : ∀ L : List (ℕ × ℤ),
    IsSumOfPowers k (L.map Prod.fst).sum ((L.map fun p => (p.1 : ℤ) * p.2 ^ k).sum).toNat
  | [] => by simpa using isSumOfPowers_zero k
  | p :: L => by
    have h1 := isSumOfPowers_mul_pow k p.1 p.2.natAbs
    have h2 := isSumOfPowers_of_list hk L
    have hc : ((p.2.natAbs ^ k : ℕ) : ℤ) = p.2 ^ k := by
      rw [Nat.cast_pow, Int.natCast_natAbs, hk.pow_abs]
    have hnn : ∀ L : List (ℕ × ℤ), 0 ≤ (L.map fun p => (p.1 : ℤ) * p.2 ^ k).sum := by
      intro L
      induction L with
      | nil => simp
      | cons q L ih => simp only [List.map_cons, List.sum_cons]; have := hk.pow_nonneg q.2; positivity
    convert h1.add h2 using 1
    · simp
    · simp only [List.map_cons, List.sum_cons]
      zify [hnn L]
      rw [Int.toNat_of_nonneg (by have := hk.pow_nonneg p.2; have := hnn L; positivity),
        Int.toNat_of_nonneg (hnn L)]
      push_cast [hc]; rw [hk.pow_abs]

/-- The terms of identity (21.4.1). -/
def sixthPowerTerms (a b c d : ℤ) : List (ℕ × ℤ) :=
  [(1, a + b + c), (1, a + b - c), (1, a - b + c), (1, a - b - c),
   (1, a + b + d), (1, a + b - d), (1, a - b + d), (1, a - b - d),
   (1, a + c + d), (1, a + c - d), (1, a - c + d), (1, a - c - d),
   (1, b + c + d), (1, b + c - d), (1, b - c + d), (1, b - c - d),
   (2, a + b), (2, a - b), (2, a + c), (2, a - c), (2, a + d), (2, a - d),
   (2, b + c), (2, b - c), (2, b + d), (2, b - d), (2, c + d), (2, c - d),
   (36, a), (36, b), (36, c), (36, d)]

/-- **Identity (21.4.1)** (Hardy–Wright):
`60(a² + b² + c² + d²)³ = ∑ (a ± b ± c)⁶ + 2 ∑ (a ± b)⁶ + 36 ∑ a⁶`, `184` sixth powers. -/
@[kb "hardywright2008" "Section 21.4, p. 444"]
theorem sixty_mul_sum_sq_cube (a b c d : ℤ) :
    60 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 3 =
      ((sixthPowerTerms a b c d).map fun p => (p.1 : ℤ) * p.2 ^ 6).sum := by
  simp only [sixthPowerTerms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast; ring

lemma card_sixthPowerTerms (a b c d : ℤ) : ((sixthPowerTerms a b c d).map Prod.fst).sum = 184 := by
  simp [sixthPowerTerms]

/-- The terms of identity (21.4.2). -/
def eighthPowerTerms (a b c d : ℤ) : List (ℕ × ℤ) :=
  [(6, 2 * a), (6, 2 * b), (6, 2 * c), (6, 2 * d),
   (60, a + b), (60, a - b), (60, a + c), (60, a - c), (60, a + d), (60, a - d),
   (60, b + c), (60, b - c), (60, b + d), (60, b - d), (60, c + d), (60, c - d),
   (1, 2 * a + b + c), (1, 2 * a + b - c), (1, 2 * a - b + c), (1, 2 * a - b - c),
   (1, 2 * a + b + d), (1, 2 * a + b - d), (1, 2 * a - b + d), (1, 2 * a - b - d),
   (1, 2 * a + c + d), (1, 2 * a + c - d), (1, 2 * a - c + d), (1, 2 * a - c - d),
   (1, 2 * b + a + c), (1, 2 * b + a - c), (1, 2 * b - a + c), (1, 2 * b - a - c),
   (1, 2 * b + a + d), (1, 2 * b + a - d), (1, 2 * b - a + d), (1, 2 * b - a - d),
   (1, 2 * b + c + d), (1, 2 * b + c - d), (1, 2 * b - c + d), (1, 2 * b - c - d),
   (1, 2 * c + a + b), (1, 2 * c + a - b), (1, 2 * c - a + b), (1, 2 * c - a - b),
   (1, 2 * c + a + d), (1, 2 * c + a - d), (1, 2 * c - a + d), (1, 2 * c - a - d),
   (1, 2 * c + b + d), (1, 2 * c + b - d), (1, 2 * c - b + d), (1, 2 * c - b - d),
   (1, 2 * d + a + b), (1, 2 * d + a - b), (1, 2 * d - a + b), (1, 2 * d - a - b),
   (1, 2 * d + a + c), (1, 2 * d + a - c), (1, 2 * d - a + c), (1, 2 * d - a - c),
   (1, 2 * d + b + c), (1, 2 * d + b - c), (1, 2 * d - b + c), (1, 2 * d - b - c),
   (6, a + b + c + d), (6, a + b + c - d), (6, a + b - c + d), (6, a + b - c - d),
   (6, a - b + c + d), (6, a - b + c - d), (6, a - b - c + d), (6, a - b - c - d)]

/-- **Identity (21.4.2)** (Hardy–Wright):
`5040(a² + b² + c² + d²)⁴ = 6 ∑ (2a)⁸ + 60 ∑ (a ± b)⁸ + ∑ (2a ± b ± c)⁸ + 6 ∑ (a ± b ± c ± d)⁸`,
`840` eighth powers. -/
@[kb "hardywright2008" "Section 21.4, p. 444"]
theorem five_thousand_forty_mul_sum_sq_pow_four (a b c d : ℤ) :
    5040 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 4 =
      ((eighthPowerTerms a b c d).map fun p => (p.1 : ℤ) * p.2 ^ 8).sum := by
  simp only [eighthPowerTerms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast; ring

lemma card_eighthPowerTerms (a b c d : ℤ) : ((eighthPowerTerms a b c d).map Prod.fst).sum = 840 := by
  simp [eighthPowerTerms]

/-- `60 X³` is the sum of `184` sixth powers, by Theorem 369 and (21.4.1). -/
lemma isSumOfPowers_six_sixty_mul_cube (X : ℕ) : IsSumOfPowers 6 184 (60 * X ^ 3) := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares X
  have := isSumOfPowers_of_list (k := 6) (by decide) (sixthPowerTerms a b c d)
  rw [card_sixthPowerTerms, ← sixty_mul_sum_sq_cube] at this
  convert this using 1
  rw [← h]; zify; push_cast
  rw [Int.toNat_of_nonneg (by positivity)]

/-- `5040 X⁴` is the sum of `840` eighth powers, by Theorem 369 and (21.4.2). -/
lemma isSumOfPowers_eight_mul_pow_four (X : ℕ) : IsSumOfPowers 8 840 (5040 * X ^ 4) := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares X
  have := isSumOfPowers_of_list (k := 8) (by decide) (eighthPowerTerms a b c d)
  rw [card_eighthPowerTerms, ← five_thousand_forty_mul_sum_sq_pow_four] at this
  convert this using 1
  rw [← h]; zify; push_cast
  rw [Int.toNat_of_nonneg (by positivity)]

/-- **Theorem 391** (Hardy–Wright). If every number is the sum of `s` cubes, then every number is
the sum of `184 s + 59` sixth powers: `g(6) ≤ 184 g(3) + 59`. -/
@[kb "hardywright2008" "Thm 391, p. 444"]
theorem isSumOfPowers_six_of_three {s : ℕ} (hs : ∀ n, IsSumOfPowers 3 s n) (n : ℕ) :
    IsSumOfPowers 6 (184 * s + 59) n := by
  obtain ⟨X, hX⟩ := hs (n / 60)
  have h1 : IsSumOfPowers 6 (s * 184) (∑ i, 60 * X i ^ 3) :=
    isSumOfPowers_sum _ fun i => isSumOfPowers_six_sixty_mul_cube (X i)
  have h2 := h1.add (isSumOfPowers_self 6 (n % 60))
  rw [← Finset.mul_sum, hX] at h2
  rw [show 60 * (n / 60) + n % 60 = n by omega] at h2
  exact h2.mono (by norm_num) (by omega)

/-- **Theorem 391** (Hardy–Wright). `g(6) ≤ 184 g(3) + 59 ≤ 2451`. -/
@[kb "hardywright2008" "Thm 391, p. 444"]
theorem waringNumber_six_le : waringNumber 6 ≤ 184 * waringNumber 3 + 59 ∧
    184 * waringNumber 3 + 59 ≤ 2451 := by
  have hex : ∃ s, ∀ n, IsSumOfPowers 3 s n := ⟨13, isSumOfPowers_three_thirteen⟩
  refine ⟨Nat.sInf_le (isSumOfPowers_six_of_three (Nat.sInf_mem (s := {s | ∀ n,
    IsSumOfPowers 3 s n}) hex)), ?_⟩
  calc 184 * waringNumber 3 + 59 ≤ 184 * 13 + 59 := by gcongr; exact waringNumber_three_le
    _ = 2451 := by norm_num

/-- **Theorem 392** (Hardy–Wright). If every number is the sum of `s` biquadrates, then every number
is the sum of `840 s + 273` eighth powers: `g(8) ≤ 840 g(4) + 273`. -/
@[kb "hardywright2008" "Thm 392, p. 444"]
theorem isSumOfPowers_eight_of_four {s : ℕ} (hs : ∀ n, IsSumOfPowers 4 s n) (n : ℕ) :
    IsSumOfPowers 8 (840 * s + 273) n := by
  obtain ⟨X, hX⟩ := hs (n / 5040)
  have h1 : IsSumOfPowers 8 (s * 840) (∑ i, 5040 * X i ^ 4) :=
    isSumOfPowers_sum _ fun i => isSumOfPowers_eight_mul_pow_four (X i)
  -- `r < 5040` is the sum of `r / 256 + r % 256 ≤ 273` eighth powers of `1` and `2`
  set r := n % 5040 with hr
  have h2 := (isSumOfPowers_mul_pow 8 (r / 256) 2).add (isSumOfPowers_self 8 (r % 256))
  have h3 := h1.add h2
  rw [← Finset.mul_sum, hX] at h3
  rw [show 5040 * (n / 5040) + (r / 256 * 2 ^ 8 + r % 256) = n by omega] at h3
  exact h3.mono (by norm_num) (by omega)

/-- **Theorem 392** (Hardy–Wright). `g(8) ≤ 840 g(4) + 273 ≤ 42273`. -/
@[kb "hardywright2008" "Thm 392, p. 444"]
theorem waringNumber_eight_le : waringNumber 8 ≤ 840 * waringNumber 4 + 273 ∧
    840 * waringNumber 4 + 273 ≤ 42273 := by
  have hex : ∃ s, ∀ n, IsSumOfPowers 4 s n := ⟨50, isSumOfPowers_four_fifty⟩
  refine ⟨Nat.sInf_le (isSumOfPowers_eight_of_four (Nat.sInf_mem (s := {s | ∀ n,
    IsSumOfPowers 4 s n}) hex)), ?_⟩
  calc 840 * waringNumber 4 + 273 ≤ 840 * 50 + 273 := by gcongr; exact waringNumber_four_le
    _ = 42273 := by norm_num

end NTKB.HardyWright
