/-
Ireland–Rosen, Chapter 15, §§15.1–15.2: p-integral rationals, congruences between them, the power
sums S_m(n), Lemmas 1 and 2 of §15.2, Proposition 15.2.1, the sign and growth of B_{2m}
(Proposition 15.1.1, size estimate (7)), the corollary to von Staudt–Clausen, and Kummer's
regular and irregular primes.
-/
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.ZetaValues
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Analysis.SpecialFunctions.Stirling
import NTKB.Attr
import NTKB.IrelandRosen.R4.Bernoulli.Defs

/-!
# Bernoulli numbers modulo primes (Ireland–Rosen, §§15.1–15.2)

Ireland and Rosen work with *p-integral* rationals (denominator prime to `p`) and congruences
`x ≡ y (mod p^e)` between them, meaning that `(x - y)/p^e` is `p`-integral. We define both
(`IsPIntegral`, `PModEq`) and the power sum `S_m(n) = 1^m + 2^m + ⋯ + (n-1)^m` (`powerSum`).
Bernoulli numbers are Mathlib's `bernoulli` (`B_1 = -1/2`); the book's results concern `B_m` for
even `m`, where both conventions agree.

* §15.2, Lemma 1 (`isPIntegral_pow_div_succ`, `pModEq_pow_div_succ`, `isPIntegral_pow_sub_two_div_succ`).
* Proposition 15.2.1 (`isPIntegral_mul_bernoulli`, `pModEq_mul_bernoulli_powerSum`).
* §15.2, Lemma 2 (`powerSum_prime_modEq`).
* Proposition 15.1.1 (b), (c) and the size estimates (7), (8) (`neg_one_pow_mul_bernoulli_pos`,
  `abs_bernoulli_gt`, `abs_bernoulli_gt_pow`, `tendsto_abs_bernoulli_div`).
* Corollary to Theorem 3 of §15.1 (`isPIntegral_bernoulli`, `pModEq_mul_bernoulli_neg_one`,
  `six_dvd_den_bernoulli`).
* Kummer's regular and irregular primes, the index of irregularity (`IsIrregularPrime`,
  `IsRegularPrimeBernoulli`, `irregularityIndex`).

Credit: the private helpers `pow_div_isPIntegral`, `factorization_succ_le_sub_one'` and
`sum_pow_add_indicator_eq_zero'` adapt private lemmas of Mathlib's `Mathlib/NumberTheory/Bernoulli.lean`
(the proof of von Staudt–Clausen), which cannot be called from outside that file.
-/

namespace NTKB.IrelandRosen

open Finset


private lemma pow_div_isPIntegral {p M N : ℕ} [Fact p.Prime] (hM : M ≠ 0)
    (hv : M.factorization p ≤ N) : IsPIntegral p ((p : ℚ) ^ N / M) := by
  set e := M.factorization p
  set M' := M / p ^ e
  have hM'_cop : M'.Coprime p := (Nat.coprime_ordCompl Fact.out hM).symm
  have hp_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)
  have hdecomp : p ^ e * M' = M := Nat.ordProj_mul_ordCompl_eq_self M p
  have hM_eq : (M : ℚ) = ↑(p ^ e) * ↑M' := by rw [← hdecomp]; simp
  have hrw : (p : ℚ) ^ N / M = (p : ℚ) ^ (N - e) / M' := by
    rw [hM_eq, Nat.cast_pow, div_mul_eq_div_div]
    congr 1
    rw [div_eq_iff (pow_ne_zero e hp_ne), ← pow_add, Nat.sub_add_cancel hv]
  have hM'_eq : ((p : ℚ) ^ (N - e) / (M' : ℚ)) = Rat.divInt (p ^ (N - e) : ℤ) (M' : ℤ) := by
    norm_cast
    simp
  rw [hrw]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).1
    (hM'_cop.coprime_dvd_left (by
      rw [hM'_eq]; exact Int.natCast_dvd_natCast.mp (Rat.den_dvd _ _))).symm

private lemma factorization_succ_le_sub_one' {p d : ℕ} [Fact p.Prime] (hd : d ≥ 2) :
    (d + 1).factorization p ≤ d - 1 := by
  by_cases hcase : p = 2 ∧ d = 2
  · obtain ⟨rfl, rfl⟩ := hcase
    simp [Nat.factorization_eq_zero_of_not_dvd (by decide : ¬(2 ∣ 3))]
  · apply Nat.factorization_le_of_le_pow
    have hp2 := (Fact.out : p.Prime).two_le
    suffices ∀ n : ℕ, n ≥ 2 → ¬(p = 2 ∧ n = 2) → n + 1 ≤ p ^ (n - 1) from this d hd hcase
    intro n hn hne'
    induction hn with
    | refl => simp at hne' ⊢; lia
    | @step m hm IH =>
      by_cases hm2 : p = 2 ∧ m = 2
      · obtain ⟨rfl, rfl⟩ := hm2; simp
      · calc m + 1 + 1 ≤ p ^ (m - 1) + 1 := by linarith [IH hm2]
          _ ≤ p ^ (m - 1) * p := by nlinarith [Nat.one_le_pow (m - 1) p (by lia)]
          _ = p ^ m := by rw [show m = m - 1 + 1 by lia]; exact pow_succ ..

/-! ### §15.2, Lemma 1 -/

/-- **Ireland–Rosen, §15.2, Lemma 1 (first part).** `p^k/(k+1)` is `p`-integral. -/
@[kb "irelandrosen1990" "§15.2, Lemma 1"]
theorem isPIntegral_pow_div_succ (p : ℕ) [Fact p.Prime] (k : ℕ) :
    IsPIntegral p ((p : ℚ) ^ k / (k + 1)) := by
  have h := pow_div_isPIntegral (p := p) (M := k + 1) (N := k) (by lia) (by
    apply Nat.factorization_le_of_le_pow
    have := (Fact.out : p.Prime).two_le
    calc k + 1 ≤ 2 ^ k := Nat.succ_le_of_lt (Nat.lt_two_pow_self)
      _ ≤ p ^ k := Nat.pow_le_pow_left this k)
  simpa using h

/-- **Ireland–Rosen, §15.2, Lemma 1 (second part).** For `k ≥ 2`, `p^k/(k+1) ≡ 0 (mod p)`. -/
@[kb "irelandrosen1990" "§15.2, Lemma 1"]
theorem pModEq_pow_div_succ (p : ℕ) [Fact p.Prime] {k : ℕ} (hk : 2 ≤ k) :
    PModEq p 1 ((p : ℚ) ^ k / (k + 1)) 0 := by
  have h := pow_div_isPIntegral (p := p) (M := k + 1) (N := k - 1) (by lia)
    (factorization_succ_le_sub_one' hk)
  unfold PModEq
  have hp : (p : ℚ) ≠ 0 := mod_cast (Fact.out : p.Prime).ne_zero
  convert h using 1
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by lia⟩
  simp only [Nat.add_sub_cancel, sub_zero, pow_one, Nat.cast_add, Nat.cast_one]
  rw [pow_succ]
  field_simp

/-- **Ireland–Rosen, §15.2, Lemma 1 (third part).** For `p ≥ 5` and `k ≥ 3`, `p^(k-2)/(k+1)` is
`p`-integral. -/
@[kb "irelandrosen1990" "§15.2, Lemma 1"]
theorem isPIntegral_pow_sub_two_div_succ (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) {k : ℕ} (hk : 3 ≤ k) :
    IsPIntegral p ((p : ℚ) ^ (k - 2) / (k + 1)) := by
  have key : ∀ n : ℕ, 1 ≤ n → n + 3 ≤ 5 ^ n := by
    intro n hn
    induction hn with
    | refl => simp
    | @step m hm IH => rw [pow_succ]; lia
  have h := pow_div_isPIntegral (p := p) (M := k + 1) (N := k - 2) (by lia) (by
    apply Nat.factorization_le_of_le_pow
    calc k + 1 = (k - 2) + 3 := by lia
      _ ≤ 5 ^ (k - 2) := key _ (by lia)
      _ ≤ p ^ (k - 2) := Nat.pow_le_pow_left hp _)
  simpa using h

/-! ### §15.2, Lemma 2 -/

private lemma sum_pow_add_indicator_eq_zero' {p : ℕ} (l : ℕ) [Fact p.Prime] :
    (∑ v ∈ Ico 1 p, (v : ZMod p) ^ l) + (if (p - 1) ∣ l then (1 : ZMod p) else 0) = 0 := by
  have hbij : (∑ v ∈ Ico 1 p, (v : ZMod p) ^ l) = ∑ u : (ZMod p)ˣ, (u : ZMod p) ^ l :=
    Finset.sum_bij'
      (fun v hv ↦ Units.mk0 (v : ZMod p) (mt (ZMod.natCast_eq_zero_iff v p).mp (by
        grind [Nat.not_dvd_of_pos_of_lt])))
      (fun u _ ↦ (u : ZMod p).val)
      (fun _ _ ↦ Finset.mem_univ _)
      (fun u _ ↦ by grind [u.ne_zero, ZMod.val_ne_zero, ZMod.val_lt])
      (fun v hv ↦ by simp [ZMod.val_cast_of_lt (Finset.mem_Ico.mp hv).2])
      (fun u _ ↦ Units.ext (ZMod.natCast_zmod_val _))
      (fun _ _ ↦ rfl)
  rw [hbij, FiniteField.sum_pow_units, ZMod.card]
  grind

/-- **Ireland–Rosen, §15.2, Lemma 2.** `S_m(p) ≡ 0 (mod p)` if `p - 1 ∤ m` and `S_m(p) ≡ -1 (mod p)`
if `p - 1 ∣ m`. -/
@[kb "irelandrosen1990" "§15.2, Lemma 2"]
theorem powerSum_prime_modEq (p : ℕ) [Fact p.Prime] (m : ℕ) :
    (powerSum m p : ℤ) ≡ (if p - 1 ∣ m then -1 else 0) [ZMOD p] := by
  have h := sum_pow_add_indicator_eq_zero' (p := p) m
  rw [← ZMod.intCast_eq_intCast_iff]
  unfold powerSum
  push_cast
  split_ifs at h ⊢
  · linear_combination h
  · linear_combination h

/-! ### Proposition 15.2.1 -/

private lemma one_div_prime_isPIntegral {p q : ℕ} [Fact p.Prime] (hq : q.Prime) (hne : q ≠ p) :
    IsPIntegral p ((1 : ℚ) / q) := by
  unfold IsPIntegral
  rw [show ((1 : ℚ) / q).den = q by simp [hq.ne_zero]]
  rw [Nat.prime_dvd_prime_iff_eq Fact.out hq]
  exact fun h => hne h.symm

/-- The key consequence of von Staudt–Clausen: `B_{2k} + [p-1 ∣ 2k]/p` is `p`-integral. -/
private lemma bernoulli_add_indicator_isPIntegral (p : ℕ) [Fact p.Prime] {k : ℕ} (hk : 0 < k) :
    IsPIntegral p (bernoulli (2 * k) + if p - 1 ∣ 2 * k then 1 / (p : ℚ) else 0) := by
  obtain ⟨n, hn⟩ := Bernoulli.vonStaudt_clausen k
  set S := (range (2 * k + 2)).filter (fun q => q.Prime ∧ (q - 1) ∣ 2 * k) with hS
  have hmem : ∀ q ∈ S.erase p, IsPIntegral p ((1 : ℚ) / q) := by
    intro q hq
    rw [Finset.mem_erase, hS, Finset.mem_filter] at hq
    exact one_div_prime_isPIntegral hq.2.2.1 hq.1
  have hsum : IsPIntegral p (∑ q ∈ S.erase p, (1 : ℚ) / q) := by
    rw [isPIntegral_iff_mem]
    exact sum_mem fun q hq => (isPIntegral_iff_mem (p := p)).1 (hmem q hq)
  have hint : IsPIntegral p ((n : ℚ)) := by
    rw [isPIntegral_iff_mem]; exact intCast_mem _ n
  have key : (bernoulli (2 * k) + if p - 1 ∣ 2 * k then 1 / (p : ℚ) else 0) =
      n - ∑ q ∈ S.erase p, (1 : ℚ) / q := by
    by_cases hd : p - 1 ∣ 2 * k
    · have hp_mem : p ∈ S := by
        rw [hS, Finset.mem_filter, Finset.mem_range]
        refine ⟨?_, Fact.out, hd⟩
        have := Nat.le_of_dvd (by lia) hd
        lia
      rw [← Finset.add_sum_erase _ _ hp_mem] at hn
      simp only [hd, ↓reduceIte]
      linarith
    · have : p ∉ S := fun h => hd (Finset.mem_filter.mp h).2.2
      rw [Finset.erase_eq_of_notMem this] at ⊢
      simp only [hd, ↓reduceIte]
      linarith
  rw [key, isPIntegral_iff_mem]
  exact sub_mem ((isPIntegral_iff_mem (p := p)).1 hint) ((isPIntegral_iff_mem (p := p)).1 hsum)

private lemma mul_bernoulli_aux (p : ℕ) [Fact p.Prime] {k : ℕ} (hk : 0 < k) :
    IsPIntegral p (p * bernoulli (2 * k)) := by
  have h := (isPIntegral_iff_mem (p := p)).1 (bernoulli_add_indicator_isPIntegral p hk)
  have hp : (p : ℚ) ≠ 0 := mod_cast (Fact.out : p.Prime).ne_zero
  have e : (p : ℚ) * bernoulli (2 * k) =
      p * (bernoulli (2 * k) + if p - 1 ∣ 2 * k then 1 / (p : ℚ) else 0) -
        (if p - 1 ∣ 2 * k then 1 else 0) := by
    split_ifs <;> field_simp <;> ring
  rw [isPIntegral_iff_mem, e]
  refine sub_mem (mul_mem (natCast_mem _ p) h) ?_
  split_ifs
  · exact one_mem _
  · exact zero_mem _

/-- **Ireland–Rosen, Proposition 15.2.1 (first part).** For even `m ≥ 2`, `p B_m` is
`p`-integral. -/
@[kb "irelandrosen1990" "Proposition 15.2.1"]
theorem isPIntegral_mul_bernoulli (p : ℕ) [Fact p.Prime] {m : ℕ} (hm : Even m) (hm0 : m ≠ 0) :
    IsPIntegral p (p * bernoulli m) := by
  obtain ⟨k, rfl⟩ := hm
  rw [← two_mul]
  exact mul_bernoulli_aux p (by lia)

/-- **Ireland–Rosen, Proposition 15.2.1 (second part).** For even `m ≥ 2`,
`p B_m ≡ S_m(p) (mod p)`. -/
@[kb "irelandrosen1990" "Proposition 15.2.1"]
theorem pModEq_mul_bernoulli_powerSum (p : ℕ) [Fact p.Prime] {m : ℕ} (hm : Even m) (hm0 : m ≠ 0) :
    PModEq p 1 (p * bernoulli m) (powerSum m p) := by
  obtain ⟨k, rfl⟩ := hm
  rw [← two_mul]
  have hk : 0 < k := by lia
  have hX := (isPIntegral_iff_mem (p := p)).1 (bernoulli_add_indicator_isPIntegral p hk)
  have h2 := powerSum_prime_modEq p (2 * k)
  obtain ⟨T, hT⟩ := Int.modEq_iff_dvd.mp h2
  have hp : (p : ℚ) ≠ 0 := mod_cast (Fact.out : p.Prime).ne_zero
  have hT' : ((if p - 1 ∣ 2 * k then (-1 : ℤ) else 0 : ℤ) : ℚ) - (powerSum (2 * k) p : ℚ) =
      p * T := by
    have := congrArg (fun z : ℤ => (z : ℚ)) hT
    simpa using this
  unfold PModEq
  rw [isPIntegral_iff_mem]
  have e : ((p : ℚ) * bernoulli (2 * k) - (powerSum (2 * k) p : ℚ)) / (p : ℚ) ^ 1 =
      (bernoulli (2 * k) + if p - 1 ∣ 2 * k then 1 / (p : ℚ) else 0) + T := by
    split_ifs at hT' ⊢
    · push_cast at hT'
      field_simp
      linarith
    · push_cast at hT'
      field_simp
      linarith
  rw [e]
  exact add_mem hX (intCast_mem _ T)

/-! ### Corollary to Theorem 3 of §15.1 (von Staudt–Clausen) -/

/-- **Ireland–Rosen, §15.1, Corollary to Theorem 3 (first part).** If `p - 1 ∤ 2m` then `B_{2m}`
is `p`-integral. -/
@[kb "irelandrosen1990" "§15.1, Corollary to Theorem 3"]
theorem isPIntegral_bernoulli (p : ℕ) [Fact p.Prime] {m : ℕ} (hpm : ¬ p - 1 ∣ 2 * m) :
    IsPIntegral p (bernoulli (2 * m)) := by
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp at hpm
    · exact h
  have := bernoulli_add_indicator_isPIntegral p hm
  simpa [hpm] using this

/-- **Ireland–Rosen, §15.1, Corollary to Theorem 3 (second part).** If `m ≥ 1` and `p - 1 ∣ 2m`
then `p B_{2m} ≡ -1 (mod p)`. -/
@[kb "irelandrosen1990" "§15.1, Corollary to Theorem 3"]
theorem pModEq_mul_bernoulli_neg_one (p : ℕ) [Fact p.Prime] {m : ℕ} (hm : 0 < m)
    (hpm : p - 1 ∣ 2 * m) : PModEq p 1 (p * bernoulli (2 * m)) (-1) := by
  have h := bernoulli_add_indicator_isPIntegral p hm
  simp only [hpm, ↓reduceIte] at h
  have hp : (p : ℚ) ≠ 0 := mod_cast (Fact.out : p.Prime).ne_zero
  unfold PModEq
  convert h using 1
  field_simp
  ring

/-- **Ireland–Rosen, §15.1, Corollary to Theorem 3 (third part).** For `m ≥ 1`, `6` divides the
denominator of `B_{2m}`. -/
@[kb "irelandrosen1990" "§15.1, Corollary to Theorem 3"]
theorem six_dvd_den_bernoulli {m : ℕ} (hm : 0 < m) : 6 ∣ (bernoulli (2 * m)).den := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 : 2 ∣ (bernoulli (2 * m)).den := Bernoulli.dvd_den_bernoulli hm (by simp)
  have h3 : 3 ∣ (bernoulli (2 * m)).den := Bernoulli.dvd_den_bernoulli hm (by simp)
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 3) h2 h3

/-! ### Proposition 15.1.1 and the size estimate (7) -/

private lemma zeta_aux {m : ℕ} (hm : 0 < m) :
    1 < (2 : ℝ) ^ (2 * m - 1) * Real.pi ^ (2 * m) / ((2 * m).factorial : ℝ) *
      ((-1 : ℝ) ^ (m + 1) * (bernoulli (2 * m) : ℝ)) := by
  have hs := hasSum_zeta_nat (k := m) (by lia)
  have h := sum_le_hasSum ({1, 2} : Finset ℕ) (fun i _ => by positivity) hs
  have h2 : (0 : ℝ) < 1 / 2 ^ (2 * m) := by positivity
  rw [Finset.sum_pair (by norm_num)] at h
  have e : (-1 : ℝ) ^ (m + 1) * (2 : ℝ) ^ (2 * m - 1) * Real.pi ^ (2 * m) *
        (bernoulli (2 * m) : ℝ) / ((2 * m).factorial : ℝ) =
      (2 : ℝ) ^ (2 * m - 1) * Real.pi ^ (2 * m) / ((2 * m).factorial : ℝ) *
      ((-1 : ℝ) ^ (m + 1) * (bernoulli (2 * m) : ℝ)) := by ring
  rw [e] at h
  have : (1 : ℝ) / ((1 : ℕ) : ℝ) ^ (2 * m) = 1 := by simp
  have h' : (1 : ℝ) / ((2 : ℕ) : ℝ) ^ (2 * m) = 1 / 2 ^ (2 * m) := by simp
  rw [this, h'] at h
  linarith

/-- **Ireland–Rosen, Proposition 15.1.1 (b).** `(-1)^(m+1) B_{2m} > 0` for `m ≥ 1`. -/
@[kb "irelandrosen1990" "Proposition 15.1.1 (b)"]
theorem neg_one_pow_mul_bernoulli_pos {m : ℕ} (hm : 0 < m) :
    0 < (-1 : ℚ) ^ (m + 1) * bernoulli (2 * m) := by
  have h := zeta_aux hm
  have hc : (0 : ℝ) < (2 : ℝ) ^ (2 * m - 1) * Real.pi ^ (2 * m) / ((2 * m).factorial : ℝ) := by
    positivity
  have : (0 : ℝ) < (-1 : ℝ) ^ (m + 1) * (bernoulli (2 * m) : ℝ) := by
    by_contra hneg
    rw [not_lt] at hneg
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hc.le hneg]
  exact_mod_cast this

/-- **Ireland–Rosen, §15.1, size estimate (7).** `|B_{2m}| > 2 (2m)!/(2π)^(2m)` for `m ≥ 1`. -/
@[kb "irelandrosen1990" "§15.1, (7)"]
theorem abs_bernoulli_gt {m : ℕ} (hm : 0 < m) :
    2 * ((2 * m).factorial : ℝ) / (2 * Real.pi) ^ (2 * m) < |(bernoulli (2 * m) : ℝ)| := by
  have h := zeta_aux hm
  have hpos : (0 : ℝ) < (-1 : ℝ) ^ (m + 1) * (bernoulli (2 * m) : ℝ) := by
    exact_mod_cast neg_one_pow_mul_bernoulli_pos hm
  have habs : |(bernoulli (2 * m) : ℝ)| = (-1 : ℝ) ^ (m + 1) * (bernoulli (2 * m) : ℝ) := by
    rw [← abs_of_pos hpos, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [habs]
  set y := (-1 : ℝ) ^ (m + 1) * (bernoulli (2 * m) : ℝ)
  have hf : (0 : ℝ) < ((2 * m).factorial : ℝ) := by positivity
  rw [div_mul_eq_mul_div, lt_div_iff₀ hf, one_mul] at h
  have e2 : (2 : ℝ) ^ (2 * m) = 2 * 2 ^ (2 * m - 1) := by
    rw [← pow_succ']; congr 1; lia
  have e : y * (2 * Real.pi) ^ (2 * m) = 2 * ((2 : ℝ) ^ (2 * m - 1) * Real.pi ^ (2 * m) * y) := by
    rw [mul_pow, e2]; ring
  rw [div_lt_iff₀ (by positivity), e]
  linarith

/-- **Ireland–Rosen, §15.1, size estimate (8).** `|B_{2m}| > 2 (m/(π e))^(2m)` for `m ≥ 1`
(from (7) and Stirling's lower bound `n! ≥ √(2πn) (n/e)^n`, Mathlib's
`Stirling.le_factorial_stirling`). -/
@[kb "irelandrosen1990" "§15.1, (8)"]
theorem abs_bernoulli_gt_pow {m : ℕ} (hm : 0 < m) :
    2 * ((m : ℝ) / (Real.pi * Real.exp 1)) ^ (2 * m) < |(bernoulli (2 * m) : ℝ)| := by
  refine lt_of_le_of_lt ?_ (abs_bernoulli_gt hm)
  have hS := Stirling.le_factorial_stirling (2 * m)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h1 : (1 : ℝ) ≤ √(2 * Real.pi * ((2 * m : ℕ) : ℝ)) := by
    rw [Real.one_le_sqrt]
    push_cast
    nlinarith [Real.two_le_pi]
  have hpos : 0 ≤ (((2 * m : ℕ) : ℝ) / Real.exp 1) ^ (2 * m) := by positivity
  have hfac : (((2 * m : ℕ) : ℝ) / Real.exp 1) ^ (2 * m) ≤ ((2 * m).factorial : ℝ) :=
    le_trans (le_mul_of_one_le_left hpos h1) hS
  have heq : 2 * ((m : ℝ) / (Real.pi * Real.exp 1)) ^ (2 * m) =
      2 * (((2 * m : ℕ) : ℝ) / Real.exp 1) ^ (2 * m) / (2 * Real.pi) ^ (2 * m) := by
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have he : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
    rw [div_pow, div_pow, mul_pow, mul_pow]
    push_cast
    rw [mul_pow]
    field_simp
  rw [heq]
  gcongr

private lemma tendsto_factorial_div (x : ℝ) (hx : 0 < x) :
    Filter.Tendsto (fun n : ℕ ↦ (n.factorial : ℝ) / x ^ n) Filter.atTop Filter.atTop := by
  have h := FloorSemiring.tendsto_pow_div_factorial_atTop x
  have h2 : Filter.Tendsto (fun n : ℕ ↦ x ^ n / (n.factorial : ℝ)) Filter.atTop
      (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.2 ⟨h, Filter.Eventually.of_forall fun n => by
      simp only [Set.mem_Ioi]; positivity⟩
  have := h2.inv_tendsto_nhdsGT_zero
  refine this.congr fun n => ?_
  simp

/-- **Ireland–Rosen, Proposition 15.1.1 (c).** `|B_{2m}/(2m)| → ∞` as `m → ∞`. -/
@[kb "irelandrosen1990" "Proposition 15.1.1 (c)"]
theorem tendsto_abs_bernoulli_div :
    Filter.Tendsto (fun m : ℕ ↦ |(bernoulli (2 * m) : ℝ) / (2 * m)|) Filter.atTop Filter.atTop := by
  have h1 := (tendsto_factorial_div (4 * Real.pi) (by positivity)).comp
    (Filter.tendsto_atTop_mono (fun m : ℕ => (by lia : m ≤ 2 * m)) Filter.tendsto_id)
  refine Filter.tendsto_atTop_mono' _ ?_ h1
  filter_upwards [Filter.eventually_gt_atTop 0] with m hm
  have h := abs_bernoulli_gt hm
  have hm' : (0 : ℝ) < 2 * m := by positivity
  rw [abs_div, abs_of_pos hm']
  rw [le_div_iff₀ hm']
  simp only [Function.comp]
  have hlt : ((2 * m : ℕ) : ℝ) < 2 ^ (2 * m) := by exact_mod_cast Nat.lt_two_pow_self
  have hf : (0 : ℝ) < ((2 * m).factorial : ℝ) := by positivity
  have hp : (0 : ℝ) < (2 * Real.pi) ^ (2 * m) := by positivity
  have e : (4 * Real.pi) ^ (2 * m) = (2 * Real.pi) ^ (2 * m) * 2 ^ (2 * m) := by
    rw [← mul_pow]; ring_nf
  rw [e]
  have h3 : ((2 * m).factorial : ℝ) / ((2 * Real.pi) ^ (2 * m) * 2 ^ (2 * m)) * (2 * m) ≤
      ((2 * m).factorial : ℝ) / (2 * Real.pi) ^ (2 * m) := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hp]
    have := mul_le_mul_of_nonneg_left hlt.le (le_of_lt (mul_pos hf hp))
    push_cast at this
    linarith
  have h4 : 0 < ((2 * m).factorial : ℝ) / (2 * Real.pi) ^ (2 * m) := by positivity
  rw [mul_div_assoc] at h
  linarith

/-! ### Regular and irregular primes (Kummer's definition, §15.1) -/

/-- **Ireland–Rosen, §15.1 (Kummer's definition).** An odd prime `p` is *irregular* if `p` divides
the numerator of one of `B_2, B_4, …, B_{p-3}`. -/
def IsIrregularPrime (p : ℕ) : Prop :=
  p.Prime ∧ p ≠ 2 ∧ ∃ k : ℕ, 1 ≤ k ∧ 2 * k ≤ p - 3 ∧ (p : ℤ) ∣ (bernoulli (2 * k)).num

/-- **Ireland–Rosen, §15.1 (Kummer's definition).** An odd prime `p` is *regular* if `p` divides
none of the numerators of `B_2, B_4, …, B_{p-3}`. (Kummer's equivalent definition by the class
number of `ℚ(ζ_p)`, §15.3, is not formalized here.) -/
def IsRegularPrimeBernoulli (p : ℕ) : Prop := p.Prime ∧ p ≠ 2 ∧ ¬ IsIrregularPrime p

/-- **Ireland–Rosen, §15.1.** The index of irregularity of `p`: the number of `B_{2i}`,
`1 ≤ i ≤ (p-3)/2`, whose numerator is divisible by `p`. -/
def irregularityIndex (p : ℕ) : ℕ :=
  ((Icc 1 ((p - 3) / 2)).filter fun i ↦ (p : ℤ) ∣ (bernoulli (2 * i)).num).card

/-- A prime is irregular iff its index of irregularity is positive. -/
theorem isIrregularPrime_iff {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    IsIrregularPrime p ↔ 0 < irregularityIndex p := by
  unfold IsIrregularPrime irregularityIndex
  rw [Finset.card_pos, Finset.filter_nonempty_iff]
  constructor
  · rintro ⟨_, _, k, hk1, hk2, hd⟩
    exact ⟨k, Finset.mem_Icc.2 ⟨hk1, by lia⟩, hd⟩
  · rintro ⟨k, hk, hd⟩
    rw [Finset.mem_Icc] at hk
    exact ⟨hp, hp2, k, hk.1, by lia, hd⟩

end NTKB.IrelandRosen
