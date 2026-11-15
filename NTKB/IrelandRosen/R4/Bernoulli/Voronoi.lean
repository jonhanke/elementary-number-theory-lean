/-
Ireland–Rosen, Chapter 15, §15.2: Proposition 15.2.2 and its corollary, and the Voronoi
congruences (Proposition 15.2.3).
-/
import NTKB.IrelandRosen.R4.Bernoulli.Defs
import Mathlib.NumberTheory.Multiplicity
import NTKB.Attr

/-!
# Power sums modulo `n^2` and the Voronoi congruences (Ireland–Rosen, §15.2)

Write `B_m = U_m / V_m` in lowest terms (`U_m = (bernoulli m).num`, `V_m = (bernoulli m).den > 0`).

* Proposition 15.2.2: for even `m ≥ 2` and `n ≥ 1`, `V_m S_m(n) ≡ U_m n (mod n^2)`
  (`den_mul_powerSum_modEq`).
* Corollary: if `p - 1 ∤ m`, then `S_m(p) ≡ p B_m (mod p^2)` (`pModEq_powerSum_mul_bernoulli`).
* Proposition 15.2.3 (Voronoi): for even `m ≥ 2`, `n ≥ 1` and `a` prime to `n`,
  `(a^m - 1) U_m ≡ m a^(m-1) V_m ∑_{j=1}^{n-1} j^(m-1) [ja/n] (mod n)` (`voronoi_congruence`).

Credit: the private helpers with suffix `_V` repeat lemmas of `Basic.lean`, some of them adapted from
private lemmas of Mathlib's `Mathlib/NumberTheory/Bernoulli.lean`; this file does not
import `Basic.lean`.
-/

namespace NTKB.IrelandRosen

open Finset

private lemma pow_div_isPIntegral_V {p M N : ℕ} [Fact p.Prime] (hM : M ≠ 0)
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

private lemma factorization_succ_le_sub_one_V {p d : ℕ} [Fact p.Prime] (hd : d ≥ 2) :
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

private lemma factorization_le_sub_three_V {p j : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (hj : 3 ≤ j) :
    j.factorization p ≤ j - 3 := by
  rcases Nat.lt_or_ge j 4 with h | h
  · have hj3 : j = 3 := by omega
    subst hj3
    have hnd : ¬ p ∣ 3 := fun hd => by have := Nat.le_of_dvd (by norm_num) hd; omega
    simp [Nat.factorization_eq_zero_of_not_dvd hnd]
  · apply Nat.factorization_le_of_le_pow
    have key : ∀ n : ℕ, 1 ≤ n → n + 3 ≤ 5 ^ n := by
      intro n hn
      induction hn with
      | refl => simp
      | @step m hm IH => rw [pow_succ]; lia
    calc j = (j - 3) + 3 := by omega
      _ ≤ 5 ^ (j - 3) := key _ (by omega)
      _ ≤ p ^ (j - 3) := Nat.pow_le_pow_left hp _

private lemma one_div_prime_isPIntegral_V {p q : ℕ} [Fact p.Prime] (hq : q.Prime) (hne : q ≠ p) :
    IsPIntegral p ((1 : ℚ) / q) := by
  unfold IsPIntegral
  rw [show ((1 : ℚ) / q).den = q by simp [hq.ne_zero]]
  rw [Nat.prime_dvd_prime_iff_eq Fact.out hq]
  exact fun h => hne h.symm

private lemma bernoulli_add_indicator_isPIntegral_V (p : ℕ) [Fact p.Prime] {k : ℕ} (hk : 0 < k) :
    IsPIntegral p (bernoulli (2 * k) + if p - 1 ∣ 2 * k then 1 / (p : ℚ) else 0) := by
  obtain ⟨n, hn⟩ := Bernoulli.vonStaudt_clausen k
  set S := (range (2 * k + 2)).filter (fun q => q.Prime ∧ (q - 1) ∣ 2 * k) with hS
  have hmem : ∀ q ∈ S.erase p, IsPIntegral p ((1 : ℚ) / q) := by
    intro q hq
    rw [Finset.mem_erase, hS, Finset.mem_filter] at hq
    exact one_div_prime_isPIntegral_V hq.2.2.1 hq.1
  have hsum : IsPIntegral p (∑ q ∈ S.erase p, (1 : ℚ) / q) := isPIntegral_sum _ hmem
  have hint : IsPIntegral p ((n : ℚ)) := isPIntegral_intCast n
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
  rw [key]
  exact hint.sub hsum

private lemma mul_bernoulli_aux_V (p : ℕ) [Fact p.Prime] {k : ℕ} (hk : 0 < k) :
    IsPIntegral p (p * bernoulli (2 * k)) := by
  have h := bernoulli_add_indicator_isPIntegral_V p hk
  have hp : (p : ℚ) ≠ 0 := mod_cast (Fact.out : p.Prime).ne_zero
  have e : (p : ℚ) * bernoulli (2 * k) =
      p * (bernoulli (2 * k) + if p - 1 ∣ 2 * k then 1 / (p : ℚ) else 0) -
        (if p - 1 ∣ 2 * k then 1 else 0) := by
    split_ifs <;> field_simp <;> ring
  rw [e]
  refine ((isPIntegral_natCast p).mul h).sub ?_
  split_ifs
  · exact isPIntegral_one
  · exact isPIntegral_zero

private lemma isPIntegral_bernoulli_V (p : ℕ) [Fact p.Prime] {m : ℕ} (hpm : ¬ p - 1 ∣ 2 * m) :
    IsPIntegral p (bernoulli (2 * m)) := by
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp at hpm
    · exact h
  have := bernoulli_add_indicator_isPIntegral_V p hm
  simpa [hpm] using this

private lemma isPIntegral_mul_bernoulli_all (p : ℕ) [Fact p.Prime] (i : ℕ) :
    IsPIntegral p (p * bernoulli i) := by
  rcases Nat.even_or_odd i with ⟨k, hk⟩ | hodd
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · have : i = 0 := by omega
      subst this
      simpa using isPIntegral_natCast (p := p) p
    · have : i = 2 * k := by omega
      subst this
      exact mul_bernoulli_aux_V p hk0
  · by_cases h1 : i = 1
    · subst h1
      rw [bernoulli_one]
      by_cases h2 : p = 2
      · subst h2
        convert isPIntegral_intCast (p := 2) (-1) using 1
        norm_num
      · have h := one_div_prime_isPIntegral_V (p := p) Nat.prime_two (Ne.symm h2)
        have := (isPIntegral_natCast (p := p) p).mul h.neg
        convert this using 1
        push_cast; ring
    · have h3 : 1 < i := by
        obtain ⟨k, hk⟩ := hodd
        omega
      rw [bernoulli_eq_zero_of_odd hodd h3]
      simpa using isPIntegral_zero (p := p)

private lemma term_pint (p : ℕ) [Fact p.Prime] (V : ℕ) (hV : p = 2 ∨ p = 3 → p ∣ V)
    (i r : ℕ) (hr : 1 ≤ r) (n : ℕ) (hn : p ∣ n) :
    IsPIntegral p ((V : ℚ) * (bernoulli i * ((i + r + 2).choose i : ℚ) / ((i + r + 2 : ℕ) : ℚ) *
      (n : ℚ) ^ r)) := by
  have hp0 : (p : ℚ) ≠ 0 := mod_cast (Fact.out : p.Prime).ne_zero
  have hC : (((i + r + 2).choose i : ℕ) : ℚ) / ((i + r + 2 : ℕ) : ℚ) =
      (((i + r + 1).choose i : ℕ) : ℚ) / ((r + 2 : ℕ) : ℚ) := by
    have h : (i + r + 1).choose i * (i + r + 2) = (i + r + 2).choose i * (r + 2) := by
      have := Nat.choose_mul_succ_eq (i + r + 1) i
      rwa [show i + r + 1 + 1 - i = r + 2 by omega] at this
    have h3 : (((i + r + 1).choose i : ℕ) : ℚ) * ((i + r + 2 : ℕ) : ℚ) =
        (((i + r + 2).choose i : ℕ) : ℚ) * ((r + 2 : ℕ) : ℚ) := by exact_mod_cast h
    rw [div_eq_div_iff (by positivity) (by positivity)]
    linarith
  rw [mul_div_assoc, hC]
  obtain ⟨n', rfl⟩ := hn
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  by_cases h5 : 5 ≤ p
  · have hpow : IsPIntegral p ((p : ℚ) ^ s / ((s + 1 + 2 : ℕ) : ℚ)) :=
      pow_div_isPIntegral_V (M := s + 1 + 2) (N := s) (by omega) (by
        have := factorization_le_sub_three_V (p := p) h5 (j := s + 1 + 2) (by omega)
        omega)
    have e : (V : ℚ) * (bernoulli i * ((((i + (s + 1) + 1).choose i : ℕ) : ℚ) /
        ((s + 1 + 2 : ℕ) : ℚ)) * (((p * n' : ℕ) : ℚ)) ^ (s + 1)) =
        ((p : ℚ) * bernoulli i) * V * (((i + (s + 1) + 1).choose i : ℕ) : ℚ) * (n' : ℚ) ^ (s + 1) *
          ((p : ℚ) ^ s / ((s + 1 + 2 : ℕ) : ℚ)) := by
      push_cast
      field_simp
      ring
    rw [e]
    exact ((((isPIntegral_mul_bernoulli_all p i).mul (isPIntegral_natCast V)).mul
      (isPIntegral_natCast _)).mul ((isPIntegral_natCast n').pow _)).mul hpow
  · have hp23 : p = 2 ∨ p = 3 := by
      have h2 := (Fact.out : p.Prime).two_le
      have h4 : p ≠ 4 := by
        rintro rfl
        exact absurd (Fact.out : Nat.Prime 4) (by decide)
      omega
    obtain ⟨V', hV'⟩ := hV hp23
    have hpow : IsPIntegral p ((p : ℚ) ^ (s + 1) / ((s + 1 + 2 : ℕ) : ℚ)) :=
      pow_div_isPIntegral_V (M := s + 1 + 2) (N := s + 1) (by omega) (by
        have := factorization_succ_le_sub_one_V (p := p) (d := s + 2) (by omega)
        simpa using this)
    have e : (V : ℚ) * (bernoulli i * ((((i + (s + 1) + 1).choose i : ℕ) : ℚ) /
        ((s + 1 + 2 : ℕ) : ℚ)) * (((p * n' : ℕ) : ℚ)) ^ (s + 1)) =
        ((p : ℚ) * bernoulli i) * V' * (((i + (s + 1) + 1).choose i : ℕ) : ℚ) * (n' : ℚ) ^ (s + 1) *
          ((p : ℚ) ^ (s + 1) / ((s + 1 + 2 : ℕ) : ℚ)) := by
      rw [hV']
      push_cast
      field_simp
      ring
    rw [e]
    exact ((((isPIntegral_mul_bernoulli_all p i).mul (isPIntegral_natCast V')).mul
      (isPIntegral_natCast _)).mul ((isPIntegral_natCast n').pow _)).mul hpow

private lemma zterm_pint (p : ℕ) [Fact p.Prime] (V m : ℕ) (hm : Even m) (hm0 : m ≠ 0)
    (hV2 : 2 ∣ V) (hV3 : 3 ∣ V) (n : ℕ) (hn : p ∣ n) (i : ℕ) (hi : i < m) :
    IsPIntegral p ((V : ℚ) * (bernoulli i * ((m + 1).choose i : ℚ) / ((m + 1 : ℕ) : ℚ) *
      (n : ℚ) ^ (m - 1 - i))) := by
  by_cases him : i = m - 1
  · subst him
    obtain ⟨k, hk⟩ := hm
    by_cases hk1 : k = 1
    · have hm2 : m = 2 := by omega
      subst hm2
      obtain ⟨V2, rfl⟩ := hV2
      have := (isPIntegral_natCast (p := p) V2).neg
      convert this using 1
      norm_num [bernoulli_one, Nat.choose]
      ring
    · have hodd : Odd (m - 1) := ⟨k - 1, by omega⟩
      have h3 : 1 < m - 1 := by omega
      rw [bernoulli_eq_zero_of_odd hodd h3]
      simpa using isPIntegral_zero (p := p)
  · obtain ⟨r, hr1, hr2⟩ : ∃ r, 1 ≤ r ∧ m = i + r + 1 := ⟨m - 1 - i, by omega, by omega⟩
    have e1 : m - 1 - i = r := by omega
    have e2 : m + 1 = i + r + 2 := by omega
    rw [e1, e2]
    refine term_pint p V ?_ i r hr1 n hn
    rintro (rfl | rfl)
    · exact hV2
    · exact hV3

/-- **Ireland–Rosen, Proposition 15.2.2.** For even `m ≥ 2` and `n ≥ 1`,
`V_m S_m(n) ≡ U_m n (mod n^2)`. -/
@[kb "irelandrosen1990" "Proposition 15.2.2"]
theorem den_mul_powerSum_modEq {m : ℕ} (hm : Even m) (hm0 : m ≠ 0) (n : ℕ) :
    ((bernoulli m).den : ℤ) * powerSum m n ≡ (bernoulli m).num * n [ZMOD (n : ℤ) ^ 2] := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [powerSum]
  obtain ⟨k, hk⟩ := hm
  have hk0 : 0 < k := by omega
  have hm2 : m = 2 * k := by omega
  have hV2 : 2 ∣ (bernoulli m).den := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [hm2]
    exact Bernoulli.dvd_den_bernoulli hk0 (by simp)
  have hV3 : 3 ∣ (bernoulli m).den := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [hm2]
    exact Bernoulli.dvd_den_bernoulli hk0 (by simp)
  have hnum : ((bernoulli m).num : ℚ) = bernoulli m * (bernoulli m).den :=
    (Rat.mul_den_eq_num (bernoulli m)).symm
  have hS : (powerSum m n : ℚ) = ∑ k ∈ range n, (k : ℚ) ^ m := by
    unfold powerSum
    push_cast
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hn]
    simp [hm0]
  have hF := sum_range_pow n m
  rw [sum_range_succ] at hF
  have hlast : bernoulli m * ((m + 1).choose m : ℚ) * (n : ℚ) ^ (m + 1 - m) / (m + 1) =
      bernoulli m * n := by
    rw [Nat.choose_succ_self_right, show m + 1 - m = 1 by omega]
    push_cast
    field_simp
  rw [hlast] at hF
  set Z : ℚ := ∑ i ∈ range m, ((bernoulli m).den : ℚ) *
    (bernoulli i * ((m + 1).choose i : ℚ) / ((m + 1 : ℕ) : ℚ) * (n : ℚ) ^ (m - 1 - i)) with hZ
  have hid : ((bernoulli m).den : ℚ) * (powerSum m n : ℚ) - ((bernoulli m).num : ℚ) * n =
      (n : ℚ) ^ 2 * Z := by
    rw [hS, hF, hnum, hZ, mul_sum]
    have : ((bernoulli m).den : ℚ) * (∑ i ∈ range m, bernoulli i * ((m + 1).choose i : ℚ) *
        (n : ℚ) ^ (m + 1 - i) / ((m : ℚ) + 1) + bernoulli m * n) -
        bernoulli m * (bernoulli m).den * n =
        ((bernoulli m).den : ℚ) * ∑ i ∈ range m, bernoulli i * ((m + 1).choose i : ℚ) *
        (n : ℚ) ^ (m + 1 - i) / ((m : ℚ) + 1) := by ring
    rw [this, mul_sum]
    refine sum_congr rfl fun i hi => ?_
    have hi' := mem_range.mp hi
    have : (n : ℚ) ^ (m + 1 - i) = (n : ℚ) ^ 2 * (n : ℚ) ^ (m - 1 - i) := by
      rw [← pow_add]; congr 1; omega
    rw [this]
    push_cast
    ring
  have hZint : ∀ p : ℕ, p.Prime → IsPIntegral p Z := by
    intro p hp
    have : Fact p.Prime := ⟨hp⟩
    by_cases hpn : p ∣ n
    · exact isPIntegral_sum _ fun i hi =>
        zterm_pint p _ m ⟨k, hk⟩ hm0 hV2 hV3 n hpn i (mem_range.mp hi)
    · have hn2 : IsPIntegral p ((n : ℚ) ^ 2)⁻¹ := by
        have := isPIntegral_inv_of_not_dvd_num (p := p) (x := ((n ^ 2 : ℕ) : ℚ)) (by
          rw [Rat.num_natCast]
          intro h
          exact hpn (hp.dvd_of_dvd_pow (Int.natCast_dvd_natCast.mp h)))
        simpa using this
      have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
      have hZeq : Z = (((((bernoulli m).den : ℤ) * powerSum m n - (bernoulli m).num * n : ℤ)) : ℚ) *
          ((n : ℚ) ^ 2)⁻¹ := by
        push_cast
        rw [hid]
        field_simp
      rw [hZeq]
      exact (isPIntegral_intCast _).mul hn2
  have hden : Z.den = 1 := by
    by_contra h
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h
    exact hZint p hp hpd
  have hZz : (Z.num : ℚ) = Z := Rat.intCast_num_of_den_eq_one hden
  have hint : (((bernoulli m).den : ℤ) * powerSum m n - (bernoulli m).num * n) =
      (n : ℤ) ^ 2 * Z.num := by
    have : ((((bernoulli m).den : ℤ) * powerSum m n - (bernoulli m).num * n : ℤ) : ℚ) =
        (((n : ℤ) ^ 2 * Z.num : ℤ) : ℚ) := by
      push_cast
      rw [hZz]
      exact hid
    exact_mod_cast this
  exact Int.modEq_iff_dvd.2 ⟨-Z.num, by linarith⟩

/-- **Ireland–Rosen, §15.2, Corollary to Proposition 15.2.2.** For even `m ≥ 2` and a prime `p`
with `p - 1 ∤ m`, `S_m(p) ≡ p B_m (mod p^2)`. -/
@[kb "irelandrosen1990" "§15.2, Corollary to Proposition 15.2.2"]
theorem pModEq_powerSum_mul_bernoulli (p : ℕ) [Fact p.Prime] {m : ℕ} (hm : Even m) (hm0 : m ≠ 0)
    (hpm : ¬ p - 1 ∣ m) : PModEq p 2 (powerSum m p) (p * bernoulli m) := by
  have h := den_mul_powerSum_modEq hm hm0 p
  obtain ⟨c, hc⟩ := Int.modEq_iff_dvd.1 h
  have hBint : IsPIntegral p (bernoulli m) := by
    obtain ⟨k, hk⟩ := hm
    have hm2 : m = 2 * k := by omega
    rw [hm2]
    exact isPIntegral_bernoulli_V p (by rw [← hm2]; exact hpm)
  have hVq : ((bernoulli m).den : ℚ) ≠ 0 := by exact_mod_cast (bernoulli m).den_nz
  have hVint : IsPIntegral p (((bernoulli m).den : ℚ))⁻¹ := by
    apply isPIntegral_inv_of_not_dvd_num
    rw [Rat.num_natCast]
    exact fun h => hBint (Int.natCast_dvd_natCast.mp h)
  have hnum : ((bernoulli m).num : ℚ) = bernoulli m * (bernoulli m).den :=
    (Rat.mul_den_eq_num (bernoulli m)).symm
  have hcq : ((bernoulli m).num : ℚ) * p - ((bernoulli m).den : ℚ) * (powerSum m p : ℚ) =
      (p : ℚ) ^ 2 * c := by
    have := congrArg (fun z : ℤ => (z : ℚ)) hc
    simpa using this
  rw [hnum] at hcq
  have key : ((bernoulli m).den : ℚ) * ((powerSum m p : ℚ) - p * bernoulli m) =
      (p : ℚ) ^ 2 * (-c) := by linear_combination (-1 : ℚ) * hcq
  refine pModEq_iff.2 ⟨-c * ((bernoulli m).den : ℚ)⁻¹, (isPIntegral_intCast (-c)).mul hVint, ?_⟩
  calc (powerSum m p : ℚ) - p * bernoulli m
      = ((bernoulli m).den : ℚ)⁻¹ * (((bernoulli m).den : ℚ) *
          ((powerSum m p : ℚ) - p * bernoulli m)) := by field_simp
    _ = (p : ℚ) ^ 2 * (-c * ((bernoulli m).den : ℚ)⁻¹) := by rw [key]; ring

/-- The Voronoi sum `∑_{j=1}^{n-1} j^(m-1) [ja/n]`. -/
def voronoiSum (m a n : ℕ) : ℤ := ∑ j ∈ Ico 1 n, (j : ℤ) ^ (m - 1) * ((j * a / n : ℕ) : ℤ)

private lemma sum_mod_perm {a n : ℕ} (han : a.Coprime n) (m : ℕ) :
    ∑ j ∈ Ico 1 n, (j * a % n) ^ m = ∑ j ∈ Ico 1 n, j ^ m := by
  have hmaps : ∀ j ∈ Ico 1 n, j * a % n ∈ Ico 1 n := by
    intro j hj
    rw [mem_Ico] at hj ⊢
    constructor
    · by_contra h0
      have h1 : n ∣ j * a := Nat.dvd_of_mod_eq_zero (by omega)
      have h2 : n ∣ j := han.symm.dvd_of_dvd_mul_right h1
      exact absurd (Nat.le_of_dvd (by omega) h2) (by omega)
    · exact Nat.mod_lt _ (by omega)
  have hinj : Set.InjOn (fun j => j * a % n) (Ico 1 n : Set ℕ) := by
    intro j hj j' hj' h
    have h1 : j ≡ j' [MOD n] := Nat.ModEq.cancel_right_of_coprime (c := a) han.symm.gcd_eq_one h
    have hj1 := (mem_Ico.mp (mem_coe.mp hj)).2
    have hj2 := (mem_Ico.mp (mem_coe.mp hj')).2
    exact h1.eq_of_lt_of_lt hj1 hj2
  have himg : (Ico 1 n).image (fun j => j * a % n) = Ico 1 n :=
    eq_of_subset_of_card_le (image_subset_iff.2 hmaps) (by rw [card_image_of_injOn hinj])
  calc ∑ j ∈ Ico 1 n, (j * a % n) ^ m
      = ∑ r ∈ (Ico 1 n).image (fun j => j * a % n), r ^ m := (sum_image (f := fun r => r ^ m) hinj).symm
    _ = ∑ j ∈ Ico 1 n, j ^ m := by rw [himg]

private lemma voronoi_term (m a n j : ℕ) :
    (n : ℤ) ^ 2 ∣ ((j * a % n : ℕ) : ℤ) ^ m - ((j : ℤ) * a) ^ m +
      m * ((j : ℤ) * a) ^ (m - 1) * n * ((j * a / n : ℕ) : ℤ) := by
  have h := Nat.div_add_mod (j * a) n
  have hr : ((j * a % n : ℕ) : ℤ) = (j : ℤ) * a + (-((n : ℤ) * ((j * a / n : ℕ) : ℤ))) := by
    have : ((n * (j * a / n) + j * a % n : ℕ) : ℤ) = ((j * a : ℕ) : ℤ) := by rw [h]
    push_cast at this ⊢
    linarith
  have key := sq_dvd_add_pow_sub_sub (-((n : ℤ) * ((j * a / n : ℕ) : ℤ))) ((j : ℤ) * a) m
  have hd : (n : ℤ) ^ 2 ∣ (-((n : ℤ) * ((j * a / n : ℕ) : ℤ))) ^ 2 :=
    ⟨((j * a / n : ℕ) : ℤ) ^ 2, by ring⟩
  rw [hr]
  have e : ((j : ℤ) * a + (-((n : ℤ) * ((j * a / n : ℕ) : ℤ)))) ^ m - ((j : ℤ) * a) ^ m +
      m * ((j : ℤ) * a) ^ (m - 1) * n * ((j * a / n : ℕ) : ℤ) =
      ((j : ℤ) * a + (-((n : ℤ) * ((j * a / n : ℕ) : ℤ)))) ^ m
        - ((j : ℤ) * a) ^ (m - 1) * (-((n : ℤ) * ((j * a / n : ℕ) : ℤ))) * m
        - ((j : ℤ) * a) ^ m := by ring
  rw [e]
  exact hd.trans key

/-- **Ireland–Rosen, Proposition 15.2.3 (Voronoi congruences).** For even `m ≥ 2`, `n ≥ 1` and
`a` prime to `n`, `(a^m - 1) U_m ≡ m a^(m-1) V_m ∑_{j=1}^{n-1} j^(m-1) [ja/n] (mod n)`. -/
@[kb "irelandrosen1990" "Proposition 15.2.3"]
theorem voronoi_congruence {m : ℕ} (hm : Even m) (hm0 : m ≠ 0) {a n : ℕ} (han : a.Coprime n) :
    ((a : ℤ) ^ m - 1) * (bernoulli m).num ≡
      m * (a : ℤ) ^ (m - 1) * (bernoulli m).den * voronoiSum m a n [ZMOD n] := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : a = 1 := by simpa using han
    subst this
    simp [voronoiSum]
  have h1 := den_mul_powerSum_modEq hm hm0 n
  have hsum : (n : ℤ) ^ 2 ∣ ∑ j ∈ Ico 1 n, (((j * a % n : ℕ) : ℤ) ^ m - ((j : ℤ) * a) ^ m +
      m * ((j : ℤ) * a) ^ (m - 1) * n * ((j * a / n : ℕ) : ℤ)) :=
    dvd_sum fun j _ => voronoi_term m a n j
  have e1 : ∑ j ∈ Ico 1 n, ((j * a % n : ℕ) : ℤ) ^ m = (powerSum m n : ℤ) := by
    have := sum_mod_perm han m
    unfold powerSum
    exact_mod_cast this
  have e2 : ∑ j ∈ Ico 1 n, ((j : ℤ) * a) ^ m = (a : ℤ) ^ m * (powerSum m n : ℤ) := by
    unfold powerSum
    push_cast
    rw [mul_sum]
    exact sum_congr rfl fun j _ => by ring
  have e3 : ∑ j ∈ Ico 1 n, (m * ((j : ℤ) * a) ^ (m - 1) * n * ((j * a / n : ℕ) : ℤ)) =
      m * (a : ℤ) ^ (m - 1) * n * voronoiSum m a n := by
    unfold voronoiSum
    rw [mul_sum]
    exact sum_congr rfl fun j _ => by ring
  rw [sum_add_distrib, sum_sub_distrib, e1, e2, e3] at hsum
  obtain ⟨c, hc⟩ := hsum
  obtain ⟨d, hd⟩ := Int.modEq_iff_dvd.1 h1
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have key : (n : ℤ) * (m * (a : ℤ) ^ (m - 1) * (bernoulli m).den * voronoiSum m a n
      - ((a : ℤ) ^ m - 1) * (bernoulli m).num) =
      (n : ℤ) * ((n : ℤ) * (((bernoulli m).den : ℤ) * c - ((a : ℤ) ^ m - 1) * d)) := by
    linear_combination ((bernoulli m).den : ℤ) * hc - ((a : ℤ) ^ m - 1) * hd
  have key2 := mul_left_cancel₀ hn0 key
  exact Int.modEq_iff_dvd.2 ⟨_, key2⟩

end NTKB.IrelandRosen
