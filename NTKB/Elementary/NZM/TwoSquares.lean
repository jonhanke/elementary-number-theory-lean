/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Attr
import NTKB.Elementary.NZM.QuadraticForms
import NTKB.Elementary.HardyWright.ArithmeticFunctions.SumTwoSquares
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Sums of two squares (Niven–Zuckerman–Montgomery, § 3.6)

* Theorem 3.20: a positive integer `n` is a sum of two coprime squares if and only if every odd prime
  factor of `n` is `≡ 1 (mod 4)` and `4 ∤ n`.
  (`⇒`: `-1` is a square modulo `n` by Mathlib's `ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_isCoprime`.
  `⇐`: `-1` is a square modulo every prime power `pᵏ`, `p ≡ 1 (mod 4)` (Hensel lifting by an explicit
  Newton step), hence modulo `n` by the Chinese remainder theorem; then Theorem 3.13 gives a form of
  discriminant `-4` properly representing `n`, which is equivalent to `x² + y²` because the only reduced
  forms of discriminant `-4` are `±(1, 0, 1)` (Theorems 3.18, 3.17).)
* Theorem 3.21 (second part): the number `R(n)` of all representations `n = x² + y²` is
  `∑_{d² ∣ n} r(n/d²)`, where `r(m)` counts the proper ones (`gcd(x, y) = 1`). The first part
  `r(n) = 4 N(n)` is not formalized here.
-/

namespace NTKB.NZM

open NTKB.Davenport

/-! ### `-1` as a square modulo `n` -/

/-- `-1` is a square in `ZMod n` iff `n ∣ s² + 1` for some integer `s`. -/
lemma isSquare_neg_one_iff_dvd (n : ℕ) :
    IsSquare (-1 : ZMod n) ↔ ∃ s : ℤ, (n : ℤ) ∣ s ^ 2 + 1 := by
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨t, rfl⟩ := ZMod.intCast_surjective r
    refine ⟨t, ?_⟩
    have h : ((t * t : ℤ) : ZMod n) = ((-1 : ℤ) : ZMod n) := by
      push_cast
      exact hr.symm
    have h1 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h
    have h2 : (n : ℤ) ∣ -(-1 - t * t) := dvd_neg.mpr h1
    have e : t ^ 2 + 1 = -(-1 - t * t) := by ring
    rw [e]
    exact h2
  · rintro ⟨s, hs⟩
    refine ⟨(s : ZMod n), ?_⟩
    have hd : (n : ℤ) ∣ (-1 : ℤ) - s * s := by
      have e : (-1 : ℤ) - s * s = -(s ^ 2 + 1) := by ring
      rw [e]
      exact dvd_neg.mpr hs
    have h : ((s * s : ℤ) : ZMod n) = ((-1 : ℤ) : ZMod n) :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr hd
    push_cast at h
    exact h.symm

/-- Hensel lifting of a square root of `-1` modulo an odd prime to every power of the prime
(an explicit Newton step `s ↦ s (1 + h (s² + 1))` with `2h = p + 1`). -/
lemma exists_dvd_sq_add_one_pow {p : ℕ} (hp : p % 2 = 1) {s : ℤ} (hs : (p : ℤ) ∣ s ^ 2 + 1) :
    ∀ k : ℕ, 1 ≤ k → ∃ t : ℤ, (p : ℤ) ^ k ∣ t ^ 2 + 1 := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    refine ⟨s, ?_⟩
    rw [pow_one]
    exact hs
  | succ j hj ih =>
    obtain ⟨t, c, hc⟩ := ih
    obtain ⟨i, hi⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    obtain ⟨h, hh⟩ : ∃ h : ℤ, 2 * h = (p : ℤ) + 1 := ⟨(p : ℤ) / 2 + 1, by omega⟩
    refine ⟨t * (1 + h * (t ^ 2 + 1)), ?_⟩
    have key : (t * (1 + h * (t ^ 2 + 1))) ^ 2 + 1 =
        (t ^ 2 + 1) ^ 2 * (1 + t ^ 2 * h ^ 2) + (p : ℤ) * t ^ 2 * (t ^ 2 + 1) := by
      linear_combination ((t ^ 2 + 1) * t ^ 2) * hh
    subst hi
    have key2 : (t * (1 + h * (t ^ 2 + 1))) ^ 2 + 1 =
        (p : ℤ) ^ (i + 1 + 1) * ((p : ℤ) ^ i * c ^ 2 * (1 + t ^ 2 * h ^ 2) + c * t ^ 2) := by
      rw [key, hc]
      ring
    exact ⟨_, key2⟩

/-- If every odd prime factor of `n` is `≡ 1 (mod 4)` and `4 ∤ n`, then `-1` is a square modulo `n`
(Chinese remainder theorem over the prime powers dividing `n`). -/
lemma isSquare_neg_one_of_conditions : ∀ n : ℕ,
    (∀ p : ℕ, p.Prime → p ∣ n → p ≠ 2 → p % 4 = 1) → ¬ 4 ∣ n → IsSquare (-1 : ZMod n) := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    intro hodd h4
    by_cases hp2 : p = 2
    · subst hp2
      have hk1 : k = 1 := by
        by_contra hne
        apply h4
        have h2k : 2 ≤ k := by omega
        exact Dvd.dvd.trans (by norm_num : (4 : ℕ) ∣ 2 ^ 2) (pow_dvd_pow 2 h2k)
      subst hk1
      rw [pow_one]
      exact ⟨1, by decide⟩
    · have hp4 : p % 4 = 1 := hodd p hp (dvd_pow_self p hk.ne') hp2
      haveI := Fact.mk hp
      have h1 : IsSquare (-1 : ZMod p) := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)
      obtain ⟨s, hs⟩ := (isSquare_neg_one_iff_dvd p).mp h1
      obtain ⟨s', hs'⟩ := exists_dvd_sq_add_one_pow (by omega : p % 2 = 1) hs k hk
      refine (isSquare_neg_one_iff_dvd (p ^ k)).mpr ⟨s', ?_⟩
      push_cast
      exact hs'
  | zero =>
    intro _ h4
    exact absurd (dvd_zero 4) h4
  | one =>
    intro _ _
    exact ⟨0, by simp only [mul_zero, eq_iff_true_of_subsingleton]⟩
  | coprime a b ha hb hab iha ihb =>
    intro hodd h4
    exact ZMod.isSquare_neg_one_mul hab
      (iha (fun p hp hpa hp2 => hodd p hp (dvd_mul_of_dvd_left hpa b) hp2)
        (fun h => h4 (dvd_mul_of_dvd_left h b)))
      (ihb (fun p hp hpb hp2 => hodd p hp (dvd_mul_of_dvd_right hpb a) hp2)
        (fun h => h4 (dvd_mul_of_dvd_right h a)))

/-! ### Forms of discriminant `-4` -/

/-- If some form of discriminant `-4` properly represents `n > 0`, then `n = x² + y²` with
`(x, y) = 1`: every such form is equivalent to its reduced form, which is `(1, 0, 1)` (the form
`(-1, 0, -1)` is negative definite and cannot represent `n > 0`). -/
lemma exists_coprime_sq_add_sq_of_disc_neg_four {n : ℤ} (hn : 0 < n)
    (h : ∃ f x y, formDisc f = -4 ∧ IsCoprime x y ∧ formEval f x y = n) :
    ∃ x y : ℤ, IsCoprime x y ∧ x ^ 2 + y ^ 2 = n := by
  obtain ⟨f, x, y, hfd, hxy, hfe⟩ := h
  have hns : ¬IsSquare (formDisc f) := by
    rw [hfd]
    rintro ⟨r, hr⟩
    nlinarith [mul_self_nonneg r]
  obtain ⟨g, hfg, hred⟩ := exists_formEquiv_isReducedForm f hns
  obtain ⟨hgd, e, he1, he2⟩ := formEquiv_rep_equiv hfg
  rw [hfd] at hgd
  obtain ⟨v, hv⟩ : ∃ v, e v = (x, y) := ⟨e.symm (x, y), e.apply_symm_apply _⟩
  have hgv : formEval g v.1 v.2 = n := by
    rw [← he1 v, hv]
    exact hfe
  have hcop : IsCoprime v.1 v.2 := by
    refine (he2 v).mp ?_
    rw [hv]
    exact hxy
  obtain ⟨a, b, c⟩ := g
  have h1 : |b| ≤ |a| := hred.abs_le_abs.1
  have h2 : |a| ≤ |c| := hred.abs_le_abs.2
  simp only [formDisc] at hgd
  simp only [formEval] at hgv
  have hb2 : b ^ 2 ≤ a ^ 2 := sq_le_sq.mpr h1
  have hac4 : 4 * (a * c) = b ^ 2 + 4 := by linear_combination -hgd
  have hpos : 0 < a * c := by
    have := sq_nonneg b
    linarith
  have hac : a ^ 2 ≤ |a * c| := by
    rw [abs_mul, sq, ← abs_mul_abs_self a]
    exact mul_le_mul_of_nonneg_left h2 (abs_nonneg a)
  rw [abs_of_pos hpos] at hac
  have ha2 : a ^ 2 ≤ 1 := by linarith
  have ha1 : -1 ≤ a ∧ a ≤ 1 := by constructor <;> nlinarith
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hpos
  have hb1 : -1 ≤ b ∧ b ≤ 1 := by constructor <;> nlinarith
  have hb0 : b = 0 := by
    rcases (by omega : b = -1 ∨ b = 0 ∨ b = 1) with rfl | rfl | rfl
    · exfalso
      norm_num at hac4 <;> omega
    · rfl
    · exfalso
      norm_num at hac4 <;> omega
  subst hb0
  have hac1 : a * c = 1 := by nlinarith
  rcases (by omega : a = 1 ∨ a = -1) with rfl | rfl
  · have hc : c = 1 := by linarith
    subst hc
    refine ⟨v.1, v.2, hcop, ?_⟩
    linear_combination hgv
  · have hc : c = -1 := by linarith
    subst hc
    exfalso
    nlinarith [sq_nonneg v.1, sq_nonneg v.2]

/-! ### Theorem 3.20 -/

/-- **Theorem 3.20.** A positive integer `n` is a sum of two squares of coprime integers if and only if
every odd prime factor of `n` is `≡ 1 (mod 4)` and `4 ∤ n`. -/
@[kb "nivenzuckermanmontgomery" "Thm 3.20, p. 165"]
theorem proper_sum_two_sq_iff {n : ℕ} (hn : 0 < n) :
    (∃ x y : ℤ, IsCoprime x y ∧ x ^ 2 + y ^ 2 = n) ↔
      (∀ p : ℕ, p.Prime → p ∣ n → p ≠ 2 → p % 4 = 1) ∧ ¬ 4 ∣ n := by
  constructor
  · rintro ⟨x, y, hc, hxy⟩
    have hsq' := ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_isCoprime (n := (n : ℤ)) (x := x)
      (y := y) hxy.symm hc
    have e : ((n : ℤ)).natAbs = n := by omega
    rw [e] at hsq'
    refine ⟨fun p hp hpn hp2 => ?_, fun h4 => ?_⟩
    · have hmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpn, hn.ne'⟩
      have h3 := Nat.mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one hmem hsq'
      rcases hp.eq_two_or_odd with h | h
      · exact absurd h hp2
      · omega
    · obtain ⟨r, hr⟩ := ZMod.isSquare_neg_one_of_dvd h4 hsq'
      have hall : ∀ r : ZMod 4, (-1 : ZMod 4) ≠ r * r := by decide
      exact hall r hr
  · rintro ⟨hodd, h4⟩
    have hsq := isSquare_neg_one_of_conditions n hodd h4
    obtain ⟨t, k, hk⟩ := (isSquare_neg_one_iff_dvd n).mp hsq
    have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
    have hmod : (2 * t) ^ 2 ≡ -4 [ZMOD 4 * |(n : ℤ)|] := by
      rw [Int.modEq_iff_dvd, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (n : ℤ))]
      exact ⟨-k, by linear_combination (-4) * hk⟩
    have hrep := (exists_proper_rep_iff hn' (-4)).mpr ⟨2 * t, hmod⟩
    exact exists_coprime_sq_add_sq_of_disc_neg_four (by exact_mod_cast hn) hrep

/-! ### Theorem 3.21: counting representations -/

/-- The representations `n = x² + y²` (`x, y ∈ ℤ`), as a finset of pairs (an auxiliary finset form of
`NTKB.HardyWright.sumTwoSquaresCount`). -/
def twoSqRepSet (n : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).filter fun p => p.1 ^ 2 + p.2 ^ 2 = n

/-- The proper representations `n = x² + y²`, `gcd(x, y) = 1`, as a finset of pairs. -/
def properTwoSqRepSet (n : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).filter fun p =>
    Int.gcd p.1 p.2 = 1 ∧ p.1 ^ 2 + p.2 ^ 2 = n

/-- Auxiliary: the cardinality of `twoSqRepSet n`; it equals Hardy–Wright's
`NTKB.HardyWright.sumTwoSquaresCount n` (`sqRepCount_eq_sumTwoSquaresCount`), which is `R(n)`. -/
def sqRepCount (n : ℕ) : ℕ := (twoSqRepSet n).card

/-- `r(n)`: the number of proper representations `n = x² + y²`, `gcd(x, y) = 1`. -/
def properSqRepCount (n : ℕ) : ℕ := (properTwoSqRepSet n).card

lemma le_sq_int (x : ℤ) : x ≤ x ^ 2 := by
  rcases le_or_gt x 0 with h | h
  · nlinarith [sq_nonneg x]
  · nlinarith [sq_nonneg (x - 1)]

lemma sq_add_sq_bound {x y : ℤ} {n : ℕ} (h : x ^ 2 + y ^ 2 = n) :
    (-(n : ℤ) ≤ x ∧ x ≤ n) ∧ (-(n : ℤ) ≤ y ∧ y ≤ n) := by
  have h1 := le_sq_int x
  have h2 := le_sq_int (-x)
  have h3 := le_sq_int y
  have h4 := le_sq_int (-y)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith [sq_nonneg x, sq_nonneg y]

lemma mem_twoSqRepSet {n : ℕ} {p : ℤ × ℤ} : p ∈ twoSqRepSet n ↔ p.1 ^ 2 + p.2 ^ 2 = n := by
  simp only [twoSqRepSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  exact ⟨fun h => h.2, fun h => ⟨sq_add_sq_bound h, h⟩⟩

lemma mem_properTwoSqRepSet {n : ℕ} {p : ℤ × ℤ} :
    p ∈ properTwoSqRepSet n ↔ Int.gcd p.1 p.2 = 1 ∧ p.1 ^ 2 + p.2 ^ 2 = n := by
  simp only [properTwoSqRepSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  exact ⟨fun h => h.2, fun h => ⟨sq_add_sq_bound h.2, h⟩⟩

/-- `R(n)` agrees with Hardy–Wright's `r(n)` (`NTKB.HardyWright.sumTwoSquaresCount`). -/
lemma sqRepCount_eq_sumTwoSquaresCount (n : ℕ) :
    sqRepCount n = NTKB.HardyWright.sumTwoSquaresCount n := by
  unfold sqRepCount NTKB.HardyWright.sumTwoSquaresCount
  have : {x : ℤ × ℤ | x.1 ^ 2 + x.2 ^ 2 = n} = ↑(twoSqRepSet n) := by
    ext p
    exact (mem_twoSqRepSet (n := n) (p := p)).symm
  rw [this, Set.ncard_coe_finset]

/-- The gcd `g` of a representation of `n > 0` is positive and `g² ∣ n`. -/
lemma gcd_pos_and_sq_dvd {x y : ℤ} {n : ℕ} (hn : 0 < n) (hs : x ^ 2 + y ^ 2 = n) :
    0 < Int.gcd x y ∧ (Int.gcd x y) ^ 2 ∣ n := by
  have hg0 : 0 < Int.gcd x y := by
    rcases Nat.eq_zero_or_pos (Int.gcd x y) with h | h
    · exfalso
      obtain ⟨hx, hy⟩ := Int.gcd_eq_zero_iff.mp h
      rw [hx, hy] at hs
      have : (n : ℤ) = 0 := by rw [← hs]; norm_num
      omega
    · exact h
  refine ⟨hg0, ?_⟩
  obtain ⟨u, v, huv, h1, h2⟩ := Int.exists_gcd_one hg0
  have hdvd : (((Int.gcd x y) ^ 2 : ℕ) : ℤ) ∣ (n : ℤ) := by
    refine ⟨u ^ 2 + v ^ 2, ?_⟩
    push_cast
    linear_combination (-1) * hs + (x + u * (Int.gcd x y : ℤ)) * h1 +
      (y + v * (Int.gcd x y : ℤ)) * h2
  exact Int.natCast_dvd_natCast.mp hdvd

/-- **Theorem 3.21** (second part). For `n > 0` the number `R(n)` of all representations of `n` as
`x² + y²` is `∑_{d² ∣ n} r(n/d²)`, where `r(m)` is the number of proper representations of `m`.
(The bijection sends `(x, y)` to `(d, (x/d, y/d))` with `d = gcd(x, y)`.) -/
theorem sqRepCount_eq_sum_properSqRepCount {n : ℕ} (hn : 0 < n) :
    sqRepCount n = ∑ d ∈ n.divisors.filter (fun d => d ^ 2 ∣ n), properSqRepCount (n / d ^ 2) := by
  have H : ∀ p ∈ twoSqRepSet n, Int.gcd p.1 p.2 ∈ n.divisors.filter (fun d => d ^ 2 ∣ n) := by
    intro p hp
    rw [mem_twoSqRepSet] at hp
    obtain ⟨_, hsq⟩ := gcd_pos_and_sq_dvd hn hp
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨(dvd_pow_self _ two_ne_zero).trans hsq, hn.ne'⟩, hsq⟩
  unfold sqRepCount
  rw [Finset.card_eq_sum_card_fiberwise (f := fun p : ℤ × ℤ => Int.gcd p.1 p.2)
    (t := n.divisors.filter (fun d => d ^ 2 ∣ n)) H]
  refine Finset.sum_congr rfl ?_
  intro d hd
  rw [Finset.mem_filter, Nat.mem_divisors] at hd
  obtain ⟨⟨hdn, _⟩, hsqd⟩ := hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
  have hd0' : (d : ℤ) ≠ 0 := by exact_mod_cast hd0.ne'
  obtain ⟨m, hm⟩ := hsqd
  have hm' : n / d ^ 2 = m := by
    rw [hm]
    exact Nat.mul_div_cancel_left m (by positivity)
  have hmz : (n : ℤ) = (d : ℤ) ^ 2 * m := by exact_mod_cast hm
  unfold properSqRepCount
  rw [hm']
  symm
  refine Finset.card_bij (fun p _ => ((d : ℤ) * p.1, (d : ℤ) * p.2)) ?_ ?_ ?_
  · intro p hp
    rw [mem_properTwoSqRepSet] at hp
    obtain ⟨hg, hs⟩ := hp
    simp only [Finset.mem_filter, mem_twoSqRepSet]
    refine ⟨?_, ?_⟩
    · rw [hmz]
      linear_combination (d : ℤ) ^ 2 * hs
    · rw [Int.gcd_mul_left, hg]
      simp
  · intro p _ q _ hpq
    simp only [Prod.mk.injEq] at hpq
    exact Prod.ext (mul_left_cancel₀ hd0' hpq.1) (mul_left_cancel₀ hd0' hpq.2)
  · intro p hp
    simp only [Finset.mem_filter, mem_twoSqRepSet] at hp
    obtain ⟨hs, hg⟩ := hp
    obtain ⟨u, v, huv, h1, h2⟩ := Int.exists_gcd_one (m := p.1) (n := p.2) (by rw [hg]; exact hd0)
    rw [hg] at h1 h2
    have e : (d : ℤ) ^ 2 * (u ^ 2 + v ^ 2) = (d : ℤ) ^ 2 * m := by
      linear_combination (-(p.1 + u * d)) * h1 + (-(p.2 + v * d)) * h2 + hs + hmz
    have e2 : u ^ 2 + v ^ 2 = m := mul_left_cancel₀ (pow_ne_zero 2 hd0') e
    refine ⟨(u, v), ?_, ?_⟩
    · rw [mem_properTwoSqRepSet]
      exact ⟨huv, e2⟩
    · refine Prod.ext ?_ ?_
      · show (d : ℤ) * u = p.1
        linear_combination -h1
      · show (d : ℤ) * v = p.2
        linear_combination -h2

/-- **Theorem 3.21** (second part). For `n > 0` the number `R(n)` of all representations of `n` as
`x² + y²` (`NTKB.HardyWright.sumTwoSquaresCount n`) is `∑_{d² ∣ n} r(n/d²)`, where `r(m)` is the number
of proper representations of `m`. -/
@[kb "nivenzuckermanmontgomery" "Thm 3.21, p. 166"]
theorem sumTwoSquaresCount_eq_sum_properSqRepCount {n : ℕ} (hn : 0 < n) :
    NTKB.HardyWright.sumTwoSquaresCount n =
      ∑ d ∈ n.divisors.filter (fun d => d ^ 2 ∣ n), properSqRepCount (n / d ^ 2) := by
  rw [← sqRepCount_eq_sumTwoSquaresCount, sqRepCount_eq_sum_properSqRepCount hn]

end NTKB.NZM
