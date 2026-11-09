/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.ArithmeticFunctions.Delta
import NTKB.Attr
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Data.Int.Interval
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.Algebra.Order.Star.Int

/-!
# Hardy–Wright, §§ 16.9–16.10: the function `r(n)`

`r(n)` is the number of representations `n = A² + B²` with `A, B` rational integers (signs and order
counted). Theorem 278: `r(n) = 4 δ(n)`, `δ(n) = ∑_{d ∣ n} χ(d)`.

The proof works in the Gaussian integers, as the book's (§ 16.10), but counts by recursion on the
prime factors of `n` instead of writing down all factorizations at once: if `p ∣ n` then
* `p = 2`: every `z` of norm `n` is divisible by `1 + i`, so `r(n) = r(n/2)`;
* `p ≡ 3 (mod 4)`: `p` divides every `z` of norm `n`, so `r(n) = r(n/p²)` (and `r(n) = 0` if
  `p² ∤ n`);
* `p ≡ 1 (mod 4)`: `p = π π̄` with `π`, `π̄` non-associated Gaussian primes, every `z` of norm `n` is
  divisible by `π` or by `π̄`, and by both exactly when `p ∣ z`; so `r(n) = 2 r(n/p) - r(n/p²)`.
`δ` satisfies the same recursions by (16.9.5).
-/

open Finset GaussianInt Zsqrtd

namespace NTKB.HardyWright

/-- The Gaussian integers of norm `n`. -/
def normSet (n : ℕ) : Set GaussianInt := {z | z.norm = n}

lemma norm_eq_sq_add_sq (z : GaussianInt) : z.norm = z.re ^ 2 + z.im ^ 2 := by
  rw [Zsqrtd.norm_def]; ring

lemma abs_re_le_of_norm {z : GaussianInt} {n : ℕ} (hz : z.norm = n) : |z.re| ≤ n ∧ |z.im| ≤ n := by
  rw [norm_eq_sq_add_sq] at hz
  have h1 : |z.re| ≤ z.re ^ 2 := by
    rcases eq_or_ne z.re 0 with h | h
    · simp [h]
    · rw [sq, ← abs_mul_abs_self]; exact le_mul_of_one_le_left (abs_nonneg _) (Int.one_le_abs h)
  have h2 : |z.im| ≤ z.im ^ 2 := by
    rcases eq_or_ne z.im 0 with h | h
    · simp [h]
    · rw [sq, ← abs_mul_abs_self]; exact le_mul_of_one_le_left (abs_nonneg _) (Int.one_le_abs h)
  constructor <;> nlinarith [sq_nonneg z.re, sq_nonneg z.im]

lemma normSet_finite (n : ℕ) : (normSet n).Finite := by
  have hfin : ((Icc (-(n : ℤ)) n ×ˢ Icc (-(n : ℤ)) n : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)).Finite :=
    finite_toSet _
  refine (hfin.image fun x => (⟨x.1, x.2⟩ : GaussianInt)).subset fun z hz => ?_
  obtain ⟨h1, h2⟩ := abs_re_le_of_norm (n := n) hz
  refine ⟨(z.re, z.im), ?_, rfl⟩
  simp only [coe_product, coe_Icc, Set.mem_prod, Set.mem_Icc]
  exact ⟨abs_le.mp h1, abs_le.mp h2⟩

/-- Multiplication by `c ≠ 0` maps the Gaussian integers of norm `m` bijectively onto those of
norm `N(c) m` divisible by `c`. -/
lemma image_mul_normSet {c : GaussianInt} (hc : c ≠ 0) (m : ℕ) (N : ℕ) (hN : c.norm * m = N) :
    (c * ·) '' normSet m = {z | z ∈ normSet N ∧ c ∣ z} := by
  ext z
  simp only [Set.mem_image, normSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨by rw [Zsqrtd.norm_mul, hw, ← hN], dvd_mul_right c w⟩
  · rintro ⟨hz, w, rfl⟩
    refine ⟨w, ?_, rfl⟩
    rw [Zsqrtd.norm_mul, ← hN] at hz
    have hc0 : c.norm ≠ 0 := by rwa [ne_eq, GaussianInt.norm_eq_zero]
    exact mul_left_cancel₀ hc0 hz

lemma ncard_mul_normSet {c : GaussianInt} (hc : c ≠ 0) (m : ℕ) (N : ℕ) (hN : c.norm * m = N) :
    {z | z ∈ normSet N ∧ c ∣ z}.ncard = (normSet m).ncard := by
  rw [← image_mul_normSet hc m N hN, Set.ncard_image_of_injective _ (mul_right_injective₀ hc)]

lemma setOf_mem_normSet_and_dvd_eq {c : GaussianInt} {n : ℕ} (h : ∀ z ∈ normSet n, c ∣ z) :
    {z | z ∈ normSet n ∧ c ∣ z} = normSet n := by
  ext z; exact ⟨fun h => h.1, fun hz => ⟨hz, h z hz⟩⟩

/-! ### `p = 2`: `r(2m) = r(m)` -/

/-- `1 + i`. -/
def onePlusI : GaussianInt := ⟨1, 1⟩

lemma norm_onePlusI : onePlusI.norm = 2 := by decide

lemma onePlusI_dvd_of_two_dvd_norm {z : GaussianInt} (h : (2 : ℤ) ∣ z.norm) : onePlusI ∣ z := by
  rw [norm_eq_sq_add_sq] at h
  have hev : Even (z.re ^ 2 + z.im ^ 2) := even_iff_two_dvd.mpr h
  rw [Int.even_add, Int.even_pow' two_ne_zero, Int.even_pow' two_ne_zero, ← Int.even_add] at hev
  obtain ⟨k, hk⟩ := hev
  refine ⟨⟨k, k - z.re⟩, ?_⟩
  ext <;> simp [onePlusI]
  linarith

lemma ncard_normSet_two_mul (m : ℕ) : (normSet (2 * m)).ncard = (normSet m).ncard := by
  rw [← ncard_mul_normSet (c := onePlusI) (by decide) m (2 * m) (by rw [norm_onePlusI]; push_cast; ring),
    setOf_mem_normSet_and_dvd_eq]
  intro z hz
  apply onePlusI_dvd_of_two_dvd_norm
  rw [hz]; push_cast; exact dvd_mul_right 2 _

/-! ### `p ≡ 3 (mod 4)`: `p ∣ A² + B²` forces `p ∣ A`, `p ∣ B` -/

lemma dvd_re_im_of_dvd_norm {p : ℕ} (hp : p.Prime) (h3 : p % 4 = 3) {z : GaussianInt}
    (h : (p : ℤ) ∣ z.norm) : (p : ℤ) ∣ z.re ∧ (p : ℤ) ∣ z.im := by
  have := Fact.mk hp
  rw [norm_eq_sq_add_sq] at h
  have hz : ((z.re : ZMod p)) ^ 2 + ((z.im : ZMod p)) ^ 2 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h
    push_cast at this; exact this
  by_cases ha : (z.re : ZMod p) = 0
  · have hb : (z.im : ZMod p) ^ 2 = 0 := by rw [ha] at hz; simpa using hz
    exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ha,
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp (pow_eq_zero_iff two_ne_zero |>.mp hb)⟩
  · exfalso
    have : IsSquare (-1 : ZMod p) := ⟨(z.im : ZMod p) / z.re, by
      field_simp
      linear_combination -hz⟩
    exact (ZMod.exists_sq_eq_neg_one_iff.mp this) h3

lemma natCast_dvd_of_dvd_norm {p : ℕ} (hp : p.Prime) (h3 : p % 4 = 3) {z : GaussianInt}
    (h : (p : ℤ) ∣ z.norm) : (p : GaussianInt) ∣ z := by
  have := (Zsqrtd.intCast_dvd (p : ℤ) z).mpr (dvd_re_im_of_dvd_norm hp h3 h)
  exact_mod_cast this

lemma norm_natCast' (p : ℕ) : (p : GaussianInt).norm = ((p ^ 2 : ℕ) : ℤ) := by
  rw [Zsqrtd.norm_natCast]; push_cast; ring

/-- For `p ≡ 3 (mod 4)` dividing `n`: `r(n) = r(n/p²)` if `p² ∣ n`, and `r(n) = 0` otherwise. -/
lemma ncard_normSet_of_mod_four_eq_three {p : ℕ} (hp : p.Prime) (h3 : p % 4 = 3) {n : ℕ}
    (hpn : p ∣ n) :
    (normSet n).ncard = if p ^ 2 ∣ n then (normSet (n / p ^ 2)).ncard else 0 := by
  have hall : ∀ z ∈ normSet n, (p : GaussianInt) ∣ z := fun z hz =>
    natCast_dvd_of_dvd_norm hp h3 (by rw [hz]; exact_mod_cast hpn)
  have hp0 : (p : GaussianInt) ≠ 0 := by exact_mod_cast hp.ne_zero
  split_ifs with hp2
  · rw [← setOf_mem_normSet_and_dvd_eq hall]
    exact ncard_mul_normSet hp0 _ _ (by rw [norm_natCast']; norm_cast; exact Nat.mul_div_cancel' hp2)
  · rw [Set.ncard_eq_zero (normSet_finite n)]
    ext z
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hz
    obtain ⟨w, rfl⟩ := hall z hz
    apply hp2
    have : ((p ^ 2 : ℕ) : ℤ) ∣ (n : ℤ) := by
      rw [← hz, Zsqrtd.norm_mul, norm_natCast']; exact dvd_mul_right _ _
    exact_mod_cast this

/-- The Gaussian integers of norm `n` divisible by the rational integer `p ≠ 0`. -/
lemma ncard_normSet_natCast_dvd {p : ℕ} (hp : p ≠ 0) (n : ℕ) :
    {z | z ∈ normSet n ∧ (p : GaussianInt) ∣ z}.ncard =
      if p ^ 2 ∣ n then (normSet (n / p ^ 2)).ncard else 0 := by
  have hp0 : (p : GaussianInt) ≠ 0 := by exact_mod_cast hp
  split_ifs with hp2
  · exact ncard_mul_normSet hp0 _ _ (by rw [norm_natCast']; norm_cast; exact Nat.mul_div_cancel' hp2)
  · have hfin : {z | z ∈ normSet n ∧ (p : GaussianInt) ∣ z}.Finite :=
      (normSet_finite n).subset fun z hz => hz.1
    rw [Set.ncard_eq_zero hfin]
    ext z
    simp only [Set.mem_empty_iff_false, iff_false, Set.mem_ofPred_eq, not_and]
    intro hz hdvd
    obtain ⟨w, rfl⟩ := hdvd
    apply hp2
    have : ((p ^ 2 : ℕ) : ℤ) ∣ (n : ℤ) := by
      rw [← hz, Zsqrtd.norm_mul, norm_natCast']; exact dvd_mul_right _ _
    exact_mod_cast this

/-! ### `p ≡ 1 (mod 4)`: `p = π π̄` -/

lemma irreducible_of_natAbs_norm_prime {z : GaussianInt} (h : z.norm.natAbs.Prime) :
    Irreducible z := by
  refine ⟨fun hu => h.ne_one (Zsqrtd.norm_eq_one_iff.mpr hu), fun x y hxy => ?_⟩
  rw [hxy, Zsqrtd.norm_mul, Int.natAbs_mul, Nat.prime_mul_iff] at h
  rcases h with ⟨_, h⟩ | ⟨_, h⟩
  · exact Or.inr (Zsqrtd.norm_eq_one_iff.mp h)
  · exact Or.inl (Zsqrtd.norm_eq_one_iff.mp h)

lemma star_dvd_of_dvd_star {x y : GaussianInt} (h : x ∣ star y) : star x ∣ y := by
  obtain ⟨w, hw⟩ := h
  refine ⟨star w, ?_⟩
  have := congrArg star hw
  rw [star_star, star_mul, mul_comm] at this
  exact this

/-- For `p ≡ 1 (mod 4)` dividing `n`: `r(n) + r(n/p²) = 2 r(n/p)` (with `r(n/p²)` read as `0`
when `p² ∤ n`). -/
lemma ncard_normSet_of_mod_four_eq_one {p : ℕ} (hp : p.Prime) (h1 : p % 4 = 1) {n : ℕ}
    (hpn : p ∣ n) :
    (normSet n).ncard + (if p ^ 2 ∣ n then (normSet (n / p ^ 2)).ncard else 0) =
      2 * (normSet (n / p)).ncard := by
  have := Fact.mk hp
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
  set π : GaussianInt := ⟨a, b⟩ with hπ
  have hnorm : π.norm = p := by rw [norm_eq_sq_add_sq, hπ]; push_cast; exact_mod_cast hab
  have hnorm' : (star π).norm = p := by rw [Zsqrtd.norm_conj, hnorm]
  have hirr : Irreducible π := irreducible_of_natAbs_norm_prime (by rw [hnorm]; simpa using hp)
  have hprime : Prime π := irreducible_iff_prime.mp hirr
  have hπ0 : π ≠ 0 := hirr.ne_zero
  have hπ0' : star π ≠ 0 := by
    intro h; apply hπ0; rw [← star_star π, h, star_zero]
  have hmul : π * star π = (p : GaussianInt) := by
    rw [← Zsqrtd.norm_eq_mul_conj, hnorm]; push_cast; rfl
  -- `π ∤ π̄`
  have hnd : ¬ π ∣ star π := by
    intro hd
    have h2a : π ∣ ((2 * a : ℤ) : GaussianInt) := by
      have : ((2 * a : ℤ) : GaussianInt) = π + star π := by
        ext <;> simp [hπ]; ring
      rw [this]; exact dvd_add dvd_rfl hd
    obtain ⟨w, hw⟩ := h2a
    have hN := congrArg Zsqrtd.norm hw
    rw [Zsqrtd.norm_intCast, Zsqrtd.norm_mul, hnorm] at hN
    have hpd : (p : ℤ) ∣ (2 * a) * (2 * a) := ⟨w.norm, hN⟩
    have hpd' : p ∣ (2 * a) * (2 * a) := by exact_mod_cast hpd
    have hpa : p ∣ a := by
      rcases (Nat.Prime.dvd_mul hp).mp hpd' with h | h <;>
      · rcases (Nat.Prime.dvd_mul hp).mp h with h' | h'
        · exfalso
          have := Nat.le_of_dvd (by norm_num) h'
          have := hp.two_le
          interval_cases p
          simp_all
        · exact h'
    have ha0 : a = 0 := by
      by_contra ha0
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) hpa
      have : p * p ≤ a * a := Nat.mul_le_mul this this
      nlinarith [hp.two_le]
    subst ha0
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add] at hab
    rw [← hab, sq] at hp
    rcases Nat.prime_mul_iff.mp hp with ⟨h, h'⟩ | ⟨h, h'⟩ <;> subst h' <;> exact Nat.not_prime_one h
  have hcop : IsCoprime π (star π) := (Irreducible.coprime_iff_not_dvd hirr).mpr hnd
  -- the two halves and their intersection
  set A := {z | z ∈ normSet n ∧ π ∣ z}
  set B := {z | z ∈ normSet n ∧ star π ∣ z}
  have hnp : (p : ℤ) * (n / p : ℕ) = n := by norm_cast; exact Nat.mul_div_cancel' hpn
  have hA : A.ncard = (normSet (n / p)).ncard :=
    ncard_mul_normSet hπ0 _ _ (by rw [hnorm, hnp])
  have hB : B.ncard = (normSet (n / p)).ncard :=
    ncard_mul_normSet hπ0' _ _ (by rw [hnorm', hnp])
  have hunion : A ∪ B = normSet n := by
    ext z
    simp only [A, B, Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hz
      have hdvd : π ∣ z * star z := by
        rw [← Zsqrtd.norm_eq_mul_conj, hz]
        obtain ⟨k, hk⟩ := hpn
        rw [hk]; push_cast
        rw [← hmul, mul_assoc]
        exact dvd_mul_right _ _
      rcases hprime.dvd_or_dvd hdvd with h | h
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr ⟨hz, star_dvd_of_dvd_star h⟩
  have hinter : A ∩ B = {z | z ∈ normSet n ∧ (p : GaussianInt) ∣ z} := by
    ext z
    simp only [A, B, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hz, h1⟩, _, h2⟩
      exact ⟨hz, hmul ▸ hcop.mul_dvd h1 h2⟩
    · rintro ⟨hz, h⟩
      exact ⟨⟨hz, (dvd_mul_right π _).trans (hmul ▸ h)⟩, hz,
        (dvd_mul_left (star π) _).trans (hmul ▸ h)⟩
  have hfinA : A.Finite := (normSet_finite n).subset fun z hz => hz.1
  have hfinB : B.Finite := (normSet_finite n).subset fun z hz => hz.1
  have key := Set.ncard_union_add_ncard_inter A B hfinA hfinB
  rw [hunion, hinter, ncard_normSet_natCast_dvd hp.ne_zero, hA, hB] at key
  rw [key]; ring

/-! ### The same recursions for `δ` -/

lemma chi4DivisorSum_pow_mul {p : ℕ} (hp : p.Prime) (a : ℕ) {m : ℕ} (hm : ¬ p ∣ m) :
    chi4DivisorSum (p ^ a * m) = chi4LocalFactor p a * chi4DivisorSum m := by
  rw [chi4DivisorSum_eq_mul_zeta, chi4DivisorSum_eq_mul_zeta,
    isMultiplicative_chi4DivisorSum.map_mul_of_coprime
      (Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)),
    ← chi4DivisorSum_eq_mul_zeta, chi4DivisorSum_prime_pow_eq hp]

/-- Write `n = p^a m` with `p ∤ m`, `a ≥ 1`. -/
lemma exists_pow_mul_of_dvd {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) (hpn : p ∣ n) :
    ∃ a m, 1 ≤ a ∧ ¬ p ∣ m ∧ n = p ^ a * m := by
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  refine ⟨a, m, ?_, hm, rfl⟩
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp at hpn; exact absurd hpn hm
  · exact ha

lemma pow_mul_div_prime {p a m : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    p ^ a * m / p = p ^ (a - 1) * m := by
  rw [show p ^ a = p * p ^ (a - 1) by rw [← pow_succ']; congr 1; omega, mul_assoc,
    Nat.mul_div_cancel_left _ hp.pos]

lemma sq_dvd_pow_mul_iff {p a m : ℕ} (hp : p.Prime) (hm : ¬ p ∣ m) :
    p ^ 2 ∣ p ^ a * m ↔ 2 ≤ a := by
  constructor
  · intro h
    by_contra ha
    push Not at ha
    have : p ^ 2 ∣ p ^ a := (Nat.Coprime.dvd_of_dvd_mul_right
      (Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)) h)
    have := Nat.pow_dvd_pow_iff_le_right hp.one_lt |>.mp this
    omega
  · intro ha
    exact (Nat.pow_dvd_pow p ha).mul_right m

lemma pow_mul_div_prime_sq {p a m : ℕ} (hp : p.Prime) (ha : 2 ≤ a) :
    p ^ a * m / p ^ 2 = p ^ (a - 2) * m := by
  rw [show p ^ a = p ^ 2 * p ^ (a - 2) by rw [← pow_add]; congr 1; omega, mul_assoc,
    Nat.mul_div_cancel_left _ (pow_pos hp.pos 2)]

/-! ### Theorem 278 -/

lemma normSet_one : normSet 1 = {1, -1, ⟨0, 1⟩, ⟨0, -1⟩} := by
  ext ⟨x, y⟩
  simp only [normSet, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
    norm_eq_sq_add_sq, Nat.cast_one]
  simp only [Zsqrtd.ext_iff]
  simp only [Zsqrtd.re_one, Zsqrtd.im_one, Zsqrtd.re_neg, Zsqrtd.im_neg, neg_zero]
  constructor
  · intro h
    have hr1 : -1 ≤ x := by nlinarith [sq_nonneg y]
    have hr2 : x ≤ 1 := by nlinarith [sq_nonneg y]
    have hi1 : -1 ≤ y := by nlinarith [sq_nonneg x]
    have hi2 : y ≤ 1 := by nlinarith [sq_nonneg x]
    interval_cases x <;> interval_cases y <;> simp_all
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

lemma ncard_normSet_one : (normSet 1).ncard = 4 := by
  rw [normSet_one]
  rw [Set.ncard_insert_of_notMem (by decide), Set.ncard_insert_of_notMem (by decide),
    Set.ncard_pair (by decide)]

theorem ncard_normSet_eq {n : ℕ} (hn : 0 < n) : ((normSet n).ncard : ℤ) = 4 * chi4DivisorSum n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    rw [ncard_normSet_one]
    simp [chi4DivisorSum, chi4]
  set p := n.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpn : p ∣ n := Nat.minFac_dvd n
  obtain ⟨a, m, ha, hm, hnm⟩ := exists_pow_mul_of_dvd hp hn.ne' hpn
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hnm; omega)
  have hpa : 0 < p ^ a := pow_pos hp.pos a
  have hδn : chi4DivisorSum n = chi4LocalFactor p a * chi4DivisorSum m := by
    rw [hnm, chi4DivisorSum_pow_mul hp a hm]
  have hdiv1 : n / p = p ^ (a - 1) * m := by rw [hnm, pow_mul_div_prime hp ha]
  have hlt1 : n / p < n := Nat.div_lt_self hn hp.one_lt
  have hpos1 : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos
  have hδ1 : chi4DivisorSum (n / p) = chi4LocalFactor p (a - 1) * chi4DivisorSum m := by
    rw [hdiv1, chi4DivisorSum_pow_mul hp _ hm]
  have hsq : p ^ 2 ∣ n ↔ 2 ≤ a := by rw [hnm]; exact sq_dvd_pow_mul_iff hp hm
  have hcases : p = 2 ∨ p % 4 = 1 ∨ p % 4 = 3 := by
    rcases hp.eq_two_or_odd with h2 | hodd
    · exact Or.inl h2
    · right; omega
  rcases hcases with h2 | h1 | h3
  · -- `p = 2`
    have hn2 : 2 * (n / p) = n := by rw [h2] at hpn ⊢; exact Nat.mul_div_cancel' hpn
    have hr := ncard_normSet_two_mul (n / p)
    rw [hn2] at hr
    rw [hr, ih _ hlt1 hpos1, hδ1, hδn]
    simp [chi4LocalFactor, h2]
  · -- `p ≡ 1 (mod 4)`
    have hrec := ncard_normSet_of_mod_four_eq_one hp h1 hpn
    have hrec' : ((normSet n).ncard : ℤ) =
        2 * (normSet (n / p)).ncard - (if p ^ 2 ∣ n then ((normSet (n / p ^ 2)).ncard : ℤ) else 0) := by
      have := congrArg (fun k : ℕ => (k : ℤ)) hrec
      push_cast [apply_ite] at this
      split_ifs at this ⊢ <;> linarith
    rw [hrec', ih _ hlt1 hpos1, hδ1, hδn]
    have hloc : ∀ k, chi4LocalFactor p k = k + 1 := fun k => by simp [chi4LocalFactor, h1]
    split_ifs with hp2
    · have ha2 := hsq.mp hp2
      have hlt2 : n / p ^ 2 < n := Nat.div_lt_self hn (by nlinarith [hp.two_le])
      have hpos2 : 0 < n / p ^ 2 := Nat.div_pos (Nat.le_of_dvd hn hp2) (pow_pos hp.pos 2)
      rw [ih _ hlt2 hpos2, show n / p ^ 2 = p ^ (a - 2) * m by rw [hnm, pow_mul_div_prime_sq hp ha2],
        chi4DivisorSum_pow_mul hp _ hm, hloc, hloc, hloc]
      push_cast [Nat.cast_sub (by omega : 1 ≤ a), Nat.cast_sub ha2]
      ring
    · have ha1 : a = 1 := by have := hsq.not.mp hp2; omega
      rw [hloc, hloc, ha1]
      ring
  · -- `p ≡ 3 (mod 4)`
    rw [ncard_normSet_of_mod_four_eq_three hp h3 hpn, hδn]
    have hloc : ∀ k, chi4LocalFactor p k = if Even k then 1 else 0 := fun k => by
      simp [chi4LocalFactor, h3]
    split_ifs with hp2
    · have ha2 := hsq.mp hp2
      have hlt2 : n / p ^ 2 < n := Nat.div_lt_self hn (by nlinarith [hp.two_le])
      have hpos2 : 0 < n / p ^ 2 := Nat.div_pos (Nat.le_of_dvd hn hp2) (pow_pos hp.pos 2)
      rw [ih _ hlt2 hpos2, show n / p ^ 2 = p ^ (a - 2) * m by rw [hnm, pow_mul_div_prime_sq hp ha2],
        chi4DivisorSum_pow_mul hp _ hm, hloc, hloc]
      have : Even (a - 2) ↔ Even a := by
        obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
        simp [Nat.even_add]
      simp only [this]
    · have ha1 : a = 1 := by have := hsq.not.mp hp2; omega
      rw [hloc, ha1]
      simp

/-- `r(n)` (Hardy–Wright § 16.9): the number of representations `n = A² + B²`, `A, B ∈ ℤ`,
representations differing in sign or order counted as distinct. -/
noncomputable def sumTwoSquaresCount (n : ℕ) : ℕ := {x : ℤ × ℤ | x.1 ^ 2 + x.2 ^ 2 = n}.ncard

lemma sumTwoSquaresCount_eq_ncard_normSet (n : ℕ) :
    sumTwoSquaresCount n = (normSet n).ncard := by
  rw [sumTwoSquaresCount, ← Set.ncard_image_of_injective (normSet n)
    (f := fun z : GaussianInt => (z.re, z.im)) (fun z w h => by
      simp only [Prod.mk.injEq] at h; exact Zsqrtd.ext h.1 h.2)]
  congr 1
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, Set.mem_image, normSet, Prod.mk.injEq]
  constructor
  · intro h; exact ⟨⟨x, y⟩, by rw [norm_eq_sq_add_sq]; exact h, rfl, rfl⟩
  · rintro ⟨z, hz, rfl, rfl⟩; rw [← hz, norm_eq_sq_add_sq]

/-- **Theorem 278** (Jacobi; Hardy–Wright). For `n ≥ 1` (the book states `n > 1`),
`r(n) = 4 δ(n) = 4 (d₁(n) - d₃(n))`. -/
@[kb "hardywright2008" "Thm 278, p. 333"]
theorem sumTwoSquaresCount_eq {n : ℕ} (hn : 0 < n) :
    (sumTwoSquaresCount n : ℤ) = 4 * chi4DivisorSum n := by
  rw [sumTwoSquaresCount_eq_ncard_normSet, ncard_normSet_eq hn]

/-- **Theorem 278** (Hardy–Wright), with `δ(n) = d₁(n) - d₃(n)` written out. -/
@[kb "hardywright2008" "Thm 278, p. 333"]
theorem sumTwoSquaresCount_eq_card_sub_card {n : ℕ} (hn : 0 < n) :
    (sumTwoSquaresCount n : ℤ) =
      4 * (#(n.divisors.filter (· % 4 = 1)) - #(n.divisors.filter (· % 4 = 3)) : ℤ) := by
  rw [sumTwoSquaresCount_eq hn, chi4DivisorSum_eq_card_sub_card]

end NTKB.HardyWright
