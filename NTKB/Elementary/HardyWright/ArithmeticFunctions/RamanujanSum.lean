/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Aesop.BuiltinRules
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
import NTKB.Attr

/-!
# Hardy–Wright, § 16.6: Ramanujan's sum

Ramanujan's sum (Hardy–Wright (16.6.1), defined in § 5.6) is
`c_n(m) = ∑_{1 ≤ h ≤ n, (h,n) = 1} e(hm/n)`, `e(x) = exp(2πix)`. Mathlib has no Ramanujan sums.

* (16.2.3): `∑_{h=1}^n F(h/n) = ∑_{d ∣ n} ∑_{1 ≤ a ≤ d, (a,d)=1} F(a/d)`.
* Theorem 271: `c_n(m) = ∑_{d ∣ m, d ∣ n} μ(n/d) d`, by Möbius inversion of (16.2.3) with
  `F(x) = e(mx)` (the book's proof, suggested by van der Pol).
* (16.6.4): `c_n(1) = μ(n)`: the sum of the primitive `n`-th roots of unity is `μ(n)`.
* Theorem 272 (Hölder): if `(n, m) = a` and `n = aN`, then `c_n(m) = μ(N) φ(n)/φ(N)`.
-/

open Finset Complex ArithmeticFunction
open scoped Real ArithmeticFunction.Moebius

namespace NTKB.HardyWright

/-- **Ramanujan's sum** (Hardy–Wright (16.6.1)): `c_n(m) = ∑_{1 ≤ h ≤ n, (h,n)=1} e(hm/n)`. -/
noncomputable def ramanujanSumNat (n m : ℕ) : ℂ :=
  ∑ h ∈ Icc 1 n with h.Coprime n, cexp (2 * π * I * (h * m / n))


/-- **(16.2.3)** (Hardy–Wright, § 16.2). Each fraction `h/n` (`1 ≤ h ≤ n`) is, in exactly one way,
a reduced fraction `a/d` with `d ∣ n`, `1 ≤ a ≤ d`, `(a, d) = 1`; hence for any function `F`,
`∑_{h=1}^n F(h/n) = ∑_{d ∣ n} ∑_{1 ≤ a ≤ d, (a,d)=1} F(a/d)`. -/
@[kb "hardywright2008" "(16.2.3), p. 322"]
theorem sum_Icc_div_eq_sum_divisors {M : Type*} [AddCommMonoid M] (F : ℚ → M) {n : ℕ}
    (hn : n ≠ 0) :
    ∑ h ∈ Icc 1 n, F (h / n) = ∑ d ∈ n.divisors, ∑ a ∈ Icc 1 d with a.Coprime d, F (a / d) := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun h => n / Nat.gcd h n) (t := n.divisors)]
  swap
  · intro h _
    simp only [Nat.mem_divisors]
    exact ⟨Nat.div_dvd_of_dvd (Nat.gcd_dvd_right h n), hn⟩
  refine sum_congr rfl fun d hd => ?_
  have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  obtain ⟨g, hg⟩ := hdn
  have hg0 : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h | h
    · subst h; simp at hg; exact absurd hg hn
    · exact h
  have hng : n / d = g := by rw [hg]; exact Nat.mul_div_cancel_left g hd0
  -- in the fibre over `d`, `gcd(h, n) = g`
  have key : ∀ h, 0 < h → (n / Nat.gcd h n = d ↔ Nat.gcd h n = g) := by
    intro h hh
    have hpos : 0 < Nat.gcd h n := Nat.gcd_pos_of_pos_left n hh
    constructor
    · intro e
      have := Nat.mul_div_cancel' (Nat.gcd_dvd_right h n)
      rw [mul_comm, e] at this
      exact Nat.eq_of_mul_eq_mul_left hd0 (this.trans hg)
    · intro e
      rw [e, hg]; exact Nat.mul_div_cancel _ hg0
  apply Finset.sum_nbij' (fun h => h / g) (fun a => a * g)
  · intro h hh
    simp only [mem_filter, mem_Icc] at hh ⊢
    have e := (key h (by omega)).mp hh.2
    have hgh : g ∣ h := e ▸ Nat.gcd_dvd_left h n
    obtain ⟨b, rfl⟩ := hgh
    rw [Nat.mul_div_cancel_left b hg0]
    have hb : 0 < b := by rcases Nat.eq_zero_or_pos b with h | h <;> [simp [h] at hh; exact h]
    refine ⟨⟨hb, ?_⟩, ?_⟩
    · have := hh.1.2
      rw [hg, mul_comm d g] at this
      exact Nat.le_of_mul_le_mul_left this hg0
    · have := Nat.coprime_div_gcd_div_gcd (m := g * b) (n := n) (by rw [e]; exact hg0)
      rw [e, Nat.mul_div_cancel_left b hg0, hg, Nat.mul_div_cancel _ hg0] at this
      exact this
  · intro a ha
    simp only [mem_filter, mem_Icc] at ha ⊢
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact Nat.mul_pos ha.1.1 hg0
    · rw [hg, mul_comm d g, mul_comm a g]; exact Nat.mul_le_mul_left g ha.1.2
    · rw [key _ (Nat.mul_pos ha.1.1 hg0), hg, mul_comm d g, mul_comm a g, Nat.gcd_mul_left,
        Nat.Coprime.gcd_eq_one ha.2, mul_one]
  · intro h hh
    simp only [mem_filter, mem_Icc] at hh
    have e := (key h (by omega)).mp hh.2
    exact Nat.div_mul_cancel (e ▸ Nat.gcd_dvd_left h n)
  · intro a _
    exact Nat.mul_div_cancel a hg0
  · intro h hh
    simp only [mem_filter, mem_Icc] at hh
    have e := (key h (by omega)).mp hh.2
    obtain ⟨b, rfl⟩ : g ∣ h := e ▸ Nat.gcd_dvd_left h n
    rw [Nat.mul_div_cancel_left b hg0, hg]
    congr 1
    push_cast
    have : (g : ℚ) ≠ 0 := by exact_mod_cast hg0.ne'
    field_simp

/-- `∑_{h=1}^d e(hm/d)` is `d` if `d ∣ m` and `0` otherwise. -/
theorem sum_Icc_exp_eq (d m : ℕ) (hd : 0 < d) :
    ∑ h ∈ Icc 1 d, cexp (2 * π * I * (m * ((h : ℚ) / d : ℚ))) = if d ∣ m then (d : ℂ) else 0 := by
  set ζ := cexp (2 * π * I * (m / d)) with hζ
  have hpow : ∀ h : ℕ, cexp (2 * π * I * (m * ((h : ℚ) / d : ℚ))) = ζ ^ h := by
    intro h
    rw [hζ, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp_rw [hpow]
  have hζd : ζ ^ d = 1 := by
    rw [hζ, ← Complex.exp_nat_mul]
    have : (d : ℂ) * (2 * π * I * (m / d)) = (m : ℕ) * (2 * π * I) := by
      have : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
      field_simp
    rw [this]
    exact Complex.exp_nat_mul_two_pi_mul_I m
  split_ifs with hdm
  · obtain ⟨k, rfl⟩ := hdm
    have : ζ = 1 := by
      rw [hζ]
      have : (2 * π * I * ((d * k : ℕ) / d : ℂ)) = (k : ℕ) * (2 * π * I) := by
        have : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
        push_cast
        field_simp
      rw [this]
      exact Complex.exp_nat_mul_two_pi_mul_I k
    simp [this]
  · have hζ1 : ζ ≠ 1 := by
      intro h1
      rw [hζ, Complex.exp_eq_one_iff] at h1
      obtain ⟨k, hk⟩ := h1
      apply hdm
      have h0 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
      have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
      have h2 : (m : ℂ) = k * d := by
        have : (m : ℂ) / d = k := by
          apply mul_left_cancel₀ h0
          rw [hk]; ring
        field_simp at this
        rw [this]; ring
      have h3 : (m : ℤ) = k * d := by exact_mod_cast h2
      exact Int.natCast_dvd_natCast.mp ⟨k, by rw [h3]; ring⟩
    have : ∑ h ∈ Icc 1 d, ζ ^ h = ζ * ∑ h ∈ range d, ζ ^ h := by
      rw [Finset.mul_sum, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr (by simp) fun h _ => by ring
    rw [this, geom_sum_eq hζ1, hζd]
    simp

/-- **Theorem 271** (Hardy–Wright). `c_n(m) = ∑_{d ∣ m, d ∣ n} μ(n/d) d`. -/
@[kb "hardywright2008" "Thm 271, p. 327"]
theorem ramanujanSum_eq_sum (n m : ℕ) (hn : 0 < n) :
    ramanujanSumNat n m = ∑ d ∈ n.divisors with d ∣ m, (μ (n / d) : ℂ) * d := by
  set F : ℚ → ℂ := fun q => cexp (2 * π * I * (m * (q : ℚ))) with hF
  have hf : ∀ d : ℕ, ∑ a ∈ Icc 1 d with a.Coprime d, F ((a : ℚ) / d) = ramanujanSumNat d m := by
    intro d
    refine sum_congr rfl fun a _ => ?_
    simp only [hF]
    congr 1
    push_cast
    ring
  have hinv := (sum_eq_iff_sum_mul_moebius_eq (R := ℂ) (f := fun d => ramanujanSumNat d m)
    (g := fun d => ∑ h ∈ Icc 1 d, F ((h : ℚ) / d))).mp (fun d hd => by
      rw [sum_Icc_div_eq_sum_divisors F hd.ne']
      exact sum_congr rfl fun e _ => (hf e).symm) n hn
  rw [← hinv, Nat.sum_divisorsAntidiagonal' (fun a b => (μ a : ℂ) *
    ∑ h ∈ Icc 1 b, F ((h : ℚ) / b)), sum_filter]
  refine sum_congr rfl fun d hd => ?_
  rw [sum_Icc_exp_eq d m (Nat.pos_of_mem_divisors hd)]
  split_ifs <;> simp

/-- **(16.6.4)** (Hardy–Wright). `c_n(1) = μ(n)`: the sum of the primitive `n`-th roots of unity
`e(h/n)`, `1 ≤ h ≤ n`, `(h, n) = 1`, is `μ(n)`. -/
@[kb "hardywright2008" "(16.6.4), p. 329"]
theorem ramanujanSum_one (n : ℕ) (hn : 0 < n) : ramanujanSumNat n 1 = μ n := by
  rw [ramanujanSum_eq_sum n 1 hn]
  have : n.divisors.filter (· ∣ 1) = {1} := by
    ext d
    simp only [mem_filter, Nat.mem_divisors, Nat.dvd_one, mem_singleton]
    constructor
    · exact fun h => h.2
    · rintro rfl; exact ⟨⟨one_dvd n, hn.ne'⟩, rfl⟩
  rw [this, sum_singleton, Nat.div_one, Nat.cast_one, mul_one]

/-- The completely multiplicative function `c ↦ 1/c` if `(c, N) = 1`, `0` otherwise. -/
private noncomputable def invCoprime (N : ℕ) : ArithmeticFunction ℚ :=
  ⟨fun c => if c.Coprime N then (c : ℚ)⁻¹ else 0, by simp⟩

private lemma invCoprime_apply (N c : ℕ) :
    invCoprime N c = if c.Coprime N then (c : ℚ)⁻¹ else 0 := rfl

private lemma isMultiplicative_invCoprime (N : ℕ) : (invCoprime N).IsMultiplicative := by
  refine ⟨by simp [invCoprime_apply], fun {b c} _ => ?_⟩
  simp only [invCoprime_apply, Nat.coprime_mul_iff_left]
  by_cases hb : b.Coprime N <;> by_cases hc : c.Coprime N
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hb, hc⟩), ite_eq_left_of_eq_true _ _ (eq_true hb),
      ite_eq_left_of_eq_true _ _ (eq_true hc)]
    push_cast; ring
  · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hc h.2), ite_eq_right_of_eq_false _ _ (eq_false hc),
      mul_zero]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hb h.1), ite_eq_right_of_eq_false _ _ (eq_false hb),
      zero_mul]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hb h.1), ite_eq_right_of_eq_false _ _ (eq_false hb),
      zero_mul]

/-- **Theorem 272** (Hölder; Hardy–Wright). If `(n, m) = a` and `n = aN`, then
`c_n(m) = μ(N) φ(n) / φ(N)`. -/
@[kb "hardywright2008" "Thm 272, p. 328"]
theorem ramanujanSum_eq_moebius_mul_totient_div {n m a N : ℕ} (hn : 0 < n)
    (ha : Nat.gcd n m = a) (hN : n = a * N) :
    ramanujanSumNat n m = μ N * (n.totient : ℂ) / N.totient := by
  have ha0 : a ≠ 0 := by rintro rfl; simp at hN; omega
  have hN0 : N ≠ 0 := by rintro rfl; simp at hN; omega
  -- Step 1: the common divisors of `m` and `n` are the divisors of `a`
  have h1 : n.divisors.filter (· ∣ m) = a.divisors := by
    ext d
    simp only [mem_filter, Nat.mem_divisors, ← ha, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h3⟩, Nat.gcd_ne_zero_left h2⟩
    · rintro ⟨⟨h1, h3⟩, _⟩; exact ⟨⟨h1, hn.ne'⟩, h3⟩
  -- Step 2: the sum over `d ∣ a` as a sum over `c = a/d`, with `n/d = Nc`
  have h2 : ∑ d ∈ a.divisors, (μ (n / d) : ℚ) * d =
      ∑ c ∈ a.divisors, (μ (N * c) : ℚ) * (a / c : ℕ) := by
    rw [← Nat.sum_div_divisors a]
    refine sum_congr rfl fun c hc => ?_
    obtain ⟨e, he⟩ := Nat.dvd_of_mem_divisors hc
    have hc0 : 0 < c := Nat.pos_of_mem_divisors hc
    have : n / (a / c) = N * c := by
      rw [he, Nat.mul_div_cancel_left e hc0, hN, he]
      rw [show c * e * N = e * (N * c) by ring, Nat.mul_div_cancel_left _
        (Nat.pos_of_ne_zero (by rintro rfl; simp at he; exact ha0 he))]
    rw [this]
  -- Step 3: `μ(Nc) = μ(N) μ(c)` or `0` according as `(N, c) = 1` or not
  have h3 : ∀ c ∈ a.divisors, (μ (N * c) : ℚ) * (a / c : ℕ) =
      μ N * a * ((μ c : ℚ) * invCoprime N c) := by
    intro c hc
    have hca : c ∣ a := Nat.dvd_of_mem_divisors hc
    have hc0 : (c : ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hc).ne'
    rw [invCoprime_apply, Nat.cast_div hca hc0]
    by_cases hcop : c.Coprime N
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hcop)]
      rw [isMultiplicative_moebius.map_mul_of_coprime hcop.symm]
      push_cast
      field_simp
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hcop)]
      rw [moebius_eq_zero_of_not_squarefree]
      · simp
      · rw [Nat.squarefree_mul_iff]
        exact fun h => hcop h.1.symm
  -- Step 4: `∑_{c ∣ a} μ(c) f(c) = ∏_{p ∣ a} (1 - f(p))`
  have h4 := IsMultiplicative.prodPrimeFactors_one_sub (invCoprime N) (isMultiplicative_invCoprime N) ha0
  -- Step 5: Euler's product for `φ(n)` and `φ(N)`
  have hpf : n.primeFactors = N.primeFactors ∪ a.primeFactors.filter (fun p => ¬ p ∣ N) := by
    rw [hN, Nat.primeFactors_mul ha0 hN0]
    ext p
    simp only [mem_union, mem_filter, Nat.mem_primeFactors]
    tauto
  have hdisj : Disjoint N.primeFactors (a.primeFactors.filter (fun p => ¬ p ∣ N)) := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    simp only [mem_filter, Nat.mem_primeFactors] at hp hp'
    exact hp'.2 hp.2.1
  have hφn := Nat.totient_eq_mul_prod_factors n
  have hφN := Nat.totient_eq_mul_prod_factors N
  rw [hpf, prod_union hdisj] at hφn
  have h5 : ∏ p ∈ a.primeFactors, (1 - invCoprime N p) =
      ∏ p ∈ a.primeFactors.filter (fun p => ¬ p ∣ N), (1 - (p : ℚ)⁻¹) := by
    rw [prod_filter]
    refine prod_congr rfl fun p hp => ?_
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hc : p.Coprime N ↔ ¬ p ∣ N := hp'.coprime_iff_not_dvd
    rw [invCoprime_apply]
    by_cases hd : p ∣ N
    · have : ¬ p.Coprime N := by rw [hc, not_not]; exact hd
      simp [this, hd]
    · simp [hc.mpr hd, hd]
  have hQ : ∏ p ∈ N.primeFactors, (1 - (p : ℚ)⁻¹) ≠ 0 := by
    rw [prod_ne_zero_iff]
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    have : (p : ℚ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast this)
    linarith
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN0
  -- conclusion, in `ℚ`
  have key : (∑ d ∈ a.divisors, (μ (n / d) : ℚ) * d) = μ N * (n.totient : ℚ) / N.totient := by
    rw [h2, sum_congr rfl h3, ← mul_sum, ← h4, h5, hφn, hφN, hN]
    push_cast
    have hQ' : ∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ)) ≠ 0 := by simpa [one_div] using hQ
    field_simp
  rw [ramanujanSum_eq_sum n m hn, h1]
  have := congrArg (fun q : ℚ => (q : ℂ)) key
  push_cast at this
  exact this

end NTKB.HardyWright
