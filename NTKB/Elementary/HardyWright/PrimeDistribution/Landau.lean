/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.PrimeDistribution.Mertens
import NTKB.Elementary.HardyWright.PrimeDistribution.Elementary
import NTKB.Analytic.Apostol.ArithmeticFunctions.Derivative
import NTKB.Analytic.Apostol.ArithmeticFunctions.GeneralizedConvolution
import NTKB.Analytic.Apostol.Primes.ChebyshevForms
import Mathlib.NumberTheory.AlmostPrime

/-!
# Hardy–Wright, § 22.18: products of `k` prime factors (Landau's theorem)

[hardywright2008, § 22.18, Theorem 437]. Let `τ_k(x)` be the number of `n ≤ x` with `Ω(n) = k`
and `π_k(x)` the number of squarefree `n ≤ x` with `ω(n) = k`. For `k ≥ 2`,
`π_k(x) ~ τ_k(x) ~ x (log log x)^(k-1) / ((k-1)! log x)`.

We follow the book. The number `c_k(n)` of ordered representations `n = p₁ ⋯ p_k` is the
Dirichlet power `P^k` of the indicator `P` of the primes, and
`Π_k(x) = ∑_{n ≤ x} c_k(n)`, `ϑ_k(x) = ∑_{n ≤ x} c_k(n) log n`, `L_k(x) = ∑_{n ≤ x} c_k(n)/n`.

* (22.18.2) `k! π_k(x) ≤ Π_k(x) ≤ k! τ_k(x)`; (22.18.3) `τ_k(x) - π_k(x) ≤ Π_{k-1}(x)`;
* the identities `k ϑ_{k+1}(x) = (k+1) ∑_{p ≤ x} ϑ_k(x/p)` (from the derivation
  `(f * g)' = f' * g + f * g'`, Apostol's Theorem 2.26) and `L_k(x) = ∑_{p ≤ x} L_{k-1}(x/p)/p`;
* (22.18.6) and the induction (22.18.7) `ϑ_k(x) - k x L_{k-1}(x) = o(x (log log x)^(k-1))`,
  with Theorem 427 and the prime number theorem (Theorem 434, proved elementarily in
  `ElementaryPNT`) at `k = 1`;
* (22.18.8) `L_k(x) ~ (log log x)^k`, from
  `(∑_{p ≤ x^(1/k)} 1/p)^k ≤ L_k(x) ≤ (∑_{p ≤ x} 1/p)^k`;
* (22.18.4) `ϑ_k(x) ~ k x (log log x)^(k-1)` and (22.18.5) `Π_k(x) ~ ϑ_k(x) / log x`.
  For (22.18.5) the book uses partial summation; we use directly
  `Π_k(x) log x - ϑ_k(x) = ∑_{n ≤ x} c_k(n) log(x/n) ≤ k! ∑_{n ≤ x} log (x/n) = O(x)`
  (Theorem 423 with `h = 1`).
-/

open Finset ArithmeticFunction Filter Chebyshev
open scoped Topology ArithmeticFunction.omega ArithmeticFunction.Omega

namespace NTKB.HardyWright

namespace Landau

open NTKB.Apostol (arithDeriv arithDeriv_mul arithDeriv_one arithDeriv_apply
  sum_Ioc_sum_divisorsAntidiagonal)

/-! ### The arithmetic functions `P` and `c_k = P^k` -/

/-- The indicator function of the primes. -/
noncomputable def primeInd : ArithmeticFunction ℝ :=
  ⟨fun n ↦ if n.Prime then 1 else 0, by simp [Nat.not_prime_zero]⟩

lemma primeInd_apply (n : ℕ) : primeInd n = if n.Prime then 1 else 0 := rfl

/-- `c k n` is the number of ordered `k`-tuples of primes with product `n`. -/
noncomputable def c (k : ℕ) : ArithmeticFunction ℝ := primeInd ^ k

lemma rsmul_apply (r : ℝ) (f : ArithmeticFunction ℝ) (n : ℕ) : (r • f) n = r * f n := rfl

lemma mul_rsmul (f g : ArithmeticFunction ℝ) (r : ℝ) : f * (r • g) = r • (f * g) := by
  ext n
  simp only [ArithmeticFunction.mul_apply, rsmul_apply, Finset.mul_sum]
  exact sum_congr rfl fun _ _ ↦ by ring

lemma primeInd_mul_apply (f : ArithmeticFunction ℝ) (n : ℕ) :
    (primeInd * f) n = ∑ p ∈ n.primeFactors, f (n / p) := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b ↦ primeInd a * f b)]
  simp only [primeInd_apply, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  congr 1
  ext p
  simp only [mem_filter, Nat.mem_divisors, Nat.mem_primeFactors]
  tauto

lemma c_zero : c 0 = 1 := pow_zero _

lemma c_succ (k : ℕ) : c (k + 1) = primeInd * c k := pow_succ' _ _

lemma c_one : c 1 = primeInd := pow_one _

lemma c_succ_apply (k n : ℕ) : c (k + 1) n = ∑ p ∈ n.primeFactors, c k (n / p) := by
  rw [c_succ, primeInd_mul_apply]

lemma c_nonneg (k n : ℕ) : 0 ≤ c k n := by
  induction k generalizing n with
  | zero => rw [c_zero, ArithmeticFunction.one_apply]; split_ifs <;> norm_num
  | succ k ih => rw [c_succ_apply]; exact sum_nonneg fun p _ ↦ ih _

lemma div_ne_zero_of_mem_primeFactors {n p : ℕ} (hp : p ∈ n.primeFactors) : n / p ≠ 0 := by
  obtain ⟨hp, hpn, hn⟩ := Nat.mem_primeFactors.1 hp
  exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpn) hp.pos).ne'

lemma cardFactors_div_add_one {n p : ℕ} (hp : p ∈ n.primeFactors) : Ω (n / p) + 1 = Ω n := by
  have h0 := div_ne_zero_of_mem_primeFactors hp
  obtain ⟨hp, hpn, -⟩ := Nat.mem_primeFactors.1 hp
  conv_rhs => rw [← Nat.div_mul_cancel hpn]
  rw [cardFactors_mul h0 hp.ne_zero, cardFactors_apply_prime hp]

lemma c_ne_zero {k n : ℕ} (h : c k n ≠ 0) : n ≠ 0 ∧ Ω n = k := by
  induction k generalizing n with
  | zero =>
    rw [c_zero, ArithmeticFunction.one_apply] at h
    split_ifs at h with h1
    · subst h1; simp
    · exact absurd rfl h
  | succ k ih =>
    rw [c_succ_apply] at h
    obtain ⟨p, hp, hpk⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    obtain ⟨-, hΩ⟩ := ih hpk
    exact ⟨(Nat.mem_primeFactors.1 hp).2.2, by rw [← cardFactors_div_add_one hp, hΩ]⟩

lemma c_le_factorial (k n : ℕ) : c k n ≤ k.factorial := by
  induction k generalizing n with
  | zero => rw [c_zero, ArithmeticFunction.one_apply]; split_ifs <;> norm_num
  | succ k ih =>
    by_cases h : c (k + 1) n = 0
    · rw [h]; positivity
    obtain ⟨-, hΩ⟩ := c_ne_zero h
    rw [c_succ_apply]
    calc ∑ p ∈ n.primeFactors, c k (n / p) ≤ ∑ p ∈ n.primeFactors, (k.factorial : ℝ) :=
          sum_le_sum fun p _ ↦ ih _
      _ = (n.primeFactors.card : ℝ) * k.factorial := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ((k + 1 : ℕ) : ℝ) * k.factorial := by
          gcongr
          rw [← hΩ, cardFactors_apply]
          exact List.toFinset_card_le _
      _ = (k + 1).factorial := by push_cast [Nat.factorial_succ]; ring

lemma one_le_c {k n : ℕ} (hn : n ≠ 0) (hΩ : Ω n = k) : 1 ≤ c k n := by
  induction k generalizing n with
  | zero =>
    have : n = 1 := by
      rcases cardFactors_eq_zero_iff_eq_zero_or_one.1 hΩ with h | h
      · exact absurd h hn
      · exact h
    subst this; simp [c_zero]
  | succ k ih =>
    have hn1 : n ≠ 1 := by rintro rfl; simp at hΩ
    obtain ⟨p, hp⟩ : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.2 (by omega)
    rw [c_succ_apply]
    calc (1 : ℝ) ≤ c k (n / p) :=
          ih (div_ne_zero_of_mem_primeFactors hp)
            (by have := cardFactors_div_add_one hp; omega)
      _ ≤ _ := single_le_sum (fun q _ ↦ c_nonneg k (n / q)) hp

lemma c_eq_factorial {k n : ℕ} (hsq : Squarefree n) (hΩ : Ω n = k) : c k n = k.factorial := by
  induction k generalizing n with
  | zero =>
    have : n = 1 := by
      rcases cardFactors_eq_zero_iff_eq_zero_or_one.1 hΩ with h | h
      · exact absurd h hsq.ne_zero
      · exact h
    subst this; simp [c_zero]
  | succ k ih =>
    have hn : n ≠ 0 := hsq.ne_zero
    rw [c_succ_apply, sum_congr rfl fun p hp ↦ ih (Squarefree.squarefree_of_dvd
      (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp)) hsq)
      (by have := cardFactors_div_add_one hp; omega)]
    rw [sum_const, nsmul_eq_mul, ← cardDistinctFactors_eq_card_primeFactors,
      (cardDistinctFactors_eq_cardFactors_iff_squarefree hn).2 hsq, hΩ]
    push_cast [Nat.factorial_succ]
    ring

lemma card_primeFactors_le_c {k n : ℕ} (hΩ : Ω n = k + 1) :
    (n.primeFactors.card : ℝ) ≤ c (k + 1) n := by
  rw [c_succ_apply, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  exact sum_le_sum fun p hp ↦ one_le_c (div_ne_zero_of_mem_primeFactors hp)
    (by have := cardFactors_div_add_one hp; omega)

/-! ### Summatory functions -/

/-- `Π_k(x) = ∑_{n ≤ x} c_k(n)`. -/
noncomputable def bigPi (k : ℕ) (x : ℝ) : ℝ := ∑ n ∈ Ioc 0 ⌊x⌋₊, c k n

/-- `ϑ_k(x) = ∑_{n ≤ x} c_k(n) log n`. -/
noncomputable def bigTheta (k : ℕ) (x : ℝ) : ℝ := ∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log n * c k n

/-- `L_k(x) = ∑_{n ≤ x} c_k(n) / n`. -/
noncomputable def bigL (k : ℕ) (x : ℝ) : ℝ := ∑ n ∈ Ioc 0 ⌊x⌋₊, c k n * (n : ℝ)⁻¹

/-- `S(x) = ∑_{p ≤ x} 1/p`. -/
noncomputable def primeRecip (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (p : ℝ)⁻¹

lemma sum_mul_weight (f g : ArithmeticFunction ℝ) (w : ℕ → ℝ) (x : ℝ) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, (f * g) n * w n =
      ∑ a ∈ Ioc 0 ⌊x⌋₊, ∑ b ∈ Ioc 0 ⌊x / a⌋₊, f a * g b * w (a * b) := by
  calc ∑ n ∈ Ioc 0 ⌊x⌋₊, (f * g) n * w n
      = ∑ n ∈ Ioc 0 ⌊x⌋₊, ∑ ab ∈ n.divisorsAntidiagonal, f ab.1 * g ab.2 * w (ab.1 * ab.2) := by
        refine sum_congr rfl fun n _ ↦ ?_
        rw [ArithmeticFunction.mul_apply, sum_mul]
        refine sum_congr rfl fun ab hab ↦ ?_
        rw [(Nat.mem_divisorsAntidiagonal.1 hab).1]
    _ = ∑ a ∈ Ioc 0 ⌊x⌋₊, ∑ b ∈ Ioc 0 (⌊x⌋₊ / a), f a * g b * w (a * b) :=
        sum_Ioc_sum_divisorsAntidiagonal (fun a b ↦ f a * g b * w (a * b)) ⌊x⌋₊
    _ = _ := by simp_rw [Nat.floor_div_natCast]

lemma sum_primeInd_mul_weight (g : ArithmeticFunction ℝ) (w : ℕ → ℝ) (x : ℝ) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, (primeInd * g) n * w n =
      ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, ∑ b ∈ Ioc 0 ⌊x / p⌋₊, g b * w (p * b) := by
  rw [sum_mul_weight, sum_filter]
  refine sum_congr rfl fun a _ ↦ ?_
  simp only [primeInd_apply]
  split_ifs <;> simp

lemma bigPi_succ (k : ℕ) (x : ℝ) :
    bigPi (k + 1) x = ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, bigPi k (x / p) := by
  have h := sum_primeInd_mul_weight (c k) (fun _ ↦ 1) x
  simp only [mul_one] at h
  rw [bigPi, c_succ, h]
  rfl

lemma bigL_succ (k : ℕ) (x : ℝ) :
    bigL (k + 1) x = ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, bigL k (x / p) * (p : ℝ)⁻¹ := by
  rw [bigL, c_succ, sum_primeInd_mul_weight]
  refine sum_congr rfl fun p _ ↦ ?_
  rw [bigL, sum_mul]
  refine sum_congr rfl fun b _ ↦ ?_
  push_cast
  rw [mul_inv]
  ring

lemma deriv_c_succ (k : ℕ) :
    arithDeriv (c (k + 1)) = ((k : ℝ) + 1) • (arithDeriv primeInd * c k) := by
  induction k with
  | zero => simp [c_succ, c_zero]
  | succ k ih =>
    rw [c_succ (k + 1), arithDeriv_mul, ih, mul_rsmul, mul_left_comm, ← c_succ, Nat.cast_succ]
    module

lemma deriv_identity (k : ℕ) :
    (k : ℝ) • arithDeriv (c (k + 1)) = ((k : ℝ) + 1) • (primeInd * arithDeriv (c k)) := by
  cases k with
  | zero => simp [c_zero, arithDeriv_one]
  | succ j =>
    rw [deriv_c_succ (j + 1), deriv_c_succ j, mul_rsmul, mul_left_comm, ← c_succ,
      smul_smul, smul_smul]
    congr 1
    push_cast
    ring

lemma bigTheta_succ (k : ℕ) (x : ℝ) :
    (k : ℝ) * bigTheta (k + 1) x =
      ((k : ℝ) + 1) * ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, bigTheta k (x / p) := by
  have h := congrArg (fun F : ArithmeticFunction ℝ ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, F n) (deriv_identity k)
  simp only [rsmul_apply, ← mul_sum] at h
  have h2 := sum_primeInd_mul_weight (arithDeriv (c k)) (fun _ ↦ 1) x
  simp only [mul_one, arithDeriv_apply, smul_eq_mul] at h2
  rw [h2] at h
  simp only [arithDeriv_apply, smul_eq_mul] at h
  exact h

lemma bigTheta_one (x : ℝ) : bigTheta 1 x = θ x := by
  rw [theta, sum_filter, bigTheta, c_one]
  refine sum_congr rfl fun n _ ↦ ?_
  simp [primeInd_apply]

lemma bigL_zero {x : ℝ} (hx : 1 ≤ x) : bigL 0 x = 1 := by
  have h1 : 1 ∈ Ioc 0 ⌊x⌋₊ := by
    simp only [mem_Ioc, zero_lt_one, true_and]
    exact Nat.one_le_floor_iff _ |>.2 hx
  rw [bigL, sum_eq_single 1]
  · simp [c_zero]
  · intro b _ hb; simp [c_zero, ArithmeticFunction.one_apply_ne hb]
  · intro h; exact absurd h1 h

lemma bigL_zero_le (x : ℝ) : bigL 0 x ≤ 1 := by
  rcases le_or_gt 1 x with hx | hx
  · rw [bigL_zero hx]
  · have : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.2 hx
    simp [bigL, this]

lemma bigPi_one (x : ℝ) : bigPi 1 x = Nat.primeCounting ⌊x⌋₊ := by
  rw [← Nat.primesLE_card_eq_primeCounting, bigPi, c_one]
  simp only [primeInd_apply]
  rw [sum_boole]
  congr 2
  ext p
  simp only [mem_filter, mem_Ioc, Nat.primesLE, Nat.primesBelow, mem_range]
  constructor
  · rintro ⟨⟨-, h⟩, hp⟩; exact ⟨by omega, hp⟩
  · rintro ⟨h, hp⟩; exact ⟨⟨hp.pos, by omega⟩, hp⟩

lemma bigTheta_nonneg (k : ℕ) (x : ℝ) : 0 ≤ bigTheta k x :=
  sum_nonneg fun n _ ↦ mul_nonneg (Real.log_natCast_nonneg n) (c_nonneg k n)

lemma bigL_nonneg (k : ℕ) (x : ℝ) : 0 ≤ bigL k x :=
  sum_nonneg fun n _ ↦ mul_nonneg (c_nonneg k n) (by positivity)

lemma bigPi_nonneg (k : ℕ) (x : ℝ) : 0 ≤ bigPi k x :=
  sum_nonneg fun n _ ↦ c_nonneg k n

lemma primeRecip_nonneg (x : ℝ) : 0 ≤ primeRecip x :=
  sum_nonneg fun n _ ↦ by positivity

lemma floor_mono_Ioc {x y : ℝ} (h : x ≤ y) : Ioc 0 ⌊x⌋₊ ⊆ Ioc 0 ⌊y⌋₊ :=
  Ioc_subset_Ioc_right (Nat.floor_mono h)

lemma bigTheta_mono (k : ℕ) {x y : ℝ} (h : x ≤ y) : bigTheta k x ≤ bigTheta k y :=
  sum_le_sum_of_subset_of_nonneg (floor_mono_Ioc h) fun n _ _ ↦
    mul_nonneg (Real.log_natCast_nonneg n) (c_nonneg k n)

lemma bigL_mono (k : ℕ) {x y : ℝ} (h : x ≤ y) : bigL k x ≤ bigL k y :=
  sum_le_sum_of_subset_of_nonneg (floor_mono_Ioc h) fun n _ _ ↦
    mul_nonneg (c_nonneg k n) (by positivity)

lemma primeRecip_mono {x y : ℝ} (h : x ≤ y) : primeRecip x ≤ primeRecip y :=
  sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (floor_mono_Ioc h)) fun n _ _ ↦
    by positivity

lemma one_le_of_mem {x : ℝ} {p : ℕ} (hp : p ∈ Ioc 0 ⌊x⌋₊) : (1 : ℝ) ≤ p ∧ (p : ℝ) ≤ x := by
  have h := mem_Ioc.1 hp
  have hx : 0 ≤ x := by
    by_contra hx
    have : ⌊x⌋₊ = 0 := Nat.floor_of_nonpos (by linarith)
    omega
  exact ⟨by exact_mod_cast h.1, (Nat.cast_le.2 h.2).trans (Nat.floor_le hx)⟩

/-! ### (22.18.8): `L_k(x) ~ (log log x)^k` -/

lemma bigL_le (k : ℕ) (x : ℝ) : bigL k x ≤ primeRecip x ^ k := by
  induction k generalizing x with
  | zero => simpa using bigL_zero_le x
  | succ k ih =>
    rw [bigL_succ, pow_succ, primeRecip, mul_sum]
    refine sum_le_sum fun p hp ↦ ?_
    have hp' := one_le_of_mem (mem_filter.1 hp).1
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    refine (ih _).trans ?_
    refine pow_le_pow_left₀ (primeRecip_nonneg _) (primeRecip_mono ?_) k
    exact div_le_self (by linarith) hp'.1

lemma le_bigL (k : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    primeRecip (x ^ ((1 : ℝ) / (k + 1))) ^ (k + 1) ≤ bigL (k + 1) x := by
  induction k generalizing x with
  | zero =>
    simp only [Nat.cast_zero, zero_add, div_one, Real.rpow_one, pow_one]
    rw [bigL_succ, primeRecip]
    refine le_of_eq (sum_congr rfl fun p hp ↦ ?_)
    have hp' := one_le_of_mem (mem_filter.1 hp).1
    rw [bigL_zero ((one_le_div (by linarith)).2 hp'.2), one_mul]
  | succ k ih =>
    set y := x ^ ((1 : ℝ) / ((k + 1 : ℕ) + 1)) with hy
    have hx0 : 0 < x := by linarith
    have hyx : y ≤ x := by
      calc y ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by
              rw [div_le_one (by positivity)]; push_cast; linarith)
        _ = x := Real.rpow_one x
    rw [bigL_succ, pow_succ, primeRecip, mul_sum]
    calc ∑ p ∈ Ioc 0 ⌊y⌋₊ with p.Prime, primeRecip y ^ (k + 1) * (p : ℝ)⁻¹
        ≤ ∑ p ∈ Ioc 0 ⌊y⌋₊ with p.Prime, bigL (k + 1) (x / p) * (p : ℝ)⁻¹ := by
          refine sum_le_sum fun p hp ↦ ?_
          have hp' := one_le_of_mem (mem_filter.1 hp).1
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have hxp : 1 ≤ x / p := (one_le_div (by linarith)).2 (hp'.2.trans hyx)
          refine le_trans ?_ (ih hxp)
          refine pow_le_pow_left₀ (primeRecip_nonneg _) (primeRecip_mono ?_) _
          -- `y ≤ (x / p)^(1/(k+1))` because `p ≤ y`
          have hp0 : (0 : ℝ) < p := by linarith [hp'.1]
          calc y = (x / y) ^ ((1 : ℝ) / (k + 1)) := by
                rw [hy, ← Real.rpow_one_sub' hx0.le, ← Real.rpow_mul hx0.le]
                · congr 1; push_cast; field_simp; ring
                · push_cast
                  have : (1 : ℝ) / ((k : ℝ) + 1 + 1) < 1 := by
                    rw [div_lt_one (by positivity)]; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
                  linarith
            _ ≤ (x / p) ^ ((1 : ℝ) / (k + 1)) := by
                refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
                exact div_le_div_of_nonneg_left hx0.le hp0 hp'.2
      _ ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, bigL (k + 1) (x / p) * (p : ℝ)⁻¹ :=
          sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (floor_mono_Ioc hyx))
            fun p _ _ ↦ mul_nonneg (bigL_nonneg _ _) (by positivity)

lemma tendsto_loglog : Tendsto (fun x : ℝ ↦ Real.log (Real.log x)) atTop atTop :=
  Real.tendsto_log_atTop.comp Real.tendsto_log_atTop

lemma tendsto_div_loglog {F : ℝ → ℝ} {B : ℝ}
    (h : Tendsto (fun x ↦ F x - Real.log (Real.log x) - B) atTop (𝓝 0)) :
    Tendsto (fun x ↦ F x / Real.log (Real.log x)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun x ↦ (F x - Real.log (Real.log x) - B + B) / Real.log (Real.log x))
      atTop (𝓝 0) := (h.add_const B).div_atTop tendsto_loglog
  have h2 := h1.add_const 1
  rw [zero_add] at h2
  refine h2.congr' ?_
  filter_upwards [tendsto_loglog.eventually_gt_atTop 0] with x hx
  field_simp
  ring

lemma primeRecip_tendsto : ∃ B : ℝ,
    Tendsto (fun x ↦ primeRecip x - Real.log (Real.log x) - B) atTop (𝓝 0) := by
  obtain ⟨B, hB⟩ := tendsto_sum_inv_primes_sub_log_log
  exact ⟨B, by simpa [primeRecip, one_div] using hB⟩

lemma tendsto_primeRecip_div : Tendsto (fun x ↦ primeRecip x / Real.log (Real.log x)) atTop
    (𝓝 1) := by
  obtain ⟨B, hB⟩ := primeRecip_tendsto
  exact tendsto_div_loglog hB

lemma tendsto_primeRecip_rpow_div {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x ↦ primeRecip (x ^ a) / Real.log (Real.log x)) atTop (𝓝 1) := by
  obtain ⟨B, hB⟩ := primeRecip_tendsto
  refine tendsto_div_loglog (B := B + Real.log a) ?_
  refine (hB.comp (tendsto_rpow_atTop ha)).congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  have hlog : 0 < Real.log x := Real.log_pos hx
  simp only [Function.comp]
  rw [Real.log_rpow (by linarith), Real.log_mul ha.ne' hlog.ne']
  ring

lemma tendsto_bigL_div (k : ℕ) :
    Tendsto (fun x ↦ bigL k x / Real.log (Real.log x) ^ k) atTop (𝓝 1) := by
  cases k with
  | zero =>
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with x hx
    simp [bigL_zero hx]
  | succ k =>
    have ha : (0 : ℝ) < 1 / (k + 1) := by positivity
    have hlo := (tendsto_primeRecip_rpow_div ha).pow (k + 1)
    have hhi := (tendsto_primeRecip_div).pow (k + 1)
    rw [one_pow] at hlo hhi
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
    · filter_upwards [eventually_ge_atTop 1, tendsto_loglog.eventually_gt_atTop 0] with x hx hL
      rw [div_pow]
      exact div_le_div_of_nonneg_right (by exact_mod_cast le_bigL k hx) (by positivity)
    · filter_upwards [tendsto_loglog.eventually_gt_atTop 0] with x hL
      rw [div_pow]
      exact div_le_div_of_nonneg_right (bigL_le _ x) (by positivity)

/-! ### (22.18.6), (22.18.7) -/

/-- `f_{k+1}(x) = ϑ_{k+1}(x) - (k + 1) x L_k(x)`. -/
noncomputable def fRem (k : ℕ) (x : ℝ) : ℝ := bigTheta (k + 1) x - ((k : ℝ) + 1) * x * bigL k x

lemma fRem_succ (k : ℕ) (x : ℝ) :
    fRem (k + 1) x = ((k : ℝ) + 2) / ((k : ℝ) + 1) *
      ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, fRem k (x / p) := by
  have hT := bigTheta_succ (k + 1) x
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hT' : bigTheta (k + 1 + 1) x = ((k : ℝ) + 2) / ((k : ℝ) + 1) *
      ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, bigTheta (k + 1) (x / p) := by
    push_cast at hT
    rw [div_mul_eq_mul_div, eq_div_iff hk.ne', mul_comm, hT]
    ring
  simp only [fRem]
  rw [hT', bigL_succ, mul_sum, mul_sum, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun p hp ↦ ?_
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (mem_filter.1 hp).2.ne_zero
  push_cast
  field_simp
  ring

lemma fRem_zero {x : ℝ} (hx : 1 ≤ x) : fRem 0 x = θ x - x := by
  simp [fRem, bigTheta_one, bigL_zero hx]

lemma abs_fRem_le_of_le (k : ℕ) {y x₀ : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x₀) :
    |fRem k y| ≤ bigTheta (k + 1) x₀ + ((k : ℝ) + 1) * x₀ * bigL k x₀ := by
  have h1 := bigTheta_nonneg (k + 1) y
  have h2 := bigL_nonneg k y
  have h3 := bigTheta_mono (k + 1) hyx
  have h4 := bigL_mono k hyx
  have hk : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  have h5 : ((k : ℝ) + 1) * y * bigL k y ≤ ((k : ℝ) + 1) * x₀ * bigL k x₀ :=
    mul_le_mul (mul_le_mul_of_nonneg_left hyx hk) h4 h2 (mul_nonneg hk (hy.trans hyx))
  have h6 : 0 ≤ ((k : ℝ) + 1) * y * bigL k y := by positivity
  rw [fRem, abs_le]
  constructor <;> linarith

lemma loglog_le_loglog {y x : ℝ} (hy : Real.exp 1 ≤ y) (hyx : y ≤ x) :
    0 ≤ Real.log (Real.log y) ∧ Real.log (Real.log y) ≤ Real.log (Real.log x) := by
  have hy0 : 0 < y := lt_of_lt_of_le (Real.exp_pos 1) hy
  have h1 : 1 ≤ Real.log y := by rwa [Real.le_log_iff_exp_le hy0]
  exact ⟨Real.log_nonneg h1, Real.log_le_log (by linarith) (Real.log_le_log hy0 hyx)⟩

/-- (22.18.7): `f_{k+1}(x) = o(x (log log x)^k)`. -/
lemma fRem_small (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, |fRem k x| ≤ ε * x * Real.log (Real.log x) ^ k := by
  induction k generalizing ε with
  | zero =>
    have hθ : Tendsto (fun x ↦ θ x / x) atTop (𝓝 1) :=
      NTKB.Apostol.apostol_thm_4_4.2.mpr tendsto_psi_div_self
    filter_upwards [Metric.tendsto_nhds.1 hθ ε hε, eventually_ge_atTop 1] with x hx hx1
    rw [fRem_zero hx1, pow_zero, mul_one]
    rw [Real.dist_eq] at hx
    have hx0 : 0 < x := by linarith
    have : θ x - x = x * (θ x / x - 1) := by field_simp
    rw [this, abs_mul, abs_of_pos hx0, mul_comm ε]
    exact mul_le_mul_of_nonneg_left hx.le hx0.le
  | succ k ih =>
    set ε' := ε / 8 with hε'
    have hε'0 : 0 < ε' := by positivity
    obtain ⟨a, ha⟩ := eventually_atTop.1 (ih hε'0)
    set x₀ := max a 16 with hx₀
    have hx₀e : Real.exp 1 ≤ x₀ := by
      have := Real.exp_one_lt_d9
      have : (16 : ℝ) ≤ x₀ := le_max_right _ _
      linarith
    have hx₀0 : 0 ≤ x₀ := (Real.exp_pos 1).le.trans hx₀e
    set D := bigTheta (k + 1) x₀ + ((k : ℝ) + 1) * x₀ * bigL k x₀ with hD
    have hD0 : 0 ≤ D := by
      have := bigTheta_nonneg (k + 1) x₀
      have := bigL_nonneg k x₀
      positivity
    have hLL := tendsto_loglog
    have hS : ∀ᶠ x in atTop, primeRecip x ≤ 2 * Real.log (Real.log x) := by
      filter_upwards [(tendsto_order.1 tendsto_primeRecip_div).2 2 (by norm_num),
        hLL.eventually_gt_atTop 0] with x hx hL
      rw [div_lt_iff₀ hL] at hx
      exact hx.le
    have hDsmall : ∀ᶠ x in atTop, D ≤ ε' * Real.log (Real.log x) ^ (k + 1) := by
      have : Tendsto (fun x ↦ ε' * Real.log (Real.log x) ^ (k + 1)) atTop atTop :=
        (tendsto_pow_atTop (Nat.succ_ne_zero k)).comp hLL |>.const_mul_atTop hε'0
      exact this.eventually_ge_atTop D
    filter_upwards [hS, hDsmall, eventually_ge_atTop x₀] with x hSx hDx hxx₀
    have hxe : Real.exp 1 ≤ x := hx₀e.trans hxx₀
    have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hxe
    have hLx := (loglog_le_loglog hxe le_rfl).1
    -- termwise bound
    have hterm : ∀ p ∈ (Ioc 0 ⌊x⌋₊).filter (fun p ↦ p.Prime),
        |fRem k (x / p)| ≤ ε' * x * Real.log (Real.log x) ^ k * (p : ℝ)⁻¹ + D := by
      intro p hp
      have hp' := one_le_of_mem (mem_filter.1 hp).1
      have hp0 : (0 : ℝ) < p := by linarith [hp'.1]
      have hxp0 : 0 ≤ x / p := by positivity
      by_cases hbig : x₀ ≤ x / p
      · have h1 := ha (x / p) ((le_max_left _ _).trans hbig)
        have hLp := loglog_le_loglog (hx₀e.trans hbig) (div_le_self hx0.le hp'.1)
        have h2 : ε' * (x / p) * Real.log (Real.log (x / p)) ^ k ≤
            ε' * x * Real.log (Real.log x) ^ k * (p : ℝ)⁻¹ := by
          rw [div_eq_mul_inv]
          have := pow_le_pow_left₀ hLp.1 hLp.2 k
          have h3 : 0 ≤ ε' * (x * (p : ℝ)⁻¹) := by positivity
          calc ε' * (x * (p : ℝ)⁻¹) * Real.log (Real.log (x / p)) ^ k
              ≤ ε' * (x * (p : ℝ)⁻¹) * Real.log (Real.log x) ^ k :=
                mul_le_mul_of_nonneg_left this h3
            _ = _ := by ring
        linarith
      · have h1 := abs_fRem_le_of_le k hxp0 (le_of_not_ge hbig)
        have : 0 ≤ ε' * x * Real.log (Real.log x) ^ k * (p : ℝ)⁻¹ := by positivity
        linarith
    have hcard : (((Ioc 0 ⌊x⌋₊).filter (fun p ↦ p.Prime)).card : ℝ) ≤ x := by
      calc (((Ioc 0 ⌊x⌋₊).filter (fun p ↦ p.Prime)).card : ℝ) ≤ (Ioc 0 ⌊x⌋₊).card := by
            exact_mod_cast card_filter_le _ _
        _ = ⌊x⌋₊ := by simp
        _ ≤ x := Nat.floor_le hx0.le
    have hsum : ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, |fRem k (x / p)| ≤
        ε' * x * Real.log (Real.log x) ^ k * primeRecip x + D * x := by
      calc ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, |fRem k (x / p)|
          ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime,
              (ε' * x * Real.log (Real.log x) ^ k * (p : ℝ)⁻¹ + D) := sum_le_sum hterm
        _ = ε' * x * Real.log (Real.log x) ^ k * primeRecip x +
              D * (((Ioc 0 ⌊x⌋₊).filter (fun p ↦ p.Prime)).card : ℝ) := by
            rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, primeRecip]
            ring
        _ ≤ _ := by gcongr
    have hk2 : ((k : ℝ) + 2) / ((k : ℝ) + 1) ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]
      linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
    have hk2' : 0 ≤ ((k : ℝ) + 2) / ((k : ℝ) + 1) := by positivity
    rw [fRem_succ, abs_mul, abs_of_nonneg hk2']
    have hA : |∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, fRem k (x / p)| ≤
        ε' * x * Real.log (Real.log x) ^ k * primeRecip x + D * x :=
      (abs_sum_le_sum_abs _ _).trans hsum
    have hB : ε' * x * Real.log (Real.log x) ^ k * primeRecip x + D * x ≤
        3 * ε' * x * Real.log (Real.log x) ^ (k + 1) := by
      have e1 : ε' * x * Real.log (Real.log x) ^ k * primeRecip x ≤
          ε' * x * Real.log (Real.log x) ^ k * (2 * Real.log (Real.log x)) := by
        gcongr
      have e2 : D * x ≤ ε' * Real.log (Real.log x) ^ (k + 1) * x :=
        mul_le_mul_of_nonneg_right hDx hx0.le
      rw [pow_succ] at e2 ⊢
      nlinarith
    have hC : 0 ≤ ε' * x * Real.log (Real.log x) ^ k * primeRecip x + D * x := by
      have := primeRecip_nonneg x
      positivity
    calc ((k : ℝ) + 2) / ((k : ℝ) + 1) * |∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, fRem k (x / p)|
        ≤ 2 * (3 * ε' * x * Real.log (Real.log x) ^ (k + 1)) :=
          mul_le_mul hk2 (hA.trans hB) (abs_nonneg _) (by norm_num)
      _ ≤ ε * x * Real.log (Real.log x) ^ (k + 1) := by
          have : 0 ≤ x * Real.log (Real.log x) ^ (k + 1) := by positivity
          rw [hε']
          nlinarith

/-! ### (22.18.4), (22.18.5) -/

/-- (22.18.4): `ϑ_{k+1}(x) ~ (k + 1) x (log log x)^k`. -/
lemma tendsto_bigTheta_div (k : ℕ) :
    Tendsto (fun x ↦ bigTheta (k + 1) x / (((k : ℝ) + 1) * x * Real.log (Real.log x) ^ k))
      atTop (𝓝 1) := by
  have hf : Tendsto (fun x ↦ fRem k x / (x * Real.log (Real.log x) ^ k)) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [fRem_small k (half_pos hε), eventually_gt_atTop 0,
      tendsto_loglog.eventually_gt_atTop 0] with x hx hx0 hL
    have hpos : 0 < x * Real.log (Real.log x) ^ k := by positivity
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hpos, div_lt_iff₀ hpos]
    nlinarith
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h := (hf.div_const ((k : ℝ) + 1)).add (tendsto_bigL_div k)
  rw [zero_div, zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0, tendsto_loglog.eventually_gt_atTop 0] with x hx0 hL
  simp only [fRem]
  have : 0 < Real.log (Real.log x) ^ k := by positivity
  field_simp
  ring

lemma bigPi_mul_log_sub_bigTheta (k : ℕ) {x : ℝ} (hx : 0 < x) :
    bigPi k x * Real.log x - bigTheta k x = ∑ n ∈ Ioc 0 ⌊x⌋₊, c k n * Real.log (x / n) := by
  rw [bigPi, bigTheta, sum_mul, ← sum_sub_distrib]
  refine sum_congr rfl fun n hn ↦ ?_
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (mem_Ioc.1 hn).1.ne'
  rw [Real.log_div hx.ne' hn0]
  ring

/-- (22.18.5) with (22.18.4): `Π_{k+1}(x) ~ (k + 1) x (log log x)^k / log x`. -/
lemma tendsto_bigPi_div (k : ℕ) :
    Tendsto (fun x ↦ bigPi (k + 1) x * Real.log x /
      (((k : ℝ) + 1) * x * Real.log (Real.log x) ^ k)) atTop (𝓝 1) := by
  cases k with
  | zero =>
    refine prime_number_theorem.congr' ?_
    filter_upwards with x
    simp [bigPi_one]
  | succ j =>
    obtain ⟨C, hC⟩ := sum_rpow_log_div_le (h := 1) one_pos
    set K : ℝ := ((j + 1 + 1).factorial : ℝ)
    have hE : Tendsto (fun x ↦ (bigPi (j + 1 + 1) x * Real.log x - bigTheta (j + 1 + 1) x) /
        ((((j + 1 : ℕ) : ℝ) + 1) * x * Real.log (Real.log x) ^ (j + 1))) atTop (𝓝 0) := by
      have hup : Tendsto (fun x ↦ K * C / ((((j + 1 : ℕ) : ℝ) + 1) *
          Real.log (Real.log x) ^ (j + 1))) atTop (𝓝 0) := by
        refine tendsto_const_nhds.div_atTop ?_
        refine Tendsto.const_mul_atTop (by positivity) ?_
        exact (tendsto_pow_atTop (Nat.succ_ne_zero j)).comp tendsto_loglog
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
      · filter_upwards [eventually_ge_atTop 1, tendsto_loglog.eventually_gt_atTop 0]
          with x hx hL
        rw [bigPi_mul_log_sub_bigTheta _ (by linarith)]
        refine div_nonneg (sum_nonneg fun n hn ↦ mul_nonneg (c_nonneg _ _) ?_) (by positivity)
        have hn := one_le_of_mem hn
        exact Real.log_nonneg ((one_le_div (by linarith)).2 hn.2)
      · filter_upwards [eventually_ge_atTop 1, tendsto_loglog.eventually_gt_atTop 0]
          with x hx hL
        have hx0 : 0 < x := by linarith
        rw [bigPi_mul_log_sub_bigTheta _ hx0]
        have hpos : 0 < (((j + 1 : ℕ) : ℝ) + 1) * x * Real.log (Real.log x) ^ (j + 1) := by
          positivity
        rw [div_le_div_iff₀ hpos (by positivity)]
        have hs : ∑ n ∈ Ioc 0 ⌊x⌋₊, c (j + 1 + 1) n * Real.log (x / n) ≤ K * (C * x) := by
          calc ∑ n ∈ Ioc 0 ⌊x⌋₊, c (j + 1 + 1) n * Real.log (x / n)
              ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, K * Real.log (x / n) := by
                refine sum_le_sum fun n hn ↦ ?_
                have hn := one_le_of_mem hn
                refine mul_le_mul_of_nonneg_right (c_le_factorial _ _) ?_
                exact Real.log_nonneg ((one_le_div (by linarith)).2 hn.2)
            _ = K * ∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log (x / n) ^ (1 : ℝ) := by
                rw [mul_sum]; simp
            _ ≤ K * (C * x) := mul_le_mul_of_nonneg_left (hC x hx) (by positivity)
        have : 0 ≤ (((j + 1 : ℕ) : ℝ) + 1) * Real.log (Real.log x) ^ (j + 1) := by positivity
        calc (∑ n ∈ Ioc 0 ⌊x⌋₊, c (j + 1 + 1) n * Real.log (x / n)) *
              ((((j + 1 : ℕ) : ℝ) + 1) * Real.log (Real.log x) ^ (j + 1))
            ≤ K * (C * x) * ((((j + 1 : ℕ) : ℝ) + 1) * Real.log (Real.log x) ^ (j + 1)) :=
              mul_le_mul_of_nonneg_right hs this
          _ = _ := by ring
    have h := (tendsto_bigTheta_div (j + 1)).add hE
    rw [add_zero] at h
    refine h.congr' ?_
    filter_upwards with x
    rw [← add_div]
    ring_nf

/-! ### Theorem 437 -/

/-- (22.18.2), first half: `k! π_k(x) ≤ Π_k(x)`. -/
lemma factorial_mul_card_le_bigPi (k : ℕ) (x : ℝ) :
    (k.factorial : ℝ) * ((Ioc 0 ⌊x⌋₊).filter fun n ↦ Squarefree n ∧ ω n = k).card ≤
      bigPi k x := by
  rw [mul_comm, ← nsmul_eq_mul, ← sum_const]
  calc ∑ _n ∈ (Ioc 0 ⌊x⌋₊).filter (fun n ↦ Squarefree n ∧ ω n = k), (k.factorial : ℝ)
      = ∑ n ∈ (Ioc 0 ⌊x⌋₊).filter (fun n ↦ Squarefree n ∧ ω n = k), c k n := by
        refine sum_congr rfl fun n hn ↦ ?_
        obtain ⟨-, hsq, hω⟩ := mem_filter.1 hn
        rw [c_eq_factorial hsq]
        rw [← (cardDistinctFactors_eq_cardFactors_iff_squarefree hsq.ne_zero).2 hsq, hω]
    _ ≤ bigPi k x := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        fun n _ _ ↦ c_nonneg k n

/-- (22.18.2), second half: `Π_k(x) ≤ k! τ_k(x)`. -/
lemma bigPi_le_factorial_mul_card (k : ℕ) (x : ℝ) :
    bigPi k x ≤
      (k.factorial : ℝ) * ((Ioc 0 ⌊x⌋₊).filter fun n ↦ Nat.IsAlmostPrime k n).card := by
  rw [bigPi, ← sum_filter_of_ne (p := fun n ↦ Nat.IsAlmostPrime k n)]
  · rw [mul_comm, ← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum fun n _ ↦ c_le_factorial k n
  · intro n _ hn
    exact c_ne_zero hn

/-- (22.18.3): `τ_{k+1}(x) - π_{k+1}(x) ≤ Π_k(x)`, in the form
`τ_{k+2}(x) ≤ π_{k+2}(x) + Π_{k+1}(x)`. -/
lemma card_almostPrime_le (k : ℕ) (x : ℝ) :
    (((Ioc 0 ⌊x⌋₊).filter fun n ↦ Nat.IsAlmostPrime (k + 1 + 1) n).card : ℝ) ≤
      ((Ioc 0 ⌊x⌋₊).filter fun n ↦ Squarefree n ∧ ω n = k + 1 + 1).card + bigPi (k + 1) x := by
  set T := (Ioc 0 ⌊x⌋₊).filter fun n ↦ Nat.IsAlmostPrime (k + 1 + 1) n
  set Q := (Ioc 0 ⌊x⌋₊).filter fun n ↦ Squarefree n ∧ ω n = k + 1 + 1
  set R := (Ioc 0 ⌊x⌋₊).filter fun m ↦ Ω m = k + 1
  have h1 : (T.filter Squarefree).card ≤ Q.card := by
    refine card_le_card fun n hn ↦ ?_
    obtain ⟨hnT, hsq⟩ := mem_filter.1 hn
    obtain ⟨hnI, hn0, hΩ⟩ := mem_filter.1 hnT
    refine mem_filter.2 ⟨hnI, hsq, ?_⟩
    rw [(cardDistinctFactors_eq_cardFactors_iff_squarefree hn0).2 hsq, hΩ]
  have h2 : (T.filter fun n ↦ ¬ Squarefree n) ⊆
      (R.sigma fun m ↦ m.primeFactors).image fun s ↦ s.1 * s.2 := by
    intro n hn
    obtain ⟨hnT, hsq⟩ := mem_filter.1 hn
    obtain ⟨hnI, hn0, hΩ⟩ := mem_filter.1 hnT
    rw [Nat.squarefree_iff_prime_squarefree] at hsq
    push Not at hsq
    obtain ⟨p, hp, hpp⟩ := hsq
    have hpn : p ∣ n := (Dvd.intro p rfl).trans hpp
    have hpf : p ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨hp, hpn, hn0⟩
    have hm0 := div_ne_zero_of_mem_primeFactors hpf
    have hmΩ : Ω (n / p) = k + 1 := by have := cardFactors_div_add_one hpf; omega
    refine mem_image.2 ⟨⟨n / p, p⟩, ?_, Nat.div_mul_cancel hpn⟩
    refine mem_sigma.2 ⟨mem_filter.2 ⟨?_, hmΩ⟩, ?_⟩
    · have hI := mem_Ioc.1 hnI
      exact mem_Ioc.2 ⟨Nat.pos_of_ne_zero hm0, (Nat.div_le_self n p).trans hI.2⟩
    · exact Nat.mem_primeFactors.2 ⟨hp, Nat.dvd_div_of_mul_dvd hpp, hm0⟩
  have h3 : (((R.sigma fun m ↦ m.primeFactors).image fun s ↦ s.1 * s.2).card : ℝ) ≤
      bigPi (k + 1) x := by
    calc (((R.sigma fun m ↦ m.primeFactors).image fun s ↦ s.1 * s.2).card : ℝ)
        ≤ (R.sigma fun m ↦ m.primeFactors).card := by exact_mod_cast card_image_le
      _ = ∑ m ∈ R, (m.primeFactors.card : ℝ) := by rw [card_sigma]; push_cast; rfl
      _ ≤ ∑ m ∈ R, c (k + 1) m := by
          refine sum_le_sum fun m hm ↦ ?_
          obtain ⟨hmI, hmΩ⟩ := mem_filter.1 hm
          exact card_primeFactors_le_c hmΩ
      _ ≤ bigPi (k + 1) x := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          fun n _ _ ↦ c_nonneg _ n
  have h4 := card_filter_add_card_filter_not (s := T) Squarefree
  have h5 := card_le_card h2
  have : (T.card : ℝ) = (T.filter Squarefree).card + (T.filter fun n ↦ ¬ Squarefree n).card := by
    exact_mod_cast h4.symm
  rw [this]
  have h1' : ((T.filter Squarefree).card : ℝ) ≤ Q.card := by exact_mod_cast h1
  have h5' : ((T.filter fun n ↦ ¬ Squarefree n).card : ℝ) ≤
      (((R.sigma fun m ↦ m.primeFactors).image fun s ↦ s.1 * s.2).card : ℝ) := by
    exact_mod_cast h5
  linarith

end Landau

open Landau in
/-- **Theorem 437** (Landau). For `k ≥ 2`, the number `π_k(x)` of squarefree `n ≤ x` with
`ω(n) = k` and the number `τ_k(x)` of `n ≤ x` with `Ω(n) = k` (Mathlib's `Nat.IsAlmostPrime k`)
both satisfy `π_k(x) ~ τ_k(x) ~ x (log log x)^(k-1) / ((k-1)! log x)`. -/
@[kb "hardywright2008" "Thm 437, p. 510"]
theorem landau_almost_prime (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (fun x : ℝ ↦ (((Ioc 0 ⌊x⌋₊).filter fun n ↦ Squarefree n ∧ ω n = k).card : ℝ) /
      (x * Real.log (Real.log x) ^ (k - 1) / ((k - 1).factorial * Real.log x))) atTop (𝓝 1) ∧
    Tendsto (fun x : ℝ ↦ (((Ioc 0 ⌊x⌋₊).filter fun n ↦ Nat.IsAlmostPrime k n).card : ℝ) /
      (x * Real.log (Real.log x) ^ (k - 1) / ((k - 1).factorial * Real.log x))) atTop
      (𝓝 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 + 1 := ⟨k - 2, by omega⟩
  rw [show j + 1 + 1 - 1 = j + 1 by omega]
  set M : ℝ → ℝ := fun x ↦
    x * Real.log (Real.log x) ^ (j + 1) / ((j + 1).factorial * Real.log x) with hM
  -- `Π_{j+2}(x) / ((j+2)! M(x)) → 1`
  have hA : Tendsto (fun x ↦ bigPi (j + 1 + 1) x / ((j + 1 + 1).factorial * M x)) atTop (𝓝 1) := by
    refine (tendsto_bigPi_div (j + 1)).congr' ?_
    filter_upwards [eventually_gt_atTop 1] with x hx
    have hlog : 0 < Real.log x := Real.log_pos hx
    simp only [hM, Nat.factorial_succ (j + 1)]
    push_cast
    have : (0 : ℝ) < (j + 1).factorial := by exact_mod_cast Nat.factorial_pos _
    field_simp
  -- `Π_{j+1}(x) / M(x) → 0`
  have hB : Tendsto (fun x ↦ bigPi (j + 1) x / M x) atTop (𝓝 0) := by
    have h0 : Tendsto (fun x ↦ ((j : ℝ) + 1) * (j + 1).factorial / Real.log (Real.log x))
        atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_loglog
    have h := (tendsto_bigPi_div j).mul h0
    rw [one_mul] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 1, tendsto_loglog.eventually_gt_atTop 0]
      with x hx hL
    have hlog : 0 < Real.log x := Real.log_pos hx
    simp only [hM]
    have : (0 : ℝ) < (j + 1).factorial := by exact_mod_cast Nat.factorial_pos _
    field_simp
    ring
  have hMpos : ∀ᶠ x in atTop, 0 < M x := by
    filter_upwards [eventually_gt_atTop 1, tendsto_loglog.eventually_gt_atTop 0]
      with x hx hL
    have hlog : 0 < Real.log x := Real.log_pos hx
    simp only [hM]
    have : (0 : ℝ) < (j + 1).factorial := by exact_mod_cast Nat.factorial_pos _
    positivity
  have hF : (0 : ℝ) < (j + 1 + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  have hlow := hA.sub hB
  rw [sub_zero] at hlow
  have hhigh := hA.add hB
  rw [add_zero] at hhigh
  have hQ : ∀ x : ℝ, (((Ioc 0 ⌊x⌋₊).filter fun n ↦ Squarefree n ∧ ω n = j + 1 + 1).card : ℝ) ≤
      bigPi (j + 1 + 1) x / (j + 1 + 1).factorial := fun x ↦ by
    rw [le_div_iff₀ hF, mul_comm]
    exact factorial_mul_card_le_bigPi _ x
  have hT : ∀ x : ℝ, bigPi (j + 1 + 1) x / (j + 1 + 1).factorial ≤
      (((Ioc 0 ⌊x⌋₊).filter fun n ↦ Nat.IsAlmostPrime (j + 1 + 1) n).card : ℝ) := fun x ↦ by
    rw [div_le_iff₀ hF, mul_comm]
    exact bigPi_le_factorial_mul_card _ x
  constructor
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hA ?_ ?_
    · filter_upwards [hMpos] with x hMx
      change _ ≤ _ / M x
      rw [← div_div, ← sub_div]
      refine div_le_div_of_nonneg_right ?_ hMx.le
      linarith [card_almostPrime_le j x, hT x]
    · filter_upwards [hMpos] with x hMx
      change _ / M x ≤ _
      rw [← div_div]
      exact div_le_div_of_nonneg_right (hQ x) hMx.le
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hA hhigh ?_ ?_
    · filter_upwards [hMpos] with x hMx
      change _ ≤ _ / M x
      rw [← div_div]
      exact div_le_div_of_nonneg_right (hT x) hMx.le
    · filter_upwards [hMpos] with x hMx
      change _ / M x ≤ _
      rw [← div_div, ← add_div]
      refine div_le_div_of_nonneg_right ?_ hMx.le
      linarith [card_almostPrime_le j x, hQ x]

end NTKB.HardyWright
