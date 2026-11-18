/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.IrelandRosen.R5.LocalPolynomial

/-!
# The coefficients of `WeierstrassCurve.LFunction` over `ℚ`

For a Weierstrass curve `W` over `ℚ`, Mathlib's `W.LFunction` is the formal Euler product over the
finite places `v` of `ℚ` of the local Euler factors `1 / f_v(p^{-s})`, `f_v` the local polynomial
(`WeierstrassCurve.localPolynomial`) and `p = placePrime v`. We prove:

* `LFunction_isMultiplicative`: the coefficients form a multiplicative arithmetic function;
* `LFunction_apply_prime_pow`: the coefficient of `p^k` is the `k`-th coefficient of the local power
  series `1 / f_v(X)` at the place above `p`;
* `LFunction_recursion`: if `f_v = 1 - s X + t X²` (after mapping to a commutative ring `S`), then
  for every `n ≠ 0` divisible by `p`, `a(n) = s a(n/p) - t a(n/p²)` (the last term read as `0` when
  `p² ∤ n`);
* `localPowerSeries_coeff_of_eq`: the same recursion for the coefficients of `1 / f_v(X)`.

These are the facts needed to compare `W.LFunction` with a Dirichlet series given by a recursion
at each prime, as for the Hecke `L`-series of Theorems 7 and 8 of Ireland–Rosen, Chapter 18.
-/

namespace NTKB.IrelandRosen.CM

open Polynomial IsDedekindDomain NumberField ArithmeticFunction

variable (W : WeierstrassCurve ℚ) (v : HeightOneSpectrum (𝓞 ℚ))

/-- The local polynomial of `W` at the finite place `v` of `ℚ`. -/
noncomputable abbrev ratLocalPolynomial : ℤ[X] :=
  (W.baseChange (v.adicCompletion ℚ)).localPolynomial (v.adicCompletionIntegers ℚ)

/-- The local power series `1 / f_v(X)` of `W` at the finite place `v` of `ℚ`. -/
noncomputable abbrev ratLocalPowerSeries : PowerSeries ℤ :=
  (W.baseChange (v.adicCompletion ℚ)).localPowerSeries (v.adicCompletionIntegers ℚ)

/-- The local polynomial has constant coefficient `1`. -/
lemma ratLocalPolynomial_coeff_zero : (ratLocalPolynomial W v).coeff 0 = 1 := by
  unfold ratLocalPolynomial WeierstrassCurve.localPolynomial
  split_ifs <;> simp

/-- The local power series is the inverse of the local polynomial. -/
lemma ratLocalPolynomial_mul_ratLocalPowerSeries :
    (ratLocalPolynomial W v : PowerSeries ℤ) * ratLocalPowerSeries W v = 1 := by
  have h0 : PowerSeries.constantCoeff (ratLocalPolynomial W v : PowerSeries ℤ) =
      ((1 : ℤˣ) : ℤ) := by
    simp [ratLocalPolynomial_coeff_zero]
  exact PowerSeries.mul_invOfUnit _ 1 h0

/-- **Recursion for the local power series.** If the local polynomial, mapped to `S`, is
`1 - s X + t X²`, the coefficients `h_k` of `1 / f_v(X)` satisfy `h_0 = 1`, `h_1 = s` and
`h_{k+2} = s h_{k+1} - t h_k`. -/
theorem localPowerSeries_coeff_of_eq {S : Type*} [CommRing S] (s t : S)
    (h : (ratLocalPolynomial W v).map (Int.castRingHom S) = 1 - C s * X + C t * X ^ 2) :
    ((PowerSeries.coeff 0 (ratLocalPowerSeries W v) : ℤ) : S) = 1 ∧
    ((PowerSeries.coeff 1 (ratLocalPowerSeries W v) : ℤ) : S) = s ∧
    ∀ k : ℕ, ((PowerSeries.coeff (k + 2) (ratLocalPowerSeries W v) : ℤ) : S) =
      s * (PowerSeries.coeff (k + 1) (ratLocalPowerSeries W v) : ℤ) -
        t * (PowerSeries.coeff k (ratLocalPowerSeries W v) : ℤ) := by
  have h1 := congrArg (PowerSeries.map (Int.castRingHom S))
    (ratLocalPolynomial_mul_ratLocalPowerSeries W v)
  rw [map_mul, map_one, ← Polynomial.polynomial_map_coe, h] at h1
  set ψ := PowerSeries.map (Int.castRingHom S) (ratLocalPowerSeries W v) with hψ
  have e : ∀ n : ℕ, PowerSeries.coeff n ψ =
      ((PowerSeries.coeff n (ratLocalPowerSeries W v) : ℤ) : S) := by
    intro n; simp [hψ]
  have h2 : ((1 - C s * X + C t * X ^ 2 : S[X]) : PowerSeries S) * ψ = 1 := h1
  have h3 : ((1 - C s * X + C t * X ^ 2 : S[X]) : PowerSeries S) * ψ =
      ψ - PowerSeries.C s * (PowerSeries.X * ψ) +
        PowerSeries.C t * (PowerSeries.X * (PowerSeries.X * ψ)) := by
    push_cast
    ring
  rw [h3] at h2
  have c0 := congrArg (PowerSeries.coeff 0) h2
  have c1 := congrArg (PowerSeries.coeff 1) h2
  have c2 : ∀ k, PowerSeries.coeff (k + 2) (ψ - PowerSeries.C s * (PowerSeries.X * ψ) +
        PowerSeries.C t * (PowerSeries.X * (PowerSeries.X * ψ))) =
      PowerSeries.coeff (k + 2) (1 : PowerSeries S) := fun k => by rw [h2]
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_zero_X_mul,
    PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_one] at c0 c1 c2
  refine ⟨?_, ?_, fun k => ?_⟩
  · rw [← e]; simpa using c0
  · have c0' : PowerSeries.coeff 0 ψ = 1 := by simpa using c0
    rw [← e]
    simp [c0'] at c1
    linear_combination c1
  · have := c2 k
    simp at this
    rw [← e, ← e, ← e]
    linear_combination this

lemma constantCoeff_ratLocalPowerSeries :
    (ratLocalPowerSeries W v).constantCoeff = 1 := by
  unfold ratLocalPowerSeries WeierstrassCurve.localPowerSeries
  simp [PowerSeries.constantCoeff_invOfUnit]

/-- `W.LFunction` as the Euler product of the `ofPowerSeries` factors. -/
lemma LFunction_eq : W.LFunction =
    eulerProduct fun w : HeightOneSpectrum (𝓞 ℚ) =>
      ofPowerSeries (placePrime w) (ratLocalPowerSeries W w) := by
  unfold WeierstrassCurve.LFunction
  congr 1
  funext w
  unfold WeierstrassCurve.localEulerFactor
  rw [card_residueField]

lemma placePrime_injective :
    Function.Injective (fun w : HeightOneSpectrum (𝓞 ℚ) => placePrime w) :=
  fun a b h => (Rat.HeightOneSpectrum.primesEquiv).injective (Subtype.ext h)

instance : Northcott (fun w : HeightOneSpectrum (𝓞 ℚ) => placePrime w) := by
  refine ⟨fun b => ?_⟩
  have : {a : HeightOneSpectrum (𝓞 ℚ) | placePrime a ≤ b} ⊆
      (fun w : HeightOneSpectrum (𝓞 ℚ) => placePrime w) ⁻¹' (Set.Iic b) := fun a ha => ha
  exact Set.Finite.subset ((Set.finite_Iic b).preimage placePrime_injective.injOn) this

/-- If `f` and `f'` agree on divisors of `n` then `f * g` and `f' * g` agree at `n`. -/
lemma mul_apply_congr_left {f f' g : ArithmeticFunction ℤ} {n : ℕ}
    (h : ∀ d, d ∣ n → f d = f' d) : (f * g) n = (f' * g) n := by
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [h x.1 (Nat.dvd_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hx))]

lemma factor_apply_pow_of_ne {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v) {j : ℕ} (hj : j ≠ 0) :
    ofPowerSeries (placePrime w) (ratLocalPowerSeries W w) (placePrime v ^ j) = 0 := by
  have hp := (placePrime_fact w).out
  have hq := (placePrime_fact v).out
  rw [ofPowerSeries_apply hp.one_lt, Function.extend_apply', Pi.zero_apply]
  rintro ⟨i, hi⟩
  have hne : placePrime w ≠ placePrime v := fun h => hw (placePrime_injective h)
  rcases i with _ | i
  · rw [pow_zero] at hi
    rcases Nat.pow_eq_one.mp hi.symm with h | h
    · exact hq.ne_one h
    · exact hj h
  · have : placePrime w ∣ placePrime v ^ j := hi ▸ dvd_pow_self _ (Nat.succ_ne_zero i)
    exact hne ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow this))

lemma prod_apply_pow_of_notMem (t : Finset (HeightOneSpectrum (𝓞 ℚ))) (ht : v ∉ t) (j : ℕ) :
    (∏ w ∈ t, ofPowerSeries (placePrime w) (ratLocalPowerSeries W w)) (placePrime v ^ j) =
      (1 : ArithmeticFunction ℤ) (placePrime v ^ j) := by
  classical
  induction t using Finset.induction_on generalizing j with
  | empty => simp
  | insert w t hw ih =>
    have hwv : w ≠ v := fun h => ht (h ▸ Finset.mem_insert_self _ _)
    have htv : v ∉ t := fun h => ht (Finset.mem_insert_of_mem h)
    rw [Finset.prod_insert hw]
    have : (ofPowerSeries (placePrime w) (ratLocalPowerSeries W w) *
        ∏ w ∈ t, ofPowerSeries (placePrime w) (ratLocalPowerSeries W w)) (placePrime v ^ j) =
        ((1 : ArithmeticFunction ℤ) * ∏ w ∈ t, ofPowerSeries (placePrime w)
          (ratLocalPowerSeries W w)) (placePrime v ^ j) := by
      refine mul_apply_congr_left fun d hd => ?_
      obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow (placePrime_fact v).out).mp hd
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · simp [constantCoeff_ratLocalPowerSeries]
      · rw [factor_apply_pow_of_ne W v hwv hi.ne']
        rw [ArithmeticFunction.one_apply_ne]
        exact (Nat.one_lt_pow hi.ne' (placePrime_fact v).out.one_lt).ne'
    rw [this, one_mul]
    exact ih htv j

lemma prod_apply_pow_of_mem (s : Finset (HeightOneSpectrum (𝓞 ℚ))) (hv : v ∈ s) (k : ℕ) :
    (∏ w ∈ s, ofPowerSeries (placePrime w) (ratLocalPowerSeries W w)) (placePrime v ^ k) =
      PowerSeries.coeff k (ratLocalPowerSeries W v) := by
  classical
  rw [← Finset.mul_prod_erase s _ hv, mul_comm]
  have : ((∏ w ∈ s.erase v, ofPowerSeries (placePrime w) (ratLocalPowerSeries W w)) *
      ofPowerSeries (placePrime v) (ratLocalPowerSeries W v)) (placePrime v ^ k) =
      ((1 : ArithmeticFunction ℤ) * ofPowerSeries (placePrime v) (ratLocalPowerSeries W v))
        (placePrime v ^ k) := by
    refine mul_apply_congr_left fun d hd => ?_
    obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow (placePrime_fact v).out).mp hd
    exact prod_apply_pow_of_notMem W v _ (Finset.notMem_erase v s) i
  rw [this, one_mul, ofPowerSeries_apply_pow (placePrime_fact v).out.one_lt]

/-- The coefficients of `W.LFunction` form a multiplicative arithmetic function. -/
theorem LFunction_isMultiplicative : W.LFunction.IsMultiplicative := by
  rw [LFunction_eq]
  refine isMultiplicative_eulerProduct _ fun w => ?_
  exact isMultiplicative_ofPowerSeries_of_isPrimePow _
    (Nat.Prime.isPrimePow (placePrime_fact w).out) _ (constantCoeff_ratLocalPowerSeries W w)

/-- The coefficient of `p^k` in `W.LFunction` is the `k`-th coefficient of the local power series
at the place `v` above `p`. -/
theorem LFunction_apply_prime_pow (k : ℕ) :
    W.LFunction (placePrime v ^ k) = PowerSeries.coeff k (ratLocalPowerSeries W v) := by
  have key := tendsTo_eulerProduct_ofPowerSeries
    (fun w : HeightOneSpectrum (𝓞 ℚ) => placePrime w)
    (fun w => ratLocalPowerSeries W w) (fun w => constantCoeff_ratLocalPowerSeries W w)
    (placePrime v ^ k)
  have key2 : ∀ᶠ s in Filter.atTop, v ∈ s :=
    (Filter.eventually_ge_atTop ({v} : Finset (HeightOneSpectrum (𝓞 ℚ)))).mono
      fun s hs => Finset.singleton_subset_iff.mp hs
  obtain ⟨s, hs1, hs2⟩ := (key.and key2).exists
  rw [LFunction_eq, ← hs1]
  exact prod_apply_pow_of_mem W v s hs2 k

/-- **The recursion at a prime.** If the local polynomial of `W` at `v`, mapped to `S`, is
`1 - s X + t X²` and `p = placePrime v` divides `n ≠ 0`, then
`a(n) = s a(n/p) - t a(n/p²)`, the last term read as `0` when `p² ∤ n`. -/
theorem LFunction_recursion {S : Type*} [CommRing S] (s t : S)
    (h : (ratLocalPolynomial W v).map (Int.castRingHom S) = 1 - C s * X + C t * X ^ 2)
    {n : ℕ} (hn0 : n ≠ 0) (hn : placePrime v ∣ n) :
    ((W.LFunction n : ℤ) : S) =
      s * (W.LFunction (n / placePrime v) : ℤ) -
        (if placePrime v ^ 2 ∣ n then t * (W.LFunction (n / placePrime v ^ 2) : ℤ) else 0) := by
  have hp := (placePrime_fact v).out
  obtain ⟨c0, c1, c2⟩ := localPowerSeries_coeff_of_eq W v s t h
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 (placePrime v) hp.ne_one
  have hmult := LFunction_isMultiplicative W
  have A : ∀ j : ℕ, ((W.LFunction (placePrime v ^ j * m) : ℤ) : S) =
      ((PowerSeries.coeff j (ratLocalPowerSeries W v) : ℤ) : S) * (W.LFunction m : ℤ) := by
    intro j
    rw [hmult.map_mul_of_coprime
      (Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)),
      LFunction_apply_prime_pow]
    push_cast
    rfl
  rcases k with _ | k
  · exact absurd (by simpa using hn) hm
  · have d1 : placePrime v ^ (k + 1) * m / placePrime v = placePrime v ^ k * m :=
      Nat.div_eq_of_eq_mul_left hp.pos (by ring)
    rw [d1]
    rcases k with _ | k
    · have hn2 : ¬ placePrime v ^ 2 ∣ placePrime v ^ (0 + 1) * m := by
        intro h2
        apply hm
        have : placePrime v * placePrime v ∣ placePrime v * m := by simpa [pow_two] using h2
        exact (Nat.mul_dvd_mul_iff_left hp.pos).mp this
      rw [if_neg hn2, A, A]
      simp only [c1, c0]
      ring
    · have hn2 : placePrime v ^ 2 ∣ placePrime v ^ (k + 1 + 1) * m :=
        Dvd.dvd.mul_right (pow_dvd_pow _ (by omega)) _
      have d2 : placePrime v ^ (k + 1 + 1) * m / placePrime v ^ 2 = placePrime v ^ k * m :=
        Nat.div_eq_of_eq_mul_left (pow_pos hp.pos 2) (by ring)
      rw [if_pos hn2, d2, A, A, A, c2 k]
      ring

end NTKB.IrelandRosen.CM
