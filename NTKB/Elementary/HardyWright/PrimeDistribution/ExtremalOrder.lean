/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.PrimeDistribution.MertensConstant
import NTKB.Elementary.HardyWright.ArithmeticFunctions.Order

/-!
# Hardy–Wright, § 22.9: proof of Theorems 323 and 328

[hardywright2008, § 22.9]. With Mertens' theorem (Theorem 429,
`∏_{p ≤ x} (1 - 1/p) ~ e^{-γ} / log x`) we prove

* **Theorem 328**: `liminf φ(n) log log n / n = e^{-γ}`;
* **Theorem 323** (Gronwall): `limsup σ(n) / (n log log n) = e^γ`.

The book's proof. Lower bound for `φ(n)/n` (22.9.1): the primes `p ∣ n` with `p > log n` number
at most `log n / log log n`, so
`φ(n)/n ≥ (1 - 1/log n)^{log n / log log n} ∏_{p ≤ log n} (1 - 1/p)`; we use Bernoulli's inequality
in the form `(1 - 1/t)^ρ ≥ 1 - ρ/t ≥ 1 - 1/log t` (`t = log n`). The upper bound for `σ(n)/n`
follows by Theorem 329 (`σ(n) φ(n) < n²`). Along `n = ∏_{p ≤ m} p`, `log n = θ(m) ≤ m log 4`
(Theorem 414) gives the other half of Theorem 328; along `n_j = ∏_{p ≤ 2^j} p^{2j}` (the book uses
`∏_{p ≤ e^j} p^j` and Theorem 280 `∏_p (1 - p^{-j-1}) = 1/ζ(j+1)`; we use the elementary bound
`∏ (1 - a_p) ≥ 1 - ∑ a_p` instead) the other half of Theorem 323.
-/

open Finset Filter ArithmeticFunction Chebyshev
open scoped Topology ArithmeticFunction.sigma

local notation "γ" => Real.eulerMascheroniConstant

namespace NTKB.HardyWright

namespace ExtremalOrder

/-- `P(t) = ∏_{p ≤ t} (1 - 1/p)`. -/
noncomputable def primeProd (t : ℝ) : ℝ := ∏ p ∈ Ioc 0 ⌊t⌋₊ with p.Prime, (1 - 1 / (p : ℝ))

lemma tendsto_loglog : Tendsto (fun x : ℝ ↦ Real.log (Real.log x)) atTop atTop :=
  Real.tendsto_log_atTop.comp Real.tendsto_log_atTop

lemma tendsto_loglog_nat : Tendsto (fun n : ℕ ↦ Real.log (Real.log n)) atTop atTop :=
  tendsto_loglog.comp tendsto_natCast_atTop_atTop

lemma one_sub_inv_mem {p : ℕ} (hp : p.Prime) : 0 < 1 - 1 / (p : ℝ) ∧ 1 - 1 / (p : ℝ) ≤ 1 := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  constructor
  · rw [sub_pos, div_lt_one (by linarith)]; linarith
  · have : 0 ≤ 1 / (p : ℝ) := by positivity
    linarith

lemma primeProd_pos (t : ℝ) : 0 < primeProd t :=
  prod_pos fun _ hp ↦ (one_sub_inv_mem (mem_filter.1 hp).2).1

lemma totient_div_eq_prod {n : ℕ} (hn : n ≠ 0) :
    (n.totient : ℝ) / n = ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ)) := by
  have h := congrArg (fun q : ℚ ↦ (q : ℝ)) (Nat.totient_eq_mul_prod_factors n)
  push_cast at h
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [h, mul_div_cancel_left₀ _ hn']
  simp [one_div]

lemma prod_le_prod_of_subset_primes {S T : Finset ℕ} (hST : S ⊆ T) (hT : ∀ p ∈ T, p.Prime) :
    ∏ p ∈ T, (1 - 1 / (p : ℝ)) ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ)) := by
  rw [← prod_sdiff hST]
  have h1 : ∏ p ∈ T \ S, (1 - 1 / (p : ℝ)) ≤ 1 :=
    prod_le_one₀ (fun p hp ↦ (one_sub_inv_mem (hT p (sdiff_subset hp))).1.le)
      (fun p hp ↦ (one_sub_inv_mem (hT p (sdiff_subset hp))).2)
  have h2 : 0 ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ)) :=
    prod_nonneg fun p hp ↦ (one_sub_inv_mem (hT p (hST hp))).1.le
  nlinarith

/-- (22.9.1): `φ(n)/n ≥ (1 - 1/log log n) ∏_{p ≤ log n} (1 - 1/p)` when `log log n ≥ 1`. -/
lemma totient_div_ge {n : ℕ} (hn : n ≠ 0) (ht : 1 ≤ Real.log (Real.log n)) :
    (1 - 1 / Real.log (Real.log n)) * primeProd (Real.log n) ≤ (n.totient : ℝ) / n := by
  set t := Real.log n with htdef
  have ht0' : 0 ≤ t := Real.log_natCast_nonneg n
  have ht1 : 1 < t := by
    by_contra h
    have := Real.log_nonpos ht0' (le_of_not_gt h)
    linarith
  have ht0 : 0 < t := by linarith
  have hlt : 0 < Real.log t := by linarith
  rw [totient_div_eq_prod hn, ← prod_filter_mul_prod_filter_not n.primeFactors
    (fun p : ℕ ↦ (p : ℝ) ≤ t)]
  set A := n.primeFactors.filter (fun p : ℕ ↦ (p : ℝ) ≤ t)
  set B := n.primeFactors.filter (fun p : ℕ ↦ ¬ (p : ℝ) ≤ t)
  have hA : primeProd t ≤ ∏ p ∈ A, (1 - 1 / (p : ℝ)) := by
    apply prod_le_prod_of_subset_primes
    · intro p hp
      obtain ⟨hpf, hpt⟩ := mem_filter.1 hp
      have hpp := Nat.prime_of_mem_primeFactors hpf
      exact mem_filter.2 ⟨mem_Ioc.2 ⟨hpp.pos, Nat.le_floor hpt⟩, hpp⟩
    · intro p hp; exact (mem_filter.1 hp).2
  have hBcard : (B.card : ℝ) * Real.log t ≤ t := by
    have hdvd : ∏ p ∈ B, p ∣ n :=
      (Finset.prod_dvd_prod_of_subset _ _ (fun p ↦ p) (filter_subset _ _)).trans
        (Nat.prod_primeFactors_dvd n)
    have hle : (∏ p ∈ B, (p : ℝ)) ≤ n := by
      rw [← Nat.cast_prod]
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
    have hge : t ^ B.card ≤ ∏ p ∈ B, (p : ℝ) := by
      rw [← prod_const]
      exact prod_le_prod₀ (fun _ _ ↦ ht0.le) (fun p hp ↦ (not_le.1 (mem_filter.1 hp).2).le)
    have hpos : 0 < t ^ B.card := pow_pos ht0 _
    have := Real.log_le_log hpos (hge.trans hle)
    rwa [Real.log_pow] at this
  have hB : 1 - 1 / Real.log t ≤ ∏ p ∈ B, (1 - 1 / (p : ℝ)) := by
    have h1 : (1 - 1 / t) ^ B.card ≤ ∏ p ∈ B, (1 - 1 / (p : ℝ)) := by
      rw [← prod_const]
      refine prod_le_prod₀ (fun _ _ ↦ ?_) (fun p hp ↦ ?_)
      · rw [sub_nonneg, div_le_one ht0]; linarith
      · have hpt := not_le.1 (mem_filter.1 hp).2
        have : 1 / (p : ℝ) ≤ 1 / t := one_div_le_one_div_of_le ht0 hpt.le
        linarith
    have h2 : 1 + (B.card : ℝ) * (-(1 / t)) ≤ (1 + -(1 / t)) ^ B.card := by
      refine one_add_mul_le_pow ?_ _
      have : 1 / t ≤ 1 := by rw [div_le_one ht0]; linarith
      linarith
    have h3 : (B.card : ℝ) / t ≤ 1 / Real.log t := by
      rw [div_le_div_iff₀ ht0 hlt]; linarith
    have e1 : 1 + (B.card : ℝ) * (-(1 / t)) = 1 - B.card / t := by ring
    rw [e1, ← sub_eq_add_neg] at h2
    linarith
  have hP0 : 0 ≤ primeProd t := (primeProd_pos t).le
  have hL0 : 0 ≤ 1 - 1 / Real.log t := by rw [sub_nonneg, div_le_one hlt]; exact ht
  calc (1 - 1 / Real.log t) * primeProd t
      ≤ (∏ p ∈ B, (1 - 1 / (p : ℝ))) * ∏ p ∈ A, (1 - 1 / (p : ℝ)) :=
        mul_le_mul hB hA hP0 (hL0.trans hB)
    _ = _ := mul_comm _ _

lemma tendsto_primeProd_mul_log_nat :
    Tendsto (fun n : ℕ ↦ primeProd (Real.log n) * Real.log (Real.log n)) atTop
      (𝓝 (Real.exp (-γ))) :=
  tendsto_prod_one_sub_inv_primes_mul_log.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- Theorem 328, lower half: eventually `φ(n) log log n / n ≥ (1 - ε) e^{-γ}`. -/
theorem eventually_totient_mul_log_log_div_ge {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (1 - ε) * Real.exp (-γ) ≤ (n.totient : ℝ) * Real.log (Real.log n) / n := by
  have hG : Tendsto (fun n : ℕ ↦ (1 - 1 / Real.log (Real.log n)) *
      (primeProd (Real.log n) * Real.log (Real.log n))) atTop (𝓝 ((1 - 0) * Real.exp (-γ))) :=
    (tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop tendsto_loglog_nat)).mul
      tendsto_primeProd_mul_log_nat
  have hlt : (1 - ε) * Real.exp (-γ) < (1 - 0) * Real.exp (-γ) := by
    have := Real.exp_pos (-γ)
    nlinarith
  filter_upwards [(tendsto_order.1 hG).1 _ hlt, tendsto_loglog_nat.eventually_ge_atTop 1,
    eventually_ne_atTop 0] with n h1 h2 h3
  have hLL : 0 ≤ Real.log (Real.log n) := by linarith
  have h4 := mul_le_mul_of_nonneg_right (totient_div_ge h3 h2) hLL
  have e : (n.totient : ℝ) * Real.log (Real.log n) / n =
      (n.totient : ℝ) / n * Real.log (Real.log n) := by ring
  rw [e]
  calc (1 - ε) * Real.exp (-γ) ≤ (1 - 1 / Real.log (Real.log n)) *
        (primeProd (Real.log n) * Real.log (Real.log n)) := h1.le
    _ = (1 - 1 / Real.log (Real.log n)) * primeProd (Real.log n) *
        Real.log (Real.log n) := by ring
    _ ≤ _ := h4

/-- The product of the primes `p ≤ m`. -/
def primorialIoc (m : ℕ) : ℕ := ∏ p ∈ (Ioc 0 m).filter Nat.Prime, p

lemma primes_Ioc (m : ℕ) : ∀ p ∈ (Ioc 0 m).filter Nat.Prime, p.Prime :=
  fun _ hp ↦ (mem_filter.1 hp).2

lemma primorialIoc_pos (m : ℕ) : 0 < primorialIoc m :=
  prod_pos fun p hp ↦ (primes_Ioc m p hp).pos

lemma log_primorialIoc (m : ℕ) : Real.log (primorialIoc m) = θ m := by
  rw [primorialIoc, Nat.cast_prod, Real.log_prod (fun p hp ↦ by
    exact_mod_cast (primes_Ioc m p hp).ne_zero), theta, Nat.floor_natCast]

lemma totient_primorialIoc (m : ℕ) :
    ((primorialIoc m).totient : ℝ) / primorialIoc m = primeProd m := by
  rw [totient_div_eq_prod (primorialIoc_pos m).ne', primorialIoc,
    Nat.primeFactors_prod (primes_Ioc m), primeProd, Nat.floor_natCast]

/-- Theorem 328, upper half: frequently `φ(n) log log n / n ≤ (1 + ε) e^{-γ}`. -/
theorem frequently_totient_mul_log_log_div_le {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ n : ℕ in atTop,
      (n.totient : ℝ) * Real.log (Real.log n) / n ≤ (1 + ε) * Real.exp (-γ) := by
  set c := Real.log (Real.log 4)
  have hlog : Tendsto (fun m : ℕ ↦ Real.log m) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hH : Tendsto (fun m : ℕ ↦ (primeProd m * Real.log m) * (1 + c / Real.log m)) atTop
      (𝓝 (Real.exp (-γ) * (1 + 0))) :=
    (tendsto_prod_one_sub_inv_primes_mul_log.comp tendsto_natCast_atTop_atTop).mul
      (tendsto_const_nhds.add (tendsto_const_nhds.div_atTop hlog))
  have hlt : Real.exp (-γ) * (1 + 0) < (1 + ε) * Real.exp (-γ) := by
    have := Real.exp_pos (-γ)
    nlinarith
  have hev : ∀ᶠ m : ℕ in atTop, ((primorialIoc m).totient : ℝ) *
      Real.log (Real.log (primorialIoc m)) / primorialIoc m ≤ (1 + ε) * Real.exp (-γ) := by
    filter_upwards [(tendsto_order.1 hH).2 _ hlt, eventually_ge_atTop 2] with m h1 hm
    have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have hθ : 0 < θ (m : ℝ) := theta_pos hm2
    have hθle : θ (m : ℝ) ≤ Real.log 4 * m := theta_le_log4_mul_x (by linarith)
    have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
    have hlogm : 0 < Real.log m := Real.log_pos (by linarith)
    have hLL : Real.log (Real.log (primorialIoc m)) ≤ Real.log m + c := by
      rw [log_primorialIoc]
      calc Real.log (θ m) ≤ Real.log (Real.log 4 * m) := Real.log_le_log hθ hθle
        _ = Real.log m + c := by rw [Real.log_mul hlog4.ne' (by linarith)]; ring
    have e : ((primorialIoc m).totient : ℝ) * Real.log (Real.log (primorialIoc m)) /
        primorialIoc m = primeProd m * Real.log (Real.log (primorialIoc m)) := by
      rw [← totient_primorialIoc m]; ring
    rw [e]
    have e2 : primeProd m * Real.log m * (1 + c / Real.log m) =
        primeProd m * (Real.log m + c) := by field_simp
    have h3 := mul_le_mul_of_nonneg_left hLL (primeProd_pos m).le
    unfold primeProd at e2 h3 ⊢
    linarith [e2 ▸ h1.le]
  rw [frequently_atTop]
  intro a
  obtain ⟨p, hap, hp⟩ := Nat.exists_infinite_primes a
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.1 hev
  refine ⟨primorialIoc (max m₀ p), ?_, hm₀ _ (le_max_left _ _)⟩
  have hpm : p ∈ (Ioc 0 (max m₀ p)).filter Nat.Prime :=
    mem_filter.2 ⟨mem_Ioc.2 ⟨hp.pos, le_max_right _ _⟩, hp⟩
  exact hap.trans (Nat.le_of_dvd (primorialIoc_pos _) (dvd_prod_of_mem _ hpm))

/-- Theorem 323, upper half: eventually `σ(n) / (n log log n) ≤ (1 + ε) e^γ`. -/
theorem eventually_sigma_div_mul_log_log_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (σ 1 n : ℝ) / (n * Real.log (Real.log n)) ≤ (1 + ε) * Real.exp γ := by
  have hε' : 0 < ε / (1 + ε) := by positivity
  obtain ⟨A, -, h329⟩ : ∃ A > 0, ∀ n : ℕ, 1 < n →
      A < (σ 1 n : ℝ) * n.totient / (n : ℝ) ^ 2 ∧ (σ 1 n : ℝ) * n.totient / (n : ℝ) ^ 2 < 1 :=
    exists_lt_sigma_mul_totient_div_sq
  filter_upwards [eventually_totient_mul_log_log_div_ge hε', eventually_ge_atTop 2,
    tendsto_loglog_nat.eventually_gt_atTop 0] with n h1 hn hLL
  have hE := Real.exp_pos (-γ)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hφ : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
  have ha : 0 < (n.totient : ℝ) * Real.log (Real.log n) / n := by positivity
  have h2 := (h329 n (by omega)).2
  have e1 : 1 - ε / (1 + ε) = 1 / (1 + ε) := by field_simp; ring
  rw [e1] at h1
  have e2 : (σ 1 n : ℝ) / (n * Real.log (Real.log n)) =
      ((σ 1 n : ℝ) * n.totient / (n : ℝ) ^ 2) /
        ((n.totient : ℝ) * Real.log (Real.log n) / n) := by
    field_simp
  rw [e2, div_le_iff₀ ha]
  have h3 : (1 + ε) * Real.exp γ * (1 / (1 + ε) * Real.exp (-γ)) = 1 := by
    rw [Real.exp_neg]; field_simp
  have h4 : (1 + ε) * Real.exp γ * (1 / (1 + ε) * Real.exp (-γ)) ≤
      (1 + ε) * Real.exp γ * ((n.totient : ℝ) * Real.log (Real.log n) / n) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  linarith

/-- `1 - ∑ a_i ≤ ∏ (1 - a_i)` for `0 ≤ a_i ≤ 1`. -/
lemma one_sub_sum_le_prod {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ 1) : 1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [sum_insert hi, prod_insert hi]
    have hai := ha i (mem_insert_self i s)
    have ih' := ih fun j hj ↦ ha j (mem_insert_of_mem hj)
    have hs : 0 ≤ ∑ j ∈ s, a j := sum_nonneg fun j hj ↦ (ha j (mem_insert_of_mem hj)).1
    nlinarith

lemma sigma_prime_pow_div {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (σ 1 (p ^ k) : ℝ) / (p : ℝ) ^ k = (1 - 1 / (p : ℝ) ^ (k + 1)) / (1 - 1 / (p : ℝ)) := by
  rw [sigma_one_apply_prime_pow hp]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hgeom : (∑ i ∈ range (k + 1), (p : ℝ) ^ i) * (p - 1) = (p : ℝ) ^ (k + 1) - 1 :=
    geom_sum_mul _ _
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hp1' : (p : ℝ) - 1 ≠ 0 := by linarith
  push_cast
  have hd : 1 - 1 / (p : ℝ) ≠ 0 := by
    have : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; exact hp1
    exact ne_of_gt (by linarith)
  have e1 : 1 - 1 / (p : ℝ) = ((p : ℝ) - 1) / p := by field_simp
  have e2 : 1 - 1 / (p : ℝ) ^ (k + 1) = ((p : ℝ) ^ (k + 1) - 1) / (p : ℝ) ^ (k + 1) := by
    field_simp
  rw [div_eq_div_iff (pow_ne_zero _ hp0) hd, e1, e2, ← hgeom]
  field_simp
  ring

/-- `n_j = ∏_{p ≤ 2^j} p^{2j}`. -/
def sigmaSeq (j : ℕ) : ℕ := ∏ p ∈ (Ioc 0 (2 ^ j)).filter Nat.Prime, p ^ (2 * j)

lemma sigmaSeq_pos (j : ℕ) : 0 < sigmaSeq j :=
  prod_pos fun p hp ↦ pow_pos (primes_Ioc _ p hp).pos _

lemma sigma_sigmaSeq (j : ℕ) :
    (σ 1 (sigmaSeq j) : ℝ) / sigmaSeq j =
      ∏ p ∈ (Ioc 0 (2 ^ j)).filter Nat.Prime,
        ((1 - 1 / (p : ℝ) ^ (2 * j + 1)) / (1 - 1 / (p : ℝ))) := by
  rw [sigmaSeq, IsMultiplicative.map_prod (fun p ↦ p ^ (2 * j)) isMultiplicative_sigma]
  · push_cast
    rw [← prod_div_distrib]
    refine prod_congr rfl fun p hp ↦ ?_
    rw [← sigma_prime_pow_div (primes_Ioc _ p hp)]
  · intro p hp q hq hpq
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (primes_Ioc _ p hp) (primes_Ioc _ q hq)).2 hpq)

lemma log_sigmaSeq (j : ℕ) : Real.log (sigmaSeq j) = 2 * j * θ ((2 ^ j : ℕ) : ℝ) := by
  rw [sigmaSeq, Nat.cast_prod, Real.log_prod (fun p hp ↦ by
    exact_mod_cast pow_ne_zero _ (primes_Ioc _ p hp).ne_zero), theta, Nat.floor_natCast,
    mul_sum]
  refine sum_congr rfl fun p _ ↦ ?_
  push_cast
  rw [Real.log_pow]
  push_cast
  ring

/-- Theorem 323, lower half: frequently `σ(n) / (n log log n) ≥ (1 - ε) e^γ`. -/
theorem frequently_sigma_div_mul_log_log_ge {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ n : ℕ in atTop, (1 - ε) * Real.exp γ ≤ (σ 1 n : ℝ) / (n * Real.log (Real.log n)) := by
  set c := Real.log (Real.log 4)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h2j : Tendsto (fun j : ℕ ↦ ((2 ^ j : ℕ) : ℝ)) atTop atTop := by
    have := tendsto_pow_atTop_atTop_of_one_lt (one_lt_two (α := ℕ))
    exact tendsto_natCast_atTop_atTop.comp this
  have hP : Tendsto (fun j : ℕ ↦ primeProd ((2 ^ j : ℕ) : ℝ) * Real.log ((2 ^ j : ℕ) : ℝ)) atTop
      (𝓝 (Real.exp (-γ))) := tendsto_prod_one_sub_inv_primes_mul_log.comp h2j
  have hjat : Tendsto (fun j : ℕ ↦ (j : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  -- `log (2j) / j → 0`
  have hl : Tendsto (fun j : ℕ ↦ Real.log (2 * j) / j) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop (1 / 2) 0 1 (by norm_num)).comp
      ((tendsto_id.const_mul_atTop two_pos).comp hjat)
    refine h.congr' ?_
    filter_upwards with j
    simp only [Function.comp, id, pow_one]
    ring_nf
  have hU : Tendsto (fun j : ℕ ↦ 1 + (Real.log (2 * j) / j + c / j) / Real.log 2) atTop
      (𝓝 (1 + (0 + 0) / Real.log 2)) :=
    tendsto_const_nhds.add ((hl.add (tendsto_const_nhds.div_atTop hjat)).div_const _)
  have hnum : Tendsto (fun j : ℕ ↦ 1 - 1 / (2 : ℝ) ^ j) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two))
  have hK := hnum.div (hP.mul hU) (by simp [Real.exp_ne_zero])
  have hlim : (1 - 0) / (Real.exp (-γ) * (1 + (0 + 0) / Real.log 2)) = Real.exp γ := by
    simp [Real.exp_neg]
  rw [hlim] at hK
  have hlt : (1 - ε) * Real.exp γ < Real.exp γ := by
    have := Real.exp_pos γ
    nlinarith
  have hev : ∀ᶠ j : ℕ in atTop, (1 - ε) * Real.exp γ ≤
      (σ 1 (sigmaSeq j) : ℝ) / (sigmaSeq j * Real.log (Real.log (sigmaSeq j))) := by
    filter_upwards [(tendsto_order.1 hK).1 _ hlt, eventually_ge_atTop 2] with j h1 hj
    have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast hj
    set T := (Ioc 0 (2 ^ j)).filter Nat.Prime
    have hpow2 : ((2 ^ j : ℕ) : ℝ) = (2 : ℝ) ^ j := by push_cast; ring
    have h2jr : (4 : ℝ) ≤ (2 : ℝ) ^ j := by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ j := pow_le_pow_right₀ one_le_two hj
    -- the factor `∏ (1 - p^{-(2j+1)}) ≥ 1 - 2^{-j}`
    have hQ : 1 - 1 / (2 : ℝ) ^ j ≤ ∏ p ∈ T, (1 - 1 / (p : ℝ) ^ (2 * j + 1)) := by
      refine le_trans ?_ (one_sub_sum_le_prod T _ fun p hp ↦ ⟨by positivity, ?_⟩)
      · have hterm : ∀ p ∈ T, 1 / (p : ℝ) ^ (2 * j + 1) ≤ 1 / (2 : ℝ) ^ (2 * j + 1) := by
          intro p hp
          have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (primes_Ioc _ p hp).two_le
          exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by norm_num) h2 _)
        have hcard : (T.card : ℝ) ≤ (2 : ℝ) ^ j := by
          have : T.card ≤ 2 ^ j := (card_filter_le _ _).trans (by simp)
          exact_mod_cast this
        have hs := sum_le_sum hterm
        rw [sum_const, nsmul_eq_mul] at hs
        have e : (2 : ℝ) ^ j * (1 / (2 : ℝ) ^ (2 * j + 1)) = 1 / (2 : ℝ) ^ (j + 1) := by
          rw [show 2 * j + 1 = j + (j + 1) by ring, pow_add]; field_simp
        have h3 : (T.card : ℝ) * (1 / (2 : ℝ) ^ (2 * j + 1)) ≤ 1 / (2 : ℝ) ^ (j + 1) := by
          rw [← e]; exact mul_le_mul_of_nonneg_right hcard (by positivity)
        have h4 : 1 / (2 : ℝ) ^ (j + 1) ≤ 1 / (2 : ℝ) ^ j :=
          one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ one_le_two (by omega))
        linarith
      · have h2 : (1 : ℝ) ≤ (p : ℝ) ^ (2 * j + 1) := one_le_pow₀ (by
          exact_mod_cast (primes_Ioc _ p hp).one_lt.le)
        rw [div_le_one (by linarith)]; exact h2
    -- `log log n_j ≤ j log 2 + log (2j) + log log 4`
    have hθ : 0 < θ ((2 ^ j : ℕ) : ℝ) := theta_pos (by rw [hpow2]; linarith)
    have hθle : θ ((2 ^ j : ℕ) : ℝ) ≤ Real.log 4 * (2 : ℝ) ^ j := by
      rw [← hpow2]; exact theta_le_log4_mul_x (by positivity)
    have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
    have hlogM : 0 < Real.log (sigmaSeq j) := by
      rw [log_sigmaSeq]; positivity
    have hLL : Real.log (Real.log (sigmaSeq j)) ≤
        j * Real.log 2 + Real.log (2 * j) + c := by
      rw [log_sigmaSeq]
      calc Real.log (2 * j * θ ((2 ^ j : ℕ) : ℝ))
          ≤ Real.log (2 * j * (Real.log 4 * (2 : ℝ) ^ j)) :=
            Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left hθle (by positivity))
        _ = _ := by
            rw [Real.log_mul (by positivity) (by positivity),
              Real.log_mul hlog4.ne' (by positivity), Real.log_pow]
            ring
    have hLLpos : 0 < Real.log (Real.log (sigmaSeq j)) := by
      have : 1 < Real.log (sigmaSeq j) := by
        rw [log_sigmaSeq]
        -- `θ(2^j) ≥ log 2`, so `2 j θ(2^j) ≥ 4 log 2 > 1`
        have h2mem : (2 : ℕ) ∈ T := mem_filter.2
          ⟨mem_Ioc.2 ⟨two_pos, by have := Nat.lt_two_pow_self (n := j); omega⟩,
            Nat.prime_two⟩
        have hle : Real.log 2 ≤ θ ((2 ^ j : ℕ) : ℝ) := by
          rw [theta, Nat.floor_natCast]
          exact single_le_sum (f := fun p : ℕ ↦ Real.log p)
            (fun p _ ↦ Real.log_natCast_nonneg p) h2mem
        have := Real.log_two_gt_d9
        nlinarith
      exact Real.log_pos this
    -- the value
    have hsig := sigma_sigmaSeq j
    rw [prod_div_distrib] at hsig
    have hPj : ∏ p ∈ T, (1 - 1 / (p : ℝ)) = primeProd ((2 ^ j : ℕ) : ℝ) := by
      rw [primeProd, Nat.floor_natCast]
    rw [hPj] at hsig
    have hPpos := primeProd_pos ((2 ^ j : ℕ) : ℝ)
    have hMpos : (0 : ℝ) < sigmaSeq j := by exact_mod_cast sigmaSeq_pos j
    have hval : (σ 1 (sigmaSeq j) : ℝ) / (sigmaSeq j * Real.log (Real.log (sigmaSeq j))) =
        (∏ p ∈ T, (1 - 1 / (p : ℝ) ^ (2 * j + 1))) / primeProd ((2 ^ j : ℕ) : ℝ) /
          Real.log (Real.log (sigmaSeq j)) := by
      rw [← hsig, div_div]
    rw [hval]
    have hU' : j * Real.log 2 + Real.log (2 * j) + c =
        Real.log ((2 ^ j : ℕ) : ℝ) * (1 + (Real.log (2 * j) / j + c / j) / Real.log 2) := by
      rw [hpow2, Real.log_pow]
      have : (j : ℝ) ≠ 0 := by linarith
      field_simp
      ring
    have hUpos : 0 < j * Real.log 2 + Real.log (2 * j) + c := lt_of_lt_of_le hLLpos hLL
    calc (1 - ε) * Real.exp γ ≤ (1 - 1 / (2 : ℝ) ^ j) /
          (primeProd ((2 ^ j : ℕ) : ℝ) * Real.log ((2 ^ j : ℕ) : ℝ) *
            (1 + (Real.log (2 * j) / j + c / j) / Real.log 2)) := h1.le
      _ = (1 - 1 / (2 : ℝ) ^ j) / primeProd ((2 ^ j : ℕ) : ℝ) /
            (j * Real.log 2 + Real.log (2 * j) + c) := by
          rw [hU', div_div, mul_assoc]
      _ ≤ (∏ p ∈ T, (1 - 1 / (p : ℝ) ^ (2 * j + 1))) / primeProd ((2 ^ j : ℕ) : ℝ) /
            (j * Real.log 2 + Real.log (2 * j) + c) := by
          gcongr
      _ ≤ _ := by
          refine div_le_div_of_nonneg_left ?_ hLLpos hLL
          have : 0 ≤ 1 - 1 / (2 : ℝ) ^ j := by
            rw [sub_nonneg, div_le_one (by positivity)]; exact one_le_pow₀ one_le_two
          exact div_nonneg (this.trans hQ) hPpos.le
  rw [frequently_atTop]
  intro a
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 hev
  refine ⟨sigmaSeq (max j₀ a + 1), ?_, hj₀ _ (by omega)⟩
  set j := max j₀ a + 1
  have h2j : 2 ≤ 2 ^ j := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right two_pos (by omega)
  have h2mem : (2 : ℕ) ∈ (Ioc 0 (2 ^ j)).filter Nat.Prime := mem_filter.2
    ⟨mem_Ioc.2 ⟨two_pos, h2j⟩, Nat.prime_two⟩
  have hdvd : 2 ^ (2 * j) ∣ sigmaSeq j := dvd_prod_of_mem (fun p ↦ p ^ (2 * j)) h2mem
  have h1 := Nat.le_of_dvd (sigmaSeq_pos j) hdvd
  have h2 : j < 2 ^ (2 * j) := (Nat.lt_two_pow_self).trans_le
    (Nat.pow_le_pow_right two_pos (by omega))
  have : a ≤ j := by omega
  omega

end ExtremalOrder

open ExtremalOrder

/-- **Theorem 328** (proved in § 22.9). `liminf φ(n) log log n / n = e^{-γ}`. -/
@[kb "hardywright2008" "Thm 328, p. 371"]
theorem liminf_totient_mul_log_log_div :
    liminf (fun n : ℕ ↦ (n.totient : ℝ) * Real.log (Real.log n) / n) atTop = Real.exp (-γ) := by
  set u := fun n : ℕ ↦ (n.totient : ℝ) * Real.log (Real.log n) / n
  have hE : 0 < Real.exp (-γ) := Real.exp_pos _
  have hbdd : IsBoundedUnder (· ≥ ·) atTop u := by
    refine isBoundedUnder_of_eventually_ge (a := 0) ?_
    filter_upwards [eventually_totient_mul_log_log_div_ge one_pos] with n hn
    simpa using hn
  have hcobdd : IsCoboundedUnder (· ≥ ·) atTop u := ⟨2 * Real.exp (-γ), fun a ha ↦ by
    obtain ⟨n, hn1, hn2⟩ := ((frequently_totient_mul_log_log_div_le one_pos).and_eventually ha).exists
    have : a ≤ u n := hn2
    show a ≤ 2 * Real.exp (-γ)
    linarith⟩
  apply le_antisymm
  · refine le_of_forall_pos_le_add fun δ hδ ↦ ?_
    refine liminf_le_of_frequently_le ?_ hbdd
    refine (frequently_totient_mul_log_log_div_le (div_pos hδ hE)).mono fun n hn ↦ ?_
    refine hn.trans (le_of_eq ?_)
    field_simp
  · refine le_of_forall_pos_le_add fun δ hδ ↦ ?_
    have h := le_liminf_of_le hcobdd (eventually_totient_mul_log_log_div_ge (div_pos hδ hE))
    have e : (1 - δ / Real.exp (-γ)) * Real.exp (-γ) = Real.exp (-γ) - δ := by
      field_simp
    linarith

/-- **Theorem 323** (Gronwall; proved in § 22.9). `limsup σ(n) / (n log log n) = e^γ`. -/
@[kb "hardywright2008" "Thm 323, p. 369"]
theorem limsup_sigma_div_mul_log_log :
    limsup (fun n : ℕ ↦ (σ 1 n : ℝ) / (n * Real.log (Real.log n))) atTop = Real.exp γ := by
  set v := fun n : ℕ ↦ (σ 1 n : ℝ) / (n * Real.log (Real.log n))
  have hE : 0 < Real.exp γ := Real.exp_pos _
  have hbdd : IsBoundedUnder (· ≤ ·) atTop v :=
    isBoundedUnder_of_eventually_le (eventually_sigma_div_mul_log_log_le one_pos)
  have hge : IsBoundedUnder (· ≥ ·) atTop v := by
    refine isBoundedUnder_of_eventually_ge (a := 0) ?_
    filter_upwards [tendsto_loglog_nat.eventually_gt_atTop 0] with n hn
    show 0 ≤ (σ 1 n : ℝ) / (n * Real.log (Real.log n))
    positivity
  apply le_antisymm
  · refine le_of_forall_pos_le_add fun δ hδ ↦ ?_
    refine limsup_le_of_le hge.isCoboundedUnder_le ?_
    refine (eventually_sigma_div_mul_log_log_le (div_pos hδ hE)).mono fun n hn ↦ ?_
    refine hn.trans (le_of_eq ?_)
    field_simp
  · refine le_of_forall_pos_le_add fun δ hδ ↦ ?_
    have h := le_limsup_of_frequently_le
      (frequently_sigma_div_mul_log_log_ge (div_pos hδ hE)) hbdd
    have e : (1 - δ / Real.exp γ) * Real.exp γ = Real.exp γ - δ := by
      field_simp
    linarith

end NTKB.HardyWright
