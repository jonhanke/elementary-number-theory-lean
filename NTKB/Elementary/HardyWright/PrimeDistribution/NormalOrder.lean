/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.PrimeDistribution.Mertens
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The average and normal order of `ω(n)` and `Ω(n)`
(Hardy–Wright, Chapter XXII, §§ 22.10–22.11)

* **Theorem 430**: `∑_{n ≤ x} ω(n) = x log log x + B₁ x + o(x)` and
  `∑_{n ≤ x} Ω(n) = x log log x + B₂ x + o(x)`.
  Proof: `∑_{n ≤ x} ω(n) = ∑_{p ≤ x} ⌊x/p⌋`, which lies between `x ∑_{p ≤ x} 1/p - π(x)` and
  `x ∑_{p ≤ x} 1/p`; then Theorem 427 and `π(x) = o(x)`.  For `Ω` one adds
  `∑_{p^m ≤ x, m ≥ 2} ⌊x/p^m⌋ = x ∑_{p, m ≥ 2} p^{-m} + o(x)`, obtained by dominated convergence
  from `⌊x/q⌋ / x → 1/q`.
* **Theorem 431** (Hardy–Ramanujan, Turán's proof): `∑_{n ≤ x} (ω(n) - log log x)² ≤ C x log log x`
  for `x ≥ 3`, from `∑ ω(n)² ≤ x (∑_{p ≤ x} 1/p)² + x ∑_{p ≤ x} 1/p` and Theorem 4.12; hence
  the number of `n ≤ x` with `|ω(n) - log log n| > ε log log n` is `o(x)`.  The same holds for
  `Ω`, since `∑_{n ≤ x} (Ω(n) - ω(n)) = O(x)`.
-/

open Finset ArithmeticFunction Real Filter
open scoped Topology ArithmeticFunction.omega ArithmeticFunction.Omega

namespace NTKB.HardyWright

open NTKB.Apostol

/-! ### Counting identities -/

/-- The primes up to `N`. -/
private abbrev primesLE (N : ℕ) : Finset ℕ := (Ioc 0 N).filter Nat.Prime

private lemma cardDistinctFactors_eq_sum {N n : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    ω n = ∑ p ∈ primesLE N, if p ∣ n then 1 else 0 := by
  rw [cardDistinctFactors_eq_card_primeFactors, ← Finset.card_filter]
  congr 1
  ext p
  simp only [Nat.mem_primeFactors, mem_filter, mem_Ioc]
  constructor
  · rintro ⟨hp, hpn, -⟩
    exact ⟨⟨⟨hp.pos, (Nat.le_of_dvd hn hpn).trans hnN⟩, hp⟩, hpn⟩
  · rintro ⟨⟨-, hp⟩, hpn⟩
    exact ⟨hp, hpn, hn.ne'⟩

private lemma cardFactors_eq_sum {N n : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    Ω n = ∑ p ∈ primesLE N, ∑ m ∈ Ioc 0 N, if p ^ m ∣ n then 1 else 0 := by
  rw [cardFactors_eq_sum_factorization,
    Finsupp.sum_of_support_subset (s := primesLE N) _ ?_ _ (fun _ _ ↦ rfl)]
  · refine Finset.sum_congr rfl fun p hp ↦ ?_
    have hpp : p.Prime := (mem_filter.1 hp).2
    simp_rw [hpp.pow_dvd_iff_le_factorization hn.ne']
    have hv : n.factorization p < N + 1 :=
      Nat.lt_succ_of_le ((Nat.factorization_lt p hn.ne').le.trans hnN)
    rw [← Finset.card_filter]
    have : (Ioc 0 N).filter (fun m ↦ m ≤ n.factorization p) = Ioc 0 (n.factorization p) := by
      ext m; simp only [mem_filter, mem_Ioc]; omega
    rw [this]; simp
  · intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    simp only [mem_filter, mem_Ioc]
    exact ⟨⟨hp.1.pos, (Nat.le_of_dvd hn hp.2.1).trans hnN⟩, hp.1⟩

private lemma sum_cardDistinctFactors (N : ℕ) :
    ∑ n ∈ Ioc 0 N, ω n = ∑ p ∈ primesLE N, N / p := by
  rw [Finset.sum_congr rfl fun n hn ↦
    cardDistinctFactors_eq_sum (N := N) (mem_Ioc.1 hn).1 (mem_Ioc.1 hn).2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [← Nat.Ioc_filter_dvd_card_eq_div, Finset.card_filter]

private lemma sum_cardFactors (N : ℕ) :
    ∑ n ∈ Ioc 0 N, Ω n = ∑ p ∈ primesLE N, ∑ m ∈ Ioc 0 N, N / p ^ m := by
  rw [Finset.sum_congr rfl fun n hn ↦
    cardFactors_eq_sum (N := N) (mem_Ioc.1 hn).1 (mem_Ioc.1 hn).2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [← Nat.Ioc_filter_dvd_card_eq_div, Finset.card_filter]

private lemma card_primesLE (N : ℕ) : (primesLE N).card = Nat.primeCounting N := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  congr 1
  ext p
  simp only [mem_filter, mem_Ioc, mem_range]
  constructor
  · rintro ⟨h, hp⟩; exact ⟨by omega, hp⟩
  · rintro ⟨h, hp⟩; exact ⟨⟨hp.pos, by omega⟩, hp⟩

private lemma cast_div_eq_floor (x : ℝ) (q : ℕ) :
    (((⌊x⌋₊ / q : ℕ)) : ℝ) = (⌊x / (q : ℝ)⌋₊ : ℝ) := by
  rw [Nat.floor_div_natCast]

private lemma sum_floor_bounds {x : ℝ} (hx : 0 ≤ x) :
    x * ∑ p ∈ primesLE ⌊x⌋₊, (1 : ℝ) / p - Nat.primeCounting ⌊x⌋₊ ≤
        ∑ p ∈ primesLE ⌊x⌋₊, (((⌊x⌋₊ / p : ℕ)) : ℝ) ∧
      ∑ p ∈ primesLE ⌊x⌋₊, (((⌊x⌋₊ / p : ℕ)) : ℝ) ≤ x * ∑ p ∈ primesLE ⌊x⌋₊, (1 : ℝ) / p := by
  have hp : ∀ p ∈ primesLE ⌊x⌋₊, 0 < (p : ℝ) := fun p hp ↦
    Nat.cast_pos.2 (Nat.Prime.pos (mem_filter.1 hp).2)
  constructor
  · have h1 : ∑ p ∈ primesLE ⌊x⌋₊, (x * (1 / (p : ℝ)) - 1) ≤
        ∑ p ∈ primesLE ⌊x⌋₊, (((⌊x⌋₊ / p : ℕ)) : ℝ) := by
      refine Finset.sum_le_sum fun p hpp ↦ ?_
      rw [cast_div_eq_floor]
      have := Nat.lt_floor_add_one (x / p)
      have e : x * (1 / (p : ℝ)) = x / p := by ring
      rw [e]; linarith
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, card_primesLE,
      nsmul_eq_mul, mul_one] at h1
    exact h1
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun p hpp ↦ ?_
    rw [cast_div_eq_floor]
    have := Nat.floor_le (div_nonneg hx (hp p hpp).le)
    calc _ ≤ x / p := this
      _ = x * (1 / p) := by ring

/-- **Theorem 430.** (For `ω`.) `∑_{n ≤ x} ω(n) = x log log x + B₁ x + o(x)`. -/
@[kb "hardywright2008" "Thm 430, p. 491"]
theorem tendsto_sum_cardDistinctFactors_sub :
    ∃ B₁ : ℝ, Tendsto
      (fun x : ℝ ↦ ((∑ n ∈ Ioc 0 ⌊x⌋₊, (ω n : ℝ)) - x * Real.log (Real.log x) - B₁ * x) / x)
      atTop (𝓝 0) := by
  obtain ⟨B, hB⟩ := tendsto_sum_inv_primes_sub_log_log
  refine ⟨B, ?_⟩
  have hπ := tendsto_primeCounting_div_self
  have key : ∀ x : ℝ, 0 < x →
      ((∑ n ∈ Ioc 0 ⌊x⌋₊, (ω n : ℝ)) - x * Real.log (Real.log x) - B * x) / x =
        (∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 : ℝ) / p - Real.log (Real.log x) - B) -
          (x * ∑ p ∈ primesLE ⌊x⌋₊, (1 : ℝ) / p - ∑ n ∈ Ioc 0 ⌊x⌋₊, (ω n : ℝ)) / x := by
    intro x hx
    field_simp
    ring
  have h2 : Tendsto (fun x : ℝ ↦
      (x * ∑ p ∈ primesLE ⌊x⌋₊, (1 : ℝ) / p - ∑ n ∈ Ioc 0 ⌊x⌋₊, (ω n : ℝ)) / x)
      atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hπ
    · filter_upwards [eventually_gt_atTop 0] with x hx
      refine div_nonneg ?_ hx.le
      have := (sum_floor_bounds hx.le).2
      have e : ∑ n ∈ Ioc 0 ⌊x⌋₊, (ω n : ℝ) =
          ∑ p ∈ primesLE ⌊x⌋₊, (((⌊x⌋₊ / p : ℕ)) : ℝ) := by
        rw [← Nat.cast_sum, sum_cardDistinctFactors]; push_cast; rfl
      rw [e]; linarith
    · filter_upwards [eventually_gt_atTop 0] with x hx
      refine div_le_div_of_nonneg_right ?_ hx.le
      have := (sum_floor_bounds hx.le).1
      have e : ∑ n ∈ Ioc 0 ⌊x⌋₊, (ω n : ℝ) =
          ∑ p ∈ primesLE ⌊x⌋₊, (((⌊x⌋₊ / p : ℕ)) : ℝ) := by
        rw [← Nat.cast_sum, sum_cardDistinctFactors]; push_cast; rfl
      rw [e]; linarith
  have := hB.sub h2
  rw [sub_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  exact (key x hx).symm

/-! ### The prime powers with exponent at least two -/

private lemma sum_cardFactors_split (N : ℕ) :
    ∑ n ∈ Ioc 0 N, Ω n = ∑ n ∈ Ioc 0 N, ω n +
      ∑ p ∈ primesLE N, ∑ m ∈ Ioc 0 N, if 2 ≤ m then N / p ^ m else 0 := by
  rcases N.eq_zero_or_pos with rfl | hN
  · simp
  rw [sum_cardFactors, sum_cardDistinctFactors, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  have : ∀ m ∈ Ioc 0 N, N / p ^ m =
      (if m = 1 then N / p else 0) + (if 2 ≤ m then N / p ^ m else 0) := by
    intro m hm
    have := (mem_Ioc.1 hm).1
    by_cases h1 : m = 1
    · subst h1; simp
    · have : 2 ≤ m := by omega
      simp [h1, this]
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_ite_eq']
  have h1 : (1 : ℕ) ∈ Ioc 0 N := by simp only [mem_Ioc]; omega
  simp [h1]

/-- The terms `∑_{p, m ≥ 2} p^{-m}`. -/
private noncomputable def tailTerm (k : ℕ × ℕ) : ℝ :=
  if k.1.Prime ∧ 2 ≤ k.2 then 1 / (k.1 : ℝ) ^ k.2 else 0

private lemma tailTerm_nonneg (k : ℕ × ℕ) : 0 ≤ tailTerm k := by
  unfold tailTerm; split_ifs <;> positivity

private lemma summable_tailTerm : Summable tailTerm := by
  have hf : Summable fun p : ℕ ↦ 4 * (1 / (p : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow.2 one_lt_two).mul_left 4
  have hg : Summable fun m : ℕ ↦ (1 / 2 : ℝ) ^ m := summable_geometric_two
  have hb := Summable.mul_of_nonneg hf hg (fun p ↦ by positivity) (fun m ↦ by positivity)
  refine Summable.of_nonneg_of_le tailTerm_nonneg (fun k ↦ ?_) hb
  obtain ⟨p, m⟩ := k
  unfold tailTerm
  dsimp only
  split_ifs with h
  · obtain ⟨hp, hm⟩ := h
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have h1 : (2 : ℝ) ^ j ≤ (p : ℝ) ^ j := pow_le_pow_left₀ (by norm_num) hp2 j
    have h2 : 1 / (p : ℝ) ^ j ≤ (1 / 2) ^ j := by
      rw [one_div_pow]
      exact one_div_le_one_div_of_le (by positivity) h1
    have hp0 : (0 : ℝ) < p := by linarith
    calc 1 / (p : ℝ) ^ (j + 2) = (1 / (p : ℝ) ^ 2) * (1 / (p : ℝ) ^ j) := by
          rw [pow_add]; field_simp
      _ ≤ (1 / (p : ℝ) ^ 2) * (1 / 2) ^ j := by gcongr
      _ = 4 * (1 / (p : ℝ) ^ 2) * (1 / 2) ^ (j + 2) := by rw [pow_add]; ring
  · positivity

private lemma tendsto_floor_div_nat {q : ℕ} (hq : 0 < q) :
    Tendsto (fun x : ℝ ↦ ((⌊x⌋₊ / q : ℕ) : ℝ) / x) atTop (𝓝 (1 / (q : ℝ))) := by
  have hq' : (0 : ℝ) < q := Nat.cast_pos.2 hq
  have h1 : Tendsto (fun x : ℝ ↦ x / (q : ℝ)) atTop atTop := tendsto_id.atTop_div_const hq'
  have h2 := (tendsto_nat_floor_div_atTop (R := ℝ)).comp h1
  have h3 := h2.mul_const (1 / (q : ℝ))
  rw [one_mul] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp only [Function.comp, cast_div_eq_floor]
  field_simp

/-- The tail contribution of prime powers with exponent at least two. -/
private noncomputable def powTail (x : ℝ) : ℝ :=
  ∑ p ∈ primesLE ⌊x⌋₊, ∑ m ∈ Ioc 0 ⌊x⌋₊, if 2 ≤ m then ((⌊x⌋₊ / p ^ m : ℕ) : ℝ) else 0

private lemma tendsto_powTail_div : Tendsto (fun x : ℝ ↦ powTail x / x) atTop (𝓝 (∑' k, tailTerm k)) := by
  set F : ℝ → ℕ × ℕ → ℝ := fun x k ↦
    if k.1.Prime ∧ 2 ≤ k.2 then ((⌊x⌋₊ / k.1 ^ k.2 : ℕ) : ℝ) / x else 0 with hF
  have hlim : Tendsto (fun x ↦ ∑' k, F x k) atTop (𝓝 (∑' k, tailTerm k)) := by
    refine tendsto_tsum_of_dominated_convergence summable_tailTerm ?_ ?_
    · intro k
      obtain ⟨p, m⟩ := k
      by_cases h : p.Prime ∧ 2 ≤ m
      · simp only [hF, tailTerm, h, and_self, ↓reduceIte]
        have := tendsto_floor_div_nat (q := p ^ m) (Nat.pow_pos h.1.pos)
        simpa using this
      · simp only [hF, tailTerm, h, ↓reduceIte]
        exact tendsto_const_nhds
    · filter_upwards [eventually_gt_atTop 0] with x hx k
      obtain ⟨p, m⟩ := k
      by_cases h : p.Prime ∧ 2 ≤ m
      · simp only [hF, tailTerm, h, and_self, ↓reduceIte]
        have hq : (0 : ℝ) < (p : ℝ) ^ m := pow_pos (Nat.cast_pos.2 h.1.pos) m
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_div_iff₀ hx hq]
        have := Nat.floor_le (div_nonneg hx.le hq.le)
        have e := cast_div_eq_floor x (p ^ m)
        push_cast at e
        rw [e]
        calc _ ≤ x / (p : ℝ) ^ m * (p : ℝ) ^ m := by gcongr
          _ = 1 * x := by field_simp
      · simp [hF, tailTerm, h]
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [tsum_eq_sum (s := Ioc 0 ⌊x⌋₊ ×ˢ Ioc 0 ⌊x⌋₊)]
  · rw [Finset.sum_product, powTail, Finset.sum_filter, Finset.sum_div]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    by_cases hpp : p.Prime
    · simp only [hF, hpp, ↓reduceIte, Finset.sum_div]
      refine Finset.sum_congr rfl fun m _ ↦ ?_
      by_cases hm : 2 ≤ m <;> simp [hm]
    · simp [hF, hpp]
  · intro k hk
    obtain ⟨p, m⟩ := k
    simp only [hF]
    split_ifs with h
    · have : ⌊x⌋₊ / p ^ m = 0 := by
        apply Nat.div_eq_of_lt
        simp only [mem_product, mem_Ioc, not_and, not_le] at hk
        have hp2 := h.1.two_le
        have hm2 := h.2
        by_cases hpN : p ≤ ⌊x⌋₊
        · have hmN : ⌊x⌋₊ < m := by omega
          calc ⌊x⌋₊ < m := hmN
            _ < 2 ^ m := Nat.lt_two_pow_self
            _ ≤ p ^ m := Nat.pow_le_pow_left hp2 m
        · calc ⌊x⌋₊ < p := by omega
            _ ≤ p ^ m := Nat.le_self_pow (by omega) p
      simp [this]
    · rfl

private lemma sum_cardFactors_real (x : ℝ) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, (Ω n : ℝ) = ∑ n ∈ Ioc 0 ⌊x⌋₊, (ω n : ℝ) + powTail x := by
  have := congrArg (Nat.cast (R := ℝ)) (sum_cardFactors_split ⌊x⌋₊)
  simpa [powTail, Nat.cast_sum, Nat.cast_ite] using this

/-- **Theorem 430.** (For `Ω`.) `∑_{n ≤ x} Ω(n) = x log log x + B₂ x + o(x)`. -/
@[kb "hardywright2008" "Thm 430, p. 491"]
theorem tendsto_sum_cardFactors_sub :
    ∃ B₂ : ℝ, Tendsto
      (fun x : ℝ ↦ ((∑ n ∈ Ioc 0 ⌊x⌋₊, (Ω n : ℝ)) - x * Real.log (Real.log x) - B₂ * x) / x)
      atTop (𝓝 0) := by
  obtain ⟨B₁, hB⟩ := tendsto_sum_cardDistinctFactors_sub
  refine ⟨B₁ + ∑' k, tailTerm k, ?_⟩
  have h := hB.add (tendsto_powTail_div.sub_const (∑' k, tailTerm k))
  rw [zero_add, sub_self] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [sum_cardFactors_real]
  field_simp
  ring

/-! ### The second moment of `ω` -/

private lemma sum_ite_dvd (N d : ℕ) :
    ∑ n ∈ Ioc 0 N, (if d ∣ n then 1 else 0) = N / d := by
  rw [← Finset.card_filter, Nat.Ioc_filter_dvd_card_eq_div]

private lemma sum_sq_cardDistinctFactors_le_nat (N : ℕ) :
    ∑ n ∈ Ioc 0 N, ω n ^ 2 ≤ ∑ p ∈ primesLE N, N / p + ∑ p ∈ primesLE N, ∑ q ∈ primesLE N, N / (p * q) := by
  calc ∑ n ∈ Ioc 0 N, ω n ^ 2
      ≤ ∑ n ∈ Ioc 0 N, ∑ p ∈ primesLE N, ∑ q ∈ primesLE N,
          ((if p = q ∧ p ∣ n then 1 else 0) + (if p * q ∣ n then 1 else 0)) := by
        refine Finset.sum_le_sum fun n hn ↦ ?_
        rw [cardDistinctFactors_eq_sum (N := N) (mem_Ioc.1 hn).1 (mem_Ioc.1 hn).2, sq,
          Finset.sum_mul_sum]
        refine Finset.sum_le_sum fun p hp ↦ Finset.sum_le_sum fun q hq ↦ ?_
        have hpp : p.Prime := (mem_filter.1 hp).2
        have hqp : q.Prime := (mem_filter.1 hq).2
        by_cases hpn : p ∣ n
        · by_cases hqn : q ∣ n
          · by_cases hpq : p = q
            · subst hpq; simp [hpn]
            · have : p * q ∣ n :=
                (Nat.coprime_primes hpp hqp).2 hpq |>.mul_dvd_of_dvd_of_dvd hpn hqn
              simp [this, hpn, hqn]
          · simp [hqn]
        · simp [hpn]
    _ = ∑ p ∈ primesLE N, ∑ q ∈ primesLE N,
          ((if p = q then N / p else 0) + N / (p * q)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q _ ↦ ?_
        rw [Finset.sum_add_distrib, sum_ite_dvd]
        congr 1
        by_cases hpq : p = q
        · subst hpq
          simp only [↓reduceIte]
          simpa only [true_and] using sum_ite_dvd N p
        · simp [hpq]
    _ = _ := by
        simp only [Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun p hp ↦ ?_
        rw [Finset.sum_ite_eq]
        simp [hp]

private lemma sum_sq_cardDistinctFactors_le (x : ℝ) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, (ω n : ℝ) ^ 2 ≤
      (⌊x⌋₊ : ℝ) * ∑ p ∈ primesLE ⌊x⌋₊, (1 : ℝ) / p +
        (⌊x⌋₊ : ℝ) * (∑ p ∈ primesLE ⌊x⌋₊, (1 : ℝ) / p) ^ 2 := by
  have h := sum_sq_cardDistinctFactors_le_nat ⌊x⌋₊
  have h' : ((∑ n ∈ Ioc 0 ⌊x⌋₊, ω n ^ 2 : ℕ) : ℝ) ≤ _ := Nat.cast_le.2 h
  push_cast at h'
  refine h'.trans ?_
  have e1 : ∑ p ∈ primesLE ⌊x⌋₊, (((⌊x⌋₊ / p : ℕ)) : ℝ) ≤
      (⌊x⌋₊ : ℝ) * ∑ p ∈ primesLE ⌊x⌋₊, (1 : ℝ) / p := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun p _ ↦ ?_
    calc _ ≤ (⌊x⌋₊ : ℝ) / p := Nat.cast_div_le
      _ = _ := by ring
  have e2 : ∑ p ∈ primesLE ⌊x⌋₊, ∑ q ∈ primesLE ⌊x⌋₊, (((⌊x⌋₊ / (p * q) : ℕ)) : ℝ) ≤
      (⌊x⌋₊ : ℝ) * (∑ p ∈ primesLE ⌊x⌋₊, (1 : ℝ) / p) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun p _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    calc _ ≤ (⌊x⌋₊ : ℝ) / ((p * q : ℕ) : ℝ) := Nat.cast_div_le
      _ = _ := by push_cast; ring
  linarith

private lemma primeCounting_le (N : ℕ) : (Nat.primeCounting N : ℝ) ≤ N := by
  rw [← card_primesLE]
  have : (primesLE N).card ≤ (Ioc 0 N).card := Finset.card_le_card (Finset.filter_subset _ _)
  simpa using (Nat.cast_le (α := ℝ)).2 this

private lemma exists_bound_sum_inv :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 2 ≤ x →
      |∑ p ∈ primesLE ⌊x⌋₊, (1 : ℝ) / p - Real.log (Real.log x)| ≤ K := by
  obtain ⟨A, C, hA⟩ := apostol_thm_4_12
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hC : 0 ≤ C := by
    have := (abs_nonneg _).trans (hA 2 le_rfl)
    exact (div_nonneg_iff.1 this).elim (fun h ↦ h.1) (fun h ↦ by linarith [h.2])
  refine ⟨|A| + C / Real.log 2, by positivity, fun x hx ↦ ?_⟩
  have h1 := hA x hx
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log two_pos hx
  have h2 : C / Real.log x ≤ C / Real.log 2 := div_le_div_of_nonneg_left hC hl2 hlx
  have h3 : |∑ p ∈ primesLE ⌊x⌋₊, (1 : ℝ) / p - Real.log (Real.log x)| ≤
      |∑ p ∈ primesLE ⌊x⌋₊, (1 : ℝ) / p - Real.log (Real.log x) - A| + |A| := by
    have := abs_add_le (∑ p ∈ primesLE ⌊x⌋₊, (1 : ℝ) / p - Real.log (Real.log x) - A) A
    simpa using this
  linarith

/-- **Theorem 431.** (Key inequality of Turán's proof, cf. § 22.11.) For `x ≥ 3`,
`∑_{n ≤ x} (ω(n) - log log x)² ≤ C x log log x`. -/
@[kb "hardywright2008" "Thm 431, p. 493"]
theorem sum_sq_cardDistinctFactors_sub_le :
    ∃ C : ℝ, ∀ x : ℝ, 3 ≤ x →
      ∑ n ∈ Ioc 0 ⌊x⌋₊, ((ω n : ℝ) - Real.log (Real.log x)) ^ 2 ≤
        C * x * Real.log (Real.log x) := by
  obtain ⟨K, hK0, hK⟩ := exists_bound_sum_inv
  have h1 : 1 < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).2 (by have := Real.exp_one_lt_d9; linarith)
  have hL0 : 0 < Real.log (Real.log 3) := Real.log_pos h1
  refine ⟨(K ^ 2 + K) / Real.log (Real.log 3) + 3, fun x hx ↦ ?_⟩
  have hx0 : 0 ≤ x := by linarith
  have hx2 : (2 : ℝ) ≤ x := by linarith
  set L := Real.log (Real.log x) with hLdef
  set S := ∑ p ∈ primesLE ⌊x⌋₊, (1 : ℝ) / p with hSdef
  have hLge : Real.log (Real.log 3) ≤ L :=
    Real.log_le_log (Real.log_pos (by norm_num)) (Real.log_le_log (by norm_num) hx)
  have hLpos : 0 < L := hL0.trans_le hLge
  have hS : |S - L| ≤ K := hK x hx2
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun p _ ↦ by positivity
  have hNx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  have hN0 : (0 : ℝ) ≤ ⌊x⌋₊ := Nat.cast_nonneg _
  have e1 : ∑ n ∈ Ioc 0 ⌊x⌋₊, (ω n : ℝ) = ∑ p ∈ primesLE ⌊x⌋₊, (((⌊x⌋₊ / p : ℕ)) : ℝ) := by
    rw [← Nat.cast_sum, sum_cardDistinctFactors]; push_cast; rfl
  have hT1 : (⌊x⌋₊ : ℝ) * S - Nat.primeCounting ⌊x⌋₊ ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, (ω n : ℝ) := by
    rw [e1]
    have := (sum_floor_bounds hx0).1
    nlinarith [mul_le_mul_of_nonneg_right hNx hS0]
  have hT2 := sum_sq_cardDistinctFactors_le x
  have E : ∑ n ∈ Ioc 0 ⌊x⌋₊, ((ω n : ℝ) - L) ^ 2 =
      ∑ n ∈ Ioc 0 ⌊x⌋₊, (ω n : ℝ) ^ 2 - 2 * L * ∑ n ∈ Ioc 0 ⌊x⌋₊, (ω n : ℝ) +
        ⌊x⌋₊ * L ^ 2 := by
    have : ∀ n : ℕ, ((ω n : ℝ) - L) ^ 2 = (ω n : ℝ) ^ 2 - 2 * L * (ω n : ℝ) + L ^ 2 :=
      fun n ↦ by ring
    simp_rw [this]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp
  have h4 : 2 * L * ((⌊x⌋₊ : ℝ) * S - Nat.primeCounting ⌊x⌋₊) ≤
      2 * L * ∑ n ∈ Ioc 0 ⌊x⌋₊, (ω n : ℝ) :=
    mul_le_mul_of_nonneg_left hT1 (by positivity)
  have h5 : (S - L) ^ 2 ≤ K ^ 2 := sq_le_sq' (abs_le.1 hS).1 (abs_le.1 hS).2
  have h6 : S ≤ L + K := by linarith [(abs_le.1 hS).2]
  have h7 : (⌊x⌋₊ : ℝ) * ((S - L) ^ 2 + S) ≤ (⌊x⌋₊ : ℝ) * (K ^ 2 + (L + K)) :=
    mul_le_mul_of_nonneg_left (by linarith) hN0
  have h8 : 2 * L * (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ 2 * L * ⌊x⌋₊ :=
    mul_le_mul_of_nonneg_left (primeCounting_le _) (by positivity)
  have h9 : (⌊x⌋₊ : ℝ) * (K ^ 2 + (L + K) + 2 * L) ≤ x * (K ^ 2 + (L + K) + 2 * L) :=
    mul_le_mul_of_nonneg_right hNx (by positivity)
  have hq : K ^ 2 + K ≤ (K ^ 2 + K) / Real.log (Real.log 3) * L := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hL0]
    exact mul_le_mul_of_nonneg_left hLge (by positivity)
  have h10 := mul_le_mul_of_nonneg_left hq hx0
  rw [E]
  nlinarith [h4, h7, h8, h9, h10, hT2]

/-! ### The normal order -/

/-- The set of `n ≤ x` at which `f n` deviates from `log log n` by more than `ε log log n`. -/
private noncomputable def badSet (f : ℕ → ℝ) (ε x : ℝ) : Finset ℕ :=
  (Ioc 0 ⌊x⌋₊).filter fun n : ℕ ↦ ε * Real.log (Real.log n) < |f n - Real.log (Real.log n)|

private lemma card_badSet_le (f : ℕ → ℝ) (C : ℝ)
    (hC : ∀ x : ℝ, 3 ≤ x →
      ∑ n ∈ Ioc 0 ⌊x⌋₊, (f n - Real.log (Real.log x)) ^ 2 ≤ C * x * Real.log (Real.log x))
    {ε : ℝ} (hε : 0 < ε) {x : ℝ} (hx : 3 ≤ x)
    (hL : 2 * (ε + 1) * Real.log 2 / ε ≤ Real.log (Real.log x)) :
    ((badSet f ε x).card : ℝ) ≤ √x + 4 * C / (ε ^ 2 * Real.log (Real.log x)) * x := by
  have hx0 : 0 < x := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set L := Real.log (Real.log x) with hLdef
  have hLpos : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hsplit := Finset.card_filter_add_card_filter_not (s := badSet f ε x) (fun n : ℕ ↦ n ≤ ⌊√x⌋₊)
  have h1 : ((badSet f ε x).filter fun n : ℕ ↦ n ≤ ⌊√x⌋₊).card ≤ ⌊√x⌋₊ := by
    calc _ ≤ (Ioc 0 ⌊√x⌋₊).card := by
          refine Finset.card_le_card fun n hn ↦ ?_
          simp only [badSet, mem_filter, mem_Ioc] at hn ⊢
          exact ⟨hn.1.1.1, hn.2⟩
      _ = _ := by simp
  have h1' : (((badSet f ε x).filter fun n : ℕ ↦ n ≤ ⌊√x⌋₊).card : ℝ) ≤ √x :=
    (Nat.cast_le.2 h1).trans (Nat.floor_le (Real.sqrt_nonneg x))
  set S' := (badSet f ε x).filter fun n : ℕ ↦ ¬ n ≤ ⌊√x⌋₊ with hS'
  have hterm : ∀ n ∈ S', (ε * L / 2) ^ 2 ≤ (f n - L) ^ 2 := by
    intro n hn
    simp only [hS', badSet, mem_filter, mem_Ioc, not_le] at hn
    obtain ⟨⟨⟨hn0, hnN⟩, hbad⟩, hnM⟩ := hn
    have hnx : (n : ℝ) ≤ x := (Nat.cast_le.2 hnN).trans (Nat.floor_le hx0.le)
    have hsq : √x < n := (Nat.floor_lt (Real.sqrt_nonneg x)).1 hnM
    have hn0' : (0 : ℝ) < n := Nat.cast_pos.2 hn0
    have hlog1 : Real.log x / 2 < Real.log n := by
      rw [← Real.log_sqrt hx0.le]; exact Real.log_lt_log (Real.sqrt_pos.2 hx0) hsq
    have hlogn : 0 < Real.log n := by linarith
    have hℓ1 : Real.log (Real.log n) ≤ L :=
      Real.log_le_log hlogn (Real.log_le_log hn0' hnx)
    have hℓ2 : L - Real.log 2 < Real.log (Real.log n) := by
      have : Real.log (Real.log x / 2) < Real.log (Real.log n) :=
        Real.log_lt_log (by positivity) hlog1
      rwa [Real.log_div hlogx.ne' two_ne_zero] at this
    set ℓ := Real.log (Real.log n)
    have h3 : ε * (L - Real.log 2) - Real.log 2 < |f n - L| := by
      have : |f n - ℓ| ≤ |f n - L| + |L - ℓ| := by
        have := abs_add_le (f n - L) (L - ℓ)
        simpa using this
      rw [abs_of_nonneg (by linarith : 0 ≤ L - ℓ)] at this
      nlinarith
    have h4 : ε * L / 2 ≤ ε * (L - Real.log 2) - Real.log 2 := by
      have : 2 * (ε + 1) * Real.log 2 ≤ ε * L := by
        rwa [div_le_iff₀ hε, mul_comm L ε] at hL
      nlinarith
    calc (ε * L / 2) ^ 2 ≤ |f n - L| ^ 2 :=
          pow_le_pow_left₀ (by positivity) (h4.trans h3.le) 2
      _ = _ := sq_abs _
  have h2 : (S'.card : ℝ) * (ε * L / 2) ^ 2 ≤ C * x * L := by
    calc (S'.card : ℝ) * (ε * L / 2) ^ 2 = ∑ _n ∈ S', (ε * L / 2) ^ 2 := by simp
      _ ≤ ∑ n ∈ S', (f n - L) ^ 2 := Finset.sum_le_sum hterm
      _ ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, (f n - L) ^ 2 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ ↦ sq_nonneg _
          intro n hn
          simp only [hS', badSet, mem_filter] at hn
          exact hn.1.1
      _ ≤ _ := hC x hx
  have h5 : (S'.card : ℝ) ≤ 4 * C / (ε ^ 2 * L) * x := by
    have hpos : 0 < (ε * L / 2) ^ 2 := by positivity
    have := (le_div_iff₀ hpos).2 h2
    refine this.trans (le_of_eq ?_)
    field_simp
    ring
  have hsplit' : ((badSet f ε x).card : ℝ) =
      (((badSet f ε x).filter fun n : ℕ ↦ n ≤ ⌊√x⌋₊).card : ℝ) + S'.card := by
    rw [← Nat.cast_add, hsplit]
  rw [hsplit']
  linarith

private lemma tendsto_badSet_div (f : ℕ → ℝ) (C : ℝ)
    (hC : ∀ x : ℝ, 3 ≤ x →
      ∑ n ∈ Ioc 0 ⌊x⌋₊, (f n - Real.log (Real.log x)) ^ 2 ≤ C * x * Real.log (Real.log x))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun x : ℝ ↦ ((badSet f ε x).card : ℝ) / x) atTop (𝓝 0) := by
  have hlogA : Tendsto (fun x : ℝ ↦ Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hA : Tendsto (fun x : ℝ ↦ 1 / √x + 4 * C / ε ^ 2 / Real.log (Real.log x)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ ↦ 1 / √x) atTop (𝓝 0) := by
      have := tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
      simpa [Function.comp_def, one_div] using this
    have h2 : Tendsto (fun x : ℝ ↦ 4 * C / ε ^ 2 / Real.log (Real.log x)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hlogA
    simpa using h1.add h2
  refine squeeze_zero' (by filter_upwards [eventually_gt_atTop 0] with x hx; positivity) ?_ hA
  filter_upwards [eventually_ge_atTop 3, hlogA.eventually_ge_atTop (2 * (ε + 1) * Real.log 2 / ε)]
    with x hx hL
  have hx0 : 0 < x := by linarith
  have h := card_badSet_le f C hC hε hx hL
  have hLpos : 0 < Real.log (Real.log x) :=
    lt_of_lt_of_le (by positivity) hL
  rw [div_le_iff₀ hx0]
  have e : (1 / √x + 4 * C / ε ^ 2 / Real.log (Real.log x)) * x =
      √x + 4 * C / (ε ^ 2 * Real.log (Real.log x)) * x := by
    have : √x ≠ 0 := (Real.sqrt_pos.2 hx0).ne'
    have hs : √x * √x = x := Real.mul_self_sqrt hx0.le
    field_simp
    linear_combination (-(ε ^ 2 * Real.log (Real.log x))) * hs
  rw [e]; exact h

/-- **Theorem 431.** (Hardy–Ramanujan, for `ω`.) The normal order of `ω(n)` is `log log n`:
for every `ε > 0`, the number of `n ≤ x` with `|ω(n) - log log n| > ε log log n` is `o(x)`. -/
@[kb "hardywright2008" "Thm 431, p. 493"]
theorem tendsto_card_normalOrder_cardDistinctFactors {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun x : ℝ ↦
      (((Ioc 0 ⌊x⌋₊).filter fun n : ℕ ↦ ε * Real.log (Real.log n) <
        |(ω n : ℝ) - Real.log (Real.log n)|).card : ℝ) / x) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := sum_sq_cardDistinctFactors_sub_le
  exact tendsto_badSet_div (fun n ↦ (ω n : ℝ)) C hC hε

/-- A first-moment (Markov) estimate: if `∑_{n ≤ x} D(n) = O(x)` for a nonnegative `D`, then
`D(n) ≤ δ log log n` for all but `o(x)` of the `n ≤ x`. -/
private lemma tendsto_card_first_moment (D : ℕ → ℝ) (hD : ∀ n, 0 ≤ D n) (K x₀ : ℝ)
    (hK : ∀ x : ℝ, x₀ ≤ x → ∑ n ∈ Ioc 0 ⌊x⌋₊, D n ≤ K * x) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun x : ℝ ↦
      (((Ioc 0 ⌊x⌋₊).filter fun n : ℕ ↦ δ * Real.log (Real.log n) < D n).card : ℝ) / x)
      atTop (𝓝 0) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogA : Tendsto (fun x : ℝ ↦ Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hA : Tendsto (fun x : ℝ ↦ 1 / √x + 2 * K / δ / Real.log (Real.log x)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ ↦ 1 / √x) atTop (𝓝 0) := by
      have := tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
      simpa [Function.comp_def, one_div] using this
    have h2 : Tendsto (fun x : ℝ ↦ 2 * K / δ / Real.log (Real.log x)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hlogA
    simpa using h1.add h2
  refine squeeze_zero' (by filter_upwards [eventually_gt_atTop 0] with x hx; positivity) ?_ hA
  filter_upwards [eventually_ge_atTop (max 3 x₀), hlogA.eventually_ge_atTop (2 * Real.log 2)]
    with x hx hL
  have hx3 : 3 ≤ x := (le_max_left _ _).trans hx
  have hx0' : x₀ ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  set L := Real.log (Real.log x) with hLdef
  have hLpos : 0 < L := by linarith
  set B := Ioc 0 ⌊x⌋₊ with hB
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := B.filter fun n : ℕ ↦ δ * Real.log (Real.log n) < D n) (fun n : ℕ ↦ n ≤ ⌊√x⌋₊)
  have h1 : ((B.filter fun n : ℕ ↦ δ * Real.log (Real.log n) < D n).filter
      fun n : ℕ ↦ n ≤ ⌊√x⌋₊).card ≤ ⌊√x⌋₊ := by
    calc _ ≤ (Ioc 0 ⌊√x⌋₊).card := by
          refine Finset.card_le_card fun n hn ↦ ?_
          simp only [hB, mem_filter, mem_Ioc] at hn ⊢
          exact ⟨hn.1.1.1, hn.2⟩
      _ = _ := by simp
  have h1' : (((B.filter fun n : ℕ ↦ δ * Real.log (Real.log n) < D n).filter
      fun n : ℕ ↦ n ≤ ⌊√x⌋₊).card : ℝ) ≤ √x :=
    (Nat.cast_le.2 h1).trans (Nat.floor_le (Real.sqrt_nonneg x))
  set S' := (B.filter fun n : ℕ ↦ δ * Real.log (Real.log n) < D n).filter
    fun n : ℕ ↦ ¬ n ≤ ⌊√x⌋₊ with hS'
  have hterm : ∀ n ∈ S', δ * L / 2 ≤ D n := by
    intro n hn
    simp only [hS', hB, mem_filter, mem_Ioc, not_le] at hn
    obtain ⟨⟨⟨hn0, hnN⟩, hbad⟩, hnM⟩ := hn
    have hsq : √x < n := (Nat.floor_lt (Real.sqrt_nonneg x)).1 hnM
    have hlog1 : Real.log x / 2 < Real.log n := by
      rw [← Real.log_sqrt hx0.le]; exact Real.log_lt_log (Real.sqrt_pos.2 hx0) hsq
    have hℓ2 : L - Real.log 2 < Real.log (Real.log n) := by
      have : Real.log (Real.log x / 2) < Real.log (Real.log n) :=
        Real.log_lt_log (by positivity) hlog1
      rwa [Real.log_div hlogx.ne' two_ne_zero] at this
    nlinarith
  have h2 : (S'.card : ℝ) * (δ * L / 2) ≤ K * x := by
    calc (S'.card : ℝ) * (δ * L / 2) = ∑ _n ∈ S', (δ * L / 2) := by simp
      _ ≤ ∑ n ∈ S', D n := Finset.sum_le_sum hterm
      _ ≤ ∑ n ∈ B, D n := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ ↦ hD n
          intro n hn
          simp only [hS', mem_filter] at hn
          exact hn.1.1
      _ ≤ _ := hK x hx0'
  have h5 : (S'.card : ℝ) ≤ 2 * K / (δ * L) * x := by
    have hpos : 0 < δ * L / 2 := by positivity
    have := (le_div_iff₀ hpos).2 h2
    refine this.trans (le_of_eq ?_)
    field_simp
  have hsplit' : ((B.filter fun n : ℕ ↦ δ * Real.log (Real.log n) < D n).card : ℝ) =
      (((B.filter fun n : ℕ ↦ δ * Real.log (Real.log n) < D n).filter
        fun n : ℕ ↦ n ≤ ⌊√x⌋₊).card : ℝ) + S'.card := by
    rw [← Nat.cast_add, hsplit]
  rw [div_le_iff₀ hx0, hsplit']
  have e : (1 / √x + 2 * K / δ / L) * x = √x + 2 * K / (δ * L) * x := by
    have : √x ≠ 0 := (Real.sqrt_pos.2 hx0).ne'
    have hs : √x * √x = x := Real.mul_self_sqrt hx0.le
    field_simp
    linear_combination (-(δ * L)) * hs
  rw [e]; linarith

/-- **Theorem 431.** (For `Ω`.) The normal order of `Ω(n)` is `log log n`: for every `ε > 0`, the
number of `n ≤ x` with `|Ω(n) - log log n| > ε log log n` is `o(x)`. -/
@[kb "hardywright2008" "Thm 431, p. 493"]
theorem tendsto_card_normalOrder_cardFactors {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun x : ℝ ↦
      (((Ioc 0 ⌊x⌋₊).filter fun n : ℕ ↦ ε * Real.log (Real.log n) <
        |(Ω n : ℝ) - Real.log (Real.log n)|).card : ℝ) / x) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := sum_sq_cardDistinctFactors_sub_le
  have hε2 : 0 < ε / 2 := by positivity
  have hD : ∀ n : ℕ, 0 ≤ (Ω n : ℝ) - ω n := fun n ↦ by
    rw [sub_nonneg]
    exact_mod_cast (show ω n ≤ Ω n by
      rw [cardDistinctFactors_eq_length_dedup_primeFactorsList, cardFactors_apply]
      exact (List.dedup_sublist _).length_le)
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1
    ((tendsto_powTail_div.eventually (gt_mem_nhds (lt_add_one (∑' k, tailTerm k)))).and
      (eventually_gt_atTop (0 : ℝ)))
  have hK : ∀ x : ℝ, x₀ ≤ x →
      ∑ n ∈ Ioc 0 ⌊x⌋₊, ((Ω n : ℝ) - ω n) ≤ (∑' k, tailTerm k + 1) * x := by
    intro x hx
    obtain ⟨h1, h2⟩ := hx₀ x hx
    rw [Finset.sum_sub_distrib, sum_cardFactors_real]
    rw [div_lt_iff₀ h2] at h1
    linarith
  have h1 := tendsto_card_first_moment (fun n ↦ (Ω n : ℝ) - ω n) hD _ x₀ hK hε2
  have h2 := tendsto_badSet_div (fun n ↦ (ω n : ℝ)) C hC hε2
  have h3 := h1.add h2
  rw [add_zero] at h3
  refine squeeze_zero' (by filter_upwards [eventually_gt_atTop 0] with x hx; positivity) ?_ h3
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ hx.le
  rw [← Nat.cast_add]
  refine Nat.cast_le.2 ?_
  refine le_trans (Finset.card_le_card (t := ((Ioc 0 ⌊x⌋₊).filter fun n : ℕ ↦
      ε / 2 * Real.log (Real.log n) < (Ω n : ℝ) - ω n) ∪ badSet (fun n ↦ (ω n : ℝ)) (ε / 2) x) ?_)
    (Finset.card_union_le _ _)
  intro n hn
  simp only [badSet, mem_union, mem_filter] at hn ⊢
  obtain ⟨hnI, hbad⟩ := hn
  by_contra hcon
  rw [not_or, not_and, not_and, not_lt, not_lt] at hcon
  obtain ⟨h4, h5⟩ := hcon
  have h4' := h4 hnI
  have h5' := h5 hnI
  have : |(Ω n : ℝ) - Real.log (Real.log n)| ≤
      |(ω n : ℝ) - Real.log (Real.log n)| + ((Ω n : ℝ) - ω n) := by
    have := abs_add_le ((ω n : ℝ) - Real.log (Real.log n)) ((Ω n : ℝ) - ω n)
    rw [abs_of_nonneg (hD n)] at this
    simpa using this
  linarith

end NTKB.HardyWright
