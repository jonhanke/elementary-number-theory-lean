/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Theta.SixCount
import Mathlib.NumberTheory.ZetaValues

/-!
# Hardy–Wright, § 20.13 notes: the coefficients of `r₁₂` (Glaisher)

Glaisher's formula `r₁₂(n) = 8 ∑_{d ∣ n} (-1)^{n+d+n/d+1} d⁵ + 16 a(n)` from an identity of
generating functions, where `a(n)` are the coefficients of `q ∏ (1 - q^{2m})¹²`.  The constant
`κ = ∑_{n odd} n⁻⁶ = π⁶/480` is computed from `ζ(6) = π⁶/945`.
-/

open Finset Filter Topology

namespace NTKB.HardyWright

/-- `O(x) = ∑_{k ≥ 0} ∑_{r ≥ 0} r⁵ x^{r(2k+1)}`. -/
noncomputable def twelveSeriesO (x : ℝ) : ℝ :=
  ∑' k : ℕ, ∑' r : ℕ, (r : ℝ) ^ 5 * x ^ (r * (2 * k + 1))

/-- `E(x) = ∑_{k ≥ 0} ∑_{r ≥ 0} (-1)^r r⁵ x^{2r(k+1)}`. -/
noncomputable def twelveSeriesE (x : ℝ) : ℝ :=
  ∑' k : ℕ, ∑' r : ℕ, (-1) ^ r * (r : ℝ) ^ 5 * x ^ (r * (2 * (k + 1)))

/-- Glaisher's divisor sum `∑_{d ∣ n} (-1)^{n + d + n/d + 1} d⁵`. -/
def glaisherSum (n : ℕ) : ℤ := ∑ d ∈ n.divisors, (-1) ^ (n + d + n / d + 1) * (d : ℤ) ^ 5

/-- `κ = ∑_{n ∈ ℤ, n odd} n⁻⁶`. -/
noncomputable def kappaTwelveR : ℝ := ∑' n : ℤ, (if Even n then 0 else 1) * (1 / (n : ℝ) ^ 6)

lemma hasSum_zeta_six : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 6) (Real.pi ^ 6 / 945) := by
  have h := hasSum_zeta_nat (k := 3) (by norm_num)
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
  have h6 : bernoulli' 6 = 1 / 42 := by
    rw [bernoulli'_def]
    norm_num [Finset.sum_range_succ, Nat.choose, h5]
  have hb : bernoulli 6 = 1 / 42 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), h6]
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub] at h
  rw [hb] at h
  convert h using 1
  norm_num [Nat.factorial]
  ring

theorem kappaTwelveR_eq : kappaTwelveR = Real.pi ^ 6 / 480 := by
  set z : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ 6 with hz
  have hZ : HasSum z (Real.pi ^ 6 / 945) := hasSum_zeta_six
  have hEv : HasSum (fun k : ℕ => z (2 * k)) (Real.pi ^ 6 / 945 / 64) := by
    have := hZ.mul_left (1 / 64)
    convert this using 1
    · ext k
      simp only [hz]
      push_cast
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · have : (k : ℝ) ≠ 0 := by positivity
        field_simp
        norm_num
    · ring
  have hOdS : Summable fun k : ℕ => z (2 * k + 1) :=
    hZ.summable.comp_injective (i := fun k : ℕ => 2 * k + 1) (by intro a b h; simpa using h)
  set S := ∑' k : ℕ, z (2 * k + 1) with hS
  have hOd : HasSum (fun k : ℕ => z (2 * k + 1)) S := hOdS.hasSum
  have hsum := HasSum.even_add_odd hEv hOd
  have hSval : S = Real.pi ^ 6 / 945 * (63 / 64) := by
    have := hZ.unique hsum
    linarith
  -- the function on `ℕ`
  set g : ℕ → ℝ := fun n => (if Even n then 0 else 1) * z n with hg
  have hgS : HasSum g S := by
    have : HasSum g (0 + S) := HasSum.even_add_odd (by
      have : (fun k : ℕ => g (2 * k)) = fun _ => 0 := by
        ext k
        simp [hg]
      rw [this]; exact hasSum_zero) (by
      refine hOd.congr_fun fun k => ?_
      simp [hg])
    simpa using this
  have h1 : HasSum (fun n : ℕ => (if Even (n : ℤ) then (0 : ℝ) else 1) * (1 / ((n : ℤ) : ℝ) ^ 6))
      S := by
    refine hgS.congr_fun fun n => ?_
    simp [hg, hz]
  have h2 : HasSum (fun n : ℕ =>
      (if Even (-((n : ℤ) + 1)) then (0 : ℝ) else 1) * (1 / ((-((n : ℤ) + 1) : ℤ) : ℝ) ^ 6)) S := by
    have h3 : HasSum (fun n : ℕ => g (n + 1)) S := by
      refine (hasSum_nat_add_iff (f := g) 1).mpr ?_
      have h0 : g 0 = 0 := by simp [hg]
      simpa [h0] using hgS
    refine h3.congr_fun fun n => ?_
    have hev : Even (-((n : ℤ) + 1)) ↔ Even (n + 1) := by
      have := Int.even_natCast (n + 1)
      push_cast at this
      rw [even_neg]; exact this
    simp only [hg, hz, hev]
    push_cast
    rw [show (-((n : ℝ) + 1)) ^ 6 = ((n : ℝ) + 1) ^ 6 by ring]
  have := HasSum.of_nat_of_neg_add_one
    (f := fun n : ℤ => (if Even n then (0 : ℝ) else 1) * (1 / (n : ℝ) ^ 6)) h1 h2
  unfold kappaTwelveR
  rw [this.tsum_eq, hSval]
  ring

lemma summable_twelve_majorant {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    Summable fun p : ℕ × ℕ => (p.2 : ℝ) ^ 5 * x ^ (p.2 * (p.1 + 1)) := by
  have hM : Summable fun p : ℕ × ℕ => (p.1 : ℝ) ^ 5 * x ^ (p.1 * (p.2 + 1)) := by
    have hnn : ∀ p : ℕ × ℕ, 0 ≤ (p.1 : ℝ) ^ 5 * x ^ (p.1 * (p.2 + 1)) :=
      fun p => by positivity
    refine (summable_prod_of_nonneg hnn).2 ⟨fun r => ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos r with rfl | hr
      · simp
      · have hxr : x ^ r < 1 := pow_lt_one₀ hx0 hx hr.ne'
        refine ((summable_geometric_of_lt_one (pow_nonneg hx0 r) hxr).mul_left
          ((r : ℝ) ^ 5 * x ^ r)).congr fun k => ?_
        show _ = _
        rw [mul_add, mul_one, pow_add, pow_mul]; ring
    · have hb : Summable fun r : ℕ => (r : ℝ) ^ 5 * x ^ r * (1 - x)⁻¹ :=
        (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 5 (r := x)
          (by rw [Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx)).mul_right _
      have h1x : 0 < 1 - x := by linarith
      refine Summable.of_nonneg_of_le (fun r => tsum_nonneg fun k => hnn (r, k)) (fun r => ?_) hb
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · simp
      · have hxr : x ^ r < 1 := pow_lt_one₀ hx0 hx hr.ne'
        have hxr' : x ^ r ≤ x := pow_le_of_le_one hx0 hx.le hr.ne'
        have : ∑' k : ℕ, (r : ℝ) ^ 5 * x ^ (r * (k + 1)) =
            (r : ℝ) ^ 5 * x ^ r * (1 - x ^ r)⁻¹ := by
          rw [← tsum_geometric_of_lt_one (pow_nonneg hx0 r) hxr, ← tsum_mul_left]
          refine tsum_congr fun k => ?_
          rw [mul_add, mul_one, pow_add, pow_mul]; ring
        show ∑' k : ℕ, (r : ℝ) ^ 5 * x ^ (r * (k + 1)) ≤ _
        rw [this]
        exact mul_le_mul_of_nonneg_left (inv_anti₀ h1x (by linarith)) (by positivity)
  exact (Equiv.prodComm ℕ ℕ).summable_iff.mpr hM

lemma glaisher_sign (d e : ℕ) :
    ((-1 : ℤ) ^ (d * e + d + e + 1)) = if e % 2 = 1 then 1 else -(-1) ^ d := by
  rcases Nat.even_or_odd' e with ⟨t, rfl | rfl⟩
  · have : d * (2 * t) + d + 2 * t + 1 = (d + 1) + 2 * (d * t + t) := by ring
    rw [this, pow_add, pow_mul]
    simp [pow_succ]
  · have : d * (2 * t + 1) + d + (2 * t + 1) + 1 = 2 * (d * t + d + t + 1) := by ring
    rw [this, pow_mul]
    simp

theorem hasSum_glaisherSum {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    HasSum (fun N : ℕ => (glaisherSum N : ℝ) * x ^ N) (twelveSeriesO x - twelveSeriesE x) := by
  set G : ℕ → ℕ → ℝ := fun r m =>
    (if m % 2 = 1 then 1 else -(-1) ^ r) * ((r : ℝ) ^ 5 * x ^ (r * m)) with hG
  have hs : Summable fun p : ℕ × ℕ => G p.2 (p.1 + 1) := by
    refine Summable.of_norm_bounded (summable_twelve_majorant hx0 hx) fun p => ?_
    have h2 : (0 : ℝ) ≤ (p.2 : ℝ) ^ 5 * x ^ (p.2 * (p.1 + 1)) := by positivity
    simp only [hG]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2]
    have : |(if (p.1 + 1) % 2 = 1 then (1 : ℝ) else -(-1) ^ p.2)| ≤ 1 := by
      split_ifs
      · simp
      · simp
    nlinarith
  have hD := hasSum_divisor_rearr G (by simp [hG]) hs
  have hU : Summable fun k : ℕ => ∑' r : ℕ, G r (k + 1) := hs.prod
  have hUe : Summable fun j : ℕ => ∑' r : ℕ, G r (2 * j + 1) :=
    hU.comp_injective (i := fun j : ℕ => 2 * j) (by intro a b h; simpa using h)
  have hUo : Summable fun j : ℕ => ∑' r : ℕ, G r (2 * j + 1 + 1) :=
    hU.comp_injective (i := fun j : ℕ => 2 * j + 1) (by intro a b h; simpa using h)
  have e1 : ∀ j : ℕ, ∑' r : ℕ, G r (2 * j + 1) = ∑' r : ℕ, (r : ℝ) ^ 5 * x ^ (r * (2 * j + 1)) := by
    intro j
    refine tsum_congr fun r => ?_
    simp only [hG]
    rw [if_pos (by omega), one_mul]
  have e2 : ∀ j : ℕ, ∑' r : ℕ, G r (2 * j + 1 + 1) =
      -∑' r : ℕ, (-1) ^ r * (r : ℝ) ^ 5 * x ^ (r * (2 * (j + 1))) := by
    intro j
    rw [← tsum_neg]
    refine tsum_congr fun r => ?_
    simp only [hG]
    rw [if_neg (by omega), show 2 * j + 1 + 1 = 2 * (j + 1) by ring]
    ring
  have eT : ∑' k : ℕ, ∑' r : ℕ, G r (k + 1) = twelveSeriesO x - twelveSeriesE x := by
    rw [← tsum_even_add_odd hUe hUo]
    simp only [e1, e2]
    rw [tsum_neg]
    rfl
  rw [eT] at hD
  refine hD.congr_fun fun N => ?_
  rw [glaisherSum]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨e, rfl⟩ := Nat.dvd_of_mem_divisors hd
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  rw [Nat.mul_div_cancel_left e hd0]
  simp only [hG]
  have hsg := glaisher_sign d e
  have hsg' : ((-1 : ℝ) ^ (d * e + d + e + 1)) = if e % 2 = 1 then 1 else -(-1) ^ d := by
    have := congrArg (Int.cast : ℤ → ℝ) hsg
    push_cast at this
    exact this
  rw [hsg']
  ring

/-- **Glaisher's formula for `r₁₂`**, from an identity of generating functions; `a` and `P` stand
for the coefficients and the sum of `q ∏ (1 - q^{2m})¹²`. -/
theorem sumSquaresCount_twelve_eq_of_forall {a : ℕ → ℤ} {P : ℝ → ℝ}
    (hP : ∀ x : ℝ, 0 ≤ x → x < 1 → HasSum (fun n : ℕ => (a n : ℝ) * x ^ n) (P x))
    (h : ∀ x : ℝ, 0 < x → x < 1 / 2 → kappaTwelveR * (∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 12 =
      kappaTwelveR + Real.pi ^ 6 / 60 * (twelveSeriesO x - twelveSeriesE x) +
        Real.pi ^ 6 / 30 * P x)
    {n : ℕ} (hn : 0 < n) :
    (sumSquaresCount 12 n : ℤ) = 8 * glaisherSum n + 16 * a n := by
  set κ := kappaTwelveR with hκdef
  have hκ : κ = Real.pi ^ 6 / 480 := kappaTwelveR_eq
  set b : ℕ → ℝ := fun N => κ * (sumSquaresCount 12 N : ℝ) - (if N = 0 then κ else 0)
    - Real.pi ^ 6 / 60 * (glaisherSum N : ℝ) - Real.pi ^ 6 / 30 * (a N : ℝ) with hb
  have hHA : ∀ x : ℝ, 0 ≤ x → x < 1 →
      HasSum (fun N : ℕ => b N * x ^ N)
        (κ * (∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 12 - κ
          - Real.pi ^ 6 / 60 * (twelveSeriesO x - twelveSeriesE x)
          - Real.pi ^ 6 / 30 * P x) := by
    intro x hx0 hx
    have h3 : HasSum (fun N : ℕ => (if N = 0 then κ else 0) * x ^ N) κ := by
      have := hasSum_ite_eq (0 : ℕ) κ
      refine this.congr_fun fun N => ?_
      by_cases hN : N = 0 <;> simp [hN]
    have := ((((hasSum_sumSquaresCount 12 hx0 hx).mul_left κ).sub h3).sub
      ((hasSum_glaisherSum hx0 hx).mul_left (Real.pi ^ 6 / 60))).sub
      ((hP x hx0 hx).mul_left (Real.pi ^ 6 / 30))
    refine this.congr_fun fun N => ?_
    simp only [hb]; ring
  have hzero : ∀ x : ℝ, 0 < x → x < 1 / 2 → ∑' N, b N * x ^ N = 0 := by
    intro x hx0 hx
    rw [(hHA x hx0.le (by linarith)).tsum_eq, h x hx0 hx]; ring
  have hs : Summable fun N => |b N| * (1 / 2 : ℝ) ^ N := by
    have := (hHA (1 / 2) (by norm_num) (by norm_num)).summable.abs
    refine this.congr fun N => ?_
    rw [abs_mul, abs_of_pos (show (0 : ℝ) < (1 / 2) ^ N by positivity)]
  have hn0 := eq_zero_of_tsum_pow_eq_zero hs hzero n
  simp only [hb, if_neg hn.ne'] at hn0
  rw [hκ] at hn0
  have hp : 0 < Real.pi ^ 6 := by positivity
  have h2 : Real.pi ^ 6 * ((sumSquaresCount 12 n : ℝ) - (8 * (glaisherSum n : ℝ)
      + 16 * (a n : ℝ))) = 0 := by
    linear_combination 480 * hn0
  have h3 : (sumSquaresCount 12 n : ℝ) = 8 * (glaisherSum n : ℝ) + 16 * (a n : ℝ) := by
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h hp.ne'
    · linarith
  exact_mod_cast h3

end NTKB.HardyWright
