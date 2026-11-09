/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Jacobi.Cotangent

/-!
# Hardy–Wright, § 20.12: Jacobi's formula for `r₄(n)` (Theorems 384–386)

* Theorem 384: `(¼ + u₁ - u₃ + u₅ - ⋯)² = 1/16 + ½(u₁ + 2u₂ + 3u₃ + 5u₅ + ⋯)` (no terms `u_{4k}`),
  from Theorem 383 with `θ = ½π` (`sq_quarter_add_chi4`). The alternating series is written
  `∑ χ(n) uₙ` with `χ` the non-principal character modulo `4` (`χ(n) = sin ½nπ`).
* Theorem 385: `(1 + 2x + 2x⁴ + 2x⁹ + ⋯)⁴ = 1 + 8 ∑' m u_m` (`m` not a multiple of `4`), from
  Theorems 312 and 384 (`theta_pow_four`).
* Theorem 386 (Jacobi): the number `r₄(n)` of representations of `n ≥ 1` as a sum of four squares
  (order and signs counted) is `8` times the sum of the divisors of `n` not divisible by `4`
  (`sumFourSquaresCount_eq`).
-/

open Finset Filter Topology Real

namespace NTKB.HardyWright

variable {x : ℝ}

/-! ### Values at multiples of `½π` -/

lemma nat_mul_pi_div_two (k : ℕ) : (k : ℝ) * (π / 2) = ((k % 4 : ℕ) : ℝ) * (π / 2) + (k / 4 : ℕ) * (2 * π) := by
  have := Nat.mod_add_div k 4
  have h : (k : ℝ) = ((k % 4 : ℕ) : ℝ) + 4 * ((k / 4 : ℕ) : ℝ) := by exact_mod_cast this.symm
  rw [h]; ring

/-- `sin (½kπ) = χ(k)`. -/
lemma sin_nat_mul_pi_div_two (k : ℕ) : sin (k * (π / 2)) = (chi4 k : ℝ) := by
  rw [nat_mul_pi_div_two, sin_add_nat_mul_two_pi, chi4_eq]
  have h4 : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have h2 : k % 2 = k % 4 % 2 := (Nat.mod_mod_of_dvd k (by norm_num)).symm
  interval_cases h : k % 4
  · simp [show k % 2 = 0 by omega]
  · simp [show k % 2 = 1 by omega]
  · simp [show k % 2 = 0 by omega, show (2 : ℝ) * (π / 2) = π by ring]
  · rw [if_neg (by omega), if_neg (by omega)]
    rw [show ((3 : ℕ) : ℝ) * (π / 2) = π / 2 + π by push_cast; ring, sin_add_pi, sin_pi_div_two]
    norm_num

/-- `cos (½kπ)` is `1, 0, -1, 0` according as `k ≡ 0, 1, 2, 3 (mod 4)`. -/
lemma cos_nat_mul_pi_div_two (k : ℕ) :
    cos (k * (π / 2)) = if k % 4 = 0 then 1 else if k % 4 = 2 then -1 else 0 := by
  rw [nat_mul_pi_div_two, cos_add_nat_mul_two_pi]
  have h4 : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases h : k % 4
  · simp
  · simp
  · simp [show (2 : ℝ) * (π / 2) = π by ring]
  · simp only [Nat.cast_ofNat]
    rw [show (3 : ℝ) * (π / 2) = π / 2 + π by ring, cos_add_pi, cos_pi_div_two]
    norm_num

lemma summable_mul_of_abs_le_one {g c : ℕ → ℝ} (hg : Summable g) (hc : ∀ n, |c n| ≤ 1) :
    Summable fun n => g n * c n :=
  Summable.of_norm_bounded hg.abs fun n => by
    rw [Real.norm_eq_abs, abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (hc n)

/-- `w(m) = m` for `4 ∤ m` and `0` for `4 ∣ m`. -/
lemma summable_weight_lambertU (hx : |x| < 1) :
    Summable fun n : ℕ => (if 4 ∣ n + 1 then 0 else ((n + 1 : ℕ) : ℝ)) * lambertU x (n + 1) :=
  Summable.of_norm_bounded (summable_succ_mul_lambertU hx).abs fun n => by
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    gcongr
    split_ifs <;> simp <;> positivity

lemma summable_succ_lambertU_mul_one_add (hx : |x| < 1) :
    Summable fun n : ℕ => lambertU x (n + 1) * (1 + lambertU x (n + 1)) :=
  (((summable_nat_add_iff (f := lambertU x) 1).2 (summable_abs_lambertU hx).of_abs).add
    ((summable_nat_add_iff (f := fun n => lambertU x n ^ 2) 1).2 (summable_lambertU_sq hx))).congr
    fun n => by ring

/-! ### Theorem 384 -/

/-- **Theorem 384** (Hardy–Wright). For `|x| < 1`,
`(¼ + u₁ - u₃ + u₅ - u₇ + ⋯)² = 1/16 + ½(u₁ + 2u₂ + 3u₃ + 5u₅ + ⋯)`, where the last series has no
terms in `u₄, u₈, u₁₂, …`; here `u₁ - u₃ + u₅ - ⋯ = ∑ χ(n) uₙ`. -/
@[kb "hardywright2008" "Thm 384, p. 433"]
theorem sq_quarter_add_chi4 (hx : |x| < 1) :
    (1 / 4 + ∑' n : ℕ, (chi4 (n + 1) : ℝ) * lambertU x (n + 1)) ^ 2 =
      1 / 16 + 1 / 2 * ∑' n : ℕ, (if 4 ∣ n + 1 then 0 else ((n + 1 : ℕ) : ℝ)) * lambertU x (n + 1) := by
  have hθ : ∀ k : ℤ, π / 2 ≠ 2 * k * π := by
    intro k hk
    have h1 : ((4 * k : ℤ) : ℝ) * π = 1 * π := by push_cast; linarith
    have : (4 * k : ℤ) = 1 := by exact_mod_cast mul_right_cancel₀ pi_ne_zero h1
    omega
  have h := cotangent_identity hx hθ
  have hcot : cot (π / 2 / 2) = 1 := by
    rw [show π / 2 / 2 = π / 4 by ring, cot_eq_cos_div_sin, cos_pi_div_four, sin_pi_div_four,
      div_self (by positivity)]
  simp only [hcot, sin_nat_mul_pi_div_two, cos_nat_mul_pi_div_two] at h
  set c : ℕ → ℝ := fun k => if k % 4 = 0 then 1 else if k % 4 = 2 then -1 else 0 with hc
  have hc1 : ∀ k, |c k| ≤ 1 := fun k => by simp only [hc]; split_ifs <;> simp
  -- (a) `∑ uₙ(1 + uₙ) cos ½nπ = -∑ (2n - 1) u_{4n-2}`, by Theorem 382
  set f : ℕ → ℝ := fun n => lambertU x (n + 1) * (1 + lambertU x (n + 1)) * c (n + 1) with hf
  have hfs : Summable f := summable_mul_of_abs_le_one (summable_succ_lambertU_mul_one_add hx)
    fun n => hc1 _
  have hfe : Summable fun m => f (2 * m) :=
    hfs.comp_injective (i := fun m => 2 * m) (fun a b h => by simp at h; omega)
  have hfo : Summable fun m => f (2 * m + 1) :=
    hfs.comp_injective (i := fun m => 2 * m + 1) (fun a b h => by simp at h; omega)
  have hf0 : ∀ m, f (2 * m) = 0 := fun m => by
    simp only [hf, hc]; rw [if_neg (by omega), if_neg (by omega), mul_zero]
  have hf1 : ∀ m, f (2 * m + 1) =
      -((-1 : ℝ) ^ m * (lambertU x (2 * (m + 1)) * (1 + lambertU x (2 * (m + 1))))) := fun m => by
    simp only [hf, hc]
    rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring]
    rcases Nat.even_or_odd m with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [if_neg (by omega), if_pos (by omega), Even.neg_one_pow ⟨j, rfl⟩]; ring
    · rw [if_pos (by omega), Odd.neg_one_pow ⟨j, rfl⟩]; ring
  have hA : ∑' n, f n = -∑' n : ℕ, (2 * (n : ℝ) + 1) * lambertU x (4 * n + 2) := by
    rw [← tsum_even_add_odd hfe hfo, tsum_congr hf0, tsum_zero, zero_add, tsum_congr hf1,
      tsum_neg, tsum_neg_one_pow_lambertU hx]
  -- (b) `½∑ n uₙ (1 - cos ½nπ) = ½∑' n uₙ + ∑ (2n - 1) u_{4n-2}`
  set g : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ) * lambertU x (n + 1) * (1 - c (n + 1)) -
    (if 4 ∣ n + 1 then 0 else ((n + 1 : ℕ) : ℝ)) * lambertU x (n + 1) with hg
  have hgv : ∀ n, g n = if (n + 1) % 4 = 2 then ((n + 1 : ℕ) : ℝ) * lambertU x (n + 1) else 0 := by
    intro n
    simp only [hg, hc]
    have h4 : (n + 1) % 4 < 4 := Nat.mod_lt _ (by norm_num)
    have hd : 4 ∣ n + 1 ↔ (n + 1) % 4 = 0 := Nat.dvd_iff_mod_eq_zero
    interval_cases h : (n + 1) % 4 <;> simp [hd] <;> ring
  have hKb := summable_succ_mul_lambertU hx
  have hs1 : Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) * lambertU x (n + 1) * (1 - c (n + 1)) :=
    Summable.of_norm_bounded (hKb.abs.mul_left 2) fun n => by
      rw [Real.norm_eq_abs, abs_mul]
      have : |1 - c (n + 1)| ≤ 2 := by
        have := hc1 (n + 1); rw [abs_le] at this ⊢; constructor <;> linarith
      nlinarith [abs_nonneg (((n + 1 : ℕ) : ℝ) * lambertU x (n + 1))]
  have hw := summable_weight_lambertU hx
  have hgs : Summable g := hs1.sub hw
  have hgi : Function.Injective fun m : ℕ => 4 * m + 1 := fun a b h => by simp at h; omega
  have hgsupp : Function.support g ⊆ Set.range fun m : ℕ => 4 * m + 1 := by
    intro n hn
    rw [Function.mem_support, hgv] at hn
    split_ifs at hn with h2
    · exact ⟨n / 4, by simp; omega⟩
    · exact absurd rfl hn
  have hB : ∑' n, g n = ∑' m : ℕ, 2 * ((2 * (m : ℝ) + 1) * lambertU x (4 * m + 2)) := by
    rw [← hgi.tsum_eq hgsupp]
    refine tsum_congr fun m => ?_
    rw [hgv, if_pos (by omega)]
    push_cast; ring_nf
  have hsplit : ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * lambertU x (n + 1) * (1 - c (n + 1)) =
      ∑' n : ℕ, (if 4 ∣ n + 1 then 0 else ((n + 1 : ℕ) : ℝ)) * lambertU x (n + 1) + ∑' n, g n := by
    rw [← Summable.tsum_add hw hgs]; exact tsum_congr fun n => by simp only [hg]; ring
  have hX : ∑' m : ℕ, 2 * ((2 * (m : ℝ) + 1) * lambertU x (4 * m + 2)) =
      2 * ∑' m : ℕ, (2 * (m : ℝ) + 1) * lambertU x (4 * m + 2) := tsum_mul_left
  have hchi : ∑' n : ℕ, (chi4 (n + 1) : ℝ) * lambertU x (n + 1) =
      ∑' n : ℕ, lambertU x (n + 1) * (chi4 (n + 1) : ℝ) := tsum_congr fun n => mul_comm _ _
  rw [hchi, h, hA, hsplit, hB, hX]
  ring

/-! ### Theorem 385 -/

lemma tsum_pnat_eq_tsum_nat_succ (f : ℕ → ℝ) : ∑' n : ℕ+, f n = ∑' n : ℕ, f (n + 1) :=
  (Equiv.pnatEquivNat.symm.tsum_eq (fun n : ℕ+ => f n)).symm

/-- **Theorem 385** (Hardy–Wright). For `|x| < 1`,
`(1 + 2x + 2x⁴ + 2x⁹ + ⋯)⁴ = 1 + 8 ∑' m u_m`, where `m` runs through the positive integers which are
not multiples of `4`. -/
@[kb "hardywright2008" "Thm 385, p. 433"]
theorem theta_pow_four (hx : |x| < 1) :
    (1 + 2 * ∑' m : ℕ+, x ^ ((m : ℕ) ^ 2)) ^ 4 =
      1 + 8 * ∑' n : ℕ, (if 4 ∣ n + 1 then 0 else ((n + 1 : ℕ) : ℝ)) * lambertU x (n + 1) := by
  have h312 := jacobi_theta_sq hx
  rw [tsum_pnat_eq_tsum_nat_succ (fun n => (chi4 n : ℝ) * x ^ n / (1 - x ^ n))] at h312
  have e : ∀ n : ℕ, (chi4 (n + 1) : ℝ) * x ^ (n + 1) / (1 - x ^ (n + 1)) =
      (chi4 (n + 1) : ℝ) * lambertU x (n + 1) := fun n => by rw [lambertU, mul_div_assoc]
  rw [tsum_congr e] at h312
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h312]
  have h384 := sq_quarter_add_chi4 hx
  have : 1 + 4 * ∑' n : ℕ, (chi4 (n + 1) : ℝ) * lambertU x (n + 1) =
      4 * (1 / 4 + ∑' n : ℕ, (chi4 (n + 1) : ℝ) * lambertU x (n + 1)) := by ring
  rw [this, mul_pow, h384]
  ring


/-! ### Theorem 386 -/

/-- `r₄(n)`: the number of representations `n = a² + b² + c² + d²` with rational integers `a, b, c, d`
(representations differing in order or sign counted as distinct). -/
noncomputable def sumFourSquaresCount (n : ℕ) : ℕ :=
  {v : (ℤ × ℤ) × (ℤ × ℤ) | v.1.1 ^ 2 + v.1.2 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 = n}.ncard

lemma neg_le_and_le_of_sq_le {t : ℤ} {a : ℕ} (h : t ^ 2 ≤ a) : -(a : ℤ) ≤ t ∧ t ≤ a := by
  have ha : (0 : ℤ) ≤ a := by positivity
  constructor <;> nlinarith [sq_nonneg (t - 1), sq_nonneg (t + 1)]

lemma setOf_sq_add_sq_finite (a : ℕ) : {p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 2 = (a : ℤ)}.Finite := by
  refine ((Set.finite_Icc (-(a : ℤ)) a).prod (Set.finite_Icc (-(a : ℤ)) a)).subset ?_
  intro p hp
  simp only [Set.mem_setOf_eq] at hp
  have h1 := neg_le_and_le_of_sq_le (t := p.1) (a := a) (by nlinarith [sq_nonneg p.2])
  have h2 := neg_le_and_le_of_sq_le (t := p.2) (a := a) (by nlinarith [sq_nonneg p.1])
  exact ⟨⟨h1.1, h1.2⟩, ⟨h2.1, h2.2⟩⟩

/-- `r₄(n) = ∑_{a + b = n} r(a) r(b)`. -/
lemma sumFourSquaresCount_eq_sum (n : ℕ) :
    sumFourSquaresCount n =
      ∑ p ∈ antidiagonal n, sumTwoSquaresCount p.1 * sumTwoSquaresCount p.2 := by
  classical
  set T : ℕ → Finset (ℤ × ℤ) := fun a => (setOf_sq_add_sq_finite a).toFinset with hTdef
  have hT : ∀ a, sumTwoSquaresCount a = (T a).card := fun a => by
    rw [sumTwoSquaresCount, Set.ncard_eq_toFinset_card _ (setOf_sq_add_sq_finite a)]
  have hmem : ∀ a (p : ℤ × ℤ), p ∈ T a ↔ p.1 ^ 2 + p.2 ^ 2 = (a : ℤ) := fun a p => by
    simp [hTdef]
  have hset : {v : (ℤ × ℤ) × (ℤ × ℤ) | v.1.1 ^ 2 + v.1.2 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 = n} =
      ↑((antidiagonal n).biUnion fun p => T p.1 ×ˢ T p.2) := by
    ext v
    simp only [Set.mem_ofPred_eq, coe_biUnion, mem_coe, Set.mem_iUnion, mem_product, hmem,
      Finset.HasAntidiagonal.mem_antidiagonal, exists_prop]
    constructor
    · intro hv
      have h1 : 0 ≤ v.1.1 ^ 2 + v.1.2 ^ 2 := by positivity
      have h2 : 0 ≤ v.2.1 ^ 2 + v.2.2 ^ 2 := by positivity
      refine ⟨((v.1.1 ^ 2 + v.1.2 ^ 2).toNat, (v.2.1 ^ 2 + v.2.2 ^ 2).toNat), ?_, ?_, ?_⟩
      · have : (((v.1.1 ^ 2 + v.1.2 ^ 2).toNat + (v.2.1 ^ 2 + v.2.2 ^ 2).toNat : ℕ) : ℤ) = n := by
          push_cast [Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2]; linarith
        exact_mod_cast this
      · simp [Int.toNat_of_nonneg h1]
      · simp [Int.toNat_of_nonneg h2]
    · rintro ⟨p, hp, h1, h2⟩
      rw [← hp]; push_cast; linarith
  rw [sumFourSquaresCount, hset, Set.ncard_coe_finset, card_biUnion]
  · exact sum_congr rfl fun p _ => by rw [card_product, hT, hT]
  · intro p hp q hq hpq
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    rintro v hv1 hv2
    rw [mem_product, hmem, hmem] at hv1 hv2
    rw [Finset.mem_coe, Finset.HasAntidiagonal.mem_antidiagonal] at hp hq
    apply hpq
    have e1 : (p.1 : ℤ) = q.1 := by rw [← hv1.1, hv2.1]
    have e1' : p.1 = q.1 := by exact_mod_cast e1
    exact Prod.ext e1' (by omega)

/-- `∑ r₄(n) xⁿ = (∑_{m ∈ ℤ} x^{m²})⁴` for `|x| < 1`. -/
lemma hasSum_sumFourSquaresCount (hx : |x| < 1) :
    HasSum (fun n : ℕ => (sumFourSquaresCount n : ℝ) * x ^ n)
      ((∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 4) := by
  set f : ℕ → ℝ := fun n => (sumTwoSquaresCount n : ℝ) * x ^ n with hf
  have h2 := hasSum_sumTwoSquaresCount_mul_pow_nat hx
  have hnorm : Summable fun n => ‖f n‖ := by
    have := (hasSum_sumTwoSquaresCount_mul_pow_nat (x := |x|) (by rwa [abs_abs])).summable
    refine this.congr fun n => ?_
    simp [hf]
  have hC := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hnorm hnorm
  have hs := (summable_norm_sum_mul_antidiagonal_of_summable_norm hnorm hnorm).of_norm
  rw [h2.tsum_eq] at hC
  have e : ∀ n, ∑ kl ∈ antidiagonal n, f kl.1 * f kl.2 = (sumFourSquaresCount n : ℝ) * x ^ n := by
    intro n
    rw [sumFourSquaresCount_eq_sum, Nat.cast_sum, sum_mul]
    refine sum_congr rfl fun kl hkl => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
    simp only [hf]; push_cast
    rw [← hkl, pow_add]; ring
  have hv : ((∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 2) * ((∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 2) =
      (∑' m : ℤ, x ^ (m.natAbs ^ 2)) ^ 4 := by ring
  have := hs.hasSum
  rw [← hC, hv] at this
  exact this.congr_fun fun n => (e n).symm

/-- Uniqueness of the coefficients of a power series: if `∑ aₙ xⁿ = 0` for `0 < x < ½` (and
`∑ |aₙ| 2⁻ⁿ < ∞`), then every `aₙ = 0`. -/
lemma eq_zero_of_tsum_pow_eq_zero {a : ℕ → ℝ} (hs : Summable fun n => |a n| * (1 / 2 : ℝ) ^ n)
    (h : ∀ x : ℝ, 0 < x → x < 1 / 2 → ∑' n, a n * x ^ n = 0) : ∀ N, a N = 0 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    -- `g(x) = ∑ a_{n+N} xⁿ` vanishes on `(0, ½)` and is continuous on `[0, ½]`
    set g : ℝ → ℝ := fun x => ∑' n, a (n + N) * x ^ n with hg
    have hsN : Summable fun n => |a (n + N)| * (1 / 2 : ℝ) ^ n := by
      have := ((summable_nat_add_iff (f := fun n => |a n| * (1 / 2 : ℝ) ^ n) N).2 hs).mul_left
        ((2 : ℝ) ^ N)
      refine this.congr fun n => ?_
      rw [pow_add, show (2 : ℝ) ^ N * (|a (n + N)| * ((1 / 2) ^ n * (1 / 2) ^ N)) =
        |a (n + N)| * (1 / 2) ^ n * ((2 : ℝ) ^ N * (1 / 2) ^ N) by ring, ← mul_pow]
      norm_num
    have hbound : ∀ n (x : ℝ), x ∈ Set.Icc (0 : ℝ) (1 / 2) → ‖a (n + N) * x ^ n‖ ≤
        |a (n + N)| * (1 / 2 : ℝ) ^ n := fun n x hx => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hx.1]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.1 hx.2 n) (abs_nonneg _)
    have hcont : ContinuousOn g (Set.Icc 0 (1 / 2)) :=
      continuousOn_tsum (fun n => (continuous_const.mul (continuous_pow n)).continuousOn) hsN hbound
    have hzero : ∀ x ∈ Set.Ioo (0 : ℝ) (1 / 2), g x = 0 := by
      intro x hx
      have hsx : Summable fun n => a n * x ^ n :=
        Summable.of_norm_bounded hs fun n => by
          rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hx.1]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.1.le hx.2.le n) (abs_nonneg _)
      have h0 := h x hx.1 hx.2
      rw [← hsx.sum_add_tsum_nat_add N] at h0
      rw [sum_eq_zero fun k hk => by rw [ih k (mem_range.1 hk), zero_mul], zero_add] at h0
      have : ∑' n, a (n + N) * x ^ (n + N) = x ^ N * g x := by
        rw [hg, ← tsum_mul_left]; exact tsum_congr fun n => by ring
      rw [this] at h0
      exact (mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ hx.1.ne')
    have hg0 : g 0 = a N := by
      rw [hg]; simp only
      rw [tsum_eq_single 0 fun n hn => by rw [zero_pow hn, mul_zero]]
      simp
    -- the limit at `0⁺`
    have htend : Tendsto g (𝓝[Set.Ioo 0 (1 / 2)] 0) (𝓝 (g 0)) :=
      ((hcont 0 ⟨le_rfl, by norm_num⟩).mono Set.Ioo_subset_Icc_self).tendsto
    have htend0 : Tendsto g (𝓝[Set.Ioo 0 (1 / 2)] 0) (𝓝 0) :=
      tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun x hx => (hzero x hx).symm)
    have : (𝓝[Set.Ioo (0 : ℝ) (1 / 2)] 0).NeBot := by
      rw [nhdsWithin_Ioo_eq_nhdsGT (by norm_num)]; infer_instance
    rw [← hg0]
    exact tendsto_nhds_unique htend htend0

/-- The sum of the divisors of `N` which are not multiples of `4`. -/
lemma sum_divisors_not_four_le (N : ℕ) :
    ∑ d ∈ N.divisors.filter (fun d => ¬ 4 ∣ d), (d : ℝ) ≤ (N : ℝ) ^ 2 := by
  have h1 : ∑ d ∈ N.divisors.filter (fun d => ¬ 4 ∣ d), (d : ℝ) ≤ ∑ d ∈ N.divisors, (d : ℝ) :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity
  have h2 : ∑ d ∈ N.divisors, (d : ℝ) ≤ N.divisors.card • (N : ℝ) :=
    sum_le_card_nsmul _ _ _ fun d hd => by exact_mod_cast Nat.divisor_le hd
  have h3 : (N.divisors.card : ℝ) ≤ N := by exact_mod_cast Nat.card_divisors_le_self N
  rw [nsmul_eq_mul] at h2
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- **Theorem 386** (Jacobi; Hardy–Wright). The number of representations of a positive integer `n`
as the sum of four squares, representations which differ only in order or sign being counted as
distinct, is `8` times the sum of the divisors of `n` which are not multiples of `4`. -/
@[kb "hardywright2008" "Thm 386, p. 434"]
theorem sumFourSquaresCount_eq {n : ℕ} (hn : 0 < n) :
    sumFourSquaresCount n = 8 * ∑ d ∈ n.divisors.filter (fun d => ¬ 4 ∣ d), d := by
  set c : ℕ → ℝ := fun N => ∑ d ∈ N.divisors.filter (fun d => ¬ 4 ∣ d), (d : ℝ) with hc
  set a : ℕ → ℝ := fun N => (sumFourSquaresCount N : ℝ) - (if N = 0 then 1 else 0) - 8 * c N
    with ha
  have hc0 : ∀ N, 0 ≤ c N := fun N => sum_nonneg fun _ _ => by positivity
  -- absolute convergence at `½`
  have hcs : ∀ y : ℝ, 0 ≤ y → y ≤ 1 / 2 → Summable fun N => c N * y ^ N := by
    intro y hy0 hy
    have := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 (r := 1 / 2)
      (by rw [Real.norm_eq_abs]; norm_num)
    refine Summable.of_norm_bounded this fun N => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hc0 N), abs_pow, abs_of_nonneg hy0]
    exact mul_le_mul (sum_divisors_not_four_le N) (pow_le_pow_left₀ hy0 hy N) (by positivity)
      (by positivity)
  have hr4 : ∀ y : ℝ, |y| < 1 → Summable fun N => (sumFourSquaresCount N : ℝ) * y ^ N :=
    fun y hy => (hasSum_sumFourSquaresCount hy).summable
  have hs : Summable fun N => |a N| * (1 / 2 : ℝ) ^ N := by
    have h1 := hr4 (1 / 2) (by norm_num)
    have h2 := hcs (1 / 2) (by norm_num) le_rfl
    have h3 : Summable fun N : ℕ => (if N = 0 then (1 : ℝ) else 0) * (1 / 2 : ℝ) ^ N :=
      summable_of_ne_finset_zero (s := {0}) fun N hN => by simp at hN; simp [hN]
    have := ((h1.sub h3).sub (h2.mul_left 8)).abs
    refine this.congr fun N => ?_
    rw [← abs_of_pos (show (0 : ℝ) < (1 / 2) ^ N by positivity), ← abs_mul, abs_of_pos
      (show (0 : ℝ) < (1 / 2) ^ N by positivity)]
    simp only [ha]; ring_nf
  -- the generating function of `a` vanishes on `(0, ½)`
  have hzero : ∀ x : ℝ, 0 < x → x < 1 / 2 → ∑' N, a N * x ^ N = 0 := by
    intro x hx0 hx
    have hx1 : |x| < 1 := by rw [abs_of_pos hx0]; linarith
    -- `∑ r₄(N) xᴺ = 1 + 8 ∑ c(N) xᴺ`
    have hθ := theta_pow_four hx1
    have hint := tsum_int_theta hx1
    have hL := hasSum_lambert (a := fun n => if 4 ∣ n then 0 else (n : ℝ)) (fun n => by
      split_ifs <;> simp) hx1
    set A : ℕ → ℝ := fun n => (if 4 ∣ n then 0 else (n : ℝ)) * x ^ n / (1 - x ^ n) with hA
    set B : ℕ → ℝ := fun N => (∑ d ∈ N.divisors, (if 4 ∣ d then 0 else (d : ℝ))) * x ^ N with hB
    have hcN : ∀ N : ℕ, ∑ d ∈ N.divisors, (if 4 ∣ d then 0 else (d : ℝ)) = c N := fun N => by
      simp only [hc]; rw [sum_filter]; exact sum_congr rfl fun d _ => by split_ifs <;> simp_all
    have hW : ∑' n : ℕ, (if 4 ∣ n + 1 then 0 else ((n + 1 : ℕ) : ℝ)) * lambertU x (n + 1) =
        ∑' N : ℕ, c N * x ^ N := by
      calc ∑' n : ℕ, (if 4 ∣ n + 1 then 0 else ((n + 1 : ℕ) : ℝ)) * lambertU x (n + 1)
          = ∑' n : ℕ, A (n + 1) := tsum_congr fun n => by simp only [hA, lambertU]; rw [mul_div_assoc]
        _ = ∑' n : ℕ+, A n := (tsum_pnat_eq_tsum_nat_succ A).symm
        _ = ∑' N : ℕ+, B N := hL.tsum_eq
        _ = ∑' N : ℕ, B (N + 1) := tsum_pnat_eq_tsum_nat_succ B
        _ = ∑' N : ℕ, c (N + 1) * x ^ (N + 1) := tsum_congr fun N => by simp only [hB]; rw [hcN]
        _ = ∑' N : ℕ, c N * x ^ N := by
          rw [(hcs x hx0.le hx.le).tsum_eq_zero_add]; simp [hc]
    have hgen := (hasSum_sumFourSquaresCount hx1).tsum_eq
    rw [hint, hθ, hW] at hgen
    have hsr := hr4 x hx1
    have h3 : Summable fun N : ℕ => (if N = 0 then (1 : ℝ) else 0) * x ^ N :=
      summable_of_ne_finset_zero (s := {0}) fun N hN => by simp at hN; simp [hN]
    have h3v : ∑' N : ℕ, (if N = 0 then (1 : ℝ) else 0) * x ^ N = 1 := by
      rw [tsum_eq_single 0 fun N hN => by simp [hN]]; simp
    have hcx := hcs x hx0.le hx.le
    calc ∑' N, a N * x ^ N
        = ∑' N, (sumFourSquaresCount N : ℝ) * x ^ N -
            ∑' N : ℕ, (if N = 0 then (1 : ℝ) else 0) * x ^ N - 8 * ∑' N, c N * x ^ N := by
          rw [← tsum_mul_left, ← Summable.tsum_sub hsr h3, ← Summable.tsum_sub (hsr.sub h3)
            (hcx.mul_left 8)]
          exact tsum_congr fun N => by simp only [ha]; ring
      _ = 0 := by rw [hgen, h3v]; ring
  have := eq_zero_of_tsum_pow_eq_zero hs hzero n
  simp only [ha, if_neg hn.ne', sub_zero, sub_eq_zero] at this
  have h' : ((sumFourSquaresCount n : ℕ) : ℝ) =
      ((8 * ∑ d ∈ n.divisors.filter (fun d => ¬ 4 ∣ d), d : ℕ) : ℝ) := by
    rw [this]; push_cast; rfl
  exact_mod_cast h'

end NTKB.HardyWright
