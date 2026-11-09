/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.ArithmeticFunctions.Average

/-!
# Hardy–Wright, § 18.6: the number of squarefree numbers

* Theorem 333 (Gegenbauer): `Q(x) = 6x/π² + O(√x)`, `Q(x)` the number of squarefree `n ≤ x`;
  so the probability that a number is squarefree is `6/π²`.
* Theorem 334: `∑_{n ≤ x} |μ(n)| = 6x/π² + O(√x)`.

Proof as in the book: every `n ≤ y²` is `d² q` with `q` squarefree in exactly one way, so
`[y²] = ∑_{d ≤ y} Q(y²/d²)`; Theorem 268 inverts this to `Q(y²) = ∑_{d ≤ y} μ(d) [y²/d²]`, and
`∑ μ(d)/d² = 6/π²`.
-/

open Finset Filter Topology Asymptotics Real
open scoped ArithmeticFunction.Moebius

namespace NTKB.HardyWright

/-- Uniqueness of `n = b² a` with `a` squarefree. -/
lemma sq_mul_squarefree_unique {a b a' b' : ℕ} (ha : Squarefree a) (ha' : Squarefree a')
    (hb : b ≠ 0) (hb' : b' ≠ 0) (h : b ^ 2 * a = b' ^ 2 * a') : a = a' ∧ b = b' := by
  have ha0 : a ≠ 0 := ha.ne_zero
  have ha0' : a' ≠ 0 := ha'.ne_zero
  have key : ∀ p, a.factorization p = a'.factorization p ∧ b.factorization p = b'.factorization p := by
    intro p
    have h1 := congrArg (fun n => n.factorization p) h
    rw [Nat.factorization_mul (pow_ne_zero 2 hb) ha0, Nat.factorization_mul (pow_ne_zero 2 hb') ha0',
      Finsupp.add_apply, Finsupp.add_apply, Nat.factorization_pow, Nat.factorization_pow,
      Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul] at h1
    have h2 := ha.natFactorization_le_one p
    have h3 := ha'.natFactorization_le_one p
    omega
  exact ⟨Nat.eq_of_factorization_eq ha0 ha0' fun p => (key p).1,
    Nat.eq_of_factorization_eq hb hb' fun p => (key p).2⟩

/-- Every `m ≤ X` is `d² q` with `q` squarefree in exactly one way: if `X ≤ N²`, then
`X = ∑_{d ≤ N} #{q ≤ X/d² : q squarefree}`. -/
lemma card_eq_sum_card_squarefree (X N : ℕ) (hXN : ∀ d, d ^ 2 ≤ X → d ≤ N) :
    X = ∑ d ∈ Ioc 0 N, #((Ioc 0 (X / d ^ 2)).filter Squarefree) := by
  rw [← card_sigma]
  have hX : X = #(Ioc 0 X) := by simp
  conv_lhs => rw [hX]
  symm
  refine card_bij (fun x _ => x.1 ^ 2 * x.2) ?_ ?_ ?_
  · intro x hx
    simp only [mem_sigma, mem_Ioc, mem_filter] at hx ⊢
    have hd : 0 < x.1 ^ 2 := pow_pos hx.1.1 2
    refine ⟨Nat.mul_pos hd hx.2.1.1, ?_⟩
    calc x.1 ^ 2 * x.2 ≤ x.1 ^ 2 * (X / x.1 ^ 2) := Nat.mul_le_mul_left _ hx.2.1.2
      _ ≤ X := Nat.mul_div_le X _
  · intro x hx y hy hxy
    simp only [mem_sigma, mem_Ioc, mem_filter] at hx hy
    obtain ⟨h1, h2⟩ := sq_mul_squarefree_unique hx.2.2 hy.2.2 hx.1.1.ne' hy.1.1.ne' hxy
    exact Sigma.ext h2 (heq_of_eq h1)
  · intro m hm
    simp only [mem_Ioc] at hm
    obtain ⟨a, b, ha, hb, hab, hsq⟩ := Nat.sq_mul_squarefree_of_pos hm.1
    refine ⟨⟨b, a⟩, ?_, hab⟩
    simp only [mem_sigma, mem_Ioc, mem_filter]
    have hb2 : b ^ 2 ≤ X := by
      calc b ^ 2 ≤ b ^ 2 * a := Nat.le_mul_of_pos_right _ ha
        _ = m := hab
        _ ≤ X := hm.2
    refine ⟨⟨hb, ?_⟩, ⟨ha, ?_⟩, hsq⟩
    · exact hXN b hb2
    · rw [Nat.le_div_iff_mul_le (pow_pos hb 2), mul_comm, hab]; exact hm.2

/-- `Q(x)`, the number of squarefree `n ≤ x`. -/
noncomputable def squarefreeCount (x : ℝ) : ℕ := #((Ioc 0 ⌊x⌋₊).filter Squarefree)

/-- Hardy–Wright § 18.6: `[y²] = ∑_{d ≤ y} Q(y²/d²)`, hence by Theorem 268
`Q(y²) = ∑_{d ≤ y} μ(d) [y²/d²]`. -/
lemma squarefreeCount_sq_eq {y : ℝ} (hy : 1 ≤ y) :
    (squarefreeCount (y ^ 2) : ℝ) = ∑ n ∈ Ioc 0 ⌊y⌋₊, (μ n : ℝ) * ⌊(y / n) ^ 2⌋₊ := by
  have hinv := moebius_inversion_floor (E := ℝ) (F := fun y => (squarefreeCount (y ^ 2) : ℝ))
    (G := fun y => (⌊y ^ 2⌋₊ : ℝ)) (fun y hy => by
      have hX := card_eq_sum_card_squarefree ⌊y ^ 2⌋₊ ⌊y⌋₊ (fun d hd => by
        apply Nat.le_floor
        have h1 : ((d : ℕ) : ℝ) ^ 2 ≤ y ^ 2 := by
          have := (Nat.le_floor_iff (sq_nonneg y)).mp hd
          exact_mod_cast this
        nlinarith [sq_nonneg ((d : ℝ) - y), Nat.cast_nonneg (α := ℝ) d])
      rw [hX]
      push_cast
      refine sum_congr rfl fun n hn => ?_
      rw [squarefreeCount, div_pow, ← Nat.cast_pow, Nat.floor_div_natCast]) y hy
  simp only [zsmul_eq_mul] at hinv
  exact hinv

/-- **Theorem 333** (Gegenbauer; Hardy–Wright). `Q(x) = 6x/π² + O(√x)`: the number of squarefree
`n ≤ x` is `6x/π² + O(√x)`. -/
@[kb "hardywright2008" "Thm 333, p. 374"]
theorem squarefreeCount_sub_isBigO :
    (fun x : ℝ => (squarefreeCount x : ℝ) - 6 / π ^ 2 * x) =O[atTop] fun x => √x := by
  refine IsBigO.of_bound 3 ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  set y := √x with hydef
  have hy : 1 ≤ y := by rw [hydef]; exact Real.one_le_sqrt.mpr hx
  have hxy : x = y ^ 2 := (Real.sq_sqrt (by linarith)).symm
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (Real.sqrt_nonneg _), ← hydef, hxy,
    squarefreeCount_sq_eq hy]
  have hN : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hN1 : y < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one y
  have h1 := abs_sum_moebius_div_sq_sub_le ⌊y⌋₊
  have key : ∑ n ∈ Ioc 0 ⌊y⌋₊, (μ n : ℝ) * ⌊(y / n) ^ 2⌋₊ - 6 / π ^ 2 * y ^ 2 =
      ∑ n ∈ Ioc 0 ⌊y⌋₊, (μ n : ℝ) * ((⌊(y / n) ^ 2⌋₊ : ℝ) - (y / n) ^ 2) -
        y ^ 2 * (6 / π ^ 2 - ∑ n ∈ Ioc 0 ⌊y⌋₊, (μ n : ℝ) / (n : ℝ) ^ 2) := by
    simp only [mul_sub, sum_sub_distrib, mul_sum]
    have : ∀ n ∈ Ioc 0 ⌊y⌋₊, (μ n : ℝ) * (y / n) ^ 2 = y ^ 2 * ((μ n : ℝ) / (n : ℝ) ^ 2) :=
      fun n _ => by ring
    rw [sum_congr rfl this]
    ring
  rw [key]
  have hA : |∑ n ∈ Ioc 0 ⌊y⌋₊, (μ n : ℝ) * ((⌊(y / n) ^ 2⌋₊ : ℝ) - (y / n) ^ 2)| ≤ y := by
    calc _ ≤ ∑ n ∈ Ioc 0 ⌊y⌋₊, |(μ n : ℝ) * ((⌊(y / n) ^ 2⌋₊ : ℝ) - (y / n) ^ 2)| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n ∈ Ioc 0 ⌊y⌋₊, (1 : ℝ) := by
          refine sum_le_sum fun n _ => ?_
          rw [abs_mul]
          have hμ : |(μ n : ℝ)| ≤ 1 := by
            rw [← Int.cast_abs, ArithmeticFunction.abs_moebius]; split_ifs <;> norm_num
          have hf1 := Nat.floor_le (sq_nonneg (y / n))
          have hf2 := Nat.lt_floor_add_one ((y / n) ^ 2)
          have : |(⌊(y / n) ^ 2⌋₊ : ℝ) - (y / n) ^ 2| ≤ 1 := by
            rw [abs_le]; constructor <;> linarith
          nlinarith [abs_nonneg (μ n : ℝ), abs_nonneg ((⌊(y / n) ^ 2⌋₊ : ℝ) - (y / n) ^ 2)]
      _ = ⌊y⌋₊ := by simp
      _ ≤ y := hN
  have hB : |y ^ 2 * (6 / π ^ 2 - ∑ n ∈ Ioc 0 ⌊y⌋₊, (μ n : ℝ) / (n : ℝ) ^ 2)| ≤ 2 * y := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg y)]
    calc y ^ 2 * |6 / π ^ 2 - ∑ n ∈ Ioc 0 ⌊y⌋₊, (μ n : ℝ) / (n : ℝ) ^ 2|
        ≤ y ^ 2 * (2 / ((⌊y⌋₊ : ℝ) + 1)) := by gcongr
      _ ≤ y ^ 2 * (2 / y) := by gcongr
      _ = 2 * y := by field_simp
  calc _ ≤ _ + _ := abs_sub _ _
    _ ≤ y + 2 * y := add_le_add hA hB
    _ = 3 * y := by ring

lemma isLittleO_sqrt_id : (fun x : ℝ => √x) =o[atTop] fun x => x := by
  rw [isLittleO_iff]
  intro c hc
  filter_upwards [eventually_ge_atTop (1 / c ^ 2), eventually_gt_atTop 0] with x hx hx0
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg hx0.le]
  have hs : 0 < √x := Real.sqrt_pos.mpr hx0
  have h1 : 1 / c ≤ √x := by
    rw [show 1 / c = √(1 / c ^ 2) by rw [Real.sqrt_div' _ (sq_nonneg c), Real.sqrt_one, Real.sqrt_sq hc.le]]
    exact Real.sqrt_le_sqrt hx
  have h2 : 1 ≤ c * √x := by rwa [div_le_iff₀' hc] at h1
  calc √x = √x * 1 := (mul_one _).symm
    _ ≤ √x * (c * √x) := by gcongr
    _ = c * x := by rw [mul_left_comm, Real.mul_self_sqrt hx0.le]

/-- **Theorem 333** (Hardy–Wright), first form: the probability that a number is squarefree is
`6/π²`, i.e. `Q(x)/x → 6/π²`. -/
@[kb "hardywright2008" "Thm 333, p. 374"]
theorem tendsto_squarefreeCount_div :
    Tendsto (fun x : ℝ => (squarefreeCount x : ℝ) / x) atTop (𝓝 (6 / π ^ 2)) := by
  have h1 : (fun x : ℝ => (squarefreeCount x : ℝ) - 6 / π ^ 2 * x) =o[atTop] fun x => x :=
    squarefreeCount_sub_isBigO.trans_isLittleO isLittleO_sqrt_id
  have h2 := h1.tendsto_div_nhds_zero
  have h3 := h2.add (tendsto_const_nhds (x := 6 / π ^ 2))
  rw [zero_add] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  field_simp
  ring

/-- **Theorem 334** (Hardy–Wright). `∑_{n ≤ x} |μ(n)| = 6x/π² + O(√x)`. -/
@[kb "hardywright2008" "Thm 334, p. 375"]
theorem sum_abs_moebius_sub_isBigO :
    (fun x : ℝ => ∑ n ∈ Ioc 0 ⌊x⌋₊, (|μ n| : ℝ) - 6 / π ^ 2 * x) =O[atTop] fun x => √x := by
  refine squarefreeCount_sub_isBigO.congr_left fun x => ?_
  rw [squarefreeCount, card_filter]
  push_cast
  congr 1
  refine sum_congr rfl fun n _ => ?_
  rw [← Int.cast_abs, ArithmeticFunction.abs_moebius]
  split_ifs <;> simp

end NTKB.HardyWright
