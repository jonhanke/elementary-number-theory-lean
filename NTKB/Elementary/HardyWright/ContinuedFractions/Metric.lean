/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.ContinuedFractions.Infinite
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Filter.Cofinite
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Metric theorems on Diophantine approximation (Hardy–Wright, §§ 11.10 and 11.11)

* Theorem 198: if `∑ 1/χ(q)` converges, the set of `ξ` with `|p/q - ξ| < 1/(q χ(q))` for infinitely many
  `q` is null (Hardy–Wright's covering argument, i.e. the first Borel–Cantelli lemma).
-/

namespace NTKB.HardyWright

open MeasureTheory Filter Set Topology GenContFract

/-- **Theorem 198.** If `χ(q) > 0` and `∑ 1/χ(q)` is convergent, then the set of `ξ` which satisfy
`|p/q - ξ| < 1/(q χ(q))` for an infinity of `q` is null. -/
@[kb "hardywright2008" "Thm 198, p. 216"]
theorem volume_infinite_approx_eq_zero {χ : ℕ → ℝ} (hχ : ∀ q, 0 < χ q)
    (hsum : Summable fun q ↦ 1 / χ q) :
    volume {ξ : ℝ | {q : ℕ | 0 < q ∧ ∃ p : ℤ, |(p : ℝ) / q - ξ| < 1 / (q * χ q)}.Infinite} = 0 := by
  set S := {ξ : ℝ | {q : ℕ | 0 < q ∧ ∃ p : ℤ, |(p : ℝ) / q - ξ| < 1 / (q * χ q)}.Infinite}
  -- it suffices to treat `S ∩ [-M, M]`
  have hcover : S ⊆ ⋃ M : ℕ, S ∩ Icc (-(M : ℝ)) M := by
    intro ξ hξ
    obtain ⟨M, hM⟩ := exists_nat_ge |ξ|
    exact mem_iUnion.mpr ⟨M, hξ, abs_le.mp hM⟩
  refine measure_mono_null hcover (measure_iUnion_null fun M ↦ ?_)
  -- the sets `s q` of `ξ ∈ [-M, M]` approximated with denominator `q`
  set s : ℕ → Set ℝ := fun q ↦
    {ξ | ξ ∈ Icc (-(M : ℝ)) M ∧ 0 < q ∧ ∃ p : ℤ, |(p : ℝ) / q - ξ| < 1 / (q * χ q)} with hs
  have hsub : S ∩ Icc (-(M : ℝ)) M ⊆ limsup s atTop := by
    rintro ξ ⟨hξ, hM⟩
    rw [Filter.mem_limsup_iff_frequently_mem, Nat.frequently_atTop_iff_infinite]
    exact Set.Infinite.mono (fun q hq ↦ by simp only [Set.mem_setOf_eq, hs] at hq ⊢; exact ⟨hM, hq⟩) hξ
  refine measure_mono_null hsub (measure_limsup_atTop_eq_zero ?_)
  -- `vol (s q) ≤ (4M + 6)/χ(q)`
  have hbound : ∀ q, volume (s q) ≤ ENNReal.ofReal ((4 * M + 6) * (1 / χ q)) := by
    intro q
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · have : s 0 = ∅ := by
        ext ξ; simp [hs]
      rw [this, measure_empty]; simp
    have hqr : (0 : ℝ) < q := by exact_mod_cast hq
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    set r := 1 / (q * χ q) with hr
    have hr0 : 0 < r := by have := hχ q; positivity
    by_cases hr1 : 1 < r
    · -- the whole interval `[-M, M]`
      calc volume (s q) ≤ volume (Icc (-(M : ℝ)) M) := measure_mono fun ξ h ↦ h.1
        _ = ENNReal.ofReal (2 * M) := by rw [Real.volume_Icc]; ring_nf
        _ ≤ ENNReal.ofReal ((4 * M + 6) * (1 / χ q)) := by
          apply ENNReal.ofReal_le_ofReal
          have : 1 / χ q = q * r := by rw [hr]; field_simp
          rw [this]
          have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
          have : 1 ≤ q * r := by nlinarith
          nlinarith
    · push Not at hr1
      -- `s q` is covered by the intervals around `p/q`, `|p| ≤ (M + 1) q`
      set N : ℤ := (M + 1) * q with hN
      have hcov : s q ⊆ ⋃ p ∈ Finset.Icc (-N) N, Ioo ((p : ℝ) / q - r) (p / q + r) := by
        rintro ξ ⟨⟨h1, h2⟩, -, p, hp⟩
        refine mem_iUnion₂.mpr ⟨p, ?_, ?_⟩
        · rw [Finset.mem_Icc]
          have hp' : |(p : ℝ) / q| ≤ M + 1 := by
            have := abs_sub_abs_le_abs_sub ((p : ℝ) / q) ξ
            have hξ : |ξ| ≤ M := abs_le.mpr ⟨h1, h2⟩
            linarith
          rw [abs_div, abs_of_pos hqr, div_le_iff₀ hqr] at hp'
          have : ((|p| : ℤ) : ℝ) ≤ ((N : ℤ) : ℝ) := by rw [hN]; push_cast; linarith
          have := (Int.cast_le.mp this)
          constructor <;> linarith [neg_abs_le p, le_abs_self p]
        · rw [abs_lt] at hp
          constructor <;> linarith [hp.1, hp.2]
      calc volume (s q) ≤ volume (⋃ p ∈ Finset.Icc (-N) N, Ioo ((p : ℝ) / q - r) (p / q + r)) :=
            measure_mono hcov
        _ ≤ ∑ p ∈ Finset.Icc (-N) N, volume (Ioo ((p : ℝ) / q - r) (p / q + r)) :=
            measure_biUnion_finset_le _ _
        _ = ∑ p ∈ Finset.Icc (-N) N, ENNReal.ofReal (2 * r) := by
            congr 1; ext p; rw [Real.volume_Ioo]; ring_nf
        _ = ENNReal.ofReal ((2 * N + 1) * (2 * r)) := by
            rw [Finset.sum_const, Int.card_Icc, nsmul_eq_mul,
              show N + 1 - -N = 2 * N + 1 by ring]
            have h0 : 0 ≤ 2 * N + 1 := by positivity
            have hc : (((2 * N + 1).toNat : ℕ) : ENNReal) = ENNReal.ofReal (2 * N + 1) := by
              rw [← ENNReal.ofReal_natCast]
              congr 1
              have : (((2 * N + 1).toNat : ℕ) : ℤ) = 2 * N + 1 := Int.toNat_of_nonneg h0
              exact_mod_cast this
            rw [hc, ← ENNReal.ofReal_mul (by exact_mod_cast h0)]
        _ ≤ ENNReal.ofReal ((4 * M + 6) * (1 / χ q)) := by
            apply ENNReal.ofReal_le_ofReal
            have : 1 / χ q = q * r := by rw [hr]; field_simp
            rw [this, hN]
            push_cast
            nlinarith
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
  rw [← ENNReal.ofReal_tsum_of_nonneg (f := fun q ↦ (4 * (M : ℝ) + 6) * (1 / χ q))
    (fun q ↦ by have := hχ q; positivity) (hsum.mul_left (4 * (M : ℝ) + 6))]
  exact ENNReal.ofReal_ne_top

/-! ### Theorem 196 -/

/-- The "cylinder" sets of Hardy–Wright § 11.10, described through complete quotients:
`cyl m K` is the set of irrational `α > 1` whose first `m` quotients satisfy `aⱼ ≤ K j`
(auxiliary). -/
private def cyl : ℕ → (ℕ → ℕ) → Set ℝ
  | 0, _ => {α | 1 < α ∧ Irrational α}
  | m + 1, K => {α | ∃ j : ℕ, j < K 0 ∧ (j + 1 : ℝ) < α ∧ α < j + 2 ∧
      1 / (α - (j + 1)) ∈ cyl m (fun i ↦ K (i + 1))}

/-- The Möbius map `t ↦ (t p + p')/(t q + q')`. -/
private noncomputable def mob (p p' q q' : ℤ) (t : ℝ) : ℝ := (t * p + p') / (t * q + q')

private lemma mob_comp (p p' q q' : ℤ) (c : ℕ) {β : ℝ} (hβ : β ≠ 0) :
    mob p p' q q' ((c + 1 : ℝ) + 1 / β) = mob ((c + 1) * p + p') p ((c + 1) * q + q') q β := by
  unfold mob
  rw [show ((c + 1 : ℝ) + 1 / β) * p + p' = (((c + 1) * p + p') * β + p) / β by field_simp; ring,
    show ((c + 1 : ℝ) + 1 / β) * q + q' = (((c + 1) * q + q') * β + q) / β by field_simp; ring,
    div_div_div_cancel_right₀ hβ]
  push_cast; ring_nf

/-- `∑_{j < N} 1/(((j+1)q + q')((j+2)q + q')) = N/((q + q')((N+1)q + q'))`. -/
private lemma telescope (q q' : ℝ) (hq : 0 < q) (hq' : 0 ≤ q') (N : ℕ) :
    ∑ j ∈ Finset.range N, 1 / (((j + 1) * q + q') * ((j + 2) * q + q')) =
      N / ((q + q') * ((N + 1) * q + q')) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : 0 < q + q' := by linarith
    have h2 : 0 < ((N : ℝ) + 1) * q + q' := by positivity
    have h3 : 0 < ((N : ℝ) + 2) * q + q' := by positivity
    push_cast
    field_simp
    ring

/-- Hardy–Wright's estimate: the image of `cyl m K` under a unimodular Möbius map with `q ≥ 1`,
`q' ≥ 0` has measure at most `∏_{i<m} K i/(K i + 1)` times the length `1/(q(q + q'))` of
the image of `(1, ∞)`. -/
private lemma volume_mob_cyl (m : ℕ) : ∀ (K : ℕ → ℕ) (p p' q q' : ℤ), 1 ≤ q → 0 ≤ q' →
    (p * q' - p' * q = 1 ∨ p * q' - p' * q = -1) →
    volume (mob p p' q q' '' cyl m K) ≤
      ENNReal.ofReal ((∏ i ∈ Finset.range m, ((K i : ℝ) / (K i + 1))) * (1 / (q * (q + q')))) := by
  induction m with
  | zero =>
    intro K p p' q q' hq hq' hdet
    simp only [Finset.range_zero, Finset.prod_empty, one_mul]
    have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hq'r : (0 : ℝ) ≤ q' := by exact_mod_cast hq'
    -- the image of `(1, ∞)` lies between `p/q` and `M 1 = (p + p')/(q + q')`
    have hsub : mob p p' q q' '' cyl 0 K ⊆ uIcc ((p : ℝ) / q) (mob p p' q q' 1) := by
      rintro _ ⟨t, ⟨ht, -⟩, rfl⟩
      have hden : 0 < t * q + q' := by nlinarith
      have hden1 : (0 : ℝ) < 1 * q + q' := by linarith
      have e : ∀ s : ℝ, 0 < s * q + q' →
          mob p p' q q' s = p / q + ((p' * q - p * q' : ℤ) : ℝ) / (q * (s * q + q')) := by
        intro s hs; unfold mob; push_cast; field_simp; ring
      rw [e t hden, e 1 hden1, Set.mem_uIcc]
      have hc : 1 / (q * (t * q + q')) ≤ 1 / (q * (1 * q + q')) :=
        one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left (by nlinarith) (by linarith))
      have hc0 : 0 < 1 / (q * (t * q + q')) := by positivity
      rcases hdet with h | h
      · have : p' * q - p * q' = -1 := by linarith
        rw [this]; push_cast
        right
        constructor
        · rw [show (-1 : ℝ) / (q * (1 * q + q')) = -(1 / (q * (1 * q + q'))) by ring,
            show (-1 : ℝ) / (q * (t * q + q')) = -(1 / (q * (t * q + q'))) by ring]
          linarith
        · rw [show (-1 : ℝ) / (q * (t * q + q')) = -(1 / (q * (t * q + q'))) by ring]
          linarith
      · have : p' * q - p * q' = 1 := by linarith
        rw [this]; push_cast
        left
        constructor
        · linarith
        · linarith
    calc volume (mob p p' q q' '' cyl 0 K) ≤ volume (uIcc ((p : ℝ) / q) (mob p p' q q' 1)) :=
          measure_mono hsub
      _ = ENNReal.ofReal |mob p p' q q' 1 - p / q| := Real.volume_interval
      _ = ENNReal.ofReal (1 / (q * (q + q'))) := by
          congr 1
          unfold mob
          have h1 : (0 : ℝ) < 1 * q + q' := by linarith
          rw [show (1 * (p : ℝ) + p') / (1 * q + q') - p / q =
            ((p' * q - p * q' : ℤ) : ℝ) / (q * (q + q')) by push_cast; field_simp; ring]
          rcases hdet with h | h
          · rw [show p' * q - p * q' = -1 by linarith]; push_cast
            rw [abs_div, abs_neg, abs_one, abs_of_pos (by positivity)]
          · rw [show p' * q - p * q' = 1 by linarith]; push_cast
            rw [abs_div, abs_one, abs_of_pos (by positivity)]
  | succ m ih =>
    intro K p p' q q' hq hq' hdet
    have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hq'r : (0 : ℝ) ≤ q' := by exact_mod_cast hq'
    -- split according to the first quotient `j + 1`
    have hsub : mob p p' q q' '' cyl (m + 1) K ⊆ ⋃ j ∈ Finset.range (K 0),
        mob ((j + 1) * p + p') p ((j + 1) * q + q') q '' cyl m (fun i ↦ K (i + 1)) := by
      rintro _ ⟨α, ⟨j, hj, h1, h2, hβ⟩, rfl⟩
      refine mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr hj, 1 / (α - (j + 1)), hβ, ?_⟩
      have hαj : 0 < α - (j + 1) := by linarith
      have hβ : 1 / (α - (j + 1)) ≠ 0 := by positivity
      rw [← mob_comp p p' q q' j hβ, one_div_one_div]
      congr 1; ring
    have hK : ∀ j ∈ Finset.range (K 0), volume (mob ((j + 1) * p + p') p ((j + 1) * q + q') q ''
        cyl m (fun i ↦ K (i + 1))) ≤ ENNReal.ofReal ((∏ i ∈ Finset.range m,
          ((K (i + 1) : ℝ) / (K (i + 1) + 1))) * (1 / ((((j : ℝ) + 1) * q + q') * ((j + 2) * q + q')))) := by
      intro j _
      have := ih (fun i ↦ K (i + 1)) ((j + 1) * p + p') p ((j + 1) * q + q') q
        (by nlinarith) (by omega) (by rcases hdet with h | h <;> [right; left] <;> linarith)
      convert this using 3
      push_cast; ring
    have hP : 0 ≤ ∏ i ∈ Finset.range m, ((K (i + 1) : ℝ) / (K (i + 1) + 1)) :=
      Finset.prod_nonneg fun i _ ↦ by positivity
    calc volume (mob p p' q q' '' cyl (m + 1) K)
        ≤ volume (⋃ j ∈ Finset.range (K 0), mob ((j + 1) * p + p') p ((j + 1) * q + q') q ''
            cyl m (fun i ↦ K (i + 1))) := measure_mono hsub
      _ ≤ ∑ j ∈ Finset.range (K 0), volume (mob ((j + 1) * p + p') p ((j + 1) * q + q') q ''
            cyl m (fun i ↦ K (i + 1))) := measure_biUnion_finset_le _ _
      _ ≤ ∑ j ∈ Finset.range (K 0), ENNReal.ofReal ((∏ i ∈ Finset.range m,
            ((K (i + 1) : ℝ) / (K (i + 1) + 1))) *
              (1 / ((((j : ℝ) + 1) * q + q') * ((j + 2) * q + q')))) := Finset.sum_le_sum hK
      _ = ENNReal.ofReal ((∏ i ∈ Finset.range m, ((K (i + 1) : ℝ) / (K (i + 1) + 1))) *
            ((K 0 : ℝ) / ((q + q') * ((K 0 + 1) * q + q')))) := by
          rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ by positivity), ← Finset.mul_sum,
            telescope (q : ℝ) q' (by linarith) hq'r]
      _ ≤ ENNReal.ofReal ((∏ i ∈ Finset.range (m + 1), ((K i : ℝ) / (K i + 1))) *
            (1 / (q * (q + q')))) := by
          apply ENNReal.ofReal_le_ofReal
          have hineq : (K 0 : ℝ) / ((q + q') * ((K 0 + 1) * q + q')) ≤
              ((K 0 : ℝ) / (K 0 + 1)) * (1 / (q * (q + q'))) := by
            rw [div_mul_div_comm, mul_one]
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            nlinarith
          rw [Finset.prod_range_succ']
          calc _ ≤ (∏ i ∈ Finset.range m, ((K (i + 1) : ℝ) / (K (i + 1) + 1))) *
                (((K 0 : ℝ) / (K 0 + 1)) * (1 / (q * (q + q')))) := mul_le_mul_of_nonneg_left hineq hP
            _ = _ := by ring

/-- The complete quotients of an infinite simple continued fraction lie in the cylinder sets. -/
private lemma mem_cyl {a : ℕ → ℤ} (ha : ∀ i, 1 ≤ i → 0 < a i) (n : ℕ) :
    ∀ (i : ℕ) (K : ℕ → ℕ) (y : ℝ), 1 ≤ i →
      Tendsto (fun t ↦ (cf (fun j ↦ ((a (i + j) : ℤ) : ℝ))).convs t) atTop (𝓝 y) →
      (∀ j < n, a (i + j) ≤ K j) → y ∈ cyl n K := by
  have hti : ∀ i, 1 ≤ i → ∀ j, 1 ≤ j → 0 < a (i + j) := fun i hi j _ ↦ ha (i + j) (by omega)
  induction n with
  | zero =>
    intro i K y hi hy _
    refine ⟨?_, ?_⟩
    · have := (cf_value_mem_Ioo (hti i hi) hy).1
      have h : (1 : ℝ) ≤ a (i + 0) := by exact_mod_cast ha (i + 0) (by omega)
      linarith
    · exact (irrational_iff_exists_unique_cf y).2 _ (hti i hi) hy
  | succ n ih =>
    intro i K y hi hy hK
    obtain ⟨h0, h1⟩ := cf_value_mem_Ioo (hti i hi) hy
    simp only [add_zero] at h0 h1
    have hai : 1 ≤ a i := ha i hi
    refine ⟨(a i - 1).toNat, ?_, ?_, ?_, ?_⟩
    · have := hK 0 (by omega); simp only [add_zero] at this; omega
    · have : ((a i - 1).toNat : ℝ) + 1 = a i := by
        have : ((a i - 1).toNat : ℤ) = a i - 1 := Int.toNat_of_nonneg (by omega)
        have : (((a i - 1).toNat : ℤ) : ℝ) = a i - 1 := by exact_mod_cast this
        push_cast at this ⊢; linarith
      linarith
    · have : ((a i - 1).toNat : ℝ) + 2 = a i + 1 := by
        have : ((a i - 1).toNat : ℤ) = a i - 1 := Int.toNat_of_nonneg (by omega)
        have : (((a i - 1).toNat : ℤ) : ℝ) = a i - 1 := by exact_mod_cast this
        push_cast at this ⊢; linarith
      linarith
    · have e1 : ((a i - 1).toNat : ℝ) + 1 = a i := by
        have : ((a i - 1).toNat : ℤ) = a i - 1 := Int.toNat_of_nonneg (by omega)
        have : (((a i - 1).toNat : ℤ) : ℝ) = a i - 1 := by exact_mod_cast this
        push_cast at this ⊢; linarith
      rw [e1]
      have ht := cf_tendsto_tail (hti i hi) hy
      simp only [add_zero] at ht
      have e : (fun j ↦ ((a (i + (j + 1)) : ℤ) : ℝ)) = fun j ↦ ((a (i + 1 + j) : ℤ) : ℝ) := by
        funext j; rw [show i + (j + 1) = i + 1 + j by ring]
      rw [e] at ht
      exact ih (i + 1) (fun j ↦ K (j + 1)) _ (by omega) ht
        (fun j hj ↦ by have := hK (j + 1) (by omega); rwa [show i + (j + 1) = i + 1 + j by ring] at this)

/-- **Theorem 196.** The partial quotients `aₙ` are unbounded for almost all `ξ`: the set of `ξ` whose
simple continued fraction has bounded quotients is null. -/
@[kb "hardywright2008" "Thm 196, p. 212"]
theorem volume_bdd_quotients_eq_zero :
    volume {ξ : ℝ | ∃ a : ℕ → ℤ, (∀ i, 1 ≤ i → 0 < a i) ∧
      Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 ξ) ∧ BddAbove (Set.range a)} = 0 := by
  -- the set lies in `⋃ a₀ ⋃ k ⋂ n, M_{a₀} (cyl n k)`
  have hcover : {ξ : ℝ | ∃ a : ℕ → ℤ, (∀ i, 1 ≤ i → 0 < a i) ∧
      Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 ξ) ∧ BddAbove (Set.range a)} ⊆
      ⋃ a₀ : ℤ, ⋃ k : ℕ, ⋂ n : ℕ, mob a₀ 1 1 0 '' cyl n (fun _ ↦ k) := by
    rintro ξ ⟨a, ha, hx, ⟨B, hB⟩⟩
    refine mem_iUnion.mpr ⟨a 0, mem_iUnion.mpr ⟨B.toNat, mem_iInter.mpr fun n ↦ ?_⟩⟩
    have ht := cf_tendsto_tail ha hx
    have hy := mem_cyl ha n 1 (fun _ ↦ B.toNat) (1 / (ξ - a 0)) le_rfl
      (by simpa [add_comm] using ht)
      (fun j _ ↦ by have := hB ⟨1 + j, rfl⟩; omega)
    refine ⟨1 / (ξ - a 0), hy, ?_⟩
    have hx0 := (cf_value_mem_Ioo ha hx).1
    unfold mob
    push_cast
    field_simp
    ring
  refine measure_mono_null hcover (measure_iUnion_null fun a₀ ↦ measure_iUnion_null fun k ↦ ?_)
  -- each `⋂ n` has measure `≤ (k/(k+1))ⁿ` for all `n`
  have hle : ∀ n : ℕ, volume (⋂ n : ℕ, mob a₀ 1 1 0 '' cyl n (fun _ ↦ k)) ≤
      ENNReal.ofReal (((k : ℝ) / (k + 1)) ^ n) := by
    intro n
    refine (measure_mono (iInter_subset _ n)).trans ?_
    have := volume_mob_cyl n (fun _ ↦ k) a₀ 1 1 0 le_rfl le_rfl (Or.inr (by ring))
    refine this.trans (le_of_eq ?_)
    congr 1
    simp [Finset.prod_const, div_pow]
  have hlim : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (((k : ℝ) / (k + 1)) ^ n)) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      (by rw [div_lt_one (by positivity)]; linarith))
  exact le_antisymm (ge_of_tendsto' hlim hle) (by simp)

/-! ### Theorem 197* -/

private lemma not_summable_inv_add_one {φ : ℕ → ℝ} (hφ : ∀ n, 0 < φ n)
    (h : ¬Summable fun n ↦ 1 / φ n) : ¬Summable fun n ↦ 1 / (φ n + 1) := by
  intro hs
  apply h
  have ht := hs.tendsto_atTop_zero
  have hev : ∀ᶠ n in atTop, 1 / (φ n + 1) < 1 / 2 := ht.eventually (gt_mem_nhds (by norm_num))
  refine Summable.of_norm_bounded_eventually (hs.mul_left 2) ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hev] with n hn
  have h0 := hφ n
  have h1 : 1 < φ n := by
    rw [div_lt_div_iff₀ (by linarith) (by norm_num)] at hn; linarith
  rw [Real.norm_eq_abs, abs_of_pos (by positivity), mul_one_div,
    div_le_div_iff₀ h0 (by linarith)]
  linarith

private lemma prod_le_exp (K : ℕ → ℕ) (m : ℕ) :
    ∏ j ∈ Finset.range m, ((K j : ℝ) / (K j + 1)) ≤
      Real.exp (-(∑ j ∈ Finset.range m, 1 / ((K j : ℝ) + 1))) := by
  have hneg : -(∑ j ∈ Finset.range m, 1 / ((K j : ℝ) + 1)) =
      ∑ j ∈ Finset.range m, -(1 / ((K j : ℝ) + 1)) := by rw [Finset.sum_neg_distrib]
  rw [hneg, Real.exp_sum]
  refine Finset.prod_le_prod₀ (fun j _ ↦ by positivity) fun j _ ↦ ?_
  have := Real.add_one_le_exp (-(1 / ((K j : ℝ) + 1)))
  have e : (K j : ℝ) / (K j + 1) = -(1 / ((K j : ℝ) + 1)) + 1 := by field_simp; ring
  rw [e]; exact this

/-- **Theorem 197*** (first half, Borel and Bernstein). If `∑ 1/φ(n)` is divergent (`φ(n) > 0`), then
the set of `ξ` for which `aₙ < φ(n)` for all sufficiently large `n` is null. (Hardy–Wright also assume
`φ` increasing; this is not needed.) -/
@[kb "hardywright2008" "Thm 197*, p. 215"]
theorem volume_eventually_lt_eq_zero {φ : ℕ → ℝ} (hφ : ∀ n, 0 < φ n)
    (hdiv : ¬Summable fun n ↦ 1 / φ n) :
    volume {ξ : ℝ | ∃ a : ℕ → ℤ, (∀ i, 1 ≤ i → 0 < a i) ∧
      Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 ξ) ∧
      ∃ N, ∀ n, N ≤ n → (a n : ℝ) < φ n} = 0 := by
  set Kseq : ℕ → ℕ → ℕ := fun N j ↦ (⌈φ (N + j)⌉ - 1).toNat with hKseq
  have hcover : {ξ : ℝ | ∃ a : ℕ → ℤ, (∀ i, 1 ≤ i → 0 < a i) ∧
      Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 ξ) ∧
      ∃ N, ∀ n, N ≤ n → (a n : ℝ) < φ n} ⊆
      ⋃ N : ℕ, ⋃ p : ℤ, ⋃ p' : ℤ, ⋃ q : ℤ, ⋃ q' : ℤ,
        ⋃ (_ : 1 ≤ q ∧ 0 ≤ q' ∧ (p * q' - p' * q = 1 ∨ p * q' - p' * q = -1)),
          ⋂ m : ℕ, mob p p' q q' '' cyl m (Kseq (N + 1)) := by
    rintro ξ ⟨a, ha, hx, N, hN⟩
    obtain ⟨y, hy⟩ := cf_convs_tendsto (fun j (hj : 1 ≤ j) ↦ ha (N + 1 + j) (by omega))
    have e := cf_value_eq_completeQuotient ha hx N hy
    obtain ⟨P1, Q1, hP1, hQ1⟩ := cf_nums_dens_int a N
    have hC1a : ((cf (fun i ↦ (a i : ℝ))).contsAux (N + 1)).a = P1 := by
      rw [← nth_cont_eq_succ_nth_contAux, ← num_eq_conts_a, hP1]
    have hC1b : ((cf (fun i ↦ (a i : ℝ))).contsAux (N + 1)).b = Q1 := by
      rw [← nth_cont_eq_succ_nth_contAux, ← den_eq_conts_b, hQ1]
    obtain ⟨P0, Q0, hC0a, hC0b, hQ0⟩ : ∃ P0 Q0 : ℤ,
        ((cf (fun i ↦ (a i : ℝ))).contsAux N).a = P0 ∧
        ((cf (fun i ↦ (a i : ℝ))).contsAux N).b = Q0 ∧ 0 ≤ Q0 := by
      rcases N with _ | N
      · exact ⟨1, 0, by simp [zeroth_contAux_eq_one_zero], by simp [zeroth_contAux_eq_one_zero],
          le_rfl⟩
      · obtain ⟨p, q, hp, hq⟩ := cf_nums_dens_int a N
        refine ⟨p, q, by rw [← nth_cont_eq_succ_nth_contAux, ← num_eq_conts_a, hp],
          by rw [← nth_cont_eq_succ_nth_contAux, ← den_eq_conts_b, hq], ?_⟩
        have := cf_dens_pos (pos_fin ha N) N le_rfl
        rw [hq] at this; exact_mod_cast this.le
    have hdet := cf_contsAux_det (fun i ↦ (a i : ℝ)) N
    rw [hC0a, hC0b, hC1a, hC1b] at hdet e
    have hdetZ : P0 * Q1 - Q0 * P1 = (-1) ^ N := by exact_mod_cast hdet
    have hQ1pos : 1 ≤ Q1 := by
      have := cf_dens_one_le (pos_finZ ha N) N le_rfl
      rw [hQ1] at this; exact_mod_cast this
    refine mem_iUnion.mpr ⟨N, mem_iUnion.mpr ⟨P1, mem_iUnion.mpr ⟨P0, mem_iUnion.mpr ⟨Q1,
      mem_iUnion.mpr ⟨Q0, mem_iUnion.mpr ⟨⟨hQ1pos, hQ0, ?_⟩, mem_iInter.mpr fun m ↦ ?_⟩⟩⟩⟩⟩⟩
    · rcases neg_one_pow_eq_or ℤ N with h | h <;> rw [h] at hdetZ
      · right; linarith
      · left; linarith
    · refine ⟨y, mem_cyl ha m (N + 1) (Kseq (N + 1)) y (by omega) hy fun j _ ↦ ?_, ?_⟩
      · have h1 := hN (N + 1 + j) (by omega)
        have h2 : (a (N + 1 + j) : ℝ) < ⌈φ (N + 1 + j)⌉ := h1.trans_le (Int.le_ceil _)
        have h3 : a (N + 1 + j) < ⌈φ (N + 1 + j)⌉ := by exact_mod_cast h2
        simp only [hKseq]
        omega
      · rw [e]; unfold mob; ring_nf
  refine measure_mono_null hcover (measure_iUnion_null fun N ↦ measure_iUnion_null fun p ↦
    measure_iUnion_null fun p' ↦ measure_iUnion_null fun q ↦ measure_iUnion_null fun q' ↦
      measure_iUnion_null fun hpq ↦ ?_)
  obtain ⟨hq, hq', hdet⟩ := hpq
  set K := Kseq (N + 1)
  set L : ℝ := 1 / (q * (q + q'))
  have hL : 0 ≤ L := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have : (0 : ℝ) ≤ q' := by exact_mod_cast hq'
    positivity
  have hle : ∀ m : ℕ, volume (⋂ m : ℕ, mob p p' q q' '' cyl m K) ≤
      ENNReal.ofReal (Real.exp (-(∑ j ∈ Finset.range m, 1 / ((K j : ℝ) + 1))) * L) := by
    intro m
    refine (measure_mono (iInter_subset _ m)).trans ?_
    refine (volume_mob_cyl m K p p' q q' hq hq' hdet).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (prod_le_exp K m) hL
  -- `∑ 1/(K j + 1) = ∞`
  have hKφ : ∀ j, 1 / (φ (N + 1 + j) + 1) ≤ 1 / ((K j : ℝ) + 1) := by
    intro j
    have h0 := hφ (N + 1 + j)
    have hc : 1 ≤ ⌈φ (N + 1 + j)⌉ := by
      have := Int.le_ceil (φ (N + 1 + j))
      have : (0 : ℝ) < ⌈φ (N + 1 + j)⌉ := lt_of_lt_of_le h0 this
      exact_mod_cast this
    have hK : ((K j : ℕ) : ℝ) + 1 = ⌈φ (N + 1 + j)⌉ := by
      have : ((K j : ℕ) : ℤ) = ⌈φ (N + 1 + j)⌉ - 1 := by
        simp only [K, hKseq]; exact Int.toNat_of_nonneg (by omega)
      have : (((K j : ℕ) : ℤ) : ℝ) = ((⌈φ (N + 1 + j)⌉ - 1 : ℤ) : ℝ) := by rw [this]
      push_cast at this; linarith
    rw [hK]
    exact one_div_le_one_div_of_le (by positivity) (Int.ceil_lt_add_one _).le
  have hnsum : ¬Summable fun j ↦ 1 / ((K j : ℝ) + 1) := by
    intro hs
    have h1 : Summable fun j ↦ 1 / (φ (N + 1 + j) + 1) :=
      Summable.of_nonneg_of_le (fun j ↦ by have := hφ (N + 1 + j); positivity) hKφ hs
    have h2 : Summable fun n ↦ 1 / (φ (n + (N + 1)) + 1) := by
      convert h1 using 2 with j
      rw [show j + (N + 1) = N + 1 + j by ring]
    exact not_summable_inv_add_one hφ hdiv ((summable_nat_add_iff (N + 1)).mp h2)
  have htop := (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun j ↦ by positivity)).mp hnsum
  have hlim : Tendsto (fun m : ℕ ↦ ENNReal.ofReal (Real.exp (-(∑ j ∈ Finset.range m,
      1 / ((K j : ℝ) + 1))) * L)) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero, show (0 : ℝ) = 0 * L by ring]
    exact ENNReal.tendsto_ofReal ((Real.tendsto_exp_neg_atTop_nhds_zero.comp htop).mul_const L)
  exact le_antisymm (ge_of_tendsto' hlim hle) (by simp)

/-- Cylinder sets with a lower bound at the last level: `cylL m B` is the set of irrational `α > 1`
whose quotient `a_m` (counting from `a₀ = ⌊α⌋`) is at least `B` (auxiliary). -/
private def cylL : ℕ → ℝ → Set ℝ
  | 0, B => {α | B ≤ α ∧ 1 < α ∧ Irrational α}
  | m + 1, B => {α | ∃ j : ℕ, (j + 1 : ℝ) < α ∧ α < j + 2 ∧ 1 / (α - (j + 1)) ∈ cylL m B}

private lemma hasSum_telescope (q q' : ℝ) (hq : 0 < q) (hq' : 0 ≤ q') :
    HasSum (fun j : ℕ ↦ 1 / (((j + 1) * q + q') * ((j + 2) * q + q'))) (1 / (q * (q + q'))) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun j ↦ by positivity)]
  simp_rw [telescope q q' hq hq']
  -- `N/((q + q')((N+1)q + q')) → 1/(q(q + q'))`
  have h : ∀ N : ℕ, (N : ℝ) / ((q + q') * ((N + 1) * q + q')) =
      1 / (q * (q + q')) - 1 / (q * ((N + 1) * q + q')) := by
    intro N
    have h1 : 0 < q + q' := by linarith
    have h2 : 0 < ((N : ℝ) + 1) * q + q' := by positivity
    field_simp; ring
  simp_rw [h]
  conv => rhs; rw [← sub_zero (1 / (q * (q + q')))]
  refine tendsto_const_nhds.sub ?_
  have : Tendsto (fun N : ℕ ↦ q * (((N : ℝ) + 1) * q + q')) atTop atTop := by
    refine Tendsto.const_mul_atTop hq (tendsto_atTop_add_const_right _ _ ?_)
    exact Tendsto.atTop_mul_const hq (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  exact (this.inv_tendsto_atTop).congr fun N ↦ by simp only [Pi.inv_apply, one_div]

/-- `vol (M '' cylL m B) ≤ (2/B) · 1/(q(q + q'))` when `0 ≤ q' ≤ q`, `q ≥ 1`. -/
private lemma volume_mob_cylL (B : ℝ) (hB : 0 < B) (m : ℕ) : ∀ (p p' q q' : ℤ), 1 ≤ q → 0 ≤ q' →
    q' ≤ q → (p * q' - p' * q = 1 ∨ p * q' - p' * q = -1) →
    volume (mob p p' q q' '' cylL m B) ≤ ENNReal.ofReal (2 / B * (1 / (q * (q + q')))) := by
  induction m with
  | zero =>
    intro p p' q q' hq hq' hqq hdet
    have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hq'r : (0 : ℝ) ≤ q' := by exact_mod_cast hq'
    have hqqr : (q' : ℝ) ≤ q := by exact_mod_cast hqq
    set t0 := max B 1 with ht0
    have ht01 : 1 ≤ t0 := le_max_right _ _
    have ht0B : B ≤ t0 := le_max_left _ _
    have e : ∀ s : ℝ, 0 < s * q + q' →
        mob p p' q q' s = p / q + ((p' * q - p * q' : ℤ) : ℝ) / (q * (s * q + q')) := by
      intro s hs; unfold mob; push_cast; field_simp; ring
    have hsub : mob p p' q q' '' cylL 0 B ⊆ uIcc ((p : ℝ) / q) (mob p p' q q' t0) := by
      rintro _ ⟨t, ⟨htB, ht1, -⟩, rfl⟩
      have htt0 : t0 ≤ t := max_le htB ht1.le
      have hden : 0 < t * q + q' := by nlinarith
      have hden0 : (0 : ℝ) < t0 * q + q' := by nlinarith
      rw [e t hden, e t0 hden0, Set.mem_uIcc]
      have hc : 1 / (q * (t * q + q')) ≤ 1 / (q * (t0 * q + q')) :=
        one_div_le_one_div_of_le (by positivity)
          (mul_le_mul_of_nonneg_left (by nlinarith) (by linarith))
      have hc0 : 0 < 1 / (q * (t * q + q')) := by positivity
      rcases hdet with h | h
      · rw [show p' * q - p * q' = -1 by linarith]; push_cast
        right
        constructor
        · rw [show (-1 : ℝ) / (q * (t0 * q + q')) = -(1 / (q * (t0 * q + q'))) by ring,
            show (-1 : ℝ) / (q * (t * q + q')) = -(1 / (q * (t * q + q'))) by ring]
          linarith
        · rw [show (-1 : ℝ) / (q * (t * q + q')) = -(1 / (q * (t * q + q'))) by ring]
          linarith
      · rw [show p' * q - p * q' = 1 by linarith]; push_cast
        left
        constructor <;> linarith
    have hden0 : (0 : ℝ) < t0 * q + q' := by nlinarith
    calc volume (mob p p' q q' '' cylL 0 B) ≤ volume (uIcc ((p : ℝ) / q) (mob p p' q q' t0)) :=
          measure_mono hsub
      _ = ENNReal.ofReal |mob p p' q q' t0 - p / q| := Real.volume_interval
      _ = ENNReal.ofReal (1 / (q * (t0 * q + q'))) := by
          congr 1
          rw [e t0 hden0, add_sub_cancel_left]
          rcases hdet with h | h
          · rw [show p' * q - p * q' = -1 by linarith]; push_cast
            rw [abs_div, abs_neg, abs_one, abs_of_pos (by positivity)]
          · rw [show p' * q - p * q' = 1 by linarith]; push_cast
            rw [abs_div, abs_one, abs_of_pos (by positivity)]
      _ ≤ ENNReal.ofReal (2 / B * (1 / (q * (q + q')))) := by
          apply ENNReal.ofReal_le_ofReal
          rw [div_mul_div_comm, mul_one]
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have h1 : B * q' ≤ B * q := mul_le_mul_of_nonneg_left hqqr hB.le
          have h2 : B * q ≤ t0 * q := mul_le_mul_of_nonneg_right ht0B (by linarith)
          nlinarith
  | succ m ih =>
    intro p p' q q' hq hq' hqq hdet
    have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hq'r : (0 : ℝ) ≤ q' := by exact_mod_cast hq'
    have hsub : mob p p' q q' '' cylL (m + 1) B ⊆ ⋃ j : ℕ,
        mob ((j + 1) * p + p') p ((j + 1) * q + q') q '' cylL m B := by
      rintro _ ⟨α, ⟨j, h1, h2, hβ⟩, rfl⟩
      refine mem_iUnion.mpr ⟨j, 1 / (α - (j + 1)), hβ, ?_⟩
      have hαj : 0 < α - (j + 1) := by linarith
      have hβ0 : 1 / (α - (j + 1)) ≠ 0 := by positivity
      rw [← mob_comp p p' q q' j hβ0, one_div_one_div]
      congr 1; ring
    have hK : ∀ j : ℕ, volume (mob ((j + 1) * p + p') p ((j + 1) * q + q') q '' cylL m B) ≤
        ENNReal.ofReal (2 / B * (1 / ((((j : ℝ) + 1) * q + q') * ((j + 2) * q + q')))) := by
      intro j
      have := ih ((j + 1) * p + p') p ((j + 1) * q + q') q (by nlinarith) (by omega) (by nlinarith)
        (by rcases hdet with h | h <;> [right; left] <;> linarith)
      convert this using 3
      push_cast; ring
    have hS := (hasSum_telescope (q : ℝ) q' (by linarith) hq'r).mul_left (2 / B)
    calc volume (mob p p' q q' '' cylL (m + 1) B)
        ≤ volume (⋃ j : ℕ, mob ((j + 1) * p + p') p ((j + 1) * q + q') q '' cylL m B) :=
          measure_mono hsub
      _ ≤ ∑' j : ℕ, volume (mob ((j + 1) * p + p') p ((j + 1) * q + q') q '' cylL m B) :=
          measure_iUnion_le _
      _ ≤ ∑' j : ℕ, ENNReal.ofReal (2 / B * (1 / ((((j : ℝ) + 1) * q + q') * ((j + 2) * q + q')))) :=
          ENNReal.tsum_le_tsum hK
      _ = ENNReal.ofReal (2 / B * (1 / (q * (q + q')))) := by
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun j ↦ by positivity) hS.summable, hS.tsum_eq]

/-- Complete quotients with a large quotient at depth `m` lie in `cylL m B`. -/
private lemma mem_cylL {a : ℕ → ℤ} (ha : ∀ i, 1 ≤ i → 0 < a i) (B : ℝ) (m : ℕ) :
    ∀ (i : ℕ) (y : ℝ), 1 ≤ i →
      Tendsto (fun t ↦ (cf (fun j ↦ ((a (i + j) : ℤ) : ℝ))).convs t) atTop (𝓝 y) →
      B ≤ a (i + m) → y ∈ cylL m B := by
  have hti : ∀ i, 1 ≤ i → ∀ j, 1 ≤ j → 0 < a (i + j) := fun i hi j _ ↦ ha (i + j) (by omega)
  induction m with
  | zero =>
    intro i y hi hy hB
    obtain ⟨h0, -⟩ := cf_value_mem_Ioo (hti i hi) hy
    have h : (1 : ℝ) ≤ a (i + 0) := by exact_mod_cast ha (i + 0) (by omega)
    exact ⟨by linarith, by linarith, (irrational_iff_exists_unique_cf y).2 _ (hti i hi) hy⟩
  | succ m ih =>
    intro i y hi hy hB
    obtain ⟨h0, h1⟩ := cf_value_mem_Ioo (hti i hi) hy
    simp only [add_zero] at h0 h1
    have hai : 1 ≤ a i := ha i hi
    have e1 : ((a i - 1).toNat : ℝ) + 1 = a i := by
      have : ((a i - 1).toNat : ℤ) = a i - 1 := Int.toNat_of_nonneg (by omega)
      have : (((a i - 1).toNat : ℤ) : ℝ) = a i - 1 := by exact_mod_cast this
      push_cast at this ⊢; linarith
    refine ⟨(a i - 1).toNat, by linarith, by linarith, ?_⟩
    rw [e1]
    have ht := cf_tendsto_tail (hti i hi) hy
    simp only [add_zero] at ht
    have e : (fun j ↦ ((a (i + (j + 1)) : ℤ) : ℝ)) = fun j ↦ ((a (i + 1 + j) : ℤ) : ℝ) := by
      funext j; rw [show i + (j + 1) = i + 1 + j by ring]
    rw [e] at ht
    exact ih (i + 1) _ (by omega) ht (by rwa [show i + 1 + m = i + (m + 1) by ring])

/-- **Theorem 197*** (second half, Borel and Bernstein). If `∑ 1/φ(n)` is convergent (`φ(n) > 0`), then
`aₙ < φ(n)` for all sufficiently large `n`, for almost all `ξ`: the set of `ξ` whose continued fraction
has `aₙ ≥ φ(n)` for infinitely many `n` is null. -/
@[kb "hardywright2008" "Thm 197*, p. 215"]
theorem volume_frequently_ge_eq_zero {φ : ℕ → ℝ} (hφ : ∀ n, 0 < φ n)
    (hsum : Summable fun n ↦ 1 / φ n) :
    volume {ξ : ℝ | ∃ a : ℕ → ℤ, (∀ i, 1 ≤ i → 0 < a i) ∧
      Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 ξ) ∧
      ∃ᶠ n in atTop, φ n ≤ a n} = 0 := by
  have hcover : {ξ : ℝ | ∃ a : ℕ → ℤ, (∀ i, 1 ≤ i → 0 < a i) ∧
      Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 ξ) ∧
      ∃ᶠ n in atTop, φ n ≤ a n} ⊆
      ⋃ a₀ : ℤ, limsup (fun n : ℕ ↦ mob a₀ 1 1 0 '' cylL n (φ (n + 1))) atTop := by
    rintro ξ ⟨a, ha, hx, hfreq⟩
    refine mem_iUnion.mpr ⟨a 0, ?_⟩
    rw [Filter.mem_limsup_iff_frequently_mem]
    have hfreq' : ∃ᶠ n in atTop, φ (n + 1) ≤ a (n + 1) := by
      rw [Nat.frequently_atTop_iff_infinite] at hfreq ⊢
      have : {n | φ (n + 1) ≤ a (n + 1)} = (fun n ↦ n + 1) ⁻¹' {n | φ n ≤ a n} := rfl
      rw [this]
      refine Set.infinite_of_forall_exists_gt fun k ↦ ?_
      obtain ⟨n, hn, hkn⟩ := hfreq.exists_gt (k + 1)
      exact ⟨n - 1, by simp only [Set.mem_preimage]; rwa [show n - 1 + 1 = n by omega], by omega⟩
    refine hfreq'.mono fun n hn ↦ ?_
    have ht := cf_tendsto_tail ha hx
    refine ⟨1 / (ξ - a 0), mem_cylL ha (φ (n + 1)) n 1 _ le_rfl (by simpa [add_comm] using ht)
      (by rw [add_comm 1 n]; exact hn), ?_⟩
    have hx0 := (cf_value_mem_Ioo ha hx).1
    unfold mob
    push_cast
    field_simp
    ring
  refine measure_mono_null hcover (measure_iUnion_null fun a₀ ↦ measure_limsup_atTop_eq_zero ?_)
  have hb : ∀ n : ℕ, volume (mob a₀ 1 1 0 '' cylL n (φ (n + 1))) ≤
      ENNReal.ofReal (2 * (1 / φ (n + 1))) := by
    intro n
    have := volume_mob_cylL (φ (n + 1)) (hφ (n + 1)) n a₀ 1 1 0 le_rfl le_rfl (by norm_num)
      (Or.inr (by ring))
    refine this.trans (le_of_eq ?_)
    congr 1; push_cast; ring
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hb)
  rw [← ENNReal.ofReal_tsum_of_nonneg (f := fun n : ℕ ↦ 2 * (1 / φ (n + 1)))
    (fun n ↦ by have := hφ (n + 1); positivity)
    (((summable_nat_add_iff 1).mpr hsum).mul_left 2)]
  exact ENNReal.ofReal_ne_top

end NTKB.HardyWright
