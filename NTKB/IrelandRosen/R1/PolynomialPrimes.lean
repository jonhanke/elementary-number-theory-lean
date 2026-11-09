/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.PSeries
import NTKB.IrelandRosen.R1.FiniteFields

/-!
# Ireland–Rosen, Chapter 2: monic irreducible polynomials as the primes of `k[x]`

* Infinitely many monic irreducibles in `k[x]` (Chapter 2, Section 1, p. 28, left there as
  Exercise 1 for finite `k`): Euclid's argument, which works for every field `k`.
* **Theorem 4** (p. 33): for a finite field `k` with `q` elements, `∑ q^(-deg p)` over the monic
  irreducibles `p` diverges.

The book proves Theorem 4 by "an exact imitation" of its proof that `∑ 1/p` diverges (the
details are left to the reader). We give a counting proof instead: by Corollary 1 to Theorem 2
of Chapter 7, `q^n = ∑_{d ∣ n} d N_d`, so `N_n q^(-n) ≥ 1/n - q^(⌊n/2⌋+1-n)`, and the series
`∑ 1/n` diverges while `∑ q^(⌊n/2⌋+1-n)` converges.
-/

open Polynomial

namespace NTKB.IrelandRosen

/-- **Ireland–Rosen, Chapter 2, Section 1 (and Exercise 1).** `k[x]` has infinitely many monic
irreducible polynomials, for every field `k`: if `p_1, …, p_l` were all of them, a monic
irreducible factor of `p_1 ⋯ p_l + 1` would be one of the `p_i` and divide `1`. -/
@[kb "irelandrosen1990" "Ch 2, Section 1, infinitely many monic irreducibles in k[x], p. 28"]
theorem infinite_setOf_monic_irreducible (k : Type*) [Field k] :
    {f : k[X] | f.Monic ∧ Irreducible f}.Infinite := by
  classical
  intro hfin
  set s := hfin.toFinset with hs
  have hmem : ∀ f, f ∈ s ↔ f.Monic ∧ Irreducible f := fun f ↦ by
    rw [hs, Set.Finite.mem_toFinset]; rfl
  have hX : X ∈ s := (hmem X).mpr ⟨monic_X, irreducible_X⟩
  set P := ∏ f ∈ s, f
  have hPmonic : P.Monic := monic_prod_of_monic _ _ fun f hf ↦ ((hmem f).mp hf).1
  have hPdeg : 1 ≤ P.natDegree := by
    rw [natDegree_prod_of_monic _ _ fun f hf ↦ ((hmem f).mp hf).1]
    calc 1 = X.natDegree := natDegree_X.symm
      _ ≤ ∑ f ∈ s, f.natDegree := Finset.single_le_sum (f := fun f : k[X] ↦ f.natDegree)
          (fun _ _ ↦ Nat.zero_le _) hX
  have hQmonic : (P + 1).Monic := hPmonic.add_of_left (by
    rw [degree_one, degree_eq_natDegree hPmonic.ne_zero]
    exact_mod_cast (by omega : 0 < P.natDegree))
  have hQdeg : 1 ≤ (P + 1).natDegree := by
    rw [natDegree_add_eq_left_of_natDegree_lt (by rw [natDegree_one]; omega)]; exact hPdeg
  have hQunit : ¬ IsUnit (P + 1) := fun hu ↦ by
    have := natDegree_eq_zero_of_isUnit hu; omega
  obtain ⟨g, hg, hgdvd⟩ := WfDvdMonoid.exists_irreducible_factor hQunit hQmonic.ne_zero
  -- the monic associate of `g`
  set g' := g * C g.leadingCoeff⁻¹
  have hg'monic : g'.Monic := monic_mul_leadingCoeff_inv hg.ne_zero
  have hg'irr : Irreducible g' :=
    (irreducible_mul_isUnit (isUnit_C.mpr
      (inv_ne_zero (leadingCoeff_ne_zero.mpr hg.ne_zero)).isUnit)).mpr hg
  have hg'dvd : g' ∣ P + 1 := (Dvd.intro (C g.leadingCoeff) (by
    rw [mul_assoc, ← C_mul, inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr hg.ne_zero), C_1,
      mul_one])).trans hgdvd
  have hg'P : g' ∣ P := Finset.dvd_prod_of_mem _ ((hmem g').mpr ⟨hg'monic, hg'irr⟩)
  have : g' ∣ 1 := (dvd_add_right hg'P).mp hg'dvd
  exact hg'irr.not_isUnit (isUnit_of_dvd_one this)

section Theorem4

variable (k : Type*) [Field k] [Finite k]

/-- The lower bound behind Theorem 4: `n N_n ≥ q^n - q^(⌊n/2⌋+1)`, from `q^n = ∑_{d ∣ n} d N_d`
(Chapter 7, Corollary 1 to Theorem 2) and `d N_d ≤ q^d`. -/
theorem card_pow_le_mul_numMonicIrreducibles_add {n : ℕ} (hn : n ≠ 0) :
    Nat.card k ^ n ≤ n * numMonicIrreducibles k n + Nat.card k ^ (n / 2 + 1) := by
  have hq : 2 ≤ Nat.card k := Finite.one_lt_card
  rw [card_pow_eq_sum_divisors k hn, ← Finset.add_sum_erase _ _ (Nat.mem_divisors_self n hn)]
  gcongr
  calc ∑ d ∈ n.divisors.erase n, d * numMonicIrreducibles k d
      ≤ ∑ d ∈ n.divisors.erase n, Nat.card k ^ d := by
        refine Finset.sum_le_sum fun d hd ↦ ?_
        have hd0 : d ≠ 0 := fun h ↦ by
          subst h; simp at hd
        rw [card_pow_eq_sum_divisors k hd0]
        exact Finset.single_le_sum (f := fun e ↦ e * numMonicIrreducibles k e)
          (fun _ _ ↦ Nat.zero_le _) (Nat.mem_divisors_self d hd0)
    _ ≤ ∑ d ∈ Finset.range (n / 2 + 1), Nat.card k ^ d := by
        refine Finset.sum_le_sum_of_subset fun d hd ↦ ?_
        obtain ⟨hne, hd⟩ := Finset.mem_erase.mp hd
        obtain ⟨⟨c, hc⟩, -⟩ := Nat.mem_divisors.mp hd
        rw [Finset.mem_range, Nat.lt_succ_iff, Nat.le_div_iff_mul_le (by norm_num)]
        rcases c with _ | _ | c
        · omega
        · simp at hc; omega
        · rw [hc]; nlinarith
    _ ≤ Nat.card k ^ (n / 2 + 1) := (Nat.geomSum_lt hq fun _ h ↦ Finset.mem_range.mp h).le

/-- **Ireland–Rosen, Chapter 2, Theorem 4.** For a finite field `k` with `q` elements,
`∑ q^(-deg p)` over the monic irreducible polynomials `p` of `k[x]` diverges. -/
@[kb "irelandrosen1990" "Ch 2, Theorem 4, p. 33"]
theorem not_summable_card_pow_natDegree_inv :
    ¬ Summable (fun f : {f : k[X] // f.Monic ∧ Irreducible f} ↦
      ((Nat.card k : ℝ) ^ f.1.natDegree)⁻¹) := by
  classical
  intro hsum
  set q := Nat.card k
  have hq : 2 ≤ q := Finite.one_lt_card
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  set g := fun f : {f : k[X] // f.Monic ∧ Irreducible f} ↦ ((q : ℝ) ^ f.1.natDegree)⁻¹
  have hg0 : ∀ f, 0 ≤ g f := fun f ↦ by positivity
  -- `a n = N_n q^(-n)`
  set a : ℕ → ℝ := fun n ↦ numMonicIrreducibles k n * ((q : ℝ) ^ n)⁻¹
  have ha0 : ∀ n, 0 ≤ a n := fun n ↦ by positivity
  -- partial sums of `a` are partial sums of `g`
  have hpartial : ∀ D, ∑ n ∈ Finset.range D, a n ≤ ∑' f, g f := by
    intro D
    set T := (Finset.range D).biUnion (monicIrreducibles k)
    have hT : ∀ f ∈ T, f.Monic ∧ Irreducible f := fun f hf ↦ by
      obtain ⟨d, -, hf⟩ := Finset.mem_biUnion.mp hf
      exact ⟨(mem_monicIrreducibles.mp hf).1, (mem_monicIrreducibles.mp hf).2.1⟩
    calc ∑ n ∈ Finset.range D, a n
        = ∑ f ∈ T, ((q : ℝ) ^ f.natDegree)⁻¹ := by
          rw [Finset.sum_biUnion]
          · refine Finset.sum_congr rfl fun d _ ↦ ?_
            rw [Finset.sum_congr rfl fun f hf ↦ by rw [(mem_monicIrreducibles.mp hf).2.2],
              Finset.sum_const, nsmul_eq_mul]
            rfl
          · intro d _ e _ hde
            simp only [Function.onFun]
            rw [Finset.disjoint_left]
            intro f hf hf'
            exact hde ((mem_monicIrreducibles.mp hf).2.2.symm.trans
              (mem_monicIrreducibles.mp hf').2.2)
      _ = ∑ f ∈ T.subtype (fun f ↦ f.Monic ∧ Irreducible f), g f := by
          symm
          exact (Finset.sum_subtype_eq_sum_filter (fun f : k[X] ↦ ((q : ℝ) ^ f.natDegree)⁻¹)).trans
            (by rw [Finset.filter_true_of_mem hT])
      _ ≤ ∑' f, g f := hsum.sum_le_tsum _ fun f _ ↦ hg0 f
  have hasum : Summable a := summable_of_sum_range_le ha0 hpartial
  -- the comparison series `q * r^n`, `r = 1/√2`
  set r : ℝ := (Real.sqrt 2)⁻¹
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ (by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num))
  have hbsum : Summable fun n : ℕ ↦ (q : ℝ) * r ^ n :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  -- `1/n ≤ a n + q r^n`
  have hle : ∀ n : ℕ, 1 / (n : ℝ) ≤ a n + q * r ^ n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.cast_zero, div_zero]; positivity
    have hcount := card_pow_le_mul_numMonicIrreducibles_add k hn.ne'
    have hcountR : (q : ℝ) ^ n ≤ n * numMonicIrreducibles k n + (q : ℝ) ^ (n / 2 + 1) := by
      exact_mod_cast hcount
    have hqn : (0 : ℝ) < (q : ℝ) ^ n := by positivity
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    -- `q^(n/2+1) / q^n ≤ q r^n`
    have hratio : (q : ℝ) ^ (n / 2 + 1) * ((q : ℝ) ^ n)⁻¹ ≤ q * r ^ n := by
      have hsplit : (q : ℝ) ^ n = (q : ℝ) ^ (n / 2) * (q : ℝ) ^ (n - n / 2) := by
        rw [← pow_add]; congr 1; omega
      rw [hsplit, pow_succ, mul_inv, ← mul_assoc, mul_comm ((q : ℝ) ^ (n / 2)) (q : ℝ),
        mul_assoc, mul_assoc, ← mul_assoc ((q : ℝ) ^ (n / 2)),
        mul_inv_cancel₀ (by positivity), one_mul]
      gcongr
      -- `q^(-(n - n/2)) ≤ 2^(-(n - n/2)) = r^(2 (n - n/2)) ≤ r^n`
      calc ((q : ℝ) ^ (n - n / 2))⁻¹ ≤ ((2 : ℝ) ^ (n - n / 2))⁻¹ := by gcongr
        _ = r ^ (2 * (n - n / 2)) := by
          rw [pow_mul, inv_pow, ← inv_pow]
          congr 1
          rw [Real.sq_sqrt (by norm_num)]
        _ ≤ r ^ n := pow_le_pow_of_le_one hr0 hr1.le (by omega)
    calc 1 / (n : ℝ) = ((q : ℝ) ^ n * ((q : ℝ) ^ n)⁻¹) / n := by
          rw [mul_inv_cancel₀ hqn.ne']
      _ ≤ ((n * numMonicIrreducibles k n + (q : ℝ) ^ (n / 2 + 1)) * ((q : ℝ) ^ n)⁻¹) / n := by
          gcongr
      _ = a n + (q : ℝ) ^ (n / 2 + 1) * ((q : ℝ) ^ n)⁻¹ / n := by
          simp only [a]; field_simp
      _ ≤ a n + (q : ℝ) ^ (n / 2 + 1) * ((q : ℝ) ^ n)⁻¹ := by
          gcongr
          exact div_le_self (by positivity) hnR
      _ ≤ a n + q * r ^ n := by gcongr
  exact Real.not_summable_one_div_natCast
    (Summable.of_nonneg_of_le (fun n ↦ by positivity) hle (hasum.add hbsum))

end Theorem4

end NTKB.IrelandRosen
