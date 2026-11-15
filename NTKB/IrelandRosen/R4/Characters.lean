/-
Ireland–Rosen, Chapter 16, §§16.3–16.5: the character group of a finite abelian group, the residue
of L(s, χ₀) at s = 1, and Lemmas 1–3 of §16.5 (Abel summation, partial sums of a nontrivial
character, Euler products of bounded multiplicative functions).
-/
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import NTKB.Attr

/-!
# Characters and L-functions (Ireland–Rosen, Chapter 16)

* §16.3: the character group `Â` of a finite abelian group `A` is isomorphic to `A`
  (`nonempty_monoidHom_units_mulEquiv`), in particular `|Â| = |A|`.
* §16.4: `(s - 1) L(s, χ₀) → φ(m)/m` as `s → 1` (`tendsto_sub_one_mul_LFunction_one`).
* §16.5, Lemma 1 (Abel summation): `∑ a_n b_n = ∑ A_n (b_n - b_{n+1})` when `A_n b_{n+1} → 0`
  (`tendsto_sum_mul_of_abel`).
* §16.5, Lemma 2: for a nontrivial character `χ` mod `m`, `|∑_{n<N} χ(n)| ≤ φ(m)`
  (`norm_sum_range_le_totient`).
* §16.5, Lemma 3: for a nonnegative multiplicative `f` with `f(p^k) ≤ c`, `∑ f(n) n^(-s)` converges
  for `s > 1` and equals its Euler product (`summable_and_hasProd_eulerProduct`).
-/

namespace NTKB.IrelandRosen

open Filter Topology Finset

/-- **Ireland–Rosen, §16.3.** The character group of a finite abelian group `A` (homomorphisms to
`ℂˣ`) is isomorphic to `A`. -/
@[kb "irelandrosen1990" "§16.3, character group of a finite abelian group"]
theorem nonempty_monoidHom_units_mulEquiv (A : Type*) [CommGroup A] [Finite A] :
    Nonempty ((A →* ℂˣ) ≃* A) :=
  CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity A ℂ

/-- **Ireland–Rosen, §16.4.** `(s - 1) L(s, χ₀) → φ(m)/m` as `s → 1`, for the trivial character
`χ₀` mod `m`. -/
@[kb "irelandrosen1990" "§16.4, (s - 1) L(s, χ₀) → φ(m)/m"]
theorem tendsto_sub_one_mul_LFunction_one {m : ℕ} [NeZero m] :
    Tendsto (fun s : ℂ ↦ (s - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ m) s)
      (𝓝[≠] 1) (𝓝 ((m.totient : ℂ) / m)) := by
  have h := (DirichletCharacter.LFunctionTrivChar_residue_one (N := m))
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hq := congrArg (fun q : ℚ ↦ (q : ℂ)) (Nat.totient_eq_mul_prod_factors m)
  simp only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_prod, Rat.cast_sub, Rat.cast_one,
    Rat.cast_inv] at hq
  have : ((m.totient : ℂ) / m) = ∏ p ∈ m.primeFactors, (1 - (p : ℂ)⁻¹) := by
    rw [hq]; field_simp
  rw [this]
  exact h

/-- **Ireland–Rosen, §16.5, Lemma 1 (Abel summation).** Let `A_n = a_0 + ⋯ + a_n`. If
`∑ A_n (b_n - b_{n+1})` converges to `S` and `A_n b_{n+1} → 0`, then `∑ a_n b_n` converges to `S`. -/
@[kb "irelandrosen1990" "§16.5, Lemma 1"]
theorem tendsto_sum_mul_of_abel (a b : ℕ → ℂ) {S : ℂ}
    (hS : Tendsto (fun N ↦ ∑ n ∈ range N, (∑ k ∈ range (n + 1), a k) * (b n - b (n + 1)))
      atTop (𝓝 S))
    (hb : Tendsto (fun n ↦ (∑ k ∈ range (n + 1), a k) * b (n + 1)) atTop (𝓝 0)) :
    Tendsto (fun N ↦ ∑ n ∈ range N, a n * b n) atTop (𝓝 S) := by
  have key : ∀ N : ℕ, ∑ n ∈ range (N + 1), a n * b n =
      (∑ k ∈ range (N + 1), a k) * b (N + 1) +
        ∑ n ∈ range (N + 1), (∑ k ∈ range (n + 1), a k) * (b n - b (n + 1)) := by
    intro N
    induction N with
    | zero => simp; ring
    | succ N ih =>
      rw [Finset.sum_range_succ _ (N + 1), ih, Finset.sum_range_succ (fun k ↦ a k) (N + 1),
        Finset.sum_range_succ (fun n ↦ (∑ k ∈ range (n + 1), a k) * (b n - b (n + 1))) (N + 1)]
      rw [Finset.sum_range_succ (fun k ↦ a k) (N + 1)]
      ring
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  have h2 := (hb.add ((Filter.tendsto_add_atTop_iff_nat 1).2 hS))
  rw [zero_add] at h2
  refine h2.congr fun N ↦ ?_
  exact (key N).symm

/-- **Ireland–Rosen, §16.5, Lemma 2.** For a nontrivial Dirichlet character `χ` modulo `m`,
`|∑_{n < N} χ(n)| ≤ φ(m)` for every `N`. -/
@[kb "irelandrosen1990" "§16.5, Lemma 2"]
theorem norm_sum_range_le_totient {m : ℕ} [NeZero m] {χ : DirichletCharacter ℂ m} (hχ : χ ≠ 1)
    (N : ℕ) : ‖∑ n ∈ range N, χ n‖ ≤ m.totient := by
  have hfull : ∑ n ∈ range m, χ (n : ZMod m) = 0 := by
    rw [← MulChar.sum_eq_zero_of_ne_one hχ]
    refine Finset.sum_nbij (fun n : ℕ ↦ (n : ZMod m)) (by simp) ?_ ?_ (fun _ _ ↦ rfl)
    · intro a ha b hb h
      simp only [Finset.coe_range, Set.mem_Iio] at ha hb
      have := (ZMod.natCast_eq_natCast_iff' a b m).1 h
      rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
    · intro x _
      exact ⟨x.val, by simp [ZMod.val_lt], by simp⟩
  have hper : ∀ q : ℕ, ∑ n ∈ range (q * m), χ (n : ZMod m) = 0 := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih, zero_add, ← hfull]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      push_cast
      simp
  have hN : N = N / m * m + N % m := by
    rw [mul_comm]; exact (Nat.div_add_mod N m).symm
  have hr : N % m < m := Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne m))
  set r := N % m
  have hsum : ∑ n ∈ range N, χ (n : ZMod m) = ∑ x ∈ range r, χ (x : ZMod m) := by
    conv_lhs => rw [hN, Finset.sum_range_add, hper, zero_add]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    push_cast
    simp
  rw [hsum]
  calc ‖∑ x ∈ range r, χ (x : ZMod m)‖ ≤ ∑ x ∈ range r, ‖χ (x : ZMod m)‖ := norm_sum_le _ _
    _ ≤ ∑ x ∈ range r, (if m.Coprime x then (1 : ℝ) else 0) := by
        refine Finset.sum_le_sum fun x _ ↦ ?_
        split_ifs with h
        · exact DirichletCharacter.norm_le_one _ _
        · have : ¬ IsUnit (x : ZMod m) := by rwa [ZMod.isUnit_iff_coprime, Nat.coprime_comm]
          rw [MulChar.map_nonunit _ this]; simp
    _ = ((range r).filter (m.Coprime)).card := by simp
    _ ≤ ((range m).filter (m.Coprime)).card := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _
          (Finset.range_subset_range.2 hr.le))
    _ = m.totient := rfl

private lemma pow_rpow_neg' (p k : ℕ) (s : ℝ) :
    (((p ^ k : ℕ) : ℝ)) ^ (-s) = ((p : ℝ) ^ (-s)) ^ k := by
  rw [Nat.cast_pow]
  exact (Real.rpow_pow_comm (Nat.cast_nonneg p) (-s) k).symm

private lemma prime_tsum_le {f : ℕ → ℝ} (hf0 : ∀ n, 0 ≤ f n) (hf1 : f 1 = 1) {C : ℝ}
    (hC1 : 1 ≤ C) (hC : ∀ p k : ℕ, p.Prime → 1 ≤ k → f (p ^ k) ≤ C) {s : ℝ} (hs : 1 < s)
    {p : ℕ} (hp : p.Prime) :
    Summable (fun k : ℕ ↦ f (p ^ k) * (((p ^ k : ℕ) : ℝ)) ^ (-s)) ∧
      ∑' k : ℕ, f (p ^ k) * (((p ^ k : ℕ) : ℝ)) ^ (-s) ≤ 1 + 2 * C * (p : ℝ) ^ (-s) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  set q : ℝ := (p : ℝ) ^ (-s) with hqdef
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by linarith) _
  have hq : q ≤ 1 / 2 := by
    rw [hqdef, Real.rpow_neg (by linarith)]
    have h1 : (p : ℝ) ^ (1 : ℝ) ≤ (p : ℝ) ^ s :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hs.le
    rw [Real.rpow_one] at h1
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    linarith
  have hle : ∀ k : ℕ, f (p ^ k) * (((p ^ k : ℕ) : ℝ)) ^ (-s) ≤ C * q ^ k := by
    intro k
    rw [pow_rpow_neg']
    rcases k with _ | k
    · simp [hf1, hC1]
    · exact mul_le_mul_of_nonneg_right (hC p (k + 1) hp (by omega)) (pow_nonneg hq0.le _)
  have hgeo : Summable (fun k : ℕ ↦ q ^ k) := summable_geometric_of_lt_one hq0.le (by linarith)
  have hsum : Summable (fun k : ℕ ↦ f (p ^ k) * (((p ^ k : ℕ) : ℝ)) ^ (-s)) :=
    Summable.of_nonneg_of_le (fun k ↦ mul_nonneg (hf0 _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      hle (hgeo.mul_left C)
  refine ⟨hsum, ?_⟩
  rw [hsum.tsum_eq_zero_add]
  have h2 : ∑' k : ℕ, f (p ^ (k + 1)) * (((p ^ (k + 1) : ℕ) : ℝ)) ^ (-s) ≤
      ∑' k : ℕ, (C * q) * q ^ k := by
    refine Summable.tsum_le_tsum (fun k ↦ ?_) ((summable_nat_add_iff 1).2 hsum)
      (hgeo.mul_left _)
    calc _ ≤ C * q ^ (k + 1) := hle (k + 1)
      _ = _ := by ring
  rw [tsum_mul_left, tsum_geometric_of_lt_one hq0.le (by linarith)] at h2
  have h3 : (1 - q)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have h4 : C * q * (1 - q)⁻¹ ≤ C * q * 2 :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  simp only [pow_zero, Nat.cast_one, Real.one_rpow, mul_one, hf1]
  linarith

/-- **Ireland–Rosen, §16.5, Lemma 3.** Let `f` be a nonnegative multiplicative function with
`f(p^k) ≤ c` for all primes `p` and `k ≥ 1`. Then for real `s > 1`, `∑ f(n) n^(-s)` converges and
equals `∏_p ∑_{k ≥ 0} f(p^k) p^(-ks)`. -/
@[kb "irelandrosen1990" "§16.5, Lemma 3"]
theorem summable_and_hasProd_eulerProduct {f : ℕ → ℝ} (hf : ArithmeticFunction.IsMultiplicative
      (⟨fun n ↦ if n = 0 then 0 else f n, by simp⟩ : ArithmeticFunction ℝ))
    (hf0 : ∀ n, 0 ≤ f n) {c : ℝ} (hc : ∀ p k : ℕ, p.Prime → 1 ≤ k → f (p ^ k) ≤ c)
    {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ ↦ f n * (n : ℝ) ^ (-s)) ∧
      HasProd (fun p : Nat.Primes ↦ ∑' k : ℕ, f ((p : ℕ) ^ k) * ((p : ℕ) ^ k : ℝ) ^ (-s))
        (∑' n : ℕ, f n * (n : ℝ) ^ (-s)) := by
  set C := max c 1 with hCdef
  have hC1 : 1 ≤ C := le_max_right _ _
  have hC : ∀ p k : ℕ, p.Prime → 1 ≤ k → f (p ^ k) ≤ C :=
    fun p k hp hk ↦ (hc p k hp hk).trans (le_max_left _ _)
  have hf1 : f 1 = 1 := by simpa using hf.map_one
  set g : ℕ → ℝ := fun n ↦ f n * (n : ℝ) ^ (-s) with hg
  have hs0 : -s ≠ 0 := neg_ne_zero.2 (by linarith)
  have hg0 : g 0 = 0 := by simp [hg, Real.zero_rpow hs0]
  have hgnn : ∀ n, 0 ≤ g n := fun n ↦
    mul_nonneg (hf0 n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hg1 : g 1 = 1 := by simp [hg, hf1]
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n → g (m * n) = g m * g n := by
    intro m n h
    by_cases hm : m = 0
    · subst hm
      have : n = 1 := by simpa using h
      subst this
      simp [hg0, hg1]
    by_cases hn : n = 0
    · subst hn
      have : m = 1 := by simpa using h
      subst this
      simp [hg0, hg1]
    have h1 := hf.map_mul_of_coprime h
    simp only [ArithmeticFunction.coe_mk, mul_ne_zero hm hn, hm, hn, ite_false] at h1
    show f (m * n) * ((m * n : ℕ) : ℝ) ^ (-s) = (f m * (m : ℝ) ^ (-s)) * (f n * (n : ℝ) ^ (-s))
    rw [h1, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    ring
  have hpr : ∀ {p : ℕ}, p.Prime → Summable (fun k : ℕ ↦ ‖g (p ^ k)‖) := by
    intro p hp
    have := (prime_tsum_le hf0 hf1 hC1 hC hs hp).1
    refine this.congr fun k ↦ ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hgnn _)]
  have hZ : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hbound : ∀ N : ℕ, ∏ p ∈ N.primesBelow, ∑' k : ℕ, g (p ^ k) ≤
      Real.exp (2 * C * ∑' n : ℕ, (n : ℝ) ^ (-s)) := by
    intro N
    have hT : ∀ p ∈ N.primesBelow, ∑' k : ℕ, g (p ^ k) ≤ Real.exp (2 * C * (p : ℝ) ^ (-s)) := by
      intro p hp
      have := (prime_tsum_le hf0 hf1 hC1 hC hs (Nat.prime_of_mem_primesBelow hp)).2
      have h2 := Real.add_one_le_exp (2 * C * (p : ℝ) ^ (-s))
      show ∑' k : ℕ, f (p ^ k) * (((p ^ k : ℕ) : ℝ)) ^ (-s) ≤ _
      linarith
    calc ∏ p ∈ N.primesBelow, ∑' k : ℕ, g (p ^ k)
        ≤ ∏ p ∈ N.primesBelow, Real.exp (2 * C * (p : ℝ) ^ (-s)) :=
          Finset.prod_le_prod₀ (fun p _ ↦ tsum_nonneg fun k ↦ hgnn _) hT
      _ = Real.exp (∑ p ∈ N.primesBelow, 2 * C * (p : ℝ) ^ (-s)) := (Real.exp_sum _ _).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.2
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        calc ∑ p ∈ N.primesBelow, (p : ℝ) ^ (-s)
            ≤ ∑ n ∈ range N, (n : ℝ) ^ (-s) :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                (fun n _ _ ↦ Real.rpow_nonneg (Nat.cast_nonneg n) _)
          _ ≤ _ := hZ.sum_le_tsum _ (fun n _ ↦ Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hsumm : Summable g := by
    refine summable_of_sum_le (c := Real.exp (2 * C * ∑' n : ℕ, (n : ℝ) ^ (-s))) hgnn
      fun F ↦ ?_
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ∈ F, n < N :=
      ⟨F.sup id + 1, fun n hn ↦ Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)⟩
    have h := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum hg1 hmul
      (fun hp ↦ hpr hp) N
    classical
    calc ∑ n ∈ F, g n = ∑ n ∈ F with n ≠ 0, g n :=
          (Finset.sum_filter_of_ne (fun x _ hx ↦ by rintro rfl; exact hx hg0)).symm
      _ = ∑ x ∈ (F.filter (· ≠ 0)).subtype (· ∈ N.smoothNumbers), g x :=
          (Finset.sum_subtype_of_mem g (fun n hn ↦ by
            rw [Finset.mem_filter] at hn
            exact Nat.mem_smoothNumbers_of_lt (Nat.pos_of_ne_zero hn.2) (hN n hn.1))).symm
      _ ≤ ∏ p ∈ N.primesBelow, ∑' k : ℕ, g (p ^ k) :=
          sum_le_hasSum _ (fun _ _ ↦ hgnn _) h.2
      _ ≤ _ := hbound N
  refine ⟨hsumm, ?_⟩
  have hnorm : Summable (fun n ↦ ‖g n‖) := by
    simpa [Real.norm_eq_abs] using hsumm.abs
  have := EulerProduct.eulerProduct_hasProd hg1 hmul hnorm hg0
  have e : (fun p : Nat.Primes ↦ ∑' k : ℕ, f ((p : ℕ) ^ k) * (((p : ℕ) : ℝ) ^ k) ^ (-s)) =
      fun p : Nat.Primes ↦ ∑' k : ℕ, g ((p : ℕ) ^ k) := by
    funext p
    simp only [hg, Nat.cast_pow]
  rw [e]
  exact this

end NTKB.IrelandRosen
