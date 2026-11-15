/-
Ireland–Rosen, Chapter 16, §§16.1–16.4: Dirichlet density, the logarithm of ζ(s) and of L(s, χ),
and Dirichlet's theorem in the density form.
-/
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import NTKB.Attr

/-!
# Dirichlet density (Ireland–Rosen, Chapter 16)

Ireland and Rosen define the Dirichlet density of a set `S` of primes as
`lim_{s → 1+} (∑_{p ∈ S} p^(-s)) / ln (1/(s - 1))` when the limit exists (§16.1). We define it for
a set `S` of natural numbers, summing over the primes in `S` (`HasDirichletDensity`). (Mathlib's
`NumberField.Set.HasDirichletDensity` is the analogue for prime ideals of a number field with the
ratio to the sum over all primes; the two agree over `ℚ` by Proposition 16.1.3.)

* Proposition 16.1.3: `ln ζ(s) = ∑_p p^(-s) + R(s)` with `R` bounded (`log_riemannZeta_sub_primeSum_bounded`).
* Proposition 16.1.4: finite sets have density `0`, sets containing all but finitely many primes
  have density `1`, densities add on disjoint unions.
* Proposition 16.4.1: with `G(s, χ) = ∑_p ∑_k χ(p)^k/(k p^(ks))` (the Dirichlet series
  `∑ χ(n) Λ(n)/(n^s ln n)`, Mathlib's `DirichletCharacter.eulerProduct_log_eq_LSeries`),
  `G(s, χ₀)/ln(1/(s-1)) → 1` and `G(s, χ)` is bounded as `s → 1+` for `χ ≠ χ₀`.
* §16.1, Theorem 1 (Dirichlet): for `(a, m) = 1` the primes `p ≡ a (mod m)` have Dirichlet density
  `1/φ(m)` (`hasDirichletDensity_modEq`).
* Proposition 16.2.1: the primes `≡ 1` and `≡ 3 (mod 4)` each have density `1/2`.
-/

namespace NTKB.IrelandRosen

open Filter Topology ArithmeticFunction

/-- `∑_{p ∈ S, p prime} p^(-s)`. -/
noncomputable def primeSum (S : Set ℕ) (s : ℝ) : ℝ :=
  ∑' p : {p : ℕ // p.Prime ∧ p ∈ S}, ((p : ℕ) : ℝ) ^ (-s)

/-- **Ireland–Rosen, §16.1.** The set of primes in `S` has Dirichlet density `δ`:
`(∑_{p ∈ S} p^(-s)) / ln (1/(s - 1)) → δ` as `s → 1+`. -/
def HasDirichletDensity (S : Set ℕ) (δ : ℝ) : Prop :=
  Tendsto (fun s : ℝ ↦ primeSum S s / Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 δ)

section Aux

open LSeries
open scoped Classical

lemma primeSum_eq (S : Set ℕ) (s : ℝ) :
    primeSum S s = ∑' n : ℕ, if n.Prime ∧ n ∈ S then (n : ℝ) ^ (-s) else 0 := by
  unfold primeSum
  refine (tsum_subtype {p : ℕ | p.Prime ∧ p ∈ S} (fun n : ℕ => (n : ℝ) ^ (-s))).trans ?_
  congr 1
  ext n
  simp [Set.indicator]

lemma summable_primeTerm (S : Set ℕ) {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => if n.Prime ∧ n ∈ S then (n : ℝ) ^ (-s) else 0) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (Real.summable_nat_rpow.2 (by linarith : -s < -1))
  · split_ifs
    · positivity
    · exact le_rfl
  · split_ifs
    · exact le_rfl
    · positivity

lemma primeSum_add {U S T : Set ℕ} (h : ∀ n, n.Prime → (n ∈ U ↔ n ∈ S ∨ n ∈ T))
    (hd : ∀ n, n.Prime → n ∈ S → n ∈ T → False) {s : ℝ} (hs : 1 < s) :
    primeSum U s = primeSum S s + primeSum T s := by
  rw [primeSum_eq, primeSum_eq, primeSum_eq,
    ← (summable_primeTerm S hs).tsum_add (summable_primeTerm T hs)]
  congr 1
  ext n
  by_cases hn : n.Prime
  · by_cases h1 : n ∈ S <;> by_cases h2 : n ∈ T
    · exact (hd n hn h1 h2).elim
    · simp [hn, h1, h2, (h n hn).2 (Or.inl h1)]
    · simp [hn, h1, h2, (h n hn).2 (Or.inr h2)]
    · have : n ∉ U := fun hu => by rcases (h n hn).1 hu with h | h <;> contradiction
      simp [hn, h1, h2, this]
  · simp [hn]

lemma primeSum_nonneg (S : Set ℕ) {s : ℝ} (_hs : 1 < s) : 0 ≤ primeSum S s := by
  rw [primeSum_eq]
  refine tsum_nonneg fun n => ?_
  split_ifs
  · positivity
  · exact le_rfl

lemma primeSum_le_of_finite {S : Set ℕ} (hS : S.Finite) {s : ℝ} (hs : 1 < s) :
    primeSum S s ≤ hS.toFinset.card := by
  rw [primeSum_eq, tsum_eq_sum (s := hS.toFinset)]
  · calc _ ≤ ∑ _n ∈ hS.toFinset, (1 : ℝ) := by
          refine Finset.sum_le_sum fun n _ => ?_
          split_ifs with h
          · exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast h.1.one_lt.le)
              (by linarith)
          · exact zero_le_one
      _ = _ := by simp
  · intro n hn
    have : n ∉ S := by simpa using hn
    simp [this]

lemma tendsto_log_inv :
    Tendsto (fun s : ℝ => Real.log (1 / (s - 1))) (𝓝[>] 1) atTop := by
  have h1 : Tendsto (fun s : ℝ => s - 1) (𝓝[>] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun s : ℝ => s - 1) (𝓝 1) (𝓝 (1 - 1)) := tendsto_id.sub_const 1
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs using sub_pos.2 (Set.mem_Ioi.1 hs)
  have h2 := tendsto_inv_nhdsGT_zero.comp h1
  exact Real.tendsto_log_atTop.comp (by simpa [Function.comp_def, one_div] using h2)

lemma hasDirichletDensity_of_bound {S : Set ℕ} {c C : ℝ}
    (h : ∀ x ∈ Set.Ioc (1 : ℝ) 2, |primeSum S x - c * Real.log (1 / (x - 1))| ≤ C) :
    HasDirichletDensity S c := by
  have hL := tendsto_log_inv
  have h0 : Tendsto (fun s : ℝ => (primeSum S s - c * Real.log (1 / (s - 1))) /
      Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun x => C / Real.log (1 / (x - 1))) ?_
      ((tendsto_const_nhds (x := C)).div_atTop hL)
    filter_upwards [Ioc_mem_nhdsGT (by norm_num : (1 : ℝ) < 2), hL.eventually_gt_atTop 0]
      with x hx hLx
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hLx]
    exact div_le_div_of_nonneg_right (h x hx) hLx.le
  unfold HasDirichletDensity
  have h1 := h0.add_const c
  rw [zero_add] at h1
  refine h1.congr' ?_
  filter_upwards [hL.eventually_gt_atTop 0] with x hx
  field_simp
  ring

lemma bdd_of_deriv (f : ℕ → ℂ) (c : ℝ) (R : ℂ → ℂ)
    (hf : ∀ n, n ≤ 1 → f n = 0)
    (hab : abscissaOfAbsConv f ≤ 1)
    (hR : ContinuousOn R {s | 1 ≤ s.re})
    (hL : ∀ x : ℝ, 1 < x → LSeries f x = R x + (c : ℂ) / ((x : ℂ) - 1)) :
    ∃ C : ℝ, ∀ x ∈ Set.Ioc (1 : ℝ) 2,
      ‖LSeries (fun n => f n / (Real.log n : ℂ)) x + c * Real.log (x - 1)‖ ≤ C := by
  set g : ℕ → ℂ := fun n => f n / (Real.log n : ℂ) with hg
  have hlog : logMul g = f := by
    funext n
    simp only [logMul, hg]
    by_cases hn : n ≤ 1
    · rw [hf n hn]; simp
    · have : (Real.log n : ℂ) ≠ 0 := by
        have : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
        exact_mod_cast this.ne'
      rw [← Complex.natCast_log]
      field_simp
  have hab' : abscissaOfAbsConv g ≤ 1 := by
    have h1 : abscissaOfAbsConv (logMul g) = abscissaOfAbsConv g := abscissaOfAbsConv_logMul
    rw [← h1, hlog]; exact hab
  have hd : ∀ x : ℝ, 1 < x → HasDerivAt
      (fun t : ℝ => LSeries g (t : ℂ) + (c : ℂ) * ((Real.log (t - 1) : ℝ) : ℂ)) (-R x) x := by
    intro x hx
    have h1 : abscissaOfAbsConv g < ((x : ℂ)).re := by
      rw [Complex.ofReal_re]
      exact lt_of_le_of_lt hab' (by exact_mod_cast hx)
    have h2 := (LSeries_hasDerivAt h1).comp_ofReal
    rw [hlog] at h2
    have h3 : HasDerivAt (fun t : ℝ => Real.log (t - 1)) (1 / (x - 1)) x := by
      have := ((hasDerivAt_id x).sub_const 1).log (by simp; linarith)
      simpa using this
    have h4 := (h3.ofReal_comp).const_mul (c : ℂ)
    convert h2.add h4 using 1
    rw [hL x hx]; push_cast; ring
  have hcont : ContinuousOn (fun t : ℝ => R t) (Set.Icc 1 2) :=
    hR.comp Complex.continuous_ofReal.continuousOn (fun t ht => by simpa using ht.1)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1 ⟨le_rfl, by norm_num⟩)
  set h := (fun t : ℝ => LSeries g (t : ℂ) + (c : ℂ) * ((Real.log (t - 1) : ℝ) : ℂ)) with hh
  refine ⟨‖h 2‖ + M, fun x hx => ?_⟩
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := h) (f' := fun t => -R t)
    (s := Set.Ioc (1 : ℝ) 2) (C := M)
    (fun t ht => (hd t ht.1).hasDerivWithinAt)
    (fun t ht => by simpa using hM t ⟨ht.1.le, ht.2⟩) (convex_Ioc _ _)
    (show (2 : ℝ) ∈ Set.Ioc (1 : ℝ) 2 from ⟨by norm_num, le_rfl⟩) hx
  have hx2 : ‖x - 2‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hx.1, hx.2]
  calc ‖h x‖ = ‖(h x - h 2) + h 2‖ := by rw [sub_add_cancel]
    _ ≤ ‖h x - h 2‖ + ‖h 2‖ := norm_add_le _ _
    _ ≤ M * 1 + ‖h 2‖ := by gcongr; exact key.trans (by gcongr)
    _ = ‖h 2‖ + M := by ring

lemma LSeries_real (g : ℕ → ℝ) (x : ℝ) (hx : 0 < x) :
    LSeries (fun n => (g n : ℂ) / (Real.log n : ℂ)) (x : ℂ) =
      ((∑' n : ℕ, g n / ((n : ℝ) ^ x * Real.log n) : ℝ) : ℂ) := by
  rw [LSeries, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [term_zero, Real.zero_rpow hx.ne']
  · rw [term_of_ne_zero hn, ← Complex.ofReal_natCast n, ← Complex.ofReal_cpow n.cast_nonneg]
    push_cast
    ring

lemma primes_diff (S : Set ℕ) (g : ℕ → ℝ) (hg0 : ∀ n, 0 ≤ g n) (hgΛ : ∀ n, g n ≤ Λ n)
    (hgp : ∀ p, p.Prime → (p ∈ S → g p = Real.log p) ∧ (p ∉ S → g p = 0))
    (hsum : Summable fun n : ℕ => (if n.Prime then 0 else g n) / n) :
    ∃ B : ℝ, ∀ x : ℝ, 1 < x →
      Summable (fun n : ℕ => g n / ((n : ℝ) ^ x * Real.log n)) ∧
      0 ≤ ∑' n : ℕ, g n / ((n : ℝ) ^ x * Real.log n) - primeSum S x ∧
      ∑' n : ℕ, g n / ((n : ℝ) ^ x * Real.log n) - primeSum S x ≤ B := by
  refine ⟨∑' n : ℕ, 2 * ((if n.Prime then 0 else g n) / n), fun x hx => ?_⟩
  set u : ℕ → ℝ := fun n => if n.Prime ∧ n ∈ S then (n : ℝ) ^ (-x) else 0 with hu
  set v : ℕ → ℝ := fun n => g n / ((n : ℝ) ^ x * Real.log n) with hv
  set b : ℕ → ℝ := fun n => 2 * ((if n.Prime then 0 else g n) / n) with hb
  have hw : ∀ n, 0 ≤ v n - u n ∧ v n - u n ≤ b n := by
    intro n
    by_cases hp : n.Prime
    · have h2 : 0 < Real.log n := Real.log_pos (by exact_mod_cast hp.one_lt)
      have h3 : (0 : ℝ) < (n : ℝ) ^ x := Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) x
      have : v n = u n := by
        by_cases hS : n ∈ S
        · simp only [hv, hu, (hgp n hp).1 hS, hp, hS, true_and, ite_true,
            Real.rpow_neg (Nat.cast_nonneg n)]
          field_simp
        · simp [hv, hu, (hgp n hp).2 hS, hp, hS]
      have hb0 : 0 ≤ b n := by simp [hb, hp]
      rw [this, sub_self]
      exact ⟨le_rfl, hb0⟩
    · have hu0 : u n = 0 := by simp [hu, hp]
      have hv0 : 0 ≤ v n := div_nonneg (hg0 n)
        (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) x) (Real.log_natCast_nonneg n))
      rw [hu0, sub_zero]
      refine ⟨hv0, ?_⟩
      by_cases hg : g n = 0
      · simp [hv, hb, hg]
      · have hgpos : 0 < g n := lt_of_le_of_ne (hg0 n) (Ne.symm hg)
        have hn2 : 2 ≤ n := by
          by_contra hlt
          push Not at hlt
          have := hgΛ n
          interval_cases n <;> simp at this <;> linarith
        have hn : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
        have hnpos : (0 : ℝ) < n := by linarith
        have h1 : (n : ℝ) ≤ (n : ℝ) ^ x := Real.self_le_rpow_of_one_le hn hx.le
        have h2 : (1 / 2 : ℝ) ≤ Real.log n := by
          have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hn2 : (2 : ℝ) ≤ n)
          have := Real.log_two_gt_d9
          linarith
        have h4 : (n : ℝ) * (1 / 2) ≤ (n : ℝ) ^ x * Real.log n :=
          mul_le_mul h1 h2 (by norm_num) (by positivity)
        calc v n = g n / ((n : ℝ) ^ x * Real.log n) := rfl
          _ ≤ g n / ((n : ℝ) * (1 / 2)) := div_le_div_of_nonneg_left hgpos.le (by positivity) h4
          _ = b n := by simp only [hb, hp]; simp; field_simp
  have hbs : Summable b := hsum.mul_left 2
  have hws : Summable (fun n => v n - u n) :=
    Summable.of_nonneg_of_le (fun n => (hw n).1) (fun n => (hw n).2) hbs
  have hus := summable_primeTerm S hx
  have hvs : Summable v := (hws.add hus).congr fun n => sub_add_cancel (v n) (u n)
  refine ⟨hvs, ?_, ?_⟩
  · rw [primeSum_eq, ← hvs.tsum_sub hus]
    exact tsum_nonneg fun n => (hw n).1
  · rw [primeSum_eq, ← hvs.tsum_sub hus]
    exact hws.tsum_le_tsum (fun n => (hw n).2) hbs

lemma norm_real_aux (g : ℕ → ℝ) (x c C : ℝ) (hx : 0 < x)
    (h : ‖LSeries (fun n => (g n : ℂ) / (Real.log n : ℂ)) (x : ℂ) + (c : ℂ) * ((Real.log (x - 1) : ℝ) : ℂ)‖ ≤ C) :
    |∑' n : ℕ, g n / ((n : ℝ) ^ x * Real.log n) + c * Real.log (x - 1)| ≤ C := by
  rw [LSeries_real g x hx, ← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.norm_real,
    Real.norm_eq_abs] at h
  exact h

lemma density_modEq_aux {m : ℕ} (hm : 0 < m) {a : ℕ} (ha : a.Coprime m) :
    HasDirichletDensity {p : ℕ | p ≡ a [MOD m]} (1 / (m.totient : ℝ)) := by
  have : NeZero m := ⟨hm.ne'⟩
  set ā : ZMod m := (a : ZMod m) with hā_def
  have hā : IsUnit ā := (ZMod.isUnit_iff_coprime a m).2 ha
  set S : Set ℕ := {p : ℕ | p ≡ a [MOD m]} with hS_def
  have hS : ∀ n : ℕ, n ∈ S ↔ (n : ZMod m) = ā := fun n =>
    (ZMod.natCast_eq_natCast_iff n a m).symm
  set g : ℕ → ℝ := vonMangoldt.residueClass ā with hg_def
  have hgp : ∀ p, p.Prime → (p ∈ S → g p = Real.log p) ∧ (p ∉ S → g p = 0) := by
    intro p hp
    constructor
    · intro h
      simp [hg_def, (hS p).1 h, vonMangoldt_apply_prime hp]
    · intro h
      have h' : ¬ ((p : ZMod m) = ā) := fun h' => h ((hS p).2 h')
      simp [hg_def, h']
  obtain ⟨B, hB⟩ := primes_diff S g (vonMangoldt.residueClass_nonneg ā)
    (vonMangoldt.residueClass_le ā) hgp (vonMangoldt.summable_residueClass_non_primes_div ā)
  obtain ⟨C, hC⟩ := bdd_of_deriv (fun n => (g n : ℂ)) (1 / (m.totient : ℝ))
    (vonMangoldt.LFunctionResidueClassAux ā)
    (fun n hn => by
      interval_cases n <;> simp [hg_def, vonMangoldt.residueClass])
    (vonMangoldt.abscissaOfAbsConv_residueClass_le_one ā)
    (vonMangoldt.continuousOn_LFunctionResidueClassAux ā)
    (fun x hx => by
      have := vonMangoldt.eqOn_LFunctionResidueClassAux hā
        (show (x : ℂ) ∈ {s : ℂ | 1 < s.re} by simpa using hx)
      simp only at this
      rw [this]
      push_cast
      ring)
  refine hasDirichletDensity_of_bound (C := B + C) fun x hx => ?_
  have hx1 : 1 < x := hx.1
  obtain ⟨hs, h0, h1⟩ := hB x hx1
  have hE := norm_real_aux g x _ C (by linarith) (hC x hx)
  have hl : Real.log (1 / (x - 1)) = -Real.log (x - 1) := by rw [one_div, Real.log_inv]
  rw [hl]
  rw [abs_le] at hE ⊢
  constructor <;> nlinarith [hE.1, hE.2]

end Aux

/-- **Ireland–Rosen, Proposition 16.1.3.** For real `s > 1`, `ln ζ(s) = ∑_p p^(-s) + R(s)` with
`R(s)` bounded (here for all `s > 1`). -/
@[kb "irelandrosen1990" "Proposition 16.1.3"]
theorem log_riemannZeta_sub_primeSum_bounded :
    ∃ C : ℝ, ∀ s : ℝ, 1 < s →
      |Real.log (riemannZeta (s : ℂ)).re - primeSum Set.univ s| ≤ C := by
  have hres : vonMangoldt.residueClass (0 : ZMod 1) = fun n => Λ n := by
    funext n
    simp [vonMangoldt.residueClass, Set.indicator, Subsingleton.elim ((n : ZMod 1)) 0]
  have hsum : Summable fun n : ℕ => (if n.Prime then 0 else Λ n) / n := by
    have := vonMangoldt.summable_residueClass_non_primes_div (0 : ZMod 1)
    rw [hres] at this
    exact this
  obtain ⟨B, hB⟩ := primes_diff Set.univ (fun n => Λ n) (fun n => vonMangoldt_nonneg)
    (fun n => le_rfl)
    (fun p hp => ⟨fun _ => vonMangoldt_apply_prime hp, fun h => (h trivial).elim⟩) hsum
  refine ⟨B, fun s hs => ?_⟩
  obtain ⟨_, h0, h1⟩ := hB s hs
  rw [log_riemannZeta_eq hs, abs_le]
  constructor <;> linarith

/-- **Ireland–Rosen, Proposition 16.1.4 (a).** A finite set of primes has Dirichlet density `0`. -/
@[kb "irelandrosen1990" "Proposition 16.1.4"]
theorem hasDirichletDensity_of_finite {S : Set ℕ} (hS : S.Finite) : HasDirichletDensity S 0 := by
  have hL := tendsto_log_inv
  have h0 : Tendsto (fun s : ℝ => (hS.toFinset.card : ℝ) / Real.log (1 / (s - 1))) (𝓝[>] 1)
      (𝓝 0) := tendsto_const_nhds.div_atTop hL
  refine squeeze_zero' ?_ ?_ h0
  · filter_upwards [self_mem_nhdsWithin, hL.eventually_gt_atTop 0] with s hs hLs
    exact div_nonneg (primeSum_nonneg S (Set.mem_Ioi.1 hs)) hLs.le
  · filter_upwards [self_mem_nhdsWithin, hL.eventually_gt_atTop 0] with s hs hLs
    exact div_le_div_of_nonneg_right (primeSum_le_of_finite hS (Set.mem_Ioi.1 hs)) hLs.le

/-- **Ireland–Rosen, Proposition 16.1.4 (b).** A set containing all but finitely many primes has
Dirichlet density `1`. -/
@[kb "irelandrosen1990" "Proposition 16.1.4"]
theorem hasDirichletDensity_of_finite_compl {S : Set ℕ} (hS : {p : ℕ | p.Prime ∧ p ∉ S}.Finite) :
    HasDirichletDensity S 1 := by
  have hT := hasDirichletDensity_of_finite hS
  have hU : HasDirichletDensity Set.univ 1 := by
    have h := density_modEq_aux (m := 1) one_pos (a := 0) (Nat.coprime_one_right 0)
    have e : {p : ℕ | p ≡ 0 [MOD 1]} = Set.univ := by ext p; simp [Nat.modEq_one]
    rw [e] at h
    simpa using h
  unfold HasDirichletDensity at hT hU ⊢
  have h2 := hU.sub hT
  rw [sub_zero] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have := primeSum_add (U := Set.univ) (S := S) (T := {p : ℕ | p.Prime ∧ p ∉ S})
    (fun n hn => by by_cases h : n ∈ S <;> simp [h, hn]) (fun n _ h1 h2 => h2.2 h1)
    (Set.mem_Ioi.1 hs)
  rw [← sub_div]
  congr 1
  linarith

/-- **Ireland–Rosen, Proposition 16.1.4 (c).** Dirichlet densities add on disjoint unions. -/
@[kb "irelandrosen1990" "Proposition 16.1.4"]
theorem HasDirichletDensity.union {S T : Set ℕ} {δ ε : ℝ} (hST : Disjoint S T)
    (hS : HasDirichletDensity S δ) (hT : HasDirichletDensity T ε) :
    HasDirichletDensity (S ∪ T) (δ + ε) := by
  unfold HasDirichletDensity at *
  refine (hS.add hT).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [primeSum_add (U := S ∪ T) (S := S) (T := T) (fun n _ => Iff.rfl)
    (fun n _ h1 h2 => Set.disjoint_left.1 hST h1 h2) (Set.mem_Ioi.1 hs), add_div]

/-- `G(s, χ) = ∑_p ∑_{k ≥ 1} χ(p)^k / (k p^(ks))`, written as the Dirichlet series
`∑_n χ(n) Λ(n) / (n^s ln n)` (Ireland–Rosen, §16.4; Mathlib's
`DirichletCharacter.eulerProduct_log_eq_LSeries` identifies the two). -/
noncomputable def logLFunction {m : ℕ} (χ : DirichletCharacter ℂ m) (s : ℂ) : ℂ :=
  LSeries (fun n : ℕ ↦ χ n * Λ n / Real.log n) s

open DirichletCharacter in
lemma trivChar_aux {m : ℕ} [NeZero m] {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ m) n * (Λ n : ℂ)) s =
      -deriv (LFunctionTrivChar₁ m) s / LFunctionTrivChar₁ m s + 1 / (s - 1) := by
  have hs₁ : s ≠ 1 := fun h => ((h ▸ hs).trans_eq Complex.one_re).false
  have h1 : LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ m) n * (Λ n : ℂ)) s =
      -deriv (LFunction (1 : DirichletCharacter ℂ m)) s / LFunction (1 : DirichletCharacter ℂ m) s := by
    rw [LFunction_eq_LSeries _ hs, deriv_LFunction_eq_deriv_LSeries _ hs]
    exact LSeries_twist_vonMangoldt_eq _ hs
  rw [h1, deriv_LFunctionTrivChar₁_apply_of_ne_one _ hs₁, LFunctionTrivChar₁,
    Function.update_of_ne hs₁]
  have hne : LFunction (1 : DirichletCharacter ℂ m) s ≠ 0 :=
    LFunction_ne_zero_of_one_le_re 1 (.inr hs₁) hs.le
  have hne2 : s - 1 ≠ 0 := sub_ne_zero_of_ne hs₁
  change -deriv (LFunction (1 : DirichletCharacter ℂ m)) s / LFunction (1 : DirichletCharacter ℂ m) s =
    -((s - 1) * deriv (LFunction (1 : DirichletCharacter ℂ m)) s +
      LFunction (1 : DirichletCharacter ℂ m) s) /
    ((s - 1) * LFunction (1 : DirichletCharacter ℂ m) s) + 1 / (s - 1)
  field_simp
  ring

/-- **Ireland–Rosen, Proposition 16.4.1 (first part).** `G(s, χ₀) / ln (1/(s - 1)) → 1` as
`s → 1+`. -/
@[kb "irelandrosen1990" "Proposition 16.4.1"]
theorem tendsto_logLFunction_one_div_log {m : ℕ} [NeZero m] :
    Tendsto (fun s : ℝ ↦ logLFunction (1 : DirichletCharacter ℂ m) s / Real.log (1 / (s - 1)))
      (𝓝[>] 1) (𝓝 1) := by
  obtain ⟨C, hC⟩ := bdd_of_deriv (fun n : ℕ => (1 : DirichletCharacter ℂ m) n * (Λ n : ℂ)) 1
    (fun s => -deriv (DirichletCharacter.LFunctionTrivChar₁ m) s /
      DirichletCharacter.LFunctionTrivChar₁ m s)
    (fun n hn => by interval_cases n <;> simp)
    (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => by
      have := DirichletCharacter.LSeriesSummable_twist_vonMangoldt
        (1 : DirichletCharacter ℂ m) (s := (y : ℂ)) (by simpa using hy)
      exact this)
    ((DirichletCharacter.continuousOn_neg_logDeriv_LFunctionTrivChar₁ m).mono fun s hs => by
      rcases eq_or_ne s 1 with h | h
      · exact Or.inl h
      · exact Or.inr (DirichletCharacter.LFunction_ne_zero_of_one_le_re 1 (.inr h) hs))
    (fun x hx => by
      have := trivChar_aux (m := m) (s := (x : ℂ)) (by simpa using hx)
      push_cast
      rw [one_div] at this
      rw [this, one_div])
  have hL := tendsto_log_inv
  have h0 : Tendsto (fun s : ℝ => logLFunction (1 : DirichletCharacter ℂ m) s /
      (Real.log (1 / (s - 1)) : ℂ) - 1) (𝓝[>] 1) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun x => C / Real.log (1 / (x - 1))) ?_
      ((tendsto_const_nhds (x := C)).div_atTop hL)
    filter_upwards [Ioc_mem_nhdsGT (by norm_num : (1 : ℝ) < 2), hL.eventually_gt_atTop 0]
      with x hx hLx
    have hLc : (Real.log (1 / (x - 1)) : ℂ) ≠ 0 := by exact_mod_cast hLx.ne'
    have hl : Real.log (1 / (x - 1)) = -Real.log (x - 1) := by rw [one_div, Real.log_inv]
    have e : logLFunction (1 : DirichletCharacter ℂ m) x / (Real.log (1 / (x - 1)) : ℂ) - 1 =
        (LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ m) n * (Λ n : ℂ) /
          (Real.log n : ℂ)) (x : ℂ) + ((1 : ℝ) : ℂ) * ((Real.log (x - 1) : ℝ) : ℂ)) /
          (Real.log (1 / (x - 1)) : ℂ) := by
      have hLℓ : (Real.log (1 / (x - 1)) : ℂ) = -((Real.log (x - 1) : ℝ) : ℂ) := by
        rw [hl]; push_cast; ring
      have alg : ∀ G ℓ : ℂ, -ℓ ≠ 0 → G / (-ℓ) - 1 = (G + ((1 : ℝ) : ℂ) * ℓ) / (-ℓ) := by
        intro G ℓ h
        rw [div_sub_one h]
        congr 1
        rw [Complex.ofReal_one]; ring
      unfold logLFunction
      rw [hLℓ] at hLc ⊢
      exact alg _ _ hLc
    rw [e, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hLx]
    exact div_le_div_of_nonneg_right (hC x hx) hLx.le
  simpa using h0.add_const 1

/-- **Ireland–Rosen, Proposition 16.4.1 (second part).** For `χ ≠ χ₀`, `G(s, χ)` stays bounded as
`s → 1+`. -/
@[kb "irelandrosen1990" "Proposition 16.4.1"]
theorem logLFunction_bounded {m : ℕ} [NeZero m] {χ : DirichletCharacter ℂ m} (hχ : χ ≠ 1) :
    ∃ C : ℝ, ∀ s : ℝ, s ∈ Set.Ioc 1 2 → ‖logLFunction χ s‖ ≤ C := by
  obtain ⟨C, hC⟩ := bdd_of_deriv (fun n : ℕ => χ n * (Λ n : ℂ)) 0
    (fun s => -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s)
    (fun n hn => by interval_cases n <;> simp)
    (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => by
      have := DirichletCharacter.LSeriesSummable_twist_vonMangoldt
        χ (s := (y : ℂ)) (by simpa using hy)
      exact this)
    ((DirichletCharacter.continuousOn_neg_logDeriv_LFunction_of_nontriv hχ).mono fun s hs =>
      DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) hs)
    (fun x hx => by
      have hx' : 1 < (x : ℂ).re := by simpa using hx
      have := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hx'
      rw [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hx',
        DirichletCharacter.LFunction_eq_LSeries χ hx']
      simp only [Complex.ofReal_zero, zero_div, add_zero]
      exact this)
  refine ⟨C, fun s hs => ?_⟩
  have := hC s hs
  simpa [logLFunction] using this

/-- **Ireland–Rosen, §16.1, Theorem 1 (Dirichlet).** For `m ≥ 1` and `a` prime to `m`, the primes
`p ≡ a (mod m)` have Dirichlet density `1/φ(m)`. -/
@[kb "irelandrosen1990" "§16.1, Theorem 1 (Dirichlet)"]
theorem hasDirichletDensity_modEq {m : ℕ} (hm : 0 < m) {a : ℕ} (ha : a.Coprime m) :
    HasDirichletDensity {p : ℕ | p ≡ a [MOD m]} (1 / (m.totient : ℝ)) :=
  density_modEq_aux hm ha

/-- **Ireland–Rosen, Proposition 16.2.1.** The primes `≡ 1 (mod 4)` and the primes `≡ 3 (mod 4)`
each have Dirichlet density `1/2`. -/
@[kb "irelandrosen1990" "Proposition 16.2.1"]
theorem hasDirichletDensity_mod_four :
    HasDirichletDensity {p : ℕ | p % 4 = 1} (1 / 2) ∧
      HasDirichletDensity {p : ℕ | p % 4 = 3} (1 / 2) := by
  have ht : (Nat.totient 4 : ℝ) = 2 := by
    have : Nat.totient 4 = 2 := by decide
    rw [this]; norm_num
  have h1 := hasDirichletDensity_modEq (m := 4) (by norm_num) (a := 1) (by norm_num)
  have h3 := hasDirichletDensity_modEq (m := 4) (by norm_num) (a := 3) (by norm_num)
  rw [ht] at h1 h3
  exact ⟨h1, h3⟩

end NTKB.IrelandRosen
