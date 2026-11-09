/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.ArithmeticFunctions.Inversion
import NTKB.Attr
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Init.Data.Nat.Sqrt.Lemmas
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Hardy–Wright, Chapter XVIII: average orders

* Theorems 318, 319, 320 (Dirichlet): `d(1) + ⋯ + d(n) = n log n + (2γ - 1) n + O(√n)`, hence
  `∑ d(k) ~ n log n ~ ∑ log k`. Proof (book, § 18.2): count the lattice points under the hyperbola
  `xy = n`, using its symmetry (Fig. 8): `∑_{k ≤ n} d(k) = 2 ∑_{a ≤ u} [n/a] - u²`, `u = [√n]`.
* Theorem 324: `σ(1) + ⋯ + σ(n) = π² n²/12 + O(n log n)`.
* Theorem 330 (Mertens): `Φ(n) = φ(1) + ⋯ + φ(n) = 3n²/π² + O(n log n)`.
* Theorem 332: the probability that two integers are coprime is `6/π²`.
-/

open Finset Filter Topology Asymptotics Real
open scoped ArithmeticFunction.sigma ArithmeticFunction.Moebius

namespace NTKB.HardyWright


lemma filter_mul_le_eq_Ioc (N a : ℕ) (ha : 0 < a) :
    (Ioc 0 N).filter (fun b => a * b ≤ N) = Ioc 0 (N / a) := by
  ext b
  simp only [mem_filter, mem_Ioc]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩
    exact ⟨h1, (Nat.le_div_iff_mul_le ha).mpr (by rwa [mul_comm])⟩
  · rintro ⟨h1, h2⟩
    have h3 := (Nat.le_div_iff_mul_le ha).mp h2
    refine ⟨⟨h1, h2.trans (Nat.div_le_self N a)⟩, by rwa [mul_comm]⟩

/-- The lattice points `(a, b)`, `a, b ≥ 1`, `ab ≤ N`. -/
def hyperbolaPoints (N : ℕ) : Finset (ℕ × ℕ) :=
  (Ioc 0 N ×ˢ Ioc 0 N).filter fun x => x.1 * x.2 ≤ N

lemma card_hyperbolaPoints_filter_fst (N u : ℕ) (hu : u ≤ N) :
    #((hyperbolaPoints N).filter fun x => x.1 ≤ u) = ∑ a ∈ Ioc 0 u, N / a := by
  rw [hyperbolaPoints, filter_filter, card_filter, sum_product]
  have hsplit : Ioc 0 N = Ioc 0 u ∪ Ioc u N := (Ioc_union_Ioc_eq_Ioc (Nat.zero_le u) hu).symm
  rw [hsplit, sum_union (Ioc_disjoint_Ioc_of_le le_rfl)]
  have h2 : ∑ a ∈ Ioc u N, ∑ b ∈ Ioc 0 u ∪ Ioc u N,
      (if a * b ≤ N ∧ a ≤ u then 1 else 0) = 0 := by
    refine sum_eq_zero fun a ha => sum_eq_zero fun b _ => ?_
    simp only [mem_Ioc] at ha
    exact ite_eq_right_of_eq_false _ _ (eq_false (by omega))
  rw [h2, add_zero, ← hsplit]
  refine sum_congr rfl fun a ha => ?_
  simp only [mem_Ioc] at ha
  simp only [ha.2, and_true]
  rw [← card_filter, filter_mul_le_eq_Ioc N a ha.1, Nat.card_Ioc, Nat.sub_zero]

lemma card_hyperbolaPoints (N : ℕ) : #(hyperbolaPoints N) = ∑ a ∈ Ioc 0 N, N / a := by
  rw [← card_hyperbolaPoints_filter_fst N N le_rfl]
  congr 1
  rw [filter_true_of_mem]
  intro x hx
  simp only [hyperbolaPoints, mem_filter, mem_product, mem_Ioc] at hx
  exact hx.1.1.2

/-- The hyperbola identity (Hardy–Wright § 18.2, Fig. 8): with `u = [√N]`,
`∑_{a ≤ N} [N/a] = 2 ∑_{a ≤ u} [N/a] - u²`. -/
lemma sum_div_add_sqrt_sq (N : ℕ) :
    ∑ a ∈ Ioc 0 N, N / a + Nat.sqrt N ^ 2 = 2 * ∑ a ∈ Ioc 0 (Nat.sqrt N), N / a := by
  set u := Nat.sqrt N with hu
  have huN : u ≤ N := Nat.sqrt_le_self N
  set T := hyperbolaPoints N
  set A := T.filter fun x => x.1 ≤ u
  set B := T.filter fun x => x.2 ≤ u
  have hA := card_hyperbolaPoints_filter_fst N u huN
  have hB : #B = #A := by
    refine card_bij (fun x _ => x.swap) ?_ ?_ ?_
    · intro x hx
      simp only [B, A, T, hyperbolaPoints, mem_filter, mem_product, Prod.fst_swap,
        Prod.snd_swap] at hx ⊢
      exact ⟨⟨⟨hx.1.1.2, hx.1.1.1⟩, by rw [mul_comm]; exact hx.1.2⟩, hx.2⟩
    · intro x _ y _ h; exact Prod.swap_injective h
    · intro y hy
      refine ⟨y.swap, ?_, by simp⟩
      simp only [B, A, T, hyperbolaPoints, mem_filter, mem_product, Prod.fst_swap,
        Prod.snd_swap] at hy ⊢
      exact ⟨⟨⟨hy.1.1.2, hy.1.1.1⟩, by rw [mul_comm]; exact hy.1.2⟩, hy.2⟩
  have hunion : A ∪ B = T := by
    ext x
    simp only [A, B, mem_union, mem_filter, ← and_or_left, and_iff_left_iff_imp]
    intro hx
    simp only [T, hyperbolaPoints, mem_filter] at hx
    by_contra h
    push Not at h
    have h1 : (u + 1) * (u + 1) ≤ x.1 * x.2 := Nat.mul_le_mul h.1 h.2
    have h2 := Nat.lt_succ_sqrt N
    rw [← hu, Nat.succ_eq_add_one] at h2
    have h3 := hx.2
    omega
  have hinter : A ∩ B = Ioc 0 u ×ˢ Ioc 0 u := by
    ext x
    simp only [A, B, T, hyperbolaPoints, mem_inter, mem_filter, mem_product, mem_Ioc]
    constructor
    · intro h
      exact ⟨⟨h.1.1.1.1.1, h.1.2⟩, h.1.1.1.2.1, h.2.2⟩
    · rintro ⟨⟨h1, h5⟩, h3, h6⟩
      have h7 : x.1 * x.2 ≤ u * u := Nat.mul_le_mul h5 h6
      have h8 := Nat.sqrt_le N
      rw [← hu] at h8
      exact ⟨⟨⟨⟨⟨h1, by omega⟩, h3, by omega⟩, by omega⟩, h5⟩,
        ⟨⟨⟨h1, by omega⟩, h3, by omega⟩, by omega⟩, h6⟩
  have := card_union_add_card_inter A B
  rw [hunion, hinter, card_product, Nat.card_Ioc, hB, hA, card_hyperbolaPoints] at this
  simp only [Nat.sub_zero] at this
  rw [sq, two_mul]
  omega

/-- `N/a - 1 < [N/a] ≤ N/a`. -/
lemma natDiv_bounds (N a : ℕ) (ha : 0 < a) :
    (N : ℝ) / a - 1 < ((N / a : ℕ) : ℝ) ∧ ((N / a : ℕ) : ℝ) ≤ (N : ℝ) / a := by
  refine ⟨?_, Nat.cast_div_le⟩
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have h := Nat.lt_div_mul_add (a := N) ha
  have : (N : ℝ) < ((N / a : ℕ) : ℝ) * a + a := by exact_mod_cast h
  rw [div_sub_one ha'.ne', div_lt_iff₀ ha']
  linarith

/-- `|∑_{a ≤ u} [N/a] - N ∑_{a ≤ u} 1/a| ≤ u`. -/
lemma abs_sum_natDiv_sub_le (N u : ℕ) :
    |∑ a ∈ Ioc 0 u, ((N / a : ℕ) : ℝ) - N * ∑ a ∈ Ioc 0 u, (1 : ℝ) / a| ≤ u := by
  rw [mul_sum, ← sum_sub_distrib]
  calc |∑ a ∈ Ioc 0 u, (((N / a : ℕ) : ℝ) - N * (1 / a))|
      ≤ ∑ a ∈ Ioc 0 u, |((N / a : ℕ) : ℝ) - N * (1 / a)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ Ioc 0 u, (1 : ℝ) := by
        refine sum_le_sum fun a ha => ?_
        have ha0 : 0 < a := (mem_Ioc.mp ha).1
        obtain ⟨h1, h2⟩ := natDiv_bounds N a ha0
        rw [mul_one_div, abs_le]
        constructor <;> linarith
    _ = u := by simp

/-- `0 < H_u - log u - γ ≤ 1/u` for `u ≥ 1`. -/
lemma harmonic_sub_log_sub_gamma_bounds {u : ℕ} (hu : 0 < u) :
    0 < (harmonic u : ℝ) - log u - eulerMascheroniConstant ∧
      (harmonic u : ℝ) - log u - eulerMascheroniConstant ≤ 1 / u := by
  have h1 := eulerMascheroniConstant_lt_eulerMascheroniSeq' u
  have h2 := eulerMascheroniSeq_lt_eulerMascheroniConstant u
  simp only [eulerMascheroniSeq', eulerMascheroniSeq, hu.ne', ite_false] at h1 h2
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu
  have hlog : log ((u : ℝ) + 1) - log u ≤ 1 / u := by
    rw [← log_div (by positivity) hu'.ne']
    have := log_le_sub_one_of_pos (x := ((u : ℝ) + 1) / u) (by positivity)
    have e : ((u : ℝ) + 1) / u - 1 = 1 / u := by field_simp; ring
    linarith
  constructor <;> linarith

/-- `∑_{a ≤ u} 1/a = H_u`. -/
lemma sum_Ioc_one_div_eq_harmonic (u : ℕ) : ∑ a ∈ Ioc 0 u, (1 : ℝ) / a = harmonic u := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  have : Ioc 0 u = Icc 1 u := by ext; simp; omega
  rw [this]
  simp [one_div]

/-- The hyperbola identity in `ℝ`: `∑_{k ≤ N} d(k) = 2 ∑_{a ≤ u} [N/a] - u²`. -/
lemma sum_sigma_zero_eq (N : ℕ) :
    ∑ k ∈ Ioc 0 N, (σ 0 k : ℝ) =
      2 * ∑ a ∈ Ioc 0 (Nat.sqrt N), ((N / a : ℕ) : ℝ) - (Nat.sqrt N : ℝ) ^ 2 := by
  have h := sum_div_add_sqrt_sq N
  rw [← ArithmeticFunction.sum_Ioc_sigma0_eq_sum_div] at h
  have h' : (∑ k ∈ Ioc 0 N, σ 0 k : ℕ) + Nat.sqrt N ^ 2 =
      2 * ∑ a ∈ Ioc 0 (Nat.sqrt N), N / a := h
  have := congrArg (fun n : ℕ => (n : ℝ)) h'
  push_cast at this
  linarith

/-- **Theorem 320** (Dirichlet; Hardy–Wright).
`d(1) + d(2) + ⋯ + d(n) = n log n + (2γ - 1) n + O(√n)`, `γ` Euler's constant. -/
@[kb "hardywright2008" "Thm 320, p. 366"]
theorem sum_card_divisors_sub_isBigO :
    (fun n : ℕ => ∑ k ∈ Ioc 0 n, (σ 0 k : ℝ) -
      (n * log n + (2 * eulerMascheroniConstant - 1) * n)) =O[atTop] fun n => √(n : ℝ) := by
  refine IsBigO.of_bound 20 ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  set u := Nat.sqrt N with hu
  have hu1 : 1 ≤ u := Nat.le_sqrt.mpr (by simpa using hN)
  have hur : (1 : ℝ) ≤ u := by exact_mod_cast hu1
  have hu0 : (0 : ℝ) < u := by linarith
  have hsq1 : u * u ≤ N := Nat.sqrt_le N
  have hsq2 : N < (u + 1) * (u + 1) := Nat.lt_succ_sqrt N
  have hsq1r : (u : ℝ) ^ 2 ≤ N := by rw [sq]; exact_mod_cast hsq1
  have hsq2r : (N : ℝ) < ((u : ℝ) + 1) ^ 2 := by rw [sq]; exact_mod_cast hsq2
  have hN0 : (0 : ℝ) < N := by linarith [sq_nonneg (u : ℝ), sq_pos_of_pos hu0]
  -- the four error terms
  have e1 := abs_sum_natDiv_sub_le N u
  rw [sum_Ioc_one_div_eq_harmonic] at e1
  obtain ⟨e2a, e2b⟩ := harmonic_sub_log_sub_gamma_bounds (u := u) (by omega)
  have e3a : 2 * log u ≤ log N := by
    rw [show (2 : ℝ) * log u = log ((u : ℝ) ^ 2) by rw [log_pow]; norm_num]
    exact log_le_log (by positivity) hsq1r
  have e3b : log N - 2 * log u ≤ 2 / u := by
    have h1 : log N ≤ 2 * log ((u : ℝ) + 1) := by
      rw [show (2 : ℝ) * log ((u : ℝ) + 1) = log (((u : ℝ) + 1) ^ 2) by rw [log_pow]; norm_num]
      exact log_le_log hN0 hsq2r.le
    have hlog : log ((u : ℝ) + 1) - log u ≤ 1 / u := by
      rw [← log_div (by positivity) hu0.ne']
      have := log_le_sub_one_of_pos (x := ((u : ℝ) + 1) / u) (by positivity)
      have e : ((u : ℝ) + 1) / u - 1 = 1 / u := by field_simp; ring
      linarith
    have : (2 : ℝ) / u = 2 * (1 / u) := by ring
    linarith
  have e4n : N ≤ u * u + 2 * u := by nlinarith [hsq2]
  have e4 : (N : ℝ) - u ^ 2 ≤ 2 * u := by
    have : (N : ℝ) ≤ u * u + 2 * u := by exact_mod_cast e4n
    nlinarith
  have hNu : (N : ℝ) / u ≤ 4 * u := by
    rw [div_le_iff₀ hu0]; nlinarith
  have hsqrt : (u : ℝ) ≤ √(N : ℝ) := Real.nat_sqrt_le_real_sqrt
  -- assemble
  rw [sum_sigma_zero_eq N, ← hu, Real.norm_eq_abs, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  set S := ∑ a ∈ Ioc 0 u, ((N / a : ℕ) : ℝ)
  set H := (harmonic u : ℝ)
  have key : 2 * S - (u : ℝ) ^ 2 - (N * log N + (2 * eulerMascheroniConstant - 1) * N) =
      2 * (S - N * H) + 2 * N * (H - log u - eulerMascheroniConstant) -
        N * (log N - 2 * log u) + (N - u ^ 2) := by ring
  rw [key]
  have hA : |2 * (S - N * H)| ≤ 2 * u := by rw [abs_mul, abs_two]; linarith
  have hB : |2 * N * (H - log u - eulerMascheroniConstant)| ≤ 8 * u := by
    rw [abs_of_pos (by positivity)]
    calc 2 * N * (H - log u - eulerMascheroniConstant) ≤ 2 * N * (1 / u) := by gcongr
      _ = 2 * (N / u) := by ring
      _ ≤ 8 * u := by linarith
  have hC : |(N : ℝ) * (log N - 2 * log u)| ≤ 8 * u := by
    rw [abs_of_nonneg (by nlinarith)]
    calc (N : ℝ) * (log N - 2 * log u) ≤ N * (2 / u) := by gcongr
      _ = 2 * (N / u) := by ring
      _ ≤ 8 * u := by linarith
  have hD : |(N : ℝ) - u ^ 2| ≤ 2 * u := by rw [abs_of_nonneg (by linarith)]; exact e4
  calc |2 * (S - N * H) + 2 * N * (H - log u - eulerMascheroniConstant) -
        N * (log N - 2 * log u) + (N - u ^ 2)|
      ≤ |2 * (S - N * H)| + |2 * N * (H - log u - eulerMascheroniConstant)| +
        |(N : ℝ) * (log N - 2 * log u)| + |(N : ℝ) - u ^ 2| := by
        have := abs_add_le (2 * (S - N * H) + 2 * N * (H - log u - eulerMascheroniConstant) -
          N * (log N - 2 * log u)) (N - u ^ 2)
        have := abs_sub (2 * (S - N * H) + 2 * N * (H - log u - eulerMascheroniConstant))
          (N * (log N - 2 * log u))
        have := abs_add_le (2 * (S - N * H)) (2 * N * (H - log u - eulerMascheroniConstant))
        linarith
    _ ≤ 20 * u := by linarith
    _ ≤ 20 * √(N : ℝ) := by linarith

lemma tendsto_log_natCast : Tendsto (fun n : ℕ => log n) atTop atTop :=
  tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- `n = o(n log n)`. -/
lemma isLittleO_id_mul_log : (fun n : ℕ => (n : ℝ)) =o[atTop] fun n => (n : ℝ) * log n := by
  have h1 : (fun _ : ℕ => (1 : ℝ)) =o[atTop] fun n => log n := by
    rw [isLittleO_one_left_iff]
    exact tendsto_norm_atTop_atTop.comp tendsto_log_natCast
  simpa using (isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).mul_isLittleO h1

/-- `√n = O(n)`. -/
lemma sqrt_isBigO_id : (fun n : ℕ => √(n : ℝ)) =O[atTop] fun n => (n : ℝ) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.norm_of_nonneg (sqrt_nonneg _), Real.norm_of_nonneg (by linarith), one_mul]
  rw [sqrt_le_left (by linarith)]
  nlinarith

/-- **Theorem 318** (Hardy–Wright). `d(1) + d(2) + ⋯ + d(n) ~ n log n`. -/
@[kb "hardywright2008" "Thm 318, p. 366"]
theorem sum_card_divisors_isEquivalent :
    (fun n : ℕ => ∑ k ∈ Ioc 0 n, (σ 0 k : ℝ)) ~[atTop] fun n => (n : ℝ) * log n := by
  have h := sum_card_divisors_sub_isBigO
  have h2 : (fun n : ℕ => ∑ k ∈ Ioc 0 n, (σ 0 k : ℝ) - (n : ℝ) * log n) =
      fun n => (∑ k ∈ Ioc 0 n, (σ 0 k : ℝ) - (n * log n + (2 * eulerMascheroniConstant - 1) * n))
        + (2 * eulerMascheroniConstant - 1) * n := by
    funext n; ring
  show (_ - _) =o[atTop] _
  rw [show ((fun n : ℕ => ∑ k ∈ Ioc 0 n, (σ 0 k : ℝ)) - fun n : ℕ => (n : ℝ) * log n) =
    fun n : ℕ => ∑ k ∈ Ioc 0 n, (σ 0 k : ℝ) - (n : ℝ) * log n from rfl, h2]
  refine IsLittleO.add ?_ ?_
  · exact h.trans_isLittleO (sqrt_isBigO_id.trans_isLittleO isLittleO_id_mul_log)
  · exact isLittleO_id_mul_log.const_mul_left _

/-- `n log n - n ≤ ∑_{k ≤ n} log k ≤ n log n`. -/
lemma sum_log_bounds (n : ℕ) :
    (n : ℝ) * log n - n ≤ ∑ k ∈ Ioc 0 n, log k ∧ ∑ k ∈ Ioc 0 n, log k ≤ (n : ℝ) * log n := by
  have hfac : ∑ k ∈ Ioc 0 n, log k = log (n.factorial : ℝ) := by
    have hI : Ioc 0 n = Ico 1 (n + 1) := by ext; simp; omega
    rw [← Finset.prod_Ico_id_eq_factorial, ← hI, Nat.cast_prod, log_prod]
    intro k hk
    exact_mod_cast (mem_Ioc.mp hk).1.ne'
  rw [hfac]
  have hpos : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  constructor
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have h := pow_div_factorial_le_exp (x := (n : ℝ)) (Nat.cast_nonneg n) n
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_iff₀ hpos] at h
    have := log_le_log (by positivity) h
    rw [log_pow, log_mul (exp_pos _).ne' hpos.ne', log_exp] at this
    linarith
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have h : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
    have := log_le_log hpos h
    rwa [log_pow] at this

/-- **Theorem 319** (Hardy–Wright). The average order of `d(n)` is `log n`:
`d(1) + ⋯ + d(n) ~ log 1 + ⋯ + log n`. -/
@[kb "hardywright2008" "Thm 319, p. 366"]
theorem sum_card_divisors_isEquivalent_sum_log :
    (fun n : ℕ => ∑ k ∈ Ioc 0 n, (σ 0 k : ℝ)) ~[atTop] fun n => ∑ k ∈ Ioc 0 n, log k := by
  refine sum_card_divisors_isEquivalent.trans ?_
  refine IsEquivalent.symm ?_
  show (_ - _) =o[atTop] _
  refine IsBigO.trans_isLittleO ?_ isLittleO_id_mul_log
  refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
  obtain ⟨h1, h2⟩ := sum_log_bounds n
  simp only [Pi.sub_apply, Real.norm_eq_abs, one_mul]
  rw [abs_of_nonpos (by linarith), abs_of_nonneg (Nat.cast_nonneg n)]
  linarith


/-- `0 ≤ ∑_{n > N} 1/n² ≤ 2/(N+1)`, as a statement about the partial sums of `ζ(2) = π²/6`. -/
lemma sum_Ioc_inv_sq_bounds (N : ℕ) :
    ∑ x ∈ Ioc 0 N, (1 : ℝ) / (x : ℝ) ^ 2 ≤ π ^ 2 / 6 ∧
      π ^ 2 / 6 - ∑ x ∈ Ioc 0 N, (1 : ℝ) / (x : ℝ) ^ 2 ≤ 2 / (N + 1) := by
  set f : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ 2 with hf
  have hs : Summable f := hasSum_zeta_two.summable
  have hrange : ∑ x ∈ Ioc 0 N, f x = ∑ x ∈ range (N + 1), f x := by
    induction N with
    | zero => simp [hf]
    | succ N ih => rw [sum_Ioc_succ_top (by omega), ih, sum_range_succ _ (N + 1)]
  have htail := hs.sum_add_tsum_nat_add (N + 1)
  rw [hasSum_zeta_two.tsum_eq] at htail
  have hnn : 0 ≤ ∑' n, f (n + (N + 1)) := tsum_nonneg fun n => by positivity
  have hle : ∑' n, f (n + (N + 1)) ≤ 2 / (N + 1) := by
    refine Real.tsum_le_of_sum_range_le (fun n => by positivity) fun M => ?_
    have : ∑ i ∈ range M, f (i + (N + 1)) = ∑ i ∈ Ioo N (M + (N + 1)), ((i : ℝ) ^ 2)⁻¹ := by
      have hI : Ioo N (M + (N + 1)) = Ico (N + 1) (M + (N + 1)) := by ext; simp
      rw [hI, Finset.sum_Ico_eq_sum_range]
      refine sum_congr (by congr 1; omega) fun i _ => ?_
      simp only [hf, one_div]
      congr 2; push_cast; ring
    rw [this]
    have := sum_Ioo_inv_sq_le (α := ℝ) N (M + (N + 1))
    exact_mod_cast this
  rw [hrange]
  constructor <;> linarith

/-- `2 (1 + 2 + ⋯ + M) = M (M + 1)`. -/
lemma two_mul_sum_Ioc_id (M : ℕ) : 2 * ∑ y ∈ Ioc 0 M, (y : ℝ) = M * (M + 1) := by
  induction M with
  | zero => simp
  | succ M ih => rw [sum_Ioc_succ_top (by omega), mul_add, ih]; push_cast; ring

/-- `|∑_{y ≤ [N/x]} y - N²/(2x²)| ≤ N/x`. -/
lemma abs_sum_Ioc_div_sub_le (N x : ℕ) (hx : 0 < x) :
    |∑ y ∈ Ioc 0 (N / x), (y : ℝ) - (N : ℝ) ^ 2 / (2 * (x : ℝ) ^ 2)| ≤ (N : ℝ) / x := by
  have hT := two_mul_sum_Ioc_id (N / x)
  obtain ⟨h1, h2⟩ := natDiv_bounds N x hx
  set q : ℝ := ((N / x : ℕ) : ℝ)
  set r : ℝ := (N : ℝ) / x
  have hx' : (0 : ℝ) < x := by exact_mod_cast hx
  have hq0 : 0 ≤ q := Nat.cast_nonneg _
  have hr : (N : ℝ) ^ 2 / (2 * (x : ℝ) ^ 2) = r ^ 2 / 2 := by
    simp only [r]; field_simp
  rw [hr, abs_le]
  have hsum : ∑ y ∈ Ioc 0 (N / x), (y : ℝ) = q * (q + 1) / 2 := by linarith
  rw [hsum]
  constructor <;> nlinarith

/-- `σ(k) = ∑_{ab = k} b`, so `∑_{k ≤ N} σ(k) = ∑_{a ≤ N} ∑_{b ≤ N/a} b`. -/
lemma sum_sigma_one_eq (N : ℕ) :
    ∑ k ∈ Ioc 0 N, (σ 1 k : ℝ) = ∑ a ∈ Ioc 0 N, ∑ b ∈ Ioc 0 (N / a), (b : ℝ) := by
  rw [sum_Ioc_sum_Ioc_div_eq (fun _ b => (b : ℝ))]
  refine sum_congr rfl fun k _ => ?_
  rw [ArithmeticFunction.sigma_one_apply, Nat.cast_sum,
    Nat.sum_divisorsAntidiagonal' (fun _ b => (b : ℝ))]

/-- `log n ≥ 1` for `n ≥ 3`. -/
lemma one_le_log_of_three_le {n : ℕ} (hn : 3 ≤ n) : 1 ≤ log n := by
  rw [le_log_iff_exp_le (by positivity)]
  have : (3 : ℝ) ≤ n := by exact_mod_cast hn
  linarith [exp_one_lt_d9]

/-- Splitting `∑_{a ≤ N} c_a T_a - (N²/2) L` into the floor errors and the tail of the series. -/
lemma abs_weighted_sum_sub_le (N : ℕ) (c : ℕ → ℝ) (hc : ∀ a, |c a| ≤ 1) (L : ℝ)
    (hL : |L - ∑ a ∈ Ioc 0 N, c a / (a : ℝ) ^ 2| ≤ 2 / (N + 1)) :
    |∑ a ∈ Ioc 0 N, c a * ∑ b ∈ Ioc 0 (N / a), (b : ℝ) - (N : ℝ) ^ 2 / 2 * L| ≤
      N * (1 + log N) + N := by
  have key : ∑ a ∈ Ioc 0 N, c a * ∑ b ∈ Ioc 0 (N / a), (b : ℝ) - (N : ℝ) ^ 2 / 2 * L =
      ∑ a ∈ Ioc 0 N, c a * (∑ b ∈ Ioc 0 (N / a), (b : ℝ) - (N : ℝ) ^ 2 / (2 * (a : ℝ) ^ 2)) -
        (N : ℝ) ^ 2 / 2 * (L - ∑ a ∈ Ioc 0 N, c a / (a : ℝ) ^ 2) := by
    have hs : ∑ a ∈ Ioc 0 N, c a * ((N : ℝ) ^ 2 / (2 * (a : ℝ) ^ 2)) =
        (N : ℝ) ^ 2 / 2 * ∑ a ∈ Ioc 0 N, c a / (a : ℝ) ^ 2 := by
      rw [mul_sum]; exact sum_congr rfl fun a _ => by ring
    simp only [mul_sub, sum_sub_distrib]
    rw [hs]
    ring
  rw [key]
  have hA : |∑ a ∈ Ioc 0 N, c a * (∑ b ∈ Ioc 0 (N / a), (b : ℝ) - (N : ℝ) ^ 2 / (2 * (a : ℝ) ^ 2))|
      ≤ N * (1 + log N) := by
    calc _ ≤ ∑ a ∈ Ioc 0 N,
            |c a * (∑ b ∈ Ioc 0 (N / a), (b : ℝ) - (N : ℝ) ^ 2 / (2 * (a : ℝ) ^ 2))| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ Ioc 0 N, (N : ℝ) / a := by
          refine sum_le_sum fun a ha => ?_
          rw [abs_mul]
          have h1 := abs_sum_Ioc_div_sub_le N a (mem_Ioc.mp ha).1
          have h2 := hc a
          have h3 := abs_nonneg (∑ b ∈ Ioc 0 (N / a), (b : ℝ) - (N : ℝ) ^ 2 / (2 * (a : ℝ) ^ 2))
          nlinarith
      _ = N * harmonic N := by
          rw [← sum_Ioc_one_div_eq_harmonic, mul_sum]; exact sum_congr rfl fun a _ => by ring
      _ ≤ N * (1 + log N) := by gcongr; exact harmonic_le_one_add_log N
  have hB : |(N : ℝ) ^ 2 / 2 * (L - ∑ a ∈ Ioc 0 N, c a / (a : ℝ) ^ 2)| ≤ (N : ℝ) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc (N : ℝ) ^ 2 / 2 * |L - ∑ a ∈ Ioc 0 N, c a / (a : ℝ) ^ 2|
        ≤ (N : ℝ) ^ 2 / 2 * (2 / ((N : ℝ) + 1)) := by gcongr
      _ ≤ (N : ℝ) := by
          rw [show (N : ℝ) ^ 2 / 2 * (2 / ((N : ℝ) + 1)) = N * (N / (N + 1)) by ring]
          have : (N : ℝ) / (N + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
          have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
          nlinarith
  exact (abs_sub _ _).trans (add_le_add hA hB)

/-- **Theorem 324** (Hardy–Wright). `σ(1) + σ(2) + ⋯ + σ(n) = π² n²/12 + O(n log n)`. -/
@[kb "hardywright2008" "Thm 324, p. 370"]
theorem sum_sigma_one_sub_isBigO :
    (fun n : ℕ => ∑ k ∈ Ioc 0 n, (σ 1 k : ℝ) - π ^ 2 / 12 * (n : ℝ) ^ 2) =O[atTop]
      fun n => (n : ℝ) * log n := by
  refine IsBigO.of_bound 3 ?_
  filter_upwards [eventually_ge_atTop 3] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog := one_le_log_of_three_le hN
  rw [sum_sigma_one_eq, Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
  have h := abs_weighted_sum_sub_le N (fun _ => 1) (fun _ => by simp) (π ^ 2 / 6) (by
    obtain ⟨h1, h2⟩ := sum_Ioc_inv_sq_bounds N
    rw [abs_of_nonneg (by simp only [one_div] at h1 ⊢; linarith)]
    simpa using h2)
  simp only [one_mul] at h
  rw [show π ^ 2 / 12 * (N : ℝ) ^ 2 = (N : ℝ) ^ 2 / 2 * (π ^ 2 / 6) by ring]
  nlinarith

/-- `∑ μ(n)/n² = 1/ζ(2) = 6/π²` (Theorem 287 at `s = 2`, with `ζ(2) = π²/6`). -/
theorem hasSum_moebius_div_sq : HasSum (fun n : ℕ => (μ n : ℝ) / (n : ℝ) ^ 2) (6 / π ^ 2) := by
  have hs : Summable fun n : ℕ => (μ n : ℝ) / (n : ℝ) ^ 2 := by
    refine Summable.of_norm_bounded hasSum_zeta_two.summable fun n => ?_
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2)]
    have : |(μ n : ℝ)| ≤ 1 := by
      have := ArithmeticFunction.abs_moebius (n := n)
      rw [← Int.cast_abs, this]; split_ifs <;> norm_num
    rw [one_div]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [div_eq_mul_inv]
    have : (0 : ℝ) ≤ ((n : ℝ) ^ 2)⁻¹ := by positivity
    nlinarith
  convert hs.hasSum
  have hL := LSeries_one_mul_Lseries_moebius (s := 2) (by norm_num)
  rw [LSeries_one_eq_riemannZeta (by norm_num), riemannZeta_two] at hL
  have hLμ : LSeries (fun n => (μ n : ℂ)) 2 = ((∑' n : ℕ, (μ n : ℝ) / (n : ℝ) ^ 2 : ℝ) : ℂ) := by
    rw [LSeries, Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [LSeries.term_of_ne_zero hn.ne', show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num,
      Complex.cpow_natCast]
    push_cast; ring
  rw [hLμ] at hL
  generalize (∑' n : ℕ, (μ n : ℝ) / (n : ℝ) ^ 2) = T at hL ⊢
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have : (T : ℂ) = ((6 / π ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat]
    field_simp
    linear_combination 6 * hL
  exact_mod_cast this.symm

lemma sum_Ioc_eq_sum_range {u : ℕ → ℝ} (hu : u 0 = 0) (N : ℕ) :
    ∑ x ∈ Ioc 0 N, u x = ∑ x ∈ range (N + 1), u x := by
  induction N with
  | zero => simp [hu]
  | succ N ih => rw [sum_Ioc_succ_top (by omega), ih, sum_range_succ _ (N + 1)]

/-- `|∑_{a ≤ N} μ(a)/a² - 6/π²| ≤ 2/(N+1)`. -/
lemma abs_sum_moebius_div_sq_sub_le (N : ℕ) :
    |6 / π ^ 2 - ∑ a ∈ Ioc 0 N, (μ a : ℝ) / (a : ℝ) ^ 2| ≤ 2 / ((N : ℝ) + 1) := by
  set g : ℕ → ℝ := fun n => (μ n : ℝ) / (n : ℝ) ^ 2 with hg
  set f : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ 2 with hf
  have hgs := hasSum_moebius_div_sq
  have hrange : ∑ x ∈ Ioc 0 N, g x = ∑ x ∈ range (N + 1), g x :=
    sum_Ioc_eq_sum_range (by simp [hg]) N
  have hfrange : ∑ x ∈ Ioc 0 N, f x = ∑ x ∈ range (N + 1), f x :=
    sum_Ioc_eq_sum_range (by simp [hf]) N
  have h1 := hgs.summable.sum_add_tsum_nat_add (N + 1)
  rw [hgs.tsum_eq] at h1
  have h2 := hasSum_zeta_two.summable.sum_add_tsum_nat_add (N + 1)
  rw [hasSum_zeta_two.tsum_eq] at h2
  have hle : |∑' n, g (n + (N + 1))| ≤ ∑' n, f (n + (N + 1)) := by
    have hsg : Summable fun n => ‖g (n + (N + 1))‖ :=
      hgs.summable.norm.comp_injective (add_left_injective (N + 1))
    have hsf : Summable fun n => f (n + (N + 1)) :=
      hasSum_zeta_two.summable.comp_injective (add_left_injective (N + 1))
    rw [← Real.norm_eq_abs]
    refine (norm_tsum_le_tsum_norm hsg).trans ?_
    refine Summable.tsum_le_tsum (fun n => ?_) hsg hsf
    simp only [hg, hf, Real.norm_eq_abs, abs_div]
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n + (N + 1) : ℕ) : ℝ) ^ 2)]
    gcongr
    have := ArithmeticFunction.abs_moebius (n := n + (N + 1))
    rw [← Int.cast_abs, this]; split_ifs <;> norm_num
  have ht := (sum_Ioc_inv_sq_bounds N).2
  have e1 : 6 / π ^ 2 - ∑ a ∈ Ioc 0 N, g a = ∑' n, g (n + (N + 1)) := by
    rw [hrange]; linarith
  have e2 : π ^ 2 / 6 - ∑ a ∈ Ioc 0 N, f a = ∑' n, f (n + (N + 1)) := by
    rw [hfrange]; linarith
  rw [e1]
  calc _ ≤ ∑' n, f (n + (N + 1)) := hle
    _ = π ^ 2 / 6 - ∑ a ∈ Ioc 0 N, f a := e2.symm
    _ ≤ 2 / (N + 1) := ht

/-- (16.3.1): `φ(n) = ∑_{dd' = n} μ(d) d'`. -/
lemma totient_eq_sum_antidiagonal {n : ℕ} (hn : 0 < n) :
    (n.totient : ℝ) = ∑ x ∈ n.divisorsAntidiagonal, (μ x.1 : ℝ) * x.2 := by
  have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℝ)
    (f := fun n => (n.totient : ℝ)) (g := fun n => (n : ℝ))).mp (fun n _ => by
      exact_mod_cast Nat.sum_totient n) n hn
  exact h.symm

/-- `Φ(N) = ∑_{d ≤ N} μ(d) ∑_{d' ≤ N/d} d'`. -/
lemma sum_totient_eq (N : ℕ) :
    ∑ k ∈ Ioc 0 N, (k.totient : ℝ) = ∑ a ∈ Ioc 0 N, (μ a : ℝ) * ∑ b ∈ Ioc 0 (N / a), (b : ℝ) := by
  simp_rw [mul_sum]
  rw [sum_Ioc_sum_Ioc_div_eq (fun a b => (μ a : ℝ) * b)]
  exact sum_congr rfl fun k hk => totient_eq_sum_antidiagonal (mem_Ioc.mp hk).1

/-- **Theorem 330** (Mertens; Hardy–Wright).
`Φ(n) = φ(1) + ⋯ + φ(n) = 3n²/π² + O(n log n)`. -/
@[kb "hardywright2008" "Thm 330, p. 372"]
theorem sum_totient_sub_isBigO :
    (fun n : ℕ => ∑ k ∈ Ioc 0 n, (k.totient : ℝ) - 3 * (n : ℝ) ^ 2 / π ^ 2) =O[atTop]
      fun n => (n : ℝ) * log n := by
  refine IsBigO.of_bound 3 ?_
  filter_upwards [eventually_ge_atTop 3] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog := one_le_log_of_three_le hN
  rw [sum_totient_eq, Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
  have h := abs_weighted_sum_sub_le N (fun a => (μ a : ℝ)) (fun a => by
    have := ArithmeticFunction.abs_moebius (n := a)
    rw [← Int.cast_abs, this]; split_ifs <;> norm_num) (6 / π ^ 2)
    (abs_sum_moebius_div_sq_sub_le N)
  rw [show 3 * (N : ℝ) ^ 2 / π ^ 2 = (N : ℝ) ^ 2 / 2 * (6 / π ^ 2) by ring]
  nlinarith

/-- The pairs `(p, q)` with `1 ≤ p ≤ q ≤ n`. -/
def fractionPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (Icc 1 n ×ˢ Icc 1 n).filter fun x => x.1 ≤ x.2

lemma card_filter_fractionPairs (n : ℕ) (P : ℕ → ℕ → Prop) [∀ p q, Decidable (P p q)] :
    #((fractionPairs n).filter fun x => P x.1 x.2) =
      ∑ q ∈ Icc 1 n, #((Icc 1 q).filter fun p => P p q) := by
  rw [fractionPairs, filter_filter, card_filter, sum_product_right]
  refine sum_congr rfl fun q hq => ?_
  rw [card_filter]
  simp only [mem_Icc] at hq
  have hsplit : Icc 1 n = Icc 1 q ∪ Ioc q n := by
    ext p; simp only [mem_Icc, mem_union, mem_Ioc]; omega
  rw [hsplit, sum_union (by
    rw [disjoint_left]; intro p h1 h2; simp only [mem_Icc, mem_Ioc] at h1 h2; omega)]
  have h0 : ∑ p ∈ Ioc q n, (if p ≤ q ∧ P p q then 1 else 0) = 0 :=
    sum_eq_zero fun p hp => by
      simp only [mem_Ioc] at hp
      exact ite_eq_right_of_eq_false _ _ (eq_false (by omega))
  rw [h0, add_zero]
  refine sum_congr rfl fun p hp => ?_
  simp only [mem_Icc] at hp
  simp [hp.2]

lemma card_fractionPairs (n : ℕ) : (#(fractionPairs n) : ℝ) = n * (n + 1) / 2 := by
  have h := card_filter_fractionPairs n (fun _ _ => True)
  simp only [filter_true_of_mem (fun _ _ => trivial), Nat.card_Icc, add_tsub_cancel_right] at h
  rw [h]
  have hI : Icc 1 n = Ioc 0 n := by ext; simp; omega
  push_cast
  rw [hI]
  have := two_mul_sum_Ioc_id n
  linarith

lemma card_coprime_fractionPairs (n : ℕ) :
    #((fractionPairs n).filter fun x => Nat.Coprime x.1 x.2) = ∑ q ∈ Ioc 0 n, q.totient := by
  rw [card_filter_fractionPairs n (fun p q => Nat.Coprime p q)]
  have hI : Icc 1 n = Ioc 0 n := by ext; simp; omega
  rw [hI]
  refine sum_congr rfl fun q _ => ?_
  have := Nat.filter_coprime_Ico_eq_totient q 1
  rw [← this]
  congr 1
  ext p
  simp only [mem_filter, mem_Icc, mem_Ico]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, by omega⟩, h3.symm⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, by omega⟩, h3.symm⟩

/-- **Theorem 332** (Hardy–Wright). The probability that two integers are coprime is `6/π²`:
if `t_n` is the number of pairs `(p, q)` with `1 ≤ p ≤ q ≤ n` and `X_n` the number of them with
`(p, q) = 1` (the fractions `p/q` in lowest terms), then `X_n / t_n → 6/π²`. -/
@[kb "hardywright2008" "Thm 332, p. 373"]
theorem tendsto_card_coprime_div_card :
    Tendsto (fun n => (#((fractionPairs n).filter fun x => Nat.Coprime x.1 x.2) : ℝ) /
      #(fractionPairs n)) atTop (𝓝 (6 / π ^ 2)) := by
  set E : ℕ → ℝ := fun n => ∑ k ∈ Ioc 0 n, (k.totient : ℝ) - 3 * (n : ℝ) ^ 2 / π ^ 2 with hE
  have hE1 : E =O[atTop] fun n => (n : ℝ) * log n := sum_totient_sub_isBigO
  have hlo : (fun n : ℕ => (n : ℝ) * log n) =o[atTop] fun n => (n : ℝ) ^ 2 := by
    have h1 : (fun n : ℕ => log (n : ℝ)) =o[atTop] fun n => (n : ℝ) :=
      isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
    simpa [sq] using (isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).mul_isLittleO h1
  have hE2 : Tendsto (fun n => E n / (n : ℝ) ^ 2) atTop (𝓝 0) :=
    (hE1.trans_isLittleO hlo).tendsto_div_nhds_zero
  have hfrac : Tendsto (fun n : ℕ => (n : ℝ) / (n + 1)) atTop (𝓝 1) :=
    tendsto_natCast_div_add_atTop 1
  have hlim := ((hE2.const_mul 2).add (tendsto_const_nhds (x := 6 / π ^ 2))).mul hfrac
  rw [show (2 * 0 + 6 / π ^ 2) * 1 = 6 / π ^ 2 by ring] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [card_fractionPairs, card_coprime_fractionPairs]
  push_cast
  have hΦ : ∑ k ∈ Ioc 0 n, (k.totient : ℝ) = E n + 3 * (n : ℝ) ^ 2 / π ^ 2 := by
    simp only [hE]; ring
  rw [hΦ]
  have hpi : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

end NTKB.HardyWright
