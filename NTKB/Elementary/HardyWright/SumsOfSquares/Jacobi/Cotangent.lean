/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Jacobi.Lemmas

/-!
# Hardy–Wright, § 20.12: the cotangent identity (Theorem 383)

For `|x| < 1`, `u_n = xⁿ/(1 - xⁿ)` and `θ` real and not an even multiple of `π`,
`L = ¼ cot ½θ + u₁ sin θ + u₂ sin 2θ + ⋯`,
`T₁ = (¼ cot ½θ)² + u₁(1 + u₁) cos θ + u₂(1 + u₂) cos 2θ + ⋯`,
`T₂ = ½{u₁(1 - cos θ) + 2u₂(1 - cos 2θ) + 3u₃(1 - cos 3θ) + ⋯}`,
then `L² = T₁ + T₂` (`cotangent_identity`).

The proof is the book's: `L²` is expanded with `½ cot ½θ sin nθ = ½ + cos θ + ⋯ + cos (n-1)θ + ½ cos nθ`
and `2 sin mθ sin nθ = cos (m - n)θ - cos (m + n)θ`, the double series are rearranged as series of
cosines of multiples of `θ` (justified by absolute convergence), and the coefficients are simplified
with `u_l u_{k-l} = u_k(1 + u_l + u_{k-l})`, `u_{k+l} + u_l u_{k+l} = u_k(u_l - u_{k+l})` and
Theorem 381.
-/

open Finset Filter Topology Real

namespace NTKB.HardyWright

variable {x : ℝ}

/-! ### Trigonometric lemma -/

/-- `½ + cos θ + ⋯ + cos (n-1)θ + ½ cos nθ`. -/
noncomputable def halfDirichlet (θ : ℝ) (n : ℕ) : ℝ :=
  1 / 2 + ∑ j ∈ Ico 1 n, cos (j * θ) + 1 / 2 * cos (n * θ)

/-- `½ cot ½θ sin nθ = ½ + cos θ + ⋯ + cos (n-1)θ + ½ cos nθ` for `n ≥ 1` (Hardy–Wright § 20.12). -/
lemma half_cot_mul_sin {φ : ℝ} (hφ : sin φ ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    cot φ / 2 * sin (n * (2 * φ)) = halfDirichlet (2 * φ) n := by
  rw [cot_eq_cos_div_sin]
  induction n, hn using Nat.le_induction with
  | base =>
    simp only [halfDirichlet, Nat.cast_one, one_mul, Ico_self, sum_empty, add_zero]
    rw [sin_two_mul, cos_two_mul]
    field_simp
    ring
  | succ n hn ih =>
    have hD : halfDirichlet (2 * φ) (n + 1) = halfDirichlet (2 * φ) n + 1 / 2 * cos (n * (2 * φ)) +
        1 / 2 * cos ((n + 1 : ℕ) * (2 * φ)) := by
      simp only [halfDirichlet]
      rw [sum_Ico_succ_top hn]
      ring
    rw [hD, ← ih]
    push_cast
    rw [show ((n : ℝ) + 1) * (2 * φ) = n * (2 * φ) + 2 * φ by ring, sin_add, cos_add, sin_two_mul,
      cos_two_mul]
    generalize sin (n * (2 * φ)) = S
    generalize cos (n * (2 * φ)) = C
    field_simp
    have := sin_sq_add_cos_sq φ
    linear_combination (2 * cos φ * S) * this

/-! ### Absolute convergence and rearrangement -/

lemma abs_lambertU_le' (hx : |x| < 1) (n : ℕ) : |lambertU x n| ≤ (1 - |x|)⁻¹ * |x| ^ n := by
  have := abs_lambertU_le hx n
  rwa [div_eq_mul_inv, mul_comm] at this

lemma summable_geom_prod (hx : |x| < 1) : Summable fun q : ℕ × ℕ => |x| ^ q.1 * |x| ^ q.2 :=
  Summable.mul_of_nonneg (summable_geometric_of_lt_one (abs_nonneg x) hx)
    (summable_geometric_of_lt_one (abs_nonneg x) hx) (fun _ => by positivity)
    (fun _ => by positivity)

lemma summable_lambertU_mul_trig (hx : |x| < 1) {g : ℕ → ℝ} (hg : ∀ n, |g n| ≤ 1) :
    Summable fun n => ‖lambertU x n * g n‖ :=
  (summable_abs_lambertU hx).of_nonneg_of_le (fun _ => norm_nonneg _) fun n => by
    rw [Real.norm_eq_abs, abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (hg n)

/-- A double series over `ℕ × ℕ` is the sum of its diagonal and of its two halves `m > n`, `m < n`. -/
lemma tsum_prod_eq_diag_add {F : ℕ × ℕ → ℝ} (hF : Summable F) :
    ∑' p, F p = ∑' n, F (n, n) + ∑' q : ℕ × ℕ, F (q.1 + q.2 + 1, q.1) +
      ∑' q : ℕ × ℕ, F (q.1, q.1 + q.2 + 1) := by
  classical
  set A : Set (ℕ × ℕ) := {p | p.1 = p.2}
  set B : Set (ℕ × ℕ) := {p | p.2 < p.1}
  set C : Set (ℕ × ℕ) := {p | p.1 < p.2}
  have hsplit : ∀ p, F p = A.indicator F p + B.indicator F p + C.indicator F p := by
    intro p
    simp only [Set.indicator, A, B, C, Set.mem_ofPred_eq]
    split_ifs <;> first | omega | simp
  have hA := hF.indicator A
  have hB := hF.indicator B
  have hC := hF.indicator C
  rw [tsum_congr hsplit, Summable.tsum_add (hA.add hB) hC, Summable.tsum_add hA hB]
  have gA : Function.Injective fun n : ℕ => (n, n) := fun a b h => by
    simpa using congrArg Prod.fst h
  have gB : Function.Injective fun q : ℕ × ℕ => (q.1 + q.2 + 1, q.1) := fun a b h => by
    simp only [Prod.mk.injEq] at h; ext <;> omega
  have gC : Function.Injective fun q : ℕ × ℕ => (q.1, q.1 + q.2 + 1) := fun a b h => by
    simp only [Prod.mk.injEq] at h; ext <;> omega
  have eA : ∑' n, A.indicator F (n, n) = ∑' p, A.indicator F p := gA.tsum_eq fun p hp => by
    have : p.1 = p.2 := Set.support_indicator_subset hp
    exact ⟨p.1, Prod.ext rfl this⟩
  have eB : ∑' q : ℕ × ℕ, B.indicator F (q.1 + q.2 + 1, q.1) = ∑' p, B.indicator F p :=
    gB.tsum_eq fun p hp => by
      have : p.2 < p.1 := Set.support_indicator_subset hp
      exact ⟨(p.2, p.1 - p.2 - 1), Prod.ext (by simp <;> omega) rfl⟩
  have eC : ∑' q : ℕ × ℕ, C.indicator F (q.1, q.1 + q.2 + 1) = ∑' p, C.indicator F p :=
    gC.tsum_eq fun p hp => by
      have : p.1 < p.2 := Set.support_indicator_subset hp
      exact ⟨(p.1, p.2 - p.1 - 1), Prod.ext rfl (by simp <;> omega)⟩
  rw [← eA, ← eB, ← eC]
  congr 1; congr 1
  · exact tsum_congr fun n => Set.indicator_of_mem (show (n, n) ∈ A from rfl) F
  · exact tsum_congr fun q => Set.indicator_of_mem (show _ ∈ B by simp [B]) F
  · exact tsum_congr fun q => Set.indicator_of_mem (show _ ∈ C by simp [C]) F

/-- The rearrangement of `S₁ = ∑ uₙ (½ cot ½θ sin nθ) = ∑ uₙ(½ + cos θ + ⋯ + ½ cos nθ)` as a series of
cosines (Hardy–Wright § 20.12). -/
lemma tsum_mul_halfDirichlet (hx : |x| < 1) (θ : ℝ) :
    ∑' n, lambertU x n * halfDirichlet θ n =
      1 / 2 * ∑' n, lambertU x n + 1 / 2 * ∑' n, lambertU x n * cos (n * θ) +
        ∑' j : ℕ, cos ((j + 1 : ℕ) * θ) * ∑' l : ℕ, lambertU x (j + l + 2) := by
  classical
  have hK : 0 < (1 - |x|)⁻¹ := inv_pos.2 (by linarith)
  set G : ℕ × ℕ → ℝ := fun q => lambertU x (q.1 + q.2 + 2) * cos ((q.1 + 1 : ℕ) * θ) with hG
  have hGs : Summable G := by
    refine Summable.of_norm_bounded ((summable_geom_prod hx).mul_left ((1 - |x|)⁻¹)) fun q => ?_
    simp only [hG, Real.norm_eq_abs, abs_mul]
    calc |lambertU x (q.1 + q.2 + 2)| * |cos ((q.1 + 1 : ℕ) * θ)|
        ≤ (1 - |x|)⁻¹ * |x| ^ (q.1 + q.2 + 2) * 1 :=
          mul_le_mul (abs_lambertU_le' hx _) (abs_cos_le_one _) (abs_nonneg _) (by positivity)
      _ ≤ (1 - |x|)⁻¹ * (|x| ^ q.1 * |x| ^ q.2) := by
          rw [mul_one, ← pow_add]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (abs_nonneg x) hx.le (by omega))
            hK.le
  set F' : ℕ × ℕ → ℝ := fun p => if 1 ≤ p.2 ∧ p.2 < p.1 then lambertU x p.1 * cos (p.2 * θ) else 0
    with hF'
  set g : ℕ × ℕ → ℕ × ℕ := fun q => (q.1 + q.2 + 2, q.1 + 1) with hg
  have hgi : Function.Injective g := fun a c h => by
    simp only [hg, Prod.mk.injEq] at h; ext <;> omega
  have hsupp : ∀ p ∉ Set.range g, F' p = 0 := by
    intro p hp
    simp only [hF']
    split_ifs with h
    · exact absurd ⟨(p.2 - 1, p.1 - p.2 - 1), Prod.ext (by simp [hg]; omega)
        (by simp [hg]; omega)⟩ hp
    · rfl
  have hcomp : F' ∘ g = G := by
    funext q
    simp only [Function.comp, hF', hg, hG]
    rw [ite_eq_left_iff.2 (fun h => absurd (by omega) h)]
  have hF's : Summable F' := (hgi.summable_iff hsupp).1 (hcomp ▸ hGs)
  have hrow : ∀ n, ∑' j, F' (n, j) = ∑ j ∈ Ico 1 n, lambertU x n * cos (j * θ) := by
    intro n
    rw [tsum_eq_sum (s := range n) (fun j hj => by
      simp only [hF']; rw [ite_eq_right_iff.2 (fun h => absurd h (by simp at hj; omega))])]
    rw [← Finset.sum_filter]
    congr 1; ext j; simp
  have e : ∀ n, lambertU x n * halfDirichlet θ n =
      1 / 2 * lambertU x n + 1 / 2 * (lambertU x n * cos (n * θ)) + ∑' j, F' (n, j) := by
    intro n; rw [hrow, halfDirichlet, ← mul_sum]; ring
  have hb := (summable_abs_lambertU hx).of_abs
  have hbc := (summable_lambertU_mul_trig hx (g := fun n => cos (n * θ))
    (fun n => abs_cos_le_one _)).of_norm
  rw [tsum_congr e, Summable.tsum_add ((hb.mul_left _).add (hbc.mul_left _)) hF's.prod,
    Summable.tsum_add (hb.mul_left _) (hbc.mul_left _), tsum_mul_left, tsum_mul_left]
  congr 1
  have htG : ∑' p, F' p = ∑' q, G q := by
    rw [← hgi.tsum_eq (fun p hp => by by_contra h; exact hp (hsupp p h))]
    exact tsum_congr fun q => congrFun hcomp q
  rw [← hF's.tsum_prod, htG, hGs.tsum_prod]
  refine tsum_congr fun j => ?_
  simp only [hG]
  rw [tsum_mul_right, mul_comm]

/-- The rearrangement of `S₂ = (∑ uₙ sin nθ)² = ½ ∑∑ u_m uₙ (cos (m - n)θ - cos (m + n)θ)` as a series
of cosines (Hardy–Wright § 20.12). -/
lemma sq_tsum_sin (hx : |x| < 1) (θ : ℝ) :
    (∑' n, lambertU x n * sin (n * θ)) ^ 2 =
      1 / 2 * ∑' n, lambertU x n ^ 2 +
        ∑' k : ℕ, cos ((k + 1 : ℕ) * θ) * ∑' n : ℕ, lambertU x (n + k + 1) * lambertU x n -
        1 / 2 * ∑' k : ℕ, cos (k * θ) * ∑ p ∈ antidiagonal k, lambertU x p.1 * lambertU x p.2 := by
  set b := lambertU x with hbdef
  set fs : ℕ → ℝ := fun n => b n * sin (n * θ) with hfs_def
  set fc : ℕ → ℝ := fun n => b n * cos (n * θ) with hfc_def
  have hfs : Summable fun n => ‖fs n‖ := summable_lambertU_mul_trig hx fun n => abs_sin_le_one _
  have hfc : Summable fun n => ‖fc n‖ := summable_lambertU_mul_trig hx fun n => abs_cos_le_one _
  -- the `cos (m + n)θ` part, by Cauchy products
  have hP : (∑' n, fc n) ^ 2 - (∑' n, fs n) ^ 2 =
      ∑' k : ℕ, cos (k * θ) * ∑ p ∈ antidiagonal k, b p.1 * b p.2 := by
    rw [sq, sq, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfc hfc,
      tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfs hfs,
      ← Summable.tsum_sub (summable_norm_sum_mul_antidiagonal_of_summable_norm hfc hfc).of_norm
        (summable_norm_sum_mul_antidiagonal_of_summable_norm hfs hfs).of_norm]
    refine tsum_congr fun k => ?_
    rw [← sum_sub_distrib, mul_sum]
    refine sum_congr rfl fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    simp only [hfc_def, hfs_def]
    rw [← hp]; push_cast; rw [add_mul, cos_add]; ring
  -- the `cos (m - n)θ` part, by splitting the double series
  have hM : (∑' n, fc n) ^ 2 + (∑' n, fs n) ^ 2 =
      ∑' n, b n ^ 2 + 2 * ∑' k : ℕ, cos ((k + 1 : ℕ) * θ) * ∑' n : ℕ, b (n + k + 1) * b n := by
    set F : ℕ × ℕ → ℝ := fun p => b p.1 * b p.2 * cos (((p.1 : ℝ) - p.2) * θ) with hF
    have hFe : ∀ p : ℕ × ℕ, fc p.1 * fc p.2 + fs p.1 * fs p.2 = F p := by
      intro p; simp only [hfc_def, hfs_def, hF]; rw [sub_mul, cos_sub]; ring
    have hs1 := summable_mul_of_summable_norm hfc hfc
    have hs2 := summable_mul_of_summable_norm hfs hfs
    have hFs : Summable F := (hs1.add hs2).congr hFe
    rw [sq, sq, tsum_mul_tsum_of_summable_norm hfc hfc, tsum_mul_tsum_of_summable_norm hfs hfs,
      ← Summable.tsum_add hs1 hs2, tsum_congr hFe, tsum_prod_eq_diag_add hFs]
    -- the three pieces
    set H : ℕ × ℕ → ℝ := fun q => cos ((q.2 + 1 : ℕ) * θ) * (b (q.1 + q.2 + 1) * b q.1) with hH
    have h1 : ∀ n, F (n, n) = b n ^ 2 := fun n => by simp [hF, sq]
    have h2 : ∀ q : ℕ × ℕ, F (q.1 + q.2 + 1, q.1) = H q := fun q => by
      simp only [hF, hH]; push_cast; ring_nf
    have h3 : ∀ q : ℕ × ℕ, F (q.1, q.1 + q.2 + 1) = H q := fun q => by
      simp only [hF, hH]; push_cast
      rw [show ((q.1 : ℝ) - (q.1 + q.2 + 1)) * θ = -(((q.2 : ℝ) + 1) * θ) by ring, cos_neg]; ring
    have hHs : Summable H := by
      have := hFs.comp_injective (i := fun q : ℕ × ℕ => (q.1 + q.2 + 1, q.1))
        (fun a c h => by simp only [Prod.mk.injEq] at h; ext <;> omega)
      exact this.congr fun q => h2 q
    have hHswap : ∑' q, H q = ∑' k : ℕ, cos ((k + 1 : ℕ) * θ) * ∑' n : ℕ, b (n + k + 1) * b n := by
      rw [← (Equiv.prodComm ℕ ℕ).tsum_eq]
      have hs' : Summable (H ∘ Equiv.prodComm ℕ ℕ) := (Equiv.prodComm ℕ ℕ).summable_iff.2 hHs
      rw [show (fun c => H ((Equiv.prodComm ℕ ℕ) c)) = H ∘ Equiv.prodComm ℕ ℕ from rfl,
        hs'.tsum_prod]
      refine tsum_congr fun k => ?_
      simp only [Function.comp, Equiv.prodComm_apply, Prod.swap_prod_mk, hH]
      rw [tsum_mul_left]
    rw [tsum_congr h1, tsum_congr h2, tsum_congr h3, hHswap]
    ring
  have : (∑' n, b n * sin (n * θ)) = ∑' n, fs n := rfl
  rw [this]
  linear_combination (1 / 2 : ℝ) * hM - (1 / 2 : ℝ) * hP

/-! ### The coefficients -/

lemma lambertU_add_mul (hx : |x| < 1) {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) :
    lambertU x (k + l) + lambertU x l * lambertU x (k + l) =
      lambertU x k * (lambertU x l - lambertU x (k + l)) := by
  have h1 := one_sub_pow_pos hx (show k ≠ 0 by omega)
  have h2 := one_sub_pow_pos hx (show l ≠ 0 by omega)
  have h3 := one_sub_pow_pos hx (show k + l ≠ 0 by omega)
  simp only [lambertU]
  rw [pow_add] at h3 ⊢
  field_simp
  ring

lemma lambertU_mul (hx : |x| < 1) {l m : ℕ} (hl : 1 ≤ l) (hm : 1 ≤ m) :
    lambertU x l * lambertU x m = lambertU x (l + m) * (1 + lambertU x l + lambertU x m) := by
  have h1 := one_sub_pow_pos hx (show l ≠ 0 by omega)
  have h2 := one_sub_pow_pos hx (show m ≠ 0 by omega)
  have h3 := one_sub_pow_pos hx (show l + m ≠ 0 by omega)
  simp only [lambertU]
  rw [pow_add] at h3 ⊢
  field_simp
  ring

/-- The coefficient of `cos kθ` (`k = K + 1`) in `L²`: `½u_k + ∑_{l ≥ 1}(u_{k+l} + u_l u_{k+l})
- ½ ∑_{l=1}^{k-1} u_l u_{k-l} = u_k(1 + u_k) - ½ k u_k` (Hardy–Wright § 20.12). -/
lemma coeff_identity (hx : |x| < 1) (K : ℕ) :
    1 / 2 * lambertU x (K + 1) + ∑' l : ℕ, lambertU x (K + l + 2) +
        ∑' n : ℕ, lambertU x (n + K + 1) * lambertU x n -
        1 / 2 * ∑ p ∈ antidiagonal (K + 1), lambertU x p.1 * lambertU x p.2 =
      lambertU x (K + 1) * (1 + lambertU x (K + 1)) - 1 / 2 * ((K : ℝ) + 1) * lambertU x (K + 1) := by
  set b := lambertU x with hb
  have hbs := (summable_abs_lambertU hx).of_abs
  -- (a) `∑_{l ≥ 1} (u_{k+l} + u_l u_{k+l}) = u_k (u₁ + ⋯ + u_k)`
  have hK : 0 < (1 - |x|)⁻¹ := inv_pos.2 (by linarith)
  have hbound : ∀ n, |b n| ≤ (1 - |x|)⁻¹ := fun n => by
    refine (abs_lambertU_le' hx n).trans ?_
    calc (1 - |x|)⁻¹ * |x| ^ n ≤ (1 - |x|)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg x) hx.le) hK.le
      _ = (1 - |x|)⁻¹ := mul_one _
  have hs1 : Summable fun l : ℕ => b (l + 1) :=
    hbs.comp_injective (i := fun l => l + 1) (fun a c h => by simpa using h)
  have hs2 : Summable fun n : ℕ => b (n + K + 1) * b n :=
    Summable.of_norm_bounded ((summable_abs_lambertU hx).mul_left (1 - |x|)⁻¹) fun n => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hbound _) (abs_nonneg _)
  have ha : ∑' l : ℕ, b (K + l + 2) + ∑' n : ℕ, b (n + K + 1) * b n =
      b (K + 1) * ∑ i ∈ range (K + 1), b (i + 1) := by
    rw [hs2.tsum_eq_zero_add]
    simp only [zero_add, lambertU_zero, mul_zero, hb]
    have hs3 : Summable fun l : ℕ => b (K + l + 2) :=
      hbs.comp_injective (i := fun l => K + l + 2) (fun a c h => by simp at h; omega)
    have hs4 : Summable fun l : ℕ => b (l + 1 + K + 1) * b (l + 1) :=
      (summable_nat_add_iff (f := fun n : ℕ => b (n + K + 1) * b n) 1).2 hs2
    rw [← Summable.tsum_add hs3 hs4]
    have e : ∀ l : ℕ, b (K + l + 2) + b (l + 1 + K + 1) * b (l + 1) =
        b (K + 1) * (b (l + 1) - b (l + (K + 1) + 1)) := fun l => by
      have := lambertU_add_mul hx (k := K + 1) (l := l + 1) (by omega) (by omega)
      rw [show K + 1 + (l + 1) = K + l + 2 by ring] at this
      rw [show l + 1 + K + 1 = K + l + 2 by ring, show l + (K + 1) + 1 = K + l + 2 by ring]
      linarith
    rw [tsum_congr e, tsum_mul_left]
    congr 1
    have hs5 : Summable fun l : ℕ => b (l + (K + 1) + 1) :=
      (summable_nat_add_iff (f := fun l => b (l + 1)) (K + 1)).2 hs1
    rw [Summable.tsum_sub hs1 hs5, ← (hs1.sum_add_tsum_nat_add (f := fun l => b (l + 1)) (K + 1))]
    ring
  -- (b) `∑_{l=1}^{k-1} u_l u_{k-l} = u_k ((k - 1) + 2(u₁ + ⋯ + u_{k-1}))`
  have hbsum : ∑ p ∈ antidiagonal (K + 1), b p.1 * b p.2 =
      b (K + 1) * (K + 2 * ∑ i ∈ range K, b (i + 1)) := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ', sum_range_succ]
    simp only [hb, lambertU_zero, mul_zero, zero_mul, add_zero, Nat.sub_self]
    have e : ∀ i ∈ range K, b (i + 1) * b (K + 1 - (i + 1)) =
        b (K + 1) * (1 + b (i + 1) + b (K - i)) := by
      intro i hi
      rw [mem_range] at hi
      have := lambertU_mul hx (l := i + 1) (m := K - i) (by omega) (by omega)
      rw [show i + 1 + (K - i) = K + 1 by omega] at this
      rw [show K + 1 - (i + 1) = K - i by omega]
      exact this
    rw [sum_congr rfl e, ← mul_sum, sum_add_distrib, sum_add_distrib]
    have hrefl : ∑ i ∈ range K, b (K - i) = ∑ i ∈ range K, b (i + 1) := by
      rw [← sum_range_reflect (fun j => b (j + 1)) K]
      exact sum_congr rfl fun i hi => by rw [mem_range] at hi; congr 1; omega
    rw [hrefl]
    simp
    ring
  rw [sum_range_succ] at ha
  linear_combination ha - (1 / 2 : ℝ) * hbsum

/-! ### Theorem 383 -/

lemma abs_lambertU_le_const (hx : |x| < 1) (n : ℕ) : |lambertU x n| ≤ (1 - |x|)⁻¹ :=
  (abs_lambertU_le' hx n).trans (by
    have hK : 0 < (1 - |x|)⁻¹ := inv_pos.2 (by linarith)
    calc (1 - |x|)⁻¹ * |x| ^ n ≤ (1 - |x|)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg x) hx.le) hK.le
      _ = (1 - |x|)⁻¹ := mul_one _)

/-- A sequence bounded by a geometric sequence, times a bounded factor, is summable. -/
lemma summable_of_abs_le_geom (hx : |x| < 1) {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ K, |f K| ≤ C * |x| ^ K) : Summable f :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one (abs_nonneg x) hx).mul_left C)
    fun K => by rw [Real.norm_eq_abs]; exact hf K

lemma abs_tsum_tail_le (hx : |x| < 1) (K : ℕ) :
    |∑' l : ℕ, lambertU x (K + l + 2)| ≤ ((1 - |x|)⁻¹ * (1 - |x|)⁻¹) * |x| ^ K := by
  have hK : 0 < (1 - |x|)⁻¹ := inv_pos.2 (by linarith)
  have hs : Summable fun l : ℕ => ‖lambertU x (K + l + 2)‖ :=
    (summable_abs_lambertU hx).comp_injective (i := fun l => K + l + 2)
      (fun a c h => by simp at h; omega)
  have hg : Summable fun l : ℕ => (1 - |x|)⁻¹ * |x| ^ K * |x| ^ l :=
    (summable_geometric_of_lt_one (abs_nonneg x) hx).mul_left _
  have h1 : ‖∑' l : ℕ, lambertU x (K + l + 2)‖ ≤ ∑' l : ℕ, ‖lambertU x (K + l + 2)‖ :=
    norm_tsum_le_tsum_norm hs
  have h2 : ∑' l : ℕ, ‖lambertU x (K + l + 2)‖ ≤ ∑' l : ℕ, (1 - |x|)⁻¹ * |x| ^ K * |x| ^ l := by
    refine hs.tsum_le_tsum (fun l => ?_) hg
    rw [Real.norm_eq_abs]
    refine (abs_lambertU_le' hx _).trans ?_
    rw [mul_assoc, ← pow_add]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (abs_nonneg x) hx.le (by omega)) hK.le
  have h3 : ∑' l : ℕ, (1 - |x|)⁻¹ * |x| ^ K * |x| ^ l = ((1 - |x|)⁻¹ * (1 - |x|)⁻¹) * |x| ^ K := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one (abs_nonneg x) hx]; ring
  rw [← Real.norm_eq_abs]
  linarith

lemma abs_tsum_shift_mul_le (hx : |x| < 1) (K : ℕ) :
    |∑' n : ℕ, lambertU x (n + K + 1) * lambertU x n| ≤
      ((1 - |x|)⁻¹ * ∑' n, |lambertU x n|) * |x| ^ K := by
  have hK : 0 < (1 - |x|)⁻¹ := inv_pos.2 (by linarith)
  have hs : Summable fun n : ℕ => ‖lambertU x (n + K + 1) * lambertU x n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (abs_lambertU_le_const hx _) (abs_nonneg _))
      ((summable_abs_lambertU hx).mul_left (1 - |x|)⁻¹)
  have h1 := norm_tsum_le_tsum_norm hs
  have h2 : ∑' n : ℕ, ‖lambertU x (n + K + 1) * lambertU x n‖ ≤
      ∑' n : ℕ, (1 - |x|)⁻¹ * |x| ^ K * |lambertU x n| := by
    refine hs.tsum_le_tsum (fun n => ?_) ((summable_abs_lambertU hx).mul_left _)
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul_of_nonneg_right ((abs_lambertU_le' hx _).trans ?_) (abs_nonneg _)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (abs_nonneg x) hx.le (by omega)) hK.le
  have h3 : ∑' n : ℕ, (1 - |x|)⁻¹ * |x| ^ K * |lambertU x n| =
      ((1 - |x|)⁻¹ * ∑' n, |lambertU x n|) * |x| ^ K := by rw [tsum_mul_left]; ring
  rw [← Real.norm_eq_abs]
  linarith

lemma summable_cos_mul_of_le_geom (hx : |x| < 1) (θ : ℝ) {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ K, |f K| ≤ C * |x| ^ K) : Summable fun K : ℕ => cos ((K + 1 : ℕ) * θ) * f K :=
  summable_of_abs_le_geom hx fun K => by
    rw [abs_mul]; exact (mul_le_of_le_one_left (abs_nonneg _) (abs_cos_le_one _)).trans (hf K)

lemma summable_cos_mul_antidiagonal (hx : |x| < 1) (θ : ℝ) :
    Summable fun k : ℕ => cos (k * θ) * ∑ p ∈ antidiagonal k, lambertU x p.1 * lambertU x p.2 := by
  have hn : Summable fun n => ‖lambertU x n‖ := by
    simpa [Real.norm_eq_abs] using summable_abs_lambertU hx
  have h := summable_norm_sum_mul_antidiagonal_of_summable_norm hn hn
  refine Summable.of_norm_bounded h fun k => ?_
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (by rw [Real.norm_eq_abs]; exact abs_cos_le_one _)

lemma summable_lambertU_sq (hx : |x| < 1) : Summable fun n : ℕ => lambertU x n ^ 2 :=
  Summable.of_norm_bounded ((summable_abs_lambertU hx).mul_left (1 - |x|)⁻¹) fun n => by
    rw [Real.norm_eq_abs, abs_pow, sq]
    exact mul_le_mul_of_nonneg_right (abs_lambertU_le_const hx n) (abs_nonneg _)

lemma summable_succ_mul_lambertU (hx : |x| < 1) :
    Summable fun K : ℕ => ((K + 1 : ℕ) : ℝ) * lambertU x (K + 1) := by
  have := (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ 1 * |lambertU x n|) 1).2
    (summable_pow_mul_abs_lambertU hx 1)
  refine Summable.of_norm_bounded this fun K => ?_
  rw [Real.norm_eq_abs, abs_mul, pow_one, Nat.abs_cast]

/-- **Theorem 383** (Hardy–Wright). If `|x| < 1` and `θ` is real and not an even multiple of `π`,
`L = ¼ cot ½θ + u₁ sin θ + u₂ sin 2θ + ⋯`, `T₁ = (¼ cot ½θ)² + u₁(1 + u₁) cos θ + u₂(1 + u₂) cos 2θ + ⋯`
and `T₂ = ½{u₁(1 - cos θ) + 2u₂(1 - cos 2θ) + 3u₃(1 - cos 3θ) + ⋯}`, then `L² = T₁ + T₂`. -/
@[kb "hardywright2008" "Thm 383, p. 430"]
theorem cotangent_identity (hx : |x| < 1) {θ : ℝ} (hθ : ∀ k : ℤ, θ ≠ 2 * k * π) :
    (cot (θ / 2) / 4 + ∑' n : ℕ, lambertU x (n + 1) * sin ((n + 1 : ℕ) * θ)) ^ 2 =
      ((cot (θ / 2) / 4) ^ 2 +
        ∑' n : ℕ, lambertU x (n + 1) * (1 + lambertU x (n + 1)) * cos ((n + 1 : ℕ) * θ)) +
      1 / 2 * ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * lambertU x (n + 1) * (1 - cos ((n + 1 : ℕ) * θ)) := by
  have hsin : sin (θ / 2) ≠ 0 := by
    intro h
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.1 h
    exact hθ k (by linarith)
  have hbs : Summable (lambertU x) := (summable_abs_lambertU hx).of_abs
  have hbs1 : Summable fun K : ℕ => lambertU x (K + 1) :=
    (summable_nat_add_iff (f := lambertU x) 1).2 hbs
  have hsumsin : Summable fun n : ℕ => lambertU x n * sin (n * θ) :=
    (summable_lambertU_mul_trig hx fun n => abs_sin_le_one _).of_norm
  have hsumcos : Summable fun n : ℕ => lambertU x n * cos (n * θ) :=
    (summable_lambertU_mul_trig hx fun n => abs_cos_le_one _).of_norm
  have hS : ∑' n : ℕ, lambertU x (n + 1) * sin ((n + 1 : ℕ) * θ) =
      ∑' n : ℕ, lambertU x n * sin (n * θ) := by
    rw [hsumsin.tsum_eq_zero_add]; simp
  rw [hS]
  -- `2cS = ∑ uₙ (½ + cos θ + ⋯ + ½ cos nθ)`
  have h2cS : 2 * (cot (θ / 2) / 4) * ∑' n : ℕ, lambertU x n * sin (n * θ) =
      ∑' n, lambertU x n * halfDirichlet θ n := by
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have := half_cot_mul_sin (φ := θ / 2) hsin hn
      rw [show 2 * (θ / 2) = θ by ring] at this
      rw [← this]; ring
  have hA := tsum_mul_halfDirichlet hx θ
  have hB := sq_tsum_sin hx θ
  -- absolute convergence of the coefficient series
  have hcos_t := summable_cos_mul_of_le_geom hx θ (abs_tsum_tail_le hx)
  have hcos_P := summable_cos_mul_of_le_geom hx θ (abs_tsum_shift_mul_le hx)
  have hcos_A := summable_cos_mul_antidiagonal hx θ
  have hcos_A1 := (summable_nat_add_iff (f := fun k : ℕ => cos (k * θ) *
    ∑ p ∈ antidiagonal k, lambertU x p.1 * lambertU x p.2) 1).2 hcos_A
  have hbc1 := (summable_nat_add_iff (f := fun n : ℕ => lambertU x n * cos (n * θ)) 1).2 hsumcos
  have hb2 := summable_lambertU_sq hx
  have hb21 := (summable_nat_add_iff (f := fun n => lambertU x n ^ 2) 1).2 hb2
  have hKb := summable_succ_mul_lambertU hx
  have hKbc : Summable fun K : ℕ =>
      ((K + 1 : ℕ) : ℝ) * lambertU x (K + 1) * cos ((K + 1 : ℕ) * θ) :=
    Summable.of_norm_bounded hKb.abs fun K => by
      rw [Real.norm_eq_abs, abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)
  -- shift the series from `0` to `1`
  have e1 : ∑' n, lambertU x n = ∑' K : ℕ, lambertU x (K + 1) := by
    rw [hbs.tsum_eq_zero_add]; simp
  have e2 : ∑' n : ℕ, lambertU x n * cos (n * θ) =
      ∑' K : ℕ, lambertU x (K + 1) * cos ((K + 1 : ℕ) * θ) := by
    rw [hsumcos.tsum_eq_zero_add]; simp
  have e3 : ∑' n, lambertU x n ^ 2 = ∑' K : ℕ, lambertU x (K + 1) ^ 2 := by
    rw [hb2.tsum_eq_zero_add]; simp
  have e4 : ∑' k : ℕ, cos (k * θ) * ∑ p ∈ antidiagonal k, lambertU x p.1 * lambertU x p.2 =
      ∑' K : ℕ, cos ((K + 1 : ℕ) * θ) *
        ∑ p ∈ antidiagonal (K + 1), lambertU x p.1 * lambertU x p.2 := by
    rw [hcos_A.tsum_eq_zero_add]; simp
  -- Theorem 381 for the constant term
  have h381 : ∑' K : ℕ, lambertU x (K + 1) + ∑' K : ℕ, lambertU x (K + 1) ^ 2 =
      ∑' K : ℕ, ((K + 1 : ℕ) : ℝ) * lambertU x (K + 1) := by
    rw [← Summable.tsum_add hbs1 hb21]
    have := tsum_lambertU_mul_one_add hx
    rw [show (fun K : ℕ => lambertU x (K + 1) + lambertU x (K + 1) ^ 2) =
      fun K => lambertU x (K + 1) * (1 + lambertU x (K + 1)) by funext K; ring, this]
    exact tsum_congr fun K => by push_cast; ring
  -- the cosine coefficients
  have hcoef : ∑' K : ℕ, lambertU x (K + 1) * cos ((K + 1 : ℕ) * θ) / 2 +
      ∑' K : ℕ, cos ((K + 1 : ℕ) * θ) * ∑' l : ℕ, lambertU x (K + l + 2) +
      ∑' K : ℕ, cos ((K + 1 : ℕ) * θ) * ∑' n : ℕ, lambertU x (n + K + 1) * lambertU x n -
      ∑' K : ℕ, (cos ((K + 1 : ℕ) * θ) *
        ∑ p ∈ antidiagonal (K + 1), lambertU x p.1 * lambertU x p.2) / 2 =
      ∑' K : ℕ, (lambertU x (K + 1) * (1 + lambertU x (K + 1)) * cos ((K + 1 : ℕ) * θ) -
        ((K + 1 : ℕ) : ℝ) * lambertU x (K + 1) * cos ((K + 1 : ℕ) * θ) / 2) := by
    rw [← Summable.tsum_add (hbc1.div_const 2) hcos_t,
      ← Summable.tsum_add ((hbc1.div_const 2).add hcos_t) hcos_P,
      ← Summable.tsum_sub (((hbc1.div_const 2).add hcos_t).add hcos_P) (hcos_A1.div_const 2)]
    refine tsum_congr fun K => ?_
    have := coeff_identity hx K
    push_cast at this ⊢
    linear_combination cos (((K : ℝ) + 1) * θ) * this
  have hT : ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * lambertU x (n + 1) * (1 - cos ((n + 1 : ℕ) * θ)) =
      ∑' K : ℕ, ((K + 1 : ℕ) : ℝ) * lambertU x (K + 1) -
        ∑' K : ℕ, ((K + 1 : ℕ) : ℝ) * lambertU x (K + 1) * cos ((K + 1 : ℕ) * θ) := by
    rw [← Summable.tsum_sub hKb hKbc]; exact tsum_congr fun K => by ring
  have hs : Summable fun n : ℕ =>
      lambertU x (n + 1) * (1 + lambertU x (n + 1)) * cos ((n + 1 : ℕ) * θ) :=
    Summable.of_norm_bounded (hbs1.abs.add hb21.abs) fun n => by
      rw [Real.norm_eq_abs, abs_mul, mul_add, mul_one, ← sq]
      refine (mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)).trans ?_
      exact (abs_add_le _ _).trans (by rw [abs_pow])
  have hR : ∑' K : ℕ, (lambertU x (K + 1) * (1 + lambertU x (K + 1)) * cos ((K + 1 : ℕ) * θ) -
        ((K + 1 : ℕ) : ℝ) * lambertU x (K + 1) * cos ((K + 1 : ℕ) * θ) / 2) =
      ∑' n : ℕ, lambertU x (n + 1) * (1 + lambertU x (n + 1)) * cos ((n + 1 : ℕ) * θ) -
        (∑' K : ℕ, ((K + 1 : ℕ) : ℝ) * lambertU x (K + 1) * cos ((K + 1 : ℕ) * θ)) / 2 := by
    rw [Summable.tsum_sub hs (hKbc.div_const 2), tsum_div_const]
  have hc1 : ∑' K : ℕ, lambertU x (K + 1) * cos ((K + 1 : ℕ) * θ) / 2 =
      (∑' K : ℕ, lambertU x (K + 1) * cos ((K + 1 : ℕ) * θ)) / 2 := tsum_div_const
  have hc2 : ∑' K : ℕ, (cos ((K + 1 : ℕ) * θ) *
        ∑ p ∈ antidiagonal (K + 1), lambertU x p.1 * lambertU x p.2) / 2 =
      (∑' K : ℕ, cos ((K + 1 : ℕ) * θ) *
        ∑ p ∈ antidiagonal (K + 1), lambertU x p.1 * lambertU x p.2) / 2 := tsum_div_const
  rw [add_sq, h2cS, hA, hB, hT, e1, e2, e3, e4]
  linear_combination (1 / 2 : ℝ) * h381 + hcoef + hR - hc1 + hc2
