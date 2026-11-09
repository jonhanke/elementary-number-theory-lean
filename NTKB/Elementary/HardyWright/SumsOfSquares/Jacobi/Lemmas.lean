/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.ArithmeticFunctions.SumTwoSquaresOrder

/-!
# Hardy–Wright, § 20.11: lemmas for the third proof of Theorem 369

For `|x| < 1` write `u_r = x^r/(1 - x^r)` (`lambertU x r`; `u_0 = 0` by Lean's convention
`a/0 = 0`, and only `r ≥ 1` occurs in the statements), so that `x^r/(1 - x^r)² = u_r(1 + u_r)`.

* Theorem 381: `∑_{m ≥ 1} u_m(1 + u_m) = ∑_{n ≥ 1} n u_n` (`tsum_lambertU_mul_one_add`).
* Theorem 382: `∑_{m ≥ 1} (-1)^(m-1) u_{2m}(1 + u_{2m}) = ∑_{n ≥ 1} (2n - 1) u_{4n-2}`
  (`tsum_neg_one_pow_lambertU`).

The series are absolutely convergent for `|x| < 1` and are rearranged as double series, as in the
book.
-/

open Finset Filter Topology

namespace NTKB.HardyWright

/-- `u_r = x^r/(1 - x^r)` (Hardy–Wright § 20.11). -/
noncomputable def lambertU (x : ℝ) (r : ℕ) : ℝ := x ^ r / (1 - x ^ r)

@[simp] lemma lambertU_zero (x : ℝ) : lambertU x 0 = 0 := by simp [lambertU]

variable {x : ℝ}

lemma abs_pow_lt_one (hx : |x| < 1) {n : ℕ} (hn : n ≠ 0) : |x ^ n| < 1 := by
  rw [abs_pow]; exact pow_lt_one₀ (abs_nonneg x) hx hn

lemma one_sub_pow_pos (hx : |x| < 1) {n : ℕ} (hn : n ≠ 0) : 0 < 1 - x ^ n := by
  have := abs_pow_lt_one hx hn
  have := le_abs_self (x ^ n)
  linarith

lemma abs_lambertU_le (hx : |x| < 1) (n : ℕ) : |lambertU x n| ≤ |x| ^ n / (1 - |x|) := by
  have h1 : 0 < 1 - |x| := by linarith
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [lambertU_zero, abs_zero, pow_zero]; exact div_nonneg zero_le_one h1.le
  have hpos := one_sub_pow_pos hx hn.ne'
  rw [lambertU, abs_div, abs_of_pos hpos, abs_pow]
  have h2 : 1 - |x| ≤ 1 - x ^ n := by
    have : x ^ n ≤ |x| ^ n := by rw [← abs_pow]; exact le_abs_self _
    have : |x| ^ n ≤ |x| := pow_le_of_le_one (abs_nonneg x) hx.le hn.ne'
    linarith
  exact div_le_div_of_nonneg_left (by positivity) h1 h2

/-- `u_n = ∑_{r ≥ 1} x^{nr}`. -/
lemma hasSum_lambertU (hx : |x| < 1) {n : ℕ} (hn : n ≠ 0) :
    HasSum (fun r : ℕ => x ^ (n * (r + 1))) (lambertU x n) := by
  have h := (hasSum_geometric_of_abs_lt_one (abs_pow_lt_one hx hn)).mul_left (x ^ n)
  rw [lambertU, div_eq_mul_inv]
  exact h.congr_fun fun r => by rw [← pow_succ', ← pow_mul]

/-- `u_n (1 + u_n) = x^n/(1 - x^n)² = ∑_{r ≥ 1} r x^{nr}`. -/
lemma hasSum_lambertU_mul_one_add (hx : |x| < 1) {n : ℕ} (hn : n ≠ 0) :
    HasSum (fun r : ℕ => ((r : ℝ) + 1) * x ^ (n * (r + 1))) (lambertU x n * (1 + lambertU x n)) := by
  have hy := abs_pow_lt_one hx hn
  have h := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := x ^ n) (by rwa [Real.norm_eq_abs])
  rw [← hasSum_nat_add_iff' 1] at h
  simp only [range_one, sum_singleton, Nat.cast_zero, zero_mul, sub_zero] at h
  have hpos := one_sub_pow_pos hx hn
  have e : lambertU x n * (1 + lambertU x n) = x ^ n / (1 - x ^ n) ^ 2 := by
    rw [lambertU]; field_simp; ring
  rw [e]
  exact h.congr_fun fun r => by push_cast; rw [← pow_mul]

lemma summable_lambertU_bound (hx : |x| < 1) (p : ℕ) :
    Summable fun n : ℕ => (n : ℝ) ^ p * (|x| ^ n / (1 - |x|)) := by
  have := (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) p (r := |x|)
    (by rwa [Real.norm_eq_abs, abs_abs])).div_const (1 - |x|)
  exact this.congr fun n => by ring

/-- `∑ nᵖ |u_n|` converges for `|x| < 1`. -/
lemma summable_pow_mul_abs_lambertU (hx : |x| < 1) (p : ℕ) :
    Summable fun n : ℕ => (n : ℝ) ^ p * |lambertU x n| :=
  (summable_lambertU_bound hx p).of_nonneg_of_le (fun n => by positivity)
    fun n => mul_le_mul_of_nonneg_left (abs_lambertU_le hx n) (by positivity)

lemma summable_abs_lambertU (hx : |x| < 1) : Summable fun n : ℕ => |lambertU x n| := by
  simpa using summable_pow_mul_abs_lambertU hx 0

/-- The double series `∑_{m, r ≥ 1} ε_m r x^{c m r}` (indices shifted to start at `0`, `|ε_m| ≤ 1`)
converges absolutely: `|r x^{c(m+1)(r+1)}| ≤ (r + 1)|x|^{r+1} · |x|^m`. -/
lemma summable_uncurry_lambert (hx : |x| < 1) {c : ℕ} (hc : c ≠ 0) (ε : ℕ → ℝ)
    (hε : ∀ m, |ε m| ≤ 1) :
    Summable (Function.uncurry fun (m r : ℕ) => ε m * ((r : ℝ) + 1) * x ^ (c * (m + 1) * (r + 1))) := by
  have h0 : 0 ≤ |x| := abs_nonneg x
  have hg1 : Summable fun m : ℕ => |x| ^ m := summable_geometric_of_lt_one h0 hx
  have hg2 : Summable fun r : ℕ => ((r : ℝ) + 1) * |x| ^ (r + 1) := by
    have := (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := |x|)
      (by rwa [Real.norm_eq_abs, abs_abs]))
    have h' := (summable_nat_add_iff 1).2 this
    exact h'.congr fun r => by push_cast; ring
  have hprod := Summable.mul_of_nonneg hg1 hg2 (fun m => by positivity) (fun r => by positivity)
  refine Summable.of_norm_bounded hprod fun p => ?_
  obtain ⟨m, r⟩ := p
  simp only [Function.uncurry_apply_pair, Real.norm_eq_abs, abs_mul, abs_pow]
  have hr : |(r : ℝ) + 1| = (r : ℝ) + 1 := abs_of_nonneg (by positivity)
  rw [hr]
  have hexp : m + (r + 1) ≤ c * (m + 1) * (r + 1) := by
    calc m + (r + 1) ≤ (m + 1) * (r + 1) := by nlinarith
      _ ≤ c * ((m + 1) * (r + 1)) := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hc)
      _ = c * (m + 1) * (r + 1) := by ring
  have hpow : |x| ^ (c * (m + 1) * (r + 1)) ≤ |x| ^ m * |x| ^ (r + 1) := by
    rw [← pow_add]; exact pow_le_pow_of_le_one h0 hx.le hexp
  calc |ε m| * ((r : ℝ) + 1) * |x| ^ (c * (m + 1) * (r + 1))
      ≤ 1 * ((r : ℝ) + 1) * (|x| ^ m * |x| ^ (r + 1)) := by gcongr; exact hε m
    _ = |x| ^ m * (((r : ℝ) + 1) * |x| ^ (r + 1)) := by ring

/-- **Theorem 381** (Hardy–Wright). For `|x| < 1`, `∑_{m ≥ 1} u_m(1 + u_m) = ∑_{n ≥ 1} n u_n`. -/
@[kb "hardywright2008" "Thm 381, p. 429"]
theorem tsum_lambertU_mul_one_add (hx : |x| < 1) :
    ∑' m : ℕ, lambertU x (m + 1) * (1 + lambertU x (m + 1)) =
      ∑' n : ℕ, ((n : ℝ) + 1) * lambertU x (n + 1) := by
  set F : ℕ → ℕ → ℝ := fun m r => 1 * ((r : ℝ) + 1) * x ^ (1 * (m + 1) * (r + 1)) with hF
  have hs := summable_uncurry_lambert hx one_ne_zero (fun _ => 1) (fun _ => by simp)
  have hrow : ∀ m, ∑' r, F m r = lambertU x (m + 1) * (1 + lambertU x (m + 1)) := fun m =>
    ((hasSum_lambertU_mul_one_add hx (Nat.succ_ne_zero m)).congr_fun fun r => by
      simp only [hF, one_mul]).tsum_eq
  have hcol : ∀ r, ∑' m, F m r = ((r : ℝ) + 1) * lambertU x (r + 1) := fun r =>
    (((hasSum_lambertU hx (Nat.succ_ne_zero r)).mul_left ((r : ℝ) + 1)).congr_fun fun m => by
      simp only [hF, one_mul]; rw [show (m + 1) * (r + 1) = (r + 1) * (m + 1) by ring]).tsum_eq
  have htc : ∑' r, ∑' m, F m r = ∑' m, ∑' r, F m r := hs.tsum_comm
  rw [← tsum_congr hrow, ← tsum_congr hcol]
  exact htc.symm

/-- `y/(1 + y) = y/(1 - y) - 2y²/(1 - y²)`, the last step of the proof of Theorem 382. -/
lemma div_one_add_eq {y : ℝ} (hy : |y| < 1) : y / (1 + y) = y / (1 - y) - 2 * (y ^ 2 / (1 - y ^ 2)) := by
  have h1 : 0 < 1 - y := by have := le_abs_self y; linarith
  have h2 : 0 < 1 + y := by have := neg_abs_le y; linarith
  have h3 : 1 - y ^ 2 = (1 - y) * (1 + y) := by ring
  rw [h3]; field_simp; ring

lemma summable_mul_lambertU_mul (hx : |x| < 1) (c : ℕ) (hc : 0 < c) :
    Summable fun r : ℕ => ((r : ℝ) + 1) * lambertU x (c * (r + 1)) := by
  have h1 := summable_pow_mul_abs_lambertU hx 1
  have h2 := (h1.comp_injective (i := fun r : ℕ => c * (r + 1))
    (fun a b h => by simp at h; omega))
  refine Summable.of_norm_bounded h2 fun r => ?_
  simp only [Function.comp, Real.norm_eq_abs, abs_mul, pow_one]
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (r : ℝ) + 1)]
  gcongr
  push_cast
  nlinarith [show (1 : ℝ) ≤ c by exact_mod_cast hc]

/-- **Theorem 382** (Hardy–Wright). For `|x| < 1`,
`∑_{m ≥ 1} (-1)^(m-1) u_{2m}(1 + u_{2m}) = ∑_{n ≥ 1} (2n - 1) u_{4n-2}`. -/
@[kb "hardywright2008" "Thm 382, p. 430"]
theorem tsum_neg_one_pow_lambertU (hx : |x| < 1) :
    ∑' m : ℕ, (-1 : ℝ) ^ m * (lambertU x (2 * (m + 1)) * (1 + lambertU x (2 * (m + 1)))) =
      ∑' n : ℕ, (2 * (n : ℝ) + 1) * lambertU x (4 * n + 2) := by
  set F : ℕ → ℕ → ℝ := fun m r => (-1 : ℝ) ^ m * ((r : ℝ) + 1) * x ^ (2 * (m + 1) * (r + 1)) with hF
  have hs := summable_uncurry_lambert hx two_ne_zero (fun m => (-1 : ℝ) ^ m)
    (fun m => by simp)
  have hrow : ∀ m, ∑' r, F m r =
      (-1 : ℝ) ^ m * (lambertU x (2 * (m + 1)) * (1 + lambertU x (2 * (m + 1)))) := fun m => by
    rw [← ((hasSum_lambertU_mul_one_add hx (by omega : 2 * (m + 1) ≠ 0)).mul_left
      ((-1 : ℝ) ^ m)).tsum_eq]
    exact tsum_congr fun r => by simp only [hF]; ring
  -- the column sums: `r ∑_m (-1)^(m-1) x^{2mr} = r x^{2r}/(1 + x^{2r})`
  have hcol : ∀ r, ∑' m, F m r = ((r : ℝ) + 1) * (x ^ (2 * (r + 1)) / (1 + x ^ (2 * (r + 1)))) := by
    intro r
    have hy := abs_pow_lt_one hx (by omega : 2 * (r + 1) ≠ 0)
    have hy' : |-(x ^ (2 * (r + 1)))| < 1 := by rwa [abs_neg]
    have h := ((hasSum_geometric_of_abs_lt_one hy').mul_left (x ^ (2 * (r + 1)))).mul_left
      ((r : ℝ) + 1)
    have e : ((r : ℝ) + 1) * (x ^ (2 * (r + 1)) / (1 + x ^ (2 * (r + 1)))) =
        ((r : ℝ) + 1) * (x ^ (2 * (r + 1)) * (1 - -x ^ (2 * (r + 1)))⁻¹) := by
      rw [sub_neg_eq_add, div_eq_mul_inv]
    rw [e, ← h.tsum_eq]
    refine tsum_congr fun m => ?_
    simp only [hF]
    rw [show 2 * (m + 1) * (r + 1) = 2 * (r + 1) * (m + 1) by ring, pow_mul, neg_pow, pow_succ]
    ring
  have htc : ∑' r, ∑' m, F m r = ∑' m, ∑' r, F m r := hs.tsum_comm
  rw [← tsum_congr hrow, ← htc, tsum_congr hcol]
  -- `r y/(1 + y) = r u_{2r} - 2r u_{4r}`
  have hsplit : ∀ r : ℕ, ((r : ℝ) + 1) * (x ^ (2 * (r + 1)) / (1 + x ^ (2 * (r + 1)))) =
      ((r : ℝ) + 1) * lambertU x (2 * (r + 1)) - 2 * ((r : ℝ) + 1) * lambertU x (4 * (r + 1)) := by
    intro r
    rw [div_one_add_eq (abs_pow_lt_one hx (by omega)), lambertU, lambertU,
      show 4 * (r + 1) = 2 * (2 * (r + 1)) by ring, pow_mul' x 2 (2 * (r + 1))]
    ring
  rw [tsum_congr hsplit]
  -- summability of the two pieces
  have hb2 := summable_mul_lambertU_mul hx 2 (by norm_num)
  have hb4 := (summable_mul_lambertU_mul hx 4 (by norm_num)).mul_left 2
  rw [Summable.tsum_sub hb2 (hb4.congr fun r => by ring)]
  -- split the first sum by the parity of `r + 1`
  set f : ℕ → ℝ := fun r => ((r : ℝ) + 1) * lambertU x (2 * (r + 1)) with hf
  have heven : Summable fun k => f (2 * k) :=
    hb2.comp_injective (i := fun k => 2 * k) (fun a b h => by simp at h; omega)
  have hodd : Summable fun k => f (2 * k + 1) :=
    hb2.comp_injective (i := fun k => 2 * k + 1) (fun a b h => by simp at h; omega)
  rw [← tsum_even_add_odd heven hodd]
  have e1 : ∀ k : ℕ, f (2 * k) = (2 * (k : ℝ) + 1) * lambertU x (4 * k + 2) := fun k => by
    simp only [hf]; push_cast; rw [show 2 * (2 * k + 1) = 4 * k + 2 by ring]
  have e2 : ∀ k : ℕ, f (2 * k + 1) = 2 * ((k : ℝ) + 1) * lambertU x (4 * (k + 1)) := fun k => by
    simp only [hf]; push_cast; rw [show 2 * (2 * k + 1 + 1) = 4 * (k + 1) by ring]; ring
  rw [tsum_congr e1, tsum_congr e2]
  ring

end NTKB.HardyWright
