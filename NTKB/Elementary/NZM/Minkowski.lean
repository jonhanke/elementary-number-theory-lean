/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Attr
import NTKB.Elementary.NZM.GeometryOfNumbers
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Minkowski's theorem and applications (Niven–Zuckerman–Montgomery, §§ 5.5, 6.4)

* Lemma 5.12: a linear congruence `α x + β y + γ z ≡ 0 (mod m)` has a small non-trivial solution
  (pigeonhole).  The book states the bounds as strict inequalities `|x| < λ, |y| < μ, |z| < ν`
  for `λ μ ν = m`; this is false when `λ, μ, ν` are all integers (e.g. `λ = μ = ν = m = 1`).
  We prove the version with non-strict bounds (`lemma_5_12`), and the strict version under the
  hypothesis that not all of `λ, μ, ν` are integers (`lemma_5_12_strict`).
* Theorem 6.25 (Dirichlet): proved in full generality from Mathlib's Minkowski convex body theorem
  applied to the standard lattice `ℤ^{k+1}` and the sheared parallelepiped
  `|u₀| < n + 1`, `|u_i - x_i u₀| < n^{-1/k}`, whose volume is `2^{k+1} (n+1)/n`.
-/

namespace NTKB.NZM

open MeasureTheory Set

/-! ### Lemma 5.12 -/

/-- Pigeonhole core of Lemma 5.12, with integer box sizes. -/
lemma exists_small_solution_congr (a b c m : ℕ) (hm : 0 < m) (hlt : m < a * b * c)
    (α β γ : ℤ) :
    ∃ x y z : ℤ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ |x| < a ∧ |y| < b ∧ |z| < c ∧
      (m : ℤ) ∣ α * x + β * y + γ * z := by
  have : NeZero m := ⟨hm.ne'⟩
  let f : Fin a × Fin b × Fin c → ZMod m := fun p =>
    ((α * (p.1 : ℕ) + β * (p.2.1 : ℕ) + γ * (p.2.2 : ℕ) : ℤ) : ZMod m)
  have hcard : Fintype.card (ZMod m) < Fintype.card (Fin a × Fin b × Fin c) := by
    simpa [ZMod.card, Fintype.card_prod, mul_assoc] using (by rwa [mul_assoc] at hlt)
  obtain ⟨p, q, hne, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  refine ⟨(p.1 : ℕ) - (q.1 : ℕ), (p.2.1 : ℕ) - (q.2.1 : ℕ), (p.2.2 : ℕ) - (q.2.2 : ℕ),
    ?_, ?_, ?_, ?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2, h3⟩ := hcon
    apply hne
    have e1 : p.1 = q.1 := Fin.ext (by omega)
    have e2 : p.2.1 = q.2.1 := Fin.ext (by omega)
    have e3 : p.2.2 = q.2.2 := Fin.ext (by omega)
    exact Prod.ext e1 (Prod.ext e2 e3)
  · have := p.1.isLt; have := q.1.isLt; rw [abs_lt]; constructor <;> omega
  · have := p.2.1.isLt; have := q.2.1.isLt; rw [abs_lt]; constructor <;> omega
  · have := p.2.2.isLt; have := q.2.2.isLt; rw [abs_lt]; constructor <;> omega
  · have h := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hf.symm
    have : α * ((p.1 : ℕ) - (q.1 : ℕ) : ℤ) + β * ((p.2.1 : ℕ) - (q.2.1 : ℕ) : ℤ) +
        γ * ((p.2.2 : ℕ) - (q.2.2 : ℕ) : ℤ) =
        (α * (p.1 : ℕ) + β * (p.2.1 : ℕ) + γ * (p.2.2 : ℕ) : ℤ) -
          (α * (q.1 : ℕ) + β * (q.2.1 : ℕ) + γ * (q.2.2 : ℕ) : ℤ) := by ring
    rw [this]
    exact h

lemma mul_lt_mul_aux {x y z x' y' z' : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x ≤ x') (h2 : y ≤ y') (h3 : z < z') : x * y * z < x' * y' * z' := by
  have hx' : 0 < x' := lt_of_lt_of_le hx h1
  have hy' : 0 < y' := lt_of_lt_of_le hy h2
  have hz' : 0 < z' := lt_trans hz h3
  calc x * y * z < (x * y) * z' := by gcongr
    _ ≤ x' * y' * z' := by gcongr

/-- **Lemma 5.12** (book form with non-strict bounds).  Let `λ, μ, ν` be positive reals whose
product `λ μ ν = m` is an integer.  Then every congruence `α x + β y + γ z ≡ 0 (mod m)` has a
solution `x, y, z`, not all zero, with `|x| ≤ λ`, `|y| ≤ μ`, `|z| ≤ ν`.  (The book writes strict
inequalities, which is false when `λ, μ, ν` are all integers; see `lemma_5_12_strict`.) -/
@[kb "nivenzuckermanmontgomery" "Lemma 5.12, p. 242"]
theorem lemma_5_12 (l μ ν : ℝ) (hl : 0 < l) (hμ : 0 < μ) (hν : 0 < ν) (m : ℕ)
    (hm : l * μ * ν = m) (α β γ : ℤ) :
    ∃ x y z : ℤ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ |(x : ℝ)| ≤ l ∧ |(y : ℝ)| ≤ μ ∧ |(z : ℝ)| ≤ ν ∧
      (m : ℤ) ∣ α * x + β * y + γ * z := by
  have hmpos : (0 : ℝ) < m := by rw [← hm]; positivity
  have hm0 : 0 < m := by exact_mod_cast hmpos
  have h1 := Nat.lt_floor_add_one l
  have h2 := Nat.lt_floor_add_one μ
  have h3 := Nat.lt_floor_add_one ν
  have hlt : m < (⌊l⌋₊ + 1) * (⌊μ⌋₊ + 1) * (⌊ν⌋₊ + 1) := by
    have : (m : ℝ) < ((⌊l⌋₊ + 1 : ℕ) : ℝ) * ((⌊μ⌋₊ + 1 : ℕ) : ℝ) * ((⌊ν⌋₊ + 1 : ℕ) : ℝ) := by
      rw [← hm]
      push_cast
      exact mul_lt_mul_aux hl hμ hν h1.le h2.le h3
    exact_mod_cast this
  obtain ⟨x, y, z, hnz, hx, hy, hz, hd⟩ :=
    exists_small_solution_congr (⌊l⌋₊ + 1) (⌊μ⌋₊ + 1) (⌊ν⌋₊ + 1) m hm0 hlt α β γ
  refine ⟨x, y, z, hnz, ?_, ?_, ?_, hd⟩
  · have : |x| ≤ (⌊l⌋₊ : ℤ) := by push_cast at hx; omega
    have h4 : |(x : ℝ)| ≤ (⌊l⌋₊ : ℝ) := by exact_mod_cast this
    exact h4.trans (Nat.floor_le hl.le)
  · have : |y| ≤ (⌊μ⌋₊ : ℤ) := by push_cast at hy; omega
    have h4 : |(y : ℝ)| ≤ (⌊μ⌋₊ : ℝ) := by exact_mod_cast this
    exact h4.trans (Nat.floor_le hμ.le)
  · have : |z| ≤ (⌊ν⌋₊ : ℤ) := by push_cast at hz; omega
    have h4 : |(z : ℝ)| ≤ (⌊ν⌋₊ : ℝ) := by exact_mod_cast this
    exact h4.trans (Nat.floor_le hν.le)

/-- **Lemma 5.12** (strict form).  If, in addition, not all of `λ, μ, ν` are integers, then the
solution can be taken with the strict bounds `|x| < λ`, `|y| < μ`, `|z| < ν`. -/
@[kb "nivenzuckermanmontgomery" "Lemma 5.12, p. 242"]
theorem lemma_5_12_strict (l μ ν : ℝ) (hl : 0 < l) (hμ : 0 < μ) (hν : 0 < ν) (m : ℕ)
    (hm : l * μ * ν = m)
    (hint : l ∉ Set.range ((↑) : ℤ → ℝ) ∨ μ ∉ Set.range ((↑) : ℤ → ℝ) ∨
      ν ∉ Set.range ((↑) : ℤ → ℝ))
    (α β γ : ℤ) :
    ∃ x y z : ℤ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ |(x : ℝ)| < l ∧ |(y : ℝ)| < μ ∧ |(z : ℝ)| < ν ∧
      (m : ℤ) ∣ α * x + β * y + γ * z := by
  have hmpos : (0 : ℝ) < m := by rw [← hm]; positivity
  have hm0 : 0 < m := by exact_mod_cast hmpos
  have h1 := Nat.le_ceil l
  have h2 := Nat.le_ceil μ
  have h3 := Nat.le_ceil ν
  have strict : ∀ t : ℝ, t ∉ Set.range ((↑) : ℤ → ℝ) → t < ⌈t⌉₊ := by
    intro t ht
    refine lt_of_le_of_ne (Nat.le_ceil t) fun h => ht ⟨(⌈t⌉₊ : ℤ), ?_⟩
    rw [h]
    simp
  have hlt : m < ⌈l⌉₊ * ⌈μ⌉₊ * ⌈ν⌉₊ := by
    have : (m : ℝ) < (⌈l⌉₊ : ℝ) * (⌈μ⌉₊ : ℝ) * (⌈ν⌉₊ : ℝ) := by
      rw [← hm]
      rcases hint with h | h | h
      · have := mul_lt_mul_aux hμ hν hl h2 h3 (strict l h)
        linarith
      · have := mul_lt_mul_aux hl hν hμ h1 h3 (strict μ h)
        linarith
      · exact mul_lt_mul_aux hl hμ hν h1 h2 (strict ν h)
    exact_mod_cast this
  obtain ⟨x, y, z, hnz, hx, hy, hz, hd⟩ :=
    exists_small_solution_congr ⌈l⌉₊ ⌈μ⌉₊ ⌈ν⌉₊ m hm0 hlt α β γ
  have key : ∀ (t : ℝ) (w : ℤ), 0 < t → |w| < (⌈t⌉₊ : ℤ) → |(w : ℝ)| < t := by
    intro t w ht hw
    have h5 : |w| + 1 ≤ (⌈t⌉₊ : ℤ) := by omega
    have h6 : (|(w : ℝ)|) + 1 ≤ (⌈t⌉₊ : ℝ) := by exact_mod_cast h5
    have h7 := Nat.ceil_lt_add_one ht.le
    linarith
  exact ⟨x, y, z, hnz, key l x hl hx, key μ y hμ hy, key ν z hν hz, hd⟩

/-! ### Theorem 6.25 -/

/-- The vector `(0, x_1, …, x_k)`. -/
def shearVec {k : ℕ} (x : Fin k → ℝ) : Fin (k + 1) → ℝ := Fin.cons (α := fun _ => ℝ) 0 x

@[simp] lemma shearVec_zero {k : ℕ} (x : Fin k → ℝ) : shearVec x 0 = 0 := by
  simp [shearVec]

@[simp] lemma shearVec_succ {k : ℕ} (x : Fin k → ℝ) (i : Fin k) : shearVec x i.succ = x i := by
  simp [shearVec]

/-- The matrix of the shear `u ↦ (u_0, u_i - x_i u_0)`. -/
noncomputable def shearMatrix {k : ℕ} (x : Fin k → ℝ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  Matrix.of fun i j => (if i = j then 1 else 0) - (if j = 0 then shearVec x i else 0)

/-- The shear `u ↦ (u_0, u_i - x_i u_0)` as a linear map. -/
noncomputable def shearMap {k : ℕ} (x : Fin k → ℝ) : (Fin (k + 1) → ℝ) →ₗ[ℝ] (Fin (k + 1) → ℝ) :=
  Matrix.toLin' (shearMatrix x)

lemma shearMap_apply {k : ℕ} (x : Fin k → ℝ) (u : Fin (k + 1) → ℝ) (i : Fin (k + 1)) :
    shearMap x u i = u i - shearVec x i * u 0 := by
  simp [shearMap, shearMatrix, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, sub_mul,
    Finset.sum_sub_distrib, ite_mul]

lemma det_shearMap {k : ℕ} (x : Fin k → ℝ) : LinearMap.det (shearMap x) = 1 := by
  rw [shearMap, LinearMap.det_toLin']
  have htri : (shearMatrix x).IsLowerTriangular := by
    intro i j hij
    have hij' : i < j := hij
    have hj : j ≠ 0 := by
      intro h
      subst h
      exact absurd hij' (by simp)
    have hne : i ≠ j := hij'.ne
    simp [shearMatrix, hne, hj]
  rw [Matrix.det_of_isLowerTriangular _ htri]
  refine Finset.prod_eq_one fun i _ => ?_
  by_cases hi : i = 0
  · subst hi
    simp [shearMatrix]
  · simp [shearMatrix, hi]

/-- Minkowski step of Theorem 6.25: a nonzero integer vector `u` with `|u_0| < n + 1` and
`|u_i - x_i u_0| < 1/n^{1/k}`. -/
lemma exists_int_vector_shear {k : ℕ} (hk : 0 < k) (x : Fin k → ℝ) (n : ℕ) (hn : 0 < n) :
    ∃ u : Fin (k + 1) → ℤ, u ≠ 0 ∧ |(u 0 : ℝ)| < n + 1 ∧
      ∀ i : Fin k, |(u i.succ : ℝ) - x i * u 0| < 1 / (n : ℝ) ^ (1 / (k : ℝ)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hρpos : 0 < (n : ℝ) ^ (1 / (k : ℝ)) := Real.rpow_pos_of_pos hn' _
  have hρk : ((n : ℝ) ^ (1 / (k : ℝ))) ^ k = n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn'.le]
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have : (1 / (k : ℝ)) * k = 1 := by field_simp
    rw [this, Real.rpow_one]
  generalize (n : ℝ) ^ (1 / (k : ℝ)) = ρ at hρpos hρk ⊢
  let r : Fin (k + 1) → ℝ := Fin.cons (α := fun _ => ℝ) ((n : ℝ) + 1) (fun _ => 1 / ρ)
  let B : Set (Fin (k + 1) → ℝ) := Set.pi univ fun i => Ioo (-r i) (r i)
  let S : Set (Fin (k + 1) → ℝ) := shearMap x ⁻¹' B
  let b := Pi.basisFun ℝ (Fin (k + 1))
  let L : AddSubgroup (Fin (k + 1) → ℝ) := (Submodule.span ℤ (Set.range b)).toAddSubgroup
  have hF := ZSpan.isAddFundamentalDomain' b (volume : Measure (Fin (k + 1) → ℝ))
  have hFvol : volume (ZSpan.fundamentalDomain b) = 1 := by
    have h1 : Matrix.of ⇑b = 1 := by
      ext i j
      simp [b, Pi.single_apply, Matrix.one_apply, eq_comm]
    rw [ZSpan.volume_fundamentalDomain, h1]
    simp
  have hvolB : volume B = ENNReal.ofReal (2 * ((n : ℝ) + 1) * (2 / ρ) ^ k) := by
    simp only [B, Real.volume_pi_Ioo, Fin.prod_univ_succ]
    simp only [r, Fin.cons_zero, Fin.cons_succ, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity)]
    congr 3 <;> ring
  have hconv : Convex ℝ S :=
    (convex_pi fun i _ => convex_Ioo (-r i) (r i)).linear_preimage (shearMap x)
  have hsymm : ∀ v ∈ S, -v ∈ S := by
    intro v hv
    simp only [S, B, mem_preimage, Set.mem_pi, mem_univ, mem_Ioo, true_implies,
      map_neg, Pi.neg_apply] at hv ⊢
    intro i
    obtain ⟨h1, h2⟩ := hv i
    constructor <;> linarith
  have hvol : volume (ZSpan.fundamentalDomain b) * 2 ^ Module.finrank ℝ (Fin (k + 1) → ℝ) <
      volume S := by
    simp only [S]
    rw [Measure.addHaar_preimage_linearMap volume (by rw [det_shearMap]; norm_num),
      det_shearMap, hvolB, hFvol]
    simp only [inv_one, abs_one, ENNReal.ofReal_one, one_mul, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin]
    have h2 : (2 : ENNReal) ^ (k + 1) = ENNReal.ofReal (2 ^ (k + 1)) := by
      rw [ENNReal.ofReal_pow (by norm_num)]
      simp
    rw [h2, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    rw [div_pow, hρk]
    have h3 : 2 * ((n : ℝ) + 1) * (2 ^ k / n) = 2 ^ (k + 1) * (((n : ℝ) + 1) / n) := by
      field_simp
      ring
    rw [h3]
    refine lt_mul_of_one_lt_right (by positivity) ?_
    rw [one_lt_div hn']
    exact lt_add_one _
  have : Countable L := by
    change Countable (Submodule.span ℤ (Set.range b))
    infer_instance
  obtain ⟨v, hv0, hvS⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (μ := volume) (L := L) hF hsymm hconv hvol
  have hvL : ((v : L) : Fin (k + 1) → ℝ) ∈ Submodule.span ℤ (Set.range b) := v.2
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hvL
  have hcoord : ∀ j, ((v : L) : Fin (k + 1) → ℝ) j = (c j : ℝ) := by
    intro j
    rw [← hc]
    simp [b, Finset.sum_apply, Pi.single_apply]
  refine ⟨c, ?_, ?_, ?_⟩
  · intro hc0
    apply hv0
    apply Subtype.ext
    funext j
    rw [hcoord j, hc0]
    simp
  · have h0 := (Set.mem_pi.1 (show shearMap x ((v : L) : Fin (k + 1) → ℝ) ∈ B from hvS))
      0 (mem_univ _)
    simp only [shearMap_apply, shearVec_zero, hcoord, r, Fin.cons_zero, mem_Ioo] at h0
    rw [abs_lt]
    constructor <;> linarith [h0.1, h0.2]
  · intro i
    have h1 := (Set.mem_pi.1 (show shearMap x ((v : L) : Fin (k + 1) → ℝ) ∈ B from hvS))
      i.succ (mem_univ _)
    simp only [shearMap_apply, shearVec_succ, hcoord, r, Fin.cons_succ, mem_Ioo] at h1
    rw [abs_lt]
    constructor <;> linarith [h1.1, h1.2]

/-- **Theorem 6.25** (Dirichlet; the book's proof via Minkowski's convex body theorem).  For reals
`x_1, …, x_k` and a positive integer `n` there are integers `a_i`, `b` with `0 < b ≤ n` and
`|x_i - a_i/b| < 1/(b n^{1/k})`. -/
@[kb "nivenzuckermanmontgomery" "Thm 6.25, p. 316"]
theorem simultaneous_approximation_general (k : ℕ) (x : Fin k → ℝ) (n : ℕ) (hn : 0 < n) :
    ∃ (a : Fin k → ℤ) (b : ℕ), 0 < b ∧ b ≤ n ∧
      ∀ i, |x i - (a i : ℝ) / b| < 1 / ((b : ℝ) * (n : ℝ) ^ (1 / (k : ℝ))) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨fun i => i.elim0, 1, one_pos, hn, fun i => i.elim0⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hρpos : 0 < (n : ℝ) ^ (1 / (k : ℝ)) := Real.rpow_pos_of_pos hn' _
  have hρ1 : 1 ≤ (n : ℝ) ^ (1 / (k : ℝ)) :=
    Real.one_le_rpow (by exact_mod_cast hn) (by positivity)
  generalize hρ : (n : ℝ) ^ (1 / (k : ℝ)) = ρ at hρpos hρ1
  obtain ⟨u, hu0, hu1, hu2⟩ := exists_int_vector_shear hk x n hn
  rw [hρ] at hu2
  -- the vector `u` has `u 0 ≠ 0`
  have hne : u 0 ≠ 0 := by
    intro h0
    apply hu0
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simpa using h0
    · have := hu2 i
      rw [h0] at this
      simp only [Int.cast_zero, mul_zero, sub_zero] at this
      have h1 : 1 / ρ ≤ 1 := by rw [div_le_one hρpos]; exact hρ1
      have h2 : |(u i.succ : ℝ)| < 1 := lt_of_lt_of_le this h1
      have h3 : |u i.succ| < 1 := by exact_mod_cast h2
      have h4 := abs_lt.1 h3
      simp only [Pi.zero_apply]
      omega
  -- reduce to `u 0 > 0`
  have main : ∀ u : Fin (k + 1) → ℤ, 0 < u 0 → |(u 0 : ℝ)| < n + 1 →
      (∀ i : Fin k, |(u i.succ : ℝ) - x i * u 0| < 1 / ρ) →
      ∃ (a : Fin k → ℤ) (b : ℕ), 0 < b ∧ b ≤ n ∧
        ∀ i, |x i - (a i : ℝ) / b| < 1 / ((b : ℝ) * ρ) := by
    intro u hpos h1 h2
    refine ⟨fun i => u i.succ, (u 0).toNat, by omega, ?_, fun i => ?_⟩
    · have h3 : |u 0| < (n : ℤ) + 1 := by exact_mod_cast h1
      rw [abs_of_pos hpos] at h3
      omega
    · have hb : ((u 0).toNat : ℝ) = (u 0 : ℝ) := by
        have : ((u 0).toNat : ℤ) = u 0 := Int.toNat_of_nonneg hpos.le
        exact_mod_cast this
      rw [hb]
      have hbpos : (0 : ℝ) < (u 0 : ℝ) := by exact_mod_cast hpos
      have h4 : x i - (u i.succ : ℝ) / (u 0 : ℝ) = -((u i.succ : ℝ) - x i * u 0) / (u 0 : ℝ) := by
        field_simp
        ring
      rw [h4, abs_div, abs_neg, abs_of_pos hbpos, div_lt_iff₀ hbpos]
      calc _ < 1 / ρ := h2 i
        _ = 1 / ((u 0 : ℝ) * ρ) * (u 0 : ℝ) := by field_simp
  rcases lt_or_gt_of_ne hne with h | h
  · refine main (-u) (by simpa using h) (by simpa using hu1) fun i => ?_
    have := hu2 i
    simp only [Pi.neg_apply, Int.cast_neg]
    rw [show -(u i.succ : ℝ) - x i * -(u 0 : ℝ) = -((u i.succ : ℝ) - x i * u 0) by ring, abs_neg]
    exact this
  · exact main u h hu1 hu2

/-- **Theorem 6.25** (Dirichlet), the full book statement `SimultaneousApproximationStatement`. -/
@[kb "nivenzuckermanmontgomery" "Thm 6.25, p. 316"]
theorem simultaneousApproximationStatement : SimultaneousApproximationStatement :=
  fun k x n hn => simultaneous_approximation_general k x n hn

end NTKB.NZM
