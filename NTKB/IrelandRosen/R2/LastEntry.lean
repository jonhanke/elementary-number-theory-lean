/-
Ireland–Rosen, Chapter 11, §5: the last entry of Gauss's diary. For `q ≡ 1 (mod 4)` the projective
curve `x²t² + y²t² + x²y² - t⁴ = 0` has `q - 1 - 2a` points, where `π = -J(ρ, χ) = a + bi`
(`ρ` quadratic, `χ` quartic), and `π ≡ 1 (mod 2 + 2i)`. For `q = p` prime this is the book's
Theorem: `p = a² + b²`, `a` odd, `b` even, `a ≡ 1 (mod 4)` iff `4 ∣ b`.

Coordinates on `P²` are `(t, x, y)`, so that `t = 0` is the line at infinity of
`NTKB.IrelandRosen.IsAtInfinity`.
-/
import NTKB.IrelandRosen.R2.Cubic
import NTKB.IrelandRosen.R2.AffineProjective

open Finset Complex
open scoped Classical LinearAlgebra.Projectivization

set_option linter.unusedSectionVars false

namespace NTKB.IrelandRosen

variable {F : Type*} [Field F] [Fintype F]

/-! ### The affine curves `C₁ : x² + y² + x²y² = 1` and `C₂ : w² + z⁴ = 1` -/

/-- The number of points of `x² + y² + x²y² = 1` in `F²`. -/
noncomputable def numC1 (F : Type*) [Field F] [Fintype F] : ℕ :=
  #{p : F × F | p.1 ^ 2 + p.2 ^ 2 + p.1 ^ 2 * p.2 ^ 2 = 1}

/-- `N(C₂) = N(C₁) + #{z : z² = -1}`, by the maps `(x, y) ↦ (x, (1 + x²)y)` and
`(z, w) ↦ (z, w / (1 + z²))` of the book (§11.5). -/
lemma numSolDiag_two_four_eq (hF : ringChar F ≠ 2) :
    numSolDiag ![(1 : F), 1] ![2, 4] 1 = numC1 F + numSolPow 2 (-1 : F) := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  unfold numSolDiag numC1 numSolPow
  rw [← Finset.card_filter_add_card_filter_not (p := fun v : Fin 2 → F => v 1 ^ 2 = -1),
    Finset.filter_filter, Finset.filter_filter]
  have hv : ∀ v : Fin 2 → F, ∑ i, ![(1 : F), 1] i * v i ^ (![2, 4] : Fin 2 → ℕ) i =
      v 0 ^ 2 + v 1 ^ 4 := by
    intro v; simp [Fin.sum_univ_two]
  simp_rw [hv]
  rw [add_comm]
  congr 1
  · -- the points with `z² ≠ -1` correspond to `C₁`
    refine Finset.card_nbij' (fun v => (v 1, v 0 / (1 + v 1 ^ 2)))
      (fun p => ![(1 + p.1 ^ 2) * p.2, p.1]) ?_ ?_ ?_ ?_
    · intro v hv
      simp only [mem_coe, mem_filter, mem_univ, true_and] at hv ⊢
      obtain ⟨h1, h2'⟩ := hv
      have hz : 1 + v 1 ^ 2 ≠ 0 := by
        intro h; apply h2'; linear_combination h
      field_simp
      linear_combination (1 + v 1 ^ 2) * h1
    · intro p hp
      simp only [mem_coe, mem_filter, mem_univ, true_and] at hp ⊢
      have hx : 1 + p.1 ^ 2 ≠ 0 := by
        intro h
        have : p.1 ^ 2 = -1 := by linear_combination h
        rw [this] at hp
        apply h2; linear_combination -hp
      refine ⟨?_, ?_⟩
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        linear_combination (1 + p.1 ^ 2) * hp
      · simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
        intro h; apply hx; linear_combination h
    · intro v hv
      simp only [mem_coe, mem_filter, mem_univ, true_and] at hv
      have hz : 1 + v 1 ^ 2 ≠ 0 := by
        intro h; apply hv.2; linear_combination h
      ext i; fin_cases i <;> simp [hz] <;> field_simp
    · intro p hp
      simp only [mem_coe, mem_filter, mem_univ, true_and] at hp
      have hx : 1 + p.1 ^ 2 ≠ 0 := by
        intro h
        have : p.1 ^ 2 = -1 := by linear_combination h
        rw [this] at hp
        apply h2; linear_combination -hp
      ext <;> simp [hx]
  · -- the points with `z² = -1` are the `(0, z)`
    refine Finset.card_nbij' (fun v => v 1) (fun z => ![0, z]) ?_ ?_ ?_ ?_
    · intro v hv
      simp only [mem_coe, mem_filter, mem_univ, true_and] at hv ⊢
      exact hv.2
    · intro z hz
      simp only [mem_coe, mem_filter, mem_univ, true_and] at hz ⊢
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      refine ⟨?_, hz⟩
      rw [show z ^ 4 = (z ^ 2) ^ 2 by ring, hz]; ring
    · intro v hv
      simp only [mem_coe, mem_filter, mem_univ, true_and] at hv
      have h0 : v 0 ^ 2 = 0 := by
        have : v 1 ^ 4 = 1 := by rw [show v 1 ^ 4 = (v 1 ^ 2) ^ 2 by ring, hv.2]; ring
        linear_combination hv.1 - this
      have : v 0 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h0
      ext i; fin_cases i <;> simp [this]
    · intro z _; simp

/-! ### `N(w² + z⁴ = 1)` by Jacobi sums -/

lemma multiJacobiSum_pair_conj (χ φ : MulChar F ℂ) :
    multiJacobiSum ![χ⁻¹, φ⁻¹] = starRingEnd ℂ (multiJacobiSum ![χ, φ]) := by
  rw [multiJacobiSum_pair, multiJacobiSum_pair, map_sum]
  simp [bookChar_inv]

/-- `N(w² + z⁴ = 1) = q - 1 + 2 Re J(ρ, χ)` for `χ` of order `4` and `ρ = χ²`. -/
theorem numSolDiag_two_four (h4 : 4 ∣ Fintype.card F - 1) {χ : MulChar F ℂ}
    (hχ : orderOf χ = 4) :
    (numSolDiag ![(1 : F), 1] ![2, 4] 1 : ℂ) =
      Fintype.card F - 1 + 2 * (multiJacobiSum ![χ ^ 2, χ]).re := by
  have hρ : orderOf (χ ^ 2) = 2 := by
    rw [orderOf_pow' χ (by norm_num), hχ]; norm_num
  have h2 : 2 ∣ Fintype.card F - 1 := (by norm_num : 2 ∣ 4).trans h4
  have hsum : (numSolDiag ![(1 : F), 1] ![2, 4] 1 : ℂ) =
      ∑ i ∈ range 2, ∑ j ∈ range 4, multiJacobiSum ![(χ ^ 2) ^ i, χ ^ j] := by
    rw [numSolDiag_eq_sum]
    have hv : ∀ v : Fin 2 → F, ∑ i, ![(1 : F), 1] i * v i = ∑ i, v i := by
      intro v; simp [Fin.sum_univ_two]
    simp_rw [hv]
    rw [sum_filter_pair]
    push_cast
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    simp_rw [numSolPow_eq_sum_range h2 hρ, numSolPow_eq_sum_range h4 hχ, multiJacobiSum_pair,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
  have hne : ∀ j, 0 < j → j < 4 → χ ^ j ≠ 1 := by
    intro j hj0 hj4 h
    have := orderOf_le_of_pow_eq_one hj0 h
    omega
  have h1 : χ ≠ 1 := by simpa using hne 1 (by norm_num) (by norm_num)
  have h2' := hne 2 (by norm_num) (by norm_num)
  have h3 := hne 3 (by norm_num) (by norm_num)
  have hχ4 : χ ^ 4 = 1 := by rw [← hχ]; exact pow_orderOf_eq_one χ
  have hρinv : (χ ^ 2)⁻¹ = χ ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_add]; exact hχ4
  have hχ3 : χ ^ 3 = χ⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ]; exact hχ4
  have hρm1 : (χ ^ 2) (-1) = 1 := by
    rw [MulChar.pow_apply' χ two_ne_zero, sq, mulChar_neg_one_sq]
  rw [hsum]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, pow_zero,
    pow_one, one_pow]
  rw [multiJacobiSum_pair_one_one, multiJacobiSum_pair_one_left h1,
    multiJacobiSum_pair_one_left h2', multiJacobiSum_pair_one_left h3,
    multiJacobiSum_pair_one_right h2']
  have hJ2 : multiJacobiSum ![χ ^ 2, χ ^ 2] = -1 := by
    conv_lhs => rw [show (![χ ^ 2, χ ^ 2] : Fin 2 → MulChar F ℂ) = ![χ ^ 2, (χ ^ 2)⁻¹] by
      rw [hρinv]]
    rw [multiJacobiSum_pair_inv h2', hρm1]
  have hJ3 : multiJacobiSum ![χ ^ 2, χ ^ 3] = starRingEnd ℂ (multiJacobiSum ![χ ^ 2, χ]) := by
    rw [← multiJacobiSum_pair_conj, hρinv, hχ3]
  rw [hJ2, hJ3]
  have hc := Complex.add_conj (multiJacobiSum ![χ ^ 2, χ])
  push_cast at hc
  linear_combination hc

/-! ### `J(ρ, χ)` is a Gaussian integer congruent to `-q` modulo `2 + 2i` -/

lemma exists_eq_add_mul_I {z : ℂ} (hz : z ∈ Algebra.adjoin ℤ ({I} : Set ℂ)) :
    ∃ c d : ℤ, z = c + d * I := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.mp hx]; exact ⟨0, 1, by simp⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx; obtain ⟨c, d, rfl⟩ := hy
    exact ⟨a + c, b + d, by push_cast; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx; obtain ⟨c, d, rfl⟩ := hy
    exact ⟨a * c - b * d, a * d + b * c, by push_cast; linear_combination (b * d : ℂ) * I_sq⟩

/-- Divisibility by `2 + 2i` in `ℤ[i]`. -/
def DvdTwoTwoI (z : ℂ) : Prop := ∃ c d : ℤ, z = (c + d * I) * (2 + 2 * I)

lemma dvdTwoTwoI_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, DvdTwoTwoI (f i)) :
    DvdTwoTwoI (∑ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty => exact ⟨0, 0, by simp⟩
  | cons j s hj ih =>
    rw [sum_cons]
    obtain ⟨a, b, hab⟩ := h j (mem_cons_self j s)
    obtain ⟨c, d, hcd⟩ := ih fun i hi => h i (mem_cons_of_mem hi)
    exact ⟨a + c, b + d, by rw [hab, hcd]; push_cast; ring⟩

lemma fourth_roots {z : ℂ} (hz : z ^ 4 = 1) : z = 1 ∨ z = -1 ∨ z = I ∨ z = -I := by
  have : (z - 1) * (z + 1) * (z - I) * (z + I) = 0 := by
    linear_combination hz + (1 - z ^ 2) * I_sq
  rcases mul_eq_zero.mp this with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · left; linear_combination h
      · right; left; linear_combination h
    · right; right; left; linear_combination h
  · right; right; right; linear_combination h

lemma square_roots {z : ℂ} (hz : z ^ 2 = 1) : z = 1 ∨ z = -1 := by
  have : (z - 1) * (z + 1) = 0 := by linear_combination hz
  rcases mul_eq_zero.mp this with h | h
  · left; linear_combination h
  · right; linear_combination h

/-- **The congruence of Hasse–Davenport** used in §11.5: `J(ρ, χ) + q ≡ 0 (mod 2 + 2i)`. -/
theorem dvdTwoTwoI_jacobiSum_add_card {χ : MulChar F ℂ}
    (hχ : orderOf χ = 4) : DvdTwoTwoI (multiJacobiSum ![χ ^ 2, χ] + Fintype.card F) := by
  have hχ4 : χ ^ 4 = 1 := by rw [← hχ]; exact pow_orderOf_eq_one χ
  have h1 : χ ≠ 1 := by rintro rfl; simp at hχ
  have h2 : χ ^ 2 ≠ 1 := by
    intro h; have := orderOf_le_of_pow_eq_one (by norm_num) h; omega
  have hexp : multiJacobiSum ![χ ^ 2, χ] + Fintype.card F =
      ∑ x : F, ((χ ^ 2) x - 1) * (χ (1 - x) - 1) := by
    rw [multiJacobiSum_pair]
    simp only [bookChar_of_ne_one h1, bookChar_of_ne_one h2]
    have hs1 : ∑ x : F, (χ ^ 2) x = 0 := MulChar.sum_eq_zero_of_ne_one h2
    have hs2 : ∑ x : F, χ (1 - x) = 0 := by
      rw [← MulChar.sum_eq_zero_of_ne_one h1]
      exact Fintype.sum_equiv (Equiv.subLeft 1) _ _ (fun x => rfl)
    have : ∑ x : F, ((χ ^ 2) x - 1) * (χ (1 - x) - 1) =
        ∑ x : F, (χ ^ 2) x * χ (1 - x) - ∑ x : F, (χ ^ 2) x - ∑ x : F, χ (1 - x) +
          Fintype.card F := by
      simp only [sub_mul, mul_sub, mul_one, one_mul, Finset.sum_sub_distrib, sum_const,
        card_univ, nsmul_eq_mul]
      ring
    rw [this, hs1, hs2]; ring
  rw [hexp]
  refine dvdTwoTwoI_sum _ _ fun x _ => ?_
  by_cases hx0 : x = 0
  · subst hx0; exact ⟨0, 0, by simp⟩
  by_cases hx1 : x = 1
  · subst hx1; exact ⟨0, 0, by simp⟩
  have hy : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  have hρx : ((χ ^ 2) x) ^ 2 = 1 := by
    rw [← MulChar.pow_apply' _ two_ne_zero, ← pow_mul, hχ4, MulChar.one_apply (Ne.isUnit hx0)]
  have hχy : (χ (1 - x)) ^ 4 = 1 := by
    rw [← MulChar.pow_apply' _ (by norm_num), hχ4, MulChar.one_apply (Ne.isUnit hy)]
  rcases square_roots hρx with hr | hr <;> rw [hr]
  · exact ⟨0, 0, by simp⟩
  · rcases fourth_roots hχy with hc | hc | hc | hc <;> rw [hc]
    · exact ⟨0, 0, by simp⟩
    · exact ⟨1, -1, by push_cast; linear_combination (2 : ℂ) * I_sq⟩
    · exact ⟨0, -1, by push_cast; linear_combination (2 : ℂ) * I_sq⟩
    · exact ⟨1, 0, by push_cast; ring⟩

/-! ### The projective curve `x²t² + y²t² + x²y² - t⁴ = 0` -/

/-- `x²t² + y²t² + x²y² - t⁴` in the coordinates `v = (t, x, y)`. -/
def lastEntryForm (v : Fin 3 → F) : F :=
  v 1 ^ 2 * v 0 ^ 2 + v 2 ^ 2 * v 0 ^ 2 + v 1 ^ 2 * v 2 ^ 2 - v 0 ^ 4

/-- The number of points of `x²t² + y²t² + x²y² - t⁴ = 0` in `P²(F)`. -/
noncomputable def numLastEntry (F : Type*) [Field F] [Fintype F] : ℕ :=
  Nat.card {P : ℙ F (Fin 3 → F) // lastEntryForm P.rep = 0}

lemma lastEntryForm_smul (c : F) (v : Fin 3 → F) :
    lastEntryForm (c • v) = c ^ 4 * lastEntryForm v := by
  simp [lastEntryForm]; ring

/-- The curve has the two points `[0, 1, 0]`, `[0, 0, 1]` at infinity (`t = 0`); the finite points
are those of `C₁`. -/
theorem numLastEntry_eq : numLastEntry F = numC1 F + 2 := by
  haveI : Fintype (ℙ F (Fin 3 → F)) := Fintype.ofFinite _
  rw [numLastEntry, Nat.card_eq_fintype_card, Fintype.card_subtype,
    ← Finset.card_filter_add_card_filter_not (p := fun P : ℙ F (Fin 3 → F) => IsAtInfinity P),
    Finset.filter_filter, Finset.filter_filter, add_comm]
  have key : ∀ (P : ℙ F (Fin 3 → F)) (v : Fin 3 → F) (c : F), c ≠ 0 → P.rep = c • v →
      (lastEntryForm P.rep = 0 ↔ lastEntryForm v = 0) := by
    intro P v c hc h
    rw [h, lastEntryForm_smul]
    exact ⟨fun h' => (mul_eq_zero.mp h').resolve_left (pow_ne_zero _ hc),
      fun h' => by rw [h', mul_zero]⟩
  congr 1
  · -- finite points
    unfold numC1
    refine Finset.card_nbij' (fun P => (projToAffine P 0, projToAffine P 1))
      (fun p => affineToProj ![p.1, p.2]) ?_ ?_ ?_ ?_
    · intro P hP
      simp only [mem_coe, mem_filter, mem_univ, true_and] at hP ⊢
      obtain ⟨hG, hinf⟩ := hP
      have h1 := affineToProj_projToAffine P hinf
      obtain ⟨c, hc, hrep⟩ := rep_affineToProj (projToAffine P)
      rw [h1] at hrep
      rw [key P _ c hc hrep] at hG
      simp only [lastEntryForm, Fin.cons_zero, Fin.cons_succ, one_pow, mul_one] at hG
      have e1 : (Fin.cons 1 (projToAffine P) : Fin 3 → F) 1 = projToAffine P 0 := rfl
      have e2 : (Fin.cons 1 (projToAffine P) : Fin 3 → F) 2 = projToAffine P 1 := rfl
      rw [e1, e2] at hG
      linear_combination hG
    · intro p hp
      simp only [mem_coe, mem_filter, mem_univ, true_and] at hp ⊢
      refine ⟨?_, not_isAtInfinity_affineToProj _⟩
      obtain ⟨c, hc, hrep⟩ := rep_affineToProj ![p.1, p.2]
      rw [key _ _ c hc hrep]
      simp only [lastEntryForm]
      have e0 : (Fin.cons 1 ![p.1, p.2] : Fin 3 → F) 0 = 1 := rfl
      have e1 : (Fin.cons 1 ![p.1, p.2] : Fin 3 → F) 1 = p.1 := rfl
      have e2 : (Fin.cons 1 ![p.1, p.2] : Fin 3 → F) 2 = p.2 := rfl
      rw [e0, e1, e2]
      linear_combination hp
    · intro P hP
      simp only [mem_coe, mem_filter, mem_univ, true_and] at hP
      have : ![projToAffine P 0, projToAffine P 1] = projToAffine P := by
        ext i; fin_cases i <;> rfl
      simp only
      rw [this, affineToProj_projToAffine P hP.2]
    · intro p _
      simp only [projToAffine_affineToProj]
      rfl
  · -- points at infinity
    have hv1 : (![0, 1, 0] : Fin 3 → F) ≠ 0 := fun h => by
      have := congrFun h 1; simp at this
    have hv2 : (![0, 0, 1] : Fin 3 → F) ≠ 0 := fun h => by
      have := congrFun h 2; simp at this
    have hfilt : ({P : ℙ F (Fin 3 → F) | lastEntryForm P.rep = 0 ∧ IsAtInfinity P} : Finset _) =
        {Projectivization.mk F _ hv1, Projectivization.mk F _ hv2} := by
      ext P
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hG, hinf⟩
        unfold IsAtInfinity at hinf
        simp only [lastEntryForm, hinf] at hG
        have hxy : P.rep 1 ^ 2 * P.rep 2 ^ 2 = 0 := by linear_combination hG
        rcases mul_eq_zero.mp hxy with h | h
        · have h1 : P.rep 1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp h
          have h2 : P.rep 2 ≠ 0 := by
            intro h2; apply P.rep_ne_zero
            ext i; fin_cases i <;> simp [hinf, h1, h2]
          right
          conv_lhs => rw [← Projectivization.mk_rep P]
          rw [Projectivization.mk_eq_mk_iff']
          refine ⟨P.rep 2, ?_⟩
          ext i; fin_cases i <;> simp [hinf, h1]
        · have h2 : P.rep 2 = 0 := pow_eq_zero_iff two_ne_zero |>.mp h
          have h1 : P.rep 1 ≠ 0 := by
            intro h1; apply P.rep_ne_zero
            ext i; fin_cases i <;> simp [hinf, h1, h2]
          left
          conv_lhs => rw [← Projectivization.mk_rep P]
          rw [Projectivization.mk_eq_mk_iff']
          refine ⟨P.rep 1, ?_⟩
          ext i; fin_cases i <;> simp [hinf, h2]
      · rintro (rfl | rfl)
        · obtain ⟨c, hc, h⟩ := rep_mk_eq (F := F) _ hv1
          refine ⟨?_, ?_⟩
          · rw [h, lastEntryForm_smul]; simp [lastEntryForm]
          · unfold IsAtInfinity; rw [h]; simp
        · obtain ⟨c, hc, h⟩ := rep_mk_eq (F := F) _ hv2
          refine ⟨?_, ?_⟩
          · rw [h, lastEntryForm_smul]; simp [lastEntryForm]
          · unfold IsAtInfinity; rw [h]; simp
    rw [hfilt, Finset.card_pair]
    intro h
    rw [Projectivization.mk_eq_mk_iff'] at h
    obtain ⟨a, ha⟩ := h
    have := congrFun ha 1
    simp at this

/-- `N(x² = -1) = 2` when `q ≡ 1 (mod 4)`. -/
lemma numSolPow_two_neg_one (h4 : 4 ∣ Fintype.card F - 1) {χ : MulChar F ℂ}
    (hχ : orderOf χ = 4) : numSolPow 2 (-1 : F) = 2 := by
  have hρ : orderOf (χ ^ 2) = 2 := by
    rw [orderOf_pow' χ (by norm_num), hχ]; norm_num
  have h2 : 2 ∣ Fintype.card F - 1 := (by norm_num : 2 ∣ 4).trans h4
  have h := numSolPow_eq_sum_range h2 hρ (-1 : F)
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, pow_zero,
    pow_one, bookChar_one] at h
  rw [bookChar_of_ne_zero _ (neg_ne_zero.mpr one_ne_zero), MulChar.pow_apply' χ two_ne_zero, sq,
    mulChar_neg_one_sq] at h
  have : ((numSolPow 2 (-1 : F) : ℕ) : ℂ) = ((2 : ℕ) : ℂ) := by rw [h]; norm_num
  exact_mod_cast this

lemma ringChar_ne_two_of_four_dvd (h4 : 4 ∣ Fintype.card F - 1) : ringChar F ≠ 2 := by
  intro h
  have := FiniteField.even_card_iff_char_two.mp h
  have hq := Fintype.one_lt_card (α := F)
  omega

/-- **The point count of §11.5 over any finite field with `q ≡ 1 (mod 4)`**: with `χ` of order `4`,
`ρ = χ²` and `π = -J(ρ, χ) = a + bi`, the curve has `q - 1 - 2a` points in `P²(F)`; moreover
`q = a² + b²` and `π ≡ 1 (mod 2 + 2i)`. -/
theorem numLastEntry_eq_of_quartic (h4 : 4 ∣ Fintype.card F - 1) {χ : MulChar F ℂ}
    (hχ : orderOf χ = 4) :
    ∃ a b : ℤ, -multiJacobiSum ![χ ^ 2, χ] = a + b * I ∧ (Fintype.card F : ℤ) = a ^ 2 + b ^ 2 ∧
      DvdTwoTwoI ((a + b * I) - 1) ∧ (numLastEntry F : ℤ) = Fintype.card F - 1 - 2 * a := by
  have hχ4 : χ ^ 4 = 1 := by rw [← hχ]; exact pow_orderOf_eq_one χ
  have h1 : χ ≠ 1 := by rintro rfl; simp at hχ
  have h2 : χ ^ 2 ≠ 1 := by
    intro h; have := orderOf_le_of_pow_eq_one (by norm_num) h; omega
  have h3 : χ ^ 2 * χ ≠ 1 := by
    rw [← pow_succ]; intro h; have := orderOf_le_of_pow_eq_one (by norm_num) h; omega
  -- `J(ρ, χ) ∈ ℤ[i]`
  have hmem : multiJacobiSum ![χ ^ 2, χ] ∈ Algebra.adjoin ℤ ({I} : Set ℂ) := by
    rw [multiJacobiSum_two h2 h1]
    exact jacobiSum_mem_algebraAdjoin_of_pow_eq_one (n := 4)
      (by rw [← pow_mul]; norm_num [hχ4]; rw [show 8 = 4 * 2 by rfl, pow_mul, hχ4, one_pow])
      hχ4 Complex.isPrimitiveRoot_I
  obtain ⟨A, B, hAB⟩ := exists_eq_add_mul_I hmem
  refine ⟨-A, -B, by rw [hAB]; push_cast; ring, ?_, ?_, ?_⟩
  · -- `|J|² = q`
    have hne : ∀ k : Fin 2, ![χ ^ 2, χ] k ≠ 1 := by
      intro k; fin_cases k
      · simpa using h2
      · simpa using h1
    have hprod : ∏ k, ![χ ^ 2, χ] k ≠ 1 := by
      rw [Fin.prod_univ_two]; simpa using h3
    have hn := norm_multiJacobiSum (r := 1) hne hprod
    rw [pow_one] at hn
    have := congrArg (· ^ 2) hn
    rw [← Complex.normSq_eq_norm_sq, hAB, Real.sq_sqrt (by positivity), Complex.normSq_apply] at this
    simp at this
    have : (Fintype.card F : ℝ) = (-A : ℤ) ^ 2 + (-B : ℤ) ^ 2 := by push_cast; linarith
    exact_mod_cast this
  · obtain ⟨c, d, hcd⟩ := dvdTwoTwoI_jacobiSum_add_card hχ
    obtain ⟨k, hk⟩ := h4
    refine ⟨-c + k, -d - k, ?_⟩
    have hq : (Fintype.card F : ℂ) = 4 * k + 1 := by
      have : Fintype.card F = 4 * k + 1 := by have := Fintype.one_lt_card (α := F); omega
      rw [this]; push_cast; ring
    rw [hAB, hq] at hcd
    push_cast
    linear_combination -hcd + (2 * k : ℂ) * I_sq
  · have hN2 := numSolDiag_two_four h4 hχ
    have hN := numSolDiag_two_four_eq (ringChar_ne_two_of_four_dvd h4)
    rw [numSolPow_two_neg_one h4 hχ] at hN
    have hre : (multiJacobiSum ![χ ^ 2, χ]).re = A := by rw [hAB]; simp
    rw [hN, hre] at hN2
    rw [numLastEntry_eq]
    have : ((numC1 F + 2 : ℕ) : ℂ) = (((Fintype.card F : ℤ) - 1 - 2 * (-A)) : ℤ) := by
      push_cast at hN2 ⊢; linear_combination hN2
    exact_mod_cast this

/-- **Lemma of §11.5.** If `a + bi ≡ 1 (mod 2 + 2i)`, then `a` is odd, `b` is even, and
`a ≡ 1 (mod 4)` if `4 ∣ b`, `a ≡ -1 (mod 4)` if `4 ∤ b`. -/
@[kb "irelandrosen1990" "Lemma (§11.5), p. 177"]
theorem lastEntry_lemma {a b : ℤ} (h : DvdTwoTwoI ((a + b * I) - 1)) :
    Odd a ∧ Even b ∧ (4 ∣ b → a ≡ 1 [ZMOD 4]) ∧ (¬4 ∣ b → a ≡ -1 [ZMOD 4]) := by
  obtain ⟨c, d, hcd⟩ := h
  have hre := congrArg Complex.re hcd
  have him := congrArg Complex.im hcd
  simp at hre him
  have e1 : a - 1 = 2 * c - 2 * d := by exact_mod_cast (by linarith : (a : ℝ) - 1 = 2 * c - 2 * d)
  have e2 : b = 2 * c + 2 * d := by exact_mod_cast (by linarith : (b : ℝ) = 2 * c + 2 * d)
  refine ⟨⟨c - d, by omega⟩, ⟨c + d, by omega⟩, fun h4 => ?_, fun h4 => ?_⟩
  · unfold Int.ModEq; omega
  · unfold Int.ModEq; omega

/-- Uniqueness of the representation of a prime as a sum of two squares, up to order and signs. -/
theorem sq_eq_sq_of_prime_eq_sq_add_sq {p : ℕ} (hp : p.Prime) {a b c d : ℤ}
    (h1 : (p : ℤ) = a ^ 2 + b ^ 2) (h2 : (p : ℤ) = c ^ 2 + d ^ 2) :
    (a ^ 2 = c ^ 2 ∧ b ^ 2 = d ^ 2) ∨ (a ^ 2 = d ^ 2 ∧ b ^ 2 = c ^ 2) := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have key : ∀ d' : ℤ, (p : ℤ) = c ^ 2 + d' ^ 2 → (p : ℤ) ∣ a * d' - b * c →
      (a ^ 2 = c ^ 2 ∧ b ^ 2 = d' ^ 2) ∨ (a ^ 2 = d' ^ 2 ∧ b ^ 2 = c ^ 2) := by
    intro d' h2' hdvd
    have hid : (p : ℤ) ^ 2 = (a * c + b * d') ^ 2 + (a * d' - b * c) ^ 2 := by
      rw [sq (p : ℤ)]; nth_rewrite 1 [h1]; rw [h2']; ring
    obtain ⟨k, hk⟩ := hdvd
    rw [hk] at hid
    have hk2 : k ^ 2 ≤ 1 := by
      by_contra hcon
      push Not at hcon
      have h2k : 2 ≤ k ^ 2 := by omega
      have hpk : (p : ℤ) ^ 2 * 2 ≤ (p * k) ^ 2 := by
        rw [mul_pow]; exact mul_le_mul_of_nonneg_left h2k (sq_nonneg _)
      have hp2 : 0 < (p : ℤ) ^ 2 := by positivity
      nlinarith [sq_nonneg (a * c + b * d')]
    have hkr : k = 0 ∨ k ^ 2 = 1 := by
      have h1' : -1 ≤ k := by nlinarith
      have h2' : k ≤ 1 := by nlinarith
      interval_cases k <;> simp
    rcases hkr with hk0' | hk1
    · left
      rw [hk0', mul_zero] at hk
      have hbd : b ^ 2 = d' ^ 2 := by
        have e1 : (p : ℤ) * d' ^ 2 = p * b ^ 2 := by
          nth_rewrite 1 [h1]; rw [h2']
          have : a * d' = b * c := by linarith
          linear_combination (a * d' + b * c) * this
        exact (mul_left_cancel₀ hp0.ne' e1).symm
      refine ⟨?_, hbd⟩
      have : (p : ℤ) - b ^ 2 = p - d' ^ 2 := by rw [hbd]
      linarith
    · right
      have hX : a * c + b * d' = 0 := by
        have : (a * c + b * d') ^ 2 = 0 := by rw [mul_pow, hk1, mul_one] at hid; linarith
        exact pow_eq_zero_iff two_ne_zero |>.mp this
      have hbc : b ^ 2 = c ^ 2 := by
        have e1 : (p : ℤ) * c ^ 2 = p * b ^ 2 := by
          nth_rewrite 1 [h1]; rw [h2']
          have : a * c = -(b * d') := by linarith
          linear_combination (a * c - b * d') * this
        exact (mul_left_cancel₀ hp0.ne' e1).symm
      refine ⟨?_, hbc⟩
      have : (p : ℤ) - b ^ 2 = p - c ^ 2 := by rw [hbc]
      linarith
  have hprod : (p : ℤ) ∣ (a * d - b * c) * (a * (-d) - b * c) := by
    refine ⟨-(d ^ 2 - b ^ 2), ?_⟩
    have : (a * d - b * c) * (a * (-d) - b * c) = -(a ^ 2 * d ^ 2 - b ^ 2 * c ^ 2) := by ring
    rw [this]
    have : a ^ 2 * d ^ 2 - b ^ 2 * c ^ 2 = (a ^ 2 + b ^ 2) * d ^ 2 - b ^ 2 * (c ^ 2 + d ^ 2) := by
      ring
    rw [this, ← h1, ← h2]; ring
  rcases hpZ.dvd_or_dvd hprod with h | h
  · exact key d h2 h
  · have := key (-d) (by rw [h2]; ring) h
    simpa using this

/-- The normalization of §11.5 (`p = a² + b²`, `a` odd, `b` even, `a ≡ 1 (mod 4)` iff `4 ∣ b`)
determines `a`. -/
theorem lastEntry_normalized_unique {p : ℕ} (hp : p.Prime) {a b a' b' : ℤ}
    (hq : (p : ℤ) = a ^ 2 + b ^ 2) (hao : Odd a) (h4b : 4 ∣ b → a ≡ 1 [ZMOD 4])
    (h4b' : ¬4 ∣ b → a ≡ -1 [ZMOD 4]) (hq' : (p : ℤ) = a' ^ 2 + b' ^ 2) (hbe' : Even b')
    (h4b1 : 4 ∣ b' → a' ≡ 1 [ZMOD 4]) (h4b1' : ¬4 ∣ b' → a' ≡ -1 [ZMOD 4]) : a' = a := by
  rcases sq_eq_sq_of_prime_eq_sq_add_sq hp hq hq' with ⟨ha, hb⟩ | ⟨ha, _⟩
  · rcases sq_eq_sq_iff_eq_or_eq_neg.mp ha.symm with h | h
    · exact h
    · exfalso
      subst h
      have hb4 : 4 ∣ b ↔ 4 ∣ b' := by
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hb with h' | h'
        · rw [h']
        · rw [h', Int.dvd_neg]
      obtain ⟨k, hk⟩ := hao
      by_cases hb0 : 4 ∣ b
      · have e1 := h4b hb0
        have e2 := h4b1 (hb4.mp hb0)
        unfold Int.ModEq at e1 e2; omega
      · have e1 := h4b' hb0
        have e2 := h4b1' (fun h => hb0 (hb4.mpr h))
        unfold Int.ModEq at e1 e2; omega
  · exfalso
    obtain ⟨k, hk⟩ := hao
    obtain ⟨l, hl⟩ := hbe'
    subst hk hl
    have : (2 * k + 1) ^ 2 % 2 = (l + l) ^ 2 % 2 := by rw [ha]
    ring_nf at this
    omega

/-- **Gauss's last entry** (Theorem of §11.5). Let `p ≡ 1 (mod 4)` be prime and write
`p = a² + b²` with `a` odd, `b` even, `a ≡ 1 (mod 4)` if `4 ∣ b` and `a ≡ -1 (mod 4)` if `4 ∤ b`
(this determines `a`). Then the curve `x²t² + y²t² + x²y² - t⁴ = 0` has `p - 1 - 2a` points in
`P²(𝔽_p)`. -/
@[kb "irelandrosen1990" "Theorem (§11.5), p. 177"]
theorem gauss_last_entry {p : ℕ} [Fact p.Prime] (hp : p % 4 = 1) :
    ∃ a b : ℤ, (p : ℤ) = a ^ 2 + b ^ 2 ∧ Odd a ∧ Even b ∧ (4 ∣ b → a ≡ 1 [ZMOD 4]) ∧
      (¬4 ∣ b → a ≡ -1 [ZMOD 4]) ∧
      (∀ a' b' : ℤ, (p : ℤ) = a' ^ 2 + b' ^ 2 → Odd a' → Even b' →
        (4 ∣ b' → a' ≡ 1 [ZMOD 4]) → (¬4 ∣ b' → a' ≡ -1 [ZMOD 4]) → a' = a) ∧
      (numLastEntry (ZMod p) : ℤ) = p - 1 - 2 * a := by
  have h4 : 4 ∣ Fintype.card (ZMod p) - 1 := by rw [ZMod.card]; omega
  obtain ⟨χ, hχ⟩ := exists_orderOf_eq h4
  obtain ⟨a, b, -, hq, hcong, hN⟩ := numLastEntry_eq_of_quartic h4 hχ
  rw [ZMod.card] at hq hN
  obtain ⟨hao, hbe, h4b, h4b'⟩ := lastEntry_lemma hcong
  exact ⟨a, b, hq, hao, hbe, h4b, h4b', fun a' b' hq' _ hbe' h4b1 h4b1' =>
    lastEntry_normalized_unique Fact.out hq hao h4b h4b' hq' hbe' h4b1 h4b1', hN⟩

end NTKB.IrelandRosen
