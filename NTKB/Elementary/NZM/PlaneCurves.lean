/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import NTKB.Attr

/-!
# Plane curves (Niven–Zuckerman–Montgomery, §§ 5.6–5.7)

Plane curves `f(x, y) = 0` with `f ∈ MvPolynomial (Fin 2) K`, `K` a field.

* **Theorem 5.15** (`plane_curve_line_dvd`): a nonvertical line `y = m x + r` meeting the curve in
  more than `d = totalDegree f` points lies on the curve, and `y - m x - r` divides `f`, with
  cofactor over the same field `K` (so the cofactor is rational when `f`, `m`, `r` are).
* Definitions: restriction of `f` to a line (`lineRestrict`), intersection multiplicity
  (`intersectionMultiplicity`), singular / simple points (`IsSingularPoint`, `IsSimplePoint`),
  inflection points (`IsInflectionPoint`), multiplicity of a point (`HasMultiplicity`), ordinary
  double points (`IsOrdinaryDoublePoint`), absolute irreducibility (`IsAbsolutelyIrreducible`).
* **Theorem 5.16**: the cubic `x^3 + y^3 = 9` has infinitely many rational points
  (`infinite_rational_points_cube_sum_nine`), via the tangent recurrence of the book.
* **Theorem 5.22**: change of the zero of the chord-and-tangent group (`shiftEquiv_add`), proved
  for an arbitrary abelian group, in particular for `WeierstrassCurve.Affine.Point`.
-/

open Polynomial

namespace NTKB.NZM

section Lines

variable {K : Type*} [Field K]

/-- The one-variable polynomial `f(x, m x + r)`: the restriction of `f` to the line `y = m x + r`. -/
noncomputable def lineRestrict (f : MvPolynomial (Fin 2) K) (m r : K) : K[X] :=
  MvPolynomial.aeval ![(Polynomial.X : K[X]), C m * Polynomial.X + C r] f

theorem natDegree_aeval_le {σ : Type*} (g : σ → K[X]) (hg : ∀ i, (g i).natDegree ≤ 1)
    (f : MvPolynomial σ K) : (MvPolynomial.aeval g f).natDegree ≤ f.totalDegree := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  refine natDegree_mul_le.trans ?_
  have h1 : (algebraMap K K[X] (f.coeff d)).natDegree = 0 := by
    rw [Polynomial.algebraMap_apply]; simp
  rw [h1, zero_add]
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ i ∈ d.support, (g i ^ d i).natDegree ≤ ∑ i ∈ d.support, d i :=
        Finset.sum_le_sum fun i _ =>
          natDegree_pow_le.trans ((Nat.mul_le_mul_left _ (hg i)).trans (by simp))
    _ ≤ f.totalDegree := MvPolynomial.le_totalDegree hd

theorem natDegree_lineRestrict_le (f : MvPolynomial (Fin 2) K) (m r : K) :
    (lineRestrict f m r).natDegree ≤ f.totalDegree := by
  apply natDegree_aeval_le
  intro i
  fin_cases i
  · simpa using natDegree_X_le
  · simpa using natDegree_linear_le (a := m) (b := r)

theorem eval_lineRestrict (f : MvPolynomial (Fin 2) K) (m r x : K) :
    (lineRestrict f m r).eval x = MvPolynomial.eval ![x, m * x + r] f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [lineRestrict]
  | add p q hp hq => simp_all [lineRestrict]
  | mul_X p i hp => fin_cases i <;> simp_all [lineRestrict]

theorem lineRestrict_mul_X (p : MvPolynomial (Fin 2) K) (i : Fin 2) (m r : K) :
    lineRestrict (p * MvPolynomial.X i) m r
      = lineRestrict p m r * ![(Polynomial.X : K[X]), C m * Polynomial.X + C r] i := by
  simp [lineRestrict]

/-- Divisibility of `f - f(x, m x + r)` (re-expanded as a polynomial in `x`) by `y - m x - r`. -/
theorem dvd_sub_lineRestrict (f : MvPolynomial (Fin 2) K) (m r : K) :
    (MvPolynomial.X 1 - MvPolynomial.C m * MvPolynomial.X 0 - MvPolynomial.C r :
        MvPolynomial (Fin 2) K) ∣
      f - Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) (lineRestrict f m r) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [lineRestrict]
  | add p q hp hq =>
    have : p + q - Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) K)
          (lineRestrict (p + q) m r)
        = (p - Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) K)
            (lineRestrict p m r))
          + (q - Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) K)
            (lineRestrict q m r)) := by
      simp only [lineRestrict, map_add]; ring
    rw [this]; exact dvd_add hp hq
  | mul_X p i hp =>
    rw [lineRestrict_mul_X]
    fin_cases i
    · have : p * MvPolynomial.X 0 - Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) K)
          (lineRestrict p m r * ![(Polynomial.X : K[X]), C m * Polynomial.X + C r] 0)
          = (p - Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) K)
            (lineRestrict p m r)) * MvPolynomial.X 0 := by
        simp; ring
      simp only [Fin.zero_eta] at this ⊢
      rw [this]; exact hp.mul_right _
    · have : p * MvPolynomial.X 1 - Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) K)
          (lineRestrict p m r * ![(Polynomial.X : K[X]), C m * Polynomial.X + C r] 1)
          = (p - Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) K)
            (lineRestrict p m r)) * MvPolynomial.X 1
            + Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) (lineRestrict p m r)
              * (MvPolynomial.X 1 - MvPolynomial.C m * MvPolynomial.X 0 - MvPolynomial.C r) := by
        simp; ring
      simp only [Fin.mk_one] at this ⊢
      rw [this]; exact dvd_add (hp.mul_right _) (dvd_mul_left _ _)

/-- If the restriction of `f` to the line vanishes identically, `y - m x - r` divides `f`. -/
theorem dvd_of_lineRestrict_eq_zero (f : MvPolynomial (Fin 2) K) (m r : K)
    (h : lineRestrict f m r = 0) :
    ∃ k : MvPolynomial (Fin 2) K,
      f = (MvPolynomial.X 1 - MvPolynomial.C m * MvPolynomial.X 0 - MvPolynomial.C r) * k := by
  have := dvd_sub_lineRestrict f m r
  rw [h, map_zero, sub_zero] at this
  exact this

/-- More than `totalDegree f` roots force the restriction to vanish. -/
theorem lineRestrict_eq_zero_of_card (f : MvPolynomial (Fin 2) K) (m r : K) (S : Finset K)
    (hS : f.totalDegree < S.card)
    (hz : ∀ x ∈ S, MvPolynomial.eval ![x, m * x + r] f = 0) : lineRestrict f m r = 0 :=
  Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ S
    (fun x hx => by rw [eval_lineRestrict]; exact hz x hx)
    ((natDegree_lineRestrict_le f m r).trans_lt hS)

/-- **Theorem 5.15.**  If the line `y = m x + r` and the curve `f = 0` (with `f` of total degree
`d`) have more than `d` distinct points in common, then the line lies on the curve and
`y - m x - r` divides `f`; the cofactor has coefficients in the same field `K`. -/
@[kb "nivenzuckermanmontgomery" "Thm 5.15, p. 252"]
theorem plane_curve_line_dvd (f : MvPolynomial (Fin 2) K) (m r : K) (S : Finset (K × K))
    (hS : f.totalDegree < S.card)
    (hline : ∀ P ∈ S, P.2 = m * P.1 + r)
    (hcurve : ∀ P ∈ S, MvPolynomial.eval ![P.1, P.2] f = 0) :
    (∀ x : K, MvPolynomial.eval ![x, m * x + r] f = 0) ∧
    ∃ k : MvPolynomial (Fin 2) K,
      f = (MvPolynomial.X 1 - MvPolynomial.C m * MvPolynomial.X 0 - MvPolynomial.C r) * k := by
  classical
  have hinj : Set.InjOn Prod.fst (S : Set (K × K)) := by
    intro P hP Q hQ h
    exact Prod.ext h (by rw [hline P hP, hline Q hQ, h])
  have hcard : (S.image Prod.fst).card = S.card := Finset.card_image_of_injOn hinj
  have h0 : lineRestrict f m r = 0 := by
    apply lineRestrict_eq_zero_of_card f m r (S.image Prod.fst) (hcard ▸ hS)
    intro x hx
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hx
    have := hcurve P hP
    rwa [hline P hP] at this
  refine ⟨fun x => ?_, dvd_of_lineRestrict_eq_zero f m r h0⟩
  rw [← eval_lineRestrict, h0, eval_zero]

end Lines

section Definitions

variable {K : Type*} [Field K]

/-- Intersection multiplicity of the line `y = m x + r` with the curve `f = 0` at abscissa `x₀`:
the order of vanishing of `f(x, m x + r)` at `x₀`. -/
noncomputable def intersectionMultiplicity (f : MvPolynomial (Fin 2) K) (m r x₀ : K) : ℕ :=
  (lineRestrict f m r).rootMultiplicity x₀

/-- The intersection multiplicity is positive exactly at points of the curve lying on the line
(provided the line is not contained in the curve). -/
theorem intersectionMultiplicity_pos_iff (f : MvPolynomial (Fin 2) K) (m r x₀ : K)
    (h : lineRestrict f m r ≠ 0) :
    0 < intersectionMultiplicity f m r x₀ ↔ MvPolynomial.eval ![x₀, m * x₀ + r] f = 0 := by
  unfold intersectionMultiplicity
  rw [Polynomial.rootMultiplicity_pos h, Polynomial.IsRoot.def, eval_lineRestrict]

/-- A singular point of the curve `f = 0`: a point of the curve at which both first partial
derivatives vanish. -/
def IsSingularPoint (f : MvPolynomial (Fin 2) K) (P : Fin 2 → K) : Prop :=
  MvPolynomial.eval P f = 0 ∧ ∀ i, MvPolynomial.eval P (MvPolynomial.pderiv i f) = 0

/-- A simple (smooth) point of the curve: a point of the curve where the gradient is nonzero. -/
def IsSimplePoint (f : MvPolynomial (Fin 2) K) (P : Fin 2 → K) : Prop :=
  MvPolynomial.eval P f = 0 ∧ ¬ ∀ i, MvPolynomial.eval P (MvPolynomial.pderiv i f) = 0

/-- Every point of the curve is either simple or singular. -/
theorem isSimplePoint_or_isSingularPoint (f : MvPolynomial (Fin 2) K) (P : Fin 2 → K)
    (h : MvPolynomial.eval P f = 0) : IsSimplePoint f P ∨ IsSingularPoint f P := by
  by_cases hg : ∀ i, MvPolynomial.eval P (MvPolynomial.pderiv i f) = 0
  · exact Or.inr ⟨h, hg⟩
  · exact Or.inl ⟨h, hg⟩

/-- The cusp `y² = x³` is singular at the origin. -/
theorem cusp_isSingularPoint :
    IsSingularPoint (MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 ^ 3 : MvPolynomial (Fin 2) ℚ)
      (fun _ => 0) := by
  refine ⟨by simp, fun i => ?_⟩
  fin_cases i <;> simp [MvPolynomial.pderiv_X]

/-- An inflection point (flex): a simple point at which some line through it (necessarily the
tangent, since the point is simple) has intersection multiplicity at least `3`.  Only
nonvertical lines `y = m x + r` are considered. -/
def IsInflectionPoint (f : MvPolynomial (Fin 2) K) (P : Fin 2 → K) : Prop :=
  IsSimplePoint f P ∧ ∃ m : K, 3 ≤ intersectionMultiplicity f m (P 1 - m * P 0) (P 0)

/-- The origin is an inflection point of the cubic parabola `y = x³`. -/
theorem cubic_parabola_isInflectionPoint :
    IsInflectionPoint (MvPolynomial.X 1 - MvPolynomial.X 0 ^ 3 : MvPolynomial (Fin 2) ℚ)
      (fun _ => 0) := by
  refine ⟨⟨by simp, fun h => ?_⟩, 0, ?_⟩
  · have := h 1
    simp [MvPolynomial.pderiv_X] at this
  · have hne : lineRestrict (MvPolynomial.X 1 - MvPolynomial.X 0 ^ 3 : MvPolynomial (Fin 2) ℚ)
        0 (0 - 0 * 0) ≠ 0 := by
      simp [lineRestrict]
    unfold intersectionMultiplicity
    rw [Polynomial.le_rootMultiplicity_iff hne]
    simp [lineRestrict]

/-- Translate the point `P` to the origin: `g(x, y) = f(x + P₀, y + P₁)`. -/
noncomputable def translateTo (f : MvPolynomial (Fin 2) K) (P : Fin 2 → K) :
    MvPolynomial (Fin 2) K :=
  MvPolynomial.aeval (fun i => MvPolynomial.X i + MvPolynomial.C (P i)) f

/-- All monomials of `f` expanded around `P` (powers of `x - P₀`, `y - P₁`) have degree `≥ M`;
i.e. all partial derivatives of order `< M` vanish at `P` (the book's multiplicity `M`). -/
def HasMultiplicityAtLeast (f : MvPolynomial (Fin 2) K) (P : Fin 2 → K) (M : ℕ) : Prop :=
  ∀ s ∈ (translateTo f P).support, M ≤ s.sum fun _ e => e

/-- The multiplicity of the point `P` on the curve is exactly `M`. -/
def HasMultiplicity (f : MvPolynomial (Fin 2) K) (P : Fin 2 → K) (M : ℕ) : Prop :=
  HasMultiplicityAtLeast f P M ∧ ¬ HasMultiplicityAtLeast f P (M + 1)

theorem constantCoeff_translateTo (f : MvPolynomial (Fin 2) K) (P : Fin 2 → K) :
    MvPolynomial.constantCoeff (translateTo f P) = MvPolynomial.eval P f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [translateTo]
  | add p q hp hq => simp_all [translateTo]
  | mul_X p i hp => simp_all [translateTo]

/-- Multiplicity at least one means exactly that the point lies on the curve. -/
theorem hasMultiplicityAtLeast_one_iff (f : MvPolynomial (Fin 2) K) (P : Fin 2 → K) :
    HasMultiplicityAtLeast f P 1 ↔ MvPolynomial.eval P f = 0 := by
  rw [← constantCoeff_translateTo, MvPolynomial.constantCoeff_eq]
  constructor
  · intro h
    by_contra h0
    have hs : (0 : Fin 2 →₀ ℕ) ∈ (translateTo f P).support := by
      rwa [MvPolynomial.mem_support_iff]
    have := h 0 hs
    simp at this
  · intro h s hs
    by_contra hlt
    have : (s.sum fun _ e => e) = 0 := by omega
    have hs0 : s = 0 := by
      ext i
      rw [Finsupp.sum, Finset.sum_eq_zero_iff] at this
      by_cases hi : i ∈ s.support
      · simpa using this i hi
      · simpa using hi
    subst hs0
    exact (MvPolynomial.mem_support_iff.mp hs) h

theorem HasMultiplicityAtLeast.mono {f : MvPolynomial (Fin 2) K} {P : Fin 2 → K} {M N : ℕ}
    (h : HasMultiplicityAtLeast f P M) (hNM : N ≤ M) : HasMultiplicityAtLeast f P N :=
  fun s hs => hNM.trans (h s hs)

/-- The discriminant `b² - 4ac` of the quadratic part `a x² + b x y + c y²` of `f` expanded
around `P`. -/
noncomputable def tangentConeDisc (f : MvPolynomial (Fin 2) K) (P : Fin 2 → K) : K :=
  (translateTo f P).coeff (Finsupp.single 0 1 + Finsupp.single 1 1) ^ 2
    - 4 * (translateTo f P).coeff (Finsupp.single 0 2)
        * (translateTo f P).coeff (Finsupp.single 1 2)

/-- An ordinary double point: a point of multiplicity exactly `2` whose tangent cone consists
of two distinct lines (nonzero discriminant of the quadratic part). -/
def IsOrdinaryDoublePoint (f : MvPolynomial (Fin 2) K) (P : Fin 2 → K) : Prop :=
  HasMultiplicity f P 2 ∧ tangentConeDisc f P ≠ 0

/-- An ordinary double point lies on the curve. -/
theorem IsOrdinaryDoublePoint.eval_eq_zero {f : MvPolynomial (Fin 2) K} {P : Fin 2 → K}
    (h : IsOrdinaryDoublePoint f P) : MvPolynomial.eval P f = 0 :=
  (hasMultiplicityAtLeast_one_iff f P).mp (h.1.1.mono (by norm_num))

/-- `f` is absolutely irreducible if it stays irreducible over the algebraic closure of `K`. -/
def IsAbsolutelyIrreducible (f : MvPolynomial (Fin 2) K) : Prop :=
  Irreducible (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f)

/-- An absolutely irreducible polynomial is nonzero. -/
theorem IsAbsolutelyIrreducible.ne_zero {f : MvPolynomial (Fin 2) K}
    (h : IsAbsolutelyIrreducible f) : f ≠ 0 := by
  rintro rfl
  exact Irreducible.ne_zero h (by simp)

end Definitions

/-! ## Theorem 5.16 -/

section CubeSum

/-- The tangent recurrence `(X, Y, Z) ↦ (X (X³ + 2Y³), -Y (2X³ + Y³), Z (X³ - Y³))`. -/
def tangentStep (t : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (t.1 * (t.1 ^ 3 + 2 * t.2.1 ^ 3), -(t.2.1 * (2 * t.1 ^ 3 + t.2.1 ^ 3)),
    t.2.2 * (t.1 ^ 3 - t.2.1 ^ 3))

/-- The invariant: `X = 2^(n+1) a`, `Y`, `Z`, `a` odd, and `X³ + Y³ = 9 Z³`. -/
def TangentInv (n : ℕ) (t : ℤ × ℤ × ℤ) : Prop :=
  ∃ a : ℤ, Odd a ∧ t.1 = 2 ^ (n + 1) * a ∧ Odd t.2.1 ∧ Odd t.2.2 ∧
    t.1 ^ 3 + t.2.1 ^ 3 = 9 * t.2.2 ^ 3

theorem tangentInv_step {n : ℕ} {t : ℤ × ℤ × ℤ} (h : TangentInv n t) :
    TangentInv (n + 1) (tangentStep t) := by
  obtain ⟨a, ha, hX, hY, hZ, hE⟩ := h
  obtain ⟨X, Y, Z⟩ := t
  simp only at hX hY hZ hE
  have heX : Even (X ^ 3) := by
    rw [hX]
    exact ((even_two.pow_of_ne_zero (Nat.succ_ne_zero n)).mul_right a).pow_of_ne_zero
      (by norm_num)
  refine ⟨a * (2 ^ (3 * n + 2) * a ^ 3 + Y ^ 3), ?_, ?_, ?_, ?_, ?_⟩
  · have he : Even (2 ^ (3 * n + 2) * a ^ 3) :=
      (even_two.pow_of_ne_zero (by omega)).mul_right _
    exact ha.mul (he.add_odd hY.pow)
  · simp only [tangentStep]
    rw [hX]
    ring
  · simp only [tangentStep]
    exact (hY.mul ((even_two_mul (X ^ 3)).add_odd (hY.pow (n := 3)))).neg
  · simp only [tangentStep]
    exact hZ.mul (heX.sub_odd hY.pow)
  · simp only [tangentStep]
    linear_combination (X ^ 3 - Y ^ 3) ^ 3 * hE

/-- The tangent sequence starting at `(2, 1, 1)`. -/
def tangentSeq (n : ℕ) : ℤ × ℤ × ℤ := tangentStep^[n] (2, 1, 1)

theorem tangentInv_seq (n : ℕ) : TangentInv n (tangentSeq n) := by
  induction n with
  | zero => exact ⟨1, odd_one, by simp [tangentSeq], by simp [tangentSeq], by simp [tangentSeq],
      by norm_num [tangentSeq]⟩
  | succ n ih =>
    have := tangentInv_step ih
    rwa [tangentSeq, Function.iterate_succ_apply'] 

theorem tangentSeq_Z_ne_zero (n : ℕ) : (tangentSeq n).2.2 ≠ 0 := by
  obtain ⟨a, ha, hX, hY, hZ, hE⟩ := tangentInv_seq n
  intro h
  rw [Int.odd_iff] at hZ
  omega

/-- The rational point attached to the `n`-th triple. -/
noncomputable def tangentPoint (n : ℕ) : ℚ × ℚ :=
  (((tangentSeq n).1 : ℚ) / (tangentSeq n).2.2, ((tangentSeq n).2.1 : ℚ) / (tangentSeq n).2.2)

theorem tangentPoint_mem (n : ℕ) : (tangentPoint n).1 ^ 3 + (tangentPoint n).2 ^ 3 = 9 := by
  obtain ⟨a, ha, hX, hY, hZ, hE⟩ := tangentInv_seq n
  have hZ0 : ((tangentSeq n).2.2 : ℚ) ≠ 0 := by exact_mod_cast tangentSeq_Z_ne_zero n
  have hQ : (((tangentSeq n).1 : ℤ) : ℚ) ^ 3 + (((tangentSeq n).2.1 : ℤ) : ℚ) ^ 3
      = 9 * (((tangentSeq n).2.2 : ℤ) : ℚ) ^ 3 := by exact_mod_cast hE
  simp only [tangentPoint]
  rw [div_pow, div_pow, ← add_div, hQ]
  field_simp

theorem tangentPoint_ne {n m : ℕ} (hnm : n < m) : tangentPoint n ≠ tangentPoint m := by
  intro h
  have h1 := congrArg Prod.fst h
  simp only [tangentPoint] at h1
  have hzn := tangentSeq_Z_ne_zero n
  have hzm := tangentSeq_Z_ne_zero m
  rw [div_eq_div_iff (by exact_mod_cast hzn) (by exact_mod_cast hzm)] at h1
  have heq : (tangentSeq n).1 * (tangentSeq m).2.2 = (tangentSeq m).1 * (tangentSeq n).2.2 := by
    exact_mod_cast h1
  obtain ⟨a, ha, hXn, -, hZn, -⟩ := tangentInv_seq n
  obtain ⟨b, hb, hXm, -, hZm, -⟩ := tangentInv_seq m
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hnm
  rw [hXn, hXm] at heq
  have h2 : (2 : ℤ) ^ (n + 1) * (a * (tangentSeq (n + k + 1)).2.2)
      = 2 ^ (n + 1) * (2 ^ (k + 1) * b * (tangentSeq n).2.2) := by
    linear_combination heq
  have h3 := mul_left_cancel₀ (pow_ne_zero _ two_ne_zero) h2
  have hodd : Odd (a * (tangentSeq (n + k + 1)).2.2) := ha.mul hZm
  rw [h3] at hodd
  have heven : Even (2 ^ (k + 1) * b * (tangentSeq n).2.2) :=
    ((even_two.pow_of_ne_zero (Nat.succ_ne_zero k)).mul_right b).mul_right _
  exact (Int.not_even_iff_odd.2 hodd) heven

/-- **Theorem 5.16.**  The cubic curve `x³ + y³ = 9` has infinitely many rational points
(the points `(Xₙ/Zₙ, Yₙ/Zₙ)` obtained by iterating the tangent construction from `(2, 1)`). -/
@[kb "nivenzuckermanmontgomery" "Thm 5.16, p. 255"]
theorem infinite_rational_points_cube_sum_nine :
    {p : ℚ × ℚ | p.1 ^ 3 + p.2 ^ 3 = 9}.Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := tangentPoint) ?_ tangentPoint_mem
  intro n m h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact tangentPoint_ne hlt h
  · exact tangentPoint_ne hgt h.symm

end CubeSum

/-! ## Theorem 5.22 -/

section ChangeOfZero

/-- The addition on the group with zero element `O'` defined from that with zero `O`:
`A ⊕ B = A + B - O'`. -/
def shiftedAdd {G : Type*} [AddCommGroup G] (O' A B : G) : G := A + B - O'

/-- The translation `A ↦ A + O'`. -/
def shiftEquiv {G : Type*} [AddCommGroup G] (O' : G) : G ≃ G := Equiv.addRight O'

/-- **Theorem 5.22** (first part).  `O' + (A ⊕ B) = A + B`. -/
@[kb "nivenzuckermanmontgomery" "Thm 5.22, p. 269"]
theorem add_shiftedAdd {G : Type*} [AddCommGroup G] (O' A B : G) :
    O' + shiftedAdd O' A B = A + B := by
  simp [shiftedAdd]

/-- **Theorem 5.22** (second part).  The map `A ↦ A + O'` carries the old addition to
`A ⊕ B = A + B - O'`, sends `O` to `O'`, and is a bijection; hence it is an isomorphism of the
group with zero `O` onto the group with zero `O'`. -/
@[kb "nivenzuckermanmontgomery" "Thm 5.22, p. 269"]
theorem shiftEquiv_add {G : Type*} [AddCommGroup G] (O' A B : G) :
    shiftEquiv O' (A + B) = shiftedAdd O' (shiftEquiv O' A) (shiftEquiv O' B) := by
  simp only [shiftEquiv, shiftedAdd, Equiv.coe_addRight]
  abel

theorem shiftEquiv_zero {G : Type*} [AddCommGroup G] (O' : G) : shiftEquiv O' 0 = O' := by
  simp [shiftEquiv]

theorem shiftedAdd_zero_left {G : Type*} [AddCommGroup G] (O' B : G) :
    shiftedAdd O' O' B = B := by
  simp [shiftedAdd]

theorem shiftedAdd_comm {G : Type*} [AddCommGroup G] (O' A B : G) :
    shiftedAdd O' A B = shiftedAdd O' B A := by
  simp [shiftedAdd, add_comm]

theorem shiftedAdd_assoc {G : Type*} [AddCommGroup G] (O' A B C : G) :
    shiftedAdd O' (shiftedAdd O' A B) C = shiftedAdd O' A (shiftedAdd O' B C) := by
  simp only [shiftedAdd]
  abel

/-- Theorem 5.22 for the chord-and-tangent group of a Weierstrass curve. -/
theorem weierstrass_shiftEquiv_add {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    (O' A B : W.Point) :
    shiftEquiv O' (A + B) = shiftedAdd O' (shiftEquiv O' A) (shiftEquiv O' B) :=
  shiftEquiv_add O' A B

end ChangeOfZero

end NTKB.NZM
