/-
Ireland–Rosen, Chapter 18, §3 and §4: the number of points of `y² = x³ - Dx` over `𝔽_p`.
-/
import NTKB.IrelandRosen.R4.JacobiQuadratic
import NTKB.IrelandRosen.R3.JacobiSum
import NTKB.IrelandRosen.R2.Characters
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The number of points of `y² = x³ - Dx` over `𝔽_p`

Ireland–Rosen, Chapter 18, §3 (the bijection and the counting) and §4, Theorem 5. We follow the
book's argument.

* `N_p = 1 + N(y² = x³ - Dx) = 2 + N(u² = v⁴ + 4D)`: the maps
  `T(u,v) = ((u+v²)/2, v(u+v²)/2)` and `S(x,y) = (2x - y²/x², y/x)` are inverse bijections between
  `C' : u² = v⁴ + 4D` and `C \ {(0,0)}` (`card_curve_eq`).
* If `p ≡ 3 (mod 4)`, every square is a fourth power, `N(u² = v⁴ + 4D) = N(u² = v² + 4D) = p - 1`,
  so `N_p = p + 1`.
* If `p ≡ 1 (mod 4)`, with `λ = χ_π` the quartic residue character of a primary `π` and
  `ρ = λ²`, counting `v⁴ = w` by `∑_{j<4} λ^j(w)` gives
  `N(u² = v⁴ + 4D) = p - 1 + T + conj T` with `T = λ(-4D) ρ(4D) J(λ, ρ)`; the Lemma
  `J(ρ, λ) = λ(4) J(λ, λ)` and Proposition 9.9.4 (`-λ(-1) J(λ, λ) = π`) give
  `T = -conj(χ_π(D)) π`, whence `N_p = p + 1 - conj(χ_π(D)) π - χ_π(D) conj π`.
* Hasse's bound `|N_p - (p + 1)| ≤ 2 √p` follows from `|π|² = p`.
-/

namespace NTKB.IrelandRosen

open Finset

local notation "ℤ[i]" => GaussianInt

set_option linter.unusedSectionVars false

section Geometry

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `T(u,v) = ((u+v²)/2, v(u+v²)/2)`. -/
private def curveT (uv : F × F) : F × F :=
  ((uv.1 + uv.2 ^ 2) / 2, uv.2 * ((uv.1 + uv.2 ^ 2) / 2))

/-- `S(x,y) = (2x - y²/x², y/x)`. -/
private def curveS (xy : F × F) : F × F :=
  (2 * xy.1 - xy.2 ^ 2 / xy.1 ^ 2, xy.2 / xy.1)

omit [Fintype F] [DecidableEq F] in
private lemma curveT_x_ne {a : F} (h2 : (2 : F) ≠ 0) (ha : a ≠ 0) {uv : F × F}
    (h : uv.1 ^ 2 = uv.2 ^ 4 + 4 * a) : (uv.1 + uv.2 ^ 2) / 2 ≠ 0 := by
  intro h0
  have h1 : uv.1 + uv.2 ^ 2 = 0 := by
    rcases div_eq_zero_iff.1 h0 with h | h
    · exact h
    · exact absurd h h2
  have h4 : (4 : F) * a = 0 := by
    have : uv.1 = -uv.2 ^ 2 := by linear_combination h1
    rw [this] at h; linear_combination -h
  have : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  exact (mul_ne_zero this ha) h4

/-- The point count of the curve `y² = x³ - a x` equals `1 +` that of `u² = v⁴ + 4a`
(Ireland–Rosen, Chapter 18, §3). -/
lemma card_curve_eq {a : F} (h2 : (2 : F) ≠ 0) (ha : a ≠ 0) :
    #{xy : F × F | xy.2 ^ 2 = xy.1 ^ 3 - a * xy.1} =
      1 + #{uv : F × F | uv.1 ^ 2 = uv.2 ^ 4 + 4 * a} := by
  have h4 : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  set C : Finset (F × F) := {xy : F × F | xy.2 ^ 2 = xy.1 ^ 3 - a * xy.1} with hC
  have memC : ∀ xy : F × F, xy ∈ C ↔ xy.2 ^ 2 = xy.1 ^ 3 - a * xy.1 := by
    intro xy; simp [hC]
  have memC' : ∀ uv : F × F, uv ∈ ({uv : F × F | uv.1 ^ 2 = uv.2 ^ 4 + 4 * a} : Finset (F × F)) ↔
      uv.1 ^ 2 = uv.2 ^ 4 + 4 * a := by
    intro uv; simp
  have h0 : ((0 : F), (0 : F)) ∈ C := by rw [memC]; simp
  have hcard := Finset.card_erase_add_one h0
  rw [← hcard, add_comm]
  congr 1
  have hxne : ∀ xy : F × F, xy ∈ C.erase (0, 0) → xy.1 ≠ 0 := by
    intro xy hxy
    rw [Finset.mem_erase, memC] at hxy
    obtain ⟨hne, hy⟩ := hxy
    intro hx
    apply hne
    rw [hx] at hy
    have : xy.2 = 0 := by simpa using hy
    exact Prod.ext hx this
  refine Finset.card_nbij' curveS curveT ?_ ?_ ?_ ?_
  · intro xy hxy
    rw [Finset.mem_coe] at hxy
    have hx := hxne xy hxy
    rw [Finset.mem_erase, memC] at hxy
    obtain ⟨-, hy⟩ := hxy
    rw [Finset.mem_coe, memC']
    simp only [curveS]
    have e : xy.2 ^ 2 / xy.1 ^ 2 = xy.1 - a / xy.1 := by
      field_simp; linear_combination hy
    have e2 : (xy.2 / xy.1) ^ 4 = (xy.2 ^ 2 / xy.1 ^ 2) ^ 2 := by ring
    rw [e2, e]
    field_simp; ring
  · intro uv huv
    rw [Finset.mem_coe, memC'] at huv
    have hx := curveT_x_ne h2 ha huv
    rw [Finset.mem_coe, Finset.mem_erase, memC]
    simp only [curveT]
    refine ⟨fun h => hx (congrArg Prod.fst h), ?_⟩
    set x := (uv.1 + uv.2 ^ 2) / 2 with hxdef
    have hx2 : 2 * x = uv.1 + uv.2 ^ 2 := by rw [hxdef]; field_simp
    have hq : (4 : F) * (x ^ 2 - uv.2 ^ 2 * x - a) = 0 := by
      linear_combination huv + (2 * x - uv.2 ^ 2 + uv.1) * hx2
    have hq' : x ^ 2 - uv.2 ^ 2 * x - a = 0 := by
      rcases mul_eq_zero.1 hq with h | h
      · exact absurd h h4
      · exact h
    linear_combination (-x) * hq'
  · intro xy hxy
    rw [Finset.mem_coe] at hxy
    have hx := hxne xy hxy
    ext
    · simp only [curveT, curveS]; field_simp; ring
    · simp only [curveT, curveS]; field_simp; ring
  · intro uv huv
    rw [Finset.mem_coe, memC'] at huv
    have hx := curveT_x_ne h2 ha huv
    have hx' : uv.1 + uv.2 ^ 2 ≠ 0 := fun h => hx (by rw [h, zero_div])
    ext
    · simp only [curveT, curveS]
      field_simp
      ring
    · simp only [curveT, curveS]
      field_simp

end Geometry

section Counting

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

lemma card_filter_prod (P : F → F → Prop) [∀ u v, Decidable (P u v)] :
    #{uv : F × F | P uv.1 uv.2} = ∑ v : F, #{u : F | P u v} := by
  rw [Finset.card_filter, Fintype.sum_prod_type_right]
  exact Finset.sum_congr rfl fun v _ => (Finset.card_filter _ _).symm

lemma card_sqrts_int (hF : ringChar F ≠ 2) (a : F) :
    (#{u : F | u ^ 2 = a} : ℤ) = quadraticChar F a + 1 := by
  have hc := quadraticChar_card_sqrts hF a
  rw [← hc]; simp

lemma sum_comp_pow_eq {R : Type*} [AddCommMonoid R] (n : ℕ) (f : F → R) :
    ∑ t : F, f (t ^ n) = ∑ x : F, #{t : F | t ^ n = x} • f x := by
  have h1 : ∀ t : F, f (t ^ n) = ∑ x : F, if t ^ n = x then f x else 0 := by
    intro t; simp
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const]

omit [Fintype F] [DecidableEq F] in
private lemma four_ne_zero' (h2 : (2 : F) ≠ 0) : (4 : F) ≠ 0 := by
  have : (4 : F) = 2 * 2 := by norm_num
  rw [this]; exact mul_ne_zero h2 h2

/-- The conic `u² = z² + c` has `q - 1` points for `c ≠ 0`. -/
lemma card_conic {c : F} (h2 : (2 : F) ≠ 0) (hc : c ≠ 0) :
    #{uz : F × F | uz.1 ^ 2 = uz.2 ^ 2 + c} = Fintype.card F - 1 := by
  have hcard : #((Finset.univ : Finset F).erase 0) = Fintype.card F - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  rw [← hcard]
  refine Finset.card_nbij' (fun uz => uz.1 - uz.2) (fun a => ((a + c / a) / 2, (c / a - a) / 2))
    ?_ ?_ ?_ ?_
  · intro uz huz
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at huz
    simp only [Finset.coe_erase, Finset.coe_univ, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff,
      true_and]
    intro h0
    have : c = (uz.1 - uz.2) * (uz.1 + uz.2) := by linear_combination -huz
    rw [h0, zero_mul] at this
    exact hc this
  · intro a ha
    simp only [Finset.coe_erase, Finset.coe_univ, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff,
      true_and] at ha
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    field_simp
    ring
  · intro uz huz
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at huz
    have h0 : uz.1 - uz.2 ≠ 0 := by
      intro h0
      have : c = (uz.1 - uz.2) * (uz.1 + uz.2) := by linear_combination -huz
      rw [h0, zero_mul] at this
      exact hc this
    have e : c / (uz.1 - uz.2) = uz.1 + uz.2 := by
      rw [div_eq_iff h0]; linear_combination -huz
    ext
    · simp only [e]; field_simp; ring
    · simp only [e]; field_simp; ring
  · intro a ha
    simp only [Finset.coe_erase, Finset.coe_univ, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff,
      true_and] at ha
    field_simp
    ring

/-- `#{u² = v⁴ + c} = q + ∑_v ρ(v⁴ + c)`. -/
lemma card_quartic_eq_sum (hF : ringChar F ≠ 2) (c : F) :
    (#{uv : F × F | uv.1 ^ 2 = uv.2 ^ 4 + c} : ℤ) =
      Fintype.card F + ∑ v : F, quadraticChar F (v ^ 4 + c) := by
  have h := card_filter_prod (fun u v : F => u ^ 2 = v ^ 4 + c)
  beta_reduce at h
  rw [h]
  push_cast
  simp_rw [card_sqrts_int hF]
  rw [Finset.sum_add_distrib]
  simp [add_comm]

/-- For `q ≡ 3 (mod 4)`, `#{u² = v⁴ + c} = q - 1`. -/
lemma card_quartic_of_neg_one (hF : ringChar F ≠ 2) (hneg : quadraticChar F (-1) = -1) {c : F}
    (hc : c ≠ 0) :
    (#{uv : F × F | uv.1 ^ 2 = uv.2 ^ 4 + c} : ℤ) = Fintype.card F - 1 := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  rw [card_quartic_eq_sum hF]
  -- `∑_z ρ(z² + c) = -1`
  have hconic : ∑ z : F, quadraticChar F (z ^ 2 + c) = -1 := by
    have h := card_conic h2 hc
    have h0 := card_filter_prod (fun u z : F => u ^ 2 = z ^ 2 + c)
    beta_reduce at h0
    rw [h0] at h
    have h' : ((∑ z : F, #{u : F | u ^ 2 = z ^ 2 + c} : ℕ) : ℤ) = ((Fintype.card F - 1 : ℕ) : ℤ) :=
      by rw [h]
    rw [Nat.cast_sum, Nat.cast_sub Fintype.card_pos] at h'
    simp_rw [card_sqrts_int hF] at h'
    rw [Finset.sum_add_distrib] at h'
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h'
    have h1 : ((Nat.succ 0 : ℕ) : ℤ) = 1 := by norm_num
    linarith
  have hodd : ∑ x : F, quadraticChar F x * quadraticChar F (x ^ 2 + c) = 0 := by
    have : ∑ x : F, quadraticChar F x * quadraticChar F (x ^ 2 + c) =
        ∑ x : F, quadraticChar F (-x) * quadraticChar F ((-x) ^ 2 + c) :=
      (Equiv.sum_comp (Equiv.neg F) (fun x => quadraticChar F x * quadraticChar F (x ^ 2 + c))).symm
    have h2' : ∀ x : F, quadraticChar F (-x) = - quadraticChar F x := by
      intro x
      rw [show -x = (-1) * x by ring, map_mul, hneg]; ring
    simp only [neg_sq, h2', neg_mul] at this
    rw [Finset.sum_neg_distrib] at this
    linarith
  have key : ∑ v : F, quadraticChar F (v ^ 4 + c) =
      ∑ x : F, (quadraticChar F x + 1) * quadraticChar F (x ^ 2 + c) := by
    have := sum_comp_pow_eq 2 (fun z : F => quadraticChar F (z ^ 2 + c))
    have e : ∀ v : F, quadraticChar F (v ^ 4 + c) = quadraticChar F ((v ^ 2) ^ 2 + c) := by
      intro v; rw [← pow_mul]
    simp_rw [e]
    rw [this]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [nsmul_eq_mul]
    have := card_sqrts_int hF x
    rw [show ((#{t : F | t ^ 2 = x} : ℕ) : ℤ) = _ from this]
  rw [key]
  simp_rw [add_mul, one_mul]
  rw [Finset.sum_add_distrib, hodd, hconic]; ring

end Counting

section Characters

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {R : Type*} [CommRing R]

/-- `∑_w φ(w) ψ(w + c) = φ(-c) ψ(c) J(φ, ψ)` for `c ≠ 0` (substituting `w = -c s`). -/
lemma sum_mul_add (φ ψ : MulChar F R) {c : F} (hc : c ≠ 0) :
    ∑ w : F, φ w * ψ (w + c) = φ (-c) * ψ c * jacobiSum φ ψ := by
  rw [← Equiv.sum_comp (Equiv.mulLeft₀ (-c) (neg_ne_zero.2 hc)) (fun w => φ w * ψ (w + c)),
    jacobiSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  show φ (-c * s) * ψ (-c * s + c) = _
  have : -c * s + c = c * (1 - s) := by ring
  rw [this, map_mul, map_mul]; ring

omit [DecidableEq F] in
lemma card_pow_eq_numSolPow (n : ℕ) (w : F) [DecidableEq F] :
    #{t : F | t ^ n = w} = numSolPow n w := by
  unfold numSolPow
  congr!

end Characters

namespace Gaussian

lemma star_eq_pow_three {u : ℤ[i]} (hu : IsUnit u) (h4 : u ^ 4 = 1) : star u = u ^ 3 := by
  have hmul := unit_mul_star hu
  linear_combination (-(star u)) * h4 + u ^ 3 * hmul

variable {π : ℤ[i]} [Fact (Nat.Prime π.norm.natAbs)] (hp2 : π.norm.natAbs ≠ 2)

include hp2

/-- The Legendre symbol modulo `p = N π`, as a `ℤ[i]`-valued multiplicative character. -/
noncomputable abbrev quadMulChar (π : ℤ[i]) [Fact (Nat.Prime π.norm.natAbs)] :
    MulChar (ZMod π.norm.natAbs) ℤ[i] :=
  (quadraticChar (ZMod π.norm.natAbs)).ringHomComp (Int.castRingHom ℤ[i])

lemma ringChar_ne_two_of_ne_two :
    ringChar (ZMod π.norm.natAbs) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]; exact hp2

lemma quarticMulChar_sq_eq : quarticMulChar π hp2 ^ 2 = quadMulChar π := by
  refine MulChar.ext fun u => ?_
  have h := quarticMulChar_sq_apply (π := π) hp2 ((u : ZMod π.norm.natAbs).val : ℤ)
  have hu : ((((u : ZMod π.norm.natAbs).val : ℕ) : ℤ) : ZMod π.norm.natAbs) = u := by simp
  rw [hu] at h
  rw [h]
  show ((quadraticChar (ZMod π.norm.natAbs)
      ((((u : ZMod π.norm.natAbs).val : ℕ) : ℤ) : ZMod π.norm.natAbs) : ℤ) : ℤ[i]) =
    ((quadraticChar (ZMod π.norm.natAbs) (u : ZMod π.norm.natAbs) : ℤ) : ℤ[i])
  rw [hu]

lemma quarticMulChar_apply_pow_four {a : ZMod π.norm.natAbs} (ha : a ≠ 0) :
    quarticMulChar π hp2 a ^ 4 = 1 := by
  have := congrArg (fun ψ : MulChar (ZMod π.norm.natAbs) ℤ[i] => ψ a) (quarticMulChar_pow_four hp2)
  simp only [MulChar.pow_apply' _ (by norm_num : (4 : ℕ) ≠ 0)] at this
  rw [this]; exact MulChar.one_apply (isUnit_iff_ne_zero.2 ha)

lemma quadMulChar_apply_sq {a : ZMod π.norm.natAbs} (ha : a ≠ 0) :
    quadMulChar π a ^ 2 = 1 := by
  rw [← quarticMulChar_sq_eq hp2, MulChar.pow_apply' _ (by norm_num : (2 : ℕ) ≠ 0), ← pow_mul]
  exact quarticMulChar_apply_pow_four hp2 ha

lemma sum_quadMulChar_add (c : ZMod π.norm.natAbs) : ∑ w, quadMulChar π (w + c) = 0 := by
  have h := quadraticChar_sum_zero (ringChar_ne_two_of_ne_two hp2)
  have h' : ∑ w : ZMod π.norm.natAbs, quadraticChar (ZMod π.norm.natAbs) (w + c) = 0 := by
    exact (Equiv.sum_comp (Equiv.addRight c) (fun a => quadraticChar (ZMod π.norm.natAbs) a)).trans h
  have : ∑ w : ZMod π.norm.natAbs, quadMulChar π (w + c) =
      ((∑ w : ZMod π.norm.natAbs, quadraticChar (ZMod π.norm.natAbs) (w + c) : ℤ) : ℤ[i]) := by
    rw [Int.cast_sum]; rfl
  rw [this, h', Int.cast_zero]

/-- The number of solutions of `x⁴ = w` is `∑_{j<4} χ^j(w)` for `w ≠ 0`. -/
lemma numSolPow_four_eq {w : ZMod π.norm.natAbs} (hw : w ≠ 0) :
    ((numSolPow 4 w : ℕ) : ℤ[i]) = ∑ j ∈ Finset.range 4, (quarticMulChar π hp2 ^ j) w := by
  let f : ℤ[i] →+* ℂ := GaussianInt.toComplex
  have hf : Function.Injective f := GaussianInt.toComplex_injective
  have hord : orderOf ((quarticMulChar π hp2).ringHomComp f) = 4 :=
    orderOf_quarticMulChar_ringHomComp hp2 f two_ne_zero
  have hdvd : 4 ∣ Fintype.card (ZMod π.norm.natAbs) - 1 := by
    rw [ZMod.card]; exact ⟨qexp π, (four_mul_qexp irreducible_of_fact hp2).symm⟩
  have H := numSolPow_eq_sum_range hdvd hord w
  apply hf
  rw [map_natCast, map_sum, H]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [bookChar_of_ne_zero _ hw, MulChar.ringHomComp_pow, MulChar.ringHomComp_apply]

/-- `∑_v ρ(v⁴ + c) = ρ(c) + ∑_{j<4} ∑_w χ^j(w) ρ(w + c)`. -/
lemma sum_quadMulChar_pow_four (c : ZMod π.norm.natAbs) :
    ∑ v : ZMod π.norm.natAbs, quadMulChar π (v ^ 4 + c) =
      quadMulChar π c + ∑ j ∈ Finset.range 4, ∑ w : ZMod π.norm.natAbs,
        (quarticMulChar π hp2 ^ j) w * quadMulChar π (w + c) := by
  rw [sum_comp_pow_eq 4 (fun w => quadMulChar π (w + c))]
  have key : ∀ w : ZMod π.norm.natAbs,
      #{t : ZMod π.norm.natAbs | t ^ 4 = w} • quadMulChar π (w + c) =
        (if w = 0 then quadMulChar π c else 0) +
          ∑ j ∈ Finset.range 4, (quarticMulChar π hp2 ^ j) w * quadMulChar π (w + c) := by
    intro w
    by_cases hw : w = 0
    · subst hw
      have h1 : #{t : ZMod π.norm.natAbs | t ^ 4 = 0} = 1 := by
        rw [Finset.card_eq_one]
        exact ⟨0, by ext x; simp⟩
      rw [h1]
      simp [MulChar.map_zero]
    · rw [if_neg hw, zero_add, nsmul_eq_mul, card_pow_eq_numSolPow, numSolPow_four_eq hp2 hw,
        Finset.sum_mul]
  simp_rw [key]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.univ) (0 : ZMod π.norm.natAbs)
    (fun _ => quadMulChar π c)]
  rw [Finset.sum_comm]
  simp

lemma sum_term_zero {c : ZMod π.norm.natAbs} :
    ∑ w : ZMod π.norm.natAbs, (quarticMulChar π hp2 ^ 0) w * quadMulChar π (w + c) =
      -quadMulChar π c := by
  have h := sum_quadMulChar_add hp2 c
  have e : ∀ w : ZMod π.norm.natAbs, (quarticMulChar π hp2 ^ 0) w * quadMulChar π (w + c) =
      quadMulChar π (w + c) - if w = 0 then quadMulChar π (0 + c) else 0 := by
    intro w
    by_cases hw : w = 0
    · subst hw; simp [MulChar.map_zero]
    · rw [pow_zero, MulChar.one_apply (isUnit_iff_ne_zero.2 hw), one_mul, if_neg hw, sub_zero]
  simp_rw [e]
  rw [Finset.sum_sub_distrib, h, Finset.sum_ite_eq' (Finset.univ) (0 : ZMod π.norm.natAbs)
    (fun _ => quadMulChar π (0 + c))]
  simp

lemma sum_term_two {c : ZMod π.norm.natAbs} (hc : c ≠ 0) :
    ∑ w : ZMod π.norm.natAbs, (quarticMulChar π hp2 ^ 2) w * quadMulChar π (w + c) = -1 := by
  have hsq := quarticMulChar_sq_eq hp2
  rw [hsq, sum_mul_add _ _ hc]
  have hinv : (quadMulChar π)⁻¹ = quadMulChar π := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← hsq, ← pow_add]; exact quarticMulChar_pow_four hp2
  have hne : quadMulChar π ≠ 1 := by rw [← hsq]; exact quarticMulChar_sq_ne_one hp2
  have hJ := jacobiSum_nontrivial_inv hne
  rw [hinv] at hJ
  rw [hJ, show -c = (-1) * c by ring, map_mul]
  have h1 := quadMulChar_apply_sq hp2 hc
  have h2 := quadMulChar_apply_sq hp2 (neg_ne_zero.2 (one_ne_zero (α := ZMod π.norm.natAbs)))
  linear_combination (-(quadMulChar π (-1) ^ 2)) * h1 + (-1) * h2

lemma sum_term_one (hP : IsPrimary π) {D : ℤ} (hD : (D : ZMod π.norm.natAbs) ≠ 0) :
    ∑ w : ZMod π.norm.natAbs,
      (quarticMulChar π hp2 ^ 1) w * quadMulChar π (w + 4 * (D : ZMod π.norm.natAbs)) =
      -star (quarticChar π D) * π := by
  have h2 : (2 : ZMod π.norm.natAbs) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_ne_two hp2)
  have h4ne : (4 : ZMod π.norm.natAbs) ≠ 0 := four_ne_zero' h2
  have hc : 4 * (D : ZMod π.norm.natAbs) ≠ 0 := mul_ne_zero h4ne hD
  have hneg := neg_mul_jacobiSum_eq hp2 hP
  have h4pow := quarticMulChar_apply_pow_four hp2 h4ne
  have hD4 := quarticMulChar_apply_pow_four hp2 hD
  set χ := quarticMulChar π hp2 with hχ
  rw [pow_one, sum_mul_add _ _ hc]
  have hJ : jacobiSum (quadMulChar π) χ = χ 4 * jacobiSum χ χ :=
    jacobiSum_quadraticChar_eq (ringChar_ne_two_of_ne_two hp2) (quarticMulChar_ne_one hp2)
  rw [jacobiSum_comm χ, hJ]
  have hρc : quadMulChar π (4 * (D : ZMod π.norm.natAbs)) = χ (4 * D) ^ 2 := by
    rw [← quarticMulChar_sq_eq hp2, MulChar.pow_apply' _ (by norm_num : (2 : ℕ) ≠ 0)]
  have hu : χ (D : ZMod π.norm.natAbs) = quarticChar π D := quarticMulChar_intCast hp2 D
  have hstar : star (χ (D : ZMod π.norm.natAbs)) = χ D ^ 3 :=
    star_eq_pow_three (isUnit_quarticMulChar hp2 hD) hD4
  have e1 : χ (-(4 * (D : ZMod π.norm.natAbs))) = χ (-1) * χ 4 * χ D := by
    rw [show -(4 * (D : ZMod π.norm.natAbs)) = (-1) * 4 * D by ring, map_mul, map_mul]
  rw [hρc, e1, ← hu, hstar, map_mul]
  linear_combination (χ (-1) * χ D ^ 3 * jacobiSum χ χ) * h4pow + (-χ D ^ 3) * hneg

lemma sum_term_three {c : ZMod π.norm.natAbs} :
    ∑ w : ZMod π.norm.natAbs, (quarticMulChar π hp2 ^ 3) w * quadMulChar π (w + c) =
      star (∑ w : ZMod π.norm.natAbs, (quarticMulChar π hp2 ^ 1) w * quadMulChar π (w + c)) := by
  rw [star_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [star_mul']
  have hρ : star (quadMulChar π (w + c)) = quadMulChar π (w + c) := by
    show star (((quadraticChar (ZMod π.norm.natAbs) (w + c) : ℤ) : ℤ[i])) = _
    exact star_intCast _
  rw [hρ]
  congr 1
  rw [MulChar.pow_apply' _ (by norm_num : (3 : ℕ) ≠ 0), pow_one]
  by_cases hw : w = 0
  · subst hw; simp [MulChar.map_zero]
  · exact (star_eq_pow_three (isUnit_quarticMulChar hp2 hw) (quarticMulChar_apply_pow_four hp2 hw)).symm

/-- The number of points of `u² = v⁴ + 4D` over `𝔽_p`, as an element of `ℤ[i]`
(Ireland–Rosen, Chapter 18, §3). -/
theorem card_quartic_gaussianInt (hP : IsPrimary π) {D : ℤ}
    (hD : ¬ (π.norm.natAbs : ℤ) ∣ D) :
    ((#{uv : ZMod π.norm.natAbs × ZMod π.norm.natAbs |
        uv.1 ^ 2 = uv.2 ^ 4 + 4 * (D : ZMod π.norm.natAbs)} : ℕ) : ℤ[i]) =
      π.norm.natAbs - 1 - star (quarticChar π D) * π - quarticChar π D * star π := by
  have hDne : (D : ZMod π.norm.natAbs) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h2 : (2 : ZMod π.norm.natAbs) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_ne_two hp2)
  have hc : 4 * (D : ZMod π.norm.natAbs) ≠ 0 := mul_ne_zero (four_ne_zero' h2) hDne
  have hcard := card_quartic_eq_sum (ringChar_ne_two_of_ne_two hp2) (4 * (D : ZMod π.norm.natAbs))
  have hM := congrArg (Int.cast : ℤ → ℤ[i]) hcard
  rw [Int.cast_add, Int.cast_natCast, Int.cast_natCast, Int.cast_sum] at hM
  have hM' : ((#{uv : ZMod π.norm.natAbs × ZMod π.norm.natAbs |
        uv.1 ^ 2 = uv.2 ^ 4 + 4 * (D : ZMod π.norm.natAbs)} : ℕ) : ℤ[i]) =
      (Fintype.card (ZMod π.norm.natAbs) : ℤ[i]) +
        ∑ v : ZMod π.norm.natAbs, quadMulChar π (v ^ 4 + 4 * (D : ZMod π.norm.natAbs)) := hM
  rw [hM', sum_quadMulChar_pow_four hp2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [sum_term_zero hp2, sum_term_two hp2 hc, sum_term_three hp2,
    sum_term_one hp2 hP hDne, ZMod.card]
  simp only [star_mul', star_neg, star_star]
  ring

end Gaussian

/-! ### The theorems -/

/-- `N_p` for the curve `y² = x³ - Dx` over `𝔽_p`: the affine solutions and the point at infinity. -/
noncomputable def numPointsQuarticCurve (p : ℕ) [NeZero p] (D : ℤ) : ℕ :=
  1 + (Finset.univ.filter fun xy : ZMod p × ZMod p => xy.2 ^ 2 = xy.1 ^ 3 - D * xy.1).card

lemma ringChar_zmod_ne_two {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]; exact hp

/-- `N_p = 2 + #{u² = v⁴ + 4D}` (Ireland–Rosen, Chapter 18, §3). -/
lemma numPointsQuarticCurve_eq_two_add {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {D : ℤ}
    (hD : ¬ (p : ℤ) ∣ D) :
    numPointsQuarticCurve p D =
      2 + #{uv : ZMod p × ZMod p | uv.1 ^ 2 = uv.2 ^ 4 + 4 * (D : ZMod p)} := by
  have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (ringChar_zmod_ne_two hp)
  have hDne : (D : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  unfold numPointsQuarticCurve
  rw [card_curve_eq h2 hDne]
  ring

/-- **Theorem 5 of Chapter 18, `p ≡ 3 (mod 4)`.** -/
@[kb "irelandrosen1990" "Ch. 18, §4, Theorem 5, p. 317"]
theorem numPointsQuarticCurve_of_mod_four_eq_three {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3)
    {D : ℤ} (hD : ¬ (p : ℤ) ∣ D) : numPointsQuarticCurve p D = p + 1 := by
  have hp2 : p ≠ 2 := by omega
  have hF := ringChar_zmod_ne_two hp2
  have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero hF
  have hDne : (D : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hc : 4 * (D : ZMod p) ≠ 0 := mul_ne_zero (four_ne_zero' h2) hDne
  have hneg : quadraticChar (ZMod p) (-1) = -1 := by
    rw [quadraticChar_neg_one_iff_not_isSquare, ZMod.exists_sq_eq_neg_one_iff.not]
    omega
  have h := card_quartic_of_neg_one hF hneg hc
  rw [ZMod.card] at h
  rw [numPointsQuarticCurve_eq_two_add hp2 hD]
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  omega

/-- **Theorem 5 of Chapter 18.** If `p ≡ 1 (mod 4)` is prime, `p = π π̄` with `π` primary
(`π ≡ 1 (mod 2 + 2i)`) and `p ∤ D`, then `N_p = p + 1 - conj((D/π)₄) π - (D/π)₄ π̄`. -/
@[kb "irelandrosen1990" "Ch. 18, §4, Theorem 5, p. 317"]
theorem numPointsQuarticCurve_eq {p : ℕ} [Fact p.Prime] (hp : p % 4 = 1) {π : GaussianInt}
    (hπ : Gaussian.IsPrimary π) (hπp : π.norm = p) {D : ℤ} (hD : ¬ (p : ℤ) ∣ D) :
    ((numPointsQuarticCurve p D : ℤ) : GaussianInt) =
      p + 1 - star (Gaussian.quarticChar π D) * π - Gaussian.quarticChar π D * star π := by
  have hp2 : p ≠ 2 := by omega
  have hN : π.norm.natAbs = p := by rw [hπp, Int.natAbs_natCast]
  rw [numPointsQuarticCurve_eq_two_add hp2 hD]
  subst hN
  have h := Gaussian.card_quartic_gaussianInt hp2 hπ hD
  push_cast
  rw [h]
  ring

/-- A prime `p ≡ 1 (mod 4)` is the norm of a primary Gaussian integer. -/
lemma exists_isPrimary_norm_eq {p : ℕ} [Fact p.Prime] (hp : p % 4 = 1) :
    ∃ π : GaussianInt, Gaussian.IsPrimary π ∧ π.norm = p := by
  obtain ⟨π0, hirr, hmul, -⟩ := Gaussian.exists_irreducible_eq_mul_star (Fact.out : p.Prime) hp
  have h := congrArg (fun x : GaussianInt => x.norm.natAbs) hmul
  simp only [Gaussian.natAbs_norm_natCast, Gaussian.natAbs_norm_mul,
    Gaussian.natAbs_norm_star] at h
  have hn : π0.norm.natAbs = p :=
    Nat.pow_left_injective (n := 2) (by norm_num) (by simpa [sq] using h.symm)
  have hnd : ¬ Gaussian.onePlusI ∣ π0 := by
    intro hd
    have := Gaussian.norm_dvd_norm hd
    rw [hn, Gaussian.norm_onePlusI] at this
    have h2 : 2 ∣ p := by simpa using this
    omega
  obtain ⟨u, ⟨hu, hprim⟩, -⟩ := Gaussian.existsUnique_isPrimary_unit_mul hirr.not_isUnit hnd
  refine ⟨u * π0, hprim, ?_⟩
  have h1 : (u * π0).norm.natAbs = p := by
    rw [Gaussian.natAbs_norm_mul, Gaussian.isUnit_iff_natAbs_norm.1 hu, hn, one_mul]
  rw [← Gaussian.natAbs_norm, h1]

/-- If `N = P + 1 - (z + z̄)` with `|z|² = P` then `|N - (P + 1)| ≤ 2 √P`. -/
lemma abs_sub_le_aux (N P : ℕ) (z : GaussianInt)
    (hH : ((N : ℤ) : GaussianInt) = P + 1 - (z + star z)) (hz : z.norm.natAbs = P) :
    |(N : ℝ) - (P + 1)| ≤ 2 * Real.sqrt P := by
  have hre := congrArg Zsqrtd.re hH
  simp at hre
  have hP : (P : ℤ) = z.norm := by rw [← hz]; exact Gaussian.natAbs_norm z
  rw [Zsqrtd.norm_def] at hP
  have hz2 : z.re ^ 2 ≤ P := by nlinarith [sq_nonneg z.im]
  have hN' : (N : ℝ) - (P + 1) = -(2 * (z.re : ℝ)) := by
    have := congrArg (Int.cast : ℤ → ℝ) hre
    push_cast at this
    linarith
  rw [hN', abs_neg, abs_mul]
  have h2 : |(2 : ℝ)| = 2 := abs_of_pos two_pos
  rw [h2]
  have := Real.abs_le_sqrt (x := (z.re : ℝ)) (y := (P : ℝ)) (by exact_mod_cast hz2)
  linarith

/-- **Hasse's bound for the curves `y² = x³ - Dx`** (from `|π|² = p`, without the general Hasse
theorem): `|N_p - (p + 1)| ≤ 2 √p` for every odd prime `p ∤ D`. -/
@[kb "irelandrosen1990" "Ch. 18, §4, Theorem 5, p. 317"]
theorem abs_numPointsQuarticCurve_sub_le {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {D : ℤ}
    (hD : ¬ (p : ℤ) ∣ D) :
    |(numPointsQuarticCurve p D : ℝ) - (p + 1)| ≤ 2 * Real.sqrt p := by
  have hodd : p % 2 = 1 := ((Fact.out : p.Prime).eq_two_or_odd).resolve_left hp2
  by_cases h4 : p % 4 = 3
  · rw [numPointsQuarticCurve_of_mod_four_eq_three h4 hD]
    push_cast
    simp
  have hp1 : p % 4 = 1 := by omega
  obtain ⟨π, hπ, hπp⟩ := exists_isPrimary_norm_eq hp1
  have H := numPointsQuarticCurve_eq hp1 hπ hπp hD
  have hN : π.norm.natAbs = p := by rw [hπp, Int.natAbs_natCast]
  subst hN
  set u := Gaussian.quarticChar π D with hu
  set z : GaussianInt := star u * π with hz
  have hz' : star z = u * star π := by rw [hz, star_mul', star_star]
  have hDne : (D : ZMod π.norm.natAbs) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hunit : IsUnit u := by
    rw [hu, ← Gaussian.quarticMulChar_intCast hp2]
    exact Gaussian.isUnit_quarticMulChar hp2 hDne
  have hznorm : z.norm.natAbs = π.norm.natAbs := by
    rw [hz, Gaussian.natAbs_norm_mul, Gaussian.natAbs_norm_star,
      Gaussian.isUnit_iff_natAbs_norm.1 hunit, one_mul]
  have H' : ((numPointsQuarticCurve π.norm.natAbs D : ℤ) : GaussianInt) =
      π.norm.natAbs + 1 - (z + star z) := by
    rw [H, hz']; ring
  exact abs_sub_le_aux _ _ z H' hznorm

end NTKB.IrelandRosen
