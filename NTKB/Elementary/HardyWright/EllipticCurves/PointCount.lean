/-
# Hardy–Wright §25.6: counting points on an elliptic curve over `𝔽_p`

For a Weierstrass curve over a finite field `F` of odd characteristic, completing the square
gives `(2y + a₁x + a₃)² = 4x³ + b₂x² + 2b₄x + b₆`, hence the number of affine solutions is
`q + ∑ₓ χ(4x³ + b₂x² + 2b₄x + b₆)` with `χ` the quadratic character, and
`#E(F) = q + 1 + ∑ₓ χ(4x³ + b₂x² + 2b₄x + b₆)` (the extra `1` is the point at infinity).
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import NTKB.Attr

namespace NTKB.HardyWright

open WeierstrassCurve

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

open scoped Classical in
/-- Number of affine solutions of a Weierstrass equation over a finite field of odd characteristic,
by completing the square: `(2y + a₁x + a₃)² = 4x³ + b₂x² + 2b₄x + b₆`. -/
theorem card_equation_eq (hF : ringChar F ≠ 2) (W : WeierstrassCurve F) :
    ((Finset.univ.filter fun xy : F × F => W.toAffine.Equation xy.1 xy.2).card : ℤ) =
      Fintype.card F + ∑ x : F, quadraticChar F (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have h4 : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have key : ∀ x : F, (Finset.univ.filter fun y : F => W.toAffine.Equation x y).card =
      (Finset.univ.filter fun z : F => z ^ 2 =
        4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆).card := by
    intro x
    refine Finset.card_bij (fun y _ => 2 * y + W.a₁ * x + W.a₃) ?_ ?_ ?_
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      rw [W.toAffine.equation_iff] at hy
      simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
      linear_combination 4 * hy
    · intro a _ b _ h
      have : 2 * a = 2 * b := by linear_combination h
      exact mul_left_cancel₀ h2 this
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
      refine ⟨(z - W.a₁ * x - W.a₃) / 2, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [W.toAffine.equation_iff]
        simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆] at hz
        apply mul_left_cancel₀ h4
        field_simp
        linear_combination hz
      · field_simp
        ring
  have hx : ∀ x : F, ((Finset.univ.filter fun y : F => W.toAffine.Equation x y).card : ℤ) =
      1 + quadraticChar F (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) := by
    intro x
    rw [key x]
    have := quadraticChar_card_sqrts hF (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)
    have e : (Finset.univ.filter fun z : F => z ^ 2 =
        4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) =
        {z : F | z ^ 2 = 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆}.toFinset := by
      ext z; simp
    rw [e, this]
    ring
  have hc : (Finset.univ.filter fun xy : F × F => W.toAffine.Equation xy.1 xy.2).card =
      ∑ x : F, (Finset.univ.filter fun y : F => W.toAffine.Equation x y).card := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.card_filter]
  rw [hc]
  push_cast
  rw [Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_add_distrib]
  simp

open scoped Classical in
/-- **Hardy–Wright §25.6.** For an elliptic curve over a finite field of odd characteristic,
`#E(F) = q + 1 + ∑ₓ χ(4x³ + b₂x² + 2b₄x + b₆)`. -/
@[kb "hardywright2008" "§25.6, p. 592"]
theorem natCard_point_eq (hF : ringChar F ≠ 2) (W : WeierstrassCurve F) [W.IsElliptic] :
    (Nat.card W.toAffine.Point : ℤ) =
      Fintype.card F + 1 + ∑ x : F, quadraticChar F (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) := by
  have e := Nat.card_congr (W.toAffine.pointEquiv)
  have e2 : Nat.card (WithZero {xy : F × F // W.toAffine.Equation xy.1 xy.2}) =
      Nat.card {xy : F × F // W.toAffine.Equation xy.1 xy.2} + 1 := by
    change Nat.card (Option _) = _
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_option]
  have e3 : Nat.card {xy : F × F // W.toAffine.Equation xy.1 xy.2} =
      (Finset.univ.filter fun xy : F × F => W.toAffine.Equation xy.1 xy.2).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [e, e2, e3]
  push_cast
  rw [card_equation_eq hF W]
  ring

/-- **Hardy–Wright §25.6**, short Weierstrass form `y² = x³ + Ax + B` over `𝔽_p`, `p` odd,
`4A³ + 27B² ≠ 0`: `#E(𝔽_p) = p + 1 + ∑ₓ ((x³ + Ax + B)/p)`. -/
@[kb "hardywright2008" "§25.6, p. 592"]
theorem natCard_point_short_eq {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (A B : ZMod p)
    (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) :
    (Nat.card (WeierstrassCurve.mk 0 0 0 A B).toAffine.Point : ℤ) =
      p + 1 + ∑ x : ZMod p, legendreSym p (x ^ 3 + A * x + B).val := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp
  have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero hF
  have hΔ' : (WeierstrassCurve.mk 0 0 0 A B : WeierstrassCurve (ZMod p)).Δ ≠ 0 := by
    have : (WeierstrassCurve.mk 0 0 0 A B : WeierstrassCurve (ZMod p)).Δ =
        -(2 ^ 4) * (4 * A ^ 3 + 27 * B ^ 2) := by
      simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      ring
    rw [this]
    exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ h2)) hΔ
  have : (WeierstrassCurve.mk 0 0 0 A B : WeierstrassCurve (ZMod p)).IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr hΔ'⟩
  rw [natCard_point_eq hF]
  rw [ZMod.card, add_right_inj]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h4 : (4 * x ^ 3 + (WeierstrassCurve.mk 0 0 0 A B : WeierstrassCurve (ZMod p)).b₂ * x ^ 2 +
      2 * (WeierstrassCurve.mk 0 0 0 A B : WeierstrassCurve (ZMod p)).b₄ * x +
      (WeierstrassCurve.mk 0 0 0 A B : WeierstrassCurve (ZMod p)).b₆) =
      2 ^ 2 * (x ^ 3 + A * x + B) := by
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    ring
  rw [h4, map_mul, quadraticChar_sq_one' h2, one_mul, legendreSym]
  simp
