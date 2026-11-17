/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.IrelandRosen.R5.LocalPolynomial
import NTKB.Attr

/-!
# Infinitely many rational points (Ireland–Rosen, Propositions 17.9.1 and 17.10.1)

* **Proposition 17.10.1**: `y² = x³ + k`, `k` sixth-power free, `k ≠ 1, -432`, with a rational point
  `(x, y)`, `xy ≠ 0`, has infinitely many rational points (`infinite_points_mordell_of_input`);
* **Proposition 17.9.1**: `x³ + y³ = a`, `a > 2` cube free, with one rational point has infinitely
  many (`infinite_points_sum_cubes_of_input`), through the birational map
  `(x, y) ↦ (12a/(x + y), 36a(x - y)/(x + y))` to `Y² = X³ - 432a²`.

Both are proved from the named input `MordellTorsionInput` (Fueter 1930): a rational point
`(x, y)` with `xy ≠ 0` of finite order on `y² = x³ + k` occurs only for `k = d⁶` or `k = -432 d⁶`.
Then the point has infinite order and its multiples are pairwise distinct. The input follows from
the Nagell–Lutz theorem (proved in Tau Ceti, `WeierstrassCurve.lutz_nagell`, not ported: about
eight thousand lines on another Mathlib) and a finite case analysis.
-/

namespace NTKB.IrelandRosen.CM

open WeierstrassCurve

/-- The Mordell curve `y² = x³ + k` over `ℚ`. -/
def mordellCurve (k : ℤ) : WeierstrassCurve ℚ := ⟨0, 0, 0, 0, k⟩

lemma mordellCurve_Δ (k : ℤ) : (mordellCurve k).Δ = -432 * (k : ℚ) ^ 2 := by
  simp only [mordellCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

lemma mordellCurve_equation_iff (k : ℤ) (x y : ℚ) :
    (mordellCurve k).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 + k := by
  rw [Affine.equation_iff]
  simp only [mordellCurve]
  constructor <;> intro h <;> linear_combination h

/-- **Fueter's theorem on the torsion of Mordell curves** (named input; Fueter 1930, see Cassels,
*Lectures on Elliptic Curves*, §14): a rational point `(x, y)` with `xy ≠ 0` of finite order on
`y² = x³ + k` exists only if `k = d⁶` (the points `(2d², ±3d³)` of order `6`) or `k = -432 d⁶` (the
points `(12d², ±36d³)` of order `3`). -/
structure MordellTorsionInput : Prop where
  out : ∀ (k : ℤ) (x y : ℚ) (h : (mordellCurve k).toAffine.Nonsingular x y), x ≠ 0 → y ≠ 0 →
    IsOfFinAddOrder (Affine.Point.some x y h) → ∃ d : ℤ, k = d ^ 6 ∨ k = -432 * d ^ 6

/-- A point of infinite order gives infinitely many rational points. -/
theorem infinite_points_of_not_isOfFinAddOrder {k : ℤ} (hk : k ≠ 0) {x y : ℚ}
    (h : (mordellCurve k).toAffine.Nonsingular x y)
    (hinf : ¬ IsOfFinAddOrder (Affine.Point.some x y h)) :
    {p : ℚ × ℚ | p.2 ^ 2 = p.1 ^ 3 + k}.Infinite := by
  have hΔ : (mordellCurve k).Δ ≠ 0 := by
    rw [mordellCurve_Δ]
    have : (k : ℚ) ≠ 0 := by exact_mod_cast hk
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ this)
  have hP : Infinite (mordellCurve k).toAffine.Point :=
    Infinite.of_injective _ (injective_nsmul_iff_not_isOfFinAddOrder.2 hinf)
  have hO : Infinite (Option (AffineSolutions (mordellCurve k))) :=
    Infinite.of_injective _ (pointEquivOption _ hΔ).injective
  have hS : Infinite (AffineSolutions (mordellCurve k)) := by
    by_contra hfin
    rw [not_infinite_iff_finite] at hfin
    exact not_finite (Option (AffineSolutions (mordellCurve k)))
  have hset : {p : ℚ × ℚ | p.2 ^ 2 = p.1 ^ 3 + k} =
      {p : ℚ × ℚ | (mordellCurve k).toAffine.Equation p.1 p.2} := by
    ext p; simp [mordellCurve_equation_iff]
  rw [hset, ← Set.infinite_coe_iff]
  exact hS

/-- **Ireland–Rosen, Proposition 17.10.1**, from `MordellTorsionInput`. Let `k ≠ 0` be sixth-power
free, `k ≠ 1, -432`. If `y² = x³ + k` has a rational solution with `xy ≠ 0`, it has infinitely
many rational solutions. -/
@[kb "irelandrosen1990" "Prop 17.10.1, p. 300"]
theorem infinite_points_mordell_of_input (hin : MordellTorsionInput) {k : ℤ} (hk0 : k ≠ 0)
    (hk : ∀ d : ℤ, d ^ 6 ∣ k → IsUnit d) (hk1 : k ≠ 1) (hk432 : k ≠ -432) {x y : ℚ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : y ^ 2 = x ^ 3 + k) :
    {p : ℚ × ℚ | p.2 ^ 2 = p.1 ^ 3 + k}.Infinite := by
  have hΔ : (mordellCurve k).Δ ≠ 0 := by
    rw [mordellCurve_Δ]
    have : (k : ℚ) ≠ 0 := by exact_mod_cast hk0
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ this)
  have h : (mordellCurve k).toAffine.Nonsingular x y :=
    ((mordellCurve k).toAffine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).1
      ((mordellCurve_equation_iff k x y).2 hxy)
  refine infinite_points_of_not_isOfFinAddOrder hk0 h fun hfin => ?_
  obtain ⟨d, hd | hd⟩ := hin.out k x y h hx hy hfin
  · have hu := hk d ⟨1, by rw [hd, mul_one]⟩
    rcases Int.isUnit_iff.1 hu with rfl | rfl <;> exact hk1 (by rw [hd]; norm_num)
  · have hu := hk d ⟨-432, by rw [hd]; ring⟩
    rcases Int.isUnit_iff.1 hu with rfl | rfl <;> exact hk432 (by rw [hd]; norm_num)

/-! ### Sums of two cubes -/

lemma add_ne_zero_of_cubes {a : ℤ} (ha : a ≠ 0) {x y : ℚ} (h : x ^ 3 + y ^ 3 = a) : x + y ≠ 0 := by
  intro hs
  have : y = -x := by linarith
  rw [this] at h
  have : (a : ℚ) = 0 := by rw [← h]; ring
  exact ha (by exact_mod_cast this)

/-- The map `(x, y) ↦ (12a/(x + y), 36a(x - y)/(x + y))` from `x³ + y³ = a` to `Y² = X³ - 432a²`. -/
noncomputable def cubesToMordell (a : ℤ) (p : ℚ × ℚ) : ℚ × ℚ :=
  (12 * a / (p.1 + p.2), 36 * a * (p.1 - p.2) / (p.1 + p.2))

lemma cubesToMordell_mem {a : ℤ} (ha : a ≠ 0) {p : ℚ × ℚ} (h : p.1 ^ 3 + p.2 ^ 3 = a) :
    (cubesToMordell a p).2 ^ 2 = (cubesToMordell a p).1 ^ 3 + ((-432 * a ^ 2 : ℤ) : ℚ) := by
  have hs := add_ne_zero_of_cubes ha h
  simp only [cubesToMordell]
  push_cast
  rw [← h]
  field_simp
  ring

/-- The inverse map `(X, Y) ↦ ((36a + Y)/(6X), (36a - Y)/(6X))`. -/
noncomputable def mordellToCubes (a : ℤ) (q : ℚ × ℚ) : ℚ × ℚ :=
  ((36 * a + q.2) / (6 * q.1), (36 * a - q.2) / (6 * q.1))

lemma mordellToCubes_cubesToMordell {a : ℤ} (ha : a ≠ 0) {p : ℚ × ℚ} (h : p.1 ^ 3 + p.2 ^ 3 = a) :
    mordellToCubes a (cubesToMordell a p) = p := by
  have hs := add_ne_zero_of_cubes ha h
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  simp only [mordellToCubes, cubesToMordell]
  ext <;> field_simp <;> ring

lemma mordellToCubes_mem {a : ℤ} {q : ℚ × ℚ} (hX : q.1 ≠ 0)
    (h : q.2 ^ 2 = q.1 ^ 3 + ((-432 * a ^ 2 : ℤ) : ℚ)) :
    (mordellToCubes a q).1 ^ 3 + (mordellToCubes a q).2 ^ 3 = a := by
  simp only [mordellToCubes]
  push_cast at h
  field_simp
  linear_combination (216 * (a : ℚ)) * h

lemma cubesToMordell_mordellToCubes {a : ℤ} (ha : a ≠ 0) {q : ℚ × ℚ} (hX : q.1 ≠ 0) :
    cubesToMordell a (mordellToCubes a q) = q := by
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have hs : (36 * a + q.2) / (6 * q.1) + (36 * a - q.2) / (6 * q.1) = 12 * a / q.1 := by
    field_simp; ring
  simp only [cubesToMordell, mordellToCubes, hs]
  ext
  · field_simp
  · field_simp; ring

/-- A rational number whose cube is an integer is an integer. -/
lemma exists_int_of_cube_eq_int {r : ℚ} {m : ℤ} (h : r ^ 3 = m) : ∃ n : ℤ, r = n := by
  have hd : r.den ^ 3 = 1 := by
    rw [← Rat.den_pow, h, Rat.den_intCast]
  have h1 : r.den = 1 := by
    have := Nat.pow_eq_one.1 hd
    omega
  exact ⟨r.num, (Rat.den_eq_one_iff r).1 h1 |>.symm⟩

/-- `x³ + y³ = a`, `(x + y)³ = 4a` is impossible for cube-free `a > 2`. -/
lemma cube_free_absurd {a : ℤ} (ha : 2 < a) (hcf : ∀ d : ℤ, d ^ 3 ∣ a → IsUnit d) {x y : ℚ}
    (hxy : x ^ 3 + y ^ 3 = a) (h4 : (x + y) ^ 3 = 4 * a) : False := by
  have hxyeq : x = y := by
    have h1 : (x + y) * (3 * x * y - (x + y) ^ 2 * (3 / 4)) = 0 := by
      linear_combination (-1 : ℚ) * hxy + (1 / 4 : ℚ) * h4
    have hs : x + y ≠ 0 := by
      intro hs; rw [hs] at h4
      have : (a : ℚ) = 0 := by linarith
      have : a = 0 := by exact_mod_cast this
      omega
    have h2 := (mul_eq_zero.1 h1).resolve_left hs
    have : (x - y) ^ 2 = 0 := by linear_combination (-4 / 3 : ℚ) * h2
    exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 this)
  subst hxyeq
  have h8 : (2 * x) ^ 3 = ((4 * a : ℤ) : ℚ) := by push_cast; linear_combination 4 * hxy
  obtain ⟨m, hm⟩ := exists_int_of_cube_eq_int h8
  have hm3 : m ^ 3 = 4 * a := by
    have : ((m ^ 3 : ℤ) : ℚ) = ((4 * a : ℤ) : ℚ) := by rw [← h8, hm]; push_cast; ring
    exact_mod_cast this
  have hm2 : 2 ∣ m := by
    have : (2 : ℤ) ∣ m ^ 3 := ⟨2 * a, by rw [hm3]; ring⟩
    exact Int.prime_two.dvd_of_dvd_pow this
  obtain ⟨n, rfl⟩ := hm2
  have han : a = 2 * n ^ 3 := by linarith [hm3, show (2 * n) ^ 3 = 8 * n ^ 3 by ring]
  have hu := hcf n ⟨2, by rw [han]; ring⟩
  rcases Int.isUnit_iff.1 hu with rfl | rfl <;> omega

/-- **Ireland–Rosen, Proposition 17.9.1**, from `MordellTorsionInput`. Let `a > 2` be cube free.
If `x³ + y³ = a` has a rational solution, it has infinitely many. -/
@[kb "irelandrosen1990" "Prop 17.9.1, p. 298"]
theorem infinite_points_sum_cubes_of_input (hin : MordellTorsionInput) {a : ℤ} (ha : 2 < a)
    (hcf : ∀ d : ℤ, d ^ 3 ∣ a → IsUnit d) {x y : ℚ} (hxy : x ^ 3 + y ^ 3 = a) :
    {p : ℚ × ℚ | p.1 ^ 3 + p.2 ^ 3 = a}.Infinite := by
  have ha0 : a ≠ 0 := by omega
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha0
  set k : ℤ := -432 * a ^ 2 with hk
  have hkneg : k < 0 := by rw [hk]; nlinarith [sq_pos_of_ne_zero ha0]
  have hk0 : k ≠ 0 := hkneg.ne
  set q := cubesToMordell a (x, y) with hq
  have hs := add_ne_zero_of_cubes ha0 hxy
  have hqmem : q.2 ^ 2 = q.1 ^ 3 + (k : ℚ) := cubesToMordell_mem ha0 (p := (x, y)) hxy
  have hΔ : (mordellCurve k).Δ ≠ 0 := by
    rw [mordellCurve_Δ]
    have : (k : ℚ) ≠ 0 := by exact_mod_cast hk0
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ this)
  have hns : (mordellCurve k).toAffine.Nonsingular q.1 q.2 :=
    ((mordellCurve k).toAffine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).1
      ((mordellCurve_equation_iff k _ _).2 hqmem)
  have hq1 : q.1 ≠ 0 := by
    simp only [hq, cubesToMordell]; exact div_ne_zero (mul_ne_zero (by norm_num) ha') hs
  -- the point has infinite order
  have hinf : ¬ IsOfFinAddOrder (Affine.Point.some q.1 q.2 hns) := by
    intro hfin
    by_cases hq2 : q.2 = 0
    · -- `y = 0`: `(12a/(x+y))³ = 432 a²`, i.e. `(x + y)³ = 4a`
      have h3 : q.1 ^ 3 = 432 * (a : ℚ) ^ 2 := by
        have := hqmem; rw [hq2, hk] at this; push_cast at this; linarith
      have hxy' : (x + y) ^ 3 = 4 * a := by
        have e : q.1 = 12 * a / (x + y) := rfl
        rw [e, div_pow] at h3
        rw [div_eq_iff (pow_ne_zero _ hs)] at h3
        have : (a : ℚ) ^ 2 * (1728 * a - 432 * (x + y) ^ 3) = 0 := by linear_combination h3
        rcases mul_eq_zero.1 this with h | h
        · exact absurd (pow_eq_zero_iff (by norm_num) |>.1 h) ha'
        · linarith
      exact cube_free_absurd ha hcf hxy hxy'
    · obtain ⟨d, hd | hd⟩ := hin.out k q.1 q.2 hns hq1 hq2 hfin
      · have : 0 ≤ d ^ 6 := by positivity
        omega
      · have h2 : a ^ 2 = (d ^ 3) ^ 2 := by
          have : -432 * a ^ 2 = -432 * d ^ 6 := by rw [← hk, hd]
          have h6 : a ^ 2 = d ^ 6 := by linarith
          rw [h6]; ring
        rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h
        · have hu := hcf d ⟨1, by rw [h, mul_one]⟩
          rcases Int.isUnit_iff.1 hu with rfl | rfl <;> norm_num at h <;> omega
        · have hu := hcf d ⟨-1, by rw [h]; ring⟩
          rcases Int.isUnit_iff.1 hu with rfl | rfl <;> norm_num at h <;> omega
  have hInf := infinite_points_of_not_isOfFinAddOrder hk0 hns hinf
  -- transport back: every point of `Y² = X³ + k` is the image of a point of `x³ + y³ = a`
  by_contra hfin
  rw [Set.not_infinite] at hfin
  apply hInf
  refine (hfin.image (cubesToMordell a)).subset fun Q hQ => ?_
  have hQ' : Q.2 ^ 2 = Q.1 ^ 3 + (k : ℚ) := hQ
  have hX : Q.1 ≠ 0 := by
    intro h0
    rw [h0] at hQ'
    have : (k : ℚ) < 0 := by exact_mod_cast hkneg
    nlinarith [sq_nonneg Q.2]
  refine ⟨mordellToCubes a Q, mordellToCubes_mem hX (by rw [← hk]; exact hQ'),
    cubesToMordell_mordellToCubes ha0 hX⟩

end NTKB.IrelandRosen.CM
