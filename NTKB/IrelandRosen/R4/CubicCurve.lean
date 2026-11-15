/-
Ireland–Rosen, Chapter 18, §3: the curve `y² = x³ + D` over `𝔽_p`.
-/
import NTKB.IrelandRosen.R4.CubicJacobi
import NTKB.IrelandRosen.R4.JacobiQuadratic
import NTKB.IrelandRosen.R4.QuarticCurve
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# `y² = x³ + D`, the local case (Ireland–Rosen, Chapter 18, §3, Theorem 4)

`N_p = 1 + N(y² = x³ + D)` (one point at infinity). If `p ≡ 2 (mod 3)`, `N_p = p + 1`. If
`p ≡ 1 (mod 3)`, `p = π π̄` with `π` primary, then
`N_p = p + 1 + conj((4D/π)₆) π + (4D/π)₆ π̄`, where `(a/π)₆` is the sixth power residue symbol,
`(a/π)₆ ≡ a^{(p-1)/6} (mod π)`; here `(a/π)₆ = (a/p) χ_π(a)²` (`sexticChar`), since its cube is
the Legendre symbol and its square is `χ_π(a)`. The book's proof: count by characters,
`N(y² = x³ + D) = p + ρχ(D) J(ρ, χ) + conj`, then `J(ρ, χ) = χ(4) J(χ, χ)` (the Lemma of §3) and
`J(χ_π, χ_π) = π` (Lemma 1 of Chapter 9, §4). Corollary: `|N_p - p - 1| ≤ 2√p`.
-/

namespace NTKB.IrelandRosen

open NTKB.HardyWright QuadraticAlgebra
open scoped Finset

local notation "ℤ[ω]" => NTKB.HardyWright.ZRho

/-- `N_p` for the curve `y² = x³ + D` over `𝔽_p`: the affine solutions and the point at infinity. -/
noncomputable def numPointsCubicCurve (p : ℕ) [NeZero p] (D : ℤ) : ℕ :=
  1 + (Finset.univ.filter fun xy : ZMod p × ZMod p => xy.2 ^ 2 = xy.1 ^ 3 + D).card

namespace Eisenstein

/-- The sixth power residue symbol `(a/π)₆ = (a/p) χ_π(a)²` for a prime `π` of norm `p`; `(a/p)`
is Mathlib's `jacobiSym`, the Legendre symbol when `p` is prime. -/
noncomputable def sexticChar (π : ℤ[ω]) (a : ℤ) : ℤ[ω] :=
  ((jacobiSym a (norm π).natAbs : ℤ) : ℤ[ω]) * cubicChar π a ^ 2

/-- `(a/π)₆ ≡ a^{(p-1)/6} (mod π)`, the book's definition of the sixth power residue symbol. -/
theorem sexticChar_spec {π : ℤ[ω]} (hp : (norm π).natAbs.Prime) (h3 : (norm π).natAbs ≠ 3)
    {a : ℤ} (ha : ¬ π ∣ (a : ℤ[ω])) :
    π ∣ (a : ℤ[ω]) ^ (((norm π).natAbs - 1) / 6) - sexticChar π a := by
  have hπ : Prime π := prime_of_natAbs_norm_prime hp
  have := Fact.mk hp
  have hq3 := natAbs_norm_mod_three hπ h3
  obtain ⟨k, hk⟩ : ∃ k, (norm π).natAbs - 1 = 6 * k := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact ⟨((norm π).natAbs - 1) / 6, by omega⟩
  have hcexp : cexp π = 2 * k := by rw [cexp]; omega
  have hk' : ((norm π).natAbs - 1) / 6 = k := by omega
  have hhalf : (norm π).natAbs / 2 = 3 * k := by omega
  rw [hk', ← toZMod_eq_zero_iff hp, map_sub, sub_eq_zero]
  have hA : toZMod hp (a : ℤ[ω]) ≠ 0 := fun h => ha ((toZMod_eq_zero_iff hp _).1 h)
  have hχ := (cubicChar_spec hπ h3 ha).2
  rw [← toZMod_eq_zero_iff hp, map_sub, sub_eq_zero, map_pow, hcexp] at hχ
  have hA' : ((a : ℤ) : ZMod (norm π).natAbs) ≠ 0 := by
    rwa [map_intCast] at hA
  have hE := legendreSym.eq_pow (norm π).natAbs a
  rw [hhalf, jacobiSym.legendreSym.to_jacobiSym] at hE
  have h1 := ZMod.pow_card_sub_one_eq_one hA'
  rw [hk] at h1
  simp only [sexticChar, map_mul, map_pow, map_intCast] at hχ ⊢
  rw [← hχ, hE]
  linear_combination (-(((a : ℤ) : ZMod (norm π).natAbs) ^ k)) * h1

/-! ### Helper lemmas: characters modulo `π` -/

lemma natAbs_norm_mod_three_of_fact (π : ℤ[ω]) [Fact (norm π).natAbs.Prime]
    (h3 : (norm π).natAbs ≠ 3) : (norm π).natAbs % 3 = 1 :=
  natAbs_norm_mod_three (prime_of_fact π) h3

lemma natAbs_norm_ne_two_of_fact (π : ℤ[ω]) [Fact (norm π).natAbs.Prime]
    (h3 : (norm π).natAbs ≠ 3) : (norm π).natAbs ≠ 2 := by
  have := natAbs_norm_mod_three_of_fact π h3
  omega

/-- The Legendre symbol modulo `p = N π`, as a `ℤ[ω]`-valued multiplicative character. -/
noncomputable abbrev quadMulChar (π : ℤ[ω]) [Fact (norm π).natAbs.Prime] :
    MulChar (ZMod (norm π).natAbs) ℤ[ω] :=
  (quadraticChar (ZMod (norm π).natAbs)).ringHomComp (Int.castRingHom ℤ[ω])

lemma quadMulChar_apply (π : ℤ[ω]) [Fact (norm π).natAbs.Prime] (a : ZMod (norm π).natAbs) :
    quadMulChar π a = ((quadraticChar (ZMod (norm π).natAbs) a : ℤ) : ℤ[ω]) := rfl

lemma star_quadMulChar (π : ℤ[ω]) [Fact (norm π).natAbs.Prime] (a : ZMod (norm π).natAbs) :
    star (quadMulChar π a) = quadMulChar π a := by
  rw [quadMulChar_apply]; exact star_intCast _

lemma sum_quadMulChar (π : ℤ[ω]) [Fact (norm π).natAbs.Prime] (h3 : (norm π).natAbs ≠ 3) :
    ∑ w : ZMod (norm π).natAbs, quadMulChar π w = 0 := by
  have h := quadraticChar_sum_zero
    (ringChar_zmod_ne_two (natAbs_norm_ne_two_of_fact π h3))
  have : ∑ w : ZMod (norm π).natAbs, quadMulChar π w =
      ((∑ w : ZMod (norm π).natAbs, quadraticChar (ZMod (norm π).natAbs) w : ℤ) : ℤ[ω]) := by
    rw [Int.cast_sum]; rfl
  rw [this, h, Int.cast_zero]

lemma quadMulChar_four (π : ℤ[ω]) [Fact (norm π).natAbs.Prime] (h3 : (norm π).natAbs ≠ 3) :
    quadMulChar π 4 = 1 := by
  have h2 : (2 : ZMod (norm π).natAbs) ≠ 0 :=
    Ring.two_ne_zero (ringChar_zmod_ne_two (natAbs_norm_ne_two_of_fact π h3))
  rw [quadMulChar_apply, show (4 : ZMod (norm π).natAbs) = 2 ^ 2 by norm_num,
    quadraticChar_sq_one' h2, Int.cast_one]

lemma four_ne_zero_of_fact (π : ℤ[ω]) [Fact (norm π).natAbs.Prime] (h3 : (norm π).natAbs ≠ 3) :
    (4 : ZMod (norm π).natAbs) ≠ 0 := by
  have h2 : (2 : ZMod (norm π).natAbs) ≠ 0 :=
    Ring.two_ne_zero (ringChar_zmod_ne_two (natAbs_norm_ne_two_of_fact π h3))
  rw [show (4 : ZMod (norm π).natAbs) = 2 * 2 by norm_num]
  exact mul_ne_zero h2 h2

section Chars

variable {π : ℤ[ω]} [Fact (norm π).natAbs.Prime] (h3 : (norm π).natAbs ≠ 3)

lemma cubicMulChar_apply_pow_three {a : ZMod (norm π).natAbs} (ha : a ≠ 0) :
    cubicMulChar π h3 a ^ 3 = 1 := by
  have := congrArg (fun ψ : MulChar (ZMod (norm π).natAbs) ℤ[ω] => ψ a)
    (cubicMulChar_pow_three h3)
  simp only [MulChar.pow_apply' _ (by norm_num : (3 : ℕ) ≠ 0)] at this
  rw [this]; exact MulChar.one_apply (isUnit_iff_ne_zero.2 ha)

lemma star_cubicMulChar (a : ZMod (norm π).natAbs) :
    star (cubicMulChar π h3 a) = cubicMulChar π h3 a ^ 2 := by
  by_cases ha : a = 0
  · subst ha; rw [MulChar.map_zero]; simp
  · exact star_eq_sq_of_pow_three (cubicMulChar_apply_pow_three h3 ha)

lemma cubicMulChar_neg_one : cubicMulChar π h3 (-1) = 1 := by
  have h1 := cubicMulChar_apply_pow_three h3 (neg_ne_zero.2 (one_ne_zero (α := ZMod (norm π).natAbs)))
  have h2 : cubicMulChar π h3 (-1) ^ 2 = 1 := by
    rw [← map_pow, neg_one_sq, map_one]
  linear_combination h1 - (cubicMulChar π h3 (-1)) * h2

/-- The number of solutions of `x³ = w` is `∑_{j<3} χ^j(w)` (Ireland–Rosen, Prop. 8.1.5), as an
element of `ℤ[ω]`. -/
lemma numSolPow_three_eq (w : ZMod (norm π).natAbs) :
    ((numSolPow 3 w : ℕ) : ℤ[ω]) =
      ∑ j ∈ Finset.range 3, bookChar (cubicMulChar π h3 ^ j) w := by
  have hdvd : 3 ∣ Fintype.card (ZMod (norm π).natAbs) - 1 := by
    rw [ZMod.card]
    have := natAbs_norm_mod_three_of_fact π h3
    omega
  have hord := orderOf_cubicMulChar_ringHomComp h3 toComplex (by norm_num)
  have H := numSolPow_eq_sum_range hdvd hord w
  apply toComplex_injective
  rw [map_natCast, map_sum, H]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by
    simp only [Finset.mem_range] at hj; omega
  rcases hj' with rfl | hj' | hj'
  · rw [pow_zero, pow_zero, bookChar_one, bookChar_one, map_one]
  · have hne : cubicMulChar π h3 ^ j ≠ 1 := by
      rw [hj', pow_one]; exact cubicMulChar_ne_one h3
    have hne' : ((cubicMulChar π h3).ringHomComp toComplex) ^ j ≠ 1 := by
      rw [hj']
      exact pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hord]; norm_num)
    rw [bookChar_of_ne_one hne, bookChar_of_ne_one hne', MulChar.ringHomComp_pow,
      MulChar.ringHomComp_apply]
  · have hne : cubicMulChar π h3 ^ j ≠ 1 := by
      rw [hj']; exact cubicMulChar_sq_ne_one h3
    have hne' : ((cubicMulChar π h3).ringHomComp toComplex) ^ j ≠ 1 := by
      rw [hj']
      exact pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hord]; norm_num)
    rw [bookChar_of_ne_one hne, bookChar_of_ne_one hne', MulChar.ringHomComp_pow,
      MulChar.ringHomComp_apply]

/-- `#{(x,y) | y² = x³ + D}` as `∑_w (1 + ρ(w)) (1 + χ(w - D) + χ²(w - D))` in `ℤ[ω]`. -/
lemma card_cubicCurve_eq_sum (D : ZMod (norm π).natAbs) :
    ((#{xy : ZMod (norm π).natAbs × ZMod (norm π).natAbs | xy.2 ^ 2 = xy.1 ^ 3 + D} : ℕ) :
        ℤ[ω]) =
      ∑ x : ZMod (norm π).natAbs, (1 + quadMulChar π x) *
        (1 + cubicMulChar π h3 (x + -D) + cubicMulChar π h3 (x + -D) ^ 2) := by
  have hF := ringChar_zmod_ne_two (natAbs_norm_ne_two_of_fact π h3)
  have h := card_filter_prod (fun x y : ZMod (norm π).natAbs => y ^ 2 = x ^ 3 + D)
  beta_reduce at h
  rw [h]
  have e1 : ∀ y : ZMod (norm π).natAbs,
      #{x : ZMod (norm π).natAbs | y ^ 2 = x ^ 3 + D} = numSolPow 3 (y ^ 2 + -D) := by
    intro y
    rw [← card_pow_eq_numSolPow]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> intro h' <;> linear_combination -h'
  simp_rw [e1]
  rw [Nat.cast_sum]
  have hs := sum_comp_pow_eq 2 (fun w : ZMod (norm π).natAbs =>
    ((numSolPow 3 (w + -D) : ℕ) : ℤ[ω]))
  rw [hs]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hc := congrArg (Int.cast : ℤ → ℤ[ω]) (card_sqrts_int hF x)
  push_cast at hc
  rw [nsmul_eq_mul, hc, numSolPow_three_eq h3]
  have hb1 : ∀ t : ZMod (norm π).natAbs, bookChar (cubicMulChar π h3) t = cubicMulChar π h3 t :=
    fun t => bookChar_of_ne_one (cubicMulChar_ne_one h3) t
  have hb2 : ∀ t : ZMod (norm π).natAbs,
      bookChar (cubicMulChar π h3 ^ 2) t = cubicMulChar π h3 t ^ 2 := fun t => by
    rw [bookChar_of_ne_one (cubicMulChar_sq_ne_one h3), MulChar.pow_apply' _ (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, bookChar_one,
    pow_one, hb1, hb2]
  rw [quadMulChar_apply]
  ring

/-- The sum `∑_w ρ(w) χ(w - D)`, by the Lemma of §3 and `J(χ_π, χ_π) = π`. -/
lemma sexticChar_eq (D : ℤ) :
    sexticChar π (4 * D) = quadMulChar π (4 * (D : ZMod (norm π).natAbs)) *
      cubicMulChar π h3 (4 * (D : ZMod (norm π).natAbs)) ^ 2 := by
  have hj : ((jacobiSym (4 * D) (norm π).natAbs : ℤ) : ℤ[ω]) =
      quadMulChar π (((4 * D : ℤ)) : ZMod (norm π).natAbs) := by
    rw [quadMulChar_apply]
    congr 2
    exact (jacobiSym.legendreSym.to_jacobiSym _ _).symm
  rw [sexticChar, hj, ← cubicMulChar_intCast h3 (4 * D)]
  push_cast
  rfl

lemma sum_rho_chi (hP : IsPrimary π) {D : ℤ} (hD : (D : ZMod (norm π).natAbs) ≠ 0) :
    ∑ x : ZMod (norm π).natAbs, quadMulChar π x * cubicMulChar π h3 (x + -(D : ZMod _)) =
      star (sexticChar π (4 * D)) * π := by
  have hF := ringChar_zmod_ne_two (natAbs_norm_ne_two_of_fact π h3)
  have hc : -(D : ZMod (norm π).natAbs) ≠ 0 := neg_ne_zero.2 hD
  have h4 := four_ne_zero_of_fact π h3
  have h4D : 4 * (D : ZMod (norm π).natAbs) ≠ 0 := mul_ne_zero h4 hD
  rw [sum_mul_add _ _ hc, jacobiSum_quadraticChar_eq hF (cubicMulChar_ne_one h3),
    jacobiSum_cubicMulChar h3 hP, sexticChar_eq h3, neg_neg]
  set u := cubicMulChar π h3 (4 * (D : ZMod (norm π).natAbs)) with hu
  have e3 : u ^ 3 = 1 := cubicMulChar_apply_pow_three h3 h4D
  have e1 : quadMulChar π (4 * (D : ZMod (norm π).natAbs)) = quadMulChar π D := by
    rw [map_mul, quadMulChar_four π h3, one_mul]
  have e2 : cubicMulChar π h3 (-(D : ZMod (norm π).natAbs)) * cubicMulChar π h3 4 = u := by
    rw [hu, show (-(D : ZMod (norm π).natAbs)) = (-1) * D by ring]
    simp only [map_mul, cubicMulChar_neg_one h3]
    ring
  rw [star_mul', star_pow, star_cubicMulChar h3, star_quadMulChar, e1]
  linear_combination (quadMulChar π D * π) * e2 - (quadMulChar π D * u * π) * e3

include h3 in
lemma sexticChar_mul_star {D : ℤ} (hD : (D : ZMod (norm π).natAbs) ≠ 0) :
    sexticChar π (4 * D) * star (sexticChar π (4 * D)) = 1 := by
  have h4 := four_ne_zero_of_fact π h3
  have h4D : 4 * (D : ZMod (norm π).natAbs) ≠ 0 := mul_ne_zero h4 hD
  rw [sexticChar_eq h3]
  set u := cubicMulChar π h3 (4 * (D : ZMod (norm π).natAbs)) with hu
  have e3 : u ^ 3 = 1 := cubicMulChar_apply_pow_three h3 h4D
  have hρ2 : quadMulChar π (4 * (D : ZMod (norm π).natAbs)) ^ 2 = 1 := by
    rw [quadMulChar_apply, ← Int.cast_pow, quadraticChar_sq_one h4D, Int.cast_one]
  rw [star_mul', star_pow, star_cubicMulChar h3, star_quadMulChar]
  linear_combination u ^ 6 * hρ2 + (u ^ 3 + 1) * e3

include h3 in
/-- The number of points of `y² = x³ + D` over `𝔽_p`, as an element of `ℤ[ω]`
(Ireland–Rosen, Chapter 18, §3). -/
theorem card_cubicCurve_eq_complex (hP : IsPrimary π) {D : ℤ}
    (hD : ¬ ((norm π).natAbs : ℤ) ∣ D) :
    ((#{xy : ZMod (norm π).natAbs × ZMod (norm π).natAbs |
        xy.2 ^ 2 = xy.1 ^ 3 + (D : ZMod (norm π).natAbs)} : ℕ) : ℤ[ω]) =
      (norm π).natAbs + star (sexticChar π (4 * D)) * π + sexticChar π (4 * D) * star π := by
  have hDne : (D : ZMod (norm π).natAbs) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  rw [card_cubicCurve_eq_sum h3]
  set c : ZMod (norm π).natAbs := -(D : ZMod (norm π).natAbs) with hc
  have hshift : ∀ ψ : MulChar (ZMod (norm π).natAbs) ℤ[ω], ψ ≠ 1 → ∑ x, ψ (x + c) = 0 :=
    fun ψ hψ => (Equiv.sum_comp (Equiv.addRight c) (fun a => ψ a)).trans
      (MulChar.sum_eq_zero_of_ne_one hψ)
  have e : ∀ x : ZMod (norm π).natAbs,
      (1 + quadMulChar π x) *
        (1 + cubicMulChar π h3 (x + c) + cubicMulChar π h3 (x + c) ^ 2) =
      1 + cubicMulChar π h3 (x + c) + cubicMulChar π h3 (x + c) ^ 2 + quadMulChar π x +
        quadMulChar π x * cubicMulChar π h3 (x + c) +
        quadMulChar π x * cubicMulChar π h3 (x + c) ^ 2 := fun x => by ring
  simp only [e, Finset.sum_add_distrib]
  have hS1 : ∑ x : ZMod (norm π).natAbs, (1 : ℤ[ω]) = (norm π).natAbs := by
    simp [ZMod.card]
  have hS2 := hshift _ (cubicMulChar_ne_one h3)
  have hS3 : ∑ x : ZMod (norm π).natAbs, cubicMulChar π h3 (x + c) ^ 2 = 0 := by
    have : ∀ x : ZMod (norm π).natAbs,
        cubicMulChar π h3 (x + c) ^ 2 = (cubicMulChar π h3 ^ 2) (x + c) := fun x =>
      (MulChar.pow_apply' _ (by norm_num) _).symm
    simp_rw [this]
    exact hshift _ (cubicMulChar_sq_ne_one h3)
  have hS6 : ∑ x : ZMod (norm π).natAbs, quadMulChar π x * cubicMulChar π h3 (x + c) ^ 2 =
      star (∑ x : ZMod (norm π).natAbs, quadMulChar π x * cubicMulChar π h3 (x + c)) := by
    rw [star_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [star_mul', star_cubicMulChar h3, star_quadMulChar]
  rw [hS1, hS2, hS3, hS6, sum_quadMulChar π h3, sum_rho_chi h3 hP hDne, star_mul', star_star]
  ring

end Chars

/-- A prime `p ≡ 1 (mod 3)` is the norm of a primary prime of `ℤ[ω]`. -/
lemma exists_isPrimary_norm_eq {p : ℕ} (hp : p.Prime) (hp3 : p % 3 = 1) :
    ∃ π : ℤ[ω], IsPrimary π ∧ norm π = (p : ℤ) := by
  obtain ⟨π₀, hπ₀, hpπ, -⟩ := exists_prime_eq_mul_star hp hp3
  have hN₀ : (norm π₀).natAbs = p := by
    have := congrArg (fun x : ℤ[ω] => (norm x).natAbs) hpπ
    simp only [natAbs_norm_natCast, map_mul, Int.natAbs_mul, natAbs_norm_star] at this
    exact Nat.pow_left_injective two_ne_zero (show (norm π₀).natAbs ^ 2 = p ^ 2 by
      rw [sq]; linarith)
  obtain ⟨u, hu, -⟩ := existsUnique_isPrimary_unit_mul hπ₀ (by rw [hN₀]; omega)
  refine ⟨(u : ℤ[ω]) * π₀, hu, ?_⟩
  have hN : (norm ((u : ℤ[ω]) * π₀)).natAbs = p := by
    rw [map_mul, Int.natAbs_mul, qa_norm_unit, one_mul, hN₀]
  rw [← Int.natAbs_of_nonneg (rho_norm_nonneg _), hN]

/-- If `N = P + 1 + (z + z̄)` with `N z = P` then `|N - (P + 1)| ≤ 2 √P`. -/
lemma abs_sub_le_aux (N P : ℕ) (z : ℤ[ω])
    (hH : ((N : ℤ) : ℤ[ω]) = P + 1 + (z + star z)) (hz : (norm z).natAbs = P) :
    |(N : ℝ) - (P + 1)| ≤ 2 * Real.sqrt P := by
  have hre := congrArg QuadraticAlgebra.re hH
  simp [QuadraticAlgebra.re_star] at hre
  have hP : (P : ℤ) = norm z := by
    rw [← hz]; exact Int.natAbs_of_nonneg (rho_norm_nonneg z)
  rw [rho_norm] at hP
  have hsq : (2 * z.re - z.im) ^ 2 ≤ 4 * (P : ℤ) := by nlinarith [sq_nonneg z.im]
  have hN' : (N : ℝ) - (P + 1) = 2 * (z.re : ℝ) - (z.im : ℝ) := by
    have : (N : ℤ) - (P + 1) = 2 * z.re - z.im := by linarith
    have := congrArg (Int.cast : ℤ → ℝ) this
    push_cast at this
    linarith
  have hsq' : (2 * (z.re : ℝ) - (z.im : ℝ)) ^ 2 ≤ (2 * Real.sqrt P) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    have := (Int.cast_le (R := ℝ)).2 hsq
    push_cast at this
    linarith
  rw [hN']
  exact abs_le_of_sq_le_sq hsq' (by positivity)

end Eisenstein

/-- For `q ≡ 2 (mod 3)`, `x ↦ x³` is inverse to `x ↦ x ^ m` with `3 m = 2 q - 1`. -/
lemma pow_two_mul_sub_one_eq_self {p : ℕ} [Fact p.Prime] (x : ZMod p) : x ^ (2 * p - 1) = x := by
  have h2 := (Fact.out : p.Prime).two_le
  by_cases hx : x = 0
  · subst hx; rw [zero_pow (by omega)]
  · have h1 := ZMod.pow_card_sub_one_eq_one hx
    have h4 : x ^ (2 * (p - 1)) = 1 := by rw [mul_comm, pow_mul, h1, one_pow]
    have : 2 * p - 1 = 2 * (p - 1) + 1 := by omega
    rw [this, pow_succ, h4, one_mul]

/-- **Theorem 4 of Chapter 18, `p ≡ 2 (mod 3)`.** -/
@[kb "irelandrosen1990" "Ch. 18, §3, Theorem 4, p. 316"]
theorem numPointsCubicCurve_of_mod_three_eq_two {p : ℕ} [Fact p.Prime] (hp : p % 3 = 2)
    (hp2 : p ≠ 2) {D : ℤ} (hD : ¬ (p : ℤ) ∣ D) : numPointsCubicCurve p D = p + 1 := by
  obtain ⟨m, hm⟩ : ∃ m, 3 * m = 2 * p - 1 := ⟨(2 * p - 1) / 3, by omega⟩
  have hcube1 : ∀ x : ZMod p, (x ^ 3) ^ m = x := fun x => by
    rw [← pow_mul, hm]; exact pow_two_mul_sub_one_eq_self x
  have hcube2 : ∀ x : ZMod p, (x ^ m) ^ 3 = x := fun x => by
    rw [← pow_mul, mul_comm, hm]; exact pow_two_mul_sub_one_eq_self x
  have hc : (Finset.univ.filter fun xy : ZMod p × ZMod p => xy.2 ^ 2 = xy.1 ^ 3 + D).card =
      (Finset.univ : Finset (ZMod p)).card := by
    refine Finset.card_nbij' (fun xy => xy.2) (fun y => (((y ^ 2 - D) ^ m), y)) ?_ ?_ ?_ ?_
    · intro xy _
      simp
    · intro y _
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      rw [hcube2]; ring
    · intro xy hxy
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hxy
      have : xy.2 ^ 2 - D = xy.1 ^ 3 := by rw [hxy]; ring
      ext
      · simp only [this, hcube1]
      · rfl
    · intro y _
      rfl
  rw [Finset.card_univ, ZMod.card] at hc
  unfold numPointsCubicCurve
  omega

/-- **Theorem 4 of Chapter 18.** If `p ≡ 1 (mod 3)` is prime, `p = π π̄` with `π ≡ 2 (mod 3)`
primary, and `p ∤ D`, then `N_p = p + 1 + conj((4D/π)₆) π + (4D/π)₆ π̄`. -/
@[kb "irelandrosen1990" "Ch. 18, §3, Theorem 4, p. 316"]
theorem numPointsCubicCurve_eq {p : ℕ} [Fact p.Prime] (hp : p % 3 = 1) {π : ℤ[ω]}
    (hπ : Eisenstein.IsPrimary π) (hπp : norm π = p) {D : ℤ} (hD : ¬ (p : ℤ) ∣ D) :
    ((numPointsCubicCurve p D : ℤ) : ℤ[ω]) =
      p + 1 + star (Eisenstein.sexticChar π (4 * D)) * π +
        Eisenstein.sexticChar π (4 * D) * star π := by
  have hN : (norm π).natAbs = p := by rw [hπp, Int.natAbs_natCast]
  subst hN
  have h3 : (norm π).natAbs ≠ 3 := by omega
  have h := Eisenstein.card_cubicCurve_eq_complex h3 hπ hD
  unfold numPointsCubicCurve
  push_cast
  rw [h]
  ring

/-- **Hasse's bound for the curves `y² = x³ + D`** (from `|π|² = p`, without the general Hasse
theorem): `|N_p - (p + 1)| ≤ 2 √p` for every prime `p > 3`, `p ∤ D`. -/
@[kb "irelandrosen1990" "Ch. 18, §3, Theorem 4, p. 316"]
theorem abs_numPointsCubicCurve_sub_le {p : ℕ} [Fact p.Prime] (hp3 : 3 < p) {D : ℤ}
    (hD : ¬ (p : ℤ) ∣ D) :
    |(numPointsCubicCurve p D : ℝ) - (p + 1)| ≤ 2 * Real.sqrt p := by
  have hp2 : p ≠ 2 := by omega
  have hmod : p % 3 ≠ 0 := by
    intro h
    have h' := (Nat.prime_dvd_prime_iff_eq Nat.prime_three (Fact.out : p.Prime)).1
      (Nat.dvd_of_mod_eq_zero h)
    omega
  by_cases h2 : p % 3 = 2
  · rw [numPointsCubicCurve_of_mod_three_eq_two h2 hp2 hD]
    push_cast
    simp
  have h1 : p % 3 = 1 := by omega
  obtain ⟨π, hπ, hπp⟩ := Eisenstein.exists_isPrimary_norm_eq (Fact.out : p.Prime) h1
  have H := numPointsCubicCurve_eq h1 hπ hπp hD
  have hN : (norm π).natAbs = p := by rw [hπp, Int.natAbs_natCast]
  subst hN
  have h3 : (norm π).natAbs ≠ 3 := by omega
  have hDne : (D : ZMod (norm π).natAbs) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hss := Eisenstein.sexticChar_mul_star h3 hDne
  set s := Eisenstein.sexticChar π (4 * D) with hs
  have hu : IsUnit (star s) := IsUnit.of_mul_eq_one s (by rw [mul_comm]; exact hss)
  have hnorm : (norm (star s * π)).natAbs = (norm π).natAbs := by
    have := qa_norm_unit hu.unit
    rw [IsUnit.unit_spec] at this
    rw [map_mul, Int.natAbs_mul, this, one_mul]
  have H' : (((numPointsCubicCurve (norm π).natAbs D : ℕ) : ℤ) : ℤ[ω]) =
      (norm π).natAbs + 1 + (star s * π + star (star s * π)) := by
    rw [H, star_mul', star_star]; ring
  exact Eisenstein.abs_sub_le_aux _ _ _ H' hnorm

end NTKB.IrelandRosen
