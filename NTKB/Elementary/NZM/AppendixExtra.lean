/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Attr
import Mathlib.NumberTheory.Niven
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Separation.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Odds and ends of Chapter 6 and the Appendix (Niven–Zuckerman–Montgomery)

* **Theorem 6.16.**  For rational `r`, the numbers `cos (rπ)`, `sin (rπ)`, `tan (rπ)` are
  irrational apart from the listed exceptions (`cos_rat_mul_pi_irrational_or_mem` etc.).  Here
  `Real.tan x = sin x / cos x` is `0` where the cosine vanishes, so the tangent statement assumes
  `cos (rπ) ≠ 0`.
* **Lemma A.1.**  A nonconstant complex polynomial has no local minimum of `|P|` at a point where
  it does not vanish (`not_isLocalMin_norm_eval`).
* **Theorem A.4.**  For the discriminant `Polynomial.discr` of Mathlib, `D((X - r) g) = D(g) g(r)²`
  when `g` has positive degree (`discr_X_sub_C_mul`).  The statement that `D(f)` is a form of
  degree `2n - 2` with integral coefficients in the coefficients of `f` is recorded as the
  proposition `DiscrIsIntegralForm`.
* **Theorem A.5.**  Lifting of singular solutions with the discriminant
  (`lift_singular_via_discr`), for `f` of degree at least `2`; the ingredient is that `D(f)`
  modulo `pʲ` depends only on `f` modulo `pʲ` and the degree (`map_discr_eq_of_map_eq`).
  (The book's conclusion is `j > 2τ`, equivalently `j ≥ 2τ + 1`, which is what Theorem 2.24
  needs.)
-/

open Polynomial Filter Topology

namespace NTKB.NZM

/-! ## Theorem 6.16 -/

section Trig

open Real

private lemma no_rat_sq_eq_three (q : ℚ) (h : (q : ℝ) ^ 2 = 3) : False := by
  have hirr := Nat.prime_three.irrational_sqrt
  have h2 : |(q : ℝ)| = √3 := by rw [← Real.sqrt_sq_eq_abs, h]
  exact hirr ⟨|q|, by rw [Rat.cast_abs, h2]; norm_num⟩

private lemma no_rat_three_sq_eq_one (q : ℚ) (h : (q : ℝ) ^ 2 * 3 = 1) : False :=
  no_rat_sq_eq_three (3 * q) (by push_cast; linear_combination 3 * h)

/-- **Theorem 6.16** (cosine): `cos (rπ)` is irrational unless it is `0`, `±1/2`, `±1`. -/
@[kb "nivenzuckermanmontgomery" "Thm 6.16, p. 308"]
theorem cos_rat_mul_pi_irrational_or_mem (r : ℚ) :
    Irrational (cos (r * π)) ∨ cos (r * π) ∈ ({-1, -1 / 2, 0, 1 / 2, 1} : Set ℝ) := by
  by_cases h : ∃ q : ℚ, cos (r * π) = q
  · exact Or.inr (niven ⟨r, rfl⟩ h)
  · refine Or.inl fun hx => h ?_
    obtain ⟨q, hq⟩ := hx
    exact ⟨q, hq.symm⟩

/-- **Theorem 6.16** (sine): `sin (rπ)` is irrational unless it is `0`, `±1/2`, `±1`. -/
@[kb "nivenzuckermanmontgomery" "Thm 6.16, p. 308"]
theorem sin_rat_mul_pi_irrational_or_mem (r : ℚ) :
    Irrational (sin (r * π)) ∨ sin (r * π) ∈ ({-1, -1 / 2, 0, 1 / 2, 1} : Set ℝ) := by
  have h : sin (r * π) = cos (((1 / 2 - r : ℚ) : ℝ) * π) := by
    rw [← Real.cos_pi_div_two_sub]
    congr 1
    push_cast
    ring
  rw [h]
  exact cos_rat_mul_pi_irrational_or_mem _

/-- **Theorem 6.16** (tangent): if `cos (rπ) ≠ 0` then `tan (rπ)` is irrational unless it is
`0` or `±1`. -/
@[kb "nivenzuckermanmontgomery" "Thm 6.16, p. 308"]
theorem tan_rat_mul_pi_irrational_or_mem (r : ℚ) (hcos : cos (r * π) ≠ 0) :
    Irrational (tan (r * π)) ∨ tan (r * π) ∈ ({0, 1, -1} : Set ℝ) := by
  by_cases h : ∃ q : ℚ, tan (r * π) = q
  swap
  · refine Or.inl fun hx => h ?_
    obtain ⟨q, hq⟩ := hx
    exact ⟨q, hq.symm⟩
  right
  obtain ⟨q, hq⟩ := h
  have hinv := Real.inv_one_add_tan_sq hcos
  rw [hq] at hinv
  have hc2 : cos (2 * (r * π)) = 2 / (1 + (q : ℝ) ^ 2) - 1 := by
    rw [Real.cos_two_mul, ← hinv]
    ring
  have hrat : ∃ q' : ℚ, cos (2 * (r * π)) = q' :=
    ⟨2 / (1 + q ^ 2) - 1, by rw [hc2]; push_cast; ring⟩
  have hmem := niven ⟨2 * r, by push_cast; ring⟩ hrat
  rw [hq]
  have hp : (0 : ℝ) < 1 + (q : ℝ) ^ 2 := by positivity
  rcases hmem with h | h | h | h | h <;> (try rw [Set.mem_singleton_iff] at h) <;> rw [hc2] at h
  · -- cos 2θ = -1
    have : (0 : ℝ) < 2 / (1 + (q : ℝ) ^ 2) := by positivity
    linarith
  · -- cos 2θ = -1/2
    have h' : 2 / (1 + (q : ℝ) ^ 2) = 1 / 2 := by linarith
    rw [div_eq_iff hp.ne'] at h'
    exact (no_rat_sq_eq_three q (by linarith)).elim
  · -- cos 2θ = 0
    have h' : 2 / (1 + (q : ℝ) ^ 2) = 1 := by linarith
    rw [div_eq_iff hp.ne'] at h'
    have h'' : ((q : ℝ) - 1) * ((q : ℝ) + 1) = 0 := by linear_combination (-1) * h'
    rcases mul_eq_zero.mp h'' with h3 | h3
    · have : (q : ℝ) = 1 := by linarith
      simp [this]
    · have : (q : ℝ) = -1 := by linarith
      simp [this]
  · -- cos 2θ = 1/2
    have h' : 2 / (1 + (q : ℝ) ^ 2) = 3 / 2 := by linarith
    rw [div_eq_iff hp.ne'] at h'
    exact (no_rat_three_sq_eq_one q (by linarith)).elim
  · -- cos 2θ = 1
    have h' : 2 / (1 + (q : ℝ) ^ 2) = 2 := by linarith
    rw [div_eq_iff hp.ne'] at h'
    have h0 : (q : ℝ) ^ 2 = 0 := by linarith
    have : (q : ℝ) = 0 := (pow_eq_zero_iff (two_ne_zero)).mp h0
    simp [this]

end Trig

/-! ## Lemma A.1 -/

/-- **Lemma A.1.**  If `P` is a complex polynomial of degree at least one and `P z₀ ≠ 0`, then
`z₀` is not a local minimum of `|P|`. -/
@[kb "nivenzuckermanmontgomery" "Lemma A.1, p. 482"]
theorem not_isLocalMin_norm_eval (P : ℂ[X]) (hP : 0 < P.natDegree) (z₀ : ℂ)
    (h0 : P.eval z₀ ≠ 0) : ¬ IsLocalMin (fun z => ‖P.eval z‖) z₀ := by
  intro hmin
  have hdiff : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ (fun z => P.eval z) z :=
    Filter.Eventually.of_forall fun z => P.differentiableAt
  rcases Complex.eventually_eq_or_eq_zero_of_isLocalMin_norm hdiff hmin with h | h
  · have hinf : Set.Infinite {x | eval x P = eval x (C (eval z₀ P))} := by
      apply infinite_of_mem_nhds z₀
      filter_upwards [h] with z hz
      simpa using hz
    have hPC := Polynomial.eq_of_infinite_eval_eq _ _ hinf
    have hd := congrArg natDegree hPC
    simp at hd
    omega
  · exact h0 h

/-! ## Theorem A.4 -/

section Disc

variable {R : Type*} [CommRing R] [IsDomain R]

/-- **Theorem A.4** (second part): `D((X - r) g) = D(g) g(r)²` for `g` of positive degree, with
`D` Mathlib's `Polynomial.discr`.  (For constant `g` the formula fails: the discriminant of a
polynomial of degree at most one is `1` in Mathlib's normalisation.) -/
@[kb "nivenzuckermanmontgomery" "Thm A.4, p. 487"]
theorem discr_X_sub_C_mul (r : R) (g : R[X]) (hg : 0 < g.natDegree) :
    discr ((X - C r) * g) = discr g * (g.eval r) ^ 2 := by
  set m := g.natDegree with hm
  have hg0 : g ≠ 0 := by
    rintro rfl
    simp [hm] at hg
  have hX : (X - C r).natDegree = 1 := natDegree_X_sub_C r
  have hfdeg : ((X - C r) * g).natDegree = m + 1 := by
    rw [natDegree_mul (X_sub_C_ne_zero r) hg0, hX]
    ring
  have hlc : ((X - C r) * g).leadingCoeff = g.leadingCoeff := by
    rw [leadingCoeff_mul, (monic_X_sub_C r).leadingCoeff, one_mul]
  obtain ⟨f', hf'⟩ : ∃ f', f' = g + (X - C r) * derivative g := ⟨_, rfl⟩
  have hder : derivative ((X - C r) * g) = f' := by
    rw [hf', derivative_mul, derivative_X_sub_C, one_mul]
  have hf'deg : f'.natDegree ≤ m := by
    rw [← hder]
    have := natDegree_derivative_le ((X - C r) * g)
    omega
  have hD := natDegree_derivative_le g
  obtain ⟨k, hk⟩ : ∃ k, m = 1 + (derivative g).natDegree + k :=
    ⟨m - 1 - (derivative g).natDegree, by omega⟩
  -- the two resultant/discriminant relations
  have h1 := resultant_deriv (f := (X - C r) * g)
    (natDegree_pos_iff_degree_pos.mp (by omega))
  rw [hder, hfdeg] at h1
  simp only [Nat.add_sub_cancel] at h1
  have h2 := resultant_deriv (f := g) (natDegree_pos_iff_degree_pos.mp hg)
  -- evaluate `Res(f, f')`
  have e1 : resultant ((X - C r) * g) f' (m + 1) m
      = resultant (X - C r) f' 1 m * resultant g f' m m := by
    have := resultant_mul_left (X - C r) g f' m hf'deg
    rw [hX, add_comm] at this
    exact this
  have e2 : resultant (X - C r) f' 1 m = g.eval r := by
    have := resultant_X_sub_C_pow_left r f' 1 m hf'deg
    rw [pow_one, pow_one] at this
    rw [this, hf']
    simp
  have e3 : resultant g f' m m = resultant g ((X - C r) * derivative g) m m := by
    have : f' = (X - C r) * derivative g + g * 1 := by rw [hf']; ring
    rw [this]
    exact resultant_add_mul_right g ((X - C r) * derivative g) 1 m m (by simp) le_rfl
  have e4 : resultant g ((X - C r) * derivative g) m m
      = resultant g (X - C r) m 1 * resultant g (derivative g) m (m - 1) := by
    have t1 := resultant_mul_right g (X - C r) (derivative g) m le_rfl
    rw [hX] at t1
    have t2 : resultant g ((X - C r) * derivative g) m (1 + (derivative g).natDegree + k)
        = g.coeff m ^ k * resultant g ((X - C r) * derivative g) m
            (1 + (derivative g).natDegree) :=
      resultant_add_right_deg g ((X - C r) * derivative g) m _ k
        ((natDegree_mul_le).trans (by rw [hX]))
    have t3 : resultant g (derivative g) m ((derivative g).natDegree + k)
        = g.coeff m ^ k * resultant g (derivative g) m (derivative g).natDegree :=
      resultant_add_right_deg g (derivative g) m _ k le_rfl
    have hmk : m - 1 = (derivative g).natDegree + k := by omega
    rw [hmk, t3]
    have t4 : resultant g ((X - C r) * derivative g) m m
        = resultant g ((X - C r) * derivative g) m (1 + (derivative g).natDegree + k) := by
      rw [← hk]
    rw [t4, t2, t1]
    ring
  have e5 : resultant g (X - C r) m 1 = (-1) ^ m * g.eval r := by
    have := resultant_X_sub_C_pow_right g r m 1 le_rfl
    rw [pow_one] at this
    simpa using this
  have hres : resultant ((X - C r) * g) f' (m + 1) m
      = g.eval r * ((-1) ^ m * g.eval r * resultant g (derivative g) m (m - 1)) := by
    rw [e1, e2, e3, e4, e5]
  -- the signs
  have hs : (m + 1) * m / 2 = m * (m - 1) / 2 + m := by
    have : (m + 1) * m = m * (m - 1) + 2 * m := by
      obtain ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      rw [hj]
      simp only [Nat.add_sub_cancel]
      ring
    rw [this]
    exact Nat.add_mul_div_left _ _ (by norm_num)
  rw [hres, h2, hs, hlc, pow_add] at h1
  have hc : (-1 : R) ^ (m * (m - 1) / 2) * (-1) ^ m * g.leadingCoeff ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))) (leadingCoeff_ne_zero.mpr hg0)
  refine mul_left_cancel₀ hc ?_
  linear_combination (-1) * h1

end Disc

/-- **Theorem A.4** (first part), as a proposition: for each `n`, the discriminant of a
polynomial of degree `n` is given by a form `F` of degree `2n - 2` with integral coefficients
evaluated at the coefficients. -/
@[kb "nivenzuckermanmontgomery" "Thm A.4, p. 487"]
def DiscrIsIntegralForm : Prop :=
  ∀ n : ℕ, ∃ F : MvPolynomial (Fin (n + 1)) ℤ, F.IsHomogeneous (2 * n - 2) ∧
    ∀ (R : Type) [CommRing R] (f : R[X]), f.natDegree = n →
      discr f = MvPolynomial.aeval (fun i : Fin (n + 1) => f.coeff i) F

/-! ## Theorem A.5 -/

section DiscrMap

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The matrix `sylvesterDeriv` of Mathlib with the degree `n` as an explicit parameter. -/
noncomputable def sylvesterDerivDeg (n : ℕ) (f : R[X]) :
    Matrix (Fin (n - 1 + n)) (Fin (n - 1 + n)) R :=
  if hn : n = 0 then 0
  else (f.derivative.sylvester f (n - 1) n).updateRow ⟨2 * n - 2, by omega⟩
    (fun j ↦ if ↑j = n - 2 then 1 else (if ↑j = 2 * n - 2 then (n : R) else 0))

theorem discr_eq_sylvesterDerivDeg {n : ℕ} {f : R[X]} (hf : f.natDegree = n) :
    discr f = (sylvesterDerivDeg n f).det * (-1) ^ (n * (n - 1) / 2) := by
  subst hf
  rfl

theorem sylvesterDerivDeg_map (φ : R →+* S) (n : ℕ) (f : R[X]) :
    φ.mapMatrix (sylvesterDerivDeg n f) = sylvesterDerivDeg n (f.map φ) := by
  unfold sylvesterDerivDeg
  split_ifs with hn
  · ext; simp
  · rw [derivative_map, sylvester_map_map]
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.updateRow_apply]
    split_ifs <;> simp_all

/-- `D(f)` is a polynomial in the coefficients of `f` (for a fixed degree): two polynomials of
the same degree with the same image under a ring homomorphism have discriminants with the same
image. -/
theorem map_discr_eq_of_map_eq (φ : R →+* S) {f g : R[X]} (hdeg : f.natDegree = g.natDegree)
    (h : f.map φ = g.map φ) : φ (discr f) = φ (discr g) := by
  rw [discr_eq_sylvesterDerivDeg hdeg, discr_eq_sylvesterDerivDeg rfl, map_mul, map_mul,
    RingHom.map_det, RingHom.map_det, sylvesterDerivDeg_map, sylvesterDerivDeg_map, h]

end DiscrMap

/-- **Theorem A.5.**  Let `f` have integral coefficients and degree at least `2`, and suppose
`pˢ ∥ D(f)`, `f(a) ≡ 0 (mod pʲ)`, `pᵗ ∥ f'(a)` and `j > s`.  Then `j > 2t`, i.e. `j ≥ 2t + 1`.
(For `f` of degree one the discriminant is `1` and the statement fails, e.g. `f = p x + p`,
`a = 0`, `j = t = 1`; the book's proof uses Theorem A.4 for `f = (x - a) g`, which needs `g`
nonconstant.) -/
@[kb "nivenzuckermanmontgomery" "Thm A.5, p. 488"]
theorem lift_singular_via_discr (f : ℤ[X]) (hf : 2 ≤ f.natDegree) (p : ℕ) (_hp : p.Prime)
    (a : ℤ) (s t j : ℕ) (_hs : (p : ℤ) ^ s ∣ discr f) (hs' : ¬ (p : ℤ) ^ (s + 1) ∣ discr f)
    (hj : (p : ℤ) ^ j ∣ f.eval a) (ht : (p : ℤ) ^ t ∣ (derivative f).eval a)
    (_ht' : ¬ (p : ℤ) ^ (t + 1) ∣ (derivative f).eval a) (hsj : s < j) : 2 * t < j := by
  set g := f /ₘ (X - C a) with hg
  have hfg : f = (X - C a) * g + C (f.eval a) := by
    have := modByMonic_add_div f (X - C a)
    rw [modByMonic_X_sub_C_eq_C_eval] at this
    rw [hg]; linear_combination -this
  have hdegh : ((X - C a) * g).natDegree = f.natDegree := by
    conv_rhs => rw [hfg]
    rw [natDegree_add_C]
  have hg0 : g ≠ 0 := by
    rintro h0
    rw [h0, mul_zero] at hdegh
    simp at hdegh
    omega
  have hdegg : 0 < g.natDegree := by
    rw [natDegree_mul (X_sub_C_ne_zero a) hg0, natDegree_X_sub_C] at hdegh
    omega
  have hder : (derivative f).eval a = g.eval a := by
    conv_lhs => rw [hfg]
    simp
  let φ := Int.castRingHom (ZMod (p ^ j))
  have hmap : f.map φ = ((X - C a) * g).map φ := by
    conv_lhs => rw [hfg]
    rw [Polynomial.map_add, map_C]
    have : φ (f.eval a) = 0 := by
      simp only [φ, eq_intCast]
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact_mod_cast hj
    rw [this, map_zero, add_zero]
  have hD := map_discr_eq_of_map_eq φ hdegh.symm hmap
  rw [discr_X_sub_C_mul a g hdegg, ← hder] at hD
  by_contra hle
  push Not at hle
  apply hs'
  have h1 : (p : ℤ) ^ j ∣ ((derivative f).eval a) ^ 2 :=
    (pow_dvd_pow _ hle).trans (by rw [pow_mul']; exact pow_dvd_pow_of_dvd ht 2)
  have h2 : (p : ℤ) ^ j ∣ discr f := by
    have h3 : φ (discr f) = 0 := by
      rw [hD, map_mul]
      have : φ (((derivative f).eval a) ^ 2) = 0 := by
        simp only [φ, eq_intCast]
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact_mod_cast h1
      rw [this, mul_zero]
    simp only [φ, eq_intCast] at h3
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h3
    exact_mod_cast h3
  exact (pow_dvd_pow _ (by omega)).trans h2

end NTKB.NZM
