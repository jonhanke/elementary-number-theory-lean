/-
Ireland–Rosen, Chapter 11, §1 (end) and Exercise 11.3: the number `N_s` of points of a projective
hypersurface over a field `F_s ⊇ F` with `[F_s : F] = s` does not depend on the choice of `F_s`.
By Proposition 11.1.2 two such fields are `F`-isomorphic, and the isomorphism maps the points of
the hypersurface onto each other.
-/
import NTKB.IrelandRosen.R2.ZetaDiagonal
import NTKB.IrelandRosen.R2.Chevalley

open Finset
open scoped Classical LinearAlgebra.Projectivization

set_option linter.unusedSectionVars false

namespace NTKB.IrelandRosen

variable {F : Type*} [Field F] [Fintype F]

/-- The number of zeros in `P^n(K)` of `f ∈ F[x_0, …, x_n]`, `K ⊇ F`. -/
noncomputable def numProjZeros (K : Type*) [Field K] [Algebra F K] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) F) : ℕ :=
  Nat.card {P : ℙ K (Fin (n + 1) → K) //
    MvPolynomial.eval P.rep (MvPolynomial.map (algebraMap F K) f) = 0}

lemma isHomogeneous_map {σ K : Type*} [Field K] {f : MvPolynomial σ F} {d : ℕ}
    (hf : f.IsHomogeneous d) (φ : F →+* K) : (MvPolynomial.map φ f).IsHomogeneous d := by
  intro e he
  rw [MvPolynomial.coeff_map] at he
  exact hf (fun h => he (by rw [h, map_zero]))

lemma eval_map_smul_iff (K : Type*) [Field K] [Fintype K] [Algebra F K] {n d : ℕ}
    {f : MvPolynomial (Fin (n + 1)) F} (hf : f.IsHomogeneous d) (c : K) (v : Fin (n + 1) → K)
    (hc : c ≠ 0) :
    MvPolynomial.eval (c • v) (MvPolynomial.map (algebraMap F K) f) = 0 ↔
      MvPolynomial.eval v (MvPolynomial.map (algebraMap F K) f) = 0 := by
  rw [eval_smul_of_isHomogeneous (isHomogeneous_map hf _)]
  exact ⟨fun h => (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hc),
    fun h => by rw [h, mul_zero]⟩

lemma numProjDiag_eq_numProjZeros (K : Type*) [Field K] [Algebra F K] {n : ℕ}
    (a : Fin (n + 1) → F) (m : ℕ) :
    numProjDiag (fun i => algebraMap F K (a i)) m =
      numProjZeros K (∑ i, MvPolynomial.C (a i) * MvPolynomial.X i ^ m) := by
  unfold numProjDiag numProjZeros
  exact Nat.card_congr (Equiv.subtypeEquivRight fun P => by simp [map_sum, MvPolynomial.eval_map])

/-- **Exercise 11.3.** If `E`, `E'` are finite fields containing `F` with `[E : F] = [E' : F]` and
`f` is homogeneous, then `f` has as many zeros in `P^n(E)` as in `P^n(E')`. -/
@[kb "irelandrosen1990" "Exercise 11.3, p. 180"]
theorem numProjZeros_eq (E E' : Type*) [Field E] [Fintype E] [Algebra F E] [Field E']
    [Fintype E'] [Algebra F E'] (h : Module.finrank F E = Module.finrank F E') {n d : ℕ}
    {f : MvPolynomial (Fin (n + 1)) F} (hf : f.IsHomogeneous d) :
    numProjZeros E f = numProjZeros E' f := by
  obtain ⟨σ⟩ := algEquiv_of_finrank_eq (F := F) (E := E) E' h
  have hc : Fintype.card E = Fintype.card E' := by
    rw [card_extension (F := F), card_extension (F := F) (E := E'), h]
  have hE := card_nonzero_zeros
    (fun v : Fin (n + 1) → E => MvPolynomial.eval v (MvPolynomial.map (algebraMap F E) f) = 0)
    (eval_map_smul_iff E hf)
  have hE' := card_nonzero_zeros
    (fun v : Fin (n + 1) → E' => MvPolynomial.eval v (MvPolynomial.map (algebraMap F E') f) = 0)
    (eval_map_smul_iff E' hf)
  -- the affine nonzero zeros correspond under `σ`
  have hbij : Nat.card {v : Fin (n + 1) → E // v ≠ 0 ∧
        MvPolynomial.eval v (MvPolynomial.map (algebraMap F E) f) = 0} =
      Nat.card {w : Fin (n + 1) → E' // w ≠ 0 ∧
        MvPolynomial.eval w (MvPolynomial.map (algebraMap F E') f) = 0} := by
    have key : ∀ v : Fin (n + 1) → E,
        MvPolynomial.eval (fun i => σ (v i)) (MvPolynomial.map (algebraMap F E') f) =
          σ (MvPolynomial.eval v (MvPolynomial.map (algebraMap F E) f)) := by
      intro v
      rw [MvPolynomial.eval_map, MvPolynomial.eval_map]
      have := MvPolynomial.eval₂_comp_left (σ : E →+* E') (algebraMap F E) v f
      rw [show ((σ : E →+* E').comp (algebraMap F E)) = algebraMap F E' from by
        ext a; simp] at this
      exact this.symm
    refine Nat.card_congr
      { toFun := fun v => ⟨fun i => σ (v.1 i), ?_, ?_⟩
        invFun := fun w => ⟨fun i => σ.symm (w.1 i), ?_, ?_⟩
        left_inv := fun v => by ext i; simp
        right_inv := fun w => by ext i; simp }
    · intro h0; apply v.2.1; funext i; exact σ.injective (by simpa using congrFun h0 i)
    · rw [key, v.2.2, map_zero]
    · intro h0; apply w.2.1; funext i; exact σ.symm.injective (by simpa using congrFun h0 i)
    · have := key (fun i => σ.symm (w.1 i))
      simp only [AlgEquiv.apply_symm_apply] at this
      rw [← σ.injective.eq_iff, ← this, map_zero]
      exact w.2.2
  rw [hE, hE', hc] at hbij
  have hpos : 0 < Fintype.card E' - 1 := Nat.sub_pos_of_lt Fintype.one_lt_card
  exact Nat.eq_of_mul_eq_mul_right hpos hbij

/-- The diagonal counts `numProjDiag` used in `zetaDiag` do not depend on the choice of the
extensions either (Exercise 11.3 for `a_0 x_0^m + ⋯ + a_n x_n^m`). -/
theorem numProjDiag_eq_of_finrank_eq (E E' : Type*) [Field E] [Fintype E] [Algebra F E]
    [Field E'] [Fintype E'] [Algebra F E'] (h : Module.finrank F E = Module.finrank F E') {n : ℕ}
    (a : Fin (n + 1) → F) (m : ℕ) :
    numProjDiag (fun i => algebraMap F E (a i)) m = numProjDiag (fun i => algebraMap F E' (a i)) m := by
  have hf : (∑ i, MvPolynomial.C (a i) * MvPolynomial.X i ^ m :
      MvPolynomial (Fin (n + 1)) F).IsHomogeneous m := by
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => ?_
    simpa using (MvPolynomial.isHomogeneous_X_pow i m).C_mul (a i)
  rw [numProjDiag_eq_numProjZeros E, numProjDiag_eq_numProjZeros E', numProjZeros_eq E E' h hf]

end NTKB.IrelandRosen
