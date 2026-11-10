/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Attr
import NTKB.Elementary.HardyWright.QuadraticFields.Units
import Mathlib.NumberTheory.Pell
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Data.Int.ModEq

/-!
# Units of real quadratic fields, polynomial rings modulo `G`, and factoring of ternary forms
(Niven–Zuckerman–Montgomery, Lemma 5.13, Theorems 9.16 and 9.23)

* Theorem 9.23: for squarefree `m > 1`, the field `ℚ(√m)` (`QuadraticAlgebra ℚ m 0`) has infinitely
  many units, i.e. integers (elements integral over `ℤ`) whose reciprocal is an integer
  (`NTKB.HardyWright.unities`). The book's proof: the numbers `x + y√m` with `x² - m y² = 1` are
  units, and Pell's equation has infinitely many solutions (here Mathlib's `Pell.Solution₁`,
  whose positive powers have strictly increasing `x`).
* Theorem 9.16: for `G ∈ ℚ[x]`, the ring of polynomials modulo `G` (`AdjoinRoot G`) is a field if and
  only if `G` is irreducible; and for the minimal polynomial `G` of an algebraic number `ξ` it is
  isomorphic to `ℚ(ξ)`.
* Lemma 5.13: if `a x² + b y² + c z²` is a product of two linear forms modulo `m` and modulo `n`
  with `(m, n) = 1`, it is a product of two linear forms modulo `m n` (the coefficients are
  combined by the Chinese remainder theorem).
-/

namespace NTKB.NZM

open NTKB.HardyWright QuadraticAlgebra

/-- **Theorem 9.23.** A real quadratic field `ℚ(√m)` (`m > 1` squarefree) has infinitely many units
(integers with integral reciprocal). -/
@[kb "nivenzuckermanmontgomery" "Thm 9.23, p. 428"]
theorem infinite_unities_of_one_lt {m : ℤ} (hm : Squarefree m) (h1 : 1 < m) :
    (unities m).Infinite := by
  have hns : ¬ IsSquare m := by
    rintro ⟨r, hr⟩
    have := hm r ⟨1, by rw [hr, mul_one]⟩
    rw [Int.isUnit_iff] at this
    rcases this with rfl | rfl <;> omega
  obtain ⟨a, hax, hay⟩ := Pell.Solution₁.exists_pos_of_not_isSquare (by omega) hns
  have hmono : StrictMono (fun n : ℕ => (a ^ (n + 1)).x) := by
    refine strictMono_nat_of_lt_succ fun n => ?_
    have hx : 0 < (a ^ (n + 1)).x := Pell.Solution₁.x_pow_pos (by omega) (n + 1)
    have hy : 0 < (a ^ (n + 1)).y := Pell.Solution₁.y_pow_succ_pos (by omega) hay n
    show (a ^ (n + 1)).x < (a ^ (n + 1 + 1)).x
    rw [pow_succ _ (n + 1), Pell.Solution₁.x_mul]
    have h2 : 0 < m * ((a ^ (n + 1)).y * a.y) := mul_pos (by omega) (mul_pos hy hay)
    have h3 : (a ^ (n + 1)).x * 1 < (a ^ (n + 1)).x * a.x := mul_lt_mul_of_pos_left hax hx
    linarith
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => (⟨(((a ^ (n + 1)).x : ℤ) : ℚ), (((a ^ (n + 1)).y : ℤ) : ℚ)⟩ :
      QuadraticAlgebra ℚ m 0)) ?_ ?_
  · intro n k h
    have h' : (((a ^ (n + 1)).x : ℤ) : ℚ) = (((a ^ (k + 1)).x : ℤ) : ℚ) := congrArg QuadraticAlgebra.re h
    exact hmono.injective (by exact_mod_cast h')
  · intro n
    refine mem_unities_of_norm_one (isIntegral_mk_int _ _) ?_
    rw [qnorm_eq]
    have h := (a ^ (n + 1)).prop
    have h' : (((a ^ (n + 1)).x : ℤ) : ℚ) ^ 2 - (m : ℚ) * (((a ^ (n + 1)).y : ℤ) : ℚ) ^ 2 = 1 := by
      exact_mod_cast h
    exact h'

/-- **Theorem 9.16.** The ring of polynomials modulo `G` (here `AdjoinRoot G`, `G ∈ ℚ[x]`) is a field
if and only if `G` is irreducible. -/
@[kb "nivenzuckermanmontgomery" "Thm 9.16, p. 421"]
theorem isField_adjoinRoot_iff_irreducible (G : Polynomial ℚ) :
    IsField (AdjoinRoot G) ↔ Irreducible G :=
  AdjoinRoot.isField_iff_irreducible

/-- **Theorem 9.16** (second part). If `G` is the minimal polynomial of an algebraic number `ξ`, the
ring of polynomials modulo `G` is isomorphic to `ℚ(ξ)`. -/
@[kb "nivenzuckermanmontgomery" "Thm 9.16, p. 421"]
noncomputable def adjoinRootMinpolyEquiv {K : Type*} [Field K] [CharZero K] (ξ : K)
    (h : IsIntegral ℚ ξ) : AdjoinRoot (minpoly ℚ ξ) ≃ₐ[ℚ] IntermediateField.adjoin ℚ {ξ} :=
  IntermediateField.adjoinRootEquivAdjoin ℚ h

/-- Chinese remainder theorem for two coprime integer moduli. -/
lemma exists_modEq_modEq {m n : ℤ} (hmn : IsCoprime m n) (u v : ℤ) :
    ∃ k : ℤ, k ≡ u [ZMOD m] ∧ k ≡ v [ZMOD n] := by
  obtain ⟨s, t, h⟩ := hmn
  refine ⟨u * t * n + v * s * m, ?_, ?_⟩
  · rw [Int.modEq_iff_dvd]
    exact ⟨(u - v) * s, by linear_combination (-u) * h⟩
  · rw [Int.modEq_iff_dvd]
    exact ⟨(v - u) * t, by linear_combination (-v) * h⟩

/-- **Lemma 5.13.** If `a x² + b y² + c z²` is congruent to a product of two linear forms modulo `m`
(coefficients `α₁ β₁ γ₁`, `α₂ β₂ γ₂`) and modulo `n` (coefficients `α₃ β₃ γ₃`, `α₄ β₄ γ₄`) with
`(m, n) = 1`, then it is congruent to a product of two linear forms modulo `m n`. -/
@[kb "nivenzuckermanmontgomery" "Lemma 5.13, p. 242"]
theorem ternary_factors_mul {a b c m n : ℤ} (hmn : Int.gcd m n = 1)
    {α₁ β₁ γ₁ α₂ β₂ γ₂ α₃ β₃ γ₃ α₄ β₄ γ₄ : ℤ}
    (hm : ∀ x y z : ℤ, a * x ^ 2 + b * y ^ 2 + c * z ^ 2 ≡
      (α₁ * x + β₁ * y + γ₁ * z) * (α₂ * x + β₂ * y + γ₂ * z) [ZMOD m])
    (hn : ∀ x y z : ℤ, a * x ^ 2 + b * y ^ 2 + c * z ^ 2 ≡
      (α₃ * x + β₃ * y + γ₃ * z) * (α₄ * x + β₄ * y + γ₄ * z) [ZMOD n]) :
    ∃ α β γ α' β' γ' : ℤ, ∀ x y z : ℤ, a * x ^ 2 + b * y ^ 2 + c * z ^ 2 ≡
      (α * x + β * y + γ * z) * (α' * x + β' * y + γ' * z) [ZMOD m * n] := by
  have hc : IsCoprime m n := Int.isCoprime_iff_gcd_eq_one.2 hmn
  obtain ⟨α, hα1, hα3⟩ := exists_modEq_modEq hc α₁ α₃
  obtain ⟨β, hβ1, hβ3⟩ := exists_modEq_modEq hc β₁ β₃
  obtain ⟨γ, hγ1, hγ3⟩ := exists_modEq_modEq hc γ₁ γ₃
  obtain ⟨α', hα'1, hα'3⟩ := exists_modEq_modEq hc α₂ α₄
  obtain ⟨β', hβ'1, hβ'3⟩ := exists_modEq_modEq hc β₂ β₄
  obtain ⟨γ', hγ'1, hγ'3⟩ := exists_modEq_modEq hc γ₂ γ₄
  refine ⟨α, β, γ, α', β', γ', fun x y z => ?_⟩
  refine (Int.modEq_and_modEq_iff_modEq_mul hmn).1 ⟨?_, ?_⟩
  · have e1 : α * x + β * y + γ * z ≡ α₁ * x + β₁ * y + γ₁ * z [ZMOD m] :=
      ((hα1.mul_right x).add (hβ1.mul_right y)).add (hγ1.mul_right z)
    have e2 : α' * x + β' * y + γ' * z ≡ α₂ * x + β₂ * y + γ₂ * z [ZMOD m] :=
      ((hα'1.mul_right x).add (hβ'1.mul_right y)).add (hγ'1.mul_right z)
    exact (hm x y z).trans (e1.mul e2).symm
  · have e1 : α * x + β * y + γ * z ≡ α₃ * x + β₃ * y + γ₃ * z [ZMOD n] :=
      ((hα3.mul_right x).add (hβ3.mul_right y)).add (hγ3.mul_right z)
    have e2 : α' * x + β' * y + γ' * z ≡ α₄ * x + β₄ * y + γ₄ * z [ZMOD n] :=
      ((hα'3.mul_right x).add (hβ'3.mul_right y)).add (hγ'3.mul_right z)
    exact (hn x y z).trans (e1.mul e2).symm

end NTKB.NZM
