/-
Ireland–Rosen, Chapter 9, §11: constructibility of regular polygons.
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.SimpleRing.Principal
import Aesop.BuiltinRules
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.FunLike.Fintype
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Presheaf
import NTKB.Attr

/-!
# The constructibility of regular polygons

Ireland–Rosen, Chapter 9, §11.

* Definition: `α ∈ ℂ` is *constructible* if there is a tower of subfields
  `ℚ = K₀ ⊆ K₁ ⊆ ⋯ ⊆ Kₙ ∋ α` with `Kᵢ = Kᵢ₋₁(√aᵢ)`, `aᵢ ∈ Kᵢ₋₁` (`IsConstructibleField`,
  `IsConstructible`).
* Lemma 1: `ζ_{2ⁿ}` is constructible (`isConstructible_of_pow_two_pow_eq_one`).
* Lemma 2: `∑_χ χ(t)` over the characters of `𝔽_p^*` (Mathlib's orthogonality relation).
* Theorem 4 (Gauss): if `p` is a Fermat prime then `ζ_p = e^{2πi/p}` is constructible, by the
  book's argument: `ζ_p = (p - 1)⁻¹ ∑_χ g(χ)` and `g(χ)^{2^m} ∈ ℤ[ζ_{2^n}]` for `χ` of order `2^m`.
-/

namespace NTKB.IrelandRosen.Constructible

open IntermediateField

/-- The towers `ℚ = K₀ ⊆ ⋯ ⊆ Kₙ` with `Kᵢ = Kᵢ₋₁(x)`, `x² ∈ Kᵢ₋₁`. -/
inductive IsConstructibleField : IntermediateField ℚ ℂ → Prop
  | bot : IsConstructibleField ⊥
  | adjoin {K : IntermediateField ℚ ℂ} {x : ℂ} (hK : IsConstructibleField K) (hx : x ^ 2 ∈ K) :
      IsConstructibleField (K ⊔ ℚ⟮x⟯)

/-- **Definition (§11).** A complex number is *constructible* if it lies in the top of a tower of
successive quadratic extensions `Kᵢ = Kᵢ₋₁(√aᵢ)` of `ℚ`. -/
@[kb "irelandrosen1990" "Ch. 9, §11, Definition (constructible), p. 141"]
def IsConstructible (α : ℂ) : Prop := ∃ K, IsConstructibleField K ∧ α ∈ K

lemma IsConstructibleField.sup {K L : IntermediateField ℚ ℂ} (hK : IsConstructibleField K)
    (hL : IsConstructibleField L) : IsConstructibleField (K ⊔ L) := by
  induction hL with
  | bot => simpa using hK
  | @adjoin L x _ hx ih =>
    rw [← sup_assoc]
    exact ih.adjoin (le_sup_right (a := K) hx)

lemma isConstructible_of_mem {K : IntermediateField ℚ ℂ} (hK : IsConstructibleField K) {α : ℂ}
    (h : α ∈ K) : IsConstructible α := ⟨K, hK, h⟩

lemma isConstructible_algebraMap (q : ℚ) : IsConstructible (q : ℂ) :=
  ⟨⊥, .bot, by simpa using (⊥ : IntermediateField ℚ ℂ).algebraMap_mem q⟩

lemma isConstructible_intCast (n : ℤ) : IsConstructible (n : ℂ) := by
  simpa using isConstructible_algebraMap n

lemma IsConstructible.add {α β : ℂ} (hα : IsConstructible α) (hβ : IsConstructible β) :
    IsConstructible (α + β) := by
  obtain ⟨K, hK, ha⟩ := hα
  obtain ⟨L, hL, hb⟩ := hβ
  exact ⟨K ⊔ L, hK.sup hL, add_mem (le_sup_left (b := L) ha) (le_sup_right (a := K) hb)⟩

lemma IsConstructible.mul {α β : ℂ} (hα : IsConstructible α) (hβ : IsConstructible β) :
    IsConstructible (α * β) := by
  obtain ⟨K, hK, ha⟩ := hα
  obtain ⟨L, hL, hb⟩ := hβ
  exact ⟨K ⊔ L, hK.sup hL, mul_mem (le_sup_left (b := L) ha) (le_sup_right (a := K) hb)⟩

lemma IsConstructible.inv {α : ℂ} (hα : IsConstructible α) : IsConstructible α⁻¹ := by
  obtain ⟨K, hK, ha⟩ := hα
  exact ⟨K, hK, inv_mem ha⟩

lemma IsConstructible.pow {α : ℂ} (hα : IsConstructible α) (n : ℕ) : IsConstructible (α ^ n) := by
  obtain ⟨K, hK, ha⟩ := hα
  exact ⟨K, hK, pow_mem ha n⟩

/-- Square roots of constructible numbers are constructible. -/
lemma IsConstructible.of_sq {x : ℂ} (h : IsConstructible (x ^ 2)) : IsConstructible x := by
  obtain ⟨K, hK, hx⟩ := h
  exact ⟨K ⊔ ℚ⟮x⟯, hK.adjoin hx, le_sup_right (a := K) (mem_adjoin_simple_self ℚ x)⟩

lemma IsConstructible.of_pow_two_pow {x : ℂ} (m : ℕ) (h : IsConstructible (x ^ 2 ^ m)) :
    IsConstructible x := by
  induction m generalizing x with
  | zero => simpa using h
  | succ m ih =>
    apply ih
    apply IsConstructible.of_sq
    rwa [← pow_mul, ← pow_succ]

lemma isConstructible_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (h : ∀ i ∈ s, IsConstructible (f i)) : IsConstructible (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isConstructible_intCast 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma isConstructible_prod {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (h : ∀ i ∈ s, IsConstructible (f i)) : IsConstructible (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isConstructible_intCast 1
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **Lemma 1 of §11.** Every `2ⁿ`-th root of unity, in particular `ζ_{2ⁿ}`, is constructible. -/
@[kb "irelandrosen1990" "Ch. 9, §11, Lemma 1, p. 141"]
theorem isConstructible_of_pow_two_pow_eq_one {μ : ℂ} {n : ℕ} (h : μ ^ 2 ^ n = 1) :
    IsConstructible μ :=
  IsConstructible.of_pow_two_pow n (by rw [h]; simpa using isConstructible_intCast 1)

lemma isConstructible_adjoin {μ : ℂ} (hμ : IsConstructible μ) :
    ∀ y ∈ Algebra.adjoin ℤ {μ}, IsConstructible y := by
  intro y hy
  induction hy using Algebra.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact hμ
  | algebraMap r => simpa using isConstructible_intCast r
  | add x y _ _ hx hy => exact hx.add hy
  | mul x y _ _ hx hy => exact hx.mul hy

/-- **Lemma 2 of §11** (Mathlib's orthogonality, for `t ≠ 0`): `∑_χ χ(t)` over the characters of
`(ZMod p)ˣ` is `p - 1` for `t = 1` and `0` otherwise (all characters vanish at `0`). -/
@[kb "irelandrosen1990" "Ch. 9, §11, Lemma 2, p. 142"]
theorem sum_characters (p : ℕ) [Fact p.Prime] (t : ZMod p) :
    ∑ χ : DirichletCharacter ℂ p, χ t = if t = 1 then ((p - 1 : ℕ) : ℂ) else 0 := by
  rw [DirichletCharacter.sum_characters_eq, Nat.totient_prime Fact.out]

/-- **Theorem 4 of §11 (Gauss).** If `p` is a Fermat prime (`p - 1` a power of `2`), then
`ζ_p = e^{2πi/p}` is constructible. -/
@[kb "irelandrosen1990" "Ch. 9, §11, Theorem 4, p. 142"]
theorem isConstructible_exp_of_fermat {p N : ℕ} [hp : Fact p.Prime] (hN : p - 1 = 2 ^ N) :
    IsConstructible (Complex.exp (2 * Real.pi * Complex.I / p)) := by
  set ψ : AddChar (ZMod p) ℂ := ZMod.stdAddChar
  have hψ : ψ.IsPrimitive := ZMod.isPrimitive_stdAddChar p
  have hψ1 : ψ 1 = Complex.exp (2 * Real.pi * Complex.I / p) := by
    have := ZMod.stdAddChar_coe (N := p) 1
    simpa using this
  -- `∑_χ g(χ) = (p - 1) ζ_p`
  have hsum : ∑ χ : DirichletCharacter ℂ p, gaussSum χ ψ = ((p - 1 : ℕ) : ℂ) * ψ 1 := by
    simp only [gaussSum]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, sum_characters]
    simp
  have hp1 : ((p - 1 : ℕ) : ℂ) ≠ 0 := by
    have := hp.out.two_le; exact_mod_cast (by omega : p - 1 ≠ 0)
  have hζ : Complex.exp (2 * Real.pi * Complex.I / p) =
      (((p - 1 : ℕ) : ℚ)⁻¹ : ℚ) * ∑ χ : DirichletCharacter ℂ p, gaussSum χ ψ := by
    rw [hsum, ← hψ1]; push_cast; field_simp
  rw [hζ]
  refine (isConstructible_algebraMap _).mul (isConstructible_sum _ _ fun χ _ => ?_)
  -- each Gauss sum is constructible
  obtain ⟨μ, hμ⟩ : ∃ μ : ℂ, IsPrimitiveRoot μ (p - 1) :=
    ⟨_, Complex.isPrimitiveRoot_exp (p - 1) (by have := hp.out.two_le; omega)⟩
  have hμc : IsConstructible μ := isConstructible_of_pow_two_pow_eq_one (by rw [← hN]; exact hμ.pow_eq_one)
  by_cases h1 : χ = 1
  · have hne : ψ ≠ 1 := by
      have := hψ (one_ne_zero (α := ZMod p)); rwa [AddChar.mulShift_one] at this
    rw [h1, gaussSum_one_left hne]
    simpa using isConstructible_intCast (-1)
  have hord : orderOf χ ∣ 2 ^ N := by
    have := MulChar.orderOf_dvd_card_sub_one (χ := χ)
    rwa [ZMod.card, hN] at this
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
  have h2 : 2 ≤ orderOf χ := by
    rcases Nat.lt_or_ge (orderOf χ) 2 with h | h
    · exfalso
      interval_cases h' : orderOf χ
      · exact (orderOf_pos χ).ne' h'
      · exact h1 (orderOf_eq_one_iff.1 h')
    · exact h
  have hpow := gaussSum_pow_eq_prod_jacobiSum h2 hψ
  rw [hm] at hpow
  refine IsConstructible.of_pow_two_pow m ?_
  rw [hpow]
  have hχn : χ ^ (p - 1) = 1 := by
    rw [hN, ← orderOf_dvd_iff_pow_eq_one]; exact hord
  have hc : IsConstructible ((Fintype.card (ZMod p) : ℕ) : ℂ) := by
    simpa using isConstructible_intCast (Fintype.card (ZMod p) : ℤ)
  have hm1 : χ (-1) * χ (-1) = 1 := by rw [← map_mul]; simp
  have hχ1 : IsConstructible (χ (-1)) := by
    rcases mul_self_eq_one_iff.1 hm1 with h | h
    · rw [h]; simpa using isConstructible_intCast 1
    · rw [h]; simpa using isConstructible_intCast (-1)
  refine (hχ1.mul hc).mul (isConstructible_prod _ _ fun i _ => ?_)
  refine isConstructible_adjoin hμc _ ?_
  haveI : NeZero (p - 1) := ⟨by have := hp.out.two_le; omega⟩
  exact jacobiSum_mem_algebraAdjoin_of_pow_eq_one hχn (by rw [← pow_mul, mul_comm, pow_mul, hχn,
    one_pow]) hμ

end NTKB.IrelandRosen.Constructible
