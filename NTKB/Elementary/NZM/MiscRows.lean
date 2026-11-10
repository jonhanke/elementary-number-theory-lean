/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Attr
import NTKB.Elementary.NZM.QuadraticForms
import NTKB.Elementary.NZM.LinearRecurrences
import NTKB.IrelandRosen.R1.PowersOfTwo
import Mathlib.FieldTheory.ChevalleyWarning
import Mathlib.Data.ZMod.Basic

/-!
# Miscellaneous rows (Niven–Zuckerman–Montgomery)

* Theorem 5.14: `ax² + by² + cz² ≡ 0 (mod p)` has a nontrivial solution (Chevalley–Warning).
* Primitive binary quadratic forms (Chapter 3, Problem 13): `IsPrimitiveForm`, and invariance of
  primitivity under equivalence (`FormEquiv`, Problem 11 gives equal contents).
* Corollary 2.44: `xⁿ ≡ a (mod 2^α)` for odd `a`, `α ≥ 3`, in the book's formulation, derived from
  the Ireland–Rosen versions in `NTKB.IrelandRosen`.
* Theorem A.9: a solution of a linear recurrence whose characteristic polynomial has distinct roots
  is `uₙ = ∑ βⱼ λⱼⁿ` (special case of Theorem A.10).
-/

namespace NTKB.NZM

open MvPolynomial

section T514

private lemma totalDegree_term_le {K : Type*} [CommRing K] [Nontrivial K] (r : K) (i : Fin 3) :
    (C r * X i ^ 2 : MvPolynomial (Fin 3) K).totalDegree ≤ 2 := by
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_pow _ _).trans ?_
  rw [totalDegree_X]

/-- **Theorem 5.14.** For a prime `p` and arbitrary integers `a, b, c`, the congruence
`ax² + by² + cz² ≡ 0 (mod p)` has a solution `(x, y, z)` with not all of `x, y, z` divisible
by `p`. Proof via the Chevalley–Warning theorem (as the book remarks). -/
@[kb "nivenzuckermanmontgomery" "Thm 5.14, p. 246"]
theorem exists_nontrivial_ternary_congr (p : ℕ) [Fact p.Prime] (a b c : ℤ) :
    ∃ x y z : ℤ, ¬ ((p : ℤ) ∣ x ∧ (p : ℤ) ∣ y ∧ (p : ℤ) ∣ z) ∧
      (p : ℤ) ∣ a * x ^ 2 + b * y ^ 2 + c * z ^ 2 := by
  classical
  set f : MvPolynomial (Fin 3) (ZMod p) :=
    C (a : ZMod p) * X 0 ^ 2 + C (b : ZMod p) * X 1 ^ 2 + C (c : ZMod p) * X 2 ^ 2 with hf
  have hdeg : f.totalDegree < Fintype.card (Fin 3) := by
    have h1 := totalDegree_term_le (a : ZMod p) 0
    have h2 := totalDegree_term_le (b : ZMod p) 1
    have h3 := totalDegree_term_le (c : ZMod p) 2
    have : f.totalDegree ≤ 2 :=
      ((totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans (max_le h1 h2)) h3))
    simpa using lt_of_le_of_lt this (by norm_num)
  have hp := char_dvd_card_solutions p hdeg
  have hzero : eval (0 : Fin 3 → ZMod p) f = 0 := by simp [hf]
  have hpos : 0 < Fintype.card { x : Fin 3 → ZMod p // eval x f = 0 } :=
    Fintype.card_pos_iff.mpr ⟨⟨0, hzero⟩⟩
  have hgt : 1 < Fintype.card { x : Fin 3 → ZMod p // eval x f = 0 } :=
    lt_of_lt_of_le (Fact.out : p.Prime).one_lt (Nat.le_of_dvd hpos hp)
  obtain ⟨y, hy⟩ := Fintype.exists_ne_of_one_lt_card hgt ⟨0, hzero⟩
  have hy0 : y.1 ≠ 0 := fun h => hy (Subtype.ext h)
  have hcast : ∀ z : ZMod p, (((z.val : ℕ) : ℤ) : ZMod p) = z := fun z => by simp
  refine ⟨(y.1 0).val, (y.1 1).val, (y.1 2).val, ?_, ?_⟩
  · rintro ⟨h0, h1, h2⟩
    have e0 : y.1 0 = 0 := by
      rw [← hcast (y.1 0)]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h0
    have e1 : y.1 1 = 0 := by
      rw [← hcast (y.1 1)]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h1
    have e2 : y.1 2 = 0 := by
      rw [← hcast (y.1 2)]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h2
    apply hy0
    funext i
    fin_cases i <;> simp [e0, e1, e2]
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have := y.2
    simp only [hf, map_add, map_mul, map_pow, eval_C, eval_X] at this
    push_cast
    simpa using this

end T514

section Primitive

open NTKB.Davenport

/-- **Primitive binary quadratic form** (Chapter 3, Problem 13): the form `ax² + bxy + cy²`
(coefficient triple `(a, b, c)`, as in `NTKB.Davenport.formDisc`) is primitive if
`gcd(a, b, c) = 1`. No equivalent predicate existed in the repository. -/
@[kb "nivenzuckermanmontgomery" "Def (primitive form), p. 163"]
def IsPrimitiveForm (f : ℤ × ℤ × ℤ) : Prop := Int.gcd (Int.gcd f.1 f.2.1) f.2.2 = 1

/-- A form is primitive iff its only common divisors of the coefficients are units. -/
theorem isPrimitiveForm_iff_forall_dvd {f : ℤ × ℤ × ℤ} :
    IsPrimitiveForm f ↔ ∀ d : ℤ, d ∣ f.1 → d ∣ f.2.1 → d ∣ f.2.2 → IsUnit d := by
  constructor
  · intro h d h1 h2 h3
    have := Int.dvd_coe_gcd (Int.dvd_coe_gcd h1 h2) h3
    rw [IsPrimitiveForm] at h
    rw [h] at this
    exact isUnit_of_dvd_one (by simpa using this)
  · intro h
    have h3 : ((Int.gcd (Int.gcd f.1 f.2.1) f.2.2 : ℕ) : ℤ) ∣ f.2.2 := Int.gcd_dvd_right _ _
    have hab : ((Int.gcd (Int.gcd f.1 f.2.1) f.2.2 : ℕ) : ℤ) ∣ ((Int.gcd f.1 f.2.1 : ℕ) : ℤ) :=
      Int.gcd_dvd_left _ _
    have h1 : ((Int.gcd (Int.gcd f.1 f.2.1) f.2.2 : ℕ) : ℤ) ∣ f.1 :=
      hab.trans (Int.gcd_dvd_left _ _)
    have h2 : ((Int.gcd (Int.gcd f.1 f.2.1) f.2.2 : ℕ) : ℤ) ∣ f.2.1 :=
      hab.trans (Int.gcd_dvd_right _ _)
    have hu := Int.isUnit_iff.mp (h _ h1 h2 h3)
    unfold IsPrimitiveForm
    omega

/-- Common divisors of the coefficients of `f` divide the coefficients of any substitution. -/
theorem dvd_formSubst {f : ℤ × ℤ × ℤ} {d : ℤ} (h1 : d ∣ f.1) (h2 : d ∣ f.2.1) (h3 : d ∣ f.2.2)
    (α β γ δ : ℤ) :
    d ∣ (formSubst f α β γ δ).1 ∧ d ∣ (formSubst f α β γ δ).2.1 ∧
      d ∣ (formSubst f α β γ δ).2.2 := by
  simp only [formSubst]
  refine ⟨?_, ?_, ?_⟩
  · exact dvd_add (dvd_add (h1.mul_right _) ((h2.mul_right _).mul_right _)) (h3.mul_right _)
  · exact dvd_add (dvd_add (((h1.mul_left 2).mul_right _).mul_right _) (h2.mul_right _))
      (((h3.mul_left 2).mul_right _).mul_right _)
  · exact dvd_add (dvd_add (h1.mul_right _) ((h2.mul_right _).mul_right _)) (h3.mul_right _)

/-- Primitivity is preserved by unimodular substitution (equivalent forms have the same content,
Chapter 3, Problem 11; here only the consequence for primitivity is needed). -/
theorem isPrimitiveForm_iff_of_formEquiv {f g : ℤ × ℤ × ℤ} (h : FormEquiv f g) :
    IsPrimitiveForm f ↔ IsPrimitiveForm g := by
  have key : ∀ {f g : ℤ × ℤ × ℤ}, FormEquiv f g → IsPrimitiveForm g → IsPrimitiveForm f := by
    intro f g ⟨α, β, γ, δ, _, hg⟩ hgp
    rw [isPrimitiveForm_iff_forall_dvd] at hgp ⊢
    intro d h1 h2 h3
    obtain ⟨e1, e2, e3⟩ := dvd_formSubst h1 h2 h3 α β γ δ
    rw [← hg] at e1 e2 e3
    exact hgp d e1 e2 e3
  exact ⟨fun hf => key (formEquiv_symm h) hf, key h⟩

end Primitive

section Cor244

/-- Helper: if `4 ∣ b - 1` and `2^(k+1) ∣ b² - 1` then `2^k ∣ b - 1`. -/
theorem two_pow_dvd_sub_one_step {b : ℤ} {k : ℕ} (hb : 4 ∣ b - 1) (h : 2 ^ (k + 1) ∣ b ^ 2 - 1) :
    2 ^ k ∣ b - 1 := by
  obtain ⟨s, hs⟩ := hb
  have e : b ^ 2 - 1 = ((b - 1) * (2 * s + 1)) * 2 := by
    have : b = 4 * s + 1 := by linarith
    subst this; ring
  rw [e, pow_succ] at h
  have h' := (mul_dvd_mul_iff_right (two_ne_zero : (2 : ℤ) ≠ 0)).mp h
  have hc : IsCoprime ((2 : ℤ) ^ k) (2 * s + 1) :=
    IsCoprime.pow_left ⟨-s, 1, by ring⟩
  exact hc.dvd_of_dvd_mul_right h'

/-- Helper: for `a ≡ 1 (mod 4)`, `a^(2^m) ≡ 1 (mod 2^α)` with `m + 2 ≤ α` forces
`a ≡ 1 (mod 2^(α-m))`. -/
theorem two_pow_dvd_sub_one_of_pow {a : ℤ} (h4 : 4 ∣ a - 1) :
    ∀ (m α : ℕ), m + 2 ≤ α → 2 ^ α ∣ a ^ 2 ^ m - 1 → 2 ^ (α - m) ∣ a - 1 := by
  intro m
  induction m with
  | zero => intro α _ h; simpa using h
  | succ m ih =>
    intro α hα h
    have hb : 4 ∣ a ^ 2 ^ m - 1 := by
      have := sub_dvd_pow_sub_pow a 1 (2 ^ m)
      rw [one_pow] at this
      exact h4.trans this
    have h' : 2 ^ ((α - 1) + 1) ∣ (a ^ 2 ^ m) ^ 2 - 1 := by
      rw [Nat.sub_add_cancel (by omega), ← pow_mul, ← pow_succ]; exact h
    have := ih (α - 1) (by omega) (two_pow_dvd_sub_one_step hb h')
    have e : α - 1 - m = α - (m + 1) := by omega
    rwa [e] at this

/-- **Corollary 2.44, `n` odd.** For odd `a` and `α ≥ 3`, `xⁿ ≡ a (mod 2^α)` has exactly one
solution when `n` is odd (derived from `NTKB.IrelandRosen.existsUnique_pow_eq_of_odd`). -/
@[kb "nivenzuckermanmontgomery" "Cor 2.44, p. 105"]
theorem existsUnique_pow_eq_two_pow_of_odd {α : ℕ} (hα : 3 ≤ α) {a : ℤ} (ha : Odd a) {n : ℕ}
    (hn : Odd n) : ∃! x : ZMod (2 ^ α), x ^ n = a :=
  NTKB.IrelandRosen.existsUnique_pow_eq_of_odd (by omega) ha hn

/-- **Corollary 2.44, `n` even.** For odd `a`, `α ≥ 3`, `n > 0` even and `(n, 2^(α-2)) = 2^P`,
the congruence `xⁿ ≡ a (mod 2^α)` has `2^(P+1)` solutions if `a ≡ 1 (mod 2^(P+2))` and none
otherwise. (Derived from the criterion and count of Ireland–Rosen, Prop. 4.2.2.) -/
@[kb "nivenzuckermanmontgomery" "Cor 2.44, p. 105"]
theorem card_pow_eq_two_pow_of_even {α : ℕ} (hα : 3 ≤ α) {a : ℤ} (ha : Odd a) {n : ℕ}
    (hn0 : 0 < n) (hn : Even n) {P : ℕ} (hP : Nat.gcd n (2 ^ (α - 2)) = 2 ^ P) :
    Nat.card {x : ZMod (2 ^ α) // x ^ n = a} =
      if a ≡ 1 [ZMOD 2 ^ (P + 2)] then 2 ^ (P + 1) else 0 := by
  have hPle : P ≤ α - 2 := by
    have : 2 ^ P ∣ 2 ^ (α - 2) := hP ▸ Nat.gcd_dvd_right n _
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp this
  have hdiv : 2 ^ (α - 2) / Nat.gcd n (2 ^ (α - 2)) = 2 ^ (α - 2 - P) := by
    rw [hP, Nat.pow_div hPle (by norm_num)]
  have hcrit := NTKB.IrelandRosen.exists_pow_eq_iff_of_even hα ha hn0 hn
  rw [hdiv] at hcrit
  split_ifs with hc
  · have h2 : (2 : ℤ) ^ (P + 2) ∣ a - 1 := Int.modEq_iff_dvd.mp hc.symm
    have h4 : (4 : ℤ) ∣ a - 1 := by
      have := (pow_dvd_pow (2 : ℤ) (by omega : 2 ≤ P + 2)).trans h2
      norm_num at this
      exact this
    have hsol : ∃ x : ZMod (2 ^ α), x ^ n = a := by
      refine hcrit.mpr ⟨Int.modEq_iff_dvd.mpr ((dvd_sub_comm).mp h4), ?_⟩
      rw [NTKB.IrelandRosen.intCast_pow_eq_one_iff]
      have := NTKB.IrelandRosen.two_pow_dvd_pow_two_pow_sub_one (by omega) h2 (α - 2 - P)
      rw [show P + 2 + (α - 2 - P) = α by omega] at this
      push_cast
      exact this
    rw [NTKB.IrelandRosen.card_pow_eq_of_even hα ha hn0 hn hsol, hP]
    ring
  · have hno : ¬ ∃ x : ZMod (2 ^ α), x ^ n = a := by
      rintro hex
      obtain ⟨h4, h⟩ := hcrit.mp hex
      rw [NTKB.IrelandRosen.intCast_pow_eq_one_iff] at h
      push_cast at h
      have h4' : (4 : ℤ) ∣ a - 1 := Int.modEq_iff_dvd.mp h4.symm
      have := two_pow_dvd_sub_one_of_pow h4' (α - 2 - P) α (by omega) h
      rw [show α - (α - 2 - P) = P + 2 by omega] at this
      exact hc (Int.modEq_iff_dvd.mpr ((dvd_sub_comm).mp this))
    exact Nat.card_eq_zero.mpr (Or.inl ⟨fun x => hno ⟨x.1, x.2⟩⟩)

end Cor244

section A9

open Polynomial

/-- **Theorem A.9.** If the characteristic polynomial of a complex linear recurrence (with
nonzero constant term, `b_k ≠ 0`) has distinct roots (`roots.Nodup`, i.e. `k` distinct roots for
a recurrence of order `k`), then every solution has the form `uₙ = ∑ⱼ βⱼ λⱼⁿ`. Special case of
Theorem A.10 (`NTKB.NZM.expPoly_of_isSolution`) where all multiplicities are `1`. -/
@[kb "nivenzuckermanmontgomery" "Thm A.9, p. 496"]
theorem solution_eq_sum_of_distinct_roots (E : LinearRecurrence ℂ)
    (h0 : E.charPoly.coeff 0 ≠ 0) (hd : E.charPoly.roots.Nodup) (u : ℕ → ℂ)
    (hu : E.IsSolution u) :
    ∃ β : ℂ → ℂ, ∀ n : ℕ, u n = ∑ l ∈ E.charPoly.roots.toFinset, β l * l ^ n := by
  classical
  obtain ⟨B, hB1, hB2⟩ := expPoly_of_isSolution E h0 u hu
  refine ⟨fun l => (B l).coeff 0, fun n => ?_⟩
  rw [hB2 n]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hm : E.charPoly.rootMultiplicity l = 1 := by
    rw [← count_roots]
    exact Multiset.count_eq_one_of_mem hd (Multiset.mem_toFinset.mp hl)
  have hdeg := hB1 l hl
  rw [hm] at hdeg
  have hC : B l = Polynomial.C ((B l).coeff 0) :=
    eq_C_of_degree_le_zero (Nat.WithBot.lt_one_iff_le_zero.mp (by simpa using hdeg))
  rw [hC, Polynomial.eval_C]

end A9

end NTKB.NZM
