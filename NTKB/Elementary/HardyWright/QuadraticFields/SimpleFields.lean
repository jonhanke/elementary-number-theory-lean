/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Attr
import Mathlib.NumberTheory.NumberField.Basic
import Aesop.BuiltinRules
import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.Tactic.TypeStar
/-!
# Properties A, B, C, D of simple fields (Hardy–Wright §§ 15.6–15.7)

For the integers `R` of a field (here: any integral domain in which factorisation into irreducibles
exists, `WfDvdMonoid R`, e.g. the ring of integers of a quadratic or any number field):

* A: any `α, β` have a greatest common divisor `δ` (`δ ∣ α`, `δ ∣ β`, and every common divisor
  divides `δ`);
* B: any `α, β` have a common divisor `δ = λα + μβ`;
* C: factorisation is unique (`UniqueFactorizationMonoid R`): the field is simple.

`properties_ABC` proves the implications of § 15.6: B ⟹ A, B ⟹ C, A ⟹ C, C ⟹ A.
`isPrincipalIdealRing_of_simple` is property D of § 15.7: every ideal of a simple field is principal.
-/

namespace NTKB.HardyWright

/-- **§ 15.6.** Properties A, B, C: B implies A, B implies C, A implies C (via (15.6.1)), and C
implies A. -/
@[kb "hardywright2008" "§ 15.6, p. 312"]
theorem properties_ABC (R : Type*) [CommRing R] [IsDomain R] [WfDvdMonoid R] :
    let A := ∀ α β : R, ∃ δ, δ ∣ α ∧ δ ∣ β ∧ ∀ δ', δ' ∣ α → δ' ∣ β → δ' ∣ δ
    let B := ∀ α β : R, ∃ δ, δ ∣ α ∧ δ ∣ β ∧ ∃ l μ : R, l * α + μ * β = δ
    let C := UniqueFactorizationMonoid R
    (B → A) ∧ (B → C) ∧ (A → C) ∧ (C → A) := by
  intro A B C
  have hBA : B → A := fun hB α β ↦ by
    obtain ⟨δ, h1, h2, l, μ, h⟩ := hB α β
    exact ⟨δ, h1, h2, fun δ' h1' h2' ↦ h ▸ dvd_add (h1'.mul_left l) (h2'.mul_left μ)⟩
  have hAC : A → C := fun hA ↦ by
    classical
    let _ : GCDMonoid R := gcdMonoidOfExistsGCD fun a b ↦ by
      obtain ⟨δ, h1, h2, h⟩ := hA a b
      exact ⟨δ, fun d ↦ ⟨fun ⟨hda, hdb⟩ ↦ h d hda hdb, fun hd ↦ ⟨hd.trans h1, hd.trans h2⟩⟩⟩
    exact ufm_of_decomposition_of_wfDvdMonoid
  have hCA : C → A := fun hC α β ↦ by
    have : UniqueFactorizationMonoid R := hC
    let _ : GCDMonoid R := UniqueFactorizationMonoid.toGCDMonoid R
    exact ⟨gcd α β, gcd_dvd_left _ _, gcd_dvd_right _ _, fun _ h1 h2 ↦ dvd_gcd h1 h2⟩
  exact ⟨hBA, fun hB ↦ hAC (hBA hB), hAC, hCA⟩

/-- **§ 15.7, property D.** Every ideal of a simple field (here: the ring of integers of a number
field with unique factorisation) is a principal ideal. -/
@[kb "hardywright2008" "§ 15.7, p. 316"]
theorem isPrincipalIdealRing_of_simple (K : Type*) [Field K] [NumberField K]
    [UniqueFactorizationMonoid (NumberField.RingOfIntegers K)] :
    IsPrincipalIdealRing (NumberField.RingOfIntegers K) :=
  IsPrincipalIdealRing.of_isDedekindDomain_of_uniqueFactorizationMonoid _

end NTKB.HardyWright
