/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.FieldTheory.Finite.Basic
import NTKB.IrelandRosen.R1.PowersOfTwo

/-!
# Ireland–Rosen: `n`-th powers in cyclic groups (Propositions 4.2.1 and 7.1.2)

The book's proofs of Propositions 4.2.1 and 7.1.2 are the same: write `a = g^b`, `x = g^y` for a
generator `g` of the cyclic group of order `m` (`m = φ(m)` resp. `q - 1`); then `x^n = a` becomes
`ny ≡ b (mod m)`, solvable iff `d = (n, m)` divides `b`, i.e. iff `a^(m/d) = 1`, and then with
exactly `d` solutions. We prove the group statement once (`exists_pow_eq_iff_of_isCyclic`,
`card_pow_eq_of_isCyclic`) and specialize it.

* **Proposition 4.2.1**: if `m` has primitive roots (`(ℤ/mℤ)ˣ` cyclic) and `(a, m) = 1`, then
  `x^n ≡ a (mod m)` is solvable iff `a^(φ(m)/d) ≡ 1 (mod m)`, `d = (n, φ(m))`, and then it has
  exactly `d` solutions (the remark after the proof).
* **Proposition 7.1.2**: in a finite field with `q` elements, for `a ≠ 0`, `x^n = a` is solvable
  iff `a^((q-1)/d) = 1`, `d = (n, q - 1)`, and then it has exactly `d` solutions.
-/

namespace NTKB.IrelandRosen

section Cyclic

variable {G : Type*} [CommGroup G] [IsCyclic G] [Finite G]

/-- In a finite cyclic group of order `m`, the `n`-th powers are exactly the elements killed by
`m/d`, `d = (n, m)`. -/
theorem range_powMonoidHom_eq_ker (n : ℕ) :
    (powMonoidHom n : G →* G).range =
      (powMonoidHom (Nat.card G / Nat.gcd n (Nat.card G)) : G →* G).ker := by
  set m := Nat.card G
  set d := Nat.gcd n m
  have hm : 0 < m := Nat.card_pos
  have hdm : d ∣ m := Nat.gcd_dvd_right n m
  have hdn : d ∣ n := Nat.gcd_dvd_left n m
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨x, rfl⟩
    rw [MonoidHom.mem_ker, powMonoidHom_apply, powMonoidHom_apply, ← pow_mul,
      show n * (m / d) = m * (n / d) by
        have hd0 : 0 < d := Nat.gcd_pos_of_pos_right _ hm
        obtain ⟨A, hA⟩ := hdm
        obtain ⟨B, hB⟩ := hdn
        rw [hA, hB, Nat.mul_div_cancel_left _ hd0, Nat.mul_div_cancel_left _ hd0]
        ring, pow_mul, pow_card_eq_one', one_pow]
  · rw [IsCyclic.card_powMonoidHom_ker, IsCyclic.card_powMonoidHom_range, Nat.gcd_comm m n,
      Nat.gcd_eq_right (Nat.div_dvd_of_dvd hdm)]

/-- In a finite cyclic group of order `m`, `x^n = a` is solvable iff `a^(m/d) = 1`,
`d = (n, m)`. -/
theorem exists_pow_eq_iff_of_isCyclic (n : ℕ) (a : G) :
    (∃ x : G, x ^ n = a) ↔ a ^ (Nat.card G / Nat.gcd n (Nat.card G)) = 1 := by
  have := SetLike.ext_iff.mp (range_powMonoidHom_eq_ker (G := G) n) a
  simpa [MonoidHom.mem_range, MonoidHom.mem_ker] using this

/-- In a finite cyclic group of order `m`, if `x^n = a` is solvable then it has exactly
`(n, m)` solutions. -/
theorem card_pow_eq_of_isCyclic {n : ℕ} {a : G} (ha : ∃ x : G, x ^ n = a) :
    Nat.card {x : G // x ^ n = a} = Nat.gcd n (Nat.card G) := by
  classical
  have := Fintype.ofFinite G
  have hker : Nat.card {x : G // x ^ n = 1} = Nat.gcd n (Nat.card G) := by
    rw [Nat.gcd_comm, ← IsCyclic.card_powMonoidHom_ker G n]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x ↦ by simp [MonoidHom.mem_ker])
  rw [← hker, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Fintype.card_subtype]
  obtain ⟨u, hu⟩ := ha
  exact MonoidHom.card_fiber_eq_of_mem_range (powMonoidHom n) ⟨u, hu⟩ ⟨1, one_pow n⟩

end Cyclic

section FiniteField

variable {F : Type*} [Field F] [Finite F]

/-- **Ireland–Rosen, Proposition 7.1.2.** In a finite field with `q` elements, for `a ≠ 0` and
`n ≥ 1`, `x^n = a` has a solution iff `a^((q-1)/d) = 1`, `d = (n, q - 1)`. -/
@[kb "irelandrosen1990" "Prop 7.1.2, p. 91"]
theorem exists_pow_eq_iff_finiteField {a : F} (ha : a ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    (∃ x : F, x ^ n = a) ↔ a ^ ((Nat.card F - 1) / Nat.gcd n (Nat.card F - 1)) = 1 := by
  set au := Units.mk0 a ha
  have hE := powSolutionsEquivUnits hn au
  have h1 : (∃ x : F, x ^ n = a) ↔ ∃ u : Fˣ, u ^ n = au :=
    ⟨fun ⟨x, hx⟩ ↦ ⟨(hE.symm ⟨x, hx⟩).1, (hE.symm ⟨x, hx⟩).2⟩,
      fun ⟨u, hu⟩ ↦ ⟨(hE ⟨u, hu⟩).1, (hE ⟨u, hu⟩).2⟩⟩
  rw [h1, exists_pow_eq_iff_of_isCyclic, Nat.card_units F, Units.ext_iff,
    Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]

/-- **Ireland–Rosen, Proposition 7.1.2** (number of solutions). In a finite field with `q`
elements, for `a ≠ 0` and `n ≥ 1`, if `x^n = a` is solvable it has exactly `(n, q - 1)`
solutions. -/
@[kb "irelandrosen1990" "Prop 7.1.2, p. 91"]
theorem card_pow_eq_finiteField {a : F} (ha : a ≠ 0) {n : ℕ} (hn : n ≠ 0)
    (hsol : ∃ x : F, x ^ n = a) :
    Nat.card {x : F // x ^ n = a} = Nat.gcd n (Nat.card F - 1) := by
  set au := Units.mk0 a ha
  have hE := powSolutionsEquivUnits hn au
  show Nat.card {x : F // x ^ n = (au : F)} = _
  rw [← Nat.card_congr hE, card_pow_eq_of_isCyclic, Nat.card_units F]
  obtain ⟨x, hx⟩ := hsol
  exact ⟨(hE.symm ⟨x, hx⟩).1, (hE.symm ⟨x, hx⟩).2⟩

/-- **Ireland–Rosen, Proposition 4.1.2.** If `d ∣ p - 1` then `x^d ≡ 1 (mod p)` has exactly `d`
solutions (a special case of Proposition 7.1.2). -/
@[kb "irelandrosen1990" "Prop 4.1.2, p. 51"]
theorem card_pow_eq_one_zmod (p : ℕ) [Fact p.Prime] {d : ℕ} (hd : d ∣ p - 1) :
    Nat.card {x : ZMod p // x ^ d = 1} = d := by
  have hp1 : 0 < p - 1 := Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt
  have hd0 : d ≠ 0 := by rintro rfl; simp at hd; omega
  rw [card_pow_eq_finiteField one_ne_zero hd0 ⟨1, one_pow d⟩, Nat.card_zmod,
    Nat.gcd_eq_left hd]

end FiniteField

section PrimitiveRoots

variable {m : ℕ} [NeZero m]

/-- **Ireland–Rosen, Proposition 4.2.1.** If `m` possesses primitive roots (`(ℤ/mℤ)ˣ` is cyclic)
and `(a, m) = 1`, then `a` is an `n`-th power residue modulo `m` iff `a^(φ(m)/d) ≡ 1 (mod m)`,
`d = (n, φ(m))` (`n ≥ 1`). -/
@[kb "irelandrosen1990" "Prop 4.2.1, p. 56"]
theorem exists_pow_eq_iff_of_isCyclic_units [IsCyclic (ZMod m)ˣ] {a : ℤ}
    (ha : IsCoprime (m : ℤ) a) {n : ℕ} (hn : n ≠ 0) :
    (∃ x : ZMod m, x ^ n = a) ↔
      (a : ZMod m) ^ (m.totient / Nat.gcd n m.totient) = 1 := by
  set au := ((ZMod.isUnit_intCast_iff_isCoprime a m).mpr ha).unit
  have hE := powSolutionsEquivUnits hn au
  have h1 : (∃ x : ZMod m, x ^ n = a) ↔ ∃ u : (ZMod m)ˣ, u ^ n = au :=
    ⟨fun ⟨x, hx⟩ ↦ ⟨(hE.symm ⟨x, hx⟩).1, (hE.symm ⟨x, hx⟩).2⟩,
      fun ⟨u, hu⟩ ↦ ⟨(hE ⟨u, hu⟩).1, (hE ⟨u, hu⟩).2⟩⟩
  rw [h1, exists_pow_eq_iff_of_isCyclic, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Units.ext_iff, Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one]

/-- **Ireland–Rosen, Chapter 4, remark after Proposition 4.2.1.** If `m` possesses primitive
roots, `(a, m) = 1` and `x^n ≡ a (mod m)` is solvable, it has exactly `(n, φ(m))` solutions. -/
@[kb "irelandrosen1990" "Prop 4.2.1, p. 56"]
theorem card_pow_eq_of_isCyclic_units [IsCyclic (ZMod m)ˣ] {a : ℤ}
    (ha : IsCoprime (m : ℤ) a) {n : ℕ} (hn : n ≠ 0) (hsol : ∃ x : ZMod m, x ^ n = a) :
    Nat.card {x : ZMod m // x ^ n = a} = Nat.gcd n m.totient := by
  set au := ((ZMod.isUnit_intCast_iff_isCoprime a m).mpr ha).unit
  have hE := powSolutionsEquivUnits hn au
  have hau : (au : ZMod m) = a := IsUnit.unit_spec _
  rw [show {x : ZMod m // x ^ n = a} = {x : ZMod m // x ^ n = (au : ZMod m)} by rw [hau],
    ← Nat.card_congr hE, card_pow_eq_of_isCyclic, Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient]
  obtain ⟨x, hx⟩ := hsol
  exact ⟨(hE.symm ⟨x, hau ▸ hx⟩).1, (hE.symm ⟨x, hau ▸ hx⟩).2⟩

end PrimitiveRoots

end NTKB.IrelandRosen
