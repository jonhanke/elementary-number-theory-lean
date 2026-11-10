/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.FieldTheory.Finite.Basic
import NTKB.Attr
import NTKB.Analytic.Apostol.PrimitiveRoots.Index
import NTKB.Analytic.Apostol.PrimitiveRoots.PrimePowers

/-!
# Primitive roots (Niven–Zuckerman–Montgomery, § 2.8)

* **Lemma 2.35.** If `q^a ∣ p - 1` there are exactly `q^a - q^(a-1)` residues of order `q^a` mod `p`.
* **Theorem 2.36.** A prime `p` has exactly `φ(p - 1)` primitive roots.
* **Theorem 2.39.** There are `φ(φ(p²)) = (p - 1) φ(p - 1)` primitive roots mod `p²`.
* **Theorem 2.40.** For odd `p`, a primitive root mod `p²` is a primitive root mod `p^a`, `a ≥ 1`.

Residues are elements of `(ZMod n)ˣ`; "order `d`" is `orderOf x = d`, and a primitive root mod `n`
is an element of order `φ(n)` (cf. `NTKB.Apostol.IsPrimitiveRootMod`). In Theorem 2.40 the
primitive root is an integer `g`, with hypothesis and conclusion on `orderOf (g : ZMod (p ^ a))`
(the same formulation as `NTKB.Apostol.orderOf_prime_pow_eq_totient_iff`).
-/

namespace NTKB.NZM

/-- **Lemma 2.35.** If `q^a ∣ p - 1` (`a ≥ 1`) there are exactly `q^a - q^(a-1)` residues mod `p`
of order `q^a`. -/
@[kb "nivenzuckermanmontgomery" "Lemma 2.35, p. 99"]
theorem card_orderOf_prime_pow_eq (p : ℕ) [Fact p.Prime] {q : ℕ} (hq : q.Prime) {a : ℕ}
    (ha : 1 ≤ a) (h : q ^ a ∣ p - 1) :
    (Finset.univ.filter fun x : (ZMod p)ˣ => orderOf x = q ^ a).card = q ^ a - q ^ (a - 1) := by
  haveI : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime Fact.out
  have hd : q ^ a ∣ Fintype.card (ZMod p)ˣ := by
    rw [ZMod.card_units p]; exact h
  rw [IsCyclic.card_orderOf_eq_totient hd, Nat.totient_prime_pow hq ha]
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ, Nat.mul_sub_one]

/-- **Theorem 2.36.** A prime `p` has exactly `φ(p - 1)` primitive roots. -/
@[kb "nivenzuckermanmontgomery" "Thm 2.36, p. 99"]
theorem card_primitiveRoots_prime (p : ℕ) [Fact p.Prime] :
    (Finset.univ.filter fun x : (ZMod p)ˣ => orderOf x = p - 1).card = Nat.totient (p - 1) := by
  haveI : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime Fact.out
  exact IsCyclic.card_orderOf_eq_totient (dvd_of_eq (ZMod.card_units p).symm)

/-- **Theorem 2.39.** A prime `p` has exactly `φ(φ(p²)) = (p - 1) φ(p - 1)` primitive roots
mod `p²`. -/
@[kb "nivenzuckermanmontgomery" "Thm 2.39, p. 102"]
theorem card_primitiveRoots_prime_sq (p : ℕ) [hp : Fact p.Prime] :
    (Finset.univ.filter fun x : (ZMod (p ^ 2))ˣ => orderOf x = Nat.totient (p ^ 2)).card =
      (p - 1) * Nat.totient (p - 1) := by
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.out.ne_zero⟩
  haveI : IsCyclic (ZMod (p ^ 2))ˣ := by
    by_cases h2 : p = 2
    · subst h2
      exact ZMod.isCyclic_units_four
    · exact ZMod.isCyclic_units_of_prime_pow p hp.out h2 2
  have htot : Nat.totient (p ^ 2) = p * (p - 1) := by
    rw [Nat.totient_prime_pow hp.out two_pos]; simp
  have hcop : Nat.Coprime p (p - 1) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp.out]
    intro hdvd
    have h2 := hp.out.two_le
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  rw [IsCyclic.card_orderOf_eq_totient (dvd_of_eq (ZMod.card_units_eq_totient (p ^ 2)).symm),
    htot, Nat.totient_mul hcop, Nat.totient_prime hp.out]

/-- **Theorem 2.40.** If `p` is an odd prime and `g` is a primitive root mod `p²` (`g` has order
`φ(p²)` in `ZMod (p²)`), then `g` is a primitive root mod `p^a` for every `a ≥ 1`
(the book states `a ≥ 3`). -/
@[kb "nivenzuckermanmontgomery" "Thm 2.40, p. 102"]
theorem orderOf_intCast_eq_totient_of_sq {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {g : ℤ}
    (hg : orderOf (g : ZMod (p ^ 2)) = Nat.totient (p ^ 2)) (a : ℕ) (ha : 1 ≤ a) :
    orderOf (g : ZMod (p ^ a)) = Nat.totient (p ^ a) := by
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have htot : Nat.totient (p ^ 2) = p * (p - 1) := by
    rw [Nat.totient_prime_pow hp.out two_pos]; simp
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.out.ne_zero⟩
  have hfin : IsOfFinOrder (g : ZMod (p ^ 2)) := by
    rw [← orderOf_pos_iff, hg, htot]
    exact Nat.mul_pos (by omega) (by omega)
  obtain ⟨u, hu⟩ := hfin.isUnit
  have hord : orderOf u = Nat.totient (p ^ 2) := by
    rw [← orderOf_units, hu, hg]
  have hprim : NTKB.Apostol.IsPrimitiveRootMod (p ^ 2) u := hord
  have hdvd : p ∣ p ^ 2 := dvd_pow_self p two_ne_zero
  -- `g` has order `p - 1` mod `p`
  have hmod : orderOf (g : ZMod p) = p - 1 := by
    have hcast : ((ZMod.unitsMap hdvd u : (ZMod p)ˣ) : ZMod p) = (g : ZMod p) := by
      rw [ZMod.unitsMap_val, hu]
      exact ZMod.cast_intCast hdvd g
    have hcard : orderOf (ZMod.unitsMap hdvd u) = Nat.card (ZMod p)ˣ :=
      orderOf_eq_card_of_forall_mem_zpowers fun v => by
        obtain ⟨h, rfl⟩ := ZMod.unitsMap_surjective hdvd v
        obtain ⟨k, rfl⟩ := hprim.exists_pow_eq h
        exact Subgroup.mem_zpowers_iff.2 ⟨(k : ℤ), by rw [zpow_natCast, map_pow]⟩
    rw [← hcast, orderOf_units, hcard, Nat.card_eq_fintype_card, ZMod.card_units p]
  -- `g ^ (p - 1) ≢ 1 (mod p²)`
  have hnd : ¬ g ^ (p - 1) ≡ 1 [ZMOD p ^ 2] := by
    intro h1
    have h1' : g ^ (p - 1) ≡ 1 [ZMOD ((p ^ 2 : ℕ) : ℤ)] := by push_cast; exact h1
    rw [← ZMod.intCast_eq_intCast_iff] at h1'
    push_cast at h1'
    have hdiv := orderOf_dvd_of_pow_eq_one h1'
    rw [hg, htot] at hdiv
    have hle := Nat.le_of_dvd (by omega) hdiv
    have h3 : 2 ≤ p - 1 := by omega
    have : p * (p - 1) > p - 1 := by nlinarith
    omega
  exact (NTKB.Apostol.orderOf_prime_pow_eq_totient_iff hp.out hp2 hmod).2 hnd a ha

end NTKB.NZM
