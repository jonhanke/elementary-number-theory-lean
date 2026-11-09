/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Identities
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.FieldTheory.Finite.Basic
import NTKB.Elementary.HardyWright.Congruences.Lagrange
import NTKB.Elementary.HardyWright.Fermat.Basic
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Roots of congruences to composite moduli (Hardy–Wright, §§ 8.2 to 8.4)

`NTKB.HardyWright.rootCount f m` is the number of roots of the congruence `f(x) ≡ 0 (mod m)` for an
integral polynomial `f`, congruent roots being counted once [hardywright2008, § 7.1].

* Theorem 122: the number of roots modulo `m = m₁ ⋯ m_k` (pairwise coprime) is the product of the
  numbers of roots modulo the `m_i`.
* Theorem 123: a root `ξ` of `f ≡ 0 (mod p^{a-1})` gives no, one or `p` roots `ξ + s p^{a-1}`
  (`0 ≤ s < p`) of `f ≡ 0 (mod p^a)` according to `f'(ξ)` and `f(ξ)`.
* Theorem 124: `x^{p-1} ≡ 1 (mod p^a)` has just `p - 1` roots for every `a`.
* Theorem 125: there are `p(p - 1)/2` quadratic residues of `p²`, and they are the roots of
  `x^{p(p-1)/2} ≡ 1 (mod p²)`.
-/

open Polynomial Finset

namespace NTKB.HardyWright

/-- The number of roots of `f(x) ≡ 0 (mod m)`, congruent roots counted once
[hardywright2008, § 7.1]. -/
noncomputable def rootCount (f : ℤ[X]) (m : ℕ) : ℕ :=
  Nat.card {x : ZMod m // (f.map (Int.castRingHom (ZMod m))).eval x = 0}

/-- Ring homomorphisms commute with evaluating an integral polynomial. -/
lemma map_eval_intPoly {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (f : ℤ[X]) (x : R) :
    φ ((f.map (Int.castRingHom R)).eval x) = (f.map (Int.castRingHom S)).eval (φ x) := by
  rw [eval_map, eval_map, hom_eval₂, RingHom.ext_int (φ.comp (Int.castRingHom R))
    (Int.castRingHom S)]

/-- **Theorem 122** [hardywright2008], two moduli: if `(m, n) = 1`, the number of roots of
`f ≡ 0 (mod m n)` is the product of the numbers of roots modulo `m` and modulo `n`. -/
@[kb "hardywright2008" "Thm 122, p. 123"]
theorem rootCount_mul (f : ℤ[X]) {m n : ℕ} (hmn : m.Coprime n) :
    rootCount f (m * n) = rootCount f m * rootCount f n := by
  set e := ZMod.chineseRemainder hmn
  let π₁ : ZMod (m * n) →+* ZMod m := (RingHom.fst _ _).comp e.toRingHom
  let π₂ : ZMod (m * n) →+* ZMod n := (RingHom.snd _ _).comp e.toRingHom
  have hroot : ∀ x : ZMod (m * n), (f.map (Int.castRingHom _)).eval x = 0 ↔
      (f.map (Int.castRingHom (ZMod m))).eval (π₁ x) = 0 ∧
        (f.map (Int.castRingHom (ZMod n))).eval (π₂ x) = 0 := by
    intro x
    rw [← map_eval_intPoly π₁, ← map_eval_intPoly π₂]
    constructor
    · intro h; simp [h]
    · rintro ⟨h1, h2⟩
      apply e.injective
      rw [map_zero]
      exact Prod.ext h1 h2
  rw [rootCount, rootCount, rootCount, ← Nat.card_prod]
  refine Nat.card_congr
    { toFun := fun x ↦ (⟨π₁ x, ((hroot x).1 x.2).1⟩, ⟨π₂ x, ((hroot x).1 x.2).2⟩)
      invFun := fun y ↦ ⟨e.symm (y.1, y.2), by
        rw [hroot]
        simp only [π₁, π₂, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
          RingEquiv.apply_symm_apply, RingHom.coe_fst, RingHom.coe_snd]
        exact ⟨y.1.2, y.2.2⟩⟩
      left_inv := fun x ↦ by
        ext
        simp [π₁, π₂]
      right_inv := fun y ↦ by
        ext <;> simp [π₁, π₂] }

lemma rootCount_one (f : ℤ[X]) : rootCount f 1 = 1 := by
  rw [rootCount, Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun x y ↦ Subtype.ext (Subsingleton.elim _ _)⟩, ⟨⟨0, Subsingleton.elim _ _⟩⟩⟩

/-- **Theorem 122** [hardywright2008]: if `m = m₁ m₂ ⋯ m_k` with no two `m_i` having a common
factor, the number of roots of `f ≡ 0 (mod m)` is the product of the numbers of roots of
`f ≡ 0 (mod m_i)`. -/
@[kb "hardywright2008" "Thm 122, p. 123"]
theorem rootCount_prod (f : ℤ[X]) {ι : Type*} (s : Finset ι) (m : ι → ℕ)
    (hm : (s : Set ι).Pairwise fun i j ↦ (m i).Coprime (m j)) :
    rootCount f (∏ i ∈ s, m i) = ∏ i ∈ s, rootCount f (m i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rootCount_one]
  | insert a s has ih =>
    rw [Finset.prod_insert has, Finset.prod_insert has, rootCount_mul, ih]
    · exact hm.mono (by simp)
    · refine Nat.Coprime.prod_right fun i hi ↦ hm (by simp) (by simp [hi]) ?_
      rintro rfl; exact has hi

/-! ### Counting with least non-negative residues -/

/-- The roots modulo `m > 0` counted among `0, 1, …, m - 1`. -/
lemma rootCount_eq_card_range (f : ℤ[X]) {m : ℕ} (hm : 0 < m) :
    rootCount f m = #{x ∈ range m | (m : ℤ) ∣ f.eval ((x : ℕ) : ℤ)} := by
  classical
  have : NeZero m := ⟨hm.ne'⟩
  have key : ∀ x : ℕ, (m : ℤ) ∣ f.eval (x : ℤ) ↔
      (f.map (Int.castRingHom (ZMod m))).eval (x : ZMod m) = 0 := by
    intro x
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← Int.cast_natCast (R := ZMod m), eval_intCast_map]
    rfl
  rw [rootCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  symm
  refine Finset.card_nbij (fun x : ℕ ↦ (x : ZMod m)) ?_ ?_ ?_
  · intro x hx
    simp only [coe_filter, Finset.mem_range] at hx
    simp only [coe_filter, Finset.mem_univ, true_and]
    exact (key x).1 hx.2
  · intro x hx y hy hxy
    simp only [coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hx hy
    simp only at hxy
    rw [← ZMod.val_natCast_of_lt hx.1, hxy, ZMod.val_natCast_of_lt hy.1]
  · intro x hx
    simp only [coe_filter, Finset.mem_univ, true_and] at hx
    refine ⟨x.val, ?_, ZMod.natCast_zmod_val x⟩
    simp only [coe_filter, Finset.mem_range]
    refine ⟨ZMod.val_lt x, (key _).2 ?_⟩
    rwa [ZMod.natCast_zmod_val]

/-! ### Theorem 123: lifting roots from `p^{a-1}` to `p^a` -/

/-- The key step of § 8.3: if `f(ξ) = p^{a-1} t` and `a ≥ 2`, then `ξ + s p^{a-1}` is a root modulo
`p^a` if and only if `t + s f'(ξ) ≡ 0 (mod p)`. -/
lemma prime_pow_dvd_eval_add_iff (f : ℤ[X]) {p a : ℕ} (hp : p.Prime) (ha : 2 ≤ a) {ξ t : ℤ}
    (ht : f.eval ξ = (p : ℤ) ^ (a - 1) * t) (s : ℤ) :
    (p : ℤ) ^ a ∣ f.eval (ξ + s * (p : ℤ) ^ (a - 1)) ↔ (p : ℤ) ∣ t + s * f.derivative.eval ξ := by
  obtain ⟨k, hk⟩ := binomExpansion f ξ (s * (p : ℤ) ^ (a - 1))
  have hpa : (p : ℤ) ^ a = (p : ℤ) ^ (a - 1) * p := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  -- `f(ξ + s p^{a-1}) = p^{a-1} (t + s f'(ξ)) + p^a (k s² p^{a-2})`, since `2a - 2 ≥ a`
  have e : f.eval (ξ + s * (p : ℤ) ^ (a - 1)) =
      (p : ℤ) ^ (a - 1) * (t + s * f.derivative.eval ξ) +
        (p : ℤ) ^ a * (k * s ^ 2 * (p : ℤ) ^ (a - 2)) := by
    rw [hk, ht]
    have : (p : ℤ) ^ a * (p : ℤ) ^ (a - 2) = ((p : ℤ) ^ (a - 1)) ^ 2 := by
      rw [← pow_add, ← pow_mul]; congr 1; omega
    linear_combination (-(k * s ^ 2)) * this
  rw [e, (dvd_add_left (dvd_mul_right _ _)), hpa]
  exact mul_dvd_mul_iff_left (pow_ne_zero _ (by exact_mod_cast hp.ne_zero))

/-- Counting the residues `0 ≤ s < p` that satisfy a condition depending only on `s (mod p)`. -/
lemma card_range_filter_eq (p : ℕ) [NeZero p] (P : ZMod p → Prop) [DecidablePred P] :
    #{s ∈ range p | P ((s : ℕ) : ZMod p)} = #{x : ZMod p | P x} := by
  refine Finset.card_nbij (fun s : ℕ ↦ (s : ZMod p)) ?_ ?_ ?_
  · intro s hs
    simp only [coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hs
    simp [hs.2]
  · intro x hx y hy hxy
    simp only [coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hx hy
    simp only at hxy
    rw [← ZMod.val_natCast_of_lt hx.1, hxy, ZMod.val_natCast_of_lt hy.1]
  · intro x hx
    simp only [coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx
    exact ⟨x.val, by simp [ZMod.val_lt, hx], ZMod.natCast_zmod_val x⟩

/-- The number of lifts `ξ + s p^{a-1}`, `0 ≤ s < p`, of a root `ξ` of `f ≡ 0 (mod p^{a-1})` to
roots of `f ≡ 0 (mod p^a)`. -/
noncomputable def numLifts (f : ℤ[X]) (p a : ℕ) (ξ : ℤ) : ℕ :=
  #{s ∈ range p | (p : ℤ) ^ a ∣ f.eval (ξ + ((s : ℕ) : ℤ) * (p : ℤ) ^ (a - 1))}

/-- **Theorem 123** [hardywright2008] (b): if `f'(ξ) ≢ 0 (mod p)`, a root `ξ` of
`f ≡ 0 (mod p^{a-1})` gives exactly one root `ξ + s p^{a-1}` of `f ≡ 0 (mod p^a)`. -/
@[kb "hardywright2008" "Thm 123, p. 124"]
theorem numLifts_eq_one (f : ℤ[X]) {p a : ℕ} (hp : p.Prime) (ha : 2 ≤ a) {ξ : ℤ}
    (hξ : (p : ℤ) ^ (a - 1) ∣ f.eval ξ) (hd : ¬(p : ℤ) ∣ f.derivative.eval ξ) :
    numLifts f p a ξ = 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ht⟩ := hξ
  have hdz : ((f.derivative.eval ξ : ℤ) : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have key : ∀ s : ℕ, (p : ℤ) ^ a ∣ f.eval (ξ + (s : ℤ) * (p : ℤ) ^ (a - 1)) ↔
      (s : ZMod p) = -(t : ZMod p) * ((f.derivative.eval ξ : ℤ) : ZMod p)⁻¹ := by
    intro s
    rw [prime_pow_dvd_eval_add_iff f hp ha ht, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    constructor
    · intro h; field_simp; linear_combination h
    · intro h; rw [h]; field_simp; ring
  rw [numLifts, Finset.filter_congr fun s _ ↦ key s,
    card_range_filter_eq p (fun x ↦ x = -(t : ZMod p) * ((f.derivative.eval ξ : ℤ) : ZMod p)⁻¹)]
  rw [Finset.filter_eq' Finset.univ, if_pos (Finset.mem_univ _), Finset.card_singleton]

/-- **Theorem 123** [hardywright2008] (a) and (c): if `f'(ξ) ≡ 0 (mod p)`, a root `ξ` of
`f ≡ 0 (mod p^{a-1})` gives no root of `f ≡ 0 (mod p^a)` if `ξ` is not one, and `p` roots
`ξ + s p^{a-1}` (every `s`) if it is. -/
@[kb "hardywright2008" "Thm 123, p. 124"]
theorem numLifts_of_dvd_derivative (f : ℤ[X]) {p a : ℕ} (hp : p.Prime) (ha : 2 ≤ a) {ξ : ℤ}
    (hξ : (p : ℤ) ^ (a - 1) ∣ f.eval ξ) (hd : (p : ℤ) ∣ f.derivative.eval ξ) :
    numLifts f p a ξ = if (p : ℤ) ^ a ∣ f.eval ξ then p else 0 := by
  classical
  obtain ⟨t, ht⟩ := hξ
  have hpa : (p : ℤ) ^ a = (p : ℤ) ^ (a - 1) * p := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  have hpt : (p : ℤ) ^ a ∣ f.eval ξ ↔ (p : ℤ) ∣ t := by
    rw [ht, hpa]; exact mul_dvd_mul_iff_left (pow_ne_zero _ (by exact_mod_cast hp.ne_zero))
  have key : ∀ s : ℕ, (p : ℤ) ^ a ∣ f.eval (ξ + (s : ℤ) * (p : ℤ) ^ (a - 1)) ↔ (p : ℤ) ∣ t := by
    intro s
    rw [prime_pow_dvd_eval_add_iff f hp ha ht, dvd_add_left (dvd_mul_of_dvd_right hd _)]
  rw [numLifts, Finset.filter_congr fun s _ ↦ key s]
  by_cases h : (p : ℤ) ^ a ∣ f.eval ξ
  · simp [h, hpt.1 h]
  · simp [h, mt hpt.2 h]

/-! ### The roots modulo `p^a` lie over the roots modulo `p^{a-1}` (§ 8.3) -/

/-- [hardywright2008, (8.3.2)–(8.3.5)]: the roots `0 ≤ x < p^a` of `f ≡ 0 (mod p^a)` are the numbers
`ξ + s p^{a-1}` with `ξ` a root modulo `p^{a-1}`, `0 ≤ ξ < p^{a-1}`, and `0 ≤ s < p`. -/
theorem rootCount_prime_pow (f : ℤ[X]) {p a : ℕ} (hp : p.Prime) (ha : 2 ≤ a) :
    rootCount f (p ^ a) =
      ∑ ξ ∈ range (p ^ (a - 1)) with (p : ℤ) ^ (a - 1) ∣ f.eval ((ξ : ℕ) : ℤ),
        numLifts f p a ((ξ : ℕ) : ℤ) := by
  classical
  have hp0 := hp.pos
  set q := p ^ (a - 1) with hq
  have hqa : p ^ a = q * p := by rw [hq, ← pow_succ, Nat.sub_add_cancel (by omega)]
  have hq0 : 0 < q := pow_pos hp0 _
  rw [rootCount_eq_card_range f (pow_pos hp0 a)]
  -- fibre over `ξ = x mod p^{a-1}`
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x : ℕ ↦ x % q)
    (t := (range q).filter fun ξ : ℕ ↦ (q : ℤ) ∣ f.eval (ξ : ℤ))]
  · refine Finset.sum_congr (by rw [hq]; push_cast; rfl) fun ξ hξ ↦ ?_
    simp only [Finset.mem_filter, Finset.mem_range] at hξ
    rw [numLifts]
    symm
    refine Finset.card_nbij (fun s : ℕ ↦ ξ + s * q) ?_ ?_ ?_
    · intro s hs
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hs
      simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_range, Set.mem_setOf_eq]
      refine ⟨⟨by rw [hqa]; nlinarith, ?_⟩, ?_⟩
      · have := hs.2
        rw [hq]; push_cast; exact this
      · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hξ.1]
    · intro s _ s' _ h
      simp only at h
      exact Nat.eq_of_mul_eq_mul_right hq0 (by omega)
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_range, Set.mem_setOf_eq] at hx
      have hxq : ξ + x / q * q = x := by rw [← hx.2]; exact Nat.mod_add_div' x q
      refine ⟨x / q, ?_, hxq⟩
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
      refine ⟨?_, ?_⟩
      · rw [Nat.div_lt_iff_lt_mul hq0, mul_comm, ← hqa]; exact hx.1.1
      · have h2 := hx.1.2
        rw [← hxq] at h2
        push_cast at h2
        rwa [hq] at h2
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_range, Set.mem_setOf_eq] at hx ⊢
    refine ⟨Nat.mod_lt _ hq0, ?_⟩
    -- `f(x) ≡ f(x mod q) (mod q)`
    have h1 : (q : ℤ) ∣ f.eval (x : ℤ) := by
      rw [hqa] at hx; push_cast at hx; exact (dvd_mul_right _ _).trans hx.2
    have h2 : ((x : ℤ) - ((x % q : ℕ) : ℤ)) ∣ f.eval (x : ℤ) - f.eval ((x % q : ℕ) : ℤ) :=
      Polynomial.sub_dvd_eval_sub _ _ _
    have h3 : (q : ℤ) ∣ (x : ℤ) - ((x % q : ℕ) : ℤ) := by
      have e : (q : ℤ) * ((x / q : ℕ) : ℤ) + ((x % q : ℕ) : ℤ) = (x : ℤ) := by
        exact_mod_cast Nat.div_add_mod x q
      exact ⟨((x / q : ℕ) : ℤ), by linarith⟩
    have := dvd_sub h1 (h3.trans h2)
    simpa using this

/-! ### Theorem 124 -/

lemma rootCount_X_pow_sub_one_eq (n m : ℕ) :
    rootCount (X ^ n - 1) m = Nat.card {x : ZMod m // x ^ n = 1} := by
  rw [rootCount]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x ↦ by simp [sub_eq_zero])

/-- **Theorem 124** [hardywright2008]: the congruence `x^{p-1} ≡ 1 (mod p^a)` has just `p - 1`
roots for every `a ≥ 1`. As in the book, each of the `p - 1` roots modulo `p` lifts uniquely to
every `p^a` by Theorem 123 (b), since `f'(ξ) = (p - 1) ξ^{p-2} ≢ 0 (mod p)`. -/
@[kb "hardywright2008" "Thm 124, p. 125"]
theorem rootCount_X_pow_pred_sub_one (p : ℕ) [hp : Fact p.Prime] {a : ℕ} (ha : 1 ≤ a) :
    rootCount (X ^ (p - 1) - 1) (p ^ a) = p - 1 := by
  classical
  have hp2 := hp.out.two_le
  induction a, ha using Nat.le_induction with
  | base =>
    rw [pow_one, rootCount_X_pow_sub_one_eq]
    exact card_pow_eq_one_of_dvd p dvd_rfl
  | succ a ha ih =>
    rw [rootCount_prime_pow _ hp.out (by omega), Nat.add_sub_cancel]
    have h1 : ∀ ξ ∈ (range (p ^ a)).filter
        (fun ξ : ℕ ↦ (p : ℤ) ^ a ∣ (X ^ (p - 1) - 1 : ℤ[X]).eval ((ξ : ℕ) : ℤ)),
        numLifts (X ^ (p - 1) - 1) p (a + 1) ((ξ : ℕ) : ℤ) = 1 := by
      intro ξ hξ
      simp only [Finset.mem_filter, Finset.mem_range] at hξ
      have hξ' : (p : ℤ) ^ (a + 1 - 1) ∣ (X ^ (p - 1) - 1 : ℤ[X]).eval ((ξ : ℕ) : ℤ) := by
        rw [Nat.add_sub_cancel]; exact hξ.2
      refine numLifts_eq_one _ hp.out (by omega) hξ' ?_
      -- `p ∤ ξ` since `ξ^{p-1} ≡ 1 (mod p)`, and `p ∤ p - 1`
      have hpZ := Nat.prime_iff_prime_int.1 hp.out
      have hpξ : ¬(p : ℤ) ∣ (ξ : ℤ) := by
        intro h
        have h1 : (p : ℤ) ∣ (ξ : ℤ) ^ (p - 1) := dvd_pow h (by omega)
        have h2 : (p : ℤ) ∣ (ξ : ℤ) ^ (p - 1) - 1 :=
          (dvd_pow_self (p : ℤ) (show a ≠ 0 by omega)).trans (by simpa using hξ.2)
        have := (dvd_sub h1 h2)
        simp only [sub_sub_cancel] at this
        exact hpZ.not_dvd_one this
      simp only [derivative_sub, derivative_X_pow, derivative_one, sub_zero, eval_mul, eval_C,
        eval_pow, eval_X]
      intro h
      rcases hpZ.dvd_or_dvd h with h | h
      · have := Int.le_of_dvd (by push_cast; omega) h
        push_cast at this
        omega
      · exact hpξ (hpZ.dvd_of_dvd_pow h)
    rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul, mul_one]
    refine Eq.trans ?_ ih
    rw [rootCount_eq_card_range _ (pow_pos hp.out.pos a)]
    push_cast
    rfl

/-! ### Theorem 125 -/

/-- `p (p - 1)/2 = p k` for `p = 2k + 1`. -/
private lemma half_totient_eq {p k : ℕ} (hk : p = 2 * k + 1) : p * (p - 1) / 2 = p * k := by
  rw [hk, Nat.add_sub_cancel, mul_comm 2 k, ← mul_assoc, Nat.mul_div_cancel _ two_pos]

/-- **Theorem 125** [hardywright2008], first part: for an odd prime `p` the congruence
`x^{p(p-1)/2} ≡ 1 (mod p²)` (8.4.1) has `p(p - 1)/2` roots: each of its `(p - 1)/2` roots modulo `p`
gives `p` roots modulo `p²` by Theorem 123 (c). -/
@[kb "hardywright2008" "Thm 125, p. 126"]
theorem rootCount_pow_half_totient (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    rootCount (X ^ (p * (p - 1) / 2) - 1) (p ^ 2) = p * (p - 1) / 2 := by
  classical
  obtain ⟨k, hk⟩ := hp.out.odd_of_ne_two hp2
  have he := half_totient_eq hk
  rw [he, rootCount_prime_pow _ hp.out le_rfl]
  have hpZ := Nat.prime_iff_prime_int.1 hp.out
  -- every root `ξ` modulo `p` gives `p` roots modulo `p²`
  have h1 : ∀ ξ ∈ (range (p ^ (2 - 1))).filter
      (fun ξ : ℕ ↦ (p : ℤ) ^ (2 - 1) ∣ (X ^ (p * k) - 1 : ℤ[X]).eval ((ξ : ℕ) : ℤ)),
      numLifts (X ^ (p * k) - 1) p 2 ((ξ : ℕ) : ℤ) = p := by
    intro ξ hξ
    simp only [Finset.mem_filter, Finset.mem_range] at hξ
    have hd : (p : ℤ) ∣ (X ^ (p * k) - 1 : ℤ[X]).derivative.eval ((ξ : ℕ) : ℤ) := by
      simp only [derivative_sub, derivative_X_pow, derivative_one, sub_zero, eval_mul, eval_C,
        eval_pow, eval_X]
      exact dvd_mul_of_dvd_left (by push_cast; exact dvd_mul_right _ _) _
    rw [numLifts_of_dvd_derivative _ hp.out le_rfl hξ.2 hd, if_pos]
    -- `u = ξ^k ≡ u^p ≡ 1 (mod p)`, so `ξ^{pk} = u^p ≡ 1 (mod p²)` by Theorem 78
    have h2 := hξ.2
    rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one, eval_sub, eval_pow, eval_X, eval_one,
      mul_comm p k, pow_mul] at h2
    show (p : ℤ) ^ 2 ∣ (X ^ (p * k) - 1 : ℤ[X]).eval ((ξ : ℕ) : ℤ)
    rw [eval_sub, eval_pow, eval_X, eval_one, mul_comm p k, pow_mul]
    set u : ℤ := ((ξ : ℕ) : ℤ) ^ k
    have hu : u ^ p ≡ 1 [ZMOD p] := (Int.modEq_iff_dvd.2 h2).symm
    have hu1 : u ≡ 1 [ZMOD (p : ℕ) ^ 1] := by
      rw [pow_one]; exact (Int.ModEq.pow_prime_eq_self hp.out u).symm.trans hu
    have := pow_prime_modEq_one (p := p) (a := 1) one_pos hu1
    exact Int.modEq_iff_dvd.1 this.symm
  rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul, mul_comm]
  congr 1
  -- the roots modulo `p` are those of `x^{(p-1)/2} ≡ 1`, i.e. the residues (Theorem 109)
  have hc := rootCount_eq_card_range (X ^ (p * k) - 1) (m := p ^ (2 - 1)) (pow_pos hp.out.pos _)
  push_cast at hc
  rw [← hc, pow_one, rootCount_X_pow_sub_one_eq]
  have : ∀ x : ZMod p, x ^ (p * k) = x ^ k := fun x ↦ by rw [pow_mul, ZMod.pow_card]
  simp only [this]
  exact card_pow_eq_one_of_dvd p ⟨2, by omega⟩

/-- The quadratic residues of `p²` (classes prime to `p` that are squares) correspond to the image of
squaring on the cyclic group `(ZMod p²)ˣ`, which has `φ(p²)/2 = p(p - 1)/2` elements. -/
theorem card_quadratic_residues_prime_sq (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    Nat.card {x : ZMod (p ^ 2) // IsUnit x ∧ IsSquare x} = p * (p - 1) / 2 := by
  have : IsCyclic (ZMod (p ^ 2))ˣ := ZMod.isCyclic_units_of_prime_pow p hp.out hp2 2
  have hcard : Nat.card (ZMod (p ^ 2))ˣ = p * (p - 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow hp.out two_pos]
    simp
  have hrange := IsCyclic.card_powMonoidHom_range (ZMod (p ^ 2))ˣ 2
  have heven : 2 ∣ p * (p - 1) := by
    obtain ⟨k, hk⟩ := hp.out.odd_of_ne_two hp2
    exact dvd_mul_of_dvd_right ⟨k, by omega⟩ _
  rw [hcard, Nat.gcd_eq_right heven] at hrange
  rw [← hrange]
  refine Nat.card_congr
    { toFun := fun x ↦ ⟨x.2.1.unit, by
        obtain ⟨y, hy⟩ := x.2.2
        have hyu : IsUnit y := isUnit_of_mul_isUnit_left (hy ▸ x.2.1)
        exact ⟨hyu.unit, by ext; simp [sq, ← hy]⟩⟩
      invFun := fun u ↦ ⟨(u : (ZMod (p ^ 2))ˣ), (u : (ZMod (p ^ 2))ˣ).isUnit, by
        obtain ⟨v, hv⟩ := u.2
        exact ⟨v, by rw [← hv]; simp [sq]⟩⟩
      left_inv := fun x ↦ by ext; simp
      right_inv := fun u ↦ by ext; simp }

/-- **Theorem 125** [hardywright2008]: for an odd prime `p` there are `p(p - 1)/2` quadratic
residues of `p²`, and these residues are the roots of `x^{p(p-1)/2} ≡ 1 (mod p²)`. -/
@[kb "hardywright2008" "Thm 125, p. 126"]
theorem quadratic_residues_prime_sq (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    Nat.card {x : ZMod (p ^ 2) // IsUnit x ∧ IsSquare x} = p * (p - 1) / 2 ∧
      ∀ x : ZMod (p ^ 2), (IsUnit x ∧ IsSquare x ↔ x ^ (p * (p - 1) / 2) = 1) := by
  classical
  refine ⟨card_quadratic_residues_prime_sq p hp2, ?_⟩
  -- every residue is a root (Theorem 72), and both sets have `p(p - 1)/2` elements
  have hsub : ∀ x : ZMod (p ^ 2), IsUnit x ∧ IsSquare x → x ^ (p * (p - 1) / 2) = 1 := by
    rintro x ⟨hx, y, rfl⟩
    have hyu : IsUnit y := isUnit_of_mul_isUnit_left hx
    have htot := ZMod.pow_totient hyu.unit
    rw [Nat.totient_prime_pow hp.out two_pos] at htot
    obtain ⟨k, hk⟩ := hp.out.odd_of_ne_two hp2
    rw [half_totient_eq hk, ← sq, ← pow_mul]
    have : 2 * (p * k) = p ^ (2 - 1) * (p - 1) := by
      subst hk; rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one, Nat.add_sub_cancel]; ring
    rw [this]
    simpa using congrArg Units.val htot
  have hR := card_quadratic_residues_prime_sq p hp2
  have hS := rootCount_pow_half_totient p hp2
  rw [rootCount_X_pow_sub_one_eq] at hS
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hR hS
  have heq : (Finset.univ.filter fun x : ZMod (p ^ 2) ↦ IsUnit x ∧ IsSquare x) =
      Finset.univ.filter fun x ↦ x ^ (p * (p - 1) / 2) = 1 :=
    Finset.eq_of_subset_of_card_le (fun x hx ↦ by simp at hx ⊢; exact hsub x hx)
      (by rw [hR, hS])
  intro x
  have := congrArg (x ∈ ·) heq
  simpa using this

end NTKB.HardyWright
