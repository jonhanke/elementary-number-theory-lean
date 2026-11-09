/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import NTKB.Attr

/-!
# Ireland–Rosen, Chapter 7: monic irreducible polynomials over a finite field

For a finite field `k` with `q` elements we prove

* Chapter 7, Lemma 2: `x^l - 1 ∣ x^m - 1` in `F[x]` iff `l ∣ m` (any field `F`);
* Chapter 7, Lemma 3: `a^l - 1 ∣ a^m - 1` iff `l ∣ m` for an integer `a > 1`;
* Chapter 7, Theorem 2: `x^(q^n) - x = ∏_{d ∣ n} F_d(x)`, where `F_d` is the product of the monic
  irreducible polynomials of degree `d`;
* its Corollary 1: `q^n = ∑_{d ∣ n} d N_d`, `N_d` the number of monic irreducibles of degree `d`;
* its Corollary 2: `n N_n = ∑_{d ∣ n} μ(n/d) q^d` (Möbius inversion);
* its Corollary 3: there is an irreducible polynomial of every degree `n ≥ 1`, by the book's
  argument that `∑_{d ∣ n} μ(n/d) q^d ≠ 0`.

The book works over `ℤ/pℤ`; the statements here are for any finite field (take `k = ZMod p`).
The divisibility criterion "a monic irreducible of degree `d` divides `x^(q^n) - x` iff `d ∣ n`"
is Mathlib's `Irreducible.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X`.
-/

open Polynomial

namespace NTKB.IrelandRosen

section Lemma2

variable {F : Type*} [Field F]

/-- **Ireland–Rosen, Chapter 7, Lemma 2.** In `F[x]`, `x^l - 1` divides `x^m - 1` iff `l ∣ m`.
The book's proof: write `m = ql + r` with `0 ≤ r < l`; then
`x^m - 1 = x^r (x^(ql) - 1) + (x^r - 1)` and `x^r - 1` has degree `< l`. -/
@[kb "irelandrosen1990" "Ch 7, Lemma 2, p. 92"]
theorem X_pow_sub_one_dvd_X_pow_sub_one_iff {l m : ℕ} :
    (X ^ l - 1 : F[X]) ∣ X ^ m - 1 ↔ l ∣ m := by
  have hXC : ∀ j : ℕ, (X ^ j - 1 : F[X]) = X ^ j - C 1 := fun j ↦ by simp
  have hdvd : ∀ {l m : ℕ}, l ∣ m → (X ^ l - 1 : F[X]) ∣ X ^ m - 1 := by
    rintro l _ ⟨c, rfl⟩
    simpa [pow_mul] using sub_dvd_pow_sub_pow (X ^ l : F[X]) 1 c
  refine ⟨fun h ↦ ?_, hdvd⟩
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · simp only [pow_zero, sub_self, zero_dvd_iff] at h
    rw [sub_eq_zero] at h
    have : m = 0 := by
      by_contra hm
      have := congrArg natDegree h
      simp at this
      exact hm this
    simp [this]
  -- `m = l * (m / l) + m % l`
  have hm : m = m % l + l * (m / l) := (Nat.mod_add_div m l).symm
  have hsplit : (X ^ m - 1 : F[X]) = X ^ (m % l) * (X ^ (l * (m / l)) - 1) + (X ^ (m % l) - 1) := by
    conv_lhs => rw [hm, pow_add]
    ring
  have h1 : (X ^ l - 1 : F[X]) ∣ X ^ (l * (m / l)) - 1 := hdvd (Dvd.intro _ rfl)
  have h2 : (X ^ l - 1 : F[X]) ∣ X ^ (m % l) - 1 := by
    have := (dvd_sub h (dvd_mul_of_dvd_right h1 (X ^ (m % l))))
    rwa [hsplit, add_sub_cancel_left] at this
  have hr : m % l < l := Nat.mod_lt m hl
  by_contra hlm
  have hr0 : m % l ≠ 0 := fun h0 ↦ hlm (Nat.dvd_of_mod_eq_zero h0)
  have hne : (X ^ (m % l) - 1 : F[X]) ≠ 0 := by
    intro h0
    have := congrArg natDegree (sub_eq_zero.mp h0)
    simp at this
    exact hr0 this
  have := natDegree_le_of_dvd h2 hne
  rw [hXC, hXC, natDegree_X_pow_sub_C, natDegree_X_pow_sub_C] at this
  omega

end Lemma2

/-- **Ireland–Rosen, Chapter 7, Lemma 3.** For an integer `a > 1`, `a^l - 1 ∣ a^m - 1` iff
`l ∣ m`. Same proof as Lemma 2, with `a` in place of `x`. -/
@[kb "irelandrosen1990" "Ch 7, Lemma 3, p. 93"]
theorem pow_sub_one_dvd_pow_sub_one_iff {a : ℕ} (ha : 1 < a) {l m : ℕ} :
    a ^ l - 1 ∣ a ^ m - 1 ↔ l ∣ m := by
  refine ⟨fun h ↦ ?_, Nat.pow_sub_one_dvd_pow_sub_one a⟩
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · simp only [pow_zero, Nat.sub_self, zero_dvd_iff] at h
    by_contra hm
    have := Nat.one_lt_pow (fun h0 : m = 0 ↦ hm (by subst h0; exact dvd_refl 0)) ha
    omega
  have hpos : ∀ j, 1 ≤ a ^ j := fun j ↦ Nat.one_le_pow j a (by omega)
  -- work in `ℤ`
  have hZ : ∀ j, ((a ^ j - 1 : ℕ) : ℤ) = (a : ℤ) ^ j - 1 := fun j ↦ by
    rw [Nat.cast_sub (hpos j)]; push_cast; ring
  have h' : ((a : ℤ) ^ l - 1) ∣ (a : ℤ) ^ m - 1 := by
    rw [← hZ, ← hZ]; exact Int.natCast_dvd_natCast.mpr h
  have hm : m = m % l + l * (m / l) := (Nat.mod_add_div m l).symm
  have hsplit : (a : ℤ) ^ m - 1 =
      (a : ℤ) ^ (m % l) * ((a : ℤ) ^ (l * (m / l)) - 1) + ((a : ℤ) ^ (m % l) - 1) := by
    conv_lhs => rw [hm, pow_add]
    ring
  have h1 : ((a : ℤ) ^ l - 1) ∣ (a : ℤ) ^ (l * (m / l)) - 1 := by
    simpa [pow_mul] using sub_dvd_pow_sub_pow ((a : ℤ) ^ l) 1 (m / l)
  have h2 : ((a : ℤ) ^ l - 1) ∣ (a : ℤ) ^ (m % l) - 1 := by
    have := dvd_sub h' (dvd_mul_of_dvd_right h1 ((a : ℤ) ^ (m % l)))
    rwa [hsplit, add_sub_cancel_left] at this
  have hr : m % l < l := Nat.mod_lt m hl
  by_contra hlm
  have hr0 : m % l ≠ 0 := fun h0 ↦ hlm (Nat.dvd_of_mod_eq_zero h0)
  have hlt : a ^ (m % l) < a ^ l := Nat.pow_lt_pow_right ha hr
  have hgt : 1 < a ^ (m % l) := Nat.one_lt_pow hr0 ha
  have hpos3 : (0 : ℤ) < (a : ℤ) ^ (m % l) - 1 := by
    rw [← hZ]; exact_mod_cast (by omega : 0 < a ^ (m % l) - 1)
  have hle := Int.le_of_dvd hpos3 h2
  rw [← hZ, ← hZ] at hle
  have := Int.ofNat_le.mp hle
  omega

section FiniteField

variable (k : Type*) [Field k] [Finite k]

/-- The polynomials of `natDegree ≤ d` over a finite field form a finite set. -/
theorem finite_setOf_natDegree_le (d : ℕ) : {f : k[X] | f.natDegree ≤ d}.Finite := by
  have := Fintype.ofFinite k
  refine Set.Finite.of_injOn (f := fun f : k[X] ↦ fun i : Fin (d + 1) ↦ f.coeff i)
    (t := Set.univ) (fun _ _ ↦ trivial) ?_ Set.finite_univ
  intro f hf g hg hfg
  ext n
  by_cases hn : n ≤ d
  · exact congrFun hfg ⟨n, by omega⟩
  · simp only [Set.mem_ofPred_eq] at hf hg
    rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

/-- The finite set of monic irreducible polynomials of degree `d` over the finite field `k`. -/
noncomputable def monicIrreducibles (d : ℕ) : Finset k[X] :=
  ((finite_setOf_natDegree_le k d).subset
    (t := {f : k[X] | f.Monic ∧ Irreducible f ∧ f.natDegree = d})
    (fun _ hf ↦ hf.2.2.le)).toFinset

variable {k} in
@[simp]
theorem mem_monicIrreducibles {d : ℕ} {f : k[X]} :
    f ∈ monicIrreducibles k d ↔ f.Monic ∧ Irreducible f ∧ f.natDegree = d := by
  simp [monicIrreducibles]

/-- `F_d(x)`: the product of the monic irreducible polynomials of degree `d` (Ireland–Rosen,
Chapter 7, Section 2). -/
noncomputable def prodMonicIrreducibles (d : ℕ) : k[X] := ∏ f ∈ monicIrreducibles k d, f

/-- `N_d`: the number of monic irreducible polynomials of degree `d`. -/
noncomputable def numMonicIrreducibles (d : ℕ) : ℕ := (monicIrreducibles k d).card

theorem monic_prodMonicIrreducibles (d : ℕ) : (prodMonicIrreducibles k d).Monic :=
  monic_prod_of_monic _ _ fun _ hf ↦ (mem_monicIrreducibles.mp hf).1

theorem natDegree_prodMonicIrreducibles (d : ℕ) :
    (prodMonicIrreducibles k d).natDegree = d * numMonicIrreducibles k d := by
  rw [prodMonicIrreducibles, natDegree_prod_of_monic _ _ fun _ hf ↦ (mem_monicIrreducibles.mp hf).1,
    Finset.sum_congr rfl fun f hf ↦ (mem_monicIrreducibles.mp hf).2.2, Finset.sum_const,
    smul_eq_mul, mul_comm, numMonicIrreducibles]

/-- **Ireland–Rosen, Chapter 7, Theorem 2.** For a finite field `k` with `q` elements and
`n ≥ 1`, `x^(q^n) - x = ∏_{d ∣ n} F_d(x)`, where `F_d` is the product of the monic irreducible
polynomials of degree `d`. As in the book: `x^(q^n) - x` has no repeated factor (its derivative
is `-1`), and a monic irreducible of degree `d` divides it iff `d ∣ n`. -/
@[kb "irelandrosen1990" "Ch 7, Theorem 2, p. 95"]
theorem X_pow_card_pow_sub_X_eq_prod {n : ℕ} (hn : n ≠ 0) :
    (X ^ Nat.card k ^ n - X : k[X]) = ∏ d ∈ n.divisors, prodMonicIrreducibles k d := by
  classical
  have hq : 1 < Nat.card k := Finite.one_lt_card
  set g : k[X] := X ^ Nat.card k ^ n - X with hg
  have hg0 : g ≠ 0 := X_pow_sub_X_ne_zero (Nat.one_lt_pow hn hq)
  obtain ⟨p, hp⟩ := CharP.exists k
  have hpprime : p.Prime := CharP.char_is_prime k p
  -- `g` is squarefree
  have hsep : g.Separable := by
    apply galois_poly_separable p
    have : (p : ℕ) ∣ Nat.card k := by
      have := Fintype.ofFinite k
      obtain ⟨m, -, hcard⟩ := FiniteField.card k p
      rw [Nat.card_eq_fintype_card, hcard]
      exact dvd_pow_self _ (PNat.ne_zero m)
    exact this.trans (dvd_pow_self _ hn)
  have hsq : Squarefree g := hsep.squarefree
  have hnodup := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hg0).mp hsq
  -- the monic irreducible factors of `g`
  have hmem : ∀ f, f ∈ UniqueFactorizationMonoid.normalizedFactors g ↔
      f ∈ n.divisors.biUnion (monicIrreducibles k) := by
    intro f
    rw [UniqueFactorizationMonoid.mem_normalizedFactors_iff' hg0, Finset.mem_biUnion]
    constructor
    · rintro ⟨hi, hnorm, hdvd⟩
      have hmonic : f.Monic := by
        rw [← hnorm]; exact monic_normalize hi.ne_zero
      exact ⟨f.natDegree, Nat.mem_divisors.mpr
        ⟨hi.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hdvd, hn⟩, mem_monicIrreducibles.mpr
        ⟨hmonic, hi, rfl⟩⟩
    · rintro ⟨d, hd, hf⟩
      obtain ⟨hmonic, hi, rfl⟩ := mem_monicIrreducibles.mp hf
      exact ⟨hi, hmonic.normalize_eq_self,
        hi.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.mp (Nat.mem_divisors.mp hd).1⟩
  have hfin : (UniqueFactorizationMonoid.normalizedFactors g).toFinset =
      n.divisors.biUnion (monicIrreducibles k) := by
    ext f; rw [Multiset.mem_toFinset, hmem]
  have hgmonic : g.Monic := by
    apply monic_X_pow_sub
    rw [degree_X]
    exact_mod_cast Nat.one_lt_pow hn hq
  calc g = (UniqueFactorizationMonoid.normalizedFactors g).prod := by
        refine (eq_of_monic_of_associated ?_ hgmonic
          (UniqueFactorizationMonoid.prod_normalizedFactors hg0)).symm
        simpa using monic_multiset_prod_of_monic _ id fun f hf ↦ by
          obtain ⟨hi, hnorm, -⟩ :=
            (UniqueFactorizationMonoid.mem_normalizedFactors_iff' hg0).mp hf
          rw [← hnorm]; exact monic_normalize hi.ne_zero
    _ = ∏ f ∈ (UniqueFactorizationMonoid.normalizedFactors g).toFinset, f := by
        rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, hnodup.dedup, Multiset.map_id']
    _ = ∏ d ∈ n.divisors, prodMonicIrreducibles k d := by
        rw [hfin, Finset.prod_biUnion]
        · rfl
        · intro d _ e _ hde
          simp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro f hf hf'
          exact hde ((mem_monicIrreducibles.mp hf).2.2.symm.trans
            (mem_monicIrreducibles.mp hf').2.2)

/-- **Ireland–Rosen, Chapter 7, Corollary 1 to Theorem 2.** `q^n = ∑_{d ∣ n} d N_d` for
`n ≥ 1`, obtained by comparing degrees in Theorem 2. -/
@[kb "irelandrosen1990" "Ch 7, Corollary 1 to Theorem 2, p. 95"]
theorem card_pow_eq_sum_divisors {n : ℕ} (hn : n ≠ 0) :
    Nat.card k ^ n = ∑ d ∈ n.divisors, d * numMonicIrreducibles k d := by
  have hq : 1 < Nat.card k := Finite.one_lt_card
  have := congrArg natDegree (X_pow_card_pow_sub_X_eq_prod k hn)
  rw [natDegree_X_pow_sub_X (Nat.one_lt_pow hn hq),
    natDegree_prod_of_monic _ _ fun d _ ↦ monic_prodMonicIrreducibles k d] at this
  rw [this]
  exact Finset.sum_congr rfl fun d _ ↦ natDegree_prodMonicIrreducibles k d

/-- **Ireland–Rosen, Chapter 7, Corollary 2 to Theorem 2.** `N_n = n⁻¹ ∑_{d ∣ n} μ(n/d) q^d`,
in the division-free form `n N_n = ∑_{d ∣ n} μ(n/d) q^d`, by Möbius inversion of
Corollary 1. -/
@[kb "irelandrosen1990" "Ch 7, Corollary 2 to Theorem 2, p. 95"]
theorem mul_numMonicIrreducibles_eq {n : ℕ} (hn : n ≠ 0) :
    ((n * numMonicIrreducibles k n : ℕ) : ℤ) =
      ∑ d ∈ n.divisors, ArithmeticFunction.moebius (n / d) * (Nat.card k : ℤ) ^ d := by
  have key := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℤ)
    (f := fun d ↦ ((d * numMonicIrreducibles k d : ℕ) : ℤ))
    (g := fun n ↦ (Nat.card k : ℤ) ^ n)).mp (fun m hm ↦ by
      rw [← Nat.cast_sum, ← card_pow_eq_sum_divisors k hm.ne']; push_cast; rfl) n
    (Nat.pos_of_ne_zero hn)
  rw [← key]
  exact Nat.sum_divisorsAntidiagonal' (fun x y ↦
    (ArithmeticFunction.moebius x : ℤ) * (Nat.card k : ℤ) ^ y)

/-- **Ireland–Rosen, Chapter 7, Corollary 3 to Theorem 2.** Over a finite field there is a
(monic) irreducible polynomial of every degree `n ≥ 1`. The book's proof: by Corollary 2,
`n N_n = q^n + ∑_{d ∣ n, d < n} μ(n/d) q^d`, a sum of distinct powers of `q` with coefficients
`0, ±1` and leading term `q^n`, which is not zero. -/
@[kb "irelandrosen1990" "Ch 7, Corollary 3 to Theorem 2, p. 95"]
theorem exists_monic_irreducible_natDegree_eq {n : ℕ} (hn : n ≠ 0) :
    ∃ f : k[X], f.Monic ∧ Irreducible f ∧ f.natDegree = n := by
  have hq : 2 ≤ Nat.card k := Finite.one_lt_card
  suffices h : 0 < numMonicIrreducibles k n by
    obtain ⟨f, hf⟩ := Finset.card_pos.mp h
    exact ⟨f, mem_monicIrreducibles.mp hf⟩
  have key := mul_numMonicIrreducibles_eq k hn
  rw [← Finset.add_sum_erase _ _ (Nat.mem_divisors_self n hn), Nat.div_self
    (Nat.pos_of_ne_zero hn), ArithmeticFunction.moebius_apply_one, one_mul] at key
  -- the remaining terms are bounded by `∑_{d < n} q^d < q^n`
  have hbound : |∑ d ∈ n.divisors.erase n, (ArithmeticFunction.moebius (n / d) : ℤ) *
      (Nat.card k : ℤ) ^ d| < (Nat.card k : ℤ) ^ n := by
    calc _ ≤ ∑ d ∈ n.divisors.erase n, |(ArithmeticFunction.moebius (n / d) : ℤ) *
          (Nat.card k : ℤ) ^ d| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ n.divisors.erase n, ((Nat.card k ^ d : ℕ) : ℤ) := by
          refine Finset.sum_le_sum fun d _ ↦ ?_
          rw [abs_mul, Nat.cast_pow]
          rw [abs_of_nonneg (by positivity : (0 : ℤ) ≤ (Nat.card k : ℤ) ^ d)]
          exact mul_le_of_le_one_left (by positivity) (ArithmeticFunction.abs_moebius_le_one)
      _ < (Nat.card k : ℤ) ^ n := by
          rw [← Nat.cast_sum]
          exact_mod_cast Nat.geomSum_lt hq fun d hd ↦ by
            obtain ⟨hne, hd⟩ := Finset.mem_erase.mp hd
            exact lt_of_le_of_ne (Nat.divisor_le hd) hne
  rcases Nat.eq_zero_or_pos (numMonicIrreducibles k n) with h0 | h0
  · rw [h0, mul_zero, Nat.cast_zero] at key
    rw [abs_lt] at hbound
    linarith [hbound.1]
  · exact h0

/-- Ireland–Rosen, Chapter 7, Corollary 3, for the book's field `ℤ/pℤ`. -/
theorem exists_irreducible_zmod (p : ℕ) [Fact p.Prime] {n : ℕ} (hn : n ≠ 0) :
    ∃ f : (ZMod p)[X], Irreducible f ∧ f.natDegree = n :=
  let ⟨f, _, hi, hd⟩ := exists_monic_irreducible_natDegree_eq (ZMod p) hn
  ⟨f, hi, hd⟩

end FiniteField

end NTKB.IrelandRosen
