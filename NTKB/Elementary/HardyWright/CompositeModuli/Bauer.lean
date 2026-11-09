/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.Congruences.Lagrange
import NTKB.Elementary.HardyWright.Residues.Basic

/-!
# Bauer's identical congruence (Hardy–Wright, §§ 8.5 and 8.6)

`NTKB.HardyWright.bauerPoly m` is `f_m(x) = ∏_{t ∈ t(m)} (x - t)`, the product over the `φ(m)`
numbers `0 ≤ t < m` prime to `m` [hardywright2008, (8.5.1)]. Congruence of integral polynomials
modulo `n` is equality of their images in `(ZMod n)[X]`.

* Theorem 126 (8.5.4): for an odd prime `p` and `a ≥ 1`, `f_{p^a}(x) ≡ (x^{p-1} - 1)^{p^{a-1}}
  (mod p^a)`.
* Theorem 126 (8.5.3): if `p^a` is the highest power of the odd prime `p` dividing `m`, then
  `f_m(x) ≡ (x^{p-1} - 1)^{φ(m)/(p-1)} (mod p^a)`.
-/

open Polynomial Finset

namespace NTKB.HardyWright

/-- First-order expansion: if all products `e_i e_j` vanish, then
`∏ (a_i + e_i) = ∏ a_i + ∑_i e_i ∏_{j ≠ i} a_j`. -/
lemma prod_add_of_mul_eq_zero {R ι : Type*} [CommRing R] [DecidableEq ι] (s : Finset ι)
    (a e : ι → R) (he : ∀ i j, e i * e j = 0) :
    ∏ i ∈ s, (a i + e i) = ∏ i ∈ s, a i + ∑ i ∈ s, e i * ∏ j ∈ s.erase i, a j := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, Finset.prod_insert hb, ih, Finset.sum_insert hb,
      Finset.erase_insert hb]
    have : ∀ i ∈ s, e i * ∏ j ∈ (insert b s).erase i, a j =
        a b * (e i * ∏ j ∈ s.erase i, a j) := by
      intro i hi
      rw [Finset.erase_insert_of_ne (fun h : b = i ↦ hb (h ▸ hi)),
        Finset.prod_insert (fun h ↦ hb (Finset.mem_of_mem_erase h))]
      ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
    have h0 : e b * ∑ i ∈ s, e i * ∏ j ∈ s.erase i, a j = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun i _ ↦ by rw [← mul_assoc, he, zero_mul]
    linear_combination h0

/-- `f_m(x) = ∏_{t ∈ t(m)} (x - t)` [hardywright2008, (8.5.1)]. -/
noncomputable def bauerPoly (m : ℕ) : ℤ[X] :=
  ∏ t ∈ (range m).filter (·.Coprime m), (X - C (t : ℤ))

/-- Two integral polynomials are congruent modulo `m` iff `C m` divides their difference. -/
lemma map_eq_map_iff_C_dvd (m : ℕ) (f g : ℤ[X]) :
    f.map (Int.castRingHom (ZMod m)) = g.map (Int.castRingHom (ZMod m)) ↔ C (m : ℤ) ∣ f - g := by
  rw [Polynomial.C_dvd_iff_dvd_coeff, ← sub_eq_zero, ← Polynomial.map_sub, Polynomial.ext_iff]
  simp only [coeff_map, coeff_zero, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]

lemma coprime_prime_pow_iff {p k t : ℕ} (hp : p.Prime) (hk : 0 < k) :
    t.Coprime (p ^ k) ↔ ¬p ∣ t := by
  rw [Nat.coprime_pow_right_iff hk, Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]

/-- The residues prime to `p^{a+1}` are the numbers `t + v p^a` with `t` prime to `p^a`,
`0 ≤ t < p^a`, `0 ≤ v < p` [hardywright2008, § 8.5]. -/
lemma filter_coprime_prime_pow_succ {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    (range (p ^ (a + 1))).filter (·.Coprime (p ^ (a + 1))) =
      (((range (p ^ a)).filter (·.Coprime (p ^ a))) ×ˢ range p).image
        (fun x ↦ x.1 + x.2 * p ^ a) := by
  have hpa : 0 < p ^ a := pow_pos hp.pos a
  ext x
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Finset.mem_product,
    Prod.exists, coprime_prime_pow_iff hp (by omega : 0 < a + 1), coprime_prime_pow_iff hp
      (by omega : 0 < a)]
  constructor
  · rintro ⟨hx, hpx⟩
    refine ⟨x % p ^ a, x / p ^ a, ⟨⟨Nat.mod_lt _ hpa, ?_⟩, ?_⟩, Nat.mod_add_div' x (p ^ a)⟩
    · intro h
      apply hpx
      rw [← Nat.mod_add_div' x (p ^ a)]
      exact dvd_add h (dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) _)
    · rw [Nat.div_lt_iff_lt_mul hpa]; rw [pow_succ] at hx; linarith
  · rintro ⟨t, v, ⟨⟨ht, hpt⟩, hv⟩, rfl⟩
    refine ⟨?_, fun h ↦ hpt ?_⟩
    · calc t + v * p ^ a < p ^ a + v * p ^ a := Nat.add_lt_add_right ht _
        _ = (v + 1) * p ^ a := by ring
        _ ≤ p * p ^ a := Nat.mul_le_mul_right _ hv
        _ = p ^ (a + 1) := by ring
    · exact (Nat.dvd_add_right (dvd_mul_of_dvd_right (dvd_pow_self p (show a ≠ 0 by omega)) v)).1
        (by rwa [add_comm] at h)

/-- `f_p(x) ≡ x^{p-1} - 1 (mod p)`: Theorem 112. -/
lemma bauerPoly_prime_map (p : ℕ) [hp : Fact p.Prime] :
    (bauerPoly p).map (Int.castRingHom (ZMod p)) = X ^ (p - 1) - 1 := by
  have hfilt : (range p).filter (·.Coprime p) = Icc 1 (p - 1) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.out]
    have := hp.out.two_le
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨Nat.one_le_iff_ne_zero.2 (by rintro rfl; exact h2 (dvd_zero p)), by omega⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, fun h ↦ absurd (Nat.le_of_dvd (by omega) h) (by omega)⟩
  rw [bauerPoly, hfilt]
  exact lagrangePoly_map p

/-- `C (p^k) = 0` in `(ZMod p^n)[X]` for `k ≥ n`. -/
lemma C_prime_pow_eq_zero (p : ℕ) {n k : ℕ} (hk : n ≤ k) :
    (C ((p ^ k : ℕ) : ZMod (p ^ n)) : (ZMod (p ^ n))[X]) = 0 := by
  rw [show p ^ k = p ^ n * p ^ (k - n) by rw [← pow_add]; congr 1; omega, Nat.cast_mul,
    ZMod.natCast_self, zero_mul, C_0]

/-- **Theorem 126** [hardywright2008], (8.5.4): for an odd prime `p` and `a ≥ 1`,
`f_{p^a}(x) = ∏_{t ∈ t(p^a)} (x - t) ≡ (x^{p-1} - 1)^{p^{a-1}} (mod p^a)`. Following the book:
`f_{p^a}(x) = ∏_{v < p} f_{p^{a-1}}(x - v p^{a-1}) ≡ f_{p^{a-1}}(x)^p (mod p^a)`, since
`∑ v = p(p - 1)/2 ≡ 0 (mod p)`, and induction. -/
@[kb "hardywright2008" "Thm 126, p. 127"]
theorem bauerPoly_prime_pow (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) {a : ℕ} (ha : 1 ≤ a) :
    (bauerPoly (p ^ a)).map (Int.castRingHom (ZMod (p ^ a))) =
      (X ^ (p - 1) - 1) ^ (p ^ (a - 1)) := by
  classical
  induction a, ha using Nat.le_induction with
  | base =>
    have key : ∀ n, n = p → (bauerPoly n).map (Int.castRingHom (ZMod n)) = X ^ (p - 1) - 1 := by
      rintro n rfl; exact bauerPoly_prime_map n
    exact (key (p ^ 1) (pow_one p)).trans (by rw [Nat.sub_self, pow_zero]; exact (pow_one _).symm)
  | succ a ha ih =>
    set R := ZMod (p ^ (a + 1))
    set φ := Int.castRingHom R
    have hodd : p % 2 = 1 := Nat.odd_iff.1 (hp.out.odd_of_ne_two hp2)
    -- the inductive hypothesis, as an identity of integral polynomials
    obtain ⟨G, hG⟩ : C ((p ^ a : ℕ) : ℤ) ∣ bauerPoly (p ^ a) - (X ^ (p - 1) - 1) ^ (p ^ (a - 1)) := by
      rw [← map_eq_map_iff_C_dvd, ih]
      simp
    set T := (range (p ^ a)).filter (·.Coprime (p ^ a)) with hT
    set F : R[X] := (bauerPoly (p ^ a)).map φ with hF
    set D : R[X] := ∑ t ∈ T, ∏ t' ∈ T.erase t, (X - C (t' : R)) with hD
    have hFprod : F = ∏ t ∈ T, (X - C (t : R)) := by
      rw [hF, bauerPoly, Polynomial.map_prod]; simp [hT]
    -- (i) `f_{p^{a+1}}(x) = ∏_{v < p} ∏_{t ∈ t(p^a)} (x - t - v p^a)`
    have hdec : bauerPoly (p ^ (a + 1)) =
        ∏ v ∈ range p, ∏ t ∈ T, (X - C (t : ℤ) + -C ((v * p ^ a : ℕ) : ℤ)) := by
      rw [bauerPoly, filter_coprime_prime_pow_succ hp.out ha, Finset.prod_image, Finset.prod_product,
        Finset.prod_comm]
      · refine Finset.prod_congr rfl fun v _ ↦ Finset.prod_congr rfl fun t _ ↦ ?_
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, C_add, C_mul]; ring
      · rintro ⟨t, v⟩ htv ⟨t', v'⟩ htv' h
        simp only [Finset.coe_product, Set.mem_prod, Finset.coe_filter, Finset.mem_range,
          Set.mem_setOf_eq, Finset.coe_range, Set.mem_Iio] at htv htv' h
        have hpa : 0 < p ^ a := pow_pos hp.out.pos a
        have h1 : t = t' := by
          have := congrArg (· % p ^ a) h
          simpa [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt htv.1.1,
            Nat.mod_eq_of_lt htv'.1.1] using this
        subst h1
        have : v * p ^ a = v' * p ^ a := by omega
        rw [Nat.eq_of_mul_eq_mul_right hpa this]
    -- `e_v e_w = 0` for `e_v = -v p^a`
    have hsq : ∀ v w : ℕ, (-C ((v * p ^ a : ℕ) : R)) * (-C ((w * p ^ a : ℕ) : R)) = 0 := by
      intro v w
      rw [neg_mul_neg, ← C_mul, ← Nat.cast_mul,
        show v * p ^ a * (w * p ^ a) = (v * w) * p ^ (a + a) by ring, Nat.cast_mul, C_mul,
        C_prime_pow_eq_zero p (by omega), mul_zero]
    -- (ii) each inner product is `F - v p^a D`
    have hinner : ∀ v : ℕ, (∏ t ∈ T, (X - C (t : ℤ) + -C ((v * p ^ a : ℕ) : ℤ))).map φ =
        F + (-C ((v * p ^ a : ℕ) : R)) * D := by
      intro v
      rw [Polynomial.map_prod]
      have : ∀ t ∈ T, (X - C (t : ℤ) + -C ((v * p ^ a : ℕ) : ℤ)).map φ =
          (X - C (t : R)) + (-C ((v * p ^ a : ℕ) : R)) := fun t _ ↦ by simp
      rw [Finset.prod_congr rfl this,
        prod_add_of_mul_eq_zero T _ (fun _ ↦ -C ((v * p ^ a : ℕ) : R)) (fun _ _ ↦ hsq v v),
        ← hFprod, ← Finset.mul_sum]
    -- (iii) the outer product is `F^p`, since `∑ v p^a = p^{a+1} (p - 1)/2 ≡ 0`
    have houter : (bauerPoly (p ^ (a + 1))).map φ = F ^ p := by
      rw [hdec, Polynomial.map_prod, Finset.prod_congr rfl fun v _ ↦ hinner v,
        prod_add_of_mul_eq_zero (range p) (fun _ ↦ F) (fun v ↦ -C ((v * p ^ a : ℕ) : R) * D)
          (fun v w ↦ by
            rw [show -C ((v * p ^ a : ℕ) : R) * D * (-C ((w * p ^ a : ℕ) : R) * D) =
              (-C ((v * p ^ a : ℕ) : R)) * (-C ((w * p ^ a : ℕ) : R)) * D ^ 2 by ring,
              hsq, zero_mul]),
        Finset.prod_const, Finset.card_range]
      have hsum : ∑ v ∈ range p, -C ((v * p ^ a : ℕ) : R) * D *
          ∏ j ∈ (range p).erase v, F = 0 := by
        have : ∀ v ∈ range p, -C ((v * p ^ a : ℕ) : R) * D * ∏ j ∈ (range p).erase v, F =
            -C ((v * p ^ a : ℕ) : R) * (D * F ^ (p - 1)) := by
          intro v hv
          rw [Finset.prod_const, Finset.card_erase_of_mem hv, Finset.card_range]; ring
        rw [Finset.sum_congr rfl this, ← Finset.sum_mul]
        have hs : ∑ v ∈ range p, -C ((v * p ^ a : ℕ) : R) = 0 := by
          rw [Finset.sum_neg_distrib, ← map_sum, ← Nat.cast_sum, ← Finset.sum_mul,
            Finset.sum_range_id]
          have : p * (p - 1) / 2 * p ^ a = (p - 1) / 2 * p ^ (a + 1) := by
            have h2 : 2 ∣ p - 1 := ⟨(p - 1) / 2, by omega⟩
            rw [Nat.mul_div_assoc p h2, pow_succ]
            ring
          rw [this, Nat.cast_mul, C_mul, C_prime_pow_eq_zero p le_rfl, mul_zero, neg_zero]
        rw [hs, zero_mul]
      rw [hsum, add_zero]

    -- (iv) `F ≡ (x^{p-1} - 1)^{p^{a-1}} (mod p^a)` gives `F^p ≡ (x^{p-1} - 1)^{p^a} (mod p^{a+1})`
    set H : R[X] := ((X : R[X]) ^ (p - 1) - 1) ^ (p ^ (a - 1)) with hH
    set ε : R[X] := C ((p ^ a : ℕ) : R) * G.map φ with hε
    have hFH : F = H + ε := by
      have := congrArg (Polynomial.map φ) hG
      simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, map_C, map_X,
        Polynomial.map_one] at this
      rw [hF, hH, hε]
      simp only [eq_intCast, Int.cast_natCast] at this
      linear_combination this
    have hεε : ε * ε = 0 := by
      have h : C ((p ^ a : ℕ) : R) * C ((p ^ a : ℕ) : R) = 0 := by
        rw [← C_mul, ← Nat.cast_mul, ← pow_add, C_prime_pow_eq_zero p (by omega)]
      rw [hε]
      linear_combination (G.map φ) ^ 2 * h

    have hpow : (H + ε) ^ p = ∏ _v ∈ range p, (H + ε) := by
      rw [Finset.prod_const, Finset.card_range]
    have hpε : ∑ v ∈ range p, ε * ∏ j ∈ (range p).erase v, H = 0 := by
      have : ∀ v ∈ range p, ε * ∏ j ∈ (range p).erase v, H = ε * H ^ (p - 1) := by
        intro v hv
        rw [Finset.prod_const, Finset.card_erase_of_mem hv, Finset.card_range]
      rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hε,
        ← mul_assoc, ← mul_assoc, ← C_eq_natCast, ← C_mul, ← Nat.cast_mul, ← pow_succ',
        C_prime_pow_eq_zero p le_rfl, zero_mul, zero_mul]
    rw [houter, hFH, hpow,
      prod_add_of_mul_eq_zero (range p) (fun _ ↦ H) (fun _ ↦ ε) (fun _ _ ↦ hεε), hpε, add_zero,
      Finset.prod_const, Finset.card_range, hH, ← pow_mul, ← pow_succ, Nat.sub_add_cancel ha,
      Nat.add_sub_cancel]

/-! ### Theorem 126 for general `m` -/

/-- A function of the residue class multiplied over a complete set of residues prime to `n`. -/
theorem IsReducedResidueSystem.prod_eq {ι M : Type*} [CommMonoid M] {n : ℕ} [NeZero n] [Fintype ι]
    {a : ι → ℤ} (ha : IsReducedResidueSystem n a) (G : ZMod n → M) :
    ∏ i, G (a i) = ∏ u : (ZMod n)ˣ, G u := by
  obtain ⟨hu, hb⟩ := isReducedResidueSystem_iff.1 ha
  rw [← hb.prod_comp (fun u : (ZMod n)ˣ ↦ G u)]
  simp

/-- The numbers `0 ≤ t < m` prime to `m` form a complete set of residues prime to `m`. -/
theorem isReducedResidueSystem_filter (m : ℕ) [NeZero m] :
    IsReducedResidueSystem m (fun t : {t // t ∈ (range m).filter (·.Coprime m)} ↦ ((t : ℕ) : ℤ)) := by
  refine ⟨fun t ↦ ?_, fun t s hts ↦ ?_, fun x hx ↦ ?_⟩
  · exact Nat.isCoprime_iff_coprime.2 (Finset.mem_filter.1 t.2).2
  · have h1 := (Finset.mem_filter.1 t.2).1
    have h2 := (Finset.mem_filter.1 s.2).1
    rw [Finset.mem_range] at h1 h2
    simp only [Int.cast_natCast] at hts
    exact Subtype.ext (by rw [← ZMod.val_natCast_of_lt h1, ← ZMod.val_natCast_of_lt h2, hts])
  · refine ⟨⟨x.val, Finset.mem_filter.2 ⟨Finset.mem_range.2 (ZMod.val_lt x), ?_⟩⟩, by simp⟩
    simpa using ZMod.val_coe_unit_coprime hx.unit

/-- [hardywright2008, § 8.5] (Darlington's argument): if `(n, M) = 1`, then
`f_{nM}(x) ≡ f_n(x)^{φ(M)} (mod n)`: the numbers `t M + T n` (`t ∈ t(n)`, `T ∈ t(M)`) form `t(nM)`
(Theorem 61), `t M + T n ≡ t M (mod n)`, and `t M` runs through `t(n)` (Theorem 58). -/
theorem bauerPoly_map_mul_coprime {n M : ℕ} [NeZero n] [NeZero M] (hcop : n.Coprime M) :
    (bauerPoly (n * M)).map (Int.castRingHom (ZMod n)) =
      ((bauerPoly n).map (Int.castRingHom (ZMod n))) ^ M.totient := by
  classical
  have : NeZero (n * M) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne M)⟩
  set R := ZMod n
  set π : ZMod (n * M) →+* R := ZMod.castHom (dvd_mul_right _ _) R
  set G : ZMod (n * M) → R[X] := fun x ↦ X - C (π x)
  -- the two complete sets of residues prime to `n M`
  set ι := {t // t ∈ (range n).filter (·.Coprime n)}
  set κ := {T // T ∈ (range M).filter (·.Coprime M)}
  have hι := isReducedResidueSystem_filter n
  have hκ := isReducedResidueSystem_filter M
  have hm := isReducedResidueSystem_filter (n * M)
  have hcrt := hι.crt hcop hκ
  have h1 : (bauerPoly (n * M)).map (Int.castRingHom R) =
      ∏ t : {t // t ∈ (range (n * M)).filter (·.Coprime (n * M))}, G ((t : ℕ) : ℤ) := by
    rw [bauerPoly, Polynomial.map_prod, ← Finset.prod_coe_sort]
    simp [G, π]
  rw [h1, hm.prod_eq G, ← hcrt.prod_eq G, Fintype.prod_prod_type]
  -- modulo `n`, `T n + t M ≡ t M`
  have h0 : ((n : ℕ) : R) = 0 := ZMod.natCast_self _
  have h2 : ∀ (t : ι) (T : κ), G ((((T : ℕ) : ℤ) * ((n : ℕ) : ℤ) + ((t : ℕ) : ℤ) * (M : ℤ) : ℤ)) =
      X - C (((t : ℕ) : R) * (M : R)) := by
    intro t T
    simp only [G]
    rw [map_intCast]
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
    rw [h0, mul_zero, zero_add]
  simp only [h2]
  rw [Finset.prod_comm, Finset.prod_const, Finset.card_univ]
  -- `t M` runs through `t(n)` (Theorem 58)
  have hι' := hι.mul (k := (M : ℤ)) (Nat.isCoprime_iff_coprime.2 hcop.symm)
  have h3 : ∏ t : ι, (X - C (((t : ℕ) : R) * (M : R))) = ∏ t : ι, (X - C (((t : ℕ) : R))) := by
    have e1 := hι'.prod_eq (fun x : R ↦ X - C x)
    have e2 := hι.prod_eq (fun x : R ↦ X - C x)
    have := e1.trans e2.symm
    simp only [Int.cast_mul, Int.cast_natCast] at this
    simpa only [mul_comm ((M : ℕ) : R)] using this
  rw [h3]
  have h4 : ∏ t : ι, (X - C (((t : ℕ) : R))) = (bauerPoly n).map (Int.castRingHom R) := by
    rw [bauerPoly, Polynomial.map_prod]
    refine (Finset.prod_coe_sort _ (fun t : ℕ ↦ X - C ((t : ℕ) : R))).trans
      (Finset.prod_congr rfl fun t _ ↦ ?_)
    simp [Polynomial.map_natCast]
  rw [h4]
  congr 1
  rw [Fintype.card_coe, Nat.totient_eq_card_coprime]
  congr 1
  ext x; simp [Nat.coprime_comm]

/-- Splitting off the exact power `p^a` of a prime `p` dividing `m`. -/
lemma exists_eq_prime_pow_mul {p m a : ℕ} (hp : p.Prime) (hm : m ≠ 0) (hpa : p ^ a ∣ m)
    (hpa1 : ¬p ^ (a + 1) ∣ m) : ∃ M, m = p ^ a * M ∧ M ≠ 0 ∧ (p ^ a).Coprime M := by
  obtain ⟨M, rfl⟩ := hpa
  refine ⟨M, rfl, by rintro rfl; simp at hm, Nat.Coprime.pow_left _ ?_⟩
  refine (Nat.Prime.coprime_iff_not_dvd hp).2 ?_
  rintro ⟨c, rfl⟩; exact hpa1 ⟨c, by ring⟩

/-- **Theorem 126** [hardywright2008], (8.5.3): if `p` is an odd prime divisor of `m` and `p^a` is
the highest power of `p` dividing `m`, then
`f_m(x) = ∏_{t ∈ t(m)} (x - t) ≡ (x^{p-1} - 1)^{φ(m)/(p-1)} (mod p^a)`. -/
@[kb "hardywright2008" "Thm 126, p. 127"]
theorem bauerPoly_map_prime_pow (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) {m a : ℕ} (hm : m ≠ 0)
    (ha : 1 ≤ a) (hpa : p ^ a ∣ m) (hpa1 : ¬p ^ (a + 1) ∣ m) :
    (bauerPoly m).map (Int.castRingHom (ZMod (p ^ a))) =
      (X ^ (p - 1) - 1) ^ (m.totient / (p - 1)) := by
  obtain ⟨M, rfl, hM0, hcop⟩ := exists_eq_prime_pow_mul hp.out hm hpa hpa1
  have : NeZero M := ⟨hM0⟩
  have : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rw [bauerPoly_map_mul_coprime hcop, bauerPoly_prime_pow p hp2 ha, ← pow_mul]
  congr 1
  -- `φ(m)/(p - 1) = p^{a-1} φ(M)`
  rw [Nat.totient_mul hcop, Nat.totient_prime_pow hp.out (by omega),
    show p ^ (a - 1) * (p - 1) * M.totient = (p - 1) * (p ^ (a - 1) * M.totient) by ring,
    Nat.mul_div_cancel_left _ (by have := hp.out.two_le; omega)]

/-! ### Theorem 127: the case `p = 2` (§ 8.6) -/

lemma bauerPoly_four_map : (bauerPoly 4).map (Int.castRingHom (ZMod 4)) = X ^ 2 - 1 := by
  have hfilt : (range 4).filter (·.Coprime 4) = {1, 3} := by decide
  have h : bauerPoly 4 = (X - C 1) * (X - C 3) := by
    rw [bauerPoly, hfilt, Finset.prod_insert (by decide), Finset.prod_singleton]
    simp
  have hd : bauerPoly 4 - (X ^ 2 - 1) = C ((4 : ℕ) : ℤ) * (-(X - 1)) := by
    rw [h, Nat.cast_ofNat, C_1, show (C (3 : ℤ) : ℤ[X]) = 3 from map_ofNat C 3,
      show (C (4 : ℤ) : ℤ[X]) = 4 from map_ofNat C 4]
    ring
  rw [(map_eq_map_iff_C_dvd 4 _ (X ^ 2 - 1)).2 ⟨_, hd⟩]
  simp

/-- **Theorem 127** [hardywright2008], (8.5.6): for `a ≥ 2`,
`f_{2^a}(x) ≡ (x² - 1)^{2^{a-2}} (mod 2^a)`. As in § 8.6: `f_{2^a}(x) = f_{2^{a-1}}(x) f_{2^{a-1}}(x - 2^{a-1})
≡ f_{2^{a-1}}(x)² - 2^{a-1} f_{2^{a-1}}(x) f'_{2^{a-1}}(x)`, and `f'_{2^{a-1}} ≡ 0 (mod 2)`. -/
@[kb "hardywright2008" "Thm 127, p. 127"]
theorem bauerPoly_two_pow {a : ℕ} (ha : 2 ≤ a) :
    (bauerPoly (2 ^ a)).map (Int.castRingHom (ZMod (2 ^ a))) = (X ^ 2 - 1) ^ (2 ^ (a - 2)) := by
  classical
  induction a, ha using Nat.le_induction with
  | base => simpa using bauerPoly_four_map
  | succ a ha ih =>
    set R := ZMod (2 ^ (a + 1))
    set φ := Int.castRingHom R
    obtain ⟨G, hG⟩ : C ((2 ^ a : ℕ) : ℤ) ∣ bauerPoly (2 ^ a) - (X ^ 2 - 1) ^ (2 ^ (a - 2)) := by
      rw [← map_eq_map_iff_C_dvd, ih]
      simp
    set T := (range (2 ^ a)).filter (·.Coprime (2 ^ a)) with hT
    set F : R[X] := (bauerPoly (2 ^ a)).map φ with hF
    set D : R[X] := ∑ t ∈ T, ∏ t' ∈ T.erase t, (X - C (t' : R)) with hD
    have hFprod : F = ∏ t ∈ T, (X - C (t : R)) := by
      rw [hF, bauerPoly, Polynomial.map_prod]; simp [hT]
    have hFD : derivative F = D := by
      rw [hFprod, derivative_prod_finset, hD]
      simp
    -- `f_{2^{a+1}}(x) = f_{2^a}(x) f_{2^a}(x - 2^a)`
    have hdec : bauerPoly (2 ^ (a + 1)) =
        ∏ v ∈ range 2, ∏ t ∈ T, (X - C (t : ℤ) + -C ((v * 2 ^ a : ℕ) : ℤ)) := by
      rw [bauerPoly, filter_coprime_prime_pow_succ Nat.prime_two (by omega), Finset.prod_image,
        Finset.prod_product, Finset.prod_comm]
      · refine Finset.prod_congr rfl fun v _ ↦ Finset.prod_congr rfl fun t _ ↦ ?_
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, C_add, C_mul]; ring
      · rintro ⟨t, v⟩ htv ⟨t', v'⟩ htv' h
        simp only [Finset.coe_product, Set.mem_prod, Finset.coe_filter, Finset.mem_range,
          Set.mem_setOf_eq, Finset.coe_range, Set.mem_Iio] at htv htv' h
        have hpa : 0 < 2 ^ a := pow_pos two_pos a
        have h1 : t = t' := by
          have := congrArg (· % 2 ^ a) h
          simpa [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt htv.1.1,
            Nat.mod_eq_of_lt htv'.1.1] using this
        subst h1
        have : v * 2 ^ a = v' * 2 ^ a := by omega
        rw [Nat.eq_of_mul_eq_mul_right hpa this]
    have hsq : (-C ((1 * 2 ^ a : ℕ) : R)) * (-C ((1 * 2 ^ a : ℕ) : R)) = 0 := by
      rw [neg_mul_neg, ← C_mul, ← Nat.cast_mul, one_mul, ← pow_add,
        C_prime_pow_eq_zero 2 (by omega)]
    have hmap : (bauerPoly (2 ^ (a + 1))).map φ = F * (F + (-C ((2 ^ a : ℕ) : R)) * D) := by
      rw [hdec, Polynomial.map_prod, Finset.prod_range_succ, Finset.prod_range_one,
        Polynomial.map_prod, Polynomial.map_prod]
      congr 1
      · rw [hFprod]
        refine Finset.prod_congr rfl fun t _ ↦ ?_
        simp
      · have : ∀ t ∈ T, (X - C (t : ℤ) + -C ((1 * 2 ^ a : ℕ) : ℤ)).map φ =
            (X - C (t : R)) + (-C ((1 * 2 ^ a : ℕ) : R)) := fun t _ ↦ by
              rw [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_neg, map_X, map_C, map_C]
              simp
        rw [Finset.prod_congr rfl this,
          prod_add_of_mul_eq_zero T _ (fun _ ↦ -C ((1 * 2 ^ a : ℕ) : R)) (fun _ _ ↦ hsq),
          ← hFprod, ← Finset.mul_sum, one_mul]
    -- `F ≡ H = (x² - 1)^{2^{a-2}} (mod 2^a)`
    set H : R[X] := ((X : R[X]) ^ 2 - 1) ^ (2 ^ (a - 2)) with hH
    set ε : R[X] := C ((2 ^ a : ℕ) : R) * G.map φ with hε
    have hFH : F = H + ε := by
      have := congrArg (Polynomial.map φ) hG
      simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, map_C, map_X,
        Polynomial.map_one] at this
      rw [hF, hH, hε]
      simp only [eq_intCast, Int.cast_natCast] at this
      linear_combination this
    have h2a : C ((2 ^ a : ℕ) : R) * C ((2 ^ a : ℕ) : R) = 0 := by
      rw [← C_mul, ← Nat.cast_mul, ← pow_add, C_prime_pow_eq_zero 2 (by omega)]
    have h2a2 : C ((2 ^ a : ℕ) : R) * 2 = 0 := by
      rw [show (2 : R[X]) = C ((2 : ℕ) : R) by rw [Nat.cast_ofNat, map_ofNat], ← C_mul, ← Nat.cast_mul, ← pow_succ,
        C_prime_pow_eq_zero 2 le_rfl]
    -- `H' = 2^{a-2} (x² - 1)^{2^{a-2} - 1} ⋅ 2x` is divisible by `2`
    set K : R[X] := C ((2 ^ (a - 2) : ℕ) : R) * ((X : R[X]) ^ 2 - 1) ^ (2 ^ (a - 2) - 1) * X
      with hK
    have hH' : derivative H = 2 * K := by
      rw [hH, hK, derivative_pow, derivative_sub, derivative_X_pow, derivative_one, sub_zero]
      simp only [C_eq_natCast, Nat.cast_ofNat, pow_one, map_ofNat]
      ring
    have hD' : D = 2 * K + C ((2 ^ a : ℕ) : R) * derivative (G.map φ) := by
      rw [← hFD, hFH, derivative_add, hε, derivative_C_mul, hH']
    rw [hmap, hFH, hD']
    have : (H ^ 2 : R[X]) = ((X : R[X]) ^ 2 - 1) ^ (2 ^ (a + 1 - 2)) := by
      rw [hH, ← pow_mul, show a + 1 - 2 = (a - 2) + 1 by omega, pow_succ 2 (a - 2)]
    rw [← this, hε]
    linear_combination (H * G.map φ - K * (H + C ((2 ^ a : ℕ) : R) * G.map φ)) * h2a2 +
      ((G.map φ) ^ 2 - derivative (G.map φ) * (H + C ((2 ^ a : ℕ) : R) * G.map φ)) * h2a

/-- **Theorem 127** [hardywright2008], (8.5.5): if `m > 2` is even and `2^a` is the highest power
of `2` dividing `m`, then `f_m(x) ≡ (x² - 1)^{φ(m)/2} (mod 2^a)`. -/
@[kb "hardywright2008" "Thm 127, p. 127"]
theorem bauerPoly_map_two_pow {m a : ℕ} (hm : 2 < m) (ha : 1 ≤ a) (hpa : 2 ^ a ∣ m)
    (hpa1 : ¬2 ^ (a + 1) ∣ m) :
    (bauerPoly m).map (Int.castRingHom (ZMod (2 ^ a))) = (X ^ 2 - 1) ^ (m.totient / 2) := by
  obtain ⟨M, rfl, hM0, hcop⟩ := exists_eq_prime_pow_mul Nat.prime_two (by omega) hpa hpa1
  have : NeZero M := ⟨hM0⟩
  have : NeZero (2 ^ a) := ⟨pow_ne_zero _ two_ne_zero⟩
  rw [bauerPoly_map_mul_coprime hcop, Nat.totient_mul hcop, Nat.totient_prime_pow Nat.prime_two
    (by omega)]
  rcases Nat.lt_or_ge a 2 with h | h
  · -- `a = 1`: `m = 2M` with `M > 1` odd; modulo `2`, `f_2(x) = x - 1` and `(x - 1)² ≡ x² - 1`
    have ha1 : a = 1 := by omega
    subst ha1
    have hM : 2 < M := by
      have hMo : ¬2 ∣ M := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 (by simpa using hcop)
      have : M ≠ 1 := by rintro rfl; simp at hm
      omega
    have hf2 : (bauerPoly (2 ^ 1)).map (Int.castRingHom (ZMod (2 ^ 1))) = X - 1 := by
      have key : ∀ n, n = 2 → (bauerPoly n).map (Int.castRingHom (ZMod n)) = X - 1 := by
        rintro n rfl
        have hfilt : (range 2).filter (·.Coprime 2) = {1} := by decide
        rw [bauerPoly, hfilt, Finset.prod_singleton]
        simp
      exact key (2 ^ 1) (pow_one 2)
    obtain ⟨k, hk⟩ := Nat.totient_even hM
    rw [hf2, hk, show 2 ^ (1 - 1) * (2 - 1) * (k + k) / 2 = k by omega,
      show k + k = 2 * k by ring, pow_mul]
    congr 1
    have h2 : (2 : (ZMod (2 ^ 1))[X]) = 0 := by
      rw [show (2 : (ZMod (2 ^ 1))[X]) = C 2 from (map_ofNat C 2).symm,
        show (2 : ZMod (2 ^ 1)) = 0 by decide, C_0]
    linear_combination (1 - X) * h2
  · rw [bauerPoly_two_pow h, ← pow_mul]
    congr 1
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
    rw [Nat.add_sub_cancel, show b + 2 - 1 = b + 1 by omega, pow_succ 2 b]
    rw [show 2 ^ b * 2 * (2 - 1) * M.totient = 2 * (2 ^ b * M.totient) by ring,
      Nat.mul_div_cancel_left _ two_pos]

end NTKB.HardyWright
