/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.IrelandRosen.R5.MinimalModel
import NTKB.IrelandRosen.R5.BadPrimesCM

/-!
# Theorems 7 and 8 of Ireland–Rosen, Chapter 18, at the remaining bad primes

The cases left open by `BadPrimesCM.lean`, where `p¹² ∣ Δ` and the given
model might not be minimal:

* `y² = x³ - Dx` at `p = 2` with `4 ∣ D`, `16 ∤ D` (`v₂(D) ∈ {2, 3}`): the model is minimal and
  the reduction additive (`noSmallerModel_quarticCurve_two`);
* `y² = x³ + D` at `p = 3` with `729 ∤ D`: minimal and additive
  (`noSmallerModel_cubicCurve_three`);
* `y² = x³ + D` at `p = 2` with `D ≡ 32` or `48 (mod 64)` (`v₂(D) = 5`, or `v₂(D) = 4` and
  `D/16 ≡ 3 (mod 4)`): minimal and additive (`noSmallerModel_cubicCurve_two`);
* `y² = x³ + D` at `p = 2` with `D ≡ 16 (mod 64)` (`v₂(D) = 4`, `D/16 ≡ 1 (mod 4)`): **good
  reduction**; `(x, y) = (4X, 8Y + 4)` gives `Y² + Y = X³ + (D - 16)/64`, of discriminant
  `-27 (D/16)²`, and the local polynomial is `1 + 2X²` (`localPolynomial_cubicCurve_two_good`).
  The book's character vanishes at `2` (it is defined modulo `12D`), so here the local factor of
  `L(E, s)` is not the Euler factor of the book's `L(s, χ)`; it is `1 - χ₀((2)) X²` with
  `χ₀((2)) = -2`, the value of the primitive character (`2` is inert in `ℤ[ω]`, of norm `4`).

Minimality is shown by hand: a change of variables `(u, r, s, t)` with `u ∈ 𝔪` keeping the model
integral gives congruences modulo `2⁴`, `2⁶` (resp. `3⁶`) for `r, s, t`, which have no solution
(`NoSmallerModel`, checked in `ZMod 16`, `ZMod 64`, `ZMod 729` by `decide`). This is the start
of Tate's algorithm (Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, IV.9).
-/

namespace NTKB.IrelandRosen.CM

open WeierstrassCurve Polynomial IsLocalRing IsDedekindDomain NumberField Rat.HeightOneSpectrum

/-! ### Congruences -/

lemma zmod16_quartic : ∀ r s t : ZMod 16, 4 * (3 * r - s ^ 2) = 0 → 4 * t = 0 →
    4 * (3 * r ^ 2 - 2 * s * t) = 0 → 3 * r ^ 2 - 2 * s * t = 0 := by
  decide

lemma zmod64_sq_of_sixteen_mul : ∀ t : ZMod 64, 16 * t = 0 → t ^ 2 = 0 ∨ t ^ 2 = 16 := by
  decide

set_option maxRecDepth 10000 in
lemma zmod64_eight_mul : ∀ s t : ZMod 64, 16 * t = 0 → 8 * s * t = 0 ∨ 8 * s * t = 32 := by
  decide

lemma zmod64_cube : ∀ r : ZMod 64, 12 * r ^ 2 = 0 ∨ 12 * r ^ 2 = 32 → r ^ 3 = 0 := by
  decide

set_option maxRecDepth 10000 in
lemma zmod729_sq : ∀ t : ZMod 729, 54 * t = 0 → t ^ 2 = 0 := by
  decide

set_option maxRecDepth 10000 in
lemma zmod729_div : ∀ t : ZMod 729, 54 * t = 0 → t = 27 * ((t.val / 27 : ℕ) : ZMod 729) := by
  decide

set_option maxRecDepth 10000 in
lemma zmod729_cube : ∀ r : ZMod 729, 27 * r ^ 2 = 0 → r ^ 3 = 0 := by
  decide

/-! ### Reduction modulo `p^k` on the completion -/

section Place

variable (v : HeightOneSpectrum (𝓞 ℚ))

/-- Reduction modulo `p^k` on the completion `ℤ_p` of `ℤ` at `v`. -/
noncomputable def placeToZMod (q k : ℕ) (hq : placePrime v = q) :
    v.adicCompletionIntegers ℚ →+* ZMod (q ^ k) :=
  ((ZMod.ringEquivCongr (by rw [hq])).toRingHom).comp
    ((PadicInt.toZModPow k).comp
      (adicCompletionIntegers.padicIntEquiv v : v.adicCompletionIntegers ℚ →+* ℤ_[placePrime v]))

lemma placeToZMod_algebraMap (q k : ℕ) (hq : placePrime v = q) (n : ℤ) :
    placeToZMod v q k hq (algebraMap ℤ _ n) = n := by
  rw [algebraMap_int_eq, eq_intCast, map_intCast]

lemma placeToZMod_natCast (q k : ℕ) (hq : placePrime v = q) :
    placeToZMod v q k hq (placePrime v : v.adicCompletionIntegers ℚ) = q := by
  rw [map_natCast, hq]

/-- An element of the maximal ideal is divisible by `p`. -/
lemma prime_dvd_of_mem_maximalIdeal {u : v.adicCompletionIntegers ℚ}
    (hu : u ∈ maximalIdeal (v.adicCompletionIntegers ℚ)) :
    (placePrime v : v.adicCompletionIntegers ℚ) ∣ u := by
  let e := adicCompletionIntegers.padicIntEquiv v
  have hea : e u ∈ maximalIdeal ℤ_[placePrime v] := by
    rw [mem_maximalIdeal, mem_nonunits_iff] at hu ⊢
    intro h
    apply hu
    have := h.map (adicCompletionIntegers.padicIntEquiv v).symm
    simpa using this
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hea
  have := map_dvd (adicCompletionIntegers.padicIntEquiv v).symm hea
  simpa [e] using this

/-- If `π^j ∣ x` and `f(π) = q`, then `q^(k - j) f(x) = 0` in `ZMod (q^k)`. -/
lemma pow_mul_eq_zero_of_dvd {A : Type*} [CommRing A] {q k : ℕ} (f : A →+* ZMod (q ^ k))
    {π : A} (hπ : f π = q) {j : ℕ} (hjk : j ≤ k) {x : A} (h : π ^ j ∣ x) :
    (q : ZMod (q ^ k)) ^ (k - j) * f x = 0 := by
  obtain ⟨y, rfl⟩ := h
  rw [map_mul, map_pow, hπ, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hjk, ← Nat.cast_pow,
    ZMod.natCast_self, zero_mul]

lemma intCast_ne_zero_of_not_dvd {n : ℕ} {D : ℤ} (h : ¬ (n : ℤ) ∣ D) : (D : ZMod n) ≠ 0 := by
  rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]

lemma intCast_eq_zero_of_dvd {n : ℕ} {D : ℤ} (h : (n : ℤ) ∣ D) : (D : ZMod n) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h

/-! ### No smaller model -/

/-- `y² = x³ - Dx` at `2` with `4 ∣ D`, `16 ∤ D`: no smaller integral model. -/
theorem noSmallerModel_quarticCurve_two (hp : placePrime v = 2) {D : ℤ} (h4 : (4 : ℤ) ∣ D)
    (h16 : ¬ (16 : ℤ) ∣ D) :
    NoSmallerModel (v.adicCompletionIntegers ℚ)
      ((quarticCurve D).map (algebraMap ℤ (v.adicCompletionIntegers ℚ))) := by
  intro u r s t hu _ _ h2 h3 h4' _
  have hπ := prime_dvd_of_mem_maximalIdeal v hu
  set f := placeToZMod v 2 4 hp
  have hf : f (placePrime v) = (2 : ℕ) := placeToZMod_natCast v 2 4 hp
  have H2 := pow_mul_eq_zero_of_dvd f hf (by norm_num : 2 ≤ 4) ((pow_dvd_pow_of_dvd hπ 2).trans h2)
  have H3 := pow_mul_eq_zero_of_dvd f hf (by norm_num : 3 ≤ 4) ((pow_dvd_pow_of_dvd hπ 3).trans h3)
  have H4 := pow_mul_eq_zero_of_dvd f hf (by norm_num : 4 ≤ 4) ((pow_dvd_pow_of_dvd hπ 4).trans h4')
  simp only [quarticCurve, map_a₁, map_a₂, map_a₃, map_a₄, map_zero, map_neg, map_sub, map_add,
    map_mul, map_pow, map_ofNat, placeToZMod_algebraMap, mul_zero, zero_mul, sub_zero, add_zero,
    zero_add, zero_sub, f] at H2 H3 H4
  set d : ZMod (2 ^ 4) := (D : ZMod (2 ^ 4)) with hd
  have hd4 : 4 * d = 0 := by
    have := intCast_eq_zero_of_dvd (n := 2 ^ 4) (D := 4 * D) (by
      push_cast; exact mul_dvd_mul_left 4 h4)
    push_cast at this; exact this
  have hd0 : d ≠ 0 := intCast_ne_zero_of_not_dvd (n := 2 ^ 4) (by push_cast; exact h16)
  set R' := placeToZMod v 2 4 hp r
  set S' := placeToZMod v 2 4 hp s
  set T' := placeToZMod v 2 4 hp t
  have k2 : 4 * (3 * R' - S' ^ 2) = 0 := by linear_combination H2
  have k3 : 4 * T' = 0 := by linear_combination H3
  have k4 : 3 * R' ^ 2 - 2 * S' * T' = d := by linear_combination H4
  have k5 : 4 * (3 * R' ^ 2 - 2 * S' * T') = 0 := by rw [k4]; exact hd4
  exact hd0 (k4.symm.trans (zmod16_quartic R' S' T' k2 k3 k5))

/-- `y² = x³ + D` at `3` with `729 ∤ D`: no smaller integral model. -/
theorem noSmallerModel_cubicCurve_three (hp : placePrime v = 3) {D : ℤ}
    (h729 : ¬ (729 : ℤ) ∣ D) :
    NoSmallerModel (v.adicCompletionIntegers ℚ)
      ((cubicCurve D).map (algebraMap ℤ (v.adicCompletionIntegers ℚ))) := by
  intro u r s t hu _ h1 _ h3 h4' h6
  have hπ := prime_dvd_of_mem_maximalIdeal v hu
  set f := placeToZMod v 3 6 hp
  have hf : f (placePrime v) = (3 : ℕ) := placeToZMod_natCast v 3 6 hp
  have h1' : u ^ 1 ∣ ((cubicCurve D).map (algebraMap ℤ (v.adicCompletionIntegers ℚ))).a₁ + 2 * s := by rw [pow_one]; exact h1
  have H1 := pow_mul_eq_zero_of_dvd f hf (by norm_num : 1 ≤ 6) ((pow_dvd_pow_of_dvd hπ 1).trans h1')
  have H3 := pow_mul_eq_zero_of_dvd f hf (by norm_num : 3 ≤ 6) ((pow_dvd_pow_of_dvd hπ 3).trans h3)
  have H4 := pow_mul_eq_zero_of_dvd f hf (by norm_num : 4 ≤ 6) ((pow_dvd_pow_of_dvd hπ 4).trans h4')
  have H6 := pow_mul_eq_zero_of_dvd f hf (by norm_num : 6 ≤ 6) ((pow_dvd_pow_of_dvd hπ 6).trans h6)
  simp only [cubicCurve, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, map_zero, map_neg, map_sub,
    map_add, map_mul, map_pow, map_ofNat, placeToZMod_algebraMap, mul_zero, zero_mul, sub_zero,
    add_zero, zero_add, zero_sub, f] at H1 H3 H4 H6
  have hd0 : (D : ZMod (3 ^ 6)) ≠ 0 := intCast_ne_zero_of_not_dvd (n := 3 ^ 6) (by
    push_cast; exact h729)
  set R' := placeToZMod v 3 6 hp r
  set S' := placeToZMod v 3 6 hp s
  set T' := placeToZMod v 3 6 hp t
  have k1 : 486 * S' = 0 := by linear_combination H1
  have k3 : 54 * T' = 0 := by linear_combination H3
  have hT := zmod729_div T' k3
  have k4 : 27 * R' ^ 2 = 0 := by
    have : 18 * S' * T' = 0 := by
      rw [hT]; linear_combination ((T'.val / 27 : ℕ) : ZMod 729) * k1
    linear_combination H4 + this
  have k6 : (D : ZMod (3 ^ 6)) = 0 := by
    have hr := zmod729_cube R' k4
    have ht := zmod729_sq T' k3
    linear_combination H6 - hr + ht
  exact hd0 k6

/-- `y² = x³ + D` at `2` with `D ≡ 32` or `48 (mod 64)`: no smaller integral model. -/
theorem noSmallerModel_cubicCurve_two (hp : placePrime v = 2) {D : ℤ}
    (hD : D % 64 = 32 ∨ D % 64 = 48) :
    NoSmallerModel (v.adicCompletionIntegers ℚ)
      ((cubicCurve D).map (algebraMap ℤ (v.adicCompletionIntegers ℚ))) := by
  intro u r s t hu _ _ _ h3 h4' h6
  have hπ := prime_dvd_of_mem_maximalIdeal v hu
  set f := placeToZMod v 2 6 hp
  have hf : f (placePrime v) = (2 : ℕ) := placeToZMod_natCast v 2 6 hp
  have H3 := pow_mul_eq_zero_of_dvd f hf (by norm_num : 3 ≤ 6) ((pow_dvd_pow_of_dvd hπ 3).trans h3)
  have H4 := pow_mul_eq_zero_of_dvd f hf (by norm_num : 4 ≤ 6) ((pow_dvd_pow_of_dvd hπ 4).trans h4')
  have H6 := pow_mul_eq_zero_of_dvd f hf (by norm_num : 6 ≤ 6) ((pow_dvd_pow_of_dvd hπ 6).trans h6)
  simp only [cubicCurve, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, map_zero, map_neg, map_sub,
    map_add, map_mul, map_pow, map_ofNat, placeToZMod_algebraMap, mul_zero, zero_mul, sub_zero,
    add_zero, zero_add, zero_sub, f] at H3 H4 H6
  have hd : (D : ZMod (2 ^ 6)) = 32 ∨ (D : ZMod (2 ^ 6)) = 48 := by
    rw [← ZMod.intCast_mod D (2 ^ 6)]
    push_cast
    rcases hD with h | h <;> rw [h] <;> [left; right] <;> rfl
  set R' := placeToZMod v 2 6 hp r
  set S' := placeToZMod v 2 6 hp s
  set T' := placeToZMod v 2 6 hp t
  have k3 : 16 * T' = 0 := by linear_combination H3
  have k4 : 12 * R' ^ 2 = 8 * S' * T' := by linear_combination H4
  have hr : R' ^ 3 = 0 := zmod64_cube R' (k4 ▸ zmod64_eight_mul S' T' k3)
  have k6 : (D : ZMod (2 ^ 6)) = T' ^ 2 := by linear_combination H6 - hr
  rcases zmod64_sq_of_sixteen_mul T' k3 with ht | ht <;> rcases hd with hd | hd <;>
    rw [k6, ht] at hd <;> exact absurd hd (by decide)

/-! ### Local polynomial `1` at a place of `ℚ` -/

/-- Integers are nonzero in the completion (stated without a `CharZero` instance, which would
bring a second `Algebra ℚ` structure on the completion). -/
lemma intCast_adicCompletion_ne_zero {n : ℤ} (h : n ≠ 0) : (n : v.adicCompletion ℚ) ≠ 0 := by
  have : (algebraMap ℚ (v.adicCompletion ℚ)) (n : ℚ) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap ℚ (v.adicCompletion ℚ)).injective]; exact_mod_cast h
  simpa using this

lemma two_adicCompletion_ne_zero : (2 : v.adicCompletion ℚ) ≠ 0 := by
  simpa using intCast_adicCompletion_ne_zero v (n := 2) (by norm_num)

lemma algebraMap_int_ne_zero {n : ℤ} (h : n ≠ 0) :
    algebraMap ℤ (v.adicCompletionIntegers ℚ) n ≠ 0 := by
  intro h'
  have := congrArg (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)) h'
  rw [map_zero, ← RingHom.comp_apply, eq_intCast] at this
  exact intCast_adicCompletion_ne_zero v h this

lemma baseChange_eq_map_map (W : WeierstrassCurve ℤ) :
    (W.baseChange ℚ).baseChange (v.adicCompletion ℚ) =
      (W.map (algebraMap ℤ (v.adicCompletionIntegers ℚ))).map
        (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)) := by
  rw [baseChange, baseChange, WeierstrassCurve.map_map, WeierstrassCurve.map_map]
  exact congrArg W.map (Subsingleton.elim _ _)

lemma baseChange_rat_eq_map (W : WeierstrassCurve ℤ) :
    (W.baseChange ℚ).baseChange (v.adicCompletion ℚ) =
      W.map (algebraMap ℤ (v.adicCompletion ℚ)) := by
  rw [baseChange, baseChange, WeierstrassCurve.map_map]
  exact congrArg W.map (Subsingleton.elim _ _)

/-- A curve with integer coefficients, `p ∣ Δ ≠ 0`, `p ∣ c₄` and no smaller model at `p`: the local
polynomial is `1`. -/
theorem localPolynomial_rat_eq_one_of_noSmallerModel (W : WeierstrassCurve ℤ) (hΔ0 : W.Δ ≠ 0)
    (hΔ : (placePrime v : ℤ) ∣ W.Δ) (hc : (placePrime v : ℤ) ∣ W.c₄)
    (hns : NoSmallerModel (v.adicCompletionIntegers ℚ)
      (W.map (algebraMap ℤ (v.adicCompletionIntegers ℚ)))) :
    ((W.baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ) = 1 := by
  rw [baseChange_eq_map_map]
  refine localPolynomial_eq_one_of_noSmallerModel _ _ ?_ ?_ ?_ hns
  · rw [map_Δ]; exact algebraMap_int_ne_zero v hΔ0
  · rw [map_Δ]; exact (algebraMap_mem_maximalIdeal_iff v _).2 hΔ
  · rw [map_c₄]; exact (algebraMap_mem_maximalIdeal_iff v _).2 hc

/-- **`y² = x³ - Dx` at `2` with `4 ∣ D`, `16 ∤ D`**: the local polynomial is `1`. -/
theorem localPolynomial_quarticCurve_eq_one_of_two_of_four_dvd (hp : placePrime v = 2) {D : ℤ}
    (h4 : (4 : ℤ) ∣ D) (h16 : ¬ (16 : ℤ) ∣ D) :
    (((quarticCurve D).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ) = 1 := by
  have hD : D ≠ 0 := by rintro rfl; exact h16 (dvd_zero _)
  refine localPolynomial_rat_eq_one_of_noSmallerModel v _ ?_ ?_ ?_
    (noSmallerModel_quarticCurve_two v hp h4 h16)
  · rw [quarticCurve_Δ]; exact mul_ne_zero (by norm_num) (pow_ne_zero _ hD)
  · rw [quarticCurve_Δ, hp]; exact ⟨32 * D ^ 3, by push_cast; ring⟩
  · rw [quarticCurve_c₄, hp]; exact ⟨24 * D, by push_cast; ring⟩

/-- **`y² = x³ + D` at `3` with `729 ∤ D`**: the local polynomial is `1`. -/
theorem localPolynomial_cubicCurve_eq_one_of_three (hp : placePrime v = 3) {D : ℤ}
    (h729 : ¬ (729 : ℤ) ∣ D) :
    (((cubicCurve D).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ) = 1 := by
  have hD : D ≠ 0 := by rintro rfl; exact h729 (dvd_zero _)
  refine localPolynomial_rat_eq_one_of_noSmallerModel v _ ?_ ?_ ?_
    (noSmallerModel_cubicCurve_three v hp h729)
  · rw [cubicCurve_Δ]; exact mul_ne_zero (by norm_num) (pow_ne_zero _ hD)
  · rw [cubicCurve_Δ, hp]; exact ⟨-144 * D ^ 2, by push_cast; ring⟩
  · rw [cubicCurve_c₄]; exact dvd_zero _

/-- **`y² = x³ + D` at `2` with `D ≡ 32` or `48 (mod 64)`**: the local polynomial is `1`. -/
theorem localPolynomial_cubicCurve_eq_one_of_two_of_mod (hp : placePrime v = 2) {D : ℤ}
    (hD : D % 64 = 32 ∨ D % 64 = 48) :
    (((cubicCurve D).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ) = 1 := by
  have hD0 : D ≠ 0 := by rintro rfl; omega
  refine localPolynomial_rat_eq_one_of_noSmallerModel v _ ?_ ?_ ?_
    (noSmallerModel_cubicCurve_two v hp hD)
  · rw [cubicCurve_Δ]; exact mul_ne_zero (by norm_num) (pow_ne_zero _ hD0)
  · rw [cubicCurve_Δ, hp]; exact ⟨-216 * D ^ 2, by push_cast; ring⟩
  · rw [cubicCurve_c₄]; exact dvd_zero _

/-! ### `y² = x³ + D` at `2` for `D ≡ 16 (mod 64)`: good reduction -/

/-- `Y² + Y = X³ + m`. -/
def cubicTwoModel (m : ℤ) : WeierstrassCurve ℤ := ⟨0, 0, 1, 0, m⟩

lemma cubicTwoModel_Δ (m : ℤ) : (cubicTwoModel m).Δ = -27 * (4 * m + 1) ^ 2 := by
  simp only [cubicTwoModel, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

lemma card_affineSolutions_cubicTwoModel (m : ℤ) :
    Nat.card (AffineSolutions ((cubicTwoModel m).map (Int.castRingHom (ZMod 2)))) = 2 := by
  have e : AffineSolutions ((cubicTwoModel m).map (Int.castRingHom (ZMod 2))) ≃
      {xy : ZMod 2 × ZMod 2 // xy.2 ^ 2 + xy.2 = xy.1 ^ 3 + (m : ZMod 2)} :=
    Equiv.subtypeEquivRight fun xy => by
      rw [WeierstrassCurve.Affine.equation_iff]
      simp only [cubicTwoModel, WeierstrassCurve.map, map_zero, map_one, eq_intCast, zero_mul,
        add_zero, mul_zero, one_mul]
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  generalize (m : ZMod 2) = c
  revert c
  decide

/-- The change of variables `(x, y) = (4X, 8Y + 4)` from `y² = x³ + D`, `D = 64m + 16`, to
`Y² + Y = X³ + m`. -/
lemma variableChange_cubicCurve_two {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) (φ : ℤ →+* K)
    (m : ℤ) : (⟨Units.mk0 (2 : K) h2, 0, 0, 4⟩ : VariableChange K) •
        (cubicCurve (64 * m + 16)).map φ = (cubicTwoModel m).map φ := by
  ext
  · simp [variableChange_a₁, cubicCurve, cubicTwoModel]
  · simp [variableChange_a₂, cubicCurve, cubicTwoModel]
  · simp [variableChange_a₃, cubicCurve, cubicTwoModel]; field_simp; norm_num
  · simp [variableChange_a₄, cubicCurve, cubicTwoModel]
  · simp [variableChange_a₆, cubicCurve, cubicTwoModel, eq_intCast]; field_simp; ring

/-- **`y² = x³ + D` at `2` for `D ≡ 16 (mod 64)`** (`v₂(D) = 4`, `D/16 ≡ 1 (mod 4)`): good
reduction, and the local polynomial is `1 + 2X²`. -/
theorem localPolynomial_cubicCurve_two_good (hp : placePrime v = 2) {D : ℤ} (hD : D % 64 = 16) :
    (((cubicCurve D).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ) = 1 + C 2 * X ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, D = 64 * m + 16 := ⟨D / 64, by omega⟩
  have hD0 : (64 * m + 16 : ℤ) ≠ 0 := by omega
  have hΔ' : ¬ (placePrime v : ℤ) ∣ (cubicTwoModel m).Δ := by
    rw [cubicTwoModel_Δ, hp]
    rintro ⟨k, hk⟩
    have h' : (2 : ℤ) * (k + 216 * m ^ 2 + 108 * m + 14) = 1 := by
      push_cast at hk; linear_combination -hk
    generalize k + 216 * m ^ 2 + 108 * m + 14 = z at h'
    omega
  have hL := localPolynomial_rat v _ hΔ'
  rw [baseChange_rat_eq_map] at hL ⊢
  have hΔ : ((cubicCurve (64 * m + 16)).map (algebraMap ℤ (v.adicCompletion ℚ))).Δ ≠ 0 := by
    rw [map_Δ, eq_intCast]
    refine intCast_adicCompletion_ne_zero v ?_
    rw [cubicCurve_Δ]; exact mul_ne_zero (by norm_num) (pow_ne_zero _ hD0)
  have hj : ((cubicCurve (64 * m + 16)).map (algebraMap ℤ (v.adicCompletion ℚ))).c₄ ^ 3 =
      algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) 0 *
        ((cubicCurve (64 * m + 16)).map (algebraMap ℤ (v.adicCompletion ℚ))).Δ := by
    rw [map_c₄, cubicCurve_c₄]; simp
  rw [← localPolynomial_smul _ _ hΔ 0 hj ⟨Units.mk0 (2 : v.adicCompletion ℚ) (two_adicCompletion_ne_zero v), 0, 0, 4⟩,
    variableChange_cubicCurve_two, hL]
  have key : ∀ (q : ℕ) [Fact q.Prime], q = 2 → 1 - C ((q : ℤ) -
      Nat.card (AffineSolutions ((cubicTwoModel m).map (Int.castRingHom (ZMod q))))) * X +
        C (q : ℤ) * X ^ 2 = (1 + C 2 * X ^ 2 : ℤ[X]) := by
    rintro q _ rfl
    rw [card_affineSolutions_cubicTwoModel]
    norm_num
  exact key _ hp

/-! ### `D` not power free: the isomorphic curve -/

/-- `y² = x³ - c⁴Dx` and `y² = x³ - Dx` have the same local polynomials (`(x, y) = (c²X, c³Y)`). -/
theorem localPolynomial_quarticCurve_pow_four_mul {c D : ℤ} (hc : c ≠ 0) (hD : D ≠ 0) :
    (((quarticCurve (c ^ 4 * D)).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ) =
      (((quarticCurve D).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ) := by
  set K := v.adicCompletion ℚ
  have hcK : (c : K) ≠ 0 := intCast_adicCompletion_ne_zero v hc
  set W := (quarticCurve (c ^ 4 * D)).map (algebraMap ℤ K)
  have hΔ : W.Δ ≠ 0 := by
    rw [map_Δ, eq_intCast]
    refine intCast_adicCompletion_ne_zero v ?_
    rw [quarticCurve_Δ]
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hc) hD))
  have hj : W.c₄ ^ 3 = algebraMap (v.adicCompletionIntegers ℚ) K 1728 * W.Δ := by
    rw [map_c₄, map_Δ, quarticCurve_c₄, quarticCurve_Δ]; simp [map_ofNat]; ring
  have hC : (⟨Units.mk0 (c : K) hcK, 0, 0, 0⟩ : VariableChange K) • W =
      (quarticCurve D).map (algebraMap ℤ K) := by
    ext
    · simp [W, variableChange_a₁, quarticCurve]
    · simp [W, variableChange_a₂, quarticCurve]
    · simp [W, variableChange_a₃, quarticCurve]
    · simp [W, variableChange_a₄, quarticCurve]; field_simp
    · simp [W, variableChange_a₆, quarticCurve]
  rw [baseChange_rat_eq_map, baseChange_rat_eq_map, ← hC, localPolynomial_smul _ W hΔ 1728 hj]

/-- `y² = x³ + c⁶D` and `y² = x³ + D` have the same local polynomials (`(x, y) = (c²X, c³Y)`). -/
theorem localPolynomial_cubicCurve_pow_six_mul {c D : ℤ} (hc : c ≠ 0) (hD : D ≠ 0) :
    (((cubicCurve (c ^ 6 * D)).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ) =
      (((cubicCurve D).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ) := by
  set K := v.adicCompletion ℚ
  have hcK : (c : K) ≠ 0 := intCast_adicCompletion_ne_zero v hc
  set W := (cubicCurve (c ^ 6 * D)).map (algebraMap ℤ K)
  have hΔ : W.Δ ≠ 0 := by
    rw [map_Δ, eq_intCast]
    refine intCast_adicCompletion_ne_zero v ?_
    rw [cubicCurve_Δ]
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hc) hD))
  have hj : W.c₄ ^ 3 = algebraMap (v.adicCompletionIntegers ℚ) K 0 * W.Δ := by
    rw [map_c₄, cubicCurve_c₄]; simp
  have hC : (⟨Units.mk0 (c : K) hcK, 0, 0, 0⟩ : VariableChange K) • W =
      (cubicCurve D).map (algebraMap ℤ K) := by
    ext
    · simp [W, variableChange_a₁, cubicCurve]
    · simp [W, variableChange_a₂, cubicCurve]
    · simp [W, variableChange_a₃, cubicCurve]
    · simp [W, variableChange_a₄, cubicCurve]
    · simp [W, variableChange_a₆, cubicCurve]; field_simp
  rw [baseChange_rat_eq_map, baseChange_rat_eq_map, ← hC, localPolynomial_smul _ W hΔ 0 hj]

end Place

end NTKB.IrelandRosen.CM
