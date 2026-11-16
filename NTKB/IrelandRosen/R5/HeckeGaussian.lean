/-
Ireland–Rosen, Chapter 18, §5, Theorem 7: the Hecke character of `ℚ(i)` attached to
`y² = x³ - Dx`, and the local factors of `L(E, s)`.
-/
import NTKB.IrelandRosen.R5.LocalPolynomial
import NTKB.IrelandRosen.R4.QuarticCurve
import NTKB.IrelandRosen.R3.Reciprocity

/-!
# The Hecke character of `y² = x³ - Dx` (Ireland–Rosen, Chapter 18, Theorem 7)

Every ideal of `ℤ[i]` prime to `2` has exactly one primary generator `α` (`α ≡ 1 (mod (1 + i)³)`,
`primaryAssoc`). For `D ≠ 0` and `α` prime to `2D`, Ireland–Rosen put
`χ((α)) = conj((D/α)₄) α`, with `(D/α)₄` the generalized quartic residue symbol of §9.8
(`quarticSymbol α D`). We define `heckeCharQuartic D α` (zero when `α` is not prime to `2D`) and prove:

* it is a function of the ideal `(α)` (`heckeCharQuartic_of_associated`) and completely
  multiplicative (`heckeCharQuartic_mul`);
* `N(χ(A)) = N(A)`, i.e. `|χ(A)| = N(A)^{1/2}`: weight one (`norm_heckeCharQuartic`,
  Proposition 18.5.1 for this character);
* `χ((α)) = α` for `α ≡ 1 (mod 4D)`, `D` odd (`heckeCharQuartic_of_modEq_one`);
* **Theorem 7, local form**: at every prime `p ∤ 2D`, Mathlib's local polynomial of `E` at `p`
  (`WeierstrassCurve.localPolynomial`, the factor of `WeierstrassCurve.LFunction`) is the Euler
  factor of `L(s, χ)` at the primes above `p`: `(1 - χ(π) X)(1 - χ(π̄) X)` if `p = π π̄` splits,
  `1 - χ((p)) X²` if `p` is inert (`X = p^{-s}`).
-/

namespace NTKB.IrelandRosen.CM

open Polynomial NTKB.IrelandRosen.Gaussian Zsqrtd

local notation "ℤ[i]" => GaussianInt

/-! ### Primary generators -/

open Classical in
/-- The primary associate of a Gaussian integer prime to `1 + i` (the element itself otherwise). -/
noncomputable def primaryAssoc (α : ℤ[i]) : ℤ[i] :=
  if h : onePlusI ∣ α then α else (exists_isPrimary'_unit_mul h).choose * α

lemma primaryAssoc_spec {α : ℤ[i]} (h : ¬ onePlusI ∣ α) :
    ∃ u : ℤ[i], IsUnit u ∧ primaryAssoc α = u * α ∧ IsPrimary' (primaryAssoc α) := by
  have hs := (exists_isPrimary'_unit_mul h).choose_spec
  refine ⟨_, hs.1, by rw [primaryAssoc, dif_neg h], ?_⟩
  rw [primaryAssoc, dif_neg h]
  exact hs.2

lemma isPrimary'_primaryAssoc {α : ℤ[i]} (h : ¬ onePlusI ∣ α) : IsPrimary' (primaryAssoc α) :=
  (primaryAssoc_spec h).choose_spec.2.2

lemma associated_primaryAssoc (α : ℤ[i]) : Associated α (primaryAssoc α) := by
  by_cases h : onePlusI ∣ α
  · rw [primaryAssoc, dif_pos h]
  · obtain ⟨u, hu, he, -⟩ := primaryAssoc_spec h
    rw [he, mul_comm]
    exact ⟨hu.unit, rfl⟩

/-- A primary associate is unique. -/
lemma primaryAssoc_eq_of_associated {α β : ℤ[i]} (hβ : IsPrimary' β) (h : Associated α β) :
    primaryAssoc α = β := by
  have h2 : ¬ onePlusI ∣ α := fun hd => hβ.not_onePlusI_dvd (h.dvd_iff_dvd_right.1 hd)
  obtain ⟨u, hu, he, hp⟩ := primaryAssoc_spec h2
  obtain ⟨w, rfl⟩ := h
  have hp' : IsPrimary' ((w : ℤ[i]) * α) := by rwa [mul_comm]
  rw [he] at hp ⊢
  rw [unit_eq_of_isPrimary' hu w.isUnit hp hp', mul_comm]

lemma primaryAssoc_of_isPrimary' {α : ℤ[i]} (h : IsPrimary' α) : primaryAssoc α = α :=
  primaryAssoc_eq_of_associated h (Associated.refl α)

lemma primaryAssoc_of_associated {α β : ℤ[i]} (h : Associated α β) (h2 : ¬ onePlusI ∣ β) :
    primaryAssoc α = primaryAssoc β :=
  primaryAssoc_eq_of_associated (isPrimary'_primaryAssoc h2)
    (h.trans (associated_primaryAssoc β))

lemma primaryAssoc_mul {α β : ℤ[i]} (hα : ¬ onePlusI ∣ α) (hβ : ¬ onePlusI ∣ β) :
    primaryAssoc (α * β) = primaryAssoc α * primaryAssoc β :=
  primaryAssoc_eq_of_associated ((isPrimary'_primaryAssoc hα).mul (isPrimary'_primaryAssoc hβ))
    ((associated_primaryAssoc α).mul_mul (associated_primaryAssoc β))

/-! ### The character -/

lemma isCoprime_iff_of_associated_left {α β m : ℤ[i]} (h : Associated α β) :
    IsCoprime α m ↔ IsCoprime β m := by
  obtain ⟨u, rfl⟩ := h
  exact (isCoprime_mul_unit_right_left u.isUnit α m).symm

lemma onePlusI_dvd_two : onePlusI ∣ (2 : ℤ[i]) := ⟨1 - I, by ext <;> simp⟩

lemma not_onePlusI_dvd_of_isCoprime {α : ℤ[i]} {D : ℤ} (h : IsCoprime α (2 * D : ℤ[i])) :
    ¬ onePlusI ∣ α := fun hd =>
  irreducible_onePlusI.not_isUnit
    (h.isUnit_of_dvd' hd (dvd_mul_of_dvd_left onePlusI_dvd_two _))

lemma ne_zero_of_isCoprime {α : ℤ[i]} {D : ℤ} (h : IsCoprime α (2 * D : ℤ[i])) : α ≠ 0 := by
  rintro rfl
  exact not_onePlusI_dvd_of_isCoprime h (dvd_zero _)

open Classical in
/-- **The Hecke character of `y² = x³ - Dx`** (Ireland–Rosen, Chapter 18, §5, Theorem 7):
`χ((α)) = conj((D/α)₄) α` for `α` prime to `2D`, `α` replaced by its primary associate; `0` on
the elements not prime to `2D`. -/
@[kb "irelandrosen1990" "Ch. 18, §5, Theorem 7, p. 322"]
noncomputable def heckeCharQuartic (D : ℤ) (α : ℤ[i]) : ℤ[i] :=
  if IsCoprime α (2 * D : ℤ[i]) then star (quarticSymbol α D) * primaryAssoc α else 0

lemma heckeCharQuartic_of_isCoprime {D : ℤ} {α : ℤ[i]} (h : IsCoprime α (2 * D : ℤ[i])) :
    heckeCharQuartic D α = star (quarticSymbol α D) * primaryAssoc α := by
  rw [heckeCharQuartic, if_pos h]

lemma heckeCharQuartic_of_not_isCoprime {D : ℤ} {α : ℤ[i]} (h : ¬ IsCoprime α (2 * D : ℤ[i])) :
    heckeCharQuartic D α = 0 := by
  rw [heckeCharQuartic, if_neg h]

/-- `χ` is a function of the ideal `(α)`. -/
theorem heckeCharQuartic_of_associated (D : ℤ) {α β : ℤ[i]} (h : Associated α β) :
    heckeCharQuartic D α = heckeCharQuartic D β := by
  by_cases hc : IsCoprime α (2 * D : ℤ[i])
  · have hc' : IsCoprime β (2 * D : ℤ[i]) :=
      (isCoprime_iff_of_associated_left h).1 hc
    rw [heckeCharQuartic_of_isCoprime hc, heckeCharQuartic_of_isCoprime hc',
      quarticSymbol_of_associated h, primaryAssoc_of_associated h (not_onePlusI_dvd_of_isCoprime hc')]
  · have hc' : ¬ IsCoprime β (2 * D : ℤ[i]) := fun h' =>
      hc ((isCoprime_iff_of_associated_left h).2 h')
    rw [heckeCharQuartic_of_not_isCoprime hc, heckeCharQuartic_of_not_isCoprime hc']

/-- `χ` is completely multiplicative. -/
theorem heckeCharQuartic_mul (D : ℤ) (α β : ℤ[i]) :
    heckeCharQuartic D (α * β) = heckeCharQuartic D α * heckeCharQuartic D β := by
  by_cases hα : IsCoprime α (2 * D : ℤ[i])
  · by_cases hβ : IsCoprime β (2 * D : ℤ[i])
    · rw [heckeCharQuartic_of_isCoprime hα, heckeCharQuartic_of_isCoprime hβ,
        heckeCharQuartic_of_isCoprime (hα.mul_left hβ),
        quarticSymbol_mul_left (ne_zero_of_isCoprime hα) (ne_zero_of_isCoprime hβ),
        primaryAssoc_mul (not_onePlusI_dvd_of_isCoprime hα) (not_onePlusI_dvd_of_isCoprime hβ),
        star_mul']
      ring
    · rw [heckeCharQuartic_of_not_isCoprime hβ, mul_zero,
        heckeCharQuartic_of_not_isCoprime fun h => hβ (IsCoprime.of_mul_left_right h)]
  · rw [heckeCharQuartic_of_not_isCoprime hα, zero_mul,
      heckeCharQuartic_of_not_isCoprime fun h => hα (IsCoprime.of_mul_left_left h)]

lemma isCoprime_intCast_of_isCoprime {α : ℤ[i]} {D : ℤ} (h : IsCoprime α (2 * D : ℤ[i])) :
    IsCoprime α (D : ℤ[i]) :=
  h.of_mul_right_right

/-- **Weight one** (Proposition 18.5.1 for this character): `N(χ(A)) = N(A)`, i.e.
`|χ(A)| = N(A)^{1/2}`, for `A` prime to `2D`. -/
@[kb "irelandrosen1990" "Prop 18.5.1, p. 319"]
theorem norm_heckeCharQuartic {D : ℤ} {α : ℤ[i]} (h : IsCoprime α (2 * D : ℤ[i])) :
    (heckeCharQuartic D α).norm = α.norm := by
  have h2 := not_onePlusI_dvd_of_isCoprime h
  have hu := isUnit_quarticSymbol h2 (isCoprime_intCast_of_isCoprime h)
  rw [heckeCharQuartic_of_isCoprime h, norm_mul, norm_conj, (isUnit_iff_norm_eq_one).1 hu, one_mul]
  obtain ⟨w, hw⟩ := associated_primaryAssoc α
  rw [← hw, norm_mul, (isUnit_iff_norm_eq_one).1 w.isUnit, mul_one]

/-- `|χ(A)| = N(A)^{1/2}` in `ℂ`. -/
@[kb "irelandrosen1990" "Prop 18.5.1, p. 319"]
theorem norm_toComplex_heckeCharQuartic {D : ℤ} {α : ℤ[i]} (h : IsCoprime α (2 * D : ℤ[i])) :
    ‖GaussianInt.toComplex (heckeCharQuartic D α)‖ = Real.sqrt (α.norm : ℝ) := by
  rw [← norm_heckeCharQuartic h, GaussianInt.intCast_real_norm, Complex.normSq_eq_norm_sq,
    Real.sqrt_sq (norm_nonneg _)]

/-! ### The congruence condition -/

lemma isCoprime_of_dvd_sub_one {α m : ℤ[i]} (h : m ∣ α - 1) : IsCoprime α m := by
  obtain ⟨k, hk⟩ := h
  exact ⟨1, -k, by linear_combination hk⟩

/-- `χ((α)) = α` for `α ≡ 1 (mod 4D)`, `D` odd: `χ` is a Hecke character of modulus `4D` with
infinity type the identity. -/
@[kb "irelandrosen1990" "Ch. 18, §5, Theorem 7, p. 322"]
theorem heckeCharQuartic_of_modEq_one {D : ℤ} (hD : Odd D) {α : ℤ[i]}
    (hα : (4 * D : ℤ[i]) ∣ α - 1) : heckeCharQuartic D α = α := by
  have hc : IsCoprime α (2 * D : ℤ[i]) :=
    isCoprime_of_dvd_sub_one ((mul_dvd_mul_right (⟨2, by norm_num⟩ : (2 : ℤ[i]) ∣ 4) _).trans hα)
  have h4 : (4 : ℤ[i]) ∣ α - 1 := (dvd_mul_right _ _).trans hα
  have hP : IsPrimary' α := by
    refine dvd_trans ⟨-(1 + I), ?_⟩ h4
    ext <;> simp [onePlusI, pow_succ] <;> norm_num
  have hre : α.re % 4 = 1 := by
    obtain ⟨k, hk⟩ := h4
    have := congrArg Zsqrtd.re hk
    simp at this
    omega
  rw [heckeCharQuartic_of_isCoprime hc, primaryAssoc_of_isPrimary' hP]
  suffices quarticSymbol α D = 1 by rw [this, star_one, one_mul]
  have h2 := hP.not_onePlusI_dvd
  -- `D = ± D'` with `D' ≡ 1 (mod 4)`
  have hDodd : D % 2 = 1 := Int.odd_iff.1 hD
  have hD' : normOdd D % 4 = 1 := normOdd_mod hDodd
  have hneg : quarticSymbol α (-1) = 1 := by
    rw [hP.quarticSymbol_neg_one]
    have : (α.re - 1) / 2 = 2 * ((α.re - 1) / 4) := by omega
    rw [this, Int.negOnePow_two_mul]; rfl
  have hmain : quarticSymbol α (normOdd D) = 1 := by
    have hdvd : (normOdd D : ℤ[i]) ∣ α - 1 := by
      refine dvd_trans ?_ ((dvd_mul_left _ _).trans hα)
      unfold normOdd
      split_ifs
      · exact dvd_rfl
      · exact ⟨-1, by push_cast; ring⟩
    have hcop : IsCoprime (normOdd D : ℤ[i]) α := (isCoprime_of_dvd_sub_one hdvd).symm
    rw [← quarticSymbol_intCast_comm hD' hP hcop, quarticSymbol_congr hdvd,
      quarticSymbol_one_right (odd_intCast_not_onePlusI_dvd (Int.odd_iff.2 (by omega)))]
  unfold normOdd at hmain
  split_ifs at hmain with h
  · exact hmain
  · have : (D : ℤ[i]) = (-1) * ((-D : ℤ) : ℤ[i]) := by push_cast; ring
    rw [this, quarticSymbol_mul_right h2, hneg, one_mul, hmain]

/-! ### Values at primes -/

lemma isCoprime_of_prime_norm {π : ℤ[i]} {p : ℕ} (hp : p.Prime) (hπp : π.norm = p) {D : ℤ}
    (hD : ¬ (p : ℤ) ∣ 2 * D) : IsCoprime π (2 * D : ℤ[i]) := by
  have hirr : Irreducible π := irreducible_of_prime_norm (by rw [hπp]; simpa using hp)
  refine (hirr.coprime_iff_not_dvd).2 fun hd => hD ?_
  have h := norm_dvd_norm hd
  rw [hπp, Int.natAbs_natCast, show (2 * D : ℤ[i]) = ((2 * D : ℤ) : ℤ[i]) by push_cast; ring,
    Zsqrtd.norm_intCast] at h
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have h' : (p : ℤ) ∣ (2 * D) * (2 * D) := Int.natCast_dvd.2 h
  rcases hp'.dvd_or_dvd h' with h1 | h1 <;> exact h1

lemma prime_ne_two_of_not_dvd {p : ℕ} {D : ℤ} (hD : ¬ (p : ℤ) ∣ 2 * D) : p ≠ 2 := by
  rintro rfl; exact hD (dvd_mul_right _ _)

lemma not_dvd_of_not_dvd_two_mul {p : ℕ} {D : ℤ} (hD : ¬ (p : ℤ) ∣ 2 * D) : ¬ (p : ℤ) ∣ D :=
  fun h => hD (dvd_mul_of_dvd_right h _)

/-- `χ(π) = conj((D/π)₄) π` for a primary prime `π` of norm `p ∤ 2D`. -/
theorem heckeCharQuartic_of_isPrimary {p : ℕ} (hp : p.Prime) {π : ℤ[i]} (hπ : IsPrimary π)
    (hπp : π.norm = p) {D : ℤ} (hD : ¬ (p : ℤ) ∣ 2 * D) :
    heckeCharQuartic D π = star (quarticChar π D) * π := by
  have hirr : Irreducible π := irreducible_of_prime_norm (by rw [hπp]; simpa using hp)
  rw [heckeCharQuartic_of_isCoprime (isCoprime_of_prime_norm hp hπp hD),
    quarticSymbol_of_irreducible hirr, primaryAssoc_of_isPrimary' hπ.2]

/-- `χ(π̄) = (D/π)₄ π̄`. -/
theorem heckeCharQuartic_star_of_isPrimary {p : ℕ} (hp : p.Prime) {π : ℤ[i]} (hπ : IsPrimary π)
    (hπp : π.norm = p) {D : ℤ} (hD : ¬ (p : ℤ) ∣ 2 * D) :
    heckeCharQuartic D (star π) = quarticChar π D * star π := by
  have hirr : Irreducible π := irreducible_of_prime_norm (by rw [hπp]; simpa using hp)
  have h2 : π.norm.natAbs ≠ 2 := by
    rw [hπp, Int.natAbs_natCast]; exact prime_ne_two_of_not_dvd hD
  have hn : (star π).norm = p := by rw [norm_conj, hπp]
  rw [heckeCharQuartic_of_isCoprime (isCoprime_of_prime_norm hp hn hD),
    quarticSymbol_of_irreducible (irreducible_star hirr), primaryAssoc_of_isPrimary' hπ.2.star,
    ← star_intCast D, quarticChar_star hirr h2, star_star, star_intCast]

/-- `χ((p)) = -p` for an inert prime `p ≡ 3 (mod 4)`, `p ∤ D`. -/
theorem heckeCharQuartic_natCast {p : ℕ} (hp : p.Prime) (hp3 : p % 4 = 3) {D : ℤ}
    (hD : ¬ (p : ℤ) ∣ 2 * D) : heckeCharQuartic D (p : ℤ[i]) = -(p : ℤ[i]) := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hc2 : IsCoprime (p : ℤ) (2 * D) := (hpZ.irreducible.coprime_iff_not_dvd).2 hD
  have hc : IsCoprime (p : ℤ[i]) (2 * D : ℤ[i]) := by
    have := intCast_isCoprime_iff.2 hc2
    push_cast at this
    exact this
  have hodd : Odd (p : ℤ) := by
    rw [Int.odd_iff]; omega
  have hsym : quarticSymbol (p : ℤ[i]) D = 1 := by
    have := quarticSymbol_intCast_intCast hodd
      ((hpZ.irreducible.coprime_iff_not_dvd).2 (not_dvd_of_not_dvd_two_mul hD))
    push_cast at this
    exact this
  have hP : IsPrimary' (-(p : ℤ[i])) := by
    rw [isPrimary'_iff]; simp; omega
  rw [heckeCharQuartic_of_isCoprime hc, hsym, star_one, one_mul,
    primaryAssoc_eq_of_associated hP (Associated.refl _).neg_right]

/-! ### Theorem 7: the local factors -/

/-- The curve `y² = x³ - Dx` over `ℤ`. -/
def quarticCurve (D : ℤ) : WeierstrassCurve ℤ := ⟨0, 0, 0, -D, 0⟩

lemma quarticCurve_Δ (D : ℤ) : (quarticCurve D).Δ = 64 * D ^ 3 := by
  simp only [quarticCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

lemma card_affineSolutions_quarticCurve (p : ℕ) [Fact p.Prime] (D : ℤ) :
    Nat.card (AffineSolutions ((quarticCurve D).map (Int.castRingHom (ZMod p)))) + 1 =
      numPointsQuarticCurve p D := by
  have e : AffineSolutions ((quarticCurve D).map (Int.castRingHom (ZMod p))) ≃
      {xy : ZMod p × ZMod p // xy.2 ^ 2 = xy.1 ^ 3 - D * xy.1} :=
    Equiv.subtypeEquivRight fun xy => by
      rw [WeierstrassCurve.Affine.equation_iff]
      simp only [quarticCurve, WeierstrassCurve.map, map_zero, map_neg, eq_intCast, zero_mul,
        add_zero, mul_zero]
      constructor <;> intro h <;> linear_combination h
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype, numPointsQuarticCurve,
    add_comm]

lemma not_dvd_quarticCurve_Δ {p : ℕ} (hp : p.Prime) {D : ℤ} (hD : ¬ (p : ℤ) ∣ 2 * D) :
    ¬ (p : ℤ) ∣ (quarticCurve D).Δ := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  rw [quarticCurve_Δ, show (64 : ℤ) * D ^ 3 = 2 ^ 6 * D ^ 3 by norm_num]
  intro h
  rcases hpZ.dvd_or_dvd h with h | h
  · exact hD (dvd_mul_of_dvd_left (hpZ.dvd_of_dvd_pow h) _)
  · exact not_dvd_of_not_dvd_two_mul hD (hpZ.dvd_of_dvd_pow h)

open IsDedekindDomain NumberField in
/-- Mathlib's local polynomial of `y² = x³ - Dx` at the place `v` above `p ∤ 2D` is
`1 - a_p X + p X²`, `a_p = p + 1 - N_p`. -/
theorem localPolynomial_quarticCurve (v : HeightOneSpectrum (𝓞 ℚ)) {D : ℤ}
    (hD : ¬ (placePrime v : ℤ) ∣ 2 * D) :
    (((quarticCurve D).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ) =
      1 - C ((placePrime v : ℤ) + 1 - numPointsQuarticCurve (placePrime v) D) * X +
        C (placePrime v : ℤ) * X ^ 2 := by
  rw [localPolynomial_rat v _ (not_dvd_quarticCurve_Δ (Fact.out) hD),
    ← card_affineSolutions_quarticCurve]
  push_cast
  ring_nf

open IsDedekindDomain NumberField in
/-- **Theorem 7 of Chapter 18, split primes.** For `p = π π̄ ∤ 2D`, `π` primary, the local
polynomial of `y² = x³ - Dx` at `p` is the Euler factor of `L(s, χ)` at `π` and `π̄`:
`(1 - χ(π) X)(1 - χ(π̄) X)`. -/
@[kb "irelandrosen1990" "Ch. 18, §5, Theorem 7, p. 322"]
theorem localPolynomial_quarticCurve_split (v : HeightOneSpectrum (𝓞 ℚ)) {D : ℤ}
    (hD : ¬ (placePrime v : ℤ) ∣ 2 * D) {π : ℤ[i]} (hπ : IsPrimary π)
    (hπp : π.norm = placePrime v) :
    ((((quarticCurve D).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ)).map (Int.castRingHom ℤ[i]) =
      (1 - C (heckeCharQuartic D π) * X) * (1 - C (heckeCharQuartic D (star π)) * X) := by
  set p := placePrime v
  have hp : p.Prime := Fact.out
  have hirr : Irreducible π := irreducible_of_prime_norm (by rw [hπp]; simpa using hp)
  have h2 : π.norm.natAbs ≠ 2 := by
    rw [hπp, Int.natAbs_natCast]; exact prime_ne_two_of_not_dvd hD
  have hp1 : p % 4 = 1 := by
    have := natAbs_norm_mod_four_eq_one hirr h2
    rwa [hπp, Int.natAbs_natCast] at this
  have hD' := not_dvd_of_not_dvd_two_mul hD
  have H := numPointsQuarticCurve_eq hp1 hπ hπp hD'
  rw [heckeCharQuartic_of_isPrimary hp hπ hπp hD, heckeCharQuartic_star_of_isPrimary hp hπ hπp hD,
    localPolynomial_quarticCurve v hD]
  set c := quarticChar π D with hc
  have hcu : IsUnit c := by
    have := isUnit_quarticSymbol hπ.2.not_onePlusI_dvd
      (isCoprime_intCast_of_isCoprime (isCoprime_of_prime_norm hp hπp hD))
    rwa [quarticSymbol_of_irreducible hirr] at this
  set N := numPointsQuarticCurve p D
  have hsum : star c * π + c * star π = (p : ℤ[i]) + 1 - ((N : ℤ) : ℤ[i]) := by
    rw [H]; ring
  have hprod : (star c * π) * (c * star π) = p := by
    have hcc : c * star c = 1 := unit_mul_star hcu
    have hn : π * star π = p := by
      rw [← Zsqrtd.norm_eq_mul_conj, hπp]; push_cast; rfl
    linear_combination (π * star π) * hcc + hn
  have hR : (1 - C (star c * π) * X) * (1 - C (c * star π) * X) =
      1 - C (star c * π + c * star π) * X + C ((star c * π) * (c * star π)) * X ^ 2 := by
    simp only [map_add, map_mul]; ring
  rw [hR, hsum, hprod]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_one,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_pow, Int.coe_castRingHom]
  push_cast
  ring

open IsDedekindDomain NumberField in
/-- **Theorem 7 of Chapter 18, inert primes.** For `p ≡ 3 (mod 4)`, `p ∤ D`, the local
polynomial of `y² = x³ - Dx` at `p` is `1 + p X² = 1 - χ((p)) X²`, the Euler factor of
`L(s, χ)` at the prime `(p)` of norm `p²` (`X = p^{-s}`). -/
@[kb "irelandrosen1990" "Ch. 18, §5, Theorem 7, p. 322"]
theorem localPolynomial_quarticCurve_inert (v : HeightOneSpectrum (𝓞 ℚ)) {D : ℤ}
    (hD : ¬ (placePrime v : ℤ) ∣ 2 * D) (hp3 : placePrime v % 4 = 3) :
    ((((quarticCurve D).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ)).map (Int.castRingHom ℤ[i]) =
      1 - C (heckeCharQuartic D (placePrime v : ℤ[i])) * X ^ 2 := by
  have hp : (placePrime v).Prime := Fact.out
  rw [localPolynomial_quarticCurve v hD,
    numPointsQuarticCurve_of_mod_four_eq_three hp3 (not_dvd_of_not_dvd_two_mul hD),
    heckeCharQuartic_natCast hp hp3 hD]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_one,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_pow, Int.coe_castRingHom]
  push_cast
  simp only [add_sub_cancel_right, sub_self, map_zero, zero_mul, sub_zero, map_neg]
  ring

open IsDedekindDomain NumberField in
/-- **Theorem 7 of Chapter 18, inert primes, over `ℤ`**: `1 + p X²`. -/
theorem localPolynomial_quarticCurve_of_mod_four_eq_three (v : HeightOneSpectrum (𝓞 ℚ)) {D : ℤ}
    (hD : ¬ (placePrime v : ℤ) ∣ 2 * D) (hp3 : placePrime v % 4 = 3) :
    (((quarticCurve D).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ) = 1 + C (placePrime v : ℤ) * X ^ 2 := by
  rw [localPolynomial_quarticCurve v hD,
    numPointsQuarticCurve_of_mod_four_eq_three hp3 (not_dvd_of_not_dvd_two_mul hD)]
  push_cast
  simp

end NTKB.IrelandRosen.CM
