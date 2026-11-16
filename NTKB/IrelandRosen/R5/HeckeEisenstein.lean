/-
Ireland–Rosen, Chapter 18, §5, Theorem 8: the Hecke character of `ℚ(ω)` attached to
`y² = x³ + D`, and the local factors of `L(E, s)`.
-/
import NTKB.IrelandRosen.R5.LocalPolynomial
import NTKB.IrelandRosen.R4.CubicCurve

/-!
# The Hecke character of `y² = x³ + D` (Ireland–Rosen, Chapter 18, Theorem 8)

Every prime `ρ` of `ℤ[ω]` of norm `≠ 3` has exactly one primary associate `ρ'` (`ρ' ≡ 2 (mod 3)`,
Proposition 9.3.5). For `ρ ∤ 6D` put `χ(ρ) = -conj((4D/ρ')₆) ρ'` when `N ρ = p` is prime, and
`χ(ρ) = -ρ'` when `ρ` is a rational prime `q ≡ 2 (mod 3)` (norm `q²`); `χ` is extended
multiplicatively to the elements prime to `6D` (a function of the ideal) and is `0` on the others
(`heckeCharSextic`). With `-ρ' ≡ 1 (mod 3)` this is the book's `χ(π) = conj((4D/π)₆) π`.

* `χ` is a function of the ideal and completely multiplicative; `N(χ(A)) = N(A)` (weight one);
* **Theorem 8, local form**: at every prime `p ∤ 6D`, Mathlib's local polynomial of `E` at `p`
  is the Euler factor of `L(s, χ)` at the primes above `p`: `(1 - χ(π) X)(1 - χ(π̄) X)` if
  `p = π π̄`, and `1 - χ((p)) X²` if `p ≡ 2 (mod 3)`.
-/

namespace NTKB.IrelandRosen.CM

open Polynomial NTKB.HardyWright QuadraticAlgebra NTKB.IrelandRosen.Eisenstein

local notation "ℤ[ω]" => NTKB.HardyWright.ZRho

/-! ### Primary associates and the character -/

open Classical in
/-- The primary associate (`≡ 2 (mod 3)`) of a prime of norm `≠ 3`; the element itself otherwise. -/
noncomputable def primaryAssocω (ρ : ℤ[ω]) : ℤ[ω] :=
  if h : Prime ρ ∧ (norm ρ).natAbs ≠ 3 then
    ((existsUnique_isPrimary_unit_mul h.1 h.2).exists.choose : ℤ[ω]) * ρ
  else ρ

open Classical in
/-- The value of the character at a prime `ρ`: `-conj((4D/ρ')₆) ρ'` if `N ρ` is a rational prime,
`-ρ'` otherwise (`ρ'` the primary associate). -/
noncomputable def heckeCharSexticPrime (D : ℤ) (ρ : ℤ[ω]) : ℤ[ω] :=
  if (norm ρ).natAbs.Prime then -(star (sexticChar (primaryAssocω ρ) (4 * D)) * primaryAssocω ρ)
  else -primaryAssocω ρ

open Classical in
/-- **The Hecke character of `y² = x³ + D`** (Ireland–Rosen, Chapter 18, §5, Theorem 8), on the
elements prime to `6D`, multiplicative over the prime factorization; `0` on the others. -/
@[kb "irelandrosen1990" "Ch. 18, §5, Theorem 8, p. 324"]
noncomputable def heckeCharSextic (D : ℤ) (α : ℤ[ω]) : ℤ[ω] :=
  if IsCoprime α (6 * D : ℤ[ω]) then
    ((UniqueFactorizationMonoid.factors α).map (heckeCharSexticPrime D)).prod
  else 0

lemma isPrimary_primaryAssocω {ρ : ℤ[ω]} (hρ : Prime ρ) (h3 : (norm ρ).natAbs ≠ 3) :
    IsPrimary (primaryAssocω ρ) := by
  rw [primaryAssocω, dif_pos ⟨hρ, h3⟩]
  exact (existsUnique_isPrimary_unit_mul hρ h3).exists.choose_spec

lemma associated_primaryAssocω {ρ : ℤ[ω]} (hρ : Prime ρ) (h3 : (norm ρ).natAbs ≠ 3) :
    Associated ρ (primaryAssocω ρ) := by
  rw [primaryAssocω, dif_pos ⟨hρ, h3⟩]
  exact ⟨_, mul_comm _ _⟩

lemma primaryAssocω_eq_of_associated {ρ σ : ℤ[ω]} (hρ : Prime ρ) (h3 : (norm ρ).natAbs ≠ 3)
    (hσ : IsPrimary σ) (h : Associated ρ σ) : primaryAssocω ρ = σ := by
  obtain ⟨w, rfl⟩ := h
  have hu := existsUnique_isPrimary_unit_mul hρ h3
  have e : primaryAssocω ρ = ((hu.exists.choose : ℤ[ω]ˣ) : ℤ[ω]) * ρ := by
    rw [primaryAssocω, dif_pos ⟨hρ, h3⟩]
  have : hu.exists.choose = w :=
    hu.unique hu.exists.choose_spec (by rw [mul_comm]; exact hσ)
  rw [e, this, mul_comm]

lemma norm_eq_of_associatedω {x y : ℤ[ω]} (h : Associated x y) : norm x = norm y := by
  have h1 := qa_natAbs_norm_eq_of_associated h
  have h2 := rho_norm_nonneg x
  have h3 := rho_norm_nonneg y
  omega

lemma heckeCharSexticPrime_of_associated (D : ℤ) {x y : ℤ[ω]} (hx : Prime x)
    (h3 : (norm x).natAbs ≠ 3) (h : Associated x y) :
    heckeCharSexticPrime D x = heckeCharSexticPrime D y := by
  have hy : Prime y := h.prime_iff.1 hx
  have h3y : (norm y).natAbs ≠ 3 := by rwa [← qa_natAbs_norm_eq_of_associated h]
  have e : primaryAssocω x = primaryAssocω y :=
    primaryAssocω_eq_of_associated hx h3 (isPrimary_primaryAssocω hy h3y)
      (h.trans (associated_primaryAssocω hy h3y))
  unfold heckeCharSexticPrime
  rw [e, qa_natAbs_norm_eq_of_associated h]

lemma factor_prop {D : ℤ} {α ρ : ℤ[ω]} (h : IsCoprime α (6 * D : ℤ[ω]))
    (hρ : ρ ∈ UniqueFactorizationMonoid.factors α) :
    Prime ρ ∧ (norm ρ).natAbs ≠ 3 ∧ ¬ ρ ∣ (D : ℤ[ω]) := by
  have hp : Prime ρ := UniqueFactorizationMonoid.irreducible_iff_prime.1
    (UniqueFactorizationMonoid.irreducible_of_factor ρ hρ)
  have hdα : ρ ∣ α := UniqueFactorizationMonoid.dvd_of_mem_factors hρ
  refine ⟨hp, ?_, ?_⟩
  · rw [natAbs_norm_ne_three_iff hp]
    intro hd
    exact hp.not_isUnit (h.isUnit_of_dvd' hdα
      (by rw [show (6 * D : ℤ[ω]) = 3 * (2 * D) by ring]; exact hd.mul_right _))
  · intro hd
    exact hp.not_isUnit (h.isUnit_of_dvd' hdα (dvd_mul_of_dvd_right hd _))

lemma prod_map_heckeCharSexticPrime_eq {D : ℤ} {s t : Multiset ℤ[ω]}
    (h : Multiset.Rel Associated s t) (hs : ∀ x ∈ s, Prime x ∧ (norm x).natAbs ≠ 3) :
    (s.map (heckeCharSexticPrime D)).prod = (t.map (heckeCharSexticPrime D)).prod := by
  have : Multiset.Rel (· = ·) (s.map (heckeCharSexticPrime D)) (t.map (heckeCharSexticPrime D)) :=
    Multiset.rel_map.2 (h.mono fun x hx y _ hxy =>
      heckeCharSexticPrime_of_associated D (hs x hx).1 (hs x hx).2 hxy)
  rw [Multiset.rel_eq] at this
  rw [this]

lemma isCoprime_iff_of_associated_left' {α β m : ℤ[ω]} (h : Associated α β) :
    IsCoprime α m ↔ IsCoprime β m := by
  obtain ⟨u, rfl⟩ := h
  exact (isCoprime_mul_unit_right_left u.isUnit α m).symm

lemma ne_zero_of_isCoprime' {α : ℤ[ω]} {D : ℤ} (h : IsCoprime α (6 * D : ℤ[ω])) : α ≠ 0 := by
  rintro rfl
  have h3 := three_eq_and_prime_one_sub_omega
  have hd : (1 - omega : ℤ[ω]) ∣ 3 := ⟨-omega ^ 2 * (1 - omega), by linear_combination h3.1⟩
  exact h3.2.not_isUnit (h.isUnit_of_dvd' (dvd_zero _)
    (by rw [show (6 * D : ℤ[ω]) = 3 * (2 * D) by ring]; exact hd.mul_right _))

/-- `χ` is a function of the ideal `(α)`. -/
theorem heckeCharSextic_of_associated (D : ℤ) {α β : ℤ[ω]} (h : Associated α β) :
    heckeCharSextic D α = heckeCharSextic D β := by
  by_cases hc : IsCoprime α (6 * D : ℤ[ω])
  · have hc' : IsCoprime β (6 * D : ℤ[ω]) := (isCoprime_iff_of_associated_left' h).1 hc
    unfold heckeCharSextic
    rw [if_pos hc, if_pos hc']
    exact prod_map_heckeCharSexticPrime_eq (UniqueFactorizationMonoid.factors_rel_of_associated h)
      fun x hx => ⟨(factor_prop hc hx).1, (factor_prop hc hx).2.1⟩
  · have hc' : ¬ IsCoprime β (6 * D : ℤ[ω]) := fun h' =>
      hc ((isCoprime_iff_of_associated_left' h).2 h')
    unfold heckeCharSextic
    rw [if_neg hc, if_neg hc']

/-- `χ` is completely multiplicative. -/
theorem heckeCharSextic_mul (D : ℤ) (α β : ℤ[ω]) :
    heckeCharSextic D (α * β) = heckeCharSextic D α * heckeCharSextic D β := by
  by_cases hα : IsCoprime α (6 * D : ℤ[ω])
  · by_cases hβ : IsCoprime β (6 * D : ℤ[ω])
    · have hαβ := hα.mul_left hβ
      unfold heckeCharSextic
      rw [if_pos hα, if_pos hβ, if_pos hαβ,
        prod_map_heckeCharSexticPrime_eq
          (UniqueFactorizationMonoid.factors_mul (ne_zero_of_isCoprime' hα)
            (ne_zero_of_isCoprime' hβ))
          (fun x hx => ⟨(factor_prop hαβ hx).1, (factor_prop hαβ hx).2.1⟩),
        Multiset.map_add, Multiset.prod_add]
    · have : ¬ IsCoprime (α * β) (6 * D : ℤ[ω]) := fun h => hβ (IsCoprime.of_mul_left_right h)
      unfold heckeCharSextic
      rw [if_neg hβ, if_neg this, mul_zero]
  · have : ¬ IsCoprime (α * β) (6 * D : ℤ[ω]) := fun h => hα (IsCoprime.of_mul_left_left h)
    unfold heckeCharSextic
    rw [if_neg hα, if_neg this, zero_mul]

lemma norm_neg' (x : ℤ[ω]) : norm (-x) = norm x := by
  rw [rho_norm, rho_norm]; simp

lemma norm_heckeCharSexticPrime {D : ℤ} {ρ : ℤ[ω]} (hρ : Prime ρ) (h3 : (norm ρ).natAbs ≠ 3)
    (hD : ¬ ρ ∣ (D : ℤ[ω])) : norm (heckeCharSexticPrime D ρ) = norm ρ := by
  have hpa := isPrimary_primaryAssocω hρ h3
  have hn' : norm (primaryAssocω ρ) = norm ρ :=
    (norm_eq_of_associatedω (associated_primaryAssocω hρ h3)).symm
  unfold heckeCharSexticPrime
  split_ifs with hpr
  · have hpr' : (norm (primaryAssocω ρ)).natAbs.Prime := by rwa [hn']
    haveI : Fact (norm (primaryAssocω ρ)).natAbs.Prime := ⟨hpr'⟩
    have h3' : (norm (primaryAssocω ρ)).natAbs ≠ 3 := by rwa [hn']
    have hD' : (D : ZMod (norm (primaryAssocω ρ)).natAbs) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      intro hdv
      apply hD
      have h1 := qa_dvd_natAbs_norm ρ
      rw [← hn'] at h1
      exact h1.trans (by exact_mod_cast map_dvd (Int.castRingHom ℤ[ω]) hdv)
    have hu := Eisenstein.sexticChar_mul_star h3' hD'
    set c := sexticChar (primaryAssocω ρ) (4 * D)
    have hc : norm c = 1 := by
      have := congrArg QuadraticAlgebra.norm hu
      rw [map_mul, QuadraticAlgebra.norm_star, map_one] at this
      have h0 := rho_norm_nonneg c
      nlinarith
    rw [norm_neg', map_mul, QuadraticAlgebra.norm_star, hc, hn', one_mul]
  · rw [norm_neg', hn']

/-- **Weight one** (Proposition 18.5.1 for this character): `N(χ(A)) = N(A)` for `A` prime
to `6D`. -/
@[kb "irelandrosen1990" "Prop 18.5.1, p. 319"]
theorem norm_heckeCharSextic {D : ℤ} {α : ℤ[ω]} (h : IsCoprime α (6 * D : ℤ[ω])) :
    norm (heckeCharSextic D α) = norm α := by
  have h0 := ne_zero_of_isCoprime' h
  have hprod := UniqueFactorizationMonoid.factors_prod h0
  rw [heckeCharSextic, if_pos h, map_multiset_prod, Multiset.map_map,
    ← norm_eq_of_associatedω hprod, map_multiset_prod]
  congr 1
  refine Multiset.map_congr rfl fun ρ hρ => ?_
  have := factor_prop h hρ
  exact norm_heckeCharSexticPrime this.1 this.2.1 this.2.2

/-! ### Values at primes -/

lemma heckeCharSextic_of_prime {D : ℤ} {π : ℤ[ω]} (hπ : Prime π) (h3 : (norm π).natAbs ≠ 3)
    (hc : IsCoprime π (6 * D : ℤ[ω])) : heckeCharSextic D π = heckeCharSexticPrime D π := by
  unfold heckeCharSextic
  rw [if_pos hc]
  have hrel : Multiset.Rel Associated (UniqueFactorizationMonoid.factors π) {π} :=
    UniqueFactorizationMonoid.factors_unique UniqueFactorizationMonoid.irreducible_of_factor
      (by simpa using hπ.irreducible)
      ((UniqueFactorizationMonoid.factors_prod hπ.ne_zero).trans (by rw [Multiset.prod_singleton]; exact Associated.refl _))
  rw [prod_map_heckeCharSexticPrime_eq hrel
    (fun x hx => ⟨(factor_prop hc hx).1, (factor_prop hc hx).2.1⟩)]
  simp

lemma prime_facts_of_norm_eq {p : ℕ} (hp : p.Prime) {π : ℤ[ω]} (hπp : norm π = p) {D : ℤ}
    (hD : ¬ (p : ℤ) ∣ 6 * D) :
    Prime π ∧ (norm π).natAbs ≠ 3 ∧ IsCoprime π (6 * D : ℤ[ω]) := by
  have hN : (norm π).natAbs = p := by rw [hπp, Int.natAbs_natCast]
  have hπ : Prime π := prime_of_natAbs_norm_prime (by rw [hN]; exact hp)
  have h3 : (norm π).natAbs ≠ 3 := by
    rw [hN]; rintro rfl
    exact hD (dvd_mul_of_dvd_left (by norm_num) _)
  refine ⟨hπ, h3, (hπ.irreducible.coprime_iff_not_dvd).2 fun hd => hD ?_⟩
  have h := natAbs_norm_dvd hd
  rw [hN, show (6 * D : ℤ[ω]) = ((6 * D : ℤ) : ℤ[ω]) by push_cast; ring,
    QuadraticAlgebra.norm_intCast] at h
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have h' : (p : ℤ) ∣ (6 * D) ^ 2 := by
    have := Int.natCast_dvd.2 h
    simpa [Int.natAbs_pow] using this
  exact hp'.dvd_of_dvd_pow h'

lemma sexticChar_star' {π : ℤ[ω]} (hπ : Prime π) (h3 : (norm π).natAbs ≠ 3) (a : ℤ) :
    sexticChar (star π) a = star (sexticChar π a) := by
  have h := cubicChar_star hπ h3 (a : ℤ[ω])
  rw [star_intCast] at h
  unfold sexticChar
  rw [star_mul', star_pow, star_intCast, ← h, natAbs_norm_star]

/-- `χ(π) = -conj((4D/π)₆) π` for a primary prime `π` of norm `p ∤ 6D`. -/
theorem heckeCharSextic_of_isPrimary {p : ℕ} (hp : p.Prime) {π : ℤ[ω]} (hπ : IsPrimary π)
    (hπp : norm π = p) {D : ℤ} (hD : ¬ (p : ℤ) ∣ 6 * D) :
    heckeCharSextic D π = -(star (sexticChar π (4 * D)) * π) := by
  obtain ⟨h1, h2, h3⟩ := prime_facts_of_norm_eq hp hπp hD
  have hN : (norm π).natAbs = p := by rw [hπp, Int.natAbs_natCast]
  rw [heckeCharSextic_of_prime h1 h2 h3, heckeCharSexticPrime,
    primaryAssocω_eq_of_associated h1 h2 hπ (Associated.refl _), if_pos (by rw [hN]; exact hp)]

/-- `χ(π̄) = -(4D/π)₆ π̄`. -/
theorem heckeCharSextic_star_of_isPrimary {p : ℕ} (hp : p.Prime) {π : ℤ[ω]} (hπ : IsPrimary π)
    (hπp : norm π = p) {D : ℤ} (hD : ¬ (p : ℤ) ∣ 6 * D) :
    heckeCharSextic D (star π) = -(sexticChar π (4 * D) * star π) := by
  have hn : norm (star π) = p := by rw [QuadraticAlgebra.norm_star, hπp]
  obtain ⟨h1, h2, h3⟩ := prime_facts_of_norm_eq hp hπp hD
  obtain ⟨h1', h2', h3'⟩ := prime_facts_of_norm_eq hp hn hD
  have hN : (norm (star π)).natAbs = p := by rw [hn, Int.natAbs_natCast]
  rw [heckeCharSextic_of_prime h1' h2' h3', heckeCharSexticPrime,
    primaryAssocω_eq_of_associated h1' h2' hπ.star (Associated.refl _),
    if_pos (by rw [hN]; exact hp), sexticChar_star' h1 h2, star_star]

/-- `χ((p)) = -p` for an inert prime `p ≡ 2 (mod 3)`, `p ∤ 6D`. -/
theorem heckeCharSextic_natCast {p : ℕ} (hp : p.Prime) (hp2 : p % 3 = 2) {D : ℤ}
    (hD : ¬ (p : ℤ) ∣ 6 * D) : heckeCharSextic D (p : ℤ[ω]) = -(p : ℤ[ω]) := by
  have h1 : Prime (p : ℤ[ω]) := prime_natCast_of_mod_three_eq_two hp hp2
  have h2 : (norm (p : ℤ[ω])).natAbs ≠ 3 := natAbs_norm_natCast_ne_three hp
  have h3 : IsCoprime (p : ℤ[ω]) (6 * D : ℤ[ω]) := by
    refine (h1.irreducible.coprime_iff_not_dvd).2 ?_
    rintro ⟨x, hx⟩
    have := congrArg QuadraticAlgebra.re hx
    simp at this
    exact hD ⟨x.re, this⟩
  have hP : IsPrimary (p : ℤ[ω]) := by
    rw [isPrimary_iff]; simp; omega
  have hnp : ¬ (norm (p : ℤ[ω])).natAbs.Prime := by
    rw [natAbs_norm_natCast]
    exact Nat.Prime.not_prime_pow (by norm_num)
  rw [heckeCharSextic_of_prime h1 h2 h3, heckeCharSexticPrime,
    primaryAssocω_eq_of_associated h1 h2 hP (Associated.refl _), if_neg hnp]

/-! ### Theorem 8: the local factors -/

/-- The curve `y² = x³ + D` over `ℤ`. -/
def cubicCurve (D : ℤ) : WeierstrassCurve ℤ := ⟨0, 0, 0, 0, D⟩

lemma cubicCurve_Δ (D : ℤ) : (cubicCurve D).Δ = -432 * D ^ 2 := by
  simp only [cubicCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

lemma card_affineSolutions_cubicCurve (p : ℕ) [Fact p.Prime] (D : ℤ) :
    Nat.card (AffineSolutions ((cubicCurve D).map (Int.castRingHom (ZMod p)))) + 1 =
      numPointsCubicCurve p D := by
  have e : AffineSolutions ((cubicCurve D).map (Int.castRingHom (ZMod p))) ≃
      {xy : ZMod p × ZMod p // xy.2 ^ 2 = xy.1 ^ 3 + D} :=
    Equiv.subtypeEquivRight fun xy => by
      rw [WeierstrassCurve.Affine.equation_iff]
      simp only [cubicCurve, WeierstrassCurve.map, map_zero, eq_intCast, zero_mul,
        add_zero]
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype, numPointsCubicCurve,
    add_comm]

lemma not_dvd_cubicCurve_Δ {p : ℕ} (hp : p.Prime) {D : ℤ} (hD : ¬ (p : ℤ) ∣ 6 * D) :
    ¬ (p : ℤ) ∣ (cubicCurve D).Δ := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  rw [cubicCurve_Δ, show (-432 : ℤ) * D ^ 2 = -(2 * 2 * 2 * 2 * 3 * 3 * 3 * D * D) by ring]
  intro h
  simp only [dvd_neg, hpZ.dvd_mul] at h
  have h2 : (p : ℤ) ∣ 2 → (p : ℤ) ∣ 6 * D := fun h => dvd_mul_of_dvd_left (h.trans ⟨3, by norm_num⟩) D
  have h3 : (p : ℤ) ∣ 3 → (p : ℤ) ∣ 6 * D := fun h => dvd_mul_of_dvd_left (h.trans ⟨2, by norm_num⟩) D
  have h4 : (p : ℤ) ∣ D → (p : ℤ) ∣ 6 * D := fun h => dvd_mul_of_dvd_right h _
  tauto

open IsDedekindDomain NumberField in
/-- Mathlib's local polynomial of `y² = x³ + D` at the place `v` above `p ∤ 6D` is
`1 - a_p X + p X²`, `a_p = p + 1 - N_p`. -/
theorem localPolynomial_cubicCurve (v : HeightOneSpectrum (𝓞 ℚ)) {D : ℤ}
    (hD : ¬ (placePrime v : ℤ) ∣ 6 * D) :
    (((cubicCurve D).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ) =
      1 - C ((placePrime v : ℤ) + 1 - numPointsCubicCurve (placePrime v) D) * X +
        C (placePrime v : ℤ) * X ^ 2 := by
  rw [localPolynomial_rat v _ (not_dvd_cubicCurve_Δ (Fact.out) hD),
    ← card_affineSolutions_cubicCurve]
  push_cast
  ring_nf

open IsDedekindDomain NumberField in
/-- **Theorem 8 of Chapter 18, split primes.** For `p = π π̄ ∤ 6D`, `π` primary, the local
polynomial of `y² = x³ + D` at `p` is `(1 - χ(π) X)(1 - χ(π̄) X)`. -/
@[kb "irelandrosen1990" "Ch. 18, §5, Theorem 8, p. 324"]
theorem localPolynomial_cubicCurve_split (v : HeightOneSpectrum (𝓞 ℚ)) {D : ℤ}
    (hD : ¬ (placePrime v : ℤ) ∣ 6 * D) {π : ℤ[ω]} (hπ : IsPrimary π)
    (hπp : norm π = placePrime v) :
    ((((cubicCurve D).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ)).map (Int.castRingHom ℤ[ω]) =
      (1 - C (heckeCharSextic D π) * X) * (1 - C (heckeCharSextic D (star π)) * X) := by
  set p := placePrime v
  have hp : p.Prime := Fact.out
  obtain ⟨hirr, h3, -⟩ := prime_facts_of_norm_eq hp hπp hD
  have hp1 : p % 3 = 1 := by
    have := natAbs_norm_mod_three hirr h3
    rwa [hπp, Int.natAbs_natCast] at this
  have hD' : ¬ (p : ℤ) ∣ D := fun h => hD (dvd_mul_of_dvd_right h _)
  have H := numPointsCubicCurve_eq hp1 hπ hπp hD'
  rw [heckeCharSextic_of_isPrimary hp hπ hπp hD, heckeCharSextic_star_of_isPrimary hp hπ hπp hD,
    localPolynomial_cubicCurve v hD]
  set c := sexticChar π (4 * D) with hc
  have hN : (norm π).natAbs = p := by rw [hπp, Int.natAbs_natCast]
  have hcu : c * star c = 1 := by
    haveI : Fact (norm π).natAbs.Prime := ⟨by rw [hN]; exact hp⟩
    refine Eisenstein.sexticChar_mul_star h3 ?_
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd, hN]
    exact hD'
  set N := numPointsCubicCurve p D
  have hsum : -(star c * π) + -(c * star π) = (p : ℤ[ω]) + 1 - ((N : ℤ) : ℤ[ω]) := by
    rw [H]; ring
  have hprod : (-(star c * π)) * (-(c * star π)) = p := by
    have hn : π * star π = p := by
      rw [mul_star, hπp]; simp
    linear_combination (π * star π) * hcu + hn
  have hR : (1 - C (-(star c * π)) * X) * (1 - C (-(c * star π)) * X) =
      1 - C (-(star c * π) + -(c * star π)) * X +
        C ((-(star c * π)) * (-(c * star π))) * X ^ 2 := by
    simp only [map_add, map_mul]; ring
  rw [hR, hsum, hprod]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_one,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_pow, Int.coe_castRingHom]
  push_cast
  ring

open IsDedekindDomain NumberField in
/-- **Theorem 8 of Chapter 18, inert primes.** For `p ≡ 2 (mod 3)`, `p ∤ 6D`, the local
polynomial is `1 - χ((p)) X² = 1 + p X²`. -/
@[kb "irelandrosen1990" "Ch. 18, §5, Theorem 8, p. 324"]
theorem localPolynomial_cubicCurve_inert (v : HeightOneSpectrum (𝓞 ℚ)) {D : ℤ}
    (hD : ¬ (placePrime v : ℤ) ∣ 6 * D) (hp2 : placePrime v % 3 = 2) :
    ((((cubicCurve D).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ)).map (Int.castRingHom ℤ[ω]) =
      1 - C (heckeCharSextic D (placePrime v : ℤ[ω])) * X ^ 2 := by
  have hp : (placePrime v).Prime := Fact.out
  have hp2' : placePrime v ≠ 2 := by
    intro h; exact hD (by rw [h]; exact ⟨3 * D, by push_cast; ring⟩)
  rw [localPolynomial_cubicCurve v hD,
    numPointsCubicCurve_of_mod_three_eq_two hp2 hp2' (fun h => hD (dvd_mul_of_dvd_right h _)),
    heckeCharSextic_natCast hp hp2 hD]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_one,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_pow, Int.coe_castRingHom]
  push_cast
  simp only [add_sub_cancel_right, sub_self, map_zero, zero_mul, sub_zero, map_neg]
  ring

open IsDedekindDomain NumberField in
/-- **Theorem 8 of Chapter 18, inert primes, over `ℤ`**: `1 + p X²`. -/
theorem localPolynomial_cubicCurve_of_mod_three_eq_two (v : HeightOneSpectrum (𝓞 ℚ)) {D : ℤ}
    (hD : ¬ (placePrime v : ℤ) ∣ 6 * D) (hp2 : placePrime v % 3 = 2) :
    (((cubicCurve D).baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ) = 1 + C (placePrime v : ℤ) * X ^ 2 := by
  have hp2' : placePrime v ≠ 2 := by
    intro h; exact hD (by rw [h]; exact ⟨3 * D, by push_cast; ring⟩)
  rw [localPolynomial_cubicCurve v hD,
    numPointsCubicCurve_of_mod_three_eq_two hp2 hp2' (fun h => hD (dvd_mul_of_dvd_right h _))]
  push_cast
  simp

end NTKB.IrelandRosen.CM
