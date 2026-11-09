/-
Ireland–Rosen, Chapter 9, §8: the quartic residue character.
-/
import NTKB.IrelandRosen.R3.Irreducible

/-!
# The quartic residue character

Ireland–Rosen, Chapter 9, §8. For an irreducible `π` of `ℤ[i]` with `N π ≠ 2` and `π ∤ α`,
`α ^ ((N π - 1) / 4)` is congruent modulo `π` to exactly one of `1, i, -1, -i`
(Proposition 9.8.2); this unit is the quartic residue character `χ_π(α)`, and `χ_π(α) = 0` when
`π ∣ α` (`quarticChar`). Proposition 9.8.3 lists its properties and Proposition 9.8.4 its value on
rational integers when `π = q ≡ 3 (mod 4)`.

The definition is a plain case distinction on divisibility in `ℤ[i]`, so it makes sense for every
`π`; the theorems assume `π` irreducible with `N π ≠ 2`.
-/

namespace NTKB.IrelandRosen

open Zsqrtd

local notation "ℤ[i]" => GaussianInt

namespace Gaussian

/-- The exponent `(N π - 1) / 4` of the quartic residue character. -/
def qexp (π : ℤ[i]) : ℕ := (π.norm.natAbs - 1) / 4

open Classical in
/-- **Definition (§8).** The quartic (biquadratic) residue character `χ_π(α)`: `0` if `π ∣ α`,
otherwise the unit `i ^ j` with `α ^ ((N π - 1) / 4) ≡ i ^ j (mod π)`. -/
@[kb "irelandrosen1990" "Ch. 9, §8, Definition (quartic residue character), p. 133"]
noncomputable def quarticChar (π α : ℤ[i]) : ℤ[i] :=
  if π ∣ α then 0 else
  if π ∣ α ^ qexp π - 1 then 1 else
  if π ∣ α ^ qexp π - I then I else
  if π ∣ α ^ qexp π - (-1) then -1 else -I

lemma qexp_of_associated {π ρ : ℤ[i]} (h : Associated π ρ) : qexp π = qexp ρ := by
  rw [qexp, qexp, natAbs_norm_eq_of_associated h]

lemma qexp_star (π : ℤ[i]) : qexp (star π) = qexp π := by rw [qexp, qexp, natAbs_norm_star]

lemma quarticChar_eq_of_iff {π ρ α β : ℤ[i]} (h0 : π ∣ α ↔ ρ ∣ β)
    (h : ∀ u, π ∣ α ^ qexp π - u ↔ ρ ∣ β ^ qexp ρ - u) : quarticChar π α = quarticChar ρ β := by
  unfold quarticChar
  by_cases ha : π ∣ α
  · rw [if_pos ha, if_pos (h0.1 ha)]
  rw [if_neg ha, if_neg (fun hb => ha (h0.2 hb))]
  by_cases h1 : π ∣ α ^ qexp π - 1
  · rw [if_pos h1, if_pos ((h 1).1 h1)]
  rw [if_neg h1, if_neg (fun hb => h1 ((h 1).2 hb))]
  by_cases h2 : π ∣ α ^ qexp π - I
  · rw [if_pos h2, if_pos ((h I).1 h2)]
  rw [if_neg h2, if_neg (fun hb => h2 ((h I).2 hb))]
  by_cases h3 : π ∣ α ^ qexp π - (-1)
  · rw [if_pos h3, if_pos ((h (-1)).1 h3)]
  rw [if_neg h3, if_neg (fun hb => h3 ((h (-1)).2 hb))]

/-- **Proposition 9.8.3 (f).** `χ_π = χ_λ` if `(π) = (λ)`. -/
@[kb "irelandrosen1990" "Prop 9.8.3 (f), p. 133"]
theorem quarticChar_of_associated {π ρ : ℤ[i]} (h : Associated π ρ) :
    quarticChar π = quarticChar ρ := by
  funext α
  have hd : ∀ x, π ∣ x ↔ ρ ∣ x := fun x => ⟨h.symm.dvd.trans, h.dvd.trans⟩
  exact quarticChar_eq_of_iff (hd α) (fun u => by rw [qexp_of_associated h]; exact hd _)

/-- **Proposition 9.8.3 (e).** If `α ≡ β (mod π)` then `χ_π(α) = χ_π(β)`. -/
@[kb "irelandrosen1990" "Prop 9.8.3 (e), p. 133"]
theorem quarticChar_congr {π α β : ℤ[i]} (h : π ∣ α - β) : quarticChar π α = quarticChar π β := by
  have h1 : π ∣ α ↔ π ∣ β := by
    constructor
    · intro ha; have := dvd_sub ha h; simpa using this
    · intro hb; have := dvd_add hb h; simpa using this
  have hk : π ∣ α ^ qexp π - β ^ qexp π := h.trans (sub_dvd_pow_sub_pow _ _ _)
  have h2 : ∀ u, π ∣ α ^ qexp π - u ↔ π ∣ β ^ qexp π - u := by
    intro u
    constructor
    · intro ha; have := dvd_sub ha hk; rwa [show α ^ qexp π - u - (α ^ qexp π - β ^ qexp π) =
        β ^ qexp π - u by ring] at this
    · intro hb; have := dvd_add hb hk; rwa [show β ^ qexp π - u + (α ^ qexp π - β ^ qexp π) =
        α ^ qexp π - u by ring] at this
  exact quarticChar_eq_of_iff h1 h2

lemma quarticChar_of_dvd {π α : ℤ[i]} (h : π ∣ α) : quarticChar π α = 0 := by
  simp [quarticChar, h]

/-! ### The basic facts behind Proposition 9.8.2 -/

lemma natAbs_norm_ne_one_of_irreducible {π : ℤ[i]} (hπ : Irreducible π) : π.norm.natAbs ≠ 1 :=
  fun h => hπ.not_isUnit (isUnit_iff_natAbs_norm.2 h)

lemma natAbs_norm_ne_four_of_irreducible {π : ℤ[i]} (hπ : Irreducible π) :
    π.norm.natAbs ≠ 4 := by
  intro h4
  rcases irreducible_cases hπ with h | ⟨q, hq, hq3, hassoc⟩
  · rw [h4] at h; exact absurd h (by decide)
  · rw [natAbs_norm_eq_of_associated hassoc, natAbs_norm_natCast] at h4
    have : q ≤ 2 := by nlinarith
    omega

/-- For an irreducible `π` with `N π ≠ 2`, `N π ≡ 1 (mod 4)`. -/
lemma natAbs_norm_mod_four_eq_one {π : ℤ[i]} (hπ : Irreducible π) (h2 : π.norm.natAbs ≠ 2) :
    π.norm.natAbs % 4 = 1 := by
  rcases irreducible_cases hπ with h | ⟨q, hq, hq3, hassoc⟩
  · have h3 := natAbs_norm_mod_four π
    rcases h.eq_two_or_odd with h' | h'
    · exact absurd h' h2
    · omega
  · rw [natAbs_norm_eq_of_associated hassoc, natAbs_norm_natCast]
    obtain ⟨t, rfl⟩ : ∃ t, q = 4 * t + 3 := ⟨q / 4, by omega⟩
    have : (4 * t + 3) ^ 2 = 4 * (4 * t ^ 2 + 6 * t + 2) + 1 := by ring
    omega

lemma four_mul_qexp {π : ℤ[i]} (hπ : Irreducible π) (h2 : π.norm.natAbs ≠ 2) :
    4 * qexp π = π.norm.natAbs - 1 := by
  have := natAbs_norm_mod_four_eq_one hπ h2
  rw [qexp]; omega

lemma natAbs_norm_sub_unit_dvd_four {u v : ℤ[i]} (hu : IsUnit u) (hv : IsUnit v) :
    (u - v).norm.natAbs ∣ 4 ∨ u = v := by
  rcases isUnit_iff_eq.1 hu with rfl | rfl | rfl | rfl <;>
  rcases isUnit_iff_eq.1 hv with rfl | rfl | rfl | rfl <;>
  first
  | (right; rfl)
  | (left; simp only [norm_def, Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_neg, Zsqrtd.im_neg,
      Zsqrtd.re_one, Zsqrtd.im_one, I_re, I_im]; norm_num)

/-- The units `1, i, -1, -i` are pairwise incongruent modulo an irreducible `π` with `N π ≠ 2`. -/
theorem eq_of_isUnit_of_dvd_sub {π u v : ℤ[i]} (hπ : Irreducible π) (h2 : π.norm.natAbs ≠ 2)
    (hu : IsUnit u) (hv : IsUnit v) (h : π ∣ u - v) : u = v := by
  rcases natAbs_norm_sub_unit_dvd_four hu hv with h4 | h4
  · have := (norm_dvd_norm h).trans h4
    have hle : π.norm.natAbs ≤ 4 := Nat.le_of_dvd (by norm_num) this
    have h1 := natAbs_norm_ne_one_of_irreducible hπ
    have h4' := natAbs_norm_ne_four_of_irreducible hπ
    have h0 : π.norm.natAbs ≠ 0 := (natAbs_norm_pos hπ.ne_zero).ne'
    interval_cases hN : π.norm.natAbs <;> simp_all
  · exact h4

lemma pow_four_sub_one_eq (x : ℤ[i]) : x ^ 4 - 1 = (x - 1) * (x - I) * (x - (-1)) * (x - -I) := by
  have : I ^ 2 = -1 := I_sq
  linear_combination (x ^ 2 - 1) * this

lemma exists_isUnit_dvd_pow_qexp_sub {π α : ℤ[i]} (hπ : Irreducible π) (h2 : π.norm.natAbs ≠ 2)
    (hα : ¬ π ∣ α) : ∃ u, (u = 1 ∨ u = I ∨ u = -1 ∨ u = -I) ∧ π ∣ α ^ qexp π - u := by
  have hF := pow_norm_sub_one_modEq hπ hα
  rw [← four_mul_qexp hπ h2, pow_mul', pow_four_sub_one_eq] at hF
  have hp := hπ.prime
  rcases hp.dvd_or_dvd hF with hF | hF
  · rcases hp.dvd_or_dvd hF with hF | hF
    · rcases hp.dvd_or_dvd hF with hF | hF
      · exact ⟨1, Or.inl rfl, hF⟩
      · exact ⟨I, Or.inr (Or.inl rfl), hF⟩
    · exact ⟨-1, Or.inr (Or.inr (Or.inl rfl)), hF⟩
  · exact ⟨-I, Or.inr (Or.inr (Or.inr rfl)), hF⟩

/-- `χ_π(α)` is a unit with `α ^ ((N π - 1) / 4) ≡ χ_π(α) (mod π)` when `π ∤ α`. -/
theorem quarticChar_spec {π α : ℤ[i]} (hπ : Irreducible π) (h2 : π.norm.natAbs ≠ 2)
    (hα : ¬ π ∣ α) : IsUnit (quarticChar π α) ∧ π ∣ α ^ qexp π - quarticChar π α := by
  obtain ⟨u, hu, hdvd⟩ := exists_isUnit_dvd_pow_qexp_sub hπ h2 hα
  unfold quarticChar
  rw [if_neg hα]
  split_ifs with h1 h3 h4
  · exact ⟨isUnit_one, h1⟩
  · exact ⟨isUnit_I, h3⟩
  · exact ⟨isUnit_one.neg, h4⟩
  · rcases hu with rfl | rfl | rfl | rfl
    · exact absurd hdvd h1
    · exact absurd hdvd h3
    · exact absurd hdvd h4
    · exact ⟨isUnit_I.neg, hdvd⟩

/-- The value `χ_π(α)` is the only unit congruent to `α ^ ((N π - 1) / 4)` modulo `π`. -/
theorem quarticChar_eq_of_dvd {π α u : ℤ[i]} (hπ : Irreducible π) (h2 : π.norm.natAbs ≠ 2)
    (hα : ¬ π ∣ α) (hu : IsUnit u) (h : π ∣ α ^ qexp π - u) : quarticChar π α = u := by
  obtain ⟨hχ, hχ'⟩ := quarticChar_spec hπ h2 hα
  refine eq_of_isUnit_of_dvd_sub hπ h2 hχ hu ?_
  have := dvd_sub h hχ'
  rwa [show α ^ qexp π - u - (α ^ qexp π - quarticChar π α) = quarticChar π α - u by ring] at this

lemma isUnit_iff_eq_I_pow {u : ℤ[i]} : IsUnit u ↔ ∃ j : Fin 4, u = I ^ (j : ℕ) := by
  rw [isUnit_iff_eq]
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨2, by simp [I_sq]⟩
    · exact ⟨1, by simp⟩
    · exact ⟨3, by ext <;> simp [pow_succ]⟩
  · rintro ⟨j, rfl⟩
    fin_cases j
    · simp
    · simp
    · simp [I_sq]
    · simp [pow_succ, I_sq]

/-- **Proposition 9.8.2.** If `π` is irreducible, `(π) ≠ (1 + i)` (equivalently `N π ≠ 2`) and
`π ∤ α`, there is a unique `j ∈ {0, 1, 2, 3}` with `α ^ ((N π - 1) / 4) ≡ i ^ j (mod π)`. -/
@[kb "irelandrosen1990" "Prop 9.8.2, p. 133"]
theorem existsUnique_pow_qexp_modEq {π α : ℤ[i]} (hπ : Irreducible π) (h2 : π.norm.natAbs ≠ 2)
    (hα : ¬ π ∣ α) : ∃! j : Fin 4, π ∣ α ^ ((π.norm.natAbs - 1) / 4) - I ^ (j : ℕ) := by
  obtain ⟨hχ, hχ'⟩ := quarticChar_spec hπ h2 hα
  obtain ⟨j, hj⟩ := isUnit_iff_eq_I_pow.1 hχ
  refine ⟨j, by beta_reduce; rw [← hj]; exact hχ', fun j' hj' => ?_⟩
  have := quarticChar_eq_of_dvd hπ h2 hα (isUnit_iff_eq_I_pow.2 ⟨j', rfl⟩) hj'
  rw [hj] at this
  -- `i ^ j = i ^ j'` with `j, j' < 4` forces `j = j'`
  fin_cases j <;> fin_cases j' <;> first | rfl | (simp [pow_succ, I_sq, Zsqrtd.ext_iff] at this)

lemma natAbs_norm_ne_two_iff {π : ℤ[i]} (hπ : Irreducible π) :
    π.norm.natAbs ≠ 2 ↔ ¬ Associated π onePlusI := by
  constructor
  · intro h h'; apply h; rw [natAbs_norm_eq_of_associated h', norm_onePlusI]; rfl
  · intro h h'
    apply h
    have hp : π ∣ 2 := by
      have := dvd_natAbs_norm π; rw [h'] at this; exact_mod_cast this
    rw [two_eq_neg_I_mul_onePlusI_sq] at hp
    have hdvd : π ∣ onePlusI := by
      rcases hπ.prime.dvd_or_dvd hp with h1 | h1
      · exact absurd (isUnit_of_dvd_unit h1 isUnit_I.neg) hπ.not_isUnit
      · exact hπ.prime.dvd_of_dvd_pow h1
    exact (irreducible_onePlusI.dvd_iff.1 hdvd).resolve_left hπ.not_isUnit |>.symm

/-! ### Proposition 9.8.3 -/

/-- **Proposition 9.8.3 (b).** `χ_π(α β) = χ_π(α) χ_π(β)`. -/
@[kb "irelandrosen1990" "Prop 9.8.3 (b), p. 133"]
theorem quarticChar_mul {π : ℤ[i]} (hπ : Irreducible π) (h2 : π.norm.natAbs ≠ 2) (α β : ℤ[i]) :
    quarticChar π (α * β) = quarticChar π α * quarticChar π β := by
  by_cases hα : π ∣ α
  · rw [quarticChar_of_dvd hα, quarticChar_of_dvd (dvd_mul_of_dvd_left hα _), zero_mul]
  by_cases hβ : π ∣ β
  · rw [quarticChar_of_dvd hβ, quarticChar_of_dvd (dvd_mul_of_dvd_right hβ _), mul_zero]
  have hαβ : ¬ π ∣ α * β := fun h => (hπ.prime.dvd_or_dvd h).elim hα hβ
  obtain ⟨u1, h1⟩ := quarticChar_spec hπ h2 hα
  obtain ⟨u2, h2'⟩ := quarticChar_spec hπ h2 hβ
  refine quarticChar_eq_of_dvd hπ h2 hαβ (u1.mul u2) ?_
  have : (α * β) ^ qexp π - quarticChar π α * quarticChar π β =
      (α ^ qexp π - quarticChar π α) * β ^ qexp π +
        quarticChar π α * (β ^ qexp π - quarticChar π β) := by ring
  rw [this]; exact dvd_add (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_right h2' _)

lemma quarticChar_one {π : ℤ[i]} (hπ : Irreducible π) (h2 : π.norm.natAbs ≠ 2) :
    quarticChar π 1 = 1 :=
  quarticChar_eq_of_dvd hπ h2 (fun h => hπ.not_isUnit (isUnit_of_dvd_one h)) isUnit_one (by simp)

/-- On units the character is `χ_π(u) = u ^ ((N π - 1) / 4)`. -/
theorem quarticChar_of_isUnit {π u : ℤ[i]} (hπ : Irreducible π) (h2 : π.norm.natAbs ≠ 2)
    (hu : IsUnit u) : quarticChar π u = u ^ qexp π :=
  quarticChar_eq_of_dvd hπ h2 (fun h => hπ.not_isUnit (isUnit_of_dvd_unit h hu)) (hu.pow _)
    (by simp)

lemma irreducible_star {π : ℤ[i]} (hπ : Irreducible π) : Irreducible (star π) :=
  (MulEquiv.irreducible_iff (starRingAut (R := ℤ[i])).toMulEquiv).2 hπ

lemma star_dvd_star_iff {α β : ℤ[i]} : star α ∣ star β ↔ α ∣ β := by
  constructor
  · intro h; simpa [starRingEnd_apply] using map_dvd (starRingEnd ℤ[i]) h
  · intro h; exact map_dvd (starRingEnd ℤ[i]) h

/-- **Proposition 9.8.3 (c).** `χ_π̄(ᾱ) = conj χ_π(α)`. -/
@[kb "irelandrosen1990" "Prop 9.8.3 (c), p. 133"]
theorem quarticChar_star {π : ℤ[i]} (hπ : Irreducible π) (h2 : π.norm.natAbs ≠ 2) (α : ℤ[i]) :
    quarticChar (star π) (star α) = star (quarticChar π α) := by
  by_cases hα : π ∣ α
  · rw [quarticChar_of_dvd hα, quarticChar_of_dvd (star_dvd_star_iff.2 hα), star_zero]
  obtain ⟨hu, hd⟩ := quarticChar_spec hπ h2 hα
  have h2' : (star π).norm.natAbs ≠ 2 := by rwa [natAbs_norm_star]
  refine quarticChar_eq_of_dvd (irreducible_star hπ) h2' (fun h => hα (star_dvd_star_iff.1 h))
    (by simpa [starRingEnd_apply] using hu.map (starRingEnd ℤ[i])) ?_
  rw [qexp_star, ← star_pow, ← star_sub]; exact star_dvd_star_iff.2 hd

/-- **Proposition 9.8.3 (a).** For `π ∤ α`, `χ_π(α) = 1` iff `x⁴ ≡ α (mod π)` is solvable. -/
@[kb "irelandrosen1990" "Prop 9.8.3 (a), p. 133"]
theorem quarticChar_eq_one_iff {π α : ℤ[i]} (hπ : Irreducible π) (h2 : π.norm.natAbs ≠ 2)
    (hα : ¬ π ∣ α) : quarticChar π α = 1 ↔ ∃ x : ℤ[i], π ∣ x ^ 4 - α := by
  obtain ⟨hmax, hcard⟩ := card_quotient_of_irreducible hπ
  letI := Ideal.Quotient.field (Ideal.span {π})
  let mk := Ideal.Quotient.mk (Ideal.span {π})
  have hmk : ∀ x y : ℤ[i], mk x = mk y ↔ π ∣ x - y := fun x y => by
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  have hk := four_mul_qexp hπ h2
  haveI : Finite (ℤ[i] ⧸ Ideal.span {π}) := Nat.finite_of_card_ne_zero (by
    rw [hcard]; exact (natAbs_norm_pos hπ.ne_zero).ne')
  have hne : mk α ≠ 0 := by
    intro h; apply hα; rw [← sub_zero α, ← hmk, map_zero]; exact h
  have hunits : Nat.card (ℤ[i] ⧸ Ideal.span {π})ˣ = 4 * qexp π := by
    rw [hk, ← hcard, Nat.card_units]
  constructor
  · intro h1
    obtain ⟨-, hd⟩ := quarticChar_spec hπ h2 hα
    rw [h1, ← hmk, map_pow, map_one] at hd
    -- in the cyclic group of units, an element whose `k`-th power is `1` is a fourth power
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ℤ[i] ⧸ Ideal.span {π})ˣ)
    let a : (ℤ[i] ⧸ Ideal.span {π})ˣ := Units.mk0 (mk α) hne
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hg a)
    have hog : orderOf g = 4 * qexp π := by
      rw [← hunits, orderOf_eq_card_of_forall_mem_zpowers hg]
    have hak : a ^ qexp π = 1 := by ext; simp [a, hd]
    rw [← hm, ← zpow_natCast, ← zpow_mul, ← orderOf_dvd_iff_zpow_eq_one, hog] at hak
    have hq0 : 0 < qexp π := by
      have := natAbs_norm_ne_one_of_irreducible hπ
      have h0 := natAbs_norm_pos hπ.ne_zero
      omega
    have h4 : (4 : ℤ) ∣ m := by
      obtain ⟨c, hc⟩ := hak
      refine ⟨c, ?_⟩
      have : (qexp π : ℤ) * m = qexp π * (4 * c) := by push_cast at hc; linarith
      exact mul_left_cancel₀ (by exact_mod_cast hq0.ne') this
    obtain ⟨c, rfl⟩ := h4
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective ((g ^ c : (ℤ[i] ⧸ Ideal.span {π})ˣ) :
      ℤ[i] ⧸ Ideal.span {π})
    refine ⟨x, (hmk _ _).1 ?_⟩
    have hx' : mk x = ((g ^ c : (ℤ[i] ⧸ Ideal.span {π})ˣ) : ℤ[i] ⧸ Ideal.span {π}) := hx
    rw [map_pow, hx', ← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul]
    have : g ^ (c * ((4 : ℕ) : ℤ)) = a := by rw [← hm]; congr 1; push_cast; ring
    rw [this]; rfl
  · rintro ⟨x, hx⟩
    refine quarticChar_eq_of_dvd hπ h2 hα isUnit_one ?_
    rw [← hmk] at hx ⊢
    rw [map_pow] at hx
    have hx0 : mk x ≠ 0 := by
      intro h; rw [h, zero_pow (by norm_num)] at hx; exact hne hx.symm
    letI := Fintype.ofFinite (ℤ[i] ⧸ Ideal.span {π})
    rw [map_pow, map_one, ← hx, ← pow_mul, hk, ← hcard, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one _ hx0

/-- **Proposition 9.8.3 (d).** For a primary irreducible `π = a + b i`,
`χ_π(-1) = (-1) ^ ((a - 1) / 2)`. -/
@[kb "irelandrosen1990" "Prop 9.8.3 (d), p. 133"]
theorem IsPrimary.quarticChar_neg_one {π : ℤ[i]} (hp : IsPrimary π) (hπ : Irreducible π) :
    quarticChar π (-1) = (-1) ^ ((π.re - 1) / 2).natAbs := by
  have h2 : π.norm.natAbs ≠ 2 := by have := hp.2.natAbs_norm_mod_four; omega
  rw [quarticChar_of_isUnit hπ h2 isUnit_one.neg]
  -- `(N π - 1) / 4 ≡ (a - 1) / 2 (mod 2)`
  have hP := (isPrimary'_iff π).1 hp.2
  have hn : (π.norm.natAbs : ℤ) = π.re ^ 2 + π.im ^ 2 := by rw [natAbs_norm, norm_def]
  obtain ⟨s, hs⟩ : ∃ s, π.re = 2 * s + 1 := ⟨π.re / 2, by have := hp.2.re_odd; omega⟩
  obtain ⟨t, ht⟩ : ∃ t, π.im = 2 * t := hp.2.im_even
  have hq : (qexp π : ℤ) = s ^ 2 + s + t ^ 2 := by
    have h4 := four_mul_qexp hπ h2
    have h1 : 1 ≤ π.norm.natAbs := natAbs_norm_pos hπ.ne_zero
    have : ((4 * qexp π : ℕ) : ℤ) = ((π.norm.natAbs - 1 : ℕ) : ℤ) := by rw [h4]
    rw [Nat.cast_mul, Nat.cast_sub h1, Nat.cast_one, hn, hs, ht] at this
    push_cast at this; linarith
  have hss : (s ^ 2 + s) % 2 = 0 := by
    have := Int.even_mul_succ_self s
    rw [show s * (s + 1) = s ^ 2 + s by ring, Int.even_iff] at this; exact this
  have htt : (t ^ 2 - t) % 2 = 0 := by
    have := Int.even_mul_succ_self (t - 1)
    rw [show (t - 1) * (t - 1 + 1) = t ^ 2 - t by ring, Int.even_iff] at this; exact this
  have hpar : Even (qexp π) ↔ Even ((π.re - 1) / 2).natAbs := by
    have e1 : (π.re - 1) / 2 = s := by omega
    rw [e1, Int.natAbs_even, ← Int.even_coe_nat, hq, Int.even_iff, Int.even_iff]
    rw [hs, ht] at hP
    omega
  rcases Nat.even_or_odd (qexp π) with he | ho
  · rw [he.neg_one_pow, (hpar.1 he).neg_one_pow]
  · rw [ho.neg_one_pow, (Nat.not_even_iff_odd.1 (fun h => (Nat.not_even_iff_odd.2 ho)
      (hpar.2 h))).neg_one_pow]

/-! ### Proposition 9.8.4 -/

/-- **Proposition 9.8.4.** If `q ≡ 3 (mod 4)` is prime then `χ_q(a) = 1` for every rational
integer `a` prime to `q`. -/
@[kb "irelandrosen1990" "Prop 9.8.4, p. 133"]
theorem quarticChar_natCast_intCast {q : ℕ} (hq : q.Prime) (hq3 : q % 4 = 3) {a : ℤ}
    (ha : ¬ (q : ℤ) ∣ a) : quarticChar (q : ℤ[i]) (a : ℤ[i]) = 1 := by
  haveI := Fact.mk hq
  have hirr : Irreducible (q : ℤ[i]) :=
    (GaussianInt.prime_of_nat_prime_of_mod_four_eq_three q hq3).irreducible
  have h2 : (q : ℤ[i]).norm.natAbs ≠ 2 := by rw [natAbs_norm_natCast]; nlinarith [hq.two_le]
  have hdvd : ∀ n : ℤ, (q : ℤ[i]) ∣ (n : ℤ[i]) ↔ (q : ℤ) ∣ n := by
    intro n; rw [← Int.cast_natCast, Zsqrtd.intCast_dvd]; simp
  refine quarticChar_eq_of_dvd hirr h2 (by rwa [hdvd]) isUnit_one ?_
  -- `a ^ ((q² - 1) / 4) = (a ^ (q - 1)) ^ ((q + 1) / 4) ≡ 1 (mod q)`
  have hexp : qexp (q : ℤ[i]) = (q - 1) * ((q + 1) / 4) := by
    rw [qexp, natAbs_norm_natCast]
    obtain ⟨t, rfl⟩ : ∃ t, q = 4 * t + 3 := ⟨q / 4, by omega⟩
    have e1 : (4 * t + 3) ^ 2 - 1 = 4 * ((4 * t + 2) * (t + 1)) := by
      rw [Nat.sub_eq_iff_eq_add (pow_pos (by omega : 0 < 4 * t + 3) 2)]; ring
    rw [e1, Nat.mul_div_cancel_left _ (by norm_num)]
    have e2 : (4 * t + 3 + 1) / 4 = t + 1 := by omega
    rw [e2]; congr 1
  have hF : (q : ℤ) ∣ a ^ (q - 1) - 1 := by
    have := Int.ModEq.pow_card_sub_one_eq_one hq
      ((Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.1 hq)).2 ha).symm
    exact (Int.ModEq.dvd this.symm)
  have : (q : ℤ) ∣ a ^ qexp (q : ℤ[i]) - 1 := by
    rw [hexp, pow_mul]
    exact hF.trans (by simpa using sub_dvd_pow_sub_pow (a ^ (q - 1)) 1 ((q + 1) / 4))
  rw [← hdvd] at this; exact_mod_cast this

end Gaussian

end NTKB.IrelandRosen
