/-
Ireland–Rosen, Chapter 9, §3: the cubic residue character.
-/
import NTKB.IrelandRosen.R4.Eisenstein

/-!
# The cubic residue character (Ireland–Rosen, Chapter 9, §3)

For a prime `π` of `ℤ[ω]` with `N π ≠ 3` and `π ∤ α`, `α ^ ((N π - 1) / 3)` is congruent modulo
`π` to exactly one of `1, ω, ω²` (Proposition 9.3.2); this is the cubic residue character
`χ_π(α) = (α/π)₃`, and `χ_π(α) = 0` when `π ∣ α` (`cubicChar`). Propositions 9.3.3 and 9.3.4, the
corollary to 9.3.4 and remark (b) after Theorem 1 list its properties.

The definition is a case distinction on divisibility in `ℤ[ω]`, so it makes sense for every `π`;
the theorems assume `π` prime with `N π ≠ 3`.
-/

namespace NTKB.IrelandRosen

open NTKB.HardyWright QuadraticAlgebra

local notation "ℤ[ω]" => NTKB.HardyWright.ZRho

namespace Eisenstein

/-- The exponent `(N π - 1) / 3` of the cubic residue character. -/
def cexp (π : ℤ[ω]) : ℕ := ((norm π).natAbs - 1) / 3

open Classical in
/-- **Definition (§3).** The cubic residue character `χ_π(α) = (α/π)₃`: `0` if `π ∣ α`,
otherwise the one of `1, ω, ω²` congruent to `α ^ ((N π - 1) / 3)` modulo `π`. -/
@[kb "irelandrosen1990" "Ch. 9, §3, Definition (cubic residue character), p. 123"]
noncomputable def cubicChar (π α : ℤ[ω]) : ℤ[ω] :=
  if π ∣ α then 0 else
  if π ∣ α ^ cexp π - 1 then 1 else
  if π ∣ α ^ cexp π - omega then omega else omega ^ 2

lemma cubicChar_of_dvd {π α : ℤ[ω]} (h : π ∣ α) : cubicChar π α = 0 := by
  simp [cubicChar, h]

/-- `N π ≢ 0, 1` constraints: an element of norm `±1` is a unit. -/
lemma isUnit_of_natAbs_norm_eq_one {x : ℤ[ω]} (h : (norm x).natAbs = 1) : IsUnit x := by
  have h1 : IsUnit (norm x) := Int.isUnit_iff_natAbs_eq.2 h
  have h2 : IsUnit (((norm x : ℤ) : ℤ[ω])) := h1.map (Int.castRingHom ℤ[ω])
  rw [← mul_star] at h2
  exact isUnit_of_mul_isUnit_left h2

/-- Associated elements have the same norm (up to sign). -/
lemma natAbs_norm_eq_of_associated {π ρ : ℤ[ω]} (h : Associated π ρ) :
    (norm π).natAbs = (norm ρ).natAbs := by
  obtain ⟨u, rfl⟩ := h
  have h1 : IsUnit (norm (u : ℤ[ω])) := u.isUnit.map QuadraticAlgebra.norm
  rw [map_mul, Int.natAbs_mul, Int.isUnit_iff_natAbs_eq.1 h1, mul_one]

lemma cexp_of_associated {π ρ : ℤ[ω]} (h : Associated π ρ) : cexp π = cexp ρ := by
  rw [cexp, cexp, natAbs_norm_eq_of_associated h]

lemma cexp_star (π : ℤ[ω]) : cexp (star π) = cexp π := by rw [cexp, cexp, natAbs_norm_star]

lemma three_mul_cexp {π : ℤ[ω]} (hπ : Prime π) (h3 : (norm π).natAbs ≠ 3) :
    3 * cexp π = (norm π).natAbs - 1 := by
  have := natAbs_norm_mod_three hπ h3
  rw [cexp]; omega

lemma cexp_pos {π : ℤ[ω]} (hπ : Prime π) (h3 : (norm π).natAbs ≠ 3) : 0 < cexp π := by
  have h1 := natAbs_norm_mod_three hπ h3
  have : (norm π).natAbs ≠ 1 := fun h => hπ.not_isUnit (isUnit_of_natAbs_norm_eq_one h)
  rw [cexp]; omega

lemma omega_ne_one : omega ≠ 1 := by
  intro h
  have := congrArg QuadraticAlgebra.re h
  simp [omega] at this

lemma omega_sq_ne_one : omega ^ 2 ≠ 1 := by
  intro h
  rw [omega_sq] at h
  have := congrArg QuadraticAlgebra.im h
  simp [omega] at this

lemma omega_ne_omega_sq : omega ≠ omega ^ 2 := by
  intro h
  rw [omega_sq] at h
  have := congrArg QuadraticAlgebra.re h
  simp [omega] at this

/-- The cube roots of unity in `ℤ[ω]` are `1, ω, ω²`. -/
lemma pow_three_eq_one_iff {u : ℤ[ω]} : u ^ 3 = 1 ↔ u = 1 ∨ u = omega ∨ u = omega ^ 2 := by
  constructor
  · intro h
    have h' : (u - 1) * (u - omega) * (u - omega ^ 2) = 0 := by
      have := omega_sq
      have h3 := omega_cube
      linear_combination h + (u - u ^ 2) * this + (u - 1) * h3
    rcases mul_eq_zero.1 h' with h' | h'
    · rcases mul_eq_zero.1 h' with h' | h'
      · exact Or.inl (sub_eq_zero.1 h')
      · exact Or.inr (Or.inl (sub_eq_zero.1 h'))
    · exact Or.inr (Or.inr (sub_eq_zero.1 h'))
  · rintro (rfl | rfl | rfl)
    · simp
    · exact omega_cube
    · rw [← pow_mul, mul_comm, pow_mul, omega_cube, one_pow]

/-- `u - v ∣ 3` for distinct cube roots of unity. -/
lemma sub_dvd_three {u v : ℤ[ω]} (hu : u ^ 3 = 1) (hv : v ^ 3 = 1) (h : u ≠ v) : u - v ∣ 3 := by
  have h3 := three_eq_and_prime_one_sub_omega.1
  have hw := omega_sq
  rw [pow_three_eq_one_iff] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  all_goals try exact absurd rfl h
  · exact ⟨-omega ^ 2 * (1 - omega), by rw [h3]; ring⟩
  · exact ⟨1 - omega, by rw [h3]; linear_combination (-(1 - omega) ^ 2) * hw⟩
  · exact ⟨omega ^ 2 * (1 - omega), by rw [h3]; ring⟩
  · exact ⟨-omega * (1 - omega), by rw [h3]; ring⟩
  · exact ⟨-(1 - omega), by rw [h3]; linear_combination (-(1 - omega) ^ 2) * hw⟩
  · exact ⟨omega * (1 - omega), by rw [h3]; ring⟩

/-- `1, ω, ω²` are pairwise incongruent modulo a prime `π` with `N π ≠ 3`. -/
theorem eq_of_pow_three_eq_one_of_dvd_sub {π u v : ℤ[ω]} (hπ : Prime π)
    (h3 : (norm π).natAbs ≠ 3) (hu : u ^ 3 = 1) (hv : v ^ 3 = 1) (h : π ∣ u - v) : u = v := by
  by_contra hne
  exact (natAbs_norm_ne_three_iff hπ).1 h3 (h.trans (sub_dvd_three hu hv hne))

lemma pow_three_sub_one_eq (x : ℤ[ω]) :
    x ^ 3 - 1 = (x - 1) * (x - omega) * (x - omega ^ 2) := by
  have := omega_sq
  have h3 := omega_cube
  linear_combination (x ^ 2 - x) * this + (1 - x) * h3

lemma exists_cube_root_dvd_pow_cexp_sub {π α : ℤ[ω]} (hπ : Prime π) (h3 : (norm π).natAbs ≠ 3)
    (hα : ¬ π ∣ α) : ∃ u, (u = 1 ∨ u = omega ∨ u = omega ^ 2) ∧ π ∣ α ^ cexp π - u := by
  have hF := pow_natAbs_norm_sub_one_modEq hπ hα
  rw [← three_mul_cexp hπ h3, pow_mul', pow_three_sub_one_eq] at hF
  rcases hπ.dvd_or_dvd hF with hF | hF
  · rcases hπ.dvd_or_dvd hF with hF | hF
    · exact ⟨1, Or.inl rfl, hF⟩
    · exact ⟨omega, Or.inr (Or.inl rfl), hF⟩
  · exact ⟨omega ^ 2, Or.inr (Or.inr rfl), hF⟩

lemma omega_pow_cube (n : ℕ) : (omega ^ n) ^ 3 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, omega_cube, one_pow]

/-- `χ_π(α)` is a cube root of unity with `α ^ ((N π - 1) / 3) ≡ χ_π(α) (mod π)` when `π ∤ α`. -/
theorem cubicChar_spec {π α : ℤ[ω]} (hπ : Prime π) (h3 : (norm π).natAbs ≠ 3) (hα : ¬ π ∣ α) :
    cubicChar π α ^ 3 = 1 ∧ π ∣ α ^ cexp π - cubicChar π α := by
  obtain ⟨u, hu, hdvd⟩ := exists_cube_root_dvd_pow_cexp_sub hπ h3 hα
  unfold cubicChar
  rw [if_neg hα]
  split_ifs with h1 h2
  · exact ⟨one_pow 3, h1⟩
  · exact ⟨omega_cube, h2⟩
  · rcases hu with rfl | rfl | rfl
    · exact absurd hdvd h1
    · exact absurd hdvd h2
    · exact ⟨omega_pow_cube 2, hdvd⟩

/-- The value `χ_π(α)` is the only cube root of unity congruent to `α ^ ((N π - 1) / 3)`. -/
theorem cubicChar_eq_of_dvd {π α u : ℤ[ω]} (hπ : Prime π) (h3 : (norm π).natAbs ≠ 3)
    (hα : ¬ π ∣ α) (hu : u ^ 3 = 1) (h : π ∣ α ^ cexp π - u) : cubicChar π α = u := by
  obtain ⟨hχ, hχ'⟩ := cubicChar_spec hπ h3 hα
  refine eq_of_pow_three_eq_one_of_dvd_sub hπ h3 hχ hu ?_
  have := dvd_sub h hχ'
  rwa [show α ^ cexp π - u - (α ^ cexp π - cubicChar π α) = cubicChar π α - u by ring] at this

lemma omega_pow_inj {i j : Fin 3} (h : omega ^ (i : ℕ) = omega ^ (j : ℕ)) : i = j := by
  fin_cases i <;> fin_cases j <;>
  first
  | rfl
  | (exfalso
     simp only [pow_zero, pow_one] at h
     first
     | exact omega_ne_one h
     | exact omega_ne_one h.symm
     | exact omega_sq_ne_one h
     | exact omega_sq_ne_one h.symm
     | exact omega_ne_omega_sq h
     | exact omega_ne_omega_sq h.symm)

/-- **Proposition 9.3.2.** If `π` is prime, `N π ≠ 3` and `π ∤ α`, there is a unique
`m ∈ {0, 1, 2}` with `α ^ ((N π - 1) / 3) ≡ ω ^ m (mod π)`. -/
@[kb "irelandrosen1990" "Prop 9.3.2, p. 123"]
theorem existsUnique_pow_cexp_modEq {π α : ℤ[ω]} (hπ : Prime π) (h3 : (norm π).natAbs ≠ 3)
    (hα : ¬ π ∣ α) : ∃! m : Fin 3, π ∣ α ^ (((norm π).natAbs - 1) / 3) - omega ^ (m : ℕ) := by
  obtain ⟨hχ, hχ'⟩ := cubicChar_spec hπ h3 hα
  obtain ⟨j, hj⟩ : ∃ j : Fin 3, cubicChar π α = omega ^ (j : ℕ) := by
    rcases pow_three_eq_one_iff.1 hχ with h | h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
    · exact ⟨2, h⟩
  refine ⟨j, by beta_reduce; rw [← hj]; exact hχ', fun j' hj' => ?_⟩
  have := cubicChar_eq_of_dvd hπ h3 hα (omega_pow_cube j') hj'
  rw [hj] at this
  exact (omega_pow_inj this).symm

lemma cubicChar_eq_of_iff {π ρ α β : ℤ[ω]} (h0 : π ∣ α ↔ ρ ∣ β)
    (h : ∀ u, π ∣ α ^ cexp π - u ↔ ρ ∣ β ^ cexp ρ - u) : cubicChar π α = cubicChar ρ β := by
  unfold cubicChar
  by_cases ha : π ∣ α
  · rw [if_pos ha, if_pos (h0.1 ha)]
  rw [if_neg ha, if_neg (fun hb => ha (h0.2 hb))]
  by_cases h1 : π ∣ α ^ cexp π - 1
  · rw [if_pos h1, if_pos ((h 1).1 h1)]
  rw [if_neg h1, if_neg (fun hb => h1 ((h 1).2 hb))]
  by_cases h2 : π ∣ α ^ cexp π - omega
  · rw [if_pos h2, if_pos ((h omega).1 h2)]
  rw [if_neg h2, if_neg (fun hb => h2 ((h omega).2 hb))]

/-- **Proposition 9.3.3 (d).** If `α ≡ β (mod π)` then `χ_π(α) = χ_π(β)`. -/
@[kb "irelandrosen1990" "Prop 9.3.3 (d), p. 123"]
theorem cubicChar_congr {π α β : ℤ[ω]} (h : π ∣ α - β) : cubicChar π α = cubicChar π β := by
  have h1 : π ∣ α ↔ π ∣ β := by
    constructor
    · intro ha; have := dvd_sub ha h; simpa using this
    · intro hb; have := dvd_add hb h; simpa using this
  have hk : π ∣ α ^ cexp π - β ^ cexp π := h.trans (sub_dvd_pow_sub_pow _ _ _)
  have h2 : ∀ u, π ∣ α ^ cexp π - u ↔ π ∣ β ^ cexp π - u := by
    intro u
    constructor
    · intro ha; have := dvd_sub ha hk; rwa [show α ^ cexp π - u - (α ^ cexp π - β ^ cexp π) =
        β ^ cexp π - u by ring] at this
    · intro hb; have := dvd_add hb hk; rwa [show β ^ cexp π - u + (α ^ cexp π - β ^ cexp π) =
        α ^ cexp π - u by ring] at this
  exact cubicChar_eq_of_iff h1 h2

/-- `χ_π = χ_ρ` if `(π) = (ρ)`. -/
theorem cubicChar_of_associated {π ρ : ℤ[ω]} (h : Associated π ρ) : cubicChar π = cubicChar ρ := by
  funext α
  have hd : ∀ x, π ∣ x ↔ ρ ∣ x := fun x => ⟨h.symm.dvd.trans, h.dvd.trans⟩
  exact cubicChar_eq_of_iff (hd α) (fun u => by rw [cexp_of_associated h]; exact hd _)

/-- **Proposition 9.3.3 (c).** `χ_π(α β) = χ_π(α) χ_π(β)`. -/
@[kb "irelandrosen1990" "Prop 9.3.3 (c), p. 123"]
theorem cubicChar_mul {π : ℤ[ω]} (hπ : Prime π) (h3 : (norm π).natAbs ≠ 3) (α β : ℤ[ω]) :
    cubicChar π (α * β) = cubicChar π α * cubicChar π β := by
  by_cases hα : π ∣ α
  · rw [cubicChar_of_dvd hα, cubicChar_of_dvd (dvd_mul_of_dvd_left hα _), zero_mul]
  by_cases hβ : π ∣ β
  · rw [cubicChar_of_dvd hβ, cubicChar_of_dvd (dvd_mul_of_dvd_right hβ _), mul_zero]
  have hαβ : ¬ π ∣ α * β := fun h => (hπ.dvd_or_dvd h).elim hα hβ
  obtain ⟨u1, h1⟩ := cubicChar_spec hπ h3 hα
  obtain ⟨u2, h2'⟩ := cubicChar_spec hπ h3 hβ
  refine cubicChar_eq_of_dvd hπ h3 hαβ (by rw [mul_pow, u1, u2, one_mul]) ?_
  have : (α * β) ^ cexp π - cubicChar π α * cubicChar π β =
      (α ^ cexp π - cubicChar π α) * β ^ cexp π +
        cubicChar π α * (β ^ cexp π - cubicChar π β) := by ring
  rw [this]; exact dvd_add (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_right h2' _)

lemma cubicChar_one {π : ℤ[ω]} (hπ : Prime π) (h3 : (norm π).natAbs ≠ 3) :
    cubicChar π 1 = 1 :=
  cubicChar_eq_of_dvd hπ h3 (fun h => hπ.not_isUnit (isUnit_of_dvd_one h)) (one_pow 3) (by simp)

lemma cubicChar_pow {π : ℤ[ω]} (hπ : Prime π) (h3 : (norm π).natAbs ≠ 3) (α : ℤ[ω]) (n : ℕ) :
    cubicChar π (α ^ n) = cubicChar π α ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, cubicChar_one hπ h3]
  | succ n ih => rw [pow_succ, pow_succ, cubicChar_mul hπ h3, ih]

/-- **Proposition 9.3.3 (a).** For `π ∤ α`, `χ_π(α) = 1` iff `x³ ≡ α (mod π)` is solvable. -/
@[kb "irelandrosen1990" "Prop 9.3.3 (a), p. 123"]
theorem cubicChar_eq_one_iff {π α : ℤ[ω]} (hπ : Prime π) (h3 : (norm π).natAbs ≠ 3)
    (hα : ¬ π ∣ α) : cubicChar π α = 1 ↔ ∃ x : ℤ[ω], π ∣ x ^ 3 - α := by
  obtain ⟨hmax, hcard⟩ := card_quotient hπ
  letI := Ideal.Quotient.field (Ideal.span {π})
  let mk := Ideal.Quotient.mk (Ideal.span {π})
  have hmk : ∀ x y : ℤ[ω], mk x = mk y ↔ π ∣ x - y := fun x y => by
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  have hk := three_mul_cexp hπ h3
  have hq0 := cexp_pos hπ h3
  haveI : Finite (ℤ[ω] ⧸ Ideal.span {π}) := Nat.finite_of_card_ne_zero (by
    rw [hcard]; have := natAbs_norm_mod_three hπ h3; omega)
  have hne : mk α ≠ 0 := by
    intro h; apply hα; rw [← sub_zero α, ← hmk, map_zero]; exact h
  have hunits : Nat.card (ℤ[ω] ⧸ Ideal.span {π})ˣ = 3 * cexp π := by
    rw [hk, ← hcard, Nat.card_units]
  constructor
  · intro h1
    obtain ⟨-, hd⟩ := cubicChar_spec hπ h3 hα
    rw [h1, ← hmk, map_pow, map_one] at hd
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ℤ[ω] ⧸ Ideal.span {π})ˣ)
    let a : (ℤ[ω] ⧸ Ideal.span {π})ˣ := Units.mk0 (mk α) hne
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hg a)
    have hog : orderOf g = 3 * cexp π := by
      rw [← hunits, orderOf_eq_card_of_forall_mem_zpowers hg]
    have hak : a ^ cexp π = 1 := by ext; simp [a, hd]
    rw [← hm, ← zpow_natCast, ← zpow_mul, ← orderOf_dvd_iff_zpow_eq_one, hog] at hak
    have h4 : (3 : ℤ) ∣ m := by
      obtain ⟨c, hc⟩ := hak
      refine ⟨c, ?_⟩
      have : (cexp π : ℤ) * m = cexp π * (3 * c) := by push_cast at hc; linarith
      exact mul_left_cancel₀ (by exact_mod_cast hq0.ne') this
    obtain ⟨c, rfl⟩ := h4
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective ((g ^ c : (ℤ[ω] ⧸ Ideal.span {π})ˣ) :
      ℤ[ω] ⧸ Ideal.span {π})
    refine ⟨x, (hmk _ _).1 ?_⟩
    have hx' : mk x = ((g ^ c : (ℤ[ω] ⧸ Ideal.span {π})ˣ) : ℤ[ω] ⧸ Ideal.span {π}) := hx
    rw [map_pow, hx', ← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul]
    have : g ^ (c * ((3 : ℕ) : ℤ)) = a := by rw [← hm]; congr 1; push_cast; ring
    rw [this]; rfl
  · rintro ⟨x, hx⟩
    refine cubicChar_eq_of_dvd hπ h3 hα (one_pow 3) ?_
    rw [← hmk] at hx ⊢
    rw [map_pow] at hx
    have hx0 : mk x ≠ 0 := by
      intro h; rw [h, zero_pow (by norm_num)] at hx; exact hne hx.symm
    letI := Fintype.ofFinite (ℤ[ω] ⧸ Ideal.span {π})
    rw [map_pow, map_one, ← hx, ← pow_mul, hk, ← hcard, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one _ hx0

lemma star_eq_sq_of_pow_three {u : ℤ[ω]} (hu : u ^ 3 = 1) : star u = u ^ 2 := by
  rcases pow_three_eq_one_iff.1 hu with rfl | rfl | rfl
  · simp
  · rw [star_omega]
  · rw [star_pow, star_omega]

/-- **Proposition 9.3.4 (a).** `conj χ_π(α) = χ_π(α)² = χ_π(α²)`. -/
@[kb "irelandrosen1990" "Prop 9.3.4 (a), p. 124"]
theorem star_cubicChar {π : ℤ[ω]} (hπ : Prime π) (h3 : (norm π).natAbs ≠ 3) (α : ℤ[ω]) :
    star (cubicChar π α) = cubicChar π α ^ 2 ∧ cubicChar π α ^ 2 = cubicChar π (α ^ 2) := by
  refine ⟨?_, (cubicChar_pow hπ h3 α 2).symm⟩
  by_cases hα : π ∣ α
  · rw [cubicChar_of_dvd hα]; simp
  · exact star_eq_sq_of_pow_three (cubicChar_spec hπ h3 hα).1

lemma prime_star {π : ℤ[ω]} (hπ : Prime π) : Prime (star π) :=
  (MulEquiv.prime_iff (starRingAut (R := ℤ[ω])).toMulEquiv).2 hπ

lemma star_dvd_star_iff {α β : ℤ[ω]} : star α ∣ star β ↔ α ∣ β := by
  constructor
  · intro h; simpa [starRingEnd_apply] using map_dvd (starRingEnd ℤ[ω]) h
  · intro h; exact map_dvd (starRingEnd ℤ[ω]) h

/-- **Proposition 9.3.4 (b).** `χ_π̄(ᾱ) = conj χ_π(α)`. -/
@[kb "irelandrosen1990" "Prop 9.3.4 (b), p. 124"]
theorem cubicChar_star {π : ℤ[ω]} (hπ : Prime π) (h3 : (norm π).natAbs ≠ 3) (α : ℤ[ω]) :
    cubicChar (star π) (star α) = star (cubicChar π α) := by
  by_cases hα : π ∣ α
  · rw [cubicChar_of_dvd hα, cubicChar_of_dvd (star_dvd_star_iff.2 hα), star_zero]
  obtain ⟨hu, hd⟩ := cubicChar_spec hπ h3 hα
  have h3' : (norm (star π)).natAbs ≠ 3 := by rwa [natAbs_norm_star]
  refine cubicChar_eq_of_dvd (prime_star hπ) h3' (fun h => hα (star_dvd_star_iff.1 h))
    (by rw [← star_pow, hu, star_one]) ?_
  rw [cexp_star, ← star_pow, ← star_sub]; exact star_dvd_star_iff.2 hd

lemma natAbs_norm_natCast_eq {q : ℕ} : (norm (q : ℤ[ω])).natAbs = q ^ 2 := by
  rw [QuadraticAlgebra.norm_natCast]; simp [Int.natAbs_pow]

lemma natAbs_norm_natCast_ne_three {q : ℕ} (hq : q.Prime) :
    (norm (q : ℤ[ω])).natAbs ≠ 3 := by
  rw [natAbs_norm_natCast_eq]; nlinarith [hq.two_le]

/-- **Corollary to Proposition 9.3.4.** For a rational prime `q ≡ 2 (mod 3)`,
`χ_q(ᾱ) = χ_q(α²)`, and `χ_q(n) = 1` for a rational integer `n` prime to `q`. -/
@[kb "irelandrosen1990" "Prop 9.3.4, Cor, p. 124"]
theorem cubicChar_natCast_star {q : ℕ} (hq : q.Prime) (hq3 : q % 3 = 2) (α : ℤ[ω]) :
    cubicChar q (star α) = cubicChar q (α ^ 2) := by
  have hπ := prime_natCast_of_mod_three_eq_two hq hq3
  have h3 := natAbs_norm_natCast_ne_three hq
  have := cubicChar_star hπ h3 α
  rw [star_natCast] at this
  rw [this, (star_cubicChar hπ h3 α).1, (star_cubicChar hπ h3 α).2]

@[kb "irelandrosen1990" "Prop 9.3.4, Cor, p. 124"]
theorem cubicChar_natCast_intCast {q : ℕ} (hq : q.Prime) (hq3 : q % 3 = 2) {n : ℤ}
    (hn : ¬ (q : ℤ) ∣ n) : cubicChar q n = 1 := by
  have hπ := prime_natCast_of_mod_three_eq_two hq hq3
  have h3 := natAbs_norm_natCast_ne_three hq
  have hdvd : ¬ (q : ℤ[ω]) ∣ (n : ℤ[ω]) := by
    rintro ⟨x, hx⟩
    have := congrArg QuadraticAlgebra.re hx
    simp at this
    exact hn ⟨x.re, this⟩
  have h1 := cubicChar_star hπ h3 (n : ℤ[ω])
  rw [star_natCast, star_intCast] at h1
  have h2 := star_eq_sq_of_pow_three (cubicChar_spec hπ h3 hdvd).1
  rw [← h1] at h2
  have h4 := (cubicChar_spec hπ h3 hdvd).1
  linear_combination (cubicChar (q : ℤ[ω]) n + 1) * h2 + h4

/-- **Remark (b) after Theorem 1.** `χ_π(-1) = 1`, and `χ_π(ω) = ω ^ ((N π - 1) / 3)`. -/
@[kb "irelandrosen1990" "Ch. 9, §3, remark (b) after Theorem 1, p. 124"]
theorem cubicChar_neg_one {π : ℤ[ω]} (hπ : Prime π) (h3 : (norm π).natAbs ≠ 3) :
    cubicChar π (-1) = 1 := by
  have hn : ¬ π ∣ (-1 : ℤ[ω]) := fun h => hπ.not_isUnit (isUnit_of_dvd_one (dvd_neg.1 h))
  have h1 := cubicChar_mul hπ h3 (-1) (-1)
  rw [show (-1 : ℤ[ω]) * -1 = 1 by ring, cubicChar_one hπ h3] at h1
  have h4 := (cubicChar_spec hπ h3 hn).1
  linear_combination h4 + cubicChar π (-1) * h1

@[kb "irelandrosen1990" "Ch. 9, §3, remark (b) after Theorem 1, p. 124"]
theorem cubicChar_omega {π : ℤ[ω]} (hπ : Prime π) (h3 : (norm π).natAbs ≠ 3) :
    cubicChar π omega = omega ^ cexp π := by
  exact cubicChar_eq_of_dvd hπ h3 (fun h => hπ.not_isUnit (isUnit_of_dvd_unit h isUnit_omega))
    (omega_pow_cube _) (by simp)

end Eisenstein

end NTKB.IrelandRosen
