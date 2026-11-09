/-
Ireland–Rosen, Chapter 9, §8: the generalized quartic residue symbol.
-/
import NTKB.IrelandRosen.R3.QuarticChar

/-!
# The generalized quartic residue symbol `χ_α(β)`

Ireland–Rosen, Chapter 9, §8, Definition after Proposition 9.8.4: for a nonunit `α` prime to
`1 + i`, write `α = ∏ λᵢ` with `λᵢ` irreducible and put `χ_α(β) = ∏ χ_{λᵢ}(β)`.
We define `quarticSymbol α β` with Mathlib's factorization `UniqueFactorizationMonoid.factors α`
and prove that any factorization into irreducibles gives the same product
(`quarticSymbol_eq_prod`), which is the book's well-definedness remark. Then:

* multiplicativity in both arguments, invariance under congruences and associates, conjugation;
* Proposition 9.8.5: `χ_a(α) = 1` for rational integers `α` and odd `a` prime to `α`;
* Proposition 9.8.6: `χ_n(i) = (-1) ^ ((n - 1) / 4)` for rational integers `n ≡ 1 (mod 4)`.
-/

namespace NTKB.IrelandRosen

open Zsqrtd UniqueFactorizationMonoid

local notation "ℤ[i]" => GaussianInt

namespace Gaussian

/-- **Definition (§8).** The generalized quartic residue symbol `χ_α(β) = ∏ χ_{λᵢ}(β)` over the
irreducible factors `λᵢ` of `α`. -/
@[kb "irelandrosen1990" "Ch. 9, §8, Definition (generalized symbol), p. 133"]
noncomputable def quarticSymbol (α β : ℤ[i]) : ℤ[i] :=
  ((factors α).map (fun ρ => quarticChar ρ β)).prod

lemma prod_map_eq_of_rel {s t : Multiset ℤ[i]} (h : Multiset.Rel Associated s t)
    {f : ℤ[i] → ℤ[i]} (hf : ∀ x y, Associated x y → f x = f y) :
    (s.map f).prod = (t.map f).prod := by
  have : Multiset.Rel (· = ·) (s.map f) (t.map f) :=
    Multiset.rel_map.2 (h.mono fun x _ y _ hxy => hf x y hxy)
  rw [Multiset.rel_eq] at this; rw [this]

lemma quarticChar_resp (β : ℤ[i]) :
    ∀ x y : ℤ[i], Associated x y → quarticChar x β = quarticChar y β :=
  fun _ _ h => congrFun (quarticChar_of_associated h) β

/-- The symbol does not depend on the factorization: for any multiset `s` of irreducibles with
product associate to `α`, `χ_α(β) = ∏_{λ ∈ s} χ_λ(β)`. -/
@[kb "irelandrosen1990" "Ch. 9, §8, Definition (generalized symbol, well defined), p. 133"]
theorem quarticSymbol_eq_prod {α : ℤ[i]} (s : Multiset ℤ[i]) (hs : ∀ x ∈ s, Irreducible x)
    (h : Associated s.prod α) (β : ℤ[i]) :
    quarticSymbol α β = (s.map (fun ρ => quarticChar ρ β)).prod := by
  have hs0 : s.prod ≠ 0 := by
    rw [Ne, Multiset.prod_eq_zero_iff]; intro h0; exact (hs 0 h0).ne_zero rfl
  have hα0 : α ≠ 0 := fun h0 => hs0 (by rw [h0] at h; exact h.eq_zero_iff.2 rfl)
  have hrel := factors_unique irreducible_of_factor hs ((factors_prod hα0).trans h.symm)
  exact prod_map_eq_of_rel hrel (quarticChar_resp β)

lemma quarticSymbol_of_isUnit {α : ℤ[i]} (hα : IsUnit α) (β : ℤ[i]) : quarticSymbol α β = 1 := by
  rw [quarticSymbol, factors_of_isUnit hα]; simp

lemma quarticSymbol_one (β : ℤ[i]) : quarticSymbol 1 β = 1 := quarticSymbol_of_isUnit isUnit_one β

lemma quarticSymbol_of_irreducible {π : ℤ[i]} (hπ : Irreducible π) (β : ℤ[i]) :
    quarticSymbol π β = quarticChar π β := by
  rw [quarticSymbol_eq_prod {π} (by simpa using hπ) (by simp) β]; simp

lemma quarticSymbol_of_associated {α α' : ℤ[i]} (h : Associated α α') :
    quarticSymbol α = quarticSymbol α' := by
  funext β
  exact prod_map_eq_of_rel (factors_rel_of_associated h) (quarticChar_resp β)

/-- Multiplicativity in the upper argument: `χ_{αα'}(β) = χ_α(β) χ_α'(β)`. -/
theorem quarticSymbol_mul_left {α α' : ℤ[i]} (hα : α ≠ 0) (hα' : α' ≠ 0) (β : ℤ[i]) :
    quarticSymbol (α * α') β = quarticSymbol α β * quarticSymbol α' β := by
  rw [quarticSymbol, prod_map_eq_of_rel (factors_mul hα hα') (quarticChar_resp β),
    Multiset.map_add, Multiset.prod_add]; rfl

lemma quarticSymbol_neg (α β : ℤ[i]) : quarticSymbol (-α) β = quarticSymbol α β := by
  rw [quarticSymbol_of_associated (Associated.neg_left (Associated.refl α))]

lemma natAbs_norm_ne_two_of_mem_factors {α ρ : ℤ[i]} (hα : ¬ onePlusI ∣ α)
    (hρ : ρ ∈ factors α) : ρ.norm.natAbs ≠ 2 := by
  have hirr := irreducible_of_factor ρ hρ
  rw [natAbs_norm_ne_two_iff hirr]
  intro h; exact hα (h.symm.dvd.trans (dvd_of_mem_factors hρ))

/-- Multiplicativity in the lower argument (for `α` prime to `1 + i`). -/
theorem quarticSymbol_mul_right {α : ℤ[i]} (hα : ¬ onePlusI ∣ α) (β γ : ℤ[i]) :
    quarticSymbol α (β * γ) = quarticSymbol α β * quarticSymbol α γ := by
  unfold quarticSymbol
  rw [← Multiset.prod_map_mul]
  congr 1
  refine Multiset.map_congr rfl fun ρ hρ => ?_
  exact quarticChar_mul (irreducible_of_factor ρ hρ) (natAbs_norm_ne_two_of_mem_factors hα hρ) β γ

lemma quarticSymbol_pow_right {α : ℤ[i]} (hα : ¬ onePlusI ∣ α) (β : ℤ[i]) (n : ℕ) :
    quarticSymbol α (β ^ n) = quarticSymbol α β ^ n := by
  induction n with
  | zero =>
    simp only [pow_zero]
    unfold quarticSymbol
    rw [Multiset.prod_eq_one]
    intro x hx
    obtain ⟨ρ, hρ, rfl⟩ := Multiset.mem_map.1 hx
    exact quarticChar_one (irreducible_of_factor ρ hρ) (natAbs_norm_ne_two_of_mem_factors hα hρ)
  | succ n ih => rw [pow_succ, quarticSymbol_mul_right hα, ih, pow_succ]

/-- `χ_α(β) = χ_α(γ)` whenever `β ≡ γ (mod α)`. -/
theorem quarticSymbol_congr {α β γ : ℤ[i]} (h : α ∣ β - γ) :
    quarticSymbol α β = quarticSymbol α γ := by
  unfold quarticSymbol
  congr 1
  exact Multiset.map_congr rfl fun ρ hρ => quarticChar_congr ((dvd_of_mem_factors hρ).trans h)

lemma star_multiset_prod (s : Multiset ℤ[i]) : star s.prod = (s.map star).prod := by
  simpa [starRingEnd_apply] using map_multiset_prod (starRingEnd ℤ[i]) s

/-- Conjugation: `χ_ᾱ(β̄) = conj χ_α(β)`. -/
theorem quarticSymbol_star {α : ℤ[i]} (hα : ¬ onePlusI ∣ α) (β : ℤ[i]) :
    quarticSymbol (star α) (star β) = star (quarticSymbol α β) := by
  by_cases h0 : α = 0
  · exact absurd (h0 ▸ dvd_zero _) hα
  have hs : ∀ x ∈ (factors α).map star, Irreducible x := by
    intro x hx; obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hx
    exact irreducible_star (irreducible_of_factor y hy)
  have hprod : Associated ((factors α).map star).prod (star α) := by
    obtain ⟨u, hu⟩ := factors_prod h0
    refine ⟨⟨star (u : ℤ[i]), star ((u⁻¹ : ℤ[i]ˣ) : ℤ[i]), ?_, ?_⟩, ?_⟩
    · rw [← star_mul', Units.mul_inv, star_one]
    · rw [← star_mul', Units.inv_mul, star_one]
    · simp only [Units.val_mk]
      conv_rhs => rw [← hu]
      rw [star_mul', star_multiset_prod]
  rw [quarticSymbol_eq_prod _ hs hprod, quarticSymbol, Multiset.map_map]
  rw [star_multiset_prod, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun ρ hρ => ?_
  exact quarticChar_star (irreducible_of_factor ρ hρ) (natAbs_norm_ne_two_of_mem_factors hα hρ) β

/-- For `α` prime to `1 + i` and to `β`, `χ_α(β)` is a unit. -/
theorem isUnit_quarticSymbol {α β : ℤ[i]} (hα : ¬ onePlusI ∣ α) (h : IsCoprime α β) :
    IsUnit (quarticSymbol α β) := by
  unfold quarticSymbol
  refine multiset_prod_isUnit _ fun x hx => ?_
  obtain ⟨ρ, hρ, rfl⟩ := Multiset.mem_map.1 hx
  have hirr := irreducible_of_factor ρ hρ
  refine (quarticChar_spec hirr (natAbs_norm_ne_two_of_mem_factors hα hρ) ?_).1
  intro hβ
  exact hirr.not_isUnit ((h.of_isCoprime_of_dvd_left (dvd_of_mem_factors hρ)).isUnit_of_dvd' dvd_rfl hβ)

lemma unit_mul_star {u : ℤ[i]} (hu : IsUnit u) : u * star u = 1 := by
  rw [← Zsqrtd.norm_eq_mul_conj, (isUnit_iff_norm_eq_one).1 hu]; rfl

lemma star_intCast (n : ℤ) : star (n : ℤ[i]) = n := by ext <;> simp

/-! ### Proposition 9.8.5 -/

lemma quarticSymbol_natCast_intCast_aux (α : ℤ) :
    ∀ n : ℕ, Odd n → IsCoprime (n : ℤ) α → quarticSymbol (n : ℤ[i]) (α : ℤ[i]) = 1 := by
  intro n
  induction n using Nat.recOnMul with
  | zero => intro h; simp at h
  | one => intro _ _; simpa using quarticSymbol_one _
  | prime p hp =>
    intro hodd hcop
    have hpα : ¬ (p : ℤ) ∣ α := fun h =>
      (Nat.prime_iff_prime_int.1 hp).not_unit (hcop.isUnit_of_dvd' dvd_rfl h)
    rcases Nat.odd_mod_four_iff.1 (by simpa [Nat.odd_iff] using hodd) with h1 | h3
    · obtain ⟨π, hπ, hpπ, -⟩ := exists_irreducible_eq_mul_star hp h1
      have hπ0 := hπ.ne_zero
      have hs0 : star π ≠ 0 := fun h => hπ0 (by simpa using congrArg star h)
      have hNπ : π.norm.natAbs = p := by
        have := congrArg (fun x : ℤ[i] => x.norm.natAbs) hpπ
        simp only [natAbs_norm_natCast, natAbs_norm_mul, natAbs_norm_star] at this
        exact Nat.pow_left_injective two_ne_zero (show π.norm.natAbs ^ 2 = p ^ 2 by rw [this, sq])
      have h2 : π.norm.natAbs ≠ 2 := by omega
      have hπα : ¬ π ∣ (α : ℤ[i]) := by
        intro h
        have := norm_dvd_norm h
        rw [hNπ, natAbs_norm_intCast] at this
        exact hpα (Int.natCast_dvd.2 (hp.dvd_of_dvd_pow this))
      rw [hpπ, quarticSymbol_mul_left hπ0 hs0, quarticSymbol_of_irreducible hπ,
        quarticSymbol_of_irreducible (irreducible_star hπ), ← star_intCast α,
        quarticChar_star hπ h2, star_intCast]
      exact unit_mul_star (quarticChar_spec hπ h2 hπα).1
    · haveI := Fact.mk hp
      have hirr : Irreducible (p : ℤ[i]) :=
        (GaussianInt.prime_of_nat_prime_of_mod_four_eq_three p h3).irreducible
      rw [quarticSymbol_of_irreducible hirr]
      exact quarticChar_natCast_intCast hp h3 hpα
  | mul a b iha ihb =>
    intro hodd hcop
    rw [Nat.odd_mul] at hodd
    push_cast at hcop ⊢
    have ha0 : (a : ℤ[i]) ≠ 0 := by
      rw [Ne, Nat.cast_eq_zero]; rintro rfl; simp at hodd
    have hb0 : (b : ℤ[i]) ≠ 0 := by
      rw [Ne, Nat.cast_eq_zero]; rintro rfl; simp at hodd
    rw [quarticSymbol_mul_left ha0 hb0, iha hodd.1 (IsCoprime.of_mul_left_left hcop),
      ihb hodd.2 (IsCoprime.of_mul_left_right hcop), one_mul]

lemma associated_intCast_natAbs (a : ℤ) : Associated (a : ℤ[i]) ((a.natAbs : ℕ) : ℤ[i]) := by
  rcases Int.natAbs_eq a with h | h
  · rw [← Int.cast_natCast, ← h]
  · conv_lhs => rw [h]
    rw [Int.cast_neg, Int.cast_natCast]
    exact (Associated.refl _).neg_left

/-- **Proposition 9.8.5.** Let `α ≠ 0` and `a` be rational integers, `a` odd and prime to `α`.
Then `χ_a(α) = 1`. -/
@[kb "irelandrosen1990" "Prop 9.8.5, p. 133"]
theorem quarticSymbol_intCast_intCast {a α : ℤ} (ha : Odd a) (hcop : IsCoprime a α) :
    quarticSymbol (a : ℤ[i]) (α : ℤ[i]) = 1 := by
  rw [quarticSymbol_of_associated (associated_intCast_natAbs a)]
  refine quarticSymbol_natCast_intCast_aux α _ (by simpa [Int.natAbs_odd] using ha) ?_
  rcases Int.natAbs_eq a with h | h
  · rwa [← h]
  · rw [h] at hcop; exact (IsCoprime.neg_left_iff _ _).1 hcop

/-! ### Proposition 9.8.6 -/

/-- The integer `±m ≡ 1 (mod 4)` attached to an odd `m`. -/
def normOdd (m : ℤ) : ℤ := if m % 4 = 1 then m else -m

lemma normOdd_mod {m : ℤ} (hm : m % 2 = 1) : normOdd m % 4 = 1 := by
  unfold normOdd; split_ifs <;> omega

lemma normOdd_mul {a b : ℤ} (ha : a % 2 = 1) (hb : b % 2 = 1) :
    normOdd (a * b) = normOdd a * normOdd b := by
  unfold normOdd
  have h1 : (a * b) % 4 = ((a % 4) * (b % 4)) % 4 := Int.mul_emod a b 4
  rcases (by omega : a % 4 = 1 ∨ a % 4 = 3) with ha4 | ha4 <;>
  rcases (by omega : b % 4 = 1 ∨ b % 4 = 3) with hb4 | hb4 <;>
  simp only [ha4, hb4] at h1 ⊢ <;> norm_num at h1 ⊢ <;> simp [h1] <;> ring

lemma negOnePow_div_four_mul {a b : ℤ} (ha : a % 4 = 1) (hb : b % 4 = 1) :
    ((a * b - 1) / 4).negOnePow = ((a - 1) / 4).negOnePow * ((b - 1) / 4).negOnePow := by
  obtain ⟨x, rfl⟩ : ∃ x, a = 4 * x + 1 := ⟨a / 4, by omega⟩
  obtain ⟨y, rfl⟩ : ∃ y, b = 4 * y + 1 := ⟨b / 4, by omega⟩
  have e : ((4 * x + 1) * (4 * y + 1) - 1) / 4 = 2 * (2 * x * y) + (x + y) := by
    rw [show (4 * x + 1) * (4 * y + 1) - 1 = 4 * (2 * (2 * x * y) + (x + y)) by ring]; omega
  rw [e, Int.negOnePow_add, Int.negOnePow_two_mul, one_mul, Int.negOnePow_add]
  congr 1 <;> congr 1 <;> omega

lemma I_pow_two_mul (m : ℕ) : I ^ (2 * m) = (((m : ℤ).negOnePow : ℤ) : ℤ[i]) := by
  rw [pow_mul, I_sq, Int.cast_negOnePow_natCast]

lemma quarticSymbol_natCast_I_aux :
    ∀ n : ℕ, Odd n → quarticSymbol (n : ℤ[i]) I =
      ((((normOdd n - 1) / 4).negOnePow : ℤ) : ℤ[i]) := by
  intro n
  induction n using Nat.recOnMul with
  | zero => intro h; simp at h
  | one => intro _; simp [quarticSymbol_one, normOdd]
  | prime p hp =>
    intro hodd
    have hp2 : p % 2 = 1 := Nat.odd_iff.1 hodd
    rcases Nat.odd_mod_four_iff.1 hp2 with h1 | h3
    · obtain ⟨π, hπ, hpπ, -⟩ := exists_irreducible_eq_mul_star hp h1
      have hπ0 := hπ.ne_zero
      have hs0 : star π ≠ 0 := fun h => hπ0 (by simpa using congrArg star h)
      have hNπ : π.norm.natAbs = p := by
        have := congrArg (fun x : ℤ[i] => x.norm.natAbs) hpπ
        simp only [natAbs_norm_natCast, natAbs_norm_mul, natAbs_norm_star] at this
        exact Nat.pow_left_injective two_ne_zero (show π.norm.natAbs ^ 2 = p ^ 2 by rw [this, sq])
      have h2 : π.norm.natAbs ≠ 2 := by omega
      have h2' : (star π).norm.natAbs ≠ 2 := by rwa [natAbs_norm_star]
      rw [hpπ, quarticSymbol_mul_left hπ0 hs0, quarticSymbol_of_irreducible hπ,
        quarticSymbol_of_irreducible (irreducible_star hπ), quarticChar_of_isUnit hπ h2 isUnit_I,
        quarticChar_of_isUnit (irreducible_star hπ) h2' isUnit_I, qexp_star, ← pow_add, ← two_mul,
        I_pow_two_mul]
      have : normOdd (p : ℤ) = p := by unfold normOdd; rw [if_pos (by omega)]
      rw [this]
      congr 3
      rw [qexp, hNπ]; omega
    · haveI := Fact.mk hp
      have hirr : Irreducible (p : ℤ[i]) :=
        (GaussianInt.prime_of_nat_prime_of_mod_four_eq_three p h3).irreducible
      have h2 : (p : ℤ[i]).norm.natAbs ≠ 2 := by rw [natAbs_norm_natCast]; nlinarith [hp.two_le]
      rw [quarticSymbol_of_irreducible hirr, quarticChar_of_isUnit hirr h2 isUnit_I]
      have : normOdd (p : ℤ) = -p := by unfold normOdd; rw [if_neg (by omega)]
      rw [this]
      obtain ⟨t, rfl⟩ : ∃ t, p = 4 * t + 3 := ⟨p / 4, by omega⟩
      have hq : qexp ((4 * t + 3 : ℕ) : ℤ[i]) = 2 * (2 * t ^ 2 + 3 * t + 1) := by
        rw [qexp, natAbs_norm_natCast]
        have : (4 * t + 3) ^ 2 - 1 = 4 * (2 * (2 * t ^ 2 + 3 * t + 1)) := by
          rw [Nat.sub_eq_iff_eq_add (pow_pos (by omega : 0 < 4 * t + 3) 2)]; ring
        rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
      rw [hq, I_pow_two_mul]
      congr 2
      rw [Int.negOnePow_eq_iff]
      push_cast
      have : (-(4 * (t : ℤ) + 3) - 1) / 4 = -((t : ℤ) + 1) := by omega
      rw [this]
      have : Even (2 * ((t : ℤ) ^ 2) + 3 * t + 1 - -(t + 1)) := by
        refine ⟨(t : ℤ) ^ 2 + 2 * t + 1, by ring⟩
      exact this
  | mul a b iha ihb =>
    intro hodd
    rw [Nat.odd_mul] at hodd
    have ha0 : (a : ℤ[i]) ≠ 0 := by
      rw [Ne, Nat.cast_eq_zero]; rintro rfl; simp at hodd
    have hb0 : (b : ℤ[i]) ≠ 0 := by
      rw [Ne, Nat.cast_eq_zero]; rintro rfl; simp at hodd
    have ha2 : (a : ℤ) % 2 = 1 := by have := Nat.odd_iff.1 hodd.1; omega
    have hb2 : (b : ℤ) % 2 = 1 := by have := Nat.odd_iff.1 hodd.2; omega
    push_cast
    rw [quarticSymbol_mul_left ha0 hb0, iha hodd.1, ihb hodd.2, normOdd_mul ha2 hb2,
      negOnePow_div_four_mul (normOdd_mod ha2) (normOdd_mod hb2)]
    push_cast; ring

/-- **Proposition 9.8.6.** For a rational integer `n ≡ 1 (mod 4)`, `χ_n(i) = (-1) ^ ((n - 1) / 4)`
(the book assumes `n ≠ 1`; for `n = 1` both sides are `1`). -/
@[kb "irelandrosen1990" "Prop 9.8.6, p. 134"]
theorem quarticSymbol_intCast_I {n : ℤ} (hn : n % 4 = 1) :
    quarticSymbol (n : ℤ[i]) I = ((((n - 1) / 4).negOnePow : ℤ) : ℤ[i]) := by
  rw [quarticSymbol_of_associated (associated_intCast_natAbs n),
    quarticSymbol_natCast_I_aux _ (by rw [Int.natAbs_odd]; exact Int.odd_iff.2 (by omega))]
  congr 4
  unfold normOdd
  rcases Int.natAbs_eq n with h | h
  · rw [← h, if_pos hn]
  · rw [show ((n.natAbs : ℕ) : ℤ) = -n by omega, if_neg (by omega), neg_neg]

end Gaussian

end NTKB.IrelandRosen
