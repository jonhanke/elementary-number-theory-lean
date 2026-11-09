/-
Ireland–Rosen, Chapter 9, §9: the law of biquadratic reciprocity.
-/
import NTKB.IrelandRosen.R3.RationalPrimes

/-!
# The law of biquadratic reciprocity

Ireland–Rosen, Chapter 9, §9: Proposition 9.9.8 (a rational `a ≡ 1 (mod 4)` against a primary
`λ`), Proposition 9.9.9 (primitive primary elements) and Theorem 2 (the law of biquadratic
reciprocity), each derived from Propositions 9.9.6 and 9.9.7 by the book's formal arguments.

We write `(-1) ^ n` for integers `n` with Mathlib's `Int.negOnePow`, cast to `ℤ[i]`.
-/

namespace NTKB.IrelandRosen

open Zsqrtd UniqueFactorizationMonoid

local notation "ℤ[i]" => GaussianInt

namespace Gaussian

/-- The sign `(-1) ^ n` in `ℤ[i]`. -/
local notation "sgn " n => (((Int.negOnePow n : ℤˣ) : ℤ) : ℤ[i])

/-! ### Helpers -/

lemma quarticSymbol_one_right {α : ℤ[i]} (hα : ¬ onePlusI ∣ α) : quarticSymbol α 1 = 1 := by
  simpa using quarticSymbol_pow_right hα 1 0

lemma IsPrimary'.not_onePlusI_dvd' {α : ℤ[i]} (h : IsPrimary' α) : ¬ onePlusI ∣ α :=
  h.not_onePlusI_dvd

lemma odd_intCast_not_onePlusI_dvd {n : ℤ} (hn : Odd n) : ¬ onePlusI ∣ (n : ℤ[i]) := by
  rw [onePlusI_dvd_iff]; simp; rcases hn with ⟨k, rfl⟩; omega

lemma IsPrimary'.eq_one_of_isUnit' {α : ℤ[i]} (h : IsPrimary' α) (hu : IsUnit α) : α = 1 :=
  h.eq_one_of_isUnit hu

/-- A nonzero symbol forces coprimality. -/
lemma isCoprime_of_quarticSymbol_ne_zero {α β : ℤ[i]} (hα : ¬ onePlusI ∣ α)
    (h : quarticSymbol α β ≠ 0) : IsCoprime α β := by
  have hα0 : α ≠ 0 := fun h0 => hα (h0 ▸ dvd_zero _)
  refine isCoprime_of_irreducible_dvd (fun h' => hα0 h'.1) fun z hz hzα hzβ => h ?_
  obtain ⟨ρ, hρ, hzρ⟩ := exists_mem_factors_of_dvd hα0 hz hzα
  unfold quarticSymbol
  rw [Multiset.prod_eq_zero_iff]
  exact Multiset.mem_map.2 ⟨ρ, hρ, quarticChar_of_dvd (hzρ.symm.dvd.trans hzβ)⟩

lemma intCast_isCoprime_iff {a b : ℤ} : IsCoprime (a : ℤ[i]) (b : ℤ[i]) ↔ IsCoprime a b := by
  constructor
  · rintro ⟨u, v, h⟩
    refine ⟨u.re, v.re, ?_⟩
    have := congrArg Zsqrtd.re h
    simpa [Zsqrtd.re_mul] using this
  · intro h; simpa using h.map (Int.castRingHom ℤ[i])

lemma quarticSymbol_multiset_prod_right {α : ℤ[i]} (hα : ¬ onePlusI ∣ α) (s : Multiset ℤ[i]) :
    quarticSymbol α s.prod = (s.map (quarticSymbol α)).prod := by
  induction s using Multiset.induction_on with
  | empty => simpa using quarticSymbol_one_right hα
  | cons a s ih => rw [Multiset.prod_cons, quarticSymbol_mul_right hα, ih, Multiset.map_cons,
      Multiset.prod_cons]

lemma negOnePow_re_mul {α β : ℤ[i]} (hα : IsPrimary' α) (hβ : IsPrimary' β) :
    ((α * β).re - 1) / 2 % 2 = ((α.re - 1) / 2 + (β.re - 1) / 2) % 2 := by
  have h1 := (isPrimary'_iff α).1 hα
  have h2 := (isPrimary'_iff β).1 hβ
  obtain ⟨s, hs⟩ : ∃ s, α.re = 2 * s + 1 := ⟨α.re / 2, by omega⟩
  obtain ⟨t, ht⟩ : ∃ t, β.re = 2 * t + 1 := ⟨β.re / 2, by omega⟩
  obtain ⟨u, hu⟩ : ∃ u, α.im = 2 * u := ⟨α.im / 2, by omega⟩
  obtain ⟨v, hv⟩ : ∃ v, β.im = 2 * v := ⟨β.im / 2, by omega⟩
  rw [hs, hu] at h1; rw [ht, hv] at h2
  have hre : (α * β).re = 2 * (2 * s * t + s + t - 2 * u * v) + 1 := by
    rw [Zsqrtd.re_mul, hs, ht, hu, hv]; ring
  rw [hre, hs, ht]
  have e1 : (2 * (2 * s * t + s + t - 2 * u * v) + 1 - 1) / 2 = 2 * s * t + s + t - 2 * u * v := by
    omega
  have e2 : (2 * s + 1 - 1) / 2 = s := by omega
  have e3 : (2 * t + 1 - 1) / 2 = t := by omega
  rw [e1, e2, e3]
  -- `u ≡ s` and `v ≡ t (mod 2)` for primary elements
  have hus : (u - s) % 2 = 0 := by omega
  have hvt : (v - t) % 2 = 0 := by omega
  have : (2 * s * t - 2 * u * v) % 2 = 0 := by
    have : 2 * s * t - 2 * u * v = 2 * (s * t - u * v) := by ring
    omega
  omega

lemma IsPrimary'.mul_re_negOnePow {α β : ℤ[i]} (hα : IsPrimary' α) (hβ : IsPrimary' β) :
    (((α * β).re - 1) / 2).negOnePow = ((α.re - 1) / 2).negOnePow * ((β.re - 1) / 2).negOnePow := by
  rw [← Int.negOnePow_add, Int.negOnePow_eq_iff, Int.even_iff]
  have := negOnePow_re_mul hα hβ
  omega

lemma neg_one_pow_natAbs (n : ℤ) : (-1 : ℤ[i]) ^ n.natAbs = sgn n := by
  rcases Int.even_or_odd n with h | h
  · rw [Int.negOnePow_even _ h, (Int.natAbs_even.2 h).neg_one_pow]; simp
  · rw [Int.negOnePow_odd _ h, (Int.natAbs_odd.2 h).neg_one_pow]; simp

/-- The supplement for `-1` (Proposition 9.8.3 (d) for composite primary `γ`):
`χ_γ(-1) = (-1) ^ ((a - 1) / 2)` for primary `γ = a + b i`. -/
theorem IsPrimary'.quarticSymbol_neg_one {γ : ℤ[i]} (hγ : IsPrimary' γ) :
    quarticSymbol γ (-1) = sgn ((γ.re - 1) / 2) := by
  by_cases hu : IsUnit γ
  · rw [hγ.eq_one_of_isUnit hu, quarticSymbol_one]; simp
  obtain ⟨s, hs, hprod⟩ := IsPrimary.exists_multiset_prod_eq ⟨hu, hγ⟩
  rw [quarticSymbol_eq_prod s (fun x hx => (hs x hx).1) (by rw [hprod]) (-1)]
  subst hprod
  induction s using Multiset.induction_on with
  | empty => simp
  | cons ρ s ih =>
    have hρ := hs ρ (Multiset.mem_cons_self _ _)
    have hs' : ∀ x ∈ s, Irreducible x ∧ IsPrimary x := fun x hx => hs x (Multiset.mem_cons_of_mem hx)
    have hγs : IsPrimary' s.prod := isPrimary'_multiset_prod _ fun x hx => (hs' x hx).2.2
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons,
      hρ.2.quarticChar_neg_one hρ.1, neg_one_pow_natAbs, IsPrimary'.mul_re_negOnePow hρ.2.2 hγs]
    by_cases hsu : IsUnit s.prod
    · have h1 := hγs.eq_one_of_isUnit hsu
      have hs0 : s = 0 := by
        by_contra hne
        obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hne
        exact (hs' x hx).1.not_isUnit (isUnit_of_dvd_unit (Multiset.dvd_prod hx) hsu)
      subst hs0
      simp only [Multiset.map_zero, Multiset.prod_zero, mul_one, Zsqrtd.re_one, sub_self,
        Int.zero_ediv, Int.negOnePow_zero]
    · rw [ih hs' hγs hsu]; push_cast; ring

/-! ### Proposition 9.9.8 -/

/-- The prime step of Proposition 9.9.8: for a primary irreducible `ρ` and an odd rational prime
`r` with `ρ ∤ r`, writing `r* = ±r ≡ 1 (mod 4)`, `χ_{r*}(ρ) = χ_ρ(r*)`. -/
lemma quarticSymbol_normOdd_prime {ρ : ℤ[i]} (hρ : Irreducible ρ) (hP : IsPrimary ρ) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hρr : ¬ ρ ∣ (r : ℤ[i])) :
    quarticSymbol ((normOdd r : ℤ) : ℤ[i]) ρ = quarticChar ρ ((normOdd r : ℤ) : ℤ[i]) := by
  have hodd : r % 2 = 1 := hr.eq_two_or_odd.resolve_left hr2
  rcases hP.irreducible_cases hρ with ⟨hpρ, hp1⟩ | ⟨q, hq, hq3, rfl⟩
  · have hrp : r ≠ ρ.norm.natAbs := by
      intro h; apply hρr; rw [h]; exact dvd_natAbs_norm ρ
    rcases Nat.odd_mod_four_iff.1 hodd with h1 | h3
    · have : normOdd (r : ℤ) = r := by unfold normOdd; rw [if_pos (by omega)]
      rw [this, Int.cast_natCast]
      exact (quarticChar_natCast_eq_quarticSymbol hP hpρ hr h1 hrp).symm
    · have hn : normOdd (r : ℤ) = -r := by unfold normOdd; rw [if_neg (by omega)]
      haveI := Fact.mk hr
      have hirr : Irreducible (r : ℤ[i]) :=
        (GaussianInt.prime_of_nat_prime_of_mod_four_eq_three r h3).irreducible
      rw [hn, Int.cast_neg, Int.cast_natCast, quarticSymbol_neg, quarticSymbol_of_irreducible hirr]
      exact quarticChar_natCast_eq_quarticChar_neg hP hpρ hr h3
  · -- `ρ = -q` with `q ≡ 3 (mod 4)`
    have hqr : ¬ (q : ℤ) ∣ normOdd r := by
      intro h
      apply hρr
      have : (q : ℤ) ∣ r := by
        unfold normOdd at h; split_ifs at h
        · exact h
        · exact (dvd_neg).1 h
      have hqr : q = r := by
        have := Int.natCast_dvd_natCast.1 this
        exact (Nat.prime_dvd_prime_iff_eq hq hr).1 this
      rw [hqr]; exact neg_dvd.2 dvd_rfl
    have hodd' : Odd (normOdd r : ℤ) := by
      unfold normOdd; split_ifs
      · exact Int.odd_iff.2 (by omega)
      · exact (Int.odd_iff.2 (by omega)).neg
    rw [quarticChar_of_associated (Associated.neg_left (Associated.refl _)),
      quarticChar_natCast_intCast hq hq3 hqr,
      show -(q : ℤ[i]) = ((-(q : ℤ) : ℤ) : ℤ[i]) by push_cast; ring]
    refine quarticSymbol_intCast_intCast hodd' ?_
    rw [IsCoprime.neg_right_iff]
    exact (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.1 hq)).2 hqr |>.symm

lemma quarticSymbol_normOdd_natCast {ρ : ℤ[i]} (hρ : Irreducible ρ) (hP : IsPrimary ρ) :
    ∀ n : ℕ, Odd n → ¬ ρ ∣ (n : ℤ[i]) →
      quarticSymbol ((normOdd n : ℤ) : ℤ[i]) ρ = quarticChar ρ ((normOdd n : ℤ) : ℤ[i]) := by
  have h2 : ρ.norm.natAbs ≠ 2 := by have := hP.2.natAbs_norm_mod_four; omega
  intro n
  induction n using Nat.recOnMul with
  | zero => intro h; exact absurd h (by decide)
  | one =>
    intro _ _
    have : normOdd ((1 : ℕ) : ℤ) = 1 := by decide
    rw [this, Int.cast_one, quarticSymbol_one, quarticChar_one hρ h2]
  | prime r hr =>
    intro hodd hρr
    have hr2 : r ≠ 2 := by rintro rfl; exact absurd hodd (by decide)
    exact quarticSymbol_normOdd_prime hρ hP hr hr2 hρr
  | mul a b iha ihb =>
    intro hodd hρab
    rw [Nat.odd_mul] at hodd
    rw [Nat.cast_mul] at hρab
    have hρa : ¬ ρ ∣ (a : ℤ[i]) := fun h => hρab (dvd_mul_of_dvd_left h _)
    have hρb : ¬ ρ ∣ (b : ℤ[i]) := fun h => hρab (dvd_mul_of_dvd_right h _)
    have ha2 : (a : ℤ) % 2 = 1 := by have := Nat.odd_iff.1 hodd.1; omega
    have hb2 : (b : ℤ) % 2 = 1 := by have := Nat.odd_iff.1 hodd.2; omega
    have hna0 : ((normOdd a : ℤ) : ℤ[i]) ≠ 0 := by
      rw [Ne, Int.cast_eq_zero]; unfold normOdd; split_ifs <;> omega
    have hnb0 : ((normOdd b : ℤ) : ℤ[i]) ≠ 0 := by
      rw [Ne, Int.cast_eq_zero]; unfold normOdd; split_ifs <;> omega
    push_cast
    rw [normOdd_mul ha2 hb2, Int.cast_mul, quarticSymbol_mul_left hna0 hnb0,
      quarticChar_mul hρ h2, iha hodd.1 hρa, ihb hodd.2 hρb]

lemma normOdd_natAbs {a : ℤ} (ha : a % 4 = 1) : normOdd (a.natAbs : ℤ) = a := by
  unfold normOdd
  rcases Int.natAbs_eq a with h | h
  · rw [← h, if_pos ha]
  · rw [show ((a.natAbs : ℕ) : ℤ) = -a by omega, if_neg (by omega), neg_neg]

/-- **Proposition 9.9.8.** Let `a ≡ 1 (mod 4)` be a rational integer and `λ` primary, prime to
`a`. Then `χ_a(λ) = χ_λ(a)`. -/
@[kb "irelandrosen1990" "Prop 9.9.8, p. 137"]
theorem quarticSymbol_intCast_comm {a : ℤ} (ha : a % 4 = 1) {μ : ℤ[i]} (hμ : IsPrimary' μ)
    (hcop : IsCoprime (a : ℤ[i]) μ) :
    quarticSymbol (a : ℤ[i]) μ = quarticSymbol μ (a : ℤ[i]) := by
  have haodd : Odd a := Int.odd_iff.2 (by omega)
  have ha2 := odd_intCast_not_onePlusI_dvd haodd
  by_cases hu : IsUnit μ
  · rw [hμ.eq_one_of_isUnit hu, quarticSymbol_one_right ha2, quarticSymbol_one]
  obtain ⟨s, hs, hprod⟩ := IsPrimary.exists_multiset_prod_eq ⟨hu, hμ⟩
  subst hprod
  rw [quarticSymbol_multiset_prod_right ha2,
    quarticSymbol_eq_prod s (fun x hx => (hs x hx).1) (Associated.refl _) (a : ℤ[i])]
  congr 1
  refine Multiset.map_congr rfl fun ρ hρ => ?_
  have hρa : ¬ ρ ∣ (a : ℤ[i]) := by
    intro h
    have hρμ : ρ ∣ s.prod := Multiset.dvd_prod hρ
    exact (hs ρ hρ).1.not_isUnit (hcop.isUnit_of_dvd' h hρμ)
  have hρn : ¬ ρ ∣ ((a.natAbs : ℕ) : ℤ[i]) := by
    intro h; exact hρa (h.trans (associated_intCast_natAbs a).symm.dvd)
  have := quarticSymbol_normOdd_natCast (hs ρ hρ).1 (hs ρ hρ).2 a.natAbs
    (by rw [Int.natAbs_odd]; exact haodd) hρn
  rwa [normOdd_natAbs ha] at this

/-! ### Proposition 9.9.9 -/

/-- Step 2 of the proof of 9.9.9: for primary `γ` and odd `n` prime to `γ`,
`χ_γ(n) = (-1) ^ (((a - 1) / 2) ((n - 1) / 2)) χ_{n*}(γ)` with `γ = a + b i` and `n* = ±n ≡ 1 (mod 4)`. -/
lemma quarticSymbol_intCast_eq_sgn_mul {γ : ℤ[i]} (hγ : IsPrimary' γ) {n : ℤ} (hn : Odd n)
    (hcop : IsCoprime (n : ℤ[i]) γ) :
    quarticSymbol γ n = (sgn (((γ.re - 1) / 2) * ((n - 1) / 2))) *
      quarticSymbol ((normOdd n : ℤ) : ℤ[i]) γ := by
  have hn2 : n % 2 = 1 := Int.odd_iff.1 hn
  rcases (by omega : n % 4 = 1 ∨ n % 4 = 3) with h1 | h3
  · have hN : normOdd n = n := by unfold normOdd; rw [if_pos h1]
    have he : Even ((γ.re - 1) / 2 * ((n - 1) / 2)) :=
      (Int.even_iff.2 (by omega : (n - 1) / 2 % 2 = 0)).mul_left _
    rw [hN, Int.negOnePow_even _ he, quarticSymbol_intCast_comm h1 hγ hcop]; simp
  · have hN : normOdd n = -n := by unfold normOdd; rw [if_neg (by omega)]
    have ho : Odd ((n - 1) / 2) := Int.odd_iff.2 (by omega)
    have hsgn : (((γ.re - 1) / 2) * ((n - 1) / 2)).negOnePow = ((γ.re - 1) / 2).negOnePow := by
      rw [Int.negOnePow_eq_iff]
      obtain ⟨k, hk⟩ := ho
      exact ⟨((γ.re - 1) / 2) * k, by rw [hk]; ring⟩
    have hcop' : IsCoprime ((-n : ℤ) : ℤ[i]) γ := by push_cast; exact (IsCoprime.neg_left_iff _ _).2 hcop
    rw [hN, hsgn, show (n : ℤ[i]) = (-1) * ((-n : ℤ) : ℤ[i]) by push_cast; ring,
      quarticSymbol_mul_right hγ.not_onePlusI_dvd, hγ.quarticSymbol_neg_one,
      quarticSymbol_intCast_comm (by omega) hγ hcop']

/-- Step 3 of the proof of 9.9.9: if `γ = a + b i` with `(a, b) = 1` and `a` odd, then
`χ_{a*}(γ) = (-1) ^ ((a* - 1) / 4)`. -/
lemma quarticSymbol_normOdd_re {γ : ℤ[i]} (hγ : IsCoprime γ.re γ.im) (hodd : Odd γ.re) :
    quarticSymbol ((normOdd γ.re : ℤ) : ℤ[i]) γ = sgn ((normOdd γ.re - 1) / 4) := by
  have h2 : γ.re % 2 = 1 := Int.odd_iff.1 hodd
  have hN4 := normOdd_mod h2
  have hdvd : ((normOdd γ.re : ℤ) : ℤ[i]) ∣ γ - (γ.im : ℤ[i]) * I := by
    have : γ - (γ.im : ℤ[i]) * I = (γ.re : ℤ[i]) := by ext <;> simp
    rw [this]
    unfold normOdd; split_ifs
    · exact dvd_rfl
    · rw [Int.cast_neg]; exact neg_dvd.2 dvd_rfl
  have hoddN : Odd (normOdd γ.re) := Int.odd_iff.2 (by omega)
  have hcopN : IsCoprime (normOdd γ.re) γ.im := by
    unfold normOdd; split_ifs
    · exact hγ
    · exact (IsCoprime.neg_left_iff _ _).2 hγ
  rw [quarticSymbol_congr hdvd, quarticSymbol_mul_right (odd_intCast_not_onePlusI_dvd hoddN),
    quarticSymbol_intCast_intCast hoddN hcopN, one_mul, quarticSymbol_intCast_I hN4]

lemma isCoprime_re_of_isCoprime_re_im {γ : ℤ[i]} (h : IsCoprime γ.re γ.im) :
    IsCoprime (γ.re : ℤ[i]) γ := by
  obtain ⟨u, v, huv⟩ := h
  refine ⟨(u : ℤ[i]) + (v : ℤ[i]) * I, -(v : ℤ[i]) * I, ?_⟩
  have e : (u : ℤ[i]) * γ.re + (v : ℤ[i]) * γ.im = 1 := by exact_mod_cast huv
  rw [← e]; ext <;> simp <;> ring

lemma isCoprime_of_isUnit_mul {α β x : ℤ[i]} (hα : ¬ onePlusI ∣ α)
    (h : IsUnit (quarticSymbol α x * β)) : IsCoprime α x :=
  isCoprime_of_quarticSymbol_ne_zero hα (left_ne_zero_of_mul (IsUnit.ne_zero h))

lemma sgn_mul_self (n : ℤ) : (sgn n) * (sgn n) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, ← Int.negOnePow_add,
    (Int.negOnePow_eq_one_iff _).2 ⟨n, rfl⟩]; simp

lemma normOdd_quarter_mul {x y : ℤ} (hx : x % 2 = 1) (hy : y % 2 = 1) :
    ((normOdd (x * y) - 1) / 4 - ((normOdd x - 1) / 4 + (normOdd y - 1) / 4)) % 2 = 0 := by
  have := negOnePow_div_four_mul (normOdd_mod hx) (normOdd_mod hy)
  rw [← normOdd_mul hx hy, ← Int.negOnePow_add, Int.negOnePow_eq_iff] at this
  obtain ⟨r, hr⟩ := this
  omega

/-- The parity identity behind Proposition 9.9.9 ("a simple exercise using Lemma 6"). -/
lemma parity_key {a b c d : ℤ} (ha : 4 ∣ a - 1 + b ∧ 4 ∣ a - 1 - b)
    (hc : 4 ∣ c - 1 + d ∧ 4 ∣ c - 1 - d) :
    Even ((a - 1) / 2 * ((a - 1) / 2) + (normOdd a - 1) / 4 +
      (a - 1) / 2 * ((a * c + b * d - 1) / 2) + (normOdd (a * c + b * d) - 1) / 4 +
      ((c - 1) / 2 * ((c - 1) / 2) + (normOdd c - 1) / 4 +
      (c - 1) / 2 * ((a * c + b * d - 1) / 2) + (a - 1) / 2 * ((c - 1) / 2))) := by
  have ha2 : a % 2 = 1 := by omega
  have hc2 : c % 2 = 1 := by omega
  have hT2 : (a * c + b * d) % 2 = 1 := by
    obtain ⟨b', hb'⟩ : ∃ b', b = 2 * b' := ⟨b / 2, by omega⟩
    rw [hb', Int.add_emod, Int.mul_emod a c, ha2, hc2]; simp [mul_assoc]
  have hac2 : (a * c) % 2 = 1 := by rw [Int.mul_emod, ha2, hc2]; rfl
  have h1 := normOdd_quarter_mul hac2 hT2
  have h2 := normOdd_quarter_mul ha2 hc2
  obtain ⟨α, hα⟩ : ∃ α, a = 2 * α + 1 := ⟨a / 2, by omega⟩
  obtain ⟨γ, hγ⟩ : ∃ γ, c = 2 * γ + 1 := ⟨c / 2, by omega⟩
  obtain ⟨u, hu⟩ : ∃ u, b = 2 * α + 4 * u := ⟨(b - 2 * α) / 4, by omega⟩
  obtain ⟨v, hv⟩ : ∃ v, d = 2 * γ + 4 * v := ⟨(d - 2 * γ) / 4, by omega⟩
  -- `a c T ≡ 1 (mod 4)` and the value of `(a c T - 1) / 4`
  have hacT : a * c * (a * c + b * d) - 1 = 4 * ((2 * α * γ + α + γ) * (2 * α * γ + α + γ + 1) +
      (2 * (2 * α * γ + α + γ) + 1) * (α + 2 * u) * (γ + 2 * v)) := by
    rw [hα, hγ, hu, hv]; ring
  have hN : normOdd (a * c * (a * c + b * d)) = a * c * (a * c + b * d) := by
    unfold normOdd; rw [if_pos (by omega)]
  rw [hN, hacT] at h1
  have hT1 : a * c + b * d - 1 = 2 * (2 * α * γ + α + γ + 2 * (α + 2 * u) * (γ + 2 * v)) := by
    rw [hα, hγ, hu, hv]; ring
  have ha1 : (a - 1) / 2 = α := by omega
  have hc1 : (c - 1) / 2 = γ := by omega
  have ht : (a * c + b * d - 1) / 2 = 2 * α * γ + α + γ + 2 * (α + 2 * u) * (γ + 2 * v) := by
    rw [hT1]; omega
  have hq : ∀ z : ℤ, (4 * z) / 4 = z := fun z => by omega
  rw [hq] at h1
  rw [ha1, hc1, ht]
  generalize (normOdd a - 1) / 4 = X at *
  generalize (normOdd c - 1) / 4 = Y at *
  generalize (normOdd (a * c + b * d) - 1) / 4 = Z at *
  generalize (normOdd (a * c) - 1) / 4 = W at *
  rw [Int.even_iff]
  have e : ∀ z : ℤ, z % 2 = 0 ↔ ((z : ZMod 2) = 0) := fun z => by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; omega
  rw [e] at h1 h2 ⊢
  push_cast at h1 h2 ⊢
  generalize (α : ZMod 2) = A at *
  generalize (γ : ZMod 2) = G at *
  generalize (u : ZMod 2) = U at *
  generalize (v : ZMod 2) = V at *
  generalize (X : ZMod 2) = X' at *
  generalize (Y : ZMod 2) = Y' at *
  generalize (Z : ZMod 2) = Z' at *
  generalize (W : ZMod 2) = W' at *
  revert A G U V X' Y' Z' W'
  decide

/-- **Proposition 9.9.9.** Let `π = a + b i` and `λ = c + d i` be relatively prime primary elements
(not necessarily irreducible) with `(a, b) = (c, d) = 1`. Then
`χ_π(λ) = χ_λ(π) (-1) ^ (((a - 1) / 2) ((c - 1) / 2))`. -/
@[kb "irelandrosen1990" "Prop 9.9.9, p. 137"]
theorem quarticSymbol_comm_of_isCoprime_re_im {π μ : ℤ[i]} (hπ : IsPrimary' π)
    (hμ : IsPrimary' μ) (hcop : IsCoprime π μ) (hab : IsCoprime π.re π.im)
    (hcd : IsCoprime μ.re μ.im) :
    quarticSymbol π μ = quarticSymbol μ π * sgn (((π.re - 1) / 2) * ((μ.re - 1) / 2)) := by
  set a := π.re with ha_def
  set b := π.im with hb_def
  set c := μ.re with hc_def
  set d := μ.im with hd_def
  have hπ2 := hπ.not_onePlusI_dvd
  have hμ2 := hμ.not_onePlusI_dvd
  have hPa := (isPrimary'_iff π).1 hπ
  have hPc := (isPrimary'_iff μ).1 hμ
  have haodd : Odd a := Int.odd_iff.2 (by omega)
  have hcodd : Odd c := Int.odd_iff.2 (by omega)
  have hTodd : Odd (a * c + b * d) := by
    obtain ⟨b', hb'⟩ : ∃ b', b = 2 * b' := ⟨b / 2, by omega⟩
    rw [hb']
    exact (haodd.mul hcodd).add_even ⟨b' * d, by ring⟩
  have hA := isUnit_quarticSymbol hπ2 hcop
  have hB := isUnit_quarticSymbol hμ2 hcop.symm
  -- the congruences `c π ≡ a c + b d (mod λ)` and `a λ ≡ a c + b d (mod π)`
  have e1 : quarticSymbol μ ((c : ℤ[i]) * π) = quarticSymbol μ ((a * c + b * d : ℤ) : ℤ[i]) :=
    quarticSymbol_congr ⟨(b : ℤ[i]) * I, by ext <;> simp [ha_def, hb_def, hc_def, hd_def] <;> ring⟩
  have e2 : quarticSymbol π ((a : ℤ[i]) * μ) = quarticSymbol π ((a * c + b * d : ℤ) : ℤ[i]) :=
    quarticSymbol_congr ⟨(d : ℤ[i]) * I, by ext <;> simp [ha_def, hb_def, hc_def, hd_def] <;> ring⟩
  rw [quarticSymbol_mul_right hμ2] at e1
  rw [quarticSymbol_mul_right hπ2] at e2
  -- coprimality
  have hcμ : IsCoprime (c : ℤ[i]) μ := isCoprime_re_of_isCoprime_re_im hcd
  have haπ : IsCoprime (a : ℤ[i]) π := isCoprime_re_of_isCoprime_re_im hab
  have hxc := isUnit_quarticSymbol hμ2 hcμ.symm
  have hxa := isUnit_quarticSymbol hπ2 haπ.symm
  have hTμ : IsCoprime μ ((a * c + b * d : ℤ) : ℤ[i]) :=
    isCoprime_of_quarticSymbol_ne_zero hμ2 (by rw [← e1]; exact (hxc.mul hB).ne_zero)
  have hTπ : IsCoprime π ((a * c + b * d : ℤ) : ℤ[i]) :=
    isCoprime_of_quarticSymbol_ne_zero hπ2 (by rw [← e2]; exact (hxa.mul hA).ne_zero)
  -- Steps 2 and 3
  have sxc := quarticSymbol_intCast_eq_sgn_mul hμ hcodd hcμ
  have sxa := quarticSymbol_intCast_eq_sgn_mul hπ haodd haπ
  have syμ := quarticSymbol_intCast_eq_sgn_mul hμ hTodd hTμ.symm
  have syπ := quarticSymbol_intCast_eq_sgn_mul hπ hTodd hTπ.symm
  rw [quarticSymbol_normOdd_re hcd hcodd] at sxc
  rw [quarticSymbol_normOdd_re hab haodd] at sxa
  -- Step 4: `χ_{T*}(π) conj χ_{T*}(λ) = χ_{T*}(i)`
  set N := normOdd (a * c + b * d) with hNdef
  have hT2 : (a * c + b * d) % 2 = 1 := Int.odd_iff.1 hTodd
  have hN4 := normOdd_mod hT2
  have hNodd : Odd N := Int.odd_iff.2 (by omega)
  have hN2 := odd_intCast_not_onePlusI_dvd hNodd
  have hNμ : IsCoprime (N : ℤ[i]) μ := by
    rw [hNdef]; unfold normOdd; split_ifs
    · exact hTμ.symm
    · rw [Int.cast_neg]; exact (IsCoprime.neg_left_iff _ _).2 hTμ.symm
  have hNπ : IsCoprime (N : ℤ[i]) π := by
    rw [hNdef]; unfold normOdd; split_ifs
    · exact hTπ.symm
    · rw [Int.cast_neg]; exact (IsCoprime.neg_left_iff _ _).2 hTπ.symm
  have hNμ' : IsCoprime (N : ℤ[i]) (star μ) := by
    have := hNμ.map (starRingEnd ℤ[i])
    simpa [starRingEnd_apply, star_intCast] using this
  have hdvdN : (N : ℤ[i]) ∣ π * star μ - ((b * c - a * d : ℤ) : ℤ[i]) * I := by
    have : π * star μ - ((b * c - a * d : ℤ) : ℤ[i]) * I = ((a * c + b * d : ℤ) : ℤ[i]) := by
      ext <;> simp [ha_def, hb_def, hc_def, hd_def] <;> ring
    rw [this, hNdef]; unfold normOdd; split_ifs
    · exact dvd_rfl
    · rw [Int.cast_neg]; exact neg_dvd.2 dvd_rfl
  have hU := isUnit_quarticSymbol hN2 (hNπ.mul_right hNμ')
  rw [quarticSymbol_congr hdvdN, quarticSymbol_mul_right hN2] at hU
  have hcop' : IsCoprime N (b * c - a * d) :=
    intCast_isCoprime_iff.1 (isCoprime_of_isUnit_mul hN2 hU)
  set V := quarticSymbol (N : ℤ[i]) μ with hV
  set W := quarticSymbol (N : ℤ[i]) π with hW
  have hWV : W * star V = sgn ((N - 1) / 4) := by
    have h1 : quarticSymbol (N : ℤ[i]) (π * star μ) = W * star V := by
      rw [quarticSymbol_mul_right hN2, ← star_intCast N, quarticSymbol_star hN2, star_intCast]
    rw [← h1, quarticSymbol_congr hdvdN, quarticSymbol_mul_right hN2,
      quarticSymbol_intCast_intCast hNodd hcop', one_mul, quarticSymbol_intCast_I hN4]
  have hVu : IsUnit V := isUnit_quarticSymbol hN2 hNμ
  have hW' : W = (sgn ((N - 1) / 4)) * V := by
    rw [← hWV, mul_assoc, mul_comm (star V), unit_mul_star hVu, mul_one]
  -- the sign algebra
  rw [← ha_def] at sxa syπ
  rw [← hc_def] at sxc syμ
  have sadd : ∀ m n : ℤ, (sgn (m + n)) = (sgn m) * (sgn n) := fun m n => by
    rw [Int.negOnePow_add]; push_cast; ring
  rw [syπ, hW', sxa, ← sadd] at e2
  rw [syμ, sxc, ← sadd] at e1
  have hA' : quarticSymbol π μ = (sgn ((a - 1) / 2 * ((a - 1) / 2) + (normOdd a - 1) / 4 +
      ((a - 1) / 2 * ((a * c + b * d - 1) / 2) + (N - 1) / 4))) * V := by
    have hs := sgn_mul_self ((a - 1) / 2 * ((a - 1) / 2) + (normOdd a - 1) / 4)
    rw [sadd ((a - 1) / 2 * ((a - 1) / 2) + (normOdd a - 1) / 4)
      ((a - 1) / 2 * ((a * c + b * d - 1) / 2) + (N - 1) / 4),
      sadd ((a - 1) / 2 * ((a * c + b * d - 1) / 2)) ((N - 1) / 4)]
    linear_combination (sgn ((a - 1) / 2 * ((a - 1) / 2) + (normOdd a - 1) / 4)) * e2 -
      quarticSymbol π μ * hs
  have hB' : quarticSymbol μ π = (sgn ((c - 1) / 2 * ((c - 1) / 2) + (normOdd c - 1) / 4 +
      (c - 1) / 2 * ((a * c + b * d - 1) / 2))) * V := by
    have hs := sgn_mul_self ((c - 1) / 2 * ((c - 1) / 2) + (normOdd c - 1) / 4)
    rw [sadd ((c - 1) / 2 * ((c - 1) / 2) + (normOdd c - 1) / 4)
      ((c - 1) / 2 * ((a * c + b * d - 1) / 2))]
    linear_combination (sgn ((c - 1) / 2 * ((c - 1) / 2) + (normOdd c - 1) / 4)) * e1 -
      quarticSymbol μ π * hs
  rw [hA', hB', mul_right_comm, ← sadd]
  have key : ((a - 1) / 2 * ((a - 1) / 2) + (normOdd a - 1) / 4 +
      ((a - 1) / 2 * ((a * c + b * d - 1) / 2) + (N - 1) / 4)).negOnePow =
      ((c - 1) / 2 * ((c - 1) / 2) + (normOdd c - 1) / 4 +
      (c - 1) / 2 * ((a * c + b * d - 1) / 2) + (a - 1) / 2 * ((c - 1) / 2)).negOnePow := by
    rw [Int.negOnePow_eq_iff]
    have hpk := parity_key hPa hPc
    rw [← ha_def, ← hb_def, ← hc_def, ← hd_def, ← hNdef] at hpk
    obtain ⟨r, hr⟩ := hpk
    exact ⟨r - ((c - 1) / 2 * ((c - 1) / 2) + (normOdd c - 1) / 4 +
      (c - 1) / 2 * ((a * c + b * d - 1) / 2) + (a - 1) / 2 * ((c - 1) / 2)), by linarith⟩
  rw [key]

/-! ### Theorem 2: the law of biquadratic reciprocity -/

/-- A primary element is `m (a + b i)` with `m ≡ 1 (mod 4)` rational and `a + b i` primary (or `1`)
with `(a, b) = 1`. -/
lemma IsPrimary'.exists_intCast_mul {π : ℤ[i]} (hπ : IsPrimary' π) :
    ∃ (m : ℤ) (π' : ℤ[i]), m % 4 = 1 ∧ IsPrimary' π' ∧ IsCoprime π'.re π'.im ∧
      π = (m : ℤ[i]) * π' := by
  have hP := (isPrimary'_iff π).1 hπ
  have ha : π.re % 2 = 1 := hπ.re_odd
  have hg : 0 < Int.gcd π.re π.im := Int.gcd_pos_of_ne_zero_left _ (by omega)
  obtain ⟨g, a', b', hg0, hgcd, hae, hbe⟩ := Int.exists_gcd_one' hg
  have hcop : IsCoprime a' b' := Int.isCoprime_iff_gcd_eq_one.2 hgcd
  have hg2 : (g : ℤ) % 2 = 1 := by
    rcases Int.emod_two_eq_zero_or_one (g : ℤ) with h | h
    · exfalso
      obtain ⟨k, hk⟩ : (2 : ℤ) ∣ g := Int.dvd_of_emod_eq_zero h
      rw [hae, hk] at ha
      have : a' * (2 * k) = 2 * (a' * k) := by ring
      omega
    · exact h
  rcases (by omega : (g : ℤ) % 4 = 1 ∨ (g : ℤ) % 4 = 3) with h1 | h3
  · refine ⟨g, ⟨a', b'⟩, h1, ?_, hcop, ?_⟩
    · rw [isPrimary'_iff]
      simp only
      obtain ⟨k, hk⟩ : (4 : ℤ) ∣ g - 1 := Int.dvd_of_emod_eq_zero (by omega)
      have e1 : π.re - a' = 4 * (k * a') := by rw [hae]; linear_combination a' * hk
      have e2 : π.im - b' = 4 * (k * b') := by rw [hbe]; linear_combination b' * hk
      omega
    · ext <;> simp [hae, hbe] <;> ring
  · refine ⟨-g, ⟨-a', -b'⟩, by omega, ?_, ?_, ?_⟩
    · rw [isPrimary'_iff]
      simp only
      obtain ⟨k, hk⟩ : (4 : ℤ) ∣ -(g : ℤ) - 1 := Int.dvd_of_emod_eq_zero (by omega)
      have e1 : π.re - (-a') = 4 * (k * (-a')) := by rw [hae]; linear_combination (-a') * hk
      have e2 : π.im - (-b') = 4 * (k * (-b')) := by rw [hbe]; linear_combination (-b') * hk
      omega
    · exact (IsCoprime.neg_left_iff _ _).2 ((IsCoprime.neg_right_iff _ _).2 hcop)
    · ext <;> simp [hae, hbe] <;> ring

/-- For primary `π = a + b i`, `(N π - 1) / 4 ≡ (a - 1) / 2 (mod 2)`. -/
lemma IsPrimary'.norm_sub_one_div_four_mod_two {π : ℤ[i]} (hπ : IsPrimary' π) :
    ((π.norm - 1) / 4) % 2 = ((π.re - 1) / 2) % 2 := by
  have hP := (isPrimary'_iff π).1 hπ
  obtain ⟨s, hs⟩ : ∃ s, π.re = 2 * s + 1 := ⟨π.re / 2, by have := hπ.re_odd; omega⟩
  obtain ⟨t, ht⟩ : ∃ t, π.im = 2 * t := hπ.im_even
  have hN : π.norm - 1 = 4 * (s * (s + 1) + t * t) := by rw [norm_def, hs, ht]; ring
  have hss : (s * (s + 1)) % 2 = 0 := Int.even_iff.1 (Int.even_mul_succ_self s)
  have htt : (t * t - t) % 2 = 0 := by
    have := Int.even_mul_succ_self (t - 1)
    rw [show (t - 1) * (t - 1 + 1) = t * t - t by ring, Int.even_iff] at this; exact this
  rw [hN, hs]
  rw [hs, ht] at hP
  have e : (2 * s + 1 - 1) / 2 = s := by omega
  rw [e, show 4 * (s * (s + 1) + t * t) / 4 = s * (s + 1) + t * t by omega]
  omega

lemma intCast_mul_re_div_two_mod_two {m : ℤ} (hm : m % 4 = 1) (x : ℤ[i]) (hx : x.re % 2 = 1) :
    (((m : ℤ[i]) * x).re - 1) / 2 % 2 = (x.re - 1) / 2 % 2 := by
  obtain ⟨k, hk⟩ : (4 : ℤ) ∣ m - 1 := Int.dvd_of_emod_eq_zero (by omega)
  have : ((m : ℤ[i]) * x).re = x.re + 4 * (k * x.re) := by
    simp only [Zsqrtd.re_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast]
    linear_combination x.re * hk
  rw [this]; omega

/-- **Theorem 2 (the law of biquadratic reciprocity).** Let `λ` and `π` be relatively prime primary
elements of `ℤ[i]`. Then `χ_π(λ) = χ_λ(π) (-1) ^ (((N λ - 1) / 4) ((N π - 1) / 4))`. -/
@[kb "irelandrosen1990" "Ch. 9, §9, Theorem 2 (biquadratic reciprocity), p. 134"]
theorem quarticSymbol_reciprocity {π μ : ℤ[i]} (hπ : IsPrimary π) (hμ : IsPrimary μ)
    (hcop : IsCoprime π μ) :
    quarticSymbol π μ = quarticSymbol μ π * sgn (((μ.norm - 1) / 4) * ((π.norm - 1) / 4)) := by
  obtain ⟨m, π', hm, hπ', hab, rfl⟩ := hπ.2.exists_intCast_mul
  obtain ⟨n, μ', hn, hμ', hcd, rfl⟩ := hμ.2.exists_intCast_mul
  have hmodd : Odd m := Int.odd_iff.2 (by omega)
  have hnodd : Odd n := Int.odd_iff.2 (by omega)
  have hm2 := odd_intCast_not_onePlusI_dvd hmodd
  have hn2 := odd_intCast_not_onePlusI_dvd hnodd
  have hm0 : (m : ℤ[i]) ≠ 0 := by rw [Ne, Int.cast_eq_zero]; omega
  have hn0 : (n : ℤ[i]) ≠ 0 := by rw [Ne, Int.cast_eq_zero]; omega
  have hπ'0 : π' ≠ 0 := by rintro rfl; exact hπ'.not_onePlusI_dvd (dvd_zero _)
  have hμ'0 : μ' ≠ 0 := by rintro rfl; exact hμ'.not_onePlusI_dvd (dvd_zero _)
  -- coprimality of the pieces
  have c1 : IsCoprime (m : ℤ[i]) ((n : ℤ[i]) * μ') := hcop.of_mul_left_left
  have c2 : IsCoprime π' ((n : ℤ[i]) * μ') := hcop.of_mul_left_right
  have c3 : IsCoprime π' (n : ℤ[i]) := c2.of_mul_right_left
  have c4 : IsCoprime π' μ' := c2.of_mul_right_right
  -- `χ_π(λ) = χ_λ(m) χ_n(π') χ_{λ'}(π') sgn`
  have hL : quarticSymbol ((m : ℤ[i]) * π') ((n : ℤ[i]) * μ') =
      quarticSymbol ((n : ℤ[i]) * μ') (m : ℤ[i]) * quarticSymbol (n : ℤ[i]) π' *
        (quarticSymbol μ' π' * sgn (((π'.re - 1) / 2) * ((μ'.re - 1) / 2))) := by
    rw [quarticSymbol_mul_left hm0 hπ'0, quarticSymbol_intCast_comm hm (hμ.2) c1,
      quarticSymbol_mul_right hπ'.not_onePlusI_dvd,
      ← quarticSymbol_intCast_comm hn hπ' c3.symm,
      quarticSymbol_comm_of_isCoprime_re_im hπ' hμ' c4 hab hcd]
    ring
  have hR : quarticSymbol ((n : ℤ[i]) * μ') ((m : ℤ[i]) * π') =
      quarticSymbol ((n : ℤ[i]) * μ') (m : ℤ[i]) * quarticSymbol (n : ℤ[i]) π' *
        quarticSymbol μ' π' := by
    rw [quarticSymbol_mul_right hμ.2.not_onePlusI_dvd, quarticSymbol_mul_left hn0 hμ'0 π']
    ring
  have h1 := hπ.2.norm_sub_one_div_four_mod_two
  have h2 := hμ.2.norm_sub_one_div_four_mod_two
  have h3 := intCast_mul_re_div_two_mod_two hm π' hπ'.re_odd
  have h4 := intCast_mul_re_div_two_mod_two hn μ' hμ'.re_odd
  have hx : Int.ModEq 2 ((π'.re - 1) / 2) ((((m : ℤ[i]) * π').norm - 1) / 4) := (h1.trans h3).symm
  have hy : Int.ModEq 2 ((μ'.re - 1) / 2) ((((n : ℤ[i]) * μ').norm - 1) / 4) := (h2.trans h4).symm
  have hd := (hx.mul hy).dvd
  have key : (((π'.re - 1) / 2) * ((μ'.re - 1) / 2)).negOnePow =
      (((((n : ℤ[i]) * μ').norm - 1) / 4) * ((((m : ℤ[i]) * π').norm - 1) / 4)).negOnePow := by
    rw [Int.negOnePow_eq_iff, even_iff_two_dvd]
    rw [show ((π'.re - 1) / 2) * ((μ'.re - 1) / 2) - ((((n : ℤ[i]) * μ').norm - 1) / 4) *
        ((((m : ℤ[i]) * π').norm - 1) / 4) = -(((((m : ℤ[i]) * π').norm - 1) / 4) *
        ((((n : ℤ[i]) * μ').norm - 1) / 4) - ((π'.re - 1) / 2) * ((μ'.re - 1) / 2)) by ring]
    exact dvd_neg.2 hd
  rw [hL, hR, key]
  ring

/-- **Theorem 2, second form** (the remark after Theorem 2). For relatively prime primary
`π = a + b i` and `λ = c + d i`, `χ_π(λ) = χ_λ(π) (-1) ^ (((a - 1) / 2) ((c - 1) / 2))`; in particular
`π` and `λ` have the same character unless both are `≡ 3 + 2i (mod 4)`. -/
@[kb "irelandrosen1990" "Ch. 9, §9, Theorem 2 (second form), p. 134"]
theorem quarticSymbol_reciprocity' {π μ : ℤ[i]} (hπ : IsPrimary π) (hμ : IsPrimary μ)
    (hcop : IsCoprime π μ) :
    quarticSymbol π μ = quarticSymbol μ π * sgn (((π.re - 1) / 2) * ((μ.re - 1) / 2)) := by
  rw [quarticSymbol_reciprocity hπ hμ hcop]
  congr 3
  rw [Int.negOnePow_eq_iff]
  have hx : Int.ModEq 2 ((μ.norm - 1) / 4) ((μ.re - 1) / 2) := hμ.2.norm_sub_one_div_four_mod_two
  have hy : Int.ModEq 2 ((π.norm - 1) / 4) ((π.re - 1) / 2) := hπ.2.norm_sub_one_div_four_mod_two
  have hd := (hx.mul hy).dvd
  rw [even_iff_two_dvd]
  rw [show (μ.norm - 1) / 4 * ((π.norm - 1) / 4) - (π.re - 1) / 2 * ((μ.re - 1) / 2) =
    -((μ.re - 1) / 2 * ((π.re - 1) / 2) - (μ.norm - 1) / 4 * ((π.norm - 1) / 4)) by ring]
  exact dvd_neg.2 hd

end Gaussian

end NTKB.IrelandRosen
