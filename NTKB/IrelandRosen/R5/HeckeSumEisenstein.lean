/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.IrelandRosen.R5.HeckeEisenstein

/-!
# The coefficients of `L(s, χ)` for the Hecke character of `y² = x³ + D`

For the character `χ = heckeCharSextic D` of Ireland–Rosen, Chapter 18, Theorem 8, the Dirichlet
series `L(s, χ) = ∑_A χ(A) N(A)^{-s}` over the nonzero ideals `A` of `ℤ[ω]` is
`(1/6) ∑_{α ≠ 0} χ(α) N(α)^{-s}`, each ideal having six generators. Its `n`-th coefficient, times
`6`, is

  `heckeSumSextic D n = ∑_{α ∈ ℤ[ω], N(α) = n} χ(α)`.

We prove the recursions of `heckeSumSextic D n` at a prime `p ∣ n`, as for `ℤ[i]`
(`NTKB/IrelandRosen/R5/HeckeSumGaussian.lean`):

* `p ∣ 6D`: `χ` vanishes on every `α` of norm `n` (`heckeSumSextic_of_dvd_six_mul`);
* `p ≡ 2 (mod 3)`, `p ∤ D`: `p ∣ α`, so the sum is `χ((p))` times the sum for `n/p²`, and `0` when
  `p² ∤ n` (`heckeSumSextic_inert`);
* `p = π π̄`, `π` primary: inclusion–exclusion over `π ∣ α`, `π̄ ∣ α` (`heckeSumSextic_split`).
-/

namespace NTKB.IrelandRosen.CM

open NTKB.HardyWright QuadraticAlgebra NTKB.IrelandRosen.Eisenstein

local notation "ℤ[ω]" => NTKB.HardyWright.ZRho

/-- The Eisenstein integers of norm `n`. -/
def normSetω (n : ℕ) : Set ℤ[ω] := {z | norm z = n}

lemma abs_le_of_norm_eq {z : ℤ[ω]} {n : ℕ} (hz : norm z = n) : |z.re| ≤ 2 * n ∧ |z.im| ≤ 2 * n := by
  rw [rho_norm] at hz
  have h1 : |z.re| ≤ z.re ^ 2 := by
    rcases eq_or_ne z.re 0 with h | h
    · simp [h]
    · rw [sq, ← abs_mul_abs_self]; exact le_mul_of_one_le_left (abs_nonneg _) (Int.one_le_abs h)
  have h2 : |z.im| ≤ z.im ^ 2 := by
    rcases eq_or_ne z.im 0 with h | h
    · simp [h]
    · rw [sq, ← abs_mul_abs_self]; exact le_mul_of_one_le_left (abs_nonneg _) (Int.one_le_abs h)
  have h3 : 3 * z.re ^ 2 ≤ 4 * n := by nlinarith [sq_nonneg (2 * z.im - z.re)]
  have h4 : 3 * z.im ^ 2 ≤ 4 * n := by nlinarith [sq_nonneg (2 * z.re - z.im)]
  constructor <;> nlinarith

lemma normSetω_finite (n : ℕ) : (normSetω n).Finite := by
  have hfin : ((Finset.Icc (-(2 * n : ℤ)) (2 * n) ×ˢ Finset.Icc (-(2 * n : ℤ)) (2 * n) :
      Finset (ℤ × ℤ)) : Set (ℤ × ℤ)).Finite := Finset.finite_toSet _
  refine (hfin.image fun x => (⟨x.1, x.2⟩ : ℤ[ω])).subset fun z hz => ?_
  obtain ⟨h1, h2⟩ := abs_le_of_norm_eq (n := n) hz
  refine ⟨(z.re, z.im), ?_, rfl⟩
  simp only [Finset.coe_product, Finset.coe_Icc, Set.mem_prod, Set.mem_Icc]
  exact ⟨abs_le.mp h1, abs_le.mp h2⟩

/-- `∑_{α ∈ ℤ[ω], N(α) = n} χ(α)` for `χ = heckeCharSextic D`: six times the `n`-th coefficient
of `L(s, χ)`. -/
noncomputable def heckeSumSextic (D : ℤ) (n : ℕ) : ℤ[ω] :=
  ∑ α ∈ (normSetω_finite n).toFinset, heckeCharSextic D α

lemma mem_normSetω_finite_toFinset {n : ℕ} {z : ℤ[ω]} :
    z ∈ (normSetω_finite n).toFinset ↔ norm z = n := by
  rw [Set.Finite.mem_toFinset]; rfl

open Classical in
/-- Sum over the elements of norm `N` divisible by `c`. -/
lemma sum_filter_dvd {c : ℤ[ω]} (hc : c ≠ 0) (N : ℕ) (f : ℤ[ω] → ℤ[ω]) :
    ∑ z ∈ (normSetω_finite N).toFinset.filter (c ∣ ·), f z =
      if (norm c).natAbs ∣ N then
        ∑ w ∈ (normSetω_finite (N / (norm c).natAbs)).toFinset, f (c * w) else 0 := by
  have hc0 : norm c ≠ 0 := fun h => hc (qa_norm_eq_zero h)
  have hnn := rho_norm_nonneg c
  have hk : (((norm c).natAbs : ℕ) : ℤ) = norm c := Int.natAbs_of_nonneg hnn
  have hkpos : 0 < (norm c).natAbs := by omega
  split_ifs with h
  · obtain ⟨m, hm⟩ := h
    have hm' : N / (norm c).natAbs = m := by rw [hm]; exact Nat.mul_div_cancel_left _ hkpos
    rw [hm']
    have himg : (normSetω_finite N).toFinset.filter (c ∣ ·) =
        (normSetω_finite m).toFinset.image (c * ·) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_image, mem_normSetω_finite_toFinset]
      constructor
      · rintro ⟨hz, w, rfl⟩
        refine ⟨w, ?_, rfl⟩
        rw [map_mul, hm, Nat.cast_mul, hk] at hz
        exact mul_left_cancel₀ hc0 hz
      · rintro ⟨w, hw, rfl⟩
        refine ⟨?_, dvd_mul_right _ _⟩
        rw [map_mul, hw, hm, Nat.cast_mul, hk]
    rw [himg, Finset.sum_image (fun a _ b _ h => mul_left_cancel₀ hc h)]
  · refine Finset.sum_eq_zero fun z hz => ?_
    exfalso
    simp only [Finset.mem_filter, mem_normSetω_finite_toFinset] at hz
    obtain ⟨hz, w, rfl⟩ := hz
    apply h
    have := congrArg Int.natAbs hz
    rw [map_mul, Int.natAbs_mul, Int.natAbs_natCast] at this
    exact ⟨_, this.symm⟩

open Classical in
lemma sum_char_filter_dvd (D : ℤ) {c : ℤ[ω]} (hc : c ≠ 0) (N : ℕ) :
    ∑ z ∈ (normSetω_finite N).toFinset.filter (c ∣ ·), heckeCharSextic D z =
      if (norm c).natAbs ∣ N then
        heckeCharSextic D c * heckeSumSextic D (N / (norm c).natAbs) else 0 := by
  rw [sum_filter_dvd hc]
  split_ifs
  · rw [heckeSumSextic, Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ => heckeCharSextic_mul D c w
  · rfl

lemma heckeCharSextic_one (D : ℤ) : heckeCharSextic D 1 = 1 := by
  unfold heckeCharSextic
  rw [if_pos isCoprime_one_left]
  simp

lemma heckeCharSextic_zero (D : ℤ) : heckeCharSextic D 0 = 0 := by
  unfold heckeCharSextic
  rw [if_neg (fun h => ne_zero_of_isCoprime' h rfl)]

theorem heckeSumSextic_zero (D : ℤ) : heckeSumSextic D 0 = 0 := by
  have : (normSetω_finite 0).toFinset = {0} := by
    ext z
    rw [mem_normSetω_finite_toFinset, Finset.mem_singleton]
    constructor
    · intro h; exact qa_norm_eq_zero (by simpa using h)
    · rintro rfl; simp
  rw [heckeSumSextic, this, Finset.sum_singleton, heckeCharSextic_zero]

lemma normSetω_one_eq : (normSetω_finite 1).toFinset =
    {1, -1, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩} := by
  ext ⟨x, y⟩
  rw [mem_normSetω_finite_toFinset, rho_norm]
  simp only [Finset.mem_insert, Finset.mem_singleton, QuadraticAlgebra.ext_iff]
  simp only [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_neg,
    QuadraticAlgebra.im_neg, neg_zero, Nat.cast_one]
  constructor
  · intro h
    have h1 : x ^ 2 ≤ 2 := by nlinarith [sq_nonneg (2 * y - x)]
    have h2 : y ^ 2 ≤ 2 := by nlinarith [sq_nonneg (2 * x - y)]
    have hr : -1 ≤ x ∧ x ≤ 1 := ⟨by nlinarith, by nlinarith⟩
    have hi : -1 ≤ y ∧ y ≤ 1 := ⟨by nlinarith, by nlinarith⟩
    obtain ⟨hr1, hr2⟩ := hr
    obtain ⟨hi1, hi2⟩ := hi
    interval_cases x <;> interval_cases y <;> simp_all
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      norm_num

theorem heckeSumSextic_one (D : ℤ) : heckeSumSextic D 1 = 6 := by
  have hχ : ∀ z ∈ (normSetω_finite 1).toFinset, heckeCharSextic D z = 1 := by
    intro z hz
    rw [mem_normSetω_finite_toFinset] at hz
    have hu : IsUnit z := qa_isUnit_iff.2 (by rw [hz]; rfl)
    rw [heckeCharSextic_of_associated D (associated_one_iff_isUnit.2 hu), heckeCharSextic_one]
  rw [heckeSumSextic, Finset.sum_congr rfl hχ, Finset.sum_const, normSetω_one_eq]
  rw [Finset.card_insert_of_notMem (by simp [QuadraticAlgebra.ext_iff]),
    Finset.card_insert_of_notMem (by simp [QuadraticAlgebra.ext_iff]),
    Finset.card_insert_of_notMem (by simp [QuadraticAlgebra.ext_iff]),
    Finset.card_insert_of_notMem (by simp [QuadraticAlgebra.ext_iff]),
    Finset.card_pair (by simp [QuadraticAlgebra.ext_iff])]
  norm_num

lemma star_dvd_of_dvd_star' {x y : ℤ[ω]} (h : x ∣ star y) : star x ∣ y := by
  obtain ⟨k, hk⟩ := h
  refine ⟨star k, ?_⟩
  have := congrArg star hk
  rw [star_star, star_mul'] at this
  exact this

lemma natCast_dvd_intCast {p : ℕ} {a : ℤ} (h : (p : ℤ) ∣ a) : (p : ℤ[ω]) ∣ (a : ℤ[ω]) := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k, by push_cast; ring⟩

/-- If a rational prime divides `N(α)` and `6D`, then `χ(α) = 0`. -/
lemma heckeCharSextic_eq_zero_of_prime_dvd_norm {D : ℤ} {α : ℤ[ω]} {p : ℕ} (hp : p.Prime)
    (h1 : (p : ℤ) ∣ norm α) (h2 : (p : ℤ) ∣ 6 * D) : heckeCharSextic D α = 0 := by
  unfold heckeCharSextic
  rw [if_neg]
  intro hc
  have hc' : IsCoprime (star α) (6 * D : ℤ[ω]) := by
    obtain ⟨u, v, h⟩ := hc
    refine ⟨star u, star v, ?_⟩
    have := congrArg star h
    simpa [star_add, star_mul', star_intCast, mul_comm] using this
  have h3 := hc.mul_left hc'
  rw [mul_star] at h3
  have hpd2 : (p : ℤ[ω]) ∣ (6 * D : ℤ[ω]) := by
    have := natCast_dvd_intCast h2
    push_cast at this
    exact this
  have hu := h3.isUnit_of_dvd' (natCast_dvd_intCast h1) hpd2
  rw [qa_isUnit_iff, natAbs_norm_natCast] at hu
  have := hp.two_le
  have : p ^ 2 ≥ 4 := by nlinarith
  omega

theorem heckeSumSextic_of_dvd_six_mul {D : ℤ} {p : ℕ} (hp : p.Prime) (hpD : (p : ℤ) ∣ 6 * D)
    {n : ℕ} (hn : p ∣ n) : heckeSumSextic D n = 0 := by
  unfold heckeSumSextic
  refine Finset.sum_eq_zero fun α hα => ?_
  rw [mem_normSetω_finite_toFinset] at hα
  exact heckeCharSextic_eq_zero_of_prime_dvd_norm hp (by rw [hα]; exact_mod_cast hn) hpD

lemma natCast_dvd_of_dvd_norm' {p : ℕ} (hp : p.Prime) (hp3 : p % 3 = 2) {z : ℤ[ω]}
    (h : (p : ℤ) ∣ norm z) : (p : ℤ[ω]) ∣ z := by
  have hpr : Prime (p : ℤ[ω]) := prime_natCast_of_mod_three_eq_two hp hp3
  have hd : (p : ℤ[ω]) ∣ z * star z := by
    rw [mul_star]; exact natCast_dvd_intCast h
  rcases hpr.dvd_or_dvd hd with h' | h'
  · exact h'
  · have := star_dvd_of_dvd_star' h'
    rwa [star_natCast] at this

theorem heckeSumSextic_inert {D : ℤ} {p : ℕ} (hp : p.Prime) (hp3 : p % 3 = 2)
    (hpD : ¬ (p : ℤ) ∣ 6 * D) {n : ℕ} (hn : p ∣ n) :
    heckeSumSextic D n =
      if p ^ 2 ∣ n then heckeCharSextic D (p : ℤ[ω]) * heckeSumSextic D (n / p ^ 2) else 0 := by
  classical
  have hp0 : (p : ℤ[ω]) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hall : ∀ z ∈ (normSetω_finite n).toFinset, (p : ℤ[ω]) ∣ z := fun z hz =>
    natCast_dvd_of_dvd_norm' hp hp3 (by rw [mem_normSetω_finite_toFinset.1 hz]; exact_mod_cast hn)
  have := sum_char_filter_dvd D hp0 n
  rw [Finset.filter_true_of_mem hall, natAbs_norm_natCast] at this
  exact this

theorem heckeSumSextic_split {D : ℤ} {p : ℕ} (hp : p.Prime) {π : ℤ[ω]} (hπ : IsPrimary π)
    (hπp : norm π = p) (hpD : ¬ (p : ℤ) ∣ 6 * D) {n : ℕ} (hn : p ∣ n) :
    heckeSumSextic D n =
      (heckeCharSextic D π + heckeCharSextic D (star π)) * heckeSumSextic D (n / p) -
        (if p ^ 2 ∣ n then
          heckeCharSextic D π * heckeCharSextic D (star π) * heckeSumSextic D (n / p ^ 2)
        else 0) := by
  classical
  have hN : (norm π).natAbs = p := by rw [hπp, Int.natAbs_natCast]
  have hprime : Prime π := prime_of_natAbs_norm_prime (by rw [hN]; exact hp)
  have hnorm' : norm (star π) = p := by rw [QuadraticAlgebra.norm_star, hπp]
  have hN' : (norm (star π)).natAbs = p := by rw [hnorm', Int.natAbs_natCast]
  have hprime' : Prime (star π) := prime_of_natAbs_norm_prime (by rw [hN']; exact hp)
  have hπ0 : π ≠ 0 := hprime.ne_zero
  have hπ0' : star π ≠ 0 := hprime'.ne_zero
  have hp0 : (p : ℤ[ω]) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hmul : π * star π = (p : ℤ[ω]) := by
    rw [mul_star, hπp]; push_cast; rfl
  have hp1 : p % 3 = 1 := by
    have h3 : p ≠ 3 := by
      rintro rfl; exact hpD ⟨2 * D, by ring⟩
    have hm := rho_norm_mod_three π.re π.im
    rw [← rho_norm, hπp] at hm
    have : p % 3 ≠ 0 := by
      intro h0
      exact h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.dvd_of_mod_eq_zero h0)).symm
    omega
  have hcop : IsCoprime π (star π) := by
    refine (hprime.irreducible.coprime_iff_not_dvd).2 fun hd => ?_
    obtain ⟨w, hw⟩ := (hprime.irreducible.associated_of_dvd hprime'.irreducible hd)
    have hwu : IsUnit (w : ℤ[ω]) := w.isUnit
    have h1 : IsPrimary (1 * π) := by rwa [one_mul]
    have h2 : IsPrimary ((w : ℤ[ω]) * π) := by rw [mul_comm, hw]; exact hπ.star
    have hw1 := unit_eq_of_isPrimary isUnit_one hwu h1 h2
    rw [← hw1, mul_one] at hw
    have him := congrArg QuadraticAlgebra.im hw
    simp at him
    have him0 : π.im = 0 := by linarith
    have hn := rho_norm π
    rw [hπp, him0] at hn
    exact (natCast_ne_sq_and_three_mul_sq hp hp1 π.re).1 (by rw [hn]; ring)
  set S := (normSetω_finite n).toFinset with hS
  have hpn : (p : ℤ) * ((n / p : ℕ) : ℤ) = n := by exact_mod_cast Nat.mul_div_cancel' hn
  have hA := sum_char_filter_dvd D hπ0 n
  have hB := sum_char_filter_dvd D hπ0' n
  rw [hN, if_pos hn] at hA
  rw [hN', if_pos hn] at hB
  have hC := sum_char_filter_dvd D hp0 n
  rw [natAbs_norm_natCast] at hC
  have hinter : S.filter (π ∣ ·) ∩ S.filter (star π ∣ ·) = S.filter ((p : ℤ[ω]) ∣ ·) := by
    ext z
    simp only [Finset.mem_inter, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hz, h1⟩, _, h2⟩
      exact ⟨hz, hmul ▸ hcop.mul_dvd h1 h2⟩
    · rintro ⟨hz, h⟩
      exact ⟨⟨hz, (dvd_mul_right π _).trans (hmul ▸ h)⟩, hz,
        (dvd_mul_left (star π) _).trans (hmul ▸ h)⟩
  have hunion : S.filter (π ∣ ·) ∪ S.filter (star π ∣ ·) = S := by
    ext z
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hz
      have hzn := mem_normSetω_finite_toFinset.1 hz
      have hdvd : π ∣ z * star z := by
        rw [mul_star, hzn]
        obtain ⟨k, hk⟩ := hn
        rw [hk]; push_cast
        rw [← hmul, mul_assoc]
        exact dvd_mul_right _ _
      rcases hprime.dvd_or_dvd hdvd with h | h
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr ⟨hz, by simpa using star_dvd_of_dvd_star' h⟩
  have key := Finset.sum_union_inter (s₁ := S.filter (π ∣ ·)) (s₂ := S.filter (star π ∣ ·))
    (f := heckeCharSextic D)
  rw [hunion, hinter, hA, hB, hC] at key
  have hχp : heckeCharSextic D (p : ℤ[ω]) = heckeCharSextic D π * heckeCharSextic D (star π) := by
    rw [← hmul, heckeCharSextic_mul]
  rw [hχp] at key
  have hH : heckeSumSextic D n = ∑ z ∈ S, heckeCharSextic D z := rfl
  rw [← hH] at key
  split_ifs at key ⊢ <;> linear_combination key

end NTKB.IrelandRosen.CM
