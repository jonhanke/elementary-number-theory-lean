/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.IrelandRosen.R5.HeckeGaussian
import NTKB.Elementary.HardyWright.ArithmeticFunctions.SumTwoSquares
import NTKB.IrelandRosen.R3.Burde

/-!
# The coefficients of `L(s, χ)` for the Hecke character of `y² = x³ - Dx`

For the character `χ = heckeCharQuartic D` of Ireland–Rosen, Chapter 18, Theorem 7, the Dirichlet
series `L(s, χ) = ∑_A χ(A) N(A)^{-s}` over the nonzero ideals `A` of `ℤ[i]` is
`(1/4) ∑_{α ≠ 0} χ(α) N(α)^{-s}`, as `χ` is a function of the ideal and each ideal has four
generators. Its `n`-th coefficient, times `4`, is

  `heckeSumQuartic D n = ∑_{α ∈ ℤ[i], N(α) = n} χ(α)`.

We prove the recursions of `heckeSumQuartic D n` at a prime `p ∣ n`, by the same counting as for
`r(n)` (`NTKB.HardyWright.ncard_normSet_eq`):

* `p ∣ 2D`: `χ` vanishes on every `α` of norm `n` (`heckeSumQuartic_of_dvd_two_mul`);
* `p ≡ 3 (mod 4)`, `p ∤ D`: `p ∣ α`, so the sum is `χ((p))` times the sum for `n/p²`, and `0` when
  `p² ∤ n` (`heckeSumQuartic_inert`);
* `p = π π̄`, `π` primary: `α` is divisible by `π` or by `π̄`, by both exactly when `p ∣ α`, so the
  sum is `(χ(π) + χ(π̄))` times the sum for `n/p`, minus `χ(π) χ(π̄)` times the sum for `n/p²`
  (`heckeSumQuartic_split`).
-/

namespace NTKB.IrelandRosen.CM

open NTKB.IrelandRosen.Gaussian Zsqrtd

local notation "ℤ[i]" => GaussianInt

/-- `∑_{α ∈ ℤ[i], N(α) = n} χ(α)` for `χ = heckeCharQuartic D`: four times the `n`-th coefficient
of `L(s, χ)`. -/
noncomputable def heckeSumQuartic (D : ℤ) (n : ℕ) : ℤ[i] :=
  ∑ α ∈ (NTKB.HardyWright.normSet_finite n).toFinset, heckeCharQuartic D α

lemma mem_normSet_finset {n : ℕ} {z : ℤ[i]} :
    z ∈ (NTKB.HardyWright.normSet_finite n).toFinset ↔ z.norm = n := by
  rw [Set.Finite.mem_toFinset]; rfl

open Classical in
lemma sum_filter_dvd_normSet {c : ℤ[i]} (hc : c ≠ 0) (m N : ℕ) (hN : c.norm * m = N)
    (f : ℤ[i] → ℤ[i]) :
    ∑ z ∈ (NTKB.HardyWright.normSet_finite N).toFinset.filter (c ∣ ·), f z =
      ∑ w ∈ (NTKB.HardyWright.normSet_finite m).toFinset, f (c * w) := by
  have : (NTKB.HardyWright.normSet_finite N).toFinset.filter (c ∣ ·) =
      (NTKB.HardyWright.normSet_finite m).toFinset.image (c * ·) := by
    ext z
    have h := Set.ext_iff.1 (NTKB.HardyWright.image_mul_normSet hc m N hN) z
    simp only [Set.mem_image, Set.mem_ofPred_eq] at h
    simp only [Finset.mem_filter, Finset.mem_image, mem_normSet_finset]
    exact h.symm
  rw [this, Finset.sum_image (fun a _ b _ h => mul_left_cancel₀ hc h)]

lemma heckeCharQuartic_eq_zero_of_dvd_norm {D : ℤ} {α : ℤ[i]} {g : ℤ} (hg : ¬ IsUnit g)
    (h1 : g ∣ α.norm) (h2 : g ∣ 2 * D) : heckeCharQuartic D α = 0 := by
  by_contra hne
  have hc : IsCoprime α (2 * D : ℤ[i]) := by
    by_contra hc; exact hne (heckeCharQuartic_of_not_isCoprime hc)
  have hc' : IsCoprime (star α) (2 * D : ℤ[i]) := by
    obtain ⟨u, v, h⟩ := hc
    refine ⟨star u, star v, ?_⟩
    have := congrArg star h
    simpa [star_add, star_mul', star_intCast] using this
  have h3 : IsCoprime ((α.norm : ℤ) : ℤ[i]) (((2 * D : ℤ)) : ℤ[i]) := by
    rw [Zsqrtd.norm_eq_mul_conj]
    push_cast
    exact hc.mul_left hc'
  exact hg ((intCast_isCoprime_iff.1 h3).isUnit_of_dvd' h1 h2)

lemma heckeCharQuartic_one (D : ℤ) : heckeCharQuartic D 1 = 1 := by
  have hm := heckeCharQuartic_mul D 1 1
  rw [mul_one] at hm
  have hne : heckeCharQuartic D 1 ≠ 0 := by
    intro h0
    have := norm_heckeCharQuartic (D := D) (α := 1) isCoprime_one_left
    rw [h0, Zsqrtd.norm_zero, Zsqrtd.norm_one] at this
    exact zero_ne_one this
  exact mul_left_cancel₀ hne (by rw [mul_one]; exact hm.symm)

theorem heckeSumQuartic_zero (D : ℤ) : heckeSumQuartic D 0 = 0 := by
  unfold heckeSumQuartic
  apply Finset.sum_eq_zero
  intro α hα
  rw [mem_normSet_finset] at hα
  exact heckeCharQuartic_eq_zero_of_dvd_norm (g := 2) (by rw [Int.isUnit_iff]; norm_num)
    (by rw [hα]; simp) (dvd_mul_right 2 D)

theorem heckeSumQuartic_one (D : ℤ) : heckeSumQuartic D 1 = 4 := by
  unfold heckeSumQuartic
  rw [Finset.sum_congr rfl (g := fun _ => (1 : ℤ[i]))]
  · rw [Finset.sum_const, nsmul_eq_mul, mul_one,
      ← Set.ncard_eq_toFinset_card _ (NTKB.HardyWright.normSet_finite 1),
      NTKB.HardyWright.ncard_normSet_one]
    norm_num
  · intro α hα
    rw [mem_normSet_finset] at hα
    have hu : IsUnit α := (isUnit_iff_norm_eq_one).2 (by rw [hα]; rfl)
    rw [heckeCharQuartic_of_associated D (associated_one_iff_isUnit.2 hu), heckeCharQuartic_one]

theorem heckeSumQuartic_of_dvd_two_mul {D : ℤ} {p : ℕ} (hp : p.Prime) (hpD : (p : ℤ) ∣ 2 * D)
    {n : ℕ} (hn : p ∣ n) : heckeSumQuartic D n = 0 := by
  unfold heckeSumQuartic
  apply Finset.sum_eq_zero
  intro α hα
  rw [mem_normSet_finset] at hα
  refine heckeCharQuartic_eq_zero_of_dvd_norm (g := p) ?_ (by rw [hα]; exact_mod_cast hn) hpD
  rw [Int.isUnit_iff]
  have := hp.two_le
  omega

theorem heckeSumQuartic_inert {D : ℤ} {p : ℕ} (hp : p.Prime) (hp3 : p % 4 = 3)
    (hpD : ¬ (p : ℤ) ∣ 2 * D) {n : ℕ} (hn : p ∣ n) :
    heckeSumQuartic D n =
      if p ^ 2 ∣ n then heckeCharQuartic D (p : ℤ[i]) * heckeSumQuartic D (n / p ^ 2) else 0 := by
  have hall : ∀ z ∈ (NTKB.HardyWright.normSet_finite n).toFinset, (p : ℤ[i]) ∣ z := fun z hz =>
    NTKB.HardyWright.natCast_dvd_of_dvd_norm hp hp3
      (by rw [mem_normSet_finset.1 hz]; exact_mod_cast hn)
  have hp0 : (p : ℤ[i]) ≠ 0 := by exact_mod_cast hp.ne_zero
  split_ifs with hp2
  · have := sum_filter_dvd_normSet hp0 (n / p ^ 2) n
      (by rw [NTKB.HardyWright.norm_natCast']; norm_cast; exact Nat.mul_div_cancel' hp2)
      (heckeCharQuartic D)
    classical
    rw [Finset.filter_true_of_mem hall] at this
    rw [heckeSumQuartic, this, heckeSumQuartic, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun w _ => heckeCharQuartic_mul D _ _)
  · unfold heckeSumQuartic
    apply Finset.sum_eq_zero
    intro z hz
    exfalso
    have hzn := mem_normSet_finset.1 hz
    obtain ⟨w, rfl⟩ := hall z hz
    apply hp2
    have : ((p ^ 2 : ℕ) : ℤ) ∣ (n : ℤ) := by
      rw [← hzn, Zsqrtd.norm_mul, NTKB.HardyWright.norm_natCast']; exact dvd_mul_right _ _
    exact_mod_cast this

theorem heckeSumQuartic_split {D : ℤ} {p : ℕ} (hp : p.Prime) {π : ℤ[i]} (hπ : IsPrimary π)
    (hπp : π.norm = p) (hpD : ¬ (p : ℤ) ∣ 2 * D) {n : ℕ} (hn : p ∣ n) :
    heckeSumQuartic D n =
      (heckeCharQuartic D π + heckeCharQuartic D (star π)) * heckeSumQuartic D (n / p) -
        (if p ^ 2 ∣ n then
          heckeCharQuartic D π * heckeCharQuartic D (star π) * heckeSumQuartic D (n / p ^ 2)
        else 0) := by
  classical
  have hpn : (p : ℤ).natAbs.Prime := by simpa using hp
  have hπpn : π.norm.natAbs.Prime := by rw [hπp]; exact hpn
  have hirr : Irreducible π := irreducible_of_prime_norm hπpn
  have hp2 : p ≠ 2 := prime_ne_two_of_not_dvd hpD
  have hcop : IsCoprime π (star π) :=
    isCoprime_star_of_prime_norm hπpn (by rw [hπp, Int.natAbs_natCast]; exact hp2)
  have hprime : Prime π := irreducible_iff_prime.mp hirr
  have hπ0 : π ≠ 0 := hirr.ne_zero
  have hπ0' : star π ≠ 0 := (irreducible_star hirr).ne_zero
  have hp0 : (p : ℤ[i]) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hnorm' : (star π).norm = p := by rw [Zsqrtd.norm_conj, hπp]
  have hmul : π * star π = (p : ℤ[i]) := by
    rw [← Zsqrtd.norm_eq_mul_conj, hπp]; push_cast; rfl
  have hnp : (p : ℤ) * ((n / p : ℕ) : ℤ) = n := by exact_mod_cast Nat.mul_div_cancel' hn
  set S := (NTKB.HardyWright.normSet_finite n).toFinset with hS
  have hA := sum_filter_dvd_normSet hπ0 (n / p) n (by rw [hπp]; exact hnp) (heckeCharQuartic D)
  have hB := sum_filter_dvd_normSet hπ0' (n / p) n (by rw [hnorm']; exact hnp)
    (heckeCharQuartic D)
  have hA' : ∑ w ∈ (NTKB.HardyWright.normSet_finite (n / p)).toFinset,
      heckeCharQuartic D (π * w) = heckeCharQuartic D π * heckeSumQuartic D (n / p) := by
    rw [heckeSumQuartic, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun w _ => heckeCharQuartic_mul D _ _)
  have hB' : ∑ w ∈ (NTKB.HardyWright.normSet_finite (n / p)).toFinset,
      heckeCharQuartic D (star π * w) =
        heckeCharQuartic D (star π) * heckeSumQuartic D (n / p) := by
    rw [heckeSumQuartic, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun w _ => heckeCharQuartic_mul D _ _)
  have hinter : S.filter (π ∣ ·) ∩ S.filter (star π ∣ ·) = S.filter ((p : ℤ[i]) ∣ ·) := by
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
      have hzn := mem_normSet_finset.1 hz
      have hdvd : π ∣ z * star z := by
        rw [← Zsqrtd.norm_eq_mul_conj, hzn]
        obtain ⟨k, hk⟩ := hn
        rw [hk]; push_cast
        rw [← hmul, mul_assoc]
        exact dvd_mul_right _ _
      rcases hprime.dvd_or_dvd hdvd with h | h
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr ⟨hz, NTKB.HardyWright.star_dvd_of_dvd_star h⟩
  have key := Finset.sum_union_inter (s₁ := S.filter (π ∣ ·)) (s₂ := S.filter (star π ∣ ·))
    (f := heckeCharQuartic D)
  rw [hunion, hinter, hA, hB, hA', hB'] at key
  have hC : ∑ z ∈ S.filter ((p : ℤ[i]) ∣ ·), heckeCharQuartic D z =
      if p ^ 2 ∣ n then
        heckeCharQuartic D π * heckeCharQuartic D (star π) * heckeSumQuartic D (n / p ^ 2)
      else 0 := by
    split_ifs with hp2'
    · rw [sum_filter_dvd_normSet hp0 (n / p ^ 2) n
        (by rw [NTKB.HardyWright.norm_natCast']; norm_cast; exact Nat.mul_div_cancel' hp2')
        (heckeCharQuartic D), heckeSumQuartic, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun w _ => ?_)
      rw [← hmul, heckeCharQuartic_mul, heckeCharQuartic_mul]
    · apply Finset.sum_eq_zero
      intro z hz
      exfalso
      rw [Finset.mem_filter] at hz
      have hzn := mem_normSet_finset.1 hz.1
      obtain ⟨w, rfl⟩ := hz.2
      apply hp2'
      have : ((p ^ 2 : ℕ) : ℤ) ∣ (n : ℤ) := by
        rw [← hzn, Zsqrtd.norm_mul, NTKB.HardyWright.norm_natCast']; exact dvd_mul_right _ _
      exact_mod_cast this
  rw [hC] at key
  have hH : heckeSumQuartic D n = ∑ z ∈ S, heckeCharQuartic D z := rfl
  rw [← hH] at key
  linear_combination key

end NTKB.IrelandRosen.CM
