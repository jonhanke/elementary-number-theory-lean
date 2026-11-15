/-
Ireland–Rosen, Chapter 15, §15.2: the corollary to Proposition 15.2.3 and the congruence
h(-p) ≡ -2 B_{(p+1)/2} (mod p) for primes p ≡ 3 (mod 4), p > 3, in terms of Jacobi's expression
for the class number.
-/
import NTKB.IrelandRosen.R4.Bernoulli.Voronoi
import NTKB.IrelandRosen.R4.Bernoulli.Kummer
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Class numbers and Bernoulli numbers (Ireland–Rosen, §15.2)

For a prime `p ≡ 3 (mod 4)`, `p > 3`, let `m = (p + 1)/2`. Ireland and Rosen derive from the
Voronoi congruence with `n = p`, `a = 2` that `2 (2 - (2/p)) B_m ≡ -∑_{j < p/2} (j/p) (mod p)`
(`two_mul_two_sub_legendreSym_mul_bernoulli`), and, with the class number formula
`h(-p) = (2 - (2/p))⁻¹ ∑_{j < p/2} (j/p)` (which they cite), that `h(-p) ≡ -2 B_m (mod p)`.

Here the class number enters through Jacobi's expression `h_J(p) = -(1/p) ∑_{j=1}^{p-1} j (j/p)`
(`jacobiClassNumber`): we prove `(2 - (2/p)) h_J(p) = ∑_{j < p/2} (j/p)`
(`two_sub_legendreSym_mul_jacobiClassNumber`) and `h_J(p) ≡ -2 B_m (mod p)`
(`jacobiClassNumber_pModEq`), unconditionally. That `h_J(p)` is the class number of `ℚ(√-p)` is
Jacobi's formula, Davenport §6 (19), proved in `NTKB.Davenport.classNumber_eq_jacobi` from two
named inputs; the congruence for the class number itself is
`NTKB.IrelandRosen.classNumber_pModEq_bernoulli` (file `ClassNumberField.lean`).
-/

namespace NTKB.IrelandRosen

open Finset

/-- Jacobi's expression `-(1/p) ∑_{j=1}^{p-1} j (j/p)` for the class number of `ℚ(√-p)`. -/
noncomputable def jacobiClassNumber (p : ℕ) [Fact p.Prime] : ℚ :=
  -(1 / (p : ℚ)) * ∑ j ∈ Ico 1 p, (j : ℚ) * legendreSym p j

section Helpers

variable {p : ℕ} [Fact p.Prime]

private lemma leg_sub (hp : p % 4 = 3) (a : ℤ) :
    legendreSym p ((p : ℤ) - a) = - legendreSym p a := by
  have hp2 : p ≠ 2 := by omega
  have h1 : legendreSym p ((p : ℤ) - a) = legendreSym p (-a) := by
    rw [legendreSym.mod p ((p : ℤ) - a), legendreSym.mod p (-a)]
    congr 1
    exact (Int.modEq_iff_dvd.2 ⟨-1, by ring⟩ : ((p : ℤ) - a) ≡ -a [ZMOD p])
  rw [h1, legendreSym.at_neg hp2, ZMod.χ₄_nat_three_mod_four hp]
  simp

private lemma leg_two_sq (hp : p % 4 = 3) :
    legendreSym p 2 * legendreSym p 2 = 1 := by
  have h2 : ((2 : ℤ) : ZMod p) ≠ 0 := by
    intro h
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd 2 p).1 h
    have := Int.le_of_dvd (by norm_num) this
    omega
  rcases legendreSym.eq_one_or_neg_one p h2 with h | h <;> simp [h]

omit [Fact p.Prime] in
private lemma sum_Ico_reflect (hp : p % 2 = 1) (g : ℕ → ℤ) :
    ∑ j ∈ Ico ((p + 1) / 2) p, g j = ∑ i ∈ Ico 1 ((p + 1) / 2), g (p - i) := by
  symm
  refine Finset.sum_nbij' (fun i => p - i) (fun j => p - j) ?_ ?_ ?_ ?_ ?_
  · intro i hi; simp only [mem_Ico] at hi ⊢; omega
  · intro i hi; simp only [mem_Ico] at hi ⊢; omega
  · intro i hi; simp only [mem_Ico] at hi; omega
  · intro i hi; simp only [mem_Ico] at hi; omega
  · intro i hi; rfl

omit [Fact p.Prime] in
private lemma sum_Ico_split (hp : p % 4 = 3) (F : ℕ → ℤ) :
    ∑ j ∈ Ico 1 p, F j =
      ∑ k ∈ Ico 1 ((p + 1) / 2), F (2 * k) + ∑ k ∈ Ico 1 ((p + 1) / 2), F (p - 2 * k) := by
  have hU : Ico 1 p = (Ico 1 ((p + 1) / 2)).image (fun k => 2 * k) ∪
      (Ico 1 ((p + 1) / 2)).image (fun k => p - 2 * k) := by
    ext j
    simp only [mem_Ico, mem_union, mem_image]
    constructor
    · intro hj
      by_cases hev : j % 2 = 0
      · left; exact ⟨j / 2, by omega, by omega⟩
      · right; exact ⟨(p - j) / 2, by omega, by omega⟩
    · rintro (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩) <;> omega
  have hdisj : Disjoint ((Ico 1 ((p + 1) / 2)).image (fun k => 2 * k))
      ((Ico 1 ((p + 1) / 2)).image (fun k => p - 2 * k)) := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    simp only [mem_image, mem_Ico] at h1 h2
    obtain ⟨k, hk, rfl⟩ := h1
    obtain ⟨l, hl, hl2⟩ := h2
    omega
  rw [hU, sum_union hdisj, sum_image, sum_image]
  · intro x hx y hy hxy; simp only [mem_coe, mem_Ico] at hx hy; simp only at hxy; omega
  · intro x hx y hy hxy; simp only [mem_coe, mem_Ico] at hx hy; simp only at hxy; omega

private lemma int_identity (hp : p % 4 = 3) :
    (2 - legendreSym p 2) * (-∑ j ∈ Ico 1 p, (j : ℤ) * legendreSym p j) =
      p * ∑ j ∈ Ico 1 ((p + 1) / 2), legendreSym p j := by
  have hε := leg_two_sq (p := p) hp
  have hp1 : p % 2 = 1 := by omega
  set ε := legendreSym p 2 with hεdef
  set T := ∑ j ∈ Ico 1 p, (j : ℤ) * legendreSym p j with hT
  set W := ∑ j ∈ Ico 1 ((p + 1) / 2), (j : ℤ) * legendreSym p j with hW
  set A := ∑ j ∈ Ico 1 ((p + 1) / 2), legendreSym p j with hA
  have e1 : T = 2 * W - p * A := by
    have := sum_Ico_consecutive (fun j : ℕ => (j : ℤ) * legendreSym p j)
      (show 1 ≤ (p + 1) / 2 by omega) (show (p + 1) / 2 ≤ p by omega)
    rw [hT, ← this, sum_Ico_reflect hp1]
    have : ∑ i ∈ Ico 1 ((p + 1) / 2), (((p - i : ℕ) : ℤ)) * legendreSym p ((p - i : ℕ) : ℤ) =
        ∑ i ∈ Ico 1 ((p + 1) / 2), (-(p : ℤ) * legendreSym p i + i * legendreSym p i) := by
      refine sum_congr rfl fun i hi => ?_
      have hi' : i ≤ p := by simp only [mem_Ico] at hi; omega
      push_cast [Nat.cast_sub hi']
      rw [leg_sub hp]
      ring
    rw [this, sum_add_distrib, ← mul_sum, hW, hA]
    ring
  have e2 : T = 4 * ε * W - ε * p * A := by
    rw [hT, sum_Ico_split hp]
    have : ∀ k ∈ Ico 1 ((p + 1) / 2),
        ((2 * k : ℕ) : ℤ) * legendreSym p ((2 * k : ℕ) : ℤ) +
          ((p - 2 * k : ℕ) : ℤ) * legendreSym p ((p - 2 * k : ℕ) : ℤ) =
        4 * ε * ((k : ℤ) * legendreSym p k) - ε * p * legendreSym p k := by
      intro k hk
      have hk' : 2 * k ≤ p := by simp only [mem_Ico] at hk; omega
      push_cast [Nat.cast_sub hk']
      rw [leg_sub hp, legendreSym.mul, hεdef]
      ring
    rw [← sum_add_distrib, sum_congr rfl this, sum_sub_distrib, hW, hA, mul_sum, mul_sum]
  linear_combination (-ε * (2 * ε)) * e1 + ε * e2 + (2 * T + p * A) * hε

end Helpers

/-- For `p ≡ 3 (mod 4)`: `(2 - (2/p)) h_J(p) = ∑_{1 ≤ j < p/2} (j/p)` (the form of the class
number formula used by Ireland–Rosen, §15.2). -/
@[kb "irelandrosen1990" "§15.2, class number formula h = (2 - (2/p))⁻¹ ∑_{j<p/2} (j/p)"]
theorem two_sub_legendreSym_mul_jacobiClassNumber (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) :
    (2 - legendreSym p 2 : ℚ) * jacobiClassNumber p =
      ∑ j ∈ Ico 1 ((p + 1) / 2), (legendreSym p j : ℚ) := by
  have h := congrArg (Int.cast : ℤ → ℚ) (int_identity (p := p) hp)
  push_cast at h
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  unfold jacobiClassNumber
  field_simp
  linarith

/-- **Ireland–Rosen, §15.2, Corollary to Proposition 15.2.3.** For a prime `p ≡ 3 (mod 4)`,
`p > 3`, and `m = (p+1)/2`: `2 (2 - (2/p)) B_m ≡ -∑_{1 ≤ j < p/2} (j/p) (mod p)`. -/
@[kb "irelandrosen1990" "§15.2, Corollary to Proposition 15.2.3"]
theorem two_mul_two_sub_legendreSym_mul_bernoulli (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3)
    (hp3 : 3 < p) :
    PModEq p 1 (2 * (2 - legendreSym p 2 : ℚ) * bernoulli ((p + 1) / 2))
      (-∑ j ∈ Ico 1 ((p + 1) / 2), (legendreSym p j : ℚ)) := by
  have hp2 : p ≠ 2 := by omega
  have hp1 : p % 2 = 1 := by omega
  have hmeven : Even ((p + 1) / 2) := ⟨(p + 1) / 4, by omega⟩
  have hm0 : (p + 1) / 2 ≠ 0 := by omega
  have hpm : ¬ p - 1 ∣ (p + 1) / 2 := fun h => by
    have := Nat.le_of_dvd (by omega) h
    omega
  have hV := not_dvd_den_bernoulli hmeven hpm
  have hvor := voronoi_congruence hmeven hm0 (a := 2) (n := p)
    ((Nat.coprime_primes Nat.prime_two (Fact.out : p.Prime)).2 (by omega))
  have hz := (ZMod.intCast_eq_intCast_iff _ _ p).2 hvor
  -- the Voronoi sum
  have hvs : voronoiSum ((p + 1) / 2) 2 p = ∑ j ∈ Ico ((p + 1) / 2) p, (j : ℤ) ^ ((p + 1) / 2 - 1) := by
    unfold voronoiSum
    rw [← sum_Ico_consecutive _ (show 1 ≤ (p + 1) / 2 by omega) (show (p + 1) / 2 ≤ p by omega)]
    have h0 : ∑ j ∈ Ico 1 ((p + 1) / 2), (j : ℤ) ^ ((p + 1) / 2 - 1) * ((j * 2 / p : ℕ) : ℤ) = 0 := by
      refine sum_eq_zero fun j hj => ?_
      simp only [mem_Ico] at hj
      rw [Nat.div_eq_of_lt (a := j * 2) (b := p) (by omega)]
      simp
    rw [h0, zero_add]
    refine sum_congr rfl fun j hj => ?_
    simp only [mem_Ico] at hj
    rw [Nat.div_eq_of_lt_le (k := 1) (m := j * 2) (n := p) (by omega) (by omega)]
    simp
  have hupper : ∑ j ∈ Ico ((p + 1) / 2) p, legendreSym p j =
      -∑ j ∈ Ico 1 ((p + 1) / 2), legendreSym p j := by
    rw [sum_Ico_reflect hp1 (fun j => legendreSym p j), ← sum_neg_distrib]
    refine sum_congr rfl fun i hi => ?_
    have hi' : i ≤ p := by simp only [mem_Ico] at hi; omega
    push_cast [Nat.cast_sub hi']
    exact leg_sub hp _
  have hpow : ∀ j : ℤ, ((legendreSym p j : ℤ) : ZMod p) = (j : ZMod p) ^ ((p + 1) / 2 - 1) := by
    intro j
    rw [legendreSym.eq_pow]
    congr 1
    omega
  obtain ⟨A, hAdef⟩ : ∃ A : ℤ, A = ∑ j ∈ Ico 1 ((p + 1) / 2), legendreSym p j := ⟨_, rfl⟩
  have hS : ((voronoiSum ((p + 1) / 2) 2 p : ℤ) : ZMod p) = -(A : ZMod p) := by
    have : ((∑ j ∈ Ico ((p + 1) / 2) p, (j : ℤ) ^ ((p + 1) / 2 - 1) : ℤ) : ZMod p) =
        ((∑ j ∈ Ico ((p + 1) / 2) p, legendreSym p j : ℤ) : ZMod p) := by
      push_cast
      refine sum_congr rfl fun j _ => ?_
      rw [hpow]
      simp
    rw [hvs, this, hupper, ← hAdef]
    simp
  have he : ((legendreSym p 2 : ℤ) : ZMod p) = 2 ^ ((p + 1) / 2 - 1) := by
    rw [hpow]; simp
  have hee : (2 : ZMod p) ^ ((p + 1) / 2 - 1) * 2 ^ ((p + 1) / 2 - 1) = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod p) (leg_two_sq (p := p) hp)
    push_cast at this
    rwa [he] at this
  have h2m : (2 : ZMod p) * (((p + 1) / 2 : ℕ) : ZMod p) = 1 := by
    have : ((2 * ((p + 1) / 2) : ℕ) : ZMod p) = ((p + 1 : ℕ) : ZMod p) := by
      congr 1; omega
    push_cast at this
    rw [this]; simp
  have hpw : (2 : ZMod p) ^ ((p + 1) / 2) = 2 * 2 ^ ((p + 1) / 2 - 1) := by
    rw [← pow_succ']; congr 1; omega
  have key : ((2 * (2 - legendreSym p 2) * (bernoulli ((p + 1) / 2)).num +
      ((bernoulli ((p + 1) / 2)).den : ℤ) * A : ℤ) : ZMod p) = 0 := by
    simp only [Int.cast_add, Int.cast_mul, Int.cast_sub, Int.cast_pow, Int.cast_one,
      Int.cast_natCast, Int.cast_ofNat, Nat.cast_ofNat] at hz ⊢
    rw [hS, hpw] at hz
    rw [he]
    linear_combination (2 * (2 : ZMod p) ^ ((p + 1) / 2 - 1)) * hz +
      (-4 * ((bernoulli ((p + 1) / 2)).num : ZMod p) -
        2 * (((p + 1) / 2 : ℕ) : ZMod p) * ((bernoulli ((p + 1) / 2)).den : ZMod p) * (A : ZMod p))
        * hee +
      (-((bernoulli ((p + 1) / 2)).den : ZMod p) * (A : ZMod p)) * h2m
  obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 key
  have hcq : (2 * (2 - (legendreSym p 2 : ℚ)) * ((bernoulli ((p + 1) / 2)).num : ℚ) +
      ((bernoulli ((p + 1) / 2)).den : ℚ) * (A : ℚ)) = p * c := by exact_mod_cast hc
  have hAq : (∑ j ∈ Ico 1 ((p + 1) / 2), (legendreSym p j : ℚ)) = (A : ℚ) := by
    rw [hAdef]; push_cast; rfl
  rw [hAq]
  have hVq : ((bernoulli ((p + 1) / 2)).den : ℚ) ≠ 0 := by exact_mod_cast (bernoulli _).den_nz
  refine pModEq_iff.mpr ⟨c * ((bernoulli ((p + 1) / 2)).den : ℚ)⁻¹,
    (isPIntegral_intCast c).mul (isPIntegral_natCast_inv hV), ?_⟩
  have hBV : bernoulli ((p + 1) / 2) * ((bernoulli ((p + 1) / 2)).den : ℚ) =
      ((bernoulli ((p + 1) / 2)).num : ℚ) := Rat.mul_den_eq_num _
  field_simp
  linear_combination hcq + (2 * (2 - (legendreSym p 2 : ℚ))) * hBV

/-- **Ireland–Rosen, §15.2: `h(-p) ≡ -2 B_{(p+1)/2} (mod p)`**, for a prime `p ≡ 3 (mod 4)`,
`p > 3`, with the class number in Jacobi's form `h_J(p) = -(1/p) ∑_{j=1}^{p-1} j (j/p)`. -/
@[kb "irelandrosen1990" "§15.2, h(-p) ≡ -2 B_{(p+1)/2} (mod p)"]
theorem jacobiClassNumber_pModEq (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) (hp3 : 3 < p) :
    PModEq p 1 (jacobiClassNumber p) (-2 * bernoulli ((p + 1) / 2)) := by
  have h1 := two_sub_legendreSym_mul_jacobiClassNumber p hp
  obtain ⟨z, hz, hzeq⟩ := pModEq_iff.mp (two_mul_two_sub_legendreSym_mul_bernoulli p hp hp3)
  have hunit : ¬ (p : ℤ) ∣ (2 - legendreSym p 2) := by
    have h2 : ((2 : ℤ) : ZMod p) ≠ 0 := by
      intro h
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd 2 p).1 h
      have := Int.le_of_dvd (by norm_num) this
      omega
    intro hd
    rcases legendreSym.eq_one_or_neg_one p h2 with h | h <;> rw [h] at hd <;>
      have := Int.le_of_dvd (by norm_num) hd <;> omega
  have hne : (((2 - legendreSym p 2 : ℤ)) : ℚ) ≠ 0 := by
    intro h
    exact hunit (by rw [Int.cast_eq_zero.mp h]; exact dvd_zero _)
  refine pModEq_iff.mpr ⟨(((2 - legendreSym p 2 : ℤ)) : ℚ)⁻¹ * z,
    (isPIntegral_intCast_inv hunit).mul hz, ?_⟩
  push_cast at hne ⊢
  field_simp
  linear_combination h1 + hzeq

end NTKB.IrelandRosen
