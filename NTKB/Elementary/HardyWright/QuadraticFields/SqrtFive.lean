/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.QuadraticFields.QuadInt
import NTKB.Elementary.HardyWright.QuadraticFields.NormEuclidean
import NTKB.Elementary.HardyWright.ContinuedFractions.Fibonacci
import Mathlib.Util.Superscript
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Algebra.Order.Star.Real

/-!
# The field `k(√5)` (Hardy–Wright § 15.4)

The integers of `k(√5)` are `a + bω`, `ω = (1 + √5)/2`, here Mathlib's `QuadraticAlgebra ℤ 1 1`
(`ω² = 1 + ω`), with norm `N(a + bω) = a² + ab - b²`; `√5 = 2ω - 1`.

* `instEuclideanDomainGold`: `k(√5)` is Euclidean (Theorem 248, `m = 5`), hence simple.
* Theorem 257 (`gold_units`, `gold_prime_iff`): the unities of `k(√5)` are `±ω^n`, `n ∈ ℤ`; the primes
  are `√5`, the rational primes `5n ± 2`, and the factors `a + bω` of the rational primes `5n ± 1`
  (and the associates of these numbers).
* Theorem 258 (`gold_fermat_p`, `gold_fermat_q`, `gold_fermat_p'`, `gold_fermat`): the analogues
  (15.4.4)–(15.4.7) of Fermat's theorem.
-/

namespace NTKB.HardyWright

open QuadraticAlgebra
open scoped goldenRatio

/-- The integers `a + bω` of `k(√5)`. -/
abbrev ZGold := QuadraticAlgebra ℤ 1 1

instance factGold : Fact (∀ r : ℚ, r ^ 2 ≠ ((1 : ℤ) : ℚ) + ((1 : ℤ) : ℚ) * r) :=
  ⟨fun r hr ↦ not_isSquare_of_between (k := 5) (n := 2) (by norm_num) (by norm_num) (by norm_num)
    ⟨2 * r - 1, by push_cast at hr; linear_combination (-4) * hr⟩⟩

lemma gold_norm (z : ZGold) : norm z = z.re ^ 2 + z.re * z.im - z.im ^ 2 := by
  rw [norm_def]; ring

lemma gold_norm_mk (x y : ℤ) : norm (⟨x, y⟩ : ZGold) = x ^ 2 + x * y - y ^ 2 := gold_norm _

lemma gold_round (ξ : QuadraticAlgebra ℚ ((1 : ℤ) : ℚ) ((1 : ℤ) : ℚ)) :
    ∃ q : ZGold, |norm (ξ - algebraMap _ _ q)| < 1 := by
  set y := round ξ.im
  set x := round (ξ.re + (ξ.im - y) / 2)
  refine ⟨⟨x, y⟩, ?_⟩
  have h1 := sq_le_quarter (abs_sub_round (ξ.re + (ξ.im - y) / 2))
  have h2 := sq_le_quarter (abs_sub_round ξ.im)
  rw [norm_def, abs_lt]
  simp only [QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub,
    QuadraticAlgebra.Int.re_algebraMap, QuadraticAlgebra.Int.im_algebraMap]
  push_cast
  constructor <;> nlinarith [sq_nonneg (ξ.re + (ξ.im - y) / 2 - x), sq_nonneg (ξ.im - y)]

/-- `k(√5)` is Euclidean (Theorem 248, `m = 5`); `ℤ[ω]` is a Euclidean domain. -/
noncomputable instance instEuclideanDomainGold : EuclideanDomain ZGold :=
  euclideanDomainOfNorm ZGold QuadraticAlgebra.norm (map_mul QuadraticAlgebra.norm)
    (fun _ h ↦ qa_norm_eq_zero h) (exists_sub_mul_lt_of_round gold_round)

/-- The real embedding `a + bω ↦ a + bφ`. -/
noncomputable def goldToReal : ZGold →ₐ[ℤ] ℝ :=
  QuadraticAlgebra.lift ⟨φ, by
    rw [← sq, Real.goldenRatio_sq]; simp; ring⟩

lemma goldToReal_apply (z : ZGold) : goldToReal z = z.re + z.im * φ := by
  simp [goldToReal, QuadraticAlgebra.lift_apply_apply, zsmul_eq_mul]

lemma goldToReal_injective : Function.Injective goldToReal := by
  intro z w h
  rw [goldToReal_apply, goldToReal_apply] at h
  have hi : z.im = w.im := by
    by_contra hne
    have hne' : ((z.im : ℝ) - w.im) ≠ 0 := by exact_mod_cast sub_ne_zero.2 hne
    have hne'' : ((w.im : ℝ) - z.im) ≠ 0 := fun h0 ↦ hne' (by linarith)
    apply Real.goldenRatio_irrational
    refine ⟨(z.re - w.re : ℚ) / (w.im - z.im), ?_⟩
    push_cast
    rw [div_eq_iff hne'']
    linear_combination h
  have hr : z.re = w.re := by
    rw [hi] at h
    exact_mod_cast add_right_cancel h
  ext <;> assumption

/-- `ω` as a unity, with inverse `ω - 1`. -/
def omegaUnit : ZGold ˣ where
  val := ⟨0, 1⟩
  inv := ⟨-1, 1⟩
  val_inv := by ext <;> simp
  inv_val := by ext <;> simp

lemma goldToReal_omega : goldToReal (omegaUnit : ZGold) = φ := by
  rw [goldToReal_apply]; simp [omegaUnit]

lemma goldToReal_zpow (n : ℤ) : goldToReal ((omegaUnit ^ n : ZGoldˣ) : ZGold) = φ ^ n := by
  let f : ZGoldˣ →* ℝˣ := Units.map goldToReal.toRingHom.toMonoidHom
  have hf : ∀ u : ZGoldˣ, ((f u : ℝˣ) : ℝ) = goldToReal (u : ZGold) := fun u ↦ rfl
  rw [← hf, map_zpow, Units.val_zpow_eq_zpow_val, hf, goldToReal_omega]

/-- As in § 14.5 (i): there is no unity strictly between `1` and `ω`. -/
lemma gold_not_unit_between {ε : ZGold} (hε : IsUnit ε) (h1 : 1 < goldToReal ε)
    (h2 : goldToReal ε < φ) : False := by
  have hN := qa_isUnit_iff.1 hε
  rw [goldToReal_apply] at h1 h2
  set x := ε.re
  set y := ε.im
  have hφ := Real.goldenRatio_sq
  have hφ1 := Real.one_lt_goldenRatio
  have hφ2 := Real.goldenRatio_lt_two
  -- the conjugate `x + yψ` satisfies `(x + yφ)(x + yψ) = ±1`
  have hN' : ((x : ℝ) + y * φ) * (x + y * (1 - φ)) = 1 ∨
      ((x : ℝ) + y * φ) * (x + y * (1 - φ)) = -1 := by
    have : (x ^ 2 + x * y - y ^ 2 : ℤ) = 1 ∨ (x ^ 2 + x * y - y ^ 2 : ℤ) = -1 := by
      have h' := Int.natAbs_eq (norm ε)
      rw [hN, gold_norm] at h'
      exact_mod_cast h'
    rcases this with h | h
    · left; have := congrArg (Int.cast : ℤ → ℝ) h; push_cast at this; nlinarith
    · right; have := congrArg (Int.cast : ℤ → ℝ) h; push_cast at this; nlinarith
  have hc : -1 < (x : ℝ) + y * (1 - φ) ∧ (x : ℝ) + y * (1 - φ) < 1 := by
    rcases hN' with h | h <;> constructor <;> nlinarith
  -- `y√5 = ε - ε'` and `2x + y = ε + ε'`
  have hy0 : (0 : ℝ) < y * (2 * φ - 1) := by nlinarith [hc.2]
  have hy1 : (y : ℝ) * (2 * φ - 1) < 1 + φ := by nlinarith [hc.1]
  have h5 : (0 : ℝ) < 2 * φ - 1 := by linarith
  have hy : y = 1 := by
    have hy0' : (0 : ℝ) < y := by
      by_contra h; push Not at h; nlinarith
    have hy1' : (y : ℝ) < 2 := by
      by_contra h; push Not at h; nlinarith
    have : (0 : ℤ) < y := by exact_mod_cast hy0'
    have : y < 2 := by exact_mod_cast hy1'
    omega
  rw [hy] at h1 h2 hc
  push_cast at h1 h2 hc
  have : (x : ℝ) < 1 := by linarith
  have : (-1 : ℝ) < x := by linarith [hc.1]
  have hx : x = 0 := by
    have : x < 1 := by exact_mod_cast ‹(x : ℝ) < 1›
    have : -1 < x := by exact_mod_cast ‹(-1 : ℝ) < x›
    omega
  rw [hx] at h2
  push_cast at h2
  linarith

/-- **Theorem 257**, unities: the unities of `k(√5)` are the numbers `±ω^n`, `n ∈ ℤ`. -/
@[kb "hardywright2008" "Thm 257, p. 307"]
theorem gold_units (u : ZGoldˣ) : ∃ n : ℤ, u = omegaUnit ^ n ∨ u = -omegaUnit ^ n := by
  have hpos : ∀ v : ZGoldˣ, 0 < goldToReal (v : ZGold) → ∃ n : ℤ, v = omegaUnit ^ n := by
    intro v hv
    obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow hv Real.one_lt_goldenRatio
    refine ⟨n, ?_⟩
    set e := v * omegaUnit ^ (-n)
    have he : goldToReal (e : ZGold) = goldToReal (v : ZGold) / φ ^ n := by
      rw [Units.val_mul, map_mul, goldToReal_zpow, zpow_neg, div_eq_mul_inv]
    have hw : (0 : ℝ) < φ ^ n := zpow_pos Real.goldenRatio_pos n
    have he1 : 1 ≤ goldToReal (e : ZGold) := by
      rw [he, le_div_iff₀ hw]; linarith
    have he2 : goldToReal (e : ZGold) < φ := by
      have h3 := hn2
      rw [zpow_add_one₀ Real.goldenRatio_ne_zero] at h3
      rw [he, div_lt_iff₀ hw]
      linarith [mul_comm φ (φ ^ n)]
    rcases he1.lt_or_eq with he1 | he1
    · exact (gold_not_unit_between e.isUnit he1 he2).elim
    · have : (e : ZGold) = 1 := goldToReal_injective (by rw [← he1, map_one])
      have he' : e = 1 := Units.ext this
      calc v = e * omegaUnit ^ n := by simp [e]
        _ = omegaUnit ^ n := by rw [he', one_mul]
  have h0 : goldToReal (u : ZGold) ≠ 0 := fun h0 ↦ by
    have := congrArg goldToReal (Units.mul_inv u)
    rw [map_mul, h0, zero_mul, map_one] at this
    exact zero_ne_one this
  rcases h0.lt_or_gt with h | h
  · obtain ⟨n, hn⟩ := hpos (-u) (by rw [Units.val_neg, map_neg]; linarith)
    exact ⟨n, Or.inr (by rw [← hn, neg_neg])⟩
  · obtain ⟨n, hn⟩ := hpos u h
    exact ⟨n, Or.inl hn⟩

/-- `√5 = 2ω - 1`. -/
def sqrtFive : ZGold := ⟨-1, 2⟩

lemma sqrtFive_sq : sqrtFive * sqrtFive = 5 := by ext <;> simp [sqrtFive]

lemma gold_natAbs_norm_sqrtFive : (norm sqrtFive).natAbs = 5 := by
  rw [gold_norm]; simp [sqrtFive]

/-- `a² + ab - b²` is never `±2 (mod 5)`. -/
lemma gold_norm_mod_five {x y : ℤ} {p : ℕ} (h : (x ^ 2 + x * y - y ^ 2).natAbs = p) :
    p % 5 ≠ 2 ∧ p % 5 ≠ 3 := by
  have key : ∀ r : ℕ, r = 2 ∨ r = 3 → p % 5 = r → False := by
    rintro r hr hp
    rcases Int.natAbs_eq (x ^ 2 + x * y - y ^ 2) with h' | h' <;> rw [h] at h' <;>
    · have := congrArg (Int.cast : ℤ → ZMod 5) h'
      push_cast at this
      rw [← ZMod.natCast_mod, hp] at this
      generalize (x : ZMod 5) = u at this
      generalize (y : ZMod 5) = v at this
      rcases hr with rfl | rfl <;> revert u v <;> decide
  exact ⟨fun h2 ↦ key 2 (Or.inl rfl) h2, fun h3 ↦ key 3 (Or.inr rfl) h3⟩

lemma gold_prime_of_natAbs_norm_prime {π : ZGold} (h : (norm π).natAbs.Prime) : Prime π :=
  irreducible_iff_prime.1 (qa_irreducible_of_natAbs_norm_prime h)

/-- A rational prime `p ≠ 2` with `p ∣ c² - 5` for some `c` is not a prime of `k(√5)`. -/
lemma gold_not_prime_of_dvd_sq_sub_five {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {c : ℤ}
    (hc : (p : ℤ) ∣ c ^ 2 - 5) : ¬ Prime (p : ZGold) := by
  intro hpp
  have hdvd : (p : ZGold) ∣ (⟨c + 1, -2⟩ : ZGold) * ⟨c - 1, 2⟩ := by
    obtain ⟨t, ht⟩ := hc
    rw [show ((⟨c + 1, -2⟩ : ZGold) * ⟨c - 1, 2⟩) = ((c ^ 2 - 5 : ℤ) : ZGold) by
      ext <;> simp [sq] <;> ring, ht]
    push_cast
    exact dvd_mul_right _ _
  have hp1 : ¬ (p : ℤ) ∣ 2 := by
    intro h
    have := Int.le_of_dvd (by norm_num) h
    have h2 := hp.two_le
    have : p ≤ 2 := by exact_mod_cast this
    omega
  rcases hpp.dvd_or_dvd hdvd with ⟨t, ht⟩ | ⟨t, ht⟩
  · apply hp1
    have := congrArg QuadraticAlgebra.im ht
    simp at this
    exact ⟨-t.im, by linarith⟩
  · apply hp1
    have := congrArg QuadraticAlgebra.im ht
    simp at this
    exact ⟨t.im, by linarith⟩

/-- **Theorem 257**, primes: the primes of `k(√5)` are (1) `√5`, (2) the rational primes `5n ± 2`,
(3) the factors `a + bω` of the rational primes `p = 5n ± 1`, i.e. the integers with
`|a² + ab - b²| = p` (and the associates of these numbers). -/
@[kb "hardywright2008" "Thm 257, p. 307"]
theorem gold_prime_iff {π : ZGold} :
    Prime π ↔ Associated π sqrtFive ∨
      (∃ q : ℕ, q.Prime ∧ (q % 5 = 2 ∨ q % 5 = 3) ∧ Associated π (q : ZGold)) ∨
      ∃ p : ℕ, p.Prime ∧ (p % 5 = 1 ∨ p % 5 = 4) ∧ (norm π).natAbs = p := by
  constructor
  · intro hπ
    obtain ⟨p, hp, hπp, hcase⟩ := qa_prime_cases hπ
    rcases hcase with hN | hassoc
    · by_cases h5 : p = 5
      · left
        subst h5
        have h5' : ((5 : ℕ) : ZGold) = sqrtFive * sqrtFive := by rw [sqrtFive_sq]; rfl
        rw [h5'] at hπp
        exact qa_associated_of_dvd hπ.ne_zero ((hπ.dvd_or_dvd hπp).elim id id)
          (by rw [hN, gold_natAbs_norm_sqrtFive])
      · right; right
        refine ⟨p, hp, ?_, hN⟩
        have := gold_norm_mod_five (x := π.re) (y := π.im) (p := p)
          (by rw [gold_norm] at hN; exact hN)
        have h0 : p % 5 ≠ 0 := fun h0 ↦ h5 ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).1
          (Nat.dvd_of_mod_eq_zero h0)).symm
        omega
    · right; left
      refine ⟨p, hp, ?_, hassoc⟩
      have hpp : Prime (p : ZGold) := hassoc.prime hπ
      by_contra h
      have h5 : p ≠ 5 := by
        rintro rfl
        have h5' : ((5 : ℕ) : ZGold) = sqrtFive * sqrtFive := by rw [sqrtFive_sq]; rfl
        have := hpp.dvd_or_dvd (dvd_of_eq h5')
        obtain ⟨t, ht⟩ : ((5 : ℕ) : ZGold) ∣ sqrtFive := this.elim id id
        have := congrArg (fun z ↦ (norm z).natAbs) ht
        simp only [map_mul, Int.natAbs_mul, gold_natAbs_norm_sqrtFive,
          QuadraticAlgebra.norm_natCast, Int.natAbs_pow, Int.natAbs_natCast] at this
        norm_num at this
        omega
      have h14 : p % 5 = 1 ∨ p % 5 = 4 := by
        have h0 : p % 5 ≠ 0 := fun h0 ↦ h5 ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).1
          (Nat.dvd_of_mod_eq_zero h0)).symm
        omega
      have hp2 : p ≠ 2 := by rintro rfl; omega
      have := Fact.mk hp
      -- `5` is a quadratic residue of `p` (Theorem 97)
      have h5sq : (5 : ZMod p) ^ (p / 2) = 1 := (five_pow_half hp2).1 h14
      have hsq : IsSquare (5 : ZMod p) := by
        have h5ne : (5 : ZMod p) ≠ 0 := by
          intro h0
          have := (ZMod.natCast_eq_zero_iff 5 p).1 (by exact_mod_cast h0)
          exact h5 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 this)
        exact (ZMod.euler_criterion p h5ne).2 h5sq
      obtain ⟨c, hc⟩ := hsq
      refine gold_not_prime_of_dvd_sq_sub_five hp hp2 (c := c.val)
        ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 ?_) hpp
      push_cast
      rw [ZMod.natCast_zmod_val, hc]; ring
  · rintro (h | ⟨q, hq, hq5, h⟩ | ⟨p, hp, -, h⟩)
    · exact h.symm.prime (gold_prime_of_natAbs_norm_prime (by
        rw [gold_natAbs_norm_sqrtFive]; norm_num))
    · refine h.symm.prime (irreducible_iff_prime.1 ⟨fun hu ↦ ?_, fun α β hαβ ↦ ?_⟩)
      · rw [qa_isUnit_iff, QuadraticAlgebra.norm_natCast] at hu
        simp at hu
        exact hq.one_lt.ne' (by simpa using hu)
      · have hN := congrArg (fun z ↦ (QuadraticAlgebra.norm z).natAbs) hαβ
        simp only [map_mul, Int.natAbs_mul, QuadraticAlgebra.norm_natCast, Int.natAbs_pow,
          Int.natAbs_natCast] at hN
        obtain ⟨k, hk, hkq⟩ := (Nat.dvd_prime_pow hq).1 (Dvd.intro _ hN.symm)
        interval_cases k
        · exact Or.inl (qa_isUnit_iff.2 (by simpa using hkq))
        · exfalso
          have := gold_norm_mod_five (x := α.re) (y := α.im) (p := q)
            (by rw [gold_norm] at hkq; simpa using hkq)
          omega
        · right
          rw [hkq] at hN
          have : 0 < q ^ 2 := pow_pos hq.pos 2
          exact qa_isUnit_iff.2 (by nlinarith)
    · exact gold_prime_of_natAbs_norm_prime (by rw [h]; exact hp)

end NTKB.HardyWright
