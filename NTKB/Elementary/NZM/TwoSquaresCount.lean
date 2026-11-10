/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.NZM.Automorphs
import NTKB.Elementary.NZM.TwoSquares
import NTKB.Elementary.HardyWright.CompositeModuli.Roots

/-!
# The number of proper representations as a sum of two squares (Niven–Zuckerman–Montgomery, § 3.6)

**Theorem 3.21** (first part): for `n > 0`, `r(n) = 4 N(n)`, where `r(n)` is the number of proper
representations `n = x² + y²` (`gcd(x, y) = 1`) and `N(n)` the number of solutions of
`s² ≡ -1 (mod n)`. (The second part, `R(n) = ∑_{d² ∣ n} r(n/d²)`, is
`sumTwoSquaresCount_eq_sum_properSqRepCount`.)

We derive it from Theorem 3.27 for the form `x² + y²`: its automorphs number `w = 4` (Theorem 3.26),
every positive definite form of discriminant `-4` is equivalent to it (the reduced forms of
discriminant `-4`), and `h ↦ h/2` maps the `h` with `0 ≤ h < 2n`, `h² ≡ -4 (mod 4n)` bijectively onto
the solutions of `s² ≡ -1 (mod n)`. (The book argues directly with the same correspondence.)
`N(n)` is Hardy–Wright's `rootCount (X² + 1) n`.
-/

namespace NTKB.NZM

open NTKB.Davenport Polynomial

/-- `N(n)`: the number of solutions of `s² ≡ -1 (mod n)` (Hardy–Wright's root count of `X² + 1`). -/
noncomputable def negOneSqrtCount (n : ℕ) : ℕ := NTKB.HardyWright.rootCount (X ^ 2 + 1) n

lemma isPosDef_sumSq : IsPosDef (1, 0, 1) := by
  intro x y hxy
  simp only [formEval, zero_mul, add_zero, one_mul]
  rcases eq_or_ne x 0 with rfl | hx
  · have : y ≠ 0 := fun h ↦ hxy (by simp [h])
    positivity
  · positivity

lemma isReducedForm_sumSq : IsReducedForm (1, 0, 1) := Or.inr ⟨le_rfl, by norm_num, rfl⟩

lemma numAutomorphs_sumSq : numAutomorphs (1, 0, 1) = 4 :=
  (isReducedForm_sumSq.numAutomorphs_eq isPosDef_sumSq).1 rfl rfl

/-- Every positive definite form of discriminant `-4` is equivalent to `x² + y²`. -/
lemma formEquiv_sumSq_of_disc {g : ℤ × ℤ × ℤ} (hg : IsPosDef g) (hd : formDisc g = -4) :
    FormEquiv (1, 0, 1) g := by
  have hns : ¬IsSquare (formDisc g) := by
    rw [hd]; rintro ⟨r, hr⟩; nlinarith [mul_self_nonneg r]
  obtain ⟨g', hgg', hred⟩ := exists_formEquiv_isReducedForm g hns
  have hp' := hg.of_formEquiv hgg'
  have hd' : formDisc g' = -4 := by rw [hgg'.formDisc_eq, hd]
  obtain ⟨ha, hc, hb1, hb2, hac, hb0⟩ := hred.posDef_bounds hp'
  obtain ⟨a, b, c⟩ := g'
  simp only [formDisc] at hd' ha hc hb1 hb2 hac hb0
  have hb : b ^ 2 ≤ a ^ 2 := by nlinarith
  have ha1 : a = 1 := by nlinarith
  subst ha1
  have hb' : b = 0 ∨ b = 1 := by omega
  rcases hb' with rfl | rfl
  · have hc1 : c = 1 := by omega
    subst hc1
    exact formEquiv_symm hgg'
  · omega

lemma properRepCount_sumSq (n : ℕ) : properRepCount (1, 0, 1) n = properSqRepCount n := by
  have : properReps (1, 0, 1) n = ↑(properTwoSqRepSet n) := by
    ext ⟨x, y⟩
    rw [Finset.mem_coe, mem_properTwoSqRepSet]
    simp only [properReps, Set.mem_ofPred_eq, formEval, Int.isCoprime_iff_gcd_eq_one]
    constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩ <;> linear_combination h2
  rw [properRepCount, this, Nat.card_coe_set_eq, Set.ncard_coe_finset, properSqRepCount]

/-- An `h = 2s` with `0 ≤ s < n` and `n ∣ s² + 1` lies in `hSet (1, 0, 1) n`. -/
lemma two_mul_mem_hSet {n : ℕ} (hn : 0 < n) {s : ℤ} (hs0 : 0 ≤ s) (hsn : s < n)
    (hdvd : (n : ℤ) ∣ s ^ 2 + 1) : 2 * s ∈ hSet (1, 0, 1) n := by
  obtain ⟨k, hk⟩ := hdvd
  have hd : formDisc ((n : ℤ), 2 * s, k) = -4 := by simp only [formDisc]; linear_combination 4 * hk
  refine ⟨by omega, by omega, k, ?_, ?_⟩
  · simp only [formDisc]; linear_combination 4 * hk
  · refine formEquiv_sumSq_of_disc ((def_of_disc_neg (by rw [hd]; norm_num)).2.1 ?_) hd
    simp only; exact_mod_cast hn

/-- The members of `hSet (1, 0, 1) n` are even. -/
lemma even_of_mem_hSet {n : ℕ} {h : ℤ} (hh : h ∈ hSet (1, 0, 1) n) : 2 ∣ h := by
  obtain ⟨-, -, k, hk, -⟩ := hh
  simp only [formDisc] at hk
  rcases Int.even_or_odd h with ⟨r, hr⟩ | ⟨r, hr⟩
  · exact ⟨r, by omega⟩
  · exfalso; subst hr
    have : 2 * (2 * r ^ 2 + 2 * r) + 1 = 2 * (2 * n * k - 2) := by linear_combination hk
    omega

lemma hCount_sumSq {n : ℕ} (hn : 0 < n) : hCount (1, 0, 1) n = negOneSqrtCount n := by
  have : NeZero n := ⟨hn.ne'⟩
  unfold hCount negOneSqrtCount NTKB.HardyWright.rootCount
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun x ↦ ⟨2 * (x.1.val : ℤ), ?_⟩) ⟨?_, ?_⟩)
  · obtain ⟨x, hx⟩ := x
    simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one,
      eval_add, eval_pow, eval_X, eval_one] at hx
    refine two_mul_mem_hSet hn (by positivity) (by exact_mod_cast ZMod.val_lt x) ?_
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val]; exact hx
  · intro a b hab
    have h1 := congrArg Subtype.val hab
    simp only at h1
    have h2 : a.1.val = b.1.val := by omega
    exact Subtype.ext (ZMod.val_injective n h2)
  · rintro ⟨h, hh⟩
    obtain ⟨s, rfl⟩ := even_of_mem_hSet hh
    obtain ⟨h0, h1, k, hk, -⟩ := hh
    simp only [formDisc] at hk
    have hs0 : 0 ≤ s := by omega
    have hsn : s < n := by omega
    lift s to ℕ using hs0
    refine ⟨⟨(s : ZMod n), ?_⟩, ?_⟩
    · simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one,
        eval_add, eval_pow, eval_X, eval_one]
      have : ((s : ℤ) : ZMod n) ^ 2 + 1 = 0 := by
        have h' : ((s : ℤ) ^ 2 + 1 : ℤ) = (n : ℤ) * k := by linarith
        rw [← Int.cast_pow, ← Int.cast_one, ← Int.cast_add, h']
        simp
      exact_mod_cast this
    · apply Subtype.ext
      simp only
      rw [ZMod.val_natCast_of_lt (by exact_mod_cast hsn)]

/-- **Theorem 3.21** (first part). For `n > 0`, the number `r(n)` of proper representations of `n`
as `x² + y²` is `4 N(n)`, where `N(n)` is the number of solutions of `s² ≡ -1 (mod n)`. -/
@[kb "nivenzuckermanmontgomery" "Thm 3.21, p. 165"]
theorem properSqRepCount_eq_four_mul {n : ℕ} (hn : 0 < n) :
    properSqRepCount n = 4 * negOneSqrtCount n := by
  rw [← properRepCount_sumSq, properRepCount_eq_mul isPosDef_sumSq (by exact_mod_cast hn),
    numAutomorphs_sumSq, hCount_sumSq hn]

end NTKB.NZM
