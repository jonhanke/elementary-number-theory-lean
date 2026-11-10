/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Ch1to6.FormReduction
import NTKB.Elementary.HardyWright.Fermat.QuadraticResidues
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Int.GCD

/-!
# Binary quadratic forms (Niven–Zuckerman–Montgomery, §§ 3.4–3.5)

A binary quadratic form `ax² + bxy + cy²` is the coefficient triple `(a, b, c) : ℤ × ℤ × ℤ` of
`NTKB.Davenport.formDisc` / `formSubst` / `FormEquiv` (Davenport, Chapter 6); `formEval f x y` is its value.
Equivalence (Definition 3.7) is `FormEquiv`: `g(x, y) = f(m₁₁x + m₁₂y, m₂₁x + m₂₂y)` with `det M = 1`.

* Theorem 3.9 (least nonresidue): the least positive quadratic nonresidue of an odd prime `p` is `< 1 + √p`.
* Theorem 3.10: for a nonsquare discriminant, `a ≠ 0`, `c ≠ 0` and `f(x, y) = 0` only at `(0, 0)`.
* Definition 3.5, Theorem 3.11: indefinite / semidefinite / definite according to the sign of `d`.
* Theorem 3.12: a form of discriminant `d` exists if and only if `d ≡ 0, 1 (mod 4)`.
* Theorem 3.13: `n ≠ 0` is properly represented by some form of discriminant `d` if and only if
  `x² ≡ d (mod 4|n|)` is solvable. (For the "only if" part we move the representation to `(1, 0)` by a
  unimodular substitution, Theorems 3.15 and 3.17, instead of the book's Chinese remainder argument.)
* Corollary 3.14: for `d ≡ 0, 1 (mod 4)` and an odd prime `p`, some form of discriminant `d` represents `p`
  if and only if `d` is a square modulo `p`, i.e. `(d/p) = 1` when `p ∤ d`.
* Theorem 3.16: equivalence is an equivalence relation (symmetry is new; reflexivity and transitivity are
  Davenport's).
* Theorem 3.17: equivalent forms have the same discriminant, and a unimodular change of variables puts
  the (proper) representations of each `n` in one-to-one correspondence.
* Definition 3.8, Theorems 3.18, 3.19: reduced forms; every class of nonsquare discriminant contains one;
  bounds for `a`; finitely many reduced forms. Definition 3.9: the class number `H(d)`, finite.
-/

namespace NTKB.NZM

open NTKB.Davenport

/-! ### Theorem 3.9 -/

/-- **Theorem 3.9.** The least positive quadratic nonresidue `q` of an odd prime `p` satisfies
`q < 1 + √p`. (From the inequality `q² < p + q`, Hardy–Wright's note to § 6.7.) -/
@[kb "nivenzuckermanmontgomery" "Thm 3.9, p. 148"]
theorem least_nonresidue_lt_one_add_sqrt {p q : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hq0 : 0 < q)
    (hq : ¬IsSquare (q : ZMod p)) (hmin : ∀ r, 0 < r → r < q → IsSquare (r : ZMod p)) :
    (q : ℝ) < 1 + √(p : ℝ) := by
  have h := NTKB.HardyWright.sq_lt_add_of_least_nonresidue hp2 hq0 hq hmin
  have h' : ((q : ℝ) - 1) ^ 2 < p := by
    have : ((q ^ 2 : ℕ) : ℝ) < ((p + q : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq0
    nlinarith
  have := Real.lt_sqrt_of_sq_lt h'
  linarith

/-! ### Values of a form -/

/-- The value `f(x, y) = ax² + bxy + cy²` of the form `f = (a, b, c)`. -/
def formEval (f : ℤ × ℤ × ℤ) (x y : ℤ) : ℤ := f.1 * x ^ 2 + f.2.1 * x * y + f.2.2 * y ^ 2

/-- Formulas (3.7): the form `formSubst f α β γ δ` takes the value `f(αx + βy, γx + δy)`. -/
theorem formEval_formSubst (f : ℤ × ℤ × ℤ) (α β γ δ x y : ℤ) :
    formEval (formSubst f α β γ δ) x y = formEval f (α * x + β * y) (γ * x + δ * y) := by
  simp only [formEval, formSubst]; ring

/-- Completing the square (3.3): `4a f(x, y) = (2ax + by)² - d y²`. -/
theorem four_mul_formEval (f : ℤ × ℤ × ℤ) (x y : ℤ) :
    4 * f.1 * formEval f x y = (2 * f.1 * x + f.2.1 * y) ^ 2 - formDisc f * y ^ 2 := by
  simp only [formEval, formDisc]; ring

/-- The same with the roles of `a` and `c` exchanged: `4c f(x, y) = (2cy + bx)² - d x²`. -/
theorem four_mul_formEval' (f : ℤ × ℤ × ℤ) (x y : ℤ) :
    4 * f.2.2 * formEval f x y = (2 * f.2.2 * y + f.2.1 * x) ^ 2 - formDisc f * x ^ 2 := by
  simp only [formEval, formDisc]; ring

/-- If `d y² = m²` with `y ≠ 0` then `d` is a square. -/
lemma isSquare_of_mul_sq_eq_sq {d y m : ℤ} (hy : y ≠ 0) (h : d * y ^ 2 = m ^ 2) : IsSquare d := by
  have hdvd : y ^ 2 ∣ m ^ 2 := ⟨d, by rw [← h]; ring⟩
  obtain ⟨t, rfl⟩ := (Int.pow_dvd_pow_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hdvd
  refine ⟨t, ?_⟩
  have h2 : y ^ 2 * d = y ^ 2 * (t * t) := by linear_combination h
  exact mul_left_cancel₀ (pow_ne_zero 2 hy) h2

/-- **Theorem 3.10.** If the discriminant `d` of `f = ax² + bxy + cy²` is not a perfect square (in
particular `d ≠ 0`), then `a ≠ 0`, `c ≠ 0`, and `f(x, y) = 0` only for `x = y = 0`. -/
@[kb "nivenzuckermanmontgomery" "Thm 3.10, p. 150"]
theorem formEval_eq_zero_of_not_isSquare {f : ℤ × ℤ × ℤ} (hd : ¬IsSquare (formDisc f)) :
    f.1 ≠ 0 ∧ f.2.2 ≠ 0 ∧ ∀ x y, formEval f x y = 0 → x = 0 ∧ y = 0 := by
  have ha := fst_ne_zero_of_not_isSquare hd
  refine ⟨ha, snd_snd_ne_zero_of_not_isSquare hd, fun x y h ↦ ?_⟩
  by_cases hy : y = 0
  · subst hy
    simp only [formEval] at h
    have : f.1 * x ^ 2 = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' ha
    · exact ⟨pow_eq_zero_iff (by norm_num) |>.mp h', rfl⟩
  · exfalso
    have e := four_mul_formEval f x y
    rw [h, mul_zero] at e
    exact hd (isSquare_of_mul_sq_eq_sq (m := 2 * f.1 * x + f.2.1 * y) hy (by linarith))

/-! ### Definition 3.5 and Theorem 3.11 -/

/-- **Definition 3.5.** `f` is *indefinite* if it takes both positive and negative values. -/
def IsIndefinite (f : ℤ × ℤ × ℤ) : Prop := (∃ x y, 0 < formEval f x y) ∧ ∃ x y, formEval f x y < 0

/-- **Definition 3.5.** `f` is *positive semidefinite* if `f(x, y) ≥ 0` for all integers `x, y`. -/
def IsPosSemidef (f : ℤ × ℤ × ℤ) : Prop := ∀ x y, 0 ≤ formEval f x y

/-- **Definition 3.5.** `f` is *negative semidefinite* if `f(x, y) ≤ 0` for all integers `x, y`. -/
def IsNegSemidef (f : ℤ × ℤ × ℤ) : Prop := ∀ x y, formEval f x y ≤ 0

/-- **Definition 3.5.** `f` is *positive definite* if `f(x, y) > 0` for all `(x, y) ≠ (0, 0)`
(a positive semidefinite form vanishing only at `(0, 0)`). -/
def IsPosDef (f : ℤ × ℤ × ℤ) : Prop := ∀ x y, (x, y) ≠ (0, 0) → 0 < formEval f x y

/-- **Definition 3.5.** `f` is *negative definite* if `f(x, y) < 0` for all `(x, y) ≠ (0, 0)`. -/
def IsNegDef (f : ℤ × ℤ × ℤ) : Prop := ∀ x y, (x, y) ≠ (0, 0) → formEval f x y < 0

/-- **Theorem 3.11** (`d > 0`). A form of positive discriminant is indefinite. -/
@[kb "nivenzuckermanmontgomery" "Thm 3.11, p. 151"]
theorem isIndefinite_of_pos {f : ℤ × ℤ × ℤ} (hd : 0 < formDisc f) : IsIndefinite f := by
  obtain ⟨a, b, c⟩ := f
  simp only [formDisc] at hd
  have e1 : formEval (a, b, c) 1 0 = a := by simp [formEval]
  have e2 : formEval (a, b, c) b (-2 * a) = -a * (b ^ 2 - 4 * a * c) := by simp [formEval]; ring
  have e3 : formEval (a, b, c) 0 1 = c := by simp [formEval]
  have e4 : formEval (a, b, c) (-2 * c) b = -c * (b ^ 2 - 4 * a * c) := by simp [formEval]; ring
  rcases lt_trichotomy a 0 with ha | ha | ha
  · exact ⟨⟨_, _, by rw [e2]; nlinarith⟩, ⟨_, _, by rw [e1]; exact ha⟩⟩
  · subst ha
    rcases lt_trichotomy c 0 with hc | hc | hc
    · exact ⟨⟨_, _, by rw [e4]; nlinarith⟩, ⟨_, _, by rw [e3]; exact hc⟩⟩
    · subst hc
      have hb : b ≠ 0 := by rintro rfl; simp at hd
      have e5 : formEval (0, b, 0) 1 1 = b := by simp [formEval]
      have e6 : formEval (0, b, 0) 1 (-1) = -b := by simp [formEval]
      rcases lt_or_gt_of_ne hb with hb | hb
      · exact ⟨⟨_, _, by rw [e6]; linarith⟩, ⟨_, _, by rw [e5]; exact hb⟩⟩
      · exact ⟨⟨_, _, by rw [e5]; exact hb⟩, ⟨_, _, by rw [e6]; linarith⟩⟩
    · exact ⟨⟨_, _, by rw [e3]; exact hc⟩, ⟨_, _, by rw [e4]; nlinarith⟩⟩
  · exact ⟨⟨_, _, by rw [e1]; exact ha⟩, ⟨_, _, by rw [e2]; nlinarith⟩⟩

/-- **Theorem 3.11** (`d = 0`). A form of discriminant `0` is semidefinite but not definite. -/
@[kb "nivenzuckermanmontgomery" "Thm 3.11, p. 151"]
theorem semidef_not_def_of_disc_eq_zero {f : ℤ × ℤ × ℤ} (hd : formDisc f = 0) :
    (IsPosSemidef f ∨ IsNegSemidef f) ∧ ∃ x y, (x, y) ≠ (0, 0) ∧ formEval f x y = 0 := by
  obtain ⟨a, b, c⟩ := f
  simp only [formDisc] at hd
  by_cases ha : a = 0
  · subst ha
    have hb : b = 0 := by nlinarith
    subst hb
    have e : ∀ x y, formEval (0, 0, c) x y = c * y ^ 2 := fun x y ↦ by simp [formEval]
    refine ⟨?_, ⟨1, 0, by simp, by simp [formEval]⟩⟩
    rcases le_total 0 c with hc | hc
    · exact Or.inl fun x y ↦ by rw [e]; positivity
    · exact Or.inr fun x y ↦ by rw [e]; nlinarith [sq_nonneg y]
  · have key : ∀ x y, 4 * a * formEval (a, b, c) x y = (2 * a * x + b * y) ^ 2 := by
      intro x y
      have := four_mul_formEval (a, b, c) x y
      simp only [formDisc] at this
      rw [this, hd]; ring
    refine ⟨?_, ⟨b, -2 * a, by simp [ha], by simp only [formEval]; linear_combination (-a) * hd⟩⟩
    rcases lt_or_gt_of_ne ha with ha | ha
    · refine Or.inr fun x y ↦ ?_
      have := key x y
      nlinarith [sq_nonneg (2 * a * x + b * y)]
    · refine Or.inl fun x y ↦ ?_
      have := key x y
      nlinarith [sq_nonneg (2 * a * x + b * y)]

/-- **Theorem 3.11** (`d < 0`). If the discriminant is negative, `a` and `c` have the same sign, and
`f` is positive definite if `a > 0`, negative definite if `a < 0`. -/
@[kb "nivenzuckermanmontgomery" "Thm 3.11, p. 151"]
theorem def_of_disc_neg {f : ℤ × ℤ × ℤ} (hd : formDisc f < 0) :
    0 < f.1 * f.2.2 ∧ (0 < f.1 → IsPosDef f) ∧ (f.1 < 0 → IsNegDef f) := by
  have hnsq : ¬IsSquare (formDisc f) := by
    rintro ⟨r, hr⟩; nlinarith [mul_self_nonneg r]
  obtain ⟨ha0, -, hzero⟩ := formEval_eq_zero_of_not_isSquare hnsq
  have hac : 0 < f.1 * f.2.2 := by
    simp only [formDisc] at hd; nlinarith [sq_nonneg f.2.1]
  -- `4a f(x, y) > 0` away from the origin
  have hpos : ∀ x y, (x, y) ≠ (0, 0) → 0 < 4 * f.1 * formEval f x y := by
    intro x y hxy
    rw [four_mul_formEval]
    have h1 : 0 ≤ (2 * f.1 * x + f.2.1 * y) ^ 2 := sq_nonneg _
    by_cases hy : y = 0
    · subst hy
      have hx : x ≠ 0 := fun hx ↦ hxy (by simp [hx])
      have : 0 < (2 * f.1 * x + f.2.1 * 0) ^ 2 := by
        simp only [mul_zero, add_zero]
        exact lt_of_le_of_ne (sq_nonneg _)
          (Ne.symm (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero two_ne_zero ha0) hx)))
      nlinarith
    · have : 0 < y ^ 2 := by positivity
      nlinarith
  refine ⟨hac, fun ha x y hxy ↦ ?_, fun ha x y hxy ↦ ?_⟩
  · have := hpos x y hxy
    by_contra h; push Not at h; nlinarith
  · have := hpos x y hxy
    by_contra h; push Not at h; nlinarith

/-! ### Theorem 3.12 -/

/-- **Theorem 3.12.** There is a binary quadratic form with integral coefficients and discriminant `d`
if and only if `d ≡ 0` or `1 (mod 4)`. -/
@[kb "nivenzuckermanmontgomery" "Thm 3.12, p. 152"]
theorem exists_formDisc_eq_iff (d : ℤ) : (∃ f, formDisc f = d) ↔ d % 4 = 0 ∨ d % 4 = 1 := by
  constructor
  · rintro ⟨⟨a, b, c⟩, rfl⟩
    simp only [formDisc]
    rcases Int.even_or_odd b with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · have : (k + k) ^ 2 - 4 * a * c = 4 * (k ^ 2 - a * c) := by ring
      rw [this]; omega
    · have : (2 * k + 1) ^ 2 - 4 * a * c = 4 * (k ^ 2 + k - a * c) + 1 := by ring
      rw [this]; omega
  · rintro (h | h)
    · exact ⟨(1, 0, -(d / 4)), by simp only [formDisc]; omega⟩
    · exact ⟨(1, 1, -(d / 4)), by simp only [formDisc]; omega⟩

/-! ### Theorems 3.13 and Corollary 3.14 -/

/-- **Theorem 3.13.** Let `n ≠ 0`. Some binary quadratic form of discriminant `d` represents `n` properly
(`f(x, y) = n` with `(x, y) = 1`) if and only if `x² ≡ d (mod 4|n|)` has a solution. -/
@[kb "nivenzuckermanmontgomery" "Thm 3.13, p. 153"]
theorem exists_proper_rep_iff {n : ℤ} (_hn : n ≠ 0) (d : ℤ) :
    (∃ f x y, formDisc f = d ∧ IsCoprime x y ∧ formEval f x y = n) ↔
      ∃ b, b ^ 2 ≡ d [ZMOD 4 * |n|] := by
  constructor
  · rintro ⟨f, x, y, hd, ⟨u, v, huv⟩, hf⟩
    -- move the representation to `(1, 0)`: the substitution with first column `(x, y)`
    set g := formSubst f x (-v) y u
    have hg1 : g.1 = n := by
      rw [← hf]; simp only [g, formSubst, formEval]
    have hgd : formDisc g = d := by
      rw [formDisc_formSubst, ← hd]
      have : x * u - -v * y = 1 := by linear_combination huv
      rw [this]; ring
    refine ⟨g.2.1, ?_⟩
    rw [Int.modEq_iff_dvd]
    have : d - g.2.1 ^ 2 = 4 * n * (-g.2.2) := by
      rw [← hgd, ← hg1]; simp only [formDisc]; ring
    rw [this]
    exact Dvd.dvd.mul_right (mul_dvd_mul_left 4 (abs_dvd_self n)) _
  · rintro ⟨b, hb⟩
    have h1 : 4 * |n| ∣ b ^ 2 - d := (Int.modEq_iff_dvd.mp hb.symm)
    have h2 : 4 * n ∣ b ^ 2 - d := by
      rcases abs_choice n with h | h
      · rwa [h] at h1
      · rw [h, mul_neg, neg_dvd] at h1; exact h1
    obtain ⟨c, hc⟩ := h2
    refine ⟨(n, b, c), 1, 0, ?_, isCoprime_one_left, by simp [formEval]⟩
    simp only [formDisc]; linear_combination hc

/-- **Corollary 3.14.** Let `d ≡ 0` or `1 (mod 4)` and `p` an odd prime. Some binary quadratic form of
discriminant `d` represents `p` if and only if `d` is a square modulo `p`; for `p ∤ d` this is
`(d/p) = 1` (see `exists_rep_prime_iff_legendreSym`). -/
@[kb "nivenzuckermanmontgomery" "Cor 3.14, p. 153"]
theorem exists_rep_prime_iff {d : ℤ} (hd4 : d % 4 = 0 ∨ d % 4 = 1) {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) :
    (∃ f x y, formDisc f = d ∧ formEval f x y = p) ↔ IsSquare (d : ZMod p) := by
  constructor
  · rintro ⟨f, x, y, rfl, hf⟩
    have hp0 : ((p : ℤ) : ZMod p) = 0 := by simp
    by_cases hy : (y : ZMod p) = 0
    · -- `p ∣ y`; then `p ∤ x` (else `p² ∣ f(x, y) = p`), and we use `4c f = (2cy + bx)² - d x²`
      have hx : (x : ZMod p) ≠ 0 := by
        intro hx
        obtain ⟨x', rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd x p).mp hx
        obtain ⟨y', rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd y p).mp hy
        have e2 : formEval f (p * x') (p * y') = p * p * formEval f x' y' := by
          simp only [formEval]; ring
        have h : (p : ℤ) * p ∣ p := Dvd.intro _ (e2.symm.trans hf)
        have hp1 : (1 : ℤ) < p := by exact_mod_cast hp.out.one_lt
        have := Int.le_of_dvd (by positivity) h
        nlinarith
      have e := congrArg (Int.cast : ℤ → ZMod p) (four_mul_formEval' f x y)
      rw [hf] at e
      push_cast at e hp0
      rw [hp0, mul_zero] at e
      refine ⟨(2 * f.2.2 * y + f.2.1 * x) * (x : ZMod p)⁻¹, ?_⟩
      have : (formDisc f : ZMod p) * (x : ZMod p) ^ 2 = (2 * f.2.2 * y + f.2.1 * x) ^ 2 := by
        linear_combination e
      field_simp
      linear_combination this
    · have e := congrArg (Int.cast : ℤ → ZMod p) (four_mul_formEval f x y)
      rw [hf] at e
      push_cast at e hp0
      rw [hp0, mul_zero] at e
      refine ⟨(2 * f.1 * x + f.2.1 * y) * (y : ZMod p)⁻¹, ?_⟩
      have : (formDisc f : ZMod p) * (y : ZMod p) ^ 2 = (2 * f.1 * x + f.2.1 * y) ^ 2 := by
        linear_combination e
      field_simp
      linear_combination this
  · rintro ⟨r, hr⟩
    -- a square root `b` of `d` modulo `p` with `b ≡ d (mod 2)`
    have hpodd : (p : ℤ) % 2 = 1 := by
      have := hp.out.eq_one_or_self_of_dvd 2
      rcases Nat.Prime.eq_two_or_odd hp.out with h | h
      · exact absurd h hp2
      · exact_mod_cast h
    set b₀ : ℤ := (r.val : ℤ)
    set b : ℤ := if b₀ % 2 = d % 2 then b₀ else b₀ + p
    have hbr : (b : ZMod p) = r := by
      simp only [b, b₀]
      split_ifs <;> simp
    have hb2 : b % 2 = d % 2 := by
      simp only [b]; split_ifs with h
      · exact h
      · omega
    have hp_dvd : (p : ℤ) ∣ b ^ 2 - d := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [hbr, hr]; ring
    have h4_dvd : (4 : ℤ) ∣ b ^ 2 - d := by
      obtain ⟨k, hk⟩ : ∃ k, b = 2 * k + b % 2 := ⟨b / 2, by omega⟩
      have he : b % 2 = 0 ∨ b % 2 = 1 := by omega
      rcases he with he | he
      · rw [hk, he]
        have : (2 * k + 0) ^ 2 - d = 4 * k ^ 2 - d := by ring
        rw [this]; exact dvd_sub (dvd_mul_right _ _) (Int.dvd_of_emod_eq_zero (by omega))
      · rw [hk, he]
        have : (2 * k + 1) ^ 2 - d = 4 * (k ^ 2 + k) + (1 - d) := by ring
        rw [this]; exact dvd_add (dvd_mul_right _ _) (Int.dvd_of_emod_eq_zero (by omega))
    have hcop : IsCoprime (4 : ℤ) p := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      have : Nat.Coprime 4 p := by
        have h2 : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp.out).mpr (Ne.symm hp2)
        simpa using h2.pow_left 2
      simpa [Int.gcd] using this
    obtain ⟨c, hc⟩ := hcop.mul_dvd h4_dvd hp_dvd
    exact ⟨(p, b, c), 1, 0, by simp only [formDisc]; linear_combination hc, by simp [formEval]⟩

/-- **Corollary 3.14** for `p ∤ d`: some form of discriminant `d` represents `p` iff `(d/p) = 1`. -/
@[kb "nivenzuckermanmontgomery" "Cor 3.14, p. 153"]
theorem exists_rep_prime_iff_legendreSym {d : ℤ} (hd4 : d % 4 = 0 ∨ d % 4 = 1) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hpd : ¬(p : ℤ) ∣ d) :
    (∃ f x y, formDisc f = d ∧ formEval f x y = p) ↔ legendreSym p d = 1 := by
  rw [exists_rep_prime_iff hd4 hp2, legendreSym.eq_one_iff]
  rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-! ### Theorems 3.16 and 3.17 -/

/-- **Theorem 3.16** (symmetry; reflexivity and transitivity are `NTKB.Davenport.FormEquiv.refl` and
`NTKB.Davenport.FormEquiv.trans`): if `f ~ g` then `g ~ f`. -/
@[kb "nivenzuckermanmontgomery" "Thm 3.16, p. 158"]
theorem formEquiv_symm {f g : ℤ × ℤ × ℤ} (h : FormEquiv f g) : FormEquiv g f := by
  obtain ⟨α, β, γ, δ, hdet, rfl⟩ := h
  refine ⟨δ, -β, -γ, α, by linear_combination hdet, ?_⟩
  rw [formSubst_formSubst]
  have e1 : α * δ + β * -γ = 1 := by linear_combination hdet
  have e2 : α * -β + β * α = 0 := by ring
  have e3 : γ * δ + δ * -γ = 0 := by ring
  have e4 : γ * -β + δ * α = 1 := by linear_combination hdet
  rw [e1, e2, e3, e4]
  obtain ⟨a, b, c⟩ := f
  simp only [formSubst, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

/-- **Theorem 3.16.** Equivalence of binary quadratic forms is an equivalence relation. -/
@[kb "nivenzuckermanmontgomery" "Thm 3.16, p. 158"]
theorem formEquiv_equivalence : Equivalence FormEquiv :=
  ⟨FormEquiv.refl, formEquiv_symm, FormEquiv.trans⟩

/-- **Theorem 3.17.** If `f ~ g`, then `f` and `g` have the same discriminant, and there is a bijection
`e` of `ℤ²` (the substitution `X ↦ MX`) with `f(e(x, y)) = g(x, y)` that preserves the proper
pairs (`(x, y) = 1`); so for every `n` the (proper) representations of `n` by `g` and by `f`
correspond one to one. -/
@[kb "nivenzuckermanmontgomery" "Thm 3.17, p. 159"]
theorem formEquiv_rep_equiv {f g : ℤ × ℤ × ℤ} (h : FormEquiv f g) :
    formDisc g = formDisc f ∧ ∃ e : ℤ × ℤ ≃ ℤ × ℤ, (∀ v : ℤ × ℤ, formEval f (e v).1 (e v).2 =
      formEval g v.1 v.2) ∧ ∀ v : ℤ × ℤ, (IsCoprime (e v).1 (e v).2 ↔ IsCoprime v.1 v.2) := by
  refine ⟨h.formDisc_eq, ?_⟩
  obtain ⟨α, β, γ, δ, hdet, rfl⟩ := h
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun v ↦ (α * v.1 + β * v.2, γ * v.1 + δ * v.2)
      invFun := fun v ↦ (δ * v.1 - β * v.2, -γ * v.1 + α * v.2)
      left_inv := fun v ↦ by
        ext
        · simp only; linear_combination v.1 * hdet
        · simp only; linear_combination v.2 * hdet
      right_inv := fun v ↦ by
        ext
        · simp only; linear_combination v.1 * hdet
        · simp only; linear_combination v.2 * hdet }
  refine ⟨e, fun v ↦ (formEval_formSubst f α β γ δ v.1 v.2).symm, fun v ↦ ?_⟩
  simp only [e, Equiv.coe_fn_mk]
  constructor
  · rintro ⟨u, w, huw⟩
    exact ⟨u * α + w * γ, u * β + w * δ, by linear_combination huw⟩
  · rintro ⟨u, w, huw⟩
    refine ⟨u * δ - w * γ, -u * β + w * α, ?_⟩
    linear_combination huw + (u * v.1 + w * v.2) * hdet

/-! ### Reduced forms: Definition 3.8, Theorems 3.18 and 3.19, Definition 3.9 -/

/-- **Definition 3.8.** A form `(a, b, c)` (of nonsquare discriminant) is *reduced* if
`-|a| < b ≤ |a| < |c|` or `0 ≤ b ≤ |a| = |c|`. -/
def IsReducedForm (f : ℤ × ℤ × ℤ) : Prop :=
  (-|f.1| < f.2.1 ∧ f.2.1 ≤ |f.1| ∧ |f.1| < |f.2.2|) ∨ (0 ≤ f.2.1 ∧ f.2.1 ≤ |f.1| ∧ |f.1| = |f.2.2|)

/-- **Theorem 3.18.** If `d` is not a perfect square, every equivalence class of forms of
discriminant `d` contains a reduced form. -/
@[kb "nivenzuckermanmontgomery" "Thm 3.18, p. 160"]
theorem exists_formEquiv_isReducedForm (f : ℤ × ℤ × ℤ) (hd : ¬IsSquare (formDisc f)) :
    ∃ g, FormEquiv f g ∧ IsReducedForm g := by
  obtain ⟨g, hfg, h1, h2⟩ := exists_formEquiv_reduced f hd
  have hgd : ¬IsSquare (formDisc g) := by rwa [hfg.formDisc_eq]
  have ha := fst_ne_zero_of_not_isSquare hgd
  obtain ⟨a, b, c⟩ := g
  simp only at h1 h2 ha
  rcases lt_or_eq_of_le h2 with h2 | h2
  · -- `|a| < |c|`: only `b = -|a|` needs a shift `x ↦ x ± y`, which keeps `a` and `c`
    by_cases hb : b = -|a|
    · rcases lt_or_gt_of_ne ha with ha' | ha'
      · rw [abs_of_neg ha'] at hb h2
        refine ⟨formSubst (a, b, c) 1 (-1) 0 1, hfg.trans ⟨1, -1, 0, 1, by ring, rfl⟩, Or.inl ?_⟩
        simp only [formSubst]
        refine ⟨?_, ?_, ?_⟩ <;> rw [abs_of_neg (by linarith)] <;> [linarith; linarith; skip]
        rw [hb]; ring_nf; linarith
      · rw [abs_of_pos ha'] at hb h2
        refine ⟨formSubst (a, b, c) 1 1 0 1, hfg.trans ⟨1, 1, 0, 1, by ring, rfl⟩, Or.inl ?_⟩
        simp only [formSubst]
        refine ⟨?_, ?_, ?_⟩ <;> rw [abs_of_pos (by linarith)] <;> [linarith; linarith; skip]
        rw [hb]; ring_nf; linarith
    · exact ⟨(a, b, c), hfg, Or.inl ⟨lt_of_le_of_ne (abs_le.mp h1).1 (Ne.symm hb),
        (abs_le.mp h1).2, h2⟩⟩
  · -- `|a| = |c|`: if `b < 0`, exchange `x` and `y` (`(a, b, c) ↦ (c, -b, a)`)
    by_cases hb : 0 ≤ b
    · exact ⟨(a, b, c), hfg, Or.inr ⟨hb, (abs_le.mp h1).2, h2⟩⟩
    · push Not at hb
      refine ⟨formSubst (a, b, c) 0 (-1) 1 0, hfg.trans ⟨0, -1, 1, 0, by ring, rfl⟩, Or.inr ?_⟩
      simp only [formSubst]
      simp only [mul_zero, zero_mul, add_zero, zero_add, mul_one, pow_two, mul_neg, neg_mul,
        neg_neg, one_mul]
      refine ⟨by linarith, ?_, by rw [← h2]⟩
      have := (abs_le.mp h1).1
      rw [← h2]; linarith

/-- The inequalities `|b| ≤ |a| ≤ |c|` of a reduced form. -/
lemma IsReducedForm.abs_le_abs {f : ℤ × ℤ × ℤ} (h : IsReducedForm f) :
    |f.2.1| ≤ |f.1| ∧ |f.1| ≤ |f.2.2| := by
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact ⟨abs_le.mpr ⟨h1.le, h2⟩, h3.le⟩
  · exact ⟨abs_le.mpr ⟨by linarith [abs_nonneg f.1], h2⟩, h3.le⟩

/-- **Theorem 3.19.** Let `f = (a, b, c)` be reduced, of nonsquare discriminant `d`. If `f` is indefinite
(`d > 0`) then `0 < |a| < √d/2`; if `f` is positive definite (`d < 0`, `a > 0`) then
`0 < a ≤ √(-d/3)`. The number of reduced forms of discriminant `d` is finite. -/
@[kb "nivenzuckermanmontgomery" "Thm 3.19, p. 161"]
theorem isReducedForm_bounds {f : ℤ × ℤ × ℤ} (hd : ¬IsSquare (formDisc f)) (hf : IsReducedForm f) :
    (0 < formDisc f → 0 < |f.1| ∧ (|f.1| : ℝ) < √(formDisc f : ℝ) / 2) ∧
      (formDisc f < 0 → 0 < f.1 → (f.1 : ℝ) ≤ √(-(formDisc f : ℝ) / 3)) := by
  obtain ⟨h1, h2⟩ := hf.abs_le_abs
  have ha := fst_ne_zero_of_not_isSquare hd
  obtain ⟨a, b, c⟩ := f
  simp only [formDisc] at hd h1 h2 ha ⊢
  have hb2 : b ^ 2 ≤ a ^ 2 := sq_le_sq.mpr h1
  have hac : a ^ 2 ≤ |a * c| := by
    rw [abs_mul, sq, ← abs_mul_abs_self a]
    exact mul_le_mul_of_nonneg_left h2 (abs_nonneg a)
  refine ⟨fun hpos ↦ ⟨abs_pos.mpr ha, ?_⟩, fun hneg ha0 ↦ ?_⟩
  · -- `a c < 0`, `d = b² + 4|ac| ≥ 4a²`, with equality impossible
    have hac' : a * c < 0 := by
      by_contra h; push Not at h
      rw [abs_of_nonneg h] at hac; nlinarith
    rw [abs_of_neg hac'] at hac
    have hge : 4 * a ^ 2 ≤ b ^ 2 - 4 * a * c := by nlinarith [sq_nonneg b]
    have hne : 4 * a ^ 2 ≠ b ^ 2 - 4 * a * c := by
      intro h; exact hd ⟨2 * a, by rw [← h]; ring⟩
    have hlt : ((2 * |a| : ℤ) : ℝ) ^ 2 < ((b ^ 2 - 4 * a * c : ℤ) : ℝ) := by
      have : (2 * |a|) ^ 2 < b ^ 2 - 4 * a * c := by
        rw [mul_pow, sq_abs]; exact lt_of_le_of_ne hge hne
      exact_mod_cast this
    have := Real.lt_sqrt_of_sq_lt hlt
    push_cast at this ⊢
    linarith
  · have hac' : 0 < a * c := by nlinarith [sq_nonneg b]
    rw [abs_of_pos hac'] at hac
    have h3 : (3 * a ^ 2 : ℤ) ≤ -(b ^ 2 - 4 * a * c) := by nlinarith
    apply Real.le_sqrt_of_sq_le
    have : ((3 * a ^ 2 : ℤ) : ℝ) ≤ ((-(b ^ 2 - 4 * a * c) : ℤ) : ℝ) := by exact_mod_cast h3
    push_cast at this ⊢
    linarith

/-- **Theorem 3.19** (finiteness). For nonsquare `d` there are only finitely many reduced forms of
discriminant `d`. -/
@[kb "nivenzuckermanmontgomery" "Thm 3.19, p. 161"]
theorem finite_isReducedForm {d : ℤ} (hd : ¬IsSquare d) :
    {f : ℤ × ℤ × ℤ | formDisc f = d ∧ IsReducedForm f}.Finite := by
  set M := |d|
  refine (Finset.finite_toSet (Finset.Icc (-M) M ×ˢ Finset.Icc (-M) M ×ˢ
    Finset.Icc (-(2 * M)) (2 * M))).subset ?_
  rintro ⟨a, b, c⟩ ⟨hfd, hf⟩
  obtain ⟨h1, h2⟩ := hf.abs_le_abs
  have hnsq : ¬IsSquare (formDisc (a, b, c)) := by rwa [hfd]
  have h3 := three_mul_sq_le_of_reduced hnsq h1 h2
  have ha0 := fst_ne_zero_of_not_isSquare hnsq
  rw [hfd] at h3
  simp only at h1 h2 h3 ha0
  have haM : |a| ≤ M := by
    have h1a := Int.one_le_abs ha0
    have : |a| ≤ a ^ 2 := by nlinarith [sq_abs a]
    linarith
  have hbM : |b| ≤ M := h1.trans haM
  have hcM : |c| ≤ 2 * M := by
    have h4 : 4 * a * c = b ^ 2 - d := by simp only [formDisc] at hfd; linarith
    have hb2 : b ^ 2 ≤ M := by
      have : b ^ 2 ≤ a ^ 2 := sq_le_sq.mpr h1
      nlinarith [sq_nonneg a]
    have hca : |c| ≤ |4 * a * c| := by
      rw [abs_mul, abs_mul]
      have : (1 : ℤ) ≤ |4| * |a| := by
        have := Int.one_le_abs ha0; norm_num; linarith
      nlinarith [abs_nonneg c]
    rw [h4] at hca
    calc |c| ≤ |b ^ 2 - d| := hca
      _ ≤ |b ^ 2| + |d| := abs_sub _ _
      _ ≤ 2 * M := by rw [abs_of_nonneg (sq_nonneg b)]; linarith
  simp only [Finset.coe_product, Set.mem_prod, Finset.coe_Icc, Set.mem_Icc]
  exact ⟨abs_le.mp haM, abs_le.mp hbM, abs_le.mp hcM⟩

/-- Equivalence of forms of discriminant `d`, as a setoid. -/
def formSetoid (d : ℤ) : Setoid {f : ℤ × ℤ × ℤ // formDisc f = d} where
  r f g := FormEquiv f.1 g.1
  iseqv := ⟨fun f ↦ FormEquiv.refl f.1, formEquiv_symm, FormEquiv.trans⟩

/-- **Definition 3.9.** The class number `H(d)`: the number of equivalence classes of binary quadratic
forms of discriminant `d` (meant for nonsquare `d`, where it is finite, `finite_formClasses`). -/
noncomputable def formClassNumber (d : ℤ) : ℕ := Nat.card (Quotient (formSetoid d))

/-- For nonsquare `d` the set of classes of forms of discriminant `d` is finite (Theorems 3.18 and 3.19),
so `H(d)` counts them. -/
@[kb "nivenzuckermanmontgomery" "Def 3.9, p. 161"]
theorem finite_formClasses {d : ℤ} (hd : ¬IsSquare d) : Finite (Quotient (formSetoid d)) := by
  have hfin := finite_isReducedForm hd
  have : Finite {f : ℤ × ℤ × ℤ // formDisc f = d ∧ IsReducedForm f} := hfin.to_subtype
  refine Finite.of_surjective
    (fun g : {f : ℤ × ℤ × ℤ // formDisc f = d ∧ IsReducedForm f} ↦
      (Quotient.mk (formSetoid d) ⟨g.1, g.2.1⟩)) ?_
  rintro ⟨f, hf⟩
  obtain ⟨g, hfg, hg⟩ := exists_formEquiv_isReducedForm f (by rwa [hf])
  have hgd : formDisc g = d := by rw [hfg.formDisc_eq, hf]
  refine ⟨⟨g, hgd, hg⟩, Quotient.sound ?_⟩
  exact formEquiv_symm hfg

end NTKB.NZM
