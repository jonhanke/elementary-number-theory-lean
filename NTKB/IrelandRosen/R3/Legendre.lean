/-
Ireland–Rosen, Chapter 17, §3: Legendre's theorem on `ax² + by² + cz² = 0`.
-/
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.ZMod.Defs
import Aesop.BuiltinRules
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Bound
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import NTKB.Attr

/-!
# Legendre's theorem

Ireland–Rosen, Chapter 17, §3. Write `m R n` (`SqMod m n`) if `m` is a square modulo `n`.

* Proposition 17.3.2: for positive square-free `a, b`, `ax² + by² = z²` has a nontrivial solution
  iff `a R b`, `b R a` and `-(ab/d²) R d` with `d = (a, b)`;
* Proposition 17.3.1 (Legendre): for square-free, pairwise coprime `a, b, c`, not all of the same
  sign, `ax² + by² + cz² = 0` has a nontrivial solution iff `-ab R c`, `-ac R b`, `-bc R a`.

The sufficiency in 17.3.2 is the book's descent: from `c² - b = aAm²` with `|c| ≤ a/2` one passes
to `AX² + bY² = Z²` with `0 < A < a`, and back through the identity
`a(AXm)² = (Zc + bY)² - b(cY + Z)²`.
-/

namespace NTKB.IrelandRosen.Legendre

/-- `m R n`: `m` is a square modulo `n`. -/
def SqMod (m n : ℤ) : Prop := ∃ x : ℤ, n ∣ x ^ 2 - m

namespace SqMod

lemma of_dvd {m n n' : ℤ} (h : SqMod m n) (hd : n' ∣ n) : SqMod m n' :=
  let ⟨x, hx⟩ := h; ⟨x, hd.trans hx⟩

lemma congr {m m' n : ℤ} (h : SqMod m n) (hm : n ∣ m - m') : SqMod m' n := by
  obtain ⟨x, hx⟩ := h
  exact ⟨x, by have := dvd_add hx hm; rwa [show x ^ 2 - m + (m - m') = x ^ 2 - m' by ring] at this⟩

lemma of_dvd_self {m n : ℤ} (h : n ∣ m) : SqMod m n := ⟨0, by simpa using h⟩

lemma sq (x n : ℤ) : SqMod (x ^ 2) n := ⟨x, by simp⟩

lemma mul {m m' n : ℤ} (h : SqMod m n) (h' : SqMod m' n) : SqMod (m * m') n := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨y, hy⟩ := h'
  refine ⟨x * y, ?_⟩
  have : (x * y) ^ 2 - m * m' = (x ^ 2 - m) * y ^ 2 + m * (y ^ 2 - m') := by ring
  rw [this]; exact dvd_add (dvd_mul_of_dvd_left hx _) (dvd_mul_of_dvd_right hy _)

/-- The Chinese remainder theorem for squares. -/
lemma crt {m n₁ n₂ : ℤ} (h₁ : SqMod m n₁) (h₂ : SqMod m n₂) (hc : IsCoprime n₁ n₂) :
    SqMod m (n₁ * n₂) := by
  obtain ⟨x₁, hx₁⟩ := h₁
  obtain ⟨x₂, hx₂⟩ := h₂
  obtain ⟨u, v, huv⟩ := id hc
  set x := x₁ * v * n₂ + x₂ * u * n₁
  have e₁ : n₁ ∣ x - x₁ := ⟨(x₂ - x₁) * u, by
    simp only [x]; linear_combination x₁ * huv⟩
  have e₂ : n₂ ∣ x - x₂ := ⟨(x₁ - x₂) * v, by
    simp only [x]; linear_combination x₂ * huv⟩
  refine ⟨x, hc.mul_dvd ?_ ?_⟩
  · have := dvd_add hx₁ (e₁.trans (sub_dvd_pow_sub_pow x x₁ 2))
    rwa [show x₁ ^ 2 - m + (x ^ 2 - x₁ ^ 2) = x ^ 2 - m by ring] at this
  · have := dvd_add hx₂ (e₂.trans (sub_dvd_pow_sub_pow x x₂ 2))
    rwa [show x₂ ^ 2 - m + (x ^ 2 - x₂ ^ 2) = x ^ 2 - m by ring] at this

/-- Cancelling a square of a unit modulo `n`. -/
lemma cancel {m k n : ℤ} (h : SqMod (m * k ^ 2) n) (hk : IsCoprime k n) : SqMod m n := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨k', w, hkw⟩ := hk
  refine ⟨x * k', ?_⟩
  have : (x * k') ^ 2 - m = k' ^ 2 * (x ^ 2 - m * k ^ 2) + m * (k' * k - 1) * (k' * k + 1) := by ring
  rw [this]
  refine dvd_add (dvd_mul_of_dvd_right hx _) ?_
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right ⟨-w, by linear_combination hkw⟩ _) _

lemma neg_right {m n : ℤ} (h : SqMod m n) : SqMod m (-n) := h.of_dvd (neg_dvd.2 dvd_rfl)

end SqMod

/-- **Exercise 26 of Chapter 17** (the form used in §3): if `n` is square-free and `m` is a square
modulo every prime dividing `n`, then `m` is a square modulo `n`. -/
theorem sqMod_of_forall_prime {m n : ℤ} (hn : Squarefree n)
    (h : ∀ p : ℤ, Prime p → p ∣ n → SqMod m p) : SqMod m n := by
  suffices H : ∀ k : ℕ, Squarefree (k : ℤ) → (∀ p : ℤ, Prime p → p ∣ k → SqMod m p) →
      SqMod m k by
    have hs : Squarefree ((n.natAbs : ℕ) : ℤ) := by
      rw [Int.squarefree_natCast, Int.squarefree_natAbs]; exact hn
    have := H n.natAbs hs fun p hp hd => h p hp (by rw [Int.natCast_natAbs] at hd; exact (dvd_abs _ _).1 hd)
    rw [Int.natCast_natAbs] at this
    exact this.of_dvd (self_dvd_abs n)
  intro k
  induction k using Nat.recOnMul with
  | zero => intro hs; exact absurd hs (by simp)
  | one => intro _ _; exact SqMod.of_dvd_self (by simp)
  | prime p hp => intro _ hk; exact hk p (Nat.prime_iff_prime_int.1 hp) dvd_rfl
  | mul a b iha ihb =>
    intro hs hk
    push_cast at hs hk ⊢
    obtain ⟨hab, hsa, hsb⟩ := squarefree_mul_iff.1 hs
    exact SqMod.crt (iha hsa fun p hp hd => hk p hp (dvd_mul_of_dvd_left hd _))
      (ihb hsb fun p hp hd => hk p hp (dvd_mul_of_dvd_right hd _)) hab.isCoprime

/-! ### Helpers -/

lemma dvd_of_dvd_sq {d c : ℤ} (hd : Squarefree d) (h : d ∣ c ^ 2) : d ∣ c :=
  (hd.dvd_pow_iff_dvd two_ne_zero).1 h

lemma isUnit_of_sq_dvd {r b : ℤ} (hb : Squarefree b) (h : r ^ 2 ∣ b) : IsUnit r :=
  hb r (by rwa [← sq])

lemma mul_div_sq_gcd {a b : ℤ} (ha : a ≠ 0) :
    a * b / ((Int.gcd a b : ℤ)) ^ 2 = (a / Int.gcd a b) * (b / Int.gcd a b) := by
  have hd0 : ((Int.gcd a b : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast (Int.gcd_pos_of_ne_zero_left b ha).ne'
  have h1 := Int.mul_ediv_cancel' (Int.gcd_dvd_left a b)
  have h2 := Int.mul_ediv_cancel' (Int.gcd_dvd_right a b)
  generalize a / Int.gcd a b = a1 at h1 ⊢
  generalize b / Int.gcd a b = b1 at h2 ⊢
  generalize ((Int.gcd a b : ℕ) : ℤ) = g at h1 h2 hd0 ⊢
  subst h1 h2
  rw [show g * a1 * (g * b1) = g ^ 2 * (a1 * b1) by ring,
    Int.mul_ediv_cancel_left _ (pow_ne_zero 2 hd0)]

/-- A square-free `b > 1` is not a square: `Z² = bY²` forces `Y = Z = 0`. -/
lemma eq_zero_of_sq_eq_mul_sq {b Y Z : ℤ} (hb : Squarefree b) (hb1 : 1 < b)
    (h : Z ^ 2 = b * Y ^ 2) : Y = 0 ∧ Z = 0 := by
  by_cases hY : Y = 0
  · subst hY; simp at h; exact ⟨rfl, h⟩
  exfalso
  have hdvd : Y ^ 2 ∣ Z ^ 2 := ⟨b, by rw [h]; ring⟩
  obtain ⟨k, rfl⟩ := (Int.pow_dvd_pow_iff two_ne_zero).1 hdvd
  have : b = k ^ 2 := by
    have : Y ^ 2 * k ^ 2 = Y ^ 2 * b := by linear_combination h
    exact (mul_left_cancel₀ (pow_ne_zero 2 hY) this).symm
  have hu := isUnit_of_sq_dvd hb ⟨1, by rw [this, mul_one]⟩
  rcases Int.isUnit_iff.1 hu with rfl | rfl <;> norm_num at this <;> omega

/-! ### The descent step -/

/-- The descent step of the proof of Proposition 17.3.2. -/
lemma descent {a b : ℤ} (ha : 0 < a) (hsa : Squarefree a) (hsb : Squarefree b)
    (h1 : SqMod a b) (h2 : SqMod b a)
    (h3 : SqMod (-((a / Int.gcd a b) * (b / Int.gcd a b))) (Int.gcd a b))
    (hab : b < a) (hb_one : 1 < b) :
    ∃ A : ℤ, 0 < A ∧ A < a ∧ Squarefree A ∧ SqMod A b ∧ SqMod b A ∧
      SqMod (-((A / Int.gcd A b) * (b / Int.gcd A b))) (Int.gcd A b) ∧
      (∀ X Y Z : ℤ, (X, Y, Z) ≠ (0, 0, 0) → A * X ^ 2 + b * Y ^ 2 = Z ^ 2 →
        ∃ x y z : ℤ, (x, y, z) ≠ (0, 0, 0) ∧ a * x ^ 2 + b * y ^ 2 = z ^ 2) := by
  -- `c² ≡ b (mod a)` with `|c| ≤ a / 2`
  obtain ⟨c0, hc0⟩ := h2
  obtain ⟨c, hca, hcb⟩ : ∃ c : ℤ, a ∣ c ^ 2 - b ∧ 4 * c ^ 2 ≤ a ^ 2 := by
    set r := c0 % a
    have hr0 : 0 ≤ r := Int.emod_nonneg _ ha.ne'
    have hra : r < a := Int.emod_lt_of_pos _ ha
    have hcr : a ∣ c0 - r := ⟨c0 / a, by simp only [r]; rw [Int.emod_def]; ring⟩
    by_cases hr : 2 * r ≤ a
    · refine ⟨r, ?_, by nlinarith⟩
      have := dvd_sub hc0 (hcr.trans (sub_dvd_pow_sub_pow c0 r 2))
      rwa [show c0 ^ 2 - b - (c0 ^ 2 - r ^ 2) = r ^ 2 - b by ring] at this
    · refine ⟨r - a, ?_, by nlinarith⟩
      have hcr' : a ∣ c0 - (r - a) := by
        have := dvd_add hcr (dvd_refl a); rwa [show c0 - r + a = c0 - (r - a) by ring] at this
      have := dvd_sub hc0 (hcr'.trans (sub_dvd_pow_sub_pow c0 (r - a) 2))
      rwa [show c0 ^ 2 - b - (c0 ^ 2 - (r - a) ^ 2) = (r - a) ^ 2 - b by ring] at this
  obtain ⟨T, hT⟩ := hca
  -- `T > 0`
  have hT0 : 0 < T := by
    rcases lt_trichotomy T 0 with h | h | h
    · nlinarith
    · exfalso
      rw [h, mul_zero, sub_eq_zero] at hT
      have := isUnit_of_sq_dvd hsb ⟨1, by rw [← hT, mul_one]⟩
      rcases Int.isUnit_iff.1 this with rfl | rfl <;> norm_num at hT <;> omega
    · exact h
  -- `T = A m²` with `A` square-free
  obtain ⟨A0, m0, hA0, hm0, hTm, hsq⟩ := Nat.sq_mul_squarefree_of_pos (Int.natAbs_pos.2 hT0.ne')
  set A : ℤ := (A0 : ℤ)
  set m : ℤ := (m0 : ℤ)
  have hTA : T = A * m ^ 2 := by
    have : (T.natAbs : ℤ) = T := Int.natAbs_of_nonneg hT0.le
    rw [← this, ← hTm]; push_cast; ring
  have hApos : 0 < A := Int.natCast_pos.2 hA0
  have hmpos : 0 < m := Int.natCast_pos.2 hm0
  have hsA : Squarefree A := Int.squarefree_natCast.2 hsq
  have hcab : c ^ 2 = a * A * m ^ 2 + b := by rw [hTA] at hT; linear_combination hT
  have hb0 : 0 < b := by omega
  have hm0' : m ≠ 0 := hmpos.ne'
  -- the decomposition `a = d a₁`, `b = d b₁`, `d = (a, b)`, and `c = d c₁`
  set d : ℤ := ((Int.gcd a b : ℕ) : ℤ) with hd
  have hdpos : 0 < d := by rw [hd]; exact_mod_cast Int.gcd_pos_of_ne_zero_left b ha.ne'
  set a1 := a / d with ha1d
  set b1 := b / d with hb1d
  have ha1 : a = d * a1 := (Int.mul_ediv_cancel' (Int.gcd_dvd_left a b)).symm
  have hb1 : b = d * b1 := (Int.mul_ediv_cancel' (Int.gcd_dvd_right a b)).symm
  have hsd : Squarefree d := hsb.squarefree_of_dvd (Int.gcd_dvd_right a b)
  have hdb1 : IsCoprime d b1 := (squarefree_mul_iff.1 (hb1 ▸ hsb)).1.isCoprime
  have hda1 : IsCoprime d a1 := (squarefree_mul_iff.1 (ha1 ▸ hsa)).1.isCoprime
  have ha1b1 : IsCoprime a1 b1 := Int.isCoprime_iff_gcd_eq_one.2
    (Int.gcd_div_gcd_div_gcd (Int.gcd_pos_of_ne_zero_left b ha.ne'))
  have hdc : d ∣ c := dvd_of_dvd_sq hsd ⟨a1 * A * m ^ 2 + b1, by
    rw [hcab]; conv_lhs => rw [ha1, hb1]
    ring⟩
  obtain ⟨c1, hc1⟩ := hdc
  have hEd : d * c1 ^ 2 = a1 * A * m ^ 2 + b1 := by
    have : d * (d * c1 ^ 2) = d * (a1 * A * m ^ 2 + b1) := by
      rw [hc1, ha1, hb1] at hcab; linear_combination hcab
    exact mul_left_cancel₀ hdpos.ne' this
  refine ⟨A, hApos, ?_, hsA, ?_, ?_, ?_, ?_⟩
  · -- `A < a`
    have hm1 : 1 ≤ m ^ 2 := by nlinarith
    have : 4 * A * m ^ 2 < a := by nlinarith
    nlinarith
  · -- `A R b`, by the Chinese remainder theorem from `A R d` and `A R b₁`
    rw [hb1]
    refine SqMod.crt ?_ ?_ hdb1
    · have hmd : IsCoprime m d := isCoprime_of_prime_dvd (fun h => hm0' h.1) fun t ht htm => by
        intro htd'
        have htb1 : t ∣ b1 := by
          have : b1 = d * c1 ^ 2 - a1 * A * m ^ 2 := by linear_combination -hEd
          rw [this]
          exact dvd_sub (dvd_mul_of_dvd_left htd' _) (dvd_mul_of_dvd_right (dvd_pow htm two_ne_zero) _)
        exact ht.not_isUnit (hdb1.isUnit_of_dvd' htd' htb1)
      refine SqMod.cancel (k := a1 * m) (h3.congr ⟨-(a1 * c1 ^ 2), ?_⟩) ?_
      · linear_combination a1 * hEd
      · exact IsCoprime.mul_left hda1.symm hmd
    · have hmb1 : IsCoprime m b1 := isCoprime_of_prime_dvd (fun h => hm0' h.1) fun t ht htm => by
        intro htb'
        have htb : t ∣ b := hb1 ▸ dvd_mul_of_dvd_right htb' _
        have htc : t ∣ c := ht.dvd_of_dvd_pow (by
          rw [hcab]; exact dvd_add (dvd_mul_of_dvd_right (dvd_pow htm two_ne_zero) _) htb)
        have : t ^ 2 ∣ b := by
          have hbe : b = c ^ 2 - a * A * m ^ 2 := by linear_combination -hcab
          rw [hbe]
          exact dvd_sub (pow_dvd_pow_of_dvd htc 2) (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd htm 2) _)
        exact ht.not_isUnit (isUnit_of_sq_dvd hsb this)
      have hab1 : IsCoprime a b1 := ha1 ▸ IsCoprime.mul_left hdb1 ha1b1
      have h0 : SqMod (a * A * m ^ 2) b1 := ⟨c, ⟨d, by rw [hcab, hb1]; ring⟩⟩
      have h00 := h0.mul ((h1.of_dvd ⟨d, by rw [hb1]; ring⟩))
      rw [show a * A * m ^ 2 * a = A * (a * m) ^ 2 by ring] at h00
      exact h00.cancel (IsCoprime.mul_left hab1 hmb1)
  · exact ⟨c, ⟨a * m ^ 2, by rw [hcab]; ring⟩⟩
  · -- the third condition for `(A, b)`
    set r : ℤ := ((Int.gcd A b : ℕ) : ℤ) with hr
    have hrpos : 0 < r := by rw [hr]; exact_mod_cast Int.gcd_pos_of_ne_zero_left b hApos.ne'
    set A1 := A / r
    set b2 := b / r
    have hA1 : A = r * A1 := (Int.mul_ediv_cancel' (Int.gcd_dvd_left A b)).symm
    have hb2 : b = r * b2 := (Int.mul_ediv_cancel' (Int.gcd_dvd_right A b)).symm
    have hsr : Squarefree r := hsb.squarefree_of_dvd (Int.gcd_dvd_right A b)
    have hrc : r ∣ c := dvd_of_dvd_sq hsr ⟨a * A1 * m ^ 2 + b2, by
      rw [hcab]; conv_lhs => rw [hA1, hb2]
      ring⟩
    obtain ⟨c2, hc2⟩ := hrc
    have hEr : r * c2 ^ 2 = a * A1 * m ^ 2 + b2 := by
      have : r * (r * c2 ^ 2) = r * (a * A1 * m ^ 2 + b2) := by
        rw [hc2, hA1, hb2] at hcab; linear_combination hcab
      exact mul_left_cancel₀ hrpos.ne' this
    have har : IsCoprime a r := isCoprime_of_prime_dvd (fun h => ha.ne' h.1) fun t ht hta => by
      intro htr'
      have htb : t ∣ b := htr'.trans (Int.gcd_dvd_right A b)
      have htA : t ∣ A := htr'.trans (Int.gcd_dvd_left A b)
      have htd : t ∣ d := by rw [hd]; exact Int.dvd_coe_gcd hta htb
      have htb1 : t ∣ b1 := by
        have : b1 = d * c1 ^ 2 - a1 * A * m ^ 2 := by linear_combination -hEd
        rw [this]
        exact dvd_sub (dvd_mul_of_dvd_left htd _) (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right htA _) _)
      exact ht.not_isUnit (hdb1.isUnit_of_dvd' htd htb1)
    have hmr : IsCoprime m r := isCoprime_of_prime_dvd (fun h => hm0' h.1) fun t ht htm => by
      intro htr'
      have htb2 : t ∣ b2 := by
        have : b2 = r * c2 ^ 2 - a * A1 * m ^ 2 := by linear_combination -hEr
        rw [this]
        exact dvd_sub (dvd_mul_of_dvd_left htr' _) (dvd_mul_of_dvd_right (dvd_pow htm two_ne_zero) _)
      have : t ^ 2 ∣ b := by
        rw [hb2, sq]; exact mul_dvd_mul htr' htb2
      exact ht.not_isUnit (isUnit_of_sq_dvd hsb this)
    have h0 : SqMod (-(A1 * b2) * (a * m ^ 2)) r := ⟨b2, ⟨b2 * c2 ^ 2, by
      linear_combination (-b2) * hEr⟩⟩
    have h00 := h0.mul (h1.of_dvd (Int.gcd_dvd_right A b))
    rw [show -(A1 * b2) * (a * m ^ 2) * a = -(A1 * b2) * (a * m) ^ 2 by ring] at h00
    exact h00.cancel (IsCoprime.mul_left har hmr)
  · -- transfer of solutions
    intro X Y Z hXYZ hXYZ'
    refine ⟨A * X * m, c * Y + Z, Z * c + b * Y, ?_, ?_⟩
    · intro h0
      simp only [Prod.mk.injEq] at h0
      obtain ⟨hx0, -, -⟩ := h0
      have hX : X = 0 := by
        rcases mul_eq_zero.1 hx0 with h | h
        · rcases mul_eq_zero.1 h with h | h
          · exact absurd h hApos.ne'
          · exact h
        · exact absurd h hmpos.ne'
      subst hX
      have := eq_zero_of_sq_eq_mul_sq hsb hb_one (by linarith : Z ^ 2 = b * Y ^ 2)
      exact hXYZ (by rw [this.1, this.2])
    · linear_combination (-(A * X ^ 2)) * hcab + (c ^ 2 - b) * hXYZ'

/-! ### Proposition 17.3.2 (sufficiency) -/

lemma isSquare_neg_one_of_sqMod {n : ℕ} (h : SqMod (-1) n) : IsSquare (-1 : ZMod n) := by
  obtain ⟨x, hx⟩ := h
  refine ⟨(x : ZMod n), ?_⟩
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).2 hx
  push_cast at this; linear_combination -this

lemma gcd_comm' (a b : ℤ) : ((Int.gcd b a : ℕ) : ℤ) = Int.gcd a b := by rw [Int.gcd_comm]

/-- **Proposition 17.3.2** (the direction proved in the book). Let `a, b` be positive square-free
integers with `a R b`, `b R a` and `-(ab/d²) R d`, `d = (a, b)`. Then `ax² + by² = z²` has a
nontrivial solution. -/
theorem exists_sol_of_sqMod {a b : ℤ} (ha : 0 < a) (hb : 0 < b) (hsa : Squarefree a)
    (hsb : Squarefree b) (h1 : SqMod a b) (h2 : SqMod b a)
    (h3 : SqMod (-(a * b / (Int.gcd a b : ℤ) ^ 2)) (Int.gcd a b)) :
    ∃ x y z : ℤ, (x, y, z) ≠ (0, 0, 0) ∧ a * x ^ 2 + b * y ^ 2 = z ^ 2 := by
  rw [mul_div_sq_gcd ha.ne'] at h3
  suffices H : ∀ n : ℕ, ∀ a b : ℤ, (a + b).toNat = n → 0 < a → 0 < b → Squarefree a →
      Squarefree b → SqMod a b → SqMod b a →
      SqMod (-((a / Int.gcd a b) * (b / Int.gcd a b))) (Int.gcd a b) →
      ∃ x y z : ℤ, (x, y, z) ≠ (0, 0, 0) ∧ a * x ^ 2 + b * y ^ 2 = z ^ 2 from
    H _ a b rfl ha hb hsa hsb h1 h2 h3
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  -- the descent, for `b < a` and `1 < b`
  have key : ∀ a b : ℤ, (a + b).toNat = n → 0 < a → 0 < b → Squarefree a → Squarefree b →
      SqMod a b → SqMod b a → SqMod (-((a / Int.gcd a b) * (b / Int.gcd a b))) (Int.gcd a b) →
      b < a → 1 < b → ∃ x y z : ℤ, (x, y, z) ≠ (0, 0, 0) ∧ a * x ^ 2 + b * y ^ 2 = z ^ 2 := by
    intro a b hn ha hb hsa hsb h1 h2 h3 hab hb1
    obtain ⟨A, hA0, hAa, hsA, hA1, hA2, hA3, htr⟩ := descent ha hsa hsb h1 h2 h3 hab hb1
    obtain ⟨X, Y, Z, hne, hXYZ⟩ := ih (A + b).toNat (by omega) A b rfl hA0 hb hsA hsb hA1 hA2 hA3
    exact htr X Y Z hne hXYZ
  intro a b hn ha hb hsa hsb h1 h2 h3
  -- the cases `a = 1`, `b = 1`, `a = b`
  by_cases ha1 : a = 1
  · exact ⟨1, 0, 1, by simp, by rw [ha1]; ring⟩
  by_cases hb1 : b = 1
  · exact ⟨0, 1, 1, by simp, by rw [hb1]; ring⟩
  rcases lt_trichotomy a b with hab | rfl | hab
  · -- swap `a` and `b`
    obtain ⟨x, y, z, hne, h⟩ := key b a (by rw [add_comm]; exact hn) hb ha hsb hsa h2 h1
      (by rw [gcd_comm', mul_comm]; exact h3) hab (by omega)
    exact ⟨y, x, z, by
      intro h0; apply hne; simp only [Prod.mk.injEq] at h0 ⊢; exact ⟨h0.2.1, h0.1, h0.2.2⟩,
      by linear_combination h⟩
  · -- `a = b`: then `-1 R a`, so `a = r² + s²`
    have hg : ((Int.gcd a a : ℕ) : ℤ) = a := by rw [Int.gcd_self, Int.natCast_natAbs, abs_of_pos ha]
    rw [hg, Int.ediv_self ha.ne', one_mul] at h3
    have hsq := isSquare_neg_one_of_sqMod (show SqMod (-1) (a.toNat : ℕ) by
      rw [Int.toNat_of_nonneg ha.le]; exact h3)
    obtain ⟨r, s, hrs⟩ := Nat.eq_sq_add_sq_of_isSquare_mod_neg_one hsq
    have hrs' : a = (r : ℤ) ^ 2 + (s : ℤ) ^ 2 := by
      have : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg ha.le
      rw [← this, hrs]; push_cast; ring
    refine ⟨r, s, a, by simp [ha.ne'], ?_⟩
    rw [sq a]; nth_rw 3 [hrs']; ring
  · exact key a b hn ha hb hsa hsb h1 h2 h3 hab (by omega)

/-! ### Proposition 17.3.1 -/

/-- `ax² + by² + cz² = 0` has a nontrivial integral solution. -/
def HasSol (a b c : ℤ) : Prop :=
  ∃ x y z : ℤ, (x, y, z) ≠ (0, 0, 0) ∧ a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0

lemma HasSol.swap12 {a b c : ℤ} (h : HasSol a b c) : HasSol b a c := by
  obtain ⟨x, y, z, hne, h⟩ := h
  exact ⟨y, x, z, by
    intro h0; apply hne; simp only [Prod.mk.injEq] at h0 ⊢; exact ⟨h0.2.1, h0.1, h0.2.2⟩,
    by linear_combination h⟩

lemma HasSol.swap23 {a b c : ℤ} (h : HasSol a b c) : HasSol a c b := by
  obtain ⟨x, y, z, hne, h⟩ := h
  exact ⟨x, z, y, by
    intro h0; apply hne; simp only [Prod.mk.injEq] at h0 ⊢; exact ⟨h0.1, h0.2.2, h0.2.1⟩,
    by linear_combination h⟩

lemma HasSol.neg {a b c : ℤ} (h : HasSol a b c) : HasSol (-a) (-b) (-c) := by
  obtain ⟨x, y, z, hne, h⟩ := h
  exact ⟨x, y, z, hne, by linear_combination -h⟩

lemma SqMod.neg_neg {m n : ℤ} (h : SqMod m n) : SqMod m (-n) := h.neg_right

lemma SqMod.of_neg {m n : ℤ} (h : SqMod m (-n)) : SqMod m n := by simpa using h.neg_right

/-- A nontrivial solution can be taken without a prime dividing all of `x, y, z`. -/
lemma HasSol.exists_primitive {a b c : ℤ} (h : HasSol a b c) :
    ∃ x y z : ℤ, (x, y, z) ≠ (0, 0, 0) ∧ a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0 ∧
      ∀ r : ℤ, Prime r → r ∣ x → r ∣ y → r ∣ z → False := by
  suffices H : ∀ n : ℕ, ∀ x y z : ℤ, x.natAbs + y.natAbs + z.natAbs = n → (x, y, z) ≠ (0, 0, 0) →
      a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0 → ∃ x y z : ℤ, (x, y, z) ≠ (0, 0, 0) ∧
        a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0 ∧
        ∀ r : ℤ, Prime r → r ∣ x → r ∣ y → r ∣ z → False by
    obtain ⟨x, y, z, hne, h⟩ := h
    exact H _ x y z rfl hne h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x y z hn hne h
  by_cases hg : ∃ r : ℤ, Prime r ∧ r ∣ x ∧ r ∣ y ∧ r ∣ z
  · obtain ⟨r, hr, ⟨x', rfl⟩, ⟨y', rfl⟩, ⟨z', rfl⟩⟩ := hg
    have hr1 : 2 ≤ r.natAbs := by
      have := Int.natAbs_pos.2 hr.ne_zero
      by_contra h'
      exact hr.not_isUnit (Int.isUnit_iff_natAbs_eq.2 (by omega))
    have hne' : (x', y', z') ≠ (0, 0, 0) := by
      intro h0; apply hne; simp only [Prod.mk.injEq] at h0 ⊢; simp [h0.1, h0.2.1, h0.2.2]
    have hpos : 0 < x'.natAbs + y'.natAbs + z'.natAbs := by
      by_contra h'
      apply hne'
      have h1 : x'.natAbs = 0 := by omega
      have h2 : y'.natAbs = 0 := by omega
      have h3 : z'.natAbs = 0 := by omega
      simp [Int.natAbs_eq_zero.1 h1, Int.natAbs_eq_zero.1 h2, Int.natAbs_eq_zero.1 h3]
    refine ih (x'.natAbs + y'.natAbs + z'.natAbs) ?_ x' y' z' rfl hne' ?_
    · rw [← hn, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul]; nlinarith
    · have hr2 : r ^ 2 ≠ 0 := pow_ne_zero _ hr.ne_zero
      exact (mul_eq_zero.1 (show r ^ 2 * (a * x' ^ 2 + b * y' ^ 2 + c * z' ^ 2) = 0 by
        rw [← h]; ring)).resolve_left hr2
  · push_neg at hg
    exact ⟨x, y, z, hne, h, fun r hr h1 h2 h3 => hg r hr h1 h2 h3⟩

/-- The necessity of the condition `-ab R c` in Legendre's theorem. -/
lemma HasSol.sqMod {a b c : ℤ} (h : HasSol a b c) (hsc : Squarefree c) (hac : IsCoprime a c) :
    SqMod (-(a * b)) c := by
  obtain ⟨x, y, z, -, h, hg⟩ := h.exists_primitive
  refine sqMod_of_forall_prime hsc fun p hp hpc => ?_
  have hpa : ¬ p ∣ a := fun hpa => hp.not_isUnit (hac.isUnit_of_dvd' hpa hpc)
  have hpy : ¬ p ∣ y := by
    intro hpy
    have hpx : p ∣ x := by
      have : p ∣ a * x ^ 2 := by
        have : a * x ^ 2 = -(b * y ^ 2) - c * z ^ 2 := by linear_combination h
        rw [this]
        exact dvd_sub (dvd_neg.2 (dvd_mul_of_dvd_right (dvd_pow hpy two_ne_zero) _))
          (dvd_mul_of_dvd_left hpc _)
      exact hp.dvd_of_dvd_pow ((hp.dvd_or_dvd this).resolve_left hpa)
    have hpz : ¬ p ∣ z := fun hpz => hg p hp hpx hpy hpz
    have h2 : p ^ 2 ∣ c * z ^ 2 := by
      have : c * z ^ 2 = -(a * x ^ 2 + b * y ^ 2) := by linear_combination h
      rw [this, dvd_neg]
      exact dvd_add (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hpx 2) _)
        (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hpy 2) _)
    have hcop : IsCoprime (p ^ 2) (z ^ 2) :=
      IsCoprime.pow ((Prime.coprime_iff_not_dvd hp).2 hpz)
    exact hp.not_isUnit (isUnit_of_sq_dvd hsc (hcop.dvd_of_dvd_mul_right h2))
  have hyp : IsCoprime y p := ((Prime.coprime_iff_not_dvd hp).2 hpy).symm
  obtain ⟨c', hc'⟩ := hpc
  refine SqMod.cancel (k := y) ⟨a * x, ⟨-(a * c' * z ^ 2), ?_⟩⟩ hyp
  rw [hc'] at h
  linear_combination a * h

lemma sqfree_neg {x : ℤ} (h : Squarefree x) : Squarefree (-x) := fun y hy => h y ((dvd_neg).1 hy)

/-- The sufficiency in Legendre's theorem when `a, b > 0 > c`, from Proposition 17.3.2. -/
lemma hasSol_of_pos_pos_neg {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : c < 0)
    (hsa : Squarefree a) (hsb : Squarefree b) (hsc : Squarefree c) (hab : IsCoprime a b)
    (hac : IsCoprime a c) (hbc : IsCoprime b c) (h1 : SqMod (-(a * b)) c)
    (h2 : SqMod (-(a * c)) b) (h3 : SqMod (-(b * c)) a) : HasSol a b c := by
  set A := -(a * c)
  set B := -(b * c)
  have hA : 0 < A := by simp only [A]; nlinarith
  have hB : 0 < B := by simp only [B]; nlinarith
  have hsA : Squarefree A := by
    simp only [A, ← mul_neg]
    exact squarefree_mul_iff.2 ⟨(hac.neg_right).isRelPrime, hsa, sqfree_neg hsc⟩
  have hsB : Squarefree B := by
    simp only [B, ← mul_neg]
    exact squarefree_mul_iff.2 ⟨(hbc.neg_right).isRelPrime, hsb, sqfree_neg hsc⟩
  have hg : ((Int.gcd A B : ℕ) : ℤ) = -c := by
    simp only [A, B, ← mul_neg]
    rw [Int.gcd_mul_right, Int.isCoprime_iff_gcd_eq_one.1 hab, one_mul, Int.natCast_natAbs,
      abs_of_pos (by linarith)]
  have hc0 : -c ≠ 0 := by linarith
  have e3 : A * B / ((Int.gcd A B : ℕ) : ℤ) ^ 2 = a * b := by
    rw [hg]; simp only [A, B]
    rw [show -(a * c) * -(b * c) = (-c) ^ 2 * (a * b) by ring,
      Int.mul_ediv_cancel_left _ (pow_ne_zero 2 hc0)]
  have hS := exists_sol_of_sqMod hA hB hsA hsB ?_ ?_ (by rw [e3, hg]; exact h1.neg_right)
  · obtain ⟨x, y, z, hne, hxyz⟩ := hS
    have hcz : c ∣ z := dvd_of_dvd_sq hsc ⟨-(a * x ^ 2 + b * y ^ 2), by
      rw [← hxyz]; simp only [A, B]; ring⟩
    obtain ⟨z', rfl⟩ := hcz
    refine ⟨x, y, z', ?_, ?_⟩
    · intro h0; apply hne; simp only [Prod.mk.injEq] at h0 ⊢; simp [h0.1, h0.2.1, h0.2.2]
    · have : c * (a * x ^ 2 + b * y ^ 2 + c * z' ^ 2) = 0 := by
        simp only [A, B] at hxyz; linear_combination -hxyz
      exact (mul_eq_zero.1 this).resolve_left (by linarith)
  · -- `A R B`: modulo `b` from `-ac R b`, modulo `-c` trivially
    simp only [B, ← mul_neg]
    exact SqMod.crt h2 (SqMod.of_dvd_self ⟨a, by simp only [A]; ring⟩) hbc.neg_right
  · simp only [A, ← mul_neg]
    exact SqMod.crt h3 (SqMod.of_dvd_self ⟨b, by simp only [B]; ring⟩) hac.neg_right

/-- **Proposition 17.3.1 (Legendre).** Let `a, b, c` be square-free, pairwise relatively prime
integers, not all positive and not all negative. Then `ax² + by² + cz² = 0` has a nontrivial
integral solution iff `-ab R c`, `-ac R b` and `-bc R a`. -/
@[kb "irelandrosen1990" "Prop 17.3.1, p. 284"]
theorem legendre {a b c : ℤ} (hsa : Squarefree a) (hsb : Squarefree b) (hsc : Squarefree c)
    (hab : IsCoprime a b) (hac : IsCoprime a c) (hbc : IsCoprime b c)
    (hpos : ¬ (0 < a ∧ 0 < b ∧ 0 < c)) (hneg : ¬ (a < 0 ∧ b < 0 ∧ c < 0)) :
    HasSol a b c ↔ SqMod (-(a * b)) c ∧ SqMod (-(a * c)) b ∧ SqMod (-(b * c)) a := by
  constructor
  · intro h
    refine ⟨h.sqMod hsc hac, ?_, ?_⟩
    · exact h.swap23.sqMod hsb hab
    · exact h.swap12.swap23.sqMod hsa hab.symm
  · rintro ⟨h1, h2, h3⟩
    have ha0 : a ≠ 0 := hsa.ne_zero
    have hb0 : b ≠ 0 := hsb.ne_zero
    have hc0 : c ≠ 0 := hsc.ne_zero
    -- reduce to `a, b > 0 > c` by permuting and negating
    have core := @hasSol_of_pos_pos_neg
    rcases lt_or_gt_of_ne ha0 with ha | ha <;> rcases lt_or_gt_of_ne hb0 with hb | hb <;>
      rcases lt_or_gt_of_ne hc0 with hc | hc
    · exact absurd ⟨ha, hb, hc⟩ hneg
    · -- `(-, -, +)`
      have := core (a := -a) (b := -b) (c := -c) (by linarith) (by linarith) (by linarith)
        (sqfree_neg hsa) (sqfree_neg hsb) (sqfree_neg hsc) hab.neg_neg hac.neg_neg hbc.neg_neg
        (by simpa using h1.neg_right) (by simpa using h2.neg_right) (by simpa using h3.neg_right)
      simpa using this.neg
    · -- `(-, +, -)`
      have := core (a := -a) (b := -c) (c := -b) (by linarith) (by linarith) (by linarith)
        (sqfree_neg hsa) (sqfree_neg hsc) (sqfree_neg hsb) hac.neg_neg hab.neg_neg hbc.symm.neg_neg
        (by simpa using h2.neg_right) (by simpa using h1.neg_right)
        (by simpa [mul_comm] using h3.neg_right)
      simpa using this.neg.swap23
    · -- `(-, +, +)`
      have := core (a := b) (b := c) (c := a) hb hc ha hsb hsc hsa hbc hab.symm hac.symm
        (by simpa [mul_comm] using h3) (by simpa [mul_comm] using h1)
        (by simpa [mul_comm] using h2)
      exact this.swap23.swap12
    · -- `(+, -, -)`
      have := core (a := -b) (b := -c) (c := -a) (by linarith) (by linarith) (by linarith)
        (sqfree_neg hsb) (sqfree_neg hsc) (sqfree_neg hsa) hbc.neg_neg hab.symm.neg_neg hac.symm.neg_neg
        (by simpa [mul_comm] using h3.neg_right) (by simpa [mul_comm] using h1.neg_right)
        (by simpa [mul_comm] using h2.neg_right)
      simpa using this.neg.swap23.swap12
    · -- `(+, -, +)`
      have := core (a := a) (b := c) (c := b) ha hc hb hsa hsc hsb hac hab hbc.symm
        h2 h1 (by simpa [mul_comm] using h3)
      exact this.swap23
    · exact core ha hb hc hsa hsb hsc hab hac hbc h1 h2 h3
    · exact absurd ⟨ha, hb, hc⟩ hpos

/-- The local condition at a prime `p ∣ a` gives `-bc R p` (proof of the Corollary to 17.3.1). -/
lemma sqMod_of_local {a b c p : ℤ} (hp : Prime p) (hpa : p ∣ a) (hsa : Squarefree a)
    (hab : IsCoprime a b) (hac : IsCoprime a c)
    (h : ∃ x y z : ℤ, ¬ (p ∣ x ∧ p ∣ y ∧ p ∣ z) ∧ p ^ 2 ∣ a * x ^ 2 + b * y ^ 2 + c * z ^ 2) :
    SqMod (-(b * c)) p := by
  obtain ⟨x, y, z, hnd, hd⟩ := h
  have hpb : ¬ p ∣ b := fun h' => hp.not_isUnit (hab.isUnit_of_dvd' hpa h')
  have hpc : ¬ p ∣ c := fun h' => hp.not_isUnit (hac.isUnit_of_dvd' hpa h')
  have hp1 : p ∣ a * x ^ 2 + b * y ^ 2 + c * z ^ 2 := (dvd_pow_self p two_ne_zero).trans hd
  have hpx_of : p ∣ y → p ∣ z → p ∣ x := by
    intro hy hz
    by_contra hx
    have h2 : p ^ 2 ∣ a * x ^ 2 := by
      have : a * x ^ 2 = (a * x ^ 2 + b * y ^ 2 + c * z ^ 2) - b * y ^ 2 - c * z ^ 2 := by ring
      rw [this]
      exact dvd_sub (dvd_sub hd (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hy 2) _))
        (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hz 2) _)
    have hcop : IsCoprime (p ^ 2) (x ^ 2) := IsCoprime.pow ((Prime.coprime_iff_not_dvd hp).2 hx)
    exact hp.not_isUnit (isUnit_of_sq_dvd hsa (hcop.dvd_of_dvd_mul_right h2))
  have hrest : p ∣ b * y ^ 2 + c * z ^ 2 := by
    have := dvd_sub hp1 (dvd_mul_of_dvd_left hpa (x ^ 2))
    rwa [show a * x ^ 2 + b * y ^ 2 + c * z ^ 2 - a * x ^ 2 = b * y ^ 2 + c * z ^ 2 by ring] at this
  have hpz : ¬ p ∣ z := by
    intro hz
    have hy : p ∣ y := by
      have : p ∣ b * y ^ 2 := by
        have := dvd_sub hrest (dvd_mul_of_dvd_right (dvd_pow hz two_ne_zero) c)
        simpa using this
      exact hp.dvd_of_dvd_pow ((hp.dvd_or_dvd this).resolve_left hpb)
    exact hnd ⟨hpx_of hy hz, hy, hz⟩
  have hzp : IsCoprime z p := ((Prime.coprime_iff_not_dvd hp).2 hpz).symm
  obtain ⟨k, hk⟩ := hrest
  exact SqMod.cancel (k := z) ⟨b * y, ⟨b * k, by linear_combination b * hk⟩⟩ hzp

/-- **Corollary to Proposition 17.3.1 (the Hasse principle for `ax² + by² + cz²`).** Let `a, b, c`
be square-free, pairwise relatively prime, not all of the same sign. If for every prime `p` and every
`m` the congruence `ax² + by² + cz² ≡ 0 (mod p^m)` has a solution not all divisible by `p`, then
`ax² + by² + cz² = 0` has a nontrivial integral solution. -/
@[kb "irelandrosen1990" "Ch. 17, §3, Corollary to Prop 17.3.1, p. 285"]
theorem hasSol_of_local {a b c : ℤ} (hsa : Squarefree a) (hsb : Squarefree b) (hsc : Squarefree c)
    (hab : IsCoprime a b) (hac : IsCoprime a c) (hbc : IsCoprime b c)
    (hpos : ¬ (0 < a ∧ 0 < b ∧ 0 < c)) (hneg : ¬ (a < 0 ∧ b < 0 ∧ c < 0))
    (hloc : ∀ p : ℤ, Prime p → ∀ m : ℕ, ∃ x y z : ℤ, ¬ (p ∣ x ∧ p ∣ y ∧ p ∣ z) ∧
      p ^ m ∣ a * x ^ 2 + b * y ^ 2 + c * z ^ 2) :
    HasSol a b c := by
  refine (legendre hsa hsb hsc hab hac hbc hpos hneg).2 ⟨?_, ?_, ?_⟩
  · refine sqMod_of_forall_prime hsc fun p hp hpc => ?_
    have := sqMod_of_local (a := c) (b := a) (c := b) hp hpc hsc hac.symm hbc.symm (by
      obtain ⟨x, y, z, h1, h2⟩ := hloc p hp 2
      exact ⟨z, x, y, fun h => h1 ⟨h.2.1, h.2.2, h.1⟩, by
        rw [show c * z ^ 2 + a * x ^ 2 + b * y ^ 2 = a * x ^ 2 + b * y ^ 2 + c * z ^ 2 by ring];
        exact h2⟩)
    exact this
  · refine sqMod_of_forall_prime hsb fun p hp hpb => ?_
    have := sqMod_of_local (a := b) (b := a) (c := c) hp hpb hsb hab.symm hbc (by
      obtain ⟨x, y, z, h1, h2⟩ := hloc p hp 2
      exact ⟨y, x, z, fun h => h1 ⟨h.2.1, h.1, h.2.2⟩, by
        rw [show b * y ^ 2 + a * x ^ 2 + c * z ^ 2 = a * x ^ 2 + b * y ^ 2 + c * z ^ 2 by ring];
        exact h2⟩)
    exact this
  · exact sqMod_of_forall_prime hsa fun p hp hpa => sqMod_of_local hp hpa hsa hab hac (hloc p hp 2)

/-- From a primitive solution of `ax² + by² = z²` with `b` square-free, `a R b`. -/
lemma sqMod_of_sol {a b x y z : ℤ} (hsb : Squarefree b) (h : a * x ^ 2 + b * y ^ 2 = z ^ 2)
    (hg : ∀ r : ℤ, Prime r → r ∣ x → r ∣ y → r ∣ z → False) : SqMod a b := by
  refine sqMod_of_forall_prime hsb fun p hp hpb => ?_
  have hpx : ¬ p ∣ x := by
    intro hpx
    have hpz : p ∣ z := hp.dvd_of_dvd_pow (by
      rw [← h]; exact dvd_add (dvd_mul_of_dvd_right (dvd_pow hpx two_ne_zero) _)
        (dvd_mul_of_dvd_left hpb _))
    have hpy : ¬ p ∣ y := fun hpy => hg p hp hpx hpy hpz
    have h2 : p ^ 2 ∣ b * y ^ 2 := by
      have : b * y ^ 2 = z ^ 2 - a * x ^ 2 := by linear_combination h
      rw [this]
      exact dvd_sub (pow_dvd_pow_of_dvd hpz 2) (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hpx 2) _)
    have hcop : IsCoprime (p ^ 2) (y ^ 2) := IsCoprime.pow ((Prime.coprime_iff_not_dvd hp).2 hpy)
    exact hp.not_isUnit (isUnit_of_sq_dvd hsb (hcop.dvd_of_dvd_mul_right h2))
  have hxp : IsCoprime x p := ((Prime.coprime_iff_not_dvd hp).2 hpx).symm
  obtain ⟨k, hk⟩ := hpb
  exact SqMod.cancel (k := x) ⟨z, ⟨k * y ^ 2, by rw [hk] at h; linear_combination -h⟩⟩ hxp

/-- **Proposition 17.3.2** (necessity): a nontrivial solution of `ax² + by² = z²` (`a, b > 0`
square-free) forces `a R b`, `b R a` and `-(ab/d²) R d`. -/
theorem sqMod_of_exists_sol {a b : ℤ} (ha : 0 < a) (hsa : Squarefree a) (hsb : Squarefree b)
    (h : ∃ x y z : ℤ, (x, y, z) ≠ (0, 0, 0) ∧ a * x ^ 2 + b * y ^ 2 = z ^ 2) :
    SqMod a b ∧ SqMod b a ∧ SqMod (-(a * b / (Int.gcd a b : ℤ) ^ 2)) (Int.gcd a b) := by
  obtain ⟨x, y, z, -, h, hg⟩ := (show HasSol a b (-1) from by
    obtain ⟨x, y, z, hne, h⟩ := h; exact ⟨x, y, z, hne, by linear_combination h⟩).exists_primitive
  have h' : a * x ^ 2 + b * y ^ 2 = z ^ 2 := by linear_combination h
  refine ⟨sqMod_of_sol hsb h' hg, sqMod_of_sol hsa (by linear_combination h')
    (fun r hr h1 h2 h3 => hg r hr h2 h1 h3), ?_⟩
  rw [mul_div_sq_gcd ha.ne']
  set d : ℤ := ((Int.gcd a b : ℕ) : ℤ) with hd
  have hdpos : 0 < d := Int.natCast_pos.2 (Int.gcd_pos_of_ne_zero_left b ha.ne')
  set a1 := a / d
  set b1 := b / d
  have ha1 : a = d * a1 := (Int.mul_ediv_cancel' (Int.gcd_dvd_left a b)).symm
  have hb1 : b = d * b1 := (Int.mul_ediv_cancel' (Int.gcd_dvd_right a b)).symm
  have hsd : Squarefree d := hsb.squarefree_of_dvd (Int.gcd_dvd_right a b)
  have hda1 : IsCoprime d a1 := (squarefree_mul_iff.1 (ha1 ▸ hsa)).1.isCoprime
  have hdz : d ∣ z := dvd_of_dvd_sq hsd ⟨a1 * x ^ 2 + b1 * y ^ 2, by rw [← h', ha1, hb1]; ring⟩
  obtain ⟨z1, hz1⟩ := hdz
  have hE : a1 * x ^ 2 + b1 * y ^ 2 = d * z1 ^ 2 := by
    have : d * (a1 * x ^ 2 + b1 * y ^ 2) = d * (d * z1 ^ 2) := by
      rw [hz1, ha1, hb1] at h'; linear_combination h'
    exact mul_left_cancel₀ hdpos.ne' this
  refine sqMod_of_forall_prime hsd fun p hp hpd => ?_
  have hpa1 : ¬ p ∣ a1 := fun h1 => hp.not_isUnit (hda1.isUnit_of_dvd' hpd h1)
  have hpy : ¬ p ∣ y := by
    intro hpy
    have hpx : p ∣ x := by
      have : p ∣ a1 * x ^ 2 := by
        have : a1 * x ^ 2 = d * z1 ^ 2 - b1 * y ^ 2 := by linear_combination hE
        rw [this]
        exact dvd_sub (dvd_mul_of_dvd_left hpd _) (dvd_mul_of_dvd_right (dvd_pow hpy two_ne_zero) _)
      exact hp.dvd_of_dvd_pow ((hp.dvd_or_dvd this).resolve_left hpa1)
    exact hg p hp hpx hpy (hz1 ▸ dvd_mul_of_dvd_left hpd _)
  have hyp : IsCoprime y p := ((Prime.coprime_iff_not_dvd hp).2 hpy).symm
  obtain ⟨k, hk⟩ := hpd
  exact SqMod.cancel (k := y) ⟨a1 * x, ⟨a1 * k * z1 ^ 2, by
    rw [hk] at hE; linear_combination a1 * hE⟩⟩ hyp

/-- **Proposition 17.3.2.** For positive square-free `a, b`, `ax² + by² = z²` has a nontrivial
solution iff `a R b`, `b R a` and `-(ab/d²) R d`, where `d = (a, b)`. -/
@[kb "irelandrosen1990" "Ch. 17, §3, Prop 17.3.2, p. 284"]
theorem exists_sol_iff {a b : ℤ} (ha : 0 < a) (hb : 0 < b) (hsa : Squarefree a)
    (hsb : Squarefree b) :
    (∃ x y z : ℤ, (x, y, z) ≠ (0, 0, 0) ∧ a * x ^ 2 + b * y ^ 2 = z ^ 2) ↔
      SqMod a b ∧ SqMod b a ∧ SqMod (-(a * b / (Int.gcd a b : ℤ) ^ 2)) (Int.gcd a b) :=
  ⟨sqMod_of_exists_sol ha hsa hsb, fun ⟨h1, h2, h3⟩ => exists_sol_of_sqMod ha hb hsa hsb h1 h2 h3⟩

end NTKB.IrelandRosen.Legendre
