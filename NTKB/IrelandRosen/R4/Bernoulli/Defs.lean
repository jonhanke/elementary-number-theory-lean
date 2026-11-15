/-
Ireland–Rosen, Chapter 15, §15.2: p-integral rationals, congruences between them, and the power
sums S_m(n).
-/
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# p-integral rationals and congruences (Ireland–Rosen, §15.2)

Ireland and Rosen work with *p-integral* rationals (denominator prime to `p`) and congruences
`x ≡ y (mod p^e)` between them, meaning that `(x - y)/p^e` is `p`-integral. We define both
(`IsPIntegral`, `PModEq`) and the power sum `S_m(n) = 1^m + 2^m + ⋯ + (n-1)^m` (`powerSum`), with
the closure properties used throughout: `p`-integral rationals form the valuation subring
`(Rat.padicValuation p).integer`.
-/

namespace NTKB.IrelandRosen

open Finset

/-- A rational number is `p`-integral if its denominator is prime to `p` (Ireland–Rosen, §15.2). -/
def IsPIntegral (p : ℕ) (x : ℚ) : Prop := ¬ p ∣ x.den

/-- `x ≡ y (mod p^e)` for rationals: `(x - y)/p^e` is `p`-integral (Ireland–Rosen, §15.2). -/
def PModEq (p e : ℕ) (x y : ℚ) : Prop := IsPIntegral p ((x - y) / (p : ℚ) ^ e)

/-- The power sum `S_m(n) = 1^m + 2^m + ⋯ + (n-1)^m` of Ireland–Rosen, §15.2. -/
def powerSum (m n : ℕ) : ℕ := ∑ j ∈ Ico 1 n, j ^ m

section API

variable {p : ℕ} [hp : Fact p.Prime]

theorem isPIntegral_iff_mem {x : ℚ} : IsPIntegral p x ↔ x ∈ (Rat.padicValuation p).integer :=
  (Rat.padicValuation_le_one_iff).symm

theorem IsPIntegral.add {x y : ℚ} (hx : IsPIntegral p x) (hy : IsPIntegral p y) :
    IsPIntegral p (x + y) := by
  rw [isPIntegral_iff_mem] at *; exact add_mem hx hy

theorem IsPIntegral.mul {x y : ℚ} (hx : IsPIntegral p x) (hy : IsPIntegral p y) :
    IsPIntegral p (x * y) := by
  rw [isPIntegral_iff_mem] at *; exact mul_mem hx hy

theorem IsPIntegral.neg {x : ℚ} (hx : IsPIntegral p x) : IsPIntegral p (-x) := by
  rw [isPIntegral_iff_mem] at *; exact neg_mem hx

theorem IsPIntegral.sub {x y : ℚ} (hx : IsPIntegral p x) (hy : IsPIntegral p y) :
    IsPIntegral p (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

theorem isPIntegral_intCast (n : ℤ) : IsPIntegral p n := by
  simp [IsPIntegral, hp.out.ne_one]

theorem isPIntegral_natCast (n : ℕ) : IsPIntegral p n := by
  simpa using isPIntegral_intCast (p := p) n

theorem isPIntegral_zero : IsPIntegral p 0 := by simpa using isPIntegral_natCast (p := p) 0

theorem isPIntegral_one : IsPIntegral p 1 := by simpa using isPIntegral_natCast (p := p) 1

theorem IsPIntegral.pow {x : ℚ} (hx : IsPIntegral p x) (n : ℕ) : IsPIntegral p (x ^ n) := by
  rw [isPIntegral_iff_mem] at *; exact pow_mem hx n

theorem isPIntegral_sum {ι : Type*} (s : Finset ι) {f : ι → ℚ} (hf : ∀ i ∈ s, IsPIntegral p (f i)) :
    IsPIntegral p (∑ i ∈ s, f i) := by
  simp_rw [isPIntegral_iff_mem] at *; exact sum_mem hf

omit hp in
/-- The inverse of a rational whose numerator is prime to `p` is `p`-integral. -/
theorem isPIntegral_inv_of_not_dvd_num {x : ℚ} (hx : ¬ (p : ℤ) ∣ x.num) : IsPIntegral p x⁻¹ := by
  unfold IsPIntegral
  intro h
  apply hx
  rcases eq_or_ne x 0 with h0 | h0
  · subst h0; simp
  · rw [Rat.den_inv_of_ne_zero h0] at h
    exact Int.natCast_dvd.mpr h

theorem PModEq.refl (e : ℕ) (x : ℚ) : PModEq p e x x := by
  simp [PModEq, isPIntegral_zero]

theorem PModEq.symm {e : ℕ} {x y : ℚ} (h : PModEq p e x y) : PModEq p e y x := by
  unfold PModEq at *; rw [← neg_sub, neg_div]; exact h.neg

theorem PModEq.trans {e : ℕ} {x y z : ℚ} (h₁ : PModEq p e x y) (h₂ : PModEq p e y z) :
    PModEq p e x z := by
  unfold PModEq at *
  have : (x - z) / (p : ℚ) ^ e = (x - y) / (p : ℚ) ^ e + (y - z) / (p : ℚ) ^ e := by ring
  rw [this]; exact h₁.add h₂

theorem PModEq.add {e : ℕ} {x y x' y' : ℚ} (h : PModEq p e x y) (h' : PModEq p e x' y') :
    PModEq p e (x + x') (y + y') := by
  unfold PModEq at *
  have : (x + x' - (y + y')) / (p : ℚ) ^ e = (x - y) / (p : ℚ) ^ e + (x' - y') / (p : ℚ) ^ e := by
    ring
  rw [this]; exact h.add h'

theorem PModEq.mul_left {e : ℕ} {x y : ℚ} (c : ℚ) (hc : IsPIntegral p c) (h : PModEq p e x y) :
    PModEq p e (c * x) (c * y) := by
  unfold PModEq at *
  have : (c * x - c * y) / (p : ℚ) ^ e = c * ((x - y) / (p : ℚ) ^ e) := by ring
  rw [this]; exact hc.mul h

/-- `PModEq` is the same as divisibility of the difference in the `p`-integral rationals. -/
theorem pModEq_iff {e : ℕ} {x y : ℚ} :
    PModEq p e x y ↔ ∃ z : ℚ, IsPIntegral p z ∧ x - y = (p : ℚ) ^ e * z := by
  have hp0 : (p : ℚ) ^ e ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  constructor
  · intro h; exact ⟨_, h, by field_simp⟩
  · rintro ⟨z, hz, h⟩; unfold PModEq; rw [h]; field_simp; exact hz

/-- Lowering the exponent of a congruence. -/
theorem PModEq.of_le {e f : ℕ} (hfe : f ≤ e) {x y : ℚ} (h : PModEq p e x y) : PModEq p f x y := by
  obtain ⟨z, hz, hxy⟩ := pModEq_iff.mp h
  refine pModEq_iff.mpr ⟨(p : ℚ) ^ (e - f) * z, ((isPIntegral_natCast p).pow _).mul hz, ?_⟩
  rw [hxy, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hfe]

/-- A congruence of integers modulo `p^e` gives a congruence of rationals. -/
theorem pModEq_of_intModEq {e : ℕ} {a b : ℤ} (h : a ≡ b [ZMOD (p : ℤ) ^ e]) :
    PModEq p e a b := by
  obtain ⟨c, hc⟩ := (Int.modEq_iff_dvd.mp h.symm)
  refine pModEq_iff.mpr ⟨c, isPIntegral_intCast c, ?_⟩
  have : ((a : ℚ) - b) = ((a - b : ℤ) : ℚ) := by push_cast; ring
  rw [this, show a - b = (p : ℤ) ^ e * c by linarith]
  push_cast; ring

end API

end NTKB.IrelandRosen
