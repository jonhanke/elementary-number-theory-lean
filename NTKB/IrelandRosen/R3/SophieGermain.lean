/-
Ireland–Rosen, Chapter 17, §4: Sophie Germain's theorem.
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Coprime.Basic
import Aesop.BuiltinRules
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import NTKB.Attr

/-!
# Sophie Germain's theorem

Ireland–Rosen, Proposition 17.4.1: if `p` is an odd prime and `q = 2p + 1` is prime, then
`x^p + y^p + z^p = 0` has no integral solution with `p ∤ xyz`. We follow the book's proof:
reduce to `(x, y, z)` without common prime factor, factor `y^p + z^p = (y + z) Φ(y, z)` with coprime
factors (so `y + z = A^p`, `Φ = T^p`, and similarly `x + y = B^p`, `x + z = C^p`), and use that
`p`-th powers are `0, ±1` modulo `q`.
-/

namespace NTKB.IrelandRosen.SophieGermain

open Finset

/-- `Φ(y, z) = z^{p-1} - z^{p-2} y + ⋯ + y^{p-1}`, with `y^p + z^p = (y + z) Φ(y, z)` for odd `p`. -/
def phi (p : ℕ) (y z : ℤ) : ℤ := ∑ i ∈ range p, z ^ i * (-y) ^ (p - 1 - i)

lemma add_pow_eq_mul_phi {p : ℕ} (hp : Odd p) (y z : ℤ) : y ^ p + z ^ p = (y + z) * phi p y z := by
  have h := geom_sum₂_mul z (-y) p
  rw [hp.neg_pow] at h
  rw [phi, mul_comm, show y + z = z - -y by ring, h]; ring

lemma dvd_phi_sub (p : ℕ) (y z : ℤ) : (y + z) ∣ phi p y z - p * z ^ (p - 1) := by
  have hp' : (p : ℤ) * z ^ (p - 1) = ∑ i ∈ range p, z ^ i * z ^ (p - 1 - i) := by
    rw [sum_congr rfl (g := fun _ => z ^ (p - 1)) (fun i hi => by
      rw [← pow_add]; congr 1; rw [mem_range] at hi; omega)]
    simp
  have : phi p y z - p * z ^ (p - 1) =
      ∑ i ∈ range p, z ^ i * ((-y) ^ (p - 1 - i) - z ^ (p - 1 - i)) := by
    rw [phi, hp', ← sum_sub_distrib]; exact sum_congr rfl fun i _ => by ring
  rw [this]
  refine dvd_sum fun i _ => dvd_mul_of_dvd_right ?_ _
  have := sub_dvd_pow_sub_pow (-y) z (p - 1 - i)
  rw [show -y - z = -(y + z) by ring, neg_dvd] at this
  exact this

/-- The coprime factorization: if `x^p + y^p + z^p = 0` with no prime dividing all of `x, y, z`
and `p ∤ x`, then `y + z` and `Φ(y, z)` are coprime `p`-th powers. -/
lemma exists_pow_of_add {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x y z : ℤ}
    (h : x ^ p + y ^ p + z ^ p = 0) (hg : ∀ r : ℤ, Prime r → r ∣ x → r ∣ y → r ∣ z → False)
    (hpx : ¬ (p : ℤ) ∣ x) :
    ∃ A T : ℤ, y + z = A ^ p ∧ phi p y z = T ^ p ∧ IsCoprime A T := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hx : (y + z) * phi p y z = (-x) ^ p := by
    rw [← add_pow_eq_mul_phi hodd, hodd.neg_pow]; linarith
  have hcop : IsCoprime (y + z) (phi p y z) := by
    refine isCoprime_of_prime_dvd (fun h0 => ?_) fun r hr h1 h2 => ?_
    · -- `y + z = 0 = Φ` would force `x = 0`, divisible by `p`
      apply hpx
      have : (-x) ^ p = 0 := by rw [← hx, h0.1, zero_mul]
      rw [neg_eq_zero.1 (pow_eq_zero_iff hp.ne_zero |>.1 this)]; exact dvd_zero _
    · have hxr : r ∣ x := by
        have : r ∣ (-x) ^ p := hx ▸ dvd_mul_of_dvd_left h1 _
        exact (dvd_neg).1 (hr.dvd_of_dvd_pow this)
      have h3 : r ∣ (p : ℤ) * z ^ (p - 1) := by
        have := dvd_sub h2 (h1.trans (dvd_phi_sub p y z))
        simpa using this
      rcases hr.dvd_or_dvd h3 with h4 | h4
      · -- `r ∣ p`, so `r` and `p` are associate and `p ∣ x`
        have : (p : ℤ) ∣ r := by
          rcases (hpZ.irreducible.dvd_iff).1 h4 |>.resolve_left hr.not_unit with ⟨u, hu⟩
          exact ⟨u, hu.symm⟩
        exact hpx (this.trans hxr)
      · have hzr := hr.dvd_of_dvd_pow h4
        have hyr : r ∣ y := by have := dvd_sub h1 hzr; simpa using this
        exact hg r hr hxr hyr hzr
  obtain ⟨A, hA⟩ := Int.eq_pow_of_mul_eq_pow_odd_left hcop hodd hx
  obtain ⟨T, hT⟩ := Int.eq_pow_of_mul_eq_pow_odd_right hcop hodd hx
  refine ⟨A, T, hA, hT, ?_⟩
  rw [hA, hT] at hcop
  exact (IsCoprime.pow_iff hp.pos hp.pos).1 hcop

/-! ### Arithmetic modulo `q = 2p + 1` -/

section ModQ

variable {p : ℕ} {q : ℕ} [hq : Fact q.Prime] (hqp : q = 2 * p + 1)
include hqp

lemma pow_eq_one_or_neg_one {n : ZMod q} (hn : n ≠ 0) : n ^ p = 1 ∨ n ^ p = -1 := by
  have h := ZMod.pow_card_sub_one_eq_one hn
  rw [show q - 1 = p * 2 by omega, pow_mul] at h
  exact mul_self_eq_one_iff.1 (by rw [← sq]; exact h)

lemma three_ne_zero (hp : 3 ≤ p) : (3 : ZMod q) ≠ 0 := by
  intro h
  have := (ZMod.natCast_eq_zero_iff 3 q).1 (by exact_mod_cast h)
  have := Nat.le_of_dvd (by norm_num) this
  omega

lemma sum_pow_ne_zero (hp : 3 ≤ p) {a b c : ZMod q} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    a ^ p + b ^ p + c ^ p ≠ 0 := by
  have h3 := three_ne_zero hqp hp
  have h1 : (1 : ZMod q) ≠ 0 := one_ne_zero
  rcases pow_eq_one_or_neg_one hqp ha with h | h <;>
  rcases pow_eq_one_or_neg_one hqp hb with h' | h' <;>
  rcases pow_eq_one_or_neg_one hqp hc with h'' | h'' <;> rw [h, h', h''] <;> intro hs
  · exact h3 (by linear_combination hs)
  · exact h1 (by linear_combination hs)
  · exact h1 (by linear_combination hs)
  · exact h1 (by linear_combination -hs)
  · exact h1 (by linear_combination hs)
  · exact h1 (by linear_combination -hs)
  · exact h1 (by linear_combination -hs)
  · exact h3 (by linear_combination -hs)

end ModQ

lemma intCast_eq_zero_iff {q : ℕ} (n : ℤ) : (n : ZMod q) = 0 ↔ (q : ℤ) ∣ n :=
  ZMod.intCast_zmod_eq_zero_iff_dvd n q

/-- The case `q ∣ x` of the proof. -/
lemma false_of_dvd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {q : ℕ} [hq : Fact q.Prime]
    (hqp : q = 2 * p + 1) {x y z : ℤ} (h : x ^ p + y ^ p + z ^ p = 0)
    (hg : ∀ r : ℤ, Prime r → r ∣ x → r ∣ y → r ∣ z → False)
    (hpx : ¬ (p : ℤ) ∣ x) (hpy : ¬ (p : ℤ) ∣ y) (hpz : ¬ (p : ℤ) ∣ z) (hqx : (q : ℤ) ∣ x) :
    False := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hq.out
  obtain ⟨A, T, hA, hT, hAT⟩ := exists_pow_of_add hp hp2 h hg hpx
  obtain ⟨B, -, hB, -, -⟩ := exists_pow_of_add hp hp2 (x := z) (y := x) (z := y)
    (by linear_combination h) (fun r hr h1 h2 h3 => hg r hr h2 h3 h1) hpz
  obtain ⟨C, -, hC, -, -⟩ := exists_pow_of_add hp hp2 (x := y) (y := x) (z := z)
    (by linear_combination h) (fun r hr h1 h2 h3 => hg r hr h2 h1 h3) hpy
  -- `B^p + C^p + (-A)^p = 2x ≡ 0 (mod q)`
  have hsum : (B : ZMod q) ^ p + (C : ZMod q) ^ p + (-(A : ZMod q)) ^ p = 0 := by
    have hx0 : (x : ZMod q) = 0 := (intCast_eq_zero_iff x).2 hqx
    have : B ^ p + C ^ p + (-A) ^ p = 2 * x := by rw [hodd.neg_pow, ← hA, ← hB, ← hC]; ring
    have := congrArg (fun t : ℤ => (t : ZMod q)) this
    push_cast at this
    rw [this, hx0, mul_zero]
  have hx0 : (x : ZMod q) = 0 := (intCast_eq_zero_iff x).2 hqx
  have hcast : ∀ a b : ℤ, a = b → (a : ZMod q) = b := fun a b h => by rw [h]
  have hall : (y : ZMod q) = 0 → (z : ZMod q) = 0 → False := fun hy hz =>
    hg (q : ℤ) hqZ hqx ((intCast_eq_zero_iff y).1 hy) ((intCast_eq_zero_iff z).1 hz)
  have hp0 : p ≠ 0 := hp.ne_zero
  have heq := hcast _ _ h
  push_cast at heq
  rw [hx0, zero_pow hp0, zero_add] at heq
  have hB0 : (B : ZMod q) ≠ 0 := by
    intro hB'
    have := hcast _ _ hB; push_cast at this
    rw [hB', zero_pow hp0, hx0, zero_add] at this
    refine hall this ?_
    rw [this, zero_pow hp0, zero_add] at heq
    exact pow_eq_zero_iff hp0 |>.1 heq
  have hC0 : (C : ZMod q) ≠ 0 := by
    intro hC'
    have := hcast _ _ hC; push_cast at this
    rw [hC', zero_pow hp0, hx0, zero_add] at this
    refine hall ?_ this
    rw [this, zero_pow hp0, add_zero] at heq
    exact pow_eq_zero_iff hp0 |>.1 heq
  have hA0 : (A : ZMod q) = 0 := by
    by_contra hA
    exact sum_pow_ne_zero hqp hp3 hB0 hC0 (neg_ne_zero.2 hA) hsum
  -- `q ∤ T`, so `T^p ≡ ±1`
  have hT0 : (T : ZMod q) ≠ 0 := by
    intro hT0
    rw [intCast_eq_zero_iff] at hA0 hT0
    exact hqZ.not_unit (hAT.isUnit_of_dvd' hA0 hT0)
  -- `y + z ≡ 0`, so `Φ(y, z) ≡ p z^{p-1}`
  have hyz : (y : ZMod q) + z = 0 := by
    have := hcast _ _ hA; push_cast at this; rw [this, hA0, zero_pow hp0]
  have hphi : ((phi p y z : ℤ) : ZMod q) = p * (z : ZMod q) ^ (p - 1) := by
    obtain ⟨k, hk⟩ := dvd_phi_sub p y z
    have := hcast _ _ hk; push_cast at this
    rw [hyz, zero_mul, sub_eq_zero] at this; exact this
  rw [hT] at hphi; push_cast at hphi
  -- `z^{p-1} = y^{p-1} = (B^p)^{p-1} = 1`
  have hyB : (y : ZMod q) = (B : ZMod q) ^ p := by
    have := hcast _ _ hB; push_cast at this; rw [hx0, zero_add] at this; exact this
  have heven : Even (p - 1) := by
    rcases hodd with ⟨k, hk⟩; exact ⟨k, by omega⟩
  have hz1 : (z : ZMod q) ^ (p - 1) = 1 := by
    rw [show (z : ZMod q) = -y by linear_combination hyz, heven.neg_pow, hyB]
    rcases pow_eq_one_or_neg_one hqp hB0 with h1 | h1 <;> rw [h1]
    · simp
    · exact heven.neg_one_pow
  rw [hz1, mul_one] at hphi
  rcases pow_eq_one_or_neg_one hqp hT0 with h1 | h1 <;> rw [h1] at hphi
  · -- `p ≡ 1 (mod q)`
    have : ((p - 1 : ℕ) : ZMod q) = 0 := by
      rw [Nat.cast_sub hp.one_le, ← hphi]; simp
    have := Nat.le_of_dvd (by omega) ((ZMod.natCast_eq_zero_iff _ _).1 this)
    omega
  · have : ((p + 1 : ℕ) : ZMod q) = 0 := by
      push_cast; rw [← hphi]; simp
    have := Nat.le_of_dvd (by omega) ((ZMod.natCast_eq_zero_iff _ _).1 this)
    omega

/-- **Proposition 17.4.1 (Sophie Germain).** If `p` is an odd prime such that `q = 2p + 1` is also
prime, then `x^p + y^p + z^p = 0` has no integral solution with `p ∤ xyz`. -/
@[kb "irelandrosen1990" "Prop 17.4.1, p. 286"]
theorem sophie_germain {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : (2 * p + 1).Prime) :
    ¬ ∃ x y z : ℤ, x ^ p + y ^ p + z ^ p = 0 ∧ ¬ (p : ℤ) ∣ x * y * z := by
  haveI := Fact.mk hq
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  rintro ⟨x, y, z, h, hxyz⟩
  -- reduce to a solution without a common prime factor, by descent on `|x|`
  suffices H : ∀ n : ℕ, ∀ x y z : ℤ, x.natAbs = n → x ^ p + y ^ p + z ^ p = 0 →
      ¬ (p : ℤ) ∣ x * y * z → False from H _ x y z rfl h hxyz
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x y z hn h hxyz
  have hpx : ¬ (p : ℤ) ∣ x := fun hd => hxyz (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd _) _)
  have hpy : ¬ (p : ℤ) ∣ y := fun hd => hxyz (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd _) _)
  have hpz : ¬ (p : ℤ) ∣ z := fun hd => hxyz (dvd_mul_of_dvd_right hd _)
  by_cases hg : ∃ r : ℤ, Prime r ∧ r ∣ x ∧ r ∣ y ∧ r ∣ z
  · obtain ⟨r, hr, ⟨x', rfl⟩, ⟨y', rfl⟩, ⟨z', rfl⟩⟩ := hg
    have hx0 : x' ≠ 0 := by rintro rfl; exact hpx (by simp)
    refine ih x'.natAbs ?_ x' y' z' rfl ?_ ?_
    · rw [← hn, Int.natAbs_mul]
      have : 1 < r.natAbs := by
        have := Int.natAbs_pos.2 hr.ne_zero
        rcases Nat.lt_or_ge 1 r.natAbs with h' | h'
        · exact h'
        · exfalso; exact hr.not_unit (Int.isUnit_iff_natAbs_eq.2 (by omega))
      have := Int.natAbs_pos.2 hx0
      nlinarith
    · have hr0 : r ^ p ≠ 0 := pow_ne_zero _ hr.ne_zero
      apply (mul_eq_zero.1 (show r ^ p * (x' ^ p + y' ^ p + z' ^ p) = 0 by
        rw [← h]; ring)).resolve_left hr0
    · intro hd; apply hxyz
      exact dvd_trans hd ⟨r * r * r, by ring⟩
  push_neg at hg
  have hg' : ∀ r : ℤ, Prime r → r ∣ x → r ∣ y → r ∣ z → False := fun r hr h1 h2 h3 =>
    hg r hr h1 h2 h3
  -- one of `x, y, z` is divisible by `q`
  have hqp : 2 * p + 1 = 2 * p + 1 := rfl
  by_cases hx : (x : ZMod (2 * p + 1)) = 0
  · exact false_of_dvd hp hp2 rfl h hg' hpx hpy hpz ((intCast_eq_zero_iff x).1 hx)
  by_cases hy : (y : ZMod (2 * p + 1)) = 0
  · exact false_of_dvd hp hp2 rfl (x := y) (y := x) (z := z) (by linear_combination h)
      (fun r hr h1 h2 h3 => hg' r hr h2 h1 h3) hpy hpx hpz ((intCast_eq_zero_iff y).1 hy)
  by_cases hz : (z : ZMod (2 * p + 1)) = 0
  · exact false_of_dvd hp hp2 rfl (x := z) (y := x) (z := y) (by linear_combination h)
      (fun r hr h1 h2 h3 => hg' r hr h2 h3 h1) hpz hpx hpy ((intCast_eq_zero_iff z).1 hz)
  have := sum_pow_ne_zero rfl hp3 hx hy hz
  apply this
  have := congrArg (fun t : ℤ => (t : ZMod (2 * p + 1))) h
  push_cast at this
  exact this

end NTKB.IrelandRosen.SophieGermain
