/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Dirichlet's construction of a ternary form of determinant one representing `n`

For `n ≢ 0, 4, 7 (mod 8)` there are integers `a, b, c` with `a > 0`, `d = ac - b² > 0` and
`nd - c = 1`; then the ternary form with matrix `[[a, b, 1], [b, c, 0], [1, 0, n]]` is positive
definite of determinant `nd - c = 1` and represents `n` (at `(0, 0, 1)`).

Construction (Dirichlet; Nathanson, *Additive Number Theory: the Classical Bases*, Lemmas 1.6–1.8):
choose `d` with `c = nd - 1` a prime `p` (for `n ≡ 2 (mod 4)`, with `p ≡ n - 1 (mod 4n)`) or twice a
prime `p` (for `n` odd, with `p ≡ (rn - 1)/2 (mod 4n)`, `r = 1` if `n ≡ 3 (mod 8)` and `r = 3`
otherwise), using Dirichlet's theorem on primes in progressions (Mathlib's
`Nat.forall_exists_prime_gt_and_modEq`). Quadratic reciprocity for the Jacobi symbol shows that
`-d` is a square modulo `p`; then `b² ≡ -d (mod c)` and `a = (b² + d)/c`.
-/

open ZMod

namespace NTKB.HardyWright.ThreeSquares

/-- From `c = nd - 1 > 0`, `d > 0` and `c ∣ b² + d` to the integers of the ternary form. -/
lemma exists_form_of_dvd {n d c b : ℤ} (hd : 0 < d) (hc : 0 < c) (hcnd : c = n * d - 1)
    (hdvd : c ∣ b ^ 2 + d) : ∃ a b c : ℤ, 0 < a ∧ 0 < a * c - b ^ 2 ∧ n * (a * c - b ^ 2) - c = 1 := by
  obtain ⟨a, ha⟩ := hdvd
  refine ⟨a, b, c, ?_, ?_, ?_⟩
  · by_contra h
    push_neg at h
    nlinarith [sq_nonneg b]
  · nlinarith
  · have : a * c - b ^ 2 = d := by linarith
    rw [this]; linarith

/-- If the Jacobi symbol `(-d / p)` is `1` for a prime `p`, then `p ∣ b² + d` for some `b`. -/
lemma exists_dvd_sq_add {p : ℕ} (hp : p.Prime) {d : ℤ} (h : jacobiSym (-d) p = 1) :
    ∃ b : ℤ, (p : ℤ) ∣ b ^ 2 + d := by
  haveI := Fact.mk hp
  rw [← jacobiSym.legendreSym.to_jacobiSym] at h
  have h0 : ((-d : ℤ) : ZMod p) ≠ 0 := by
    intro h0
    rw [(legendreSym.eq_zero_iff p (-d)).mpr h0] at h
    norm_num at h
  obtain ⟨r, hr⟩ := (legendreSym.eq_one_iff p h0).mp h
  refine ⟨(r.val : ℤ), ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_val, ZMod.cast_id', id, sq, ← hr]
  push_cast; ring

/-- `J(2 | d) J(p | d) = J(-1 | d)` when `2p ≡ -1 (mod d)`. -/
lemma jacobi_p_of_two_mul {p d : ℕ} (hd : Odd d) (h : ((2 * p : ℕ) : ℤ) % d = (-1 : ℤ) % d) :
    jacobiSym 2 d * jacobiSym p d = jacobiSym (-1) d := by
  rw [← jacobiSym.mul_left]
  exact jacobiSym.mod_left' (by push_cast at h ⊢; exact h)

/-- The case `n ≡ 2 (mod 4)`. -/
lemma exists_form_two_mod_four {n : ℕ} (hn : n % 4 = 2) :
    ∃ a b c : ℤ, 0 < a ∧ 0 < a * c - b ^ 2 ∧ (n : ℤ) * (a * c - b ^ 2) - c = 1 := by
  have hn2 : 2 ≤ n := by omega
  have hcop : (n - 1).Coprime (4 * n) := by
    apply Nat.Coprime.mul_right
    · have : Odd (n - 1) := by rw [Nat.odd_iff]; omega
      have : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [this]
      exact Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr ‹Odd (n - 1)›)
    · have h1 : n = (n - 1) + 1 := by omega
      conv_rhs => rw [h1]
      simp
  obtain ⟨p, hpn, hp, hpmod⟩ := Nat.forall_exists_prime_gt_and_modEq n (by omega) hcop
  have hpmod' : p % (4 * n) = n - 1 := by
    rw [Nat.ModEq] at hpmod; rw [hpmod]; exact Nat.mod_eq_of_lt (by omega)
  set j := p / (4 * n) with hj
  have hpj : p = 4 * n * j + (n - 1) := by
    have := Nat.div_add_mod p (4 * n); rw [hpmod', ← hj] at this; linarith
  set d := 4 * j + 1 with hd
  have hpd : p = n * d - 1 := by
    rw [hd, hpj]
    have : n * (4 * j + 1) = 4 * n * j + n := by ring
    omega
  obtain ⟨N, hN⟩ : ∃ N, N = n * j := ⟨_, rfl⟩
  have hp4 : p % 4 = 1 := by
    have : p = 4 * N + (n - 1) := by rw [hpj, hN]; ring
    omega
  have hdodd : Odd d := by rw [hd]; exact ⟨2 * j, by ring⟩
  have hpodd : Odd p := Nat.odd_iff.mpr (by omega)
  -- `(-d / p) = 1`
  have hJ : jacobiSym (-(d : ℤ)) p = 1 := by
    rw [neg_eq_neg_one_mul, jacobiSym.mul_left, jacobiSym.at_neg_one hpodd,
      χ₄_nat_one_mod_four hp4, one_mul]
    rw [jacobiSym.quadratic_reciprocity_one_mod_four' hdodd hp4]
    have hmod : ((p : ℕ) : ℤ) % (d : ℕ) = (-1 : ℤ) % (d : ℕ) := by
      have hd1 : (1 : ℕ) ≤ n * d := by
        have : 1 ≤ d := by omega
        nlinarith
      have : ((p : ℕ) : ℤ) = (n : ℤ) * (d : ℤ) - 1 := by
        rw [hpd]; push_cast [Nat.cast_sub hd1]; ring
      rw [this]
      exact Int.modEq_iff_dvd.mpr ⟨-(n : ℤ), by ring⟩
    rw [jacobiSym.mod_left' hmod, jacobiSym.at_neg_one hdodd,
      χ₄_nat_one_mod_four (by omega)]
  obtain ⟨b, hb⟩ := exists_dvd_sq_add hp hJ
  have hd1 : (1 : ℕ) ≤ n * d := by
    have : 1 ≤ d := by omega
    nlinarith
  exact exists_form_of_dvd (d := d) (c := p) (b := b) (by positivity)
    (by exact_mod_cast hp.pos) (by rw [hpd]; push_cast [Nat.cast_sub hd1]; ring) hb

/-- The case `n` odd, `n ≢ 7 (mod 8)`. -/
lemma exists_form_odd {n : ℕ} (hn : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5) :
    ∃ a b c : ℤ, 0 < a ∧ 0 < a * c - b ^ 2 ∧ (n : ℤ) * (a * c - b ^ 2) - c = 1 := by
  set r : ℕ := if n % 8 = 3 then 1 else 3 with hr
  have hr8 : (n % 8 = 3 ∧ r = 1) ∨ (n % 8 ≠ 3 ∧ r = 3) := by
    by_cases h : n % 8 = 3
    · left; exact ⟨h, by simp [hr, h]⟩
    · right; exact ⟨h, by simp [hr, h]⟩
  have hn1 : 1 ≤ n := by omega
  set a0 := (r * n - 1) / 2 with ha0
  have h2a0 : 2 * a0 = r * n - 1 := by
    rcases hr8 with ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h'] at ha0 ⊢ <;> omega
  have ha0lt : a0 < 4 * n := by
    rcases hr8 with ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h'] at h2a0 <;> omega
  have ha0odd : a0 % 2 = 1 := by
    rcases hr8 with ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h'] at h2a0 <;> omega
  have hcop : a0.Coprime (4 * n) := by
    apply Nat.Coprime.mul_right
    · have : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [this]
      exact Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr (Nat.odd_iff.mpr ha0odd))
    · rw [Nat.coprime_iff_gcd_eq_one, Nat.eq_one_iff_not_exists_prime_dvd]
      intro q hq hqd
      have h1 : q ∣ a0 := hqd.trans (Nat.gcd_dvd_left _ _)
      have h2 : q ∣ n := hqd.trans (Nat.gcd_dvd_right _ _)
      have h3 : q ∣ 2 * a0 := dvd_mul_of_dvd_right h1 2
      have h4 : q ∣ r * n := dvd_mul_of_dvd_right h2 r
      have h5 : r * n = 2 * a0 + 1 := by
        have : 1 ≤ r * n := by rcases hr8 with ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h'] <;> omega
        omega
      rw [h5] at h4
      have : q ∣ 1 := (Nat.dvd_add_right h3).mp h4
      exact hq.one_lt.ne' (Nat.dvd_one.mp this)
  obtain ⟨p, hpn, hp, hpmod⟩ := Nat.forall_exists_prime_gt_and_modEq (n + 2) (by omega) hcop
  have hpmod' : p % (4 * n) = a0 := by
    rw [Nat.ModEq] at hpmod; rw [hpmod]; exact Nat.mod_eq_of_lt ha0lt
  set j := p / (4 * n) with hj
  have hpj : p = 4 * n * j + a0 := by
    have := Nat.div_add_mod p (4 * n); rw [hpmod', ← hj] at this; linarith
  set d := 8 * j + r with hd
  have h2p : 2 * p + 1 = n * d := by
    rw [hd, hpj]
    have : n * (8 * j + r) = 2 * (4 * n * j) + r * n := by ring
    omega
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  obtain ⟨N, hN⟩ : ∃ N, N = n * j := ⟨_, rfl⟩
  have hd8 : d % 8 = r := by
    rw [hd]; rcases hr8 with ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h'] <;> omega
  have hdodd : Odd d := Nat.odd_iff.mpr (by rcases hr8 with ⟨h, h'⟩ | ⟨h, h'⟩ <;> omega)
  -- `(p / d) = 1`
  have hmod : ((2 * p : ℕ) : ℤ) % (d : ℕ) = (-1 : ℤ) % (d : ℕ) := by
    have : ((2 * p : ℕ) : ℤ) = (n : ℤ) * (d : ℤ) - 1 := by
      have := congrArg (fun t : ℕ => (t : ℤ)) h2p; push_cast at this ⊢; linarith
    rw [this]
    exact Int.modEq_iff_dvd.mpr ⟨-(n : ℤ), by ring⟩
  have hJ2 := jacobi_p_of_two_mul hdodd hmod
  rw [jacobiSym.at_two hdodd, jacobiSym.at_neg_one hdodd] at hJ2
  have hJpd : jacobiSym p d = 1 := by
    rcases hr8 with ⟨h, h'⟩ | ⟨h, h'⟩
    · rw [h'] at hd8
      rw [χ₈_nat_eq_if_mod_eight, χ₄_nat_one_mod_four (by omega)] at hJ2
      simp only [show d % 2 = 1 by omega, hd8] at hJ2
      norm_num at hJ2
      exact_mod_cast hJ2
    · rw [h'] at hd8
      rw [χ₈_nat_eq_if_mod_eight, χ₄_nat_three_mod_four (by omega)] at hJ2
      simp only [show d % 2 = 1 by omega, hd8] at hJ2
      norm_num at hJ2
      have : (jacobiSym p d) = 1 := by linarith
      exact this
  -- `(-d / p) = 1`
  have hJ : jacobiSym (-(d : ℤ)) p = 1 := by
    rw [neg_eq_neg_one_mul, jacobiSym.mul_left, jacobiSym.at_neg_one hpodd]
    have hp4 : p % 4 = 1 ∨ (p % 4 = 3 ∧ d % 4 = 3) := by
      have : 2 * (4 * N + a0) + 1 = n * d := by rw [← h2p, hpj, hN]; ring
      rcases hr8 with ⟨h, h'⟩ | ⟨h, h'⟩
      · left
        have hpN : p = 4 * N + a0 := by rw [hpj, hN]; ring
        rw [h'] at h2a0
        omega
      · have hpN : p = 4 * N + a0 := by rw [hpj, hN]; ring
        rw [h'] at h2a0
        omega
    rcases hp4 with hp4 | ⟨hp4, hd4⟩
    · rw [χ₄_nat_one_mod_four hp4, one_mul,
        jacobiSym.quadratic_reciprocity_one_mod_four' hdodd hp4]
      exact_mod_cast hJpd
    · rw [χ₄_nat_three_mod_four hp4, jacobiSym.quadratic_reciprocity_three_mod_four hd4 hp4]
      rw [hJpd]; norm_num
  obtain ⟨b0, hb0⟩ := exists_dvd_sq_add hp hJ
  -- make `b` odd
  obtain ⟨b, hb, hbodd⟩ : ∃ b : ℤ, (p : ℤ) ∣ b ^ 2 + d ∧ Odd b := by
    rcases Int.even_or_odd b0 with he | ho
    · refine ⟨b0 + p, ?_, ?_⟩
      · have : (b0 + p) ^ 2 + d = (b0 ^ 2 + d) + p * (2 * b0 + p) := by ring
        rw [this]; exact dvd_add hb0 (dvd_mul_right _ _)
      · exact he.add_odd (by exact_mod_cast hpodd)
    · exact ⟨b0, hb0, ho⟩
  have h2 : (2 : ℤ) ∣ b ^ 2 + d := by
    have hdo : Odd (d : ℤ) := by exact_mod_cast hdodd
    exact (hbodd.pow.add_odd hdo).two_dvd
  have hcop2 : IsCoprime (2 : ℤ) p := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (by omega)
    exact_mod_cast this
  have hdvd : (2 * p : ℤ) ∣ b ^ 2 + d := hcop2.mul_dvd h2 hb
  refine exists_form_of_dvd (d := d) (c := 2 * p) (b := b) (by positivity)
    (by have := hp.pos; positivity) ?_ hdvd
  have := congrArg (fun t : ℕ => (t : ℤ)) h2p
  push_cast at this
  linarith

/-- **Dirichlet's construction.** For `n ≢ 0, 4, 7 (mod 8)` there are integers `a, b, c` with
`a > 0`, `ac - b² > 0` and `n(ac - b²) - c = 1`. -/
theorem exists_form (n : ℕ) (hn : n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 6) :
    ∃ a b c : ℤ, 0 < a ∧ 0 < a * c - b ^ 2 ∧ (n : ℤ) * (a * c - b ^ 2) - c = 1 := by
  rcases hn with h | h | h | h | h
  · exact exists_form_odd (Or.inl h)
  · exact exists_form_two_mod_four (by omega)
  · exact exists_form_odd (Or.inr (Or.inl h))
  · exact exists_form_odd (Or.inr (Or.inr h))
  · exact exists_form_two_mod_four (by omega)

end NTKB.HardyWright.ThreeSquares
