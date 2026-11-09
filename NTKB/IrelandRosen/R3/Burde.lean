/-
Ireland–Rosen, Chapter 9, §10: rational biquadratic reciprocity.
-/
import NTKB.IrelandRosen.R3.Reciprocity
import NTKB.Elementary.SpecialValues.QuadraticGaussSum
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import NTKB.IrelandRosen.R3.RationalPrimes

/-!
# Rational biquadratic reciprocity (Burde)

Ireland–Rosen, Chapter 9, §10. Throughout, `p ≠ q` are primes `≡ 1 (mod 4)`, `π` is an irreducible
of `ℤ[i]` dividing `p` and `λ` one dividing `q`; `ψ_q` is the Legendre symbol modulo `q`.

* Lemma 1: `χ_π(q) = 1` iff `x⁴ ≡ q (mod p)` is solvable in `ℤ`;
* Lemma 2: if `ψ_p(q) = 1` then `χ_π(q) = ±1`;
* Proposition 9.10.1: `g(χ_π)² = -(-1)^((p-1)/4) √p π` (Gauss sums in `ℂ`, with Gauss's sign
  of the quadratic Gauss sum, `NTKB.gaussSum_legendreChar`);
* Proposition 9.10.2: `χ_π(q) χ_λ(p) ≡ π^((q-1)/2) (mod q)` for primary `π`;
* Proposition 9.10.3 and Lemma 3: `π^((q-1)/2) ≡ ψ_q(d) ψ_q(ad - bc) (mod q)`;
* Lemma 4: `ψ_q(d) = (-1)^((q-1)/4)` for `q = c² + d²`, `c > 0` odd;
* Theorem 3 (Burde): `χ_π(q) χ_λ(p) = (-1)^((q-1)/4) ψ_q(ad - bc)` for `p = a² + b²`,
  `q = c² + d²`, `a, c` odd, `π = a + b i`, `λ = c + d i`, when `ψ_q(p) = 1`.
-/

namespace NTKB.IrelandRosen

open Zsqrtd

local notation "ℤ[i]" => GaussianInt

namespace Gaussian

/-! ### Elementary facts -/

/-- Euler's criterion as a divisibility in `ℤ`: `q ∣ n ^ ((q - 1) / 2) - ψ_q(n)`. -/
lemma dvd_pow_sub_legendreSym {q : ℕ} [Fact q.Prime] (n : ℤ) :
    (q : ℤ) ∣ n ^ (q / 2) - legendreSym q n := by
  have h := legendreSym.eq_pow q n
  rw [← Int.cast_pow] at h
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ q).1 h.symm |> fun h' => by
    rw [← dvd_neg]; convert h' using 1; ring

lemma eq_of_dvd_sub_of_sq_eq_one {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {x y : ℤ}
    (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) (h : (q : ℤ) ∣ x - y) : x = y := by
  have hq3 : (3 : ℤ) ≤ q := by have := hq.two_le; have : q ≠ 2 := hq2; omega
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · rfl
  · exfalso; obtain ⟨k, hk⟩ := h; norm_num at hk
    rcases lt_trichotomy k 0 with hk0 | hk0 | hk0 <;> nlinarith
  · exfalso; obtain ⟨k, hk⟩ := h; norm_num at hk
    rcases lt_trichotomy k 0 with hk0 | hk0 | hk0 <;> nlinarith
  · rfl

lemma not_dvd_of_sq_add_sq {q : ℕ} (hq : q.Prime) {c d : ℤ} (h : (q : ℤ) = c ^ 2 + d ^ 2) :
    ¬ (q : ℤ) ∣ d := by
  intro hd
  have hne := (natCast_prime_sq_add_sq hq h.symm).2
  obtain ⟨k, rfl⟩ := hd
  have hk : k ≠ 0 := by rintro rfl; simp at hne
  have h1 : (1 : ℤ) ≤ k ^ 2 := by rw [← sq_abs]; nlinarith [Int.one_le_abs hk]
  have h2 : (2 : ℤ) ≤ q := by exact_mod_cast hq.two_le
  nlinarith [sq_nonneg c, sq_nonneg (q : ℤ)]

lemma legendreSym_neg_one_of_mod_four {q : ℕ} [Fact q.Prime] (hq : q % 4 = 1) :
    legendreSym q (-1) = 1 :=
  (legendreSym.at_neg_one (by omega)).trans (by rw [ZMod.χ₄_nat_one_mod_four hq])

/-- **Lemma 3 of §10.** If `p = a² + b²`, `q = c² + d²` and `ψ_q(p) = 1`, then
`ψ_q(ad - bc) = ψ_q(ad + bc)`. -/
@[kb "irelandrosen1990" "Ch. 9, §10, Lemma 3, p. 140"]
theorem legendreSym_sub_eq_add {p q : ℕ} [Fact q.Prime] {a b c d : ℤ}
    (hp : (p : ℤ) = a ^ 2 + b ^ 2) (hq : (q : ℤ) = c ^ 2 + d ^ 2) (hpq : legendreSym q p = 1) :
    legendreSym q (a * d - b * c) = legendreSym q (a * d + b * c) := by
  have hqd : ¬ (q : ℤ) ∣ d := not_dvd_of_sq_add_sq Fact.out hq
  have hd0 : ((d : ℤ) : ZMod q) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hcong : ((a * d - b * c) * (a * d + b * c)) % q = (d ^ 2 * p) % q :=
    Int.emod_eq_emod_iff_emod_sub_eq_zero.2 (Int.emod_eq_zero_of_dvd ⟨-b ^ 2, by
      rw [hp, hq]; ring⟩)
  have hmul : legendreSym q (a * d - b * c) * legendreSym q (a * d + b * c) = 1 := by
    rw [← legendreSym.mul, legendreSym.mod q, hcong, ← legendreSym.mod, legendreSym.mul,
      legendreSym.sq_one' q hd0, one_mul, hpq]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hmul with h | h <;> rw [h] at hmul ⊢ <;> linarith

/-- **Lemma 4 of §10.** If `q ≡ 1 (mod 4)` is prime, `q = c² + d²` with `c > 0` odd, then
`ψ_q(d) = (-1) ^ ((q - 1) / 4)`. -/
@[kb "irelandrosen1990" "Ch. 9, §10, Lemma 4, p. 141"]
theorem legendreSym_eq_neg_one_pow {q : ℕ} [hq : Fact q.Prime] (hq4 : q % 4 = 1) {c d : ℤ}
    (hcd : (q : ℤ) = c ^ 2 + d ^ 2) (hc0 : 0 < c) (hc : Odd c) :
    legendreSym q d = (-1) ^ ((q - 1) / 4) := by
  have hq2 : q ≠ 2 := by omega
  -- `ψ_q(c) = J(q | c) = J(d² | c) = 1`
  have hgcd : Int.gcd d c = 1 := by
    have h2 : (Int.gcd d c) ^ 2 ∣ q := by
      have : ((Int.gcd d c : ℕ) : ℤ) ^ 2 ∣ (q : ℤ) := by
        rw [hcd]
        exact dvd_add (pow_dvd_pow_of_dvd (Int.gcd_dvd_right d c) 2)
          (pow_dvd_pow_of_dvd (Int.gcd_dvd_left d c) 2)
      exact_mod_cast this
    rcases (Nat.dvd_prime hq.out).1 ((dvd_pow_self _ two_ne_zero).trans h2) with h | h
    · exact h
    · exfalso; rw [h] at h2; have := Nat.le_of_dvd hq.out.pos h2; nlinarith [hq.out.two_le]
  have hcn : (c.natAbs : ℤ) = c := Int.natAbs_of_nonneg hc0.le
  have hcodd : Odd c.natAbs := by rwa [Int.natAbs_odd]
  have hψc : legendreSym q c = 1 := by
    rw [jacobiSym.legendreSym.to_jacobiSym, ← hcn,
      ← jacobiSym.quadratic_reciprocity_one_mod_four hq4 hcodd]
    rw [jacobiSym.mod_left' (a₂ := d ^ 2) (by
      rw [hcd, hcn, show c ^ 2 + d ^ 2 = d ^ 2 + c * c by ring, Int.add_mul_emod_self_left])]
    exact jacobiSym.sq_one' (by rw [hcn]; exact hgcd)
  -- Euler: `c ^ ((q - 1) / 2) ≡ (-1) ^ ((q - 1) / 4) d ^ ((q - 1) / 2) (mod q)`
  have hEc := legendreSym.eq_pow q c
  have hEd := legendreSym.eq_pow q d
  have hsq : ((c : ZMod q)) ^ 2 = -((d : ZMod q)) ^ 2 := by
    have : ((q : ℤ) : ZMod q) = 0 := by simp
    rw [hcd] at this; push_cast at this; linear_combination this
  have hk : q / 2 = 2 * ((q - 1) / 4) := by omega
  rw [hψc, hk, pow_mul, hsq, neg_pow, ← pow_mul, ← hk, ← hEd] at hEc
  push_cast at hEc
  have hqd : ¬ (q : ℤ) ∣ d := not_dvd_of_sq_add_sq hq.out hcd
  have hd1 := legendreSym.eq_one_or_neg_one q (a := d) (by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd])
  have hs1 : ((-1 : ℤ) ^ ((q - 1) / 4) = 1 ∨ (-1 : ℤ) ^ ((q - 1) / 4) = -1) := by
    rcases Nat.even_or_odd ((q - 1) / 4) with h | h
    · left; exact h.neg_one_pow
    · right; exact h.neg_one_pow
  refine eq_of_dvd_sub_of_sq_eq_one hq.out hq2 hd1 hs1 ?_
  rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
  push_cast
  -- from `1 = (-1)^k ψ(d)` and `((-1)^k)² = 1`
  have hm : ((-1 : ZMod q) ^ ((q - 1) / 4)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]; simp
  linear_combination ((-1 : ZMod q) ^ ((q - 1) / 4)) * hEc + (legendreSym q d : ZMod q) * hm

/-- For `π` of prime norm `p ≠ 2`, `π` and `π̄` are not associate (Lemma 5 of §7 for any such `π`). -/
lemma not_associated_star_of_prime_norm {π : ℤ[i]} (hp : π.norm.natAbs.Prime)
    (hp2 : π.norm.natAbs ≠ 2) : ¬ Associated π (star π) := by
  rintro ⟨u, hu⟩
  have hN : π.re ^ 2 + π.im ^ 2 = π.norm.natAbs := by rw [natAbs_norm, norm_def]
  obtain ⟨ha0, hb0⟩ := natCast_prime_sq_add_sq hp hN
  have hre := congrArg Zsqrtd.re hu
  have him := congrArg Zsqrtd.im hu
  rcases isUnit_iff_eq.1 u.isUnit with h | h | h | h <;> rw [h] at hre him <;> simp at hre him
  · omega
  · omega
  all_goals
    have him' : π.im ^ 2 = π.re ^ 2 := by
      have : π.im = -π.re ∨ π.im = π.re := by omega
      rcases this with h | h <;> rw [h]; ring
    have : (π.norm.natAbs : ℤ) = 2 * π.re ^ 2 := by rw [← hN, him']; ring
    have e : ((π.re.natAbs : ℕ) : ℤ) * π.re.natAbs = π.re * π.re := Int.natAbs_mul_self' π.re
    have h2 : π.norm.natAbs = 2 * (π.re.natAbs * π.re.natAbs) := by
      have : ((π.norm.natAbs : ℕ) : ℤ) = 2 * ((π.re.natAbs : ℤ) * π.re.natAbs) := by
        rw [e, this]; ring
      exact_mod_cast this
    rcases Nat.prime_mul_iff.1 (h2 ▸ hp) with ⟨-, h3⟩ | ⟨-, h3⟩
    · rw [h3] at h2; omega
    · omega

lemma isCoprime_star_of_prime_norm {ρ : ℤ[i]} (hp : ρ.norm.natAbs.Prime)
    (hp2 : ρ.norm.natAbs ≠ 2) : IsCoprime ρ (star ρ) := by
  have hirr := irreducible_of_prime_norm hp
  refine (Irreducible.coprime_iff_not_dvd hirr).2 fun h => not_associated_star_of_prime_norm hp hp2 ?_
  obtain ⟨γ, hγ⟩ := h
  have hN := congrArg (fun x : ℤ[i] => x.norm.natAbs) hγ
  simp only [natAbs_norm_star, natAbs_norm_mul] at hN
  have hγ1 : γ.norm.natAbs = 1 := (Nat.mul_eq_left hp.ne_zero).1 hN.symm
  rw [hγ]; exact associated_mul_unit_right _ _ (isUnit_iff_natAbs_norm.2 hγ1)

/-! ### Proposition 9.10.3 -/

lemma dvd_sub_legendreSym_aux {q : ℕ} [Fact q.Prime] {ρ x : ℤ[i]} (hρq : ρ ∣ (q : ℤ[i]))
    {d e : ℤ} (hd : ¬ (q : ℤ) ∣ d) (h : ρ ∣ (d : ℤ[i]) * x - e) :
    ρ ∣ x ^ (q / 2) - ((legendreSym q d * legendreSym q e : ℤ) : ℤ[i]) := by
  have hq' : ∀ n : ℤ, ρ ∣ (n : ℤ[i]) ^ (q / 2) - (legendreSym q n : ℤ[i]) := fun n => by
    have := dvd_pow_sub_legendreSym (q := q) n
    have h' : ((q : ℤ) : ℤ[i]) ∣ ((n ^ (q / 2) - legendreSym q n : ℤ) : ℤ[i]) :=
      Int.cast_dvd_cast _ _ this
    push_cast at h'
    exact hρq.trans h'
  have h1 : ρ ∣ ((d : ℤ[i]) * x) ^ (q / 2) - (e : ℤ[i]) ^ (q / 2) :=
    h.trans (sub_dvd_pow_sub_pow _ _ _)
  have hd2 : legendreSym q d * legendreSym q d = 1 := by
    rw [← sq]; exact legendreSym.sq_one q (by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd])
  have hd2' : ((legendreSym q d : ℤ[i])) * (legendreSym q d : ℤ[i]) = 1 := by exact_mod_cast hd2
  -- `ψ(d) x^k ≡ ψ(e)`, then multiply by `ψ(d)`
  have h2 : ρ ∣ (legendreSym q d : ℤ[i]) * x ^ (q / 2) - (legendreSym q e : ℤ[i]) := by
    have := dvd_add (dvd_sub h1 (dvd_mul_of_dvd_left (hq' d) (x ^ (q / 2)))) (hq' e)
    convert this using 1; ring
  have := dvd_mul_of_dvd_right h2 (legendreSym q d : ℤ[i])
  push_cast
  convert this using 1
  linear_combination (-(x ^ (q / 2))) * hd2'

/-- **Proposition 9.10.3.** Let `q ≡ 1 (mod 4)` be prime, `p = a² + b²`, `q = c² + d²` with
`ψ_q(p) = 1`, and `π = a + b i`. Then `π ^ ((q - 1) / 2) ≡ ψ_q(d) ψ_q(ad - bc) (mod q)`. -/
@[kb "irelandrosen1990" "Prop 9.10.3, p. 140"]
theorem pow_modEq_legendreSym_mul {p q : ℕ} [hq : Fact q.Prime] (hq4 : q % 4 = 1) {a b c d : ℤ}
    (hp : (p : ℤ) = a ^ 2 + b ^ 2) (hqcd : (q : ℤ) = c ^ 2 + d ^ 2) (hpq : legendreSym q p = 1) :
    (q : ℤ[i]) ∣ (⟨a, b⟩ : ℤ[i]) ^ ((q - 1) / 2) -
      ((legendreSym q d * legendreSym q (a * d - b * c) : ℤ) : ℤ[i]) := by
  set ρ : ℤ[i] := ⟨c, d⟩
  have hNρ : ρ.norm.natAbs = q := by
    have : ρ.norm = q := by rw [norm_def, hqcd]
    rw [this]; simp
  have hq2 : q ≠ 2 := by omega
  have hqρ : (q : ℤ[i]) = ρ * star ρ := by
    rw [← hNρ, ← Int.cast_natCast, natAbs_norm, Zsqrtd.norm_eq_mul_conj]
  have hd : ¬ (q : ℤ) ∣ d := not_dvd_of_sq_add_sq hq.out hqcd
  have hk : (q - 1) / 2 = q / 2 := by omega
  rw [hk]
  have h1 := dvd_sub_legendreSym_aux (ρ := ρ) (x := ⟨a, b⟩) ⟨star ρ, hqρ⟩ hd (e := a * d - b * c)
    ⟨b, by ext <;> simp [ρ] <;> ring⟩
  have h2 := dvd_sub_legendreSym_aux (ρ := star ρ) (x := ⟨a, b⟩) ⟨ρ, by rw [hqρ, mul_comm]⟩ hd
    (e := a * d + b * c) ⟨-b, by ext <;> simp [ρ] <;> ring⟩
  rw [← legendreSym_sub_eq_add hp hqcd hpq] at h2
  rw [hqρ]
  exact (isCoprime_star_of_prime_norm (hNρ ▸ hq.out) (by omega)).mul_dvd h1 h2

/-! ### Lemmas 1 and 2 -/

/-- **Lemma 1 of §10.** For `π` of prime norm `p ≡ 1 (mod 4)` and a rational integer `q` prime to `p`,
`χ_π(q) = 1` iff `x⁴ ≡ q (mod p)` has a solution in `ℤ`. -/
@[kb "irelandrosen1990" "Ch. 9, §10, Lemma 1, p. 139"]
theorem quarticChar_intCast_eq_one_iff {π : ℤ[i]} (hp : π.norm.natAbs.Prime)
    (hp2 : π.norm.natAbs ≠ 2) {q : ℤ} (hq : ¬ (π.norm.natAbs : ℤ) ∣ q) :
    quarticChar π q = 1 ↔ ∃ x : ℤ, (π.norm.natAbs : ℤ) ∣ x ^ 4 - q := by
  have hπ := irreducible_of_prime_norm hp
  have hint : ∀ n : ℤ, π ∣ (n : ℤ[i]) ↔ (π.norm.natAbs : ℤ) ∣ n := fun n => by
    rw [← toZMod_eq_zero_iff hp, map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hπq : ¬ π ∣ (q : ℤ[i]) := by rwa [hint]
  rw [quarticChar_eq_one_iff hπ hp2 hπq]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨(toZMod hp x).val, ?_⟩
    rw [← hint]
    have hx' : π ∣ x - (((toZMod hp x).val : ℤ) : ℤ[i]) := by
      haveI : NeZero π.norm.natAbs := ⟨hp.ne_zero⟩
      rw [← toZMod_eq_iff hp, map_intCast, Int.cast_natCast, ZMod.natCast_zmod_val]
    have := dvd_sub hx (hx'.trans (sub_dvd_pow_sub_pow x _ 4))
    rw [Int.cast_sub, Int.cast_pow]
    convert this using 1; ring
  · rintro ⟨x, hx⟩
    exact ⟨x, by rw [← hint] at hx; exact_mod_cast hx⟩

/-- **Lemma 2 of §10.** If `ψ_p(q) = 1` then `χ_π(q) = ±1`. -/
@[kb "irelandrosen1990" "Ch. 9, §10, Lemma 2, p. 139"]
theorem quarticChar_eq_one_or_neg_one {π : ℤ[i]} [Fact (Nat.Prime π.norm.natAbs)]
    (hp2 : π.norm.natAbs ≠ 2) {q : ℤ} (hq : legendreSym π.norm.natAbs q = 1) :
    quarticChar π q = 1 ∨ quarticChar π q = -1 := by
  have h := quarticMulChar_sq_apply hp2 q
  rw [MulChar.pow_apply' _ two_ne_zero, quarticMulChar_intCast, hq, Int.cast_one, sq] at h
  exact mul_self_eq_one_iff.1 h

lemma quarticChar_eq_one_or_neg_one' {π : ℤ[i]} {p : ℕ} [Fact p.Prime] (hNπ : π.norm.natAbs = p)
    (hp2 : p ≠ 2) {q : ℤ} (hq : legendreSym p q = 1) :
    quarticChar π q = 1 ∨ quarticChar π q = -1 := by
  subst hNπ
  exact quarticChar_eq_one_or_neg_one hp2 hq

/-! ### Proposition 9.10.1 -/

/-- **Proposition 9.10.1.** Let `π` be the primary irreducible dividing `p` (prime norm). Then
`g(χ_π)² = -(-1)^((p-1)/4) √p π`, the Gauss sum taken in `ℂ` with `ψ(t) = e^{2πit/p}`. -/
@[kb "irelandrosen1990" "Prop 9.10.1, p. 139"]
theorem gaussSum_sq_eq {π : ℤ[i]} [Fact (Nat.Prime π.norm.natAbs)] (hp2 : π.norm.natAbs ≠ 2)
    (hP : IsPrimary π) :
    gaussSum ((quarticMulChar π hp2).ringHomComp GaussianInt.toComplex) ZMod.stdAddChar ^ 2 =
      -((-1 : ℂ) ^ ((π.norm.natAbs - 1) / 4)) * √(π.norm.natAbs : ℝ) * (π : ℂ) := by
  set χ := quarticMulChar π hp2
  set f : ℤ[i] →+* ℂ := GaussianInt.toComplex
  have hp4 := hP.2.natAbs_norm_mod_four
  have hsq : χ.ringHomComp f * χ.ringHomComp f = NTKB.legendreChar π.norm.natAbs := by
    refine MulChar.ext fun u => ?_
    rw [MulChar.mul_apply, ← map_mul, ← sq, MulChar.ringHomComp_apply, NTKB.legendreChar_apply]
    have := quarticMulChar_sq_apply hp2 ((u : ZMod π.norm.natAbs).val : ℤ)
    have e : ((((u : ZMod π.norm.natAbs).val : ℤ)) : ZMod π.norm.natAbs) = u := by simp
    rw [e, MulChar.pow_apply' _ two_ne_zero] at this
    rw [map_pow, this, map_intCast]
    simp only [legendreSym, e]
  have hne : χ.ringHomComp f * χ.ringHomComp f ≠ 1 := by
    rw [← MulChar.ringHomComp_mul, MulChar.ringHomComp_ne_one_iff GaussianInt.toComplex_injective,
      ← sq]
    exact quarticMulChar_sq_ne_one hp2
  have H := jacobiSum_mul_nontrivial hne ZMod.stdAddChar
  rw [hsq, NTKB.gaussSum_legendreChar _ (by omega), if_pos hp4, jacobiSum_ringHomComp,
    jacobiSum_quarticMulChar_eq hp2 hP, quarticMulChar_apply] at H
  rw [sq, ← H]
  have hval : quarticChar π (((-1 : ZMod π.norm.natAbs).val : ℕ) : ℤ[i]) =
      (-1) ^ qexp π := by
    rw [← quarticMulChar_apply hp2, show (-1 : ZMod π.norm.natAbs) = ((-1 : ℤ) : ZMod _) by simp,
      quarticMulChar_intCast, Int.cast_neg, Int.cast_one,
      quarticChar_of_isUnit irreducible_of_fact hp2 isUnit_one.neg]
  rw [hval, qexp]
  simp only [map_mul, map_neg, map_pow, map_one]
  ring

/-! ### Proposition 9.10.2 -/

/-- The prime-by-prime step of Proposition 9.10.2: for a prime `ρ` of norm `q` (the book's `λ`,
or its conjugate), `χ_π(q) χ_ρ(p) ≡ π ^ ((q - 1) / 2) (mod ρ)`. -/
lemma dvd_quarticChar_mul_sub_pow {π : ℤ[i]} [hp : Fact (Nat.Prime π.norm.natAbs)]
    (hp2 : π.norm.natAbs ≠ 2) (hP : IsPrimary π) {ρ : ℤ[i]} {q : ℕ} (hq : q.Prime)
    (hNρ : ρ.norm.natAbs = q) (hq4 : q % 4 = 1) (hpq : q ≠ π.norm.natAbs)
    (hχq : quarticChar π q = 1 ∨ quarticChar π q = -1)
    (hχp : quarticChar ρ (π.norm.natAbs : ℤ[i]) = 1 ∨
      quarticChar ρ (π.norm.natAbs : ℤ[i]) = -1) :
    ρ ∣ quarticChar π q * quarticChar ρ (π.norm.natAbs : ℤ[i]) - π ^ ((q - 1) / 2) := by
  haveI := Fact.mk hq
  have hρ := irreducible_of_prime_norm (hNρ ▸ hq)
  have hρ2 : ρ.norm.natAbs ≠ 2 := by omega
  have hρq : ρ ∣ (q : ℤ[i]) := hNρ ▸ dvd_natAbs_norm ρ
  obtain ⟨L, _, _, φ, ψ, hψ, hker⟩ := exists_field_charP hρ hq hρq π.norm.natAbs hpq
  have h2L : (2 : L) ≠ 0 := two_ne_zero_of_charP (by omega)
  have h4 := gaussSum_pow_four_eq_pow_three_mul_star hp2 φ hP h2L hψ
  have hord := orderOf_quarticMulChar_ringHomComp hp2 φ h2L
  have hρπ : ¬ ρ ∣ π := not_dvd_of_prime_norm_ne hp.out hρ (by rw [hNρ]; exact hpq)
  have hρA : ¬ ρ ∣ π ^ 3 * star π := by
    intro h
    rcases hρ.prime.dvd_or_dvd h with h | h
    · exact hρπ (hρ.prime.dvd_of_dvd_pow h)
    · have := norm_dvd_norm h
      rw [natAbs_norm_star, hNρ] at this
      have h' := (Nat.dvd_prime hp.out).1 this
      rcases h' with h' | h'
      · exact hq.one_lt.ne' h'
      · exact hpq h'
  -- `g² = J(χ', χ') g(χ'²)` and `g(χ'²)² = p`
  have hsq1 : ((quarticMulChar π hp2).ringHomComp φ) ^ 2 ≠ 1 := fun h => by
    have := orderOf_dvd_of_pow_eq_one h; rw [hord] at this; omega
  have hquad : (((quarticMulChar π hp2).ringHomComp φ) ^ 2).IsQuadratic := by
    rw [MulChar.isQuadratic_iff_sq_eq_one, ← pow_mul, show 2 * 2 = 4 by rfl, ← hord,
      pow_orderOf_eq_one]
  have hneg : (((quarticMulChar π hp2).ringHomComp φ) ^ 2) (-1) = 1 := by
    rw [MulChar.pow_apply' _ two_ne_zero, ← map_pow, neg_one_sq, map_one]
  have hG := gaussSum_sq hsq1 hquad hψ
  rw [hneg, one_mul, ZMod.card] at hG
  have hJ := jacobiSum_mul_nontrivial (by rwa [← sq]) ψ (χ := (quarticMulChar π hp2).ringHomComp φ)
    (φ := (quarticMulChar π hp2).ringHomComp φ)
  rw [← sq, jacobiSum_ringHomComp, jacobiSum_quarticMulChar_eq hp2 hP] at hJ
  have hfrob := gaussSum_pow_char_of_mod_four_eq_one hp2 q φ (ψ := ψ) hq4 hpq
  have hc : φ (-(quarticMulChar π hp2 (-1)) * π) ^ 2 = φ π ^ 2 := by
    rw [← map_pow, mul_pow, neg_sq, sq (quarticMulChar π hp2 (-1)),
      NTKB.Port.MulChar.apply_neg_one_mul_self, one_mul, map_pow]
  -- abstract the Gauss sums
  generalize gaussSum ((quarticMulChar π hp2).ringHomComp φ) ψ = g at h4 hJ hfrob
  generalize gaussSum (((quarticMulChar π hp2).ringHomComp φ) ^ 2) ψ = G at hG hJ
  have hg0 : g ≠ 0 := by
    intro h; rw [h, zero_pow (by norm_num)] at h4
    exact hρA ((hker _).1 h4.symm)
  obtain ⟨t, ht⟩ : ∃ t, q = 4 * t + 1 := ⟨q / 4, by omega⟩
  have hqexp : qexp ρ = t := by rw [qexp, hNρ, ht]; omega
  have hk : (q - 1) / 2 = 2 * t := by omega
  -- `g ^ q = φ(π) ^ (2t) p ^ t g`
  have hgq : g ^ q = (φ π ^ (2 * t) * (π.norm.natAbs : L) ^ t) * g := by
    have e : g ^ q = (g * g) ^ (2 * t) * g := by rw [← sq, ← pow_mul, ← pow_succ, ht]; ring_nf
    rw [e, ← hJ, mul_pow, pow_mul, pow_mul (φ (-(quarticMulChar π hp2 (-1)) * π)) 2 t, hc, hG,
      ← pow_mul]
    ring
  rw [hgq, ← mul_assoc] at hfrob
  have h1 : φ (quarticChar π q) * (φ π ^ (2 * t) * (π.norm.natAbs : L) ^ t) = 1 :=
    mul_right_cancel₀ hg0 (by rw [hfrob, one_mul])
  -- `p ^ t ≡ χ_ρ(p) (mod ρ)`
  have hρp : ¬ ρ ∣ (π.norm.natAbs : ℤ[i]) := by
    intro h
    have := norm_dvd_norm h
    rw [natAbs_norm_natCast, hNρ] at this
    exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp.out).1 (hq.dvd_of_dvd_pow this))
  obtain ⟨-, hspec⟩ := quarticChar_spec hρ hρ2 hρp
  rw [← hker, map_sub, sub_eq_zero, hqexp, map_pow, map_natCast] at hspec
  rw [hspec] at h1
  rw [hk, ← hker, map_sub, map_mul, map_pow]
  have hsq2 : ∀ x : ℤ[i], (x = 1 ∨ x = -1) → φ x * φ x = 1 := by
    rintro x (rfl | rfl) <;> simp
  have e1 := hsq2 _ hχq
  have e2 := hsq2 _ hχp
  linear_combination (-(φ (quarticChar π q) * φ (quarticChar ρ (π.norm.natAbs : ℤ[i])))) * h1 +
    (φ π ^ (2 * t) * φ (quarticChar ρ (π.norm.natAbs : ℤ[i])) *
      φ (quarticChar ρ (π.norm.natAbs : ℤ[i]))) * e1 + (φ π ^ (2 * t)) * e2

/-- **Proposition 9.10.2.** Let `p ≠ q` be primes `≡ 1 (mod 4)` with `ψ_q(p) = 1`, `π` the primary
irreducible dividing `p` and `λ` an irreducible dividing `q`. Then
`χ_π(q) χ_λ(p) ≡ π ^ ((q - 1) / 2) (mod q)`. -/
@[kb "irelandrosen1990" "Prop 9.10.2, p. 139"]
theorem dvd_quarticChar_mul_quarticChar_sub_pow {π : ℤ[i]} [hp : Fact (Nat.Prime π.norm.natAbs)]
    (hP : IsPrimary π) {μ : ℤ[i]} {q : ℕ} [hqf : Fact q.Prime] (hNμ : μ.norm.natAbs = q)
    (hq4 : q % 4 = 1) (hpq : q ≠ π.norm.natAbs) (hψ : legendreSym q π.norm.natAbs = 1) :
    (q : ℤ[i]) ∣ quarticChar π q * quarticChar μ (π.norm.natAbs : ℤ[i]) - π ^ ((q - 1) / 2) := by
  subst hNμ
  have hq := hqf.out
  have hp4 := hP.2.natAbs_norm_mod_four
  have hp2 : π.norm.natAbs ≠ 2 := by omega
  have hψ' : legendreSym π.norm.natAbs μ.norm.natAbs = 1 := by
    rw [← legendreSym.quadratic_reciprocity_one_mod_four hp4 (by omega)]; exact_mod_cast hψ
  have hχq := quarticChar_eq_one_or_neg_one hp2 (q := μ.norm.natAbs) (by exact_mod_cast hψ')
  have hμ2 : μ.norm.natAbs ≠ 2 := by omega
  have hχp := quarticChar_eq_one_or_neg_one hμ2 (q := π.norm.natAbs) (by exact_mod_cast hψ)
  simp only [Int.cast_natCast] at hχp
  have hNμ : μ.norm.natAbs = μ.norm.natAbs := rfl
  have hNμ' : (star μ).norm.natAbs = μ.norm.natAbs := by rw [natAbs_norm_star]
  have hstar : quarticChar (star μ) (π.norm.natAbs : ℤ[i]) = quarticChar μ (π.norm.natAbs : ℤ[i]) := by
    have := quarticChar_star (irreducible_of_prime_norm hq) hμ2 (π.norm.natAbs : ℤ[i])
    rw [star_natCast] at this
    rw [this]
    rcases hχp with h | h <;> rw [h] <;> simp
  have h1 := dvd_quarticChar_mul_sub_pow hp2 hP hq hNμ hq4 hpq hχq hχp
  have h2 := dvd_quarticChar_mul_sub_pow hp2 hP hq hNμ' hq4 hpq hχq (by rwa [hstar])
  rw [hstar] at h2
  have hqμ : ((μ.norm.natAbs : ℕ) : ℤ[i]) = μ * star μ := by
    rw [← Int.cast_natCast, natAbs_norm, Zsqrtd.norm_eq_mul_conj]
  have := (isCoprime_star_of_prime_norm hq hμ2).mul_dvd h1 h2
  rwa [← hqμ] at this

/-! ### Theorem 3 (Burde) -/

/-- **Theorem 3 of §10 (Burde's rational biquadratic reciprocity law).** Let `p ≠ q` be primes
`≡ 1 (mod 4)` with `ψ_q(p) = 1`, and write `p = a² + b²`, `q = c² + d²` with `a, c` odd. With
`π = a + b i` and `λ = c + d i`, `χ_π(q) χ_λ(p) = (-1) ^ ((q - 1) / 4) ψ_q(ad - bc)`. -/
@[kb "irelandrosen1990" "Ch. 9, §10, Theorem 3 (Burde), p. 139"]
theorem burde {p q : ℕ} (hp : p.Prime) [hqf : Fact q.Prime] (hp4 : p % 4 = 1) (hq4 : q % 4 = 1)
    (hpq : p ≠ q) {a b c d : ℤ} (hab : (p : ℤ) = a ^ 2 + b ^ 2) (hcd : (q : ℤ) = c ^ 2 + d ^ 2)
    (ha : Odd a) (hc : Odd c) (hψ : legendreSym q p = 1) :
    quarticChar (⟨a, b⟩ : ℤ[i]) q * quarticChar (⟨c, d⟩ : ℤ[i]) p =
      (((-1) ^ ((q - 1) / 4) * legendreSym q (a * d - b * c) : ℤ) : ℤ[i]) := by
  have hq := hqf.out
  haveI := Fact.mk hp
  set π : ℤ[i] := ⟨a, b⟩ with hπdef
  have hNπ : π.norm.natAbs = p := by
    have : π.norm = p := by rw [norm_def, hab]
    rw [this]; simp
  have hNμ : (⟨c, d⟩ : ℤ[i]).norm.natAbs = q := by
    have : (⟨c, d⟩ : ℤ[i]).norm = q := by rw [norm_def, hcd]
    rw [this]; simp
  haveI : Fact (Nat.Prime π.norm.natAbs) := ⟨hNπ ▸ hp⟩
  have hp2 : π.norm.natAbs ≠ 2 := by omega
  -- the primary associate `π' = ε π`, `ε = ±1`
  have hb : Even b := by
    rcases Int.even_or_odd b with h | h
    · exact h
    · exfalso
      have hp' : Odd (p : ℤ) := by rw [Int.odd_iff]; omega
      have : Even (p : ℤ) := by rw [hab]; exact (ha.pow).add_odd h.pow
      exact (Int.not_even_iff_odd.2 hp') this
  obtain ⟨ε, hε, hP⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ IsPrimary ((ε : ℤ[i]) * π) := by
    have hu : ¬ IsUnit π := fun h => by
      have := isUnit_iff_natAbs_norm.1 h; rw [hNπ] at this; exact hp.one_lt.ne' this
    obtain ⟨b', rfl⟩ := hb
    have hodd := Int.odd_iff.1 ha
    by_cases h : (a % 4 = 1 ∧ (b' + b') % 4 = 0) ∨ (a % 4 = 3 ∧ (b' + b') % 4 = 2)
    · refine ⟨1, Or.inl rfl, ?_⟩
      rw [Int.cast_one, one_mul, isPrimary_iff]; exact ⟨hu, h⟩
    · refine ⟨-1, Or.inr rfl, ?_⟩
      rw [isPrimary_iff]
      refine ⟨fun h' => hu (by
        rw [Int.cast_neg, Int.cast_one, neg_one_mul] at h'; exact (IsUnit.neg_iff π).1 h'), ?_⟩
      simp only [Int.cast_neg, Int.cast_one, neg_one_mul, Zsqrtd.re_neg, Zsqrtd.im_neg, hπdef]
      omega
  have hassoc : Associated π ((ε : ℤ[i]) * π) := by
    rcases hε with rfl | rfl
    · simp
    · rw [Int.cast_neg, Int.cast_one, neg_one_mul]; exact (Associated.refl π).neg_right
  have hNπ' : ((ε : ℤ[i]) * π).norm.natAbs = p := by
    rw [← natAbs_norm_eq_of_associated hassoc, hNπ]
  haveI : Fact (Nat.Prime ((ε : ℤ[i]) * π).norm.natAbs) := ⟨hNπ' ▸ hp⟩
  -- 9.10.2 and 9.10.3 for `π'`
  have h1 := dvd_quarticChar_mul_quarticChar_sub_pow hP hNμ hq4 (by omega) (by rw [hNπ']; exact hψ)
  rw [hNπ', ← quarticChar_of_associated hassoc] at h1
  have hab' : (p : ℤ) = (ε * a) ^ 2 + (ε * b) ^ 2 := by
    rcases hε with rfl | rfl <;> simp [hab]
  have h2 := pow_modEq_legendreSym_mul (p := p) hq4 hab' hcd hψ
  have hπ' : ((ε : ℤ[i]) * π) = ⟨ε * a, ε * b⟩ := by ext <;> simp [hπdef]
  rw [← hπ'] at h2
  have hneg1 := legendreSym_neg_one_of_mod_four (q := q) hq4
  have hsym : legendreSym q (ε * a * d - ε * b * c) = legendreSym q (a * d - b * c) := by
    rcases hε with rfl | rfl
    · simp
    · rw [show -1 * a * d - -1 * b * c = -1 * (a * d - b * c) by ring, legendreSym.mul, hneg1,
        one_mul]
  rw [hsym] at h2
  -- Lemma 4 with `|c|`
  have hL4 : legendreSym q d = (-1) ^ ((q - 1) / 4) :=
    legendreSym_eq_neg_one_pow hq4 (c := |c|) (by rw [sq_abs]; exact hcd)
      (abs_pos.2 (by rintro rfl; simp at hc)) (by rw [← Int.natCast_natAbs, Int.odd_coe_nat, Int.natAbs_odd]; exact hc)
  rw [hL4] at h2
  have h3 := dvd_add h1 h2
  rw [show quarticChar π q * quarticChar ⟨c, d⟩ p - ((ε : ℤ[i]) * π) ^ ((q - 1) / 2) +
      (((ε : ℤ[i]) * π) ^ ((q - 1) / 2) - (((-1) ^ ((q - 1) / 4) * legendreSym q (a * d - b * c) :
        ℤ) : ℤ[i])) = quarticChar π q * quarticChar ⟨c, d⟩ p -
        (((-1) ^ ((q - 1) / 4) * legendreSym q (a * d - b * c) : ℤ) : ℤ[i]) by ring] at h3
  -- both sides are `±1`
  have hψp : legendreSym p q = 1 := by
    rw [← legendreSym.quadratic_reciprocity_one_mod_four hp4 (by omega)]; exact hψ
  have hχq := quarticChar_eq_one_or_neg_one' hNπ (by omega) (q := q) (by exact_mod_cast hψp)
  have hχp := quarticChar_eq_one_or_neg_one' hNμ (by omega) (q := p) (by exact_mod_cast hψ)
  simp only [Int.cast_natCast] at hχq hχp
  have hlhs : ∃ z : ℤ, (z = 1 ∨ z = -1) ∧ quarticChar π q * quarticChar ⟨c, d⟩ p = (z : ℤ[i]) := by
    rcases hχq with h | h <;> rcases hχp with h' | h' <;> rw [h, h']
    · exact ⟨1, Or.inl rfl, by simp⟩
    · exact ⟨-1, Or.inr rfl, by simp⟩
    · exact ⟨-1, Or.inr rfl, by simp⟩
    · exact ⟨1, Or.inl rfl, by simp⟩
  obtain ⟨z, hz, hzeq⟩ := hlhs
  rw [hzeq, ← Int.cast_sub, ← Int.cast_natCast, Zsqrtd.intCast_dvd_intCast] at h3
  rw [hzeq]
  congr 1
  have hs1 : ((-1 : ℤ) ^ ((q - 1) / 4) = 1 ∨ (-1 : ℤ) ^ ((q - 1) / 4) = -1) := by
    rcases Nat.even_or_odd ((q - 1) / 4) with h | h
    · left; exact h.neg_one_pow
    · right; exact h.neg_one_pow
  have hw : legendreSym q (a * d - b * c) = 1 ∨ legendreSym q (a * d - b * c) = -1 := by
    by_cases h0 : ((a * d - b * c : ℤ) : ZMod q) = 0
    · exfalso
      rw [(legendreSym.eq_zero_iff q _).2 h0, mul_zero, sub_zero] at h3
      have h1 : (q : ℤ) ∣ 1 := by rcases hz with rfl | rfl; exacts [h3, (dvd_neg).1 h3]
      have := Int.eq_one_of_dvd_one (by positivity) h1
      have : q = 1 := by exact_mod_cast this
      exact hq.one_lt.ne' this
    · exact legendreSym.eq_one_or_neg_one q h0
  refine eq_of_dvd_sub_of_sq_eq_one hq (by omega) hz ?_ h3
  rcases hs1 with h | h <;> rcases hw with h' | h' <;> rw [h, h'] <;> norm_num

end Gaussian

end NTKB.IrelandRosen
