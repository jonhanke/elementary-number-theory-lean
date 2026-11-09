/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.QuadraticFields.CubeDescent

/-!
# Fermat's equation for cubes in `k(ρ)` and `x³ + y³ = 3z³` (Hardy–Wright §§ 13.4–13.6)

`K` is a number field with `IsCyclotomicExtension {3} ℚ K` (the field `k(ρ)`), `λ = η - 1` the prime
above `3` (the book's `λ = 1 - ρ`, up to sign).

* Theorem 229 (`lambda_dvd_of_cube_add_cube_add_cube`): if `ξ³ + η³ + ζ³ = 0` then `λ` divides one
  of `ξ, η, ζ`.
* Theorem 227 (`cube_add_cube_add_cube_ne_zero`): `ξ³ + η³ + ζ³ = 0` has no solution in non-zero
  integers of `k(ρ)`; in particular (`int_cube_add_cube_ne_cube`) `x³ + y³ = z³` has no solution in
  non-zero rational integers.
* Theorem 232 (`eq_zero_of_cube_add_cube_eq_three_mul_cube`): `x³ + y³ = 3z³` only for `z = 0`.
* Theorem 233 (`exists_pos_not_sum_two_rat_cubes`): `3` is not a sum of two rational cubes.

Theorems 228, 230 and 231 are `CubeDescent.cube_congr` (Mathlib's
`lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd`), `CubeDescent.not_sol_of_le_three`
and `CubeDescent.sol_descent`.
-/

namespace NTKB.HardyWright

open NumberField IsCyclotomicExtension.Rat.Three CubeDescent

section field

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]
  {ζ : K} (hζ : IsPrimitiveRoot ζ 3)

local notation3 "η" => (IsPrimitiveRoot.isUnit (hζ.toInteger_isPrimitiveRoot) (by decide)).unit
local notation3 "λ" => hζ.toInteger - 1

include hζ in
lemma lambda_pow_four_not_dvd_one : ¬ λ ^ 4 ∣ (1 : 𝓞 K) := fun h ↦
  lambda_not_dvd_one (hζ := hζ) (dvd_trans (dvd_pow_self _ (by decide)) h)

include hζ in
lemma lambda_pow_four_not_dvd_three : ¬ λ ^ 4 ∣ (3 : 𝓞 K) := by
  intro h
  have hp := lambda_prime (hζ := hζ)
  rw [three_eq (hζ := hζ), show (4 : ℕ) = 2 + 2 by rfl, pow_add,
    mul_dvd_mul_iff_right (pow_ne_zero 2 hp.ne_zero), dvd_neg] at h
  exact hp.not_isUnit (isUnit_of_dvd_unit (dvd_trans (dvd_pow_self _ (by decide)) h)
    ((Units.isUnit η).pow 2))

/-- **Theorem 229.** If `ξ³ + η³ + ζ³ = 0` in integers of `k(ρ)`, then one of `ξ, η, ζ` is divisible
by `λ`. -/
@[kb "hardywright2008" "Thm 229, p. 269"]
theorem lambda_dvd_of_cube_add_cube_add_cube {a b c : 𝓞 K} (h : a ^ 3 + b ^ 3 + c ^ 3 = 0) :
    λ ∣ a ∨ λ ∣ b ∨ λ ∣ c := by
  by_contra! hn
  obtain ⟨ha, hb, hc⟩ := hn
  have sgn : ∀ {x : 𝓞 K}, ¬ λ ∣ x → ∃ s : 𝓞 K, (s = 1 ∨ s = -1) ∧ λ ^ 4 ∣ x ^ 3 - s := by
    intro x hx
    rcases cube_congr (hζ := hζ) hx with h | h
    · exact ⟨1, Or.inl rfl, h⟩
    · exact ⟨-1, Or.inr rfl, by rwa [sub_neg_eq_add]⟩
  obtain ⟨s, hs, hsa⟩ := sgn ha
  obtain ⟨t, ht, htb⟩ := sgn hb
  obtain ⟨r, hr, hrc⟩ := sgn hc
  have hsum : λ ^ 4 ∣ s + t + r := by
    have := dvd_add (dvd_add hsa htb) hrc
    rw [show a ^ 3 - s + (b ^ 3 - t) + (c ^ 3 - r) = (a ^ 3 + b ^ 3 + c ^ 3) - (s + t + r) by ring,
      h, zero_sub, dvd_neg] at this
    exact this
  have h1 := lambda_pow_four_not_dvd_one hζ
  have h3 := lambda_pow_four_not_dvd_three hζ
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> rcases hr with rfl | rfl <;>
    norm_num at hsum
  · exact h3 hsum
  · exact h1 hsum
  · exact h1 hsum
  · exact h1 (by simpa using hsum)
  · exact h1 hsum
  · exact h1 (by simpa using hsum)
  · exact h1 (by simpa using hsum)
  · exact h3 (by simpa using hsum)

omit [NumberField K] [IsCyclotomicExtension {3} ℚ K] in
/-- If `a, b` are coprime and `a³ + b³ + c³ = 0`, then `a, c` are coprime. -/
lemma isCoprime_of_cube_sum {a b c : 𝓞 K} (hab : IsCoprime a b) (h : a ^ 3 + b ^ 3 + c ^ 3 = 0) :
    IsCoprime a c := by
  have h1 : IsCoprime a (b ^ 3) := hab.pow_right
  rw [show b ^ 3 = -c ^ 3 + a * (-a ^ 2) by linear_combination h,
    IsCoprime.add_mul_left_right_iff, IsCoprime.neg_right_iff] at h1
  exact IsCoprime.of_isCoprime_of_dvd_right h1 (dvd_pow_self c (by decide))

/-- The case `λ ∤ a b`, `a, b` coprime, `c ≠ 0` of Theorem 227: here `λ ∣ c` by Theorem 229 and the
equation is `(13.4.2)`, excluded by the descent. -/
lemma cube_add_cube_add_cube_ne_zero_aux {a b c : 𝓞 K} (hab : IsCoprime a b) (ha : ¬ λ ∣ a)
    (hb : ¬ λ ∣ b) (hc0 : c ≠ 0) (h : a ^ 3 + b ^ 3 + c ^ 3 = 0) : False := by
  have hp := lambda_prime (hζ := hζ)
  have hc : λ ∣ c := by
    rcases lambda_dvd_of_cube_add_cube_add_cube hζ h with h' | h' | h'
    · exact absurd h' ha
    · exact absurd h' hb
    · exact h'
  obtain ⟨n, γ, hγ, rfl⟩ := WfDvdMonoid.max_power_factor hc0 hp.irreducible
  have hn : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_mul] at hc
    exact hγ hc
  exact not_sol (hζ := hζ) (3 * n) (by omega) (by omega)
    { a := a, b := b, w := γ, u := -1, ha := ha, hb := hb, hw := hγ, coprime := hab
      H := by push_cast; linear_combination h }

/-- **Theorem 227.** There are no solutions of `ξ³ + η³ + ζ³ = 0` in non-zero integers of `k(ρ)`. -/
@[kb "hardywright2008" "Thm 227, p. 268"]
theorem cube_add_cube_add_cube_ne_zero {a b c : 𝓞 K} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    a ^ 3 + b ^ 3 + c ^ 3 ≠ 0 := by
  classical
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  let _ : IsPrincipalIdealRing (𝓞 K) := IsCyclotomicExtension.Rat.three_pid K
  let _ : GCDMonoid (𝓞 K) := UniqueFactorizationMonoid.toGCDMonoid _
  intro h
  -- reduce to `(a, b) = 1` (13.4.1)
  obtain ⟨a', b', ha', hb', hu⟩ := extract_gcd a b
  set d := gcd a b
  have hd : d ≠ 0 := fun h0 ↦ ha (by rw [ha', h0, zero_mul])
  have hdc : d ∣ c := by
    refine (IsIntegrallyClosed.pow_dvd_pow_iff (R := 𝓞 K) (n := 3) (by decide)).1 ?_
    exact ⟨-(a' ^ 3 + b' ^ 3), by rw [ha', hb'] at h; linear_combination h⟩
  obtain ⟨c', rfl⟩ := hdc
  have h' : a' ^ 3 + b' ^ 3 + c' ^ 3 = 0 := by
    rw [ha', hb'] at h
    apply mul_left_cancel₀ (pow_ne_zero 3 hd)
    linear_combination h
  have hcop : IsCoprime a' b' := (gcd_isUnit_iff a' b').1 hu
  have ha0 : a' ≠ 0 := fun h0 ↦ ha (by rw [ha', h0, mul_zero])
  have hb0 : b' ≠ 0 := fun h0 ↦ hb (by rw [hb', h0, mul_zero])
  have hc0 : c' ≠ 0 := fun h0 ↦ hc (by rw [h0, mul_zero])
  have hac : IsCoprime a' c' := isCoprime_of_cube_sum hcop h'
  have hbc : IsCoprime b' c' :=
    isCoprime_of_cube_sum hcop.symm (by linear_combination h')
  have hp := lambda_prime (hζ := hζ)
  have nd : ∀ {x y : 𝓞 K}, IsCoprime x y → hζ.toInteger - 1 ∣ x → ¬ hζ.toInteger - 1 ∣ y :=
    fun hxy hx hy ↦
    hp.not_isUnit (hxy.isUnit_of_dvd' hx hy)
  rcases lambda_dvd_of_cube_add_cube_add_cube hζ h' with h1 | h1 | h1
  · exact cube_add_cube_add_cube_ne_zero_aux hζ hbc (nd hcop h1) (nd hac h1) ha0
      (by linear_combination h')
  · exact cube_add_cube_add_cube_ne_zero_aux hζ hac.symm (nd hbc h1) (nd hcop.symm h1) hb0
      (by linear_combination h')
  · exact cube_add_cube_add_cube_ne_zero_aux hζ hcop (nd hac.symm h1) (nd hbc.symm h1) hc0 h'

include hζ in
/-- The coprime case of Theorem 232, in `k(ρ)`: `x³ + y³ = 3 · 3^(3j) z'³ = ε λ^(6j+2) z'³`. -/
lemma cube_add_cube_eq_three_mul_cube_aux {x y z : ℤ} (hcop : IsCoprime x y) (h3x : ¬ (3 : ℤ) ∣ x)
    (h3y : ¬ (3 : ℤ) ∣ y) (hz : z ≠ 0) (h : x ^ 3 + y ^ 3 = 3 * z ^ 3) : False := by
  obtain ⟨j, z', hz', rfl⟩ := WfDvdMonoid.max_power_factor hz Int.prime_three.irreducible
  have hl : ∀ m : ℤ, λ ∣ (m : 𝓞 K) ↔ (3 : ℤ) ∣ m := lambda_dvd_intCast_iff (hζ := hζ)
  refine not_sol (hζ := hζ) (6 * j + 2) (by omega) (by omega)
    { a := x, b := y, w := z', u := (-(η ^ 2)) ^ (3 * j + 1)
      ha := fun h ↦ h3x ((hl x).1 h)
      hb := fun h ↦ h3y ((hl y).1 h)
      hw := fun h ↦ hz' ((hl z').1 h)
      coprime := hcop.intCast
      H := ?_ }
  have h' : ((x : 𝓞 K)) ^ 3 + (y : 𝓞 K) ^ 3 = 3 * ((3 : 𝓞 K) ^ j * z') ^ 3 := by
    exact_mod_cast h
  rw [h', mul_pow, ← pow_mul, ← mul_assoc, ← pow_succ', three_eq (hζ := hζ)]
  push_cast
  rw [mul_pow, ← pow_mul, show 2 * (j * 3 + 1) = 6 * j + 2 by ring]
  ring

end field

set_option backward.isDefEq.respectTransparency false in
/-- `CyclotomicField 3 ℚ` is a model of `k(ρ)`. -/
lemma cyclotomicField_three_facts :
    NumberField (CyclotomicField 3 ℚ) ∧ IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
  ⟨IsCyclotomicExtension.numberField {3} ℚ _, inferInstance⟩

/-- The rational case of Theorem 227 (Fermat's theorem for cubes), deduced from the statement in
`k(ρ)`. -/
@[kb "hardywright2008" "Thm 227, p. 268"]
theorem int_cube_add_cube_ne_cube {x y z : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    x ^ 3 + y ^ 3 ≠ z ^ 3 := by
  let K := CyclotomicField 3 ℚ
  obtain ⟨_, _⟩ := cyclotomicField_three_facts
  intro h
  refine cube_add_cube_add_cube_ne_zero (K := K) (a := (x : 𝓞 K)) (b := (y : 𝓞 K)) (c := ((-z : ℤ) : 𝓞 K))
    (by exact_mod_cast hx) (by exact_mod_cast hy) (by simpa using hz) ?_
  have : ((x ^ 3 + y ^ 3 + (-z) ^ 3 : ℤ) : 𝓞 K) = 0 := by
    rw [show x ^ 3 + y ^ 3 + (-z) ^ 3 = 0 by linear_combination h]; simp
  exact_mod_cast this

/-- In `x³ + y³ = 3z³` a common prime factor of `x` and `y` divides `z`. -/
lemma prime_dvd_of_cube_add_cube_eq_three_mul_cube {x y z p : ℤ} (hp : Prime p)
    (h : x ^ 3 + y ^ 3 = 3 * z ^ 3) (hx : p ∣ x) (hy : p ∣ y) : p ∣ z := by
  by_contra hz
  have h2 : p ^ 2 ∣ 3 * z ^ 3 := by
    rw [← h]
    exact dvd_add (dvd_trans (pow_dvd_pow_of_dvd hx 2) (pow_dvd_pow _ (by decide)))
      (dvd_trans (pow_dvd_pow_of_dvd hy 2) (pow_dvd_pow _ (by decide)))
  have hcop : IsCoprime (p ^ 2) (z ^ 3) :=
    IsCoprime.pow ((Prime.coprime_iff_not_dvd hp).2 hz)
  have h3 : p ^ 2 ∣ 3 := hcop.dvd_of_dvd_mul_right h2
  have hp2 : 2 ≤ |p| := by
    have := Int.prime_iff_natAbs_prime.1 hp |>.two_le
    rw [Int.abs_eq_natAbs]
    exact_mod_cast this
  have := Int.le_of_dvd (by norm_num) h3
  have h4 : |p| ^ 2 ≤ 3 := by rw [sq_abs]; exact this
  nlinarith

/-- **Theorem 232.** The equation `x³ + y³ = 3z³` has no solutions in integers except the trivial
ones with `z = 0`. -/
@[kb "hardywright2008" "Thm 232, p. 272"]
theorem eq_zero_of_cube_add_cube_eq_three_mul_cube {x y z : ℤ} (h : x ^ 3 + y ^ 3 = 3 * z ^ 3) :
    z = 0 := by
  -- reduction to `(x, y) = 1` by induction on `|z|`
  induction hn : z.natAbs using Nat.strong_induction_on generalizing x y z with
  | _ n ih =>
  by_contra hz
  by_cases hg : Int.gcd x y = 1
  · -- the coprime case, in `k(ρ)`
    obtain ⟨_, _⟩ := cyclotomicField_three_facts
    have hcop : IsCoprime x y := Int.isCoprime_iff_gcd_eq_one.2 hg
    have h3x : ¬ (3 : ℤ) ∣ x := by
      intro h3
      obtain ⟨k, rfl⟩ := h3
      have : (3 : ℤ) ∣ y ^ 3 := ⟨z ^ 3 - 9 * k ^ 3, by linear_combination h⟩
      exact Int.prime_three.not_isUnit
        (hcop.isUnit_of_dvd' (dvd_mul_right _ _) (Int.prime_three.dvd_of_dvd_pow this))
    have h3y : ¬ (3 : ℤ) ∣ y := by
      intro h3
      obtain ⟨k, rfl⟩ := h3
      have : (3 : ℤ) ∣ x ^ 3 := ⟨z ^ 3 - 9 * k ^ 3, by linear_combination h⟩
      exact Int.prime_three.not_isUnit
        (hcop.isUnit_of_dvd' (Int.prime_three.dvd_of_dvd_pow this) (dvd_mul_right _ _))
    exact cube_add_cube_eq_three_mul_cube_aux
      (IsCyclotomicExtension.zeta_spec 3 ℚ (CyclotomicField 3 ℚ)) hcop h3x h3y hz h
  · -- a common prime factor `p` of `x, y` divides `z`; divide by it
    have hg0 : Int.gcd x y ≠ 0 := by
      intro h0
      rw [Int.gcd_eq_zero_iff] at h0
      obtain ⟨rfl, rfl⟩ := h0
      apply hz
      have : z ^ 3 = 0 := by linarith
      exact pow_eq_zero_iff (by decide) |>.1 this
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg
    have hpx : (p : ℤ) ∣ x := Int.natCast_dvd.2 (dvd_trans hpg (Int.gcd_dvd_left _ _ |> fun h ↦
      Int.natCast_dvd.1 h))
    have hpy : (p : ℤ) ∣ y := Int.natCast_dvd.2 (dvd_trans hpg (Int.gcd_dvd_right _ _ |> fun h ↦
      Int.natCast_dvd.1 h))
    have hpz := prime_dvd_of_cube_add_cube_eq_three_mul_cube (Nat.prime_iff_prime_int.1 hp) h
      hpx hpy
    obtain ⟨x', rfl⟩ := hpx
    obtain ⟨y', rfl⟩ := hpy
    obtain ⟨z', rfl⟩ := hpz
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have h' : x' ^ 3 + y' ^ 3 = 3 * z' ^ 3 := by
      apply mul_left_cancel₀ (pow_ne_zero 3 hp0)
      linear_combination h
    have hz' : z' ≠ 0 := fun h0 ↦ hz (by rw [h0, mul_zero])
    refine hz' (ih z'.natAbs ?_ h' rfl)
    rw [← hn, Int.natAbs_mul]
    have : 1 < (p : ℤ).natAbs := by simpa using hp.one_lt
    have : 0 < z'.natAbs := Int.natAbs_pos.2 hz'
    nlinarith

/-- `3` is not the sum of two rational cubes. -/
theorem rat_cube_add_cube_ne_three (x y : ℚ) : x ^ 3 + y ^ 3 ≠ 3 := by
  intro h
  have hb : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
  have hd : (y.den : ℚ) ≠ 0 := by exact_mod_cast y.den_ne_zero
  have key : (x.num * y.den) ^ 3 + (y.num * x.den) ^ 3 = 3 * ((x.den : ℤ) * y.den) ^ 3 := by
    have e1 := Rat.num_div_den x
    have e2 := Rat.num_div_den y
    rw [← e1, ← e2] at h
    field_simp at h
    exact_mod_cast (by linear_combination h :
      ((x.num : ℚ) * y.den) ^ 3 + ((y.num : ℚ) * x.den) ^ 3 = 3 * ((x.den : ℚ) * y.den) ^ 3)
  have := eq_zero_of_cube_add_cube_eq_three_mul_cube key
  have h0 : ((x.den : ℤ) * y.den : ℤ) ≠ 0 := by positivity
  exact h0 this

/-- **Theorem 233.** There are positive rationals (for example `3`) which are not sums of two
non-negative rational cubes. -/
@[kb "hardywright2008" "Thm 233, p. 274"]
theorem exists_pos_not_sum_two_rat_cubes :
    ∃ r : ℚ, 0 < r ∧ ¬ ∃ x y : ℚ, 0 ≤ x ∧ 0 ≤ y ∧ x ^ 3 + y ^ 3 = r :=
  ⟨3, by norm_num, fun ⟨x, y, _, _, h⟩ ↦ rat_cube_add_cube_ne_three x y h⟩

end NTKB.HardyWright
