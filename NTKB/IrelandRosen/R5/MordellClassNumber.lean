/-
Ireland–Rosen, Chapter 17, §10, Proposition 17.10.2: integral points on `y² = x³ - d` and the
class number of `ℚ(√-d)`.
-/
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import NTKB.Attr
import NTKB.IrelandRosen.R5.QuadraticFields

/-!
# `y² = x³ - d` and the class number of `ℚ(√-d)` (Ireland–Rosen, Proposition 17.10.2)

Let `d > 1` be squarefree with `d ≡ 1, 2 (mod 4)` and suppose `3` does not divide the class number
of `K = ℚ(√-d)`. Then `y² = x³ - d` has a solution in integers iff `d = 3t² ± 1` for an integer `t`.

The proof is the book's: the ring of integers of `K` is `ℤ[√-d]` (Proposition 13.1.1), in which
`x³ = (y + √-d)(y - √-d)` with coprime factors (`x` is odd and prime to `d`); the ideal
`(y + √-d)` is the cube of an ideal, principal because `3 ∤ h`; the units are `±1`, so
`y + √-d = (m + n√-d)³`, and comparing the coefficients of `√-d` gives `1 = n(3m² - dn²)`.
Conversely `(4t² ± 1, ∓(8t³ ± 3t))` are solutions.

The ring of integers of `ℚ(√-d)` (Ireland–Rosen, Proposition 13.1.1) is proved in the library
(`NTKB.IrelandRosen.isIntegral_iff_of_mod_four_ne_one`); the main proof takes it as the hypothesis
`IntegersOfImagQuad d` (that statement for `-d`), proved by `integersOfImagQuad`.
-/

namespace NTKB.IrelandRosen.CM

open QuadraticAlgebra NumberField

/-- `ℚ(√-d)` as `QuadraticAlgebra ℚ (-d) 0` (`ω = √-d`). -/
abbrev ImagQuad (d : ℤ) := QuadraticAlgebra ℚ ((-d : ℤ) : ℚ) 0

lemma not_isSquare_neg {d : ℤ} (hd : 0 < d) : ¬ IsSquare ((-d : ℤ) : ℚ) := by
  rintro ⟨r, hr⟩
  have h1 : ((-d : ℤ) : ℚ) < 0 := by push_cast; exact_mod_cast neg_neg_of_pos hd
  nlinarith [mul_self_nonneg r]

instance factNotIsSquareImagQuad (d : ℤ) [hd : Fact (1 < d)] :
    Fact (¬ IsSquare ((-d : ℤ) : ℚ)) :=
  ⟨not_isSquare_neg (by have := hd.out; omega)⟩

instance (d : ℤ) [Fact (1 < d)] : NumberField (ImagQuad d) where
  to_charZero := inferInstance
  to_finiteDimensional := inferInstance

/-- **Ireland–Rosen, Proposition 13.1.1 for `ℚ(√-d)`, `-d ≡ 2, 3 (mod 4)`**: the integers of
`ℚ(√-d)` are `ℤ[√-d]`. Proved by `integersOfImagQuad` (`NTKB.IrelandRosen.isIntegral_iff_of_mod_four_ne_one`
with `d := -d`). -/
structure IntegersOfImagQuad (d : ℤ) : Prop where
  isIntegral_iff (z : ImagQuad d) :
    IsIntegral ℤ z ↔ ∃ m n : ℤ, z = (m : ImagQuad d) + (n : ImagQuad d) * ω

/-! ### Elementary facts about a solution -/

lemma intCast_zmod_four_of_emod {d : ℤ} {r : ℕ} (h : d % 4 = r) : (d : ZMod 4) = r := by
  have h' : d % ((4 : ℕ) : ℤ) = r := by exact_mod_cast h
  rw [← ZMod.intCast_mod, h']; push_cast; rfl

/-- `x` is odd. -/
lemma odd_of_sq_eq_cube_sub {d x y : ℤ} (h4 : d % 4 = 1 ∨ d % 4 = 2) (h : y ^ 2 = x ^ 3 - d) :
    Odd x := by
  by_contra hx
  rw [Int.not_odd_iff_even] at hx
  obtain ⟨k, rfl⟩ := hx
  have key : ∀ a b c : ZMod 4, (c = 1 ∨ c = 2) → a ^ 2 ≠ (b + b) ^ 3 - c := by decide
  have hc : (d : ZMod 4) = 1 ∨ (d : ZMod 4) = 2 := by
    rcases h4 with h4 | h4
    · left; exact intCast_zmod_four_of_emod (r := 1) h4
    · right; exact intCast_zmod_four_of_emod (r := 2) h4
  apply key y k d hc
  exact_mod_cast congrArg (Int.cast : ℤ → ZMod 4) h

/-- `x` is prime to `d` (`d` squarefree). -/
lemma isCoprime_of_sq_eq_cube_sub {d x y : ℤ} (hsq : Squarefree d) (h : y ^ 2 = x ^ 3 - d) :
    IsCoprime x d := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨ℓ, hℓ, hdvd⟩ := Nat.exists_prime_and_dvd hne
  have hℓZ : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.1 hℓ
  have hx : (ℓ : ℤ) ∣ x := (Int.natCast_dvd_natCast.2 hdvd).trans (Int.gcd_dvd_left x d)
  have hd : (ℓ : ℤ) ∣ d := (Int.natCast_dvd_natCast.2 hdvd).trans (Int.gcd_dvd_right x d)
  have hy2 : (ℓ : ℤ) ∣ y ^ 2 := by rw [h]; exact dvd_sub (dvd_pow hx (by norm_num)) hd
  have hy := hℓZ.dvd_of_dvd_pow hy2
  have hdd : (ℓ : ℤ) * ℓ ∣ d := by
    have he : d = x ^ 3 - y ^ 2 := by linarith
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact he ▸ ⟨ℓ * a ^ 3 - b ^ 2, by ring⟩
  exact hℓZ.not_isUnit (hsq _ hdd)

/-! ### The ring of integers of `ℚ(√-d)` -/

section Integers

variable {d : ℤ} [Fact (1 < d)]

lemma norm_mk_int (m n : ℤ) :
    QuadraticAlgebra.norm ((m : ImagQuad d) + (n : ImagQuad d) * (ω : ImagQuad d)) =
      (m ^ 2 + d * n ^ 2 : ℤ) := by
  rw [norm_def]
  simp only [re_add, im_add, re_intCast, im_intCast, re_mul, im_mul, re_omega, im_omega]
  push_cast
  ring

/-- The units of `ℤ[√-d]`, `d > 1`, are `±1`. -/
lemma units_eq_one_or_neg_one (hA3 : IntegersOfImagQuad d) (u : (𝓞 (ImagQuad d))ˣ) :
    (u : 𝓞 (ImagQuad d)) = 1 ∨ (u : 𝓞 (ImagQuad d)) = -1 := by
  have hd1 : 1 < d := Fact.out
  obtain ⟨m, n, hmn⟩ := (hA3.isIntegral_iff ((u : 𝓞 (ImagQuad d)) : ImagQuad d)).1
    (u : 𝓞 (ImagQuad d)).2
  obtain ⟨m', n', hmn'⟩ := (hA3.isIntegral_iff (((u⁻¹ : (𝓞 (ImagQuad d))ˣ) : 𝓞 (ImagQuad d)) :
    ImagQuad d)).1 (u⁻¹ : (𝓞 (ImagQuad d))ˣ).1.2
  have h1 : ((u : 𝓞 (ImagQuad d)) : ImagQuad d) *
      (((u⁻¹ : (𝓞 (ImagQuad d))ˣ) : 𝓞 (ImagQuad d)) : ImagQuad d) = 1 := by
    have := congrArg (algebraMap (𝓞 (ImagQuad d)) (ImagQuad d)) (Units.mul_inv u)
    rwa [map_mul, map_one] at this
  have hN := congrArg QuadraticAlgebra.norm h1
  rw [map_mul, hmn, hmn', norm_mk_int, norm_mk_int, map_one] at hN
  have hN' : (m ^ 2 + d * n ^ 2) * (m' ^ 2 + d * n' ^ 2) = 1 := by exact_mod_cast hN
  have hpos : 0 ≤ m ^ 2 + d * n ^ 2 := by positivity
  have hpos' : 0 ≤ m' ^ 2 + d * n' ^ 2 := by positivity
  have he : m ^ 2 + d * n ^ 2 = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hN' with h | h
    · exact h
    · omega
  have hn : n = 0 := by
    by_contra hn
    have h' : 0 < n ^ 2 := lt_of_le_of_ne (sq_nonneg n) (Ne.symm (pow_ne_zero 2 hn))
    nlinarith [sq_nonneg m]
  subst hn
  have hm : m = 1 ∨ m = -1 := by
    have : (m - 1) * (m + 1) = 0 := by linear_combination he
    rcases mul_eq_zero.1 this with h | h
    · left; linarith
    · right; linarith
  rcases hm with rfl | rfl
  · left; apply RingOfIntegers.ext; rw [hmn, Int.cast_zero, zero_mul, add_zero, Int.cast_one]; rfl
  · right; apply RingOfIntegers.ext
    rw [hmn, Int.cast_zero, zero_mul, add_zero, Int.cast_neg, Int.cast_one]; rfl

/-- `y + √-d` is a cube in `𝓞 K`: the factors `y ± √-d` of `x³` are coprime, and the ideal
`(y + √-d)`, a cube, is principal since `3 ∤ h`. -/
theorem exists_cube_of_sq_eq_cube_sub (hsq : Squarefree d) (h4 : d % 4 = 1 ∨ d % 4 = 2)
    (hA3 : IntegersOfImagQuad d) (h3 : ¬ 3 ∣ classNumber (ImagQuad d)) {x y : ℤ}
    (h : y ^ 2 = x ^ 3 - d) (s : 𝓞 (ImagQuad d)) (hs : (s : ImagQuad d) = ω) :
    ∃ γ : 𝓞 (ImagQuad d), (y : 𝓞 (ImagQuad d)) + s = γ ^ 3 := by
  have hs2 : s * s = -(d : (𝓞 (ImagQuad d))) := by
    have h0 : (s : ImagQuad d) * s = ((-d : ℤ) : ImagQuad d) := by
      rw [hs, omega_mul_omega_eq_mk]; ext <;> simp
    apply RingOfIntegers.ext
    rw [RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.coe_eq_algebraMap, map_mul, map_neg,
      map_intCast, ← RingOfIntegers.coe_eq_algebraMap, h0, Int.cast_neg]
  have hab : ((y : (𝓞 (ImagQuad d))) + s) * ((y : (𝓞 (ImagQuad d))) - s) = (x : (𝓞 (ImagQuad d))) ^ 3 := by
    have hc := congrArg (Int.cast : ℤ → (𝓞 (ImagQuad d))) h
    push_cast at hc
    linear_combination hc - hs2
  -- the two factors are coprime
  have hcop : IsCoprime ((y : (𝓞 (ImagQuad d))) + s) ((y : (𝓞 (ImagQuad d))) - s) := by
    have hx2 : IsCoprime x 2 := by
      obtain ⟨k, rfl⟩ := odd_of_sq_eq_cube_sub h4 h
      exact ⟨1, -k, by ring⟩
    have hxd := isCoprime_of_sq_eq_cube_sub hsq h
    obtain ⟨u, v, huv⟩ := (hx2.mul_right hxd).pow_left (m := 3)
    refine ⟨(u : (𝓞 (ImagQuad d))) * ((y : (𝓞 (ImagQuad d))) - s) - (v : (𝓞 (ImagQuad d))) * s, (v : (𝓞 (ImagQuad d))) * s, ?_⟩
    have hc := congrArg (Int.cast : ℤ → (𝓞 (ImagQuad d))) huv
    push_cast at hc
    linear_combination hc + (u : (𝓞 (ImagQuad d))) * hab - 2 * (v : (𝓞 (ImagQuad d))) * hs2
  -- the ideal `(y + √-d)` is a cube
  obtain ⟨I, hI⟩ : ∃ I : Ideal (𝓞 (ImagQuad d)), Ideal.span {(y : (𝓞 (ImagQuad d))) + s} = I ^ 3 := by
    refine exists_eq_pow_of_mul_eq_pow (b := Ideal.span {(y : (𝓞 (ImagQuad d))) - s})
      (c := Ideal.span {(x : (𝓞 (ImagQuad d)))}) ?_ ?_
    · rw [Ideal.gcd_eq_sup, Ideal.isUnit_iff, ← Ideal.isCoprime_iff_sup_eq,
        Ideal.isCoprime_span_singleton_iff]
      exact hcop
    · rw [Ideal.span_singleton_mul_span_singleton, hab, Ideal.span_singleton_pow]
  -- principal, since `3 ∤ h`
  have hcop3 : Nat.Coprime 3 (Fintype.card (ClassGroup (𝓞 (ImagQuad d)))) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
  have hprin : I.IsPrincipal :=
    Ideal.IsPrincipal.of_isPrincipal_pow_of_coprime hcop3 (hI ▸ ⟨⟨_, rfl⟩⟩)
  obtain ⟨β, hβ⟩ := hprin
  rw [hβ, Ideal.submodule_span_eq, Ideal.span_singleton_pow,
    Ideal.span_singleton_eq_span_singleton] at hI
  obtain ⟨u, hu⟩ := hI.symm
  rcases units_eq_one_or_neg_one hA3 u with h1 | h1
  · exact ⟨β, by rw [← hu, h1, mul_one]⟩
  · exact ⟨-β, by rw [← hu, h1]; ring⟩

/-- **Ireland–Rosen, Proposition 17.10.2, the direct implication.** -/
theorem exists_eq_of_sq_eq_cube_sub (hsq : Squarefree d) (h4 : d % 4 = 1 ∨ d % 4 = 2)
    (hA3 : IntegersOfImagQuad d) (h3 : ¬ 3 ∣ classNumber (ImagQuad d)) {x y : ℤ}
    (h : y ^ 2 = x ^ 3 - d) : ∃ t : ℤ, d = 3 * t ^ 2 + 1 ∨ d = 3 * t ^ 2 - 1 := by
  have hω : IsIntegral ℤ (ω : ImagQuad d) := (hA3.isIntegral_iff ω).2
    ⟨0, 1, by simp only [Int.cast_zero, Int.cast_one, zero_add, one_mul]⟩
  obtain ⟨γ, hγ⟩ := exists_cube_of_sq_eq_cube_sub hsq h4 hA3 h3 h ⟨ω, hω⟩ rfl
  obtain ⟨m, n, hmn⟩ := (hA3.isIntegral_iff (γ : ImagQuad d)).1 γ.2
  have hK : (y : ImagQuad d) + ω = ((m : ImagQuad d) + (n : ImagQuad d) * ω) ^ 3 := by
    have := congrArg (fun z : 𝓞 (ImagQuad d) => (z : ImagQuad d)) hγ
    push_cast at this
    rw [← hmn]
    exact this
  have him := congrArg QuadraticAlgebra.im hK
  simp only [pow_succ, pow_zero, one_mul, im_add, im_intCast, im_omega, im_mul, re_mul,
    re_add, re_intCast, re_omega] at him
  have him' : (1 : ℤ) = n * (3 * m ^ 2 - d * n ^ 2) := by
    have : (1 : ℚ) = n * (3 * m ^ 2 - d * n ^ 2) := by
      push_cast at him
      linear_combination him
    exact_mod_cast this
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' him'.symm with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact ⟨m, Or.inr (by linarith)⟩
  · exact ⟨m, Or.inl (by linarith)⟩

/-- **Ireland–Rosen, Proposition 17.10.2.** Let `d > 1` be squarefree, `d ≡ 1, 2 (mod 4)`, and
suppose that `3` does not divide the class number of `ℚ(√-d)`. Then `y² = x³ - d` has a solution
in integers iff `d = 3t² ± 1` for some integer `t`. (The ring of integers of `ℚ(√-d)`, Proposition
13.1.1, is the hypothesis `hA3`, proved by `integersOfImagQuad`.) -/
@[kb "irelandrosen1990" "Prop 17.10.2, p. 301"]
theorem exists_sq_eq_cube_sub_iff (hsq : Squarefree d) (h4 : d % 4 = 1 ∨ d % 4 = 2)
    (hA3 : IntegersOfImagQuad d) (h3 : ¬ 3 ∣ classNumber (ImagQuad d)) :
    (∃ x y : ℤ, y ^ 2 = x ^ 3 - d) ↔ ∃ t : ℤ, d = 3 * t ^ 2 + 1 ∨ d = 3 * t ^ 2 - 1 := by
  constructor
  · rintro ⟨x, y, h⟩
    exact exists_eq_of_sq_eq_cube_sub hsq h4 hA3 h3 h
  · rintro ⟨t, rfl | rfl⟩
    · exact ⟨4 * t ^ 2 + 1, 8 * t ^ 3 + 3 * t, by ring⟩
    · exact ⟨4 * t ^ 2 - 1, 8 * t ^ 3 - 3 * t, by ring⟩

/-- The hypothesis is proved: for `d > 1` squarefree with `d ≡ 1, 2 (mod 4)`, the integers of
`ℚ(√-d)` are `ℤ[√-d]` (Ireland–Rosen, Proposition 13.1.1, `NTKB.IrelandRosen.isIntegral_iff_of_mod_four_ne_one`
for `-d`, `-d ≡ 3, 2 (mod 4)`). -/
theorem integersOfImagQuad (hsq : Squarefree d) (h4 : d % 4 = 1 ∨ d % 4 = 2) :
    IntegersOfImagQuad d :=
  ⟨fun z => NTKB.IrelandRosen.isIntegral_iff_of_mod_four_ne_one (d := -d)
    (fun x hx => hsq x (dvd_neg.mp hx)) (by omega) z⟩

/-- **Ireland–Rosen, Proposition 17.10.2, unconditional** (with the ring of integers proved). -/
@[kb "irelandrosen1990" "Prop 17.10.2, p. 301"]
theorem exists_sq_eq_cube_sub_iff_unconditional (hsq : Squarefree d) (h4 : d % 4 = 1 ∨ d % 4 = 2)
    (h3 : ¬ 3 ∣ classNumber (ImagQuad d)) :
    (∃ x y : ℤ, y ^ 2 = x ^ 3 - d) ↔ ∃ t : ℤ, d = 3 * t ^ 2 + 1 ∨ d = 3 * t ^ 2 - 1 :=
  exists_sq_eq_cube_sub_iff hsq h4 (integersOfImagQuad hsq h4) h3

end Integers

end NTKB.IrelandRosen.CM
