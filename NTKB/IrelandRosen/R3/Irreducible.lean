/-
Ireland–Rosen, Chapter 9, §7–§8: irreducibles of `ℤ[i]` and their residue fields.
-/
import NTKB.IrelandRosen.R3.Gaussian
import NTKB.Attr
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Tactic.NormNum.Prime

/-!
# Irreducibles of `ℤ[i]` and the residue fields `ℤ[i]/π`

Ireland–Rosen, Chapter 9, §7 (Lemmas 1, 2, 3, 5, 8) and §8 (Proposition 9.8.1 and its corollary).

* every irreducible divides a rational prime (Lemma 1); an element of prime norm is irreducible
  (Lemma 2); `1 + i` is irreducible (Lemma 3);
* a prime `p ≡ 1 (mod 4)` is `π π̄` with `π` irreducible and `π`, `π̄` not associate (Lemma 5);
* an irreducible has prime norm or is associate to a rational prime `q ≡ 3 (mod 4)`
  (`irreducible_cases`), and a primary irreducible is either of prime norm `≡ 1 (mod 4)` or `-q`;
* a primary element is a product of primary irreducibles (Lemma 8);
* `ℤ[i]/π` has `N π` elements (Proposition 9.8.1), hence Fermat's theorem modulo `π`.
-/

namespace NTKB.IrelandRosen

open Zsqrtd

local notation "ℤ[i]" => GaussianInt

namespace Gaussian

lemma natAbs_norm_mul (x y : ℤ[i]) :
    (x * y).norm.natAbs = x.norm.natAbs * y.norm.natAbs := by
  rw [Zsqrtd.norm_mul, Int.natAbs_mul]

lemma dvd_norm (x : ℤ[i]) : x ∣ (x.norm : ℤ[i]) := ⟨star x, Zsqrtd.norm_eq_mul_conj x⟩

lemma dvd_natAbs_norm (x : ℤ[i]) : x ∣ ((x.norm.natAbs : ℕ) : ℤ[i]) := by
  have : ((x.norm.natAbs : ℕ) : ℤ[i]) = ((x.norm : ℤ) : ℤ[i]) := by
    rw [← Int.cast_natCast, natAbs_norm]
  rw [this]; exact dvd_norm x

lemma norm_dvd_norm {x y : ℤ[i]} (h : x ∣ y) : x.norm.natAbs ∣ y.norm.natAbs := by
  obtain ⟨z, rfl⟩ := h; rw [natAbs_norm_mul]; exact dvd_mul_right _ _

lemma natAbs_norm_natCast (n : ℕ) : (n : ℤ[i]).norm.natAbs = n ^ 2 := by
  rw [Zsqrtd.norm_natCast, Int.natAbs_mul, Int.natAbs_natCast, sq]

lemma natAbs_norm_intCast (n : ℤ) : (n : ℤ[i]).norm.natAbs = n.natAbs ^ 2 := by
  rw [Zsqrtd.norm_intCast, Int.natAbs_mul, sq]

lemma natAbs_norm_eq_of_associated {x y : ℤ[i]} (h : Associated x y) :
    x.norm.natAbs = y.norm.natAbs :=
  Nat.dvd_antisymm (norm_dvd_norm h.dvd) (norm_dvd_norm h.symm.dvd)

lemma natAbs_norm_star (x : ℤ[i]) : (star x).norm.natAbs = x.norm.natAbs := by
  simp [norm_def]

lemma isUnit_iff_natAbs_norm {x : ℤ[i]} : IsUnit x ↔ x.norm.natAbs = 1 :=
  Zsqrtd.norm_eq_one_iff.symm

lemma ne_zero_of_irreducible {x : ℤ[i]} (h : Irreducible x) : x ≠ 0 := h.ne_zero

lemma natAbs_norm_pos {x : ℤ[i]} (h : x ≠ 0) : 0 < x.norm.natAbs := by
  rw [Int.natAbs_pos]; intro h'; exact h (by simpa [norm_def] using GaussianInt.norm_eq_zero.1 h')

/-- **Lemma 2 of §7.** An element of `ℤ[i]` whose norm is a rational prime is irreducible. -/
@[kb "irelandrosen1990" "Ch. 9, §7, Lemma 2, p. 131"]
theorem irreducible_of_prime_norm {α : ℤ[i]} (h : α.norm.natAbs.Prime) : Irreducible α := by
  refine ⟨fun hu => h.one_lt.ne' (isUnit_iff_natAbs_norm.1 hu), fun a b hab => ?_⟩
  rw [hab, natAbs_norm_mul, Nat.prime_mul_iff] at h
  rcases h with ⟨-, hb⟩ | ⟨-, ha⟩
  · exact Or.inr (isUnit_iff_natAbs_norm.2 hb)
  · exact Or.inl (isUnit_iff_natAbs_norm.2 ha)

/-- **Lemma 3 of §7** (irreducibility part): `1 + i` is irreducible. -/
@[kb "irelandrosen1990" "Ch. 9, §7, Lemma 3, p. 131"]
theorem irreducible_onePlusI : Irreducible onePlusI :=
  irreducible_of_prime_norm (by rw [norm_onePlusI]; norm_num)

lemma prime_onePlusI : Prime onePlusI := irreducible_onePlusI.prime

/-- **Lemma 1 of §7.** Every irreducible of `ℤ[i]` divides a rational prime. -/
@[kb "irelandrosen1990" "Ch. 9, §7, Lemma 1, p. 131"]
theorem exists_prime_dvd_of_irreducible {π : ℤ[i]} (hπ : Irreducible π) :
    ∃ p : ℕ, p.Prime ∧ π ∣ (p : ℤ[i]) := by
  have hp := hπ.prime
  suffices H : ∀ n : ℕ, n ≠ 0 → π ∣ (n : ℤ[i]) → ∃ p : ℕ, p.Prime ∧ π ∣ (p : ℤ[i]) from
    H _ (natAbs_norm_pos hπ.ne_zero).ne' (dvd_natAbs_norm π)
  intro n
  induction n using Nat.recOnMul with
  | zero => intro h; exact absurd rfl h
  | one => intro _ h; exact absurd (isUnit_of_dvd_one (by simpa using h)) hπ.not_isUnit
  | prime p hp' => intro _ h; exact ⟨p, hp', h⟩
  | mul a b iha ihb =>
    intro hab h
    rw [Nat.cast_mul] at h
    rcases hp.dvd_or_dvd h with h | h
    · exact iha (left_ne_zero_of_mul hab) h
    · exact ihb (right_ne_zero_of_mul hab) h

lemma natCast_prime_sq_add_sq {p : ℕ} (hp : p.Prime) {a b : ℤ} (h : a ^ 2 + b ^ 2 = p) :
    a ≠ 0 ∧ b ≠ 0 := by
  have key : ∀ c : ℤ, c ^ 2 ≠ p := by
    intro c hc
    have : c.natAbs ^ 2 = p := by
      have := congrArg Int.natAbs hc; simpa [Int.natAbs_pow] using this
    rw [sq] at this
    rcases Nat.prime_mul_iff.1 (this ▸ hp) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2] at h1 <;>
      exact Nat.not_prime_one h1
  constructor
  · rintro rfl; exact key b (by simpa using h)
  · rintro rfl; exact key a (by simpa using h)

/-- **Lemma 5 of §7.** A prime `p ≡ 1 (mod 4)` factors as `p = π π̄` with `π` irreducible, and the
ideals `(π)` and `(π̄)` are distinct (`π` and `π̄` are not associate). -/
@[kb "irelandrosen1990" "Ch. 9, §7, Lemma 5, p. 131"]
theorem exists_irreducible_eq_mul_star {p : ℕ} (hp : p.Prime) (h4 : p % 4 = 1) :
    ∃ π : ℤ[i], Irreducible π ∧ (p : ℤ[i]) = π * star π ∧ ¬ Associated π (star π) := by
  haveI := Fact.mk hp
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
  set π : ℤ[i] := ⟨a, b⟩ with hπdef
  have hN : π.norm = p := by rw [norm_def]; simp [hπdef]; exact_mod_cast hab
  have hNat : π.norm.natAbs = p := by rw [hN]; simp
  refine ⟨π, irreducible_of_prime_norm (hNat ▸ hp), ?_, ?_⟩
  · rw [← Zsqrtd.norm_eq_mul_conj, hN]; simp
  · rintro ⟨u, hu⟩
    have hab' : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = p := by exact_mod_cast hab
    obtain ⟨ha0, hb0⟩ := natCast_prime_sq_add_sq hp hab'
    have hu' := isUnit_iff_eq.1 u.isUnit
    have hre := congrArg Zsqrtd.re hu
    have him := congrArg Zsqrtd.im hu
    rcases hu' with h | h | h | h <;> rw [h] at hre him <;>
      simp [hπdef] at hre him
    · omega
    · omega
    · -- `a = -b`: then `p = 2 a²`
      have : (p : ℤ) = 2 * (a : ℤ) ^ 2 := by rw [← hab']; nlinarith
      have h2 : p = 2 * (a * a) := by zify; rw [this]; ring
      rcases Nat.prime_mul_iff.1 (h2 ▸ hp) with ⟨-, h3⟩ | ⟨-, h3⟩
      · rw [h3] at h2; omega
      · omega
    · have : (p : ℤ) = 2 * (a : ℤ) ^ 2 := by rw [← hab']; nlinarith
      have h2 : p = 2 * (a * a) := by zify; rw [this]; ring
      rcases Nat.prime_mul_iff.1 (h2 ▸ hp) with ⟨-, h3⟩ | ⟨-, h3⟩
      · rw [h3] at h2; omega
      · omega

/-- An irreducible of `ℤ[i]` either has prime norm or is associate to a rational prime
`q ≡ 3 (mod 4)` (the description of the irreducibles completed by Lemmas 1–5 of §7). -/
@[kb "irelandrosen1990" "Ch. 9, §7 (description of the irreducibles), p. 132"]
theorem irreducible_cases {π : ℤ[i]} (hπ : Irreducible π) :
    π.norm.natAbs.Prime ∨ ∃ q : ℕ, q.Prime ∧ q % 4 = 3 ∧ Associated π (q : ℤ[i]) := by
  obtain ⟨p, hp, hπp⟩ := exists_prime_dvd_of_irreducible hπ
  have hdvd := norm_dvd_norm hπp
  rw [natAbs_norm_natCast, Nat.dvd_prime_pow hp] at hdvd
  obtain ⟨k, hk, hk'⟩ := hdvd
  interval_cases k
  · exact absurd (isUnit_iff_natAbs_norm.2 (by simpa using hk')) hπ.not_isUnit
  · left; rw [hk', pow_one]; exact hp
  · right
    obtain ⟨γ, hγ⟩ := hπp
    have hγ1 : γ.norm.natAbs = 1 := by
      have := congrArg (fun x : ℤ[i] => x.norm.natAbs) hγ
      simp only [natAbs_norm_natCast, natAbs_norm_mul, hk'] at this
      have hp2 : 0 < p ^ 2 := pow_pos hp.pos 2
      exact (Nat.mul_eq_left hp2.ne').1 this.symm
    have hassoc : Associated π (p : ℤ[i]) := by
      rw [hγ]; exact (associated_mul_unit_right π γ (isUnit_iff_natAbs_norm.2 hγ1))
    haveI := Fact.mk hp
    exact ⟨p, hp, GaussianInt.mod_four_eq_three_of_nat_prime_of_prime p
      (hassoc.prime_iff.1 hπ.prime), hassoc⟩

lemma natAbs_norm_mod_four (x : ℤ[i]) : x.norm.natAbs % 4 ≠ 3 := by
  have h : (x.norm.natAbs : ℤ) = x.re ^ 2 + x.im ^ 2 := by rw [natAbs_norm, norm_def]
  have : ∀ t : ℤ, t ^ 2 % 4 = 0 ∨ t ^ 2 % 4 = 1 := by
    intro t
    rcases Int.emod_two_eq_zero_or_one t with ht | ht
    · obtain ⟨s, rfl⟩ : 2 ∣ t := Int.dvd_of_emod_eq_zero ht
      left; ring_nf; omega
    · obtain ⟨s, hs⟩ : ∃ s, t = 2 * s + 1 := ⟨t / 2, by omega⟩
      subst hs; right; ring_nf; omega
  have h1 := this x.re; have h2 := this x.im
  omega

/-- The norm of an element `≡ 1 (mod (1 + i)³)` is `≡ 1 (mod 4)`. -/
lemma IsPrimary'.natAbs_norm_mod_four {α : ℤ[i]} (h : IsPrimary' α) :
    α.norm.natAbs % 4 = 1 := by
  have hn : (α.norm.natAbs : ℤ) = α.re ^ 2 + α.im ^ 2 := by rw [natAbs_norm, norm_def]
  have hr := h.re_odd
  obtain ⟨m, hm⟩ := h.im_even
  obtain ⟨s, hs⟩ : ∃ s, α.re = 2 * s + 1 := ⟨α.re / 2, by omega⟩
  rw [hs, hm] at hn
  have : (α.norm.natAbs : ℤ) = 4 * (s ^ 2 + s + m ^ 2) + 1 := by rw [hn]; ring
  omega

/-- A primary irreducible is either of prime norm `p ≡ 1 (mod 4)` or equal to `-q` for a rational
prime `q ≡ 3 (mod 4)`. -/
theorem IsPrimary.irreducible_cases {π : ℤ[i]} (hp : IsPrimary π) (hπ : Irreducible π) :
    (π.norm.natAbs.Prime ∧ π.norm.natAbs % 4 = 1) ∨
      ∃ q : ℕ, q.Prime ∧ q % 4 = 3 ∧ π = -(q : ℤ[i]) := by
  rcases Gaussian.irreducible_cases hπ with h | ⟨q, hq, hq3, u, hu⟩
  · exact Or.inl ⟨h, hp.2.natAbs_norm_mod_four⟩
  · right
    refine ⟨q, hq, hq3, ?_⟩
    have hπeq : π = (u⁻¹ : ℤ[i]ˣ) * (q : ℤ[i]) := by
      rw [← hu, mul_comm, mul_assoc, Units.mul_inv, mul_one]
    have hP := hp.2
    rw [hπeq] at hP ⊢
    rw [isPrimary'_iff] at hP
    rcases isUnit_iff_eq.1 (u⁻¹).isUnit with h | h | h | h <;> rw [h] at hP ⊢ <;> simp at hP
    · omega
    · simp
    · omega
    · omega

/-! ### Lemma 8: factorization into primary irreducibles -/

lemma multiset_prod_isUnit (s : Multiset ℤ[i]) (h : ∀ x ∈ s, IsUnit x) : IsUnit s.prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons]
    exact (h a (Multiset.mem_cons_self _ _)).mul (ih fun x hx => h x (Multiset.mem_cons_of_mem hx))

/-- **Lemma 8 of §7.** A primary element is a product of primary irreducibles. -/
@[kb "irelandrosen1990" "Ch. 9, §7, Lemma 8, p. 132"]
theorem IsPrimary.exists_multiset_prod_eq {α : ℤ[i]} (hα : IsPrimary α) :
    ∃ s : Multiset ℤ[i], (∀ x ∈ s, Irreducible x ∧ IsPrimary x) ∧ s.prod = α := by
  classical
  have hα0 : α ≠ 0 := by
    rintro rfl; exact hα.2.not_onePlusI_dvd (dvd_zero _)
  obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod hα0
  set f := UniqueFactorizationMonoid.factors α
  -- each factor is irreducible and prime to `1 + i`
  have hirr : ∀ x ∈ f, Irreducible x := fun x hx => UniqueFactorizationMonoid.irreducible_of_factor x hx
  have hdvd : ∀ x ∈ f, x ∣ α := fun x hx => UniqueFactorizationMonoid.dvd_of_mem_factors hx
  have h2 : ∀ x ∈ f, ¬ onePlusI ∣ x := fun x hx h =>
    hα.2.not_onePlusI_dvd (h.trans (hdvd x hx))
  -- the unit making a factor primary
  have hex : ∀ x ∈ f, ∃ v : ℤ[i], IsUnit v ∧ IsPrimary' (v * x) := fun x hx =>
    exists_isPrimary'_unit_mul (h2 x hx)
  let v : ℤ[i] → ℤ[i] := fun x => if hx : x ∈ f then (hex x hx).choose else 1
  have hv : ∀ x ∈ f, IsUnit (v x) ∧ IsPrimary' (v x * x) := fun x hx => by
    simp only [v, hx, ↓reduceDIte]; exact (hex x hx).choose_spec
  refine ⟨f.map (fun x => v x * x), ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hy
    refine ⟨(irreducible_isUnit_mul (hv x hx).1).2 (hirr x hx), fun h => (hirr x hx).not_isUnit ?_, (hv x hx).2⟩
    exact isUnit_of_mul_isUnit_right h
  · -- `α = w ∏ (v x * x)` for a unit `w`, and both `α` and the product are primary, so `w = 1`
    have hprod : (f.map (fun x => v x * x)).prod = (f.map v).prod * f.prod := by
      rw [Multiset.prod_map_mul, Multiset.map_id']
    have hvu : IsUnit (f.map v).prod := by
      exact multiset_prod_isUnit _ fun y hy => by
        obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hy; exact (hv x hx).1
    obtain ⟨w, hw⟩ := hvu
    have hP : IsPrimary' (f.map (fun x => v x * x)).prod :=
      isPrimary'_multiset_prod _ fun y hy => by
        obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hy; exact (hv x hx).2
    -- `prod = w * f.prod = w * α * u⁻¹`
    have hfprod : f.prod = α * ((u⁻¹ : ℤ[i]ˣ) : ℤ[i]) := by
      rw [← hu, mul_assoc, Units.mul_inv, mul_one]
    have heq : (f.map (fun x => v x * x)).prod = α * ((w * u⁻¹ : ℤ[i]ˣ) : ℤ[i]) := by
      rw [hprod, ← hw, hfprod, Units.val_mul]; ring
    -- the unit `w u⁻¹` is primary-congruent to 1
    have hunit : IsPrimary' ((w * u⁻¹ : ℤ[i]ˣ) : ℤ[i]) := by
      rw [heq] at hP
      -- `α (z) ≡ 1` and `α ≡ 1` give `z ≡ 1` modulo `(1 + i)³`, as `1 + i ∤ α`
      unfold IsPrimary' at hP ⊢
      have h1 : onePlusI ^ 3 ∣ α * (((w * u⁻¹ : ℤ[i]ˣ) : ℤ[i]) - 1) := by
        have : α * (((w * u⁻¹ : ℤ[i]ˣ) : ℤ[i]) - 1) =
            (α * ((w * u⁻¹ : ℤ[i]ˣ) : ℤ[i]) - 1) - (α - 1) := by ring
        rw [this]; exact dvd_sub hP hα.2
      exact (prime_onePlusI.pow_dvd_of_dvd_mul_left 3
        hα.2.not_onePlusI_dvd h1)
    have := hunit.eq_one_of_isUnit (Units.isUnit _)
    rw [heq, this, mul_one]

/-! ### Proposition 9.8.1: the residue fields -/

lemma isMaximal_span {π : ℤ[i]} (hπ : Irreducible π) : (Ideal.span {π}).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible hπ

lemma card_quotient_natCast {n : ℕ} (hn : n ≠ 0) :
    Nat.card (ℤ[i] ⧸ Ideal.span {(n : ℤ[i])}) = n ^ 2 := by
  haveI : NeZero n := ⟨hn⟩
  let g : ZMod n × ZMod n → ℤ[i] ⧸ Ideal.span {(n : ℤ[i])} :=
    fun x => Ideal.Quotient.mk _ ⟨x.1.val, x.2.val⟩
  have hmk : ∀ y z : ℤ[i], Ideal.Quotient.mk (Ideal.span {(n : ℤ[i])}) y =
      Ideal.Quotient.mk _ z ↔ (n : ℤ) ∣ y.re - z.re ∧ (n : ℤ) ∣ y.im - z.im := by
    intro y z
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, ← Int.cast_natCast, Zsqrtd.intCast_dvd]
    simp
  have key : ∀ a b : ZMod n, (n : ℤ) ∣ (a.val : ℤ) - b.val → a = b := by
    intro a b h
    apply ZMod.val_injective
    have ha := a.val_lt; have hb := b.val_lt
    have := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
    omega
  have hinj : Function.Injective g := by
    rintro ⟨x1, x2⟩ ⟨y1, y2⟩ h
    rw [hmk] at h
    simp only at h
    rw [key x1 y1 h.1, key x2 y2 h.2]
  have hsurj : Function.Surjective g := by
    intro y
    obtain ⟨α, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨((α.re : ZMod n), (α.im : ZMod n)), ?_⟩
    simp only [g]
    rw [hmk]
    simp only [ZMod.val_intCast]
    constructor
    · exact ⟨-(α.re / n), by rw [Int.emod_def]; ring⟩
    · exact ⟨-(α.im / n), by rw [Int.emod_def]; ring⟩
  rw [← Nat.card_congr (Equiv.ofBijective g ⟨hinj, hsurj⟩), Nat.card_prod, Nat.card_zmod, sq]

lemma nonempty_residueEquivZMod {π : ℤ[i]} (hp : π.norm.natAbs.Prime) :
    Nonempty (ℤ[i] ⧸ Ideal.span {π} ≃+* ZMod π.norm.natAbs) := by
  set p := π.norm.natAbs with hpdef
  set R := ℤ[i] ⧸ Ideal.span {π}
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  -- `π ∣ n` iff `p ∣ n` for rational integers `n`
  have hdiv : ∀ n : ℤ, π ∣ (n : ℤ[i]) ↔ (p : ℤ) ∣ n := by
    intro n
    constructor
    · intro h
      have := norm_dvd_norm h
      rw [natAbs_norm_intCast] at this
      exact Int.natCast_dvd.2 (hp.dvd_of_dvd_pow this)
    · rintro ⟨m, rfl⟩
      have : π ∣ ((p : ℤ) : ℤ[i]) := by rw [Int.cast_natCast]; exact dvd_natAbs_norm π
      rw [Int.cast_mul]; exact dvd_mul_of_dvd_left this _
  -- the imaginary part of `π` is prime to `p`
  have hb : ¬ (p : ℤ) ∣ π.im := by
    rintro ⟨c, hc⟩
    have hN : π.re ^ 2 + π.im ^ 2 = p := by rw [hpdef, natAbs_norm, norm_def]
    have hne := (natCast_prime_sq_add_sq hp hN).2
    have hc0 : c ≠ 0 := by rintro rfl; exact hne (by simpa using hc)
    have : (p : ℤ) ^ 2 ≤ π.im ^ 2 := by
      have h1 : (1 : ℤ) ≤ c ^ 2 := by rw [← sq_abs]; nlinarith [Int.one_le_abs hc0]
      rw [hc, mul_pow]; nlinarith [sq_nonneg (p : ℤ)]
    have h2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
    nlinarith [sq_nonneg π.re]
  have hcop : IsCoprime π.im (p : ℤ) :=
    ((Int.isCoprime_iff_gcd_eq_one).2 (by
      rw [Int.gcd_comm]
      exact (Nat.Coprime.symm ((Nat.coprime_comm).1 ((Nat.Prime.coprime_iff_not_dvd hp).2
        (by rw [← Int.natCast_dvd]; simpa using hb))))))
  obtain ⟨u, v, huv⟩ := hcop
  -- `i ≡ -a u (mod π)`
  have hi : π ∣ I - ((-(π.re * u) : ℤ) : ℤ[i]) := by
    have hpdvd : π ∣ ((p : ℤ) : ℤ[i]) := by rw [Int.cast_natCast]; exact dvd_natAbs_norm π
    have : I - ((-(π.re * u) : ℤ) : ℤ[i]) = (u : ℤ[i]) * π + ((v * I : ℤ[i])) * ((p : ℤ) : ℤ[i]) := by
      have e : (u : ℤ[i]) * π.im + (v : ℤ[i]) * (p : ℤ) = 1 := by exact_mod_cast huv
      conv_lhs => rw [show I = I * 1 by ring, ← e]
      conv_rhs => rw [eq_re_add_im π]
      push_cast; ring
    rw [this]; exact dvd_add (dvd_mul_left _ _) (dvd_mul_of_dvd_right hpdvd _)
  -- the map `ℤ → ℤ[i]/π` is surjective with kernel `p ℤ`
  let f : ℤ →+* R := Int.castRingHom R
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨α, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨α.re + α.im * (-(π.re * u)), ?_⟩
    simp only [f, eq_intCast, ← map_intCast (Ideal.Quotient.mk (Ideal.span {π}))]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
    have : ((α.re + α.im * (-(π.re * u)) : ℤ) : ℤ[i]) - α =
        -((α.im : ℤ[i]) * (I - ((-(π.re * u) : ℤ) : ℤ[i]))) := by
      ext <;> simp <;> ring
    rw [this]; exact (dvd_mul_of_dvd_right hi _).neg_right
  have hker : RingHom.ker f = Ideal.span {(p : ℤ)} := by
    ext n
    rw [RingHom.mem_ker, Ideal.mem_span_singleton, ← hdiv]
    simp only [f, eq_intCast, ← map_intCast (Ideal.Quotient.mk (Ideal.span {π}))]
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have e1 : R ≃+* ℤ ⧸ Ideal.span {(p : ℤ)} :=
    ((RingHom.quotientKerEquivOfSurjective hsurj).symm).trans (Ideal.quotEquivOfEq hker)
  exact ⟨e1.trans (Int.quotientSpanNatEquivZMod p)⟩

/-- For `π` of prime norm `p`, the residue field `ℤ[i]/π` is `ZMod p`. -/
noncomputable def residueEquivZMod {π : ℤ[i]} (hp : π.norm.natAbs.Prime) :
    ℤ[i] ⧸ Ideal.span {π} ≃+* ZMod π.norm.natAbs :=
  (nonempty_residueEquivZMod hp).some

/-- Reduction modulo `π` (of prime norm `p`) as a ring homomorphism `ℤ[i] → ZMod p`. -/
noncomputable def toZMod {π : ℤ[i]} (hp : π.norm.natAbs.Prime) : ℤ[i] →+* ZMod π.norm.natAbs :=
  (residueEquivZMod hp).toRingHom.comp (Ideal.Quotient.mk _)

lemma toZMod_eq_zero_iff {π : ℤ[i]} (hp : π.norm.natAbs.Prime) (α : ℤ[i]) :
    toZMod hp α = 0 ↔ π ∣ α := by
  rw [toZMod, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    map_eq_zero_iff _ (residueEquivZMod hp).injective, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]

lemma toZMod_eq_iff {π : ℤ[i]} (hp : π.norm.natAbs.Prime) (α β : ℤ[i]) :
    toZMod hp α = toZMod hp β ↔ π ∣ α - β := by
  rw [← sub_eq_zero, ← map_sub, toZMod_eq_zero_iff]

lemma card_quotient_of_prime_norm {π : ℤ[i]} (hp : π.norm.natAbs.Prime) :
    Nat.card (ℤ[i] ⧸ Ideal.span {π}) = π.norm.natAbs := by
  rw [Nat.card_congr (residueEquivZMod hp).toEquiv, Nat.card_zmod]

/-- **Proposition 9.8.1.** For an irreducible `π` of `ℤ[i]`, the residue ring `ℤ[i]/π` (a field) has
`N π` elements. -/
@[kb "irelandrosen1990" "Prop 9.8.1, p. 132"]
theorem card_quotient_of_irreducible {π : ℤ[i]} (hπ : Irreducible π) :
    (Ideal.span {π}).IsMaximal ∧ Nat.card (ℤ[i] ⧸ Ideal.span {π}) = π.norm.natAbs := by
  refine ⟨isMaximal_span hπ, ?_⟩
  rcases irreducible_cases hπ with h | ⟨q, hq, -, hassoc⟩
  · exact card_quotient_of_prime_norm h
  · rw [Ideal.span_singleton_eq_span_singleton.2 hassoc, natAbs_norm_eq_of_associated hassoc,
      natAbs_norm_natCast, card_quotient_natCast hq.ne_zero]

/-- **Corollary to Proposition 9.8.1** (Fermat's theorem modulo `π`): if `π ∤ α` then
`α ^ (N π - 1) ≡ 1 (mod π)`. -/
@[kb "irelandrosen1990" "Ch. 9, §8, Corollary to Prop 9.8.1, p. 133"]
theorem pow_norm_sub_one_modEq {π α : ℤ[i]} (hπ : Irreducible π) (hα : ¬ π ∣ α) :
    π ∣ α ^ (π.norm.natAbs - 1) - 1 := by
  obtain ⟨hmax, hcard⟩ := card_quotient_of_irreducible hπ
  letI := Ideal.Quotient.field (Ideal.span {π})
  haveI : Finite (ℤ[i] ⧸ Ideal.span {π}) := Nat.finite_of_card_ne_zero (by
    rw [hcard]; exact (natAbs_norm_pos hπ.ne_zero).ne')
  letI := Fintype.ofFinite (ℤ[i] ⧸ Ideal.span {π})
  have hne : Ideal.Quotient.mk (Ideal.span {π}) α ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have := FiniteField.pow_card_sub_one_eq_one _ hne
  rw [Fintype.card_eq_nat_card, hcard, ← map_pow, ← map_one (Ideal.Quotient.mk _),
    Ideal.Quotient.eq, Ideal.mem_span_singleton] at this
  exact this

end Gaussian

end NTKB.IrelandRosen
