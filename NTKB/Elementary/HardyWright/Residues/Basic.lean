/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Data.ZMod.Units
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import NTKB.Attr

/-!
# Complete and reduced residue systems (Hardy–Wright, Chapter V, §§ 5.2 to 5.5)

Hardy and Wright call a family of integers `a₁, …, aₘ` a *complete system of incongruent
residues* modulo `m` when every integer is congruent to exactly one `aᵢ`, and a *complete set of
residues prime to `m`* when the `aᵢ` are prime to `m` and every integer prime to `m` is congruent to
exactly one of them. Mathlib has no name for these notions; we state them for an indexed family
`a : ι → ℤ` through the reduction map `ℤ → ZMod m`:

* `NTKB.HardyWright.IsCompleteResidueSystem m a`: `i ↦ (a i : ZMod m)` is a bijection;
* `NTKB.HardyWright.IsReducedResidueSystem m a`: every `a i` is prime to `m`, `i ↦ (a i : ZMod m)`
  is injective and every unit of `ZMod m` is hit.

Results: Theorems 54, 56, 57, 58, 59 and 61 of Hardy–Wright. (Theorem 55 is Mathlib's
`Int.ModEq.cancel_left_of_coprime` with `Int.ModEq.mul_left`, Theorem 60 is `Nat.totient_mul`.)
The locators of the `@[kb]` tags are the printed pages of the sixth edition.
-/

namespace NTKB.HardyWright

/-- A family `a : ι → ℤ` is a complete system of incongruent residues modulo `m`
[hardywright2008, § 5.2]: every residue class modulo `m` contains exactly one `a i`. -/
def IsCompleteResidueSystem (m : ℕ) {ι : Type*} (a : ι → ℤ) : Prop :=
  Function.Bijective fun i ↦ (a i : ZMod m)

/-- A family `a : ι → ℤ` is a complete set of residues prime to `m` [hardywright2008, § 5.5]:
every `a i` is prime to `m`, and every residue class of numbers prime to `m` contains exactly one
`a i`. -/
def IsReducedResidueSystem (m : ℕ) {ι : Type*} (a : ι → ℤ) : Prop :=
  (∀ i, IsCoprime (a i) m) ∧ (Function.Injective fun i ↦ (a i : ZMod m)) ∧
    ∀ x : ZMod m, IsUnit x → ∃ i, (a i : ZMod m) = x

variable {ι κ : Type*}

/-- The least non-negative residues `0, 1, …, m - 1` form a complete system. -/
theorem isCompleteResidueSystem_range (m : ℕ) [NeZero m] :
    IsCompleteResidueSystem m (fun i : Fin m ↦ ((i : ℕ) : ℤ)) := by
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨fun i j h ↦ ?_, by simp⟩
  simp only [Int.cast_natCast] at h
  exact Fin.ext (by rw [← ZMod.val_natCast_of_lt i.2, ← ZMod.val_natCast_of_lt j.2, h])

lemma IsCompleteResidueSystem.finite {m : ℕ} [NeZero m] {a : ι → ℤ}
    (h : IsCompleteResidueSystem m a) : Finite ι :=
  Finite.of_injective _ h.1

lemma IsCompleteResidueSystem.card {m : ℕ} [NeZero m] {a : ι → ℤ}
    (h : IsCompleteResidueSystem m a) : Nat.card ι = m := by
  rw [Nat.card_eq_of_bijective _ h, Nat.card_zmod]

lemma IsReducedResidueSystem.isUnit {m : ℕ} {a : ι → ℤ} (h : IsReducedResidueSystem m a)
    (i : ι) : IsUnit (a i : ZMod m) :=
  (ZMod.isUnit_intCast_iff_isCoprime _ _).2 (h.1 i).symm

/-- A reduced residue system is the same as a bijection onto the units of `ZMod m`. -/
lemma isReducedResidueSystem_iff {m : ℕ} {a : ι → ℤ} :
    IsReducedResidueSystem m a ↔ ∃ ha : ∀ i, IsUnit (a i : ZMod m),
      Function.Bijective fun i ↦ (ha i).unit := by
  constructor
  · intro h
    refine ⟨h.isUnit, fun i j hij ↦ h.2.1 (congrArg Units.val hij), fun u ↦ ?_⟩
    obtain ⟨i, hi⟩ := h.2.2 u u.isUnit
    exact ⟨i, Units.ext (by simpa using hi)⟩
  · rintro ⟨ha, hb⟩
    refine ⟨fun i ↦ ((ZMod.isUnit_intCast_iff_isCoprime _ _).1 (ha i)).symm,
      fun i j hij ↦ hb.1 (Units.ext (by simpa using hij)), fun x hx ↦ ?_⟩
    obtain ⟨i, hi⟩ := hb.2 hx.unit
    exact ⟨i, by simpa using congrArg Units.val hi⟩

lemma IsReducedResidueSystem.card {m : ℕ} [NeZero m] {a : ι → ℤ}
    (h : IsReducedResidueSystem m a) : Nat.card ι = m.totient := by
  obtain ⟨ha, hb⟩ := isReducedResidueSystem_iff.1 h
  rw [Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

/-- **Theorem 54** [hardywright2008]: if `(k, m) = d`, then `ka ≡ ka' (mod m)` if and only if
`a ≡ a' (mod m / d)`. -/
@[kb "hardywright2008" "Thm 54, p. 61"]
theorem modEq_mul_left_iff_modEq_div_gcd {m : ℤ} (hm : 0 < m) (k a a' : ℤ) :
    k * a ≡ k * a' [ZMOD m] ↔ a ≡ a' [ZMOD m / m.gcd k] := by
  refine ⟨Int.ModEq.cancel_left_div_gcd hm, fun h ↦ ?_⟩
  -- `m = d (m / d)` and `d ∣ k`, so `m ∣ k (a' - a)`.
  set d : ℤ := (m.gcd k : ℤ) with hd_def
  have hd : d ∣ m := Int.gcd_dvd_left ..
  obtain ⟨k', hk'⟩ : d ∣ k := Int.gcd_dvd_right ..
  rw [Int.modEq_iff_dvd] at h ⊢
  have hm' : m = d * (m / d) := (Int.mul_ediv_cancel' hd).symm
  rw [hm', hk', ← mul_sub, mul_assoc]
  exact mul_dvd_mul_left _ (dvd_mul_of_dvd_right h _)

/-- **Theorem 56** [hardywright2008]: if `a₁, …, aₘ` is a complete system of residues modulo
`m` and `(k, m) = 1`, then `ka₁, …, kaₘ` is also one; more generally so is `ka₁ + l, …, kaₘ + l`
(the remark after the theorem). -/
@[kb "hardywright2008" "Thm 56, p. 61"]
theorem IsCompleteResidueSystem.mul_add {m : ℕ} {a : ι → ℤ} (h : IsCompleteResidueSystem m a)
    {k : ℤ} (hk : IsCoprime k m) (l : ℤ) :
    IsCompleteResidueSystem m (fun i ↦ k * a i + l) := by
  have hu : IsUnit (k : ZMod m) := (ZMod.isUnit_intCast_iff_isCoprime _ _).2 hk.symm
  have : (fun i ↦ ((k * a i + l : ℤ) : ZMod m)) =
      (fun x ↦ (k : ZMod m) * x + l) ∘ fun i ↦ (a i : ZMod m) := by
    ext i; push_cast; rfl
  unfold IsCompleteResidueSystem
  rw [this]
  refine Function.Bijective.comp ⟨fun x y hxy ↦ ?_, fun y ↦ ⟨hu.unit⁻¹ * (y - l), ?_⟩⟩ h
  · simpa [hu.mul_right_inj] using hxy
  · simp [← mul_assoc]

/-- **Theorem 56** [hardywright2008], the case `l = 0` as stated. -/
@[kb "hardywright2008" "Thm 56, p. 61"]
theorem IsCompleteResidueSystem.mul {m : ℕ} {a : ι → ℤ} (h : IsCompleteResidueSystem m a)
    {k : ℤ} (hk : IsCoprime k m) : IsCompleteResidueSystem m (fun i ↦ k * a i) := by
  simpa using h.mul_add hk 0

/-- **Theorem 57** [hardywright2008]: if `(k, m) = d` then `kx ≡ l (mod m)` is soluble if and only
if `d ∣ l`, and it then has just `d` solutions (incongruent modulo `m`). -/
@[kb "hardywright2008" "Thm 57, p. 62"]
theorem exists_mul_modEq_iff_and_card (m : ℕ) [NeZero m] (k l : ℤ) :
    ((∃ x : ℤ, k * x ≡ l [ZMOD m]) ↔ (k.gcd m : ℤ) ∣ l) ∧
      ((k.gcd m : ℤ) ∣ l →
        Nat.card {x : ZMod m // (k : ZMod m) * x = l} = k.gcd m) := by
  have hsol : (∃ x : ℤ, k * x ≡ l [ZMOD m]) ↔ (k.gcd m : ℤ) ∣ l := by
    constructor
    · rintro ⟨x, hx⟩
      have h1 : (k.gcd m : ℤ) ∣ k * x := dvd_mul_of_dvd_left (Int.gcd_dvd_left ..) _
      have h2 : (k.gcd m : ℤ) ∣ l - k * x :=
        (Int.gcd_dvd_right ..).trans (Int.modEq_iff_dvd.1 hx)
      simpa using dvd_add h2 h1
    · rintro ⟨c, rfl⟩
      refine ⟨k.gcdA m * c, ?_⟩
      rw [Int.gcd_eq_gcd_ab, Int.modEq_iff_dvd]
      exact ⟨k.gcdB m * c, by ring⟩
  refine ⟨hsol, fun hd ↦ ?_⟩
  obtain ⟨x₀, hx₀⟩ := hsol.2 hd
  -- the solutions form a coset of the kernel of `x ↦ k x`, which has `gcd (m, k)` elements
  let f : ZMod m →+ ZMod m := nsmulAddMonoidHom (k : ZMod m).val
  have hf : ∀ x, f x = (k : ZMod m) * x := fun x ↦ by
    simp [f, nsmul_eq_mul]
  have hrange : (l : ZMod m) ∈ Set.range f :=
    ⟨x₀, by rw [hf]; exact_mod_cast (ZMod.intCast_eq_intCast_iff _ _ _).2 hx₀⟩
  classical
  have hfib := AddMonoidHom.card_fiber_eq_of_mem_range f hrange ⟨0, map_zero f⟩
  have hker := IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod m) (k : ZMod m).val
  rw [Nat.card_zmod] at hker
  have hgcd : m.gcd (k : ZMod m).val = k.gcd m := by
    rw [Int.gcd_natCast_natCast .. |>.symm, ZMod.val_intCast, Int.gcd_comm, Int.gcd_emod]
  rw [hgcd] at hker
  have h0 : Nat.card (nsmulAddMonoidHom (k : ZMod m).val).ker = Nat.card {x // f x = 0} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x ↦ AddMonoidHom.mem_ker)
  rw [← hker, h0, Nat.card_eq_fintype_card, Fintype.card_subtype, Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  convert hfib using 2
  ext x; simp [hf]

/-- **Theorem 69** [hardywright2008] (a general principle, § 5.7): let `P` be a property of
non-negative integers such that `P(a)` and `P(b)` imply `P(a + b)` and (for `b ≤ a`) `P(a - b)`,
and let `r` be the least positive integer with `P(r)`. Then (a) `P(kr)` holds for every `k ≥ 0`,
and (b) every `q` with `P(q)` is a multiple of `r`. -/
@[kb "hardywright2008" "Thm 69, p. 70"]
theorem general_principle (P : ℕ → Prop) (hadd : ∀ a b, P a → P b → P (a + b))
    (hsub : ∀ a b, b ≤ a → P a → P b → P (a - b)) {r : ℕ} (hr : 0 < r) (hPr : P r)
    (hmin : ∀ x, 0 < x → x < r → ¬P x) :
    (∀ k, P (k * r)) ∧ ∀ q, P q → r ∣ q := by
  have ha : ∀ k, P (k * r) := by
    intro k
    induction k with
    | zero => simpa using hsub r r le_rfl hPr hPr
    | succ k ih => rw [add_mul, one_mul]; exact hadd _ _ ih hPr
  refine ⟨ha, fun q hq ↦ ?_⟩
  -- `q = k r + s` with `0 ≤ s < r`, and `P(s) = P(q - k r)`
  have hs : P (q % r) := by
    have := hsub q (q / r * r) (Nat.div_mul_le_self q r) hq (ha _)
    rwa [show q - q / r * r = q % r by rw [Nat.mod_eq_sub_div_mul]] at this
  by_contra h
  exact hmin (q % r) (Nat.pos_of_ne_zero fun h0 ↦ h (Nat.dvd_of_mod_eq_zero h0))
    (Nat.mod_lt q hr) hs

/-- **Theorem 58** [hardywright2008]: if `a₁, …, a_φ(m)` is a complete set of residues prime to
`m` and `(k, m) = 1`, then `ka₁, …, ka_φ(m)` is also such a set. -/
@[kb "hardywright2008" "Thm 58, p. 63"]
theorem IsReducedResidueSystem.mul {m : ℕ} {a : ι → ℤ} (h : IsReducedResidueSystem m a)
    {k : ℤ} (hk : IsCoprime k m) : IsReducedResidueSystem m (fun i ↦ k * a i) := by
  have hu : IsUnit (k : ZMod m) := (ZMod.isUnit_intCast_iff_isCoprime _ _).2 hk.symm
  refine ⟨fun i ↦ hk.mul_left (h.1 i), fun i j hij ↦ h.2.1 ?_, fun x hx ↦ ?_⟩
  · simpa [hu.mul_right_inj] using hij
  · obtain ⟨i, hi⟩ := h.2.2 (hu.unit⁻¹ * x) ((Units.isUnit _).mul hx)
    exact ⟨i, by simp [hi, ← mul_assoc]⟩

/-- Reduction modulo a factor `m` of `m m'` of `a' m + a m'` is `a m'`. -/
private lemma cast_crt_left {m m' : ℕ} (a a' : ℤ) :
    ZMod.castHom (dvd_mul_right m m') (ZMod m) ((a' * m + a * m' : ℤ) : ZMod (m * m')) =
      (a : ZMod m) * m' := by
  simp

private lemma cast_crt_right {m m' : ℕ} (a a' : ℤ) :
    ZMod.castHom (dvd_mul_left m' m) (ZMod m') ((a' * m + a * m' : ℤ) : ZMod (m * m')) =
      (a' : ZMod m') * m := by
  simp

/-- The injectivity step common to Theorems 59 and 61: `a'₁ m + a₁ m' ≡ a'₂ m + a₂ m' (mod mm')`
implies `a₁ ≡ a₂ (mod m)` and `a'₁ ≡ a'₂ (mod m')`. -/
private lemma crt_injective {m m' : ℕ} (hmm' : m.Coprime m') {a : ι → ℤ} {a' : κ → ℤ}
    (ha : Function.Injective fun i ↦ (a i : ZMod m))
    (ha' : Function.Injective fun i ↦ (a' i : ZMod m')) :
    Function.Injective fun p : ι × κ ↦ ((a' p.2 * m + a p.1 * m' : ℤ) : ZMod (m * m')) := by
  rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h
  have h1 := congrArg (ZMod.castHom (dvd_mul_right m m') (ZMod m)) h
  have h2 := congrArg (ZMod.castHom (dvd_mul_left m' m) (ZMod m')) h
  simp only [cast_crt_left, cast_crt_right] at h1 h2
  have u1 : IsUnit (m' : ZMod m) := (ZMod.isUnit_iff_coprime _ _).2 hmm'.symm
  have u2 : IsUnit (m : ZMod m') := (ZMod.isUnit_iff_coprime _ _).2 hmm'
  rw [u1.mul_left_inj] at h1
  rw [u2.mul_left_inj] at h2
  rw [ha h1, ha' h2]

/-- **Theorem 59** [hardywright2008]: if `(m, m') = 1`, `a` runs through a complete set of
residues modulo `m` and `a'` through one modulo `m'`, then `a'm + am'` runs through a complete set
of residues modulo `mm'`. -/
@[kb "hardywright2008" "Thm 59, p. 63"]
theorem IsCompleteResidueSystem.crt {m m' : ℕ} [NeZero m] [NeZero m'] (hmm' : m.Coprime m')
    {a : ι → ℤ} {a' : κ → ℤ} (ha : IsCompleteResidueSystem m a)
    (ha' : IsCompleteResidueSystem m' a') :
    IsCompleteResidueSystem (m * m') (fun p : ι × κ ↦ a' p.2 * m + a p.1 * m') := by
  have := ha.finite
  have := ha'.finite
  -- there are `m m'` numbers `a'm + am'`, all incongruent
  refine (crt_injective hmm' ha.1 ha'.1).bijective_of_nat_card_le ?_
  rw [Nat.card_zmod, Nat.card_prod, ha.card, ha'.card]

/-- **Theorem 61** [hardywright2008]: if `(m, m') = 1`, `a` runs through a complete set of
residues prime to `m` and `a'` through one prime to `m'`, then `am' + a'm` runs through a complete
set of residues prime to `mm'`. -/
@[kb "hardywright2008" "Thm 61, p. 64"]
theorem IsReducedResidueSystem.crt {m m' : ℕ} [NeZero m] [NeZero m'] (hmm' : m.Coprime m')
    {a : ι → ℤ} {a' : κ → ℤ} (ha : IsReducedResidueSystem m a)
    (ha' : IsReducedResidueSystem m' a') :
    IsReducedResidueSystem (m * m') (fun p : ι × κ ↦ a' p.2 * m + a p.1 * m') := by
  have hc : IsCoprime (m : ℤ) m' := Nat.isCoprime_iff_coprime.2 hmm'
  -- `(a'm + am', mm') = 1` since `(a, m) = 1` and `(a', m') = 1`
  have hcop : ∀ p : ι × κ, IsCoprime (a' p.2 * m + a p.1 * m') ((m * m' : ℕ) : ℤ) := by
    intro p
    push_cast
    refine IsCoprime.mul_right ?_ ?_
    · have : IsCoprime (a p.1 * m') m := (ha.1 p.1).mul_left hc.symm
      simpa [add_comm, mul_comm] using this.add_mul_left_left (a' p.2)
    · have : IsCoprime (a' p.2 * m) m' := (ha'.1 p.2).mul_left hc
      simpa [mul_comm] using this.add_mul_left_left (a p.1)
  have hinj := crt_injective hmm' ha.2.1 ha'.2.1
  refine ⟨hcop, hinj, ?_⟩
  -- the `φ(m) φ(m') = φ(mm')` values are units and pairwise incongruent, so they are all the units
  have hfin : Finite ι := Finite.of_injective _ ha.2.1
  have hfin' : Finite κ := Finite.of_injective _ ha'.2.1
  have hu : ∀ p : ι × κ, IsUnit ((a' p.2 * m + a p.1 * m' : ℤ) : ZMod (m * m')) := fun p ↦
    (ZMod.isUnit_intCast_iff_isCoprime _ _).2 (hcop p).symm
  have hbij : Function.Bijective fun p : ι × κ ↦ (hu p).unit := by
    refine Function.Injective.bijective_of_nat_card_le
      (fun p q hpq ↦ hinj (congrArg Units.val hpq)) ?_
    rw [Nat.card_prod, ha.card, ha'.card, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_mul hmm']
  intro x hx
  obtain ⟨p, hp⟩ := hbij.2 hx.unit
  exact ⟨p, by simpa using congrArg Units.val hp⟩

end NTKB.HardyWright
