/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import NTKB.Elementary.HardyWright.Residues.Basic

/-!
# Multiplicativity of Gauss's, Ramanujan's and Kloosterman's sums (Hardy–Wright, § 5.6)

With `e(r) = exp(2πir)`, Hardy and Wright define

* Gauss's sum `S(m, n) = ∑_{h=0}^{n-1} e(h² m / n)` (`NTKB.HardyWright.gaussQuadSum`);
* Ramanujan's sum `c_q(m) = ∑_{h* (q)} e(h m / q)`, `h` running through residues prime to `q`
  (`NTKB.HardyWright.ramanujanSum`);
* Kloosterman's sum `S(u, v, n) = ∑_{h* (n)} e((u h + v h̄) / n)` with `h h̄ ≡ 1 (mod n)`
  (`NTKB.HardyWright.kloostermanSum`);

taking for `h` the least non-negative residues, and prove (Theorems 64, 67, 68) that they are
multiplicative in the stated senses, by Theorems 59 and 61 (`IsCompleteResidueSystem.crt`,
`IsReducedResidueSystem.crt`). The book's notation `∑_{h (n)}` (any complete system) is justified
by `gaussQuadSum_eq_sum_completeResidueSystem` and its analogues.

Mathlib's `gaussSum χ ψ` is the Gauss sum of a multiplicative character, a different object.
-/

open Complex Finset
open scoped Real

namespace NTKB.HardyWright

variable {ι κ : Type*}

section sums

variable {M : Type*} [AddCommMonoid M] {n : ℕ} [NeZero n]

/-- A function of the residue class summed over a complete residue system. -/
theorem IsCompleteResidueSystem.sum_eq [Fintype ι] {a : ι → ℤ}
    (ha : IsCompleteResidueSystem n a) (G : ZMod n → M) : ∑ i, G (a i) = ∑ x, G x :=
  ha.sum_comp G

/-- A function of the residue class summed over a complete set of residues prime to `n`. -/
theorem IsReducedResidueSystem.sum_eq [Fintype ι] {a : ι → ℤ}
    (ha : IsReducedResidueSystem n a) (G : ZMod n → M) :
    ∑ i, G (a i) = ∑ u : (ZMod n)ˣ, G u := by
  obtain ⟨hu, hb⟩ := isReducedResidueSystem_iff.1 ha
  rw [← hb.sum_comp (fun u : (ZMod n)ˣ ↦ G u)]
  simp

variable (n) in
/-- The representatives `x.val` of the classes `x : ZMod n` form a complete system. -/
theorem isCompleteResidueSystem_val : IsCompleteResidueSystem n (fun x : ZMod n ↦ (x.val : ℤ)) := by
  have : (fun x : ZMod n ↦ (((x.val : ℤ)) : ZMod n)) = id := by ext x; simp
  rw [IsCompleteResidueSystem, this]
  exact Function.bijective_id

variable (n) in
/-- The representatives `u.val` of the units `u` of `ZMod n` form a complete set of residues prime
to `n`. -/
theorem isReducedResidueSystem_val :
    IsReducedResidueSystem n (fun u : (ZMod n)ˣ ↦ ((u : ZMod n).val : ℤ)) := by
  refine isReducedResidueSystem_iff.2 ⟨fun u ↦ by simp, fun u v huv ↦ ?_, fun u ↦ ⟨u, ?_⟩⟩
  · exact Units.ext (by simpa using congrArg Units.val huv)
  · exact Units.ext (by simp)

variable (n) in
theorem sum_range_eq_sum_zmod (G : ZMod n → M) : ∑ h ∈ range n, G h = ∑ x, G x := by
  rw [← Fin.sum_univ_eq_sum_range (fun h ↦ G h), ← (isCompleteResidueSystem_range n).sum_eq G]
  simp

variable (n) in
theorem sum_range_coprime_eq_sum_units (G : ZMod n → M) :
    ∑ h ∈ range n with h.Coprime n, G h = ∑ u : (ZMod n)ˣ, G u := by
  rw [← Finset.sum_coe_sort]
  have hred : IsReducedResidueSystem n
      (fun h : {h // h ∈ (range n).filter (·.Coprime n)} ↦ ((h : ℕ) : ℤ)) := by
    refine ⟨fun h ↦ ?_, fun h k hhk ↦ ?_, fun x hx ↦ ?_⟩
    · exact Nat.isCoprime_iff_coprime.2 (Finset.mem_filter.1 h.2).2
    · have h1 := (Finset.mem_filter.1 h.2).1
      have h2 := (Finset.mem_filter.1 k.2).1
      rw [Finset.mem_range] at h1 h2
      simp only [Int.cast_natCast] at hhk
      exact Subtype.ext (by rw [← ZMod.val_natCast_of_lt h1, ← ZMod.val_natCast_of_lt h2, hhk])
    · refine ⟨⟨x.val, Finset.mem_filter.2 ⟨Finset.mem_range.2 (ZMod.val_lt x), ?_⟩⟩, by simp⟩
      simpa using ZMod.val_coe_unit_coprime hx.unit
  simpa using hred.sum_eq G

end sums

/-! ### The character `e(x / N)` -/

/-- `e(x/N)` for an integer `x`, as Mathlib's standard additive character of `ZMod N`. -/
lemma exp_eq_stdAddChar (N : ℕ) [NeZero N] (x : ℤ) :
    exp (2 * π * I * x / N) = ZMod.stdAddChar (x : ZMod N) :=
  (ZMod.stdAddChar_coe x).symm

/-- `e((A n' + B n + C n n') / (n n')) = e(A / n) e(B / n')`. -/
lemma stdAddChar_crt (n n' : ℕ) [NeZero n] [NeZero n'] (A B C : ℤ) :
    ZMod.stdAddChar (N := n * n') ((A * n' + B * n + C * (n * n') : ℤ)) =
      ZMod.stdAddChar (A : ZMod n) * ZMod.stdAddChar (B : ZMod n') := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  have hn' : (n' : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n')
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ← exp_add]
  have : 2 * π * I * ((A * n' + B * n + C * (n * n') : ℤ) : ℂ) / ((n * n' : ℕ) : ℂ) =
      (2 * π * I * A / n + 2 * π * I * B / n') + C * (2 * π * I) := by
    push_cast
    field_simp
  rw [this, exp_add, exp_int_mul_two_pi_mul_I, mul_one]

/-! ### Gauss's sum -/

/-- Gauss's sum `S(m, n) = ∑_{h=0}^{n-1} e(h² m / n)` [hardywright2008, § 5.6 (1)]. -/
noncomputable def gaussQuadSum (m : ℤ) (n : ℕ) : ℂ :=
  ∑ h ∈ range n, exp (2 * π * I * ((h : ℂ) ^ 2 * m) / n)

lemma gaussQuadSum_eq_sum_zmod (m : ℤ) (n : ℕ) [NeZero n] :
    gaussQuadSum m n = ∑ x : ZMod n, ZMod.stdAddChar ((m : ZMod n) * x ^ 2) := by
  rw [gaussQuadSum, ← sum_range_eq_sum_zmod]
  refine Finset.sum_congr rfl fun h _ ↦ ?_
  rw [show (m : ZMod n) * (h : ZMod n) ^ 2 = (((h : ℤ) ^ 2 * m : ℤ) : ZMod n) by push_cast; ring,
    ← exp_eq_stdAddChar]
  push_cast
  rfl

/-- `S(m, n) = ∑_{h (n)} e(h² m / n)` for any complete residue system `h` modulo `n`. -/
theorem gaussQuadSum_eq_sum_completeResidueSystem (m : ℤ) (n : ℕ) [NeZero n] [Fintype ι]
    {a : ι → ℤ} (ha : IsCompleteResidueSystem n a) :
    gaussQuadSum m n = ∑ i, exp (2 * π * I * ((a i : ℂ) ^ 2 * m) / n) := by
  rw [gaussQuadSum_eq_sum_zmod, ← ha.sum_eq]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [show (m : ZMod n) * (a i : ZMod n) ^ 2 = ((a i ^ 2 * m : ℤ) : ZMod n) by push_cast; ring,
    ← exp_eq_stdAddChar]
  push_cast
  rfl

/-- **Theorem 64** [hardywright2008]: if `(n, n') = 1`, then `S(m, nn') = S(mn', n) S(mn, n')`. -/
@[kb "hardywright2008" "Thm 64, p. 66"]
theorem gaussQuadSum_mul (m : ℤ) {n n' : ℕ} [NeZero n] [NeZero n'] (hnn' : n.Coprime n') :
    gaussQuadSum m (n * n') = gaussQuadSum (m * n') n * gaussQuadSum (m * n) n' := by
  -- `H = h n' + h' n` runs through a complete system modulo `n n'` (Theorem 59)
  have hH := (isCompleteResidueSystem_val n).crt hnn' (isCompleteResidueSystem_val n')
  rw [gaussQuadSum_eq_sum_zmod, ← hH.sum_eq, gaussQuadSum_eq_sum_zmod, gaussQuadSum_eq_sum_zmod,
    Finset.sum_mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y _ ↦ ?_
  -- `m H² ≡ m h² n'² + m h'² n² (mod n n')`
  have : (m : ZMod (n * n')) * (((y.val : ℤ) * n + (x.val : ℤ) * n' : ℤ) : ZMod (n * n')) ^ 2 =
      (((m * n' * x.val ^ 2) * n' + (m * n * y.val ^ 2) * n + (2 * m * x.val * y.val) * (n * n')
        : ℤ) : ZMod (n * n')) := by
    push_cast; ring
  rw [this, stdAddChar_crt]
  simp

/-! ### Ramanujan's sum -/

/-- Ramanujan's sum `c_q(m) = ∑_{h* (q)} e(h m / q)`, `h` running through the residues prime to
`q` [hardywright2008, § 5.6 (2)]. -/
noncomputable def ramanujanSum (q : ℕ) (m : ℤ) : ℂ :=
  ∑ h ∈ range q with h.Coprime q, exp (2 * π * I * ((h : ℂ) * m) / q)

lemma ramanujanSum_eq_sum_units (q : ℕ) [NeZero q] (m : ℤ) :
    ramanujanSum q m = ∑ u : (ZMod q)ˣ, ZMod.stdAddChar ((u : ZMod q) * (m : ZMod q)) := by
  rw [ramanujanSum, ← sum_range_coprime_eq_sum_units q (fun x ↦ ZMod.stdAddChar (x * (m : ZMod q)))]
  refine Finset.sum_congr rfl fun h _ ↦ ?_
  rw [show (h : ZMod q) * (m : ZMod q) = (((h : ℤ) * m : ℤ) : ZMod q) by push_cast; ring,
    ← exp_eq_stdAddChar]
  push_cast
  rfl

/-- `c_q(m) = ∑_{h* (q)} e(h m / q)` for any complete set `h` of residues prime to `q`. -/
theorem ramanujanSum_eq_sum_reducedResidueSystem (q : ℕ) [NeZero q] (m : ℤ) [Fintype ι]
    {a : ι → ℤ} (ha : IsReducedResidueSystem q a) :
    ramanujanSum q m = ∑ i, exp (2 * π * I * ((a i : ℂ) * m) / q) := by
  rw [ramanujanSum_eq_sum_units, ← ha.sum_eq (fun x ↦ ZMod.stdAddChar (x * (m : ZMod q)))]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [show (a i : ZMod q) * (m : ZMod q) = ((a i * m : ℤ) : ZMod q) by push_cast; ring,
    ← exp_eq_stdAddChar]
  push_cast
  rfl

/-- **Theorem 67** [hardywright2008]: if `(q, q') = 1`, then `c_{qq'}(m) = c_q(m) c_{q'}(m)`. -/
@[kb "hardywright2008" "Thm 67, p. 68"]
theorem ramanujanSum_mul {q q' : ℕ} [NeZero q] [NeZero q'] (hqq' : q.Coprime q') (m : ℤ) :
    ramanujanSum (q * q') m = ramanujanSum q m * ramanujanSum q' m := by
  -- `h q' + h' q` runs through a complete set of residues prime to `q q'` (Theorem 61)
  have hH := (isReducedResidueSystem_val q).crt hqq' (isReducedResidueSystem_val q')
  rw [ramanujanSum_eq_sum_units,
    ← hH.sum_eq (fun x : ZMod (q * q') ↦ ZMod.stdAddChar (x * (m : ZMod (q * q')))),
    ramanujanSum_eq_sum_units, ramanujanSum_eq_sum_units, Finset.sum_mul_sum,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y _ ↦ ?_
  have : (((((y : ZMod q').val : ℤ) * q + ((x : ZMod q).val : ℤ) * q' : ℤ) : ZMod (q * q')) *
      (m : ZMod (q * q'))) = ((((x : ZMod q).val * m) * q' + ((y : ZMod q').val * m) * q +
        0 * (q * q') : ℤ) : ZMod (q * q')) := by
    push_cast; ring
  rw [this, stdAddChar_crt]
  simp

/-! ### Kloosterman's sum -/

/-- Kloosterman's sum `S(u, v, n) = ∑_{h* (n)} e((u h + v h̄) / n)`, `h` running through the
residues prime to `n` and `h h̄ ≡ 1 (mod n)` [hardywright2008, § 5.6 (3)]; here `h̄` is the least
non-negative such residue. -/
noncomputable def kloostermanSum (u v : ℤ) (n : ℕ) : ℂ :=
  ∑ h ∈ range n with h.Coprime n,
    exp (2 * π * I * ((u : ℂ) * h + v * (((h : ZMod n)⁻¹).val : ℂ)) / n)

lemma kloostermanSum_eq_sum_units (u v : ℤ) (n : ℕ) [NeZero n] :
    kloostermanSum u v n = ∑ x : (ZMod n)ˣ,
      ZMod.stdAddChar ((u : ZMod n) * (x : ZMod n) + (v : ZMod n) * (x : ZMod n)⁻¹) := by
  rw [kloostermanSum, ← sum_range_coprime_eq_sum_units n
    (fun x ↦ ZMod.stdAddChar ((u : ZMod n) * x + (v : ZMod n) * x⁻¹))]
  refine Finset.sum_congr rfl fun h _ ↦ ?_
  rw [show (u : ZMod n) * (h : ZMod n) + v * (h : ZMod n)⁻¹ =
      ((u * h + v * ((h : ZMod n)⁻¹).val : ℤ) : ZMod n) by push_cast; simp,
    ← exp_eq_stdAddChar]
  push_cast
  rfl

/-- `S(u, v, n) = ∑_{h* (n)} e((u h + v h̄) / n)` for any complete set `h` of residues prime to `n`
and any choice of `h̄` with `h h̄ ≡ 1 (mod n)`. -/
theorem kloostermanSum_eq_sum_reducedResidueSystem (u v : ℤ) (n : ℕ) [NeZero n] [Fintype ι]
    {a : ι → ℤ} (ha : IsReducedResidueSystem n a) (abar : ι → ℤ)
    (habar : ∀ i, a i * abar i ≡ 1 [ZMOD n]) :
    kloostermanSum u v n = ∑ i, exp (2 * π * I * ((u : ℂ) * a i + v * abar i) / n) := by
  rw [kloostermanSum_eq_sum_units, ← ha.sum_eq
    (fun x ↦ ZMod.stdAddChar ((u : ZMod n) * x + (v : ZMod n) * x⁻¹))]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hinv : (a i : ZMod n)⁻¹ = (abar i : ZMod n) := by
    have h1 : (a i : ZMod n) * abar i = 1 := by
      exact_mod_cast (ZMod.intCast_eq_intCast_iff _ _ _).2 (habar i)
    exact ZMod.inv_eq_of_mul_eq_one n _ _ h1
  rw [hinv, show (u : ZMod n) * (a i : ZMod n) + v * (abar i : ZMod n) =
      ((u * a i + v * abar i : ℤ) : ZMod n) by push_cast; ring, ← exp_eq_stdAddChar]
  push_cast
  rfl

/-- **Theorem 68** [hardywright2008]: if `(n, n') = 1`, then
`S(u, v, n) S(u, v', n') = S(u, V, nn')` with `V = v n'² + v' n²`. -/
@[kb "hardywright2008" "Thm 68, p. 68"]
theorem kloostermanSum_mul (u v v' : ℤ) {n n' : ℕ} [NeZero n] [NeZero n'] (hnn' : n.Coprime n') :
    kloostermanSum u v n * kloostermanSum u v' n' =
      kloostermanSum u (v * n' ^ 2 + v' * n ^ 2) (n * n') := by
  -- `H = h n' + h' n` runs through a complete set of residues prime to `n n'` (Theorem 61)
  have hH := (isReducedResidueSystem_val n).crt hnn' (isReducedResidueSystem_val n')
  set V : ℤ := v * n' ^ 2 + v' * n ^ 2 with hV
  rw [kloostermanSum_eq_sum_units, kloostermanSum_eq_sum_units, kloostermanSum_eq_sum_units,
    ← hH.sum_eq (fun x : ZMod (n * n') ↦
      ZMod.stdAddChar ((u : ZMod (n * n')) * x + (V : ZMod (n * n')) * x⁻¹)),
    Finset.sum_mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y _ ↦ ?_
  -- integer representatives `h, h'` and their inverses `h̄, h̄'`
  set h : ℤ := ((x : ZMod n).val : ℤ) with hh
  set h' : ℤ := ((y : ZMod n').val : ℤ) with hh'
  set hb : ℤ := (((x⁻¹ : (ZMod n)ˣ) : ZMod n).val : ℤ) with hhb
  set hb' : ℤ := (((y⁻¹ : (ZMod n')ˣ) : ZMod n').val : ℤ) with hhb'
  obtain ⟨t, ht⟩ : (n : ℤ) ∣ h * hb - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp [h, hb]
  obtain ⟨t', ht'⟩ : (n' : ℤ) ∣ h' * hb' - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp [h', hb']
  -- (5.6.2): `K ≡ V H̄ (mod n n')` with `K = v h̄ n' + v' h̄' n`
  have hK : ((h' * n + h * n' : ℤ) : ZMod (n * n'))⁻¹ * V =
      ((v * hb * n' + v' * hb' * n : ℤ) : ZMod (n * n')) := by
    have hu : IsUnit ((h' * n + h * n' : ℤ) : ZMod (n * n')) := hH.isUnit (x, y)
    rw [← hu.mul_right_inj, ← mul_assoc, ZMod.mul_inv_of_unit _ hu, one_mul]
    have : (h' * n + h * n') * (v * hb * n' + v' * hb' * n) =
        V + (v * hb * h' + v' * hb' * h + v * n' * t + v' * n * t') * (n * n') := by
      rw [hV]
      linear_combination (v * n' ^ 2) * ht + (v' * n ^ 2) * ht'
    rw [← Int.cast_mul, this]
    have h0 : ((n : ZMod (n * n')) * n') = 0 := by exact_mod_cast ZMod.natCast_self (n * n')
    push_cast
    rw [h0, mul_zero, add_zero]
  rw [mul_comm (V : ZMod (n * n')), hK]
  have : (u : ZMod (n * n')) * ((h' * n + h * n' : ℤ) : ZMod (n * n')) +
      ((v * hb * n' + v' * hb' * n : ℤ) : ZMod (n * n')) =
      (((u * h + v * hb) * n' + (u * h' + v' * hb') * n + 0 * (n * n') : ℤ) :
        ZMod (n * n')) := by
    push_cast; ring
  rw [this, stdAddChar_crt]
  simp [h, h', hb, hb']

end NTKB.HardyWright
