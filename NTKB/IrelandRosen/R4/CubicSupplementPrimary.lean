/- Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license. -/
import NTKB.Attr
import NTKB.IrelandRosen.R4.CubicReciprocity

/-!
# The supplement to cubic reciprocity for every primary prime

This file proves `χ_π(1 - ω) = ω^{2m}` for every primary prime `π` of `ℤ[ω]` with real part
`3m - 1` (`cubicChar_one_sub_omega_of_isPrimary`), together with `χ_π(ω)` for primary primes
(`cubicChar_omega_primary`).

Copied from the library's historical formalizations (not published; `cubicChar_jacobi_recip` and its
lemmas, and the supplement), renamed into the namespace `NTKB.IrelandRosen.CubicSupplement`; statements unchanged.

Route: reciprocity for cubic Jacobi symbols gives, together with the rational case of the
supplement, the value of `χ_π(1 - ω)` for a prime `π` of prime norm; the inert case is the rational
case `cubicChar_natCast_one_sub_omega`.
-/

set_option autoImplicit false

namespace NTKB.IrelandRosen.CubicSupplement

open NTKB.IrelandRosen NTKB.IrelandRosen.Eisenstein NTKB.HardyWright
open QuadraticAlgebra hiding omega

local notation "ℤ[ω]" => NTKB.HardyWright.ZRho
local notation "ωE" => NTKB.IrelandRosen.Eisenstein.omega

lemma three_dvd_iff_zrho (x : ℤ[ω]) : (3 : ℤ[ω]) ∣ x ↔ 3 ∣ x.re ∧ 3 ∣ x.im := by
  have := intCast_dvd_iff 3 x
  rwa [Int.cast_ofNat] at this

lemma natAbs_norm_ne_three_of_dvd {π x : ℤ[ω]} (hπ : Prime π) (hdx : π ∣ x)
    (h : (3 : ℤ[ω]) ∣ x - 1 ∨ (3 : ℤ[ω]) ∣ x + 1) : (norm π).natAbs ≠ 3 := by
  apply (natAbs_norm_ne_three_iff hπ).2
  intro h3π
  have h1 : π ∣ 1 := by
    rcases h with h | h
    · have := dvd_sub hdx (h3π.trans h)
      simpa using this
    · have := dvd_sub (h3π.trans h) hdx
      simpa using this
  exact hπ.not_isUnit (isUnit_of_dvd_one h1)

lemma natAbs_norm_ne_three_of_not_dvd {π : ℤ[ω]} (hπ : Prime π) (h : ¬ π ∣ 1 - ωE) :
    (norm π).natAbs ≠ 3 := by
  apply (natAbs_norm_ne_three_iff hπ).2
  intro h3
  rw [three_eq_and_prime_one_sub_omega.1] at h3
  rcases hπ.dvd_or_dvd h3 with h4 | h4
  · exact hπ.not_isUnit (isUnit_of_dvd_unit h4 (isUnit_omega.pow 2).neg)
  · exact h (hπ.dvd_of_dvd_pow h4)

lemma eq_pm_one_of_isUnit {V : ℤ[ω]} (hV : IsUnit V)
    (h : (3 : ℤ[ω]) ∣ V - 1 ∨ (3 : ℤ[ω]) ∣ V + 1) : V = 1 ∨ V = -1 := by
  rcases isUnit_iff_eq.1 hV with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  all_goals
    exfalso
    rcases h with h | h <;> (try simp only [omega_sq_eq] at h) <;> rw [three_dvd_iff_zrho] at h <;>
      simp [NTKB.IrelandRosen.Eisenstein.omega] at h

lemma three_dvd_unit_of_prod {V P : ℤ[ω]} (h1 : (3 : ℤ[ω]) ∣ P - 1 ∨ (3 : ℤ[ω]) ∣ P + 1)
    (h2 : (3 : ℤ[ω]) ∣ V * P - 1 ∨ (3 : ℤ[ω]) ∣ V * P + 1) :
    (3 : ℤ[ω]) ∣ V - 1 ∨ (3 : ℤ[ω]) ∣ V + 1 := by
  obtain ⟨a, ha, ha'⟩ : ∃ a : ℤ[ω], (a = 1 ∨ a = -1) ∧ (3 : ℤ[ω]) ∣ P - a := by
    rcases h1 with h | h
    · exact ⟨1, Or.inl rfl, h⟩
    · exact ⟨-1, Or.inr rfl, by simpa [sub_neg_eq_add] using h⟩
  obtain ⟨b, hb, hb'⟩ : ∃ b : ℤ[ω], (b = 1 ∨ b = -1) ∧ (3 : ℤ[ω]) ∣ V * P - b := by
    rcases h2 with h | h
    · exact ⟨1, Or.inl rfl, h⟩
    · exact ⟨-1, Or.inr rfl, by simpa [sub_neg_eq_add] using h⟩
  have ha2 : a * a = 1 := by rcases ha with rfl | rfl <;> ring
  have e1 : V - b * a = V * (-(P - a) * (P + a)) + (V * P - b) * P + b * (P - a) := by
    linear_combination (-V) * ha2
  have h3 : (3 : ℤ[ω]) ∣ V - b * a := by
    rw [e1]
    exact dvd_add (dvd_add (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left ha'.neg_right _) _)
      (dvd_mul_of_dvd_left hb' _)) (dvd_mul_of_dvd_right ha' _)
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · left; simpa using h3
  · right; simpa [sub_neg_eq_add] using h3
  · right; simpa [sub_neg_eq_add] using h3
  · left; simpa using h3

lemma cubicChar_pm_one_mul {π ε x : ℤ[ω]} (hπ : Prime π) (h3 : (norm π).natAbs ≠ 3)
    (hε : ε = 1 ∨ ε = -1) : cubicChar π (ε * x) = cubicChar π x := by
  rcases hε with rfl | rfl
  · rw [one_mul]
  · rw [cubicChar_mul hπ h3, cubicChar_neg_one hπ h3, one_mul]

lemma associated_unit_mul {π v : ℤ[ω]} (hv : IsUnit v) : Associated π (v * π) := by
  obtain ⟨u, rfl⟩ := hv
  exact ⟨u, mul_comm _ _⟩

lemma cubicChar_recip_primary {π π' v v' : ℤ[ω]} (hπ : Prime π) (hπ' : Prime π')
    (hv : IsUnit v) (hv' : IsUnit v') (hP : IsPrimary (v * π)) (hP' : IsPrimary (v' * π'))
    (hN : (norm π).natAbs ≠ (norm π').natAbs) :
    cubicChar π' (v * π) = cubicChar π (v' * π') := by
  have a1 := associated_unit_mul (π := π) hv
  have a2 := associated_unit_mul (π := π') hv'
  have hrec := cubic_reciprocity (a2.prime_iff.1 hπ') (a1.prime_iff.1 hπ) hP' hP (by
    rw [← natAbs_norm_eq_of_associated a1, ← natAbs_norm_eq_of_associated a2]; exact hN.symm)
  calc cubicChar π' (v * π) = cubicChar (v' * π') (v * π) := by rw [cubicChar_of_associated a2]
    _ = cubicChar (v * π) (v' * π') := hrec
    _ = cubicChar π (v' * π') := by rw [cubicChar_of_associated a1]

lemma cubicChar_list_prod {π : ℤ[ω]} (hπ : Prime π) (h3 : (norm π).natAbs ≠ 3)
    (L : List ℤ[ω]) : cubicChar π L.prod = (L.map (cubicChar π)).prod := by
  induction L with
  | nil => simp [cubicChar_one hπ h3]
  | cons a L ih => simp [cubicChar_mul hπ h3, ih]

lemma three_dvd_prod_of_primary (L : List ℤ[ω]) (h : ∀ x ∈ L, IsPrimary x) :
    (3 : ℤ[ω]) ∣ L.prod - 1 ∨ (3 : ℤ[ω]) ∣ L.prod + 1 := by
  induction L with
  | nil => left; simp
  | cons x L ih =>
    have hx : (3 : ℤ[ω]) ∣ x + 1 := by
      have := h x (by simp)
      have e : x + 1 = (x - 2) + 3 := by ring
      rw [e]; exact dvd_add this dvd_rfl
    rcases ih (fun y hy => h y (by simp [hy])) with h1 | h1
    · right
      have e : (x :: L).prod + 1 = (x + 1) * L.prod - (L.prod - 1) := by
        rw [List.prod_cons]; ring
      rw [e]; exact dvd_sub (dvd_mul_of_dvd_left hx _) h1
    · left
      have e : (x :: L).prod - 1 = (x + 1) * L.prod - (L.prod + 1) := by
        rw [List.prod_cons]; ring
      rw [e]; exact dvd_sub (dvd_mul_of_dvd_left hx _) h1

lemma exists_unit_fn : ∃ v : ℤ[ω] → ℤ[ω], ∀ x, Prime x → (norm x).natAbs ≠ 3 →
    IsUnit (v x) ∧ IsPrimary (v x * x) := by
  have : ∀ x : ℤ[ω], ∃ w, Prime x → (norm x).natAbs ≠ 3 → IsUnit w ∧ IsPrimary (w * x) := by
    intro x
    by_cases h : Prime x ∧ (norm x).natAbs ≠ 3
    · obtain ⟨u, hu, -⟩ := existsUnique_isPrimary_unit_mul h.1 h.2
      exact ⟨u, fun _ _ => ⟨u.isUnit, hu⟩⟩
    · exact ⟨1, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose v hv using this
  exact ⟨v, hv⟩

lemma list_prod_swap {α β M : Type*} [CommMonoid M] (f : α → β → M) (xs : List α) (ys : List β) :
    (ys.map fun y => (xs.map fun x => f x y).prod).prod =
      (xs.map fun x => (ys.map fun y => f x y).prod).prod := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [List.prod_map_mul, ih]

lemma cubicChar_symm_of_pm_one {π π' : ℤ[ω]} (hπ : Prime π) (hπ' : Prime π')
    (h1 : (3 : ℤ[ω]) ∣ π - 1 ∨ (3 : ℤ[ω]) ∣ π + 1)
    (h2 : (3 : ℤ[ω]) ∣ π' - 1 ∨ (3 : ℤ[ω]) ∣ π' + 1)
    (hN : (norm π).natAbs ≠ (norm π').natAbs) : cubicChar π' π = cubicChar π π' := by
  have prim : ∀ x : ℤ[ω], ((3 : ℤ[ω]) ∣ x - 1 ∨ (3 : ℤ[ω]) ∣ x + 1) →
      ∃ ε : ℤ[ω], (ε = 1 ∨ ε = -1) ∧ IsUnit ε ∧ IsPrimary (ε * x) := by
    intro x h
    rcases h with h | h
    · refine ⟨-1, Or.inr rfl, isUnit_one.neg, ?_⟩
      have e : (-1 : ℤ[ω]) * x - 2 = -(x - 1) - 3 := by ring
      unfold IsPrimary; rw [e]; exact dvd_sub h.neg_right dvd_rfl
    · refine ⟨1, Or.inl rfl, isUnit_one, ?_⟩
      have e : (1 : ℤ[ω]) * x - 2 = (x + 1) - 3 := by ring
      unfold IsPrimary; rw [e]; exact dvd_sub h dvd_rfl
  obtain ⟨ε, hε, hu, hP⟩ := prim π h1
  obtain ⟨ε', hε', hu', hP'⟩ := prim π' h2
  have h3 := natAbs_norm_ne_three_of_dvd hπ dvd_rfl h1
  have h3' := natAbs_norm_ne_three_of_dvd hπ' dvd_rfl h2
  calc cubicChar π' π = cubicChar π' (ε * π) := (cubicChar_pm_one_mul hπ' h3' hε).symm
    _ = cubicChar π (ε' * π') := cubicChar_recip_primary hπ hπ' hu hu' hP hP' hN
    _ = cubicChar π π' := cubicChar_pm_one_mul hπ h3 hε'

lemma cubicChar_prod_eq (v : ℤ[ω] → ℤ[ω])
    (hv : ∀ x, Prime x → (norm x).natAbs ≠ 3 → IsUnit (v x) ∧ IsPrimary (v x * x))
    (M : List ℤ[ω]) (hM : ∀ x ∈ M, Prime x)
    (hM1 : (3 : ℤ[ω]) ∣ M.prod - 1 ∨ (3 : ℤ[ω]) ∣ M.prod + 1) {π : ℤ[ω]} (hπ : Prime π)
    (h3 : (norm π).natAbs ≠ 3) :
    cubicChar π M.prod = (M.map fun m => cubicChar π (v m * m)).prod := by
  have h3M : ∀ m ∈ M, (norm m).natAbs ≠ 3 := fun m hx =>
    natAbs_norm_ne_three_of_dvd (hM m hx) (List.dvd_prod hx) hM1
  have hWprim : (3 : ℤ[ω]) ∣ (M.map fun m => v m * m).prod - 1 ∨
      (3 : ℤ[ω]) ∣ (M.map fun m => v m * m).prod + 1 := by
    apply three_dvd_prod_of_primary
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨m, hm, rfl⟩ := hx
    exact (hv m (hM m hm) (h3M m hm)).2
  have hWeq : (M.map fun m => v m * m).prod = (M.map v).prod * M.prod := by
    rw [List.prod_map_mul]; simp
  have hVunit : IsUnit (M.map v).prod := by
    have key : ∀ N : List ℤ[ω], (∀ m ∈ N, Prime m) → (∀ m ∈ N, (norm m).natAbs ≠ 3) →
        IsUnit (N.map v).prod := by
      intro N
      induction N with
      | nil => intro _ _; simp
      | cons a N ih =>
        intro h h'
        rw [List.map_cons, List.prod_cons]
        exact (hv a (h a (by simp)) (h' a (by simp))).1.mul
          (ih (fun m hm => h m (by simp [hm])) (fun m hm => h' m (by simp [hm])))
    exact key M hM h3M
  have hVpm := eq_pm_one_of_isUnit hVunit (three_dvd_unit_of_prod hM1 (hWeq ▸ hWprim))
  rw [← cubicChar_pm_one_mul hπ h3 hVpm, ← hWeq, cubicChar_list_prod hπ h3, List.map_map]
  rfl

lemma not_dvd_prod_of_coprime {ls ls' : List ℤ[ω]} (hl' : ∀ x ∈ ls', Prime x)
    (hc : Nat.Coprime (norm ls.prod).natAbs (norm ls'.prod).natAbs) {l' : ℤ[ω]} (hx : l' ∈ ls') :
    ¬ l' ∣ ls.prod := by
  intro hd
  have d1 := natAbs_norm_dvd hd
  have d2 := natAbs_norm_dvd (List.dvd_prod hx)
  have := Nat.dvd_gcd d1 d2
  rw [hc.gcd_eq_one] at this
  exact (hl' l' hx).not_isUnit (isUnit_of_natAbs_norm_eq_one (Nat.dvd_one.1 this))

lemma not_dvd_of_norm_ne {π π' : ℤ[ω]} (hπ : Prime π) (hπ' : Prime π')
    (hN : (norm π').natAbs ≠ (norm π).natAbs) : ¬ π' ∣ π := by
  rintro ⟨c, rfl⟩
  rcases hπ.irreducible.isUnit_or_isUnit rfl with h | h
  · exact hπ'.not_isUnit h
  · have : Associated (π' * c) π' := ⟨h.unit⁻¹, by rw [mul_assoc]; simp⟩
    exact hN (natAbs_norm_eq_of_associated this).symm

/-- Reciprocity for cubic Jacobi symbols in `ℤ[ω]`. -/
theorem cubicChar_jacobi_recip (ls ls' : List ℤ[ω]) (hl : ∀ x ∈ ls, Prime x)
    (hl' : ∀ x ∈ ls', Prime x) (h1 : (3 : ℤ[ω]) ∣ ls.prod - 1 ∨ (3 : ℤ[ω]) ∣ ls.prod + 1)
    (h2 : (3 : ℤ[ω]) ∣ ls'.prod - 1 ∨ (3 : ℤ[ω]) ∣ ls'.prod + 1)
    (hc : Nat.Coprime (norm ls.prod).natAbs (norm ls'.prod).natAbs) :
    (ls'.map fun l' => cubicChar l' ls.prod).prod =
      (ls.map fun l => cubicChar l ls'.prod).prod := by
  obtain ⟨v, hv⟩ := exists_unit_fn
  have h3 : ∀ l ∈ ls, (norm l).natAbs ≠ 3 := fun l hx =>
    natAbs_norm_ne_three_of_dvd (hl l hx) (List.dvd_prod hx) h1
  have h3' : ∀ l ∈ ls', (norm l).natAbs ≠ 3 := fun l hx =>
    natAbs_norm_ne_three_of_dvd (hl' l hx) (List.dvd_prod hx) h2
  have hN : ∀ l ∈ ls, ∀ l' ∈ ls', (norm l).natAbs ≠ (norm l').natAbs := by
    intro l hx l' hx' heq
    have d1 : (norm l).natAbs ∣ (norm ls.prod).natAbs := natAbs_norm_dvd (List.dvd_prod hx)
    have d2 : (norm l).natAbs ∣ (norm ls'.prod).natAbs :=
      heq ▸ natAbs_norm_dvd (List.dvd_prod hx')
    have := Nat.dvd_gcd d1 d2
    rw [hc.gcd_eq_one] at this
    exact (hl l hx).not_isUnit (isUnit_of_natAbs_norm_eq_one (Nat.dvd_one.1 this))
  have L : (ls'.map fun l' => cubicChar l' ls.prod) =
      ls'.map fun l' => (ls.map fun l => cubicChar l' (v l * l)).prod :=
    List.map_congr_left fun l' hx' => cubicChar_prod_eq v hv ls hl h1 (hl' l' hx') (h3' l' hx')
  have R : (ls.map fun l => cubicChar l ls'.prod) =
      ls.map fun l => (ls'.map fun l' => cubicChar l (v l' * l')).prod :=
    List.map_congr_left fun l hx => cubicChar_prod_eq v hv ls' hl' h2 (hl l hx) (h3 l hx)
  rw [L, R, list_prod_swap (fun l l' => cubicChar l' (v l * l)) ls ls']
  congr 1
  refine List.map_congr_left fun l hx => ?_
  congr 1
  refine List.map_congr_left fun l' hx' => ?_
  exact cubicChar_recip_primary (hl l hx) (hl' l' hx') (hv l (hl l hx) (h3 l hx)).1
    (hv l' (hl' l' hx') (h3' l' hx')).1 (hv l (hl l hx) (h3 l hx)).2
    (hv l' (hl' l' hx') (h3' l' hx')).2 (hN l hx l' hx')

/-! ### Powers of `ω` with integer exponents read mod 3 -/

/-- `ω ^ k` for an integer exponent, read modulo `3`. -/
noncomputable def opow (k : ℤ) : ℤ[ω] := omega ^ (k % 3).toNat

lemma omega_pow_mod (n : ℕ) : omega ^ n = omega ^ (n % 3) := by
  conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, omega_cube, one_pow, one_mul]

lemma opow_natCast (n : ℕ) : opow n = omega ^ n := by
  unfold opow
  rw [omega_pow_mod n]
  congr 1

lemma opow_zero : opow 0 = 1 := by simp [opow]

lemma opow_congr {x y : ℤ} (h : x % 3 = y % 3) : opow x = opow y := by
  unfold opow; rw [h]

lemma opow_add (x y : ℤ) : opow (x + y) = opow x * opow y := by
  unfold opow
  rw [← pow_add, omega_pow_mod ((x % 3).toNat + (y % 3).toNat)]
  congr 1
  omega

lemma opow_pow (n : ℕ) (x : ℤ) : opow x ^ n = opow (n * x) := by
  induction n with
  | zero => simp [opow_zero]
  | succ n ih => rw [pow_succ, ih, ← opow_add]; congr 1; push_cast; ring

lemma opow_cube (x : ℤ) : opow x ^ 3 = 1 := by
  rw [opow_pow, show ((3 : ℕ) : ℤ) * x = 3 * x from rfl]
  rw [opow_congr (x := 3 * x) (y := 0) (by omega), opow_zero]

lemma opow_eq_iff {x y : ℤ} : opow x = opow y ↔ x % 3 = y % 3 := by
  refine ⟨fun h => ?_, opow_congr⟩
  unfold opow at h
  have h1 : ((x % 3).toNat : ℕ) < 3 := by omega
  have h2 : ((y % 3).toNat : ℕ) < 3 := by omega
  have := omega_pow_inj (i := ⟨_, h1⟩) (j := ⟨_, h2⟩) h
  have h3 := congrArg Fin.val this
  simp only at h3
  omega

lemma exists_opow {u : ℤ[ω]} (hu : u ^ 3 = 1) : ∃ x : ℤ, u = opow x := by
  rcases pow_three_eq_one_iff.1 hu with rfl | rfl | rfl
  · exact ⟨0, opow_zero.symm⟩
  · exact ⟨1, by rw [← Nat.cast_one, opow_natCast, pow_one]⟩
  · exact ⟨2, by rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, opow_natCast]⟩

/-! ### Cubic Jacobi symbols for lists of primes -/

/-- The cubic Jacobi symbol for a list of moduli. -/
noncomputable def jac (ls : List ℤ[ω]) (α : ℤ[ω]) : ℤ[ω] := (ls.map fun ρ => cubicChar ρ α).prod

/-- A list of primes none of which has norm `3`. -/
def GoodList (ls : List ℤ[ω]) : Prop := ∀ x ∈ ls, Prime x ∧ (norm x).natAbs ≠ 3

lemma jac_nil (α : ℤ[ω]) : jac [] α = 1 := by simp [jac]

lemma jac_cons (ρ : ℤ[ω]) (ls : List ℤ[ω]) (α : ℤ[ω]) :
    jac (ρ :: ls) α = cubicChar ρ α * jac ls α := by simp [jac]

lemma jac_append (l₁ l₂ : List ℤ[ω]) (α : ℤ[ω]) : jac (l₁ ++ l₂) α = jac l₁ α * jac l₂ α := by
  simp [jac]

lemma GoodList.of_cons {ρ : ℤ[ω]} {ls : List ℤ[ω]} (h : GoodList (ρ :: ls)) : GoodList ls :=
  fun x hx => h x (List.mem_cons_of_mem _ hx)

lemma jac_mul {ls : List ℤ[ω]} (h : GoodList ls) (α β : ℤ[ω]) :
    jac ls (α * β) = jac ls α * jac ls β := by
  induction ls with
  | nil => simp [jac_nil]
  | cons ρ ls ih =>
    rw [jac_cons, jac_cons, jac_cons, cubicChar_mul (h ρ (by simp)).1 (h ρ (by simp)).2,
      ih h.of_cons]
    ring

lemma jac_one {ls : List ℤ[ω]} (h : GoodList ls) : jac ls 1 = 1 := by
  induction ls with
  | nil => simp [jac_nil]
  | cons ρ ls ih => rw [jac_cons, cubicChar_one (h ρ (by simp)).1 (h ρ (by simp)).2, ih h.of_cons,
      one_mul]

lemma jac_neg_one {ls : List ℤ[ω]} (h : GoodList ls) : jac ls (-1) = 1 := by
  induction ls with
  | nil => simp [jac_nil]
  | cons ρ ls ih => rw [jac_cons, cubicChar_neg_one (h ρ (by simp)).1 (h ρ (by simp)).2,
      ih h.of_cons, one_mul]

lemma jac_pow {ls : List ℤ[ω]} (h : GoodList ls) (α : ℤ[ω]) (n : ℕ) :
    jac ls (α ^ n) = jac ls α ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, jac_one h]
  | succ n ih => rw [pow_succ, pow_succ, jac_mul h, ih]

lemma jac_congr {ls : List ℤ[ω]} {α β : ℤ[ω]} (h : ∀ x ∈ ls, x ∣ α - β) :
    jac ls α = jac ls β := by
  induction ls with
  | nil => simp [jac_nil]
  | cons ρ ls ih =>
    rw [jac_cons, jac_cons, cubicChar_congr (h ρ (by simp)), ih fun x hx => h x (by simp [hx])]

lemma jac_neg {ls : List ℤ[ω]} (h : GoodList ls) (α : ℤ[ω]) : jac ls (-α) = jac ls α := by
  rw [← neg_one_mul, jac_mul h, jac_neg_one h, one_mul]

lemma cubicChar_cube {π α : ℤ[ω]} (hπ : Prime π) (h3 : (norm π).natAbs ≠ 3) (hα : ¬ π ∣ α) :
    cubicChar π α ^ 3 = 1 := (cubicChar_spec hπ h3 hα).1

lemma jac_cube {ls : List ℤ[ω]} (h : GoodList ls) {α : ℤ[ω]} (hα : ∀ x ∈ ls, ¬ x ∣ α) :
    jac ls α ^ 3 = 1 := by
  induction ls with
  | nil => simp [jac_nil]
  | cons ρ ls ih =>
    rw [jac_cons, mul_pow, cubicChar_cube (h ρ (by simp)).1 (h ρ (by simp)).2 (hα ρ (by simp)),
      ih h.of_cons (fun x hx => hα x (by simp [hx])), one_mul]

lemma jac_eq_opow {ls : List ℤ[ω]} (h : GoodList ls) {α : ℤ[ω]} (hα : ∀ x ∈ ls, ¬ x ∣ α) :
    ∃ x : ℤ, jac ls α = opow x := exists_opow (jac_cube h hα)

/-! ### Jacobi symbols of rational integers -/

lemma natAbs_norm_intCast (s : ℤ) : (norm (s : ℤ[ω])).natAbs = s.natAbs ^ 2 := by
  rw [rho_norm]
  simp only [QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast, Int.cast_id]
  have h : s ^ 2 - s * 0 + 0 ^ 2 = s ^ 2 := by ring
  rw [h, Int.natAbs_pow]

lemma not_dvd_intCast_of_coprime {ρ : ℤ[ω]} {q : ℕ} (hq : q.Prime) (hρ : (norm ρ).natAbs = q)
    {s : ℤ} (hc : Nat.Coprime q s.natAbs) : ¬ ρ ∣ (s : ℤ[ω]) := by
  intro h
  have h1 := natAbs_norm_dvd h
  rw [hρ, natAbs_norm_intCast] at h1
  have h2 := hq.dvd_of_dvd_pow h1
  have := Nat.dvd_gcd (dvd_refl q) h2
  rw [hc.gcd_eq_one] at this
  exact hq.one_lt.ne' (Nat.dvd_one.1 this)

lemma exists_split {q : ℕ} (hq : q.Prime) (hq3 : q % 3 = 1) :
    ∃ ρ : ℤ[ω], Prime ρ ∧ (q : ℤ[ω]) = ρ * star ρ ∧ (norm ρ).natAbs = q := by
  obtain ⟨ρ, hρ, h, -⟩ := exists_prime_eq_mul_star hq hq3
  refine ⟨ρ, hρ, h, ?_⟩
  have h2 : ((norm ρ : ℤ) : ℤ[ω]) = (q : ℤ[ω]) := by rw [← mul_star, h]
  have h3 : norm ρ = (q : ℤ) := by exact_mod_cast h2
  rw [h3]; simp

lemma sq_sub_one_mul (A B : ℤ) (hA : A % 3 = 1) (hB : B % 3 = 1) :
    ((A * B - 1) / 3) % 3 = ((A - 1) / 3 + (B - 1) / 3) % 3 := by
  obtain ⟨u, hu⟩ : ∃ u, A = 3 * u + 1 := ⟨(A - 1) / 3, by omega⟩
  obtain ⟨v, hv⟩ : ∃ v, B = 3 * v + 1 := ⟨(B - 1) / 3, by omega⟩
  have h : A * B - 1 = 3 * (3 * (u * v) + u + v) := by rw [hu, hv]; ring
  rw [h, Int.mul_ediv_cancel_left _ (by norm_num)]
  omega

lemma sq_mod_three {a : ℤ} (ha : a % 3 ≠ 0) : a ^ 2 % 3 = 1 := by
  have : a % 3 = 1 ∨ a % 3 = 2 := by omega
  rcases this with h | h <;> simp [pow_two, Int.mul_emod, h]

lemma lam_exp_mul (ra rb : ℤ) (ha : ra % 3 = 2) (hb : rb % 3 = 2) :
    (2 * ((-(ra * rb) + 1) / 3)) % 3 = (2 * ((ra + 1) / 3) + 2 * ((rb + 1) / 3)) % 3 := by
  obtain ⟨u, hu⟩ : ∃ u, ra = 3 * u - 1 := ⟨(ra + 1) / 3, by omega⟩
  obtain ⟨v, hv⟩ : ∃ v, rb = 3 * v - 1 := ⟨(rb + 1) / 3, by omega⟩
  have h : -(ra * rb) + 1 = 3 * (-3 * (u * v) + u + v) := by rw [hu, hv]; ring
  have h1 : ra + 1 = 3 * u := by omega
  have h2 : rb + 1 = 3 * v := by omega
  rw [h, h1, h2, Int.mul_ediv_cancel_left _ (by norm_num), Int.mul_ediv_cancel_left _ (by norm_num),
    Int.mul_ediv_cancel_left _ (by norm_num)]
  omega

/-- The properties of a list of primes with product `n` giving all the Jacobi symbols of `n`. -/
def RatJac (n : ℕ) (ls : List ℤ[ω]) : Prop :=
  GoodList ls ∧ ls.prod = (n : ℤ[ω]) ∧
  (∀ s : ℤ, Nat.Coprime n s.natAbs → jac ls (s : ℤ[ω]) = 1) ∧
  jac ls omega = opow (((n : ℤ) ^ 2 - 1) / 3) ∧
  (∀ r : ℤ, (r = n ∨ r = -(n : ℤ)) → r % 3 = 2 → jac ls (1 - omega) = opow (2 * ((r + 1) / 3)))

lemma RatJac.one : RatJac 1 [] := by
  refine ⟨fun x hx => by simp at hx, by simp, fun s _ => jac_nil _, ?_, ?_⟩
  · rw [jac_nil]; simp [opow_zero]
  · intro r hr hr2
    rcases hr with rfl | rfl
    · simp at hr2
    · simp [jac_nil, opow_zero]

lemma RatJac.mul {a b : ℕ} {la lb : List ℤ[ω]} (ha : ¬ 3 ∣ a) (hb : ¬ 3 ∣ b)
    (Ha : RatJac a la) (Hb : RatJac b lb) : RatJac (a * b) (la ++ lb) := by
  obtain ⟨Ga, Pa, A1, A2, A3⟩ := Ha
  obtain ⟨Gb, Pb, B1, B2, B3⟩ := Hb
  have G : GoodList (la ++ lb) := fun x hx => by
    rcases List.mem_append.1 hx with h | h
    · exact Ga x h
    · exact Gb x h
  refine ⟨G, by rw [List.prod_append, Pa, Pb]; push_cast; rfl, ?_, ?_, ?_⟩
  · intro s hs
    rw [jac_append, A1 s (Nat.Coprime.coprime_mul_right (by exact hs)),
      B1 s (Nat.Coprime.coprime_mul_left (by exact hs)), one_mul]
  · rw [jac_append, A2, B2, ← opow_add]
    apply opow_congr
    have ha' : ((a : ℤ)) % 3 ≠ 0 := by omega
    have hb' : ((b : ℤ)) % 3 ≠ 0 := by omega
    have := sq_sub_one_mul ((a : ℤ) ^ 2) ((b : ℤ) ^ 2) (sq_mod_three ha') (sq_mod_three hb')
    push_cast
    rw [mul_pow]
    exact this.symm
  · intro r hr hr2
    have ha' : ((a : ℤ)) % 3 ≠ 0 := by omega
    have hb' : ((b : ℤ)) % 3 ≠ 0 := by omega
    obtain ⟨ra, hra, hra2⟩ : ∃ ra : ℤ, (ra = a ∨ ra = -(a : ℤ)) ∧ ra % 3 = 2 := by
      by_cases h : (a : ℤ) % 3 = 2
      · exact ⟨a, Or.inl rfl, h⟩
      · exact ⟨-a, Or.inr rfl, by omega⟩
    obtain ⟨rb, hrb, hrb2⟩ : ∃ rb : ℤ, (rb = b ∨ rb = -(b : ℤ)) ∧ rb % 3 = 2 := by
      by_cases h : (b : ℤ) % 3 = 2
      · exact ⟨b, Or.inl rfl, h⟩
      · exact ⟨-b, Or.inr rfl, by omega⟩
    have hr' : r = -(ra * rb) := by
      have h1 : (-(ra * rb)) % 3 = 2 := by
        have : (ra * rb) % 3 = 1 := by simp [Int.mul_emod, hra2, hrb2]
        omega
      have h2 : (-(ra * rb) = ((a * b : ℕ) : ℤ)) ∨ (-(ra * rb) = -((a * b : ℕ) : ℤ)) := by
        push_cast
        rcases hra with rfl | rfl <;> rcases hrb with rfl | rfl
        · right; ring
        · left; ring
        · left; ring
        · right; ring
      have h3 : ((a * b : ℕ) : ℤ) % 3 ≠ 0 := by
        push_cast; rw [Int.mul_emod]; intro h
        have : (a : ℤ) % 3 * ((b : ℤ) % 3) % 3 = 0 := h
        have : (a : ℤ) % 3 = 1 ∨ (a : ℤ) % 3 = 2 := by omega
        have : (b : ℤ) % 3 = 1 ∨ (b : ℤ) % 3 = 2 := by omega
        rcases ‹(a : ℤ) % 3 = 1 ∨ _› with h1 | h1 <;> rcases this with h2 | h2 <;>
          simp_all
      generalize ((a * b : ℕ) : ℤ) = N at *
      omega
    rw [jac_append, A3 ra hra hra2, B3 rb hrb hrb2, ← opow_add, hr']
    apply opow_congr
    exact (lam_exp_mul ra rb hra2 hrb2).symm

lemma ratJac_inert {q : ℕ} (hq : q.Prime) (hq3 : q % 3 = 2) : RatJac q [(q : ℤ[ω])] := by
  have hq' : Prime (q : ℤ[ω]) := prime_natCast_of_mod_three_eq_two hq hq3
  have h3 : (norm (q : ℤ[ω])).natAbs ≠ 3 := natAbs_norm_natCast_ne_three hq
  have G : GoodList [(q : ℤ[ω])] := fun x hx => by
    rw [List.mem_singleton.1 hx]; exact ⟨hq', h3⟩
  refine ⟨G, by simp, ?_, ?_, ?_⟩
  · intro s hs
    rw [jac_cons, jac_nil, mul_one]
    apply cubicChar_natCast_intCast hq hq3
    intro h
    have := Int.natCast_dvd.1 h
    have := Nat.dvd_gcd (dvd_refl q) this
    rw [hs.gcd_eq_one] at this
    exact hq.one_lt.ne' (Nat.dvd_one.1 this)
  · rw [jac_cons, jac_nil, mul_one, cubicChar_omega hq' h3, ← opow_natCast]
    congr 1
    unfold cexp
    rw [natAbs_norm_natCast]
    have : (q : ℤ) ^ 2 = ((q ^ 2 : ℕ) : ℤ) := by push_cast; rfl
    have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq.pos
    rw [this]
    generalize q ^ 2 = Q at *
    omega
  · intro r hr hr2
    have hrq : r = q := by
      rcases hr with h | h
      · exact h
      · omega
    subst hrq
    rw [jac_cons, jac_nil, mul_one, cubicChar_natCast_one_sub_omega hq hq3, ← opow_natCast]
    congr 1

lemma star_lam : star (1 - omega) = (1 - omega) * (-omega ^ 2) := by
  rw [star_sub, star_one, star_omega]
  linear_combination (-1 : ℤ[ω]) * omega_cube

lemma ratJac_split {q : ℕ} (hq : q.Prime) (hq3 : q % 3 = 1) :
    ∃ ls, RatJac q ls := by
  obtain ⟨ρ, hρ, hqρ, hN⟩ := exists_split hq hq3
  have h3 : (norm ρ).natAbs ≠ 3 := by rw [hN]; omega
  have hσ : Prime (star ρ) := prime_star hρ
  have h3' : (norm (star ρ)).natAbs ≠ 3 := by rw [natAbs_norm_star]; exact h3
  have G : GoodList [ρ, star ρ] := fun x hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨hρ, h3⟩
    · rw [List.mem_singleton.1 hx]; exact ⟨hσ, h3'⟩
  obtain ⟨t, ht⟩ : ∃ t : ℕ, q = 3 * t + 1 := ⟨q / 3, by omega⟩
  have hcexp : cexp ρ = t := by unfold cexp; rw [hN]; omega
  have hcexp' : cexp (star ρ) = t := by rw [cexp_star, hcexp]
  refine ⟨[ρ, star ρ], G, by simp [hqρ], ?_, ?_, ?_⟩
  · intro s hs
    have hnd : ¬ ρ ∣ (s : ℤ[ω]) := not_dvd_intCast_of_coprime hq hN hs
    have h1 := cubicChar_star hρ h3 (s : ℤ[ω])
    rw [star_intCast] at h1
    have h2 := (star_cubicChar hρ h3 (s : ℤ[ω])).1
    rw [← h1] at h2
    rw [jac_cons, jac_cons, jac_nil, mul_one, h2]
    calc cubicChar ρ ↑s * cubicChar ρ ↑s ^ 2 = cubicChar ρ ↑s ^ 3 := by ring
      _ = 1 := cubicChar_cube hρ h3 hnd
  · rw [jac_cons, jac_cons, jac_nil, mul_one, cubicChar_omega hρ h3, cubicChar_omega hσ h3',
      hcexp, hcexp', ← pow_add, ← opow_natCast]
    apply opow_congr
    have : ((q : ℤ) ^ 2 - 1) = 3 * (3 * (t : ℤ) ^ 2 + 2 * t) := by rw [ht]; push_cast; ring
    rw [this, Int.mul_ediv_cancel_left _ (by norm_num)]
    push_cast
    omega
  · intro r hr hr2
    have hrq : r = -(q : ℤ) := by
      rcases hr with h | h
      · omega
      · exact h
    have hnd : ¬ ρ ∣ (1 - omega) := by
      intro h
      apply (natAbs_norm_ne_three_iff hρ).1 h3
      rw [three_eq_and_prime_one_sub_omega.1]
      exact Dvd.dvd.mul_left (dvd_pow h two_ne_zero) _
    have hndω : ¬ ρ ∣ omega := fun h => hρ.not_isUnit (isUnit_of_dvd_unit h isUnit_omega)
    set u := cubicChar ρ (1 - omega) with hu
    set w := cubicChar ρ omega with hw
    have hu3 : u ^ 3 = 1 := cubicChar_cube hρ h3 hnd
    have hw3 : w ^ 3 = 1 := cubicChar_cube hρ h3 hndω
    have hσu : cubicChar (star ρ) (1 - omega) = u ^ 2 * w := by
      have h1 := cubicChar_star hρ h3 (star (1 - omega))
      rw [star_star] at h1
      rw [h1, star_lam, show (1 - omega) * (-omega ^ 2) = (1 - omega) * ((-1) * omega ^ 2) by ring,
        cubicChar_mul hρ h3, cubicChar_mul hρ h3, cubicChar_neg_one hρ h3, cubicChar_pow hρ h3,
        one_mul, star_mul', star_pow, (star_cubicChar hρ h3 (1 - omega)).1,
        (star_cubicChar hρ h3 omega).1]
      calc u ^ 2 * (w ^ 2) ^ 2 = u ^ 2 * w * w ^ 3 := by ring
        _ = u ^ 2 * w := by rw [hw3, mul_one]
    rw [jac_cons, jac_cons, jac_nil, mul_one, hσu, hrq]
    calc u * (u ^ 2 * w) = u ^ 3 * w := by ring
      _ = w := by rw [hu3, one_mul]
      _ = _ := by
        rw [hw, cubicChar_omega hρ h3, hcexp, ← opow_natCast]
        apply opow_congr
        have : -(q : ℤ) + 1 = 3 * (-(t : ℤ)) := by rw [ht]; push_cast; ring
        rw [this, Int.mul_ediv_cancel_left _ (by norm_num)]
        omega

lemma exists_ratJac (n : ℕ) (hn : ¬ 3 ∣ n) : ∃ ls, RatJac n ls := by
  induction n using Nat.recOnMul with
  | zero => exact absurd (dvd_zero 3) hn
  | one => exact ⟨[], RatJac.one⟩
  | prime q hq =>
    have hq3 : q % 3 = 1 ∨ q % 3 = 2 := by omega
    rcases hq3 with hq3 | hq3
    · exact ratJac_split hq hq3
    · exact ⟨_, ratJac_inert hq hq3⟩
  | mul a b ha hb =>
    have ha' : ¬ 3 ∣ a := fun h => hn (h.mul_right b)
    have hb' : ¬ 3 ∣ b := fun h => hn (h.mul_left a)
    obtain ⟨la, Ha⟩ := ha ha'
    obtain ⟨lb, Hb⟩ := hb hb'
    exact ⟨_, RatJac.mul ha' hb' Ha Hb⟩

/-! ### Reciprocity for rational integers modulo a primary prime of prime norm -/

lemma chi_eq_jac {π : ℤ[ω]} (hπ : Prime π) (hp : (norm π).natAbs.Prime) (hP : IsPrimary π)
    {n : ℕ} {ls : List ℤ[ω]} (H : RatJac n ls) (hn3 : ¬ 3 ∣ n) (hpn : ¬ (norm π).natAbs ∣ n) :
    cubicChar π (n : ℤ[ω]) = jac ls π := by
  have h3 : (norm π).natAbs ≠ 3 := (natAbs_norm_ne_three_iff hπ).2 (hP.not_dvd_three hπ dvd_rfl)
  obtain ⟨G, Pr, -⟩ := H
  have hh := cubicChar_jacobi_recip [π] ls
    (fun x hx => by rw [List.mem_singleton.1 hx]; exact hπ) (fun x hx => (G x hx).1)
    (by
      right
      simp only [List.prod_cons, List.prod_nil, mul_one]
      have e : π + 1 = (π - 2) + 3 := by ring
      rw [e]; exact dvd_add hP dvd_rfl)
    (by
      rw [Pr]
      have : (n : ℤ) % 3 = 1 ∨ (n : ℤ) % 3 = 2 := by omega
      rcases this with h | h
      · left
        have := (Int.castRingHom ℤ[ω]).map_dvd (show (3 : ℤ) ∣ (n : ℤ) - 1 by omega)
        simpa using this
      · right
        have := (Int.castRingHom ℤ[ω]).map_dvd (show (3 : ℤ) ∣ (n : ℤ) + 1 by omega)
        simpa using this)
    (by
      simp only [List.prod_cons, List.prod_nil, mul_one, Pr, natAbs_norm_natCast]
      exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpn))
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, Pr] at hh
  rw [← hh]
  rfl

lemma chi_int {π : ℤ[ω]} (hπ : Prime π) (hp : (norm π).natAbs.Prime) (hP : IsPrimary π)
    {r : ℤ} (hr3 : r % 3 ≠ 0) (hrp : ¬ ((norm π).natAbs : ℤ) ∣ r) {β : ℤ[ω]}
    (hdiv : (r : ℤ[ω]) ∣ π - β) :
    ∃ ls, RatJac r.natAbs ls ∧ cubicChar π (r : ℤ[ω]) = jac ls β := by
  have hn3 : ¬ 3 ∣ r.natAbs := by omega
  obtain ⟨ls, H⟩ := exists_ratJac r.natAbs hn3
  have hpn : ¬ (norm π).natAbs ∣ r.natAbs := fun h => hrp (Int.natCast_dvd.2 h)
  refine ⟨ls, H, ?_⟩
  have hnd : ((r.natAbs : ℕ) : ℤ[ω]) ∣ (r : ℤ[ω]) := by
    have := (Int.castRingHom ℤ[ω]).map_dvd (Int.natAbs_dvd_self (a := r))
    simpa using this
  have e1 : cubicChar π (r : ℤ[ω]) = cubicChar π ((r.natAbs : ℕ) : ℤ[ω]) := by
    have h3 : (norm π).natAbs ≠ 3 :=
      (natAbs_norm_ne_three_iff hπ).2 (hP.not_dvd_three hπ dvd_rfl)
    rcases Int.natAbs_eq r with h | h
    · have h' : (r : ℤ[ω]) = ((r.natAbs : ℕ) : ℤ[ω]) := by
        have := congrArg (Int.cast : ℤ → ℤ[ω]) h
        simp only [Int.cast_natCast] at this
        exact this
      rw [h']
    · have h' : (r : ℤ[ω]) = -((r.natAbs : ℕ) : ℤ[ω]) := by
        have := congrArg (Int.cast : ℤ → ℤ[ω]) h
        simp only [Int.cast_neg, Int.cast_natCast] at this
        exact this
      rw [h', ← neg_one_mul, cubicChar_mul hπ h3, cubicChar_neg_one hπ h3, one_mul]
  rw [e1, chi_eq_jac hπ hp hP H hn3 hpn]
  apply jac_congr
  intro x hx
  have : x ∣ ls.prod := List.dvd_prod hx
  rw [H.2.1] at this
  exact this.trans (hnd.trans hdiv)

lemma natAbs_norm_eq_int (π : ℤ[ω]) :
    (((norm π).natAbs : ℕ) : ℤ) = π.re ^ 2 - π.re * π.im + π.im ^ 2 := by
  rw [← rho_norm]; exact Int.natAbs_of_nonneg (rho_norm_nonneg π)

lemma isUnit_of_dvd_re_im {π : ℤ[ω]} (hp : (norm π).natAbs.Prime) {d : ℤ} (h1 : d ∣ π.re)
    (h2 : d ∣ π.im) : IsUnit d := by
  obtain ⟨a', ha'⟩ := h1
  obtain ⟨b', hb'⟩ := h2
  have hpp : Prime (((norm π).natAbs : ℕ) : ℤ) := Nat.prime_iff_prime_int.1 hp
  apply hpp.irreducible.squarefree d
  refine ⟨a' ^ 2 - a' * b' + b' ^ 2, ?_⟩
  rw [natAbs_norm_eq_int, ha', hb']
  ring

lemma not_dvd_re {π : ℤ[ω]} (hp : (norm π).natAbs.Prime) : ¬ ((norm π).natAbs : ℤ) ∣ π.re := by
  intro h
  have hpp : Prime (((norm π).natAbs : ℕ) : ℤ) := Nat.prime_iff_prime_int.1 hp
  have h2 : ((norm π).natAbs : ℤ) ∣ π.im ^ 2 := by
    have e : π.im ^ 2 = ((norm π).natAbs : ℤ) - π.re * (π.re - π.im) := by
      rw [natAbs_norm_eq_int]; ring
    rw [e]
    exact dvd_sub dvd_rfl (dvd_mul_of_dvd_left h _)
  have := isUnit_of_dvd_re_im hp h (hpp.dvd_of_dvd_pow h2)
  exact hpp.not_isUnit this

lemma not_dvd_im {π : ℤ[ω]} (hp : (norm π).natAbs.Prime) : ¬ ((norm π).natAbs : ℤ) ∣ π.im := by
  intro h
  have hpp : Prime (((norm π).natAbs : ℕ) : ℤ) := Nat.prime_iff_prime_int.1 hp
  have h2 : ((norm π).natAbs : ℤ) ∣ π.re ^ 2 := by
    have e : π.re ^ 2 = ((norm π).natAbs : ℤ) - π.im * (π.im - π.re) := by
      rw [natAbs_norm_eq_int]; ring
    rw [e]
    exact dvd_sub dvd_rfl (dvd_mul_of_dvd_left h _)
  exact not_dvd_re hp (hpp.dvd_of_dvd_pow h2)

lemma not_dvd_re_add_im {π : ℤ[ω]} (hp : (norm π).natAbs.Prime) (hp3 : (norm π).natAbs ≠ 3) :
    ¬ ((norm π).natAbs : ℤ) ∣ π.re + π.im := by
  intro h
  have hpp : Prime (((norm π).natAbs : ℕ) : ℤ) := Nat.prime_iff_prime_int.1 hp
  have h2 : ((norm π).natAbs : ℤ) ∣ 3 * π.re ^ 2 := by
    have e : 3 * π.re ^ 2 = ((norm π).natAbs : ℤ) + 3 * π.re * (π.re + π.im) -
        (π.re + π.im) * (π.re + π.im) := by
      rw [natAbs_norm_eq_int]; ring
    rw [e]
    exact dvd_sub (dvd_add dvd_rfl (dvd_mul_of_dvd_right h _)) (dvd_mul_of_dvd_left h _)
  rcases hpp.dvd_or_dvd h2 with h3 | h3
  · have : (norm π).natAbs ∣ 3 := by exact_mod_cast h3
    rcases (Nat.dvd_prime Nat.prime_three).1 this with h4 | h4
    · exact hp.one_lt.ne' h4
    · exact hp3 h4
  · exact not_dvd_re hp (hpp.dvd_of_dvd_pow h3)

lemma coprime_of_dvd_im {π : ℤ[ω]} (hp : (norm π).natAbs.Prime) {d : ℤ} (h : d ∣ π.im) :
    Nat.Coprime d.natAbs π.re.natAbs := by
  have h1 : ((Int.gcd d π.re : ℕ) : ℤ) ∣ π.re := Int.gcd_dvd_right _ _
  have h2 : ((Int.gcd d π.re : ℕ) : ℤ) ∣ d := Int.gcd_dvd_left _ _
  have hu := isUnit_of_dvd_re_im hp h1 (h2.trans h)
  have := Int.isUnit_iff_natAbs_eq.1 hu
  rw [Int.natAbs_natCast] at this
  exact this

lemma exists_three_pow (b : ℤ) (hb : b ≠ 0) : ∃ (k : ℕ) (c : ℤ), b = 3 ^ k * c ∧ c % 3 ≠ 0 := by
  obtain ⟨k, c', hc', hk⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.2 hb) 3
    (by norm_num)
  have hk' : (b.natAbs : ℤ) = 3 ^ k * (c' : ℤ) := by exact_mod_cast hk
  rcases Int.natAbs_eq b with h | h
  · exact ⟨k, c', by rw [h, hk'], by omega⟩
  · exact ⟨k, -(c' : ℤ), by rw [h, hk']; ring, by omega⟩

lemma coprime_add_im {π : ℤ[ω]} (hp : (norm π).natAbs.Prime) :
    Nat.Coprime (π.re + π.im).natAbs π.im.natAbs := by
  have h1 : ((Int.gcd (π.re + π.im) π.im : ℕ) : ℤ) ∣ π.im := Int.gcd_dvd_right _ _
  have h2 : ((Int.gcd (π.re + π.im) π.im : ℕ) : ℤ) ∣ π.re + π.im := Int.gcd_dvd_left _ _
  have h3 : ((Int.gcd (π.re + π.im) π.im : ℕ) : ℤ) ∣ π.re := by
    have := dvd_sub h2 h1
    simpa using this
  have hu := isUnit_of_dvd_re_im hp h3 h1
  have := Int.isUnit_iff_natAbs_eq.1 hu
  rw [Int.natAbs_natCast] at this
  exact this

lemma not_dvd_lam {ρ : ℤ[ω]} (hρ : Prime ρ) (h3 : (norm ρ).natAbs ≠ 3) : ¬ ρ ∣ (1 - omega) := by
  intro h
  apply (natAbs_norm_ne_three_iff hρ).1 h3
  rw [three_eq_and_prime_one_sub_omega.1]
  exact Dvd.dvd.mul_left (dvd_pow h two_ne_zero) _

lemma cubicChar_three {ρ : ℤ[ω]} (hρ : Prime ρ) (h3 : (norm ρ).natAbs ≠ 3) :
    cubicChar ρ 3 = cubicChar ρ omega ^ 2 * cubicChar ρ (1 - omega) ^ 2 := by
  rw [three_eq_and_prime_one_sub_omega.1, neg_mul, ← neg_one_mul, cubicChar_mul hρ h3,
    cubicChar_neg_one hρ h3, one_mul, cubicChar_mul hρ h3, cubicChar_pow hρ h3,
    cubicChar_pow hρ h3]

lemma cexp_primary {π : ℤ[ω]} (hP : IsPrimary π) :
    ((cexp π : ℕ) : ℤ) % 3 = ((π.re + 1) / 3 + π.im / 3) % 3 := by
  obtain ⟨ha3, hb3⟩ := (isPrimary_iff π).1 hP
  obtain ⟨m, hm⟩ : ∃ m, π.re = 3 * m - 1 := ⟨(π.re + 1) / 3, by omega⟩
  obtain ⟨n, hn⟩ : ∃ n, π.im = 3 * n := ⟨π.im / 3, by omega⟩
  have hN := natAbs_norm_eq_int π
  have hQ : (((norm π).natAbs : ℕ) : ℤ) =
      3 * (3 * (m ^ 2 - m * n + n ^ 2) - 2 * m + n) + 1 := by
    rw [hN, hm, hn]; ring
  generalize m ^ 2 - m * n + n ^ 2 = T at hQ
  unfold cexp
  rw [hm, hn]
  omega

lemma opow_comb (k : ℕ) (c x : ℤ) : (opow c ^ 2 * opow x ^ 2) ^ k = opow (k * (2 * c + 2 * x)) := by
  rw [opow_pow, opow_pow, ← opow_add, opow_pow]
  congr 1

lemma final_decide : ∀ K M N X : ZMod 3, (K = 1 ∨ N = 0) →
    K * (2 * (M + N) + 2 * X) + (M + N) = 3 * M ^ 2 - 2 * M →
    K * (2 * (M + N) + 2 * X) + X = 2 * (M + N) →
    X = 2 * M := by decide

theorem cubicChar_one_sub_omega_of_primeNorm {π : ℤ[ω]} (hπ : Prime π)
    (hp : (norm π).natAbs.Prime) (hP : IsPrimary π) :
    cubicChar π (1 - omega) = opow (2 * ((π.re + 1) / 3)) := by
  have h3 : (norm π).natAbs ≠ 3 := (natAbs_norm_ne_three_iff hπ).2 (hP.not_dvd_three hπ dvd_rfl)
  obtain ⟨ha3, hb3⟩ := (isPrimary_iff π).1 hP
  have e := eq_re_add_im π
  have hpa := not_dvd_re hp
  have hpb := not_dvd_im hp
  have hpab := not_dvd_re_add_im hp h3
  have hb0 : π.im ≠ 0 := fun h => hpb (h ▸ dvd_zero _)
  obtain ⟨k, c, hbc, hc3⟩ := exists_three_pow π.im hb0
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hbc; omega
    · exact h
  have hk2 : 2 ≤ k → π.im / 3 % 3 = 0 := by
    intro hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have : π.im = 9 * (3 ^ j * c) := by rw [hbc]; ring
    omega
  have hcb : c ∣ π.im := ⟨3 ^ k, by rw [hbc]; ring⟩
  have hpc : ¬ ((norm π).natAbs : ℤ) ∣ c := fun h => hpb (h.trans hcb)
  -- the characters of `λ` and `ω`
  obtain ⟨x, hx⟩ := exists_opow (cubicChar_cube hπ h3 (not_dvd_lam hπ h3))
  have hw : cubicChar π omega = opow (cexp π : ℤ) := by rw [cubicChar_omega hπ h3, opow_natCast]
  -- `χ(c) = 1`
  obtain ⟨lc, Hc, hχc⟩ := chi_int hπ hp hP (r := c) hc3 hpc (β := (π.re : ℤ[ω]))
    (by
      have : π - (π.re : ℤ[ω]) = (π.im : ℤ[ω]) * omega := by linear_combination e
      rw [this]
      exact dvd_mul_of_dvd_left ((Int.castRingHom ℤ[ω]).map_dvd hcb) _)
  have hχc1 : cubicChar π (c : ℤ[ω]) = 1 := by
    rw [hχc]; exact Hc.2.2.1 π.re (coprime_of_dvd_im hp hcb)
  -- `χ(b)`
  have hb_cast : (π.im : ℤ[ω]) = (3 : ℤ[ω]) ^ k * (c : ℤ[ω]) := by
    have := congrArg (Int.cast : ℤ → ℤ[ω]) hbc
    push_cast at this
    exact this
  have hχb : cubicChar π (π.im : ℤ[ω]) =
      (cubicChar π omega ^ 2 * cubicChar π (1 - omega) ^ 2) ^ k := by
    rw [hb_cast, cubicChar_mul hπ h3, cubicChar_pow hπ h3, cubicChar_three hπ h3, hχc1, mul_one]
  -- `χ(a)`
  obtain ⟨la, Ha, hχa⟩ := chi_int hπ hp hP (r := π.re) (by omega) hpa
    (β := (π.im : ℤ[ω]) * omega) ⟨1, by rw [mul_one]; linear_combination e⟩
  have hχa' : cubicChar π (π.re : ℤ[ω]) = opow ((π.re ^ 2 - 1) / 3) := by
    rw [hχa, jac_mul Ha.1, Ha.2.2.1 π.im (coprime_of_dvd_im hp dvd_rfl).symm, Ha.2.2.2.1,
      one_mul, Int.natAbs_sq]
  -- `χ(a+b)`
  obtain ⟨lab, Hab, hχab⟩ := chi_int hπ hp hP (r := π.re + π.im) (by omega) hpab
    (β := -((π.im : ℤ[ω]) * (1 - omega))) ⟨1, by push_cast; rw [mul_one]; linear_combination e⟩
  have hχab' : cubicChar π ((π.re + π.im : ℤ) : ℤ[ω]) = opow (2 * ((π.re + π.im + 1) / 3)) := by
    rw [hχab, jac_neg Hab.1, jac_mul Hab.1, Hab.2.2.1 π.im (coprime_add_im hp), one_mul]
    exact Hab.2.2.2.2 (π.re + π.im) (Int.natAbs_eq _) (by omega)
  -- the two relations
  have hI : cubicChar π (π.im : ℤ[ω]) * cubicChar π omega = cubicChar π (π.re : ℤ[ω]) := by
    rw [← cubicChar_mul hπ h3, cubicChar_congr (β := -(π.re : ℤ[ω])) ⟨1, by
      rw [mul_one]; linear_combination (-1 : ℤ[ω]) * e⟩, ← neg_one_mul, cubicChar_mul hπ h3,
      cubicChar_neg_one hπ h3, one_mul]
  have hII : cubicChar π (π.im : ℤ[ω]) * cubicChar π (1 - omega) =
      cubicChar π ((π.re + π.im : ℤ) : ℤ[ω]) := by
    rw [← cubicChar_mul hπ h3, cubicChar_congr (β := ((π.re + π.im : ℤ) : ℤ[ω])) ⟨-1, by
      push_cast; linear_combination e⟩]
  rw [hχb, hw, hx, opow_comb, hχa', ← opow_add, opow_eq_iff] at hI
  rw [hχb, hw, hx, opow_comb, hχab', ← opow_add, opow_eq_iff] at hII
  rw [hx]
  apply opow_congr
  obtain ⟨m, hm⟩ : ∃ m, π.re = 3 * m - 1 := ⟨(π.re + 1) / 3, by omega⟩
  obtain ⟨n, hn⟩ : ∃ n, π.im = 3 * n := ⟨π.im / 3, by omega⟩
  have hcc := cexp_primary hP
  have hα : (π.re ^ 2 - 1) / 3 = 3 * m ^ 2 - 2 * m := by
    have : π.re ^ 2 - 1 = 3 * (3 * m ^ 2 - 2 * m) := by rw [hm]; ring
    rw [this]; omega
  have hβ : (π.re + π.im + 1) / 3 = m + n := by omega
  have hγ : (π.re + 1) / 3 = m := by omega
  have hnn : π.im / 3 = n := by omega
  rw [hα] at hI
  rw [hβ] at hII
  rw [hγ, hnn] at hcc
  rw [hγ]
  have hK : ((k : ℕ) : ZMod 3) = 1 ∨ (n : ZMod 3) = 0 := by
    rcases Nat.lt_or_ge k 2 with h | h
    · left; have : k = 1 := by omega
      subst this; simp
    · right
      have h0 := hk2 h
      rw [hnn] at h0
      have : (n : ZMod 3) = ((0 : ℤ) : ZMod 3) := (ZMod.intCast_eq_intCast_iff' ..).2 (by simpa using h0)
      simpa using this
  generalize ((cexp π : ℕ) : ℤ) = cc at hI hII hcc
  have h1 := (ZMod.intCast_eq_intCast_iff' ..).2 hI
  have h2 := (ZMod.intCast_eq_intCast_iff' ..).2 hII
  have h3 := (ZMod.intCast_eq_intCast_iff' ..).2 hcc
  push_cast at h1 h2 h3
  rw [h3] at h1 h2
  have := final_decide (k : ZMod 3) m n x hK (by linear_combination h1) (by linear_combination h2)
  have h4 : ((x : ℤ) : ZMod 3) = ((2 * m : ℤ) : ZMod 3) := by push_cast; exact this
  exact (ZMod.intCast_eq_intCast_iff' ..).1 h4

/-! ### The supplements for every primary prime -/

lemma isPrimary_natCast {q : ℕ} (hq3 : q % 3 = 2) : IsPrimary (q : ℤ[ω]) := by
  have := (isPrimary_intCast_iff (q : ℤ)).2 (by omega)
  simpa using this

/-- **Supplement for `1 - ω`**, every primary prime (split or inert). -/
theorem cubicChar_one_sub_omega_primary {π : ℤ[ω]} (hπ : Prime π) (hP : IsPrimary π) :
    cubicChar π (1 - omega) = opow (2 * ((π.re + 1) / 3)) := by
  have h3 : (norm π).natAbs ≠ 3 := (natAbs_norm_ne_three_iff hπ).2 (hP.not_dvd_three hπ dvd_rfl)
  rcases rho_prime_iff.1 hπ with h | ⟨q, hq, hq3, h⟩ | ⟨p, hp, hp3, h⟩
  · exact absurd (by rw [qa_natAbs_norm_eq_of_associated h, rho_natAbs_norm_lam]) h3
  · obtain ⟨u, hu⟩ := h.symm
    have hu1 : (u : ℤ[ω]) = 1 :=
      unit_eq_of_isPrimary (α := (q : ℤ[ω])) u.isUnit isUnit_one
        (by rw [mul_comm, hu]; exact hP) (by rw [one_mul]; exact isPrimary_natCast hq3)
    have hπq : π = q := by rw [← hu, hu1, mul_one]
    subst hπq
    rw [cubicChar_natCast_one_sub_omega hq hq3, ← opow_natCast]
    apply opow_congr
    have : ((q : ℤ[ω])).re = q := by simp
    rw [this]
    omega
  · have hp' : (norm π).natAbs.Prime := by rw [h, Int.natAbs_natCast]; exact hp
    exact cubicChar_one_sub_omega_of_primeNorm hπ hp' hP

/-- **Supplement for `ω`**, every primary prime. -/
theorem cubicChar_omega_primary {π : ℤ[ω]} (hπ : Prime π) (hP : IsPrimary π) :
    cubicChar π omega = opow ((π.re + π.im + 1) / 3) := by
  have h3 : (norm π).natAbs ≠ 3 := (natAbs_norm_ne_three_iff hπ).2 (hP.not_dvd_three hπ dvd_rfl)
  obtain ⟨ha3, hb3⟩ := (isPrimary_iff π).1 hP
  rw [cubicChar_omega hπ h3, ← opow_natCast]
  apply opow_congr
  rw [cexp_primary hP]
  omega

end NTKB.IrelandRosen.CubicSupplement

namespace NTKB.IrelandRosen.Eisenstein

open NTKB.HardyWright
open QuadraticAlgebra hiding omega

local notation "ℤ[ω]" => NTKB.HardyWright.ZRho

/-- **Theorem 1' (supplement to cubic reciprocity)**, every primary prime. For a primary prime `π`
of `ℤ[ω]` with real part `a = 3m - 1`: `χ_π(1 - ω) = ω^{2m}` (the exponent read modulo 3). The
rational case `π = q`, `q = 3m - 1`, is `cubicChar_natCast_one_sub_omega`. -/
@[kb "irelandrosen1990" "Ch. 9, §3, Theorem 1', p. 125"]
theorem cubicChar_one_sub_omega_of_isPrimary {π : ℤ[ω]} (hπ : Prime π) (hP : IsPrimary π) {m : ℤ}
    (hm : π.re = 3 * m - 1) :
    cubicChar π (1 - omega) = omega ^ ((2 * m) % 3).toNat := by
  have h := CubicSupplement.cubicChar_one_sub_omega_primary hπ hP
  have e : (π.re + 1) / 3 = m := by omega
  rw [h, e]
  rfl

end NTKB.IrelandRosen.Eisenstein
