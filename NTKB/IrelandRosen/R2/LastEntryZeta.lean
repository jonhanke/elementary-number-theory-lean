/-
Ireland–Rosen, Chapter 11: Exercise 11.18 (`J(χ_1', …, χ_n') = (-1)^{(s-1)(n-1)} J(χ_1, …, χ_n)^s`)
and the zeta function of the curve of Gauss's last entry (Theorem of §11.5, second part):
`Z(u) = (1 - 2au + pu²) / ((1 - u)(1 - pu))`.
-/
import NTKB.IrelandRosen.R2.LastEntry
import NTKB.IrelandRosen.R2.ZetaDiagonal

open Finset PowerSeries
open scoped Classical

set_option linter.unusedSectionVars false

namespace NTKB.IrelandRosen

variable {F : Type*} [Field F] [Fintype F] {E : Type*} [Field E] [Fintype E] [Algebra F E]

lemma gaussSum_ne_zero {K : Type*} [Field K] [Fintype K] {χ : MulChar K ℂ} (hχ : χ ≠ 1)
    {ψ : AddChar K ℂ} (hψ : ψ.IsPrimitive) : gaussSum χ ψ ≠ 0 := by
  intro h
  have := norm_gaussSum hχ hψ
  rw [h, norm_zero] at this
  have hq : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  exact (Real.sqrt_pos.mpr hq).ne' this.symm

/-- **Exercise 11.18.** If `χ_1, …, χ_{r+1}` are nontrivial characters of `F` with nontrivial
product and `[E : F] = s`, then `J(χ_1', …, χ_{r+1}') = (-1)^{(s-1) r} J(χ_1, …, χ_{r+1})^s`. -/
@[kb "irelandrosen1990" "Exercise 11.18, p. 171"]
theorem multiJacobiSum_liftNorm {r : ℕ} {χ : Fin (r + 1) → MulChar F ℂ} (hχ : ∀ i, χ i ≠ 1)
    (hprod : ∏ i, χ i ≠ 1) :
    multiJacobiSum (fun i => liftNorm (E := E) (χ i)) =
      (-1) ^ ((Module.finrank F E - 1) * r) * multiJacobiSum χ ^ Module.finrank F E := by
  obtain ⟨ψ, hψ⟩ := exists_isPrimitive_addChar (F := F)
  have hψ1 : ψ ≠ 1 := fun h => by
    apply hψ one_ne_zero; ext x; simp [h]
  have hψ' : (liftTrace (E := E) ψ).IsPrimitive :=
    AddChar.IsPrimitive.of_ne_one (liftTrace_ne_one hψ1)
  set s := Module.finrank F E with hs
  have hs1 : 1 ≤ s := Module.finrank_pos
  have hχ' : ∀ i, liftNorm (E := E) (χ i) ≠ 1 := fun i => liftNorm_ne_one (hχ i)
  have hprodE : ∏ i, liftNorm (E := E) (χ i) = liftNorm (∏ i, χ i) := by
    rw [← liftNormHom_apply, map_prod]; rfl
  have hprod' : ∏ i, liftNorm (E := E) (χ i) ≠ 1 := by rw [hprodE]; exact liftNorm_ne_one hprod
  have hF := prod_gaussSum_eq_multiJacobiSum_mul hχ hprod ψ
  have hE := prod_gaussSum_eq_multiJacobiSum_mul hχ' hprod' (liftTrace ψ)
  have hHD : ∀ φ : MulChar F ℂ, gaussSum (liftNorm (E := E) φ) (liftTrace ψ) =
      -(-gaussSum φ ψ) ^ s := by
    intro φ; rw [hasse_davenport (E := E) φ hψ1, neg_neg]
  rw [hprodE, hHD] at hE
  simp only [hHD] at hE
  rw [Finset.prod_neg, Finset.prod_pow, Finset.prod_neg, card_univ, Fintype.card_fin, hF] at hE
  set G := gaussSum (∏ i, χ i) ψ
  have hG : G ≠ 0 := gaussSum_ne_zero hprod hψ
  set J := multiJacobiSum χ
  set J' := multiJacobiSum fun i => liftNorm (E := E) (χ i)
  obtain ⟨t, ht⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  rw [ht] at hE ⊢
  simp only [Nat.add_sub_cancel]
  have hGs : (-(-G) ^ (t + 1)) ≠ 0 := neg_ne_zero.mpr (pow_ne_zero _ (neg_ne_zero.mpr hG))
  apply mul_right_cancel₀ hGs
  rw [← hE]
  set u : ℂ := (-1) ^ r
  have hu : u ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have e1 : ((-1 : ℂ) ^ (r + 1)) = -u := by rw [pow_succ]; ring
  have e2 : ((-1 : ℂ) ^ (t * r)) = u ^ t := by rw [mul_comm, pow_mul]
  rw [e1, e2, mul_pow, mul_pow, neg_pow G, neg_pow u]
  linear_combination (-(-1 : ℂ) ^ (t + 1) * u ^ t * J ^ (t + 1) * G ^ (t + 1)) * hu

/-- `N = q - 1 + 2 Re J(ρ, χ)` for the curve of §11.5 (`χ` of order `4`, `ρ = χ²`). -/
theorem numLastEntry_eq_re {K : Type*} [Field K] [Fintype K] (h4 : 4 ∣ Fintype.card K - 1)
    {χ : MulChar K ℂ} (hχ : orderOf χ = 4) :
    (numLastEntry K : ℂ) = Fintype.card K - 1 + 2 * (multiJacobiSum ![χ ^ 2, χ]).re := by
  have hN2 := numSolDiag_two_four h4 hχ
  rw [numSolDiag_two_four_eq (ringChar_ne_two_of_four_dvd h4), numSolPow_two_neg_one h4 hχ]
    at hN2
  rw [numLastEntry_eq]
  push_cast at hN2 ⊢
  linear_combination hN2

/-- Over the extension `E` of degree `s`: `N_s = q^s - 1 - π^s - π̄^s` with `π = -J(ρ, χ)`. -/
theorem numLastEntry_extension (h4 : 4 ∣ Fintype.card F - 1) {χ : MulChar F ℂ}
    (hχ : orderOf χ = 4) :
    (numLastEntry E : ℂ) = (Fintype.card F : ℂ) ^ Module.finrank F E - 1 -
      (-multiJacobiSum ![χ ^ 2, χ]) ^ Module.finrank F E -
      starRingEnd ℂ (-multiJacobiSum ![χ ^ 2, χ]) ^ Module.finrank F E := by
  set s := Module.finrank F E with hs
  have hχE : orderOf (liftNorm (E := E) χ) = 4 := by
    rw [← liftNormHom_apply, orderOf_injective _ liftNorm_injective, hχ]
  have h4E : 4 ∣ Fintype.card E - 1 := dvd_card_extension_sub_one h4
  have hN := numLastEntry_eq_re h4E hχE
  have h1 : χ ≠ 1 := by rintro rfl; simp at hχ
  have h2 : χ ^ 2 ≠ 1 := by
    intro h; have := orderOf_le_of_pow_eq_one (by norm_num) h; omega
  have h3 : χ ^ 2 * χ ≠ 1 := by
    rw [← pow_succ]; intro h; have := orderOf_le_of_pow_eq_one (by norm_num) h; omega
  have hne : ∀ k : Fin 2, ![χ ^ 2, χ] k ≠ 1 := by
    intro k; fin_cases k
    · simpa using h2
    · simpa using h1
  have hprod : ∏ k, ![χ ^ 2, χ] k ≠ 1 := by
    rw [Fin.prod_univ_two]; simpa using h3
  have hJE : multiJacobiSum ![liftNorm (E := E) χ ^ 2, liftNorm χ] =
      (-1) ^ ((s - 1) * 1) * multiJacobiSum ![χ ^ 2, χ] ^ s := by
    have := multiJacobiSum_liftNorm (E := E) hne hprod
    have e : (fun i => liftNorm (E := E) (![χ ^ 2, χ] i)) = ![liftNorm χ ^ 2, liftNorm χ] := by
      funext i; fin_cases i
      · simp [← liftNormHom_apply, map_pow]
      · simp
    rw [e] at this
    exact this
  rw [hN, card_extension (F := F), hJE, ← hs]
  set J := multiJacobiSum ![χ ^ 2, χ]
  have hc := Complex.add_conj ((-1) ^ ((s - 1) * 1) * J ^ s)
  push_cast at hc ⊢
  obtain ⟨t, ht⟩ : ∃ t, s = t + 1 := ⟨s - 1, by have := Module.finrank_pos (R := F) (M := E); omega⟩
  rw [ht] at hc ⊢
  simp only [Nat.add_sub_cancel, mul_one, map_mul, map_pow, map_neg, map_one] at hc ⊢
  rw [neg_pow J, neg_pow (starRingEnd ℂ J)]
  linear_combination -hc

/-- **The zeta function of the curve of §11.5** over any finite field with `q ≡ 1 (mod 4)`:
`Z(u) (1 - qu) = (1 - u)(1 - πu)(1 - π̄u)`, `π = -J(ρ, χ)`. -/
theorem zeta_lastEntry (Ext : ℕ → Type*) [∀ s, Field (Ext s)] [∀ s, Fintype (Ext s)]
    [∀ s, Algebra F (Ext s)] (hE : ∀ s, 1 ≤ s → Module.finrank F (Ext s) = s)
    (h4 : 4 ∣ Fintype.card F - 1) {χ : MulChar F ℂ} (hχ : orderOf χ = 4) :
    zetaOfCounts (fun s => (numLastEntry (Ext s) : ℂ)) * (1 - C (Fintype.card F : ℂ) * X) =
      (1 - X) * ((1 - C (-multiJacobiSum ![χ ^ 2, χ]) * X) *
        (1 - C (starRingEnd ℂ (-multiJacobiSum ![χ ^ 2, χ])) * X)) := by
  have := (zetaOfCounts_mul_eq_iff (fun s => (numLastEntry (Ext s) : ℂ))
    {1, -multiJacobiSum ![χ ^ 2, χ], starRingEnd ℂ (-multiJacobiSum ![χ ^ 2, χ])}
    {(Fintype.card F : ℂ)}).mpr (by
      intro s hs
      rw [numLastEntry_extension (E := Ext s) h4 hχ, hE s hs]
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
        Multiset.sum_cons, Multiset.sum_singleton, one_pow]
      ring)
  simpa [Multiset.insert_eq_cons] using this

/-- **Gauss's last entry, the zeta function** (Theorem of §11.5): for `p ≡ 1 (mod 4)` prime and the
normalized `a` (`p = a² + b²`, `a` odd, `b` even, `a ≡ 1 (mod 4)` iff `4 ∣ b`), the zeta function
of `x²t² + y²t² + x²y² - t⁴ = 0` over `𝔽_p` is `(1 - 2au + pu²)(1 - u) / (1 - pu)`. Here the
extensions of degree `s` are any family `E s` of fields with `[E s : 𝔽_p] = s`. -/
@[kb "irelandrosen1990" "Theorem (§11.5), p. 177"]
theorem gauss_last_entry_zeta {p : ℕ} [Fact p.Prime] (hp : p % 4 = 1)
    (Ext : ℕ → Type*) [∀ s, Field (Ext s)] [∀ s, Fintype (Ext s)] [∀ s, Algebra (ZMod p) (Ext s)]
    (hE : ∀ s, 1 ≤ s → Module.finrank (ZMod p) (Ext s) = s) {a b : ℤ}
    (hq : (p : ℤ) = a ^ 2 + b ^ 2) (hbe : Even b) (h4b : 4 ∣ b → a ≡ 1 [ZMOD 4])
    (h4b' : ¬4 ∣ b → a ≡ -1 [ZMOD 4]) :
    zetaOfCounts (fun s => (numLastEntry (Ext s) : ℂ)) * (1 - C (p : ℂ) * X) =
      (1 - C (2 * (a : ℂ)) * X + C (p : ℂ) * X ^ 2) * (1 - X) := by
  have h4 : 4 ∣ Fintype.card (ZMod p) - 1 := by rw [ZMod.card]; omega
  obtain ⟨χ, hχ⟩ := exists_orderOf_eq h4
  obtain ⟨a0, b0, hπ, hq0, hcong, -⟩ := numLastEntry_eq_of_quartic h4 hχ
  rw [ZMod.card] at hq0
  obtain ⟨hao0, -, h4b0, h4b0'⟩ := lastEntry_lemma hcong
  have haa : a = a0 := lastEntry_normalized_unique Fact.out hq0 hao0 h4b0 h4b0' hq hbe h4b h4b'
  subst haa
  have hz := zeta_lastEntry Ext hE h4 hχ
  rw [ZMod.card, hπ] at hz
  rw [hz]
  have hconj : starRingEnd ℂ ((a : ℂ) + b0 * Complex.I) = a - b0 * Complex.I := by
    simp; ring
  rw [hconj]
  have hpC : (p : ℂ) = (a : ℂ) ^ 2 + (b0 : ℂ) ^ 2 := by exact_mod_cast hq0
  have hCI : (C Complex.I : ℂ⟦X⟧) ^ 2 = -1 := by rw [← map_pow, Complex.I_sq, map_neg, map_one]
  have hC2 : (C (2 : ℂ) : ℂ⟦X⟧) = 2 := map_ofNat _ 2
  rw [hpC]
  simp only [map_add, map_sub, map_mul, map_pow, hC2]
  linear_combination (-(C (b0 : ℂ)) ^ 2 * X ^ 2 * (1 - X)) * hCI

end NTKB.IrelandRosen
