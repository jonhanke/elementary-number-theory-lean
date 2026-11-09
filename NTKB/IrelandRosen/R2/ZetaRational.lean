/-
Ireland–Rosen, Chapter 11, §1: Proposition 11.1.1 in the book's form — the zeta function is a
rational function iff `N_s = ∑ β_j^s - ∑ α_i^s` for finitely many complex `α_i, β_j` — together
with Exercise 11.1 (a rational power series with constant term `1` is `P/Q` with
`P(0) = Q(0) = 1`).
-/
import NTKB.IrelandRosen.R2.ZetaSeries
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

open PowerSeries

namespace NTKB.IrelandRosen

/-- A power series is rational if `Z Q = P` for polynomials `P`, `Q` with `Q ≠ 0`. -/
def IsRationalSeries (Z : ℂ⟦X⟧) : Prop :=
  ∃ P Q : Polynomial ℂ, Q ≠ 0 ∧ Z * (Q : ℂ⟦X⟧) = (P : ℂ⟦X⟧)

/-- The coercion of `∏ (1 - r x)`. -/
lemma coe_prod_one_sub (R : Multiset ℂ) :
    (((R.map fun r => (1 - Polynomial.C r * Polynomial.X : Polynomial ℂ)).prod : Polynomial ℂ) :
        ℂ⟦X⟧) = (R.map fun r => (1 - C r * X : ℂ⟦X⟧)).prod := by
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_multiset_prod, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun r _ => ?_
  simp [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, Polynomial.coe_X]

/-- Over `ℂ`, a nonzero polynomial is `c X^k ∏ (1 - r X)`. -/
lemma exists_factor (f : Polynomial ℂ) (hf : f ≠ 0) :
    ∃ (c : ℂ) (k : ℕ) (R : Multiset ℂ), c ≠ 0 ∧
      f = Polynomial.C c * Polynomial.X ^ k *
        (R.map fun r => (1 - Polynomial.C r * Polynomial.X : Polynomial ℂ)).prod := by
  classical
  have hs := (IsAlgClosed.splits f).eq_prod_roots
  set rts := f.roots
  have hsplit := Multiset.filter_add_not (fun r : ℂ => r = 0) rts
  have h0 : rts.filter (fun r => r = 0) = Multiset.replicate (rts.count 0) 0 := by
    rw [Multiset.filter_eq']
  refine ⟨f.leadingCoeff * ((rts.filter fun r => ¬r = 0).map fun r => -r).prod, rts.count 0,
    (rts.filter fun r => ¬r = 0).map fun r => r⁻¹, ?_, ?_⟩
  · refine mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hf) ?_
    refine Multiset.prod_ne_zero ?_
    intro h
    obtain ⟨r, hr, hr0⟩ := Multiset.mem_map.mp h
    rw [Multiset.mem_filter] at hr
    exact hr.2 (neg_eq_zero.mp hr0)
  · conv_lhs => rw [hs, ← hsplit, Multiset.map_add, Multiset.prod_add, h0]
    simp only [Multiset.map_replicate, map_zero, sub_zero, Multiset.prod_replicate, map_mul,
      Multiset.map_map, Function.comp_def]
    have : ∀ r ∈ rts.filter (fun r => ¬r = 0),
        (Polynomial.X - Polynomial.C r : Polynomial ℂ) =
          Polynomial.C (-r) * (1 - Polynomial.C r⁻¹ * Polynomial.X) := by
      intro r hr
      rw [Multiset.mem_filter] at hr
      rw [mul_sub, mul_one, ← mul_assoc, ← map_mul, show -r * r⁻¹ = -1 by field_simp [hr.2],
        map_neg, map_neg, Polynomial.C_1]
      ring
    rw [Multiset.map_congr rfl this, Multiset.prod_map_mul]
    have hC : ((rts.filter fun r => ¬r = 0).map fun x => Polynomial.C (-x)).prod =
        Polynomial.C (((rts.filter fun r => ¬r = 0).map fun r => -r).prod) := by
      rw [map_multiset_prod, Multiset.map_map]; rfl
    rw [hC]; ring

/-- **Exercise 11.1 and the reduction in Proposition 11.1.1.** If `Z(0) = 1` and `Z Q = P` with
`Q ≠ 0`, then `Z ∏ (1 - β_j u) = ∏ (1 - α_i u)` for some complex `α_i, β_j`; in particular `Z = P'/Q'`
with `P'(0) = Q'(0) = 1`. -/
@[kb "irelandrosen1990" "Exercise 11.1, p. 180"]
theorem exists_mul_prod_eq_prod {Z : ℂ⟦X⟧} (hZ0 : constantCoeff Z = 1) (hZ : IsRationalSeries Z) :
    ∃ α β : Multiset ℂ, Z * (β.map fun b => (1 - C b * X : ℂ⟦X⟧)).prod =
      (α.map fun a => (1 - C a * X : ℂ⟦X⟧)).prod := by
  obtain ⟨P, Q, hQ, hPQ⟩ := hZ
  have hP : P ≠ 0 := by
    rintro rfl
    rw [Polynomial.coe_zero] at hPQ
    rcases mul_eq_zero.mp hPQ with h | h
    · rw [h, map_zero] at hZ0; exact zero_ne_one hZ0
    · exact hQ (Polynomial.coe_eq_zero_iff.mp h)
  obtain ⟨c, k, R, hc, hQf⟩ := exists_factor Q hQ
  obtain ⟨d, l, S, hd, hPf⟩ := exists_factor P hP
  rw [hQf, hPf] at hPQ
  simp only [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_C, Polynomial.coe_X,
    coe_prod_one_sub] at hPQ
  set B := (R.map fun r => (1 - C r * X : ℂ⟦X⟧)).prod
  set A := (S.map fun r => (1 - C r * X : ℂ⟦X⟧)).prod
  have hB0 : constantCoeff B = 1 := constantCoeff_prod_one_sub R
  have hA0 : constantCoeff A = 1 := constantCoeff_prod_one_sub S
  -- compare the orders at `X`
  have hkl : k = l := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · obtain ⟨m, rfl⟩ : ∃ m, l = k + m + 1 := ⟨l - k - 1, by omega⟩
      have : (X : ℂ⟦X⟧) ^ k * (Z * C c * B) = X ^ k * (C d * X ^ (m + 1) * A) := by
        rw [show k + m + 1 = k + (m + 1) by ring, pow_add] at hPQ
        linear_combination hPQ
      have h2 := mul_left_cancel₀ (pow_ne_zero k X_ne_zero) this
      have := congrArg constantCoeff h2
      simp [hZ0, hB0, hA0] at this
      exact hc this
    · obtain ⟨m, rfl⟩ : ∃ m, k = l + m + 1 := ⟨k - l - 1, by omega⟩
      have : (X : ℂ⟦X⟧) ^ l * (Z * C c * X ^ (m + 1) * B) = X ^ l * (C d * A) := by
        rw [show l + m + 1 = l + (m + 1) by ring, pow_add] at hPQ
        linear_combination hPQ
      have h2 := mul_left_cancel₀ (pow_ne_zero l X_ne_zero) this
      have := congrArg constantCoeff h2
      simp [hZ0, hB0, hA0] at this
      exact hd this.symm
  subst hkl
  have h1 : (X : ℂ⟦X⟧) ^ k * (C c * (Z * B)) = X ^ k * (C d * A) := by linear_combination hPQ
  have h2 := mul_left_cancel₀ (pow_ne_zero k X_ne_zero) h1
  have hcd : c = d := by
    have := congrArg constantCoeff h2
    simpa [hZ0, hB0, hA0] using this
  subst hcd
  have h3 := mul_left_cancel₀ (by simpa using hc : (C c : ℂ⟦X⟧) ≠ 0) h2
  exact ⟨S, R, h3⟩

/-- **Proposition 11.1.1** (with Exercise 11.2 for the converse). The zeta function is a rational
function iff there are finitely many complex numbers `α_i`, `β_j` with
`N_s = ∑ β_j^s - ∑ α_i^s` for all `s ≥ 1`. -/
@[kb "irelandrosen1990" "Prop 11.1.1, p. 166"]
theorem isRationalSeries_zetaOfCounts_iff (N : ℕ → ℂ) :
    IsRationalSeries (zetaOfCounts N) ↔
      ∃ α β : Multiset ℂ, ∀ s, 1 ≤ s → N s = (β.map fun b => b ^ s).sum -
        (α.map fun a => a ^ s).sum := by
  constructor
  · intro h
    obtain ⟨α, β, hαβ⟩ := exists_mul_prod_eq_prod (constantCoeff_zetaOfCounts N) h
    exact ⟨α, β, (zetaOfCounts_mul_eq_iff N α β).mp hαβ⟩
  · rintro ⟨α, β, h⟩
    have hz := (zetaOfCounts_mul_eq_iff N α β).mpr h
    refine ⟨(α.map fun r => (1 - Polynomial.C r * Polynomial.X : Polynomial ℂ)).prod,
      (β.map fun r => (1 - Polynomial.C r * Polynomial.X : Polynomial ℂ)).prod, ?_, ?_⟩
    · intro h0
      have := congrArg (Polynomial.eval 0) h0
      rw [Polynomial.eval_multiset_prod, Multiset.map_map] at this
      simp at this
    · rw [coe_prod_one_sub, coe_prod_one_sub]; exact hz

end NTKB.IrelandRosen
