/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.ContinuedFractions.Infinite

/-!
# Equivalent numbers (Hardy–Wright, Chapter X, §§ 10.10 and 10.11)

`ξ` is *equivalent* to `η` if `ξ = (aη + b)/(cη + d)` with integers `a, b, c, d`, `ad - bc = ±1`
(Hardy–Wright § 10.11; we require `cη + d ≠ 0`, so that the quotient is a genuine one).

* Theorem 172: if `x = (Pζ + R)/(Qζ + S)` with `ζ > 1`, `Q > S > 0`, `PS - QR = ±1`, then `R/S` and
  `P/Q` are consecutive convergents `p_{n-1}/q_{n-1}`, `pₙ/qₙ` of a simple continued fraction
  `[a₀, …, aₙ]` with `x = [a₀, …, aₙ, ζ]`; if `ζ` is irrational, `ζ` is the `(n+1)`-th complete quotient
  of the continued fraction of `x`.
* Theorem 173: equivalence is transitive (and symmetric, and reflexive).
* Theorem 174: any two rational numbers are equivalent.
* Theorem 175: two irrational numbers are equivalent if and only if their continued fractions have the same
  tail.
-/

namespace NTKB.HardyWright

open GenContFract Filter Topology

/-- `ξ` is equivalent to `η` (Hardy–Wright § 10.11): `ξ = (aη + b)/(cη + d)` with integers `a, b, c, d`,
`ad - bc = ±1` and `cη + d ≠ 0`. -/
def IsEquivalent (ξ η : ℝ) : Prop :=
  ∃ a b c d : ℤ, (a * d - b * c = 1 ∨ a * d - b * c = -1) ∧ (c * η + d : ℝ) ≠ 0 ∧
    ξ = (a * η + b) / (c * η + d)

lemma IsEquivalent.refl (ξ : ℝ) : IsEquivalent ξ ξ :=
  ⟨1, 0, 0, 1, Or.inl (by ring), by simp, by simp⟩

/-- Equivalence is symmetric (Hardy–Wright § 10.11). -/
lemma IsEquivalent.symm {ξ η : ℝ} (h : IsEquivalent ξ η) : IsEquivalent η ξ := by
  obtain ⟨a, b, c, d, hdet, hne, rfl⟩ := h
  have hdet' : ((a * d - b * c : ℤ) : ℝ) ≠ 0 := by rcases hdet with h | h <;> rw [h] <;> norm_num
  push_cast at hdet'
  generalize hD : (c : ℝ) * η + d = D at hne ⊢
  have key : -(c : ℝ) * ((a * η + b) / D) + a = (a * d - b * c) / D := by
    rw [eq_div_iff hne, add_mul, mul_assoc, div_mul_cancel₀ _ hne, ← hD]; ring
  have hne' : -(c : ℝ) * ((a * η + b) / D) + a ≠ 0 := by rw [key]; exact div_ne_zero hdet' hne
  refine ⟨d, -b, -c, a, by rcases hdet with h | h <;> [left; right] <;> linear_combination h, by
    push_cast; exact hne', ?_⟩
  push_cast
  rw [key, eq_div_iff (div_ne_zero hdet' hne), mul_div_assoc', mul_div_assoc', div_add' _ _ _ hne,
    div_left_inj' hne, ← hD]
  ring

/-- **Theorem 173.** If `ξ` and `η` are equivalent, and `η` and `ζ` are equivalent, then `ξ` and `ζ` are
equivalent. -/
@[kb "hardywright2008" "Thm 173, p. 181"]
theorem IsEquivalent.trans {ξ η ζ : ℝ} (h₁ : IsEquivalent ξ η) (h₂ : IsEquivalent η ζ) :
    IsEquivalent ξ ζ := by
  obtain ⟨a, b, c, d, hdet, hne, rfl⟩ := h₁
  obtain ⟨a', b', c', d', hdet', hE, rfl⟩ := h₂
  generalize hN : (a' : ℝ) * ζ + b' = N at hne ⊢
  generalize hE' : (c' : ℝ) * ζ + d' = E at hne hE ⊢
  have e1 : (a : ℝ) * (N / E) + b = (a * N + b * E) / E := by field_simp
  have e2 : (c : ℝ) * (N / E) + d = (c * N + d * E) / E := by field_simp
  rw [e2] at hne
  have hcd : (c : ℝ) * N + d * E ≠ 0 := fun h ↦ hne (by rw [h, zero_div])
  have hden : ((c * a' + d * c' : ℤ) : ℝ) * ζ + ((c * b' + d * d' : ℤ) : ℝ) = c * N + d * E := by
    rw [← hN, ← hE']; push_cast; ring
  refine ⟨a * a' + b * c', a * b' + b * d', c * a' + d * c', c * b' + d * d', ?_, ?_, ?_⟩
  · have : (a * a' + b * c') * (c * b' + d * d') - (a * b' + b * d') * (c * a' + d * c') =
        (a * d - b * c) * (a' * d' - b' * c') := by ring
    rw [this]
    rcases hdet with h | h <;> rcases hdet' with h' | h' <;> rw [h, h'] <;> norm_num
  · rw [hden]; exact hcd
  · rw [hden, e1, e2, div_div_div_cancel_right₀ hE]
    congr 1
    rw [← hN, ← hE']; push_cast; ring

/-- **Theorem 174.** Any two rational numbers are equivalent. -/
@[kb "hardywright2008" "Thm 174, p. 182"]
theorem isEquivalent_rat (r s : ℚ) : IsEquivalent r s := by
  -- every rational `h/k` is equivalent to `0`
  have key : ∀ r : ℚ, IsEquivalent r 0 := by
    intro r
    obtain ⟨u, v, huv⟩ := Rat.isCoprime_num_den r
    refine ⟨v, r.num, -u, r.den, Or.inl ?_, by simp, ?_⟩
    · linear_combination huv
    · simp only [mul_zero, zero_add]
      exact_mod_cast (Rat.num_div_den r).symm
  exact (key r).trans (key s).symm

/-! ### Theorem 172 -/

/-- Two coprime representations `P/Q = p/q` with positive denominators are equal. -/
lemma eq_of_div_eq_div {P Q p q : ℤ} (hPQ : IsCoprime P Q) (hpq : IsCoprime p q) (hQ : 0 < Q)
    (hq : 0 < q) (h : (P : ℝ) / Q = p / q) : P = p ∧ Q = q := by
  have hQ' : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [div_eq_div_iff hQ' hq'] at h
  have h' : P * q = p * Q := by exact_mod_cast h
  have h1 : Q ∣ q := hPQ.symm.dvd_of_dvd_mul_left ⟨p, by linarith⟩
  have h2 : q ∣ Q := hpq.symm.dvd_of_dvd_mul_left ⟨P, by linarith⟩
  have hQq : Q = q := Int.dvd_antisymm hQ.le hq.le h1 h2
  subst hQq
  refine ⟨?_, rfl⟩
  have := mul_right_cancel₀ hQ.ne' (h'.trans (mul_comm p Q) |>.trans (mul_comm Q p))
  exact this

/-- A non-integral rational number has a simple expansion `[a₀, …, a_{m+1}]` whose determinant sign
`(-1)^m` is any prescribed `s = ±1` (Theorems 158 and 162). -/
lemma exists_cf_rat_sign (x : ℚ) (hx : ∀ z : ℤ, (x : ℝ) ≠ z) (s : ℤ) (hs : s = 1 ∨ s = -1) :
    ∃ (m : ℕ) (a : ℕ → ℤ), (∀ i, 1 ≤ i → i ≤ m + 1 → 0 < a i) ∧
      (cf (fun i ↦ (a i : ℝ))).convs (m + 1) = x ∧ (-1) ^ m = s := by
  obtain ⟨N, a, M, b, ha, hax, -, hb, hbx, -, -, hMN, -⟩ := cf_rat_two_expansions x
  have hN : N ≠ 0 := by
    rintro rfl
    exact hx (a 0) (by rw [← hax, cf_convs_zero])
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  have hpm : (-1 : ℤ) ^ m = 1 ∨ (-1 : ℤ) ^ m = -1 := by
    rcases neg_one_pow_eq_or ℤ m with h | h <;> simp [h]
  by_cases h : (-1 : ℤ) ^ m = s
  · exact ⟨m, a, ha, hax, h⟩
  · subst hMN
    refine ⟨m + 1, b, hb, hbx, ?_⟩
    rw [pow_succ]
    rcases hpm with h' | h' <;> rcases hs with hs | hs <;> rw [h'] at h ⊢ <;> simp_all

/-- **Theorem 172.** If `x = (Pζ + R)/(Qζ + S)`, where `ζ > 1` and `P, Q, R, S` are integers with
`Q > S > 0`, `PS - QR = ±1`, then `R/S` and `P/Q` are two consecutive convergents `p_m/q_m`, `p_{m+1}/q_{m+1}`
of a simple continued fraction `[a₀, …, a_{m+1}]`, and `x = [a₀, …, a_{m+1}, ζ]`. -/
@[kb "hardywright2008" "Thm 172, p. 180"]
theorem exists_cf_of_eq_moebius {x ζ : ℝ} {P Q R S : ℤ} (_hζ : 1 < ζ) (hQS : S < Q) (hS : 0 < S)
    (hdet : P * S - Q * R = 1 ∨ P * S - Q * R = -1) (hx : x = (P * ζ + R) / (Q * ζ + S)) :
    ∃ (m : ℕ) (a : ℕ → ℤ), (∀ i, 1 ≤ i → i ≤ m + 1 → 0 < a i) ∧
      (cf (fun i ↦ (a i : ℝ))).nums (m + 1) = P ∧ (cf (fun i ↦ (a i : ℝ))).dens (m + 1) = Q ∧
      (cf (fun i ↦ (a i : ℝ))).nums m = R ∧ (cf (fun i ↦ (a i : ℝ))).dens m = S ∧
      x = (cf (fun i ↦ if i ≤ m + 1 then (a i : ℝ) else ζ)).convs (m + 2) := by
  have hQ : 0 < Q := hS.trans hQS
  have hcop : IsCoprime P Q := by
    rcases hdet with h | h
    · exact ⟨S, -R, by linear_combination h⟩
    · exact ⟨-S, R, by linear_combination -h⟩
  -- `P/Q` is not an integer, since `Q > 1` and `(P, Q) = 1`
  have hnonint : ∀ z : ℤ, (((P / Q : ℚ)) : ℝ) ≠ z := by
    intro z hz
    push_cast at hz
    rw [div_eq_iff (by exact_mod_cast hQ.ne')] at hz
    have hz' : P = z * Q := by exact_mod_cast hz
    have : IsUnit Q := hcop.isUnit_of_dvd' ⟨z, by rw [hz', mul_comm]⟩ dvd_rfl
    rw [Int.isUnit_iff] at this
    omega
  obtain ⟨m, a, ha, hax, hsign⟩ := exists_cf_rat_sign (P / Q) hnonint (P * S - Q * R) hdet
  obtain ⟨p1, q1, hp1, hq1⟩ := cf_nums_dens_int a (m + 1)
  obtain ⟨p0, q0, hp0, hq0⟩ := cf_nums_dens_int a m
  have hpos := fun i h1 h2 ↦ (show (0 : ℝ) < a i by exact_mod_cast ha i h1 h2)
  have hq1pos : 0 < q1 := by
    have := cf_dens_pos hpos (m + 1) le_rfl
    rw [hq1] at this; exact_mod_cast this
  -- `P = p_{m+1}`, `Q = q_{m+1}`
  obtain ⟨hPp, hQq⟩ : P = p1 ∧ Q = q1 := by
    refine eq_of_div_eq_div hcop (cf_isCoprime_nums_dens a (m + 1) hp1 hq1) hQ hq1pos ?_
    rw [← hp1, ← hq1, ← cf_convs, hax]; push_cast; rfl
  subst hPp hQq
  -- the determinant gives `P (S - q_m) = Q (R - p_m)`
  have hdet' := cf_nums_mul_dens_sub (fun i ↦ (a i : ℝ)) m
  rw [hp1, hq1, hp0, hq0] at hdet'
  have hdetZ : P * q0 - p0 * Q = (-1) ^ m := by exact_mod_cast hdet'
  have hkey : P * (S - q0) = Q * (R - p0) := by linear_combination -hsign - hdetZ
  have hdvd : Q ∣ S - q0 := hcop.symm.dvd_of_dvd_mul_left ⟨R - p0, by linarith⟩
  -- `1 ≤ q_m ≤ q_{m+1} = Q`
  have hq0pos : 1 ≤ q0 := by
    have := cf_dens_one_le ha m (by omega)
    rw [hq0] at this; exact_mod_cast this
  have hq0le : q0 ≤ Q := by
    have := (cf_dens_le_dens_succ ha (n := m) le_rfl).1
    rw [hq0, hq1] at this; exact_mod_cast this
  have hSq : S = q0 := by
    obtain ⟨t, ht⟩ := hdvd
    have : t = 0 := by
      rcases lt_trichotomy t 0 with h | h | h
      · have : Q * t ≤ -Q := by nlinarith
        omega
      · exact h
      · have : Q ≤ Q * t := by nlinarith
        omega
    subst this; omega
  subst hSq
  have hRp : R = p0 := by
    have : Q * (R - p0) = 0 := by rw [← hkey]; ring
    rcases mul_eq_zero.mp this with h | h <;> omega
  subst hRp
  refine ⟨m, a, ha, hp1, hq1, hp0, hq0, ?_⟩
  -- `[a₀, …, a_{m+1}, ζ] = (ζ P + R)/(ζ Q + S)`
  have hc := cf_nums_dens_congr (a := fun i ↦ if i ≤ m + 1 then (a i : ℝ) else ζ)
    (b := fun i ↦ (a i : ℝ)) (N := m + 1) (fun i hi ↦ by simp [hi])
  rw [cf_convs, cf_nums_add_two, cf_dens_add_two, (hc (m + 1) le_rfl).1, (hc (m + 1) le_rfl).2,
    (hc m (by omega)).1, (hc m (by omega)).2, hp1, hq1, hp0, hq0, hx]
  simp only [show ¬(m + 2 ≤ m + 1) by omega, ite_false]
  ring_nf

/-- **Theorem 172** (infinite form). Under the hypotheses of Theorem 172, if `ζ = [c₀, c₁, …]` is the value
of an infinite simple continued fraction, then `x` is the value of a simple continued fraction
`[a₀, …, a_{m+1}, c₀, c₁, …]`, whose `m`-th and `(m+1)`-th convergents are `R/S` and `P/Q` and whose
`(m+2)`-th complete quotient is `ζ`. -/
theorem exists_cf_of_eq_moebius_infinite {x ζ : ℝ} {P Q R S : ℤ} (hζ : 1 < ζ) (hQS : S < Q)
    (hS : 0 < S) (hdet : P * S - Q * R = 1 ∨ P * S - Q * R = -1)
    (hx : x = (P * ζ + R) / (Q * ζ + S)) {c : ℕ → ℤ} (hc : ∀ i, 1 ≤ i → 0 < c i)
    (hζc : Tendsto (fun t ↦ (cf (fun i ↦ (c i : ℝ))).convs t) atTop (𝓝 ζ)) :
    ∃ (m : ℕ) (a : ℕ → ℤ), (∀ i, 1 ≤ i → 0 < a i) ∧ (∀ i, a (m + 2 + i) = c i) ∧
      (cf (fun i ↦ (a i : ℝ))).nums (m + 1) = P ∧ (cf (fun i ↦ (a i : ℝ))).dens (m + 1) = Q ∧
      (cf (fun i ↦ (a i : ℝ))).nums m = R ∧ (cf (fun i ↦ (a i : ℝ))).dens m = S ∧
      Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 x) := by
  obtain ⟨m, a, ha, hp1, hq1, hp0, hq0, -⟩ := exists_cf_of_eq_moebius hζ hQS hS hdet hx
  have hc0 : 0 < c 0 := by
    have := (cf_floor_value_eq hc hζc).1
    rw [← this]; exact Int.floor_pos.mpr hζ.le
  set a' : ℕ → ℤ := fun i ↦ if i ≤ m + 1 then a i else c (i - (m + 2)) with ha'
  have ha'pos : ∀ i, 1 ≤ i → 0 < a' i := by
    intro i hi
    by_cases h : i ≤ m + 1
    · simp only [ha', h, ite_true]; exact ha i hi h
    · simp only [ha', h, ite_false]
      rcases Nat.eq_zero_or_pos (i - (m + 2)) with h' | h'
      · rw [h']; exact hc0
      · exact hc _ h'
  have htail : ∀ i, a' (m + 2 + i) = c i := by
    intro i; simp only [ha', show ¬(m + 2 + i ≤ m + 1) by omega, ite_false]; congr 1; omega
  have hcongr := cf_nums_dens_congr (a := fun i ↦ (a' i : ℝ)) (b := fun i ↦ (a i : ℝ)) (N := m + 1)
    (fun i hi ↦ by simp [ha', hi])
  refine ⟨m, a', ha'pos, htail, by rw [(hcongr (m + 1) le_rfl).1, hp1],
    by rw [(hcongr (m + 1) le_rfl).2, hq1], by rw [(hcongr m (by omega)).1, hp0],
    by rw [(hcongr m (by omega)).2, hq0], ?_⟩
  obtain ⟨v, hv⟩ := cf_convs_tendsto ha'pos
  have hy : Tendsto (fun t ↦ (cf (fun i ↦ ((a' (m + 1 + 1 + i) : ℤ) : ℝ))).convs t) atTop (𝓝 ζ) := by
    have e : (fun i ↦ ((a' (m + 1 + 1 + i) : ℤ) : ℝ)) = fun i ↦ (c i : ℝ) := by
      funext i; rw [show m + 1 + 1 + i = m + 2 + i by ring, htail]
    rw [e]; exact hζc
  have e := cf_value_eq_completeQuotient ha'pos hv (m + 1) hy
  have h1 : ((cf (fun i ↦ (a' i : ℝ))).contsAux (m + 1 + 1)).a = P := by
    rw [← nth_cont_eq_succ_nth_contAux, ← num_eq_conts_a, (hcongr (m + 1) le_rfl).1, hp1]
  have h2 : ((cf (fun i ↦ (a' i : ℝ))).contsAux (m + 1 + 1)).b = Q := by
    rw [← nth_cont_eq_succ_nth_contAux, ← den_eq_conts_b, (hcongr (m + 1) le_rfl).2, hq1]
  have h3 : ((cf (fun i ↦ (a' i : ℝ))).contsAux (m + 1)).a = R := by
    rw [← nth_cont_eq_succ_nth_contAux, ← num_eq_conts_a, (hcongr m (by omega)).1, hp0]
  have h4 : ((cf (fun i ↦ (a' i : ℝ))).contsAux (m + 1)).b = S := by
    rw [← nth_cont_eq_succ_nth_contAux, ← den_eq_conts_b, (hcongr m (by omega)).2, hq0]
  rw [h1, h2, h3, h4] at e
  rw [hx, show (P * ζ + R : ℝ) = ζ * P + R by ring, show (Q * ζ + S : ℝ) = ζ * Q + S by ring, ← e]
  exact hv

/-! ### Theorem 175 -/

/-- An irrational number is equivalent to each of its complete quotients `a'_{n+2}`. -/
lemma isEquivalent_completeQuotient {a : ℕ → ℤ} (ha : ∀ i, 1 ≤ i → 0 < a i) {x : ℝ}
    (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 x)) (n : ℕ) {y : ℝ}
    (hy : Tendsto (fun t ↦ (cf (fun i ↦ ((a (n + 2 + i) : ℤ) : ℝ))).convs t) atTop (𝓝 y)) :
    IsEquivalent x y := by
  have hy' : Tendsto (fun t ↦ (cf (fun i ↦ ((a (n + 1 + 1 + i) : ℤ) : ℝ))).convs t) atTop (𝓝 y) := by
    simpa only [show n + 1 + 1 = n + 2 by ring] using hy
  have e := cf_value_eq_completeQuotient ha hx (n + 1) hy'
  obtain ⟨p1, q1, hp1, hq1⟩ := cf_nums_dens_int a (n + 1)
  obtain ⟨p0, q0, hp0, hq0⟩ := cf_nums_dens_int a n
  rw [← nth_cont_eq_succ_nth_contAux, ← nth_cont_eq_succ_nth_contAux, ← num_eq_conts_a,
    ← num_eq_conts_a, ← den_eq_conts_b, ← den_eq_conts_b, hp1, hq1, hp0, hq0] at e
  have hdet := cf_nums_mul_dens_sub (fun i ↦ (a i : ℝ)) n
  rw [hp1, hq1, hp0, hq0] at hdet
  have hdetZ : p1 * q0 - p0 * q1 = (-1) ^ n := by exact_mod_cast hdet
  have hp := pos_fin ha (n + 2)
  have hq1pos : (0 : ℝ) < q1 := by rw [← hq1]; exact cf_dens_pos hp (n + 1) (by omega)
  have hq0pos : (0 : ℝ) < q0 := by rw [← hq0]; exact cf_dens_pos hp n (by omega)
  have hy1 : 0 < y := by
    have := (cf_value_mem_Ioo (fun i hi ↦ ha (n + 2 + i) (by omega)) hy).1
    have h : (1 : ℤ) ≤ a (n + 2 + 0) := ha (n + 2 + 0) (by omega)
    have h' : (1 : ℝ) ≤ a (n + 2 + 0) := by exact_mod_cast h
    linarith
  refine ⟨p1, p0, q1, q0, ?_, by positivity, ?_⟩
  · rcases neg_one_pow_eq_or ℤ n with h | h <;> rw [h] at hdetZ <;> [left; right] <;> exact hdetZ
  · rw [e]; ring

/-- **Theorem 175.** Two irrational numbers `ξ = [a₀, a₁, …]` and `η = [b₀, b₁, …]` are equivalent if and
only if the sequence of quotients of `ξ` after the `m`-th is the same as the sequence of quotients of `η`
after the `n`-th, for some `m` and `n`. -/
@[kb "hardywright2008" "Thm 175, p. 182"]
theorem isEquivalent_iff_tail_eq {a b : ℕ → ℤ} (ha : ∀ i, 1 ≤ i → 0 < a i)
    (hb : ∀ i, 1 ≤ i → 0 < b i) {ξ η : ℝ}
    (hξ : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 ξ))
    (hη : Tendsto (fun t ↦ (cf (fun i ↦ (b i : ℝ))).convs t) atTop (𝓝 η)) :
    IsEquivalent ξ η ↔ ∃ m n : ℕ, ∀ i, a (m + i) = b (n + i) := by
  constructor
  · rintro ⟨A, B, C, D, hdet, hne, hξη⟩
    have hirr := ((irrational_iff_exists_unique_cf ξ).2 a ha hξ)
    -- `η = (A' ξ + B')/(C' ξ + D')` with `C' ξ + D' > 0`
    have hη' := (IsEquivalent.symm ⟨A, B, C, D, hdet, hne, hξη⟩)
    obtain ⟨A, B, C, D, hdet, hne, hηξ⟩ := hη'
    obtain ⟨A, B, C, D, hdet, hL, hηξ⟩ : ∃ A B C D : ℤ, (A * D - B * C = 1 ∨ A * D - B * C = -1) ∧
        (0 : ℝ) < C * ξ + D ∧ η = (A * ξ + B) / (C * ξ + D) := by
      rcases lt_or_gt_of_ne hne with h | h
      · refine ⟨-A, -B, -C, -D, by rcases hdet with h' | h' <;> [left; right] <;> linear_combination h',
          by push_cast; linarith, ?_⟩
        rw [hηξ]; push_cast
        rw [show -(A : ℝ) * ξ + -B = -(A * ξ + B) by ring,
          show -(C : ℝ) * ξ + -D = -(C * ξ + D) by ring, neg_div_neg_eq]
      · exact ⟨A, B, C, D, hdet, h, hηξ⟩
    set L := (C : ℝ) * ξ + D with hLdef
    -- choose `n` large
    obtain ⟨n, hn⟩ := exists_nat_gt (2 * |(C : ℝ)| / L + 2)
    obtain ⟨p1, q1, hp1, hq1⟩ := cf_nums_dens_int a (n + 1)
    obtain ⟨p0, q0, hp0, hq0⟩ := cf_nums_dens_int a n
    -- the complete quotient `ζ = a'_{n+2}`
    have hpt : ∀ i, 1 ≤ i → 0 < a (n + 2 + i) := fun i hi ↦ ha (n + 2 + i) (by omega)
    obtain ⟨ζ, hζ⟩ := cf_convs_tendsto hpt
    have hζ' : Tendsto (fun t ↦ (cf (fun i ↦ ((a (n + 1 + 1 + i) : ℤ) : ℝ))).convs t) atTop (𝓝 ζ) := by
      simpa only [show n + 1 + 1 = n + 2 by ring] using hζ
    have e := cf_value_eq_completeQuotient ha hξ (n + 1) hζ'
    rw [← nth_cont_eq_succ_nth_contAux, ← nth_cont_eq_succ_nth_contAux, ← num_eq_conts_a,
      ← num_eq_conts_a, ← den_eq_conts_b, ← den_eq_conts_b, hp1, hq1, hp0, hq0] at e
    have hζ1 : 1 < ζ := by
      have := (cf_value_mem_Ioo (fun i hi ↦ ha (n + 2 + i) (by omega)) hζ).1
      have h : (1 : ℝ) ≤ a (n + 2 + 0) := by exact_mod_cast ha (n + 2 + 0) (by omega)
      linarith
    have hp := pos_fin ha (n + 3)
    have hq1pos : (0 : ℝ) < q1 := by rw [← hq1]; exact cf_dens_pos hp (n + 1) (by omega)
    have hq0pos : (0 : ℝ) < q0 := by rw [← hq0]; exact cf_dens_pos hp n (by omega)
    -- `|qₖ ξ - pₖ| < 1`
    have herr : ∀ k, |(cf (fun i ↦ (a i : ℝ))).dens k * ξ - (cf (fun i ↦ (a i : ℝ))).nums k| < 1 := by
      intro k
      obtain ⟨D', hD1, -, -, e2⟩ := cf_sub_convs_eq ha hξ k
      have hq := cf_dens_one_le (pos_finZ ha (k + 1)) (k + 1) le_rfl
      rw [e2, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos (by linarith)]
      rw [div_lt_one (by linarith)]; linarith
    have herr1 := herr (n + 1)
    have herr0 := herr n
    rw [hp1, hq1] at herr1
    rw [hp0, hq0] at herr0
    -- `q_{n+1} - q_n ≥ q_{n-1} ≥ n - 1`, `q_n ≥ n`
    have hqn : (n : ℝ) ≤ q0 := by rw [← hq0]; exact (cf_le_dens (pos_finZ ha n) le_rfl).1
    have hgap : (n : ℝ) - 1 ≤ q1 - q0 := by
      rcases n with _ | n
      · have := cf_dens_le_dens_succ (pos_finZ ha 1) (n := 0) le_rfl
        rw [hq1, hq0] at this; push_cast; linarith [this.1]
      · have h2 := cf_dens_add_two (fun i ↦ (a i : ℝ)) n
        have h3 := (cf_le_dens (pos_finZ ha n) (n := n) le_rfl).1
        have h5 : (1 : ℝ) ≤ a (n + 2) := by exact_mod_cast ha (n + 2) (by omega)
        rw [show n + 1 + 1 = n + 2 from rfl] at hq1
        rw [hq1, hq0] at h2
        push_cast
        nlinarith [hq0pos]
    -- the integers `P, Q, R, S`
    set P := A * p1 + B * q1
    set Q := C * p1 + D * q1
    set R := A * p0 + B * q0
    set S := C * p0 + D * q0
    have hQr : (Q : ℝ) = L * q1 + C * (p1 - q1 * ξ) := by simp only [Q, hLdef]; push_cast; ring
    have hSr : (S : ℝ) = L * q0 + C * (p0 - q0 * ξ) := by simp only [S, hLdef]; push_cast; ring
    have hCb1 : |(C : ℝ) * (p1 - q1 * ξ)| ≤ |(C : ℝ)| := by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (by rw [abs_sub_comm]; exact herr1.le)
    have hCb0 : |(C : ℝ) * (p0 - q0 * ξ)| ≤ |(C : ℝ)| := by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (by rw [abs_sub_comm]; exact herr0.le)
    have hn' : 2 * |(C : ℝ)| < L * ((n : ℝ) - 2) := by
      rw [div_add' _ _ _ hL.ne', div_lt_iff₀ hL] at hn
      nlinarith
    have hS0 : (0 : ℝ) < S := by
      rw [hSr]
      have := abs_le.mp hCb0
      nlinarith [abs_nonneg (C : ℝ)]
    have hQS : (S : ℝ) < Q := by
      rw [hQr, hSr]
      have := abs_le.mp hCb0
      have := abs_le.mp hCb1
      nlinarith [abs_nonneg (C : ℝ)]
    have hdetPQ : P * S - Q * R = 1 ∨ P * S - Q * R = -1 := by
      have hdetZ : p1 * q0 - p0 * q1 = (-1) ^ n := by
        have := cf_nums_mul_dens_sub (fun i ↦ (a i : ℝ)) n
        rw [hp1, hq1, hp0, hq0] at this; exact_mod_cast this
      have : P * S - Q * R = (A * D - B * C) * (p1 * q0 - p0 * q1) := by
        simp only [P, Q, R, S]; ring
      rw [this, hdetZ]
      rcases hdet with h | h <;> rcases neg_one_pow_eq_or ℤ n with h' | h' <;> rw [h, h'] <;> norm_num
    have hηPQ : η = (P * ζ + R) / (Q * ζ + S) := by
      have hW : (0 : ℝ) < ζ * q1 + q0 := by nlinarith
      have hWne := hW.ne'
      have e1 : (A : ℝ) * ξ + B = (P * ζ + R) / (ζ * q1 + q0) := by
        rw [e, eq_div_iff hWne]; simp only [P, R]; push_cast; field_simp; ring
      have e2 : (C : ℝ) * ξ + D = (Q * ζ + S) / (ζ * q1 + q0) := by
        rw [e, eq_div_iff hWne]; simp only [Q, S]; push_cast; field_simp; ring
      rw [hηξ, hLdef, e1, e2, div_div_div_cancel_right₀ hWne]
    obtain ⟨m, c, hc, htail, -, -, -, -, hcη⟩ := exists_cf_of_eq_moebius_infinite hζ1
      (by exact_mod_cast hQS) (by exact_mod_cast hS0) hdetPQ hηPQ (c := fun i ↦ a (n + 2 + i))
      (fun i hi ↦ ha (n + 2 + i) (by omega)) hζ
    have hbc := cf_eq_of_tendsto hb hc hη hcη
    subst hbc
    exact ⟨n + 2, m + 2, fun i ↦ (htail i).symm⟩
  · rintro ⟨m, n, h⟩
    have hpt : ∀ i, 1 ≤ i → 0 < a (m + 2 + i) := fun i hi ↦ ha (m + 2 + i) (by omega)
    obtain ⟨ω, hω⟩ := cf_convs_tendsto hpt
    have hω' : Tendsto (fun t ↦ (cf (fun i ↦ ((b (n + 2 + i) : ℤ) : ℝ))).convs t) atTop (𝓝 ω) := by
      have e : (fun i ↦ ((b (n + 2 + i) : ℤ) : ℝ)) = fun i ↦ ((a (m + 2 + i) : ℤ) : ℝ) := by
        funext i; rw [show m + 2 + i = m + (2 + i) by ring, h, show n + (2 + i) = n + 2 + i by ring]
      rw [e]; exact hω
    exact (isEquivalent_completeQuotient ha hξ m hω).trans
      (isEquivalent_completeQuotient hb hη n hω').symm

end NTKB.HardyWright
