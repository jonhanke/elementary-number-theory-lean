/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.NZM.Pell

/-!
# Purely periodic continued fractions (Niven–Zuckerman–Montgomery, Theorem 7.20)

**Theorem 7.20** (Galois). The continued fraction expansion of the real quadratic irrational `ξ` is purely
periodic if and only if `ξ > 1` and `-1 < ξ' < 0`, where `ξ'` is the conjugate of `ξ`.

We write the quadratic irrational as `ξ = (P + √D)/Q` with integers `P, Q`, `Q ≠ 0`, and a positive
integer `D` which is not a square; its conjugate is `ξ' = (P - √D)/Q`. The continued fraction of `ξ` is,
as in the Hardy–Wright files of `NTKB`, a sequence `a : ℕ → ℤ` with `aᵢ > 0` for `i ≥ 1` whose
convergents tend to `ξ`; "purely periodic" means `a_{i+r} = aᵢ` for all `i ≥ 0` and some `r ≥ 1`.

The proof is the book's. With `ξ₀ = ξ` written as `(m₀ + √d)/q₀`, `q₀ ∣ d - m₀²` (here `d = D Q²`,
`m₀ = P |Q|`, `q₀ = Q |Q|`), the recursion (7.13) gives the complete quotients `ξᵢ = (mᵢ + √d)/qᵢ`, and
their conjugates `ξ'ᵢ = (mᵢ - √d)/qᵢ` satisfy `ξ'_{i+1} = 1/(ξ'ᵢ - aᵢ)` (7.14).
* If `ξ > 1` and `-1 < ξ' < 0`, then by induction `ξᵢ > 1` and `-1 < ξ'ᵢ < 0` for all `i`, so
  `0 < mᵢ < √d` and `0 < qᵢ < 2√d`; two of the pairs `(mᵢ, qᵢ)` agree, `ξⱼ = ξₖ` with `j < k`, and
  `aᵢ₋₁ = ⌊-1/ξ'ᵢ⌋` lets us step back from `ξⱼ = ξₖ` to `ξ₀ = ξ_{k-j}`.
* If `ξ = ⟨\overline{a₀, …, a_{r-1}}⟩` then `ξ > a₀ ≥ 1` and `ξ = (ξ h_{r-1} + h_{r-2})/(ξ k_{r-1} + k_{r-2})`,
  so `ξ` and `ξ'` are the roots of `f(x) = k_{r-1}x² + (k_{r-2} - h_{r-1})x - h_{r-2}`; `f(0) < 0 < f(-1)`.
-/

namespace NTKB.NZM

open NTKB.HardyWright GenContFract Filter Topology

variable {d : ℕ} {m₀ q₀ : ℤ}

/-- The conjugates `ξ'ᵢ = (mᵢ - √d)/qᵢ` of the numbers of the recursion (7.13). -/
noncomputable def xiConj (d : ℕ) (m₀ q₀ : ℤ) (n : ℕ) : ℝ :=
  (((mq d m₀ q₀ n).1 : ℤ) - √(d : ℝ)) / ((mq d m₀ q₀ n).2 : ℤ)

/-- The algebra behind (7.7) and (7.14): if `m' = aq - m` and `q'q = d - m'²`, then for `s² = d`,
`(m' + s)/q' = 1/((m + s)/q - a)`. -/
lemma succ_aux {m q m' q' a s dd : ℝ} (hq : q ≠ 0) (hq' : q' ≠ 0) (hs : s ^ 2 = dd)
    (hne : s - m' ≠ 0) (hm : m' = a * q - m) (hmul : q' * q = dd - m' ^ 2) :
    (m' + s) / q' = 1 / ((m + s) / q - a) := by
  have e1 : (m + s) / q - a = (s - m') / q := by rw [hm]; field_simp; ring
  rw [e1, one_div_div, div_eq_div_iff hq' hne]
  linear_combination hs - hmul

/-- Equation (7.14): `ξ'_{i+1} = 1/(ξ'ᵢ - aᵢ)` with `aᵢ = ⌊ξᵢ⌋`. -/
theorem xiConj_succ (hd : ¬IsSquare d) (hq₀ : q₀ ≠ 0) (hdvd : q₀ ∣ d - m₀ ^ 2) (n : ℕ) :
    xiConj d m₀ q₀ (n + 1) = 1 / (xiConj d m₀ q₀ n - ⌊xi d m₀ q₀ n⌋) := by
  have hirr : Irrational √(d : ℝ) := irrational_sqrt_natCast_iff.mpr hd
  have hq := (mq_snd_ne_zero_dvd hd hq₀ hdvd n).1
  have hq1 := (mq_snd_ne_zero_dvd hd hq₀ hdvd (n + 1)).1
  have hmul : (((mq d m₀ q₀ (n + 1)).2 * (mq d m₀ q₀ n).2 : ℤ) : ℝ) =
      ((d - (mq d m₀ q₀ (n + 1)).1 ^ 2 : ℤ) : ℝ) := by
    exact_mod_cast mq_snd_mul hd hq₀ hdvd n
  have hm : (((mq d m₀ q₀ (n + 1)).1 : ℤ) : ℝ) =
      ((⌊xi d m₀ q₀ n⌋ * (mq d m₀ q₀ n).2 - (mq d m₀ q₀ n).1 : ℤ) : ℝ) := by
    exact_mod_cast mq_succ_fst n
  push_cast at hmul hm
  have hs : (-√(d : ℝ)) ^ 2 = d := by rw [neg_sq]; exact Real.sq_sqrt (by positivity)
  have hne : -√(d : ℝ) - (mq d m₀ q₀ (n + 1)).1 ≠ 0 := by
    intro h
    exact hirr ⟨-(mq d m₀ q₀ (n + 1)).1, by push_cast; linarith⟩
  simp only [xiConj, sub_eq_add_neg]
  exact succ_aux (by exact_mod_cast hq) (by exact_mod_cast hq1) hs (by simpa [sub_eq_add_neg] using hne)
    hm hmul

/-- With `ξ₀ = (m₀ + √d)/q₀` the recursion (7.13) gives the continued fraction of `ξ₀`: the `n`-th
quotient is `⌊ξₙ⌋` and the complete quotient `⟨aₙ, a_{n+1}, …⟩` is `ξₙ`. -/
theorem tail_tendsto_xi (hd : ¬IsSquare d) (hq₀ : q₀ ≠ 0) (hdvd : q₀ ∣ d - m₀ ^ 2) {a : ℕ → ℤ}
    (ha : ∀ i, 1 ≤ i → 0 < a i)
    (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 (xi d m₀ q₀ 0))) (n : ℕ) :
    Tendsto (fun t ↦ (cf (fun i ↦ ((a (n + i) : ℤ) : ℝ))).convs t) atTop (𝓝 (xi d m₀ q₀ n)) ∧
      a n = ⌊xi d m₀ q₀ n⌋ := by
  have key : ∀ n, Tendsto (fun t ↦ (cf (fun i ↦ ((a (n + i) : ℤ) : ℝ))).convs t) atTop
      (𝓝 (xi d m₀ q₀ n)) := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih =>
      have hb : ∀ i, 1 ≤ i → 0 < a (n + i) := fun i hi ↦ ha (n + i) (by omega)
      have h1 := cf_tendsto_tail hb ih
      have h0 : ⌊xi d m₀ q₀ n⌋ = a (n + 0) := (cf_floor_value_eq hb ih).1
      rw [xi_succ hd hq₀ hdvd n, h0]
      have e : (fun i ↦ ((a (n + 1 + i) : ℤ) : ℝ)) = fun i ↦ ((a (n + (i + 1)) : ℤ) : ℝ) := by
        funext i; congr 2; omega
      rw [e]
      exact h1
  refine ⟨key n, ?_⟩
  have hb : ∀ i, 1 ≤ i → 0 < a (n + i) := fun i hi ↦ ha (n + i) (by omega)
  simpa using ((cf_floor_value_eq hb (key n)).1).symm

/-- Two integers in an open interval of length `1` are equal. -/
lemma int_eq_of_mem_Ioo {u v : ℤ} {c : ℝ} (hu : c - 1 < u ∧ (u : ℝ) < c) (hv : c - 1 < v ∧ (v : ℝ) < c) :
    u = v := by
  have h1 : ((u - v : ℤ) : ℝ) < 1 := by push_cast; linarith
  have h2 : (-1 : ℝ) < ((u - v : ℤ) : ℝ) := by push_cast; linarith
  have h1' : u - v < 1 := by exact_mod_cast h1
  have h2' : -1 < u - v := by exact_mod_cast h2
  omega

/-- The "if" part of Theorem 7.20 for `ξ = (m₀ + √d)/q₀` with `q₀ ∣ d - m₀²`. -/
theorem purelyPeriodic_of_reduced (hd : ¬IsSquare d) (hq₀ : q₀ ≠ 0) (hdvd : q₀ ∣ d - m₀ ^ 2)
    {a : ℕ → ℤ} (ha : ∀ i, 1 ≤ i → 0 < a i)
    (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 (xi d m₀ q₀ 0)))
    (h1 : 1 < xi d m₀ q₀ 0) (h2 : -1 < xiConj d m₀ q₀ 0) (h3 : xiConj d m₀ q₀ 0 < 0) :
    ∃ r, 1 ≤ r ∧ ∀ i, a (i + r) = a i := by
  have hT := tail_tendsto_xi hd hq₀ hdvd ha hx
  have hxs := xi_succ hd hq₀ hdvd
  have hys := xiConj_succ hd hq₀ hdvd
  set x := xi d m₀ q₀
  set y := xiConj d m₀ q₀
  -- `aᵢ < ξᵢ < aᵢ + 1`
  have hI : ∀ i, (a i : ℝ) < x i ∧ x i < a i + 1 := by
    intro i
    have := cf_value_mem_Ioo (fun j hj ↦ ha (i + j) (by omega)) (hT i).1
    simpa using this
  -- the invariant `ξᵢ > 1`, `-1 < ξ'ᵢ < 0`
  have hinv : ∀ i, 1 < x i ∧ -1 < y i ∧ y i < 0 := by
    intro i
    induction i with
    | zero => exact ⟨h1, h2, h3⟩
    | succ i ih =>
      obtain ⟨hx1, hy1, hy2⟩ := ih
      have hai : (1 : ℝ) ≤ a i := by
        have := (hT i).2
        have h : (1 : ℤ) ≤ ⌊x i⌋ := Int.le_floor.mpr (by exact_mod_cast hx1.le)
        rw [← this] at h; exact_mod_cast h
      obtain ⟨hlo, hhi⟩ := hI i
      rw [hxs i, hys i, ← (hT i).2]
      refine ⟨?_, ?_, ?_⟩
      · rw [lt_div_iff₀ (by linarith)]; linarith
      · rw [lt_div_iff_of_neg (by linarith)]; linarith
      · exact div_neg_of_pos_of_neg one_pos (by linarith)
  -- bounds on `(mᵢ, qᵢ)`
  have hsd : (0 : ℝ) < √(d : ℝ) := by
    have : d ≠ 0 := by rintro rfl; exact hd ⟨0, rfl⟩
    exact Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero this)
  have hsdd : √(d : ℝ) ≤ d := by
    have : (1 : ℝ) ≤ d := by
      have : d ≠ 0 := by rintro rfl; exact hd ⟨0, rfl⟩
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ d by positivity), Real.sqrt_nonneg (d : ℝ)]
  have hbd : ∀ i, mq d m₀ q₀ i ∈ Finset.Icc (1 : ℤ) (2 * d) ×ˢ Finset.Icc (1 : ℤ) (2 * d) := by
    intro i
    obtain ⟨hx1, hy1, hy2⟩ := hinv i
    have hq := (mq_snd_ne_zero_dvd hd hq₀ hdvd i).1
    set m := (mq d m₀ q₀ i).1
    set q := (mq d m₀ q₀ i).2
    have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq
    have ex : x i = (m + √(d : ℝ)) / q := rfl
    have ey : y i = (m - √(d : ℝ)) / q := rfl
    -- `q > 0` from `ξᵢ - ξ'ᵢ = 2√d/q > 0`
    have hqpos : (0 : ℝ) < q := by
      have : x i - y i = 2 * √(d : ℝ) / q := by rw [ex, ey]; field_simp; ring
      have hp : 0 < 2 * √(d : ℝ) / q := by rw [← this]; linarith
      by_contra hc; push Not at hc
      exact absurd hp (not_lt.mpr (div_nonpos_of_nonneg_of_nonpos (by linarith) hc))
    rw [ex] at hx1; rw [ey] at hy1 hy2
    rw [lt_div_iff₀ hqpos] at hx1
    rw [lt_div_iff₀ hqpos] at hy1
    rw [div_lt_iff₀ hqpos] at hy2
    have hm1 : (0 : ℝ) < m := by linarith
    have hm2 : (m : ℝ) < √(d : ℝ) := by linarith
    have hq2 : (q : ℝ) < 2 * √(d : ℝ) := by linarith
    have hm1' : 0 < m := by exact_mod_cast hm1
    have hq1' : 0 < q := by exact_mod_cast hqpos
    have hm2' : m ≤ 2 * d := by
      have : (m : ℝ) ≤ 2 * d := by linarith
      exact_mod_cast this
    have hq2' : q ≤ 2 * d := by
      have : (q : ℝ) ≤ 2 * d := by linarith
      exact_mod_cast this
    simp only [Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨by omega, hm2'⟩, ⟨by omega, hq2'⟩⟩
  -- pigeonhole
  set t := Finset.Icc (1 : ℤ) (2 * d) ×ˢ Finset.Icc (1 : ℤ) (2 * d)
  obtain ⟨j, hj, k, hk, hjk, hmq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (t.card + 1)) (t := t) (f := mq d m₀ q₀) (by simp)
    (fun i _ ↦ hbd i)
  -- WLOG `j < k`
  have main : ∀ j k, j < k → mq d m₀ q₀ j = mq d m₀ q₀ k → ∃ r, 1 ≤ r ∧ ∀ i, a (i + r) = a i := by
    intro j k hlt heq
    have hxy : x j = x k ∧ y j = y k := by
      refine ⟨?_, ?_⟩ <;> simp only [x, y, xi, xiConj, heq]
    -- step back
    have back : ∀ s, s ≤ j → x (j - s) = x (k - s) ∧ y (j - s) = y (k - s) := by
      intro s hs
      induction s with
      | zero => simpa using hxy
      | succ s ih =>
        obtain ⟨ex, ey⟩ := ih (by omega)
        obtain ⟨u, hu⟩ : ∃ u, j - s = u + 1 := ⟨j - s - 1, by omega⟩
        obtain ⟨v, hv⟩ : ∃ v, k - s = v + 1 := ⟨k - s - 1, by omega⟩
        have hu' : j - (s + 1) = u := by omega
        have hv' : k - (s + 1) = v := by omega
        rw [hu, hv] at ex ey
        rw [hu', hv']
        -- `ξ'_{u+1} = 1/(ξ'ᵤ - aᵤ)`, `-1 < ξ'ᵤ < 0`
        have hyu := hys u
        have hyv := hys v
        rw [← (hT u).2] at hyu
        rw [← (hT v).2] at hyv
        obtain ⟨-, hu1, hu2⟩ := hinv u
        obtain ⟨-, hv1, hv2⟩ := hinv v
        obtain ⟨-, hU1, hU2⟩ := hinv (u + 1)
        have hdu : y u - a u ≠ 0 := by
          have : (0 : ℝ) < a u := by
            have := (hI u).1; have := (hinv u).1
            have h : (1 : ℤ) ≤ ⌊x u⌋ := Int.le_floor.mpr (by exact_mod_cast (hinv u).1.le)
            rw [← (hT u).2] at h; exact_mod_cast (show (0 : ℤ) < a u by omega)
          linarith
        have hdv : y v - a v ≠ 0 := by
          have : (0 : ℝ) < a v := by
            have h : (1 : ℤ) ≤ ⌊x v⌋ := Int.le_floor.mpr (by exact_mod_cast (hinv v).1.le)
            rw [← (hT v).2] at h; exact_mod_cast (show (0 : ℤ) < a v by omega)
          linarith
        have eu : y u - a u = 1 / y (u + 1) := by rw [hyu, one_div_one_div]
        have ev : y v - a v = 1 / y (v + 1) := by rw [hyv, one_div_one_div]
        have hauv : a u = a v := by
          apply int_eq_of_mem_Ioo (c := -(1 / y (u + 1)))
          · constructor <;> linarith
          · rw [← ey] at ev; constructor <;> linarith
        have hxu := hxs u
        have hxv := hxs v
        rw [← (hT u).2] at hxu
        rw [← (hT v).2] at hxv
        have hpu : x u - a u ≠ 0 := by have := (hI u).1; linarith
        have hpv : x v - a v ≠ 0 := by have := (hI v).1; linarith
        have fu : x u = a u + 1 / x (u + 1) := by rw [hxu, one_div_one_div]; ring
        have fv : x v = a v + 1 / x (v + 1) := by rw [hxv, one_div_one_div]; ring
        have gu : y u = a u + 1 / y (u + 1) := by linarith
        have gv : y v = a v + 1 / y (v + 1) := by linarith
        exact ⟨by rw [fu, fv, ex, hauv], by rw [gu, gv, ey, hauv]⟩
    have h0 := (back j le_rfl).1
    rw [Nat.sub_self] at h0
    refine ⟨k - j, by omega, ?_⟩
    have fwd : ∀ i, x (i + (k - j)) = x i := by
      intro i
      induction i with
      | zero => simpa using h0.symm
      | succ i ih => rw [show i + 1 + (k - j) = i + (k - j) + 1 by omega, hxs, hxs, ih]
    intro i
    rw [(hT (i + (k - j))).2, (hT i).2, fwd]
  rcases lt_or_gt_of_ne hjk with h | h
  · exact main j k h hmq
  · exact main k j h hmq.symm

section Headline

variable {D : ℕ} {P Q : ℤ} {a : ℕ → ℤ}

/-- The "only if" part of Theorem 7.20: a purely periodic expansion has `ξ > 1` and `-1 < ξ' < 0`. -/
theorem gt_one_and_conj_mem_of_purelyPeriodic (hD : ¬IsSquare D) (hQ : Q ≠ 0)
    (ha : ∀ i, 1 ≤ i → 0 < a i)
    (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 ((P + √(D : ℝ)) / Q)))
    (hper : ∃ r, 1 ≤ r ∧ ∀ i, a (i + r) = a i) :
    1 < (P + √(D : ℝ)) / Q ∧ -1 < (P - √(D : ℝ)) / Q ∧ (P - √(D : ℝ)) / Q < 0 := by
  obtain ⟨r, hr, hp⟩ := hper
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  have ha0 : ∀ i, 0 < a i := by
    intro i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [← hp 0]; exact ha _ (by omega)
    · exact ha i hi
  set ξ := (P + √(D : ℝ)) / Q with hξ
  set ξ' := (P - √(D : ℝ)) / Q with hξ'
  have hξ1 : 1 < ξ := by
    have h1 := (cf_value_mem_Ioo ha hx).1
    have h2 : (1 : ℝ) ≤ a 0 := by exact_mod_cast ha0 0
    linarith
  -- the complete quotient `ξ_r` is `ξ`
  have htail : Tendsto (fun t ↦ (cf (fun i ↦ ((a (n + 1 + i) : ℤ) : ℝ))).convs t) atTop (𝓝 ξ) := by
    have e : (fun i ↦ ((a (n + 1 + i) : ℤ) : ℝ)) = fun i ↦ (a i : ℝ) := by
      funext i; rw [add_comm, hp]
    rw [e]; exact hx
  have e := cf_value_eq_completeQuotient ha hx n htail
  obtain ⟨H, K, hH, hK, -, hK0⟩ := cf_contsAux_int_pos ha0 (n + 1)
  obtain ⟨H', K', hH', hK', hH'1, hK'0⟩ := cf_contsAux_int_pos ha0 n
  have hKpos : 0 < K := by
    have := cf_dens_pos (pos_fin ha n) n le_rfl
    rw [den_eq_conts_b, nth_cont_eq_succ_nth_contAux, hK] at this
    exact_mod_cast this
  have hlt := cf_contsAux_lt ha0 one_pos n
  rw [hH, hK, hH', hK'] at e hlt
  have hKr : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hK'r : (0 : ℝ) ≤ K' := by exact_mod_cast hK'0
  have hH'r : (1 : ℝ) ≤ H' := by exact_mod_cast hH'1
  have hden : 0 < ξ * K + K' := by nlinarith
  -- `f(ξ) = K ξ² + (K' - H) ξ - H' = 0`
  have hf : (K : ℝ) * ξ ^ 2 + (K' - H) * ξ - H' = 0 := by
    have := e
    rw [eq_div_iff hden.ne'] at this
    linear_combination this
  -- hence also `f(ξ') = 0`
  have hQr : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ
  have hs : √(D : ℝ) ^ 2 = D := Real.sq_sqrt (by positivity)
  have hf' : (K : ℝ) * ξ' ^ 2 + (K' - H) * ξ' - H' = 0 := by
    have hQ2 : (K : ℝ) * (P + √(D : ℝ)) ^ 2 + (K' - H) * Q * (P + √(D : ℝ)) - H' * Q ^ 2 = 0 := by
      have := congrArg (· * (Q : ℝ) ^ 2) hf
      simp only [zero_mul] at this
      rw [← this, hξ]; field_simp
    have key : ((K * (P ^ 2 + D) + (K' - H) * Q * P - H' * Q ^ 2 : ℤ) : ℝ) +
        ((2 * K * P + (K' - H) * Q : ℤ) : ℝ) * √(D : ℝ) = 0 := by
      push_cast; linear_combination hQ2 - (K : ℝ) * hs
    obtain ⟨hA, hB⟩ := int_add_mul_sqrt_eq_zero hD key
    have hA' : ((K * (P ^ 2 + D) + (K' - H) * Q * P - H' * Q ^ 2 : ℤ) : ℝ) = 0 := by
      rw [hA]; simp
    have hB' : ((2 * K * P + (K' - H) * Q : ℤ) : ℝ) = 0 := by rw [hB]; simp
    push_cast at hA' hB'
    have : ((K : ℝ) * ξ' ^ 2 + (K' - H) * ξ' - H') * Q ^ 2 = 0 := by
      rw [hξ']; field_simp
      linear_combination hA' - √(D : ℝ) * hB' + (K : ℝ) * hs
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h) hQr
  -- Vieta
  have hne : ξ - ξ' ≠ 0 := by
    have : ξ - ξ' = 2 * √(D : ℝ) / Q := by rw [hξ, hξ']; field_simp; ring
    rw [this]
    have : 0 < √(D : ℝ) := Real.sqrt_pos.mpr (by
      have : 2 ≤ D := two_le_of_not_isSquare hD
      exact_mod_cast (show 0 < D by omega))
    exact div_ne_zero (by positivity) hQr
  have hsum : (K : ℝ) * (ξ + ξ') + (K' - H) = 0 := by
    have : (ξ - ξ') * ((K : ℝ) * (ξ + ξ') + (K' - H)) = 0 := by linear_combination hf - hf'
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hne
    · exact h
  have hprod : -(H' : ℝ) = K * ξ * ξ' := by linear_combination hf - ξ * hsum
  refine ⟨hξ1, ?_, ?_⟩
  · -- `f(-1) = K(1 + ξ)(1 + ξ') = K - K' + H - H' > 0`
    have hm1 : (K : ℝ) * (1 + ξ) * (1 + ξ') = K - K' + H - H' := by
      linear_combination hsum - hprod
    have hpos : (0 : ℝ) < K - K' + H - H' := by linarith
    by_contra hc
    push Not at hc
    have : (K : ℝ) * (1 + ξ) * (1 + ξ') ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    linarith
  · -- `f(0) = K ξ ξ' = -H' < 0`
    by_contra hc
    push Not at hc
    have : 0 ≤ (K : ℝ) * ξ * ξ' := mul_nonneg (by positivity) hc
    linarith

/-- **Theorem 7.20** (Galois). Let `ξ = (P + √D)/Q` be a real quadratic irrational (`P, Q` integers,
`Q ≠ 0`, `D` a positive integer which is not a square) and `ξ' = (P - √D)/Q` its conjugate, and let
`ξ = ⟨a₀, a₁, a₂, …⟩` be its continued fraction. The expansion is purely periodic
(`a_{i+r} = aᵢ` for all `i ≥ 0`, for some `r ≥ 1`) if and only if `ξ > 1` and `-1 < ξ' < 0`. -/
@[kb "nivenzuckermanmontgomery" "Thm 7.20, p. 348"]
theorem purelyPeriodic_iff (hD : ¬IsSquare D) (hQ : Q ≠ 0) (ha : ∀ i, 1 ≤ i → 0 < a i)
    (hx : Tendsto (fun t ↦ (cf (fun i ↦ (a i : ℝ))).convs t) atTop (𝓝 ((P + √(D : ℝ)) / Q))) :
    (∃ r, 1 ≤ r ∧ ∀ i, a (i + r) = a i) ↔
      1 < (P + √(D : ℝ)) / Q ∧ -1 < (P - √(D : ℝ)) / Q ∧ (P - √(D : ℝ)) / Q < 0 := by
  refine ⟨gt_one_and_conj_mem_of_purelyPeriodic hD hQ ha hx, fun ⟨h1, h2, h3⟩ ↦ ?_⟩
  -- write `ξ = (m₀ + √d)/q₀` with `d = D Q²`, `m₀ = P |Q|`, `q₀ = Q |Q|`
  set k := Q.natAbs with hk
  have hk0 : k ≠ 0 := by simpa [hk] using hQ
  have hkr : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk0
  have hsq : √((D * k ^ 2 : ℕ) : ℝ) = √(D : ℝ) * k := by
    push_cast
    rw [Real.sqrt_mul' _ (by positivity), Real.sqrt_sq hkr.le]
  have hd : ¬IsSquare (D * k ^ 2) := by
    rw [← irrational_sqrt_natCast_iff, hsq]
    exact (irrational_sqrt_natCast_iff.mpr hD).mul_natCast hk0
  have hq₀ : Q * (k : ℤ) ≠ 0 := mul_ne_zero hQ (by exact_mod_cast hk0)
  have hdvd : Q * (k : ℤ) ∣ ((D * k ^ 2 : ℕ) : ℤ) - (P * k) ^ 2 := by
    have h1 : Q ∣ (k : ℤ) := Int.dvd_natCast.mpr dvd_rfl
    have : ((D * k ^ 2 : ℕ) : ℤ) - (P * k) ^ 2 = k * k * (D - P ^ 2) := by push_cast; ring
    rw [this]
    exact Dvd.dvd.mul_right (mul_dvd_mul h1 dvd_rfl) _
  have hx0 : xi (D * k ^ 2) (P * k) (Q * k) 0 = (P + √(D : ℝ)) / Q := by
    simp only [xi, mq_zero]
    rw [hsq]; push_cast
    rw [show (P : ℝ) * k + √(D : ℝ) * k = (P + √(D : ℝ)) * k by ring, mul_div_mul_right _ _ hkr.ne']
  have hy0 : xiConj (D * k ^ 2) (P * k) (Q * k) 0 = (P - √(D : ℝ)) / Q := by
    simp only [xiConj, mq_zero]
    rw [hsq]; push_cast
    rw [show (P : ℝ) * k - √(D : ℝ) * k = (P - √(D : ℝ)) * k by ring, mul_div_mul_right _ _ hkr.ne']
  exact purelyPeriodic_of_reduced hd hq₀ hdvd ha (hx0 ▸ hx) (hx0 ▸ h1) (hy0 ▸ h2) (hy0 ▸ h3)

end Headline

end NTKB.NZM
