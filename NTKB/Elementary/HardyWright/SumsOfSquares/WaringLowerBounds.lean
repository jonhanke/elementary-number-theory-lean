/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.HardyWright.SumsOfSquares.Waring
import NTKB.Attr
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Sym.Card
import Mathlib.FieldTheory.Finite.Basic

/-!
# Hardy–Wright, §§ 21.5–21.6: lower bounds for `g(k)` and `G(k)`

Every lower bound is proved for each admissible `s` (every `n`, resp. every large `n`, is the sum of
`s` `k`th powers), and hence for `g(k)`, `G(k)` themselves whenever they exist.

* Theorem 393: `g(k) ≥ 2ᵏ + q - 2`, `q = ⌊(3/2)ᵏ⌋` (`two_pow_add_le_of_forall_isSumOfPowers`).
* Theorem 394: `G(k) ≥ k + 1` for `k ≥ 2` (counting argument) (`succ_le_of_eventually_isSumOfPowers`).
* Theorem 395: `G(4) ≥ 16`.
* Theorem 396: `G(2^θ) ≥ 2^(θ+2)` for `θ ≥ 2`.
* Theorem 397: `G(p^θ (p - 1)) ≥ p^(θ+1)` for an odd prime `p`.
* Theorem 398: `G(p^θ (p - 1)/2) ≥ (p^(θ+1) - 1)/2` for an odd prime `p` (the book's `G{½p^θ(p-1)}`).
* Theorem 399: `G(3 · 2^θ) ≥ 2^(θ+2)` for `θ ≥ 2`.
* Theorem 400: the summary.
-/

open Finset Filter Topology

namespace NTKB.HardyWright

/-! ### Theorem 393 -/

/-- **Theorem 393** (Hardy–Wright). If every number is the sum of `s` `k`th powers (`k ≥ 1`), then
`s ≥ 2ᵏ + q - 2` with `q = ⌊(3/2)ᵏ⌋ = ⌊3ᵏ / 2ᵏ⌋`: the number `2ᵏ q - 1 < 3ᵏ` needs that many. -/
@[kb "hardywright2008" "Thm 393, p. 445"]
theorem two_pow_add_le_of_forall_isSumOfPowers {k s : ℕ} (hk : k ≠ 0)
    (hs : ∀ n, IsSumOfPowers k s n) : 2 ^ k + 3 ^ k / 2 ^ k - 2 ≤ s := by
  obtain ⟨q, hq⟩ : ∃ q, q = 3 ^ k / 2 ^ k := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = 2 ^ k := ⟨_, rfl⟩
  rw [← hq, ← ht]
  have h2 : 0 < t := by rw [ht]; positivity
  have hq1 : 1 ≤ q := by
    rw [hq, Nat.le_div_iff_mul_le (by positivity), one_mul]
    exact Nat.pow_le_pow_left (by norm_num) k
  have hqle : t * q ≤ 3 ^ k := by rw [hq, ht]; exact Nat.mul_div_le _ _
  have htq : 1 ≤ t * q := Nat.one_le_iff_ne_zero.2 (by positivity)
  obtain ⟨x, hx⟩ := hs (t * q - 1)
  -- every `xᵢ` is `0`, `1` or `2`
  have hle : ∀ i, x i ≤ 2 := by
    intro i
    by_contra h
    have h3 : 3 ^ k ≤ x i ^ k := Nat.pow_le_pow_left (by omega) k
    have : x i ^ k ≤ ∑ j, x j ^ k :=
      single_le_sum (f := fun j => x j ^ k) (fun _ _ => Nat.zero_le _) (mem_univ i)
    omega
  set A := (univ.filter fun i => x i = 2).card
  set B := (univ.filter fun i => x i = 1).card
  have hsum : ∑ i, x i ^ k = t * A + B := by
    have : ∀ i, x i ^ k = (if x i = 2 then t else 0) + (if x i = 1 then 1 else 0) := by
      intro i
      have := hle i
      interval_cases h : x i <;> simp [zero_pow hk, ht]
    rw [sum_congr rfl fun i _ => this i, sum_add_distrib, sum_ite, sum_ite]
    simp [A, B, mul_comm]
  have hAB : A + B ≤ s := by
    rw [← card_union_of_disjoint (disjoint_filter.2 fun i _ h1 h2 => by omega)]
    exact (card_le_univ _).trans (by simp)
  rw [hsum] at hx
  have hA : A + 1 ≤ q := by
    by_contra h
    have := Nat.mul_le_mul_left t (show q ≤ A by omega)
    omega
  -- `A + B = n - A(2ᵏ - 1) ≥ 2ᵏ q - 1 - (q - 1)(2ᵏ - 1) = 2ᵏ + q - 2`
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hA
  have e1 : t * A + B + 1 = t * q := by omega
  rw [hr, Nat.mul_add, Nat.mul_add, mul_one] at e1
  have : r ≤ t * r := Nat.le_mul_of_pos_left r h2
  omega

/-- **Theorem 393** for `g(k)`: if `g(k)` exists, then `g(k) ≥ 2ᵏ + ⌊(3/2)ᵏ⌋ - 2`. -/
@[kb "hardywright2008" "Thm 393, p. 445"]
theorem two_pow_add_le_waringNumber {k : ℕ} (hk : k ≠ 0) (hex : ∃ s, ∀ n, IsSumOfPowers k s n) :
    2 ^ k + 3 ^ k / 2 ^ k - 2 ≤ waringNumber k :=
  le_waringNumber hex fun _ hs => two_pow_add_le_of_forall_isSumOfPowers hk hs

/-! ### Theorem 394 -/

open Classical in
/-- The number of `n ≤ Tᵏ` which are sums of `s` `k`th powers is at most `C(T + s, s)`: such an
`n` is the image of a multiset of `s` numbers `≤ T`. -/
lemma card_isSumOfPowers_le {k s : ℕ} (hk : k ≠ 0) (T : ℕ) :
    ((range (T ^ k + 1)).filter fun n => IsSumOfPowers k s n).card ≤ (T + s).choose s := by
  let g : Sym (Fin (T + 1)) s → ℕ := fun m => (Multiset.map (fun i : Fin (T + 1) => i.val ^ k)
    m.1).sum
  have hsub : ((range (T ^ k + 1)).filter fun n => IsSumOfPowers k s n) ⊆ univ.image g := by
    intro n hn
    simp only [mem_filter, mem_range] at hn
    obtain ⟨hn, x, rfl⟩ := hn
    have hle : ∀ i, x i ≤ T := by
      intro i
      have : x i ^ k ≤ T ^ k := by
        have := single_le_sum (f := fun j => x j ^ k) (fun _ _ => Nat.zero_le _) (mem_univ i)
        omega
      exact (Nat.pow_le_pow_iff_left hk).1 this
    refine mem_image.2 ⟨⟨(univ.val.map fun i => (⟨x i, by have := hle i; omega⟩ : Fin (T + 1))),
      by simp⟩, mem_univ _, ?_⟩
    simp only [g, Multiset.map_map, Function.comp_def, Finset.sum]
  calc _ ≤ (univ.image g).card := card_le_card hsub
    _ ≤ (univ : Finset (Sym (Fin (T + 1)) s)).card := card_image_le
    _ = (T + s).choose s := by
      rw [card_univ, Sym.card_sym_eq_choose, Fintype.card_fin]
      congr 1; omega

/-- **Theorem 394** (Hardy–Wright). For `k ≥ 2`, if all large numbers are sums of `s` `k`th powers
then `s ≥ k + 1`. -/
@[kb "hardywright2008" "Thm 394, p. 445"]
theorem succ_le_of_eventually_isSumOfPowers {k s : ℕ} (hk : 2 ≤ k)
    (hs : ∀ᶠ n in atTop, IsSumOfPowers k s n) : k + 1 ≤ s := by
  classical
  by_contra hlt
  have hk0 : k ≠ 0 := by omega
  obtain ⟨N, hN⟩ := eventually_atTop.1 hs
  -- the number of representable `n ≤ Tᵏ` is at least `Tᵏ + 1 - N`
  have hlow : ∀ T : ℕ, T ^ k + 1 - N ≤ (T + k).choose k := by
    intro T
    refine le_trans ?_ (card_isSumOfPowers_le hk0 (s := k) T)
    have hsub : (Ico N (T ^ k + 1)) ⊆ (range (T ^ k + 1)).filter fun n => IsSumOfPowers k k n := by
      intro n hn
      simp only [mem_Ico] at hn
      simp only [mem_filter, mem_range]
      exact ⟨hn.2, (hN n hn.1).mono hk0 (by omega)⟩
    simpa using card_le_card hsub
  -- but `C(T + k, k) ≤ (T + k)ᵏ / k! ≤ (T + k)ᵏ / 2`, which is eventually `< (3/4) Tᵏ`.
  have hlim1 : Tendsto (fun T : ℕ => (1 + (k : ℝ) / T) ^ k) atTop (𝓝 1) := by
    have := ((tendsto_const_div_atTop_nhds_zero_nat (k : ℝ)).const_add 1).pow k
    simpa using this
  have hlim2 : Tendsto (fun T : ℕ => (1 : ℝ) - N / (T : ℝ) ^ k) atTop (𝓝 1) := by
    have h0 : Tendsto (fun T : ℕ => (N : ℝ) / (T : ℝ) ^ k) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop hk0).comp tendsto_natCast_atTop_atTop)
    simpa using h0.const_sub 1
  have e1 := hlim1.eventually (gt_mem_nhds (show (1 : ℝ) < 3 / 2 by norm_num))
  have e2 := hlim2.eventually (lt_mem_nhds (show (3 / 4 : ℝ) < 1 by norm_num))
  obtain ⟨T, ⟨hT1, hT2⟩, hTpos⟩ := ((e1.and e2).and (eventually_gt_atTop 0)).exists
  have hTr : (0 : ℝ) < T := by exact_mod_cast hTpos
  have hTk : (0 : ℝ) < (T : ℝ) ^ k := by positivity
  have hfact : (2 : ℝ) ≤ (k.factorial : ℝ) := by
    have : 2 ≤ k.factorial := by
      calc 2 = (2 : ℕ).factorial := rfl
        _ ≤ k.factorial := Nat.factorial_le hk
    exact_mod_cast this
  have hchoose : ((T + k).choose k : ℝ) ≤ ((T : ℝ) + k) ^ k / 2 := by
    have := Nat.choose_le_pow_div (α := ℝ) k (T + k)
    push_cast at this
    refine this.trans ?_
    gcongr
  have hpow : ((T : ℝ) + k) ^ k = (T : ℝ) ^ k * (1 + k / T) ^ k := by
    rw [← mul_pow]; congr 1; field_simp
  have hlowR : (T : ℝ) ^ k + 1 - N ≤ ((T + k).choose k : ℝ) := by
    have := hlow T
    have h' : ((T ^ k + 1 - N : ℕ) : ℝ) ≤ ((T + k).choose k : ℝ) := by exact_mod_cast this
    have h'' : (T : ℝ) ^ k + 1 - N ≤ ((T ^ k + 1 - N : ℕ) : ℝ) := by
      rw [sub_le_iff_le_add]
      have : ((T ^ k + 1 : ℕ) : ℝ) ≤ ((T ^ k + 1 - N : ℕ) : ℝ) + N := by
        exact_mod_cast le_tsub_add (a := N) (b := T ^ k + 1)
      push_cast at this
      linarith
    linarith
  have hT2' : (3 / 4 : ℝ) * (T : ℝ) ^ k < (T : ℝ) ^ k - N := by
    have := mul_lt_mul_of_pos_right hT2 hTk
    rw [sub_mul, div_mul_cancel₀ _ hTk.ne'] at this
    linarith
  have : (T : ℝ) ^ k * (1 + k / T) ^ k ≤ (T : ℝ) ^ k * (3 / 2) :=
    mul_le_mul_of_nonneg_left hT1.le hTk.le
  nlinarith

/-! ### Congruence arguments: Theorems 395–400 -/

/-- If every `f i` is `≡ 0` or `1 (mod M)`, the sum is congruent to the number of `1`s. -/
lemma sum_mod_eq_card_of_mod_le_one {s M : ℕ} (f : Fin s → ℕ) (hf : ∀ i, f i % M = 0 ∨ f i % M = 1) :
    (∑ i, f i) % M = (univ.filter fun i => f i % M = 1).card % M := by
  rw [Finset.sum_nat_mod, card_eq_sum_ones, Finset.sum_filter, Finset.sum_nat_mod (f := fun i =>
    if f i % M = 1 then 1 else 0)]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rcases hf i with h | h
  · simp [h]
  · have : M ≠ 1 := by rintro rfl; omega
    simp [h, Nat.one_mod_eq_one.2 this]

/-- If fewer than `M` numbers, each `≡ 0` or `1 (mod M)`, have sum `≡ 0 (mod M)`, then all of them are
`≡ 0 (mod M)`. -/
lemma all_mod_eq_zero_of_sum_mod_eq_zero {s M : ℕ} (hs : s < M) (f : Fin s → ℕ)
    (hf : ∀ i, f i % M = 0 ∨ f i % M = 1) (h : (∑ i, f i) % M = 0) : ∀ i, f i % M = 0 := by
  rw [sum_mod_eq_card_of_mod_le_one f hf] at h
  have hc : (univ.filter fun i => f i % M = 1).card < M :=
    (card_le_univ _).trans_lt (by simpa using hs)
  rw [Nat.mod_eq_of_lt hc, card_eq_zero, filter_eq_empty_iff] at h
  intro i
  rcases hf i with h' | h'
  · exact h'
  · exact absurd h' (h (mem_univ i))

/-- `x^(2^θ) ≡ 1 (mod 2^(θ+2))` for odd `x` and `θ ≥ 1`. -/
lemma pow_two_pow_mod_of_odd {x : ℕ} (hx : x % 2 = 1) :
    ∀ θ : ℕ, 1 ≤ θ → x ^ 2 ^ θ % 2 ^ (θ + 2) = 1 := by
  intro θ hθ
  induction θ, hθ using Nat.le_induction with
  | base =>
    have : x % 8 = 1 ∨ x % 8 = 3 ∨ x % 8 = 5 ∨ x % 8 = 7 := by omega
    norm_num [Nat.pow_mod]
    rcases this with h | h | h | h <;> simp [h]
  | succ θ hθ ih =>
    obtain ⟨t, ht⟩ : ∃ t, x ^ 2 ^ θ = 1 + 2 ^ (θ + 2) * t := by
      refine ⟨x ^ 2 ^ θ / 2 ^ (θ + 2), ?_⟩
      have := Nat.mod_add_div (x ^ 2 ^ θ) (2 ^ (θ + 2))
      omega
    have : x ^ 2 ^ (θ + 1) = 1 + 2 ^ (θ + 1 + 2) * (t + 2 ^ (θ + 1) * t ^ 2) := by
      rw [pow_succ, pow_mul, ht]; ring
    rw [this, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))

/-- `x^(2^θ) ≡ 0` or `1 (mod 2^(θ+2))` for `θ ≥ 2`, and `≡ 0` exactly when `x` is even. -/
lemma pow_two_pow_mod {θ : ℕ} (hθ : 2 ≤ θ) (x : ℕ) :
    (x % 2 = 0 ∧ x ^ 2 ^ θ % 2 ^ (θ + 2) = 0) ∨ (x % 2 = 1 ∧ x ^ 2 ^ θ % 2 ^ (θ + 2) = 1) := by
  rcases Nat.mod_two_eq_zero_or_one x with h | h
  · refine Or.inl ⟨h, ?_⟩
    obtain ⟨y, rfl⟩ : 2 ∣ x := Nat.dvd_of_mod_eq_zero h
    have hθ2 : θ + 2 ≤ 2 ^ θ := by
      induction θ, hθ using Nat.le_induction with
      | base => norm_num
      | succ n hn ih => rw [pow_succ]; omega
    rw [mul_pow]
    exact Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_right (Nat.pow_dvd_pow 2 hθ2) _)
  · exact Or.inr ⟨h, pow_two_pow_mod_of_odd h θ (by omega)⟩

/-- **Theorem 395** (Hardy–Wright), the arithmetic: `16ᵐ · 31` is not the sum of `15` biquadrates. -/
lemma not_isSumOfPowers_four_fifteen (m : ℕ) : ¬ IsSumOfPowers 4 15 (16 ^ m * 31) := by
  have hmod : ∀ x : ℕ, (x % 2 = 0 ∧ x ^ 4 % 16 = 0) ∨ (x % 2 = 1 ∧ x ^ 4 % 16 = 1) := by
    simpa using pow_two_pow_mod (θ := 2) le_rfl
  induction m with
  | zero =>
    rintro ⟨x, hx⟩
    simp only [pow_zero, one_mul] at hx
    -- all fifteen are odd, so all are `1`, and the sum is `15 ≠ 31`
    have hall : ∀ i, (x i ^ 4) % 16 = 1 := by
      have h15 : (∑ i, x i ^ 4) % 16 = 15 := by rw [hx]
      rw [sum_mod_eq_card_of_mod_le_one _ fun i => (hmod (x i)).imp And.right And.right] at h15
      have hc : (univ.filter fun i => x i ^ 4 % 16 = 1).card ≤ 15 :=
        (card_le_univ _).trans (by simp)
      have hc' : (univ.filter fun i => x i ^ 4 % 16 = 1).card = 15 := by omega
      intro i
      by_contra hi
      have : (univ.filter fun i => x i ^ 4 % 16 = 1) ⊂ univ :=
        ssubset_univ_iff.2 fun h => hi (by simpa using (filter_eq_self.1 h) i (mem_univ i))
      have := card_lt_card this
      simp [hc'] at this
    have hge : ∀ i, 1 ≤ x i ^ 4 ∧ (x i ^ 4 = 1 ∨ 81 ≤ x i ^ 4) := by
      intro i
      have h1 := hall i
      have : x i ≠ 0 := by rintro h; simp [h] at h1
      rcases Nat.lt_or_ge (x i) 2 with h | h
      · have : x i = 1 := by omega
        simp [this]
      · have : 2 ^ 4 ≤ x i ^ 4 := Nat.pow_le_pow_left h 4
        have : x i ≠ 2 := by rintro h; simp [h] at h1
        have : 3 ^ 4 ≤ x i ^ 4 := Nat.pow_le_pow_left (by omega) 4
        exact ⟨by omega, Or.inr (by norm_num at this ⊢; omega)⟩
    by_cases hbig : ∃ i, 81 ≤ x i ^ 4
    · obtain ⟨i, hi⟩ := hbig
      have := single_le_sum (f := fun j => x j ^ 4) (fun _ _ => Nat.zero_le _) (mem_univ i)
      omega
    · push Not at hbig
      have : ∀ i, x i ^ 4 = 1 := fun i => ((hge i).2.resolve_right (by have := hbig i; omega))
      simp [this] at hx
  | succ m ih =>
    rintro ⟨x, hx⟩
    have h0 : ∀ i, x i ^ 4 % 16 = 0 := by
      refine all_mod_eq_zero_of_sum_mod_eq_zero (by norm_num) (fun i => x i ^ 4)
        (fun i => (hmod (x i)).imp And.right And.right) ?_
      rw [hx, pow_succ]; simp [Nat.mul_mod, Nat.mul_assoc]
    have heven : ∀ i, 2 ∣ x i := fun i => by
      rcases hmod (x i) with h | h
      · exact Nat.dvd_of_mod_eq_zero h.1
      · have := h0 i; omega
    choose y hy using heven
    apply ih
    refine ⟨y, ?_⟩
    have : ∑ i, x i ^ 4 = 16 * ∑ i, y i ^ 4 := by
      rw [Finset.mul_sum]; exact sum_congr rfl fun i _ => by rw [hy i]; ring
    rw [this, pow_succ] at hx
    omega

/-- **Theorem 395** (Hardy–Wright). `G(4) ≥ 16`: if all large numbers are sums of `s` biquadrates,
then `s ≥ 16`. -/
@[kb "hardywright2008" "Thm 395, p. 447"]
theorem sixteen_le_of_eventually_isSumOfPowers_four {s : ℕ}
    (hs : ∀ᶠ n in atTop, IsSumOfPowers 4 s n) : 16 ≤ s :=
  le_of_frequently_not (by norm_num) (fun n₀ => ⟨16 ^ n₀ * 31, by
    have := Nat.lt_pow_self (show 1 < 16 by norm_num) (n := n₀); nlinarith,
    not_isSumOfPowers_four_fifteen n₀⟩) hs

@[kb "hardywright2008" "Thm 395, p. 447"]
theorem sixteen_le_asymptoticWaringNumber_four : 16 ≤ asymptoticWaringNumber 4 :=
  le_asymptoticWaringNumber ⟨50, Eventually.of_forall isSumOfPowers_four_fifty⟩
    fun _ hs => sixteen_le_of_eventually_isSumOfPowers_four hs

/-- **Theorem 396** (Hardy–Wright), the arithmetic for `θ ≥ 3`: if `n` is odd then `2^(θ+2) n` is not
the sum of `2^(θ+2) - 1` `(2^θ)`th powers. -/
lemma add_three_le_two_pow {θ : ℕ} (hθ : 3 ≤ θ) : θ + 3 ≤ 2 ^ θ := by
  induction θ, hθ using Nat.le_induction with
  | base => norm_num
  | succ m hm ih => rw [pow_succ]; omega

lemma not_isSumOfPowers_two_pow {θ n : ℕ} (hθ : 3 ≤ θ) (hn : n % 2 = 1) :
    ¬ IsSumOfPowers (2 ^ θ) (2 ^ (θ + 2) - 1) (2 ^ (θ + 2) * n) := by
  rintro ⟨x, hx⟩
  have hM : 2 ^ (θ + 2) - 1 < 2 ^ (θ + 2) := Nat.sub_lt (by positivity) one_pos
  have h0 := all_mod_eq_zero_of_sum_mod_eq_zero hM (fun i => x i ^ 2 ^ θ)
    (fun i => (pow_two_pow_mod (θ := θ) (by omega) (x i)).imp And.right And.right)
    (by rw [hx]; exact Nat.mul_mod_right _ _)
  have heven : ∀ i, 2 ∣ x i := fun i => by
    rcases pow_two_pow_mod (θ := θ) (by omega) (x i) with h | h
    · exact Nat.dvd_of_mod_eq_zero h.1
    · have := h0 i; omega
  -- each term is divisible by `2^(2^θ)`, and `2^θ ≥ θ + 3`
  have hdvd : 2 ^ (θ + 3) ∣ 2 ^ (θ + 2) * n := by
    rw [← hx]
    refine dvd_sum fun i _ => ?_
    obtain ⟨y, hy⟩ := heven i
    rw [hy, mul_pow]
    exact Dvd.dvd.mul_right (Nat.pow_dvd_pow 2 (add_three_le_two_pow hθ)) _
  rw [pow_succ, Nat.mul_dvd_mul_iff_left (by positivity)] at hdvd
  omega

/-- **Theorem 396** (Hardy–Wright). For `θ ≥ 2`, if all large numbers are sums of `s` `(2^θ)`th
powers then `s ≥ 2^(θ+2)`. -/
@[kb "hardywright2008" "Thm 396, p. 447"]
theorem two_pow_le_of_eventually_isSumOfPowers {θ s : ℕ} (hθ : 2 ≤ θ)
    (hs : ∀ᶠ n in atTop, IsSumOfPowers (2 ^ θ) s n) : 2 ^ (θ + 2) ≤ s := by
  rcases eq_or_lt_of_le hθ with rfl | hθ
  · exact sixteen_le_of_eventually_isSumOfPowers_four hs
  refine le_of_frequently_not (by positivity) (fun n₀ => ⟨2 ^ (θ + 2) * (2 * n₀ + 1), ?_, ?_⟩) hs
  · have : 1 ≤ 2 ^ (θ + 2) := Nat.one_le_two_pow; nlinarith
  · exact not_isSumOfPowers_two_pow hθ (by omega)

/-- For an odd prime `p` and `k = p^θ (p - 1)`, `xᵏ ≡ 0 (mod p^(θ+1))` if `p ∣ x` and `≡ 1` otherwise. -/
lemma pow_totient_mod {p θ : ℕ} (hp : p.Prime) (x : ℕ) :
    (p ∣ x ∧ x ^ (p ^ θ * (p - 1)) % p ^ (θ + 1) = 0) ∨
      (¬ p ∣ x ∧ x ^ (p ^ θ * (p - 1)) % p ^ (θ + 1) = 1) := by
  by_cases h : p ∣ x
  · refine Or.inl ⟨h, Nat.mod_eq_zero_of_dvd ?_⟩
    obtain ⟨y, rfl⟩ := h
    rw [mul_pow]
    refine Dvd.dvd.mul_right (Nat.pow_dvd_pow p ?_) _
    have h1 : θ + 1 ≤ p ^ θ := by
      have := Nat.lt_pow_self hp.one_lt (n := θ); omega
    have h2 : 1 ≤ p - 1 := by have := hp.two_le; omega
    nlinarith
  · refine Or.inr ⟨h, ?_⟩
    have hcop : Nat.Coprime x (p ^ (θ + 1)) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 h)))
    have := Nat.ModEq.pow_totient hcop
    rw [Nat.totient_prime_pow_succ hp] at this
    rw [this, Nat.mod_eq_of_lt]
    exact Nat.one_lt_pow (by omega) hp.one_lt

/-- **Theorem 397** (Hardy–Wright). For an odd prime `p` and `θ ≥ 0`, if all large numbers are sums of
`s` `(p^θ (p-1))`th powers then `s ≥ p^(θ+1)`. -/
@[kb "hardywright2008" "Thm 397, p. 448"]
theorem prime_pow_le_of_eventually_isSumOfPowers {p θ s : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hs : ∀ᶠ n in atTop, IsSumOfPowers (p ^ θ * (p - 1)) s n) : p ^ (θ + 1) ≤ s := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hk : p ^ θ * (p - 1) ≠ 0 := Nat.mul_ne_zero (by positivity) (by omega)
  refine le_of_frequently_not hk (fun n₀ => ⟨p ^ (θ + 1) * (p * n₀ + 1), ?_, ?_⟩) hs
  · exact (show n₀ ≤ p * n₀ + 1 by nlinarith [hp.pos]).trans
      (Nat.le_mul_of_pos_left _ (by positivity))
  rintro ⟨x, hx⟩
  have hM : p ^ (θ + 1) - 1 < p ^ (θ + 1) := Nat.sub_lt (by positivity) one_pos
  have h0 := all_mod_eq_zero_of_sum_mod_eq_zero hM (fun i => x i ^ (p ^ θ * (p - 1)))
    (fun i => (pow_totient_mod hp (x i)).imp And.right And.right)
    (by rw [hx]; exact Nat.mul_mod_right _ _)
  have hdiv : ∀ i, p ∣ x i := fun i => by
    rcases pow_totient_mod (θ := θ) hp (x i) with h | h
    · exact h.1
    · have := h0 i; omega
  -- each term is divisible by `p^k`, and `k ≥ θ + 2`
  have hk2 : θ + 2 ≤ p ^ θ * (p - 1) := by
    have h1 : θ + 1 ≤ p ^ θ := by have := Nat.lt_pow_self hp.one_lt (n := θ); omega
    have h2 : 2 ≤ p - 1 := by omega
    nlinarith
  have hdvd : p ^ (θ + 2) ∣ p ^ (θ + 1) * (p * n₀ + 1) := by
    rw [← hx]
    refine dvd_sum fun i _ => ?_
    obtain ⟨y, hy⟩ := hdiv i
    rw [hy, mul_pow]
    exact Dvd.dvd.mul_right (Nat.pow_dvd_pow p hk2) _
  rw [pow_succ, Nat.mul_dvd_mul_iff_left (by positivity)] at hdvd
  have : p ∣ 1 := (Nat.dvd_add_right (dvd_mul_right p n₀)).1 hdvd
  exact hp.one_lt.ne' (Nat.dvd_one.1 this)

/-- For an odd prime `p` and `k = p^θ (p - 1)/2`, `xᵏ ≡ 0, 1` or `-1 (mod p^(θ+1))`. -/
lemma pow_half_totient_mod {p θ : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (x : ℕ) :
    (x : ℤ) ^ (p ^ θ * (p - 1) / 2) ≡ 0 [ZMOD p ^ (θ + 1)] ∨
      (x : ℤ) ^ (p ^ θ * (p - 1) / 2) ≡ 1 [ZMOD p ^ (θ + 1)] ∨
      (x : ℤ) ^ (p ^ θ * (p - 1) / 2) ≡ -1 [ZMOD p ^ (θ + 1)] := by
  have hodd : (p - 1) % 2 = 0 := by
    rcases hp.eq_two_or_odd with h | h <;> omega
  set k := p ^ θ * (p - 1) / 2 with hk
  have h2k : 2 * k = p ^ θ * (p - 1) := by
    rw [hk]; have : 2 ∣ p ^ θ * (p - 1) := Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero hodd) _
    omega
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  rcases pow_totient_mod (θ := θ) hp x with ⟨hd, _⟩ | ⟨hd, h1⟩
  · left
    have hθk : θ + 1 ≤ k := by
      have h1 : θ + 1 ≤ p ^ θ := by have := Nat.lt_pow_self hp.one_lt (n := θ); omega
      have : 2 ≤ p - 1 := by have := hp.two_le; omega
      have : 2 * (θ + 1) ≤ p ^ θ * (p - 1) := by nlinarith
      omega
    obtain ⟨y, rfl⟩ := hd
    refine Int.modEq_zero_iff_dvd.2 ?_
    push_cast
    rw [mul_pow]
    exact Dvd.dvd.mul_right (pow_dvd_pow _ hθk) _
  · right
    have hM1 : (1 : ℤ) < (p : ℤ) ^ (θ + 1) := by exact_mod_cast Nat.one_lt_pow (by omega) hp.one_lt
    have hmod : ((x : ℤ) ^ (p ^ θ * (p - 1))) % ((p : ℤ) ^ (θ + 1)) = 1 := by exact_mod_cast h1
    have hcong : (1 : ℤ) ≡ (x : ℤ) ^ (p ^ θ * (p - 1)) [ZMOD (p : ℤ) ^ (θ + 1)] := by
      unfold Int.ModEq; rw [hmod, Int.emod_eq_of_lt (by norm_num) hM1]
    have hsq : (p : ℤ) ^ (θ + 1) ∣ ((x : ℤ) ^ k - 1) * ((x : ℤ) ^ k + 1) := by
      have : ((x : ℤ) ^ k - 1) * ((x : ℤ) ^ k + 1) = (x : ℤ) ^ (p ^ θ * (p - 1)) - 1 := by
        rw [← h2k, pow_mul']; ring
      rw [this]; exact hcong.dvd
    by_cases hp1 : (p : ℤ) ∣ (x : ℤ) ^ k + 1
    · right
      have hnot : ¬ (p : ℤ) ∣ (x : ℤ) ^ k - 1 := by
        intro h
        have h2 := dvd_sub hp1 h
        rw [show (x : ℤ) ^ k + 1 - ((x : ℤ) ^ k - 1) = ((2 : ℕ) : ℤ) by push_cast; ring] at h2
        have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (Int.natCast_dvd_natCast.1 h2)
        exact hp2 this
      have hcop : IsCoprime ((p : ℤ) ^ (θ + 1)) ((x : ℤ) ^ k - 1) :=
        ((hpZ.irreducible.coprime_iff_not_dvd).2 hnot).pow_left
      have := hcop.dvd_of_dvd_mul_left hsq
      refine Int.modEq_iff_dvd.2 ?_
      rw [show (-1 : ℤ) - (x : ℤ) ^ k = -((x : ℤ) ^ k + 1) by ring]
      exact (dvd_neg).2 this
    · left
      have hcop : IsCoprime ((p : ℤ) ^ (θ + 1)) ((x : ℤ) ^ k + 1) :=
        ((hpZ.irreducible.coprime_iff_not_dvd).2 hp1).pow_left
      have := hcop.dvd_of_dvd_mul_right hsq
      refine Int.modEq_iff_dvd.2 ?_
      rw [show (1 : ℤ) - (x : ℤ) ^ k = -((x : ℤ) ^ k - 1) by ring]
      exact (dvd_neg).2 this

/-- A sum of `s` integers, each `≡ 0, 1` or `-1 (mod M)`, is `≡ a - b (mod M)` with `a + b ≤ s`. -/
lemma sum_modEq_of_mem_zero_one_neg_one {M : ℤ} : ∀ {s : ℕ} (f : Fin s → ℤ),
    (∀ i, f i ≡ 0 [ZMOD M] ∨ f i ≡ 1 [ZMOD M] ∨ f i ≡ -1 [ZMOD M]) →
    ∃ a b : ℕ, a + b ≤ s ∧ ∑ i, f i ≡ a - b [ZMOD M]
  | 0, _, _ => ⟨0, 0, le_rfl, by simp [Int.ModEq.refl]⟩
  | s + 1, f, hf => by
    obtain ⟨a, b, hab, h⟩ := sum_modEq_of_mem_zero_one_neg_one (fun i => f (Fin.castSucc i))
      fun i => hf _
    rw [Fin.sum_univ_castSucc]
    rcases hf (Fin.last s) with h0 | h1 | h2
    · exact ⟨a, b, by omega, by simpa using h.add h0⟩
    · exact ⟨a + 1, b, by omega, by have := h.add h1; push_cast; convert this using 1; ring⟩
    · exact ⟨a, b + 1, by omega, by have := h.add h2; push_cast; convert this using 1; ring⟩

/-- **Theorem 398** (Hardy–Wright). For an odd prime `p` and `θ ≥ 0`, with `k = p^θ (p - 1)/2`
(the book's `G{½ p^θ (p - 1)}`), if all large numbers are sums of `s` `k`th powers then
`s ≥ (p^(θ+1) - 1)/2`: the numbers `p^(θ+1) m + (p^(θ+1) - 1)/2` need that many. -/
@[kb "hardywright2008" "Thm 398, p. 448"]
theorem half_prime_pow_le_of_eventually_isSumOfPowers {p θ s : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hs : ∀ᶠ n in atTop, IsSumOfPowers (p ^ θ * (p - 1) / 2) s n) :
    (p ^ (θ + 1) - 1) / 2 ≤ s := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hk : p ^ θ * (p - 1) / 2 ≠ 0 := by
    have : 2 ≤ p ^ θ * (p - 1) := by
      have : 1 ≤ p ^ θ := Nat.one_le_pow _ _ hp.pos
      nlinarith [show 2 ≤ p - 1 by omega]
    omega
  obtain ⟨M, hM⟩ : ∃ M, M = p ^ (θ + 1) := ⟨_, rfl⟩
  rw [← hM]
  have hMpos : 3 ≤ M := by
    have : p ≤ M := by rw [hM]; exact Nat.le_self_pow (by omega) p
    omega
  have hModd : M % 2 = 1 := by
    rw [hM, Nat.pow_mod]; rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · simp [h]
  set h := (M - 1) / 2 with hh
  refine le_of_frequently_not hk (fun n₀ => ⟨M * n₀ + h, ?_, ?_⟩) hs
  · nlinarith
  rintro ⟨x, hx⟩
  obtain ⟨a, b, hab, hcong⟩ := sum_modEq_of_mem_zero_one_neg_one (M := (M : ℤ))
    (fun i => ((x i : ℤ)) ^ (p ^ θ * (p - 1) / 2)) fun i => by
      have := pow_half_totient_mod (θ := θ) hp hp2 (x i); rw [hM]; push_cast; exact this
  have hx' : ∑ i, ((x i : ℤ)) ^ (p ^ θ * (p - 1) / 2) = (M * n₀ + h : ℕ) := by
    rw [← hx]; push_cast; rfl
  rw [hx'] at hcong
  -- `h - (a - b)` is a multiple of `M` strictly between `0` and `M`
  have hdvd := (Int.ModEq.dvd hcong)
  have hmul : ((M : ℤ)) ∣ (h : ℤ) - (a - b) := by
    have : ((a : ℤ) - b) - ((M * n₀ + h : ℕ) : ℤ) = -(((h : ℤ) - (a - b)) + M * n₀) := by
      push_cast; ring
    rw [this, dvd_neg] at hdvd
    exact (dvd_add_left (dvd_mul_right _ _)).1 hdvd
  obtain ⟨c, hc⟩ := hmul
  have h2h : 2 * h + 1 = M := by omega
  have hlt1 : (0 : ℤ) < (h : ℤ) - (a - b) := by
    have : (a : ℤ) + b < h := by exact_mod_cast (show a + b < h by omega)
    have : (0 : ℤ) ≤ b := by positivity
    linarith
  have hlt2 : (h : ℤ) - (a - b) < M := by
    have : (a : ℤ) + b < h := by exact_mod_cast (show a + b < h by omega)
    have : (0 : ℤ) ≤ a := by positivity
    have : (2 * h + 1 : ℤ) = M := by exact_mod_cast h2h
    linarith
  rw [hc] at hlt1 hlt2
  have hM0 : (0 : ℤ) < M := by positivity
  have : 0 < c := pos_of_mul_pos_right hlt1 hM0.le
  have : c < 1 := by nlinarith
  omega

/-- A `(3k)`th power is a `k`th power, so sums of `s` `(3k)`th powers are sums of `s` `k`th powers. -/
lemma IsSumOfPowers.of_mul {k m s n : ℕ} (h : IsSumOfPowers (m * k) s n) : IsSumOfPowers k s n := by
  obtain ⟨x, rfl⟩ := h
  exact ⟨fun i => x i ^ m, by simp [← pow_mul]⟩

/-- **Theorem 399** (Hardy–Wright). For `θ ≥ 2`, if all large numbers are sums of `s` `(3 · 2^θ)`th
powers then `s ≥ 2^(θ+2)`. -/
@[kb "hardywright2008" "Thm 399, p. 449"]
theorem two_pow_le_of_eventually_isSumOfPowers_three_mul {θ s : ℕ} (hθ : 2 ≤ θ)
    (hs : ∀ᶠ n in atTop, IsSumOfPowers (3 * 2 ^ θ) s n) : 2 ^ (θ + 2) ≤ s :=
  two_pow_le_of_eventually_isSumOfPowers hθ (hs.mono fun _ h => h.of_mul)

/-- **Theorem 400** (Hardy–Wright). The lower bounds for `G(k)`: if all large numbers are sums of
`s` `k`th powers, then (i) `s ≥ 2^(θ+2)` if `k` is `2^θ` or `3 · 2^θ` with `θ ≥ 2`;
(ii) `s ≥ p^(θ+1)` if `p > 2` and `k = p^θ (p - 1)`; (iii) `s ≥ (p^(θ+1) - 1)/2` if `p > 2` and
`k = p^θ (p - 1)/2`; (iv) `s ≥ k + 1` in any case (`k ≥ 2`). -/
@[kb "hardywright2008" "Thm 400, p. 449"]
theorem lower_bounds_asymptoticWaring {k s : ℕ} (hs : ∀ᶠ n in atTop, IsSumOfPowers k s n) :
    (∀ θ, 2 ≤ θ → (k = 2 ^ θ ∨ k = 3 * 2 ^ θ) → 2 ^ (θ + 2) ≤ s) ∧
    (∀ p θ, p.Prime → p ≠ 2 → k = p ^ θ * (p - 1) → p ^ (θ + 1) ≤ s) ∧
    (∀ p θ, p.Prime → p ≠ 2 → k = p ^ θ * (p - 1) / 2 → (p ^ (θ + 1) - 1) / 2 ≤ s) ∧
    (2 ≤ k → k + 1 ≤ s) := by
  refine ⟨fun θ hθ hk => ?_, fun p θ hp hp2 hk => ?_, fun p θ hp hp2 hk => ?_, fun hk => ?_⟩
  · rcases hk with rfl | rfl
    · exact two_pow_le_of_eventually_isSumOfPowers hθ hs
    · exact two_pow_le_of_eventually_isSumOfPowers_three_mul hθ hs
  · subst hk; exact prime_pow_le_of_eventually_isSumOfPowers hp hp2 hs
  · subst hk; exact half_prime_pow_le_of_eventually_isSumOfPowers hp hp2 hs
  · exact succ_le_of_eventually_isSumOfPowers hk hs

end NTKB.HardyWright
