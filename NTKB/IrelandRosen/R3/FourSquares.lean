/-
Ireland–Rosen, Chapter 17, §7: Jacobi's theorem on four odd squares.
-/
import NTKB.IrelandRosen.R3.TwoSquares

/-!
# Jacobi's four-square theorem for `n ≡ 4 (mod 8)` (Proposition 17.7.2)

Ireland–Rosen, Proposition 17.7.2: for `n ≡ 4 (mod 8)`, the number of `(x, y, z, w)` with
`x, y, z, w` positive odd and `x² + y² + z² + w² = n` is the sum of the odd divisors of `n`.

We follow the book. Write `n = 2m`. Lemmas 3 and 4 turn the count into
`∑ χ(de)` over the positive odd `(d, e, s, t)` with `ds + et = m` (through Corollary 2 of
Proposition 17.6.1). The terms with `d = e` give `∑_{d ∣ m odd} m/(2d)`, the sum of the odd divisors
of `n`; the terms with `d > e` cancel under the involution of Lemmas 5 and 6,
`(d, e, s, t) ↦ (d', e', s', t')` with `k = ⌊e/(d - e)⌋` and
`d' = (k+1)t + (k+2)s`, `e' = kt + (k+1)s`, `s' = (k+1)e - kd`, `t' = (k+1)d - (k+2)e`
(the book's matrices `A_k`), which changes the sign of `χ(de)`; the terms with `d < e` are their
mirror images.
-/

namespace NTKB.IrelandRosen.FourSquares

open Finset

/-- `χ(n)` for the nontrivial character modulo `4`, on `ℤ`. -/
def chi (n : ℤ) : ℤ := ZMod.χ₄ (n : ZMod 4)

lemma chi_mul (a b : ℤ) : chi (a * b) = chi a * chi b := by
  simp [chi, map_mul]

lemma chi_of_odd {a : ℤ} (ha : a % 2 = 1) : chi a = if a % 4 = 1 then 1 else -1 := by
  unfold chi
  rw [ZMod.χ₄_int_eq_if_mod_four]
  rw [if_neg (by omega)]

/-- The set `S` of positive odd `(d, e, s, t)` with `ds + et = m`, as a finset. -/
def S (m : ℤ) : Finset (ℤ × ℤ × ℤ × ℤ) :=
  ((Icc 1 m) ×ˢ (Icc 1 m) ×ˢ (Icc 1 m) ×ˢ (Icc 1 m)).filter fun q =>
    q.1 % 2 = 1 ∧ q.2.1 % 2 = 1 ∧ q.2.2.1 % 2 = 1 ∧ q.2.2.2 % 2 = 1 ∧
      q.1 * q.2.2.1 + q.2.1 * q.2.2.2 = m

lemma mem_S {m : ℤ} {q : ℤ × ℤ × ℤ × ℤ} :
    q ∈ S m ↔ 0 < q.1 ∧ 0 < q.2.1 ∧ 0 < q.2.2.1 ∧ 0 < q.2.2.2 ∧
      q.1 % 2 = 1 ∧ q.2.1 % 2 = 1 ∧ q.2.2.1 % 2 = 1 ∧ q.2.2.2 % 2 = 1 ∧
      q.1 * q.2.2.1 + q.2.1 * q.2.2.2 = m := by
  obtain ⟨d, e, s, t⟩ := q
  simp only [S, mem_filter, mem_product, mem_Icc]
  constructor
  · rintro ⟨⟨⟨h1, -⟩, ⟨h2, -⟩, ⟨h3, -⟩, ⟨h4, -⟩⟩, h⟩
    exact ⟨by omega, by omega, by omega, by omega, h⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h⟩
    refine ⟨⟨⟨by omega, ?_⟩, ⟨by omega, ?_⟩, ⟨by omega, ?_⟩, ⟨by omega, ?_⟩⟩, h5, h6, h7, h8, h⟩ <;>
      nlinarith

/-! ### The involution (Lemmas 5 and 6) -/

/-- The book's map `Φ`, with `k = ⌊e / (d - e)⌋`. -/
def phi (q : ℤ × ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ × ℤ :=
  let d := q.1; let e := q.2.1; let s := q.2.2.1; let t := q.2.2.2
  let k := e / (d - e)
  ((k + 1) * t + (k + 2) * s, k * t + (k + 1) * s, (k + 1) * e - k * d, (k + 1) * d - (k + 2) * e)

/-- The defining inequalities of `k = ⌊e / (d - e)⌋`. -/
lemma floor_bounds {d e : ℤ} (hde : e < d) :
    (e / (d - e)) * (d - e) ≤ e ∧ e < (e / (d - e) + 1) * (d - e) := by
  have h := Int.emod_def e (d - e)
  have h1 := Int.emod_nonneg e (show d - e ≠ 0 by omega)
  have h2 := Int.emod_lt_of_pos e (show 0 < d - e by omega)
  constructor <;> nlinarith

/-- **Lemma 5 of §7.** `Φ` maps `S ∩ {d > e}` into itself. -/
lemma phi_mem {m : ℤ} {q : ℤ × ℤ × ℤ × ℤ} (hq : q ∈ S m) (hde : q.2.1 < q.1) :
    phi q ∈ S m ∧ (phi q).2.1 < (phi q).1 := by
  obtain ⟨d, e, s, t⟩ := q
  rw [mem_S] at hq ⊢
  simp only at hq hde ⊢
  obtain ⟨hd, he, hs, ht, hd2, he2, hs2, ht2, hm⟩ := hq
  simp only [phi]
  set k := e / (d - e) with hk
  obtain ⟨hk1, hk2⟩ := floor_bounds hde
  have hk0 : 0 ≤ k := Int.ediv_nonneg he.le (by omega)
  -- `k (d - e) ≠ e` since `d - e` is even and `e` odd
  have hne : k * (d - e) ≠ e := by
    intro h
    have : (2 : ℤ) ∣ d - e := ⟨(d - e) / 2, by omega⟩
    obtain ⟨c, hc⟩ := this
    rw [hc] at h
    have : e = 2 * (k * c) := by rw [← h]; ring
    omega
  have hk1' : k * (d - e) < e := lt_of_le_of_ne hk1 hne
  refine ⟨⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, ?_, ?_, ?_, ?_, ?_⟩, by nlinarith⟩
  · rcases Int.emod_two_eq_zero_or_one k with h | h <;>
    · have := Int.add_mul_emod_self_left
      rw [Int.add_emod, Int.mul_emod, Int.mul_emod (k + 2)]
      simp [Int.add_emod, h, ht2, hs2]
  · rcases Int.emod_two_eq_zero_or_one k with h | h <;>
      simp [Int.add_emod, Int.mul_emod, h, ht2, hs2]
  · rcases Int.emod_two_eq_zero_or_one k with h | h <;>
      simp [Int.sub_emod, Int.add_emod, Int.mul_emod, h, he2, hd2]
  · rcases Int.emod_two_eq_zero_or_one k with h | h <;>
      simp [Int.sub_emod, Int.add_emod, Int.mul_emod, h, he2, hd2]
  · linear_combination hm

/-- **Lemma 6 of §7.** `Φ` is an involution of `S ∩ {d > e}`. -/
lemma phi_phi {m : ℤ} {q : ℤ × ℤ × ℤ × ℤ} (hq : q ∈ S m) (hde : q.2.1 < q.1) : phi (phi q) = q := by
  obtain ⟨d, e, s, t⟩ := q
  rw [mem_S] at hq
  simp only at hq hde
  obtain ⟨hd, he, hs, ht, -, -, -, -, -⟩ := hq
  set k := e / (d - e) with hk
  have hk' : (k * t + (k + 1) * s) / ((k + 1) * t + (k + 2) * s - (k * t + (k + 1) * s)) = k := by
    rw [show (k + 1) * t + (k + 2) * s - (k * t + (k + 1) * s) = t + s by ring,
      show k * t + (k + 1) * s = s + (t + s) * k by ring, Int.add_mul_ediv_left _ _ (by omega),
      Int.ediv_eq_zero_of_lt hs.le (by omega), zero_add]
  simp only [phi]
  rw [← hk, hk']
  ext <;> simp <;> ring

lemma zmod4_of_odd {x : ℤ} (hx : x % 2 = 1) : (x : ZMod 4) = 1 ∨ (x : ZMod 4) = 3 := by
  have e : ∀ c : ℤ, (x : ZMod 4) = (c : ZMod 4) ↔ x % 4 = c % 4 := fun c => by
    have := ZMod.intCast_eq_intCast_iff' x c 4; push_cast at this; exact this
  rcases (by omega : x % 4 = 1 ∨ x % 4 = 3) with h | h
  · left; have := (e 1).2 (by rw [h]; rfl); simpa using this
  · right; have := (e 3).2 (by rw [h]; rfl); simpa using this

lemma chi_mul_odd {x y : ℤ} (hx : x % 2 = 1) (hy : y % 2 = 1) :
    chi (x * y) = if ((x - y : ℤ) : ZMod 4) = 0 then 1 else -1 := by
  have h1 := zmod4_of_odd hx
  have h2 := zmod4_of_odd hy
  unfold chi
  push_cast
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] <;> decide

/-- `Φ` changes the sign of `χ(de)` (the end of the proof of 17.7.2): `d' - e' = s + t` and
`ds + et ≡ 2 (mod 4)`. -/
lemma chi_phi {m : ℤ} (hm : m % 4 = 2) {q : ℤ × ℤ × ℤ × ℤ} (hq : q ∈ S m) (hde : q.2.1 < q.1) :
    chi ((phi q).1 * (phi q).2.1) = -chi (q.1 * q.2.1) := by
  have hq' := (phi_mem hq hde).1
  obtain ⟨d, e, s, t⟩ := q
  rw [mem_S] at hq hq'
  obtain ⟨-, -, -, -, hd2, he2, hs2, ht2, hm'⟩ := hq
  obtain ⟨-, -, -, -, hd2', he2', -, -, -⟩ := hq'
  simp only at hd2 he2 hs2 ht2 hm' hd2' he2' ⊢
  rw [chi_mul_odd hd2' he2', chi_mul_odd hd2 he2]
  have hdiff : (phi (d, e, s, t)).1 - (phi (d, e, s, t)).2.1 = s + t := by simp only [phi]; ring
  rw [hdiff]
  have hm4 : ((d * s + e * t : ℤ) : ZMod 4) = 2 := by
    rw [hm']
    have := (ZMod.intCast_eq_intCast_iff' m 2 4).2 (by push_cast; rw [hm])
    simpa using this
  push_cast at hm4 ⊢
  have key : ∀ a b c f : ZMod 4, (a = 1 ∨ a = 3) → (b = 1 ∨ b = 3) → (c = 1 ∨ c = 3) →
      (f = 1 ∨ f = 3) → a * c + b * f = 2 → (a - b = 0 ↔ ¬ c + f = 0) := by decide
  have := key _ _ _ _ (zmod4_of_odd hd2) (zmod4_of_odd he2) (zmod4_of_odd hs2) (zmod4_of_odd ht2) hm4
  by_cases h : (d : ZMod 4) - e = 0
  · rw [if_pos h, if_neg (this.1 h)]
  · rw [if_neg h, if_pos (not_not.1 (mt this.2 h))]; ring

/-- The terms with `d > e` cancel. -/
lemma sum_gt_eq_zero {m : ℤ} (hm : m % 4 = 2) :
    ∑ q ∈ (S m).filter (fun q => q.2.1 < q.1), chi (q.1 * q.2.1) = 0 := by
  refine sum_involution (fun q _ => phi q) (fun q hq => ?_) (fun q hq _ => ?_) (fun q hq => ?_)
    (fun q hq => ?_)
  · rw [mem_filter] at hq; rw [chi_phi hm hq.1 hq.2]; ring
  · rw [mem_filter] at hq
    intro h
    have := chi_phi hm hq.1 hq.2
    rw [h] at this
    have h1 : chi (q.1 * q.2.1) ≠ 0 := by
      have := (mem_S.1 hq.1)
      rw [chi_mul_odd this.2.2.2.2.1 this.2.2.2.2.2.1]; split_ifs <;> decide
    exact h1 (by linarith)
  · rw [mem_filter] at hq ⊢; exact phi_mem hq.1 hq.2
  · rw [mem_filter] at hq; exact phi_phi hq.1 hq.2

/-- The swap `(d, e, s, t) ↦ (e, d, t, s)`. -/
def swap (q : ℤ × ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ × ℤ := (q.2.1, q.1, q.2.2.2, q.2.2.1)

lemma swap_mem {m : ℤ} {q : ℤ × ℤ × ℤ × ℤ} (hq : q ∈ S m) : swap q ∈ S m := by
  obtain ⟨d, e, s, t⟩ := q
  rw [mem_S] at hq ⊢
  simp only [swap] at hq ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hq
  exact ⟨h2, h1, h4, h3, h6, h5, h8, h7, by linear_combination h9⟩

/-- The terms with `d < e` cancel too (mirror image of `d > e`). -/
lemma sum_lt_eq_zero {m : ℤ} (hm : m % 4 = 2) :
    ∑ q ∈ (S m).filter (fun q => q.1 < q.2.1), chi (q.1 * q.2.1) = 0 := by
  rw [← sum_gt_eq_zero hm]
  refine sum_nbij' swap swap (fun q hq => ?_) (fun q hq => ?_) (fun q _ => rfl) (fun q _ => rfl)
    (fun q _ => by simp only [swap]; rw [mul_comm])
  · simp only [mem_coe, mem_filter] at hq ⊢; exact ⟨swap_mem hq.1, hq.2⟩
  · simp only [mem_coe, mem_filter] at hq ⊢; exact ⟨swap_mem hq.1, hq.2⟩

lemma chi_sq_odd {d : ℤ} (hd : d % 2 = 1) : chi (d * d) = 1 := by
  rw [chi_mul_odd hd hd]; simp

/-- `∑_S χ(de) = #{(d, e, s, t) ∈ S : d = e}`. -/
lemma sum_S_eq_card {m : ℤ} (hm : m % 4 = 2) :
    ∑ q ∈ S m, chi (q.1 * q.2.1) = ((S m).filter (fun q => q.1 = q.2.1)).card := by
  have hsplit : ∀ q ∈ S m, chi (q.1 * q.2.1) =
      (if q.2.1 < q.1 then chi (q.1 * q.2.1) else 0) +
      (if q.1 < q.2.1 then chi (q.1 * q.2.1) else 0) + (if q.1 = q.2.1 then 1 else 0) := by
    intro q hq
    have hd := (mem_S.1 hq).2.2.2.2.1
    rcases lt_trichotomy q.2.1 q.1 with h | h | h
    · rw [if_pos h, if_neg (by omega), if_neg (by omega)]; ring
    · rw [if_neg (by omega), if_neg (by omega), if_pos h.symm, h, chi_sq_odd hd]
      ring
    · rw [if_neg (by omega), if_pos h, if_neg (by omega)]; ring
  rw [sum_congr rfl hsplit, sum_add_distrib, sum_add_distrib, ← sum_filter, ← sum_filter,
    sum_gt_eq_zero hm, sum_lt_eq_zero hm, ← sum_filter]
  simp

/-- The terms with `d = e`: for each odd `d ∣ M` (`m = 2M`), `s + t = m/d` has `M/d` solutions in
positive odd `s, t`. -/
lemma card_diag {M : ℕ} (hM : Odd M) :
    ((S (2 * M)).filter (fun q => q.1 = q.2.1)).card = ∑ d ∈ M.divisors, M / d := by
  rw [card_eq_sum_card_fiberwise (f := fun q => q.1) (t := M.divisors.map Nat.castEmbedding)]
  · rw [sum_map]
    refine sum_congr rfl fun d hd => ?_
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    obtain ⟨c, hc⟩ := Nat.dvd_of_mem_divisors hd
    have hcd : M / d = c := by rw [hc, Nat.mul_div_cancel_left _ hd0]
    rw [hcd]
    have hMc : (M : ℤ) = d * c := by exact_mod_cast hc
    have hd2 : (d : ℤ) % 2 = 1 := by
      have := Nat.odd_iff.1 (hM.of_dvd_nat ⟨c, hc⟩); omega
    have hdpos : (0 : ℤ) < d := by exact_mod_cast hd0
    rw [← card_range c]
    refine card_bij' (fun q _ => ((q.2.2.1 - 1) / 2).toNat)
      (fun i _ => ((d : ℤ), (d : ℤ), 2 * (i : ℤ) + 1, 2 * (c : ℤ) - 2 * i - 1)) ?_ ?_ ?_ ?_
    · rintro ⟨d', e', s', t'⟩ hq
      simp only [mem_filter, Nat.castEmbedding_apply] at hq
      obtain ⟨⟨hS, h1⟩, h2⟩ := hq
      rw [mem_S] at hS
      simp only at hS h1 h2
      obtain ⟨-, -, h3, h4, -, -, h7, h8, h9⟩ := hS
      subst h2 h1
      push_cast at h9
      have hst : (d : ℤ) * (s' + t') = d * (2 * c) := by linear_combination h9 + 2 * hMc
      have hst' : s' + t' = 2 * c := mul_left_cancel₀ hdpos.ne' hst
      rw [mem_range]; simp only; omega
    · intro i hi
      rw [mem_range] at hi
      simp only [mem_filter, Nat.castEmbedding_apply, mem_S]
      refine ⟨⟨⟨hdpos, hdpos, by omega, by omega, hd2, hd2, by omega, by omega, ?_⟩, trivial⟩, trivial⟩
      rw [hMc]; push_cast; ring
    · rintro ⟨d', e', s', t'⟩ hq
      simp only [mem_filter, Nat.castEmbedding_apply] at hq
      obtain ⟨⟨hS, h1⟩, h2⟩ := hq
      rw [mem_S] at hS
      simp only at hS h1 h2
      obtain ⟨-, -, h3, h4, -, -, h7, h8, h9⟩ := hS
      subst h2 h1
      push_cast at h9
      have hst : (d : ℤ) * (s' + t') = d * (2 * c) := by linear_combination h9 + 2 * hMc
      have hst' : s' + t' = 2 * c := mul_left_cancel₀ hdpos.ne' hst
      simp only [Prod.mk.injEq]
      refine ⟨trivial, trivial, by omega, by omega⟩
    · intro i _
      simp only
      omega
  · intro q hq
    simp only [mem_coe, mem_filter, mem_S] at hq
    obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, h10⟩ := hq
    simp only [mem_coe, mem_map, Nat.castEmbedding_apply]
    refine ⟨q.1.toNat, ?_, Int.toNat_of_nonneg h1.le⟩
    rw [Nat.mem_divisors]
    refine ⟨?_, by have := hM.pos; omega⟩
    obtain ⟨k, hk⟩ : (2 : ℤ) ∣ q.2.2.1 + q.2.2.2 := ⟨(q.2.2.1 + q.2.2.2) / 2, by omega⟩
    have h11 : 2 * (M : ℤ) = 2 * (q.1 * k) := by
      rw [← h10] at h9; linear_combination -h9 + q.1 * hk
    have : (M : ℤ) = q.1 * k := by linarith
    have h' : (q.1.toNat : ℤ) ∣ M := ⟨k, by rw [Int.toNat_of_nonneg h1.le]; exact this⟩
    exact_mod_cast h'

/-! ### Lemmas 3 and 4 -/

lemma sq_mod_four (x : ℤ) : (x % 2 = 0 → x ^ 2 % 4 = 0) ∧ (x % 2 = 1 → x ^ 2 % 8 = 1) := by
  constructor
  · intro h; obtain ⟨k, rfl⟩ : ∃ k, x = 2 * k := ⟨x / 2, by omega⟩
    have : (2 * k) ^ 2 = 4 * (k * k) := by ring
    omega
  · intro h; obtain ⟨k, rfl⟩ : ∃ k, x = 2 * k + 1 := ⟨x / 2, by omega⟩
    have : (2 * k + 1) ^ 2 = 8 * (k * (k + 1) / 2) + 1 := by
      have h2 : (k * (k + 1)) % 2 = 0 := Int.even_iff.1 (Int.even_mul_succ_self k)
      have : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
      omega
    omega

/-- If `x² + y² = 2v` with `v` odd then `x, y` are odd. -/
lemma odd_of_sq_add_sq {x y v : ℤ} (h : x ^ 2 + y ^ 2 = 2 * v) (hv : v % 2 = 1) :
    x % 2 = 1 ∧ y % 2 = 1 := by
  have hx := sq_mod_four x
  have hy := sq_mod_four y
  rcases Int.emod_two_eq_zero_or_one x with h1 | h1 <;>
    rcases Int.emod_two_eq_zero_or_one y with h2 | h2
  · have := hx.1 h1; have := hy.1 h2; omega
  · have := hx.1 h1; have := hy.2 h2; omega
  · have := hx.2 h1; have := hy.1 h2; omega
  · exact ⟨h1, h2⟩

/-- The positive solutions of `x² + y² = 2u`. -/
def P (u : ℤ) : Finset (ℤ × ℤ) :=
  ((Icc 1 (2 * u)) ×ˢ (Icc 1 (2 * u))).filter fun v => v.1 ^ 2 + v.2 ^ 2 = 2 * u

lemma mem_P {u : ℤ} {v : ℤ × ℤ} : v ∈ P u ↔ 0 < v.1 ∧ 0 < v.2 ∧ v.1 ^ 2 + v.2 ^ 2 = 2 * u := by
  simp only [P, mem_filter, mem_product, mem_Icc]
  constructor
  · rintro ⟨⟨⟨h1, -⟩, ⟨h2, -⟩⟩, h⟩; exact ⟨by omega, by omega, h⟩
  · rintro ⟨h1, h2, h⟩
    refine ⟨⟨⟨by omega, ?_⟩, ⟨by omega, ?_⟩⟩, h⟩ <;> nlinarith

/-- Corollary 2 of 17.6.1 in the form used here: for `u > 0` odd,
`#P(u) = ∑_{d ∣ u} χ(d)`. -/
lemma card_P {u : ℕ} (hu : 0 < u) (hodd : Odd u) :
    ((P u).card : ℤ) = ∑ d ∈ u.divisors, chi d := by
  have h := NTKB.IrelandRosen.TwoSquares.ncard_pos_pos_two_mul hu hodd
  have hset : {v : ℤ × ℤ | 0 < v.1 ∧ 0 < v.2 ∧ v.1 ^ 2 + v.2 ^ 2 = 2 * u} = ↑(P u) := by
    ext v; simp only [Set.mem_setOf_eq, mem_coe, mem_P]
  rw [hset, Set.ncard_coe_finset] at h
  rw [h]
  refine sum_congr rfl fun d _ => ?_
  simp [chi, NTKB.HardyWright.chi4]

/-- The positive odd solutions of `x² + y² + z² + w² = n`. -/
def Q (n : ℤ) : Finset (ℤ × ℤ × ℤ × ℤ) :=
  ((Icc 1 n) ×ˢ (Icc 1 n) ×ˢ (Icc 1 n) ×ˢ (Icc 1 n)).filter fun q =>
    q.1 % 2 = 1 ∧ q.2.1 % 2 = 1 ∧ q.2.2.1 % 2 = 1 ∧ q.2.2.2 % 2 = 1 ∧
      q.1 ^ 2 + q.2.1 ^ 2 + q.2.2.1 ^ 2 + q.2.2.2 ^ 2 = n

lemma mem_Q {n : ℤ} {q : ℤ × ℤ × ℤ × ℤ} :
    q ∈ Q n ↔ 0 < q.1 ∧ 0 < q.2.1 ∧ 0 < q.2.2.1 ∧ 0 < q.2.2.2 ∧
      q.1 % 2 = 1 ∧ q.2.1 % 2 = 1 ∧ q.2.2.1 % 2 = 1 ∧ q.2.2.2 % 2 = 1 ∧
      q.1 ^ 2 + q.2.1 ^ 2 + q.2.2.1 ^ 2 + q.2.2.2 ^ 2 = n := by
  obtain ⟨x, y, z, w⟩ := q
  simp only [Q, mem_filter, mem_product, mem_Icc]
  constructor
  · rintro ⟨⟨⟨h1, -⟩, ⟨h2, -⟩, ⟨h3, -⟩, ⟨h4, -⟩⟩, h⟩
    exact ⟨by omega, by omega, by omega, by omega, h⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h⟩
    refine ⟨⟨⟨by omega, ?_⟩, ⟨by omega, ?_⟩, ⟨by omega, ?_⟩, ⟨by omega, ?_⟩⟩, h5, h6, h7, h8, h⟩ <;>
      nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z, sq_nonneg w]

/-- The odd `u` with `0 < u < m`. -/
def U (m : ℤ) : Finset ℤ := (Icc 1 (m - 1)).filter (· % 2 = 1)

/-- **Lemma 3 of §7.** `N = ∑_{u + v = m, u, v odd} #P(u) #P(v)`. -/
lemma card_Q {m : ℤ} (hm : m % 4 = 2) :
    (Q (2 * m)).card = ∑ u ∈ U m, (P u).card * (P (m - u)).card := by
  rw [card_eq_sum_card_fiberwise (f := fun q => (q.1 ^ 2 + q.2.1 ^ 2) / 2) (t := U m)]
  · refine sum_congr rfl fun u hu => ?_
    simp only [U, mem_filter, mem_Icc] at hu
    rw [← card_product]
    have hmu : (m - u) % 2 = 1 := by omega
    refine card_bij' (fun q _ => ((q.1, q.2.1), (q.2.2.1, q.2.2.2)))
      (fun v _ => (v.1.1, v.1.2, v.2.1, v.2.2)) ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl)
    · rintro ⟨x, y, z, w⟩ hq
      simp only [mem_filter, mem_Q] at hq
      obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, h10⟩ := hq
      have hx := (sq_mod_four x).2 h5
      have hy := (sq_mod_four y).2 h6
      have hxy : x ^ 2 + y ^ 2 = 2 * u := by omega
      simp only [mem_product, mem_P]
      exact ⟨⟨h1, h2, hxy⟩, ⟨h3, h4, by linear_combination h9 - hxy⟩⟩
    · rintro ⟨⟨x, y⟩, ⟨z, w⟩⟩ hv
      simp only [mem_product, mem_P] at hv
      obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5, h6⟩⟩ := hv
      obtain ⟨hx, hy⟩ := odd_of_sq_add_sq h3 hu.2
      obtain ⟨hz, hw⟩ := odd_of_sq_add_sq h6 hmu
      simp only [mem_filter, mem_Q]
      refine ⟨⟨h1, h2, h4, h5, hx, hy, hz, hw, by linear_combination h3 + h6⟩, ?_⟩
      rw [h3]; omega
  · intro q hq
    simp only [mem_coe, mem_Q] at hq
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hq
    have hx := (sq_mod_four q.1).2 h5
    have hy := (sq_mod_four q.2.1).2 h6
    have hz := (sq_mod_four q.2.2.1).2 h7
    have hw := (sq_mod_four q.2.2.2).2 h8
    have := sq_nonneg q.1; have := sq_nonneg q.2.1
    have := sq_nonneg q.2.2.1; have := sq_nonneg q.2.2.2
    simp only [mem_coe, U, mem_filter, mem_Icc]
    omega

/-- The positive divisors of `u`, in `ℤ`. -/
def divZ (u : ℤ) : Finset ℤ := (Icc 1 u).filter (· ∣ u)

lemma sum_divisors_eq_divZ {u : ℕ} (hu : 0 < u) (f : ℤ → ℤ) :
    ∑ d ∈ u.divisors, f d = ∑ d ∈ divZ u, f d := by
  rw [show (∑ d ∈ u.divisors, f d) = ∑ d ∈ u.divisors.map Nat.castEmbedding, f d by
    rw [sum_map]; rfl]
  congr 1
  ext d
  simp only [mem_map, Nat.mem_divisors, Nat.castEmbedding_apply, divZ, mem_filter, mem_Icc]
  constructor
  · rintro ⟨d', ⟨hd', -⟩, rfl⟩
    have := Nat.pos_of_dvd_of_pos hd' hu
    refine ⟨⟨by exact_mod_cast this, by exact_mod_cast Nat.le_of_dvd hu hd'⟩,
      by exact_mod_cast hd'⟩
  · rintro ⟨⟨h1, -⟩, h2⟩
    refine ⟨d.toNat, ⟨?_, by omega⟩, by omega⟩
    have : ((d.toNat : ℕ) : ℤ) ∣ (u : ℤ) := by rw [Int.toNat_of_nonneg (by omega)]; exact h2
    exact_mod_cast this

/-- **Lemma 4 of §7.** `N = ∑_{(d, e, s, t) ∈ S} χ(de)`. -/
lemma sum_U_eq_sum_S {m : ℤ} (hm : m % 4 = 2) :
    ∑ u ∈ U m, (((P u).card * (P (m - u)).card : ℕ) : ℤ) = ∑ q ∈ S m, chi (q.1 * q.2.1) := by
  have hA : ∀ u ∈ U m, (((P u).card * (P (m - u)).card : ℕ) : ℤ) =
      ∑ x ∈ (divZ u) ×ˢ (divZ (m - u)), chi (x.1 * x.2) := by
    intro u hu
    simp only [U, mem_filter, mem_Icc] at hu
    have hu0 : 0 < u := by omega
    have hv0 : 0 < m - u := by omega
    push_cast
    have e1 := card_P (u := u.toNat) (by omega) (by rw [Nat.odd_iff]; omega)
    have e2 := card_P (u := (m - u).toNat) (by omega) (by rw [Nat.odd_iff]; omega)
    rw [Int.toNat_of_nonneg hu0.le] at e1
    rw [Int.toNat_of_nonneg hv0.le] at e2
    rw [e1, e2, sum_divisors_eq_divZ (by omega), sum_divisors_eq_divZ (by omega),
      Int.toNat_of_nonneg hu0.le, Int.toNat_of_nonneg hv0.le, sum_mul_sum, sum_product]
    simp_rw [chi_mul]
  rw [sum_congr rfl hA, sum_sigma']
  refine sum_bij' (fun x _ => (x.2.1, x.2.2, x.1 / x.2.1, (m - x.1) / x.2.2))
    (fun q _ => ⟨q.1 * q.2.2.1, (q.1, q.2.1)⟩) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · rintro ⟨u, d, e⟩ hx
    simp only [mem_sigma, mem_product, U, divZ, mem_filter, mem_Icc] at hx
    obtain ⟨⟨⟨hu1, hu2⟩, hu3⟩, ⟨⟨hd1, hd2⟩, hd3⟩, ⟨he1, he2⟩, he3⟩ := hx
    obtain ⟨s, rfl⟩ := hd3
    obtain ⟨t, ht⟩ := he3
    have hd0 : d ≠ 0 := by omega
    have he0 : e ≠ 0 := by omega
    rw [mem_S]
    simp only
    rw [Int.mul_ediv_cancel_left _ hd0, ht, Int.mul_ediv_cancel_left _ he0]
    have hs0 : 0 < s := by
      by_contra h; push_neg at h; nlinarith
    have ht0 : 0 < t := by
      by_contra h; push_neg at h; nlinarith
    have hds : Odd d ∧ Odd s := Int.odd_mul.1 (Int.odd_iff.2 hu3)
    have het : Odd e ∧ Odd t := Int.odd_mul.1 (Int.odd_iff.2 (by rw [← ht]; omega))
    exact ⟨by omega, by omega, hs0, ht0, Int.odd_iff.1 hds.1, Int.odd_iff.1 het.1,
      Int.odd_iff.1 hds.2, Int.odd_iff.1 het.2, by linear_combination -ht⟩
  · rintro ⟨d, e, s, t⟩ hq
    rw [mem_S] at hq
    simp only at hq
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hq
    simp only [mem_sigma, mem_product, U, divZ, mem_filter, mem_Icc]
    have hds : d * s ≤ d * s := le_rfl
    refine ⟨⟨⟨by nlinarith, by nlinarith⟩, ?_⟩, ⟨⟨by omega, by nlinarith⟩, ⟨s, by ring⟩⟩,
      ⟨⟨by omega, by nlinarith⟩, ⟨t, by linear_combination -h9⟩⟩⟩
    · rw [Int.mul_emod, h5, h7]; rfl
  · rintro ⟨u, d, e⟩ hx
    simp only [mem_sigma, mem_product, U, divZ, mem_filter, mem_Icc] at hx
    obtain ⟨-, ⟨-, hd3⟩, -⟩ := hx
    simp only [Sigma.mk.injEq]
    exact ⟨Int.mul_ediv_cancel' hd3, HEq.rfl⟩
  · rintro ⟨d, e, s, t⟩ hq
    rw [mem_S] at hq
    simp only at hq
    obtain ⟨h1, h2, -, -, -, -, -, -, h9⟩ := hq
    simp only [Prod.mk.injEq]
    refine ⟨trivial, trivial, Int.mul_ediv_cancel_left _ (by omega), ?_⟩
    rw [show m - d * s = e * t by linear_combination -h9, Int.mul_ediv_cancel_left _ (by omega)]

/-- **Proposition 17.7.2 (Jacobi).** Let `n ≡ 4 (mod 8)`. The number of integral solutions
`(x, y, z, w)`, `x, y, z, w` positive and odd, of `x² + y² + z² + w² = n` is the sum of the positive
odd divisors of `n`. -/
@[kb "irelandrosen1990" "Prop 17.7.2, p. 293"]
theorem ncard_odd_four_squares {n : ℕ} (hn : n % 8 = 4) :
    {v : ℤ × ℤ × ℤ × ℤ | 0 < v.1 ∧ 0 < v.2.1 ∧ 0 < v.2.2.1 ∧ 0 < v.2.2.2 ∧
      v.1 % 2 = 1 ∧ v.2.1 % 2 = 1 ∧ v.2.2.1 % 2 = 1 ∧ v.2.2.2 % 2 = 1 ∧
      v.1 ^ 2 + v.2.1 ^ 2 + v.2.2.1 ^ 2 + v.2.2.2 ^ 2 = n}.ncard =
      ∑ d ∈ n.divisors.filter Odd, d := by
  obtain ⟨M, hM⟩ : ∃ M, n = 4 * M := ⟨n / 4, by omega⟩
  have hMo : Odd M := Nat.odd_iff.2 (by omega)
  have hset : {v : ℤ × ℤ × ℤ × ℤ | 0 < v.1 ∧ 0 < v.2.1 ∧ 0 < v.2.2.1 ∧ 0 < v.2.2.2 ∧
      v.1 % 2 = 1 ∧ v.2.1 % 2 = 1 ∧ v.2.2.1 % 2 = 1 ∧ v.2.2.2 % 2 = 1 ∧
      v.1 ^ 2 + v.2.1 ^ 2 + v.2.2.1 ^ 2 + v.2.2.2 ^ 2 = n} = ↑(Q (2 * (2 * M))) := by
    ext v; simp only [Set.mem_setOf_eq, mem_coe, mem_Q, hM]; push_cast; ring_nf
  have hm : (2 * (M : ℤ)) % 4 = 2 := by have := Nat.odd_iff.1 hMo; omega
  rw [hset, Set.ncard_coe_finset]
  have key : ((Q (2 * (2 * M))).card : ℤ) = ∑ d ∈ M.divisors, (M / d : ℕ) := by
    rw [card_Q hm, Nat.cast_sum, sum_U_eq_sum_S hm, sum_S_eq_card hm, card_diag hMo]
  have key' : (Q (2 * (2 * M))).card = ∑ d ∈ M.divisors, M / d := by exact_mod_cast key
  rw [key', Nat.sum_div_divisors M (fun d => d)]
  congr 1
  ext d
  simp only [Nat.mem_divisors, mem_filter, hM]
  constructor
  · rintro ⟨hd, hM0⟩
    have hdo : Odd d := hMo.of_dvd_nat hd
    exact ⟨⟨dvd_mul_of_dvd_right hd 4, by omega⟩, hdo⟩
  · rintro ⟨⟨hd, h0⟩, hdo⟩
    refine ⟨?_, by omega⟩
    have hc : Nat.Coprime d 4 := by
      rw [show (4 : ℕ) = 2 ^ 2 by rfl]
      have h2 : ¬ 2 ∣ d := by have := Nat.odd_iff.1 hdo; omega
      exact Nat.Coprime.pow_right 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h2).symm
    exact hc.dvd_of_dvd_mul_left hd

end NTKB.IrelandRosen.FourSquares
