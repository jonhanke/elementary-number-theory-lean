/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Attr
import NTKB.Elementary.HardyWright.ArithmeticFunctions.SumTwoSquares
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities

/-!
# Hardy–Wright, §§ 21.9–21.10: the problem of Prouhet and Tarry

For integers `a₁, …, a_s` write `S_h(a) = a₁ʰ + ⋯ + a_sʰ`.  A non-trivial solution of (21.9.3)
is a family of `j` sets of `s` integers having the same `S_h` for `1 ≤ h ≤ k`, no two of which
are permutations of one another.  `prouhetTarryNumber k j` is the book's `P(k, j)`, the least `s`
for which such a solution exists.

* Section 21.9: if `s ≤ k` the equations `S_h(a) = S_h(b)` (`1 ≤ h ≤ k`) only have trivial
  solutions (`multiset_map_eq_of_sum_pow_eq`), by Newton's relations.
* Theorem 408: a non-trivial solution has `k + 1 ≤ s`, and a non-trivial solution for `j` sets
  gives one for two sets, hence `k + 1 ≤ P(k, 2) ≤ P(k, j)`.
* Theorem 409: `P(k, j) ≤ k (k + 1) / 2 + 1`, by a pigeonhole argument.
* Theorem 410: `P(k, j) = k + 1` for `k = 2, 3, 5` and all `j ≥ 2`, from explicit solutions.
* Theorem 411: `P(k, 2) = k + 1` for `1 ≤ k ≤ 6`, from explicit solutions.
-/

open Finset

namespace NTKB.HardyWright

/-- A non-trivial solution of (21.9.3): `j` sets of `s` integers with equal power sums
`S_h` for `1 ≤ h ≤ k`, no two of which are permutations of one another. -/
def IsNontrivialPTSolution (k j s : ℕ) (a : Fin j → Fin s → ℤ) : Prop :=
  (∀ h, 1 ≤ h → h ≤ k → ∀ u v, ∑ i, a u i ^ h = ∑ i, a v i ^ h) ∧
    ∀ u v, u ≠ v → (Finset.univ.val.map (a u)) ≠ (Finset.univ.val.map (a v))

/-- `P(k, j)`: the least `s` for which (21.9.3) has a non-trivial solution. -/
noncomputable def prouhetTarryNumber (k j : ℕ) : ℕ :=
  sInf {s | ∃ a : Fin j → Fin s → ℤ, IsNontrivialPTSolution k j s a}

/-! ### Section 21.9: trivial solutions -/

/-- **Trivial solutions** (Hardy–Wright, § 21.9). If `s ≤ k` and `S_h(a) = S_h(b)` for
`1 ≤ h ≤ k`, then `b` is a permutation of `a`. -/
@[kb "hardywright2008" "Section 21.9, p. 454"]
theorem multiset_map_eq_of_sum_pow_eq {s k : ℕ} (hsk : s ≤ k) (a b : Fin s → ℤ)
    (h : ∀ h, 1 ≤ h → h ≤ k → ∑ i, a i ^ h = ∑ i, b i ^ h) :
    Finset.univ.val.map a = Finset.univ.val.map b := by
  have hps : ∀ (c : Fin s → ℤ) n,
      MvPolynomial.aeval c (MvPolynomial.psum (Fin s) ℤ n) = ∑ i, c i ^ n := by
    intro c n; simp [MvPolynomial.psum]
  have hE : ∀ m, m ≤ s → MvPolynomial.aeval a (MvPolynomial.esymm (Fin s) ℤ m) =
      MvPolynomial.aeval b (MvPolynomial.esymm (Fin s) ℤ m) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      rcases Nat.eq_zero_or_pos m with rfl | hpos
      · simp
      · have key := MvPolynomial.mul_esymm_eq_sum (Fin s) ℤ m
        have ka := congrArg (MvPolynomial.aeval a) key
        have kb := congrArg (MvPolynomial.aeval b) key
        simp only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum, hps] at ka kb
        have : (m : ℤ) * MvPolynomial.aeval a (MvPolynomial.esymm (Fin s) ℤ m) =
            m * MvPolynomial.aeval b (MvPolynomial.esymm (Fin s) ℤ m) := by
          rw [ka, kb]
          congr 1
          apply Finset.sum_congr rfl
          intro x hx
          rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hx
          obtain ⟨hx1, hx2⟩ := hx
          rw [ih x.1 (by omega) (by omega), h x.2 (by omega) (by omega)]
        exact mul_left_cancel₀ (by exact_mod_cast hpos.ne') this
  have hcard : ∀ c : Fin s → ℤ, Multiset.card (Finset.univ.val.map c) = s := by simp
  have hpoly : ((Finset.univ.val.map a).map fun t => (Polynomial.X : Polynomial ℤ) -
        Polynomial.C t).prod =
      ((Finset.univ.val.map b).map fun t => (Polynomial.X : Polynomial ℤ) -
        Polynomial.C t).prod := by
    ext n
    have hdeg : ∀ c : Fin s → ℤ, (((Finset.univ.val.map c).map fun t =>
        (Polynomial.X : Polynomial ℤ) - Polynomial.C t).prod).natDegree = s := by
      intro c; rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card]; simp
    by_cases hn : n ≤ s
    · rw [Multiset.prod_X_sub_C_coeff _ (by simpa using hn),
        Multiset.prod_X_sub_C_coeff _ (by simpa using hn)]
      simp only [hcard]
      rw [← MvPolynomial.aeval_esymm_eq_multiset_esymm (R := ℤ) (σ := Fin s) (n := s - n) a,
        ← MvPolynomial.aeval_esymm_eq_multiset_esymm (R := ℤ) (σ := Fin s) (n := s - n) b,
        hE _ (by omega)]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; omega)]
  have := congrArg Polynomial.roots hpoly
  rwa [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at this

/-! ### Theorem 408 -/

/-- **Theorem 408** (Hardy–Wright), first inequality: a non-trivial solution of (21.9.3) with
at least two sets has `k + 1 ≤ s`. -/
@[kb "hardywright2008" "Thm 408, p. 455"]
theorem succ_le_of_isNontrivialPTSolution {k j s : ℕ} {a : Fin j → Fin s → ℤ} (hj : 2 ≤ j)
    (h : IsNontrivialPTSolution k j s a) : k + 1 ≤ s := by
  by_contra hlt
  have hsk : s ≤ k := by omega
  have h01 : (⟨0, by omega⟩ : Fin j) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  exact h.2 _ _ h01 (multiset_map_eq_of_sum_pow_eq hsk _ _ fun n hn1 hnk => h.1 n hn1 hnk _ _)

/-- A non-trivial solution of (21.9.3) for `j ≥ 2` sets includes one for two sets with the same
`s`. -/
theorem isNontrivialPTSolution_two_of_le {k j s : ℕ} {a : Fin j → Fin s → ℤ} (hj : 2 ≤ j)
    (h : IsNontrivialPTSolution k j s a) :
    IsNontrivialPTSolution k 2 s (fun u => a (Fin.castLE hj u)) :=
  ⟨fun n hn1 hnk _ _ => h.1 n hn1 hnk _ _, fun _ _ huv =>
    h.2 _ _ fun e => huv (Fin.castLE_injective hj e)⟩

/-- **Theorem 408** (Hardy–Wright): `P(k, 2) ≤ P(k, j)` for `j ≥ 2`, provided a non-trivial
solution for `j` sets exists. -/
@[kb "hardywright2008" "Thm 408, p. 455"]
theorem prouhetTarryNumber_two_le {k j : ℕ} (hj : 2 ≤ j)
    (hex : ∃ s a, IsNontrivialPTSolution k j s a) :
    prouhetTarryNumber k 2 ≤ prouhetTarryNumber k j := by
  obtain ⟨s, a, ha⟩ := hex
  have hne : {s | ∃ a : Fin j → Fin s → ℤ, IsNontrivialPTSolution k j s a}.Nonempty :=
    ⟨s, a, ha⟩
  obtain ⟨b, hb⟩ := Nat.sInf_mem hne
  exact Nat.sInf_le ⟨_, isNontrivialPTSolution_two_of_le hj hb⟩

/-- **Theorem 408** (Hardy–Wright): `k + 1 ≤ P(k, j)` for `j ≥ 2`, provided a non-trivial
solution exists. -/
@[kb "hardywright2008" "Thm 408, p. 455"]
theorem succ_le_prouhetTarryNumber {k j : ℕ} (hj : 2 ≤ j)
    (hex : ∃ s a, IsNontrivialPTSolution k j s a) : k + 1 ≤ prouhetTarryNumber k j := by
  obtain ⟨s, a, ha⟩ := hex
  have hne : {s | ∃ a : Fin j → Fin s → ℤ, IsNontrivialPTSolution k j s a}.Nonempty :=
    ⟨s, a, ha⟩
  obtain ⟨b, hb⟩ := Nat.sInf_mem hne
  exact succ_le_of_isNontrivialPTSolution hj hb

/-- **Theorem 408** (Hardy–Wright), in the book's form `P(k, j) ≥ P(k, 2) ≥ k + 1`. -/
@[kb "hardywright2008" "Thm 408, p. 455"]
theorem succ_le_prouhetTarryNumber_two_le {k j : ℕ} (hj : 2 ≤ j)
    (hex : ∃ s a, IsNontrivialPTSolution k j s a) :
    k + 1 ≤ prouhetTarryNumber k 2 ∧ prouhetTarryNumber k 2 ≤ prouhetTarryNumber k j := by
  refine ⟨?_, prouhetTarryNumber_two_le hj hex⟩
  obtain ⟨s, a, ha⟩ := hex
  have hne : {s | ∃ a : Fin 2 → Fin s → ℤ, IsNontrivialPTSolution k 2 s a}.Nonempty :=
    ⟨s, _, isNontrivialPTSolution_two_of_le hj ha⟩
  obtain ⟨b, hb⟩ := Nat.sInf_mem hne
  exact succ_le_of_isNontrivialPTSolution le_rfl hb

/-! ### Theorem 411 -/

/-- Two sets of `s` integers with equal power sums for `1 ≤ h ≤ k` that are not permutations of
one another form a non-trivial solution for two sets. -/
lemma isNontrivialPTSolution_pair {k s : ℕ} (A B : Fin s → ℤ)
    (hsum : ∀ h, 1 ≤ h → h ≤ k → ∑ i, A i ^ h = ∑ i, B i ^ h)
    (hne : Finset.univ.val.map A ≠ Finset.univ.val.map B) :
    IsNontrivialPTSolution k 2 s ![A, B] := by
  refine ⟨fun h h1 hk u v => ?_, fun u v huv => ?_⟩
  · fin_cases u <;> fin_cases v <;> simp [hsum h h1 hk]
  · fin_cases u <;> fin_cases v
    · exact absurd rfl huv
    · exact hne
    · exact fun e => hne e.symm
    · exact absurd rfl huv

/-- If `s = k + 1` and a non-trivial solution for two sets exists, then `P(k, 2) = k + 1`. -/
lemma prouhetTarryNumber_two_eq_of {k : ℕ} (A B : Fin (k + 1) → ℤ)
    (hsum : ∀ h, 1 ≤ h → h ≤ k → ∑ i, A i ^ h = ∑ i, B i ^ h)
    (hne : Finset.univ.val.map A ≠ Finset.univ.val.map B) :
    prouhetTarryNumber k 2 = k + 1 := by
  have h1 : prouhetTarryNumber k 2 ≤ k + 1 :=
    Nat.sInf_le ⟨_, isNontrivialPTSolution_pair A B hsum hne⟩
  have h2 := (succ_le_prouhetTarryNumber_two_le (k := k) (j := 2) le_rfl
    ⟨_, _, isNontrivialPTSolution_pair A B hsum hne⟩).1
  omega

/-- **Theorem 411** (Hardy–Wright): `P(k, 2) = k + 1` for `1 ≤ k ≤ 6`.  The solutions
(§ 21.10) are `[0,3]₁ = [1,2]₁`, `[1,2,6]₂ = [0,4,5]₂`, `[0,4,7,11]₃ = [1,2,9,10]₃`,
`[1,2,10,14,18]₄ = [0,4,8,16,17]₄`, `[0,4,9,17,22,26]₅ = [1,2,12,14,24,25]₅` and
`[0,18,27,58,64,89,101]₆ = [1,13,38,44,75,84,102]₆`. -/
@[kb "hardywright2008" "Thm 411, p. 459"]
theorem prouhetTarryNumber_two_eq {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ 6) :
    prouhetTarryNumber k 2 = k + 1 := by
  interval_cases k
  · refine prouhetTarryNumber_two_eq_of ![0, 3] ![1, 2] ?_ (by decide +kernel)
    intro h h1 hk; interval_cases h; decide +kernel
  · refine prouhetTarryNumber_two_eq_of ![1, 2, 6] ![0, 4, 5] ?_ (by decide +kernel)
    intro h h1 hk; interval_cases h <;> decide +kernel
  · refine prouhetTarryNumber_two_eq_of ![0, 4, 7, 11] ![1, 2, 9, 10] ?_ (by decide +kernel)
    intro h h1 hk; interval_cases h <;> decide +kernel
  · refine prouhetTarryNumber_two_eq_of ![1, 2, 10, 14, 18] ![0, 4, 8, 16, 17] ?_
      (by decide +kernel)
    intro h h1 hk; interval_cases h <;> decide +kernel
  · refine prouhetTarryNumber_two_eq_of ![0, 4, 9, 17, 22, 26] ![1, 2, 12, 14, 24, 25] ?_
      (by decide +kernel)
    intro h h1 hk; interval_cases h <;> decide +kernel
  · refine prouhetTarryNumber_two_eq_of ![0, 18, 27, 58, 64, 89, 101]
      ![1, 13, 38, 44, 75, 84, 102] ?_ (by decide +kernel)
    intro h h1 hk; interval_cases h <;> decide +kernel

/-! ### Theorem 409 -/

/-- Two tuples with the same multiset of values differ by a permutation of the indices. -/
lemma exists_perm_of_multiset_map_eq {s : ℕ} (a b : Fin s → ℕ)
    (h : Finset.univ.val.map a = Finset.univ.val.map b) :
    ∃ σ : Equiv.Perm (Fin s), a = b ∘ σ := by
  have hp : ∀ c : Fin s → ℕ, (List.ofFn (c ∘ Tuple.sort c)).Perm (List.ofFn c) :=
    fun c => (Tuple.sort c).ofFn_comp_perm c
  have hs : ∀ c : Fin s → ℕ, (List.ofFn (c ∘ Tuple.sort c)).Pairwise (· ≤ ·) := fun c => by
    rw [List.pairwise_ofFn]
    intro i j hij
    exact Tuple.monotone_sort c hij.le
  have hab : (List.ofFn a).Perm (List.ofFn b) := by
    rw [Fin.univ_val_map, Fin.univ_val_map] at h
    exact Multiset.coe_eq_coe.mp h
  have h1 : (List.ofFn (a ∘ Tuple.sort a)).Perm (List.ofFn (b ∘ Tuple.sort b)) :=
    ((hp a).trans hab).trans (hp b).symm
  have h2 := h1.eq_of_pairwise (fun x y _ _ => le_antisymm) (hs a) (hs b)
  have h3 := List.ofFn_injective h2
  refine ⟨(Tuple.sort a).symm.trans (Tuple.sort b), ?_⟩
  funext i
  have := congrFun h3 ((Tuple.sort a).symm i)
  simpa using this

lemma two_mul_sum_range_succ (k : ℕ) : 2 * ∑ i ∈ range k, (i + 1) = k * (k + 1) := by
  induction k with
  | zero => simp
  | succ m ih => rw [sum_range_succ, mul_add, ih]; ring

/-- **Theorem 409** (Hardy–Wright), the construction: for every `k` and `j` there is a
non-trivial solution of (21.9.3) with `s = k (k + 1) / 2 + 1`.  The proof is the pigeonhole
argument of the book: among the `nˢ` tuples in `[1, n]ˢ`, with `n > s! sᵏ j`, at least `s! j`
have the same vector `(S₁, …, S_k)`, and at most `s!` of them are permutations of one another. -/
@[kb "hardywright2008" "Thm 409, p. 455"]
theorem exists_isNontrivialPTSolution (k j : ℕ) :
    ∃ a : Fin j → Fin (k * (k + 1) / 2 + 1) → ℤ,
      IsNontrivialPTSolution k j (k * (k + 1) / 2 + 1) a := by
  have hsum : ∑ h : Fin k, (h.1 + 1) = k * (k + 1) / 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => i + 1) k, ← two_mul_sum_range_succ,
      Nat.mul_div_cancel_left _ (by norm_num)]
  generalize hs : k * (k + 1) / 2 + 1 = s at *
  have hs1 : 1 ≤ s := by omega
  have hsum' : ∑ h : Fin k, (h.1 + 1) = s - 1 := by omega
  obtain ⟨n, hn⟩ : ∃ n, n = Nat.factorial s * s ^ k * j + 1 := ⟨_, rfl⟩
  have hnpos : 0 < n := by omega
  set X : Finset (Fin s → ℕ) := Fintype.piFinset fun _ => Icc 1 n with hX
  set Y : Finset (Fin k → ℕ) := Fintype.piFinset fun h => Icc s (s * n ^ (h.1 + 1)) with hY
  set F : (Fin s → ℕ) → (Fin k → ℕ) := fun a h => ∑ i, a i ^ (h.1 + 1) with hF
  have hmaps : ∀ a ∈ X, F a ∈ Y := by
    intro a ha
    rw [hX, Fintype.mem_piFinset] at ha
    rw [hY, Fintype.mem_piFinset]
    intro h
    rw [Finset.mem_Icc]
    constructor
    · calc s = ∑ _i : Fin s, 1 := by simp
        _ ≤ ∑ i, a i ^ (h.1 + 1) :=
          Finset.sum_le_sum fun i _ => Nat.one_le_pow _ _ (Finset.mem_Icc.mp (ha i)).1
    · calc ∑ i, a i ^ (h.1 + 1) ≤ ∑ _i : Fin s, n ^ (h.1 + 1) :=
          Finset.sum_le_sum fun i _ => Nat.pow_le_pow_left (Finset.mem_Icc.mp (ha i)).2 _
        _ = s * n ^ (h.1 + 1) := by simp
  have hcardX : X.card = n ^ s := by simp [hX]
  have hcardY : Y.card ≤ s ^ k * n ^ (s - 1) := by
    rw [hY, Fintype.card_piFinset]
    simp only [Nat.card_Icc]
    calc ∏ h : Fin k, (s * n ^ (h.1 + 1) + 1 - s) ≤ ∏ h : Fin k, (s * n ^ (h.1 + 1)) :=
          by gcongr with h _; omega
      _ = s ^ k * n ^ (s - 1) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            Finset.prod_pow_eq_pow_sum, hsum']
  have hlt : Y.card * (Nat.factorial s * j) < X.card := by
    have hpow : 0 < n ^ (s - 1) := Nat.pow_pos hnpos
    have : n ^ s = n * n ^ (s - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [hcardX, this]
    calc Y.card * (Nat.factorial s * j) ≤ s ^ k * n ^ (s - 1) * (Nat.factorial s * j) :=
          Nat.mul_le_mul_right _ hcardY
      _ = (Nat.factorial s * s ^ k * j) * n ^ (s - 1) := by ring
      _ < n * n ^ (s - 1) := Nat.mul_lt_mul_of_pos_right (by omega) hpow
  obtain ⟨y, -, hy⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hlt
  set T : Finset (Fin s → ℕ) := {x ∈ X | F x = y} with hT
  set g : (Fin s → ℕ) → Multiset ℕ := fun a => Finset.univ.val.map a with hg
  have hfib : ∀ m ∈ T.image g, #{a ∈ T | g a = m} ≤ Nat.factorial s := by
    intro m hm
    obtain ⟨a0, -, ha0⟩ := Finset.mem_image.mp hm
    calc #{a ∈ T | g a = m}
        ≤ #((Finset.univ : Finset (Equiv.Perm (Fin s))).image
            fun σ : Equiv.Perm (Fin s) => a0 ∘ (σ : Fin s → Fin s)) := by
          apply Finset.card_le_card
          intro a ha
          rw [Finset.mem_filter] at ha
          obtain ⟨σ, hσ⟩ := exists_perm_of_multiset_map_eq a a0 (ha.2.trans ha0.symm)
          exact Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, hσ.symm⟩
      _ ≤ Fintype.card (Equiv.Perm (Fin s)) :=
          Finset.card_image_le.trans (le_of_eq Finset.card_univ)
      _ = Nat.factorial s := by rw [Fintype.card_perm, Fintype.card_fin]
  have hcard := Finset.card_le_mul_card_image T (Nat.factorial s) hfib
  have hjlt : j ≤ (T.image g).card := by
    by_contra hc
    have : Nat.factorial s * (T.image g).card < Nat.factorial s * j :=
      Nat.mul_lt_mul_of_pos_left (by omega) (Nat.factorial_pos s)
    omega
  obtain ⟨U, hUsub, hUcard⟩ := Finset.exists_subset_card_eq hjlt
  let ε : U ≃ Fin j := Finset.equivFinOfCardEq hUcard
  have hex : ∀ u : Fin j, ∃ x ∈ T, g x = ((ε.symm u : U) : Multiset ℕ) :=
    fun u => Finset.mem_image.mp (hUsub (ε.symm u).2)
  choose x hxT hxg using hex
  refine ⟨fun u i => (x u i : ℤ), ?_, ?_⟩
  · intro h h1 hk u v
    have hu := (Finset.mem_filter.mp (hxT u)).2
    have hv := (Finset.mem_filter.mp (hxT v)).2
    have := congrFun (hu.trans hv.symm) ⟨h - 1, by omega⟩
    simp only [hF, Nat.sub_add_cancel h1] at this
    show ∑ i, ((x u i : ℤ)) ^ h = ∑ i, ((x v i : ℤ)) ^ h
    exact_mod_cast this
  · intro u v huv e
    apply huv
    have h1 : ∀ w, (Finset.univ.val.map fun i => (x w i : ℤ)) =
        (g (x w)).map (Nat.cast : ℕ → ℤ) := by
      intro w; rw [hg, Multiset.map_map]; rfl
    have h3 : g (x u) = g (x v) :=
      Multiset.map_injective Nat.cast_injective (by rw [← h1, ← h1]; exact e)
    have h4 : ((ε.symm u : U) : Multiset ℕ) = ε.symm v := by
      rw [← hxg u, ← hxg v]; exact h3
    exact ε.symm.injective (Subtype.ext h4)

/-- **Theorem 409** (Hardy–Wright): `P(k, j) ≤ k (k + 1) / 2 + 1`. -/
@[kb "hardywright2008" "Thm 409, p. 455"]
theorem prouhetTarryNumber_le (k j : ℕ) : prouhetTarryNumber k j ≤ k * (k + 1) / 2 + 1 :=
  Nat.sInf_le (exists_isNontrivialPTSolution k j)

/-- **Theorems 408 and 409** (Hardy–Wright), together and unconditionally (Theorem 409 provides the
non-trivial solutions): `k + 1 ≤ P(k, 2) ≤ P(k, j) ≤ ½k(k + 1) + 1` for `j ≥ 2`. -/
@[kb "hardywright2008" "Thm 408, p. 455"]
theorem prouhetTarryNumber_bounds {k j : ℕ} (hj : 2 ≤ j) :
    k + 1 ≤ prouhetTarryNumber k 2 ∧ prouhetTarryNumber k 2 ≤ prouhetTarryNumber k j ∧
      prouhetTarryNumber k j ≤ k * (k + 1) / 2 + 1 :=
  ⟨(succ_le_prouhetTarryNumber_two_le hj ⟨_, exists_isNontrivialPTSolution k j⟩).1,
    (succ_le_prouhetTarryNumber_two_le hj ⟨_, exists_isNontrivialPTSolution k j⟩).2,
    prouhetTarryNumber_le k j⟩

/-! ### Theorem 410 -/

/-- If `a` is a non-trivial solution of (21.9.3) for `j ≥ 2` sets of `k + 1` integers, then
`P(k, j) = k + 1`. -/
lemma prouhetTarryNumber_eq_succ_of {k j : ℕ} (hj : 2 ≤ j) (a : Fin j → Fin (k + 1) → ℤ)
    (h : IsNontrivialPTSolution k j (k + 1) a) : prouhetTarryNumber k j = k + 1 :=
  le_antisymm (Nat.sInf_le ⟨a, h⟩) (succ_le_prouhetTarryNumber hj ⟨_, a, h⟩)

lemma mem_eight_aux {u v : ℤ} {a b : ℕ} (h1 : max u.natAbs v.natAbs = a)
    (h2 : min u.natAbs v.natAbs = b) :
    (u = a ∧ v = b) ∨ (u = -a ∧ v = b) ∨ (u = a ∧ v = -b) ∨ (u = -a ∧ v = -b) ∨
      (u = b ∧ v = a) ∨ (u = -b ∧ v = a) ∨ (u = b ∧ v = -a) ∨ (u = -b ∧ v = -a) := by
  have hh : (u.natAbs = a ∧ v.natAbs = b) ∨ (u.natAbs = b ∧ v.natAbs = a) := by omega
  rcases Int.natAbs_eq u with hu | hu <;> rcases Int.natAbs_eq v with hv | hv <;>
    rcases hh with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> rw [h3] at hu <;> rw [h4] at hv <;> simp [hu, hv]

/-- For every `j` there is a power of `5` with at least `j` representations as a sum of two
squares `c² + d²` with `c ≥ d ≥ 0`, all with distinct pairs `(c, d)`.  (The book uses its Theorem
337 for this; here the count `r(5ᵐ) = 4 (m + 1)` is used.) -/
lemma exists_sq_add_sq_reps (j : ℕ) :
    ∃ n : ℕ, ∃ c d : Fin j → ℕ, (∀ u, c u ^ 2 + d u ^ 2 = n) ∧ (∀ u, d u ≤ c u) ∧
      Function.Injective fun u => (c u, d u) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = 5 ^ (2 * j) := ⟨_, rfl⟩
  have hn1 : (1 : ℤ) ≤ n := by rw [hn]; exact_mod_cast Nat.one_le_pow _ _ (by norm_num)
  set R : Set (ℤ × ℤ) := {x | x.1 ^ 2 + x.2 ^ 2 = n} with hR
  have hbd : ∀ t : ℤ, t ^ 2 ≤ n → -(n : ℤ) ≤ t ∧ t ≤ n := by
    intro t ht
    constructor <;> nlinarith
  have hfin : R.Finite := by
    refine (Set.finite_Icc ((-(n : ℤ)), -(n : ℤ)) ((n : ℤ), (n : ℤ))).subset ?_
    intro x hx
    simp only [hR, Set.mem_ofPred_eq] at hx
    have h1 := hbd x.1 (by nlinarith [sq_nonneg x.2])
    have h2 := hbd x.2 (by nlinarith [sq_nonneg x.1])
    exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩
  set T := hfin.toFinset with hT
  have hcard : T.card = 4 * (2 * j + 1) := by
    rw [hT, ← Set.ncard_eq_toFinset_card R hfin]
    have h := sumTwoSquaresCount_eq (n := 5 ^ (2 * j)) (by positivity)
    rw [chi4DivisorSum_prime_pow_eq (by norm_num : Nat.Prime 5)] at h
    simp only [chi4LocalFactor] at h
    have h5 : (5 : ℕ) % 4 = 1 := by norm_num
    simp only [ite_true] at h
    have : sumTwoSquaresCount (5 ^ (2 * j)) = 4 * (2 * j + 1) := by omega
    rw [← this, sumTwoSquaresCount, hR, hn]
  let φ : ℤ × ℤ → ℕ × ℕ := fun p => (max p.1.natAbs p.2.natAbs, min p.1.natAbs p.2.natAbs)
  have hfib : ∀ a ∈ T.image φ, #{x ∈ T | φ x = a} ≤ 8 := by
    intro a _
    let l : List (ℤ × ℤ) := [((a.1 : ℤ), (a.2 : ℤ)), (-(a.1 : ℤ), (a.2 : ℤ)),
      ((a.1 : ℤ), -(a.2 : ℤ)), (-(a.1 : ℤ), -(a.2 : ℤ)), ((a.2 : ℤ), (a.1 : ℤ)),
      (-(a.2 : ℤ), (a.1 : ℤ)), ((a.2 : ℤ), -(a.1 : ℤ)), (-(a.2 : ℤ), -(a.1 : ℤ))]
    calc #{x ∈ T | φ x = a} ≤ l.toFinset.card := by
          apply Finset.card_le_card
          intro x hx
          rw [Finset.mem_filter] at hx
          have := hx.2
          simp only [φ, Prod.ext_iff] at this
          rcases mem_eight_aux this.1 this.2 with ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩ |
              ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩ <;>
            simp [l, Prod.ext_iff, hu, hv]
      _ ≤ l.length := List.toFinset_card_le l
      _ = 8 := rfl
  have h8 := Finset.card_le_mul_card_image T 8 hfib
  have hS : ∀ a ∈ T.image φ, a.2 ≤ a.1 ∧ a.1 ^ 2 + a.2 ^ 2 = n := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    have hx' : x.1 ^ 2 + x.2 ^ 2 = n := by
      have := (hfin.mem_toFinset).mp hx
      simpa [hR] using this
    refine ⟨by simp only [φ]; omega, ?_⟩
    have e1 : ((x.1.natAbs : ℕ) : ℤ) ^ 2 = x.1 ^ 2 := Int.natAbs_sq x.1
    have e2 : ((x.2.natAbs : ℕ) : ℤ) ^ 2 = x.2 ^ 2 := Int.natAbs_sq x.2
    simp only [φ]
    rcases le_total x.1.natAbs x.2.natAbs with h | h
    · rw [max_eq_right h, min_eq_left h]
      have : ((x.2.natAbs ^ 2 + x.1.natAbs ^ 2 : ℕ) : ℤ) = n := by
        rw [Nat.cast_add, Nat.cast_pow, Nat.cast_pow, e1, e2]; linarith
      exact_mod_cast this
    · rw [max_eq_left h, min_eq_right h]
      have : ((x.1.natAbs ^ 2 + x.2.natAbs ^ 2 : ℕ) : ℤ) = n := by
        rw [Nat.cast_add, Nat.cast_pow, Nat.cast_pow, e1, e2]; linarith
      exact_mod_cast this
  have hjle : j ≤ (T.image φ).card := by omega
  let S := T.image φ
  let f : Fin j → S := fun u => S.equivFin.symm (Fin.castLE hjle u)
  have hf : Function.Injective f := fun u v h =>
    Fin.castLE_injective hjle (S.equivFin.symm.injective h)
  refine ⟨n, fun u => (f u).1.1, fun u => (f u).1.2, fun u => (hS _ (f u).2).2,
    fun u => (hS _ (f u).2).1, fun u v h => hf (Subtype.ext (Prod.ext ?_ ?_))⟩
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

/-- Theorem 410 for `k = 3`: for every `j` there is a non-trivial solution of (21.9.3) with
`s = 4`, namely `(c_u, d_u, -c_u, -d_u)` with `c_u² + d_u²` independent of `u`. -/
lemma exists_isNontrivialPTSolution_three (j : ℕ) :
    ∃ a : Fin j → Fin 4 → ℤ, IsNontrivialPTSolution 3 j 4 a := by
  obtain ⟨n, c, d, hcd, hdc, hinj⟩ := exists_sq_add_sq_reps j
  refine ⟨fun u => ![(c u : ℤ), d u, -(c u), -(d u)], ?_, ?_⟩
  · intro h h1 hk u v
    have key : ∀ w : Fin j, ∑ i, (![(c w : ℤ), d w, -(c w), -(d w)] i) ^ h =
        if h = 2 then 2 * n else 0 := by
      intro w
      have hw : (c w : ℤ) ^ 2 + (d w) ^ 2 = n := by exact_mod_cast hcd w
      interval_cases h
      · simp [Fin.sum_univ_four]
      · simp [Fin.sum_univ_four]; linear_combination 2 * hw
      · simp [Fin.sum_univ_four]; ring
    rw [key u, key v]
  · intro u v huv e
    apply huv
    have hs : ∀ w : Fin j, ∑ i, |(![(c w : ℤ), d w, -(c w), -(d w)] i)| =
        2 * ((c w : ℤ) + d w) := by
      intro w
      simp [Fin.sum_univ_four]
      ring
    have hm : ∀ w : Fin j, ∑ i, |(![(c w : ℤ), d w, -(c w), -(d w)] i)| =
        ((Finset.univ.val.map (![(c w : ℤ), d w, -(c w), -(d w)])).map abs).sum := by
      intro w
      rw [Multiset.map_map]; rfl
    have e' := congrArg (fun m : Multiset ℤ => (m.map abs).sum) e
    simp only at e'
    rw [← hm u, ← hm v, hs u, hs v] at e'
    have hu := hcd u
    have hv := hcd v
    have hu' := hdc u
    have hv' := hdc v
    have hsum : c u + d u = c v + d v := by omega
    have hsq : (c u - d u : ℤ) ^ 2 = (c v - d v : ℤ) ^ 2 := by
      have : ((c u : ℤ)) ^ 2 + (d u) ^ 2 = (c v) ^ 2 + (d v) ^ 2 := by exact_mod_cast hu.trans hv.symm
      have hs' : (c u : ℤ) + d u = c v + d v := by exact_mod_cast hsum
      nlinarith
    have hdiff : (c u : ℤ) - d u = c v - d v := by
      have hle1 : (d u : ℤ) ≤ c u := by exact_mod_cast hu'
      have hle2 : (d v : ℤ) ≤ c v := by exact_mod_cast hv'
      have h1 : (0 : ℤ) ≤ c u - d u := by linarith
      have h2 : (0 : ℤ) ≤ c v - d v := by linarith
      exact (sq_eq_sq₀ h1 h2).mp hsq
    apply hinj
    have : c u = c v := by omega
    have : d u = d v := by omega
    simp [*]

/-- Theorem 410 for `k = 3`. -/
@[kb "hardywright2008" "Thm 410, p. 456"]
theorem prouhetTarryNumber_three_eq {j : ℕ} (hj : 2 ≤ j) : prouhetTarryNumber 3 j = 4 := by
  obtain ⟨a, ha⟩ := exists_isNontrivialPTSolution_three j
  exact prouhetTarryNumber_eq_succ_of hj a ha

/-- If the sets `a u` (`u < j`) are such that every element of `a u` is divisible by `7 ^ (j - 1 - u)`
but one fixed element `a u i₀` is not divisible by `7 ^ (j - u)`, then no two of the sets are
permutations of one another. -/
lemma multiset_map_ne_of_seven_pow {j s : ℕ} (a : Fin j → Fin s → ℤ) (i0 : Fin s)
    (hdiv : ∀ (u : Fin j) i, (7 : ℤ) ^ (j - 1 - (u : ℕ)) ∣ a u i)
    (hnd : ∀ u : Fin j, ¬ (7 : ℤ) ^ (j - 1 - (u : ℕ) + 1) ∣ a u i0) :
    ∀ u v, u ≠ v → Finset.univ.val.map (a u) ≠ Finset.univ.val.map (a v) := by
  have key : ∀ u v : Fin j, u < v → Finset.univ.val.map (a u) ≠ Finset.univ.val.map (a v) := by
    intro u v huv e
    have hmem : a v i0 ∈ Finset.univ.val.map (a u) := by
      rw [e]; exact Multiset.mem_map.mpr ⟨i0, Finset.mem_univ_val _, rfl⟩
    obtain ⟨i, -, hi⟩ := Multiset.mem_map.mp hmem
    apply hnd v
    have h1 : (7 : ℤ) ^ (j - 1 - (v : ℕ) + 1) ∣ (7 : ℤ) ^ (j - 1 - (u : ℕ)) :=
      pow_dvd_pow _ (by have := v.2; have : (u : ℕ) < v := huv; omega)
    refine h1.trans ?_
    rw [← hi]; exact hdiv u i
  intro u v huv
  rcases lt_or_gt_of_ne huv with h | h
  · exact key u v h
  · exact (key v u h).symm

/-- The coefficients of `π ^ (2 (n + 1)) = A - B ρ`, where `π = 3 + ρ`, `ρ` a primitive cube
root of unity (so `ρ² = -1 - ρ` and `π² = 8 + 5 ρ`); the pair is `(A, B)`, and multiplication
by `π²` is `(A, B) ↦ (8 A + 5 B, -5 A + 3 B)`. -/
def ptSeq : ℕ → ℤ × ℤ
  | 0 => (8, -5)
  | n + 1 => (8 * (ptSeq n).1 + 5 * (ptSeq n).2, -5 * (ptSeq n).1 + 3 * (ptSeq n).2)

/-- The norm `A² + A B + B²` of `A - B ρ` is `7 ^ (2 (n + 1))`. -/
lemma ptSeq_norm (n : ℕ) :
    (ptSeq n).1 ^ 2 + (ptSeq n).1 * (ptSeq n).2 + (ptSeq n).2 ^ 2 = 49 ^ (n + 1) := by
  induction n with
  | zero => norm_num [ptSeq]
  | succ n ih =>
    have h49 : (49 : ℤ) ^ (n + 1 + 1) = 49 * 49 ^ (n + 1) := by ring
    rw [h49]
    simp only [ptSeq]
    linear_combination 49 * ih

/-- Replacement for the book's argument with primes of `ℚ(ρ)`: modulo `7`, `ρ ↦ 4` sends `π` to
`0` and `ρ ↦ 2` sends `π` to `5`, so `A - 4 B` is always divisible by `7` while `A - 2 B` never is
(`A - 2 B ≡ 4 ^ (n + 1)`). -/
lemma ptSeq_mod (n : ℕ) :
    (7 : ℤ) ∣ (ptSeq n).1 - 4 * (ptSeq n).2 ∧ ¬ (7 : ℤ) ∣ (ptSeq n).1 - 2 * (ptSeq n).2 := by
  induction n with
  | zero => simp only [ptSeq]; omega
  | succ n ih =>
    simp only [ptSeq]
    obtain ⟨h1, h2⟩ := ih
    omega

/-- `7` divides neither `A_u` nor `B_u`. -/
lemma ptSeq_not_dvd (n : ℕ) : ¬ (7 : ℤ) ∣ (ptSeq n).1 ∧ ¬ (7 : ℤ) ∣ (ptSeq n).2 := by
  obtain ⟨h1, h2⟩ := ptSeq_mod n
  constructor <;> omega

/-- The integers `c_u = 7 ^ (j - u) A_u`, `d_u = 7 ^ (j - u) B_u` (indices shifted by one) of the
book: `c² + c d + d² = 7 ^ (2 j)`, both divisible by `7 ^ (j - 1 - u)` and `c_u` not divisible by
`7 ^ (j - u)`. -/
lemma exists_seven_triples (j : ℕ) : ∃ x y : Fin j → ℤ,
    (∀ u, x u ^ 2 + x u * y u + y u ^ 2 = 7 ^ (2 * j)) ∧
    (∀ u : Fin j, (7 : ℤ) ^ (j - 1 - (u : ℕ)) ∣ x u) ∧
    (∀ u : Fin j, (7 : ℤ) ^ (j - 1 - (u : ℕ)) ∣ y u) ∧
    ∀ u : Fin j, ¬ (7 : ℤ) ^ (j - 1 - (u : ℕ) + 1) ∣ x u := by
  refine ⟨fun u => 7 ^ (j - 1 - (u : ℕ)) * (ptSeq u).1,
    fun u => 7 ^ (j - 1 - (u : ℕ)) * (ptSeq u).2, ?_, fun u => dvd_mul_right _ _,
    fun u => dvd_mul_right _ _, ?_⟩
  · intro u
    obtain ⟨e, he⟩ : ∃ e, j = e + u + 1 := ⟨j - 1 - u, by have := u.2; omega⟩
    have h1 : j - 1 - (u : ℕ) = e := by omega
    have h2 : (7 : ℤ) ^ (2 * j) = 7 ^ (2 * e) * 49 ^ ((u : ℕ) + 1) := by
      rw [show (49 : ℤ) = 7 ^ 2 by norm_num, ← pow_mul, ← pow_add]
      congr 1; omega
    have := ptSeq_norm u
    simp only [h1]
    rw [h2, ← this]; ring
  · intro u h
    dsimp only at h
    rw [pow_succ] at h
    have := (mul_dvd_mul_iff_left (pow_ne_zero _ (by norm_num : (7 : ℤ) ≠ 0))).mp h
    exact (ptSeq_not_dvd u).1 this

/-- Theorem 410 for `k = 2`: a non-trivial solution with `s = 3` for every `j`. -/
lemma exists_isNontrivialPTSolution_two (j : ℕ) :
    ∃ a : Fin j → Fin 3 → ℤ, IsNontrivialPTSolution 2 j 3 a := by
  obtain ⟨x, y, hN, hx, hy, hnd⟩ := exists_seven_triples j
  refine ⟨fun u => ![x u, y u, -(x u + y u)], ?_, ?_⟩
  · intro h h1 hk u v
    have key : ∀ w, ∑ i, (![x w, y w, -(x w + y w)] i) ^ h =
        if h = 2 then 2 * 7 ^ (2 * j) else 0 := by
      intro w
      interval_cases h
      · simp [Fin.sum_univ_three]
      · simp [Fin.sum_univ_three]; linear_combination 2 * hN w
    rw [key u, key v]
  · refine multiset_map_ne_of_seven_pow _ 0 ?_ hnd
    intro u i
    fin_cases i
    · exact hx u
    · exact hy u
    · exact dvd_neg.mpr (dvd_add (hx u) (hy u))

/-- Theorem 410 for `k = 5`: a non-trivial solution with `s = 6` for every `j`. -/
lemma exists_isNontrivialPTSolution_five (j : ℕ) :
    ∃ a : Fin j → Fin 6 → ℤ, IsNontrivialPTSolution 5 j 6 a := by
  obtain ⟨x, y, hN, hx, hy, hnd⟩ := exists_seven_triples j
  refine ⟨fun u => ![x u, y u, -(x u + y u), -x u, -y u, x u + y u], ?_, ?_⟩
  · intro h h1 hk u v
    have key : ∀ w, ∑ i, (![x w, y w, -(x w + y w), -x w, -y w, x w + y w] i) ^ h =
        if h = 2 then 4 * 7 ^ (2 * j) else if h = 4 then 4 * 7 ^ (4 * j) else 0 := by
      intro w
      have h4 : (7 : ℤ) ^ (4 * j) = (7 ^ (2 * j)) ^ 2 := by rw [← pow_mul]; ring_nf
      interval_cases h
      · simp [Fin.sum_univ_six]; ring
      · simp [Fin.sum_univ_six]; linear_combination 4 * hN w
      · simp [Fin.sum_univ_six]; ring
      · simp [Fin.sum_univ_six]
        rw [h4, ← hN w]; ring
      · simp [Fin.sum_univ_six]; ring
    rw [key u, key v]
  · refine multiset_map_ne_of_seven_pow _ 0 ?_ hnd
    intro u i
    fin_cases i
    · exact hx u
    · exact hy u
    · exact dvd_neg.mpr (dvd_add (hx u) (hy u))
    · exact dvd_neg.mpr (hx u)
    · exact dvd_neg.mpr (hy u)
    · exact dvd_add (hx u) (hy u)

/-- **Theorem 410** (Hardy–Wright) for `k = 2`: `P(2, j) = 3`. -/
@[kb "hardywright2008" "Thm 410, p. 456"]
theorem prouhetTarryNumber_two_eq_three {j : ℕ} (hj : 2 ≤ j) : prouhetTarryNumber 2 j = 3 := by
  obtain ⟨a, ha⟩ := exists_isNontrivialPTSolution_two j
  exact prouhetTarryNumber_eq_succ_of hj a ha

/-- **Theorem 410** (Hardy–Wright) for `k = 5`: `P(5, j) = 6`. -/
@[kb "hardywright2008" "Thm 410, p. 456"]
theorem prouhetTarryNumber_five_eq {j : ℕ} (hj : 2 ≤ j) : prouhetTarryNumber 5 j = 6 := by
  obtain ⟨a, ha⟩ := exists_isNontrivialPTSolution_five j
  exact prouhetTarryNumber_eq_succ_of hj a ha

/-- **Theorem 410** (Hardy–Wright): `P(k, j) = k + 1` for `k = 2, 3, 5` and all `j ≥ 2`. -/
@[kb "hardywright2008" "Thm 410, p. 456"]
theorem prouhetTarryNumber_eq_succ {k j : ℕ} (hk : k = 2 ∨ k = 3 ∨ k = 5) (hj : 2 ≤ j) :
    prouhetTarryNumber k j = k + 1 := by
  rcases hk with rfl | rfl | rfl
  · exact prouhetTarryNumber_two_eq_three hj
  · exact prouhetTarryNumber_three_eq hj
  · exact prouhetTarryNumber_five_eq hj

end NTKB.HardyWright
