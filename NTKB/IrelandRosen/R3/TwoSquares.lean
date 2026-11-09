/-
Ireland–Rosen, Chapter 17, §6: sums of two squares.
-/
import NTKB.Elementary.HardyWright.ArithmeticFunctions.SumTwoSquares

/-!
# Sums of two squares (Proposition 17.6.1)

Ireland–Rosen, Proposition 17.6.1: the number of `(x, y)` with `x > 0`, `y ≥ 0` and
`x² + y² = n` is `∑_{d ∣ n} χ(d)`, `χ` the nontrivial character modulo `4`; and Corollary 2: for odd
`m`, the number of `(x, y)` with `x, y > 0` and `x² + y² = 2m` is `∑_{d ∣ m} χ(d)`.

The book obtains 17.6.1 from the zeta function of `ℤ[i]`. We deduce it from Hardy–Wright's
Theorem 278 of Hardy–Wright in this library (`NTKB.HardyWright.sumTwoSquaresCount_eq`, `r(n) = 4 ∑_{d ∣ n} χ(d)`) by
splitting the Gaussian integers of norm `n` into the four quarter planes `iᵏ Q`,
`Q = {x + iy : x > 0, y ≥ 0}` (each nonzero Gaussian integer has a unique associate in `Q`, as in
the book).
-/

namespace NTKB.IrelandRosen.TwoSquares

open NTKB.HardyWright Zsqrtd

/-- The solutions `(x, y)`, `x > 0`, `y ≥ 0`, of `x² + y² = n`. -/
def quarterSet (n : ℕ) : Set (ℤ × ℤ) := {v | 0 < v.1 ∧ 0 ≤ v.2 ∧ v.1 ^ 2 + v.2 ^ 2 = n}

lemma finite_sols (n : ℕ) : {v : ℤ × ℤ | v.1 ^ 2 + v.2 ^ 2 = n}.Finite := by
  refine ((Set.finite_Icc (-(n : ℤ)) n).prod (Set.finite_Icc (-(n : ℤ)) n)).subset ?_
  rintro ⟨x, y⟩ h
  simp only [Set.mem_setOf_eq] at h
  simp only [Set.mem_prod, Set.mem_Icc]
  refine ⟨⟨by nlinarith [sq_nonneg y, sq_nonneg (x + 1)], by nlinarith [sq_nonneg y, sq_nonneg (x - 1)]⟩,
    ⟨by nlinarith [sq_nonneg x, sq_nonneg (y + 1)], by nlinarith [sq_nonneg x, sq_nonneg (y - 1)]⟩⟩

/-- The four rotations of the quarter plane. -/
def rot : ℕ → ℤ × ℤ → ℤ × ℤ
  | 0, v => v
  | 1, v => (-v.2, v.1)
  | 2, v => (-v.1, -v.2)
  | _, v => (v.2, -v.1)

lemma rot_injective (k : ℕ) : Function.Injective (rot k) := by
  intro v w h
  match k with
  | 0 => exact h
  | 1 => simp only [rot, Prod.mk.injEq, neg_inj] at h; ext <;> omega
  | 2 => simp only [rot, Prod.mk.injEq, neg_inj] at h; ext <;> omega
  | k + 3 => simp only [rot, Prod.mk.injEq, neg_inj] at h; ext <;> omega

/-- For `n > 0`, `r(n) = 4 · #{x > 0, y ≥ 0}`. -/
lemma sumTwoSquaresCount_eq_four_mul (n : ℕ) (hn : 0 < n) :
    sumTwoSquaresCount n = 4 * (quarterSet n).ncard := by
  have hfin := finite_sols n
  set S := {v : ℤ × ℤ | v.1 ^ 2 + v.2 ^ 2 = n}
  have hQ : ∀ k : ℕ, rot k '' quarterSet n ⊆ S := by
    rintro k _ ⟨v, ⟨h1, h2, h3⟩, rfl⟩
    match k with
    | 0 => exact h3
    | 1 => simp only [rot, S, Set.mem_setOf_eq]; linear_combination h3
    | 2 => simp only [rot, S, Set.mem_setOf_eq]; linear_combination h3
    | k + 3 => simp only [rot, S, Set.mem_setOf_eq]; linear_combination h3
  -- the four images partition `S`
  have hS : S = (rot 0 '' quarterSet n ∪ rot 1 '' quarterSet n) ∪
      (rot 2 '' quarterSet n ∪ rot 3 '' quarterSet n) := by
    ext ⟨x, y⟩
    constructor
    · intro h
      simp only [S, Set.mem_setOf_eq] at h
      have h0 : ¬ (x = 0 ∧ y = 0) := by
        rintro ⟨rfl, rfl⟩; simp at h; omega
      simp only [Set.mem_union, Set.mem_image, quarterSet, Set.mem_setOf_eq, rot, Prod.exists,
        Prod.mk.injEq]
      rcases lt_trichotomy x 0 with hx | hx | hx <;> rcases lt_trichotomy y 0 with hy | hy | hy
      · exact Or.inr (Or.inl ⟨-x, -y, ⟨by omega, by omega, by linear_combination h⟩, by ring, by ring⟩)
      · exact Or.inr (Or.inl ⟨-x, -y, ⟨by omega, by omega, by linear_combination h⟩, by ring, by ring⟩)
      · exact Or.inl (Or.inr ⟨y, -x, ⟨by omega, by omega, by linear_combination h⟩, by ring, rfl⟩)
      · exact Or.inr (Or.inr ⟨-y, x, ⟨by omega, by omega, by linear_combination h⟩, rfl, by ring⟩)
      · exact absurd ⟨hx, hy⟩ h0
      · exact Or.inl (Or.inr ⟨y, -x, ⟨by omega, by omega, by linear_combination h⟩, by ring, rfl⟩)
      · exact Or.inr (Or.inr ⟨-y, x, ⟨by omega, by omega, by linear_combination h⟩, rfl, by ring⟩)
      · exact Or.inl (Or.inl ⟨x, y, ⟨hx, by omega, h⟩, rfl, rfl⟩)
      · exact Or.inl (Or.inl ⟨x, y, ⟨hx, by omega, h⟩, rfl, rfl⟩)
    · intro h
      rcases h with (h | h) | (h | h)
      · exact hQ 0 h
      · exact hQ 1 h
      · exact hQ 2 h
      · exact hQ 3 h
  have hqf : (quarterSet n).Finite := hfin.subset fun v h => h.2.2
  have hc : ∀ k : ℕ, (rot k '' quarterSet n).ncard = (quarterSet n).ncard :=
    fun k => Set.ncard_image_of_injective _ (rot_injective k)
  have hfk : ∀ k : ℕ, (rot k '' quarterSet n).Finite := fun k => hqf.image _
  have hdisj : ∀ i j : ℕ, i < 4 → j < 4 → i ≠ j →
      Disjoint (rot i '' quarterSet n) (rot j '' quarterSet n) := by
    intro i j hi hj hij
    rw [Set.disjoint_left]
    rintro _ ⟨v, ⟨h1, h2, -⟩, rfl⟩ ⟨w, ⟨h1', h2', -⟩, hw⟩
    interval_cases i <;> interval_cases j <;> simp [rot, Prod.ext_iff] at hw <;>
      first | exact hij rfl | omega
  rw [sumTwoSquaresCount, show {x : ℤ × ℤ | x.1 ^ 2 + x.2 ^ 2 = (n : ℤ)} = S from rfl, hS,
    Set.ncard_union_eq _ ((hfk 0).union (hfk 1)) ((hfk 2).union (hfk 3)),
    Set.ncard_union_eq (hdisj 0 1 (by decide) (by decide) (by decide)) (hfk 0) (hfk 1),
    Set.ncard_union_eq (hdisj 2 3 (by decide) (by decide) (by decide)) (hfk 2) (hfk 3), hc, hc, hc, hc]
  · ring
  · rw [Set.disjoint_union_left, Set.disjoint_union_right, Set.disjoint_union_right]
    exact ⟨⟨hdisj 0 2 (by decide) (by decide) (by decide), hdisj 0 3 (by decide) (by decide) (by decide)⟩,
      ⟨hdisj 1 2 (by decide) (by decide) (by decide), hdisj 1 3 (by decide) (by decide) (by decide)⟩⟩

/-- **Proposition 17.6.1.** The number of integral solutions `(x, y)`, `x > 0`, `y ≥ 0`, of
`x² + y² = n` (`n ≥ 1`) is `∑_{d ∣ n} χ(d)`. -/
@[kb "irelandrosen1990" "Prop 17.6.1, p. 290"]
theorem ncard_quarterSet {n : ℕ} (hn : 0 < n) :
    ((quarterSet n).ncard : ℤ) = ∑ d ∈ n.divisors, chi4 d := by
  have h := sumTwoSquaresCount_eq hn
  rw [sumTwoSquaresCount_eq_four_mul n hn, chi4DivisorSum] at h
  push_cast at h
  linarith

/-- **Corollary 2 of Proposition 17.6.1.** For odd `m > 0`, the number of integral solutions
`(x, y)`, `x, y > 0`, of `x² + y² = 2m` is `∑_{d ∣ m} χ(d)`. -/
@[kb "irelandrosen1990" "Ch. 17, §6, Corollary 2 to Prop 17.6.1, p. 291"]
theorem ncard_pos_pos_two_mul {m : ℕ} (hm : 0 < m) (hodd : Odd m) :
    (({v : ℤ × ℤ | 0 < v.1 ∧ 0 < v.2 ∧ v.1 ^ 2 + v.2 ^ 2 = 2 * m}.ncard : ℕ) : ℤ) =
      ∑ d ∈ m.divisors, chi4 d := by
  have h := ncard_quarterSet (n := 2 * m) (by omega)
  have hset : {v : ℤ × ℤ | 0 < v.1 ∧ 0 < v.2 ∧ v.1 ^ 2 + v.2 ^ 2 = 2 * m} = quarterSet (2 * m) := by
    ext ⟨x, y⟩
    simp only [quarterSet, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2.le, by push_cast; exact h3⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, lt_of_le_of_ne h2 ?_, by push_cast at h3; exact h3⟩
      rintro rfl
      -- `x² = 2m` with `m` odd is impossible
      push_cast at h3
      have h3' : x ^ 2 = 2 * m := by linarith
      have hev : Even x := (Int.even_pow' two_ne_zero).1 ⟨m, by rw [h3']; ring⟩
      obtain ⟨j, rfl⟩ := hev
      have h4 : 2 * (m : ℤ) = 2 * (2 * (j * j)) := by linear_combination -h3'
      have := Nat.odd_iff.1 hodd
      omega
  rw [hset, h]
  -- the even divisors of `2m` contribute nothing
  have hdiv : (2 * m).divisors = m.divisors ∪ m.divisors.map ⟨(2 * ·), mul_right_injective₀ two_ne_zero⟩ := by
    ext d
    simp only [Nat.mem_divisors, Finset.mem_union, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨hd, -⟩
      rcases Nat.even_or_odd d with ⟨e, rfl⟩ | hd'
      · right
        refine ⟨e, ⟨Nat.dvd_of_mul_dvd_mul_left two_pos (by rwa [two_mul]), by omega⟩, by change 2 * e = _; ring⟩
      · left
        have hc : Nat.Coprime d 2 :=
          ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (Nat.two_dvd_ne_zero.2
            (Nat.odd_iff.1 hd'))).symm
        exact ⟨hc.dvd_of_dvd_mul_left hd, by omega⟩
    · rintro (⟨hd, -⟩ | ⟨e, ⟨he, -⟩, rfl⟩)
      · exact ⟨dvd_mul_of_dvd_right hd 2, by omega⟩
      · exact ⟨mul_dvd_mul_left 2 he, by omega⟩
  rw [hdiv, Finset.sum_union, Finset.sum_map]
  · have h0 : ∑ x ∈ m.divisors, chi4 (2 * x) = 0 :=
      Finset.sum_eq_zero fun e _ => by rw [chi4_eq]; simp
    change _ + ∑ x ∈ m.divisors, chi4 (2 * x) = _
    rw [h0, add_zero]
  · rw [Finset.disjoint_left]
    rintro d hd hd'
    obtain ⟨e, -, he⟩ := Finset.mem_map.1 hd'
    have hde : d = 2 * e := he.symm
    have := Nat.odd_iff.1 (hodd.of_dvd_nat (Nat.dvd_of_mem_divisors hd))
    omega

/-- **Corollary 1 of Proposition 17.6.1.** For `n > 0`, `x² + y² = n` has an integral solution iff
`ord_q n` is even for every prime `q ≡ 3 (mod 4)`; in that case the number of solutions with
`x > 0`, `y ≥ 0` is `∏_{p ≡ 1 (4)} (1 + ord_p n)`. -/
@[kb "irelandrosen1990" "Ch. 17, §6, Corollary 1 to Prop 17.6.1, p. 290"]
theorem exists_sq_add_sq_iff_and_ncard {n : ℕ} (hn : 0 < n) :
    ((∃ x y : ℤ, x ^ 2 + y ^ 2 = n) ↔
      ∀ q ∈ n.primeFactors, q % 4 = 3 → Even (n.factorization q)) ∧
    ((∀ q ∈ n.primeFactors, q % 4 = 3 → Even (n.factorization q)) →
      ((quarterSet n).ncard : ℤ) = ∏ p ∈ n.primeFactors with p % 4 = 1, (1 + n.factorization p : ℤ)) := by
  constructor
  · constructor
    · rintro ⟨x, y, h⟩
      have := Nat.eq_sq_add_sq_iff.1 ⟨x.natAbs, y.natAbs, by
        zify; rw [sq_abs, sq_abs]; exact h.symm⟩
      intro q hq hq3
      rw [Nat.factorization_def n (Nat.prime_of_mem_primeFactors hq), ← Nat.padicValNat_def]
      exact this q hq hq3
    · intro h
      obtain ⟨x, y, hxy⟩ := Nat.eq_sq_add_sq_iff.2 fun q hq hq3 => by
        rw [Nat.padicValNat_def, ← Nat.factorization_def n (Nat.prime_of_mem_primeFactors hq)]
        exact h q hq hq3
      exact ⟨x, y, by exact_mod_cast hxy.symm⟩
  · intro heven
    rw [ncard_quarterSet hn, ← chi4DivisorSum, chi4DivisorSum_eq_prod hn.ne', Finset.prod_filter]
    refine Finset.prod_congr rfl fun p hp => ?_
    simp only [chi4LocalFactor]
    by_cases h1 : p % 4 = 1
    · simp [h1]; ring
    · by_cases h3 : p % 4 = 3
      · simp [h3, heven p hp h3]
      · simp [h1, h3]

end NTKB.IrelandRosen.TwoSquares
