/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Attr
import NTKB.Elementary.NZM.Farey
import NTKB.Elementary.HardyWright.ArithmeticFunctions.Farey
import Mathlib.Tactic.Linarith

/-!
# The Farey table (Niven–Zuckerman–Montgomery, § 6.1)

Row `1` of the table is `0/1, 1/1`; row `n + 1` is obtained from row `n` by inserting the mediant
`(a + a')/(b + b')` between consecutive entries `a/b, a'/b'` whenever `b + b' = n + 1`.  A row is
a `List (ℕ × ℕ)` of (numerator, denominator) pairs.

* `fareyRow`, `insertMediants`: the table (`fareyRow 0` is a junk value equal to `fareyRow 1`).
* Theorem 6.1: consecutive entries satisfy `a'b - ab' = 1`.
* Corollary 6.2: every entry is in lowest terms.
* Corollary 6.3: every row is strictly increasing.
* Theorem 6.5: a reduced `x/y` with `0 < x < y` is in row `n` iff `y ≤ n`.
* Corollary 6.6: the values of row `n` are exactly `NTKB.HardyWright.fareySeries n`, in increasing
  order.

Since "consecutive" is awkward for lists, the induction runs through recursively defined predicates
(`FareyDet`, `FareySum`) on lists; `fareyRow_consecutive_det` translates back to a statement about
`l₁ ++ p :: q :: l₂`.
-/

namespace NTKB.NZM

/-- The value `a/b` of a table entry `(a, b)`. -/
def fareyVal (p : ℕ × ℕ) : ℚ := (p.1 : ℚ) / p.2

/-- Insert the mediant between consecutive entries `p, q` whenever `p.2 + q.2 = n`. -/
def insertMediants (n : ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | [p] => [p]
  | p :: q :: rest =>
    if p.2 + q.2 = n then
      p :: (p.1 + q.1, p.2 + q.2) :: insertMediants n (q :: rest)
    else p :: insertMediants n (q :: rest)

/-- The Farey table: row `1` is `0/1, 1/1`, row `n + 1` is `insertMediants (n + 1)` of row `n`.
(`fareyRow 0` is a junk value, equal to row `1`.) -/
def fareyRow : ℕ → List (ℕ × ℕ)
  | 0 => [(0, 1), (1, 1)]
  | 1 => [(0, 1), (1, 1)]
  | n + 2 => insertMediants (n + 2) (fareyRow (n + 1))

/-- Consecutive entries `p, q` of the list satisfy `q.1 p.2 = p.1 q.2 + 1` (i.e. `a'b - ab' = 1`). -/
def FareyDet : List (ℕ × ℕ) → Prop
  | [] => True
  | [_] => True
  | p :: q :: rest => q.1 * p.2 = p.1 * q.2 + 1 ∧ FareyDet (q :: rest)

/-- Consecutive entries `p, q` of the list satisfy `n < p.2 + q.2`. -/
def FareySum (n : ℕ) : List (ℕ × ℕ) → Prop
  | [] => True
  | [_] => True
  | p :: q :: rest => n < p.2 + q.2 ∧ FareySum n (q :: rest)

/-- Every entry has denominator in `[1, n]`, numerator `≤` denominator, and is reduced. -/
abbrev FareyElts (n : ℕ) (l : List (ℕ × ℕ)) : Prop :=
  ∀ p ∈ l, 0 < p.2 ∧ p.2 ≤ n ∧ p.1 ≤ p.2 ∧ Nat.Coprime p.1 p.2

/-- The invariant of the `n`-th row. -/
structure FareyInv (n : ℕ) (l : List (ℕ × ℕ)) : Prop where
  elts : FareyElts n l
  det : FareyDet l
  sum : FareySum n l

theorem fareyDet_cons_cons {p q : ℕ × ℕ} {rest : List (ℕ × ℕ)} :
    FareyDet (p :: q :: rest) ↔ (q.1 * p.2 = p.1 * q.2 + 1 ∧ FareyDet (q :: rest)) := Iff.rfl

theorem fareySum_cons_cons {n : ℕ} {p q : ℕ × ℕ} {rest : List (ℕ × ℕ)} :
    FareySum n (p :: q :: rest) ↔ (n < p.2 + q.2 ∧ FareySum n (q :: rest)) := Iff.rfl

theorem fareyDet_tail {a : ℕ × ℕ} {l : List (ℕ × ℕ)} (h : FareyDet (a :: l)) : FareyDet l := by
  cases l with
  | nil => simp [FareyDet]
  | cons q rest => exact (fareyDet_cons_cons.1 h).2

theorem fareySum_tail {n : ℕ} {a : ℕ × ℕ} {l : List (ℕ × ℕ)} (h : FareySum n (a :: l)) :
    FareySum n l := by
  cases l with
  | nil => simp [FareySum]
  | cons q rest => exact (fareySum_cons_cons.1 h).2

theorem fareyElts_tail {n : ℕ} {a : ℕ × ℕ} {l : List (ℕ × ℕ)} (h : FareyElts n (a :: l)) :
    FareyElts n l := fun r hr => h r (by simp [hr])

theorem fareyElts_mono {n : ℕ} {l : List (ℕ × ℕ)} (h : FareyElts n l) : FareyElts (n + 1) l :=
  fun r hr => by
    obtain ⟨h1, h2, h3, h4⟩ := h r hr
    exact ⟨h1, by omega, h3, h4⟩

theorem insertMediants_single (n : ℕ) (p : ℕ × ℕ) : insertMediants n [p] = [p] := by
  simp [insertMediants]

theorem insertMediants_cons_cons_of_eq {n : ℕ} {p q : ℕ × ℕ} (rest : List (ℕ × ℕ))
    (h : p.2 + q.2 = n) :
    insertMediants n (p :: q :: rest) =
      p :: (p.1 + q.1, p.2 + q.2) :: insertMediants n (q :: rest) := by
  simp [insertMediants, h]

theorem insertMediants_cons_cons_of_ne {n : ℕ} {p q : ℕ × ℕ} (rest : List (ℕ × ℕ))
    (h : ¬ p.2 + q.2 = n) :
    insertMediants n (p :: q :: rest) = p :: insertMediants n (q :: rest) := by
  simp [insertMediants, h]

theorem insertMediants_cons (n : ℕ) (p : ℕ × ℕ) (l : List (ℕ × ℕ)) :
    ∃ r, insertMediants n (p :: l) = p :: r := by
  cases l with
  | nil => exact ⟨[], insertMediants_single n p⟩
  | cons q rest =>
    by_cases h : p.2 + q.2 = n
    · exact ⟨_, insertMediants_cons_cons_of_eq rest h⟩
    · exact ⟨_, insertMediants_cons_cons_of_ne rest h⟩

theorem mem_insertMediants_of_mem (k : ℕ) (z : ℕ × ℕ) :
    ∀ l : List (ℕ × ℕ), z ∈ l → z ∈ insertMediants k l := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons p t ih =>
    intro hz
    cases t with
    | nil => rw [insertMediants_single]; exact hz
    | cons q rest =>
      by_cases hs : p.2 + q.2 = k
      · rw [insertMediants_cons_cons_of_eq rest hs]
        rcases List.mem_cons.mp hz with h | h
        · simp [h]
        · simp [ih h]
      · rw [insertMediants_cons_cons_of_ne rest hs]
        rcases List.mem_cons.mp hz with h | h
        · simp [h]
        · simp [ih h]

theorem coprime_of_det {a b c d : ℕ} (h : c * b = a * d + 1) : Nat.Coprime c d := by
  have h1 : Nat.gcd c d ∣ c * b := Dvd.dvd.mul_right (Nat.gcd_dvd_left c d) b
  have h2 : Nat.gcd c d ∣ a * d := Dvd.dvd.mul_left (Nat.gcd_dvd_right c d) a
  rw [h] at h1
  have h3 : Nat.gcd c d ∣ 1 := (Nat.dvd_add_right h2).mp h1
  exact Nat.dvd_one.mp h3

/-- One step of the table preserves the invariant. -/
theorem fareyInv_insert (n : ℕ) :
    ∀ l : List (ℕ × ℕ), FareyInv n l → FareyInv (n + 1) (insertMediants (n + 1) l) := by
  intro l
  induction l with
  | nil =>
    intro _
    have e : insertMediants (n + 1) [] = [] := rfl
    rw [e]
    exact ⟨fun p hp => by simp at hp, by simp [FareyDet], by simp [FareySum]⟩
  | cons p t ih =>
    intro hI
    cases t with
    | nil =>
      rw [insertMediants_single]
      exact ⟨fareyElts_mono hI.elts, by simp [FareyDet], by simp [FareySum]⟩
    | cons q rest =>
      have hT : FareyInv n (q :: rest) :=
        ⟨fareyElts_tail hI.elts, fareyDet_tail hI.det, fareySum_tail hI.sum⟩
      have hIH := ih hT
      obtain ⟨r', hr'⟩ := insertMediants_cons (n + 1) q rest
      rw [hr'] at hIH
      obtain ⟨hEI, hDI, hSI⟩ := hIH
      obtain ⟨hdet, _⟩ := fareyDet_cons_cons.1 hI.det
      obtain ⟨hsum, _⟩ := fareySum_cons_cons.1 hI.sum
      obtain ⟨hp1, hp2, hp3, hp4⟩ := hI.elts p (by simp)
      obtain ⟨hq1, hq2, hq3, hq4⟩ := hI.elts q (by simp)
      by_cases hs : p.2 + q.2 = n + 1
      · rw [insertMediants_cons_cons_of_eq rest hs, hr']
        have hmc : Nat.Coprime (p.1 + q.1) (p.2 + q.2) :=
          coprime_of_det (a := p.1) (b := p.2) (by nlinarith [hdet])
        refine ⟨?_, ?_, ?_⟩
        · intro r hr
          rcases List.mem_cons.mp hr with h | hr
          · rw [h]; exact ⟨hp1, by omega, hp3, hp4⟩
          · rcases List.mem_cons.mp hr with h | hr
            · rw [h]
              exact ⟨by show 0 < p.2 + q.2; omega, by show p.2 + q.2 ≤ n + 1; omega,
                by show p.1 + q.1 ≤ p.2 + q.2; omega, hmc⟩
            · exact hEI r hr
        · refine fareyDet_cons_cons.2 ⟨?_, fareyDet_cons_cons.2 ⟨?_, hDI⟩⟩
          · show (p.1 + q.1) * p.2 = p.1 * (p.2 + q.2) + 1
            nlinarith [hdet]
          · show q.1 * (p.2 + q.2) = (p.1 + q.1) * q.2 + 1
            nlinarith [hdet]
        · refine fareySum_cons_cons.2 ⟨?_, fareySum_cons_cons.2 ⟨?_, hSI⟩⟩
          · show n + 1 < p.2 + (p.2 + q.2)
            omega
          · show n + 1 < (p.2 + q.2) + q.2
            omega
      · rw [insertMediants_cons_cons_of_ne rest hs, hr']
        refine ⟨?_, fareyDet_cons_cons.2 ⟨hdet, hDI⟩, fareySum_cons_cons.2 ⟨by omega, hSI⟩⟩
        intro r hr
        rcases List.mem_cons.mp hr with h | hr
        · rw [h]; exact ⟨hp1, by omega, hp3, hp4⟩
        · exact hEI r hr

/-- Key step of Theorem 6.5: a reduced fraction `x/y` with `y = n + 1`, lying strictly above the
first entry `p` and strictly below some entry of the list, is inserted into the next row. -/
theorem mem_insertMediants_of_between {n x y : ℕ} (hy : y = n + 1) (hxy : Nat.Coprime x y) :
    ∀ (l : List (ℕ × ℕ)) (p : ℕ × ℕ), FareyInv n (p :: l) → p.1 * y < x * p.2 →
      (∃ r ∈ p :: l, x * r.2 < r.1 * y) → (x, y) ∈ insertMediants (n + 1) (p :: l) := by
  intro l
  induction l with
  | nil =>
    intro p _ hpx hex
    obtain ⟨r, hr, hlt⟩ := hex
    have hrp : r = p := by simpa using hr
    rw [hrp] at hlt
    exact absurd hlt (lt_asymm hpx)
  | cons q rest ih =>
    intro p hI hpx hex
    obtain ⟨hdet, _⟩ := fareyDet_cons_cons.1 hI.det
    obtain ⟨hsum, _⟩ := fareySum_cons_cons.1 hI.sum
    obtain ⟨hp1, hp2, hp3, hp4⟩ := hI.elts p (by simp)
    obtain ⟨hq1, hq2, hq3, hq4⟩ := hI.elts q (by simp)
    rcases lt_trichotomy (x * q.2) (q.1 * y) with hlt | heq | hgt
    · -- `x/y` lies strictly between `p` and `q`: Theorem 6.4
      have hb : (0 : ℤ) < p.2 := by exact_mod_cast hp1
      have hb' : (0 : ℤ) < q.2 := by exact_mod_cast hq1
      have hdetZ : (q.1 : ℤ) * p.2 - p.1 * q.2 = 1 := by
        have h' : ((q.1 * p.2 : ℕ) : ℤ) = ((p.1 * q.2 + 1 : ℕ) : ℤ) := by rw [hdet]
        push_cast at h'
        linarith
      have hyZ : (0 : ℤ) < y := by exact_mod_cast (show 0 < y by omega)
      have h1 : (p.1 : ℤ) * y < x * p.2 := by exact_mod_cast hpx
      have h2 : (x : ℤ) * q.2 < q.1 * y := by exact_mod_cast hlt
      obtain ⟨hle, himp⟩ := mediant_least_denominator hb hb' hdetZ hyZ h1 h2
      have hleN : p.2 + q.2 ≤ y := by exact_mod_cast hle
      have hsEq : p.2 + q.2 = n + 1 := by omega
      have hyZeq : (y : ℤ) = p.2 + q.2 := by exact_mod_cast (show y = p.2 + q.2 by omega)
      have hxZ := himp hyZeq
      have hxN : x = p.1 + q.1 := by exact_mod_cast hxZ
      have e : (x, y) = (p.1 + q.1, p.2 + q.2) :=
        Prod.ext hxN (by show y = p.2 + q.2; omega)
      rw [insertMediants_cons_cons_of_eq rest hsEq, e]
      simp
    · -- `x/y = q`: impossible since `y` is larger than every denominator in the row
      exfalso
      have hd1 : y ∣ x * q.2 := by rw [heq]; exact dvd_mul_left y q.1
      have hd2 : y ∣ q.2 := (Nat.Coprime.symm hxy).dvd_of_dvd_mul_left hd1
      have := Nat.le_of_dvd hq1 hd2
      omega
    · -- `x/y` is above `q`: recurse
      have hT : FareyInv n (q :: rest) :=
        ⟨fareyElts_tail hI.elts, fareyDet_tail hI.det, fareySum_tail hI.sum⟩
      have hex' : ∃ r ∈ q :: rest, x * r.2 < r.1 * y := by
        obtain ⟨r, hr, hlt⟩ := hex
        rcases List.mem_cons.mp hr with h | h
        · rw [h] at hlt; exact absurd hlt (lt_asymm hpx)
        · exact ⟨r, h, hlt⟩
      have hih := ih q hT hgt hex'
      by_cases hs : p.2 + q.2 = n + 1
      · rw [insertMediants_cons_cons_of_eq rest hs]; simp [hih]
      · rw [insertMediants_cons_cons_of_ne rest hs]; simp [hih]

theorem fareyRow_succ (n : ℕ) (hn : 1 ≤ n) :
    fareyRow (n + 1) = insertMediants (n + 1) (fareyRow n) := by
  cases n with
  | zero => omega
  | succ m => rfl

theorem fareyRow_head (n : ℕ) : ∃ t, fareyRow n = (0, 1) :: t := by
  induction n with
  | zero => exact ⟨[(1, 1)], rfl⟩
  | succ m ih =>
    obtain ⟨t, ht⟩ := ih
    cases m with
    | zero => exact ⟨[(1, 1)], rfl⟩
    | succ k =>
      have e : fareyRow (k + 1 + 1) = insertMediants (k + 1 + 1) (fareyRow (k + 1)) := by
        rfl
      rw [e, ht]
      exact insertMediants_cons _ _ _

/-- The invariant and the covering property of the `n`-th row, `n ≥ 1`. -/
theorem fareyRow_spec (n : ℕ) (hn : 1 ≤ n) :
    FareyInv n (fareyRow n) ∧
      ∀ x y : ℕ, Nat.Coprime x y → x ≤ y → 0 < y → y ≤ n → (x, y) ∈ fareyRow n := by
  induction n, hn using Nat.le_induction with
  | base =>
    have h1 : fareyRow 1 = [(0, 1), (1, 1)] := rfl
    rw [h1]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro p hp
      simp at hp
      rcases hp with rfl | rfl <;> simp
    · exact fareyDet_cons_cons.2 ⟨by decide, by simp [FareyDet]⟩
    · exact fareySum_cons_cons.2 ⟨by decide, by simp [FareySum]⟩
    · intro x y hc hxy hy hy1
      obtain rfl : y = 1 := by omega
      have hx : x = 0 ∨ x = 1 := by omega
      rcases hx with rfl | rfl <;> simp
  | succ n hn ih =>
    obtain ⟨hI, hcov⟩ := ih
    rw [fareyRow_succ n hn]
    refine ⟨fareyInv_insert n _ hI, ?_⟩
    intro x y hc hxy hy hyn
    by_cases hyle : y ≤ n
    · exact mem_insertMediants_of_mem (n + 1) (x, y) _ (hcov x y hc hxy hy hyle)
    · have hyeq : y = n + 1 := by omega
      have hy2 : 2 ≤ y := by omega
      have hx0 : 0 < x := by
        rcases Nat.eq_zero_or_pos x with h | h
        · rw [h] at hc
          have hy1 : y = 1 := by simpa using hc
          omega
        · exact h
      have hxlt : x < y := by
        rcases Nat.lt_or_ge x y with h | h
        · exact h
        · have hxe : x = y := le_antisymm hxy h
          rw [← hxe] at hc
          have hx1 : x = 1 := by simpa using hc
          omega
      obtain ⟨t, ht⟩ := fareyRow_head n
      have hone : (1, 1) ∈ fareyRow n :=
        hcov 1 1 (Nat.coprime_one_left 1) le_rfl one_pos hn
      have key := mem_insertMediants_of_between hyeq hc t (0, 1) (by rw [← ht]; exact hI)
        (by show 0 * y < x * 1; omega)
        ⟨(1, 1), by rw [← ht]; exact hone, by show x * 1 < 1 * y; omega⟩
      rw [ht]
      exact key

theorem pairwise_lt_of_det :
    ∀ l : List (ℕ × ℕ), (∀ p ∈ l, 0 < p.2) → FareyDet l →
      l.Pairwise (fun p q => fareyVal p < fareyVal q) := by
  intro l
  induction l with
  | nil => intro _ _; exact List.Pairwise.nil
  | cons p t ih =>
    intro hpos hD
    have hrest := ih (fun r hr => hpos r (by simp [hr])) (fareyDet_tail hD)
    cases t with
    | nil => exact List.pairwise_cons.mpr ⟨by simp, List.Pairwise.nil⟩
    | cons q rest =>
      obtain ⟨hdet, _⟩ := fareyDet_cons_cons.1 hD
      have hp : 0 < p.2 := hpos p (by simp)
      have hq : 0 < q.2 := hpos q (by simp)
      have hpq : fareyVal p < fareyVal q := by
        unfold fareyVal
        have hp' : (0 : ℚ) < p.2 := by exact_mod_cast hp
        have hq' : (0 : ℚ) < q.2 := by exact_mod_cast hq
        have h' : (q.1 : ℚ) * p.2 = p.1 * q.2 + 1 := by exact_mod_cast hdet
        rw [div_lt_div_iff₀ hp' hq']
        linarith
      refine List.pairwise_cons.mpr ⟨?_, hrest⟩
      intro r hr
      rcases List.mem_cons.mp hr with h | h
      · rw [h]; exact hpq
      · exact lt_trans hpq ((List.pairwise_cons.mp hrest).1 r h)

/-- **Theorem 6.1 (Farey table form).** If `a/b` and `a'/b'` are consecutive fractions in the
`n`-th row of the Farey table, `a/b` to the left of `a'/b'`, then `a'b - ab' = 1`. -/
@[kb "nivenzuckermanmontgomery" "Thm 6.1, p. 298"]
theorem fareyRow_consecutive_det {n : ℕ} (hn : 1 ≤ n) {l₁ l₂ : List (ℕ × ℕ)} {p q : ℕ × ℕ}
    (h : fareyRow n = l₁ ++ p :: q :: l₂) : (q.1 : ℤ) * p.2 - p.1 * q.2 = 1 := by
  have hD := (fareyRow_spec n hn).1.det
  rw [h] at hD
  have key : ∀ (l₁ : List (ℕ × ℕ)), FareyDet (l₁ ++ p :: q :: l₂) →
      q.1 * p.2 = p.1 * q.2 + 1 := by
    intro l₁
    induction l₁ with
    | nil => intro h; exact (fareyDet_cons_cons.1 h).1
    | cons a t ih =>
      intro h
      rw [List.cons_append] at h
      exact ih (fareyDet_tail h)
  have h' : ((q.1 * p.2 : ℕ) : ℤ) = ((p.1 * q.2 + 1 : ℕ) : ℤ) := by rw [key l₁ hD]
  push_cast at h'
  linarith

/-- **Corollary 6.2.** Every `a/b` in the Farey table is in reduced form, `(a, b) = 1`. -/
@[kb "nivenzuckermanmontgomery" "Cor 6.2, p. 298"]
theorem fareyRow_coprime {n : ℕ} (hn : 1 ≤ n) {p : ℕ × ℕ} (hp : p ∈ fareyRow n) :
    Nat.Coprime p.1 p.2 :=
  ((fareyRow_spec n hn).1.elts p hp).2.2.2

/-- **Corollary 6.3.** The fractions in each row of the Farey table are listed in (strictly
increasing) order of their size. -/
@[kb "nivenzuckermanmontgomery" "Cor 6.3, p. 298"]
theorem fareyRow_pairwise_lt {n : ℕ} (hn : 1 ≤ n) :
    (fareyRow n).Pairwise (fun p q => fareyVal p < fareyVal q) := by
  obtain ⟨hI, _⟩ := fareyRow_spec n hn
  exact pairwise_lt_of_det _ (fun p hp => (hI.elts p hp).1) hI.det

/-- Every denominator in row `n` is at most `n` (the second half of Theorem 6.5: a fraction with
denominator `y` does not occur before row `y`). -/
theorem denom_le_of_mem_fareyRow {n : ℕ} (hn : 1 ≤ n) {p : ℕ × ℕ} (hp : p ∈ fareyRow n) :
    p.2 ≤ n :=
  ((fareyRow_spec n hn).1.elts p hp).2.1

/-- **Theorem 6.5.** If `0 < x < y` and `(x, y) = 1`, then `x/y` appears in the `y`-th and all later
rows, and in no earlier row: for `n ≥ 1`, `x/y ∈ row n ↔ y ≤ n`. -/
@[kb "nivenzuckermanmontgomery" "Thm 6.5, p. 299"]
theorem mem_fareyRow_iff {n : ℕ} (hn : 1 ≤ n) {x y : ℕ} (hx : 0 < x) (hxy : x < y)
    (hc : Nat.Coprime x y) : (x, y) ∈ fareyRow n ↔ y ≤ n := by
  constructor
  · intro h
    exact denom_le_of_mem_fareyRow hn h
  · intro h
    exact (fareyRow_spec n hn).2 x y hc hxy.le (by omega) h

/-- Theorem 6.5, covering form including `0/1` and `1/1`. -/
theorem mem_fareyRow_of_le {n : ℕ} (hn : 1 ≤ n) {x y : ℕ} (hc : Nat.Coprime x y) (hxy : x ≤ y)
    (hy : 0 < y) (hyn : y ≤ n) : (x, y) ∈ fareyRow n :=
  (fareyRow_spec n hn).2 x y hc hxy hy hyn

theorem mem_fareyRow_iff_fareyPairs {n : ℕ} (hn : 1 ≤ n) (p : ℕ × ℕ) :
    p ∈ fareyRow n ↔ p ∈ NTKB.HardyWright.fareyPairs n := by
  simp only [NTKB.HardyWright.fareyPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · intro hp
    obtain ⟨h1, h2, h3, h4⟩ := (fareyRow_spec n hn).1.elts p hp
    exact ⟨⟨⟨Nat.zero_le _, by omega⟩, by omega, h2⟩, h3, h4⟩
  · rintro ⟨⟨⟨_, _⟩, h1, h2⟩, h3, h4⟩
    exact (fareyRow_spec n hn).2 p.1 p.2 h4 h3 (by omega) h2

/-- **Corollary 6.6.** The `n`-th row consists exactly of the reduced fractions `a/b` with
`0 ≤ a/b ≤ 1` and `0 < b ≤ n` (its set of values is `NTKB.HardyWright.fareySeries n`), listed in
increasing order. -/
@[kb "nivenzuckermanmontgomery" "Cor 6.6, p. 300"]
theorem fareyRow_values {n : ℕ} (hn : 1 ≤ n) :
    ((fareyRow n).map fareyVal).toFinset = NTKB.HardyWright.fareySeries n ∧
      ((fareyRow n).map fareyVal).Pairwise (· < ·) := by
  refine ⟨?_, ?_⟩
  · rw [NTKB.HardyWright.fareySeries_eq_image]
    ext q
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_image]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, (mem_fareyRow_iff_fareyPairs hn p).1 hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, (mem_fareyRow_iff_fareyPairs hn p).2 hp, rfl⟩
  · rw [List.pairwise_map]
    exact fareyRow_pairwise_lt hn

end NTKB.NZM
