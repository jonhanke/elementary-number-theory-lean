/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.LegendreSymbol.GaussEisensteinLemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import NTKB.Attr

/-!
# Ireland–Rosen, Chapter 5, Section 3: quadratic reciprocity by Eisenstein's product

With `f(z) = e^(2πiz) - e^(-2πiz) = 2i sin 2πz`:

* **Lemma** (p. 70): for odd `n` and `ζ = e^(2πi/n)`,
  `x^n - y^n = ∏_{k=0}^{n-1} (ζ^k x - ζ^(-k) y)`;
* **Proposition 5.3.1**: for odd `n`, `f(nz) = f(z) ∏_{k=1}^{(n-1)/2} f(z + k/n) f(z - k/n)`;
* **Proposition 5.3.2**: for an odd prime `p ∤ a`,
  `∏_{l=1}^{(p-1)/2} f(la/p) = (a/p) ∏_{l=1}^{(p-1)/2} f(l/p)`;
* **Quadratic reciprocity** (p. 71), deduced from 5.3.1 and 5.3.2 as in the book.

The only input from Mathlib's theory of quadratic residues is Gauss' lemma
(`ZMod.gauss_lemma`, with `ZMod.Ico_map_valMinAbs_natAbs_eq_Ico_map_id`); Mathlib's own proof of
reciprocity (via Gauss sums) is not used.
-/

open Complex Finset Real

namespace NTKB.IrelandRosen

/-- Eisenstein's function `f(z) = e^(2πiz) - e^(-2πiz)` (Ireland–Rosen, Chapter 5, Section 3). -/
noncomputable def eisensteinF (z : ℂ) : ℂ := cexp (2 * π * I * z) - cexp (-(2 * π * I * z))

theorem eisensteinF_eq_sin (z : ℂ) : eisensteinF z = 2 * I * Complex.sin (2 * π * z) := by
  rw [eisensteinF, Complex.sin, show (2 * (π : ℂ) * z * I) = 2 * π * I * z by ring,
    show (-(2 * (π : ℂ) * z) * I) = -(2 * π * I * z) by ring]
  linear_combination (cexp (2 * π * I * z) - cexp (-(2 * π * I * z))) * I_sq

/-- `f(z + m) = f(z)` for an integer `m`. -/
theorem eisensteinF_add_int (z : ℂ) (m : ℤ) : eisensteinF (z + m) = eisensteinF z := by
  simp only [eisensteinF]
  have h1 : 2 * π * I * (z + m) = 2 * π * I * z + m * (2 * π * I) := by ring
  have h2 : -(2 * π * I * (z + m)) = -(2 * π * I * z) + (-m : ℤ) * (2 * π * I) := by
    push_cast; ring
  rw [h2, h1, Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
    Complex.exp_int_mul_two_pi_mul_I, mul_one, mul_one]

/-- `f(-z) = -f(z)`. -/
theorem eisensteinF_neg (z : ℂ) : eisensteinF (-z) = -eisensteinF z := by
  simp only [eisensteinF, mul_neg, neg_neg]
  ring

/-- `f(r) ≠ 0` for real `0 < r < 1/2`. -/
theorem eisensteinF_ne_zero {r : ℝ} (h0 : 0 < r) (h1 : r < 1 / 2) : eisensteinF r ≠ 0 := by
  rw [eisensteinF_eq_sin]
  have : Complex.sin (2 * π * r) = (Real.sin (2 * π * r) : ℂ) := by push_cast; rfl
  rw [this]
  have hpos : 0 < Real.sin (2 * π * r) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  exact mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (by exact_mod_cast hpos.ne')

/-- The `n`-th roots of unity are the powers `μ^k`, `k < n`, of a primitive one. -/
theorem prod_nthRootsFinset_eq_prod_range {K M : Type*} [CommRing K] [IsDomain K] [CommMonoid M]
    {μ : K} {n : ℕ} (h : IsPrimitiveRoot μ n) (hn : 0 < n) (g : K → M) :
    ∏ ζ ∈ Polynomial.nthRootsFinset n (1 : K), g ζ = ∏ k ∈ range n, g (μ ^ k) := by
  classical
  have hinj : Set.InjOn (fun k : ℕ ↦ μ ^ k) (range n : Set ℕ) := fun a ha b hb hab ↦
    h.pow_inj (mem_range.mp ha) (mem_range.mp hb) hab
  have himage : (range n).image (fun k ↦ μ ^ k) = Polynomial.nthRootsFinset n (1 : K) := by
    refine eq_of_subset_of_card_le (fun x hx ↦ ?_) ?_
    · obtain ⟨k, -, rfl⟩ := mem_image.mp hx
      rw [Polynomial.mem_nthRootsFinset hn, ← pow_mul, mul_comm, pow_mul, h.pow_eq_one, one_pow]
    · rw [h.card_nthRootsFinset, card_image_of_injOn hinj, card_range]
  rw [← himage, prod_image hinj]

/-- **Ireland–Rosen, Chapter 5, Lemma of Section 3.** For odd `n > 0` and `ζ = e^(2πi/n)`,
`x^n - y^n = ∏_{k=0}^{n-1} (ζ^k x - ζ^(-k) y)`. -/
@[kb "irelandrosen1990" "Ch 5, Section 3, Lemma, p. 70"]
theorem pow_sub_pow_eq_prod_zeta {n : ℕ} (hn : Odd n) (x y : ℂ) :
    x ^ n - y ^ n = ∏ k ∈ range n,
      (cexp (2 * π * I / n) ^ k * x - (cexp (2 * π * I / n) ^ k)⁻¹ * y) := by
  set ζ := cexp (2 * π * I / n)
  have hn0 : 0 < n := hn.pos
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn0.ne'
  have hζ0 : ζ ≠ 0 := Complex.exp_ne_zero _
  -- `μ = ζ^(-2)` is also a primitive `n`-th root of unity
  have hμ : IsPrimitiveRoot (ζ⁻¹ ^ 2) n :=
    hζ.inv.pow_of_coprime 2 (Nat.coprime_two_left.mpr hn)
  rw [hμ.pow_sub_pow_eq_prod_sub_mul x y hn0, prod_nthRootsFinset_eq_prod_range hμ hn0
    (fun μ ↦ x - μ * y)]
  -- `ζ^k x - ζ^(-k) y = ζ^k (x - ζ^(-2k) y)` and `∏ ζ^k = ζ^(n(n-1)/2) = 1`
  have hfac : ∀ k, ζ ^ k * x - (ζ ^ k)⁻¹ * y = ζ ^ k * (x - (ζ⁻¹ ^ 2) ^ k * y) := fun k ↦ by
    rw [← pow_mul, inv_pow, mul_comm 2 k, pow_mul]
    field_simp
  rw [prod_congr rfl fun k _ ↦ hfac k, prod_mul_distrib, prod_pow_eq_pow_sum, sum_range_id]
  have : ζ ^ (n * (n - 1) / 2) = 1 := by
    obtain ⟨m, rfl⟩ := hn
    rw [show (2 * m + 1) * (2 * m + 1 - 1) / 2 = (2 * m + 1) * m by
      rw [Nat.add_sub_cancel, mul_comm 2 m, ← mul_assoc, Nat.mul_div_cancel _ two_pos]]
    rw [pow_mul, hζ.pow_eq_one, one_pow]
  rw [this, one_mul]

/-- `f(z) = ζ^0`-factor form: `f(z + k/n) = ζ^k e(z) - ζ^(-k) e(-z)`. -/
theorem eisensteinF_add_div (z : ℂ) (n k : ℕ) :
    eisensteinF (z + k / n) = cexp (2 * π * I / n) ^ k * cexp (2 * π * I * z) -
      (cexp (2 * π * I / n) ^ k)⁻¹ * cexp (-(2 * π * I * z)) := by
  rw [eisensteinF, ← Complex.exp_nat_mul, ← Complex.exp_neg, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 2 <;> ring

/-- `f(nz) = ∏_{k=0}^{n-1} f(z + k/n)` for odd `n` (first step of Proposition 5.3.1). -/
theorem eisensteinF_mul_eq_prod_range {n : ℕ} (hn : Odd n) (z : ℂ) :
    eisensteinF (n * z) = ∏ k ∈ range n, eisensteinF (z + k / n) := by
  rw [prod_congr rfl fun k _ ↦ eisensteinF_add_div z n k, ← pow_sub_pow_eq_prod_zeta hn,
    eisensteinF, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  congr 2 <;> ring

/-- **Ireland–Rosen, Proposition 5.3.1.** For odd `n > 0`,
`f(nz) = f(z) ∏_{k=1}^{(n-1)/2} f(z + k/n) f(z - k/n)`; the book writes it as
`f(nz)/f(z) = ∏ …` (see `eisensteinF_mul_div` for that form). -/
@[kb "irelandrosen1990" "Prop 5.3.1, p. 70"]
theorem eisensteinF_mul {n : ℕ} (hn : Odd n) (z : ℂ) :
    eisensteinF (n * z) =
      eisensteinF z *
        ∏ k ∈ Icc 1 ((n - 1) / 2), eisensteinF (z + k / n) * eisensteinF (z - k / n) := by
  obtain ⟨m, rfl⟩ := hn
  have hm : (2 * m + 1 - 1) / 2 = m := by omega
  set c : ℂ := ((2 * m + 1 : ℕ) : ℂ) with hc
  have hc0 : c ≠ 0 := by rw [hc]; exact_mod_cast (by omega : 2 * m + 1 ≠ 0)
  rw [hm, eisensteinF_mul_eq_prod_range ⟨m, rfl⟩, prod_range_succ',
    show range (2 * m) = range (m + m) by rw [two_mul], prod_range_add]
  -- the factors `k = m + 1, …, 2m` are `f(z - j/n)`, `j = m, …, 1`
  have hsecond : ∏ x ∈ range m, eisensteinF (z + ((m + x + 1 : ℕ) : ℂ) / c) =
      ∏ j ∈ range m, eisensteinF (z - ((j + 1 : ℕ) : ℂ) / c) := by
    rw [← prod_range_reflect]
    refine prod_congr rfl fun j hj ↦ ?_
    have hj := mem_range.mp hj
    have hcast : ((m + (m - 1 - j) + 1 : ℕ) : ℂ) = c - ((j + 1 : ℕ) : ℂ) := by
      rw [hc, ← Nat.cast_sub (by omega)]; congr 1; omega
    rw [hcast, sub_div, div_self hc0, ← add_sub_assoc, add_comm z, add_sub_assoc,
      show (1 : ℂ) = ((1 : ℤ) : ℂ) by simp, add_comm, eisensteinF_add_int]
  rw [hsecond, ← Finset.Ico_add_one_right_eq_Icc, prod_Ico_eq_prod_range, Nat.add_sub_cancel,
    prod_mul_distrib]
  simp only [Nat.cast_zero, zero_div, add_zero, add_comm 1]
  ring

/-- **Ireland–Rosen, Proposition 5.3.1**, in the book's form `f(nz)/f(z) = ∏ …` (when
`f(z) ≠ 0`). -/
theorem eisensteinF_mul_div {n : ℕ} (hn : Odd n) {z : ℂ} (hz : eisensteinF z ≠ 0) :
    eisensteinF (n * z) / eisensteinF z =
      ∏ k ∈ Icc 1 ((n - 1) / 2), eisensteinF (z + k / n) * eisensteinF (z - k / n) := by
  rw [eisensteinF_mul hn, mul_div_cancel_left₀ _ hz]

/-- `f(u/p) = f(v/p)` when `u ≡ v (mod p)`. -/
theorem eisensteinF_intCast_div_congr {p : ℕ} (hp : p ≠ 0) {u v : ℤ} (h : (u : ZMod p) = v) :
    eisensteinF (u / p) = eisensteinF (v / p) := by
  obtain ⟨t, ht⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub u v p).mp h
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  have : (v : ℂ) / p = u / p + t := by
    have := congrArg (fun z : ℤ ↦ (z : ℂ)) ht
    push_cast at this
    field_simp
    linear_combination this
  rw [this, eisensteinF_add_int]

/-- One factor of Proposition 5.3.2: `la ≡ ±m_l (mod p)` with `1 ≤ m_l ≤ (p-1)/2`, hence
`f(la/p) = ±f(m_l/p)`, the sign being `-` iff the least positive residue of `la` exceeds
`p/2`. -/
theorem eisensteinF_mul_div_eq {p : ℕ} [Fact p.Prime] (a : ℤ) (l : ℕ) :
    eisensteinF (l * a / p) =
      (if ((a : ZMod p) * l).val ≤ p / 2 then 1 else -1) *
        eisensteinF (((a : ZMod p) * l).valMinAbs.natAbs / p) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  set v := ((a : ZMod p) * l).valMinAbs
  have hcongr : (((l : ℤ) * a : ℤ) : ZMod p) = (v : ZMod p) := by
    rw [ZMod.coe_valMinAbs]; push_cast; ring
  have h1 := eisensteinF_intCast_div_congr hp hcongr
  push_cast at h1
  rw [h1]
  split_ifs with hv
  · rw [← ZMod.valMinAbs_nonneg_iff] at hv
    rw [one_mul]
    congr 2
    rw [← Int.cast_natCast, Int.natCast_natAbs, abs_of_nonneg hv]
  · rw [← ZMod.valMinAbs_nonneg_iff, not_le] at hv
    have : (v : ℂ) = -((v.natAbs : ℕ) : ℂ) := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, abs_of_neg hv]; push_cast; ring
    rw [this, neg_div, eisensteinF_neg, neg_one_mul]

/-- **Ireland–Rosen, Proposition 5.3.2.** For an odd prime `p` and `p ∤ a`,
`∏_{l=1}^{(p-1)/2} f(la/p) = (a/p) ∏_{l=1}^{(p-1)/2} f(l/p)`. As in the book: `la ≡ ±m_l` with
`l ↦ m_l` a permutation of `1, …, (p-1)/2`, and Gauss' lemma counts the minus signs. -/
@[kb "irelandrosen1990" "Prop 5.3.2, p. 71"]
theorem prod_eisensteinF_mul_div {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {a : ℤ}
    (ha : (a : ZMod p) ≠ 0) :
    ∏ l ∈ Icc 1 ((p - 1) / 2), eisensteinF (l * a / p) =
      legendreSym p a * ∏ l ∈ Icc 1 ((p - 1) / 2), eisensteinF (l / p) := by
  classical
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  have hhalf : (p - 1) / 2 = p / 2 := by obtain ⟨k, rfl⟩ := hodd; omega
  rw [hhalf, ← Finset.Ico_add_one_right_eq_Icc, prod_congr rfl fun l _ ↦ eisensteinF_mul_div_eq a l,
    prod_mul_distrib, Finset.prod_ite]
  simp only [prod_const_one, one_mul, prod_const]
  -- the permutation `l ↦ m_l`
  have hperm : ∏ l ∈ Ico 1 (p / 2 + 1),
      eisensteinF (((a : ZMod p) * l).valMinAbs.natAbs / p) =
      ∏ l ∈ Ico 1 (p / 2 + 1), eisensteinF (l / p) := by
    rw [prod_eq_multiset_prod, prod_eq_multiset_prod]
    have := ZMod.Ico_map_valMinAbs_natAbs_eq_Ico_map_id p (a : ZMod p) ha
    have h2 := congrArg (fun s : Multiset ℕ ↦ (s.map fun k : ℕ ↦ eisensteinF (k / p)).prod) this
    simp only [Multiset.map_map, Function.comp_def, Nat.succ_eq_add_one] at h2
    exact h2
  rw [hperm, ZMod.gauss_lemma hp ha]
  push_cast
  congr 2
  congr 1
  ext x
  simp

/-- **Quadratic reciprocity by Eisenstein's trigonometric proof** (Ireland–Rosen, Chapter 5,
Section 3, p. 71): for distinct odd primes `p, q`,
`(q/p)(p/q) = (-1)^((p-1)/2 · (q-1)/2)`, derived from Propositions 5.3.1 and 5.3.2. -/
@[kb "irelandrosen1990" "Ch 5, Section 3, Theorem 1 (Eisenstein's proof), p. 71"]
theorem quadratic_reciprocity_eisenstein {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hp : p ≠ 2)
    (hq : q ≠ 2) (hpq : p ≠ q) :
    legendreSym q p * legendreSym p q = (-1) ^ ((p - 1) / 2 * ((q - 1) / 2)) := by
  classical
  -- `(q/p) = ∏_{l,m} f(l/p + m/q) f(l/p - m/q)` and symmetrically
  have key : ∀ {p q : ℕ} [Fact p.Prime] [Fact q.Prime], p ≠ 2 → q ≠ 2 → p ≠ q →
      (legendreSym p q : ℂ) = ∏ l ∈ Icc 1 ((p - 1) / 2), ∏ m ∈ Icc 1 ((q - 1) / 2),
        eisensteinF (l / p + m / q) * eisensteinF (l / p - m / q) := by
    intro p q _ _ hp hq hpq
    have hqp : ((q : ℤ) : ZMod p) ≠ 0 := by
      rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
      exact fun h ↦ hpq ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime)
        (Fact.out : q.Prime)).mp h)
    have hqodd : Odd q := (Fact.out : q.Prime).odd_of_ne_two hq
    have h532 := prod_eisensteinF_mul_div hp hqp
    have hA : ∏ l ∈ Icc 1 ((p - 1) / 2), eisensteinF (l / p) ≠ 0 := by
      rw [prod_ne_zero_iff]
      intro l hl
      obtain ⟨hl1, hl2⟩ := mem_Icc.mp hl
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
      have := eisensteinF_ne_zero (r := l / p) (by positivity) (by
        rw [div_lt_iff₀ hp0]
        have : 2 * l < p := by omega
        have : (2 * l : ℝ) < p := by exact_mod_cast this
        linarith)
      push_cast at this
      exact this
    rw [prod_congr rfl fun (l : ℕ) _ ↦ show eisensteinF ((l : ℂ) * ((q : ℤ) : ℂ) / p) =
        eisensteinF ((q : ℂ) * ((l : ℂ) / p)) by push_cast; ring_nf,
      prod_congr rfl fun (l : ℕ) _ ↦ eisensteinF_mul hqodd ((l : ℂ) / p), prod_mul_distrib,
      mul_comm (legendreSym p q : ℂ)] at h532
    exact (mul_left_cancel₀ hA h532).symm
  have hqp := key hp hq hpq
  have hpq' := key hq hp (Ne.symm hpq)
  -- `f(m/q - l/p) = -f(l/p - m/q)`
  have hswap : (legendreSym q p : ℂ) = (-1) ^ ((p - 1) / 2 * ((q - 1) / 2)) * legendreSym p q := by
    rw [hpq', hqp, prod_comm]
    simp_rw [show ∀ x y : ℂ, eisensteinF (x / q + y / p) * eisensteinF (x / q - y / p) =
        -(eisensteinF (y / p + x / q) * eisensteinF (y / p - x / q)) from fun x y ↦ by
          rw [add_comm, show x / q - y / p = -(y / p - x / q) by ring, eisensteinF_neg]; ring]
    rw [prod_congr rfl fun l _ ↦ prod_neg _]
    simp only [Nat.card_Icc, Nat.add_sub_cancel]
    rw [prod_mul_distrib, prod_const, Nat.card_Icc, Nat.add_sub_cancel, ← pow_mul,
      Nat.mul_comm ((q - 1) / 2), mul_comm]
  have hsq : (legendreSym p q : ℂ) ^ 2 = 1 := by
    have hqp0 : ((q : ℤ) : ZMod p) ≠ 0 := by
      rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
      exact fun h ↦ hpq ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime)
        (Fact.out : q.Prime)).mp h)
    exact_mod_cast legendreSym.sq_one p hqp0
  apply Int.cast_injective (α := ℂ)
  push_cast
  rw [hswap, mul_assoc, ← sq, hsq, mul_one]

end NTKB.IrelandRosen
