/-
Ireland–Rosen, Chapter 15, §15.2: Adams' theorem (Proposition 15.2.4), the Kummer congruences
(Theorem 5) and Carlitz's theorem that there are infinitely many irregular primes (Theorem 6).
-/
import NTKB.IrelandRosen.R4.Bernoulli.Basic
import NTKB.IrelandRosen.R4.Bernoulli.Voronoi

/-!
# Adams, Kummer, Carlitz (Ireland–Rosen, §15.2)

* Proposition 15.2.4 (Adams): if `p - 1 ∤ m` (`m` even, `m ≥ 2`), then `B_m / m` is `p`-integral;
  equivalently, `p^l ∣ m` implies `p^l ∣ U_m` (`isPIntegral_bernoulli_div`, `pow_dvd_num_bernoulli`).
* Theorem 5 (Kummer congruences): if `p - 1 ∤ m` and `m' ≡ m (mod φ(p^e))` (`m, m'` even and
  positive), then `(1 - p^(m'-1)) B_{m'}/m' ≡ (1 - p^(m-1)) B_m/m (mod p^e)`
  (`kummer_congruence`); for `e = 1` the factors drop: `B_{m'}/m' ≡ B_m/m (mod p)`
  (`kummer_congruence_mod_p`).
* Theorem 6 (Carlitz): there are infinitely many irregular primes (`infinite_setOf_isIrregularPrime`).

The proofs follow the book: Adams and Kummer from the Voronoi congruences with `n` a power of `p`
and `a` a primitive root modulo `p` (the terms with `p ∣ j` of the Voronoi sum for `p^N` are
`p^(m-1)` times the Voronoi sum for `p^(N-1)`, which produces the factor `1 - p^(m-1)`); Carlitz
from the Kummer congruences, von Staudt–Clausen and the growth of `|B_m/m|`.
-/

namespace NTKB.IrelandRosen

open Finset

section Helpers

variable {p : ℕ} [hp : Fact p.Prime]

/-- If `p - 1 ∤ m` with `m` even, then `p ≥ 5`. -/
lemma five_le_of_not_dvd {m : ℕ} (hm : Even m) (hpm : ¬ p - 1 ∣ m) : 5 ≤ p := by
  have h2 := hp.out.two_le
  by_contra h
  interval_cases p
  · exact hpm (by simp)
  · exact hpm (by simpa using even_iff_two_dvd.mp hm)
  · exact absurd hp.out (by decide)

/-- If `p - 1 ∤ m` with `m` even, then `p` does not divide the denominator of `B_m`. -/
lemma not_dvd_den_bernoulli {m : ℕ} (hm : Even m) (hpm : ¬ p - 1 ∣ m) :
    ¬ p ∣ (bernoulli m).den := by
  obtain ⟨k, rfl⟩ := hm
  have := isPIntegral_bernoulli p (m := k) (by rwa [two_mul])
  rwa [two_mul] at this

omit hp in
lemma isPIntegral_natCast_inv {n : ℕ} (hn : ¬ p ∣ n) : IsPIntegral p (n : ℚ)⁻¹ :=
  isPIntegral_inv_of_not_dvd_num (by rw [Rat.num_natCast]; exact_mod_cast hn)

omit hp in
lemma isPIntegral_intCast_inv {z : ℤ} (hz : ¬ (p : ℤ) ∣ z) : IsPIntegral p (z : ℚ)⁻¹ :=
  isPIntegral_inv_of_not_dvd_num (by rwa [Rat.num_intCast])

/-- An integer divided by `p^l` that is `p`-integral is an integer multiple: `p^l ∣ z`. -/
lemma pow_dvd_of_isPIntegral_div {z : ℤ} {l : ℕ} (h : IsPIntegral p ((z : ℚ) / (p : ℚ) ^ l)) :
    (p : ℤ) ^ l ∣ z := by
  set x : ℚ := (z : ℚ) / (p : ℚ) ^ l with hx
  have hxd : (x.den : ℤ) ∣ (p : ℤ) ^ l := by
    have : x = Rat.divInt z ((p : ℤ) ^ l) := by rw [hx, Rat.divInt_eq_div]; push_cast; rfl
    rw [this]; exact Rat.den_dvd _ _
  have hcop : Nat.Coprime x.den (p ^ l) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_comm).mp ((Nat.Prime.coprime_iff_not_dvd hp.out).2 h))
  have hd1 : x.den = 1 := by
    have hxd' : x.den ∣ p ^ l := by exact_mod_cast hxd
    exact Nat.Coprime.eq_one_of_dvd hcop hxd'
  have hxnum : x = (x.num : ℚ) := by
    conv_lhs => rw [← Rat.num_div_den x]
    rw [hd1]; simp
  have hp0 : ((p : ℚ) ^ l) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  refine ⟨x.num, ?_⟩
  have : (z : ℚ) = (p : ℚ) ^ l * x.num := by rw [← hxnum, hx]; field_simp
  exact_mod_cast this

/-- If `p ∣ num x` then `x / p` is `p`-integral. -/
lemma isPIntegral_div_of_dvd_num {x : ℚ} (h : (p : ℤ) ∣ x.num) : IsPIntegral p (x / p) := by
  obtain ⟨k, hk⟩ := h
  have hcop : ¬ p ∣ x.den := by
    intro hd
    have h1 : (p : ℤ) ∣ (x.den : ℤ) := by exact_mod_cast hd
    have h2 : IsCoprime x.num (x.den : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]; exact_mod_cast x.reduced
    have := h2.isUnit_of_dvd' ⟨k, hk⟩ h1
    rw [Int.isUnit_iff] at this
    rcases this with h | h <;> [exact hp.out.ne_one (by exact_mod_cast h); omega]
  have hx : x / p = Rat.divInt k x.den := by
    rw [Rat.divInt_eq_div]
    conv_lhs => rw [← Rat.num_div_den x, hk]
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    push_cast; field_simp
  unfold IsPIntegral
  rw [hx]
  intro hd
  apply hcop
  have : ((Rat.divInt k x.den).den : ℤ) ∣ (x.den : ℤ) := Rat.den_dvd _ _
  have h3 : (Rat.divInt k x.den).den ∣ x.den := by exact_mod_cast this
  exact hd.trans h3

/-- An integer `c` prime to `p` with `c^m ≢ 1 (mod p)` exists when `p - 1 ∤ m` (a primitive root). -/
lemma exists_pow_ne_one {m : ℕ} (hpm : ¬ p - 1 ∣ m) :
    ∃ c : ℕ, ¬ p ∣ c ∧ ¬ (p : ℤ) ∣ (c : ℤ) ^ m - 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  have hgm : g ^ m ≠ 1 := by
    intro h; exact hpm (hord ▸ orderOf_dvd_of_pow_eq_one h)
  refine ⟨(g : ZMod p).val, ?_, ?_⟩
  · intro hdvd
    have : ((g : ZMod p).val : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    rw [ZMod.natCast_zmod_val] at this
    exact g.ne_zero this
  · intro hdvd
    have h0 : ((((g : ZMod p).val : ℤ) ^ m - 1 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd
    push_cast at h0
    rw [ZMod.natCast_zmod_val, sub_eq_zero] at h0
    exact hgm (Units.ext (by simpa using h0))

/-- The Voronoi congruence for `n = p^N`, divided by `m V_m`: writing `v = v_p(m)`,
`(c^m - 1) B_m / m ≡ c^(m-1) ∑_{j < p^N} j^(m-1) [jc/p^N] (mod p^(N-v))`. -/
lemma voronoi_pModEq {m : ℕ} (hm : Even m) (hm0 : m ≠ 0) (hpm : ¬ p - 1 ∣ m) {c N : ℕ}
    (hc : ¬ p ∣ c) (hN : m.factorization p ≤ N) :
    PModEq p (N - m.factorization p) (((c : ℚ) ^ m - 1) * bernoulli m / m)
      ((c : ℚ) ^ (m - 1) * voronoiSum m c (p ^ N)) := by
  set v := m.factorization p
  set r := m / p ^ v
  have hmr : p ^ v * r = m := Nat.ordProj_mul_ordCompl_eq_self m p
  have hr : ¬ p ∣ r := Nat.not_dvd_ordCompl hp.out hm0
  have hcop : c.Coprime (p ^ N) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_comm).mp ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hc))
  have hV := not_dvd_den_bernoulli hm hpm
  have hvor := voronoi_congruence hm hm0 hcop
  obtain ⟨k, hk⟩ := Int.ModEq.dvd hvor
  set U := (bernoulli m).num
  set V := (bernoulli m).den
  set T := voronoiSum m c (p ^ N)
  have hB : bernoulli m = (U : ℚ) / V := (Rat.num_div_den _).symm
  have hV0 : (V : ℚ) ≠ 0 := by exact_mod_cast (bernoulli m).den_nz
  have hr0 : (r : ℚ) ≠ 0 := by
    have : r ≠ 0 := fun h ↦ hm0 (by rw [← hmr, h, mul_zero])
    exact_mod_cast this
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hm' : (m : ℚ) = (p : ℚ) ^ v * r := by rw [← hmr]; push_cast; ring
  have hkq : (m : ℚ) * (c : ℚ) ^ (m - 1) * V * T - ((c : ℚ) ^ m - 1) * U =
      (p : ℚ) ^ N * k := by
    have := congrArg (fun z : ℤ ↦ (z : ℚ)) hk
    push_cast at this
    linear_combination this
  refine pModEq_iff.mpr ⟨-(k : ℚ) * ((r * V : ℕ) : ℚ)⁻¹, ?_, ?_⟩
  · refine (isPIntegral_intCast k).neg.mul (isPIntegral_natCast_inv ?_)
    intro h
    rcases (Nat.Prime.dvd_mul hp.out).mp h with h | h
    · exact hr h
    · exact hV h
  · have hpN : (p : ℚ) ^ N = (p : ℚ) ^ (N - v) * (p : ℚ) ^ v := by
      rw [← pow_add, Nat.sub_add_cancel hN]
    rw [hB, hm']
    rw [hpN, hm'] at hkq
    push_cast
    field_simp
    linear_combination (-1 : ℚ) * hkq

/-- The terms with `p ∣ j` of the Voronoi sum for `p^N` give `p^(m-1)` times the Voronoi sum for
`p^(N-1)`. -/
lemma voronoiSum_split (m c : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    voronoiSum m c (p ^ N) =
      (∑ j ∈ (Ico 1 (p ^ N)).filter (fun j ↦ ¬ p ∣ j),
          (j : ℤ) ^ (m - 1) * ((j * c / p ^ N : ℕ) : ℤ)) +
        (p : ℤ) ^ (m - 1) * voronoiSum m c (p ^ (N - 1)) := by
  unfold voronoiSum
  rw [← sum_filter_not_add_sum_filter (Ico 1 (p ^ N)) (fun j ↦ p ∣ j)]
  congr 1
  have hpN : p ^ N = p * p ^ (N - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hN]
  have himg : (Ico 1 (p ^ N)).filter (fun j ↦ p ∣ j) =
      (Ico 1 (p ^ (N - 1))).image (fun i ↦ p * i) := by
    ext j
    simp only [mem_filter, mem_Ico, mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨i, rfl⟩⟩
      refine ⟨i, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos i with rfl | h <;> [simp at h1; exact h]
      · rw [hpN] at h2; exact Nat.lt_of_mul_lt_mul_left h2
    · rintro ⟨i, ⟨h1, h2⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, dvd_mul_right _ _⟩
      · exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hp.out.ne_zero (by omega))
      · rw [hpN]; exact Nat.mul_lt_mul_of_pos_left h2 hp.out.pos
  rw [himg, sum_image (fun a _ b _ h ↦ Nat.eq_of_mul_eq_mul_left hp.out.pos h), mul_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  have : p * i * c / p ^ N = i * c / p ^ (N - 1) := by
    rw [hpN, mul_assoc, Nat.mul_div_mul_left _ _ hp.out.pos]
  rw [this]
  push_cast
  ring

/-- `x^a ≡ x^b (mod n)` when `x` is prime to `n` and `a ≡ b (mod φ(n))`. -/
lemma pow_modEq_of_modEq_totient {x n a b : ℕ} (hx : x.Coprime n) (hab : a ≡ b [MOD n.totient]) :
    x ^ a ≡ x ^ b [MOD n] := by
  have key : ∀ t : ℕ, x ^ t ≡ x ^ (t % n.totient) [MOD n] := by
    intro t
    have h1 := Nat.ModEq.pow_totient hx
    conv_lhs => rw [← Nat.div_add_mod t n.totient, pow_add, pow_mul]
    simpa using (h1.pow (t / n.totient)).mul_right (x ^ (t % n.totient))
  have := key a
  rw [hab] at this
  exact this.trans (key b).symm

lemma PModEq.sub {e : ℕ} {x y x' y' : ℚ} (h : PModEq p e x y) (h' : PModEq p e x' y') :
    PModEq p e (x - x') (y - y') := by
  have := h.add (h'.mul_left (-1) (isPIntegral_intCast (-1)))
  simpa [sub_eq_add_neg] using this

lemma PModEq.mul_right {e : ℕ} {x y : ℚ} (c : ℚ) (hc : IsPIntegral p c) (h : PModEq p e x y) :
    PModEq p e (x * c) (y * c) := by
  simpa [mul_comm] using h.mul_left c hc

end Helpers

/-- **Ireland–Rosen, Proposition 15.2.4 (Adams).** If `m ≥ 2` is even and `p - 1 ∤ m`, then
`B_m / m` is `p`-integral. -/
@[kb "irelandrosen1990" "Proposition 15.2.4"]
theorem isPIntegral_bernoulli_div (p : ℕ) [Fact p.Prime] {m : ℕ} (hm : Even m) (hm0 : m ≠ 0)
    (hpm : ¬ p - 1 ∣ m) : IsPIntegral p (bernoulli m / m) := by
  obtain ⟨c, hc, hcm⟩ := exists_pow_ne_one (p := p) hpm
  have h := voronoi_pModEq hm hm0 hpm hc (N := m.factorization p) le_rfl
  rw [Nat.sub_self] at h
  have hY : IsPIntegral p (((c : ℚ) ^ m - 1) * bernoulli m / m) := by
    have h' : IsPIntegral p ((((c : ℚ) ^ m - 1) * bernoulli m / m -
        (c : ℚ) ^ (m - 1) * voronoiSum m c (p ^ m.factorization p))) := by
      simpa [PModEq] using h
    have := h'.add (((isPIntegral_natCast c).pow (m - 1)).mul (isPIntegral_intCast
      (voronoiSum m c (p ^ m.factorization p))))
    simpa using this
  have hc0 : ((c : ℤ) ^ m - 1 : ℤ) ≠ 0 := fun h0 ↦ hcm (by rw [h0]; exact dvd_zero _)
  have hinv := isPIntegral_intCast_inv (p := p) hcm
  have : bernoulli m / m = (((c : ℤ) ^ m - 1 : ℤ) : ℚ)⁻¹ * (((c : ℚ) ^ m - 1) * bernoulli m / m) := by
    have : (((c : ℤ) ^ m - 1 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hc0
    push_cast at this ⊢
    field_simp
  rw [this]
  exact hinv.mul hY

/-- **Ireland–Rosen, Proposition 15.2.4 (Adams), as stated in the book.** If `m ≥ 2` is even,
`p - 1 ∤ m` and `p^l ∣ m`, then `p^l ∣ U_m`. -/
@[kb "irelandrosen1990" "Proposition 15.2.4"]
theorem pow_dvd_num_bernoulli (p : ℕ) [Fact p.Prime] {m l : ℕ} (hm : Even m) (hm0 : m ≠ 0)
    (hpm : ¬ p - 1 ∣ m) (hl : p ^ l ∣ m) : (p : ℤ) ^ l ∣ (bernoulli m).num := by
  obtain ⟨r, hr⟩ := hl
  have h := isPIntegral_bernoulli_div p hm hm0 hpm
  apply pow_dvd_of_isPIntegral_div (p := p)
  have hV0 : ((bernoulli m).den : ℚ) ≠ 0 := by exact_mod_cast (bernoulli m).den_nz
  have hr0 : (r : ℚ) ≠ 0 := by
    have : r ≠ 0 := fun h ↦ hm0 (by rw [hr, h, mul_zero])
    exact_mod_cast this
  have hp0 : ((p : ℚ) ^ l) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have : ((bernoulli m).num : ℚ) / (p : ℚ) ^ l =
      (bernoulli m / m) * ((r : ℚ) * (bernoulli m).den) := by
    rw [← Rat.mul_den_eq_num (bernoulli m), hr]; push_cast; field_simp
  rw [this]
  exact h.mul ((isPIntegral_natCast r).mul (isPIntegral_natCast _))

/-- **Ireland–Rosen, §15.2, Theorem 5 (Kummer congruences).** Let `m, m'` be positive even
integers with `p - 1 ∤ m` and `m' ≡ m (mod φ(p^e))`. Then
`(1 - p^(m'-1)) B_{m'}/m' ≡ (1 - p^(m-1)) B_m/m (mod p^e)`. -/
@[kb "irelandrosen1990" "§15.2, Theorem 5 (Kummer congruences)"]
theorem kummer_congruence (p : ℕ) [Fact p.Prime] {e m m' : ℕ} (he : 1 ≤ e)
    (hm : Even m) (hm0 : m ≠ 0) (hm' : Even m') (hm'0 : m' ≠ 0) (hpm : ¬ p - 1 ∣ m)
    (hmm' : m' ≡ m [MOD (p ^ e).totient]) :
    PModEq p e ((1 - (p : ℚ) ^ (m' - 1)) * bernoulli m' / m')
      ((1 - (p : ℚ) ^ (m - 1)) * bernoulli m / m) := by
  have hp := (Fact.out : p.Prime)
  have htot : p - 1 ∣ (p ^ e).totient := by
    rw [Nat.totient_prime_pow hp (by omega)]; exact dvd_mul_left _ _
  have hmod1 : m' ≡ m [MOD p - 1] := hmm'.of_dvd htot
  have hpm' : ¬ p - 1 ∣ m' := fun h ↦ hpm ((hmod1.dvd_iff dvd_rfl).mp h)
  obtain ⟨c, hc, hcm⟩ := exists_pow_ne_one (p := p) hpm
  set N := e + 1 + m.factorization p + m'.factorization p with hN
  set F := (Ico 1 (p ^ N)).filter (fun j ↦ ¬ p ∣ j) with hF
  -- the Voronoi congruence for `p^N` minus `p^(k-1)` times the one for `p^(N-1)`
  have step : ∀ {k : ℕ}, Even k → k ≠ 0 → ¬ p - 1 ∣ k → k.factorization p + e + 1 ≤ N →
      PModEq p e (((c : ℚ) ^ k - 1) * ((1 - (p : ℚ) ^ (k - 1)) * bernoulli k / k))
        ((c : ℚ) ^ (k - 1) *
          ((∑ j ∈ F, (j : ℤ) ^ (k - 1) * ((j * c / p ^ N : ℕ) : ℤ) : ℤ) : ℚ)) := by
    intro k hk hk0 hpk hkN
    have h1 := (voronoi_pModEq hk hk0 hpk hc (N := N) (by omega)).of_le
      (show e ≤ N - k.factorization p by omega)
    have h2 := ((voronoi_pModEq hk hk0 hpk hc (N := N - 1) (by omega)).of_le
      (show e ≤ N - 1 - k.factorization p by omega)).mul_left ((p : ℚ) ^ (k - 1))
      ((isPIntegral_natCast p).pow _)
    have h3 := h1.sub h2
    rw [voronoiSum_split (p := p) k c (N := N) (by omega)] at h3
    convert h3 using 1
    · ring
    · push_cast; ring
  have hA := step hm hm0 hpm (by omega)
  have hB := step hm' hm'0 hpm' (by omega)
  -- the two sums over `j` prime to `p` agree modulo `p^e`
  have hmm1 : m' - 1 ≡ m - 1 [MOD (p ^ e).totient] := by
    have h2m : 2 ≤ m := by obtain ⟨r, rfl⟩ := hm; omega
    have h2m' : 2 ≤ m' := by obtain ⟨r, rfl⟩ := hm'; omega
    refine Nat.ModEq.add_right_cancel' 1 ?_
    rwa [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)]
  have hpc : ∀ x : ℕ, ¬ p ∣ x → x.Coprime (p ^ e) := fun x hx ↦
    Nat.Coprime.pow_right _ ((Nat.coprime_comm).mp ((Nat.Prime.coprime_iff_not_dvd hp).2 hx))
  have hT : PModEq p e
      ((c : ℚ) ^ (m' - 1) * ((∑ j ∈ F, (j : ℤ) ^ (m' - 1) * ((j * c / p ^ N : ℕ) : ℤ) : ℤ) : ℚ))
      ((c : ℚ) ^ (m - 1) * ((∑ j ∈ F, (j : ℤ) ^ (m - 1) * ((j * c / p ^ N : ℕ) : ℤ) : ℤ) : ℚ)) := by
    have hZ : (c : ℤ) ^ (m' - 1) * (∑ j ∈ F, (j : ℤ) ^ (m' - 1) * ((j * c / p ^ N : ℕ) : ℤ)) ≡
        (c : ℤ) ^ (m - 1) * (∑ j ∈ F, (j : ℤ) ^ (m - 1) * ((j * c / p ^ N : ℕ) : ℤ))
        [ZMOD (p : ℤ) ^ e] := by
      rw [Int.modEq_iff_dvd, mul_sum, mul_sum, ← sum_sub_distrib]
      refine dvd_sum fun j hj ↦ ?_
      have hj : ¬ p ∣ j := (mem_filter.mp hj).2
      have hcop : (c * j).Coprime (p ^ e) := Nat.coprime_mul_iff_left.mpr ⟨hpc c hc, hpc j hj⟩
      have h1 := pow_modEq_of_modEq_totient hcop hmm1
      have h2 : (((c * j) ^ (m' - 1) : ℕ) : ℤ) ≡ (((c * j) ^ (m - 1) : ℕ) : ℤ)
          [ZMOD ((p ^ e : ℕ) : ℤ)] := Int.natCast_modEq_iff.mpr h1
      have h3 := Int.ModEq.dvd h2
      push_cast at h3
      have := dvd_mul_of_dvd_left h3 ((j * c / p ^ N : ℕ) : ℤ)
      convert this using 1
      ring
    have := pModEq_of_intModEq (p := p) hZ
    push_cast at this ⊢
    exact this
  -- `c^(m') ≡ c^m (mod p^e)`
  have hcpow : PModEq p e ((c : ℚ) ^ m' - 1) ((c : ℚ) ^ m - 1) := by
    have h1 := pow_modEq_of_modEq_totient (hpc c hc) hmm'
    have h2 : ((c ^ m' : ℕ) : ℤ) - 1 ≡ ((c ^ m : ℕ) : ℤ) - 1 [ZMOD ((p : ℤ) ^ e)] := by
      have := (Int.natCast_modEq_iff (n := p ^ e)).mpr h1
      push_cast at this ⊢
      exact this.sub_right 1
    have := pModEq_of_intModEq (p := p) h2
    push_cast at this
    exact this
  have hX' : IsPIntegral p ((1 - (p : ℚ) ^ (m' - 1)) * bernoulli m' / m') := by
    rw [mul_div_assoc]
    exact ((isPIntegral_one).sub ((isPIntegral_natCast p).pow _)).mul
      (isPIntegral_bernoulli_div p hm' hm'0 hpm')
  have hchain : PModEq p e (((c : ℚ) ^ m - 1) * ((1 - (p : ℚ) ^ (m' - 1)) * bernoulli m' / m'))
      (((c : ℚ) ^ m - 1) * ((1 - (p : ℚ) ^ (m - 1)) * bernoulli m / m)) :=
    (hcpow.mul_right _ hX').symm.trans (hB.trans (hT.trans hA.symm))
  have hc0 : ((c : ℤ) ^ m - 1 : ℤ) ≠ 0 := fun h0 ↦ hcm (by rw [h0]; exact dvd_zero _)
  have hc0' : ((c : ℚ) ^ m - 1) ≠ 0 := by exact_mod_cast hc0
  have hinv := isPIntegral_intCast_inv (p := p) hcm
  have := hchain.mul_left _ hinv
  push_cast at this
  rwa [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hc0', one_mul, one_mul] at this

/-- **Ireland–Rosen, §15.2, Theorem 5 (Kummer congruences), `e = 1`.** If `m, m'` are positive even
integers with `p - 1 ∤ m` and `m' ≡ m (mod p - 1)`, then `B_{m'}/m' ≡ B_m/m (mod p)`. -/
@[kb "irelandrosen1990" "§15.2, Theorem 5 (Kummer congruences)"]
theorem kummer_congruence_mod_p (p : ℕ) [Fact p.Prime] {m m' : ℕ}
    (hm : Even m) (hm0 : m ≠ 0) (hm' : Even m') (hm'0 : m' ≠ 0) (hpm : ¬ p - 1 ∣ m)
    (hmm' : m' ≡ m [MOD p - 1]) :
    PModEq p 1 (bernoulli m' / m') (bernoulli m / m) := by
  have hp := (Fact.out : p.Prime)
  have h := kummer_congruence p (e := 1) le_rfl hm hm0 hm' hm'0 hpm
    (by rwa [pow_one, Nat.totient_prime hp])
  have hpm' : ¬ p - 1 ∣ m' := fun h ↦ hpm ((hmm'.dvd_iff dvd_rfl).mp h)
  have aux : ∀ k, Even k → k ≠ 0 → ¬ p - 1 ∣ k →
      PModEq p 1 ((1 - (p : ℚ) ^ (k - 1)) * bernoulli k / k) (bernoulli k / k) := by
    intro k hk hk0 hpk
    have hI := isPIntegral_bernoulli_div p hk hk0 hpk
    have hk1 : k - 1 = (k - 2) + 1 := by obtain ⟨r, rfl⟩ := hk; omega
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hk0' : (k : ℚ) ≠ 0 := by exact_mod_cast hk0
    unfold PModEq
    have : ((1 - (p : ℚ) ^ (k - 1)) * bernoulli k / k - bernoulli k / k) / (p : ℚ) ^ 1 =
        -((p : ℚ) ^ (k - 2) * (bernoulli k / k)) := by
      rw [hk1, pow_succ]; field_simp; ring
    rw [this]
    exact (((isPIntegral_natCast p).pow _).mul hI).neg
  exact ((aux m' hm' hm'0 hpm').symm.trans h).trans (aux m hm hm0 hpm)

/-- **Ireland–Rosen, §15.2, Theorem 6 (Carlitz).** There are infinitely many irregular primes. -/
@[kb "irelandrosen1990" "§15.2, Theorem 6 (Carlitz)"]
theorem infinite_setOf_isIrregularPrime : {p : ℕ | IsIrregularPrime p}.Infinite := by
  intro hfin
  set F := hfin.toFinset with hF
  set M := ∏ q ∈ F, (q - 1) with hM
  have hFq : ∀ q ∈ F, 3 ≤ q := by
    intro q hq
    obtain ⟨hqp, hq2, -⟩ := hfin.mem_toFinset.mp hq
    have := hqp.two_le; omega
  have hM0 : 0 < M := Finset.prod_pos fun q hq ↦ by have := hFq q hq; omega
  have hdvdM : ∀ q ∈ F, q - 1 ∣ M := fun q hq ↦ Finset.dvd_prod_of_mem _ hq
  -- choose `j = M (k + 1)` with `|B_{2j}/(2j)| > 1` (Proposition 15.1.1 (c))
  have ht : Filter.Tendsto (fun k : ℕ ↦ M * (k + 1)) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_mono (fun k ↦ ?_) (Filter.tendsto_add_atTop_nat 1)
    nlinarith
  obtain ⟨k, hk⟩ :=
    ((tendsto_abs_bernoulli_div.comp ht).eventually (Filter.eventually_gt_atTop 1)).exists
  set j := M * (k + 1) with hj
  have hj0 : 0 < j := by positivity
  set x : ℚ := bernoulli (2 * j) / ((2 * j : ℕ) : ℚ) with hx
  have hx1 : 1 < |x| := by
    have h' : (((|x| : ℚ)) : ℝ) = |(bernoulli (2 * j) : ℝ) / (2 * (j : ℝ))| := by
      rw [hx]; push_cast; rfl
    have : (1 : ℝ) < ((|x| : ℚ) : ℝ) := by rw [h']; exact hk
    exact_mod_cast this
  -- a prime `p` divides the numerator of `x`
  have hnum : x.num.natAbs ≠ 1 := by
    intro h1
    have hden : (1 : ℚ) ≤ x.den := by exact_mod_cast x.den_pos
    have habs : |(x.num : ℚ)| = 1 := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs, h1]; simp
    have : |x| ≤ 1 := by
      rw [← Rat.num_div_den x, abs_div, habs, Nat.abs_cast]
      exact div_le_one_of_le₀ hden (by positivity)
    linarith
  obtain ⟨p, hp, hpx⟩ := Nat.exists_prime_and_dvd hnum
  have : Fact p.Prime := ⟨hp⟩
  have hpnum : (p : ℤ) ∣ x.num := Int.natCast_dvd.mpr hpx
  have hpden : ¬ p ∣ x.den := by
    intro hd
    have h1 : (p : ℤ) ∣ (x.den : ℤ) := by exact_mod_cast hd
    have h2 : IsCoprime x.num (x.den : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]; exact_mod_cast x.reduced
    have := h2.isUnit_of_dvd' hpnum h1
    rw [Int.isUnit_iff] at this
    rcases this with h | h <;> [exact hp.ne_one (by exact_mod_cast h); omega]
  -- `p - 1 ∤ 2j`, by von Staudt–Clausen
  have hpj : ¬ p - 1 ∣ 2 * j := by
    intro h
    have h1 := Bernoulli.dvd_den_bernoulli (p := p) hj0 h
    have h2j : ((2 * j : ℕ) : ℚ) ≠ 0 := by positivity
    have hB : bernoulli (2 * j) = x * ((2 * j : ℕ) : ℚ) := by rw [hx]; field_simp
    have h2 : (bernoulli (2 * j)).den ∣ x.den := by
      have := Rat.mul_den_dvd x ((2 * j : ℕ) : ℚ)
      rw [Rat.den_natCast, mul_one] at this
      rwa [hB]
    exact hpden (h1.trans h2)
  have hp5 := five_le_of_not_dvd (p := p) (even_two_mul j) hpj
  have hpF : p ∉ F := fun h ↦
    hpj ((hdvdM p h).trans ((Dvd.intro _ rfl : M ∣ j).trans (dvd_mul_left j 2)))
  -- `m' ≡ 2j (mod p - 1)` with `2 ≤ m' ≤ p - 3` even
  set m' := 2 * j % (p - 1) with hm'
  have hp1 : 2 ∣ p - 1 := even_iff_two_dvd.mp (hp.even_sub_one (by omega))
  have hm'2 : m' % 2 = 0 := by
    rw [hm', Nat.mod_mod_of_dvd _ hp1]; omega
  have hm'even : Even m' := Nat.even_iff.mpr hm'2
  have hm'0 : m' ≠ 0 := fun h ↦ hpj (Nat.dvd_of_mod_eq_zero h)
  have hm'lt : m' < p - 1 := Nat.mod_lt _ (by omega)
  have hmod : m' ≡ 2 * j [MOD p - 1] := Nat.mod_modEq _ _
  have hK := kummer_congruence_mod_p p (even_two_mul j) (by omega) hm'even hm'0 hpj hmod
  have hx0 : PModEq p 1 x 0 := by
    unfold PModEq; simpa using isPIntegral_div_of_dvd_num hpnum
  have h0 : PModEq p 1 (bernoulli m' / m') 0 := hK.trans hx0
  have h1 : IsPIntegral p (((bernoulli m').num : ℚ) / (p : ℚ) ^ 1) := by
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hm0' : (m' : ℚ) ≠ 0 := by exact_mod_cast hm'0
    have : ((bernoulli m').num : ℚ) / (p : ℚ) ^ 1 =
        ((bernoulli m' / m' - 0) / (p : ℚ) ^ 1) * ((m' : ℚ) * (bernoulli m').den) := by
      rw [sub_zero, ← Rat.mul_den_eq_num]; field_simp
    rw [this]
    exact h0.mul ((isPIntegral_natCast _).mul (isPIntegral_natCast _))
  have h2 := pow_dvd_of_isPIntegral_div h1
  rw [pow_one] at h2
  obtain ⟨t, ht⟩ := hm'even
  obtain ⟨u, hu⟩ := hp1
  refine hpF (hfin.mem_toFinset.mpr ⟨hp, by omega, t, by omega, by omega, ?_⟩)
  rw [show 2 * t = m' by omega]
  exact h2

end NTKB.IrelandRosen
