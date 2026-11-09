/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.UniformSpace.Cauchy
import Aesop.BuiltinRules
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Tactic.PNatToNat
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Separation.CompletelyRegular
import Std.Tactic.BVDecide.Normalize.Prop
import NTKB.Attr

/-!
# Hardy–Wright, § 16.5: inversion formulae over real arguments

* Theorem 268: if `G(x) = ∑_{n ≤ x} F(x/n)` for all `x > 0`, then `F(x) = ∑_{n ≤ x} μ(n) G(x/n)`.
* Theorem 269: the converse.
* Theorem 270: `g(x) = ∑_{m ≥ 1} f(mx)` if and only if `f(x) = ∑_{n ≥ 1} μ(n) g(nx)`, under absolute
  convergence of the double series `∑_{m,n} |f(mnx)|` (for the direction `⇒`, as in the book) and of
  `∑_{m,n} |g(mnx)|` (for the direction `⇐`). Some such condition is needed for `⇐`: the book only
  says that "some care is required about convergence".

All proofs are those of the book: rearrange the double sum according to `k = mn` and use
Theorem 263, `∑_{d ∣ k} μ(d) = [k = 1]`.

The functions take values in any additive group (Theorems 268 and 269) or any complete normed
additive group (Theorem 270), with `μ(n)` acting by integer multiplication.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius

namespace NTKB.HardyWright

/-- Theorem 263 in divisor-sum form: `∑_{d ∣ k} μ(d) = 1` if `k = 1` and `0` otherwise. -/
theorem sum_divisors_moebius (k : ℕ) : ∑ d ∈ k.divisors, μ d = if k = 1 then 1 else 0 := by
  have := congrArg (· k) moebius_mul_coe_zeta
  simp only [coe_mul_zeta_apply] at this
  exact this

/-- Rearranging `∑_{n ≤ N} ∑_{m ≤ N/n} h(n, m)` according to `k = nm`. -/
theorem sum_Ioc_sum_Ioc_div_eq {M : Type*} [AddCommMonoid M] (h : ℕ → ℕ → M) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, ∑ m ∈ Ioc 0 (N / n), h n m =
      ∑ k ∈ Ioc 0 N, ∑ x ∈ k.divisorsAntidiagonal, h x.1 x.2 := by
  symm
  trans ∑ k ∈ Ioc 0 N, ∑ x ∈ Ioc 0 N ×ˢ Ioc 0 N with x.1 * x.2 = k, h x.1 x.2
  · refine sum_congr rfl fun k hk ↦ ?_
    simp only [mem_Ioc] at hk
    rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le hk.1.ne' hk.2]
  rw [sum_comm' (t' := (Ioc 0 N ×ˢ Ioc 0 N).filter fun x => x.1 * x.2 ≤ N)
    (s' := fun x => {x.1 * x.2})]
  · rw [sum_filter, sum_product]
    refine sum_congr rfl fun n hn => ?_
    simp only [sum_singleton]
    rw [← sum_filter]
    apply sum_congr _ fun _ _ => rfl
    ext m
    simp only [mem_filter, mem_Ioc] at hn ⊢
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, (Nat.le_div_iff_mul_le hn.1).mpr (by rwa [mul_comm])⟩
    · rintro ⟨h1, h2⟩
      have := (Nat.le_div_iff_mul_le hn.1).mp h2
      refine ⟨⟨h1, ?_⟩, by rwa [mul_comm]⟩
      calc m ≤ m * n := Nat.le_mul_of_pos_right m hn.1
        _ ≤ N := this
  · intro x k
    simp only [mem_filter, mem_product, mem_Ioc, mem_singleton]
    constructor
    · rintro ⟨⟨_, h2⟩, h3, rfl⟩
      exact ⟨rfl, h3, h2⟩
    · rintro ⟨rfl, h3, h2⟩
      exact ⟨⟨Nat.mul_pos h3.1.1 h3.2.1, h2⟩, h3, rfl⟩

/-- The sum over the divisor pairs of `k` of `μ(d) • a`, which is `a` if `k = 1` and `0`
otherwise. -/
private lemma sum_antidiagonal_moebius_smul {E : Type*} [AddCommGroup E] (k : ℕ) (a : E) :
    ∑ x ∈ k.divisorsAntidiagonal, μ x.1 • a = if k = 1 then a else 0 := by
  rw [← Finset.sum_smul, Nat.sum_divisorsAntidiagonal (fun d _ => μ d), sum_divisors_moebius]
  split_ifs <;> simp

variable {E : Type*} [AddCommGroup E]

/-- The common rearrangement behind Theorems 268 and 269: for `x ≥ 1`,
`∑_{n ≤ x} μ(n) ∑_{m ≤ x/n} H(x/(nm)) = H(x)`. -/
private lemma sum_moebius_sum_floor {H : ℝ → E} {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, ∑ m ∈ Ioc 0 (⌊x⌋₊ / n), μ n • H (x / ↑(n * m)) = H x := by
  rw [sum_Ioc_sum_Ioc_div_eq (fun n m => μ n • H (x / ↑(n * m)))]
  have h2 : ∀ k ∈ Ioc 0 ⌊x⌋₊, ∑ y ∈ k.divisorsAntidiagonal, μ y.1 • H (x / ↑(y.1 * y.2)) =
      if k = 1 then H x else 0 := by
    intro k _
    rw [sum_congr rfl fun y hy => by rw [(Nat.mem_divisorsAntidiagonal.mp hy).1],
      sum_antidiagonal_moebius_smul]
    split_ifs with h <;> simp [h]
  have h1 : 1 ∈ Ioc 0 ⌊x⌋₊ := by
    simp only [mem_Ioc, zero_lt_one, true_and]
    exact Nat.one_le_floor_iff x |>.mpr hx
  rw [sum_congr rfl h2, sum_ite_eq']
  simp [h1]

/-- **Theorem 268** (Hardy–Wright). If `G(x) = ∑_{n=1}^{[x]} F(x/n)` for all positive `x`, then
`F(x) = ∑_{n=1}^{[x]} μ(n) G(x/n)`.

The conclusion is stated for `x ≥ 1`, which is where the book's proof applies (it uses
`1 ≤ [x]`): for `0 < x < 1` the right-hand side is an empty sum, and the hypothesis says nothing
about `F(x)` there. -/
@[kb "hardywright2008" "Thm 268, p. 326"]
theorem moebius_inversion_floor {F G : ℝ → E}
    (hG : ∀ x > 0, G x = ∑ n ∈ Ioc 0 ⌊x⌋₊, F (x / n)) :
    ∀ x ≥ 1, F x = ∑ n ∈ Ioc 0 ⌊x⌋₊, μ n • G (x / n) := by
  intro x hx
  have h1 : ∀ n ∈ Ioc 0 ⌊x⌋₊, μ n • G (x / n) =
      ∑ m ∈ Ioc 0 (⌊x⌋₊ / n), μ n • F (x / ↑(n * m)) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by simp only [mem_Ioc] at hn; exact_mod_cast hn.1
    rw [hG _ (div_pos (by linarith) hn0), Nat.floor_div_natCast, Finset.smul_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [div_div, Nat.cast_mul]
  rw [sum_congr rfl h1, sum_moebius_sum_floor hx]

/-- **Theorem 269** (Hardy–Wright). Conversely, if `F(x) = ∑_{n=1}^{[x]} μ(n) G(x/n)` for all
positive `x`, then `G(x) = ∑_{n=1}^{[x]} F(x/n)` (for `x ≥ 1`, as in Theorem 268). -/
@[kb "hardywright2008" "Thm 269, p. 326"]
theorem moebius_inversion_floor_converse {F G : ℝ → E}
    (hF : ∀ x > 0, F x = ∑ n ∈ Ioc 0 ⌊x⌋₊, μ n • G (x / n)) :
    ∀ x ≥ 1, G x = ∑ n ∈ Ioc 0 ⌊x⌋₊, F (x / n) := by
  intro x hx
  have h1 : ∀ m ∈ Ioc 0 ⌊x⌋₊, F (x / m) =
      ∑ n ∈ Ioc 0 (⌊x⌋₊ / m), μ n • G (x / ↑(m * n)) := by
    intro m hm
    have hm0 : (0 : ℝ) < m := by simp only [mem_Ioc] at hm; exact_mod_cast hm.1
    rw [hF _ (div_pos (by linarith) hm0), Nat.floor_div_natCast]
    refine sum_congr rfl fun n _ => ?_
    rw [div_div, Nat.cast_mul]
  rw [sum_congr rfl h1]
  -- swap the roles of the two indices and rearrange
  rw [sum_Ioc_sum_Ioc_div_eq (fun m n => μ n • G (x / ↑(m * n)))]
  have h2 : ∀ k ∈ Ioc 0 ⌊x⌋₊, ∑ y ∈ k.divisorsAntidiagonal, μ y.2 • G (x / ↑(y.1 * y.2)) =
      ∑ y ∈ k.divisorsAntidiagonal, μ y.1 • G (x / ↑(y.1 * y.2)) := by
    intro k _
    rw [← Nat.map_swap_divisorsAntidiagonal, Finset.sum_map]
    simp [mul_comm]
  rw [sum_congr rfl h2, ← sum_Ioc_sum_Ioc_div_eq (fun n m => μ n • G (x / ↑(n * m))),
    sum_moebius_sum_floor hx]

/-- Rearranging an absolutely convergent double series `∑_{a,b ≥ 1} H(a, b)` according to the
product `k = ab`. -/
theorem tsum_pnat_prod_eq_tsum_divisorsAntidiagonal {E : Type*} [NormedAddCommGroup E]
    [CompleteSpace E] (H : ℕ → ℕ → E) (hH : Summable fun c : ℕ+ × ℕ+ => H c.1 c.2) :
    ∑' c : ℕ+ × ℕ+, H c.1 c.2 = ∑' k : ℕ+, ∑ y ∈ (k : ℕ).divisorsAntidiagonal, H y.1 y.2 := by
  have hs : Summable fun c : (Σ k : ℕ+, (k : ℕ).divisorsAntidiagonal) =>
      H (sigmaAntidiagonalEquivProd c).1 (sigmaAntidiagonalEquivProd c).2 :=
    (sigmaAntidiagonalEquivProd.summable_iff (f := fun c : ℕ+ × ℕ+ => H c.1 c.2)).mpr hH
  rw [← sigmaAntidiagonalEquivProd.tsum_eq (fun c : ℕ+ × ℕ+ => H c.1 c.2), hs.tsum_sigma]
  refine tsum_congr fun k => ?_
  rw [tsum_fintype, ← (k : ℕ).divisorsAntidiagonal.sum_attach (fun y => H y.1 y.2)]
  rfl

section Series

variable {F : Type*} [NormedAddCommGroup F] [CompleteSpace F]

private lemma summable_smul_of_summable_norm {φ : ℕ+ × ℕ+ → F} (z : ℕ+ × ℕ+ → ℤ)
    (hz : ∀ c, |z c| ≤ 1) (hφ : Summable fun c => ‖φ c‖) : Summable fun c => z c • φ c := by
  refine Summable.of_norm_bounded hφ fun c => ?_
  calc ‖z c • φ c‖ ≤ ‖z c‖ * ‖φ c‖ := norm_zsmul_le _ _
    _ ≤ 1 * ‖φ c‖ := by
        gcongr
        rw [Int.norm_eq_abs]
        exact_mod_cast hz c
    _ = ‖φ c‖ := one_mul _

private lemma abs_moebius_le_one (n : ℕ) : |μ n| ≤ 1 := by
  rw [abs_moebius]; split_ifs <;> norm_num

/-- **Theorem 270**, direction `⇒` (Hardy–Wright). If `g(x) = ∑_{m=1}^∞ f(mx)` for all positive `x`,
and the double series `∑_{m,n} |f(mnx)|` converges for every positive `x` (the sufficient condition
given in the book), then `f(x) = ∑_{n=1}^∞ μ(n) g(nx)`. -/
@[kb "hardywright2008" "Thm 270, p. 326"]
theorem moebius_inversion_tsum {f g : ℝ → F}
    (hg : ∀ x > 0, g x = ∑' m : ℕ+, f ((m : ℕ) * x))
    (hf : ∀ x > 0, Summable fun c : ℕ+ × ℕ+ => ‖f (((c.1 : ℕ) * (c.2 : ℕ) : ℕ) * x)‖) :
    ∀ x > 0, f x = ∑' n : ℕ+, μ n • g ((n : ℕ) * x) := by
  intro x hx
  set H : ℕ → ℕ → F := fun a b => μ a • f (((a * b : ℕ) : ℝ) * x) with hH
  have hsum : Summable fun c : ℕ+ × ℕ+ => H c.1 c.2 :=
    summable_smul_of_summable_norm (fun c => μ c.1) (fun c => abs_moebius_le_one _) (hf x hx)
  have h1 : ∀ n : ℕ+, μ n • g ((n : ℕ) * x) = ∑' m : ℕ+, H n m := by
    intro n
    have hn : (0 : ℝ) < (n : ℕ) := by exact_mod_cast n.pos
    rw [hg _ (mul_pos hn hx)]
    have hs : Summable fun m : ℕ+ => f (((n * m : ℕ) : ℝ) * x) :=
      (((hf x hx).prod_factor n).of_norm)
    have he : ∑' m : ℕ+, f ((m : ℕ) * ((n : ℕ) * x)) = ∑' m : ℕ+, f (((n * m : ℕ) : ℝ) * x) :=
      tsum_congr fun m => by congr 1; push_cast; ring
    rw [he, ← hs.tsum_const_smul]
  rw [tsum_congr h1, ← hsum.tsum_prod, tsum_pnat_prod_eq_tsum_divisorsAntidiagonal H hsum]
  have h2 : ∀ k : ℕ+, ∑ y ∈ (k : ℕ).divisorsAntidiagonal, H y.1 y.2 =
      if k = 1 then f x else 0 := by
    intro k
    simp only [hH]
    rw [sum_congr rfl fun y hy => by rw [(Nat.mem_divisorsAntidiagonal.mp hy).1],
      sum_antidiagonal_moebius_smul]
    by_cases hk : k = 1
    · subst hk; simp
    · have : (k : ℕ) ≠ 1 := fun h => hk (PNat.coe_eq_one_iff.mp h)
      simp [hk, this]
  rw [tsum_congr h2, tsum_ite_eq]

/-- **Theorem 270**, direction `⇐` (Hardy–Wright). If `f(x) = ∑_{n=1}^∞ μ(n) g(nx)` for all positive
`x`, and the double series `∑_{m,n} |g(mnx)|` converges for every positive `x`, then
`g(x) = ∑_{m=1}^∞ f(mx)`. -/
@[kb "hardywright2008" "Thm 270, p. 326"]
theorem moebius_inversion_tsum_converse {f g : ℝ → F}
    (hf : ∀ x > 0, f x = ∑' n : ℕ+, μ n • g ((n : ℕ) * x))
    (hg : ∀ x > 0, Summable fun c : ℕ+ × ℕ+ => ‖g (((c.1 : ℕ) * (c.2 : ℕ) : ℕ) * x)‖) :
    ∀ x > 0, g x = ∑' m : ℕ+, f ((m : ℕ) * x) := by
  intro x hx
  set H : ℕ → ℕ → F := fun a b => μ b • g (((a * b : ℕ) : ℝ) * x) with hH
  have hsum : Summable fun c : ℕ+ × ℕ+ => H c.1 c.2 :=
    summable_smul_of_summable_norm (fun c => μ c.2) (fun c => abs_moebius_le_one _) (hg x hx)
  have h1 : ∀ m : ℕ+, f ((m : ℕ) * x) = ∑' n : ℕ+, H m n := by
    intro m
    have hm : (0 : ℝ) < (m : ℕ) := by exact_mod_cast m.pos
    rw [hf _ (mul_pos hm hx)]
    refine tsum_congr fun n => ?_
    simp only [hH]
    congr 2
    push_cast; ring
  rw [tsum_congr h1, ← hsum.tsum_prod, tsum_pnat_prod_eq_tsum_divisorsAntidiagonal H hsum]
  have h2 : ∀ k : ℕ+, ∑ y ∈ (k : ℕ).divisorsAntidiagonal, H y.1 y.2 =
      if k = 1 then g x else 0 := by
    intro k
    simp only [hH]
    rw [sum_congr rfl fun y hy => by rw [(Nat.mem_divisorsAntidiagonal.mp hy).1],
      ← Finset.sum_smul, Nat.sum_divisorsAntidiagonal' (fun _ d => μ d), sum_divisors_moebius]
    by_cases hk : k = 1
    · subst hk; simp
    · have : (k : ℕ) ≠ 1 := fun h => hk (PNat.coe_eq_one_iff.mp h)
      simp [hk, this]
  rw [tsum_congr h2, tsum_ite_eq]

/-- **Theorem 270** (Hardy–Wright), as an equivalence: under absolute convergence of
`∑_{m,n} |f(mnx)|` and of `∑_{m,n} |g(mnx)|` for every positive `x`,
`g(x) = ∑_{m=1}^∞ f(mx)` for all `x > 0` if and only if `f(x) = ∑_{n=1}^∞ μ(n) g(nx)` for all
`x > 0`. -/
@[kb "hardywright2008" "Thm 270, p. 326"]
theorem moebius_inversion_tsum_iff {f g : ℝ → F}
    (hf : ∀ x > 0, Summable fun c : ℕ+ × ℕ+ => ‖f (((c.1 : ℕ) * (c.2 : ℕ) : ℕ) * x)‖)
    (hg : ∀ x > 0, Summable fun c : ℕ+ × ℕ+ => ‖g (((c.1 : ℕ) * (c.2 : ℕ) : ℕ) * x)‖) :
    (∀ x > 0, g x = ∑' m : ℕ+, f ((m : ℕ) * x)) ↔
      ∀ x > 0, f x = ∑' n : ℕ+, μ n • g ((n : ℕ) * x) :=
  ⟨fun h => moebius_inversion_tsum h hf, fun h => moebius_inversion_tsum_converse h hg⟩

end Series

end NTKB.HardyWright
