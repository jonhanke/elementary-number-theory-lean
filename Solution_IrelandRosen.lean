/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import NTKB.IrelandRosen.R2.HasseDavenport
import NTKB.IrelandRosen.R2.LastEntry
import NTKB.IrelandRosen.R3.Reciprocity
import NTKB.IrelandRosen.R3.Legendre
import NTKB.IrelandRosen.R3.SophieGermain

/-!
# Proofs of the Ireland–Rosen headline statements

The statements of `Challenge_IrelandRosen.lean`, proved by the library theorems. `lake comparator` checks that each
statement here is exactly the one in `Challenge_IrelandRosen.lean`.
-/

namespace NTKB.Headlines.IrelandRosen

open NTKB.IrelandRosen

theorem hasse_davenport {F : Type*} [Field F] [Fintype F] {E : Type*} [Field E] [Fintype E] [Algebra F E]
    {R : Type*} [CommRing R] [IsDomain R] (χ : MulChar F R) {ψ : AddChar F R} (hψ : ψ ≠ 1) :
    (-gaussSum χ ψ) ^ Module.finrank F E = -gaussSum (liftNorm (E := E) χ) (liftTrace ψ) :=
  NTKB.IrelandRosen.hasse_davenport χ hψ

theorem biquadratic_reciprocity {π μ : GaussianInt} (hπ : Gaussian.IsPrimary π) (hμ : Gaussian.IsPrimary μ)
    (hcop : IsCoprime π μ) :
    Gaussian.quarticSymbol π μ = Gaussian.quarticSymbol μ π *
      (((Int.negOnePow (((μ.norm - 1) / 4) * ((π.norm - 1) / 4)) : ℤˣ) : ℤ) : GaussianInt) :=
  Gaussian.quarticSymbol_reciprocity hπ hμ hcop

theorem gauss_last_entry {p : ℕ} [Fact p.Prime] (hp : p % 4 = 1) :
    ∃ a b : ℤ, (p : ℤ) = a ^ 2 + b ^ 2 ∧ Odd a ∧ Even b ∧ (4 ∣ b → a ≡ 1 [ZMOD 4]) ∧
      (¬4 ∣ b → a ≡ -1 [ZMOD 4]) ∧
      (∀ a' b' : ℤ, (p : ℤ) = a' ^ 2 + b' ^ 2 → Odd a' → Even b' →
        (4 ∣ b' → a' ≡ 1 [ZMOD 4]) → (¬4 ∣ b' → a' ≡ -1 [ZMOD 4]) → a' = a) ∧
      (numLastEntry (ZMod p) : ℤ) = p - 1 - 2 * a :=
  NTKB.IrelandRosen.gauss_last_entry hp

theorem legendre {a b c : ℤ} (hsa : Squarefree a) (hsb : Squarefree b) (hsc : Squarefree c)
    (hab : IsCoprime a b) (hac : IsCoprime a c) (hbc : IsCoprime b c)
    (hpos : ¬ (0 < a ∧ 0 < b ∧ 0 < c)) (hneg : ¬ (a < 0 ∧ b < 0 ∧ c < 0)) :
    Legendre.HasSol a b c ↔
      Legendre.SqMod (-(a * b)) c ∧ Legendre.SqMod (-(a * c)) b ∧ Legendre.SqMod (-(b * c)) a :=
  Legendre.legendre hsa hsb hsc hab hac hbc hpos hneg

theorem sophie_germain {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : (2 * p + 1).Prime) :
    ¬ ∃ x y z : ℤ, x ^ p + y ^ p + z ^ p = 0 ∧ ¬ (p : ℤ) ∣ x * y * z :=
  SophieGermain.sophie_germain hp hp2 hq

end NTKB.Headlines.IrelandRosen
