/-
Ireland–Rosen, Chapter 15, §15.2: h(-p) ≡ -2 B_{(p+1)/2} (mod p) for the class number of the
imaginary quadratic field of discriminant -p.
-/
import NTKB.IrelandRosen.R4.Bernoulli.ClassNumber
import NTKB.Analytic.Davenport.ClassNumber.Finite

/-!
# `h(-p) ≡ -2 B_{(p+1)/2} (mod p)` for the class number of `ℚ(√-p)`

Combines the unconditional congruence `jacobiClassNumber_pModEq` with Jacobi's formula
`NTKB.Davenport.classNumber_eq_jacobi` (Davenport §6 (19)), which is proved from the
named inputs `QuadraticFieldDiscriminants` and `QuadraticIdealCount`.
Ireland and Rosen cite the class number formula (from Borevich–Shafarevich) rather than prove it.
-/

namespace NTKB.IrelandRosen

open NumberField Module

/-- **Ireland–Rosen, §15.2: `h(-p) ≡ -2 B_{(p+1)/2} (mod p)`.** For a prime `p ≡ 3 (mod 4)`,
`p > 3`, and the quadratic field `K` of discriminant `-p`, the class number of `K` is congruent to
`-2 B_{(p+1)/2}` modulo `p`; conditional on the named inputs of Jacobi's formula. -/
@[kb "irelandrosen1990" "§15.2, h(-p) ≡ -2 B_{(p+1)/2} (mod p)"]
theorem classNumber_pModEq_bernoulli (hF : NTKB.Davenport.QuadraticFieldDiscriminants)
    (hI : NTKB.Davenport.QuadraticIdealCount) {K : Type} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) (hp3 : 3 < p) (hK : finrank ℚ K = 2)
    (hD : discr K = -p) :
    PModEq p 1 (classNumber K) (-2 * bernoulli ((p + 1) / 2)) := by
  have h := NTKB.Davenport.classNumber_eq_jacobi hF hI hp hp3 hK hD
  have hq : ((classNumber K : ℕ) : ℚ) = jacobiClassNumber p := by
    have h' := congrArg (Int.cast : ℤ → ℚ) h
    push_cast at h'
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    unfold jacobiClassNumber
    field_simp
    linarith
  rw [hq]
  exact jacobiClassNumber_pModEq p hp hp3

end NTKB.IrelandRosen
