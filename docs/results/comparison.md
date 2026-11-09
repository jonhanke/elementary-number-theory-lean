# Comparison with Mathlib, Tau Ceti and PrimeNumberTheoremAnd

For each headline of this release, what the three libraries closest to it already have, and what this library adds.
Libraries searched (source trees of 2026-11-07 and 2026-11-08): Mathlib master `df6966d` (this library is built on
Mathlib `1b1ccf4`, an earlier commit), Tau Ceti main `d2083f0f`, PrimeNumberTheoremAnd `127b50e`. A result is a
headline only if none of the three has it, or if the form here is stronger; the related results are cited. The
searches were by name and by content (statements read); "not found" means that no declaration of that content was
found, not a proof of absence.

## Headlines

| headline (Lean, namespace `NTKB.Headlines`) | Mathlib | Tau Ceti | PrimeNumberTheoremAnd |
|---|---|---|---|
| `HardyWright.complex_euclidean_quadratic_fields` (Theorem 246) | the Euclidean algorithm of `ℤ[i]` (`GaussianInt.natAbs_norm_mod_lt`); `ℤ[ζ₃]` is a principal ideal domain (`IsCyclotomicExtension.Rat.three_pid`) | not found | — |
| `HardyWright.cube_add_cube_eq_three_mul_cube` (Theorem 232) | Fermat's last theorem for exponent 3 (`fermatLastTheoremThree`), whose general form `a³ + b³ = u c³` in `ℤ[ζ₃]` does not give this equation | not found | — |
| `HardyWright.jacobi_triple_product` (Theorem 352) | Euler's pentagonal number theorem (`eulerFunction_eq_tsum_pentagonal`); Jacobi's theta function as a series (`jacobiTheta`) | the theta product `qTheta` with its functional equations (`qTheta_eq_mul_tprod_mul_tprod`), not the series expansion; its Tate-curve file says it neither uses nor proves the identity | — |
| `HardyWright.ramanujan_five`, `ramanujan_seven` (Theorems 359, 360) | partitions (`Nat.Partition`), Euler's generating functions; no congruence | not found | not found (its "Ramanujan" files are about Ramanujan's prime inequality) |
| `HardyWright.rogers_ramanujan_one`, `rogers_ramanujan_two` (Theorems 362, 363) | not found | not found | — |
| `HardyWright.jacobi_four_squares` (Theorem 386) | Lagrange's four-square theorem (`Nat.sum_four_squares`), Euler's identity | Euler's identity for quadratic maps; no count | — |
| `IrelandRosen.hasse_davenport` (Chapter 11, § 3) | Gauss sums, `gaussSum_sq`, `gaussSum_mul_gaussSum_eq_card`, Jacobi sums | Jacobi sums of cubic and quartic characters (`gaussSum_pow_three_eq_card_mul_jacobiSum`); not the relation | — |
| `IrelandRosen.biquadratic_reciprocity` (Chapter 9, § 9) | quadratic reciprocity | cubic reciprocity (`IsPrimaryEisenstein.cubic_reciprocity`); the quartic residue symbol of `ℤ[i]` with its supplementary laws (`IsPrimaryGaussian.powerResidueSymbolIdeal_mk_toInteger`, `powerResidueSymbolIdeal_intCast_four`); not this law | — |
| `IrelandRosen.gauss_last_entry` (Chapter 11, § 5) | not found | not found | — |
| `IrelandRosen.legendre` (Proposition 17.3.1) | not found | isotropy of quadratic forms over number fields place by place (`NumberTheory/QuadraticForm/Global/`), not this criterion | — |
| `IrelandRosen.sophie_germain` (Proposition 17.4.1) | Fermat's last theorem for the exponents 3 and 4; Sophie Germain's identity (`pow_four_add_four_mul_pow_four`) | not found | — |
| `SpecialValues.LFunction_one_sub_nat` | `ζ(-k)` and `hurwitzZeta_neg_nat` (`k ≥ 1`); the value of `L(0, χ)` for even `χ` (`ZMod.LFunction_apply_zero_of_even`) | the generalized Bernoulli numbers (`DirichletCharacter.generalizedBernoulli`, ported here) | — |
| `SpecialValues.LFunction_natCast` | the functional equation of `L(s, χ)` (`ZMod.LFunction_one_sub`) | `τ(χ) ∑_{n ∈ ℤ} χ̄(n) n^{-k} = -(2πi)^k B_{k,χ}/(k! N^{k-1})` for `k ≥ 2` (`DirichletCharacter.gaussSum_mul_tsum_inv_pow_eq_generalizedBernoulli`, ported here); not `k = 1` nor `L(k, χ)` | — |
| `SpecialValues.gaussSum_kroneckerChar` | `τ(χ)² = χ(-1) p` (`gaussSum_sq`) | `∑_{r mod N} e^{2πi r²/N}` for every `N` (`sum_range_cexp_two_pi_I_sq_div`, ported here); Gauss sums of lattices; not the Gauss sums of Jacobi or Kronecker characters | — |

## Candidates considered and not chosen

| candidate | verdict |
|---|---|
| The prime number theorem by the elementary method (Hardy–Wright, Chapter XXII; `NTKB.HardyWright.prime_number_theorem`, Selberg's formula `NTKB.HardyWright.selberg_theorem`) | proved here; PrimeNumberTheoremAnd has the prime number theorem (analytic proof), so not a headline. Mathlib has the Chebyshev bounds only. |
| `L(0, χ_D) = 2h(D)/w(D)` for `D < 0` | not proved. Missing: the factorization `ζ_{ℚ(√D)}(s) = ζ(s) L(s, χ_D)` (equivalently, the number of ideals of norm `n` of `ℚ(√D)` is `∑_{d ∣ n} χ_D(d)`) and the identification of the discriminant of `ℚ(√D)` with `D`; with them, Mathlib's residue of the Dedekind zeta function gives the formula. |
| Eisenstein reciprocity (Ireland–Rosen, Chapter 14) | not in this library (Chapter 14 is outside this release); proved in algebraic-number-theory-lean (`NumberFieldKB.MilneCFT.Ch8.Eisenstein.eisensteinReciprocity`). |
| Mordell equations (Ireland–Rosen, Propositions 17.10.1 and 17.10.2; Hardy–Wright, Theorems 478 and 479) | not proved: 17.10.1 needs Mordell's theorem (no proof in the book), 17.10.2 the class group of `ℤ[√-d]`, Theorem 479 unique factorization in `ℤ[√-2]` applied to `y² = x³ - 2`; Theorem 478 (`y² = x³ + 7`) is elementary but not done. |
| Ramanujan's congruence modulo 11 (Hardy–Wright, Theorem 361) | not proved; the book gives no proof. |

## Results proved here that the other libraries also prove

Each book map lists them in its column *Also in*: 70 rows of Hardy–Wright (mostly results with a weaker or
differently stated Mathlib or PrimeNumberTheoremAnd form, for example the Chebyshev bounds and the prime number
theorem), 42 of Ireland–Rosen (mostly finite fields, Gauss and Jacobi sums, with Mathlib or Tau Ceti forms), and 3
of the special values (ports of Tau Ceti theorems).
