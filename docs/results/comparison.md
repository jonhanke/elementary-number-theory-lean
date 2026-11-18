# Comparison with Mathlib, Tau Ceti and PrimeNumberTheoremAnd

For each headline of this release, what the three libraries closest to it already have, and what this library adds.
Libraries searched (source trees of 2026-11-07 and 2026-11-08): Mathlib master `df6966d` (this library is built on
Mathlib `1b1ccf4`, an earlier commit), Tau Ceti main `d2083f0f`, PrimeNumberTheoremAnd `127b50e`. A result is a
headline only if none of the three has it, or if the form here is stronger; the related results are cited. The
searches were by name and by content (statements read); "not found" means that no declaration of that content was
found, not a proof of absence. The six headlines new in release 0.3.0 were searched again on 2026-11-15 in Mathlib
`1b1ccf4` (the dependency; the proofs' authors also searched Mathlib master `4cf60f1d`), Tau Ceti main `9f43ade0`
and PrimeNumberTheoremAnd `a4fb6989`. The eight headlines new in release 0.4.0 were searched on 2026-11-16 in
Mathlib master `a8754b1`, Tau Ceti main `726e93ef` and PrimeNumberTheoremAnd `a4fb6989`. The five headlines new in
release 0.4.1 were searched on 2026-11-17 in Mathlib master `d9a73ae1` and Tau Ceti main `7b4d5f70`
(PrimeNumberTheoremAnd, which has no curves and no sums of squares, was not searched again). The four headlines new in release 0.5.0 were searched on
2026-11-18 in Mathlib master `5198cccb` and Tau Ceti main `6532c340` (PrimeNumberTheoremAnd, as for 0.4.1, not
searched).

## Headlines

| headline (Lean, namespace `NTKB.Headlines`) | Mathlib | Tau Ceti | PrimeNumberTheoremAnd |
|---|---|---|---|
| `HardyWright.complex_euclidean_quadratic_fields` (Theorem 246) | the Euclidean algorithm of `ℤ[i]` (`GaussianInt.natAbs_norm_mod_lt`); `ℤ[ζ₃]` is a principal ideal domain (`IsCyclotomicExtension.Rat.three_pid`) | not found | — |
| `HardyWright.cube_add_cube_eq_three_mul_cube` (Theorem 232) | Fermat's last theorem for exponent 3 (`fermatLastTheoremThree`), whose general form `a³ + b³ = u c³` in `ℤ[ζ₃]` does not give this equation | not found | — |
| `HardyWright.jacobi_triple_product` (Theorem 352) | Euler's pentagonal number theorem (`eulerFunction_eq_tsum_pentagonal`); Jacobi's theta function as a series (`jacobiTheta`) | the theta product `qTheta` with its functional equations (`qTheta_eq_mul_tprod_mul_tprod`), not the series expansion; its Tate-curve file says it neither uses nor proves the identity | — |
| `HardyWright.ramanujan_five`, `ramanujan_seven` (Theorems 359, 360) | partitions (`Nat.Partition`), Euler's generating functions; no congruence | not found | not found (its "Ramanujan" files are about Ramanujan's prime inequality) |
| `HardyWright.rogers_ramanujan_one`, `rogers_ramanujan_two` (Theorems 362, 363) | not found | not found | — |
| `HardyWright.jacobi_four_squares` (Theorem 386) | Lagrange's four-square theorem (`Nat.sum_four_squares`), Euler's identity | Euler's identity for quadratic maps; no count | — |
| `HardyWright.three_squares` (Section 20.10; new in 0.3.0) | the two-square theorem (`Nat.eq_sq_add_sq_iff`), Lagrange's four-square theorem; Minkowski's convex body theorem and Dirichlet's theorem on primes in progressions (used in the proof) | not found (quadratic forms over local and global fields, theta series of lattices; no three-square theorem) | — |
| `HardyWright.jacobi_eight_squares` (Section 20.13; new in 0.3.0) | Jacobi's theta function, the Eisenstein series `E₄` and its `q`-expansion, the discriminant `Δ` (used in the proof); no count of representations | theta series of lattices on congruence subgroups, `r_{E₈}(2m) = 240 σ₃(m)` for the `E₈` root lattice (`ThetaSeries/E8.lean`), the theta series of `ℤ` (`ZLattice.thetaSeries_span_one`); not `r₈` for `ℤ⁸` | — |
| `IrelandRosen.hasse_davenport` (Chapter 11, § 3) | Gauss sums, `gaussSum_sq`, `gaussSum_mul_gaussSum_eq_card`, Jacobi sums | Jacobi sums of cubic and quartic characters (`gaussSum_pow_three_eq_card_mul_jacobiSum`); not the relation | — |
| `IrelandRosen.biquadratic_reciprocity` (Chapter 9, § 9) | quadratic reciprocity | cubic reciprocity (`IsPrimaryEisenstein.cubic_reciprocity`); the quartic residue symbol of `ℤ[i]` with its supplementary laws (`IsPrimaryGaussian.powerResidueSymbolIdeal_mk_toInteger`, `powerResidueSymbolIdeal_intCast_four`); not this law | — |
| `IrelandRosen.gauss_last_entry` (Chapter 11, § 5) | not found | not found | — |
| `IrelandRosen.legendre` (Proposition 17.3.1) | not found | isotropy of quadratic forms over number fields place by place (`NumberTheory/QuadraticForm/Global/`), not this criterion | — |
| `IrelandRosen.sophie_germain` (Proposition 17.4.1) | Fermat's last theorem for the exponents 3 and 4; Sophie Germain's identity (`pow_four_add_four_mul_pow_four`) | not found | — |
| `IrelandRosen.cube_eq_two_iff` (Proposition 9.6.2; new in 0.3.0) | not found | cubic reciprocity (`IsPrimaryEisenstein.cubic_reciprocity`); the splitting field of `X³ - 2` as a Galois example (`Chebotarev/FixedField/S3Contraction.lean`); not this criterion | — |
| `IrelandRosen.points_y_sq_eq_x_cube_sub_D_x` (Chapter 18, Theorem 5; new in 0.3.0) | Weierstrass curves and their points; no point count | Hasse's bound for every elliptic curve over a finite field (`WeierstrassCurve.hasse_bound`); point counts of `y² = x³ ± x` over `𝔽₃` and `𝔽₅` as worked examples (`Isogeny/Frobenius/WorkedExamples.lean`); Jacobi sums of quartic characters; not this formula | — |
| `IrelandRosen.kummer_congruences` (Chapter 15, § 2, Theorem 5; new in 0.3.0) | Bernoulli numbers, the theorem of von Staudt and Clausen (`vonStaudt_clausen`, `dvd_den_bernoulli`); no Kummer congruence | not found | — |
| `IrelandRosen.class_number_bernoulli` (Chapter 15, § 2; new in 0.3.0) | the residue of the Dedekind zeta function (analytic class number formula of every number field); no congruence | the class number formula of imaginary quadratic fields (`TauCeti.NumberField.classNumber_eq_card_units_mul_LFunction_one`); no congruence with Bernoulli numbers | — |
| `NivenZuckermanMontgomery.proper_representation_iff` (Theorem 3.13) | not found | binary quadratic forms, their discriminants and proper equivalence (`BinaryQuadraticForm`); a primitive form properly represents an integer prime to a given one (`United.lean`); not this criterion | — |
| `NivenZuckermanMontgomery.linear_system_local_global` (Theorem 5.2) | the Smith normal form of submodules over a principal ideal domain (`Submodule.smithNormalForm`, used in the proof); not this theorem | not found | — |
| `NivenZuckermanMontgomery.quartic_eq_square` (Theorem 5.9) | not found | not found | — |
| `NivenZuckermanMontgomery.rational_points_y_sq_eq_x_cube_sub_four_x` (Theorem 5.24) | Weierstrass curves and their group law; Fermat's last theorem for exponent 4 (`not_fermat_42`, used in the proof); no congruent numbers | not found | — |
| `NivenZuckermanMontgomery.galois_purely_periodic` (Theorem 7.20) | generalized continued fractions (`GenContFract`) and the continued fraction of a real number; no periodicity | not found | — |
| `NivenZuckermanMontgomery.eq_convergent_of_sq_sub_mul_sq` (Theorem 7.24) | Pell's equation (`Pell.Solution₁`, `Pell.exists_of_not_isSquare`); not its relation to convergents | not found | — |
| `NivenZuckermanMontgomery.omega_maximal_order` (Theorem 8.30) | `ω` (`ArithmeticFunction.cardDistinctFactors`) and Chebyshev's bounds | not found | `ω` in its sieve files, without this order |
| `NivenZuckermanMontgomery.partition_bounds` (Theorem 10.12) | partitions (`Nat.Partition`) and their generating function; no growth bound | not found | not found |
| `NivenZuckermanMontgomery.exists_squarefree_add` (Theorem 11.2) | squarefree numbers (`Squarefree`); not this | not found | not found |
| `NivenZuckermanMontgomery.mann_alpha_beta` (Theorem 11.10) | Schnirelmann density (`schnirelmannDensity`) and the case `d(A) + d(B) ≥ 1` (`add_eq_univ_of_one_le_schirelmannDensity_add_schnirelmannDensity`); Mann's theorem is listed as a to-do in `Mathlib/Combinatorics/Schnirelmann.lean` | not found | — |
| `SpecialValues.LFunction_one_sub_nat` | `ζ(-k)` and `hurwitzZeta_neg_nat` (`k ≥ 1`); the value of `L(0, χ)` for even `χ` (`ZMod.LFunction_apply_zero_of_even`) | the generalized Bernoulli numbers (`DirichletCharacter.generalizedBernoulli`, ported here) | — |
| `SpecialValues.LFunction_natCast` | the functional equation of `L(s, χ)` (`ZMod.LFunction_one_sub`) | `τ(χ) ∑_{n ∈ ℤ} χ̄(n) n^{-k} = -(2πi)^k B_{k,χ}/(k! N^{k-1})` for `k ≥ 2` (`DirichletCharacter.gaussSum_mul_tsum_inv_pow_eq_generalizedBernoulli`, ported here); not `k = 1` nor `L(k, χ)` | — |
| `SpecialValues.gaussSum_kroneckerChar` | `τ(χ)² = χ(-1) p` (`gaussSum_sq`) | `∑_{r mod N} e^{2πi r²/N}` for every `N` (`sum_range_cexp_two_pi_I_sq_div`, ported here); Gauss sums of lattices; not the Gauss sums of Jacobi or Kronecker characters | — |
| `HardyWright.jacobi_six_squares` (Section 20.13, (20.13.1); new in 0.4.0) | sums of two and four squares; no `r₆` | theta series of lattices as modular forms (`ZLattice.thetaSeries_span_orthonormalBasis`: the theta series of `ℤⁿ` is `jacobiTheta ^ n`); no count | not found |
| `HardyWright.glaisher_twelve_squares` (Glaisher, beyond the book; new in 0.4.0) | Dedekind's `η` (used in the proof); no `r₁₂` (its "Glaisher" theorem is the partition theorem) | as for `r₆`; no count | not found |
| `IrelandRosen.class_number_bernoulli_field` (corollary to 15.2.3, the class number of the field; new in 0.4.0) | the class number `NumberField.classNumber`, Bernoulli numbers; no congruence | the class number formula of imaginary quadratic fields (`classNumber_eq_card_units_mul_LFunction_one`); no congruence | — |
| `IrelandRosen.hecke_character_quartic_curve_split`, `_inert` (Chapter 18, Theorem 7; new in 0.4.0) | `WeierstrassCurve.localPolynomial` and `WeierstrassCurve.LFunction` (definitions, used in the statements), `NumberField.HeckeCharacter` (a definition); no link | Hecke L-functions of ray class characters and Grössencharacters (`LFunctions/Hecke/`, `LFunctions/Grossencharacter/`), the complex multiplication of `y² = x³ + ax` (`hasGeometricCM_of_a₆_eq_zero`); no link between `L(E, s)` and a Hecke character | — |
| `IrelandRosen.hecke_character_cubic_curve_split`, `_inert` (Chapter 18, Theorem 8; new in 0.4.0) | as above | as above | — |
| `IrelandRosen.mordell_class_number` (Proposition 17.10.2; new in 0.4.0) | class groups; no Mordell equation | Mordell–Weil and worked examples of curves; not this criterion | — |
| `HardyWright.liouville_ten_squares` (Liouville, beyond the book; new in 0.4.1) | Jacobi's theta function and its functional equation in two variables (used in the proof); no `r₁₀` | as for `r₆`; no count | — |
| `IrelandRosen.hecke_character_quartic_curve_bad`, `hecke_character_cubic_curve_bad` (Chapter 18, Theorems 7 and 8 at the primes of additive reduction; new in 0.4.1) | `WeierstrassCurve.localPolynomial` (a definition; its value `1` at a prime of additive reduction is only a comment), the reduction types of a minimal model (`HasAdditiveReduction`); no theorem on the local polynomial | as for the 0.4.0 forms; no link | — |
| `IrelandRosen.infinite_points_mordell`, `infinite_points_sum_cubes` (Propositions 17.10.1 and 17.9.1, conditional on `MordellTorsionInput`; new in 0.4.1) | the group of points of a Weierstrass curve; no infinitude statement | the Lutz–Nagell theorem (`WeierstrassCurve.lutz_nagell`), worked examples of curves of positive rank; not Fueter's classification, not these statements | — |
| `IrelandRosen.hecke_character_quartic_curve_every_prime`, `hecke_character_cubic_curve_every_prime` (Chapter 18, Theorems 7 and 8 at every prime; new in 0.5.0) | `WeierstrassCurve.localPolynomial` (a definition); no value at a bad prime, no Hecke character of a curve | general facts on the local polynomial (`localPolynomial_eq_of_hasGoodReduction`, `localPolynomial_eq_one_of_hasPotentialGoodReduction_of_not_hasGoodReduction`); no link to a Hecke character | — |
| `HardyWright.glaisher_fourteen_squares`, `glaisher_sixteen_squares` (beyond the book; new in 0.5.0) | modular forms of level one, q-expansions; no `r₁₄`, `r₁₆` | theta series of lattices; no count | — |

## Candidates considered and not chosen

| candidate | verdict |
|---|---|
| The prime number theorem by the elementary method (Hardy–Wright, Chapter XXII; `NTKB.HardyWright.prime_number_theorem`, Selberg's formula `NTKB.HardyWright.selberg_theorem`) | proved here; PrimeNumberTheoremAnd has the prime number theorem (analytic proof), so not a headline. Mathlib has the Chebyshev bounds only. |
| `L(0, χ_D) = 2h(D)/w(D)` for `D < 0` | not proved. Missing: the factorization `ζ_{ℚ(√D)}(s) = ζ(s) L(s, χ_D)` (equivalently, the number of ideals of norm `n` of `ℚ(√D)` is `∑_{d ∣ n} χ_D(d)`) and the identification of the discriminant of `ℚ(√D)` with `D`; with them, Mathlib's residue of the Dedekind zeta function gives the formula. |
| Eisenstein reciprocity (Ireland–Rosen, Chapter 14) | not in this library (Chapter 14 is outside this release); proved in algebraic-number-theory-lean (`NumberFieldKB.MilneCFT.Ch8.Eisenstein.eisensteinReciprocity`). |
| Mordell equations (Ireland–Rosen, Propositions 17.10.1 and 17.10.2; Hardy–Wright, Theorems 478 and 479) | 17.10.2 is a headline since 0.4.0; 17.10.1 (and 17.9.1) are conditional headlines since 0.4.1, from Fueter's classification of the torsion points (a named input); Theorem 479 unique factorization in `ℤ[√-2]` applied to `y² = x³ - 2`; Theorem 478 (`y² = x³ + 7`) is elementary but not done. |
| Ramanujan's congruence modulo 11 (Hardy–Wright, Theorem 361) | not proved; the book gives no proof. |
| Simultaneous Diophantine approximation (Niven–Zuckerman–Montgomery, Theorem 6.25; `NTKB.NZM.simultaneous_approximation_general`) | proved here; Tau Ceti has Dirichlet's simultaneous approximation theorem (`TauCeti.simultaneous_dirichlet`, with `≤` in place of `<`), so not a headline. |
| The number of representations by a positive definite binary form, `r_f(n) = w(f) H_f(n)` (Niven–Zuckerman–Montgomery, Theorem 3.27) | proved here; not chosen as a headline because its statement needs several definitions of the library (automorphs, the count `H_f`); a candidate for a later release. |
| The splitting of rational primes in a quadratic field with unique factorization (Niven–Zuckerman–Montgomery, Theorem 9.29) | only part (a) proved; parts (b) to (e) stated, not proved. |

| Cubic reciprocity and its supplement (Ireland–Rosen, Chapter 9, § 3, Theorems 1 and 1'; `NTKB.IrelandRosen.Eisenstein.cubic_reciprocity`) | proved here (the supplement in the rational case the book proves); Tau Ceti has cubic reciprocity, so not a headline. Its consequence 9.6.2 is a headline. |
| Hasse's bound `\|N_p - (p + 1)\| ≤ 2√p` for `y² = x³ - Dx` and `y² = x³ + D` (`abs_numPointsQuarticCurve_sub_le`, `abs_numPointsCubicCurve_sub_le`) | proved here from `\|π\|² = p`; Tau Ceti has Hasse's bound for every elliptic curve over a finite field, so not a headline. |
| The number of points of `y² = x³ + D` over `𝔽_p` by sextic characters (Ireland–Rosen, Chapter 18, Theorem 4; `NTKB.IrelandRosen.numPointsCubicCurve_eq`) | proved here; not chosen (the companion of the headline Theorem 5, with a sextic residue symbol defined in the library). |
| Liouville's formula for `r₁₀(n)` (beyond the books) | stated only in 0.4.0; proved and a headline since 0.4.1 (`liouville_ten_squares`). (Jacobi's `r₆`, a candidate in 0.3.0, is a headline since 0.4.0.) |
| Ireland–Rosen 18, Theorem 6 (`L(s, χ)` entire for the two Hecke characters) | not proved (the analytic continuation by Hecke's theta series is not formalized). |
| The ring of integers, discriminant and decomposition law of `ℚ(√d)` (Ireland–Rosen 13.1.1 to 13.1.4) | proved here (new in 0.4.0); Tau Ceti proves them (`NumberField/Quadratic/RingOfIntegers.lean`, `PrimeDecomposition.lean`), so not a headline. |
| Theorem 6 of Ireland–Rosen 18 (the analytic continuation of `L(s, χ)` for the two characters) and the Euler factors at the primes dividing `2D` (resp. `6D`) | not proved. |
| Primes in a progression have Dirichlet density `1/φ(m)` (Ireland–Rosen, Chapter 16, Theorem 1; `NTKB.IrelandRosen.hasDirichletDensity_modEq`) | proved here; Mathlib has the natural-density form of Dirichlet's theorem and the definition of Dirichlet density for number fields, so not a headline. |
| Carlitz: infinitely many irregular primes (Ireland–Rosen, Chapter 15, § 2, Theorem 6; `NTKB.IrelandRosen.infinite_setOf_isIrregularPrime`) | proved here; not chosen in favour of the Kummer congruences it is derived from (a candidate for a later release). |

## Results proved here that the other libraries also prove

Each book map lists them in its column *Also in*: 79 rows of Hardy–Wright (mostly results with a weaker or
differently stated Mathlib or PrimeNumberTheoremAnd form, for example the Chebyshev bounds and the prime number
theorem), 67 of Ireland–Rosen (mostly finite fields, Gauss and Jacobi sums, with Mathlib or Tau Ceti forms), 84 of
Niven–Zuckerman–Montgomery, and 3 of the special values (ports of Tau Ceti theorems).
