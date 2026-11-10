# Elementary number theory in Lean 4

[![Lean build](https://github.com/jonhanke/elementary-number-theory-lean/actions/workflows/build.yml/badge.svg)](https://github.com/jonhanke/elementary-number-theory-lean/actions/workflows/build.yml) [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24088043.svg)](https://doi.org/10.5281/zenodo.24088043)

A Lean 4 library (built on Mathlib) that formalizes three texts of elementary number theory item by item: Hardy
and Wright's *An Introduction to the Theory of Numbers* (6th edition), Ireland and Rosen's *A Classical Introduction
to Modern Number Theory* (Chapters 1 to 11, 15 and 16, and part of Chapter 17) and Niven, Zuckerman and Montgomery's
*An Introduction to the Theory of Numbers* (5th edition), together with the special values of Dirichlet
$`L`$-functions at the integers. The Lean library is called `NTKB`; the repository is
elementary-number-theory-lean.

- **Book maps**: for each book, a table from every result (theorem, proposition, lemma, corollary, result stated in
  the text) to the Lean declaration that formalizes it and its status: [docs/results/books/](docs/results/books/README.md).
- **Literature statements**: each result from a book or paper is a Lean declaration tagged
  `@[kb "<source key>" "<locator>"]`, with the keys of [`references.bib`](references.bib).
- **What is proved**: every theorem is checked by the Lean kernel; the only `sorry`s in the repository are the
  deliberate ones in the `Challenge_<book>.lean` files, which state the headline results without proofs. The CI
  workflow builds the library, checks that the headline theorems depend only on the standard axioms `propext`,
  `Classical.choice` and `Quot.sound` ([scripts/check_axioms.lean](scripts/check_axioms.lean)), checks that every Lean
  name of the book maps exists ([scripts/check_map_names.lean](scripts/check_map_names.lean)), and runs
  `lake comparator` once per book to check the proved statements against the `Challenge_<book>.lean` files.
- **Cited results are named**: where the library assumes a result it does not prove, the result is a named Lean
  structure, never assumed silently; a theorem that uses it has it as a hypothesis and the book maps mark the row
  *conditional* (in this release only one row, which assumes the abc conjecture).
- **Comparison**: [docs/results/comparison.md](docs/results/comparison.md) says, for each headline, what Mathlib,
  [Tau Ceti](https://github.com/TauCetiProject/TauCeti) and
  [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) already have and what this library
  adds. This library depends on Mathlib only.

## The books

| book | rows | proved | proved in part | conditional | in Mathlib | other | proved here, also elsewhere |
|---|---|---|---|---|---|---|---|
| [G. H. Hardy and E. M. Wright, *An Introduction to the Theory of Numbers* (6th ed., 2008)](docs/results/books/hardy-wright.md) | 626 | 279 | 14 | 1 | 178 | 154 | 79 |
| [K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory* (2nd ed., 1990), Chapters 1–11, 15, 16 and the results of Chapter 17 proved here](docs/results/books/ireland-rosen.md) | 401 | 120 | 5 | 0 | 178 | 98 | 53 |
| [I. Niven, H. S. Zuckerman and H. L. Montgomery, *An Introduction to the Theory of Numbers* (5th ed., 1991)](docs/results/books/niven-zuckerman-montgomery.md) | 406 | 194 | 4 | 0 | 191 | 17 | 84 |
| [Special values of Dirichlet $L$-functions and Gauss's sign of quadratic Gauss sums](docs/results/books/special-values.md) | 25 | 25 | 0 | 0 | 0 | 0 | 3 |

*Proved*: proved with only the standard axioms and no unproved input. *Proved in part*: a part, a special case or one instance is proved. *Conditional*: proved from a named unproved input (here only the abc conjecture, in a note of Hardy–Wright). *In Mathlib*: Mathlib (a dependency) has the result; the map names the Mathlib declaration. *Other*: refuted as stated in the book (the corrected form is proved), in Tau Ceti or PrimeNumberTheoremAnd only (not dependencies), partly formalized elsewhere, or not formalized (see each map). *Proved here, also elsewhere*: rows proved (in whole or in part) here whose result, a part of it or a closely related statement is also in Mathlib, Tau Ceti or PrimeNumberTheoremAnd; each map names those declarations in its column *Also in*. Rows that are not results (definitions, remarks, history, open problems) are omitted from the maps.

## Highlights

Every result listed here is a headline theorem of a `Challenge_<book>.lean` file: it is checked by the Lean kernel
with only the standard axioms and depends on no unproved input. Headlines are only results that are in none of
Mathlib, Tau Ceti and PrimeNumberTheoremAnd, or that are stronger here ([comparison](docs/results/comparison.md));
related results of those libraries are cited next to each headline. The statements have **not yet been reviewed by
a human** (see Provenance).

**Hardy and Wright, *An Introduction to the Theory of Numbers*** ([`Challenge_HardyWright.lean`](Challenge_HardyWright.lean))

- **The complex Euclidean quadratic fields:** for squarefree $`m < 0`$, $`\mathbb Q(\sqrt m)`$ is (norm-)Euclidean
  exactly for $`m = -1, -2, -3, -7, -11`$ (`complex_euclidean_quadratic_fields`, Theorem 246). Related: Mathlib has
  the Euclidean algorithm of the Gaussian integers (`GaussianInt.natAbs_norm_mod_lt`) and that
  $`\mathbb Z[\zeta_3]`$ is a principal ideal domain (`IsCyclotomicExtension.Rat.three_pid`), not the cases
  $`-2, -7, -11`$ nor the exclusion of every other $`m`$.
- **$`x^3 + y^3 = 3z^3`$** has only the solutions with $`z = 0`$ (`cube_add_cube_eq_three_mul_cube`, Theorem 232).
  Related: Mathlib's Fermat's last theorem for exponent 3 (`fermatLastTheoremThree`, with its form
  $`a^3 + b^3 = u c^3`$ over $`\mathbb Z[\zeta_3]`$), which does not give this equation.
- **Jacobi's triple product identity**
  $`\prod_{n\ge1}(1-x^{2n})(1+x^{2n-1}z)(1+x^{2n-1}z^{-1})=\sum_{n\in\mathbb Z}x^{n^2}z^n`$ for $`|x|<1`$, $`z\ne0`$
  (`jacobi_triple_product`, Theorem 352). Related: Mathlib has Euler's pentagonal number theorem
  (`eulerFunction_eq_tsum_pentagonal`) and Jacobi's theta function as a series; Tau Ceti has the theta product
  (`qTheta`, with its functional equations), not its series expansion.
- **Ramanujan's congruences** $`p(5m+4) \equiv 0 \pmod 5`$ and $`p(7m+5) \equiv 0 \pmod 7`$ (`ramanujan_five`,
  `ramanujan_seven`, Theorems 359 and 360), by the book's proofs through Jacobi's identities.
- **The Rogers–Ramanujan identities**
  $`\sum_{s\ge0}x^{s^2}/((1-x)\cdots(1-x^s)) = \prod_{m\ge0}1/((1-x^{5m+1})(1-x^{5m+4}))`$ and its companion with
  $`x^{s(s+1)}`$ and $`5m+2, 5m+3`$ (`rogers_ramanujan_one`, `rogers_ramanujan_two`, Theorems 362 and 363).
- **Jacobi's four-square theorem:** the number of representations of $`n \ge 1`$ as a sum of four squares of
  integers is $`8\sum_{d \mid n,\ 4 \nmid d} d`$ (`jacobi_four_squares`, Theorem 386). Related: Mathlib has
  Lagrange's theorem that every $`n`$ is a sum of four squares (`Nat.sum_four_squares`), not the count.

**Ireland and Rosen, *A Classical Introduction to Modern Number Theory*** ([`Challenge_IrelandRosen.lean`](Challenge_IrelandRosen.lean))

- **The Hasse–Davenport relation** $`(-g(\chi))^s = -g(\chi \circ N_{E/F})`$ for an extension $`E/F`$ of finite
  fields of degree $`s`$, the Gauss sums over $`E`$ taken with $`\psi \circ \operatorname{tr}_{E/F}`$
  (`hasse_davenport`, Chapter 11, § 3, Theorem 1). Related: Mathlib has Gauss sums and Jacobi sums with
  `gaussSum_sq` and `gaussSum_mul_gaussSum_eq_card`, not the relation.
- **The law of biquadratic reciprocity** for relatively prime primary $`\lambda, \pi \in \mathbb Z[i]`$:
  $`\chi_\pi(\lambda) = \chi_\lambda(\pi)(-1)^{\frac{N\lambda-1}{4}\cdot\frac{N\pi-1}{4}}`$
  (`biquadratic_reciprocity`, Chapter 9, § 9, Theorem 2). Related: Tau Ceti has cubic reciprocity
  (`IsPrimaryEisenstein.cubic_reciprocity`) and the supplementary laws of the quartic residue symbol of
  $`\mathbb Z[i]`$, not this law.
- **Gauss's last entry:** for a prime $`p \equiv 1 \pmod 4`$, $`p = a^2 + b^2`$ with $`a`$ normalized as in the
  book, the curve $`x^2t^2 + y^2t^2 + x^2y^2 = t^4`$ has $`p - 1 - 2a`$ points in $`\mathbb P^2(\mathbb F_p)`$
  (`gauss_last_entry`, Chapter 11, § 5).
- **Legendre's theorem:** for squarefree, pairwise coprime $`a, b, c`$, not all of the same sign,
  $`ax^2 + by^2 + cz^2 = 0`$ has a nontrivial integral solution if and only if $`-ab`$, $`-ac`$, $`-bc`$ are squares
  modulo $`c`$, $`b`$, $`a`$ (`legendre`, Proposition 17.3.1). Related: Tau Ceti studies the isotropy of quadratic
  forms over number fields place by place, without this criterion.
- **Sophie Germain's theorem:** if $`p`$ and $`2p + 1`$ are odd primes, $`x^p + y^p + z^p = 0`$ has no integral
  solution with $`p \nmid xyz`$ (`sophie_germain`, Proposition 17.4.1). Related: Mathlib has Fermat's last theorem
  for the exponents 3 and 4 and Sophie Germain's algebraic identity (`pow_four_add_four_mul_pow_four`), not this
  theorem.

**Niven, Zuckerman and Montgomery, *An Introduction to the Theory of Numbers*** ([`Challenge_NivenZuckermanMontgomery.lean`](Challenge_NivenZuckermanMontgomery.lean)) (new in 0.2.0)

- **Proper representations by binary quadratic forms:** for integers $`n \ne 0`$ and $`d`$, some form
  $`ax^2 + bxy + cy^2`$ of discriminant $`b^2 - 4ac = d`$ represents $`n`$ at a relatively prime pair $`(x, y)`$ if
  and only if $`d`$ is a square modulo $`4|n|`$ (`proper_representation_iff`, Theorem 3.13). Related: Tau Ceti has
  binary quadratic forms and their discriminants, not this criterion.
- **The local-global principle for linear systems:** a system $`Ax = b`$ with integer coefficients that has a real
  solution and is solvable modulo every $`q \ge 1`$ has an integral solution (`linear_system_local_global`,
  Theorem 5.2). Related: Mathlib has the Smith normal form, which the proof uses.
- **$`x^4 + x^3 + x^2 + x + 1 = y^2`$** has exactly the integral solutions $`(-1, \pm1)`$, $`(0, \pm1)`$, $`(3, \pm11)`$
  (`quartic_eq_square`, Theorem 5.9).
- **The rational points of $`y^2 = x^3 - 4x`$** are $`(0,0)`$, $`(2,0)`$, $`(-2,0)`$ (and the point at infinity): $`2`$ is
  not a congruent number (`rational_points_y_sq_eq_x_cube_sub_four_x`, Theorem 5.24). Related: Mathlib has
  Weierstrass curves and Fermat's last theorem for the exponent 4, not this equation.
- **Galois's theorem:** the continued fraction of a real quadratic irrational $`\xi`$ is purely periodic if and only if
  $`\xi > 1`$ and its conjugate lies in $`(-1, 0)`$ (`galois_purely_periodic`, Theorem 7.20). Related: Mathlib has
  generalized continued fractions and the continued fraction of a real number, not periodicity.
- **Small values of $`x^2 - dy^2`$:** if $`|N| < \sqrt d`$, every solution of $`s^2 - dt^2 = N`$ in relatively prime
  positive integers is a convergent of $`\sqrt d`$ (`eq_convergent_of_sq_sub_mul_sq`, Theorem 7.24). Related: Mathlib
  has the solutions of Pell's equation (`Pell.Solution₁`), not their relation to continued fractions.
- **The maximal order of $`\omega(n)`$:** for every $`\varepsilon > 0`$, $`\omega(n) < (1+\varepsilon)\log n/\log\log n`$
  for all large $`n`$, and $`\omega(n) > (1-\varepsilon)\log n/\log\log n`$ for infinitely many $`n`$
  (`omega_maximal_order`, Theorem 8.30).
- **Bounds for the partition function:** $`2^{\sqrt n} < p(n) < e^{\pi\sqrt{2n/3}}`$ for $`n \ge 4`$
  (`partition_bounds`, Theorem 10.12).
- **Sums of two squarefree numbers:** every integer $`n > 1`$ is the sum of two squarefree positive integers
  (`exists_squarefree_add`, Theorem 11.2).
- **Mann's $`\alpha + \beta`$ theorem:** for sets $`A, B`$ of natural numbers containing $`0`$, the Schnirelmann density
  satisfies $`d(A + B) \ge \min(1, d(A) + d(B))`$ (`mann_alpha_beta`, Theorem 11.10). Related: Mathlib has the
  Schnirelmann density and the case $`d(A) + d(B) \ge 1`$; Mann's theorem is on its list of things to do.

**Special values of Dirichlet $`L`$-functions** ([`Challenge_SpecialValues.lean`](Challenge_SpecialValues.lean))

- **$`L(1-k,\chi) = -B_{k,\chi}/k`$** for every Dirichlet character $`\chi`$ and every $`k \ge 1`$, with no
  primitivity or nontriviality hypothesis (`LFunction_one_sub_nat`; Washington, Theorem 4.2). Related: Mathlib has
  $`\zeta(-k)`$ and the Hurwitz zeta function at $`-k`$ for $`k \ge 1`$ (`hurwitzZeta_neg_nat`); Tau Ceti has the
  generalized Bernoulli numbers $`B_{k,\chi}`$, not this formula.
- **$`L(k,\chi)`$ by Gauss sums:** for primitive $`\chi`$ modulo $`N`$, $`k \ge 1`$, $`\chi(-1) = (-1)^k`$,
  $`\delta = k \bmod 2`$: $`L(k,\chi)=(-1)^{1+(k-\delta)/2}\,\frac{\tau(\chi)}{2i^{\delta}}\left(\frac{2\pi}{N}\right)^{k}\frac{B_{k,\bar\chi}}{k!}`$
  (`LFunction_natCast`). Related: Tau Ceti has
  $`\tau(\chi)\sum_{n\in\mathbb Z}\bar\chi(n)n^{-k} = -\frac{(2\pi i)^k}{k!\,N^{k-1}}B_{k,\chi}`$ for $`k \ge 2`$
  (`DirichletCharacter.gaussSum_mul_tsum_inv_pow_eq_generalizedBernoulli`, ported here with credit); the case
  $`k = 1`$ and the passage to $`L(k,\chi)`$ are new here.
- **Gauss's sign of the quadratic Gauss sum, for every fundamental discriminant:** $`\tau(\chi_D) = \sqrt D`$ if
  $`D > 0`$ and $`i\sqrt{|D|}`$ if $`D < 0`$ (`gaussSum_kroneckerChar`). Related: Mathlib has
  $`\tau(\chi)^2 = \chi(-1)p`$ (`gaussSum_sq`); Tau Ceti has the evaluation of $`\sum_{r \bmod N} e^{2\pi i r^2/N}`$
  for every $`N`$ (`sum_range_cexp_two_pi_I_sq_div`, ported here with credit), not the Gauss sums of Jacobi or
  Kronecker characters.

**Main statements.** To check what is claimed, read four files: [`Challenge_HardyWright.lean`](Challenge_HardyWright.lean),
[`Challenge_IrelandRosen.lean`](Challenge_IrelandRosen.lean),
[`Challenge_NivenZuckermanMontgomery.lean`](Challenge_NivenZuckermanMontgomery.lean) and
[`Challenge_SpecialValues.lean`](Challenge_SpecialValues.lean) state the results above, with a docstring for each and a list of the library definitions the statements use; every
proof there is a deliberate `sorry`. The matching `Solution_<book>.lean` files prove the same statements by appeal
to the library theorems, and `lake comparator`, configured per book by `comparator/<book>.json` (the books are
listed in [`comparator.json`](comparator.json)), checks that each proved statement is exactly the one in the
challenge file and uses only the standard axioms. The check is run one book at a time: each needs only the files of
its book. [`formalization.yaml`](formalization.yaml) records the scope, sources, divergences from the literature,
provenance and review status in the [formalization.yaml](https://github.com/mathlib-initiative/formalization.yaml)
format.

**Also proved here, not headlines because another library has them:** the prime number theorem by the elementary
method of Selberg and Erdős as in Hardy–Wright, Chapter XXII (`NTKB.HardyWright.prime_number_theorem`, with
Selberg's formula `NTKB.HardyWright.selberg_theorem`; PrimeNumberTheoremAnd proves the prime number theorem
analytically); Dirichlet's theorem in the special cases of Hardy–Wright, Chapter II (Mathlib has Dirichlet's
theorem); the two-square and four-square theorems in their book forms (Mathlib). Each book map credits, in its
column *Also in*, the results proved here that Mathlib, Tau Ceti or PrimeNumberTheoremAnd also prove. From
Niven–Zuckerman–Montgomery: simultaneous Diophantine approximation (Theorem 6.25,
`NTKB.NZM.simultaneous_approximation_general`; Tau Ceti has Dirichlet's simultaneous approximation theorem).

## Corrections to the books

Statements false as printed, found while formalizing them; the library proves the printed statement false and
proves the corrected form ([docs/updates-and-errata.md](docs/updates-and-errata.md) has the details):

- **Hardy–Wright, Theorem 20** (§ 2.6): $`\pi(x) \ge \log x/(2\log 2)`$ for real $`x \ge 1`$ fails for
  $`1 < x < 2`$ (e.g. $`x = 3/2`$, where $`\pi(x) = 0`$). True for integers $`x \ge 1`$, i.e. with $`\log\lfloor x\rfloor`$
  (`NTKB.HardyWright.primeCounting_ge_log_div_and_nth_prime_lt`; refuted as printed by
  `NTKB.HardyWright.not_primeCounting_ge_log_div_real`).
- **Hardy–Wright, (13.7.11)** (§ 13.7): Euler's parametric solution of $`x^4 + y^4 = u^4 + v^4`$ prints the
  polynomial for $`u`$ equal to the one for $`x`$, so the identity fails; the term $`3a^2b^5`$ of $`u`$ should be
  $`-3a^2b^5`$, which agrees with the book's example $`133^4 + 134^4 = 158^4 + 59^4`$
  (`NTKB.HardyWright.euler_fourth_powers`; `NTKB.HardyWright.not_euler_fourth_powers_printed`).
- **Hardy–Wright, notes to Chapter XIII:** the abc conjecture is printed without the coprimality of $`a`$ and $`b`$,
  and in that form it is false ($`a = b = 2^k`$); and $`3(1 + \tfrac12) = \tfrac92`$, not $`\tfrac72`$, so the argument
  for Fermat's equation needs $`\varepsilon = \tfrac16`$ (`NTKB.HardyWright.not_abc_without_coprime`;
  `NTKB.HardyWright.fermat_finite_of_abc` assumes the corrected conjecture `NTKB.HardyWright.AbcConjecture`).
- **Hardy–Wright, Theorems 268 and 269** (§ 16.5): the Möbius inversion formulas over real arguments are printed
  "for all positive $`x`$", but fail for $`0 < x < 1`$; they hold for $`x \ge 1`$
  (`NTKB.HardyWright.moebius_inversion_floor`, `NTKB.HardyWright.moebius_inversion_floor_converse`; refuted as
  printed by `NTKB.HardyWright.not_moebius_inversion_floor_all_pos` and
  `NTKB.HardyWright.not_moebius_inversion_floor_converse_all_pos`).

## Layout

```
Challenge_<book>.lean   the headline statements of one book (proofs: deliberate sorry);
                        <book> = HardyWright, IrelandRosen, NivenZuckermanMontgomery, SpecialValues
Solution_<book>.lean    the same statements, proved from the library
comparator.json         the books, each with its lake comparator configuration comparator/<book>.json
formalization.yaml      scope, sources, divergences, provenance, review (formalization.yaml v0.4)
docs/results/books/     the book maps; docs/results/comparison.md: comparison with Mathlib, Tau Ceti, PNT+
docs/updates-and-errata.md  corrections to the books
NTKB/
  Elementary/HardyWright/   Hardy-Wright, by topic (PrimeDistribution, Congruences, Residues, ContinuedFractions,
                            QuadraticFields, ArithmeticFunctions, Partitions, SumsOfSquares, ...)
  IrelandRosen/R1, R2, R3/  Ireland-Rosen: R1 Chapters 1-7 and 16; R2 Chapters 8, 10, 11 (Gauss and Jacobi sums,
                            equations over finite fields, zeta functions); R3 Chapters 9 and 17 (reciprocity, Z[i],
                            Diophantine equations)
  Elementary/NZM/           Niven-Zuckerman-Montgomery (the results not already proved for the other books)
  Elementary/SpecialValues/ the special values of Dirichlet L-functions and the quadratic Gauss sums
  Analytic/Apostol/, Analytic/Davenport/  supporting files (see below)
  Port/                     files ported from Tau Ceti (Apache 2.0), with credit in their headers
  Attr.lean                 the @[kb] citation attribute
references.bib          bibliography; the keys used by @[kb]
scripts/check_axioms.lean       prints the axioms of the headline theorems (run in CI)
scripts/check_map_names.lean    checks that the Lean names of the book maps exist (run in CI)
scripts/verify-comparator.sh    runs lake comparator for one book with the toolchain's kernels (run in CI)
.github/workflows/build.yml  the CI workflow (build, axioms, map names, one comparator check per book)
```

**Supporting files outside this release's books.** The books import 35 files of the library's treatment
of Apostol's *Introduction to Analytic Number Theory* and Davenport's *Multiplicative Number Theory* (Jacobi's triple
product, the Chebyshev functions and the equivalent forms of the prime number theorem, partial summation, the
partition function, the reduction of binary quadratic forms). They are shipped so that the library builds; the
analytic books are not part of this release. Some ported files carry the proofs of Tau Ceti results that the
library needs (Tau Ceti is not a dependency).

## Usage

```bash
lake exe cache get       # once: download prebuilt Mathlib
lake build               # build and check everything
lake env lean scripts/check_axioms.lean          # axioms of the headline theorems
./scripts/verify-comparator.sh HardyWright       # Solution_HardyWright against Challenge_HardyWright
                                                 # (Linux; needs bubblewrap); likewise IrelandRosen,
                                                 # NivenZuckermanMontgomery, SpecialValues
```

Mathlib comes prebuilt from its cache; this library is built from source (241 modules, about 64,000 lines; no file
imports all of Mathlib, so only the Mathlib modules it needs are loaded). On 8 cores and 31 GB (2026-11-10), with
Mathlib's cache in place, `lake build` took about 6 minutes, with at most 7.3 GB of memory in use and a largest
single Lean process of 5.6 GB. Each `lake comparator` check (one book: build, export, and the Lean, NanoDa and
con-ron kernels) took 4 to 8 minutes, with at most 3.8 GB in use and a largest single process of at most 4.6 GB
(`leanexport`).

## Provenance

NTKB was written by AI, with Claude Code (Anthropic): almost entirely by Claude Opus 5.5, with a share by Claude
Sonnet 5.5, in October and November 2026. Jonathan Hanke designed and directed it: he chose the books, the results,
the conventions and the proof routes. The files under `NTKB/Port/` and the files of `NTKB/Elementary/SpecialValues/`
that say so in their headers contain code ported from Tau Ceti (by the Tau Ceti contributors, Apache 2.0). The proofs
are checked by the Lean kernel, and CI checks that the headline theorems use only the standard axioms. The 26
headline statements of this release in the `Challenge_<book>.lean` files, and the definitions they use, have **not
yet been reviewed** by a human; that review is planned for a later release. `lake comparator` checks that each
`Solution_<book>.lean` proves exactly the statements of its `Challenge_<book>.lean`. The rest of the library (its
other definitions and intermediate results, and the book maps) has not been reviewed by a human; as with any
AI-written formalization, treat it as untrustworthy until checked against the literature. Corrections and reports of
mis-formalizations are very welcome.

## Releases

Releases are tagged with semantic versions; `main` continues to develop. The DOI [10.5281/zenodo.24088043](https://doi.org/10.5281/zenodo.24088043) always resolves to the latest release. To cite a specific version, use its release page or the "Cite this repository" button.

- **[v0.1.0](https://github.com/jonhanke/elementary-number-theory-lean/releases/tag/v0.1.0)** (Lean v4.36.0-rc2, Mathlib `1b1ccf4`), archived on Zenodo as [doi:10.5281/zenodo.24088044](https://doi.org/10.5281/zenodo.24088044): the first release: the book maps of Hardy–Wright and
  Ireland–Rosen, the special values of Dirichlet $`L`$-functions, and 16 headline statements (those of Hardy–Wright,
  Ireland–Rosen and the special values above).
- **[v0.2.0](https://github.com/jonhanke/elementary-number-theory-lean/releases/tag/v0.2.0)** (Lean v4.36.0-rc2, Mathlib `1b1ccf4`), archived on Zenodo as [doi:10.5281/zenodo.24117540](https://doi.org/10.5281/zenodo.24117540): Niven, Zuckerman and Montgomery's *An Introduction to the
  Theory of Numbers* as the third book: its book map (406 results: 194 proved, 4 proved in part, 191 in Mathlib) and 10 new headline statements
  (`Challenge_NivenZuckermanMontgomery.lean`); refreshed maps of Hardy–Wright and Ireland–Rosen
  (32 more rows linked to theorems of the library: Hardy–Wright 279 proved and 14 in part, was 266 and 9;
  Ireland–Rosen 120 and 5, was 109 and 3); the 16
  headlines of 0.1.0 unchanged. The comparator check stays one per book (now four, run as a matrix in CI); no file
  imports all of Mathlib.

**Not in this release** (planned for later releases): Chapters 12 to 14 and 18 to 20 of Ireland–Rosen (algebraic number theory, the Stickelberger relation and Eisenstein
reciprocity, elliptic curves); the analytic books (Apostol, Davenport), planned for a separate library
analytic-number-theory-lean.

## License

Apache License 2.0; see [LICENSE](LICENSE). Files ported from Tau Ceti are Apache 2.0, copyright the Tau Ceti
contributors.
