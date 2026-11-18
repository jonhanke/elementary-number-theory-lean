# Elementary number theory in Lean 4

[![Lean build](https://github.com/jonhanke/elementary-number-theory-lean/actions/workflows/build.yml/badge.svg)](https://github.com/jonhanke/elementary-number-theory-lean/actions/workflows/build.yml) [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24088043.svg)](https://doi.org/10.5281/zenodo.24088043)

A Lean 4 library (built on Mathlib) that formalizes three texts of elementary number theory item by item: Hardy
and Wright's *An Introduction to the Theory of Numbers* (6th edition), Ireland and Rosen's *A Classical Introduction
to Modern Number Theory* (Chapters 1 to 11, 15 and 16, and the results of Chapter 13, section 1 and of Chapters 17
and 18 proved here) and Niven,
Zuckerman and Montgomery's *An Introduction to the Theory of Numbers* (5th edition), together with the special values
of Dirichlet $`L`$-functions at the integers. The Lean library is called `NTKB`; the repository is
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
  *conditional* (in this release three rows: one, in a note of Hardy–Wright, assumes the abc conjecture, and two
  headlines, Ireland–Rosen's Propositions 17.9.1 and 17.10.1, assume Fueter's classification of the torsion points of
  $`y^2 = x^3 + k`$; see [Conditional theorems](#conditional-theorems)). Conjectures are stated, never assumed as true.
- **Comparison**: [docs/results/comparison.md](docs/results/comparison.md) says, for each headline, what Mathlib,
  [Tau Ceti](https://github.com/TauCetiProject/TauCeti) and
  [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) already have and what this library
  adds. This library depends on Mathlib only.

## What's new in 0.5.0

- **Theorems 7 and 8 of Ireland–Rosen, Chapter 18, at every prime:** for $`y^2 = x^3 - c^4Dx`$ ($`D`$ fourth-power
  free) and $`y^2 = x^3 + c^6D`$ ($`D`$ sixth-power free), Mathlib's local polynomial at every prime is the Euler
  factor of $`L(s, \chi)`$ at the primes above it, the bad primes and the primes dividing $`c`$ included, with one
  exception for Theorem 8 at $`p = 2`$, $`D \equiv 16 \pmod{64}`$ (see [Known restrictions](#known-restrictions)). On
  the way: the local polynomial is unchanged by a change of variables, and is $`1`$ at a prime where no integral model
  with smaller discriminant exists and the reduction is additive (minimality checked on the congruences modulo
  $`2^4`$, $`2^6`$, $`3^6`$).
- **Sums of fourteen and sixteen squares** (beyond Hardy–Wright, § 20.13): $`r_{14}(n)`$ and $`r_{16}(n)`$ as an
  Eisenstein part plus the coefficients of the cusp forms $`\theta^2\eta^{12}`$ and $`\theta^4\eta^{12}`$ on
  $`\Gamma_0(4)`$, by modular forms of level one as for $`r_6`$ to $`r_{12}`$.
- **Congruent numbers and the curves with complex multiplication** (Hardy–Wright, Chapter 25): a positive rational
  $`n`$ is congruent if and only if $`y^2 = x^3 - n^2x`$ has a rational point with $`y \ne 0`$, if and only if it has
  one with $`x, y > 0`$ (§ 25.1); the endomorphisms $`[i] : (x, y) \mapsto (-x, iy)`$ and
  $`[\rho] : (x, y) \mapsto (\rho x, y)`$ of $`y^2 = x^3 + Ax`$ and $`y^2 = x^3 + B`$ are additive maps of the point
  groups with $`[i]^2 = -1`$ and $`[\rho]^2 + [\rho] + 1 = 0`$ (§ 25.2, in part: that these are all the endomorphisms
  is not formalized); and the bijection between $`X^3 + Y^3 = A`$ and $`y^2 = x^3 - 432A^2`$, $`x \ne 0`$
  (Theorem 465).
- **Four new headline statements** (two of Ireland–Rosen, two of Hardy–Wright; marked "new in 0.5.0" below); the 45
  headlines of 0.1.0 to 0.4.1 are unchanged. Maps: Hardy–Wright 630 results (288 proved, 14 in part, 1 conditional; was 628, 284,
  13, 1), Ireland–Rosen 415 (174 proved, 8 in part, 2 conditional; unchanged: Theorems 7 and 8 stay *in part* until
  the identity of Dirichlet series is assembled).
- Not published: the library's historical formalizations (rounds 1 to 7, results from Dickson's *History* and
  Gauss's *Disquisitiones*) are not part of this release, as before.

## What's new in 0.4.1

- **Liouville's ten-square theorem** (beyond Hardy–Wright, § 20.13, which gives $`r_6`$ and $`r_8`$): for $`n \ge 1`$,
  $`5r_{10}(n) = 4\sum_{d \mid n}\chi(d)d^4 + 64\sum_{d \mid n}\chi(n/d)d^4 + 8\sum_{N(a) = n}a^4`$, the last sum over the
  Gaussian integers $`a`$ of norm $`n`$. Stated only in 0.4.0, now proved: the transformation law of the theta series
  $`\sum_{a \in \mathbb Z[i]}a^4q^{N(a)}`$ under $`\tau \mapsto -1/\tau`$ comes from Mathlib's functional equation of
  the two-variable Jacobi theta function, and the identity from modular forms of level one, as for $`r_6`$ and
  $`r_{12}`$.
- **Theorems 7 and 8 of Ireland–Rosen, Chapter 18, at more primes:** at the primes $`p \mid 2D`$ (resp. $`p \mid 6D`$)
  with $`p^{12}`$ not dividing the discriminant, Mathlib's local polynomial of the curve is $`1`$ (the reduction is
  additive) and the Hecke character vanishes on the primes above $`p`$, so the two Euler factors agree there too. On
  the way: for a Weierstrass curve over $`\mathbb Z`$, the local polynomial is $`1`$ at a prime $`p`$ dividing
  $`\Delta`$ and $`c_4`$ with $`p^{12} \nmid \Delta`$.
- **Propositions 17.9.1 and 17.10.1 of Ireland–Rosen** (*conditional*): one rational point on $`x^3 + y^3 = a`$
  ($`a > 2`$ cube free), or one with $`xy \ne 0`$ on $`y^2 = x^3 + k`$ ($`k`$ sixth-power free, $`k \ne 1, -432`$), gives
  infinitely many, from Fueter's classification of the rational points of finite order on $`y^2 = x^3 + k`$, a named
  input that the library does not prove (see [Conditional theorems](#conditional-theorems)).
- **Five new headline statements** (four of Ireland–Rosen, two of them conditional; one of Hardy–Wright; marked "new in
  0.4.1" below); the 40 headlines of 0.1.0 to 0.4.0 are unchanged. Maps: Ireland–Rosen 415 results (174 proved, 8 in
  part, 2 conditional; was 413, 174, 8, 0), Hardy–Wright 628 (284 proved, 13 in part, 1 conditional; was 283).

## What's new in 0.4.0

- **Quadratic fields with no assumed input** (Ireland–Rosen, Chapter 13, § 1): the ring of integers, the
  discriminant and the decomposition law of $`\mathbb Q(\sqrt d)`$, the prime 2 included, proved from Mathlib's
  `QuadraticAlgebra`; every quadratic number field is $`\mathbb Q(\sqrt D)`$ with $`D`$ a fundamental discriminant;
  the units of the imaginary quadratic fields. With them, the two cited results that 0.3.0 assumed (the discriminants
  of the quadratic fields, and the number of ideals of norm $`n`$) are theorems, and
  $`h(-p) \equiv -2B_{(p+1)/2} \pmod p`$ holds for the class number of the field itself (a headline).
- **Hecke characters of the curves with complex multiplication** (Ireland–Rosen, Chapter 18, § 5, Theorems 7 and 8):
  the Hecke characters $`\chi`$ of $`\mathbb Q(i)`$ and $`\mathbb Q(\omega)`$ attached to $`y^2 = x^3 - Dx`$ and
  $`y^2 = x^3 + D`$ (completely multiplicative functions of ideals with $`N(\chi(A)) = N(A)`$) and, at every prime
  $`p \nmid 2D`$ (resp. $`p \nmid 6D`$), the equality of Mathlib's local factor of $`L(E, s)`$
  (`WeierstrassCurve.localPolynomial`) with the Euler factor of $`L(s, \chi)`$. On the way: for a Weierstrass curve
  over $`\mathbb Z`$, the local polynomial at a prime of good reduction is $`1 - a_pX + pX^2`$ with
  $`a_p = p - \#\{\text{affine points mod } p\}`$.
- **Integral points and class numbers** (Ireland–Rosen, Proposition 17.10.2): $`y^2 = x^3 - d`$ and the class number
  of $`\mathbb Q(\sqrt{-d})`$.
- **Sums of six and twelve squares** (Hardy–Wright, Section 20.13, and beyond the book): Jacobi's formula for
  $`r_6(n)`$ and Glaisher's formula for $`r_{12}(n)`$ (with the coefficients of $`\eta(2z)^{12}`$), both by modular
  forms of level one, as for $`r_8`$ in 0.3.0. Liouville's formula for $`r_{10}(n)`$ is stated, not proved (proved in
  0.4.1).
- **Eight new headline statements** (six of Ireland–Rosen, two of Hardy–Wright; marked "new in 0.4.0" below); the 32
  headlines of 0.1.0 to 0.3.0 are unchanged. Maps: Ireland–Rosen 413 results (174 proved, 8 in part, none
  conditional; was 404, 167, 5, 1), Hardy–Wright 628 (283 proved, 13 in part, 1 conditional; was 626, 281, 14, 1).

## The books

| book | rows | proved | proved in part | conditional | in Mathlib | other | proved here, also elsewhere |
|---|---|---|---|---|---|---|---|
| [G. H. Hardy and E. M. Wright, *An Introduction to the Theory of Numbers* (6th ed., 2008)](docs/results/books/hardy-wright.md) | 630 | 288 | 14 | 1 | 178 | 149 | 79 |
| [K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory* (2nd ed., 1990), Chapters 1–11, 15, 16 and the results of Chapter 13 §1 and Chapters 17 and 18 proved here](docs/results/books/ireland-rosen.md) | 415 | 174 | 8 | 2 | 178 | 53 | 67 |
| [I. Niven, H. S. Zuckerman and H. L. Montgomery, *An Introduction to the Theory of Numbers* (5th ed., 1991)](docs/results/books/niven-zuckerman-montgomery.md) | 406 | 194 | 4 | 0 | 191 | 17 | 84 |
| [Special values of Dirichlet $L$-functions and Gauss's sign of quadratic Gauss sums](docs/results/books/special-values.md) | 25 | 25 | 0 | 0 | 0 | 0 | 3 |

*Proved*: proved with only the standard axioms and no unproved input. *Proved in part*: a part, a special case or one instance is proved. *Conditional*: proved from a named unproved input (here the abc conjecture, in a note of Hardy–Wright; since 0.4.0 the two inputs of the class number formula of quadratic fields are proved, so Ireland–Rosen's congruence h(-p) ≡ -2B_{(p+1)/2} (mod p) holds unconditionally). *In Mathlib*: Mathlib (a dependency) has the result; the map names the Mathlib declaration. *Other*: refuted as stated in the book (the corrected form is proved), in Tau Ceti or PrimeNumberTheoremAnd only (not dependencies), partly formalized elsewhere, or not formalized (see each map). *Proved here, also elsewhere*: rows proved (in whole or in part) here whose result, a part of it or a closely related statement is also in Mathlib, Tau Ceti or PrimeNumberTheoremAnd; each map names those declarations in its column *Also in*. Rows that are not results (definitions, remarks, history, open problems) are omitted from the maps.

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
- **The three-square theorem** (new in 0.3.0): a natural number is a sum of three squares if and only if it is not
  of the form $`4^a(8m+7)`$ (`three_squares`, Section 20.10; the book states it without proof). Proved by
  Dirichlet's method: ternary forms of determinant 1, Minkowski's convex body theorem and Dirichlet's theorem on
  primes in progressions (both in Mathlib). Related: Mathlib has the two- and four-square theorems, not this one.
- **Jacobi's eight-square theorem** (new in 0.3.0): for $`n \ge 1`$, the number of $`z \in \mathbb Z^8`$ with
  $`z_1^2 + \dots + z_8^2 = n`$ is $`16\sum_{d \mid n}(-1)^{n+d}d^3`$ (`jacobi_eight_squares`, Section 20.13, stated
  without proof in the book). Proved from $`\theta^8 = (E_4(\tau/2) - 2E_4(\tau) + 16E_4(2\tau))/15`$ with Mathlib's
  modular forms of level one. Related: Tau Ceti has theta series of lattices and $`r(2m) = 240\sigma_3(m)`$ for the
  $`E_8`$ root lattice, not the count for $`\mathbb Z^8`$.
- **Jacobi's six-square theorem** (new in 0.4.0): for $`n \ge 1`$, the number of $`z \in \mathbb Z^6`$ with
  $`z_1^2 + \dots + z_6^2 = n`$ is $`16\sum_{d \mid n}\chi(n/d)d^2 - 4\sum_{d \mid n}\chi(d)d^2`$, $`\chi`$ the
  nontrivial character modulo 4 (`jacobi_six_squares`, Section 20.13, stated without proof in the book). Proved from
  an identity between $`\theta^6`$ and a lattice sum of weight 3, by modular forms of level one. Related: neither
  Mathlib nor Tau Ceti has the count.
- **Glaisher's twelve-square theorem** (new in 0.4.0, beyond the book): for $`n \ge 1`$,
  $`r_{12}(n) = 8\sum_{d \mid n}(-1)^{n+d+n/d+1}d^5 + 16a(n)`$, where $`\sum a(n)q^n = q\prod_{m \ge 1}(1 - q^{2m})^{12}`$
  is $`\eta(2z)^{12}`$, the cusp form of weight 6 and level 4 (`glaisher_twelve_squares`; J. W. L. Glaisher, 1907).
  The first $`r_k`$ here with a cusp form. Related: Tau Ceti has theta series of lattices as modular forms, not this
  count.
- **Liouville's ten-square theorem** (new in 0.4.1, beyond the book): for $`n \ge 1`$,
  $`5r_{10}(n) = 4\sum_{d \mid n}\chi(d)d^4 + 64\sum_{d \mid n}\chi(n/d)d^4 + 8\sum_{x^2 + y^2 = n}(x^4 - 6x^2y^2 + y^4)`$,
  $`\chi`$ the nontrivial character modulo 4 (`liouville_ten_squares`; J. Liouville, 1866), by a theta series of
  weight 5 with the harmonic polynomial $`\operatorname{Re} a^4`$ and modular forms of level one. Related: neither Mathlib
  nor Tau Ceti has the count.
- **The fourteen- and sixteen-square formulas** (new in 0.5.0, beyond the book): for $`n \ge 1`$,
  $`61r_{14}(n) = 4\big(64\sum_{d \mid n}\chi(n/d)d^6 - \sum_{d \mid n}\chi(d)d^6\big) + 1456c_{14}(n)`$ and
  $`17r_{16}(n) = 32\sum_{d \mid n}(-1)^{n+d}d^7 + 512c_{16}(n)`$, where $`c_{14}(n)`$ and $`c_{16}(n)`$ are the
  coefficients of the cusp forms $`\theta^2\eta^{12}`$ (weight 7) and $`\theta^4\eta^{12}`$ (weight 8) on
  $`\Gamma_0(4)`$, written as $`\sum_{i \le n}r_2(i)a(n-i)`$ and $`\sum_{i \le n}r_4(i)a(n-i)`$ with $`a(n)`$ the
  coefficients of $`q\prod_{m \ge 1}(1 - q^{2m})^{12}`$ (`glaisher_fourteen_squares`, `glaisher_sixteen_squares`).
  Proved by the level-one method of
  $`r_{10}`$ and $`r_{12}`$. The constants are the library's own derivation (see
  [Known restrictions](#known-restrictions)). Related: neither Mathlib nor Tau Ceti has these counts.

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
- **Two is a cubic residue exactly when $`p = C^2 + 27D^2`$** (new in 0.3.0): for a prime $`p \equiv 1 \pmod 3`$,
  $`x^3 \equiv 2 \pmod p`$ is solvable if and only if $`p = C^2 + 27D^2`$ with integers $`C, D`$ (`cube_eq_two_iff`,
  Proposition 9.6.2), from the law of cubic reciprocity and its supplement, proved in the library. Related: Tau Ceti
  has cubic reciprocity (`IsPrimaryEisenstein.cubic_reciprocity`), not this criterion.
- **The points of $`y^2 = x^3 - Dx`$ over $`\mathbb F_p`$** (new in 0.3.0): for a prime $`p \equiv 1 \pmod 4`$,
  $`p = \pi\bar\pi`$ with $`\pi`$ primary in $`\mathbb Z[i]`$ and $`p \nmid D`$, the number of points (with the point
  at infinity) is $`p + 1 - \overline{\chi_\pi(D)}\,\pi - \chi_\pi(D)\,\bar\pi`$, $`\chi_\pi`$ the quartic residue
  symbol (`points_y_sq_eq_x_cube_sub_D_x`, Chapter 18, § 4, Theorem 5). Related: Tau Ceti has Hasse's bound for every
  elliptic curve over a finite field (`WeierstrassCurve.hasse_bound`), not this formula.
- **The Kummer congruences** (new in 0.3.0): for a prime $`p`$, $`e \ge 1`$ and positive even $`m, m'`$ with
  $`p - 1 \nmid m`$ and $`m' \equiv m \pmod{\varphi(p^e)}`$,
  $`(1 - p^{m'-1})B_{m'}/m' \equiv (1 - p^{m-1})B_m/m \pmod{p^e}`$ (`kummer_congruences`, Chapter 15, § 2, Theorem 5).
  Related: Mathlib has the theorem of von Staudt and Clausen (`vonStaudt_clausen`), not these congruences.
- **The class number of $`\mathbb Q(\sqrt{-p})`$ modulo $`p`$** (new in 0.3.0): for a prime $`p \equiv 3 \pmod 4`$,
  $`p > 3`$, Jacobi's expression $`h = -\frac1p\sum_{j=1}^{p-1} j\left(\frac jp\right)`$ satisfies
  $`h \equiv -2B_{(p+1)/2} \pmod p`$ (`class_number_bernoulli`, Chapter 15, § 2). That $`h`$ is the class number is
  Jacobi's class number formula, which the book cites; since 0.4.0 it is proved, see the next item. Related:
  Tau Ceti has the class number formula of imaginary quadratic fields, not this congruence.
- **The class number of $`\mathbb Q(\sqrt{-p})`$ modulo $`p`$, for the field** (new in 0.4.0): for a prime
  $`p \equiv 3 \pmod 4`$, $`p > 3`$, and the quadratic field $`K`$ of discriminant $`-p`$,
  $`h(K) \equiv -2B_{(p+1)/2} \pmod p`$ with Mathlib's class number $`h(K)`$, with no assumed input
  (`class_number_bernoulli_field`). Related: neither Mathlib nor Tau Ceti has the congruence.
- **The Hecke character of $`y^2 = x^3 - Dx`$** (new in 0.4.0; Chapter 18, § 5, Theorem 7): for every prime
  $`p \nmid 2D`$, Mathlib's local polynomial of the curve at $`p`$ is $`(1 - \chi(\pi)X)(1 - \chi(\bar\pi)X)`$ if
  $`p = \pi\bar\pi`$ ($`\pi`$ primary in $`\mathbb Z[i]`$) and $`1 - \chi((p))X^2`$ if $`p \equiv 3 \pmod 4`$, where
  $`\chi((\alpha)) = \overline{(D/\alpha)_4}\,\alpha`$ is the book's Hecke character of $`\mathbb Q(i)`$
  (`hecke_character_quartic_curve_split`, `hecke_character_quartic_curve_inert`): the Euler factors of $`L(E, s)`$
  and $`L(s, \chi)`$ agree at every $`p \nmid 2D`$. Related: Mathlib has the local polynomials and the $`L`$-function
  of a Weierstrass curve, and Hecke characters, as definitions; Tau Ceti has Hecke $`L`$-functions and the complex
  multiplication of $`y^2 = x^3 + ax`$; neither links the $`L`$-function of a curve to a Hecke character.
- **The Hecke character of $`y^2 = x^3 + D`$** (new in 0.4.0; Chapter 18, § 5, Theorem 8): the same over
  $`\mathbb Z[\omega]`$ with the sextic residue symbol, at every prime $`p \nmid 6D`$
  (`hecke_character_cubic_curve_split`, `hecke_character_cubic_curve_inert`).
- **The same at the primes of additive reduction** (new in 0.4.1): for $`p \mid 2D`$ with $`p^{12} \nmid 64D^3`$ (resp.
  $`p \mid 6D`$ with $`p^{12} \nmid 432D^2`$), Mathlib's local polynomial of the curve at $`p`$ is $`1`$ and $`\chi`$ is
  $`0`$ on every prime of $`\mathbb Z[i]`$ (resp. $`\mathbb Z[\omega]`$) above $`p`$, so both Euler factors are $`1`$
  (`hecke_character_quartic_curve_bad`, `hecke_character_cubic_curve_bad`). Related: Mathlib defines the local
  polynomial and the reduction types; it does not prove the value at an additive prime.
- **Theorems 7 and 8 at every prime** (new in 0.5.0): for $`y^2 = x^3 - c^4Dx`$ with $`D`$ fourth-power free and
  $`c \ne 0`$, Mathlib's local polynomial at every prime $`p`$ is the Euler factor of $`L(s, \chi)`$ at the primes above
  $`p`$ ($`\chi`$ the Hecke character of $`D`$): $`1`$ for $`p \mid 2D`$, and the split and inert factors above
  (`hecke_character_quartic_curve_every_prime`); the same for $`y^2 = x^3 + c^6D`$ with $`D`$ sixth-power free
  (`hecke_character_cubic_curve_every_prime`), except at $`p = 2`$ for $`D \equiv 16 \pmod{64}`$, where the curve has
  good reduction and the local polynomial is $`1 + 2X^2`$ while the book's character vanishes at 2 (see
  [Known restrictions](#known-restrictions)). The book compares the good primes only. Related: Tau Ceti now has general
  facts on the local polynomial (its value at a prime of additive reduction); neither Mathlib nor Tau Ceti links it to
  a Hecke character.
- **Integral points on $`y^2 = x^3 - d`$** (new in 0.4.0; Proposition 17.10.2): for squarefree $`d > 1`$ with
  $`d \equiv 1, 2 \pmod 4`$ and $`3`$ not dividing the class number of $`\mathbb Q(\sqrt{-d})`$, the equation has an
  integral solution if and only if $`d = 3t^2 \pm 1`$ for an integer $`t`$ (`mordell_class_number`), by the book's
  proof (the ring of integers $`\mathbb Z[\sqrt{-d}]`$, the cube of an ideal, principal because $`3 \nmid h`$).
  Related: neither Mathlib nor Tau Ceti has this criterion.
- **Infinitely many rational points from one** (new in 0.4.1; Propositions 17.9.1 and 17.10.1; *conditional* on the
  named input `NTKB.IrelandRosen.CM.MordellTorsionInput`): if $`k`$ is sixth-power free, $`k \ne 1, -432`$, and
  $`y^2 = x^3 + k`$ has a rational solution with $`xy \ne 0`$, it has infinitely many (`infinite_points_mordell`); if
  $`a > 2`$ is cube free and $`x^3 + y^3 = a`$ has a rational solution, it has infinitely many
  (`infinite_points_sum_cubes`, through the map $`(x, y) \mapsto (12a/(x + y), 36a(x - y)/(x + y))`$ to
  $`Y^2 = X^3 - 432a^2`$). Related: Tau Ceti has the Lutz–Nagell theorem, not Fueter's classification nor these
  statements; Mathlib has neither.

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
`NTKB.NZM.simultaneous_approximation_general`; Tau Ceti has Dirichlet's simultaneous approximation theorem). New in
0.3.0: the law of cubic reciprocity (`NTKB.IrelandRosen.Eisenstein.cubic_reciprocity`; Tau Ceti has it); Hasse's
bound for the curves $`y^2 = x^3 - Dx`$ and $`y^2 = x^3 + D`$ (`NTKB.IrelandRosen.abs_numPointsQuarticCurve_sub_le`,
`NTKB.IrelandRosen.abs_numPointsCubicCurve_sub_le`; Tau Ceti has Hasse's bound for every elliptic curve over a
finite field); Dirichlet's theorem in the form of Dirichlet density (`NTKB.IrelandRosen.hasDirichletDensity_modEq`;
Mathlib has the natural-density form). New in 0.4.0: the ring of integers, the discriminant and the decomposition
law of $`\mathbb Q(\sqrt d)`$, the prime 2 included (Ireland–Rosen 13.1.1 to 13.1.4,
`NTKB.IrelandRosen.isIntegral_iff_of_mod_four_ne_one`, `NTKB.IrelandRosen.discr_quadField`,
`NTKB.QuadraticField.exists_split`, `NTKB.QuadraticField.isPrime_of_inert`, `NTKB.QuadraticField.exists_ramified`;
Tau Ceti has them, by a different route).

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

## Conditional theorems

Theorems proved from a named input that the library does not prove. Two headlines are conditional (new in 0.4.1).

- **Ireland–Rosen, Propositions 17.9.1 and 17.10.1 (headlines `infinite_points_sum_cubes`, `infinite_points_mordell`):**
  proved from the named input `NTKB.IrelandRosen.CM.MordellTorsionInput`, Fueter's classification (1930; see Cassels,
  *Lectures on Elliptic Curves*, § 14): a rational point $`(x, y)`$ with $`xy \ne 0`$ of finite order on
  $`y^2 = x^3 + k`$ exists only if $`k = d^6`$ or $`k = -432d^6`$. It follows from the Lutz–Nagell theorem and a finite
  case analysis, not formalized here. The input is a hypothesis of the two headlines, never an axiom.

- **Hardy–Wright, notes to Chapter XIII (the abc conjecture):** the finiteness of the set of coprime solutions of
  Fermat's equation $`x^n + y^n = z^n`$ with $`n \ge 4`$ (all exponents together) is proved from the (corrected) abc
  conjecture, an open problem, which is the hypothesis `NTKB.HardyWright.AbcConjecture` of
  `NTKB.HardyWright.fermat_finite_of_abc`; the conjecture is stated, not assumed.

Liouville's formula for $`r_{10}(n)`$, stated only in 0.4.0, is proved in 0.4.1 (headline `liouville_ten_squares`).

## Known restrictions

Results of the books that the library proves only in part, or under a hypothesis that the book does not make. Each
is marked in the book maps.

- **Ireland–Rosen, Chapter 18, Theorems 7 and 8 (headlines):** since 0.5.0 the Euler factors of $`L(E, s)`$ and
  $`L(s, \chi)`$ agree at every prime, with one exception: for $`y^2 = x^3 + c^6D`$ at $`p = 2`$ with
  $`D \equiv 16 \pmod{64}`$ (for example $`D = -432`$, the curve $`x^3 + y^3 = 1`$) the curve has good reduction and
  the local polynomial is $`1 + 2X^2`$, the Euler factor of a character with $`\chi((2)) = -2`$, while the book's
  character, defined modulo $`12D`$, vanishes at 2 (the book compares the good primes only). The identity of the
  $`L`$-functions as Dirichlet series (a sum over the ideals of $`\mathbb Z[i]`$, resp. $`\mathbb Z[\omega]`$) is not
  assembled from the Euler factors. Theorem 6 of the same section (the analytic continuation of $`L(s, \chi)`$) is
  not proved.
- **Sums of fourteen and sixteen squares (headlines, beyond the books):** the formulas were derived by the library's
  authors from the theta series (and checked numerically for $`n \le 59`$ before being proved); they have not been
  compared with Grosswald, *Representations of Integers as Sums of Squares* (1985), Chapter 9.
- **Hardy–Wright, § 25.2:** the maps $`[i]`$ and $`[\rho]`$ are endomorphisms with the stated relations; that the
  endomorphism rings are exactly $`\mathbb Z[i]`$ and $`\mathbb Z[\rho]`$ (stated without proof in the book) is not
  formalized.
- **Ireland–Rosen, Propositions 17.9.1 and 17.10.1 (headlines):** conditional on Fueter's classification of the
  torsion points (see [Conditional theorems](#conditional-theorems)); the book's own argument (denominators of the
  points of the tangent process) is not formalized.
- **Ireland–Rosen, Proposition 17.10.2 (headline):** the library proves the answer $`d = 3t^2 + 1`$ or
  $`d = 3t^2 - 1`$, which the book's proof gives ($`d = 2`$ needs the second form: $`5^2 = 3^3 - 2`$); whether the
  printed statement has both signs was not rechecked against the book.
- **Ireland–Rosen, Chapter 9, Theorem 1' (the supplement to cubic reciprocity):** proved in the rational case, the
  case the book proves; the case of a general primary prime (the book's Exercises 24 to 26 of Chapter 9) is not
  formalized.

## Layout

```
Challenge_<book>.lean   the headline statements of one book (proofs: deliberate sorry);
                        <book> = HardyWright, IrelandRosen, NivenZuckermanMontgomery, SpecialValues
Solution_<book>.lean    the same statements, proved from the library
comparator.json         the books, each with its lake comparator configuration comparator/<book>.json
formalization.yaml      scope, sources, divergences, provenance, review (formalization.yaml v0.4)
docs/results/books/     the book maps; docs/results/comparison.md: comparison with Mathlib, Tau Ceti and
                        PrimeNumberTheoremAnd
docs/updates-and-errata.md  corrections to the books
NTKB/
  Elementary/HardyWright/   Hardy-Wright, by topic (PrimeDistribution, Congruences, Residues, ContinuedFractions,
                            QuadraticFields, ArithmeticFunctions, Partitions, SumsOfSquares, ...)
  IrelandRosen/R1, ..., R4/ Ireland-Rosen: R1 Chapters 1-7 and 16; R2 Chapters 8, 10, 11 (Gauss and Jacobi sums,
                            equations over finite fields, zeta functions); R3 Chapters 9 and 17 (reciprocity, Z[i],
                            Diophantine equations); R4 (new in 0.3.0) cubic reciprocity in Z[omega] and Chapter 18
                            (points of y^2 = x^3 + D and y^2 = x^3 - Dx), Chapter 5 (quadratic residues for every
                            modulus), Chapter 15 (Bernoulli numbers), Chapter 16 (Dirichlet density); R5 (new in
                            0.4.0) Chapter 13, section 1 (quadratic fields), the Hecke characters of Chapter 18 and
                            Propositions 17.9.1, 17.10.1 (since 0.4.1) and 17.10.2
  Elementary/QuadraticField/ (new in 0.4.0) quadratic number fields: the model Q(sqrt D) of a fundamental
                            discriminant D, its ring of integers, the decomposition law and the ideal count
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

**Supporting files outside this release's books.** The books import 81 files of the library's treatment
of Apostol's *Introduction to Analytic Number Theory* and Davenport's *Multiplicative Number Theory* (Jacobi's triple
product, the Chebyshev functions and the equivalent forms of the prime number theorem, partial summation, the
partition function, the reduction of binary quadratic forms, and, since 0.3.0, Jacobi's class number formula of
imaginary quadratic fields, whose two inputs are proved since 0.4.0). They are shipped so that the library builds; the
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

Mathlib comes prebuilt from its cache; this library is built from source (375 modules, about 99,500 lines; no file
imports all of Mathlib, so only the Mathlib modules it needs are loaded). On 8 cores and 31 GB (2026-11-18), with
Mathlib's cache in place, `lake build` took about 9 minutes, with at most 7.7 GB of memory in use and a largest
single Lean process of 7.1 GB. Each `lake comparator` check (one book: build, export, and the Lean, NanoDa and
con-ron kernels) took 4 to 14 minutes, with at most 8.1 GB in use and a largest single process of at most 5.3 GB
(`con-ron`).

## Provenance

NTKB was written by AI, with Claude Code (Anthropic): almost entirely by Claude Opus 5.5, with a share by Claude
Sonnet 5.5, in October and November 2026. Jonathan Hanke designed and directed it: he chose the books, the results,
the conventions and the proof routes. The files under `NTKB/Port/` and the files of `NTKB/Elementary/SpecialValues/`
that say so in their headers contain code ported from Tau Ceti (by the Tau Ceti contributors, Apache 2.0). The proofs
are checked by the Lean kernel, and CI checks that the headline theorems use only the standard axioms. The 45
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
- **[v0.3.0](https://github.com/jonhanke/elementary-number-theory-lean/releases/tag/v0.3.0)** (Lean v4.36.0-rc2, Mathlib `1b1ccf4`), archived on Zenodo as [doi:10.5281/zenodo.24257518](https://doi.org/10.5281/zenodo.24257518):
  cubic reciprocity and curves over finite fields, quadratic residues for every modulus, Dirichlet density, the
  Bernoulli congruences of Ireland–Rosen § 15.2, the three-square theorem and Jacobi's eight-square theorem; 6 new headline statements (Ireland–Rosen 4, Hardy–Wright 2), the 26
  headlines of 0.1.0 and 0.2.0 unchanged; maps: Ireland–Rosen 404 results (167 proved, 5 in part, 1 conditional),
  Hardy–Wright 626 (281 proved, 14 in part, 1 conditional). The comparator check stays one per book (four, run as a
  matrix in CI); no file imports all of Mathlib.

- **[v0.4.0](https://github.com/jonhanke/elementary-number-theory-lean/releases/tag/v0.4.0)** (Lean v4.36.0-rc2, Mathlib `1b1ccf4`), archived on Zenodo as [doi:10.5281/zenodo.24285920](https://doi.org/10.5281/zenodo.24285920):
  quadratic fields with no assumed input (Ireland–Rosen 13.1), the Hecke characters of the curves
  $`y^2 = x^3 - Dx`$ and $`y^2 = x^3 + D`$ against Mathlib's local factors of $`L(E, s)`$ (Ireland–Rosen 18, Theorems 7
  and 8), Proposition 17.10.2, Jacobi's six-square and Glaisher's twelve-square theorems (see
  [What's new in 0.4.0](#whats-new-in-040)); 8 new headline statements (Ireland–Rosen 6, Hardy–Wright 2), the 32
  headlines of 0.1.0 to 0.3.0 unchanged; maps: Ireland–Rosen 413 results (174 proved, 8 in part, none conditional),
  Hardy–Wright 628 (283 proved, 13 in part, 1 conditional). The comparator check stays one per book (four, run as a
  matrix in CI); no file imports all of Mathlib.
- **[v0.4.1](https://github.com/jonhanke/elementary-number-theory-lean/releases/tag/v0.4.1)** (Lean v4.36.0-rc2, Mathlib `1b1ccf4`), archived on Zenodo as [doi:10.5281/zenodo.24301260](https://doi.org/10.5281/zenodo.24301260):
  Liouville's ten-square theorem, Theorems 7 and 8 of Ireland–Rosen 18 at the primes of additive reduction, and
  Propositions 17.9.1 and 17.10.1 conditional on Fueter's classification of the torsion points (see
  [What's new in 0.4.1](#whats-new-in-041)); 5 new headline statements (Ireland–Rosen 4, two of them conditional;
  Hardy–Wright 1), the 40 headlines of 0.1.0 to 0.4.0 unchanged; maps: Ireland–Rosen 415 results (174 proved, 8 in
  part, 2 conditional), Hardy–Wright 628 (284 proved, 13 in part, 1 conditional). The comparator check stays one per
  book (four, run as a matrix in CI); no file imports all of Mathlib.
- **[v0.5.0](https://github.com/jonhanke/elementary-number-theory-lean/releases/tag/v0.5.0)** (Lean v4.36.0-rc2, Mathlib `1b1ccf4`), archived on Zenodo as [doi:10.5281/zenodo.24333712](https://doi.org/10.5281/zenodo.24333712):
  Theorems 7 and 8 of Ireland–Rosen 18 at every prime (one exception for Theorem 8 at 2), the formulas for
  $`r_{14}(n)`$ and $`r_{16}(n)`$, congruent numbers and Hardy–Wright's Theorem 465 (see
  [What's new in 0.5.0](#whats-new-in-050)); 4 new headline statements (Ireland–Rosen 2, Hardy–Wright 2), the 45
  headlines of 0.1.0 to 0.4.1 unchanged; maps: Hardy–Wright 630 results (288 proved, 14 in part, 1
  conditional), Ireland–Rosen 415 (174 proved, 8 in part, 2 conditional). The comparator check stays one per book (four, run as a
  matrix in CI); no file imports all of Mathlib.

**Not in this release** (planned for later releases): Chapters 12, 14, 19 and 20 of Ireland–Rosen and the rest of
Chapter 13 (algebraic number theory, the Stickelberger relation and Eisenstein reciprocity, the arithmetic of
elliptic curves), and the results of Chapters 17 and 18 not proved here (Theorem 6 of Chapter 18; Propositions 17.9.1
and 17.10.1 are conditional). The analytic books (Apostol, Davenport) are in the
separate library analytic-number-theory-lean. The library's historical formalizations (results from Dickson's
*History of the Theory of Numbers* and Gauss's *Disquisitiones Arithmeticae*) are a separate Lean
library and are not published in this repository.

## License

Apache License 2.0; see [LICENSE](LICENSE). Files ported from Tau Ceti are Apache 2.0, copyright the Tau Ceti
contributors.
