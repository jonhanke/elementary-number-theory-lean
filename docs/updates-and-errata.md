# Updates and errata to the source books

Each entry: the source and its locator, what is printed, what is true, and the Lean evidence.

## Hardy and Wright, *An Introduction to the Theory of Numbers*, 6th edition (2008) [hardywright2008]

### Theorems 268 and 269 (§ 16.5, printed page 307, pdf page 326): the conclusion fails for 0 < x < 1

- **Printed.** Theorem 268: if `G(x) = ∑_{n=1}^{[x]} F(x/n)` for all positive `x`, then
  `F(x) = ∑_{n=1}^{[x]} μ(n) G(x/n)`. Theorem 269 is the converse, also "for all positive `x`".
  The book's footnote says that an empty sum is `0`, "thus `G(x) = 0` if `0 < x < 1`".
- **Error.** For `0 < x < 1` both sums in the conclusion are empty, so Theorem 268 asserts `F(x) = 0`,
  which the hypothesis does not give (it constrains nothing about `F` on `(0, 1)`); likewise Theorem 269
  asserts `G(x) = 0` there. The book's proof (rearranging by `k = mn` and using
  `∑_{d ∣ k} μ(d) = [k = 1]`, Theorem 263, for `1 ≤ k ≤ [x]`) needs `[x] ≥ 1`. This is not a hypothesis the
  book states elsewhere: it explicitly allows all positive `x` and discusses the range `0 < x < 1` in
  the footnote.
- **Correct statement.** With the hypothesis for all `x > 0`, the conclusion holds for `x ≥ 1`
  (equivalently: for all `x > 0` if `F`, resp. `G`, vanishes on `(0, 1)`).
- **Counterexamples** (at `x = 1/2`): Theorem 268 with `F = 1`, `G(x) = [x]`; Theorem 269 with `G = 1`,
  `F(x) = ∑_{n ≤ x} μ(n)`.
- **Lean.** Correct forms `NTKB.HardyWright.moebius_inversion_floor` and
  `NTKB.HardyWright.moebius_inversion_floor_converse`
  (`NTKB/Elementary/HardyWright/ArithmeticFunctions/Inversion.lean`); the printed forms are refuted by
  `NTKB.HardyWright.not_moebius_inversion_floor_all_pos` and
  `NTKB.HardyWright.not_moebius_inversion_floor_converse_all_pos`
  (`NTKB/Elementary/HardyWright/ArithmeticFunctions/InversionCounterexample.lean`).
- Harmless in the book's later use (the formulae are applied for `x ≥ 1`).

### Theorem 20 (§ 2.6, printed page 21, pdf page 40): the first inequality fails for 1 < x < 2

- **Printed.** `π(x) ≥ log x / (2 log 2)` `(x ≥ 1)`; `p_n ≤ 4^n`. Here `π(x)` is the number of primes
  not exceeding the real number `x` (§ 1.5).
- **Error.** For `1 < x < 2`, `π(x) = 0` while `log x / (2 log 2) > 0`; e.g. `x = 3/2`. The proof takes
  `N(x) = x`, i.e. `x` an integer.
- **Correct statement.** The inequality for integers `x ≥ 1`, equivalently `π(x) ≥ log [x] / (2 log 2)`
  for real `x ≥ 1`.
- **Lean.** Correct form `NTKB.HardyWright.primeCounting_ge_log_div_and_nth_prime_lt`
  (`NTKB/Elementary/HardyWright/PrimeDistribution/Elementary.lean`, with `⌊x⌋`, and `p_n < 4^n`);
  the printed form is refuted by `NTKB.HardyWright.not_primeCounting_ge_log_div_real`
  (`NTKB/Elementary/HardyWright/Wave2Errata.lean`).
- Harmless for the book's use (`π(10^9) ≥ 15`).

### (13.7.11) (§ 13.7, printed page 260, pdf page 279): the formula for u is misprinted

- **Printed.** Euler's parametric solution of `x⁴ + y⁴ = u⁴ + v⁴` with
  `u = a⁷ + a⁵b² − 2a³b⁴ + 3a²b⁵ + ab⁶`, the same polynomial as `x`.
- **Error.** Then `u = x` and the identity would need `y⁴ = v⁴`, which fails: at `a = b = 1`,
  `(x, y, u, v) = (4, −2, 4, 4)` and `4⁴ + 2⁴ ≠ 4⁴ + 4⁴`.
- **Correct statement.** `u = a⁷ + a⁵b² − 2a³b⁴ − 3a²b⁵ + ab⁶`. The book's example `a = 1, b = 2`
  (`133⁴ + 134⁴ = 158⁴ + 59⁴`) agrees with the corrected sign.
- **Lean.** `NTKB.HardyWright.euler_fourth_powers` (corrected identity, any commutative ring) and
  `NTKB.HardyWright.not_euler_fourth_powers_printed` (the printed one fails at `a = b = 1`).

### Notes to Chapter XIII (printed page 263, pdf page 282): the abc conjecture and Fermat's equation

- **Printed.** The abc conjecture: for `ε > 0` there is `K(ε)` with `c ≤ K(ε) r(abc)^{1+ε}` for all
  positive integers with `a + b = c`. Then, for Fermat's equation, `z^n ≤ K(ε) z^{3(1+ε)}`, and
  "choosing `ε = 1/2`" and `n ≥ 4`, `z^n ≤ K(1/2) z^{7/2} ≤ K(1/2) z^{7n/8}`.
- **Errors.** (1) The conjecture needs `a` and `b` coprime: as printed it is false (`a = b = 2^k`,
  `c = 2^{k+1}`, `r(abc) = 2`). (2) `3(1 + 1/2) = 9/2`, not `7/2`; with `ε = 1/2` and `n = 4` the
  argument gives nothing. The exponent `7/2` is `3(1 + 1/6)`.
- **Correct statement.** With coprimality in the conjecture and `ε = 1/6`, the argument gives
  `z^n ≤ K(1/6)^8` for coprime solutions with `n ≥ 4`, so finitely many.
- **Lean.** `NTKB.HardyWright.AbcConjecture` (named hypothesis, with coprimality),
  `NTKB.HardyWright.fermat_finite_of_abc` (with `ε = 1/6`);
  `NTKB.HardyWright.not_abc_without_coprime` refutes the printed form of the conjecture.

### Not errata (recorded so that they are not reported again)

- Theorem 97: the machine-read text prints "7 is a quadratic residue of primes 10n ± 1"; that is false
  (7 is not a square modulo 11), but the book's own proof in § 6.13 treats 5, so the "7" is a misreading of
  the scan, not of the book. Proved for 5: `NTKB.HardyWright.isSquare_five_iff`.
- Theorem 270: the book gives a sufficient convergence condition for one direction only and says "some
  care is required about convergence"; the formalization assumes the analogous condition for the converse
  (without it the converse fails: `g = 1`, `f = 0`, using `∑ μ(n) = 0`). An omitted hypothesis that the
  book flags, not an error.
- Theorems 160, 181 to 183, 203, 102, 103, (8.7.4): hypotheses read or slightly strengthened/weakened as
  listed in the notes of the coverage audit; none is false as printed.
- Theorem 398: the machine-read text gives `G(2p^θ(p − 1))`; the book has `G(½p^θ(p − 1)) ≥ ½(p^{θ+1} − 1)`
  (its example `G(10) ≥ 12` is `p = 5, θ = 1`). A misreading of the scan.

## Ireland and Rosen, *A Classical Introduction to Modern Number Theory*, 2nd edition (1990) [irelandrosen1990]

### Not errata (recorded so that they are not reported again)

- Proposition 8.4.1 (pdf page 110) and Theorem 5 of Chapter 8 (pdf page 115): the book prints `≤`
  (the machine-read text suggested `<`, which would fail for `n ≤ 2`, resp. `M = 0`). The library's forms
  `NTKB.IrelandRosen.norm_numSolDiag_fermat_sub_le`, `NTKB.IrelandRosen.numSolDiag_zero`,
  `NTKB.IrelandRosen.numSolDiag_of_ne_zero` are the printed statements.
