# I. Niven, H. S. Zuckerman and H. L. Montgomery, *An Introduction to the Theory of Numbers* (5th ed., 1991): map to the Lean library

Each row is a result of the book, the Lean declarations that formalize it, and its status, computed from the Lean kernel (an audit of the axioms and hypotheses of every declaration): *proved* means proved with only the standard axioms and no unproved input; *proved in part* that a part, a special case or one instance is proved; *proved, conditional* that an unproved input (a named statement) is assumed; *refuted as stated in the book* that the library proves the printed statement false and proves a corrected form (see the errata in the README); *in Mathlib* that Mathlib (a dependency) has the result and the Lean name is Mathlib's. Results that are only in Tau Ceti or PrimeNumberTheoremAnd (which this library does not depend on) are marked so. The statements in the third column are short descriptions, not quotations; read the book for the exact wording. The column *Also in* credits other libraries: Mathlib, Tau Ceti or PrimeNumberTheoremAnd declarations that prove the result, a part of it, or a closely related statement (as recorded by the coverage audit). Pages are pages of the pdf file of the 5th edition; items are numbered by chapter, as in the book. Besides the numbered items, the map has rows for definitions and notions without a number that are Lean objects.

Rows: 406. proved: 194; in Mathlib: 191; partly in other libraries; not proved here: 16; proved in part: 4; not formalized: 1. Proved here and also in another library: 84.


## Chapter 1

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Definition 1.1 | 15 | b is divisible by a (a nonzero) if b = ax for an integer x; a divides b, a is a divisor of b, b is a multiple of a | `dvd_def`, `Dvd.intro` | in Mathlib |  |
| Definition (proper divisor) | 15 | If a divides b and 0 < a < b then a is a proper divisor of b | `Nat.properDivisors` | in Mathlib |  |
| Theorem 1.1 | 16 | Six divisibility properties: a divides b implies a divides bc; transitivity; linear combinations; a and b divide each other implies a = plus or minus b; positive a divides positive b implies a <= b; ma divides mb iff a divides b | `dvd_mul_of_dvd_left`, `dvd_trans`, `Dvd.dvd.linear_comb`, `dvd_antisymm`, `mul_dvd_mul_iff_left` | in Mathlib |  |
| Theorem 1.2 | 16 | Division algorithm: for a > 0 there are unique q, r with b = qa + r and 0 <= r < a, with 0 < r < a if a does not divide b | `div_add_mod` | in Mathlib |  |
| Definition (greatest integer function) | 17 | [x] denotes the largest integer not exceeding the real x | `Int.floor` | in Mathlib |  |
| Definition 1.2 | 18 | Common divisor, and the greatest common divisor (b, c) of integers not both zero (also for n integers) | `GCDMonoid`, `gcd_dvd_left`, `dvd_gcd_iff` | in Mathlib |  |
| Theorem 1.3 | 18 | The gcd g of b and c is a linear combination g = bx0 + cy0 | `gcd_eq_gcd_ab`, `gcd_eq_sum` | in Mathlib |  |
| Theorem 1.4 | 18 | gcd is (A) the least positive value of bx + cy and (B) the positive common divisor divisible by every common divisor | `NTKB.NZM.gcd_least_pos_comb` | proved | Mathlib: `dvd_gcd_iff`, Mathlib: `gcd_dvd_iff_exists` |
| Theorem 1.5 | 19 | gcd of b1,...,bn (not all zero) is a linear combination, the least positive value of the form, and the positive common divisor divisible by all common divisors | `Finset.gcd_eq_sum_mul`, `Finset.dvd_gcd_iff` | in Mathlib |  |
| Theorem 1.6 | 19 | For m > 0, (ma, mb) = m(a, b) | `gcd_mul_left` | in Mathlib |  |
| Theorem 1.7 | 19 | If d divides a and b with d > 0 then (a/d, b/d) = (a, b)/d; in particular (a/g, b/g) = 1 | `NTKB.NZM.gcd_div_of_dvd` | proved | Mathlib: `gcd_mul_left` |
| Theorem 1.8 | 20 | If (a, m) = (b, m) = 1 then (ab, m) = 1 | `IsCoprime.mul_left`, `Int.isCoprime_iff_gcd_eq_one` | in Mathlib |  |
| Definition 1.3 | 20 | a and b relatively prime if (a, b) = 1; relatively prime in pairs; also called coprime | `IsCoprime`, `Int.isCoprime_iff_gcd_eq_one`, `Nat.isCoprime_iff_coprime` | in Mathlib |  |
| Theorem 1.9 | 20 | (a, b) = (b, a) = (a, -b) = (a, b + ax) for any integer x | `NTKB.NZM.gcd_symm_neg_add_mul` | proved | Mathlib: `gcd_comm`, Mathlib: `gcd_neg`, Mathlib: `gcd_val` |
| Theorem 1.10 | 21 | If c divides ab and (b, c) = 1 then c divides a | `IsCoprime.dvd_of_dvd_mul_right`, `Nat.Coprime.dvd_mul_right` | in Mathlib |  |
| Theorem 1.11 | 22 | Euclidean algorithm: repeated division gives (b, c) as the last nonzero remainder, with x0, y0 by back substitution | `gcd_val`, `gcd_eq_gcd_ab` | in Mathlib |  |
| Definition 1.4 | 27 | Common multiple and least common multiple [a1,...,an] of nonzero integers | `lcm_dvd`, `lcm_dvd_iff`, `Finset.lcm_dvd_iff` | in Mathlib |  |
| Theorem 1.12 | 27 | Every common multiple of a1,...,an is a multiple of their lcm | `lcm_dvd`, `Finset.lcm_dvd_iff` | in Mathlib |  |
| Theorem 1.13 | 27 | For m > 0, [ma, mb] = m[a, b]; and [a, b](a, b) = abs(ab) | `lcm_mul_left`, `gcd_mul_lcm` | in Mathlib |  |
| Definition (parity) | 28 | Two integers have the same parity if both even or both odd, otherwise opposite parity | `Even`, `Odd`, `Int.even_or_odd` | in Mathlib |  |
| Definition (triangular numbers) | 30 | The triangular numbers 1, 3, 6, 10,... are n(n+1)/2 | `NTKB.NZM.triangular` | proved |  |
| Definition 1.5 | 31 | A prime is an integer p > 1 with no divisor d with 1 < d < p; a composite is an integer > 1 that is not prime | `Nat.Prime`, `Nat.prime_def` | in Mathlib |  |
| Theorem 1.14 | 31 | Every integer n > 1 is a product of primes | `Nat.prod_primeFactorsList`, `Nat.exists_prime_and_dvd` | in Mathlib |  |
| Definition (canonical factoring) | 32 | The representation of n as a product of primes powers is the canonical factoring | `Nat.factorization`, `Nat.primeFactorsList` | in Mathlib |  |
| Definition (prime in Z[sqrt -6]) | 33 | In the example domain, a number of norm > 1 that cannot be factored is called a prime in that domain | `Irreducible` | in Mathlib |  |
| Theorem 1.15 | 34 | If a prime p divides ab then p divides a or b; more generally p divides some factor of a product | `Nat.Prime.dvd_mul`, `Prime.dvd_prod_iff`, `Prime.dvd_finsetProd_iff` | in Mathlib |  |
| Theorem 1.16 | 34 | Fundamental theorem of arithmetic: factoring into primes is unique up to order | `Nat.primeFactorsList_unique`, `UniqueFactorizationMonoid.factors_unique` | in Mathlib |  |
| Theorem 1.17 | 36 | Euclid: there are infinitely many primes | `Nat.exists_infinite_primes` | in Mathlib |  |
| Theorem 1.18 | 37 | There are arbitrarily large gaps in the primes: for every k there are k consecutive composite integers | `NTKB.HardyWright.exists_consecutive_composites` | proved |  |
| Theorem 1.19 | 37 | For real y > 2, the sum of 1/p over primes p <= y is at least log log y - 1; so the series of 1/p diverges | `NTKB.NZM.sum_inv_primes_gt_log_log_sub_one` | proved | Mathlib: `not_summable_one_div_on_primes`, Mathlib: `Nat.Primes.not_summable_one_div`, PNT+: `sum_prime_div_eq_log_log` |
| Definition (Fermat numbers) | 44 | The Fermat numbers are F_n = 2^(2^n) + 1 | `Nat.fermatNumber` | in Mathlib |  |
| Definition (Mersenne numbers) | 44 | The Mersenne numbers are M_p = 2^p - 1 for a prime p | — | in Mathlib |  |
| Definition 1.6 | 46 | Binomial coefficient (a choose k) = a(a-1)...(a-k+1)/k! for real a and k >= 0 | `Nat.choose`, `Ring.choose` | partly in other libraries; not proved here |  |
| Theorem 1.20 | 46 | A set with n elements has exactly (n choose k) subsets of size k | `Finset.card_powersetCard` | in Mathlib |  |
| Theorem 1.21 | 47 | The product of any k consecutive integers is divisible by k! | `NTKB.NZM.factorial_dvd_prod_consecutive` | proved | Mathlib: `Nat.factorial_dvd_ascFactorial`, Mathlib: `Nat.factorial_dvd_descFactorial` |
| Theorem 1.22 | 47 | Binomial theorem: (x+y)^n = sum of (n choose k) x^k y^(n-k) | `add_pow`, `Commute.add_pow` | in Mathlib |  |
| Lemma 1.23 | 48 | For a real polynomial P(z) = sum a_k z^k, a_r = P^(r)(0)/r! | `Polynomial.coeff_iterate_derivative` | in Mathlib |  |
| Definition (integer-valued polynomial) | 49 | A polynomial taking integral values at integers is called integer-valued | `NTKB.NZM.IsIntegerValued` | proved |  |
| Definition (forward difference) | 53 | The k-th forward difference of a function f | — | in Mathlib |  |

## Chapter 2

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Corollary 2.30 | 106 | If d divides p-1 then x^d = 1 (mod p) has exactly d solutions | `NTKB.HardyWright.card_pow_eq_one_of_dvd`, `NTKB.IrelandRosen.card_pow_eq_one_zmod` | proved | Mathlib: `IsPrimitiveRoot.card_nthRoots_one`, Mathlib: `Polynomial.card_nthRoots` |
| Definition 2.1 | 59 | a is congruent to b mod m when m divides a-b | `Int.ModEq`, `Nat.ModEq` | in Mathlib |  |
| Theorem 2.1 | 59 | Congruence is an equivalence relation compatible with sums, products, passing to a divisor of the modulus, and multiplying modulus and sides by c | `Int.ModEq.symm`, `Int.ModEq.trans`, `Int.ModEq.add`, `Int.ModEq.mul`, `Int.ModEq.of_dvd`, `Int.ModEq.mul_left'`, `Int.modEq_iff_dvd` | in Mathlib |  |
| Theorem 2.2 | 59 | If a = b (mod m) then f(a) = f(b) (mod m) for f with integer coefficients | `Polynomial.sub_dvd_eval_sub` | in Mathlib |  |
| Theorem 2.3 | 60 | Cancellation: ax = ay (mod m) iff x = y (mod m/(a,m)); coprime case; x = y mod each m_i iff mod lcm | `NTKB.NZM.modEq_finset_lcm_iff`, `NTKB.HardyWright.modEq_mul_left_iff_modEq_div_gcd` | proved | Mathlib: `Int.ModEq.cancel_left_div_gcd`, Mathlib: `Nat.ModEq.cancel_left_div_gcd`, Mathlib: `Nat.ModEq.cancel_left_of_coprime`, Mathlib: `Int.modEq_and_modEq_iff_modEq_lcm`, Mathlib: `Nat.modEq_and_modEq_iff_modEq_lcm` |
| Definition 2.2 | 61 | y is a residue of x mod m; complete residue system; residue class | `NTKB.HardyWright.IsCompleteResidueSystem` | proved in part | Mathlib: `ZMod` |
| Theorem 2.4 | 61 | If b = c (mod m) then (b,m) = (c,m) | `Nat.ModEq.gcd_eq` | in Mathlib |  |
| Definition 2.3 | 61 | Reduced residue system: pairwise incongruent integers prime to m representing every class prime to m | `NTKB.HardyWright.IsReducedResidueSystem` | proved | Mathlib: `ZMod.unitOfCoprime`, Mathlib: `ZMod` |
| Theorem 2.5 | 62 | phi(m) is the number of integers 1..m prime to m | `Nat.totient`, `Nat.totient_eq_card_coprime` | in Mathlib |  |
| Theorem 2.6 | 62 | If (a,m)=1 then a times a complete (reduced) residue system is a complete (reduced) residue system | `NTKB.HardyWright.IsCompleteResidueSystem.mul`, `NTKB.HardyWright.IsReducedResidueSystem.mul` | proved | Mathlib: `ZMod.unitOfCoprime` |
| Theorem 2.7 | 62 | Fermat: a^(p-1) = 1 (mod p) for p not dividing a, and a^p = a (mod p) | `ZMod.pow_card`, `ZMod.pow_card_sub_one_eq_one`, `Int.ModEq.pow_card_sub_one_eq_one` | in Mathlib |  |
| Theorem 2.8 | 62 | Euler: a^phi(m) = 1 (mod m) when (a,m)=1 | `Nat.ModEq.pow_totient`, `ZMod.pow_totient` | in Mathlib |  |
| Theorem 2.9 | 63 | ax = 1 (mod m) is solvable iff (a,m)=1, and the solution is unique mod m | `ZMod.coe_mul_inv_eq_one`, `Nat.exists_mul_mod_eq_one_of_coprime`, `Nat.coprime_of_mul_modEq_one`, `ZMod.unitOfCoprime` | in Mathlib |  |
| Lemma 2.10 | 63 | For prime p, x^2 = 1 (mod p) iff x = +-1 (mod p) | `sq_eq_one_iff`, `mul_self_eq_one_iff` | in Mathlib |  |
| Theorem 2.11 | 64 | Wilson: (p-1)! = -1 (mod p) for p prime | `ZMod.wilsons_lemma`, `Nat.prime_iff_fac_equiv_neg_one` | in Mathlib |  |
| Theorem 2.12 | 64 | x^2 = -1 (mod p) is solvable iff p = 2 or p = 1 (mod 4) | `ZMod.exists_sq_eq_neg_one_iff` | in Mathlib |  |
| Lemma 2.13 | 65 | A prime p = 1 (mod 4) is a sum of two positive squares | `Nat.Prime.sq_add_sq` | in Mathlib |  |
| Lemma 2.14 | 66 | If a prime q = 3 (mod 4) divides a^2+b^2 then q divides a and q divides b | `NTKB.HardyWright.dvd_re_im_of_dvd_norm` | proved | Mathlib: `Nat.mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one`, Mathlib: `ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_coprime`, Mathlib: `Nat.eq_sq_add_sq_iff` |
| Theorem 2.15 | 66 | n is a sum of two squares iff every prime q = 3 (mod 4) occurs to an even power | `Nat.eq_sq_add_sq_iff` | in Mathlib |  |
| Theorem 2.16 | 72 | A solution of f(x) = 0 (mod m) is a solution mod every divisor d of m | `Int.ModEq.of_dvd` | in Mathlib |  |
| Theorem 2.17 | 73 | ax = b (mod m) is solvable iff (a,m) divides b, and then has (a,m) solutions mod m | `NTKB.HardyWright.exists_mul_modEq_iff_and_card`, `NTKB.Apostol.exists_mul_modEq_iff` | proved | Mathlib: `Int.ModEq.cancel_left_div_gcd`, Mathlib: `ZMod.coe_mul_inv_eq_one` |
| Theorem 2.18 | 75 | Chinese Remainder Theorem for pairwise coprime moduli: solutions exist and are unique mod the product | `Nat.chineseRemainder`, `Nat.chineseRemainderOfList`, `Nat.chineseRemainderOfList_modEq_unique`, `ZMod.chineseRemainder` | in Mathlib |  |
| Theorem 2.19 | 80 | phi is multiplicative on coprime arguments and phi(m) = product of p^a - p^(a-1) = m times product (1-1/p) | `Nat.totient_mul`, `Nat.totient_prime_pow`, `Nat.totient_eq_prod_factorization`, `Nat.totient_eq_mul_prod_factors` | in Mathlib |  |
| Theorem 2.20 | 81 | The number N(m) of roots of f mod m is multiplicative: N(m1 m2) = N(m1) N(m2) for coprime m1, m2 | `NTKB.HardyWright.rootCount_mul`, `NTKB.Apostol.card_roots_prod_eq` | proved |  |
| Lemma 2.21 | 90 | Probability that k independent choices from {1..n} are distinct is the product of (1 - j/n) | `NTKB.NZM.lemma_2_21` | proved | Mathlib: `Fintype.card_embedding_eq` |
| Lemma 2.22 | 95 | If k k' = 1 (mod phi(m)) and (a,m)=1 then a^(k k') = a (mod m) | `NTKB.NZM.pow_mul_modEq_self` | proved | Mathlib: `Nat.pow_totient_mod`, Mathlib: `Nat.pow_add_mul_totient_mod_eq`, Mathlib: `Nat.ModEq.pow_totient` |
| Theorem 2.23 | 98 | Hensel's lemma: a nonsingular root mod p^j lifts uniquely mod p^(j+1) | `NTKB.HardyWright.numLifts_eq_one`, `NTKB.Apostol.existsUnique_lift` | proved | Mathlib: `hensels_lemma`, Mathlib: `HenselianLocalRing.TFAE` |
| Theorem 2.24 | 100 | Lifting singular roots when j >= 2 tau + 1 where p^tau exactly divides f'(a) | `NTKB.NZM.lift_singular_root` | proved | Mathlib: `hensels_lemma` |
| Theorem 2.25 | 103 | A congruence of degree n >= p mod p is satisfied by every integer or is equivalent to a monic one of degree less than p | `NTKB.NZM.natDegree_modByMonic_lt_and_eval_eq`, `NTKB.NZM.eval_eq_zero_or_exists_monic` | proved |  |
| Theorem 2.26 | 104 | A congruence of degree n mod a prime has at most n solutions | `Polynomial.card_roots'` | in Mathlib |  |
| Corollary 2.27 | 105 | If b_n x^n + ... + b_0 = 0 (mod p) has more than n solutions then all b_j are divisible by p | `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero`, `Polynomial.card_roots'` | in Mathlib |  |
| Theorem 2.28 | 105 | Every function from residues mod p to residues mod p is a polynomial function of degree at most p-1 | `NTKB.NZM.exists_polynomial_eval_eq`, `NTKB.NZM.polynomial_eq_of_eval_eq` | proved | Mathlib: `Lagrange.eval_interpolate_at_node`, Mathlib: `Lagrange.degree_interpolate_lt` |
| Theorem 2.29 | 105 | A monic congruence f of degree n mod p has n solutions iff f divides x^p - x modulo p | `NTKB.NZM.card_roots_eq_natDegree_iff_dvd` | proved |  |
| Definition (probable prime and pseudoprime) | 88 | n is a probable prime to base 2 if 2^(n-1) = 1 (mod n); a composite probable prime is a pseudoprime | `Nat.ProbablePrime`, `Nat.FermatPsp` | in Mathlib |  |
| Definition (Carmichael number) | 70 | A composite m that is a pseudoprime to every base a prime to m | `Nat.IsCarmichael` | in Mathlib |  |
| Definition 2.6 | 108 | order of a modulo m is the least h>0 with a^h = 1 mod m (a belongs to exponent h) | — | in Mathlib |  |
| Lemma 2.31 | 109 | a^k = 1 mod m iff order h divides k | `orderOf_dvd_iff_pow_eq_one`, `orderOf_dvd_of_pow_eq_one` | in Mathlib |  |
| Corollary 2.32 | 109 | If (a,m)=1 the order of a modulo m divides phi(m) | `pow_totient`, `orderOf_dvd_of_pow_eq_one`, `orderOf_dvd_card` | in Mathlib |  |
| Lemma 2.33 | 109 | If a has order h then a^k has order h/(h,k) | `orderOf_pow'`, `orderOf_pow` | in Mathlib |  |
| Lemma 2.34 | 109 | If orders h,k of a,b are coprime then ab has order hk | `orderOf_mul_eq_mul_orderOf_of_coprime` | in Mathlib |  |
| Definition 2.7 | 110 | g is a primitive root mod m if its order mod m is phi(m) | `NTKB.Apostol.IsPrimitiveRootMod` | proved | Mathlib: `IsCyclic` |
| Lemma 2.35 | 110 | If q^a divides p-1 there are exactly q^a - q^(a-1) residues mod p of order q^a | `NTKB.NZM.card_orderOf_prime_pow_eq` | proved | Mathlib: `card_orderOf_eq_totient`, Mathlib: `isCyclic_units_prime` |
| Theorem 2.36 | 110 | A prime p has phi(p-1) primitive roots | `NTKB.NZM.card_primitiveRoots_prime` | proved | Mathlib: `isCyclic_units_prime`, Mathlib: `card_orderOf_eq_totient` |
| Definition 2.8 | 111 | a coprime to p is an n-th power residue mod p if x^n = a mod p is solvable | `NTKB.NZM.IsPowerResidue`, `NTKB.NZM.isPowerResidue_iff_pow_eq_one` | proved |  |
| Theorem 2.37 | 112 | x^n = a mod p has (n,p-1) solutions if a^((p-1)/(n,p-1)) = 1 mod p, else none | `NTKB.IrelandRosen.exists_pow_eq_iff_finiteField`, `NTKB.IrelandRosen.card_pow_eq_finiteField` | proved | Mathlib: `card_powMonoidHom_ker`, Mathlib: `card_powMonoidHom_range` |
| Corollary 2.38 | 112 | Euler's criterion: x^2 = a mod p solvable iff a^((p-1)/2) = 1 | `euler_criterion`, `euler_criterion_units` | in Mathlib |  |
| Theorem 2.39 | 113 | A prime p has phi(phi(p^2)) = (p-1)phi(p-1) primitive roots mod p^2 | `NTKB.NZM.card_primitiveRoots_prime_sq` | proved | Mathlib: `isCyclic_units_of_prime_pow`, Mathlib: `card_orderOf_eq_totient` |
| Theorem 2.40 | 113 | For odd p, a primitive root mod p^2 is a primitive root mod p^a for all a >= 3 | `NTKB.NZM.orderOf_intCast_eq_totient_of_sq` | proved | Mathlib: `isCyclic_units_of_prime_pow`, Mathlib: `orderOf_one_add_mul_prime_pow` |
| Theorem 2.41 | 115 | A primitive root mod m exists iff m = 1, 2, 4, p^a, 2p^a (p odd prime) | `isCyclic_units_iff`, `isCyclic_units_two_pow_iff`, `isCyclic_units_two_mul_iff_of_odd`, `not_isCyclic_units_eight` | in Mathlib |  |
| Corollary 2.42 | 115 | For m with a primitive root, x^n = a mod m has (n,phi(m)) solutions iff a^(phi(m)/(n,phi(m))) = 1, else none | `NTKB.IrelandRosen.exists_pow_eq_iff_of_isCyclic_units`, `NTKB.IrelandRosen.card_pow_eq_of_isCyclic_units` | proved | Mathlib: `card_powMonoidHom_ker`, Mathlib: `isCyclic_units_iff` |
| Theorem 2.43 | 116 | For a >= 3 the order of 5 mod 2^a is 2^(a-2); the numbers +-5^j form a reduced residue system and odd a = (-1)^i 5^j uniquely | `orderOf_unitFive`, `isComplement'_zpowers_unitFive_neg_one`, `disjoint_zpowers_unitFive_neg_one` | in Mathlib |  |
| Corollary 2.44 | 116 | For odd a and a >= 3: x^n = a mod 2^a has one solution for n odd; for n even, 2^(b+1) solutions iff a = 1 mod 2^(b+2), else none | `NTKB.NZM.existsUnique_pow_eq_two_pow_of_odd`, `NTKB.NZM.card_pow_eq_two_pow_of_even`, `NTKB.IrelandRosen.existsUnique_pow_eq_of_odd`, `NTKB.IrelandRosen.exists_pow_eq_iff_of_even`, `NTKB.IrelandRosen.card_pow_eq_of_even` | proved |  |
| Theorem 2.45 | 122 | If a, b have order 2^j (j>0) mod prime p then ab has order 2^j' with j' < j | `NTKB.NZM.exists_orderOf_mul_two_pow_lt` | proved |  |
| Definition 2.9 | 127 | a group: set closed under an associative operation with identity and inverses | `Group` | in Mathlib |  |
| Definition abelian group | 128 | a group is abelian if a*b = b*a for all a, b | `CommGroup` | in Mathlib |  |
| Definition order of a group | 128 | the number of elements of a finite group is its order | `Nat.card` | in Mathlib |  |
| Definition 2.10 | 129 | groups are isomorphic if a bijection preserves the operation | `MulEquiv` | in Mathlib |  |
| Theorem 2.46 | 130 | Any complete residue system mod m is a group under addition mod m; any two are isomorphic | — | in Mathlib |  |
| Theorem 2.47 | 132 | A reduced residue system mod m is a group of order phi(m) under multiplication mod m; any two are isomorphic | `card_units_eq_totient`, `Units` | in Mathlib |  |
| Theorem 2.48 | 133 | In a group ab = ac implies b = c (and ba = ca); in a finite group each element has a smallest positive r with a^r = e | `mul_left_cancel`, `mul_right_cancel`, `isOfFinOrder_of_finite`, `orderOf_pos` | in Mathlib |  |
| Definition 2.11 | 133 | element of finite order and its order; infinite order; cyclic group and generator | `IsOfFinOrder`, `IsCyclic` | in Mathlib |  |
| Theorem 2.49 | 134 | The order of an element of a finite group divides the group order; a^n = e | `orderOf_dvd_card`, `pow_card_eq_one` | in Mathlib |  |
| Definition 2.12 | 135 | a ring is a commutative group under + with associative distributive multiplication; a field has nonzero elements forming a commutative group | `Ring`, `Field` | in Mathlib |  |
| Theorem 2.50 | 136 | Z_m is a ring for m > 1, and a field iff m is prime | `NTKB.NZM.zmod_isField_iff_prime` | proved |  |

## Chapter 3

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Definition 3.1 | 142 | a with (a,m)=1 is a quadratic residue mod m if x^2 = a (mod m) is solvable; otherwise a nonresidue | `IsSquare` | in Mathlib |  |
| Definition 3.2 | 143 | Legendre symbol (a/p): 1 if a is a residue, -1 if nonresidue, 0 if p divides a | — | in Mathlib |  |
| Theorem 3.1 | 143 | Euler criterion (a/p) = a^((p-1)/2) mod p, multiplicativity, dependence on a mod p, (a^2 b/p)=(b/p), (1/p)=1 and (-1/p)=(-1)^((p-1)/2) | `legendreSym.eq_pow`, `legendreSym.mul`, `legendreSym.mod`, `legendreSym.at_one`, `legendreSym.at_neg_one`, `legendreSym.sq_one'`, `legendreSym.card_sqrts` | in Mathlib |  |
| Theorem 3.2 | 144 | Lemma of Gauss: (a/p) = (-1)^n with n the number of least residues of a, 2a, ..., ((p-1)/2)a exceeding p/2 | `ZMod.gauss_lemma` | in Mathlib |  |
| Definition 3.3 | 145 | floor [x] (greatest integer at most x) and fractional part | `Int.floor`, `Int.fract` | in Mathlib |  |
| Theorem 3.3 | 145 | for a odd with (a,2p)=1, (a/p) = (-1)^(sum of [ja/p]); and (2/p) = (-1)^((p^2-1)/8) | `ZMod.eisenstein_lemma`, `legendreSym.at_two`, `ZMod.exists_sq_eq_two_iff` | in Mathlib |  |
| Theorem 3.4 | 148 | Gaussian reciprocity law (p/q)(q/p) = (-1)^((p-1)(q-1)/4) for distinct odd primes p, q, with the 4k+1 and 4k+3 restatement | `legendreSym.quadratic_reciprocity`, `ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one`, `ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three` | in Mathlib |  |
| Theorem 3.5 | 150 | for an odd prime p and a prime q>p, (p/q) is determined by q mod 4p via an explicit residue r | `NTKB.NZM.legendreSym_eq_of_reduction` | proved | Mathlib: `jacobiSym.mod_right'`, Mathlib: `jacobiSym.mod_right` |
| Definition 3.4 | 153 | Jacobi symbol (P/Q) as the product of Legendre symbols over the odd prime factors of Q | — | in Mathlib |  |
| Theorem 3.6 | 154 | basic Jacobi properties: multiplicativity in each argument, dependence on P mod Q, value in {1,-1} if (P,Q)=1 and (P^2/Q)=1 | `jacobiSym.mul_right`, `jacobiSym.mul_left`, `jacobiSym.mod_left`, `jacobiSym.eq_one_or_neg_one`, `jacobiSym.sq_one'` | in Mathlib |  |
| Theorem 3.7 | 155 | for Q odd positive, (-1/Q)=(-1)^((Q-1)/2) and (2/Q)=(-1)^((Q^2-1)/8) | `jacobiSym.at_neg_one`, `jacobiSym.at_two` | in Mathlib |  |
| Theorem 3.8 | 156 | Jacobi reciprocity (P/Q)(Q/P) = (-1)^((P-1)(Q-1)/4) for coprime odd positive P, Q | `jacobiSym.quadratic_reciprocity`, `jacobiSym.quadratic_reciprocity'` | in Mathlib |  |
| Theorem 3.9 | 158 | the least positive quadratic nonresidue mod an odd prime p is less than 1 + sqrt(p) | `NTKB.NZM.least_nonresidue_lt_one_add_sqrt`, `NTKB.HardyWright.sq_lt_add_of_least_nonresidue` | proved |  |
| Theorem 3.10 | 161 | a binary form with nonsquare nonzero discriminant has a and c nonzero and represents zero only at (0,0) | `NTKB.NZM.formEval_eq_zero_of_not_isSquare`, `NTKB.NZM.formEval` | proved | Tau Ceti: `a_ne_zero_of_not_isSquare_discrim`, Tau Ceti: `c_ne_zero_of_not_isSquare_discrim` |
| Definition (form) | 161 | form: homogeneous polynomial; quadratic form of degree 2; binary form in two variables | `QuadraticMap`, `QuadraticForm`, `BinaryQuadraticForm` | in Mathlib |  |
| Definition 3.5 | 162 | indefinite, semidefinite and definite forms f(x,y) | `NTKB.NZM.IsIndefinite`, `NTKB.NZM.IsPosSemidef`, `NTKB.NZM.IsNegSemidef`, `NTKB.NZM.IsPosDef`, `NTKB.NZM.IsNegDef` | proved | Mathlib: `QuadraticMap.PosDef` |
| Theorem 3.11 | 162 | binary form of discriminant d: indefinite if d>0, semidefinite not definite if d=0, definite with sign of a if d<0 | `NTKB.NZM.isIndefinite_of_pos`, `NTKB.NZM.semidef_not_def_of_disc_eq_zero`, `NTKB.NZM.def_of_disc_neg` | proved |  |
| Theorem 3.12 | 163 | an integral binary form of discriminant d exists iff d = 0 or 1 mod 4 | `NTKB.NZM.exists_formDisc_eq_iff` | proved | Tau Ceti: `discrim_emod_four_eq_zero_or_one`, Tau Ceti: `discrim_principalForm` |
| Theorem 3.13 | 164 | n is properly represented by a form of discriminant d iff x^2 = d (mod 4\\|n\\|) is solvable | `NTKB.NZM.exists_proper_rep_iff` | proved |  |
| Corollary 3.14 | 164 | for d = 0 or 1 mod 4 and an odd prime p, some form of discriminant d represents p iff (d/p)=1 | `NTKB.NZM.exists_rep_prime_iff`, `NTKB.NZM.exists_rep_prime_iff_legendreSym` | proved |  |
| Definition 3.6 | 168 | the modular group Gamma of integral 2x2 matrices of determinant 1 | `Matrix.SpecialLinearGroup` | in Mathlib |  |
| Definition 3.7 | 168 | forms f and g are equivalent if some M in Gamma takes f to g by substitution | `NTKB.Davenport.FormEquiv` | proved | Tau Ceti: `BinaryQuadraticForm`, Tau Ceti: `eval_smul` |
| Theorem 3.15 | 166 | the transform of ax^2+bxy+cy^2 by a matrix M has coefficients A,B,C given by explicit formulas and discriminant (det M)^2 d | `NTKB.Davenport.formSubst`, `NTKB.Davenport.formDisc_formSubst` | proved | Tau Ceti: `smul_a`, Tau Ceti: `smul_b`, Tau Ceti: `smul_c`, Tau Ceti: `discrim_smul`, Tau Ceti: `isUnit_det_of_quadratic_identity` |
| Theorem 3.16 | 169 | equivalence of forms is reflexive, symmetric and transitive | `NTKB.NZM.formEquiv_symm`, `NTKB.NZM.formEquiv_equivalence`, `NTKB.Davenport.FormEquiv.refl`, `NTKB.Davenport.FormEquiv.trans` | proved | Tau Ceti: `eval_smul` |
| Theorem 3.17 | 170 | equivalent forms have the same discriminant and bijective (proper) representations of n | `NTKB.NZM.formEquiv_rep_equiv`, `NTKB.Davenport.FormEquiv.formDisc_eq` | proved | Tau Ceti: `discrim_smul`, Tau Ceti: `eval_smul` |
| Definition 3.8 | 170 | a form of nonsquare discriminant is reduced if -\\|a\\|<b<=\\|a\\|<=\\|c\\| with a sign condition when \\|a\\|=\\|c\\| | `NTKB.NZM.IsReducedForm` | proved | Tau Ceti: `IsReducedForm`, Tau Ceti: `IsLagrangeReduced` |
| Theorem 3.18 | 171 | every equivalence class of forms of nonsquare discriminant contains a reduced form | `NTKB.NZM.exists_formEquiv_isReducedForm` | proved | Tau Ceti: `exists_smul_isReducedForm`, Tau Ceti: `exists_smul_isLagrangeReduced` |
| Theorem 3.19 | 172 | reduced forms satisfy the bound on a, so only finitely many reduced forms of nonsquare discriminant d | `NTKB.NZM.isReducedForm_bounds`, `NTKB.NZM.finite_isReducedForm` | proved | Tau Ceti: `four_mul_sq_a_lt_discrim`, Tau Ceti: `mem_reducedForms`, Tau Ceti: `finite_orbitRel_quotient_of_forall_discrim_eq`, Tau Ceti: `finite_orbitRel_quotient_posDef` |
| Definition 3.9 | 172 | the class number H(d) of a nonsquare discriminant d is the number of equivalence classes of forms | `NTKB.NZM.formClassNumber`, `NTKB.NZM.finite_formClasses` | proved | Tau Ceti: `finite_orbitRel_quotient_posDef`, Tau Ceti: `hurwitzClassNumber_eq_finsum` |
| Theorem 3.20 | 175 | n is properly represented as a sum of two squares iff all odd prime factors of n are 1 mod 4 and 4 does not divide n | `NTKB.NZM.proper_sum_two_sq_iff` | proved | Mathlib: `ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_coprime`, Mathlib: `Nat.eq_sq_add_sq_of_isSquare_mod_neg_one`, Mathlib: `ZMod.isSquare_neg_one_iff_forall_mem_primeFactors_mod_four_ne_three` |
| Theorem 3.21 | 176 | r(n) = 4 N(n) with N(n) the number of solutions of s^2 = -1 (mod n), and R(n) = sum of r(n/d^2) | `NTKB.NZM.properSqRepCount_eq_four_mul`, `NTKB.NZM.negOneSqrtCount`, `NTKB.NZM.sumTwoSquaresCount_eq_sum_properSqRepCount`, `NTKB.NZM.properSqRepCount` | proved |  |
| Theorem 3.22 | 177 | explicit formulas for r(n) and R(n) in terms of the prime factorization of n | `NTKB.NZM.properSqRepCount_eq`, `NTKB.HardyWright.sumTwoSquaresCount_eq`, `NTKB.HardyWright.chi4DivisorSum_eq_prod` | proved |  |
| Corollary 3.23 | 178 | R(n) = 4 times the excess of divisors of n of the form 4k+1 over those 4k+3 | `NTKB.HardyWright.sumTwoSquaresCount_eq_card_sub_card` | proved |  |
| Lemma 3.24 | 181 | a reduced positive definite form f with f(x,y)<c at a coprime pair (x,y) takes the value a or c at one of six points | `NTKB.NZM.IsReducedForm.mem_sixPoints`, `NTKB.NZM.IsReducedForm.formEval_eq_of_le`, `NTKB.NZM.IsReducedForm.properReps_fst` | proved |  |
| Theorem 3.25 | 183 | two equivalent reduced positive definite forms are equal | `NTKB.NZM.eq_of_formEquiv_of_isReducedForm` | proved | Tau Ceti: `orbit_mk_injOn_isReducedForm` |
| Definition 3.10 | 183 | an automorph of a positive definite form f is M in Gamma taking f to itself | `NTKB.NZM.automorphs`, `NTKB.NZM.numAutomorphs`, `NTKB.NZM.formMaps` | proved |  |
| Theorem 3.26 | 184 | equivalent positive definite forms have the same number w(f) of automorphs (2, 4 or 6), exactly w(f) matrices take f to g, and w is given for reduced forms | `NTKB.NZM.IsReducedForm.automorphs_eq`, `NTKB.NZM.IsReducedForm.numAutomorphs_eq`, `NTKB.NZM.numAutomorphs_mem`, `NTKB.NZM.automorphs_equiv_formMaps` | proved | Tau Ceti: `reducedFormWeight_eq_two_div_card_stabilizer` |
| Theorem 3.27 | 185 | for positive definite f of discriminant d<0, r_f(n) = w(f) H_f(n) and R_f(n) = sum over m^2 dividing n of r_f(n/m^2) | `NTKB.NZM.properRepCount_eq_mul`, `NTKB.NZM.repCount_eq_sum`, `NTKB.NZM.hCount` | proved |  |
| Definition (primitive form) | 174 | a form ax^2+bxy+cy^2 is primitive if gcd(a,b,c)=1 | `NTKB.NZM.IsPrimitiveForm`, `NTKB.NZM.isPrimitiveForm_iff_of_formEquiv` | proved | Tau Ceti: `IsPrimitive` |
| Definition (fundamental discriminant) | 174 | d is a fundamental discriminant if all forms of discriminant d are primitive | `NTKB.Davenport.isFundamentalDiscriminant_iff_forall_primitive` | proved | Mathlib: `Int.IsFundamentalDiscr` |
| Definition (modular function) | 188 | a function f(z) invariant under the action of the modular group | `ModularForm`, `SlashInvariantForm` | partly in other libraries; not proved here |  |

## Chapter 4

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Theorem 4.1 | 191 | Basic properties of the greatest integer function: bounds, $[x+m]=[x]+m$, $[x]+[y]\le[x+y]\le[x]+[y]+1$, $[[x]/m]=[x/m]$, $-[-x]$ is the ceiling, nearest-integer formulas, $[n/a]$ counts multiples of $a$ up to $n$ | `NTKB.NZM.thm_4_1_a`, `NTKB.NZM.thm_4_1_a'`, `NTKB.NZM.thm_4_1_sum`, `NTKB.NZM.thm_4_1_b`, `NTKB.NZM.thm_4_1_c`, `NTKB.NZM.thm_4_1_d`, `NTKB.NZM.thm_4_1_d'`, `NTKB.NZM.thm_4_1_e`, `NTKB.NZM.thm_4_1_f`, `NTKB.NZM.thm_4_1_g`, `NTKB.NZM.thm_4_1_g_tie`, `NTKB.NZM.thm_4_1_g'`, `NTKB.NZM.thm_4_1_g'_tie`, `NTKB.NZM.thm_4_1_h` | proved | Mathlib: `Int.floor_le`, Mathlib: `Int.lt_floor_add_one`, Mathlib: `Int.floor_add_intCast`, Mathlib: `Int.le_floor_add`, Mathlib: `Int.le_floor_add_floor`, Mathlib: `Int.floor_div_natCast`, Mathlib: `Int.floor_neg`, Mathlib: `round_eq`, Mathlib: `Nat.Ioc_filter_dvd_card_eq_div` |
| Theorem 4.2 | 193 | de Polignac's formula: the exponent of $p$ in $n!$ is $\sum_{i\ge1}[n/p^i]$ | `factorization_factorial`, `emultiplicity_factorial` | in Mathlib |  |
| Definition 4.1 | 199 | $d(n)$, $\sigma(n)$, $\sigma_k(n)$, $\omega(n)$, $\Omega(n)$: divisor count, divisor sum, sum of $k$th powers, number of distinct primes, number of primes with multiplicity | — | in Mathlib |  |
| Theorem 4.3 | 200 | $d(n)=\prod_{p^a\Vert n}(a+1)$ | `card_divisors` | in Mathlib |  |
| Definition 4.2 | 200 | Multiplicative (nonzero, $f(mn)=f(m)f(n)$ for coprime $m,n$) and totally multiplicative arithmetic function | `NTKB.Apostol.IsCompletelyMultiplicative` | proved | Mathlib: `IsMultiplicative` |
| Theorem 4.4 | 201 | If $f$ is multiplicative then $F(n)=\sum_{d\mid n}f(d)$ is multiplicative | `IsMultiplicative.mul`, `isMultiplicative_zeta` | in Mathlib |  |
| Theorem 4.5 | 202 | $\sigma(n)=\prod_{p^a\Vert n}(p^{a+1}-1)/(p-1)$ | `sum_divisors`, `isMultiplicative_sigma`, `sigma_one_apply_prime_pow` | in Mathlib |  |
| Theorem 4.6 | 202 | $\sum_{d\mid n}\varphi(d)=n$ | `sum_totient` | in Mathlib |  |
| Definition 4.3 | 204 | Möbius function: $\mu(n)=(-1)^{\omega(n)}$ for squarefree $n$, else $0$ | `moebius_apply_of_squarefree`, `moebius_eq_zero_of_not_squarefree` | in Mathlib |  |
| Theorem 4.7 | 204 | $\mu$ is multiplicative and $\sum_{d\mid n}\mu(d)$ is $1$ for $n=1$ and $0$ otherwise | `isMultiplicative_moebius`, `moebius_mul_coe_zeta`, `coe_zeta_mul_coe_moebius` | in Mathlib |  |
| Theorem 4.8 | 205 | Möbius inversion: if $F(n)=\sum_{d\mid n}f(d)$ then $f(n)=\sum_{d\mid n}\mu(d)F(n/d)$ | `sum_eq_iff_sum_mul_moebius_eq`, `sum_eq_iff_sum_smul_moebius_eq` | in Mathlib |  |
| Theorem 4.9 | 205 | Converse of Möbius inversion: if $f(n)=\sum_{d\mid n}\mu(d)F(n/d)$ then $F(n)=\sum_{d\mid n}f(d)$ | `sum_eq_iff_sum_mul_moebius_eq`, `sum_eq_iff_sum_smul_moebius_eq` | in Mathlib |  |
| Theorem 4.10 | 210 | Order-2 linear recurrence $u_n=au_{n-1}+bu_{n-2}$ with distinct roots $\lambda,\mu$ of $z^2-az-b$ has $u_n=\alpha\lambda^n+\beta\mu^n$ | `NTKB.NZM.recurrence_distinct_roots`, `NTKB.NZM.exists_unique_coeffs`, `NTKB.NZM.recurrence_of_distinct_roots_converse` | proved | Mathlib: `eq_mk_of_is_sol_of_eq_init`, Mathlib: `geom_sol_iff_root_charPoly`, Mathlib: `coe_fib_eq` |
| Theorem 4.11 | 211 | If $a^2+4b=0$, $b\ne0$ (repeated root $\lambda$) then $u_n=(\alpha+\beta n)\lambda^n$ | `NTKB.NZM.recurrence_double_root` | proved |  |
| Theorem 4.12 | 213 | If $p$ is an odd prime with $(D/p)=-1$, $D=a^2+4b$, then $p\mid U_{p+1}$ | `NTKB.NZM.prime_dvd_lucasU_succ` | proved |  |
| Lucas functions | 212 | $U_n(a,b)=(\lambda^n-\mu^n)/\sqrt D$, $V_n(a,b)=\lambda^n+\mu^n$ (Lucas functions; $F_n=U_n(1,1)$, $L_n=V_n(1,1)$) | `NTKB.NZM.lucasU`, `NTKB.NZM.lucasV`, `NTKB.NZM.sub_mul_lucasU`, `NTKB.NZM.lucasV_eq_pow_add_pow` | proved |  |
| Lucas probable prime | 214 | $n$ with $(D/n)=-1$ and $n\mid U_{n+1}$ | `NTKB.NZM.IsLucasProbablePrime`, `NTKB.NZM.isLucasProbablePrime_of_prime` | proved |  |
| Lucas pseudoprime | 214 | A composite Lucas probable prime | `NTKB.NZM.IsLucasPseudoprime` | proved |  |
| Linear recurrence | 215 | A sequence satisfying $u_n=au_{n-1}+bu_{n-2}$ (linear recurrence of order 2) | `LinearRecurrence` | in Mathlib |  |

## Chapter 5

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Theorem 5.1 | 224 | $ax+by=c$ is solvable in integers iff $\gcd(a,b)\mid c$, and then all solutions are $x_1+kb/g$, $y_1-ka/g$ | `NTKB.NZM.linear_diophantine_solvable_iff`, `NTKB.NZM.linear_diophantine_solutions`, `NTKB.NZM.linear_diophantine_infinite` | proved | Mathlib: `gcd_dvd_iff` |
| Theorem 5.2 | 237 | A linear system with a real solution and solvable modulo every $q$ has an integral solution (local-global for linear systems) | `NTKB.NZM.exists_int_solution_of_real_of_forall_modEq` | proved |  |
| Definition 5.1 | 238 | A square integer matrix is unimodular if $\det=\pm1$ | `NTKB.NZM.IsUnimodular`, `NTKB.NZM.isUnimodular_iff_isUnit` | proved | Mathlib: `isUnit_iff_isUnit_det` |
| Theorem 5.3 | 238 | For an integer square matrix $U$: $\det U=\pm1$, $U^{-1}$ integral, $U$ a product of elementary row matrices, and of elementary column matrices, are equivalent | `NTKB.NZM.isUnimodular_iff_isUnit`, `NTKB.NZM.isUnimodular_iff_exists_inverse`, `NTKB.NZM.isUnimodular_iff_exists_left_inverse`, `NTKB.NZM.unimodular_mem_closure`, `NTKB.NZM.unimodularElementaryProduct` | proved | Mathlib: `isUnit_iff_isUnit_det` |
| Lemma 5.4 | 243 | Coprime positive integers $u,v$ with $uv$ a perfect square are both squares | `sq_of_gcd_eq_one`, `exists_associated_pow_of_mul_eq_pow` | in Mathlib |  |
| Theorem 5.5 | 243 | Primitive positive solutions of $x^2+y^2=z^2$ with $y$ even are $x=r^2-s^2$, $y=2rs$, $z=r^2+s^2$ with $r>s>0$ coprime of opposite parity | `coprime_classification'`, `coprime_classification` | in Mathlib |  |
| Theorem 5.6 | 245 | $15x^2-7y^2=9$ has no integral solution | `NTKB.NZM.no_solution_fifteen_sq_sub_seven_sq` | proved |  |
| Theorem 5.7 | 246 | $x^3+2y^3+4z^3=9w^3$ has no nontrivial solution | `NTKB.NZM.cubic_form_only_trivial` | proved |  |
| Theorem 5.8 | 247 | $y^2=x^3+7$ has no integral solution (statement garbled by OCR; the proof factors $y^2+1=x^3+8$) | `NTKB.NZM.no_solution_sq_eq_cube_add_seven` | proved |  |
| Theorem 5.9 | 248 | $x^4+x^3+x^2+x+1=y^2$ has exactly the integral solutions $(-1,\pm1),(0,\pm1),(3,\pm11)$ | `NTKB.NZM.quartic_eq_sq_iff` | proved |  |
| Theorem 5.10 | 248 | $x^4+y^4=z^2$ has no solution in positive integers (Fermat) | `not_fermat_42` | in Mathlib |  |
| Theorem 5.11 | 253 | Legendre: $ax^2+by^2+cz^2=0$ ($abc$ squarefree) has a nontrivial integral solution iff $a,b,c$ do not all have the same sign and $-bc,-ca,-ab$ are quadratic residues mod $a,b,c$ | `NTKB.IrelandRosen.Legendre.legendre`, `NTKB.IrelandRosen.Legendre.hasSol_of_local` | proved |  |
| Lemma 5.12 | 253 | For positive reals $\lambda\mu\nu=m\in\mathbb Z$, $\alpha x+\beta y+\gamma z\equiv0 \pmod m$ has a nonzero solution with $\lvert x\rvert<\lambda,\lvert y\rvert<\mu,\lvert z\rvert<\nu$ | `NTKB.NZM.lemma_5_12`, `NTKB.NZM.lemma_5_12_strict` | proved |  |
| Lemma 5.13 | 253 | If $ax^2+by^2+cz^2$ factors into linear forms mod $m$ and mod $n$ with $(m,n)=1$ then it factors mod $mn$ | `NTKB.NZM.ternary_factors_mul` | proved |  |
| Theorem 5.14 | 257 | For any integers $a,b,c$ the congruence $ax^2+by^2+cz^2\equiv0 \pmod p$ has a nontrivial solution | `NTKB.NZM.exists_nontrivial_ternary_congr` | proved | Mathlib: `char_dvd_card_solutions` |
| Theorem 5.15 | 263 | A line meeting a degree-$d$ plane curve in more than $d$ points lies on it, and the curve equation factors through it | `NTKB.NZM.plane_curve_line_dvd` | proved |  |
| Theorem 5.16 | 268 | The cubic $x^3+y^3=9$ has infinitely many rational points | `NTKB.NZM.infinite_rational_points_cube_sum_nine` | proved |  |
| Definition 5.2 | 272 | A real cubic polynomial defines an elliptic curve if irreducible and with no singular point in the real projective plane | `WeierstrassCurve`, `IsElliptic` | partly in other libraries; not proved here |  |
| Theorem 5.17 | 273 | A nonsingular complex cubic is irreducible; $y^2=q(x)$ with $q$ cubic is nonsingular iff $q$ has no repeated root | `equation_iff_nonsingular`, `equation_iff_nonsingular_of_Δ_ne_zero` | partly in other libraries; not proved here |  |
| Lemma 5.18 | 275 | Chord-and-tangent addition has identity $0$, is commutative, and each point has a unique inverse | `add_def`, `neg_def`, `toClass_injective` | partly in other libraries; not proved here |  |
| Lemma 5.19 | 277 | Cayley–Bacharach type: if nine points are common to two cubics and three lie on a line not in the curve, the other six lie on a conic | — | not formalized |  |
| Lemma 5.20 | 278 | Associativity $(A+B)+C=A+(B+C)$ of the chord-and-tangent addition | `toClass_injective` | partly in other libraries; not proved here |  |
| Theorem 5.21 | 280 | The points of an elliptic curve over ℝ form an abelian group with chosen $0$; rational points form a subgroup iff $0$ is rational | `toClass_injective`, `map_injective` | partly in other libraries; not proved here |  |
| Theorem 5.22 | 280 | Changing the base point $0$ to $0'$ gives an isomorphic group via $A\mapsto A+0'$ | `NTKB.NZM.shiftEquiv_add`, `NTKB.NZM.add_shiftedAdd`, `NTKB.NZM.weierstrass_shiftEquiv_add` | proved |  |
| Theorem 5.23 | 281 | Three distinct points on an elliptic curve are collinear iff $A+B+C=\infty$ | `add_some` | partly in other libraries; not proved here |  |
| Theorem 5.24 | 282 | The only rational points on $y^2=x^3-4x$ are $(2,0),(0,0),(-2,0)$ and the point at infinity | `NTKB.NZM.rational_solutions_y_sq_x_cubed_sub_four_x` | proved |  |
| Theorem 5.25 | 286 | For integral $y^2=x^3+ax^2+bx+c$, a rational point not at infinity has $x=u/w^2$, $y=v/w^3$ with $\gcd(u,w)=\gcd(v,w)=1$ | `NTKB.NZM.rational_point_denominators` | proved |  |
| Powerful number | 230 | A positive integer $a$ is powerful if $p^2\mid a$ whenever $p\mid a$ | `NTKB.NZM.IsPowerful` | proved |  |
| Invariant factors | 240 | The diagonal entries $s_i$ in the Smith normal form of an integer matrix | `NTKB.NZM.invariantFactor` | proved | Mathlib: `SmithNormalForm` |
| Determinantal divisors | 241 | $d_k(A)$ = gcd of the $k\times k$ minors of $A$ | `NTKB.NZM.determinantalDivisor`, `NTKB.NZM.determinantalDivisor_dvd`, `NTKB.NZM.dvd_determinantalDivisor` | proved |  |
| Plane curve and rational point | 260 | A point $(x,y)$ with rational coordinates; curve $f(x,y)=0$ is a line if $\deg f=1$ and a conic if $\deg f=2$ | `Equation`, `Nonsingular` | partly in other libraries; not proved here |  |
| Intersection multiplicity | 263 | Multiplicity of a zero of the restriction of $f$ to a line, called the intersection multiplicity | `NTKB.NZM.intersectionMultiplicity`, `NTKB.NZM.intersectionMultiplicity_pos_iff` | proved |  |
| Singular point and nonsingular curve | 264 | Multiplicity of a point; simple/smooth vs singular points; nonsingular curve (including points at infinity) | `NTKB.NZM.IsSingularPoint`, `NTKB.NZM.IsSimplePoint`, `NTKB.NZM.HasMultiplicity` | proved in part | Mathlib: `Nonsingular` |
| Inflection point | 265 | A simple point whose tangent has intersection multiplicity at least 3 | `NTKB.NZM.IsInflectionPoint` | proved |  |
| Irreducible polynomial | 269 | Polynomial not a product of two polynomials of lower degree | `Irreducible` | in Mathlib |  |
| Absolutely irreducible polynomial | 270 | $f$ irreducible over ℂ | `NTKB.NZM.IsAbsolutelyIrreducible` | proved |  |
| Projective plane | 270 | Real projective plane: nonzero triples modulo proportionality, with projective coordinates $X:Y:Z$ | `Projectivization` | in Mathlib |  |
| Chord-and-tangent addition | 275 | Group addition $A+B=0(AB)$ on an elliptic curve with chosen zero | `add_def`, `add_some` | partly in other libraries; not proved here |  |
| Finitely generated abelian group | 288 | Every element is an integer combination of finitely many generators | `IsAddFG` | in Mathlib |  |
| Rank of an abelian group | 288 | The number $r$ of independent generators of infinite order | — | partly in other libraries; not proved here |  |
| Circle group | 292 | The group $\mathbb T$ of complex numbers of modulus 1 | `Circle` | in Mathlib |  |
| Elliptic curve modulo p | 294 | A cubic mod $p$ that is irreducible and with no singular projective point | `IsElliptic` | partly in other libraries; not proved here |  |
| Ordinary double point | 299 | A double point where the quadratic form of second derivatives has distinct roots | `NTKB.NZM.IsOrdinaryDoublePoint` | proved |  |
| Elliptic integral | 305 | An integral involving the square root of a cubic or quartic polynomial | — | partly in other libraries; not proved here |  |

## Chapter 6

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Theorem 6.1 | 309 | Consecutive fractions a/b, a'/b' in a row of the Farey table satisfy a'b - ab' = 1 | `NTKB.NZM.fareyRow_consecutive_det`, `NTKB.NZM.fareyRow`, `NTKB.NZM.farey_adjacent` | proved |  |
| Corollary 6.2 | 309 | Every fraction in the Farey table is in lowest terms | `NTKB.NZM.fareyRow_coprime` | proved |  |
| Corollary 6.3 | 309 | The fractions in each row of the table are listed in increasing order | `NTKB.NZM.fareyRow_pairwise_lt` | proved |  |
| Theorem 6.4 | 309 | Between consecutive fractions a/b, a'/b' the mediant (a+a')/(b+b') is the unique fraction of least denominator | `NTKB.NZM.mediant_least_denominator` | proved |  |
| Theorem 6.5 | 310 | A reduced fraction x/y with 0 < x < y first appears in row y and in all later rows | `NTKB.NZM.mem_fareyRow_iff` | proved |  |
| Corollary 6.6 | 311 | The nth row consists of all reduced fractions in (0,1) with denominator at most n, in order | `NTKB.NZM.fareyRow_values` | proved |  |
| Definition 6.1 | 311 | The Farey sequence of order n: all reduced fractions with denominators at most n, in order | `NTKB.NZM.fareyRow`, `NTKB.NZM.fareyRow_values`, `NTKB.HardyWright.fareySeries`, `NTKB.HardyWright.fareySeries_eq_image` | proved |  |
| Theorem 6.7 | 312 | If a/b, c/d are adjacent in the Farey sequence of order n then the mediant is within 1/(b(n+1)) of a/b and within 1/(d(n+1)) of c/d | `NTKB.NZM.farey_mediant_gap`, `NTKB.NZM.mediant_sub_eq`, `NTKB.NZM.mediant_sub_le` | proved |  |
| Theorem 6.8 | 313 | For real x and positive integer n there is a/b with 0 < b <= n and abs(x - a/b) <= 1/(b(n+1)) | `exists_rat_abs_sub_le_and_den_le` | in Mathlib |  |
| Theorem 6.9 | 313 | For irrational xi there are infinitely many rationals a/b with abs(xi - a/b) < 1/b^2 | `infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational` | in Mathlib |  |
| Lemma 6.10 | 314 | For positive integers x, y the two displayed inequalities in x, y (involving sqrt5 and 1/x^2 + 1/y^2) cannot both hold | `NTKB.NZM.not_both_hurwitz_ineq` | proved |  |
| Theorem 6.11 | 315 | Hurwitz: for irrational xi there are infinitely many h/k with abs(xi - h/k) < 1/(sqrt5 k^2) | `infinite_rat_abs_sub_lt_one_div_sqrt_five_mul_den_sq_of_irrational` | in Mathlib |  |
| Theorem 6.12 | 316 | The constant sqrt5 in Hurwitz's theorem is best possible (golden ratio is the extremal example) | `NTKB.HardyWright.finite_abs_sub_lt_of_sqrt_five_lt` | proved |  |
| Theorem 6.13 | 318 | Rational root theorem: a rational root a/b (lowest terms) of an integer polynomial satisfies a divides c_0 and b divides c_n | `num_dvd_of_is_root`, `den_dvd_of_is_root` | in Mathlib |  |
| Corollary 6.14 | 319 | A monic integer polynomial equation with a nonzero rational root has an integer root dividing c_0 | `isInteger_of_is_root_of_monic`, `exists_integer_of_is_root_of_monic` | in Mathlib |  |
| Corollary 6.15 | 319 | Rational solutions of x^n = c are integers; so x^n = c has a rational solution iff c is an nth power | `irrational_nrt_of_notint_nrt` | in Mathlib |  |
| Theorem 6.16 | 319 | For rational r, cos, sin, tan of r*pi are irrational except for the listed values | `NTKB.NZM.cos_rat_mul_pi_irrational_or_mem`, `NTKB.NZM.sin_rat_mul_pi_irrational_or_mem`, `NTKB.NZM.tan_rat_mul_pi_irrational_or_mem` | proved | Mathlib: `irrational_cos_rat_mul_pi`, Mathlib: `niven_sin` |
| Lemma 6.17 | 320 | For a polynomial g with integer coefficients, x^n g(x) and all its derivatives at 0 are integers divisible by n! | `NTKB.NZM.factorial_dvd_iterate_derivative_X_pow_mul` | proved |  |
| Theorem 6.18 | 320 | pi is irrational | `irrational_pi` | in Mathlib |  |
| Theorem 6.19 | 323 | Blichfeldt's principle: a set of volume greater than 1 in R^n contains two distinct points differing by an integer vector | `exists_pair_mem_lattice_not_disjoint_vadd` | in Mathlib |  |
| Theorem 6.20 | 324 | Minkowski's convex body theorem: a convex symmetric set of volume > 2^n contains a nonzero integer point | `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure` | in Mathlib |  |
| Theorem 6.21 | 326 | Minkowski's theorem for the lattice A Z^n: convex symmetric set of volume > 2^n d(A) contains a nonzero lattice point | `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure` | in Mathlib |  |
| Corollary 6.22 | 326 | Closed bounded version of Minkowski's theorem with non-strict inequality v >= 2^n d(A) | `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure` | in Mathlib |  |
| Theorem 6.23 | 326 | For nonsingular A, B: B Z^n is contained in A Z^n iff B = AK with K an integer matrix | `NTKB.NZM.matrixLattice_subset_iff`, `NTKB.NZM.matrixLattice` | proved |  |
| Corollary 6.24 | 326 | A Z^n = B Z^n iff B = AU with U unimodular | `NTKB.NZM.matrixLattice_eq_iff` | proved |  |
| Theorem 6.25 | 327 | Simultaneous Diophantine approximation: for reals x_1..x_k and n there are integers a_i, 0 < b <= n with abs(x_i - a_i/b) < 1/(b n^(1/k)) | `NTKB.NZM.simultaneous_approximation_general`, `NTKB.NZM.simultaneous_approximation` | proved |  |
| Theorem 6.26 | 328 | Lagrange: every positive integer is a sum of four squares | `sum_four_squares` | in Mathlib |  |
| Corollary 6.27 | 329 | Infinitely many positive integers are not sums of four positive squares, but every n > 169 is a sum of five positive squares | `NTKB.NZM.corollary_6_27` | proved |  |
| Definition (irrational number) | 308 | A real number that is not rational | `Irrational` | in Mathlib |  |
| Definition (lattice) | 325 | For nonsingular A, the set A Z^n is a lattice; its members are lattice points, the columns of A a basis | `IsZLattice` | in Mathlib |  |
| Definition (determinant of a lattice) | 325 | The absolute value of det A is the determinant d(Lambda) of the lattice | — | in Mathlib |  |
| Definition (interior point) | 331 | A point of a planar set having a disc around it contained in the set | — | in Mathlib |  |

## Chapter 7

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Theorem 7.1 | 339 | Uniqueness: if two finite simple continued fractions are equal and the last terms exceed 1, they have the same length and terms | `NTKB.HardyWright.cf_eq_of_value_eq` | proved |  |
| Theorem 7.2 | 340 | A finite simple continued fraction is rational; every rational has exactly two finite simple expansions | `NTKB.HardyWright.exists_cf_eq_rat`, `NTKB.HardyWright.cf_rat_two_expansions`, `NTKB.HardyWright.cf_nums_dens_int` | proved | Mathlib: `terminates_iff_rat`, Mathlib: `exists_rat_eq_of_terminates`, Mathlib: `terminates_of_rat` |
| Theorem 7.3 | 340 | For positive real x, (a_0,...,a_(n-1),x) = (x h_(n-1) + h_(n-2))/(x k_(n-1) + k_(n-2)) | `NTKB.NZM.finite_cf_value`, `NTKB.HardyWright.cf_value_eq_completeQuotient` | proved | Mathlib: `nums_recurrence`, Mathlib: `dens_recurrence` |
| Theorem 7.4 | 341 | The nth convergent (a_0,...,a_n) equals h_n/k_n | `convs_eq_convs'` | in Mathlib |  |
| Theorem 7.5 | 341 | h_i k_(i-1) - h_(i-1) k_i = (-1)^i, difference formulas for r_i, and h_i/k_i is in lowest terms | `NTKB.HardyWright.cf_nums_mul_dens_sub`, `NTKB.HardyWright.cf_nums_mul_dens_sub_two`, `NTKB.HardyWright.cf_convs_succ_sub`, `NTKB.HardyWright.cf_convs_add_two_sub`, `NTKB.HardyWright.cf_isCoprime_nums_dens` | proved |  |
| Theorem 7.6 | 342 | Even convergents increase, odd ones decrease, every even one is below every odd one, and the limit exists | `NTKB.HardyWright.cf_convs_even_lt`, `NTKB.HardyWright.cf_convs_odd_lt`, `NTKB.HardyWright.cf_convs_even_lt_odd`, `NTKB.HardyWright.cf_convs_tendsto` | proved | Mathlib: `of_convergence` |
| Definition 7.1 | 342 | The value of an infinite simple continued fraction (a_0,a_1,...) is the limit of its convergents | `NTKB.HardyWright.cf_convs_tendsto`, `NTKB.HardyWright.cf_convergent` | proved | Mathlib: `SimpContFract` |
| Theorem 7.7 | 343 | The value of any infinite simple continued fraction is irrational | `NTKB.HardyWright.irrational_iff_exists_unique_cf` | proved |  |
| Lemma 7.8 | 343 | For theta = (a_0,a_1,...), a_0 = floor(theta) and theta = a_0 + 1/theta_1 | `NTKB.HardyWright.cf_floor_value_eq`, `NTKB.HardyWright.cf_tendsto_tail` | proved |  |
| Theorem 7.9 | 344 | Two distinct infinite simple continued fractions have different values | `NTKB.HardyWright.cf_eq_of_tendsto` | proved |  |
| Theorem 7.10 | 346 | Every irrational xi is uniquely an infinite simple continued fraction; conversely any infinite one is irrational; monotone convergents; xi = (a_0,...,a_(n-1),xi_n) | `NTKB.HardyWright.irrational_iff_exists_unique_cf`, `NTKB.HardyWright.cf_even_lt_value_lt_odd`, `NTKB.HardyWright.cf_value_eq_completeQuotient` | proved | Mathlib: `of_isSimpContFract`, Mathlib: `of_convergence`, Mathlib: `terminates_iff_rat` |
| Theorem 7.11 | 347 | abs(xi - h_n/k_n) < 1/(k_n k_(n+1)) and abs(xi k_n - h_n) < 1/k_(n+1) | `NTKB.HardyWright.cf_abs_sub_convs_bounds`, `NTKB.HardyWright.cf_sub_convs_eq` | proved | Mathlib: `abs_sub_convs_le`, Mathlib: `abs_sub_convergents_le'` |
| Theorem 7.12 | 348 | The convergents are successively closer to xi: abs(xi k_n - h_n) < abs(xi k_(n-1) - h_(n-1)) | `NTKB.HardyWright.cf_abs_sub_convs_bounds` | proved |  |
| Theorem 7.13 | 349 | Best approximation: if abs(xi b - a) < abs(xi k_n - h_n) then b >= k_(n+1) (and a/b closer than h_n/k_n forces b > k_n) | `NTKB.NZM.dens_succ_le_of_abs_lt`, `NTKB.NZM.best_approximation_of_one_le`, `NTKB.HardyWright.abs_nums_sub_lt`, `NTKB.HardyWright.abs_convs_sub_lt` | proved |  |
| Theorem 7.14 | 350 | If abs(xi - a/b) < 1/(2b^2) then a/b is a convergent of xi (Legendre) | `exists_rat_eq_convergent` | in Mathlib |  |
| Theorem 7.15 | 350 | The nth convergent of 1/x is the reciprocal of the (n-1)st convergent of x, for x > 1 | `NTKB.NZM.convergent_one_div` | proved | Mathlib: `convergent_succ` |
| Lemma 7.16 | 353 | If x > 1 and x + 1/x < sqrt5 then x < (sqrt5+1)/2 and 1/x > (sqrt5-1)/2 | `NTKB.NZM.lt_golden_of_add_inv_lt` | proved |  |
| Theorem 7.17 | 353 | Hurwitz: infinitely many h/k with abs(xi - h/k) < 1/(sqrt5 k^2) | `infinite_rat_abs_sub_lt_one_div_sqrt_five_mul_den_sq_of_irrational` | in Mathlib |  |
| Theorem 7.18 | 354 | The constant sqrt5 in Hurwitz's theorem is best possible (golden ratio (1,1,1,...)) | `NTKB.HardyWright.finite_abs_sub_lt_of_sqrt_five_lt` | proved |  |
| Theorem 7.19 | 356 | A periodic simple continued fraction is a quadratic irrational and conversely (Euler and Lagrange) | `NTKB.HardyWright.quadratic_of_isPeriodic`, `NTKB.HardyWright.isPeriodic_of_quadratic` | proved |  |
| Theorem 7.20 | 359 | The expansion of a real quadratic irrational is purely periodic iff xi > 1 and -1 < conjugate < 0 (Galois) | `NTKB.NZM.purelyPeriodic_iff` | proved |  |
| Theorem 7.21 | 361 | For non-square d, sqrt(d) = (a_0,a_1,...,a_(r-1),2a_0) with the palindromic period and the q_i relations | `NTKB.NZM.sqrt_cf_period_mq`, `NTKB.NZM.mq`, `NTKB.HardyWright.pell_period` | proved |  |
| Theorem 7.22 | 362 | For non-square d, h_n^2 - d k_n^2 = (-1)^(n+1) q_(n+1) for the convergents of sqrt(d) | `NTKB.NZM.sq_sub_mul_sq_convergent`, `NTKB.NZM.mq` | proved |  |
| Corollary 7.23 | 363 | h_(nr-1)^2 - d k_(nr-1)^2 = (-1)^(nr) giving infinitely many solutions of x^2 - d y^2 = 1 | `NTKB.HardyWright.pell_period` | proved |  |
| Theorem 7.24 | 363 | If abs(N) < sqrt(d), every positive coprime solution of x^2 - d y^2 = N is a convergent of sqrt(d) | `NTKB.NZM.eq_convergent_of_sq_sub_mul_sq` | proved |  |
| Theorem 7.25 | 364 | All positive solutions of x^2 - d y^2 = 1 are given by convergents h_(nr-1), k_(nr-1) according to the parity of the period r | `NTKB.NZM.pell_solutions_of_period`, `NTKB.HardyWright.pell_period` | proved |  |
| Theorem 7.26 | 365 | If (x_1,y_1) is the least positive solution of x^2 - d y^2 = 1 then all positive solutions are x_n + y_n sqrt(d) = (x_1 + y_1 sqrt(d))^n | `eq_pow_of_nonneg`, `exists_pos_of_not_isSquare` | in Mathlib |  |
| Definition (simple continued fraction) | 338 | A continued fraction with all integer terms is simple | `SimpContFract` | in Mathlib |  |
| Definition (continued fraction expansion of xi) | 345 | The expansion of xi by a_i = floor(xi_i), xi_(i+1) = 1/(xi_i - a_i) | — | in Mathlib |  |
| Definition (periodic continued fraction) | 355 | An infinite simple continued fraction with a_r = a_(n+r) for all large r | `NTKB.HardyWright.IsPeriodic` | proved |  |

## Chapter 8

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Definition 8.1 | 372 | von Mangoldt function Λ(n)=log p if n=p^k, else 0; Chebyshev ψ(x)=Σ_{n<=x}Λ(n), θ(x)=Σ_{p<=x}log p, and π(x) | — | in Mathlib |  |
| Theorem 8.1 | 372 | Σ_{d divides n} Λ(d)=log n | `vonMangoldt_sum` | in Mathlib |  |
| Lemma 8.2 | 372 | T(x)=Σ_{n<=x}log n = x log x - x + θ log(ex) with abs(θ)<=1 | `sum_log_le`, `le_sum_log` | in Mathlib |  |
| Theorem 8.3 | 375 | Chebyshev: ax<ψ(x)<bx for large x for any a<0.78... and b>1.17... | `NTKB.NZM.chebyshev_psi_bounds` | proved | Mathlib: `psi_le_const_mul_self`, Mathlib: `psi_ge_of_seven_le`, Mathlib: `psi_ge'` |
| Theorem 8.4 | 376 | θ(x)=ψ(x)+O(x^{1/2}) | `isBigO_psi_sub_theta_sqrt`, `abs_psi_sub_theta_le_sqrt_mul_log` | in Mathlib |  |
| Theorem 8.5 | 377 | π(x)=θ(x)/log x + O(x/(log x)^2) | `primeCounting_sub_theta_div_log_isBigO` | in Mathlib |  |
| Corollary 8.6 | 377 | The inequalities a x/log x<π(x)<b x/log x hold for large x with the constants of Theorem 8.3 | `NTKB.NZM.chebyshev_primeCounting_bounds` | proved | Mathlib: `eventually_primeCounting_le`, Mathlib: `pi_ge_of_four_le` |
| Theorem 8.7 | 378 | Bertrand's postulate: a prime in (x,2x) for real x>1 | `exists_prime_lt_and_le_two_mul` | in Mathlib |  |
| Theorem 8.8 | 380 | Mertens: Σ_{n<=x}Λ(n)/n=log x+O(1); Σ_{p<=x}log p/p=log x+O(1); integral of ψ(u)/u^2; Σ1/p=log log x+b+O(1/log x); Π(1-1/p) ~ c/log x | `NTKB.HardyWright.sum_vonMangoldt_div_eq_log`, `NTKB.HardyWright.sum_log_prime_div_eq_log`, `NTKB.HardyWright.integral_psi_div_sq`, `NTKB.Apostol.apostol_thm_4_12`, `NTKB.HardyWright.tendsto_prod_one_sub_inv_primes_mul_log` | proved | PNT+: `E₁Λ.bounded`, PNT+: `sum_log_prime_div_eq_log'`, PNT+: `E₂p.bound`, PNT+: `sum_prime_div_eq`, PNT+: `E₃.bound''` |
| Corollary 8.9 | 382 | limsup π(x)/(x/log x)>=1 and liminf<=1; so if a limit exists it is 1 | `NTKB.HardyWright.primeCounting_mul_log_div_limits` | proved |  |
| Corollary 8.10 | 383 | For next prime p', limsup (p'-p)/log p>=1 and liminf<=1 | `NTKB.NZM.exists_large_prime_gap`, `NTKB.NZM.exists_small_prime_gap`, `NTKB.HardyWright.nth_prime_asymptotic` | proved |  |
| Theorem 8.11 | 386 | Every Dirichlet series has a unique abscissa of absolute convergence; uniform convergence on [c,infinity) for c>σ_a | `NTKB.NZM.lseriesSummable_iff_abscissa`, `NTKB.NZM.abscissaOfAbsConv_unique`, `NTKB.NZM.tendstoUniformlyOn_LSeries` | proved | Mathlib: `LSeriesSummable_of_abscissaOfAbsConv_lt_re`, Mathlib: `LSeriesSummable_lt_re_of_abscissaOfAbsConv_lt_re` |
| Corollary 8.12 | 386 | A(s) is continuous on (σ_a, infinity) | `NTKB.NZM.continuousOn_LSeries` | proved | Mathlib: `LSeries_differentiableOn`, Mathlib: `LSeries_analyticOnNhd` |
| Theorem 8.13 | 387 | σ_a<=c iff Σ_{n<=x}abs(a_n)=O(x^c), with converse for c>max(0,σ_a) | `NTKB.NZM.abscissaOfAbsConv_le_of_sum_norm_isBigO`, `NTKB.NZM.sum_norm_isBigO_of_abscissaOfAbsConv_lt` | proved | Tau Ceti: `abscissaOfAbsConv_le_iff_sum_norm_isBigO` |
| Theorem 8.14 | 388 | Product of absolutely convergent Dirichlet series A(s)B(s) is the Dirichlet series of the convolution | `LSeries_convolution'`, `LSeries_convolution`, `LSeriesSummable.convolution` | in Mathlib |  |
| Theorem 8.15 | 389 | 1/ζ(s)=Σμ(n)/n^s for s>1 | `LSeries_zeta_mul_Lseries_moebius`, `LSeries_one_mul_Lseries_moebius`, `abscissaOfAbsConv_moebius` | in Mathlib |  |
| Lemma 8.16 | 390 | Dominated convergence for series: if abs(M_n(x))<=M_n, summable, and limits exist, then the limit of the sum is the sum of limits | `tendsto_tsum_of_dominated_convergence` | in Mathlib |  |
| Theorem 8.17 | 390 | A Dirichlet series vanishing for all large s has all coefficients zero; uniqueness of Dirichlet series expansion | `LSeries_eq_zero_iff`, `LSeries_injOn`, `eq_of_LSeries_eventually_eq` | in Mathlib |  |
| Theorem 8.18 | 392 | Euler product: for multiplicative f with absolutely convergent F(s), F(s)=Π_p(1+f(p)/p^s+f(p^2)/p^{2s}+...) | `eulerProduct_tprod`, `DirichletCharacter.LSeries_eulerProduct` | in Mathlib |  |
| Corollary 8.19 | 393 | For totally multiplicative f, F(s)=Π_p (1-f(p)/p^s)^{-1} | `eulerProduct_completely_multiplicative_tprod`, `riemannZeta_eulerProduct_tprod` | in Mathlib |  |
| Corollary 8.20 | 394 | Σμ(n)^2/n^s=ζ(s)/ζ(2s) for s>1 | `NTKB.HardyWright.LSeries_powerFreeIndicator` | proved |  |
| Theorem 8.21 | 395 | Term-by-term differentiation: abscissa of B(s)=-Σa_n log n/n^s equals σ_a and A'(s)=B(s) | `LSeries_deriv`, `LSeries_hasDerivAt`, `abscissaOfAbsConv_logMul` | in Mathlib |  |
| Corollary 8.22 | 396 | Series -ζ'(s)=Σlog n/n^s and -ζ'(s)/ζ(s)=ΣΛ(n)/n^s have abscissa 1 and these values for s>1 | `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`, `LSeries_vonMangoldt_eq`, `LSeriesSummable_vonMangoldt` | in Mathlib |  |
| Theorem 8.23 | 397 | ζ(s)=1/(s-1)+O(1), ζ'(s)=-1/(s-1)^2+O(1), ζ'/ζ(s)=-1/(s-1)+O(1) near s=1 | `isBigO_riemannZeta_sub_one_div`, `deriv_riemannZeta_add_inv_sub_sq_bounded`, `log_deriv_riemannZeta_add_inv_sub_bounded` | in Mathlib |  |
| Theorem 8.24 | 401 | Σ_{n<=x}φ(n)/n=(6/π^2)x+O(log x) | `NTKB.NZM.abs_sum_totient_div_sub_le` | proved |  |
| Theorem 8.25 | 401 | Number of squarefree n<=x is (6/π^2)x+O(sqrt x) | `NTKB.HardyWright.squarefreeCount_sub_isBigO` | proved |  |
| Theorem 8.26 | 402 | Σ_{n<=x}ω(n)=x log log x+bx+O(x/log x) | `NTKB.NZM.sum_cardDistinctFactors_sub_isBigO`, `NTKB.HardyWright.tendsto_sum_cardDistinctFactors_sub` | proved |  |
| Lemma 8.27 | 403 | Σ_{n<=x}1/n=log x+γ+O(1/x) | `NTKB.HardyWright.sum_inv_eq_log_add_eulerMascheroni`, `NTKB.Apostol.abs_sum_inv_sub_log_sub_eulerMascheroni_le` | proved | Mathlib: `tendsto_harmonic_sub_log`, Mathlib: `eulerMascheroniSeq_lt_eulerMascheroniConstant` |
| Theorem 8.28 | 404 | Σ_{n<=x}d(n)=x log x+(2γ-1)x+O(sqrt x) | `NTKB.Apostol.abs_sum_sigma_zero_sub_le`, `NTKB.HardyWright.sum_card_divisors_sub_isBigO` | proved | Mathlib: `sum_Ioc_sigma0_eq_sum_div` |
| Theorem 8.29 | 404 | Number of n in an interval of length N coprime to q is (φ(q)/q)N+O(2^{ω(q)}) | `NTKB.NZM.abs_card_coprime_Ioc_sub_le` | proved |  |
| Theorem 8.30 | 405 | ω(n)<=(1+ε)log n/log log n for large n, and this is sharp | `NTKB.NZM.omega_lt_of_large`, `NTKB.NZM.omega_gt_infinitely_often`, `NTKB.NZM.omegaOrderStatement` | proved |  |
| Theorem 8.31 | 407 | d(n)<n^{(1+ε)log 2/log log n} for large n | `NTKB.Apostol.apostol_thm_13_12_a`, `NTKB.HardyWright.eventually_log_card_divisors_lt` | proved | Tau Ceti: `exists_pos_card_divisors_le_rpow` |
| Theorem 8.32 | 407 | Σ_{n<=x}(ω(n)-log log n)^2=O(x log log x) (Turan variance) | `NTKB.NZM.sum_sq_omega_sub_loglog_le`, `NTKB.HardyWright.sum_sq_cardDistinctFactors_sub_le` | proved |  |
| Corollary 8.33 | 409 | Hardy-Ramanujan: abs(ω(n)-log log n)<(log log n)^{3/4} for all but O(x/(log log x)^{1/2}) integers n<=x | `NTKB.NZM.card_bad_omega_le`, `NTKB.HardyWright.sum_sq_cardDistinctFactors_sub_le` | proved |  |
| Definition (Riemann zeta function) | 386 | ζ(s)=Σ_{n>=1}1/n^s for s>1 | `zeta_eq_tsum_one_div_nat_add_one_cpow` | in Mathlib |  |
| Definition (abscissa of absolute convergence) | 386 | The unique σ_a with absolute convergence for s>σ_a but not s<σ_a | — | in Mathlib |  |
| Definition (Dirichlet convolution of sequences) | 388 | c_r=Σ_{d divides r}a_d b_{r/d} | — | in Mathlib |  |
| Definition (Euler's constant) | 403 | γ=0.5772... defined as the constant in Σ1/n=log x+γ+O(1/x) | — | in Mathlib |  |

## Chapter 9

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Theorem 9.1 | 421 | Division algorithm in Q[x]: f = gq + r with r = 0 or deg r < deg g, q and r unique | `div_add_mod`, `div_modByMonic_unique` | in Mathlib |  |
| Theorem 9.2 | 422 | Any f, g not both zero have a common divisor h = fF + gG | `gcd_eq_gcd_ab`, `exists_gcd_eq_mul_add_mul` | in Mathlib |  |
| Theorem 9.3 | 422 | Unique monic gcd d: divides both, linear combination, divisible by every common divisor | `gcd_eq_gcd_ab`, `gcd_dvd_left`, `dvd_gcd` | in Mathlib |  |
| Definition 9.1 | 423 | The monic polynomial d of Theorem 9.3 is the gcd (f, g) | — | in Mathlib |  |
| Definition 9.2 | 423 | Irreducible (prime) polynomial over Q: no factoring into two polynomials of positive degree | `Irreducible` | in Mathlib |  |
| Theorem 9.4 | 423 | An irreducible polynomial dividing fg divides f or g | `Irreducible.prime` | in Mathlib |  |
| Theorem 9.5 | 423 | Unique factorization of a polynomial over Q into constant times monic irreducibles | `to_uniqueFactorizationMonoid`, `exists_prime_factors` | in Mathlib |  |
| Definition 9.3 | 424 | Integer-coefficient polynomial is primitive if the gcd of its coefficients is 1 | `IsPrimitive` | in Mathlib |  |
| Theorem 9.6 | 424 | The product of two primitive polynomials is primitive | `IsPrimitive.mul` | in Mathlib |  |
| Theorem 9.7 | 424 | Gauss's lemma: monic integer f = gh with g, h monic over Q implies g, h have integer coefficients | `IsIntegrallyClosed.eq_map_mul_C_of_dvd`, `integralClosure.mem_lifts_of_monic_of_dvd_map`, `IsPrimitive.Int.irreducible_iff_irreducible_map_cast` | in Mathlib |  |
| Definition 9.4 | 425 | Algebraic number: complex number that is a root of a nonzero polynomial over Q | `IsAlgebraic` | in Mathlib |  |
| Theorem 9.8 | 426 | An algebraic number has a unique monic irreducible polynomial over Q, dividing every polynomial vanishing at it | — | in Mathlib |  |
| Definition 9.5 | 426 | Minimal equation, minimal polynomial and degree of an algebraic number | — | in Mathlib |  |
| Definition 9.6 | 426 | Algebraic integer: root of a monic integer polynomial | `IsIntegral` | in Mathlib |  |
| Theorem 9.9 | 426 | A rational algebraic integer is a rational integer | `algebraMap_eq_of_integral`, `isIntegral_iff` | in Mathlib |  |
| Theorem 9.10 | 427 | The minimal polynomial of an algebraic integer is monic with integer coefficients | `isIntegrallyClosed_eq_field_fractions`, `isIntegrallyClosed_dvd` | in Mathlib |  |
| Theorem 9.11 | 427 | If a nonzero rational vector satisfies a matrix equation with entries a_ij, the eigenvalue xi is algebraic (algebraic integer if a_ij integers) | `LinearMap.exists_monic_and_aeval_eq_zero`, `isIntegral_of_smul_mem_submodule`, `IsIntegral.of_finite` | in Mathlib |  |
| Theorem 9.12 | 428 | Sum and product of algebraic numbers (algebraic integers) are algebraic (algebraic integers) | `IsIntegral.add`, `IsIntegral.mul` | in Mathlib |  |
| Theorem 9.13 | 428 | Algebraic numbers form a field and algebraic integers form a ring | — | in Mathlib |  |
| Definition 9.a | 420 | Polynomial over Q, degree, leading coefficient, monic, divisibility of polynomials (candidates D178-D182) | `Polynomial`, `Monic` | in Mathlib |  |
| Definition 9.b | 426 | Transcendental number: complex number that is not algebraic (candidates D186, D196) | `Transcendental` | in Mathlib |  |
| Definition 9.c | 430 | The extension field Q(xi) of Q by an algebraic number xi, and algebraic number field | `NumberField` | in Mathlib |  |
| Theorem 9.14 | 431 | If xi has degree n, every element of Q(xi) is uniquely a_0 + a_1 xi + ... + a_{n-1} xi^{n-1} | `adjoin.powerBasis` | in Mathlib |  |
| Definition 9.d | 431 | Congruence of polynomials modulo G(x) and residue system | `AdjoinRoot` | partly in other libraries; not proved here |  |
| Theorem 9.15 | 432 | Polynomials of degree below n over Q with arithmetic modulo G(x) form a ring | `AdjoinRoot` | in Mathlib |  |
| Theorem 9.16 | 432 | The ring modulo G(x) is a field iff G irreducible; for G the minimal polynomial of xi it is isomorphic to Q(xi) | `NTKB.NZM.isField_adjoinRoot_iff_irreducible`, `NTKB.NZM.adjoinRootMinpolyEquiv` | proved |  |
| Theorem 9.17 | 435 | For any algebraic alpha there is a rational integer b with b alpha an algebraic integer | `exists_integral_multiple` | in Mathlib |  |
| Theorem 9.18 | 435 | The integers of an algebraic number field form a ring | `RingOfIntegers` | in Mathlib |  |
| Definition 9.7 | 436 | Divisibility, unit, associates for integers of an algebraic number field (candidates D189-D192) | `IsUnit`, `Associated` | in Mathlib |  |
| Theorem 9.19 | 436 | The reciprocal of a unit is a unit; units form a multiplicative group (hence associate is symmetric) | `isUnit_iff_exists_inv`, `Units` | in Mathlib |  |
| Theorem 9.20 | 437 | Quadratic field Q(sqrt m), m squarefree not 1; its integers are a+b sqrt m for m = 2,3 mod 4 and (a+b sqrt m)/2 with a,b odd allowed for m = 1 mod 4 | `NTKB.NZM.isIntegral_quadratic_iff`, `NTKB.NZM.isIntegral_iff_half`, `NTKB.HardyWright.exists_int_of_isIntegral`, `NTKB.HardyWright.isIntegral_mk_int`, `NTKB.HardyWright.exists_half_of_isIntegral`, `NTKB.HardyWright.isIntegral_mk_half` | proved | Tau Ceti: `isIntegral_iff_of_mod_four_ne_one`, Tau Ceti: `isIntegral_iff_of_mod_four_eq_one` |
| Definition 9.8 | 438 | Norm of a number in Q(sqrt m) as product with its conjugate | `norm_def` | in Mathlib |  |
| Theorem 9.21 | 438 | Norm is multiplicative, vanishes only at 0, integer norm for integers, N(gamma) = ±1 iff gamma is a unit | `norm_mul`, `norm_eq_zero_iff`, `norm_eq_one_iff`, `isUnit_iff_norm` | in Mathlib |  |
| Theorem 9.22 | 439 | Units of imaginary quadratic fields are ±1 except Q(i) (±1, ±i) and Q(sqrt -3) (six units) | `NTKB.HardyWright.ncard_unities_of_neg`, `NTKB.HardyWright.isUnity_iff_norm` | proved | Tau Ceti: `card_units_of_isTotallyComplex`, Tau Ceti: `eq_one_or_neg_one_of_isTotallyComplex`, Tau Ceti: `torsionOrder_eq_of_minpoly_eq_X_sq_sub_C` |
| Definition 9.e | 439 | Imaginary (m<0) and real (m>1) quadratic field (candidate D193) | `IsTotallyReal`, `IsTotallyComplex` | partly in other libraries; not proved here |  |
| Theorem 9.23 | 440 | Every real quadratic field has infinitely many units | `NTKB.NZM.infinite_unities_of_one_lt` | proved | Mathlib: `exists_of_not_isSquare`, Mathlib: `exists_pos_of_not_isSquare` |
| Definition 9.9 | 440 | Prime of Q(sqrt m): non-unit algebraic integer divisible only by associates and units | `Irreducible` | in Mathlib |  |
| Theorem 9.24 | 440 | If the norm of an integer of Q(sqrt m) is ±p for a rational prime p, it is a prime | `NTKB.HardyWright.zsqrtd_irreducible_of_natAbs_norm_prime`, `NTKB.HardyWright.qa_irreducible_of_natAbs_norm_prime` | proved |  |
| Theorem 9.25 | 440 | Every nonzero nonunit integer of Q(sqrt m) factors into primes | `exists_factors`, `exists_irreducible_factor` | in Mathlib |  |
| Definition 9.10 | 441 | Unique factorization property for integers of a quadratic field | `UniqueFactorizationMonoid` | in Mathlib |  |
| Definition 9.11 | 441 | Q(sqrt m) is (norm-)Euclidean: for alpha, beta there are gamma, delta with alpha = beta gamma + delta and \\| N(delta) \\| < \\| N(beta) \\| | `NTKB.HardyWright.IsNormEuclidean` | proved | Mathlib: `EuclideanDomain` |
| Theorem 9.26 | 441 | Every Euclidean quadratic field has unique factorization | `to_uniqueFactorizationMonoid` | in Mathlib |  |
| Theorem 9.27 | 442 | Q(sqrt m) is Euclidean for m = -1, -2, -3, -7, 2, 3 | `NTKB.HardyWright.isNormEuclidean_iff_of_neg`, `NTKB.HardyWright.isNormEuclidean_of_mem` | proved | Mathlib: `norm_mod_lt`, Mathlib: `natAbs_norm_mod_lt` |
| Theorem 9.28 | 444 | In a UFD quadratic field each prime divides exactly one rational prime | `NTKB.HardyWright.existsUnique_nat_prime_dvd` | proved |  |
| Theorem 9.29 | 444 | In a UFD quadratic field: splitting of rational primes (prime or product of two primes, Legendre symbol criterion, prime 2 cases, ramified primes) | `NTKB.NZM.prime_or_mul_of_finrank_two`, `NTKB.NZM.Theorem929` | proved in part |  |
| Lemma 9.30 | 452 | Every integer of Q(sqrt -3) is congruent to 0, 1 or -1 modulo theta = sqrt -3 | `NTKB.NZM.lemma_9_30` | proved |  |
| Lemma 9.31 | 452 | For xi, eta not divisible by theta: xi ≡ ±1 (mod theta) implies xi^3 ≡ ±1 (mod theta^4), and related sum/difference of cubes | `NTKB.NZM.lemma_9_31_sub_one`, `NTKB.NZM.lemma_9_31_add_one`, `NTKB.NZM.lemma_9_31_cube_add`, `NTKB.NZM.lemma_9_31_cube_sub` | proved | Mathlib: `a_cube_b_cube_congr_one_or_neg_one`, Mathlib: `cube_of_castHom_ne_zero` |
| Lemma 9.32 | 453 | If a^3 + b^3 + c^3 = 0 with gcd 1 then theta divides exactly one of them | `NTKB.NZM.lemma_9_32` | proved | Mathlib: `lambda_sq_dvd_or_dvd_or_dvd` |
| Lemma 9.33 | 453 | If a^3 + e1 b^3 + e2 (theta^r c)^3 = 0 with theta not dividing abc, then e1 = ±1 and r >= 2 (OCR of 9.33) | `NTKB.NZM.lemma_9_33` | proved | Mathlib: `lambda_pow_four_dvd_c_cube`, Mathlib: `lambda_sq_dvd_c`, Mathlib: `u₄_eq_one_or_neg_one` |
| Lemma 9.34 | 454 | No nonzero a, b, c with a^3 + b^3 + e (theta^r c)^3 = 0, r >= 2, theta not dividing the others (descent) | `NTKB.NZM.lemma_9_34` | proved | Mathlib: `exists_Solution_multiplicity_lt`, Mathlib: `Solution.exists_minimal` |
| Theorem 9.35 | 455 | a^3 + b^3 + c^3 = 0 has no solution in nonzero integers of Q(sqrt -3); x^3 + y^3 = z^3 has no positive integer solutions | — | in Mathlib |  |

## Chapter 10

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Definition 10.1 | 457 | The partition function p(n) is the number of ways to write n as an unordered sum of positive integers (parts), with p(0) = 1 | `Nat.Partition` | in Mathlib |  |
| Definition 10.2 | 457 | p_m(n): partitions into parts at most m; p^o(n): into odd parts; p^d(n): into distinct parts; q^e(n), q^o(n): into an even or odd number of distinct parts | `NTKB.HardyWright.evenDistinctCount`, `NTKB.HardyWright.oddDistinctCount` | proved | Mathlib: `Nat.Partition.restricted`, Mathlib: `Nat.Partition.odds`, Mathlib: `Nat.Partition.distincts`, Mathlib: `Nat.Partition.countRestricted` |
| Theorem 10.1 | 458 | Basic relations: p_m(n) = p(n) for n <= m; p_m(n) <= p(n); p_m(n) = p_{m-1}(n) + p_m(n-m); p^d(n) = q^e(n) + q^o(n) | `NTKB.NZM.card_restricted_le_eq_card_partition`, `NTKB.NZM.card_restricted_le_card_partition`, `NTKB.NZM.card_restricted_eq_add`, `NTKB.NZM.card_distincts_eq_even_add_odd` | proved |  |
| Theorem 10.2 | 458 | The number of partitions of n into distinct parts equals the number into odd parts | `card_odds_eq_card_distincts` | in Mathlib |  |
| Theorem 10.3 | 459 | Partitions of n into m parts are equinumerous with partitions with largest part m (via conjugation); also at most m parts versus parts at most m | `NTKB.HardyWright.card_partitions_parts_eq_card_partitions_largest`, `NTKB.HardyWright.card_partitions_parts_le_eq_card_partitions_largest_le` | proved | Mathlib: `conjugate_conjugate` |
| Theorem 10.4 | 459 | q^e(n) - q^o(n) equals (-1)^j if n = j(3j +- 1)/2, and 0 otherwise | `NTKB.HardyWright.evenDistinctCount_sub_oddDistinctCount` | proved |  |
| Definition (formal power series) | 463 | Formal power series a_0 + a_1 x + ...; equality coefficientwise; Cauchy product; units are those with nonzero constant term; infinite products defined when each power of x occurs in finitely many factors | `PowerSeries` | in Mathlib |  |
| Definition (generating function for p(n)) | 466 | The product of (1 - x^n)^(-1) is the generating function of p(n) (and of p_m, p^o, p^d analogously) | `Nat.Partition.genFun`, `hasProd_genFun`, `hasProd_powerSeriesMk_card_restricted` | in Mathlib |  |
| Theorem 10.5 | 467 | Euler's identity: p(n) = p(n-1) + p(n-2) - p(n-5) - p(n-7) + ... over generalized pentagonal numbers | `NTKB.HardyWright.card_partition_pentagonal_recurrence`, `NTKB.Apostol.sum_negOnePow_card_partition_sub_pentagonal` | proved |  |
| Theorem 10.6 | 468 | For 0 < x < 1, the series of p_m(n) x^n converges and equals 1 over the finite product of (1 - x^n), n <= m | `NTKB.NZM.hasSum_card_restricted_mul_pow` | proved | Mathlib: `hasProd_powerSeriesMk_card_restricted` |
| Theorem 10.7 | 469 | For 0 < x < 1 the limit of the finite products of (1 - x^n) exists and is nonzero | `NTKB.NZM.exists_tendsto_eulerPartialProd` | proved | Mathlib: `multipliable_one_sub_pow_add`, Tau Ceti: `tprod_one_sub_pow_ne_zero` |
| Theorem 10.8 | 470 | For 0 < x < 1 the series of p(n) x^n converges and equals the reciprocal of the product of (1 - x^n) | `NTKB.NZM.hasSum_card_partition_mul_pow` | proved | Mathlib: `hasProd_genFun`, Mathlib: `hasProd_powerSeriesMk_card_restricted` |
| Theorem 10.9 | 470 | Euler's pentagonal formula: the product of (1 - x^n) equals 1 + sum of (-1)^j (x^(j(3j-1)/2) + x^(j(3j+1)/2)) for 0 < x < 1 | `eulerFunction_eq_tprod`, `eulerFunction_eq_tsum_pentagonal`, `tprod_one_sub_X_pow` | in Mathlib |  |
| Lemma 10.10 | 471 | Cauchy product of absolutely convergent power series converges to the product; equal power series on an interval have equal coefficients | `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`, `HasFPowerSeriesAt.eq_formalMultilinearSeries` | in Mathlib |  |
| Theorem 10.11 | 471 | Recurrence for the sum of divisors sigma(n) along pentagonal numbers: sigma(n) - sigma(n-1) - sigma(n-2) + sigma(n-5) + ... equals (-1)^(j+1) n if n is a pentagonal number, else 0 | `NTKB.NZM.sum_sigma_mul_pentagonal`, `NTKB.NZM.sum_sigma_mul_pentagonal_of_pentagonal`, `NTKB.NZM.sum_sigma_mul_pentagonal_of_not_pentagonal` | proved |  |
| Theorem 10.12 | 473 | Bounds 2^(sqrt n) < p(n) < exp(c sqrt n), c = pi sqrt(2/3) | `NTKB.NZM.two_rpow_sqrt_lt_card_partition`, `NTKB.NZM.two_rpow_sqrt_lt_card_partition_lt_exp`, `NTKB.Apostol.card_partition_lt_exp` | proved |  |
| Theorem 10.13 | 474 | Jacobi's formula: the product of (1 - x^n)^3 equals sum over j >= 0 of (-1)^j (2j+1) x^(j(j+1)/2) | `NTKB.Apostol.apostol_thm_14_7`, `NTKB.HardyWright.jacobi_cube_identity` | proved |  |
| Theorem 10.14 | 478 | For prime p and 0 < x < 1, phi(x^p)/phi(x)^p = 1 + sum a_j x^j with integers a_j divisible by p | `NTKB.NZM.exists_expand_pentagonalSeries_eq_pow_mul` | proved |  |
| Theorem 10.15 | 480 | The fourth power of the Euler product has integer coefficients b_m with b_m = 0 mod 5 when m = 0 mod 5 | `NTKB.NZM.five_dvd_coeff_X_mul_pentagonalSeries_pow_four` | proved |  |
| Theorem 10.16 | 481 | Ramanujan's congruence p(5m + 4) = 0 mod 5 | `NTKB.HardyWright.five_dvd_card_partition` | proved |  |

## Chapter 11

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Definition (disjoint sets) | 483 | Sets A and B with no common element are disjoint | `Disjoint` | in Mathlib |  |
| Definition 11.1 | 484 | The asymptotic density of a set A of positive integers is the liminf of A(n)/n; it is the natural density if the limit exists | `NTKB.NZM.asymptoticDensity`, `NTKB.NZM.HasNaturalDensity` | proved |  |
| Theorem 11.1 | 484 | For an infinite sequence a_1 < a_2 < ..., the asymptotic density is liminf of n / a_n, and the natural density if it exists is lim n / a_n | `NTKB.NZM.asymptoticDensity_range`, `NTKB.NZM.hasNaturalDensity_range_iff` | proved |  |
| Theorem 11.2 | 485 | Every integer greater than 1 is a sum of two squarefree integers | `NTKB.NZM.exists_squarefree_add` | proved |  |
| Lemma 11.3 | 485 | Among 1, ..., n at least n/2 integers are squarefree | `NTKB.NZM.two_mul_card_squarefree_ge`, `NTKB.NZM.lt_two_mul_card_squarefree` | proved |  |
| Definition 11.2 | 487 | The Schnirelmann density of a set of non-negative integers is the infimum over n >= 1 of A(n)/n, where A(n) counts positive elements up to n | — | in Mathlib |  |
| Definition 11.3 | 488 | The sum A + B of sets of non-negative integers is the set of all a + b | `Set.mul` | in Mathlib |  |
| Lemma 11.4 | 489 | Shifting step: if B_1 is not contained in A_1, there are A_2, B_2 with C_2 contained in C_1, B_2(g) < B_1(g) and the density inequality preserved | `NTKB.NZM.lemma_11_4` | proved |  |
| Lemma 11.5 | 489 | If B_1 is contained in A_1 and B_1(g) > 0, then A_1(z) >= A_1(b) + A_1(z - b) for suitable b, z | `NTKB.NZM.lemma_11_5` | proved |  |
| Lemma 11.6 | 489 | If A_1(y) < theta y for some y at most g, then y > a_0 | `NTKB.NZM.lemma_11_6` | proved |  |
| Lemma 11.7 | 490 | Construction of A_2 and B_2 in the case B_1 contained in A_1, with C_2 contained in C_1 and B_2(g) < B_1(g) | `NTKB.NZM.lemma_11_7` | proved |  |
| Lemma 11.8 | 490 | The density inequality A_2(m) + B_2(m) >= theta m holds for the new sets | `NTKB.NZM.lemma_11_8` | proved |  |
| Theorem 11.9 | 491 | If A_1(m) + B_1(m) >= theta m for m up to g, then C_1(g) >= theta g | `NTKB.NZM.theorem_11_9` | proved |  |
| Theorem 11.10 | 491 | The alpha-beta theorem (Mann): d(A + B) >= min(1, d(A) + d(B)) for sets containing 0 | `NTKB.NZM.theorem_11_10` | proved | Mathlib: `add_eq_univ_of_one_le_schirelmannDensity_add_schnirelmannDensity` |

## Appendix

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Appendix A.1 Lemma A.1 | 493 | A nonconstant complex polynomial P with P(z_0) nonzero has no local minimum of the modulus at z_0 | `NTKB.NZM.not_isLocalMin_norm_eval` | proved | Mathlib: `eventually_eq_or_eq_zero_of_isLocalMin_norm` |
| Appendix A.1 Theorem A.2 | 494 | Fundamental theorem of algebra: every complex polynomial of degree at least one has a complex root (hence n roots with multiplicity) | `exists_root` | in Mathlib |  |
| Appendix A.2 Definition (symmetric polynomial, elementary symmetric polynomials) | 495 | A polynomial in r_1, ..., r_n is symmetric if invariant under permuting the variables; sigma_k is the k-th elementary symmetric polynomial | `IsSymmetric` | in Mathlib |  |
| Appendix A.2 Definition (degree and leading term of a multivariable polynomial) | 496 | Degree of a monomial is the sum of exponents; degree of a polynomial is the maximum; lexicographic order of monomials and leading term | `IsHomogeneous` | in Mathlib |  |
| Appendix A.2 Theorem A.3 | 496 | Fundamental theorem of symmetric polynomials: every symmetric polynomial F in n variables is P(sigma_1, ..., sigma_n) with P having coefficients in the coefficient ring (integral linear combinations of those of F), and deg P is the highest power of r_1 in F | `esymmAlgHom_surjective`, `esymmAlgHom_injective` | partly in other libraries; not proved here |  |
| Appendix A.2 Definition A.1 | 498 | Discriminant of a polynomial f of degree n with leading coefficient a_n: a_n to the power 2n-2 times the product over i < j of (r_i - r_j)^2 | — | in Mathlib |  |
| Appendix A.2 Theorem A.4 | 498 | D(f) is a homogeneous integral polynomial of degree 2n-2 in the coefficients; and D(f) = D(g) g(r_1)^2 if f = (z - r_1) g | `NTKB.NZM.discr_X_sub_C_mul`, `NTKB.NZM.map_discr_eq_of_map_eq`, `NTKB.NZM.DiscrIsIntegralForm` | proved in part |  |
| Appendix A.2 Theorem A.5 | 499 | If p^s exactly divides D(f), f(a) = 0 mod p^j, p^t exactly divides f'(a), and j > s, then j > 2t + 1 (lifting singular solutions) | `NTKB.NZM.lift_singular_via_discr` | proved |  |
| Appendix A.3 Theorem A.6 | 501 | The sum of 1/n^2 over n >= 1 equals pi^2 / 6 | `hasSum_zeta_two` | in Mathlib |  |
| Appendix A.4 Definition A.2 | 504 | A sequence satisfies a linear recurrence of order k: u_n = b_1 u_{n-1} + ... + b_k u_{n-k} for n >= k | `LinearRecurrence`, `IsSolution` | in Mathlib |  |
| Appendix A.4 Theorem A.7 | 505 | A sequence satisfies a linear recurrence of order k iff its generating function has positive radius of convergence and is a rational function P/Q with degrees below k | `NTKB.NZM.recurrence_iff_rational` | proved |  |
| Appendix A.4 Lemma A.8 | 506 | Partial fractions: P/Q with deg P < k = deg Q splits as a sum of a_ij / (z - r_j)^i over the distinct roots r_j | `mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse`, `div_prod_eq_quo_add_sum_rem_div` | in Mathlib |  |
| Appendix A.4 Theorem A.9 | 507 | If Q has k distinct roots, then u_n = sum of beta_j lambda_j^n | `NTKB.NZM.solution_eq_sum_of_distinct_roots` | proved | Mathlib: `geom_sol_iff_root_charPoly`, Mathlib: `solSpace_rank` |
| Appendix A.4 Theorem A.10 | 508 | General solutions of a linear recurrence are sums of B_j(n) lambda_j^n with polynomial B_j of degree below the multiplicity (repeated roots), and conversely | `NTKB.NZM.solutionsAreExpPoly`, `NTKB.NZM.isSolution_of_expPoly`, `NTKB.NZM.expPoly_of_isSolution` | proved |  |
