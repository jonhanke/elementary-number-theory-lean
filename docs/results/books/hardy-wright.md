# G. H. Hardy and E. M. Wright, *An Introduction to the Theory of Numbers* (6th ed., 2008): map to the Lean library

Each row is a result of the book, the Lean declarations that formalize it, and its status, computed from the Lean kernel (an audit of the axioms and hypotheses of every declaration): *proved* means proved with only the standard axioms and no unproved input; *proved in part* that a part, a special case or one instance is proved; *proved, conditional* that an unproved input (a named statement) is assumed; *refuted as stated in the book* that the library proves the printed statement false and proves a corrected form (see the errata in the README); *in Mathlib* that Mathlib (a dependency) has the result and the Lean name is Mathlib's. Results that are only in Tau Ceti or PrimeNumberTheoremAnd (which this library does not depend on) are marked so. The statements in the third column are short descriptions, not quotations; read the book for the exact wording. The column *Also in* credits other libraries: Mathlib, Tau Ceti or PrimeNumberTheoremAnd declarations that prove the result, a part of it, or a closely related statement (as recorded by the coverage audit). Pages are pages of the pdf file of the 6th edition; theorems are numbered globally, as in the book.

Rows: 626. proved: 279; in Mathlib: 178; not formalized: 96; partly in other libraries; not proved here: 36; proved in part: 14; in Tau Ceti only (not a dependency): 12; in PrimeNumberTheoremAnd only (not a dependency): 6; refuted as stated in the book; corrected form proved: 4; proved, conditional: 1. Proved here and also in another library: 79.


## Chapter I. The series of primes (1)

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Theorem 1 | 21 | Every positive integer except 1 is a product of primes | `Nat.prod_primeFactorsList`, `Nat.exists_prime_and_dvd` | in Mathlib |  |
| Theorem 2 | 22 | Fundamental theorem of arithmetic: the standard form of n is unique | `Nat.primeFactorsList_unique`, `UniqueFactorizationMonoid.factors_unique` | in Mathlib |  |
| Theorem 3 | 22 | Euclid's first theorem: p prime and p divides ab implies p divides a or b | `Nat.Prime.dvd_mul`, `Int.Prime.dvd_mul` | in Mathlib |  |
| Theorem 4 | 24 | Euclid's second theorem: there are infinitely many primes | `Nat.exists_infinite_primes` | in Mathlib |  |
| Theorem 5 | 25 | There are arbitrarily long blocks of consecutive composite numbers | `NTKB.HardyWright.exists_consecutive_composites` | proved |  |
| Theorem 6 | 29 | Prime number theorem: pi(x) is asymptotic to x/log x | `NTKB.HardyWright.prime_number_theorem` | proved | PNT+: `pi_alt'`, PNT+: `pi_asymp` |
| Theorem 7 | 30 | Chebyshev: pi(x) has order of magnitude x/log x | `Chebyshev.pi_ge_of_four_le`, `Chebyshev.pi_ge'`, `Chebyshev.pi_le_log4_mul_div` | in Mathlib |  |
| Theorem 8 | 31 | The n-th prime p_n is asymptotic to n log n | `NTKB.HardyWright.nth_prime_asymptotic` | proved | PNT+: `nth_prime_asymp` |
| Theorem 9 | 31 | p_n has order of magnitude n log n | `NTKB.HardyWright.nth_prime_order` | proved | PNT+: `nth_prime_asymp`, Mathlib: `Chebyshev.pi_ge_of_four_le` |

## Chapter II. The series of primes (2)

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Theorem 10 | 34 | pi(x) > log log x for x > 2 | `NTKB.HardyWright.log_log_lt_primeCounting` | proved | Mathlib: `Chebyshev.pi_ge_of_four_le` |
| Theorem 11 | 34 | There are infinitely many primes of the form 4n+3 | `Nat.forall_exists_prime_gt_and_modEq`, `Nat.infinite_setOfPred_prime_and_eq_mod` | in Mathlib |  |
| Theorem 12 | 34 | There are infinitely many primes of the form 6n+5 | `Nat.forall_exists_prime_gt_and_modEq` | in Mathlib |  |
| Theorem 13 | 35 | If a, b are coprime, every odd prime divisor of a^2+b^2 has the form 4n+1 | `Nat.mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one`, `ZMod.mod_four_ne_three_of_sq_eq_neg_sq'` | in Mathlib |  |
| Theorem 14 | 35 | There are infinitely many primes of the form 8n+5 | `Nat.forall_exists_prime_gt_and_modEq` | in Mathlib |  |
| Theorem 15* | 35 | Dirichlet's theorem: infinitely many primes an+b when (a,b)=1 | `Nat.forall_exists_prime_gt_and_eq_mod`, `Nat.forall_exists_prime_gt_and_zmodEq` | in Mathlib |  |
| Theorem 16 | 36 | No two Fermat numbers have a common divisor greater than 1 | `Nat.coprime_fermatNumber_fermatNumber` | in Mathlib |  |
| Theorem 17 | 37 | If a > 2 and a^n+1 is prime then a is even and n is a power of 2 | `Nat.pow_of_pow_add_prime` | in Mathlib |  |
| Theorem 18 | 38 | If n > 1 and a^n-1 is prime then a = 2 and n is prime | `Nat.prime_of_pow_sub_one_prime` | in Mathlib |  |
| Theorem 19 | 39 | The series of reciprocals of primes diverges | `Nat.Primes.not_summable_one_div`, `not_summable_one_div_on_primes` | in Mathlib |  |
| Theorem 20 | 40 | pi(x) ≥ (log x)/(2 log 2) and p_n < 4^n | `NTKB.HardyWright.primeCounting_ge_log_div_and_nth_prime_lt` | refuted as stated in the book; corrected form proved | Mathlib: `Chebyshev.pi_ge_of_four_le`, Mathlib: `primorial_lt_four_pow` |
| Theorem 21 | 41 | No non-constant integer polynomial f(n) is prime for all n (or all large n) | `NTKB.HardyWright.not_eventually_prime_polynomial` | proved |  |
| Theorem 22 | 41 | A polynomial in n, 2n, ..., kn with integer coefficients tending to infinity is composite for infinitely many n | `NTKB.HardyWright.infinite_not_prime_polynomial_exp` | proved |  |
| Theorem 23 | 43 | Every non-zero modulus (additive subgroup of the integers) is the set of multiples of a positive integer d | `EuclideanDomain.instIsPrincipalIdealRing` | in Mathlib |  |
| Theorem 24 | 44 | The modulus xa+yb is the set of multiples of d = (a,b) | `Int.gcd_eq_gcd_ab` | in Mathlib |  |
| Theorem 25 | 44 | ax+by=n is soluble in integers iff d divides n | `Int.gcd_eq_gcd_ab`, `Int.isCoprime_iff_gcd_eq_one` | in Mathlib |  |
| Theorem 26 | 44 | Any common divisor of a and b divides d | `dvd_gcd` | in Mathlib |  |
| Theorem 27 | 44 | (a,b)=d and c>0 imply (ac,bc)=dc | `gcd_mul_left` | in Mathlib |  |

## Chapter III. Farey series and a theorem of Minkowski

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Theorem 28 | 47 | Successive Farey fractions h/k < h'/k' of order n satisfy kh' - hk' = 1. | `NTKB.NZM.farey_adjacent` | proved |  |
| Theorem 29 | 47 | For three successive Farey fractions the middle one is the mediant (h+h')/(k+k') up to the stated form h''/k'' = (h+h')/(k+k'). | — | not formalized |  |
| Theorem 30 | 47 | Successive Farey fractions of order n have k + k' > n. | `NTKB.NZM.farey_adjacent` | proved |  |
| Theorem 31 | 48 | For n > 1 no two successive Farey fractions of order n share a denominator. | — | not formalized |  |
| Section 3.2 (equivalence of Theorems 28 and 29) | 48 | Each of Theorems 28 and 29 implies the other. | — | not formalized |  |
| Section 3.4 (successor rule) | 50 | The successor of h/k in the Farey series of order n is x/y with kx - hy = 1 and n-k < y <= n (worked example 4/9 -> 5/11 for n=13). | — | not formalized |  |
| Theorem 32 | 53 | The map (x,y) -> (ax+by, cx+dy) with integer coefficients and nonzero determinant sends Z^2 onto itself iff the determinant is +-1. | `NTKB.NZM.matrixLattice_eq_iff` | proved | Mathlib: `Matrix.isUnit_iff_isUnit_det`, Mathlib: `Int.isUnit_iff` |
| Theorem 33 | 53 | The lattice based on points OP, OQ is equivalent to the integer lattice iff the parallelogram OPQ has area 1. | `NTKB.NZM.matrixLattice_eq_iff`, `NTKB.NZM.matrixLattice_subset_iff` | proved in part |  |
| Section 3.6 (visible points) | 53 | A lattice point (x,y) is visible from the origin iff (x,y) = 1. | — | not formalized |  |
| Theorem 34 | 54 | For visible P, Q with parallelogram area S: no lattice point inside iff S = 1; if S > 1 there is at least one inside, and two unless it is the centre. | — | not formalized |  |
| Theorem 35 | 56 | In the Farey dissection of order n > 1 each half-arc around h/k has length between 1/(k(2n-1)) and 1/(k(n+1)). | — | not formalized |  |
| Theorem 36 | 56 | For real xi and positive n there is a reduced h/k with 0<k<=n and \\|xi - h/k\\| below 1/(k(n+1)) (bound as in book; OCR of strictness garbled). | `Real.exists_rat_abs_sub_le_and_den_le` | in Mathlib |  |
| Section 3.9 (equivalence of the two definitions of convex region) | 56 | A region is convex via chords iff through every boundary point there is a supporting line. | — | not formalized |  |
| Theorem 37 | 58 | Minkowski: a convex region symmetric about 0 of area > 4 contains a nonzero integer lattice point. | `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`, `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure` | in Mathlib |  |
| Theorem 38 | 58 | If translates of an open region R0 by the lattice points are pairwise disjoint then area(R0) <= 1. | `MeasureTheory.exists_pair_mem_lattice_not_disjoint_vadd` | in Mathlib |  |
| Theorem 39 | 60 | The map (3.6.1) preserves a general lattice iff its determinant is +-1 (same statement as Theorem 32, in oblique coordinates). | `Matrix.isUnit_iff_isUnit_det`, `Int.isUnit_iff` | partly in other libraries; not proved here |  |
| Theorem 40 | 60 | For lattice points P, Q the lattice based on OP, OQ equals the lattice iff the area of OPQ equals the fundamental parallelogram area. | `NTKB.NZM.matrixLattice_eq_iff`, `NTKB.NZM.matrixLattice_subset_iff` | proved in part |  |
| Theorem 41 | 61 | For any lattice with disjoint translates of R0, area(R0) is at most that of the fundamental parallelogram. | `MeasureTheory.exists_pair_mem_lattice_not_disjoint_vadd` | in Mathlib |  |
| Theorem 42 | 62 | If a parallelogram R0 has area equal to the fundamental parallelogram and no two equivalent interior points, translates of its closure cover the plane. | — | not formalized |  |
| Section 3.11 (n-dimensional remark) | 62 | Minkowski's theorem holds in n dimensions with volume bound 2^n. | `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure` | in Mathlib |  |

## Chapter IV. Irrational numbers

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Theorem 43 | 66 | sqrt 2 is irrational. | `irrational_sqrt_two` | in Mathlib |  |
| Theorem 44 | 66 | The m-th root of N is irrational unless N is an m-th power of an integer. | `irrational_nrt_of_notint_nrt` | in Mathlib |  |
| Theorem 45 | 67 | A real root of a monic integer polynomial is an integer or irrational. | `isInteger_of_is_root_of_monic` | in Mathlib |  |
| Section 4.6 (sqrt 5 irrational, geometric proof) | 71 | sqrt 5 is irrational by infinite descent on golden-section segments. | `Nat.Prime.irrational_sqrt` | in Mathlib |  |
| Section 4.7 (sqrt 2 + sqrt 3 irrational) | 72 | sqrt 2 + sqrt 3 is irrational since it is a non-integer root of x^4 - 10x^2 + 1. | — | not formalized |  |
| Theorem 46 | 72 | log_10 2 is irrational (more generally log_n m when one of m, n has a prime factor the other lacks). | — | not formalized |  |
| Theorem 47 | 72 | e is irrational. | — | not formalized |  |
| Section 4.7 (integrality lemma for f(x) = x^n(1-x)^n/n!) | 72 | f and all its derivatives take integer values at 0 and 1 and 0 < f < 1/n! on (0,1). | `NTKB.NZM.factorial_dvd_iterate_derivative_X_pow_mul` | proved in part |  |
| Theorem 48 | 73 | e^y is irrational for every nonzero rational y. | — | not formalized |  |
| Theorem 49 | 73 | pi and pi^2 are irrational. | `irrational_pi` | partly in other libraries; not proved here |  |
| Section 4.7 notes (zeta(2) irrational) | 74 | zeta(2) = pi^2/6 is irrational by Theorem 49, and zeta(m) for even m (Theorem 205). | — | not formalized |  |
| Section 4.7 notes (Apery, zeta(3)) | 74 | zeta(3) is irrational (Apery 1978). | — | not formalized |  |

## Chapter V. Congruences and residues

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Theorem 50 | 76 | gcd(a,b) is the product of p^min(exponents) | `Nat.factorization_gcd` | in Mathlib |  |
| Theorem 51 | 77 | lcm{a,b} is the product of p^max(exponents) | `Nat.factorization_lcm` | in Mathlib |  |
| Theorem 52 | 77 | gcd(a,b) * lcm{a,b} = ab (lcm = ab/gcd) | `Nat.gcd_mul_lcm`, `gcd_mul_lcm` | in Mathlib |  |
| Section 5.2-5.3 (properties (i)-(vi)) | 79 | congruence is symmetric, transitive, compatible with sums, products, powers, integer polynomials | `Nat.ModEq.add`, `Nat.ModEq.mul`, `Nat.ModEq.pow` | in Mathlib |  |
| Theorem 53 | 79 | congruent mod m and mod n implies congruent mod lcm; mod mn if coprime | `Nat.modEq_and_modEq_iff_modEq_lcm`, `Nat.modEq_and_modEq_iff_modEq_mul` | in Mathlib |  |
| Theorem 54 | 80 | ka = ka' mod m iff a = a' mod m/gcd(k,m) | `NTKB.HardyWright.modEq_mul_left_iff_modEq_div_gcd` | proved | Mathlib: `Nat.ModEq.cancel_left_div_gcd` |
| Theorem 55 | 80 | if gcd(k,m)=1, ka = ka' mod m iff a = a' mod m | `Nat.ModEq.cancel_left_of_coprime` | in Mathlib |  |
| Theorem 56 | 80 | k times a complete residue system mod m is again one when gcd(k,m)=1 | `NTKB.HardyWright.IsCompleteResidueSystem.mul`, `NTKB.HardyWright.IsCompleteResidueSystem.mul_add` | proved |  |
| Theorem 57 | 81 | kx = l mod m is solvable iff gcd(k,m) divides l, then exactly gcd solutions | `NTKB.HardyWright.exists_mul_modEq_iff_and_card` | proved | Mathlib: `Nat.exists_mul_mod_eq_gcd`, `Nat.exists_mul_mod_eq_one_of_coprime` |
| Theorem 58 | 82 | k times a complete reduced residue system is again one when gcd(k,m)=1 | `NTKB.HardyWright.IsReducedResidueSystem.mul` | proved |  |
| Theorem 59 | 82 | a'm + am' runs over a complete system mod mm' for coprime m,m' | `NTKB.HardyWright.IsCompleteResidueSystem.crt` | proved | Mathlib: `ZMod.chineseRemainder` |
| Theorem 60 | 83 | Euler phi is multiplicative | `Nat.totient_mul` | in Mathlib |  |
| Theorem 61 | 83 | for coprime m,m' the numbers am'+a'm over reduced systems form a reduced system mod mm' | `NTKB.HardyWright.IsReducedResidueSystem.crt` | proved |  |
| Theorem 62 | 83 | phi(m) = m * product over p dividing m of (1 - 1/p) | `Nat.totient_eq_mul_prod_factors`, `Nat.totient_eq_prod_factorization` | in Mathlib |  |
| Theorem 63 | 84 | sum of phi(d) over d dividing m equals m | `Nat.sum_totient` | in Mathlib |  |
| Theorem 64 | 85 | S(m,nn') = S(mn',n) S(mn,n') for coprime n,n' (quadratic Gauss sum) | `NTKB.HardyWright.gaussQuadSum_mul` | proved | Tau Ceti: `Matrix.sum_stdAddChar_dotProduct_mulVec_mul` |
| Theorem 65 | 86 | every q-th root of unity is a primitive r-th root for some r dividing q | `IsPrimitiveRoot.orderOf`, `orderOf_dvd_iff_pow_eq_one` | in Mathlib |  |
| Theorem 66 | 86 | the q-th roots of unity are e(h/q); primitive iff h prime to q | `Complex.mem_rootsOfUnity`, `Complex.isPrimitiveRoot_iff` | in Mathlib |  |
| Theorem 67 | 87 | Ramanujan sum c_q(m) is multiplicative in q | `NTKB.HardyWright.ramanujanSum_mul` | proved |  |
| Theorem 68 | 87 | Kloosterman sum multiplicativity S(u,v,n)S(u,v',n') = S(u,V,nn') | `NTKB.HardyWright.kloostermanSum_mul` | proved |  |
| Theorem 69 | 89 | if P is closed under sums and differences and r is least with P(r), then P holds exactly on multiples of r | `NTKB.HardyWright.general_principle` | proved | Mathlib: `orderOf_dvd_iff_pow_eq_one` |
| Section 5.8 (Gauss: regular p-gon, Fermat primes) | 90 | regular n-gon is constructible iff n is a product of a power of 2 and distinct Fermat primes (quoted from Gauss) | `NTKB.IrelandRosen.Constructible.isConstructible_exp_of_fermat` | proved in part |  |
| Section 5.8 (explicit 17-gon) | 91 | periods x1,x2,y1..y4 solve nested quadratics; closed form for 2 cos(2 pi/17) | — | not formalized |  |
| Section 5.8 notes (cyclotomic irreducibility) | 96 | the polynomial whose roots are the primitive n-th roots of unity is irreducible over Q | `Polynomial.cyclotomic.irreducible` | in Mathlib |  |

## Chapter VI. Fermat's theorem and its consequences

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Theorem 70 | 97 | a^p = a mod p for prime p | `Int.ModEq.pow_prime_eq_self` | in Mathlib |  |
| Theorem 71 | 97 | Fermat: a^(p-1) = 1 mod p if p does not divide a | `Nat.ModEq.pow_card_sub_one_eq_one`, `Int.ModEq.pow_card_sub_one_eq_one`, `ZMod.pow_card_sub_one_eq_one` | in Mathlib |  |
| Theorem 72 | 97 | Fermat-Euler: a^phi(m) = 1 mod m for gcd(a,m)=1 | `Nat.ModEq.pow_totient`, `ZMod.pow_totient` | in Mathlib |  |
| Theorem 73 | 98 | the binomial coefficients m(m-1)...(m-n+1)/n! and the rising version are integers | `NTKB.HardyWright.factorial_dvd_prod_consecutive` | proved | Mathlib: `Nat.descFactorial_eq_factorial_mul_choose`, `Nat.ascFactorial_eq_factorial_mul_choose` |
| Theorem 74 | 98 | product of n consecutive positive integers is divisible by n! | `Nat.factorial_dvd_ascFactorial` | in Mathlib |  |
| Theorem 75 | 99 | p divides C(p,r) for 0<r<p, p prime | `Nat.Prime.dvd_choose_self` | in Mathlib |  |
| Theorem 76 | 99 | all coefficients of (1-x)^(-p) are divisible by p except those of x^(kp), which are 1 mod p | `NTKB.HardyWright.coeff_invOneSubPow_prime`, `NTKB.HardyWright.choose_prime_sub_one_add_modEq` | proved |  |
| Theorem 77 | 100 | (x+y+...+w)^p = x^p+...+w^p mod p | `sum_pow_char`, `add_pow_char` | in Mathlib |  |
| Theorem 78 | 100 | if m = 1 mod p^a (a>0) then m^p = 1 mod p^(a+1) | `NTKB.HardyWright.pow_prime_modEq_one` | proved | Mathlib: `dvd_sub_pow_of_dvd_sub`, `Int.emultiplicity_pow_sub_pow` |
| Theorem 79 | 104 | (p-1)! = -(a/p) a^((p-1)/2) mod p | `NTKB.HardyWright.factorial_eq_neg_legendreSym_mul_pow` | proved | Mathlib: `ZMod.wilsons_lemma`, `legendreSym.eq_pow` |
| Theorem 80 | 104 | Wilson: (p-1)! = -1 mod p | `ZMod.wilsons_lemma` | in Mathlib |  |
| Theorem 81 | 105 | m>1 is prime iff m divides (m-1)!+1 | `Nat.prime_iff_fac_equiv_neg_one` | in Mathlib |  |
| Theorem 82 | 105 | -1 is a residue of primes 4k+1, a non-residue of 4k+3 | `ZMod.exists_sq_eq_neg_one_iff`, `legendreSym.at_neg_one` | in Mathlib |  |
| Theorem 83 | 105 | (a/p) = a^((p-1)/2) mod p (Euler criterion) | `legendreSym.eq_pow`, `ZMod.euler_criterion` | in Mathlib |  |
| Theorem 84 | 106 | an odd prime has (p-1)/2 residues and (p-1)/2 non-residues | `NTKB.HardyWright.card_residues_and_nonresidues` | proved | Mathlib: `quadraticChar_sum_zero` |
| Theorem 85 | 106 | residue*residue and nonresidue*nonresidue are residues, mixed products are non-residues | `legendreSym.mul` | in Mathlib |  |
| Theorem 86 | 106 | for p = 4k+1 there is x with 1+x^2 = mp, 0<m<p | `NTKB.HardyWright.exists_one_add_sq_eq_mul` | proved | Mathlib: `ZMod.exists_sq_eq_neg_one_iff`, `Int.exists_sq_add_sq_add_one_eq_mul` |
| Theorem 87 | 107 | for odd p there are x,y with 1+x^2+y^2 = mp, 0<m<p | `Int.exists_sq_add_sq_add_one_eq_mul` | in Mathlib |  |
| Theorem 88 | 108 | order of a mod m divides phi(m); a^x = 1 mod m iff order divides x | `orderOf_dvd_iff_pow_eq_one`, `ZMod.pow_totient`, `ZMod.orderOf_units_dvd_card_sub_one` | in Mathlib |  |
| Theorem 89 | 109 | there are infinitely many pseudoprimes to every base a>1 | `Nat.exists_infinite_pseudoprimes`, `Nat.frequently_atTop_fermatPsp`, `Nat.infinite_setOfPred_pseudoprimes` | in Mathlib |  |
| Theorem 90 | 109 | Lucas converse: a^(m-1)=1 and a^x != 1 for proper divisors x of m-1 imply m prime | `lucas_primality`, `lucas_primality_iff` | in Mathlib |  |
| Theorem 91 | 110 | 2^(p-1) = 1 mod p^2 for p = 1093 (also 3511) | `NTKB.HardyWright.exists_prime_two_pow_modEq_one_sq`, `NTKB.HardyWright.two_pow_1092_modEq_one`, `NTKB.HardyWright.two_pow_3510_modEq_one` | proved |  |
| Theorem 92 | 112 | Gauss's lemma: (m/p) = (-1)^mu, mu = number of multiples m..((p-1)/2)m with residue above p/2 | `ZMod.gauss_lemma` | in Mathlib |  |
| Theorem 93 | 113 | (2/p) = (-1)^[(p+1)/4] | `legendreSym.at_two` | in Mathlib |  |
| Theorem 94 | 113 | (2/p) = (-1)^[(p^2-1)/8] | `legendreSym.at_two` | in Mathlib |  |
| Theorem 95 | 113 | 2 is a residue of primes 8n+-1, a non-residue of primes 8n+-3 | `ZMod.exists_sq_eq_two_iff` | in Mathlib |  |
| Theorem 96 | 114 | -3 is a residue of primes 6n+1 and a non-residue of 6n+5 | `NTKB.HardyWright.isSquare_neg_three_iff`, `NTKB.HardyWright.isSquare_neg_three_of_mod_six` | proved |  |
| Theorem 97 | 114 | the OCR text says 7, but the proof at Section 6.13 treats 5: 5 is a residue of primes 10n+-1, a non-residue of 10n+-3 | `NTKB.HardyWright.isSquare_five_iff` | proved |  |
| Theorem 98 | 114 | quadratic reciprocity (p/q)(q/p) = (-1)^(p'q') | `legendreSym.quadratic_reciprocity`, `legendreSym.quadratic_reciprocity'` | in Mathlib |  |
| Theorem 99 | 114 | (p/q) = (q/p) unless both are 3 mod 4, then opposite sign | `legendreSym.quadratic_reciprocity_one_mod_four`, `legendreSym.quadratic_reciprocity_three_mod_four` | in Mathlib |  |
| Theorem 100 | 115 | S(q,p)+S(p,q) = p'q' (lattice-point count of floor sums) | `ZMod.sum_mul_div_add_sum_mul_div_eq_mul` | in Mathlib |  |
| Theorem 101 | 117 | primality test for n = hp+1 or hp^2+1 with h<p, 2^h != 1, 2^(n-1) = 1 mod n | `NTKB.HardyWright.prime_of_two_pow_modEq_one` | proved |  |
| Theorem 102 | 118 | Proth-type test: n = h 2^m+1, p a non-residue mod n, n prime iff p^((n-1)/2) = -1 mod n | `NTKB.HardyWright.prime_iff_pow_half_eq_neg_one` | proved |  |
| Section 6.14 (test for Fermat numbers F_k) | 119 | F_k is prime iff F_k divides 3^((F_k-1)/2)+1 | `NTKB.HardyWright.fermatNumber_prime_iff` | proved | Mathlib: `Nat.pepin_primality'` |
| Theorem 103 | 119 | Euler: for p = 4k+3 prime, 2p+1 is prime iff 2^p = 1 mod 2p+1, and then it divides M_p | `NTKB.HardyWright.prime_two_mul_add_one_iff`, `NTKB.HardyWright.dvd_mersenne_and_not_prime` | proved |  |
| Section 6.7 notes (least non-residue bound) | 120 | the least positive quadratic non-residue q satisfies q^2 < p+q; Burgess quoted | `NTKB.HardyWright.sq_lt_add_of_least_nonresidue` | proved |  |
| Section 6.9 notes (Korselt criterion) | 121 | n is Carmichael iff squarefree and p-1 divides n-1 for every prime p dividing n | `Nat.isCarmichael_iff_korselt` | in Mathlib |  |
| Section 6.9 notes (infinitely many Carmichael numbers) | 121 | Alford-Granville-Pomerance: infinitely many Carmichael numbers | — | not formalized |  |
| Section 6.14 notes (AKS) | 121 | polynomial time primality test of Agrawal, Kayal, Saxena | — | not formalized |  |

## Chapter VII. General properties of congruences

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Theorem 104 | 123 | (i) if fg = 0 mod p identically then f = 0 or g = 0 mod p; (ii) if fg = 0 mod p^a and f not 0 mod p then g = 0 mod p^a | `NTKB.HardyWright.C_dvd_or_C_dvd_of_C_dvd_mul`, `NTKB.HardyWright.C_pow_dvd_of_C_pow_dvd_mul` | proved | Mathlib: `mul_eq_zero` |
| Theorem 105 | 124 | (x-a) divides f(x) mod m if and only if f(a) = 0 mod m | `Polynomial.dvd_iff_isRoot` | in Mathlib |  |
| Theorem 106 | 125 | If f = gh mod p, every root of f mod p is a root of g or of h | `Polynomial.eval_mul`, `Polynomial.dvd_iff_isRoot` | in Mathlib |  |
| Theorem 107 | 126 | A polynomial of degree n with more than n roots mod p is identically 0 mod p (Lagrange) | `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero`, `Polynomial.card_roots'` | in Mathlib |  |
| Theorem 108 | 126 | A polynomial of degree n with n roots a_i mod p equals c0 prod(x - a_i) mod p | `Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C` | in Mathlib |  |
| Theorem 109 | 127 | If d divides p-1 then x^d = 1 mod p has exactly d roots | `NTKB.HardyWright.card_pow_eq_one_of_dvd` | proved | Mathlib: `IsCyclic.card_pow_eq_one_le`, Mathlib: `ZMod.isCyclic_units_prime` |
| Theorem 110 | 127 | Exactly phi(d) of the roots of x^d = 1 mod p have order d; so phi(p-1) primitive roots | `IsCyclic.card_orderOf_eq_totient`, `ZMod.isCyclic_units_prime`, `ZMod.card_units` | in Mathlib |  |
| Theorem 111 | 128 | For odd prime p there is g with 1, g, ..., g^(p-2) incongruent mod p (primitive root exists) | `ZMod.isCyclic_units_prime` | in Mathlib |  |
| Theorem 112 | 128 | x^(p-1) - 1 = (x-1)(x-2)...(x-p+1) mod p (Lagrange) | `Lagrange.nodal_subgroup_eq_X_pow_card_sub_one`, `NTKB.HardyWright.prod_X_sub_C_Icc_eq` | in Mathlib |  |
| Theorem 113 | 128 | For odd p and 1<=l<=p-2 the l-th elementary symmetric sum of 1..p-1 is 0 mod p | `NTKB.HardyWright.prime_dvd_coeff_lagrangePoly`, `NTKB.HardyWright.prime_dvd_esymm` | proved |  |
| Section 7.7 (case p=4n+1 of ((p-1)/2)!) | 130 | For p = 1 mod 4, ((p-1)/2)!^2 = -1 mod p | `ZMod.half_factorial_sq_eq_neg_one` | in Mathlib |  |
| Theorem 114 | 131 | For prime p = 4n+3, ((p-1)/2)! = (-1)^v mod p where v counts non-residues below p/2 | `NTKB.HardyWright.half_factorial_eq_neg_one_pow` | proved | Mathlib: `ZMod.factorial_eq_neg_one_pow_mul_half_factorial_sq` |
| Theorem 115 | 131 | Wolstenholme: for p>3 numerator of 1+1/2+...+1/(p-1) is divisible by p^2 | `NTKB.HardyWright.prime_sq_dvd_num_harmonic` | proved |  |
| Section 7.8 (formula 7.8.2) | 132 | Sum of 1/i over i<p is 0 mod p | `NTKB.HardyWright.sum_inv_eq_zero_mod_prime` | proved |  |
| Theorem 116 | 132 | Wolstenholme in associates form: sum of inverses mod p^2 of 1..p-1 is 0 mod p^2 | `NTKB.HardyWright.sum_inv_eq_zero_mod_prime_sq` | proved |  |
| Theorem 117 | 133 | For p>3 the numerator of sum of 1/i^2 (i<p) is divisible by p | `NTKB.HardyWright.prime_dvd_num_sum_inv_sq` | proved |  |
| Section 7.9 (Faulhaber formula 7.9.1) | 134 | 1^k+...+(n-1)^k = sum over r of Bernoulli terms times n^(k+1-r) | `sum_range_pow` | in Mathlib |  |
| Theorem 118 | 134 | von Staudt-Clausen: (-1)^k B_k is congruent mod 1 to the sum of 1/p over primes p with p-1 dividing 2k | `Bernoulli.vonStaudt_clausen` | in Mathlib |  |
| Theorem 119 | 135 | Sum of m^k over m=1..p-1 is -E_k(p) mod p | `FiniteField.sum_pow_units` | in Mathlib |  |
| Theorem 120 | 137 | If k is a prime of the form 3n+1 then B_k = 1/6 mod 1 (Rado) | `NTKB.HardyWright.bernoulli_eq_one_sixth_add_int` | proved |  |

## Chapter VIII. Congruences to composite moduli

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Theorem 121 | 140 | Chinese remainder: x = c_i mod m_i with m_i pairwise coprime has a unique solution mod product, given by formula | `Nat.chineseRemainderOfList`, `Nat.chineseRemainderOfFinset`, `Nat.chineseRemainder`, `ZMod.chineseRemainder` | in Mathlib |  |
| Theorem 122 | 142 | Number of roots of f mod m is the product of numbers of roots mod the pairwise coprime factors | `NTKB.HardyWright.rootCount_mul`, `NTKB.HardyWright.rootCount_prod` | proved |  |
| Theorem 123 | 143 | Number of lifts of a root xi mod p^(a-1): none, one, or p according to f'(xi) and f(xi) mod p^a (Hensel counting) | `NTKB.HardyWright.numLifts_eq_one`, `NTKB.HardyWright.numLifts_of_dvd_derivative`, `NTKB.HardyWright.rootCount_prime_pow` | proved | Mathlib: `hensels_lemma` |
| Theorem 124 | 144 | x^(p-1) = 1 mod p^a has exactly p-1 roots for every a | `NTKB.HardyWright.rootCount_X_pow_pred_sub_one` | proved |  |
| Theorem 125 | 145 | There are p(p-1)/2 quadratic residues mod p^2, the roots of x^(p(p-1)/2) = 1 mod p^2 | `NTKB.HardyWright.quadratic_residues_prime_sq`, `NTKB.HardyWright.rootCount_pow_half_totient`, `NTKB.HardyWright.card_quadratic_residues_prime_sq` | proved | Tau Ceti: `TauCeti.ZMod.natCard_sqrts_prime_pow_eq_legendreSym_add_one` |
| Section 8.4 (x^2 = c mod p^a) | 145 | For odd p not dividing c, x^2=c mod p^a has two roots or none according to c residue or not | `TauCeti.ZMod.natCard_sqrts_prime_pow_eq_legendreSym_add_one` | in Tau Ceti only (not a dependency) |  |
| Theorem 126 | 146 | Bauer: for odd prime p^a exactly dividing m, prod over t of (x-t) = (x^(p-1)-1)^(phi(m)/(p-1)) mod p^a | `NTKB.HardyWright.bauerPoly_prime_pow`, `NTKB.HardyWright.bauerPoly_map_prime_pow` | proved |  |
| Theorem 127 | 146 | Bauer, p=2: for even m>2, f_m(x) = (x^2-1)^(phi(m)/2) mod 2^a | `NTKB.HardyWright.bauerPoly_two_pow`, `NTKB.HardyWright.bauerPoly_map_two_pow` | proved |  |
| Theorem 128 | 149 | Leudesdorf: sum of inverses of units mod m is 0 mod m^2 with exceptional factors for 2 and 3 dividing m | `NTKB.HardyWright.sq_dvd_num_sum_inv_coprime`, `NTKB.HardyWright.sq_div_three_dvd_num_sum_inv`, `NTKB.HardyWright.sq_div_two_dvd_num_sum_inv`, `NTKB.HardyWright.sq_div_six_dvd_num_sum_inv`, `NTKB.HardyWright.sq_div_four_dvd_num_sum_inv` | proved |  |
| Theorem 129 | 151 | Product of units mod m is -1 if m is 4, p^a or 2p^a (p odd), else +1 (Gauss generalized Wilson) | `NTKB.HardyWright.prod_coprime_eq_ite` | proved | Mathlib: `ZMod.wilsons_lemma`, Mathlib: `FiniteField.prod_univ_units_id_eq_neg_one` |
| Theorem 130 | 152 | If A_(2v+1) is a homogeneous product sum of units mod p^a and p-1 does not divide 2v then it is 0 mod p^(2a) | `NTKB.HardyWright.prime_pow_two_mul_dvd_residueEsymm` | proved |  |
| Theorem 131 | 153 | For 2v<p-3 the numerator of sum of 1/k^(2v+1) (k<p) is divisible by p^2 | `NTKB.HardyWright.prime_sq_dvd_num_sum_inv_pow` | proved |  |
| Theorem 132 | 154 | Eisenstein: the Fermat quotient (2^(p-1)-1)/p is congruent mod p to a sum of reciprocals of the odd numbers 1,3,...,p-2 (formula 8.9.1, OCR garbled) | `NTKB.HardyWright.fermatQuotient_two_eq` | proved |  |
| Theorem 133 | 155 | (p-1)! = (-1)^((p-1)/2) 2^(p-2) times square of binomial-type expression mod p^2 | `NTKB.HardyWright.factorial_eq_mod_prime_sq` | proved |  |

## Chapter IX. The representation of numbers by decimals

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Section 9.1 (terminating decimals) | 159 | The decimal of x terminates iff x is a fraction with denominator 2^a 5^b; a decimal can never end in all 9s | — | not formalized |  |
| Theorem 134 | 160 | Every positive number has a decimal expansion (not ending in all 9s) and the correspondence numbers <-> such decimals is one-to-one | `Real.ofDigits_digits`, `Nat.ofDigits_digits`, `Nat.digits_inj_iff`, `Real.ofDigits_const_last_eq_one'` | partly in other libraries; not proved here |  |
| Theorem 135 | 162 | A rational in (0,1) has a terminating or recurring decimal and conversely; with q = 2^a 5^b Q the decimal has max(a,b) non-recurring digits and a period equal to the order of 10 mod Q | — | not formalized |  |
| Theorem 136 | 163 | Same as Theorem 134 in any scale r that is squarefree; termination, period and non-recurring digit counts given by order of r mod Q | `Real.ofDigits_digits`, `Real.ofDigits_SurjOn` | partly in other libraries; not proved here |  |
| Section 9.4 (non-terminating non-recurring decimals are irrational) | 164 | A decimal that neither terminates nor recurs represents an irrational; e.g. 0.0100100010... | — | not formalized |  |
| Theorem 137 | 164 | The decimal with digit 1 at prime places and 0 elsewhere is irrational | — | not formalized |  |
| Theorem 138 | 164 | The decimal 0.2357111317... formed by concatenating the primes is irrational | — | not formalized |  |
| Section 9.5 (tests for divisibility by 2^v, 5^v, 3, 9, 11) | 165 | Divisibility by 2^v or 5^v depends on the last v digits; by 9 or 3 on the digit sum; by 11 on the alternating digit sum | `Nat.nine_dvd_iff`, `Nat.three_dvd_iff`, `Nat.eleven_dvd_iff`, `Nat.modEq_nine_digits_sum`, `Nat.modEq_eleven_digits_sum` | partly in other libraries; not proved here |  |
| Section 9.5 (test for 7, 11, 13 using 1001) | 166 | Since 7.11.13 = 1001, a number is divisible by 7, 11 or 13 iff the alternating sum of its 3-digit blocks is | — | not formalized |  |
| Theorem 139 | 167 | If q is prime and 10 is a primitive root of q then the decimals for p/q, p = 1..q-1, have period q-1 and differ by cyclic permutation | — | not formalized |  |
| Theorem 140 | 168 | Weights 1, 2, 4, ..., 2^(n-1) weigh every integer up to 2^n - 1 (one pan) and no other set of n weights does as well; every such integer has a unique binary expansion | `Nat.ofDigits_digits`, `Nat.digits_lt_base`, `Nat.digits_inj_iff` | partly in other libraries; not proved here |  |
| Theorem 141 | 168 | Weights 1, 3, 9, ..., 3^(n-1) in either pan weigh every integer up to (3^n - 1)/2 and no other set of n weights does as well (balanced ternary) | `Nat.ofDigits_digits`, `Nat.digits_lt_base` | partly in other libraries; not proved here |  |
| Theorem 142 | 171 | A Nim position is a winning position iff it is correct (bitwise XOR of heap sizes is 0) | — | not formalized |  |
| Theorem 143 | 173 | Almost all integers contain any given digit or digit string (density of integers missing a digit tends to 0) | — | not formalized |  |
| Theorem 144 | 173 | The sum of the reciprocals of the integers that miss a given digit converges (Kempner-type) | — | not formalized |  |
| Section 9.10 (countable sets are null, countable unions of null sets are null) | 175 | Any enumerable set (such as the rationals in [0,1]) has measure zero and an enumerable union of null sets is null | `Set.Countable.measure_zero`, `MeasureTheory.measure_iUnion_null_iff` | in Mathlib |  |
| Theorem 145 | 176 | The set of reals in [0,1) whose decimal in a scale r misses a given digit is null; almost all decimals contain every digit | — | not formalized |  |
| Theorem 146 | 177 | Almost all decimals in any scale contain every finite digit sequence | — | not formalized |  |
| Theorem 147 | 177 | Cantor's ternary set is perfect and of measure zero | `isClosed_cantorSet`, `isCompact_cantorSet`, `cantorSet_eq_zero_two_ofDigits` | partly in other libraries; not proved here |  |
| Theorem 148 | 179 | Almost all numbers are normal in every scale (Borel) | — | not formalized |  |
| Section 9.13 (Champernowne number is normal) | 182 | The number 0.123456789101112... formed by writing all integers in order is normal | — | not formalized |  |
| Notes 9.12-13 (Niven-Zuckerman converse, Copeland-Erdos) | 183 | (9.12.2) for every digit string implies normal; and if a_n < n^(1+eps) increasing then concatenating the a_n gives a normal number | — | not formalized |  |

## Chapter X. Continued fractions

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Section 10.1 (nesting identities 10.1.2-10.1.5) | 185 | [a0..an] = [a0..a(n-1), a(n-1)+1/an] = a0 + 1/[a1..an], and [a0..an] = [a0..a(m-1),[am..an]] | `GenContFract.succ_nth_conv'_eq_squashGCF_nth_conv'`, `GenContFract.convs_eq_convs'` | partly in other libraries; not proved here |  |
| Theorem 149 | 185 | p_n = a_n p_(n-1) + p_(n-2), q_n likewise, and p_n/q_n equals the n-th convergent [a0..an] | `GenContFract.nums_recurrence`, `GenContFract.dens_recurrence`, `GenContFract.conv_eq_num_div_den`, `ContFract.convs_eq_convs'` | in Mathlib |  |
| Theorem 150 | 186 | p_n q_(n-1) - p_(n-1) q_n = (-1)^(n-1) | `SimpContFract.determinant`, `GenContFract.determinant`, `NTKB.HardyWright.cf_nums_mul_dens_sub` | in Mathlib |  |
| Theorem 151 | 187 | p_n q_(n-2) - p_(n-2) q_n = (-1)^n a_n | `NTKB.HardyWright.cf_nums_mul_dens_sub_two` | proved |  |
| Theorem 152 | 187 | Even convergents increase strictly, odd convergents decrease strictly | `NTKB.HardyWright.cf_convs_even_lt`, `NTKB.HardyWright.cf_convs_odd_lt` | proved |  |
| Theorem 153 | 187 | Every odd convergent exceeds every even convergent | `NTKB.HardyWright.cf_convs_even_lt_odd` | proved |  |
| Theorem 154 | 188 | The value of a continued fraction exceeds its even convergents and is below its odd convergents | `NTKB.HardyWright.cf_convs_even_lt_value_lt_odd` | proved | Mathlib: `GenContFract.sub_convs_eq` |
| Theorem 155 | 188 | q_n >= q_(n-1) for n >= 1 | `NTKB.HardyWright.cf_dens_le_dens_succ` | proved | Mathlib: `GenContFract.of_den_mono`, Tau Ceti: `Real.monotone_den_convergent` |
| Theorem 156 | 188 | q_n >= n, strictly for n > 3 | `NTKB.HardyWright.cf_le_dens` | proved | Mathlib: `GenContFract.succ_nth_fib_le_of_nth_den`, Tau Ceti: `Real.fib_succ_le_den_convergent` |
| Theorem 157 | 188 | Convergents of a simple continued fraction are in lowest terms | `NTKB.HardyWright.cf_isCoprime_nums_dens` | proved | Tau Ceti: `Real.den_convergent`, Tau Ceti: `Real.num_convergent` |
| Theorem 158 | 189 | A number with a simple continued fraction of odd (even) number of convergents has one with even (odd) number (last quotient 1 trick) | `NTKB.HardyWright.cf_exists_other_parity` | proved |  |
| Section 10.5 (complete quotients and formula 10.5.1) | 189 | x = (alpha_n p_(n-1) + p_(n-2))/(alpha_n q_(n-1) + q_(n-2)) with alpha_n the n-th complete quotient | `NTKB.HardyWright.cf_value_eq_completeQuotient`, `NTKB.NZM.finite_cf_value` | proved | Mathlib: `GenContFract.compExactValue_correctness_of_stream_eq_some` |
| Theorem 159 | 190 | The n-th complete quotient has integer part a_n, except a_(N-1) = [alpha_(N-1)] - 1 when a_N = 1 | `NTKB.HardyWright.cf_floor_completeQuotient` | proved |  |
| Theorem 160 | 190 | Two finite simple continued fractions with equal value and last quotient > 1 are identical | `NTKB.HardyWright.cf_eq_of_value_eq` | proved |  |
| Section 10.6 (continued fraction algorithm and Euclid's algorithm) | 191 | The continued fraction algorithm on h/k is exactly Euclid's algorithm; the last quotient a_N >= 2 | `GenContFract.of` | partly in other libraries; not proved here |  |
| Theorem 161 | 192 | Every rational number has a finite simple continued fraction | `GenContFract.terminates_of_rat`, `GenContFract.of_correctness_of_terminates`, `GenContFract.of_isSimpContFract`, `GenContFract.terminates_iff_rat`, `NTKB.HardyWright.exists_cf_eq_rat` | in Mathlib |  |
| Theorem 162 | 193 | A rational has exactly two finite simple expansions, one with even and one with odd number of convergents | `NTKB.HardyWright.cf_rat_two_expansions` | proved |  |
| Theorem 163 | 194 | x - p_n/q_n = (-1)^n d_n/(q_n q'_(n+1)) for the finite continued fraction | `GenContFract.sub_convs_eq` | partly in other libraries; not proved here |  |
| Theorem 164 | 195 | Differences x - p_n/q_n and q_n x - p_n decrease in absolute value with sign (-1)^n and bounds 1/q_(n+1) < \\|q_n x - p_n\\|, \\|x - p_n/q_n\\| < 1/(q_n q_(n+1)) | `GenContFract.abs_sub_convs_le`, `Real.abs_sub_convergent_le`, `Real.one_div_lt_abs_sub_convergent` | partly in other libraries; not proved here |  |
| Theorem 165 | 196 | For integers a_n with a_n > 0 (n >= 1) the convergents x_n tend to a limit | `NTKB.HardyWright.cf_convs_tendsto` | proved | Mathlib: `GenContFract.of_convergence` |
| Theorem 166 | 196 | All infinite simple continued fractions converge | `NTKB.HardyWright.cf_convergent` | proved | Mathlib: `GenContFract.of_convergence` |
| Theorem 167 | 197 | An infinite simple continued fraction lies below its odd convergents and above its even ones | `NTKB.HardyWright.cf_even_lt_value_lt_odd` | proved | Mathlib: `GenContFract.sub_convs_eq` |
| Theorem 168 | 197 | If [a0,a1,...] = x then a0 = [x] and a_n = [alpha_n] | `NTKB.HardyWright.cf_floor_value_eq` | proved | Mathlib: `GenContFract.of_h_eq_floor`, Mathlib: `GenContFract.convs_succ` |
| Theorem 169 | 197 | Two infinite simple continued fractions with the same value are identical | `NTKB.HardyWright.cf_eq_of_tendsto` | proved |  |
| Theorem 170 | 198 | Every irrational has exactly one infinite simple continued fraction; the value of an infinite simple fraction is irrational | `NTKB.HardyWright.irrational_iff_exists_unique_cf` | proved | Mathlib: `GenContFract.of_convergence`, Mathlib: `GenContFract.terminates_iff_rat`, Mathlib: `GenContFract.of_isSimpContFract`, Tau Ceti: `Irrational.not_of_terminatedAt` |
| Theorem 171 | 199 | The results of Theorems 163-164 hold for infinite fractions, in particular 1/(q_n(q_(n+1)+q_n)) < \\|x - p_n/q_n\\| < 1/(q_n q_(n+1)) | `NTKB.HardyWright.cf_abs_sub_convs_bounds`, `NTKB.HardyWright.cf_sub_convs_eq`, `NTKB.HardyWright.cf_value_eq_completeQuotient` | proved | Mathlib: `GenContFract.abs_sub_convs_le`, Tau Ceti: `Real.one_div_lt_abs_sub_convergent`, Tau Ceti: `Real.abs_sub_convergent_le` |
| Theorem 172 | 199 | If x = (P z + R)/(Q z + S) with z > 1, Q > S > 0, PS - QR = +-1, then R/S and P/Q are consecutive convergents and z is the (n+1)-th complete quotient | `NTKB.HardyWright.exists_cf_of_eq_moebius`, `NTKB.HardyWright.exists_cf_of_eq_moebius_infinite` | proved |  |
| Theorem 173 | 200 | Equivalence of numbers is transitive | `NTKB.HardyWright.IsEquivalent.trans`, `NTKB.HardyWright.IsEquivalent.symm`, `NTKB.HardyWright.IsEquivalent.refl` | proved |  |
| Theorem 174 | 201 | Any two rational numbers are equivalent | `NTKB.HardyWright.isEquivalent_rat` | proved |  |
| Theorem 175 | 201 | Two irrationals are equivalent iff their continued fractions have the same tail | `NTKB.HardyWright.isEquivalent_iff_tail_eq` | proved |  |
| Theorem 176 | 203 | A periodic continued fraction is a quadratic surd | `NTKB.HardyWright.quadratic_of_isPeriodic` | proved |  |
| Theorem 177 | 204 | The continued fraction of a quadratic surd is periodic (Lagrange) | `NTKB.HardyWright.isPeriodic_of_quadratic` | proved |  |
| Section 10.13 (x = [b,a,b,a,...] satisfies x^2 - bx - c = 0) | 207 | For a \\| b, b = ac, the periodic fraction (10.13.5) is the root of x^2 - b x - c = 0 | `NTKB.HardyWright.cf_alternating_value` | proved |  |
| Theorem 178 | 207 | Closed form for the convergents of [b,a,b,a,...] via u_n = (x^n - y^n)/(x - y) with x, y the roots of x^2 - bx - c | `NTKB.HardyWright.cf_alternating_convs` | proved |  |
| Section 10.14 (Binet formula and Fibonacci/Lucas series) | 209 | u_n = (x^n - y^n)/sqrt5 with x,y = (1 +- sqrt5)/2 and v_n = x^n + y^n | `Real.coe_fib_eq` | partly in other libraries; not proved here |  |
| Theorem 179 | 209 | (u_n,u_(n+1)) = 1; u_n \\| u_(rn); (u_m,u_n) = u_(gcd(m,n)); u_m u_n \\| u_(mn) for coprime m,n; also parity and v_n statements | `Nat.fib_coprime_fib_succ`, `Nat.fib_gcd`, `Nat.fib_dvd` | partly in other libraries; not proved here |  |
| Section 10.14 (identities 10.14.5-10.14.9) | 210 | u_(-n) = (-1)^(n-1) u_n, 2u_(m+n) = u_m v_n + u_n v_m, v_n^2 - 5u_n^2 = 4(-1)^n, Cassini-type identities | `Int.fib_succ_mul_fib_pred_sub_fib_sq`, `Int.fib_add` | partly in other libraries; not proved here |  |
| Theorem 180 | 211 | Every prime p divides some Fibonacci number; u_(p-1) = 0 mod p if p = +-1 mod 5, u_(p+1) = 0 mod p if p = +-2 mod 5 | `NTKB.HardyWright.prime_dvd_fib` | proved |  |
| Theorem 181 | 213 | If n > 1, 0 < q < q_n, p/q != p_n/q_n then the error of p_n/q_n is strictly smaller than the error of p/q (distance to x) | `NTKB.HardyWright.abs_convs_sub_lt` | proved in part |  |
| Theorem 182 | 213 | If n > 1, 0 < q < q_n, p/q != p_n/q_n then \\|p_n - q_n x\\| < \\|p - q x\\| (convergents are best approximations of the second kind) | `NTKB.HardyWright.abs_nums_sub_lt` | proved in part |  |
| Theorem 183 | 215 | Of two consecutive convergents at least one satisfies \\|p/q - x\\| < 1/(2q^2) (Vahlen) | `NTKB.HardyWright.abs_convs_sub_lt_or` | proved in part |  |
| Theorem 184 | 215 | If \\|p/q - x\\| < 1/(2q^2) then p/q is a convergent of x (Legendre) | `Real.exists_rat_eq_convergent`, `Real.exists_convs_eq_rat` | in Mathlib |  |

## Chapter XI. Approximation of irrationals by rationals

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Theorem 185 | 218 | Irrational xi has infinitely many p/q with \\|xi-p/q\\|<1/q^2 | `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational` | in Mathlib |  |
| Section 11.3 (Dirichlet's argument) | 220 | For real xi and n>=1 there are integers 0<k<=n, j with \\|k xi - j\\|<=1/(n+1) | `Real.exists_int_int_abs_mul_sub_le` | in Mathlib |  |
| Theorem 186 | 222 | A rational is approximable to order 1 and no higher | `TauCeti.irrationalityExponent_ratCast` | in Tau Ceti only (not a dependency) |  |
| Theorem 187 | 222 | Every irrational is approximable to order 2 | `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational`, `Irrational.liouvilleWith_two` | in Mathlib |  |
| Theorem 188 | 222 | A quadratic irrational is approximable to order 2 and no higher | `IsAlgebraic.irrationalityExponent_eq_two` | in Tau Ceti only (not a dependency) |  |
| Section 11.5 (Euclidean numbers are algebraic) | 223 | Every ruler-and-compass constructible length is algebraic (stated without proof, via real quadratic type) | `NTKB.HardyWright.IsRealQuadraticType.isAlgebraic`, `NTKB.HardyWright.sqrt_example` | proved |  |
| Theorem 189 | 224 | The set of algebraic numbers is countable (so real algebraic numbers have measure zero) | `Algebraic.countable` | in Mathlib |  |
| Theorem 190 | 224 | Almost all real numbers are transcendental | `Algebraic.countable` | partly in other libraries; not proved here |  |
| Theorem 191 | 225 | A real algebraic number of degree n is not approximable to any order greater than n (Liouville) | `Liouville.exists_pos_real_of_irrational_root` | in Mathlib |  |
| Theorem 192 | 227 | The numbers sum 10^(-n!) (two displayed variants) are transcendental | `transcendental_liouvilleNumber`, `liouville_liouvilleNumber`, `Liouville.transcendental` | partly in other libraries; not proved here |  |
| Theorem 193 | 228 | Every irrational has infinitely many p/q with \\|xi-p/q\\|<1/(sqrt5 q^2) (Hurwitz) | `Real.infinite_rat_abs_sub_lt_one_div_sqrt_five_mul_den_sq_of_irrational` | in Mathlib |  |
| Theorem 194 | 229 | The constant sqrt5 in Theorem 193 is best possible (golden ratio) | `NTKB.HardyWright.finite_abs_sub_lt_of_sqrt_five_lt` | proved |  |
| Theorem 195 | 229 | Of any three consecutive convergents to xi at least one satisfies \\|xi-p/q\\|<1/(sqrt5 q^2) | `NTKB.HardyWright.abs_convs_sub_lt_sqrt_five` | proved |  |
| Theorem 196 | 231 | Partial quotients a_n are unbounded for almost all xi (bounded-quotient set is null) | `NTKB.HardyWright.volume_bdd_quotients_eq_zero` | proved |  |
| Theorem 197* | 234 | Metric theorem on a_n < phi(n) for large n: null set if sum 1/phi(n) diverges, full measure if converges (Khinchin type) | `NTKB.HardyWright.volume_eventually_lt_eq_zero`, `NTKB.HardyWright.volume_frequently_ge_eq_zero` | proved |  |
| Theorem 198 | 235 | If sum 1/chi(q) converges then \\|xi-p/q\\|<1/(q chi(q)) holds for infinitely many q only on a null set | `NTKB.HardyWright.volume_infinite_approx_eq_zero` | proved | Mathlib: `ae_not_liouvilleWith` |
| Theorem 199* | 235 | If chi(q)/q increases and sum 1/chi(q) diverges, then \\|xi-p/q\\|<1/(q chi(q)) infinitely often for almost all xi (Khinchin) | — | not formalized |  |
| Theorem 200 | 236 | For any k reals the system \\|xi_i-p_i/q\\|<1/q^(1+1/k) has a solution; infinitely many if some xi_i irrational | `TauCeti.simultaneous_dirichlet` | partly in other libraries; not proved here |  |
| Theorem 201 | 237 | For any xi_1..xi_k and eps>0 there is a positive integer q with every q xi_i within eps of an integer | `NTKB.NZM.simultaneous_approximation_general` | proved | Tau Ceti: `TauCeti.simultaneous_dirichlet` |
| Theorem 202 | 238 | For polynomial phi, e^x phi(h)=Phi(x+h)+eps(x)e^\\|x\\| (identity for the transcendence proof) | `NTKB.HardyWright.exp_mul_hEval`, `NTKB.HardyWright.abs_epsR_lt_one` | proved |  |
| Theorem 203 | 239 | For integral polynomial f, F1(h) and F2(h) are integers with F1(h)=f(0), F2(h)=0 mod m (Hermite-type lemma) | `NTKB.HardyWright.hEval_integral` | proved |  |
| Theorem 204 | 240 | e is transcendental | `TauCeti.linearIndependent_exp` | in Tau Ceti only (not a dependency) |  |
| Theorem 205 | 242 | pi is transcendental | `TauCeti.linearIndependent_exp` | in Tau Ceti only (not a dependency) |  |

## Chapter XII. The fundamental theorem of arithmetic in k(1), k(i), and k(rho)

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Theorem 206 | 248 | A rational algebraic integer is a rational integer | `IsIntegrallyClosed.isIntegral_iff` | in Mathlib |  |
| Theorem 207 | 251 | The last nonzero remainder in Euclid's algorithm equals (a,b) | `EuclideanDomain.gcd_val` | in Mathlib |  |
| Theorem 208 | 251 | If f divides a and b then f divides (a,b) | `EuclideanDomain.dvd_gcd` | in Mathlib |  |
| Theorem 209 | 252 | If (a,b)=1 and b divides ac then b divides c | `IsCoprime.dvd_of_dvd_mul_right` | in Mathlib |  |
| Theorem 210 | 254 | The norm of a unity is 1, and an integer of norm 1 is a unity | `Zsqrtd.norm_eq_one_iff'` | in Mathlib |  |
| Theorem 211 | 255 | The unities of k(i) are i^s, s=0..3 (i.e. +-1, +-i) | `Zsqrtd.norm_eq_one_iff'` | partly in other libraries; not proved here |  |
| Theorem 212 | 255 | A Gaussian integer whose norm is a rational prime is prime | `NTKB.HardyWright.gauss_prime_of_natAbs_norm_prime` | proved | Mathlib: `Ideal.prime_of_irreducible_absNorm_span` |
| Theorem 213 | 256 | Every Gaussian integer not 0 or a unity is divisible by a prime | `WfDvdMonoid.exists_irreducible_factor` | in Mathlib |  |
| Theorem 214 | 257 | Every Gaussian integer not 0 or a unity is a product of primes | `UniqueFactorizationMonoid.exists_prime_factors` | in Mathlib |  |
| Theorem 215 | 257 | Fundamental theorem for Gaussian integers: factorization into primes is unique up to order, units, associates | `UniqueFactorizationMonoid.factors_unique` | in Mathlib |  |
| Theorem 216 | 257 | Division with remainder in k(i): y=kappa y1+y2 with N(y2)<N(y1) | `GaussianInt.norm_mod_lt` | in Mathlib |  |
| Theorem 217 | 260 | If (y,y1)=1 and y1 divides beta y then y1 divides beta (Gaussian analogue of Theorem 209) | `IsCoprime.dvd_of_dvd_mul_right` | in Mathlib |  |
| Theorem 218 | 260 | If a Gaussian prime pi divides beta gamma then pi divides beta or gamma | `Irreducible.prime` | in Mathlib |  |
| Section 12.9 (integers of k(rho), norm a^2-ab+b^2) | 260 | k(rho) integers a+b rho have norm a^2-ab+b^2, divisibility etc. as for k(i) | `IsPrimitiveRoot.norm_intCast_add_intCast_mul_toInteger_of_three` | partly in other libraries; not proved here |  |
| Theorem 219 | 262 | Division with remainder in k(rho): y=kappa y1+y2 with N(y2)<N(y1) | `NTKB.HardyWright.isNormEuclidean_iff_of_neg`, `NTKB.HardyWright.rho_round` | proved |  |
| Theorem 220 | 262 | Fundamental theorem for k(rho): unique factorization into primes up to order, units, associates | `IsCyclotomicExtension.Rat.three_pid` | in Mathlib |  |
| Theorem 221 | 262 | lambda = 1-rho is prime in k(rho) | `IsPrimitiveRoot.zeta_sub_one_prime'` | in Mathlib |  |
| Theorem 222 | 263 | Every integer of k(rho) is congruent to 0, 1 or -1 mod lambda (three classes) | `IsCyclotomicExtension.Rat.Three.lambda_dvd_or_dvd_sub_one_or_dvd_add_one` | in Mathlib |  |
| Theorem 223 | 263 | 3 is associated with lambda^2 | `IsPrimitiveRoot.toInteger_sub_one_sq_dvd_three` | partly in other libraries; not proved here |  |
| Theorem 224 | 263 | +-(1-rho), +-(1-rho^2), +-rho(1-rho) are all associated with lambda | — | not formalized |  |

## Chapter XIII. Some Diophantine equations

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Section 13.1 (Fermat's last theorem, general n) | 264 | x^n+y^n=z^n has no nontrivial integer solutions for n>2 (book notes: completed by Wiles and Taylor) | — | not formalized |  |
| Theorem 225 | 264 | general primitive Pythagorean triple (x even, gcd(x,y)=1, positive) is x=2ab, y=a^2-b^2, z=a^2+b^2 with a>b>0 coprime of opposite parity, bijectively | `PythagoreanTriple.coprime_classification'`, `PythagoreanTriple.coprime_classification` | in Mathlib |  |
| Theorem 226 | 266 | x^4+y^4=z^2 has no solution in positive integers (hence FLT for n=4), by descent | `not_fermat_42` | in Mathlib |  |
| Section 13.4 (reduction of FLT to n=4 and odd primes) | 267 | if FLT holds for n it holds for every multiple of n, so it suffices to treat n=4 and odd prime n | `FermatLastTheoremFor.mono`, `FermatLastTheorem.of_odd_primes` | in Mathlib |  |
| Theorem 227 | 268 | no solutions of xi^3+eta^3+zeta^3=0 in nonzero integers of k(rho) (Eisenstein integers); in particular FLT for n=3 | `NTKB.HardyWright.cube_add_cube_add_cube_ne_zero`, `NTKB.HardyWright.int_cube_add_cube_ne_cube` | proved | Mathlib: `FermatLastTheoremForThreeGen`, Mathlib: `FermatLastTheoremForThreeGen.exists_Solution_multiplicity_lt` |
| Theorem 228 | 268 | if lambda does not divide omega in k(rho) then omega^3 = +-1 (mod lambda^4) | `IsCyclotomicExtension.Rat.Three.lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd` | in Mathlib |  |
| Theorem 229 | 269 | if xi^3+eta^3+zeta^3=0 in k(rho) then lambda divides one of xi, eta, zeta | `NTKB.HardyWright.lambda_dvd_of_cube_add_cube_add_cube` | proved | Mathlib: `fermatLastTheoremThree_case_1` |
| Theorem 230 | 270 | in the descent equation xi^3+eta^3+eps lambda^(3n) gamma^3=0 one has n>=2 | `FermatLastTheoremForThreeGen.Solution'.two_le_multiplicity`, `FermatLastTheoremForThreeGen.a_cube_b_cube_congr_one_or_neg_one`, `NTKB.HardyWright.CubeDescent.not_sol_of_le_three` | in Mathlib |  |
| Theorem 231 | 270 | if the descent equation is solvable for n=m>1 then it is solvable for n=m-1 | `FermatLastTheoremForThreeGen.exists_Solution_multiplicity_lt`, `NTKB.HardyWright.CubeDescent.sol_descent`, `NTKB.HardyWright.CubeDescent.not_sol` | in Mathlib |  |
| Theorem 232 | 272 | x^3+y^3=3z^3 has only the trivial integer solutions z=0 | `NTKB.HardyWright.eq_zero_of_cube_add_cube_eq_three_mul_cube` | proved |  |
| Theorem 233 | 274 | some positive rationals (e.g. 3) are not sums of two non-negative rational cubes (corollary of Theorem 232) | `NTKB.HardyWright.exists_pos_not_sum_two_rat_cubes`, `NTKB.HardyWright.rat_cube_add_cube_ne_three` | proved |  |
| Theorem 234 | 274 | every positive rational is a sum of three positive rational cubes (Ryley/Richmond parametrization) | `NTKB.HardyWright.exists_three_pos_rat_cubes` | proved |  |
| Theorem 235 | 278 | general rational solution of x^3+y^3=u^3+v^3 is the Euler/Binet parametrization (13.7.8) in rational a,b,lambda, apart from trivial ones | `NTKB.HardyWright.cube_add_cube_eq_iff`, `NTKB.HardyWright.eulerBinet`, `NTKB.HardyWright.eulerBinet_examples` | proved |  |
| Section 13.7 (Ramanujan's solution of x^3+y^3+z^3=t^3) | 279 | explicit quadratic polynomial parametrization (13.7.1) of x^3+y^3+z^3=t^3 by Ramanujan, e.g. (17,14,7,20) | `NTKB.HardyWright.ramanujan_cubes`, `NTKB.HardyWright.cube_examples` | proved |  |
| Section 13.7 (13.7.10-13.7.11, x^4+y^4=u^4+v^4) | 279 | Euler/Gerardin parametric solution of x^4+y^4=u^4+v^4; smallest integral solution 133^4+134^4=158^4+59^4 | `NTKB.HardyWright.euler_fourth_powers`, `NTKB.HardyWright.euler_fourth_powers_example`, `NTKB.HardyWright.not_euler_fourth_powers_printed` | refuted as stated in the book; corrected form proved |  |
| Notes 13.1 (Kummer regular primes, Wieferich criterion, computations) | 280 | FLT holds for regular primes (Kummer); Wieferich: a counterexample to first case needs 2^(p-1)=1 mod p^2; checked up to 125000 and various bounds | — | not formalized |  |
| Notes 13.6 (Segre: a cubic with one rational point has infinitely many) | 281 | Segre: a non-degenerate cubic in three variables with a rational point has infinitely many | — | not formalized |  |
| Notes 13.7 (Catalan's conjecture, Mihailescu) | 282 | x^p-y^q=1 in integers >1 has only 3^2-2^3=1 | — | not formalized |  |
| Notes 13.7 (Faltings' theorem for homogeneous f of degree >=4) | 282 | a nonsingular ternary form of degree >=4 has finitely many projective integer solutions; consequence for generalized Fermat | — | not formalized |  |
| Notes 13.7 (abc conjecture) | 282 | for every eps>0 there is K(eps) with c < K(eps) rad(abc)^(1+eps) whenever a+b=c in positive integers | `TauCeti.AbcConjecture` | in Tau Ceti only (not a dependency) |  |
| Notes 13.7 (abc conjecture implies finiteness for generalized Fermat n>=4) | 282 | abc conjecture implies x^n+y^n=z^n has finitely many solutions in x,y,z,n with n>=4 | `NTKB.HardyWright.fermat_finite_of_abc` | proved, conditional |  |

## Chapter XIV. Quadratic fields (1)

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Section 14.1 (every member of k(sqrt m) is rational or quadratic, eq 14.1.2) | 284 | an element (a+b sqrt m)/c of a quadratic field satisfies c^2x^2-2acx+a^2-mb^2=0 | `QuadraticAlgebra.sq_sub_trace_smul_add_norm_eq_zero` | in Mathlib |  |
| Section 14.1 (the two definitions of integers of k(sqrt m) agree) | 284 | a number of a quadratic field is an algebraic integer iff it satisfies a monic degree-2 integer equation | `QuadraticAlgebra.isIntegral_iff` | in Mathlib |  |
| Theorem 236 | 284 | an algebraic number of degree n satisfies a unique primitive equation of degree n, whose leading coefficient is 1 if the number is an algebraic integer | `NTKB.HardyWright.existsUnique_primitive`, `NTKB.HardyWright.leadingCoeff_eq_one_of_isIntegral` | proved | Mathlib: `minpoly.isIntegrallyClosed_eq_field_fractions`, Mathlib: `minpoly.unique`, Mathlib: `Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast` |
| Theorem 237 | 285 | if f is the primitive equation of degree n of xi and g is any primitive equation satisfied by xi then g = f h with h primitive (Gauss lemma) | `NTKB.HardyWright.exists_primitive_mul` | proved | Mathlib: `minpoly.isIntegrallyClosed_dvd`, Mathlib: `Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast` |
| Theorem 238 | 286 | the integers of k(sqrt m) are a+b sqrt m if m=2,3 mod 4 and a+b(sqrt m -1)/2 if m=1 mod 4, with a,b in Z | `QuadraticAlgebra.Int.isIntegralClosure_iff`, `NumberField.adjoin_gen_eq_top_of_mod_four_ne_one`, `NumberField.adjoin_halfGen_eq_top_of_mod_four_eq_one`, `NTKB.HardyWright.exists_int_of_isIntegral`, `NTKB.HardyWright.exists_half_of_isIntegral`, `NTKB.HardyWright.isIntegral_mk_int`, `NTKB.HardyWright.isIntegral_mk_half` | in Mathlib |  |
| Theorem 239 | 287 | products and quotients of unities (units) are unities | `IsUnit.mul` | in Mathlib |  |
| Section 14.4 (norm of an element, N(xi eta)=N xi N eta) | 288 | norm N(xi)=xi*conj(xi)=r^2-ms^2; integer norm for integers; multiplicative | `Zsqrtd.norm_mul`, `QuadraticAlgebra.norm_def` | in Mathlib |  |
| Theorem 240 | 288 | the norm of a unity is +-1, and every integer of norm +-1 is a unity (finitely many unities for m<0: 4 in k(i), 6 in k(rho), else 2) | `NTKB.HardyWright.isUnity_iff_norm`, `NTKB.HardyWright.ncard_unities_of_neg` | proved | Mathlib: `QuadraticAlgebra.isUnit_iff_norm_isUnit`, Mathlib: `Zsqrtd.norm_eq_one_iff`, Tau Ceti: `TauCeti.NumberField.Units.card_units_of_isTotallyComplex` |
| Theorem 241 | 289 | an integer whose norm is a rational prime is prime | `Ideal.prime_of_irreducible_absNorm_span`, `NTKB.HardyWright.zsqrtd_irreducible_of_natAbs_norm_prime`, `NTKB.HardyWright.qa_irreducible_of_natAbs_norm_prime` | in Mathlib |  |
| Theorem 242 | 289 | every integer other than 0 or a unity is a product of primes (irreducibles); uniqueness open | `WfDvdMonoid.exists_factors`, `IsNoetherianRing.wfDvdMonoid` | in Mathlib |  |
| Theorem 243 | 289 | the unities of k(sqrt 2) are exactly +-w^n, n integer, w=1+sqrt 2 | `NTKB.HardyWright.sqrtTwo_units` | proved | Mathlib: `Pell.IsFundamental.eq_zpow_or_neg_zpow` |
| Theorem 244 | 290 | all integer solutions of x^2-2y^2=1 are x+y sqrt2 = +-(1+sqrt2)^(2n), and of x^2-2y^2=-1 are +-(1+sqrt2)^(2n+1) | `NTKB.HardyWright.sq_sub_two_mul_sq_eq_one_iff`, `NTKB.HardyWright.sq_sub_two_mul_sq_eq_neg_one_iff` | proved | Mathlib: `Pell.IsFundamental.eq_zpow_or_neg_zpow` |
| Section 14.5 (Pell equation solved via convergents of sqrt m) | 290 | x^2-my^2=1 always has infinitely many solutions, obtained from the continued fraction of sqrt m; for m=2 the convergents give all solutions | `NTKB.HardyWright.pell_period`, `NTKB.HardyWright.eq_convergent_of_pell` | proved | Mathlib: `Pell.exists_of_not_isSquare`, Mathlib: `Real.exists_rat_eq_convergent` |
| Section 14.6 (examples: unique factorization fails in k(sqrt -5), k(sqrt 10)) | 292 | 6=2*3=(1+sqrt-5)(1-sqrt-5) are two factorizations into primes in Z[sqrt -5]; also 6=2*3=(4+sqrt10)(4-sqrt10) in Z[sqrt 10] | `NTKB.HardyWright.sqrtNegFive_two_factorizations`, `NTKB.HardyWright.not_ufm_sqrtNegFive`, `NTKB.HardyWright.sqrtTen_two_factorizations`, `NTKB.HardyWright.not_ufm_sqrtTen` | proved | Tau Ceti: `TauCeti.NumberField.SqrtNegFive.not_uniqueFactorizationMonoid`, Tau Ceti: `TauCeti.NumberField.SqrtNegFive.two_mul_three_eq`, Tau Ceti: `TauCeti.NumberField.SqrtNegFive.irreducible_two` |
| Section 14.6 (Bezout fails in k(sqrt -5): 3x+(1+sqrt-5)y=1 unsolvable) | 293 | no integers lambda1, lambda2 with 3*lambda1+(1+sqrt-5)*lambda2=1 in Z[sqrt -5] | `NTKB.HardyWright.sqrtNegFive_no_bezout` | proved |  |
| Theorem 245 | 294 | the fundamental theorem of arithmetic (unique factorization) holds in any Euclidean quadratic field | `EuclideanDomain.instIsPrincipalIdealRing`, `PrincipalIdealRing.to_uniqueFactorizationMonoid`, `NTKB.HardyWright.euclideanDomainOfNorm` | in Mathlib |  |
| Theorem 246 | 294 | there are exactly five complex norm-Euclidean quadratic fields, m=-1,-2,-3,-7,-11 | `NTKB.HardyWright.isNormEuclidean_iff_of_neg` | proved | Mathlib: `GaussianInt.natAbs_norm_mod_lt`, Mathlib: `IsCyclotomicExtension.Rat.three_pid` |
| Section 14.7 (the nine simple complex quadratic fields m=-1,-2,-3,-7,-11,-19,-43,-67,-163) | 295 | the fields in which unique factorization holds are exactly these nine (Heilbronn finiteness; Heilbronn-Linfoot, Stark, Baker, Heegner in the notes) | `TauCeti.classNumber_eq_one_of_mem_heegnerNumbers` | partly in other libraries; not proved here |  |
| Theorem 247 | 295 | k(sqrt m), m>0, is norm-Euclidean exactly for m=2,3,5,6,7,11,13,17,19,21,29,33,37,41,57,73 | — | not formalized |  |
| Theorem 248 | 296 | k(sqrt m) is norm-Euclidean for m=2,3,5,6,7,13,17,21,29 (by a case analysis on (14.8.1)) | `NTKB.HardyWright.isNormEuclidean_of_mem` | proved |  |
| Section 14.8 (no algorithm for m=23) | 298 | k(sqrt 23) is not norm-Euclidean (take r=0, s=7/23), though it is simple | `NTKB.HardyWright.not_isNormEuclidean_23` | proved |  |
| Theorem 249 | 298 | only finitely many real norm-Euclidean fields k(sqrt m) with m=2 or 3 (mod 4) | `NTKB.HardyWright.finite_isNormEuclidean` | proved |  |
| Notes 14 (norm-Euclidean versus Euclidean; Samuel, Harper, Davenport, Biro) | 299 | notes: Euclidean by an arbitrary function; no further complex Euclidean fields (Samuel); k(sqrt 14) Euclidean but not norm-Euclidean (Harper); real norm-Euclidean bound m<=2^14 (Davenport); k(sqrt 97) not norm-Euclidean; Biro's m=4r^2+1 result | — | not formalized |  |

## Chapter XV. Quadratic fields (2)

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Theorem 250 | 302 | Every prime of a simple quadratic field k(sqrt m) divides exactly one rational prime. | `NTKB.HardyWright.existsUnique_nat_prime_dvd` | proved | Mathlib: `Ideal.IsPrime.under` |
| Theorem 251 | 303 | A rational prime 4n+1 is a sum of two squares a^2+b^2. | `Nat.Prime.sq_add_sq` | in Mathlib |  |
| Section 15.1 (uniqueness of the sum of two squares) | 303 | For p=4n+1 the representation p=a^2+b^2 is unique up to the eight sign and order variations (15.1.2, 15.1.3). | `NTKB.HardyWright.sq_add_sq_unique` | proved |  |
| Theorem 252 | 303 | The primes of Z[i] are 1+i with associates, rational primes 4n+3 with associates, and the factors a+bi of rational primes 4n+1. | `NTKB.HardyWright.gaussianInt_prime_iff` | proved | Mathlib: `GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime`, Mathlib: `GaussianInt.sq_add_sq_of_nat_prime_of_not_irreducible` |
| Theorem 253 | 304 | Fermat analogue in Z[i]: a^phi(pi) = 1 mod pi for a prime to the Gaussian prime pi, phi(pi)=N(pi)-1. | `NTKB.HardyWright.gaussianInt_fermat` | proved |  |
| Theorem 254 | 306 | A rational prime 3n+1 is of the form a^2-ab+b^2. | `NTKB.HardyWright.exists_sq_sub_mul_add_sq` | proved |  |
| Theorem 255 | 306 | The primes of Z[omega] are 1-omega with associates, rational primes 3n+2, and the factors a+b*omega of primes 3n+1. | `NTKB.HardyWright.rho_prime_iff` | proved |  |
| Theorem 256 | 306 | The primes of Z[sqrt 2] are sqrt 2, rational primes 8n+-3, and factors a+b*sqrt2 of primes 8n+-1. | `NTKB.HardyWright.sqrtTwo_prime_iff` | proved |  |
| Theorem 257 | 307 | Unities of the field k(sqrt 5) are +-w^n; primes are sqrt5, rational primes 5n+-2, factors a+b*w of primes 5n+-1. | `NTKB.HardyWright.gold_units`, `NTKB.HardyWright.gold_prime_iff` | proved |  |
| Theorem 258 | 307 | Fermat analogue in Z[(1+sqrt5)/2]: a^(N(pi)-1)=1 mod pi, a^(q+1)=Na mod q, a^(p-1)=1 mod p (15.4.4-15.4.7). | `NTKB.HardyWright.gold_fermat`, `NTKB.HardyWright.gold_fermat_p`, `NTKB.HardyWright.gold_fermat_q`, `NTKB.HardyWright.gold_fermat_p'` | proved |  |
| Section 15.4 (Fibonacci consequence) | 309 | From (15.4.4-15.4.6): u_(p-1) = 0 mod p for p=5n+-1 and u_(q+1) = 0 mod q for q=5n+-2 (another proof of Theorem 180). | `NTKB.HardyWright.prime_dvd_fib_of_gold` | proved |  |
| Theorem 259 | 310 | Lucas test with sequence 3,7,47,...(r_(m+1)=r_m^2-2): for p=4n+3, M_p is prime iff r_(p-1) = 0 mod M_p. | `NTKB.HardyWright.lucas_test`, `NTKB.HardyWright.lucasR` | proved | Mathlib: `lucas_lehmer_sufficiency`, Mathlib: `lucas_lehmer_necessity` |
| Section 15.5 (second Lucas test, sequence 4,14,194) | 311 | The sequence 4,14,194,... gives the analogous primality test for M_p for any odd p (proof not given in text). | `lucas_lehmer_sufficiency`, `lucas_lehmer_necessity` | in Mathlib |  |
| Section 15.6 (properties A, B, C: equivalences) | 312 | Properties A (gcd), B (gcd as linear combination), C (unique factorization): B implies A, B implies C, A implies C, C implies A. | `NTKB.HardyWright.properties_ABC` | proved |  |
| Section 15.7 (properties D and E) | 316 | D: every ideal of a simple field is principal; E: in a simple complex field every ideal is a lattice similar to the full lattice (fails in k(sqrt -5)). | `NTKB.HardyWright.isPrincipalIdealRing_of_simple`, `NTKB.HardyWright.sqrtNegFive_not_principal` | proved in part |  |
| Section 15.5 (notes: Newman generalization) | 320 | For odd h<2^p, M=h*2^p-1 prime and 2 mod 5 variant, a test R_(m-1)=0 mod M (statement partly garbled in OCR). | — | not formalized |  |

## Chapter XVI. The arithmetical functions phi(n), mu(n), d(n), sigma(n), r(n)

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Theorem 260 | 321 | Inclusion-exclusion: the number of objects with none of properties alpha, beta,... is N - sum N_alpha + sum N_alphabeta - .... | `Finset.inclusion_exclusion_card_inf_compl` | in Mathlib |  |
| Theorem 261 | 322 | The number of integers <= n not divisible by any of a coprime set a,b,... is n - sum floor(n/a) + sum floor(n/ab) - .... | `Finset.inclusion_exclusion_card_inf_compl` | partly in other libraries; not proved here |  |
| Section 16.2 (further proof of Theorem 63) | 322 | n equals the sum of phi(d) over d dividing n, by classifying fractions h/n by reduced form. | `Nat.sum_totient`, `NTKB.HardyWright.sum_Icc_div_eq_sum_divisors` | in Mathlib |  |
| Theorem 262 | 323 | mu(n) is multiplicative. | `ArithmeticFunction.isMultiplicative_moebius` | in Mathlib |  |
| Section 16.3 (phi(n) as a mu-sum, 16.3.1) | 323 | phi(n)=n sum mu(d)/d = sum d mu(n/d). | `NTKB.HardyWright.totient_eq_sum_antidiagonal` | proved | Mathlib: `ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub` |
| Theorem 263 | 323 | Sum of mu(d) over d dividing n is 1 for n=1 and 0 for n>1. | `ArithmeticFunction.moebius_mul_coe_zeta`, `ArithmeticFunction.coe_mul_zeta_apply` | in Mathlib |  |
| Theorem 264 | 323 | For n>1 with k distinct prime factors, sum of \\|mu(d)\\| over d dividing n is 2^k. | `NTKB.HardyWright.sum_divisors_abs_moebius` | proved |  |
| Theorem 265 | 324 | If f is multiplicative then g(n)=sum of f(d) over d dividing n is multiplicative. | `ArithmeticFunction.IsMultiplicative.mul`, `ArithmeticFunction.isMultiplicative_zeta`, `ArithmeticFunction.coe_mul_zeta_apply` | in Mathlib |  |
| Theorem 266 | 324 | Moebius inversion: g(n)=sum_(d\\|n) f(d) implies f(n)=sum_(d\\|n) mu(n/d) g(d). | `ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq`, `ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq` | in Mathlib |  |
| Theorem 267 | 325 | Converse of Moebius inversion: f(n)=sum mu(n/d) g(d) implies g(n)=sum_(d\\|n) f(d). | `ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq` | in Mathlib |  |
| Theorem 268 | 326 | If G(x)=sum_(n<=x) F(x/n) for all x>0 then F(x)=sum_(n<=x) mu(n) G(x/n). | `NTKB.HardyWright.moebius_inversion_floor`, `NTKB.HardyWright.not_moebius_inversion_floor_all_pos` | refuted as stated in the book; corrected form proved |  |
| Theorem 269 | 326 | Converse: F(x)=sum mu(n) G(x/n) implies G(x)=sum F(x/n). | `NTKB.HardyWright.moebius_inversion_floor_converse`, `NTKB.HardyWright.not_moebius_inversion_floor_converse_all_pos` | refuted as stated in the book; corrected form proved |  |
| Theorem 270 | 326 | g(x)=sum_m f(mx) iff f(x)=sum_n mu(n) g(nx) (under absolute convergence). | `NTKB.HardyWright.moebius_inversion_tsum`, `NTKB.HardyWright.moebius_inversion_tsum_converse`, `NTKB.HardyWright.moebius_inversion_tsum_iff` | proved |  |
| Theorem 271 | 327 | c_n(m) equals the sum over d dividing both m and n of d*mu(n/d). | `NTKB.HardyWright.ramanujanSum_eq_sum` | proved |  |
| Theorem 272 | 328 | If (n,m)=a, n=aN then c_n(m)=mu(N)phi(n)/phi(N). | `NTKB.HardyWright.ramanujanSum_eq_moebius_mul_totient_div` | proved |  |
| Section 16.6 (c_n(1)=mu(n), 16.6.4) | 329 | The sum of primitive nth roots of unity e(h/n) equals mu(n). | `NTKB.HardyWright.ramanujanSum_one` | proved |  |
| Theorem 273 | 329 | d(n) = product of (a_i + 1) for n = product of p_i^a_i. | `Nat.card_divisors` | in Mathlib |  |
| Theorem 274 | 330 | sigma_k(n) = product of (p_i^((a_i+1)k) - 1)/(p_i^k - 1). | `NTKB.HardyWright.sigma_eq_prod_div` | proved | Mathlib: `ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul` |
| Theorem 275 | 330 | sigma(n) = product of (p_i^(a_i+1) - 1)/(p_i - 1). | `NTKB.HardyWright.sigma_one_eq_prod_div` | proved | Mathlib: `Nat.sum_divisors` |
| Theorem 276 | 330 | If 2^(n+1)-1 is prime then 2^n(2^(n+1)-1) is perfect. | `NTKB.HardyWright.perfect_two_pow_mul_mersenne` | proved |  |
| Theorem 277 | 331 | Every even perfect number is 2^n(2^(n+1)-1) with 2^(n+1)-1 prime. | `NTKB.HardyWright.eq_two_pow_mul_mersenne_of_even_perfect` | proved |  |
| Section 16.9 (delta(n)=d1(n)-d3(n)) | 332 | delta(n)=sum of chi(d)=d_1(n)-d_3(n) with chi multiplicative on odd numbers (16.9.1-16.9.2). | `NTKB.HardyWright.chi4DivisorSum`, `NTKB.HardyWright.chi4DivisorSum_eq_card_sub_card` | proved |  |
| Section 16.9 (closed form of delta(n), 16.9.5) | 333 | delta(n)=0 unless v is a square, then delta(n)=d(mu). | `NTKB.HardyWright.chi4DivisorSum_eq_prod`, `NTKB.HardyWright.chi4DivisorSum_eq_zero`, `NTKB.HardyWright.chi4DivisorSum_eq_card_divisors` | proved |  |
| Theorem 278 | 333 | For n>1, r(n)=4 delta(n)=4 (d_1(n)-d_3(n)). | `NTKB.HardyWright.sumTwoSquaresCount_eq`, `NTKB.HardyWright.sumTwoSquaresCount_eq_card_sub_card` | proved |  |

## Chapter XVII. Generating functions of arithmetical functions

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Section 17.1 (1) (absolute convergence persists for larger s) | 338 | If sum a_n n^-s converges absolutely at s1 it does so at every larger s | `LSeriesSummable_of_abscissaOfAbsConv_lt_re` | in Mathlib |  |
| Section 17.1 (2) (term-by-term differentiation) | 338 | An absolutely convergent Dirichlet series may be differentiated termwise: F'(s) = -sum a_n log n n^-s | `LSeries_hasDerivAt`, `LSeries_deriv` | in Mathlib |  |
| Section 17.1 (3) (uniqueness theorem) | 338 | If sum a_n n^-s = sum b_n n^-s for all large s then a_n = b_n for all n | `LSeries_eq_iff_of_abscissaOfAbsConv_lt_top`, `LSeries_injOn` | in Mathlib |  |
| Section 17.1 (4) (product of two Dirichlet series) | 339 | Two absolutely convergent Dirichlet series can be multiplied | `LSeries_convolution'` | in Mathlib |  |
| Section 17.2 (17.2.2) (zeta(2) = pi^2/6) | 339 | zeta(2) = sum 1/n^2 = pi^2/6 | `hasSum_zeta_two` | in Mathlib |  |
| Section 17.2 (footnote: zeta(2n) rational multiple of pi^2n via Bernoulli numbers) | 339 | zeta(2n) is a rational multiple of pi^(2n) given by Bernoulli numbers | `hasSum_zeta_nat`, `riemannZeta_two_mul_nat` | in Mathlib |  |
| Theorem 279 | 339 | zeta'(s) = - sum log n / n^s for s > 1 | `LSeries_deriv`, `LSeries_one_eq_riemannZeta` | in Mathlib |  |
| Theorem 280 | 339 | Euler product: zeta(s) = prod over primes (1 - p^-s)^-1 for s > 1 | `riemannZeta_eulerProduct_tprod`, `riemannZeta_eulerProduct_hasProd`, `riemannZeta_eulerProduct` | in Mathlib |  |
| Theorem 281 | 341 | zeta(s) = 1/(s-1) + O(1) as s tends to 1 from above | `isBigO_riemannZeta_sub_one_div`, `tendsto_riemannZeta_sub_one_div` | in Mathlib |  |
| Theorem 282 | 341 | log zeta(s) = log(1/(s-1)) + O(s-1) as s tends to 1 from above | `log_riemannZeta_add_log_sub_isBigO_ofReal` | in Mathlib |  |
| Section 17.3 (zeta(s) ~ 1/(s-1)) | 342 | (s-1) zeta(s) tends to 1 as s tends to 1 | `riemannZeta_residue_one` | in Mathlib |  |
| Theorem 283 | 342 | zeta'(s) = -1/(s-1)^2 + O(1) as s tends to 1 from above | `deriv_riemannZeta_add_inv_sub_sq_bounded` | in Mathlib |  |
| Theorem 284 | 343 | Product of two absolutely convergent Dirichlet series is the series of the Dirichlet convolution of the coefficients | `LSeries_convolution'`, `LSeries_mul'` | in Mathlib |  |
| Theorem 285 | 344 | For f multiplicative with f(1)=1, sum f(n) n^-s is the formal product of the local series 1 + f(p)p^-s + f(p^2)p^-2s + ... | `EulerProduct.eulerProduct_hasProd` | partly in other libraries; not proved here |  |
| Theorem 286 | 345 | Euler product for an arbitrary multiplicative f with sum \\|f(n)\\| n^-s convergent | `EulerProduct.eulerProduct_tprod`, `EulerProduct.eulerProduct_hasProd`, `EulerProduct.eulerProduct` | in Mathlib |  |
| Theorem 287 | 345 | 1/zeta(s) = sum mu(n) n^-s for s > 1 | `LSeries_zeta_mul_Lseries_moebius`, `LSeries_one_mul_Lseries_moebius` | in Mathlib |  |
| Theorem 288 | 346 | zeta(s-1)/zeta(s) = sum phi(n) n^-s for s > 2 | `LSeries_totient_eq` | in PrimeNumberTheoremAnd only (not a dependency) |  |
| Theorem 289 | 346 | zeta(s)^2 = sum d(n) n^-s for s > 1 | `NTKB.Apostol.LSeries_divisorC` | proved | PNT+: `LSeries_tau_eq_riemannZeta_sq` |
| Theorem 290 | 346 | zeta(s) zeta(s-1) = sum sigma(n) n^-s for s > 2 | `LSeries_sigma_eq_riemannZeta_mul` | in PrimeNumberTheoremAnd only (not a dependency) |  |
| Theorem 291 | 346 | zeta(s) zeta(s-k) = sum sigma_k(n) n^-s for s > 1 and s > k+1 | `LSeries_sigma_eq_riemannZeta_mul`, `sigmaR_natCast` | in PrimeNumberTheoremAnd only (not a dependency) |  |
| Theorem 292 | 347 | sum_n c_n(m) n^-s = sigma_{s-1}(m) / (m^(s-1) zeta(s)) for Ramanujan sums c_n(m) | `NTKB.HardyWright.LSeries_ramanujanSum` | proved |  |
| Theorem 293 | 347 | sum_n c_n(m)/n^2 = 6 sigma(m)/(pi^2 m) | `NTKB.HardyWright.tsum_ramanujanSum_div_sq` | proved |  |
| Section 17.6 (Mobius inversion via Dirichlet series; Z x M = I) | 348 | Formal Dirichlet series identity Z x M = I (17.6.1), equivalent to the sum of mu(d) over d \\| n being [n=1] | `ArithmeticFunction.coe_zeta_mul_coe_moebius`, `ArithmeticFunction.moebius_mul_coe_zeta` | in Mathlib |  |
| Theorem 294 | 351 | -zeta'(s)/zeta(s) = sum Lambda(n) n^-s for s > 1 | `ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div` | in Mathlib |  |
| Theorem 295 | 352 | Lambda(n) = sum over d \\| n of mu(n/d) log d | `ArithmeticFunction.moebius_mul_log_eq_vonMangoldt`, `ArithmeticFunction.log_mul_moebius_eq_vonMangoldt` | in Mathlib |  |
| Theorem 296 | 352 | log n = sum over d \\| n of Lambda(d) | `ArithmeticFunction.vonMangoldt_sum` | in Mathlib |  |
| Theorem 297 | 353 | mu(n) log n = - sum over d \\| n of mu(d) Lambda(n/d) | `mu_log_eq_mu_mul_neg_lambda` | in PrimeNumberTheoremAnd only (not a dependency) |  |
| Theorem 298 | 353 | Lambda(n) = - sum over d \\| n of mu(d) log d | `ArithmeticFunction.sum_moebius_mul_log_eq` | in Mathlib |  |
| Theorem 299 | 353 | zeta(s)^k = sum d_k(n) n^-s, d_k(n) the number of ordered factorisations into k factors | `LSeries_d_eq_riemannZeta_pow` | in PrimeNumberTheoremAnd only (not a dependency) |  |
| Theorem 300 | 354 | zeta(2s)/zeta(s) = sum lambda(n) n^-s with lambda(n) = (-1)^(number of prime factors with multiplicity) | `NTKB.HardyWright.LSeries_liouville` | proved |  |
| Theorem 301 | 354 | zeta(s)^2/zeta(2s) = sum 2^omega(n) n^-s | `zeta_pow_two` | in PrimeNumberTheoremAnd only (not a dependency) |  |
| Theorem 302 | 354 | zeta(s)/zeta(2s) = sum \\|mu(n)\\| n^-s (squarefree numbers) | `NTKB.Apostol.LSeries_moebiusSq` | proved | PNT+: `zeta_alt` |
| Theorem 303 | 355 | zeta(s)/zeta(ks) = sum q_k(n) n^-s, q_k the indicator of k-th-power-free numbers | `NTKB.HardyWright.LSeries_powerFreeIndicator` | proved |  |
| Theorem 304 | 355 | Ramanujan: zeta(s)^4/zeta(2s) = sum d(n)^2 n^-s | `NTKB.HardyWright.LSeries_card_divisors_sq` | proved |  |
| Theorem 305 | 356 | Ramanujan: zeta(s) zeta(s-a) zeta(s-b) zeta(s-a-b) / zeta(2s-a-b) = sum sigma_a(n) sigma_b(n) n^-s | `NTKB.HardyWright.LSeries_sigma_mul_sigma` | proved |  |
| Section 17.9 (Euler product of L(s), L(s) = L-series of chi_4) | 356 | L(s) = 1 - 3^-s + 5^-s - ... equals the Euler product prod (1 - chi(p) p^-s)^-1 | `DirichletCharacter.LSeries_eulerProduct_tprod` | in Mathlib |  |
| Theorem 306 | 356 | sum r(n) n^-s = 4 zeta(s) L(s) for s > 1 | `NTKB.HardyWright.LSeries_sumTwoSquaresCount` | proved |  |
| Theorem 307 | 358 | sum a_n x^n/(1-x^n) = sum b_n x^n iff zeta(s) f(s) = g(s), where b_N is the sum of a_n over n \\| N | `NTKB.HardyWright.hasSum_lambert` | proved in part | Tau Ceti: `TauCeti.hasSum_sum_divisors_mul_pow`, Mathlib: `tsum_pow_div_one_sub_eq_tsum_sigma` |
| Theorem 308 | 359 | sum mu(n) x^n/(1-x^n) = x | `NTKB.HardyWright.hasSum_moebius_lambert` | proved |  |
| Theorem 309 | 359 | sum phi(n) x^n/(1-x^n) = x/(1-x)^2 | `NTKB.HardyWright.hasSum_totient_lambert` | proved |  |
| Theorem 310 | 359 | sum d(n) x^n = sum x^n/(1-x^n) (Lambert series for the divisor function) | `tsum_pow_div_one_sub_eq_tsum_sigma`, `ArithmeticFunction.sigma_zero_apply` | in Mathlib |  |
| Theorem 311 | 359 | sum r(n) x^n = 4 (x/(1-x) - x^3/(1-x^3) + x^5/(1-x^5) - ...) | `NTKB.HardyWright.hasSum_sumTwoSquaresCount_mul_pow` | proved |  |
| Theorem 312 | 359 | Jacobi: (1+2x+2x^4+2x^9+...)^2 = 1 + 4 (x/(1-x) - x^3/(1-x^3) + ...) | `NTKB.HardyWright.jacobi_theta_sq`, `NTKB.HardyWright.hasSum_sumTwoSquaresCount_mul_pow_nat` | proved |  |

## Chapter XVIII. The order of magnitude of arithmetical functions

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Theorem 313 | 361 | liminf d(n) = 2 (d(p)=2 for primes, d(n)>2 otherwise) | `NTKB.HardyWright.liminf_card_divisors` | proved |  |
| Theorem 314 | 361 | d(n) = O((log n)^A) is false for every A | `NTKB.HardyWright.not_card_divisors_isBigO_log_rpow` | proved |  |
| Theorem 315 | 362 | d(n) = O(n^delta) for every delta > 0 | `NTKB.HardyWright.card_divisors_isLittleO_rpow`, `NTKB.HardyWright.card_divisors_isBigO_rpow` | proved | Tau Ceti: `TauCeti.exists_pos_card_divisors_le_rpow` |
| Theorem 316 | 362 | If f is multiplicative and f(p^m) tends to 0 as p^m tends to infinity, then f(n) tends to 0 | `NTKB.HardyWright.tendsto_zero_of_isMultiplicative` | proved |  |
| Theorem 317 | 364 | Wigert: limsup log d(n) loglog n / log n = log 2 | `NTKB.HardyWright.limsup_log_card_divisors`, `NTKB.HardyWright.eventually_log_card_divisors_lt`, `NTKB.HardyWright.frequently_log_card_divisors_gt`, `NTKB.HardyWright.log_card_divisors_le` | proved |  |
| Theorem 318 | 366 | d(1)+...+d(n) ~ n log n | `NTKB.HardyWright.sum_card_divisors_isEquivalent` | proved |  |
| Theorem 319 | 366 | The average order of d(n) is log n | `NTKB.HardyWright.sum_card_divisors_isEquivalent_sum_log` | proved |  |
| Theorem 320 | 366 | Dirichlet: d(1)+...+d(n) = n log n + (2 gamma - 1) n + O(sqrt n) | `NTKB.HardyWright.sum_card_divisors_sub_isBigO` | proved |  |
| Section 18.2 (almost all n have about (log n)^(log 2) divisors) | 368 | Almost all n have about (log n)^(log 2) divisors; proof deferred to 22.13 | `NTKB.HardyWright.tendsto_card_normalOrder_card_divisors`, `NTKB.HardyWright.tendsto_card_normalOrder_cardDistinctFactors` | proved |  |
| Theorem 321 | 369 | sigma(n) >= n | `NTKB.HardyWright.le_sigma_one` | proved |  |
| Theorem 322 | 369 | sigma(n) = O(n^(1+delta)) for every delta > 0 | `NTKB.HardyWright.sigma_one_isBigO_rpow` | proved | Tau Ceti: `TauCeti.sigma_le_rpow_mul_tsum` |
| Theorem 323 | 369 | Gronwall: limsup sigma(n)/(n log log n) = e^gamma | `NTKB.HardyWright.limsup_sigma_div_mul_log_log`, `NTKB.HardyWright.ExtremalOrder.eventually_sigma_div_mul_log_log_le`, `NTKB.HardyWright.ExtremalOrder.frequently_sigma_div_mul_log_log_ge` | proved |  |
| Theorem 324 | 370 | sigma(1)+...+sigma(n) = (pi^2/12) n^2 + O(n log n) | `NTKB.HardyWright.sum_sigma_one_sub_isBigO` | proved |  |
| Theorem 325 | 371 | phi(n) < n for n > 1 | `Nat.totient_lt` | in Mathlib |  |
| Theorem 326 | 371 | limsup phi(n)/n = 1 | `NTKB.HardyWright.limsup_totient_div` | proved |  |
| Theorem 327 | 371 | phi(n) / n^(1-delta) tends to infinity for every delta > 0 | `NTKB.HardyWright.tendsto_totient_div_rpow` | proved |  |
| Theorem 328 | 371 | liminf phi(n) loglog n / n = e^-gamma | `NTKB.HardyWright.liminf_totient_mul_log_log_div`, `NTKB.HardyWright.ExtremalOrder.eventually_totient_mul_log_log_div_ge`, `NTKB.HardyWright.ExtremalOrder.frequently_totient_mul_log_log_div_le` | proved |  |
| Theorem 329 | 371 | A < sigma(n) phi(n)/n^2 < 1 for a positive constant A (A = 6/pi^2) | `NTKB.HardyWright.exists_lt_sigma_mul_totient_div_sq`, `NTKB.HardyWright.sigmaTotientDivSq_eq_prod` | proved |  |
| Theorem 330 | 372 | Phi(n) = phi(1)+...+phi(n) = 3n^2/pi^2 + O(n log n) | `NTKB.HardyWright.sum_totient_sub_isBigO` | proved |  |
| Theorem 331 | 373 | The number of terms of the Farey series of order n is about 3n^2/pi^2 | `NTKB.HardyWright.card_fareySeries_sub_isBigO`, `NTKB.HardyWright.card_fareySeries_isEquivalent`, `NTKB.HardyWright.card_fareySeries` | proved |  |
| Theorem 332 | 373 | The probability that two integers are coprime is 6/pi^2 | `NTKB.HardyWright.tendsto_card_coprime_div_card` | proved |  |
| Theorem 333 | 374 | The squarefree numbers up to x number 6x/pi^2 + O(sqrt x) | `NTKB.HardyWright.squarefreeCount_sub_isBigO`, `NTKB.HardyWright.tendsto_squarefreeCount_div` | proved |  |
| Theorem 334 | 375 | sum_{n<=x} \\|mu(n)\\| = 6x/pi^2 + O(sqrt x) | `NTKB.HardyWright.sum_abs_moebius_sub_isBigO` | proved |  |
| Theorem 335 | 375 | M(x) = sum_{n<=x} mu(n) = o(x) | `NTKB.HardyWright.tendsto_mertens_div_self` | proved | PNT+: `mu_pnt` |
| Theorem 336 | 375 | The lower limit of r(n) is 0 (printed as lim r(n) = 0; r(n)=0 for n = 3 mod 4) | `NTKB.HardyWright.liminf_sumTwoSquaresCount` | proved |  |
| Theorem 337 | 375 | r(n) = O((log n)^A) is false for every A | `NTKB.HardyWright.not_sumTwoSquaresCount_isBigO_log_rpow` | proved |  |
| Theorem 338 | 375 | r(n) = O(n^delta) for every delta > 0 | `NTKB.HardyWright.sumTwoSquaresCount_isBigO_rpow` | proved |  |
| Section 18.7 (maximum order of r(n)) | 376 | The maximum order of r(n) is 2^(log n/log log n) up to the exponent constants | — | not formalized |  |
| Theorem 339 | 376 | Gauss: r(1)+...+r(n) = pi n + O(sqrt n) | `NTKB.HardyWright.sum_sumTwoSquaresCount_sub_isBigO`, `NTKB.HardyWright.tendsto_sum_sumTwoSquaresCount_div` | proved |  |
| Theorem 340 | 376 | r_3(1)+...+r_3(n) = (4/3) pi n^(3/2) + O(n) | `NTKB.HardyWright.sum_sumSquaresCount_three_sub_isBigO` | proved |  |
| Theorem 341 | 378 | sum_{v<=x} r(v) = 4 (floor x - floor(x/3) + floor(x/5) - ...) | `NTKB.HardyWright.sum_sumTwoSquaresCount_eq` | proved |  |

## Chapter XIX. Partitions

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Theorem 342 | 381 | Number of partitions of n into m parts equals number of partitions of n with largest part m | `NTKB.HardyWright.card_partitions_parts_eq_card_partitions_largest` | proved | Mathlib: `Nat.Partition.conjugate`, Mathlib: `Nat.Partition.conjugate_conjugate` |
| Theorem 343 | 381 | Number of partitions of n into at most m parts equals number into parts not exceeding m | `NTKB.HardyWright.card_partitions_parts_le_eq_card_partitions_largest_le` | proved | Mathlib: `Nat.Partition.conjugate`, Mathlib: `Nat.Partition.conjugate_conjugate` |
| Section 19.3 (19.3.1, Euler's generating function of p(n)) | 382 | sum p(n)x^n = product over k of 1/(1-x^k) | `NTKB.HardyWright.tprod_one_sub_X_pow_mul_partitionSeries`, `NTKB.NZM.exists_tendsto_eulerPartialProd`, `NTKB.NZM.hasSum_card_partition_mul_pow` | proved in part | Mathlib: `Nat.Partition.hasProd_genFun`, Mathlib: `Nat.Partition.hasProd_powerSeriesMk_card_restricted` |
| Section 19.3 (19.3.7, parts at most m) | 383 | 1/((1-x)...(1-x^m)) enumerates partitions of n into parts not exceeding m (equivalently at most m parts) | `NTKB.NZM.hasSum_card_restricted_mul_pow`, `NTKB.HardyWright.card_partitions_parts_le_eq_card_partitions_largest_le` | proved in part | Mathlib: `Nat.Partition.hasProd_powerSeriesMk_card_restricted` |
| Section 19.4 (19.4.1-19.4.5, generating functions with restricted parts) | 384 | Generating functions for partitions into odd, even, unequal, odd-and-unequal parts and parts congruent to 1,4 mod 5 | `Nat.Partition.hasProd_powerSeriesMk_card_restricted`, `Nat.Partition.hasProd_powerSeriesMk_card_countRestricted` | partly in other libraries; not proved here |  |
| Section 19.4 (19.4.7, product identity behind Theorem 344) | 385 | prod (1+x^k) = prod 1/(1-x^(2k-1)); analytic form: prod(1+q^n) prod(1-q^(2n+1)) = 1 | `TauCeti.tprod_one_add_pow_mul_tprod_one_sub_pow_odd` | in Tau Ceti only (not a dependency) |  |
| Theorem 344 | 385 | Partitions of n into unequal parts are as many as partitions into odd parts | `Nat.Partition.card_odds_eq_card_distincts` | in Mathlib |  |
| Theorem 345 | 385 | (1+x)(1+x^3)(1+x^5)... = 1 + x/(1-x^2) + x^4/((1-x^2)(1-x^4)) + ... | `NTKB.HardyWright.tprod_one_add_pow_odd_eq_tsum` | proved |  |
| Theorem 346 | 386 | (1+x^2)(1+x^4)(1+x^6)... = 1 + x^2/(1-x^2) + x^6/((1-x^2)(1-x^4)) + ... | `NTKB.HardyWright.tprod_one_add_pow_even_eq_tsum` | proved |  |
| Section 19.5 (19.5.1, two-parameter form) | 386 | (1+ax)(1+ax^3)(1+ax^5)... = 1 + sum a^m x^(m^2)/((1-x^2)...(1-x^(2m))) (Euler) | `NTKB.HardyWright.hasProd_one_add_mul_pow_odd`, `NTKB.HardyWright.hasProd_one_add_mul_pow` | proved |  |
| Theorem 347 | 388 | Partitions of n into odd unequal parts are equinumerous with self-conjugate partitions of n | `NTKB.HardyWright.card_oddDistincts_eq_card_selfConjugate` | proved |  |
| Theorem 348 | 389 | q-binomial theorem: finite product (1+ax)...(1+ax^j) equals a sum with Gaussian binomial coefficients | `NTKB.HardyWright.prod_one_add_mul_pow_eq_sum_qBinom`, `NTKB.HardyWright.qBinom_eq_prod_div` | proved |  |
| Theorem 349 | 389 | q-binomial series: 1/((1-ax)...(1-ax^j)) expansion | `NTKB.HardyWright.hasSum_one_div_prod_one_sub_mul_pow`, `NTKB.HardyWright.hasSum_inv_tprod_one_sub_mul_pow` | proved |  |
| Theorem 350 | 389 | 1/((1-x)(1-x^2)...) = 1 + x/(1-x) + x^2/((1-x)(1-x^2)) + ... (the limit a=1, j to infinity) | `NTKB.HardyWright.hasSum_one_div_tprod_one_sub_pow` | proved |  |
| Theorem 351 | 390 | prod 1/(1-x^k) = 1 + sum x^(i^2)/((1-x)^2...(1-x^i)^2) (Durfee square) | `NTKB.HardyWright.hasSum_pow_sq_div_prod_sq`, `NTKB.HardyWright.Durfee.qBinom_two_mul_eq_sum` | proved |  |
| Theorem 352 | 391 | Jacobi triple product: prod (1-x^2n)(1+x^(2n-1)z)(1+x^(2n-1)/z) = sum x^(n^2) z^n | `NTKB.HardyWright.jacobi_triple`, `NTKB.HardyWright.jacobi_triple_symm` | proved |  |
| Section 19.9 (19.9.1-19.9.2, specialisations of the triple product) | 394 | Product-sum identities for exponents kn^2+ln (k,l small) | `NTKB.HardyWright.jacobi_special_sub`, `NTKB.HardyWright.jacobi_special_add` | proved |  |
| Theorem 353 | 395 | Euler pentagonal number theorem: prod(1-x^n) = sum over integers n of (-1)^n x^(n(3n+1)/2) | `eulerFunction_eq_tprod`, `eulerFunction_eq_tsum_pentagonal`, `PowerSeries.WithPiTopology.tprod_one_sub_X_pow` | in Mathlib |  |
| Section 19.9 (19.9.3, pentagonal series as +/- pairs) | 395 | prod(1-x^k) = 1 - x - x^2 + x^5 + x^7 - x^12 - ... | `eulerFunction_eq_tsum_pentagonal_pair` | in Mathlib |  |
| Theorem 354 | 395 | prod (1-x^2n)/(1-x^(2n-1)) = 1 + x + x^3 + x^6 + ... (triangular numbers; Gauss) | `NTKB.HardyWright.hasProd_eq_tsum_triangular` | proved |  |
| Theorem 355 | 395 | prod (1-x^(5n+1))(1-x^(5n+4))(1-x^(5n+5)) = sum (-1)^n x^(n(5n+3)/2) | `NTKB.HardyWright.hasProd_five_one_four` | proved |  |
| Theorem 356 | 395 | prod (1-x^(5n+2))(1-x^(5n+3))(1-x^(5n+5)) = sum (-1)^n x^(n(5n+1)/2) | `NTKB.HardyWright.hasProd_five_two_three` | proved |  |
| Theorem 357 | 396 | Jacobi: prod(1-x^n)^3 = sum (-1)^m (2m+1) x^(m(m+1)/2) | `NTKB.HardyWright.jacobi_cube_identity`, `NTKB.HardyWright.pentagonalSeries_pow_three` | proved |  |
| Theorem 358 | 397 | E(n) - U(n) (partitions into even / odd number of unequal parts) is 0 unless n is a pentagonal number, where it is (-1)^k | `NTKB.HardyWright.evenDistinctCount_sub_oddDistinctCount` | proved |  |
| Section 19.10 (19.10.2, pentagonal recurrence for p(n)) | 397 | p(n) - p(n-1) - p(n-2) + p(n-5) + ... = 0 | `NTKB.HardyWright.card_partition_pentagonal_recurrence` | proved |  |
| Theorem 359 | 399 | p(5m+4) is divisible by 5 | `NTKB.HardyWright.five_dvd_card_partition` | proved |  |
| Theorem 360 | 399 | p(7m+5) is divisible by 7 | `NTKB.HardyWright.seven_dvd_card_partition` | proved |  |
| Theorem 361 | 399 | p(11m+6) is divisible by 11 (starred in book) | — | not formalized |  |
| Section 19.12 (higher prime-power moduli, Ramanujan conjecture, Watson) | 400 | p(25m+24) divisible by 25; p(n) divisible by 5^a 7^b 11^c if 24n is 1 mod the modulus (7^b modified by Watson) | — | not formalized |  |
| Section 19.12 (Dyson rank, Atkin-Swinnerton-Dyer) | 402 | For n congruent to 4 mod 5 the five rank classes (mod 5) of partitions of n are equinumerous | — | not formalized |  |
| Theorem 362 | 402 | First Rogers-Ramanujan identity: sum x^(n^2)/((1-x)...(1-x^n)) = prod 1/((1-x^(5m+1))(1-x^(5m+4))) | `NTKB.HardyWright.rogers_ramanujan_one`, `NTKB.HardyWright.rrH_one`, `NTKB.HardyWright.rrH_two_sub`, `NTKB.HardyWright.rrH_two_eq`, `NTKB.HardyWright.rrH_two_eq_rrG` | proved |  |
| Theorem 363 | 403 | Second Rogers-Ramanujan identity: sum x^(n(n+1))/((1-x)...(1-x^n)) = prod 1/((1-x^(5m+2))(1-x^(5m+3))) | `NTKB.HardyWright.rogers_ramanujan_two` | proved |  |
| Theorem 364 | 404 | Partitions with minimal difference 2 are equinumerous with partitions into parts congruent to 1 or 4 mod 5 | — | not formalized |  |
| Theorem 365 | 404 | Partitions into parts at least 2 with minimal difference 2 are equinumerous with partitions into parts congruent to 2 or 3 mod 5 | — | not formalized |  |
| Section 19.15 (19.15.1, Rogers-Ramanujan continued fraction) | 408 | F(a)/F(ax) = 1 + ax/(1+ ax^2/(1+ ...)); at a=1 gives the ratio of the Rogers-Ramanujan products; value at e^(-2 pi) stated | — | not formalized |  |

## Chapter XX. The representation of a number by two or four squares

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Section 20.1 (counting: k-1 kth powers do not suffice) | 412 | Most numbers are not sums of k-1 or fewer kth powers (so s at least k) | `NTKB.HardyWright.tendsto_card_isSumOfPowers_pred_div`, `NTKB.HardyWright.card_isSumOfPowers_le_pow` | proved |  |
| Section 20.1 (Hilbert-Waring existence of g(k); values g(3)=9) | 413 | g(k) exists for each k (Hilbert); g(3)=9, only 23 and 239 need 9 cubes | `NTKB.HardyWright.waringNumber_two`, `NTKB.HardyWright.waringNumber_three_le`, `NTKB.HardyWright.waringNumber_four_le`, `NTKB.HardyWright.waringNumber_six_le`, `NTKB.HardyWright.waringNumber_eight_le` | proved in part |  |
| Theorem 366 | 414 | n is a sum of two squares iff every prime factor 4m+3 occurs to an even power | `Nat.eq_sq_add_sq_iff` | in Mathlib |  |
| Section 20.3 (product of two sums of two squares) | 415 | (x1^2+y1^2)(x2^2+y2^2) = (x1x2+y1y2)^2 + (x1y2-x2y1)^2 | `Nat.sq_add_sq_mul`, `sq_add_sq_mul` | in Mathlib |  |
| Theorem 251 (recalled in Section 20.3) | 415 | A prime p of the form 4m+1 is a sum of two squares | `Nat.Prime.sq_add_sq` | in Mathlib |  |
| Theorem 367 | 415 | If p=4m+3 divides n then n has no primitive representation as x^2+y^2 | `ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_coprime`, `Nat.mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one`, `NTKB.HardyWright.not_primitive_sq_add_sq` | in Mathlib |  |
| Theorem 368 | 415 | If p=4m+3 divides n to an odd power then n has no representation as a sum of two squares | `Nat.eq_sq_add_sq_iff`, `NTKB.HardyWright.not_sq_add_sq_of_odd_multiplicity` | in Mathlib |  |
| Section 20.5 (20.5.1, Euler four-square identity) | 418 | (sum x_i^2)(sum y_i^2) = sum of four squares of bilinear forms | `euler_four_squares`, `Nat.euler_four_squares`, `sum_four_sq_mul_sum_four_sq` | in Mathlib |  |
| Theorem 369 | 418 | Lagrange: every positive integer is a sum of four squares | `Nat.sum_four_squares` | in Mathlib |  |
| Theorem 370 | 418 | Every prime is a sum of four squares | `Nat.Prime.sum_four_squares`, `NTKB.HardyWright.Nat.Prime.sum_four_squares_of_quaternions` | in Mathlib |  |
| Section 20.6 (quaternion algebra, conjugate and norm; 20.6.5, 20.6.8) | 420 | Quaternions form a non-commutative ring; q times its conjugate is the norm, and the norm is multiplicative | `Quaternion.normSq`, `Quaternion.star_mul_self` | in Mathlib |  |
| Section 20.6 (integral quaternions, Hurwitz order; 20.6.13) | 421 | Integral quaternions (all coordinates integers or all halves of odd integers) are closed under product; basis rho,i1,i2,i3 | `NTKB.HardyWright.integralQuaternions`, `NTKB.HardyWright.mem_integralQuaternions_iff` | proved |  |
| Section 20.6 (the 24 unities) | 422 | The integral quaternions of norm 1 are exactly the 24 listed units (covers D118) | `NTKB.HardyWright.isUnit_iff_mem_unities`, `NTKB.HardyWright.ncard_unities`, `NTKB.HardyWright.isUnit_iff_qnorm_eq_one` | proved |  |
| Theorem 371 | 422 | Every integral quaternion has an associate with integral coordinates; an odd one has an associate with non-integral coordinates | `NTKB.HardyWright.exists_isUnit_hasIntCoords_mul`, `NTKB.HardyWright.exists_isUnit_not_hasIntCoords_mul` | proved |  |
| Theorem 372 | 423 | For an integral quaternion K and m>0 there is an integral L with norm(K - mL) < m^2 | `NTKB.HardyWright.exists_qnorm_sub_natCast_mul_lt` | proved |  |
| Theorem 373 | 424 | Division with remainder in integral quaternions: a = L b + c with N(c) < N(b) | `NTKB.HardyWright.exists_eq_mul_add_qnorm_lt` | proved |  |
| Theorem 374 | 424 | Every right ideal of integral quaternions is principal | `NTKB.HardyWright.ideal_eq_mul_singleton`, `NTKB.HardyWright.ideal_isPrincipal` | proved |  |
| Theorem 375 | 425 | Two integral quaternions have a highest common right divisor, unique up to a left unit, of the form mu a + nu b | `NTKB.HardyWright.exists_highestCommonRightDivisor`, `NTKB.HardyWright.IsHighestCommonRightDivisor.unique` | proved |  |
| Theorem 376 | 426 | For a integral and b = m rational integer, (a,b) right-coprime iff (N a, m) = 1 | `NTKB.HardyWright.rightCoprime_natCast_iff` | proved |  |
| Theorem 377 | 426 | An integral quaternion is prime iff its norm is a rational prime | `NTKB.HardyWright.irreducible_iff_prime_qnorm` | proved |  |
| Theorem 378 | 426 | A rational prime is not a prime quaternion | `NTKB.HardyWright.not_irreducible_natCast` | proved |  |
| Theorem 379 | 428 | For odd prime p, 4p is a sum of four odd squares | `NTKB.HardyWright.four_mul_prime_eq_sum_four_odd_sq` | proved |  |
| Theorem 380 | 428 | g(2) = G(2) = 4 | `NTKB.HardyWright.waringNumber_two`, `NTKB.HardyWright.asymptoticWaringNumber_two`, `NTKB.HardyWright.four_le_of_eventually_isSumOfPowers_two` | proved | Mathlib: `Nat.sum_four_squares` |
| Section 20.10 (three-square theorem) | 428 | n is a sum of three squares iff n is not of the form 4^a(8m+7) (Legendre-Gauss); stated without proof | `NTKB.HardyWright.not_isSumOfPowers_two_three` | proved in part |  |
| Theorem 381 | 429 | sum over m of u_m(1+u_m) = sum n u_n, with u_r = x^r/(1-x^r) | `NTKB.HardyWright.tsum_lambertU_mul_one_add`, `NTKB.HardyWright.lambertU` | proved |  |
| Theorem 382 | 430 | sum (-1)^(m-1) u_(2m)(1+u_(2m)) = sum (2n-1) x^(4n-2)/(1-x^(4n-2)) | `NTKB.HardyWright.tsum_neg_one_pow_lambertU` | proved |  |
| Theorem 383 | 430 | Cotangent identity L^2 = T1 + T2 for L = (1/4)cot(theta/2) + sum u_n sin n theta | `NTKB.HardyWright.cotangent_identity` | proved |  |
| Theorem 384 | 433 | (1/4 + u1 - u3 + u5 - u7 + ...)^2 = (1/16) + 2(u1 + 2u2 + 3u3 + 5u5 + ...) (no u_4k terms) | `NTKB.HardyWright.sq_quarter_add_chi4` | proved |  |
| Theorem 385 | 433 | (1+2x+2x^4+2x^9+...)^4 = 1 + 8 sum m x^m/(1+(-x)^m), m not multiple of 4 | `NTKB.HardyWright.theta_pow_four` | proved |  |
| Theorem 386 | 434 | Jacobi: the number of representations of n as an ordered signed sum of four squares is 8 times the sum of divisors of n not divisible by 4 | `NTKB.HardyWright.sumFourSquaresCount_eq`, `NTKB.HardyWright.hasSum_sumFourSquaresCount` | proved |  |
| Section 20.13 (r6(n) and r8(n) formulas) | 434 | Formulae for the number of representations as six and eight squares in terms of divisor sums (Jacobi) | — | not formalized |  |
| Section 20.13 notes (Conway-Schneeberger fifteen theorem) | 436 | A positive-definite integral quadratic form representing 1 to 15 represents all positive integers | — | not formalized |  |

## Chapter XXI. Representation by cubes and higher powers

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Theorem 387 | 438 | g(4) exists and is at most 50 (via four squares and a 12-biquadrate identity) | `NTKB.HardyWright.isSumOfPowers_four_fifty`, `NTKB.HardyWright.waringNumber_four_le`, `NTKB.HardyWright.isSumOfPowers_four_nineteen_of_le` | proved |  |
| Section 21.1 (identity 21.1.1) | 438 | 6(a^2+b^2+c^2+d^2)^2 equals a sum of twelve fourth powers of linear forms | `NTKB.HardyWright.six_mul_sum_sq_sq` | proved |  |
| Theorem 388 | 439 | G(3) <= 13 (all large n are sums of 13 non-negative cubes) | `NTKB.HardyWright.eventually_isSumOfPowers_three_thirteen`, `NTKB.HardyWright.asymptoticWaringNumber_three_le` | proved |  |
| Theorem 389 | 441 | Every n > 10^25 is a sum of 13 non-negative cubes | `NTKB.HardyWright.isSumOfPowers_three_thirteen_of_gt`, `NTKB.HardyWright.isSumOfPowers_three_thirteen_of_mem` | proved |  |
| Theorem 390 | 443 | g(3) <= 13 (true value 9, needs three-squares theorem) | `NTKB.HardyWright.isSumOfPowers_three_thirteen`, `NTKB.HardyWright.waringNumber_three_le` | proved |  |
| Theorem 391 | 444 | g(6) <= 184 g(3)+59 < 2451 | `NTKB.HardyWright.isSumOfPowers_six_of_three`, `NTKB.HardyWright.waringNumber_six_le`, `NTKB.HardyWright.sixty_mul_sum_sq_cube` | proved |  |
| Section 21.4 (identity 21.4.2) | 444 | 5040(a^2+b^2+c^2+d^2)^4 is a sum of 840 eighth powers of linear forms | `NTKB.HardyWright.five_thousand_forty_mul_sum_sq_pow_four` | proved |  |
| Theorem 392 | 444 | g(8) <= 540 g(4)+273 < 42273 | `NTKB.HardyWright.isSumOfPowers_eight_of_four`, `NTKB.HardyWright.waringNumber_eight_le` | proved |  |
| Theorem 393 | 445 | g(k) >= 2^k + floor((3/2)^k) - 2 | `NTKB.HardyWright.two_pow_add_le_of_forall_isSumOfPowers`, `NTKB.HardyWright.two_pow_add_le_waringNumber` | proved |  |
| Theorem 394 | 445 | G(k) >= k+1 for k > 2 | `NTKB.HardyWright.succ_le_of_eventually_isSumOfPowers` | proved |  |
| Theorem 395 | 447 | G(4) >= 16 | `NTKB.HardyWright.sixteen_le_of_eventually_isSumOfPowers_four`, `NTKB.HardyWright.sixteen_le_asymptoticWaringNumber_four` | proved |  |
| Theorem 396 | 447 | G(2^theta) >= 2^(theta+2) for theta >= 2 | `NTKB.HardyWright.two_pow_le_of_eventually_isSumOfPowers` | proved |  |
| Theorem 397 | 448 | For p odd prime, G(p^theta (p-1)) >= p^(theta+1) | `NTKB.HardyWright.prime_pow_le_of_eventually_isSumOfPowers` | proved |  |
| Theorem 398 | 448 | For p odd prime, G(2 p^theta (p-1)) >= (p^(theta+1)-1)/2 | `NTKB.HardyWright.half_prime_pow_le_of_eventually_isSumOfPowers` | proved |  |
| Theorem 399 | 449 | G(3*2^theta) >= 2^(theta+2) for theta >= 2 | `NTKB.HardyWright.two_pow_le_of_eventually_isSumOfPowers_three_mul` | proved |  |
| Theorem 400 | 449 | Summary of the four known lower bounds for G(k) | `NTKB.HardyWright.lower_bounds_asymptoticWaring` | proved |  |
| Theorem 401 | 450 | v(k) (Waring with signs) exists for every k | `NTKB.HardyWright.exists_forall_isSignedSumOfPowers`, `NTKB.HardyWright.IsSignedSumOfPowers`, `NTKB.HardyWright.signedWaringNumber` | proved |  |
| Theorem 402 | 450 | The (k-1)th forward difference of x^k at integer steps equals k!x plus a constant | `NTKB.HardyWright.exists_sum_choose_pow_eq` | proved | Mathlib: `fwdDiff_iter_eq_factorial` |
| Theorem 403 | 451 | v(k) <= 2^(k-1) + k!/2 | `NTKB.HardyWright.isSignedSumOfPowers_two_pow_add_factorial`, `NTKB.HardyWright.signedWaringNumber_le`, `NTKB.HardyWright.isSignedSumOfPowers_succ_of_eventually`, `NTKB.HardyWright.signedWaringNumber_le_asymptoticWaringNumber_add_one` | proved |  |
| Theorem 404 | 452 | v(2) = 3 | `NTKB.HardyWright.signedWaringNumber_two` | proved |  |
| Theorem 405 | 453 | v(3) is 4 or 5 | `NTKB.HardyWright.signedWaringNumber_three` | proved |  |
| Theorem 406 | 453 | 9 <= v(4) <= 12 | `NTKB.HardyWright.signedWaringNumber_four` | proved |  |
| Theorem 407 | 454 | 5 <= v(5) <= 10 | `NTKB.HardyWright.signedWaringNumber_five` | proved |  |
| Section 21.9 (trivial solutions) | 454 | The system S_h(a)=S_h(b), 1<=h<=k, has only permutation solutions when s<=k (Newton relations) | `NTKB.HardyWright.multiset_map_eq_of_sum_pow_eq`, `NTKB.HardyWright.IsNontrivialPTSolution`, `NTKB.HardyWright.prouhetTarryNumber` | proved |  |
| Theorem 408 | 455 | P(k,j) >= P(k,2) >= k+1 (Prouhet-Tarry numbers) | `NTKB.HardyWright.succ_le_of_isNontrivialPTSolution`, `NTKB.HardyWright.succ_le_prouhetTarryNumber_two_le` | proved |  |
| Theorem 409 | 455 | P(k,j) <= k(k+1)/2 + 1 | `NTKB.HardyWright.exists_isNontrivialPTSolution`, `NTKB.HardyWright.prouhetTarryNumber_le`, `NTKB.HardyWright.prouhetTarryNumber_bounds` | proved |  |
| Theorem 410 | 456 | P(k,j) = k+1 for k = 2, 3, 5 and all j | `NTKB.HardyWright.prouhetTarryNumber_eq_succ`, `NTKB.HardyWright.prouhetTarryNumber_two_eq_three`, `NTKB.HardyWright.prouhetTarryNumber_three_eq`, `NTKB.HardyWright.prouhetTarryNumber_five_eq` | proved |  |
| Theorem 411 | 459 | P(k,2) = k+1 for k < 7 | `NTKB.HardyWright.prouhetTarryNumber_two_eq` | proved |  |
| Section 21.11 (identity 21.11.4) | 460 | Explicit identity writing every twelfth power eta^12 (small eta) as sum of three positive cubes | `NTKB.HardyWright.three_cubes_identity`, `NTKB.HardyWright.three_cubes_identity_homogeneous`, `NTKB.HardyWright.exists_three_positive_cubes_eq_pow_twelve`, `NTKB.HardyWright.biquadrate_identity_one`, `NTKB.HardyWright.biquadrate_identity_two`, `NTKB.HardyWright.four_biquadrates_example`, `NTKB.HardyWright.fifth_power_identity`, `NTKB.HardyWright.fifth_power_three_three_example`, `NTKB.HardyWright.sixth_power_three_three_example` | proved in part |  |
| Theorem 412 | 461 | For every r some number is a sum of two positive cubes in at least r ways | `NTKB.HardyWright.exists_many_sum_two_cubes` | proved |  |
| Notes (Davenport G(4)=16) | 465 | G(4) = 16 (Davenport), g(4)=19 (Balasubramanian-Deshouillers-Dress) | — | not formalized |  |
| Notes (formula for g(k)) | 466 | g(k) = 2^k + floor((3/2)^k) - 2 whenever B <= 2^k - A - 2 (Dickson-Pillai-Niven) | — | not formalized |  |

## Chapter XXII. The series of primes (3)

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Section 22.1 (22.1.3) | 470 | psi(x) = log of lcm of 1..x | `Chebyshev.psi_eq_log_lcmUpto`, `Chebyshev.psi_eq_psi_coe_floor` | in Mathlib |  |
| Section 22.1 (22.1.5) | 471 | psi(x) = sum over m of theta(x^(1/m)) | `Chebyshev.psi_eq_sum_theta` | in Mathlib |  |
| Theorem 413 | 471 | psi(x) = theta(x) + O(sqrt(x) log^2 x) | `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log` | in Mathlib |  |
| Theorem 414 | 472 | theta(x) and psi(x) are of order x (A x < theta,psi < B x for x>=2) | `NTKB.HardyWright.theta_psi_order` | proved | Mathlib: `Chebyshev.theta_le_log4_mul_x`, Mathlib: `Chebyshev.psi_le_const_mul_self`, Mathlib: `Chebyshev.psi_ge'`, Mathlib: `Chebyshev.theta_ge'` |
| Theorem 415 | 472 | theta(n) < 2 n log 2 for n > 1 | `Chebyshev.theta_le_log4_mul_x`, `primorial_lt_four_pow` | in Mathlib |  |
| Theorem 416 | 473 | n! = prod over primes p of p^(sum_m floor(n/p^m)) (Legendre/de Polignac) | `Nat.factorization_factorial` | in Mathlib |  |
| Theorem 417 | 474 | There is B with a prime in (x, Bx) for every x > 1 | `NTKB.HardyWright.exists_prime_between` | proved | Mathlib: `Nat.exists_prime_lt_and_le_two_mul` |
| Theorem 418 | 474 | Bertrand's postulate: a prime p with n < p < 2n for n > 1 (equivalently p_(r+1) < 2 p_r) | `Nat.exists_prime_lt_and_le_two_mul` | in Mathlib |  |
| Theorem 419 | 476 | With a = sum p_m 10^(-2^m), p_n = [10^(2^n) a] - 10^(2^(n-1)) [10^(2^(n-1)) a] | `NTKB.HardyWright.nth_prime_eq_floor_moserConstant`, `NTKB.HardyWright.moserConstant` | proved |  |
| Theorem 420 | 478 | pi(x), theta(x)/log x, psi(x)/log x and x/log x have the same order | `Chebyshev.pi_ge'`, `Chebyshev.pi_le_log4_mul_div`, `Chebyshev.primeCounting_sub_theta_div_log_isBigO` | in Mathlib |  |
| Theorem 421 | 479 | Abel summation: sum c_n f(n) = sum C(n)(f(n)-f(n+1)) + C(x) f([x]), and integral form | `Finset.sum_Ioc_by_parts`, `sum_mul_eq_sub_integral_mul` | in Mathlib |  |
| Theorem 422 | 480 | sum_(n<=x) 1/n = log x + gamma + O(1/x) | `NTKB.HardyWright.sum_inv_eq_log_add_eulerMascheroni` | proved | Mathlib: `Real.tendsto_harmonic_sub_log`, Mathlib: `harmonic_le_one_add_log` |
| Theorem 423 | 480 | sum_(n<=x) log^h(x/n) = O(x) for h>0 | `NTKB.HardyWright.sum_rpow_log_div_le` | proved | PNT+: `sum_log_div_isBigO` |
| Theorem 424 | 481 | sum_(n<=x) Lambda(n)/n = log x + O(1) | `NTKB.HardyWright.sum_vonMangoldt_div_eq_log` | proved | PNT+: `Mertens.sum_mangoldt_div_eq_log` |
| Theorem 425 | 481 | sum_(p<=x) log p/p = log x + O(1) | `NTKB.HardyWright.sum_log_prime_div_eq_log` | proved | PNT+: `Mertens.sum_log_prime_div_eq_log` |
| Theorem 426 | 482 | liminf pi(x) log x/x <= 1 <= limsup; if the limit exists it equals 1 | `NTKB.HardyWright.primeCounting_mul_log_div_limits` | proved |  |
| Section 22.6 (22.6.1) | 482 | integral from 2 to x of psi(t)/t^2 dt = log x + O(1) | `NTKB.HardyWright.abs_integral_psiRem_div_sq_le`, `NTKB.HardyWright.integral_psi_div_sq` | proved |  |
| Section 22.7 (divergence of sum 1/p and prod (1-1/p)) | 483 | Euler: sum 1/p diverges and prod (1-1/p) diverges to 0 | `NTKB.HardyWright.tendsto_prod_one_sub_inv_primes` | proved | Mathlib: `Nat.Primes.not_summable_one_div`, PNT+: `Mertens.E₃.bound''` |
| Section 22.7 (pi(x) = o(x) elementary) | 483 | From divergence of the product, pi(x)=o(x) | `NTKB.HardyWright.tendsto_primeCounting_div_self` | proved |  |
| Theorem 427 | 485 | sum_(p<=x) 1/p = log log x + B1 + o(1) | `NTKB.HardyWright.tendsto_sum_inv_primes_sub_log_log` | proved | PNT+: `Mertens.sum_prime_div_eq`, PNT+: `Mertens.E₂p.bound'` |
| Theorem 428 | 485 | B1 = gamma + sum_p (log(1-1/p) + 1/p) | `NTKB.HardyWright.tendsto_sum_inv_primes_sub_log_log_eulerMascheroni` | proved | PNT+: `Mertens.M.eq` |
| Theorem 429 | 485 | Mertens: prod_(p<=x)(1-1/p) ~ e^(-gamma)/log x | `NTKB.HardyWright.tendsto_prod_one_sub_inv_primes_mul_log` | proved | PNT+: `Mertens.E₃.bound''` |
| Section 22.9 (Theorems 323, 328 proved) | 488 | liminf phi(n) loglog n/n = e^(-gamma) and limsup sigma(n)/(n loglog n) = e^gamma | `NTKB.HardyWright.limsup_sigma_div_mul_log_log`, `NTKB.HardyWright.liminf_totient_mul_log_log_div`, `NTKB.HardyWright.ExtremalOrder.totient_div_ge` | proved |  |
| Theorem 430 | 491 | Average order of omega(n) and Omega(n) is loglog n with sum = x loglog x + B x + o(x) | `NTKB.HardyWright.tendsto_sum_cardDistinctFactors_sub`, `NTKB.HardyWright.tendsto_sum_cardFactors_sub` | proved |  |
| Theorem 431 | 493 | Normal order of omega(n), Omega(n) is loglog n (Hardy-Ramanujan, Turan proof) | `NTKB.HardyWright.sum_sq_cardDistinctFactors_sub_le`, `NTKB.HardyWright.tendsto_card_normalOrder_cardDistinctFactors`, `NTKB.HardyWright.tendsto_card_normalOrder_cardFactors` | proved |  |
| Theorem 432 | 497 | For almost all n, d(n) lies between (log n)^(log 2 (1-e)) and (log n)^(log 2 (1+e)) | `NTKB.HardyWright.tendsto_card_normalOrder_card_divisors`, `NTKB.HardyWright.two_pow_cardDistinctFactors_le_card_divisors`, `NTKB.HardyWright.card_divisors_le_two_pow_cardFactors` | proved |  |
| Theorem 433 | 497 | Selberg's symmetry formula: psi(x) log x + sum Lambda(n) psi(x/n) = 2x log x + O(x), equivalently the Lambda*Lambda form | `NTKB.HardyWright.selberg_theorem`, `NTKB.HardyWright.selberg_theorem'`, `NTKB.HardyWright.sum_vonMangoldt_mul_log_div_le`, `NTKB.HardyWright.psiRem_log_add_sum`, `NTKB.HardyWright.abs_psiRem_mul_log_sq_le`, `NTKB.HardyWright.abs_psiRem_mul_log_sq_le_integral`, `NTKB.HardyWright.sum_psiAddId_div_le`, `NTKB.HardyWright.selbergV` | proved |  |
| Theorem 434 | 500 | psi(x) ~ x (equivalent to the Prime Number Theorem) | `NTKB.HardyWright.tendsto_psi_div_self`, `NTKB.HardyWright.tendsto_selbergV` | proved | PNT+: `WeakPNT''` |
| Theorem 435 | 505 | Uniform integral bound on V(eta) for the Selberg-method remainder | `NTKB.HardyWright.abs_integral_selbergV_le` | proved |  |
| Theorem 436 | 506 | Short-interval integral bound for V near a zero of V | `NTKB.HardyWright.integral_abs_selbergV_add_le`, `NTKB.HardyWright.abs_selbergV_add_le`, `NTKB.HardyWright.sq_mul_abs_selbergV_le` | proved |  |
| Section 22.17 (Theorem 335) | 508 | Mertens function M(x) = o(x), i.e. sum of mu(n) = o(x) | `NTKB.HardyWright.tendsto_mertens_div_self` | proved | PNT+: `mu_pnt` |
| Theorem 437 | 510 | Landau: pi_k(x) ~ tau_k(x) ~ x (loglog x)^(k-1)/((k-1)! log x), products of k primes | `NTKB.HardyWright.landau_almost_prime`, `NTKB.HardyWright.Landau.factorial_mul_card_le_bigPi`, `NTKB.HardyWright.Landau.bigPi_le_factorial_mul_card`, `NTKB.HardyWright.Landau.card_almostPrime_le`, `NTKB.HardyWright.Landau.tendsto_bigTheta_div`, `NTKB.HardyWright.Landau.tendsto_bigPi_div`, `NTKB.HardyWright.Landau.fRem_small`, `NTKB.HardyWright.Landau.tendsto_bigL_div` | proved |  |
| Section 22.19 (22.19.2) | 513 | For fixed e>0 and large x there is a prime between x and (1+e)x | `NTKB.HardyWright.eventually_exists_prime_between` | proved | PNT+: `prime_between` |
| Section 22.19 (22.19.3) | 513 | pi(2x) - pi(x) ~ pi(x) | `NTKB.HardyWright.tendsto_primeCounting_two_mul_sub_div` | proved |  |

## Chapter XXIII. Kronecker's theorem

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Section 23.1 (Dirichlet's Theorem 201 recalled) | 520 | For any reals, n*theta_i can be made simultaneously close to integers (Dirichlet, simultaneous approximation). | `NTKB.NZM.simultaneous_approximation_general` | proved | Tau Ceti: `TauCeti.simultaneous_dirichlet` |
| Theorem 438 | 520 | For irrational theta, any alpha, N and eps>0 there are integers n>N, p with \\|n*theta-p-alpha\\|<eps. | `TauCeti.kronecker_approximation_nat` | in Tau Ceti only (not a dependency) |  |
| Theorem 439 | 521 | For irrational theta the fractional parts (n*theta) are dense in (0,1). | `AddCircle.denseRange_zsmul_coe_iff` | in Mathlib |  |
| Theorem 440 | 522 | For irrational theta, alpha and N there are n>N and p with \\|n*theta-p-alpha\\| < 3/n (quantitative Kronecker, sharper than 438). | — | not formalized |  |
| Theorem 441 | 524 | A light ray in a square with mirror sides is either periodic (iff the tangent of its angle is rational) or dense in the square. | — | not formalized |  |
| Theorem 442 | 528 | Kronecker: if theta_1..theta_k,1 are linearly independent over Q, any alphas, N and eps>0 give n>N and p_m with \\|n*theta_m-p_m-alpha_m\\|<eps. | `TauCeti.kronecker_approximation_nat` | in Tau Ceti only (not a dependency) |  |
| Theorem 443 | 529 | If theta_i,1 are linearly independent then the points ({n theta_1},...,{n theta_k}) are dense in the unit cube. | `TauCeti.denseRange_mul_sub_intCast` | in Tau Ceti only (not a dependency) |  |
| Theorem 444 | 529 | If theta_1..theta_k are linearly independent, then for any T,eps there is real t>T and integers p_m with \\|t*theta_m-p_m-alpha_m\\|<eps. | `AddCircle.denseRange_coe_add_mul_iff` | partly in other libraries; not proved here |  |
| Theorem 445 | 539 | For irrational theta the points (n*theta) are uniformly distributed in (0,1) (Weyl, one dimension). | `TauCeti.UnitAddTorus.tendsto_inv_smul_intervalIntegral` | partly in other libraries; not proved here |  |

## Chapter XXIV. Geometry of numbers

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Theorem 446 | 542 | Minkowski: a convex region in R^n symmetric about 0 with volume >2^n contains a nonzero integer point. | `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure` | in Mathlib |  |
| Theorem 447 | 543 | Minkowski for a lattice of determinant Delta: convex symmetric region of volume >2^n\\|Delta\\| contains a nonzero lattice point. | `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`, `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure` | in Mathlib |  |
| Theorem 448 | 543 | Minkowski linear forms: n real linear forms of determinant Delta and lambda_i>0 with prod lambda_i >= \\|Delta\\| admit a nonzero integer point with \\|xi_i\\| <= lambda_i (first strict). | `Matrix.exists_ne_zero_int_abs_sum_mul_le` | partly in other libraries; not proved here |  |
| Theorem 449 | 544 | For n real linear forms of determinant D there are integers, not all 0, with \\|xi_1\\|+...+\\|xi_n\\| < (n!\\|D\\|)^(1/n). | — | not formalized |  |
| Theorem 450 | 544 | Integers not all 0 with \\|xi_1 xi_2 ... xi_n\\| < n! \\|D\\| / n^n (AM-GM consequence of 449). | — | not formalized |  |
| Theorem 451 | 545 | Integers not all 0 with xi_1^2+...+xi_n^2 below an explicit constant times \\|D\\|^(2/n) (ball volume, from Theorem 447). | — | not formalized |  |
| Theorem 452 | 545 | A positive definite quadratic form of determinant D takes, at some nonzero integer point, a value bounded by an explicit constant times D^(1/n) (Hermite-type bound). | — | not formalized |  |
| Section 24.4 (best-possible inequalities) | 548 | Theorem 448 is sharp (cannot replace product>= \\|Delta\\| by k\\|Delta\\|, k<1); n=2 case of Theorem 449 is sharp; 450 and 451 are not sharp. | — | not formalized |  |
| Theorem 453 | 550 | For binary x^2+y^2 type form: integers x,y not both 0 with xi^2+eta^2 < (2/sqrt3)\\|Delta\\| (sharp), equality only for x^2+xy+y^2 forms. | — | not formalized |  |
| Theorem 454 | 551 | Integers x,y not both 0 with \\|xi*eta\\| <= \\|Delta\\|/sqrt5, with equality only for forms equivalent to x^2+xy-y^2. | — | not formalized |  |
| Theorem 455 | 553 | Minkowski: for non-homogeneous binary linear forms xi-rho, eta-sigma of determinant Delta there are integers with \\|(xi-rho)(eta-sigma)\\| <= \\|Delta\\|/4. | — | not formalized |  |
| Theorem 456 | 553 | Lattice version of 455: for a lattice of determinant Delta and any point Q, some lattice-equivalent point has \\|xi*eta\\| <= \\|Delta\\|/4. | — | not formalized |  |
| Theorem 457 | 556 | Tchebotaref: for linear forms with determinant Delta and shifts rho_i, the lower bound m of \\|prod (xi_i-rho_i)\\| satisfies m <= 2^(-2n)\\|Delta\\|. | — | not formalized |  |
| Theorem 458 | 559 | A bounded plane region of area V<1 admits a lattice of determinant 1 with no nonzero point in it. | — | not formalized |  |
| Theorem 459 | 560 | For visible lattice points f(p) of the lattice p*Z^2 in P, p^2 f(p) tends to V/zeta(2) as p tends to 0. | — | not formalized |  |
| Theorem 460 | 562 | A star region symmetric about 0 with area V < 2 zeta(2) = pi^2/3 admits a lattice of determinant 1 with no nonzero point in it. | — | not formalized |  |

## Chapter XXV. Elliptic curves

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Section 25.1 (congruent numbers and y^2=x^3-n^2x) | 568 | Squarefree n is a congruent number iff y^2=x^3-n^2x has a rational solution with x,y>0 (explicit bijection with rational right triangles of area n). | — | not formalized |  |
| Theorem 461 | 569 | Elliptic curves y^2=x^3+Ax+B and y^2=x^3+A'x+B' over a field k are k-isomorphic iff j agrees and (A=A'=0 with B/B' a 6th power) or (B=B'=0 with A/A' a 4th power) or (ABA'B' nonzero with AB'/A'B a square). | `WeierstrassCurve.exists_variableChange_of_j_eq`, `WeierstrassCurve.variableChange_j`, `WeierstrassCurve.j_of_isShortNF` | partly in other libraries; not proved here |  |
| Section 25.2 (addition formulae 25.2.3-25.2.9) | 571 | Chord-tangent formulae: slope, x_R = lambda^2 - x_P - x_Q, P+Q = (x_R,-y_R), and the duplication formula for x_{2P}. | `WeierstrassCurve.Affine.slope`, `WeierstrassCurve.Affine.addX`, `WeierstrassCurve.Affine.addY`, `WeierstrassCurve.Affine.negAddY` | in Mathlib |  |
| Theorem 462 | 572 | The chord-tangent addition on an elliptic curve has identity O, inverses, is commutative, and (starred part) associative, so E is an abelian group. | `WeierstrassCurve.Affine.Point.toClass_injective` | in Mathlib |  |
| Theorem 463 | 573 | For A,B in a field k the k-rational points E(k) (with O) are closed under sum and difference, so E(k) is an abelian group. | `WeierstrassCurve.Affine.Point.map`, `WeierstrassCurve.Affine.Point.map_injective` | in Mathlib |  |
| Theorem 464 | 574 | A point P=(x,y) different from O on E has order 2 iff y=0. | `WeierstrassCurve.Affine.Point.add_self_of_Y_eq`, `WeierstrassCurve.Affine.Point.isRoot_twoTorsionPolynomial_iff` | partly in other libraries; not proved here |  |
| Section 25.2 (CM endomorphisms; End(E)=Z[i], Z[rho] for y^2=x^3+Ax, y^2=x^3+B) | 575 | The curves y^2=x^3+Ax and y^2=x^3+B have extra endomorphisms (x,y)->(-x,iy), (x,y)->(rho x,y); endomorphism rings are the Gaussian integers and Z[rho]; endomorphisms form a ring. | — | not formalized |  |
| Theorem 465 | 576 | The map (X,Y)->(12A/(X+Y), 36A(X-Y)/(X+Y)) is a bijection from nonzero solutions of X^3+Y^3=A to solutions (x neq 0) of y^2=x^3-432A^2, with explicit inverse. | — | not formalized |  |
| Section 25.3 (nonsingular cubic with a point is an elliptic curve) | 576 | Any nonsingular plane cubic with a rational point can be transformed to a Weierstrass equation with coefficients in the same field. | — | not formalized |  |
| Section 25.3 (discriminant effect of change of variables) | 577 | Under the substitution x=u^2x'+r, y=u^3y'+u^2sx'+t the discriminant scales by u^-12. | `WeierstrassCurve.variableChange_Δ` | in Mathlib |  |
| Section 25.3 (reduction to short Weierstrass form) | 577 | If char k is not 2 or 3, a substitution turns a generalized Weierstrass equation into y^2=x^3+Ax+B with explicit A,B. | `WeierstrassCurve.exists_variableChange_isShortNF` | in Mathlib |  |
| Section 25.4 (points of order m in E(C) form Z/m x Z/m) | 578 | The m-torsion of E(C) is a product of two cyclic groups of order m. | — | not formalized |  |
| Theorem 466 | 578 | (Nagell-Lutz) A torsion point in E(Q) for integral A,B has integer coordinates, and y=0 or y^2 divides 4A^3+27B^2. | `WeierstrassCurve.Affine.finite_torsion` | partly in other libraries; not proved here |  |
| Theorem 467 | 579 | Formula for the z-coordinate of P+Q in the (z,w)=(x/y,1/y) coordinates: z_{P+Q} = (-2A alpha beta - 3B alpha^2 beta)/(1+A alpha^2+B alpha^3) - z_P - z_Q. | — | not formalized |  |
| Section 25.4 (valuation rules 25.4.8-25.4.10) | 581 | v_p(ab)=v_p(a)+v_p(b), v_p(a+b)>=min, and equality when valuations differ, on the rationals. | `padicValRat.mul`, `padicValRat.min_le_padicValRat_add`, `padicValRat.add_eq_of_lt` | in Mathlib |  |
| Theorem 468 | 581 | For integral E and a rational point, v_p(z)>0 iff v_p(w)>0 iff v_p(x)<0 iff v_p(y)<0, and then v_p(x)=-2v_p(z), v_p(y)=-3v_p(z), v_p(w)=3v_p(z). | — | not formalized |  |
| Theorem 469 | 581 | For points in (z,w)-coordinates with z_P, z_Q divisible by p^k, z_{P+Q} is congruent to z_P+z_Q mod p^{5k} (the first step of formal group filtration). | — | not formalized |  |
| Theorem 470 | 584 | (Mordell-Weil) For E over Q the group E(Q) is finitely generated. | `AddCommGroup.fg_of_descent'`, `WeierstrassCurve.Affine.approx_parallelogram_law`, `WeierstrassCurve.Affine.finite_naiveHeight_le` | partly in other libraries; not proved here |  |
| Theorem 471 | 584 | Structure form of Mordell-Weil: every point is uniquely n1P1+...+nrPr+T with T torsion; r is the rank of E(Q). | `AddCommGroup.equiv_free_prod_directSum_zmod` | partly in other libraries; not proved here |  |
| Theorem 472 | 584 | Rational points of E have the form (a/d^2, b/d^3) with gcd(a,d)=gcd(b,d)=1. | `NTKB.NZM.rational_point_denominators` | proved |  |
| Theorem 473 | 584 | y^2=x^3+x has rank 0: E(Q)={O,(0,0)}. | `not_fermat_42` | partly in other libraries; not proved here |  |
| Theorem 474 | 585 | For B in {16,-144,-432,3888}, E_B: y^2=x^3+B has finite E_B(Q) (rank 0). | — | not formalized |  |
| Theorem 475 | 586 | (Weak Mordell-Weil, starred, no proof in the book) E(Q)/2E(Q) is finite. | — | not formalized |  |
| Section 25.5 (finitely many rational points of bounded height) | 586 | Only finitely many points of E(Q) have height below any bound. | `WeierstrassCurve.Affine.finite_naiveHeight_le` | in Mathlib |  |
| Theorem 476 | 587 | For integral E there are c1,c2>0 with H(P+Q)<=c1 H(P)^2 H(Q)^2 and H(2P)>=c2 H(P)^4 for rational points. | `WeierstrassCurve.Affine.approx_parallelogram_law` | partly in other libraries; not proved here |  |
| Section 25.5 (descent: finite index of 2E plus heights give generation) | 590 | With H(P+Q)<=c1 H(P)^2 H(Q)^2 and H(2P)>=c2 H(P)^4, a finite set of bounded height generates E(Q). | `AddCommGroup.fg_of_descent'`, `CommGroup.fg_of_descent` | in Mathlib |  |
| Section 25.6 (counting points: #E(F_p) = p+1 + sum of Legendre symbols) | 592 | #E(F_p) = 1 + sum_x (1 + (x^3+Ax+B / p)) = p+1+sum_x (x^3+Ax+B/p). | — | not formalized |  |
| Theorem 477 | 592 | (Hasse bound) \\|#E(F_p)-(p+1)\\| < 2 sqrt p for an elliptic curve over F_p. | — | not formalized |  |
| Theorem 478 | 593 | The equation y^2=x^3+7 has no integer solutions. | `NTKB.NZM.no_solution_sq_eq_cube_add_seven` | proved |  |
| Theorem 479 | 593 | The only integer solutions of y^2=x^3-2 are (3,+-5). | — | not formalized |  |
| Theorem 480 | 594 | Every integer solution of x^3+y^3=A (A nonzero) satisfies x^2+y^2<=2\\|A\\|. | — | not formalized |  |
| Theorem 481 | 595 | For d not a cube and A nonzero, x^3+dy^3=A has finitely many integer solutions. | `TauCeti.finite_setOf_mul_pow_add_mul_pow_eq`, `MvPolynomial.IsHomogeneous.finite_setOf_eval_eq` | in Tau Ceti only (not a dependency) |  |
| Theorem 482 | 595 | (Roth) For algebraic alpha of degree >=2 and eps>0, \\|alpha - a/b\\| > C(alpha,eps)/b^{2+eps} for all a/b. | `IsAlgebraic.finite_setOfPred_abs_sub_le_mulHeight₁_rpow_neg` | in Tau Ceti only (not a dependency) |  |
| Theorem 483 | 597 | (Siegel) An elliptic curve with rational coefficients has only finitely many integer points. | — | not formalized |  |
| Theorem 484 | 597 | For distinct rational points P_n of E(Q) with x(P_n)=a_n/b_n, log\\|a_n\\|/log\\|b_n\\| tends to 1. | — | not formalized |  |
| Theorem 485 | 598 | The L-series coefficients a_n are multiplicative, satisfy a_p a_{p^k}=a_{p^{k+1}}+p a_{p^{k-1}} for good p, and \\|a_n\\|<=d(n) sqrt n. | — | not formalized |  |
| Theorem 486 | 599 | L(E,s) converges absolutely and is nonvanishing holomorphic for Re(s)>3/2. | — | not formalized |  |
| Theorem 487 | 600 | (Modularity of L-series) L(E,s) continues analytically to C and its completed form satisfies a functional equation s -> 2-s with sign +-1 and conductor N_E. | — | not formalized |  |
| Section 25.8 (BSD conjecture) | 600 | Conjecture: ord_{s=1} L(E,s) = rank E(Q); in particular L(E,1)=0 iff E(Q) infinite. | — | not formalized |  |
| Theorem 488 | 601 | (Gross-Zagier, Kolyvagin) If L(E,1) neq 0 then rank E(Q)=0; if L(E,1)=0 and L'(E,1) neq 0 then rank 1. | — | not formalized |  |
| Theorem 489 | 601 | If P in E(k) has 2P and 3P nonzero, a change of variables over k puts E in the form y^2+(w+1)xy+vy=x^3+vx^2 with P=(0,0), with w,v unique and a stated discriminant. | — | not formalized |  |
| Theorem 490 | 603 | For N>=4 there is a nonzero integer polynomial Psi_N(w,v) with (0,0) of order N on E_{w,v} iff Psi_N=0, and every curve with a point of exact order N has such a model. | — | not formalized |  |
| Section 25.9 (polynomials Psi_5..Psi_9 and parametrizations for N=5,6,7) | 604 | Explicit Psi_5=W-V, Psi_6=W^2-W+V, Psi_7, Psi_8, Psi_9; parametrization of curves with point of order 7 by Z. | — | not formalized |  |
| Theorem 491 | 605 | (Mazur) A rational point of exact order N on an elliptic curve over Q has N<=10 or N=12. | — | not formalized |  |
| Theorem 492 | 605 | (Fermat's Last Theorem, Wiles) a^n+b^n=c^n has no solutions in nonzero integers for n>=3. | `FermatLastTheorem` | partly in other libraries; not proved here |  |
| Section 25.10 (Frey curve discriminant 25.10.3 and Ribet level lowering) | 606 | The Frey curve y^2=x(x+a^p)(x-b^p) has discriminant 16(abc)^{2p}; Ribet's theorem shows it is not modular. | — | not formalized |  |
| Theorem 493 | 607 | (Modularity theorem; Wiles, Taylor, Breuil-Conrad-Diamond) Every elliptic curve over Q is modular, i.e. covered by some X_1(N). | — | not formalized |  |
