# Special values of Dirichlet $L$-functions: map to the Lean library

The results on special values: generalized Bernoulli numbers, the values $L(1-k,\chi)$ and $L(k,\chi)$ of Dirichlet $L$-functions, and Gauss's sign of quadratic Gauss sums. Sources: Washington, *Introduction to Cyclotomic Fields*, Chapter 4; Ireland–Rosen, Chapters 6 and 16; Miyake, §3.3. Each row is a result of the book, the Lean declarations that formalize it, and its status, computed from the Lean kernel (an audit of the axioms and hypotheses of every declaration): *proved* means proved with only the standard axioms and no unproved input; *proved in part* that a part, a special case or one instance is proved; *proved, conditional* that an unproved input (a named statement) is assumed; *refuted as stated in the book* that the library proves the printed statement false and proves a corrected form (see the errata in the README); *in Mathlib* that Mathlib (a dependency) has the result and the Lean name is Mathlib's. Results that are only in Tau Ceti or PrimeNumberTheoremAnd (which this library does not depend on) are marked so. The statements in the third column are short descriptions, not quotations; read the book for the exact wording. The column *Also in* credits other libraries: Mathlib, Tau Ceti or PrimeNumberTheoremAnd declarations that prove the result, a part of it, or a closely related statement (as recorded by the coverage audit).

Rows: 25. proved: 25. Proved here and also in another library: 3.


## (a) Generalized Bernoulli numbers and $L(1-k,\chi)$

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| — | — | $\displaystyle\Big(\sum_{n\ge0}B_{n,\chi}\frac{t^n}{n!}\Big)(e^{Nt}-1)=\sum_{a=1}^{N}\chi(a)\,t\,e^{at}$ in $\mathbb C[[t]]$ | `NTKB.generalizedBernoulli_generating_function` | proved |  |
| — | — | the generating function determines $(B_{n,\chi})_n$ | `NTKB.generalizedBernoulli_unique_of_generating_function` | proved |  |
| — | — | $B_{n,\chi}=0$ if $\chi(-1)=-(-1)^n$, unless $n=1,N=1$ | `NTKB.generalizedBernoulli_eq_zero_of_apply_neg_one_eq_neg` | proved |  |
| — | — | $B_{n,\chi}=B_n(1)$ for $N=1$ | `NTKB.generalizedBernoulli_modOne` | proved |  |
| — | — | **$L(1-k,\chi)=-B_{k,\chi}/k$ for every Dirichlet character $\chi$ and every $k\ge1$** | `NTKB.LFunction_one_sub_nat` | proved |  |
| — | — | $L(0,\chi)=-B_{1,\chi}$ | `NTKB.LFunction_zero` | proved |  |
| — | — | $\zeta_{\mathrm{odd}}(a,1)=\tfrac{\pi}{2}\cot(\pi a)$ for $0<a<1$ | `NTKB.hurwitzZetaOdd_one` | proved |  |

## (b) $L(k,\chi)$ for primitive $\chi$

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| — | — | $\tau(\chi)\sum_{n\in\mathbb Z}\bar\chi(n)n^{-k}=-\frac{(2\pi i)^k}{k!\,N^{k-1}}B_{k,\chi}$, $\chi$ primitive, $k\ge2$ (Tau Ceti) | `NTKB.gaussSum_mul_tsum_inv_pow_eq_generalizedBernoulli` | proved | Tau Ceti (ported here): `gaussSum_mul_tsum_inv_pow_eq_generalizedBernoulli` |
| — | — | $\tau(\chi)\tau(\bar\chi)=\chi(-1)N$ for primitive $\chi$ (Tau Ceti) | `NTKB.gaussSum_mul_gaussSum_inv_eq_neg_one_mul_card_of_isPrimitive` | proved | Tau Ceti (ported here): `gaussSum_mul_gaussSum_inv_eq_neg_one_mul_card_of_isPrimitive` |
| — | — | $\sum_{n\in\mathbb Z}\chi(n)n^{-k}=2L(k,\chi)$ if $\chi(-1)=(-1)^k$, $k\ge2$ | `NTKB.hasSum_int_eq_two_mul_LFunction` | proved |  |
| — | — | the theorem for $k\ge2$ | `NTKB.LFunction_natCast_of_two_le` | proved |  |
| — | — | $L(1,\chi)=\pi i\,\tau(\chi)B_{1,\bar\chi}/f$, $\chi$ primitive odd (from Mathlib's functional equation and (a)) | `NTKB.LFunction_one_of_odd` | proved |  |
| — | — | check against Mathlib's $\zeta(2)=\pi^2/6$ | `NTKB.LFunction_natCast_check_zeta_two` | proved |  |
| — | — | $L(k,\chi)=(-1)^{1+(k-\delta)/2}\tau(\chi)/(2i^\delta)\,(2\pi/f)^k B_{k,\bar\chi}/k!$ for primitive $\chi$, $k\ge1$, $\chi(-1)=(-1)^k$ | `NTKB.LFunction_natCast` | proved |  |
| — | — | the variant with $\tau(\chi)/2$ in place of $\tau(\chi)/(2i^\delta)$: true for even primitive $\chi$ | `NTKB.issueTwoLValueFormula_of_even` | proved |  |
| — | — | that variant is false for every odd primitive $\chi$ | `NTKB.not_issueTwoLValueFormula_of_odd` | proved |  |

## (c) Gauss's sign of the quadratic Gauss sum

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| — | — | $\sum_{r=0}^{N-1}e^{2\pi i r^2/N}=\frac{1+i}{2}(1+(-i)^N)\sqrt N$ for every $N$ (theta-function proof, Tau Ceti) | `NTKB.sum_range_cexp_two_pi_I_sq_div` | proved | Tau Ceti (ported here): `sum_range_cexp_two_pi_I_sq_div` |
| — | — | $p$ odd prime: $\tau\big((\tfrac{\cdot}{p})\big)=\sqrt p$ if $p\equiv1$, $i\sqrt p$ if $p\equiv3 \pmod 4$ | `NTKB.gaussSum_legendreChar` | proved |  |
| — | — | $\tau\big((\tfrac{\cdot}{p})\big)=\sum_{x}e^{2\pi i x^2/p}$ | `NTKB.gaussSum_legendreChar_eq_sum_sq` | proved |  |
| — | — | $m$ odd squarefree: $\tau\big((\tfrac{\cdot}{m})\big)=\sqrt m$ or $i\sqrt m$ by $m \bmod 4$ (Jacobi symbol) | `NTKB.gaussSum_jacobiChar` | proved |  |
| — | — | $\tau(\chi_{-4})=2i$, $\tau(\chi_8)=2\sqrt2$, $\tau(\chi_{-8})=2\sqrt2\,i$ | `NTKB.gaussSum_chi4`, `NTKB.gaussSum_chi8`, `NTKB.gaussSum_chi8'` | proved |  |
| — | — | $N=mn$, $(m,n)=1$, $\Xi(a)=\chi(a)\psi(a)$: $\tau(\Xi)=\chi(n)\psi(m)\tau(\chi)\tau(\psi)$ | `NTKB.gaussSum_eq_mul_of_coprime` | proved |  |
| — | — | **$D$ fundamental: $\tau(\chi_D)=\sqrt D$ if $D>0$, $i\sqrt{\lvert D\rvert}$ if $D<0$** | `NTKB.gaussSum_kroneckerChar` | proved |  |

## (d) The quadratic case

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| — | — | $L(1-k,\chi_D)=-B_{k,\chi_D}/k\in\mathbb Q$ for a fundamental discriminant $D$ | `NTKB.LFunction_kroneckerChar_one_sub_nat` | proved |  |
| — | — | $L(k,\chi_D)$ is a rational multiple of $\pi^k/\sqrt{\|D\|}$ (explicit formula) | `NTKB.LFunction_kroneckerChar_natCast`, `NTKB.exists_rat_LFunction_kroneckerChar_natCast` | proved |  |
